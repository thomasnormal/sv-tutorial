#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT_DIR/scripts/toolchain.lock.sh"

MOX_DIR="${1:-vendor/mox}"
BUILD_DIR="${BUILD_DIR:-$MOX_DIR/build-wasm}"
JOBS="${MOX_WASM_JOBS:-6}"
CONFIGURE_TIMEOUT_MIN="${MOX_WASM_CONFIGURE_TIMEOUT_MIN:-30}"
BUILD_TIMEOUT_MIN="${MOX_WASM_BUILD_TIMEOUT_MIN:-120}"
MEMORY_LIMIT_KB="${MOX_WASM_MEMORY_LIMIT_KB:-0}"
SKIP_BUILD="${MOX_WASM_SKIP_BUILD:-0}"
# MOX_WASM_TARGETS — space-separated ninja targets to build. Set this to
# narrow rebuilds when iterating on a single tool, e.g.:
#   MOX_WASM_TARGETS=mox-sim scripts/build-mox-wasm.sh
TARGETS_RAW="${MOX_WASM_TARGETS:-mox-verilog mox-sim mox-bmc mox-lec}"
CLEAN_BUILD="${MOX_WASM_CLEAN_BUILD:-0}"
AUTO_RETRY_CLEAN="${MOX_WASM_AUTO_RETRY_CLEAN:-1}"
# Compiler launcher caches emcc invocations; ~5-10x speedup on incremental
# rebuilds after warmup. Pass CCACHE=0 to disable.
USE_CCACHE="${CCACHE:-1}"
CCACHE_BIN="$(command -v ccache 2>/dev/null || true)"

if [[ ! "$JOBS" =~ ^[1-9][0-9]*$ ]]; then
  echo "MOX_WASM_JOBS must be a positive integer (got $JOBS)" >&2
  exit 1
fi

run_configure() {
  echo "Configuring wasm build in $BUILD_DIR"
  # - Tcl bindings default ON in upstream CMakeLists.txt and require tcl.h,
  #   which is not part of a typical wasm/emsdk toolchain. Not used by any
  #   sv-tutorial lesson.
  # - LLVM examples/benchmarks are not needed for our wasm targets; the
  #   examples tree in the upstream fork is also missing
  #   examples/Kaleidoscope/BuildingAJIT, so leaving them ON fails configure.
  local extra_args=(
    -DMOX_BINDINGS_TCL_ENABLED=OFF
    -DLLVM_INCLUDE_EXAMPLES=OFF
    -DLLVM_BUILD_EXAMPLES=OFF
    -DLLVM_INCLUDE_BENCHMARKS=OFF
    -DLLVM_BUILD_BENCHMARKS=OFF
  )
  if [[ "$USE_CCACHE" == "1" && -n "$CCACHE_BIN" ]]; then
    echo "  using ccache launcher: $CCACHE_BIN"
    # PCH compiles (~90% of LLVM/MOX cxx work) are uncacheable by default
    # because ccache doesn't trust __DATE__/__TIME__/PCH mtimes. The
    # sloppiness flags below let ccache cache them. CCACHE_BASEDIR rewrites
    # absolute paths in compile commands to relative form so hits survive
    # across worktrees and across configure runs that pick different build
    # dirs.
    export CCACHE_SLOPPINESS="${CCACHE_SLOPPINESS:-pch_defines,time_macros,include_file_mtime,include_file_ctime}"
    export CCACHE_BASEDIR="${CCACHE_BASEDIR:-$HOME}"
    extra_args+=(
      "-DCMAKE_C_COMPILER_LAUNCHER=$CCACHE_BIN"
      "-DCMAKE_CXX_COMPILER_LAUNCHER=$CCACHE_BIN"
    )
  fi
  run_with_timeout "$CONFIGURE_TIMEOUT_MIN" \
    nice -n 10 env BUILD_DIR="$BUILD_DIR" \
    "$MOX_DIR/utils/configure_wasm_build.sh" \
    "${extra_args[@]}"
}

run_build() {
  echo "Building targets: ${targets[*]} (jobs=$JOBS)"
  run_with_timeout "$BUILD_TIMEOUT_MIN" \
    nice -n 10 ninja -C "$BUILD_DIR" -j"$JOBS" "${targets[@]}"
}

run_with_timeout() {
  local minutes="$1"
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout --preserve-status "${minutes}m" "$@"
    return
  fi
  if command -v gtimeout >/dev/null 2>&1; then
    gtimeout --preserve-status "${minutes}m" "$@"
    return
  fi
  echo "Warning: timeout/gtimeout not found; running without wall-clock guard." >&2
  "$@"
}

if [[ "$MEMORY_LIMIT_KB" != "0" ]]; then
  if ulimit -v "$MEMORY_LIMIT_KB" >/dev/null 2>&1; then
    echo "Applied virtual memory limit: ${MEMORY_LIMIT_KB} KB"
  else
    echo "Warning: unable to apply ulimit -v=$MEMORY_LIMIT_KB on this shell/platform." >&2
  fi
fi

STRICT_NODE_VERSION=0 "$ROOT_DIR/scripts/check-requirements.sh" --with-wasm

if [[ ! -d "$MOX_DIR" ]]; then
  echo "Missing MOX checkout: $MOX_DIR" >&2
  echo "Run scripts/setup-mox.sh first." >&2
  exit 1
fi

read -r -a targets <<< "$TARGETS_RAW"
if ((${#targets[@]} == 0)); then
  echo "MOX_WASM_TARGETS resolved to an empty target list." >&2
  exit 1
fi

if [[ "$CLEAN_BUILD" == "1" && -d "$BUILD_DIR" ]]; then
  echo "Cleaning build directory: $BUILD_DIR"
  cmake -E rm -rf "$BUILD_DIR"
fi

run_configure

if [[ "$SKIP_BUILD" == "1" ]]; then
  echo "Skipping ninja build because MOX_WASM_SKIP_BUILD=1"
  exit 0
fi

if ! run_build; then
  if [[ "$AUTO_RETRY_CLEAN" == "1" && "$CLEAN_BUILD" != "1" ]]; then
    echo "Initial build failed; retrying once from a clean build directory."
    cmake -E rm -rf "$BUILD_DIR"
    run_configure
    run_build
  else
    exit 1
  fi
fi

echo "Built MOX wasm artifacts in: $BUILD_DIR/bin"
ls -lh \
  "$BUILD_DIR/bin/mox-verilog.js" "$BUILD_DIR/bin/mox-verilog.wasm" \
  "$BUILD_DIR/bin/mox-sim.js" "$BUILD_DIR/bin/mox-sim.wasm" \
  "$BUILD_DIR/bin/mox-bmc.js" "$BUILD_DIR/bin/mox-bmc.wasm"
