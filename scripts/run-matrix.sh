#!/usr/bin/env bash
set -Eeuo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MOX_WASM_DIR="${1:-}"
if [[ -z "$MOX_WASM_DIR" ]]; then
  echo "usage: scripts/run-matrix.sh <mox-wasm-dir>" >&2
  exit 2
fi

MOX_WASM_DIR="$(cd "$MOX_WASM_DIR" 2>/dev/null && pwd)" || {
  echo "Mox WASM directory does not exist: $1" >&2
  exit 2
}
STATIC_MOX="$REPO_ROOT/static/mox"
INPUT_COPY_ROOT=""
# It is convenient to validate the checked-out artifact directory itself
# during local QA. Copy it before staging because the wrapper temporarily
# moves static/mox out of the way below.
if [[ "$MOX_WASM_DIR" == "$STATIC_MOX" ]]; then
  INPUT_COPY_ROOT="$(mktemp -d /var/tmp/sv-tutorial-matrix-input.XXXXXX)"
  cp -a "$MOX_WASM_DIR"/. "$INPUT_COPY_ROOT"/
  MOX_WASM_DIR="$INPUT_COPY_ROOT"
fi
for artifact in \
  mox-verilog.js mox-verilog.wasm \
  mox-sim.js mox-sim.wasm \
  mox-bmc.js mox-bmc.wasm \
  mox-lec.js mox-lec.wasm; do
  [[ -f "$MOX_WASM_DIR/$artifact" ]] || {
    echo "Mox WASM directory is missing $artifact: $MOX_WASM_DIR" >&2
    exit 2
  }
done

if [[ ! -f "$MOX_WASM_DIR/mox-sim-vpi.js" || ! -f "$MOX_WASM_DIR/mox-sim-vpi.wasm" ]]; then
  echo "Note: mox-sim-vpi is absent; the matrix will use mox-sim as its VPI fallback." >&2
fi

resolve_mox_sha() {
  if [[ -n "${MATRIX_MOX_SHA:-}" ]]; then
    printf '%s' "$MATRIX_MOX_SHA"
    return
  fi
  local candidate
  candidate="$MOX_WASM_DIR"
  for _ in 1 2 3 4 5 6; do
    if git -C "$candidate" rev-parse --show-toplevel >/dev/null 2>&1; then
      git -C "$candidate" rev-parse HEAD
      return
    fi
    candidate="$(dirname "$candidate")"
  done
  echo "Unable to determine the Mox build SHA. Set MATRIX_MOX_SHA=<git-sha>." >&2
  exit 2
}

MATRIX_MOX_SHA="$(resolve_mox_sha)"
MATRIX_RESULTS_OUTPUT="${MATRIX_RESULTS_OUTPUT:-$REPO_ROOT/results/$MATRIX_MOX_SHA.md}"

BACKUP_ROOT="$(mktemp -d /var/tmp/sv-tutorial-matrix.XXXXXX)"
BACKUP_MOX="$BACKUP_ROOT/mox"
STAGED_MOX="$BACKUP_ROOT/staged-mox"
RESTORE_NEEDED=0
if [[ -e "$STATIC_MOX" || -L "$STATIC_MOX" ]]; then
  mv "$STATIC_MOX" "$BACKUP_MOX"
  RESTORE_NEEDED=1
fi

# Fleet build directories usually contain only the wasm/js artifacts.  Keep
# the checked-in UVM manifest/source tree available to the browser worker when
# the handoff does not include it.
mkdir -p "$STAGED_MOX"
cp -a "$MOX_WASM_DIR"/. "$STAGED_MOX"/
if [[ ! -d "$STAGED_MOX/uvm-core" && -d "$BACKUP_MOX/uvm-core" ]]; then
  cp -a "$BACKUP_MOX/uvm-core" "$STAGED_MOX/uvm-core"
fi
if [[ ! -f "$STAGED_MOX/mox-sim-vpi.js" || ! -f "$STAGED_MOX/mox-sim-vpi.wasm" ]]; then
  cp -f "$STAGED_MOX/mox-sim.js" "$STAGED_MOX/mox-sim-vpi.js"
  cp -f "$STAGED_MOX/mox-sim.wasm" "$STAGED_MOX/mox-sim-vpi.wasm"
fi
ln -s "$STAGED_MOX" "$STATIC_MOX"
if [[ "$RESTORE_NEEDED" == 0 ]]; then RESTORE_NEEDED=2; fi

PORT="${MATRIX_PORT:-4173}"
PREVIEW_LOG="${MATRIX_LOG:-/var/tmp/sv-tutorial-matrix-preview.log}"
PREVIEW_PID=""
cleanup() {
  if [[ -n "$PREVIEW_PID" ]]; then kill "$PREVIEW_PID" 2>/dev/null || true; wait "$PREVIEW_PID" 2>/dev/null || true; fi
  if [[ "$RESTORE_NEEDED" == 1 ]]; then
    # The build adapter may materialize a staged symlink as a directory.
    rm -rf "$STATIC_MOX"
    mv "$BACKUP_MOX" "$STATIC_MOX"
  elif [[ "$RESTORE_NEEDED" == 2 ]]; then
    rm -rf "$STATIC_MOX"
  fi
  rm -rf "$BACKUP_ROOT"
  if [[ -n "$INPUT_COPY_ROOT" ]]; then rm -rf "$INPUT_COPY_ROOT"; fi
}
trap cleanup EXIT

cd "$REPO_ROOT"
npm run build
npm run preview -- --host 127.0.0.1 --port "$PORT" >"$PREVIEW_LOG" 2>&1 &
PREVIEW_PID=$!
for _ in $(seq 1 120); do
  if curl -fsS "http://127.0.0.1:$PORT/" >/dev/null 2>&1; then break; fi
  sleep 1
done
curl -fsS "http://127.0.0.1:$PORT/" >/dev/null
MATRIX_BASE_URL="http://127.0.0.1:$PORT" \
MATRIX_MOX_SHA="$MATRIX_MOX_SHA" \
MATRIX_RESULTS_OUTPUT="$MATRIX_RESULTS_OUTPUT" \
node scripts/run-matrix.mjs
kill "$PREVIEW_PID" 2>/dev/null || true
wait "$PREVIEW_PID" 2>/dev/null || true
PREVIEW_PID=""
npm run build
