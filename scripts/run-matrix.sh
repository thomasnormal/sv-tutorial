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
for artifact in \
  mox-verilog.js mox-verilog.wasm \
  mox-sim.js mox-sim.wasm \
  mox-bmc.js mox-bmc.wasm \
  mox-lec.js mox-lec.wasm \
  mox-sim-vpi.js mox-sim-vpi.wasm; do
  [[ -f "$MOX_WASM_DIR/$artifact" ]] || {
    echo "Mox WASM directory is missing $artifact: $MOX_WASM_DIR" >&2
    exit 2
  }
done

STATIC_MOX="$REPO_ROOT/static/mox"
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
ln -s "$STAGED_MOX" "$STATIC_MOX"
if [[ "$RESTORE_NEEDED" == 0 ]]; then RESTORE_NEEDED=2; fi

PORT="${MATRIX_PORT:-4173}"
PREVIEW_LOG="${MATRIX_LOG:-/var/tmp/sv-tutorial-matrix-preview.log}"
PREVIEW_PID=""
cleanup() {
  if [[ -n "$PREVIEW_PID" ]]; then kill "$PREVIEW_PID" 2>/dev/null || true; wait "$PREVIEW_PID" 2>/dev/null || true; fi
  if [[ "$RESTORE_NEEDED" == 1 ]]; then
    rm -f "$STATIC_MOX"
    mv "$BACKUP_MOX" "$STATIC_MOX"
  elif [[ "$RESTORE_NEEDED" == 2 ]]; then
    rm -f "$STATIC_MOX"
  fi
  rm -rf "$BACKUP_ROOT"
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
MATRIX_BASE_URL="http://127.0.0.1:$PORT" node scripts/run-matrix.mjs
kill "$PREVIEW_PID" 2>/dev/null || true
wait "$PREVIEW_PID" 2>/dev/null || true
PREVIEW_PID=""
npm run build
