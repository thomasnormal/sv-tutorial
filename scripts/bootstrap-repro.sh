#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT_DIR"

scripts/check-requirements.sh
npm ci
scripts/setup-surfer.sh
scripts/setup-pyodide.sh
scripts/setup-mox.sh
scripts/build-mox-wasm.sh
npm run local-publish:mox
npm run build

echo "Bootstrap complete."
