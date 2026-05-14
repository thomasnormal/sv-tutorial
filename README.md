# sv-tutorial

Svelte-based interactive tutorial shell for SystemVerilog, SVA, and UVM.

## Reproducible Requirements

Pinned versions are centralized in `scripts/toolchain.lock.sh`:

- Node major: `22`
- Emscripten (emsdk): `4.0.21`
- MOX repo: `https://github.com/normal-computing/mox.git`
- MOX ref: `8e8ca87dcda1c8abd47103ae7789c8ed261d5de3`
- LLVM submodule ref: `972cd847efb20661ea7ee8982dd19730aa040c75`

Host tools:

- `git`
- `node`/`npm` (Node 22.x)
- `cmake` (>= 3.24)
- `ninja` (>= 1.10)
- `python3` (>= 3.10)
- `rsync`
- `unzip`

Check prerequisites:

- `npm run check:req` (frontend/tooling only)
- `npm run check:req:wasm` (includes emsdk/emcc verification)

## Reproducible Local Build

1. Activate emsdk `4.0.21` (or ensure `emcc -v` reports `4.0.21`).
2. Run the one-shot bootstrap:
   - `npm run bootstrap:repro`

Equivalent step-by-step:

1. `npm ci`
2. `scripts/setup-surfer.sh`
3. `npm run setup:pyodide`
4. `npm run setup:mox`
5. `npm run build:mox`
6. `npm run local-publish:mox`
7. `npm run build`

The MOX wasm build script enforces conservative resource limits by default:

- Ninja parallelism: `MOX_WASM_JOBS=4`
- Configure timeout: `MOX_WASM_CONFIGURE_TIMEOUT_MIN=30`
- Build timeout: `MOX_WASM_BUILD_TIMEOUT_MIN=120`
- Force clean build dir first: `MOX_WASM_CLEAN_BUILD=1`
- Build targets override: `MOX_WASM_TARGETS="mox-verilog mox-sim mox-bmc"`
- Optional virtual memory cap: `MOX_WASM_MEMORY_LIMIT_KB=<kb>`

To also build `mox-sim-vpi` (required for cocotb lessons):

```
MOX_WASM_TARGETS="mox-verilog mox-sim mox-bmc mox-sim-vpi" npm run build:mox
```

## Scripts

- `npm run dev`
- `npm run preview`
- `npm run test:e2e`
- `npm run setup:pyodide`
- `npm run setup:mox`
- `npm run build:mox`
- `npm run local-publish:mox`
- `npm run bootstrap:repro`

## Optional Runtime Overrides

In `.env` (copy `.env.example`):

- `VITE_MOX_VERILOG_JS_URL`
- `VITE_MOX_VERILOG_WASM_URL`
- `VITE_MOX_SIM_JS_URL`
- `VITE_MOX_SIM_WASM_URL`
- `VITE_MOX_BMC_JS_URL`
- `VITE_MOX_BMC_WASM_URL`
- `VITE_MOX_SIM_VPI_JS_URL` (cocotb lessons)
- `VITE_MOX_SIM_VPI_WASM_URL` (cocotb lessons)
- `VITE_PYODIDE_URL` (cocotb lessons, default: `/pyodide/pyodide.js`)
- `VITE_MOX_VERILOG_ARGS`
- `VITE_MOX_SIM_ARGS`
- `VITE_MOX_BMC_ARGS`

## Offline Mode

- Runtime assets are lazy-loaded by default (toolchain wasm, Surfer, Pyodide, z3).
- The header includes a "Download offline bundle" button that prefetches and caches runtime assets for offline use.
- For local/offline cocotb, install Pyodide assets once:
  - `npm run setup:pyodide`
- Keep runtime URLs same-origin (default `/mox/*`, `/z3/*`, `/surfer/*`, `/pyodide/*`) for robust offline behavior.

## Runtime Notes

- Runtime uses a real 2-stage wasm toolchain by default:
  - `mox-verilog` lowers SV/SVA/UVM source to MLIR
  - `mox-sim` executes lowered MLIR and emits VCD for the waveform pane
- Tool invocations run in isolated Web Workers to avoid global Emscripten symbol collisions and re-entry issues.
- UI includes a `self-check` action in the Runtime panel to validate artifact compatibility.
- Waves tab appears automatically only when a valid VCD is generated.

## CI

- `.github/workflows/ci.yml` builds with pinned toolchain requirements:
  1. install Node 22
  2. install emsdk 4.0.21
  3. run `scripts/setup-surfer.sh`
  4. run `scripts/setup-pyodide.sh`
  5. run `scripts/setup-mox.sh` (pinned MOX ref)
  6. run `scripts/build-mox-wasm.sh`
  7. run `npm run local-publish:mox`
  8. run `npm run build`

## E2E

- `npm run test:e2e -- e2e/waveform.spec.js`
- Includes:
  - non-mock pipeline check (`mox-verilog` + `mox-sim`, waveform generated)
  - Surfer waveform render check when browser WebGL support is available in the test environment
