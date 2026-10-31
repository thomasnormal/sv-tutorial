# sv-tutorial

Svelte-based interactive tutorial shell for SystemVerilog, SVA, and UVM.

The [curriculum tracker](CURRICULUM.md) is the source of truth for lesson order,
prerequisites, and quality scores. Completed lessons include starter and solution
source plus a runnable testbench with labelled PASS/FAIL output where the lesson
can be checked in simulation.

The build-generated [`Lesson status`](/status) page lists the current browser
result for every lesson. Each lesson carries the same status badge; lessons
with a Mox or environment limitation include the measured diagnostic, the
relevant IEEE clause, a browser-friendly fallback, and a native-Mox command.

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for setup, lesson authoring, validation,
and pull-request guidance.

## Reproducible Requirements

Pinned versions are centralized in `scripts/toolchain.lock.sh`:

- Node major: `22`
- Emscripten (emsdk): `4.0.21`
- MOX repo: `https://github.com/normal-computing/mox.git` (ref and LLVM ref are
  read from `scripts/toolchain.lock.sh`)

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

## Keyboard Controls

- Focus a panel separator and press **Arrow** keys to resize it; hold **Shift** for a larger step.
- Press **Ctrl+Enter** (or **Cmd+Enter**) to run the current lesson, and **Escape** to close open menus or dialogs.

## Runtime Notes

- Runtime uses a real 2-stage wasm toolchain by default:
  - `mox-verilog` lowers SV/SVA/UVM source to MLIR
  - `mox-sim` executes lowered MLIR and emits VCD for the waveform pane
- UVM lessons are currently qualified in interpreter mode only; `--mode=compile`
  does not yet run the UVM-bench rows. Native receipt runs therefore report the
  interpreter as the supported UVM path until the corresponding Mox AOT rows
  land.
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

## Re-running the published lesson matrix

The 109-case browser matrix is reproducible against any Mox WASM directory. A
new Mox build from the fleet normally lands under
`/scratch/thomas-ahle/tmp/sv-tutorial/...`; pass that build directory to the
runner:

```bash
scripts/run-matrix.sh /scratch/thomas-ahle/tmp/sv-tutorial/<build>/bin
```

The runner temporarily serves that directory as `static/mox`, visits every
lesson's run and verify path, and rewrites
`docs/mox-bugs/mox-wasm-item16-failures.md` with the measured failure table.
It then runs `npm run build`, whose prebuild step regenerates the status page
and lesson badges from that table. The temporary artifact handoff is removed
when the command exits; the generated census and status page remain for review.

For a focused rerun, set `MATRIX_SLUGS` to a comma-separated list and send the
partial census to a temporary path, for example:

```bash
MATRIX_SLUGS=cocotb/first-test,cocotb/clock-and-timing \
MATRIX_OUTPUT=/tmp/cocotb-matrix.md \
MATRIX_MOX_SHA=<mox-commit> scripts/run-matrix.sh /scratch/thomas-ahle/tmp/sv-tutorial/<build>/bin
```

Each run also writes a complete four-column result table to `results/<mox-sha>.md`.
The SHA is inferred from a Mox checkout ancestor when possible; for a fleet
artifact directory, provide it explicitly with `MATRIX_MOX_SHA=<git-sha>`. Keep
these files as the build history, then compare two builds with:

When an artifact is a documented fallback rather than a freshly rebuilt
checkout, record that with `MATRIX_ARTIFACT_NOTE="..."`; the note appears in
the result history and status page.

```bash
scripts/matrix-diff.sh results/<old-sha>.md results/<new-sha>.md
```

The `/status` page generates its **What changed** section from the two newest
result tables. A fleet build copied from `/scratch/thomas-ahle/tmp/sv-tutorial/`
should therefore be run as, for example:

```bash
MATRIX_MOX_SHA=<mox-commit> scripts/run-matrix.sh /scratch/thomas-ahle/tmp/sv-tutorial/<build>/bin
```
