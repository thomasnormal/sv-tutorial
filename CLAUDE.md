# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
npm ci                # Install the locked dependencies
npm test              # Vitest unit and source-contract tests
npm run test:e2e      # Playwright browser tests
npm run dev          # Start dev server (Vite)
npm run build        # Production build
npm run preview      # Preview production build

scripts/setup-mox.sh          # Clone/update the MOX fork into vendor/mox
scripts/setup-mox.sh <dir>    # Clone into a custom directory

scripts/setup-surfer.sh         # Download Surfer waveform viewer web build into public/surfer
scripts/setup-surfer.sh <dir>   # Download into a custom directory
```

The unit tests use Vitest and the browser tests use Playwright. Keep focused
tests close to the lesson or runtime contract they protect.

## Architecture

This is a SvelteKit static app using Svelte 5. The lesson route is
`src/routes/lesson/[part]/[name]/+page.svelte`; the root route redirects legacy
`?lesson=N` URLs in `src/routes/+page.js`.

### Lesson Data (`src/lessons/`)

The catalog hierarchy and flat lesson list live in `src/lessons/index.js`.
Titles, focus files, runners, and tops live in `src/lessons/meta.js`.
Each lesson keeps its starter source, solution source, and
`description.html` beside the lesson directory. `src/lib/tutorial-data.js` is
only the compatibility re-export used by the SvelteKit route loaders.

### Lesson State (`src/routes/lesson/[part]/[name]/+page.svelte`)

The lesson page owns the editor workspace, run state, runtime logs, and
waveform state. Shared completion and settings state lives in
`src/lib/stores/`. Lesson file merging and top-name inference are in
`src/lib/lesson-utils.js`.

### MOX WASM Runtime (`src/runtime/`)

Two files handle the runtime bridge:

**`mox-config.js`** reads Vite env vars and resolves the separate
`mox-verilog`, `mox-sim`, `mox-bmc`, `mox-lec`, and cocotb runtime URLs under
`/mox/`.

**`mox-adapter.js`** lazy-loads those workers. Plain SystemVerilog lessons
use the unified `mox-run` path; UVM lessons use the bundled UVM compile path;
MLIR lessons use `mox-verilog` followed by `mox-sim`; formal lessons use
`mox-bmc` or `mox-lec`. The adapter writes workspace files under the worker's
`/workspace/` filesystem and reads VCD output from `/workspace/out/`.

### MOX WASM Artifacts

The generated runtime assets live under `static/mox/` and are gitignored.
Use the pinned values in `scripts/toolchain.lock.sh` with the setup/build
scripts to produce them.

Without these files, the runtime reports that the Mox artifacts are missing.

### Surfer Waveform Viewer (`src/lib/components/WaveformViewer.svelte`)

The waveform pane embeds [Surfer](https://surfer-project.org/) via an `<iframe src="/surfer/">`.

- Surfer must be self-hosted (same origin) so that blob URLs created from in-memory VCD data are fetchable by the iframe.
- When MOX produces a VCD string (`lastWaveform.text`), the component creates a `Blob` → `URL.createObjectURL` and sends `{ command: 'LoadUrl', url }` via `postMessage` with progressive retries (0 / 800 / 2200 / 4500 ms) to absorb Surfer's WASM initialization time.
- If `/surfer/index.html` is not found (HEAD 404), the component shows a prompt to run `scripts/setup-surfer.sh`.

Install artifacts:
```bash
scripts/setup-surfer.sh    # downloads from GitLab CI → public/surfer/
```

Copy `.env.example` to `.env` to configure runtime overrides without modifying source.
