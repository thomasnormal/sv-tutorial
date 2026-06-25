# Browser-Worker UVM Repro (`Malformed attribute storage object`)

This reproduces the MOX wasm UVM failure in the **browser worker** path
without using lesson UI clicks.

## Preconditions

1. `vendor/mox` is checked out and wasm artifacts are built.
2. Artifacts are synced into `public/mox`:

```bash
scripts/setup-mox.sh
npm run local-publish:mox
```

## Repro command

```bash
node scripts/repro-uvm-browser-worker-assert.mjs
```

Optional:

```bash
# Use an already-running dev server instead of spawning one.
REPRO_BASE_URL=http://127.0.0.1:4174 node scripts/repro-uvm-browser-worker-assert.mjs
```

## What it does

- starts Vite dev server on `http://127.0.0.1:43173` (`--strictPort`)
- opens Chromium headless via Playwright
- imports `createMoxWasmAdapter` from `/src/runtime/mox-adapter.js`
- runs compile-only (`simulate: false`) on minimal UVM files:
  - `/src/my_test.sv`
  - `/src/tb_top.sv`
- uses full UVM path (`--uvm-path /mox/uvm-core -I /mox/uvm-core/src`)

## Expected failure signature

- run result `ok=false`
- logs include both:
  - `Aborted(`
  - `Malformed attribute storage object`
- logs do **not** reach `$ mox-sim`

If this signature appears, the script exits `0` and prints:

`REPRODUCED: browser-worker UVM compile hit malformed-attribute abort`

If not, it exits non-zero.
