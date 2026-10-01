# Missing generic receipt matrix

This matrix closes the generic-receipt gap for the 18 lesson slugs that were
not covered by the original `artifacts/tutorial/receipts/*.json` set. The
seven post-September capability chapters have their own receipt bundles and
are intentionally not duplicated here.

Base: `origin/main` at `24175be0f38db6f468e73883384b74dc01713a2f`.
Native Mox receipts use `/var/tmp/thomas-ahle/wt/landing/build-dev-fast`,
`taskset -c 0-79`, and a 30-second process guard. The native binary reports
Mox `e81e1f9272f85df16ed1a479d2b3eba670f022f1`; this identifies the existing
box build and does not imply that the browser WASM was rebuilt.

## Results

| Lesson | Native receipt | Result | Evidence |
|---|---|---|---|
| `uvm/constrained-random` | Mox interpret / compile | PASS / FAIL (AOT wall guard) | `constrained-random-{interpret,compile}.log` |
| `uvm/monitor` | Mox interpret / compile | FAIL / FAIL (`mem_agent.drv` unresolved) | `monitor-{interpret,compile}.log` |
| `uvm/env` | Mox interpret / compile | FAIL / FAIL (`mem_agent.drv` unresolved) | `env-{interpret,compile}.log` |
| `uvm/covergroup` | Mox interpret / compile | FAIL / FAIL (expected `;`) | `covergroup-{interpret,compile}.log` |
| `uvm/cross-coverage` | Mox interpret / compile | FAIL / FAIL (expected `;`) | `cross-coverage-{interpret,compile}.log` |
| `uvm/coverage-driven` | Mox interpret / compile | FAIL / FAIL (`mem_agent.drv` unresolved) | `coverage-driven-{interpret,compile}.log` |
| `uvm/factory-override` | Mox interpret / compile | FAIL / FAIL (`uvm_spell_chkr.svh`) | `factory-override-{interpret,compile}.log` |
| `uvm/ral` | Mox interpret / compile | FAIL / FAIL (`uvm_reg_field` unresolved) | `ral-{interpret,compile}.log` |
| `rtl/rtl-to-gates` | Mox interpret / compile | PASS / PASS | `rtl-to-gates-{interpret,compile}.log` |
| `rtl/synthesis-gotchas` | Mox interpret / compile | PASS / PASS | `synthesis-gotchas-{interpret,compile}.log` |
| `mlir/intro` | Mox sim, design + testbench | PASS | `mlir-intro.log` |
| `mlir/comb` | Mox sim, design + testbench | PASS | `mlir-comb.log` |
| `mlir/seq` | Mox sim, design + testbench | PASS | `mlir-seq.log` |
| `mlir/lowering` | Mox sim, design + testbench | PASS | `mlir-lowering.log` |
| `cocotb/first-test` | generated Mox Icarus driver | BLOCKED | `first-test-cb18.log` |
| `cocotb/clock-and-timing` | generated Mox Icarus driver | BLOCKED | `clock-and-timing-cb18.log` |
| `cocotb/edge-triggers` | generated Mox Icarus driver | BLOCKED | `edge-triggers-cb18.log` |
| `cocotb/clockcycles-patterns` | generated Mox Icarus driver | BLOCKED | `clockcycles-patterns-cb18.log` |

The cocotb native smoke is marked `BLOCKED`, not `PASS`: the box has
`cocotb` 2.0.1 but not `cocotb-test`, and the temporary compatibility install
still fails before simulation because `cocotb_test` imports the removed
`cocotb.simulator` module under the available wheel. The browser-specific
receipt comes from the full Playwright run and remains governed by the
pinned WASM/Mox status in `artifacts/tutorial/broken-census.md`.

## Commands

RTL solution runs use:

```text
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=<interpret|compile> --max-wall-ms=25000 src/lessons/rtl/<lesson>/<design>.sol.sv src/lessons/rtl/<lesson>/tb.sv
```

MLIR runs concatenate the lesson's design and `*_tb.mlir` into one temporary
input, then use:

```text
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-sim --top tb --max-wall-ms=25000 /tmp/tutorial-<lesson>.mlir
```

UVM runs use the staging and include-root rules in
`scripts/test-all-lessons.mjs`, with `--uvm-path static/mox/uvm-core` and
`-I static/mox/uvm-core/src`; the exact output is preserved in each log.
The cocotb attempt used the generated `mox-cocotb-driver.py` and is retained
to make the missing Python prerequisite reproducible.

## Browser receipt

The complete Playwright matrix, including every route and the current pinned
browser runtime, is preserved at
`artifacts/tutorial/e2e/tutorial-full-e2e-20261001.log`. The command was
`npm run test:e2e`; it completed with 177 passed and 54 failed in 29.6 minutes
(exit 1). The failures are not hidden: the log includes the four cocotb VPI
failures, UVM compile failures, formal/Mox gaps, and known stale-browser
limitations. Its SHA-256 is
`e50f079ac80421689521ac0d4388bfe0df9be5669fbc407dc9161f14408aa0d9`.
