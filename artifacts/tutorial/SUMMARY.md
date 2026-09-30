# sv-tutorial: make lessons pass, fix wrong content, make the QA honest

## 2026-09-30 continuation

The repository baseline is `24175be` (`origin/main`). The required install,
unit-test, and production-build commands pass. Browser installation cannot
install OS dependencies without sudo, but an existing Chromium ran the focused
tests. The new findings and receipts are recorded at the top of
`artifacts/tutorial/broken-census.md` and `artifacts/tutorial/content-census.md`.

Branch `fleet/tutorial-fixes` starts at `origin/main` (`24175be`). Each fix adds a vitest or e2e test that
fails before the commit and passes after it. The complete findings are in `broken-census.md` (things that break)
and `content-census.md` (things that are wrong against IEEE 1800-2023 / 1800.2-2020).

## What was broken
- **The whole-tutorial QA could not fail.** It asserted "no `exit code: 1`" right after clicking Run, before any
  output appeared. Its lesson list was hand-copied and had drifted: 62 of 73 lessons, with stale titles. Once
  fixed, 23 of 73 solutions failed in the browser.
- **CI is red on main.**
  - `ci`: the UVM smoke hits a `mox-verilog` `Aborted()` while compiling uvm-core. The `uvm_re_*` lines are remarks, not the cause.
  - `uvm-nightly`: red since 2026-03.
  - `e2e-waveform`: cancelled at its 20-minute limit, because the specs expect `mox-verilog`/`mox-sim` for lessons
    that now run through `mox-run`.
- **The pinned WASM (release `mox-wasm`, Mox 805b42d2) breaks 16 lessons that current native Mox runs correctly:**
  - all 12 UVM lessons;
  - Interfaces, Modports and Tasks ("memory access out of bounds");
  - FSM (false "mem driven by always_ff").
- **Mox BMC crashes on sequence-basics Verify** (assert with a pass action; GAPS.md TUT-SVA-4).
- **Every cocotb lesson hung the page.** mox-sim-vpi in the pinned WASM aborts when the simulation starts (native Mox
  and real cocotb 2.0.1 pass all four). The abort happened during an Asyncify rewind, so the worker never answered
  and Run stayed on "Cancel" forever. The shim also lacked `ReadOnly` and cocotb 2.0's `unit=` keyword, which two
  lessons use.
- **The waveform toolbar's transition buttons did nothing on lessons whose signals change at time 0.** The viewer
  skipped all changes at the dump time when picking the signal to focus, so on modules-and-ports it picked none.
- **The lessons/waveform e2e specs were stale or vacuous:** they expected the old tool names, used a removed lesson
  and an old toolbar protocol, and checked BMC logs before BMC had printed anything.
- **The MLIR lessons never ran their testbenches.** Run simulated only the focus file's design module, so
  `*_tb.mlir` checks never executed. seq and lowering failed outright, and intro and comb "passed" without printing
  anything.

## What was wrong (content)
Fixed here:
- **Constrained Randomization:** the solution could not pass on any simulator. Inline `with {}` constraints are
  added to the class constraints, not substituted for them (§18.7), so the "override" was infeasible. `low_bank_c`
  is now `soft` (§18.5.13), and the description explains why.
- **Dynamic Arrays and Queues:** the solution hung on every simulator.
  - `logic [3:0] v = q.pop_front();` in a loop body is a static variable, so its initializer runs once (§6.21).
    It is now `automatic`.
  - `logic'(i)` truncated the addresses to 1 bit (§6.24.1). It is now `4'(i)`.
  - The testbench now checks the queue size after the pushes.
- **assume property:** the assume `rst |-> state == 0` constrained a design output. It failed in simulation at the
  first edge (state X), and it did not rule out a non-reset initial state in BMC. It is now
  `initial assume property (@(posedge clk) rst);` (§16.14.6), with the description reworded. Xcelium passes it.
  Mox still fails Run, because it evaluates the initial assume at every edge (TUT-SVA-7).
- **UVM:**
  - `uvm_top` and `finish_on_completion` are not in IEEE 1800.2-2020 (F.7). Replaced with
    `uvm_root::get().set_finish_on_completion(0)`.
  - `mem_item` fields were used in `uvm_field_*` macros before their declaration (§6.5).
- **Coverage lessons printed 0%:** the browser now enables coverage collection when a design declares a
  `covergroup`.

Still open (author decisions; see content-census.md): about 100 rows. The main ones:
- Most BMC lessons check a monitor whose inputs are all free, so Verify finds a counterexample for the *solution*.
- Several SVA explanations are wrong: checker `|=>` window, throughout `mosi[*8]`, `intersect` burst, recursive
  tautology, reject_on vs sync_reject_on, `.triggered` restriction.
- `$bits(16)` is described as 4 (it is 32).
- coverpoint-bins has no ignore_bins.
- The modports snippet omits `clk`.
- Weak testbenches in 8 SV lessons accept wrong designs (mutations print PASS).

## What changed
One commit per issue, each with the test that fails before it and passes after:

| Commit | Change | Test |
|---|---|---|
| `24e2a82` | uvm: declare mem_item fields before the uvm_field_* macros | `src/lessons/lesson-sources.test.js` |
| `45c87e7` | uvm: use `uvm_root::get().set_finish_on_completion(0)`, not `uvm_top` | `src/lessons/lesson-sources.test.js` |
| `67d45ef` | runtime: enable coverage collection for designs with covergroups | `src/runtime/mox-adapter.test.js` |
| `cc306c9` | e2e: the all-lessons QA waits for each run and names known failures (`test.fail` + reason) | `e2e/qa-all-lessons.spec.js`, `e2e/lesson-run.js` |
| `44fd83e` | sv/randomization: `soft` low_bank_c | QA run entry (known failure before, removed) |
| `440d8d6` | sv/queues-arrays: `automatic` pop variable, `4'(i)`, size check, description | QA run entry (known failure before, removed) |
| `3c5b151` | mlir: run the `@tb` testbench together with the design | `src/runtime/mox-adapter.test.js`, `e2e/mlir-run.spec.js`, QA entries removed |
| `c9cb02a` | sva/formal-assume: assume reset at the first edge | `src/lessons/lesson-sources.test.js` (assumptions name only inputs) |
| `e119e6d` | e2e: lessons/waveform specs expect `$ mox-run` | `e2e/lessons.spec.js`, `e2e/waveform.spec.js` |
| `6564184` | cocotb: end the run when the simulator aborts instead of hanging | `e2e/cocotb-run.spec.js` |
| `8783379` | cocotb: shim `ReadOnly` (cbReadOnlySynch, §38.36.2) and `unit=` | `src/runtime/cocotb-shim.test.js`, `src/runtime/cocotb-worker-source.test.js` |
| `a8dcd88` | waveform: count changes at the dump time when picking the focused signal | `src/lib/vcd.test.js`; toolbar and transition_next e2e |
| `46c7eed` | e2e: update the stale waveform and formal checks | `e2e/waveform.spec.js`, `e2e/lessons.spec.js` |
| `a10a082` | e2e: the QA waits for hydration before clicking (a lost Run click flaked 1 of 90) | reproduced by delaying the app's JS 1.5 s |

### Landed capability chapters

Added five one-lesson chapters for user-facing SystemVerilog capabilities
landed in Mox between September 22 and September 30, 2026. The UDP chapter
tracks landing tip `36b040f6190c`; the pinned browser WASM remains unchanged.

| Lesson | IEEE reference | Mox native | Xcelium/refdiff | Evidence |
|---|---|---|---|---|
| `sv/macro-formal-continuation` | §22.5.1 | starter FAIL; solution PASS in interpreter and compile modes | solution PASS; output equal | `artifacts/tutorial/capability-receipts/*macro-formal-continuation*` |
| `sv/struct-field-refs` | §7.2.1 | starter FAIL; solution PASS in interpreter and compile modes | solution PASS; output equal | `artifacts/tutorial/capability-receipts/*struct-field-refs*` |
| `sv/indexed-part-select` | §11.5.1 | starter FAIL; solution PASS in interpreter and compile modes | solution PASS; output equal | `artifacts/tutorial/capability-receipts/*indexed-part-select*` |
| `sv/nested-child-input` | §§23.2.2, 9.4.2 | starter FAIL; solution PASS in interpreter and compile modes | solution PASS; output equal | `artifacts/tutorial/capability-receipts/*nested-child-input*` |
| `sv/sequential-udp-init` | §§29.3.2, 29.6, 29.7 | starter FAIL; solution PASS in interpreter and compile modes | starter both_fail; solution PASS; output equal | `artifacts/tutorial/capability-receipts/*sequential-udp-init*` |

The capability receipt summaries are in
`artifacts/tutorial/capability-receipts/{summary,final-summary}.tsv`.
Their corrected-tip hashes, native/reference argv, and the final build/e2e
receipt are recorded in
`artifacts/tutorial/capability-receipts/PROVENANCE.md`.

### Compile-mode status chapter

`sv/compile-mode-status` is a runnable native compile smoke test plus a status
page for the current AOT census. Its browser run is interpreter-backed; native
Mox `--mode=compile` passes the solution, while the S4 receipt for the five
frozen UVM rows is honestly `0/5` with all rows classified `HELD`. The chapter
and durable receipts are in `src/lessons/sv/compile-mode-status/` and
`artifacts/tutorial/compile-mode-status/`.

## WASM rebuild (done locally, NOT published; release `mox-wasm` is unchanged)
Built with emsdk 4.0.21 from Mox main `9c5418532b9` (and landing `ea0fcd2`): mox-verilog, mox-sim, mox-bmc and
mox-lec. Mox has no wasm target for mox-run (GAPS TUT-WASM-MOXRUN), so two more commits went in:
- `d760369`: the adapter falls back to mox-verilog + mox-sim when `mox-run.wasm` is absent (vitest).
- `24175be`: the build script passes C++20 to the NATIVE host sub-build (GAPS TUT-WASM-NATIVE-CXX20).

The all-lessons QA on the rebuilt WASM gave 63 passed and 11 failed (log: `ci/qa-wasm-main-9c54.log`). Every
failure is a Mox gap, so **do not publish this WASM yet**:
- TUT-WASM-UNLINKED-RUNTIME: the wasm mox-sim cannot resolve the `__mox_sim_*` runtime hooks. This breaks the
  covergroup, coverpoint-bins, classes and queues lessons.
- TUT-WASM-CROSS-ABI: mox-verilog asserts on any `cross` (a wasm32 ABI size check).
- TUT-WASM-ALLOCA-RETIRE: mox-sim aborts at teardown after an event wait or a queue push. This breaks Events and
  Randomization.
- TUT-BMC-LTL-NOT: mox-bmc fails to legalize `ltl.not`, which breaks Immediate Assertions, Recursive Properties and
  assume property Verify. Native Mox fails the same way.
- Concurrent Assertions in Simulation: this is not a bug. The new mox-sim reports the deliberate `req_gnt_check`
  failure. The matching QA change is in `qa-concurrent-sim-with-new-wasm.patch`, which is uncommitted on purpose:
  it would fail against the old WASM. Apply it together with the publish.

Once these are fixed, publish, update `scripts/toolchain.lock.sh` and the README pins, and delete the `test.fail`
entries that then report "unexpectedly passed".

**Update 18:55 UTC: WASM with native 0033 (TUT-WASM-ALLOCA-RETIRE fix).** Mox 9c54 + `0033` rebuilt locally. The QA
gives 67 passed and 7 failed (log `ci/qa-wasm-9c54-0033.log`). Events, Classes and Objects, Randomization and Concurrent Assertions
in Simulation (with the held QA patch) now pass. The 7 left are UNLINKED-RUNTIME (15, 16, 19), CROSS-ABI (17) and
BMC-LTL-NOT (25, 47, 48). Still do not publish; 0033 is in review.

**CI's UVM smoke (`ci` run 36034279627, old release WASM).** The `uvm_re_*` lines are compile-time remarks, not
a runtime `UVM/DPI/REGEX` error. `mox-verilog.wasm` itself aborts while compiling uvm-core (log:
`ci/ci-36034279627-failed.log`). Recheck it against the rebuilt WASM before planning any DPI bridge change.

## Left open (documentation and a legacy harness; no behaviour change, so no test)
- B14: `scripts/test-all-lessons.mjs` predates mox-run and accepts any `PASS` line. Retire it in favour of
  `e2e/qa-all-lessons.spec.js`, or port it to mox-run and require a final PASS with exit 0.
- B15: CLAUDE.md still describes `src/tutorial-data.js` / `App.svelte`. Lessons are in `src/lessons/` and the app
  is SvelteKit.

## Needs a Mox fix (GAPS.md)
- TUT-SVA-3: `disable iff` over a Boolean property / compound immediate assert crash BMC (`ltl.not`).
- TUT-SVA-4: an assert with a pass action crashes BMC.
- TUT-SVA-2: weak sequences refuted by BMC.
- TUT-SVA-1: ranged-delay covers never fire.
- TUT-SVA-5: late failure reporting.
- TUT-SVA-6: reject_on treated as synchronous.
- TUT-UVM-DIAG: diagnostics lost under `--uvm-path`.
- TUT-SVA-7: an `initial` assert/assume property is evaluated at every clock edge instead of once (§16.14.6); blocks
  formal-assume Run.
- TUT-VCD-DUMPVARS-TIME: the VCD writer puts `#0` inside `$dumpvars` (§21.7.2.1). The viewer now tolerates it.

## How to test
Install the runtime assets first: `scripts/setup-surfer.sh` and `scripts/setup-pyodide.sh` (the waveform and cocotb
tests are meaningless without them), plus the pinned WASM in `static/mox`. Then run `npx vitest run` and
`npx playwright test e2e/qa-all-lessons.spec.js e2e/mlir-run.spec.js e2e/cocotb-run.spec.js e2e/lessons.spec.js e2e/waveform.spec.js`.
Stop any running `vite preview` on port 4173 first, because Playwright reuses an existing server.

Last verified at `a10a082`: vitest 52/52; the five e2e specs give 90 passed and exit 0. Each known failure is a `test.fail`
with its reason, so it will show up as "unexpectedly passed" once fixed.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
