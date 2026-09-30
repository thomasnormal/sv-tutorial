# sv-tutorial BROKEN census

## Current-main refresh — 2026-09-30

This refresh is against the fetched repository tip `24175be` (`origin/main`;
the coordinator-referenced `bcdf57717c1` is a Mox landing tip and is not a
commit in this repository). Required baseline receipts:

- `npm ci`: exit 0; 143 packages installed; npm reports 10 audit findings.
- `npm test`: exit 0; 12 files / 53 tests passed.
- `npm run build`: exit 0; Svelte emits existing a11y and duplicate-output warnings.
- `npx playwright install --with-deps chromium`: exit 1 because sudo cannot
  prompt on this host. Chromium was nevertheless already available, so the
  suite ran.
- `npx playwright test e2e/qa-all-lessons.spec.js`: exit 1; the run reached
  the runtime matrix, then was stopped after the UVM portion began. Observed
  failures include unlinked `__mox_sim_register_host_allocation`, unlinked
  `__mox_sv_open_array_copy_or_register_bounds`, and BMC `ltl.not` legalization.
- `npx playwright test e2e/mobile-nav.spec.js e2e/split-view.spec.js e2e/offline.spec.js`:
  exit 1; 6 passed, 3 failed because `sv/priority-enc` is not a current route.

The local browser assets are the 2026-09-24 rebuilt artifacts and contain no
`mox-run.js`/`mox-run.wasm`; plain SV therefore logs the fallback
`mox-verilog` + `mox-sim` path. The deployed release remains a separate WASM
qualification concern and is not changed by this branch.

The eight sampled `uvm-nightly` runs (September 22–29, 2026) all reproduce the
same compile-stage `Aborted()` in `mox-verilog` while importing uvm-core; the
`uvm_re_*` lines are compiler remarks, not an executed regex failure. The
full raw logs are in `/tmp/tutorial-uvm-nightly-*.log` when collected by the
coordinator.

Branch `fleet/tutorial-fixes` (from main 1d90d97). "Broken" means something a learner or CI can observe
failing: a crash, a red workflow, or a solution that does not pass. Content that runs but is *wrong* is in
content-census.md.

Evidence sources:
- **Browser QA** (before any fixes: 50 passed / 23 failed): `e2e/qa-all-lessons.spec.js`, rewritten on this branch. It covers every lesson in
  `src/lessons/meta.js` and waits for each run to finish. The full log is at `/tmp/tut/qa-new.log`.
- **Pinned WASM**: `gh release mox-wasm`, "built from normal-computing/mox @ 805b42d2", published 2026-06-25.
- **Native Mox**: landing `build-dev-fast`.
- **Xcelium**: via `fleet/bin/refdiff` / `refsim`.

Severity: **S1** = a learner cannot complete a lesson, or CI is red. **S2** = a wrong result is visible.
**S3** = tooling or documentation rot.

| # | failure | reproducer | root cause | proposed fix | sev | status |
|---|---|---|---|---|---|---|
| B1 | The old whole-tutorial QA was vacuous and passed while lessons were broken. It asserted `not.toContainText('exit code: 1')` straight after clicking Run, which resolves before the run has produced any output. Its hardcoded lesson list (62 entries) also had drifted from meta.js (73 lessons, stale titles such as "Tasks and Functions"). | `git show main:e2e/qa-all-lessons.spec.js` | The spec never waited for the run to end, and the lesson list was copied instead of derived. | Derive LESSONS from meta.js. `runAndWait()` waits for `$ mox` and then for the button to leave its "Cancel" state, and the test asserts on the finished log (`e2e/lesson-run.js`). | S1 (hides every other item) | fixed on branch |
| B2 | The `uvm-nightly` workflow has failed every night since 2026-03. The `ci` workflow's UVM smoke fails on main (run 28242548385): `mox-verilog` hits `Aborted()` right after `uvm_report_error("UVM/DPI/REGEX", uvm_re_buffer())`. | `gh run view 28242548385 --log-failed`. In the browser, open any `uvm/*` lesson and click Run. | This is a defect in the pinned WASM (805b42d2). Current native Mox compiles and runs all 12 UVM solutions. | **WASM rebuild required** (emscripten is not available in this lane). | S1 | needs WASM rebuild |
| B3 | Two-Always Moore FSM (`sv/fsm`, and every lesson that instantiates `sram.sv`) fails: `sram.sv:10:13: error: variable 'mem' driven by always_ff procedure`, `# mox-run exit code: 1`. | QA [14], or Solve then Run in the browser | This is a false multiple-driver diagnostic in the pinned mox-run WASM. Native Mox and Xcelium both accept the design. | **WASM rebuild required** | S1 | needs WASM rebuild |
| B4 | Interfaces, Modports and Tasks crash: `# runtime unavailable: RuntimeError: memory access out of bounds`. | QA [9], [10], [12] | This is a trap inside the pinned mox-run WASM. Native Mox runs all three solutions and prints PASS. The adapter's mox-run path retries only on `Aborted(`/OOM (`isRetryableSimAbortText`), so this is not retried. | **WASM rebuild required**. See the adapter-retry note below. | S1 | needs WASM rebuild |
| B5 | Dynamic Arrays and Queues never finishes: the log fills with `pop: x`, the renderer grows to about 6.5 GB, and the run is still in "Cancel" after 180 s. | QA [19]. `refdiff addr_buf.sol.sv`: Xcelium TIMEOUT and Mox TIMEOUT. | The lesson content is wrong (not the WASM; this corrects an earlier draft). `logic [3:0] v = q.pop_front();` in the loop body declares a static variable, and its initializer runs once, at time 0, while q is empty. So the loop never pops (§6.21 requires an explicit `static` there). `logic'(i)` also truncates the addresses to 1 bit (§6.24.1). | Use `automatic logic [3:0] v = q.pop_front();` and `4'(i)`, and check the queue size after the pushes. After the fix both simulators PASS. | S1 | fixed on branch |
| B6 | The Constrained Randomization solution fails on every simulator: `*W,SVRNDF randomize method call failed`, `FAIL: addr not in high bank`. | QA [21]. `refdiff rand_txn.sol.sv`: Xcelium FAIL (exit 2), Mox FAIL (exit 1). | The lesson content is wrong: inline `with {addr inside {[8:15]}}` is solved *together with* the class constraint `low_bank_c {addr inside {[0:7]}}` (IEEE 1800-2023 §18.7), which leaves no solution. | Make `low_bank_c` `soft` (§18.5.13) and explain it in the description. After the fix both simulators PASS. | S1 | fixed on branch |
| B7 | UVM covergroup, cross-coverage and coverage-driven report 0% coverage. coverage-driven hits its `$fatal` after 50 iterations, and covergroup raises `UVM_ERROR`. | Native `mox-run` without `--coverage-report`, or Xcelium without `-coverage functional` | Mox (like Xcelium) samples covergroups only when coverage collection is on, and the browser never enabled it. | The adapter adds `--coverage-report` to mox-run/mox-sim when a file declares a `covergroup` (vitest in `mox-adapter.test.js`). | S1 | fixed on branch (the pinned WASM has the flag) |
| B8 | All 12 UVM lessons are rejected by a standard UVM: Xcelium's IEEE UVM gives `*E,CUVUNF uvm_top` and `*E,UNDIDN` (a field used in `uvm_field_*` before it is declared). | refsim on any `uvm/*/tb_top.sv` or `mem_item.sol.sv` | `uvm_top` and the `finish_on_completion` field are not in IEEE 1800.2-2020 (F.7.2.2, F.7.3.4). Using a variable before its declaration violates IEEE 1800-2023 §6.5. | Use `uvm_root::get().set_finish_on_completion(0)` and declare fields before the macros (vitest `src/lessons/lesson-sources.test.js`). | S2 | fixed on branch |
| B9 | Sequences and Properties Verify crashes: `'llhd.process' op cannot be handed off from llhd-structuralize-processes to llhd-eliminate-processes`, `# mox-bmc exit code: 1`. | QA [26]; `/tmp/tut/audit/repro/bmc_pass_action.sv` | This is a Mox BMC bug: a concurrent assert with a *pass* action block crashes the pipeline. The bug is also present in native Mox. | Fix in Mox (GAPS.md). | S1 | Mox bug |
| B10 | `disable iff` on a Boolean property, and immediate asserts on compound expressions, crash BMC (`failed to legalize operation 'ltl.not'`). This hits recursive, formal-assume and immediate-assert. | `/tmp/tut/audit/repro/bmc_disable_bool.sv`, `bmc_imm_compound.sv` | Mox BMC bug (also present in native Mox) | Fix in Mox (GAPS.md) | S1 | Mox bug |
| B11 | The assume property lesson fails in simulation: `SVA assumption failed at time 5000000 fs`. | QA [48]. Xcelium: `__assert_1 has failed` at 5 NS. | The lesson content is wrong: `assume property (rst \|-> state==0)` is checked at the first edge while `state` is still X. The lesson also never constrains the initial reset (§16.14.2). | Replace it with `initial assume property (@(posedge clk) rst);` (§16.14.6): the environment starts in reset. Verify (BMC) now passes in the browser. Xcelium passes the simulation, but Mox evaluates the initial assume at every clock edge (GAPS TUT-SVA-7), so Run still fails. | S1 | content fixed on branch; Run blocked by Mox gap TUT-SVA-7 |
| B12 | For nearly every BMC lesson, Verify on the *solution* reports "Assertion can be violated" (SAT). Only formal-intro and seq-args prove. | `/tmp/tut/audit/sva-bmc/all.txt` | Monitors whose inputs are all free are not constrained, so any property on them can be violated (§16.12.2). | Add a DUT or assumptions per lesson (content-census, systemic row) | S2 | open |
| B13 | `e2e/lessons.spec.js` and `e2e/waveform.spec.js` expect `$ mox-verilog`, `$ mox-sim` and `--mode interpret` for plain SV lessons. Since a369bce and c257a60 these run through `mox-run` without `--mode`, so both specs fail. The `e2e-waveform` workflow is cancelled at its 20-minute limit on main. | `npx playwright test e2e/waveform.spec.js` | The specs were not updated when the lessons moved to mox-run. | Expect `$ mox-run`, and drop the `--mode interpret` assertion. | S3 | fixed on branch |
| B14 | `scripts/test-all-lessons.mjs` (node harness) does not run against the current artifacts. It drives `mox-verilog` + `mox-sim` rather than `mox-run` (which the browser uses), and treats any line starting with `PASS` as a pass, so a half-correct design passes (counter mutation). | `node scripts/test-all-lessons.mjs` | The harness predates mox-run, and its pass detector is too weak. | Retire it in favour of the e2e QA, or port it to mox-run and require a final PASS with exit 0. | S3 | open |
| B15 | Documentation rot. README pins MOX `8e8ca87` / LLVM `972cd84`, `scripts/toolchain.lock.sh` pins `18483f66` / `aa3d6b37`, and the shipped release was built from `805b42d2`. CLAUDE.md describes `src/tutorial-data.js` / `App.svelte`, which no longer exist (lessons are in `src/lessons/`, and the app is SvelteKit). | `grep -n "MOX ref" README.md; cat scripts/toolchain.lock.sh` | Pins and documents are hand-copied and have drifted. | At the next WASM rebuild, set the lock to the built commit and make README refer to the lock file. Update CLAUDE.md. | S3 | open |
| B16 | MLIR lessons never run their testbench. Run simulates only the focus file's design module, so the `*_tb.mlir` checks never execute: intro and comb print nothing and "pass", while seq and lowering fail (mox-sim cannot interpret a bare `seq.hlmem` / `sv.reg` top). | QA [66]-[69] | `pickTopModules` uses the focus-derived top, and the adapter simulated a single `.mlir` file (`pickMlirSourcePath`). | Pick `tb` when a file defines `hw.module @tb`, and simulate all `.mlir` files as one module (vitest, `e2e/mlir-run.spec.js`). Native mox-sim prints PASS for all four. | S1 | fixed on branch |
| B17 | $isunknown fails its QA run on purpose: `tb.sv` injects X, and 3 SVA failures plus exit 1 are the intended outcome. | QA [24] | The lesson is working as designed; the QA only lacked a way to express that. | The QA expects the three named assertion failures and no runtime crash. | — | fixed in QA |
| B18 | Every cocotb lesson aborts in the browser: `Aborted(Assertion failed: detail::isPresent(Val) && "dyn_cast on a non-existent value" ... Casting.h)` right after `[mox-sim] Starting simulation`. Earlier QA runs missed this because `static/pyodide` was absent locally (`importScripts` failed) and the old checks did not require the shim's `PASS  name` line. | QA [70]-[73] after `scripts/setup-pyodide.sh`; `/tmp/tut/coco-probe.mjs` | Pinned mox-sim-vpi WASM (805b42d2). Native landing mox-sim `--vpi libcocotbvpi_ius.so` with real cocotb 2.0.1 passes all four lesson solutions. | WASM rebuild | S1 | needs WASM rebuild |
| B19 | After that abort, the Run button stays on "Cancel" forever and no result is reported. | QA [70]-[73] timed out at 180 s | An Emscripten abort inside an Asyncify rewind throws outside `callMain`'s try/catch, so `Asyncify.whenDone()` never settles and the worker never posts a result. | `Module.onAbort` resolves a promise raced against `whenDone()`; the result is `ok: false` (`e2e/cocotb-run.spec.js`). | S2 | fixed on branch |
| B20 | cocotb/edge-triggers and clockcycles-patterns use `ReadOnly` and `Clock(..., unit="ns")`, which the shim did not provide (ImportError / TypeError). | `src/runtime/cocotb-shim.test.js` | The shim implemented the cocotb 1.x subset only. | `ReadOnly` registers a zero-delay cbReadOnlySynch callback (§38.36.2), and Timer/Clock accept `unit=` as well as `units=`. The browser check is blocked by B18. | S1 | fixed on branch |
| B21 | Beyond B13, the lessons and waveform specs had five more stale or vacuous checks, and they hid a viewer bug. (1) The toolbar test expected command blobs from the transition buttons, which inject `MoveCursorToTransition` since 5e9b59a. (2) The transition_next test opened the removed `sv/priority-enc`. (3) concurrent-sim expected 'SVA assertion failed', but the lesson's else block prints its own `$error`. (4, 5) immediate-assert and sequence-basics checked the log before mox-bmc had printed anything, so they passed however BMC ended. The viewer bug: `firstTransitioningVar` dropped every change at the dump time that followed `$dumpvars`, so modules-and-ports auto-selected nothing and its transition buttons did nothing. Mox also writes `#0` inside `$dumpvars`, which Syntax 21-20 does not allow (GAPS TUT-VCD-DUMPVARS-TIME). | `npx playwright test e2e/lessons.spec.js e2e/waveform.spec.js` (after `scripts/setup-surfer.sh`) | The tests were not updated with the viewer/lesson changes; the viewer's VCD scan reset the time when it skipped the dump block. | Move the scan to src/lib/vcd.js and carry the dump time over (with a vitest). Update the specs, wait for runs to finish, and mark sequence-basics test.fail (TUT-SVA-4). | S3 | fixed on branch (a8dcd88, 46c7eed) |

## Adapter-retry note (B4)

`runOnce(withTraceAll=true)` is retried without `--trace-all` only when the error text matches
`isRetryableSimAbortText` (`Aborted(` or OOM). A `memory access out of bounds` trap is not retried there,
although it *is* treated as retryable for mox-verilog. This is recorded as an observation, not a fix: retrying
would only hide a runtime bug in the WASM, and the root-cause fix is the rebuild.

## Needs a WASM rebuild (cannot be done in this lane: emscripten is not installed)
B2, B3, B4, B18. After a rebuild at current Mox, re-run `npx playwright test e2e/qa-all-lessons.spec.js`.
The `test.fail` annotations for these lessons will then fail, which marks them for removal.
