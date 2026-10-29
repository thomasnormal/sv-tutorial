# Full-UVM browser compile timeout

On 2026-10-29, after regenerating `static/mox` from the item-11 Mox pin
`b90b3a51a68b772a1510c837166afd6d429d8f20` (LLVM
`e3e4f161d0160f10dc7cbd746abd639dd740ecde`), the solved
`UVM: Functional Coverage` Playwright test was run against the production
preview. The worker loaded the UVM manifest and emitted the full command:

```text
$ mox-verilog --resource-guard=false --ir-llhd --timescale 1ns/1ns --single-unit --uvm-path /mox/uvm-core -I /mox/uvm-core/src --top tb_top -o /workspace/out/design.llhd.mlir /workspace/__svt_uvm_bundle.sv
```

It streamed the known UVM warning at
`uvm_config_db_implementation.svh:375:26` and the DPI import remarks, then
made no further progress for the 900-second Playwright polling timeout. No
`mox-sim` command and no `mox-verilog` exit line were produced. The same
behavior was reproduced by a direct Node WASM invocation: the full-UVM
compile remained active for several minutes and did not produce MLIR before
the bounded reproduction was stopped.

The generated artifacts themselves are healthy: `npm test` passes 27 files and
91 tests, including the real Mox WASM smoke tests, and `npm run build` passes.
This is a full-UVM browser compiler-performance/blocker record; it does not
change the lesson publication or quarantine rules.

On the resumed audit, the same behavior was reproduced with the existing
`uvm/reporting` lesson, which has only one bundled source root. A direct WASM
run using native source roots instead of the adapter's bundled single-unit
root also stalled for the same bounded five-minute run and emitted the same
UVM package diagnostics. Removing the optional RAL include from a temporary
copy of `uvm_pkg.sv` did not change the behavior. The timeout therefore
predates the three coverage lessons and is not caused by their coverage code,
root bundling, or the optional register-model sources.

The direct compile's complete diagnostic (once the bounded run was allowed to
finish) identifies the underlying Mox rejection:

```text
continuous-evaluator-effect-ownership-not-admitted construct=continuous-assignment clause=10.3
continuous evaluator cannot rematerialize operation llvm.load
failed to legalize operation 'moore.assign'
```

It points at the SRAM instance's `rdata` connection in `tb_top.sv`. A
temporary `always_comb` readback rewrite did not remove the rejection, so the
lesson-side workaround is not qualified.

The rejection is emitted by Mox
`lib/Conversion/MooreToCore/MooreToCoreContinuousAssign.cpp` in
`materializeContinuousAssignEvaluation` (the `source->emitError` at the
`findUnownedContinuousEvaluationEffect` result). The attached note identifies
the nested `LLVM::LoadOp`; the ownership walk treats it as an unowned effect
and refuses to rematerialize the evaluator. This source location is the
upstream handoff target; the tutorial checkout does not vendor or patch Mox.

On the next resumed audit, a temporary testbench with the SRAM child removed
entirely (the UVM environment and coverage code were unchanged; `rdata` was
driven by a local top-level combinational expression) still failed to produce
an exit or MLIR within a bounded six-minute direct WASM compile. A scan of all
local Mox refs found no post-`b90b3a51a68` change to this conversion or a
UVM-related fix. The child-output rejection is therefore a concrete first
diagnostic, but not the only full-UVM compilation blocker at this pin.

As a minimal browser-worker cross-check, `scripts/repro-uvm-browser-worker-assert.mjs`
was run with `--expect-fail --no-simulate` using only a small `uvm_test` class
and a `tb_top` that calls `run_test("my_test")` (no lesson package, SRAM, or
coverage sources). The worker started the same `createMoxWasmAdapter` compile
but produced no completion payload before the script's 180-second bound:

```text
Error: compile timed out after 180000ms
```

This minimal case therefore confirms that the browser-worker timeout is a
general UVM compilation stall at the current Mox artifacts, rather than a
failure specific to the published coverage lessons or their source topology.

On the first resumed audit after the goal was reopened, the same command was
run again against the unchanged artifacts:

```text
timeout 240 node scripts/repro-uvm-browser-worker-assert.mjs --expect-fail --no-simulate
```

The worker again entered `createMoxWasmAdapter` compilation and emitted no
completion payload. The script's browser cleanup remained stuck past its
180-second compile bound; an outer 240-second watchdog terminated it with:

```text
page.evaluate: Target page, context or browser has been closed
```

This is a fresh reproduction of the non-terminating minimal UVM browser
compile at Mox `b90b3a51a68`; no artifact or source revision changed during
the audit.

The second resumed audit repeated the same check on a fresh Vite port:

```text
REPRO_PORT=43174 timeout 240 node scripts/repro-uvm-browser-worker-assert.mjs --expect-fail --no-simulate
```

It again reached the browser-worker compile with no completion payload and was
terminated by the outer watchdog after the script's cleanup failed to return,
with the identical `page.evaluate: Target page, context or browser has been
closed` error. The Mox pin, WASM artifacts, and source tree were unchanged.

The third resumed audit used another fresh port and the same bounded command:

```text
REPRO_PORT=43175 timeout 240 node scripts/repro-uvm-browser-worker-assert.mjs --expect-fail --no-simulate
```

It again emitted only the browser-worker startup lines, never returned a
compile result, and ended under the outer watchdog with
`page.evaluate: Target page, context or browser has been closed`. This is the
third consecutive reproduction after the goal was resumed, with no Mox ref,
artifact, or source change; the lane remains blocked on an upstream Mox UVM
compile fix.

After the goal was reopened again, the first audit checked local Mox history
for a post-pin change to this conversion path. `origin/main` and all local
refs still resolve to `b90b3a51a68`; the only nearby continuous-assignment
change (`236a0197f7d`) handles unrealized conversion-cast cycles and does not
address UVM compilation. A fresh browser-worker run on port 43176:

```text
REPRO_PORT=43176 timeout 240 node scripts/repro-uvm-browser-worker-assert.mjs --expect-fail --no-simulate
```

again emitted only startup lines and then ended with the script's bounded
diagnostic:

```text
Error: compile timed out after 180000ms
```

No completion payload or simulation command was produced.

The second audit of this reopened cycle repeated the minimal check on port
43177:

```text
REPRO_PORT=43177 timeout 240 node scripts/repro-uvm-browser-worker-assert.mjs --expect-fail --no-simulate
```

It again emitted no completion payload or simulation command and ended with
the script's bounded `Error: compile timed out after 180000ms` diagnostic. The
Mox ref, generated artifacts, and source tree remained unchanged.

The third audit of this reopened cycle used port 43178:

```text
REPRO_PORT=43178 timeout 240 node scripts/repro-uvm-browser-worker-assert.mjs --expect-fail --no-simulate
```

The worker again produced no completion payload or simulation command. The
outer watchdog ended the run with `page.evaluate: Target page, context or
browser has been closed`. This is the third consecutive reproduction in this
cycle with no Mox or artifact movement, so the UVM browser requirement remains
blocked on an upstream compiler fix.

After the goal was reopened again, the coordinator's exact UVM demo packet
`/scratch/thomas-ahle/tmp/uvmb/uvm-demo-20261029T1238Z/` was still live, with
`CONFIGURE_RC=0`, no `terminal.json`, and no files newer than its initial
configure/build records. Its wrapper and build processes remained live while
waiting for the shared build dispatcher. Since this is the permitted external
UVM campaign, the lane did not duplicate it; no new compiler artifact or
browser result was available in this audit.

On the second poll after reopening, the same packet still had no
`terminal.json` and no files newer than its initial configure/build records.
The wrapper and `slot-run.sh` build PIDs remained live, and neither
`build.log` nor `unit.log` had advanced. The permitted campaign therefore
remains an in-progress wait; it has not supplied a Mox artifact or browser
result that could change this blocker.

The third poll after reopening again found the exact packet live with
`CONFIGURE_RC=0`, no `terminal.json`, no new packet files, and the same
wrapper/build processes still active. The permitted UVM campaign has therefore
made no artifact or runtime progress across three verified waits; the lane
remains blocked until it completes or an upstream Mox fix is supplied.

After the goal was reopened once more, the same permitted packet was polled
again. It still had no `terminal.json` or files newer than the initial
configure/build records, while its wrapper and `slot-run.sh` build processes
remained live after roughly 1 hour 47 minutes. The coordinator's dispatcher
diagnosis remains external to this lane; no duplicate browser/compiler run was
started and no new Mox artifact was available.

After the goal was reopened again, the permitted UVM packet remained live for
more than two hours. It still had no `terminal.json` or files newer than the
initial configure/build records; its wrapper and `slot-run.sh` build process
were alive. The tutorial Mox ref and generated WASM artifacts remained at
`b90b3a51a68`. This audit therefore records a verified wait and does not
duplicate the coordinator's campaign.

The third poll of this reopened cycle again found the packet live with no
`terminal.json` or files newer than its initial records. The wrapper and
`slot-run.sh` build processes remained live at nearly 1 hour 50 minutes, and
the locked Mox ref plus generated WASM artifacts were unchanged. Three
verified waits have now completed without an artifact or runtime result.

On the second poll of this reopened cycle, the packet still had no
`terminal.json` or files newer than the initial records. Its wrapper and
`slot-run.sh` build processes remained live after more than 1 hour 48 minutes,
and the tutorial's locked Mox/WASM state was unchanged. This remains a
verified wait on the permitted external campaign, not a new browser result.

On the second poll of this reopened cycle, the exact packet still had no
`terminal.json` or files newer than its initial records. Its wrapper and
`slot-run.sh` build process remained live beyond two hours, while the packet
logs and tutorial Mox/WASM state were unchanged. This is another verified wait
on the permitted external campaign; no duplicate run was started.

The third poll of this reopened cycle again found the packet live after more
than two hours, with no `terminal.json`, no new packet files, unchanged build
records, and the same wrapper/build processes active. Mox `b90b3a51a68` and the
generated WASM artifacts were unchanged. Three verified waits in this cycle
have now completed without a compiler artifact or runtime result.

After the goal was reopened again, the permitted packet remained live after
more than 2 hours 17 minutes. It still had no `terminal.json` or files newer
than the initial configure/build records; its wrapper and `slot-run.sh` build
processes remained active, and the tutorial Mox/WASM state was unchanged at
`b90b3a51a68`. This audit records a verified wait and does not duplicate the
coordinator's campaign.
