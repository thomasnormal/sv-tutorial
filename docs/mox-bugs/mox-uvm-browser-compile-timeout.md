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
