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
