# circt-verilog.wasm aborts compiling full UVM (`uvm_pkg`)

## Title
`circt-verilog.wasm` aborts compiling full UVM (`uvm_pkg`) with MLIR assert (`Malformed attribute storage object`)

## CIRCT Revision
- Fork: `thomasnormal/circt`
- CIRCT commit tested: `0246e937a9e11f602c85a80dc2fcb2c69c5e5a84`
- LLVM submodule: `972cd847efb20661ea7ee8982dd19730aa040c75`
- Date observed: `2026-02-24`

## Environment
- wasm build artifacts: `circt-verilog.js` + `circt-verilog.wasm`
- Browser worker execution (NODERAWFS-style, in-memory FS)
- UVM sources loaded from `uvm-core/src` via manifest

## Repro

Command run in app logs:

```sh
circt-verilog --resource-guard=false --ir-llhd --timescale 1ns/1ns \
  --uvm-path /circt/uvm-core -I /circt/uvm-core/src \
  --top tb_top -o /workspace/out/design.llhd.mlir /workspace/src/tb_top.sv
```

Standalone browser-worker repro in this repo:

```sh
node scripts/repro-uvm-browser-worker-assert.mjs
```

This launches a headless Chromium page, imports `createCirctWasmAdapter` from
`/src/runtime/circt-adapter.js`, runs compile-only (`simulate: false`) on a
minimal `tb_top + my_test` UVM input, and reproduces the same assert.

`tb_top.sv`:

```systemverilog
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "my_test.sv"

module tb_top;
  initial run_test("my_test");
endmodule
```

`my_test.sv`:

```systemverilog
import uvm_pkg::*;
`include "uvm_macros.svh"

class my_test extends uvm_test;
  `uvm_component_utils(my_test)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  task run_phase(uvm_phase phase);
  endtask
endclass
```

## Actual Result
- `circt-verilog` aborts before producing MLIR.
- Warning emitted first:
  - `uvm_config_db_implementation.svh:375:26: warning: unknown character escape sequence '\.'`
- Then hard abort:
  - `Aborted(Assertion failed: abstractAttribute && "Malformed attribute storage object.", ... mlir/IR/AttributeSupport.h:177, getAbstractAttribute)`
- Stack includes wasm frames inside `circt-verilog.wasm`.

## Expected Result
- Successful lowering to LLHD MLIR for UVM input, or at minimum a graceful user-facing diagnostic (not assert/abort).

## Notes
- UVM file discovery/loading is working (no `unknown package 'uvm_pkg'` at this point).
- Non-UVM lessons compile and simulate successfully in the same environment.
- This still reproduces after the wasm stack-size increase in `0246e937a`.
