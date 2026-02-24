# Bug Report: `circt-verilog.wasm` aborts on full UVM in browser-like runtime

## Title
`circt-verilog.wasm` aborts compiling full `uvm_pkg` with:
`Malformed attribute storage object` (MLIR `AttributeSupport.h:177`)

## Date
February 24, 2026

## Revisions
- CIRCT fork: `thomasnormal/circt`
- CIRCT commit: `20fa81a69add402715db28203335596192ce7c39`
- LLVM submodule: `972cd847efb20661ea7ee8982dd19730aa040c75`

## Why this report
This is a clean CIRCT-only repro (no `sv-tutorial` runtime dependency). It reproduces using only CIRCT wasm artifacts + UVM sources from the CIRCT tree.

## Repro (standalone, browser-like wasm path)

### Preconditions
From CIRCT repo root:
- `build-wasm/bin/circt-verilog.js`
- `build-wasm/bin/circt-verilog.wasm`
- `lib/Runtime/uvm-core/src/uvm_pkg.sv`

If needed for the browser harness:
```bash
npm i -D @playwright/test
```

### Script
Use attached script file:
- `utils/repro_wasm_uvm_browser_assert.mjs`

### Run
```bash
node utils/repro_wasm_uvm_browser_assert.mjs
```

## Expected
`circt-verilog.wasm` lowers minimal UVM test to MLIR (or emits a normal diagnostic), without aborting.

## Actual
The run aborts before output MLIR is produced.

Failure signature from script summary:
- `exitCode=0`
- `callMainErrorPresent=true`
- `outMlirBytes=0`
- `hasMalformed=true`
- `hasAbort=true`
- `reachedSim=false`
- final marker: `REPRODUCED: malformed attribute storage abort in browser-like wasm execution`

Representative log excerpt:
```text
RuntimeError: Aborted(Assertion failed: abstractAttribute && "Malformed attribute storage object.", at: .../mlir/include/mlir/IR/AttributeSupport.h,177,getAbstractAttribute)

../circt/uvm-core/src/base/uvm_config_db_implementation.svh:375:26: warning: unknown character escape sequence '\.' [-Wunknown-escape-code]
../circt/uvm-core/src/uvm_pkg.sv:57:2: note: included from here
../circt/uvm-core/src/base/uvm_base.svh:77:3: note: included from here

Aborted(Assertion failed: abstractAttribute && "Malformed attribute storage object.", ...)
```

## Minimal SV payload used in repro
```systemverilog
// my_test.sv
import uvm_pkg::*;
`include "uvm_macros.svh"

class my_test extends uvm_test;
  `uvm_component_utils(my_test)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("TEST", "Hello from UVM!", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass
```

```systemverilog
// tb_top.sv
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "my_test.sv"

module tb_top;
  initial run_test("my_test");
endmodule
```

## Notes
- This repro intentionally emulates browser-like wasm execution (no Node native FS).
- A separate Node MEMFS helper that compiles a simpler UVM sample may pass; this payload still reproduces the abort.
