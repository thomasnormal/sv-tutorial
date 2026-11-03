# UVM package precompile timing receipt

This receipt compares the pinned native frontend compiling each UVM lesson
with source-backed UVM against the same frontend importing the precompiled
package artifact. It is a timing receipt, not browser qualification: the
browser still uses the mapped artifact path until the shared lowered-library
consumer lands in `mox-verilog`.

- Mox frontend SHA: `b90b3a51a68b772a1510c837166afd6d429d8f20`
- Source-backed invocation: `mox-verilog --resource-guard=false --ir-llhd --timescale 1ns/1ns --single-unit --uvm-path <uvm-root> -I <uvm-root>/src --top tb_top -o <out> <lesson>/tb_top.sv`
- Mapped-artifact invocation: the source invocation plus `--read-vlib <artifact> --read-vlib-mapped-moore-ir`, with package source replay disabled
- Artifact: `static/mox/packages/uvm_pkg-b90b3a5.vlib`
- Artifact bytes: `58,912,612`
- Artifact SHA-256: `058e528f971d915e06fe87499a3c895bd927d4dcb9f6f86bc5680c2dfe1ead11`
- Per-invocation timeout: `120,000 ms`

| lesson | source ms | mapped artifact ms | source result | mapped artifact result | source MLIR bytes | mapped MLIR bytes |
| --- | ---: | ---: | --- | --- | ---: | ---: |
| reporting | 42,271 | 79,759 | PASS | PASS | 53,441,834 | 89,637,083 |
| seq-item | 40,150 | 79,539 | PASS | PASS | 54,419,469 | 90,629,798 |
| sequence | 46,619 | 112,954 | PASS | PASS | 56,688,538 | 96,524,340 |
| driver | 45,772 | 120,129 | PASS | TIMEOUT | 57,846,639 | — |
| constrained-random | 40,303 | 82,595 | PASS | PASS | 54,397,031 | 90,620,158 |
| monitor | 47,527 | 120,105 | PASS | TIMEOUT | 58,461,049 | — |
| env | 53,534 | 120,108 | PASS | TIMEOUT | 58,691,392 | — |
| covergroup | 1,230 | 5,275 | FAIL(1) | FAIL(1) | — | — |
| cross-coverage | 684 | 3,422 | FAIL(1) | FAIL(1) | — | — |
| coverage-driven | 703 | 3,383 | FAIL(1) | FAIL(1) | — | — |
| factory-override | 39,237 | 77,808 | PASS | PASS | 54,549,108 | 90,768,531 |
| ral | 39,510 | 85,340 | PASS | PASS | 55,027,785 | 90,579,106 |

The mapped artifact is valid, but this pinned native receipt is slower than
source compilation and times out on `driver`, `monitor`, and `env`. The
browser `uvm/reporting` probe likewise did not return within 900 seconds. The
follow-up lowered-library receipt will replace this table only after the
shared `mox-verilog` consumer is landed and browser rows are rerun.
