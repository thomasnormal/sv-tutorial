# Item 21 environment rerun

Item 21 reran the four cocotb rows against the current checked-in WASM Mox
artifact (`540e3f0`) after fixing the browser worker startup path and keeping
each DUT alive for the VPI startup callback.

| Lesson | Before | After | Evidence |
|---|---|---|---|
| `cocotb/first-test` | VPI worker ended at 0 fs without a result | PASS | `scripts/run-matrix.mjs`: PASS |
| `cocotb/clock-and-timing` | VPI worker ended at 0 fs without a result | PASS | `scripts/run-matrix.mjs`: PASS |
| `cocotb/edge-triggers` | VPI worker ended at 0 fs without a result | Mox refusal | pinned VPI `cbValueChange` callback did not fire after a cocotb clock write |
| `cocotb/clockcycles-patterns` | VPI worker ended at 0 fs without a result | Mox refusal | pinned VPI `cbValueChange` callback did not fire after a cocotb clock write |

The twelve UVM rows remain environment rows. Full-UVM compilation emitted the
`uvm_config_db_implementation.svh` escape warning and was still compiling after
240 seconds in a direct browser run, so increasing the matrix polling timeout
would not turn those rows into a green lesson run.
