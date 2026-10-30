# Item 16 browser failure census

The item-15 published-site matrix recorded 49 passing and 60 failing run/verify
cases. This table is the single reader-facing handoff for every non-PASS result
observed in that matrix. `PASS*` means the row's expected-failure-aware harness status was
PASS even though the browser log still contained the refusal; it remains here so
that the coordinator has the complete refusal set. The diagnostic text is the
first diagnostic retained by the QA run. The status column is the reader-facing
bucket consumed by the generated status page.

| Lesson | Mode | Construct | Exact diagnostic | IEEE 1800-2023 clause | Current status |
|---|---|---|---|---|---|
| `sv/events` | run | named event trigger and wait | `__moore_event_trigger` unresolved | §15.5 (named events) | Mox refusal |
| `sv/interfaces` | run | interface signal connection | `__mox_sim_notify_native_memory_write` unlinked | §25.3 (interface declarations) | Mox refusal |
| `sv/modports` | run | modport direction view | `__mox_sim_notify_native_memory_write` unlinked | §25.5 (modports) | Mox refusal |
| `sv/tasks-functions` | run | timing-aware task over interface | `continuous-evaluator-effect-ownership-not-admitted` | §10.3 (continuous assignment evaluator) | Mox refusal |
| `sv/covergroup-basics` | run | covergroup allocation and sampling | `__mox_sim_register_host_allocation` unlinked | §19.2 (covergroup declarations) | Mox refusal |
| `sv/coverpoint-bins` | run | coverpoint bins and ignore bins | `__mox_sim_register_host_allocation` unlinked | §19.4 and §19.6 (coverpoints and bins) | Mox refusal |
| `sv/cross-coverage` | run | cross, binsof, and intersect | `assertMooreCrossBinsofFilterStructABI` | §19.5 (cross coverage) | Mox refusal |
| `sv/queues-arrays` | run | dynamic array and queue values | `__mox_sv_open_array_copy_or_register_bounds` unlinked | §§7.5 and 7.10 (arrays and queues) | Mox refusal |
| `sva/concurrent-sim` | run | concurrent `assert property` | `temporal-property-evaluator-not-admitted` | §16.2 (concurrent assertions) | Mox refusal |
| `sva/vacuous-pass` | run | implication vacuity | `temporal-property-evaluator-not-admitted` | §16.14.8 (vacuous success) | Mox refusal |
| `sva/isunknown` | run | sampled `$isunknown` assertion | `temporal-property-evaluator-not-admitted` | §20.9 (bit system functions) | Mox refusal |
| `sva/immediate-assert` | run, verify (`PASS*`) | immediate assertion action | `temporal-property-evaluator-not-admitted` | §16.3 (immediate assertions) | Mox refusal |
| `sva/sequence-basics` | run, verify | named sequence and property | `temporal-property-evaluator-not-admitted` | §§16.3 and 16.4 (sequence/property declarations) | Mox refusal |
| `sva/implication` | run, verify | overlapped and non-overlapped implication | `temporal-property-evaluator-not-admitted` | §16.10 (implication operators) | Mox refusal |
| `sva/formal-intro` | run, verify | assertion used for bounded proof | `temporal-property-evaluator-not-admitted` | §16.14 (assertion statements) | Mox refusal |
| `sva/clock-delay` | run, verify | `##m` and `##[m:n]` delays | `temporal-property-evaluator-not-admitted` | §16.10.1 (cycle delay) | Mox refusal |
| `sva/rose-fell` | run, verify | `$rose` and `$fell` | `temporal-property-evaluator-not-admitted` | §16.9.3 (sampled-value functions) | Mox refusal |
| `sva/req-ack` | run, verify | request/acknowledge implication | `temporal-property-evaluator-not-admitted` | §§16.9 and 16.10 (sequence and implication) | Mox refusal |
| `sva/consecutive-rep` | run, verify | consecutive repetition `[*]` | `temporal-property-evaluator-not-admitted` | §16.10.4 (repetition) | Mox refusal |
| `sva/nonconsec-rep` | run, verify | goto repetition `[->]` | `unbounded goto repetition has an unbounded sampled gap` | §16.10.6 (goto repetition) | Mox refusal |
| `sva/nonconsec-eq` | run, verify | non-consecutive repetition `[=]` | `sequence-zero-delay-endpoint-overlap-not-representable` | §16.10.7 (non-consecutive repetition) | Mox refusal |
| `sva/throughout` | run, verify | `throughout` sequence constraint | `temporal-property-evaluator-not-admitted` | §16.10.5 (throughout) | Mox refusal |
| `sva/sequence-ops` | run, verify | `intersect`, `within`, `and`, `or` | `temporal-property-evaluator-not-admitted` | §16.9 (sequence operators) | Mox refusal |
| `sva/seq-args` | run, verify | typed sequence formal arguments | `temporal-property-evaluator-not-admitted` | §16.8 (sequence declarations) | Mox refusal |
| `sva/stable-past` | run, verify | `$stable` and `$past` | `temporal-property-evaluator-not-admitted` | §16.9.3 (sampled-value functions) | Mox refusal |
| `sva/changed` | run, verify | `$changed` and `$sampled` | `temporal-property-evaluator-not-admitted` | §16.9.3 (sampled-value functions) | Mox refusal |
| `sva/disable-iff` | run, verify | `disable iff` property abort | `temporal-property-evaluator-not-admitted` | §16.12.1 (`disable iff`) | Mox refusal |
| `sva/abort` | run, verify | `reject_on` and `accept_on` | `temporal-property-evaluator-not-admitted` | §16.12.2 (abort operators) | Mox refusal |
| `sva/cover-property` | run, verify | `cover property` | `temporal-property-evaluator-not-admitted` | §16.14.3 (property coverage) | Mox refusal |
| `sva/local-vars` | run, verify | local variables in sequences | `temporal-property-evaluator-not-admitted` | §16.8.2 (sequence local variables) | Mox refusal |
| `sva/onehot` | run, verify | `$onehot`, `$onehot0`, `$countones` | `temporal-property-evaluator-not-admitted` | §20.9 (bit system functions) | Mox refusal |
| `sva/triggered` | run, verify | sequence `.triggered` method | `temporal-property-evaluator-not-admitted` | §16.9.11 (sequence methods) | Mox refusal |
| `sva/checker` | run, verify | `checker` declaration | `temporal-property-evaluator-not-admitted` | §17.2 (checker declarations) | Mox refusal |
| `sva/recursive` | run, verify | recursive property | `temporal-property-evaluator-not-admitted` | §16.8 (property/sequence declarations) | Mox refusal |
| `sva/bind` | run | `bind` checker attachment | `temporal-property-evaluator-not-admitted` | §23.11 (`bind`) | Mox refusal |
| `sva/let` | run | `let` sequence expression | `temporal-property-evaluator-not-admitted` | §16.8.4 (`let` declarations) | Mox refusal |
| `sva/formal-assume` | run, verify | `assume property` | `temporal-property-evaluator-not-admitted` | §16.14.2 (assumption statements) | Mox refusal |
| `sva/always-eventually` | run, verify | `always` and `s_eventually` | `temporal-property-evaluator-not-admitted` | §16.13 (liveness operators) | Mox refusal |
| `sva/until` | run, verify | `until` and `s_until` | `temporal-property-evaluator-not-admitted` | §16.10.3 (until operators) | Mox refusal |
| `sva/lec` | verify (`PASS*`) | property miter for LEC | `temporal-property-evaluator-not-admitted` | §16.14 (assertion statements) | Mox refusal |
| `sva/followed-by` | verify | `#-#` and `#=#` followed-by | `temporal-property-evaluator-not-admitted` | §16.10.8 (followed-by operators) | Mox refusal |

## Environment gaps

These rows are environment limitations rather than Mox language refusals. They
are kept in the same source table so the generated page and lesson badges cannot
drift from the item-16 measurements.

| Lesson | Mode | Construct | Exact diagnostic | IEEE 1800-2023 clause | Current status |
|---|---|---|---|---|---|
| `uvm/reporting` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/seq-item` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/sequence` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/driver` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/constrained-random` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/monitor` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/env` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/covergroup` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/cross-coverage` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/coverage-driven` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/factory-override` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `uvm/ral` | run | full-UVM browser compilation | `compile timed out before simulation` | environment (UVM worker) | environment |
| `cocotb/first-test` | run | VPI worker exits at 0 fs | `mox-sim-vpi completed at 0 fs without a cocotb result` | environment (VPI worker) | environment |
| `cocotb/clock-and-timing` | run | VPI worker exits at 0 fs | `mox-sim-vpi completed at 0 fs without a cocotb result` | environment (VPI worker) | environment |
| `cocotb/edge-triggers` | run | VPI worker exits at 0 fs | `mox-sim-vpi completed at 0 fs without a cocotb result` | environment (VPI worker) | environment |
| `cocotb/clockcycles-patterns` | run | VPI worker exits at 0 fs | `mox-sim-vpi completed at 0 fs without a cocotb result` | environment (VPI worker) | environment |

The tutorial does not change source examples to hide these refusals: each is a
Mox runtime/compiler capability gap, and the source remains a useful language
reference while the upstream implementation is completed. The status column is
consumed by `scripts/generate-lesson-status.mjs`; run `npm run build` to
regenerate the reader-facing status page and lesson badges.
