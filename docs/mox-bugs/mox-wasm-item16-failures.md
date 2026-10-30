# Item 16 browser failure census

The item-15 published-site matrix recorded 49 passing and 60 failing run/verify
cases. This table is the single Mox-refusal handoff for every refusal observed
in that matrix. `PASS*` means the row's expected-failure-aware harness status was
PASS even though the browser log still contained the refusal; it remains here so
that the coordinator has the complete refusal set. The diagnostic text is the
first Mox diagnostic retained by the QA run.

| Lesson | Mode | Construct | Exact diagnostic | IEEE 1800-2023 clause |
|---|---|---|---|---|
| `sv/events` | run | named event trigger and wait | `__moore_event_trigger` unresolved | §15.5 (named events) |
| `sv/interfaces` | run | interface signal connection | `__mox_sim_notify_native_memory_write` unlinked | §25.3 (interface declarations) |
| `sv/modports` | run | modport direction view | `__mox_sim_notify_native_memory_write` unlinked | §25.5 (modports) |
| `sv/tasks-functions` | run | timing-aware task over interface | `continuous-evaluator-effect-ownership-not-admitted` | §10.3 (continuous assignment evaluator) |
| `sv/covergroup-basics` | run | covergroup allocation and sampling | `__mox_sim_register_host_allocation` unlinked | §19.2 (covergroup declarations) |
| `sv/coverpoint-bins` | run | coverpoint bins and ignore bins | `__mox_sim_register_host_allocation` unlinked | §19.4 and §19.6 (coverpoints and bins) |
| `sv/cross-coverage` | run | cross, binsof, and intersect | `assertMooreCrossBinsofFilterStructABI` | §19.5 (cross coverage) |
| `sv/queues-arrays` | run | dynamic array and queue values | `__mox_sv_open_array_copy_or_register_bounds` unlinked | §§7.5 and 7.10 (arrays and queues) |
| `sva/concurrent-sim` | run | concurrent `assert property` | `temporal-property-evaluator-not-admitted` | §16.2 (concurrent assertions) |
| `sva/vacuous-pass` | run | implication vacuity | `temporal-property-evaluator-not-admitted` | §16.14.8 (vacuous success) |
| `sva/isunknown` | run | sampled `$isunknown` assertion | `temporal-property-evaluator-not-admitted` | §20.9 (bit system functions) |
| `sva/immediate-assert` | run, verify (`PASS*`) | immediate assertion action | `temporal-property-evaluator-not-admitted` | §16.3 (immediate assertions) |
| `sva/sequence-basics` | run, verify | named sequence and property | `temporal-property-evaluator-not-admitted` | §§16.3 and 16.4 (sequence/property declarations) |
| `sva/implication` | run, verify | overlapped and non-overlapped implication | `temporal-property-evaluator-not-admitted` | §16.10 (implication operators) |
| `sva/formal-intro` | run, verify | assertion used for bounded proof | `temporal-property-evaluator-not-admitted` | §16.14 (assertion statements) |
| `sva/clock-delay` | run, verify | `##m` and `##[m:n]` delays | `temporal-property-evaluator-not-admitted` | §16.10.1 (cycle delay) |
| `sva/rose-fell` | run, verify | `$rose` and `$fell` | `temporal-property-evaluator-not-admitted` | §16.9.3 (sampled-value functions) |
| `sva/req-ack` | run, verify | request/acknowledge implication | `temporal-property-evaluator-not-admitted` | §§16.9 and 16.10 (sequence and implication) |
| `sva/consecutive-rep` | run, verify | consecutive repetition `[*]` | `temporal-property-evaluator-not-admitted` | §16.10.4 (repetition) |
| `sva/nonconsec-rep` | run, verify | goto repetition `[->]` | `unbounded goto repetition has an unbounded sampled gap` | §16.10.6 (goto repetition) |
| `sva/nonconsec-eq` | run, verify | non-consecutive repetition `[=]` | `sequence-zero-delay-endpoint-overlap-not-representable` | §16.10.7 (non-consecutive repetition) |
| `sva/throughout` | run, verify | `throughout` sequence constraint | `temporal-property-evaluator-not-admitted` | §16.10.5 (throughout) |
| `sva/sequence-ops` | run, verify | `intersect`, `within`, `and`, `or` | `temporal-property-evaluator-not-admitted` | §16.9 (sequence operators) |
| `sva/seq-args` | run, verify | typed sequence formal arguments | `temporal-property-evaluator-not-admitted` | §16.8 (sequence declarations) |
| `sva/stable-past` | run, verify | `$stable` and `$past` | `temporal-property-evaluator-not-admitted` | §16.9.3 (sampled-value functions) |
| `sva/changed` | run, verify | `$changed` and `$sampled` | `temporal-property-evaluator-not-admitted` | §16.9.3 (sampled-value functions) |
| `sva/disable-iff` | run, verify | `disable iff` property abort | `temporal-property-evaluator-not-admitted` | §16.12.1 (`disable iff`) |
| `sva/abort` | run, verify | `reject_on` and `accept_on` | `temporal-property-evaluator-not-admitted` | §16.12.2 (abort operators) |
| `sva/cover-property` | run, verify | `cover property` | `temporal-property-evaluator-not-admitted` | §16.14.3 (property coverage) |
| `sva/local-vars` | run, verify | local variables in sequences | `temporal-property-evaluator-not-admitted` | §16.8.2 (sequence local variables) |
| `sva/onehot` | run, verify | `$onehot`, `$onehot0`, `$countones` | `temporal-property-evaluator-not-admitted` | §20.9 (bit system functions) |
| `sva/triggered` | run, verify | sequence `.triggered` method | `temporal-property-evaluator-not-admitted` | §16.9.11 (sequence methods) |
| `sva/checker` | run, verify | `checker` declaration | `temporal-property-evaluator-not-admitted` | §17.2 (checker declarations) |
| `sva/recursive` | run, verify | recursive property | `temporal-property-evaluator-not-admitted` | §16.8 (property/sequence declarations) |
| `sva/bind` | run | `bind` checker attachment | `temporal-property-evaluator-not-admitted` | §23.11 (`bind`) |
| `sva/let` | run | `let` sequence expression | `temporal-property-evaluator-not-admitted` | §16.8.4 (`let` declarations) |
| `sva/formal-assume` | run, verify | `assume property` | `temporal-property-evaluator-not-admitted` | §16.14.2 (assumption statements) |
| `sva/always-eventually` | run, verify | `always` and `s_eventually` | `temporal-property-evaluator-not-admitted` | §16.13 (liveness operators) |
| `sva/until` | run, verify | `until` and `s_until` | `temporal-property-evaluator-not-admitted` | §16.10.3 (until operators) |
| `sva/lec` | verify (`PASS*`) | property miter for LEC | `temporal-property-evaluator-not-admitted` | §16.14 (assertion statements) |
| `sva/followed-by` | verify | `#-#` and `#=#` followed-by | `temporal-property-evaluator-not-admitted` | §16.10.8 (followed-by operators) |

The tutorial does not change source examples to hide these refusals: each is a
Mox runtime/compiler capability gap, and the source remains a useful language
reference while the upstream implementation is completed.
