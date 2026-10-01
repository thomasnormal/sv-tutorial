# pc-runner d2: main `a0c4488a587` (2026-10-01)

This is the latest durable five-row receipt available for the published Mox
tip. The end-to-end `daily.sh` run completed on 2026-10-01 09:15–09:30 UTC,
with all four tools reporting `a0c4488a587` and CPUs selected from `0-79`.

**Compile PASS: 0/5 rows.** Interpreter mode passes all five rows. The
positive and negative counter controls pass, and counter replay agrees on
5/5 rows.

| row | row_id | compile status | compile stage | classification |
|---|---|---|---|---|
| 0 | `0001:35objections-01timeout` | fail | `apply-demotions` | `HELD` |
| 1 | `0876:60inventory-55object_macro-281field_queue_int_set_contract` | fail | `apply-demotions` | `NEW-REFUSAL` |
| 2 | `1713:60inventory-100mem-95backdoor_read_missing_path_status` | fail | `apply-demotions` | `HELD` |
| 3 | `2535:60inventory-8_2-08abstract_component_default_tname` | fail | `apply-demotions` | `NEW-REFUSAL` |
| 4 | `3346:60inventory-110common_phases-03bottomup_dispatches` | fail | `apply-demotions` | `NEW-REFUSAL` |

All five rows refuse before simulation on the mandatory-retain promise for
`uvm_pkg::uvm_mem_single_access_seq::body` (`runtime:caller_retry_required`
and `runtime:delay`). The `NEW-REFUSAL` labels for rows 1, 3, and 4 mean the
stage moved relative to the frozen `d0` ledger; they are not semantic
simulation failures. The prior `d0` receipt remains at
`artifacts/tutorial/compile-mode-status/s4-d0-report.md` for comparison.

Source receipt: `/var/tmp/thomas-ahle/fleet/artifacts/perf/pc-runner/d2/RECEIPT.md`.
