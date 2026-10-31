# Item 20 tutorial-failure audit

Item 20 asked for the tutorial-side failures from the item-19 matrix to be
fixed first. The authoritative census at
[`mox-wasm-item16-failures.md`](mox-wasm-item16-failures.md) started with 57 rows before item 21; the current census has 55 disposition rows:

| Disposition | Rows | Meaning |
|---|---:|---|
| Mox refusal | 43 | The browser reached a documented Mox language or runtime refusal. |
| Environment | 12 | The UVM browser worker did not reach a lesson simulation. |
| Tutorial | 0 | No wrong expected output, non-IEEE construct, stale API, or missing include was observed. |

The first failed lessons in README order are `sv/events`, `sv/interfaces`,
`sv/modports`, `sv/tasks-functions`, and `sv/covergroup-basics`. Their exact
diagnostics are, respectively, `__moore_event_trigger` unresolved,
`__mox_sim_notify_native_memory_write` unlinked (for both interface lessons),
`continuous-evaluator-effect-ownership-not-admitted`, and
`__mox_sim_register_host_allocation` unlinked. Each is already recorded as a
Mox refusal with its IEEE clause in the census. Item 21 reran the four cocotb rows:
two now pass, and the two edge-trigger rows are documented as Mox VPI callback
refusals. The remaining 12 environment rows are the full-UVM compile timeouts.

Because no row has tutorial disposition, there is no lesson text or source fix
to make and no tutorial row that can legitimately flip on a rerun. The newest
available WASM artifact remains the item-18 static build; item 19 recorded that
the current-main rebuild stopped at the wasm32 `EX_IOERR`/`::write` portability
errors. The five lessons above therefore remain unchanged pending a Mox build
that removes their refusals.
