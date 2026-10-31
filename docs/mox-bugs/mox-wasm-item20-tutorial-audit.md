# Item 20 tutorial-failure audit

Item 20 asked for the tutorial-side failures from the item-19 matrix to be
fixed first. The authoritative census at
[`mox-wasm-item16-failures.md`](mox-wasm-item16-failures.md) contains 57 rows:

| Disposition | Rows | Meaning |
|---|---:|---|
| Mox refusal | 41 | The browser reached a documented Mox language or runtime refusal. |
| Environment | 16 | The UVM or VPI browser worker did not reach a lesson simulation. |
| Tutorial | 0 | No wrong expected output, non-IEEE construct, stale API, or missing include was observed. |

The first failed lessons in README order are `sv/events`, `sv/interfaces`,
`sv/modports`, `sv/tasks-functions`, and `sv/covergroup-basics`. Their exact
diagnostics are, respectively, `__moore_event_trigger` unresolved,
`__mox_sim_notify_native_memory_write` unlinked (for both interface lessons),
`continuous-evaluator-effect-ownership-not-admitted`, and
`__mox_sim_register_host_allocation` unlinked. Each is already recorded as a
Mox refusal with its IEEE clause in the census. The remaining 36 Mox rows and
all 16 environment rows are classified the same way there.

Because no row has tutorial disposition, there is no lesson text or source fix
to make and no tutorial row that can legitimately flip on a rerun. The newest
available WASM artifact remains the item-18 static build; item 19 recorded that
the current-main rebuild stopped at the wasm32 `EX_IOERR`/`::write` portability
errors. The five lessons above therefore remain unchanged pending a Mox build
that removes their refusals.
