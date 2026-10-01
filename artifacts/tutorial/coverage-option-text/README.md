# Coverage option text receipt

This receipt supports `sv/coverage-option-text`. The lesson teaches the
instance-specific `option.comment` default and a procedural assignment on a
covergroup instance. The starter deliberately rejects the standard empty
default; the solution accepts it, assigns the runtime comment, samples one
value, and prints `PASS`.

## Standard and landing basis

IEEE 1800-2023 §19.7 and Table 19-1 define instance-specific coverage
options. The `comment` option defaults to `""`, is associated with the
covergroup instance, and may be assigned procedurally after instantiation.
The lesson does not claim that a simulator's coverage-report formatting is
portable.

The native capability landed in Mox commit `b481355f9fe`
(`b481355f9fe63237a9a5f6307accb8a0133e1e77`), recorded by
`/var/tmp/thomas-ahle/fleet/artifacts/landing/push-b481355f9fe.md`. The exact-
tip qualification established the nine named Chapter-19 controls at 9/9.
The native receipt uses `/var/tmp/thomas-ahle/wt/landing/build-dev-fast` at
`35ec19ea7f9398d76cf704252703ae731dad04d5`, which contains b481 as an
ancestor. No Mox worktree was modified.

## Native runs

The native runs use CPUs `0-79` and a 30-second wall guard. The logs use
`mox-verilog` plus `mox-sim`; the build also has no `mox-run` binary.

| variant | mode | exit | first result line |
|---|---:|---:|---|
| starter | interpret | 0 | `FAIL: starter rejected the empty default comment` |
| starter | compile | 0 | `FAIL: starter rejected the empty default comment` |
| solution | interpret | 0 | `PASS` |
| solution | compile | 0 | `PASS` |

Both compile logs report `AOT interpreter invocations total: 0`. The committed
logs are the six `*-{import,interpret,compile}.log` files in this directory.

## Differential runs

`refdiff` was run on each committed fixture against the same native build:

```text
/var/tmp/thomas-ahle/fleet/bin/refdiff src/lessons/sv/coverage-option-text/coverage_option_text.sv --build-dir /var/tmp/thomas-ahle/wt/landing/build-dev-fast
/var/tmp/thomas-ahle/fleet/bin/refdiff src/lessons/sv/coverage-option-text/coverage_option_text.sol.sv --build-dir /var/tmp/thomas-ahle/wt/landing/build-dev-fast
```

- `starter-refdiff.json`: `both_fail`; both engines reject the deliberate
  wrong expectation of a nonempty default.
- `solution-refdiff.json`: `both_pass`; normalized outputs are equivalent.
- The committed refdiff JSON `sha256` field is the exact committed source
  hash; `refdiff_cache_key` is the separate 64-hex receipt cache identity.
  The receipts were regenerated from the committed fixtures with the commands
  above. `starter-source.sha256` and `solution-source.sha256` independently
  repeat the source binding. Standing ruling — `general: refdiff cache identity
  is receipt provenance, not a runtime performance cache`.

## Browser qualification

The browser result is recorded in `browser-qa.md`. It is an expected pinned-WASM
failure caused by the unlinked coverage runtime host-allocation call
`__mox_sim_register_host_allocation`; the explicit `test.fail` remains until a
WASM rebuild. Native Mox passes, and the browser run does not qualify native
AOT. Standing ruling — `general: pinned interpreter fallback is an explicitly
scoped browser compatibility path`.
