# Browser QA receipt

Command:

```text
npx playwright test e2e/qa-all-lessons.spec.js --grep 'Coverage Option Text' --reporter=line
```

Result: `1 passed` as an expected failure (`e2e/qa-all-lessons.spec.js:67:5`,
lesson `[32]`, `run`), wall time `33.6s`.

The pinned browser WASM route fails with the known unlinked coverage runtime
host-allocation call (`__mox_sim_register_host_allocation`); native Mox passes.
The entry is an explicit `test.fail` for a WASM rebuild, not a tutorial-source
failure and not native AOT qualification.
