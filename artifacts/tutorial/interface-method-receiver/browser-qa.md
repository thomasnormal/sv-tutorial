# Browser QA receipt

The focused browser check is expected to fail against the checked-in WASM:
the interface-method receiver lowering landed in Mox `ed441eb5b58` after the
pinned browser artifact. Native Mox interpreter and compile receipts pass the
solution, but this chapter does not claim that the old WASM implements it.

Expected focused command:

```text
npx playwright test e2e/qa-all-lessons.spec.js --grep 'Interface Method Receivers' --reporter=line
```

The route remains registered and the failure is quarantined with a reason in
`e2e/qa-all-lessons.spec.js`. Remove that expectation only after a qualified
WASM rebuild and rerun of the focused browser check.

Receipt: October 1, 2026, `1 passed` in 31.3 seconds. The pass is the
expected-failure disposition, not evidence that the pinned WASM supports the
new receiver behavior.
