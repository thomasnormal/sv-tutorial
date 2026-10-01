# Browser QA receipt

Command:

```text
npx playwright test e2e/qa-all-lessons.spec.js --grep 'Virtual Method Provider Closure'
```

Result: `1 passed` (`e2e/qa-all-lessons.spec.js:65:5`, lesson `[28]`,
`run`), wall time `52.7s`.

The test observed the expected pinned-WASM behavior: `/mox/mox-run.js` was
absent, so the runtime used its `mox-verilog` + `mox-sim` fallback. This is
interpreter-backed browser qualification, not native AOT qualification.
