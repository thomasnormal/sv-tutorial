# Browser QA receipt

Command:

```text
npx playwright test e2e/qa-all-lessons.spec.js --grep 'Clocking Sampler Retention'
```

Result: `1 passed` in 45.0s. The browser run uses the pinned WASM runtime and
is interpreter-backed; it does not qualify native AOT. The complete Playwright
output is retained in `browser-qa.log`.
