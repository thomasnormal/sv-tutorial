# Browser QA receipt

Command:

```text
npx playwright test e2e/qa-all-lessons.spec.js --grep 'Protected Envelope Boundary'
```

Result: expected failure under the pinned WASM; Playwright exits 0 with `1
passed` because the lesson is registered in the known-failure ledger. The
runtime reports that the pinned `mox-verilog.wasm` rejects the comment-form
protected envelope, while native Mox passes the solution. The complete output
is retained in `browser-qa.log`.
