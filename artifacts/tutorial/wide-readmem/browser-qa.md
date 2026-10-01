# Browser QA receipt

Command:

```text
npx playwright test e2e/qa-all-lessons.spec.js --grep 'Wide Four-State Memory Loading' --reporter=line
```

Result: `1 passed` (`e2e/qa-all-lessons.spec.js:66:5`, lesson `[31]`,
`run`), wall time `48.1s`.

The web server logged a 404 for `/mox/mox-run.js`; this is the expected
toolchain fallback. The route completed through the pinned `mox-verilog` plus
`mox-sim` interpreter path, so this receipt does not qualify browser native
AOT.
