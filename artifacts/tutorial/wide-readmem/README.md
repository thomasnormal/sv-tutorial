# Wide four-state memory-loading receipt

This receipt supports `sv/wide-readmem`. The lesson teaches that
`$readmemh` loads packed words into an unpacked memory, including explicit
start and finish addresses and four-state hexadecimal data. The starter uses a
64-bit word for 65-bit file values; the solution uses a 65-bit word.

## Standard and landing basis

IEEE 1800-2023 §21.4 defines `$readmemb` and `$readmemh`, including the
optional `start_addr` and `finish_addr` arguments. Section §21.4.1 says these
system tasks support unpacked arrays of packed data and treat each packed
element as the vector equivalent. Section §21.4 also permits `x`, `z`, and
underscores in the hexadecimal numbers. The lesson uses those rules directly;
it does not claim behavior for dynamic or associative arrays.

The native capability landed in Mox commit `e7da9630dcd`
(`9cd0fcd389e505f9b031a8b99a347888181e9451`), recorded by
`/var/tmp/thomas-ahle/fleet/artifacts/landing/push-e7da9630dcd.md`. Its exact-
tip focused controls passed 3/3 in each of three trials. The native receipt
uses `/var/tmp/thomas-ahle/wt/landing/build-dev-fast` at
`35ec19ea7f9398d76cf704252703ae731dad04d5`, whose parent contains the landed
readmem change. No Mox worktree was modified.

## Native runs

The native runs use CPUs `0-79` and a 30-second wall guard. This build has no
`mox-run`, so the runtime uses the `mox-verilog` plus `mox-sim` path. The
committed logs are `starter-import.log`, `starter-interpret.log`,
`starter-compile.log`, `solution-import.log`, `solution-interpret.log`, and
`solution-compile.log`.

| variant | mode | exit | first result line |
|---|---:|---:|---|
| starter | interpret | 0 | `FAIL: 0123456789abcdef fedcba9876543210 0000000000000000` |
| starter | compile | 0 | `FAIL: 0123456789abcdef fedcba9876543210 0000000000000000` |
| solution | interpret | 0 | `PASS` |
| solution | compile | 0 | `PASS` |

The solution compile receipt reports `AOT interpreter invocations total: 0`.
The browser asset is older than this landing and therefore the browser result
does not qualify native AOT.

## Differential runs

`refdiff` was run on each committed fixture against the same native build:

```text
/var/tmp/thomas-ahle/fleet/bin/refdiff src/lessons/sv/wide-readmem/wide_readmem.sv --build-dir /var/tmp/thomas-ahle/wt/landing/build-dev-fast
/var/tmp/thomas-ahle/fleet/bin/refdiff src/lessons/sv/wide-readmem/wide_readmem.sol.sv --build-dir /var/tmp/thomas-ahle/wt/landing/build-dev-fast
```

- `starter-refdiff.json`: `both_fail`; Xcelium and Mox reject the too-narrow
  memory through the test's value check.
- `solution-refdiff.json`: `both_pass`; outputs are equivalent.
- Both JSON receipts bind their `sha256` values to the committed source and
  retain their `refdiff_cache_key` values. Standing ruling — `general:
  refdiff_cache_key is receipt provenance, not a runtime performance cache`.

## Browser qualification

The focused Playwright run passed 1/1:

```text
npx playwright test e2e/qa-all-lessons.spec.js --grep 'Wide Four-State Memory Loading' --reporter=line
```

The route used the pinned interpreter-backed WASM fallback because
`/mox/mox-run.js` is absent. This is browser interpreter qualification only,
not native AOT qualification. Standing ruling — `general: pinned interpreter
fallback is an explicitly scoped browser compatibility path`.

The lesson writes its input file under `/tmp`; the run environment must provide
a writable temporary directory, as stated in the lesson itself.
