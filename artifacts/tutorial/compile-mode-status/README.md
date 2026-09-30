# Compile-mode status receipt

This receipt supports the `sv/compile-mode-status` chapter. The lesson source
is intentionally small and self-contained so it can be checked in under 30
seconds on CPUs `0-79`.

## Native example

The solution passes both native modes with Mox build
`/var/tmp/thomas-ahle/wt/landing/build-dev-fast` at Mox tip
`640b4195ed1b1bfbb90520db9064aecd9099290b`:

```text
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=interpret --max-wall-ms=25000 src/lessons/sv/compile-mode-status/compile_mode_status.sol.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=compile --max-wall-ms=25000 src/lessons/sv/compile-mode-status/compile_mode_status.sol.sv
```

Both print `PASS: compile-ready design sum=5` and exit 0. The starter prints
`FAIL: sum=31` in both modes. The starter and solution Xcelium differential
receipts are `starter-refdiff.json` and `solution-refdiff.json`; they report
`both_fail` and `both_pass`, respectively. The committed source hashes are:

```text
compile_mode_status.sv     5305d10dae3dc97215c1dae5dc8cf217f1e443fd33f4cc1984e5db970513469b
compile_mode_status.sol.sv 0cf6f9c5a4934046f1ce9d12b54fcc9f8700e5d8228466b549bf020e1d0a9bd2
```

## S4 status

`s4-d0-report.md` is copied from the prepared `pc-runner` receipt for landing
tip `36b040f6190ce488d406ce49a1c5e0aafb85d6ac`. It reports interpreter 5/5
and compile 0/5. Every compile row is `HELD`; rows 0 and 2 stop at
`apply-demotions` on mandatory-retain obligations, and rows 1, 3, and 4 stop
at `no-reentry-closure-after-process-externalization` on provider-dirty
obligations. The positive and negative counter controls both pass.

The daily check is not a browser lesson action; run it from the perf worktree
with a fresh label:

```text
cd /var/tmp/thomas-ahle/wt/perf
/var/tmp/thomas-ahle/fleet/artifacts/perf/pc-runner/daily.sh d3
```
