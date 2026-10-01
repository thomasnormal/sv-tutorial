# Compile-mode status receipt

This receipt supports the `sv/compile-mode-status` chapter. The lesson source
is intentionally small and self-contained so it can be checked in under 30
seconds on CPUs `0-79`.

## Native example

The solution passes both native modes with Mox build
`/var/tmp/thomas-ahle/wt/landing/build-dev-fast` at Mox tip
`e81e1f9272f85df16ed1a479d2b3eba670f022f1`:

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

`s4-d2-report.md` is copied from the end-to-end `pc-runner` receipt for
published Mox tip `a0c4488a587` on 2026-10-01. It reports interpreter 5/5 and
compile 0/5. Rows 0 and 2 are `HELD`; rows 1, 3, and 4 are `NEW-REFUSAL`
because their refusal stage moved after provider closure landed. All five now
stop at `apply-demotions` on the same mandatory-retain body promise. The
positive and negative counter controls both pass. The earlier `d0` snapshot at
`s4-d0-report.md` remains for comparison.

The daily check is not a browser lesson action; run it from the perf worktree
with a fresh label:

```text
cd /var/tmp/thomas-ahle/wt/perf
/var/tmp/thomas-ahle/fleet/artifacts/perf/pc-runner/daily.sh d3
```
