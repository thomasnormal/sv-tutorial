# Clocking sampler retention receipt

This receipt supports `sv/clocking-sampler-retention`. The solution restores an
explicit `#0` clocking-input skew and passes in both native modes and through
Xcelium `refdiff`; the starter's default input skew fails in both engines.

## Native example

The commands use CPUs `0-79`, a 30-second wall guard, and the current native
Mox build:

```text
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=interpret --max-wall-ms=25000 --top tb src/lessons/sv/clocking-sampler-retention/clocking_sampler.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=compile --max-wall-ms=25000 --top tb src/lessons/sv/clocking-sampler-retention/clocking_sampler.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=interpret --max-wall-ms=25000 --top tb src/lessons/sv/clocking-sampler-retention/clocking_sampler.sol.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=compile --max-wall-ms=25000 --top tb src/lessons/sv/clocking-sampler-retention/clocking_sampler.sol.sv
```

The starter prints `FAIL: first sample=aa` in both modes. The solution prints
`PASS: clocking sample retained=bb` in both modes. The current native Mox
build used for this receipt is `643f9b3d30259a3fbaae4743cb26903e65fdf110`.

The committed source hashes are:

```text
clocking_sampler.sv     25ca50f72941b026d8c96f65890b439a3cf35df69cde8359eed17cc9b9970a4a
clocking_sampler.sol.sv 7231082a4cd4f46b798b65be466590f27927b22a783f50faf67529e068376d96
```

## Differential receipts

`starter-refdiff.json` reports `both_fail` with equal output and
`solution-refdiff.json` reports `both_pass` with equal output. Both receipts
bind their source SHA-256 to the committed fixtures and retain the refdiff
cache key.

## Browser qualification

The browser receipt is interpreter-backed through the pinned WASM runtime; it
does not qualify native AOT. The focused lesson run is recorded in
`browser-qa.md`.
