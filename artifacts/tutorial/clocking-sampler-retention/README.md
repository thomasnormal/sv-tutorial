# Clocking sampler retention receipt

This receipt supports `sv/clocking-sampler-retention`. The solution restores an
explicit `#0` clocking-input skew and passes in both native modes and through
Xcelium `refdiff`; the starter's default input skew fails in both engines.

## Native example

The commands use CPUs `0-79`, a 30-second wall guard, and the shared landing
build:

```text
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=interpret --max-wall-ms=25000 --top tb src/lessons/sv/clocking-sampler-retention/clocking_sampler.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=compile --max-wall-ms=25000 --top tb src/lessons/sv/clocking-sampler-retention/clocking_sampler.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=interpret --max-wall-ms=25000 --top tb src/lessons/sv/clocking-sampler-retention/clocking_sampler.sol.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=compile --max-wall-ms=25000 --top tb src/lessons/sv/clocking-sampler-retention/clocking_sampler.sol.sv
```

The starter prints `FAIL: first sample=aa` in both modes. The solution prints
`PASS: clocking sample retained=bb` in both modes. The available binary reports
Mox `bcbd69b0d63800f2e057a58acf0fc0377db9411f`, which predates the landed
MQ93 test lock but reproduces its behavior. The exact current-main landing
receipt for the upstream MQ93 control is recorded at
`/var/tmp/thomas-ahle/fleet/artifacts/landing2/sched-r5-9529d51aacb/`.

The committed source hashes are:

```text
clocking_sampler.sv     75d8287e2293d920c34c1aee73473a7aef293b0b0ddc660bd994e3d8ee06b006
clocking_sampler.sol.sv e4a21ce79f011dcbd439935ecad93d7cfbcd6bf54dc7acbe7432e923670ec117
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
