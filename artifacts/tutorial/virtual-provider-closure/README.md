# Virtual method provider-closure receipt

This receipt supports `sv/virtual-provider-closure`. The lesson is a
self-contained virtual-method dispatch example and is bounded to less than
30 seconds on CPUs `0-79`.

## Landing basis

The capability landed in Mox tip
`3bc88e77921e5e776411d00e133f2b497c750943` (`[mox-sim] Preserve provider
bodies for vtable closure`), recorded by
`/var/tmp/thomas-ahle/fleet/artifacts/landing/push-3bc88e77921.md`. The
landing control is the mapped-vlib provider regression
`test/Tools/mox-run/vlib-mapped-vtable-provider-closure.sv`; its exact-tip
focused controls passed 4/4 after rebuilding the matching frontend. The
lesson keeps its source self-contained, while the native receipt below checks
the same user-visible base-handle/derived-object dispatch shape.

The native build used for this receipt is
`/var/tmp/thomas-ahle/wt/landing/build-dev-fast`, Mox tip
`e81e1f9272f85df16ed1a479d2b3eba670f022f1`. That tree contains the landed
provider-closure change and was not modified by this lane.

## Native runs

Commands, each pinned to CPUs `0-79` with a 30-second outer timeout:

```text
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=interpret --max-wall-ms=25000 --top tb src/lessons/sv/virtual-provider-closure/virtual_provider.sv -v 1
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=compile --max-wall-ms=25000 --top tb src/lessons/sv/virtual-provider-closure/virtual_provider.sv -v 1
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=interpret --max-wall-ms=25000 --top tb src/lessons/sv/virtual-provider-closure/virtual_provider.sol.sv -v 1
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=compile --max-wall-ms=25000 --top tb src/lessons/sv/virtual-provider-closure/virtual_provider.sol.sv -v 1
```

| variant | mode | exit | first result line |
|---|---:|---:|---|
| starter | interpret | 0 | `FAIL: virtual provider value=6 id=606` |
| starter | compile | 0 | `FAIL: virtual provider value=6 id=606` |
| solution | interpret | 0 | `PASS: virtual provider value=7 id=707` |
| solution | compile | 0 | `PASS: virtual provider value=7 id=707` |

Full logs are `starter-interpret.log`, `starter-compile.log`,
`solution-interpret.log`, and `solution-compile.log` in this directory.

The pinned-browser lesson check is recorded in `browser-qa.md`: the focused
Playwright run passed 1/1 through the interpreter-backed WASM fallback.

## Differential runs

`refdiff` was run on each committed fixture against the same native build:

```text
/var/tmp/thomas-ahle/fleet/bin/refdiff src/lessons/sv/virtual-provider-closure/virtual_provider.sv --build-dir /var/tmp/thomas-ahle/wt/landing/build-dev-fast
/var/tmp/thomas-ahle/fleet/bin/refdiff src/lessons/sv/virtual-provider-closure/virtual_provider.sol.sv --build-dir /var/tmp/thomas-ahle/wt/landing/build-dev-fast
```

- `starter-refdiff.json`: `both_fail`, reference and Mox exit 0, output equal.
- `solution-refdiff.json`: `both_pass`, reference and Mox exit 0, output equal.
- The JSON `sha256` values are hashes of the committed fixtures; the original
  refdiff cache identities are retained as `refdiff_cache_key`.

The browser Run action remains interpreter-backed by the pinned WASM. No WASM
rebuild or Mox worktree change is part of this chapter.
