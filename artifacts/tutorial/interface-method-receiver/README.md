# Interface method receiver receipt

This receipt supports `sv/interface-method-receiver`. The lesson uses two
instances of one interface and a class-held `virtual` interface. The starter
binds `u_a`; the solution binds `u_b` and checks plain, cast, and parenthesized
method calls against `u_b`'s path and answer.

## Standard and landing basis

IEEE 1800-2023 §21.2.1.5 defines `%m` as the hierarchical name of the design
element or subroutine that invokes the system task containing the format
specifier. Section §25.9 defines a virtual interface as a variable representing
an interface instance, permits passing it to methods, and makes the selected
instance's components available through dot notation after initialization.

The native capability landed in Mox commit `ed441eb5b583c8ae6146bbb4b32073fedd4d7b77`,
recorded in the landing ledger as interface-method receiver handling. The
exact-tip build used here is `/var/tmp/thomas-ahle/fleet-probes/ed441-tutorial-20261001/build-dev-fast`;
the source tree is read-only and no Mox worktree was changed. The checked-in
browser WASM predates this landing and is not used as native evidence.

## Native runs

Each run is pinned to CPUs `0-79` and guarded by a 30-second wall timeout. The
import step uses `mox-verilog --ir-llhd`; simulation uses `mox-sim` in the
requested mode.

```text
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/fleet-probes/ed441-tutorial-20261001/build-dev-fast/bin/mox-verilog --ir-llhd --top=tb src/lessons/sv/interface-method-receiver/interface_method_receiver.sv -o <tmp>.mlir
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/fleet-probes/ed441-tutorial-20261001/build-dev-fast/bin/mox-sim <tmp>.mlir --top tb --mode=interpret
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/fleet-probes/ed441-tutorial-20261001/build-dev-fast/bin/mox-sim <tmp>.mlir --top tb --mode=compile --aot-require-zero-interpreter
```

| variant | mode | exit | first result line |
|---|---:|---:|---|
| starter | interpret | 0 | `FAIL: path=tb.u_a cast=tb.u_a paren=tb.u_a answers=1/1` |
| starter | compile | 0 | `FAIL: path=tb.u_a cast=tb.u_a paren=tb.u_a answers=1/1` |
| solution | interpret | 0 | `PASS` |
| solution | compile | 0 | `PASS` |

The solution compile log reports the whole-design zero-interpreter gate as
satisfied. Full logs are `starter-interpret.log`, `starter-compile.log`,
`solution-interpret.log`, and `solution-compile.log`.

## Differential runs

`refdiff` was run on each committed fixture against the exact-tip native build:

```text
/var/tmp/thomas-ahle/fleet/bin/refdiff src/lessons/sv/interface-method-receiver/interface_method_receiver.sv --build-dir /var/tmp/thomas-ahle/fleet-probes/ed441-tutorial-20261001/build-dev-fast
/var/tmp/thomas-ahle/fleet/bin/refdiff src/lessons/sv/interface-method-receiver/interface_method_receiver.sol.sv --build-dir /var/tmp/thomas-ahle/fleet-probes/ed441-tutorial-20261001/build-dev-fast
```

- `starter-refdiff.json`: `both_fail`; reference and Mox exit 0 and output is equal.
- `solution-refdiff.json`: `both_pass`; reference and Mox exit 0 and output is equal.
- The JSON `sha256` values are the committed source hashes. The separate
  `refdiff_cache_key` fields retain the differential-run cache identities.

## Browser qualification

`browser-qa.md` records the focused route result. The browser uses the pinned
WASM, which predates this receiver lowering, so a native receipt must not be
presented as browser qualification or native AOT qualification.
