# Protected envelope boundary receipt

This receipt supports `sv/protected-envelope-boundary`. It documents Mox's
same-buffer comment-form protected-envelope callback with no keyring; it does
not claim protected decryption, licensing, or cross-file envelope support.

## Native example

The commands use CPUs `0-79`, a 30-second wall guard, and the shared landing
build:

```text
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=interpret --max-wall-ms=25000 --top tb src/lessons/sv/protected-envelope-boundary/protected_envelope.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=compile --max-wall-ms=25000 --top tb src/lessons/sv/protected-envelope-boundary/protected_envelope.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=interpret --max-wall-ms=25000 --top tb src/lessons/sv/protected-envelope-boundary/protected_envelope.sol.sv
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=compile --max-wall-ms=25000 --top tb src/lessons/sv/protected-envelope-boundary/protected_envelope.sol.sv
```

The starter fails in both modes with `unterminated protected envelope`. The
solution warns that no keyring was provided and prints
`PASS: opaque protected wrapper` in both modes. The available binary reports
Mox `bcbd69b0d63800f2e057a58acf0fc0377db9411f`, while the exact landed
callback control is recorded at
`/var/tmp/thomas-ahle/fleet/artifacts/landing2/langdesign-0371-3b1760ff203/`.

The committed source hashes are:

```text
protected_envelope.sv     3736b69785fbb71e2c8e751ea6f61dc972369dd5f6d24e877e3df45a3f609363
protected_envelope.sol.sv 7e668eec39dc000cdb73c70e6df8584aa647d028b86eab34dae86997d240e08f
```

## Differential receipts

The starter is `both_fail` because both tools reject the unterminated
envelope. The solution is `reference_only_fail`: Mox compiles the no-key
opaque wrapper, while Xcelium attempts decryption and rejects the unkeyed
comment-form envelope. This mismatch is intentional and is not presented as
portable simulator parity.

## Browser qualification

The browser receipt is interpreter-backed through the pinned WASM runtime and
does not qualify native AOT. The focused lesson run is recorded in
`browser-qa.md`.
