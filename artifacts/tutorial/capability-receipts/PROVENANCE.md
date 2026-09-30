# Capability receipt provenance

The corrected receipt bundle contains 54 files and includes the sequential-UDP
chapter validated against Mox landing tip `36b040f6190ce488d406ce49a1c5e0aafb85d6ac`.
The tutorial's browser WASM remains the pinned release; it was not rebuilt.

## Immutable hashes

- `final-summary.tsv`: `4e7a47aad5188a3b7ec2bcdd6609e04f46e9f0013495ee4c792c25cc9309e6a2`
- Sorted `sha256sum` digest of the 54 receipt files in this directory,
  excluding this provenance file: `b14ade8bf5482d7517d5a31731b9bb12118aa068de0f8a47764d8f57dc14031a`
  (computed from `sha256sum` output over filenames sorted within this directory).
- Solution source hashes are recorded in each `refdiff` row of `final-summary.tsv`:
  `macro-formal-continuation` `70bcc182fc6b32c4e8fac7eaee06196d845ffe8aed28318e592a8887a42224fd`;
  `struct-field-refs` `4eb7d716460e54ad94242d81f5f1d9c5fb67d1565c250a62ca6ec2d251d43555`;
  `indexed-part-select` `ece4013deb0c782d749812bba7586a9ea7dd9b2750bfa3747931782e4ea79c64`;
  `nested-child-input` `353b4404864303525e4a800307026c25dbde4a0a27faee79c3c56d319afbaa62`.
- The `sha256` field in each UDP differential receipt is the committed source
  blob hash; the `refdiff_cache_key` field preserves the cache identity emitted
  by the differential command. Actual SHA-256 source hashes for the new UDP fixture are
  `sequential_udp.sv` `8b4d8ad11e344f9dc8686bfb0dd7de116f9f6cf8820898f6b1e2350d2ba59557`
  and `sequential_udp.sol.sv` `657718f5569a38a703a0a7795f34f317aac9f35bb83ae5f46b19c7220fa38540`.

## Native and reference argv

Each native receipt used the following command shape, with the lesson's
self-contained source substituted for `<source>` and `--mode` set to the
recorded mode:

```text
taskset -c 0-79 timeout --kill-after=3s 30s /var/tmp/thomas-ahle/wt/landing/build-dev-fast/bin/mox-run --single-unit --timescale=1ns/1ns --mode=<interpret|compile> --max-wall-ms=25000 <source>
```

Each differential receipt used:

```text
/var/tmp/thomas-ahle/fleet/bin/refdiff <source> --build-dir /var/tmp/thomas-ahle/wt/landing/build-dev-fast
```

The full JSON results, including source hashes, verdicts, and build directory,
are the `*.final.txt` files beside the TSV summary.

## Final validation on the corrected tip

- `npm test`: 13 files, 57 tests passed.
- `npm run build`: exit 0.
- `npm run test:e2e`: completed in 15.3 minutes with 131 passed and 98 failed
  (exit 1); the failures are the existing pinned-browser-WASM/Mox and stale
  route limitations. The sequential-UDP target passed 1/1 against the pinned
  browser assets. The immutable full-suite log is
  `artifacts/tutorial/e2e/tutorial-udp-full-e2e.log` (SHA-256
  `043df075681607526f60e3c0a1319dcd5fef170e2572335d8c1638ac9c1128c9`).
  No WASM rebuild was made.
