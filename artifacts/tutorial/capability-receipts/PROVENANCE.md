# Capability receipt provenance

The corrected receipt bundle is pinned to tutorial commit
`e096f9a814ad65cda0921c92c02ce070c9eb33c1` (the indexed-part-select starter
calibration and its regression assertions). The bundle contains 42 files.

## Immutable hashes

- `final-summary.tsv`: `f6dd8c06383714e8ba95d2843cf03bfd40838338cb42cfb6d7a96c3bfe5dea6b`
- Sorted `sha256sum` digest of the 42 receipt files in this directory,
  excluding this provenance file: `f99454a7b7294b8b29d307333e6a56bb4ca7d07da284505701e24d2fab29033f`
- Solution source hashes are recorded in each `refdiff` row of `final-summary.tsv`:
  `macro-formal-continuation` `70bcc182fc6b32c4e8fac7eaee06196d845ffe8aed28318e592a8887a42224fd`;
  `struct-field-refs` `4eb7d716460e54ad94242d81f5f1d9c5fb67d1565c250a62ca6ec2d251d43555`;
  `indexed-part-select` `ece4013deb0c782d749812bba7586a9ea7dd9b2750bfa3747931782e4ea79c64`;
  `nested-child-input` `353b4404864303525e4a800307026c25dbde4a0a27faee79c3c56d319afbaa62`.

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

- `npm test`: 13 files, 55 tests passed.
- `npm run build`: exit 0.
- `npm run test:e2e`: completed in 30.2 minutes with 175 passed and 53 failed;
  the failures are the existing pinned-browser-WASM/Mox limitations, including
  the expected macro, packed-struct, and nested-child rows that require a WASM
  rebuild. Indexed part-select passed in the browser. No WASM rebuild was made.
