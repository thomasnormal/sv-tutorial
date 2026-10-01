import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';

const capabilityReceipts = [
  [
    'sv/macro-formal-continuation',
    'bcdf57717c13858e8031a146aaf8554292d2749c',
    'artifacts/tutorial/capability-receipts/sv__macro-formal-continuation__solution__refdiff.final.txt',
    '70bcc182fc6b32c4e8fac7eaee06196d845ffe8aed28318e592a8887a42224fd'
  ],
  [
    'sv/struct-field-refs',
    '0585a62233b6fc087fcbcd78dd92ab1395f1f4fd',
    'artifacts/tutorial/capability-receipts/sv__struct-field-refs__solution__refdiff.final.txt',
    '4eb7d716460e54ad94242d81f5f1d9c5fb67d1565c250a62ca6ec2d251d43555'
  ],
  [
    'sv/indexed-part-select',
    '5a49d2b68cf059fad392a038c8111db59f6a6eed',
    'artifacts/tutorial/capability-receipts/sv__indexed-part-select__solution__refdiff.final.txt',
    'ece4013deb0c782d749812bba7586a9ea7dd9b2750bfa3747931782e4ea79c64'
  ],
  [
    'sv/nested-child-input',
    '5fdce05081ea458d7d9c6f9934d614f09b498b2e',
    'artifacts/tutorial/capability-receipts/sv__nested-child-input__solution__refdiff.final.txt',
    '353b4404864303525e4a800307026c25dbde4a0a27faee79c3c56d319afbaa62'
  ],
  [
    'sv/sequential-udp-init',
    '36b040f6190ce488d406ce49a1c5e0aafb85d6ac',
    'artifacts/tutorial/capability-receipts/sv__sequential-udp-init__solution__refdiff.final.txt',
    '657718f5569a38a703a0a7795f34f317aac9f35bb83ae5f46b19c7220fa38540'
  ],
  [
    'sv/virtual-provider-closure',
    '3bc88e77921e5e776411d00e133f2b497c750943',
    'artifacts/tutorial/virtual-provider-closure/solution-refdiff.json',
    'd7579c1969f88d393942fd576eccf5043402c3ea20e65c9babfa5a1e89f0890d'
  ]
];

describe('landed capability census', () => {
  it('covers the current Mox tip without stale capability claims', () => {
    const census = readFileSync(
      path.resolve(process.cwd(), 'artifacts/tutorial/content-census.md'),
      'utf8'
    );

    expect(census).toContain('## Current-main refresh — 2026-10-01');
    expect(census).toContain(
      'Mox `origin/main` at\n`ed441eb5b583c8ae6146bbb4b32073fedd4d7b77`'
    );
    expect(census).toContain('e81e1f9272f85df16ed1a479d2b3eba670f022f1');
    expect(census).toContain('4d6185ae036d939c9b7266fe89a25f92ed9c294e');
    expect(census).toContain('published\nbehavior tip');
    expect(census).toContain('`a0c4488a587d753fa9f26d465814aaa44e77586e`');
    expect(census).not.toContain('These four short chapters');
    expect(census).not.toContain('deliberately exclude the later');

    for (const [slug, commit, receiptPath, sourceHash] of capabilityReceipts) {
      expect(census).toContain(`| \`${slug}\` | \`${commit}\`,`);
      const receipt = JSON.parse(readFileSync(path.resolve(process.cwd(), receiptPath), 'utf8'));
      expect(receipt.sha256).toBe(sourceHash);
    }

    expect(census).toContain('| `sv/clocking-sampler-retention` | `3b1760ff2030378cfde16ca319e2c1b806ab9d31`,');
    expect(census).toContain('| `sv/protected-envelope-boundary` | `c3799f427f1e51abcd389dcf15771150223cae75`,');
    expect(census).toContain('same-buffer opaque callback-boundary exercise');
    expect(census).toContain('| `sv/interface-method-receiver` | `ed441eb5b58`,');
  });

  it('labels the native receipt binary as an intermediate landing build', () => {
    for (const filename of [
      'artifacts/tutorial/virtual-provider-closure/README.md',
      'artifacts/tutorial/compile-mode-status/README.md',
      'artifacts/tutorial/receipts/20261001-missing/README.md',
      'artifacts/tutorial/capability-receipts/PROVENANCE.md'
    ]) {
      const receipt = readFileSync(path.resolve(process.cwd(), filename), 'utf8');
      expect(receipt).toContain('intermediate landing binary');
      expect(receipt).toContain('readmem');
      expect(receipt).toContain('not evidence that this binary is published');
    }
  });
});
