import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';

describe('landed capability census', () => {
  it('covers the current Mox tip without stale capability claims', () => {
    const census = readFileSync(
      path.resolve(process.cwd(), 'artifacts/tutorial/content-census.md'),
      'utf8'
    );

    expect(census).toContain('## Current-main refresh — 2026-10-01');
    expect(census).toContain('Mox `origin/main` at `9fe4bd9d5ac`');
    expect(census).toContain('published behavior tip');
    expect(census).toContain('`a0c4488a587`');
    expect(census).not.toContain('These four short chapters');
    expect(census).not.toContain('deliberately exclude the later');

    for (const slug of [
      'sv/macro-formal-continuation',
      'sv/struct-field-refs',
      'sv/indexed-part-select',
      'sv/nested-child-input',
      'sv/sequential-udp-init',
      'sv/virtual-provider-closure'
    ]) {
      expect(census).toContain(`| \`${slug}\` |`);
    }

    expect(census).toContain('No additional user-facing language capability');
    expect(census).toContain('omitted from this chapter set');
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
