import { describe, expect, it } from 'vitest';
import { existsSync, readdirSync, readFileSync } from 'node:fs';
import path from 'node:path';
import meta from './meta.js';

const root = path.resolve(process.cwd());
const receiptDir = path.join(root, 'artifacts/tutorial/receipts');
const missingDir = path.join(receiptDir, '20261001-missing');

function genericReceiptSlugs() {
  return readdirSync(receiptDir)
    .filter((name) => /^.+__(interpret|compile)\.json$/.test(name))
    .map((name) => name.replace(/__(interpret|compile)\.json$/, '').replace('__', '/'));
}

describe('tutorial receipt coverage', () => {
  it('accounts for every registered lesson with a durable receipt bundle', () => {
    const matrix = JSON.parse(readFileSync(path.join(missingDir, 'matrix.json'), 'utf8'));
    const specialized = [
      'sv/compile-mode-status',
      'sv/indexed-part-select',
      'sv/macro-formal-continuation',
      'sv/nested-child-input',
      'sv/sequential-udp-init',
      'sv/clocking-sampler-retention',
      'sv/protected-envelope-boundary',
      'sv/struct-field-refs',
      'sv/virtual-provider-closure',
      'sv/wide-readmem',
      'sv/coverage-option-text',
      'sv/interface-method-receiver'
    ];
    const covered = new Set([
      ...genericReceiptSlugs(),
      ...specialized,
      ...matrix.entries.map((entry) => entry.slug)
    ]);
    expect([...covered].sort()).toEqual(Object.keys(meta).sort());
  });

  it('keeps every missing-matrix log and exit result bound to its row', () => {
    const matrix = JSON.parse(readFileSync(path.join(missingDir, 'matrix.json'), 'utf8'));
    for (const entry of matrix.entries) {
      expect(entry.runs.length).toBeGreaterThan(0);
      for (const run of entry.runs) {
        expect(existsSync(path.join(missingDir, run.log))).toBe(true);
        expect(run.exit).toBeTypeOf('number');
        expect(['PASS', 'FAIL', 'BLOCKED']).toContain(run.result);
      }
    }
  });

  it('keeps the full browser receipt durable and truthful', () => {
    const log = readFileSync(
      path.join(root, 'artifacts/tutorial/e2e/tutorial-full-e2e-20261001.log'),
      'utf8'
    );
    expect(log).toContain('177 passed (29.6m)');
    expect(log).toContain('e2e_exit=1');
  });
});
