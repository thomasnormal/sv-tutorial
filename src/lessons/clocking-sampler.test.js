import { describe, expect, it } from 'vitest';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import path from 'node:path';

const root = path.resolve(process.cwd());
const lessonDir = path.join(root, 'src/lessons/sv/clocking-sampler-retention');
const description = readFileSync(path.join(lessonDir, 'description.html'), 'utf8');
const starter = readFileSync(path.join(lessonDir, 'clocking_sampler.sv'), 'utf8');
const solution = readFileSync(path.join(lessonDir, 'clocking_sampler.sol.sv'), 'utf8');

describe('clocking sampler retention lesson', () => {
  it('teaches standard clocking-block sampling without internal status text', () => {
    expect(description).toContain('IEEE 1800-2023 §14.3');
    expect(description).toContain('§14.4');
    expect(description).toContain('§14.13');
    expect(description).toContain('explicit <code>#0</code>');
    expect(description).toContain('sampled values');
    expect(description).not.toMatch(/Mox|WASM|Mox's|commit|receipt|\/var\/tmp|fleet|census/i);
  });

  it('keeps the starter and solution distinct and binds both refdiff receipts', () => {
    expect(starter).toContain('input sig;');
    expect(starter).not.toContain('input #0 sig;');
    expect(solution).toContain('input #0 sig;');

    for (const [file, expectedCategory] of [
      ['starter-refdiff.json', 'both_fail'],
      ['solution-refdiff.json', 'both_pass'],
    ]) {
      const sourceName = file.startsWith('starter') ? 'clocking_sampler.sv' : 'clocking_sampler.sol.sv';
      const source = readFileSync(path.join(lessonDir, sourceName));
      const receipt = JSON.parse(
        readFileSync(path.join(root, 'artifacts/tutorial/clocking-sampler-retention', file), 'utf8')
      );
      expect(receipt.category).toBe(expectedCategory);
      expect(receipt.sha256).toBe(createHash('sha256').update(source).digest('hex'));
    }
  });
});
