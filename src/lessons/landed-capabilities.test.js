import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import meta from './meta.js';

const root = path.resolve(process.cwd(), 'src/lessons');
const capabilities = [
  ['sv/macro-formal-continuation', 'macro_formal'],
  ['sv/struct-field-refs', 'struct_field'],
  ['sv/indexed-part-select', 'indexed_part_select'],
  ['sv/nested-child-input', 'nested_child_input']
];

describe('landed Mox capability lessons', () => {
  it('are registered with runnable simulation metadata', () => {
    for (const [slug, basename] of capabilities) {
      expect(meta[slug]?.runner ?? 'sim').toBe('sim');
      const dir = path.join(root, slug);
      const source = readFileSync(path.join(dir, `${basename}.sv`), 'utf8');
      const solution = readFileSync(path.join(dir, `${basename}.sol.sv`), 'utf8');
      expect(source).toContain('module tb');
      expect(solution).toContain('$display("PASS")');
    }
  });

  it('keeps the indexed-select starter unsolved and its range wording precise', () => {
    const dir = path.join(root, 'sv/indexed-part-select');
    const source = readFileSync(path.join(dir, 'indexed_part_select.sv'), 'utf8');
    const description = readFileSync(path.join(dir, 'description.html'), 'utf8');
    const receipts = readFileSync(
      path.resolve(process.cwd(), 'artifacts/tutorial/capability-receipts/final-summary.tsv'),
      'utf8'
    );
    expect(source).toContain('base = 2;');
    expect(source).toContain("inside_slice !== 4'b1101");
    expect(description).toContain('completely out-of-range read');
    expect(description).not.toContain('A partially out-of-range read returns');
    expect(receipts).toContain('sv/indexed-part-select\tstarter\tinterpret\t0\tFAIL: inside=0101 partial=xxxx');
    expect(receipts).toContain('sv/indexed-part-select\tstarter\tcompile\t0\tFAIL: inside=0101 partial=xxxx');
  });
});
