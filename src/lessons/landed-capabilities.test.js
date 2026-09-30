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
});
