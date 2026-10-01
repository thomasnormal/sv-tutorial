import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import meta from './meta.js';

describe('curriculum integrity', () => {
  it('marks only registered lesson slugs as existing', () => {
    const curriculum = readFileSync(path.resolve(process.cwd(), 'CURRICULUM.md'), 'utf8');
    const missing = [];
    for (const line of curriculum.split('\n')) {
      const match = line.match(/^\| `([^`]+)` \| .*\| ✅ \|/);
      if (match && !meta[match[1]]) missing.push(match[1]);
    }
    expect(missing).toEqual([]);
  });

  it('does not advertise concepts absent from the corresponding lessons', () => {
    const curriculum = readFileSync(path.resolve(process.cwd(), 'CURRICULUM.md'), 'utf8');
    expect(curriculum).not.toContain('2-state `int`/`bit` (testbench)');
    expect(curriculum).not.toContain('apostrophe cast `state_t\'(bits)`');
    expect(curriculum).not.toContain('`$get_coverage()`');
    expect(curriculum).toContain('cycle-counted stimulus');
  });
});
