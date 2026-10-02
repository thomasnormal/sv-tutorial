import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';

const description = readFileSync(
  path.resolve(process.cwd(), 'src/lessons/sva/triggered/description.html'),
  'utf8'
);

describe('sequence method lesson', () => {
  it('describes triggered and matched according to IEEE 1800-2023', () => {
    expect(description).toContain('IEEE 1800-2023 §16.9.11');
    expect(description).toContain('IEEE 1800-2023 §16.13.5');
    expect(description).toMatch(/IEEE 1800-2023 §§16\.9\.11 and 16\.13\.6/);
    expect(description).toContain('inside another sequence');
    expect(description).not.toMatch(/\.triggered[^.]*can only be used in the antecedent/i);
    expect(description).not.toMatch(/\.matched[^.]*stays true until the next clock edge of a different clock domain/i);
  });
});
