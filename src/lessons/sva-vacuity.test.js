import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';

const descriptions = [
  'src/lessons/sva/vacuous-pass/description.html',
  'src/lessons/sva/cover-property/description.html',
  'src/lessons/sva/concurrent-sim/description.html'
].map((file) => readFileSync(file, 'utf8'));

describe('SVA coverage explanations', () => {
  it('grounds vacuity and cover semantics in the IEEE clauses', () => {
    for (const text of descriptions) {
      expect(text).toMatch(/16\.14\.3/);
      expect(text).toMatch(/16\.14\.8/);
    }
  });

  it('does not claim a cover pass action proves the antecedent fired', () => {
    const text = descriptions.join('\n');
    expect(text).not.toMatch(/pass action[^.]*confirm(?:s|ing) the antecedent/i);
    expect(text).not.toMatch(/cover property is essential[^.]*confirm/i);
  });

  it('uses a sequence cover for the nonvacuous request/grant exercise', () => {
    const text = descriptions[0];
    expect(text).toContain('cover sequence');
    expect(text).toContain('##[1:2]');
    expect(text).not.toContain('add the <code>assert</code> and <code>cover property</code>');
  });
});
