import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';

const description = readFileSync(
  path.resolve(process.cwd(), 'src/lessons/sva/stable-past/description.html'),
  'utf8'
);
const plainText = description.replace(/<[^>]+>/g, ' ');

describe('sampled value lesson', () => {
  it('describes sampling and four-state stability accurately', () => {
    expect(description).toContain('IEEE 1800-2023 §16.5.1');
    expect(description).toContain('===');
    expect(description).toContain('sampled values taken from the Preponed region');
    expect(description).not.toContain('evaluated in SVA\'s Observed region');
    expect(
      plainText.match(/while\s+valid\s+is\s+high\s+and\s+ready\s+is\s+low,\s+data\s+must\s+not\s+change\s+on\s+the\s+next\s+cycle/gi)
    ).toHaveLength(1);
  });
});
