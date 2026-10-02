import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import metas from './meta.js';
import { BMC_EXPECTED_VERDICTS } from '../lib/bmc-verdict.js';

const root = path.resolve(process.cwd(), 'src/lessons/sva');
const bmcLessons = Object.entries(metas)
  .filter(([, meta]) => meta.runner === 'bmc' || meta.runner === 'both')
  .map(([slug]) => slug.split('/').pop());

describe('BMC lesson presentation', () => {
  it('does not promise a Waves tab for BMC runs', () => {
    const offenders = bmcLessons.filter((name) => {
      const text = readFileSync(path.join(root, name, 'description.html'), 'utf8')
        .replace(/BMC does not generate a Waves tab/g, '');
      return /Waves|waveform/i.test(text);
    });
    expect(offenders).toEqual([]);
  });

  it('uses bounded verdict language instead of claiming unbounded proof', () => {
    const offenders = bmcLessons.filter((name) =>
      /BMC proves\b|BMC proves all\b|Click Verify[^.]*proves\b/i.test(
        readFileSync(path.join(root, name, 'description.html'), 'utf8')
      )
    );
    expect(offenders).toEqual([]);
  });

  it('declares the expected bounded verdict for every BMC lesson', () => {
    const missing = Object.entries(metas)
      .filter(([, meta]) => meta.runner === 'bmc' || meta.runner === 'both')
      .filter(([, meta]) => !BMC_EXPECTED_VERDICTS.has(meta.bmcExpected))
      .map(([slug]) => slug);
    expect(missing).toEqual([]);
  });

  it('keeps the formal starter tasks aligned with the supplied skeletons', () => {
    const cases = [
      ['formal-intro', 'assertion skeleton are provided', 'Add a concurrent assertion'],
      ['formal-assume', 'starter already provides', 'Add an <code>assume property</code>'],
      ['disable-iff', 'clause are provided', 'add <code>disable iff'],
    ];
    for (const [name, required, forbidden] of cases) {
      const text = readFileSync(path.join(root, name, 'description.html'), 'utf8');
      expect(text).toContain(required);
      expect(text).not.toContain(forbidden);
    }
  });
});
