import { describe, expect, it } from 'vitest';
import { readdirSync, readFileSync } from 'node:fs';
import path from 'node:path';

const root = path.resolve(process.cwd(), 'src/lessons/sva');
const bmcLessons = readdirSync(root).filter((name) => name !== 'lec' && name !== 'concurrent-sim');

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
});
