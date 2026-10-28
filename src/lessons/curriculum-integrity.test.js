import { describe, expect, it } from 'vitest';
import { readFileSync, readdirSync, statSync } from 'node:fs';
import path from 'node:path';
import meta from './meta.js';

const removedStatusLessons = [
  'sv/macro-formal-continuation',
  'sv/struct-field-refs',
  'sv/indexed-part-select',
  'sv/nested-child-input',
  'sv/sequential-udp-init',
  'sv/compile-mode-status',
  'sv/protected-envelope-boundary',
  'sv/virtual-provider-closure',
  'sv/wide-readmem',
  'sv/coverage-option-text',
  'sv/interface-method-receiver'
];

function publicLessonFiles(dir, files = []) {
  for (const name of readdirSync(dir)) {
    const file = path.join(dir, name);
    if (statSync(file).isDirectory()) publicLessonFiles(file, files);
    else if (/\.(html|sv|svh)$/.test(file)) files.push(file);
  }
  return files;
}

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

  it('keeps internal regression status pages and references out of public content', () => {
    for (const slug of removedStatusLessons) expect(meta[slug]).toBeUndefined();

    const publicFiles = [path.resolve(process.cwd(), 'CURRICULUM.md'), ...publicLessonFiles(path.resolve(process.cwd(), 'src/lessons'))];
    const internalReference = /\/var\/tmp|thomas-ahle|fleet\/|\bcensus\b|\b(?:AGREE|NEW-REFUSAL|ORACLE-DRIFT|DIVERGE)\b|\b(?=[0-9a-f]{12,40}\b)(?=[0-9a-f]*\d)[0-9a-f]+\b/i;
    const offenders = publicFiles.filter((file) => internalReference.test(readFileSync(file, 'utf8')));
    expect(offenders).toEqual([]);

    const viteConfig = readFileSync(path.resolve(process.cwd(), 'vite.config.js'), 'utf8');
    expect(viteConfig).not.toMatch(/sourcemap:\s*true/);
  });
});
