import { describe, expect, it } from 'vitest';
import { readdirSync, readFileSync, statSync } from 'node:fs';
import path from 'node:path';

const LESSONS_DIR = path.resolve(process.cwd(), 'src/lessons');

function descriptionFiles(dir) {
  const files = [];
  for (const name of readdirSync(dir)) {
    const full = path.join(dir, name);
    if (statSync(full).isDirectory()) files.push(...descriptionFiles(full));
    else if (name === 'description.html') files.push(full);
  }
  return files;
}

describe('lesson HTML contracts', () => {
  it('protects every new-tab lesson link with both opener guards', () => {
    const problems = [];

    for (const file of descriptionFiles(LESSONS_DIR)) {
      const html = readFileSync(file, 'utf8');
      for (const match of html.matchAll(/<a\b[^>]*target\s*=\s*["']_blank["'][^>]*>/gi)) {
        const tag = match[0];
        const rel = tag.match(/\brel\s*=\s*["']([^"']*)["']/i)?.[1]
          .split(/\s+/)
          .map((token) => token.toLowerCase()) ?? [];
        if (!rel.includes('noopener') || !rel.includes('noreferrer')) {
          const relative = path.relative(process.cwd(), file);
          problems.push(`${relative}: ${tag}`);
        }
      }
    }

    expect(problems).toEqual([]);
  });
});
