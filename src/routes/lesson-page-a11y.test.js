import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';

const lessonPage = readFileSync(
  path.resolve(process.cwd(), 'src/routes/lesson/[part]/[name]/+page.svelte'),
  'utf8'
);

describe('lesson panel accessibility contract', () => {
  it('keeps every draggable separator keyboard-resizable and measurable', () => {
    expect((lessonPage.match(/role="separator"/g) ?? []).length).toBe(4);
    expect((lessonPage.match(/tabindex="0"/g) ?? []).length).toBe(4);
    expect((lessonPage.match(/aria-valuemin=/g) ?? []).length).toBe(4);
    expect((lessonPage.match(/aria-valuemax=/g) ?? []).length).toBe(4);
    expect((lessonPage.match(/aria-valuenow=/g) ?? []).length).toBe(4);
    expect((lessonPage.match(/onkeydown=\{\(e\) => adjustResize/g) ?? []).length).toBe(4);
    expect(lessonPage).toContain("{ ArrowLeft: -1, ArrowRight: 1 }");
    expect(lessonPage).toContain("{ ArrowUp: -1, ArrowDown: 1 }");
  });
});
