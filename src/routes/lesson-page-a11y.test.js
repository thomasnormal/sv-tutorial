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

  it('connects runtime tabs to labelled panels', () => {
    expect(lessonPage).toContain('role="tablist" aria-label="Runtime output"');
    expect(lessonPage).toContain('id="runtime-tab-logs" role="tab" aria-controls="runtime-panel-logs"');
    expect(lessonPage).toContain('id="runtime-tab-waves" role="tab" aria-controls="runtime-panel-waves"');
    expect((lessonPage.match(/onkeydown=\{onRuntimeTabKeydown\}/g) ?? []).length).toBe(2);
    expect((lessonPage.match(/tabindex=\{activeRuntimeTab === '(?:logs|waves)' \? 0 : -1\}/g) ?? []).length).toBe(2);
    expect(lessonPage).toContain("if (e.key === 'ArrowRight')");
    expect(lessonPage).toContain("else if (e.key === 'Home') next = 0;");
    expect(lessonPage).toContain('id="runtime-panel-logs"\n        role="tabpanel"\n        aria-labelledby="runtime-tab-logs"');
    expect(lessonPage).toContain('id="runtime-panel-waves"\n          role="tabpanel"\n          aria-labelledby="runtime-tab-waves"');
  });
});
