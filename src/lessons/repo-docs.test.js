import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';

describe('repository documentation', () => {
  it('keeps README and CLAUDE aligned with the current toolchain and app tree', () => {
    const readme = readFileSync(path.resolve(process.cwd(), 'README.md'), 'utf8');
    const claude = readFileSync(path.resolve(process.cwd(), 'CLAUDE.md'), 'utf8');
    const lock = readFileSync(path.resolve(process.cwd(), 'scripts/toolchain.lock.sh'), 'utf8');

    expect(readme).toContain('scripts/toolchain.lock.sh');
    expect(readme).not.toContain('8e8ca87dcda1c8abd47103ae7789c8ed261d5de3');
    expect(readme).not.toContain('972cd847efb20661ea7ee8982dd19730aa040c75');
    expect(claude).toContain('src/lessons/index.js');
    expect(claude).toContain('src/routes/lesson/[part]/[name]/+page.svelte');
    expect(claude).not.toContain('src/tutorial-data.js');
    expect(claude).not.toContain('src/App.svelte');
    expect(lock).toMatch(/MOX_REF_LOCKED="[0-9a-f]{40}"/);
    expect(lock).toMatch(/MOX_LLVM_SUBMODULE_REF_LOCKED="[0-9a-f]{40}"/);
  });
});
