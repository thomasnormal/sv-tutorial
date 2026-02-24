import { describe, expect, it } from 'vitest';
import { WORKER_NODE_COMPAT_SOURCE } from './worker-node-compat-source.js';

describe('worker node compat source', () => {
  it('defines setup helper with process + require shims', () => {
    expect(WORKER_NODE_COMPAT_SOURCE).toContain('function setupWorkerNodeCompat');
    expect(WORKER_NODE_COMPAT_SOURCE).toContain("process.binding(");
    expect(WORKER_NODE_COMPAT_SOURCE).toContain("mod === 'path'");
    expect(WORKER_NODE_COMPAT_SOURCE).toContain("mod === 'fs'");
  });
});
