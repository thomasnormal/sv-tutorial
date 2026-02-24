import { describe, expect, it } from 'vitest';
import { WORKER_RUNTIME_HELPERS_SOURCE } from './worker-runtime-helpers-source.js';

describe('worker runtime helpers source', () => {
  it('provides shared helpers for path + noderawfs loading', () => {
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('var WORKER_PATH_SHIM');
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('function isNoderawfsScript');
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('function fetchScriptText');
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('function installPathRequireOnly');
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('function loadEmscriptenTool');
  });
});
