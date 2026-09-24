import { describe, expect, it } from 'vitest';
import { COCOTB_WORKER_SOURCE } from './cocotb-worker-source.js';

describe('cocotb worker source', () => {
  it('embeds shared VPI constants', () => {
    expect(COCOTB_WORKER_SOURCE).toContain('"vpiIntVal":6');
    expect(COCOTB_WORKER_SOURCE).toContain('"vpiSimTime":2');
    expect(COCOTB_WORKER_SOURCE).toContain('function wsAddFunctionToTable');
  });

  it('registers ReadOnly triggers as cbReadOnlySynch callbacks', () => {
    expect(COCOTB_WORKER_SOURCE).toMatch(/spec\.type === 'read_only'[\s\S]*?VPI\.cbReadOnlySynch/);
  });

  it('omits debug MLIR dump logging', () => {
    expect(COCOTB_WORKER_SOURCE).not.toContain('MLIR (first 2000 chars)');
  });
});
