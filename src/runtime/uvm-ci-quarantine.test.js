import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import {
  isPinnedUvmAbort,
  PINNED_MOX_VERILOG_WASM_SHA256
} from '../../scripts/uvm-known-failure.mjs';

const CI_WORKFLOW = readFileSync(
  path.resolve(process.cwd(), '.github/workflows/ci.yml'),
  'utf8'
);
const NIGHTLY_WORKFLOW = readFileSync(
  path.resolve(process.cwd(), '.github/workflows/uvm-nightly.yml'),
  'utf8'
);

const PINNED_UVM_ABORT_LOG = [
  '$ mox-verilog --resource-guard=false --ir-llhd --uvm-path /mox/uvm-core',
  '/mox/uvm-core/src/base/uvm_config_db_implementation.svh:375:26: warning: unknown character escape sequence',
  'Aborted()'
].join('\n');

describe('UVM CI known-failure quarantine', () => {
  it('recognizes only the pinned WASM UVM abort signature', () => {
    expect(
      isPinnedUvmAbort({
        log: PINNED_UVM_ABORT_LOG,
        wasmSha256: PINNED_MOX_VERILOG_WASM_SHA256
      })
    ).toBe(true);

    expect(
      isPinnedUvmAbort({
        log: PINNED_UVM_ABORT_LOG,
        wasmSha256: 'current-or-unknown-artifact'
      })
    ).toBe(false);

    expect(
      isPinnedUvmAbort({
        log: PINNED_UVM_ABORT_LOG.replace('Aborted()', 'Aborted(OOM)'),
        wasmSha256: PINNED_MOX_VERILOG_WASM_SHA256
      })
    ).toBe(false);
  });

  it('quarantines only the reporting smoke in CI, not nightly parity', () => {
    expect(CI_WORKFLOW).toContain('--known-failure pinned-wasm-uvm-abort');
    expect(CI_WORKFLOW).toContain('run-uvm-browser-worker-matrix.sh');
    expect(NIGHTLY_WORKFLOW).not.toContain('--known-failure');
  });
});
