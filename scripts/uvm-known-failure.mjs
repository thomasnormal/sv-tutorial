import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

export const PINNED_MOX_VERILOG_WASM_SHA256 =
  'eb6badaf759c72dd4a7dff97d025e58dea75ea0863c2461464219bee69ec65a2';

const PINNED_UVM_ABORT_MARKERS = [
  'mox-verilog --resource-guard=false',
  '--uvm-path /mox/uvm-core',
  'uvm_config_db_implementation.svh:375:26: warning: unknown character escape sequence',
  'Aborted()'
];

export function isPinnedUvmAbort({ log, wasmSha256 }) {
  return (
    wasmSha256 === PINNED_MOX_VERILOG_WASM_SHA256 &&
    PINNED_UVM_ABORT_MARKERS.every((marker) => log.includes(marker))
  );
}

export async function sha256File(filePath) {
  const contents = await readFile(filePath);
  return createHash('sha256').update(contents).digest('hex');
}

async function main() {
  const [logPath, wasmPath] = process.argv.slice(2);
  if (!logPath || !wasmPath) {
    console.error('usage: node scripts/uvm-known-failure.mjs <log> <mox-verilog.wasm>');
    process.exitCode = 2;
    return;
  }

  const [log, wasmSha256] = await Promise.all([
    readFile(logPath, 'utf8'),
    sha256File(wasmPath)
  ]);

  if (!isPinnedUvmAbort({ log, wasmSha256 })) {
    process.exitCode = 1;
    return;
  }

  console.log(
    `recognized pinned-WASM UVM abort (${path.basename(wasmPath)} sha256=${wasmSha256})`
  );
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}
