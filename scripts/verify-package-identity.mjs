import { createHash } from 'node:crypto';
import { readFile, stat } from 'node:fs/promises';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

const DEFAULT_MANIFEST = 'static/mox/packages/manifest.json';
const DEFAULT_VERILOG_WASM = 'static/mox/mox-verilog.wasm';

async function sha256File(filePath) {
  const hash = createHash('sha256');
  hash.update(await readFile(filePath));
  return hash.digest('hex');
}

export async function verifyPackageManifest({
  manifestPath = DEFAULT_MANIFEST,
  verilogWasmPath = DEFAULT_VERILOG_WASM
} = {}) {
  const manifest = JSON.parse(await readFile(manifestPath, 'utf8'));
  const packages = Array.isArray(manifest.packages) ? manifest.packages : [];
  if (packages.length === 0) return { packageCount: 0, wasmSha256: null };

  const wasmSha256 = await sha256File(verilogWasmPath);
  const manifestDir = path.dirname(manifestPath);
  for (const [index, entry] of packages.entries()) {
    const label = entry?.name || `packages[${index}]`;
    if (entry.moxVerilogWasmSha256 !== wasmSha256) {
      throw new Error(
        `${label}: producer mox-verilog.wasm SHA-256 ${entry.moxVerilogWasmSha256 || '<missing>'} ` +
        `does not match deployed ${wasmSha256}`
      );
    }
    if (typeof entry.url !== 'string' || !entry.url || entry.url.includes('://')) {
      throw new Error(`${label}: package URL must be a same-origin relative path`);
    }
    const artifactPath = path.resolve(manifestDir, entry.url);
    const [artifactSha256, artifactStat] = await Promise.all([
      sha256File(artifactPath),
      stat(artifactPath)
    ]);
    if (entry.sha256 !== artifactSha256) {
      throw new Error(`${label}: artifact SHA-256 ${entry.sha256 || '<missing>'} does not match ${artifactSha256}`);
    }
    if (entry.bytes !== artifactStat.size) {
      throw new Error(`${label}: artifact size ${entry.bytes ?? '<missing>'} does not match ${artifactStat.size}`);
    }
  }
  return { packageCount: packages.length, wasmSha256 };
}

async function main() {
  const result = await verifyPackageManifest();
  console.log(`Verified ${result.packageCount} precompiled package(s) against deployed mox-verilog.wasm` +
    (result.wasmSha256 ? ` (${result.wasmSha256})` : ''));
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  await main();
}
