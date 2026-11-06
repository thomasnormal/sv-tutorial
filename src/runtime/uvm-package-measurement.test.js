import { afterEach, expect, it } from 'vitest';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { mkdtemp, readFile, readdir, rm, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import os from 'node:os';
import path from 'node:path';

const run = promisify(execFile);
const scratch = [];

afterEach(async () => {
  await Promise.all(scratch.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

async function fixture() {
  const dir = await mkdtemp(path.join(os.tmpdir(), 'svt-measure-test-'));
  scratch.push(dir);
  const frontend = path.join(dir, 'frontend');
  const artifact = path.join(dir, 'package.vlib');
  const output = path.join(dir, 'matrix.md');
  await writeFile(artifact, 'original artifact');
  await writeFile(frontend, `#!/usr/bin/env node
const fs = require('node:fs');
const args = process.argv.slice(2);
if (args.includes('--version')) {
  console.log('MOX test-commit\\nmox-frontend-v1:test-identity');
  process.exit(0);
}
if (args.includes('--read-vlib')) {
  if (process.env.SVT_MEASURE_MUTATE === '1')
    fs.writeFileSync(args[args.indexOf('--read-vlib') + 1], 'replaced artifact');
  console.error('tb_top.sv:7:5: error: imported method receiver is invalid');
  process.exit(1);
}
const staged = fs.readFileSync(require('node:path').join(
  require('node:path').dirname(args.at(-1)), 'my_test.sv'), 'utf8');
if (!staged.includes('Hello from UVM!')) throw new Error('solution was not staged');
fs.writeFileSync(args[args.indexOf('-o') + 1], 'module {}');
console.log('source compiled');
`, { mode: 0o755 });
  return {
    dir, artifact, output,
    args: ['scripts/measure-uvm-package.mjs', '--mox-verilog', frontend,
      '--uvm-root', 'static/mox/uvm-core', '--artifact', artifact,
      '--output', output, '--artifact-mode', 'lowered', '--lesson', 'reporting',
      '--timeout-ms', '2000']
  };
}

async function evidence(f) {
  const [name] = (await readdir(f.dir)).filter((name) => name.startsWith('matrix.md.logs-'));
  const dir = path.join(f.dir, name);
  return { dir, receipt: JSON.parse(await readFile(path.join(dir, 'receipt.json'), 'utf8')) };
}

it('preserves exact commands, identity and diagnostics after intermediate cleanup', async () => {
  const f = await fixture();
  await run(process.execPath, f.args);
  const { dir, receipt } = await evidence(f);
  expect(receipt.frontendVersion).toContain('mox-frontend-v1:test-identity');
  expect(receipt.artifactSha256).toBe(createHash('sha256').update('original artifact').digest('hex'));
  expect(receipt.inputsUnchanged).toBe(true);
  const row = receipt.rows[0];
  expect(row.source.code).toBe(0);
  expect(row.artifact.code).toBe(1);
  expect(row.artifact.args).toContain('--read-vlib-lowered-library-ir');
  expect(row.artifactMlirBytes).toBe(0);
  expect(await readFile(path.join(dir, row.artifact.log), 'utf8'))
    .toContain('error: imported method receiver is invalid');
  expect(await readFile(f.output, 'utf8')).toContain('Inputs unchanged during matrix: yes');
});

it('invalidates the receipt when an artifact is replaced during the matrix', async () => {
  const f = await fixture();
  await expect(run(process.execPath, f.args, {
    env: { ...process.env, SVT_MEASURE_MUTATE: '1' }
  })).rejects.toThrow();
  expect((await evidence(f)).receipt.inputsUnchanged).toBe(false);
  expect(await readFile(f.output, 'utf8')).toContain('INVALID RECEIPT');
});
