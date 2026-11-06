#!/usr/bin/env node

/**
 * Measure the generic package import boundary against source-backed UVM.
 *
 * The lesson files are staged the same way as the browser workspace: a
 * `.sol.sv` file replaces its starter file, then tb_top.sv is the sole
 * frontend root (its includes pull in the lesson sources). The output is a
 * markdown receipt suitable for results/ or the Item 23 journal.
 */
import { mkdtemp, mkdir, readdir, stat, writeFile, rm, cp } from 'node:fs/promises';
import { createReadStream } from 'node:fs';
import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';

const REPO_ROOT = process.cwd();
const LESSON_ROOT = path.join(REPO_ROOT, 'src', 'lessons', 'uvm');
const DEFAULT_LESSONS = [
  'reporting', 'seq-item', 'sequence', 'driver', 'constrained-random',
  'monitor', 'env', 'covergroup', 'cross-coverage', 'coverage-driven',
  'factory-override', 'ral'
];

function usage() {
  console.error(`Usage: node scripts/measure-uvm-package.mjs --mox-verilog PATH \
  --uvm-root PATH --artifact PATH --output PATH [--artifact-mode mapped|lowered] \
  [--lesson SLUG] [--timeout-ms N]`);
  process.exit(2);
}

function parseArgs(argv) {
  const out = { lessons: DEFAULT_LESSONS, timeoutMs: 900_000, output: '', artifactMode: 'mapped' };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--mox-verilog') out.moxVerilog = argv[++i];
    else if (arg === '--uvm-root') out.uvmRoot = argv[++i];
    else if (arg === '--artifact') out.artifact = argv[++i];
    else if (arg === '--output') out.output = argv[++i];
    else if (arg === '--artifact-mode') out.artifactMode = argv[++i];
    else if (arg === '--lesson') out.lessons = [argv[++i]];
    else if (arg === '--timeout-ms') out.timeoutMs = Number(argv[++i]);
    else if (arg === '--help' || arg === '-h') usage();
    else usage();
  }
  if (!out.moxVerilog || !out.uvmRoot || !out.artifact || !out.output ||
      !Number.isFinite(out.timeoutMs) || out.timeoutMs < 1 ||
      !['mapped', 'lowered'].includes(out.artifactMode)) usage();
  return out;
}

async function stageLesson(slug, tempRoot) {
  const sourceDir = path.join(LESSON_ROOT, slug);
  const destination = path.join(tempRoot, slug);
  await mkdir(destination, { recursive: true });
  const names = (await readdir(sourceDir)).filter((name) => /\.sv$/i.test(name));
  const solved = new Set(names.filter((name) => name.endsWith('.sol.sv'))
    .map((name) => name.replace(/\.sol\.sv$/, '.sv')));
  for (const name of names) {
    if (!name.endsWith('.sol.sv') && solved.has(name)) continue;
    const destinationName = name.endsWith('.sol.sv')
      ? name.replace(/\.sol\.sv$/, '.sv')
      : name;
    await cp(path.join(sourceDir, name), path.join(destination, destinationName));
  }
  return destination;
}

function runFrontend(executable, args, timeoutMs, logPath) {
  return new Promise((resolve, reject) => {
    const started = Date.now();
    const output = [];
    const child = spawn(executable, args, { cwd: REPO_ROOT });
    const append = (chunk) => output.push(String(chunk));
    child.stdout.on('data', append);
    child.stderr.on('data', append);
    let timedOut = false;
    const timer = setTimeout(() => {
      timedOut = true;
      child.kill('SIGTERM');
      setTimeout(() => child.kill('SIGKILL'), 1000).unref();
    }, timeoutMs);
    child.on('error', reject);
    child.on('close', async (code, signal) => {
      clearTimeout(timer);
      const elapsedMs = Date.now() - started;
      const text = output.join('');
      try {
        await writeFile(logPath, text);
      } catch (error) {
        reject(error);
        return;
      }
      resolve({
        args,
        log: path.basename(logPath),
        code: timedOut ? null : code,
        signal,
        timedOut,
        elapsedMs,
        output: text
      });
    });
  });
}

async function sha256(filePath) {
  const hash = createHash('sha256');
  for await (const chunk of createReadStream(filePath)) hash.update(chunk);
  return hash.digest('hex');
}

function bytesOrZero(filePath) {
  return stat(filePath).then((value) => value.size).catch(() => 0);
}

function formatMs(value) {
  return value == null ? 'timeout' : String(value);
}

function formatStatus(result) {
  if (result.timedOut) return 'TIMEOUT';
  return result.code === 0 ? 'PASS' : `FAIL(${result.code ?? 'signal'})`;
}

async function main() {
  const options = parseArgs(process.argv.slice(2));
  await mkdir(path.dirname(options.output), { recursive: true });
  // Each receipt owns a distinct log directory so a later rerun cannot
  // overwrite its diagnostics. Only large intermediate MLIR files are temporary.
  const evidenceDir = await mkdtemp(`${options.output}.logs-`);
  const tempRoot = await mkdtemp(path.join(os.tmpdir(), 'svt-uvm-package-'));
  const rows = [];
  try {
    const started = new Date().toISOString();
    const frontendSha256 = await sha256(options.moxVerilog);
    const artifactSha256 = await sha256(options.artifact);
    const artifactBytes = (await stat(options.artifact)).size;
    const version = await runFrontend(options.moxVerilog, ['--version'],
      options.timeoutMs, path.join(evidenceDir, 'frontend-version.log'));
    if (version.code !== 0) throw new Error('Cannot read frontend version; see ' + evidenceDir);
    for (const slug of options.lessons) {
      const lessonDir = await stageLesson(slug, tempRoot);
      const sourceOutput = path.join(tempRoot, `${slug}.source.mlir`);
      const artifactOutput = path.join(tempRoot, `${slug}.artifact.mlir`);
      const sourceLog = path.join(evidenceDir, `${slug}.source.log`);
      const artifactLog = path.join(evidenceDir, `${slug}.artifact.log`);
      const artifactFlags = options.artifactMode === 'lowered'
        ? ['--read-vlib', options.artifact, '--read-vlib-lowered-library-ir']
        : ['--read-vlib', options.artifact, '--read-vlib-mapped-moore-ir'];
      const common = [
        '--resource-guard=false', '--ir-llhd', '--timescale', '1ns/1ns',
        '--single-unit', '-I', path.join(options.uvmRoot, 'src'), '--top', 'tb_top'
      ];
      const source = await runFrontend(options.moxVerilog, [
        ...common, '--uvm-path', options.uvmRoot, '-o', sourceOutput,
        path.join(lessonDir, 'tb_top.sv')
      ], options.timeoutMs, sourceLog);
      const artifact = await runFrontend(options.moxVerilog, [
        ...common, ...artifactFlags, '-o', artifactOutput,
        path.join(lessonDir, 'tb_top.sv')
      ], options.timeoutMs, artifactLog);
      rows.push({
        slug,
        source,
        artifact,
        sourceMlirBytes: await bytesOrZero(sourceOutput),
        artifactMlirBytes: await bytesOrZero(artifactOutput),
        artifactBytes
      });
      console.error(`${slug}: source=${formatStatus(source)} ${source.elapsedMs}ms; artifact=${formatStatus(artifact)} ${artifact.elapsedMs}ms`);
    }
    // Shared fleet binaries can be replaced while a matrix is running. A
    // mixed-identity run must never be mistaken for a qualified exact pair.
    const inputsUnchanged = frontendSha256 === await sha256(options.moxVerilog) &&
      artifactSha256 === await sha256(options.artifact);
    await writeFile(path.join(evidenceDir, 'receipt.json'), JSON.stringify({
      started, ended: new Date().toISOString(), options,
      frontendSha256, frontendVersion: version.output.trim(), artifactSha256,
      artifactBytes, inputsUnchanged,
      rows: rows.map((row) => ({
        ...row,
        source: { ...row.source, output: undefined },
        artifact: { ...row.artifact, output: undefined }
      }))
    }, null, 2) + '\n');
    const lines = [
      '# UVM package precompile receipt', '',
      `- Mox frontend: \`${options.moxVerilog}\``,
      `- Frontend SHA-256: \`${frontendSha256}\``,
      `- Frontend version: ${version.output.trim().replaceAll('\n', ' / ')}`,
      `- UVM source root: \`${options.uvmRoot}\``,
      `- Artifact: \`${options.artifact}\` (${artifactBytes} bytes; ${options.artifactMode} mode)`,
      `- Artifact SHA-256: \`${artifactSha256}\``,
      `- Inputs unchanged during matrix: ${inputsUnchanged ? 'yes' : 'NO — INVALID RECEIPT'}`,
      `- Diagnostics and invocation arguments: [receipt.json](${path.basename(evidenceDir)}/receipt.json)`,
      `- Timeout per invocation: ${options.timeoutMs} ms`, '',
      '| lesson | source ms | artifact ms | source result | artifact result | source MLIR bytes | artifact MLIR bytes | artifact bytes |',
      '| --- | ---: | ---: | --- | --- | ---: | ---: | ---: |'
    ];
    for (const row of rows) {
      lines.push(`| ${row.slug} | ${formatMs(row.source.elapsedMs)} | ${formatMs(row.artifact.elapsedMs)} | ${formatStatus(row.source)} | ${formatStatus(row.artifact)} | ${row.sourceMlirBytes} | ${row.artifactMlirBytes} | ${row.artifactBytes} |`);
    }
    lines.push('', '## Diagnostics', '');
    for (const row of rows) {
      for (const leg of ['source', 'artifact']) {
        const result = row[leg];
        lines.push(`- ${row.slug} ${leg}: [${formatStatus(result)}](${path.basename(evidenceDir)}/${result.log})`);
      }
    }
    await writeFile(options.output, `${lines.join('\n')}\n`);
    if (!inputsUnchanged) throw new Error('Frontend or artifact changed during matrix; receipt is invalid');
  } finally {
    await rm(tempRoot, { recursive: true, force: true });
  }
}

await main();
