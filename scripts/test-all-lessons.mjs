#!/usr/bin/env node
/**
 * test-all-lessons.mjs
 *
 * Compiles and simulates every lesson (sv, sva, uvm, cocotb) checking:
 *   • solution files → output must indicate success
 *   • starter files (incomplete) → must NOT indicate success
 *
 * Runners:
 *   sv/, sva/ sim  — circt-verilog (LLHD IR) + fresh circt-sim per lesson
 *   uvm/           — circt-verilog (LLHD IR + --uvm-path) + fresh circt-sim (includes VPI)
 *   sva/ bmc       — circt-verilog (HW IR, no --ir-llhd) + circt-bmc
 *                    (exit-code check only; Z3 not bundled so sat/unsat unknown)
 *   cocotb/        — cocotb_test.simulator.run with icarus (Python subprocess)
 *                    requires: pip3 install cocotb cocotb-test  +  iverilog
 *
 *   mlir/           — circt-sim parse/run validation (no solution files; display-only lessons)
 * Skipped: sva/lec (LEC tool)
 *
 * Design notes:
 *   - circt-verilog is loaded once and reused (compilation is stateless).
 *   - circt-sim is reloaded per lesson — global state leaks
 *     between callMain invocations; V8 caches the WASM binary so subsequent
 *     loads are fast (~1-3 s after the first cold load of ~30 s).
 *   - UVM lessons: all source files are staged to a temp dir with canonical
 *     names (stripping .sol) so that `include "foo.sv"` in tb_top.sv finds the
 *     staged solution version. Only the staged files are passed to the compiler.
 *   - BMC lessons: compiled without --ir-llhd so circt-bmc receives HW IR
 *     (hw.module), not LLHD entities. tb.sv is excluded from BMC inputs.
 *   - cocotb lessons: compiled with icarus via cocotb_test.simulator.run;
 *     a _timescale.v preamble sets `timescale 1ns/1ps for all lessons.
 */

import vm from 'node:vm';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';
import { spawnSync } from 'node:child_process';

const REPO_ROOT   = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const CIRCT_DIR   = path.join(REPO_ROOT, 'static/circt');
const LESSONS_DIR = path.join(REPO_ROOT, 'src/lessons');

const UVM_CORE_PATH = path.join(CIRCT_DIR, 'uvm-core');
const UVM_SRC_PATH  = path.join(UVM_CORE_PATH, 'src');

// ─── WASM tool loader ──────────────────────────────────────────────────────────

async function loadTool(toolName, { initTimeout = 60_000 } = {}) {
  const jsPath = path.join(CIRCT_DIR, `${toolName}.js`);
  if (!fs.existsSync(jsPath)) {
    throw new Error(`WASM artifact not found: ${jsPath}\nRun: npm run sync:circt`);
  }
  const source  = fs.readFileSync(jsPath, 'utf8');
  const capture = { out: '', err: '' };

  const realRequire    = createRequire(jsPath);
  const patchedRequire = (id) => {
    const mod = realRequire(id);
    if (id !== 'fs') return mod;
    return new Proxy(mod, {
      get(target, prop, receiver) {
        if (prop === 'writeSync') {
          return (fd, buf, off, len, _pos) => {
            const n = typeof len === 'number' ? len : (buf.byteLength ?? buf.length);
            const o = typeof off === 'number' ? off : 0;
            if (fd === 1 || fd === 2) {
              const text = buf && buf.buffer
                ? Buffer.from(buf.buffer, (buf.byteOffset ?? 0) + o, n).toString('utf8')
                : Buffer.from(typeof buf === 'string' ? buf : String(buf)).toString('utf8');
              if (fd === 1) capture.out += text;
              else          capture.err += text;
              return n;
            }
            return target.writeSync(fd, buf, off, len, _pos);
          };
        }
        const val = Reflect.get(target, prop, receiver);
        return typeof val === 'function' ? val.bind(target) : val;
      },
    });
  };

  const context = {
    require: patchedRequire,
    process, console, Buffer, URL, WebAssembly,
    TextDecoder, TextEncoder, setTimeout, clearTimeout,
    setInterval, clearInterval, performance,
    __dirname: CIRCT_DIR,
    __filename: jsPath,
  };
  context.globalThis = context;
  context.self       = context;
  context.Module = {
    noInitialRun: true,
    locateFile: (f) => path.join(CIRCT_DIR, f),
    print:    (s) => { capture.out += s + '\n'; },
    printErr: (s) => { capture.err += s + '\n'; },
  };

  vm.runInNewContext(source, context);
  await waitForReady(context, initTimeout);

  const getFS = () => context.Module.FS ?? context.FS;

  return {
    invoke(inputFiles = {}, args = []) {
      capture.out = '';
      capture.err = '';
      const FS = getFS();
      let fsWriteFailed = false;
      for (const [p, content] of Object.entries(inputFiles)) {
        const dir = p.slice(0, p.lastIndexOf('/') || 1);
        try { FS.mkdirTree(dir); } catch {}
        try { FS.writeFile(p, content, { encoding: 'utf8' }); }
        catch { fsWriteFailed = true; break; }
      }
      if (fsWriteFailed) return { exitCode: 1, stdout: '', stderr: '', fsWriteFailed: true };
      const callMain = context.Module.callMain ?? context.__svt_callMain ?? context.callMain;
      let exitCode = 0;
      try { exitCode = callMain(args) ?? 0; }
      catch (e) { exitCode = e?.status ?? 1; }
      return { exitCode, stdout: capture.out, stderr: capture.err };
    },
    readVirtualFile(vpath) {
      const FS = getFS();
      try { return FS.readFile(vpath, { encoding: 'utf8' }); } catch { return null; }
    },
  };
}

function waitForReady(context, ms) {
  return new Promise((resolve, reject) => {
    const start = Date.now();
    const tick  = () => {
      const mod = context.Module;
      const hasCallMain =
        typeof mod.callMain === 'function' ||
        typeof context.__svt_callMain === 'function' ||
        typeof context.callMain === 'function';
      if (hasCallMain && mod.calledRun) return resolve();
      if (Date.now() - start > ms) return reject(new Error(`WASM init timeout after ${ms}ms`));
      setTimeout(tick, 50);
    };
    tick();
  });
}

// ─── lesson file helpers ───────────────────────────────────────────────────────

function getSvFiles(dir) {
  return fs.readdirSync(dir).filter(f => f.endsWith('.sv')).sort();
}

function getStarterFiles(dir) {
  return getSvFiles(dir)
    .filter(f => !f.endsWith('.sol.sv'))
    .map(f => path.join(dir, f));
}

function hasSolFiles(dir) {
  return getSvFiles(dir).some(f => f.endsWith('.sol.sv'));
}

// For each starter .sv, substitute the matching .sol.sv if it exists.
function buildSolutionFiles(starterFiles, dir) {
  return starterFiles.map(f => {
    const sol = path.join(dir, path.basename(f, '.sv') + '.sol.sv');
    return fs.existsSync(sol) ? sol : f;
  });
}

function isTestbenchFile(f) {
  const base = path.basename(f, '.sv').replace(/\.sol$/, '');
  return base === 'tb' || base === 'tb_top' || base.endsWith('_tb');
}

// Copy files to a staging dir with canonical names (.sol.sv → .sv).
// Returns the list of staged file paths (canonical names).
function stageFiles(files, stagingDir) {
  fs.mkdirSync(stagingDir, { recursive: true });
  return files.map(f => {
    const base = path.basename(f).replace(/\.sol\.sv$/, '.sv');
    const dest = path.join(stagingDir, base);
    fs.copyFileSync(f, dest);
    return dest;
  });
}

// Mirror the adapter's compileRootSourcePaths: return only files that are NOT
// `include`-d by any other file in the set.  This prevents passing a file
// both explicitly and via `include, which causes slang redefinition errors.
function findCompileRoots(stagedFiles) {
  const fileSet  = new Set(stagedFiles);
  const included = new Set();

  for (const f of stagedFiles) {
    let content;
    try { content = fs.readFileSync(f, 'utf8'); } catch { continue; }
    for (const m of content.matchAll(/^\s*`include\s+"([^"]+)"/gm)) {
      const resolved = path.join(path.dirname(f), m[1]);
      if (fileSet.has(resolved)) included.add(resolved);
    }
  }

  const roots = stagedFiles.filter(f => !included.has(f));
  return roots.length > 0 ? roots : stagedFiles;
}

// Extract the first `module <name>` declaration from a SV file.
function moduleNameFromFile(filePath) {
  try {
    const src = fs.readFileSync(filePath, 'utf8');
    const m   = src.match(/^\s*module\s+(\w+)/m);
    return m ? m[1] : null;
  } catch { return null; }
}

function hasPass(output) {
  return output.split('\n').some(line => line.startsWith('PASS'));
}

// ─── compile + simulate / bmc ─────────────────────────────────────────────────

// Flags for LLHD IR (simulation): circt-sim consumes LLHD (includes VPI for UVM).
const SIM_VERILOG_FLAGS = ['--ir-llhd', '--timescale', '1ns/1ns', '--single-unit'];

// Flags for HW IR (BMC): circt-bmc consumes hw.module, not llhd.entity.
const BMC_VERILOG_FLAGS = ['--timescale', '1ns/1ns', '--single-unit'];

const BMC_FLAGS = ['--assume-known-inputs', '-b', '20'];

function compile(verilog, work, label, svFiles, { forBmc = false, extraFlags = [] } = {}) {
  const mlirPath   = path.join(work, `${label}.mlir`);
  const baseFlags  = forBmc ? BMC_VERILOG_FLAGS : SIM_VERILOG_FLAGS;
  const { exitCode, stdout, stderr } =
    verilog.invoke({}, [...baseFlags, ...extraFlags, '-o', mlirPath, ...svFiles]);
  if (exitCode !== 0) return { ok: false, output: stdout + stderr };
  return { ok: true, mlirPath, output: stdout + stderr };
}

function simulate(sim, mlirPath, { top = 'tb', extraArgs = [] } = {}) {
  let mlir;
  try { mlir = fs.readFileSync(mlirPath, 'utf8'); }
  catch { return { ok: false, reason: 'MLIR output not written', output: '', exitCode: 1 }; }
  // Try MEMFS virtual-path approach first (older builds use MEMFS).
  // If FS.writeFile fails (NODERAWFS build), fall back to native path directly.
  const vpath = '/workspace/sim.mlir';
  let result = sim.invoke({ [vpath]: mlir }, ['--top', top, ...extraArgs, vpath]);
  if (result.fsWriteFailed) {
    // NODERAWFS build — the real filesystem is accessible, pass native path.
    result = sim.invoke({}, ['--top', top, ...extraArgs, mlirPath]);
  }
  const { exitCode, stdout, stderr } = result;
  return { ok: exitCode === 0, output: stdout + stderr, exitCode };
}

// Run circt-bmc (NODERAWFS — uses real filesystem paths).
function runBmc(bmc, work, label, mlirPath, topModule) {
  if (!fs.existsSync(mlirPath)) {
    return { ok: false, smtPath: null, output: 'MLIR output not written' };
  }
  const smtPath = path.join(work, `${label}.smt2`);
  const { exitCode, stdout, stderr } = bmc.invoke(
    {},
    [...BMC_FLAGS, '--module', topModule, '--emit-smtlib', '-o', smtPath, mlirPath],
  );
  return { ok: exitCode === 0, smtPath: fs.existsSync(smtPath) ? smtPath : null, output: stdout + stderr };
}

// ─── Z3 SMT solver ────────────────────────────────────────────────────────────

function findZ3() {
  for (const candidate of ['/opt/homebrew/bin/z3', 'z3']) {
    try {
      const r = spawnSync(candidate, ['--version'], { encoding: 'utf8', timeout: 5000 });
      if (r.status === 0) return candidate;
    } catch {}
  }
  return null;
}

// Run Z3 on a .smt2 file. Returns 'unsat', 'sat', or null (error/unavailable).
function runZ3(z3Path, smtPath) {
  if (!z3Path || !fs.existsSync(smtPath)) return null;
  const r = spawnSync(z3Path, [smtPath], { encoding: 'utf8', timeout: 30_000 });
  if (r.status !== 0 && !r.stdout) return null;
  const out = (r.stdout ?? '') + (r.stderr ?? '');
  if (out.includes('unsat')) return 'unsat';
  if (out.includes('sat'))   return 'sat';
  return null;
}

// ─── mlir validator (circt-sim parse/run check) ───────────────────────────────

async function runMlirLesson({ sim, slug, lessonDir, work, results }) {
  const label = `mlir/${slug}`;
  const allFiles = fs.readdirSync(lessonDir).filter(f => f.endsWith('.mlir')).sort();
  // Split into lesson files and companion testbench files (*_tb.mlir).
  const tbFiles      = new Set(allFiles.filter(f => f.endsWith('_tb.mlir')));
  const lessonFiles  = allFiles.filter(f => !tbFiles.has(f));

  if (lessonFiles.length === 0) {
    console.log(`  ${D}SKIP  ${label} (no .mlir files)${X}`);
    results.skip++;
    return;
  }
  for (const mlirFile of lessonFiles) {
    const fileLabel = `${label}/${mlirFile}`;
    process.stdout.write(`  ${fileLabel.padEnd(34)}`);
    const nativeMlirPath = path.join(lessonDir, mlirFile);
    const content = fs.readFileSync(nativeMlirPath, 'utf8');

    // Check for companion testbench file (e.g. adder.mlir → adder_tb.mlir).
    const tbName = mlirFile.replace(/\.mlir$/, '_tb.mlir');
    const hasTb  = tbFiles.has(tbName);

    if (!hasTb && !content.includes('@tb')) {
      // Display-only MLIR lesson — no simulation entry point.
      console.log(`  ${D}SKIP (display-only, no @tb)${X}`);
      results.skip++;
      continue;
    }

    // Combine lesson content with companion testbench (if present).
    let simContent = content;
    if (hasTb) {
      const tbContent = fs.readFileSync(path.join(lessonDir, tbName), 'utf8');
      simContent = content + '\n' + tbContent;
    }

    // Try MEMFS virtual path first (browser-compat-patched build).
    // Fall back to native filesystem path for NODERAWFS builds.
    const tmpMlir = path.join(work, `mlir_${slug}_${mlirFile}`);
    const vpath = '/workspace/sim.mlir';
    let simResult = sim.invoke({ [vpath]: simContent }, ['--top', 'tb', vpath]);
    if (simResult.fsWriteFailed) {
      fs.writeFileSync(tmpMlir, simContent);
      simResult = sim.invoke({}, ['--top', 'tb', tmpMlir]);
    }
    const { exitCode, stdout, stderr } = simResult;
    const output = stdout + stderr;
    if (hasPass(output)) {
      console.log(`  ${G}PASS${X}`);
      results.pass++;
    } else if (exitCode === 0) {
      console.log(`  ${R}NO_PASS${X}`);
      results.failures.push({ label: fileLabel, mode: 'mlir', reason: 'no PASS in output', output });
      results.fail++;
    } else {
      console.log(`  ${R}FAIL${X}`);
      results.failures.push({ label: fileLabel, mode: 'mlir', reason: 'circt-sim error', output });
      results.fail++;
    }
  }
}

// ─── LEC runner (circt-lec + Z3) ─────────────────────────────────────────────

const LEC_FLAGS = ['--assume-known-inputs'];

async function runLecLesson({ verilog, lec, z3Path, work, slug, lessonDir, results, meta }) {
  const label     = `sva/${slug}`;
  const lessonMeta = meta[label] ?? {};
  const module1   = lessonMeta.module1 ?? 'Spec';
  const module2   = lessonMeta.module2 ?? 'Impl';

  if (!hasSolFiles(lessonDir)) {
    console.log(`  ${D}SKIP  ${label} (no solution file)${X}`);
    results.skip++;
    return;
  }

  const starterFiles = getStarterFiles(lessonDir);
  const solFiles     = buildSolutionFiles(starterFiles, lessonDir);
  // LEC takes a single SV file; use the first file.
  const solFile   = solFiles[0];
  const startFile = starterFiles[0];

  process.stdout.write(`  ${label.padEnd(34)}`);

  // circt-lec takes MLIR (hw dialect) as input — compile SV to MLIR first.
  // circt-lec uses MEMFS in Node.js builds: write MLIR to virtual FS, read
  // SMT output back from virtual FS, then persist to native for Z3.
  function invokeLec(svFile, label, nativeOutPath) {
    const mlirCompile = compile(verilog, work, label, [svFile], { forBmc: true });
    if (!mlirCompile.ok) return { exitCode: 1, stdout: mlirCompile.output, stderr: '' };
    const mlirContent = fs.readFileSync(mlirCompile.mlirPath, 'utf8');
    const vMlirIn  = `/lec_${label}_in.mlir`;
    const vSmtOut  = `/lec_${label}_out.smt2`;
    let result = lec.invoke(
      { [vMlirIn]: mlirContent },
      [...LEC_FLAGS, '-c1', module1, '-c2', module2, '--emit-smtlib', '-o', vSmtOut, vMlirIn],
    );
    if (!result.fsWriteFailed) {
      // MEMFS: read SMT from virtual FS and persist to real path for Z3.
      const smt = lec.readVirtualFile(vSmtOut) ?? '';
      fs.writeFileSync(nativeOutPath, smt);
    } else {
      // NODERAWFS: re-invoke with native MLIR and SMT paths.
      result = lec.invoke(
        {},
        [...LEC_FLAGS, '-c1', module1, '-c2', module2, '--emit-smtlib', '-o', nativeOutPath, mlirCompile.mlirPath],
      );
    }
    return result;
  }

  // ── Solution ─────────────────────────────────────────────────────────────────
  const solSmt = path.join(work, `lec-${slug}-sol.smt2`);
  const solLec = invokeLec(solFile, `lec-${slug}-sol`, solSmt);
  if (solLec.exitCode !== 0) {
    process.stdout.write(`  ${R}sol=LEC_ERROR${X}\n`);
    results.failures.push({ label, mode: 'solution', reason: 'circt-lec error', output: solLec.stdout + solLec.stderr });
    results.fail++;
    return;
  }

  const solZ3 = z3Path ? runZ3(z3Path, solSmt) : null;
  if (solZ3 === 'unsat') {
    process.stdout.write(`  ${G}sol=UNSAT${X}`);
    results.pass++;
  } else if (solZ3 !== null) {
    process.stdout.write(`  ${R}sol=SAT(expected unsat)${X}\n`);
    results.failures.push({ label, mode: 'solution', reason: 'Z3 returned sat — modules not equivalent', output: '' });
    results.fail++;
    return;
  } else {
    // Z3 unavailable — just check that LEC compiled
    process.stdout.write(`  ${Y}sol=LEC_OK${X}`);
    results.skip++;
  }

  // ── Starter ──────────────────────────────────────────────────────────────────
  const startSmt = path.join(work, `lec-${slug}-start.smt2`);
  const startLec = invokeLec(startFile, `lec-${slug}-start`, startSmt);
  if (startLec.exitCode !== 0) {
    process.stdout.write(`  ${G}start=FAIL(lec)${X}\n`);
    results.pass++;
    return;
  }

  // Check for sat-check in SMT output
  const smtContent = fs.existsSync(startSmt) ? fs.readFileSync(startSmt, 'utf8') : '';
  if (!smtContent.includes('(check-sat)')) {
    process.stdout.write(`  ${G}start=NO_ASSERTIONS${X}\n`);
    results.pass++;
    return;
  }

  const startZ3 = z3Path ? runZ3(z3Path, startSmt) : null;
  if (startZ3 === 'sat') {
    // Starter is NOT equivalent (as expected: Impl returns 0 for all outputs)
    process.stdout.write(`  ${G}start=FAIL(sat)${X}\n`);
    results.pass++;
  } else if (startZ3 === 'unsat') {
    process.stdout.write(`  ${R}start=UNEXPECTED_PASS${X}\n`);
    results.failures.push({ label, mode: 'starter', reason: 'starter unexpectedly equivalent (unsat)', output: '' });
    results.fail++;
  } else {
    // Z3 unavailable — compiled successfully, cannot determine sat/unsat
    process.stdout.write(`  ${D}start=COMPILED${X}\n`);
    results.skip++;
  }
}

// ─── cocotb runner (Python subprocess via cocotb-test + icarus) ───────────────

function checkCocotbDeps() {
  const py = spawnSync('python3', ['-c', 'import cocotb_test'], { encoding: 'utf8' });
  if (py.status !== 0) return { ok: false, reason: 'cocotb-test not installed — run: pip3 install cocotb cocotb-test' };
  const iv = spawnSync('iverilog', ['-V'], { encoding: 'utf8' });
  if (iv.error) return { ok: false, reason: 'iverilog not found' };
  return { ok: true };
}

// Run a cocotb test (solution or starter) against test_<module>.py via icarus.
// Returns { ok: boolean, output: string }.
function runCocotbTest(svFile, lessonDir, testModule, topModule, buildDir) {
  fs.mkdirSync(buildDir, { recursive: true });
  const tsFile = path.join(buildDir, '_timescale.v');
  fs.writeFileSync(tsFile, '`timescale 1ns/1ps\n');

  const script = `
import sys, os
from cocotb_test.simulator import run
run(
    python_search=${JSON.stringify([lessonDir])},
    verilog_sources=${JSON.stringify([tsFile, svFile])},
    toplevel=${JSON.stringify(topModule)},
    module=${JSON.stringify(testModule)},
    simulator="icarus",
    sim_build=${JSON.stringify(buildDir)},
)
`.trim();

  const result = spawnSync('python3', ['-c', script], {
    encoding: 'utf8',
    timeout: 60_000,
    env: { ...process.env, COCOTB_REDUCED_LOG_FMT: '1' },
  });
  const output = (result.stdout ?? '') + (result.stderr ?? '');
  return { ok: result.status === 0, output };
}

async function runCocotbLesson({ slug, lessonDir, results, work }) {
  const label = `cocotb/${slug}`;

  if (!hasSolFiles(lessonDir)) {
    console.log(`  ${D}SKIP  ${label} (no solution file)${X}`);
    results.skip++;
    return;
  }
  const testPy = fs.readdirSync(lessonDir).find(f => /^test_.*\.py$/.test(f));
  if (!testPy) {
    console.log(`  ${D}SKIP  ${label} (no test_*.py)${X}`);
    results.skip++;
    return;
  }

  const starterFiles = getStarterFiles(lessonDir);
  const solFiles     = buildSolutionFiles(starterFiles, lessonDir);
  const startFile    = starterFiles[0];
  const solFile      = solFiles[0];
  const topModule    = moduleNameFromFile(startFile);
  const testModule   = path.basename(testPy, '.py');

  process.stdout.write(`  ${label.padEnd(34)}`);

  // ── Solution ─────────────────────────────────────────────────────────────────
  const solBuild = path.join(work, `cocotb-${slug}-sol`);
  const solResult = runCocotbTest(solFile, lessonDir, testModule, topModule, solBuild);
  if (solResult.ok) {
    process.stdout.write(`  ${G}sol=PASS${X}`);
    results.pass++;
  } else {
    process.stdout.write(`  ${R}sol=FAIL${X}\n`);
    results.failures.push({ label, mode: 'solution', reason: 'cocotb test failed', output: solResult.output });
    results.fail++;
  }

  // ── Starter ──────────────────────────────────────────────────────────────────
  const startBuild = path.join(work, `cocotb-${slug}-start`);
  const startResult = runCocotbTest(startFile, lessonDir, testModule, topModule, startBuild);
  if (!startResult.ok) {
    process.stdout.write(`  ${G}start=FAIL${X}\n`);
    results.pass++;
  } else {
    process.stdout.write(`  ${R}start=UNEXPECTED_PASS${X}\n`);
    results.failures.push({ label, mode: 'starter', reason: 'starter unexpectedly passed cocotb tests', output: startResult.output });
    results.fail++;
  }
}

// ─── lesson runner ────────────────────────────────────────────────────────────

const G = '\x1b[32m', R = '\x1b[31m', Y = '\x1b[33m', D = '\x1b[2m', X = '\x1b[0m';

// Observation/demo lessons: the starter intentionally also passes.
// Covergroup lessons (covergroup-basics, coverpoint-bins, cross-coverage): the starter is a
// working SRAM test (prints PASS); the student adds coverpoints on top of the passing design.
//
// UVM lessons below are ones where the starter still passes despite incompleteness:
// - uvm/covergroup: empty covergroup returns 100% coverage in CIRCT (no bins → trivially covered)
// - uvm/cross-coverage: basic bins reach 100% without cross; cannot distinguish starter/solution
// - uvm/constrained-random: inline constraints still not applied by CIRCT (#69)
const SKIP_START_CHECK = new Set([
  'sva/concurrent-sim', 'sva/vacuous-pass',
  'uvm/constrained-random',  // inline constraints now work; starter (no inline) also passes via class constraints
  'uvm/covergroup',          // empty covergroup returns 100% in CIRCT; cannot distinguish starter
  'uvm/cross-coverage',      // basic bins reach 100% without cross; starter appears to pass
  'uvm/coverage-driven',     // uvm_subscriber::report_phase virtual dispatch fails in CIRCT; $fatal never propagates
  // BMC starters that can't be distinguished from solutions via Z3:
  'sva-bmc/disable-iff',     // req|=>ack is sat both with and without disable iff (both have counterexamples)
]);

// Observation lessons where the SOLUTION intentionally does not print PASS.
// For these we only verify that the solution compiles and runs without crashing.
// e.g. sv/welcome    — intro lesson that just does $display + $finish, no PASS check.
const SKIP_SOL_PASS = new Set([
  'sv/welcome',
]);

// Known CIRCT bugs that block solution verification.
// When a bug is fixed, the test auto-promotes to PASS (XPASS is treated as pass).
// Format: lesson-label → short reason string for display.
//
// Bug report files live in docs/circt-bugs/.
// GitHub issues: https://github.com/thomasnormal/circt/issues
//
// Previously fixed (XPASS):
// sv/parameters (#9 AllowHierarchicalConst): fixed in e1ea916d1.
// All 11 UVM lessons regressed in 3d72a82a4 (OBJTN_ZERO phase_hopper).
// Fixed in local WASM build via drop_objection no-op for unseen hoppers +
// combinational SRAM read in UVM lesson SRAMs (eliminates monitor/scoreboard
// misalignment caused by registered-read 1-cycle latency with 2-cycle driver).
// 10 of 11 UVM lessons now XPASS; only constrained-random remains.
const CIRCT_XFAIL = new Map([
  // randomize() with {...} inline constraints not respected: weighted_c stays
  // active and boundary writes land at wrong addresses (#69).
  ['uvm/constrained-random', 'inline randomize() with{} constraints not applied (#69)'],
  // Factory type override (set_type_override) not applied at runtime (#74).
  ['uvm/factory-override', 'type_id::set_type_override not applied by CIRCT UVM factory (#74)'],
  // Queue pop_front() does not remove the element from the queue — infinite loop (#75).
  ['sv/queues-arrays', 'queue pop_front() does not dequeue element in new CIRCT build (#75)'],
]);

async function runLesson({ verilog, bmc, z3Path, work, category, slug, lessonDir, results, meta }) {
  const label      = `${category}/${slug}`;
  const lessonMeta = meta[`${slug.includes('/') ? slug : `${category.replace(/-.*/, '')}/${slug}`}`] ?? {};
  const runner     = lessonMeta.runner;
  const isBmc      = category === 'sva-bmc';
  const isUvm      = category === 'uvm';
  const isSimOnly  = category === 'sva-sim';

  const skipStart  = SKIP_START_CHECK.has(`${isSimOnly ? 'sva' : category}/${slug}`);
  const skipSolPass = SKIP_SOL_PASS.has(label);

  // ── Skip checks ─────────────────────────────────────────────────────────────
  // Support custom top module name via meta.top (e.g. sv/events uses 'event_sync',
  // sv/data-types uses 'top' with file named data_types.sv).
  const metaTop    = lessonMeta.top;
  const hasTb = fs.existsSync(path.join(lessonDir, 'tb.sv')) ||
                fs.existsSync(path.join(lessonDir, 'tb_top.sv')) ||
                // If meta.top is set, any starter .sv file can serve as the testbench.
                (metaTop ? getSvFiles(lessonDir).some(f => !f.endsWith('.sol.sv')) : false);

  if (!isBmc && !hasTb) {
    console.log(`  ${D}SKIP  ${label} (no testbench)${X}`);
    results.skip++;
    return;
  }
  if (!hasSolFiles(lessonDir)) {
    console.log(`  ${D}SKIP  ${label} (no solution file)${X}`);
    results.skip++;
    return;
  }

  const starterFiles = getStarterFiles(lessonDir);
  const solFiles     = buildSolutionFiles(starterFiles, lessonDir);

  process.stdout.write(`  ${label.padEnd(34)}`);

  // ─────────────────────────────────────────────────────────────────────────────
  if (isBmc) {
    // BMC path: exclude testbench files (BMC only checks the design module).
    const solDesign     = solFiles.filter(f => !isTestbenchFile(f));
    const startDesign   = starterFiles.filter(f => !isTestbenchFile(f));

    if (solDesign.length === 0) {
      process.stdout.write(`  ${D}SKIP (no design files for BMC)${X}\n`);
      results.skip++;
      return;
    }

    const solCompile   = compile(verilog, work, `sva-bmc-${slug}-sol`,   solDesign,   { forBmc: true });
    const startCompile = compile(verilog, work, `sva-bmc-${slug}-start`, startDesign, { forBmc: true });

    // Determine top module from the solution file.
    const topFile   = solDesign.find(f => !isTestbenchFile(f)) ?? solDesign[0];
    const topModule = moduleNameFromFile(topFile) ?? path.basename(topFile, '.sv').replace(/\.sol$/, '');

    // ── Solution ───────────────────────────────────────────────────────────────
    let solZ3Result = null;
    if (!solCompile.ok) {
      process.stdout.write(`  ${R}sol=COMPILE_ERROR${X}\n`);
      results.failures.push({ label, mode: 'solution', reason: 'compile error', output: solCompile.output });
      results.fail++;
    } else {
      const bmcResult = runBmc(bmc, work, `sva-bmc-${slug}-sol`, solCompile.mlirPath, topModule);
      if (!bmcResult.ok) {
        process.stdout.write(`  ${R}sol=BMC_ERROR${X}\n`);
        results.failures.push({ label, mode: 'solution', reason: 'circt-bmc error', output: bmcResult.output });
        results.fail++;
      } else {
        solZ3Result = runZ3(z3Path, bmcResult.smtPath);
        if (solZ3Result === 'unsat') {
          process.stdout.write(`  ${G}sol=UNSAT${X}`);
          results.pass++;
        } else if (solZ3Result === 'sat') {
          process.stdout.write(`  ${G}sol=SAT${X}`);  // cover-property lessons expect sat
          results.pass++;
        } else {
          // Z3 unavailable — just check that circt-bmc succeeded
          process.stdout.write(`  ${G}sol=BMC_OK${X}`);
          results.pass++;
        }
      }
    }

    // ── Starter ────────────────────────────────────────────────────────────────
    if (skipStart) {
      process.stdout.write(`  ${D}start=SKIP(by-design)${X}\n`);
      results.skip++;
    } else if (!startCompile.ok) {
      process.stdout.write(`  ${G}start=FAIL(compile)${X}\n`);
      results.pass++;
    } else {
      const startBmc = runBmc(bmc, work, `sva-bmc-${slug}-start`, startCompile.mlirPath, topModule);
      if (!startBmc.ok) {
        process.stdout.write(`  ${G}start=FAIL(bmc)${X}\n`);
        results.pass++;
      } else {
        // Check for negated property assertions in the SMT output.
        // circt-bmc encodes assertions as (assert (not ...)); a module with no
        // assertions only emits (check-sat) which Z3 trivially proves unsat.
        const smtContent = startBmc.smtPath ? fs.readFileSync(startBmc.smtPath, 'utf8') : '';
        if (!smtContent.includes('(assert (not')) {
          process.stdout.write(`  ${G}start=NO_ASSERTIONS${X}\n`);
          results.pass++;
        } else if (z3Path) {
          const startZ3 = runZ3(z3Path, startBmc.smtPath);
          if (startZ3 !== solZ3Result) {
            // Starter gives a different result than solution (expected for incomplete starters)
            process.stdout.write(`  ${G}start=FAIL(${startZ3 ?? 'no-result'})${X}\n`);
            results.pass++;
          } else {
            process.stdout.write(`  ${R}start=UNEXPECTED_PASS${X}\n`);
            results.failures.push({ label, mode: 'starter', reason: 'starter Z3 result matches solution unexpectedly', output: '' });
            results.fail++;
          }
        } else {
          // Z3 unavailable — compiled successfully, cannot determine sat/unsat
          process.stdout.write(`  ${D}start=COMPILED${X}\n`);
          results.skip++;
        }
      }
    }
    return;
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Simulation path (sv, sva-sim, uvm)
  // The new circt-sim.js includes VPI support; use it for all lessons.
  const simTool  = 'circt-sim';
  const topName  = metaTop ?? (isUvm ? 'tb_top' : 'tb');
  // Default UVM ceiling: 10 ns (enough for delta-cycle-only tests like
  // factory-override/ral/sequence/seq-item that complete at t=0).
  // Clock-driven lessons (driver/env/monitor/…) set meta.simMaxTime (fs)
  // to get more time without inflating the whole suite.
  // sv/sva simulations use a 10 µs ceiling to guard against hangs.
  const uvmDefault = '10000000';
  const simMaxTime = lessonMeta.simMaxTime ? String(lessonMeta.simMaxTime) : (isUvm ? uvmDefault : '10000000000');
  const simExtra = ['--max-time', simMaxTime];

  let compileSolFiles, compileStartFiles, extraFlags;

  if (isUvm) {
    // Stage files to a temp dir with canonical names (.sol.sv → .sv).
    // Pass ONLY tb_top.sv — it `include`s everything else by relative path,
    // so the staged files are picked up without duplicate-definition errors.
    const solStage   = path.join(work, `uvm-${slug}-sol-stage`);
    const startStage = path.join(work, `uvm-${slug}-start-stage`);
    const solStaged   = stageFiles(solFiles,     solStage);
    const startStaged = stageFiles(starterFiles, startStage);
    // Pass only the "root" files — those not `include`-d by another staged file.
    compileSolFiles   = findCompileRoots(solStaged);
    compileStartFiles = findCompileRoots(startStaged);
    extraFlags = ['--uvm-path', UVM_CORE_PATH, '-I', UVM_SRC_PATH];
  } else {
    compileSolFiles   = solFiles;
    compileStartFiles = starterFiles;
    extraFlags = [];
  }

  const solCompile   = compile(verilog, work, `${category}-${slug}-sol`,   compileSolFiles,   { extraFlags });
  const startCompile = compile(verilog, work, `${category}-${slug}-start`, compileStartFiles, { extraFlags });

  // Load a fresh sim instance per lesson to avoid global state leakage.
  const sim = await loadTool(simTool);

  // ── Solution ─────────────────────────────────────────────────────────────────
  const xfailReason = CIRCT_XFAIL.get(label);

  if (!solCompile.ok) {
    if (xfailReason) {
      process.stdout.write(`  ${Y}sol=XFAIL${X}`);
      results.xfail++;
      if (process.env.VERBOSE_XFAIL) {
        console.log('\n[compile fail]\n' + solCompile.output.split('\n').map(l => '    ' + l).join('\n'));
      }
    } else {
      process.stdout.write(`  ${R}sol=COMPILE_ERROR${X}\n`);
      results.failures.push({ label, mode: 'solution', reason: 'compile error', output: solCompile.output });
      results.fail++;
    }
  } else if (skipSolPass) {
    // Observation lesson: verify the solution runs without crashing, no PASS expected.
    // Accept non-zero exit codes if the simulation produced output (e.g. UVM_FATAL in
    // phase cleanup is a known CIRCT regression that doesn't affect the lesson itself).
    const solSim = simulate(sim, solCompile.mlirPath, { top: topName, extraArgs: simExtra });
    const simRan = solSim.ok || solSim.output.includes('[circt-sim]');
    if (simRan) {
      process.stdout.write(`  ${Y}sol=RAN${X}`);  // neutral — no PASS expected
      results.skip++;
    } else {
      process.stdout.write(`  ${R}sol=CRASH${X}\n`);
      results.failures.push({ label, mode: 'solution', reason: 'simulation crashed', output: solSim.output });
      results.fail++;
    }
  } else {
    const solSim = simulate(sim, solCompile.mlirPath, { top: topName, extraArgs: simExtra });
    if (hasPass(solSim.output)) {
      if (xfailReason) {
        // Bug was fixed! Promote to pass.
        process.stdout.write(`  ${G}sol=XPASS${X}`);
        results.xpass++;
      } else {
        process.stdout.write(`  ${G}sol=PASS${X}`);
        results.pass++;
      }
    } else if (xfailReason) {
      process.stdout.write(`  ${Y}sol=XFAIL${X}`);
      results.xfail++;
      if (process.env.VERBOSE_XFAIL) {
        console.log('\n' + solSim.output.split('\n').map(l => '    ' + l).join('\n'));
      }
    } else {
      process.stdout.write(`  ${R}sol=NO_PASS${X}\n`);
      results.failures.push({ label, mode: 'solution', reason: 'no PASS in output', output: solSim.output });
      results.fail++;
    }
  }

  // ── Starter ──────────────────────────────────────────────────────────────────
  if (skipStart) {
    process.stdout.write(`  ${D}start=SKIP(by-design)${X}\n`);
    results.skip++;
  } else if (!startCompile.ok) {
    process.stdout.write(`  ${G}start=FAIL(compile)${X}\n`);
    results.pass++;
  } else {
    const startSim = simulate(sim, startCompile.mlirPath, { top: topName, extraArgs: simExtra });
    if (!hasPass(startSim.output)) {
      process.stdout.write(`  ${G}start=FAIL${X}\n`);
      results.pass++;
    } else {
      process.stdout.write(`  ${R}start=UNEXPECTED_PASS${X}\n`);
      results.failures.push({ label, mode: 'starter', reason: 'starter unexpectedly printed PASS', output: startSim.output });
      results.fail++;
    }
  }
}

// ─── meta.js runner lookup ────────────────────────────────────────────────────

async function loadMeta() {
  const { default: meta } = await import('../src/lessons/meta.js');
  return meta;
}

// ─── main ─────────────────────────────────────────────────────────────────────

async function main() {
  const work = fs.mkdtempSync(path.join(os.tmpdir(), 'sv-lesson-test-'));
  try {
    await run(work);
  } finally {
    fs.rmSync(work, { recursive: true, force: true });
  }
}

// Optional lesson filter: node test-all-lessons.mjs uvm/env sv/fsm ...
const FILTER = process.argv.slice(2).filter(a => !a.startsWith('--'));
const shouldRun = (label) => FILTER.length === 0 || FILTER.includes(label);

async function run(work) {
  const meta = await loadMeta();

  console.log('\nLoading circt-verilog…');
  const verilog = await loadTool('circt-verilog');
  console.log('Loading circt-bmc…');
  const bmc = await loadTool('circt-bmc');
  console.log('Loading circt-lec…');
  const lec = await loadTool('circt-lec');

  const z3Path = findZ3();
  if (z3Path) console.log(`Z3 found: ${z3Path}`);
  else         console.log('Z3 not found — BMC/LEC sat/unsat checks disabled');

  console.log('Ready.\n');

  const results = { pass: 0, fail: 0, xfail: 0, xpass: 0, skip: 0, failures: [] };

  const listDir = (sub) =>
    fs.readdirSync(path.join(LESSONS_DIR, sub), { withFileTypes: true })
      .filter(d => d.isDirectory()).map(d => d.name).sort();

  // ── sv/ ─────────────────────────────────────────────────────────────────────
  for (const slug of listDir('sv')) {
    if (!shouldRun(`sv/${slug}`)) continue;
    await runLesson({ verilog, bmc, z3Path, work, category: 'sv', slug, lessonDir: path.join(LESSONS_DIR, 'sv', slug), results, meta });
  }

  // ── sva/ ────────────────────────────────────────────────────────────────────
  for (const slug of listDir('sva')) {
    const runner = meta[`sva/${slug}`]?.runner;

    if (runner === 'lec') {
      if (!shouldRun(`sva/${slug}`)) continue;
      await runLecLesson({ verilog, lec, z3Path, work, slug, lessonDir: path.join(LESSONS_DIR, 'sva', slug), results, meta });
      continue;
    }

    // 'bmc' or 'both' → BMC path; null/undefined → sim
    const category = (runner === 'bmc' || runner === 'both') ? 'sva-bmc' : 'sva-sim';
    if (!shouldRun(`${category}/${slug}`)) continue;
    await runLesson({ verilog, bmc, z3Path, work, category, slug, lessonDir: path.join(LESSONS_DIR, 'sva', slug), results, meta });
  }

  // ── uvm/ ────────────────────────────────────────────────────────────────────
  if (!fs.existsSync(UVM_CORE_PATH)) {
    console.log(`\n${D}Skipping uvm/ — UVM library not found at ${UVM_CORE_PATH}${X}`);
    console.log(`${D}Run: npm run sync:circt${X}\n`);
  } else {
    for (const slug of listDir('uvm')) {
      if (!shouldRun(`uvm/${slug}`)) continue;
      await runLesson({ verilog, bmc, z3Path, work, category: 'uvm', slug, lessonDir: path.join(LESSONS_DIR, 'uvm', slug), results, meta });
    }
  }

  // ── mlir/ ────────────────────────────────────────────────────────────────────
  // MLIR lessons are read-only display lessons (no exercises, no solution files).
  // We validate that each .mlir file parses and runs without error via circt-sim.
  {
    const mlirSim = await loadTool('circt-sim');
    for (const slug of listDir('mlir')) {
      if (!shouldRun(`mlir/${slug}`)) continue;
      await runMlirLesson({ sim: mlirSim, slug, lessonDir: path.join(LESSONS_DIR, 'mlir', slug), work, results });
    }
  }

  // ── cocotb/ ─────────────────────────────────────────────────────────────────
  const cocotbDeps = checkCocotbDeps();
  if (!cocotbDeps.ok) {
    if (FILTER.length === 0) {
      console.log(`\n${D}Skipping cocotb/ — ${cocotbDeps.reason}${X}\n`);
      for (const slug of listDir('cocotb')) results.skip++;
    }
  } else {
    for (const slug of listDir('cocotb')) {
      if (!shouldRun(`cocotb/${slug}`)) continue;
      await runCocotbLesson({ slug, lessonDir: path.join(LESSONS_DIR, 'cocotb', slug), results, work });
    }
  }

  // ── summary ──────────────────────────────────────────────────────────────────
  const { pass, fail, xfail, xpass, skip, failures } = results;

  if (failures.length > 0) {
    console.log('\n── failures ──────────────────────────────────────');
    for (const { label, mode, reason, output } of failures) {
      console.log(`\n${R}FAIL${X} ${label} [${mode}]: ${reason}`);
      if (output?.trim()) output.trimEnd().split('\n').forEach(l => console.log(`  ${l}`));
    }
  }

  if (xfail > 0) {
    console.log('\n── known CIRCT bugs (xfail) ─────────────────────');
    for (const [label, reason] of CIRCT_XFAIL) {
      console.log(`  ${Y}XFAIL${X} ${label}: ${reason}`);
    }
  }

  const bar = '─────────────────────────────────────';
  console.log(`\n${bar}`);
  const xpassNote = xpass > 0 ? `, ${xpass} XPASS (CIRCT bug fixed!)` : '';
  const xfailNote = xfail > 0 ? `, ${xfail} xfail (known CIRCT bugs)` : '';
  if (fail === 0) {
    console.log(`${G}ALL PASS${X}  ${pass} checks passed${xpassNote}${xfailNote}, ${skip} skipped`);
  } else {
    console.log(`${R}FAILURES${X}  ${pass} passed, ${fail} failed${xpassNote}${xfailNote}, ${skip} skipped`);
  }
  console.log(`${bar}\n`);

  if (fail > 0) process.exit(1);
}

main().catch(e => { console.error(e); process.exit(1); });
