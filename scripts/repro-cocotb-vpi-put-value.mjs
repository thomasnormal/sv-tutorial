#!/usr/bin/env node
import { spawn } from 'node:child_process';
import fs from 'node:fs/promises';
import path from 'node:path';
import vm from 'node:vm';
import { createRequire } from 'node:module';
import { performance } from 'node:perf_hooks';
import { fileURLToPath } from 'node:url';
import {
  VPI,
  vpiWriteString as wsWriteString,
  vpiMakeCbData,
  vpiFree,
  vpiMakeIntValue as wsMakeVpiValue,
  vpiReadIntValue as wsReadVpiIntValue
} from '../src/runtime/vpi-abi.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const ROOT = path.resolve(__dirname, '..');
const CIRCT_DIR = path.join(ROOT, 'public', 'circt');
const VERILOG_JS = path.join(CIRCT_DIR, 'circt-verilog.js');
const SIM_VPI_JS = path.join(CIRCT_DIR, 'circt-sim-vpi.js');
const SIM_VPI_WASM = path.join(CIRCT_DIR, 'circt-sim-vpi.wasm');
const DEFAULT_SOURCE = path.join(ROOT, 'src', 'lessons', 'cocotb', 'first-test', 'adder.sol.sv');
const DEFAULT_TOP = 'adder';

function parseArgs(argv) {
  const out = {
    source: DEFAULT_SOURCE,
    top: DEFAULT_TOP,
    keepTmp: false
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--source' && argv[i + 1]) {
      out.source = path.resolve(argv[++i]);
      continue;
    }
    if (arg === '--top' && argv[i + 1]) {
      out.top = argv[++i];
      continue;
    }
    if (arg === '--keep-tmp') {
      out.keepTmp = true;
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      printHelp();
      process.exit(0);
    }
    throw new Error(`unknown argument: ${arg}`);
  }

  return out;
}

function printHelp() {
  console.log(
    [
      'Usage: node scripts/repro-cocotb-vpi-put-value.mjs [options]',
      '',
      'Options:',
      '  --source <file>   SystemVerilog source to compile (default: cocotb adder.sol.sv)',
      '  --top <name>      top module name (default: adder)',
      '  --keep-tmp        keep temporary mlir/output files',
      '  --help            show this help text'
    ].join('\n')
  );
}

async function fileExists(p) {
  try {
    await fs.access(p);
    return true;
  } catch {
    return false;
  }
}

async function runNodeScript(scriptPath, args) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [scriptPath, ...args], {
      stdio: ['ignore', 'pipe', 'pipe']
    });
    let stdout = '';
    let stderr = '';

    child.stdout.on('data', (buf) => { stdout += String(buf); });
    child.stderr.on('data', (buf) => { stderr += String(buf); });
    child.on('error', reject);
    child.on('exit', (code) => resolve({ code: code ?? 1, stdout, stderr }));
  });
}

function ensureSimModuleHelpers(M, context) {
  if (typeof M._malloc !== 'function' && typeof context._malloc === 'function') {
    M._malloc = (size) => context._malloc(size);
  }
  if (typeof M._free !== 'function' && typeof context._free === 'function') {
    M._free = (ptr) => context._free(ptr);
  }
  if (typeof M.getValue !== 'function') {
    M.getValue = (ptr, type) => {
      if (type === 'i32') return context.HEAP32[ptr >>> 2];
      if (type === 'double') return context.HEAPF64[ptr >>> 3];
      return 0;
    };
  }
  if (typeof M.setValue !== 'function') {
    M.setValue = (ptr, value, type) => {
      if (type === 'i32') context.HEAP32[ptr >>> 2] = value | 0;
      else if (type === 'double') context.HEAPF64[ptr >>> 3] = +value;
    };
  }
  if (!M.HEAPU8) {
    Object.defineProperty(M, 'HEAPU8', {
      get() { return context.HEAPU8; },
      configurable: true
    });
  }
  if (!M.FS && context.FS) M.FS = context.FS;
}

function wsGetSignal(M, signalName) {
  const namePtr = wsWriteString(M, signalName);
  const handle = (M._vpi_handle_by_name(namePtr, 0)) | 0;
  M._free(namePtr);
  if (!handle) return { handle: 0, id: 0, type: -1, size: -1, value: null, name: signalName };

  const valuePtr = wsMakeVpiValue(M, 0);
  M._vpi_get_value(handle, valuePtr);
  const value = wsReadVpiIntValue(M, valuePtr);
  M._free(valuePtr);

  return {
    handle,
    id: M.getValue(handle, 'i32') | 0,
    type: (M._vpi_get(VPI.vpiType, handle)) | 0,
    size: (M._vpi_get(VPI.vpiSize, handle)) | 0,
    value,
    name: signalName
  };
}

function wsPutSignal(M, handle, intVal) {
  const valuePtr = wsMakeVpiValue(M, intVal);
  const ret = (M._vpi_put_value(handle, valuePtr, 0, 0)) | 0;
  M._free(valuePtr);
  return ret;
}

function createTableAllocator(table) {
  const reserved = new Set();
  const replaced = [];

  function reserveSlot() {
    for (let i = 1; i < table.length; i += 1) {
      if (reserved.has(i)) continue;
      if (table.get(i) === null) return i;
    }
    // If the table is fixed-size with no non-zero null slots, borrow from the tail.
    for (let i = table.length - 1; i >= 1; i -= 1) {
      if (!reserved.has(i)) return i;
    }
    throw new Error('unable to reserve a wasm table slot');
  }

  return {
    install(wasmBytes, imports = undefined) {
      const mod = new WebAssembly.Module(wasmBytes);
      const inst = new WebAssembly.Instance(mod, imports);
      const slot = reserveSlot();
      reserved.add(slot);
      replaced.push({ slot, fn: table.get(slot) });
      table.set(slot, inst.exports.f);
      return slot;
    },
    restore() {
      for (let i = replaced.length - 1; i >= 0; i -= 1) {
        const { slot, fn } = replaced[i];
        table.set(slot, fn);
      }
    }
  };
}

function makeNoopCbPtr(allocator) {
  try {
    return allocator.install(new Uint8Array([
      0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
      0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f,
      0x03, 0x02, 0x01, 0x00,
      0x07, 0x05, 0x01, 0x01, 0x66, 0x00, 0x00,
      0x0a, 0x06, 0x01, 0x04, 0x00, 0x41, 0x00, 0x0b
    ]));
  } catch {
    return 1;
  }
}

function installStartupFunction({ M, allocator, cbRtn, onStartupRegister }) {
  const startupBytes = new Uint8Array([
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
    0x01, 0x04, 0x01, 0x60, 0x00, 0x00,
    0x02, 0x09, 0x01, 0x03, 0x65, 0x6e, 0x76, 0x01, 0x72, 0x00, 0x00,
    0x03, 0x02, 0x01, 0x00,
    0x07, 0x05, 0x01, 0x01, 0x66, 0x00, 0x01,
    0x0a, 0x06, 0x01, 0x04, 0x00, 0x10, 0x00, 0x0b
  ]);

  const slot = allocator.install(startupBytes, {
    env: {
      r() {
        const cbData = vpiMakeCbData(M, {
          reason: VPI.cbStartOfSimulation,
          cbRtn,
          obj: 0,
          time: 0,
          value: 0,
          userData: 0
        });
        const handle = (M._vpi_register_cb(cbData)) | 0;
        vpiFree(M, cbData);
        onStartupRegister(handle);
      }
    }
  });

  return slot;
}

function isExitException(err) {
  const t = String((err && err.message) || err || '');
  return t.includes('ExitStatus') || t.includes('Program terminated') || t.includes('exit(');
}

function pickFirstFound(M, names) {
  const attempts = [];
  for (const name of names) {
    const info = wsGetSignal(M, name);
    attempts.push(info);
    if (info.handle) return { chosen: info, attempts };
  }
  return { chosen: attempts[0] || wsGetSignal(M, names[0]), attempts };
}

async function compileToMlir({ sourcePath, top, outMlirPath }) {
  const args = [
    '--resource-guard=false',
    '--ir-llhd',
    '--timescale',
    '1ps/1ps',
    '--single-unit',
    '--top',
    top,
    '-o',
    outMlirPath,
    sourcePath
  ];

  const { code, stdout, stderr } = await runNodeScript(VERILOG_JS, args);
  if (code !== 0) {
    throw new Error(
      [
        `circt-verilog failed (exit=${code})`,
        stdout.trim(),
        stderr.trim()
      ].filter(Boolean).join('\n')
    );
  }
}

async function loadSimModule() {
  const simSource = await fs.readFile(SIM_VPI_JS, 'utf8');
  const logs = [];
  let ready = false;

  const context = {
    console,
    process,
    Buffer,
    URL,
    TextEncoder,
    TextDecoder,
    WebAssembly,
    performance,
    setTimeout,
    clearTimeout,
    setInterval,
    clearInterval,
    require: createRequire(SIM_VPI_JS),
    __filename: SIM_VPI_JS,
    __dirname: path.dirname(SIM_VPI_JS),
    module: { exports: {} },
    exports: {}
  };
  context.globalThis = context;
  context.Module = {
    noInitialRun: true,
    noExitRuntime: true,
    locateFile(file) {
      return file.endsWith('.wasm') ? SIM_VPI_WASM : file;
    },
    onRuntimeInitialized() {
      ready = true;
    },
    print(line) {
      logs.push(`[sim] ${line}`);
    },
    printErr(line) {
      logs.push(`[sim] ${line}`);
    }
  };

  vm.createContext(context);
  vm.runInContext(`var Module = globalThis.Module || {};\n${simSource}`, context, { filename: SIM_VPI_JS });

  const start = Date.now();
  while (!ready && Date.now() - start < 30_000) {
    await new Promise((resolve) => setTimeout(resolve, 20));
  }
  if (!ready) throw new Error('timed out waiting for circt-sim-vpi runtime initialization');

  const M = context.Module;
  ensureSimModuleHelpers(M, context);
  if (!M.FS || typeof M.FS.writeFile !== 'function') {
    throw new Error('sim module FS API is unavailable');
  }

  return { context, M, logs };
}

async function main() {
  const args = parseArgs(process.argv.slice(2));

  if (!(await fileExists(VERILOG_JS))) throw new Error(`missing file: ${VERILOG_JS}`);
  if (!(await fileExists(SIM_VPI_JS))) throw new Error(`missing file: ${SIM_VPI_JS}`);
  if (!(await fileExists(SIM_VPI_WASM))) throw new Error(`missing file: ${SIM_VPI_WASM}`);
  if (!(await fileExists(args.source))) throw new Error(`missing source file: ${args.source}`);

  const tmpDir = await fs.mkdtemp('/tmp/repro-vpi-put-value-');
  const hostMlirPath = path.join(tmpDir, 'design.llhd.mlir');
  const simMlirPath = '/workspace/out/design.llhd.mlir';
  let tableAllocator = null;
  const debug = {
    startupRegisterHandle: null,
    startOfSimulationFired: false,
    cbFuncPtr: null,
    signalChoice: {},
    signalAttempts: {},
    preRead: {},
    put: {},
    postRead: {},
    notes: []
  };

  try {
    await compileToMlir({ sourcePath: args.source, top: args.top, outMlirPath: hostMlirPath });
    const mlirText = await fs.readFile(hostMlirPath, 'utf8');

    const { context, M, logs } = await loadSimModule();

    try { M.FS.mkdir('/workspace'); } catch {}
    try { M.FS.mkdir('/workspace/out'); } catch {}
    M.FS.writeFile(simMlirPath, mlirText, { encoding: 'utf8' });

    const table = context.wasmTable;
    if (!table) throw new Error('wasmTable is unavailable in sim runtime');
    tableAllocator = createTableAllocator(table);

    const cbRtn = makeNoopCbPtr(tableAllocator);
    let startupSlot = 0;
    if (typeof M._vpi_startup_register === 'function') {
      try {
        startupSlot = installStartupFunction({
          M,
          allocator: tableAllocator,
          cbRtn,
          onStartupRegister(handle) {
            debug.startupRegisterHandle = handle;
          }
        });
        M._vpi_startup_register(startupSlot);
      } catch (err) {
        debug.notes.push(`startup function install failed: ${String(err && err.message || err)}`);
        M._vpi_startup_register(0);
      }
    } else {
      debug.notes.push('sim module has no _vpi_startup_register export');
    }

    context.circtSimVpiYieldHook = async (cbFuncPtr, cbDataPtr) => {
      const reason = M.getValue(cbDataPtr + 0, 'i32') | 0;
      debug.cbFuncPtr = cbFuncPtr | 0;
      if (reason !== VPI.cbStartOfSimulation) return;

      debug.startOfSimulationFired = true;

      const resolveA = pickFirstFound(M, ['A', `${args.top}.A`, 'dut.A']);
      const resolveB = pickFirstFound(M, ['B', `${args.top}.B`, 'dut.B']);
      const resolveX = pickFirstFound(M, ['X', `${args.top}.X`, 'dut.X']);

      debug.signalChoice.A = resolveA.chosen;
      debug.signalChoice.B = resolveB.chosen;
      debug.signalChoice.X = resolveX.chosen;
      debug.signalAttempts.A = resolveA.attempts;
      debug.signalAttempts.B = resolveB.attempts;
      debug.signalAttempts.X = resolveX.attempts;

      debug.preRead.A = wsGetSignal(M, resolveA.chosen.name).value;
      debug.preRead.B = wsGetSignal(M, resolveB.chosen.name).value;
      debug.preRead.X = wsGetSignal(M, resolveX.chosen.name).value;

      debug.put.A = resolveA.chosen.handle ? wsPutSignal(M, resolveA.chosen.handle, 9) : null;
      debug.put.B = resolveB.chosen.handle ? wsPutSignal(M, resolveB.chosen.handle, 6) : null;
      debug.put.X = resolveX.chosen.handle ? wsPutSignal(M, resolveX.chosen.handle, 15) : null;

      debug.postRead.A = wsGetSignal(M, resolveA.chosen.name).value;
      debug.postRead.B = wsGetSignal(M, resolveB.chosen.name).value;
      debug.postRead.X = wsGetSignal(M, resolveX.chosen.name).value;

      try {
        M._vpi_control(VPI.vpiFinish, 0);
      } catch (err) {
        debug.notes.push(`vpi_control(vpiFinish) failed: ${String(err && err.message || err)}`);
      }
    };

    const simArgs = [
      '--resource-guard=false',
      '--max-time=1000000',
      '--mode',
      'interpret',
      simMlirPath
    ];

    try {
      const ret = context.callMain(simArgs);
      if (ret && typeof ret.then === 'function') await ret;
    } catch (err) {
      if (!isExitException(err)) throw err;
    }

    const summary = {
      top: args.top,
      source: args.source,
      startupSlot,
      startupRegisterHandle: debug.startupRegisterHandle,
      startOfSimulationFired: debug.startOfSimulationFired,
      selectedSignals: {
        A: debug.signalChoice.A?.name || null,
        B: debug.signalChoice.B?.name || null,
        X: debug.signalChoice.X?.name || null
      },
      handles: {
        A: debug.signalChoice.A || null,
        B: debug.signalChoice.B || null,
        X: debug.signalChoice.X || null
      },
      preRead: debug.preRead,
      putReturn: debug.put,
      postRead: debug.postRead,
      notes: debug.notes
    };

    console.log(JSON.stringify(summary, null, 2));

    const aWrote = typeof debug.put.A === 'number' && debug.put.A !== 0;
    const bWrote = typeof debug.put.B === 'number' && debug.put.B !== 0;
    const xObserved = debug.postRead.X === 15;
    const pass = debug.startOfSimulationFired && aWrote && bWrote && xObserved;

    if (!pass) {
      const tail = logs.slice(-30).join('\n');
      if (tail) {
        console.error('\n--- sim log tail ---');
        console.error(tail);
      }
      process.exitCode = 1;
    }
  } finally {
    if (tableAllocator) {
      try { tableAllocator.restore(); } catch {}
    }
    if (!args.keepTmp) {
      await fs.rm(tmpDir, { recursive: true, force: true });
    } else {
      console.error(`# kept tmp dir: ${tmpDir}`);
    }
  }
}

main().catch((err) => {
  console.error(String(err && err.stack ? err.stack : err));
  process.exitCode = 1;
});
