export const MOX_FORK_REPO = 'git@github.com:normal-computing/mox.git';

function normalizeBaseUrl(raw) {
  const base = String(raw || '').trim();
  if (!base || base === '.' || base === './') return '/';

  // Normalize optional leading "./" used by static builds.
  const noDotPrefix = base.startsWith('./') ? base.slice(1) : base;
  const withLeadingSlash = noDotPrefix.startsWith('/') ? noDotPrefix : `/${noDotPrefix}`;
  const withTrailingSlash = withLeadingSlash.endsWith('/')
    ? withLeadingSlash
    : `${withLeadingSlash}/`;

  // Remove "/./" segments so "/./mox" becomes "/mox".
  return withTrailingSlash.replace(/\/\.\//g, '/');
}

const BASE = normalizeBaseUrl(import.meta.env.VITE_BASE || import.meta.env.BASE_URL);

export function getRuntimeBasePath() {
  return BASE;
}

export const Z3_SCRIPT_URL = `${BASE}z3/z3-built.js`;
const DEFAULT_TOOLCHAIN = {
  verilog: {
    js: `${BASE}mox/mox-verilog.js`,
    wasm: `${BASE}mox/mox-verilog.wasm`
  },
  sim: {
    js: `${BASE}mox/mox-sim.js`,
    wasm: `${BASE}mox/mox-sim.wasm`
  },
  run: {
    js: `${BASE}mox/mox-run.js`,
    wasm: `${BASE}mox/mox-run.wasm`
  },
  bmc: {
    js: `${BASE}mox/mox-bmc.js`,
    wasm: `${BASE}mox/mox-bmc.wasm`
  },
  simVpi: {
    js: `${BASE}mox/mox-sim-vpi.js`,
    wasm: `${BASE}mox/mox-sim-vpi.wasm`
  },
  lec: {
    js: `${BASE}mox/mox-lec.js`,
    wasm: `${BASE}mox/mox-lec.wasm`
  }
};

const DEFAULT_VERILOG_ARGS = ['--resource-guard=false', '--ir-llhd', '--timescale', '1ns/1ns', '--single-unit'];
const DEFAULT_LEC_VERILOG_ARGS = ['--resource-guard=false', '--ir-hw', '--single-unit'];
const DEFAULT_LEC_ARGS = [
  '--resource-guard=false',
  '--assume-known-inputs',
  '-c1', '{module1}',
  '-c2', '{module2}',
  '--emit-smtlib',
  '-o', '/workspace/out/check.smt2',
  '{input}'
];
const DEFAULT_SIM_ARGS = ['--resource-guard=false'];
// mox-run is the unified single-command compile+simulate driver. These are the
// frontend/sim flags shared by every invocation; the adapter appends per-run
// --top, --vcd and --trace-all. We deliberately omit flags whose defaults
// already work in the wasm build: --mode interpret (no AOT is available, so
// interpret is the default) and --resource-guard=false (the guard does not
// interfere with these sims) — keeping the taught command minimal.
const DEFAULT_RUN_ARGS = ['--timescale', '1ns/1ns', '--single-unit'];
const DEFAULT_BMC_ARGS = [
  '--resource-guard=false',
  '--assume-known-inputs',
  '-b',
  '20',
  '--module',
  '{top}',
  '--emit-smtlib',
  '-o',
  '/workspace/out/check.smt2',
  '{input}'
];

function parseArgs(raw, fallback) {
  if (!raw) return fallback;
  try {
    const parsed = JSON.parse(raw);
    if (Array.isArray(parsed) && parsed.every((v) => typeof v === 'string')) {
      return parsed;
    }
  } catch {
    // Fallback to a simple shell-like split for convenience.
  }
  return raw
    .split(' ')
    .map((s) => s.trim())
    .filter(Boolean);
}

function pickUrlFromEnv(primary, fallback) {
  return primary || fallback;
}

export function getMoxRuntimeConfig() {
  return {
    toolchain: {
      verilog: {
        js: pickUrlFromEnv(import.meta.env.VITE_MOX_VERILOG_JS_URL, DEFAULT_TOOLCHAIN.verilog.js),
        wasm: pickUrlFromEnv(import.meta.env.VITE_MOX_VERILOG_WASM_URL, DEFAULT_TOOLCHAIN.verilog.wasm)
      },
      sim: {
        js: pickUrlFromEnv(import.meta.env.VITE_MOX_SIM_JS_URL, DEFAULT_TOOLCHAIN.sim.js),
        wasm: pickUrlFromEnv(import.meta.env.VITE_MOX_SIM_WASM_URL, DEFAULT_TOOLCHAIN.sim.wasm)
      },
      run: {
        js: pickUrlFromEnv(import.meta.env.VITE_MOX_RUN_JS_URL, DEFAULT_TOOLCHAIN.run.js),
        wasm: pickUrlFromEnv(import.meta.env.VITE_MOX_RUN_WASM_URL, DEFAULT_TOOLCHAIN.run.wasm)
      },
      bmc: {
        js: pickUrlFromEnv(import.meta.env.VITE_MOX_BMC_JS_URL, DEFAULT_TOOLCHAIN.bmc.js),
        wasm: pickUrlFromEnv(import.meta.env.VITE_MOX_BMC_WASM_URL, DEFAULT_TOOLCHAIN.bmc.wasm)
      },
      simVpi: {
        js: pickUrlFromEnv(import.meta.env.VITE_MOX_SIM_VPI_JS_URL, DEFAULT_TOOLCHAIN.simVpi.js),
        wasm: pickUrlFromEnv(import.meta.env.VITE_MOX_SIM_VPI_WASM_URL, DEFAULT_TOOLCHAIN.simVpi.wasm)
      },
      lec: {
        js: pickUrlFromEnv(import.meta.env.VITE_MOX_LEC_JS_URL, DEFAULT_TOOLCHAIN.lec.js),
        wasm: pickUrlFromEnv(import.meta.env.VITE_MOX_LEC_WASM_URL, DEFAULT_TOOLCHAIN.lec.wasm)
      }
    },
    pyodideUrl: import.meta.env.VITE_PYODIDE_URL || `${BASE}pyodide/pyodide.js`,
    verilogArgs: parseArgs(import.meta.env.VITE_MOX_VERILOG_ARGS, DEFAULT_VERILOG_ARGS),
    simArgs: parseArgs(import.meta.env.VITE_MOX_SIM_ARGS, DEFAULT_SIM_ARGS),
    runArgs: parseArgs(import.meta.env.VITE_MOX_RUN_ARGS, DEFAULT_RUN_ARGS),
    bmcArgs: parseArgs(import.meta.env.VITE_MOX_BMC_ARGS, DEFAULT_BMC_ARGS),
    lecVerilogArgs: parseArgs(import.meta.env.VITE_MOX_LEC_VERILOG_ARGS, DEFAULT_LEC_VERILOG_ARGS),
    lecArgs: parseArgs(import.meta.env.VITE_MOX_LEC_ARGS, DEFAULT_LEC_ARGS),
    note: import.meta.env.VITE_MOX_NOTE || ''
  };
}

export function getRuntimeEnvDoc() {
  return {
    VITE_MOX_VERILOG_JS_URL: 'mox-verilog JS artifact URL.',
    VITE_MOX_VERILOG_WASM_URL: 'mox-verilog WASM artifact URL.',
    VITE_MOX_SIM_JS_URL: 'mox-sim JS artifact URL.',
    VITE_MOX_SIM_WASM_URL: 'mox-sim WASM artifact URL.',
    VITE_MOX_BMC_JS_URL: 'mox-bmc JS artifact URL.',
    VITE_MOX_BMC_WASM_URL: 'mox-bmc WASM artifact URL.',
    VITE_MOX_VERILOG_ARGS: 'JSON array or space-separated args passed before source files.',
    VITE_MOX_SIM_ARGS: 'JSON array or space-separated args passed before MLIR input.',
    VITE_MOX_BMC_ARGS: 'JSON array or space-separated args for BMC fallback.'
  };
}
