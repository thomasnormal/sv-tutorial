import { describe, expect, it } from 'vitest';
import { MoxWasmAdapter } from './mox-adapter.js';

function createAdapterWithInvokeTool(invokeTool) {
  const adapter = new MoxWasmAdapter();
  adapter.init = async () => {
    adapter.ready = true;
  };
  adapter._invokeTool = invokeTool;
  return adapter;
}

describe('MoxWasmAdapter.run with MLIR workspace input', () => {
  it('simulates MLIR input directly without requiring SystemVerilog files', async () => {
    const calls = [];
    const adapter = createAdapterWithInvokeTool(async (toolName, request) => {
      calls.push({ toolName, request });
      return {
        exitCode: 0,
        stdout: '',
        stderr: '',
        files: {
          '/workspace/out/waves.vcd': '$enddefinitions $end\n'
        }
      };
    });

    const result = await adapter.run({
      files: {
        '/src/adder.mlir': `
          hw.module @adder(in %a : i8, in %b : i8, out sum : i8) {
            %0 = comb.add %a, %b : i8
            hw.output %0 : i8
          }
        `
      },
      top: 'adder'
    });

    expect(result.ok).toBe(true);
    expect(result.logs).toContain('# using MLIR source: /src/adder.mlir');
    expect(result.logs).not.toContain('# no SystemVerilog source files found in workspace');
    expect(calls).toHaveLength(1);
    expect(calls[0].toolName).toBe('sim');
    expect(calls[0].request.args).toContain('--top');

    const topArgIndex = calls[0].request.args.indexOf('--top');
    expect(calls[0].request.args[topArgIndex + 1]).toBe('adder');
    expect(calls[0].request.files['/workspace/out/design.llhd.mlir']).toContain('hw.module @adder');
  });

  it('chooses an MLIR module name when focus-derived top does not exist', async () => {
    const calls = [];
    const adapter = createAdapterWithInvokeTool(async (toolName, request) => {
      calls.push({ toolName, request });
      return {
        exitCode: 0,
        stdout: '',
        stderr: '',
        files: {}
      };
    });

    const result = await adapter.run({
      files: {
        '/src/lowering.mlir': `
          hw.module @dff_before(in %d : i8, in %clk : i1, out q : i8) {
            hw.output %d : i8
          }
          hw.module @dff_after(in %d : i8, in %clk : i1, out q : i8) {
            hw.output %d : i8
          }
        `
      },
      top: 'lowering'
    });

    expect(result.ok).toBe(true);
    expect(calls).toHaveLength(1);
    const topArgIndex = calls[0].request.args.indexOf('--top');
    expect(calls[0].request.args[topArgIndex + 1]).toBe('dff_after');
  });

  it('runs the @tb testbench together with the design it instantiates', async () => {
    const calls = [];
    const adapter = createAdapterWithInvokeTool(async (toolName, request) => {
      calls.push({ toolName, request });
      return { exitCode: 0, stdout: '', stderr: '', files: {} };
    });

    // Lessons keep the design in the focus file and the testbench in *_tb.mlir;
    // the page passes the focus-derived top ('adder').
    const result = await adapter.run({
      files: {
        '/src/adder.mlir': 'hw.module @adder(in %a : i8, in %b : i8, out sum : i8) {\n}\n',
        '/src/adder_tb.mlir': 'hw.module @tb() {\n  %s = hw.instance "dut" @adder(a: %a: i8, b: %b: i8) -> (sum: i8)\n}\n'
      },
      top: 'adder'
    });

    expect(result.ok).toBe(true);
    expect(calls).toHaveLength(1);
    const { args, files } = calls[0].request;
    expect(args[args.indexOf('--top') + 1]).toBe('tb');
    const mlir = files['/workspace/out/design.llhd.mlir'];
    expect(mlir).toContain('hw.module @adder');
    expect(mlir).toContain('hw.module @tb');
  });
});

describe('MoxWasmAdapter.run coverage collection', () => {
  // Mox (like Xcelium without -coverage) does not sample covergroups unless
  // coverage is enabled, so get_coverage() returns 0 and no report prints.
  async function runArgsFor(source) {
    const calls = [];
    const adapter = createAdapterWithInvokeTool(async (toolName, request) => {
      calls.push({ toolName, request });
      return { exitCode: 0, stdout: '', stderr: '', files: {} };
    });
    await adapter.run({ files: { '/src/top.sv': source }, top: 'top' });
    expect(calls).toHaveLength(1);
    expect(calls[0].toolName).toBe('run');
    return calls[0].request.args;
  }

  it('enables coverage when the design declares a covergroup', async () => {
    const args = await runArgsFor(`module top;
  bit v;
  covergroup cg; coverpoint v; endgroup
  cg c = new;
endmodule
`);
    expect(args).toContain('--coverage-report');
  });

  it('does not enable coverage for designs without covergroups', async () => {
    const args = await runArgsFor('module top; initial $display("hi"); endmodule\n');
    expect(args).not.toContain('--coverage-report');
  });
});

describe('MoxWasmAdapter.run without a mox-run artifact', () => {
  // Mox does not build mox-run for wasm (tools/CMakeLists.txt gates it with
  // `if(NOT EMSCRIPTEN)`), so a toolchain rebuilt from Mox has no mox-run.js.
  // Plain SV lessons must still run through mox-verilog -> mox-sim.
  it('falls back to mox-verilog + mox-sim when mox-run cannot load', async () => {
    const calls = [];
    const logs = [];
    const adapter = createAdapterWithInvokeTool(async (toolName, request) => {
      calls.push(toolName);
      if (toolName === 'run') {
        throw new Error('Failed to load tool script: http://localhost/mox/mox-run.js');
      }
      if (toolName === 'verilog') {
        return {
          exitCode: 0, stdout: '', stderr: '',
          files: { '/workspace/out/design.llhd.mlir': 'hw.module @top() { hw.output }\n' }
        };
      }
      return { exitCode: 0, stdout: 'PASS\n', stderr: '', files: {} };
    });
    const result = await adapter.run({
      files: { '/src/top.sv': 'module top; initial $display("PASS"); endmodule\n' },
      top: 'top',
      onLog: (line) => logs.push(line)
    });
    expect(calls).toEqual(['run', 'verilog', 'sim']);
    expect(result.ok).toBe(true);
    expect(logs.join('\n')).toContain('mox-run is not available');

    // Later runs skip the failed mox-run load.
    calls.length = 0;
    await adapter.run({
      files: { '/src/top.sv': 'module top; initial $display("PASS"); endmodule\n' },
      top: 'top'
    });
    expect(calls).toEqual(['verilog', 'sim']);
  });
});
