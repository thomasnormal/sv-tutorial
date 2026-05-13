import { describe, expect, it } from 'vitest';
import { CirctWasmAdapter } from './circt-adapter.js';

function createAdapterWithInvokeTool(invokeTool) {
  const adapter = new CirctWasmAdapter();
  adapter.init = async () => {
    adapter.ready = true;
  };
  adapter._invokeTool = invokeTool;
  return adapter;
}

describe('CirctWasmAdapter.run with MLIR workspace input', () => {
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
});
