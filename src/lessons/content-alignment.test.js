import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import path from 'node:path';

const root = path.resolve(process.cwd(), 'src/lessons');
const read = (file) => readFileSync(path.join(root, file), 'utf8');

describe('browser-audit lesson alignment', () => {
  it('does not mark incomplete starters as passed', () => {
    expect(read('sva/concurrent-sim/tb.sv')).not.toContain('$display("PASS")');
    expect(read('sva/vacuous-pass/tb.sv')).not.toContain('$display("PASS")');
    expect(read('sva/formal-assume/tb.sv')).not.toContain('$display("PASS")');
  });

  it('keeps UVM coverage starters syntactically valid', () => {
    expect(read('uvm/covergroup/mem_coverage.sv')).toMatch(/report_phase[\s\S]*?\$fatal\([^;]+\);/);
    expect(read('uvm/cross-coverage/mem_coverage.sv')).toMatch(/report_phase[\s\S]*?\$fatal\([^;]+\);/);
  });

  it('keeps official code and instructions aligned', () => {
    expect(read('sv/modports/description.html')).toContain('modport target   (input  we, addr, wdata, clk, output rdata);');
    expect(read('sv/coverpoint-bins/cov_bins.sol.sv')).toContain('ignore_bins reserved = {14, 15};');
    expect(read('sva/vacuous-pass/tb.sol.sv')).toContain('$display("done: did rg_cover fire?");');
    expect(read('sva/concurrent-sim/monitor.sol.sv')).toContain('PASS: assertion exercised');
    expect(read('sva/sequence-basics/grant_check.sol.sv')).not.toContain('llhd.process');
    expect(read('sva/sequence-basics/grant_check.sol.sv')).not.toContain('$display("PASS at');
  });
});
