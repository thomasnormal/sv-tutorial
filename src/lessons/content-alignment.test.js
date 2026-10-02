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

  it('keeps the SystemVerilog Basics copy technically accurate', () => {
    const welcome = read('sv/welcome/description.html');
    const events = read('sv/events/description.html');
    const parameters = read('sv/parameters/description.html');
    const enums = read('sv/enums/description.html');

    expect(welcome).not.toContain('One tight paragraph on printf/display notation');
    expect(welcome).toContain('Calling <code>$finish</code> explicitly ends the simulation');
    expect(events).not.toContain('events are not stateful (latching)');
    expect(events).toContain('wait(event_name.triggered)');
    expect(events).toContain('IEEE 1800-2023 §15.5');
    expect(events).toContain('This event is generated automatically');
    expect(parameters).not.toContain('$bits(16) = 4');
    expect(parameters).toContain('IEEE 1800-2023 §20.6.2');
    expect(parameters).toContain('IEEE 1800-2023 §20.8.1');
    expect(parameters).toContain('replace the hardcoded dimensions');
    expect(enums).not.toContain('remove <code>state_bits</code>');
    expect(enums).toContain('do not add a separate <code>state_bits</code> port');
    expect(enums).toContain('IEEE 1800-2023 §6.19');
  });
});
