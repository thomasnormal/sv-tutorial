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

  it('keeps the functional coverage visual paired with its explanation', () => {
    const description = read('uvm/covergroup/description.html');
    expect(description).toContain('coverage-flow.svg');
    expect(description).toContain('get_coverage()');
    expect(description).toContain('every address in both read and write modes');
  });

  it('keeps the coverage-driven loop visual paired with its explanation', () => {
    const description = read('uvm/coverage-driven/description.html');
    expect(description).toContain('coverage-loop.svg');
    expect(description).toContain('raise_objection()');
    expect(description).toContain('finite number of attempts');
  });

  it('keeps the cross-coverage matrix visual paired with its explanation', () => {
    expect(read('uvm/cross-coverage/description.html')).toContain('cross-matrix.svg');
  });

  it('keeps the welcome lesson focused on its one generated idea', () => {
    const description = read('sv/welcome/description.html');
    expect(description).toContain("Today's one idea is simulation output");
    expect(description).toContain('supplied scaffolding');
  });

  it('keeps the data-types exercise aligned with its five intent checks', () => {
    const description = read('sv/data-types/description.html');
    const starter = read('sv/data-types/data_types.sv');
    expect(description).toContain('Five declarations use the wrong type or shape');
    expect(description).toContain('five FAIL lines should become five OK lines');
    expect(starter).toContain('signed 8-bit 2-state type for a testbench offset');
    expect(starter).toContain('4-state 4-bit type for an RTL status nibble');
  });

  it('keeps the priority encoder exercise aligned with its casez patterns', () => {
    const description = read('sv/priority-enc/description.html');
    const starter = read('sv/priority-enc/priority_enc.sv');
    expect(description).toContain('first matching branch wins');
    expect(description).toContain('4\'b1???');
    expect(starter).toContain('casez (req)');
    expect(starter).toContain('four branches in descending priority');
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
