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

  it('keeps the operator exercise aligned with its seven expression outputs', () => {
    const description = read('sv/assign-operators/description.html');
    const starter = read('sv/assign-operators/operator_lab.sv');
    expect(description).toContain('continuous <code>assign</code>');
    expect(description).toContain('seven outputs');
    expect(description).toContain('widened operands for <code>full_sum</code>');
    expect(description).toContain('signed addition for <code>signed_sum</code>');
    expect(starter).toContain('bitwise, reduction, ternary,');
    expect(starter).toContain('unsigned-sum, and signed-sum outputs');
    for (const output of ['bitwise_and', 'bitwise_or', 'any_set', 'chosen', 'wrapped_sum', 'full_sum', 'signed_sum']) {
      expect(starter).toContain(output);
    }
  });

  it('keeps the counter exercise aligned with its reset-priority behavior', () => {
    const description = read('sv/counter/description.html');
    const starter = read('sv/counter/counter.sv');
    expect(description).toContain('ordered control conditions');
    expect(description).toContain('repeat(5) @(posedge clk);');
    expect(description).toContain('reset higher priority than enable');
    expect(starter).toContain('synchronous reset, then increment when en');
    expect(starter).toContain('always_ff @(posedge clk)');
  });

  it('keeps the shift-register exercise aligned with its concatenation behavior', () => {
    const description = read('sv/shift-reg/description.html');
    const starter = read('sv/shift-reg/shift_reg.sv');
    expect(description).toContain('vector concatenation');
    expect(description).toContain('{&lt;state&gt;[N-2:0], &lt;serial_in&gt;}');
    expect(description).toContain('old <code>q[3]</code> to <code>serial_out</code>');
    expect(starter).toContain('synchronously clear q and serial_out');
    expect(starter).toContain('expose the old MSB, then shift serial_in into q[0]');
  });

  it('keeps the generate exercise aligned with its parameterized lanes', () => {
    const description = read('sv/generate/description.html');
    const starter = read('sv/generate/generate_lab.sv');
    expect(description).toContain('generate-for loop');
    expect(description).toContain('genvar');
    expect(description).toContain('<code>WIDTH</code> controls how many lanes');
    expect(starter).toContain('one-bit lane across the vector in both branches');
    expect(starter).toContain('named generate-for from 0 through WIDTH-1');
    expect(starter).toContain('matching generate-for');
  });

  it('keeps the typedef exercise aligned with its shared aliases', () => {
    const description = read('sv/typedef/description.html');
    const starter = read('sv/typedef/typedef_lab.sv');
    expect(description).toContain('typedef aliases');
    expect(description).toContain('one alias keeps width and intent together');
    expect(description).toContain('shared type names');
    expect(starter).toContain('aliases are ready to use');
    expect(starter).toContain('sum, result, selected lane, and lane_copy');
    expect(starter).toContain('typedef logic [7:0] data_t;');
    expect(starter).toContain('typedef logic [1:0] lane_t;');
  });

  it('keeps the tasks exercise aligned with its timing-aware helpers', () => {
    const description = read('sv/tasks-functions/description.html');
    const starter = read('sv/tasks-functions/tb.sv');
    expect(description).toContain('A <strong><dfn');
    expect(description).toContain('three routine stubs');
    expect(description).toContain('<code>write_word(vif, addr, data)</code>');
    expect(description).toContain('<code>read_word(vif, addr, data)</code>');
    expect(starter).toContain('odd number of set bits (reduction XOR)');
    expect(starter).toContain('drive vif.we=1, vif.addr, vif.wdata for one rising edge');
    expect(starter).toContain('set vif.addr, wait one rising edge, capture vif.rdata into data');
  });

  it('keeps the first UVM test aligned with its objection lifecycle', () => {
    const description = read('uvm/reporting/description.html');
    const starter = read('uvm/reporting/my_test.sv');
    const top = read('uvm/reporting/tb_top.sv');
    expect(description).toContain('raise_objection');
    expect(description).toContain('drop_objection');
    expect(description).toContain('`uvm_info(ID, msg, verbosity)');
    expect(description).toContain('`uvm_error(ID, msg)');
    expect(starter).toContain('TODO 1: raise the objection');
    expect(starter).toContain('TODO 4: drop the objection');
    expect(starter).toContain('TODO 5: print a PASS completion marker');
    expect(top).toContain('run_test("my_test")');
  });

  it('keeps constrained-random work aligned with its three constraint scopes', () => {
    const description = read('uvm/constrained-random/description.html');
    const item = read('uvm/constrained-random/mem_item.sv');
    const test = read('uvm/constrained-random/mem_test.sv');
    const top = read('uvm/constrained-random/tb_top.sv');
    expect(description).toContain('three ways to do that');
    expect(description).toContain('randomize() with { }');
    expect(description).toContain('constraint_mode(0)');
    expect(item).toContain('TODO: add a dist weighting');
    expect(test).toContain('TODO: use randomize() with');
    expect(test).toContain('TODO: disable the named weighting constraint');
    expect(top).toContain('get_severity_count(UVM_ERROR) == 0');
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
