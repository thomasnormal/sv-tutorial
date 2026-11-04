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

  it('keeps modules and ports aligned with the typed declaration pattern', () => {
    const description = read('sv/modules-and-ports/description.html');
    const starter = read('sv/modules-and-ports/adder.sv');
    expect(description).toContain('Read <code>input logic [7:0] a</code> from left to right');
    expect(description).toContain('direction, <code>logic</code> gives the four-state type');
    expect(starter).toContain('declare a as an 8-bit logic input');
    expect(starter).toContain('declare sum as an 8-bit logic output');
  });

  it('keeps the data-types exercise aligned with its five intent checks', () => {
    const description = read('sv/data-types/description.html');
    const starter = read('sv/data-types/data_types.sv');
    expect(description).toContain('Five declarations use the wrong type or shape');
    expect(description).toContain('five FAIL lines should become five OK lines');
    expect(description).toContain('four elements with the default index range <code>[0:3]</code>');
    expect(description).toContain('<code>mem[0]</code> selects the first whole byte');
    expect(starter).toContain('signed 8-bit 2-state type for a testbench offset');
    expect(starter).toContain('4-state 4-bit type for an RTL status nibble');
  });

  it('keeps static-array arithmetic width visible in the exercise', () => {
    const description = read('sv/arrays-static/description.html');
    const testbench = read('sv/arrays-static/tb.sv');
    expect(description).toContain('8\'hFF');
    expect(description).toContain('8-bit <code>unpacked_total</code> wraps to zero');
    expect(testbench).toContain('0xFF + 1 wraps at 8 bits');
  });

  it('keeps the priority encoder exercise aligned with its casez patterns', () => {
    const description = read('sv/priority-enc/description.html');
    const starter = read('sv/priority-enc/priority_enc.sv');
    expect(description).toContain('first matching branch wins');
    expect(description).toContain('4\'b1???');
    expect(description).toContain('does not hide an unknown <code>X</code>');
    expect(description).toContain('default keeps the outputs known');
    expect(starter).toContain('casez (req)');
    expect(starter).toContain('four branches in descending priority');
  });

  it('keeps enum decoding explicit about invalid-state recovery', () => {
    const description = read('sv/enums/description.html');
    const solution = read('sv/enums/status.sol.sv');
    expect(description).toContain('state can contain <code>X</code> bits');
    expect(description).toContain('default keeps both outputs low');
    expect(solution).toContain('default: ;');
  });

  it('keeps the always_comb exercise latch-safe', () => {
    const description = read('sv/always-comb/description.html');
    const starter = read('sv/always-comb/mux.sv');
    const solution = read('sv/always-comb/mux.sol.sv');
    expect(description).toContain('Give the output a default value before the <code>case</code>');
    expect(description).toContain('synthesis can infer storage');
    expect(starter).toContain("y = '0;");
    expect(solution).toContain("y = '0;");
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
    expect(description).toContain('bitwise: one result bit per input bit');
    expect(description).toContain('Use <code>&amp;</code> and <code>|</code> when the operands are buses');
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
    expect(description).toContain('keeps <code>en=1</code> while <code>rst_n=0</code>');
    expect(description).toContain('reset branch wins before the increment branch');
    expect(starter).toContain('synchronous reset, then increment when en');
    expect(starter).toContain('always_ff @(posedge clk)');
    const alwaysFf = read('sv/always-ff/description.html');
    expect(alwaysFf).toContain('The same scheduling rule explains the <code>#1</code>');
    expect(alwaysFf).toContain('active region');
  });

  it('keeps the always_ff SRAM explanation aligned with NBA read timing', () => {
    const description = read('sv/always-ff/description.html');
    const starter = read('sv/always-ff/sram_core.sv');
    const solution = read('sv/always-ff/sram_core.sol.sv');
    expect(description).toContain('read-during-write behavior');
    expect(description).toContain('samples the old byte');
    expect(description).toContain('A later read of that address');
    expect(starter).toContain('this creates 1-cycle read latency');
    expect(solution).toContain('rdata <= mem[addr];');
  });

  it('keeps the events lesson explicit about same-slot race safety', () => {
    const description = read('sv/events/description.html');
    expect(description).toContain('<code>wait(write_done.triggered)</code>');
    expect(description).toContain('Use this form when either side may run first');
    expect(description).toContain('already made in this time slot');
  });

  it('keeps the shift-register exercise aligned with its concatenation behavior', () => {
    const description = read('sv/shift-reg/description.html');
    const starter = read('sv/shift-reg/shift_reg.sv');
    expect(description).toContain('vector concatenation');
    expect(description).toContain('{&lt;state&gt;[N-2:0], &lt;serial_in&gt;}');
    expect(description).toContain('old <code>q[3]</code> to <code>serial_out</code>');
    expect(description).toContain('the rightmost term becomes <code>q[0]</code>');
    expect(description).toContain('stream enters at the least-significant end');
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
    expect(description).toContain('different from a procedural <code>for</code> loop');
    expect(description).toContain('only the XOR branch exists');
  });

  it('keeps the Moore FSM explanation aligned with its two-block timing', () => {
    const description = read('sv/fsm/description.html');
    const testbench = read('sv/fsm/tb.sv');
    expect(description).toContain('reusable two-block shape');
    expect(description).toContain('next = state');
    expect(description).toContain('output defaults before the <code>case</code>');
    expect(description).toContain('one-cycle rhythm');
    expect(description).toContain('reports the failure count otherwise');
    expect(testbench).toContain('FAIL: %0d Moore FSM checks were wrong');
  });

  it('keeps the Mealy FSM explanation aligned with its immediate outputs', () => {
    const description = read('sv/mealy-fsm/description.html');
    const starter = read('sv/mealy-fsm/mealy_ctrl.sv');
    expect(description).toContain('raising <code>req</code> makes <code>grant</code> high immediately');
    expect(description).toContain('Current state');
    expect(description).toContain('short input glitch');
    expect(description).toContain('Register the output instead');
    expect(starter).toContain('Drive grant/done/busy from the current state and inputs.');
  });

  it('keeps covergroup sampling aligned with nonblocking stimulus timing', () => {
    const description = read('sv/covergroup-basics/description.html');
    const starter = read('sv/covergroup-basics/cov_intro.sv');
    expect(description).toContain('nonblocking assignments');
    expect(description).toContain('new random values become visible after that edge');
    expect(description).toContain('first sample records the initial zeros');
    expect(starter).toContain('we   <= $random;');
    expect(starter).toContain('addr <= $random;');
  });

  it('keeps named-bin exclusions aligned with the coverage denominator', () => {
    const description = read('sv/coverpoint-bins/description.html');
    const solution = read('sv/coverpoint-bins/cov_bins.sol.sv');
    expect(description).toContain('removes 14 and 15 from that coverpoint\'s denominator');
    expect(description).toContain('Ignoring a value does not prevent the stimulus from generating it');
    expect(solution).toContain('bins hi_half = {[8:15]};');
    expect(solution).toContain('ignore_bins reserved = {14, 15};');
  });

  it('keeps cross coverage aligned with its four named-bin cells', () => {
    const description = read('sv/cross-coverage/description.html');
    const starter = read('sv/cross-coverage/cov_cross.sv');
    expect(description).toContain('Each cell is built from the named bins');
    expect(description).toContain('16 × 2 raw value pairs');
    expect(description).toContain('high-address write');
    expect(description).toContain('name any missing cell');
    expect(starter).toContain('TODO: add a cross of cp_addr and cp_we');
  });

  it('keeps class construction explicit about four-state readback', () => {
    const description = read('sv/classes/description.html');
    const starter = read('sv/classes/mem_item.sv');
    const solution = read('sv/classes/mem_item.sol.sv');
    expect(description).toContain('explicitly initialize <code>rdata</code> to <code>8\'h00</code>');
    expect(description).toContain('avoids carrying an unknown value');
    expect(starter).toContain('initialize rdata to a known zero value');
    expect(solution).toContain('this.rdata = 8\'h00;');
  });

  it('keeps dynamic-array and queue work honest about FIFO order', () => {
    const description = read('sv/queues-arrays/description.html');
    const starter = read('sv/queues-arrays/addr_buf.sv');
    const solution = read('sv/queues-arrays/addr_buf.sol.sv');
    expect(description).toContain('form a FIFO');
    expect(description).toContain('popped sequence (<code>0, 1, 2, 3</code>)');
    expect(description).toContain('only when the four values come out in FIFO order');
    expect(starter).toContain('Check each value against expected');
    expect(solution).toContain('FIFO order expected');
  });

  it('keeps fork variants aligned with child lifetime and parent timing', () => {
    const description = read('sv/fork-join/description.html');
    const starter = read('sv/fork-join/concurrent.sv');
    const solution = read('sv/fork-join/concurrent.sol.sv');
    expect(description).toContain('join_any</code> only controls when the parent resumes');
    expect(description).toContain('<code>disable fork</code>');
    expect(description).toContain('leaves them alive so you can see their later messages');
    expect(starter).toContain('join_none: parent should continue at t=40ns');
    expect(solution).toContain('assert ($time == 40)');
  });

  it('keeps constrained randomization honest about solver failure', () => {
    const description = read('sv/randomization/description.html');
    const starter = read('sv/randomization/rand_txn.sv');
    const solution = read('sv/randomization/rand_txn.sol.sv');
    expect(description).toContain('The return value indicates success');
    expect(description).toContain('always check it');
    expect(starter).toContain('check that it succeeds');
    expect(starter).toContain('assert (t.randomize())');
    expect(solution).toContain('high_bank override randomize failed');
    expect(solution).not.toContain("void'(t.randomize())");
  });

  it('keeps concurrent assertion timing aligned with the driven scenarios', () => {
    const description = read('sva/concurrent-sim/description.html');
    const starter = read('sva/concurrent-sim/tb.sv');
    const solution = read('sva/concurrent-sim/monitor.sol.sv');
    expect(description).toContain('the first allowed edge for <code>gnt</code>');
    expect(description).toContain('no grant by <code>t+3</code> fails');
    expect(description).toContain('valid grant at the second allowed edge');
    expect(starter).toContain('// +2 cycles: gnt seen');
    expect(solution).toContain('req |-> ##[1:3] gnt');
  });

  it('keeps the vacuous-pass experiment explicit about its two runs', () => {
    const description = read('sva/vacuous-pass/description.html');
    const starter = read('sva/vacuous-pass/tb.sv');
    const solution = read('sva/vacuous-pass/vacuous.sol.sv');
    expect(description).toContain('the pulse is sampled on a rising edge');
    expect(description).toContain('first run cannot fail because it never creates an attempt');
    expect(description).toContain('second run produces visible cover output');
    expect(starter).toContain('TODO: uncomment the request stimulus');
    expect(solution).toContain('cover sequence (@(posedge clk) $rose(req) ##[1:2] gnt)');
  });

  it('keeps $isunknown coverage aligned with vector and sampling behavior', () => {
    const description = read('sva/isunknown/description.html');
    const testbench = read('sva/isunknown/tb.sv');
    const solution = read('sva/isunknown/xcheck.sol.sv');
    expect(description).toContain("logic [3:0] addr = 4'b01x0");
    expect(description).toContain('changed value is sampled by the <em>next</em> rising edge');
    expect(testbench).toContain('Inject X on addr');
    expect(solution).toContain('!$isunknown(addr)');
  });

  it('keeps immediate assertion examples aligned with their sampled FIFO cycles', () => {
    const description = read('sva/immediate-assert/description.html');
    const starter = read('sva/immediate-assert/tb.sv');
    const solution = read('sva/immediate-assert/fifo_checker.sol.sv');
    expect(description).toContain('cycle 1');
    expect(description).toContain('count=9</code> for <code>DEPTH=8');
    expect(description).toContain('assertion sees it on the following edge');
    expect(starter).toContain('Four deliberate violations');
    expect(solution).toContain('Write to full FIFO');
  });

  it('keeps sequence basics explicit about edge-counted delays', () => {
    const description = read('sva/sequence-basics/description.html');
    const starter = read('sva/sequence-basics/grant_check.sv');
    const solution = read('sva/sequence-basics/grant_check.sol.sv');
    expect(description).toContain('samples <code>cStart</code> and the first <code>req</code> term on the same rising edge');
    expect(description).toContain('clock-edge count, not a time literal');
    expect(description).toContain('second subsequent sampled edge');
    expect(starter).toContain('TODO: req is high, then 2 cycles later gnt is high');
    expect(solution).toContain('req ##2 gnt');
  });

  it('keeps implication examples explicit about edge-sensitive failures', () => {
    const description = read('sva/implication/description.html');
    const starter = read('sva/implication/implication.sv');
    const testbench = read('sva/implication/tb.sv');
    expect(description).toContain('ack</code> only at the request edge');
    expect(description).toContain('the supplied trace');
    expect(description).toContain('remove one of the two <code>ack = 1</code> assignments');
    expect(starter).toContain('TODO: use |->');
    expect(testbench).toContain('same-edge/next-edge trace');
  });

  it('keeps the typedef exercise aligned with its shared aliases', () => {
    const description = read('sv/typedef/description.html');
    const starter = read('sv/typedef/typedef_lab.sv');
    expect(description).toContain('typedef aliases');
    expect(description).toContain('one alias keeps width and intent together');
    expect(description).toContain('A package is a reusable boundary');
    expect(description).toContain('build the package once and reuse its type declarations');
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
    expect(starter).toContain('FAIL: %0d task/function checks were wrong');
    expect(description).toContain('starter testbench writes and reads one address');
    expect(description).toContain('solution repeats the same helpers at three addresses');
  });

  it('keeps the first UVM test aligned with its objection lifecycle', () => {
    const description = read('uvm/reporting/description.html');
    const starter = read('uvm/reporting/my_test.sv');
    const top = read('uvm/reporting/tb_top.sv');
    expect(description).toContain('raise_objection');
    expect(description).toContain('drop_objection');
    expect(description).toContain('`uvm_info(ID, msg, verbosity)');
    expect(description).toContain('`uvm_error(ID, msg)');
    expect(description).toContain('uses a warning for its demonstration');
    expect(starter).toContain('TODO 1: raise the objection');
    expect(starter).toContain('TODO 3: print a warning message using `uvm_warning');
    expect(starter).toContain('TODO 4: drop the objection');
    expect(starter).toContain('TODO 5: after the drop, print PASS only when the UVM error count is zero');
    expect(read('uvm/reporting/my_test.sol.sv')).toContain('get_severity_count(UVM_ERROR) == 0');
    expect(top).toContain('run_test("my_test")');
  });

  it('keeps functional coverage aligned with its collector TODOs and completion guard', () => {
    const description = read('uvm/covergroup/description.html');
    const starter = read('uvm/covergroup/mem_coverage.sv');
    const solution = read('uvm/covergroup/mem_coverage.sol.sv');
    const top = read('uvm/covergroup/tb_top.sv');
    expect(description).toContain('complete three things');
    expect(description).toContain('<strong>cp_addr</strong> coverpoint');
    expect(description).toContain('<strong>cp_we</strong> coverpoint');
    expect(description).toContain('empty covergroup has no bins');
    expect(description).toContain('coverage_ready = 1');
    expect(description).toContain('supplied check reaches 100%');
    expect(starter).toContain('TODO: add cp_addr coverpoint');
    expect(starter).toContain('TODO: add cp_we coverpoint');
    expect(starter).toContain('coverage_ready = 1');
    expect(starter).toContain('item = t;');
    expect(starter).toContain('mem_cg.sample();');
    expect(solution).toContain('bins addr[] = {[0:15]};');
    expect(solution).toContain('bins reads  = {0};');
    expect(solution).toContain('bins writes = {1};');
    expect(solution).toContain('bit coverage_ready = 1;');
    expect(top).toContain('get_severity_count(UVM_ERROR) == 0');
  });

  it('keeps cross coverage aligned with reserved-address instructions', () => {
    const description = read('uvm/cross-coverage/description.html');
    const starter = read('uvm/cross-coverage/mem_coverage.sv');
    const solution = read('uvm/cross-coverage/mem_coverage.sol.sv');
    const top = read('uvm/cross-coverage/tb_top.sv');
    expect(description).toContain('addr_x_we: cross cp_addr, cp_we;');
    expect(description).toContain('That single line creates 32 bins');
    expect(description).toContain('cross_ready');
    expect(description).toContain('remaining 30 bins are checked');
    expect(description).toContain('binsof</dfn></code> and <code>intersect');
    expect(description).toContain('reserved write addresses (14 and 15)');
    expect(starter).toContain('TODO 1: add addr_x_we cross');
    expect(starter).toContain('TODO 2: exclude the write combinations');
    expect(starter).toContain('while keeping the read combinations covered');
    expect(starter).toContain('TODO: set cross_ready = 1');
    expect(solution).toContain('addr_x_we: cross cp_addr, cp_we');
    expect(solution).toContain('ignore_bins no_write_reserved');
    expect(solution).toContain('binsof(cp_addr.addr) intersect {14, 15}');
    expect(solution).toContain('binsof(cp_we.writes)');
    expect(solution).toContain('bit cross_ready = 1;');
    expect(top).toContain('get_severity_count(UVM_ERROR) == 0');
  });

  it('keeps coverage-driven work aligned with its bounded loop', () => {
    const description = read('uvm/coverage-driven/description.html');
    const starter = read('uvm/coverage-driven/mem_test.sv');
    const solution = read('uvm/coverage-driven/mem_test.sol.sv');
    const top = read('uvm/coverage-driven/tb_top.sv');
    expect(description).toContain('while (&lt;covergroup&gt;.get_coverage()');
    expect(description).toContain('finite number of attempts');
    expect(description).toContain('raise_objection()');
    expect(description).toContain('drop_objection()');
    expect(description).toContain('Log the current coverage after each sequence run');
    expect(description).toContain('check the final percentage');
    expect(starter).toContain('TODO: replace the single seq.start() call with a while loop');
    expect(starter).toContain('keeps running sequences until mem_cg coverage reaches 100%');
    expect(starter).toContain('logging current coverage after each run');
    expect(starter).toContain('seq.start(env.agent.seqr);');
    expect(starter).toContain('FAIL: coverage only');
    expect(solution).toContain('while (env.cov.mem_cg.get_coverage() < 100.0)');
    expect(solution).toContain('`uvm_info("TEST", $sformatf("coverage = %.1f%%"');
    expect(solution).toContain('if (++iterations >= 50)');
    expect(solution).toContain('Reached iteration limit');
    expect(solution).toContain('FAIL: coverage target not reached');
    expect(top).toContain('get_severity_count(UVM_ERROR) == 0');
  });

  it('keeps constrained-random work aligned with its three constraint scopes', () => {
    const description = read('uvm/constrained-random/description.html');
    const item = read('uvm/constrained-random/mem_item.sv');
    const test = read('uvm/constrained-random/mem_test.sv');
    const top = read('uvm/constrained-random/tb_top.sv');
    expect(description).toContain('three ways to do that');
    expect(description).toContain('randomize() with { }');
    expect(description).toContain('returns zero when the active rules cannot be satisfied');
    expect(description).toContain('constraint_mode(0)');
    expect(item).toContain('TODO: add a dist weighting');
    expect(test).toContain('TODO: use randomize() with');
    expect(test).toContain('TODO: disable the named weighting constraint');
    expect(test).toContain('if (!item.randomize())');
    expect(read('uvm/constrained-random/mem_test.sol.sv')).toContain('if (!item.randomize() with');
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
    expect(events).toContain('catches a future post only');
    expect(events).toContain('the simpler <code>@(write_done)</code> is sufficient');
    expect(parameters).not.toContain('$bits(16) = 4');
    expect(parameters).toContain('IEEE 1800-2023 §20.6.2');
    expect(parameters).toContain('IEEE 1800-2023 §20.8.1');
    expect(parameters).toContain('replace the hardcoded dimensions');
    expect(parameters).toContain('$clog2(10)</code> is <code>4');
    expect(parameters).toContain('addresses 0 through 9 are valid');
    expect(enums).not.toContain('remove <code>state_bits</code>');
    expect(enums).toContain('do not add a separate <code>state_bits</code> port');
    expect(enums).toContain('IEEE 1800-2023 §6.19');
  });
});
