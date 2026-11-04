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

  it('keeps bounded reset proof aligned with its next-edge obligation', () => {
    const description = read('sva/formal-intro/description.html');
    const starter = read('sva/formal-intro/top.sv');
    const solution = read('sva/formal-intro/top.sol.sv');
    expect(description).toContain('<code>reset_event</code> matches');
    expect(description).toContain('<code>cnt == 0</code> must hold');
    expect(description).toContain('consequent starts one sampled edge after');
    expect(starter).toContain('TODO: replace the placeholder with a sampled reset event');
    expect(solution).toContain('reset_event |=> (cnt == 0)');
  });

  it('keeps clock-delay ranges explicit about inclusive endpoints', () => {
    const description = read('sva/clock-delay/description.html');
    const starter = read('sva/clock-delay/delay_check.sv');
    const testbench = read('sva/clock-delay/tb.sv');
    const solution = read('sva/clock-delay/delay_check.sol.sv');
    expect(description).toContain('<code>t+2</code> through <code>t+5</code>');
    expect(description).toContain('brackets in <code>##[2:5]</code> include both endpoints');
    expect(testbench).toContain('acknowledgement exactly two sampled edges later');
    expect(solution).toContain('##[2:5] delayed_ack');
  });

  it('keeps rose/fell windows aligned with sampled transitions', () => {
    const description = read('sva/rose-fell/description.html');
    const starter = read('sva/rose-fell/edge_check.sv');
    const testbench = read('sva/rose-fell/tb.sv');
    const solution = read('sva/rose-fell/edge_check.sol.sv');
    expect(description).toContain('<code>t+1</code>');
    expect(description).toContain('earliest legal rise');
    expect(description).toContain('keeping <code>ack</code> high from an earlier cycle');
    expect(starter).toContain('TODO: match one sampled rising edge on ack');
    expect(testbench).toContain('active-low chip-select edge');
    expect(solution).toContain('$fell(cs_n) |=> ##[0:1] ack_rise');
  });

  it('keeps request/ack windows explicit about non-overlap timing', () => {
    const description = read('sva/req-ack/description.html');
    const starter = read('sva/req-ack/req_ack.sv');
    const testbench = read('sva/req-ack/tb.sv');
    const solution = read('sva/req-ack/req_ack.sol.sv');
    expect(description).toContain('<code>t+1</code>');
    expect(description).toContain('latest legal acknowledgement');
    expect(description).toContain('an acknowledgement here is too late');
    expect(description).toContain('Use <code>$rose(ack)</code> when the protocol requires a new transition');
    expect(starter).toContain('TODO: match one sampled acknowledgement level');
    expect(testbench).toContain('third legal edge');
    expect(solution).toContain('$rose(req) |=> ##[0:2] ack_window');
  });

  it('keeps consecutive repetition aligned with contiguous samples', () => {
    const description = read('sva/consecutive-rep/description.html');
    const starter = read('sva/consecutive-rep/hold_check.sv');
    const testbench = read('sva/consecutive-rep/tb.sv');
    const solution = read('sva/consecutive-rep/hold_check.sol.sv');
    expect(description).toContain('<code>t+1</code>');
    expect(description).toContain('a 0 here breaks the run');
    expect(description).toContain('does not allow a gap or skip ahead');
    expect(description).toContain('<code>busy[*2:3]</code>');
    expect(starter).toContain('TODO: match three consecutive busy samples');
    expect(testbench).toContain('three consecutive busy samples');
    expect(solution).toContain('busy[*3]');
  });

  it('keeps goto repetition aligned with its third-match endpoint', () => {
    const description = read('sva/nonconsec-rep/description.html');
    const starter = read('sva/nonconsec-rep/multi_ack.sv');
    const testbench = read('sva/nonconsec-rep/tb.sv');
    const solution = read('sva/nonconsec-rep/multi_ack.sol.sv');
    expect(description).toContain('<code>t+5</code>');
    expect(description).toContain('gap allowed; the sequence remains open');
    expect(description).toContain('<code>##1 done</code>');
    expect(description).toContain('lets its sequence continue through later cycles');
    expect(starter).toContain('TODO: match three non-consecutive acknowledgement pulses');
    expect(testbench).toContain('Three separated acknowledgement pulses');
    expect(solution).toContain('ack[->3]');
    expect(solution).toContain('three_acks ##1 done');
  });

  it('keeps equal repetition aligned with its open completion window', () => {
    const description = read('sva/nonconsec-eq/description.html');
    const starter = read('sva/nonconsec-eq/multi_ack2.sv');
    const testbench = read('sva/nonconsec-eq/tb.sv');
    const solution = read('sva/nonconsec-eq/multi_ack2.sol.sv');
    expect(description).toContain('<code>t+5</code>');
    expect(description).toContain('can still extend through this trailing gap');
    expect(description).toContain('<code>##[0:$] done</code>');
    expect(description).toContain('delayed completion is legal here');
    expect(starter).toContain('TODO: match three non-consecutive acknowledgement pulses');
    expect(testbench).toContain('deliberately late done');
    expect(solution).toContain('ack[=3]');
    expect(solution).toContain('ack_burst ##[0:$] done');
  });

  it('keeps throughout timing independent of arbitrary MOSI data', () => {
    const description = read('sva/throughout/description.html');
    const starter = read('sva/throughout/spi_check.sv');
    const testbench = read('sva/throughout/tb.sv');
    const solution = read('sva/throughout/spi_check.sol.sv');
    expect(description).toContain('<code>t+1</code> through <code>t+8</code>');
    expect(description).toContain('each MOSI bit may be 0 or 1');
    expect(description).toContain('<code>1\'b1[*8]</code>');
    expect(description).toContain('without accidentally requiring <code>mosi</code> to be high');
    expect(starter).toContain('TODO: when cs_n falls');
    expect(testbench).toContain('eight-sample MOSI transfer');
    expect(solution).toContain('(!cs_n) throughout (1\'b1[*8])');
  });

  it('keeps sequence composition aligned with endpoint timing', () => {
    const description = read('sva/sequence-ops/description.html');
    const starter = read('sva/sequence-ops/bus_check.sv');
    const testbench = read('sva/sequence-ops/tb.sv');
    const solution = read('sva/sequence-ops/bus_check.sol.sv');
    expect(description).toContain('<code>t1</code> through <code>t3</code>');
    expect(description).toContain('both operands end together after four samples');
    expect(description).toContain('<code>done</code> has its own eight-cycle window');
    expect(description).toContain('when one complete sequence must fit inside another');
    expect(starter).toContain('TODO 1: use intersect');
    expect(starter).toContain('TODO 2: use and');
    expect(testbench).toContain('done arrives later in its own window');
    expect(solution).toContain('(valid[*4]) intersect (ready[*4])');
    expect(solution).toContain('(##[1:4] ready) and (##[1:8] done)');
  });

  it('keeps sequence formal arguments aligned with sampled readback timing', () => {
    const description = read('sva/seq-args/description.html');
    const starter = read('sva/seq-args/sram_check.sv');
    const testbench = read('sva/seq-args/tb.sv');
    const solution = read('sva/seq-args/sram_check.sol.sv');
    expect(description).toContain('<code>t+1</code>');
    expect(description).toContain('<code>read_txn(a,d)</code>');
    expect(description).toContain('substituted at each call site during elaboration');
    expect(description).toContain('same-edge guard');
    expect(starter).toContain('TODO: fill in the write_txn body');
    expect(testbench).toContain('Two writes and reads exercise both formal-argument call sites');
    expect(solution).toContain('write_txn(a, d) |=> (addr == a) |-> read_txn(a, d)');
    expect(solution).toContain('wr_rd_p(4\'hF, 8\'hFF)');
  });

  it('keeps stable-past stimulus ordered around the handshake edge', () => {
    const description = read('sva/stable-past/description.html');
    const starter = read('sva/stable-past/stable_check.sv');
    const testbench = read('sva/stable-past/tb.sv');
    const solution = read('sva/stable-past/stable_check.sol.sv');
    expect(description).toContain('<code>t1</code>');
    expect(description).toContain('<code>$stable(data)</code> passes');
    expect(description).toContain('raises <code>ready</code> while <code>data</code> is still <code>3C</code>');
    expect(description).toContain('Moving the data change one edge earlier would violate the property');
    expect(starter).toContain('TODO: while valid is high and ready is low');
    expect(testbench).toContain('ready = 1;');
    expect(testbench).toContain('data = 8\'hA5;');
    expect(solution).toContain('(valid && !ready) |=> $stable(data)');
  });

  it('keeps changed stimulus ordered around the final delta', () => {
    const description = read('sva/changed/description.html');
    const starter = read('sva/changed/toggle_check.sv');
    const testbench = read('sva/changed/tb.sv');
    const solution = read('sva/changed/toggle_check.sol.sv');
    expect(description).toContain('<code>t2</code>');
    expect(description).toContain('<code>$changed(data)</code> passes');
    expect(description).toContain('deasserts <code>update</code> together');
    expect(description).toContain('without opening another update obligation');
    expect(starter).toContain('TODO: when update is high');
    expect(testbench).toContain('data = 8\'h12; update = 0;');
    expect(solution).toContain('update |=> $changed(data)');
  });

  it('keeps disable-iff timing aligned with reset-gated attempts', () => {
    const description = read('sva/disable-iff/description.html');
    const starter = read('sva/disable-iff/reset_check.sv');
    const testbench = read('sva/disable-iff/tb.sv');
    const solution = read('sva/disable-iff/reset_check.sol.sv');
    expect(description).toContain('<code>t0</code>');
    expect(description).toContain('the request is disabled');
    expect(description).toContain('opens an acknowledgement obligation');
    expect(description).toContain('would abort that attempt immediately');
    expect(starter).toContain('TODO: match an acknowledgement on the sampled edge');
    expect(testbench).toContain('request during reset is ignored');
    expect(solution).toContain('@(posedge clk) disable iff (!rst_n)');
    expect(solution).toContain('req |=> ack_next');
  });

  it('keeps abort rejection windows aligned after non-overlap', () => {
    const description = read('sva/abort/description.html');
    const starter = read('sva/abort/abort_check.sv');
    const testbench = read('sva/abort/tb.sv');
    const solution = read('sva/abort/abort_check.sol.sv');
    expect(description).toContain('<code>t+1</code>');
    expect(description).toContain('<code>##0</code> is the earliest legal acknowledgement');
    expect(description).toContain('<code>##[0:3]</code>');
    expect(description).toContain('<code>accept_on(err)</code>');
    expect(starter).toContain('TODO: if err fires while ack_window is active');
    expect(testbench).toContain('late error arrives after the window');
    expect(solution).toContain('##[0:3] ack');
    expect(solution).toContain('start |=> reject_on(err) ack_window');
  });

  it('keeps cover-property timing distinct from assertion correctness', () => {
    const description = read('sva/cover-property/description.html');
    const starter = read('sva/cover-property/bus_check.sv');
    const testbench = read('sva/cover-property/tb.sv');
    const solution = read('sva/cover-property/bus_check.sol.sv');
    expect(description).toContain('<code>t+1</code>');
    expect(description).toContain('cover records the nonvacuous match');
    expect(description).toContain('If <code>frame_</code> never rises');
    expect(description).toContain('answers “did this scenario happen?”');
    expect(starter).toContain('TODO: assert ldpcheck');
    expect(starter).toContain('TODO: cover  ldpcheck');
    expect(testbench).toContain('frame pulse followed by ldp_ falling two sampled edges later');
    expect(solution).toContain('aP: assert property (ldpcheck)');
    expect(solution).toContain('cP: cover property (ldpcheck)');
  });

  it('keeps local-variable capture aligned with the delayed output edge', () => {
    const description = read('sva/local-vars/description.html');
    const starter = read('sva/local-vars/pipeline_check.sv');
    const testbench = read('sva/local-vars/tb.sv');
    const solution = read('sva/local-vars/pipeline_check.sol.sv');
    expect(description).toContain('<code>t0</code>');
    expect(description).toContain('<code>v=A5</code>');
    expect(description).toContain('<code>##2</code> is still counting');
    expect(description).toContain('its own <code>v</code>');
    expect(starter).toContain('TODO: capture in_data when valid_in fires');
    expect(testbench).toContain('three-edge output point');
    expect(solution).toContain('(valid_in, v = in_data) |=> ##2 (out_data == v)');
  });

  it('keeps onehot ownership checks aligned with idle handling', () => {
    const description = read('sva/onehot/description.html');
    const starter = read('sva/onehot/arbiter_check.sv');
    const testbench = read('sva/onehot/tb.sv');
    const solution = read('sva/onehot/arbiter_check.sol.sv');
    expect(description).toContain('<code>t0</code>');
    expect(description).toContain('<code>$onehot(grant)</code> passes');
    expect(description).toContain('separate <code>!any_grant</code> property');
    expect(description).toContain('use <code>$onehot0(grant)</code>');
    expect(starter).toContain('TODO: property grant_onehot_p');
    expect(testbench).toContain('Two legal ownership decisions followed by an idle bus');
    expect(solution).toContain('any_grant |-> $onehot(grant)');
    expect(solution).toContain('!any_grant |-> (grant == 4\'b0)');
  });

  it('keeps triggered endpoint timing aligned with the response window', () => {
    const description = read('sva/triggered/description.html');
    const starter = read('sva/triggered/trigger_check.sv');
    const testbench = read('sva/triggered/tb.sv');
    const solution = read('sva/triggered/trigger_check.sol.sv');
    expect(description).toContain('<code>t1</code>');
    expect(description).toContain('<code>s_req_done.triggered</code> is true here');
    expect(description).toContain('<code>##1 ack</code> is the earliest legal response');
    expect(description).toContain('an endpoint event, not a level');
    expect(starter).toContain('TODO: when s_req_done fires');
    expect(testbench).toContain('request leaves its busy phase');
    expect(solution).toContain('s_req_done.triggered |-> ##[1:3] ack');
  });

  it('keeps checker instances aligned with non-overlap timing', () => {
    const description = read('sva/checker/description.html');
    const starter = read('sva/checker/top.sv');
    const testbench = read('sva/checker/tb.sv');
    const solution = read('sva/checker/top.sol.sv');
    expect(description).toContain('<code>##[0:2]</code>');
    expect(description).toContain('<code>$stable(data)</code> compares this sample');
    expect(description).toContain('data change on the edge where <code>valid</code> first becomes inactive');
    expect(starter).toContain('TODO 1: when req fires');
    expect(starter).toContain('TODO 2: while valid is high');
    expect(testbench).toContain('independent channel timing');
    expect(testbench).toContain('ack1 = 0; ack2 = 1; valid2 = 0');
    expect(solution).toContain('req |=> ##[0:2] ack');
    expect(solution).toContain('valid |=> $stable(data)');
  });

  it('keeps bind attachment aligned with sampled counter timing', () => {
    const description = read('sva/bind/description.html');
    const target = read('sva/bind/counter.sv');
    const starter = read('sva/bind/counter_check.sv');
    const testbench = read('sva/bind/tb.sv');
    const solution = read('sva/bind/counter_check.sol.sv');
    expect(description).toContain('one checker instance for each target instance');
    expect(description).toContain('<code>t1</code>');
    expect(description).toContain('sampled values before the counter\'s nonblocking assignment');
    expect(description).toContain('every <code>counter</code> instance receives its own checker');
    expect(target).toContain('counter interface reused by the bound checker');
    expect(starter).toContain('TODO: when en is high, count increments on the following edge');
    expect(starter).toContain('TODO: bind counter to one counter_checker instance with named ports.');
    expect(testbench).toContain('counting: count=%0d (expect 4)');
    expect(solution).toContain('en |=> count == $past(count) + 8\'d1');
    expect(solution).toContain('bind counter counter_checker count_check_i');
    expect(solution).toContain('.count (count)');
  });

  it('keeps let reuse aligned with the guarded stability phases', () => {
    const description = read('sva/let/description.html');
    const starter = read('sva/let/let_check.sv');
    const testbench = read('sva/let/tb.sv');
    const solution = read('sva/let/let_check.sol.sv');
    expect(description).toContain('<code>t1</code>');
    expect(description).toContain('<code>$stable(data)</code> compares with the prior sample');
    expect(description).toContain('acceptance makes the guard false');
    expect(description).toContain('does not create procedural storage or a new module');
    expect(starter).toContain('TODO: define a parameterised let expression for a held data bus.');
    expect(starter).toContain('TODO: while valid is high and ready is low, data stays stable');
    expect(testbench).toContain('A ready handshake permits the next value to change.');
    expect(testbench).toContain('invalid bus: data=%h (expect 5C)');
    expect(solution).toContain('let hold_bus(value, active, accepted) =');
    expect(solution).toContain('@(posedge clk) hold_bus(data, valid, ready);');
    expect(solution).toContain('$stable(value)');
  });

  it('keeps formal assumptions aligned with reset and invariant timing', () => {
    const description = read('sva/formal-assume/description.html');
    const starter = read('sva/formal-assume/top.sv');
    const testbench = read('sva/formal-assume/tb.sv');
    const solution = read('sva/formal-assume/top.sol.sv');
    expect(description).toContain('<code>t0</code>');
    expect(description).toContain('<code>initial assume property</code> accepts this reset-starting world');
    expect(description).toContain('<code>disable iff (rst)</code> keeps <code>no_invalid</code> inactive');
    expect(description).toContain('assumptions on environment inputs such as <code>rst</code>');
    expect(starter).toContain('// TODO: assume property — rst is high at the first clock edge');
    expect(starter).toContain('// TODO: state 3 is never reached');
    expect(testbench).toContain('Simulation complete; click Verify');
    expect(solution).toContain('initial assume property (@(posedge clk) rst);');
    expect(solution).toContain('@(posedge clk) disable iff (rst) state != 2\'d3');
  });

  it('keeps liveness and safety aligned with their sampled endpoints', () => {
    const description = read('sva/always-eventually/description.html');
    const starter = read('sva/always-eventually/liveness.sv');
    const testbench = read('sva/always-eventually/tb.sv');
    const solution = read('sva/always-eventually/liveness.sol.sv');
    expect(description).toContain('<code>t1</code>');
    expect(description).toContain('<code>s_eventually lock</code> liveness obligation');
    expect(description).toContain('<code>always lock</code> continues to require ownership');
    expect(description).toContain('cannot prove the unbounded tail');
    expect(starter).toContain('// TODO: after reset de-asserts, lock must eventually become true');
    expect(starter).toContain('// TODO: once lock asserts, it must hold true at every future cycle');
    expect(testbench).toContain('lock trace: rst_n=%0b lock=%0b (expect 1,1)');
    expect(solution).toContain('$rose(rst_n) |-> s_eventually lock');
    expect(solution).toContain('lock |-> always lock');
  });

  it('keeps until variants aligned with the inclusive completion edge', () => {
    const description = read('sva/until/description.html');
    const starter = read('sva/until/hold_check.sv');
    const testbench = read('sva/until/tb.sv');
    const solution = read('sva/until/hold_check.sol.sv');
    expect(description).toContain('<code>t1</code>');
    expect(description).toContain('<code>valid s_until done</code>');
    expect(description).toContain('<code>until_with</code> includes the completion edge');
    expect(description).toContain('s_until</code> rejects that deadlock');
    expect(starter).toContain('TODO: valid must stay high until done arrives, and done must eventually arrive');
    expect(starter).toContain('TODO: from valid going high, data_ok must hold on every cycle including the done cycle');
    expect(testbench).toContain('completion: valid=%0b done=%0b data_ok=%0b (expect 1,1,1)');
    expect(solution).toContain('valid |-> valid s_until done');
    expect(solution).toContain('valid |-> data_ok until_with done');
  });

  it('keeps LEC identities aligned with exhaustive comparison', () => {
    const description = read('sva/lec/description.html');
    const starter = read('sva/lec/top.sv');
    const testbench = read('sva/lec/tb.sv');
    const solution = read('sva/lec/top.sol.sv');
    expect(description).toContain('<code>000</code> through <code>111</code>');
    expect(description).toContain('<code>sat</code> means the miter found a concrete counterexample input');
    expect(description).toContain('<code>unsat</code> means no input can distinguish');
    expect(description).toContain('enumerates the same eight input combinations');
    expect(starter).toContain('TODO 1: ~(a & b) = ? using De Morgan\'s law');
    expect(starter).toContain('TODO 2: ~(a | b) = ? using De Morgan\'s law');
    expect(starter).toContain('TODO 3: c ? a : b = ? using Boolean expansion');
    expect(testbench).toContain('for (int i = 0; i < 8; i++)');
    expect(testbench).toContain('TODO: replace the three Impl placeholders');
    expect(solution).toContain('assign nand_y = ~a | ~b;');
    expect(solution).toContain('assign nor_y  = ~a & ~b;');
    expect(solution).toContain('assign mux_y  = a_when_c | b_when_not_c;');
  });

  it('keeps followed-by operators aligned with sequence endpoints', () => {
    const description = read('sva/followed-by/description.html');
    const starter = read('sva/followed-by/followed_by.sv');
    const testbench = read('sva/followed-by/tb.sv');
    const solution = read('sva/followed-by/followed_by.sol.sv');
    expect(description).toContain('<code>2</code>');
    expect(description).toContain('<code>#-#</code> checks <code>data_ok</code> on this same endpoint');
    expect(description).toContain('<code>#=#</code> checks one sampled edge after the endpoint');
    expect(description).toContain('if the three-event burst never matches');
    expect(starter).toContain('TODO: describe a start followed by two beat cycles');
    expect(starter).toContain('TODO: require data_ok when burst_read ends (overlapped)');
    expect(starter).toContain('TODO: require data_ok one cycle after burst_read ends (non-overlapped)');
    expect(testbench).toContain('cycle 2 (sequence endpoint)');
    expect(testbench).toContain('cycle 3 (next sample)');
    expect(solution).toContain('burst_start ##1 burst_beat ##1 burst_beat;');
    expect(solution).toContain('burst_read #-# data_ok');
    expect(solution).toContain('burst_read #=# data_ok');
    expect(solution).toContain('burst_start |=> data_ok');
  });

  it('keeps RTL-to-gates timing aligned with mux and register behavior', () => {
    const description = read('rtl/rtl-to-gates/description.html');
    const starter = read('rtl/rtl-to-gates/mux_reg.sv');
    const testbench = read('rtl/rtl-to-gates/tb.sv');
    const solution = read('rtl/rtl-to-gates/mux_reg.sol.sv');
    expect(description).toContain('<code>t1+</code>');
    expect(description).toContain('the combinational mux drives <code>d=A5</code>');
    expect(description).toContain('the register captures <code>5A</code>');
    expect(description).toContain('one-cycle separation is the pipeline stage');
    expect(starter).toContain('TODO: use always_comb to drive d');
    expect(starter).toContain('TODO: use always_ff to register d into q');
    expect(testbench).toContain('sel = 0;');
    expect(testbench).toContain('sel = 1;');
    expect(solution).toContain('always_comb d = sel ? b : a;');
    expect(solution).toContain('always_ff @(posedge clk) q <= d;');
  });

  it('keeps synthesis gotchas aligned with complete decoder coverage', () => {
    const description = read('rtl/synthesis-gotchas/description.html');
    const starter = read('rtl/synthesis-gotchas/decoder.sv');
    const testbench = read('rtl/synthesis-gotchas/tb.sv');
    const solution = read('rtl/synthesis-gotchas/decoder.sol.sv');
    expect(description).toContain('<code>sel=11</code>');
    expect(description).toContain('<code>y=1000</code>');
    expect(description).toContain('the added branch prevents an inferred latch');
    expect(description).toContain('every 2-bit input a combinational result');
    expect(starter).toContain('WARNING: this module currently infers a latch');
    expect(starter).toContain('TODO: this case statement is missing a branch for 2\'b11.');
    expect(starter).toContain('Then change `case` to `unique case`');
    expect(testbench).toContain('sel = 2\'b11; #5;');
    expect(testbench).toContain('FAIL 11: got %04b (latch?)');
    expect(solution).toContain('unique case (sel)');
    expect(solution).toContain('2\'b11: y = 4\'b1000;');
  });

  it('keeps the MLIR intro aligned with its SSA adder data flow', () => {
    const description = read('mlir/intro/description.html');
    const source = read('mlir/intro/adder.mlir');
    const testbench = read('mlir/intro/adder_tb.mlir');
    expect(description).toContain('<code>%0 = comb.add %a, %b : i8</code>');
    expect(description).toContain('<code>5 + 3 = 8</code>');
    expect(description).toContain('There is no procedural ordering between the operations');
    expect(source).toContain('hw.module @adder(in %a : i8, in %b : i8, out sum : i8)');
    expect(source).toContain('%0 = comb.add %a, %b : i8');
    expect(source).toContain('hw.output %0 : i8');
    expect(testbench).toContain('hw.instance "dut" @adder');
    expect(testbench).toContain('sim.proc.print');
    expect(testbench).toContain('sim.terminate success, quiet');
  });

  it('keeps the comb dialect aligned with priority mux data flow', () => {
    const description = read('mlir/comb/description.html');
    const source = read('mlir/comb/priority_enc.mlir');
    const testbench = read('mlir/comb/priority_enc_tb.mlir');
    expect(description).toContain('<code>%g01 = comb.mux %req1, %c1, %c0</code>');
    expect(description).toContain('<code>%grant = comb.mux %req3, %c3, %g012</code>');
    expect(description).toContain('changing <code>req</code> recomputes the entire graph');
    expect(source).toContain('hw.module @priority_enc(in %req : i4');
    expect(source).toContain('%req1 = comb.extract %req from 1 : (i4) -> i1');
    expect(source).toContain('%g012  = comb.mux %req2, %c2, %g01');
    expect(source).toContain('%valid = comb.or %req0, %req1, %req2, %req3 : i1');
    expect(testbench).toContain('%req   = hw.constant 2 : i4');
    expect(testbench).toContain('sim.fmt.literal "PASS\\0A"');
  });

  it('keeps the seq dialect aligned with clocked register timing', () => {
    const description = read('mlir/seq/description.html');
    const source = read('mlir/seq/sram_core.mlir');
    const testbench = read('mlir/seq/sram_core_tb.mlir');
    expect(description).toContain('<code>5 ns</code>');
    expect(description).toContain('<code>q</code> becomes <code>0x42</code>');
    expect(description).toContain('one cycle after the address is sampled');
    expect(source).toContain('seq.hlmem @sram_core %clk, %false : <16xi8>');
    expect(source).toContain('seq.write %mem[%addr] %wdata wren %we');
    expect(source).toContain('%rdata      = seq.compreg %rdata_comb, %clk : i8');
    expect(source).toContain('%q = seq.compreg %d, %clk : i8');
    expect(testbench).toContain('%c42    = hw.constant 66  : i8');
    expect(testbench).toContain('%c11ns  = hw.constant 11000000');
    expect(testbench).toContain('sim.fmt.literal "PASS\\0A"');
  });

  it('keeps lowering stages aligned with the two output paths', () => {
    const description = read('mlir/lowering/description.html');
    const source = read('mlir/lowering/lowering.mlir');
    const testbench = read('mlir/lowering/lowering_tb.mlir');
    expect(description).toContain('<code>%q = seq.compreg %d, %clk : i8</code>');
    expect(description).toContain('<code>sv.reg</code> + <code>sv.always</code> + <code>sv.passign</code>');
    expect(description).toContain('<code>verif.bmc</code> → SMTLIB → Z3');
    expect(description).toContain('Run lowers toward executable SystemVerilog');
    expect(source).toContain('hw.module @dff_before');
    expect(source).toContain('%q_reg = sv.reg name "q"');
    expect(source).toContain('sv.always posedge %clk');
    expect(source).toContain('q <= d;');
    expect(source).toContain('LowerHWtoBMC');
    expect(testbench).toContain('@dff_before');
    expect(testbench).toContain('%cAA     = hw.constant 170');
    expect(testbench).toContain('sim.fmt.literal "PASS\\0A"');
  });

  it('keeps the first cocotb lesson aligned with VPI phase timing', () => {
    const description = read('cocotb/first-test/description.html');
    const rtl = read('cocotb/first-test/adder.sv');
    const solution = read('cocotb/first-test/adder.sol.sv');
    const python = read('cocotb/first-test/test_adder.py');
    expect(description).toContain('<code>ReadWrite()</code>');
    expect(description).toContain('<code>Timer(1, units="ns")</code>');
    expect(description).toContain('<code>ReadOnly()</code>');
    expect(description).toContain('<code>15 + 15 = 30</code>');
    expect(description).toContain('Complete the missing assignment in the <code>always @(*)</code> block');
    expect(rtl).toContain('// TODO: compute X as the sum of A and B');
    expect(solution).toContain('always @(*) X = A + B;');
    expect(python).toContain('await Timer(1, units="fs")');
    expect(python).toContain('await ReadWrite()');
    expect(python).toContain('await ReadOnly()');
    expect(python).toContain('check(dut, 15, 15, 30)');
  });

  it('keeps cocotb clock timing aligned with synchronous counter reset', () => {
    const description = read('cocotb/clock-and-timing/description.html');
    const rtl = read('cocotb/clock-and-timing/counter.sv');
    const solution = read('cocotb/clock-and-timing/counter.sol.sv');
    const python = read('cocotb/clock-and-timing/test_counter.py');
    expect(description).toContain('five rising edges increment <code>count</code> to <code>5</code>');
    expect(description).toContain('the next posedge clears the count back to <code>0</code>');
    expect(description).toContain('Reset is synchronous');
    expect(rtl).toContain('// TODO: reset count to 0 when rst is high, otherwise increment');
    expect(solution).toContain('if (rst) count <= 4\'d0;');
    expect(solution).toContain('else     count <= count + 4\'d1;');
    expect(python).toContain('async def clock_cycle(dut, period_ns=10):');
    expect(python).toContain('await Timer(period_ns // 2, units="ns")');
    expect(python).toContain('for _ in range(5):');
    expect(python).toContain('assert dut.count.value == 5');
  });

  it('keeps cocotb edge triggers aligned with register sampling', () => {
    const description = read('cocotb/edge-triggers/description.html');
    const rtl = read('cocotb/edge-triggers/reg_en.sv');
    const solution = read('cocotb/edge-triggers/reg_en.sol.sv');
    const python = read('cocotb/edge-triggers/test_reg_en.py');
    expect(description).toContain('first <code>RisingEdge</code>');
    expect(description).toContain('<code>ReadOnly</code> observes the committed NBA');
    expect(description).toContain('two <code>ClockCycles</code> later');
    expect(description).toContain('safe half-cycle to change inputs');
    expect(rtl).toContain('// TODO: clear q on reset, otherwise load d when en is high.');
    expect(solution).toContain('if (rst)      q <= 4\'d0;');
    expect(solution).toContain('else if (en)  q <= d;');
    expect(python).toContain('Clock(dut.clk, 10, unit="ns")');
    expect(python).toContain('await FallingEdge(dut.clk)');
    expect(python).toContain('await ClockCycles(dut.clk, 2)');
    expect(python).toContain('assert dut.q.value == 0x4');
  });

  it('keeps cocotb ClockCycles patterns aligned with pulse counts', () => {
    const description = read('cocotb/clockcycles-patterns/description.html');
    const rtl = read('cocotb/clockcycles-patterns/pulse_counter.sv');
    const solution = read('cocotb/clockcycles-patterns/pulse_counter.sol.sv');
    const python = read('cocotb/clockcycles-patterns/test_pulse_counter.py');
    expect(description).toContain('<code>1</code> (hold)');
    expect(description).toContain('<code>5</code></td></tr>');
    expect(description).toContain('changes <code>pulse</code> after a <code>FallingEdge</code>');
    expect(description).toContain('initial and final <code>ClockCycles(..., 1)</code>');
    expect(rtl).toContain('// TODO: clear on reset, otherwise increment when pulse is high.');
    expect(solution).toContain('if (rst)        count <= 4\'d0;');
    expect(solution).toContain('else if (pulse) count <= count + 4\'d1;');
    expect(python).toContain('pattern = [1, 0, 1, 1, 0, 0, 1, 1]');
    expect(python).toContain('await ClockCycles(dut.clk, 1)');
    expect(python).toContain('await FallingEdge(dut.clk)');
    expect(python).toContain('expected = (expected + 1) & 0xF');
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
