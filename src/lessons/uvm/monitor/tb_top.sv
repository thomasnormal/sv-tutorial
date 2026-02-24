import uvm_pkg::*;
`include "uvm_macros.svh"
`include "adder_item.sv"
`include "adder_driver.sv"
`include "adder_monitor.sv"
`include "adder_scoreboard.sv"
`include "adder_agent.sv"
`include "adder_seq.sv"

class monitor_test extends uvm_test;
  `uvm_component_utils(monitor_test)
  adder_agent      agent;
  adder_scoreboard scbd;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = adder_agent::type_id::create("agent", this);
    scbd  = adder_scoreboard::type_id::create("scbd", this);
  endfunction
  function void connect_phase(uvm_phase phase);
    agent.mon.ap.connect(scbd.analysis_export);
  endfunction
  task run_phase(uvm_phase phase);
    adder_seq seq = adder_seq::type_id::create("seq");
    phase.raise_objection(this);
    seq.start(agent.seqr);
    phase.drop_objection(this);
  endtask
endclass

module tb_top;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  logic clk = 0;
  always #5 clk = ~clk;
  adder_if aif(.clk(clk));
  adder dut(.a(aif.a), .b(aif.b), .sum(aif.sum), .carry(aif.carry));
  initial begin
    uvm_config_db #(virtual adder_if)::set(null, "uvm_test_top.*", "vif", aif);
    run_test("monitor_test");
  end
endmodule
