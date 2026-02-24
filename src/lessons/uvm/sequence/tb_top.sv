import uvm_pkg::*;
`include "uvm_macros.svh"
`include "adder_item.sv"
`include "adder_driver.sv"
`include "adder_agent.sv"
`include "adder_seq.sv"

class seq_test extends uvm_test;
  `uvm_component_utils(seq_test)
  adder_agent agent;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = adder_agent::type_id::create("agent", this);
  endfunction
  task run_phase(uvm_phase phase);
    adder_seq seq = adder_seq::type_id::create("seq");
    phase.raise_objection(this);
    seq.start(agent.seqr);
    phase.drop_objection(this);
  endtask
endclass

module tb_top;
  initial run_test("seq_test");
endmodule
