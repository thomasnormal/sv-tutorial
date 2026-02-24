import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_test extends uvm_test;
  `uvm_component_utils(adder_test)
  adder_env env;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = adder_env::type_id::create("env", this);
  endfunction
  task run_phase(uvm_phase phase);
    adder_seq seq = adder_seq::type_id::create("seq");
    phase.raise_objection(this);
    seq.start(env.agent.seqr);
    phase.drop_objection(this);
  endtask
endclass
