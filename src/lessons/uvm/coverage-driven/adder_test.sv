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

    // TODO: Replace the single seq.start() call below with a while loop that
    //       keeps running sequences until adder_cg coverage reaches 100%.
    //
    //       while (env.cov.adder_cg.get_coverage() < 100.0) begin
    //         seq = adder_seq::type_id::create("seq");
    //         seq.start(env.agent.seqr);
    //         `uvm_info("TEST", $sformatf("coverage = %.1f%%",
    //           env.cov.adder_cg.get_coverage()), UVM_LOW)
    //       end

    seq.start(env.agent.seqr);

    phase.drop_objection(this);
  endtask
endclass
