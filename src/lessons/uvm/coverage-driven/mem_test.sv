import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_test extends uvm_test;
  `uvm_component_utils(mem_test)
  mem_env env;

  function new(string name, uvm_component parent); super.new(name, parent); endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = mem_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    mem_seq seq = mem_seq::type_id::create("seq");
    phase.raise_objection(this);

    // TODO: replace the single seq.start() call with a while loop that
    //       keeps running sequences until mem_cg coverage reaches 100%,
    //       logging current coverage after each run

    seq.start(env.agent.seqr);
    if (env.cov.mem_cg.get_coverage() < 100.0)
      `uvm_error("COV", $sformatf("FAIL: coverage only %.1f%% after one sequence", env.cov.mem_cg.get_coverage()))
    phase.drop_objection(this);
  endtask
endclass
