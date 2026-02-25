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
    int iterations = 0;
    phase.raise_objection(this);

    while (env.cov.mem_cg.get_coverage() < 100.0) begin
      mem_seq seq = mem_seq::type_id::create("seq");
      seq.start(env.agent.seqr);
      `uvm_info("TEST", $sformatf("coverage = %.1f%%",
        env.cov.mem_cg.get_coverage()), UVM_LOW)
      if (++iterations >= 50) begin
        `uvm_warning("TEST", "Reached iteration limit — a coverage bin may be unreachable")
        break;
      end
    end

    phase.drop_objection(this);
  endtask
endclass
