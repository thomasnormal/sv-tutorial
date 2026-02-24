import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_env extends uvm_env;
  `uvm_component_utils(adder_env)
  adder_agent      agent;
  adder_scoreboard scbd;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // TODO: agent = adder_agent::type_id::create("agent", this);
    // TODO: scbd  = adder_scoreboard::type_id::create("scbd",  this);
  endfunction
  function void connect_phase(uvm_phase phase);
    // TODO: agent.mon.ap.connect(scbd.analysis_export);
  endfunction
endclass
