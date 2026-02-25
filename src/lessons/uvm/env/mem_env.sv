import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_env extends uvm_env;
  `uvm_component_utils(mem_env)
  mem_agent      agent;
  mem_scoreboard scbd;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // TODO: create the agent and scoreboard components using type_id::create
  endfunction
  function void connect_phase(uvm_phase phase);
    // TODO: connect the monitor's analysis port to the scoreboard's analysis export
  endfunction
endclass
