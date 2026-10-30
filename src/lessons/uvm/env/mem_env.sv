`ifndef SVT_UVM_ENV_MEM_ENV_SV
`define SVT_UVM_ENV_MEM_ENV_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_agent.sv"
`include "mem_scoreboard.sv"
`include "mem_coverage.sv"

class mem_env extends uvm_env;
  `uvm_component_utils(mem_env)
  mem_agent      agent;
  mem_scoreboard scbd;
  mem_coverage   cov;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // TODO: create agent, scbd, and cov using type_id::create("name", this)
  endfunction
  function void connect_phase(uvm_phase phase);
    // TODO: connect agent.mon.ap to both scbd.analysis_export and cov.analysis_export
    //       (the same port can feed multiple subscribers — no change to the monitor needed)
  endfunction
endclass

`endif
