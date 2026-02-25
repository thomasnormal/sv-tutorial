import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_agent extends uvm_agent;
  `uvm_component_utils(mem_agent)
  mem_driver drv;
  uvm_sequencer #(mem_item) seqr;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    seqr = uvm_sequencer #(mem_item)::type_id::create("seqr", this);
    drv  = mem_driver::type_id::create("drv", this);
  endfunction
  function void connect_phase(uvm_phase phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction
endclass
