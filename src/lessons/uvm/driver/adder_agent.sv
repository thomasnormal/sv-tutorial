import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_agent extends uvm_agent;
  `uvm_component_utils(adder_agent)
  adder_driver drv;
  uvm_sequencer #(adder_item) seqr;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    seqr = uvm_sequencer #(adder_item)::type_id::create("seqr", this);
    drv  = adder_driver::type_id::create("drv", this);
  endfunction
  function void connect_phase(uvm_phase phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction
endclass
