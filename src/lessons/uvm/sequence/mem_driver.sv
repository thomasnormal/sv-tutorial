import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_driver extends uvm_driver #(mem_item);
  `uvm_component_utils(mem_driver)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    mem_item req;
    forever begin
      seq_item_port.get_next_item(req);
      seq_item_port.item_done();
    end
  endtask
endclass
