import uvm_pkg::*;
`include "uvm_macros.svh"

// Stub driver — acknowledges items without a real DUT
class adder_driver extends uvm_driver #(adder_item);
  `uvm_component_utils(adder_driver)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    adder_item req;
    forever begin
      seq_item_port.get_next_item(req);
      #10;
      seq_item_port.item_done();
    end
  endtask
endclass
