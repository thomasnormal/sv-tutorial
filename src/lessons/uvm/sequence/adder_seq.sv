import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_seq extends uvm_sequence #(adder_item);
  `uvm_object_utils(adder_seq)
  int unsigned num_items = 5;
  function new(string name = "adder_seq"); super.new(name); endfunction
  task body();
    repeat (num_items) begin
      adder_item item = adder_item::type_id::create("item");
      // TODO: start_item(item);
      // TODO: void'(item.randomize());
      // TODO: `uvm_info("SEQ", item.convert2string(), UVM_MEDIUM)
      // TODO: finish_item(item);
    end
  endtask
endclass
