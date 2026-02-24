import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_seq extends uvm_sequence #(adder_item);
  `uvm_object_utils(adder_seq)
  int unsigned num_items = 8;
  function new(string name = "adder_seq"); super.new(name); endfunction
  task body();
    repeat (num_items) begin
      adder_item item = adder_item::type_id::create("item");
      start_item(item); void'(item.randomize()); finish_item(item);
    end
  endtask
endclass
