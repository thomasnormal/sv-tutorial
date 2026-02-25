import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_seq extends uvm_sequence #(mem_item);
  `uvm_object_utils(mem_seq)
  int unsigned num_items = 8;
  function new(string name = "mem_seq"); super.new(name); endfunction
  task body();
    repeat (num_items) begin
      mem_item item = mem_item::type_id::create("item");
      start_item(item);
      void'(item.randomize() with { addr inside {0, 4, 8, 12}; });
      `uvm_info("SEQ", item.convert2string(), UVM_MEDIUM)
      finish_item(item);
    end
  endtask
endclass
