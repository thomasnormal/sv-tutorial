import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_seq extends uvm_sequence #(mem_item);
  `uvm_object_utils(mem_seq)
  int unsigned num_items = 8;
  function new(string name = "mem_seq"); super.new(name); endfunction
  task body();
    repeat (num_items) begin
      mem_item item = mem_item::type_id::create("item");
      // TODO: step 1 — request a slot from the sequencer (blocks until granted)
      // TODO: step 2 — randomize the item, constraining addr to every 4th address
      // TODO: step 3 — log the transaction with `uvm_info at UVM_MEDIUM verbosity
      // TODO: step 4 — hand the item to the driver (blocks until driver calls item_done)
    end
  endtask
endclass
