`ifndef SVT_UVM_ENV_MEM_SEQ_SV
`define SVT_UVM_ENV_MEM_SEQ_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"

class mem_seq extends uvm_sequence #(mem_item);
  `uvm_object_utils(mem_seq)
  int unsigned num_items = 8;
  function new(string name = "mem_seq"); super.new(name); endfunction
  task body();
    for (int unsigned i = 0; i < num_items; i++) begin
      mem_item item = mem_item::type_id::create("item");
      start_item(item);
      item.read_c.constraint_mode(0);
      void'(item.randomize() with {
        addr == ((i % (num_items / 2)) * 4);
      });
      item.we = (i < num_items / 2);
      if (item.we) item.wdata = 8'h20 + i;
      `uvm_info("SEQ", item.convert2string(), UVM_MEDIUM)
      finish_item(item);
    end
  endtask
endclass

`endif
