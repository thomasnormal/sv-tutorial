import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_seq extends uvm_sequence #(mem_item);
  `uvm_object_utils(mem_seq)
  function new(string name = "mem_seq"); super.new(name); endfunction
  task body();
    // Drive one read and one write at every address so all coverage bins are hit.
    for (int a = 0; a < 16; a++) begin
      for (int w = 0; w < 2; w++) begin
        mem_item item = mem_item::type_id::create("item");
        start_item(item);
        item.addr  = a[3:0];
        item.we    = w[0];
        item.wdata = $urandom_range(255, 0);
        `uvm_info("SEQ", item.convert2string(), UVM_MEDIUM)
        finish_item(item);
      end
    end
  endtask
endclass
