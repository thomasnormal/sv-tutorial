import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_seq extends uvm_sequence #(mem_item);
  `uvm_object_utils(mem_seq)
  function new(string name = "mem_seq"); super.new(name); endfunction
  task body();
    // Read every address (covers all cp_addr bins and cp_we reads bin).
    // Write to non-reserved addresses 0–13 (covers cp_we writes bin and all
    // required addr×we cross bins; writes to 14–15 are ignore_bins).
    for (int a = 0; a < 16; a++) begin
      mem_item item = mem_item::type_id::create("item");
      start_item(item);
      item.addr = a[3:0]; item.we = 0;
      `uvm_info("SEQ", item.convert2string(), UVM_MEDIUM)
      finish_item(item);

      if (a < 14) begin
        item = mem_item::type_id::create("item");
        start_item(item);
        item.addr = a[3:0]; item.we = 1; item.wdata = $urandom_range(255, 0);
        `uvm_info("SEQ", item.convert2string(), UVM_MEDIUM)
        finish_item(item);
      end
    end
  endtask
endclass
