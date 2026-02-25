import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_item extends uvm_sequence_item;
  `uvm_object_utils_begin(mem_item)
    // TODO: add uvm_field_int macros for all four fields (we, addr, wdata, rdata)
  `uvm_object_utils_end

  // TODO: declare rand fields for we (1 bit), addr (4 bits), wdata (8 bits)
  // TODO: declare rdata (8 bits) as non-random — it is captured from the DUT output

  // TODO: add a constraint that makes all operations reads by default

  function new(string name = "mem_item");
    super.new(name);
  endfunction

  function string convert2string();
    return we ? $sformatf("WR [%0d] = %0d", addr, wdata)
              : $sformatf("RD [%0d]", addr);
  endfunction
endclass
