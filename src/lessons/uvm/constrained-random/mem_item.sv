import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_item extends uvm_sequence_item;
  `uvm_object_utils_begin(mem_item)
    `uvm_field_int(we,    UVM_ALL_ON)
    `uvm_field_int(addr,  UVM_ALL_ON)
    `uvm_field_int(wdata, UVM_ALL_ON)
  `uvm_object_utils_end

  rand bit         we;
  rand logic [3:0] addr;
  rand logic [7:0] wdata;
  logic [7:0]      rdata;

  // Bias toward boundary addresses: 0 and 15 are 3x more likely than interior
  constraint weighted_c {
    addr dist { [0:0] := 3, [1:14] := 1, [15:15] := 3 };
  }

  function new(string name = "mem_item"); super.new(name); endfunction

  function string convert2string();
    return we ? $sformatf("WR [%0d] = %0d", addr, wdata)
              : $sformatf("RD [%0d]", addr);
  endfunction
endclass
