import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_item extends uvm_sequence_item;
  `uvm_object_utils_begin(adder_item)
    // TODO: `uvm_field_int(a, UVM_ALL_ON)
    // TODO: `uvm_field_int(b, UVM_ALL_ON)
  `uvm_object_utils_end

  // TODO: rand logic [7:0] a, b;

  // TODO: constraint small_c { a < 100; b < 100; }

  function new(string name = "adder_item");
    super.new(name);
  endfunction

  function string convert2string();
    return $sformatf("a=%3d b=%3d", a, b);
  endfunction
endclass
