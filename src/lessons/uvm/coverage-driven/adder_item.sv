import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_item extends uvm_sequence_item;
  `uvm_object_utils_begin(adder_item)
    `uvm_field_int(a,     UVM_ALL_ON)
    `uvm_field_int(b,     UVM_ALL_ON)
    `uvm_field_int(sum,   UVM_ALL_ON)
    `uvm_field_int(carry, UVM_ALL_ON)
  `uvm_object_utils_end
  rand logic [7:0] a, b;
  logic [7:0] sum;
  logic       carry;
  function new(string name = "adder_item"); super.new(name); endfunction
  function string convert2string();
    return $sformatf("a=%3d b=%3d => sum=%3d carry=%b", a, b, sum, carry);
  endfunction
endclass
