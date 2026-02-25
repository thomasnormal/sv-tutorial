import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"
`include "corner_mem_item.sv"
`include "mem_test_corner.sv"

module tb_top;
  initial run_test("mem_test_corner");
endmodule
