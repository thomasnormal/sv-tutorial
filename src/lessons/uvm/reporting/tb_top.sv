import uvm_pkg::*;
`include "uvm_macros.svh"
`include "my_test.sv"

module tb_top;
  initial run_test("my_test");
endmodule
