import uvm_pkg::*;
`include "uvm_macros.svh"
`include "my_test.sv"

module tb_top;
  initial begin
    uvm_top.finish_on_completion = 0;
    run_test("my_test");
    $finish;
  end
endmodule
