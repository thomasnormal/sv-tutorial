import uvm_pkg::*;
`include "uvm_macros.svh"
`include "my_test.sv"

module tb_top;
  initial begin
    run_test("my_test");
    if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0)
      $display("PASS");
  end
endmodule
