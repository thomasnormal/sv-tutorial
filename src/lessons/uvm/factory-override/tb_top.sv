import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"
`include "corner_mem_item.sv"
`include "mem_test_corner.sv"

module tb_top;
  initial begin
    run_test("mem_test_corner");
    if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0)
      $display("PASS");
  end
endmodule
