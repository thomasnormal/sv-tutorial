import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"
`include "mem_test.sv"

module tb_top;
  initial begin
    run_test("mem_test");
    if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0)
      $display("PASS");
  end
endmodule
