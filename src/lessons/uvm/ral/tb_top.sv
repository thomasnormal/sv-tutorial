import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sram_reg_block.sv"
`include "mem_test_ral.sv"

module tb_top;
  initial begin
    uvm_root::get().set_finish_on_completion(0);
    run_test("mem_test_ral");
    if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0)
      $display("PASS");
    $finish;
  end
endmodule
