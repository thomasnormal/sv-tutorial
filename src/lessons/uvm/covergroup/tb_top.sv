import uvm_pkg::*;
`include "uvm_macros.svh"
`include "adder_item.sv"
`include "adder_driver.sv"
`include "adder_monitor.sv"
`include "adder_scoreboard.sv"
`include "adder_coverage.sv"
`include "adder_agent.sv"
`include "adder_seq.sv"
`include "adder_env.sv"
`include "adder_test.sv"

module tb_top;
  logic clk = 0;
  always #5 clk = ~clk;
  adder_if aif(.clk(clk));
  adder dut(.a(aif.a), .b(aif.b), .sum(aif.sum), .carry(aif.carry));
  initial begin
    uvm_config_db #(virtual adder_if)::set(null, "uvm_test_top.*", "vif", aif);
    run_test("adder_test");
  end
endmodule
