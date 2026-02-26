import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"
`include "mem_driver.sv"
`include "mem_monitor.sv"
`include "mem_scoreboard.sv"
`include "mem_agent.sv"
`include "mem_seq.sv"
`include "mem_env.sv"

class monitor_test extends uvm_test;
  `uvm_component_utils(monitor_test)
  mem_env env;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = mem_env::type_id::create("env", this);
  endfunction
  task run_phase(uvm_phase phase);
    mem_seq seq = mem_seq::type_id::create("seq");
    phase.raise_objection(this);
    // Enable writes too
    seq.start(env.agent.seqr);
    phase.drop_objection(this);
  endtask
endclass

module tb_top;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  logic clk = 0;
  always #5 clk = ~clk;
  mem_if mif(.clk(clk));
  sram dut(.clk(mif.clk), .we(mif.we), .addr(mif.addr), .wdata(mif.wdata), .rdata(mif.rdata));
  initial begin
    uvm_config_db #(virtual mem_if)::set(null, "uvm_test_top.*", "vif", mif);
    run_test("monitor_test");
    if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0)
      $display("PASS");
  end
endmodule
