`ifndef SVT_UVM_ENV_MEM_DRIVER_SV
`define SVT_UVM_ENV_MEM_DRIVER_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"
`include "mem_if.sv"

class mem_driver extends uvm_driver #(mem_item);
  `uvm_component_utils(mem_driver)
  virtual mem_if vif;
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(virtual mem_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found")
  endfunction
  task run_phase(uvm_phase phase);
    mem_item req;
    forever begin
      seq_item_port.get_next_item(req);
      @(posedge vif.clk);
      vif.valid <= 1'b1;
      vif.we    <= req.we;
      vif.addr  <= req.addr;
      vif.wdata <= req.wdata;
      @(posedge vif.clk);
      req.rdata = vif.rdata;
      vif.valid <= 1'b0;
      seq_item_port.item_done();
    end
  endtask
endclass

`endif
