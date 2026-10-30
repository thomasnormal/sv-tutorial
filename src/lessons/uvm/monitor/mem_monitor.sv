`ifndef SVT_UVM_MONITOR_MEM_MONITOR_SV
`define SVT_UVM_MONITOR_MEM_MONITOR_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"
`include "mem_if.sv"

class mem_monitor extends uvm_monitor;
  `uvm_component_utils(mem_monitor)
  virtual mem_if vif;
  uvm_analysis_port #(mem_item) ap;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
    if (!uvm_config_db #(virtual mem_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found")
  endfunction
  task run_phase(uvm_phase phase);
    mem_item item;
    forever begin
      @(posedge vif.clk);
      if (vif.valid) begin
        item = mem_item::type_id::create("item");
        item.we    = vif.we;
        item.addr  = vif.addr;
        item.wdata = vif.wdata;
        item.rdata = vif.rdata;
        ap.write(item);
      end
    end
  endtask
endclass

`endif
