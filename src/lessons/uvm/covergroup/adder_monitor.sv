import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_monitor extends uvm_monitor;
  `uvm_component_utils(adder_monitor)
  virtual adder_if vif;
  uvm_analysis_port #(adder_item) ap;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
    if (!uvm_config_db #(virtual adder_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found")
  endfunction
  task run_phase(uvm_phase phase);
    adder_item item;
    @(posedge vif.clk);
    forever begin
      @(posedge vif.clk);
      item = adder_item::type_id::create("item");
      item.a = vif.a; item.b = vif.b;
      item.sum = vif.sum; item.carry = vif.carry;
      ap.write(item);
    end
  endtask
endclass
