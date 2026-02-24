import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_driver extends uvm_driver #(adder_item);
  `uvm_component_utils(adder_driver)
  virtual adder_if vif;
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(virtual adder_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found")
  endfunction
  task run_phase(uvm_phase phase);
    adder_item req;
    forever begin
      seq_item_port.get_next_item(req);
      @(posedge vif.clk);
      vif.a <= req.a;
      vif.b <= req.b;
      @(posedge vif.clk);
      seq_item_port.item_done();
    end
  endtask
endclass
