import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_test extends uvm_test;
  `uvm_component_utils(mem_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction

  task run_phase(uvm_phase phase);
    mem_item item = mem_item::type_id::create("item");
    phase.raise_objection(this);

    `uvm_info("TEST", "=== Scenario 1: weighted_c active ===", UVM_LOW)
    repeat (4) begin
      void'(item.randomize());
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end

    `uvm_info("TEST", "=== Scenario 2: inline override ===", UVM_LOW)
    repeat (4) begin
      void'(item.randomize() with { addr inside {0, 15}; we == 1; });
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end

    `uvm_info("TEST", "=== Scenario 3: weighted_c disabled ===", UVM_LOW)
    item.weighted_c.constraint_mode(0);
    repeat (4) begin
      void'(item.randomize());
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end

    phase.drop_objection(this);
  endtask
endclass
