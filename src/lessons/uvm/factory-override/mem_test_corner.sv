import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_test_corner extends uvm_test;
  `uvm_component_utils(mem_test_corner)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // TODO: register the factory override so every mem_item::type_id::create()
    //       silently produces a corner_mem_item instead
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("TEST", "=== Before override: range_c avoids boundaries ===", UVM_LOW)
    repeat (4) begin
      mem_item item = mem_item::type_id::create("item");
      void'(item.randomize());
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end
    phase.drop_objection(this);
  endtask
endclass
