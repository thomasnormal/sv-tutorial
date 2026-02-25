import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"

class item_test extends uvm_test;
  `uvm_component_utils(item_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    mem_item item = mem_item::type_id::create("item");
    phase.raise_objection(this);
    // Default: read_c active — only reads
    `uvm_info("TEST", "=== reads only (read_c active) ===", UVM_LOW)
    repeat (5) begin
      void'(item.randomize());
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end
    // Disable read_c to allow writes
    `uvm_info("TEST", "=== reads + writes (read_c disabled) ===", UVM_LOW)
    item.read_c.constraint_mode(0);
    repeat (5) begin
      void'(item.randomize());
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end
    phase.drop_objection(this);
  endtask
endclass

module tb_top;
  initial run_test("item_test");
endmodule
