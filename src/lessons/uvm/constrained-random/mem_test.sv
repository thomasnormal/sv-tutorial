`ifndef SVT_UVM_CONSTRAINED_RANDOM_MEM_TEST_SV
`define SVT_UVM_CONSTRAINED_RANDOM_MEM_TEST_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"

class mem_test extends uvm_test;
  `uvm_component_utils(mem_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction

  task run_phase(uvm_phase phase);
    mem_item item = mem_item::type_id::create("item");
    phase.raise_objection(this);

    // ── Scenario 1: default weighted distribution ─────────────────────────────
    `uvm_info("TEST", "=== Scenario 1: weighted_c active ===", UVM_LOW)
    repeat (4) begin
      void'(item.randomize());
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end

    // ── Scenario 2: inline constraint — force boundary writes ──────────────────
    // TODO: use randomize() with { ... } to force writes (we==1) to boundary addresses (0 and 15)
    `uvm_info("TEST", "=== Scenario 2: inline constraint (boundary writes only) ===", UVM_LOW)
    begin
      int boundary_writes = 0;
      repeat (4) begin
        void'(item.randomize());  // replace with randomize() with { ... }
        `uvm_info("TEST", item.convert2string(), UVM_LOW)
        if (!(item.addr inside {0, 15}) || item.we !== 1'b1)
          `uvm_error("TEST", $sformatf("FAIL: expected boundary write, got addr=%0d we=%0b", item.addr, item.we))
        else
          boundary_writes++;
      end
      if (boundary_writes == 4)
        `uvm_info("TEST", "PASS: all 4 items were boundary writes", UVM_LOW)
      else
        `uvm_error("TEST", $sformatf("FAIL: only %0d/4 items were boundary writes", boundary_writes))
    end

    // ── Scenario 3: constraint_mode off — uniform distribution ────────────────
    // TODO: call constraint_mode(0) on weighted_c to disable it
    `uvm_info("TEST", "=== Scenario 3: weighted_c disabled ===", UVM_LOW)
    begin
      int interior = 0;
      int boundary = 0;
      repeat (160) begin
        void'(item.randomize());
        if (item.addr inside {[1:14]}) interior++;
        else boundary++;
      end
      if (interior >= 130)
        `uvm_info("TEST", $sformatf("PASS: %0d/160 items hit interior addresses (%0d boundary)", interior, boundary), UVM_LOW)
      else
        `uvm_error("TEST", $sformatf("FAIL: only %0d/160 items hit interior addresses (%0d boundary); weighted_c may still be active", interior, boundary))
    end

    phase.drop_objection(this);
  endtask
endclass

`endif
