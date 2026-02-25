import uvm_pkg::*;
`include "uvm_macros.svh"

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

    // ── Scenario 2: inline override ───────────────────────────────────────────
    // TODO: use randomize() with { ... } to force writes to boundary addresses (0 and 15)
    `uvm_info("TEST", "=== Scenario 2: inline override ===", UVM_LOW)
    repeat (4) begin
      void'(item.randomize());  // replace with randomize() with { ... }
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end

    // ── Scenario 3: constraint_mode off ──────────────────────────────────────
    // TODO: disable weighted_c so addr draws uniformly from the full range
    `uvm_info("TEST", "=== Scenario 3: weighted_c disabled ===", UVM_LOW)
    repeat (4) begin
      void'(item.randomize());
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end

    phase.drop_objection(this);
  endtask
endclass
