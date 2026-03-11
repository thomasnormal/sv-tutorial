import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_coverage extends uvm_subscriber #(mem_item);
  `uvm_component_utils(mem_coverage)

  mem_item item;

  covergroup mem_cg;
    // TODO: add cp_addr coverpoint with one bin per address (0–15)
    // TODO: add cp_we coverpoint with separate bins for reads and writes
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mem_cg = new();
  endfunction

  function void write(mem_item t);
    item = t;
    mem_cg.sample();
  endfunction

  function void report_phase(uvm_phase phase);
    real pct = mem_cg.get_coverage();
    `uvm_info("COV", $sformatf("Functional coverage: %.1f%%", pct), UVM_LOW)
    if (pct == 100.0)
      `uvm_info("COV", "PASS: all coverage bins hit", UVM_LOW)
    else
      $fatal(0, $sformatf("Coverage %.1f%% — implement coverpoints and this check in report_phase", pct))
  endfunction
endclass
