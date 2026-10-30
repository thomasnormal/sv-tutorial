import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_coverage extends uvm_subscriber #(mem_item);
  `uvm_component_utils(mem_coverage)

  mem_item item;
  bit cross_ready = 0;
  // TODO: set cross_ready = 1 after adding the cross and ignore_bins

  covergroup mem_cg;
    cp_addr: coverpoint item.addr {
      bins addr[] = {[0:15]};
    }
    cp_we: coverpoint item.we {
      bins reads  = {0};
      bins writes = {1};
    }
    // TODO 1: add addr_x_we cross of cp_addr and cp_we
    // TODO 2: exclude the write combinations for reserved addresses 14 and 15
    //         from this cross while keeping the read combinations covered.
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
    `uvm_info("COV", $sformatf("Cross coverage: %.1f%%", pct), UVM_LOW)
    if (cross_ready && pct == 100.0)
      `uvm_info("COV", "PASS: all required addr x op bins hit", UVM_LOW)
    else
      $fatal(0, $sformatf("Coverage %.1f%% - add the cross and reserved-address ignore bins", pct));
  endfunction
endclass
