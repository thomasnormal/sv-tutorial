import uvm_pkg::*;
`include "uvm_macros.svh"

class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    // TODO 1: phase.raise_objection(this);
    // TODO 2: `uvm_info("TEST", "Hello from UVM!", UVM_LOW)
    // TODO 3: `uvm_error("TEST", "Intentional error — simulation continues")
    // TODO 4: phase.drop_objection(this);
  endtask
endclass
