import uvm_pkg::*;
`include "uvm_macros.svh"

class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("TEST", "Hello from UVM!", UVM_LOW)
    `uvm_error("TEST", "Intentional error — simulation continues")
    phase.drop_objection(this);
  endtask
endclass
