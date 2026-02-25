import uvm_pkg::*;
`include "uvm_macros.svh"

class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    // TODO 1: raise the objection so simulation waits for us
    // TODO 2: print an info message using `uvm_info with verbosity UVM_LOW
    // TODO 3: print an error message using `uvm_error (simulation should continue)
    // TODO 4: drop the objection to let simulation end
  endtask
endclass
