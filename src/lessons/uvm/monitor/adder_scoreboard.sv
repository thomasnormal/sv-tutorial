import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(adder_scoreboard)
  uvm_analysis_imp #(adder_item, adder_scoreboard) analysis_export;
  int pass_count, fail_count;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    analysis_export = new("analysis_export", this);
  endfunction
  function void write(adder_item item);
    logic [8:0] expected = 9'(item.a) + 9'(item.b);
    // TODO: if actual matches expected, `uvm_info PASS, pass_count++
    //       else `uvm_error FAIL, fail_count++
  endfunction
  function void report_phase(uvm_phase phase);
    `uvm_info("SCBD", $sformatf("Results: PASS=%0d FAIL=%0d", pass_count, fail_count), UVM_LOW)
  endfunction
endclass
