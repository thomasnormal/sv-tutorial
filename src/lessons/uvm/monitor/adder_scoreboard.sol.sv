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
    if (item.sum === expected[7:0] && item.carry === expected[8]) begin
      pass_count++;
      `uvm_info("SCBD", {"PASS: ", item.convert2string()}, UVM_MEDIUM)
    end else begin
      fail_count++;
      `uvm_error("SCBD", $sformatf("FAIL: %s -- expected sum=%0d carry=%b",
        item.convert2string(), expected[7:0], expected[8]))
    end
  endfunction
  function void report_phase(uvm_phase phase);
    `uvm_info("SCBD", $sformatf("Results: PASS=%0d FAIL=%0d", pass_count, fail_count), UVM_LOW)
  endfunction
endclass
