import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(mem_scoreboard)
  uvm_analysis_imp #(mem_item, mem_scoreboard) analysis_export;
  logic [7:0] shadow [16];  // shadow memory: tracks what the SRAM should contain
  int pass_count, fail_count;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    analysis_export = new("analysis_export", this);
  endfunction
  function void write(mem_item item);
    if (item.we) begin
      // TODO: update shadow memory at item.addr with item.wdata
    end else begin
      // TODO: compare item.rdata to shadow[item.addr]
      //       increment pass_count and log UVM_MEDIUM info on match
      //       increment fail_count and log a `uvm_error on mismatch
    end
  endfunction
  function void report_phase(uvm_phase phase);
    `uvm_info("SCBD", $sformatf("Results: PASS=%0d FAIL=%0d", pass_count, fail_count), UVM_LOW)
  endfunction
endclass
