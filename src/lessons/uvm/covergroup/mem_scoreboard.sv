import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(mem_scoreboard)
  uvm_analysis_imp #(mem_item, mem_scoreboard) analysis_export;
  logic [7:0] shadow [16];
  int pass_count, fail_count;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    analysis_export = new("analysis_export", this);
  endfunction
  function void write(mem_item item);
    if (item.we) begin
      shadow[item.addr] = item.wdata;
    end else begin
      if (item.rdata === shadow[item.addr]) begin
        pass_count++;
        `uvm_info("SCBD", {"PASS: ", item.convert2string()}, UVM_MEDIUM)
      end else begin
        fail_count++;
        `uvm_error("SCBD", $sformatf("FAIL: %s expected=%0d got=%0d",
          item.convert2string(), shadow[item.addr], item.rdata))
      end
    end
  endfunction
  function void report_phase(uvm_phase phase);
    `uvm_info("SCBD", $sformatf("Results: PASS=%0d FAIL=%0d", pass_count, fail_count), UVM_LOW)
  endfunction
endclass
