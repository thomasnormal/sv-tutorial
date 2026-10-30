`ifndef SVT_UVM_ENV_MEM_IF_SV
`define SVT_UVM_ENV_MEM_IF_SV

interface mem_if (input logic clk);
  logic        we;
  logic        valid = 1'b0;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;
  modport initiator(output valid, we, addr, wdata, input clk, rdata);
  modport target   (input  valid, we, addr, wdata, output rdata);
endinterface

`endif
