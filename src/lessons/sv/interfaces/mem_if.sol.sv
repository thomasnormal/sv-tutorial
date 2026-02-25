interface mem_if (input logic clk);
  logic        we;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;

  modport initiator(output we, addr, wdata, input clk, rdata);
  modport target   (input  we, addr, wdata, output rdata);
endinterface
