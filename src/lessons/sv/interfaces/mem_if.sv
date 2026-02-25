// Bundle all SRAM signals into one reusable port.
interface mem_if (input logic clk);
  logic        we;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;

  // TODO: add modport initiator — testbench side: drives we/addr/wdata, reads rdata
  // TODO: add modport target   — SRAM side: reads commands, drives rdata
endinterface
