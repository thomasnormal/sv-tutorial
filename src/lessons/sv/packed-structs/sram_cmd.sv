import mem_pkg::*;

module sram_cmd (
  input  logic     clk,
  input  mem_cmd_t cmd,
  output logic [7:0] rdata
);
  logic [7:0] mem [0:15];

  always_ff @(posedge clk) begin
    if (cmd.we) mem[cmd.addr] <= cmd.wdata;
    rdata <= mem[cmd.addr];
  end
endmodule
