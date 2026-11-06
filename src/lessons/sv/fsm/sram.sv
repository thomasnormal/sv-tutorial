module sram #(parameter int DEPTH = 16, parameter int WIDTH = 8) (
  input  logic                      clk,
  input  logic                      we,
  input  logic [$clog2(DEPTH)-1:0] addr,
  input  logic [WIDTH-1:0]         wdata,
  output logic [WIDTH-1:0]         rdata
);
  // Memory contents are unknown until a write.  Keeping the array free of a
  // declaration initializer lets its only writer remain the clocked process.
  logic [WIDTH-1:0] mem [0:DEPTH-1];
  always_ff @(posedge clk) begin
    if (we) mem[addr] <= wdata;
  end
  assign rdata = mem[addr];
endmodule
