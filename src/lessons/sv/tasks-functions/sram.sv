module sram #(parameter int DEPTH = 16, parameter int WIDTH = 8) (
  input  logic                      clk,    // clock: state updates on the rising edge
  input  logic                      we,     // write-enable: 1 = write wdata to mem[addr]
  input  logic [$clog2(DEPTH)-1:0] addr,   // address: selects which entry to access (0..DEPTH-1)
  input  logic [WIDTH-1:0]         wdata,  // write data: stored when we = 1
  output logic [WIDTH-1:0]         rdata   // read data: mem[addr] from the previous cycle
);
  logic [WIDTH-1:0] mem [0:DEPTH-1];
  always_ff @(posedge clk) begin
    if (we) mem[addr] <= wdata;
    rdata <= mem[addr];
  end
endmodule
