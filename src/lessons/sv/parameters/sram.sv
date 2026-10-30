// TODO: add a parameter block — one parameter for number of entries (DEPTH) and one for bits per entry (WIDTH)
module sram (
  input  logic       clk,
  input  logic       we,
  input  logic [3:0] addr,   // TODO: use DEPTH to compute the correct address width
  input  logic [7:0] wdata,  // TODO: use WIDTH for the data width
  output logic [7:0] rdata   // TODO: use WIDTH for the data width
);
  localparam int LAST_ADDR = 15; // TODO: derive the last index from DEPTH
  logic [7:0] mem [0:LAST_ADDR]; // TODO: use WIDTH for each stored element

  always_ff @(posedge clk) begin
    if (we) mem[addr] <= wdata;
    rdata <= mem[addr];
  end
endmodule
