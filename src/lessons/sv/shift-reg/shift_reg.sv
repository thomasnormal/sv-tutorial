// A four-bit serial-in, serial-out shift register.
// The register advances on each rising clock edge.
module shift_reg (
  input  logic       clk,
  input  logic       rst_n,
  input  logic       serial_in,
  output logic [3:0] q,
  output logic       serial_out
);
  always_ff @(posedge clk) begin
    // TODO: synchronously clear q and serial_out while rst_n is low.
    //       Otherwise expose the old MSB, then shift serial_in into q[0].
  end
endmodule
