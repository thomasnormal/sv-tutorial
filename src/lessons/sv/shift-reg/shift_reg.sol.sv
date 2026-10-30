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
    if (!rst_n) begin
      q          <= 4'b0000;
      serial_out <= 1'b0;
    end else begin
      serial_out <= q[3];
      q          <= {q[2:0], serial_in};
    end
  end
endmodule
