module mux_reg #(parameter int W = 8) (
  input  logic         clk,
  input  logic         sel,
  input  logic [W-1:0] a, b,
  output logic [W-1:0] q
);
  logic [W-1:0] d;

  always_comb d = sel ? b : a;
  always_ff @(posedge clk) q <= d;

endmodule
