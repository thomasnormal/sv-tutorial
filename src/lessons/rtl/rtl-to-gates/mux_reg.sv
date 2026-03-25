// A pipeline stage: a multiplexer feeding a flip-flop.
// This is the fundamental building block of all RTL datapaths.
module mux_reg #(parameter int W = 8) (
  input  logic         clk,
  input  logic         sel,
  input  logic [W-1:0] a, b,
  output logic [W-1:0] q
);
  logic [W-1:0] d;

  // TODO: use always_comb to drive d:
  //       when sel=0 output a, when sel=1 output b

  // TODO: use always_ff to register d into q on the rising edge of clk

endmodule
