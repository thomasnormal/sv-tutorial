module signals(
  input        clk,
  input  [3:0] a,
  input  [3:0] b,
  output [3:0] and_out,    // wire output: a & b
  output reg [3:0] reg_out // reg output: latched a on posedge clk
);
  // TODO: use assign for and_out
  // TODO: use always @(posedge clk) to latch 'a' into reg_out
endmodule
