module signals(
  input        clk,
  input  [3:0] a,
  input  [3:0] b,
  output [3:0] and_out,
  output reg [3:0] reg_out
);
  assign and_out = a & b;

  always @(posedge clk)
    reg_out <= a;
endmodule
