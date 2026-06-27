module ops(
  input  [3:0] a,
  input  [3:0] b,
  input        sel,
  output       parity,
  output [7:0] combined,
  output [3:0] mux_out
);
  assign parity   = ^a;
  assign combined = {a, b};
  assign mux_out  = sel ? a : b;
endmodule
