module ops(
  input  [3:0] a,
  input  [3:0] b,
  input        sel,
  output       parity,    // XOR reduction of a
  output [7:0] combined,  // {a, b} concatenated
  output [3:0] mux_out    // sel ? a : b
);
  // TODO: implement using reduction, concatenation, and ternary operators
endmodule
