module Spec(
  input  logic a, b, c,
  output logic nand_y,
  output logic nor_y,
  output logic mux_y
);
  assign nand_y = ~(a & b);
  assign nor_y  = ~(a | b);
  assign mux_y  = c ? a : b;
endmodule

module Impl(
  input  logic a, b, c,
  output logic nand_y,
  output logic nor_y,
  output logic mux_y
);
  assign nand_y = ~a | ~b;           // De Morgan: ~(a & b) = ~a | ~b
  assign nor_y  = ~a & ~b;           // De Morgan: ~(a | b) = ~a & ~b
  assign mux_y  = (c & a) | (~c & b); // Boolean: c ? a : b = (c & a) | (~c & b)
endmodule
