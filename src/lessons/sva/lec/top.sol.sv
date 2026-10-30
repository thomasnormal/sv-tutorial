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
  logic a_when_c, b_when_not_c;

  assign nand_y = ~a | ~b;           // De Morgan: ~(a & b) = ~a | ~b
  assign nor_y  = ~a & ~b;           // De Morgan: ~(a | b) = ~a & ~b
  assign a_when_c = c & a;
  assign b_when_not_c = ~c & b;
  assign mux_y  = a_when_c | b_when_not_c; // Boolean: c ? a : b = (c & a) | (~c & b)
endmodule
