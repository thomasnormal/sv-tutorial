// Spec: three canonical boolean functions — the reference implementation
module Spec(
  input  logic a, b, c,
  output logic nand_y,   // 2-input NAND
  output logic nor_y,    // 2-input NOR
  output logic mux_y     // 2-input mux selected by c
);
  assign nand_y = ~(a & b);
  assign nor_y  = ~(a | b);
  assign mux_y  = c ? a : b;
endmodule

// Impl: equivalent circuits using only ~, &, | (no ? operator)
// LEC will prove Spec and Impl produce identical outputs for every input.
// Complete each assign using the identities in the description.
module Impl(
  input  logic a, b, c,
  output logic nand_y,   // TODO 1: ~(a & b) = ? using De Morgan's law
  output logic nor_y,    // TODO 2: ~(a | b) = ? using De Morgan's law
  output logic mux_y     // TODO 3: c ? a : b = ? using Boolean expansion
);
  assign nand_y = /* TODO 1 */ 1'b0;
  assign nor_y  = /* TODO 2 */ 1'b0;
  assign mux_y  = /* TODO 3 */ 1'b0;
endmodule
