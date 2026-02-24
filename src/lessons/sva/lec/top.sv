// Golden reference: NAND gate
module Spec(input a, b, output y);
  assign y = ~(a & b);
endmodule

// TODO: fix to be equivalent to Spec using De Morgan's law
// ~(a & b)  ≡  ~a | ~b
module Impl(input a, b, output y);
  assign y = ~a | b; // BUG: missing ~ on b
endmodule
