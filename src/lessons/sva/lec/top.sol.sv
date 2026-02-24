// Golden reference: NAND gate
module Spec(input a, b, output y);
  assign y = ~(a & b);
endmodule

// Fixed implementation using De Morgan's law: ~(a & b) ≡ ~a | ~b
module Impl(input a, b, output y);
  assign y = ~a | ~b;
endmodule
