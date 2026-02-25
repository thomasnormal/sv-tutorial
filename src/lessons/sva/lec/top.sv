// Golden reference: NAND gate
module Spec(input a, b, output y);
  assign y = ~(a & b);
endmodule

// TODO: fix the bug so Impl is equivalent to Spec
module Impl(input a, b, output y);
  assign y = ~a | b; // BUG: one inversion is missing
endmodule
