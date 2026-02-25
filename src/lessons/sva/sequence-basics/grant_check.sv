module grant_check(input logic clk, cStart, req, gnt);

  // Spec: when cStart is high, req must be high the same cycle
  // and gnt must be high exactly 2 cycles later.

  // A sequence is a temporal pattern
  sequence sr1;
    // TODO: req is high, then 2 cycles later gnt is high
  endsequence

  // A property binds a sequence to a clock and a trigger
  property pr1;
    // TODO: when cStart fires, sr1 must follow
  endproperty

  // TODO: assert the property

endmodule
