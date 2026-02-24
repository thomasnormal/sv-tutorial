module grant_check(input logic clk, cStart, req, gnt);

  // A sequence is a temporal pattern
  sequence sr1;
    // TODO: req ##2 gnt;
  endsequence

  // A property binds a sequence to a clock and a trigger
  property pr1;
    // TODO: @(posedge clk) cStart |-> sr1;
  endproperty

  // TODO: reqGnt: assert property (pr1);

endmodule
