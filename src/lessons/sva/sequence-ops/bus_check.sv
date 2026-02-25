module bus_check(input logic clk, valid, ready, done);

  // intersect: both valid and ready must hold for exactly the same 4 cycles
  property p_transfer;
    @(posedge clk)
      // TODO 1: use intersect to require valid and ready to hold high for the same 4 cycles
      ;
  endproperty

  // and: after valid, ready must arrive within 4 cycles AND done within 8 —
  //      the two conditions are checked independently and may complete at different times
  property p_complete;
    @(posedge clk)
      // TODO 2: use and to check ready arrives within 4 cycles AND done within 8, independently
      ;
  endproperty

  transfer_a: assert property (p_transfer);
  complete_a: assert property (p_complete);

endmodule
