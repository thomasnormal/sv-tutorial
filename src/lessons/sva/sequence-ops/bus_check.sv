module bus_check(input logic clk, valid, ready);

  // Spec: once valid is asserted, both valid and ready must stay
  // high for exactly 4 consecutive cycles simultaneously.
  property p_transfer;
    @(posedge clk)
      // TODO: valid |-> (valid[*4]) intersect (ready[*4]);
      ;
  endproperty

  transfer_a: assert property (p_transfer);

endmodule
