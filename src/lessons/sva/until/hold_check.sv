module hold_check(input logic clk, valid, done, data_ok);

  // valid must stay high until done arrives (and done must eventually arrive)
  property p_valid_holds;
    @(posedge clk)
      // TODO: valid must stay high until done arrives, and done must eventually arrive
      ;
  endproperty

  // data_ok must be high on the same cycle that done fires
  property p_done_clean;
    @(posedge clk)
      // TODO: from valid going high, data_ok must hold on every cycle including the done cycle
      ;
  endproperty

  valid_holds_a: assert property (p_valid_holds);
  done_clean_a:  assert property (p_done_clean);

endmodule
