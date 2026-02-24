module hold_check(input logic clk, valid, done, data_ok);

  // valid must stay high until done arrives (and done must eventually arrive)
  property p_valid_holds;
    @(posedge clk)
      // TODO: valid |-> valid s_until done;
      ;
  endproperty

  // data_ok must be high on the same cycle that done fires
  property p_done_clean;
    @(posedge clk)
      // TODO: valid |-> data_ok until_with done;
      ;
  endproperty

  valid_holds_a: assert property (p_valid_holds);
  done_clean_a:  assert property (p_done_clean);

endmodule
