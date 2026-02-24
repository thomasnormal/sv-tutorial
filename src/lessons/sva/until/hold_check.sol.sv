module hold_check(input logic clk, valid, done, data_ok);

  property p_valid_holds;
    @(posedge clk) valid |-> valid s_until done;
  endproperty

  property p_done_clean;
    @(posedge clk) valid |-> data_ok until_with done;
  endproperty

  valid_holds_a: assert property (p_valid_holds);
  done_clean_a:  assert property (p_done_clean);

endmodule
