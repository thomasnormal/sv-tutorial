module abort_check(input logic clk, start, ack, err);

  sequence ack_window;
    ##[1:4] ack;
  endsequence

  property p_burst_ok;
    @(posedge clk) start |=> reject_on(err) ack_window;
  endproperty

  burst_ok_a: assert property (p_burst_ok);

endmodule
