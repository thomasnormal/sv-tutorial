module abort_check(input logic clk, start, ack, err);

  property p_burst_ok;
    @(posedge clk) start |=> reject_on(err) (##[1:4] ack);
  endproperty

  burst_ok_a: assert property (p_burst_ok);

endmodule
