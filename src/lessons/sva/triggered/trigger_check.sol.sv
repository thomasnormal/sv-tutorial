module trigger_check(input logic clk, req, busy, ack);

  sequence s_req_done;
    @(posedge clk) req ##1 !busy;
  endsequence

  property p_ack_follows;
    @(posedge clk) s_req_done.triggered |-> ##[1:3] ack;
  endproperty

  ack_follows_a: assert property (p_ack_follows);

endmodule
