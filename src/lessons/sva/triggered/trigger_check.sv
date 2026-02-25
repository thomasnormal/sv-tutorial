module trigger_check(input logic clk, req, busy, ack);

  // Sequence: request is active for one cycle, then busy de-asserts
  sequence s_req_done;
    @(posedge clk) req ##1 !busy;
  endsequence

  property p_ack_follows;
    @(posedge clk)
      // TODO: when s_req_done fires, ack must arrive within 3 cycles
      ;
  endproperty

  ack_follows_a: assert property (p_ack_follows);

endmodule
