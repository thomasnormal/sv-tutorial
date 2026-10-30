module multi_ack2(input logic clk, start, ack, done);

  sequence ack_burst;
    // TODO: match three non-consecutive acknowledgement pulses
    1'b0;
  endsequence

  property three_acks_p;
    @(posedge clk)
      // TODO: after start, ack_burst must finish before done arrives
      start |=> ack_burst ##[0:$] done;
  endproperty

  // TODO: assert three_acks_p on every clock edge.

endmodule
