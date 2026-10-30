module multi_ack(input logic clk, req, ack, done);

  sequence three_acks;
    // TODO: match three non-consecutive acknowledgement pulses
    1'b0;
  endsequence

  property three_acks_p;
    @(posedge clk)
      // TODO: after req, wait for three_acks, then check done next cycle
      req |=> three_acks ##1 done;
  endproperty

  // TODO: assert three_acks_p on every clock edge.

endmodule
