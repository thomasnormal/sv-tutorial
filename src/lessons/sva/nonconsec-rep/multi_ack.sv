module multi_ack(input logic clk, req, ack, done);

  property three_acks_p;
    @(posedge clk)
      // TODO: after req, wait for 3 non-consecutive ack pulses, then check done is high
      ;
  endproperty

  three_acks_a: assert property (three_acks_p);

endmodule
