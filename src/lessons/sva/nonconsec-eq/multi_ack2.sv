module multi_ack2(input logic clk, start, ack, done);

  property three_acks_p;
    @(posedge clk)
      // TODO: after start, ack must pulse 3 times, then done must arrive at any later point
      ;
  endproperty

  three_acks_a: assert property (three_acks_p);

endmodule
