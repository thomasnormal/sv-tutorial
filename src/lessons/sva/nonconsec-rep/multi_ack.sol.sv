module multi_ack(input logic clk, req, ack, done);

  sequence three_acks;
    ack[->3];
  endsequence

  property three_acks_p;
    @(posedge clk) req |=> three_acks ##1 done;
  endproperty

  three_acks_a: assert property (three_acks_p);

endmodule
