module multi_ack2(input logic clk, start, ack, done);

  sequence ack_burst;
    ack[=3];
  endsequence

  property three_acks_p;
    @(posedge clk) start |=> ack_burst ##[0:$] done;
  endproperty

  three_acks_a: assert property (three_acks_p);

endmodule
