module multi_ack(input logic clk, req, ack, done);

  property three_acks_p;
    @(posedge clk) req |=> ack[->3] ##1 done;
  endproperty

  three_acks_a: assert property (three_acks_p);

endmodule
