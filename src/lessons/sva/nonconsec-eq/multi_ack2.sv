module multi_ack2(input logic clk, start, ack, done);

  property three_acks_p;
    @(posedge clk)
      // TODO: start |=> ack[=3] ##[0:$] done;
      ;
  endproperty

  three_acks_a: assert property (three_acks_p);

endmodule
