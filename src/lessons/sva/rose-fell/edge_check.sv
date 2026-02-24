module edge_check(input logic clk, cs_n, ack);

  property cs_ack_p;
    @(posedge clk)
      // TODO: $fell(cs_n) |=> ##[0:1] $rose(ack);
      ;
  endproperty

  cs_ack_a: assert property (cs_ack_p);

endmodule
