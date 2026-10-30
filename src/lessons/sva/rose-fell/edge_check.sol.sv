module edge_check(input logic clk, cs_n, ack);

  sequence ack_rise;
    $rose(ack);
  endsequence

  property cs_ack_p;
    @(posedge clk) $fell(cs_n) |=> ##[0:1] ack_rise;
  endproperty

  cs_ack_a: assert property (cs_ack_p);

endmodule
