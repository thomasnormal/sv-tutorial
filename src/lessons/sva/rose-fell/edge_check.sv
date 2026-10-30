module edge_check(input logic clk, cs_n, ack);

  sequence ack_rise;
    // TODO: match one sampled rising edge on ack
    1'b0;
  endsequence

  property cs_ack_p;
    @(posedge clk)
      // TODO: when cs_n falls, ack_rise must follow within 0–1 cycles
      $fell(cs_n) |=> ##[0:1] ack_rise;
  endproperty

  // TODO: assert cs_ack_p on every clock edge.

endmodule
