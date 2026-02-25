module edge_check(input logic clk, cs_n, ack);

  property cs_ack_p;
    @(posedge clk)
      // TODO: when cs_n falls (goes active-low), ack must rise within 0–1 cycles
      ;
  endproperty

  cs_ack_a: assert property (cs_ack_p);

endmodule
