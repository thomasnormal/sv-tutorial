module reset_check(
  input logic clk, rst_n,
  input logic req, ack
);
  sequence ack_next;
    // TODO: match an acknowledgement on the sampled edge
    1'b0;
  endsequence

  property req_ack_p;
    @(posedge clk) disable iff (!rst_n)
      // TODO: when req fires outside reset, ack_next must follow
      req |=> ack_next;
  endproperty

  // TODO: assert req_ack_p on every clock edge.

endmodule
