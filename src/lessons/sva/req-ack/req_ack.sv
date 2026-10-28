module req_ack(input logic clk, req, ack);

  sequence ack_window;
    // TODO: match one sampled acknowledgement level
    1'b0;
  endsequence

  property req_ack_p;
    @(posedge clk)
      // TODO: when req rises, ack_window must match within 1–3 cycles
      $rose(req) |=> ##[0:2] ack_window;
  endproperty

  // TODO: assert req_ack_p on every clock edge.

endmodule
