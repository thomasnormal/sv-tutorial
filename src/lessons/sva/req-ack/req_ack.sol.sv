module req_ack(input logic clk, req, ack);

  sequence ack_window;
    ack;
  endsequence

  property req_ack_p;
    @(posedge clk) $rose(req) |=> ##[0:2] ack_window;
  endproperty

  req_ack_a: assert property (req_ack_p);

endmodule
