module req_ack(input logic clk, req, ack);

  property req_ack_p;
    @(posedge clk)
      // TODO: when req rises, ack must be high within 1–3 cycles
      ;
  endproperty

  req_ack_a: assert property (req_ack_p);

endmodule
