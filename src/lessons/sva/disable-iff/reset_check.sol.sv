module reset_check(
  input logic clk, rst_n,
  input logic req, ack
);
  property req_ack_p;
    @(posedge clk) disable iff (!rst_n)
      req |=> ack;
  endproperty

  req_ack_a: assert property (req_ack_p);

endmodule
