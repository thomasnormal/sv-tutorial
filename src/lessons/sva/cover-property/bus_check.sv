module bus_check(input logic clk, frame_, ldp_);

  property ldpcheck;
    @(posedge clk) $rose(frame_) |-> ##[1:2] $fell(ldp_);
  endproperty

  // TODO: assert ldpcheck — print an error message when it fails
  // TODO: cover  ldpcheck — print a pass message each time it succeeds

endmodule
