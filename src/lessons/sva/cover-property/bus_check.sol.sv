module bus_check(input logic clk, frame_, ldp_);

  property ldpcheck;
    @(posedge clk) $rose(frame_) |-> ##[1:2] $fell(ldp_);
  endproperty

  aP: assert property (ldpcheck)
    else $display("ldpcheck FAIL");
  cP: cover property (ldpcheck)
    $display("ldpcheck PASS");

endmodule
