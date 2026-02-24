module vacuous_demo (
  input logic clk, rst_n,
  input logic req, gnt
);
  // This property checks: whenever req rises, gnt follows within 2 clocks.
  // But if req NEVER rises in simulation, the assert still passes — vacuously.
  property req_gnt;
    @(posedge clk) disable iff (!rst_n)
      $rose(req) |-> ##[1:2] gnt;
  endproperty

  // TODO: rg_assert: assert property (req_gnt)
  //         else $display("req_gnt FAIL at t=%0t", $time);
  // TODO: rg_cover:  cover  property (req_gnt)
  //                  $display("req_gnt antecedent fired at t=%0t", $time);

endmodule
