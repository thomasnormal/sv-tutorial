module arbiter_check(
  input logic       clk,
  input logic [3:0] req,
  input logic [3:0] grant,
  input logic       any_grant
);

  // TODO: property grant_onehot_p:
  //   @(posedge clk) any_grant |-> $onehot(grant);

  // TODO: property grant_idle_p:
  //   @(posedge clk) !any_grant |-> (grant == 4'b0);

  // TODO: assert both properties

endmodule
