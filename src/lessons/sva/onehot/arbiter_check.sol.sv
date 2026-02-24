module arbiter_check(
  input logic       clk,
  input logic [3:0] req,
  input logic [3:0] grant,
  input logic       any_grant
);

  property grant_onehot_p;
    @(posedge clk) any_grant |-> $onehot(grant);
  endproperty

  property grant_idle_p;
    @(posedge clk) !any_grant |-> (grant == 4'b0);
  endproperty

  grant_onehot_a: assert property (grant_onehot_p);
  grant_idle_a:   assert property (grant_idle_p);

endmodule
