module arbiter_check(
  input logic       clk,
  input logic [3:0] req,
  input logic [3:0] grant,
  input logic       any_grant
);

  // TODO: property grant_onehot_p — when any_grant is high, exactly one bit of grant must be set

  // TODO: property grant_idle_p — when any_grant is low, grant must be all zeros

  // TODO: assert both properties

endmodule
