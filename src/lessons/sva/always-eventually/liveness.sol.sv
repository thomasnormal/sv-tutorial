module liveness(input logic clk, rst_n, lock);

  property p_lock_live;
    @(posedge clk) $rose(rst_n) |-> s_eventually lock;
  endproperty

  property p_lock_stable;
    @(posedge clk) lock |-> always lock;
  endproperty

  lock_live_a:   assert property (p_lock_live);
  lock_stable_a: assert property (p_lock_stable);

endmodule
