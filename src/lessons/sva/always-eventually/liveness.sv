module liveness(input logic clk, rst_n, lock);

  // After POR, the lock signal must eventually assert (liveness)
  property p_lock_live;
    @(posedge clk)
      // TODO: $rose(rst_n) |-> s_eventually lock;
      ;
  endproperty

  // Once lock asserts it never de-asserts (safety)
  property p_lock_stable;
    @(posedge clk)
      // TODO: lock |-> always lock;
      ;
  endproperty

  lock_live_a:   assert property (p_lock_live);
  lock_stable_a: assert property (p_lock_stable);

endmodule
