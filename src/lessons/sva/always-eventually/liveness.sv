module liveness(input logic clk, rst_n, lock);

  // After POR, the lock signal must eventually assert (liveness)
  property p_lock_live;
    @(posedge clk)
      // TODO: after reset de-asserts, lock must eventually become true
      ;
  endproperty

  // Once lock asserts it never de-asserts (safety)
  property p_lock_stable;
    @(posedge clk)
      // TODO: once lock asserts, it must hold true at every future cycle
      ;
  endproperty

  lock_live_a:   assert property (p_lock_live);
  lock_stable_a: assert property (p_lock_stable);

endmodule
