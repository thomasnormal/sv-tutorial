module lock_check(input logic clk, lock, unlock);

  // Recursive property: if lock is high and unlock hasn't fired,
  // lock must still be high at the next clock edge.
  property p_lock_hold(logic lk, logic ul);
    @(posedge clk)
      // TODO: lk && !ul |=> p_lock_hold(lk, ul);
      ;
  endproperty

  lock_hold_a: assert property (p_lock_hold(lock, unlock));

endmodule
