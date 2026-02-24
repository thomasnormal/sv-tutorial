module lock_check(input logic clk, lock, unlock);

  property p_lock_hold(logic lk, logic ul);
    @(posedge clk) lk && !ul |=> p_lock_hold(lk, ul);
  endproperty

  lock_hold_a: assert property (p_lock_hold(lock, unlock));

endmodule
