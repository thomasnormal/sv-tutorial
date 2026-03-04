// The SRAM write-lock protocol: once locked, writes are forbidden until unlock.
// A recursive property would say "lock holds until unlock — forever".
// BMC proves the equivalent one-step inductive form for all depths up to its bound.
module lock_check(
  input logic clk, rst_n,
  input logic lock, unlock,  // lock/unlock control signals
  input logic we             // SRAM write-enable
);

  // Property 1: if lock is high and unlock has not fired, lock must remain
  //             high on the very next cycle (the inductive "hold" step)
  property p_lock_hold;
    @(posedge clk) disable iff (!rst_n)
      // TODO 1: lock && !unlock implies lock is still high next cycle
      ;
  endproperty

  // Property 2: while the SRAM is locked, writes must be blocked
  property p_writes_blocked;
    @(posedge clk) disable iff (!rst_n)
      // TODO 2: if lock is high, we must be low
      ;
  endproperty

  // Property 3: lock and unlock must not be asserted simultaneously
  property p_no_simultaneous;
    @(posedge clk) disable iff (!rst_n)
      // TODO 3: lock and unlock are mutually exclusive
      ;
  endproperty

  lock_hold_a:      assert property (p_lock_hold);
  writes_blocked_a: assert property (p_writes_blocked);
  no_simul_a:       assert property (p_no_simultaneous);

endmodule
