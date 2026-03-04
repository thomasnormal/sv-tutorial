module lock_check(
  input logic clk, rst_n,
  input logic lock, unlock,
  input logic we
);

  property p_lock_hold;
    @(posedge clk) disable iff (!rst_n)
      lock && !unlock |=> lock;
  endproperty

  property p_writes_blocked;
    @(posedge clk) disable iff (!rst_n)
      lock |-> !we;
  endproperty

  property p_no_simultaneous;
    @(posedge clk) disable iff (!rst_n)
      !(lock && unlock);
  endproperty

  lock_hold_a:      assert property (p_lock_hold);
  writes_blocked_a: assert property (p_writes_blocked);
  no_simul_a:       assert property (p_no_simultaneous);

endmodule
