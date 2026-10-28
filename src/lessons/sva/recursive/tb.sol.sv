// Reset, an unlocked cycle, then a lock held while writes stay blocked.
module tb;
  logic clk = 0, rst_n = 0;
  logic lock = 0, unlock = 0, we = 0;

  always #5 clk = ~clk;

  lock_check dut(.clk, .rst_n, .lock, .unlock, .we);

  initial begin
    @(posedge clk); #1;
    rst_n = 0; lock = 0; unlock = 0; we = 0;
    @(posedge clk); #1;
    rst_n = 1; lock = 0; unlock = 1; we = 0;
    @(posedge clk); #1;
    lock = 1; unlock = 0; we = 0;
    @(posedge clk); #1;
    lock = 1; unlock = 0; we = 0;
    @(posedge clk); #1;
    if (lock !== 1 || we !== 0 || unlock !== 0) begin
      $display("FAIL: the locked cycle did not block writes");
      $finish;
    end
    lock = 1; unlock = 0; we = 0;
    @(posedge clk); #1;
    if (lock !== 1 || we !== 0) begin
      $display("FAIL: lock was not held on the next cycle");
      $finish;
    end

    $display("PASS: the lock stayed asserted and blocked writes across every sampled cycle");
    $finish;
  end
endmodule
