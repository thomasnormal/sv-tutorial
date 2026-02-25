module tb;
  logic clk=0, rst_n=0, en=0;
  logic [7:0] count;

  // `always` without a sensitivity list runs forever; #5 waits 5 time units.
  // Together this toggles clk every 5 units → 10-unit period clock.
  always #5 clk = ~clk;

  counter dut(.clk, .rst_n, .en, .count);

  initial begin
    // Reset holds count at 0
    rst_n=0; en=1;
    repeat(3) @(posedge clk); #1;
    $display("%s rst_n=0 holds count=0: count=%0d",
             count===0 ? "PASS" : "FAIL", count);

    // Count increments when en=1
    rst_n=1;
    repeat(4) @(posedge clk); #1;
    $display("%s counted 4: count=%0d (expect 4)",
             count===4 ? "PASS" : "FAIL", count);

    // Enable gate: en=0 freezes count
    en=0;
    repeat(3) @(posedge clk); #1;
    $display("%s en=0 freezes count: count=%0d (expect 4)",
             count===4 ? "PASS" : "FAIL", count);

    // Synchronous reset clears on next rising edge
    rst_n=0; @(posedge clk); #1; rst_n=1;
    $display("%s sync reset clears to 0: count=%0d",
             count===0 ? "PASS" : "FAIL", count);

    $finish;
  end
endmodule
