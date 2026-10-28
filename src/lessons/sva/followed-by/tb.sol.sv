module tb;
  logic clk = 0;
  logic burst_start = 0;
  logic burst_beat = 0;
  logic data_ok = 0;
  int fail = 0;

  top dut(.*);
  always #5 clk = ~clk;

  initial begin
    // The same burst is checked at the sequence endpoint and one sample later.
    @(posedge clk); #1;
    burst_start = 1; burst_beat = 0; data_ok = 0;
    $display("cycle 0 (start): burst_start=%0b burst_beat=%0b data_ok=%0b", burst_start, burst_beat, data_ok);
    if (burst_start !== 1 || burst_beat !== 0 || data_ok !== 0) fail++;

    @(posedge clk); #1;
    burst_start = 0; burst_beat = 1; data_ok = 1;
    $display("cycle 1 (first beat): burst_start=%0b burst_beat=%0b data_ok=%0b", burst_start, burst_beat, data_ok);
    if (burst_start !== 0 || burst_beat !== 1 || data_ok !== 1) fail++;

    @(posedge clk); #1;
    burst_beat = 1; data_ok = 1;
    $display("cycle 2 (sequence endpoint): burst_start=%0b burst_beat=%0b data_ok=%0b  <-- #-#", burst_start, burst_beat, data_ok);
    if (burst_start !== 0 || burst_beat !== 1 || data_ok !== 1) begin
      $display("FAIL: #-# endpoint sample did not carry data_ok");
      fail++;
    end

    @(posedge clk); #1;
    burst_beat = 0; data_ok = 1;
    $display("cycle 3 (next sample): burst_start=%0b burst_beat=%0b data_ok=%0b  <-- #=#", burst_start, burst_beat, data_ok);
    if (burst_start !== 0 || burst_beat !== 0 || data_ok !== 1) begin
      $display("FAIL: #=# next sample did not carry data_ok");
      fail++;
    end

    if (fail == 0) $display("PASS: #-# checked the burst endpoint and #=# checked the following sample");
    else $display("FAIL: %0d followed-by timing checks were wrong", fail);
    $finish;
  end
endmodule
