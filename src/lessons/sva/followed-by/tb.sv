module tb;
  logic clk = 0;
  logic burst_start = 0;
  logic burst_beat = 0;
  logic data_ok = 0;

  top dut(.*);
  always #5 clk = ~clk;

  initial begin
    // This file is only a readable stimulus sketch; use Verify for BMC.
    repeat (6) @(posedge clk);
    $display("Use Verify to compare #-# and #=# across all input traces.");
    $finish;
  end
endmodule
