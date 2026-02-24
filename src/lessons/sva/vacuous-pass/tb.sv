// Testbench that never drives req high — the antecedent never fires.
// The assert reports no failures, but nothing was checked.
module tb;
  logic clk = 0, rst_n = 0;
  logic req = 0, gnt = 0;

  always #5 clk = ~clk;

  vacuous_demo dut(.clk, .rst_n, .req, .gnt);

  initial begin
    @(posedge clk); rst_n = 1;
    // req stays low the entire run — $rose(req) never fires.
    repeat (10) @(posedge clk);
    $display("done: no assert failures, but did rg_cover ever fire?");
    $finish;
  end
endmodule
