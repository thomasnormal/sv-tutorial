// A short simulation trace for the immediate-assertion checker.
// The four illegal cycles should be reported once the assertions are added.
module tb;
  logic clk = 0;
  logic wr_en = 0, rd_en = 0;
  logic full = 0, empty = 0;
  logic [3:0] count = 0;

  always #5 clk = ~clk;

  fifo_checker dut(.clk, .wr_en, .rd_en, .full, .empty, .count);

  initial begin
    @(posedge clk); #1;
    // Legal baseline: one write below full and a count in range.
    wr_en = 1; full = 0; rd_en = 0; empty = 0; count = 1;
    @(posedge clk); #1;

    // Four deliberate violations for the four assertions.
    wr_en = 1; full = 1; count = 2;       // write while full
    @(posedge clk); #1;
    wr_en = 0; full = 0; rd_en = 1; empty = 1; // read while empty
    @(posedge clk); #1;
    rd_en = 1; empty = 0; wr_en = 1;           // read and write together
    @(posedge clk); #1;
    wr_en = 0; rd_en = 0; count = 9;           // count exceeds DEPTH
    @(posedge clk); #1;

    $display("TODO: add the four immediate assertions and inspect their error actions.");
    $finish;
  end
endmodule
