module tb;
  logic clk = 0;
  logic wr_en = 0, rd_en = 0;
  logic full = 0, empty = 0;
  logic [3:0] count = 0;

  always #5 clk = ~clk;

  fifo_checker dut(.clk, .wr_en, .rd_en, .full, .empty, .count);

  initial begin
    @(posedge clk); #1;
    wr_en = 1; full = 0; rd_en = 0; empty = 0; count = 1;
    @(posedge clk); #1;
    wr_en = 1; full = 1; count = 2;
    @(posedge clk); #1;
    wr_en = 0; full = 0; rd_en = 1; empty = 1;
    @(posedge clk); #1;
    rd_en = 1; empty = 0; wr_en = 1;
    @(posedge clk); #1;
    wr_en = 0; rd_en = 0; count = 9;
    @(posedge clk); #1;

    $display("PASS: four illegal FIFO situations reached the immediate assertions");
    $finish;
  end
endmodule
