module tb;
  logic clk = 0, rst;
  logic [3:0] cnt;
  top dut(.clk(clk), .rst(rst), .cnt(cnt));
  always #5 clk = ~clk;
  initial begin
    rst = 1;
    repeat(3) @(posedge clk);
    rst = 0;
    repeat(10) @(posedge clk);
    rst = 1;
    repeat(2) @(posedge clk);
    rst = 0;
    repeat(5) @(posedge clk);
    $finish;
  end
endmodule
