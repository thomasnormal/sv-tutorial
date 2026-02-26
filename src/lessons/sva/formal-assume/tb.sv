module tb;
  logic clk = 0, rst;
  logic [1:0] state;
  top dut(.clk(clk), .rst(rst), .state(state));
  always #5 clk = ~clk;
  initial begin
    rst = 1;
    repeat(2) @(posedge clk);
    rst = 0;
    repeat(12) @(posedge clk);
    $display("PASS");
    $finish;
  end
endmodule
