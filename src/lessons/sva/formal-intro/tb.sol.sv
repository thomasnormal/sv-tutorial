module tb;
  logic clk = 0, rst = 0;
  logic [3:0] cnt;

  always #5 clk = ~clk;

  top dut(.clk, .rst, .cnt);

  initial begin
    @(posedge clk); #1;
    rst = 1;
    @(posedge clk); #1;
    if (cnt !== 4'd0) begin $display("FAIL: reset did not clear cnt"); $finish; end
    rst = 0;
    @(posedge clk); #1;
    if (cnt !== 4'd1) begin $display("FAIL: cnt did not advance to 1"); $finish; end
    @(posedge clk); #1;
    if (cnt !== 4'd2) begin $display("FAIL: cnt did not advance to 2"); $finish; end

    $display("PASS: reset cleared cnt and the bounded counter trace advanced correctly");
    $finish;
  end
endmodule
