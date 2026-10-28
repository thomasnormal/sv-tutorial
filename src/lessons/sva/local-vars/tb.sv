// Capture one input value and present it at the three-edge output point.
module tb;
  logic clk = 0, valid_in = 0;
  logic [7:0] in_data = 0, out_data = 0;

  always #5 clk = ~clk;

  pipeline_check dut(.clk, .valid_in, .in_data, .out_data);

  initial begin
    @(posedge clk); #1;
    valid_in = 1; in_data = 8'hA5; out_data = 8'h00;
    @(posedge clk); #1;
    valid_in = 0; out_data = 8'h00;
    @(posedge clk); #1;
    out_data = 8'h00;
    @(posedge clk); #1;
    out_data = 8'hA5;
    @(posedge clk); #1;
    if (out_data !== 8'hA5) begin $display("FAIL: delayed output did not match input"); $finish; end

    $display("TODO: complete the local-variable property, then rerun this pipeline trace.");
    $finish;
  end
endmodule
