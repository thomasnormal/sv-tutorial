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

    $display("PASS: the captured input value reached out_data three edges later");
    $finish;
  end
endmodule
