module tb;
  logic clk = 0, update = 0;
  logic [7:0] data = 8'h00;

  always #5 clk = ~clk;

  toggle_check dut(.clk, .update, .data);

  initial begin
    @(posedge clk); #1;
    update = 1; data = 8'h10;
    @(posedge clk); #1;
    data = 8'h11;
    @(posedge clk); #1;
    data = 8'h12;
    @(posedge clk); #1;
    update = 0;

    $display("PASS: data changed on every sampled edge while update was high");
    $finish;
  end
endmodule
