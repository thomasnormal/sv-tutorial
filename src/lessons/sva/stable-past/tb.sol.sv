module tb;
  logic clk = 0, valid = 0, ready = 1;
  logic [7:0] data = 8'h00;

  always #5 clk = ~clk;

  stable_check dut(.clk, .valid, .ready, .data);

  initial begin
    @(posedge clk); #1;
    valid = 1; ready = 0; data = 8'h3C;
    @(posedge clk); #1;
    data = 8'h3C;
    @(posedge clk); #1;
    ready = 1; data = 8'hA5;
    @(posedge clk); #1;
    valid = 0;
    @(posedge clk); #1;

    $display("PASS: data stayed stable while valid stalled and changed after ready");
    $finish;
  end
endmodule
