module tb;
  logic clk = 0, frame_ = 0, ldp_ = 1;

  always #5 clk = ~clk;

  bus_check dut(.clk, .frame_, .ldp_);

  initial begin
    @(posedge clk); #1;
    frame_ = 1; ldp_ = 1;
    @(posedge clk); #1;
    frame_ = 0; ldp_ = 1;
    @(posedge clk); #1;
    ldp_ = 0;
    @(posedge clk); #1;

    $display("PASS: cover reached the frame-to-ldp_ timing scenario");
    $finish;
  end
endmodule
