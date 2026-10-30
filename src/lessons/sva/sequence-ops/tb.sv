// Valid/ready stay aligned for four samples; done arrives later in its own window.
module tb;
  logic clk = 0, valid = 0, ready = 0, done = 0;

  always #5 clk = ~clk;

  bus_check dut(.clk, .valid, .ready, .done);

  initial begin
    @(posedge clk); #1;
    valid = 1; ready = 1;
    @(posedge clk); #1;
    valid = 1; ready = 1;
    @(posedge clk); #1;
    valid = 1; ready = 1;
    @(posedge clk); #1;
    valid = 1; ready = 1;
    @(posedge clk); #1;
    valid = 0; ready = 0; done = 1;
    @(posedge clk); #1;
    if (done !== 1) begin
      $display("FAIL: done did not arrive after the lock-step transfer");
      $finish;
    end
    done = 0;

    $display("TODO: complete p_transfer and p_complete, then rerun this composition trace.");
    $finish;
  end
endmodule
