// Exercise both reusable checker instances with independent channel timing.
module tb;
  logic clk = 0;
  logic req1 = 0, ack1 = 0, req2 = 0, ack2 = 0;
  logic valid1 = 0, valid2 = 0;
  logic [7:0] data1 = 8'hA5, data2 = 8'h5A;

  always #5 clk = ~clk;

  top dut(.clk, .req1, .ack1, .req2, .ack2, .valid1, .valid2, .data1, .data2);

  initial begin
    @(posedge clk); #1;
    req1 = 1;
    @(posedge clk); #1;
    req1 = 0; req2 = 1; valid1 = 1; data1 = 8'hA5;
    @(posedge clk); #1;
    req2 = 0; valid1 = 1; data1 = 8'hA5; valid2 = 1; data2 = 8'h5A;
    @(posedge clk); #1;
    ack1 = 1; valid1 = 0; valid2 = 1; data2 = 8'h5A;
    @(posedge clk); #1;
    if (ack1 !== 1 || data1 !== 8'hA5 || data2 !== 8'h5A) begin
      $display("FAIL: channel 1 response or held data was incorrect");
      $finish;
    end
    ack1 = 0; ack2 = 0; valid2 = 1; data2 = 8'h5A;
    @(posedge clk); #1;
    ack2 = 1; valid2 = 0;
    @(posedge clk); #1;
    if (ack2 !== 1) begin
      $display("FAIL: channel 2 response did not arrive in its legal window");
      $finish;
    end

    $display("PASS: two checker instances accepted independent handshakes and stable data");
    $finish;
  end
endmodule
