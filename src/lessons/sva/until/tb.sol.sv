module tb;
  logic clk = 0, valid = 0, done = 0, data_ok = 0;
  int fail = 0;

  always #5 clk = ~clk;
  hold_check dut(.clk, .valid, .done, .data_ok);

  initial begin
    @(posedge clk); #1;
    valid = 1;
    done = 0;
    data_ok = 1;
    @(posedge clk); #1;
    done = 1;
    @(posedge clk); #1;
    $display("completion: valid=%0b done=%0b data_ok=%0b (expect 1,1,1)", valid, done, data_ok);
    if (valid !== 1 || done !== 1 || data_ok !== 1) begin
      $display("FAIL: completion edge did not include a clean payload");
      fail++;
    end
    valid = 0;
    done = 0;
    data_ok = 0;
    @(posedge clk); #1;

    if (fail == 0) $display("PASS: valid held until done and data_ok included the done edge");
    else $display("FAIL: %0d until trace checks were wrong", fail);
    $finish;
  end
endmodule
