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
    if (valid !== 1 || done !== 1 || data_ok !== 1) fail++;
    valid = 0;
    done = 0;
    data_ok = 0;
    @(posedge clk); #1;

    if (fail == 0) $display("TODO: complete p_valid_holds and p_done_clean, then rerun this request trace.");
    else $display("FAIL: %0d until trace checks were wrong", fail);
    $finish;
  end
endmodule
