module tb;
  logic passed;

  event_sync dut(.passed(passed));

  initial begin
    // The writer waits 10 time units before posting write_done.
    #11;
    if (passed === 1'b1) $display("PASS");
    else $display("FAIL: event pipeline did not complete correctly");
    $finish;
  end
endmodule
