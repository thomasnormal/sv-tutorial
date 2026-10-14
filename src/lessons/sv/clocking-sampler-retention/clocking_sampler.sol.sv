module tb;
  logic clk = 0;
  logic [7:0] sig = 8'hAA;
  bit reactive_done = 0;

  clocking cb @(posedge clk);
    input #0 sig;
  endclocking

  always #5 clk = ~clk;
  always @(posedge clk) sig = 8'hBB;
  reactive_writer writer(.clk(clk));

  initial begin
    @(cb);
    if (cb.sig !== 8'hBB) begin
      $display("FAIL: first sample=%h", cb.sig);
      $finish;
    end
    wait (reactive_done);
    if (cb.sig !== 8'hBB) begin
      $display("FAIL: same-slot sample=%h", cb.sig);
      $finish;
    end
    #1;
    if (cb.sig !== 8'hBB) begin
      $display("FAIL: retained sample=%h", cb.sig);
      $finish;
    end
    #5;
    if (cb.sig !== 8'hBB) begin
      $display("FAIL: negedge sample=%h", cb.sig);
      $finish;
    end
    @(cb);
    if (cb.sig !== 8'hBB) begin
      $display("FAIL: resample=%h", cb.sig);
      $finish;
    end
    $display("PASS: clocking sample retained=%h", cb.sig);
    $finish;
  end
endmodule

program reactive_writer(input logic clk);
  initial begin
    @(posedge clk);
    tb.sig = 8'hCC;
    #0;
    tb.reactive_done = 1;
    #100;
  end
endprogram
