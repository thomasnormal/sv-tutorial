primitive dff1(output reg q = 1'b1, input clk, input d);
  table
    (01) 0 : ? : 0;
    (01) 1 : ? : 1;
    (10) ? : ? : -;
  endtable
endprimitive

module tb;
  logic clk;
  logic d;
  wire q;
  dff1 dut(q, clk, d);

  initial begin
    #1;
    if (q !== 1'b1) begin
      $display("FAIL: initial q=%b", q);
      $finish;
    end
    $display("INITIAL q=%b", q);

    d = 0;
    clk = 0;
    #1;
    clk = 1;
    #1;
    if (q !== 1'b0)
      $display("FAIL: edge q=%b", q);
    else
      $display("PASS");
    $finish;
  end
endmodule
