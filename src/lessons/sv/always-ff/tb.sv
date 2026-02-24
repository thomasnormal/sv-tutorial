module tb;
  logic clk=0, rst_n=0, d=0, q;
  always #5 clk = ~clk;
  dff dut(.clk,.rst_n,.d,.q);
  initial begin
    @(posedge clk); #1;
    $display("in reset:    q=%b (expect 0)", q);
    rst_n=1; d=1; @(posedge clk); #1;
    $display("d=1 clocked: q=%b (expect 1)", q);
    d=0; @(posedge clk); #1;
    $display("d=0 clocked: q=%b (expect 0)", q);
    $finish;
  end
endmodule
