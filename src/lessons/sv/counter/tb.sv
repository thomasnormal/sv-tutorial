module tb;
  logic clk=0, rst_n=0, en=0;
  logic [7:0] count;
  always #5 clk = ~clk;
  counter dut(.clk,.rst_n,.en,.count);
  initial begin
    @(posedge clk); rst_n=1; en=1;
    repeat(5) @(posedge clk);
    #1 $display("after 5 cycles: %0d (expect 5)", count);
    en=0; @(posedge clk); #1;
    $display("after pause:    %0d (expect 5)", count);
    rst_n=0; @(posedge clk); #1;
    $display("after reset:    %0d (expect 0)", count);
    $finish;
  end
endmodule
