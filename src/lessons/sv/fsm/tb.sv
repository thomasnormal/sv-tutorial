module tb;
  logic clk=0, rst_n=0, din=0, detected;
  always #5 clk = ~clk;
  seq_det dut(.clk,.rst_n,.din,.detected);
  task automatic send(input logic b);
    din = b; @(posedge clk); #1;
  endtask
  initial begin
    @(posedge clk); rst_n = 1;
    send(1); send(0); send(1);
    $display("after 1-0-1: detected=%b (expect 1)", detected);
    send(0); send(1); send(0); send(1);
    $display("after 1-0-1: detected=%b (expect 1)", detected);
    send(0);
    $display("after extra 0: detected=%b (expect 0)", detected);
    $finish;
  end
endmodule
