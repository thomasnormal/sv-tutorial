module tb;
  logic [7:0] a, b, sum;
  adder dut(.a(a), .b(b), .sum(sum));
  initial begin
    a = 8'd10; b = 8'd32;
    #1 $display("sum = %0d", sum);
  end
endmodule
