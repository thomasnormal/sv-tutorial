module adder(
  input  [3:0] a,
  input  [3:0] b,
  output [4:0] sum
);
  assign sum = a + b;
endmodule

module top;
  reg  [3:0] a, b;
  wire [4:0] sum;

  adder dut (.a(a), .b(b), .sum(sum));

  initial begin
    a = 4'd3; b = 4'd5;
    #10;
    $display("a=%0d b=%0d sum=%0d", a, b, sum);
    if (sum !== 5'd8) begin
      $display("FAIL: expected 8"); $finish;
    end

    a = 4'd15; b = 4'd1;
    #10;
    $display("a=%0d b=%0d sum=%0d", a, b, sum);
    if (sum !== 5'd16) begin
      $display("FAIL: expected 16"); $finish;
    end

    $display("ALL TESTS PASSED");
    $finish;
  end
endmodule
