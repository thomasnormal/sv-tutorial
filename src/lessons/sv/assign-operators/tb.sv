module tb;
  logic [3:0]        a, b;
  logic              choose_a;
  logic signed [3:0] signed_a, signed_b;
  logic [3:0]        bitwise_and, bitwise_or, chosen, wrapped_sum;
  logic              any_set;
  logic [4:0]        full_sum;
  logic signed [3:0] signed_sum;
  int                fail = 0;

  operator_lab dut(.*);

  initial begin
    a = 4'b1010;
    b = 4'b0110;
    choose_a = 1'b0;
    signed_a = -3;
    signed_b = -2;
    #1;

    $display("a=%b b=%b  and=%b or=%b any=%b choose=%b", a, b,
             bitwise_and, bitwise_or, any_set, chosen);
    $display("unsigned sum: wrapped=%0d full=%0d; signed sum=%0d",
             wrapped_sum, full_sum, signed_sum);

    if (bitwise_and !== 4'b0010) fail++;
    if (bitwise_or  !== 4'b1110) fail++;
    if (any_set     !== 1'b1)    fail++;
    if (chosen      !== 4'b0110) fail++;
    if (wrapped_sum !== 4'd0)    fail++; // 10 + 6 = 16, truncated to 4 bits
    if (full_sum    !== 5'd16)   fail++; // the widened result preserves carry
    if (signed_sum  !== -5)      fail++; // signed two's-complement arithmetic

    choose_a = 1'b1;
    #1;
    if (chosen !== 4'b1010) fail++;

    if (fail == 0) $display("PASS");
    else $display("FAIL: %0d operator checks were wrong", fail);
    $finish;
  end
endmodule
