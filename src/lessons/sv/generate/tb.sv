module tb;
  logic [3:0] a4, b4, xor4, or4;
  logic [7:0] a8, b8, xor8;
  int         fail = 0;

  generate_lab #(.WIDTH(4), .USE_XOR(1'b1)) u_xor4(
    .a(a4), .b(b4), .y(xor4));
  generate_lab #(.WIDTH(4), .USE_XOR(1'b0)) u_or4(
    .a(a4), .b(b4), .y(or4));
  generate_lab #(.WIDTH(8), .USE_XOR(1'b1)) u_xor8(
    .a(a8), .b(b8), .y(xor8));

  initial begin
    a4 = 4'b1010;
    b4 = 4'b1100;
    a8 = 8'b1010_0101;
    b8 = 8'b0011_1100;
    #1;

    $display("4-bit XOR=%b (expect 0110), OR=%b (expect 1110)", xor4, or4);
    $display("8-bit XOR=%b (expect 1001_1001)", xor8);
    if (xor4 !== 4'b0110) fail++;
    if (or4  !== 4'b1110) fail++;
    if (xor8 !== 8'b1001_1001) fail++;

    if (fail == 0) $display("PASS");
    else $display("FAIL: %0d generated-logic checks were wrong", fail);
    $finish;
  end
endmodule
