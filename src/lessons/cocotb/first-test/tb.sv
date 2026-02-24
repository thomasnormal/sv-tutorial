// SystemVerilog equivalent of the cocotb test above.
// In a real project you would replace this with a Python cocotb testbench.
module tb;
  logic [3:0] A, B;
  logic [4:0] X;
  adder dut(.A, .B, .X);

  task automatic check(input logic [3:0] a, b, input logic [4:0] expected);
    A = a; B = b; #2;
    if (X === expected)
      $display("PASS  %0d + %0d = %0d", a, b, X);
    else
      $display("FAIL  %0d + %0d = %0d (expected %0d)", a, b, X, expected);
  endtask

  initial begin
    check(0,  0,  0);   // dut.A.value = 0;  dut.B.value = 0;  assert dut.X.value == 0
    check(9,  6,  15);  // dut.A.value = 9;  dut.B.value = 6;  assert dut.X.value == 15
    check(15, 15, 30);  // dut.A.value = 15; dut.B.value = 15; assert dut.X.value == 30
    check(8,  9,  17);  // dut.A.value = 8;  dut.B.value = 9;  assert dut.X.value == 17
  end
endmodule
