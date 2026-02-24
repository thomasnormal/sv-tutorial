module tb;
  logic [7:0] a, b;
  logic [7:0] result;            // tb-level wire to capture the output

  // Instantiate the design under test, connecting ports by name
  adder dut(.a(a), .b(b), .sum(result));

  initial begin
    a = 8'd10; b = 8'd32;              // apply inputs
    #1 $display("sum = %0d", result);  // wait 1 time unit, then print result
  end
endmodule
