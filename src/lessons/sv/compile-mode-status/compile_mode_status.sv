module tb;
  logic [3:0] left = 4'd2;
  logic [3:0] right = 4'd3;
  logic [4:0] sum;

  assign sum = left - right;

  initial begin
    #1;
    if (sum !== 5'd5) begin
      $display("FAIL: sum=%0d", sum);
      $finish;
    end
    $display("PASS: compile-ready design sum=%0d", sum);
    $finish;
  end
endmodule
