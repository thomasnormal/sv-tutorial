module source(input logic clk, output logic valid);
  initial valid = 1'b0;
  always @(negedge clk) valid <= 1'b1;
  always @(posedge clk) valid <= 1'b0;
endmodule

module sink(input logic clk, input logic valid, output logic seen);
  initial seen = 1'b0;
  always @(posedge clk)
    if (valid) seen <= 1'b1;
endmodule

module wrapper(input logic clk, input logic valid, output logic seen);
  sink inner(clk, 1'b0, seen);
endmodule

module tb;
  logic clk = 1'b0;
  logic valid;
  logic direct_seen;
  logic nested_seen;
  source src(clk, valid);
  sink direct(clk, valid, direct_seen);
  wrapper nested(clk, valid, nested_seen);
  always #5 clk = ~clk;

  initial begin
    #16;
    if (direct_seen !== 1'b1 || nested_seen !== 1'b1)
      $display("FAIL: direct=%b nested=%b", direct_seen, nested_seen);
    else
      $display("PASS");
    $finish;
  end
endmodule
