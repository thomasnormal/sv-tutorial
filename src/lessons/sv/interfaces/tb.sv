module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  adder_if bus(.clk(clk));
  adder    dut(.bus(bus));

  initial begin
    bus.a = 8'd10;  bus.b = 8'd20;
    @(posedge clk); #1;
    $display("10 + 20 = %0d  carry=%b", bus.sum, bus.carry);

    bus.a = 8'd200; bus.b = 8'd100;
    @(posedge clk); #1;
    $display("200 + 100 = %0d  carry=%b", bus.sum, bus.carry);

    $finish;
  end
endmodule
