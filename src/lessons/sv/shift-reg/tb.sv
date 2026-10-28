module tb;
  logic       clk = 0;
  logic       rst_n = 0;
  logic       serial_in = 0;
  logic [3:0] q;
  logic       serial_out;
  int         fail = 0;

  always #5 clk = ~clk;

  shift_reg dut(.*);

  initial begin
    @(posedge clk); #1;
    if (q !== 4'b0000 || serial_out !== 1'b0) fail++;
    $display("reset: q=%b serial_out=%b (expect 0000, 0)", q, serial_out);

    rst_n = 1'b1;

    serial_in = 1'b1; @(posedge clk); #1;
    $display("in=1: q=%b serial_out=%b (expect 0001, 0)", q, serial_out);
    if (q !== 4'b0001 || serial_out !== 1'b0) fail++;

    serial_in = 1'b0; @(posedge clk); #1;
    $display("in=0: q=%b serial_out=%b (expect 0010, 0)", q, serial_out);
    if (q !== 4'b0010 || serial_out !== 1'b0) fail++;

    serial_in = 1'b1; @(posedge clk); #1;
    $display("in=1: q=%b serial_out=%b (expect 0101, 0)", q, serial_out);
    if (q !== 4'b0101 || serial_out !== 1'b0) fail++;

    serial_in = 1'b1; @(posedge clk); #1;
    $display("in=1: q=%b serial_out=%b (expect 1011, 0)", q, serial_out);
    if (q !== 4'b1011 || serial_out !== 1'b0) fail++;

    // Four zeroes flush the four input bits back out through serial_out.
    serial_in = 1'b0; @(posedge clk); #1;
    $display("flush 1: q=%b serial_out=%b (expect 0110, 1)", q, serial_out);
    if (q !== 4'b0110 || serial_out !== 1'b1) fail++;

    @(posedge clk); #1;
    $display("flush 2: q=%b serial_out=%b (expect 1100, 0)", q, serial_out);
    if (q !== 4'b1100 || serial_out !== 1'b0) fail++;

    @(posedge clk); #1;
    $display("flush 3: q=%b serial_out=%b (expect 1000, 1)", q, serial_out);
    if (q !== 4'b1000 || serial_out !== 1'b1) fail++;

    @(posedge clk); #1;
    $display("flush 4: q=%b serial_out=%b (expect 0000, 1)", q, serial_out);
    if (q !== 4'b0000 || serial_out !== 1'b1) fail++;

    if (fail == 0) $display("PASS");
    else $display("FAIL: %0d shift-register checks were wrong", fail);
    $finish;
  end
endmodule
