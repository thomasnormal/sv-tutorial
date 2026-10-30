module tb;
  logic [7:0] packed_in, byte0, byte1;
  logic [7:0] packed_value, unpacked_total;
  logic [1:0] packed_lanes, unpacked_length;
  int fail = 0;

  arrays_lab dut(.*);

  initial begin
    packed_in = 8'b1011_0010;
    byte0 = 8'd17;
    byte1 = 8'd25;
    #1;

    $display("packed=%b (expect 10110010), unpacked sum=%0d (expect 42)",
             packed_value, unpacked_total);
    $display("packed lanes=%0d unpacked length=%0d (expect 2, 2)",
             packed_lanes, unpacked_length);
    if (packed_value !== 8'b1011_0010) fail++;
    if (unpacked_total !== 8'd42) fail++;
    if (packed_lanes !== 2'd2) fail++;
    if (unpacked_length !== 2'd2) fail++;

    packed_in = 8'h3C;
    byte0 = 8'hFF;
    byte1 = 8'h01;
    #1;
    $display("second packed=%h sum=%h", packed_value, unpacked_total);
    if (packed_value !== 8'h3C) fail++;
    if (unpacked_total !== 8'h00) fail++; // 0xFF + 1 wraps at 8 bits

    if (fail == 0) $display("PASS");
    else $display("FAIL: %0d static-array checks were wrong", fail);
    $finish;
  end
endmodule
