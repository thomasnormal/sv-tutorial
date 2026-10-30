import typedef_pkg::*;

module tb;
  data_t left, right;
  lane_t lane;
  data_t result;
  logic [1:0] lane_copy;
  int fail = 0;

  typedef_lab dut(.*);

  initial begin
    left = 8'h12;
    right = 8'h23;
    lane = 2'b10;
    #1;
    $display("left=%h right=%h sum^lane=%h lane_copy=%b", left, right, result, lane_copy);
    if (result !== 8'h37) fail++; // 0x12 + 0x23 = 0x35; XOR with 2 = 0x37
    if (lane_copy !== 2'b10) fail++;

    left = 8'hF0;
    right = 8'h0F;
    lane = 2'b01;
    #1;
    $display("left=%h right=%h sum^lane=%h lane_copy=%b", left, right, result, lane_copy);
    if (result !== 8'hFE) fail++; // 0xFF XOR 1 = 0xFE; the 8-bit sum wraps to FF.
    if (lane_copy !== 2'b01) fail++;

    if (fail == 0) $display("PASS");
    else $display("FAIL: %0d typedef checks were wrong", fail);
    $finish;
  end
endmodule
