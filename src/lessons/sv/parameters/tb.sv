module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  // 8-deep × 4-bit SRAM
  logic [2:0] addr4; logic [3:0] wdata4, rdata4; logic we4;
  sram #(.DEPTH(8), .WIDTH(4)) u_small(
    .clk, .we(we4), .addr(addr4), .wdata(wdata4), .rdata(rdata4));

  // 256-deep × 16-bit SRAM
  logic [7:0] addr16; logic [15:0] wdata16, rdata16; logic we16;
  sram #(.DEPTH(256), .WIDTH(16)) u_large(
    .clk, .we(we16), .addr(addr16), .wdata(wdata16), .rdata(rdata16));

  initial begin
    // Write and read on the 8×4 instance
    we4=1; addr4=3'd5; wdata4=4'hA; @(posedge clk); #1;
    we4=0; addr4=3'd5; @(posedge clk); #1;
    $display("small[5] = %0h (expect a)", rdata4);

    // Write and read on the 256×16 instance
    we16=1; addr16=8'd200; wdata16=16'hBEEF; @(posedge clk); #1;
    we16=0; addr16=8'd200; @(posedge clk); #1;
    $display("large[200] = %0h (expect beef)", rdata16);

    $finish;
  end
endmodule
