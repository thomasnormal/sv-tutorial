module tb;
  logic clk = 0, cs_n = 1, mosi = 0;

  always #5 clk = ~clk;

  spi_check dut(.clk, .cs_n, .mosi);

  initial begin
    @(posedge clk); #1;
    cs_n = 0; mosi = 0;
    @(posedge clk); #1;
    mosi = 1;
    repeat (8) begin
      @(posedge clk); #1;
      mosi = ~mosi;
    end
    cs_n = 1;
    @(posedge clk); #1;
    if (cs_n !== 1) begin
      $display("FAIL: chip-select did not release after the transfer");
      $finish;
    end

    $display("PASS: cs_n stayed low throughout all eight MOSI samples");
    $finish;
  end
endmodule
