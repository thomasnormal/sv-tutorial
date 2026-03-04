module tb;
  logic       clk = 0, rst_n;
  logic       we;
  logic [3:0] addr;
  logic [7:0] rdata;

  xcheck dut(.clk, .rst_n, .we, .addr, .rdata);

  always #5 clk = ~clk;

  initial begin
    // Hold in reset — assertions suppressed during this period
    rst_n = 0; we = 0; addr = 0; rdata = 0;
    @(posedge clk); #1;
    rst_n = 1;

    // Normal operation — no assertion fires
    @(posedge clk); #1; we = 1; addr = 4'd3;  rdata = 8'hA5;
    @(posedge clk); #1; we = 0; addr = 4'd3;  rdata = 8'hA5;
    @(posedge clk); #1; we = 0; addr = 4'd7;  rdata = 8'hFF;

    // Inject X on we — we_a fires
    @(posedge clk); #1; we = 'x;

    // Inject X on addr — addr_a fires
    @(posedge clk); #1; we = 0; addr = 'x;

    // Inject X on rdata — rdata_a fires (simulates uninitialized memory read)
    @(posedge clk); #1; addr = 0; rdata = 'x;

    @(posedge clk); #1;
    $display("PASS");
    $finish;
  end
endmodule
