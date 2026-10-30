module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  mem_if bus(.clk(clk));
  sram   dut(.bus(bus));

  int fail = 0;

  initial begin
    // Write address 4 with data 88
    bus.we = 1; bus.addr = 4'd4; bus.wdata = 8'd88;
    @(posedge clk); #1;
    $display("wrote:  %s", bus.sprint());
    if (bus.sprint() != "we=1 addr=4 wdata=58 rdata=x") fail++;
    bus.we = 0;

    // Read back — 1-cycle registered latency
    bus.addr = 4'd4;
    @(posedge clk); #1;
    $display("read:   %s", bus.sprint());
    if (bus.sprint() != "we=0 addr=4 wdata=58 rdata=58") fail++;
    if (bus.rdata !== 8'd88) fail++;

    // Write address 11 with data 200
    bus.we = 1; bus.addr = 4'd11; bus.wdata = 8'd200;
    @(posedge clk); #1;
    $display("wrote:  %s", bus.sprint());
    if (bus.sprint() != "we=1 addr=b wdata=c8 rdata=x") fail++;
    bus.we = 0;

    bus.addr = 4'd11;
    @(posedge clk); #1;
    $display("read:   %s", bus.sprint());
    if (bus.sprint() != "we=0 addr=b wdata=c8 rdata=c8") fail++;
    if (bus.rdata !== 8'd200) fail++;

    if (fail == 0) $display("PASS");
    $finish;
  end
endmodule
