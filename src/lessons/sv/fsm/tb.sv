module tb;
  logic clk=0, rst_n=0;
  always #5 clk = ~clk;

  // Host signals — simulate a simple bus master
  logic       cmd_valid=0, cmd_we=0;
  logic [3:0] cmd_addr=0;
  logic [7:0] cmd_wdata=0;

  // Controller outputs
  logic sram_we, ready;

  // Read data from SRAM
  logic [7:0] rdata;

  int fail = 0;

  // Memory controller (this lesson) gates SRAM access
  mem_ctrl ctrl(.clk, .rst_n, .cmd_valid, .cmd_we, .sram_we, .ready);

  // The SRAM from the parameters lesson — writes gated by the controller
  sram dut(
    .clk,
    .we   (sram_we),    // controller decides when to write
    .addr (cmd_addr),
    .wdata(cmd_wdata),
    .rdata
  );

  initial begin
    rst_n = 1;
    @(posedge clk); #1;
    $display("IDLE:  ready=%b (expect 1)", ready);
    if (ready !== 1'b1) fail++;

    // Issue a write command — controller gates the sram_we signal
    cmd_valid=1; cmd_we=1; cmd_addr=4'd3; cmd_wdata=8'd77;
    @(posedge clk); #1; cmd_valid=0;
    $display("WRITE: sram_we=%b (expect 1)", sram_we);
    if (sram_we !== 1'b1) fail++;

    @(posedge clk); #1;
    $display("IDLE:  ready=%b (expect 1)", ready);
    if (ready !== 1'b1) fail++;

    // Issue a read command — sram_we must stay 0
    cmd_valid=1; cmd_we=0; cmd_addr=4'd3;
    @(posedge clk); #1; cmd_valid=0;
    $display("READ:  sram_we=%b (expect 0)", sram_we);
    if (sram_we !== 1'b0) fail++;

    // Wait 1 more cycle for registered read output
    @(posedge clk); #1;
    $display("rdata=%0d (expect 77)", rdata);
    if (rdata !== 8'd77) fail++;

    if (fail == 0) $display("PASS");
    $finish;
  end
endmodule
