module top(output logic passed);
  // TODO: choose a signed 32-bit 2-state type for a testbench counter
  bit [31:0] count;

  // TODO: choose a 4-state 8-bit type so an RTL signal propagates X
  bit [7:0]  data;

  // TODO: make mem an unpacked array of four byte-wide elements
  logic [7:0] mem;

  // TODO: choose a signed 8-bit 2-state type for a testbench offset
  bit [7:0] delta;

  // TODO: choose a 4-state 4-bit type for an RTL status nibble
  bit [3:0] status;

  int fail = 0;

  initial begin
    passed = 1'b0;
    // A testbench counter must hold negative values
    count = -100;
    if (count < 0) $display("count = %0d  OK", count);
    else begin
      $display("FAIL count: %0d is not negative — use int, not bit [31:0]", count);
      fail++;
    end

    // A signed byte should retain a small negative offset
    delta = -5;
    if (delta < 0) $display("delta = %0d  OK", delta);
    else begin
      $display("FAIL delta: %0d is not negative — use a signed byte type", delta);
      fail++;
    end

    // An RTL signal must be able to hold the unknown value X
    data = 'x;
    if ($isunknown(data)) $display("data  = X     OK");
    else begin
      $display("FAIL data: 0x%02h is not X — use logic [7:0], not bit [7:0]", data);
      fail++;
    end

    // A small RTL status field must retain unknown bits
    status = 'x;
    if ($isunknown(status)) $display("status = X    OK");
    else begin
      $display("FAIL status: 0x%0h is not X — use a 4-state logic type", status);
      fail++;
    end

    // An unpacked array element must hold a full byte, not just one bit
    mem[0] = 8'hAB;
    mem[1] = 8'h12;
    if (mem[0] === 8'hAB && mem[1] === 8'h12) $display("mem[]  = {AB,12}  OK");
    else begin
      $display("FAIL mem: mem[0] is only 1 bit wide — add [4] after the name to make it an array");
      fail++;
    end

    if (fail == 0) $display("type checks complete");
    passed = (fail == 0);
  end
endmodule
