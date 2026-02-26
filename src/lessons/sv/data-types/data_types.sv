module top;
  // TODO: change to int (2-state signed 32-bit — used for loop counters in testbenches)
  bit [31:0] count;

  // TODO: change to logic [7:0] (4-state — RTL signals must propagate X to catch bugs)
  bit [7:0]  data;

  int fail = 0;

  initial begin
    // A testbench counter must hold negative values
    count = -100;
    if (count < 0) $display("count = %0d  OK", count);
    else begin
      $display("FAIL count: %0d is not negative — use int, not bit [31:0]", count);
      fail++;
    end

    // An RTL signal must be able to hold the unknown value X
    data = 'x;
    if ($isunknown(data)) $display("data  = X     OK");
    else begin
      $display("FAIL data: 0x%02h is not X — use logic [7:0], not bit [7:0]", data);
      fail++;
    end

    if (fail == 0) $display("PASS");
    $finish;
  end
endmodule
