// A three-process testbench pipeline for the SRAM.
// Writer, reader, and checker must run in order — events enforce that.
module event_sync;

  event write_done;   // writer → reader:  "memory is ready"
  event read_done;    // reader → checker: "verification complete"

  logic [7:0] mem [0:3];
  int         errors = 0;

  // ── Writer ────────────────────────────────────────────────────────────────
  // Fills the array after 10 time units, then signals it is done.
  initial begin
    #10;
    mem[0] = 8'd10; mem[1] = 8'd20; mem[2] = 8'd30; mem[3] = 8'd40;
    $display("writer: stored 10 20 30 40");
    // TODO: post write_done so the reader can start
  end

  // ── Reader ────────────────────────────────────────────────────────────────
  // Must wait for the writer, then check the values, then signal the checker.
  initial begin
    // TODO: wait for write_done before reading
    if (mem[0] !== 8'd10 || mem[1] !== 8'd20) errors++;
    if (mem[2] !== 8'd30 || mem[3] !== 8'd40) errors++;
    $display("reader: %0d error(s)", errors);
    // TODO: post read_done so the checker can report
  end

  // ── Checker ───────────────────────────────────────────────────────────────
  // Must wait for the reader before declaring the result.
  initial begin
    // TODO: wait for read_done before reporting
    if (errors == 0) $display("PASS");
    $finish;
  end

endmodule
