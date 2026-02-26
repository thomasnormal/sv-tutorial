module event_sync;

  event write_done;
  event read_done;

  logic [7:0] mem [0:3];
  int         errors = 0;

  initial begin
    #10;
    mem[0] = 8'd10; mem[1] = 8'd20; mem[2] = 8'd30; mem[3] = 8'd40;
    $display("writer: stored 10 20 30 40");
    -> write_done;
  end

  initial begin
    @(write_done);
    if (mem[0] !== 8'd10 || mem[1] !== 8'd20) errors++;
    if (mem[2] !== 8'd30 || mem[3] !== 8'd40) errors++;
    $display("reader: %0d error(s)", errors);
    -> read_done;
  end

  initial begin
    @(read_done);
    if (errors == 0) $display("PASS");
    $finish;
  end

endmodule
