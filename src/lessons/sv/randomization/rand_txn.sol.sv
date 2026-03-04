class rand_txn;
  rand logic [3:0] addr;
  rand bit         we;

  constraint low_bank_c { addr inside {[0:7]}; }
endclass

module rand_txn_tb;
  rand_txn t;

  initial begin
    t = new();

    $display("=== low_bank (addr 0-7) ===");
    repeat (4) begin
      void'(t.randomize());
      $display("  addr=%0d  we=%0b", t.addr, t.we);
      assert (t.addr inside {[0:7]}) else $fatal(1, "FAIL: addr out of range");
    end

    $display("=== high_bank override (addr 8-15) ===");
    repeat (4) begin
      void'(t.randomize() with { addr inside {[8:15]}; });
      $display("  addr=%0d  we=%0b", t.addr, t.we);
      assert (t.addr >= 4'd8) else $fatal(1, "FAIL: addr not in high bank");
    end

    $display("=== no constraint (addr 0-15) ===");
    t.low_bank_c.constraint_mode(0);
    repeat (4) begin
      void'(t.randomize());
      $display("  addr=%0d  we=%0b", t.addr, t.we);
    end

    $display("PASS");
  end
endmodule
