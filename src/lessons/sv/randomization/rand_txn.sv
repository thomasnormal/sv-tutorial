// Constrained randomization lets a class generate legal stimulus automatically.
// Mark fields with 'rand' so randomize() picks new values each call.
// Constraints are named boolean expressions that the solver must satisfy.

class rand_txn;
  // TODO: declare two rand fields
  //   rand logic [3:0] addr
  //   rand bit         we

  // TODO: add a constraint named 'low_bank_c' that restricts addr to [0:7]
  //   Hint: constraint low_bank_c { addr inside {[0:7]}; }
endclass

module rand_txn_tb;
  rand_txn t;

  initial begin
    t = new();

    // ── Scenario 1: default constraint active ─────────────────────────────
    $display("=== low_bank (addr 0-7) ===");
    repeat (4) begin
      void'(t.randomize());
      $display("  addr=%0d  we=%0b", t.addr, t.we);
      assert (t.addr inside {[0:7]}) else $fatal(1, "FAIL: addr out of range");
    end

    // ── Scenario 2: inline override — high bank ───────────────────────────
    $display("=== high_bank override (addr 8-15) ===");
    repeat (4) begin
      // TODO: call t.randomize() with an inline constraint { addr inside {[8:15]}; }
      //       then $display addr and we, then assert addr >= 8
      $display("  addr=%0d  we=%0b", t.addr, t.we);
    end

    // ── Scenario 3: disable constraint — full range ───────────────────────
    $display("=== no constraint (addr 0-15) ===");
    t.low_bank_c.constraint_mode(0);
    repeat (4) begin
      void'(t.randomize());
      $display("  addr=%0d  we=%0b", t.addr, t.we);
    end

    $display("PASS");
  end
endmodule
