// fork...join spawns parallel threads — all must finish before the parent continues.
// fork...join_any — parent resumes when the *first* thread finishes.
// fork...join_none — parent continues immediately; threads run in the background.

module concurrent_tb;

  // Helper: print a message after a delay
  task automatic delay_print(int cycles, string msg);
    #(cycles * 10);
    $display("[%0t ns] %s", $time, msg);
  endtask

  initial begin
    // ── fork...join — wait for ALL threads ────────────────────────────────
    // (given — shows the pattern)
    $display("--- fork...join ---");
    fork
      delay_print(3, "thread A (30 ns)");
      delay_print(1, "thread B (10 ns)");
      delay_print(2, "thread C (20 ns)");
    join
    $display("all done at %0t ns", $time);  // prints at 30 ns

    // ── fork...join_any — wait for FIRST thread ────────────────────────────
    // TODO: launch the same three delay_print calls.
    //       After join_any, $display "first done at <time> ns".
    //       Expected: continues at 10 ns after fork (40 ns total).
    $display("--- fork...join_any ---");

    // ── fork...join_none — fire and forget ────────────────────────────────
    // TODO: launch delay_print(2, "background (20 ns)") inside fork...join_none.
    //       Then immediately $display "parent continues at <time> ns"
    //       (should print before the background thread finishes).
    $display("--- fork...join_none ---");

    #50;  // let background threads finish
    $display("PASS");
  end
endmodule
