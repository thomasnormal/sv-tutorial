module concurrent_tb;

  task automatic delay_print(int cycles, string msg);
    #(cycles * 10);
    $display("[%0t ns] %s", $time, msg);
  endtask

  initial begin
    $display("--- fork...join ---");
    fork
      delay_print(3, "thread A (30 ns)");
      delay_print(1, "thread B (10 ns)");
      delay_print(2, "thread C (20 ns)");
    join
    $display("all done at %0t ns", $time);

    $display("--- fork...join_any ---");
    fork
      delay_print(3, "thread A (30 ns)");
      delay_print(1, "thread B (10 ns)");
      delay_print(2, "thread C (20 ns)");
    join_any
    $display("first done at %0t ns", $time);

    $display("--- fork...join_none ---");
    fork
      delay_print(2, "background (20 ns)");
    join_none
    $display("parent continues at %0t ns", $time);

    #50;
    $display("PASS");
  end
endmodule
