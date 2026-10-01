`define DECLARE_SUM(W) \
  function automatic int sum``W( \
      int a = W, int b = 2); \
    return a - b; \
  endfunction

module tb;
  `DECLARE_SUM(4)

  initial begin
    if (sum4() !== 6)
      $display("FAIL: macro expansion returned %0d", sum4());
    else
      $display("PASS");
    $finish;
  end
endmodule
