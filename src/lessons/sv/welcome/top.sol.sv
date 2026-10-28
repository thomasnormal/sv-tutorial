module top(output logic greeted);
  initial begin
    $display("Hello, SRAM world!");
    greeted = 1'b1;
  end
endmodule
