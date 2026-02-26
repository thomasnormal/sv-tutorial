module tb;
  // Give each input a distinct constant so it's easy to confirm the right one was selected
  logic [7:0] a=8'hAA, b=8'hBB, c=8'hCC, d=8'hDD;
  logic [1:0] sel;
  logic [7:0] y;                   // output captured here

  int fail = 0;

  // Instantiate the design under test, connecting ports by name
  mux4 dut(.sel, .a, .b, .c, .d, .y);

  initial begin
    // Step through all four select values; each should route its input to y
    sel=0; #1 $display("sel=0 → y=%0h (expect aa)", y);
    if (y !== 8'hAA) fail++;
    sel=1; #1 $display("sel=1 → y=%0h (expect bb)", y);
    if (y !== 8'hBB) fail++;
    sel=2; #1 $display("sel=2 → y=%0h (expect cc)", y);
    if (y !== 8'hCC) fail++;
    sel=3; #1 $display("sel=3 → y=%0h (expect dd)", y);
    if (y !== 8'hDD) fail++;
    if (fail == 0) $display("PASS");
  end
endmodule
