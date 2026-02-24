module tb;
  logic [1:0]  sel;
  logic [7:0]  a=8'hAA, b=8'hBB, c=8'hCC, d=8'hDD, y;
  mux4 dut(.sel,.a,.b,.c,.d,.y);
  initial begin
    sel=0; #1 $display("sel=0 y=%0h",y);
    sel=1; #1 $display("sel=1 y=%0h",y);
    sel=2; #1 $display("sel=2 y=%0h",y);
    sel=3; #1 $display("sel=3 y=%0h",y);
  end
endmodule
