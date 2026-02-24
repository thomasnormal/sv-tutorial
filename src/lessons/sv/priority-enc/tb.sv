module tb;
  logic [3:0] req;
  logic [1:0] grant;
  logic       valid;
  priority_enc dut(.req,.grant,.valid);
  initial begin
    req=4'b0000; #1 $display("req=%b grant=%0d valid=%b",req,grant,valid);
    req=4'b0001; #1 $display("req=%b grant=%0d valid=%b",req,grant,valid);
    req=4'b0110; #1 $display("req=%b grant=%0d valid=%b",req,grant,valid);
    req=4'b1010; #1 $display("req=%b grant=%0d valid=%b",req,grant,valid);
  end
endmodule
