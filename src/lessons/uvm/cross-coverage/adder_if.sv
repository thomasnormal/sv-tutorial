interface adder_if (input logic clk);
  logic [7:0] a, b, sum;
  logic       carry;
  modport master(output a, b, input  clk, sum, carry);
  modport slave (input  a, b, output sum, carry);
endinterface
