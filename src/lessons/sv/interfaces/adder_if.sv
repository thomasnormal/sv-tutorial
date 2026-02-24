// Bundle all adder signals into one reusable port.
interface adder_if (input logic clk);
  logic [7:0] a, b, sum;
  logic       carry;

  // TODO: modport master(output a, b, input  clk, sum, carry);
  // TODO: modport slave (input  a, b, output sum, carry);
endinterface
