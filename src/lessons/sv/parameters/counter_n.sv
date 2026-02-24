module counter_n (
  // TODO: add #(parameter int N = 8)
  input  logic       clk, rst_n, en,
  output logic [7:0] count  // TODO: change to [N-1:0]
);
  // TODO: add localparam int MAX = (1 << N) - 1;
  always_ff @(posedge clk)
    if (!rst_n)  count <= '0;
    else if (en) count <= count + 1'b1;
endmodule
