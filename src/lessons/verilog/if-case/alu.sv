module alu(
  input  [7:0] a,
  input  [7:0] b,
  input  [1:0] op,      // 00=ADD, 01=SUB, 10=AND, 11=OR
  output reg [7:0] result
);
  // TODO: use a case statement on 'op' to compute result
  always @(*) begin
    result = 8'b0;
  end
endmodule
