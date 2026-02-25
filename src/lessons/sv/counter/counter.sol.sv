module counter (
  input  logic       clk,    // clock: count updates on the rising edge
  input  logic       rst_n,  // active-low reset: holds count = 0 while low
  input  logic       en,     // enable: count only increments when this is 1
  output logic [7:0] count   // current counter value (0–255)
);
  always_ff @(posedge clk) begin
    if (!rst_n)  count <= 8'd0;
    else if (en) count <= count + 8'd1;
  end
endmodule
