module mux2(
  input  a,
  input  b,
  input  sel,
  output y
);
  // TODO: build a 2:1 mux using and, or, not gates
  // y = (a & ~sel) | (b & sel)
  wire sel_n, w1, w2;
endmodule
