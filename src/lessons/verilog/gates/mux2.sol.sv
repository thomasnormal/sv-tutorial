module mux2(
  input  a,
  input  b,
  input  sel,
  output y
);
  wire sel_n, w1, w2;
  not u1 (sel_n, sel);
  and u2 (w1, a, sel_n);
  and u3 (w2, b, sel);
  or  u4 (y, w1, w2);
endmodule
