// priority_enc.sv — rewritten as CIRCT MLIR.
//
// The comb dialect represents purely combinational logic:
// no state, no clock, no side effects.
// The same inputs always produce the same outputs.
//
// A casez priority encoder becomes a chain of comb.mux operations.
// comb.mux %sel, %on_true, %on_false : T
//   ≈  sel ? on_true : on_false
//
// comb.extract %value from N : (iW) -> iK
//   slices K bits starting at bit N from a W-bit value.

hw.module @priority_enc(in %req : i4,
                        out grant : i2,
                        out valid : i1) {

  // Compile-time constants
  %c0 = hw.constant 0 : i2
  %c1 = hw.constant 1 : i2
  %c2 = hw.constant 2 : i2
  %c3 = hw.constant 3 : i2

  // Extract individual request bits
  %req0 = comb.extract %req from 0 : (i4) -> i1
  %req1 = comb.extract %req from 1 : (i4) -> i1
  %req2 = comb.extract %req from 2 : (i4) -> i1
  %req3 = comb.extract %req from 3 : (i4) -> i1

  // Priority chain: req[3] wins over req[2] over req[1] over req[0].
  // This is the comb equivalent of nested casez branches.
  %g01   = comb.mux %req1, %c1, %c0  : i2
  %g012  = comb.mux %req2, %c2, %g01 : i2
  %grant = comb.mux %req3, %c3, %g012 : i2

  // valid = req[3] | req[2] | req[1] | req[0]
  // comb.or is variadic — takes any number of same-typed operands.
  %valid = comb.or %req0, %req1, %req2, %req3 : i1

  hw.output %grant, %valid : i2, i1
}
