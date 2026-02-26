// The adder from Part 1 — expressed as CIRCT MLIR.
//
// Every MLIR file is a sequence of operations.
// Here there is one top-level operation: hw.module.
//
// hw.module corresponds to a SystemVerilog module declaration.
// Ports are written as  in %name : type  or  out name : type.
// The body between { } is a region — a list of operations that
// execute as a graph (all concurrently, no ordering between them).

hw.module @adder(in %a : i8, in %b : i8, out sum : i8) {

  // %0 is a Value — an SSA name for the result of this operation.
  // It can be used as many times as needed, but is defined exactly once.
  // comb.add is the operation.  %a and %b are its operands.
  // : i8 is the type of the result (8-bit signless integer).
  %0 = comb.add %a, %b : i8

  // hw.output is the module terminator.  It assigns the output ports.
  hw.output %0 : i8
}
