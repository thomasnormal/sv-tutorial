# Lowered-library browser import boundary

Item 23 keeps the precompiled `uvm_pkg` artifact and the generic manifest-driven
consumer, but browser qualification is waiting on the Mox consumer tool.

The pinned mapped-Moore artifact is `static/mox/packages/uvm_pkg-b90b3a5.vlib`
(58,912,612 bytes; SHA-256
`058e528f971d915e06fe87499a3c895bd927d4dcb9f6f86bc5680c2dfe1ead11`). The
native receipt at Mox `b90b3a51a68b772a1510c837166afd6d429d8f20` is recorded in
`/tmp/svt-uvm-receipt-all.md`: source-backed rows complete in about 40–54 s,
while mapped-vlib rows take about 80–113 s and four rows time out at 120 s.
The browser `uvm/reporting` probe reached mapped-vlib diagnostics but did not
return within 900 s.

Interp's in-progress general consumer adds
`mox-run --read-vlib-lowered-library-ir=<file>` alongside ordinary sources.
The site adapter already supports this contract through a manifest `tool:
"run"` entry and path-qualified flags. The native rebuild check on 2026-11-03
failed before linking because the patch includes the nonexistent
`mlir/IR/SymbolInterfaces.h`; the generated interface is supplied through
`SymbolTable.h`. No browser `mox-run.js`/`.wasm` exists, and Mox's current
`tools/CMakeLists.txt` excludes `mox-run` when `EMSCRIPTEN` is enabled. The
manifest therefore remains on the validated mapped-vlib/mox-verilog path, and
UVM browser rows stay timeout-dispositioned until a browser-compatible lowered
library consumer is landed.
