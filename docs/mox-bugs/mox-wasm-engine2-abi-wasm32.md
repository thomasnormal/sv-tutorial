# Mox WASM build after Engine 2 wasm32 ABI fix

On 2026-10-28, the tutorial lane tested Mox `22e2d8e131c1d42de19d3c8fa330dfc4ca57c5d0` (the `origin/main` tip at the time, containing Engine 2 commit `92228f2b7b0`) with LLVM submodule `e3e4f161d0160f10dc7cbd746abd639dd740ecde` and the locked Emscripten 4.0.21 from `/scratch/thomas-ahle/emsdk`.

The first clean configure attempt reported the generic CMake error:

```
CMake Error at cmake/modules/CheckCompilerVersion.cmake:88 (message):
  libstdc++ version must be at least 7.4.
```

The configure log identified the environmental cause: Emscripten's `wasm-opt` could not load `libatomic.so.1`. Supplying `/var/tmp/thomas-ahle/mamba/envs/mox/lib` in `LD_LIBRARY_PATH` made the compiler checks pass and allowed the target build to proceed.

The subsequent WASM build stopped while compiling `tools/mox/lib/Conversion/ImportVerilog/ScopeCapture/GraphWireKinds.cpp`:

```
error: variable 'found' with type 'const auto *' has incompatible initializer of type 'std::__wrap_iter<const mox::ImportVerilog::SourceScopeKind *>'
error: variable 'found' with type 'const auto *' has incompatible initializer of type 'std::__wrap_iter<const mox::ImportVerilog::SourceTypeKind *>'
... (the same error for nine std::find instantiations)
ninja: build stopped: subcommand failed.
```

Because this source compile failure prevents generating browser artifacts, the tutorial keeps the previous lock (`MOX_REF_LOCKED=18483f66c8202c5bc4561abddd0f07bbfb54fbd8`, LLVM `aa3d6b37c7945bfb4c261dd994689de2a2de25bf`) and does not sync `static/mox`. Full output is retained at `/var/tmp/thomas-ahle/fleet2/logs/sv-tutorial-build.log`.

On 2026-10-29, a fresh fetch confirmed that Mox `origin/main` is `4db3fa211d27fcbdb50139e8c104b7076f72e2bc`. It contains `92228f2b7b0` but not the follow-up `6b4cf50d1b5` GraphWireKinds fix; the current file still declares `const auto *found = std::find(...)`. The lock therefore remains unchanged until that portability fix lands on main.
