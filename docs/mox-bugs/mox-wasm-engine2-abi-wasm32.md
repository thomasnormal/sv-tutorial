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

On 2026-10-29, the prescribed item-7 attempt advanced to Mox `6176e563f6d4dc42e7c5b9af0c693e405d72f47b` with LLVM `e3e4f161d0160f10dc7cbd746abd639dd740ecde` and reached 4,216/5,058 WASM build tasks before failing in `GraphWireKinds.cpp`. Emscripten 4.0.21 and the required 20 GB / 8-job limits were active. The exact failure remained the nine wasm32 iterator type errors:

```
GraphWireKinds.cpp:25:15: error: variable 'found' with type 'const auto *' has incompatible initializer of type 'std::__wrap_iter<const mox::ImportVerilog::SourceScopeKind *>'
... the same error for SourceTypeKind, SourceParameterKind, SourceFactOriginKind,
DesignNodeKind, SourceGraphPreparation::Root::Role, SourceCallParentheses,
SourceCallArgumentShape, and SourceExpressionKind (9 errors generated).
ninja: build stopped: subcommand failed.
```

The lock was restored to `18483f66c8202c5bc4561abddd0f07bbfb54fbd8` / `aa3d6b37c7945bfb4c261dd994689de2a2de25bf`; no browser artifacts were synced.

After that attempt, a fresh fetch advanced `origin/main` to `76465a67826e7dc0ae91bbbbe27228933972af61`. Its `GraphWireKinds.cpp` is unchanged at the failing declaration, so the newer tip does not remove the blocker.

On 2026-10-29, the item-7 retry used Mox `48f113e4cf073d93a004126867e6b0aadcc5fbd4` with LLVM `e3e4f161d0160f10dc7cbd746abd639dd740ecde`. The GraphWireKinds compile passed, but the clean WASM build then failed in `tools/mox/tools/mox-sim/Engine2Emitter.cpp` (and, on the clean retry, `Engine2ProcessCells.cpp`) at the Engine 2 process-context layout assertion:

```
vendor/mox/tools/mox-sim/Engine2ProcessCells.h:62:15: error: static assertion failed due to requirement 'sizeof(mox::sim::emission::CompiledProcessContext) == 4 * sizeof(void *) + sizeof(unsigned long long)'
vendor/mox/tools/mox-sim/Engine2ProcessCells.h:62:46: note: expression evaluates to '32 == 24'
ninja: build stopped: subcommand failed.
```

The clean retry reached 5,027/5,058 tasks before the same assertion stopped the build. Because the wasm32 layout remains incompatible, the lock was restored to Mox `18483f66c8202c5bc4561abddd0f07bbfb54fbd8` / LLVM `aa3d6b37c7945bfb4c261dd994689de2a2de25bf`; no browser artifacts were synced.

On 2026-10-29, item 11 advanced the lock to Mox `b90b3a51a68b772a1510c837166afd6d429d8f20` (including landed Engine 2 fix `e82736e8877`) with LLVM `e3e4f161d0160f10dc7cbd746abd639dd740ecde`. `npm run check:req:wasm` passed with emsdk 4.0.21, but the guarded WASM build did not produce artifacts. The first build reached 435/5,050 tasks and failed because the host loader could not find the mamba runtime's atomic library:

```
/scratch/thomas-ahle/emsdk/upstream/bin/wasm-opt: error while loading shared libraries: libatomic.so.1: cannot open shared object file: No such file or directory
em++: error: error running binaryen executable (/scratch/thomas-ahle/emsdk/upstream/bin/wasm-opt). Please check your binaryen installation
ninja: build stopped: subcommand failed.
```

The prescribed clean retry then stopped during configure before linking any Mox target:

```
CMake Error at cmake/modules/CheckCompilerVersion.cmake:88 (message):
  libstdc++ version must be at least 7.4.
-- Configuring incomplete, errors occurred!
```

No wasm32 Engine 2 source assertion was reached after `e82736e8877`; `static/mox` was not regenerated. The exact build log is retained at `/var/tmp/thomas-ahle/fleet2/logs/sv-tutorial-build.log`.
