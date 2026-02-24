import { VPI_WORKER_CONST_SOURCE } from './vpi-abi.js';
import { WORKER_RUNTIME_HELPERS_SOURCE } from './worker-runtime-helpers-source.js';

export const COCOTB_WORKER_SOURCE = String.raw`
${VPI_WORKER_CONST_SOURCE}
${WORKER_RUNTIME_HELPERS_SOURCE}

function wsWriteString(M, str) {
  var bytes = new TextEncoder().encode(str + '\0');
  var ptr = M._malloc(bytes.length);
  M.HEAPU8.set(bytes, ptr);
  return ptr;
}

function wsMakeVpiTime(M, fsBI) {
  var ps = BigInt(fsBI) / 1000n;
  var hi = Number(ps >> 32n) >>> 0;
  var lo = Number(ps & 0xFFFFFFFFn) >>> 0;
  var ptr = M._malloc(VPI_LAYOUT.vpiTime.size);
  M.setValue(ptr + VPI_LAYOUT.vpiTime.type, VPI.vpiSimTime, 'i32');
  M.setValue(ptr + VPI_LAYOUT.vpiTime.high, hi, 'i32');
  M.setValue(ptr + VPI_LAYOUT.vpiTime.low, lo, 'i32');
  M.setValue(ptr + VPI_LAYOUT.vpiTime.real, 0.0, 'double');
  return ptr;
}

function wsMakeCbData(M, reason, cbRtn, obj, time, userData) {
  var ptr = M._malloc(VPI_LAYOUT.cbData.size);
  M.setValue(ptr + VPI_LAYOUT.cbData.reason, reason || 0, 'i32');
  M.setValue(ptr + VPI_LAYOUT.cbData.cbRtn, cbRtn || 0, 'i32');
  M.setValue(ptr + VPI_LAYOUT.cbData.obj, obj || 0, 'i32');
  M.setValue(ptr + VPI_LAYOUT.cbData.time, time || 0, 'i32');
  M.setValue(ptr + VPI_LAYOUT.cbData.value, 0, 'i32');
  M.setValue(ptr + VPI_LAYOUT.cbData.index, 0, 'i32');
  M.setValue(ptr + VPI_LAYOUT.cbData.userData, userData || 0, 'i32');
  return ptr;
}

function wsMakeVpiValue(M, intVal) {
  var ptr = M._malloc(VPI_LAYOUT.vpiValue.size);
  M.setValue(ptr + VPI_LAYOUT.vpiValue.format, VPI.vpiIntVal, 'i32');
  M.setValue(ptr + VPI_LAYOUT.vpiValue.integer, intVal | 0, 'i32');
  return ptr;
}

function wsReadVpiIntValue(M, ptr) {
  return M.getValue(ptr + VPI_LAYOUT.vpiValue.integer, 'i32');
}

function wsRegisterVpiTrigger(M, spec, cbFnPtr) {
  if (spec.type === 'timer') {
    var timePtr = wsMakeVpiTime(M, BigInt(spec.fs));
    var cbData = wsMakeCbData(M, VPI.cbAfterDelay, cbFnPtr, 0, timePtr, spec.id);
    var handle = M._vpi_register_cb(cbData);
    M._free(timePtr);
    M._free(cbData);
    return handle;
  }
  if (spec.type === 'rising_edge' || spec.type === 'falling_edge') {
    var namePtr = wsWriteString(M, spec.signal);
    var sigHandle = M._vpi_handle_by_name(namePtr, 0);
    M._free(namePtr);
    var cbData2 = wsMakeCbData(M, VPI.cbValueChange, cbFnPtr, sigHandle, 0, spec.id);
    var handle2 = M._vpi_register_cb(cbData2);
    M._free(cbData2);
    return handle2;
  }
  return 0;
}

function wsVpiGetSignalValue(M, name) {
  var namePtr = wsWriteString(M, name);
  var handle = M._vpi_handle_by_name(namePtr, 0);
  M._free(namePtr);
  if (!handle) return 0;
  var vp = wsMakeVpiValue(M, 0);
  M._vpi_get_value(handle, vp);
  var result = wsReadVpiIntValue(M, vp);
  M._free(vp);
  return result;
}

function wsVpiSetSignalValue(M, name, val) {
  var namePtr = wsWriteString(M, name);
  var handle = M._vpi_handle_by_name(namePtr, 0);
  M._free(namePtr);
  if (!handle) return;
  var vp = wsMakeVpiValue(M, val);
  M._vpi_put_value(handle, vp, 0, 0);
  M._free(vp);
}

function isExitException(err) {
  var t = String((err && err.message) || err || '');
  return t.includes('ExitStatus') || t.includes('Program terminated') || t.includes('exit(');
}

// WASM: (i32) -> (i32), returns 0
var WS_NOOP_CB_WASM = new Uint8Array([
  0x00,0x61,0x73,0x6d, 0x01,0x00,0x00,0x00,
  0x01,0x06,0x01,0x60,0x01,0x7f,0x01,0x7f,
  0x03,0x02,0x01,0x00,
  0x07,0x05,0x01,0x01,0x66,0x00,0x00,
  0x0a,0x06,0x01,0x04,0x00,0x41,0x00,0x0b
]);

// WASM: () -> (), imports env.r and calls it.
var WS_STARTUP_CB_WASM = new Uint8Array([
  0x00,0x61,0x73,0x6d, 0x01,0x00,0x00,0x00,
  0x01,0x04, 0x01,0x60,0x00,0x00,
  0x02,0x09, 0x01, 0x03,0x65,0x6e,0x76, 0x01,0x72, 0x00,0x00,
  0x03,0x02, 0x01,0x00,
  0x07,0x05, 0x01, 0x01,0x66, 0x00,0x01,
  0x0a,0x06, 0x01,0x04, 0x00,0x10,0x00,0x0b
]);

function wsAddFunctionToTable(wasmBytes, imports) {
  try {
    var mod = new WebAssembly.Module(wasmBytes);
    var inst = new WebAssembly.Instance(mod, imports || {});
    var tbl = (typeof wasmTable !== 'undefined') ? wasmTable : null;
    if (!tbl) return 0;
    // Scan the tail of the table for a null (empty) slot; avoid grow()
    // since Emscripten may compile with a fixed table maximum.
    var slot = -1;
    var len = tbl.length;
    for (var i = Math.max(1, len - 512); i < len; i++) {
      if (tbl.get(i) === null) { slot = i; break; }
    }
    if (slot < 0) {
      // Full scan as last resort.
      for (var j = 1; j < len && slot < 0; j++) {
        if (tbl.get(j) === null) slot = j;
      }
    }
    if (slot < 0) {
      // Table is completely full — try growing.
      try { slot = tbl.length; tbl.grow(1); } catch(_g) { return 0; }
    }
    tbl.set(slot, inst.exports.f);
    return slot;
  } catch(e) { return 0; }
}

function makeSimInMemFS(stdout, stderr) {
  var store = {};
  var symlinks = {};
  var dirs = new Set(['/', '/dev', '/workspace', '/workspace/src', '/workspace/out']);
  var fds = {};
  var nextFd = 3;

  function ensureParentDir(path) {
    var parts = String(path).split('/').filter(Boolean);
    var cur = '';
    for (var i = 0; i < parts.length - 1; i++) { cur += '/' + parts[i]; dirs.add(cur); }
  }

  function makeStat(path) {
    path = String(path);
    if (symlinks[path]) {
      return { ino: 3, mode: 0o120777, size: symlinks[path].length, dev: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
               blksize: 4096, blocks: 1, atime: new Date(), mtime: new Date(), ctime: new Date(),
               isDirectory: function(){return false;}, isFile: function(){return false;},
               isSymbolicLink: function(){return true;} };
    }
    if (dirs.has(path)) {
      return { ino: 1, mode: 0o40755, size: 0, dev: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
               blksize: 4096, blocks: 0, atime: new Date(), mtime: new Date(), ctime: new Date(),
               isDirectory: function(){return true;}, isFile: function(){return false;},
               isSymbolicLink: function(){return false;} };
    }
    if (store[path]) {
      return { ino: 2, mode: 0o100644, size: store[path].length, dev: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
               blksize: 4096, blocks: Math.ceil(store[path].length / 512),
               atime: new Date(), mtime: new Date(), ctime: new Date(),
               isDirectory: function(){return false;}, isFile: function(){return true;},
               isSymbolicLink: function(){return false;} };
    }
    var e = new Error('ENOENT: no such file or directory, stat \'' + path + '\'');
    e.code = 'ENOENT'; throw e;
  }

  var nodeApi = {
    readFileSync: function(path, opts) {
      path = String(path);
      if (!store[path]) { var e = new Error('ENOENT: ' + path); e.code = 'ENOENT'; throw e; }
      var enc = (typeof opts === 'string') ? opts : (opts && opts.encoding);
      return enc ? new TextDecoder().decode(store[path]) : store[path];
    },
    existsSync: function(p) { return dirs.has(p) || !!store[p] || !!symlinks[p]; },
    statSync: makeStat,
    lstatSync: makeStat,
    realpathSync: function(p) {
      var path = String(p);
      return symlinks[path] || path;
    },
    readlinkSync: function(p) {
      var path = String(p);
      if (symlinks[path]) return symlinks[path];
      var e = new Error('EINVAL: invalid argument, readlink \'' + path + '\'');
      e.code = 'EINVAL';
      throw e;
    },
    symlinkSync: function(target, path) {
      var link = String(path);
      ensureParentDir(link);
      symlinks[link] = String(target);
    },
    fstatSync: function(fd) {
      var f = fds[fd]; if (!f) { var e = new Error('EBADF'); e.code = 'EBADF'; throw e; }
      return makeStat(f.path);
    },
    readdirSync: function(path) {
      if (!dirs.has(path)) { var e = new Error('ENOENT: ' + path); e.code = 'ENOENT'; throw e; }
      var prefix = path === '/' ? '/' : path + '/';
      var entries = new Set();
      dirs.forEach(function(d) {
        if (d !== path && d.startsWith(prefix)) {
          var rel = d.slice(prefix.length);
          if (rel.indexOf('/') < 0) entries.add(rel);
        }
      });
      Object.keys(store).forEach(function(f) {
        if (f.startsWith(prefix)) {
          var rel = f.slice(prefix.length);
          if (rel.indexOf('/') < 0) entries.add(rel);
        }
      });
      return Array.from(entries);
    },
    mkdirSync: function(p) { dirs.add(String(p)); },
    rmdirSync: function(p) { dirs.delete(p); },
    unlinkSync: function(p) { delete store[p]; delete symlinks[p]; },
    renameSync: function(from, to) {
      if (store[from]) { store[to] = store[from]; delete store[from]; }
      if (symlinks[from]) { symlinks[to] = symlinks[from]; delete symlinks[from]; }
    },
    chmodSync: function() {}, chownSync: function() {}, utimesSync: function() {}, fsyncSync: function() {},
    ftruncateSync: function(fd, len) {
      var f = fds[fd]; var d = store[f.path] || new Uint8Array(0);
      store[f.path] = len <= d.length ? d.subarray(0, len) : (function(){ var g = new Uint8Array(len); g.set(d); return g; })();
    },
    openSync: function(path, flags) {
      path = String(path);
      var writable;
      if (typeof flags === 'string') {
        writable = flags.indexOf('w') >= 0 || flags.indexOf('a') >= 0 || flags.indexOf('+') >= 0;
      } else {
        var numericFlags = Number(flags) || 0;
        var accessMode = numericFlags & 3; // O_RDONLY=0, O_WRONLY=1, O_RDWR=2
        writable = accessMode !== 0 || !!(numericFlags & 64) || !!(numericFlags & 512) || !!(numericFlags & 1024);
      }
      if (writable) { store[path] = new Uint8Array(0); ensureParentDir(path); }
      else if (!store[path] && !dirs.has(path)) { var e = new Error('ENOENT: ' + path); e.code = 'ENOENT'; throw e; }
      var fd = nextFd++; fds[fd] = { path: path, pos: 0 }; return fd;
    },
    closeSync: function(fd) { delete fds[fd]; },
    readSync: function(fd, buf, bufOffset, length, position) {
      if (fd === 0) return 0;
      var f = fds[fd]; var data = store[f.path] || new Uint8Array(0);
      var pos = position != null ? position : f.pos;
      var avail = Math.min(length, data.length - pos);
      if (avail <= 0) return 0;
      buf.set(data.subarray(pos, pos + avail), bufOffset);
      if (position == null) f.pos += avail;
      return avail;
    },
    writeSync: function(fd, buf, bufOffset, length, position) {
      var src;
      if (typeof buf === 'string') {
        src = new TextEncoder().encode(buf);
      } else if (ArrayBuffer.isView(buf)) {
        src = new Uint8Array(buf.buffer, buf.byteOffset, buf.byteLength);
      } else if (buf instanceof ArrayBuffer) {
        src = new Uint8Array(buf);
      } else {
        src = new Uint8Array(0);
      }
      var start = Number.isFinite(bufOffset) ? Number(bufOffset) : 0;
      if (start < 0) start = 0;
      var writeLen = Number.isFinite(length) ? Number(length) : (src.length - start);
      if (writeLen < 0) writeLen = 0;
      var end = Math.min(src.length, start + writeLen);
      var chunk = src.subarray(start, end);
      if (fd === 1) { stdout.push(new TextDecoder().decode(chunk)); return chunk.length; }
      if (fd === 2) { stderr.push(new TextDecoder().decode(chunk)); return chunk.length; }
      var f = fds[fd]; var pos = position != null ? position : f.pos;
      var data = store[f.path] || new Uint8Array(0);
      var needed = pos + chunk.length;
      if (needed > data.length) { var g = new Uint8Array(needed); g.set(data); data = g; }
      data.set(chunk, pos); store[f.path] = data;
      if (position == null) f.pos += chunk.length;
      return chunk.length;
    },
  };

  return {
    nodeApi: nodeApi,
    // Write a text file before the module loads (used to pre-populate MLIR).
    writeTextFile: function(path, text) {
      var bytes = new TextEncoder().encode(text);
      ensureParentDir(path);
      store[path] = bytes;
    },
  };
}

self.onmessage = async function(event) {
  var req = event.data || {};
  var simJsUrl   = req.simJsUrl;
  var simWasmUrl = req.simWasmUrl;
  var pyodideUrl = req.pyodideUrl;
  var mlir       = req.mlir;
  var topModule  = req.topModule;
  var pyCode     = req.pyCode;
  var shimCode   = req.shimCode;
  var maxTimeNs  = req.maxTimeNs || 1000000;

  var simStdout = [];
  var simStderr = [];
  var logs = [];
  function onLog(msg) {
    var line = String(msg);
    logs.push(line);
    self.postMessage({ type: 'log', line: line });
  }
  async function runPyodideTicks(pyodide, shouldStop, phase) {
    for (var i = 0; i < 20; i++) {
      try {
        await pyodide.runPythonAsync('await __import__("asyncio").sleep(0)');
      } catch(e) {
        var suffix = phase ? ' (' + phase + ')' : '';
        onLog('[cocotb] runPythonAsync error at i=' + i + suffix + ': ' + e);
        break;
      }
      if (shouldStop()) break;
    }
  }

  try {
    // ── 1. Load the VPI circt-sim WASM ───────────────────────────────────────
    // Fetch the JS source first so we can detect NODERAWFS=1 (recognisable by
    // the unconditional require('path') / require('fs') calls at module level).
    onLog('[cocotb] Loading simulator...');
    var simInMemFS = null;
    var simReady = false;
    self.Module = {
      noInitialRun: true,
      onRuntimeInitialized: function() { simReady = true; },
      print:    function(line) { onLog('[sim] ' + line); },
      printErr: function(line) { onLog('[sim] ' + line); },
      locateFile: function(path) { return path.endsWith('.wasm') ? simWasmUrl : path; },
      instantiateWasm: function(imports, callback) {
        // Wrap _circt_vpi_wasm_yield (import 'r') with Asyncify.handleAsync so
        // WASM calls to the yield import trigger Asyncify unwind/rewind instead
        // of running synchronously (instrumentWasmImports is never called by the
        // compiled artifact's createWasm(), so we must wrap here ourselves).
        if (typeof Asyncify !== 'undefined' && imports && imports.a && typeof imports.a.r === 'function') {
          var _origYield = imports.a.r;
          imports.a.r = function() {
            var _args = arguments;
            return Asyncify.handleAsync(function() { return _origYield.apply(null, _args); });
          };
        }
        WebAssembly.instantiateStreaming(fetch(simWasmUrl), imports)
          .then(function(r) { callback(r.instance, r.module); })
          .catch(function() {
            fetch(simWasmUrl)
              .then(function(r) { return r.arrayBuffer(); })
              .then(function(buf) { return WebAssembly.instantiate(buf, imports); })
              .then(function(r) { callback(r.instance, r.module); });
          });
        return {};
      }
    };
    await loadEmscriptenTool({
      jsUrl: simJsUrl,
      pathShim: WORKER_PATH_SHIM,
      makeFs: function() {
        simInMemFS = makeSimInMemFS(simStdout, simStderr);
        return simInMemFS;
      },
      onStdout: function(s) { simStdout.push(String(s)); },
      onStderr: function(s) { simStderr.push(String(s)); }
    });

    // Wait for the runtime to initialize and VPI exports to be ready.
    var simModule = await new Promise(function(resolve, reject) {
      var start = Date.now();
      function tick() {
        try {
          var m = self.Module;
          if (m && typeof m.callMain !== 'function' && typeof self.callMain === 'function') {
            m.callMain = self.callMain;
          }
          if (simReady && m && typeof m.callMain === 'function') {
            resolve(m); return;
          }
          if (Date.now() - start >= 45000) {
            reject(new Error('VPI sim module did not become ready in time'));
            return;
          }
          setTimeout(tick, 25);
        } catch(e) { reject(e); }
      }
      tick();
    });

    // ── 1b. Patch Module to expose Emscripten internals needed by VPI helpers ─
    // circt-sim-vpi.js assigns _malloc/_free to module-level globals but not to
    // Module["_malloc"] / Module["_free"].  setValue/getValue and HEAPU8 are
    // absent from EXPORTED_RUNTIME_METHODS for this build.  After importScripts
    // (or indirect eval) these become worker-scope globals we can forward.
    if (typeof simModule._malloc !== 'function') {
      simModule._malloc = function(size) { return _malloc(size); };
    }
    if (typeof simModule._free !== 'function') {
      simModule._free = function(ptr) { _free(ptr); };
    }
    if (typeof simModule.getValue !== 'function') {
      simModule.getValue = function(ptr, type) {
        if (type === 'i32')    return HEAP32[ptr >>> 2];
        if (type === 'double') return HEAPF64[ptr >>> 3];
        return 0;
      };
    }
    if (typeof simModule.setValue !== 'function') {
      simModule.setValue = function(ptr, value, type) {
        if (type === 'i32')    { HEAP32[ptr >>> 2] = value | 0; }
        else if (type === 'double') { HEAPF64[ptr >>> 3] = +value; }
      };
    }
    if (!simModule.HEAPU8) {
      Object.defineProperty(simModule, 'HEAPU8', {
        get: function() { return HEAPU8; },
        configurable: true
      });
    }
    if (!simModule.FS && typeof FS !== 'undefined') {
      simModule.FS = FS;
    }

    // ── 2. Write MLIR to the virtual FS ──────────────────────────────────────
    var mlirPath = '/workspace/out/design.llhd.mlir';
    if (simInMemFS) {
      // NODERAWFS mode: pre-populate the store so callMain can read the file.
      simInMemFS.writeTextFile(mlirPath, mlir);
    } else if (simModule.FS && typeof simModule.FS.writeFile === 'function') {
      try { simModule.FS.mkdir('/workspace'); } catch(_) {}
      try { simModule.FS.mkdir('/workspace/out'); } catch(_) {}
      simModule.FS.writeFile(mlirPath, mlir, { encoding: 'utf8' });
    }

    // ── 3. Load Pyodide ───────────────────────────────────────────────────────
    onLog('[cocotb] Loading Pyodide...');
    importScripts(pyodideUrl);
    var pyodide = await loadPyodide({ stdout: onLog, stderr: onLog });
    onLog('[cocotb] Pyodide ready');

    // ── 4. Install JS→Python bridge on the worker global scope ───────────────
    var _pendingRegistrations = [];
    var _triggerSpecs = {};   // id -> spec, kept for edge-direction filtering
    var _testsDone = false;
    var _testsOk   = false;

    self._cocotb_register_trigger = function(jsonStr) {
      var spec = JSON.parse(jsonStr);
      _pendingRegistrations.push(spec);
      _triggerSpecs[spec.id] = spec;
    };
    self._cocotb_get_signal = function(name) {
      return wsVpiGetSignalValue(simModule, String(name));
    };
    self._cocotb_set_signal = function(name, val) {
      wsVpiSetSignalValue(simModule, String(name), Number(val));
    };
    self._cocotb_log = function(msg) { onLog(String(msg)); };
    // Python passes allPassed as a boolean; Pyodide converts it to JS boolean.
    self._cocotb_tests_done = function(allPassed) { _testsDone = true; _testsOk = !!allPassed; };

    // ── 5. Install the cocotb shim into Pyodide ───────────────────────────────
    pyodide.runPython(shimCode);
    pyodide.runPython("import sys; sys.modules['cocotb'] = sys.modules[__name__]");

    // ── 6. Run the user's Python test file ───────────────────────────────────
    try {
      pyodide.runPython(pyCode);
    } catch(e) {
      onLog('[cocotb] Python error in test file: ' + String(e));
      self.postMessage({ ok: false, logs: logs });
      return;
    }

    // ── 7. Create a no-op cb_rtn function pointer for VPI callbacks ──────────
    // VPIRuntime::registerCb rejects null cb_rtn (returns 0 without storing).
    // We need a valid WASM (i32)->i32 function pointer for the cb_rtn field.
    // Compile a tiny WASM module and insert its export into circt-sim's table.
    // Fallback to WebAssembly.Function (Chrome 97+) or placeholder value 1.
    var noopCbPtr = wsAddFunctionToTable(WS_NOOP_CB_WASM);
    if (!noopCbPtr) { try {
      var cFn = new WebAssembly.Function({parameters:['i32'], results:['i32']}, function(){return 0;});
      var tbl = wasmTable; var s = tbl.length; tbl.grow(1); tbl.set(s, cFn); noopCbPtr = s;
    } catch(_) {} }
    // Last resort: value 1 — registerCb only checks non-zero; the patched
    // _circt_vpi_wasm_yield wraps the table call in try-catch.
    var cbRtn = noopCbPtr || 1;

    // ── 8. Install a VPI startup routine in the WASM function table ──────────
    // VPIRuntime::active starts false and is set to true inside callMain.
    // Calling _vpi_register_cb before callMain always returns 0 (no-op).
    //
    // Fix: compile a tiny WASM module (type ()->()) that imports one JS function
    // "r" and calls it. Insert the export into a null slot in the WASM table,
    // then call _vpi_startup_register(slot). circt-sim invokes startup routines
    // via invoke_v(slot) inside callMain once active=true, so "r" runs and can
    // call _vpi_register_cb successfully to register cbStartOfSimulation.
    //
    // Non-zero slot avoids null-pointer guards in VPIRuntime::runStartupRoutines.
    // WASM module is <60 bytes — synchronous compile is allowed in web workers.
    var _vpiStartupSlot = 0;
    (function() {
      try {
        _vpiStartupSlot = wsAddFunctionToTable(WS_STARTUP_CB_WASM, {
          env: {
            r: function() {
              // Called inside callMain with VPIRuntime::active=true.
              // Errors must not propagate back into invoke_v (would rethrow).
              try {
                var _ptr = wsMakeCbData(
                  simModule,
                  VPI.cbStartOfSimulation,
                  cbRtn,
                  0,
                  0,
                  0
                );
                (simModule._vpi_register_cb(_ptr)) | 0;
                simModule._free(_ptr);
              } catch(_e) { /* swallow */ }
            }
          }
        });
        if (!_vpiStartupSlot) {
          onLog('[cocotb] Warning: no table slot available for VPI startup');
        }
      } catch(e) {
        onLog('[cocotb] Warning: VPI startup install failed: ' + e);
      }
    })();

    if (typeof simModule._vpi_startup_register === 'function') {
      if (_vpiStartupSlot) {
        // Happy path: startup function runs inside callMain with active=true.
        simModule._vpi_startup_register(_vpiStartupSlot);
      } else {
        // Fallback: enable VPI subsystem with null marker, then try direct
        // registration (will return 0 if active=false, but worth attempting).
        simModule._vpi_startup_register(0);
        var _startCbData = wsMakeCbData(simModule, VPI.cbStartOfSimulation, cbRtn, 0, 0, 0);
        var _cbHandle = (simModule._vpi_register_cb(_startCbData)) | 0;
        simModule._free(_startCbData);
        if (_cbHandle) {
          onLog('[cocotb] Registered cbStartOfSimulation (direct), handle=' + _cbHandle);
        } else {
          onLog('[cocotb] Warning: _vpi_register_cb returned 0 — VPI callbacks will not fire');
        }
      }
    }

    // ── 9. Set up the Asyncify yield hook ─────────────────────────────────────
    // _circt_vpi_wasm_yield (in circt-sim-vpi.js) calls:
    //   await globalThis.circtSimVpiYieldHook(cbFuncPtr, cbDataPtr)
    //   try { wasmTable.get(cbFuncPtr)(cbDataPtr) } catch(e) {}  [patched]
    // Our hook handles all Python dispatch; cbRtn is always non-zero, which
    // satisfies registerCb's cb_rtn check. The wasmTable callback is wrapped.
    self.circtSimVpiYieldHook = async function(_cbFuncPtr, cbDataPtr) {
      var reason    = simModule.getValue(cbDataPtr +  0, 'i32');
      var triggerId = simModule.getValue(cbDataPtr + 24, 'i32');

      if (reason === VPI.cbStartOfSimulation) {
        onLog('[cocotb] cbStartOfSimulation fired — starting tests');
        try { pyodide.runPython('_start_tests_sync()'); } catch(e) { onLog('[cocotb] _start_tests_sync error: ' + e); }
        await runPyodideTicks(pyodide, function() {
          return _pendingRegistrations.length > 0 || _testsDone;
        }, 'startup');
      } else if (reason !== VPI.cbEndOfSimulation) {
        // A value-change or delay trigger fired.
        // For edge triggers, filter by direction before waking Python.
        // cbValueChange fires on every transition; RisingEdge/FallingEdge must
        // only wake when the actual edge direction matches.
        var spec = _triggerSpecs[triggerId];
        var edgeMismatch = false;
        if (spec && (spec.type === 'rising_edge' || spec.type === 'falling_edge')) {
          var currentVal = wsVpiGetSignalValue(simModule, spec.signal);
          edgeMismatch = (spec.type === 'rising_edge')  ? (currentVal === 0)
                       : (spec.type === 'falling_edge') ? (currentVal !== 0)
                       : false;
        }
        if (edgeMismatch) {
          // Wrong edge — re-register the same trigger and skip waking Python.
          _pendingRegistrations.push(spec);
        } else {
          delete _triggerSpecs[triggerId];
          pyodide.runPython('_vpi_event(' + triggerId + ')');
          await runPyodideTicks(pyodide, function() {
            return _pendingRegistrations.length > 0 || _testsDone;
          }, 'event');
        }
      }

      if (_testsDone) {
        simModule._vpi_control(VPI.vpiFinish, 0);
        return;
      }

      // Register any new VPI callbacks queued by Python.
      var regs = _pendingRegistrations;
      _pendingRegistrations = [];
      for (var j = 0; j < regs.length; j++) {
        wsRegisterVpiTrigger(simModule, regs[j], cbRtn);
      }
    };

    // ── 10. cbStartOfSimulation registered by startup function ───────────────
    // The startup function installed in the WASM table (step 8) calls _vpi_register_cb
    // from within callMain when VPIRuntime::active=true. Calling here (before
    // callMain) always fails because active=false at this point.

    // ── 11. Run the simulation ────────────────────────────────────────────────
    // callMain is synchronous. If Asyncify is enabled, the first VPI yield
    // causes WASM to unwind back to callMain (which returns EXITSTATUS).
    // We then await Asyncify.whenDone() to wait for the full simulation cycle
    // (all subsequent yields are handled by wakeUp → doRewind inside the
    // Asyncify machinery until the simulation completes and currData == null).
    var maxTimePs = maxTimeNs * 1000;
    var simArgs = [
      '--resource-guard=false',
      '--mode', 'interpret',
      '--max-time=' + maxTimePs,
      '--top', topModule,
      mlirPath
    ];
    onLog('[cocotb] Starting simulation...');
    try {
      simModule.callMain(simArgs);
    } catch(e) {
      if (!isExitException(e)) {
        onLog('[cocotb] Simulation error: ' + String(e && e.message || e));
      }
    }
    // If Asyncify triggered (currData is non-null after callMain), wait for the
    // full async simulation to complete before proceeding with cleanup.
    if (typeof Asyncify !== 'undefined' && Asyncify.currData) {
      try {
        await Asyncify.whenDone();
      } catch(e) {
        if (!isExitException(e)) {
          onLog('[cocotb] Simulation error: ' + String(e && e.message || e));
        }
      }
    }

    // Merge any stdout/stderr that went through the NODERAWFS path.
    var fsOut = simStdout.join('').trim();
    var fsErr = simStderr.join('').trim();
    if (fsOut) {
      fsOut.split(/\r?\n/).forEach(function(line) { onLog('[sim] ' + line); });
    }
    if (fsErr) {
      fsErr.split(/\r?\n/).forEach(function(line) { onLog('[sim] ' + line); });
    }

    onLog('[cocotb] Simulation complete');
    self.postMessage({ type: 'result', ok: _testsOk, logs: logs });

  } catch(e) {
    self.postMessage({ type: 'result', ok: false, logs: [...logs, '# cocotb error: ' + String(e && e.message || e)] });
  }
};
`;
