/**
 * Shared VPI ABI constants/helpers for wasm32 circt-sim bridges.
 *
 * Keep this as the single source of truth for:
 * - VPI enum values used by JS <-> wasm calls
 * - struct field offsets for t_cb_data / t_vpi_time / t_vpi_value
 *
 * Notes:
 * - These layouts target wasm32 + clang default ABI used by Emscripten.
 * - t_vpi_value places the union at offset 8 (4-byte format + 4-byte padding)
 *   because the union contains a double and therefore has 8-byte alignment.
 */

export const VPI = Object.freeze({
  // vpi_get properties / object kinds (subset used by JS bridges).
  vpiType: 1,
  vpiName: 2,
  vpiFullName: 3,
  vpiSize: 4,
  vpiReg: 48,

  // Callback reasons.
  cbValueChange: 1,
  cbStmt: 2,
  cbForce: 3,
  cbRelease: 4,
  cbAtStartOfSimTime: 5,
  cbReadWriteSynch: 6,
  cbReadOnlySynch: 7,
  cbNextSimTime: 8,
  cbAfterDelay: 9,
  cbEndOfCompile: 10,
  cbStartOfSimulation: 11,
  cbEndOfSimulation: 12,
  cbError: 13,

  // vpi_control operations.
  vpiFinish: 66,
  vpiStop: 67,

  // vpi_get_value / vpi_put_value formats.
  vpiBinStrVal: 1,
  vpiOctStrVal: 2,
  vpiDecStrVal: 3,
  vpiHexStrVal: 4,
  vpiScalarVal: 5,
  vpiIntVal: 6,
  vpiRealVal: 7,
  vpiStringVal: 8,
  vpiVectorVal: 9,

  // vpi_time types.
  vpiScaledRealTime: 1,
  vpiSimTime: 2
});

export const VPI_LAYOUT = Object.freeze({
  cbData: Object.freeze({
    size: 28,
    reason: 0,
    cbRtn: 4,
    obj: 8,
    time: 12,
    value: 16,
    index: 20,
    userData: 24
  }),
  vpiTime: Object.freeze({
    size: 20,
    type: 0,
    high: 4,
    low: 8,
    real: 12
  }),
  vpiValue: Object.freeze({
    size: 16,
    format: 0,
    union: 8,
    integer: 8
  })
});

export const VPI_WORKER_CONST_SOURCE = [
  `var VPI = ${JSON.stringify(VPI)};`,
  `var VPI_LAYOUT = ${JSON.stringify(VPI_LAYOUT)};`
].join('\n');

export function vpiWriteString(Module, str) {
  const bytes = new TextEncoder().encode(`${str}\0`);
  const ptr = Module._malloc(bytes.length);
  Module.HEAPU8.set(bytes, ptr);
  return ptr;
}

export function vpiFree(Module, ptr) {
  Module._free(ptr);
}

export function vpiMakeCbData(Module, {
  reason = 0,
  cbRtn = 0,
  obj = 0,
  time = 0,
  value = 0,
  userData = 0
} = {}) {
  const ptr = Module._malloc(VPI_LAYOUT.cbData.size);
  Module.setValue(ptr + VPI_LAYOUT.cbData.reason, reason, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.cbData.cbRtn, cbRtn, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.cbData.obj, obj, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.cbData.time, time, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.cbData.value, value, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.cbData.index, 0, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.cbData.userData, userData, 'i32');
  return ptr;
}

export function vpiMakeTime(Module, fs) {
  const ps = BigInt(fs) / 1000n;
  const hi = Number(ps >> 32n) >>> 0;
  const lo = Number(ps & 0xFFFFFFFFn) >>> 0;
  const ptr = Module._malloc(VPI_LAYOUT.vpiTime.size);
  Module.setValue(ptr + VPI_LAYOUT.vpiTime.type, VPI.vpiSimTime, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.vpiTime.high, hi, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.vpiTime.low, lo, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.vpiTime.real, 0, 'double');
  return ptr;
}

export function vpiMakeIntValue(Module, intVal) {
  const ptr = Module._malloc(VPI_LAYOUT.vpiValue.size);
  Module.setValue(ptr + VPI_LAYOUT.vpiValue.format, VPI.vpiIntVal, 'i32');
  Module.setValue(ptr + VPI_LAYOUT.vpiValue.integer, intVal | 0, 'i32');
  return ptr;
}

export function vpiReadIntValue(Module, valuePtr) {
  return Module.getValue(valuePtr + VPI_LAYOUT.vpiValue.integer, 'i32');
}
