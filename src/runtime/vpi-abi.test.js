import { describe, expect, it } from 'vitest';
import {
  VPI,
  VPI_LAYOUT,
  VPI_WORKER_CONST_SOURCE,
  vpiMakeCbData,
  vpiMakeTime,
  vpiMakeIntValue,
  vpiReadIntValue
} from './vpi-abi.js';

function makeMockModule(bytes = 1024) {
  const buffer = new ArrayBuffer(bytes);
  const heapU8 = new Uint8Array(buffer);
  const view = new DataView(buffer);
  let next = 32;

  return {
    HEAPU8: heapU8,
    _malloc(size) {
      const ptr = next;
      next += size;
      return ptr;
    },
    _free() {},
    setValue(ptr, value, type) {
      if (type === 'i32') {
        view.setInt32(ptr, value | 0, true);
        return;
      }
      if (type === 'double') {
        view.setFloat64(ptr, Number(value), true);
      }
    },
    getValue(ptr, type) {
      if (type === 'i32') return view.getInt32(ptr, true);
      if (type === 'double') return view.getFloat64(ptr, true);
      return 0;
    }
  };
}

describe('vpi-abi constants', () => {
  it('matches CIRCT VPI value/time enums', () => {
    expect(VPI.vpiIntVal).toBe(6);
    expect(VPI.vpiScalarVal).toBe(5);
    expect(VPI.vpiVectorVal).toBe(9);
    expect(VPI.vpiSimTime).toBe(2);
    expect(VPI.vpiScaledRealTime).toBe(1);
  });

  it('documents wasm struct offsets used by the bridge', () => {
    expect(VPI_LAYOUT.vpiValue.size).toBe(16);
    expect(VPI_LAYOUT.vpiValue.format).toBe(0);
    expect(VPI_LAYOUT.vpiValue.integer).toBe(8);
    expect(VPI_LAYOUT.vpiTime.size).toBe(20);
    expect(VPI_LAYOUT.cbData.size).toBe(28);
  });

  it('embeds constants for worker-source generation', () => {
    expect(VPI_WORKER_CONST_SOURCE).toContain('"vpiIntVal":6');
    expect(VPI_WORKER_CONST_SOURCE).toContain('"vpiSimTime":2');
    expect(VPI_WORKER_CONST_SOURCE).toContain('"integer":8');
  });
});

describe('vpi-abi helpers', () => {
  it('writes and reads integer vpi_value at union offset', () => {
    const M = makeMockModule();
    const ptr = vpiMakeIntValue(M, 42);
    expect(M.getValue(ptr + VPI_LAYOUT.vpiValue.format, 'i32')).toBe(VPI.vpiIntVal);
    expect(M.getValue(ptr + 4, 'i32')).toBe(0);
    expect(M.getValue(ptr + VPI_LAYOUT.vpiValue.integer, 'i32')).toBe(42);
    expect(vpiReadIntValue(M, ptr)).toBe(42);
  });

  it('writes cb_data fields at stable offsets', () => {
    const M = makeMockModule();
    const ptr = vpiMakeCbData(M, {
      reason: VPI.cbAfterDelay,
      cbRtn: 123,
      obj: 456,
      time: 789,
      value: 321,
      userData: 654
    });
    expect(M.getValue(ptr + VPI_LAYOUT.cbData.reason, 'i32')).toBe(VPI.cbAfterDelay);
    expect(M.getValue(ptr + VPI_LAYOUT.cbData.cbRtn, 'i32')).toBe(123);
    expect(M.getValue(ptr + VPI_LAYOUT.cbData.obj, 'i32')).toBe(456);
    expect(M.getValue(ptr + VPI_LAYOUT.cbData.time, 'i32')).toBe(789);
    expect(M.getValue(ptr + VPI_LAYOUT.cbData.value, 'i32')).toBe(321);
    expect(M.getValue(ptr + VPI_LAYOUT.cbData.userData, 'i32')).toBe(654);
  });

  it('encodes simulation time as ps split hi/lo', () => {
    const M = makeMockModule();
    const fs = 123_456_789_012_345n;
    const ptr = vpiMakeTime(M, fs);
    expect(M.getValue(ptr + VPI_LAYOUT.vpiTime.type, 'i32')).toBe(VPI.vpiSimTime);
    const hi = M.getValue(ptr + VPI_LAYOUT.vpiTime.high, 'i32') >>> 0;
    const lo = M.getValue(ptr + VPI_LAYOUT.vpiTime.low, 'i32') >>> 0;
    const ps = (BigInt(hi) << 32n) | BigInt(lo);
    expect(ps).toBe(fs / 1000n);
  });
});
