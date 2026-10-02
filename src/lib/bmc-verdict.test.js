import { describe, expect, it } from 'vitest';
import { bmcRunPasses } from './bmc-verdict.js';

describe('BMC lesson verdicts', () => {
  it('accepts the expected counterexample as a completed lesson result', () => {
    expect(bmcRunPasses({ bmcExpected: 'counterexample' }, { verdict: 'counterexample', ok: false })).toBe(true);
  });

  it('does not accept the wrong bounded verdict', () => {
    expect(bmcRunPasses({ bmcExpected: 'proved' }, { verdict: 'counterexample', ok: false })).toBe(false);
  });

  it('fails closed when the bounded verdict is missing', () => {
    expect(bmcRunPasses({ bmcExpected: 'proved' }, { ok: true })).toBe(false);
    expect(bmcRunPasses({ bmcExpected: 'counterexample' }, { verdict: null, ok: false })).toBe(false);
  });

  it('keeps non-BMC completion tied to the runner result', () => {
    expect(bmcRunPasses({}, { verdict: 'counterexample', ok: false })).toBe(false);
    expect(bmcRunPasses({}, { verdict: 'proved', ok: true })).toBe(true);
  });
});
