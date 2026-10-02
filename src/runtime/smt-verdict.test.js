import { describe, expect, it } from 'vitest';
import { addModelQuery, classifySmtOutput, parseModelAssignments } from './smt-verdict.js';

describe('SMT verdicts', () => {
  it('maps unsat to a bounded proof', () => {
    expect(classifySmtOutput('unsat')).toEqual({ status: 'proved', ok: true, lines: ['unsat'] });
  });

  it('maps sat to a counterexample', () => {
    expect(classifySmtOutput('sat')).toEqual({ status: 'counterexample', ok: false, lines: ['sat'] });
  });

  it('keeps unknown solver output distinct from a proof', () => {
    expect(classifySmtOutput('unknown')).toEqual({ status: 'unknown', ok: false, lines: ['unknown'] });
  });
});

describe('SMT models', () => {
  it('inserts get-model before a trailing reset', () => {
    expect(addModelQuery('(check-sat)\n(reset)\n')).toBe('(check-sat)\n(get-model)\n(reset)\n');
  });

  it('decodes four-state bitvectors and booleans', () => {
    const model = `sat
      (define-fun |req| () (_ BitVec 2) #b10)
      (define-fun rst () Bool true)
      (define-fun c0_internal () (_ BitVec 2) #b00)`;
    expect(parseModelAssignments(model)).toEqual([
      { name: 'req', value: '1', raw: '#b10' },
      { name: 'rst', value: '1', raw: 'true' }
    ]);
  });
});
