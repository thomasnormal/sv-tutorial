import { describe, expect, it } from 'vitest';
import meta from '../lessons/meta.js';
import { lessonStatuses, lessonStatusBySlug, statusSummary, statusForLesson } from './generated-lesson-status.js';

describe('generated lesson status', () => {
  it('covers every lesson and uses only reader-facing status buckets', () => {
    expect(lessonStatuses).toHaveLength(Object.keys(meta).length);
    expect(Object.keys(lessonStatusBySlug).sort()).toEqual(Object.keys(meta).sort());
    expect(new Set(lessonStatuses.map(({ status }) => status))).toEqual(
      new Set(['PASS', 'Mox refusal', 'environment'])
    );
    expect(Object.values(statusSummary).reduce((sum, count) => sum + count, 0)).toBe(lessonStatuses.length);
  });

  it('preserves the measured blockers and exposes exact diagnostics', () => {
    expect(statusForLesson('sva/nonconsec-rep').status).toBe('Mox refusal');
    expect(statusForLesson('sva/nonconsec-rep').rows[0].diagnostic).toContain('unbounded sampled gap');
    expect(statusForLesson('uvm/reporting').status).toBe('environment');
    expect(statusForLesson('cocotb/first-test').rows[0].diagnostic).toContain('0 fs');
    expect(statusForLesson('sv/welcome').status).toBe('PASS');
  });
});
