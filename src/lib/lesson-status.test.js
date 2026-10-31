import { describe, expect, it } from 'vitest';
import meta from '../lessons/meta.js';
import {
  lessonStatuses,
  lessonStatusBySlug,
  statusSummary,
  statusForLesson,
  matrixHistory,
  matrixDiff
} from './generated-lesson-status.js';
import { computeMatrixDiff, parseResultTable } from '../../scripts/matrix-results.mjs';

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

  it('publishes a build-to-build matrix diff when result history is available', () => {
    expect(matrixHistory.old?.sha ?? matrixHistory.new?.sha).toMatch(/^[0-9a-f]{40}$/);
    if (matrixHistory.new) expect(matrixHistory.new.sha).toMatch(/^[0-9a-f]{40}$/);
    expect(matrixDiff.moves).toBeInstanceOf(Array);
    expect(matrixDiff.diagnosticChanges).toBeInstanceOf(Array);
  });

  it('detects verdict and diagnostic changes by lesson and mode', () => {
    const table = (status, diagnostic) => parseResultTable([
      '- Mox build: `aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa`',
      '- Generated: 2026-10-30T00:00:00Z',
      '| Lesson | Mode | Status | Diagnostic |',
      '|---|---|---|---|',
      `| \`sv/example\` | run | ${status} | ${diagnostic} |`
    ].join('\n'));
    const oldTable = table('Mox refusal', 'old diagnostic');
    const newTable = table('PASS', '');
    const diff = computeMatrixDiff(oldTable, newTable);
    expect(diff.moves[0]).toMatchObject({ slug: 'sv/example', mode: 'run', oldVerdict: 'FAIL', newVerdict: 'PASS' });
    expect(diff.diagnosticChanges[0].oldDiagnostic).toBe('old diagnostic');
  });
});
