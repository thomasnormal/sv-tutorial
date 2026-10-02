import { describe, expect, it } from 'vitest';
import { lessons } from './index.js';

const browserBlocked = [
  'sv/interfaces',
  'sv/modports',
  'sv/tasks-functions',
  'sv/fsm',
  'uvm/reporting',
  'uvm/seq-item',
  'uvm/sequence',
  'uvm/driver',
  'uvm/constrained-random',
  'uvm/monitor',
  'uvm/env',
  'uvm/covergroup',
  'uvm/cross-coverage',
  'uvm/coverage-driven',
  'uvm/factory-override',
  'uvm/ral',
  'cocotb/first-test',
  'cocotb/clock-and-timing',
  'cocotb/edge-triggers',
  'cocotb/clockcycles-patterns'
];

describe('compiler-blocked lessons', () => {
  it('does not publish lessons whose browser compiler path is not qualified', () => {
    const published = new Set(lessons.map(({ slug }) => slug));
    expect(browserBlocked.filter((slug) => published.has(slug))).toEqual([]);
  });
});
