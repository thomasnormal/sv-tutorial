import { describe, expect, it } from 'vitest';
import { topNameForLesson } from './lesson-utils.js';

describe('lesson top selection', () => {
  it('prefers an explicit lesson top over the focus filename', () => {
    expect(topNameForLesson({ focus: '/src/struct_field.sv', top: 'tb' })).toBe('tb');
  });

  it('derives the top from focus when metadata has no override', () => {
    expect(topNameForLesson({ focus: '/src/adder.sv' })).toBe('adder');
  });
});
