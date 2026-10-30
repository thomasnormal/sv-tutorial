import { describe, expect, it } from 'vitest';
import { highlightCode } from './highlight-code.js';

function fakePre(classes = []) {
  const attributes = new Map();
  return {
    classList: { contains: (name) => classes.includes(name) },
    hasAttribute: (name) => attributes.has(name),
    setAttribute: (name, value) => attributes.set(name, value),
    getAttribute: (name) => attributes.get(name),
  };
}

describe('highlightCode accessibility contract', () => {
  it('makes lesson blocks keyboard-scrollable and gives them context', () => {
    const diagram = fakePre(['diagram']);
    const example = fakePre();
    const node = {
      querySelectorAll(selector) {
        return selector === 'pre' ? [diagram, example] : [];
      },
    };

    highlightCode(node);

    expect(diagram.getAttribute('tabindex')).toBe('0');
    expect(diagram.getAttribute('role')).toBe('group');
    expect(diagram.getAttribute('aria-label')).toBe('Lesson diagram');
    expect(example.getAttribute('aria-label')).toBe('Code example');
  });
});
