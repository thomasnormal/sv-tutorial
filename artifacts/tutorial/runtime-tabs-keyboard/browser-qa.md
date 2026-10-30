# Runtime tab keyboard browser receipt

This receipt covers the Logs/Waves tab keyboard interaction in the lesson
runtime pane.

## Browser receipt

The focused Playwright test passed 1/1 on 2026-10-30:

```text
CI=1 npx playwright test e2e/waveform.spec.js -g 'runtime tabs support keyboard navigation' --workers=1
1 passed (4.1m)
```

The test runs the solved `sv/modules-and-ports` lesson through the real VCD
pipeline, focuses the Logs tab, presses `ArrowRight`, and verifies that focus
moves to Waves, `aria-selected` changes, the roving `tabindex` changes, and
the Waves panel becomes visible.
