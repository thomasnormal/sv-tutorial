import { test, expect } from '@playwright/test';

// A cocotb run must always end with a result. If mox-sim aborts while the
// worker is suspended in an Asyncify yield, the run used to hang in "Cancel".
test('cocotb: a run settles with a test result or the simulator error', async ({ page }) => {
  await page.goto('/lesson/cocotb/first-test');
  await expect(page.getByTestId('lesson-title')).toHaveText('Your First cocotb Test');

  const button = page.getByTestId('run-button');
  const logs = page.getByTestId('runtime-logs');
  await button.click();
  await expect(logs).toContainText('$ mox-sim', { timeout: 60_000 });
  await expect(button).not.toHaveAttribute('aria-label', /^Cancel/, { timeout: 60_000 });
  await expect(logs).toContainText(/^(PASS|FAIL|ERROR)\s+\w+|Aborted\(/m);
});
