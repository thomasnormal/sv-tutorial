import { test, expect } from '@playwright/test';

test('cocotb: debug - check wasmTable', async ({ page }) => {
  const consoleLogs = [];
  page.on('console', msg => {
    const text = `[${msg.type()}] ${msg.text()}`;
    consoleLogs.push(text);
  });

  // Cocotb is quarantined from the sidebar; navigate to its direct route.
  await page.goto('/lesson/cocotb/first-test');
  await page.getByTestId('options-button').click();
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();

  await page.waitForTimeout(20000);

  const logs = page.getByTestId('runtime-logs');
  const text = await logs.textContent();

  console.log('=== Runtime logs ===');
  console.log(text);
  console.log('=== Console logs (last 40) ===');
  consoleLogs.slice(-40).forEach(l => console.log(l));

  expect(text).not.toContain('# cocotb error');
});
