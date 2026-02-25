import { test, expect } from '@playwright/test';

async function goToLesson(page, lessonName) {
  await page.getByRole('button', { name: 'cocotb Basics' }).click();
  await page.getByRole('button', { name: new RegExp(lessonName) }).click();
  await expect(page.getByRole('heading', { level: 2, name: lessonName })).toBeVisible();
}

async function clickSolve(page) {
  await page.getByRole('button', { name: 'Editor options' }).first().click();
  const solveButton = page.getByTestId('solve-button');
  await expect(solveButton).toBeVisible();
  await solveButton.click();
}

test.describe('offline cocotb runtime', () => {
  test('downloads offline bundle and runs cocotb fully offline', async ({ page, context }) => {
    test.setTimeout(420_000);

    await page.goto('/');
    await page.evaluate(async () => {
      for (const key of Object.keys(localStorage)) {
        if (key.startsWith('svt:')) localStorage.removeItem(key);
      }
      if ('caches' in window) {
        const keys = await caches.keys();
        await Promise.all(keys.map((key) => caches.delete(key)));
      }
      if ('serviceWorker' in navigator) {
        const regs = await navigator.serviceWorker.getRegistrations();
        await Promise.all(regs.map((reg) => reg.unregister()));
      }
    });
    await page.reload({ waitUntil: 'networkidle' });

    const offlineButton = page.getByTestId('offline-download-button');
    const statusChip = page.getByTestId('offline-download-status');
    await expect(offlineButton).toBeVisible();

    await offlineButton.click();
    await expect(statusChip).toContainText(/offline ready/i, { timeout: 300_000 });

    await goToLesson(page, 'Your First cocotb Test');
    // Ensure app + service worker state is settled before cutting the network.
    await page.reload({ waitUntil: 'networkidle' });
    await context.setOffline(true);

    await clickSolve(page);
    await page.getByTestId('run-button').click();

    const logs = page.getByTestId('runtime-logs');
    await expect(logs).toContainText('$ circt-verilog', { timeout: 240_000 });
    await expect(logs).toContainText('$ python /workspace/src/test_adder.py', { timeout: 240_000 });
    await expect(logs).toContainText('$ circt-sim', { timeout: 240_000 });
    await expect(logs).toContainText('PASS  adder_test', { timeout: 240_000 });
    await expect(logs).not.toContainText("Failed to execute 'importScripts'");
    await expect(logs).not.toContainText('is invalid');
  });
});
