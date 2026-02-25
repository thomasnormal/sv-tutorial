/**
 * E2E tests for the cocotb runner (circt-verilog → circt-sim + Pyodide).
 */
import { test, expect } from '@playwright/test';

async function goToLesson(page, lessonName) {
  await page.goto('/');
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

test('cocotb: shows "test" button, not "run"', async ({ page }) => {
  await goToLesson(page, 'Your First cocotb Test');
  await expect(page.getByTestId('run-button')).toHaveAttribute('title', /test/i);
});

test('cocotb: Your First cocotb Test — solution passes all assertions', async ({ page }) => {
  await goToLesson(page, 'Your First cocotb Test');

  // The Python test file is the starter; apply the SV solution (correct adder).
  await clickSolve(page);
  await page.getByTestId('run-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ python /workspace/src/test_adder.py', { timeout: 180_000 });
  await expect(logs).toContainText('PASS', { timeout: 180_000 });
  await expect(logs).toContainText('[circt-sim] Simulation completed', { timeout: 180_000 });
  await expect(logs).not.toContainText('AssertionError');
  await expect(logs).not.toContainText("Failed to execute 'importScripts'");
  await expect(logs).not.toContainText('is invalid');
});

test('cocotb: Clock and Timing — solution passes all assertions', async ({ page }) => {
  await goToLesson(page, 'Clock and Timing');

  await clickSolve(page);
  await page.getByTestId('run-button').click();

  const logs = page.getByTestId('runtime-logs');
  await expect(logs).toContainText('$ python /workspace/src/test_counter.py', { timeout: 180_000 });
  await expect(logs).toContainText('PASS', { timeout: 180_000 });
  await expect(logs).toContainText('[circt-sim] Simulation completed', { timeout: 180_000 });
  await expect(logs).not.toContainText('AssertionError');
  await expect(logs).not.toContainText("Failed to execute 'importScripts'");
  await expect(logs).not.toContainText('is invalid');
});
