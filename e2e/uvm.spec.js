/**
 * E2E tests for all UVM lessons (circt-verilog → circt-sim with full UVM).
 */
import { test, expect } from '@playwright/test';

const UVM_ROUTES = {
  'The First UVM Test': '/lesson/uvm/reporting',
  'Sequence Items': '/lesson/uvm/seq-item',
  'Sequences': '/lesson/uvm/sequence',
  'The Driver': '/lesson/uvm/driver',
  'Monitor and Scoreboard': '/lesson/uvm/monitor',
  'Environment and Test': '/lesson/uvm/env'
};

async function goToLesson(page, lessonName) {
  const route = UVM_ROUTES[lessonName];
  if (!route) {
    throw new Error(`No UVM route mapping found for lesson "${lessonName}"`);
  }
  await page.goto(route);
  await expect(page.getByRole('heading', { level: 2, name: lessonName })).toBeVisible();
}

// Common assertions for full-UVM execution.
async function expectCleanUvmRun(logs) {
  await expect(logs).toContainText('$ circt-verilog', { timeout: 120_000 });
  await expect(logs).toContainText('$ circt-sim', { timeout: 120_000 });
  await expect(logs).toContainText('--mode interpret');
  await expect(logs).not.toContainText('--compiled');
  await expect(logs).not.toContainText("# circt-verilog exit code: 1");
  await expect(logs).not.toContainText('uvm-lite compatibility shim');
  await expect(logs).not.toContainText("unknown package 'uvm_pkg'");
  await expect(logs).not.toContainText("'uvm_macros.svh': No such file or directory");
  await expect(logs).not.toContainText('not a valid top-level module');
  await expect(logs).not.toContainText('redefinition of');
}

test('UVM Foundations: The First UVM Test', async ({ page }) => {
  await goToLesson(page, 'The First UVM Test');
  await page.getByTestId('run-button').click();
  await expectCleanUvmRun(page.getByTestId('runtime-logs'));
});

test('UVM Foundations: Sequence Items — solution compiles and runs', async ({ page }) => {
  await goToLesson(page, 'Sequence Items');
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();
  await expectCleanUvmRun(page.getByTestId('runtime-logs'));
});

test('Stimulus: Sequences — solution compiles and runs', async ({ page }) => {
  await goToLesson(page, 'Sequences');
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();
  await expectCleanUvmRun(page.getByTestId('runtime-logs'));
});

test('Stimulus: The Driver — solution compiles and runs', async ({ page }) => {
  await goToLesson(page, 'The Driver');
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();
  await expectCleanUvmRun(page.getByTestId('runtime-logs'));
});

test('Checking: Monitor and Scoreboard — solution compiles and runs', async ({ page }) => {
  await goToLesson(page, 'Monitor and Scoreboard');
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();
  await expectCleanUvmRun(page.getByTestId('runtime-logs'));
});

test('Checking: Environment and Test — solution compiles and runs', async ({ page }) => {
  await goToLesson(page, 'Environment and Test');
  await page.getByTestId('solve-button').click();
  await page.getByTestId('run-button').click();
  await expectCleanUvmRun(page.getByTestId('runtime-logs'));
});
