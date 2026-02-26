import { defineConfig } from '@playwright/test';

/**
 * Config for running smoke tests against the live GitHub Pages deployment.
 * No local webServer — tests go directly to the live URL.
 */
export default defineConfig({
  testDir: '../e2e',
  testMatch: 'ghpages.spec.js',
  timeout: 180_000,
  fullyParallel: false,
  retries: 1,
  workers: 1,
  reporter: [['list']],
  use: {
    channel: 'chromium',
    headless: true,
    launchOptions: {
      args: [
        '--use-angle=swiftshader',
        '--enable-webgl',
        '--enable-unsafe-swiftshader',
        '--ignore-gpu-blocklist'
      ]
    },
    trace: 'on-first-retry',
    screenshot: 'only-on-failure'
  }
  // No webServer block — tests hit the live site directly
});
