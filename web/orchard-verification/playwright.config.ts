import { defineConfig, devices } from "@playwright/test";

const e2eOrigin = process.env.ORCHARD_E2E_ORIGIN ?? "http://127.0.0.1:4173";
const e2ePort = new URL(e2eOrigin).port || "4173";

export default defineConfig({
  testDir: "./tests/e2e",
  outputDir: "./test-results",
  fullyParallel: true,
  forbidOnly: Boolean(process.env.CI),
  retries: process.env.CI ? 2 : 0,
  reporter: process.env.CI ? "github" : "list",
  use: {
    baseURL: e2eOrigin,
    trace: "retain-on-failure",
  },
  projects: [
    {
      name: "desktop-chromium",
      use: { ...devices["Desktop Chrome"] },
    },
    {
      name: "mobile-chromium",
      use: { ...devices["Pixel 7"] },
    },
  ],
  webServer: {
    command: `npm run dev -- --host 127.0.0.1 --port ${e2ePort}`,
    url: e2eOrigin,
    reuseExistingServer: !process.env.CI,
  },
});
