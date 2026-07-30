import { defineConfig, devices } from "@playwright/test";

const e2eBaseUrl = new URL(
  process.env.ORCHARD_E2E_ORIGIN ?? "http://127.0.0.1:4173/",
);
if (!e2eBaseUrl.pathname.endsWith("/")) e2eBaseUrl.pathname += "/";
const e2ePort = e2eBaseUrl.port || "4173";

export default defineConfig({
  testDir: "./tests/e2e",
  outputDir: "./test-results",
  fullyParallel: true,
  forbidOnly: Boolean(process.env.CI),
  retries: process.env.CI ? 2 : 0,
  reporter: process.env.CI ? "github" : "list",
  use: {
    baseURL: e2eBaseUrl.href,
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
    command:
      `npm run preview -- --host 127.0.0.1 --port ${e2ePort} --strictPort ` +
      `--base ${e2eBaseUrl.pathname}`,
    url: e2eBaseUrl.href,
    reuseExistingServer:
      process.env.ORCHARD_E2E_REUSE_EXISTING_SERVER === "1" ||
      !process.env.CI,
  },
});
