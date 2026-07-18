import AxeBuilder from "@axe-core/playwright";
import { expect, test, type Page } from "@playwright/test";

import { orchardVerificationData as data } from "../../src/data/content";

function observeRuntime(page: Page) {
  const consoleErrors: string[] = [];
  const pageErrors: string[] = [];
  const externalRequests: string[] = [];
  const allowedOrigin = "http://127.0.0.1:4173";

  page.on("console", (message) => {
    if (message.type() === "error") consoleErrors.push(message.text());
  });
  page.on("pageerror", (error) => pageErrors.push(error.message));
  page.on("request", (request) => {
    const url = request.url();
    if (url.startsWith("data:") || url.startsWith("blob:")) return;
    if (new URL(url).origin !== allowedOrigin) externalRequests.push(url);
  });

  return () => {
    expect(consoleErrors, "browser console errors").toEqual([]);
    expect(pageErrors, "uncaught browser errors").toEqual([]);
    expect(externalRequests, "external runtime requests").toEqual([]);
  };
}

async function expectNoHorizontalPageOverflow(page: Page): Promise<void> {
  const overflow = await page.evaluate(() => ({
    viewport: document.documentElement.clientWidth,
    content: document.documentElement.scrollWidth,
  }));
  expect(overflow.content).toBeLessThanOrEqual(overflow.viewport + 1);
}

async function expectNoAxeViolations(page: Page): Promise<void> {
  const result = await new AxeBuilder({ page })
    .withTags(["wcag2a", "wcag2aa", "wcag21aa", "wcag22aa"])
    .analyze();
  const summary = result.violations.map((violation) => ({
    id: violation.id,
    impact: violation.impact,
    targets: violation.nodes.map((node) => node.target.join(" ")),
  }));
  expect(summary).toEqual([]);
}

test.describe("Orchard verification journey", () => {
  test("supports deep links, navigation, end-stop, and replay", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    const initial = data.stages[1];
    await page.goto(`/index.html#stage=${initial.id}`);

    await expect(page.getByRole("heading", { name: "Orchard Verification Journey" })).toBeVisible();
    await expect(page.getByRole("heading", { name: initial.title })).toBeVisible();
    await expect(page).toHaveURL(new RegExp(`#stage=${initial.id}$`));

    await page.getByRole("button", { name: "Next stage" }).click();
    await expect(page.getByRole("heading", { name: data.stages[2].title })).toBeVisible();
    await expect(page).toHaveURL(new RegExp(`#stage=${data.stages[2].id}$`));

    await page.getByRole("slider", { name: "Journey playhead" }).fill(String(data.stages.length));
    await expect(page.getByRole("button", { name: "Replay journey" })).toBeVisible();
    await expect(page.getByRole("button", { name: "Next stage" })).toBeDisabled();
    await expect(page.getByRole("heading", { name: data.stages.at(-1)!.title })).toBeVisible();

    await page.getByRole("button", { name: "Replay journey" }).click();
    await expect(page.getByRole("button", { name: "Pause journey" })).toBeVisible();
    await expect(page.getByRole("heading", { name: data.stages[0].title })).toBeVisible();
    await expect(page).toHaveURL(new RegExp(`#stage=${data.stages[0].id}$`));

    await expectNoHorizontalPageOverflow(page);
    assertRuntimeClean();
  });

  test("has an accessible, self-contained responsive page", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    await page.goto(`/index.html#stage=${data.stages[0].id}`);

    await expect(page.getByRole("navigation", { name: "Visualization views" })).toBeVisible();
    await expect(page.getByRole("region", { name: "Journey playback" })).toBeVisible();
    await expect(page.getByRole("article").getByText("Established here")).toBeVisible();
    await expectNoHorizontalPageOverflow(page);
    await expectNoAxeViolations(page);
    assertRuntimeClean();
  });
});

test.describe("Orchard verification atlas", () => {
  test("filters while retaining details and supports keyboard and list inspection", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    const pinned = data.nodes[0];
    const keyboardNode = data.nodes[1];
    const listNode = data.nodes[2];
    const otherStatus = data.filters.statuses.find(({ id }) => id !== pinned.status)!;
    await page.goto(`/proof-map.html#node=${pinned.id}`);

    const inspector = page.getByRole("complementary", { name: "Proof node details" });
    await expect(page.getByRole("heading", { name: "Orchard Verification Atlas" })).toBeVisible();
    await expect(inspector.getByRole("heading", { name: pinned.title })).toBeVisible();

    await page.getByRole("checkbox", { name: otherStatus.label }).check();
    await expect(inspector.getByRole("heading", { name: pinned.title })).toBeVisible();
    await expect(inspector.getByText(/pinned node is outside the current filters/i)).toBeVisible();
    await page.getByRole("button", { name: "Reset filters" }).click();

    const svgNode = page.locator(`svg [data-node-id="${keyboardNode.id}"]`);
    await svgNode.focus();
    await svgNode.press("Enter");
    await expect(inspector.getByRole("heading", { name: keyboardNode.title })).toBeVisible();
    await expect(page).toHaveURL(new RegExp(`#node=${keyboardNode.id}$`));

    const list = page.locator(".proof-map__list-alternative");
    await list.locator("summary").click();
    await expect(list).toHaveAttribute("open", "");
    await list.getByRole("button", { name: new RegExp(listNode.title) }).click();
    await expect(inspector.getByRole("heading", { name: listNode.title })).toBeVisible();
    await expect(page).toHaveURL(new RegExp(`#node=${listNode.id}$`));

    await expectNoHorizontalPageOverflow(page);
    assertRuntimeClean();
  });

  test("has an accessible, self-contained responsive page", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    await page.goto("/proof-map.html");

    await expect(page.getByRole("searchbox", { name: "Search the atlas" })).toBeVisible();
    await expect(page.getByRole("group", { name: "Interactive Orchard verification proof atlas" })).toBeVisible();
    await expect(page.getByText(/Browse the filtered atlas as a list/)).toBeVisible();
    await expectNoHorizontalPageOverflow(page);
    await expectNoAxeViolations(page);
    assertRuntimeClean();
  });
});
