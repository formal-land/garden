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

test.describe("Orchard circuit explorer", () => {
  test("lazy-loads the snapshot and drills from flow to exact region operations", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    const dataResponse = page.waitForResponse((response) =>
      new URL(response.url()).pathname.endsWith("/data/orchard-circuit-highlevel.v1.json")
    );
    await page.goto("/circuit.html");
    await expect(page.getByRole("heading", { name: "Orchard Circuit Explorer" })).toBeVisible();
    await expect((await dataResponse).ok()).toBe(true);
    await expect(page.getByRole("searchbox", { name: "Search circuit structure" })).toBeVisible();
    await expect(page.getByRole("link", { name: "Circuit", exact: true })).toHaveAttribute("aria-current", "page");

    const merkleNode = (page.viewportSize()?.width ?? 1280) <= 760
      ? page.locator(".circuit-mobile-flow button").filter({ hasText: "Merkle path" })
      : page.locator(".circuit-flow-node").filter({ hasText: "Merkle" });
    await merkleNode.click();
    await expect(page).toHaveURL(/#level=component&item=component%3Amerkle-path/);
    const canvas = page.locator(".circuit-canvas");
    await expect(canvas.getByRole("heading", { name: "Merkle path" })).toBeVisible();
    await expect(canvas.getByRole("heading", { name: "Merkle path" })).toBeFocused();
    await expect(page.getByRole("complementary", { name: "Circuit item details" }))
      .toContainText("Source mapping confidence");

    await page.getByRole("button", { name: "Show exact concrete regions" }).click();
    const occurrence = canvas.locator(".circuit-card--region-occurrence").first();
    await expect(occurrence).toBeVisible();
    await occurrence.click();
    await expect(canvas.locator(".circuit-operation-list button").first()).toBeVisible();
    await expect(page).toHaveURL(/#level=detail&item=region%3A\d+&mode=exact/);

    await page.goBack();
    await expect(canvas.getByRole("heading", { name: "Merkle path" })).toBeFocused();
    await expect(page).toHaveURL(/#level=component&item=component%3Amerkle-path&mode=exact/);

    const search = page.getByRole("searchbox", { name: "Search circuit structure" });
    await search.fill("Orchard circuit checks");
    await expect(search).toBeFocused();
    await expect(page.locator("#circuit-search-results")).toContainText("Orchard circuit checks");
    await expectNoHorizontalPageOverflow(page);
    assertRuntimeClean();
  });

  test("supports exact gate deep links and an accessible responsive layout", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    await page.goto("/circuit.html#level=detail&item=gate%3A0&mode=exact");

    const canvas = page.locator(".circuit-canvas");
    await expect(canvas.getByRole("heading", { name: "Orchard circuit checks" })).toBeVisible();
    await expect(canvas.locator(".circuit-constraint-list button").first()).toBeVisible();
    await expect(page.getByRole("complementary", { name: "Circuit item details" }))
      .toContainText("Exact");
    await expect(page.getByText("Browse the circuit as an outline")).toBeVisible();

    await expectNoHorizontalPageOverflow(page);
    await expectNoAxeViolations(page);
    assertRuntimeClean();
  });
});
