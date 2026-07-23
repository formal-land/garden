import AxeBuilder from "@axe-core/playwright";
import { expect, test, type Page } from "@playwright/test";

import { orchardVerificationData as data } from "../../src/data/content";

function observeRuntime(page: Page) {
  const consoleErrors: string[] = [];
  const pageErrors: string[] = [];
  const externalRequests: string[] = [];
  const allowedOrigin = process.env.ORCHARD_E2E_ORIGIN ?? "http://127.0.0.1:4173";

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

async function openCircuitInspector(page: Page) {
  const inspector = page.getByRole("complementary", { name: "Circuit item details" });
  const toggle = page.getByRole("button", { name: "Evidence and provenance" });
  if ((page.viewportSize()?.width ?? 1280) <= 1160) {
    await expect(toggle).toBeVisible();
    await toggle.click();
  }
  await expect(inspector).toBeVisible();
  return inspector;
}

test.describe("Orchard verification journey", () => {
  test("supports deep links, manual navigation, and discrete tour controls", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    const initial = data.stages[1];
    await page.goto(`/index.html#stage=${initial.id}`);

    await expect(page.getByRole("heading", { name: "Orchard Verification Journey" })).toBeVisible();
    await expect(page.getByRole("heading", { name: initial.title })).toBeVisible();
    await expect(page).toHaveURL(new RegExp(`#stage=${initial.id}$`));

    await page.getByRole("button", { name: "Next stage" }).click();
    await expect(page.getByRole("heading", { name: data.stages[2].title })).toBeVisible();
    await expect(page).toHaveURL(new RegExp(`#stage=${data.stages[2].id}$`));

    await expect(page.getByRole("slider")).toHaveCount(0);
    await expect(page.getByRole("button", { name: "Play tour" })).toBeVisible();
    await page.getByRole("button", {
      name: new RegExp(`^Stage ${data.stages.length}:`),
    }).click();
    await expect(page.getByRole("button", { name: "Next stage" })).toBeDisabled();
    await expect(page.getByRole("heading", { name: data.stages.at(-1)!.title })).toBeVisible();

    await page.getByRole("button", { name: "Play tour" }).click();
    await expect(page.getByRole("button", { name: "Pause tour" })).toBeVisible();
    await page.getByRole("button", { name: "Pause tour" }).click();
    await expect(page.getByRole("button", { name: "Play tour" })).toBeVisible();

    await expectNoHorizontalPageOverflow(page);
    assertRuntimeClean();
  });

  test("has an accessible, self-contained responsive page", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    const stage = data.stages[0];
    const gardenEvidence = stage.evidenceIds
      .map((id) => data.evidence.find((item) => item.id === id))
      .find((item) => item?.repoId === "garden" && item.url)!;
    await page.goto(`/index.html#stage=${stage.id}`);

    await expect(page.getByRole("navigation", { name: "Visualization views" })).toBeVisible();
    await expect(page.getByRole("region", { name: "Journey controls" })).toBeVisible();
    if ((page.viewportSize()?.width ?? 1280) > 980) {
      const snapshotContext = page.locator(".evidence-context");
      await snapshotContext.locator("summary").click();
      await expect(snapshotContext).toHaveAttribute("open", "");
      await page.mouse.click(10, 10);
      await expect(snapshotContext).not.toHaveAttribute("open", "");
    }
    await expect(page.getByRole("article").getByText("Established in this stage")).toBeVisible();
    await expect(page.getByRole("article").getByText("Not yet established")).toBeVisible();
    await expect(page.locator(".stage-story .evidence-chip").filter({ hasText: gardenEvidence.label }))
      .toHaveAttribute("href", gardenEvidence.url!);
    expect(gardenEvidence.url).toMatch(/^https:\/\/github\.com\/clarus\/garden-private\//);
    const mobile = (page.viewportSize()?.width ?? 1280) <= 760;
    const stageNodeList = page.getByRole("list", { name: "Proof nodes in this stage" });
    if (mobile) await expect(stageNodeList).toBeVisible();
    else await expect(stageNodeList).toBeHidden();

    const footerContext = page.locator(".site-footer__context");
    await footerContext.locator("summary").click();
    await expect(footerContext).toContainText(data.snapshot.caveat);
    await expect(footerContext).toContainText(data.snapshot.repositoryRefs.garden.slice(0, 12));
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
    const relatedEdge = data.edges.find(
      ({ from, to }) => from === keyboardNode.id || to === keyboardNode.id,
    )!;
    const relatedNodeId = relatedEdge.from === keyboardNode.id
      ? relatedEdge.to
      : relatedEdge.from;
    const otherStatus = data.filters.statuses.find(({ id }) => id !== pinned.status)!;
    await page.goto(`/proof-map.html#node=${pinned.id}`);

    const inspector = page.getByRole("complementary", { name: "Proof node details" });
    await expect(page.getByRole("heading", { name: "Orchard Verification Atlas" })).toBeVisible();
    await expect(inspector.getByRole("heading", { name: pinned.title })).toBeVisible();

    const mobile = (page.viewportSize()?.width ?? 1280) <= 760;
    if (mobile) {
      await inspector.getByRole("button", { name: "Close proof node details" }).click();
      await page.getByRole("button", { name: "Filter nodes" }).click();
      await page.getByRole("checkbox", { name: otherStatus.label }).check();
      await page.getByRole("button", { name: "Reset", exact: true }).click();
      await page.getByRole("tab", { name: "Graph" }).click();
    } else {
      await page.getByRole("checkbox", { name: otherStatus.label }).check();
      await expect(inspector.getByRole("heading", { name: pinned.title })).toBeVisible();
      await expect(inspector.getByText(/pinned node is outside the current filters/i)).toBeVisible();
      await page.getByRole("button", { name: "Reset", exact: true }).click();
    }

    const svgNode = page.locator(`svg [data-node-id="${keyboardNode.id}"]`);
    await svgNode.focus();
    await svgNode.press("Enter");
    await expect(inspector.getByRole("heading", { name: keyboardNode.title })).toBeVisible();
    await expect(page).toHaveURL(new RegExp(`#node=${keyboardNode.id}$`));
    await expect(svgNode).toHaveClass(/is-selected/);
    await expect(svgNode).not.toHaveClass(/is-related/);
    await expect(svgNode).toHaveAttribute("data-emphasis", "selected");
    await expect(svgNode).toHaveAttribute("aria-pressed", "true");
    const relatedNode = page.locator(`svg [data-node-id="${relatedNodeId}"]`);
    await expect(relatedNode).toHaveClass(/is-related/);
    await expect(relatedNode).not.toHaveClass(/is-selected/);
    await expect(relatedNode).toHaveAttribute("data-emphasis", "related");
    await expect(relatedNode).toHaveAttribute("aria-pressed", "false");

    if (mobile) {
      await inspector.getByRole("button", { name: "Close proof node details" }).click();
    } else {
      await inspector.evaluate((element) => {
        element.scrollTop = 600;
      });
    }
    await page.getByRole("tab", { name: "List" }).click();
    const list = page.getByRole("tabpanel", { name: "List" });
    await expect(list).toBeVisible();
    const listButton = list.getByRole("button", { name: new RegExp(listNode.title) });
    await listButton.click();
    await expect(inspector.getByRole("heading", { name: listNode.title })).toBeVisible();
    await expect(page).toHaveURL(new RegExp(`#node=${listNode.id}$`));
    if (!mobile) {
      await expect.poll(() => inspector.evaluate((element) => element.scrollTop)).toBe(0);
    }
    await expect(listButton).toHaveClass(/is-selected/);
    await expect(listButton).toHaveAttribute("aria-pressed", "true");

    await expectNoHorizontalPageOverflow(page);
    assertRuntimeClean();
  });

  test("has an accessible, self-contained responsive page", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    await page.goto("/proof-map.html");

    await expect(page.getByRole("searchbox", { name: "Search the atlas" })).toBeVisible();
    await expect(page.getByRole("group", { name: /^Work stream/ })).toHaveCount(0);
    const mobile = (page.viewportSize()?.width ?? 1280) <= 760;
    if (mobile) await page.getByRole("tab", { name: "Graph" }).click();
    await expect(page.getByLabel("Map view controls")).toBeVisible();
    await expect(page.getByRole("button", { name: "Zoom in" })).toBeVisible();
    await expect(page.getByRole("button", { name: "Zoom out" })).toBeVisible();
    await expect(page.getByRole("button", { name: "Fit visible nodes" })).toBeVisible();
    await expect(page.getByLabel("Current map zoom")).toHaveText("100%");

    const atlas = page.getByRole("group", { name: "Interactive Orchard verification proof atlas" });
    await expect(atlas).toBeVisible();
    const fittedViewBox = await atlas.getAttribute("viewBox");
    await page.getByRole("button", { name: "Zoom in" }).click();
    await expect(atlas).not.toHaveAttribute("viewBox", fittedViewBox!);
    await page.getByRole("button", { name: "Reset map view" }).click();
    await expect(atlas).toHaveAttribute("viewBox", fittedViewBox!);
    await page.getByRole("tab", { name: "List" }).click();
    await expect(page.getByRole("tabpanel", { name: "List" })).toBeVisible();
    await expectNoHorizontalPageOverflow(page);
    await expectNoAxeViolations(page);
    assertRuntimeClean();
  });
});

test.describe("Orchard circuit explorer", () => {
  test("lazy-loads the snapshot and drills from flow to inline region operations", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    const dataResponse = page.waitForResponse((response) =>
      new URL(response.url()).pathname.endsWith("/data/orchard-circuit-highlevel.v1.json")
    );
    await page.goto("/circuit.html");
    await expect(page.getByRole("heading", { name: "Orchard Circuit Explorer" })).toBeVisible();
    await expect((await dataResponse).ok()).toBe(true);
    await expect(page.getByRole("searchbox", { name: "Search circuit structure" })).toBeVisible();
    await expect(page.getByRole("link", { name: "Circuit", exact: true })).toHaveAttribute("aria-current", "page");
    await expect(page.getByRole("heading", { name: "Choose a circuit item" })).toBeVisible();
    await expect(page.getByRole("heading", { name: "Explore the circuit by component" })).toBeVisible();
    await expect(page.getByRole("complementary", { name: "Circuit item details" })).toHaveCount(0);
    await expect(page.locator(".circuit-workspace")).toHaveClass(/circuit-workspace--flow/);
    await expect(page.getByRole("button", { name: /theme/i })).toHaveCount(0);
    await expect(page.getByRole("button", { name: /exact concrete|aggregate repeated/i })).toHaveCount(0);

    const mobile = (page.viewportSize()?.width ?? 1280) <= 760;
    await expect(page.locator(".circuit-interpretation-note")).toContainText("Interpretation layer");
    const metricBorder = await page.locator(".circuit-intro .circuit-metrics--strip")
      .evaluate((element) => getComputedStyle(element).borderLeftWidth);
    expect(metricBorder).not.toBe("0px");
    const merkleNode = mobile
      ? page.locator(".circuit-mobile-flow button").filter({ hasText: "Merkle path" })
      : page.locator(".circuit-flow-node").filter({ hasText: "Merkle" });
    const flowFocus = page.locator(".circuit-flow-focus");
    await merkleNode.focus();
    await expect(flowFocus).toHaveAttribute("data-flow-item", "component:merkle-path");
    await expect(flowFocus).toContainText("Merkle");
    const hoverCopyStyle = await flowFocus.locator("span").evaluate((element) => ({
      overflowWrap: getComputedStyle(element).overflowWrap,
      whiteSpace: getComputedStyle(element).whiteSpace,
    }));
    expect(hoverCopyStyle).toEqual({ overflowWrap: "anywhere", whiteSpace: "normal" });
    if (!mobile) {
      await merkleNode.hover();
      await expect(page.locator(".circuit-flow-edge.is-emphasized")).toHaveCount(2);
      const rootWire = page.locator('[data-edge-id="flow-edge:flow-merkle-action"]');
      await page.mouse.move(1, 1);
      await rootWire.locator("text").focus();
      await expect(flowFocus).toHaveAttribute("data-flow-item", "flow-edge:flow-merkle-action");
      await expect(flowFocus).toContainText("Feeds the reconstructed Merkle root");
      await expect(rootWire).toHaveClass(/is-emphasized/);
    }
    await merkleNode.click();
    await expect(page).toHaveURL(/#level=component&item=component%3Amerkle-path/);
    const canvas = page.locator(".circuit-canvas");
    await expect(canvas.getByRole("heading", { name: "Merkle path" })).toBeVisible();
    await expect(canvas.getByRole("heading", { name: "Merkle path" })).toBeFocused();
    const componentInspector = await openCircuitInspector(page);
    await expect(componentInspector).toContainText("Source mapping");
    if (mobile) {
      await componentInspector.getByRole("button", {
        name: "Close evidence and provenance",
      }).click();
    }
    await expect(page.getByRole("heading", { name: "Explore the circuit by component" })).toHaveCount(0);
    await expect(canvas.locator(".circuit-card--region").first()).toBeVisible();
    await expect(canvas.locator(".circuit-card--gate").first()).toBeVisible();
    await expect(canvas.locator(".circuit-card--region-occurrence")).toHaveCount(0);

    await canvas.locator(".circuit-card--region").first().click();
    const operation = canvas.locator(".circuit-operation-record").first();
    await expect(operation).toBeVisible();
    expect(await operation.evaluate((element) => element.tagName)).toBe("ARTICLE");
    await expect(operation.getByRole("button")).toHaveCount(0);
    await expect(page).toHaveURL(/#level=detail&item=region-group%3A/);
    await expect(page.getByRole("heading", { name: "Explore the circuit by component" })).toHaveCount(0);

    await page.goBack();
    await expect(canvas.getByRole("heading", { name: "Merkle path" })).toBeFocused();
    await expect(page).toHaveURL(/#level=component&item=component%3Amerkle-path$/);

    const search = page.getByRole("searchbox", { name: "Search circuit structure" });
    await search.fill("Orchard circuit checks");
    await expect(search).toBeFocused();
    await expect(page.locator("#circuit-search-results")).toContainText("Orchard circuit checks");
    await expectNoHorizontalPageOverflow(page);
    assertRuntimeClean();
  });

  test("canonicalizes legacy gate links and renders inline constraints accessibly", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    await page.goto("/circuit.html#level=detail&item=gate%3A0&mode=exact");

    const canvas = page.locator(".circuit-canvas");
    await expect(canvas.getByRole("heading", { name: "Orchard circuit checks" })).toBeVisible();
    await expect(page).toHaveURL(/#level=detail&item=gate%3A0$/);
    const constraint = canvas.locator(".circuit-constraint-record").first();
    await expect(constraint).toBeVisible();
    expect(await constraint.evaluate((element) => element.tagName)).toBe("ARTICLE");
    await expect(constraint.getByRole("button")).toHaveCount(0);
    const inspector = await openCircuitInspector(page);
    await expect(inspector).toContainText("Source mapping");
    await expect(page.getByRole("heading", { name: "Explore the circuit by component" })).toHaveCount(0);
    await expect(page.getByRole("button", { name: /theme/i })).toHaveCount(0);
    await expect(page.getByRole("button", { name: /exact concrete|aggregate repeated/i })).toHaveCount(0);
    await expect(canvas.getByText(/^In Halo2, every gate/)).toHaveCount(0);

    await expectNoHorizontalPageOverflow(page);
    await expectNoAxeViolations(page);
    assertRuntimeClean();
  });

  test("keeps deep region provenance readable with short source labels", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    await page.goto(
      "/circuit.html#level=detail&item=region-group%3Acomponent-nullifier%3Acomplete-point-addition-257b3ed2",
    );

    const inspector = await openCircuitInspector(page);
    await expect(page.locator(".circuit-canvas").getByRole("heading", {
      name: "complete point addition",
      level: 2,
    })).toBeVisible();
    await expect(inspector.getByRole("heading", { name: "Evidence and provenance" })).toBeVisible();
    const scrollState = await inspector.evaluate((element) => ({
      clientHeight: element.clientHeight,
      overflowY: getComputedStyle(element).overflowY,
      scrollHeight: element.scrollHeight,
    }));
    expect(["visible", "auto", "scroll"]).toContain(scrollState.overflowY);
    if (scrollState.overflowY === "visible") {
      expect(scrollState.scrollHeight).toBe(scrollState.clientHeight);
    } else {
      expect(scrollState.scrollHeight).toBeGreaterThanOrEqual(scrollState.clientHeight);
    }

    const sourceLabels = await inspector.locator(".circuit-source-panel a code").allTextContents();
    expect(sourceLabels.length).toBeGreaterThan(0);
    expect(sourceLabels.every((label) => !label.includes("/") && !label.includes("\\"))).toBe(true);
    expect(sourceLabels.every((label) => /\.[a-z0-9]+(?::\d+)?$/i.test(label))).toBe(true);
    await expect(inspector.getByRole("button", {
      name: /Copy full (?:candidate )?source file path/,
    }).first()).toBeVisible();

    await expectNoHorizontalPageOverflow(page);
    assertRuntimeClean();
  });
});

test.describe("Orchard circuit grid", () => {
  test("lazy-loads the placement trace and pins a selector cell with a Circuit link", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    const dataResponse = page.waitForResponse((response) =>
      new URL(response.url()).pathname.endsWith("/data/orchard-circuit-grid.v1.json")
    );
    await page.goto("/circuit-grid.html");

    await expect(page.getByRole("heading", { name: "Orchard Circuit Grid" })).toBeVisible();
    await expect((await dataResponse).ok()).toBe(true);
    await expect(page.getByRole("link", { name: "Grid", exact: true })).toHaveAttribute(
      "aria-current",
      "page",
    );
    await expect(page.getByRole("navigation", { name: "Visualization views" }).getByRole("link"))
      .toHaveCount(4);
    await expect(page.getByRole("searchbox", { name: "Search circuit grid" })).toBeVisible();

    const gridTab = page.getByRole("tab", { name: "Grid", exact: true });
    if (await gridTab.getAttribute("aria-selected") !== "true") await gridTab.click();
    const grid = page.getByRole("region", { name: "Circuit grid", exact: true });
    await expect(grid).toBeVisible();
    await expect(grid).toHaveAttribute("data-track-count", "26");

    await page.getByRole("button", { name: "Expand 56 selectors" }).click();
    await expect(grid).toHaveAttribute("data-track-count", "81");

    await page.evaluate(() => {
      window.location.hash = "row=1758&column=selector%3A5";
    });
    const selectorCell = grid.locator('[data-row="1758"][data-column="selector:5"]');
    await expect(selectorCell).toBeVisible();
    await expect(selectorCell).toBeInViewport();
    const inspector = page.getByRole("complementary", { name: "Cell details" });
    await expect(inspector.getByRole("heading", { name: /^Row 1758 · / })).toBeVisible();
    await expect(inspector).toContainText("QWitnessPoint");
    const circuitLink = inspector.getByRole("link", { name: /Open .* in Circuit/i }).first();
    await expect(circuitLink).toHaveAttribute("href", /circuit\.html#level=detail&item=/);

    await inspector.getByRole("button", { name: "Close cell details" }).click();
    await expect(inspector).toHaveCount(0);
    await selectorCell.click();
    await expect(page.getByRole("complementary", { name: "Cell details" })).toBeVisible();
    await expect(page).toHaveURL(/#row=1758&column=selector%3A5$/);

    const localOverflow = await grid.evaluate((element) => ({
      clientWidth: element.clientWidth,
      scrollWidth: element.scrollWidth,
    }));
    expect(localOverflow.scrollWidth).toBeGreaterThan(localOverflow.clientWidth);
    await expectNoHorizontalPageOverflow(page);
    assertRuntimeClean();
  });

  test("provides a responsive List alternative and an accessible self-contained page", async ({ page }) => {
    const assertRuntimeClean = observeRuntime(page);
    await page.goto("/circuit-grid.html");

    const listTab = page.getByRole("tab", { name: "List", exact: true });
    const mobile = (page.viewportSize()?.width ?? 1280) <= 760;
    if (mobile) {
      await expect(listTab).toHaveAttribute("aria-selected", "true");
    } else {
      await listTab.click();
    }

    const list = page.getByRole("tabpanel", { name: "List" });
    await expect(list).toBeVisible();
    await expect(list.locator(".circuit-grid-list li button").first()).toBeVisible();
    await expect(page.locator(".circuit-grid-coverage"))
      .toContainText(/ordinary(?: witness)? assignments are not recorded/i);
    await expect(page.locator(".circuit-grid-coverage")).toContainText("references-only");

    await expectNoHorizontalPageOverflow(page);
    await expectNoAxeViolations(page);
    assertRuntimeClean();
  });
});
