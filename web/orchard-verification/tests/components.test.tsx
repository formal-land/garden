import { act, fireEvent, render, screen, cleanup, within } from "@testing-library/react";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import { App } from "../src/App";
import { JourneyView } from "../src/components/JourneyView";
import { ProofMap } from "../src/components/ProofMap";
import { orchardVerificationData as data } from "../src/data/content";

function useMediaPreference(reducedMotion: boolean): void {
  Object.defineProperty(window, "matchMedia", {
    configurable: true,
    writable: true,
    value: (query: string): MediaQueryList => ({
      matches: query.includes("prefers-reduced-motion") && reducedMotion,
      media: query,
      onchange: null,
      addListener: () => undefined,
      removeListener: () => undefined,
      addEventListener: () => undefined,
      removeEventListener: () => undefined,
      dispatchEvent: () => false,
    }),
  });
}

beforeEach(() => {
  useMediaPreference(true);
  window.history.replaceState(null, "", "/index.html");
  document.documentElement.dataset.view = "journey";
});

afterEach(() => {
  cleanup();
  vi.clearAllTimers();
  vi.useRealTimers();
});

describe("journey application", () => {
  it("navigates stages with controls and keyboard while keeping a deep link", () => {
    render(<JourneyView data={data} />);

    expect(screen.getByRole("heading", { name: data.stages[0].title, level: 2 })).toBeVisible();
    expect(screen.getByText(`Stage 1 of ${data.stages.length}`)).toBeVisible();
    expect(window.location.hash).toBe(`#stage=${data.stages[0].id}`);

    fireEvent.click(screen.getByRole("button", { name: "Next stage" }));
    expect(screen.getByRole("heading", { name: data.stages[1].title, level: 2 })).toBeVisible();
    expect(window.location.hash).toBe(`#stage=${data.stages[1].id}`);

    fireEvent.keyDown(document.body, { key: "ArrowRight" });
    expect(screen.getByRole("heading", { name: data.stages[2].title, level: 2 })).toBeVisible();

    fireEvent.keyDown(document.body, { key: "ArrowLeft" });
    expect(screen.getByRole("heading", { name: data.stages[1].title, level: 2 })).toBeVisible();
  });

  it("opens directly at a valid stage hash", () => {
    const requested = data.stages.at(-1)!;
    window.history.replaceState(null, "", `/index.html#stage=${requested.id}`);

    render(<JourneyView data={data} />);

    expect(screen.getByRole("heading", { name: requested.title, level: 2 })).toBeVisible();
    expect(screen.getByText(`Stage ${data.stages.length} of ${data.stages.length}`)).toBeVisible();
    expect(screen.getByRole("button", { name: "Next stage" })).toBeDisabled();
  });

  it("links Journey evidence and migrated work history through public Garden", () => {
    const stage = data.stages[0];
    const gardenEvidence = stage.evidenceIds
      .map((id) => data.evidence.find((item) => item.id === id))
      .find((item) => item?.repoId === "garden" && item.url);
    expect(gardenEvidence).toBeDefined();

    render(<JourneyView data={data} />);

    expect(screen.getByRole("link", { name: /PR #88 · Add Orchard circuit verification/i }))
      .toHaveAttribute("href", "https://github.com/formal-land/garden/pull/88");
    expect(screen.getByRole("link", { name: /PR #89 · Add Journey Pages/i }))
      .toHaveAttribute("href", "https://github.com/formal-land/garden/pull/89");

    const stageArticle = screen.getByRole("article", {
      name: data.stages[0].title,
    });
    const evidencePanel = stageArticle.querySelector<HTMLElement>(".stage-story__evidence")!;
    const evidenceLink = within(evidencePanel).getByRole("link", {
      name: new RegExp(gardenEvidence!.label),
    });
    expect(evidenceLink).toHaveAttribute("href", gardenEvidence!.url);
    expect(evidenceLink?.getAttribute("href")).toMatch(
      /^https:\/\/github\.com\/formal-land\/garden\//,
    );

    const workPanel = within(stageArticle).getByLabelText("Work delivered");
    expect(within(workPanel).getByText("Framework and circuit capture")).toBeVisible();
    fireEvent.click(within(workPanel).getAllByText(/Pull requests and commits/)[0]);
    expect(within(workPanel).getByRole("link", { name: /Migrated PR #6/i }))
      .toHaveAttribute("href", "https://github.com/formal-land/garden/commit/7ca385f");
  });

  it("starts manually, stops at the end, and replays from stage one", () => {
    vi.useFakeTimers();
    render(<JourneyView data={data} />);

    expect(screen.getByRole("button", { name: "Play tour" })).toBeVisible();
    expect(screen.queryByRole("slider")).not.toBeInTheDocument();
    expect(screen.queryByRole("combobox", { name: /playback speed/i })).not.toBeInTheDocument();

    fireEvent.click(screen.getByRole("button", {
      name: new RegExp(`^Stage ${data.stages.length}:`),
    }));
    fireEvent.click(screen.getByRole("button", { name: "Play tour" }));
    act(() => vi.advanceTimersByTime(30_000));

    const replay = screen.getByRole("button", { name: "Replay tour" });
    expect(screen.getByRole("heading", { name: data.stages.at(-1)!.title, level: 2 })).toBeVisible();

    fireEvent.click(replay);
    expect(screen.getByRole("button", { name: "Pause tour" })).toBeVisible();
    expect(screen.getByRole("heading", { name: data.stages[0].title, level: 2 })).toBeVisible();
  });

  it("does not auto-play when reduced motion is requested", () => {
    vi.useFakeTimers();
    useMediaPreference(true);
    render(<JourneyView data={data} />);

    act(() => vi.advanceTimersByTime(30_000));

    expect(screen.getByRole("button", { name: "Play tour" })).toBeVisible();
    expect(screen.getByText(`Stage 1 of ${data.stages.length}`)).toBeVisible();
  });

  it("selects the configured view without exposing a theme toggle", () => {
    render(<App />);

    expect(screen.getByRole("heading", { name: "Orchard Verification Journey", level: 1 })).toBeVisible();
    expect(screen.queryByRole("button", { name: /theme/i })).not.toBeInTheDocument();
    expect(document.querySelector(".theme-toggle")).not.toBeInTheDocument();
    expect(screen.queryByText("Repository versions · Known limitations"))
      .not.toBeInTheDocument();
    expect(screen.queryByText(/Methodology/)).not.toBeInTheDocument();

    const snapshotSummary = screen.getByText("Snapshot").closest("summary")!;
    const snapshotDetails = snapshotSummary.closest("details")!;
    fireEvent.click(snapshotSummary);
    expect(snapshotDetails).toHaveAttribute("open");
    fireEvent.pointerDown(document.body);
    expect(snapshotDetails).not.toHaveAttribute("open");

    cleanup();
    document.documentElement.dataset.view = "atlas";
    render(<App />);
    expect(screen.getByRole("heading", { name: "Orchard Verification Atlas", level: 1 })).toBeVisible();
    expect(screen.getByRole("searchbox", { name: "Search the atlas" })).toBeVisible();
    expect(screen.getByLabelText("Filter by work unit")).toBeVisible();
    expect(screen.queryByRole("link", { name: /Open guided journey/i })).not.toBeInTheDocument();
    expect(screen.queryByRole("button", { name: /theme/i })).not.toBeInTheDocument();
  });
});

describe("proof atlas interactions", () => {
  it("opens a hash-selected node and retains its inspector outside later filters", () => {
    const node = data.nodes[0];
    const otherStatus = data.filters.statuses.find(({ id }) => id !== node.status)!;
    window.history.replaceState(null, "", `/proof-map.html#node=${node.id}`);
    render(<ProofMap data={data} />);

    expect(screen.getByRole("heading", { name: node.title, level: 2 })).toBeVisible();
    expect(screen.getByLabelText(otherStatus.label)).not.toBeChecked();

    fireEvent.click(screen.getByLabelText(otherStatus.label));

    expect(screen.getByRole("heading", { name: node.title, level: 2 })).toBeVisible();
    expect(screen.getByText(/pinned node is outside the current filters/i)).toBeVisible();
  });

  it("provides search, graph controls, and a resettable fitted viewport", () => {
    const { container } = render(<ProofMap data={data} />);

    expect(screen.getByRole("searchbox", { name: "Search the atlas" })).toBeVisible();
    expect(screen.queryByRole("group", { name: /^Work stream/ })).not.toBeInTheDocument();
    expect(screen.getByLabelText("Map view controls")).toBeVisible();
    expect(screen.getByRole("button", { name: "Zoom in" })).toBeVisible();
    expect(screen.getByRole("button", { name: "Zoom out" })).toBeVisible();
    expect(screen.getByRole("button", { name: "Fit visible nodes" })).toBeVisible();
    expect(screen.getByLabelText("Current map zoom")).toHaveTextContent("100%");

    const atlas = container.querySelector<SVGSVGElement>(".proof-map__canvas")!;
    const fittedViewBox = atlas.getAttribute("viewBox");
    fireEvent.click(screen.getByRole("button", { name: "Zoom in" }));
    expect(atlas).not.toHaveAttribute("viewBox", fittedViewBox!);
    expect(screen.getByLabelText("Current map zoom")).toHaveTextContent("125%");
    fireEvent.click(screen.getByRole("button", { name: "Reset map view" }));
    expect(atlas).toHaveAttribute("viewBox", fittedViewBox!);
  });

  it("supports filters, keyboard inspection, inspector scrolling, and the accessible list", () => {
    const selectedNode = data.nodes[1];
    const selectedEdge = data.edges.find(
      ({ from, to }) => from === selectedNode.id || to === selectedNode.id,
    )!;
    const relatedNodeId = selectedEdge.from === selectedNode.id
      ? selectedEdge.to
      : selectedEdge.from;
    const listNode = data.nodes.find(({ id }) =>
      id !== selectedNode.id && id !== relatedNodeId
    )!;
    const { container } = render(<ProofMap data={data} />);

    expect(screen.getByRole("group", { name: /^Repositories/ })).toBeVisible();
    expect(screen.getByRole("group", { name: /^Proof status/ })).toBeVisible();
    expect(screen.getByLabelText("Trust boundary")).toBeVisible();
    expect(screen.getByLabelText("Filter by work unit")).toBeVisible();
    expect(screen.queryByRole("group", { name: /^Work stream/ })).not.toBeInTheDocument();
    const repositoryFilter = screen.getByLabelText(data.filters.repositories[0].label);
    fireEvent.click(repositoryFilter);
    expect(screen.getByRole("button", { name: "Reset" })).toBeEnabled();
    fireEvent.click(screen.getByRole("button", { name: "Reset" }));
    expect(repositoryFilter).not.toBeChecked();

    const selected = container.querySelector<SVGGElement>(
      `[data-node-id="${selectedNode.id}"]`,
    )!;
    fireEvent.keyDown(selected, { key: "Enter" });
    expect(screen.getByRole("heading", { name: selectedNode.title, level: 2 })).toBeVisible();
    expect(window.location.hash).toBe(`#node=${selectedNode.id}`);
    expect(selected).toHaveClass("is-selected");
    expect(selected).not.toHaveClass("is-related");
    expect(selected).toHaveAttribute("data-emphasis", "selected");
    expect(selected).toHaveAttribute("aria-pressed", "true");

    const related = container.querySelector<SVGGElement>(
      `[data-node-id="${relatedNodeId}"]`,
    )!;
    expect(related).toHaveClass("is-related");
    expect(related).not.toHaveClass("is-selected");
    expect(related).toHaveAttribute("data-emphasis", "related");
    expect(related).toHaveAttribute("aria-pressed", "false");

    const inspector = screen.getByRole("complementary", { name: "Proof node details" });
    expect(within(inspector).getByText("Development history")).toBeVisible();
    for (const workUnitId of selectedNode.workUnitIds) {
      const workUnit = data.development.workUnits.find(({ id }) => id === workUnitId)!;
      expect(within(inspector).getByText(workUnit.title)).toBeVisible();
    }
    inspector.scrollTop = 480;

    fireEvent.click(screen.getByRole("tab", { name: "List" }));
    const listPanel = screen.getByRole("tabpanel", { name: "List" });
    const listButton = within(listPanel).getByRole("button", {
      name: new RegExp(listNode.title.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")),
    });
    fireEvent.click(listButton);
    expect(screen.getByRole("heading", { name: listNode.title, level: 2 })).toBeVisible();
    expect(inspector.scrollTop).toBe(0);
    expect(listButton).toHaveClass("is-selected");
    expect(listButton).toHaveAttribute("aria-pressed", "true");
    expect(window.location.hash).toBe(`#node=${listNode.id}`);

    const gardenEvidence = listNode.evidenceIds
      .map((id) => data.evidence.find((item) => item.id === id))
      .find((item) => item?.repoId === "garden" && item.url);
    expect(gardenEvidence).toBeDefined();
    const gardenEvidenceLink = within(inspector).getByRole("link", {
      name: gardenEvidence!.label,
    });
    expect(gardenEvidenceLink).toHaveAttribute("href", gardenEvidence!.url);
    expect(gardenEvidenceLink?.getAttribute("href")).toMatch(
      /^https:\/\/github\.com\/formal-land\/garden\//,
    );
  });

  it("filters and searches nodes by development provenance", () => {
    const workUnit = data.development.workUnits.find(
      ({ id }) => id === "work-operational-soundness",
    )!;
    const matchingNodes = data.nodes.filter(({ workUnitIds }) =>
      workUnitIds.includes(workUnit.id)
    );
    render(<ProofMap data={data} />);

    fireEvent.change(screen.getByLabelText("Filter by work unit"), {
      target: { value: workUnit.id },
    });
    expect(screen.getByText(`${matchingNodes.length} of ${data.nodes.length} nodes`))
      .toBeVisible();

    fireEvent.change(screen.getByRole("searchbox", { name: "Search the atlas" }), {
      target: { value: "Migrated PR 29" },
    });
    expect(screen.getByText(`${matchingNodes.length} of ${data.nodes.length} nodes`))
      .toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: "Reset" }));
    expect(screen.getByLabelText("Filter by work unit")).toHaveValue("");
    expect(screen.getByRole("searchbox", { name: "Search the atlas" })).toHaveValue("");
    expect(screen.getByText(`${data.nodes.length} of ${data.nodes.length} nodes`))
      .toBeVisible();
  });

  it("collapses and expands clusters from the keyboard", () => {
    const cluster = data.clusters[0];
    const { container } = render(<ProofMap data={data} />);
    const heading = container.querySelector<SVGGElement>(
      `[data-cluster-id="${cluster.id}"] .proof-map__cluster-heading`,
    )!;

    fireEvent.keyDown(heading, { key: "Enter" });
    const collapsed = container.querySelector<SVGGElement>(
      ".proof-map__collapsed-summary[aria-expanded='false']",
    )!;
    expect(collapsed).toHaveAccessibleName(new RegExp(`Expand ${cluster.title} cluster`));

    fireEvent.keyDown(collapsed, { key: " " });
    expect(
      container.querySelector(`[data-cluster-id="${cluster.id}"] .proof-map__cluster-heading`),
    ).toHaveAttribute("aria-expanded", "true");
  });
});
