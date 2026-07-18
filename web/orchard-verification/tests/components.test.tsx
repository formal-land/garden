import { act, fireEvent, render, screen, cleanup, within } from "@testing-library/react";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import { App } from "../src/App";
import { JourneyView } from "../src/components/JourneyView";
import { ProofMap } from "../src/components/ProofMap";
import { orchardVerificationData as data } from "../src/data/content";

function useMediaPreference(reducedMotion: boolean, darkMode = false): void {
  Object.defineProperty(window, "matchMedia", {
    configurable: true,
    writable: true,
    value: (query: string): MediaQueryList => ({
      matches:
        (query.includes("prefers-reduced-motion") && reducedMotion) ||
        (query.includes("prefers-color-scheme") && darkMode),
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
  window.localStorage.clear();
  window.history.replaceState(null, "", "/index.html");
  document.documentElement.dataset.view = "journey";
  delete document.documentElement.dataset.theme;
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

  it("stops at the end and replays from stage one", () => {
    render(<JourneyView data={data} />);

    fireEvent.change(screen.getByRole("slider", { name: "Journey playhead" }), {
      target: { value: String(data.stages.length) },
    });

    const replay = screen.getByRole("button", { name: "Replay journey" });
    expect(replay).toHaveTextContent("Replay");
    expect(screen.getByRole("heading", { name: data.stages.at(-1)!.title, level: 2 })).toBeVisible();

    fireEvent.click(replay);
    expect(screen.getByRole("button", { name: "Pause journey" })).toBeVisible();
    expect(screen.getByRole("heading", { name: data.stages[0].title, level: 2 })).toBeVisible();
  });

  it("does not auto-play when reduced motion is requested", () => {
    vi.useFakeTimers();
    useMediaPreference(true);
    render(<JourneyView data={data} />);

    act(() => vi.advanceTimersByTime(30_000));

    expect(screen.getByRole("button", { name: "Play journey" })).toBeVisible();
    expect(screen.getByText(`Stage 1 of ${data.stages.length}`)).toBeVisible();
  });

  it("selects the configured view and persists theme changes", () => {
    window.localStorage.setItem("garden-orchard-theme", "dark");
    render(<App />);

    expect(screen.getByRole("heading", { name: "Orchard Verification Journey", level: 1 })).toBeVisible();
    expect(document.documentElement.dataset.theme).toBe("dark");
    fireEvent.click(screen.getByRole("button", { name: "Use light theme" }));
    expect(document.documentElement.dataset.theme).toBe("light");
    expect(window.localStorage.getItem("garden-orchard-theme")).toBe("light");

    cleanup();
    document.documentElement.dataset.view = "atlas";
    render(<App />);
    expect(screen.getByRole("heading", { name: "Orchard Verification Atlas", level: 1 })).toBeVisible();
    expect(screen.getByRole("searchbox", { name: "Search the atlas" })).toBeVisible();
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

  it("supports search, reset, keyboard inspection, and the accessible list", () => {
    const node = data.nodes[0];
    const { container } = render(<ProofMap data={data} />);
    const search = screen.getByRole("searchbox", { name: "Search the atlas" });

    fireEvent.change(search, { target: { value: node.title } });
    expect(container.querySelector(".proof-map__result-count")).toHaveTextContent(
      `1 of ${data.nodes.length} nodes match`,
    );
    expect(screen.getByRole("button", { name: "Reset filters" })).toBeEnabled();
    fireEvent.click(screen.getByRole("button", { name: "Reset filters" }));
    expect(search).toHaveValue("");

    const svgNode = container.querySelector<SVGGElement>(`[data-node-id="${node.id}"]`)!;
    fireEvent.keyDown(svgNode, { key: "Enter" });
    expect(screen.getByRole("heading", { name: node.title, level: 2 })).toBeVisible();
    expect(window.location.hash).toBe(`#node=${node.id}`);

    const details = container.querySelector<HTMLDetailsElement>(".proof-map__list-alternative")!;
    fireEvent.click(within(details).getByText(/Browse the filtered atlas as a list/));
    expect(details).toHaveAttribute("open");
    const listNode = within(details).getByRole("button", {
      name: new RegExp(node.title.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")),
    });
    fireEvent.click(listNode);
    expect(screen.getByText("Choose a proof node")).toBeVisible();
    expect(window.location.hash).toBe("");
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
