import {
  cleanup,
  fireEvent,
  render,
  screen,
  waitFor,
  within,
} from "@testing-library/react";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import { normalizeCircuitExplorerData } from "../src/circuit/loader";
import { CircuitExplorer } from "../src/components/CircuitExplorer";
import {
  circuitExplorerFixture,
  rawCircuitExplorerFixture,
} from "./fixtures/circuit-explorer";

beforeEach(() => {
  window.history.replaceState(null, "", "/circuit.html");
});

afterEach(() => {
  cleanup();
  vi.restoreAllMocks();
});

describe("circuit explorer schema adapter", () => {
  it("normalizes grouped and exact synthesis records without flattening the AST", () => {
    const data = normalizeCircuitExplorerData(rawCircuitExplorerFixture);

    expect(data.metadata.title).toBe("Fixture Orchard Action circuit");
    expect(data.metadata.metrics.map(({ value }) => value)).toEqual([
      "1",
      "1",
      "1",
      "2",
      "7",
      "2",
    ]);
    expect(data.flow.bounds).toEqual({ width: 1000, height: 600 });
    expect(data.flow.nodes.at(-1)?.kind).toBe("output");
    expect(data.synthesis.components.map(({ id }) => id)).toEqual([
      "component:private-inputs",
      "component:merkle-path",
      "component:action-checks",
      "component:instance-root",
    ]);
    expect(data.synthesis.components.at(-1)).toMatchObject({
      instanceRowIds: ["instance-row:0"],
      operationIds: ["region:1/op:1"],
    });

    expect(data.synthesis.regions).toHaveLength(1);
    expect(data.synthesis.regions[0]).toMatchObject({
      id: "region-group:merkle-layer",
      count: 2,
      eventCount: 6,
      selectorCount: 1,
      copyCount: 2,
      occurrenceIds: ["region:0", "region:1"],
      sourceConfidence: "ambiguous",
    });
    expect(data.synthesis.occurrences).toHaveLength(2);
    expect(data.synthesis.occurrences[0]).toMatchObject({
      groupId: "region-group:merkle-layer",
      operationIds: [
        "region:0/op:0",
        "region:0/op:1",
        "region:0/op:2",
        "region:0/op:3",
      ],
      namespacePath: ["action", "merkle path"],
    });

    const selector = data.synthesis.operations[0];
    expect(selector.selectorId).toBe("7");
    expect(selector.selectorName).toBe("QMerkle");
    expect(selector.relativeOffset).toBe(0);
    expect(selector.absoluteRow).toBe(12);
    expect(selector.sourceIds).toEqual(["source:rocq"]);
    expect(selector.sourceConfidence).toBe("exact");
    expect(data.synthesis.operations[2].cells.map(({ column }) => column)).toEqual(["A2", "A2"]);
    expect(data.synthesis.operations[5]).toMatchObject({
      kind: "constrain-instance",
      componentId: "component:instance-root",
      sourceConfidence: "mapped",
    });
    expect(data.synthesis.operations[5].regionId).toBeUndefined();
    expect(data.synthesis.operations[5].sourceIds).toEqual([]);
    expect(data.synthesis.operations[5].sourceCandidates[0]).toMatchObject({
      sourceId: "source:rocq",
      confidence: "mapped",
    });
    expect(data.synthesis.operations[5].cells).toEqual([
      expect.objectContaining({ kind: "advice", column: "A2", regionId: "region:1" }),
      expect.objectContaining({
        id: "cell:instance:0:row:3",
        kind: "instance",
        column: "Primary",
        relativeOffset: 3,
        absoluteRow: 3,
      }),
    ]);
    expect(data.synthesis.operations[6].lookupEntries).toEqual([
      {
        id: "lookup-column:0",
        column: "0",
        columnName: "TableRange",
        annotation: "table_idx",
        valueCount: 1024,
        defaultValue: "0",
      },
    ]);

    const constraint = data.configure.constraints[0];
    expect(constraint.expressionAst).toEqual(
      rawCircuitExplorerFixture.configure.gates[0].constraints[0].constraint,
    );
    expect(constraint.expression).toContain("QMerkle");
    expect(constraint.columns).toEqual(["A2", "F3"]);
    expect(constraint.rotations).toEqual([-1, 0]);
    expect(constraint.sourceConfidence).toBe("exact");
    expect(data.configure.lookups[0].pairs[0]).toMatchObject({
      inputAst: rawCircuitExplorerFixture.configure.lookups[0].pairs[0].input,
      inputExpression: "A5@0",
      tableId: "0",
      tableName: "TableRange",
    });

    expect(data.sources.find(({ id }) => id === "source:rust")?.confidence).toBe("mapped");
    expect(data.diagnostics[0]).toMatchObject({
      id: "region-source-ambiguous",
      severity: "warning",
      itemIds: ["region:1"],
    });
  });

  it("rejects incompatible schema versions and dangling flow edges", () => {
    expect(() => normalizeCircuitExplorerData({
      ...rawCircuitExplorerFixture,
      schema: "garden.orchard.circuit-highlevel.v2",
    })).toThrow(/Unsupported circuit explorer schema/);

    expect(() => normalizeCircuitExplorerData({
      ...rawCircuitExplorerFixture,
      flow: {
        ...rawCircuitExplorerFixture.flow,
        edges: [{ id: "dangling", from: "missing", to: "component:merkle-path" }],
      },
    })).toThrow(/dangling endpoint/);
  });

  it("does not assign a shared gate to an arbitrary first component", () => {
    const sharedGateFixture = structuredClone(rawCircuitExplorerFixture);
    Object.assign(sharedGateFixture.configure.gates[0], {
      componentId: null,
      componentIds: ["component:merkle-path", "component:action-checks"],
    });

    const data = normalizeCircuitExplorerData(sharedGateFixture);
    expect(data.configure.gates[0].componentId).toBeUndefined();
    expect(data.configure.gates[0].componentIds).toEqual([
      "component:merkle-path",
      "component:action-checks",
    ]);
  });
});

describe("circuit explorer interactions", () => {
  it("drills through aggregate and exact layers, preserves provenance, and restores focus", async () => {
    const loader = vi.fn(async () => circuitExplorerFixture);
    const { container } = render(<CircuitExplorer loader={loader} />);

    expect(screen.getByRole("status")).toHaveTextContent("Loading circuit structure");
    const merkleFlowNode = await screen.findByRole("button", { name: /Merkle path\. Reconstructs/ });
    expect(loader).toHaveBeenCalledOnce();

    fireEvent.click(merkleFlowNode);
    await waitFor(() => {
      expect(window.location.hash).toContain("level=component");
      expect(window.location.hash).toContain("item=component%3Amerkle-path");
    });
    const componentHeading = within(container.querySelector(".circuit-canvas") as HTMLElement)
      .getByRole("heading", { name: "Merkle path" });
    expect(componentHeading).toHaveFocus();
    expect(screen.getByRole("link", { name: /Open gadgets-sinsemilla-merkle in the Atlas/ }))
      .toHaveAttribute("href", "./proof-map.html#node=gadgets-sinsemilla-merkle");
    expect(screen.getByText(/Source mapping confidence:/)).toHaveTextContent("Mapped");

    const aggregateRegion = container.querySelector<HTMLButtonElement>(".circuit-card--region")!;
    fireEvent.click(aggregateRegion);
    expect(await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Merkle layer", level: 2 })).toHaveFocus();
    expect(container.querySelector(".circuit-detail-summary"))
      .toHaveTextContent("Switch to Exact to inspect the 2 concrete occurrences");
    const inspector = screen.getByRole("complementary", { name: "Circuit item details" });
    fireEvent.click(within(inspector).getByText("2 mapping candidates"));
    expect(within(inspector).getByRole("link", { name: /src\/circuit\.rs/ }))
      .toHaveAttribute("href", rawCircuitExplorerFixture.sources.records[1].url);

    fireEvent.click(screen.getByRole("button", { name: "Show exact concrete regions" }));
    await waitFor(() => {
      expect(container.querySelectorAll(".circuit-card--region-occurrence")).toHaveLength(2);
    });
    expect(within(container.querySelector(".circuit-canvas") as HTMLElement)
      .getByRole("heading", { name: "Merkle layer", level: 2 })).toHaveFocus();

    fireEvent.click(container.querySelectorAll<HTMLButtonElement>(".circuit-card--region-occurrence")[0]);
    expect(await screen.findByText("4 operations")).toBeVisible();
    expect(within(container.querySelector(".circuit-canvas") as HTMLElement)
      .getByRole("heading", { name: "Merkle layer", level: 2 })).toHaveFocus();
    expect(within(container.querySelector(".circuit-canvas") as HTMLElement)
      .getByText("action / merkle path")).toBeVisible();

    fireEvent.click(container.querySelectorAll<HTMLButtonElement>(".circuit-operation-list button")[2]);
    expect(await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Copy", level: 2 })).toHaveFocus();
    const cellTable = screen.getByRole("table", { name: "Cells referenced by this operation" });
    expect(within(cellTable).getAllByText("A2")).toHaveLength(2);
    expect(screen.getByText(/Source mapping confidence:/)).toHaveTextContent("Exact");

    fireEvent.click(screen.getByRole("button", { name: "Merkle" }));
    expect(await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Merkle path", level: 2 })).toHaveFocus();
    fireEvent.click(screen.getByRole("button", { name: "Circuit flow" }));
    await waitFor(() => expect(container.querySelector(".circuit-canvas")).toHaveFocus());

    fireEvent.click(container.querySelector<HTMLButtonElement>(".circuit-flow-node--output")!);
    expect(await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Anchor instance", level: 2 })).toHaveFocus();
    const instanceOperation = container.querySelector<HTMLButtonElement>(".circuit-card--operation")!;
    expect(instanceOperation).toHaveTextContent("Constrain Instance");
    fireEvent.click(instanceOperation);
    const instanceTable = await screen.findByRole("table", { name: "Cells referenced by this operation" });
    expect(within(instanceTable).getByText("Primary")).toBeVisible();
    expect(within(instanceTable).getAllByText("3")).toHaveLength(2);
  });

  it("searches every layer without stealing focus and opens exact gate constraints", async () => {
    const { container } = render(
      <CircuitExplorer loader={async () => circuitExplorerFixture} />,
    );
    await screen.findByRole("searchbox", { name: "Search circuit structure" });

    const search = screen.getByRole("searchbox", { name: "Search circuit structure" });
    search.focus();
    fireEvent.change(search, { target: { value: "Merkle consistency" } });
    expect(search).toHaveFocus();
    expect(screen.getByText(/matching items suggested/)).toBeVisible();

    const results = container.querySelector("#circuit-search-results") as HTMLElement;
    const gateResult = within(results).getByRole("button", { name: /GateMerkle consistency/ });
    fireEvent.click(gateResult);
    expect(await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Merkle consistency", level: 2 })).toHaveFocus();

    fireEvent.click(screen.getByRole("button", { name: "Show exact concrete regions" }));
    const constraintButton = await screen.findByRole("button", {
      name: /Current root matches the parent/,
    });
    expect(constraintButton).toHaveTextContent("QMerkle");
    fireEvent.click(constraintButton);
    expect(await within(container.querySelector(".circuit-canvas") as HTMLElement).findByRole("heading", {
      name: "Current root matches the parent",
      level: 2,
    })).toHaveFocus();
    expect(screen.getByText("A2, F3")).toBeVisible();
    expect(screen.getByText("-1, 0")).toBeVisible();
  });

  it("honors valid hashes and recovers from invalid links", async () => {
    window.history.replaceState(
      null,
      "",
      "/circuit.html#level=detail&item=region%3A0&mode=exact",
    );
    const { unmount } = render(
      <CircuitExplorer loader={async () => circuitExplorerFixture} />,
    );
    expect(await screen.findByText("4 operations")).toBeVisible();
    expect(within(document.querySelector(".circuit-canvas") as HTMLElement)
      .getByRole("heading", { name: "Merkle layer", level: 2 })).toHaveFocus();
    unmount();

    window.history.replaceState(
      null,
      "",
      "/circuit.html#level=detail&item=region%3Amissing&mode=exact",
    );
    render(<CircuitExplorer loader={async () => circuitExplorerFixture} />);
    expect(await screen.findByText(/linked circuit item “region:missing” is not present/)).toBeVisible();
    expect(window.location.hash).toBe("#mode=exact");
  });

  it("renders lookup initialization entries and structured lookup pairs", async () => {
    window.history.replaceState(
      null,
      "",
      "/circuit.html#level=detail&item=lookup-tables%3A0&mode=exact",
    );
    const { unmount } = render(
      <CircuitExplorer loader={async () => circuitExplorerFixture} />,
    );
    const initialization = await screen.findByRole("table", {
      name: "Lookup table columns initialized by this operation",
    });
    expect(within(initialization).getByText("TableRange")).toBeVisible();
    expect(within(initialization).getByText("1024")).toBeVisible();
    expect(within(initialization).getByText("table_idx")).toBeVisible();
    unmount();

    window.history.replaceState(
      null,
      "",
      "/circuit.html#level=detail&item=lookup-argument%3A0",
    );
    render(<CircuitExplorer loader={async () => circuitExplorerFixture} />);
    const pairs = await screen.findByRole("table", { name: "Lookup input and table pairs" });
    expect(within(pairs).getByText("A5@0")).toBeVisible();
    expect(within(pairs).getByText("TableRange (0)")).toBeVisible();
  });

  it("shows a recoverable loading error", async () => {
    const loader = vi.fn()
      .mockRejectedValueOnce(new Error("fixture unavailable"))
      .mockResolvedValueOnce(circuitExplorerFixture);
    render(<CircuitExplorer loader={loader} />);

    expect(await screen.findByRole("alert")).toHaveTextContent("fixture unavailable");
    fireEvent.click(screen.getByRole("button", { name: "Retry loading the circuit" }));
    expect(await screen.findByRole("searchbox", { name: "Search circuit structure" })).toBeVisible();
    expect(loader).toHaveBeenCalledTimes(2);
  });
});
