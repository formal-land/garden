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
    expect(data.flow.nodes.map(({ kind }) => kind)).toEqual([
      "input",
      "component",
      "check",
      "input",
    ]);
    expect(data.flow.edges[1]).toMatchObject({
      id: "edge:merkle-check",
      label: "root",
      summary: "Sends the reconstructed root to the Action checks.",
      kind: "data",
    });
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
  it("explains flow nodes and wires on pointer and keyboard focus", async () => {
    const loader = vi.fn(async () => circuitExplorerFixture);
    const { container } = render(<CircuitExplorer loader={loader} />);

    expect(screen.getByRole("status")).toHaveTextContent("Loading circuit structure");
    const merkleFlowNode = await screen.findByRole("button", { name: /Merkle path\. Reconstructs/ });
    expect(loader).toHaveBeenCalledOnce();
    expect(screen.getByRole("heading", { name: "Choose a circuit item", level: 2 })).toBeVisible();
    expect(screen.getByRole("heading", { name: "Explore the circuit by component", level: 2 })).toBeVisible();
    expect(screen.queryByRole("complementary", { name: "Circuit item details" })).not.toBeInTheDocument();
    expect(container.querySelector(".circuit-workspace")).toHaveClass("circuit-workspace--flow");

    const focusDescription = container.querySelector<HTMLElement>(".circuit-flow-focus")!;
    const witnessEdge = container.querySelector<SVGGElement>('[data-edge-id="edge:witness-merkle"]')!;
    const rootEdge = container.querySelector<SVGGElement>('[data-edge-id="edge:merkle-check"]')!;
    const anchorEdge = container.querySelector<SVGGElement>('[data-edge-id="edge:check-anchor"]')!;

    fireEvent.mouseEnter(merkleFlowNode);
    expect(focusDescription).toHaveAttribute("data-flow-item", "component:merkle-path");
    expect(focusDescription).toHaveTextContent("Reconstructs the note-commitment root.");
    expect(witnessEdge).toHaveClass("is-emphasized");
    expect(rootEdge).toHaveClass("is-emphasized");
    expect(anchorEdge).toHaveClass("is-muted");

    fireEvent.mouseLeave(merkleFlowNode);
    fireEvent.focus(merkleFlowNode);
    expect(focusDescription).toHaveAttribute("data-flow-item", "component:merkle-path");
    expect(rootEdge).toHaveClass("is-emphasized");
    fireEvent.blur(merkleFlowNode);

    fireEvent.mouseEnter(rootEdge);
    expect(focusDescription).toHaveAttribute("data-flow-item", "edge:merkle-check");
    expect(focusDescription).toHaveTextContent("Sends the reconstructed root to the Action checks.");
    expect(rootEdge).toHaveClass("is-emphasized", "is-label-hovered");
    fireEvent.mouseLeave(rootEdge);

    const rootLabel = rootEdge.querySelector("text")!;
    fireEvent.focus(rootLabel);
    expect(focusDescription).toHaveAttribute("data-flow-item", "edge:merkle-check");
    expect(focusDescription).toHaveTextContent("Circuit wire");
    fireEvent.blur(rootLabel);
  });

  it("drills into grouped regions with inline operations and restores focus", async () => {
    const { container } = render(
      <CircuitExplorer loader={async () => circuitExplorerFixture} />,
    );
    const merkleFlowNode = await screen.findByRole("button", { name: /Merkle path\. Reconstructs/ });

    fireEvent.click(merkleFlowNode);
    await waitFor(() => {
      expect(window.location.hash).toContain("level=component");
      expect(window.location.hash).toContain("item=component%3Amerkle-path");
    });
    const componentHeading = within(container.querySelector(".circuit-canvas") as HTMLElement)
      .getByRole("heading", { name: "Merkle path" });
    expect(componentHeading).toHaveFocus();
    expect(screen.getByRole("link", { name: /Open Sinsemilla and Merkle proofs in the Atlas/ }))
      .toHaveAttribute("href", "./proof-map.html#node=gadgets-sinsemilla-merkle");
    expect(screen.getByText(/Source mapping confidence:/)).toHaveTextContent("Mapped");
    expect(container.querySelectorAll(".circuit-card--region")).toHaveLength(1);
    expect(container.querySelectorAll(".circuit-card--gate")).toHaveLength(1);
    expect(container.querySelectorAll(".circuit-card--lookup")).toHaveLength(1);
    expect(container.querySelectorAll(".circuit-card--region-occurrence")).toHaveLength(0);
    expect(screen.queryByRole("button", { name: /exact concrete regions/i })).not.toBeInTheDocument();
    expect(screen.queryByRole("button", { name: /aggregate repeated regions/i })).not.toBeInTheDocument();
    expect(screen.queryByRole("heading", { name: "Explore the circuit by component" })).not.toBeInTheDocument();

    fireEvent.click(container.querySelector<HTMLButtonElement>(".circuit-card--region")!);
    expect(await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Merkle layer", level: 2 })).toHaveFocus();
    const occurrencePicker = screen.getByRole("combobox", { name: /^Exact occurrence shown/ });
    expect(occurrencePicker).toHaveValue("region:0");
    expect(container.querySelectorAll(".circuit-occurrence")).toHaveLength(1);
    expect(container.querySelectorAll(".circuit-operation-record")).toHaveLength(4);
    const inspector = screen.getByRole("complementary", { name: "Circuit item details" });
    expect(within(inspector).getByText("2 mapping candidates")).toBeVisible();
    expect(within(inspector).getByRole("link", { name: /src\/circuit\.rs/ }))
      .toHaveAttribute("href", rawCircuitExplorerFixture.sources.records[1].url);
    expect(within(container.querySelector(".circuit-canvas") as HTMLElement)
      .getByText("action / merkle path")).toBeVisible();

    fireEvent.change(occurrencePicker, { target: { value: "region:1" } });
    expect(occurrencePicker).toHaveValue("region:1");
    expect(container.querySelectorAll(".circuit-occurrence")).toHaveLength(1);
    expect(container.querySelectorAll(".circuit-operation-record")).toHaveLength(1);
    expect(container.querySelector('[data-operation-id="region:1/op:0"]')).toBeVisible();
    expect(container.querySelector('[data-operation-id="region:0/op:2"]')).not.toBeInTheDocument();

    fireEvent.change(occurrencePicker, { target: { value: "region:0" } });
    expect(container.querySelectorAll(".circuit-operation-record")).toHaveLength(4);

    const copyOperation = container.querySelector<HTMLElement>('[data-operation-id="region:0/op:2"]')!;
    expect(copyOperation.tagName).toBe("ARTICLE");
    expect(within(copyOperation).getByRole("heading", { name: "Copy", level: 4 })).toBeVisible();
    expect(within(copyOperation).getAllByText("column A2")).toHaveLength(2);
    expect(within(copyOperation).queryByRole("button")).not.toBeInTheDocument();
    expect(within(container.querySelector(".circuit-canvas") as HTMLElement)
      .queryByRole("heading", { name: "Copy", level: 2 })).not.toBeInTheDocument();

    fireEvent.click(screen.getByRole("button", { name: "Merkle" }));
    expect(await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Merkle path", level: 2 })).toHaveFocus();
    fireEvent.click(screen.getByRole("button", { name: "Circuit flow" }));
    expect(await screen.findByRole("heading", { name: "Choose a circuit item", level: 2 })).toHaveFocus();
    expect(screen.getByRole("heading", { name: "Explore the circuit by component", level: 2 })).toBeVisible();
    expect(screen.queryByRole("complementary", { name: "Circuit item details" })).not.toBeInTheDocument();

    fireEvent.click(screen.getByRole("button", { name: /Anchor instance\. Exposes/ }));
    expect(await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Anchor instance", level: 2 })).toHaveFocus();
    const instanceOperation = container.querySelector<HTMLElement>('[data-operation-id="region:1/op:1"]')!;
    expect(instanceOperation.tagName).toBe("ARTICLE");
    expect(instanceOperation).toHaveTextContent("Constrain Instance");
    expect(within(instanceOperation).getByText("column Primary")).toBeVisible();
    expect(within(instanceOperation).getByText("offset 3")).toBeVisible();
    expect(within(instanceOperation).getByText("row 3")).toBeVisible();
    expect(within(instanceOperation).queryByRole("button")).not.toBeInTheDocument();
  });

  it("searches every layer without stealing focus and opens inline owner records", async () => {
    const { container } = render(
      <CircuitExplorer loader={async () => circuitExplorerFixture} />,
    );
    await screen.findByRole("searchbox", { name: "Search circuit structure" });

    const search = screen.getByRole("searchbox", { name: "Search circuit structure" });
    search.focus();
    fireEvent.change(search, { target: { value: "Current root matches the parent" } });
    expect(search).toHaveFocus();
    expect(screen.getByText(/matching items suggested/)).toBeVisible();

    const results = container.querySelector("#circuit-search-results") as HTMLElement;
    const constraintResult = within(results).getByRole("button", {
      name: /ConstraintCurrent root matches the parent/,
    });
    fireEvent.click(constraintResult);
    await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Merkle consistency", level: 2 });
    expect(window.location.hash).toBe(
      "#level=detail&item=gate%3Amerkle-consistency&focus=constraint%3Amerkle-equality",
    );
    expect(screen.getByText(/shown directly inside its gate/)).toBeVisible();
    const constraint = container.querySelector<HTMLElement>('[data-constraint-id="constraint:merkle-equality"]')!;
    expect(constraint.tagName).toBe("ARTICLE");
    expect(within(constraint).getByRole("heading", {
      name: "Current root matches the parent",
      level: 3,
    })).toBeVisible();
    expect(constraint).toHaveTextContent("QMerkle");
    expect(constraint).toHaveTextContent("A2, F3");
    expect(constraint).toHaveTextContent("-1, 0");
    expect(within(constraint).queryByRole("button")).not.toBeInTheDocument();
    await waitFor(() => expect(constraint).toHaveFocus());
    expect(screen.queryByRole("heading", { name: "Explore the circuit by component" })).not.toBeInTheDocument();

    fireEvent.change(search, { target: { value: "region:0/op:2" } });
    const operationResults = container.querySelector("#circuit-search-results") as HTMLElement;
    fireEvent.click(within(operationResults).getByRole("button", { name: /OperationCopy/ }));
    await within(container.querySelector(".circuit-canvas") as HTMLElement)
      .findByRole("heading", { name: "Merkle layer", level: 2 });
    expect(window.location.hash).toBe(
      "#level=detail&item=region%3A0&focus=region%3A0%2Fop%3A2",
    );
    expect(screen.getByText(/operation “Copy” is shown directly inside/)).toBeVisible();
    const operation = container.querySelector<HTMLElement>('[data-operation-id="region:0/op:2"]')!;
    expect(operation).toBeVisible();
    await waitFor(() => expect(operation).toHaveFocus());
  });

  it("canonicalizes legacy exact, constraint, and operation hashes and recovers invalid links", async () => {
    window.history.replaceState(
      null,
      "",
      "/circuit.html#level=detail&item=region%3A0&mode=exact",
    );
    const { unmount } = render(
      <CircuitExplorer loader={async () => circuitExplorerFixture} />,
    );
    expect((await screen.findAllByText("4 operations")).length).toBeGreaterThan(0);
    expect(within(document.querySelector(".circuit-canvas") as HTMLElement)
      .getByRole("heading", { name: "Merkle layer", level: 2 })).toHaveFocus();
    await waitFor(() => expect(window.location.hash).toBe("#level=detail&item=region%3A0"));
    expect(document.querySelectorAll(".circuit-operation-record")).toHaveLength(4);
    unmount();

    window.history.replaceState(
      null,
      "",
      "/circuit.html#level=detail&item=constraint%3Amerkle-equality&mode=exact",
    );
    const constraintView = render(
      <CircuitExplorer loader={async () => circuitExplorerFixture} />,
    );
    const constraintCanvas = await constraintView.findByRole("region", {
      name: "Detail circuit layer",
    });
    expect(within(constraintCanvas)
      .getByRole("heading", { name: "Merkle consistency", level: 2 })).toBeVisible();
    await waitFor(() => {
      expect(window.location.hash).toBe(
        "#level=detail&item=gate%3Amerkle-consistency&focus=constraint%3Amerkle-equality",
      );
    });
    expect(screen.getByText(/constraint .* is shown directly inside its gate/i)).toBeVisible();
    const constraint = document.querySelector<HTMLElement>(
      '[data-constraint-id="constraint:merkle-equality"]',
    )!;
    expect(constraint).toBeVisible();
    await waitFor(() => expect(constraint).toHaveFocus());
    constraintView.unmount();

    window.history.replaceState(
      null,
      "",
      "/circuit.html#level=detail&item=region%3A0%2Fop%3A2&mode=exact",
    );
    const operationView = render(
      <CircuitExplorer loader={async () => circuitExplorerFixture} />,
    );
    const operationCanvas = await operationView.findByRole("region", {
      name: "Detail circuit layer",
    });
    expect(within(operationCanvas)
      .getByRole("heading", { name: "Merkle layer", level: 2 })).toBeVisible();
    await waitFor(() => {
      expect(window.location.hash).toBe(
        "#level=detail&item=region%3A0&focus=region%3A0%2Fop%3A2",
      );
    });
    expect(screen.getByText(/operation “Copy” is shown directly inside/)).toBeVisible();
    const operation = document.querySelector<HTMLElement>('[data-operation-id="region:0/op:2"]')!;
    expect(operation).toBeVisible();
    await waitFor(() => expect(operation).toHaveFocus());
    operationView.unmount();

    window.history.replaceState(
      null,
      "",
      "/circuit.html#level=detail&item=region%3Amissing&mode=exact",
    );
    render(<CircuitExplorer loader={async () => circuitExplorerFixture} />);
    expect(await screen.findByText(/linked circuit item “region:missing” is not present/)).toBeVisible();
    expect(window.location.hash).toBe("");
    expect(screen.getByRole("heading", { name: "Explore the circuit by component", level: 2 })).toBeVisible();
  });

  it("renders parent-owned lookup initialization and structured lookup pairs", async () => {
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
    expect(window.location.hash).toBe(
      "#level=component&item=component%3Amerkle-path&focus=lookup-tables%3A0",
    );
    expect(screen.getByText(/operation “generator_table” is shown directly inside/)).toBeVisible();
    const initializationOperation = document.querySelector<HTMLElement>(
      '[data-operation-id="lookup-tables:0"]',
    )!;
    await waitFor(() => expect(initializationOperation).toHaveFocus());
    expect(screen.queryByRole("heading", { name: "Explore the circuit by component" })).not.toBeInTheDocument();
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
    expect(window.location.hash).toBe("#level=detail&item=lookup-argument%3A0");
  });

  it("paginates large inline operation traces", async () => {
    const baseOperation = circuitExplorerFixture.synthesis.operations[0];
    const pagedOperations = Array.from({ length: 61 }, (_, index) => ({
      ...baseOperation,
      id: `region:0/op:paged-${index}`,
      title: `Synthetic operation ${index + 1}`,
      occurrenceId: "region:0",
      regionId: "region:0",
    }));
    const pagedFixture = {
      ...circuitExplorerFixture,
      synthesis: {
        ...circuitExplorerFixture.synthesis,
        operations: pagedOperations,
        occurrences: circuitExplorerFixture.synthesis.occurrences.map((occurrence) => ({
          ...occurrence,
          operationIds: occurrence.id === "region:0"
            ? pagedOperations.map(({ id }) => id)
            : [],
        })),
      },
    };
    window.history.replaceState(
      null,
      "",
      "/circuit.html#level=detail&item=region-group%3Amerkle-layer",
    );
    const { container } = render(
      <CircuitExplorer loader={async () => pagedFixture} />,
    );

    expect(await screen.findByRole("heading", { name: "Region operations", level: 3 })).toBeVisible();
    expect(container.querySelectorAll(".circuit-operation-record")).toHaveLength(60);
    expect(container.querySelectorAll(".circuit-operation-record button")).toHaveLength(0);
    fireEvent.click(screen.getByRole("button", { name: "Show all 1 remaining operations" }));
    expect(container.querySelectorAll(".circuit-operation-record")).toHaveLength(61);
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
