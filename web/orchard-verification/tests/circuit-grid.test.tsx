import {
  cleanup,
  fireEvent,
  render,
  screen,
  waitFor,
  within,
} from "@testing-library/react";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import { normalizeCircuitGridData } from "../src/circuit-grid/loader";
import { CIRCUIT_GRID_SCHEMA } from "../src/circuit-grid/model";
import { CircuitGrid } from "../src/components/CircuitGrid";

const rawCircuitGridFixture = {
  schema: CIRCUIT_GRID_SCHEMA,
  metadata: {
    circuit: {
      id: "orchard-action",
      name: "Fixture Orchard Action circuit",
      version: "FixedPostNu6_2",
      field: "pallas::Base",
      k: 11,
      rowCount: 2048,
      floorPlanner: "V1",
      stage: "pre-selector-compression",
    },
    capabilities: {
      adviceAssignments: "references-only",
      witnessValues: "omitted",
      selectors: "virtual",
      permutation: "copy-edges",
    },
    inputs: [
      {
        id: "rocq-synthesis",
        path: "Garden/Orchard/Snapshots/circuit_synthesis_generated_from_model.json",
        sha256: "a".repeat(64),
      },
      {
        id: "rust-synthesis",
        path: "Garden/Orchard/Snapshots/circuit_synthesis_generated_from_implementation.json",
        sha256: "b".repeat(64),
      },
    ],
    parity: {
      configure: "equal",
      synthesis: "equal",
    },
    repositoryRefs: {
      garden: "8d99eeec",
      halo2: "6fcb5136",
      orchard: "8da86412",
    },
  },
  columns: [
    {
      id: "instance:0",
      kind: "instance",
      index: 0,
      name: "Primary",
      role: "Public output",
    },
    ...Array.from({ length: 10 }, (_, index) => ({
      id: `advice:${index}`,
      kind: "advice",
      index,
      name: `A${index}`,
      role: "Witness reference",
    })),
    ...Array.from({ length: 14 }, (_, index) => ({
      id: `fixed:${index}`,
      kind: "fixed",
      index,
      name: index < 3 ? ["TableIdx", "TableX", "TableY"][index] : `F${index}`,
      role: index < 3 ? "Lookup table" : "Fixed assignment",
    })),
  ],
  selectors: Array.from({ length: 56 }, (_, index) => ({
    id: `selector:${index}`,
    index,
    name: index === 5 ? "QWitnessPoint" : `Q${index}`,
    gateIds: index === 5 ? ["gate:5"] : [],
    lookupIds: [],
    circuitTarget: index === 5
      ? {
          id: "target:gate:5",
          kind: "gate",
          title: "Witness point gate",
          href: "./circuit.html#level=detail&item=gate%3A5",
        }
      : undefined,
  })),
  regions: [
    {
      id: "region:2",
      regionIndex: 2,
      startRow: 1758,
      endRow: 1759,
      name: "Witness point",
      namespace: ["Action", "Spend", "Witness point"],
      componentId: "component:witness-point",
      selectorIds: ["selector:5"],
      gateIds: ["gate:5"],
      lookupIds: [],
      operationIds: ["region:2/op:0", "region:2/op:1"],
      circuitTarget: {
        id: "target:region:2",
        kind: "region",
        title: "Witness point region",
        href: "./circuit.html#level=detail&item=region%3A2",
      },
    },
  ],
  events: [
    {
      id: "trace-event:0",
      kind: "enable_selector",
      row: 1758,
      selectorId: "selector:5",
      annotation: "Enable witness-point gate",
      endpoints: [],
      peerEventIds: [],
      regionId: "region:2",
      namespace: ["Action", "Spend", "Witness point"],
      gateIds: ["gate:5"],
      lookupIds: [],
      operationIds: ["region:2/op:0"],
      circuitTarget: {
          id: "target:operation:0",
          kind: "operation",
          title: "Selector activation",
          href: "./circuit.html#level=detail&item=region%3A2&focus=region%3A2%2Fop%3A0",
        },
    },
    {
      id: "trace-event:1",
      kind: "assign_fixed",
      row: 1758,
      columnId: "fixed:3",
      annotation: "Witness-point coefficient",
      value: "1",
      endpoints: [{ columnId: "fixed:3", row: 1758 }],
      peerEventIds: [],
      regionId: "region:2",
      namespace: ["Action", "Spend", "Witness point"],
      gateIds: ["gate:5"],
      lookupIds: [],
      operationIds: ["region:2/op:1"],
    },
    {
      id: "trace-event:2",
      kind: "copy",
      row: 1758,
      endpoints: [
        { columnId: "advice:0", row: 1758 },
        { columnId: "advice:1", row: 1759 },
      ],
      peerEventIds: [],
      regionId: "region:2",
      namespace: ["Action", "Spend", "Witness point"],
      gateIds: [],
      lookupIds: [],
      operationIds: ["region:2/op:2"],
    },
  ],
  rows: [
    {
      row: 1758,
      eventIds: ["trace-event:0", "trace-event:1", "trace-event:2"],
      regionIds: ["region:2"],
      selectorIds: ["selector:5"],
      columnIds: ["fixed:3", "advice:0"],
    },
    {
      row: 1759,
      eventIds: ["trace-event:2"],
      regionIds: ["region:2"],
      selectorIds: [],
      columnIds: ["advice:1"],
    },
  ],
  summary: {
    columnCount: 25,
    selectorCount: 56,
    regionCount: 1,
    eventCount: 3,
    populatedRowCount: 2,
    counts: {
      enableSelector: 1,
      assignFixed: 1,
      copy: 1,
    },
  },
};

const circuitGridFixture = normalizeCircuitGridData(rawCircuitGridFixture);

beforeEach(() => {
  window.history.replaceState(null, "", "/circuit-grid.html");
});

afterEach(() => {
  cleanup();
  vi.restoreAllMocks();
});

describe("circuit grid schema adapter", () => {
  it("preserves the physical layout, virtual selectors, coverage, and links", () => {
    expect(circuitGridFixture.metadata.circuit).toMatchObject({
      k: 11,
      rowCount: 2048,
      floorPlanner: "V1",
      stage: "pre-selector-compression",
    });
    expect(circuitGridFixture.columns).toHaveLength(25);
    expect(circuitGridFixture.selectors).toHaveLength(56);
    expect(circuitGridFixture.metadata.capabilities).toEqual({
      adviceAssignments: "references-only",
      witnessValues: "omitted",
      selectors: "virtual",
      permutation: "copy-edges",
    });
    expect(circuitGridFixture.rows[0]).toMatchObject({
      row: 1758,
      selectorIds: ["selector:5"],
      regionIds: ["region:2"],
    });
    expect(circuitGridFixture.selectors[5].circuitTarget?.href)
      .toBe("./circuit.html#level=detail&item=gate%3A5");
  });

  it("rejects incompatible schemas and out-of-bounds events", () => {
    expect(() => normalizeCircuitGridData({
      ...rawCircuitGridFixture,
      schema: "garden.halo2.circuit-grid.v2",
    })).toThrow(/Unsupported circuit grid schema/);

    expect(() => normalizeCircuitGridData({
      ...rawCircuitGridFixture,
      events: [
        {
          ...rawCircuitGridFixture.events[0],
          row: 2048,
        },
      ],
    })).toThrow(/outside 0–2047/);
  });
});

describe("circuit grid interactions", () => {
  it("lazy-loads a collapsed 26-track grid and expands all 56 selectors", async () => {
    const loader = vi.fn(async () => circuitGridFixture);
    const { container } = render(<CircuitGrid loader={loader} />);

    expect(screen.getByRole("heading", { name: "Loading circuit grid" })).toBeVisible();
    await screen.findByRole("heading", { name: "Orchard Circuit Grid" });
    expect(loader).toHaveBeenCalledOnce();
    expect(screen.getByRole("searchbox", { name: "Search circuit grid" })).toBeVisible();
    expect(screen.getByRole("tab", { name: "Grid" })).toHaveAttribute(
      "aria-selected",
      "true",
    );

    const trackSurface = container.querySelector<HTMLElement>("[data-track-count]")!;
    expect(trackSurface).toHaveAttribute("data-track-count", "26");
    fireEvent.click(screen.getByRole("button", { name: "Expand 56 selectors" }));
    expect(trackSurface).toHaveAttribute("data-track-count", "81");
    expect(screen.getByRole("button", { name: "Collapse 56 selectors" })).toBeVisible();
  });

  it("restores a deep-linked selector, exposes multiline context, and pins Circuit links", async () => {
    window.history.replaceState(
      null,
      "",
      "/circuit-grid.html#row=1758&column=selector%3A5",
    );
    const { container } = render(
      <CircuitGrid loader={async () => circuitGridFixture} />,
    );

    const cell = await waitFor(() => {
      const result = container.querySelector<HTMLElement>(
        '[data-row="1758"][data-column="selector:5"]',
      );
      expect(result).toBeVisible();
      return result!;
    });
    const inspector = screen.getByRole("complementary", { name: "Cell details" });
    expect(within(inspector).getByRole("heading", { name: /^Row 1758 · QWitnessPoint/ }))
      .toBeVisible();
    expect(inspector).toHaveTextContent("Witness point");
    const circuitLink = within(inspector).getAllByRole("link", {
      name: /Open .* in Circuit/i,
    })[0] as HTMLAnchorElement;
    expect(circuitLink.getAttribute("href")).toContain("circuit.html#level=detail");

    fireEvent.mouseEnter(cell);
    const tooltip = screen.getByRole("tooltip");
    expect(tooltip).toHaveTextContent("Row 1758");
    expect(tooltip).toHaveTextContent("QWitnessPoint");
    expect(tooltip.querySelectorAll("p").length).toBeGreaterThan(1);
    fireEvent.mouseLeave(cell);

    fireEvent.click(within(inspector).getByRole("button", { name: "Close cell details" }));
    expect(screen.queryByRole("complementary", { name: "Cell details" }))
      .not.toBeInTheDocument();
    fireEvent.click(cell);
    expect(screen.getByRole("complementary", { name: "Cell details" })).toBeVisible();
    expect(window.location.hash).toBe("#row=1758&column=selector%3A5");
  });

  it("offers a keyboard-accessible List view without implying absent witness data", async () => {
    render(<CircuitGrid loader={async () => circuitGridFixture} />);
    await screen.findByRole("heading", { name: "Orchard Circuit Grid" });

    fireEvent.click(screen.getByRole("tab", { name: "List" }));
    const list = screen.getByRole("tabpanel", { name: "List" });
    expect(list).toBeVisible();
    expect(within(list).getByText(/Witness point/)).toBeVisible();
    const coverage = screen.getByRole("note");
    expect(coverage).toHaveTextContent(/ordinary(?: witness)? assignments are not recorded/i);
    expect(coverage).toHaveTextContent("references-only");

    const rowItem = within(list).getByRole("button", { name: /Row 1758.*Witness point/i });
    rowItem.focus();
    expect(rowItem).toHaveFocus();
    fireEvent.click(rowItem);
    expect(screen.getByRole("complementary", { name: "Cell details" })).toBeVisible();
    expect(window.location.hash).toContain("row=1758");
  });
});
