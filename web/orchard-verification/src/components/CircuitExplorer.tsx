import {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
  type CSSProperties,
  type KeyboardEvent as ReactKeyboardEvent,
  type ReactNode,
} from "react";

import {
  clearCircuitExplorerDataCache,
  loadCircuitExplorerData,
} from "../circuit/loader";
import type {
  CircuitComponent,
  CircuitConstraint,
  CircuitExplorerData,
  CircuitExplorerLevel,
  CircuitExplorerRoute,
  CircuitFlowEdge,
  CircuitFlowNode,
  CircuitGate,
  CircuitItemKind,
  CircuitLookup,
  CircuitMetric,
  CircuitRegionGroup,
  CircuitRegionOccurrence,
  CircuitRegionOperation,
  CircuitSource,
  CircuitSourceConfidence,
  CircuitSourceResolutionCandidate,
  InspectableCircuitItem,
} from "../circuit/model";

const EXACT_PAGE_SIZE = 60;
const RELATIONSHIP_PREVIEW_SIZE = 12;

type DataLoader = () => Promise<CircuitExplorerData>;
type EntryOrigin = "flow" | "component" | "detail";

interface ExplorerEntry {
  readonly key: string;
  readonly id: string;
  readonly kind: CircuitItemKind;
  readonly origin: EntryOrigin;
  readonly title: string;
  readonly summary: string;
  readonly componentId?: string;
  readonly sourceIds: readonly string[];
  readonly sourceConfidence?: CircuitSourceConfidence;
  readonly sourceCandidates: readonly CircuitSourceResolutionCandidate[];
  readonly proofNodeIds: readonly string[];
  readonly metrics: readonly CircuitMetric[];
  readonly namespacePath: readonly string[];
  readonly searchText: string;
  readonly item: InspectableCircuitItem;
}

interface LaidOutNode {
  readonly node: CircuitFlowNode;
  readonly x: number;
  readonly y: number;
}

interface FlowFocus {
  readonly id: string;
  readonly kind: "node" | "wire";
  readonly title: string;
  readonly summary: string;
}

function classNames(
  ...values: ReadonlyArray<string | false | null | undefined>
): string {
  return values.filter(Boolean).join(" ");
}

function titleCase(value: string): string {
  return value
    .replace(/([a-z0-9])([A-Z])/g, "$1 $2")
    .replace(/[_-]+/g, " ")
    .replace(/\b\w/g, (letter) => letter.toUpperCase());
}

const PROOF_NODE_TITLES: Readonly<Record<string, string>> = {
  "gadgets-ecc": "ECC gadget proofs",
  "gadgets-poseidon-range": "Poseidon and range-check proofs",
  "gadgets-sinsemilla-merkle": "Sinsemilla and Merkle proofs",
  "capture-synthesis-model": "Rocq synthesis model",
  "action-valid-inputs": "Action input validity",
  "action-seven-outputs": "Action public outputs",
  "action-theorem": "Action circuit theorem",
};

function proofNodeTitle(id: string): string {
  return PROOF_NODE_TITLES[id] ?? titleCase(id);
}

function defaultRoute(): CircuitExplorerRoute {
  return { level: "flow", itemId: null, query: "", focusId: null };
}

function routeHash(route: CircuitExplorerRoute): string {
  const parameters = new URLSearchParams();
  if (route.level !== "flow") parameters.set("level", route.level);
  if (route.itemId) parameters.set("item", route.itemId);
  if (route.query) parameters.set("q", route.query);
  if (route.focusId) parameters.set("focus", route.focusId);
  const value = parameters.toString();
  return value ? `#${value}` : "";
}

function entryForFlowNode(
  node: CircuitFlowNode,
  componentIds: ReadonlySet<string>,
): ExplorerEntry {
  const componentId = node.componentId ?? (componentIds.has(node.id) ? node.id : undefined);
  return {
    key: `flow:${node.id}`,
    id: node.id,
    kind: node.kind,
    origin: "flow",
    title: node.title,
    summary: node.summary,
    componentId,
    sourceIds: node.sourceIds,
    sourceCandidates: [],
    proofNodeIds: node.proofNodeIds,
    metrics: node.metrics,
    namespacePath: [],
    searchText: [node.id, node.title, node.summary, ...node.tags].join(" ").toLocaleLowerCase(),
    item: node,
  };
}

function buildEntries(data: CircuitExplorerData): ExplorerEntry[] {
  const componentIds = new Set(data.synthesis.components.map(({ id }) => id));
  const sourcesById = new Map(data.sources.map((source) => [source.id, source]));
  const detailProofNodes = (
    sourceIds: readonly string[],
    candidates: readonly CircuitSourceResolutionCandidate[] = [],
  ): string[] => {
    const paths = [...sourceIds, ...candidates.map(({ sourceId }) => sourceId)]
      .flatMap((id) => {
        const source = sourcesById.get(id);
        return source ? [source.path.toLocaleLowerCase()] : [];
      });
    const proofNodeIds = new Set<string>(["capture-synthesis-model"]);
    if (paths.some((path) => path.includes("/poseidon/") || path.includes("range_check"))) {
      proofNodeIds.add("gadgets-poseidon-range");
    }
    if (paths.some((path) => path.includes("/ecc/"))) {
      proofNodeIds.add("gadgets-ecc");
    }
    if (paths.some((path) => path.includes("sinsemilla") || path.includes("merkle"))) {
      proofNodeIds.add("gadgets-sinsemilla-merkle");
    }
    return [...proofNodeIds];
  };
  const occurrencesById = new Map(
    data.synthesis.occurrences.map((occurrence) => [occurrence.id, occurrence]),
  );
  const entries: ExplorerEntry[] = data.flow.nodes.map((node) =>
    entryForFlowNode(node, componentIds)
  );

  for (const component of data.synthesis.components) {
    entries.push({
      key: `component:${component.id}`,
      id: component.id,
      kind: "component",
      origin: "component",
      title: component.title,
      summary: component.summary,
      componentId: component.id,
      sourceIds: component.sourceIds,
      sourceConfidence: component.sourceConfidence,
      sourceCandidates: component.sourceCandidates,
      proofNodeIds: component.proofNodeIds,
      metrics: component.metrics,
      namespacePath: [],
      searchText: [
        component.id,
        component.title,
        component.summary,
        component.detail,
        ...component.tags,
      ].join(" ").toLocaleLowerCase(),
      item: component,
    });
  }

  for (const region of data.synthesis.regions) {
    entries.push({
      key: `region:${region.id}`,
      id: region.id,
      kind: "region",
      origin: "detail",
      title: region.title,
      summary: region.summary || `${region.count} synthesis occurrence${region.count === 1 ? "" : "s"}.`,
      componentId: region.componentId || undefined,
      sourceIds: region.sourceIds,
      sourceConfidence: region.sourceConfidence,
      sourceCandidates: region.sourceCandidates,
      proofNodeIds: detailProofNodes(region.sourceIds, region.sourceCandidates),
      metrics: region.metrics,
      namespacePath: region.namespacePath,
      searchText: [region.id, region.title, region.semanticId, region.summary, ...region.namespacePath, ...region.searchTerms]
        .filter(Boolean).join(" ").toLocaleLowerCase(),
      item: region,
    });
  }

  for (const occurrence of data.synthesis.occurrences) {
    entries.push({
      key: `occurrence:${occurrence.id}`,
      id: occurrence.id,
      kind: "region-occurrence",
      origin: "detail",
      title: occurrence.title,
      summary: `Exact synthesis region ${occurrence.index}.`,
      componentId: occurrence.componentId || undefined,
      sourceIds: occurrence.sourceIds,
      sourceConfidence: occurrence.sourceConfidence,
      sourceCandidates: occurrence.sourceCandidates,
      proofNodeIds: detailProofNodes(occurrence.sourceIds, occurrence.sourceCandidates),
      metrics: occurrence.metrics,
      namespacePath: occurrence.namespacePath,
      searchText: [occurrence.id, occurrence.title, occurrence.semanticId, ...occurrence.namespacePath, ...occurrence.searchTerms]
        .filter(Boolean).join(" ").toLocaleLowerCase(),
      item: occurrence,
    });
  }

  for (const gate of data.configure.gates) {
    entries.push({
      key: `gate:${gate.id}`,
      id: gate.id,
      kind: "gate",
      origin: "detail",
      title: gate.title,
      summary: gate.summary || `${gate.constraintIds.length} named constraint${gate.constraintIds.length === 1 ? "" : "s"}.`,
      componentId: gate.componentId,
      sourceIds: gate.sourceIds,
      sourceConfidence: gate.sourceConfidence,
      sourceCandidates: gate.sourceCandidates,
      proofNodeIds: detailProofNodes(gate.sourceIds, gate.sourceCandidates),
      metrics: gate.metrics,
      namespacePath: [],
      searchText: [gate.id, gate.title, gate.summary, gate.selector, ...gate.regionIds, ...gate.searchTerms]
        .filter(Boolean).join(" ").toLocaleLowerCase(),
      item: gate,
    });
  }

  for (const lookup of data.configure.lookups) {
    entries.push({
      key: `lookup:${lookup.id}`,
      id: lookup.id,
      kind: "lookup",
      origin: "detail",
      title: lookup.title,
      summary: lookup.summary || `${lookup.pairCount} lookup pair${lookup.pairCount === 1 ? "" : "s"}.`,
      componentId: lookup.componentId,
      sourceIds: lookup.sourceIds,
      sourceConfidence: lookup.sourceConfidence,
      sourceCandidates: lookup.sourceCandidates,
      proofNodeIds: detailProofNodes(lookup.sourceIds, lookup.sourceCandidates),
      metrics: lookup.metrics,
      namespacePath: [],
      searchText: [
        lookup.id,
        lookup.title,
        lookup.summary,
        ...lookup.selectorIds,
        ...lookup.tableIds,
        ...lookup.searchTerms,
        ...lookup.pairs.flatMap((pair) => [
          pair.inputExpression,
          pair.tableId,
          pair.tableName,
        ]),
      ]
        .filter(Boolean).join(" ").toLocaleLowerCase(),
      item: lookup,
    });
  }

  for (const constraint of data.configure.constraints) {
    const gate = data.configure.gates.find(({ id }) => id === constraint.gateId);
    entries.push({
      key: `constraint:${constraint.id}`,
      id: constraint.id,
      kind: "constraint",
      origin: "detail",
      title: constraint.title,
      summary: constraint.expression,
      componentId: gate?.componentId,
      sourceIds: constraint.sourceIds.length ? constraint.sourceIds : gate?.sourceIds ?? [],
      sourceConfidence: constraint.sourceConfidence ?? gate?.sourceConfidence,
      sourceCandidates: constraint.sourceCandidates.length
        ? constraint.sourceCandidates
        : gate?.sourceCandidates ?? [],
      proofNodeIds: gate
        ? detailProofNodes(
            constraint.sourceIds.length ? constraint.sourceIds : gate.sourceIds,
            constraint.sourceCandidates.length
              ? constraint.sourceCandidates
              : gate.sourceCandidates,
          )
        : detailProofNodes(constraint.sourceIds, constraint.sourceCandidates),
      metrics: [],
      namespacePath: [],
      searchText: [
        constraint.id,
        constraint.title,
        constraint.expression,
        ...constraint.columns,
        ...constraint.rotations.map(String),
      ].join(" ").toLocaleLowerCase(),
      item: constraint,
    });
  }

  for (const operation of data.synthesis.operations) {
    const occurrence = occurrencesById.get(operation.occurrenceId ?? operation.regionId ?? "");
    entries.push({
      key: `operation:${operation.id}`,
      id: operation.id,
      kind: "operation",
      origin: "detail",
      title: operation.title,
      summary: operation.annotation || titleCase(operation.kind),
      componentId: operation.componentId ?? occurrence?.componentId,
      sourceIds: operation.sourceIds.length ? operation.sourceIds : occurrence?.sourceIds ?? [],
      sourceConfidence: operation.sourceConfidence ?? occurrence?.sourceConfidence,
      sourceCandidates: operation.sourceCandidates.length
        ? operation.sourceCandidates
        : occurrence?.sourceCandidates ?? [],
      proofNodeIds: detailProofNodes(
        operation.sourceIds.length ? operation.sourceIds : occurrence?.sourceIds ?? [],
        operation.sourceCandidates.length
          ? operation.sourceCandidates
          : occurrence?.sourceCandidates ?? [],
      ),
      metrics: [],
      namespacePath: occurrence?.namespacePath ?? [],
      searchText: [
        operation.id,
        operation.title,
        operation.kind,
        operation.annotation,
        operation.selectorId,
        operation.selectorName,
        operation.relativeOffset,
        operation.absoluteRow,
        operation.value,
        ...operation.lookupEntries.flatMap((entry) => [
          entry.id,
          entry.column,
          entry.columnName,
          entry.annotation,
          entry.valueCount,
          entry.defaultValue,
        ]),
        ...operation.cells.map(({ label }) => label),
      ].filter(Boolean).join(" ").toLocaleLowerCase(),
      item: operation,
    });
  }

  return entries;
}

function findSelectedEntry(
  entries: readonly ExplorerEntry[],
  route: CircuitExplorerRoute,
): ExplorerEntry | null {
  if (!route.itemId) return null;
  if (route.level === "flow") {
    return entries.find((entry) => entry.origin === "flow" && entry.id === route.itemId) ?? null;
  }
  if (route.level === "component") {
    return entries.find((entry) => entry.origin === "component" && entry.id === route.itemId) ?? null;
  }
  return entries.find((entry) => entry.origin === "detail" && entry.id === route.itemId) ?? null;
}

function presentationEntryFor(
  data: CircuitExplorerData,
  entries: readonly ExplorerEntry[],
  entry: ExplorerEntry,
): ExplorerEntry {
  if (entry.kind === "constraint") {
    const constraint = entry.item as CircuitConstraint;
    return entries.find((candidate) =>
      candidate.kind === "gate" && candidate.id === constraint.gateId
    ) ?? entry;
  }
  if (entry.kind === "operation") {
    const operation = entry.item as CircuitRegionOperation;
    const occurrenceId = operation.occurrenceId ?? operation.regionId;
    const occurrence = occurrenceId
      ? entries.find((candidate) =>
          candidate.kind === "region-occurrence" && candidate.id === occurrenceId
        )
      : undefined;
    if (occurrence) return occurrence;
    const componentId = operation.componentId ?? data.synthesis.occurrences.find(
      (candidate) => candidate.id === occurrenceId,
    )?.componentId;
    return entries.find((candidate) =>
      candidate.origin === "component" && candidate.id === componentId
    ) ?? entry;
  }
  return entry;
}

function parseRoute(
  data: CircuitExplorerData,
  entries: readonly ExplorerEntry[],
): { route: CircuitExplorerRoute; notice?: string; replace?: boolean } {
  const parameters = new URLSearchParams(window.location.hash.slice(1));
  const requestedLevel = parameters.get("level");
  const level: CircuitExplorerLevel =
    requestedLevel === "component" || requestedLevel === "detail"
      ? requestedLevel
      : "flow";
  const query = parameters.get("q") ?? "";
  const requestedItem = parameters.get("item");
  const requestedFocus = parameters.get("focus");
  const candidate: CircuitExplorerRoute = {
    level,
    itemId: requestedItem,
    query,
    focusId: requestedFocus,
  };

  if (!requestedItem && level === "flow") {
    return { route: candidate, replace: parameters.has("mode") };
  }
  const found = findSelectedEntry(entries, candidate);
  if (found) {
    const presented = presentationEntryFor(data, entries, found);
    if (presented !== found) {
      const targetLevel = presented.origin === "component" ? "component" : "detail";
      return {
        route: {
          level: targetLevel,
          itemId: presented.id,
          query,
          focusId: found.kind === "operation" || found.kind === "constraint" ? found.id : null,
        },
        notice: entryRedirectNotice(found, presented),
        replace: true,
      };
    }
    return { route: candidate, replace: parameters.has("mode") };
  }

  if (level === "component" && !requestedItem && data.synthesis.components[0]) {
    return {
      route: { ...candidate, itemId: data.synthesis.components[0].id },
      notice: "The component link was incomplete, so the first circuit component is shown.",
      replace: true,
    };
  }
  return {
    route: { ...defaultRoute(), query },
    notice: requestedItem
      ? `The linked circuit item “${requestedItem}” is not present in this evidence snapshot.`
      : "The linked circuit view was incomplete, so the circuit overview is shown.",
    replace: true,
  };
}

function entryRedirectNotice(from: ExplorerEntry, to: ExplorerEntry): string {
  if (from.kind === "constraint") {
    return `The constraint “${from.title}” is shown directly inside its gate, “${to.title}”.`;
  }
  return `The operation “${from.title}” is shown directly inside “${to.title}”.`;
}

function layoutFlowNodes(
  nodes: readonly CircuitFlowNode[],
  bounds: CircuitExplorerData["flow"]["bounds"],
): LaidOutNode[] {
  const groups = new Map<CircuitFlowNode["kind"], CircuitFlowNode[]>();
  for (const node of nodes) {
    const existing = groups.get(node.kind) ?? [];
    existing.push(node);
    groups.set(node.kind, existing);
  }
  const columns: Record<CircuitFlowNode["kind"], number> = {
    input: bounds.width * 0.08,
    component: bounds.width * 0.4,
    check: bounds.width * 0.68,
    output: bounds.width * 0.93,
  };

  return nodes.map((node) => {
    if (node.position) {
      return {
        node,
        x: node.position.x <= 1.2 ? node.position.x * bounds.width : node.position.x,
        y: node.position.y <= 1.2 ? node.position.y * bounds.height : node.position.y,
      };
    }
    const peers = groups.get(node.kind) ?? [node];
    const index = peers.indexOf(node);
    const spacing = bounds.height / (peers.length + 1);
    return { node, x: columns[node.kind], y: spacing * (index + 1) };
  });
}

function flowEdgeSummary(
  edge: CircuitFlowEdge,
  nodes: ReadonlyMap<string, CircuitFlowNode>,
): string {
  if (edge.summary) return edge.summary;
  const from = nodes.get(edge.from)?.title ?? edge.from;
  const to = nodes.get(edge.to)?.title ?? edge.to;
  return edge.label
    ? `Carries ${edge.label} from ${from} to ${to}.`
    : `Connects ${from} to ${to}.`;
}

function metricsWithFallback(entry: ExplorerEntry): CircuitMetric[] {
  if (entry.metrics.length) return [...entry.metrics];
  if (entry.kind === "region") {
    const region = entry.item as CircuitRegionGroup;
    return [
      { id: `${entry.id}-occurrences`, label: "Occurrences", value: String(region.count) },
      { id: `${entry.id}-events`, label: "Events", value: String(region.eventCount) },
      { id: `${entry.id}-selectors`, label: "Selector enables", value: String(region.selectorCount) },
      { id: `${entry.id}-copies`, label: "Copies", value: String(region.copyCount) },
    ];
  }
  if (entry.kind === "region-occurrence" && "eventCount" in entry.item) {
    const occurrence = entry.item as CircuitRegionOccurrence;
    return [
      { id: `${entry.id}-events`, label: "Events", value: String(occurrence.eventCount) },
      { id: `${entry.id}-selectors`, label: "Selector enables", value: String(occurrence.selectorCount) },
      { id: `${entry.id}-copies`, label: "Copies", value: String(occurrence.copyCount) },
    ];
  }
  if (entry.kind === "gate") {
    const gate = entry.item as CircuitGate;
    return [{ id: `${entry.id}-constraints`, label: "Constraints", value: String(gate.constraintIds.length) }];
  }
  if (entry.kind === "lookup") {
    const lookup = entry.item as CircuitLookup;
    return [{ id: `${entry.id}-pairs`, label: "Lookup pairs", value: String(lookup.pairCount) }];
  }
  return [];
}

function MetricGrid({ metrics }: { metrics: readonly CircuitMetric[] }) {
  if (!metrics.length) return null;
  return (
    <dl className="circuit-metrics">
      {metrics.map((metric) => (
        <div key={metric.id}>
          <dt>{metric.label}</dt>
          <dd>{metric.value}</dd>
          {metric.detail ? <dd>{metric.detail}</dd> : null}
        </div>
      ))}
    </dl>
  );
}

function RelationshipLinks({
  label,
  ids,
  entries,
  origin,
  kind,
  onSelect,
}: {
  label: string;
  ids: readonly string[];
  entries: readonly ExplorerEntry[];
  origin: EntryOrigin;
  kind?: CircuitItemKind;
  onSelect: (entry: ExplorerEntry) => void;
}) {
  const [expanded, setExpanded] = useState(false);
  useEffect(() => setExpanded(false), [ids]);
  if (!ids.length) return null;
  const visibleIds = expanded ? ids : ids.slice(0, RELATIONSHIP_PREVIEW_SIZE);
  return (
    <section className="circuit-relationship-links">
      <h3>{ids.length} linked {label}</h3>
      <ul>
        {visibleIds.map((id) => {
          const target = entries.find((candidate) =>
            candidate.id === id && candidate.origin === origin && (!kind || candidate.kind === kind)
          );
          return (
            <li key={id}>
              {target ? (
                <button type="button" onClick={() => onSelect(target)}>
                  {target.title}<code>{id}</code>
                </button>
              ) : <code>{id}</code>}
            </li>
          );
        })}
      </ul>
      {!expanded && ids.length > visibleIds.length ? (
        <button
          className="circuit-relationship-links__more"
          type="button"
          onClick={() => setExpanded(true)}
        >
          Show all {ids.length} linked {label}
        </button>
      ) : null}
    </section>
  );
}

function EntryCard({
  entry,
  onSelect,
}: {
  entry: ExplorerEntry;
  onSelect: (entry: ExplorerEntry) => void;
}) {
  return (
    <button
      type="button"
      className={`circuit-card circuit-card--${entry.kind}`}
      onClick={() => onSelect(entry)}
    >
      <span className="circuit-card__kind">{titleCase(entry.kind)}</span>
      <strong>{entry.title}</strong>
      <span>{entry.summary}</span>
      {entry.namespacePath.length ? (
        <code>{entry.namespacePath.join(" / ")}</code>
      ) : null}
    </button>
  );
}

function FlowCanvas({
  data,
  selectedId,
  onSelect,
}: {
  data: CircuitExplorerData;
  selectedId: string | null;
  onSelect: (node: CircuitFlowNode) => void;
}) {
  const laidOut = useMemo(
    () => layoutFlowNodes(data.flow.nodes, data.flow.bounds),
    [data.flow.nodes, data.flow.bounds],
  );
  const { width, height } = data.flow.bounds;
  const byId = useMemo(
    () => new Map(laidOut.map((item) => [item.node.id, item])),
    [laidOut],
  );
  const nodesById = useMemo(
    () => new Map(data.flow.nodes.map((node) => [node.id, node])),
    [data.flow.nodes],
  );
  const [hoveredNodeId, setHoveredNodeId] = useState<string | null>(null);
  const [hoveredEdgeId, setHoveredEdgeId] = useState<string | null>(null);
  const activeNodeId = hoveredNodeId ?? selectedId;
  const connectedNodeIds = useMemo(() => {
    const result = new Set<string>();
    if (activeNodeId) {
      result.add(activeNodeId);
      for (const edge of data.flow.edges) {
        if (edge.from === activeNodeId) result.add(edge.to);
        if (edge.to === activeNodeId) result.add(edge.from);
      }
    }
    if (hoveredEdgeId) {
      const edge = data.flow.edges.find(({ id }) => id === hoveredEdgeId);
      if (edge) {
        result.add(edge.from);
        result.add(edge.to);
      }
    }
    return result;
  }, [activeNodeId, data.flow.edges, hoveredEdgeId]);
  const focusedDescription = useMemo<FlowFocus | null>(() => {
    if (hoveredEdgeId) {
      const edge = data.flow.edges.find(({ id }) => id === hoveredEdgeId);
      if (edge) {
        return {
          id: edge.id,
          kind: "wire",
          title: edge.label ?? "Circuit connection",
          summary: flowEdgeSummary(edge, nodesById),
        };
      }
    }
    if (activeNodeId) {
      const node = nodesById.get(activeNodeId);
      if (node) {
        return {
          id: node.id,
          kind: "node",
          title: node.title,
          summary: node.summary,
        };
      }
    }
    return null;
  }, [activeNodeId, data.flow.edges, hoveredEdgeId, nodesById]);
  const buttonRefs = useRef(new Map<string, HTMLButtonElement>());

  const moveFocus = (event: ReactKeyboardEvent<HTMLButtonElement>, current: LaidOutNode) => {
    if (!["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown"].includes(event.key)) return;
    event.preventDefault();
    const candidates = laidOut.filter((candidate) => {
      const dx = candidate.x - current.x;
      const dy = candidate.y - current.y;
      if (event.key === "ArrowLeft") return dx < 0;
      if (event.key === "ArrowRight") return dx > 0;
      if (event.key === "ArrowUp") return dy < 0;
      return dy > 0;
    });
    const vertical = event.key === "ArrowUp" || event.key === "ArrowDown";
    candidates.sort((left, right) => {
      const leftPrimary = vertical ? Math.abs(left.y - current.y) : Math.abs(left.x - current.x);
      const leftSecondary = vertical ? Math.abs(left.x - current.x) : Math.abs(left.y - current.y);
      const rightPrimary = vertical ? Math.abs(right.y - current.y) : Math.abs(right.x - current.x);
      const rightSecondary = vertical ? Math.abs(right.x - current.x) : Math.abs(right.y - current.y);
      return leftPrimary + leftSecondary * 0.45 - (rightPrimary + rightSecondary * 0.45);
    });
    const next = candidates[0];
    if (next) buttonRefs.current.get(next.node.id)?.focus();
  };

  return (
    <>
      <div
        className="circuit-flow-canvas"
        role="group"
        aria-label="High-level Orchard circuit signal flow"
      >
        <svg
          className="circuit-flow-canvas__edges"
          viewBox={`0 0 ${width} ${height}`}
          role="group"
          aria-label="Circuit wires"
          preserveAspectRatio="none"
        >
          <defs>
            {(["data", "constraint", "public"] as const).map((kind) => (
              <marker
                id={`circuit-flow-arrow-${kind}`}
                className={`circuit-flow-arrow--${kind}`}
                key={kind}
                viewBox="0 0 10 10"
                refX="9"
                refY="5"
                markerWidth="6"
                markerHeight="6"
                orient="auto-start-reverse"
              >
                <path d="M 0 0 L 10 5 L 0 10 z" />
              </marker>
            ))}
          </defs>
          <g className="circuit-flow-hit-layer" aria-hidden="true">
            {data.flow.edges.map((edge) => {
              const from = byId.get(edge.from);
              const to = byId.get(edge.to);
              if (!from || !to) return null;
              const bend = Math.max(45, Math.abs(to.x - from.x) * 0.42);
              const path = `M ${from.x} ${from.y} C ${from.x + bend} ${from.y}, ${to.x - bend} ${to.y}, ${to.x} ${to.y}`;
              return (
                <path
                  key={edge.id}
                  className="circuit-flow-edge__hit"
                  d={path}
                  onMouseEnter={() => setHoveredEdgeId(edge.id)}
                  onMouseLeave={() => setHoveredEdgeId(null)}
                />
              );
            })}
          </g>
          {data.flow.edges.map((edge) => {
            const from = byId.get(edge.from);
            const to = byId.get(edge.to);
            if (!from || !to) return null;
            const bend = Math.max(45, Math.abs(to.x - from.x) * 0.42);
            const path = `M ${from.x} ${from.y} C ${from.x + bend} ${from.y}, ${to.x - bend} ${to.y}, ${to.x} ${to.y}`;
            const incident = Boolean(activeNodeId) &&
              (edge.from === activeNodeId || edge.to === activeNodeId);
            const emphasized = hoveredEdgeId === edge.id || incident;
            const muted = Boolean(activeNodeId || hoveredEdgeId) && !emphasized;
            const summary = flowEdgeSummary(edge, nodesById);
            return (
              <g
                key={edge.id}
                className={classNames(
                  "circuit-flow-edge",
                  `circuit-flow-edge--${edge.kind}`,
                  emphasized && "is-emphasized",
                  hoveredEdgeId === edge.id && "is-label-hovered",
                  muted && "is-muted",
                )}
                data-edge-id={edge.id}
                onMouseEnter={() => setHoveredEdgeId(edge.id)}
                onMouseLeave={() => setHoveredEdgeId(null)}
              >
                <title>{summary}</title>
                <path
                  d={path}
                  markerEnd={`url(#circuit-flow-arrow-${edge.kind})`}
                />
                {edge.label ? (
                  <text
                    x={(from.x + to.x) / 2}
                    y={(from.y + to.y) / 2 - 7}
                    textAnchor="middle"
                    tabIndex={0}
                    aria-label={`${edge.label}. ${summary}`}
                    aria-describedby="circuit-flow-focus-description"
                    onFocus={() => setHoveredEdgeId(edge.id)}
                    onBlur={() => setHoveredEdgeId(null)}
                  >
                    {edge.label}
                  </text>
                ) : null}
              </g>
            );
          })}
        </svg>
        {laidOut.map((item) => {
          const muted = Boolean(activeNodeId || hoveredEdgeId) && !connectedNodeIds.has(item.node.id);
          const connected = connectedNodeIds.has(item.node.id) && item.node.id !== activeNodeId;
          const style = {
            "--circuit-node-x": `${(item.x / width) * 100}%`,
            "--circuit-node-y": `${(item.y / height) * 100}%`,
          } as CSSProperties;
          return (
            <button
              type="button"
              key={item.node.id}
              ref={(node) => {
                if (node) buttonRefs.current.set(item.node.id, node);
                else buttonRefs.current.delete(item.node.id);
              }}
              className={classNames(
                "circuit-flow-node",
                `circuit-flow-node--${item.node.kind}`,
                selectedId === item.node.id && "is-selected",
                connected && "is-connected",
                muted && "is-muted",
              )}
              style={style}
              aria-current={selectedId === item.node.id ? "true" : undefined}
              aria-label={`${item.node.title}. ${item.node.summary}`}
              aria-describedby="circuit-flow-focus-description"
              onClick={() => onSelect(item.node)}
              onMouseEnter={() => setHoveredNodeId(item.node.id)}
              onMouseLeave={() => setHoveredNodeId(null)}
              onFocus={() => setHoveredNodeId(item.node.id)}
              onBlur={() => setHoveredNodeId(null)}
              onKeyDown={(event) => moveFocus(event, item)}
            >
              <span>{titleCase(item.node.kind)}</span>
              <strong>{item.node.shortTitle}</strong>
            </button>
          );
        })}
      </div>
      <div
        className={classNames("circuit-flow-focus", focusedDescription && "is-active")}
        id="circuit-flow-focus-description"
        data-flow-item={focusedDescription?.id}
      >
        <p>{focusedDescription?.kind === "wire" ? "Circuit wire" : focusedDescription ? "Circuit item" : "Interactive guide"}</p>
        <h3>{focusedDescription?.title ?? "Follow an item through the circuit"}</h3>
        <span>
          {focusedDescription?.summary ??
            "Hover or focus a circuit item or wire name to see its role. Select an item to inspect its regions, gates, and source."}
        </span>
      </div>
      <ol className="circuit-mobile-flow" aria-label="High-level Orchard circuit flow">
        {data.flow.nodes.map((node) => (
          <li key={node.id}>
            <button
              type="button"
              className={`circuit-mobile-flow__node--${node.kind}`}
              onClick={() => onSelect(node)}
              onFocus={() => setHoveredNodeId(node.id)}
              onBlur={() => setHoveredNodeId(null)}
              aria-current={selectedId === node.id ? "true" : undefined}
            >
              <span>{titleCase(node.kind)}</span>
              <strong>{node.title}</strong>
              <small>{node.summary}</small>
            </button>
          </li>
        ))}
      </ol>
      <section className="circuit-mobile-wires" aria-labelledby="circuit-mobile-wires-title">
        <h3 id="circuit-mobile-wires-title">Circuit wires</h3>
        <p>Connections are listed explicitly on small screens, where hover is unavailable.</p>
        <ul>
          {data.flow.edges.map((edge) => {
            const from = nodesById.get(edge.from);
            const to = nodesById.get(edge.to);
            return (
              <li className={`circuit-mobile-wire--${edge.kind}`} key={edge.id}>
                <span>{titleCase(edge.kind)} wire</span>
                <strong>{edge.label || `${from?.shortTitle ?? edge.from} to ${to?.shortTitle ?? edge.to}`}</strong>
                <small>{from?.shortTitle ?? edge.from} → {to?.shortTitle ?? edge.to}</small>
                <p>{flowEdgeSummary(edge, nodesById)}</p>
              </li>
            );
          })}
        </ul>
      </section>
    </>
  );
}

function OperationRecord({ operation }: { operation: CircuitRegionOperation }) {
  return (
    <article className="circuit-operation-record" data-operation-id={operation.id} tabIndex={-1}>
      <p className="circuit-card__kind">{titleCase(operation.kind)}</p>
      <h4>{operation.title}</h4>
      {operation.annotation ? <p>{operation.annotation}</p> : null}
      <dl className="circuit-operation-facts">
        {operation.selectorId ? <><dt>Selector ID</dt><dd><code>{operation.selectorId}</code></dd></> : null}
        {operation.selectorName ? <><dt>Selector name</dt><dd><code>{operation.selectorName}</code></dd></> : null}
        {operation.relativeOffset !== undefined ? <><dt>Relative offset</dt><dd>{operation.relativeOffset}</dd></> : null}
        {operation.absoluteRow !== undefined ? <><dt>Absolute row</dt><dd>{operation.absoluteRow}</dd></> : null}
        {operation.value ? <><dt>Value</dt><dd><code>{operation.value}</code></dd></> : null}
        {operation.regionId ? <><dt>Region</dt><dd><code>{operation.regionId}</code></dd></> : null}
      </dl>
      {operation.cells.length ? (
        <ul className="circuit-operation-cells" aria-label="Referenced cells">
          {operation.cells.map((cell) => (
            <li key={cell.id}>
              <code>{cell.label}</code>
              <span>{titleCase(cell.kind)}</span>
              {cell.column ? <span>column {cell.column}</span> : null}
              {cell.relativeOffset !== undefined ? <span>offset {cell.relativeOffset}</span> : null}
              {cell.absoluteRow !== undefined ? <span>row {cell.absoluteRow}</span> : null}
            </li>
          ))}
        </ul>
      ) : operation.lookupEntries.length ? null : <p>No cell operands are recorded for this operation.</p>}
      {operation.lookupEntries.length ? (
        <div className="circuit-cell-table-wrap">
          <table className="circuit-cell-table">
            <caption>Lookup table columns initialized by this operation</caption>
            <thead>
              <tr><th>Entry</th><th>Column</th><th>Name</th><th>Annotation</th><th>Values</th><th>Default</th></tr>
            </thead>
            <tbody>
              {operation.lookupEntries.map((entry) => (
                <tr key={entry.id}>
                  <th scope="row"><code>{entry.id}</code></th>
                  <td>{entry.column ?? "—"}</td>
                  <td><code>{entry.columnName ?? "—"}</code></td>
                  <td>{entry.annotation ?? "—"}</td>
                  <td>{entry.valueCount ?? "—"}</td>
                  <td><code>{entry.defaultValue ?? "—"}</code></td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      ) : null}
    </article>
  );
}

function ConstraintRecord({ constraint }: { constraint: CircuitConstraint }) {
  return (
    <article className="circuit-constraint-record" data-constraint-id={constraint.id}>
      <p className="circuit-card__kind">Polynomial constraint</p>
      <h3>{constraint.title}</h3>
      <pre><code>{constraint.expression}</code></pre>
      <dl>
        <div>
          <dt>Columns</dt>
          <dd>{constraint.columns.length ? constraint.columns.join(", ") : "Derived from the expression"}</dd>
        </div>
        <div>
          <dt>Rotations</dt>
          <dd>{constraint.rotations.length ? constraint.rotations.join(", ") : "0 / not annotated"}</dd>
        </div>
      </dl>
    </article>
  );
}

function RegionOperationList({
  occurrences,
  operations,
  visibleLimit,
  focusId,
  onShowMore,
}: {
  occurrences: readonly CircuitRegionOccurrence[];
  operations: readonly CircuitRegionOperation[];
  visibleLimit: number;
  focusId: string | null;
  onShowMore: () => void;
}) {
  const operationsByOccurrence = new Map<string, CircuitRegionOperation[]>();
  for (const operation of operations) {
    const occurrenceId = operation.occurrenceId ?? operation.regionId;
    if (!occurrenceId) continue;
    const current = operationsByOccurrence.get(occurrenceId) ?? [];
    current.push(operation);
    operationsByOccurrence.set(occurrenceId, current);
  }
  const focusedOccurrence = focusId
    ? occurrences.find((occurrence) =>
        operationsByOccurrence.get(occurrence.id)?.some((operation) => operation.id === focusId)
      )
    : undefined;
  const [chosenOccurrenceId, setChosenOccurrenceId] = useState(occurrences[0]?.id ?? "");
  const [dismissedFocusId, setDismissedFocusId] = useState<string | null>(null);
  const activeOccurrence = (focusId !== dismissedFocusId ? focusedOccurrence : undefined) ??
    occurrences.find((occurrence) => occurrence.id === chosenOccurrenceId) ??
    occurrences[0];

  useEffect(() => {
    const nextId = (focusId !== dismissedFocusId ? focusedOccurrence?.id : undefined) ?? (
      occurrences.some((occurrence) => occurrence.id === chosenOccurrenceId)
        ? chosenOccurrenceId
        : occurrences[0]?.id ?? ""
    );
    if (nextId !== chosenOccurrenceId) setChosenOccurrenceId(nextId);
  }, [chosenOccurrenceId, dismissedFocusId, focusId, focusedOccurrence?.id, occurrences]);

  const orderedOperations = activeOccurrence
    ? operationsByOccurrence.get(activeOccurrence.id) ?? []
    : [];
  const focusIndex = focusId
    ? orderedOperations.findIndex((operation) => operation.id === focusId)
    : -1;
  const effectiveLimit = Math.max(visibleLimit, focusIndex + 1);
  const visibleOperations = orderedOperations.slice(0, effectiveLimit);
  const total = occurrences.reduce(
    (count, occurrence) => count + (operationsByOccurrence.get(occurrence.id)?.length ?? 0),
    0,
  );
  const emptyOccurrenceCount = occurrences.filter(
    (occurrence) => !(operationsByOccurrence.get(occurrence.id)?.length),
  ).length;

  return (
    <section className="circuit-region-operations" aria-labelledby="region-operations-title">
      <div className="circuit-layer-heading">
        <div>
          <p className="circuit-card__kind">Free-monad synthesis trace</p>
          <h3 id="region-operations-title">Region operations</h3>
          <p>
            These operators are shown directly in evaluator order. Selectors, rows,
            values, and referenced cells come from the extracted Rocq trace.
          </p>
        </div>
        <p>{total} operator{total === 1 ? "" : "s"} across {occurrences.length} exact occurrence{occurrences.length === 1 ? "" : "s"}</p>
      </div>
      {occurrences.length > 1 && total ? (
        <div className="circuit-occurrence-picker">
          <label htmlFor="circuit-occurrence-select">Exact occurrence shown</label>
          <select
            id="circuit-occurrence-select"
            aria-describedby="circuit-occurrence-help"
            value={activeOccurrence?.id ?? ""}
            onChange={(event) => {
              setChosenOccurrenceId(event.currentTarget.value);
              setDismissedFocusId(focusId);
            }}
          >
            {occurrences.map((occurrence) => {
              const count = operationsByOccurrence.get(occurrence.id)?.length ?? 0;
              return (
                <option key={occurrence.id} value={occurrence.id}>
                  #{occurrence.index} · {occurrence.title} · {count} operator{count === 1 ? "" : "s"}
                </option>
              );
            })}
          </select>
          <small id="circuit-occurrence-help">Repeated regions share one definition; choose an exact evaluator occurrence to inspect its ordered operators.</small>
        </div>
      ) : null}
      <div className="circuit-occurrence-list">
        {activeOccurrence && orderedOperations.length ? (
          <section className="circuit-occurrence" key={activeOccurrence.id}>
            <header>
              <div>
                <p className="circuit-card__kind">Exact region {activeOccurrence.index}</p>
                <h3>{activeOccurrence.title}</h3>
              </div>
              <span>{visibleOperations.length} of {orderedOperations.length} operator{orderedOperations.length === 1 ? "" : "s"} shown</span>
            </header>
            {activeOccurrence.namespacePath.length ? (
              <p className="circuit-namespace-path">{activeOccurrence.namespacePath.join(" / ")}</p>
            ) : null}
            <div className="circuit-operation-list">
              {visibleOperations.map((operation) => (
                <OperationRecord key={operation.id} operation={operation} />
              ))}
            </div>
          </section>
        ) : null}
      </div>
      {emptyOccurrenceCount ? (
        <p className="circuit-empty-note">
          {emptyOccurrenceCount} exact occurrence{emptyOccurrenceCount === 1 ? "" : "s"} emitted no operators in the extracted trace.
        </p>
      ) : null}
      {visibleOperations.length < orderedOperations.length ? (
        <button className="circuit-show-more" type="button" onClick={onShowMore}>
          Show all {orderedOperations.length - visibleOperations.length} remaining operations
        </button>
      ) : null}
    </section>
  );
}

function DetailCanvas({
  data,
  entries,
  entry,
  visibleLimit,
  focusId,
  onSelect,
  onShowMore,
}: {
  data: CircuitExplorerData;
  entries: readonly ExplorerEntry[];
  entry: ExplorerEntry | null;
  visibleLimit: number;
  focusId: string | null;
  onSelect: (entry: ExplorerEntry) => void;
  onShowMore: () => void;
}) {
  if (!entry) {
    return (
      <div className="circuit-empty-layer">
        <p className="eyebrow">Region and gate detail</p>
        <h2>Choose a synthesis region or gate</h2>
        <p>Drill through a component to inspect its exact operations, constraints, cells, and source provenance.</p>
      </div>
    );
  }

  if (entry.kind === "region") {
    const region = entry.item as CircuitRegionGroup;
    const occurrences = data.synthesis.occurrences.filter((occurrence) =>
      occurrence.groupId === region.id || region.occurrenceIds.includes(occurrence.id)
    );
    const operations = data.synthesis.operations.filter((operation) =>
      occurrences.some((occurrence) =>
        operation.occurrenceId === occurrence.id ||
        operation.regionId === occurrence.id ||
        occurrence.operationIds.includes(operation.id)
      )
    );
    return (
      <div>
        <div className="circuit-layer-heading">
          <div>
            <p className="circuit-card__kind">Synthesis region</p>
            <h2>{region.title}</h2>
            <p>{region.summary}</p>
          </div>
          <p>{occurrences.length} exact occurrence{occurrences.length === 1 ? "" : "s"}</p>
        </div>
        {region.semanticId ? <code>{region.semanticId}</code> : null}
        <MetricGrid metrics={metricsWithFallback(entry)} />
        <RegionOperationList
          occurrences={occurrences}
          operations={operations}
          visibleLimit={visibleLimit}
          focusId={focusId}
          onShowMore={onShowMore}
        />
      </div>
    );
  }

  if (entry.kind === "region-occurrence" && "operationIds" in entry.item) {
    const occurrence = entry.item as CircuitRegionOccurrence;
    const operations = data.synthesis.operations.filter((operation) =>
      operation.occurrenceId === occurrence.id ||
      operation.regionId === occurrence.id ||
      occurrence.operationIds.includes(operation.id)
    );
    return (
      <div>
        <div className="circuit-layer-heading">
          <div><p className="circuit-card__kind">Exact region</p><h2>{occurrence.title}</h2></div>
          <p>{operations.length} operation{operations.length === 1 ? "" : "s"}</p>
        </div>
        {occurrence.namespacePath.length ? <p className="circuit-namespace-path">{occurrence.namespacePath.join(" / ")}</p> : null}
        <MetricGrid metrics={metricsWithFallback(entry)} />
        <RegionOperationList
          occurrences={[occurrence]}
          operations={operations}
          visibleLimit={visibleLimit}
          focusId={focusId}
          onShowMore={onShowMore}
        />
      </div>
    );
  }

  if (entry.kind === "gate") {
    const gate = entry.item as CircuitGate;
    const constraints = data.configure.constraints.filter((constraint) =>
      constraint.gateId === gate.id || gate.constraintIds.includes(constraint.id)
    );
    return (
      <div>
        <div className="circuit-layer-heading">
          <div>
            <p className="circuit-card__kind">Gate</p>
            <h2>{gate.title}</h2>
            <p>{gate.summary}</p>
            {gate.selector ? <p>Enabled by <code>{gate.selector}</code></p> : null}
          </div>
          <p>{constraints.length} constraint{constraints.length === 1 ? "" : "s"}</p>
        </div>
        <MetricGrid metrics={metricsWithFallback(entry)} />
        <div className="circuit-direct-explanation">
          In Halo2, every gate is declared during circuit configuration. The extracted configure free monad defines the following polynomial constraints for this gate.
        </div>
        <div className="circuit-constraint-list">
          {constraints.map((constraint) => (
            <ConstraintRecord key={constraint.id} constraint={constraint} />
          ))}
        </div>
        <RelationshipLinks label="components" ids={gate.componentIds} entries={entries} origin="component" onSelect={onSelect} />
        <RelationshipLinks label="synthesis regions" ids={gate.regionIds} entries={entries} origin="detail" kind="region-occurrence" onSelect={onSelect} />
      </div>
    );
  }

  if (entry.kind === "lookup") {
    const lookup = entry.item as CircuitLookup;
    return (
      <article className="circuit-detail-summary">
        <p className="circuit-card__kind">Lookup argument</p>
        <h2>{lookup.title}</h2>
        <p>{lookup.summary}</p>
        <MetricGrid metrics={metricsWithFallback(entry)} />
        {lookup.selectorIds.length ? <p>Selectors: <code>{lookup.selectorIds.join(", ")}</code></p> : null}
        {lookup.tableIds.length ? <p>Tables: <code>{lookup.tableIds.join(", ")}</code></p> : null}
        <RelationshipLinks label="components" ids={lookup.componentIds} entries={entries} origin="component" onSelect={onSelect} />
        <RelationshipLinks label="synthesis regions" ids={lookup.regionIds} entries={entries} origin="detail" kind="region-occurrence" onSelect={onSelect} />
        {lookup.pairs.length ? (
          <div className="circuit-cell-table-wrap">
            <table className="circuit-cell-table">
              <caption>Lookup input and table pairs</caption>
              <thead><tr><th>Pair</th><th>Input expression</th><th>Table</th></tr></thead>
              <tbody>
                {lookup.pairs.map((pair, index) => (
                  <tr key={pair.id}>
                    <th scope="row">{index + 1}</th>
                    <td><code>{pair.inputExpression}</code></td>
                    <td>
                      <code>{pair.tableName ?? "Table"}{pair.tableId ? ` (${pair.tableId})` : ""}</code>
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        ) : null}
      </article>
    );
  }

  return <EntryCard entry={entry} onSelect={onSelect} />;
}

function sourceForIds(data: CircuitExplorerData, ids: readonly string[]): CircuitSource[] {
  const byId = new Map(data.sources.map((source) => [source.id, source]));
  return ids.flatMap((id) => {
    const source = byId.get(id);
    return source ? [source] : [];
  });
}

function CircuitInspector({
  data,
  entry,
}: {
  data: CircuitExplorerData;
  entry: ExplorerEntry | null;
}) {
  if (!entry) {
    return (
      <aside className="circuit-inspector" aria-label="Circuit item details" aria-live="polite">
        <div className="circuit-inspector__empty">
          <p className="eyebrow">Circuit inspector</p>
          <h2>Choose a circuit item</h2>
          <p>Select a signal, component, region, gate, lookup, or exact operation to inspect its role and provenance.</p>
        </div>
      </aside>
    );
  }

  const sources = sourceForIds(data, entry.sourceIds);
  const sourcesById = new Map(data.sources.map((source) => [source.id, source]));
  const diagnostics = data.diagnostics.filter(({ itemId, itemIds }) =>
    itemId === entry.id || itemIds.includes(entry.id)
  );
  const metrics = metricsWithFallback(entry);

  return (
    <aside className="circuit-inspector" aria-label="Circuit item details" aria-live="polite">
      <div className="circuit-inspector__content" data-item-id={entry.id}>
        <p className="circuit-inspector__eyebrow">{titleCase(entry.kind)}</p>
        <h2>{entry.title}</h2>
        <p className="circuit-inspector__summary">{entry.summary}</p>
        {entry.namespacePath.length ? (
          <p className="circuit-namespace-path"><span>Namespace</span>{entry.namespacePath.join(" / ")}</p>
        ) : null}
        <MetricGrid metrics={metrics} />

        {entry.sourceConfidence ? (
          <p className="circuit-source-confidence">
            Source mapping confidence:{" "}
            <span className={`circuit-confidence circuit-confidence--${entry.sourceConfidence}`}>
              {titleCase(entry.sourceConfidence)}
            </span>
          </p>
        ) : null}

        <section className="circuit-source-panel">
          <h3>Source provenance</h3>
          {sources.length ? (
            <ul>
              {sources.map((source) => (
                <li key={source.id}>
                  <div>
                    <strong>{source.label}</strong>
                    <span className={`circuit-confidence circuit-confidence--${source.confidence}`}>
                      {titleCase(source.confidence)}
                    </span>
                  </div>
                  {source.url ? (
                    <a href={source.url} target="_blank" rel="noopener noreferrer">
                      <code>{source.path}{source.symbol ? ` :: ${source.symbol}` : ""}{source.line ? `:${source.line}` : ""}</code>
                      <span aria-hidden="true"> ↗</span>
                    </a>
                  ) : (
                    <code>{source.path}{source.symbol ? ` :: ${source.symbol}` : ""}{source.line ? `:${source.line}` : ""}</code>
                  )}
                  {source.candidates.length ? (
                    <div className="circuit-source-candidates">
                      <h4>{source.candidates.length} source candidate{source.candidates.length === 1 ? "" : "s"}</h4>
                      <ul>
                        {source.candidates.map((candidate, index) => (
                          <li key={`${candidate.path}:${candidate.symbol}:${index}`}>
                            <strong>{candidate.label}</strong>
                            <code>{candidate.path}{candidate.symbol ? ` :: ${candidate.symbol}` : ""}</code>
                            {candidate.confidence ? <small>{candidate.confidence}</small> : null}
                          </li>
                        ))}
                      </ul>
                    </div>
                  ) : null}
                </li>
              ))}
            </ul>
          ) : (
            <p>No primary source anchor is assigned to this item. Candidate mappings remain explicit below.</p>
          )}
          {entry.sourceCandidates.length ? (
            <div className="circuit-source-candidates">
              <h4>
                {entry.sourceCandidates.length} mapping candidate{entry.sourceCandidates.length === 1 ? "" : "s"}
              </h4>
              <ul>
                {entry.sourceCandidates.map((candidate, index) => {
                  const source = sourcesById.get(candidate.sourceId);
                  const sourceLabel = source
                    ? `${source.path}${source.symbol ? ` :: ${source.symbol}` : ""}${source.line ? `:${source.line}` : ""}`
                    : candidate.sourceId;
                  return (
                    <li key={`${entry.id}:${candidate.sourceId}:${candidate.confidence}:${index}`}>
                      <strong>{source?.label ?? candidate.sourceId}</strong>
                      <span className={`circuit-confidence circuit-confidence--${candidate.confidence}`}>
                        {titleCase(candidate.confidence)}
                      </span>
                      {source?.url ? (
                        <a href={source.url} target="_blank" rel="noopener noreferrer">
                          <code>{sourceLabel}</code><span aria-hidden="true"> ↗</span>
                        </a>
                      ) : <code>{sourceLabel}</code>}
                      {candidate.reason ? <small>{candidate.reason}</small> : null}
                    </li>
                  );
                })}
              </ul>
            </div>
          ) : null}
        </section>

        {entry.proofNodeIds.length ? (
          <section className="circuit-atlas-links">
            <h3>Verification Atlas</h3>
            <ul>
              {entry.proofNodeIds.map((nodeId) => (
                <li key={nodeId}>
                  <a href={`./proof-map.html#node=${encodeURIComponent(nodeId)}`}>
                    Open {proofNodeTitle(nodeId)} in the Atlas <span aria-hidden="true">→</span>
                  </a>
                </li>
              ))}
            </ul>
          </section>
        ) : null}

        {diagnostics.length ? (
          <section className="circuit-diagnostics">
            <h3>Data diagnostics</h3>
            <ul>
              {diagnostics.map((diagnostic) => (
                <li className={`circuit-diagnostic--${diagnostic.severity}`} key={diagnostic.id}>
                  {diagnostic.message}
                </li>
              ))}
            </ul>
          </section>
        ) : null}
      </div>
    </aside>
  );
}

function CircuitSectionHeading({
  eyebrow,
  id,
  title,
  description,
  children,
}: {
  eyebrow: string;
  id?: string;
  title: string;
  description: string;
  children?: ReactNode;
}) {
  return (
    <header className="circuit-section-heading">
      <div>
        <p className="eyebrow">{eyebrow}</p>
        <h2 id={id}>{title}</h2>
        <p>{description}</p>
      </div>
      {children}
    </header>
  );
}

function CircuitOutline({
  data,
  entries,
  onSelect,
}: {
  data: CircuitExplorerData;
  entries: readonly ExplorerEntry[];
  onSelect: (entry: ExplorerEntry) => void;
}) {
  return (
    <section className="circuit-outline-alternative" aria-labelledby="circuit-outline-title">
      <CircuitSectionHeading
        eyebrow="Component index"
        id="circuit-outline-title"
        title="Explore the circuit by component"
        description="Each card is a functional part of the Orchard Action circuit. Within each card, the list contains aggregated synthesis-region names; the occurrence count tells you how many exact regions the Rocq evaluator emitted."
      />
      <div>
        {data.synthesis.components.map((component) => {
          const componentEntry = entries.find((entry) =>
            entry.origin === "component" && entry.id === component.id
          );
          const regions = data.synthesis.regions.filter((region) =>
            region.componentId === component.id || component.regionIds.includes(region.id)
          );
          return (
            <section key={component.id}>
              <p className="circuit-card__kind">Functional component</p>
              <h3>{component.title}</h3>
              <p>{component.summary}</p>
              {componentEntry ? (
                <button type="button" onClick={() => onSelect(componentEntry)}>
                  Explore {component.shortTitle}
                </button>
              ) : null}
              <p className="circuit-outline-alternative__list-label">
                Synthesis region groups ({regions.length})
              </p>
              {regions.length ? (
                <ul>
                  {regions.map((region) => (
                    <li key={region.id}>
                      <button type="button" onClick={() => {
                        const entry = entries.find((candidate) => candidate.item === region);
                        if (entry) onSelect(entry);
                      }}>
                        {region.title} · {region.count} occurrence{region.count === 1 ? "" : "s"}
                      </button>
                    </li>
                  ))}
                </ul>
              ) : <p>No named synthesis regions are assigned to this component.</p>}
            </section>
          );
        })}
      </div>
    </section>
  );
}

function EmbeddedGadgets({
  data,
  entries,
  onSelect,
}: {
  data: CircuitExplorerData;
  entries: readonly ExplorerEntry[];
  onSelect: (entry: ExplorerEntry) => void;
}) {
  const sourcesById = new Map(data.sources.map((source) => [source.id, source]));
  const families = [
    {
      id: "poseidon",
      title: "Poseidon",
      matcher: "/poseidon/",
      detail: "Poseidon is nested in nullifier derivation: its full-round, partial-round, and pad-and-add gates implement the hash before the ECC-based nullifier step.",
    },
    {
      id: "ecc",
      title: "Elliptic-curve gadgets",
      matcher: "/ecc/",
      detail: "ECC point checks, additions, and variable- and fixed-base multiplication are shared across commitments, authority randomization, address integrity, nullifier derivation, and note construction.",
    },
  ] as const;

  return (
    <section className="circuit-helper-section" aria-labelledby="circuit-helper-title">
      <CircuitSectionHeading
        eyebrow="Shared gadgets"
        id="circuit-helper-title"
        title="Where Poseidon and ECC live"
        description="They are not missing. This flow is grouped by Orchard function, while reusable Poseidon, ECC, Sinsemilla, and range-check gadgets are nested inside the components that call them."
      />
      <div className="circuit-helper-grid">
        {families.map((family) => {
          const gates = data.configure.gates.filter((gate) =>
            gate.sourceIds.some((sourceId) =>
              sourcesById.get(sourceId)?.path.toLocaleLowerCase().includes(family.matcher)
            )
          );
          const componentIds = [...new Set(gates.flatMap((gate) =>
            [gate.componentId, ...gate.componentIds].filter((id): id is string => Boolean(id))
          ))];
          const components = componentIds.flatMap((id) => {
            const component = data.synthesis.components.find((candidate) => candidate.id === id);
            const entry = entries.find((candidate) =>
              candidate.origin === "component" && candidate.id === id
            );
            return component && entry ? [{ component, entry }] : [];
          });
          return (
            <article key={family.id} className={`circuit-helper-card circuit-helper-card--${family.id}`}>
              <p className="circuit-card__kind">Integrated helper family</p>
              <h3>{family.title}</h3>
              <p>{family.detail}</p>
              <p className="circuit-helper-card__metric">
                <strong>{gates.length}</strong> extracted gate{gates.length === 1 ? "" : "s"} across <strong>{components.length}</strong> component{components.length === 1 ? "" : "s"}
              </p>
              <div className="circuit-helper-card__components" aria-label={`${family.title} components`}>
                {components.map(({ component, entry }) => (
                  <button type="button" key={component.id} onClick={() => onSelect(entry)}>
                    {component.shortTitle}
                  </button>
                ))}
              </div>
            </article>
          );
        })}
      </div>
    </section>
  );
}

function CircuitSnapshot({ data }: { data: CircuitExplorerData }) {
  return (
    <section className="circuit-snapshot-note" aria-labelledby="circuit-snapshot-title">
      <div className="circuit-snapshot-note__intro">
        <p className="eyebrow">Generated Rocq snapshot</p>
        <h2 id="circuit-snapshot-title">{data.metadata.title}</h2>
        <p>{data.metadata.description}</p>
      </div>
      <dl className="circuit-snapshot-facts">
        {data.metadata.version ? <div><dt>Version</dt><dd><code>{data.metadata.version}</code></dd></div> : null}
        {data.metadata.field ? <div><dt>Field</dt><dd><code>{data.metadata.field}</code></dd></div> : null}
        {data.metadata.k !== undefined ? <div><dt>k</dt><dd>{data.metadata.k}</dd></div> : null}
        {data.metadata.floorPlanner ? <div><dt>Floor planner</dt><dd>{data.metadata.floorPlanner}</dd></div> : null}
        {data.metadata.witnessValues ? <div><dt>Witness values</dt><dd>{titleCase(data.metadata.witnessValues)}</dd></div> : null}
      </dl>
      {data.metadata.placement ? <p className="circuit-snapshot-note__placement">{data.metadata.placement}</p> : null}
      {Object.keys(data.metadata.repositoryRefs).length ? (
        <div className="circuit-snapshot-note__revisions">
          <h3>Pinned sources</h3>
          <dl>
            {Object.entries(data.metadata.repositoryRefs).map(([repository, revision]) => (
              <div key={repository}><dt>{titleCase(repository)}</dt><dd><code>{revision.slice(0, 12)}</code></dd></div>
            ))}
          </dl>
        </div>
      ) : null}
    </section>
  );
}

function LoadingExplorer() {
  return (
    <main id="main-content" className="circuit-page" tabIndex={-1} aria-busy="true">
      <section className="circuit-intro">
        <p className="eyebrow">Loading the pinned Rocq evidence snapshot</p>
        <h1>Orchard Circuit Explorer</h1>
        <p>The generated snapshot is fetched separately, keeping exact region and gate details outside the application’s initial JavaScript bundle.</p>
      </section>
      <div className="circuit-loading" role="status">
        <span aria-hidden="true" />
        Loading circuit structure…
      </div>
    </main>
  );
}

function ExplorerError({ message, onRetry }: { message: string; onRetry: () => void }) {
  return (
    <main id="main-content" className="circuit-page" tabIndex={-1}>
      <section className="circuit-intro">
        <p className="eyebrow">Pinned evidence unavailable</p>
        <h1>Orchard Circuit Explorer</h1>
      </section>
      <div className="circuit-load-error" role="alert">
        <h2>The circuit data could not be opened</h2>
        <p>{message}</p>
        <button type="button" onClick={onRetry}>Retry loading the circuit</button>
      </div>
    </main>
  );
}

export function CircuitExplorer({ loader = loadCircuitExplorerData }: { loader?: DataLoader }) {
  const [data, setData] = useState<CircuitExplorerData | null>(null);
  const [loadError, setLoadError] = useState<string | null>(null);
  const [attempt, setAttempt] = useState(0);
  const [route, setRoute] = useState<CircuitExplorerRoute>(defaultRoute);
  const [notice, setNotice] = useState("");
  const [searchOpen, setSearchOpen] = useState(false);
  const [visibleLimit, setVisibleLimit] = useState(EXACT_PAGE_SIZE);
  const searchRef = useRef<HTMLInputElement>(null);
  const layerRef = useRef<HTMLDivElement>(null);
  const focusedRouteRef = useRef(`${route.level}:${route.itemId ?? ""}:${route.focusId ?? ""}`);

  useEffect(() => {
    let active = true;
    setLoadError(null);
    loader().then(
      (loaded) => {
        if (active) setData(loaded);
      },
      (error: unknown) => {
        if (active) setLoadError(error instanceof Error ? error.message : "Unknown data-loading error");
      },
    );
    return () => { active = false; };
  }, [attempt, loader]);

  const entries = useMemo(() => data ? buildEntries(data) : [], [data]);

  useEffect(() => {
    if (!data) return undefined;
    const syncFromHash = () => {
      const parsed = parseRoute(data, entries);
      setRoute(parsed.route);
      setNotice(parsed.notice ?? "");
      setVisibleLimit(EXACT_PAGE_SIZE);
      if (parsed.notice || parsed.replace) {
        window.history.replaceState(null, "", routeHash(parsed.route) || window.location.pathname);
      }
    };
    syncFromHash();
    window.addEventListener("hashchange", syncFromHash);
    return () => window.removeEventListener("hashchange", syncFromHash);
  }, [data, entries]);

  useEffect(() => {
    const routeKey = `${route.level}:${route.itemId ?? ""}:${route.focusId ?? ""}`;
    if (focusedRouteRef.current === routeKey) return;
    focusedRouteRef.current = routeKey;
    const layer = layerRef.current;
    if (!layer) return;
    const focusedItem = route.focusId
      ? [...layer.querySelectorAll<HTMLElement>("[data-operation-id], [data-constraint-id]")]
          .find((candidate) =>
            candidate.dataset.operationId === route.focusId ||
            candidate.dataset.constraintId === route.focusId
          )
      : null;
    const target = focusedItem ?? layer.querySelector<HTMLElement>(
      '.circuit-flow-node[aria-current="true"], h2, h3',
    );
    if (target && !target.hasAttribute("tabindex")) target.tabIndex = -1;
    (target ?? layer).focus();
  }, [route.level, route.itemId, route.focusId]);

  const navigate = useCallback((next: CircuitExplorerRoute, replace = false) => {
    const hash = routeHash(next);
    const url = `${window.location.pathname}${window.location.search}${hash}`;
    window.history[replace ? "replaceState" : "pushState"](null, "", url);
    setRoute(next);
    setNotice("");
    setVisibleLimit(EXACT_PAGE_SIZE);
  }, []);

  if (loadError) {
    return (
      <ExplorerError
        message={loadError}
        onRetry={() => {
          clearCircuitExplorerDataCache();
          setData(null);
          setAttempt((current) => current + 1);
        }}
      />
    );
  }
  if (!data) return <LoadingExplorer />;

  const selectedEntry = findSelectedEntry(entries, route);
  const selectedComponent = route.level === "component"
    ? data.synthesis.components.find(({ id }) => id === route.itemId) ?? null
    : selectedEntry?.componentId
      ? data.synthesis.components.find(({ id }) => id === selectedEntry.componentId) ?? null
      : null;
  const normalizedQuery = route.query.trim().toLocaleLowerCase();
  const searchResults = normalizedQuery
    ? entries.filter((entry) => entry.searchText.includes(normalizedQuery)).slice(0, 12)
    : [];

  const selectEntry = (entry: ExplorerEntry) => {
    setSearchOpen(false);
    const presented = presentationEntryFor(data, entries, entry);
    const focusId = presented !== entry && (entry.kind === "operation" || entry.kind === "constraint")
      ? entry.id
      : null;
    if (presented.origin === "component") {
      navigate({ ...route, level: "component", itemId: presented.id, query: "", focusId });
    } else if (presented.origin === "flow") {
      if (presented.componentId) {
        navigate({ ...route, level: "component", itemId: presented.componentId, query: "", focusId: null });
      } else {
        navigate({ ...route, level: "flow", itemId: presented.id, query: "", focusId: null });
      }
    } else {
      navigate({ ...route, level: "detail", itemId: presented.id, query: "", focusId });
    }
    if (presented !== entry) setNotice(entryRedirectNotice(entry, presented));
  };

  const selectFlowNode = (node: CircuitFlowNode) => {
    const entry = entries.find((candidate) => candidate.origin === "flow" && candidate.id === node.id);
    if (entry) selectEntry(entry);
  };

  const componentRegions = selectedComponent
    ? data.synthesis.regions.filter((region) =>
        region.componentId === selectedComponent.id || selectedComponent.regionIds.includes(region.id)
      )
    : [];
  const componentGates = selectedComponent
    ? data.configure.gates.filter((gate) =>
        gate.componentId === selectedComponent.id ||
        gate.componentIds.includes(selectedComponent.id) ||
        selectedComponent.gateIds.includes(gate.id)
      )
    : [];
  const componentLookups = selectedComponent
    ? data.configure.lookups.filter((lookup) =>
        lookup.componentId === selectedComponent.id ||
        lookup.componentIds.includes(selectedComponent.id) ||
        selectedComponent.lookupIds.includes(lookup.id)
      )
    : [];
  const componentOperations = selectedComponent
    ? data.synthesis.operations.filter((operation) =>
        selectedComponent.operationIds.includes(operation.id) ||
        (operation.componentId === selectedComponent.id && !operation.regionId)
      )
    : [];
  const componentCanvasEntries = [
    ...componentRegions.map((item) => entries.find((entry) => entry.item === item)),
    ...componentGates.map((item) => entries.find((entry) => entry.item === item)),
    ...componentLookups.map((item) => entries.find((entry) => entry.item === item)),
  ].filter((entry): entry is ExplorerEntry => Boolean(entry));
  const filteredComponentEntries = normalizedQuery
    ? componentCanvasEntries.filter(({ searchText }) => searchText.includes(normalizedQuery))
    : componentCanvasEntries;

  return (
    <main id="main-content" className="circuit-page" tabIndex={-1}>
      <section className="circuit-intro" aria-labelledby="circuit-title">
        <div>
          <p className="eyebrow">Rocq model · configure · synthesis · source</p>
          <h1 id="circuit-title">Orchard Circuit Explorer</h1>
          <p>
            Follow the high-level Action circuit, then drill into its semantic
            regions, exact layouter operations, gates, lookups, and pinned source provenance.
          </p>
          <p className="circuit-trust-note">
            {data.metadata.representations.flow ??
              "The functional flow is curated navigation; it is not inferred proof evidence."}
          </p>
        </div>
        <MetricGrid metrics={data.metadata.metrics.slice(0, 6)} />
      </section>

      <section className="circuit-toolbar" aria-label="Circuit explorer controls">
        <div className="circuit-search">
          <label htmlFor="circuit-search">Search circuit structure</label>
          <input
            ref={searchRef}
            id="circuit-search"
            type="search"
            value={route.query}
            placeholder="Output, component, region, gate, cell…"
            autoComplete="off"
            aria-controls={searchOpen && normalizedQuery ? "circuit-search-results" : undefined}
            onFocus={() => setSearchOpen(true)}
            onChange={(event) => {
              const query = event.currentTarget.value;
              setSearchOpen(true);
              navigate({ ...route, query }, true);
            }}
            onKeyDown={(event) => {
              if (event.key === "Escape") {
                setSearchOpen(false);
                if (route.query) navigate({ ...route, query: "" }, true);
              }
            }}
          />
          <p className="circuit-search__count" aria-live="polite">
            {normalizedQuery ? `${searchResults.length} matching items suggested` : "Search across every explorer layer"}
          </p>
          {searchOpen && normalizedQuery ? (
            <div className="circuit-search-results" id="circuit-search-results">
              {searchResults.length ? (
                <ul>
                  {searchResults.map((entry) => (
                    <li key={entry.key}>
                      <button
                        type="button"
                        onMouseDown={(event) => event.preventDefault()}
                        onClick={() => selectEntry(entry)}
                      >
                        <span>{titleCase(entry.kind)}</span>
                        <strong>{entry.title}</strong>
                        <small>{entry.summary}</small>
                      </button>
                    </li>
                  ))}
                </ul>
              ) : <p>No circuit items match “{route.query}”.</p>}
            </div>
          ) : null}
        </div>

      </section>

      <nav className="circuit-breadcrumbs" aria-label="Circuit explorer depth">
        <button
          type="button"
          aria-current={route.level === "flow" ? "page" : undefined}
          onClick={() => navigate({ ...route, level: "flow", itemId: null, focusId: null })}
        >
          Circuit flow
        </button>
        <span aria-hidden="true">/</span>
        {selectedComponent ? (
          <button
            type="button"
            aria-current={route.level === "component" ? "page" : undefined}
            onClick={() => navigate({ ...route, level: "component", itemId: selectedComponent.id, focusId: null })}
          >
            {selectedComponent.shortTitle}
          </button>
        ) : <span>Component</span>}
        <span aria-hidden="true">/</span>
        <span aria-current={route.level === "detail" ? "page" : undefined}>
          {route.level === "detail" && selectedEntry ? selectedEntry.title : "Region or gate"}
        </span>
      </nav>

      {notice ? <p className="circuit-route-notice" role="status">{notice}</p> : null}
      <p className="visually-hidden" aria-live="polite">
        {route.level === "flow"
          ? "Showing the high-level circuit flow."
          : route.level === "component"
            ? `Showing ${selectedComponent?.title ?? "a circuit component"}.`
            : `Showing ${selectedEntry?.title ?? "circuit detail"}.`}
      </p>

      <section className={classNames("circuit-workspace", route.level === "flow" && "circuit-workspace--flow")}>
        <div
          ref={layerRef}
          className={`circuit-canvas circuit-canvas--${route.level}`}
          role="region"
          tabIndex={-1}
          aria-label={`${titleCase(route.level)} circuit layer`}
        >
          {route.level === "flow" ? (
            <div className="circuit-flow-view">
              <CircuitSectionHeading
                eyebrow="High-level Action flow"
                id="circuit-flow-title"
                title="Choose a circuit item"
                description="Start with the functional circuit map. Hover or focus nodes and wire names for an explanation, then select a node to inspect the extracted regions, gates, and source anchors behind it."
              >
                <div className="circuit-flow-legends">
                  <ul className="circuit-flow-legend" aria-label="Circuit item types">
                    <li className="circuit-flow-legend--input">Input</li>
                    <li className="circuit-flow-legend--component">Component</li>
                    <li className="circuit-flow-legend--check">Check</li>
                    <li className="circuit-flow-legend--output">Public output</li>
                  </ul>
                  <ul className="circuit-wire-legend" aria-label="Circuit wire types">
                    <li className="circuit-wire-legend--data">Data</li>
                    <li className="circuit-wire-legend--constraint">Constraint</li>
                    <li className="circuit-wire-legend--public">Public value</li>
                  </ul>
                </div>
              </CircuitSectionHeading>
              <FlowCanvas data={data} selectedId={route.itemId} onSelect={selectFlowNode} />
            </div>
          ) : route.level === "component" ? (
            selectedComponent ? (
              <div>
                <div className="circuit-layer-heading">
                  <div>
                    <p className="circuit-card__kind">Circuit component</p>
                    <h2 tabIndex={-1}>{selectedComponent.title}</h2>
                    <p>{selectedComponent.detail || selectedComponent.summary}</p>
                  </div>
                  <p>{filteredComponentEntries.length} item{filteredComponentEntries.length === 1 ? "" : "s"}</p>
                </div>
                <MetricGrid metrics={selectedComponent.metrics} />
                <div className="circuit-card-grid">
                  {filteredComponentEntries.slice(0, visibleLimit).map((entry) => (
                    <EntryCard key={entry.key} entry={entry} onSelect={selectEntry} />
                  ))}
                </div>
                {!filteredComponentEntries.length ? (
                  <div className="circuit-empty-note">
                    <p>No region, gate, or lookup records match this component and search.</p>
                    {route.query ? <button type="button" onClick={() => navigate({ ...route, query: "" }, true)}>Clear search</button> : null}
                  </div>
                ) : null}
                {filteredComponentEntries.length > visibleLimit ? (
                  <button className="circuit-show-more" type="button" onClick={() => setVisibleLimit((current) => current + EXACT_PAGE_SIZE)}>
                    Show more circuit items
                  </button>
                ) : null}
                {componentOperations.length ? (
                  <section className="circuit-component-operations">
                    <div className="circuit-layer-heading">
                      <div>
                        <p className="circuit-card__kind">Component-level synthesis trace</p>
                        <h3>Operations linked at component level</h3>
                        <p>These extracted operators either belong directly to the component or bind one of its results to a public instance row.</p>
                      </div>
                      <p>{componentOperations.length} operation{componentOperations.length === 1 ? "" : "s"}</p>
                    </div>
                    <div className="circuit-operation-list">
                      {componentOperations.slice(0, visibleLimit).map((operation) => (
                        <OperationRecord key={operation.id} operation={operation} />
                      ))}
                    </div>
                    {componentOperations.length > visibleLimit ? (
                      <button className="circuit-show-more" type="button" onClick={() => setVisibleLimit((current) => current + EXACT_PAGE_SIZE)}>
                        Show more operations
                      </button>
                    ) : null}
                  </section>
                ) : null}
              </div>
            ) : (
              <div className="circuit-empty-layer"><h2>Choose a circuit component</h2></div>
            )
          ) : (
            <DetailCanvas
              data={data}
              entries={entries}
              entry={selectedEntry}
              visibleLimit={visibleLimit}
              focusId={route.focusId}
              onSelect={selectEntry}
              onShowMore={() => setVisibleLimit(Number.MAX_SAFE_INTEGER)}
            />
          )}
        </div>
        {route.level !== "flow" ? <CircuitInspector data={data} entry={selectedEntry} /> : null}
      </section>

      {route.level === "flow" ? (
        <>
          <CircuitOutline data={data} entries={entries} onSelect={selectEntry} />
          <EmbeddedGadgets data={data} entries={entries} onSelect={selectEntry} />
          <CircuitSnapshot data={data} />
        </>
      ) : null}
    </main>
  );
}
