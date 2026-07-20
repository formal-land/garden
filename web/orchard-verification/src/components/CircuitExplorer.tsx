import {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
  type CSSProperties,
  type KeyboardEvent as ReactKeyboardEvent,
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
  CircuitExplorerMode,
  CircuitExplorerRoute,
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

function defaultRoute(): CircuitExplorerRoute {
  return { level: "flow", itemId: null, mode: "aggregate", query: "" };
}

function routeHash(route: CircuitExplorerRoute): string {
  const parameters = new URLSearchParams();
  if (route.level !== "flow") parameters.set("level", route.level);
  if (route.itemId) parameters.set("item", route.itemId);
  if (route.mode === "exact") parameters.set("mode", "exact");
  if (route.query) parameters.set("q", route.query);
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
      proofNodeIds: [],
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
      proofNodeIds: [],
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
      proofNodeIds: [],
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
      proofNodeIds: [],
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
      proofNodeIds: [],
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
      proofNodeIds: [],
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

function parseRoute(
  data: CircuitExplorerData,
  entries: readonly ExplorerEntry[],
): { route: CircuitExplorerRoute; notice?: string } {
  const parameters = new URLSearchParams(window.location.hash.slice(1));
  const requestedLevel = parameters.get("level");
  const level: CircuitExplorerLevel =
    requestedLevel === "component" || requestedLevel === "detail"
      ? requestedLevel
      : "flow";
  const mode: CircuitExplorerMode = parameters.get("mode") === "exact" ? "exact" : "aggregate";
  const query = parameters.get("q") ?? "";
  const requestedItem = parameters.get("item");
  const candidate: CircuitExplorerRoute = {
    level,
    itemId: requestedItem,
    mode,
    query,
  };

  if (!requestedItem && level === "flow") return { route: candidate };
  const found = findSelectedEntry(entries, candidate);
  if (found) return { route: candidate };

  if (level === "component" && !requestedItem && data.synthesis.components[0]) {
    return {
      route: { ...candidate, itemId: data.synthesis.components[0].id },
      notice: "The component link was incomplete, so the first circuit component is shown.",
    };
  }
  return {
    route: { ...defaultRoute(), mode, query },
    notice: requestedItem
      ? `The linked circuit item “${requestedItem}” is not present in this evidence snapshot.`
      : "The linked circuit view was incomplete, so the circuit overview is shown.",
  };
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

function upstreamNodeIds(data: CircuitExplorerData, selectedId: string | null): Set<string> {
  if (!selectedId) return new Set();
  const result = new Set([selectedId]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const edge of data.flow.edges) {
      if (result.has(edge.to) && !result.has(edge.from)) {
        result.add(edge.from);
        changed = true;
      }
    }
  }
  return result;
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
  if (!ids.length) return null;
  return (
    <details className="circuit-relationship-links">
      <summary>{ids.length} linked {label}</summary>
      <ul>
        {ids.map((id) => {
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
    </details>
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
  const highlighted = useMemo(
    () => upstreamNodeIds(data, selectedId),
    [data, selectedId],
  );
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
          aria-hidden="true"
          preserveAspectRatio="none"
        >
          <defs>
            <marker id="circuit-flow-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
              <path d="M 0 0 L 10 5 L 0 10 z" />
            </marker>
          </defs>
          {data.flow.edges.map((edge) => {
            const from = byId.get(edge.from);
            const to = byId.get(edge.to);
            if (!from || !to) return null;
            const active = !selectedId || (highlighted.has(edge.from) && highlighted.has(edge.to));
            const bend = Math.max(45, Math.abs(to.x - from.x) * 0.42);
            return (
              <g
                key={edge.id}
                className={`circuit-flow-edge circuit-flow-edge--${edge.kind} ${active ? "is-active" : "is-muted"}`}
              >
                <path
                  d={`M ${from.x} ${from.y} C ${from.x + bend} ${from.y}, ${to.x - bend} ${to.y}, ${to.x} ${to.y}`}
                  markerEnd="url(#circuit-flow-arrow)"
                />
                {edge.label ? (
                  <text x={(from.x + to.x) / 2} y={(from.y + to.y) / 2 - 7} textAnchor="middle">
                    {edge.label}
                  </text>
                ) : null}
              </g>
            );
          })}
        </svg>
        {laidOut.map((item) => {
          const muted = selectedId && !highlighted.has(item.node.id);
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
                muted && "is-muted",
              )}
              style={style}
              aria-pressed={selectedId === item.node.id}
              aria-label={`${item.node.title}. ${item.node.summary}`}
              onClick={() => onSelect(item.node)}
              onKeyDown={(event) => moveFocus(event, item)}
            >
              <span>{titleCase(item.node.kind)}</span>
              <strong>{item.node.shortTitle}</strong>
            </button>
          );
        })}
      </div>
      <ol className="circuit-mobile-flow" aria-label="High-level Orchard circuit flow">
        {data.flow.nodes.map((node) => (
          <li key={node.id}>
            <button type="button" onClick={() => onSelect(node)} aria-pressed={selectedId === node.id}>
              <span>{titleCase(node.kind)}</span>
              <strong>{node.title}</strong>
              <small>{node.summary}</small>
            </button>
          </li>
        ))}
      </ol>
    </>
  );
}

function OperationDetail({ operation }: { operation: CircuitRegionOperation }) {
  return (
    <article className="circuit-operation-detail">
      <p className="circuit-card__kind">{titleCase(operation.kind)}</p>
      <h2>{operation.title}</h2>
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
        <div className="circuit-cell-table-wrap">
          <table className="circuit-cell-table">
            <caption>Cells referenced by this operation</caption>
            <thead><tr><th>Cell</th><th>Kind</th><th>Column</th><th>Offset</th><th>Absolute row</th></tr></thead>
            <tbody>
              {operation.cells.map((cell) => (
                <tr key={cell.id}>
                  <th scope="row"><code>{cell.id}</code></th>
                  <td>{titleCase(cell.kind)}</td>
                  <td>{cell.column ?? "—"}</td>
                  <td>{cell.relativeOffset ?? "—"}</td>
                  <td>{cell.absoluteRow ?? "—"}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
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

function DetailCanvas({
  data,
  entries,
  entry,
  mode,
  visibleLimit,
  onSelect,
  onShowMore,
}: {
  data: CircuitExplorerData;
  entries: readonly ExplorerEntry[];
  entry: ExplorerEntry | null;
  mode: CircuitExplorerMode;
  visibleLimit: number;
  onSelect: (entry: ExplorerEntry) => void;
  onShowMore: () => void;
}) {
  if (!entry) {
    return (
      <div className="circuit-empty-layer">
        <p className="eyebrow">Region and gate detail</p>
        <h2>Choose a synthesis region or configured gate</h2>
        <p>Drill through a component to inspect its exact operations, constraints, cells, and source provenance.</p>
      </div>
    );
  }

  if (entry.item && "kind" in entry.item && "cells" in entry.item) {
    return <OperationDetail operation={entry.item as CircuitRegionOperation} />;
  }

  if (entry.kind === "region") {
    const region = entry.item as CircuitRegionGroup;
    const occurrences = data.synthesis.occurrences.filter((occurrence) =>
      occurrence.groupId === region.id || region.occurrenceIds.includes(occurrence.id)
    );
    if (mode === "aggregate") {
      return (
        <article className="circuit-detail-summary">
          <p className="circuit-card__kind">Aggregated region</p>
          <h2>{region.title}</h2>
          <p>{region.summary}</p>
          {region.semanticId ? <code>{region.semanticId}</code> : null}
          <MetricGrid metrics={metricsWithFallback(entry)} />
          <p>Switch to <strong>Exact</strong> to inspect the {region.count} concrete occurrence{region.count === 1 ? "" : "s"} and their operations.</p>
        </article>
      );
    }
    const visible = occurrences.slice(0, visibleLimit);
    return (
      <div>
        <div className="circuit-layer-heading">
          <div><p className="circuit-card__kind">Exact occurrences</p><h2>{region.title}</h2></div>
          <p>{visible.length} of {occurrences.length} shown</p>
        </div>
        <div className="circuit-card-grid">
          {visible.map((occurrence) => {
            const occurrenceEntry = entries.find((candidate) =>
              candidate.origin === "detail" && candidate.id === occurrence.id
            );
            return occurrenceEntry ? <EntryCard key={occurrence.id} entry={occurrenceEntry} onSelect={onSelect} /> : null;
          })}
        </div>
        {visible.length < occurrences.length ? (
          <button className="circuit-show-more" type="button" onClick={onShowMore}>
            Show {Math.min(EXACT_PAGE_SIZE, occurrences.length - visible.length)} more occurrences
          </button>
        ) : null}
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
        <div className="circuit-operation-list">
          {operations.length ? operations.slice(0, visibleLimit).map((operation) => {
            const operationEntry = entries.find((candidate) => candidate.item === operation);
            return (
              <button type="button" key={operation.id} onClick={() => operationEntry && onSelect(operationEntry)}>
                <span>{titleCase(operation.kind)}</span>
                <strong>{operation.title}</strong>
                <small>
                  {operation.annotation ?? operation.selectorName ?? operation.selectorId ?? operation.value ??
                    (operation.lookupEntries.length
                      ? `${operation.lookupEntries.length} lookup table columns`
                      : operation.absoluteRow !== undefined
                        ? `absolute row ${operation.absoluteRow}`
                        : "")}
                </small>
              </button>
            );
          }) : <p className="circuit-empty-note">No region operations were emitted for this occurrence.</p>}
        </div>
        {operations.length > visibleLimit ? (
          <button className="circuit-show-more" type="button" onClick={onShowMore}>Show more operations</button>
        ) : null}
      </div>
    );
  }

  if (entry.kind === "gate") {
    const gate = entry.item as CircuitGate;
    const constraints = data.configure.constraints.filter((constraint) =>
      constraint.gateId === gate.id || gate.constraintIds.includes(constraint.id)
    );
    if (mode === "aggregate") {
      return (
        <article className="circuit-detail-summary">
          <p className="circuit-card__kind">Configured gate</p>
          <h2>{gate.title}</h2>
          <p>{gate.summary}</p>
          {gate.selector ? <p>Enabled by <code>{gate.selector}</code></p> : null}
          <MetricGrid metrics={metricsWithFallback(entry)} />
          <RelationshipLinks label="components" ids={gate.componentIds} entries={entries} origin="component" onSelect={onSelect} />
          <RelationshipLinks label="synthesis regions" ids={gate.regionIds} entries={entries} origin="detail" kind="region-occurrence" onSelect={onSelect} />
          <p>Switch to <strong>Exact</strong> to expand every named polynomial constraint.</p>
        </article>
      );
    }
    return (
      <div>
        <div className="circuit-layer-heading">
          <div><p className="circuit-card__kind">Exact constraints</p><h2>{gate.title}</h2></div>
          <p>{constraints.length} constraint{constraints.length === 1 ? "" : "s"}</p>
        </div>
        <div className="circuit-constraint-list">
          {constraints.map((constraint) => {
            const constraintEntry = entries.find((candidate) => candidate.item === constraint);
            return (
              <button type="button" key={constraint.id} onClick={() => constraintEntry && onSelect(constraintEntry)}>
                <strong>{constraint.title}</strong>
                <code>{constraint.expression}</code>
              </button>
            );
          })}
        </div>
        <RelationshipLinks label="components" ids={gate.componentIds} entries={entries} origin="component" onSelect={onSelect} />
        <RelationshipLinks label="synthesis regions" ids={gate.regionIds} entries={entries} origin="detail" kind="region-occurrence" onSelect={onSelect} />
      </div>
    );
  }

  if (entry.kind === "constraint") {
    const constraint = entry.item as CircuitConstraint;
    return (
      <article className="circuit-constraint-detail">
        <p className="circuit-card__kind">Polynomial constraint</p>
        <h2>{constraint.title}</h2>
        <pre><code>{constraint.expression}</code></pre>
        <dl>
          <div><dt>Gate</dt><dd><code>{constraint.gateId}</code></dd></div>
          <div><dt>Columns</dt><dd>{constraint.columns.length ? constraint.columns.join(", ") : "Derived from the expression AST"}</dd></div>
          <div><dt>Rotations</dt><dd>{constraint.rotations.length ? constraint.rotations.join(", ") : "0 / not annotated"}</dd></div>
        </dl>
      </article>
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
                    <details>
                      <summary>{source.candidates.length} source candidate{source.candidates.length === 1 ? "" : "s"}</summary>
                      <ul>
                        {source.candidates.map((candidate, index) => (
                          <li key={`${candidate.path}:${candidate.symbol}:${index}`}>
                            <strong>{candidate.label}</strong>
                            <code>{candidate.path}{candidate.symbol ? ` :: ${candidate.symbol}` : ""}</code>
                            {candidate.confidence ? <small>{candidate.confidence}</small> : null}
                          </li>
                        ))}
                      </ul>
                    </details>
                  ) : null}
                </li>
              ))}
            </ul>
          ) : (
            <p>No primary source anchor is assigned to this item. Candidate mappings remain explicit below.</p>
          )}
          {entry.sourceCandidates.length ? (
            <details>
              <summary>
                {entry.sourceCandidates.length} mapping candidate{entry.sourceCandidates.length === 1 ? "" : "s"}
              </summary>
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
            </details>
          ) : null}
        </section>

        {entry.proofNodeIds.length ? (
          <section className="circuit-atlas-links">
            <h3>Verification Atlas</h3>
            <ul>
              {entry.proofNodeIds.map((nodeId) => (
                <li key={nodeId}>
                  <a href={`./proof-map.html#node=${encodeURIComponent(nodeId)}`}>
                    Open {nodeId} in the Atlas <span aria-hidden="true">→</span>
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
  const focusedRouteRef = useRef(`${route.level}:${route.itemId ?? ""}:${route.mode}`);

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
      if (parsed.notice) {
        window.history.replaceState(null, "", routeHash(parsed.route) || window.location.pathname);
      }
    };
    syncFromHash();
    window.addEventListener("hashchange", syncFromHash);
    return () => window.removeEventListener("hashchange", syncFromHash);
  }, [data, entries]);

  useEffect(() => {
    const routeKey = `${route.level}:${route.itemId ?? ""}:${route.mode}`;
    if (focusedRouteRef.current === routeKey) return;
    focusedRouteRef.current = routeKey;
    const layer = layerRef.current;
    if (!layer) return;
    const target = layer.querySelector<HTMLElement>(
      '.circuit-flow-node[aria-pressed="true"], h2, h3',
    );
    if (target && !target.hasAttribute("tabindex")) target.tabIndex = -1;
    (target ?? layer).focus();
  }, [route.level, route.itemId, route.mode]);

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
    if (entry.origin === "component") {
      navigate({ ...route, level: "component", itemId: entry.id, query: "" });
    } else if (entry.origin === "flow") {
      if (entry.componentId) {
        navigate({ ...route, level: "component", itemId: entry.componentId, query: "" });
      } else {
        navigate({ ...route, level: "flow", itemId: entry.id, query: "" });
      }
    } else {
      navigate({ ...route, level: "detail", itemId: entry.id, query: "" });
    }
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
  const componentOccurrences = selectedComponent
    ? data.synthesis.occurrences.filter((occurrence) =>
        occurrence.componentId === selectedComponent.id ||
        componentRegions.some((region) =>
          occurrence.groupId === region.id || region.occurrenceIds.includes(occurrence.id)
        )
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
  const componentCanvasEntries = route.mode === "aggregate"
    ? [
        ...componentRegions.map((item) => entries.find((entry) => entry.item === item)),
        ...componentGates.map((item) => entries.find((entry) => entry.item === item)),
        ...componentLookups.map((item) => entries.find((entry) => entry.item === item)),
        ...componentOperations.map((item) => entries.find((entry) => entry.item === item)),
      ].filter((entry): entry is ExplorerEntry => Boolean(entry))
    : [
        ...(componentOccurrences.length ? componentOccurrences : componentRegions)
          .map((item) => entries.find((entry) => entry.item === item)),
        ...componentGates.map((item) => entries.find((entry) => entry.item === item)),
        ...componentLookups.map((item) => entries.find((entry) => entry.item === item)),
        ...componentOperations.map((item) => entries.find((entry) => entry.item === item)),
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

        <fieldset className="circuit-mode-toggle">
          <legend>Region detail</legend>
          <button
            type="button"
            aria-pressed={route.mode === "aggregate"}
            aria-label="Aggregate repeated regions"
            onClick={() => navigate({ ...route, mode: "aggregate" })}
          >
            Aggregate
            <small>Group repeats</small>
          </button>
          <button
            type="button"
            aria-pressed={route.mode === "exact"}
            aria-label="Show exact concrete regions"
            onClick={() => navigate({ ...route, mode: "exact" })}
          >
            Exact
            <small>Concrete regions</small>
          </button>
        </fieldset>
      </section>

      <nav className="circuit-breadcrumbs" aria-label="Circuit explorer depth">
        <button
          type="button"
          aria-current={route.level === "flow" ? "page" : undefined}
          onClick={() => navigate({ ...route, level: "flow", itemId: null })}
        >
          Circuit flow
        </button>
        <span aria-hidden="true">/</span>
        {selectedComponent ? (
          <button
            type="button"
            aria-current={route.level === "component" ? "page" : undefined}
            onClick={() => navigate({ ...route, level: "component", itemId: selectedComponent.id })}
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
            ? `Showing ${selectedComponent?.title ?? "a circuit component"} in ${route.mode} mode.`
            : `Showing ${selectedEntry?.title ?? "circuit detail"}.`}
      </p>

      <section className="circuit-workspace">
        <div
          ref={layerRef}
          className={`circuit-canvas circuit-canvas--${route.level}`}
          role="region"
          tabIndex={-1}
          aria-label={`${titleCase(route.level)} circuit layer`}
        >
          {route.level === "flow" ? (
            <FlowCanvas data={data} selectedId={route.itemId} onSelect={selectFlowNode} />
          ) : route.level === "component" ? (
            selectedComponent ? (
              <div>
                <div className="circuit-layer-heading">
                  <div>
                    <p className="circuit-card__kind">Circuit component · {titleCase(route.mode)}</p>
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
                    <p>No {route.mode} region or gate records match this component and search.</p>
                    {route.query ? <button type="button" onClick={() => navigate({ ...route, query: "" }, true)}>Clear search</button> : null}
                  </div>
                ) : null}
                {filteredComponentEntries.length > visibleLimit ? (
                  <button className="circuit-show-more" type="button" onClick={() => setVisibleLimit((current) => current + EXACT_PAGE_SIZE)}>
                    Show more exact items
                  </button>
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
              mode={route.mode}
              visibleLimit={visibleLimit}
              onSelect={selectEntry}
              onShowMore={() => setVisibleLimit((current) => current + EXACT_PAGE_SIZE)}
            />
          )}
        </div>
        <CircuitInspector data={data} entry={selectedEntry} />
      </section>

      <details className="circuit-outline-alternative">
        <summary>Browse the circuit as an outline</summary>
        <div>
          {data.synthesis.components.map((component) => (
            <section key={component.id}>
              <h2>{component.title}</h2>
              <p>{component.summary}</p>
              <button
                type="button"
                onClick={() => selectEntry(entries.find((entry) => entry.origin === "component" && entry.id === component.id)!)}
              >
                Explore {component.shortTitle}
              </button>
              <ul>
                {data.synthesis.regions
                  .filter((region) => region.componentId === component.id || component.regionIds.includes(region.id))
                  .map((region) => (
                    <li key={region.id}>
                      <button type="button" onClick={() => {
                        const entry = entries.find((candidate) => candidate.item === region);
                        if (entry) selectEntry(entry);
                      }}>
                        {region.title} · {region.count} occurrence{region.count === 1 ? "" : "s"}
                      </button>
                    </li>
                  ))}
              </ul>
            </section>
          ))}
        </div>
      </details>

      <section className="circuit-snapshot-note" aria-label="Circuit data snapshot">
        <p>
          <strong>{data.metadata.title}</strong>
          {data.metadata.asOf ? ` · ${data.metadata.asOf}` : ""}
        </p>
        <p>{data.metadata.description}</p>
        {data.metadata.placement ? <p>{data.metadata.placement}</p> : null}
        {Object.keys(data.metadata.repositoryRefs).length ? (
          <dl>
            {Object.entries(data.metadata.repositoryRefs).map(([repository, revision]) => (
              <div key={repository}><dt>{titleCase(repository)}</dt><dd><code>{revision.slice(0, 12)}</code></dd></div>
            ))}
          </dl>
        ) : null}
      </section>
    </main>
  );
}
