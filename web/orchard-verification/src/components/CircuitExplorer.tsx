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
import { type DataLoader, useLoadableData } from "../hooks/useLoadableData";
import { useMediaQuery } from "../hooks/useMediaQuery";
import type {
  CircuitCell,
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
  CircuitSourceCandidate,
  CircuitSourceConfidence,
  CircuitSourceResolutionCandidate,
  InspectableCircuitItem,
} from "../circuit/model";
import {
  circuitExplorerRouteHash as routeHash,
  defaultCircuitExplorerRoute as defaultRoute,
} from "../circuit/routing";

const EXACT_PAGE_SIZE = 60;
const RELATIONSHIP_PREVIEW_SIZE = 8;

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

function sourceLocation(path: string, line?: number): string {
  const filename = path.split(/[\\/]/).filter(Boolean).at(-1) ?? path;
  return `${filename}${line ? `:${line}` : ""}`;
}

function fullSourceLocation(path: string, line?: number): string {
  return `${path}${line ? `:${line}` : ""}`;
}

function middleEllipsis(value: string, maximumLength = 38): string {
  if (value.length <= maximumLength) return value;
  const visibleLength = maximumLength - 1;
  const leadingLength = Math.ceil(visibleLength / 2);
  const trailingLength = Math.floor(visibleLength / 2);
  return `${value.slice(0, leadingLength)}…${value.slice(-trailingLength)}`;
}

function symbolParts(value: string): { module?: string; symbol: string } {
  const separator = value.includes("::") ? "::" : ".";
  const parts = value.split(separator).filter(Boolean);
  if (parts.length < 2) return { symbol: value };
  return {
    module: parts.slice(0, -1).join(separator),
    symbol: parts.at(-1) ?? value,
  };
}

function atlasActionLabel(id: string): string {
  const labels: Readonly<Record<string, string>> = {
    "capture-synthesis-model": "Open synthesis model",
    "gadgets-poseidon-range": "Open range-check proofs",
    "gadgets-ecc": "Open ECC proofs",
    "gadgets-sinsemilla-merkle": "Open Merkle proofs",
    "action-valid-inputs": "Open input proofs",
    "action-seven-outputs": "Open output proofs",
    "action-theorem": "Open Action theorem",
  };
  return labels[id] ?? "Open in Atlas";
}

function metricDescription(label: string): string | undefined {
  const descriptions: Readonly<Record<string, string>> = {
    Gates: "Configured polynomial gates",
    Constraints: "Polynomial equations across all gates",
    Lookups: "Configured lookup arguments",
    "Exact regions": "Concrete synthesis-region executions",
    Operations: "Recorded layouter operations",
    Namespaces: "Nested synthesis scopes",
  };
  return descriptions[label];
}

function formatMetricValue(value: string): string {
  return /^\d{4,}$/.test(value)
    ? Number(value).toLocaleString("en-US")
    : value;
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

function CanonicalValue({
  value,
  maximumLength = 38,
}: {
  value: string;
  maximumLength?: number;
}) {
  return (
    <code className="circuit-canonical-value" title={value} aria-label={value}>
      {middleEllipsis(value, maximumLength)}
    </code>
  );
}

function CopyCanonicalButton({
  value,
  label,
}: {
  value: string;
  label: string;
}) {
  const [status, setStatus] = useState<"idle" | "copied" | "failed">("idle");

  useEffect(() => setStatus("idle"), [value]);

  const copy = async () => {
    try {
      if (!navigator.clipboard?.writeText) throw new Error("Clipboard unavailable");
      await navigator.clipboard.writeText(value);
      setStatus("copied");
    } catch {
      setStatus("failed");
    }
  };

  const buttonLabel = status === "copied"
    ? `Copied full ${label}`
    : status === "failed"
      ? `Could not copy full ${label}`
      : `Copy full ${label}`;

  return (
    <button
      type="button"
      className="circuit-copy-canonical"
      title={buttonLabel}
      aria-label={buttonLabel}
      onClick={copy}
    >
      {status === "copied" ? "Copied" : status === "failed" ? "Copy failed" : "Copy"}
    </button>
  );
}

function MetricGrid({
  metrics,
  compact = false,
}: {
  metrics: readonly CircuitMetric[];
  compact?: boolean;
}) {
  if (!metrics.length) return null;
  return (
    <dl className={classNames("circuit-metrics", compact && "circuit-metrics--strip")}>
      {metrics.map((metric) => (
        <div key={metric.id}>
          <dt>{metric.label}</dt>
          <dd>{formatMetricValue(metric.value)}</dd>
          {!compact && (metric.detail || metricDescription(metric.label)) ? (
            <dd>{metric.detail ?? metricDescription(metric.label)}</dd>
          ) : null}
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

  const relationshipItems = ids.reduce<Array<{
    key: string;
    canonicalId: string;
    count: number;
    target?: ExplorerEntry;
    title: string;
  }>>((items, id) => {
    const target = entries.find((candidate) =>
      candidate.id === id && candidate.origin === origin && (!kind || candidate.kind === kind)
    );
    if (kind !== "region-occurrence" || !target) {
      items.push({
        key: id,
        canonicalId: id,
        count: 1,
        target,
        title: target?.title ?? id,
      });
      return items;
    }

    const occurrence = target.item as CircuitRegionOccurrence;
    const groupId = occurrence.groupId || target.title;
    const existing = items.find(({ key }) => key === groupId);
    if (existing) {
      existing.count += 1;
      return items;
    }
    const groupedTarget = entries.find((candidate) =>
      candidate.origin === "detail" && candidate.kind === "region" && candidate.id === occurrence.groupId
    );
    items.push({
      key: groupId,
      canonicalId: occurrence.groupId || id,
      count: 1,
      target: groupedTarget ?? target,
      title: groupedTarget?.title ?? target.title,
    });
    return items;
  }, []);
  const visibleItems = expanded
    ? relationshipItems
    : relationshipItems.slice(0, RELATIONSHIP_PREVIEW_SIZE);
  const modifier = kind === "region-occurrence" ? "regions" : label;
  return (
    <section className={`circuit-relationship-links circuit-relationship-links--${modifier.replace(/\s+/g, "-")}`}>
      <h3>{ids.length} linked {label}</h3>
      <ul>
        {visibleItems.map(({ canonicalId, count, key, target, title }) => (
          <li key={key}>
            {target ? (
              <button
                type="button"
                title={`Open ${title} · ${canonicalId}`}
                aria-label={`Open ${title}; canonical identifier ${canonicalId}`}
                onClick={() => onSelect(target)}
              >
                <span className="circuit-relationship-links__identity">
                  <strong>{title}</strong>
                  <CanonicalValue value={canonicalId} maximumLength={46} />
                </span>
                <span className="circuit-relationship-links__affordance">
                  {count > 1 ? `${count} exact regions` : null}
                  <span aria-hidden="true">›</span>
                </span>
              </button>
            ) : <CanonicalValue value={canonicalId} maximumLength={46} />}
          </li>
        ))}
      </ul>
      {!expanded && relationshipItems.length > visibleItems.length ? (
        <button
          className="circuit-relationship-links__more"
          type="button"
          onClick={() => setExpanded(true)}
        >
          View {relationshipItems.length - visibleItems.length} more
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
      title={`${entry.title} · ${entry.id}`}
      onClick={() => onSelect(entry)}
    >
      <span className="circuit-card__kind">{titleCase(entry.kind)}</span>
      <strong title={entry.title}>{entry.title}</strong>
      <span title={entry.summary}>{entry.summary}</span>
      {entry.namespacePath.length ? (
        <CanonicalValue value={entry.namespacePath.join(" / ")} maximumLength={54} />
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
      {focusedDescription ? (
        <div
          className="circuit-flow-focus is-active"
          id="circuit-flow-focus-description"
          data-flow-item={focusedDescription.id}
          role="status"
        >
          <p>{focusedDescription.kind === "wire" ? "Circuit wire" : "Circuit item"}</p>
          <h3>{focusedDescription.title}</h3>
          <span>{focusedDescription.summary}</span>
        </div>
      ) : null}
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

function cellsIdentifySamePhysicalCell(
  source: CircuitCell,
  destination: CircuitCell,
): boolean {
  if (source.id && destination.id && source.id === destination.id) return true;
  if (
    source.kind !== destination.kind ||
    !source.column ||
    source.column !== destination.column
  ) {
    return false;
  }
  if (
    source.absoluteRow !== undefined &&
    destination.absoluteRow !== undefined
  ) {
    return source.absoluteRow === destination.absoluteRow;
  }
  return Boolean(
    source.regionId &&
    source.regionId === destination.regionId &&
    source.relativeOffset !== undefined &&
    source.relativeOffset === destination.relativeOffset,
  );
}

export function CircuitOperationRecord({
  operation,
}: {
  readonly operation: CircuitRegionOperation;
}) {
  const selfCopy = operation.kind === "copy" &&
    operation.cells.length >= 2 &&
    cellsIdentifySamePhysicalCell(operation.cells[0], operation.cells[1]);
  return (
    <article className="circuit-operation-record" data-operation-id={operation.id} tabIndex={-1}>
      <p className="circuit-card__kind">{titleCase(operation.kind)}</p>
      <h4>{selfCopy ? "Self-copy" : operation.title}</h4>
      {operation.annotation ? <p>{operation.annotation}</p> : null}
      {selfCopy ? (
        <p className="circuit-operation-self-copy" role="note">
          Source and destination identify the same physical cell, so this copy
          is a permutation no-op. Both exact endpoint records are retained below.
        </p>
      ) : null}
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
      <header className="circuit-constraint-record__header">
        <p className="circuit-card__kind">Constraint</p>
        <h3>{constraint.title}</h3>
      </header>
      <pre tabIndex={0} aria-label={`Formula for ${constraint.title}`}>
        <code>{constraint.expression}</code>
      </pre>
      <dl className="circuit-constraint-meta" aria-label="Constraint references">
        <div>
          <dt>Columns</dt>
          <dd>
            <code title={constraint.columns.join(", ") || "Derived from the expression"}>
              {constraint.columns.length ? constraint.columns.join(", ") : "Derived from expression"}
            </code>
          </dd>
        </div>
        <div>
          <dt>Rotations</dt>
          <dd>
            <code title={constraint.rotations.join(", ") || "0 / not annotated"}>
              {constraint.rotations.length ? constraint.rotations.join(", ") : "0 / not annotated"}
            </code>
          </dd>
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
                <CircuitOperationRecord key={operation.id} operation={operation} />
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
        <header className="circuit-entity-heading">
          <h2>{gate.title}</h2>
          <ul className="circuit-entity-meta" aria-label="Selected gate summary">
            <li>Gate</li>
            {gate.selector ? (
              <li>
                Selector <CanonicalValue value={gate.selector} maximumLength={24} />
              </li>
            ) : null}
            <li>{constraints.length} constraint{constraints.length === 1 ? "" : "s"}</li>
            {entry.sourceConfidence ? (
              <li>{titleCase(entry.sourceConfidence)} source mapping</li>
            ) : null}
          </ul>
          {gate.summary ? <p>{gate.summary}</p> : null}
        </header>
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

function SourceFileLink({
  path,
  line,
  url,
}: Pick<CircuitSource, "path" | "line" | "url">) {
  const visibleLocation = sourceLocation(path, line);
  const completeLocation = fullSourceLocation(path, line);
  if (!url) {
    return <CanonicalValue value={completeLocation} maximumLength={34} />;
  }
  return (
    <a
      href={url}
      target="_blank"
      rel="noopener noreferrer"
      title={`Open ${completeLocation}`}
      aria-label={visibleLocation}
    >
      <code>{visibleLocation}</code>
      <span aria-hidden="true"> ↗</span>
    </a>
  );
}

function SourceCandidateRecord({ candidate }: { candidate: CircuitSourceCandidate }) {
  const canonicalSymbol = candidate.symbol ?? candidate.label;
  const { module, symbol } = symbolParts(canonicalSymbol);
  const completeLocation = fullSourceLocation(candidate.path, candidate.line);
  return (
    <li className="circuit-source-candidate-record">
      <div className="circuit-source-candidate-record__heading">
        <strong>Source candidate</strong>
        {candidate.confidence ? <small>{candidate.confidence}</small> : null}
      </div>
      <dl className="circuit-source-fields">
        <div>
          <dt>Symbol</dt>
          <dd>
            <CanonicalValue value={symbol} maximumLength={26} />
            <CopyCanonicalButton value={canonicalSymbol} label="candidate symbol" />
          </dd>
        </div>
        {module ? (
          <div>
            <dt>Module</dt>
            <dd><CanonicalValue value={module} maximumLength={30} /></dd>
          </div>
        ) : null}
        <div>
          <dt>File</dt>
          <dd>
            <CanonicalValue value={completeLocation} maximumLength={30} />
            <CopyCanonicalButton value={completeLocation} label="candidate file path" />
          </dd>
        </div>
      </dl>
    </li>
  );
}

function SourceProvenanceRecord({ source }: { source: CircuitSource }) {
  const canonicalSymbol = source.symbol ?? source.label;
  const { module, symbol } = symbolParts(canonicalSymbol);
  const completeLocation = fullSourceLocation(source.path, source.line);
  return (
    <li className="circuit-source-record">
      <div className="circuit-source-record__heading">
        <strong>{source.repository ? `${titleCase(source.repository)} source` : "Source"}</strong>
        <span className={`circuit-confidence circuit-confidence--${source.confidence}`}>
          {titleCase(source.confidence)}
        </span>
      </div>
      <dl className="circuit-source-fields">
        <div>
          <dt>Symbol</dt>
          <dd>
            <CanonicalValue value={symbol} maximumLength={28} />
            <CopyCanonicalButton value={canonicalSymbol} label="canonical symbol" />
          </dd>
        </div>
        {module ? (
          <div>
            <dt>Module</dt>
            <dd><CanonicalValue value={module} maximumLength={34} /></dd>
          </div>
        ) : null}
        <div>
          <dt>File</dt>
          <dd>
            <SourceFileLink path={source.path} line={source.line} url={source.url} />
            <CopyCanonicalButton value={completeLocation} label="source file path" />
          </dd>
        </div>
        {source.revision ? (
          <div>
            <dt>Revision</dt>
            <dd>
              <CanonicalValue value={source.revision} maximumLength={14} />
              <CopyCanonicalButton value={source.revision} label="source revision" />
            </dd>
          </div>
        ) : null}
        <div>
          <dt>Mapping</dt>
          <dd>{titleCase(source.confidence)}</dd>
        </div>
      </dl>
      {source.candidates.length ? (
        <div className="circuit-source-candidates">
          <h4>{source.candidates.length} source candidate{source.candidates.length === 1 ? "" : "s"}</h4>
          <ul>
            {source.candidates.map((candidate, index) => (
              <SourceCandidateRecord
                key={`${candidate.path}:${candidate.symbol}:${index}`}
                candidate={candidate}
              />
            ))}
          </ul>
        </div>
      ) : null}
    </li>
  );
}

function CircuitInspector({
  data,
  entry,
  mobileHidden = false,
  onMobileClose,
}: {
  data: CircuitExplorerData;
  entry: ExplorerEntry | null;
  mobileHidden?: boolean;
  onMobileClose?: () => void;
}) {
  if (!entry) {
    return (
      <aside
        className="circuit-inspector"
        id="circuit-inspector"
        aria-label="Circuit item details"
        aria-live="polite"
        hidden={mobileHidden}
        tabIndex={-1}
      >
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

  return (
    <aside
      className="circuit-inspector"
      id="circuit-inspector"
      aria-label="Circuit item details"
      aria-live="polite"
      hidden={mobileHidden}
      tabIndex={-1}
    >
      <div className="circuit-inspector__content" data-item-id={entry.id}>
        <header className="circuit-inspector__heading">
          <div>
            <p className="circuit-inspector__eyebrow">{titleCase(entry.kind)} evidence</p>
            <h2>Evidence and provenance</h2>
          </div>
          {onMobileClose ? (
            <button
              className="circuit-inspector__mobile-close"
              type="button"
              onClick={onMobileClose}
              aria-label="Close evidence and provenance"
            >
              <span aria-hidden="true">×</span>
              Close
            </button>
          ) : null}
        </header>
        <dl className="circuit-inspector__facts">
          <div>
            <dt>Selected item</dt>
            <dd>
              <CanonicalValue value={entry.id} maximumLength={34} />
              <CopyCanonicalButton value={entry.id} label="item identifier" />
            </dd>
          </div>
          {entry.namespacePath.length ? (
            <div>
              <dt>Namespace</dt>
              <dd>
                <CanonicalValue value={entry.namespacePath.join(" / ")} maximumLength={34} />
              </dd>
            </div>
          ) : null}
          {entry.sourceConfidence ? (
            <div>
              <dt>Source mapping</dt>
              <dd>
                <span className={`circuit-confidence circuit-confidence--${entry.sourceConfidence}`}>
                  {titleCase(entry.sourceConfidence)}
                </span>
              </dd>
            </div>
          ) : null}
        </dl>

        <section className="circuit-source-panel">
          <h3>Source provenance</h3>
          {sources.length ? (
            <ul>
              {sources.map((source) => (
                <SourceProvenanceRecord key={source.id} source={source} />
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
                    ? sourceLocation(source.path, source.line)
                    : candidate.sourceId;
                  return (
                    <li
                      className="circuit-source-mapping-candidate"
                      key={`${entry.id}:${candidate.sourceId}:${candidate.confidence}:${index}`}
                    >
                      <div>
                        <strong
                          title={source?.label ?? candidate.sourceId}
                          aria-label={source?.label ?? candidate.sourceId}
                        >
                          {source?.repository ? `${titleCase(source.repository)} source` : source?.label ?? candidate.sourceId}
                        </strong>
                        <span className={`circuit-confidence circuit-confidence--${candidate.confidence}`}>
                          {titleCase(candidate.confidence)}
                        </span>
                      </div>
                      {source ? (
                        <span className="circuit-source-mapping-candidate__location">
                          <SourceFileLink path={source.path} line={source.line} url={source.url} />
                          <CopyCanonicalButton
                            value={fullSourceLocation(source.path, source.line)}
                            label="candidate source file path"
                          />
                        </span>
                      ) : <CanonicalValue value={sourceLabel} maximumLength={34} />}
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
                  <a
                    href={`./proof-map.html#node=${encodeURIComponent(nodeId)}`}
                    aria-label={`${atlasActionLabel(nodeId)}; Atlas: ${proofNodeTitle(nodeId)}`}
                  >
                    <strong>{atlasActionLabel(nodeId)}</strong>
                    <span>Atlas · {proofNodeTitle(nodeId)}</span>
                    <span aria-hidden="true">→</span>
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
        description="Browse functional components and their grouped synthesis regions. Each occurrence count reports how many exact regions the Rocq evaluator emitted."
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
      matchers: ["/poseidon/"],
      detail: "Poseidon is nested in nullifier derivation: its full-round, partial-round, and pad-and-add gates implement the hash before the ECC-based nullifier step.",
    },
    {
      id: "ecc",
      title: "Elliptic-curve gadgets",
      matchers: ["/ecc/"],
      detail: "ECC point checks, additions, and variable- and fixed-base multiplication are shared across commitments, authority randomization, address integrity, nullifier derivation, and note construction.",
    },
    {
      id: "sinsemilla",
      title: "Sinsemilla and Merkle",
      matchers: ["/sinsemilla/", "/merkle/"],
      detail: "Sinsemilla hashing and its Merkle-path helpers support note-commitment and commitment-tree checks, including the short-commit and conditional-swap work nested inside those components.",
    },
    {
      id: "range-check",
      title: "Range checks",
      matchers: ["range_check", "range-check"],
      detail: "Lookup-based range checks constrain compact values and decomposed limbs throughout the circuit, including the short range-check paths reused by higher-level Orchard components.",
    },
  ] as const;

  return (
    <section className="circuit-helper-section" aria-labelledby="circuit-helper-title">
      <CircuitSectionHeading
        eyebrow="Shared gadgets"
        id="circuit-helper-title"
        title="Where the main shared gadgets live"
        description="The flow is grouped by Orchard function. Reusable Poseidon, elliptic-curve, Sinsemilla, Merkle, and range-check gadgets appear here under the components that invoke them."
      />
      <div className="circuit-helper-grid">
        {families.map((family) => {
          const gates = data.configure.gates.filter((gate) =>
            gate.sourceIds.some((sourceId) =>
              family.matchers.some((matcher) =>
                sourcesById.get(sourceId)?.path.toLocaleLowerCase().includes(matcher)
              )
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

export function CircuitExplorer({
  loader = loadCircuitExplorerData,
}: {
  loader?: DataLoader<CircuitExplorerData>;
}) {
  const { data, error: loadError, retry } = useLoadableData(
    loader,
    "Unknown data-loading error",
  );
  const [route, setRoute] = useState<CircuitExplorerRoute>(defaultRoute);
  const [notice, setNotice] = useState("");
  const [searchOpen, setSearchOpen] = useState(false);
  const [visibleLimit, setVisibleLimit] = useState(EXACT_PAGE_SIZE);
  const narrowInspector = useMediaQuery("(max-width: 1160px)");
  const [mobileInspectorOpen, setMobileInspectorOpen] = useState(false);
  const searchRef = useRef<HTMLInputElement>(null);
  const layerRef = useRef<HTMLDivElement>(null);
  const inspectorToggleRef = useRef<HTMLButtonElement>(null);
  const focusedRouteRef = useRef(`${route.level}:${route.itemId ?? ""}:${route.focusId ?? ""}`);

  useEffect(() => {
    if (!narrowInspector) setMobileInspectorOpen(false);
  }, [narrowInspector]);

  useEffect(() => {
    setMobileInspectorOpen(false);
  }, [route.level, route.itemId]);

  useEffect(() => {
    if (!mobileInspectorOpen) return undefined;
    const onKeyDown = (event: KeyboardEvent) => {
      if (event.key !== "Escape") return;
      setMobileInspectorOpen(false);
      window.requestAnimationFrame(() => inspectorToggleRef.current?.focus());
    };
    document.addEventListener("keydown", onKeyDown);
    return () => document.removeEventListener("keydown", onKeyDown);
  }, [mobileInspectorOpen]);

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

  const openMobileInspector = () => {
    setMobileInspectorOpen(true);
    window.requestAnimationFrame(() => {
      document.querySelector<HTMLElement>("#circuit-inspector")?.focus();
    });
  };

  const closeMobileInspector = () => {
    setMobileInspectorOpen(false);
    window.requestAnimationFrame(() => inspectorToggleRef.current?.focus());
  };

  if (loadError) {
    return (
      <ExplorerError
        message={loadError}
        onRetry={() => {
          clearCircuitExplorerDataCache();
          retry();
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
        <div className="circuit-intro__copy">
          <p className="eyebrow">Rocq model · configure · synthesis · source</p>
          <h1 id="circuit-title">Orchard Circuit Explorer</h1>
          <p>
            Inspect the Orchard Action circuit from components and synthesis regions
            down to gates, lookups, constraints, and source locations.
          </p>
          <p className="circuit-interpretation-note" role="note">
            <strong>Interpretation layer:</strong>{" "}
            {data.metadata.representations.flow ??
              "Curated from source metadata; not itself a proof claim."}
          </p>
        </div>
        <MetricGrid compact metrics={data.metadata.metrics.slice(0, 6)} />
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
            title={selectedComponent.title}
            aria-label={selectedComponent.title}
            aria-current={route.level === "component" ? "page" : undefined}
            onClick={() => navigate({ ...route, level: "component", itemId: selectedComponent.id, focusId: null })}
          >
            {selectedComponent.shortTitle}
          </button>
        ) : <span>Component</span>}
        <span aria-hidden="true">/</span>
        <span
          className="circuit-breadcrumbs__current"
          title={route.level === "detail" && selectedEntry ? selectedEntry.title : undefined}
          aria-label={route.level === "detail" && selectedEntry ? selectedEntry.title : undefined}
          aria-current={route.level === "detail" ? "page" : undefined}
        >
          {route.level === "detail" && selectedEntry ? selectedEntry.title : "Region or gate"}
        </span>
      </nav>

      <section className="circuit-toolbar" aria-label="Circuit search">
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
                        <strong title={entry.title}>{entry.title}</strong>
                        <small title={entry.summary}>{entry.summary}</small>
                      </button>
                    </li>
                  ))}
                </ul>
              ) : <p>No circuit items match “{route.query}”.</p>}
            </div>
          ) : null}
        </div>
      </section>

      {notice ? <p className="circuit-route-notice" role="status">{notice}</p> : null}
      <p className="visually-hidden" aria-live="polite">
        {route.level === "flow"
          ? "Showing the high-level circuit flow."
          : route.level === "component"
            ? `Showing ${selectedComponent?.title ?? "a circuit component"}.`
            : `Showing ${selectedEntry?.title ?? "circuit detail"}.`}
      </p>

      {route.level !== "flow" && selectedEntry ? (
        <button
          ref={inspectorToggleRef}
          className="circuit-inspector-toggle"
          type="button"
          aria-controls="circuit-inspector"
          aria-expanded={mobileInspectorOpen}
          onClick={openMobileInspector}
        >
          Evidence and provenance
          <span aria-hidden="true">→</span>
        </button>
      ) : null}

      {narrowInspector && mobileInspectorOpen ? (
        <button
          className="circuit-inspector-backdrop"
          type="button"
          aria-label="Close evidence and provenance"
          onClick={closeMobileInspector}
        />
      ) : null}

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
                        <CircuitOperationRecord key={operation.id} operation={operation} />
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
        {route.level !== "flow" ? (
          <CircuitInspector
            data={data}
            entry={selectedEntry}
            mobileHidden={narrowInspector && !mobileInspectorOpen}
            onMobileClose={narrowInspector ? closeMobileInspector : undefined}
          />
        ) : null}
      </section>

      {route.level === "flow" ? (
        <>
          <CircuitOutline data={data} entries={entries} onSelect={selectEntry} />
          <EmbeddedGadgets data={data} entries={entries} onSelect={selectEntry} />
        </>
      ) : null}
    </main>
  );
}
