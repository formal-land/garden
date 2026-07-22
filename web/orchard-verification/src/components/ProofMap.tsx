import {
  useCallback,
  useEffect,
  useId,
  useMemo,
  useRef,
  useState,
  type Dispatch,
  type KeyboardEvent as ReactKeyboardEvent,
  type SetStateAction,
} from "react";

import type {
  AtlasBounds,
  AtlasPoint,
  FilterOption,
  OrchardVerificationData,
  ProofCluster,
  ProofEdge,
  ProofNode,
  ProofStatus,
  RepositoryId,
} from "../data/model";
import { statusLabels } from "./EvidencePanel";

const NODE_WIDTH = 176;
const NODE_HEIGHT = 78;
const MAP_PADDING = 54;

interface ViewBox extends AtlasBounds {}

type FocusValue = string | readonly string[] | null;
type AtlasViewMode = "graph" | "list";

export interface ProofMapProps {
  readonly data: OrchardVerificationData;
  /** Node or nodes emphasized by the journey at its current stage. */
  readonly focus?: FocusValue;
  /** When supplied, only these nodes are drawn. Useful for journey progression. */
  readonly revealed?: readonly string[] | null;
  /** A compact map omits the atlas toolbar, inspector, legend, and list view. */
  readonly compact?: boolean;
  readonly className?: string;
  /** Compatibility aliases for callers that prefer explicit names. */
  readonly focusNodeIds?: readonly string[];
  readonly revealedNodeIds?: readonly string[];
}

interface FilterGroupProps<T extends string> {
  readonly legend: string;
  readonly options: readonly FilterOption<T>[];
  readonly active: ReadonlySet<T>;
  readonly onToggle: (id: T) => void;
  readonly onClear: () => void;
}

function classNames(
  ...values: ReadonlyArray<string | false | null | undefined>
): string {
  return values.filter(Boolean).join(" ");
}

function titleCase(value: string): string {
  return value
    .split("-")
    .map((part) => part.charAt(0).toUpperCase() + part.slice(1))
    .join(" ");
}

function toIdSet(value: FocusValue): Set<string> {
  if (typeof value === "string") return new Set([value]);
  return new Set(value ?? []);
}

function wrapText(value: string, maximum = 29, lineLimit = 3): string[] {
  const words = value.trim().split(/\s+/);
  const lines: string[] = [];
  let line = "";

  for (const word of words) {
    const next = line ? `${line} ${word}` : word;
    if (next.length <= maximum || !line) {
      line = next;
      continue;
    }
    lines.push(line);
    line = word;
    if (lines.length === lineLimit - 1) break;
  }

  if (line && lines.length < lineLimit) lines.push(line);
  const consumed = lines.join(" ").split(/\s+/).length;
  if (consumed < words.length && lines.length) {
    const last = lines.length - 1;
    lines[last] = `${lines[last].replace(/[.,;:]$/, "")}…`;
  }
  return lines;
}

function calculateMapBounds(
  clusters: readonly ProofCluster[],
  nodes: readonly ProofNode[],
): ViewBox {
  const left = clusters.length
    ? Math.min(...clusters.map((cluster) => cluster.bounds.x))
    : Math.min(0, ...nodes.map((node) => node.position.x - NODE_WIDTH / 2));
  const top = clusters.length
    ? Math.min(...clusters.map((cluster) => cluster.bounds.y))
    : Math.min(0, ...nodes.map((node) => node.position.y - NODE_HEIGHT / 2));
  const right = clusters.length
    ? Math.max(
        ...clusters.map(
          (cluster) => cluster.bounds.x + cluster.bounds.width,
        ),
      )
    : Math.max(640, ...nodes.map((node) => node.position.x + NODE_WIDTH / 2));
  const bottom = clusters.length
    ? Math.max(
        ...clusters.map(
          (cluster) => cluster.bounds.y + cluster.bounds.height,
        ),
      )
    : Math.max(420, ...nodes.map((node) => node.position.y + NODE_HEIGHT / 2));

  return {
    x: left - MAP_PADDING,
    y: top - MAP_PADDING,
    width: Math.max(320, right - left + MAP_PADDING * 2),
    height: Math.max(240, bottom - top + MAP_PADDING * 2),
  };
}

function calculateNodeBounds(
  nodes: readonly ProofNode[],
  positions: ReadonlyMap<string, AtlasPoint> = new Map(),
): ViewBox | null {
  if (!nodes.length) return null;
  const padding = 92;
  const positionFor = (node: ProofNode) => positions.get(node.id) ?? node.position;
  const left = Math.min(...nodes.map((node) => positionFor(node).x - NODE_WIDTH / 2));
  const top = Math.min(...nodes.map((node) => positionFor(node).y - NODE_HEIGHT / 2));
  const right = Math.max(...nodes.map((node) => positionFor(node).x + NODE_WIDTH / 2));
  const bottom = Math.max(...nodes.map((node) => positionFor(node).y + NODE_HEIGHT / 2));

  return {
    x: left - padding,
    y: top - padding,
    width: Math.max(360, right - left + padding * 2),
    height: Math.max(260, bottom - top + padding * 2),
  };
}

function clusterCentre(cluster: ProofCluster): AtlasPoint {
  return {
    x: cluster.bounds.x + cluster.bounds.width / 2,
    y: cluster.bounds.y + cluster.bounds.height / 2,
  };
}

function shortenEdge(from: AtlasPoint, to: AtlasPoint): {
  from: AtlasPoint;
  to: AtlasPoint;
} {
  const dx = to.x - from.x;
  const dy = to.y - from.y;
  const distance = Math.max(1, Math.hypot(dx, dy));
  const inset = Math.min(54, distance * 0.22);
  const xInset = (dx / distance) * inset;
  const yInset = (dy / distance) * inset;
  return {
    from: { x: from.x + xInset, y: from.y + yInset },
    to: { x: to.x - xInset, y: to.y - yInset },
  };
}

function edgePath(fromPoint: AtlasPoint, toPoint: AtlasPoint): string {
  const { from, to } = shortenEdge(fromPoint, toPoint);
  const dx = to.x - from.x;
  const dy = to.y - from.y;

  if (Math.abs(dx) >= Math.abs(dy) * 0.55) {
    const bend = Math.max(30, Math.abs(dx) * 0.36);
    const direction = dx >= 0 ? 1 : -1;
    return `M ${from.x} ${from.y} C ${from.x + bend * direction} ${from.y}, ${to.x - bend * direction} ${to.y}, ${to.x} ${to.y}`;
  }

  const bend = Math.max(30, Math.abs(dy) * 0.34);
  const direction = dy >= 0 ? 1 : -1;
  return `M ${from.x} ${from.y} C ${from.x} ${from.y + bend * direction}, ${to.x} ${to.y - bend * direction}, ${to.x} ${to.y}`;
}

function midpoint(from: AtlasPoint, to: AtlasPoint): AtlasPoint {
  return { x: (from.x + to.x) / 2, y: (from.y + to.y) / 2 };
}

function readNodeFromHash(): string | null {
  if (typeof window === "undefined") return null;
  return new URLSearchParams(window.location.hash.slice(1)).get("node");
}

function writeNodeToHash(nodeId: string | null): void {
  if (typeof window === "undefined") return;
  const parameters = new URLSearchParams(window.location.hash.slice(1));
  if (nodeId) parameters.set("node", nodeId);
  else parameters.delete("node");
  const hash = parameters.toString();
  window.history.replaceState(
    null,
    "",
    `${window.location.pathname}${window.location.search}${hash ? `#${hash}` : ""}`,
  );
}

function toggleSelection<T extends string>(
  setter: Dispatch<SetStateAction<Set<T>>>,
  value: T,
): void {
  setter((current) => {
    const next = new Set(current);
    if (next.has(value)) next.delete(value);
    else next.add(value);
    return next;
  });
}

function FilterGroup<T extends string>({
  legend,
  options,
  active,
  onToggle,
  onClear,
}: FilterGroupProps<T>) {
  return (
    <fieldset className="proof-map__filter-group">
      <legend>
        {legend}
        <span className="proof-map__filter-count">
          {active.size ? ` · ${active.size} selected` : " · All"}
        </span>
      </legend>
      <div className="proof-map__filter-options">
        {options.map((option) => (
          <label className="proof-map__filter-option" key={option.id}>
            <input
              type="checkbox"
              checked={active.has(option.id)}
              onChange={() => onToggle(option.id)}
            />
            <span title={option.description}>{option.label}</span>
          </label>
        ))}
      </div>
      {active.size ? (
        <button
          className="proof-map__filter-clear"
          type="button"
          onClick={onClear}
        >
          Clear {legend.toLowerCase()}
        </button>
      ) : null}
    </fieldset>
  );
}

export function ProofMap({
  data,
  focus = null,
  revealed = null,
  compact = false,
  className,
  focusNodeIds = [],
  revealedNodeIds,
}: ProofMapProps) {
  const inspectorRef = useRef<HTMLElement>(null);
  const rawId = useId();
  const markerPrefix = rawId.replace(/:/g, "");
  const formalMarkerId = `${markerPrefix}-formal-arrow`;
  const provenanceMarkerId = `${markerPrefix}-provenance-arrow`;
  const filtersPanelId = `${markerPrefix}-filters`;
  const graphPanelId = `${markerPrefix}-graph`;
  const listPanelId = `${markerPrefix}-list`;

  const nodeById = useMemo(
    () => new Map(data.nodes.map((node) => [node.id, node])),
    [data.nodes],
  );
  const clusterById = useMemo(
    () => new Map(data.clusters.map((cluster) => [cluster.id, cluster])),
    [data.clusters],
  );
  const evidenceById = useMemo(
    () => new Map(data.evidence.map((item) => [item.id, item])),
    [data.evidence],
  );
  const repositoryById = useMemo(
    () => new Map(data.repositories.map((repository) => [repository.id, repository])),
    [data.repositories],
  );

  const focusedIds = useMemo(() => {
    const values = toIdSet(focus);
    for (const id of focusNodeIds) values.add(id);
    return values;
  }, [focus, focusNodeIds]);
  const revealedIds = useMemo(() => {
    if (revealed === null && revealedNodeIds === undefined) return null;
    const values = new Set(revealed ?? []);
    for (const id of revealedNodeIds ?? []) values.add(id);
    return values;
  }, [revealed, revealedNodeIds]);

  const baseViewBox = useMemo(
    () => calculateMapBounds(data.clusters, data.nodes),
    [data.clusters, data.nodes],
  );
  const [collapsedClusters, setCollapsedClusters] = useState<Set<string>>(
    () => new Set(),
  );
  const [hoveredNodeId, setHoveredNodeId] = useState<string | null>(null);
  const [selectedNodeId, setSelectedNodeId] = useState<string | null>(() =>
    compact ? null : readNodeFromHash(),
  );
  const [repositoryFilters, setRepositoryFilters] = useState<Set<RepositoryId>>(
    () => new Set(),
  );
  const [statusFilters, setStatusFilters] = useState<Set<ProofStatus>>(
    () => new Set(),
  );
  const [searchQuery, setSearchQuery] = useState("");
  const [filtersOpen, setFiltersOpen] = useState(false);
  const [viewMode, setViewMode] = useState<AtlasViewMode>(
    () =>
      typeof window !== "undefined" &&
      window.matchMedia("(max-width: 760px)").matches
        ? "list"
        : "graph",
  );
  const [graphViewBox, setGraphViewBox] = useState<ViewBox | null>(null);
  const [showRelatedOnly, setShowRelatedOnly] = useState(false);

  useEffect(() => {
    const query = window.matchMedia("(max-width: 760px)");
    const onChange = (event: MediaQueryListEvent) =>
      setViewMode(event.matches ? "list" : "graph");
    query.addEventListener("change", onChange);
    return () => query.removeEventListener("change", onChange);
  }, []);

  useEffect(() => {
    if (!selectedNodeId) setShowRelatedOnly(false);
  }, [selectedNodeId]);

  useEffect(() => {
    if (compact) return undefined;
    const onHashChange = () => {
      const candidate = readNodeFromHash();
      setSelectedNodeId(candidate && nodeById.has(candidate) ? candidate : null);
    };
    onHashChange();
    window.addEventListener("hashchange", onHashChange);
    return () => window.removeEventListener("hashchange", onHashChange);
  }, [compact, nodeById]);

  useEffect(() => {
    if (!selectedNodeId) return;
    const selected = nodeById.get(selectedNodeId);
    if (!selected) {
      setSelectedNodeId(null);
      if (!compact) writeNodeToHash(null);
      return;
    }
    setCollapsedClusters((current) => {
      if (!current.has(selected.clusterId)) return current;
      const next = new Set(current);
      next.delete(selected.clusterId);
      return next;
    });
  }, [compact, nodeById, selectedNodeId]);

  useEffect(() => {
    if (!compact && inspectorRef.current) inspectorRef.current.scrollTop = 0;
  }, [compact, selectedNodeId]);

  const isRevealed = useCallback(
    (nodeId: string) => revealedIds === null || revealedIds.has(nodeId),
    [revealedIds],
  );

  const nodeMatches = useMemo(() => {
    const result = new Map<string, boolean>();
    const normalizedQuery = searchQuery.trim().toLocaleLowerCase();
    for (const node of data.nodes) {
      const repositoryMatch =
        repositoryFilters.size === 0 ||
        node.repoIds.some((repoId) => repositoryFilters.has(repoId));
      const statusMatch =
        statusFilters.size === 0 || statusFilters.has(node.status);
      const cluster = clusterById.get(node.clusterId);
      const searchMatch =
        normalizedQuery.length === 0 ||
        [
          node.title,
          node.shortTitle,
          node.summary,
          node.detail,
          node.status,
          node.track,
          ...node.tags,
          cluster?.title,
          cluster?.summary,
          ...node.repoIds.flatMap((repoId) => {
            const repository = repositoryById.get(repoId);
            return repository
              ? [repository.name, repository.shortName]
              : [repoId];
          }),
        ]
          .filter((value): value is string => value !== undefined)
          .join(" ")
          .toLocaleLowerCase()
          .includes(normalizedQuery);
      result.set(
        node.id,
        repositoryMatch && statusMatch && searchMatch,
      );
    }
    return result;
  }, [
    clusterById,
    data.nodes,
    repositoryById,
    repositoryFilters,
    searchQuery,
    statusFilters,
  ]);

  const resultNodes = useMemo(
    () =>
      data.nodes.filter(
        (node) => isRevealed(node.id) && nodeMatches.get(node.id),
      ),
    [data.nodes, isRevealed, nodeMatches],
  );

  const attentionIds = useMemo(() => {
    if (selectedNodeId && nodeMatches.get(selectedNodeId)) return new Set([selectedNodeId]);
    if (selectedNodeId) return new Set([selectedNodeId]);
    if (hoveredNodeId) return new Set([hoveredNodeId]);
    return focusedIds;
  }, [focusedIds, hoveredNodeId, nodeMatches, selectedNodeId]);

  const neighbourIds = useMemo(() => {
    const neighbours = new Set<string>();
    if (attentionIds.size === 0) return neighbours;
    for (const edge of data.edges) {
      if (attentionIds.has(edge.from)) neighbours.add(edge.to);
      if (attentionIds.has(edge.to)) neighbours.add(edge.from);
    }
    return neighbours;
  }, [attentionIds, data.edges]);

  const toggleCluster = useCallback((clusterId: string) => {
    setCollapsedClusters((current) => {
      const next = new Set(current);
      if (next.has(clusterId)) next.delete(clusterId);
      else next.add(clusterId);
      return next;
    });
  }, []);

  const inspectNode = useCallback(
    (nodeId: string) => {
      const next = selectedNodeId === nodeId ? null : nodeId;
      setSelectedNodeId(next);
      if (!compact) writeNodeToHash(next);
      if (next) {
        const node = nodeById.get(next);
        if (node) {
          setCollapsedClusters((current) => {
            if (!current.has(node.clusterId)) return current;
            const expanded = new Set(current);
            expanded.delete(node.clusterId);
            return expanded;
          });
        }
      }
    },
    [compact, nodeById, selectedNodeId],
  );

  const onNodeKeyDown = useCallback(
    (event: ReactKeyboardEvent<SVGGElement>, nodeId: string) => {
      if (event.key !== "Enter" && event.key !== " ") return;
      event.preventDefault();
      event.stopPropagation();
      inspectNode(nodeId);
    },
    [inspectNode],
  );

  const onClusterKeyDown = useCallback(
    (event: ReactKeyboardEvent<SVGGElement>, clusterId: string) => {
      if (event.key !== "Enter" && event.key !== " ") return;
      event.preventDefault();
      event.stopPropagation();
      toggleCluster(clusterId);
    },
    [toggleCluster],
  );

  const resetFilters = useCallback(() => {
    setRepositoryFilters(new Set());
    setStatusFilters(new Set());
    setSearchQuery("");
  }, []);

  const onViewTabKeyDown = useCallback(
    (event: ReactKeyboardEvent<HTMLButtonElement>) => {
      let nextView: AtlasViewMode | null = null;
      if (event.key === "ArrowLeft" || event.key === "Home") {
        nextView = "graph";
      } else if (event.key === "ArrowRight" || event.key === "End") {
        nextView = "list";
      }
      if (!nextView) return;
      event.preventDefault();
      setViewMode(nextView);
      document
        .getElementById(`${markerPrefix}-${nextView}-tab`)
        ?.focus();
    },
    [markerPrefix],
  );

  const selectedNode = selectedNodeId
    ? nodeById.get(selectedNodeId) ?? null
    : null;
  const selectedEvidence = selectedNode
    ? selectedNode.evidenceIds
        .map((id) => evidenceById.get(id))
        .filter((item) => item !== undefined)
    : [];
  const filtersAreActive =
    repositoryFilters.size > 0 ||
    statusFilters.size > 0 ||
    searchQuery.trim().length > 0;
  const compactPositionById = useMemo(() => {
    const positions = new Map<string, AtlasPoint>();
    if (!compact || revealedIds === null) return positions;
    const visibleNodes = data.nodes
      .filter((node) => revealedIds.has(node.id))
      .sort((left, right) =>
        left.position.y - right.position.y || left.position.x - right.position.x
      );
    const columns = Math.min(5, Math.max(1, Math.ceil(Math.sqrt(visibleNodes.length * 1.6))));
    visibleNodes.forEach((node, index) => {
      positions.set(node.id, {
        x: 120 + (index % columns) * 240,
        y: 90 + Math.floor(index / columns) * 140,
      });
    });
    return positions;
  }, [compact, data.nodes, revealedIds]);

  const endpointFor = useCallback(
    (nodeId: string): AtlasPoint | null => {
      const node = nodeById.get(nodeId);
      if (!node || !isRevealed(nodeId)) return null;
      const cluster = clusterById.get(node.clusterId);
      if (cluster && collapsedClusters.has(cluster.id)) {
        return clusterCentre(cluster);
      }
      return compactPositionById.get(nodeId) ?? node.position;
    },
    [clusterById, collapsedClusters, compactPositionById, isRevealed, nodeById],
  );

  const visibleEdges = useMemo(
    () =>
      data.edges
        .map((edge) => ({
          edge,
          from: endpointFor(edge.from),
          to: endpointFor(edge.to),
        }))
        .filter(
          (
            item,
          ): item is {
            edge: ProofEdge;
            from: AtlasPoint;
            to: AtlasPoint;
          } =>
            item.from !== null &&
            item.to !== null &&
            (item.from.x !== item.to.x || item.from.y !== item.to.y),
        ),
    [data.edges, endpointFor],
  );
  const fittedViewBox = useMemo(() => {
    if (!compact || revealedIds === null) return baseViewBox;
    return calculateNodeBounds(
      data.nodes.filter((node) => revealedIds.has(node.id)),
      compactPositionById,
    ) ?? baseViewBox;
  }, [baseViewBox, compact, compactPositionById, data.nodes, revealedIds]);

  const displayedViewBox = graphViewBox ?? fittedViewBox;
  const graphZoom = Math.round(
    Math.min(
      fittedViewBox.width / displayedViewBox.width,
      fittedViewBox.height / displayedViewBox.height,
    ) * 100,
  );

  const zoomGraph = useCallback(
    (factor: number) => {
      setGraphViewBox((current) => {
        const source = current ?? fittedViewBox;
        const sourceScale = fittedViewBox.width / source.width;
        const nextScale = Math.min(2.5, Math.max(0.5, sourceScale / factor));
        const nextWidth = fittedViewBox.width / nextScale;
        const nextHeight = source.height * (nextWidth / source.width);
        return {
          x: source.x + (source.width - nextWidth) / 2,
          y: source.y + (source.height - nextHeight) / 2,
          width: nextWidth,
          height: nextHeight,
        };
      });
    },
    [fittedViewBox],
  );

  const fitFilteredNodes = useCallback(() => {
    setGraphViewBox(
      calculateNodeBounds(resultNodes, compactPositionById) ?? fittedViewBox,
    );
    setViewMode("graph");
  }, [compactPositionById, fittedViewBox, resultNodes]);

  const resetGraphView = useCallback(() => setGraphViewBox(null), []);

  const selectedIncomingEdges = useMemo(
    () =>
      selectedNodeId
        ? data.edges.filter((edge) => edge.to === selectedNodeId)
        : [],
    [data.edges, selectedNodeId],
  );
  const selectedOutgoingEdges = useMemo(
    () =>
      selectedNodeId
        ? data.edges.filter((edge) => edge.from === selectedNodeId)
        : [],
    [data.edges, selectedNodeId],
  );

  const proofStatusCounts = useMemo(() => {
    const counts = new Map<ProofStatus, number>();
    for (const node of resultNodes) {
      counts.set(node.status, (counts.get(node.status) ?? 0) + 1);
    }
    return counts;
  }, [resultNodes]);

  return (
    <section
      className={classNames(
        "proof-map",
        compact && "proof-map--compact",
        className,
      )}
      data-compact={compact || undefined}
      data-view={compact ? "graph" : viewMode}
    >
      {!compact ? (
        <div className="proof-map__toolbar" aria-label="Atlas controls">
          <button
            className="proof-map__filter-toggle"
            type="button"
            aria-expanded={filtersOpen}
            aria-controls={filtersPanelId}
            onClick={() => setFiltersOpen((current) => !current)}
          >
            Filter nodes
            {filtersAreActive
              ? ` (${repositoryFilters.size + statusFilters.size + (searchQuery.trim() ? 1 : 0)})`
              : ""}
          </button>

          <div
            className={classNames(
              "proof-map__filters",
              filtersOpen && "is-open",
            )}
            id={filtersPanelId}
          >
            <FilterGroup
              legend="Repositories"
              options={data.filters.repositories}
              active={repositoryFilters}
              onToggle={(id) => toggleSelection(setRepositoryFilters, id)}
              onClear={() => setRepositoryFilters(new Set())}
            />
            <FilterGroup
              legend="Proof status"
              options={data.filters.statuses}
              active={statusFilters}
              onToggle={(id) => toggleSelection(setStatusFilters, id)}
              onClear={() => setStatusFilters(new Set())}
            />
          </div>

          <label className="proof-map__search">
            <span>Search</span>
            <input
              type="search"
              value={searchQuery}
              aria-label="Search the atlas"
              placeholder="Claims, sources, repositories…"
              onChange={(event) => setSearchQuery(event.currentTarget.value)}
            />
          </label>

          <div className="proof-map__toolbar-actions">
            <output className="proof-map__result-count" aria-live="polite">
              {resultNodes.length} of {data.nodes.length} nodes
            </output>
            <button
              className="proof-map__reset-filters"
              type="button"
              disabled={!filtersAreActive}
              onClick={resetFilters}
            >
              Reset
            </button>
            <button
              className="proof-map__fit-filtered"
              type="button"
              disabled={resultNodes.length === 0}
              onClick={fitFilteredNodes}
            >
              Fit graph
            </button>
          </div>

          <div className="proof-map__view-switcher" role="tablist" aria-label="Atlas view">
            <button
              id={`${markerPrefix}-graph-tab`}
              type="button"
              role="tab"
              aria-selected={viewMode === "graph"}
              aria-controls={graphPanelId}
              tabIndex={viewMode === "graph" ? 0 : -1}
              onClick={() => setViewMode("graph")}
              onKeyDown={onViewTabKeyDown}
            >
              Graph
            </button>
            <button
              id={`${markerPrefix}-list-tab`}
              type="button"
              role="tab"
              aria-selected={viewMode === "list"}
              aria-controls={listPanelId}
              tabIndex={viewMode === "list" ? 0 : -1}
              onClick={() => setViewMode("list")}
              onKeyDown={onViewTabKeyDown}
            >
              List
            </button>
          </div>
        </div>
      ) : null}

      <div
        className={classNames(
          "proof-map__workspace",
          selectedNode && !compact ? "has-inspector" : "is-visualization-only",
        )}
      >
        <div className="proof-map__view-panels">
          <div
            className="proof-map__graph-panel"
            id={compact ? undefined : graphPanelId}
            role={compact ? undefined : "tabpanel"}
            aria-labelledby={compact ? undefined : `${markerPrefix}-graph-tab`}
            hidden={!compact && viewMode !== "graph"}
          >
            <div className="proof-map__canvas-wrap">
              <p className="visually-hidden" id={`${markerPrefix}-graph-instructions`}>
                Use Tab to move between proof nodes and Enter or Space to inspect one.
                Arrowheads show the direction of each relationship.
              </p>
              <svg
                className="proof-map__canvas"
                viewBox={`${displayedViewBox.x} ${displayedViewBox.y} ${displayedViewBox.width} ${displayedViewBox.height}`}
                preserveAspectRatio="xMidYMid meet"
                role="group"
                aria-label="Interactive Orchard verification proof atlas"
                aria-describedby={`${markerPrefix}-graph-instructions`}
              >
                <defs>
                  <marker
                    id={formalMarkerId}
                    className="proof-map__marker proof-map__marker--formal"
                    viewBox="0 0 10 10"
                    refX="9"
                    refY="5"
                    markerWidth="7"
                    markerHeight="7"
                    orient="auto"
                  >
                    <path d="M 0 0 L 10 5 L 0 10 z" />
                  </marker>
                  <marker
                    id={provenanceMarkerId}
                    className="proof-map__marker proof-map__marker--provenance"
                    viewBox="0 0 10 10"
                    refX="9"
                    refY="5"
                    markerWidth="7"
                    markerHeight="7"
                    orient="auto"
                  >
                    <path d="M 0 1 L 9 5 L 0 9 L 3 5 z" />
                  </marker>
                </defs>

                <g className="proof-map__clusters">
                  {data.clusters.map((cluster) => {
                    const visibleNodeIds = cluster.nodeIds.filter(isRevealed);
                    if (revealedIds !== null && visibleNodeIds.length === 0) {
                      return null;
                    }
                    const isCollapsed = collapsedClusters.has(cluster.id);
                    const hasSelectedNode =
                      selectedNodeId !== null &&
                      visibleNodeIds.includes(selectedNodeId);
                    const hasMatch =
                      hasSelectedNode ||
                      visibleNodeIds.some(
                        (nodeId) => nodeMatches.get(nodeId) ?? false,
                      );
                    return (
                      <g
                        className={classNames(
                          "proof-map__cluster",
                          `proof-map__cluster--${cluster.status}`,
                          `proof-map__cluster--track-${cluster.track}`,
                          isCollapsed && "is-collapsed",
                          !hasMatch && "is-filtered-out",
                        )}
                        key={cluster.id}
                        data-cluster-id={cluster.id}
                        data-status={cluster.status}
                        data-track={cluster.track}
                        opacity={hasMatch ? 1 : 0.1}
                      >
                        <rect
                          className="proof-map__cluster-shape"
                          x={cluster.bounds.x}
                          y={cluster.bounds.y}
                          width={cluster.bounds.width}
                          height={cluster.bounds.height}
                          rx="12"
                        />
                        {!isCollapsed ? (
                          <g
                            className="proof-map__cluster-heading"
                            role="button"
                            tabIndex={0}
                            aria-label={`Collapse ${cluster.title} cluster`}
                            aria-expanded="true"
                            onPointerDown={(event) => event.stopPropagation()}
                            onClick={(event) => {
                              event.stopPropagation();
                              toggleCluster(cluster.id);
                            }}
                            onKeyDown={(event) =>
                              onClusterKeyDown(event, cluster.id)
                            }
                          >
                            <rect
                              className="proof-map__cluster-heading-hitbox"
                              x={cluster.bounds.x + 8}
                              y={cluster.bounds.y + 5}
                              width={Math.min(250, cluster.bounds.width - 16)}
                              height="42"
                              rx="4"
                            />
                            <text
                              x={cluster.bounds.x + 19}
                              y={cluster.bounds.y + 31}
                            >
                              {cluster.shortTitle}
                              <tspan className="proof-map__cluster-toggle-glyph"> −</tspan>
                            </text>
                          </g>
                        ) : null}
                      </g>
                    );
                  })}
                </g>

                <g className="proof-map__edges" aria-hidden="true">
                  {visibleEdges.map(({ edge, from, to }) => {
                    const isConnected =
                      attentionIds.has(edge.from) || attentionIds.has(edge.to);
                    const filteredOut =
                      !nodeMatches.get(edge.from) || !nodeMatches.get(edge.to);
                    const muted = attentionIds.size > 0 && !isConnected;
                    const outsideFocus = showRelatedOnly && !isConnected;
                    const point = midpoint(from, to);
                    return (
                      <g
                        key={edge.id}
                        className={classNames(
                          "proof-map__edge",
                          `proof-map__edge--${edge.family}`,
                          `proof-map__edge--${edge.status}`,
                          isConnected && "is-active",
                          muted && "is-muted",
                          filteredOut && "is-filtered-out",
                          outsideFocus && "is-outside-focus",
                        )}
                        data-relation={edge.relation}
                        data-direction={`${edge.from}:${edge.to}`}
                        opacity={
                          outsideFocus
                            ? 0.04
                            : filteredOut && !isConnected
                              ? 0.08
                              : muted
                                ? 0.24
                                : 1
                        }
                      >
                        <path
                          d={edgePath(from, to)}
                          fill="none"
                          strokeWidth={isConnected ? 2.8 : 1.7}
                          strokeDasharray={
                            edge.family === "provenance" ? "7 6" : undefined
                          }
                          markerEnd={`url(#${
                            edge.family === "formal"
                              ? formalMarkerId
                              : provenanceMarkerId
                          })`}
                        />
                        {isConnected && attentionIds.size > 0 ? (
                          <text
                            className="proof-map__edge-label"
                            x={point.x}
                            y={point.y - 7}
                            textAnchor="middle"
                          >
                            {edge.label}
                          </text>
                        ) : null}
                      </g>
                    );
                  })}
                </g>

                <g className="proof-map__collapsed-clusters">
                  {data.clusters.map((cluster) => {
                    if (!collapsedClusters.has(cluster.id)) return null;
                    const visibleNodeIds = cluster.nodeIds.filter(isRevealed);
                    if (revealedIds !== null && visibleNodeIds.length === 0) {
                      return null;
                    }
                    const centre = clusterCentre(cluster);
                    const lines = wrapText(cluster.collapsedSummary, 34, 3);
                    return (
                      <g
                        key={cluster.id}
                        className="proof-map__collapsed-summary"
                        role="button"
                        tabIndex={0}
                        aria-expanded="false"
                        aria-label={`Expand ${cluster.title} cluster. ${cluster.collapsedSummary}`}
                        onPointerDown={(event) => event.stopPropagation()}
                        onClick={(event) => {
                          event.stopPropagation();
                          toggleCluster(cluster.id);
                        }}
                        onKeyDown={(event) =>
                          onClusterKeyDown(event, cluster.id)
                        }
                      >
                        <rect
                          x={centre.x - 116}
                          y={centre.y - 55}
                          width="232"
                          height="110"
                          rx="12"
                        />
                        <text
                          className="proof-map__collapsed-title"
                          x={centre.x}
                          y={centre.y - 27}
                          textAnchor="middle"
                        >
                          {cluster.shortTitle} +
                        </text>
                        <text
                          className="proof-map__collapsed-copy"
                          x={centre.x}
                          y={centre.y - 5}
                          textAnchor="middle"
                        >
                          {lines.map((line, index) => (
                            <tspan
                              x={centre.x}
                              dy={index === 0 ? 0 : 17}
                              key={`${index}-${line}`}
                            >
                              {line}
                            </tspan>
                          ))}
                        </text>
                      </g>
                    );
                  })}
                </g>

                <g className="proof-map__nodes">
                  {data.nodes.map((node) => {
                    if (
                      !isRevealed(node.id) ||
                      collapsedClusters.has(node.clusterId)
                    ) {
                      return null;
                    }
                    const matches = nodeMatches.get(node.id) ?? false;
                    const isActive = attentionIds.has(node.id);
                    const isNeighbour = neighbourIds.has(node.id);
                    const isSelected = selectedNodeId === node.id;
                    const isMuted =
                      attentionIds.size > 0 &&
                      !isActive &&
                      !isNeighbour &&
                      !isSelected;
                    const outsideFocus = showRelatedOnly && isMuted;
                    const isInteractive = matches || isSelected;
                    const titleLines = wrapText(node.shortTitle, 23, 2);
                    const repositoryLabels = node.repoIds
                      .map(
                        (repoId) =>
                          repositoryById.get(repoId)?.shortName ?? repoId,
                      );
                    const statusLabel = statusLabels[node.status];
                    const primaryRepository = repositoryLabels[0];
                    const statusWithContext = primaryRepository
                      ? `${statusLabel} · ${primaryRepository}`
                      : statusLabel;
                    const nodeMeta = statusWithContext.length <= 22
                      ? statusWithContext
                      : statusLabel;
                    const position =
                      compactPositionById.get(node.id) ?? node.position;
                    return (
                      <g
                        key={node.id}
                        className={classNames(
                          "proof-map__node",
                          `proof-map__node--${node.status}`,
                          `proof-map__node--track-${node.track}`,
                          isActive && "is-active",
                          isNeighbour && "is-related",
                          isSelected && "is-selected",
                          isMuted && "is-muted",
                          outsideFocus && "is-outside-focus",
                          !matches && "is-filtered-out",
                        )}
                        transform={`translate(${position.x - NODE_WIDTH / 2} ${position.y - NODE_HEIGHT / 2})`}
                        role="button"
                        tabIndex={isInteractive ? 0 : -1}
                        aria-hidden={!isInteractive || undefined}
                        aria-label={`${node.title}. ${statusLabels[node.status]}. ${node.summary}`}
                        aria-pressed={isSelected}
                        data-emphasis={
                          isSelected
                            ? "selected"
                            : isNeighbour
                              ? "related"
                              : undefined
                        }
                        data-node-id={node.id}
                        data-status={node.status}
                        data-track={node.track}
                        opacity={
                          outsideFocus
                            ? 0.04
                            : !matches && !isSelected
                              ? 0.08
                              : isMuted
                                ? 0.48
                                : 1
                        }
                        onPointerDown={(event) => event.stopPropagation()}
                        onPointerEnter={() =>
                          isInteractive && setHoveredNodeId(node.id)
                        }
                        onPointerLeave={() => setHoveredNodeId(null)}
                        onFocus={() =>
                          isInteractive && setHoveredNodeId(node.id)
                        }
                        onBlur={() => setHoveredNodeId(null)}
                        onClick={(event) => {
                          event.stopPropagation();
                          if (isInteractive) inspectNode(node.id);
                        }}
                        onKeyDown={(event) => onNodeKeyDown(event, node.id)}
                      >
                        {isSelected ? (
                          <rect
                            className="proof-map__selection-ring proof-map__selection-outline"
                            x="-6"
                            y="-6"
                            width={NODE_WIDTH + 12}
                            height={NODE_HEIGHT + 12}
                            rx="12"
                          />
                        ) : null}
                        <rect
                          className="proof-map__node-card"
                          width={NODE_WIDTH}
                          height={NODE_HEIGHT}
                          rx="9"
                        />
                        <circle
                          className="proof-map__node-status-dot"
                          cx="15"
                          cy="16"
                          r="5"
                        />
                        <text className="proof-map__node-title" x="28" y="20">
                          {titleLines.map((line, index) => (
                            <tspan
                              x="28"
                              dy={index === 0 ? 0 : 16}
                              key={`${index}-${line}`}
                            >
                              {line}
                            </tspan>
                          ))}
                        </text>
                        <text className="proof-map__node-meta" x="15" y="65">
                          <tspan>{nodeMeta}</tspan>
                        </text>
                        {isNeighbour && !isSelected ? (
                          <circle
                            className="proof-map__related-indicator"
                            cx="160"
                            cy="16"
                            r="6"
                          />
                        ) : null}
                      </g>
                    );
                  })}
                </g>
              </svg>

              {!compact ? (
                <>
                  <div
                    className="proof-map__graph-controls"
                    role="toolbar"
                    aria-label="Map view controls"
                  >
                    <button
                      type="button"
                      aria-label="Zoom out"
                      disabled={graphZoom <= 50}
                      onClick={() => zoomGraph(1.25)}
                    >
                      −
                    </button>
                    <output aria-label="Current map zoom">{graphZoom}%</output>
                    <button
                      type="button"
                      aria-label="Zoom in"
                      disabled={graphZoom >= 250}
                      onClick={() => zoomGraph(0.8)}
                    >
                      +
                    </button>
                    <button
                      type="button"
                      aria-label="Fit visible nodes"
                      disabled={resultNodes.length === 0}
                      onClick={fitFilteredNodes}
                    >
                      Fit
                    </button>
                    <button
                      type="button"
                      aria-label="Reset map view"
                      disabled={graphViewBox === null}
                      onClick={resetGraphView}
                    >
                      Reset view
                    </button>
                    <button
                      type="button"
                      aria-pressed={showRelatedOnly}
                      disabled={!selectedNode}
                      onClick={() => setShowRelatedOnly((current) => !current)}
                    >
                      Related only
                    </button>
                  </div>

                  <details className="proof-map__legend proof-map__canvas-legend">
                    <summary>Legend</summary>
                    <div className="proof-map__legend-content">
                      <span>
                        <i className="proof-map__legend-line proof-map__legend-line--formal" />
                        Formal implication
                      </span>
                      <span>
                        <i className="proof-map__legend-line proof-map__legend-line--provenance" />
                        Provenance or parity
                      </span>
                      <span>
                        <i className="proof-map__legend-line proof-map__legend-line--assumption" />
                        Assumption or trust boundary
                      </span>
                      {data.filters.statuses.map((status) => (
                        <span key={status.id}>
                          <i
                            className={`proof-map__legend-node proof-map__legend-node--${status.id}`}
                          />
                          {status.label}
                          {proofStatusCounts.has(status.id)
                            ? ` (${proofStatusCounts.get(status.id)})`
                            : ""}
                        </span>
                      ))}
                      <span>
                        <i className="proof-map__legend-node proof-map__legend-node--selected" />
                        Selected
                      </span>
                      <span>
                        <i className="proof-map__legend-node proof-map__legend-node--related" />
                        Directly related
                      </span>
                    </div>
                  </details>

                  {resultNodes.length === 0 ? (
                    <div className="proof-map__graph-empty" role="status">
                      <p>No proof nodes match these filters.</p>
                      <button type="button" onClick={resetFilters}>
                        Reset filters
                      </button>
                    </div>
                  ) : null}
                </>
              ) : null}
            </div>
          </div>

          {!compact ? (
            <section
              className="proof-map__list-alternative"
              id={listPanelId}
              role="tabpanel"
              aria-labelledby={`${markerPrefix}-list-tab`}
              hidden={viewMode !== "list"}
            >
              <header className="proof-map__list-heading">
                <div>
                  <h2 id={`${markerPrefix}-list-heading`}>Atlas nodes</h2>
                  <p>
                    {resultNodes.length} of {data.nodes.length} nodes match the current filters.
                  </p>
                </div>
              </header>
              {resultNodes.length ? (
                <div className="proof-map__list-clusters">
                  {data.clusters.map((cluster) => {
                    const nodes = resultNodes.filter(
                      (node) => node.clusterId === cluster.id,
                    );
                    if (!nodes.length) return null;
                    return (
                      <section key={cluster.id}>
                        <h3>{cluster.title}</h3>
                        <p>{cluster.summary}</p>
                        <ul>
                          {nodes.map((node) => (
                            <li key={node.id}>
                              <button
                                type="button"
                                className={classNames(
                                  "proof-map__list-node",
                                  selectedNodeId === node.id && "is-selected",
                                )}
                                aria-pressed={selectedNodeId === node.id}
                                onClick={() => inspectNode(node.id)}
                              >
                                <span>{node.title}</span>
                                <span>
                                  {statusLabels[node.status]} · {titleCase(node.track)}
                                </span>
                                <span>{node.summary}</span>
                              </button>
                            </li>
                          ))}
                        </ul>
                      </section>
                    );
                  })}
                </div>
              ) : (
                <div className="proof-map__empty-results">
                  <p>No proof nodes match these filters.</p>
                  <button type="button" onClick={resetFilters}>
                    Reset filters
                  </button>
                </div>
              )}
            </section>
          ) : null}
        </div>

        {!compact && selectedNode ? (
          <aside
            ref={inspectorRef}
            className="proof-map__inspector"
            aria-label="Proof node details"
            aria-live="polite"
            aria-atomic="false"
          >
            <div
              className="proof-map__inspector-content"
              data-node-id={selectedNode.id}
              data-filtered-out={!nodeMatches.get(selectedNode.id) || undefined}
            >
              <div className="proof-map__inspector-heading">
                <div>
                  <p className="proof-map__eyebrow">
                    Proof node · {statusLabels[selectedNode.status]}
                  </p>
                  <h2>{selectedNode.title}</h2>
                </div>
                <button
                  type="button"
                  aria-label="Close proof node details"
                  onClick={() => inspectNode(selectedNode.id)}
                >
                  ×
                </button>
              </div>

              {!nodeMatches.get(selectedNode.id) ? (
                <p className="proof-map__filter-notice">
                  This pinned node is outside the current filters. Its details remain available.
                </p>
              ) : null}

              <dl className="proof-map__inspector-facts">
                <div>
                  <dt>Proof status</dt>
                  <dd>{statusLabels[selectedNode.status]}</dd>
                </div>
                <div>
                  <dt>Work stream</dt>
                  <dd>{titleCase(selectedNode.track)}</dd>
                </div>
                <div>
                  <dt>Repositories</dt>
                  <dd>
                    {selectedNode.repoIds
                      .map(
                        (repoId) =>
                          repositoryById.get(repoId)?.shortName ?? repoId,
                      )
                      .join(", ")}
                  </dd>
                </div>
              </dl>

              <section className="proof-map__inspector-section proof-map__claim">
                <h3>Exact claim</h3>
                <p className="proof-map__inspector-summary">
                  {selectedNode.summary}
                </p>
                <p>{selectedNode.detail}</p>
                <ul>
                  {selectedNode.established.map((claim) => (
                    <li key={claim}>{claim}</li>
                  ))}
                </ul>
              </section>

              {selectedNode.metrics?.length ? (
                <dl className="proof-map__metrics" aria-label="Claim metrics">
                  {selectedNode.metrics.map((metric) => (
                    <div key={metric.label}>
                      <dt>{metric.label}</dt>
                      <dd>{metric.value}</dd>
                      {metric.detail ? <dd>{metric.detail}</dd> : null}
                    </div>
                  ))}
                </dl>
              ) : null}

              <section className="proof-map__inspector-section proof-map__evidence">
                <h3>Supporting evidence</h3>
                <ul>
                  {selectedEvidence.map((item) => {
                    const href = item.url ?? item.publicFallbackUrl;
                    return (
                      <li key={item.id}>
                        <p>
                          {href ? (
                            <a href={href} target="_blank" rel="noreferrer">
                              {item.label}
                            </a>
                          ) : (
                            <strong>{item.label}</strong>
                          )}
                          <span
                            className={`proof-map__publication proof-map__publication--${item.publication}`}
                          >
                            {titleCase(item.publication)}
                          </span>
                        </p>
                        <p>{item.description}</p>
                      </li>
                    );
                  })}
                </ul>
              </section>

              <section className="proof-map__inspector-section proof-map__relationships">
                <h3>Relationships</h3>
                {selectedIncomingEdges.length || selectedOutgoingEdges.length ? (
                  <div className="proof-map__relationship-groups">
                    {selectedIncomingEdges.length ? (
                      <div>
                        <h4>Incoming</h4>
                        <ul>
                          {selectedIncomingEdges.map((edge) => {
                            const source = nodeById.get(edge.from);
                            if (!source) return null;
                            return (
                              <li key={edge.id}>
                                <button type="button" onClick={() => inspectNode(source.id)}>
                                  <span>{source.title}</span>
                                  <small>
                                    {titleCase(edge.relation)} · {edge.label}
                                  </small>
                                </button>
                              </li>
                            );
                          })}
                        </ul>
                      </div>
                    ) : null}
                    {selectedOutgoingEdges.length ? (
                      <div>
                        <h4>Outgoing</h4>
                        <ul>
                          {selectedOutgoingEdges.map((edge) => {
                            const target = nodeById.get(edge.to);
                            if (!target) return null;
                            return (
                              <li key={edge.id}>
                                <button type="button" onClick={() => inspectNode(target.id)}>
                                  <span>{target.title}</span>
                                  <small>
                                    {titleCase(edge.relation)} · {edge.label}
                                  </small>
                                </button>
                              </li>
                            );
                          })}
                        </ul>
                      </div>
                    ) : null}
                  </div>
                ) : (
                  <p>No direct relationships are recorded for this node.</p>
                )}
              </section>

              <section className="proof-map__inspector-section proof-map__remaining-boundary">
                <h3>Remaining assumptions or trust boundary</h3>
                {selectedNode.carried.length ? (
                  <ul>
                    {selectedNode.carried.map((claim) => (
                      <li key={claim}>{claim}</li>
                    ))}
                  </ul>
                ) : (
                  <p>No additional carried assumption is recorded.</p>
                )}
              </section>

              <section className="proof-map__inspector-section proof-map__provenance">
                <h3>Source provenance</h3>
                {selectedEvidence.some((item) => item.anchor) ? (
                  <ul>
                    {selectedEvidence.map((item) =>
                      item.anchor ? (
                        <li key={item.id}>
                          <strong>{item.label}</strong>
                          <dl>
                            <div>
                              <dt>Repository</dt>
                              <dd>
                                {repositoryById.get(item.repoId)?.shortName ??
                                  item.repoId}
                              </dd>
                            </div>
                            <div>
                              <dt>File</dt>
                              <dd>
                                <code>
                                  {item.anchor.path}
                                  {item.anchor.line ? `:${item.anchor.line}` : ""}
                                </code>
                              </dd>
                            </div>
                            {item.anchor.symbol ? (
                              <div>
                                <dt>Symbol</dt>
                                <dd>
                                  <code>{item.anchor.symbol}</code>
                                </dd>
                              </div>
                            ) : null}
                          </dl>
                        </li>
                      ) : null,
                    )}
                  </ul>
                ) : (
                  <p>No exact source anchor is recorded for this node.</p>
                )}
              </section>

              <nav className="proof-map__inspector-section proof-map__cross-links" aria-label="Open this claim elsewhere">
                <h3>Explore further</h3>
                <ul>
                  {selectedNode.stageIds.map((stageId) => {
                    const stage = data.stages.find((item) => item.id === stageId);
                    return stage ? (
                      <li key={stage.id}>
                        <a href={`./#stage=${encodeURIComponent(stage.id)}`}>
                          <span>{stage.title}</span>
                          <small>Journey · Stage {stage.ordinal}</small>
                        </a>
                      </li>
                    ) : null;
                  })}
                  <li>
                    <a href="./circuit.html">
                      <span>Open Circuit Explorer</span>
                      <small>Implementation structure and source mappings</small>
                    </a>
                  </li>
                </ul>
              </nav>
            </div>
          </aside>
        ) : null}
      </div>
    </section>
  );
}

export default ProofMap;
