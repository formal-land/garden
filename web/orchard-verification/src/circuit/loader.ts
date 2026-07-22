import {
  CIRCUIT_EXPLORER_SCHEMA,
  type CircuitComponent,
  type CircuitConstraint,
  type CircuitDiagnostic,
  type CircuitExplorerData,
  type CircuitFlowEdge,
  type CircuitFlowNode,
  type CircuitGate,
  type CircuitLookup,
  type CircuitMetric,
  type CircuitNamespace,
  type CircuitRegionOperation,
  type CircuitRegionGroup,
  type CircuitRegionOccurrence,
  type CircuitSource,
  type CircuitSourceConfidence,
  type CircuitSourceResolutionCandidate,
} from "./model";

type JsonRecord = Record<string, unknown>;

const DATA_FILE = "data/orchard-circuit-highlevel.v1.json";
let cachedLoad: Promise<CircuitExplorerData> | null = null;

function record(value: unknown): JsonRecord {
  return value !== null && typeof value === "object" && !Array.isArray(value)
    ? value as JsonRecord
    : {};
}

function array(value: unknown): unknown[] {
  return Array.isArray(value) ? value : [];
}

function pick(target: JsonRecord, ...keys: readonly string[]): unknown {
  for (const key of keys) {
    if (target[key] !== undefined) return target[key];
  }
  return undefined;
}

function text(target: JsonRecord, keys: readonly string[], fallback = ""): string {
  const value = pick(target, ...keys);
  return typeof value === "string" || typeof value === "number"
    ? String(value)
    : fallback;
}

function numberValue(
  target: JsonRecord,
  keys: readonly string[],
  fallback = 0,
): number {
  const value = pick(target, ...keys);
  const parsed = typeof value === "number" ? value : Number(value);
  return Number.isFinite(parsed) ? parsed : fallback;
}

function optionalNumber(target: JsonRecord, keys: readonly string[]): number | undefined {
  const value = pick(target, ...keys);
  if (value === undefined || value === null || value === "") return undefined;
  const parsed = typeof value === "number" ? value : Number(value);
  return Number.isFinite(parsed) ? parsed : undefined;
}

function stringList(value: unknown): string[] {
  return array(value)
    .map((item) => {
      if (typeof item === "string" || typeof item === "number") return String(item);
      const itemRecord = record(item);
      return text(itemRecord, ["id", "name", "label"]);
    })
    .filter(Boolean);
}

function titleCase(value: string): string {
  return value
    .replace(/([a-z0-9])([A-Z])/g, "$1 $2")
    .replace(/[_-]+/g, " ")
    .replace(/\b\w/g, (letter) => letter.toUpperCase());
}

function slug(value: string): string {
  return value
    .toLocaleLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-|-$/g, "") || "item";
}

function normalizeMetrics(value: unknown, prefix: string): CircuitMetric[] {
  if (Array.isArray(value)) {
    return value.map((raw, index) => {
      const item = record(raw);
      const label = text(item, ["label", "name", "id"], `Metric ${index + 1}`);
      return {
        id: text(item, ["id"], `${prefix}-${slug(label)}`),
        label,
        value: text(item, ["value", "count", "total"], "0"),
        detail: text(item, ["detail", "description"]) || undefined,
      };
    });
  }
  const valueRecord = record(value);
  return Object.entries(valueRecord).flatMap(([id, raw]) => {
    if (raw === null || raw === undefined) return [];
    if (typeof raw !== "object") {
      return [{ id: `${prefix}-${slug(id)}`, label: titleCase(id), value: String(raw) }];
    }
    const nested = record(raw);
    const min = optionalNumber(nested, ["min", "start"]);
    const max = optionalNumber(nested, ["max", "end"]);
    if (min !== undefined || max !== undefined) {
      return [{
        id: `${prefix}-${slug(id)}`,
        label: titleCase(id),
        value: min === max ? String(min ?? max) : `${min ?? "?"}–${max ?? "?"}`,
      }];
    }
    const explicit = pick(nested, "value", "count", "total");
    if (explicit !== undefined) {
      return [{
        id: `${prefix}-${slug(id)}`,
        label: titleCase(id),
        value: String(explicit),
        detail: text(nested, ["detail", "description"]) || undefined,
      }];
    }
    const scalarEntries = Object.entries(nested).filter(([, nestedValue]) =>
      typeof nestedValue === "string" || typeof nestedValue === "number"
    );
    if (!scalarEntries.length) return [];
    const numericTotal = scalarEntries.reduce(
      (total, [, nestedValue]) => total + (Number(nestedValue) || 0),
      0,
    );
    return [{
      id: `${prefix}-${slug(id)}`,
      label: titleCase(id),
      value: String(numericTotal),
      detail: scalarEntries.map(([key, nestedValue]) => `${titleCase(key)} ${nestedValue}`).join(" · "),
    }];
  });
}

function listFromSection(section: JsonRecord, ...keys: readonly string[]): unknown[] {
  const value = pick(section, ...keys);
  if (Array.isArray(value)) return value;
  const valueRecord = record(value);
  return Object.entries(valueRecord).map(([id, item]) => ({
    id,
    ...record(item),
  }));
}

function formatExpression(value: unknown): string {
  if (typeof value === "string" || typeof value === "number") return String(value);
  if (Array.isArray(value)) return value.map(formatExpression).join(", ");
  const node = record(value);
  const tag = text(node, ["tag", "kind", "type"]);
  const args = array(pick(node, "args", "children", "terms"));
  switch (tag) {
    case "Advice":
    case "Fixed":
    case "Instance":
    case "Instance_":
      return `${text(node, ["column_name"], `${tag.toLocaleLowerCase()}[${text(node, ["column", "index"], "?")}]`)}@${text(node, ["rotation", "row"], "0")}`;
    case "Selector":
      return text(node, ["selector_name"], `selector[${text(node, ["selector", "index"], "?")}]`);
    case "Constant":
      return text(node, ["value"], "0");
    case "Negated":
      return `−(${formatExpression(pick(node, "expr", "value", "child"))})`;
    case "Scaled":
      return `${text(node, ["scale"], "?")} · (${formatExpression(pick(node, "expr", "value", "child"))})`;
    case "Sum":
      return `(${args.map(formatExpression).join(" + ")})`;
    case "Product":
      return `(${args.map(formatExpression).join(" · ")})`;
    case "Select":
      return `${text(node, ["selector_name"], `selector[${text(node, ["selector"], "?")}]`)} · (${formatExpression(pick(node, "constraint", "expression", "expr"))})`;
    case "Equal":
      return `(${formatExpression(node.left)}) = (${formatExpression(node.right)})`;
    case "Either":
      return `(${formatExpression(node.left)}) ∨ (${formatExpression(node.right)})`;
    case "EqualZeroToPrecise":
      return `(${formatExpression(pick(node, "expression", "expr", "value"))}) = 0`;
    case "Boolean":
      return `${formatExpression(pick(node, "expression", "expr", "value"))} ∈ {0, 1}`;
    case "Range": {
      const expression = formatExpression(pick(node, "expression", "expr", "value"));
      const upperBound = text(node, ["range", "upper", "bound"]);
      return upperBound ? `0 ≤ ${expression} < ${upperBound}` : `range(${expression})`;
    }
    default: {
      const rendered = text(node, ["expression", "text", "display"]);
      if (rendered) return rendered;
      try {
        return JSON.stringify(value);
      } catch {
        return "Expression unavailable";
      }
    }
  }
}

function expressionReferences(value: unknown): { columns: string[]; rotations: number[] } {
  const columns = new Set<string>();
  const rotations = new Set<number>();
  const visit = (candidate: unknown): void => {
    if (Array.isArray(candidate)) {
      candidate.forEach(visit);
      return;
    }
    if (candidate === null || typeof candidate !== "object") return;
    const node = record(candidate);
    const tag = text(node, ["tag", "kind", "type"]);
    if (tag === "Advice" || tag === "Fixed" || tag === "Instance" || tag === "Instance_") {
      const column = text(
        node,
        ["column_name"],
        `${tag}[${text(node, ["column", "index"], "?")}]`,
      );
      if (column) columns.add(column);
      const rotation = optionalNumber(node, ["rotation", "row"]);
      if (rotation !== undefined) rotations.add(rotation);
    }
    Object.values(node).forEach(visit);
  };
  visit(value);
  return { columns: [...columns], rotations: [...rotations].sort((a, b) => a - b) };
}

function sourceConfidence(value: unknown): CircuitSourceConfidence | undefined {
  if (value === "exact" || value === "mapped" || value === "ambiguous" || value === "unresolved") {
    return value;
  }
  if (value === "derived") return "mapped";
  if (value === "candidate") return "ambiguous";
  return undefined;
}

function sourceResolution(item: JsonRecord): {
  sourceIds: string[];
  sourceConfidence?: CircuitSourceConfidence;
  sourceCandidateIds: string[];
  sourceCandidates: CircuitSourceResolutionCandidate[];
} {
  const mapping = record(pick(item, "source", "sourceResolution", "source_resolution"));
  const candidates = array(pick(mapping, "candidates", "sourceCandidates", "source_candidates"))
    .flatMap((rawCandidate): CircuitSourceResolutionCandidate[] => {
      const candidate = record(rawCandidate);
      const sourceId = text(candidate, ["sourceId", "source_id", "id"]);
      if (!sourceId) return [];
      return [{
        sourceId,
        confidence: sourceConfidence(pick(candidate, "confidence")) ?? "ambiguous",
        reason: text(candidate, ["reason", "description"]) || undefined,
      }];
    });
  const directSourceIds = stringList(pick(item, "sourceIds", "source_ids", "sources"));
  const primarySourceId = text(mapping, ["primarySourceId", "primary_source_id"]);
  const sourceIds = directSourceIds.length
    ? directSourceIds
    : primarySourceId
      ? [primarySourceId]
      : [];
  return {
    sourceIds,
    sourceConfidence: sourceConfidence(pick(mapping, "confidence")) ??
      sourceConfidence(pick(item, "sourceConfidence", "source_confidence")),
    sourceCandidateIds: candidates.map(({ sourceId }) => sourceId),
    sourceCandidates: candidates,
  };
}

function normalizeSources(raw: unknown): CircuitSource[] {
  const section = record(raw);
  const records = pick(section, "records", "items", "sources");
  const selected = records ?? raw;
  const items = Array.isArray(selected)
    ? selected
    : Object.entries(record(selected)).map(([id, item]) => ({ id, ...record(item) }));
  return items.map((rawItem, index) => {
    const item = record(rawItem);
    const path = text(item, ["path", "file", "source_path"]);
    const rawConfidence = text(item, ["confidence", "source_confidence"]);
    const candidates = array(pick(item, "candidates", "source_candidates")).map((rawCandidate) => {
      const candidate = record(rawCandidate);
      return {
        label: text(candidate, ["label", "title", "symbol", "path"], "Source candidate"),
        path: text(candidate, ["path", "file", "source_path"]),
        symbol: text(candidate, ["symbol", "definition"]) || undefined,
        line: optionalNumber(candidate, ["line", "line_start"]),
        confidence: text(candidate, ["confidence", "reason"]) || undefined,
      };
    });
    return {
      id: text(item, ["id", "source_id"], `source:${index}`),
      label: text(item, ["label", "title", "symbol"], path || `Source ${index + 1}`),
      path,
      symbol: text(item, ["symbol", "definition"]) || undefined,
      line: optionalNumber(item, ["line", "line_start"]),
      url: text(item, ["url", "href", "github_url"]) || undefined,
      repository: text(item, ["repository", "repo"]) || undefined,
      revision: text(item, ["revision", "ref", "commit"]) || undefined,
      confidence: sourceConfidence(rawConfidence) ??
        (text(item, ["verification"]).includes("path-map") ? "mapped" : "exact"),
      candidates,
    };
  });
}

function flowKind(value: string): CircuitFlowNode["kind"] {
  if (value === "input" || value === "output" || value === "check") return value;
  if (value === "public-input") return "input";
  if (value === "instance") return "output";
  if (value === "instance-flag") return "input";
  return "component";
}

function normalizeFlowNodes(section: JsonRecord): CircuitFlowNode[] {
  return listFromSection(section, "nodes", "items").map((raw, index) => {
    const item = record(raw);
    const id = text(item, ["id", "node_id"], `flow:${index}`);
    const title = text(item, ["title", "label", "name"], id);
    const position = record(pick(item, "position", "point", "layout"));
    const x = optionalNumber(position, ["x"]) ?? optionalNumber(item, ["x"]);
    const y = optionalNumber(position, ["y"]) ?? optionalNumber(item, ["y"]);
    return {
      id,
      kind: flowKind(text(item, ["kind", "type", "category"])),
      title,
      shortTitle: text(item, ["shortTitle", "short_title", "short", "label"], title),
      summary: text(item, ["summary", "description", "detail"]),
      componentId: text(item, ["componentId", "component_id", "component"]) || undefined,
      regionIds: stringList(pick(item, "regionIds", "region_ids", "regions")),
      gateIds: stringList(pick(item, "gateIds", "gate_ids", "gates")),
      lookupIds: stringList(pick(item, "lookupIds", "lookup_ids", "lookups")),
      operationIds: stringList(pick(item, "layoutOperationIds", "layout_operation_ids", "operationIds", "operation_ids")),
      instanceRowIds: stringList(pick(item, "instanceRowIds", "instance_row_ids")),
      sourceIds: stringList(pick(item, "sourceIds", "source_ids", "sources")),
      proofNodeIds: stringList(pick(item, "proofNodeIds", "proof_node_ids", "proof_nodes")),
      position: x !== undefined && y !== undefined ? { x, y } : undefined,
      metrics: normalizeMetrics(pick(item, "metrics", "counts"), `${id}-metric`),
      tags: stringList(pick(item, "tags", "keywords", "searchTerms", "search_terms")),
    };
  });
}

function normalizeFlowEdges(section: JsonRecord): CircuitFlowEdge[] {
  return listFromSection(section, "edges", "links").map((raw, index) => {
    const item = record(raw);
    const from = text(item, ["from", "source", "from_id"]);
    const to = text(item, ["to", "target", "to_id"]);
    const rawKind = text(item, ["kind", "type", "relation"]);
    return {
      id: text(item, ["id", "edge_id"], `edge:${index}:${from}:${to}`),
      from,
      to,
      label: text(item, ["label", "title", "relation"]) || undefined,
      summary: text(item, ["summary", "description"]),
      kind: rawKind === "constraint" || rawKind === "public" ? rawKind : "data",
    };
  });
}

function normalizeComponents(section: JsonRecord, flow: JsonRecord): CircuitComponent[] {
  const rawComponents = listFromSection(section, "components", "component_groups");
  const instanceRowsById = new Map(
    listFromSection(section, "instanceRows", "instance_rows").map((raw, index) => {
      const item = record(raw);
      return [text(item, ["id"], `instance-row:${index}`), item] as const;
    }),
  );
  const source = rawComponents.length
    ? rawComponents
    : listFromSection(flow, "nodes", "items").filter((raw) => {
        const item = record(raw);
        return [
          "regionIds", "region_ids", "gateIds", "gate_ids", "lookupIds", "lookup_ids",
          "layoutOperationIds", "layout_operation_ids", "operationIds", "operation_ids",
          "instanceRowIds", "instance_row_ids",
        ]
          .some((key) => array(item[key]).length > 0);
      });
  return source.map((raw, index) => {
    const item = record(raw);
    const id = text(item, ["id", "component_id"], `component:${index}`);
    const title = text(item, ["title", "label", "name"], id);
    const resolution = sourceResolution(item);
    const instanceRowIds = stringList(pick(item, "instanceRowIds", "instance_row_ids"));
    const directOperationIds = stringList(
      pick(item, "layoutOperationIds", "layout_operation_ids", "operationIds", "operation_ids"),
    );
    const instanceOperationIds = instanceRowIds.flatMap((instanceRowId) =>
      stringList(pick(instanceRowsById.get(instanceRowId) ?? {}, "operationIds", "operation_ids"))
    );
    return {
      id,
      title,
      shortTitle: text(item, ["shortTitle", "short_title", "short", "label"], title),
      summary: text(item, ["summary", "description"]),
      detail: text(item, ["detail", "description", "summary"]),
      regionIds: stringList(pick(item, "regionIds", "region_ids", "regions")),
      gateIds: stringList(pick(item, "gateIds", "gate_ids", "gates")),
      lookupIds: stringList(pick(item, "lookupIds", "lookup_ids", "lookups")),
      operationIds: [...new Set([...directOperationIds, ...instanceOperationIds])],
      instanceRowIds,
      ...resolution,
      proofNodeIds: stringList(pick(item, "proofNodeIds", "proof_node_ids", "proof_nodes")),
      metrics: normalizeMetrics(pick(item, "metrics", "counts", "summary_metrics"), `${id}-metric`),
      tags: stringList(pick(item, "tags", "keywords", "searchTerms", "search_terms")),
    };
  });
}

function normalizeRegions(section: JsonRecord): CircuitRegionGroup[] {
  return listFromSection(section, "regionGroups", "region_groups", "groups").map((raw, index) => {
    const item = record(raw);
    const metricRecord = record(pick(item, "metrics", "counts"));
    const operationCounts = record(pick(metricRecord, "operationCounts", "operation_counts"));
    const rows = record(pick(metricRecord, "rowRange", "row_range", "rows") ?? pick(item, "rows", "row_range"));
    const id = text(item, ["id", "region_id", "group_id"], `region-group:${index}`);
    const count = numberValue(item, ["count", "occurrenceCount", "occurrence_count", "instances"], 1);
    const resolution = sourceResolution(item);
    return {
      id,
      componentId: text(item, ["componentId", "component_id", "component"]),
      title: text(item, ["title", "label", "name"], id),
      semanticId: text(item, ["semanticId", "semantic_id", "region_constructor"]) || undefined,
      summary: text(item, ["summary", "description"]),
      namespacePath: stringList(pick(item, "namespacePath", "namespace_path", "namespace", "namespaces")),
      occurrenceIds: stringList(pick(item, "occurrenceIds", "occurrence_ids", "regionIds", "region_ids", "occurrences", "instances")),
      gateIds: stringList(pick(item, "gateIds", "gate_ids", "gates")),
      ...resolution,
      metrics: normalizeMetrics(pick(item, "metrics", "counts"), `${id}-metric`),
      count,
      eventCount: numberValue(metricRecord, ["operationCount", "operation_count"], numberValue(item, ["eventCount", "event_count", "events"])),
      selectorCount: numberValue(operationCounts, ["enable_selector", "enableSelector"], numberValue(item, ["selectorCount", "selector_count", "selectors"])),
      copyCount: numberValue(operationCounts, ["copy"], numberValue(item, ["copyCount", "copy_count", "copies"])),
      rowStart: optionalNumber(rows, ["start", "min"]) ?? optionalNumber(item, ["rowStart", "row_start"]),
      rowEnd: optionalNumber(rows, ["end", "max"]) ?? optionalNumber(item, ["rowEnd", "row_end"]),
      searchTerms: stringList(pick(item, "searchTerms", "search_terms", "keywords", "tags")),
    };
  });
}

function normalizeOccurrences(section: JsonRecord): CircuitRegionOccurrence[] {
  return listFromSection(section, "occurrences", "region_occurrences", "instances", "regions").map((raw, index) => {
    const item = record(raw);
    const metricRecord = record(pick(item, "metrics", "counts"));
    const operationCounts = record(pick(metricRecord, "operationCounts", "operation_counts"));
    const rows = record(pick(metricRecord, "rowRange", "row_range", "rows") ?? pick(item, "rows", "row_range"));
    const id = text(item, ["id", "occurrence_id", "region_id"], `region:${index}`);
    const resolution = sourceResolution(item);
    return {
      id,
      groupId: text(item, ["groupId", "group_id", "region_group_id"]),
      componentId: text(item, ["componentId", "component_id", "component"]),
      title: text(item, ["title", "label", "name"], id),
      semanticId: text(item, ["semanticId", "semantic_id", "region_constructor"]) || undefined,
      index: numberValue(item, ["index", "occurrence_index", "region_index"], index),
      namespacePath: stringList(pick(item, "namespacePath", "namespace_path", "namespace", "namespaces")),
      ...resolution,
      operationIds: stringList(pick(item, "operationIds", "operation_ids")).length
        ? stringList(pick(item, "operationIds", "operation_ids"))
        : array(pick(item, "operations", "ops")).map((operation, operationIndex) =>
            text(record(operation), ["id", "operation_id"], `operation:${id}:${operationIndex}`)
          ),
      metrics: normalizeMetrics(pick(item, "metrics", "counts"), `${id}-metric`),
      eventCount: numberValue(metricRecord, ["operationCount", "operation_count"], numberValue(item, ["eventCount", "event_count", "events"])),
      selectorCount: numberValue(operationCounts, ["enable_selector", "enableSelector"], numberValue(item, ["selectorCount", "selector_count", "selectors"])),
      copyCount: numberValue(operationCounts, ["copy"], numberValue(item, ["copyCount", "copy_count", "copies"])),
      rowStart: optionalNumber(rows, ["start", "min"]) ?? optionalNumber(item, ["rowStart", "row_start", "startRow", "start_row", "absolute_row_start"]),
      rowEnd: optionalNumber(rows, ["end", "max"]) ?? optionalNumber(item, ["rowEnd", "row_end", "absolute_row_end"]),
      searchTerms: stringList(pick(item, "searchTerms", "search_terms", "keywords", "tags")),
    };
  });
}

function normalizeNamespaces(section: JsonRecord): CircuitNamespace[] {
  return listFromSection(section, "namespaces", "namespace_nodes").map((raw, index) => {
    const item = record(raw);
    const id = text(item, ["id", "namespace_id"], `namespace:${index}`);
    return {
      id,
      title: text(item, ["title", "label", "name"], id),
      parentId: text(item, ["parentId", "parent_id", "parent"]) || undefined,
      componentId: text(item, ["componentId", "component_id", "component"]) || undefined,
      childIds: stringList(pick(item, "childIds", "child_ids", "children")),
      regionIds: stringList(pick(item, "regionIds", "region_ids", "regions")).length
        ? stringList(pick(item, "regionIds", "region_ids", "regions"))
        : stringList(pick(item, "childIds", "child_ids", "children")).filter((childId) => childId.startsWith("region:")),
      path: stringList(pick(item, "path", "namespacePath", "namespace_path", "namespace")),
      sourceIds: stringList(pick(item, "sourceIds", "source_ids", "sources")),
    };
  });
}

function operationKind(value: string): CircuitRegionOperation["kind"] {
  const normalized = value.replace(/[_\s]+/g, "-").toLocaleLowerCase();
  if (normalized === "enableselector" || normalized === "enable-selector") return "enable-selector";
  if (normalized === "assignfixed" || normalized === "assign-fixed") return "assign-fixed";
  if (normalized === "copy") return "copy";
  if (normalized === "constrainconstant" || normalized === "constrain-constant") return "constrain-constant";
  if (normalized === "constraininstance" || normalized === "constrain-instance") return "constrain-instance";
  if (normalized === "initlookuptables" || normalized === "init-lookup-tables") return "init-lookup-tables";
  return "other";
}

function normalizeCell(raw: unknown, fallbackId: string) {
  const item = record(raw);
  const column = record(item.column);
  const rawKind = text(item, ["kind", "column_kind"], text(column, ["kind", "type"])).toLocaleLowerCase();
  const normalizedKind = rawKind === "instance_" ? "instance" : rawKind;
  const kind = normalizedKind === "advice" || normalizedKind === "fixed" || normalizedKind === "instance" || normalizedKind === "lookup"
    ? normalizedKind
    : rawKind === "lookup-table" || rawKind === "lookup_table"
      ? "lookup"
      : "unknown";
  const columnId = text(
    item,
    ["column_name", "column_id"],
    text(column, ["name", "id", "index"], typeof item.column === "string" ? item.column : ""),
  );
  const rawRegionId = text(item, ["regionId", "region_id", "region"]);
  const regionIndex = optionalNumber(item, ["regionIndex", "region_index"]);
  const regionId = rawRegionId || (regionIndex !== undefined ? `region:${regionIndex}` : "");
  const relativeOffset = optionalNumber(item, ["relativeOffset", "relative_offset", "offset"]);
  const absoluteRow = optionalNumber(item, ["absoluteRow", "absolute_row", "row"]);
  const id = text(item, ["id", "cell_id"], fallbackId);
  return {
    id,
    kind,
    column: columnId || undefined,
    regionId: regionId || undefined,
    relativeOffset,
    absoluteRow,
    label: text(item, ["label", "name"], [kind, columnId && `[${columnId}]`, absoluteRow !== undefined && `row ${absoluteRow}`].filter(Boolean).join(" ")),
  } as const;
}

function normalizeOperations(section: JsonRecord): CircuitRegionOperation[] {
  const direct = listFromSection(section, "operations", "region_operations");
  const occurrences = listFromSection(section, "occurrences", "region_occurrences", "instances", "regions");
  const nested = occurrences.flatMap((rawOccurrence, occurrenceIndex) => {
    const occurrence = record(rawOccurrence);
    const occurrenceId = text(occurrence, ["id", "occurrence_id", "region_id"], `region:${occurrenceIndex}`);
    return array(pick(occurrence, "operations", "ops")).map((rawOperation, operationIndex) => ({
      ...record(rawOperation),
      occurrence_id: occurrenceId,
      id: text(record(rawOperation), ["id", "operation_id"], `operation:${occurrenceId}:${operationIndex}`),
    }));
  });
  return (direct.length ? direct : nested).map((raw, index) => {
    const item = record(raw);
    const id = text(item, ["id", "operation_id"], `operation:${index}`);
    const kind = operationKind(text(item, ["kind", "tag", "type"]));
    const rawCells = array(pick(item, "cells", "cell_refs"));
    const namedCells = ["cell", "left", "right", "lhs", "rhs", "target", "source"]
      .flatMap((key) => item[key] === undefined ? [] : [item[key]]);
    const cells = (rawCells.length ? rawCells : namedCells).map((cell, cellIndex) =>
      normalizeCell(cell, `cell:${id}:${cellIndex}`)
    );
    const instanceCellId = text(item, ["instance_cell_id", "instanceCellId"]);
    if (kind === "constrain-instance" && instanceCellId) {
      cells.push(normalizeCell({
        id: instanceCellId,
        kind: "Instance_",
        column: {
          kind: "Instance_",
          index: pick(item, "instance_column", "instanceColumn"),
          name: pick(item, "instance_column_name", "instanceColumnName"),
        },
        offset: pick(item, "row", "instance_row", "instanceRow"),
        absolute_row: pick(item, "row", "instance_row", "instanceRow"),
      }, `cell:${id}:instance`));
    }
    const explicitRegionId = text(item, ["regionId", "region_id", "region"]);
    const regionId = explicitRegionId;
    const lookupEntries = array(pick(item, "entries", "lookupEntries", "lookup_entries"))
      .map((rawEntry, entryIndex) => {
        const entry = record(rawEntry);
        return {
          id: text(entry, ["id"], `lookup-entry:${id}:${entryIndex}`),
          column: text(entry, ["column", "column_id"]) || undefined,
          columnName: text(entry, ["columnName", "column_name", "name"]) || undefined,
          annotation: text(entry, ["annotation", "label"]) || undefined,
          valueCount: optionalNumber(entry, ["valueCount", "value_count", "count"]),
          defaultValue: text(entry, ["defaultValue", "default_value", "default"]) || undefined,
        };
      });
    const resolution = sourceResolution(item);
    return {
      id,
      componentId: text(item, ["componentId", "component_id", "component"]) || undefined,
      occurrenceId: text(item, ["occurrenceId", "occurrence_id"]) || regionId || undefined,
      regionId: regionId || undefined,
      kind,
      title: text(item, ["title", "label", "name"], titleCase(kind)),
      annotation: text(item, ["annotation", "description"]) || undefined,
      selectorId: text(item, ["selectorId", "selector_id", "selector", "selectorName", "selector_name"]) || undefined,
      selectorName: text(item, ["selectorName", "selector_name"]) || undefined,
      relativeOffset: optionalNumber(item, ["relativeOffset", "relative_offset", "offset"]),
      absoluteRow: optionalNumber(item, ["absoluteRow", "absolute_row", "row"]),
      cells,
      value: text(item, ["value", "constant"]) || undefined,
      lookupEntries,
      ...resolution,
    };
  });
}

function normalizeConstraints(configure: JsonRecord, rawGates: readonly unknown[]): CircuitConstraint[] {
  const direct = listFromSection(configure, "constraints", "constraint_items");
  const nested = rawGates.flatMap((gate, gateIndex) => {
    const gateRecord = record(gate);
    const gateId = text(gateRecord, ["id", "gate_id"], `gate:${gateIndex}`);
    return array(pick(gateRecord, "constraints", "constraint_items")).map((constraint) => ({
      ...record(constraint),
      gate_id: gateId,
    }));
  });
  return (direct.length ? direct : nested).map((raw, index) => {
    const item = record(raw);
    const gateId = text(item, ["gateId", "gate_id", "gate"]);
    const expression = pick(item, "expression", "constraint", "ast", "text");
    const references = expressionReferences(expression);
    const resolution = sourceResolution(item);
    return {
      id: text(item, ["id", "constraint_id"], `constraint:${gateId}:${index}`),
      gateId,
      title: text(item, ["title", "label", "name"], `Constraint ${index + 1}`),
      expression: formatExpression(expression),
      expressionAst: expression !== undefined ? expression : undefined,
      columns: stringList(pick(item, "columns", "column_ids")).length
        ? stringList(pick(item, "columns", "column_ids"))
        : references.columns,
      rotations: array(pick(item, "rotations", "rotation_offsets")).length
        ? array(pick(item, "rotations", "rotation_offsets")).map(Number).filter(Number.isFinite)
        : references.rotations,
      ...resolution,
    };
  });
}

function normalizeGates(configure: JsonRecord): CircuitGate[] {
  return listFromSection(configure, "gates", "gate_groups").map((raw, index) => {
    const item = record(raw);
    const id = text(item, ["id", "gate_id"], `gate:${index}`);
    const nestedIds = array(pick(item, "constraints", "constraint_items")).map((constraint, constraintIndex) =>
      text(record(constraint), ["id", "constraint_id"], `constraint:${id}:${constraintIndex}`)
    );
    const componentIds = stringList(pick(item, "componentIds", "component_ids", "components"));
    const resolution = sourceResolution(item);
    return {
      id,
      componentId: text(item, ["componentId", "component_id", "component"]) ||
        (componentIds.length === 1 ? componentIds[0] : undefined),
      componentIds,
      title: text(item, ["title", "label", "name"], id),
      summary: text(item, ["summary", "description"]),
      selector: stringList(pick(item, "selectorIds", "selector_ids", "selectors"))[0] ??
        (text(item, ["selector_name", "selector", "selector_id"]) || undefined),
      constraintIds: stringList(pick(item, "constraintIds", "constraint_ids")).length
        ? stringList(pick(item, "constraintIds", "constraint_ids"))
        : nestedIds,
      regionIds: stringList(pick(item, "regionIds", "region_ids", "regions")),
      ...resolution,
      metrics: normalizeMetrics(pick(item, "metrics", "counts"), `${id}-metric`),
      searchTerms: stringList(pick(item, "searchTerms", "search_terms", "keywords", "tags")),
    };
  });
}

function normalizeLookups(configure: JsonRecord): CircuitLookup[] {
  return listFromSection(configure, "lookups", "lookup_arguments", "lookupArgs").map((raw, index) => {
    const item = record(raw);
    const id = text(item, ["id", "lookup_id"], `lookup:${index}`);
    const componentIds = stringList(pick(item, "componentIds", "component_ids", "components"));
    const resolution = sourceResolution(item);
    const pairs = array(pick(item, "pairs", "lookupPairs", "lookup_pairs")).map((rawPair, pairIndex) => {
      const pair = record(rawPair);
      const inputAst = pick(pair, "input", "expression", "input_expression");
      return {
        id: text(pair, ["id"], `${id}/pair:${pairIndex}`),
        inputExpression: formatExpression(inputAst),
        inputAst: inputAst !== undefined ? inputAst : undefined,
        tableId: text(pair, ["tableId", "table_id", "table", "column"]) || undefined,
        tableName: text(pair, ["tableName", "table_name", "column_name"]) || undefined,
      };
    });
    return {
      id,
      componentId: text(item, ["componentId", "component_id", "component"]) ||
        (componentIds.length === 1 ? componentIds[0] : undefined),
      componentIds,
      title: text(item, ["title", "label", "name"], `Lookup argument ${index + 1}`),
      summary: text(item, ["summary", "description"]),
      pairCount: numberValue(item, ["pairCount", "pair_count"], pairs.length),
      pairs,
      selectorIds: stringList(pick(item, "selectorIds", "selector_ids", "selectors")),
      tableIds: stringList(pick(item, "tableIds", "table_ids", "tables")),
      regionIds: stringList(pick(item, "regionIds", "region_ids", "regions")),
      ...resolution,
      metrics: normalizeMetrics(pick(item, "metrics", "counts"), `${id}-metric`),
      searchTerms: stringList(pick(item, "searchTerms", "search_terms", "keywords", "tags")),
    };
  });
}

function normalizeDiagnostics(raw: unknown): CircuitDiagnostic[] {
  const section = record(raw);
  const items = Array.isArray(raw)
    ? raw.map((item) => ({ item, severity: undefined }))
    : [
        ...array(section.errors).map((item) => ({ item, severity: "error" as const })),
        ...array(section.warnings).map((item) => ({ item, severity: "warning" as const })),
        ...array(section.info).map((item) => ({ item, severity: "info" as const })),
      ];
  return items.map(({ item: rawItem, severity: sectionSeverity }, index) => {
    if (typeof rawItem === "string") {
      return {
        id: `diagnostic:${index}`,
        severity: sectionSeverity ?? "info",
        message: rawItem,
        itemIds: [],
      };
    }
    const item = record(rawItem);
    const rawSeverity = text(item, ["severity", "level"]);
    const itemIds = stringList(pick(item, "itemIds", "item_ids", "entityIds", "entity_ids", "targets"));
    const itemId = text(item, ["itemId", "item_id", "target"]) || itemIds[0] || undefined;
    return {
      id: text(item, ["id", "code"], `diagnostic:${index}`),
      severity: sectionSeverity ??
        (rawSeverity === "error" || rawSeverity === "warning" ? rawSeverity : "info"),
      message: text(item, ["message", "description", "detail"], "Unspecified diagnostic"),
      itemId,
      itemIds,
    };
  });
}

function assertUnique(label: string, items: readonly { id: string }[]): void {
  const seen = new Set<string>();
  for (const item of items) {
    if (!item.id) throw new Error(`${label} contains an item without an id`);
    if (seen.has(item.id)) throw new Error(`${label} contains duplicate id ${item.id}`);
    seen.add(item.id);
  }
}

export function normalizeCircuitExplorerData(raw: unknown): CircuitExplorerData {
  const root = record(raw);
  const schema = text(root, ["schema"]);
  if (schema !== CIRCUIT_EXPLORER_SCHEMA) {
    throw new Error(
      `Unsupported circuit explorer schema ${schema || "(missing)"}; expected ${CIRCUIT_EXPLORER_SCHEMA}`,
    );
  }

  const metadata = record(root.metadata);
  const configure = record(root.configure);
  const synthesis = record(root.synthesis);
  const flow = record(root.flow);
  const rawGates = listFromSection(configure, "gates", "gate_groups");
  const nodes = normalizeFlowNodes(flow);
  const edges = normalizeFlowEdges(flow);
  const rawComponents = normalizeComponents(synthesis, flow);
  const namespaces = normalizeNamespaces(synthesis);
  const regions = normalizeRegions(synthesis);
  const rawOccurrences = normalizeOccurrences(synthesis);
  const rawOperations = normalizeOperations(synthesis);
  const groupByOccurrence = new Map(
    regions.flatMap((group) => group.occurrenceIds.map((occurrenceId) => [occurrenceId, group.id] as const)),
  );
  const operationsByOccurrence = new Map<string, string[]>();
  for (const operation of rawOperations) {
    const occurrenceId = operation.occurrenceId ?? operation.regionId;
    if (!occurrenceId) continue;
    const operationIds = operationsByOccurrence.get(occurrenceId) ?? [];
    operationIds.push(operation.id);
    operationsByOccurrence.set(occurrenceId, operationIds);
  }
  const occurrences = rawOccurrences.map((occurrence) => ({
    ...occurrence,
    groupId: occurrence.groupId || groupByOccurrence.get(occurrence.id) || "",
    operationIds: occurrence.operationIds.length
      ? occurrence.operationIds
      : operationsByOccurrence.get(occurrence.id) ?? [],
  }));
  const occurrenceById = new Map(occurrences.map((occurrence) => [occurrence.id, occurrence]));
  const operations = rawOperations.map((operation) => {
    if (operation.sourceConfidence || operation.sourceIds.length || operation.sourceCandidates.length) {
      return operation;
    }
    const ownedOccurrence = occurrenceById.get(operation.occurrenceId ?? operation.regionId ?? "");
    if (ownedOccurrence) return {
      ...operation,
      sourceIds: ownedOccurrence.sourceIds,
      sourceConfidence: ownedOccurrence.sourceConfidence,
      sourceCandidateIds: ownedOccurrence.sourceCandidateIds,
      sourceCandidates: ownedOccurrence.sourceCandidates,
    };

    // A top-level ConstrainInstance is not owned by its advice cell's region,
    // but that unique region is still useful provenance for the value being
    // exposed. Keep it candidate-only and mapped so the UI cannot mistake it
    // for the source definition of the layout operation itself.
    if (operation.kind === "constrain-instance") {
      const sourceRegionIds = [...new Set(
        operation.cells.flatMap((cell) =>
          cell.kind !== "instance" && cell.regionId ? [cell.regionId] : []
        ),
      )];
      const sourceOccurrence = sourceRegionIds.length === 1
        ? occurrenceById.get(sourceRegionIds[0])
        : undefined;
      if (sourceOccurrence) {
        const sourceCandidateIds = [...new Set([
          ...sourceOccurrence.sourceIds,
          ...sourceOccurrence.sourceCandidateIds,
        ])];
        if (sourceCandidateIds.length) {
          return {
            ...operation,
            sourceConfidence: "mapped" as const,
            sourceCandidateIds,
            sourceCandidates: sourceCandidateIds.map((sourceId) => ({
              sourceId,
              confidence: "mapped" as const,
              reason: "Source region of the advice cell constrained to this public instance row.",
            })),
          };
        }
      }
    }
    return operation;
  });
  const gates = normalizeGates(configure);
  const gateById = new Map(gates.map((gate) => [gate.id, gate]));
  const constraints = normalizeConstraints(configure, rawGates).map((constraint) => {
    if (constraint.sourceConfidence || constraint.sourceIds.length || constraint.sourceCandidates.length) {
      return constraint;
    }
    const gate = gateById.get(constraint.gateId);
    return gate ? {
      ...constraint,
      sourceIds: gate.sourceIds,
      sourceConfidence: gate.sourceConfidence,
      sourceCandidateIds: gate.sourceCandidateIds,
      sourceCandidates: gate.sourceCandidates,
    } : constraint;
  });
  const lookups = normalizeLookups(configure);
  const components = rawComponents.map((component) => {
    if (component.sourceIds.length || component.sourceCandidates.length) return component;
    const related = [
      ...regions.filter((region) => region.componentId === component.id),
      ...gates.filter((gate) => gate.componentId === component.id || gate.componentIds.includes(component.id)),
      ...lookups.filter((lookup) => lookup.componentId === component.id || lookup.componentIds.includes(component.id)),
      ...operations.filter((operation) =>
        operation.componentId === component.id || component.operationIds.includes(operation.id)
      ),
    ];
    const sourceIds = [...new Set(related.flatMap((item) => item.sourceIds))];
    const candidatesByKey = new Map<string, CircuitSourceResolutionCandidate>();
    for (const candidate of related.flatMap((item) => item.sourceCandidates)) {
      candidatesByKey.set(`${candidate.sourceId}:${candidate.confidence}`, candidate);
    }
    const sourceCandidates = [...candidatesByKey.values()];
    const relatedConfidences = related.flatMap(({ sourceConfidence: confidence }) => confidence ? [confidence] : []);
    const sourceConfidence: CircuitSourceConfidence | undefined = !relatedConfidences.length
      ? undefined
      : !sourceIds.length && relatedConfidences.includes("unresolved")
        ? "unresolved"
        : !sourceIds.length && relatedConfidences.includes("ambiguous")
          ? "ambiguous"
          : "mapped";
    return {
      ...component,
      sourceIds,
      sourceConfidence,
      sourceCandidateIds: sourceCandidates.map(({ sourceId }) => sourceId),
      sourceCandidates,
    };
  });
  const sources = normalizeSources(root.sources);

  assertUnique("flow.nodes", nodes);
  assertUnique("flow.edges", edges);
  assertUnique("synthesis.components", components);
  assertUnique("synthesis.namespaces", namespaces);
  assertUnique("synthesis.regions", regions);
  assertUnique("synthesis.occurrences", occurrences);
  assertUnique("synthesis.operations", operations);
  assertUnique("configure.gates", gates);
  assertUnique("configure.constraints", constraints);
  assertUnique("configure.lookups", lookups);
  assertUnique("sources", sources);

  const nodeIds = new Set(nodes.map(({ id }) => id));
  for (const edge of edges) {
    if (!nodeIds.has(edge.from) || !nodeIds.has(edge.to)) {
      throw new Error(`Flow edge ${edge.id} has a dangling endpoint`);
    }
  }

  if (!nodes.length || !components.length) {
    throw new Error("Circuit explorer data must contain flow nodes and components");
  }

  const refsRaw = record(pick(metadata, "repositoryRefs", "repository_refs", "revisions"));
  const repositoryRefs = Object.fromEntries(
    Object.entries(refsRaw).map(([key, value]) => [key, String(value)]),
  );
  const representationsRaw = record(pick(metadata, "representations"));
  const representations = Object.fromEntries(
    Object.entries(representationsRaw).flatMap(([key, value]) =>
      typeof value === "string" ? [[key, value]] : []
    ),
  );
  const circuit = record(metadata.circuit);
  const configureSummary = record(configure.summary);
  const synthesisSummary = record(synthesis.summary);
  const metadataMetrics: CircuitMetric[] = [
    ["gates", "Gates", numberValue(configureSummary, ["gate_count", "gateCount"], gates.length)],
    ["constraints", "Constraints", numberValue(configureSummary, ["constraint_count", "constraintCount"], constraints.length)],
    ["lookups", "Lookups", numberValue(configureSummary, ["lookup_count", "lookupCount"], lookups.length)],
    ["regions", "Exact regions", numberValue(synthesisSummary, ["region_count", "regionCount"], occurrences.length)],
    ["operations", "Operations", numberValue(synthesisSummary, ["operationCount", "operation_count", "region_operation_count"], operations.length)],
    ["namespaces", "Namespaces", numberValue(synthesisSummary, ["namespace_count", "namespaceCount"], namespaces.length)],
  ].map(([id, label, value]) => ({ id: `dataset-${id}`, label: String(label), value: String(value) }));
  const explicitMetadataMetrics = normalizeMetrics(pick(metadata, "metrics", "counts", "summary"), "dataset-metric");
  const bounds = record(flow.bounds);

  return {
    schema: CIRCUIT_EXPLORER_SCHEMA,
    metadata: {
      title: text(metadata, ["title"], text(circuit, ["name"], "Orchard Action circuit")),
      description: text(
        metadata,
        ["description", "summary"],
        "A pinned high-level and exact view of gates and lookups declared during configuration, synthesis regions, and layouter operations captured from the Rocq model.",
      ),
      asOf: text(metadata, ["asOf", "as_of", "generated_at", "date"]),
      version: text(circuit, ["version"]),
      field: text(circuit, ["field"]),
      k: optionalNumber(circuit, ["k"]),
      floorPlanner: text(metadata, ["floorPlanner", "floor_planner"]),
      witnessValues: text(circuit, ["witnessValues", "witness_values"]),
      placement: text(metadata, ["placement"]),
      representations,
      repositoryRefs,
      metrics: explicitMetadataMetrics.length ? explicitMetadataMetrics : metadataMetrics,
    },
    flow: {
      nodes,
      edges,
      bounds: {
        width: numberValue(bounds, ["width"], 1160),
        height: numberValue(bounds, ["height"], 720),
      },
    },
    synthesis: { components, namespaces, regions, occurrences, operations },
    configure: { gates, constraints, lookups },
    sources,
    diagnostics: normalizeDiagnostics(root.diagnostics),
  };
}

export function circuitExplorerDataUrl(): string {
  return new URL(DATA_FILE, document.baseURI).href;
}

export function loadCircuitExplorerData(): Promise<CircuitExplorerData> {
  if (!cachedLoad) {
    cachedLoad = fetch(circuitExplorerDataUrl(), {
      headers: { Accept: "application/json" },
    })
      .then(async (response) => {
        if (!response.ok) {
          throw new Error(`Could not load circuit data (${response.status})`);
        }
        return normalizeCircuitExplorerData(await response.json());
      })
      .catch((error: unknown) => {
        cachedLoad = null;
        throw error;
      });
  }
  return cachedLoad;
}

export function clearCircuitExplorerDataCache(): void {
  cachedLoad = null;
}
