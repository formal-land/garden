import {
  CIRCUIT_GRID_SCHEMA,
  type CircuitGridCapabilities,
  type CircuitGridColumn,
  type CircuitGridColumnKind,
  type CircuitGridData,
  type CircuitGridEndpoint,
  type CircuitGridEvent,
  type CircuitGridEventKind,
  type CircuitGridInput,
  type CircuitGridRegion,
  type CircuitGridSelector,
  type CircuitGridSparseRow,
  type CircuitGridTarget,
  type CircuitGridTargetKind,
} from "./model";
import {
  numberValue,
  optionalNumber,
  pick,
  record,
  text,
  type JsonRecord,
} from "../shared/json";

const DATA_FILE = "data/orchard-circuit-grid.v1.json";
let cachedLoad: Promise<CircuitGridData> | null = null;

function list(value: unknown): unknown[] {
  if (Array.isArray(value)) return value;
  return Object.entries(record(value)).map(([id, item]) => ({
    id,
    ...record(item),
  }));
}

function stringList(value: unknown): string[] {
  return list(value)
    .map((item) => {
      if (typeof item === "string" || typeof item === "number") return String(item);
      return text(record(item), ["id", "name", "label"]);
    })
    .filter(Boolean);
}

function words(value: string): string {
  return value
    .replace(/([a-z0-9])([A-Z])/g, "$1 $2")
    .replace(/[_-]+/g, " ")
    .trim()
    .replace(/\b\w/g, (letter) => letter.toUpperCase());
}

function normalizeTarget(
  value: unknown,
  fallbackId: string,
  fallbackKind: CircuitGridTargetKind,
  fallbackTitle: string,
): CircuitGridTarget | undefined {
  if (typeof value === "string" && value) {
    return {
      id: `target:${fallbackId}`,
      kind: fallbackKind,
      title: fallbackTitle,
      href: value,
    };
  }
  const target = record(value);
  const href = text(target, ["href", "url", "circuitHref", "circuit_href"]);
  if (!href) return undefined;
  const rawKind = text(target, ["kind", "type"], fallbackKind);
  const validKinds: readonly CircuitGridTargetKind[] = [
    "component",
    "region",
    "operation",
    "gate",
    "lookup",
    "constraint",
    "other",
  ];
  return {
    id: text(target, ["id"], `target:${fallbackId}`),
    kind: validKinds.includes(rawKind as CircuitGridTargetKind)
      ? rawKind as CircuitGridTargetKind
      : fallbackKind,
    title: text(target, ["title", "label"], fallbackTitle),
    href,
  };
}

function columnKind(value: string): CircuitGridColumnKind {
  const normalized = value.toLocaleLowerCase();
  if (normalized.includes("instance")) return "instance";
  if (normalized.includes("fixed")) return "fixed";
  return "advice";
}

function normalizeColumns(value: unknown): CircuitGridColumn[] {
  return list(value).map((rawColumn, position) => {
    const item = record(rawColumn);
    const id = text(item, ["id", "columnId", "column_id"]);
    const kind = columnKind(text(item, ["kind", "columnKind", "column_kind"], id));
    const index = numberValue(item, ["index", "columnIndex", "column_index"], position);
    const name = text(
      item,
      ["name", "label", "displayName", "display_name"],
      `${kind === "instance" ? "I" : kind === "fixed" ? "F" : "A"}${index}`,
    );
    const normalizedId = id || `${kind}:${index}`;
    return {
      id: normalizedId,
      kind,
      index,
      name,
      role: text(item, ["role", "purpose", "description"]) || undefined,
      circuitTarget: normalizeTarget(
        pick(item, "circuitTarget", "circuit_target", "target"),
        normalizedId,
        "other",
        name,
      ),
    };
  });
}

function normalizeSelectors(value: unknown): CircuitGridSelector[] {
  return list(value).map((rawSelector, position) => {
    const item = record(rawSelector);
    const index = numberValue(item, ["index", "selectorIndex", "selector_index"], position);
    const id = text(item, ["id", "selectorId", "selector_id"], `selector:${index}`);
    const name = text(
      item,
      ["name", "label", "displayName", "display_name"],
      `Selector ${index}`,
    );
    return {
      id,
      index,
      name,
      gateIds: stringList(pick(item, "gateIds", "gate_ids", "gates")),
      lookupIds: stringList(pick(item, "lookupIds", "lookup_ids", "lookups")),
      circuitTarget: normalizeTarget(
        pick(item, "circuitTarget", "circuit_target", "target"),
        id,
        "gate",
        name,
      ),
    };
  });
}

function normalizeRegions(value: unknown): CircuitGridRegion[] {
  return list(value).map((rawRegion, position) => {
    const item = record(rawRegion);
    const index = numberValue(item, ["regionIndex", "region_index", "index"], position);
    const id = text(item, ["id", "regionId", "region_id"], `region:${index}`);
    const name = text(item, ["name", "title", "label"], `Region ${index}`);
    return {
      id,
      regionIndex: index,
      startRow: numberValue(item, ["startRow", "start_row", "row"], 0),
      endRow: optionalNumber(item, ["endRow", "end_row", "rowEnd", "row_end"]),
      name,
      namespace: stringList(pick(item, "namespace", "namespacePath", "namespace_path")),
      componentId: text(item, ["componentId", "component_id"]) || undefined,
      selectorIds: stringList(pick(item, "selectorIds", "selector_ids", "selectors")),
      gateIds: stringList(pick(item, "gateIds", "gate_ids", "gates")),
      lookupIds: stringList(pick(item, "lookupIds", "lookup_ids", "lookups")),
      operationIds: stringList(pick(item, "operationIds", "operation_ids", "operations")),
      circuitTarget: normalizeTarget(
        pick(item, "circuitTarget", "circuit_target", "target"),
        id,
        "region",
        name,
      ),
    };
  });
}

function eventKind(value: string): CircuitGridEventKind {
  switch (value.replace(/[^a-z]/gi, "").toLocaleLowerCase()) {
    case "assignfixed":
      return "assign-fixed";
    case "enableselector":
      return "enable-selector";
    case "copy":
      return "copy";
    case "fill":
    case "fillfromrow":
    case "assignfixedrange":
      return "fill";
    case "constrainconstant":
      return "constrain-constant";
    case "constraininstance":
      return "constrain-instance";
    case "advicereference":
    case "referenceadvice":
      return "advice-reference";
    case "regionstart":
      return "region-start";
    default:
      return "other";
  }
}

function normalizeEndpoint(value: unknown): CircuitGridEndpoint | undefined {
  const endpoint = record(value);
  const nestedColumn = record(pick(endpoint, "column"));
  const nestedKind = text(nestedColumn, ["kind", "type"]);
  const nestedIndex = optionalNumber(nestedColumn, ["index", "columnIndex", "column_index"]);
  const fallbackColumnId = nestedIndex === undefined
    ? ""
    : `${columnKind(nestedKind)}:${nestedIndex}`;
  const columnId = text(
    endpoint,
    ["columnId", "column_id"],
    text(nestedColumn, ["id", "columnId", "column_id"], fallbackColumnId),
  );
  const row = optionalNumber(endpoint, ["row", "absoluteRow", "absolute_row"]);
  return columnId && row !== undefined ? { columnId, row } : undefined;
}

function endpointList(item: JsonRecord): CircuitGridEndpoint[] {
  const explicit = list(pick(item, "endpoints", "cells"))
    .flatMap((rawEndpoint) => {
      const endpoint = normalizeEndpoint(rawEndpoint);
      return endpoint ? [endpoint] : [];
    });
  if (explicit.length) return explicit;
  return [
    pick(item, "left", "lhs", "source", "cell"),
    pick(item, "right", "rhs", "destination", "instance"),
  ].flatMap((candidate) => {
    const endpoint = normalizeEndpoint(candidate);
    return endpoint ? [endpoint] : [];
  });
}

function normalizeEvents(value: unknown): CircuitGridEvent[] {
  return list(value).map((rawEvent, position) => {
    const item = record(rawEvent);
    const sourceTag = text(item, ["tag", "sourceTag", "source_tag", "kind", "type"], "Other");
    const kind = eventKind(sourceTag);
    const id = text(item, ["id", "eventId", "event_id"], `trace-event:${position}`);
    const selectorValue = pick(item, "selectorId", "selector_id", "selector");
    const selectorId = selectorValue === undefined || selectorValue === null
      ? undefined
      : typeof selectorValue === "object"
        ? text(record(selectorValue), ["id", "selectorId", "selector_id"])
        : String(selectorValue).startsWith("selector:")
          ? String(selectorValue)
          : `selector:${String(selectorValue)}`;
    const rawColumn = pick(item, "columnId", "column_id", "column");
    const columnId = typeof rawColumn === "object"
      ? normalizeEndpoint({ column: rawColumn, row: 0 })?.columnId
      : rawColumn === undefined || rawColumn === null
        ? undefined
        : String(rawColumn).includes(":")
          ? String(rawColumn)
          : `fixed:${String(rawColumn)}`;
    const endpoints = endpointList(item);
    const fallbackRow = endpoints[0]?.row;
    return {
      id,
      kind,
      sourceIndex: optionalNumber(item, ["sourceIndex", "source_index", "index"]),
      sourceTag,
      row: optionalNumber(item, ["row", "absoluteRow", "absolute_row"]) ?? fallbackRow,
      columnId: columnId ?? (endpoints.length === 1 ? endpoints[0].columnId : undefined),
      selectorId,
      annotation: text(item, ["annotation", "label", "description"]) || undefined,
      value: text(item, ["value", "defaultValue", "default_value"]) || undefined,
      fromRow: optionalNumber(item, ["fromRow", "from_row", "startRow", "start_row"]),
      toRow: optionalNumber(item, ["toRow", "to_row", "endRow", "end_row"]),
      endpoints,
      peerEventIds: stringList(pick(item, "peerEventIds", "peer_event_ids", "peers")),
      regionId: text(item, ["regionId", "region_id"]) || undefined,
      namespace: stringList(pick(item, "namespace", "namespacePath", "namespace_path")),
      gateIds: stringList(pick(item, "gateIds", "gate_ids", "gates")),
      lookupIds: stringList(pick(item, "lookupIds", "lookup_ids", "lookups")),
      operationIds: stringList(pick(item, "operationIds", "operation_ids", "operations")),
      circuitTarget: normalizeTarget(
        pick(item, "circuitTarget", "circuit_target", "target"),
        id,
        "operation",
        text(item, ["annotation", "label"], words(sourceTag)),
      ),
    };
  });
}

function normalizeRows(value: unknown): CircuitGridSparseRow[] {
  return list(value).map((rawRow, position) => {
    const item = record(rawRow);
    return {
      row: numberValue(item, ["row", "index"], position),
      eventIds: stringList(pick(item, "eventIds", "event_ids", "events")),
      regionIds: stringList(pick(item, "regionIds", "region_ids", "regions")),
      selectorIds: stringList(pick(item, "selectorIds", "selector_ids", "selectors")),
      columnIds: stringList(pick(item, "columnIds", "column_ids", "columns")),
    };
  }).sort((left, right) => left.row - right.row);
}

function normalizeInputs(value: unknown): CircuitGridInput[] {
  return list(value).map((rawInput, position) => {
    const item = record(rawInput);
    return {
      id: text(item, ["id", "name", "label"], `input:${position}`),
      path: text(item, ["path", "file"]),
      sha256: text(item, ["sha256", "hash", "digest"]) || undefined,
    };
  });
}

function scalarRecord(value: unknown): Record<string, string> {
  return Object.fromEntries(
    Object.entries(record(value)).flatMap(([key, rawValue]) =>
      typeof rawValue === "string" || typeof rawValue === "number" ||
          typeof rawValue === "boolean"
        ? [[key, String(rawValue)]]
        : []
    ),
  );
}

function countRecord(value: unknown): Record<string, number> {
  return Object.fromEntries(
    Object.entries(record(value)).flatMap(([key, rawValue]) => {
      const parsed = Number(rawValue);
      return Number.isFinite(parsed) ? [[key, parsed]] : [];
    }),
  );
}

function assertUnique(label: string, items: readonly { id: string }[]): void {
  const ids = new Set<string>();
  for (const item of items) {
    if (!item.id) throw new Error(`${label} contains an item without an id`);
    if (ids.has(item.id)) throw new Error(`${label} contains duplicate id ${item.id}`);
    ids.add(item.id);
  }
}

function fallbackRows(
  events: readonly CircuitGridEvent[],
  regions: readonly CircuitGridRegion[],
): CircuitGridSparseRow[] {
  const rows = new Map<number, {
    eventIds: Set<string>;
    regionIds: Set<string>;
    selectorIds: Set<string>;
    columnIds: Set<string>;
  }>();
  const row = (index: number) => {
    const existing = rows.get(index);
    if (existing) return existing;
    const created = {
      eventIds: new Set<string>(),
      regionIds: new Set<string>(),
      selectorIds: new Set<string>(),
      columnIds: new Set<string>(),
    };
    rows.set(index, created);
    return created;
  };
  for (const event of events) {
    const endpoints = event.endpoints.length
      ? event.endpoints
      : event.row !== undefined && event.columnId
        ? [{ row: event.row, columnId: event.columnId }]
        : [];
    for (const endpoint of endpoints) {
      const entry = row(endpoint.row);
      entry.eventIds.add(event.id);
      entry.columnIds.add(endpoint.columnId);
      if (event.regionId) entry.regionIds.add(event.regionId);
    }
    if (event.row !== undefined && event.selectorId) {
      const entry = row(event.row);
      entry.eventIds.add(event.id);
      entry.selectorIds.add(event.selectorId);
      if (event.regionId) entry.regionIds.add(event.regionId);
    }
  }
  for (const region of regions) row(region.startRow).regionIds.add(region.id);
  return [...rows.entries()]
    .sort(([left], [right]) => left - right)
    .map(([index, item]) => ({
      row: index,
      eventIds: [...item.eventIds],
      regionIds: [...item.regionIds],
      selectorIds: [...item.selectorIds],
      columnIds: [...item.columnIds],
    }));
}

export function normalizeCircuitGridData(raw: unknown): CircuitGridData {
  const root = record(raw);
  const schema = text(root, ["schema"]);
  if (schema !== CIRCUIT_GRID_SCHEMA) {
    throw new Error(
      `Unsupported circuit grid schema ${schema || "(missing)"}; expected ${CIRCUIT_GRID_SCHEMA}`,
    );
  }

  const metadata = record(root.metadata);
  const circuit = record(metadata.circuit);
  const rawCapabilities = record(
    pick(metadata, "capabilities", "coverage", "representations"),
  );
  const columns = normalizeColumns(root.columns);
  const selectors = normalizeSelectors(root.selectors);
  const regions = normalizeRegions(root.regions);
  const events = normalizeEvents(root.events);
  const explicitRows = normalizeRows(root.rows);
  const rows = explicitRows.length ? explicitRows : fallbackRows(events, regions);
  const summary = record(root.summary);
  const rowCount = numberValue(
    circuit,
    ["rowCount", "row_count"],
    numberValue(metadata, ["rowCount", "row_count"], 2 ** numberValue(circuit, ["k"], 11)),
  );

  assertUnique("columns", columns);
  assertUnique("selectors", selectors);
  assertUnique("regions", regions);
  assertUnique("events", events);

  if (!columns.length || rowCount < 1) {
    throw new Error("Circuit grid data must contain columns and at least one row");
  }
  const columnIds = new Set(columns.map(({ id }) => id));
  const selectorIds = new Set(selectors.map(({ id }) => id));
  for (const event of events) {
    const referencedColumns = [
      ...(event.columnId ? [event.columnId] : []),
      ...event.endpoints.map(({ columnId }) => columnId),
    ];
    for (const columnId of referencedColumns) {
      if (!columnIds.has(columnId)) {
        throw new Error(`Event ${event.id} references unknown column ${columnId}`);
      }
    }
    if (event.selectorId && !selectorIds.has(event.selectorId)) {
      throw new Error(`Event ${event.id} references unknown selector ${event.selectorId}`);
    }
    const referencedRows = [
      ...(event.row === undefined ? [] : [event.row]),
      ...(event.fromRow === undefined ? [] : [event.fromRow]),
      ...(event.toRow === undefined ? [] : [event.toRow]),
      ...event.endpoints.map(({ row }) => row),
    ];
    if (referencedRows.some((row) => row < 0 || row >= rowCount)) {
      throw new Error(`Event ${event.id} references a row outside 0–${rowCount - 1}`);
    }
  }

  const targets = new Map<string, CircuitGridTarget>();
  for (const target of [
    ...columns.flatMap(({ circuitTarget }) => circuitTarget ? [circuitTarget] : []),
    ...selectors.flatMap(({ circuitTarget }) => circuitTarget ? [circuitTarget] : []),
    ...regions.flatMap(({ circuitTarget }) => circuitTarget ? [circuitTarget] : []),
    ...events.flatMap(({ circuitTarget }) => circuitTarget ? [circuitTarget] : []),
    ...list(root.targets).flatMap((rawTarget, index) => {
      const item = record(rawTarget);
      const target = normalizeTarget(
        item,
        text(item, ["id"], `explicit:${index}`),
        "other",
        text(item, ["title", "label"], `Circuit target ${index + 1}`),
      );
      return target ? [target] : [];
    }),
  ]) targets.set(target.id, target);

  const capabilities: CircuitGridCapabilities = {
    adviceAssignments: text(
      rawCapabilities,
      ["adviceAssignments", "advice_assignments"],
      "references-only",
    ),
    witnessValues: text(
      rawCapabilities,
      ["witnessValues", "witness_values"],
      "omitted",
    ),
    selectors: text(rawCapabilities, ["selectors"], "virtual"),
    permutation: text(rawCapabilities, ["permutation"], "copy-edges"),
  };

  return {
    schema: CIRCUIT_GRID_SCHEMA,
    metadata: {
      circuit: {
        id: text(circuit, ["id"], "orchard-action"),
        name: text(circuit, ["name", "title"], "Orchard Action Circuit"),
        version: text(circuit, ["version"]),
        field: text(circuit, ["field"]),
        k: numberValue(circuit, ["k"], 11),
        rowCount,
        floorPlanner: text(
          circuit,
          ["floorPlanner", "floor_planner"],
          text(metadata, ["floorPlanner", "floor_planner"], "V1"),
        ),
        stage: text(
          circuit,
          ["stage"],
          text(metadata, ["stage"], "pre-selector-compression"),
        ),
      },
      capabilities,
      inputs: normalizeInputs(metadata.inputs),
      parity: scalarRecord(metadata.parity),
      repositoryRefs: scalarRecord(
        pick(metadata, "repositoryRefs", "repository_refs", "revisions"),
      ),
    },
    columns,
    selectors,
    regions,
    events,
    rows,
    targets: [...targets.values()],
    summary: {
      columnCount: numberValue(summary, ["columnCount", "column_count"], columns.length),
      selectorCount: numberValue(summary, ["selectorCount", "selector_count"], selectors.length),
      regionCount: numberValue(summary, ["regionCount", "region_count"], regions.length),
      eventCount: numberValue(summary, ["eventCount", "event_count"], events.length),
      populatedRowCount: numberValue(
        summary,
        ["populatedRowCount", "populated_row_count"],
        rows.length,
      ),
      counts: countRecord(pick(summary, "counts", "eventCounts", "event_counts")),
    },
  };
}

export function circuitGridDataUrl(): string {
  return new URL(DATA_FILE, document.baseURI).href;
}

export function loadCircuitGridData(): Promise<CircuitGridData> {
  if (!cachedLoad) {
    cachedLoad = fetch(circuitGridDataUrl(), {
      headers: { Accept: "application/json" },
    })
      .then(async (response) => {
        if (!response.ok) {
          throw new Error(`Could not load circuit grid data (${response.status})`);
        }
        return normalizeCircuitGridData(await response.json());
      })
      .catch((error: unknown) => {
        cachedLoad = null;
        throw error;
      });
  }
  return cachedLoad;
}

export function clearCircuitGridDataCache(): void {
  cachedLoad = null;
}
