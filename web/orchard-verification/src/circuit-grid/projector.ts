import type {
  CircuitGridCellProjection,
  CircuitGridColumn,
  CircuitGridData,
  CircuitGridEndpoint,
  CircuitGridEvent,
  CircuitGridMark,
  CircuitGridRegion,
  CircuitGridSearchResult,
  CircuitGridSelector,
  CircuitGridTarget,
  CircuitGridTrack,
} from "./model";

const COLLAPSED_SELECTOR_ID = "selectors:collapsed";

function cellKey(row: number, columnId: string): string {
  return `${row}\u0000${columnId}`;
}

function uniqueById<T extends { readonly id: string }>(items: readonly T[]): T[] {
  return [...new Map(items.map((item) => [item.id, item])).values()];
}

function columnWeight(column: CircuitGridColumn): number {
  if (column.kind === "instance") return 0;
  if (column.kind === "advice") return 1;
  return /\b(lookup|table)\b/i.test(column.role ?? "") ? 2 : 3;
}

function columnTracks(columns: readonly CircuitGridColumn[]): CircuitGridTrack[] {
  return [...columns]
    .sort((left, right) =>
      columnWeight(left) - columnWeight(right) ||
      left.index - right.index ||
      left.id.localeCompare(right.id)
    )
    .map((column): CircuitGridTrack => ({
      id: column.id,
      kind: column.kind,
      label: column.name,
      description: [
        `${column.kind[0].toLocaleUpperCase()}${column.kind.slice(1)} column ${column.index}`,
        column.role,
      ].filter(Boolean).join(" · "),
      column,
    }));
}

function selectorTracks(
  selectors: readonly CircuitGridSelector[],
  expanded: boolean,
): CircuitGridTrack[] {
  if (!expanded) {
    return [{
      id: COLLAPSED_SELECTOR_ID,
      kind: "selectors",
      label: "Q",
      description: `${selectors.length} virtual selector columns (collapsed)`,
    }];
  }
  return [...selectors]
    .sort((left, right) => left.index - right.index)
    .map((selector): CircuitGridTrack => ({
      id: selector.id,
      kind: "selector",
      label: selector.name || `Q${selector.index}`,
      description: [
        `Virtual selector ${selector.index}`,
        selector.gateIds.length
          ? `${selector.gateIds.length} gate${selector.gateIds.length === 1 ? "" : "s"}`
          : null,
        selector.lookupIds.length
          ? `${selector.lookupIds.length} lookup${selector.lookupIds.length === 1 ? "" : "s"}`
          : null,
      ].filter(Boolean).join(" · "),
      selector,
    }));
}

function eventLabel(
  event: CircuitGridEvent,
  selector?: CircuitGridSelector,
  peer?: CircuitGridEndpoint,
): string {
  switch (event.kind) {
    case "enable-selector":
      return selector?.name ?? event.selectorId ?? "Selector enabled";
    case "assign-fixed":
      return event.annotation || "Fixed assignment";
    case "fill":
      return event.annotation || `Fixed fill ${event.fromRow ?? "?"}–${event.toRow ?? "?"}`;
    case "copy":
      return peer
        ? `Copy edge to ${peer.columnId} · row ${peer.row}`
        : "Copy edge";
    case "constrain-constant":
      return event.annotation || "Constant reference";
    case "constrain-instance":
      return event.annotation || "Public instance reference";
    case "advice-reference":
      return event.annotation || "Referenced advice cell";
    case "region-start":
      return event.annotation || "Region starts";
    default:
      return event.annotation || event.sourceTag || "Recorded event";
  }
}

function mark(
  event: CircuitGridEvent,
  selector?: CircuitGridSelector,
  peer?: CircuitGridEndpoint,
  fromRange = false,
): CircuitGridMark {
  const suffix = selector?.id ??
    (peer ? `${peer.columnId}:${peer.row}` : "mark");
  return {
    id: `${event.id}:${suffix}`,
    kind: event.kind,
    label: eventLabel(event, selector, peer),
    event,
    selector,
    peer,
    fromRange,
  };
}

function regionsAtRow(
  row: number,
  rowRegionIds: readonly string[],
  regionById: ReadonlyMap<string, CircuitGridRegion>,
  regions: readonly CircuitGridRegion[],
): CircuitGridRegion[] {
  const explicit = rowRegionIds.flatMap((id) => {
    const region = regionById.get(id);
    return region ? [region] : [];
  });
  const containing = regions.filter((region) =>
    region.startRow <= row &&
    (region.endRow === undefined ? region.startRow === row : row <= region.endRow)
  );
  return uniqueById([...explicit, ...containing]);
}

function targetForIds(
  ids: readonly string[],
  kind: CircuitGridTarget["kind"],
  fallbackTitle: string,
): CircuitGridTarget[] {
  return ids.map((id) => ({
    id: `derived:${kind}:${id}`,
    kind,
    title: fallbackTitle || id,
    href: circuitHref(kind, id),
  }));
}

export function circuitHref(
  kind: CircuitGridTarget["kind"],
  id: string,
  parentId?: string,
): string {
  const parameters = new URLSearchParams();
  if (kind === "component") {
    parameters.set("level", "component");
    parameters.set("item", id);
  } else if (kind === "operation" && parentId) {
    parameters.set("level", "detail");
    parameters.set("item", parentId);
    parameters.set("focus", id);
  } else {
    parameters.set("level", "detail");
    parameters.set("item", id);
  }
  return `circuit.html#${parameters.toString()}`;
}

export interface CircuitGridProjection {
  readonly data: CircuitGridData;
  readonly tracks: readonly CircuitGridTrack[];
  readonly rowsWithData: readonly number[];
  readonly regionStarts: ReadonlyMap<number, readonly CircuitGridRegion[]>;
  readonly cell: (row: number, columnId: string) => CircuitGridCellProjection;
  readonly rowEvents: (row: number) => readonly CircuitGridEvent[];
  readonly rowRegions: (row: number) => readonly CircuitGridRegion[];
  readonly search: (query: string, limit?: number) => readonly CircuitGridSearchResult[];
}

export function createCircuitGridProjection(
  data: CircuitGridData,
  selectorsExpanded: boolean,
): CircuitGridProjection {
  const tracks = [
    ...columnTracks(data.columns),
    ...selectorTracks(data.selectors, selectorsExpanded),
  ];
  const trackById = new Map(tracks.map((track) => [track.id, track]));
  const eventById = new Map(data.events.map((event) => [event.id, event]));
  const selectorById = new Map(data.selectors.map((selector) => [selector.id, selector]));
  const regionById = new Map(data.regions.map((region) => [region.id, region]));
  const rowByIndex = new Map(data.rows.map((row) => [row.row, row]));
  const directMarks = new Map<string, CircuitGridMark[]>();
  const selectorMarks = new Map<number, CircuitGridMark[]>();
  const rangesByColumn = new Map<string, CircuitGridEvent[]>();
  const regionStarts = new Map<number, CircuitGridRegion[]>();

  const addDirectMark = (row: number, columnId: string, value: CircuitGridMark) => {
    const key = cellKey(row, columnId);
    const values = directMarks.get(key) ?? [];
    values.push(value);
    directMarks.set(key, values);
  };

  for (const event of data.events) {
    if (event.kind === "enable-selector" && event.row !== undefined && event.selectorId) {
      const selector = selectorById.get(event.selectorId);
      const value = mark(event, selector);
      const rowValues = selectorMarks.get(event.row) ?? [];
      rowValues.push(value);
      selectorMarks.set(event.row, rowValues);
      if (selector) addDirectMark(event.row, selector.id, value);
      continue;
    }

    if (
      event.kind === "fill" &&
      event.columnId &&
      event.fromRow !== undefined &&
      event.toRow !== undefined
    ) {
      const ranges = rangesByColumn.get(event.columnId) ?? [];
      ranges.push(event);
      rangesByColumn.set(event.columnId, ranges);
      continue;
    }

    if (event.endpoints.length) {
      event.endpoints.forEach((endpoint, endpointIndex) => {
        const peers = event.endpoints.filter((_, index) => index !== endpointIndex);
        if (!peers.length) {
          addDirectMark(endpoint.row, endpoint.columnId, mark(event));
          return;
        }
        peers.forEach((peer) => {
          addDirectMark(endpoint.row, endpoint.columnId, mark(event, undefined, peer));
        });
      });
      continue;
    }

    if (event.row !== undefined && event.columnId) {
      addDirectMark(event.row, event.columnId, mark(event));
    }
  }

  for (const region of data.regions) {
    const starts = regionStarts.get(region.startRow) ?? [];
    starts.push(region);
    regionStarts.set(region.startRow, starts);
  }

  const rowRegionCache = new Map<number, CircuitGridRegion[]>();
  const rowRegions = (row: number): CircuitGridRegion[] => {
    const cached = rowRegionCache.get(row);
    if (cached) return cached;
    const projected = regionsAtRow(
      row,
      rowByIndex.get(row)?.regionIds ?? [],
      regionById,
      data.regions,
    );
    rowRegionCache.set(row, projected);
    return projected;
  };

  const rowEvents = (row: number): CircuitGridEvent[] => {
    const rowEventIds = rowByIndex.get(row)?.eventIds ?? [];
    const explicit = rowEventIds.flatMap((id) => {
      const event = eventById.get(id);
      return event ? [event] : [];
    });
    const ranges = [...rangesByColumn.values()]
      .flat()
      .filter((event) =>
        event.fromRow !== undefined &&
        event.toRow !== undefined &&
        event.fromRow <= row &&
        row <= event.toRow
      );
    return uniqueById([...explicit, ...ranges]);
  };

  const cell = (row: number, columnId: string): CircuitGridCellProjection => {
    const track = trackById.get(columnId) ?? tracks[0];
    if (!track) throw new Error("Circuit grid projection has no visible tracks");
    const marks = columnId === COLLAPSED_SELECTOR_ID
      ? selectorMarks.get(row) ?? []
      : [
          ...(directMarks.get(cellKey(row, columnId)) ?? []),
          ...(rangesByColumn.get(columnId) ?? [])
            .filter((event) =>
              event.fromRow !== undefined &&
              event.toRow !== undefined &&
              event.fromRow <= row &&
              row <= event.toRow
            )
            .map((event) => mark(event, undefined, undefined, true)),
        ];
    const regions = rowRegions(row);
    const eventTargets = marks.flatMap(({ event }) => {
      if (event.circuitTarget) return [event.circuitTarget];
      if (event.operationIds.length) {
        return event.operationIds.map((operationId) => ({
          id: `derived:operation:${operationId}`,
          kind: "operation" as const,
          title: "Open operation",
          href: circuitHref("operation", operationId, event.regionId),
        }));
      }
      return [];
    });
    const selectorTargets = marks.flatMap(({ selector }) => {
      if (!selector) return [];
      if (selector.circuitTarget) return [selector.circuitTarget];
      return [
        ...targetForIds(selector.gateIds, "gate", "Open gate"),
        ...targetForIds(selector.lookupIds, "lookup", "Open lookup"),
      ];
    });
    const regionTargets = regions.map((region) =>
      region.circuitTarget ?? {
        id: `derived:region:${region.id}`,
        kind: "region" as const,
        title: `Open ${region.name}`,
        href: circuitHref("region", region.id),
      }
    );
    return {
      row,
      track,
      marks: uniqueById(marks),
      regions,
      targets: uniqueById([...eventTargets, ...selectorTargets, ...regionTargets]),
    };
  };

  const rowsWithData = [...new Set([
    ...data.rows.map(({ row }) => row),
    ...data.regions.map(({ startRow }) => startRow),
    ...data.events.flatMap((event) => [
      ...(event.row === undefined ? [] : [event.row]),
      ...(event.fromRow === undefined ? [] : [event.fromRow]),
      ...event.endpoints.map(({ row }) => row),
    ]),
  ])].filter((row) => row >= 0 && row < data.metadata.circuit.rowCount)
    .sort((left, right) => left - right);

  const search = (rawQuery: string, limit = 14): CircuitGridSearchResult[] => {
    const query = rawQuery.trim().toLocaleLowerCase();
    if (!query) return [];
    const results: CircuitGridSearchResult[] = [];
    const numericRow = Number(query.replace(/^row\s*/i, ""));
    if (
      Number.isInteger(numericRow) &&
      numericRow >= 0 &&
      numericRow < data.metadata.circuit.rowCount
    ) {
      results.push({
        id: `row:${numericRow}`,
        kind: "row",
        title: `Row ${numericRow}`,
        detail: rowEvents(numericRow).length
          ? `${rowEvents(numericRow).length} recorded event${rowEvents(numericRow).length === 1 ? "" : "s"}`
          : "No directly recorded events",
        row: numericRow,
      });
    }
    for (const selector of data.selectors) {
      const haystack = [
        selector.id,
        selector.name,
        ...selector.gateIds,
        ...selector.lookupIds,
      ].join(" ").toLocaleLowerCase();
      if (!haystack.includes(query)) continue;
      const firstRow = data.rows.find(({ selectorIds }) => selectorIds.includes(selector.id))?.row ??
        data.events.find(({ selectorId }) => selectorId === selector.id)?.row ??
        0;
      results.push({
        id: `selector-result:${selector.id}`,
        kind: "selector",
        title: selector.name,
        detail: `${selector.gateIds.length} gates · ${selector.lookupIds.length} lookups`,
        row: firstRow,
        columnId: selector.id,
      });
    }
    for (const region of data.regions) {
      const haystack = [
        region.id,
        region.name,
        region.componentId,
        ...region.namespace,
      ].filter(Boolean).join(" ").toLocaleLowerCase();
      if (!haystack.includes(query)) continue;
      results.push({
        id: `region-result:${region.id}`,
        kind: "region",
        title: region.name,
        detail: `Row ${region.startRow}${region.componentId ? ` · ${region.componentId}` : ""}`,
        row: region.startRow,
      });
    }
    const components = new Map<string, CircuitGridRegion[]>();
    for (const region of data.regions) {
      if (!region.componentId) continue;
      const related = components.get(region.componentId) ?? [];
      related.push(region);
      components.set(region.componentId, related);
    }
    for (const [componentId, regions] of components) {
      if (!componentId.toLocaleLowerCase().includes(query)) continue;
      results.push({
        id: `component-result:${componentId}`,
        kind: "component",
        title: componentId,
        detail: `${regions.length} region${regions.length === 1 ? "" : "s"}`,
        row: Math.min(...regions.map(({ startRow }) => startRow)),
      });
    }
    return uniqueById(results).slice(0, limit);
  };

  return {
    data,
    tracks,
    rowsWithData,
    regionStarts,
    cell,
    rowEvents,
    rowRegions,
    search,
  };
}
