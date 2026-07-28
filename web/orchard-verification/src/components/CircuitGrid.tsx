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
  clearCircuitGridDataCache,
  loadCircuitGridData,
} from "../circuit-grid/loader";
import type {
  CircuitGridCellProjection,
  CircuitGridData,
  CircuitGridEvent,
  CircuitGridSearchResult,
  CircuitGridSelection,
  CircuitGridTarget,
} from "../circuit-grid/model";
import {
  createCircuitGridProjection,
  type CircuitGridProjection,
} from "../circuit-grid/projector";
import { type DataLoader, useLoadableData } from "../hooks/useLoadableData";
import { useMediaQuery } from "../hooks/useMediaQuery";

const ROW_HEIGHT = 32;
const OVERSCAN_ROWS = 8;
const DEFAULT_VIEWPORT_HEIGHT = 620;
const REGION_COLUMN_WIDTH_REM = 10.5;
const ROW_NUMBER_COLUMN_WIDTH_REM = 3.5;

interface HoverPreview {
  readonly cell: CircuitGridCellProjection;
  readonly left: number;
  readonly top: number;
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
    .trim()
    .replace(/\b\w/g, (letter) => letter.toUpperCase());
}

export function parseCircuitGridHash(
  hash = typeof window === "undefined" ? "" : window.location.hash,
): CircuitGridSelection | null {
  const parameters = new URLSearchParams(hash.replace(/^#/, ""));
  const row = Number(parameters.get("row"));
  const columnId = parameters.get("column");
  return Number.isInteger(row) && row >= 0 && columnId
    ? { row, columnId }
    : null;
}

function selectionHash(selection: CircuitGridSelection | null): string {
  if (!selection) return "";
  const parameters = new URLSearchParams();
  parameters.set("row", String(selection.row));
  parameters.set("column", selection.columnId);
  return `#${parameters.toString()}`;
}

function cellName(cell: CircuitGridCellProjection): string {
  return `Row ${cell.row} · ${cell.track.label}`;
}

function cellDescription(cell: CircuitGridCellProjection): string {
  const activity = cell.marks.length
    ? cell.marks.map(({ label }) => label).join("; ")
    : "No activity recorded";
  const regions = cell.regions.length
    ? ` Region: ${cell.regions.map(({ name }) => name).join(", ")}.`
    : "";
  return `${cellName(cell)}. ${activity}.${regions}`;
}

function eventSummary(event: CircuitGridEvent): string {
  const location = event.endpoints.length
    ? event.endpoints.map(({ columnId, row }) => `${columnId} row ${row}`).join(" ↔ ")
    : [
        event.columnId,
        event.row === undefined ? null : `row ${event.row}`,
      ].filter(Boolean).join(" · ");
  return [
    event.annotation,
    location,
    event.value === undefined ? null : `Value ${event.value}`,
  ].filter(Boolean).join(" · ");
}

function targetLabel(target: CircuitGridTarget): string {
  const base = target.title.trim();
  const action = /^open\b/i.test(base) ? base : `Open ${base}`;
  const kind = target.kind === "other" || new RegExp(`\\b${target.kind}\\b`, "i").test(action)
    ? ""
    : ` ${target.kind}`;
  return `${action}${kind} in Circuit`;
}

function SelectionInspector({
  cell,
  narrow,
  onClose,
  onMove,
}: {
  readonly cell: CircuitGridCellProjection;
  readonly narrow: boolean;
  readonly onClose: () => void;
  readonly onMove: (selection: CircuitGridSelection) => void;
}) {
  const closeRef = useRef<HTMLButtonElement>(null);
  useEffect(() => {
    if (narrow) closeRef.current?.focus();
  }, [narrow, cell.row, cell.track.id]);

  const peers = cell.marks.flatMap(({ peer }) => peer ? [peer] : []);
  const activities = [...new Map(
    cell.marks.map((activity) => [activity.event.id, activity]),
  ).values()];

  return (
    <aside
      className={classNames("circuit-grid-inspector", narrow && "is-drawer")}
      id="circuit-grid-inspector"
      aria-label="Cell details"
    >
      <div className="circuit-grid-inspector__heading">
        <div>
          <p className="context-label">Cell details</p>
          <h2>{cellName(cell)}</h2>
        </div>
        <button ref={closeRef} type="button" aria-label="Close cell details" onClick={onClose}>
          ×
        </button>
      </div>
      <dl className="circuit-grid-inspector__facts">
        <div><dt>Row</dt><dd>{cell.row.toLocaleString("en-US")}</dd></div>
        <div><dt>Track</dt><dd><code>{cell.track.id}</code></dd></div>
        <div><dt>Type</dt><dd>{titleCase(cell.track.kind)}</dd></div>
        <div><dt>Events</dt><dd>{activities.length}</dd></div>
      </dl>

      {activities.length ? (
        <section className="circuit-grid-inspector__section">
          <h3>Recorded activity</h3>
          <ul className="circuit-grid-inspector__events">
            {activities.map(({ event, selector }) => (
              <li key={event.id}>
                <strong>
                  {titleCase(event.kind)}
                  {selector ? ` · ${selector.name}` : ""}
                </strong>
                <p>
                  {selector ? (
                    <span className="circuit-grid-inspector__selector-id">
                      {selector.id}
                    </span>
                  ) : null}
                  {selector && eventSummary(event) ? " · " : null}
                  {eventSummary(event) ||
                    (selector
                      ? "Activated in the structural parity trace."
                      : "Recorded by the structural parity trace.")}
                </p>
                <code title={event.id}>{event.id}</code>
              </li>
            ))}
          </ul>
        </section>
      ) : (
        <p className="circuit-grid-inspector__empty">
          No activity is recorded at this coordinate. Blank advice cells mean
          “not present in this structural trace,” not “unassigned.”
        </p>
      )}

      {peers.length ? (
        <section className="circuit-grid-inspector__section">
          <h3>Copy peers</h3>
          <ul className="circuit-grid-inspector__links">
            {peers.map((peer, index) => (
              <li key={`${peer.columnId}:${peer.row}:${index}`}>
                <button
                  type="button"
                  onClick={() => onMove({ row: peer.row, columnId: peer.columnId })}
                >
                  <span>{peer.columnId}</span>
                  <strong>Row {peer.row}</strong>
                  <span aria-hidden="true">→</span>
                </button>
              </li>
            ))}
          </ul>
        </section>
      ) : null}

      {cell.regions.length ? (
        <section className="circuit-grid-inspector__section">
          <h3>Regions at this row</h3>
          <ul className="circuit-grid-inspector__regions">
            {cell.regions.map((region) => (
              <li key={region.id}>
                <strong>{region.name}</strong>
                <span>
                  Row {region.startRow}
                  {region.endRow === undefined ? "" : `–${region.endRow}`}
                </span>
                {region.namespace.length ? <code>{region.namespace.join(" / ")}</code> : null}
              </li>
            ))}
          </ul>
        </section>
      ) : null}

      {cell.targets.length ? (
        <section className="circuit-grid-inspector__section">
          <h3>Explore in Circuit</h3>
          <ul className="circuit-grid-inspector__targets">
            {cell.targets.map((target) => (
              <li key={target.id}>
                <a href={target.href}>
                  <span>{targetLabel(target)}</span>
                  <span aria-hidden="true">↗</span>
                </a>
              </li>
            ))}
          </ul>
        </section>
      ) : null}
    </aside>
  );
}

function HoverCard({ preview }: { readonly preview: HoverPreview }) {
  return (
    <div
      className="circuit-grid-tooltip"
      role="tooltip"
      style={{ left: preview.left, top: preview.top }}
    >
      <strong>{cellName(preview.cell)}</strong>{"\n"}
      <span>{titleCase(preview.cell.track.kind)}</span>{"\n"}
      {preview.cell.marks.length ? (
        preview.cell.marks.slice(0, 4).map((mark) => (
          <p key={mark.id}>{mark.label}{"\n"}</p>
        ))
      ) : <p>No activity recorded in the structural trace.{"\n"}</p>}
      {preview.cell.marks.length > 4 ? (
        <p>+ {preview.cell.marks.length - 4} more stacked events{"\n"}</p>
      ) : null}
      {preview.cell.regions.slice(0, 2).map((region) => (
        <p key={region.id}>Region · {region.name}{"\n"}</p>
      ))}
    </div>
  );
}

function SearchToolbar({
  projection,
  query,
  results,
  selectorsExpanded,
  onQuery,
  onChoose,
  onToggleSelectors,
}: {
  readonly projection: CircuitGridProjection;
  readonly query: string;
  readonly results: readonly CircuitGridSearchResult[];
  readonly selectorsExpanded: boolean;
  readonly onQuery: (query: string) => void;
  readonly onChoose: (result: CircuitGridSearchResult) => void;
  readonly onToggleSelectors: () => void;
}) {
  const [open, setOpen] = useState(false);
  return (
    <section className="circuit-grid-toolbar" aria-label="Grid controls">
      <div className="circuit-grid-search">
        <label htmlFor="circuit-grid-search">Search circuit grid</label>
        <input
          id="circuit-grid-search"
          type="search"
          aria-label="Search circuit grid"
          autoComplete="off"
          placeholder="Row, region, component, selector…"
          value={query}
          aria-controls={open && query ? "circuit-grid-search-results" : undefined}
          onFocus={() => setOpen(true)}
          onBlur={() => window.setTimeout(() => setOpen(false), 100)}
          onChange={(event) => {
            onQuery(event.currentTarget.value);
            setOpen(true);
          }}
          onKeyDown={(event) => {
            if (event.key === "Escape") {
              event.preventDefault();
              event.stopPropagation();
              setOpen(false);
              onQuery("");
            } else if (event.key === "Enter" && results[0]) {
              event.preventDefault();
              onChoose(results[0]);
              setOpen(false);
            }
          }}
        />
        <p aria-live="polite">
          {query
            ? `${results.length} suggested result${results.length === 1 ? "" : "s"}`
            : `Rows 0–${projection.data.metadata.circuit.rowCount - 1}`}
        </p>
        {open && query ? (
          <div className="circuit-grid-search__results" id="circuit-grid-search-results">
            {results.length ? (
              <ul>
                {results.map((result) => (
                  <li key={result.id}>
                    <button
                      type="button"
                      onMouseDown={(event) => event.preventDefault()}
                      onClick={() => {
                        onChoose(result);
                        setOpen(false);
                      }}
                    >
                      <span>{titleCase(result.kind)}</span>
                      <strong>{result.title}</strong>
                      <small>{result.detail}</small>
                    </button>
                  </li>
                ))}
              </ul>
            ) : <p>No grid records match “{query}”.</p>}
          </div>
        ) : null}
      </div>
      <button
        className="circuit-grid-selector-toggle"
        type="button"
        aria-pressed={selectorsExpanded}
        onClick={onToggleSelectors}
      >
        {selectorsExpanded
          ? `Collapse ${projection.data.selectors.length} selectors`
          : `Expand ${projection.data.selectors.length} selectors`}
      </button>
    </section>
  );
}

function GridCanvas({
  projection,
  selection,
  onSelect,
  onPreview,
}: {
  readonly projection: CircuitGridProjection;
  readonly selection: CircuitGridSelection | null;
  readonly onSelect: (selection: CircuitGridSelection) => void;
  readonly onPreview: (preview: HoverPreview | null) => void;
}) {
  const viewportRef = useRef<HTMLDivElement>(null);
  const cellRefs = useRef(new Map<string, HTMLButtonElement>());
  const [scrollTop, setScrollTop] = useState(0);
  const [viewportHeight, setViewportHeight] = useState(DEFAULT_VIEWPORT_HEIGHT);
  const [active, setActive] = useState<CircuitGridSelection>(() => ({
    row: selection?.row ?? 0,
    columnId: selection?.columnId ?? projection.tracks[0]?.id ?? "",
  }));
  const rowCount = projection.data.metadata.circuit.rowCount;
  const startRow = Math.max(0, Math.floor(scrollTop / ROW_HEIGHT) - OVERSCAN_ROWS);
  const endRow = Math.min(
    rowCount - 1,
    Math.ceil((scrollTop + viewportHeight) / ROW_HEIGHT) + OVERSCAN_ROWS,
  );
  const visibleRows = Array.from(
    { length: Math.max(0, endRow - startRow + 1) },
    (_, index) => startRow + index,
  );
  const gridTemplateColumns =
    `${REGION_COLUMN_WIDTH_REM}rem ${ROW_NUMBER_COLUMN_WIDTH_REM}rem ` +
    `repeat(${projection.tracks.length}, 3rem)`;
  const effectiveActive = active.row >= startRow && active.row <= endRow
    ? active
    : { row: startRow, columnId: projection.tracks[0]?.id ?? "" };

  useEffect(() => {
    const viewport = viewportRef.current;
    if (!viewport) return;
    setViewportHeight(viewport.clientHeight || DEFAULT_VIEWPORT_HEIGHT);
    if (typeof ResizeObserver === "undefined") return;
    const observer = new ResizeObserver(([entry]) => {
      if (entry) setViewportHeight(entry.contentRect.height);
    });
    observer.observe(viewport);
    return () => observer.disconnect();
  }, []);

  const reveal = useCallback((next: CircuitGridSelection, focus = true) => {
    const viewport = viewportRef.current;
    if (!viewport) return;
    const top = next.row * ROW_HEIGHT;
    const bottom = top + ROW_HEIGHT;
    if (top < viewport.scrollTop + ROW_HEIGHT) {
      viewport.scrollTop = Math.max(0, top - ROW_HEIGHT * 2);
    } else if (bottom > viewport.scrollTop + viewport.clientHeight) {
      viewport.scrollTop = Math.max(0, bottom - viewport.clientHeight + ROW_HEIGHT * 2);
    }
    setScrollTop(viewport.scrollTop);
    setActive(next);
    window.requestAnimationFrame(() => {
      window.requestAnimationFrame(() => {
        const cell = cellRefs.current.get(`${next.row}:${next.columnId}`);
        if (!cell) return;
        const row = cell.closest<HTMLElement>(".circuit-grid-row");
        const stickyWidth = [
          row?.querySelector<HTMLElement>(".circuit-grid-region-cell"),
          row?.querySelector<HTMLElement>(".circuit-grid-row-number"),
        ].reduce((width, element) => width + (element?.offsetWidth ?? 0), 0);
        const left = cell.offsetLeft;
        const right = left + cell.offsetWidth;
        if (left < viewport.scrollLeft + stickyWidth) {
          viewport.scrollLeft = Math.max(0, left - stickyWidth);
        } else if (right > viewport.scrollLeft + viewport.clientWidth) {
          viewport.scrollLeft = right - viewport.clientWidth + 8;
        }
        const bounds = cell.getBoundingClientRect();
        if (bounds.top < 72 || bounds.bottom > window.innerHeight) {
          cell.scrollIntoView({ block: "center", inline: "nearest" });
        }
        if (focus) cell.focus();
      });
    });
  }, []);

  useEffect(() => {
    if (selection) reveal(selection, false);
  }, [selection?.row, selection?.columnId, reveal]);

  const handleKey = (
    event: ReactKeyboardEvent<HTMLButtonElement>,
    row: number,
    columnIndex: number,
  ) => {
    let nextRow = row;
    let nextColumn = columnIndex;
    switch (event.key) {
      case "ArrowUp": nextRow -= 1; break;
      case "ArrowDown": nextRow += 1; break;
      case "ArrowLeft": nextColumn -= 1; break;
      case "ArrowRight": nextColumn += 1; break;
      case "PageUp": nextRow -= Math.max(1, Math.floor(viewportHeight / ROW_HEIGHT) - 1); break;
      case "PageDown": nextRow += Math.max(1, Math.floor(viewportHeight / ROW_HEIGHT) - 1); break;
      case "Home":
        if (event.ctrlKey || event.metaKey) nextRow = 0;
        nextColumn = 0;
        break;
      case "End":
        if (event.ctrlKey || event.metaKey) nextRow = rowCount - 1;
        nextColumn = projection.tracks.length - 1;
        break;
      case "Enter":
      case " ":
        event.preventDefault();
        onSelect({ row, columnId: projection.tracks[columnIndex]?.id ?? "" });
        return;
      default:
        return;
    }
    event.preventDefault();
    nextRow = Math.min(rowCount - 1, Math.max(0, nextRow));
    nextColumn = Math.min(projection.tracks.length - 1, Math.max(0, nextColumn));
    reveal({ row: nextRow, columnId: projection.tracks[nextColumn]?.id ?? "" });
  };

  return (
    <div
      ref={viewportRef}
      className="circuit-grid-scroll"
      role="region"
      aria-label="Circuit grid"
      data-track-count={projection.tracks.length}
      onScroll={(event) => {
        setScrollTop(event.currentTarget.scrollTop);
        onPreview(null);
      }}
    >
      <div
        className="circuit-grid-sheet"
        role="grid"
        data-track-count={projection.tracks.length}
        aria-label={`${projection.data.metadata.circuit.name} structural placement`}
        aria-rowcount={rowCount + 1}
        aria-colcount={projection.tracks.length + 2}
        style={{
          "--circuit-grid-region-width": `${REGION_COLUMN_WIDTH_REM}rem`,
          "--circuit-grid-width":
            `${REGION_COLUMN_WIDTH_REM + ROW_NUMBER_COLUMN_WIDTH_REM + 2 +
              projection.tracks.length * 3}rem`,
        } as CSSProperties}
      >
        <div
          className="circuit-grid-header"
          role="row"
          style={{ gridTemplateColumns }}
        >
          <div role="columnheader">Region start</div>
          <div role="columnheader">Row</div>
          {projection.tracks.map((track) => (
            <div
              key={track.id}
              role="columnheader"
              title={track.description}
              className={`is-${track.kind}`}
            >
              <span>{track.label}</span>
            </div>
          ))}
        </div>
        <div
          className="circuit-grid-virtual-body"
          style={{ height: rowCount * ROW_HEIGHT }}
        >
          {visibleRows.map((row) => {
            const startRegions = projection.regionStarts.get(row) ?? [];
            const rowRegions = projection.rowRegions(row);
            return (
              <div
                className={classNames(
                  "circuit-grid-row",
                  startRegions.length > 0 && "has-region-start",
                  rowRegions.length > 0 && "is-in-region",
                )}
                key={row}
                role="row"
                aria-rowindex={row + 2}
                style={{
                  gridTemplateColumns,
                  transform: `translateY(${row * ROW_HEIGHT}px)`,
                }}
              >
                <button
                  type="button"
                  role="gridcell"
                  aria-label={
                    startRegions.length
                      ? `Row ${row} region start: ${startRegions.map(({ name }) => name).join(", ")}`
                      : `Row ${row} region gutter`
                  }
                  className="circuit-grid-region-cell"
                  title={startRegions.map(({ name }) => name).join(", ") || undefined}
                  tabIndex={-1}
                  onClick={() => onSelect({
                    row,
                    columnId: projection.tracks[0]?.id ?? "",
                  })}
                >
                  {startRegions.length ? (
                    <>
                      <span>{startRegions[0]?.name}</span>
                      {startRegions.length > 1 ? <strong>+{startRegions.length - 1}</strong> : null}
                    </>
                  ) : <span aria-hidden="true" />}
                </button>
                <div className="circuit-grid-row-number" role="rowheader">{row}</div>
                {projection.tracks.map((track, columnIndex) => {
                  const cell = projection.cell(row, track.id);
                  const selected = selection?.row === row &&
                    selection.columnId === track.id;
                  const activeCell = effectiveActive.row === row &&
                    effectiveActive.columnId === track.id;
                  const primaryKind = cell.marks[0]?.kind;
                  return (
                    <button
                      key={track.id}
                      ref={(node) => {
                        const key = `${row}:${track.id}`;
                        if (node) cellRefs.current.set(key, node);
                        else cellRefs.current.delete(key);
                      }}
                      type="button"
                      role="gridcell"
                      aria-label={cellDescription(cell)}
                      aria-selected={selected || undefined}
                      data-row={row}
                      data-column={track.id}
                      data-event-count={cell.marks.length}
                      className={classNames(
                        "circuit-grid-cell",
                        primaryKind && `has-${primaryKind}`,
                        cell.marks.length > 1 && "has-stacked-events",
                        selected && "is-selected",
                      )}
                      tabIndex={activeCell ? 0 : -1}
                      onFocus={(event) => {
                        setActive({ row, columnId: track.id });
                        const bounds = event.currentTarget.getBoundingClientRect();
                        onPreview({
                          cell,
                          left: Math.min(window.innerWidth - 300, Math.max(8, bounds.left)),
                          top: Math.min(window.innerHeight - 180, bounds.bottom + 8),
                        });
                      }}
                      onBlur={() => onPreview(null)}
                      onMouseEnter={(event) => {
                        const bounds = event.currentTarget.getBoundingClientRect();
                        onPreview({
                          cell,
                          left: Math.min(window.innerWidth - 300, Math.max(8, bounds.left)),
                          top: Math.min(window.innerHeight - 180, bounds.bottom + 8),
                        });
                      }}
                      onMouseLeave={() => onPreview(null)}
                      onClick={() => onSelect({ row, columnId: track.id })}
                      onKeyDown={(event) => handleKey(event, row, columnIndex)}
                    >
                      {cell.marks.length ? (
                        <>
                          <span className="circuit-grid-cell__mark" aria-hidden="true" />
                          {cell.marks.length > 1 ? (
                            <span className="circuit-grid-cell__count" aria-hidden="true">
                              {cell.marks.length}
                            </span>
                          ) : null}
                        </>
                      ) : null}
                    </button>
                  );
                })}
              </div>
            );
          })}
        </div>
      </div>
    </div>
  );
}

function LoadingGrid() {
  return (
    <main id="main-content" className="circuit-grid-page" tabIndex={-1}>
      <section className="circuit-grid-state" aria-live="polite">
        <span className="circuit-grid-state__spinner" aria-hidden="true" />
        <h1>Loading circuit grid</h1>
        <p>Reading the checked structural parity trace…</p>
      </section>
    </main>
  );
}

function GridError({
  message,
  onRetry,
}: {
  readonly message: string;
  readonly onRetry: () => void;
}) {
  return (
    <main id="main-content" className="circuit-grid-page" tabIndex={-1}>
      <section className="circuit-grid-state circuit-grid-state--error" role="alert">
        <p className="eyebrow">Circuit grid unavailable</p>
        <h1>The structural trace could not be loaded</h1>
        <p>{message}</p>
        <button type="button" onClick={onRetry}>Retry</button>
      </section>
    </main>
  );
}

export function CircuitGrid({
  loader = loadCircuitGridData,
}: {
  readonly loader?: DataLoader<CircuitGridData>;
}) {
  const narrow = useMediaQuery("(max-width: 760px)");
  const { data, error: loadError, retry } = useLoadableData(
    loader,
    "Unknown grid data error",
  );
  const [selection, setSelection] = useState<CircuitGridSelection | null>(
    () => parseCircuitGridHash(),
  );
  const [selectorsExpanded, setSelectorsExpanded] = useState(
    () => parseCircuitGridHash()?.columnId.startsWith("selector:") ?? false,
  );
  const [query, setQuery] = useState("");
  const [preview, setPreview] = useState<HoverPreview | null>(null);
  const selectionOriginRef = useRef<HTMLElement | null>(null);

  useEffect(() => {
    const restore = () => {
      const restored = parseCircuitGridHash();
      setSelection(restored);
      if (restored?.columnId.startsWith("selector:")) setSelectorsExpanded(true);
    };
    window.addEventListener("hashchange", restore);
    window.addEventListener("popstate", restore);
    return () => {
      window.removeEventListener("hashchange", restore);
      window.removeEventListener("popstate", restore);
    };
  }, []);

  const projection = useMemo(
    () => data ? createCircuitGridProjection(data, selectorsExpanded) : null,
    [data, selectorsExpanded],
  );
  const results = useMemo(
    () => projection?.search(query) ?? [],
    [projection, query],
  );

  const commitSelection = useCallback((next: CircuitGridSelection) => {
    const activeElement = document.activeElement;
    if (
      activeElement instanceof HTMLElement &&
      !activeElement.closest("#circuit-grid-inspector")
    ) {
      selectionOriginRef.current = activeElement;
    }
    setSelection(next);
    setPreview(null);
    if (next.columnId.startsWith("selector:")) setSelectorsExpanded(true);
    window.history.pushState(null, "", selectionHash(next));
  }, []);

  const closeSelection = useCallback(() => {
    const origin = selectionOriginRef.current;
    setSelection(null);
    setPreview(null);
    window.history.pushState(null, "", `${window.location.pathname}${window.location.search}`);
    window.requestAnimationFrame(() => {
      if (origin?.isConnected) origin.focus();
    });
  }, []);

  useEffect(() => {
    if (!selection) return;
    const closeOnEscape = (event: KeyboardEvent) => {
      if (event.key !== "Escape" || event.defaultPrevented) return;
      event.preventDefault();
      closeSelection();
    };
    document.addEventListener("keydown", closeOnEscape);
    return () => document.removeEventListener("keydown", closeOnEscape);
  }, [selection, closeSelection]);

  if (loadError) {
    return (
      <GridError
        message={loadError}
        onRetry={() => {
          clearCircuitGridDataCache();
          retry();
        }}
      />
    );
  }
  if (!data || !projection) return <LoadingGrid />;

  const validSelection = selection &&
    selection.row < data.metadata.circuit.rowCount &&
    projection.tracks.some(({ id }) => id === selection.columnId)
    ? selection
    : null;
  const selectedCell = validSelection
    ? projection.cell(validSelection.row, validSelection.columnId)
    : null;

  const chooseSearchResult = (result: CircuitGridSearchResult) => {
    if (result.columnId?.startsWith("selector:")) setSelectorsExpanded(true);
    commitSelection({
      row: result.row,
      columnId: result.columnId ??
        projection.tracks[0]?.id ??
        "",
    });
  };

  return (
    <main id="main-content" className="circuit-grid-page" tabIndex={-1}>
      <section className="circuit-grid-intro" aria-labelledby="circuit-grid-title">
        <div>
          <p className="eyebrow">V1 placement · before selector compression</p>
          <h1 id="circuit-grid-title">Orchard Circuit Grid</h1>
          <p>
            Explore the checked structural layout of the unoptimized Orchard
            Action circuit across physical columns, virtual selectors, regions,
            fixed assignments, and permutation copy edges.
          </p>
          <p className="circuit-grid-coverage" role="note">
            <strong>Trace coverage:</strong>{" "}
            {`Advice assignments are ${data.metadata.capabilities.adviceAssignments}; ordinary witness assignments are not recorded by this structural trace. Witness values are ${data.metadata.capabilities.witnessValues}. Blank advice cells do not assert that a cell is unassigned.`}
          </p>
        </div>
        <dl className="circuit-grid-metrics">
          <div><dt>Rows</dt><dd>{data.metadata.circuit.rowCount.toLocaleString("en-US")}</dd></div>
          <div><dt>Physical columns</dt><dd>{data.columns.length}</dd></div>
          <div><dt>Virtual selectors</dt><dd>{data.selectors.length}</dd></div>
          <div><dt>Exact regions</dt><dd>{data.regions.length}</dd></div>
        </dl>
      </section>

      <p className="circuit-grid-context">
        {data.metadata.circuit.version} · k = {data.metadata.circuit.k} ·{" "}
        {data.metadata.circuit.floorPlanner} floor planner
      </p>

      <SearchToolbar
        projection={projection}
        query={query}
        results={results}
        selectorsExpanded={selectorsExpanded}
        onQuery={setQuery}
        onChoose={chooseSearchResult}
        onToggleSelectors={() => {
          if (selectorsExpanded && selection?.columnId.startsWith("selector:")) {
            const collapsedSelection = {
              row: selection.row,
              columnId: "selectors:collapsed",
            };
            setSelection(collapsedSelection);
            window.history.replaceState(null, "", selectionHash(collapsedSelection));
          } else if (
            !selectorsExpanded &&
            selection?.columnId === "selectors:collapsed"
          ) {
            const expandedColumnId = projection
              .cell(selection.row, "selectors:collapsed")
              .marks.find(({ selector }) => selector)?.selector?.id ??
              data.selectors[0]?.id;
            if (expandedColumnId) {
              const expandedSelection = {
                row: selection.row,
                columnId: expandedColumnId,
              };
              setSelection(expandedSelection);
              window.history.replaceState(null, "", selectionHash(expandedSelection));
            }
          }
          setSelectorsExpanded((current) => !current);
        }}
      />

      <section
        className={classNames(
          "circuit-grid-workspace",
          selectedCell && "has-inspector",
        )}
      >
        <div className="circuit-grid-primary">
          <ul className="circuit-grid-legend" aria-label="Grid activity legend">
            <li className="is-selector">Selector</li>
            <li className="is-fixed">Fixed assignment</li>
            <li className="is-copy">Copy endpoint</li>
            <li className="is-public">Public / constant</li>
            <li className="is-advice">Advice reference</li>
          </ul>
          <GridCanvas
            projection={projection}
            selection={validSelection}
            onSelect={commitSelection}
            onPreview={setPreview}
          />
        </div>
        {narrow && selectedCell ? (
          <button
            className="circuit-grid-inspector-backdrop"
            type="button"
            aria-label="Close cell details"
            onClick={closeSelection}
          />
        ) : null}
        {selectedCell ? (
          <SelectionInspector
            cell={selectedCell}
            narrow={narrow}
            onClose={closeSelection}
            onMove={commitSelection}
          />
        ) : null}
      </section>

      {preview ? <HoverCard preview={preview} /> : null}
      <p className="visually-hidden" aria-live="polite">
        {selectedCell ? `${cellName(selectedCell)} selected.` : "No grid cell selected."}
      </p>
    </main>
  );
}
