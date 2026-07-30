#!/usr/bin/env python3
"""Generate the deterministic parity-backed Orchard circuit-grid artifact.

The grid is intentionally a structural view of the V1 placement trace.  The
Rocq model and Rust implementation snapshots must compare equal as parsed JSON
before any data is emitted.  The source-enriched Circuit Explorer artifact
supplies stable names, region identities, and deep links; it is not used to
decide parity.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Mapping, MutableMapping, Sequence
from urllib.parse import urlencode


OUTPUT_SCHEMA = "garden.halo2.circuit-grid.v1"
EXPLORER_SCHEMA = "garden.orchard.circuit-highlevel.v1"
GENERATOR_NAME = "scripts/generate_orchard_circuit_grid.py"
GENERATOR_VERSION = "1.0.0"

SCRIPT_PATH = Path(__file__).resolve()
DEFAULT_GARDEN_ROOT = SCRIPT_PATH.parent.parent
DEFAULT_SNAPSHOT_ROOT = DEFAULT_GARDEN_ROOT / "Garden" / "Orchard" / "Snapshots"
DEFAULT_CONFIGURE_MODEL = (
    DEFAULT_SNAPSHOT_ROOT / "circuit_configure_generated_from_model.json"
)
DEFAULT_CONFIGURE_IMPLEMENTATION = (
    DEFAULT_SNAPSHOT_ROOT / "circuit_configure_generated_from_implementation.json"
)
DEFAULT_SYNTHESIS_MODEL = (
    DEFAULT_SNAPSHOT_ROOT / "circuit_synthesis_generated_from_model.json"
)
DEFAULT_SYNTHESIS_IMPLEMENTATION = (
    DEFAULT_SNAPSHOT_ROOT / "circuit_synthesis_generated_from_implementation.json"
)
DEFAULT_EXPLORER = (
    DEFAULT_GARDEN_ROOT
    / "web"
    / "orchard-verification"
    / "public"
    / "data"
    / "orchard-circuit-highlevel.v1.json"
)
DEFAULT_OUTPUT = (
    DEFAULT_GARDEN_ROOT
    / "web"
    / "orchard-verification"
    / "public"
    / "data"
    / "orchard-circuit-grid.v1.json"
)


class GenerationError(RuntimeError):
    """A deterministic generation or validation failure."""


def read_json(path: Path) -> tuple[Any, bytes]:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise GenerationError(f"cannot read {path}: {error}") from error
    try:
        return json.loads(raw), raw
    except json.JSONDecodeError as error:
        raise GenerationError(f"malformed JSON in {path}: {error}") from error


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, separators=(",", ":")) + "\n"
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def integer(value: Any, *, label: str) -> int:
    try:
        parsed = int(value)
    except (TypeError, ValueError) as error:
        raise GenerationError(f"{label} must be an integer, got {value!r}") from error
    return parsed


def relative_path(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError as error:
        raise GenerationError(f"input {path} is outside Garden root {root}") from error


def circuit_target(
    item_id: str,
    *,
    kind: str,
    title: str,
    focus_id: str | None = None,
) -> dict[str, str]:
    parameters: list[tuple[str, str]] = [("level", "detail"), ("item", item_id)]
    if focus_id is not None:
        parameters.append(("focus", focus_id))
    suffix = f":{focus_id}" if focus_id else ""
    return {
        "id": f"target:{item_id}{suffix}",
        "kind": kind,
        "title": title,
        "href": f"circuit.html#{urlencode(parameters)}",
    }


def normalized_column_kind(value: Any) -> str:
    normalized = str(value).casefold().rstrip("_")
    if normalized == "instance":
        return "instance"
    if normalized == "fixed":
        return "fixed"
    if normalized == "advice":
        return "advice"
    raise GenerationError(f"unknown circuit column kind: {value!r}")


def column_id(kind: Any, index: Any) -> str:
    return f"{normalized_column_kind(kind)}:{integer(index, label='column index')}"


def endpoint_from_trace(value: Mapping[str, Any]) -> dict[str, Any]:
    column = value.get("column")
    if not isinstance(column, Mapping):
        raise GenerationError(f"copy endpoint has no column: {value!r}")
    return {
        "columnId": column_id(column.get("kind"), column.get("index")),
        "row": integer(value.get("row"), label="copy row"),
    }


def endpoint_from_explorer(value: Mapping[str, Any]) -> dict[str, Any] | None:
    column = value.get("column")
    if not isinstance(column, Mapping):
        return None
    absolute_row = value.get("absolute_row", value.get("absoluteRow", value.get("row")))
    if absolute_row is None:
        return None
    return {
        "columnId": column_id(column.get("kind"), column.get("index")),
        "row": integer(absolute_row, label="explorer cell row"),
    }


def endpoint_key(endpoint: Mapping[str, Any]) -> tuple[str, int]:
    return (str(endpoint["columnId"]), integer(endpoint["row"], label="endpoint row"))


def copy_key(
    left: Mapping[str, Any],
    right: Mapping[str, Any],
) -> tuple[tuple[str, int], tuple[str, int]]:
    return tuple(sorted((endpoint_key(left), endpoint_key(right))))  # type: ignore[return-value]


def target_key(target: Mapping[str, Any]) -> str:
    return str(target["id"])


def add_target(
    targets: MutableMapping[str, dict[str, str]],
    target: dict[str, str] | None,
) -> dict[str, str] | None:
    if target is None:
        return None
    target_id = target_key(target)
    previous = targets.get(target_id)
    if previous is not None and previous != target:
        raise GenerationError(f"conflicting circuit target {target_id}")
    targets[target_id] = target
    return target


def ensure_parity(
    configure_model: Mapping[str, Any],
    configure_implementation: Mapping[str, Any],
    synthesis_model: Mapping[str, Any],
    synthesis_implementation: Mapping[str, Any],
) -> tuple[list[dict[str, Any]], Mapping[str, Any]]:
    model_configure = configure_model.get("configure")
    implementation_configure = configure_implementation.get("configure")
    if model_configure != implementation_configure:
        raise GenerationError(
            "configure parity mismatch between Rocq model and Rust implementation"
        )
    model_events = synthesis_model.get("events")
    implementation_events = synthesis_implementation.get("events")
    if model_events != implementation_events:
        raise GenerationError(
            "synthesis parity mismatch between Rocq model and Rust implementation"
        )
    if not isinstance(model_configure, Mapping):
        raise GenerationError("configure snapshot is missing its configure object")
    if not isinstance(model_events, list) or not all(
        isinstance(event, Mapping) for event in model_events
    ):
        raise GenerationError("synthesis snapshot is missing its event list")
    return [dict(event) for event in model_events], model_configure


def build_columns(explorer: Mapping[str, Any]) -> list[dict[str, Any]]:
    metadata = explorer.get("metadata")
    if not isinstance(metadata, Mapping):
        raise GenerationError("Circuit Explorer artifact is missing metadata")
    symbols = metadata.get("symbols")
    if not isinstance(symbols, Mapping):
        raise GenerationError("Circuit Explorer artifact is missing symbols")
    raw_columns = symbols.get("columns")
    if not isinstance(raw_columns, Mapping):
        raise GenerationError("Circuit Explorer artifact is missing column symbols")

    columns: list[dict[str, Any]] = []
    specifications = (
        ("instance", 1, "instance", "public input"),
        ("advice", 10, "advice", "referenced advice"),
        ("lookup", 3, "fixed", "lookup table"),
        ("fixed", 11, "fixed", "fixed"),
    )
    for symbol_kind, count, output_kind, role in specifications:
        values = raw_columns.get(symbol_kind)
        if not isinstance(values, Mapping):
            raise GenerationError(f"missing {symbol_kind} column symbols")
        expected_indices = range(0, count) if symbol_kind != "fixed" else range(3, 14)
        for index in expected_indices:
            name = values.get(str(index))
            if not isinstance(name, str) or not name:
                raise GenerationError(
                    f"missing display name for {symbol_kind} column {index}"
                )
            columns.append(
                {
                    "id": f"{output_kind}:{index}",
                    "kind": output_kind,
                    "index": index,
                    "name": name,
                    "role": role,
                }
            )
    if len(columns) != 25 or len({item["id"] for item in columns}) != 25:
        raise GenerationError("expected exactly 25 distinct physical columns")
    return columns


def build_selectors(
    explorer: Mapping[str, Any],
    targets: MutableMapping[str, dict[str, str]],
) -> list[dict[str, Any]]:
    metadata = explorer.get("metadata", {})
    raw_selectors = metadata.get("symbols", {}).get("selectors", {})
    configure = explorer.get("configure", {})
    gates = configure.get("gates", [])
    lookups = configure.get("lookups", [])
    if not isinstance(raw_selectors, Mapping):
        raise GenerationError("Circuit Explorer artifact is missing selector symbols")

    gate_by_id = {
        str(gate["id"]): gate
        for gate in gates
        if isinstance(gate, Mapping) and "id" in gate
    }
    lookup_by_id = {
        str(lookup["id"]): lookup
        for lookup in lookups
        if isinstance(lookup, Mapping) and "id" in lookup
    }
    selectors: list[dict[str, Any]] = []
    for index in range(56):
        selector_id = f"selector:{index}"
        name = raw_selectors.get(str(index))
        if not isinstance(name, str) or not name:
            raise GenerationError(f"missing display name for {selector_id}")
        gate_ids = sorted(
            str(gate["id"])
            for gate in gates
            if isinstance(gate, Mapping)
            and selector_id in gate.get("selectorIds", [])
        )
        lookup_ids = sorted(
            str(lookup["id"])
            for lookup in lookups
            if isinstance(lookup, Mapping)
            and selector_id in lookup.get("selectorIds", [])
        )
        target: dict[str, str] | None = None
        if gate_ids:
            gate = gate_by_id[gate_ids[0]]
            target = circuit_target(
                gate_ids[0],
                kind="gate",
                title=str(gate.get("name", name)),
            )
        elif lookup_ids:
            lookup = lookup_by_id[lookup_ids[0]]
            target = circuit_target(
                lookup_ids[0],
                kind="lookup",
                title=str(lookup.get("name") or f"Lookup {lookup_ids[0]}"),
            )
        selectors.append(
            {
                "id": selector_id,
                "index": index,
                "name": name,
                "gateIds": gate_ids,
                "lookupIds": lookup_ids,
                **(
                    {"circuitTarget": add_target(targets, target)}
                    if target is not None
                    else {}
                ),
            }
        )
    return selectors


def operation_region_id(operation: Mapping[str, Any]) -> str | None:
    direct = operation.get("regionId")
    if isinstance(direct, str):
        return direct
    for key in ("cell", "source", "lhs", "left"):
        cell = operation.get(key)
        if isinstance(cell, Mapping):
            index = cell.get("region_index", cell.get("regionIndex"))
            if index is not None:
                return f"region:{integer(index, label='operation region index')}"
    return None


def explorer_operation_links(
    explorer: Mapping[str, Any],
) -> tuple[
    dict[tuple[str, int], list[Mapping[str, Any]]],
    dict[tuple[tuple[str, int], tuple[str, int]], list[Mapping[str, Any]]],
    dict[tuple[str, str, int], list[Mapping[str, Any]]],
    dict[tuple[str, int, str], list[Mapping[str, Any]]],
    dict[str, list[str]],
]:
    operations = explorer.get("synthesis", {}).get("operations", [])
    endpoint_operations: dict[
        tuple[str, int], list[Mapping[str, Any]]
    ] = defaultdict(list)
    copy_operations: dict[
        tuple[tuple[str, int], tuple[str, int]], list[Mapping[str, Any]]
    ] = defaultdict(list)
    selector_operations: dict[
        tuple[str, str, int], list[Mapping[str, Any]]
    ] = defaultdict(list)
    fixed_operations: dict[
        tuple[str, int, str], list[Mapping[str, Any]]
    ] = defaultdict(list)
    region_operation_ids: dict[str, list[str]] = defaultdict(list)

    for operation in operations:
        if not isinstance(operation, Mapping) or "id" not in operation:
            continue
        operation_id = str(operation["id"])
        region_id = operation_region_id(operation)
        if region_id is not None:
            region_operation_ids[region_id].append(operation_id)
        kind = operation.get("kind")
        if kind == "enable_selector" and region_id is not None:
            selector_id = str(operation.get("selector_id"))
            row = integer(operation.get("absolute_row"), label="selector row")
            selector_operations[(region_id, selector_id, row)].append(operation)
        elif kind == "copy":
            left = operation.get("lhs", operation.get("left"))
            right = operation.get("rhs", operation.get("right"))
            if isinstance(left, Mapping) and isinstance(right, Mapping):
                normalized_left = endpoint_from_explorer(left)
                normalized_right = endpoint_from_explorer(right)
                if normalized_left is not None and normalized_right is not None:
                    copy_operations[
                        copy_key(normalized_left, normalized_right)
                    ].append(operation)
        elif kind == "constrain_instance":
            source = operation.get("source")
            if isinstance(source, Mapping):
                normalized_source = endpoint_from_explorer(source)
                instance_column = operation.get("instance_column", "0")
                instance_row = operation.get("row")
                if normalized_source is not None and instance_row is not None:
                    normalized_instance = {
                        "columnId": f"instance:{integer(instance_column, label='instance column')}",
                        "row": integer(instance_row, label="instance row"),
                    }
                    copy_operations[
                        copy_key(normalized_source, normalized_instance)
                    ].append(operation)
        elif kind in {"assign_fixed", "constrain_constant"}:
            cell = operation.get("cell")
            if not isinstance(cell, Mapping):
                continue
            normalized = endpoint_from_explorer(cell)
            if normalized is None:
                continue
            endpoint_operations[endpoint_key(normalized)].append(operation)
            if kind == "assign_fixed":
                value = str(operation.get("value", ""))
                fixed_operations[
                    (normalized["columnId"], normalized["row"], value)
                ].append(operation)
    return (
        endpoint_operations,
        copy_operations,
        selector_operations,
        fixed_operations,
        region_operation_ids,
    )


def normalized_trace_events(
    raw_events: Sequence[Mapping[str, Any]],
    explorer: Mapping[str, Any],
    selectors: Sequence[Mapping[str, Any]],
    row_count: int,
    targets: MutableMapping[str, dict[str, str]],
) -> tuple[list[dict[str, Any]], dict[str, tuple[int, int] | None]]:
    regions = explorer.get("synthesis", {}).get("regions", [])
    if not isinstance(regions, list):
        raise GenerationError("Circuit Explorer artifact is missing synthesis regions")
    selector_by_id = {str(item["id"]): item for item in selectors}
    (
        endpoint_operations,
        copy_operations,
        selector_operations,
        fixed_operations,
        _,
    ) = explorer_operation_links(explorer)

    normalized: list[dict[str, Any]] = []
    namespace: list[str] = []
    current_region: str | None = None
    next_region_index = 0
    region_ranges: dict[str, list[int]] = defaultdict(list)
    lookup_region_seen = False

    for source_index, raw in enumerate(raw_events):
        tag = raw.get("tag")
        if not isinstance(tag, str):
            raise GenerationError(f"trace event {source_index} has no tag")
        event: dict[str, Any] = {
            "id": f"trace-event:{source_index}",
            "kind": "other",
            "sourceIndex": source_index,
            "sourceTag": tag,
        }
        if namespace:
            event["namespace"] = list(namespace)

        if tag == "PushNamespace":
            name = str(raw.get("name", ""))
            event["annotation"] = name
            namespace.append(name)
        elif tag == "PopNamespace":
            if not namespace:
                raise GenerationError(f"namespace stack underflow at event {source_index}")
            namespace.pop()
        elif tag == "EnterRegion":
            name = str(raw.get("name", ""))
            event["annotation"] = name
            if name == "generator_table" and not lookup_region_seen:
                current_region = "lookup-tables:0"
                lookup_region_seen = True
            else:
                if next_region_index >= len(regions):
                    raise GenerationError("trace contains more regions than explorer data")
                expected = regions[next_region_index]
                if not isinstance(expected, Mapping):
                    raise GenerationError("invalid Circuit Explorer region record")
                expected_name = str(expected.get("name", ""))
                if name != expected_name:
                    raise GenerationError(
                        "trace/explorer region mismatch at "
                        f"{next_region_index}: {name!r} != {expected_name!r}"
                    )
                current_region = str(expected.get("id", f"region:{next_region_index}"))
                next_region_index += 1
            event["regionId"] = current_region
        elif tag == "ExitRegion":
            if current_region is None:
                raise GenerationError(f"region stack underflow at event {source_index}")
            event["regionId"] = current_region
            current_region = None
        else:
            if current_region is not None:
                event["regionId"] = current_region

            operation_records: list[Mapping[str, Any]] = []
            if tag == "AssignFixed":
                row = integer(raw.get("row"), label="fixed assignment row")
                fixed_column_id = f"fixed:{integer(raw.get('column'), label='fixed column')}"
                value = str(raw.get("value", ""))
                event.update(
                    {
                        "kind": "assign-fixed",
                        "row": row,
                        "columnId": fixed_column_id,
                        "annotation": str(raw.get("annotation", "")),
                        "value": value,
                        "endpoints": [{"columnId": fixed_column_id, "row": row}],
                    }
                )
                operation_records.extend(
                    fixed_operations.get((fixed_column_id, row, value), [])
                )
                if current_region is not None:
                    region_ranges[current_region].append(row)
            elif tag == "EnableSelector":
                row = integer(raw.get("row"), label="selector row")
                selector_id = f"selector:{integer(raw.get('selector'), label='selector')}"
                selector = selector_by_id.get(selector_id)
                if selector is None:
                    raise GenerationError(f"unknown selector in trace: {selector_id}")
                event.update(
                    {
                        "kind": "enable-selector",
                        "row": row,
                        "selectorId": selector_id,
                    }
                )
                annotation = str(raw.get("annotation", ""))
                if annotation:
                    event["annotation"] = annotation
                if selector["gateIds"]:
                    event["gateIds"] = list(selector["gateIds"])
                if selector["lookupIds"]:
                    event["lookupIds"] = list(selector["lookupIds"])
                if current_region is not None:
                    operation_records.extend(
                        selector_operations.get((current_region, selector_id, row), [])
                    )
                    region_ranges[current_region].append(row)
            elif tag == "Copy":
                left = raw.get("left")
                right = raw.get("right")
                if not isinstance(left, Mapping) or not isinstance(right, Mapping):
                    raise GenerationError(f"copy event {source_index} has invalid endpoints")
                endpoints = [endpoint_from_trace(left), endpoint_from_trace(right)]
                event.update({"kind": "copy", "endpoints": endpoints})
                operation_records.extend(copy_operations.get(copy_key(*endpoints), []))
                if current_region is not None:
                    region_ranges[current_region].extend(
                        endpoint["row"] for endpoint in endpoints
                    )
            elif tag == "FillFromRow":
                start = integer(raw.get("from_row"), label="fill start row")
                fixed_column_id = f"fixed:{integer(raw.get('column'), label='fill column')}"
                event.update(
                    {
                        "kind": "fill",
                        "columnId": fixed_column_id,
                        "fromRow": start,
                        "toRow": row_count - 1,
                        "value": str(raw.get("value", "")),
                    }
                )
                if current_region is not None:
                    region_ranges[current_region].extend((start, row_count - 1))
            else:
                raise GenerationError(f"unsupported trace event tag {tag!r}")

            if operation_records:
                operation_ids = sorted({str(item["id"]) for item in operation_records})
                event["operationIds"] = operation_ids

        normalized.append(event)

    if namespace:
        raise GenerationError("synthesis trace ended with namespaces still open")
    if current_region is not None:
        raise GenerationError("synthesis trace ended with a region still open")
    if next_region_index != len(regions):
        raise GenerationError(
            f"trace contains {next_region_index} regions; explorer contains {len(regions)}"
        )

    finalized_ranges: dict[str, tuple[int, int] | None] = {}
    for region in regions:
        region_id = str(region["id"])
        rows = region_ranges.get(region_id, [])
        finalized_ranges[region_id] = (min(rows), max(rows)) if rows else None
    return normalized, finalized_ranges


def build_regions(
    explorer: Mapping[str, Any],
    _trace_ranges: Mapping[str, tuple[int, int] | None],
    targets: MutableMapping[str, dict[str, str]],
) -> list[dict[str, Any]]:
    raw_regions = explorer.get("synthesis", {}).get("regions", [])
    (
        _,
        _,
        _,
        _,
        region_operation_ids,
    ) = explorer_operation_links(explorer)
    regions: list[dict[str, Any]] = []
    for position, raw in enumerate(raw_regions):
        if not isinstance(raw, Mapping):
            raise GenerationError("invalid Circuit Explorer region record")
        region_id = str(raw.get("id", f"region:{position}"))
        region_index = integer(
            raw.get("regionIndex", raw.get("region_index", position)),
            label="region index",
        )
        start_row = integer(
            raw.get("startRow", raw.get("start_row")),
            label="region start row",
        )
        name = str(raw.get("name", f"Region {region_index}"))
        target = circuit_target(region_id, kind="region", title=name)
        metrics = raw.get("metrics")
        row_range = metrics.get("rowRange") if isinstance(metrics, Mapping) else None
        region = {
            "id": region_id,
            "regionIndex": region_index,
            "startRow": start_row,
            "name": name,
            "namespace": [str(item) for item in raw.get("namespace", [])],
            "selectorIds": sorted(str(item) for item in raw.get("selectorIds", [])),
            "gateIds": sorted(str(item) for item in raw.get("gateIds", [])),
            "lookupIds": sorted(str(item) for item in raw.get("lookupIds", [])),
            "operationIds": sorted(region_operation_ids.get(region_id, [])),
            "circuitTarget": add_target(targets, target),
        }
        component_id = raw.get("componentId")
        if isinstance(component_id, str) and component_id:
            region["componentId"] = component_id
        # The Explorer range deliberately counts only cells owned by this
        # region. A copy event also names a peer cell that may belong to a
        # distant region, so a min/max over raw copy endpoints would invent
        # enormous spans and is not a trustworthy placement boundary.
        if isinstance(row_range, Mapping) and row_range.get("max") is not None:
            region["endRow"] = integer(
                row_range["max"],
                label=f"{region_id} end row",
            )
        regions.append(region)
    return regions


def add_row_reference(
    rows: MutableMapping[str, Any],
    row_index: int,
    *,
    event_id: str | None = None,
    region_id: str | None = None,
    selector_id: str | None = None,
    column_id_value: str | None = None,
) -> None:
    row = rows.setdefault(
        row_index,
        {
            "eventIds": set(),
            "regionIds": set(),
            "selectorIds": set(),
            "columnIds": set(),
        },
    )
    if event_id is not None:
        row["eventIds"].add(event_id)
    if region_id is not None:
        row["regionIds"].add(region_id)
    if selector_id is not None:
        row["selectorIds"].add(selector_id)
    if column_id_value is not None:
        row["columnIds"].add(column_id_value)


def build_rows(
    events: Sequence[Mapping[str, Any]],
    regions: Sequence[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    rows: dict[int, dict[str, set[str]]] = {}
    for event in events:
        event_id = str(event["id"])
        if event["kind"] == "fill":
            for row_index in range(int(event["fromRow"]), int(event["toRow"]) + 1):
                add_row_reference(
                    rows,
                    row_index,
                    event_id=event_id,
                    column_id_value=str(event["columnId"]),
                )
        for endpoint in event.get("endpoints", []):
            add_row_reference(
                rows,
                int(endpoint["row"]),
                event_id=event_id,
                column_id_value=str(endpoint["columnId"]),
            )
        if "row" in event and event.get("selectorId"):
            add_row_reference(
                rows,
                int(event["row"]),
                event_id=event_id,
                selector_id=str(event["selectorId"]),
            )
    for region in regions:
        start_row = int(region["startRow"])
        end_row = int(region.get("endRow", start_row))
        for row_index in range(start_row, end_row + 1):
            add_row_reference(
                rows,
                row_index,
                region_id=str(region["id"]),
            )
    return [
        {
            "row": row_index,
            "eventIds": sorted(values["eventIds"]),
            "regionIds": sorted(values["regionIds"]),
            "selectorIds": sorted(values["selectorIds"]),
            "columnIds": sorted(values["columnIds"]),
        }
        for row_index, values in sorted(rows.items())
    ]


def validate_generated_data(data: Mapping[str, Any]) -> None:
    if data.get("schema") != OUTPUT_SCHEMA:
        raise GenerationError("generated artifact has the wrong schema")
    circuit = data.get("metadata", {}).get("circuit", {})
    row_count = integer(circuit.get("rowCount"), label="row count")
    if row_count != 2 ** integer(circuit.get("k"), label="circuit k"):
        raise GenerationError("rowCount must equal 2^k")
    columns = data.get("columns", [])
    selectors = data.get("selectors", [])
    regions = data.get("regions", [])
    events = data.get("events", [])
    rows = data.get("rows", [])
    if len(columns) != 25:
        raise GenerationError("generated grid must contain 25 physical columns")
    if len(selectors) != 56:
        raise GenerationError("generated grid must contain 56 virtual selectors")
    if len(regions) != 395:
        raise GenerationError("generated grid must contain 395 exact regions")
    for label, records in (
        ("column", columns),
        ("selector", selectors),
        ("region", regions),
        ("event", events),
    ):
        ids = [record.get("id") for record in records]
        if None in ids or len(ids) != len(set(ids)):
            raise GenerationError(f"generated grid has invalid {label} IDs")
    column_ids = {record["id"] for record in columns}
    selector_ids = {record["id"] for record in selectors}
    region_ids = {record["id"] for record in regions}
    event_ids = {record["id"] for record in events}
    for event in events:
        for endpoint in event.get("endpoints", []):
            if endpoint["columnId"] not in column_ids:
                raise GenerationError(
                    f"{event['id']} references unknown column {endpoint['columnId']}"
                )
            if not 0 <= int(endpoint["row"]) < row_count:
                raise GenerationError(f"{event['id']} references an invalid row")
        if event.get("columnId") not in (None, *column_ids):
            raise GenerationError(f"{event['id']} references an unknown column")
        if event.get("selectorId") not in (None, *selector_ids):
            raise GenerationError(f"{event['id']} references an unknown selector")
        if event.get("regionId") not in (None, "lookup-tables:0", *region_ids):
            raise GenerationError(f"{event['id']} references an unknown region")
    previous_row = -1
    for row in rows:
        index = int(row["row"])
        if index <= previous_row or not 0 <= index < row_count:
            raise GenerationError("sparse row index must be sorted and in bounds")
        previous_row = index
        if not set(row["eventIds"]).issubset(event_ids):
            raise GenerationError(f"row {index} references an unknown event")
        if not set(row["regionIds"]).issubset(region_ids | {"lookup-tables:0"}):
            raise GenerationError(f"row {index} references an unknown region")
        if not set(row["selectorIds"]).issubset(selector_ids):
            raise GenerationError(f"row {index} references an unknown selector")
        if not set(row["columnIds"]).issubset(column_ids):
            raise GenerationError(f"row {index} references an unknown column")
    summary = data.get("summary", {})
    expected = {
        "columnCount": len(columns),
        "selectorCount": len(selectors),
        "regionCount": len(regions),
        "eventCount": len(events),
        "populatedRowCount": len(rows),
    }
    for key, value in expected.items():
        if summary.get(key) != value:
            raise GenerationError(f"summary {key} is stale")


def generate_data(
    configure_model: Mapping[str, Any],
    configure_model_bytes: bytes,
    configure_implementation: Mapping[str, Any],
    configure_implementation_bytes: bytes,
    synthesis_model: Mapping[str, Any],
    synthesis_model_bytes: bytes,
    synthesis_implementation: Mapping[str, Any],
    synthesis_implementation_bytes: bytes,
    explorer: Mapping[str, Any],
    explorer_bytes: bytes,
    *,
    paths: Mapping[str, str],
) -> dict[str, Any]:
    if explorer.get("schema") != EXPLORER_SCHEMA:
        raise GenerationError(
            f"unsupported Circuit Explorer schema {explorer.get('schema')!r}"
        )
    raw_events, _ = ensure_parity(
        configure_model,
        configure_implementation,
        synthesis_model,
        synthesis_implementation,
    )
    explorer_metadata = explorer.get("metadata", {})
    explorer_circuit = explorer_metadata.get("circuit", {})
    k = integer(explorer_circuit.get("k"), label="circuit k")
    row_count = 2**k
    targets: dict[str, dict[str, str]] = {}
    columns = build_columns(explorer)
    selectors = build_selectors(explorer, targets)
    events, ranges = normalized_trace_events(
        raw_events,
        explorer,
        selectors,
        row_count,
        targets,
    )
    regions = build_regions(explorer, ranges, targets)
    rows = build_rows(events, regions)
    event_counts = Counter(str(event["kind"]) for event in events)
    source_tag_counts = Counter(str(event["sourceTag"]) for event in events)
    inputs = [
        {
            "id": identifier,
            "path": paths[identifier],
            "sha256": sha256_bytes(raw),
        }
        for identifier, raw in (
            ("configure-model", configure_model_bytes),
            ("configure-implementation", configure_implementation_bytes),
            ("synthesis-model", synthesis_model_bytes),
            ("synthesis-implementation", synthesis_implementation_bytes),
            ("circuit-explorer", explorer_bytes),
        )
    ]
    artifact = {
        "schema": OUTPUT_SCHEMA,
        "metadata": {
            "generator": {
                "name": GENERATOR_NAME,
                "version": GENERATOR_VERSION,
            },
            "circuit": {
                "id": "orchard-action",
                "name": str(explorer_circuit.get("name", "Orchard Action Circuit")),
                "version": str(explorer_circuit.get("version", "")),
                "field": str(explorer_circuit.get("field", "")),
                "k": k,
                "rowCount": row_count,
                "floorPlanner": str(explorer_metadata.get("floorPlanner", "V1")),
                "stage": "pre-selector-compression",
            },
            "capabilities": {
                "adviceAssignments": "references-only",
                "witnessValues": "omitted",
                "selectors": "virtual",
                "permutation": "copy-edges",
            },
            "inputs": inputs,
            "parity": {
                "configure": "exact",
                "synthesis": "exact",
                "comparison": "parsed-json",
            },
            "repositoryRefs": dict(explorer_metadata.get("repositoryRefs", {})),
        },
        "columns": columns,
        "selectors": selectors,
        "regions": regions,
        "events": events,
        "rows": rows,
        # Selector and region targets stay next to the entities they describe.
        # Keeping a second top-level copy added several megabytes without
        # carrying new information; the frontend normalizer collects them.
        "targets": [],
        "summary": {
            "columnCount": len(columns),
            "selectorCount": len(selectors),
            "regionCount": len(regions),
            "eventCount": len(events),
            "populatedRowCount": len(rows),
            "counts": {
                **{key: event_counts[key] for key in sorted(event_counts)},
                **{
                    f"source:{key}": source_tag_counts[key]
                    for key in sorted(source_tag_counts)
                },
            },
        },
    }
    validate_generated_data(artifact)
    return artifact


def parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--garden-root", type=Path, default=DEFAULT_GARDEN_ROOT)
    parser.add_argument(
        "--configure-model", type=Path, default=DEFAULT_CONFIGURE_MODEL
    )
    parser.add_argument(
        "--configure-implementation",
        type=Path,
        default=DEFAULT_CONFIGURE_IMPLEMENTATION,
    )
    parser.add_argument(
        "--synthesis-model", type=Path, default=DEFAULT_SYNTHESIS_MODEL
    )
    parser.add_argument(
        "--synthesis-implementation",
        type=Path,
        default=DEFAULT_SYNTHESIS_IMPLEMENTATION,
    )
    parser.add_argument("--explorer", type=Path, default=DEFAULT_EXPLORER)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail unless the output is already byte-for-byte current",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        loaded: dict[str, tuple[Any, bytes]] = {}
        for identifier, path in (
            ("configure-model", args.configure_model),
            ("configure-implementation", args.configure_implementation),
            ("synthesis-model", args.synthesis_model),
            ("synthesis-implementation", args.synthesis_implementation),
            ("circuit-explorer", args.explorer),
        ):
            loaded[identifier] = read_json(path)
        paths = {
            identifier: relative_path(path, args.garden_root)
            for identifier, path in (
                ("configure-model", args.configure_model),
                ("configure-implementation", args.configure_implementation),
                ("synthesis-model", args.synthesis_model),
                ("synthesis-implementation", args.synthesis_implementation),
                ("circuit-explorer", args.explorer),
            )
        }
        artifact = generate_data(
            loaded["configure-model"][0],
            loaded["configure-model"][1],
            loaded["configure-implementation"][0],
            loaded["configure-implementation"][1],
            loaded["synthesis-model"][0],
            loaded["synthesis-model"][1],
            loaded["synthesis-implementation"][0],
            loaded["synthesis-implementation"][1],
            loaded["circuit-explorer"][0],
            loaded["circuit-explorer"][1],
            paths=paths,
        )
        expected = canonical_json_bytes(artifact)
        if args.check:
            try:
                actual = args.output.read_bytes()
            except OSError as error:
                raise GenerationError(f"cannot read {args.output}: {error}") from error
            if actual != expected:
                raise GenerationError(
                    f"{args.output} is stale; run {GENERATOR_NAME} without --check"
                )
            print(f"{args.output} is current")
            return 0
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(expected)
        print(
            f"wrote {args.output} "
            f"({len(artifact['events'])} trace events, {len(artifact['rows'])} rows)"
        )
        return 0
    except GenerationError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
