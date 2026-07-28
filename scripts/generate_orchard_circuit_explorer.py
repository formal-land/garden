#!/usr/bin/env python3
"""Build the deterministic Orchard circuit-explorer data artifact.

The primary input is the Garden evaluator's recursive raw structure
(`garden.orchard.circuit-structure.raw.v1`).  An adapter for Orchard's
`orchard.action_circuit.highlevel.v1` exporter is kept so the enrichment and
frontend can be developed before (or independently from) a Rocq extraction.

The generated file intentionally contains no wall-clock timestamp and never
derives repository revisions from a working tree.  Permalinks are pinned by
the curated manifest; input and scanned-source SHA-256 digests record the
actual bytes used for a generation.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, MutableMapping, Sequence


OUTPUT_SCHEMA = "garden.orchard.circuit-highlevel.v1"
RAW_SCHEMA = "garden.orchard.circuit-structure.raw.v1"
ORCHARD_HIGHLEVEL_SCHEMA = "orchard.action_circuit.highlevel.v1"
MANIFEST_SCHEMA = "garden.orchard.circuit-highlevel.manifest.v1"
GENERATOR_NAME = "scripts/generate_orchard_circuit_explorer.py"

SCRIPT_PATH = Path(__file__).resolve()
DEFAULT_GARDEN_ROOT = SCRIPT_PATH.parent.parent
DEFAULT_MANIFEST = SCRIPT_PATH.with_name("orchard_circuit_explorer_manifest.v1.json")
DEFAULT_INPUT = (
    DEFAULT_GARDEN_ROOT
    / "Garden"
    / "Orchard"
    / "Snapshots"
    / "circuit_structure_generated_from_model.json"
)
DEFAULT_OUTPUT = (
    DEFAULT_GARDEN_ROOT
    / "web"
    / "orchard-verification"
    / "public"
    / "data"
    / "orchard-circuit-highlevel.v1.json"
)


class GenerationError(RuntimeError):
    """A deterministic generation or validation failure."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


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
    return (json.dumps(value, ensure_ascii=False, separators=(",", ":")) + "\n").encode("utf-8")


def slug(value: str, *, fallback: str = "item", limit: int = 48) -> str:
    normalized = re.sub(r"[^a-z0-9]+", "-", value.casefold()).strip("-")
    return (normalized or fallback)[:limit].rstrip("-")


def line_column(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    last_newline = text.rfind("\n", 0, offset)
    return line, offset - last_newline


def ensure_relative_path(value: str, *, label: str) -> None:
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        raise GenerationError(f"{label} must stay inside its repository root: {value!r}")


def path_inside(root: Path, candidate: Path, *, label: str) -> Path:
    root = root.resolve()
    candidate = candidate.resolve()
    try:
        candidate.relative_to(root)
    except ValueError as error:
        raise GenerationError(f"{label} escapes repository root {root}: {candidate}") from error
    return candidate


def mask_rocq_comments(text: str) -> str:
    """Mask nested Rocq comments while preserving offsets and line endings.

    Strings remain intact, including doubled-quote escapes.  Keeping exact
    offsets lets the source index attach stable symbols and advisory line
    metadata without a Rocq parser dependency.
    """

    chars = list(text)
    depth = 0
    in_string = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith("(*", i):
                if chars[i] != "\n":
                    chars[i] = " "
                if chars[i + 1] != "\n":
                    chars[i + 1] = " "
                depth += 1
                i += 2
                continue
            if text.startswith("*)", i):
                if chars[i] != "\n":
                    chars[i] = " "
                if chars[i + 1] != "\n":
                    chars[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if chars[i] != "\n":
                chars[i] = " "
            i += 1
            continue

        if in_string:
            if text[i] == '"':
                if i + 1 < len(text) and text[i + 1] == '"':
                    i += 2
                    continue
                in_string = False
            i += 1
            continue

        if text.startswith("(*", i):
            chars[i] = " "
            chars[i + 1] = " "
            depth = 1
            i += 2
        elif text[i] == '"':
            in_string = True
            i += 1
        elif text.startswith("*)", i):
            raise GenerationError("unmatched Rocq comment terminator")
        else:
            i += 1

    if depth:
        raise GenerationError("unterminated Rocq comment")
    if in_string:
        raise GenerationError("unterminated Rocq string")
    return "".join(chars)


ROCQ_DECLARATION_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:Local|Global)\s+)?"
    r"(?:Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Variant|Class|"
    r"Theorem|Lemma|Fact|Remark|Corollary|Proposition|Example)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)
ROCQ_STRING_RE = re.compile(r'"(?P<value>(?:[^"\n]|"")*)"')
GATE_NAME_RE = re.compile(r'Gate\.name\s*:=\s*"(?P<value>(?:[^"\n]|"")*)"')
ADD_REGION_RE = re.compile(r"𝓛\.AddRegion\b")


def decode_rocq_string(value: str) -> str:
    return value.replace('""', '"')


def qualified_module_for_path(path: str) -> str:
    without_suffix = path[:-2] if path.endswith(".v") else path
    return without_suffix.replace("/", ".")


@dataclass(frozen=True)
class Declaration:
    name: str
    qualified_symbol: str
    start: int
    end: int


@dataclass(frozen=True)
class SourceSite:
    repository: str
    path: str
    language: str
    symbol: str | None
    line: int | None
    column: int | None
    byte_offset: int | None
    site_kind: str
    site_ordinal: int | None = None
    literal: str | None = None
    verification: str = "scanned"

    @property
    def id(self) -> str:
        if self.symbol:
            fragment = self.symbol
            if self.site_ordinal is not None:
                fragment += f"@{self.site_kind}-{self.site_ordinal}"
                if self.literal is not None:
                    fragment += f"-{sha256_text(self.literal)[:8]}"
        elif self.literal is not None:
            fragment = f"{self.site_kind}-literal-{sha256_text(self.literal)[:12]}"
        else:
            fragment = self.site_kind
        return f"{self.repository}:{self.path}#{fragment}"


def declarations_for_source(path: str, masked: str) -> list[Declaration]:
    matches = list(ROCQ_DECLARATION_RE.finditer(masked))
    module_name = qualified_module_for_path(path)
    declarations: list[Declaration] = []
    for index, match in enumerate(matches):
        start = match.start()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(masked)
        name = match.group("name")
        declarations.append(
            Declaration(
                name=name,
                qualified_symbol=f"{module_name}.{name}",
                start=start,
                end=end,
            )
        )
    return declarations


class SourceIndex:
    def __init__(self, repositories: Mapping[str, Mapping[str, Any]]) -> None:
        self.repositories = repositories
        self.records: dict[str, dict[str, Any]] = {}
        self.files: dict[tuple[str, str], dict[str, Any]] = {}
        self.gates: MutableMapping[str, list[str]] = defaultdict(list)
        self.regions: MutableMapping[str, list[str]] = defaultdict(list)
        self._mapped_for_source: MutableMapping[str, list[str]] = defaultdict(list)

    def add_file(self, repository: str, path: str, language: str, raw: bytes) -> None:
        ensure_relative_path(path, label="source path")
        self.files[(repository, path)] = {
            "id": f"{repository}:{path}",
            "repository": repository,
            "path": path,
            "language": language,
            "sha256": sha256_bytes(raw),
        }

    def add_site(self, site: SourceSite) -> str:
        repository = self.repositories.get(site.repository)
        if repository is None:
            raise GenerationError(f"unknown repository in source site: {site.repository}")
        ensure_relative_path(site.path, label="source site path")
        url = f"{repository['base_url']}/blob/{repository['revision']}/{site.path}"
        if site.line is not None:
            url += f"#L{site.line}"
        record = {
            "id": site.id,
            "repository": site.repository,
            "revision": repository["revision"],
            "path": site.path,
            "language": site.language,
            "symbol": site.symbol,
            "line": site.line,
            "column": site.column,
            "byteOffset": site.byte_offset,
            "siteKind": site.site_kind,
            "literal": site.literal,
            "verification": site.verification,
            "url": url,
        }
        previous = self.records.get(site.id)
        if previous is not None and previous != record:
            raise GenerationError(f"unstable duplicate source ID: {site.id}")
        self.records[site.id] = record
        return site.id

    def add_mapping(self, source_id: str, mapped_id: str) -> None:
        if mapped_id not in self._mapped_for_source[source_id]:
            self._mapped_for_source[source_id].append(mapped_id)

    def resolution(self, literal: str, *, kind: str) -> dict[str, Any]:
        index = self.gates if kind == "gate" else self.regions
        exact_ids = sorted(set(index.get(literal, [])))
        if len(exact_ids) == 1:
            confidence = "exact"
            primary = exact_ids[0]
        elif len(exact_ids) > 1:
            confidence = "ambiguous"
            primary = None
        else:
            confidence = "unresolved"
            primary = None

        candidates: list[dict[str, str]] = []
        for source_id in exact_ids:
            candidates.append(
                {
                    "sourceId": source_id,
                    "confidence": "exact",
                    "reason": f"exact {kind} literal in translated Rocq source",
                }
            )
            for mapped_id in sorted(self._mapped_for_source.get(source_id, [])):
                candidates.append(
                    {
                        "sourceId": mapped_id,
                        "confidence": "mapped",
                        "reason": "deterministic translated-source path mapping",
                    }
                )
        return {
            "confidence": confidence,
            "primarySourceId": primary,
            "candidates": candidates,
        }


def iter_manifest_files(root: Path, config: Mapping[str, Any]) -> Iterator[Path]:
    seen: set[Path] = set()
    for pattern in config.get("includes", []):
        ensure_relative_path(pattern, label="source glob")
        for path in sorted(root.glob(pattern)):
            if not path.is_file():
                continue
            resolved = path_inside(root, path, label="scanned source")
            relative = resolved.relative_to(root)
            if any(str(relative).endswith(suffix) for suffix in config.get("exclude_suffixes", [])):
                continue
            if any(part in config.get("exclude_path_parts", []) for part in relative.parts):
                continue
            if resolved not in seen:
                seen.add(resolved)
                yield resolved


def scan_rocq_sources(
    garden_root: Path,
    config: Mapping[str, Any],
    source_index: SourceIndex,
) -> None:
    repository = str(config["repository"])
    for path in iter_manifest_files(garden_root, config):
        relative = path.relative_to(garden_root).as_posix()
        raw = path.read_bytes()
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError as error:
            raise GenerationError(f"Rocq source is not UTF-8: {relative}") from error
        masked = mask_rocq_comments(text)
        source_index.add_file(repository, relative, "rocq", raw)

        for declaration in declarations_for_source(relative, masked):
            segment = masked[declaration.start : declaration.end]
            for gate_match in GATE_NAME_RE.finditer(segment):
                value = decode_rocq_string(gate_match.group("value"))
                offset = declaration.start + gate_match.start()
                line, column = line_column(text, offset)
                site = SourceSite(
                    repository=repository,
                    path=relative,
                    language="rocq",
                    symbol=declaration.qualified_symbol,
                    line=line,
                    column=column,
                    byte_offset=len(text[:offset].encode("utf-8")),
                    site_kind="gate",
                    literal=value,
                )
                source_id = source_index.add_site(site)
                source_index.gates[value].append(source_id)

            add_region_ordinal = 0
            for add_match in ADD_REGION_RE.finditer(segment):
                add_region_ordinal += 1
                call_start = declaration.start + add_match.start()
                tail = masked[call_start : declaration.end]
                fun_offset = tail.find("(fun")
                if fun_offset < 0:
                    fun_offset = min(len(tail), 1200)
                call_prefix = tail[:fun_offset]
                for string_match in ROCQ_STRING_RE.finditer(call_prefix):
                    value = decode_rocq_string(string_match.group("value"))
                    offset = call_start + string_match.start()
                    line, column = line_column(text, offset)
                    site = SourceSite(
                        repository=repository,
                        path=relative,
                        language="rocq",
                        symbol=declaration.qualified_symbol,
                        line=line,
                        column=column,
                        byte_offset=len(text[:offset].encode("utf-8")),
                        site_kind="add-region",
                        site_ordinal=add_region_ordinal,
                        literal=value,
                    )
                    source_id = source_index.add_site(site)
                    source_index.regions[value].append(source_id)


def rust_mapping_for_path(path: str, mappings: Sequence[Mapping[str, Any]]) -> tuple[str, str] | None:
    for mapping in mappings:
        if mapping.get("rocq_path") == path:
            return str(mapping["repository"]), str(mapping["rust_path"])
        prefix = mapping.get("rocq_prefix")
        if prefix and path.startswith(str(prefix)) and path.endswith(".v"):
            suffix = path[len(str(prefix)) : -2] + ".rs"
            return str(mapping["repository"]), str(mapping["rust_prefix"]) + suffix
    return None


def add_mapped_rust_sites(
    source_index: SourceIndex,
    mappings: Sequence[Mapping[str, Any]],
) -> None:
    for source_id, record in list(source_index.records.items()):
        if record["language"] != "rocq" or record.get("literal") is None:
            continue
        mapping = rust_mapping_for_path(record["path"], mappings)
        if mapping is None:
            continue
        repository, rust_path = mapping
        mapped_site = SourceSite(
            repository=repository,
            path=rust_path,
            language="rust",
            symbol=None,
            line=None,
            column=None,
            byte_offset=None,
            site_kind=record["siteKind"],
            literal=record["literal"],
            verification="path-map",
        )
        mapped_id = source_index.add_site(mapped_site)
        source_index.add_mapping(source_id, mapped_id)


COLUMN_INDEX_RE = re.compile(
    r"\|\s*(?P<module>Advice|Lookup|Fixed|Instance_|Selector)\."
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*=>\s*(?P<index>[0-9]+)"
)


def parse_column_symbols(path: Path) -> dict[str, dict[str, str]]:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as error:
        raise GenerationError(f"cannot read column definitions {path}: {error}") from error
    masked = mask_rocq_comments(text)
    module_names = {
        "Advice": "advice",
        "Lookup": "lookup",
        "Fixed": "fixed",
        "Instance_": "instance",
        "Selector": "selector",
    }
    result: dict[str, dict[str, str]] = {name: {} for name in module_names.values()}
    for match in COLUMN_INDEX_RE.finditer(masked):
        result[module_names[match.group("module")]][match.group("index")] = match.group("name")
    expected = {"advice": 10, "lookup": 3, "fixed": 11, "instance": 1, "selector": 56}
    for kind, count in expected.items():
        if len(result[kind]) != count:
            raise GenerationError(
                f"expected {count} {kind} symbols in {path}, found {len(result[kind])}"
            )
    return result


def physical_fixed_symbol(index: str, symbols: Mapping[str, Mapping[str, str]]) -> str | None:
    return symbols["fixed"].get(index) or symbols["lookup"].get(index)


def symbolic_column(
    kind: str,
    index: str,
    symbols: Mapping[str, Mapping[str, str]],
) -> str | None:
    normalized = kind.casefold().rstrip("_")
    if normalized == "fixed":
        return physical_fixed_symbol(index, symbols)
    if normalized == "instance":
        return symbols["instance"].get(index)
    return symbols.get(normalized, {}).get(index)


def annotate_symbols(value: Any, symbols: Mapping[str, Mapping[str, str]]) -> Any:
    """Recursively retain numeric indices and add their Orchard symbolic names."""

    if isinstance(value, list):
        return [annotate_symbols(item, symbols) for item in value]
    if not isinstance(value, dict):
        return value

    result = {key: annotate_symbols(item, symbols) for key, item in value.items()}
    tag = value.get("tag")
    if tag in {"Advice", "Fixed", "Instance", "Instance_", "Lookup"} and "column" in value:
        name = symbolic_column(str(tag), str(value["column"]), symbols)
        if name is not None:
            result["column_name"] = name
    column = value.get("column")
    if isinstance(column, dict) and "kind" in column and "index" in column:
        name = symbolic_column(str(column["kind"]), str(column["index"]), symbols)
        if name is not None:
            result["column"]["name"] = name
    if "selector" in value and not isinstance(value["selector"], (dict, list)):
        name = symbols["selector"].get(str(value["selector"]))
        if name is not None:
            result["selector_name"] = name
    if "table" in value and not isinstance(value["table"], (dict, list)):
        name = symbols["lookup"].get(str(value["table"]))
        if name is not None:
            result["table_name"] = name
    if "instance_column" in value:
        name = symbols["instance"].get(str(value["instance_column"]))
        if name is not None:
            result["instance_column_name"] = name
    if value.get("kind") == "init_lookup_tables" and isinstance(value.get("entries"), list):
        for original, annotated in zip(value["entries"], result["entries"]):
            name = symbols["lookup"].get(str(original.get("column")))
            if name is not None:
                annotated["column_name"] = name
    return result


def collect_symbolic_terms(value: Any) -> list[str]:
    terms: set[str] = set()

    def visit(item: Any) -> None:
        if isinstance(item, list):
            for child in item:
                visit(child)
        elif isinstance(item, dict):
            for key, child in item.items():
                if key.endswith("_name") and isinstance(child, str) and child:
                    terms.add(child)
                elif key == "name" and isinstance(child, str) and len(child) < 160:
                    terms.add(child)
                visit(child)

    visit(value)
    return sorted(terms, key=lambda item: (item.casefold(), item))


def parse_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value, 0)
        except ValueError:
            return None
    return None


def row_values(value: Any, *, region_index: int | None = None) -> Iterator[int]:
    """Yield rows occupied by a region's own operations.

    Structural copy operations retain both endpoints.  One endpoint can be a
    cell from an earlier region (or an instance cell), so including every
    nested ``absolute_row`` would turn a region footprint into the span of all
    rows it references.  When a structural region index is available, only
    cells owned by that region contribute; a top-level operation row (for
    example an enabled selector) always contributes.  The schema adapter has
    no region identity and therefore keeps the older all-referenced-rows
    fallback.
    """

    def visit(item: Any, *, operation_root: bool = False) -> Iterator[int]:
        if isinstance(item, list):
            for child in item:
                yield from visit(child, operation_root=True)
            return
        if not isinstance(item, dict):
            return

        absolute_row = parse_int(item.get("absolute_row"))
        cell_region = parse_int(item.get("region_index"))
        if absolute_row is not None and (
            operation_root or region_index is None or cell_region == region_index
        ):
            yield absolute_row

        if region_index is None:
            for key in ("row", "start_row", "from_row"):
                parsed = parse_int(item.get(key))
                if parsed is not None:
                    yield parsed

        for key, child in item.items():
            if key in {"absolute_row", "row", "start_row", "from_row"}:
                continue
            yield from visit(child)

    yield from visit(value)


def operation_metrics(
    operations: Sequence[Mapping[str, Any]],
    *,
    region_index: int | None = None,
) -> dict[str, Any]:
    counts = Counter(str(operation.get("kind", "unknown")) for operation in operations)
    rows = list(row_values(list(operations), region_index=region_index))
    return {
        "operationCount": len(operations),
        "operationCounts": dict(sorted(counts.items())),
        "rowRange": {"min": min(rows), "max": max(rows)} if rows else None,
    }


def component_id(alias: str) -> str:
    return f"component:{alias}"


def validate_manifest(manifest: Mapping[str, Any]) -> None:
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise GenerationError(
            f"manifest schema must be {MANIFEST_SCHEMA!r}, found {manifest.get('schema')!r}"
        )
    repositories = manifest.get("repositories")
    if not isinstance(repositories, list) or not repositories:
        raise GenerationError("manifest.repositories must be a non-empty array")
    repository_ids = [item.get("id") for item in repositories]
    if len(repository_ids) != len(set(repository_ids)):
        raise GenerationError("manifest contains duplicate repository IDs")
    for repository in repositories:
        revision = repository.get("revision")
        if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
            raise GenerationError(f"repository {repository.get('id')} has an unpinned revision")
        if not str(repository.get("base_url", "")).startswith("https://"):
            raise GenerationError(f"repository {repository.get('id')} has an unsafe base URL")

    flow = manifest.get("flow")
    if not isinstance(flow, dict):
        raise GenerationError("manifest.flow must be an object")
    nodes = flow.get("nodes", [])
    edges = flow.get("edges", [])
    node_ids = [node.get("id") for node in nodes]
    edge_ids = [edge.get("id") for edge in edges]
    if len(node_ids) != len(set(node_ids)):
        raise GenerationError("manifest flow contains duplicate node IDs")
    if len(edge_ids) != len(set(edge_ids)):
        raise GenerationError("manifest flow contains duplicate edge IDs")
    known_nodes = set(node_ids)
    for edge in edges:
        if edge.get("from") not in known_nodes or edge.get("to") not in known_nodes:
            raise GenerationError(f"flow edge {edge.get('id')} has a dangling endpoint")
        if edge.get("from") == edge.get("to"):
            raise GenerationError(f"flow edge {edge.get('id')} is a self-loop")

    adjacency: MutableMapping[str, list[str]] = defaultdict(list)
    indegree = {str(node_id): 0 for node_id in node_ids}
    for edge in edges:
        source = str(edge["from"])
        target = str(edge["to"])
        adjacency[source].append(target)
        indegree[target] += 1
    frontier = sorted(node_id for node_id, degree in indegree.items() if degree == 0)
    visited = 0
    while frontier:
        node_id = frontier.pop(0)
        visited += 1
        for target in sorted(adjacency[node_id]):
            indegree[target] -= 1
            if indegree[target] == 0:
                frontier.append(target)
                frontier.sort()
    if visited != len(node_ids):
        raise GenerationError("manifest flow must be a directed acyclic graph")


def rule_matches_region(rule: Mapping[str, Any], region: Mapping[str, Any]) -> bool:
    root_name = region.get("rootNamespace")
    root_occurrence = region.get("rootNamespaceOccurrence")
    name = region.get("name")
    if "root_names" in rule and root_name not in rule["root_names"]:
        return False
    if "root_prefixes" in rule and not any(
        isinstance(root_name, str) and root_name.startswith(prefix)
        for prefix in rule["root_prefixes"]
    ):
        return False
    if "root_name" in rule and root_name != rule["root_name"]:
        return False
    if "root_occurrences" in rule and root_occurrence not in rule["root_occurrences"]:
        return False
    if "region_names" in rule and name not in rule["region_names"]:
        return False
    return any(
        key in rule
        for key in ("root_names", "root_prefixes", "root_name", "root_occurrences", "region_names")
    )


def match_region_component(region: Mapping[str, Any], flow_nodes: Sequence[Mapping[str, Any]]) -> str | None:
    matches = []
    for node in flow_nodes:
        if any(rule_matches_region(rule, region) for rule in node.get("match", [])):
            matches.append(component_id(str(node["id"])))
    if len(matches) > 1:
        raise GenerationError(f"region {region.get('id')} matches multiple components: {matches}")
    return matches[0] if matches else None


def match_instance_component(row: Any, flow_nodes: Sequence[Mapping[str, Any]]) -> str | None:
    parsed = parse_int(row)
    matches = []
    for node in flow_nodes:
        for rule in node.get("match", []):
            if parsed is not None and parsed in rule.get("instance_rows", []):
                matches.append(component_id(str(node["id"])))
                break
    if len(matches) > 1:
        raise GenerationError(f"instance row {row} matches multiple components: {matches}")
    return matches[0] if matches else None


def source_terms(resolution: Mapping[str, Any], source_index: SourceIndex) -> list[str]:
    terms: set[str] = set()
    for candidate in resolution.get("candidates", []):
        record = source_index.records.get(candidate.get("sourceId"))
        if record and record.get("symbol"):
            terms.add(str(record["symbol"]))
    return sorted(terms)


@dataclass
class SynthesisBuild:
    tree: list[dict[str, Any]]
    regions: list[dict[str, Any]]
    layout_operations: list[dict[str, Any]]
    instance_rows: MutableMapping[int, dict[str, Any]]


def make_region_summary(region: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "id": region["id"],
        "rawId": region.get("rawId"),
        "occurrence": region["occurrence"],
        "regionIndex": region.get("regionIndex"),
        "startRow": region.get("startRow"),
        "name": region["name"],
        "namespace": region["namespace"],
        "namespaceIds": region["namespaceIds"],
        "rootNamespace": region.get("rootNamespace"),
        "rootNamespaceOccurrence": region.get("rootNamespaceOccurrence"),
        "componentId": region.get("componentId"),
        "metrics": region["metrics"],
        "source": region["source"],
        "searchTerms": region["searchTerms"],
    }


def record_instance_references(
    value: Any,
    operation_id: str,
    instance_rows: MutableMapping[int, dict[str, Any]],
) -> None:
    if isinstance(value, list):
        for item in value:
            record_instance_references(item, operation_id, instance_rows)
        return
    if not isinstance(value, dict):
        return
    cell_id = value.get("id")
    if isinstance(cell_id, str):
        match = re.fullmatch(r"cell:instance:[^:]+:row:(-?[0-9]+)", cell_id)
        if match:
            row = int(match.group(1))
            record = instance_rows.setdefault(row, {"operationIds": set(), "cellIds": set()})
            record["operationIds"].add(operation_id)
            record["cellIds"].add(cell_id)
    for child in value.values():
        record_instance_references(child, operation_id, instance_rows)


def add_configure_entrypoints(
    garden_root: Path,
    entrypoints: Sequence[Mapping[str, Any]],
    source_index: SourceIndex,
) -> dict[str, Any]:
    candidates: list[dict[str, str]] = []
    primary: str | None = None
    for entrypoint in entrypoints:
        repository = str(entrypoint["repository"])
        path = str(entrypoint["path"])
        symbol = str(entrypoint["symbol"])
        if repository == "garden":
            absolute = path_inside(garden_root, garden_root / path, label="configure entrypoint")
            if not absolute.is_file():
                raise GenerationError(f"configure entrypoint does not exist: {path}")
            text = absolute.read_text(encoding="utf-8")
            masked = mask_rocq_comments(text)
            local_name = symbol.rsplit(".", 1)[-1]
            declaration = next(
                (item for item in declarations_for_source(path, masked) if item.name == local_name),
                None,
            )
            if declaration is None:
                raise GenerationError(f"configure entrypoint symbol not found: {path}#{symbol}")
            line, column = line_column(text, declaration.start)
            source_id = source_index.add_site(
                SourceSite(
                    repository=repository,
                    path=path,
                    language="rocq",
                    symbol=symbol,
                    line=line,
                    column=column,
                    byte_offset=len(text[: declaration.start].encode("utf-8")),
                    site_kind="configure",
                )
            )
            primary = source_id
            candidates.append(
                {
                    "sourceId": source_id,
                    "confidence": "exact",
                    "reason": "curated configure entrypoint found in translated Rocq source",
                }
            )
        else:
            source_id = source_index.add_site(
                SourceSite(
                    repository=repository,
                    path=path,
                    language="rust",
                    symbol=symbol,
                    line=None,
                    column=None,
                    byte_offset=None,
                    site_kind="configure",
                    verification="path-map",
                )
            )
            candidates.append(
                {
                    "sourceId": source_id,
                    "confidence": "mapped",
                    "reason": "curated implementation configure entrypoint",
                }
            )
    return {
        "confidence": "exact" if primary else "mapped" if candidates else "unresolved",
        "primarySourceId": primary,
        "candidates": candidates,
    }


def normalize_raw_configure(
    configure: Mapping[str, Any],
    source_index: SourceIndex,
    symbols: Mapping[str, Mapping[str, str]],
    entrypoint_source: Mapping[str, Any],
) -> dict[str, Any]:
    operations = configure.get("operations")
    if not isinstance(operations, list):
        raise GenerationError("raw configure.operations must be an array")
    gates: list[dict[str, Any]] = []
    lookups: list[dict[str, Any]] = []
    operation_index: list[dict[str, Any]] = []
    seen_gate_ids: set[str] = set()
    seen_lookup_ids: set[str] = set()

    for position, operation in enumerate(operations):
        if not isinstance(operation, dict):
            raise GenerationError(f"configure operation {position} must be an object")
        kind = operation.get("kind")
        operation_id = operation.get("id")
        if not isinstance(operation_id, str):
            raise GenerationError(f"configure operation {position} has no stable ID")
        if kind == "create_gate":
            gate_id = operation.get("gate_id")
            gate = operation.get("gate")
            if not isinstance(gate_id, str) or not isinstance(gate, dict):
                raise GenerationError(f"{operation_id} has malformed gate data")
            if gate_id in seen_gate_ids:
                raise GenerationError(f"duplicate gate ID: {gate_id}")
            seen_gate_ids.add(gate_id)
            name = gate.get("name")
            if not isinstance(name, str) or not name:
                raise GenerationError(f"{gate_id} has no gate name")
            enriched_gate = annotate_symbols(copy.deepcopy(gate), symbols)
            constraints = enriched_gate.get("constraints", [])
            if not isinstance(constraints, list):
                raise GenerationError(f"{gate_id}.constraints must be an array")
            enriched_constraints = []
            for constraint_index, constraint in enumerate(constraints):
                if not isinstance(constraint, dict):
                    raise GenerationError(f"{gate_id} constraint {constraint_index} is malformed")
                enriched_constraints.append(
                    {
                        "id": f"{gate_id}/constraint:{constraint_index}",
                        "index": constraint_index,
                        **constraint,
                    }
                )
            resolution = source_index.resolution(name, kind="gate")
            if resolution["confidence"] == "ambiguous":
                raise GenerationError(f"gate {name!r} has multiple exact Rocq definitions")
            enriched_gate["constraints"] = enriched_constraints
            enriched_gate.update(
                {
                    "id": gate_id,
                    "index": parse_int(operation.get("gate_index")),
                    "configureOperationId": operation_id,
                    "source": resolution,
                }
            )
            enriched_gate["searchTerms"] = sorted(
                set([name, *collect_symbolic_terms(enriched_gate), *source_terms(resolution, source_index)]),
                key=lambda item: (item.casefold(), item),
            )
            gates.append(enriched_gate)
            operation_index.append(
                {"id": operation_id, "kind": kind, "gateId": gate_id, "gateIndex": enriched_gate["index"]}
            )
        elif kind == "create_lookup":
            lookup_id = operation.get("lookup_id")
            lookup = operation.get("lookup")
            if not isinstance(lookup_id, str) or not isinstance(lookup, dict):
                raise GenerationError(f"{operation_id} has malformed lookup data")
            if lookup_id in seen_lookup_ids:
                raise GenerationError(f"duplicate lookup ID: {lookup_id}")
            seen_lookup_ids.add(lookup_id)
            enriched_lookup = annotate_symbols(copy.deepcopy(lookup), symbols)
            enriched_lookup.update(
                {
                    "id": lookup_id,
                    "index": parse_int(operation.get("lookup_index")),
                    "configureOperationId": operation_id,
                    "searchTerms": collect_symbolic_terms(enriched_lookup),
                }
            )
            lookups.append(enriched_lookup)
            operation_index.append(
                {
                    "id": operation_id,
                    "kind": kind,
                    "lookupId": lookup_id,
                    "lookupIndex": enriched_lookup["index"],
                }
            )
        else:
            raise GenerationError(f"unsupported configure operation kind {kind!r} in {operation_id}")

    indices = [gate["index"] for gate in gates]
    if indices != list(range(len(gates))):
        raise GenerationError("gate indices are not contiguous in configure order")
    lookup_indices = [lookup["index"] for lookup in lookups]
    if lookup_indices != list(range(len(lookups))):
        raise GenerationError("lookup indices are not contiguous in configure order")
    summary = copy.deepcopy(configure.get("summary", {}))
    if parse_int(summary.get("gate_count")) not in {None, len(gates)}:
        raise GenerationError("configure gate_count does not match operations")
    if parse_int(summary.get("lookup_count")) not in {None, len(lookups)}:
        raise GenerationError("configure lookup_count does not match operations")
    return {
        "summary": summary,
        "entrypointSource": copy.deepcopy(entrypoint_source),
        "operations": operation_index,
        "gates": gates,
        "lookups": lookups,
    }


def normalize_raw_synthesis(
    synthesis: Mapping[str, Any],
    source_index: SourceIndex,
    symbols: Mapping[str, Mapping[str, str]],
    flow_nodes: Sequence[Mapping[str, Any]],
) -> SynthesisBuild:
    raw_nodes = synthesis.get("nodes")
    if not isinstance(raw_nodes, list):
        raise GenerationError("raw synthesis.nodes must be an array")
    regions: list[dict[str, Any]] = []
    layout_operations: list[dict[str, Any]] = []
    instance_rows: MutableMapping[int, dict[str, Any]] = defaultdict(
        lambda: {"operationIds": set(), "cellIds": set()}
    )
    seen_ids: set[str] = set()

    def walk_nodes(
        nodes: Sequence[Any],
        namespace_names: list[str],
        namespace_ids: list[str],
        namespace_occurrences: list[int],
    ) -> list[dict[str, Any]]:
        result: list[dict[str, Any]] = []
        sibling_counts: Counter[str] = Counter()
        for raw_node in nodes:
            if not isinstance(raw_node, dict):
                raise GenerationError("synthesis tree node must be an object")
            node_id = raw_node.get("id")
            kind = raw_node.get("kind")
            if not isinstance(node_id, str) or node_id in seen_ids:
                raise GenerationError(f"missing or duplicate synthesis node ID: {node_id!r}")
            seen_ids.add(node_id)
            if kind == "namespace":
                name = raw_node.get("name")
                children = raw_node.get("children")
                if not isinstance(name, str) or not isinstance(children, list):
                    raise GenerationError(f"malformed namespace node {node_id}")
                sibling_counts[name] += 1
                occurrence = sibling_counts[name]
                enriched = {
                    "id": node_id,
                    "kind": "namespace",
                    "name": name,
                    "occurrence": occurrence,
                    "namespace": [*namespace_names, name],
                    "namespaceIds": [*namespace_ids, node_id],
                    "children": walk_nodes(
                        children,
                        [*namespace_names, name],
                        [*namespace_ids, node_id],
                        [*namespace_occurrences, occurrence],
                    ),
                }
                result.append(enriched)
            elif kind == "region":
                name = raw_node.get("name")
                operations = raw_node.get("operations")
                if not isinstance(name, str) or not isinstance(operations, list):
                    raise GenerationError(f"malformed region node {node_id}")
                annotated_operations = annotate_symbols(copy.deepcopy(operations), symbols)
                for operation in annotated_operations:
                    operation_id = operation.get("id")
                    if not isinstance(operation_id, str):
                        raise GenerationError(f"operation without stable ID in {node_id}")
                    record_instance_references(operation, operation_id, instance_rows)
                occurrence = len(regions)
                resolution = source_index.resolution(name, kind="region")
                enriched = annotate_symbols(copy.deepcopy(raw_node), symbols)
                enriched.update(
                    {
                        "rawId": node_id,
                        "occurrence": occurrence,
                        "regionIndex": raw_node.get("region_index"),
                        "startRow": raw_node.get("start_row"),
                        "namespace": list(namespace_names),
                        "namespaceIds": list(namespace_ids),
                        "rootNamespace": namespace_names[0] if namespace_names else None,
                        "rootNamespaceOccurrence": namespace_occurrences[0]
                        if namespace_occurrences
                        else None,
                        "operations": annotated_operations,
                        "metrics": operation_metrics(
                            annotated_operations,
                            region_index=parse_int(raw_node.get("region_index")),
                        ),
                        "source": resolution,
                    }
                )
                enriched["componentId"] = match_region_component(enriched, flow_nodes)
                annotations = {
                    str(operation.get("annotation"))
                    for operation in annotated_operations
                    if operation.get("annotation")
                }
                enriched["searchTerms"] = sorted(
                    set(
                        [
                            name,
                            *namespace_names,
                            *annotations,
                            *collect_symbolic_terms(annotated_operations),
                            *source_terms(resolution, source_index),
                        ]
                    ),
                    key=lambda item: (item.casefold(), item),
                )
                regions.append(make_region_summary(enriched))
                result.append(enriched)
            elif kind in {"constrain_instance", "init_lookup_tables"}:
                enriched = annotate_symbols(copy.deepcopy(raw_node), symbols)
                if kind == "constrain_instance":
                    row = parse_int(raw_node.get("row"))
                    enriched["componentId"] = match_instance_component(row, flow_nodes)
                    if row is not None:
                        instance_record = instance_rows[row]
                        instance_record["operationIds"].add(node_id)
                        cell_id = raw_node.get("instance_cell_id")
                        if isinstance(cell_id, str):
                            instance_record["cellIds"].add(cell_id)
                    record_instance_references(enriched, node_id, instance_rows)
                else:
                    enriched["componentId"] = component_id("lookup-tables")
                enriched["namespace"] = list(namespace_names)
                enriched["namespaceIds"] = list(namespace_ids)
                enriched["searchTerms"] = collect_symbolic_terms(enriched)
                layout_operations.append(enriched)
                result.append(enriched)
            else:
                raise GenerationError(f"unsupported synthesis node kind {kind!r} in {node_id}")
        return result

    tree = walk_nodes(raw_nodes, [], [], [])
    return SynthesisBuild(
        tree=tree,
        regions=regions,
        layout_operations=layout_operations,
        instance_rows=instance_rows,
    )


def normalize_highlevel_configure(
    configure: Mapping[str, Any],
    source_index: SourceIndex,
    symbols: Mapping[str, Mapping[str, str]],
    entrypoint_source: Mapping[str, Any],
) -> dict[str, Any]:
    raw_gates = configure.get("gates")
    raw_lookups = configure.get("lookups")
    if not isinstance(raw_gates, list) or not isinstance(raw_lookups, list):
        raise GenerationError("Orchard high-level configure must contain gates and lookups arrays")
    gates: list[dict[str, Any]] = []
    operations: list[dict[str, Any]] = []
    for position, raw_gate in enumerate(raw_gates):
        if not isinstance(raw_gate, dict):
            raise GenerationError(f"high-level gate {position} is malformed")
        index = parse_int(raw_gate.get("index"))
        if index is None:
            index = position
        gate_id = f"gate:{index}"
        gate = annotate_symbols(copy.deepcopy(raw_gate), symbols)
        name = gate.get("name")
        if not isinstance(name, str):
            raise GenerationError(f"{gate_id} has no name")
        constraints = []
        for constraint_position, constraint in enumerate(gate.get("constraints", [])):
            constraint_index = parse_int(constraint.get("index"))
            if constraint_index is None:
                constraint_index = constraint_position
            constraints.append(
                {
                    "id": f"{gate_id}/constraint:{constraint_index}",
                    **constraint,
                }
            )
        resolution = source_index.resolution(name, kind="gate")
        if resolution["confidence"] == "ambiguous":
            raise GenerationError(f"gate {name!r} has multiple exact Rocq definitions")
        gate.update(
            {
                "id": gate_id,
                "index": index,
                "constraints": constraints,
                "configureOperationId": f"configure-op:{position}",
                "source": resolution,
            }
        )
        gate["searchTerms"] = sorted(
            set([name, *collect_symbolic_terms(gate), *source_terms(resolution, source_index)]),
            key=lambda item: (item.casefold(), item),
        )
        gates.append(gate)
        operations.append(
            {"id": f"configure-op:{position}", "kind": "create_gate", "gateId": gate_id, "gateIndex": index}
        )

    lookups = []
    for position, raw_lookup in enumerate(raw_lookups):
        index = parse_int(raw_lookup.get("index")) if isinstance(raw_lookup, dict) else None
        if index is None:
            index = position
        lookup_id = f"lookup-argument:{index}"
        lookup = annotate_symbols(copy.deepcopy(raw_lookup), symbols)
        lookup.update(
            {
                "id": lookup_id,
                "index": index,
                "configureOperationId": f"configure-op:{len(operations)}",
            }
        )
        lookup["searchTerms"] = collect_symbolic_terms(lookup)
        lookups.append(lookup)
        operations.append(
            {
                "id": f"configure-op:{len(operations)}",
                "kind": "create_lookup",
                "lookupId": lookup_id,
                "lookupIndex": index,
            }
        )

    resource_keys = [
        "schema",
        "columns",
        "selectors",
        "advice_queries",
        "instance_queries",
        "fixed_queries",
        "permutation",
        "constants",
        "minimum_degree",
    ]
    resources = annotate_symbols(
        {key: copy.deepcopy(configure[key]) for key in resource_keys if key in configure}, symbols
    )
    return {
        "summary": {
            "operation_count": len(operations),
            "gate_count": len(gates),
            "lookup_count": len(lookups),
            "constraint_count": sum(len(gate.get("constraints", [])) for gate in gates),
        },
        "entrypointSource": copy.deepcopy(entrypoint_source),
        "resources": resources,
        "operations": operations,
        "gates": gates,
        "lookups": lookups,
    }


def normalize_highlevel_synthesis(
    synthesis: Mapping[str, Any],
    source_index: SourceIndex,
    symbols: Mapping[str, Mapping[str, str]],
    flow_nodes: Sequence[Mapping[str, Any]],
) -> SynthesisBuild:
    events = synthesis.get("events")
    if not isinstance(events, list):
        raise GenerationError("Orchard high-level synthesis.events must be an array")
    root: list[dict[str, Any]] = []
    child_stack: list[list[dict[str, Any]]] = [root]
    namespace_stack: list[dict[str, Any]] = []
    sibling_counts_stack: list[Counter[str]] = [Counter()]
    current_region: dict[str, Any] | None = None
    regions: list[dict[str, Any]] = []
    layout_operations: list[dict[str, Any]] = []
    instance_rows: MutableMapping[int, dict[str, Any]] = defaultdict(
        lambda: {"operationIds": set(), "cellIds": set()}
    )

    for position, raw_event in enumerate(events):
        if not isinstance(raw_event, dict):
            raise GenerationError(f"high-level event {position} is malformed")
        event_index = parse_int(raw_event.get("index"))
        if event_index is None:
            event_index = position
        event_kind = raw_event.get("event")
        if not isinstance(event_kind, str):
            raise GenerationError(f"high-level event {position} has no event kind")
        if event_kind == "push_namespace":
            if current_region is not None:
                raise GenerationError("namespace pushed inside an active region")
            name = raw_event.get("name")
            if not isinstance(name, str):
                raise GenerationError(f"push_namespace event {event_index} has no name")
            sibling_counts_stack[-1][name] += 1
            occurrence = sibling_counts_stack[-1][name]
            node_id = f"namespace:{event_index}"
            node = {
                "id": node_id,
                "kind": "namespace",
                "name": name,
                "occurrence": occurrence,
                "namespace": [*[item["name"] for item in namespace_stack], name],
                "namespaceIds": [*[item["id"] for item in namespace_stack], node_id],
                "children": [],
            }
            child_stack[-1].append(node)
            namespace_stack.append(node)
            child_stack.append(node["children"])
            sibling_counts_stack.append(Counter())
        elif event_kind == "pop_namespace":
            if current_region is not None:
                raise GenerationError("namespace popped inside an active region")
            if not namespace_stack:
                raise GenerationError(f"pop_namespace event {event_index} underflows the stack")
            name = raw_event.get("name")
            if name is not None and name != namespace_stack[-1]["name"]:
                raise GenerationError(f"namespace pop mismatch at event {event_index}")
            namespace_stack.pop()
            child_stack.pop()
            sibling_counts_stack.pop()
        elif event_kind == "enter_region":
            if current_region is not None:
                raise GenerationError("nested regions are not supported by the V1 floor planner")
            name = raw_event.get("name")
            if not isinstance(name, str):
                raise GenerationError(f"enter_region event {event_index} has no name")
            occurrence = len(regions)
            region_id = f"region:{occurrence}"
            resolution = source_index.resolution(name, kind="region")
            current_region = {
                "id": region_id,
                "rawId": None,
                "kind": "region",
                "occurrence": occurrence,
                "regionIndex": None,
                "startRow": None,
                "name": name,
                "namespace": [item["name"] for item in namespace_stack],
                "namespaceIds": [item["id"] for item in namespace_stack],
                "rootNamespace": namespace_stack[0]["name"] if namespace_stack else None,
                "rootNamespaceOccurrence": namespace_stack[0]["occurrence"]
                if namespace_stack
                else None,
                "eventRange": {"start": event_index, "end": None},
                "operations": [],
                "source": resolution,
            }
            current_region["componentId"] = match_region_component(current_region, flow_nodes)
            child_stack[-1].append(current_region)
        elif event_kind == "exit_region":
            if current_region is None:
                raise GenerationError(f"exit_region event {event_index} has no matching region")
            current_region["eventRange"]["end"] = event_index
            current_region["metrics"] = operation_metrics(current_region["operations"])
            current_region["startRow"] = (
                current_region["metrics"]["rowRange"]["min"]
                if current_region["metrics"]["rowRange"]
                else None
            )
            annotations = {
                str(operation.get("annotation"))
                for operation in current_region["operations"]
                if operation.get("annotation")
            }
            current_region["searchTerms"] = sorted(
                set(
                    [
                        current_region["name"],
                        *current_region["namespace"],
                        *annotations,
                        *collect_symbolic_terms(current_region["operations"]),
                        *source_terms(current_region["source"], source_index),
                    ]
                ),
                key=lambda item: (item.casefold(), item),
            )
            regions.append(make_region_summary(current_region))
            current_region = None
        else:
            operation = annotate_symbols(
                {
                    "id": f"layout-op:{event_index}",
                    "kind": event_kind,
                    "eventIndex": event_index,
                    **{
                        key: copy.deepcopy(value)
                        for key, value in raw_event.items()
                        if key not in {"index", "event", "region", "namespace"}
                    },
                },
                symbols,
            )
            record_instance_references(operation, operation["id"], instance_rows)
            if current_region is not None:
                current_region["operations"].append(operation)
            else:
                row = parse_int(operation.get("row"))
                operation["componentId"] = match_instance_component(row, flow_nodes)
                operation["namespace"] = [item["name"] for item in namespace_stack]
                operation["namespaceIds"] = [item["id"] for item in namespace_stack]
                operation["searchTerms"] = collect_symbolic_terms(operation)
                layout_operations.append(operation)
                child_stack[-1].append(operation)

    if current_region is not None or namespace_stack:
        raise GenerationError("unterminated region or namespace in high-level synthesis events")
    return SynthesisBuild(root, regions, layout_operations, instance_rows)


def flatten_synthesis_tree(
    tree: Sequence[Mapping[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    namespaces: list[dict[str, Any]] = []
    operations: list[dict[str, Any]] = []

    def walk(nodes: Sequence[Mapping[str, Any]]) -> None:
        for node in nodes:
            kind = node.get("kind")
            if kind == "namespace":
                namespaces.append(
                    {
                        "id": node["id"],
                        "name": node["name"],
                        "occurrence": node["occurrence"],
                        "namespace": node["namespace"],
                        "namespaceIds": node["namespaceIds"],
                        "childIds": [child["id"] for child in node["children"]],
                    }
                )
                walk(node["children"])
            elif kind == "region":
                for operation in node.get("operations", []):
                    operations.append(
                        {
                            **copy.deepcopy(operation),
                            "regionId": node["id"],
                        }
                    )
            else:
                operations.append(copy.deepcopy(node))

    walk(tree)
    return namespaces, operations


def compact_tree_operation_payloads(tree: Sequence[dict[str, Any]]) -> None:
    """Keep the exact operation order in the tree while storing payloads once."""

    for node in tree:
        if node.get("kind") == "namespace":
            compact_tree_operation_payloads(node.get("children", []))
        elif node.get("kind") == "region":
            operations = node.pop("operations", [])
            node["operationIds"] = [operation["id"] for operation in operations]


def collect_selector_ids(value: Any) -> list[str]:
    selectors: set[str] = set()

    def visit(item: Any) -> None:
        if isinstance(item, list):
            for child in item:
                visit(child)
        elif isinstance(item, dict):
            selector_id = item.get("selector_id")
            if isinstance(selector_id, str) and re.fullmatch(r"selector:[0-9]+", selector_id):
                selectors.add(selector_id)
            selector = item.get("selector")
            if not isinstance(selector, (dict, list, bool)):
                parsed = parse_int(selector)
                if parsed is not None:
                    selectors.add(f"selector:{parsed}")
            for child in item.values():
                visit(child)

    visit(value)
    return sorted(selectors, key=lambda item: int(item.split(":", 1)[1]))


def collect_table_ids(value: Any) -> list[str]:
    tables: set[str] = set()

    def visit(item: Any) -> None:
        if isinstance(item, list):
            for child in item:
                visit(child)
        elif isinstance(item, dict):
            table = item.get("table")
            if not isinstance(table, (dict, list, bool)):
                parsed = parse_int(table)
                if parsed is not None:
                    tables.add(f"lookup-column:{parsed}")
            for child in item.values():
                visit(child)

    visit(value)
    return sorted(tables, key=lambda item: int(item.rsplit(":", 1)[1]))


def add_configure_synthesis_links(
    configure: MutableMapping[str, Any],
    synthesis_build: SynthesisBuild,
) -> None:
    selector_to_gates: MutableMapping[str, set[str]] = defaultdict(set)
    selector_to_lookups: MutableMapping[str, set[str]] = defaultdict(set)
    selector_to_regions: MutableMapping[str, set[str]] = defaultdict(set)
    regions_by_id = {region["id"]: region for region in synthesis_build.regions}

    for gate in configure["gates"]:
        selector_ids = collect_selector_ids(gate.get("constraints", []))
        gate["selectorIds"] = selector_ids
        for selector_id in selector_ids:
            selector_to_gates[selector_id].add(gate["id"])
    for lookup in configure["lookups"]:
        selector_ids = collect_selector_ids(lookup)
        table_ids = collect_table_ids(lookup)
        lookup["selectorIds"] = selector_ids
        lookup["tableIds"] = table_ids
        for selector_id in selector_ids:
            selector_to_lookups[selector_id].add(lookup["id"])

    def enrich_tree(nodes: Sequence[MutableMapping[str, Any]]) -> None:
        for node in nodes:
            if node.get("kind") == "namespace":
                enrich_tree(node.get("children", []))
            elif node.get("kind") == "region":
                selector_ids = collect_selector_ids(node.get("operations", []))
                gate_ids = sorted(
                    {gate_id for selector in selector_ids for gate_id in selector_to_gates[selector]}
                )
                lookup_ids = sorted(
                    {
                        lookup_id
                        for selector in selector_ids
                        for lookup_id in selector_to_lookups[selector]
                    }
                )
                node["selectorIds"] = selector_ids
                node["gateIds"] = gate_ids
                node["lookupIds"] = lookup_ids
                summary = regions_by_id[node["id"]]
                summary["selectorIds"] = selector_ids
                summary["gateIds"] = gate_ids
                summary["lookupIds"] = lookup_ids
                for selector_id in selector_ids:
                    selector_to_regions[selector_id].add(node["id"])

    enrich_tree(synthesis_build.tree)
    for gate in configure["gates"]:
        region_ids = sorted(
            {region_id for selector in gate["selectorIds"] for region_id in selector_to_regions[selector]},
            key=lambda identifier: int(identifier.split(":", 1)[1]),
        )
        component_ids = sorted(
            {
                regions_by_id[region_id]["componentId"]
                for region_id in region_ids
                if regions_by_id[region_id].get("componentId") is not None
            }
        )
        gate["regionIds"] = region_ids
        gate["componentIds"] = component_ids
        gate["componentId"] = component_ids[0] if len(component_ids) == 1 else None
    for lookup in configure["lookups"]:
        region_ids = sorted(
            {
                region_id
                for selector in lookup["selectorIds"]
                for region_id in selector_to_regions[selector]
            },
            key=lambda identifier: int(identifier.split(":", 1)[1]),
        )
        lookup["regionIds"] = region_ids
        lookup["componentIds"] = sorted(
            {
                regions_by_id[region_id]["componentId"]
                for region_id in region_ids
                if regions_by_id[region_id].get("componentId") is not None
            }
        )


def build_region_groups(regions: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    buckets: MutableMapping[tuple[str | None, str], list[Mapping[str, Any]]] = defaultdict(list)
    for region in regions:
        buckets[(region.get("componentId"), str(region["name"]))].append(region)
    groups = []
    for (component, name), members in sorted(
        buckets.items(), key=lambda item: ((item[0][0] or ""), item[0][1].casefold(), item[0][1])
    ):
        operation_counts: Counter[str] = Counter()
        operation_count = 0
        rows: list[int] = []
        for member in members:
            metrics = member["metrics"]
            operation_count += metrics["operationCount"]
            operation_counts.update(metrics["operationCounts"])
            if metrics["rowRange"]:
                rows.extend([metrics["rowRange"]["min"], metrics["rowRange"]["max"]])
        identity = json.dumps([component, name], ensure_ascii=False, separators=(",", ":"))
        groups.append(
            {
                "id": f"region-group:{slug(component or 'unclassified')}:{slug(name)}-{sha256_text(identity)[:8]}",
                "name": name,
                "componentId": component,
                "occurrenceCount": len(members),
                "regionIds": [member["id"] for member in members],
                "selectorIds": sorted(
                    {identifier for member in members for identifier in member.get("selectorIds", [])},
                    key=lambda identifier: int(identifier.split(":", 1)[1]),
                ),
                "gateIds": sorted(
                    {identifier for member in members for identifier in member.get("gateIds", [])}
                ),
                "lookupIds": sorted(
                    {identifier for member in members for identifier in member.get("lookupIds", [])}
                ),
                "metrics": {
                    "operationCount": operation_count,
                    "operationCounts": dict(sorted(operation_counts.items())),
                    "rowRange": {"min": min(rows), "max": max(rows)} if rows else None,
                },
                "source": copy.deepcopy(members[0]["source"]),
                "searchTerms": sorted(
                    set(term for member in members for term in member["searchTerms"]),
                    key=lambda item: (item.casefold(), item),
                ),
            }
        )
    return groups


INSTANCE_ROW_LABELS = {
    0: "ANCHOR",
    1: "CV_NET_X",
    2: "CV_NET_Y",
    3: "NF_OLD",
    4: "RK_X",
    5: "RK_Y",
    6: "CMX",
    7: "ENABLE_SPEND",
    8: "ENABLE_OUTPUT",
}


def build_instance_rows(
    instance_references: Mapping[int, Mapping[str, Any]],
    flow_nodes: Sequence[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    rows = []
    for row, label in INSTANCE_ROW_LABELS.items():
        references = instance_references.get(row, {})
        component = match_instance_component(row, flow_nodes)
        rows.append(
            {
                "id": f"instance-row:{row}",
                "row": row,
                "name": label,
                "componentId": component,
                "role": "control-flag" if row >= 7 else "statement-entry",
                "operationIds": sorted(references.get("operationIds", set())),
                "cellIds": sorted(references.get("cellIds", set())),
                "searchTerms": [label, f"instance row {row}", "Primary"],
            }
        )
    return rows


def default_instance_proof_nodes(row: int) -> list[str]:
    if row in {0, 7, 8}:
        return ["action-valid-inputs", "action-theorem", "capture-synthesis-model"]
    return ["action-seven-outputs", "action-theorem", "capture-synthesis-model"]


def build_flow(
    flow_manifest: Mapping[str, Any],
    configure: Mapping[str, Any],
    regions: Sequence[Mapping[str, Any]],
    operations: Sequence[Mapping[str, Any]],
    instance_rows: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    nodes = []
    operations_by_id = {
        operation["id"]: operation
        for operation in operations
        if isinstance(operation.get("id"), str)
    }
    for manifest_node in flow_manifest.get("nodes", []):
        identifier = component_id(str(manifest_node["id"]))
        member_regions = [region for region in regions if region.get("componentId") == identifier]
        member_operations = [
            operation for operation in operations if operation.get("componentId") == identifier
        ]
        member_rows = [row for row in instance_rows if row.get("componentId") == identifier]
        operation_counts: Counter[str] = Counter()
        operation_count = 0
        counted_operation_ids: set[str] = set()
        for region in member_regions:
            operation_count += region["metrics"]["operationCount"]
            operation_counts.update(region["metrics"]["operationCounts"])
            counted_operation_ids.update(
                operation["id"]
                for operation in operations
                if operation.get("regionId") == region["id"]
                and isinstance(operation.get("id"), str)
            )
        for operation in member_operations:
            if not operation.get("regionId"):
                operation_count += 1
                operation_counts[str(operation.get("kind", "unknown"))] += 1
                counted_operation_ids.add(operation["id"])
        for operation_id in {
            operation_id
            for row in member_rows
            for operation_id in row.get("operationIds", [])
        } - counted_operation_ids:
            operation = operations_by_id.get(operation_id)
            if operation is not None:
                operation_count += 1
                operation_counts[str(operation.get("kind", "unknown"))] += 1
                counted_operation_ids.add(operation_id)
        proof_node_ids = list(manifest_node.get("proof_node_ids", []))
        if member_rows and not proof_node_ids:
            proof_node_ids = default_instance_proof_nodes(int(member_rows[0]["row"]))
        gate_ids = sorted(
            {identifier for region in member_regions for identifier in region.get("gateIds", [])}
        )
        lookup_ids = sorted(
            {identifier for region in member_regions for identifier in region.get("lookupIds", [])}
        )
        selector_ids = sorted(
            {identifier for region in member_regions for identifier in region.get("selectorIds", [])},
            key=lambda identifier: int(identifier.split(":", 1)[1]),
        )
        table_ids = sorted(
            {
                entry["id"]
                for operation in member_operations
                if operation.get("kind") == "init_lookup_tables"
                for entry in operation.get("entries", [])
                if isinstance(entry, dict) and isinstance(entry.get("id"), str)
            }
        )
        if table_ids:
            linked_lookups = [
                lookup
                for lookup in configure["lookups"]
                if set(lookup.get("tableIds", [])) & set(table_ids)
            ]
            lookup_ids = sorted({*lookup_ids, *(lookup["id"] for lookup in linked_lookups)})
            selector_ids = sorted(
                {
                    *selector_ids,
                    *(selector for lookup in linked_lookups for selector in lookup.get("selectorIds", [])),
                },
                key=lambda identifier: int(identifier.split(":", 1)[1]),
            )
        nodes.append(
            {
                "id": identifier,
                "alias": manifest_node["id"],
                "kind": manifest_node["kind"],
                "title": manifest_node["title"],
                "shortTitle": manifest_node["short_title"],
                "summary": manifest_node["summary"],
                "position": copy.deepcopy(manifest_node["position"]),
                "proofNodeIds": proof_node_ids,
                "proofMapLinks": [f"proof-map.html#node={node_id}" for node_id in proof_node_ids],
                "regionIds": [region["id"] for region in member_regions],
                "layoutOperationIds": [
                    operation["id"] for operation in member_operations if not operation.get("regionId")
                ],
                "instanceRowIds": [row["id"] for row in member_rows],
                "selectorIds": selector_ids,
                "gateIds": gate_ids,
                "lookupIds": lookup_ids,
                "tableIds": table_ids,
                "metrics": {
                    "regionCount": len(member_regions),
                    "operationCount": operation_count,
                    "operationCounts": dict(sorted(operation_counts.items())),
                },
                "searchTerms": sorted(
                    set(
                        [
                            manifest_node["title"],
                            manifest_node["short_title"],
                            *proof_node_ids,
                            *(row["name"] for row in member_rows),
                        ]
                    ),
                    key=lambda item: (item.casefold(), item),
                ),
            }
        )
        if not member_regions and not member_operations and not member_rows:
            raise GenerationError(
                f"curated component matcher resolved no target: {manifest_node['id']}"
            )
    edges = [
        {
            "id": f"flow-edge:{edge['id']}",
            "from": component_id(str(edge["from"])),
            "to": component_id(str(edge["to"])),
            "label": edge["label"],
            "summary": edge.get("summary", ""),
            "kind": edge.get("kind", "data"),
        }
        for edge in flow_manifest.get("edges", [])
    ]
    return {
        "bounds": copy.deepcopy(flow_manifest["bounds"]),
        "proofNodeIds": ["capture-synthesis-model"],
        "proofMapLinks": ["proof-map.html#node=capture-synthesis-model"],
        "nodes": nodes,
        "edges": edges,
    }


def validate_raw_summary(
    summary: Mapping[str, Any],
    namespaces: Sequence[Mapping[str, Any]],
    regions: Sequence[Mapping[str, Any]],
    operations: Sequence[Mapping[str, Any]],
) -> None:
    expected_region_count = parse_int(summary.get("region_count"))
    expected_namespace_count = parse_int(summary.get("namespace_count"))
    expected_operation_count = parse_int(summary.get("region_operation_count"))
    actual_region_operations = sum(1 for operation in operations if operation.get("regionId"))
    if expected_region_count is not None and expected_region_count != len(regions):
        raise GenerationError(
            f"raw region_count says {expected_region_count}, flattened tree has {len(regions)}"
        )
    if expected_namespace_count is not None and expected_namespace_count != len(namespaces):
        raise GenerationError(
            f"raw namespace_count says {expected_namespace_count}, flattened tree has {len(namespaces)}"
        )
    if expected_operation_count is not None and expected_operation_count != actual_region_operations:
        raise GenerationError(
            "raw region_operation_count says "
            f"{expected_operation_count}, flattened tree has {actual_region_operations}"
        )
    semantic_indices = [parse_int(region.get("regionIndex")) for region in regions]
    if all(index is not None for index in semantic_indices):
        if semantic_indices != list(range(len(regions))):
            raise GenerationError("semantic region indices are not contiguous in tree order")


def build_diagnostics(
    configure: Mapping[str, Any],
    regions: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    warnings = []
    for confidence in ("ambiguous", "unresolved"):
        names = sorted(
            {
                str(region["name"])
                for region in regions
                if region["source"]["confidence"] == confidence
            },
            key=lambda item: (item.casefold(), item),
        )
        if names:
            affected = [region["id"] for region in regions if region["name"] in names]
            warnings.append(
                {
                    "code": f"region-source-{confidence}",
                    "message": (
                        f"{len(names)} distinct region names have {confidence} source provenance; "
                        "all candidates are retained and no first grep hit is selected."
                    ),
                    "names": names,
                    "entityIds": affected,
                }
            )
    unmatched = [region["id"] for region in regions if region.get("componentId") is None]
    if unmatched:
        warnings.append(
            {
                "code": "unclassified-regions",
                "message": f"{len(unmatched)} exact region occurrences are outside the curated flow.",
                "entityIds": unmatched,
            }
        )
    unresolved_gates = [
        gate["id"] for gate in configure["gates"] if gate["source"]["confidence"] == "unresolved"
    ]
    if unresolved_gates:
        warnings.append(
            {
                "code": "gate-source-unresolved",
                "message": f"{len(unresolved_gates)} gates have no exact Rocq definition.",
                "entityIds": unresolved_gates,
            }
        )
    return {
        "errors": [],
        "warnings": warnings,
        "summary": {
            "errorCount": 0,
            "warningCount": len(warnings),
            "exactGateSources": sum(
                gate["source"]["confidence"] == "exact" for gate in configure["gates"]
            ),
            "exactRegionSources": sum(
                region["source"]["confidence"] == "exact" for region in regions
            ),
            "ambiguousRegionSources": sum(
                region["source"]["confidence"] == "ambiguous" for region in regions
            ),
            "unresolvedRegionSources": sum(
                region["source"]["confidence"] == "unresolved" for region in regions
            ),
            "unclassifiedRegions": len(unmatched),
        },
    }


def canonical_input_label(schema: str) -> str:
    if schema == RAW_SCHEMA:
        return "Garden/Orchard/Snapshots/circuit_structure_generated_from_model.json"
    if schema == ORCHARD_HIGHLEVEL_SCHEMA:
        return "orchard/src/circuit_data/action_circuit.highlevel.json"
    return "unknown-input.json"


def build_sources(source_index: SourceIndex, repositories: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    records = [source_index.records[key] for key in sorted(source_index.records)]
    files = [source_index.files[key] for key in sorted(source_index.files)]
    return {
        "confidenceLevels": {
            "exact": "One exact literal or curated symbol in the translated Rocq source.",
            "mapped": "A deterministic path/symbol mapping to the pinned Rust implementation.",
            "ambiguous": "More than one exact Rocq source candidate; no primary was selected.",
            "unresolved": "No exact source site was found; the missing mapping remains explicit.",
        },
        "repositories": copy.deepcopy(list(repositories)),
        "files": files,
        "records": records,
        "summary": {
            "fileCount": len(files),
            "recordCount": len(records),
            "rocqRecordCount": sum(record["language"] == "rocq" for record in records),
            "rustRecordCount": sum(record["language"] == "rust" for record in records),
        },
    }


def generate_data(
    input_data: Mapping[str, Any],
    input_bytes: bytes,
    manifest: Mapping[str, Any],
    manifest_bytes: bytes,
    garden_root: Path,
    *,
    input_label: str | None = None,
) -> dict[str, Any]:
    validate_manifest(manifest)
    schema = input_data.get("schema")
    if schema not in {RAW_SCHEMA, ORCHARD_HIGHLEVEL_SCHEMA}:
        raise GenerationError(
            f"unsupported input schema {schema!r}; expected {RAW_SCHEMA!r} or {ORCHARD_HIGHLEVEL_SCHEMA!r}"
        )
    repositories = manifest["repositories"]
    repositories_by_id = {item["id"]: item for item in repositories}
    source_index = SourceIndex(repositories_by_id)
    scan_rocq_sources(garden_root, manifest["source_scan"]["rocq"], source_index)

    columns_path = path_inside(
        garden_root,
        garden_root / "Garden" / "Orchard" / "columns.v",
        label="column definitions",
    )
    symbols = parse_column_symbols(columns_path)
    source_index.add_file(
        "garden",
        columns_path.relative_to(garden_root).as_posix(),
        "rocq",
        columns_path.read_bytes(),
    )
    add_mapped_rust_sites(source_index, manifest["source_scan"].get("rust_path_maps", []))
    entrypoint_source = add_configure_entrypoints(
        garden_root,
        manifest["source_scan"].get("configure_entrypoints", []),
        source_index,
    )
    flow_nodes = manifest["flow"]["nodes"]

    if schema == RAW_SCHEMA:
        configure_input = input_data.get("configure")
        synthesis_input = input_data.get("synthesis")
        if not isinstance(configure_input, dict) or not isinstance(synthesis_input, dict):
            raise GenerationError("raw input requires configure and synthesis objects")
        configure = normalize_raw_configure(
            configure_input, source_index, symbols, entrypoint_source
        )
        synthesis_build = normalize_raw_synthesis(
            synthesis_input, source_index, symbols, flow_nodes
        )
        synthesis_summary = copy.deepcopy(synthesis_input.get("summary", {}))
        floor_planner = "V1"
        circuit = copy.deepcopy(manifest["circuit"])
    else:
        configure_input = input_data.get("configure")
        synthesis_input = input_data.get("synthesis")
        if not isinstance(configure_input, dict) or not isinstance(synthesis_input, dict):
            raise GenerationError("Orchard high-level input requires configure and synthesis objects")
        configure = normalize_highlevel_configure(
            configure_input, source_index, symbols, entrypoint_source
        )
        synthesis_build = normalize_highlevel_synthesis(
            synthesis_input, source_index, symbols, flow_nodes
        )
        synthesis_summary = copy.deepcopy(synthesis_input.get("summary", {}))
        floor_planner = synthesis_input.get("floor_planner", "V1")
        circuit = copy.deepcopy(input_data.get("circuit", manifest["circuit"]))

    add_configure_synthesis_links(configure, synthesis_build)
    namespaces, operations = flatten_synthesis_tree(synthesis_build.tree)
    if schema == RAW_SCHEMA:
        validate_raw_summary(
            synthesis_summary, namespaces, synthesis_build.regions, operations
        )
    instance_rows = build_instance_rows(synthesis_build.instance_rows, flow_nodes)
    region_groups = build_region_groups(synthesis_build.regions)
    flow = build_flow(
        manifest["flow"], configure, synthesis_build.regions, operations, instance_rows
    )
    diagnostics = build_diagnostics(configure, synthesis_build.regions)
    compact_tree_operation_payloads(synthesis_build.tree)

    synthesis_summary.update(
        {
            "namespaceCount": len(namespaces),
            "regionCount": len(synthesis_build.regions),
            "operationCount": len(operations),
            "regionGroupCount": len(region_groups),
            "componentCount": len(flow["nodes"]),
        }
    )
    output = {
        "schema": OUTPUT_SCHEMA,
        "metadata": {
            "generator": {"name": GENERATOR_NAME, "version": manifest["generator_version"]},
            "manifestSha256": sha256_bytes(manifest_bytes),
            "input": {
                "schema": schema,
                "path": input_label or canonical_input_label(str(schema)),
                "sha256": sha256_bytes(input_bytes),
            },
            "circuit": circuit,
            "floorPlanner": floor_planner,
            "placement": (
                "Namespace, region, and operation structure is evaluated from the Rocq "
                "free monads; regionIndex, startRow, and absoluteRow use the "
                "implementation-generated V1 region-start table in "
                "Garden/Orchard/circuit_synthesis_layout.v."
            ),
            "repositoryRefs": {
                repository["id"]: repository["revision"] for repository in repositories
            },
            "symbols": {
                "selectors": symbols["selector"],
                "columns": {
                    "advice": symbols["advice"],
                    "lookup": symbols["lookup"],
                    "fixed": symbols["fixed"],
                    "instance": symbols["instance"],
                },
                "instanceRows": {str(row): name for row, name in INSTANCE_ROW_LABELS.items()},
            },
            "representations": {
                "tree": "Exact recursive namespace/region tree with ordered operation IDs.",
                "namespaces": "Flattened namespace index; children remain authoritative in tree.",
                "regions": "Flattened exact-occurrence summaries; operations remain authoritative in tree.",
                "operations": "The single complete operation store; regionId resolves namespace and occurrence context.",
                "placement": "Relative cells come from the free-monad trace; physical rows use the pinned V1 region-start table.",
                "regionGroups": "Derived aggregation by curated component and exact region name.",
                "flow": "Curated functional interpretation; it is not inferred proof evidence.",
            },
        },
        "configure": configure,
        "synthesis": {
            "summary": synthesis_summary,
            "tree": synthesis_build.tree,
            "namespaces": namespaces,
            "regions": synthesis_build.regions,
            "operations": operations,
            "regionGroups": region_groups,
            "instanceRows": instance_rows,
        },
        "flow": flow,
        "sources": build_sources(source_index, repositories),
        "diagnostics": diagnostics,
    }
    validate_generated_data(output)
    return output


def duplicate_ids(items: Sequence[Mapping[str, Any]]) -> list[str]:
    ids = [item.get("id") for item in items]
    counts = Counter(ids)
    return sorted(str(identifier) for identifier, count in counts.items() if count > 1)


def validate_generated_data(data: Mapping[str, Any]) -> None:
    if data.get("schema") != OUTPUT_SCHEMA:
        raise GenerationError(f"generated schema must be {OUTPUT_SCHEMA!r}")
    for key in ("metadata", "configure", "synthesis", "flow", "sources", "diagnostics"):
        if not isinstance(data.get(key), dict):
            raise GenerationError(f"generated {key} must be an object")

    placement = data["metadata"].get("placement")
    if not isinstance(placement, str) or not placement.strip():
        raise GenerationError("generated metadata.placement must disclose row placement provenance")

    configure = data["configure"]
    synthesis = data["synthesis"]
    flow = data["flow"]
    sources = data["sources"]
    for label, items in (
        ("gates", configure.get("gates", [])),
        ("lookups", configure.get("lookups", [])),
        ("configure operations", configure.get("operations", [])),
        ("namespaces", synthesis.get("namespaces", [])),
        ("regions", synthesis.get("regions", [])),
        ("operations", synthesis.get("operations", [])),
        ("region groups", synthesis.get("regionGroups", [])),
        ("instance rows", synthesis.get("instanceRows", [])),
        ("flow nodes", flow.get("nodes", [])),
        ("flow edges", flow.get("edges", [])),
        ("source records", sources.get("records", [])),
    ):
        if not isinstance(items, list):
            raise GenerationError(f"generated {label} must be an array")
        duplicates = duplicate_ids(items)
        if duplicates:
            raise GenerationError(f"generated {label} has duplicate IDs: {duplicates[:5]}")

    source_ids = {record["id"] for record in sources["records"]}
    resolutions: list[tuple[str, Mapping[str, Any]]] = [
        ("configure entrypoint", configure["entrypointSource"]),
        *[(gate["id"], gate["source"]) for gate in configure["gates"]],
        *[(region["id"], region["source"]) for region in synthesis["regions"]],
        *[(group["id"], group["source"]) for group in synthesis["regionGroups"]],
    ]
    for entity_id, resolution in resolutions:
        confidence = resolution.get("confidence")
        if confidence not in {"exact", "mapped", "ambiguous", "unresolved"}:
            raise GenerationError(f"{entity_id} has invalid source confidence {confidence!r}")
        primary = resolution.get("primarySourceId")
        if primary is not None and primary not in source_ids:
            raise GenerationError(f"{entity_id} has unknown primary source {primary}")
        for candidate in resolution.get("candidates", []):
            if candidate.get("sourceId") not in source_ids:
                raise GenerationError(
                    f"{entity_id} has unknown source candidate {candidate.get('sourceId')}"
                )
        if confidence == "exact" and primary is None:
            raise GenerationError(f"{entity_id} exact source has no primary")
        if confidence in {"ambiguous", "unresolved"} and primary is not None:
            raise GenerationError(f"{entity_id} {confidence} source must not select a primary")

    flow_node_ids = {node["id"] for node in flow["nodes"]}
    gate_ids = {gate["id"] for gate in configure["gates"]}
    lookup_ids = {lookup["id"] for lookup in configure["lookups"]}
    operation_ids = {operation["id"] for operation in synthesis["operations"]}
    selector_ids = {
        f"selector:{index}" for index in data["metadata"]["symbols"]["selectors"]
    }
    table_ids = {
        entry["id"]
        for operation in synthesis["operations"]
        if operation.get("kind") == "init_lookup_tables"
        for entry in operation.get("entries", [])
    } | {
        f"lookup-column:{index}"
        for index in data["metadata"]["symbols"]["columns"]["lookup"]
    }
    for edge in flow["edges"]:
        if edge.get("from") not in flow_node_ids or edge.get("to") not in flow_node_ids:
            raise GenerationError(f"flow edge {edge.get('id')} has a dangling endpoint")
    for region in synthesis["regions"]:
        if region.get("componentId") is not None and region["componentId"] not in flow_node_ids:
            raise GenerationError(f"region {region['id']} has an unknown component")

    region_ids = {region["id"] for region in synthesis["regions"]}
    namespace_ids = {namespace["id"] for namespace in synthesis["namespaces"]}
    tree_region_ids: set[str] = set()
    tree_namespace_ids: set[str] = set()
    tree_operation_ids: set[str] = set()

    def walk(nodes: Sequence[Mapping[str, Any]]) -> None:
        for node in nodes:
            if node.get("kind") == "namespace":
                tree_namespace_ids.add(node["id"])
                walk(node.get("children", []))
            elif node.get("kind") == "region":
                tree_region_ids.add(node["id"])
                tree_operation_ids.update(node.get("operationIds", []))
            else:
                tree_operation_ids.add(node["id"])

    walk(synthesis.get("tree", []))
    if tree_region_ids != region_ids:
        raise GenerationError("flattened region index does not match the exact tree")
    if tree_namespace_ids != namespace_ids:
        raise GenerationError("flattened namespace index does not match the exact tree")
    if tree_operation_ids != operation_ids:
        raise GenerationError("flattened operation store does not match the exact tree")

    def require_known(entity: str, values: Iterable[str], known: set[str], target: str) -> None:
        unknown = sorted(set(values) - known)
        if unknown:
            raise GenerationError(f"{entity} links unknown {target}: {unknown[:5]}")

    for gate in configure["gates"]:
        require_known(gate["id"], gate.get("selectorIds", []), selector_ids, "selectors")
        require_known(gate["id"], gate.get("regionIds", []), region_ids, "regions")
        require_known(gate["id"], gate.get("componentIds", []), flow_node_ids, "components")
    for lookup in configure["lookups"]:
        require_known(lookup["id"], lookup.get("selectorIds", []), selector_ids, "selectors")
        require_known(lookup["id"], lookup.get("tableIds", []), table_ids, "tables")
        require_known(lookup["id"], lookup.get("regionIds", []), region_ids, "regions")
        require_known(lookup["id"], lookup.get("componentIds", []), flow_node_ids, "components")
    for region in synthesis["regions"]:
        require_known(region["id"], region.get("selectorIds", []), selector_ids, "selectors")
        require_known(region["id"], region.get("gateIds", []), gate_ids, "gates")
        require_known(region["id"], region.get("lookupIds", []), lookup_ids, "lookups")
    for group in synthesis["regionGroups"]:
        require_known(group["id"], group.get("regionIds", []), region_ids, "regions")
        require_known(group["id"], group.get("gateIds", []), gate_ids, "gates")
        require_known(group["id"], group.get("lookupIds", []), lookup_ids, "lookups")
    for node in flow["nodes"]:
        require_known(node["id"], node.get("regionIds", []), region_ids, "regions")
        require_known(node["id"], node.get("gateIds", []), gate_ids, "gates")
        require_known(node["id"], node.get("lookupIds", []), lookup_ids, "lookups")
        require_known(node["id"], node.get("tableIds", []), table_ids, "tables")
        require_known(
            node["id"], node.get("layoutOperationIds", []), operation_ids, "operations"
        )
    if [row.get("row") for row in synthesis["instanceRows"]] != list(range(9)):
        raise GenerationError("instanceRows must explicitly cover rows 0 through 8")
    if data["diagnostics"].get("errors"):
        raise GenerationError("generated diagnostics contains errors")


def validate_optional_rust_roots(
    data: Mapping[str, Any],
    roots: Mapping[str, Path | None],
) -> list[str]:
    diagnostics = []
    for record in data["sources"]["records"]:
        if record.get("language") != "rust" or record.get("verification") != "path-map":
            continue
        root = roots.get(str(record["repository"]))
        if root is None:
            continue
        path = path_inside(root, root / record["path"], label="optional Rust mapping")
        if not path.is_file():
            diagnostics.append(f"mapped Rust path is missing: {record['repository']}:{record['path']}")
            continue
        literal = record.get("literal")
        if literal is not None and literal not in path.read_text(encoding="utf-8"):
            diagnostics.append(
                f"mapped Rust literal is absent: {record['repository']}:{record['path']} {literal!r}"
            )
    return diagnostics


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT, help="raw/high-level input JSON")
    parser.add_argument("--input-label", help="stable repository-relative label stored in metadata")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--garden-root", type=Path, default=DEFAULT_GARDEN_ROOT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true", help="fail if --output is not byte-current")
    parser.add_argument(
        "--validate",
        type=Path,
        metavar="ARTIFACT",
        help="validate an existing generated artifact without regenerating it",
    )
    parser.add_argument(
        "--orchard-root",
        type=Path,
        help="optional read-only validation of curated Orchard Rust mappings",
    )
    parser.add_argument(
        "--halo2-root",
        type=Path,
        help="optional read-only validation of curated Halo2 Rust mappings",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    try:
        if args.validate is not None:
            artifact, _ = read_json(args.validate)
            if not isinstance(artifact, dict):
                raise GenerationError("generated artifact root must be an object")
            validate_generated_data(artifact)
            print(f"validated {args.validate}")
            return 0

        garden_root = args.garden_root.resolve()
        input_data, input_bytes = read_json(args.input)
        manifest, manifest_bytes = read_json(args.manifest)
        if not isinstance(input_data, dict) or not isinstance(manifest, dict):
            raise GenerationError("input and manifest roots must be JSON objects")
        artifact = generate_data(
            input_data,
            input_bytes,
            manifest,
            manifest_bytes,
            garden_root,
            input_label=args.input_label,
        )
        output_bytes = canonical_json_bytes(artifact)
        optional_diagnostics = validate_optional_rust_roots(
            artifact,
            {
                "orchard": args.orchard_root.resolve() if args.orchard_root else None,
                "halo2": args.halo2_root.resolve() if args.halo2_root else None,
            },
        )
        for diagnostic in optional_diagnostics:
            print(f"warning: {diagnostic}", file=sys.stderr)

        if args.check:
            try:
                current = args.output.read_bytes()
            except OSError as error:
                raise GenerationError(f"cannot read checked output {args.output}: {error}") from error
            if current != output_bytes:
                raise GenerationError(
                    f"generated artifact is stale: run {GENERATOR_NAME} --output {args.output}"
                )
            print(f"current {args.output} ({sha256_bytes(output_bytes)})")
            return 0

        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(output_bytes)
        print(
            f"wrote {args.output} ({len(output_bytes)} bytes, sha256 {sha256_bytes(output_bytes)})"
        )
        return 0
    except GenerationError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
