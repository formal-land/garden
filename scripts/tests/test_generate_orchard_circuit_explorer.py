from __future__ import annotations

import copy
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path


GARDEN_ROOT = Path(__file__).resolve().parents[2]
SCRIPT_PATH = GARDEN_ROOT / "scripts" / "generate_orchard_circuit_explorer.py"
MANIFEST_PATH = GARDEN_ROOT / "scripts" / "orchard_circuit_explorer_manifest.v1.json"
RAW_INPUT_PATH = (
    GARDEN_ROOT
    / "Garden"
    / "Orchard"
    / "Snapshots"
    / "circuit_structure_generated_from_model.json"
)
OUTPUT_PATH = (
    GARDEN_ROOT
    / "web"
    / "orchard-verification"
    / "public"
    / "data"
    / "orchard-circuit-highlevel.v1.json"
)

SPEC = importlib.util.spec_from_file_location("orchard_circuit_explorer_generator", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
GENERATOR = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GENERATOR
SPEC.loader.exec_module(GENERATOR)


class RocqSourceScannerTests(unittest.TestCase):
    def test_nested_comments_are_masked_without_changing_offsets(self) -> None:
        source = (
            'Definition visible := "(* this is a string *)".\n'
            "(* outer\n"
            "   (* Gate.name := \"not a gate\". *)\n"
            "   hidden\n"
            "*)\n"
            'Definition gate := {| Gate.name := "visible" |}.\n'
        )
        masked = GENERATOR.mask_rocq_comments(source)
        self.assertEqual(len(masked), len(source))
        self.assertEqual(masked.count("\n"), source.count("\n"))
        self.assertIn('"(* this is a string *)"', masked)
        self.assertNotIn("not a gate", masked)
        self.assertIn('Gate.name := "visible"', masked)

    def test_unbalanced_comments_fail_loudly(self) -> None:
        with self.assertRaises(GENERATOR.GenerationError):
            GENERATOR.mask_rocq_comments("(* missing terminator")
        with self.assertRaises(GENERATOR.GenerationError):
            GENERATOR.mask_rocq_comments("unexpected *)")

    def test_source_ids_do_not_depend_on_advisory_line_numbers(self) -> None:
        repositories = {
            "garden": {
                "id": "garden",
                "revision": "0" * 40,
                "base_url": "https://example.test/garden",
            }
        }
        config = {
            "repository": "garden",
            "includes": ["Garden/Test.v"],
            "exclude_suffixes": [],
            "exclude_path_parts": [],
        }
        body = (
            'Definition demo_gate := {| Gate.name := "Demo gate" |}.\n'
            'Definition layout := 𝓛.AddRegion region "Demo region" (fun _ => x).\n'
            '(* (* Gate.name := "Comment gate" *) *)\n'
        )
        ids = []
        lines = []
        for prefix in ("", "(* inserted documentation *)\n\n"):
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                path = root / "Garden" / "Test.v"
                path.parent.mkdir(parents=True)
                path.write_text(prefix + body, encoding="utf-8")
                index = GENERATOR.SourceIndex(repositories)
                GENERATOR.scan_rocq_sources(root, config, index)
                ids.append((tuple(index.gates["Demo gate"]), tuple(index.regions["Demo region"])))
                lines.append(index.records[index.gates["Demo gate"][0]]["line"])
                self.assertNotIn("Comment gate", index.gates)
        self.assertEqual(ids[0], ids[1])
        self.assertNotEqual(lines[0], lines[1])


class ValidationUnitTests(unittest.TestCase):
    def test_repository_paths_cannot_escape_their_root(self) -> None:
        with self.assertRaises(GENERATOR.GenerationError):
            GENERATOR.ensure_relative_path("../orchard/secret.rs", label="test path")
        with self.assertRaises(GENERATOR.GenerationError):
            GENERATOR.ensure_relative_path("/absolute/path", label="test path")
        GENERATOR.ensure_relative_path("Garden/Orchard/circuit.v", label="test path")

    def test_curated_flow_must_be_a_dag(self) -> None:
        manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
        cyclic = copy.deepcopy(manifest)
        cyclic["flow"]["edges"].append(
            {
                "id": "forced-cycle",
                "from": "action-checks",
                "to": "private-inputs",
                "label": "test cycle",
                "summary": "Creates a test-only cycle.",
                "kind": "constraint",
            }
        )
        with self.assertRaisesRegex(GENERATOR.GenerationError, "directed acyclic graph"):
            GENERATOR.validate_manifest(cyclic)

    def test_instance_underscore_ast_tag_gets_primary_name(self) -> None:
        symbols = GENERATOR.parse_column_symbols(GARDEN_ROOT / "Garden" / "Orchard" / "columns.v")
        annotated = GENERATOR.annotate_symbols(
            {"tag": "Instance_", "column": "0", "rotation": "0"}, symbols
        )
        self.assertEqual(annotated["column"], "0")
        self.assertEqual(annotated["column_name"], "Primary")

    def test_region_row_range_excludes_cells_owned_by_other_regions(self) -> None:
        operations = [
            {
                "kind": "copy",
                "lhs": {"region_index": "12", "absolute_row": "80"},
                "rhs": {"region_index": "3", "absolute_row": "900"},
            },
            {
                "kind": "copy",
                "lhs": {"region_index": "12", "absolute_row": "81"},
                "rhs": {"region_index": None, "absolute_row": "0"},
            },
            {"kind": "enable_selector", "absolute_row": "82"},
        ]
        metrics = GENERATOR.operation_metrics(operations, region_index=12)
        self.assertEqual(metrics["rowRange"], {"min": 80, "max": 82})

    def test_highlevel_adapter_reconstructs_tree_and_exact_operations(self) -> None:
        repositories = {
            "garden": {
                "id": "garden",
                "revision": "0" * 40,
                "base_url": "https://example.test/garden",
            }
        }
        source_index = GENERATOR.SourceIndex(repositories)
        symbols = GENERATOR.parse_column_symbols(GARDEN_ROOT / "Garden" / "Orchard" / "columns.v")
        synthesis = {
            "events": [
                {"index": 0, "event": "push_namespace", "name": "phase"},
                {"index": 1, "event": "enter_region", "name": "demo"},
                {"index": 2, "event": "enable_selector", "selector": 0, "row": 4},
                {"index": 3, "event": "exit_region", "name": "demo"},
                {"index": 4, "event": "pop_namespace", "name": "phase"},
            ]
        }
        flow_nodes = [
            {
                "id": "phase",
                "match": [{"root_names": ["phase"]}],
            }
        ]
        built = GENERATOR.normalize_highlevel_synthesis(
            synthesis, source_index, symbols, flow_nodes
        )
        namespaces, operations = GENERATOR.flatten_synthesis_tree(built.tree)
        self.assertEqual([item["name"] for item in namespaces], ["phase"])
        self.assertEqual([item["id"] for item in built.regions], ["region:0"])
        self.assertEqual(operations[0]["id"], "layout-op:2")
        self.assertEqual(operations[0]["selector_name"], "QOrchard")
        self.assertEqual(operations[0]["regionId"], "region:0")


class GeneratedArtifactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.raw_data, cls.raw_bytes = GENERATOR.read_json(RAW_INPUT_PATH)
        cls.manifest, cls.manifest_bytes = GENERATOR.read_json(MANIFEST_PATH)
        cls.artifact = GENERATOR.generate_data(
            cls.raw_data,
            cls.raw_bytes,
            cls.manifest,
            cls.manifest_bytes,
            GARDEN_ROOT,
        )
        cls.artifact_bytes = GENERATOR.canonical_json_bytes(cls.artifact)

    def test_generated_artifact_is_byte_current_and_valid(self) -> None:
        GENERATOR.validate_generated_data(self.artifact)
        self.assertEqual(self.artifact_bytes, OUTPUT_PATH.read_bytes())

    def test_expected_counts_ids_and_source_confidence(self) -> None:
        configure = self.artifact["configure"]
        synthesis = self.artifact["synthesis"]
        diagnostics = self.artifact["diagnostics"]["summary"]
        self.assertIn("Rocq free monads", self.artifact["metadata"]["placement"])
        self.assertIn(
            "Garden/Orchard/circuit_synthesis_layout.v",
            {item["path"] for item in self.artifact["sources"]["files"]},
        )
        self.assertEqual(len(configure["gates"]), 55)
        self.assertEqual(len(configure["lookups"]), 3)
        self.assertEqual(sum(len(gate["constraints"]) for gate in configure["gates"]), 193)
        self.assertEqual(len(synthesis["namespaces"]), 408)
        self.assertEqual(len(synthesis["regions"]), 395)
        self.assertEqual(
            sum(1 for operation in synthesis["operations"] if operation.get("regionId")),
            14808,
        )
        self.assertEqual([row["row"] for row in synthesis["instanceRows"]], list(range(10)))
        self.assertEqual(diagnostics["exactGateSources"], 55)
        self.assertEqual(diagnostics["unclassifiedRegions"], 0)
        self.assertEqual(
            len({gate["source"]["primarySourceId"] for gate in configure["gates"]}),
            37,
        )
        for gate in configure["gates"]:
            self.assertEqual(gate["source"]["confidence"], "exact")
            self.assertIsNotNone(gate["source"]["primarySourceId"])
        for region in synthesis["regions"]:
            if region["source"]["confidence"] in {"ambiguous", "unresolved"}:
                self.assertIsNone(region["source"]["primarySourceId"])

    def test_selector_gate_region_component_and_lookup_links(self) -> None:
        configure = self.artifact["configure"]
        synthesis = self.artifact["synthesis"]
        flow_nodes = {node["id"]: node for node in self.artifact["flow"]["nodes"]}
        orchard_gate = configure["gates"][0]
        self.assertEqual(orchard_gate["selectorIds"], ["selector:0"])
        self.assertEqual(orchard_gate["regionIds"], ["region:393", "region:394"])
        self.assertEqual(orchard_gate["componentId"], "component:action-checks")
        orchard_region = next(region for region in synthesis["regions"] if region["id"] == "region:393")
        self.assertIn(orchard_gate["id"], orchard_region["gateIds"])
        self.assertEqual(
            orchard_region["metrics"]["rowRange"],
            {"min": 1745, "max": 1745},
        )
        cross_address_region = next(
            region for region in synthesis["regions"] if region["id"] == "region:394"
        )
        self.assertEqual(cross_address_region["componentId"], "component:action-checks")
        self.assertEqual(
            cross_address_region["metrics"]["rowRange"],
            {"min": 1681, "max": 1684},
        )

        for lookup in configure["lookups"]:
            self.assertTrue(lookup["selectorIds"])
            self.assertTrue(lookup["tableIds"])
        table_component = flow_nodes["component:lookup-tables"]
        self.assertEqual(set(table_component["lookupIds"]), {lookup["id"] for lookup in configure["lookups"]})
        self.assertEqual(set(table_component["tableIds"]), {"lookup-column:0", "lookup-column:1", "lookup-column:2"})
        anchor_component = flow_nodes["component:instance-anchor"]
        self.assertEqual(anchor_component["metrics"]["operationCount"], 1)
        self.assertEqual(anchor_component["metrics"]["operationCounts"], {"copy": 1})

    def test_every_curated_matcher_resolves_and_flow_is_acyclic(self) -> None:
        for node in self.artifact["flow"]["nodes"]:
            resolved = (
                len(node["regionIds"])
                + len(node["layoutOperationIds"])
                + len(node["instanceRowIds"])
            )
            self.assertGreater(resolved, 0, node["id"])

        edges = self.artifact["flow"]["edges"]
        adjacency: dict[str, list[str]] = {}
        for edge in edges:
            adjacency.setdefault(edge["from"], []).append(edge["to"])
        active: set[str] = set()
        done: set[str] = set()

        def visit(node_id: str) -> None:
            self.assertNotIn(node_id, active, f"cycle at {node_id}")
            if node_id in done:
                return
            active.add(node_id)
            for target in adjacency.get(node_id, []):
                visit(target)
            active.remove(node_id)
            done.add(node_id)

        for node in self.artifact["flow"]["nodes"]:
            visit(node["id"])

    def test_check_mode_detects_stale_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "artifact.json"
            output.write_bytes(self.artifact_bytes)
            args = [
                "--input",
                str(RAW_INPUT_PATH),
                "--manifest",
                str(MANIFEST_PATH),
                "--garden-root",
                str(GARDEN_ROOT),
                "--output",
                str(output),
                "--check",
            ]
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                self.assertEqual(GENERATOR.main(args), 0)
            output.write_bytes(self.artifact_bytes + b" ")
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                self.assertEqual(GENERATOR.main(args), 1)


if __name__ == "__main__":
    unittest.main()
