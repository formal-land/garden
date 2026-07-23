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
SCRIPT_PATH = GARDEN_ROOT / "scripts" / "generate_orchard_circuit_grid.py"
SCHEMA_PATH = GARDEN_ROOT / "scripts" / "orchard_circuit_grid.schema.json"
SNAPSHOT_ROOT = GARDEN_ROOT / "Garden" / "Orchard" / "Snapshots"
CONFIGURE_MODEL_PATH = SNAPSHOT_ROOT / "circuit_configure_generated_from_model.json"
CONFIGURE_IMPLEMENTATION_PATH = (
    SNAPSHOT_ROOT / "circuit_configure_generated_from_implementation.json"
)
SYNTHESIS_MODEL_PATH = SNAPSHOT_ROOT / "circuit_synthesis_generated_from_model.json"
SYNTHESIS_IMPLEMENTATION_PATH = (
    SNAPSHOT_ROOT / "circuit_synthesis_generated_from_implementation.json"
)
EXPLORER_PATH = (
    GARDEN_ROOT
    / "web"
    / "orchard-verification"
    / "public"
    / "data"
    / "orchard-circuit-highlevel.v1.json"
)
OUTPUT_PATH = (
    GARDEN_ROOT
    / "web"
    / "orchard-verification"
    / "public"
    / "data"
    / "orchard-circuit-grid.v1.json"
)

SPEC = importlib.util.spec_from_file_location("orchard_circuit_grid_generator", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
GENERATOR = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GENERATOR
SPEC.loader.exec_module(GENERATOR)


class ParityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.configure_model, _ = GENERATOR.read_json(CONFIGURE_MODEL_PATH)
        cls.configure_implementation, _ = GENERATOR.read_json(
            CONFIGURE_IMPLEMENTATION_PATH
        )
        cls.synthesis_model, _ = GENERATOR.read_json(SYNTHESIS_MODEL_PATH)
        cls.synthesis_implementation, _ = GENERATOR.read_json(
            SYNTHESIS_IMPLEMENTATION_PATH
        )

    def test_current_snapshots_have_exact_parsed_parity(self) -> None:
        events, configure = GENERATOR.ensure_parity(
            self.configure_model,
            self.configure_implementation,
            self.synthesis_model,
            self.synthesis_implementation,
        )
        self.assertEqual(len(events), 19617)
        self.assertEqual(len(configure["gates"]), 55)

    def test_configure_mismatch_fails_before_generation(self) -> None:
        changed = copy.deepcopy(self.configure_implementation)
        changed["configure"]["gates"][0]["name"] = "changed"
        with self.assertRaisesRegex(GENERATOR.GenerationError, "configure parity mismatch"):
            GENERATOR.ensure_parity(
                self.configure_model,
                changed,
                self.synthesis_model,
                self.synthesis_implementation,
            )

    def test_synthesis_mismatch_fails_before_generation(self) -> None:
        changed = {"events": list(self.synthesis_implementation["events"])}
        changed["events"][0] = dict(changed["events"][0], name="changed")
        with self.assertRaisesRegex(GENERATOR.GenerationError, "synthesis parity mismatch"):
            GENERATOR.ensure_parity(
                self.configure_model,
                self.configure_implementation,
                self.synthesis_model,
                changed,
            )


class GeneratedArtifactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        loaded = {}
        for identifier, path in (
            ("configure-model", CONFIGURE_MODEL_PATH),
            ("configure-implementation", CONFIGURE_IMPLEMENTATION_PATH),
            ("synthesis-model", SYNTHESIS_MODEL_PATH),
            ("synthesis-implementation", SYNTHESIS_IMPLEMENTATION_PATH),
            ("circuit-explorer", EXPLORER_PATH),
        ):
            loaded[identifier] = GENERATOR.read_json(path)
        cls.artifact = GENERATOR.generate_data(
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
            paths={
                "configure-model": str(CONFIGURE_MODEL_PATH.relative_to(GARDEN_ROOT)),
                "configure-implementation": str(
                    CONFIGURE_IMPLEMENTATION_PATH.relative_to(GARDEN_ROOT)
                ),
                "synthesis-model": str(SYNTHESIS_MODEL_PATH.relative_to(GARDEN_ROOT)),
                "synthesis-implementation": str(
                    SYNTHESIS_IMPLEMENTATION_PATH.relative_to(GARDEN_ROOT)
                ),
                "circuit-explorer": str(EXPLORER_PATH.relative_to(GARDEN_ROOT)),
            },
        )
        cls.artifact_bytes = GENERATOR.canonical_json_bytes(cls.artifact)

    def test_committed_artifact_is_byte_current_and_valid(self) -> None:
        GENERATOR.validate_generated_data(self.artifact)
        self.assertEqual(self.artifact_bytes, OUTPUT_PATH.read_bytes())

    def test_schema_contract_and_grid_counts(self) -> None:
        schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
        self.assertEqual(schema["properties"]["schema"]["const"], GENERATOR.OUTPUT_SCHEMA)
        self.assertEqual(self.artifact["schema"], GENERATOR.OUTPUT_SCHEMA)
        self.assertEqual(
            self.artifact["metadata"]["circuit"],
            {
                "id": "orchard-action",
                "name": "Orchard Action Circuit",
                "version": "FixedPostNu6_2",
                "field": "pallas::Base",
                "k": 11,
                "rowCount": 2048,
                "floorPlanner": "V1",
                "stage": "pre-selector-compression",
            },
        )
        self.assertEqual(len(self.artifact["columns"]), 25)
        self.assertEqual(
            {
                kind: sum(1 for column in self.artifact["columns"] if column["kind"] == kind)
                for kind in ("instance", "advice", "fixed")
            },
            {"instance": 1, "advice": 10, "fixed": 14},
        )
        self.assertEqual(len(self.artifact["selectors"]), 56)
        self.assertEqual(len(self.artifact["regions"]), 394)
        self.assertEqual(len(self.artifact["events"]), 19617)
        self.assertEqual(len(self.artifact["rows"]), 2048)

    def test_capabilities_and_input_hashes_are_explicit(self) -> None:
        metadata = self.artifact["metadata"]
        self.assertEqual(
            metadata["capabilities"],
            {
                "adviceAssignments": "references-only",
                "witnessValues": "omitted",
                "selectors": "virtual",
                "permutation": "copy-edges",
            },
        )
        self.assertEqual(
            metadata["parity"],
            {
                "configure": "exact",
                "synthesis": "exact",
                "comparison": "parsed-json",
            },
        )
        self.assertEqual(
            {item["id"] for item in metadata["inputs"]},
            {
                "configure-model",
                "configure-implementation",
                "synthesis-model",
                "synthesis-implementation",
                "circuit-explorer",
            },
        )
        for item in metadata["inputs"]:
            self.assertRegex(item["sha256"], r"^[0-9a-f]{64}$")

    def test_known_overlapping_selectors_and_deep_links(self) -> None:
        selector = next(
            item for item in self.artifact["selectors"] if item["id"] == "selector:5"
        )
        self.assertEqual(selector["name"], "QWitnessPoint")
        self.assertEqual(selector["gateIds"], ["gate:3"])
        self.assertEqual(
            selector["circuitTarget"]["href"],
            "circuit.html#level=detail&item=gate%3A3",
        )
        row = next(item for item in self.artifact["rows"] if item["row"] == 1758)
        self.assertEqual(
            row["selectorIds"],
            ["selector:2", "selector:4", "selector:5"],
        )
        self.assertEqual(
            row["regionIds"],
            ["region:2", "region:288"],
        )
        event = next(
            item
            for item in self.artifact["events"]
            if item.get("selectorId") == "selector:5" and item.get("row") == 1758
        )
        self.assertEqual(event["id"], "trace-event:3087")
        self.assertEqual(event["regionId"], "region:2")
        self.assertEqual(event["operationIds"], ["region:2/op:0"])
        self.assertEqual(
            GENERATOR.circuit_target(
                event["regionId"],
                kind="operation",
                title=event["operationIds"][0],
                focus_id=event["operationIds"][0],
            )["href"],
            "circuit.html#level=detail&item=region%3A2&focus=region%3A2%2Fop%3A0",
        )

    def test_fill_events_are_ranges_and_copy_events_keep_both_endpoints(self) -> None:
        fills = [event for event in self.artifact["events"] if event["kind"] == "fill"]
        self.assertEqual(len(fills), 3)
        self.assertTrue(
            all(
                event["fromRow"] == 1024 and event["toRow"] == 2047
                for event in fills
            )
        )
        copies = [event for event in self.artifact["events"] if event["kind"] == "copy"]
        self.assertEqual(len(copies), 2964)
        self.assertTrue(all(len(event["endpoints"]) == 2 for event in copies))
        self.assertTrue(
            any(
                {endpoint["columnId"] for endpoint in event["endpoints"]}
                == {"advice:2", "instance:0"}
                for event in copies
            )
        )

    def test_every_region_has_a_canonical_circuit_target(self) -> None:
        for region in self.artifact["regions"]:
            self.assertEqual(region["circuitTarget"]["kind"], "region")
            self.assertEqual(
                region["circuitTarget"]["href"],
                f"circuit.html#level=detail&item=region%3A{region['regionIndex']}",
            )
        witness_point = next(
            region for region in self.artifact["regions"] if region["id"] == "region:2"
        )
        self.assertEqual(witness_point["startRow"], 1758)
        self.assertEqual(witness_point["endRow"], 1758)
        # Copy peers must not inflate a region's span across the circuit.
        self.assertLess(
            max(
                region["endRow"] - region["startRow"]
                for region in self.artifact["regions"]
                if "endRow" in region
            ),
            200,
        )

    def test_check_mode_detects_stale_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "grid.json"
            output.write_bytes(self.artifact_bytes)
            arguments = [
                "--garden-root",
                str(GARDEN_ROOT),
                "--configure-model",
                str(CONFIGURE_MODEL_PATH),
                "--configure-implementation",
                str(CONFIGURE_IMPLEMENTATION_PATH),
                "--synthesis-model",
                str(SYNTHESIS_MODEL_PATH),
                "--synthesis-implementation",
                str(SYNTHESIS_IMPLEMENTATION_PATH),
                "--explorer",
                str(EXPLORER_PATH),
                "--output",
                str(output),
                "--check",
            ]
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                self.assertEqual(GENERATOR.main(arguments), 0)
            output.write_bytes(self.artifact_bytes + b" ")
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                self.assertEqual(GENERATOR.main(arguments), 1)


if __name__ == "__main__":
    unittest.main()
