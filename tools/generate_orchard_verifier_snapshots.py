#!/usr/bin/env python3
"""Generate the Rocq differential corpus from the neutral Rust JSON snapshot."""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from typing import Any, Iterable


EXPECTED_PINS = {
    "orchard": "05d899241b7a907d9c47dc5d3d7b3aa1361d785c",
    "halo2": "cca1dd70c5ac76daa7d9773eb9a26e33ceea9a6a",
    "rocq_of_rust": "dbb90c1e3dc76707bba73f8cd10ead38790c808d",
}
EXPECTED_RUST_TARGET = "x86_64-unknown-linux-gnu"
EXPECTED_CASES = 40
EXPECTED_COVERAGE_IDS = 44
PALLAS_P = (1 << 254) + 45560315531419706090280762371685220353
EXPECTED_SHAPE = {
    "circuit": "PostNu6_3",
    "k": 11,
    "instance_width": 10,
    "proof_base_bytes": 2720,
    "proof_bytes_per_action": 2272,
    "advice_queries": 25,
    "fixed_queries": 29,
    "permutation_columns": 15,
    "permutation_sets": 3,
    "lookups": 3,
    "quotient_pieces": 8,
    "multiopen_point_sets": 5,
    "ipa_rounds": 11,
}
REQUIRED_COVERAGE = {
    "verified",
    "one_action",
    "two_actions",
    "restricted_flag",
    "unrestricted_flag",
    "spends_disabled_flag",
    "outputs_disabled_flag",
    "two_action_rejection",
    "trailing_bytes",
    "instance_binding",
    "zero_proofs",
    "canonical_scalar_tamper",
    "transcript_scalar_decode",
    "transcript_point_decode",
    "transcript_identity_rejection",
    "permutation_eval_desync",
    "multiopen_u",
    "ipa_round",
    "ipa_final",
    "constraint_system_failure",
    "opening",
    "truncated_stream",
    "empty",
    "partial_first_point",
    "after_advice_commitments",
    "after_lookup_permuted",
    "after_permutation_products",
    "after_lookup_products",
    "after_random_commitment",
    "after_quotient_pieces",
    "after_instance_evals",
    "after_advice_evals",
    "after_fixed_evals",
    "after_random_eval",
    "after_permutation_common",
    "inside_permutation_sets",
    "after_permutation_sets",
    "after_lookup_evals",
    "after_q_prime",
    "after_multiopen_u",
    "after_s_commitment",
    "inside_ipa_rounds",
    "before_ipa_c",
    "before_ipa_f",
}


def identifier(value: str) -> str:
    result = re.sub(r"[^a-zA-Z0-9_]", "_", value)
    if not result or result[0].isdigit():
        result = "snapshot_" + result
    return result


def hex_bytes(value: str, context: str) -> list[int]:
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise ValueError(f"{context}: invalid hex: {error}") from error
    return list(decoded)


def scalar_from_hex(value: str, context: str) -> int:
    decoded = hex_bytes(value, context)
    if len(decoded) != 32:
        raise ValueError(f"{context}: scalar is {len(decoded)} bytes, expected 32")
    return int.from_bytes(decoded, "little")


def render_nat_list(values: Iterable[int], indent: str = "    ") -> str:
    values = list(values)
    if not values:
        return "[]"
    width = 24
    rows = [values[index : index + width] for index in range(0, len(values), width)]
    rendered = ["; ".join(str(value) for value in row) for row in rows]
    if len(rendered) == 1:
        return "[" + rendered[0] + "]"
    return "[" + (";\n" + indent).join(rendered) + "]"


def render_z_list(values: Iterable[int], indent: str = "    ") -> str:
    return render_nat_list(values, indent)


def validate(snapshot: dict[str, Any]) -> None:
    if snapshot.get("schema_version") != 1:
        raise ValueError("only snapshot schema version 1 is supported")
    source = snapshot.get("source", {})
    for name, expected in EXPECTED_PINS.items():
        actual = source.get(name)
        if actual != expected:
            raise ValueError(f"source pin {name} is {actual!r}, expected {expected}")
    if source.get("rust_target") != EXPECTED_RUST_TARGET:
        raise ValueError(
            f"Rust target is {source.get('rust_target')!r}, "
            f"expected {EXPECTED_RUST_TARGET!r}"
        )
    if source.get("usize_bits") != 64:
        raise ValueError("the Rust corpus must be produced on a 64-bit usize target")
    if snapshot.get("shape") != EXPECTED_SHAPE:
        raise ValueError(
            f"verifier shape is {snapshot.get('shape')!r}, expected {EXPECTED_SHAPE!r}"
        )

    proofs = snapshot.get("proofs")
    inputs = snapshot.get("inputs")
    cases = snapshot.get("cases")
    if not isinstance(proofs, list) or not isinstance(inputs, list) or not isinstance(cases, list):
        raise ValueError("proofs, inputs, and cases must be arrays")
    if len(cases) != EXPECTED_CASES:
        raise ValueError(
            f"snapshot has {len(cases)} cases, expected exactly {EXPECTED_CASES}"
        )

    proof_ids: set[str] = set()
    for proof in proofs:
        proof_id = proof["id"]
        if proof_id in proof_ids:
            raise ValueError(f"duplicate proof id {proof_id}")
        proof_ids.add(proof_id)
        proof_bytes = hex_bytes(proof["proof_hex"], f"proof {proof_id}")
        expected = 2720 + 2272 * proof["num_actions"]
        if len(proof_bytes) != expected:
            raise ValueError(
                f"proof {proof_id} is {len(proof_bytes)} bytes, expected {expected}"
            )

    input_ids: set[str] = set()
    for input_source in inputs:
        input_id = input_source["id"]
        if input_id in input_ids:
            raise ValueError(f"duplicate input id {input_id}")
        input_ids.add(input_id)
        for action_index, instance in enumerate(input_source["instances_le_hex"]):
            if len(instance) != 10:
                raise ValueError(
                    f"input {input_id} action {action_index} has {len(instance)} scalars"
                )
            for scalar_index, scalar in enumerate(instance):
                value = scalar_from_hex(
                    scalar, f"input {input_id}[{action_index}][{scalar_index}]"
                )
                if not 0 <= value < PALLAS_P:
                    raise ValueError(
                        f"input {input_id}[{action_index}][{scalar_index}] "
                        "is not a canonical PallasP scalar"
                    )
                if scalar_index >= 7 and value not in {0, 1}:
                    raise ValueError(
                        f"input {input_id}[{action_index}][{scalar_index}] "
                        "is not a boolean flag"
                    )

    case_ids: set[str] = set()
    covered: dict[str, set[str]] = {}
    for case in cases:
        case_id = case["id"]
        if case_id in case_ids:
            raise ValueError(f"duplicate case id {case_id}")
        case_ids.add(case_id)
        if case["proof"] not in proof_ids:
            raise ValueError(f"case {case_id} names unknown proof {case['proof']}")
        if case["inputs"] not in input_ids:
            raise ValueError(f"case {case_id} names unknown input {case['inputs']}")
        mutation = case["mutation"]
        kind = mutation["kind"]
        if kind in {"append", "replace_chunk"}:
            payload = hex_bytes(mutation["hex"], f"case {case_id} mutation")
            if kind == "replace_chunk" and len(payload) != 32:
                raise ValueError(f"case {case_id}: replacement is not one chunk")
        for branch in case["covers"]:
            covered.setdefault(branch, set()).add(case_id)

    if len(REQUIRED_COVERAGE) != EXPECTED_COVERAGE_IDS:
        raise ValueError(
            "generator coverage inventory has "
            f"{len(REQUIRED_COVERAGE)} IDs, expected exactly {EXPECTED_COVERAGE_IDS}"
        )

    coverage_entries = snapshot.get("branch_coverage")
    if not isinstance(coverage_entries, list):
        raise ValueError("branch_coverage must be an array")
    manifest: dict[str, set[str]] = {}
    for entry in coverage_entries:
        branch_id = entry["id"]
        if branch_id in manifest:
            raise ValueError(f"duplicate branch_coverage id {branch_id}")
        manifest[branch_id] = set(entry["cases"])

    actual_coverage = set(manifest)
    missing = REQUIRED_COVERAGE - actual_coverage
    extra = actual_coverage - REQUIRED_COVERAGE
    if missing or extra:
        details = []
        if missing:
            details.append("missing: " + ", ".join(sorted(missing)))
        if extra:
            details.append("extra: " + ", ".join(sorted(extra)))
        raise ValueError(
            "branch_coverage IDs differ from the exact inventory ("
            + "; ".join(details)
            + ")"
        )
    if manifest != covered:
        raise ValueError("branch_coverage does not match the case cover annotations")


def render_mutation(mutation: dict[str, Any]) -> str:
    kind = mutation["kind"]
    if kind == "identity":
        return "OrchardVerifierSnapshot.Identity"
    if kind == "append":
        return "OrchardVerifierSnapshot.Append " + render_z_list(hex_bytes(mutation["hex"], "append"))
    if kind == "truncate":
        return f"OrchardVerifierSnapshot.Truncate {mutation['len']}%nat"
    if kind == "replace_chunk":
        values = render_z_list(hex_bytes(mutation["hex"], "replacement"), "        ")
        return (
            f"OrchardVerifierSnapshot.ReplaceChunk {mutation['index']}%nat " + values
        )
    if kind == "remove_chunk":
        return f"OrchardVerifierSnapshot.RemoveChunk {mutation['index']}%nat"
    if kind == "increment_scalar":
        return f"OrchardVerifierSnapshot.IncrementScalar {mutation['index']}%nat"
    if kind == "flip_point_sign":
        return f"OrchardVerifierSnapshot.FlipPointSign {mutation['index']}%nat"
    raise ValueError(f"unknown mutation kind {kind}")


def render_outcome(outcome: dict[str, Any]) -> str:
    kind = outcome["kind"]
    if kind == "verified":
        return "OrchardVerifierSnapshot.Verified"
    if kind == "panicked":
        return "OrchardVerifierSnapshot.Panicked"
    if kind != "rejected":
        raise ValueError(f"unknown outcome kind {kind}")
    error = outcome["error"]
    if error == "opening":
        encoded = "OrchardVerifierSnapshot.Opening"
    elif error == "constraint_system_failure":
        encoded = "OrchardVerifierSnapshot.ConstraintSystemFailure"
    elif error == "invalid_instances":
        encoded = "OrchardVerifierSnapshot.InvalidInstances"
    elif error == "instance_too_large":
        encoded = "OrchardVerifierSnapshot.InstanceTooLarge"
    elif error == "transcript":
        detail = outcome.get("detail", "")
        causes = {
            "failed to fill whole buffer": "UnexpectedEof",
            "invalid field element encoding in proof": "InvalidScalarEncoding",
            "invalid point encoding in proof": "InvalidPointEncoding",
            "cannot write points at infinity to the transcript": "PointAtInfinity",
        }
        if detail not in causes:
            raise ValueError(f"unknown transcript cause {detail!r}")
        encoded = (
            "OrchardVerifierSnapshot.Transcript "
            f"OrchardVerifierSnapshot.{causes[detail]}"
        )
    else:
        raise ValueError(f"unsupported Rust verifier error {error}")
    return f"OrchardVerifierSnapshot.Rejected ({encoded})"


def generate(snapshot: dict[str, Any], source_name: str) -> str:
    proof_indices = {proof["id"]: index for index, proof in enumerate(snapshot["proofs"])}
    input_indices = {input_source["id"]: index for index, input_source in enumerate(snapshot["inputs"])}
    lines = [
        "(** Auto-generated from " + source_name + ".  Do not edit. *)",
        "From Stdlib Require Import ZArith Lists.List Strings.String Strings.PrimString Bool.",
        "Require Import Garden.Orchard.Verifier.Snapshots.Schema.",
        "",
        "Import ListNotations.",
        "Import PStringNotations.",
        "Local Open Scope Z_scope.",
        "Local Open Scope string_scope.",
        "",
        "Module OrchardVerifierGeneratedSnapshots.",
        f"  Definition schema_version : nat := {snapshot['schema_version']}%nat.",
        f"  Definition orchard_pin : string := \"{snapshot['source']['orchard']}\".",
        f"  Definition halo2_pin : string := \"{snapshot['source']['halo2']}\".",
        f"  Definition rocq_of_rust_pin : string := \"{snapshot['source']['rocq_of_rust']}\".",
        f"  Definition rust_target : string := \"{snapshot['source']['rust_target']}\".",
        f"  Definition usize_bits : nat := {snapshot['source']['usize_bits']}%nat.",
        "",
    ]

    proof_names: list[str] = []
    for proof in snapshot["proofs"]:
        name = "proof_" + identifier(proof["id"])
        proof_names.append(name)
        encoded = bytes(
            hex_bytes(proof["proof_hex"], f"proof {proof['id']}")
        ).hex()
        lines.extend(
            [
                f"  Definition {name} : OrchardVerifierSnapshot.proof_source := {{|",
                f"    OrchardVerifierSnapshot.proof_num_actions := {proof['num_actions']}%nat;",
                "    OrchardVerifierSnapshot.proof_cross_address_enabled := "
                + ("true" if proof["cross_address_enabled"] else "false")
                + ";",
                "    OrchardVerifierSnapshot.proof_bytes := "
                + "OrchardVerifierSnapshot.bytes_of_hex "
                + f'"{encoded}"%pstring',
                "  |}.",
                "",
            ]
        )
    lines.append(
        "  Definition proofs : list OrchardVerifierSnapshot.proof_source := ["
        + "; ".join(proof_names)
        + "]."
    )
    lines.append("")

    input_names: list[str] = []
    for input_source in snapshot["inputs"]:
        name = "input_" + identifier(input_source["id"])
        input_names.append(name)
        instances = []
        for action_index, instance in enumerate(input_source["instances_le_hex"]):
            values = [
                scalar_from_hex(value, f"{input_source['id']}[{action_index}]")
                for value in instance
            ]
            instances.append(render_z_list(values, "        "))
        rendered_instances = "[]" if not instances else "[" + ";\n      ".join(instances) + "]"
        lines.extend(
            [
                f"  Definition {name} : OrchardVerifierSnapshot.input_source := {{|",
                "    OrchardVerifierSnapshot.input_instances := " + rendered_instances,
                "  |}.",
                "",
            ]
        )
    lines.append(
        "  Definition inputs : list OrchardVerifierSnapshot.input_source := ["
        + "; ".join(input_names)
        + "]."
    )
    lines.append("")

    case_names: list[str] = []
    for case in snapshot["cases"]:
        name = "case_" + identifier(case["id"])
        case_names.append(name)
        lines.extend(
            [
                f"  (** Rust case [{case['id']}]. *)",
                f"  Definition {name} : OrchardVerifierSnapshot.case := {{|",
                "    OrchardVerifierSnapshot.case_proof_index := "
                f"{proof_indices[case['proof']]}%nat;",
                "    OrchardVerifierSnapshot.case_input_index := "
                f"{input_indices[case['inputs']]}%nat;",
                "    OrchardVerifierSnapshot.case_mutation := "
                + render_mutation(case["mutation"])
                + ";",
                "    OrchardVerifierSnapshot.case_expected := "
                + render_outcome(case["rust_outcome"]),
                "  |}.",
                "",
            ]
        )
    lines.append(
        "  Definition cases : list OrchardVerifierSnapshot.case := [\n    "
        + ";\n    ".join(case_names)
        + "\n  ]."
    )
    lines.extend(
        [
            "",
            "  Example all_proof_sources_well_formed :",
            "    List.forallb OrchardVerifierSnapshot.source_well_formedb proofs = true.",
            "  Proof. vm_compute. reflexivity. Qed.",
            "",
            "  Example all_input_sources_well_formed :",
            "    List.forallb OrchardVerifierSnapshot.inputs_well_formedb inputs = true.",
            "  Proof. vm_compute. reflexivity. Qed.",
            "End OrchardVerifierGeneratedSnapshots.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input",
        nargs="?",
        type=pathlib.Path,
        default=pathlib.Path("Garden/Orchard/Verifier/Snapshots/post_nu6_3.json"),
    )
    parser.add_argument(
        "output",
        nargs="?",
        type=pathlib.Path,
        default=pathlib.Path("Garden/Orchard/Verifier/Snapshots/Generated.v"),
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    try:
        snapshot = json.loads(args.input.read_text(encoding="utf-8"))
        validate(snapshot)
        rendered = generate(snapshot, args.input.name)
        if args.check:
            actual = args.output.read_text(encoding="utf-8")
            if actual != rendered:
                raise ValueError(f"{args.output} is stale; regenerate it")
        else:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
