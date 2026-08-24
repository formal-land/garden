#!/usr/bin/env python3
"""Generate compact Rocq runtime leaves from Orchard's pinned VK JSON.

The generated values contain only the compiled gate and lookup expression
trees consumed by the verifier.  A separate Rocq module proves these literals
equal to the values derived from Garden's circuit model, so this generator is
not a trusted equivalence boundary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


EXPECTED_FORMAT = "halo2_pinned_debug_json_v1"
EXPECTED_CIRCUIT = "orchard_action"
EXPECTED_VERSION = "PostNu6_3"


def scalar(value: object) -> int:
    if not isinstance(value, str) or not value.startswith("0x"):
        raise ValueError(f"expected a hexadecimal scalar, got {value!r}")
    return int(value, 16)


def expression(value: object, indent: int = 0) -> str:
    if not isinstance(value, dict):
        raise ValueError(f"expression is not an object: {value!r}")

    pad = " " * indent
    child_pad = " " * (indent + 2)
    leaf_kind = value.get("type")
    if leaf_kind in {"Advice", "Fixed", "Instance"}:
        fields = value.get("fields")
        if not isinstance(fields, dict):
            raise ValueError(f"query has no fields: {value!r}")
        query_index = fields.get("query_index")
        rotation = fields.get("rotation")
        if not isinstance(query_index, int):
            raise ValueError(f"query index is not an integer: {value!r}")
        if not isinstance(rotation, dict) or rotation.get("variant") != "Rotation":
            raise ValueError(f"query rotation is malformed: {value!r}")
        rotation_args = rotation.get("args")
        if not (
            isinstance(rotation_args, list)
            and len(rotation_args) == 1
            and isinstance(rotation_args[0], int)
        ):
            raise ValueError(f"query rotation arguments are malformed: {value!r}")
        return f"query P.{leaf_kind} {query_index}%nat ({rotation_args[0]})"

    variant = value.get("variant")
    args = value.get("args")
    if not isinstance(args, list):
        raise ValueError(f"expression arguments are malformed: {value!r}")

    if variant == "Constant" and len(args) == 1:
        return f"P.Constant {scalar(args[0])}"
    if variant == "Selector" and len(args) == 1 and isinstance(args[0], int):
        return f"P.Selector {args[0]}%nat"
    if variant == "Negated" and len(args) == 1:
        return (
            "P.Negated\n"
            f"{child_pad}({expression(args[0], indent + 2)})"
        )
    if variant in {"Sum", "Product"} and len(args) == 2:
        return (
            f"P.{variant}\n"
            f"{child_pad}({expression(args[0], indent + 2)})\n"
            f"{child_pad}({expression(args[1], indent + 2)})"
        )
    if variant == "Scaled" and len(args) == 2:
        return (
            "P.Scaled\n"
            f"{child_pad}({expression(args[0], indent + 2)})\n"
            f"{child_pad}{scalar(args[1])}"
        )
    raise ValueError(f"unsupported expression: {value!r}")


def render_list(items: list[str], indent: int) -> str:
    if not items:
        return "[]"
    pad = " " * indent
    separator = ";\n" + pad + "  "
    return "[ " + separator.join(items) + "\n" + pad + "]"


def render(source: Path) -> str:
    raw = source.read_bytes()
    document = json.loads(raw)
    if document.get("format") != EXPECTED_FORMAT:
        raise ValueError(f"unexpected format: {document.get('format')!r}")
    if document.get("circuit") != EXPECTED_CIRCUIT:
        raise ValueError(f"unexpected circuit: {document.get('circuit')!r}")
    if document.get("circuit_version") != EXPECTED_VERSION:
        raise ValueError(
            f"unexpected circuit version: {document.get('circuit_version')!r}"
        )

    representation = document.get("representation")
    if not isinstance(representation, dict):
        raise ValueError("missing representation")
    fields = representation.get("fields")
    if not isinstance(fields, dict):
        raise ValueError("missing representation fields")
    constraint_system = fields.get("cs")
    if not isinstance(constraint_system, dict):
        raise ValueError("missing constraint system")
    cs_fields = constraint_system.get("fields")
    if not isinstance(cs_fields, dict):
        raise ValueError("missing constraint-system fields")

    gates = cs_fields.get("gates")
    lookups = cs_fields.get("lookups")
    if not isinstance(gates, list) or len(gates) != 193:
        raise ValueError("expected exactly 193 compiled gates")
    if not isinstance(lookups, list) or len(lookups) != 3:
        raise ValueError("expected exactly three compiled lookups")

    gate_values = [f"[ {expression(gate, 4)} ]" for gate in gates]
    lookup_values: list[str] = []
    for lookup in lookups:
        if not isinstance(lookup, dict) or lookup.get("type") != "Argument":
            raise ValueError(f"malformed lookup: {lookup!r}")
        lookup_fields = lookup.get("fields")
        if not isinstance(lookup_fields, dict):
            raise ValueError(f"lookup has no fields: {lookup!r}")
        inputs = lookup_fields.get("input_expressions")
        tables = lookup_fields.get("table_expressions")
        if not isinstance(inputs, list) or not isinstance(tables, list):
            raise ValueError(f"lookup expressions are malformed: {lookup!r}")
        input_values = [expression(item, 8) for item in inputs]
        table_values = [expression(item, 8) for item in tables]
        lookup_values.append(
            "{|\n"
            "      LookupVerifier.input_expressions := "
            f"{render_list(input_values, 6)};\n"
            "      LookupVerifier.table_expressions := "
            f"{render_list(table_values, 6)}\n"
            "    |}"
        )

    digest = hashlib.sha256(raw).hexdigest()
    return f'''(** * Materialized Post-NU6.3 verifier expression data

    Generated by [tools/generate_orchard_verifier_runtime_data.py] from
    Orchard's pinned [circuit_description_post_nu6_3.json].  This module is
    deliberately runtime-only: it does not import Garden's circuit compiler.
    [PostNu6_3Materialization.v] checks these literals against the independently
    derived Garden values.  Source SHA-256: [{digest}]. *)

From Stdlib Require Import ZArith Lists.List.
Require Import Garden.Halo2.Verifier.Plonk.
Require Import Garden.Halo2.Verifier.Lookup.

Import ListNotations.
Local Open Scope Z_scope.

Module OrchardPostNu63Data.
  Module P := PlonkVerifier.

  Definition query (kind : P.column_kind) (index : nat) (rotation : Z) :
      P.expression :=
    P.Query {{|
      P.query_column := {{|
        P.column_type := kind;
        P.column_index := index
      |}};
      P.query_rotation := rotation
    |}}.

  Definition gate_polynomials : list (list P.expression) :=
    {render_list(gate_values, 4)}.

  Definition lookup_descriptions : list LookupVerifier.argument :=
    {render_list(lookup_values, 4)}.
End OrchardPostNu63Data.
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    generated = render(args.source)
    if args.check:
        if not args.output.exists() or args.output.read_text() != generated:
            raise SystemExit(f"generated output is stale: {args.output}")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(generated)


if __name__ == "__main__":
    main()
