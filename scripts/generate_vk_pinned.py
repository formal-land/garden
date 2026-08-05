#!/usr/bin/env python3
"""Generate the Rocq literals that pin Orchard's verifying-key description.

The Orchard implementation stores ``vk.pinned()`` as a pretty Rust Debug dump
and, on this branch, also exposes a lossless JSON parse of that dump.  This
script turns those two implementation artifacts into:

* ``Garden/Orchard/vk/bytes.v``: byte-exact primitive-string shards;
* ``Garden/Orchard/vk/data.v``: the fields not derived by Garden's compiler;
* the pinned BLAKE2b checkpoint states and scalar in
  ``Garden/Orchard/vk/transcript_repr.v``.

The JSON tree is also rendered in Rust's compact Debug form.  This is the
string Halo2 hashes in ``VerifyingKey::from_parts``.  The BLAKE2b computation
below is deliberately small and self-contained so that ``--check`` validates
all generated literals without requiring a Rust build or a Rocq reduction.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Iterable


SHARD_SIZE = 65_536
PERSONALIZATION = b"Halo2-Verify-Key"
MASK64 = (1 << 64) - 1
BLAKE2B_IV = (
    0x6A09E667F3BCC908,
    0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B,
    0xA54FF53A5F1D36F1,
    0x510E527FADE682D1,
    0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B,
    0x5BE0CD19137E2179,
)
BLAKE2B_SIGMA = (
    (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15),
    (14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3),
    (11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4),
    (7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8),
    (9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13),
    (2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9),
    (12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11),
    (13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10),
    (6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5),
    (10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0),
    (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15),
    (14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3),
)
CHECKPOINT_BLOCKS = (557, 1114, 1671, 2227)


def parse_args() -> argparse.Namespace:
    repo_root = Path(__file__).resolve().parents[1]
    description = (
        repo_root
        / "third-party/orchard/src/circuit_data/circuit_description_post_nu6_3"
    )
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=description)
    parser.add_argument("--json-input", type=Path, default=description.with_suffix(".json"))
    parser.add_argument(
        "--bytes-output",
        type=Path,
        default=repo_root / "Garden/Orchard/vk/bytes.v",
    )
    parser.add_argument(
        "--data-output",
        type=Path,
        default=repo_root / "Garden/Orchard/vk/data.v",
    )
    parser.add_argument(
        "--transcript-output",
        type=Path,
        default=repo_root / "Garden/Orchard/vk/transcript_repr.v",
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--check",
        action="store_true",
        help="Fail if any generated output is stale.",
    )
    mode.add_argument(
        "--dry-run",
        action="store_true",
        help="Validate inputs and print metadata without writing files.",
    )
    return parser.parse_args()


def display_source(path: Path, repo_root: Path) -> str:
    try:
        relative = path.resolve().relative_to(repo_root)
    except ValueError:
        return path.as_posix()
    if relative.parts and relative.parts[0] == "third-party":
        relative = Path(*relative.parts[1:])
    return relative.as_posix()


def load_description(raw_path: Path, json_path: Path) -> tuple[str, dict[str, Any]]:
    raw = raw_path.read_bytes()
    try:
        pretty = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise ValueError(f"{raw_path} is not ASCII") from error

    payload = json.loads(json_path.read_text(encoding="utf-8"))
    expected_hash = payload.get("source_sha256")
    actual_hash = hashlib.sha256(raw).hexdigest()
    if expected_hash != actual_hash:
        raise ValueError(
            f"{json_path} parses a different dump: "
            f"expected sha256 {expected_hash}, got {actual_hash}"
        )

    representation = payload.get("representation")
    if not isinstance(representation, dict):
        raise ValueError(f"{json_path} has no representation object")
    if representation.get("type") != "PinnedVerificationKey":
        raise ValueError(f"{json_path} is not a PinnedVerificationKey")
    return pretty, representation


def compact_debug(value: Any, *, quoted_string: bool = False) -> str:
    """Render the generic JSON parse as Rust's compact ``Debug`` syntax."""

    if value is None:
        return "None"
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        if quoted_string:
            return json.dumps(value, ensure_ascii=True)
        if re.fullmatch(r"(?:0x[0-9a-f]+|[A-Za-z_][A-Za-z0-9_]*)", value):
            return value
        return json.dumps(value, ensure_ascii=True)
    if isinstance(value, list):
        return "[" + ", ".join(compact_debug(item) for item in value) + "]"
    if not isinstance(value, dict):
        raise TypeError(f"unsupported Debug value: {value!r}")

    if set(value) == {"type", "fields"}:
        fields = value["fields"]
        if not isinstance(fields, dict):
            raise ValueError(f"struct fields must be an object: {value!r}")
        body = ", ".join(
            f"{name}: {compact_debug(field, quoted_string=name in {'base_modulus', 'scalar_modulus'})}"
            for name, field in fields.items()
        )
        return f"{value['type']} {{ {body} }}"
    if set(value) == {"variant", "args"}:
        args = value["args"]
        return f"{value['variant']}(" + ", ".join(compact_debug(arg) for arg in args) + ")"
    if set(value) == {"tuple"}:
        items = value["tuple"]
        suffix = "," if len(items) == 1 else ""
        return "(" + ", ".join(compact_debug(item) for item in items) + suffix + ")"
    raise ValueError(f"unrecognized generic Debug node: {value!r}")


def rotate_right(value: int, shift: int) -> int:
    return ((value >> shift) | (value << (64 - shift))) & MASK64


def blake2b_mix(
    state: list[int],
    a: int,
    b: int,
    c: int,
    d: int,
    x: int,
    y: int,
) -> None:
    state[a] = (state[a] + state[b] + x) & MASK64
    state[d] = rotate_right(state[d] ^ state[a], 32)
    state[c] = (state[c] + state[d]) & MASK64
    state[b] = rotate_right(state[b] ^ state[c], 24)
    state[a] = (state[a] + state[b] + y) & MASK64
    state[d] = rotate_right(state[d] ^ state[a], 16)
    state[c] = (state[c] + state[d]) & MASK64
    state[b] = rotate_right(state[b] ^ state[c], 63)


def blake2b_initial_state() -> list[int]:
    parameter_block = bytearray(64)
    parameter_block[0:4] = bytes((64, 0, 1, 1))
    parameter_block[48:64] = PERSONALIZATION
    words = [
        int.from_bytes(parameter_block[offset : offset + 8], "little")
        for offset in range(0, 64, 8)
    ]
    return [left ^ right for left, right in zip(BLAKE2B_IV, words)]


def blake2b_compress(
    chaining: list[int],
    block: bytes,
    consumed: int,
    final: bool,
) -> list[int]:
    if len(block) != 128:
        raise ValueError("BLAKE2b blocks must have 128 bytes")
    message = [
        int.from_bytes(block[offset : offset + 8], "little")
        for offset in range(0, 128, 8)
    ]
    state = list(chaining) + list(BLAKE2B_IV)
    state[12] ^= consumed & MASK64
    state[13] ^= consumed >> 64
    if final:
        state[14] ^= MASK64

    for schedule in BLAKE2B_SIGMA:
        blake2b_mix(state, 0, 4, 8, 12, message[schedule[0]], message[schedule[1]])
        blake2b_mix(state, 1, 5, 9, 13, message[schedule[2]], message[schedule[3]])
        blake2b_mix(state, 2, 6, 10, 14, message[schedule[4]], message[schedule[5]])
        blake2b_mix(state, 3, 7, 11, 15, message[schedule[6]], message[schedule[7]])
        blake2b_mix(state, 0, 5, 10, 15, message[schedule[8]], message[schedule[9]])
        blake2b_mix(state, 1, 6, 11, 12, message[schedule[10]], message[schedule[11]])
        blake2b_mix(state, 2, 7, 8, 13, message[schedule[12]], message[schedule[13]])
        blake2b_mix(state, 3, 4, 9, 14, message[schedule[14]], message[schedule[15]])

    return [
        chaining[index] ^ state[index] ^ state[index + 8] for index in range(8)
    ]


def transcript_metadata(compact: str, scalar_modulus: int) -> dict[str, Any]:
    compact_bytes = compact.encode("ascii")
    transcript_input = len(compact_bytes).to_bytes(8, "little") + compact_bytes
    blocks = [
        transcript_input[offset : offset + 128].ljust(128, b"\0")
        for offset in range(0, len(transcript_input), 128)
    ]
    chaining = blake2b_initial_state()
    checkpoints: dict[int, list[int]] = {}
    for index, block in enumerate(blocks, start=1):
        final = index == len(blocks)
        consumed = len(transcript_input) if final else index * 128
        chaining = blake2b_compress(chaining, block, consumed, final)
        if not final and index in CHECKPOINT_BLOCKS:
            checkpoints[index] = list(chaining)

    if tuple(checkpoints) != CHECKPOINT_BLOCKS:
        raise ValueError(
            "compact description changed the transcript proof's block partition: "
            f"got {len(blocks)} blocks and checkpoints {tuple(checkpoints)}"
        )

    digest = b"".join(word.to_bytes(8, "little") for word in chaining)
    reference_digest = hashlib.blake2b(
        transcript_input,
        digest_size=64,
        person=PERSONALIZATION,
    ).digest()
    if digest != reference_digest:
        raise AssertionError("self-contained BLAKE2b disagrees with hashlib")

    return {
        "compact_length": len(compact_bytes),
        "input_length": len(transcript_input),
        "block_count": len(blocks),
        "checkpoints": [checkpoints[index] for index in CHECKPOINT_BLOCKS],
        "last_block": list(blocks[-1]),
        "transcript_repr": int.from_bytes(digest, "little") % scalar_modulus,
    }


def point_list(value: Any, name: str) -> list[tuple[str, str]]:
    if not isinstance(value, list):
        raise ValueError(f"{name} must be a list")
    result: list[tuple[str, str]] = []
    for item in value:
        if not isinstance(item, dict) or set(item) != {"tuple"}:
            raise ValueError(f"{name} contains a non-tuple point")
        coordinates = item["tuple"]
        if not isinstance(coordinates, list) or len(coordinates) != 2:
            raise ValueError(f"{name} contains a malformed point")
        x, y = coordinates
        if not all(
            isinstance(coordinate, str)
            and re.fullmatch(r"0x[0-9a-f]+", coordinate)
            for coordinate in (x, y)
        ):
            raise ValueError(f"{name} contains a non-hex coordinate")
        result.append((x, y))
    return result


def render_points(points: Iterable[tuple[str, str]]) -> str:
    point_list_ = list(points)
    lines: list[str] = []
    for index, (x, y) in enumerate(point_list_):
        suffix = ";" if index + 1 < len(point_list_) else ""
        lines.extend((f"  ({x},", f"   {y}){suffix}"))
    return "\n".join(lines)


def render_data_v(
    representation: dict[str, Any],
    source: str,
) -> str:
    fields = representation["fields"]
    domain = fields["domain"]["fields"]
    constraint_system = fields["cs"]["fields"]
    permutation = fields["permutation"]["fields"]
    fixed_commitments = point_list(fields["fixed_commitments"], "fixed commitments")
    permutation_commitments = point_list(
        permutation["commitments"], "permutation commitments"
    )
    if len(fixed_commitments) != 29 or len(permutation_commitments) != 15:
        raise ValueError(
            "unexpected commitment shape: "
            f"{len(fixed_commitments)} fixed, "
            f"{len(permutation_commitments)} permutation"
        )
    minimum_degree = constraint_system["minimum_degree"]
    minimum_degree_rocq = "None" if minimum_degree is None else f"Some {minimum_degree}"

    return f"""(** * Pinned verifying-key literals for the transcript byte channel.

    The components of the pinned verifying-key description
    ([{source}]) that the model does not derive:
    the base/scalar modulus strings, the [extended_k] domain constant,
    [minimum_degree], and the 44 commitment coordinate pairs (29
    fixed-column + 15 permutation commitments, affine Vesta points).
    These remain literal inputs to the byte printer, but
    [vk/provenance/generated/certificates/Main.v] now separately derives
    every coordinate from the model's column evaluations, [Params::new(11)],
    the inverse FFT, and the MSM in an optimized executable Rocq model. They
    are also certified byte-for-byte against the dump by the T1 parity
    certificate ([vk/parity.v]).

    Generated by [scripts/generate_vk_pinned.py]; regenerate with:
      python3 scripts/generate_vk_pinned.py *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.PrimString.

Import ListNotations.
Local Open Scope Z_scope.

Module VkPinnedData.

(** [C::Base::MODULUS] and [C::Scalar::MODULUS] for [C = vesta::Affine],
    as printed (the quotes are added by the string Debug rendering). *)
Definition base_modulus : PrimString.string :=
  "{fields['base_modulus']}"%pstring.

Definition scalar_modulus : PrimString.string :=
  "{fields['scalar_modulus']}"%pstring.

(** The extended evaluation-domain size exponent ([k = {domain['k']}] is pinned in
    [PolyDomain.k]). *)
Definition extended_k : Z := {domain['extended_k']}.

Definition minimum_degree : option Z := {minimum_degree_rocq}.

(** The {len(fixed_commitments)} fixed-column commitments, affine (x, y) coordinates. *)
Definition fixed_commitments : list (Z * Z) := [
{render_points(fixed_commitments)}
].

(** The {len(permutation_commitments)} permutation commitments, affine (x, y) coordinates. *)
Definition permutation_commitments : list (Z * Z) := [
{render_points(permutation_commitments)}
].

End VkPinnedData.
"""


def render_bytes_v(pretty: str, source: str) -> str:
    raw_length = len(pretty.encode("ascii"))
    chunks = [pretty[index : index + SHARD_SIZE] for index in range(0, len(pretty), SHARD_SIZE)]
    shard_names = [f"shard_{index:02d}" for index in range(len(chunks))]
    definitions = []
    for name, chunk in zip(shard_names, chunks):
        escaped = chunk.replace('"', '""')
        definitions.append(
            f'Definition {name} : PrimString.string :=\n  "{escaped}".\n'
        )

    expression = shard_names[-1]
    for name in reversed(shard_names[:-1]):
        expression = f"PrimString.cat {name} ({expression})"

    return f"""(** * The pinned verifying-key Debug dump, as primitive-string shards.

    The byte-for-byte content of
    [{source}] (the pretty
    [format!("{{:#?}}\\n", vk.pinned())] Debug dump of the Post-NU6.3
    verifying key; {raw_length} bytes), imported as {len(chunks)}
    PrimString literals of at most {SHARD_SIZE} bytes.  Untrusted
    witness input: the T1 parity certificate ([vk/parity.v])
    proves the in-model printer reproduces exactly these bytes.

    Generated by [scripts/generate_vk_pinned.py]; regenerate with:
      python3 scripts/generate_vk_pinned.py *)

Require Import Stdlib.Strings.PrimString.

Local Open Scope pstring_scope.

Module VkPinnedBytes.

{chr(10).join(definitions)}
(** The whole dump, all shards concatenated in order. *)
Definition dump : PrimString.string :=
  {expression}.

End VkPinnedBytes.
"""


def format_state(values: list[int]) -> str:
    pairs = [values[index : index + 2] for index in range(0, len(values), 2)]
    lines = [
        "   " + "; ".join(str(value) for value in pair)
        for pair in pairs
    ]
    return "\n".join(
        line + (";" if index + 1 < len(lines) else "")
        for index, line in enumerate(lines)
    )


def format_bytes(values: list[int]) -> str:
    lines = []
    for index in range(0, len(values), 16):
        line = "; ".join(str(value) for value in values[index : index + 16])
        if index + 16 < len(values):
            line += ";"
        lines.append("   " + line)
    return "\n".join(lines)


def inline_list_literal(formatted_items: str) -> str:
    lines = formatted_items.splitlines()
    lines[0] = "  [" + lines[0].strip()
    lines[-1] += "]."
    return "\n".join(lines)


def update_transcript_v(original: str, metadata: dict[str, Any]) -> str:
    if (
        metadata["compact_length"],
        metadata["input_length"],
        metadata["block_count"],
    ) != (285_134, 285_142, 2_228):
        raise ValueError(
            "the compact description length changed; update the transcript "
            "proof's hard-coded lengths and block sharding before regenerating"
        )

    updated = original
    for index, state in enumerate(metadata["checkpoints"], start=1):
        pattern = (
            rf"Definition t2_h{index} : list Z :=\n"
            rf"\s*\[.*?\]\."
        )
        replacement = (
            f"Definition t2_h{index} : list Z :=\n"
            f"{inline_list_literal(format_state(state))}"
        )
        updated, count = re.subn(pattern, replacement, updated, flags=re.DOTALL)
        if count != 1:
            raise ValueError(f"could not uniquely update t2_h{index}")

    last_block_pattern = (
        r"Definition t2_last_block : list Z :=\n"
        r"\s*\[.*?\]\."
    )
    last_block_replacement = (
        "Definition t2_last_block : list Z :=\n"
        f"{inline_list_literal(format_bytes(metadata['last_block']))}"
    )
    updated, count = re.subn(
        last_block_pattern,
        last_block_replacement,
        updated,
        flags=re.DOTALL,
    )
    if count != 1:
        raise ValueError("could not uniquely update t2_last_block")

    scalar_pattern = (
        r"Definition transcript_repr : Z :=\n"
        r"  (?:0x[0-9a-f]+|[0-9]+)\."
    )
    scalar_replacement = (
        "Definition transcript_repr : Z :=\n"
        f"  0x{metadata['transcript_repr']:064x}."
    )
    updated, count = re.subn(scalar_pattern, scalar_replacement, updated)
    if count != 1:
        raise ValueError("could not uniquely update transcript_repr")
    return updated


def check_or_write(path: Path, expected: str, check: bool) -> bool:
    current = path.read_text(encoding="utf-8") if path.exists() else None
    if current == expected:
        return True
    if check:
        print(f"stale generated file: {path}")
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(expected, encoding="utf-8")
    print(path)
    return True


def main() -> None:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    pretty, representation = load_description(args.input, args.json_input)
    source = display_source(args.input, repo_root)
    compact = compact_debug(representation)
    fields = representation["fields"]
    metadata = transcript_metadata(compact, int(fields["scalar_modulus"], 16))

    summary = {
        "source": source,
        "pretty_length": len(pretty.encode("ascii")),
        "compact_length": metadata["compact_length"],
        "input_length": metadata["input_length"],
        "block_count": metadata["block_count"],
        "transcript_repr": f"0x{metadata['transcript_repr']:064x}",
    }
    print(json.dumps(summary, indent=2))
    if args.dry_run:
        return

    bytes_v = render_bytes_v(pretty, source)
    data_v = render_data_v(representation, source)
    transcript_original = args.transcript_output.read_text(encoding="utf-8")
    transcript_v = update_transcript_v(transcript_original, metadata)
    results = (
        check_or_write(args.bytes_output, bytes_v, args.check),
        check_or_write(args.data_output, data_v, args.check),
        check_or_write(args.transcript_output, transcript_v, args.check),
    )
    if not all(results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
