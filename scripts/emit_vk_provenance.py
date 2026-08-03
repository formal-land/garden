#!/usr/bin/env python3
"""Emit sharded Rocq witnesses for Orchard VK commitment provenance.

All arithmetic is independently recomputed by ``generate_vk_provenance``.
The emitted literals carry no trust: certificate leaves in
``Garden/Orchard/vk/provenance/generated`` replay the corresponding checks
with primitive Uint63/PArray code inside Rocq.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import tempfile
from pathlib import Path

import generate_vk_provenance as oracle


OUT = oracle.ROOT / "Garden/Orchard/vk/provenance/generated"
CERTS = OUT / "certificates"
MANIFEST_NAME = ".manifest"
STATE_NAME = ".state.json"
WIDTH = 8
HALF_WINDOWS = 16


def set_output_directory(path: Path) -> None:
    global OUT, CERTS
    OUT = path
    CERTS = OUT / "certificates"


def indexed(prefix: str, count: int, suffix: str = ".v") -> list[str]:
    return [f"{prefix}{index:02d}{suffix}" for index in range(count)]


def expected_vfiles() -> list[str]:
    """Return the complete, stable set of generated paths relative to OUT."""
    column_prefixes = [
        *[f"Fixed{index:02d}" for index in range(29)],
        *[f"Permutation{index:02d}" for index in range(15)],
    ]
    data = [
        "DomainData.v",
        *indexed("Fixed", 29, "Data.v"),
        *indexed("Permutation", 15, "Data.v"),
        *indexed("Sigma", 15, "Data.v"),
        "SigmaData.v",
        *indexed("SrsData", 32),
        "SrsExtraData.v",
        "SrsAll.v",
        *indexed("SrsCoordinates", 32, "Data.v"),
        "SrsCoordinatesExtraData.v",
        "SrsCoordinatesAll.v",
    ]
    certificates = [
        "certificates/Domain.v",
        *[
            f"certificates/Domain{name}.v"
            for name in (
                "BitReversal",
                "DeltaPowers",
                "InverseRoots",
                "NInverse",
                "OmegaPowers",
            )
        ],
        "certificates/Sigma.v",
        *[f"certificates/{name}" for name in indexed("Sigma", 15)],
        "certificates/Srs.v",
        *[f"certificates/{name}" for name in indexed("Srs", 32)],
        "certificates/SrsExtra.v",
        "certificates/Commitments.v",
        *[
            f"certificates/{prefix}{suffix}.v"
            for prefix in column_prefixes
            for suffix in ("", "Assembly", "Calibration", "High", "Low")
        ],
        "certificates/Main.v",
    ]
    result = sorted([*data, *certificates])
    if len(result) != 407 or len(set(result)) != len(result):
        raise AssertionError("the generated-source inventory must contain 407 paths")
    return result


def source_inputs() -> list[Path]:
    return [
        Path(__file__).resolve(),
        Path(oracle.__file__).resolve(),
        oracle.ROOT / "Garden/Orchard/Snapshots/circuit_synthesis_generated_from_model.json",
        oracle.ROOT
        / "Garden/Orchard/Snapshots/circuit_selector_compression_generated_from_implementation.json",
        oracle.ROOT / "Garden/Orchard/vk/data.v",
    ]


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def source_digest() -> str:
    digest = hashlib.sha256()
    for path in source_inputs():
        relative = path.relative_to(oracle.ROOT).as_posix().encode()
        digest.update(len(relative).to_bytes(4, "big"))
        digest.update(relative)
        with path.open("rb") as source:
            for chunk in iter(lambda: source.read(1024 * 1024), b""):
                digest.update(chunk)
    return digest.hexdigest()


def manifest_text() -> str:
    return "".join(
        f"Orchard/vk/provenance/generated/{relative}\n"
        for relative in expected_vfiles()
    )


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    try:
        temporary.write_text(content)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def invalidate_state() -> None:
    (OUT / STATE_NAME).unlink(missing_ok=True)


def words(value: int, modulus: int, montgomery: bool) -> tuple[int, ...]:
    if montgomery:
        value = value * pow(2, 315, modulus) % modulus
    else:
        value %= modulus
    mask = (1 << 63) - 1
    return tuple((value >> (63 * i)) & mask for i in range(5))


def words_term(value: int, modulus: int, montgomery: bool, indent: str = "") -> str:
    w = words(value, modulus, montgomery)
    return (
        "{| Prim63Words.w0 := " + str(w[0]) + "%uint63;\n"
        + indent + "   Prim63Words.w1 := " + str(w[1]) + "%uint63;\n"
        + indent + "   Prim63Words.w2 := " + str(w[2]) + "%uint63;\n"
        + indent + "   Prim63Words.w3 := " + str(w[3]) + "%uint63;\n"
        + indent + "   Prim63Words.w4 := " + str(w[4]) + "%uint63 |}"
    )


def affine_term(point: oracle.Point, indent: str = "") -> str:
    if point is None:
        raise AssertionError("generated affine witness unexpectedly is identity")
    x, y = point
    return (
        "{| VkProvenanceDataTypes.x_words :=\n"
        + indent + "     " + words_term(x, oracle.Q, True, indent + "     ") + ";\n"
        + indent + "   VkProvenanceDataTypes.y_words :=\n"
        + indent + "     " + words_term(y, oracle.Q, True, indent + "     ") + " |}"
    )


JacobianPoint = tuple[int, int, int]


def jacobian_term(point: JacobianPoint, indent: str = "") -> str:
    x, y, z = point
    return (
        "{| VkProvenanceDataTypes.jacobian_x_words :=\n"
        + indent + "     " + words_term(x, oracle.Q, True, indent + "     ") + ";\n"
        + indent + "   VkProvenanceDataTypes.jacobian_y_words :=\n"
        + indent + "     " + words_term(y, oracle.Q, True, indent + "     ") + ";\n"
        + indent + "   VkProvenanceDataTypes.jacobian_z_words :=\n"
        + indent + "     " + words_term(z, oracle.Q, True, indent + "     ") + " |}"
    )


JACOBIAN_IDENTITY: JacobianPoint = (0, 1, 0)


def jacobian_of_affine(point: oracle.Point) -> JacobianPoint:
    if point is None:
        return JACOBIAN_IDENTITY
    return point[0], point[1], 1


def jacobian_double(point: JacobianPoint) -> JacobianPoint:
    x, y, z = point
    if z == 0:
        return JACOBIAN_IDENTITY
    q = oracle.Q
    xx = x * x % q
    yy = y * y % q
    yyyy = yy * yy % q
    s = 2 * (((x + yy) ** 2 - xx - yyyy) % q) % q
    s %= q
    m = 3 * xx % q
    x3 = (m * m - 2 * s) % q
    y3 = (m * (s - x3) - 8 * yyyy) % q
    z3 = 2 * y * z % q
    return x3, y3, z3


def jacobian_add(left: JacobianPoint, right: JacobianPoint) -> JacobianPoint:
    x1, y1, z1 = left
    x2, y2, z2 = right
    if z1 == 0:
        return right
    if z2 == 0:
        return left
    q = oracle.Q
    z1z1 = z1 * z1 % q
    z2z2 = z2 * z2 % q
    u1 = x1 * z2z2 % q
    u2 = x2 * z1z1 % q
    s1 = y1 * (z2 * z2z2 % q) % q
    s2 = y2 * (z1 * z1z1 % q) % q
    if u1 == u2:
        return jacobian_double(left) if s1 == s2 else JACOBIAN_IDENTITY
    h = (u2 - u1) % q
    i = (2 * h) ** 2 % q
    j = h * i % q
    r = 2 * (s2 - s1) % q
    v = u1 * i % q
    x3 = (r * r - j - 2 * v) % q
    y3 = (r * (v - x3) - 2 * s1 * j) % q
    z3 = (((z1 + z2) ** 2 - z1z1 - z2z2) * h) % q
    return x3, y3, z3


def jacobian_double_n(count: int, point: JacobianPoint) -> JacobianPoint:
    for _ in range(count):
        point = jacobian_double(point)
    return point


def jacobian_to_affine(point: JacobianPoint) -> oracle.Point:
    x, y, z = point
    if z == 0:
        return None
    z_inv = pow(z, -1, oracle.Q)
    z2_inv = z_inv * z_inv % oracle.Q
    return x * z2_inv % oracle.Q, y * z2_inv % oracle.Q * z_inv % oracle.Q


def jacobian_pippenger_range(
    scalars: list[int], points: list[oracle.Point], start: int, count: int
) -> JacobianPoint:
    mask = (1 << WIDTH) - 1
    window_sums: list[JacobianPoint] = []
    for window in range(start, start + count):
        buckets = [JACOBIAN_IDENTITY] * mask
        shift = window * WIDTH
        for scalar, point in zip(scalars, points):
            digit = (scalar >> shift) & mask
            if digit:
                buckets[digit - 1] = jacobian_add(
                    buckets[digit - 1], jacobian_of_affine(point)
                )
        running = JACOBIAN_IDENTITY
        total = JACOBIAN_IDENTITY
        for bucket in reversed(buckets):
            running = jacobian_add(running, bucket)
            total = jacobian_add(total, running)
        window_sums.append(total)
    acc = JACOBIAN_IDENTITY
    for value in reversed(window_sums):
        acc = jacobian_add(jacobian_double_n(WIDTH, acc), value)
    return acc


def write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    content = content.rstrip() + "\n"
    if not path.exists() or path.read_text() != content:
        atomic_write(path, content)


def pippenger_range(
    scalars: list[int], points: list[oracle.Point], start: int, count: int
) -> oracle.Point:
    mask = (1 << WIDTH) - 1
    sums: list[oracle.Point] = []
    for window in range(start, start + count):
        buckets: list[oracle.Point] = [None] * mask
        shift = window * WIDTH
        for scalar, point in zip(scalars, points):
            digit = (scalar >> shift) & mask
            if digit:
                buckets[digit - 1] = oracle.curve_add(buckets[digit - 1], point)
        running: oracle.Point = None
        total: oracle.Point = None
        for bucket in reversed(buckets):
            running = oracle.curve_add(running, bucket)
            total = oracle.curve_add(total, running)
        sums.append(total)
    acc: oracle.Point = None
    for value in reversed(sums):
        for _ in range(WIDTH):
            acc = oracle.curve_add(acc, acc)
        acc = oracle.curve_add(acc, value)
    return acc


def bit_reverse_11(value: int) -> int:
    result = 0
    for _ in range(11):
        result = (result << 1) | (value & 1)
        value >>= 1
    return result


def emit_domain_data() -> None:
    omega_inv = pow(oracle.OMEGA, -1, oracle.P)
    inverse_roots = [pow(omega_inv, i, oracle.P) for i in range(1024)]
    omega_powers = [pow(oracle.OMEGA, i, oracle.P) for i in range(oracle.N)]
    delta_powers = [pow(oracle.DELTA, i, oracle.P) for i in range(15)]

    def field_list(name: str, values: list[int]) -> str:
        body = ";\n  ".join(words_term(v, oracle.P, True, "  ") for v in values)
        return f"Definition {name} : list PallasP.t := [\n  {body}\n].\n"

    bit_reversed = "; ".join(f"{bit_reverse_11(i)}%uint63" for i in range(oracle.N))
    source = """(** Generated domain tables; checked by the provenance leaves. *)
From Corelib Require Import PrimArray PrimInt63.
From Stdlib Require Import Lists.List Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.Words.
Require Import Garden.Prim63.Pasta.
Require Import Garden.Orchard.vk.provenance.Jacobian.

Import ListNotations.
Local Open Scope uint63_scope.

Module VkDomainData.
"""
    source += f"Definition bit_reversed : list PrimInt63.int := [{bit_reversed}].\n\n"
    source += field_list("inverse_roots", inverse_roots) + "\n"
    source += field_list("omega_powers", omega_powers) + "\n"
    source += field_list("delta_powers", delta_powers) + "\n"
    source += "Definition n_inverse : PallasP.t :=\n  "
    source += words_term(pow(oracle.N, -1, oracle.P), oracle.P, True, "  ") + ".\n\n"
    source += """Definition bit_reversed_array : PrimArray.array PrimInt63.int :=
  VkJacobian.array_of_list 0 bit_reversed.
Definition inverse_roots_array : PrimArray.array PallasP.t :=
  VkJacobian.array_of_list PallasP.zero inverse_roots.
Definition omega_powers_array : PrimArray.array PallasP.t :=
  VkJacobian.array_of_list PallasP.zero omega_powers.
Definition delta_powers_array : PrimArray.array PallasP.t :=
  VkJacobian.array_of_list PallasP.zero delta_powers.
End VkDomainData.
"""
    write(OUT / "DomainData.v", source)


def srs_entry_term(
    message: bytes,
    point: oracle.Point,
    witnesses: tuple[tuple[bool, int], tuple[bool, int]],
) -> str:
    (square0, root0), (square1, root1) = witnesses
    message_term = "; ".join(str(value) for value in message)
    return (
        "{| VkProvenanceDataTypes.message := [" + message_term + "];\n"
        "   VkProvenanceDataTypes.coordinates :=\n"
        "     " + affine_term(point, "     ") + ";\n"
        "   VkProvenanceDataTypes.was_square0 := " + str(square0).lower() + ";\n"
        "   VkProvenanceDataTypes.root0 := " + str(root0) + ";\n"
        "   VkProvenanceDataTypes.was_square1 := " + str(square1).lower() + ";\n"
        "   VkProvenanceDataTypes.root1 := " + str(root1) + " |}"
    )


def emit_srs(
    bases: list[oracle.Point],
    w: oracle.Point,
    u: oracle.Point,
    witness_rows: list[object],
) -> None:
    imports = """(** Generated Params::new(11) hash-to-Vesta witnesses. *)
From Stdlib Require Import ZArith Lists.List Bool.Bool Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.Words.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope Z_scope.
"""
    module_names = []
    for shard in range(32):
        module = f"VkSrsData{shard:02d}"
        module_names.append(module)
        entries = []
        for index in range(shard * 64, (shard + 1) * 64):
            point, witnesses = witness_rows[index]  # type: ignore[misc]
            assert point == bases[index]
            entries.append(
                srs_entry_term(b"\x00" + index.to_bytes(4, "little"), point, witnesses)
            )
        body = ";\n  ".join(entries)
        write(
            OUT / f"SrsData{shard:02d}.v",
            imports + f"\nModule {module}.\nDefinition entries : list VkProvenanceDataTypes.srs_entry := [\n  {body}\n].\nEnd {module}.\n",
        )
        coordinate_module = f"VkSrsCoordinates{shard:02d}Data"
        coordinate_body = ";\n  ".join(
            affine_term(bases[index], "  ")
            for index in range(shard * 64, (shard + 1) * 64)
        )
        write(
            OUT / f"SrsCoordinates{shard:02d}Data.v",
            "(** Generated coordinate-only Params::new(11) shard. *)\n"
            "From Stdlib Require Import Lists.List Numbers.Cyclic.Int63.Uint63.\n"
            "Require Import Garden.Prim63.Words.\n"
            "Require Import Garden.Orchard.vk.provenance.DataTypes.\n"
            "Import ListNotations.\nLocal Open Scope uint63_scope.\n"
            f"Module {coordinate_module}.\n"
            "Definition coordinates : list "
            "VkProvenanceDataTypes.affine_words := [\n  "
            + coordinate_body
            + f"\n].\nEnd {coordinate_module}.\n",
        )

    w_point, w_witnesses = witness_rows[oracle.N]  # type: ignore[misc]
    u_point, u_witnesses = witness_rows[oracle.N + 1]  # type: ignore[misc]
    assert w_point == w and u_point == u
    write(
        OUT / "SrsExtraData.v",
        imports
        + "\nModule VkSrsExtraData.\nDefinition w_entry : VkProvenanceDataTypes.srs_entry :=\n  "
        + srs_entry_term(b"\x01", w, w_witnesses)
        + ".\nDefinition u_entry : VkProvenanceDataTypes.srs_entry :=\n  "
        + srs_entry_term(b"\x02", u, u_witnesses)
        + ".\nEnd VkSrsExtraData.\n",
    )
    write(
        OUT / "SrsCoordinatesExtraData.v",
        "(** Generated coordinate-only blinding bases. *)\n"
        "From Stdlib Require Import Numbers.Cyclic.Int63.Uint63.\n"
        "Require Import Garden.Prim63.Words.\n"
        "Require Import Garden.Orchard.vk.provenance.DataTypes.\n"
        "Local Open Scope uint63_scope.\n"
        "Module VkSrsCoordinatesExtraData.\n"
        "Definition w : VkProvenanceDataTypes.affine_words :=\n  "
        + affine_term(w, "  ")
        + ".\nDefinition u : VkProvenanceDataTypes.affine_words :=\n  "
        + affine_term(u, "  ")
        + ".\nEnd VkSrsCoordinatesExtraData.\n",
    )

    require_lines = "\n".join(
        f"Require Import Garden.Orchard.vk.provenance.generated.SrsData{i:02d}."
        for i in range(32)
    )
    joined = "\n    ++ ".join(f"VkSrsData{i:02d}.entries" for i in range(32))
    write(
        OUT / "SrsAll.v",
        "(** Generated ordered aggregation of the 32 SRS shards. *)\n"
        "From Stdlib Require Import Lists.List.\n"
        + require_lines
        + "\nRequire Import Garden.Orchard.vk.provenance.generated.SrsExtraData.\n"
        "Import ListNotations.\nModule VkSrsAll.\nDefinition g_entries :=\n    "
        + joined
        + ".\nDefinition w_entry := VkSrsExtraData.w_entry.\nDefinition u_entry := VkSrsExtraData.u_entry.\nEnd VkSrsAll.\n",
    )

    coordinate_require_lines = "\n".join(
        f"Require Import Garden.Orchard.vk.provenance.generated.SrsCoordinates{i:02d}Data."
        for i in range(32)
    )
    coordinate_joined = "\n    ++ ".join(
        f"VkSrsCoordinates{i:02d}Data.coordinates" for i in range(32)
    )
    write(
        OUT / "SrsCoordinatesAll.v",
        "(** Coordinate-only aggregate loaded by every MSM leaf. *)\n"
        "From Stdlib Require Import Lists.List.\n"
        + coordinate_require_lines
        + "\nRequire Import Garden.Orchard.vk.provenance.generated.SrsCoordinatesExtraData.\n"
        "Import ListNotations.\n"
        "Module VkSrsCoordinatesAll.\n"
        "Definition g :=\n    "
        + coordinate_joined
        + ".\nDefinition w := VkSrsCoordinatesExtraData.w.\n"
        "Definition u := VkSrsCoordinatesExtraData.u.\n"
        "End VkSrsCoordinatesAll.\n",
    )


def emit_sigma(mapping: list[list[tuple[int, int]]]) -> None:
    if len(mapping) != 15 or any(len(column) != oracle.N for column in mapping):
        raise AssertionError("expected a 15 x 2048 sigma mapping")
    for index, column in enumerate(mapping):
        # Packing is injective over the 15 x 2048 cell domain and avoids the
        # enormous elaboration cost of 30,720 pairs of Peano naturals.
        packed = [target_column * oracle.N + target_row
                  for target_column, target_row in column]
        body = ";\n  ".join(f"{value}%uint63" for value in packed)
        write(
            OUT / f"Sigma{index:02d}Data.v",
            "(** Generated untrusted packed sigma column witness. *)\n"
            "From Corelib Require Import PrimArray PrimInt63.\n"
            "From Stdlib Require Import Lists.List Numbers.Cyclic.Int63.Uint63.\n"
            "Require Import Garden.Orchard.vk.provenance.Jacobian.\n"
            "Import ListNotations.\n"
            f"Module VkSigma{index:02d}Data.\n"
            "Definition mapping : list PrimInt63.int := [\n  "
            + body
            + "\n].\n"
            "Definition mapping_array : PrimArray.array PrimInt63.int :=\n"
            "  VkJacobian.array_of_list 0%uint63 mapping.\n"
            f"End VkSigma{index:02d}Data.\n",
        )

    imports = "\n".join(
        f"Require Import Garden.Orchard.vk.provenance.generated.Sigma{i:02d}Data."
        for i in range(15)
    )
    arrays = ";\n  ".join(
        f"VkSigma{i:02d}Data.mapping_array" for i in range(15)
    )
    write(
        OUT / "SigmaData.v",
        "(** Generated aggregation of the 15 packed sigma columns. *)\n"
        "From Corelib Require Import PrimArray PrimInt63.\n"
        "From Stdlib Require Import Lists.List Numbers.Cyclic.Int63.Uint63.\n"
        "Require Import Garden.Orchard.vk.provenance.Jacobian.\n"
        + imports
        + "\nImport ListNotations.\n"
        "Module VkSigmaData.\n"
        "Definition mapping_columns : list (PrimArray.array PrimInt63.int) := [\n  "
        + arrays
        + "\n].\n"
        "Definition default_column : PrimArray.array PrimInt63.int :=\n"
        "  PrimArray.make 2048%uint63 0%uint63.\n"
        "Definition mapping_array : PrimArray.array (PrimArray.array PrimInt63.int) :=\n"
        "  VkJacobian.array_of_list default_column mapping_columns.\n"
        "End VkSigmaData.\n",
    )


def emit_column_data(
    kind: str,
    index: int,
    coefficients: list[int],
    low_projective: JacobianPoint,
    high_projective: JacobianPoint,
) -> None:
    cap = kind.capitalize()
    module = f"Vk{cap}{index:02d}Data"
    coeff_body = ";\n  ".join(
        words_term(value, oracle.P, False, "  ") for value in coefficients
    )
    source = f"""(** Generated untrusted {kind} column {index} witnesses. *)
From Stdlib Require Import Lists.List Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Prim63.Words.
Require Import Garden.Orchard.vk.provenance.DataTypes.
Import ListNotations.
Local Open Scope uint63_scope.
Module {module}.
Definition coefficients : list Prim63Words.words5 := [
  {coeff_body}
].
Definition low_projective_expected : VkProvenanceDataTypes.point_words :=
  {jacobian_term(low_projective, '  ')}.
Definition high_projective_expected : VkProvenanceDataTypes.point_words :=
  {jacobian_term(high_projective, '  ')}.
End {module}.
"""
    write(OUT / f"{cap}{index:02d}Data.v", source)


def emit_data() -> None:
    events = oracle.load_events()
    fixed = oracle.fixed_evaluations(events)
    mapping = oracle.sigma_mapping(events)
    permutation = oracle.permutation_evaluations(events)
    evaluations = fixed + permutation
    bases, w, u, witness_rows = oracle.params_points()
    pinned = oracle.pinned_commitments()

    emit_domain_data()
    emit_srs(bases, w, u, witness_rows)
    emit_sigma(mapping)

    for absolute, (column, wanted) in enumerate(zip(evaluations, pinned)):
        coefficients = oracle.ifft(column)
        low_projective = jacobian_pippenger_range(
            coefficients, bases, 0, HALF_WINDOWS
        )
        high_projective = jacobian_pippenger_range(
            coefficients, bases, HALF_WINDOWS, HALF_WINDOWS
        )
        low = jacobian_to_affine(low_projective)
        high = jacobian_to_affine(high_projective)
        assembled_projective = jacobian_add(
            jacobian_add(low_projective, jacobian_double_n(128, high_projective)),
            jacobian_of_affine(w),
        )
        assembled = jacobian_to_affine(assembled_projective)
        if assembled != wanted:
            raise AssertionError(f"split MSM mismatch for column {absolute}")
        kind = "fixed" if absolute < 29 else "permutation"
        index = absolute if absolute < 29 else absolute - 29
        emit_column_data(
            kind, index, coefficients,
            low_projective, high_projective,
        )
        print(f"[{absolute + 1:02d}/44] emitted {kind} {index}")


def emit_sigma_data() -> None:
    emit_sigma(oracle.sigma_mapping(oracle.load_events()))


def emit_domain_certificates() -> None:
    checks = [
        ("BitReversal", "bit_reversal_check"),
        ("InverseRoots", "inverse_roots_check"),
        ("OmegaPowers", "omega_powers_check"),
        ("DeltaPowers", "delta_powers_check"),
        ("NInverse", "n_inverse_check"),
    ]
    for cap, check in checks:
        write(
            CERTS / f"Domain{cap}.v",
            "(** Generated kernel certificate for one evaluation-domain table. *)\n"
            "Require Import Garden.Orchard.vk.provenance.Domain.\n\n"
            f"Module VkDomain{cap}Certificate.\n"
            f"Lemma checked : VkDomain.{check} = true.\n"
            "Proof. vm_compute. reflexivity. Qed.\n"
            f"End VkDomain{cap}Certificate.\n",
        )

    imports = "\n".join(
        f"Require Import Garden.Orchard.vk.provenance.generated.certificates.Domain{cap}."
        for cap, _ in checks
    )
    fields = "\n".join(
        f"    VkDomain.{check.replace('_check', '_checked')} := "
        f"VkDomain{cap}Certificate.checked;"
        for cap, check in checks
    )
    write(
        CERTS / "Domain.v",
        "(** Generated aggregation of the five domain-table certificates. *)\n"
        "Require Import Garden.Orchard.vk.provenance.Domain.\n"
        + imports
        + "\n\nModule VkDomainCertificate.\n"
        "Definition checked : VkDomain.certificate :=\n"
        "  {|\n"
        + fields.rstrip(";")
        + "\n  |}.\nEnd VkDomainCertificate.\n",
    )


def emit_sigma_certificate() -> None:
    imports: list[str] = []
    record_fields: list[str] = []
    values: list[str] = []
    for index in range(15):
        filename = f"Sigma{index:02d}"
        module = f"VkSigma{index:02d}Certificate"
        write(
            CERTS / f"{filename}.v",
            f"(** Generated kernel certificate for sigma column {index}. *)\n"
            "Require Import Garden.Orchard.vk.provenance.Sigma.\n\n"
            f"Module {module}.\n"
            f"Lemma checked : VkSigma.column_check {index} = true.\n"
            "Proof. vm_compute. reflexivity. Qed.\n"
            f"End {module}.\n",
        )
        imports.append(
            f"Require Import Garden.Orchard.vk.provenance.generated.certificates.{filename}."
        )
        record_fields.append(
            f"    sigma_{index:02d} : VkSigma.column_check {index} = true;"
        )
        values.append(f"    sigma_{index:02d} := {module}.checked;")
    write(
        CERTS / "Sigma.v",
        "(** Generated aggregation tying all sigma columns to the model. *)\n"
        "Require Import Garden.Orchard.vk.provenance.Sigma.\n"
        + "\n".join(imports)
        + "\n\nModule VkSigmaCertificate.\n"
        "Record certificate : Prop := {\n"
        + "\n".join(record_fields).rstrip(";")
        + "\n}.\n\nDefinition checked : certificate :=\n  {|\n"
        + "\n".join(values).rstrip(";")
        + "\n  |}.\nEnd VkSigmaCertificate.\n",
    )


def emit_srs_certificates() -> None:
    imports: list[str] = []
    data_imports: list[str] = []
    fields: list[str] = []
    record_fields: list[str] = []
    for shard in range(32):
        data = f"VkSrsData{shard:02d}"
        module = f"VkSrs{shard:02d}Certificate"
        filename = f"Srs{shard:02d}"
        write(
            CERTS / f"{filename}.v",
            "(** Generated kernel certificate for 64 Params::new(11) bases. *)\n"
            "Require Import Garden.Orchard.vk.provenance.Srs.\n"
            f"Require Import Garden.Orchard.vk.provenance.generated.SrsData{shard:02d}.\n\n"
            f"Require Import Garden.Orchard.vk.provenance.generated.SrsCoordinates{shard:02d}Data.\n\n"
            f"Module {module}.\n"
            f"Lemma checked : VkSrs.check_g_shard {shard * 64} "
            f"{data}.entries VkSrsCoordinates{shard:02d}Data.coordinates = true.\n"
            "Proof. vm_compute. reflexivity. Qed.\n"
            f"End {module}.\n",
        )
        imports.append(
            f"Require Import Garden.Orchard.vk.provenance.generated.certificates.{filename}."
        )
        data_imports.append(
            f"Require Import Garden.Orchard.vk.provenance.generated.SrsData{shard:02d}.\n"
            f"Require Import Garden.Orchard.vk.provenance.generated.SrsCoordinates{shard:02d}Data."
        )
        record_fields.append(
            f"    srs_{shard:02d} : VkSrs.check_g_shard {shard * 64} "
            f"{data}.entries VkSrsCoordinates{shard:02d}Data.coordinates = true;"
        )
        fields.append(f"    srs_{shard:02d} := {module}.checked;")

    write(
        CERTS / "SrsExtra.v",
        "(** Generated kernel certificate for the blinding bases w and u. *)\n"
        "Require Import Garden.Orchard.vk.provenance.Srs.\n"
        "Require Import Garden.Orchard.vk.provenance.generated.SrsExtraData.\n\n"
        "Require Import Garden.Orchard.vk.provenance.generated.SrsCoordinatesExtraData.\n\n"
        "Module VkSrsExtraCertificate.\n"
        "Lemma checked :\n"
        "  VkSrs.check_extra_entries VkSrsExtraData.w_entry\n"
        "    VkSrsExtraData.u_entry VkSrsCoordinatesExtraData.w\n"
        "    VkSrsCoordinatesExtraData.u = true.\n"
        "Proof. vm_compute. reflexivity. Qed.\n"
        "End VkSrsExtraCertificate.\n",
    )
    imports.append(
        "Require Import Garden.Orchard.vk.provenance.generated.certificates.SrsExtra."
    )
    data_imports.append(
        "Require Import Garden.Orchard.vk.provenance.generated.SrsExtraData.\n"
        "Require Import Garden.Orchard.vk.provenance.generated.SrsCoordinatesExtraData."
    )
    record_fields.append(
        "    srs_extra : VkSrs.check_extra_entries "
        "VkSrsExtraData.w_entry VkSrsExtraData.u_entry "
        "VkSrsCoordinatesExtraData.w VkSrsCoordinatesExtraData.u = true;"
    )
    fields.append("    srs_extra := VkSrsExtraCertificate.checked;")

    write(
        CERTS / "Srs.v",
        "(** Generated aggregation of the sharded Params::new(11) checks. *)\n"
        "Require Import Garden.Orchard.vk.provenance.Srs.\n"
        + "\n".join(data_imports)
        + "\n"
        + "\n".join(imports)
        + "\n\nModule VkSrsCertificate.\n"
        "Record certificate : Prop := {\n"
        + "\n".join(record_fields).rstrip(";")
        + "\n}.\n\nDefinition checked : certificate :=\n  {|\n"
        + "\n".join(fields).rstrip(";")
        + "\n  |}.\nEnd VkSrsCertificate.\n",
    )


def commitment_metadata(kind: str, index: int) -> tuple[str, str, str, str]:
    cap = kind.capitalize()
    data = f"Vk{cap}{index:02d}Data"
    column_kind = f"VkColumnKinds.{cap}"
    prefix = f"{cap}{index:02d}"
    return cap, data, column_kind, prefix


def emit_commitment_certificates() -> None:
    aggregates: list[tuple[str, str, str, int]] = []
    for kind, count in (("fixed", 29), ("permutation", 15)):
        for index in range(count):
            cap, data, column_kind, prefix = commitment_metadata(kind, index)
            data_import = (
                f"Garden.Orchard.vk.provenance.generated.{cap}{index:02d}Data"
            )

            calibration_module = f"Vk{prefix}CalibrationCertificate"
            write(
                CERTS / f"{prefix}Calibration.v",
                f"(** Generated inverse-FFT certificate for {kind} column {index}. *)\n"
                "Require Import Garden.Orchard.vk.provenance.Calibration.\n"
                "Require Import Garden.Orchard.vk.provenance.Kinds.\n"
                f"Require Import {data_import}.\n\n"
                f"Module {calibration_module}.\n"
                f"Lemma checked : VkCalibration.check {column_kind} {index} "
                f"{data}.coefficients = true.\n"
                "Proof. vm_compute. reflexivity. Qed.\n"
                f"End {calibration_module}.\n",
            )

            for half in ("Low", "High"):
                module = f"Vk{prefix}{half}Certificate"
                check = half.lower() + "_exact"
                expected = half.lower() + "_projective_expected"
                write(
                    CERTS / f"{prefix}{half}.v",
                    f"(** Generated {half.lower()}-half Pippenger certificate for "
                    f"{kind} column {index}. *)\n"
                    "Require Import Garden.Orchard.vk.provenance.MsmChecks.\n"
                    f"Require Import {data_import}.\n\n"
                    f"Module {module}.\n"
                    f"Lemma checked : VkMsmChecks.{check} {data}.coefficients "
                    f"{data}.{expected}.\n"
                    "Proof. vm_compute. reflexivity. Qed.\n"
                    f"End {module}.\n",
                )

            assembly_module = f"Vk{prefix}AssemblyCertificate"
            write(
                CERTS / f"{prefix}Assembly.v",
                f"(** Generated final commitment assembly certificate for "
                f"{kind} column {index}. *)\n"
                "Require Import Garden.Orchard.vk.provenance.AssemblyCheck.\n"
                "Require Import Garden.Orchard.vk.provenance.Kinds.\n"
                f"Require Import {data_import}.\n\n"
                f"Module {assembly_module}.\n"
                f"Lemma checked : VkAssemblyCheck.check {column_kind} {index} "
                f"{data}.low_projective_expected "
                f"{data}.high_projective_expected = true.\n"
                "Proof. vm_compute. reflexivity. Qed.\n"
                f"End {assembly_module}.\n",
            )

            aggregate_module = f"Vk{prefix}Certificate"
            imports = "\n".join(
                f"Require Import Garden.Orchard.vk.provenance.generated.certificates.{prefix}{suffix}."
                for suffix in ("Calibration", "Low", "High", "Assembly")
            )
            write(
                CERTS / f"{prefix}.v",
                f"(** Generated aggregate certificate for {kind} column {index}. *)\n"
                "Require Import Garden.Orchard.vk.provenance.Checks.\n"
                "Require Import Garden.Orchard.vk.provenance.Kinds.\n"
                f"Require Import {data_import}.\n"
                + imports
                + f"\n\nModule {aggregate_module}.\n"
                "Definition checked : VkProvenanceChecks.commitment_certificate\n"
                f"    {column_kind} {index} {data}.coefficients\n"
                f"    {data}.low_projective_expected "
                f"{data}.high_projective_expected :=\n"
                "  {| VkProvenanceChecks.calibration_checked := "
                f"{calibration_module}.checked;\n"
                "     VkProvenanceChecks.low_checked := "
                f"Vk{prefix}LowCertificate.checked;\n"
                "     VkProvenanceChecks.high_checked := "
                f"Vk{prefix}HighCertificate.checked;\n"
                "     VkProvenanceChecks.assembly_checked := "
                f"{assembly_module}.checked |}}.\n"
                f"End {aggregate_module}.\n",
            )
            aggregates.append((prefix, data, column_kind, index))

    imports = "\n".join(
        f"Require Import Garden.Orchard.vk.provenance.generated.{prefix}Data.\n"
        f"Require Import Garden.Orchard.vk.provenance.generated.certificates.{prefix}."
        for prefix, _, _, _ in aggregates
    )
    record_fields = "\n".join(
        f"    {prefix.lower()} : VkProvenanceChecks.commitment_certificate "
        f"{kind} {index} {data}.coefficients "
        f"{data}.low_projective_expected "
        f"{data}.high_projective_expected;"
        for prefix, data, kind, index in aggregates
    )
    values = "\n".join(
        f"    {prefix.lower()} := Vk{prefix}Certificate.checked;"
        for prefix, _, _, _ in aggregates
    )
    write(
        CERTS / "Commitments.v",
        "(** Generated aggregation of all 44 commitment certificates. *)\n"
        "Require Import Garden.Orchard.vk.provenance.Checks.\n"
        "Require Import Garden.Orchard.vk.provenance.Kinds.\n"
        + imports
        + "\n\nModule VkCommitmentsCertificate.\n"
        "Record certificate : Prop := {\n"
        + record_fields.rstrip(";")
        + "\n}.\n\nDefinition checked : certificate :=\n  {|\n"
        + values.rstrip(";")
        + "\n  |}.\nEnd VkCommitmentsCertificate.\n",
    )


def emit_main_certificate() -> None:
    write(
        CERTS / "Main.v",
        "(** * Kernel-checked provenance of the Orchard VK commitments *)\n"
        "Require Import Garden.Orchard.vk.provenance.generated.certificates.Domain.\n"
        "Require Import Garden.Orchard.vk.provenance.generated.certificates.Sigma.\n"
        "Require Import Garden.Orchard.vk.provenance.generated.certificates.Srs.\n"
        "Require Import Garden.Orchard.vk.provenance.generated.certificates.Commitments.\n\n"
        "Require Import Garden.Orchard.vk.provenance.Domain.\n"
        "Require Import Garden.Orchard.vk.provenance.Sigma.\n"
        "Require Import Garden.Orchard.vk.provenance.ModelColumnsCorrect.\n"
        "Module OrchardVkProvenance.\n"
        "Record certificate : Prop := {\n"
        "  fixed_column_model : VkModelColumnsCorrect.certificate;\n"
        "  domain_tables : VkDomain.certificate;\n"
        "  sigma_mapping : VkSigmaCertificate.certificate;\n"
        "  params_new_11 : VkSrsCertificate.certificate;\n"
        "  commitments : VkCommitmentsCertificate.certificate\n"
        "}.\n\n"
        "Theorem orchard_vk_commitments_derived : certificate.\n"
        "Proof.\n"
        "  exact {| fixed_column_model := VkModelColumnsCorrect.checked;\n"
        "           domain_tables := VkDomainCertificate.checked;\n"
        "           sigma_mapping := VkSigmaCertificate.checked;\n"
        "           params_new_11 := VkSrsCertificate.checked;\n"
        "           commitments := VkCommitmentsCertificate.checked |}.\n"
        "Qed.\n"
        "End OrchardVkProvenance.\n",
    )


def emit_certificates() -> None:
    emit_domain_certificates()
    emit_sigma_certificate()
    emit_srs_certificates()
    emit_commitment_certificates()
    emit_main_certificate()


def generated_state() -> dict[str, object]:
    expected = expected_vfiles()
    missing = [relative for relative in expected if not (OUT / relative).is_file()]
    if missing:
        raise AssertionError(
            "generator did not emit expected paths: " + ", ".join(missing)
        )
    return {
        "schema": "garden.orchard.vk-provenance.generated-state.v1",
        "source_sha256": source_digest(),
        "files": {
            relative: file_sha256(OUT / relative)
            for relative in expected
        },
    }


def write_generation_metadata() -> None:
    manifest = OUT / MANIFEST_NAME
    wanted_manifest = manifest_text()
    if not manifest.exists() or manifest.read_text() != wanted_manifest:
        atomic_write(manifest, wanted_manifest)

    state = OUT / STATE_NAME
    wanted_state = json.dumps(generated_state(), indent=2, sort_keys=True) + "\n"
    if not state.exists() or state.read_text() != wanted_state:
        atomic_write(state, wanted_state)
    else:
        # Make uses this file as the stamp for generator inputs.  Refresh its
        # timestamp even when a touched input still has identical contents.
        state.touch()


def generation_is_current() -> tuple[bool, str]:
    manifest = OUT / MANIFEST_NAME
    if not manifest.is_file() or manifest.read_text() != manifest_text():
        return False, "manifest is absent or stale"

    state_path = OUT / STATE_NAME
    try:
        state = json.loads(state_path.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return False, "generation state is absent or invalid"
    if state.get("schema") != "garden.orchard.vk-provenance.generated-state.v1":
        return False, "generation-state schema is stale"
    if state.get("source_sha256") != source_digest():
        return False, "a generator input changed"

    expected = expected_vfiles()
    hashes = state.get("files")
    if not isinstance(hashes, dict) or set(hashes) != set(expected):
        return False, "generation-state inventory is stale"
    for relative in expected:
        path = OUT / relative
        if not path.is_file():
            return False, f"generated source is missing: {relative}"
        if hashes[relative] != file_sha256(path):
            return False, f"generated source was modified: {relative}"
    return True, "generated sources are current"


def emit_all() -> None:
    emit_data()
    emit_certificates()
    write_generation_metadata()


def ensure_generated() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    lock_path = OUT / ".generation.lock"
    with lock_path.open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        current, reason = generation_is_current()
        if current:
            print(f"[vk provenance] {reason}")
            return
        print(f"[vk provenance] regenerating: {reason}")
        emit_all()


def check_generated() -> None:
    real_out = OUT
    with tempfile.TemporaryDirectory(prefix="garden-vk-provenance-") as temporary:
        temporary_out = Path(temporary) / "generated"
        try:
            set_output_directory(temporary_out)
            emit_all()
        finally:
            set_output_directory(real_out)

        expected = expected_vfiles()
        actual = sorted(
            path.relative_to(real_out).as_posix()
            for path in real_out.rglob("*.v")
        ) if real_out.exists() else []
        if actual != expected:
            missing = sorted(set(expected) - set(actual))
            extra = sorted(set(actual) - set(expected))
            raise AssertionError(
                f"generated inventory mismatch; missing={missing}, extra={extra}"
            )
        mismatches = [
            relative
            for relative in expected
            if (real_out / relative).read_bytes()
            != (temporary_out / relative).read_bytes()
        ]
        if mismatches:
            raise AssertionError(
                "generated sources differ from a fresh run: "
                + ", ".join(mismatches)
            )
    print("[vk provenance] all 407 generated Rocq sources are current")


def refresh_generated_headers() -> None:
    """Apply generator-header updates without recomputing the witnesses."""
    replacements = {
        "From Stdlib Require Import ZArith Lists.List Bool.Bool.":
            "From Stdlib Require Import ZArith Lists.List Bool.Bool Numbers.Cyclic.Int63.Uint63.",
        "From Stdlib Require Import Lists.List.":
            "From Stdlib Require Import Lists.List Numbers.Cyclic.Int63.Uint63.",
        "Local Open Scope Z_scope.\nLocal Open Scope uint63_scope.":
            "Local Open Scope uint63_scope.\nLocal Open Scope Z_scope.",
    }
    targets = [*OUT.glob("SrsData*.v"), OUT / "SrsExtraData.v",
               *OUT.glob("Fixed*Data.v"), *OUT.glob("Permutation*Data.v")]
    for path in targets:
        source = path.read_text()
        for old, new in replacements.items():
            source = source.replace(old, new)
        write(path, source)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--emit-all", action="store_true")
    actions.add_argument("--ensure", action="store_true")
    actions.add_argument("--check", action="store_true")
    actions.add_argument("--emit-data", action="store_true")
    actions.add_argument("--emit-sigma-data", action="store_true")
    actions.add_argument("--emit-certificates", action="store_true")
    actions.add_argument("--refresh-generated-headers", action="store_true")
    args = parser.parse_args()
    if args.emit_all:
        emit_all()
    elif args.ensure:
        ensure_generated()
    elif args.check:
        check_generated()
    elif args.emit_data:
        emit_data()
        invalidate_state()
    elif args.emit_sigma_data:
        emit_sigma_data()
        invalidate_state()
    elif args.emit_certificates:
        emit_certificates()
        invalidate_state()
    elif args.refresh_generated_headers:
        refresh_generated_headers()
        invalidate_state()


if __name__ == "__main__":
    main()
