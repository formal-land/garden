#!/usr/bin/env python3
"""Offline witness generator for the Sinsemilla S-table provenance shards.

Recomputes GroupHash^P("z.cash:SinsemillaS", I2LEOSP_32(j)) for every table
index j in [0, 1024) (protocol section 5.4.1.9; the halo2_gadgets generator
table), reusing the pipeline of generate_grouphash_witnesses.py, and
cross-checks each derived point against the corresponding entry of
Garden/Halo2/halo2_gadgets/sinsemilla/sinsemilla_s.v.  Only when all 1024
points match does it emit the eight checker shard leaves
Garden/Halo2/halo2_gadgets/sinsemilla/provenance/shard_{0..7}.v (128 entries
each), pasting the per-entry sqrt_ratio witnesses (was_square flag and root,
one pair per hash_to_field output u).

The witnesses are untrusted: each shard's checker validates every root by
one squaring and one multiplication (Sswu.swu_witness_ok) and recomputes the
BLAKE2b-512 XMD expansion, the witnessed SSWU maps, the iso-curve addition,
and iso_map in-kernel.  Standard library only; no network.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import generate_grouphash_witnesses as gh  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SINSEMILLA_S = os.path.join(
    ROOT, "Garden", "Halo2", "halo2_gadgets", "sinsemilla", "sinsemilla_s.v")
OUT_DIR = os.path.join(
    ROOT, "Garden", "Halo2", "halo2_gadgets", "sinsemilla", "provenance")

TABLE_SIZE = 1024
SHARDS = 8
SHARD_LEN = TABLE_SIZE // SHARDS

HEADER = '''\
(** * Provenance of the Sinsemilla [S] table, shard {k}: entries [{lo}..{hi}]

    In-kernel derivation of 128 entries of the Sinsemilla generator table
    ([Halo2/halo2_gadgets/sinsemilla/sinsemilla_s.v]) from the protocol's own
    algorithm (§5.4.1.9): for each index [j],
    [S(j) = GroupHash^P("z.cash:SinsemillaS", I2LEOSP_32(j))], via the
    pipeline of [GroupHash/group_hash.v].  The two [sqrt_ratio] outputs per
    entry are pasted untrusted witnesses from
    [scripts/generate_sinsemilla_witnesses.py], validated by
    [GroupHash.witnesses_ok] (one squaring and one multiplication per root);
    the BLAKE2b-512 XMD expansion, the witnessed SSWU maps, the iso-curve
    addition, and [iso_map] are recomputed by the checker's [vm_compute].
    The index lemma pins this shard's entries to the contiguous index range,
    for the whole-table statement in [provenance/main.v]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.
Require Import Garden.Field.Field.
Require Import Garden.Field.Sqrt.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.EllipticCurve.Pallas.
Require Import Garden.GroupHash.xmd.
Require Import Garden.GroupHash.sswu.
Require Import Garden.GroupHash.group_hash.
Require Garden.Halo2.halo2_gadgets.sinsemilla.sinsemilla_s.

Import ListNotations.

Global Open Scope Z_scope.

#[local] Existing Instance Primes.PallasPIsPrime.

Strategy opaque [is_square modpow modpow_pos field_sqrt].

(** Entry shape: [(j, was_square0, root0, was_square1, root1)] — the table
    index and the two pasted [sqrt_ratio] witnesses. *)
Definition entries : list (Z * bool * Z * bool * Z) := [
{entries}
].

(** The entry indices are exactly [{lo}..{hi}], in order. *)
Lemma sinsemilla_s_shard_{k}_indices :
  List.map
    (fun e : Z * bool * Z * bool * Z => let '(j, _, _, _, _) := e in j)
    entries
  = List.map (fun n : nat => {lo} + Z.of_nat n) (List.seq 0 128).
Proof. vm_compute; reflexivity. Qed.

(** Per entry: the pasted witnesses satisfy the [sqrt_ratio] defining
    equations at the two [hash_to_field] outputs for
    [I2LEOSP_32(j)] (little-endian byte decomposition of [j]), and the
    witnessed [GroupHash^P] recomputation equals the table entry. *)
Lemma sinsemilla_s_shard_{k}_check :
  List.forallb
    (fun e : Z * bool * Z * bool * Z =>
      let '(j, was_square0, root0, was_square1, root1) := e in
      let m := [j mod 256; j / 256 mod 256;
                j / 65536 mod 256; j / 16777216 mod 256] in
      GroupHash.witnesses_ok (Xmd.bytes_of_string "z.cash:SinsemillaS"%string)
        m was_square0 root0 was_square1 root1
        && GroupHash.point_eqb
             (GroupHash.group_hash_with_witness
               (Xmd.bytes_of_string "z.cash:SinsemillaS"%string)
               m was_square0 root0 was_square1 root1)
             (Weierstrass.Affine
               (fst (sinsemilla_s.get j)) (snd (sinsemilla_s.get j))))
    entries
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
'''


def parse_table():
    with open(SINSEMILLA_S) as f:
        text = f.read()
    body = text.split("Definition values", 1)[1].split("].", 1)[0]
    pairs = re.findall(r"\((\d+),\s*(\d+)\)", body)
    assert len(pairs) == TABLE_SIZE, f"parsed {len(pairs)} entries"
    return [(int(x), int(y)) for x, y in pairs]


def main():
    table = parse_table()
    results = []
    failures = []
    for j in range(TABLE_SIZE):
        point, witnesses = gh.group_hash(
            "z.cash:SinsemillaS", j.to_bytes(4, "little"))
        if point != table[j]:
            failures.append((j, table[j], point))
        results.append(witnesses)
    if failures:
        for j, expected, got in failures:
            print(f"MISMATCH S[{j}]:", file=sys.stderr)
            print(f"  literal  x = {expected[0]}", file=sys.stderr)
            print(f"  literal  y = {expected[1]}", file=sys.stderr)
            print(f"  computed x = {got[0]}", file=sys.stderr)
            print(f"  computed y = {got[1]}", file=sys.stderr)
        print(f"{len(failures)} of {TABLE_SIZE} entries mismatch; "
              "no files written.", file=sys.stderr)
        sys.exit(1)
    print(f"All {TABLE_SIZE} derived points match sinsemilla_s.values.")

    os.makedirs(OUT_DIR, exist_ok=True)
    for k in range(SHARDS):
        lo = k * SHARD_LEN
        hi = lo + SHARD_LEN - 1
        lines = []
        for j in range(lo, lo + SHARD_LEN):
            (ws0, r0), (ws1, r1) = results[j]
            sep = ";" if j != lo + SHARD_LEN - 1 else ""
            lines.append(f"  ({j}, {str(ws0).lower()}, {r0}, "
                         f"{str(ws1).lower()}, {r1}){sep}")
        path = os.path.join(OUT_DIR, f"shard_{k}.v")
        with open(path, "w") as f:
            f.write(HEADER.replace("{entries}", "\n".join(lines))
                    .replace("{k}", str(k))
                    .replace("{lo}", str(lo))
                    .replace("{hi}", str(hi)))
        print(f"wrote {path} ({os.path.getsize(path)} bytes)")


if __name__ == "__main__":
    main()
