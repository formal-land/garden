#!/usr/bin/env python3
"""Offline oracle for the Halo2 Vesta SRS certificates.

Recomputes the IPA SRS of halo2's Params::<vesta::Affine>::new(11)
(halo2_proofs/src/poly/commitment.rs, halo2 @ 6fcb5136): the n = 2048
generators g_i = hash_to_curve("Halo2-Parameters")([0x00, le32(i)]) and the
blind generator w = hash_to_curve("Halo2-Parameters")([0x01]), where
hash_to_curve is the pasta_curves Vesta pipeline (crate 0.5.1 @ fe08536:
BLAKE2b-512 XMD hash_to_field with curve_id "vesta" -> simplified SWU onto
iso-Vesta -> iso-curve addition -> degree-3 isogeny to Vesta), mirroring the
Rocq pipeline of Garden/GroupHash/{blake2b,xmd,sswu_vesta,group_hash_vesta}.v.

Ground-truth anchoring (no Rust toolchain is required): every constant is the
from_raw limb transcription of the pinned pasta_curves sources
(src/curves.rs `impl Eq` / `iso-vesta`, src/fields/fq.rs ROOT_OF_UNITY), each
is re-derived from its defining relation, and the whole pipeline is asserted
against the three test vectors committed in the pinned checkout's
src/vesta.rs (test_map_to_curve_simple_swu at u = 0 and u = 1, and
test_hash_to_curve for ("z.cash:test", b"hello")).

Emits, per point, the two sqrt_ratio witnesses (was_square flag and root, one
pair per hash_to_field output u_i).  The witnesses and point literals are
untrusted: the Rocq shard certificates (Garden/Orchard/vk_srs_cert_*.v)
verify each root by one squaring and one multiplication
(SswuVesta.swu_witness_ok) and recompute every other stage in-kernel.

Usage (from the repository root):
  python3 scripts/generate_vk_srs_witnesses.py --json OUT.json
  python3 scripts/generate_vk_srs_witnesses.py --json OUT.json \
      --emit-data Garden/Orchard/vk_srs_data.v \
      --emit-certs Garden/Orchard
The --emit-* modes re-parse every literal they wrote and diff it against the
in-memory oracle values before exiting (a transcription slip fails here, not
at vm_compute time).  Standard library only; no network.
"""

import argparse
import hashlib
import json
import re
import sys

# ---------------------------------------------------------------------------
# Fields: Vesta base = pasta Fq = pallas_q; Vesta scalar = pasta Fp = pallas_p
# ---------------------------------------------------------------------------

Q = 2**254 + 45560315531506369815346746415080538113  # pallas_q, point coords
P = 2**254 + 45560315531419706090280762371685220353  # pallas_p, scalars


def from_raw(limbs):
    """pasta's from_raw: little-endian u64 limbs."""
    assert len(limbs) == 4
    return sum(l << (64 * i) for i, l in enumerate(limbs))


# iso-Vesta (pasta_curves src/curves.rs, new_curve_impl! "iso-vesta" a/b and
# impl Eq { ISOGENY_CONSTANTS, Z, THETA }; src/fields/fq.rs ROOT_OF_UNITY).
A_ISO = from_raw([0xc515ad7242eaa6b1, 0x9673928c7d01b212,
                  0x81639c4d96f78773, 0x267f9b2ee592271a])
B_ISO = 1265
Z_ISO = from_raw([0x8c46eb20fffffff4, 0x224698fc0994a8dd,
                  0x0000000000000000, 0x4000000000000000])
THETA = from_raw([0x632cae9872df1b5d, 0x38578ccadf03ac27,
                  0x53c3808d9e2f2357, 0x2b3483a1ee9a382f])
LAMBDA = from_raw([0xa70e2c1102b6d05f, 0x9bb97ea3c106f049,
                   0x9e5c4dfd492ae26e, 0x2de6a9b8746d3f58])

ISO_CONSTANTS = [from_raw(l) for l in [
    [0x43cd42c800000001, 0x0205dd51cfa0961a, 0x8e38e38e38e38e39, 0x38e38e38e38e38e3],
    [0x8b95c6aaf703bcc5, 0x216b8861ec72bd5d, 0xacecf10f5f7c09a2, 0x1d935247b4473d17],
    [0xaeac67bbeb586a3d, 0xd59d03d23b39cb11, 0xed7ee4a9cdf78f8f, 0x18760c7f7a9ad20d],
    [0xfb539a6f0000002b, 0xe1c521a795ac8356, 0x1c71c71c71c71c71, 0x31c71c71c71c71c7],
    [0xb7284f7eaf21a2e9, 0xa3ad678129b604d3, 0x1454798a5b5c56b2, 0x0a2de485568125d5],
    [0xf169c187d2533465, 0x30cd6d53df49d235, 0x0c621de8b91c242a, 0x14735171ee542778],
    [0x6bef1642aaaaaaab, 0x5601f4709a8adcb3, 0xda12f684bda12f68, 0x12f684bda12f684b],
    [0x8bee58e5fb81de63, 0x21d910aefb03b31d, 0xd6767887afbe04d1, 0x2ec9a923da239e8b],
    [0x4986913ab4443034, 0x97a3ca5c24e9ea63, 0x66d1466e9de10e64, 0x19b0d87e16e25788],
    [0x8f64842c55555533, 0x8bc32d36fb21a6a3, 0x425ed097b425ed09, 0x1ed097b425ed097b],
    [0x58dfecce86b2745e, 0x06a767bfc35b5bac, 0x9e7eb64f890a820c, 0x2f44d6c801c1b8bf],
    [0xd43d449776f99d2f, 0x926847fb9ddd76a1, 0x252659ba2b546c7e, 0x3d59f455cafc7668],
    [0x8c46eb20fffffde5, 0x224698fc0994a8dd, 0x0000000000000000, 0x4000000000000000],
]]

# Vesta itself: y^2 = x^3 + 5 over F_Q.
A_VESTA = 0
B_VESTA = 5

N_POINTS = 2048  # k = 11

# ---------------------------------------------------------------------------
# Field helpers over Q
# ---------------------------------------------------------------------------


def inv(x):
    return pow(x, -1, Q)


def is_square(x):
    x %= Q
    return x == 0 or pow(x, (Q - 1) // 2, Q) == 1


def tonelli_shanks(n):
    """Square root mod Q (Q - 1 = 2^32 * odd). Raises if n is a nonsquare."""
    n %= Q
    if n == 0:
        return 0
    assert is_square(n), "tonelli_shanks called on a nonsquare"
    q = Q - 1
    s = 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 5  # 5 is a nonsquare mod Q (the reference GENERATOR of Fq)
    assert not is_square(z)
    m = s
    c = pow(z, q, Q)
    t = pow(n, q, Q)
    r = pow(n, (q + 1) // 2, Q)
    while t != 1:
        t2 = t
        i = 0
        while t2 != 1:
            t2 = t2 * t2 % Q
            i += 1
        b = pow(c, 1 << (m - i - 1), Q)
        m = i
        c = b * b % Q
        t = t * c % Q
        r = r * b % Q
    assert r * r % Q == n
    return r


# ---------------------------------------------------------------------------
# Constant sanity: defining relations of the pinned constants
# ---------------------------------------------------------------------------


def check_constants():
    assert Z_ISO == Q - 13, "Eq::Z is not -13 mod q"
    assert LAMBDA == pow(5, (Q - 1) // 2**32, Q), "Fq::ROOT_OF_UNITY provenance"
    assert not is_square(LAMBDA), "lambda must be a nonsquare"
    assert not is_square(Z_ISO), "Z must be a nonsquare"
    assert THETA * THETA % Q * LAMBDA % Q == Z_ISO, "THETA^2 * lambda = Z"
    assert (4 * pow(A_ISO, 3, Q) + 27 * B_ISO * B_ISO) % Q != 0, "iso-Vesta singular"
    assert ISO_CONSTANTS[12] == Q - 540


# ---------------------------------------------------------------------------
# XMD / hash_to_field (Garden/GroupHash/xmd.v, curve_id "vesta")
# ---------------------------------------------------------------------------


def blake2b512(msg):
    return hashlib.blake2b(msg, digest_size=64).digest()


def expand_message_xmd(msg, dst):
    dst_prime = dst + bytes([len(dst)])
    b0 = blake2b512(b"\x00" * 128 + msg + bytes([0, 128, 0]) + dst_prime)
    b1 = blake2b512(b0 + b"\x01" + dst_prime)
    b2 = blake2b512(bytes(x ^ y for x, y in zip(b0, b1)) + b"\x02" + dst_prime)
    return b1 + b2


def hash_to_field(domain_prefix, msg_bytes):
    dst = domain_prefix.encode() + b"-" + b"vesta" + b"_XMD:BLAKE2b_SSWU_RO_"
    assert len(dst) < 256
    uniform = expand_message_xmd(msg_bytes, dst)
    u0 = int.from_bytes(uniform[:64], "big") % Q
    u1 = int.from_bytes(uniform[64:], "big") % Q
    return u0, u1


# ---------------------------------------------------------------------------
# Simplified SWU onto iso-Vesta (Garden/GroupHash/sswu_vesta.v)
# ---------------------------------------------------------------------------


def sswu_intermediates(u):
    z_u2 = Z_ISO * u % Q * u % Q
    ta = (z_u2 * z_u2 + z_u2) % Q
    x1_num = B_ISO * (ta + 1) % Q
    x_div = A_ISO * Z_ISO % Q if ta == 0 else A_ISO * (-ta) % Q
    x_div3 = x_div * x_div % Q * x_div % Q
    gx1_num = ((x1_num * x1_num + A_ISO * x_div % Q * x_div) % Q * x1_num
               + B_ISO * x_div3) % Q
    x2_num = z_u2 * x1_num % Q
    return z_u2, x1_num, x_div, x_div3, gx1_num, x2_num


def sqrt_ratio(num, div):
    """(was_square, root): root^2 * div = num if square, = LAMBDA * num else."""
    r = num * inv(div) % Q
    if is_square(r):
        was_square, root = True, tonelli_shanks(r)
        assert root * root % Q * div % Q == num % Q
    else:
        was_square, root = False, tonelli_shanks(LAMBDA * r % Q)
        assert root * root % Q * div % Q == LAMBDA * num % Q
    return was_square, root


def map_to_curve_simple_swu(u, was_square, root):
    z_u2, x1_num, x_div, _x_div3, _gx1_num, x2_num = sswu_intermediates(u)
    x_num = x1_num if was_square else x2_num
    y_prime = root if was_square else THETA * z_u2 % Q * u % Q * root % Q
    y = (-y_prime) % Q if (u % 2) != (y_prime % 2) else y_prime % Q
    return (x_num * inv(x_div) % Q, y)


def on_curve(a, b, pt):
    if pt is None:
        return True
    x, y = pt
    return y * y % Q == (x * x % Q * x + a * x + b) % Q


def curve_add(a, p1, p2):
    """Complete affine addition, mirroring Weierstrass.add."""
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if (x1 - x2) % Q == 0:
        if (y1 + y2) % Q == 0:
            return None
        lam = (3 * x1 * x1 + a) * inv(2 * y1) % Q
    else:
        lam = (y2 - y1) * inv(x2 - x1) % Q
    x3 = (lam * lam - x1 - x2) % Q
    y3 = (lam * (x1 - x3) - y1) % Q
    return (x3, y3)


def iso_map(pt):
    """Degree-3 isogeny iso-Vesta -> Vesta, affine."""
    if pt is None:
        return None
    x, y = pt
    c = ISO_CONSTANTS
    x_num = (((c[0] * x + c[1]) % Q * x + c[2]) % Q * x + c[3]) % Q
    x_den = ((x + c[4]) % Q * x + c[5]) % Q
    y_num = ((((c[6] * x + c[7]) % Q * x + c[8]) % Q * x + c[9]) % Q * y) % Q
    y_den = (((x + c[10]) % Q * x + c[11]) % Q * x + c[12]) % Q
    if x_den == 0 or y_den == 0:
        return None
    return (x_num * inv(x_den) % Q, y_num * inv(y_den) % Q)


# ---------------------------------------------------------------------------
# hash_to_curve and the pinned test vectors of pasta_curves src/vesta.rs
# ---------------------------------------------------------------------------


def hash_to_curve(domain_prefix, msg_bytes):
    """Returns (point, witnesses): the Vesta point and the two
    (was_square, root) sqrt_ratio witnesses."""
    u0, u1 = hash_to_field(domain_prefix, msg_bytes)
    witnesses = []
    iso_points = []
    for u in (u0, u1):
        _z_u2, _x1n, _xd, x_div3, gx1_num, _x2n = sswu_intermediates(u)
        was_square, root = sqrt_ratio(gx1_num, x_div3)
        witnesses.append((was_square, root))
        pt = map_to_curve_simple_swu(u, was_square, root)
        assert on_curve(A_ISO, B_ISO, pt), "SSWU output not on iso-Vesta"
        iso_points.append(pt)
    total = curve_add(A_ISO, iso_points[0], iso_points[1])
    assert on_curve(A_ISO, B_ISO, total), "iso-curve sum not on iso-Vesta"
    result = iso_map(total)
    assert result is not None, "hash_to_curve output hit the isogeny kernel"
    assert on_curve(A_VESTA, B_VESTA, result), "output not on Vesta"
    return result, witnesses


def jacobian_to_affine(x, y, z):
    zi = inv(z)
    return (x * zi * zi % Q, y * zi * zi % Q * zi % Q)


def check_test_vectors():
    """The three vectors committed in pasta_curves src/vesta.rs (@ fe08536)."""
    # test_map_to_curve_simple_swu, u = 0 (exercises the ta = 0 branch).
    ws, root = sqrt_ratio(*(lambda t: (t[4], t[3]))(sswu_intermediates(0)))
    got = map_to_curve_simple_swu(0, ws, root)
    exp = jacobian_to_affine(
        0x2ccc4c6ec2660e5644305bc52527d904d408f92407f599df8f158d50646a2e78,
        0x29a34381321d13d72d50b6b462bb4ea6a9e47393fa28a47227bf35bc0ee7aa59,
        0x0b851e9e579403a76df1100f556e1f226e5656bdf38f3bf8601d8a3a9a15890b)
    assert got == exp, "SSWU u=0 vector mismatch"
    # test_map_to_curve_simple_swu, u = 1.
    ws, root = sqrt_ratio(*(lambda t: (t[4], t[3]))(sswu_intermediates(1)))
    got = map_to_curve_simple_swu(1, ws, root)
    exp = jacobian_to_affine(
        0x165f8b71841c5abc3d742ec13fb16f099d596b781e6f5c7d0b6682b1216a8258,
        0x0dadef21de74ed7337a37dd74f126a92e4df73c3a704da501e36eaf59cf03120,
        0x0a3d6f6c1af02bd9274cc0b80129759ce77edeef578d7de968d4a47d39026c82)
    assert got == exp, "SSWU u=1 vector mismatch"
    # test_hash_to_curve: ("z.cash:test", b"hello").
    got, _w = hash_to_curve("z.cash:test", b"hello")
    exp = jacobian_to_affine(
        0x12763505036e0e1a6684b7a7d8d5afb7378cc2b191a95e34f44824a06fcbd08e,
        0x0256eafc0188b79bfa7c4b2b393893ddc298e90da500fa4a9aee17c2ea4240e6,
        0x1b58d4aa4d68c3f4d9916b77c79ff9911597a27f2ee46244e98eb9615172d2ad)
    assert got == exp, "hash_to_curve vector mismatch"
    return {"sswu_u0": jacobian_to_affine(
                0x2ccc4c6ec2660e5644305bc52527d904d408f92407f599df8f158d50646a2e78,
                0x29a34381321d13d72d50b6b462bb4ea6a9e47393fa28a47227bf35bc0ee7aa59,
                0x0b851e9e579403a76df1100f556e1f226e5656bdf38f3bf8601d8a3a9a15890b),
            "sswu_u1": jacobian_to_affine(
                0x165f8b71841c5abc3d742ec13fb16f099d596b781e6f5c7d0b6682b1216a8258,
                0x0dadef21de74ed7337a37dd74f126a92e4df73c3a704da501e36eaf59cf03120,
                0x0a3d6f6c1af02bd9274cc0b80129759ce77edeef578d7de968d4a47d39026c82),
            "hash": got}


# ---------------------------------------------------------------------------
# The SRS
# ---------------------------------------------------------------------------


def srs_message(i):
    """The 5-byte message of g_i: [0x00, le32(i)] (commitment.rs:57-58)."""
    return bytes([0]) + i.to_bytes(4, "little")


def compute_srs():
    g = []
    for i in range(N_POINTS):
        pt, wits = hash_to_curve("Halo2-Parameters", srs_message(i))
        (ws0, r0), (ws1, r1) = wits
        g.append({"i": i, "x": pt[0], "y": pt[1],
                  "ws0": ws0, "root0": r0, "ws1": ws1, "root1": r1})
    ptw, witsw = hash_to_curve("Halo2-Parameters", bytes([1]))
    (ws0, r0), (ws1, r1) = witsw
    w = {"x": ptw[0], "y": ptw[1],
         "ws0": ws0, "root0": r0, "ws1": ws1, "root1": r1}
    return g, w


# ---------------------------------------------------------------------------
# Rocq emission
# ---------------------------------------------------------------------------

SHARDS = 16
SHARD_SIZE = N_POINTS // SHARDS

DATA_SHARD_TEMPLATE = '''(** * Halo2 Vesta SRS literals, shard {k}: generators [g_{lo} .. g_{hi}]

    128 entries of the SRS of [Params::<vesta::Affine>::new(11)]
    ([halo2_proofs/src/poly/commitment.rs]): per generator, the index, the
    two [sqrt_ratio] witnesses, and the affine coordinates (reduced residues
    of the Vesta base field [F_{{pallas_q}}]); entry shape
    [Orchard/vk_srs_entry.v].  Untrusted witness input, verified in-kernel by
    [Orchard/vk_srs_cert_{k}.v]; the whole-SRS table is assembled in
    [Orchard/vk_srs_data.v].  The tables are sharded across sixteen files
    because single-file elaboration cost grows superlinearly in the number of
    literal blocks.

    Generated by [scripts/generate_vk_srs_witnesses.py]; regenerate with

      python3 scripts/generate_vk_srs_witnesses.py \\
        --emit-data Garden/Orchard/vk_srs_data.v --emit-certs Garden/Orchard *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Orchard.vk_srs_entry.

Import ListNotations.

Global Open Scope Z_scope.

Module VkSrsData{k}.
  Import VkSrsEntry (E).

  Definition shard : list VkSrsEntry.t := [
{rows}
  ].
End VkSrsData{k}.
'''

DATA_MAIN_TEMPLATE = '''(** * The Halo2 Vesta SRS ([k = 11], [n = 2048]), assembled literal tables

    The [n + 1] affine Vesta points of [Params::<vesta::Affine>::new(11)]
    ([halo2_proofs/src/poly/commitment.rs]): the generators
    [g_i = hash_to_curve("Halo2-Parameters")([0x00, le32(i)])] and the blind
    generator [w = hash_to_curve("Halo2-Parameters")([0x01])], with the two
    [sqrt_ratio] witnesses (an is-square flag and a root per [hash_to_field]
    output [u_j]) each certificate needs.  Coordinates and roots are reduced
    residues of the Vesta base field [F_{{pallas_q}}].  The per-shard literal
    tables live in [Orchard/vk_srs_data_{{0..15}}.v] (entry shape
    [Orchard/vk_srs_entry.v]).

    Untrusted witness input: every entry is verified in-kernel by the shard
    certificates [Garden/Orchard/vk_srs_cert_{{0..15}}.v] (the witnesses by
    the [SswuVesta.swu_witness_ok] squaring equations, the points by
    recomputing the full [GroupHashVesta] pipeline) and assembled in
    [Garden/Orchard/vk_srs_cert.v].

    Generated by [scripts/generate_vk_srs_witnesses.py]; regenerate with

      python3 scripts/generate_vk_srs_witnesses.py \\
        --emit-data Garden/Orchard/vk_srs_data.v --emit-certs Garden/Orchard *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Orchard.vk_srs_entry.
{requires}

Import ListNotations.

Global Open Scope Z_scope.

Module VkSrsData.
{aliases}

  (** The 2048 SRS entries in index order. *)
  Definition g_entries : list VkSrsEntry.t :=
{shard_concat}.

  (** The generator points [g_0 .. g_2047], index order. *)
  Definition g_points : list (Z * Z) :=
    List.map VkSrsEntry.point g_entries.

  (** The blind generator [w] and its witnesses
      ([was_square0, root0, was_square1, root1, x, y]). *)
  Definition w_entry : bool * Z * bool * Z * Z * Z :=
    ({w_ws0},
     {w_root0},
     {w_ws1},
     {w_root1},
     {w_x},
     {w_y}).

  Definition w_point : Z * Z :=
    let '(_, _, _, _, x, y) := w_entry in (x, y).
End VkSrsData.
'''

CERT_TEMPLATE = '''(** * Vesta SRS provenance, shard {k}: generators [g_{lo} .. g_{hi}]

    In-kernel derivation of 128 generators of the Halo2 Vesta SRS
    ([Params::<vesta::Affine>::new(11)], [halo2_proofs/src/poly/commitment.rs]):
    for each index [i], [g_i = hash_to_curve("Halo2-Parameters")(m_i)] with
    [m_i] the 5 bytes [0x00, le32(i)], via the pipeline of
    [GroupHash/group_hash_vesta.v].  The two [sqrt_ratio] outputs per entry
    are pasted untrusted witnesses from
    [scripts/generate_vk_srs_witnesses.py], validated by
    [GroupHashVesta.witnesses_ok] (one squaring and one multiplication per
    root); the BLAKE2b-512 XMD expansion, the witnessed SSWU maps, the
    iso-curve addition, and [SswuVesta.iso_map] are recomputed by the
    checker's [vm_compute].  The index lemma pins this shard's entries to the
    contiguous index range, for the whole-SRS statement in
    [Orchard/vk_srs_cert.v]. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Garden.Field.Field.
Require Import Garden.EllipticCurve.Weierstrass.
Require Import Garden.GroupHash.group_hash.
Require Import Garden.GroupHash.group_hash_vesta.
Require Import Garden.Orchard.vk_srs_entry.
Require Import Garden.Orchard.vk_srs_data_{k}.

Import ListNotations.

Global Open Scope Z_scope.

(** The entry indices are exactly [{lo} .. {hi}], in order. *)
Lemma vk_srs_shard_{k}_indices :
  List.map VkSrsEntry.index VkSrsData{k}.shard
  = List.map (fun n : nat => {lo} + Z.of_nat n) (List.seq 0 128).
Proof. vm_compute; reflexivity. Qed.

(** Per entry: the pasted witnesses satisfy the [sqrt_ratio] defining
    equations at the two [hash_to_field] outputs for [m_i], and the witnessed
    [GroupHashVesta] recomputation equals the pasted generator. *)
Lemma vk_srs_shard_{k}_check :
  List.forallb
    (fun e : VkSrsEntry.t =>
      let '(i, was_square0, root0, was_square1, root1, x, y) := e in
      GroupHashVesta.witnesses_ok GroupHashVesta.halo2_parameters_prefix
        (GroupHashVesta.srs_message i) was_square0 root0 was_square1 root1
        && GroupHash.point_eqb
             (GroupHashVesta.group_hash_with_witness
               GroupHashVesta.halo2_parameters_prefix
               (GroupHashVesta.srs_message i)
               was_square0 root0 was_square1 root1)
             (Weierstrass.Affine x y))
    VkSrsData{k}.shard
  = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
'''


def emit_data(path, g, w):
    assert path.endswith("vk_srs_data.v")
    base = path[:-len("vk_srs_data.v")]
    for k in range(SHARDS):
        lo = k * SHARD_SIZE
        rows = []
        for e in g[lo:lo + SHARD_SIZE]:
            rows.append(
                "    E {i} {ws0} {root0} {ws1} {root1} {x} {y}".format(
                    i=e["i"],
                    ws0=str(e["ws0"]).lower(), root0=e["root0"],
                    ws1=str(e["ws1"]).lower(), root1=e["root1"],
                    x=e["x"], y=e["y"]))
        with open(f"{base}vk_srs_data_{k}.v", "w") as f:
            f.write(DATA_SHARD_TEMPLATE.format(
                k=k, lo=lo, hi=lo + SHARD_SIZE - 1, rows=";\n".join(rows)))
    requires = "\n".join(
        f"Require Import Garden.Orchard.vk_srs_data_{k}."
        for k in range(SHARDS))
    aliases = "\n".join(
        f"  Definition shard_{k} : list VkSrsEntry.t := VkSrsData{k}.shard."
        for k in range(SHARDS))
    shard_concat = "\n".join(
        "    {}shard_{}".format("" if k == 0 else "++ ", k)
        for k in range(SHARDS))
    with open(path, "w") as f:
        f.write(DATA_MAIN_TEMPLATE.format(
            requires=requires, aliases=aliases, shard_concat=shard_concat,
            w_ws0=str(w["ws0"]).lower(), w_root0=w["root0"],
            w_ws1=str(w["ws1"]).lower(), w_root1=w["root1"],
            w_x=w["x"], w_y=w["y"]))


def emit_certs(directory, g):
    for k in range(SHARDS):
        lo = k * SHARD_SIZE
        path = f"{directory}/vk_srs_cert_{k}.v"
        with open(path, "w") as f:
            f.write(CERT_TEMPLATE.format(k=k, lo=lo, hi=lo + SHARD_SIZE - 1))


def reparse_and_diff(data_path, g, w):
    """Parse every literal back out of the emitted data files and diff it
    against the oracle values; a mismatch is fatal."""
    assert data_path.endswith("vk_srs_data.v")
    base = data_path[:-len("vk_srs_data.v")]
    text = "".join(open(f"{base}vk_srs_data_{k}.v").read()
                   for k in range(SHARDS))
    entry_re = re.compile(
        r"E (\d+) (true|false) (\d+) (true|false) (\d+) (\d+) (\d+)")
    seen = {}
    for m in entry_re.finditer(text):
        i = int(m.group(1))
        assert i not in seen, f"duplicate entry index {i}"
        seen[i] = (m.group(2) == "true", int(m.group(3)),
                   m.group(4) == "true", int(m.group(5)),
                   int(m.group(6)), int(m.group(7)))
    text = open(data_path).read()
    assert len(seen) == N_POINTS, f"parsed {len(seen)} entries"
    for e in g:
        got = seen[e["i"]]
        exp = (e["ws0"], e["root0"], e["ws1"], e["root1"], e["x"], e["y"])
        assert got == exp, f"entry {e['i']} literal diff"
    wm = re.search(
        r"Definition w_entry[^(]*\(\s*(true|false),\s*(\d+),\s*"
        r"(true|false),\s*(\d+),\s*(\d+),\s*(\d+)\)", text, re.S)
    assert wm, "w_entry not found"
    got = (wm.group(1) == "true", int(wm.group(2)),
           wm.group(3) == "true", int(wm.group(4)),
           int(wm.group(5)), int(wm.group(6)))
    exp = (w["ws0"], w["root0"], w["ws1"], w["root1"], w["x"], w["y"])
    assert got == exp, "w literal diff"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", help="write the oracle dump to this path")
    ap.add_argument("--emit-data", help="write Garden/Orchard/vk_srs_data.v")
    ap.add_argument("--emit-certs",
                    help="directory for vk_srs_cert_{0..15}.v")
    args = ap.parse_args()

    check_constants()
    vectors = check_test_vectors()
    print("constants and the three pinned vesta.rs test vectors: ok")
    print("  hash_to_curve('z.cash:test', b'hello') affine =")
    print(f"    x = {vectors['hash'][0]}")
    print(f"    y = {vectors['hash'][1]}")

    g, w = compute_srs()
    print(f"computed {len(g)} generators + w; all on Vesta")

    if args.json:
        with open(args.json, "w") as f:
            json.dump({"g": g, "w": w}, f)
        print(f"wrote {args.json}")
    if args.emit_data:
        emit_data(args.emit_data, g, w)
        reparse_and_diff(args.emit_data, g, w)
        print(f"wrote {args.emit_data} (re-parsed: every literal matches)")
    if args.emit_certs:
        emit_certs(args.emit_certs, g)
        print(f"wrote {args.emit_certs}/vk_srs_cert_{{0..15}}.v")


if __name__ == "__main__":
    main()
