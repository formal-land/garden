#!/usr/bin/env python3
"""Generate the per-column literal data files for the vk-commitment MSM
certificates (Garden/Orchard/vk_msm.v machinery).

Inputs (untrusted; every literal is re-verified in-kernel):
  - the certified SRS literals Garden/Orchard/vk_srs_data_{0..15}.v and
    the blind point in Garden/Orchard/vk_srs_data.v;
  - the pinned commitment literals in Garden/Orchard/vk_pinned_data.v;
  - a column dump: the full 2048-row Lagrange vector of one compiled
    fixed/permutation column, produced by an `Eval vm_compute` on the
    replayed grid accessor (see the header of the emitted file).

Per column this script computes c = iNTT(v) mod pallas_p, cross-checks
  sum_m c_m * g_m + w  ==  pinned commitment
offline (full EC MSM over Vesta), computes the two half-range Pippenger
checkpoint points, and emits a paste-ready data file
Garden/Orchard/vk_msm_data_<name>.v.

Usage (from the repository root):

  python3 scripts/generate_vk_msm.py <dump.txt> <index> fixed|perm <name>

e.g.  python3 scripts/generate_vk_msm.py /tmp/col0_dump.txt 0 fixed fixed0
"""
import re
import sys
import os

ROOT = os.path.join(os.path.dirname(__file__), "..")
GARDEN = os.path.join(ROOT, "Garden")

q = 2**254 + 45560315531506369815346746415080538113   # Vesta base field
p = 2**254 + 45560315531419706090280762371685220353   # Vesta group order

omega = 0x181b50ad5f32119e31cbd395426d600b7a9b88bcaaa1c24eef28545aada17813
omega_inv = pow(omega, -1, p)
n_inv = pow(2048, -1, p)

CMD = "python3 scripts/generate_vk_msm.py"


def parse_srs():
    pts = {}
    for s in range(16):
        with open(os.path.join(GARDEN, "Orchard", f"vk_srs_data_{s}.v")) as f:
            text = f.read()
        for m in re.finditer(
                r"E (\d+) (?:false|true) \d+ (?:false|true) \d+ (\d+) (\d+)",
                text):
            pts[int(m.group(1))] = (int(m.group(2)), int(m.group(3)))
    assert sorted(pts) == list(range(2048)), "missing SRS indices"
    with open(os.path.join(GARDEN, "Orchard", "vk_srs_data.v")) as f:
        text = f.read()
    m = re.search(
        r"w_entry[^(]*\(\s*(?:false|true),\s*(\d+),\s*(?:false|true),"
        r"\s*(\d+),\s*(\d+),\s*(\d+)\)", text, re.S)
    assert m, "w_entry not found"
    return [pts[i] for i in range(2048)], (int(m.group(3)), int(m.group(4)))


def parse_pinned():
    with open(os.path.join(GARDEN, "Orchard", "vk_pinned_data.v")) as f:
        text = f.read()

    def plist(name):
        m = re.search(name + r"\s*:\s*list \(Z \* Z\) := \[(.*?)\]\.",
                      text, re.S)
        pairs = re.findall(r"\((0x[0-9a-f]+),\s*(0x[0-9a-f]+)\)", m.group(1))
        return [(int(a, 16), int(b, 16)) for a, b in pairs]
    return plist("fixed_commitments"), plist("permutation_commitments")


def ec_add(P, Q):
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if (x1 - x2) % q == 0:
        if (y1 + y2) % q == 0:
            return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, q) % q
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, q) % q
    x3 = (lam * lam - x1 - x2) % q
    return (x3, (lam * (x1 - x3) - y1) % q)


def ec_mul(k, P):
    R = None
    while k:
        if k & 1:
            R = ec_add(R, P)
        P = ec_add(P, P)
        k >>= 1
    return R


def ntt(a, root, mod):
    n = len(a)
    if n == 1:
        return a[:]
    e = ntt(a[0::2], root * root % mod, mod)
    o = ntt(a[1::2], root * root % mod, mod)
    out = [0] * n
    t = 1
    for j in range(n // 2):
        u, v = e[j], t * o[j] % mod
        out[j] = (u + v) % mod
        out[j + n // 2] = (u - v) % mod
        t = t * root % mod
    return out


def pippenger(scalars, bases):
    """Mirror of VkMsm.msm_pippenger: 32 windows of 8 bits, MSB first,
    buckets 1..255, suffix-sum aggregation."""
    acc = None
    for t in reversed(range(32)):
        for _ in range(8):
            acc = ec_add(acc, acc)
        buckets = [None] * 256
        for c, g in zip(scalars, bases):
            d = (c >> (8 * t)) & 255
            if d:
                buckets[d] = ec_add(buckets[d], g)
        run = None
        wsum = None
        for v in reversed(range(1, 256)):
            run = ec_add(run, buckets[v])
            wsum = ec_add(wsum, run)
        acc = ec_add(acc, wsum)
    return acc


def parse_dump(path):
    with open(path) as f:
        text = f.read()
    m = re.search(r"= Some\s*\[(.*?)\]", text, re.S)
    return [int(x) for x in re.split(r";", m.group(1))]


def main():
    dump, idx, kind, name = (sys.argv[1], int(sys.argv[2]), sys.argv[3],
                             sys.argv[4])
    g, w = parse_srs()
    fixed, perm = parse_pinned()
    pinned = (fixed if kind == "fixed" else perm)[idx]

    v = parse_dump(dump)
    assert len(v) == 2048, len(v)
    assert all(0 <= x < p for x in v)
    c = [x * n_inv % p for x in ntt(v, omega_inv, p)]

    # offline cross-check of the whole pipeline against the pinned point
    acc = None
    for ci, gi in zip(c, g):
        acc = ec_add(acc, ec_mul(ci, gi))
    assert ec_add(acc, w) == pinned, "MSM does not match the pinned point"

    cpa = pippenger(c[:1024], g[:1024])
    cpb = pippenger(c[1024:], g[1024:])
    assert ec_add(ec_add(cpa, cpb), w) == pinned

    mod = "VkMsmData" + name.capitalize()
    out = os.path.join(GARDEN, "Orchard", f"vk_msm_data_{name}.v")

    # A checkpoint of an all-zero coefficient shard is the point at
    # infinity (no affine (x, y) representation).  When either half-range
    # checkpoint is the identity, emit both checkpoints as [VkMsm.point]
    # values ([Weierstrass.Affine x y] / [Weierstrass.Infinity]) instead
    # of the affine [Z * Z] pairs; the consuming certificate then passes
    # [cpa]/[cpb] to [commit_two_shards] directly, with no [aff] wrapper.
    degenerate = (cpa is None) or (cpb is None)

    def pt_lit(P):
        if P is None:
            return "Weierstrass.Infinity"
        return f"Weierstrass.Affine\n      {P[0]}\n      {P[1]}"

    with open(out, "w") as f:
        chkpt_doc = ("the two half-range Pippenger checkpoint points over "
                     "Vesta")
        if degenerate:
            chkpt_doc += (" (a shard whose coefficients are all zero has "
                          "the point at infinity as its checkpoint, so the "
                          "checkpoints are given as [VkMsm.point] values)")
        f.write(f"""(** * MSM certificate literals: {kind} column {idx}

    The full 2048-row Lagrange vector [v] of the compiled column (dumped
    from the replayed grid accessor), its inverse-NTT coefficient vector
    [c] over [F_pallas_p], and {chkpt_doc}.  Untrusted witness input:
    the certificates re-derive [v] from the accessor, [c] by the
    in-kernel [VkMsm.intt], the checkpoints by [VkMsm.msm_pippenger],
    and the final sum against the pinned commitment literal.

    Generated by [scripts/generate_vk_msm.py]; regenerate with

      {CMD} <dump> {idx} {kind} {name} *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
""")
        if degenerate:
            f.write("Require Import Garden.EllipticCurve.Weierstrass.\n")
        f.write(f"""
Import ListNotations.

Global Open Scope Z_scope.

Module {mod}.
""")
        f.write("  Definition v : list Z := [\n    "
                + ";\n    ".join(str(x) for x in v) + "].\n\n")
        f.write("  Definition c : list Z := [\n    "
                + ";\n    ".join(str(x) for x in c) + "].\n\n")
        if degenerate:
            f.write(f"  Definition cpa : Weierstrass.point :=\n    "
                    f"{pt_lit(cpa)}.\n\n")
            f.write(f"  Definition cpb : Weierstrass.point :=\n    "
                    f"{pt_lit(cpb)}.\n")
        else:
            f.write(f"  Definition cpa : Z * Z :=\n    "
                    f"({cpa[0]},\n     {cpa[1]}).\n\n")
            f.write(f"  Definition cpb : Z * Z :=\n    "
                    f"({cpb[0]},\n     {cpb[1]}).\n")
        f.write(f"End {mod}.\n")
    print("wrote", out, "(degenerate)" if degenerate else "")

    # small-scale reference values for a cheap checker validation
    mini = pippenger(c[:8], g[:8])
    print("mini8:", mini)


if __name__ == "__main__":
    main()
