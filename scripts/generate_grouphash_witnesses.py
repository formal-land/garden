#!/usr/bin/env python3
"""Offline witness generator for the GroupHash^P provenance checkers.

Recomputes GroupHash^P (protocol section 5.4.9.8: BLAKE2b-512 XMD ->
simplified SWU onto iso-Pallas -> iso-curve addition -> degree-3 isogeny)
for the nine Orchard target points -- the six fixed-base generators and the
three Sinsemilla Q points -- mirroring the Rocq pipeline of
Garden/GroupHash/{blake2b,xmd,sswu,group_hash}.v, cross-checks each result
against the hard-coded literal in the Rocq tree, and dumps the per-point
sqrt_ratio witnesses (was_square flag and root, one pair per hash_to_field
output u) in a paste-ready Rocq shape.

The witnesses are untrusted: the Rocq checker leaves verify each root by one
squaring and one multiplication (Sswu.swu_witness_ok) and recompute the rest
of the pipeline in-kernel. Standard library only; no network.
"""

import hashlib
import sys

# ---------------------------------------------------------------------------
# Field and curve constants (Garden/GroupHash/sswu.v, EllipticCurve/Pallas.v)
# ---------------------------------------------------------------------------

P = 2**254 + 45560315531419706090280762371685220353  # pallas_p

# iso-Pallas (IsoPallas module in sswu.v)
A_ISO = 10949663248450308183708987909873589833737836120165333298109615750520499732811
B_ISO = 1265
Z_ISO = P - 13
LAMBDA = 19814229590243028906643993866117402072516588566294623396325693409366934201135
THETA = 7003529136733518259227950775588032800807760729532353866644138209790443401614

ISO_CONSTANTS = [
    6432893846517566412420610278260439325191790329320346825767705947633326140075,
    23989696149150192365340222745168215001509815558210986772351135915822265203574,
    10492611921771203378452795982353351666191589197598957448093274638589204800759,
    12865787693035132824841220556520878650383580658640693651535411895266652280192,
    13271109177048389296812780941310096270046944650307955939477485891950613419807,
    22768321103861051515190775253992702316905399997697804654926324362758820947460,
    11793638718615538422771118843477472096184948937087302513907460903994431256804,
    11994848074575096182670111372584107500754907779105493386175567957911132601787,
    28823569610051396102362669851238297121581474897215657071023781420043761726004,
    1072148974419594402070101713043406554198631721553391137627950991272221023311,
    5432652610908059517272798285879155923388888734491153551238890455750936314542,
    10408918692925056833786833257634153023990087029210292532869619559576527581706,
    28948022309329048855892746252171976963363056481941560715954676764349967629797,
]

# Pallas itself: y^2 = x^3 + 5
A_PALLAS = 0
B_PALLAS = 5

# ---------------------------------------------------------------------------
# The nine targets and their hard-coded Rocq literals
# ---------------------------------------------------------------------------

TARGETS = [
    # (rocq_name, domain_prefix, message, (x, y) literal, literal location)
    ("spend_auth_g_G", "z.cash:Orchard", "G",
     (25027635063850382358429654596649554085117301901282348152423547104939793041763,
      12128007492603938773365931378340937928001494939630793217712875072231079427017),
     "Orchard/Pallas/Generators.v"),
    ("nullifier_k_G", "z.cash:Orchard", "K",
     (17144890976040313974462754624161095328261290075490099718273142830262355741301,
      9661337292872073193100428608853316471968232023361741282759000480983323509196),
     "Orchard/Pallas/Generators.v"),
    ("value_commit_v_G", "z.cash:Orchard-cv", "v",
     (21457208314186520936880902219424053485005045883401337627148481900742711001959,
      20379375922573002911833717643813254676246486412159279022689151936901102105230),
     "Orchard/Pallas/Generators.v"),
    ("value_commit_r_G", "z.cash:Orchard-cv", "r",
     (3597772235883004661259329170144280297379687592370687591147658848249887611537,
      16317546749781193797530044795837656238506071957562073482938086095508632426954),
     "Orchard/Pallas/Generators.v"),
    ("note_commit_r_G", "z.cash:Orchard-NoteCommit-r", "",
     (17502433695644481444785977856966854265310331039772160001849803703443502427667,
      27531606546556235994383748883097777001194017792923801570415255878186539366371),
     "Orchard/Pallas/Generators.v"),
    ("commit_ivk_r_G", "z.cash:Orchard-CommitIvk-r", "",
     (17022113834174368664964072539940476916905682548990455171271428285673934201112,
      18912017636736613471143674001158885358143653198146604093009134371854861983145),
     "Orchard/Pallas/Generators.v"),
    ("merkle_q", "z.cash:SinsemillaQ", "z.cash:Orchard-MerkleCRH",
     (9991206725476878888751475603038274618448000607209514551456795194094072219296,
      24209798415301550423396126020228723009317736024280831393239261884225294625378),
     "Orchard/circuit.v"),
    ("q_note_commit_m", "z.cash:SinsemillaQ", "z.cash:Orchard-NoteCommit-M",
     (10629404576683096409262958701336170057000067777256141967953463442979689100381,
      22898949290933268079297281211505753011910178734473470279111609228438645877859),
     "Orchard/circuit/note_commit.v"),
    ("q_commit_ivk_m", "z.cash:SinsemillaQ", "z.cash:Orchard-CommitIvk-M",
     (2593820817260930114322133467408868473290945477826616247349533151445648376562,
      12214744946019415453501880094709511126888074367290315326445800415816181472958),
     "Orchard/circuit/commit_ivk.v"),
]

# ---------------------------------------------------------------------------
# Field helpers
# ---------------------------------------------------------------------------


def inv(x):
    return pow(x, -1, P)


def is_square(x):
    x %= P
    return x == 0 or pow(x, (P - 1) // 2, P) == 1


def tonelli_shanks(n):
    """Square root mod P (P - 1 = 2^32 * odd). Raises if n is a nonsquare."""
    n %= P
    if n == 0:
        return 0
    assert is_square(n), "tonelli_shanks called on a nonsquare"
    q = P - 1
    s = 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 5  # 5 is a nonsquare mod pallas_p (the reference ROOT_OF_UNITY base)
    assert not is_square(z)
    m = s
    c = pow(z, q, P)
    t = pow(n, q, P)
    r = pow(n, (q + 1) // 2, P)
    while t != 1:
        t2 = t
        i = 0
        while t2 != 1:
            t2 = t2 * t2 % P
            i += 1
        b = pow(c, 1 << (m - i - 1), P)
        m = i
        c = b * b % P
        t = t * c % P
        r = r * b % P
    assert r * r % P == n
    return r


# ---------------------------------------------------------------------------
# XMD / hash_to_field (Garden/GroupHash/xmd.v)
# ---------------------------------------------------------------------------


def blake2b512(msg):
    return hashlib.blake2b(msg, digest_size=64).digest()


def expand_message_xmd(msg, dst):
    dst_prime = dst + bytes([len(dst)])
    b0 = blake2b512(b"\x00" * 128 + msg + bytes([0, 128, 0]) + dst_prime)
    b1 = blake2b512(b0 + b"\x01" + dst_prime)
    b2 = blake2b512(bytes(x ^ y for x, y in zip(b0, b1)) + b"\x02" + dst_prime)
    return b1 + b2


def hash_to_field(domain_prefix, msg):
    """msg is a str (encoded as UTF-8) or raw bytes."""
    dst = domain_prefix.encode() + b"-" + b"pallas" + b"_XMD:BLAKE2b_SSWU_RO_"
    assert len(dst) < 256
    msg_bytes = msg if isinstance(msg, bytes) else msg.encode()
    uniform = expand_message_xmd(msg_bytes, dst)
    u0 = int.from_bytes(uniform[:64], "big") % P
    u1 = int.from_bytes(uniform[64:], "big") % P
    return u0, u1


# ---------------------------------------------------------------------------
# Simplified SWU onto iso-Pallas (Garden/GroupHash/sswu.v, Sswu module)
# ---------------------------------------------------------------------------


def sswu_intermediates(u):
    z_u2 = Z_ISO * u % P * u % P
    ta = (z_u2 * z_u2 + z_u2) % P
    x1_num = B_ISO * (ta + 1) % P
    x_div = A_ISO * Z_ISO % P if ta == 0 else A_ISO * (-ta) % P
    x_div3 = x_div * x_div % P * x_div % P
    gx1_num = ((x1_num * x1_num + A_ISO * x_div % P * x_div) % P * x1_num
               + B_ISO * x_div3) % P
    x2_num = z_u2 * x1_num % P
    return z_u2, x1_num, x_div, x_div3, gx1_num, x2_num


def sqrt_ratio(num, div):
    """(was_square, root): root^2 * div = num if square, = LAMBDA * num else."""
    r = num * inv(div) % P
    if is_square(r):
        was_square, root = True, tonelli_shanks(r)
        assert root * root % P * div % P == num % P
    else:
        was_square, root = False, tonelli_shanks(LAMBDA * r % P)
        assert root * root % P * div % P == LAMBDA * num % P
    return was_square, root


def map_to_curve_simple_swu(u, was_square, root):
    z_u2, x1_num, x_div, _x_div3, _gx1_num, x2_num = sswu_intermediates(u)
    x_num = x1_num if was_square else x2_num
    y_prime = root if was_square else THETA * z_u2 % P * u % P * root % P
    y = (-y_prime) % P if (u % 2) != (y_prime % 2) else y_prime % P
    return (x_num * inv(x_div) % P, y)


def on_curve(a, b, pt):
    if pt is None:
        return True
    x, y = pt
    return y * y % P == (x * x % P * x + a * x + b) % P


def curve_add(a, p1, p2):
    """Complete affine addition, mirroring Weierstrass.add."""
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if (x1 - x2) % P == 0:
        if (y1 + y2) % P == 0:
            return None
        lam = (3 * x1 * x1 + a) * inv(2 * y1) % P
    else:
        lam = (y2 - y1) * inv(x2 - x1) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return (x3, y3)


def iso_map(pt):
    """Degree-3 isogeny iso-Pallas -> Pallas, affine (sswu.v Sswu.iso_map)."""
    if pt is None:
        return None
    x, y = pt
    c = ISO_CONSTANTS
    x_num = (((c[0] * x + c[1]) % P * x + c[2]) % P * x + c[3]) % P
    x_den = ((x + c[4]) % P * x + c[5]) % P
    y_num = ((((c[6] * x + c[7]) % P * x + c[8]) % P * x + c[9]) % P * y) % P
    y_den = (((x + c[10]) % P * x + c[11]) % P * x + c[12]) % P
    if x_den == 0 or y_den == 0:
        return None
    return (x_num * inv(x_den) % P, y_num * inv(y_den) % P)


# ---------------------------------------------------------------------------
# GroupHash^P and the witness dump
# ---------------------------------------------------------------------------


def group_hash(domain_prefix, msg):
    """Returns (point, witnesses): the Pallas point and the two
    (was_square, root) sqrt_ratio witnesses."""
    u0, u1 = hash_to_field(domain_prefix, msg)
    witnesses = []
    iso_points = []
    for u in (u0, u1):
        _z_u2, _x1n, _xd, x_div3, gx1_num, _x2n = sswu_intermediates(u)
        was_square, root = sqrt_ratio(gx1_num, x_div3)
        witnesses.append((was_square, root))
        pt = map_to_curve_simple_swu(u, was_square, root)
        assert on_curve(A_ISO, B_ISO, pt), "SSWU output not on iso-Pallas"
        iso_points.append(pt)
    total = curve_add(A_ISO, iso_points[0], iso_points[1])
    assert on_curve(A_ISO, B_ISO, total), "iso-curve sum not on iso-Pallas"
    result = iso_map(total)
    assert result is not None, "GroupHash output hit the isogeny kernel"
    assert on_curve(A_PALLAS, B_PALLAS, result), "GroupHash output not on Pallas"
    return result, witnesses


def main():
    failures = []
    print("(* Generated by scripts/generate_grouphash_witnesses.py.")
    print("   Entry shape per point: was_square0, root0, was_square1, root1. *)")
    for name, domain_prefix, msg, expected, location in TARGETS:
        point, witnesses = group_hash(domain_prefix, msg)
        if point != expected:
            failures.append((name, location, expected, point))
            status = "MISMATCH"
        else:
            status = "ok"
        (ws0, r0), (ws1, r1) = witnesses
        print(f"(* {name} <- GroupHash^P({domain_prefix!r}, {msg!r})"
              f" [{location}] : {status} *)")
        print(f"(* {name} *) ({str(ws0).lower()},")
        print(f"  {r0},")
        print(f"  {str(ws1).lower()},")
        print(f"  {r1})")
    if failures:
        print()
        for name, location, expected, got in failures:
            print(f"MISMATCH {name} ({location}):", file=sys.stderr)
            print(f"  literal  x = {expected[0]}", file=sys.stderr)
            print(f"  literal  y = {expected[1]}", file=sys.stderr)
            print(f"  computed x = {got[0]}", file=sys.stderr)
            print(f"  computed y = {got[1]}", file=sys.stderr)
        sys.exit(1)
    print()
    print("(* All 9 points match their Rocq literals. *)")


if __name__ == "__main__":
    main()
