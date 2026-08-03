#!/usr/bin/env python3
"""Generate/check Orchard verifying-key commitment provenance witnesses.

This is deliberately an *untrusted* generator.  The generated values are
consumed by small Rocq certificate leaves which recompute the relevant
GroupHash, inverse-FFT and MSM equations in the kernel.  Keeping the
generator independent and simple is useful nevertheless: ``--verify``
must reproduce all 29 fixed-column and 15 permutation commitments in the
deployed Post-NU6.3 verifying key before any witness files are emitted.

Only the Python standard library is used.  The implementation mirrors:

* ``pasta_curves::CurveExt::hash_to_curve`` for Vesta;
* ``halo2_proofs::poly::commitment::Params::new(11)``;
* selector compression and permutation assembly for the committed model
  snapshots; and
* ``Params::commit_lagrange(poly, Blind::default())``, where the default
  blind is one and therefore contributes the point ``w``.

The command is intentionally side-effect free for now.  ``--verify`` emits
a compact JSON summary to stdout; the Rocq shard emitter is layered on this
checked core below.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Iterable, Optional


ROOT = Path(__file__).resolve().parents[1]
N = 2048
K = 11

# The scalar field used by Vesta / the field of Orchard circuit columns.
P = 2**254 + 45560315531419706090280762371685220353
# The coordinate field used by Vesta.
Q = 2**254 + 45560315531506369815346746415080538113


def from_u64_limbs(words: Iterable[int]) -> int:
    return sum(word << (64 * i) for i, word in enumerate(words))


# iso-Vesta and hash-to-curve constants from pasta_curves 0.5.x,
# src/curves.rs (the arguments of Fq::from_raw are canonical integers).
A_ISO = from_u64_limbs(
    [
        0xC515AD7242EAA6B1,
        0x9673928C7D01B212,
        0x81639C4D96F78773,
        0x267F9B2EE592271A,
    ]
)
B_ISO = 1265
Z_ISO = Q - 13
ROOT_OF_UNITY_Q = from_u64_limbs(
    [
        0xA70E2C1102B6D05F,
        0x9BB97EA3C106F049,
        0x9E5C4DFD492AE26E,
        0x2DE6A9B8746D3F58,
    ]
)
THETA = from_u64_limbs(
    [
        0x632CAE9872DF1B5D,
        0x38578CCADF03AC27,
        0x53C3808D9E2F2357,
        0x2B3483A1EE9A382F,
    ]
)
ISO_CONSTANTS = [
    from_u64_limbs(words)
    for words in [
        [0x43CD42C800000001, 0x0205DD51CFA0961A, 0x8E38E38E38E38E39, 0x38E38E38E38E38E3],
        [0x8B95C6AAF703BCC5, 0x216B8861EC72BD5D, 0xACECF10F5F7C09A2, 0x1D935247B4473D17],
        [0xAEAC67BBEB586A3D, 0xD59D03D23B39CB11, 0xED7EE4A9CDF78F8F, 0x18760C7F7A9AD20D],
        [0xFB539A6F0000002B, 0xE1C521A795AC8356, 0x1C71C71C71C71C71, 0x31C71C71C71C71C7],
        [0xB7284F7EAF21A2E9, 0xA3AD678129B604D3, 0x1454798A5B5C56B2, 0x0A2DE485568125D5],
        [0xF169C187D2533465, 0x30CD6D53DF49D235, 0x0C621DE8B91C242A, 0x14735171EE542778],
        [0x6BEF1642AAAAAAAB, 0x5601F4709A8ADCB3, 0xDA12F684BDA12F68, 0x12F684BDA12F684B],
        [0x8BEE58E5FB81DE63, 0x21D910AEFB03B31D, 0xD6767887AFBE04D1, 0x2EC9A923DA239E8B],
        [0x4986913AB4443034, 0x97A3CA5C24E9EA63, 0x66D1466E9DE10E64, 0x19B0D87E16E25788],
        [0x8F64842C55555533, 0x8BC32D36FB21A6A3, 0x425ED097B425ED09, 0x1ED097B425ED097B],
        [0x58DFECCE86B2745E, 0x06A767BFC35B5BAC, 0x9E7EB64F890A820C, 0x2F44D6C801C1B8BF],
        [0xD43D449776F99D2F, 0x926847FB9DDD76A1, 0x252659BA2B546C7E, 0x3D59F455CAFC7668],
        [0x8C46EB20FFFFFDE5, 0x224698FC0994A8DD, 0x0000000000000000, 0x4000000000000000],
    ]
]

# Concrete field-domain constants already certified in
# Orchard/compiled/{algebraic.v} and Halo2/plonkish/poly_domain.v.
OMEGA = 0x181B50AD5F32119E31CBD395426D600B7A9B88BCAAA1C24EEF28545AADA17813
DELTA = 0x0A757D0F0006AB6CBD455B7112A5049DF5E4F3F13EEE56366A6CCD20DD7B9BA2

Point = Optional[tuple[int, int]]


def inv(x: int, modulus: int) -> int:
    return pow(x % modulus, -1, modulus)


def is_square(x: int, modulus: int) -> bool:
    x %= modulus
    return x == 0 or pow(x, (modulus - 1) // 2, modulus) == 1


def tonelli_shanks(n: int, modulus: int) -> int:
    n %= modulus
    if n == 0:
        return 0
    if not is_square(n, modulus):
        raise ValueError("square root requested for a nonsquare")
    q = modulus - 1
    s = 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 5
    while is_square(z, modulus):
        z += 1
    m = s
    c = pow(z, q, modulus)
    t = pow(n, q, modulus)
    r = pow(n, (q + 1) // 2, modulus)
    while t != 1:
        t2 = t
        i = 0
        while t2 != 1:
            t2 = t2 * t2 % modulus
            i += 1
            if i == m:
                raise AssertionError("Tonelli-Shanks invariant failed")
        b = pow(c, 1 << (m - i - 1), modulus)
        m = i
        c = b * b % modulus
        t = t * c % modulus
        r = r * b % modulus
    return r


def curve_add(p1: Point, p2: Point) -> Point:
    """Complete affine addition on Vesta/iso-Vesta (a is supplied below)."""
    return curve_add_a(p1, p2, 0)


def curve_add_a(p1: Point, p2: Point, a: int) -> Point:
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if (x1 - x2) % Q == 0:
        if (y1 + y2) % Q == 0:
            return None
        slope = (3 * x1 * x1 + a) * inv(2 * y1, Q) % Q
    else:
        slope = (y2 - y1) * inv(x2 - x1, Q) % Q
    x3 = (slope * slope - x1 - x2) % Q
    y3 = (slope * (x1 - x3) - y1) % Q
    return x3, y3


def curve_mul(point: Point, scalar: int) -> Point:
    acc: Point = None
    base = point
    while scalar:
        if scalar & 1:
            acc = curve_add(acc, base)
        base = curve_add(base, base)
        scalar >>= 1
    return acc


def on_curve(point: Point, a: int = 0, b: int = 5) -> bool:
    if point is None:
        return True
    x, y = point
    return y * y % Q == (x * x % Q * x + a * x + b) % Q


def expand_message_xmd(message: bytes, dst: bytes) -> bytes:
    dst_prime = dst + bytes([len(dst)])
    h = lambda value: hashlib.blake2b(value, digest_size=64).digest()
    b0 = h(bytes(128) + message + bytes([0, 128, 0]) + dst_prime)
    b1 = h(b0 + b"\x01" + dst_prime)
    b2 = h(bytes(x ^ y for x, y in zip(b0, b1)) + b"\x02" + dst_prime)
    return b1 + b2


def hash_to_field_vesta(domain_prefix: str, message: bytes) -> tuple[int, int]:
    dst = domain_prefix.encode() + b"-vesta_XMD:BLAKE2b_SSWU_RO_"
    uniform = expand_message_xmd(message, dst)
    return int.from_bytes(uniform[:64], "big") % Q, int.from_bytes(uniform[64:], "big") % Q


def sswu_intermediates(u: int) -> tuple[int, int, int, int, int, int]:
    z_u2 = Z_ISO * u % Q * u % Q
    ta = (z_u2 * z_u2 + z_u2) % Q
    x1_num = B_ISO * (ta + 1) % Q
    x_div = A_ISO * (Z_ISO if ta == 0 else -ta) % Q
    x_div3 = x_div * x_div % Q * x_div % Q
    gx1_num = (
        (x1_num * x1_num + A_ISO * x_div % Q * x_div) % Q * x1_num
        + B_ISO * x_div3
    ) % Q
    x2_num = z_u2 * x1_num % Q
    return z_u2, x1_num, x_div, x_div3, gx1_num, x2_num


def sqrt_ratio_witness(num: int, den: int) -> tuple[bool, int]:
    ratio = num * inv(den, Q) % Q
    square = is_square(ratio, Q)
    radicand = ratio if square else ROOT_OF_UNITY_Q * ratio % Q
    root = tonelli_shanks(radicand, Q)
    expected = num if square else ROOT_OF_UNITY_Q * num % Q
    assert root * root % Q * den % Q == expected
    return square, root


def map_to_iso_vesta(u: int, witness: tuple[bool, int]) -> Point:
    square, root = witness
    z_u2, x1_num, x_div, _x_div3, _gx1_num, x2_num = sswu_intermediates(u)
    x_num = x1_num if square else x2_num
    y_prime = root if square else THETA * z_u2 % Q * u % Q * root % Q
    y = -y_prime % Q if (u & 1) != (y_prime & 1) else y_prime
    result = x_num * inv(x_div, Q) % Q, y
    assert on_curve(result, A_ISO, B_ISO)
    return result


def iso_map(point: Point) -> Point:
    if point is None:
        return None
    x, y = point
    c = ISO_CONSTANTS
    x_num = (((c[0] * x + c[1]) % Q * x + c[2]) % Q * x + c[3]) % Q
    x_den = ((x + c[4]) % Q * x + c[5]) % Q
    y_num = ((((c[6] * x + c[7]) % Q * x + c[8]) % Q * x + c[9]) % Q * y) % Q
    y_den = (((x + c[10]) % Q * x + c[11]) % Q * x + c[12]) % Q
    if x_den == 0 or y_den == 0:
        return None
    result = x_num * inv(x_den, Q) % Q, y_num * inv(y_den, Q) % Q
    assert on_curve(result)
    return result


def group_hash_vesta(message: bytes) -> tuple[Point, tuple[tuple[bool, int], tuple[bool, int]]]:
    us = hash_to_field_vesta("Halo2-Parameters", message)
    witnesses = tuple(
        sqrt_ratio_witness(sswu_intermediates(u)[4], sswu_intermediates(u)[3]) for u in us
    )
    q0 = map_to_iso_vesta(us[0], witnesses[0])
    q1 = map_to_iso_vesta(us[1], witnesses[1])
    point = iso_map(curve_add_a(q0, q1, A_ISO))
    assert point is not None and on_curve(point)
    return point, witnesses  # type: ignore[return-value]


def params_points() -> tuple[list[Point], Point, Point, list[object]]:
    points: list[Point] = []
    witness_rows: list[object] = []
    for i in range(N):
        message = b"\x00" + i.to_bytes(4, "little")
        point, witnesses = group_hash_vesta(message)
        points.append(point)
        witness_rows.append((point, witnesses))
    w, w_witness = group_hash_vesta(b"\x01")
    u, u_witness = group_hash_vesta(b"\x02")
    witness_rows.extend([(w, w_witness), (u, u_witness)])
    return points, w, u, witness_rows


def load_events() -> list[dict[str, object]]:
    path = ROOT / "Garden/Orchard/Snapshots/circuit_synthesis_generated_from_model.json"
    return json.loads(path.read_text())["events"]


def fixed_evaluations(events: list[dict[str, object]]) -> list[list[int]]:
    columns = [[0] * N for _ in range(14)]
    selector_rows: list[set[int]] = [set() for _ in range(56)]
    for event in events:
        tag = event["tag"]
        if tag == "AssignFixed":
            column = int(event["column"])
            row = int(event["row"])
            columns[column][row] = int(event["value"])
        elif tag == "FillFromRow":
            column = int(event["column"])
            from_row = int(event["from_row"])
            # Serialization fills lookup defaults through usable_rows=2042.
            columns[column][from_row:2042] = [int(event["value"])] * (2042 - from_row)
        elif tag == "EnableSelector":
            selector_rows[int(event["selector"])].add(int(event["row"]))

    compression_path = (
        ROOT / "Garden/Orchard/Snapshots/circuit_selector_compression_generated_from_implementation.json"
    )
    compression = json.loads(compression_path.read_text())
    for combination in compression["combinations"]:
        values = [0] * N
        for member in combination["members"]:
            selector = int(member["selector"])
            label = int(member["label"])
            for row in selector_rows[selector]:
                if values[row] != 0:
                    raise AssertionError(f"selector collision in combination {combination['index']} row {row}")
                values[row] = label
        assert int(combination["fixed_column"]["index"]) == len(columns)
        columns.append(values)
    assert len(columns) == 29 and all(len(column) == N for column in columns)
    return [[value % P for value in column] for column in columns]


PERMUTATION_COLUMNS = [
    ("Instance_", 0),
    *(("Advice", i) for i in range(10)),
    ("Fixed", 3),
    ("Fixed", 8),
    ("Fixed", 9),
    ("Fixed", 10),
]


def cell_of_json(value: dict[str, object]) -> tuple[int, int]:
    column = value["column"]
    assert isinstance(column, dict)
    key = str(column["kind"]), int(column["index"])
    try:
        position = PERMUTATION_COLUMNS.index(key)
    except ValueError as error:
        raise AssertionError(f"copy cell outside permutation columns: {key}") from error
    row = int(value["row"])
    if not 0 <= row < N:
        raise AssertionError(f"copy row outside domain: {row}")
    return position, row


def sigma_mapping(events: list[dict[str, object]]) -> list[list[tuple[int, int]]]:
    width = len(PERMUTATION_COLUMNS)
    mapping = [[(column, row) for row in range(N)] for column in range(width)]
    aux = [[(column, row) for row in range(N)] for column in range(width)]
    sizes = [[1] * N for _ in range(width)]

    def get(matrix: list[list[object]], cell: tuple[int, int]):
        return matrix[cell[0]][cell[1]]

    def set_(matrix: list[list[object]], cell: tuple[int, int], value: object) -> None:
        matrix[cell[0]][cell[1]] = value

    for event in events:
        if event["tag"] != "Copy":
            continue
        left = cell_of_json(event["left"])  # type: ignore[arg-type]
        right = cell_of_json(event["right"])  # type: ignore[arg-type]
        left_cycle = get(aux, left)
        right_cycle = get(aux, right)
        assert isinstance(left_cycle, tuple) and isinstance(right_cycle, tuple)
        if left_cycle == right_cycle:
            continue
        if get(sizes, left_cycle) < get(sizes, right_cycle):
            left_cycle, right_cycle = right_cycle, left_cycle
        set_(sizes, left_cycle, int(get(sizes, left_cycle)) + int(get(sizes, right_cycle)))

        cursor = right_cycle
        while True:
            set_(aux, cursor, left_cycle)
            next_cell = get(mapping, cursor)
            assert isinstance(next_cell, tuple)
            if next_cell == right_cycle:
                break
            cursor = next_cell

        left_image = get(mapping, left)
        right_image = get(mapping, right)
        set_(mapping, left, right_image)
        set_(mapping, right, left_image)

    return mapping  # type: ignore[return-value]


def permutation_evaluations(events: list[dict[str, object]]) -> list[list[int]]:
    mapping = sigma_mapping(events)
    omega_powers = [pow(OMEGA, row, P) for row in range(N)]
    delta_powers = [pow(DELTA, column, P) for column in range(len(mapping))]
    return [
        [delta_powers[target_column] * omega_powers[target_row] % P for target_column, target_row in column]
        for column in mapping
    ]


def bit_reverse_permute(values: list[int]) -> None:
    n = len(values)
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            values[i], values[j] = values[j], values[i]


def ifft(evaluations: list[int]) -> list[int]:
    values = [value % P for value in evaluations]
    bit_reverse_permute(values)
    omega_inv = pow(OMEGA, -1, P)
    length = 2
    while length <= N:
        root = pow(omega_inv, N // length, P)
        for base in range(0, N, length):
            twiddle = 1
            half = length // 2
            for offset in range(half):
                even = values[base + offset]
                odd = values[base + offset + half] * twiddle % P
                values[base + offset] = (even + odd) % P
                values[base + offset + half] = (even - odd) % P
                twiddle = twiddle * root % P
        length *= 2
    n_inv = pow(N, -1, P)
    return [value * n_inv % P for value in values]


def pippenger(scalars: list[int], points: list[Point], width: int = 8) -> Point:
    if len(scalars) != len(points):
        raise ValueError("MSM input length mismatch")
    windows = (255 + width - 1) // width
    window_sums: list[Point] = []
    mask = (1 << width) - 1
    for window in range(windows):
        buckets: list[Point] = [None] * mask
        shift = window * width
        for scalar, point in zip(scalars, points):
            digit = (scalar >> shift) & mask
            if digit:
                buckets[digit - 1] = curve_add(buckets[digit - 1], point)
        running: Point = None
        total: Point = None
        for bucket in reversed(buckets):
            running = curve_add(running, bucket)
            total = curve_add(total, running)
        window_sums.append(total)
    acc: Point = None
    for window_sum in reversed(window_sums):
        for _ in range(width):
            acc = curve_add(acc, acc)
        acc = curve_add(acc, window_sum)
    return acc


def pinned_commitments() -> list[Point]:
    source = (ROOT / "Garden/Orchard/vk/data.v").read_text()
    start = source.index("Definition fixed_commitments")
    end = source.index("End VkPinnedData")
    pairs = re.findall(r"\(0x([0-9a-f]+),\s*0x([0-9a-f]+)\)", source[start:end], re.I)
    result: list[Point] = [(int(x, 16), int(y, 16)) for x, y in pairs]
    if len(result) != 44:
        raise AssertionError(f"expected 44 pinned commitments, found {len(result)}")
    return result


def verify_all() -> dict[str, object]:
    events = load_events()
    fixed = fixed_evaluations(events)
    permutation = permutation_evaluations(events)
    evaluations = fixed + permutation
    assert len(evaluations) == 44

    bases, w, u, _witnesses = params_points()
    expected = pinned_commitments()
    mismatches: list[dict[str, object]] = []
    coefficients: list[list[int]] = []
    for index, (column, wanted) in enumerate(zip(evaluations, expected)):
        coeffs = ifft(column)
        coefficients.append(coeffs)
        derived = curve_add(pippenger(coeffs, bases), w)
        if derived != wanted:
            mismatches.append(
                {
                    "kind": "fixed" if index < 29 else "permutation",
                    "index": index if index < 29 else index - 29,
                    "expected": wanted,
                    "derived": derived,
                }
            )
        print(f"[{index + 1:02d}/44] {'ok' if derived == wanted else 'MISMATCH'}", file=sys.stderr)
    if mismatches:
        raise AssertionError(json.dumps(mismatches, indent=2))
    return {
        "schema": "garden.orchard.vk-provenance.summary.v1",
        "k": K,
        "n": N,
        "fixed_commitments": 29,
        "permutation_commitments": 15,
        "params": {
            "g_count": len(bases),
            "w": w,
            "u": u,
        },
        "all_commitments_match": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="recompute all 44 commitments")
    args = parser.parse_args()
    if not args.verify:
        parser.error("the checked core currently exposes --verify")
    print(json.dumps(verify_all(), indent=2))


if __name__ == "__main__":
    main()
