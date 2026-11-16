#!/usr/bin/env python3
"""Vectors for the datapath unit test (tb/unit_dp.cpp), from the reference model and the
qsag Lean oracle fixture. Usage: gen_dp_vectors.py <fixture.json> <out.txt>"""
import json
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "model"))
import qsag_prims as q  # noqa: E402

P = q.P
rng = random.Random(0x51A6)
fx = json.load(open(sys.argv[1]))
print("model selfcheck:", q.selfcheck(sys.argv[1]))
lines = []


def emit(tag, *words):
    lines.append(tag + " " + " ".join(f"{w:016x}" for w in words))


EDGE = [0, 1, 2, P - 1, P - 2, 2**32 - 1, 2**32, 2**32 + 1, P - 2**32, 0xFFFFFFFF00000000, 7, 2**63]


def rnd_limb():
    r = rng.random()
    if r < 0.25:
        return rng.choice(EDGE)
    return rng.randrange(P)


def rnd_e4():
    return [rnd_limb() for _ in range(4)]


# base multiply through EMUL with embedded base elements (canonical operands)
pairs = [(int(e["a_canon"]), int(e["b_canon"]), int(e["mul"])) for e in fx["goldilocks_edges"]]
pairs += [(a, b, a * b % P) for a in EDGE for b in EDGE if a < P and b < P]
for a, b, r in pairs:
    emit("E", a, 0, 0, 0, b, 0, 0, 0, r, 0, 0, 0)
for e in fx["goldilocks_ext4"]:
    emit("E", *[int(v) for v in e["x"]], *[int(v) for v in e["y"]], *[int(v) for v in e["mul"]])
for _ in range(60):
    x, y = rnd_e4(), rnd_e4()
    emit("E", *x, *y, *q.ext4_mul(x, y))
    emit("+", *x, *y, *q.ext4_add(x, y))
    emit("-", *x, *y, *q.ext4_sub(x, y))
    emit("=", *x, *y, int(x == y))
    emit("=", *x, *x, 1)
# non-canonical words entering through SETW / ABSW
for e in fx["goldilocks_edges"]:
    a, b = int(e["a_raw"]), int(e["b_raw"])
    emit("S", a, int(e["a_canon"]))
    emit("A", a % P, b, int(e["add"]))
for _ in range(40):
    a, b = rng.randrange(P), rng.randrange(2**64)
    emit("S", b, b % P)
    emit("A", a, b, (a + b) % P)
for e in fx["poseidon2_12"]:
    emit("P", *[int(v) for v in e["input"]], *[int(v) for v in e["perm"]])
for _ in range(6):
    st = [rnd_limb() for _ in range(12)]
    emit("P", *st, *q.p2_perm(st))
# Canopy feed-forward: X <- st[0..3] + L + 2R + 4C
for _ in range(30):
    st, x, y, key = rnd_e4(), rnd_e4(), rnd_e4(), rnd_e4()[:3]
    t0 = (q.P2_DOMAIN_CANOPY_NODE_HI | rng.randrange(2**32)) % P
    d = rng.randrange(2)
    l, r = (y, x) if d else (x, y)
    c = [t0] + key
    emit("F", d, t0, *st, *x, *y, *key, *[(st[i] + l[i] + 2 * r[i] + 4 * c[i]) % P for i in range(4)])
# Keccak-f[1600] and Keccak-p[1600, 12]
for rounds in (24, 12, 24, 12):
    st = [rng.randrange(2**64) for _ in range(25)]
    emit("K", rounds, *st, *q.keccak_p(st, rounds))
emit("K", 24, *([0] * 25), *q.keccak_p([0] * 25, 24))
open(sys.argv[2], "w").write("\n".join(lines) + "\n")
print("wrote", len(lines), "vectors")
