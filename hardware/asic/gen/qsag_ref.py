#!/usr/bin/env python3
"""Bit-exact Python reference for the QSAG-NI primitives and verifier protocols.

Transcribed from the Rust definitions (crates/qsag-accel/src/poseidon2.rs,
crates/qsag-agg/src/field.rs, crates/qsag-agg/src/sponge.rs,
crates/qsag-agg/src/pcs.rs, crates/qsag-agg/src/recursive_fold.rs,
crates/qsag-asm/src/portable.rs). `selfcheck(fixture)` compares every primitive
against validation/tests/fixtures/lean_external_oracle_vectors.json and hashlib.
"""
import hashlib
import json
import sys

P = 2**64 - 2**32 + 1
EPS = 2**32 - 1
M64 = 2**64 - 1

# ---------------------------------------------------------------- Goldilocks


def gl(x):
    return x % P


def gl_add(a, b):
    return (a + b) % P


def gl_sub(a, b):
    return (a - b) % P


def gl_mul(a, b):
    return (a * b) % P


def gl_pow7(x):
    x2 = gl_mul(x, x)
    x3 = gl_mul(x2, x)
    x6 = gl_mul(x3, x3)
    return gl_mul(x6, x)


# ---------------------------------------------------------------- Ext4
# Limb order [c0.c0, c0.c1, c1.c0, c1.c1] = coefficients of [v^0, v^2, v^1, v^3]
# in F_p[v]/(v^4 - 7), i.e. tower basis [1, u, v, u*v] with v^2 = u, u^2 = 7.
LIMB_TO_POLY = [0, 2, 1, 3]  # poly index k -> limb index


def ext4_muladd(x, y, z=(0, 0, 0, 0)):
    a = [x[LIMB_TO_POLY[k]] % P for k in range(4)]
    b = [y[LIMB_TO_POLY[k]] % P for k in range(4)]
    c = [z[LIMB_TO_POLY[k]] % P for k in range(4)]
    out = [0] * 4
    for k in range(4):
        acc = c[k]
        for i in range(4):
            if i <= k:
                acc += a[i] * b[k - i]
            else:
                acc += 7 * a[i] * b[k + 4 - i]
        out[k] = acc % P
    return [out[0], out[2], out[1], out[3]]


def ext4_karatsuba_muladd(x, y, z=(0, 0, 0, 0)):
    """Tower Karatsuba 9-product Ext4 multiply-add matching qsag_ext4_kara_*."""
    a = [v % P for v in x]
    b = [v % P for v in y]
    c = [v % P for v in z]
    groups = [[0], [1], [0, 1], [2], [3], [2, 3], [0, 2], [1, 3], [0, 1, 2, 3]]
    qa = [sum(a[i] for i in g) % P for g in groups]
    qb = [sum(b[i] for i in g) % P for g in groups]
    pr = [(qa[m] * qb[m]) % P for m in range(9)]
    weights = [
        [1, 7, 0, -7, -7, 7, 0, 0, 0],
        [-1, -1, 1, 1, 7, 0, 0, 0, 0],
        [-1, -7, 0, -1, -7, 0, 1, 7, 0],
        [1, 1, -1, 1, 1, -1, -1, -1, 1],
    ]
    return [(c[j] + sum(w * pr[i] for i, w in enumerate(row))) % P for j, row in enumerate(weights)]


def ext4_add(x, y):
    return [gl_add(a, b) for a, b in zip(x, y)]


def ext4_sub(x, y):
    return [gl_sub(a, b) for a, b in zip(x, y)]


def ext4_mul_base(x, s):
    s %= P
    return [(a * s) % P for a in x]


def ext4_eval_poly(coeffs, r):
    """Horner evaluation c_0 + c_1*r + ... + c_d*r^d."""
    acc = [0, 0, 0, 0]
    for c in reversed(coeffs):
        acc = ext4_muladd(acc, r, c)
    return acc


# ---------------------------------------------------------------- [CWYZ26] DuetFold
def cwyz_duet_step(v0, v1, theta, alpha, beta, inv_two, inv_two_x, x_sq):
    even = ext4_mul_base(ext4_add(v0, v1), inv_two)
    odd = ext4_mul_base(ext4_sub(v0, v1), inv_two_x)
    mixed = ext4_add(even, ext4_muladd(theta, odd))
    gamma = ext4_add(alpha, ext4_mul_base(beta, x_sq))
    return ext4_add(odd, ext4_muladd(gamma, mixed))


# ---------------------------------------------------------------- Poseidon2-12
P2_IV = 0x504F53325F474C31
P2_DOMAIN_CANOPY_SALT = 0x5032434E534C5401
P2_DOMAIN_CANOPY_LEAF_R0 = 0x5032434E4C463001
P2_DOMAIN_CANOPY_LEAF_BATCH = 0x5032434E4C464201
P2_DOMAIN_CANOPY_LEAF_EXT4 = 0x5032434E4C464501
P2_CANOPY_NODE_HI = 0x50324E4400000000
P2_DOMAIN_CANOPY_ROOT = 0x5032434E524F4F54


def _rc_bij(x):
    z0 = (x + 0x9E3779B97F4A7C15) & M64
    z1 = ((z0 ^ (z0 >> 30)) * 0xBF58476D1CE4E5B9) & M64
    z2 = ((z1 ^ (z1 >> 27)) * 0x94D049BB133111EB) & M64
    return z2 ^ (z2 >> 31)


def p2_rc(tag, rnd, lane):
    return _rc_bij(_rc_bij(_rc_bij(P2_IV ^ tag) ^ rnd) ^ lane) % P


def _m4(b):
    s = (b[0] + b[1] + b[2] + b[3]) % P
    return [
        (s + b[0] + 2 * b[1]) % P,
        (s + b[1] + 2 * b[2]) % P,
        (s + b[2] + 2 * b[3]) % P,
        (s + b[3] + 2 * b[0]) % P,
    ]


def p2_me(st):
    st = [x % P for x in st]
    st = [st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11]]
    y = [_m4(st[0:4]), _m4(st[4:8]), _m4(st[8:12])]
    o = [0] * 12
    for i in range(4):
        s = (y[0][i] + y[1][i] + y[2][i]) % P
        for blk in range(3):
            o[4 * blk + i] = (y[blk][i] + s) % P
    return [o[0], o[4], o[8], o[1], o[5], o[9], o[2], o[6], o[10], o[3], o[7], o[11]]


P2_MI_DIAG = [P - 64] + [1 << i for i in range(11)]


def p2_mi(st):
    s = sum(st) % P
    return [(P2_MI_DIAG[i] * st[i] + s) % P for i in range(12)]


def p2_me_matrix():
    cols = [p2_me([1 if j == i else 0 for j in range(12)]) for i in range(12)]
    return [[cols[j][i] for j in range(12)] for i in range(12)]


def p2_perm(st):
    st = p2_me(st)
    for r in range(4):
        st = p2_me([gl_pow7(gl_add(x, p2_rc(0, r, l))) for l, x in enumerate(st)])
    for r in range(22):
        st = list(st)
        st[0] = gl_pow7(gl_add(st[0], p2_rc(1, r, 0)))
        st = p2_mi(st)
    for r in range(4):
        st = p2_me([gl_pow7(gl_add(x, p2_rc(2, r, l))) for l, x in enumerate(st)])
    return st


def p2_sponge_limbs(domain_tag, init_cap, limbs):
    st = [0] * 8 + [c % P for c in init_cap]
    stream = [domain_tag % P, len(limbs) % P] + [v % P for v in limbs]
    for off in range(0, len(stream), 8):
        blk = stream[off:off + 8]
        for i, v in enumerate(blk):
            st[i] = (st[i] + v) % P
        st = p2_perm(st)
    return st[:4]


def p2_canopy_tree_key(stage_idx, log_leaves, tree_salt=(0, 0, 0, 0)):
    return p2_sponge_limbs(P2_DOMAIN_CANOPY_SALT, tree_salt, [stage_idx, log_leaves])


def p2_canopy_node(left, right, key3, node_idx):
    l = [x % P for x in left]
    r = [x % P for x in right]
    t0 = (P2_CANOPY_NODE_HI | (node_idx & 0xFFFFFFFF)) % P
    c = [t0] + [k % P for k in key3[:3]]
    st = p2_perm(l + r + c)
    return [(st[i] + l[i] + 2 * r[i] + 4 * c[i]) % P for i in range(4)]


def p2_canopy_root(stage_idx, log_leaves, top_limbs, tree_salt=(0, 0, 0, 0)):
    return p2_sponge_limbs(P2_DOMAIN_CANOPY_ROOT, tree_salt, [stage_idx, log_leaves] + list(top_limbs))


def p2_round0_leaf(leaf_idx, salt16, num_polys, vals):
    arity = len(vals) // num_polys
    salt_limbs = []
    for off in (0, 7, 14):
        chunk = salt16[off:min(off + 7, 16)]
        salt_limbs.append(int.from_bytes(chunk + b"\x00" * (8 - len(chunk)), "little"))
    dom = P2_DOMAIN_CANOPY_LEAF_R0 if num_polys == 1 else P2_DOMAIN_CANOPY_LEAF_BATCH
    return p2_sponge_limbs(dom, [leaf_idx, arity, num_polys, 0], salt_limbs + list(vals))


def p2_ext4_leaf(stage_idx, leaf_idx, ext4_vals):
    flat = [w for e in ext4_vals for w in e]
    return p2_sponge_limbs(P2_DOMAIN_CANOPY_LEAF_EXT4, [leaf_idx, len(ext4_vals), stage_idx, 0], flat)


def p2_merkle_2block(left, right, pk_seed, dom, meta0, tree_lo, tree_hi):
    st = [x % P for x in pk_seed] + [x % P for x in left] + [dom % P, meta0 % P, tree_lo % P, tree_hi % P]
    st = p2_perm(st)
    for i in range(4):
        st[i] = gl_add(st[i], right[i] % P)
    st[4] = gl_add(st[4], 1)
    st[5] = gl_add(st[5], P2_IV % P)
    return p2_perm(st)[:4]


def p2_canopy_path(leaf, siblings, key3, leaf_index):
    """Root of a depth-len(siblings) Canopy path; heap node index of the leaf is 2^D + leaf_index."""
    depth = len(siblings)
    idx = (1 << depth) | leaf_index
    cur = list(leaf)
    for sib in siblings:
        parent = idx >> 1
        if idx & 1:
            cur = p2_canopy_node(sib, cur, key3, parent)
        else:
            cur = p2_canopy_node(cur, sib, key3, parent)
        idx = parent
    return cur


# ---------------------------------------------------------------- Keccak & TurboSHAKE Canopy
KECCAK_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
KECCAK_ROT = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
]  # [x][y]

TAG_MERKLE_INTERNAL = 0x00
TAG_MERKLE_ROOT = 0x01
TAG_ROUND0_SALT = 0x02
TAG_ROUND0_SINGLE = 0x10
TAG_ROUND0_BATCH = 0x11
TAG_EXT4_STAGE_LEAF = 0x12


def _rol(v, n):
    n %= 64
    return ((v << n) | (v >> (64 - n))) & M64 if n else v


def keccak_round(a, rc):
    c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
    d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
    a = [a[i] ^ d[i % 5] for i in range(25)]
    b = [0] * 25
    for x in range(5):
        for y in range(5):
            b[y + 5 * ((2 * x + 3 * y) % 5)] = _rol(a[x + 5 * y], KECCAK_ROT[x][y])
    o = [b[i] ^ ((~b[(i % 5 + 1) % 5 + 5 * (i // 5)]) & b[(i % 5 + 2) % 5 + 5 * (i // 5)] & M64) for i in range(25)]
    o[0] ^= rc
    return o


def keccak_p(a, rounds=24):
    a = list(a)
    for r in range(24 - rounds, 24):
        a = keccak_round(a, KECCAK_RC[r])
    return a


def _sponge(msg, rate, suffix, outlen, rounds, state=None):
    st = list(state) if state else [0] * 25
    msg = bytes(msg)
    full = len(msg) // rate
    for i in range(full):
        blk = msg[i * rate:(i + 1) * rate]
        for l in range(rate // 8):
            st[l] ^= int.from_bytes(blk[8 * l:8 * l + 8], "little")
        st = keccak_p(st, rounds)
    blk = bytearray(rate)
    rem = msg[full * rate:]
    blk[:len(rem)] = rem
    blk[len(rem)] ^= suffix
    blk[rate - 1] ^= 0x80
    for l in range(rate // 8):
        st[l] ^= int.from_bytes(blk[8 * l:8 * l + 8], "little")
    st = keccak_p(st, rounds)
    out = b""
    while len(out) < outlen:
        out += b"".join(st[l].to_bytes(8, "little") for l in range(rate // 8))
        if len(out) < outlen:
            st = keccak_p(st, rounds)
    return out[:outlen]


def shake256(msg, outlen):
    return _sponge(msg, 136, 0x1F, outlen, 24)


def sha3_256(msg):
    return _sponge(msg, 136, 0x06, 32, 24)


def turboshake256(msg, outlen, suffix=0x07, state=None):
    return _sponge(msg, 136, suffix, outlen, 12, state)


def turboshake256_midstate(custom):
    blk = bytearray(136)
    blk[0:4] = bytes([1, 136, 1, 0])
    bit_len = len(custom) * 8
    if bit_len < 256:
        blk[4:6] = bytes([1, bit_len])
        p = 6
    else:
        blk[4:7] = bytes([2, bit_len >> 8, bit_len & 0xFF])
        p = 7
    blk[p:p + len(custom)] = custom
    st = [0] * 25
    for l in range(17):
        st[l] = int.from_bytes(blk[8 * l:8 * l + 8], "little")
    return keccak_p(st, 12)


TURBOSHAKE_CANOPY_CUSTOM = b"QSAG.PCS.TURBOCANOPY/v1"
_TS_MID = None


def ts_canopy_32(payload):
    global _TS_MID
    if _TS_MID is None:
        _TS_MID = turboshake256_midstate(TURBOSHAKE_CANOPY_CUSTOM)
    return turboshake256(payload, 32, 0x07, _TS_MID)


def ts_canopy_internal(node_idx, left32, right32):
    return ts_canopy_32(bytes([TAG_MERKLE_INTERNAL]) + node_idx.to_bytes(4, "little") + bytes(left32) + bytes(right32))


def ts_canopy_root(log_leaves, top32):
    return ts_canopy_32(bytes([TAG_MERKLE_ROOT, log_leaves]) + bytes(top32))


def ts_round0_leaf(leaf_idx, salt16, num_polys, vals):
    arity = len(vals) // num_polys
    body = b"".join(v.to_bytes(8, "little") for v in vals)
    if num_polys == 1:
        hdr = bytes([TAG_ROUND0_SINGLE, arity]) + leaf_idx.to_bytes(4, "little") + bytes(salt16)
    else:
        hdr = bytes([TAG_ROUND0_BATCH, arity, num_polys]) + leaf_idx.to_bytes(4, "little") + bytes(salt16)
    return ts_canopy_32(hdr + body)


def ts_ext4_leaf(stage_idx, leaf_idx, ext4_vals):
    hdr = bytes([TAG_EXT4_STAGE_LEAF, stage_idx, len(ext4_vals)]) + leaf_idx.to_bytes(4, "little")
    body = b"".join(w.to_bytes(8, "little") for e in ext4_vals for w in e)
    return ts_canopy_32(hdr + body)


# ---------------------------------------------------------------- GF(2^128)
M128 = 2**128 - 1


def clmul(a, b):
    r = 0
    i = 0
    while b >> i:
        if (b >> i) & 1:
            r ^= a << i
        i += 1
    return r


def gf128_reduce(x):
    """mod z^128 + z^7 + z^2 + z + 1"""
    for i in range(x.bit_length() - 1, 127, -1):
        if (x >> i) & 1:
            x ^= (0x87 | (1 << 128)) << (i - 128)
    return x


def gf128_mul(a, b):
    return gf128_reduce(clmul(a, b))


TOWER_GENS = [
    0x295AC0B1F4731AF9676AAC9FA4B20B08,
    0x500317BD159D73BB34D2F7FBA603E341,
    0x872430DCDF135BCC433F53640B5AB39A,
    0x08EE6D05A2AFA6E5F848729A9637483A,
    0x6167C15AE3F2515951C65CFFFDD09B94,
    0x11BF2AE00EEFB7458F1990F8FFD4B9BC,
    0x8845A6B78C9FFFC36A2A74600CFA98DE,
]


def tower_basis():
    """(T7->poly columns, poly->T7 columns), as build_tower128_basis_pair."""
    t7 = []
    for m in range(128):
        prod = 1
        for bit in range(7):
            if (m >> bit) & 1:
                prod = gf128_mul(prod, TOWER_GENS[bit])
        t7.append(prod)
    lhs = [sum(((t7[c] >> r) & 1) << c for c in range(128)) for r in range(128)]
    rhs = [1 << r for r in range(128)]
    for col in range(128):
        piv = next(r for r in range(col, 128) if (lhs[r] >> col) & 1)
        lhs[col], lhs[piv] = lhs[piv], lhs[col]
        rhs[col], rhs[piv] = rhs[piv], rhs[col]
        for row in range(128):
            if row != col and (lhs[row] >> col) & 1:
                lhs[row] ^= lhs[col]
                rhs[row] ^= rhs[col]
    poly = [0] * 128
    for out_bit in range(128):
        for in_bit in range(128):
            if (rhs[out_bit] >> in_bit) & 1:
                poly[in_bit] |= 1 << out_bit
    return t7, poly


_TB = None


def _lin(cols, x):
    r = 0
    for i in range(128):
        if (x >> i) & 1:
            r ^= cols[i]
    return r


def tower_to_poly(x):
    global _TB
    _TB = _TB or tower_basis()
    return _lin(_TB[0], x)


def poly_to_tower(x):
    global _TB
    _TB = _TB or tower_basis()
    return _lin(_TB[1], x)


def tower128_mul(a, b):
    return poly_to_tower(gf128_mul(tower_to_poly(a), tower_to_poly(b)))


# ---------------------------------------------------------------- self-check


def selfcheck(fixture_path):
    fx = json.load(open(fixture_path))
    n = 0
    for e in fx["goldilocks_edges"]:
        a, b = int(e["a_raw"]), int(e["b_raw"])
        assert gl(a) == int(e["a_canon"]) and gl_add(a, b) == int(e["add"])
        assert gl_sub(a, b) == int(e["sub"]) and gl_mul(a, b) == int(e["mul"])
        assert gl_pow7(a % P) == int(e["pow7_a"])
        n += 1
    for e in fx["goldilocks_ext4"]:
        x = [int(v) for v in e["x"]]
        y = [int(v) for v in e["y"]]
        assert ext4_muladd(x, y) == [int(v) for v in e["mul"]]
        assert ext4_karatsuba_muladd(x, y) == [int(v) for v in e["mul"]]
        n += 1
    for e in fx["poseidon2_12"]:
        assert p2_perm([int(v) for v in e["input"]]) == [int(v) for v in e["perm"]]
        n += 1
    for e in fx["sponges"]:
        m = bytes.fromhex(e["msg_hex"])
        assert sha3_256(m).hex() == e["sha3_256_hex"]
        assert shake256(m, 64).hex() == e["shake256_64_hex"]
        assert shake256(m, 64) == hashlib.shake_256(m).digest(64)
        n += 1
    for e in fx["tower128"]:
        a = int.from_bytes(bytes.fromhex(e["a_le_hex"]), "little")
        b = int.from_bytes(bytes.fromhex(e["b_le_hex"]), "little")
        assert tower128_mul(a, b).to_bytes(16, "little").hex() == e["mul_le_hex"]
        n += 1
    # RFC 9861 TurboSHAKE256(M = empty, D = 0x1F), first 8 output bytes.
    assert turboshake256(b"", 64, 0x1F).hex().startswith("367a329dafea871c"), turboshake256(b"", 64, 0x1F).hex()
    # Artin-Schreier relations of the tower generators (as the Rust const assert).
    for k in range(7):
        xk = 1 if k == 0 else TOWER_GENS[k - 1]
        g = TOWER_GENS[k]
        assert gf128_mul(g, g) ^ gf128_mul(xk, g) == 1
    return n


if __name__ == "__main__":
    print("selfcheck vectors OK:", selfcheck(sys.argv[1]))
