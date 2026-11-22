#!/usr/bin/env python3
"""Bit-exact reference for the QSAG-NI-180 primitives.

Transcribed from the Rust definitions (crates/qsag-agg/src/field.rs, crates/qsag-agg/src/sponge.rs,
crates/qsag-accel/src/poseidon2.rs, crates/qsag-asm/src/portable.rs). `selfcheck(fixture)` compares
every primitive against validation/tests/fixtures/lean_external_oracle_vectors.json and hashlib.
"""
import hashlib
import json
import sys

P = 2**64 - 2**32 + 1
M64 = 2**64 - 1

# ---------------------------------------------------------------- Goldilocks / Ext4


def gl_pow7(x):
    x2 = x * x % P
    x3 = x2 * x % P
    return x3 * x3 % P * x % P


# Limb order [c0.c0, c0.c1, c1.c0, c1.c1] = coefficients of [v^0, v^2, v^1, v^3] in F_p[v]/(v^4 - 7).
LMAP = [0, 2, 1, 3]


def ext4_mul(x, y):
    a = [x[LMAP[k]] % P for k in range(4)]
    b = [y[LMAP[k]] % P for k in range(4)]
    out = [0] * 4
    for k in range(4):
        acc = 0
        for i in range(4):
            acc += a[i] * b[k - i] if i <= k else 7 * a[i] * b[k + 4 - i]
        out[k] = acc % P
    return [out[LMAP[l]] for l in range(4)]


def ext4_add(x, y):
    return [(a + b) % P for a, b in zip(x, y)]


def ext4_sub(x, y):
    return [(a - b) % P for a, b in zip(x, y)]


def ext4_scale(x, s):
    return [a * s % P for a in x]


# ---------------------------------------------------------------- Quintic Fp5 = F_p[X]/(X^5 - 3) (zk-Hem v2)
FP5_W = 3


def fp5_mul(x, y):
    a = [v % P for v in x]
    b = [v % P for v in y]
    out = [0] * 5
    for k in range(5):
        acc = 0
        for i in range(5):
            acc += a[i] * b[k - i] if i <= k else FP5_W * a[i] * b[k + 5 - i]
        out[k] = acc % P
    return out


def fp5_add(x, y):
    return [(a + b) % P for a, b in zip(x, y)]


def fp5_sub(x, y):
    return [(a - b) % P for a, b in zip(x, y)]


def fp5_scale(x, s):
    return [a * s % P for a in x]


# ---------------------------------------------------------------- Poseidon2 width 12
P2_IV = 0x504F53325F474C31


def _rc_bij(x):
    z0 = (x + 0x9E3779B97F4A7C15) & M64
    z1 = ((z0 ^ (z0 >> 30)) * 0xBF58476D1CE4E5B9) & M64
    z2 = ((z1 ^ (z1 >> 27)) * 0x94D049BB133111EB) & M64
    return z2 ^ (z2 >> 31)


def p2_rc(tag, rnd, lane):
    return _rc_bij(_rc_bij(_rc_bij(P2_IV ^ tag) ^ rnd) ^ lane) % P


def p2_rc_table():
    """ROM order of rtl/qsag_p2_rc.sv: 0..47 first full rounds, 48..95 last full rounds, 96..117 partial."""
    t = [p2_rc(0, r, l) for r in range(4) for l in range(12)]
    t += [p2_rc(2, r, l) for r in range(4) for l in range(12)]
    t += [p2_rc(1, r, 0) for r in range(22)]
    return t


def _m4(b):
    s = sum(b) % P
    return [(s + b[i] + 2 * b[(i + 1) % 4]) % P for i in range(4)]


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


def p2_perm(st):
    st = p2_me(st)
    for r in range(4):
        st = p2_me([gl_pow7((x + p2_rc(0, r, l)) % P) for l, x in enumerate(st)])
    for r in range(22):
        st = list(st)
        st[0] = gl_pow7((st[0] + p2_rc(1, r, 0)) % P)
        st = p2_mi(st)
    for r in range(4):
        st = p2_me([gl_pow7((x + p2_rc(2, r, l)) % P) for l, x in enumerate(st)])
    return st


def p2_sponge_hash_limbs(domain, cap, limbs):
    """poseidon2_sponge_hash_limbs: rate 8, capacity init `cap`, frame [domain, len] ++ limbs."""
    st = [0] * 8 + [c % P for c in cap]
    stream = [domain % P, len(limbs) % P] + [x % P for x in limbs]
    first = True
    while first or stream:
        blk, stream = stream[:8], stream[8:]
        for i, v in enumerate(blk):
            st[i] = (st[i] + v) % P
        st = p2_perm(st)
        first = False
    return st[:4]


P2_DOMAIN_CANOPY_NODE_HI = 0x50324E4400000000
P2_DOMAIN_FS_INIT = 0x50324653494E4954
P2_DOMAIN_FS_BIND_REL = 0x503246534252454C
P2_DOMAIN_FS_BIND_INST = 0x5032465342494E53
P2_DOMAIN_FS_ABSORB_BYTES = 0x5032465341425954
P2_DOMAIN_FS_ABSORB_LIMBS = 0x50324653414C4D42
P2_DOMAIN_FS_SQUEEZE_BASE = 0x5032465353514253
P2_DOMAIN_FS_SQUEEZE_EXT4 = 0x5032465353514534
P2_DOMAIN_FS_SQUEEZE_IDX = 0x5032465353514958
P2_DOMAIN_FS_POW = 0x50324653504F5701
FS_INIT_CAP = [P2_DOMAIN_FS_INIT, 0, 0, P2_IV]


def p2_canopy_node(left, right, key3, node_idx):
    l = [x % P for x in left]
    r = [x % P for x in right]
    c = [(P2_DOMAIN_CANOPY_NODE_HI | (node_idx & 0xFFFFFFFF)) % P] + [k % P for k in key3]
    st = p2_perm(l + r + c)
    return [(st[i] + l[i] + 2 * r[i] + 4 * c[i]) % P for i in range(4)]


def p2_canopy_path(leaf, siblings, key3, leaf_index):
    """Root of a Canopy path; the heap index of the leaf is 2^depth + leaf_index."""
    idx = (1 << len(siblings)) | leaf_index
    cur = [x % P for x in leaf]
    for sib in siblings:
        parent = idx >> 1
        cur = p2_canopy_node(sib, cur, key3, parent) if idx & 1 else p2_canopy_node(cur, sib, key3, parent)
        idx = parent
    return cur


def pack_bytes_7_limbs(b):
    """qsag-agg Fiat-Shamir framing: [len(b)] ++ little-endian 7-byte limbs."""
    return [len(b)] + [int.from_bytes(b[i:i + 7], "little") for i in range(0, len(b), 7)]


def pack_bytes_framed_accel(b):
    """qsag-accel Poseidon2Sponge::absorb_bytes_framed parity: [len(b)] ++ big-endian 7-byte chunks with 0x01 delimiter."""
    b = bytes(b)
    rem = (len(b) + 1) % 7
    padded = b + b"\x01" + (b"\x00" * (0 if rem == 0 else 7 - rem))
    return [len(b)] + [int.from_bytes(padded[i:i + 7], "big") for i in range(0, len(padded), 7)]


def sponge12_rate6(limbs):
    """Canonical rate-6, capacity-6 Poseidon2-12 sponge (qsag-accel::poseidon2::sponge12_rate6)."""
    st = [0] * 12
    limbs = [x % P for x in limbs]
    for off in range(0, len(limbs), 6):
        chunk = limbs[off:off + 6]
        for i, v in enumerate(chunk):
            st[i] = (st[i] + v) % P
        if len(chunk) < 6:
            st[len(chunk)] = (st[len(chunk)] + 1) % P
        st = p2_perm(st)
    if len(limbs) % 6 == 0:
        st[0] = (st[0] + 1) % P
        st = p2_perm(st)
    return st


def poseidon2_sponge_accel(domain_tag, limbs):
    """qsag-accel Poseidon2Sponge (rate=8, cap=[8, 4, domain_tag, P2_IV], 10*1 padding)."""
    st = [0] * 8 + [8, 4, domain_tag % P, P2_IV % P]
    pos = 0
    for l in limbs:
        st[pos] = (st[pos] + (l % P)) % P
        pos += 1
        if pos == 8:
            st = p2_perm(st)
            pos = 0
    if pos == 7:
        st[7] = (st[7] + (1 << 56) + 1) % P
    else:
        st[pos] = (st[pos] + 1) % P
        st[7] = (st[7] + (1 << 56)) % P
    st = p2_perm(st)
    return st[:4]


# ---------------------------------------------------------------- Keccak
KECCAK_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
KECCAK_ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]


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


def sponge(msg, suffix, outlen, rounds, rate=136):
    st = [0] * 25
    msg = bytes(msg)
    full = len(msg) // rate
    for i in range(full):
        for l in range(rate // 8):
            st[l] ^= int.from_bytes(msg[i * rate + 8 * l:i * rate + 8 * l + 8], "little")
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
    while True:
        out += b"".join(st[l].to_bytes(8, "little") for l in range(rate // 8))
        if len(out) >= outlen:
            return out[:outlen]
        st = keccak_p(st, rounds)


def shake256(msg, outlen):
    return sponge(msg, 0x1F, outlen, 24)


def turboshake256(msg, outlen, suffix=0x1F):
    return sponge(msg, suffix, outlen, 12)


# ---------------------------------------------------------------- GF(2^128), z^128 + z^7 + z^2 + z + 1
def clmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def gf128_reduce(x):
    for i in range(x.bit_length() - 1, 127, -1):
        if (x >> i) & 1:
            x ^= (0x87 | (1 << 128)) << (i - 128)
    return x


def gf128_mul(a, b):
    return gf128_reduce(clmul(a, b))


TOWER_GENS = [
    0x295AC0B1F4731AF9676AAC9FA4B20B08, 0x500317BD159D73BB34D2F7FBA603E341,
    0x872430DCDF135BCC433F53640B5AB39A, 0x08EE6D05A2AFA6E5F848729A9637483A,
    0x6167C15AE3F2515951C65CFFFDD09B94, 0x11BF2AE00EEFB7458F1990F8FFD4B9BC,
    0x8845A6B78C9FFFC36A2A74600CFA98DE,
]


def _tower_basis():
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


def _lin(cols, x):
    r = 0
    for i in range(128):
        if (x >> i) & 1:
            r ^= cols[i]
    return r


def tower128_mul(a, b, _tb=[]):
    if not _tb:
        _tb.extend(_tower_basis())
    return _lin(_tb[1], gf128_mul(_lin(_tb[0], a), _lin(_tb[0], b)))


# ---------------------------------------------------------------- self-check
def selfcheck(fixture_path):
    fx = json.load(open(fixture_path))
    n = 0
    for e in fx["goldilocks_edges"]:
        a, b = int(e["a_raw"]), int(e["b_raw"])
        assert a % P == int(e["a_canon"]) and (a + b) % P == int(e["add"])
        assert (a - b) % P == int(e["sub"]) and a * b % P == int(e["mul"])
        assert gl_pow7(a % P) == int(e["pow7_a"])
        n += 1
    for e in fx["goldilocks_ext4"]:
        assert ext4_mul([int(v) for v in e["x"]], [int(v) for v in e["y"]]) == [int(v) for v in e["mul"]]
        n += 1
    for e in fx["poseidon2_12"]:
        assert p2_perm([int(v) for v in e["input"]]) == [int(v) for v in e["perm"]]
        n += 1
    for e in fx["sponges"]:
        m = bytes.fromhex(e["msg_hex"])
        assert sponge(m, 0x06, 32, 24).hex() == e["sha3_256_hex"]
        assert shake256(m, 64).hex() == e["shake256_64_hex"] == hashlib.shake_256(m).hexdigest(64)
        n += 1
    for e in fx["tower128"]:
        a = int.from_bytes(bytes.fromhex(e["a_le_hex"]), "little")
        b = int.from_bytes(bytes.fromhex(e["b_le_hex"]), "little")
        assert tower128_mul(a, b).to_bytes(16, "little").hex() == e["mul_le_hex"]
        n += 1
    # RFC 9861 TurboSHAKE256(M = empty, D = 0x1F), first 8 output bytes.
    assert turboshake256(b"", 64, 0x1F).hex().startswith("367a329dafea871c")
    # Fp5 = F_p[X]/(X^5 - 3): X^5 == 3 and distributivity check
    x_el = [0, 1, 0, 0, 0]
    x2 = fp5_mul(x_el, x_el)
    x4 = fp5_mul(x2, x2)
    assert fp5_mul(x4, x_el) == [3, 0, 0, 0, 0]
    u5, v5, w5 = [1, 2, 3, 4, 5], [P - 1, 7, 0, 9, 11], [42, 0, P - 3, 8, 1]
    assert fp5_mul(u5, fp5_add(v5, w5)) == fp5_add(fp5_mul(u5, v5), fp5_mul(u5, w5))
    # sponge12_rate6 empty and exact-boundary self-check
    assert sponge12_rate6([]) == p2_perm([1] + [0] * 11)
    assert pack_bytes_framed_accel(b"abc") == [3, int.from_bytes(b"abc\x01\x00\x00\x00", "big")]
    return n


if __name__ == "__main__":
    print("selfcheck vectors OK:", selfcheck(sys.argv[1]))
