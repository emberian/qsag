#!/usr/bin/env python3
"""Write unit vectors and top-level command traces (with expected responses) from the
Python reference, after checking the reference against the qsag fixture.

  python3 gen/gen_vectors.py fixtures/lean_external_oracle_vectors.json vec/
"""
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(__file__))
import qsag_ref as R

P = R.P
rnd = random.Random(0x51534147)
EDGE = [0, 1, 2, P - 1, P - 2, P, P + 1, 2**64 - 1, 2**32 - 1, 2**32, 2**32 + 1, 2**63, 2**63 - 1,
        0xFFFFFFFF00000000, 0x00000000FFFFFFFF, 0x8000000000000000]


def canon():
    return rnd.choice([0, 1, P - 1, P - 2, 2**32 - 1, 2**32]) if rnd.random() < 0.1 else rnd.randrange(P)


def pack(lanes):
    return sum(v << (64 * i) for i, v in enumerate(lanes))


def unit_vectors(fx, out):
    with open(f"{out}/glmul.hex", "w") as f:
        pairs = [(a, b) for a in EDGE for b in EDGE]
        pairs += [(int(e["a_raw"]), int(e["b_raw"])) for e in fx["goldilocks_edges"]]
        pairs += [(rnd.getrandbits(64), rnd.getrandbits(64)) for _ in range(20000)]
        pairs += [(rnd.getrandbits(64) | (2**64 - 2**rnd.randrange(1, 64)), rnd.getrandbits(64)) for _ in range(2000)]
        for a, b in pairs:
            f.write(f"{a:016x} {b:016x} {a * b % P:016x}\n")
    with open(f"{out}/red128.hex", "w") as f:
        vs = [a * b for a in EDGE for b in EDGE] + [2**128 - 1, 2**127, 2**96, 2**96 - 1, 2**64, 2**64 - 1]
        vs += [rnd.getrandbits(128) for _ in range(20000)]
        vs += [(2**128 - 1) ^ rnd.getrandbits(rnd.randrange(1, 100)) for _ in range(2000)]
        for v in vs:
            f.write(f"{v:032x} {v % P:016x}\n")
    with open(f"{out}/me.hex", "w") as fe, open(f"{out}/mi.hex", "w") as fi:
        cases = [[P - 1] * 12, [0] * 12, list(range(12))] + [[canon() for _ in range(12)] for _ in range(3000)]
        for x in cases:
            rc = [canon() for _ in range(12)]
            ye = [(v + c) % P for v, c in zip(R.p2_me(x), rc)]
            yi = [(v + c) % P for v, c in zip(R.p2_mi(x), rc)]
            fe.write(f"{pack(x):0192x} {pack(rc):0192x} {pack(ye):0192x}\n")
            fi.write(f"{pack(x):0192x} {pack(rc):0192x} {pack(yi):0192x}\n")
    with open(f"{out}/gfpoly.hex", "w") as f:
        for _ in range(3000):
            a, b = rnd.getrandbits(128), rnd.getrandbits(128)
            f.write(f"{a:032x} {b:032x} {R.gf128_mul(a, b):032x}\n")
        for a, b in [(0, 5), (1, 2**127), (2**127, 2**127), (2**128 - 1, 2**128 - 1), (2, 2**127)]:
            f.write(f"{a:032x} {b:032x} {R.gf128_mul(a, b):032x}\n")
    with open(f"{out}/gftower.hex", "w") as f:
        for e in fx["tower128"]:
            a = int.from_bytes(bytes.fromhex(e["a_le_hex"]), "little")
            b = int.from_bytes(bytes.fromhex(e["b_le_hex"]), "little")
            m = int.from_bytes(bytes.fromhex(e["mul_le_hex"]), "little")
            assert R.tower128_mul(a, b) == m
            f.write(f"{a:032x} {b:032x} {m:032x}\n")
        for _ in range(500):
            a, b = rnd.getrandbits(128), rnd.getrandbits(128)
            f.write(f"{a:032x} {b:032x} {R.tower128_mul(a, b):032x}\n")
    with open(f"{out}/keccak_round.hex", "w") as f:
        for i in range(300):
            st = [rnd.getrandbits(64) for _ in range(25)]
            rc = R.KECCAK_RC[i % 24]
            f.write(f"{pack(st):0400x} {rc:016x} {pack(R.keccak_round(st, rc)):0400x}\n")


class Emu:
    """Functional model of qsag_ni_asic_top; every method appends its command to the trace."""

    def __init__(self, path):
        self.f = open(path, "w")
        self.st, self.mem, self.key = [0] * 12, {}, [0] * 3
        self.ks, self.shadow = [0] * 25, [0] * 25

    def cmd(self, op, idx=0, addr=0, data=0, chk=0, exp=0):
        self.f.write(f"{op:02x} {idx:02x} {addr:06x} {data:016x} {chk:x} {exp:016x}\n")

    def mark(self, tag, label=0):
        self.cmd(0xF0, 0, label, tag)

    def wr_st(self, i, v):
        self.st[i] = v
        self.cmd(0x01, i, 0, v)

    def wr_all(self, vals, base=0):
        for i, v in enumerate(vals):
            self.wr_st(base + i, v)

    def rd_st(self, i):
        self.cmd(0x02, i, 0, 0, 1, self.st[i])

    def rd4(self):
        for i in range(4):
            self.rd_st(i)

    def wr_mem(self, a, v):
        self.mem[a] = v
        self.cmd(0x03, 0, a, v)

    def rd_mem(self, a):
        self.cmd(0x04, 0, a, 0, 1, self.mem[a])

    def wr_key(self, i, v):
        self.key[i] = v
        self.cmd(0x05, i, 0, v)

    def ld4(self, idx, a):
        self.st[idx:idx + 4] = [self.mem[a + i] for i in range(4)]
        self.cmd(0x06, idx, a)

    def sv4(self, a):
        for i in range(4):
            self.mem[a + i] = self.st[i]
        self.cmd(0x07, 0, a)

    def perm(self):
        self.st = R.p2_perm(self.st)
        self.cmd(0x10)

    def _canopy(self):
        l, r, c = self.st[0:4], self.st[4:8], self.st[8:12]
        self.st = R.p2_perm(self.st)
        for i in range(4):
            self.st[i] = (self.st[i] + l[i] + 2 * r[i] + 4 * c[i]) % P

    def canopy(self):
        self._canopy()
        self.cmd(0x11)

    def merkle(self, depth, base, leaf_index):
        node = (1 << depth) | leaf_index
        for lvl in range(depth):
            sib = [self.mem[base + 4 * lvl + i] for i in range(4)]
            if node & 1:
                self.st[4:8] = self.st[0:4]
                self.st[0:4] = sib
            else:
                self.st[4:8] = sib
            self.st[8] = R.P2_CANOPY_NODE_HI | (node >> 1)
            self.st[9:12] = self.key
            self._canopy()
            node >>= 1
        self.cmd(0x12, depth, base, leaf_index)

    def absorb8(self, a):
        for i in range(8):
            self.st[i] = (self.st[i] + self.mem[a + i]) % P
        self.st = R.p2_perm(self.st)
        self.cmd(0x13, 0, a)

    def emuladd(self):
        self.st[0:4] = R.ext4_muladd(self.st[0:4], self.st[4:8], self.st[8:12])
        self.cmd(0x20)

    def eadd(self):
        self.st[0:4] = R.ext4_add(self.st[0:4], self.st[8:12])
        self.cmd(0x21)

    def esub(self):
        self.st[0:4] = R.ext4_sub(self.st[0:4], self.st[8:12])
        self.cmd(0x22)

    def glmul(self):
        self.st[0] = self.st[0] * self.st[1] % P
        self.cmd(0x23)

    def fold(self, base, pairs):
        r = self.st[4:8]
        for i in range(pairs):
            lo = [self.mem[base + 8 * i + j] for j in range(4)]
            hi = [self.mem[base + 8 * i + 4 + j] for j in range(4)]
            res = R.ext4_muladd(R.ext4_sub(hi, lo), r, lo)
            for j in range(4):
                self.mem[base + 4 * i + j] = res[j]
            self.st[8:12] = lo
            self.st[0:4] = res
        self.cmd(0x24, 0, base, pairs)

    def k_xor(self, i, v):
        self.ks[i] ^= v
        self.cmd(0x30, i, 0, v)

    def k_set(self, i, v):
        self.ks[i] = v
        self.cmd(0x31, i, 0, v)

    def k_rd(self, i):
        self.cmd(0x32, i, 0, 0, 1, self.ks[i])

    def k_perm(self, rounds):
        self.ks = R.keccak_p(self.ks, rounds)
        self.cmd(0x33 if rounds == 12 else 0x34)

    def k_save(self):
        self.shadow = list(self.ks)
        self.cmd(0x35)

    def k_restore(self):
        self.ks = list(self.shadow)
        self.cmd(0x36)

    def gf(self, poly):
        a = self.st[1] << 64 | self.st[0]
        b = self.st[3] << 64 | self.st[2]
        r = R.gf128_mul(a, b) if poly else R.tower128_mul(a, b)
        self.st[0], self.st[1] = r & R.M64, r >> 64
        self.cmd(0x41 if poly else 0x40)

    # ---- composite host sequences
    def k_absorb_bytes(self, msg, rounds, suffix):
        """Absorb a padded message into the current Keccak state (rate 136) and permute."""
        full = len(msg) // 136
        blocks = [bytearray(msg[i * 136:(i + 1) * 136]) for i in range(full)]
        last = bytearray(136)
        rem = msg[full * 136:]
        last[:len(rem)] = rem
        last[len(rem)] ^= suffix
        last[135] ^= 0x80
        for blk in blocks + [last]:
            for l in range(17):
                v = int.from_bytes(blk[8 * l:8 * l + 8], "little")
                if v:
                    self.k_xor(l, v)
            self.k_perm(rounds)

    def p2_sponge(self, domain, cap, limbs, base):
        """poseidon2_sponge_hash_limbs_with_cap with the blocks staged at mem[base..]."""
        blocks = [domain % P, len(limbs)] + list(limbs[:6])
        blocks += [0] * (8 - len(blocks))
        rest = list(limbs[6:])
        while rest:
            blk = rest[:8]
            blocks += blk + [0] * (8 - len(blk))
            rest = rest[8:]
        for i, v in enumerate(blocks):
            self.wr_mem(base + i, v % P)
        self.wr_all([0] * 8 + [c % P for c in cap])
        for b in range(len(blocks) // 8):
            self.absorb8(base + 8 * b)
        return len(blocks) // 8


def bytes_of_limbs(limbs):
    return b"".join(v.to_bytes(8, "little") for v in limbs)


def trace_kat(fx, out):
    e = Emu(f"{out}/trace_kat.hex")
    # Poseidon2-12 permutation KATs
    for i, v in enumerate(fx["poseidon2_12"]):
        e.wr_all([int(x) for x in v["input"]])
        e.mark(0)
        e.perm()
        e.mark(100, i)  # one permutation
        assert e.st == [int(x) for x in v["perm"]]
        for l in range(12):
            e.rd_st(l)
    # Goldilocks multiplier and Ext4 KATs
    for v in fx["goldilocks_edges"]:
        e.wr_st(0, int(v["a_raw"]))
        e.wr_st(1, int(v["b_raw"]))
        e.glmul()
        assert e.st[0] == int(v["mul"])
        e.rd_st(0)
    for v in fx["goldilocks_ext4"]:
        e.wr_all([int(x) for x in v["x"]] + [int(x) for x in v["y"]] + [0] * 4)
        e.mark(0)
        e.emuladd()
        e.mark(101)
        assert e.st[0:4] == [int(x) for x in v["mul"]]
        e.rd4()
    for _ in range(200):
        e.wr_all([canon() for _ in range(12)])
        rnd.choice([e.emuladd, e.eadd, e.esub, e.emuladd])()
        e.rd4()
    # Canopy node, 2-block Merkle node, Canopy path
    key = [canon() for _ in range(3)]
    for i in range(3):
        e.wr_key(i, key[i])
    l, r = [canon() for _ in range(4)], [canon() for _ in range(4)]
    e.wr_all(l + r + [R.P2_CANOPY_NODE_HI | 12345] + key)
    e.mark(0)
    e.canopy()
    e.mark(102)
    assert e.st[0:4] == R.p2_canopy_node(l, r, key, 12345)
    e.rd4()
    seed = [canon() for _ in range(4)]
    dom, meta0, tlo, thi = 0x515341474D524B4C, (3 << 48) | (5 << 32) | 77, 9, 1
    e.mark(0)
    e.wr_all(seed + l + [dom % P, meta0 % P, tlo, thi])
    e.perm()
    first = list(e.st)
    for i in (4, 5, 8, 9, 10, 11):       # the host reads the lanes it has to patch or restore
        e.rd_st(i)
    for i in range(4):
        e.wr_st(8 + i, r[i])
    e.eadd()  # st[0..3] += right
    e.wr_st(4, (first[4] + 1) % P)       # host-side constant adds (lanes 4, 5)
    e.wr_st(5, (first[5] + R.P2_IV) % P)
    for i in range(4):
        e.wr_st(8 + i, first[8 + i])
    e.perm()
    e.mark(103)  # 2-block Merkle node, host-sequenced
    assert e.st[0:4] == R.p2_merkle_2block(l, r, seed, dom, meta0, tlo, thi)
    e.rd4()
    for depth, label in ((20, 20), (17, 17)):
        leaf = [canon() for _ in range(4)]
        sibs = [[canon() for _ in range(4)] for _ in range(depth)]
        index = rnd.getrandbits(depth)
        for lvl, s in enumerate(sibs):
            for i in range(4):
                e.wr_mem(0x100 + 4 * lvl + i, s[i])
        e.wr_all(leaf)
        e.mark(0)
        e.merkle(depth, 0x100, index)
        e.mark(104, label)
        assert e.st[0:4] == R.p2_canopy_path(leaf, sibs, key, index)
        e.rd4()
    # Poseidon2 sponge (rate 8) through P2_ABSORB8
    limbs = [canon() for _ in range(32)]
    cap = [canon() for _ in range(4)]
    e.mark(0)
    e.p2_sponge(0x5032434E534C5401, cap, limbs, 0x200)
    e.mark(105)
    e.rd4()
    # SHAKE256 (24 rounds) on the fixture messages
    for v in fx["sponges"]:
        msg = bytes.fromhex(v["msg_hex"])
        for l in range(25):
            e.k_set(l, 0)
        e.k_absorb_bytes(msg, 24, 0x1F)
        got = b"".join(e.ks[l].to_bytes(8, "little") for l in range(8))
        assert got.hex() == v["shake256_64_hex"]
        for l in range(8):
            e.k_rd(l)
    # TurboSHAKE256 from the Canopy customization midstate (as turboshake256_from_midstate_32)
    mid = R.turboshake256_midstate(R.TURBOSHAKE_CANOPY_CUSTOM)
    for l in range(25):
        e.k_set(l, mid[l])
    e.k_save()
    for n in (0, 64, 135, 136, 200):
        msg = bytes(rnd.getrandbits(8) for _ in range(n))
        e.mark(0)
        e.k_restore()
        e.k_absorb_bytes(msg, 12, 0x07)
        e.mark(106, n)
        assert b"".join(e.ks[l].to_bytes(8, "little") for l in range(4)) == R.turboshake256(msg, 32, 0x07, mid)
        for l in range(4):
            e.k_rd(l)
    e.mark(0)
    e.k_perm(12)
    e.mark(107)
    e.k_perm(24)
    e.mark(108)
    # GF(2^128): tower KATs and polynomial-basis products
    for v in fx["tower128"]:
        a = int.from_bytes(bytes.fromhex(v["a_le_hex"]), "little")
        b = int.from_bytes(bytes.fromhex(v["b_le_hex"]), "little")
        e.wr_all([a & R.M64, a >> 64, b & R.M64, b >> 64])
        e.mark(0)
        e.gf(False)
        e.mark(109)
        assert (e.st[1] << 64 | e.st[0]).to_bytes(16, "little").hex() == v["mul_le_hex"]
        e.rd_st(0)
        e.rd_st(1)
    for _ in range(50):
        e.wr_all([rnd.getrandbits(64) for _ in range(4)])
        e.gf(True)
        e.rd_st(0)
        e.rd_st(1)
    # small fold with memory read-back
    for i in range(64):
        e.wr_mem(0x400 + i, canon())
    e.wr_all([canon() for _ in range(4)], 4)
    e.fold(0x400, 8)
    for i in range(32):
        e.rd_mem(0x400 + i)
    e.rd4()


# QSAGSTA1 verification op-trace model (see README "Workload model"): three WHIR openings,
# stage = (queries, path depth, leaf limbs); query counts are anchored to the 282,000-byte opening
# size of the root proof (docs/QUORUM_AND_CONSENSUS_SCALING.md), geometry nv = 20 from the fixture.
STA1_OPENINGS = 3
STA1_STAGES = [(62, 17, 32), (31, 16, 32), (21, 14, 64)]
STA1_FS_PERMS = 600
STA1_SUMCHECK_MULADDS = 3000


def trace_sta1(out, mode):
    e = Emu(f"{out}/trace_sta1_{mode}.hex")
    key = [canon() for _ in range(3)]
    for i in range(3):
        e.wr_key(i, key[i])
    mid = R.turboshake256_midstate(R.TURBOSHAKE_CANOPY_CUSTOM)
    if mode == "ts":
        for l in range(25):
            e.k_set(l, mid[l])
        e.k_save()
    e.mark(0)
    nodes = leaf_hashes = muladds = words = 0
    for _ in range(STA1_OPENINGS):
        for q, depth, leaf_limbs in STA1_STAGES:
            for _ in range(q):
                limbs = [canon() for _ in range(leaf_limbs)]
                sibs = [[canon() for _ in range(4)] for _ in range(depth)]
                index = rnd.getrandbits(depth)
                words += leaf_limbs + 4 * depth
                if mode == "p2":
                    e.p2_sponge(0x5032434E534C5401, key + [0], limbs, 0x1000)
                    for lvl, s in enumerate(sibs):
                        for i in range(4):
                            e.wr_mem(0x100 + 4 * lvl + i, s[i])
                    e.merkle(depth, 0x100, index)
                    e.rd4()
                else:
                    e.k_restore()
                    e.k_absorb_bytes(bytes_of_limbs(limbs), 12, 0x07)
                    cur = [e.ks[l] for l in range(4)]
                    node = (1 << depth) | index
                    for s in sibs:
                        left, right = (s, cur) if node & 1 else (cur, s)
                        e.k_restore()
                        e.k_absorb_bytes(bytes_of_limbs(left + right), 12, 0x07)
                        cur = [e.ks[l] for l in range(4)]
                        node >>= 1
                    for l in range(4):
                        e.k_rd(l)
                    # leaf values still enter the field datapath for the fold
                    for i, v in enumerate(limbs):
                        e.wr_mem(0x1000 + i, v)
                nodes += depth
                leaf_hashes += 1
                # fold the opened leaf: Horner over groups of four limbs with the challenge in E1
                e.wr_all([canon() for _ in range(4)], 4)
                e.wr_all([0, 0, 0, 0])
                base = 0x1000 + (8 if mode == "p2" else 0)
                for g in range(leaf_limbs // 4 - (2 if mode == "p2" else 0)):
                    e.ld4(8, base + 4 * g)
                    e.emuladd()
                    muladds += 1
                e.rd4()
    # sumcheck / GKR round algebra and Fiat-Shamir transcript permutations
    e.wr_all([canon() for _ in range(12)])
    for i in range(STA1_SUMCHECK_MULADDS):
        e.emuladd()
        muladds += 1
    e.rd4()
    for i in range(STA1_FS_PERMS):
        if mode == "p2":
            e.perm()
        else:
            e.k_perm(12)
    if mode == "p2":
        e.rd4()
    else:
        e.k_rd(0)
    e.mark(200 if mode == "p2" else 201)
    return dict(mode=mode, merkle_nodes=nodes, leaf_hashes=leaf_hashes, ext4_muladds=muladds, proof_words=words,
                fs_perms=STA1_FS_PERMS)


def trace_fold(out, nvars):
    e = Emu(f"{out}/trace_fold{nvars}.hex")
    n = 1 << nvars
    for i in range(4 * n):
        e.wr_mem(i, rnd.randrange(P))
    e.mark(0)
    pairs = n // 2
    total = 0
    while pairs >= 1:
        e.wr_all([canon() for _ in range(4)], 4)  # round challenge
        e.fold(0, pairs)
        total += pairs
        pairs //= 2
    e.mark(300, nvars)
    e.rd4()
    for i in range(4):
        e.rd_mem(i)
    return dict(nvars=nvars, pair_folds=total)


if __name__ == "__main__":
    fixture, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    print("reference selfcheck:", R.selfcheck(fixture))
    fx = json.load(open(fixture))
    unit_vectors(fx, out)
    trace_kat(fx, out)
    info = [trace_sta1(out, "p2"), trace_sta1(out, "ts"), trace_fold(out, 16)]
    json.dump(info, open(f"{out}/workloads.json", "w"), indent=1)
    print(json.dumps(info))
