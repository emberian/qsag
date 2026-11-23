#!/usr/bin/env python3
"""Generate leaf vectors and a command-port known-answer trace.

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
        for i in range(128):
            for j in range(128):
                f.write(f"{1 << i:032x} {1 << j:032x} {R.gf128_mul(1 << i, 1 << j):032x}\n")
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
    """Bit-exact functional model of qsag_ni_asic_top (AW = 16, 512 KiB 4-bank SRAM)."""

    def __init__(self, path):
        self.f = open(path, "w")
        self.st = [0] * 12
        self.mem = {}
        self.key = [0] * 3
        self.ks = [0] * 25
        self.shadow = [0] * 25
        self.wptr = 0
        self.verify_fail = 0
        self.verify_checks = 0

    def close(self):
        self.f.close()

    def cmd(self, op, idx=0, addr=0, data=0, chk=0, exp=0):
        self.f.write(f"{op:02x} {idx:02x} {addr & 0xFFFFFF:06x} {data & R.M64:016x} {chk:x} {exp & R.M64:016x}\n")

    def mark(self, tag, label=0):
        self.cmd(0xF0, 0, label, tag)

    def wr_st(self, i, v):
        self.st[i] = v & R.M64
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
        a &= 0xFFFF
        self.mem[a] = v & R.M64
        self.cmd(0x03, 0, a, v)

    def rd_mem(self, a):
        a &= 0xFFFF
        self.cmd(0x04, 0, a, 0, 1, self.mem[a])

    def wr_key(self, i, v):
        self.key[i] = v & R.M64
        self.cmd(0x05, i, 0, v)

    def ld4(self, idx, a):
        a &= 0xFFFF
        self.st[idx:idx + 4] = [self.mem[(a + i) & 0xFFFF] for i in range(4)]
        self.cmd(0x06, idx, a)

    def sv4(self, a):
        a &= 0xFFFF
        for i in range(4):
            self.mem[(a + i) & 0xFFFF] = self.st[i]
        self.cmd(0x07, 0, a)

    def set_wptr(self, a):
        self.wptr = a & 0xFFFF
        self.cmd(0x08, 0, self.wptr)

    def clr_status(self):
        self.verify_fail = 0
        self.verify_checks = 0
        self.cmd(0x08, 1, 0)

    def wr_mem_burst(self, addr, words):
        self.set_wptr(addr)
        for w in words:
            self.mem[self.wptr] = w & R.M64
            self.cmd(0x09, 0, 0, w)
            self.wptr = (self.wptr + 1) & 0xFFFF

    def check_eq4(self, use_keccak, addr, expect_match=True):
        addr &= 0xFFFF
        got = self.ks[:4] if use_keccak else self.st[:4]
        exp_vec = [self.mem[(addr + i) & 0xFFFF] for i in range(4)]
        mism = int(got != exp_vec)
        if mism:
            self.verify_fail = 1
        self.verify_checks += 1
        assert (mism == 0) == expect_match, f"check_eq4 mismatch: got={got} exp={exp_vec}"
        self.cmd(0x0A, 1 if use_keccak else 0, addr, 0, 1, 0 if mism else 1)

    def rd_status(self, expect_ok=True):
        ok_bit = 1 - self.verify_fail
        assert (ok_bit == 1) == expect_ok, f"status ok_bit={ok_bit} != {expect_ok}"
        exp = (ok_bit << 32) | (self.verify_checks & 0xFFFFFFFF)
        self.cmd(0x0B, 0, 0, 0, 1, exp)

    def perm(self):
        self.st = R.p2_perm(self.st)
        self.cmd(0x10)

    def _canopy_one(self, st12):
        l, r, c = st12[0:4], st12[4:8], st12[8:12]
        p = R.p2_perm(st12)
        for i in range(4):
            p[i] = (p[i] + l[i] + 2 * r[i] + 4 * c[i]) % P
        return p

    def canopy(self):
        self.st = self._canopy_one(self.st)
        self.cmd(0x11)

    def merkle(self, depth, base, leaf_index):
        base &= 0xFFFF
        node = (1 << depth) | leaf_index
        for lvl in range(depth):
            sib = [self.mem[(base + 4 * lvl + i) & 0xFFFF] for i in range(4)]
            if node & 1:
                self.st[4:8] = self.st[0:4]
                self.st[0:4] = sib
            else:
                self.st[4:8] = sib
            self.st[8] = R.P2_CANOPY_NODE_HI | (node >> 1)
            self.st[9:12] = self.key
            self.st = self._canopy_one(self.st)
            node >>= 1
        self.cmd(0x12, depth, base, leaf_index)

    def absorb8(self, a):
        a &= 0xFFFF
        for i in range(8):
            self.st[i] = (self.st[i] + self.mem[(a + i) & 0xFFFF]) % P
        self.st = R.p2_perm(self.st)
        self.cmd(0x13, 0, a)

    def canopy4_batch(self, desc_base, num_quads):
        """4-way C-slowed Canopy batch: 36 words/quad at desc_base -> 16 words/quad at self.wptr."""
        cur = desc_base & 0xFFFF
        for _ in range(num_quads):
            for s in range(4):
                nidx = self.mem[cur] & 0xFFFFFFFF
                left = [self.mem[(cur + 1 + i) & 0xFFFF] for i in range(4)]
                right = [self.mem[(cur + 5 + i) & 0xFFFF] for i in range(4)]
                c = [R.P2_CANOPY_NODE_HI | nidx] + list(self.key)
                out = self._canopy_one(left + right + c)[:4]
                if s == 0:
                    # slot 0 stays in st[0..3] (full 12-lane state after S4_FF)
                    full = self._canopy_one(left + right + c)
                    self.st = full
                for i in range(4):
                    self.mem[(self.wptr + i) & 0xFFFF] = out[i]
                self.wptr = (self.wptr + 4) & 0xFFFF
                cur = (cur + 9) & 0xFFFF
        self.cmd(0x14, 0, desc_base, num_quads)

    def p2_sponge_m(self, base, num_blocks):
        base &= 0xFFFF
        for b in range(num_blocks):
            for i in range(8):
                self.st[i] = (self.st[i] + self.mem[(base + 8 * b + i) & 0xFFFF]) % P
            self.st = R.p2_perm(self.st)
        self.cmd(0x15, 0, base, num_blocks)

    def glmul(self):
        self.st[0] = self.st[0] * self.st[1] % P
        self.cmd(0x23)

    def k_xor(self, i, v):
        self.ks[i] ^= (v & R.M64)
        self.cmd(0x30, i, 0, v)

    def k_set(self, i, v):
        self.ks[i] = v & R.M64
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

    def k_absorb_mem(self, base, num_words, rounds12=True, pad_end=True):
        base &= 0xFFFF
        for i in range(num_words):
            self.ks[i] ^= self.mem[(base + i) & 0xFFFF]
        if pad_end:
            self.ks[16] ^= (1 << 63)
        self.ks = R.keccak_p(self.ks, 12 if rounds12 else 24)
        idx = ((1 if rounds12 else 0) << 1) | (1 if pad_end else 0)
        self.cmd(0x37, idx, base, num_words)

    def ts_canopy_batch(self, desc_base, num_nodes):
        cur = desc_base & 0xFFFF
        for _ in range(num_nodes):
            nidx = self.mem[cur] & 0xFFFFFFFF
            left_w = [self.mem[(cur + 1 + i) & 0xFFFF] for i in range(4)]
            right_w = [self.mem[(cur + 5 + i) & 0xFFFF] for i in range(4)]
            raw = bytes([0x00]) + nidx.to_bytes(4, "little")
            raw += b"".join(w.to_bytes(8, "little") for w in left_w)
            raw += b"".join(w.to_bytes(8, "little") for w in right_w)
            raw += bytes([0x07, 0x00, 0x00])
            st = list(self.shadow)
            for l in range(9):
                st[l] ^= int.from_bytes(raw[8 * l:8 * l + 8], "little")
            st[16] ^= (1 << 63)
            self.ks = R.keccak_p(st, 12)
            for i in range(4):
                self.mem[(self.wptr + i) & 0xFFFF] = self.ks[i]
            self.wptr = (self.wptr + 4) & 0xFFFF
            cur = (cur + 9) & 0xFFFF
        self.cmd(0x38, 0, desc_base, num_nodes)

    def gf(self, poly):
        a = self.st[1] << 64 | self.st[0]
        b = self.st[3] << 64 | self.st[2]
        r = R.gf128_mul(a, b) if poly else R.tower128_mul(a, b)
        self.st[0], self.st[1] = r & R.M64, r >> 64
        self.cmd(0x41 if poly else 0x40)

    def k_absorb_bytes_sram(self, msg, rounds, suffix, stage_addr):
        """Absorb arbitrary padded byte slice via dual-port SRAM + K_ABSORB_MEM."""
        full = len(msg) // 136
        blocks = [bytearray(msg[i * 136:(i + 1) * 136]) for i in range(full)]
        last = bytearray(136)
        rem = msg[full * 136:]
        last[:len(rem)] = rem
        last[len(rem)] ^= suffix
        for blk in blocks:
            ws = [int.from_bytes(blk[8 * l:8 * l + 8], "little") for l in range(17)]
            self.wr_mem_burst(stage_addr, ws)
            self.k_absorb_mem(stage_addr, 17, rounds12=(rounds == 12), pad_end=False)
        # Trim trailing zero words on last block (pad_end handles lane 16 bit 63)
        ws_last = [int.from_bytes(last[8 * l:8 * l + 8], "little") for l in range(17)]
        nw = 17
        while nw > 0 and ws_last[nw - 1] == 0:
            nw -= 1
        if nw > 0:
            self.wr_mem_burst(stage_addr, ws_last[:nw])
        self.k_absorb_mem(stage_addr, nw, rounds12=(rounds == 12), pad_end=True)

    def p2_sponge(self, domain, cap, limbs, base):
        blocks = [domain % P, len(limbs)] + [v % P for v in limbs[:6]]
        blocks += [0] * (8 - len(blocks))
        rest = [v % P for v in limbs[6:]]
        while rest:
            blk = rest[:8]
            blocks += blk + [0] * (8 - len(blk))
            rest = rest[8:]
        self.wr_mem_burst(base, blocks)
        self.wr_all([0] * 8 + [c % P for c in cap])
        nb = len(blocks) // 8
        self.p2_sponge_m(base, nb)
        return nb


def trace_kat(fx, out):
    e = Emu(f"{out}/trace_kat.hex")
    e.clr_status()
    # Poseidon2-12 permutation KATs (1-slot)
    for i, v in enumerate(fx["poseidon2_12"]):
        e.wr_all([int(x) for x in v["input"]])
        e.mark(0)
        e.perm()
        e.mark(100, i)
        assert e.st == [int(x) for x in v["perm"]]
        for l in range(12):
            e.rd_st(l)
    # Goldilocks multiplier edge KATs
    for v in fx["goldilocks_edges"]:
        e.wr_st(0, int(v["a_raw"]))
        e.wr_st(1, int(v["b_raw"]))
        e.glmul()
        assert e.st[0] == int(v["mul"])
        e.rd_st(0)
    # Canopy node (1-slot) + 4-way C-slowed Canopy batch (`P2_CANOPY4_BATCH`)
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

    # 4-way C-slowed Canopy batch KAT (4 distinct Canopy nodes in parallel -> 58.75 clks/node compute!)
    desc = []
    exp_c4 = []
    for k in range(4):
        lk = [canon() for _ in range(4)]
        rk = [canon() for _ in range(4)]
        nidx = 500 + k
        desc += [nidx] + lk + rk
        exp_c4 += R.p2_canopy_node(lk, rk, key, nidx)
    e.wr_mem_burst(0x0800, desc)
    e.set_wptr(0x0900)
    e.mark(0)
    e.canopy4_batch(0x0800, 1)
    e.mark(110, 4)
    for i in range(16):
        assert e.mem[0x0900 + i] == exp_c4[i]
        e.rd_mem(0x0900 + i)

    # Canopy path (depth 17 & 20)
    for depth, label in ((20, 20), (17, 17)):
        leaf = [canon() for _ in range(4)]
        sibs = [[canon() for _ in range(4)] for _ in range(depth)]
        index = rnd.getrandbits(depth)
        e.wr_mem_burst(0x0100, [w for s in sibs for w in s])
        e.wr_all(leaf)
        e.mark(0)
        e.merkle(depth, 0x0100, index)
        e.mark(104, label)
        assert e.st[0:4] == R.p2_canopy_path(leaf, sibs, key, index)
        e.rd4()

    # Multi-block Poseidon2 sponge (`P2_SPONGE_M`)
    limbs = [canon() for _ in range(32)]
    cap = [canon() for _ in range(4)]
    e.mark(0)
    e.p2_sponge(0x5032434E534C5401, cap, limbs, 0x0200)
    e.mark(105)
    e.rd4()

    # SHAKE256 (24 rounds) on fixture messages + TurboSHAKE256 Canopy internal node batch (`TS_CANOPY_BATCH`)
    for v in fx["sponges"]:
        msg = bytes.fromhex(v["msg_hex"])
        for l_i in range(25):
            e.k_set(l_i, 0)
        e.k_absorb_bytes_sram(msg, 24, 0x1F, 0x0300)
        got = b"".join(e.ks[l_i].to_bytes(8, "little") for l_i in range(8))
        assert got.hex() == v["shake256_64_hex"]
        for l_i in range(8):
            e.k_rd(l_i)

    mid = R.turboshake256_midstate(R.TURBOSHAKE_CANOPY_CUSTOM)
    for l_i in range(25):
        e.k_set(l_i, mid[l_i])
    e.k_save()
    ts_desc = []
    ts_exp = []
    for k in range(4):
        lw = [rnd.getrandbits(64) for _ in range(4)]
        rw = [rnd.getrandbits(64) for _ in range(4)]
        nidx = 900 + k
        ts_desc += [nidx] + lw + rw
        lb = b"".join(w.to_bytes(8, "little") for w in lw)
        rb = b"".join(w.to_bytes(8, "little") for w in rw)
        exp_b = R.ts_canopy_internal(nidx, lb, rb)
        ts_exp += [int.from_bytes(exp_b[8 * i:8 * i + 8], "little") for i in range(4)]
    e.wr_mem_burst(0x0A00, ts_desc)
    e.set_wptr(0x0B00)
    e.mark(0)
    e.ts_canopy_batch(0x0A00, 4)
    e.mark(111, 4)
    for i in range(16):
        assert e.mem[0x0B00 + i] == ts_exp[i]
        e.rd_mem(0x0B00 + i)

    # GF(2^128) tower & poly KATs
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

    # Memory moves and sponge absorption.
    base = 0x0c00
    for j in range(8):
        e.wr_mem(base+j, canon())
    e.ld4(0, base)
    e.sv4(base+8)
    e.check_eq4(False, base+8)
    e.absorb8(base)
    e.rd4()

    # Nonce injection, domain initialization, depth-zero root and odd squeeze.
    e.cmd(0x3a, 0)
    e.ks = R.turboshake256_midstate(b"QSAG.ZKHEM2.TRANSCRIPT")
    nonce = [canon() for _ in range(4)]
    for j, word in enumerate(nonce):
        e.cmd(0x0c, j, data=word)
    e.cmd(0x0d)
    frame = pack(nonce) << 48
    for j in range(5):
        e.ks[j] ^= (frame >> (64*j)) & R.M64
        e.k_rd(j)
    e.k_save()
    e.k_xor(0, 71)
    for rounds in (12, 24):
        e.k_perm(rounds)
        e.k_rd(0)
    e.k_restore()
    e.k_rd(0)
    child = pack(e.ks[:7]).to_bytes(56, "little")[:50]
    stage = 5
    e.cmd(0x16, data=stage << 32)
    root = R.turboshake256(bytes([1, stage, 0]) + child, 40,
                            state=R.turboshake256_midstate(b"QSAG.ZKHEM2.TREE/v1"))
    e.cmd(0x39, addr=base, data=5)
    for j in range(5):
        e.mem[base+j] = int.from_bytes(root[8*j:8*j+8], "little")
        e.rd_mem(base+j)

    for op in (0x28, 0x29, 0x2a, 0x2b):
        r = [canon() for _ in range(5)]
        a = [canon() for _ in range(5)]
        terms = [[canon() for _ in range(5)] for _ in range(3)]
        if op == 0x2b:
            a = [(2*x+y+z) % P for x,y,z in zip(*terms)]
        e.wr_all(a+r)
        e.wr_mem_burst(base, [v for row in terms for v in row])
        if op == 0x28:
            result = R.fp5_muladd(a, r, terms[0])
            e.cmd(op, addr=base)
        elif op == 0x29:
            result = a
            for term in terms:
                result = R.fp5_muladd(result, r, term)
            e.cmd(op, addr=base, data=len(terms))
        elif op == 0x2a:
            lo, hi = terms[:2]
            result = R.fp5_muladd([y-x for x,y in zip(lo,hi)], r, lo)
            e.cmd(op, addr=base, data=1)
            for j, value in enumerate(result):
                e.mem[base+j] = value
                e.rd_mem(base+j)
        else:
            result = [0]*5
            for term in reversed(terms):
                result = R.fp5_muladd(result, r, term)
            e.cmd(op, addr=base, data=len(terms)-1)
            e.verify_checks += 1
        e.st[:5] = result
        for j in range(10):
            e.rd_st(j)
    e.rd_status()
    e.close()


if __name__ == "__main__":
    fixture, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    print("reference selfcheck:", R.selfcheck(fixture))
    fx = json.load(open(fixture))
    unit_vectors(fx, out)
    trace_kat(fx, out)
