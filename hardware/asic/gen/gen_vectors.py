#!/usr/bin/env python3
"""Generate unit vectors, KAT trace, tiled 16-variable Ext4 fold trace (inside 512 KiB 4-bank SRAM),
and REAL QSAGSTA1 (Poseidon2 Canopy + TurboSHAKE256 Canopy) & [CWYZ26] DuetFold hardware verifier
+ tamper-rejection traces from fixtures/real_proof_bundle.json.

  python3 gen/gen_vectors.py fixtures/lean_external_oracle_vectors.json vec/
"""
import json
import os
import pathlib
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


def limbs_of_hex32(h):
    bs = bytes.fromhex(h)
    return [int.from_bytes(bs[8 * i:8 * i + 8], "little") for i in range(4)]


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

    def emuladd(self):
        self.st[0:4] = R.ext4_muladd(self.st[0:4], self.st[4:8], self.st[8:12])
        self.cmd(0x20)

    def emulbase(self):
        self.st[0:4] = R.ext4_mul_base(self.st[0:4], self.st[4])
        self.cmd(0x27)

    def eadd(self):
        self.st[0:4] = R.ext4_add(self.st[0:4], self.st[8:12])
        self.cmd(0x21)

    def esub(self):
        self.st[0:4] = R.ext4_sub(self.st[0:4], self.st[8:12])
        self.cmd(0x22)

    def glmul(self):
        self.st[0] = self.st[0] * self.st[1] % P
        self.cmd(0x23)

    def fold(self, base, pairs, use_wptr=False):
        base &= 0xFFFF
        wb = self.wptr if use_wptr else base
        r = self.st[4:8]
        for i in range(pairs):
            lo = [self.mem[(base + 8 * i + j) & 0xFFFF] for j in range(4)]
            hi = [self.mem[(base + 8 * i + 4 + j) & 0xFFFF] for j in range(4)]
            res = R.ext4_muladd(R.ext4_sub(hi, lo), r, lo)
            for j in range(4):
                self.mem[(wb + 4 * i + j) & 0xFFFF] = res[j]
            self.st[8:12] = lo
            self.st[0:4] = res
        if use_wptr:
            self.wptr = (wb + 4 * pairs) & 0xFFFF
        self.cmd(0x24, 1 if use_wptr else 0, base, pairs)

    def cwyz_duet_batch(self, base, count):
        base &= 0xFFFF
        for g in range(count):
            off = (base + 27 * g) & 0xFFFF
            ws = [self.mem[(off + i) & 0xFFFF] for i in range(27)]
            v0, v1, theta, alpha, beta, claimed = [ws[4 * k:4 * k + 4] for k in range(6)]
            inv_two, inv_two_x, x_sq = ws[24], ws[25], ws[26]
            even = R.ext4_mul_base(R.ext4_add(v0, v1), inv_two)
            odd = R.ext4_mul_base(R.ext4_sub(v0, v1), inv_two_x)
            mixed = R.ext4_add(even, R.ext4_muladd(odd, theta))
            gamma = R.ext4_add(alpha, R.ext4_mul_base(beta, x_sq))
            got = R.ext4_add(odd, R.ext4_muladd(gamma, mixed))
            self.st[0:4] = got
            self.st[4:8] = mixed
            self.st[8:12] = odd
            if got != claimed:
                self.verify_fail = 1
            self.verify_checks += 1
        self.cmd(0x25, 0, base, count)

    def ext4_horner(self, base, count):
        base &= 0xFFFF
        for i in range(count):
            c = [self.mem[(base + 4 * i + j) & 0xFFFF] for j in range(4)]
            self.st[8:12] = c
            self.st[0:4] = R.ext4_muladd(self.st[0:4], self.st[4:8], c)
        self.cmd(0x26, 0, base, count)

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
    # Goldilocks multiplier and Karatsuba Ext4 KATs
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
        rnd.choice([e.emuladd, e.eadd, e.esub, e.emulbase])()
        e.rd4()
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

    # [CWYZ26] DuetFold hardware gate batch KAT
    v0 = [canon() for _ in range(4)]
    v1 = [canon() for _ in range(4)]
    theta = [canon() for _ in range(4)]
    alpha = [canon() for _ in range(4)]
    beta = [canon() for _ in range(4)]
    inv2 = pow(2, P - 2, P)
    inv2x = pow(14, P - 2, P)
    xsq = 49
    claimed = R.cwyz_duet_step(v0, v1, theta, alpha, beta, inv2, inv2x, xsq)
    e.wr_mem_burst(0x0C00, v0 + v1 + theta + alpha + beta + claimed + [inv2, inv2x, xsq])
    e.mark(0)
    e.cwyz_duet_batch(0x0C00, 1)
    e.mark(112, 1)
    e.rd4()
    e.rd_status(expect_ok=True)
    e.close()


def _emit_steiner_opening(e, op, tamper_sib=False):
    """Execute a real Steiner-deduplicated CanopyMultiProof opening on the ASIC!
    Uses 4-way C-slowed `P2_CANOPY4_BATCH` (Poseidon2) or `TS_CANOPY_BATCH` (TurboSHAKE256)
    level by level, then computes the domain-bound commitment root and asserts `CHECK_EQ4`!
    """
    n = 1 << op["log_leaves"]
    active = [(n + idx, limbs_of_hex32(h)) for idx, h in op["leaves"]]
    sibs = [limbs_of_hex32(h) for h in op["siblings"]]
    if tamper_sib and sibs:
        sibs[0][0] ^= 1
    cur_s = 0
    is_p2 = (op["mode"] == "poseidon2")
    if is_p2:
        tkey = R.p2_canopy_tree_key(op["stage_idx"], op["log_leaves"])
        for i in range(3):
            e.wr_key(i, tkey[i])

    nodes_hashed = 0
    DESC_ADDR = 0x2000
    OUT_ADDR = 0x6000
    for _ in range(op["log_leaves"]):
        step_nodes = []
        k = 0
        while k < len(active):
            u, hu = active[k]
            if k + 1 < len(active) and active[k + 1][0] == (u ^ 1):
                hsib = active[k + 1][1]
                k += 2
            else:
                hsib = sibs[cur_s]
                cur_s += 1
                k += 1
            left, right = (hsib, hu) if (u & 1) else (hu, hsib)
            step_nodes.append((u >> 1, left, right))
        nodes_hashed += len(step_nodes)

        if is_p2:
            # Pad to multiple of 4 for 4-way C-slowed P2_CANOPY4_BATCH
            quads = (len(step_nodes) + 3) // 4
            padded = list(step_nodes) + [(1, [0] * 4, [0] * 4)] * (4 * quads - len(step_nodes))
            words = [w for (pidx, l, r) in padded for w in ([pidx] + l + r)]
            e.wr_mem_burst(DESC_ADDR, words)
            e.set_wptr(OUT_ADDR)
            e.canopy4_batch(DESC_ADDR, quads)
        else:
            words = [w for (pidx, l, r) in step_nodes for w in ([pidx] + l + r)]
            e.wr_mem_burst(DESC_ADDR, words)
            e.set_wptr(OUT_ADDR)
            e.ts_canopy_batch(DESC_ADDR, len(step_nodes))

        active = [
            (pidx, [e.mem[OUT_ADDR + 4 * idx_n + j] for j in range(4)])
            for idx_n, (pidx, _, _) in enumerate(step_nodes)
        ]

    top_limbs = active[0][1]
    exp_root = limbs_of_hex32(op["root"])
    e.wr_mem_burst(0x0080, exp_root)
    if is_p2:
        e.p2_sponge(R.P2_DOMAIN_CANOPY_ROOT, [0, 0, 0, 0],
                    [op["stage_idx"], op["log_leaves"]] + top_limbs, 0x0100)
        e.check_eq4(False, 0x0080, expect_match=not (tamper_sib and bool(sibs)))
    else:
        top_bytes = b"".join(w.to_bytes(8, "little") for w in top_limbs)
        msg = bytes([R.TAG_MERKLE_ROOT, op["log_leaves"]]) + top_bytes
        e.k_restore()
        e.k_absorb_bytes_sram(msg, 12, 0x07, 0x0100)
        e.check_eq4(True, 0x0080, expect_match=not (tamper_sib and bool(sibs)))
    return nodes_hashed


def trace_real_qsagsta1(bundle, out, mode, tamper=False):
    key_name = "qsagsta1_poseidon2" if mode == "p2" else "qsagsta1_turboshake"
    d = bundle[key_name]
    suffix = "_tamper" if tamper else ""
    e = Emu(f"{out}/trace_sta1_{mode}{suffix}.hex")
    e.clr_status()

    if mode == "ts":
        mid = R.turboshake256_midstate(R.TURBOSHAKE_CANOPY_CUSTOM)
        for l_i in range(25):
            e.k_set(l_i, mid[l_i])
        e.k_save()

    # Pre-stage all 306 real [CWYZ26] DuetFoldStatement gates into SRAM (306 * 27 = 8,262 words @ 0x8000)
    duet_words = []
    for gi, g in enumerate(d["duet_gates"]):
        claimed = [int(w, 16) for w in g["claimed"]]
        if tamper and gi == 0:
            claimed[0] = (claimed[0] + 1) % P
        for fld in ("v0", "v1", "theta", "alpha", "beta"):
            duet_words += [int(w, 16) for w in g[fld]]
        duet_words += claimed
        duet_words += [int(g["inv_two"], 16), int(g["inv_two_x"], 16), int(g["x_sq"], 16)]
    e.wr_mem_burst(0x8000, duet_words)

    e.mark(0)  # ---- BEGIN REAL PROOF VERIFICATION TIMING WINDOW ----

    # 1. Transcript sample permutations (Poseidon2 Fiat-Shamir blocks)
    for smp in d["p2_samples"]:
        e.wr_all([int(w, 16) for w in smp["in"]])
        e.perm()
        e.wr_mem_burst(0x0040, [int(w, 16) for w in smp["out"][:4]])
        e.check_eq4(False, 0x0040, expect_match=True)

    # 2. All 13 real Hologram / Spark / LogUp-GKR sumcheck round checks:
    #    Check g(0) + g(1) == claim_in AND Horner g(chal) == claim_out!
    for si, sc in enumerate(d["sumcheck_rounds"]):
        cin = [int(w, 16) for w in sc["claim_in"]]
        coeffs = [[int(w, 16) for w in c] for c in sc["coeffs"]]
        chal = [int(w, 16) for w in sc["chal"]]
        cout = [int(w, 16) for w in sc["claim_out"]]
        if tamper and si == 0:
            coeffs[0][0] = (coeffs[0][0] + 1) % P
        # g(0) + g(1) = c_0 + sum_j c_j
        e.wr_all(coeffs[0], 0)
        for c in coeffs:
            e.wr_all(c, 8)
            e.eadd()
        e.wr_mem_burst(0x0050, cin)
        e.check_eq4(False, 0x0050, expect_match=not (tamper and si == 0))
        # Horner evaluation g(chal) via EXT4_HORNER
        rev_flat = [w for c in reversed(coeffs) for w in c]
        e.wr_mem_burst(0x0200, rev_flat)
        e.wr_all([0, 0, 0, 0] + chal)
        e.ext4_horner(0x0200, len(coeffs))
        e.wr_mem_burst(0x0054, cout)
        e.check_eq4(False, 0x0054, expect_match=not (tamper and si == 0))

    # 3. All 3 real WHIR Stage-0 Dual-OOD evaluation pin checks
    for oi, ood in enumerate(d["ood_checks"]):
        cin = [int(w, 16) for w in ood["claim_in"]]
        cout = [int(w, 16) for w in ood["claim_out"]]
        e.wr_all(cin, 8)
        for k in range(2):
            xi = [int(w, 16) for w in ood["xis"][k]]
            ev = [int(w, 16) for w in ood["evals"][k]]
            if tamper and oi == 0 and k == 0:
                ev[0] = (ev[0] + 1) % P
            e.wr_all(xi, 0)
            e.wr_all(ev, 4)
            e.emuladd()
            if k == 0:
                e.wr_all(list(e.st[0:4]), 8)
        e.wr_mem_burst(0x0060, cout)
        e.check_eq4(False, 0x0060, expect_match=not (tamper and oi == 0))

    # 4. Real Round-0 salted leaves & Stage-k Ext4 leaves
    leaf_hashes = 0
    for lf in d["r0_leaves"]:
        salt = bytes.fromhex(lf["salt"])
        vals = [int(w, 16) for w in lf["vals"]]
        arity = len(vals) // lf["num_polys"]
        s_limbs = [int.from_bytes(salt[off:min(off + 7, 16)].ljust(8, b"\x00"), "little") for off in (0, 7, 14)]
        dom = R.P2_DOMAIN_CANOPY_LEAF_R0 if lf["num_polys"] == 1 else R.P2_DOMAIN_CANOPY_LEAF_BATCH
        e.p2_sponge(dom, [lf["leaf_idx"], arity, lf["num_polys"], 0], s_limbs + vals, 0x0400)
        e.wr_mem_burst(0x0070, limbs_of_hex32(lf["digest"]))
        e.check_eq4(False, 0x0070, expect_match=True)
        leaf_hashes += 1
    for lf in d["ext4_leaves"]:
        flat = [int(w, 16) for ext in lf["vals"] for w in ext]
        e.p2_sponge(R.P2_DOMAIN_CANOPY_LEAF_EXT4, [lf["leaf_idx"], len(lf["vals"]), lf["stage_idx"], 0], flat, 0x0400)
        e.wr_mem_burst(0x0074, limbs_of_hex32(lf["digest"]))
        e.check_eq4(False, 0x0074, expect_match=True)
        leaf_hashes += 1

    # 5. All 6 real Steiner CanopyMultiProof Merkle openings
    total_nodes = 0
    for op_i, op in enumerate(d["canopy_openings"]):
        total_nodes += _emit_steiner_opening(e, op, tamper_sib=(tamper and op_i == 1))

    # 6. All 306 real [CWYZ26] DuetFoldStatement gates via hardware CWYZ_DUET_BATCH!
    e.cwyz_duet_batch(0x8000, len(d["duet_gates"]))

    # 7. Hardware accept/reject status check!
    e.rd_status(expect_ok=not tamper)
    e.mark(200 if mode == "p2" else 201, 1 if tamper else 0)
    checks_done = e.verify_checks
    e.close()
    return dict(
        trace=f"trace_sta1_{mode}{suffix}",
        mode=mode,
        tamper=tamper,
        wire_bytes=d["wire_bytes"],
        canopy_openings=len(d["canopy_openings"]),
        canopy_internal_nodes=total_nodes,
        leaf_sponges=leaf_hashes,
        sumcheck_rounds=len(d["sumcheck_rounds"]),
        ood_checks=len(d["ood_checks"]),
        cwyz_duet_gates=len(d["duet_gates"]),
        hw_assertions=checks_done,
    )


def trace_real_duet_component(bundle, out, tamper=False):
    df = bundle["cwyz26_duet_fold"]
    p2_gates = bundle["qsagsta1_poseidon2"]["duet_gates"][:df["num_statements"]]
    suffix = "_tamper" if tamper else ""
    e = Emu(f"{out}/trace_duet_comp{suffix}.hex")
    e.clr_status()

    # Pre-stage the 4 real 27-word DuetFoldStatements and 64-column MLE evaluations into SRAM
    duet_words = []
    for gi, g in enumerate(p2_gates):
        claimed = [int(w, 16) for w in g["claimed"]]
        if tamper and gi == 1:
            claimed[2] = (claimed[2] + 1) % P
        for fld in ("v0", "v1", "theta", "alpha", "beta"):
            duet_words += [int(w, 16) for w in g[fld]]
        duet_words += claimed
        duet_words += [int(g["inv_two"], 16), int(g["inv_two_x"], 16), int(g["x_sq"], 16)]
    e.wr_mem_burst(0x1000, duet_words)

    col_words = [int(w, 16) for col in df["column_evaluations"] for w in col]
    e.wr_mem_burst(0x2000, col_words)

    e.mark(0)
    # 1. Verify all [CWYZ26] DuetFoldStatement rows in hardware
    e.cwyz_duet_batch(0x1000, len(p2_gates))
    # 2. Verify cubic round polynomials g_r(0) + g_r(1) == claim (round 0 claim == 0!)
    for ri, rp in enumerate(df["round_polynomials"]):
        coeffs = [[int(w, 16) for w in c] for c in rp]
        if ri == 0:
            if tamper:
                coeffs[2][0] = (coeffs[2][0] + 1) % P
            e.wr_all(coeffs[0], 0)
            for c in coeffs:
                e.wr_all(c, 8)
                e.eadd()
            e.wr_mem_burst(0x0040, [0, 0, 0, 0])
            e.check_eq4(False, 0x0040, expect_match=not tamper)
    # 3. Fold the 64-column evaluations across 6 boolean hypercube variables in SRAM
    for v in range(6):
        e.wr_all([canon() for _ in range(4)], 4)
        e.fold(0x2000, 32 >> v)
    e.rd4()
    e.rd_status(expect_ok=not tamper)
    e.mark(310, 1 if tamper else 0)
    checks_done = e.verify_checks
    e.close()
    return dict(trace=f"trace_duet_comp{suffix}", tamper=tamper, statements=len(p2_gates), hw_assertions=checks_done)


def trace_fold16_tiled(out):
    """Exact 16-variable Ext4 multilinear fold (65,536 Ext4 elements = 65,535 pair folds)
    streamed through the 4-bank 512 KiB (65,536-word = 16,384-Ext4) SRAM in 4 subcube tiles!
    Checked bit-for-bit against the monolithic 16-variable Python reference fold!
    """
    e = Emu(f"{out}/trace_fold16.hex")
    chals = [[canon() for _ in range(4)] for _ in range(16)]
    table = [[rnd.randrange(P) for _ in range(4)] for _ in range(1 << 16)]

    # Reference monolithic 16-variable fold
    ref_cur = list(table)
    for r in chals:
        h = len(ref_cur) // 2
        # Note: in-place sequential pair fold pairs (2*i, 2*i+1): lo + r*(hi - lo)
        ref_cur = [R.ext4_muladd(R.ext4_sub(ref_cur[2 * i + 1], ref_cur[2 * i]), r, ref_cur[2 * i]) for i in range(h)]
    assert len(ref_cur) == 1
    expected_final = ref_cur[0]

    # Tiled hardware execution inside 512 KiB (AW=16, 16,384 Ext4 capacity):
    # Each tile t in 0..3 holds 2^14 = 16,384 contiguous Ext4 elements (65,536 words = full 512 KiB!).
    # Folding pairs (2*i, 2*i+1) for the first 14 challenges chals[0..13] reduces each tile to 1 Ext4!
    tile_outs = []
    total_folds = 0
    for t in range(4):
        sub_elems = table[t * (1 << 14):(t + 1) * (1 << 14)]
        e.wr_mem_burst(0x0000, [w for ext in sub_elems for w in ext])
        e.mark(0 if t == 0 else 1, t)
        pairs = (1 << 14) // 2
        for v in range(14):
            e.wr_all(chals[v], 4)
            e.fold(0x0000, pairs)
            total_folds += pairs
            pairs //= 2
        tile_outs.append([e.mem[j] for j in range(4)])

    # Fold the 4 tile scalars across chals[14] and chals[15]
    e.wr_mem_burst(0x0000, [w for ext in tile_outs for w in ext])
    for v, pairs in ((14, 2), (15, 1)):
        e.wr_all(chals[v], 4)
        e.fold(0x0000, pairs)
        total_folds += pairs

    assert total_folds == (1 << 16) - 1
    assert [e.mem[j] for j in range(4)] == expected_final
    e.mark(300, 16)
    e.wr_mem_burst(0x0100, expected_final)
    e.ld4(0, 0x0000)
    e.check_eq4(False, 0x0100, expect_match=True)
    e.rd4()
    e.close()
    return dict(nvars=16, pair_folds=total_folds, tiles=4, sram_kib=512)


if __name__ == "__main__":
    fixture, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    print("reference selfcheck:", R.selfcheck(fixture))
    fx = json.load(open(fixture))
    bundle_path = pathlib.Path(fixture).with_name("real_proof_bundle.json")
    bundle = json.load(open(bundle_path))
    unit_vectors(fx, out)
    trace_kat(fx, out)
    info = [
        trace_real_qsagsta1(bundle, out, "p2", tamper=False),
        trace_real_qsagsta1(bundle, out, "p2", tamper=True),
        trace_real_qsagsta1(bundle, out, "ts", tamper=False),
        trace_real_qsagsta1(bundle, out, "ts", tamper=True),
        trace_real_duet_component(bundle, out, tamper=False),
        trace_real_duet_component(bundle, out, tamper=True),
        trace_fold16_tiled(out),
    ]
    json.dump(info, open(f"{out}/workloads.json", "w"), indent=2)
    print(json.dumps(info, indent=2))
