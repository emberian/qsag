#!/usr/bin/env python3
"""Golden model of the QSAG-NI-180 wire protocol (QSAG-Wire v1).

Builds request word streams and the exact response word streams the chip must return, from the
primitive reference (qsag_prims.py), hashlib and the qsag Lean oracle fixture. It is written
from the protocol specification (README.md), independently of the RTL.
"""
import hashlib
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import qsag_prims as q  # noqa: E402

P = q.P
M64 = q.M64

OP_PING, OP_CSR, OP_P2, OP_MERKLE, OP_KECCAK = 0x01, 0x02, 0x10, 0x11, 0x20
OP_FOLD, OP_HEM, OP_KEYLOAD, OP_CTH, OP_PRFMSG = 0x30, 0x31, 0x40, 0x41, 0x42
E_MAGIC, E_OPCODE, E_LEN, E_NOKEY, E_MAC, E_ANCHOR_EMPTY, E_ROLLBACK, E_REUSE, E_ANCHOR_IO, E_KEYSET, E_TRNG = range(1, 12)
CHIP_ID = int.from_bytes(b"QSAGNI18", "little")
C_FRAM = int.from_bytes(b"QSAGNIFR", "little")
C_MASK = int.from_bytes(b"QSAGNIMK", "little")


def hdr(op, flags=0, length=0, arg=0):
    return 0x51 | (op << 8) | (flags << 16) | (length << 24) | (arg << 48)


def rhdr(op, length=0, ok=True, err=0):
    flags = (0x80 if err else 0) | (1 if (ok and not err) else 0)
    return 0x51 | ((op | 0x80) << 8) | (flags << 16) | (length << 24) | (err << 48)


def words_of(b):
    b = bytes(b) + bytes(-len(b) % 8)
    return [int.from_bytes(b[i:i + 8], "little") for i in range(0, len(b), 8)]


def bytes_of(ws):
    return b"".join(w.to_bytes(8, "little") for w in ws)


def error(op, code):
    return [rhdr(op, 0, False, code)]


# ---------------------------------------------------------------- stateless operations
def ping():
    """Response words; None = not checked by the model (live telemetry)."""
    return [hdr(OP_PING)], [rhdr(OP_PING, 32), CHIP_ID, None, None, None]


def csr_write(value):
    return [hdr(OP_CSR, 0, 8), value], [rhdr(OP_CSR, 0)]


def p2_raw(state):
    return [hdr(OP_P2, 1, 96)] + list(state), [rhdr(OP_P2, 96)] + q.p2_perm([x % P for x in state])


def p2_hash(domain, cap, limbs):
    req = [hdr(OP_P2, 0, 8 * (5 + len(limbs))), domain] + list(cap) + list(limbs)
    return req, [rhdr(OP_P2, 32)] + q.p2_sponge_hash_limbs(domain, cap, limbs)


def merkle(key3, leaf_index, leaf, siblings, root):
    depth = len(siblings)
    req = [hdr(OP_MERKLE, 0, 96 + 32 * depth, depth)] + list(key3) + [leaf_index] + list(leaf)
    for s in siblings:
        req += list(s)
    req += list(root)
    got = q.p2_canopy_path(leaf, siblings, key3, leaf_index)
    ok = got == [x % P for x in root]
    return req, [rhdr(OP_MERKLE, 40, ok), int(ok)] + got


def keccak(msg, out_words, suffix=0x1F, turbo=True):
    req = [hdr(OP_KECCAK, 1 if turbo else 0, len(msg), suffix | (out_words << 8))] + words_of(msg)
    out = q.sponge(msg, suffix, 8 * out_words, 12 if turbo else 24)
    return req, [rhdr(OP_KECCAK, 8 * out_words)] + words_of(out)


# ---------------------------------------------------------------- device state (keys, anchor)
class Device:
    """Enclave state the model tracks alongside the chip: keys, monotone counter, FRAM image."""

    def __init__(self):
        self.key = None            # (sk_seed, sk_prf, k_mac) as 16-byte strings
        self.hwm = None
        self.fram = bytearray(64)  # slot 0 at 0x00, slot 1 at 0x20 (24 bytes each)

    @property
    def delta(self):
        return int.from_bytes(self.key[2], "little")

    def ghash(self, acc, word):
        return q.gf128_mul(acc ^ word, self.delta)

    def fram_tag(self, ctr):
        return q.turboshake256(self.key[2] + ctr.to_bytes(8, "little") + b"QSAGNIFR", 16)

    def fram_record(self, ctr):
        return ctr.to_bytes(8, "little") + self.fram_tag(ctr)

    def fram_read(self, slot):
        rec = bytes(self.fram[32 * slot:32 * slot + 24])
        ctr = int.from_bytes(rec[:8], "little")
        return (ctr < 2**32 and rec[8:] == self.fram_tag(ctr)), ctr & 0xFFFFFFFF

    # -------------------------------------------------- key load (host-provisioned keys)
    def keyload_host(self, sk_seed, sk_prf, k_mac, anchor_init=True):
        flags = 1 | (2 if anchor_init else 0)
        req = [hdr(OP_KEYLOAD, flags, 48)] + words_of(k_mac) + words_of(sk_seed) + words_of(sk_prf)
        if self.key is not None:
            return req, error(OP_KEYLOAD, E_KEYSET)
        self.key = (bytes(sk_seed), bytes(sk_prf), bytes(k_mac))
        if anchor_init:
            for slot in (0, 1):
                self.fram[32 * slot:32 * slot + 24] = self.fram_record(0)
            self.hwm = 0
        return req, [rhdr(OP_KEYLOAD, 0)]

    def zeroize(self):
        self.key = None
        self.hwm = None

    # -------------------------------------------------- PRF_msg
    def prf_msg(self, payload):
        req = [hdr(OP_PRFMSG, 0, len(payload))] + words_of(payload)
        if self.key is None:
            return req, error(OP_PRFMSG, E_NOKEY)
        r = hashlib.shake_256(self.key[1] + bytes(payload)).digest(16)
        return req, [rhdr(OP_PRFMSG, 16)] + words_of(r)

    # -------------------------------------------------- Cut-the-Hash signing oracle
    def cth(self, leaf, layer, tree, adrs_type, keypair, pk_seed, symbols, sw, pubgen=False, stateful=False,
            bad_tag=False, tamper_request=False):
        """adrs_type: 0 WOTS (symbols = base-2^sw digits), 3 FORS (symbols = leaf indices)."""
        n = len(symbols)
        per_word = 64 // sw
        assert n <= 3 * per_word and all(0 <= s < (1 << sw) for s in symbols)
        symw = [0, 0, 0]
        for i, s in enumerate(symbols):
            symw[i // per_word] |= s << (sw * (i % per_word))
        a1 = int.from_bytes(tree.to_bytes(8, "big"), "little")
        a2 = int.from_bytes(adrs_type.to_bytes(4, "big") + keypair.to_bytes(4, "big"), "little")
        s = [leaf | (layer << 32)] + words_of(pk_seed) + [a1, a2] + symw
        flags = (1 if pubgen else 0) | (2 if stateful else 0)
        h = hdr(OP_CTH, flags, 80, n | (sw << 8))
        tag = [0, 0]
        if self.key is not None:
            acc = self.ghash(0, h)
            for w in s:
                acc = self.ghash(acc, w)
            mask = int.from_bytes(q.turboshake256(self.key[2] + s[0].to_bytes(8, "little") + b"QSAGNIMK", 16), "little")
            t = acc ^ mask
            tag = [t & M64, t >> 64]
        if bad_tag:
            tag[1] ^= 1 << 17
        sent = list(s)
        if tamper_request:
            sent[5] ^= 1  # a digit changes after the tag was issued
        req = [h] + sent + tag
        if self.key is None:
            return req, error(OP_CTH, E_NOKEY)
        if not pubgen and (bad_tag or tamper_request):
            return req, error(OP_CTH, E_MAC)
        if stateful and not pubgen:
            v0, c0 = self.fram_read(0)
            v1, c1 = self.fram_read(1)
            cur = c0
            older = 1
            if v1 and (not v0 or c1 >= c0):
                cur, older = c1, 0
            if not (v0 or v1):
                return req, error(OP_CTH, E_ANCHOR_EMPTY)
            if self.hwm is not None and cur < self.hwm:
                return req, error(OP_CTH, E_ROLLBACK)
            if leaf < cur or leaf == 0xFFFFFFFF:
                return req, error(OP_CTH, E_REUSE)
            self.fram[32 * older:32 * older + 24] = self.fram_record(leaf + 1)
            self.hwm = leaf + 1
        out = []
        for i, sym in enumerate(sent_symbols(sent[5:8], n, sw)):
            if adrs_type == 3:
                idx = (i << sw) | sym
                x = slh_prf(pk_seed, self.key[0], adrs(layer, tree, 6, keypair, 0, idx))
                if pubgen:
                    x = slh_f(pk_seed, adrs(layer, tree, 3, keypair, 0, idx), x)
            else:
                x = slh_prf(pk_seed, self.key[0], adrs(layer, tree, 5, keypair, i, 0))
                for j in range((1 << sw) - 1 if pubgen else sym):
                    x = slh_f(pk_seed, adrs(layer, tree, 0, keypair, i, j), x)
            out += words_of(x)
        return req, [rhdr(OP_CTH, 16 * n)] + out


def sent_symbols(symw, n, sw):
    per_word = 64 // sw
    return [(symw[i // per_word] >> (sw * (i % per_word))) & ((1 << sw) - 1) for i in range(n)]


# ---------------------------------------------------------------- FIPS 205 (SLH-DSA-SHAKE, n = 16)
def adrs(layer, tree, typ, keypair, chain, hash_):
    return (layer.to_bytes(4, "big") + tree.to_bytes(12, "big") + typ.to_bytes(4, "big") + keypair.to_bytes(4, "big")
            + chain.to_bytes(4, "big") + hash_.to_bytes(4, "big"))


def slh_prf(pk_seed, sk_seed, a):
    return hashlib.shake_256(pk_seed + a + sk_seed).digest(16)


def slh_f(pk_seed, a, m):
    return hashlib.shake_256(pk_seed + a + m).digest(16)


# ---------------------------------------------------------------- verifier VM
R_T0, R_CH, R_A, R_B, R_X, R_Y = range(6)
H_HASH, H_EMUL, H_EADD, H_ESUB, H_LOAD, H_ASSERT_EQ, H_ASSERT_POW, H_MERKLE, H_BIND_IDX = range(1, 10)


class Hvm:
    """Assembler and interpreter for the verifier VM (opcodes 0x30 / 0x31)."""

    def __init__(self, dev, op=OP_HEM):
        self.dev, self.op = dev, op
        self.recs = []          # (header fields, data words, number of immediates)
        self.reg = {r: [0, 0, 0, 0] for r in range(6)}

    def rec(self, hop, a=0, b=0, c=0, data=(), k=0):
        self.recs.append([hop, a, b, c, list(data), k])

    # --- assembler helpers (transcript operations of qsag-agg's Poseidon2 Fiat-Shamir) ---
    def hash(self, dst, cap, domain, imm, proof=(), latch=0, skip=0):
        """dst <- sponge_hash_limbs(domain, cap, imm ++ proof); cap = register or 'init'."""
        c = (latch & 7) | (8 if cap == "init" else 0) | (skip << 4)
        self.rec(H_HASH, dst, 0 if cap == "init" else cap, c, [domain] + list(imm) + list(proof), 1 + len(imm))

    def absorb_limbs(self, label, limbs, latch=0, skip=0):
        self.hash(R_CH, R_CH, q.P2_DOMAIN_FS_ABSORB_LIMBS, q.pack_bytes_7_limbs(label), limbs, latch, skip)

    def squeeze_ext4(self, dst, label, counter):
        self.hash(dst, R_CH, q.P2_DOMAIN_FS_SQUEEZE_EXT4, q.pack_bytes_7_limbs(label) + [counter])

    def load(self, dst, val, imm=False):
        self.rec(H_LOAD, dst, 0, 0, val, 4 if imm else 0)

    def emul(self, d, a, b):
        self.rec(H_EMUL, d, a, b)

    def eadd(self, d, a, b):
        self.rec(H_EADD, d, a, b)

    def esub(self, d, a, b):
        self.rec(H_ESUB, d, a, b)

    def assert_eq(self, a, b):
        self.rec(H_ASSERT_EQ, 0, a, b)

    def assert_pow(self, a, bits):
        self.rec(H_ASSERT_POW, 0, a, bits)

    def bind_idx(self, reg, limb, bits):
        self.rec(H_BIND_IDX, limb, reg, bits)

    def merkle(self, key_reg, leaf_index, siblings):
        self.rec(H_MERKLE, len(siblings), key_reg, 0, [leaf_index] + [x for s in siblings for x in s])

    # --- stream and interpreter ---
    def request(self, mutate=None):
        words = []
        for hop, a, b, c, data, k in self.recs:
            words.append(hop | (a << 8) | (b << 16) | (c << 24) | (len(data) << 32) | (k << 48))
            words += data
        if mutate:
            mutate(words)
        return [hdr(self.op, 0, 8 * len(words))] + words

    def run(self, req):
        """Execute a request stream exactly as the chip does; returns the response words."""
        dev = self.dev
        keyed = dev.key is not None
        delta = dev.delta if keyed else 0
        kmac = dev.key[2] if keyed else bytes(16)
        reg = {r: [0, 0, 0, 0] for r in range(6)}
        ws = req[1:]
        pdig = q.gf128_mul(req[0], delta)
        fail = noncanon = False
        fidx = recidx = 0
        lidx, armed = 0, False
        i = 0
        while i < len(ws):
            h = ws[i]
            i += 1
            pdig = q.gf128_mul(pdig ^ h, delta)
            hop = h & 0xFF if (h & 0xF0) == 0 else 15
            a, b, c = (h >> 8) & 0xFF, (h >> 16) & 0xFF, (h >> 24) & 0xFF
            n, k = (h >> 32) & 0xFFFF, (h >> 48) & 0xFFFF
            data = ws[i:i + n]
            i += n
            recidx += 1
            bad = False

            def bound(cnt):  # immediates among the first cnt consumed data words
                nonlocal pdig
                for w in data[:min(cnt, k)]:
                    pdig = q.gf128_mul(pdig ^ w, delta)

            def canon_chk(vals, first):  # proof words (not immediates) must be canonical
                nonlocal noncanon
                for j, v in enumerate(vals):
                    if first + j >= k and v >= P:
                        noncanon = True

            if hop == H_HASH:
                if n == 0:
                    bad = True
                else:
                    bound(n)
                    canon_chk(data[1:], 1)
                    cap = q.FS_INIT_CAP if c & 8 else reg[b & 7]
                    limbs = [x % P for x in data[1:]]
                    res = q.p2_sponge_hash_limbs(data[0], cap, limbs)
                    latch, skip = c & 7, (c >> 4) & 3
                    if latch and len(limbs) >= 1:
                        cur = list(reg[latch])
                        for pos in range(4):  # limb at distance skip + 4 - pos from the end
                            src = len(limbs) - skip - 4 + pos
                            if src >= 0:
                                cur[pos] = limbs[src]
                        reg[latch] = cur
                    reg[R_T0] = res
                    if a & 7:
                        reg[a & 7] = res
            elif hop in (H_EMUL, H_EADD, H_ESUB):
                f = {H_EMUL: q.ext4_mul, H_EADD: q.ext4_add, H_ESUB: q.ext4_sub}[hop]
                reg[a & 7] = f(reg[b & 7], reg[c & 7])
            elif hop == H_LOAD:
                if n != 4:
                    bad = True
                else:
                    bound(4)
                    canon_chk(data, 0)
                    reg[a & 7] = [x % P for x in data]
            elif hop == H_ASSERT_EQ:
                bad = reg[b & 7] != reg[c & 7]
            elif hop == H_ASSERT_POW:
                bits = min(c & 63, 32)
                bad = (reg[b & 7][0] & ((1 << bits) - 1)) != 0
            elif hop == H_MERKLE:
                depth = a & 63
                if depth == 0 or depth > 32 or n != 1 + 4 * depth:
                    bad = True
                else:
                    idx = data[0] & 0xFFFFFFFF
                    if armed and idx != lidx:
                        bad = True
                    armed = False
                    sibs = [data[1 + 4 * j:5 + 4 * j] for j in range(depth)]
                    for sgl in sibs:
                        if any(v >= P for v in sgl):
                            noncanon = True
                    reg[R_X] = q.p2_canopy_path(reg[R_X], sibs, reg[b & 7][:3], idx)
                    reg[R_Y] = [x % P for x in sibs[-1]]
            elif hop == H_BIND_IDX:
                bits = min(c & 63, 32)
                lidx = reg[b & 7][a & 3] & 0xFFFFFFFF & ((1 << bits) - 1)
                armed = True
            else:
                bad = True
            if bad:
                fail = True
            if fail and not fidx:
                fidx = recidx
        verdict = not fail and not noncanon
        stat = int(verdict) | (int(noncanon) << 1) | (int(keyed) << 2) | (fidx << 16) | (recidx << 32) | (self.op << 48)
        msg = kmac + stat.to_bytes(8, "little") + pdig.to_bytes(16, "little") + bytes_of(reg[R_CH])
        receipt = q.turboshake256(msg, 32)
        return [rhdr(self.op, 72, verdict), stat] + words_of(receipt) + list(reg[R_CH])
