#!/usr/bin/env python3
"""Golden model of the Dregg-180 (QSAG-NI-180) wire protocol & Houyhnhnm Enclave.

Builds request word streams and the exact response word streams the chip must return, from the
primitive reference (qsag_prims.py), hashlib, and the qsag Lean oracle fixture.
"""
import hashlib
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import qsag_prims as q  # noqa: E402

P = q.P
M64 = q.M64

OP_PING, OP_CSR, OP_BIST = 0x01, 0x02, 0x03
OP_P2, OP_MERKLE, OP_KECCAK = 0x10, 0x11, 0x20
OP_FOLD, OP_HEM, OP_KEYLOAD, OP_CTH, OP_PRFMSG = 0x30, 0x31, 0x40, 0x41, 0x42
OP_PUF, OP_VAT, OP_DB_NCO, OP_VAT_ZK = 0x50, 0x51, 0x52, 0x53

(E_MAGIC, E_OPCODE, E_LEN, E_NOKEY, E_MAC, E_ANCHOR_EMPTY, E_ROLLBACK,
 E_REUSE, E_ANCHOR_IO, E_KEYSET, E_TRNG, E_PUF, E_CAP, E_LOCKED) = range(1, 15)

CHIP_ID = int.from_bytes(b"QSAGNI18", "little")
C_FRAM = int.from_bytes(b"QSAGNIFR", "little")
C_MASK = int.from_bytes(b"QSAGNIMK", "little")
C_PUF = int.from_bytes(b"DREGGPUF", "little")
C_PUF_CHK = int.from_bytes(b"DREGGCHK", "little")
C_VAT = int.from_bytes(b"DREGGVAT", "little")
C_ZKG = int.from_bytes(b"DREGGZKG", "little")
C_NFC = int.from_bytes(b"DREGGNFC", "little")
H_ZK_PIN = 0x9E3779B97F4A7C15_504F53325F474C31


def hdr(op, flags=0, length=0, arg=0):
    return 0x51 | (op << 8) | (flags << 16) | (length << 24) | (arg << 48)


def rhdr(op, length=0, ok=True, err=0):
    flags = (0x80 if err else 0) | (1 if (ok and not err) else 0)
    return 0x51 | ((op | 0x80) << 8) | (flags << 16) | (length << 24) | (err << 48)


def words_of(b):
    b = bytes(b) + bytes(-len(b) % 8)
    return [int.from_bytes(b[i:i + 8], "little") for i in range(0, len(b), 8)]


def bytes_of(ws):
    return b"".join((w & M64).to_bytes(8, "little") for w in ws)


def error(op, code):
    return [rhdr(op, 0, False, code)]


# ---------------------------------------------------------------- stateless operations
def ping():
    return [hdr(OP_PING)], [rhdr(OP_PING, 32), CHIP_ID, None, None, None]


def csr_write(value):
    return [hdr(OP_CSR, 0, 8), value], [rhdr(OP_CSR, 0)]


def p2_raw(state):
    return [hdr(OP_P2, 1, 96)] + list(state), [rhdr(OP_P2, 96)] + q.p2_perm([x % P for x in state])


def p2_hash(domain, cap, limbs):
    req = [hdr(OP_P2, 0, 8 * (5 + len(limbs))), domain] + list(cap) + list(limbs)
    return req, [rhdr(OP_P2, 32)] + q.p2_sponge_hash_limbs(domain, cap, limbs)


def p2_rate6(limbs):
    req = [hdr(OP_P2, 2, 8 * len(limbs))] + list(limbs)
    return req, [rhdr(OP_P2, 48)] + q.sponge12_rate6(limbs)[:6]


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


# ---------------------------------------------------------------- NFC authenticated frame builder
def crc16_iso14443a_msb(bits144):
    crc = 0x6363
    for b in bits144:
        fb = ((crc >> 15) ^ b) & 1
        crc = ((crc << 1) & 0xFFFF) ^ (0x1021 if fb else 0)
    return [(crc >> (15 - i)) & 1 for i in range(16)]


def nfc_mac96(kvat_bytes, seq, quorum_flags, bind_lo, bind_hi):
    blk = (b"DREGGNFC" + bytes(kvat_bytes)
           + (seq | (quorum_flags << 48)).to_bytes(8, "little")
           + (bind_lo & M64).to_bytes(8, "little")
           + (bind_hi & M64).to_bytes(8, "little"))
    raw = q.turboshake256(blk, 16)
    w0 = int.from_bytes(raw[:8], "little")
    w1 = int.from_bytes(raw[8:12], "little")
    return w0 | (w1 << 64)


# ---------------------------------------------------------------- device state (keys, vat, anchor)
class Device:
    def __init__(self):
        self.key = None            # (sk_seed, sk_prf, k_mac) as 16-byte strings
        self.kvat = None           # 32-byte vat root key
        self.mint_locked = False
        self.vat_spend_used = 0
        self.zk_pin = None         # 4 x u64 (prog_digest_lo, prog_digest_hi, ch_pin0, ch_pin1)
        self.hwm = None
        self.fram = bytearray(64)

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

    def keyload_host(self, sk_seed, sk_prf, k_mac, anchor_init=True, kvat=None):
        flags = 1 | (2 if anchor_init else 0) | (4 if kvat is not None else 0)
        extra = words_of(kvat) if kvat is not None else []
        req = [hdr(OP_KEYLOAD, flags, 80 if kvat is not None else 48)] + words_of(k_mac) + words_of(sk_seed) + words_of(sk_prf) + extra
        if self.key is not None:
            return req, error(OP_KEYLOAD, E_KEYSET)
        self.key = (bytes(sk_seed), bytes(sk_prf), bytes(k_mac))
        if kvat is not None:
            self.kvat = bytes(kvat)
            self.vat_spend_used = 0
        if anchor_init:
            for slot in (0, 1):
                self.fram[32 * slot:32 * slot + 24] = self.fram_record(0)
            self.hwm = 0
        return req, [rhdr(OP_KEYLOAD, 0)]

    def zeroize(self):
        self.key = None
        self.kvat = None
        self.mint_locked = False
        self.vat_spend_used = 0
        self.zk_pin = None
        self.hwm = None

    # -------------------------------------------------- SpongeMacaroon seal & CapTP Vat
    def macaroon_seal(self, desc8):
        msg = b"DREGGVAT" + self.kvat + bytes_of(desc8)
        return words_of(q.turboshake256(msg, 32))

    def vat_mint(self, desc8, lock_mint=False):
        flags = 8 if lock_mint else 0
        req = [hdr(OP_VAT, flags, 64)] + list(desc8)
        if self.kvat is None:
            return req, error(OP_VAT, E_NOKEY)
        if self.mint_locked:
            return req, error(OP_VAT, E_LOCKED)
        if lock_mint:
            self.mint_locked = True
        mac = list(desc8) + self.macaroon_seal(desc8)
        return req, [rhdr(OP_VAT, 96)] + mac

    def vat_attenuate(self, parent_mac12, child_desc8, bad_seal=False):
        sent_p = list(parent_mac12)
        if bad_seal:
            sent_p[9] ^= 1
        req = [hdr(OP_VAT, 1, 160)] + sent_p + list(child_desc8)
        if self.kvat is None:
            return req, error(OP_VAT, E_NOKEY)
        if sent_p[8:] != self.macaroon_seal(sent_p[:8]):
            return req, error(OP_VAT, E_MAC)
        pw = sent_p[:8]
        cw = child_desc8
        p_rights, p_guards, p_maxd = pw[1] & 0xFFFF, (pw[1] >> 16) & 0xFFFF, pw[1] >> 32
        c_rights, c_guards, c_maxd = cw[1] & 0xFFFF, (cw[1] >> 16) & 0xFFFF, cw[1] >> 32
        p_ef, p_ec = pw[2] & 0xFFFFFFFF, pw[2] >> 32
        c_ef, c_ec = cw[2] & 0xFFFFFFFF, cw[2] >> 32
        p_sp, c_sp = pw[3] & 0xFFFFFFFF, cw[3] & 0xFFFFFFFF
        vk_pinned = bool((p_guards & 8) or any(x != 0 for x in pw[4:8]))
        ok = (bool(p_rights & 8)
              and (c_rights & ~p_rights) == 0
              and (c_guards & p_guards) == p_guards
              and c_maxd <= p_maxd
              and c_ef >= p_ef and c_ec <= p_ec and c_ef <= c_ec
              and 0 < c_sp <= p_sp
              and (not vk_pinned or list(cw[4:8]) == list(pw[4:8])))
        if not ok:
            return req, error(OP_VAT, E_CAP)
        return req, [rhdr(OP_VAT, 96)] + list(cw) + self.macaroon_seal(cw)

    def vat_invoke_zk(self, mac12, epoch=0):
        req = [hdr(OP_VAT_ZK, 0, 96, epoch)] + list(mac12)
        if self.kvat is None:
            return req, error(OP_VAT_ZK, E_NOKEY)
        if list(mac12[8:]) != self.macaroon_seal(mac12[:8]):
            return req, error(OP_VAT_ZK, E_MAC)
        pw = mac12[:8]
        p_rights = pw[1] & 0xFFFF
        p_ef, p_ec = pw[2] & 0xFFFFFFFF, pw[2] >> 32
        p_sp = pw[3] & 0xFFFFFFFF
        if not (p_rights & 4) or not (p_ef <= epoch <= p_ec) or self.vat_spend_used + 1 > p_sp:
            return req, error(OP_VAT_ZK, E_CAP)
        if self.zk_pin is None or list(pw[4:8]) != list(self.zk_pin):
            return req, error(OP_VAT_ZK, E_CAP)
        self.vat_spend_used += 1
        grant = q.turboshake256(b"DREGGZKG" + self.kvat + epoch.to_bytes(8, "little") + bytes_of(self.zk_pin), 32)
        return req, [rhdr(OP_VAT_ZK, 32)] + words_of(grant)

    # -------------------------------------------------- Authenticated PRF_msg
    def prf_msg(self, payload, bad_tag=False, tamper_request=False):
        payload = bytes(payload)
        pwords = words_of(payload)
        h = hdr(OP_PRFMSG, 0, len(payload) + 16)
        tag = [0, 0]
        if self.key is not None:
            acc = self.ghash(0, h)
            for w in pwords:
                acc = self.ghash(acc, w)
            mask = int.from_bytes(q.turboshake256(self.key[2] + h.to_bytes(8, "little") + b"QSAGNIMK", 16), "little")
            t = acc ^ mask
            tag = [t & M64, t >> 64]
        if bad_tag:
            tag[0] ^= 1 << 13
        sent = list(pwords)
        if tamper_request and sent:
            sent[0] ^= 1
        req = [h] + sent + tag
        if self.key is None:
            return req, error(OP_PRFMSG, E_NOKEY)
        if self.kvat is not None:
            return req, error(OP_PRFMSG, E_CAP)
        if bad_tag or (tamper_request and sent):
            return req, error(OP_PRFMSG, E_MAC)
        r = hashlib.shake_256(self.key[1] + payload).digest(16)
        return req, [rhdr(OP_PRFMSG, 16)] + words_of(r)

    def prf_msg_cap(self, mac12, payload, epoch=0):
        payload = bytes(payload)
        req = [hdr(OP_PRFMSG, 4, 96 + len(payload), epoch)] + list(mac12) + words_of(payload)
        if self.key is None or self.kvat is None:
            return req, error(OP_PRFMSG, E_NOKEY)
        if list(mac12[8:]) != self.macaroon_seal(mac12[:8]):
            return req, error(OP_PRFMSG, E_MAC)
        pw = mac12[:8]
        p_rights = pw[1] & 0xFFFF
        p_ef, p_ec = pw[2] & 0xFFFFFFFF, pw[2] >> 32
        p_sp = pw[3] & 0xFFFFFFFF
        if not (p_rights & 2) or not (p_ef <= epoch <= p_ec) or self.vat_spend_used + 1 > p_sp:
            return req, error(OP_PRFMSG, E_CAP)
        self.vat_spend_used += 1
        r = hashlib.shake_256(self.key[1] + payload).digest(16)
        return req, [rhdr(OP_PRFMSG, 16)] + words_of(r)

    # -------------------------------------------------- Cut-the-Hash signing oracle
    def cth(self, leaf, layer, tree, adrs_type, keypair, pk_seed, symbols, sw, pubgen=False, stateful=False,
            bad_tag=False, tamper_request=False):
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
            sent[5] ^= 1
        req = [h] + sent + tag
        if self.key is None:
            return req, error(OP_CTH, E_NOKEY)
        if self.kvat is not None:
            return req, error(OP_CTH, E_CAP)
        if bad_tag or tamper_request:
            return req, error(OP_CTH, E_MAC)
        if pubgen and adrs_type != 3 and sw != 4:
            return req, error(OP_CTH, E_LEN)
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


def adrs(layer, tree, typ, keypair, chain, hash_):
    return (layer.to_bytes(4, "big") + tree.to_bytes(12, "big") + typ.to_bytes(4, "big") + keypair.to_bytes(4, "big")
            + chain.to_bytes(4, "big") + hash_.to_bytes(4, "big"))


def slh_prf(pk_seed, sk_seed, a):
    return hashlib.shake_256(pk_seed + a + sk_seed).digest(16)


def slh_f(pk_seed, a, m):
    return hashlib.shake_256(pk_seed + a + m).digest(16)


# ---------------------------------------------------------------- verifier VM (Ext4 + Fp5)
R_T0, R_CH, R_A, R_B, R_X, R_Y = range(6)
H_HASH, H_EMUL, H_EADD, H_ESUB, H_LOAD, H_ASSERT_EQ, H_ASSERT_POW, H_MERKLE, H_BIND_IDX = range(1, 10)


class Hvm:
    """Assembler and interpreter for the verifier VM (opcodes 0x30 / 0x31)."""

    def __init__(self, dev, op=OP_HEM, pin_mode=False, fp5_mode=False):
        self.dev, self.op = dev, op
        self.pin_mode = pin_mode
        self.fp5_mode = fp5_mode and (op == OP_HEM)
        self.limbs = 5 if self.fp5_mode else 4
        self.recs = []

    def rec(self, hop, a=0, b=0, c=0, data=(), k=0):
        self.recs.append([hop, a, b, c, list(data), k])

    def hash(self, dst, cap, domain, imm, proof=(), latch=0, skip=0):
        c = (latch & 7) | (8 if cap == "init" else 0) | (skip << 4)
        self.rec(H_HASH, dst, 0 if cap == "init" else cap, c, [domain] + list(imm) + list(proof), 1 + len(imm))

    def hash_rate6(self, dst, imm, proof=(), latch=0, skip=0):
        c = (latch & 7) | (skip << 4) | 0x40
        self.rec(H_HASH, dst, 0, c, list(imm) + list(proof), len(imm))

    def absorb_limbs(self, label, limbs, latch=0, skip=0):
        self.hash(R_CH, R_CH, q.P2_DOMAIN_FS_ABSORB_LIMBS, q.pack_bytes_7_limbs(label), limbs, latch, skip)

    def squeeze_ext4(self, dst, label, counter):
        self.hash(dst, R_CH, q.P2_DOMAIN_FS_SQUEEZE_EXT4, q.pack_bytes_7_limbs(label) + [counter])

    def load(self, dst, val, imm=False):
        self.rec(H_LOAD, dst, 0, 0, val, self.limbs if imm else 0)

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

    def request(self, mutate=None):
        words = []
        for hop, a, b, c, data, k in self.recs:
            words.append(hop | (a << 8) | (b << 16) | (c << 24) | (len(data) << 32) | (k << 48))
            words += data
        if mutate:
            mutate(words)
        flags = (8 if self.pin_mode else 0) | (16 if self.fp5_mode else 0)
        return [hdr(self.op, flags, 8 * len(words))] + words

    def run(self, req):
        dev = self.dev
        keyed = dev.key is not None
        flags = (req[0] >> 16) & 0xFF
        pin_mode = bool(flags & 8)
        fp5_mode = (self.op == OP_HEM) and bool(flags & 16)
        L = 5 if fp5_mode else 4
        delta = H_ZK_PIN if pin_mode else (dev.delta if keyed else 0)
        kmac = dev.key[2] if keyed else bytes(16)
        dev.zk_pin = None

        reg = {r: [0] * L for r in range(6)}
        ws = req[1:]
        pdig = q.gf128_mul(req[0], delta)
        fail = noncanon = has_assert = False
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

            def bound(cnt):
                nonlocal pdig
                for w in data[:min(cnt, k)]:
                    pdig = q.gf128_mul(pdig ^ w, delta)

            def canon_chk(vals, first):
                nonlocal noncanon
                for j, v in enumerate(vals):
                    if first + j >= k and v >= P:
                        noncanon = True

            if hop == H_HASH:
                if c & 0x40:  # sponge12_rate6
                    bound(n)
                    canon_chk(data, 0)
                    limbs = [x % P for x in data]
                    res = q.sponge12_rate6(limbs)[:L]
                    latch, skip = c & 7, (c >> 4) & 3
                    if latch and len(limbs) >= 1:
                        cur = list(reg[latch])
                        for pos in range(L):
                            src = len(limbs) - skip - L + pos
                            if src >= 0:
                                cur[pos] = limbs[src]
                        reg[latch] = cur
                    reg[R_T0] = res
                    if a & 7:
                        reg[a & 7] = list(res)
                elif n == 0:
                    bad = True
                else:
                    bound(n)
                    canon_chk(data[1:], 1)
                    cap = q.FS_INIT_CAP if c & 8 else reg[b & 7][:4]
                    limbs = [x % P for x in data[1:]]
                    res4 = q.p2_sponge_hash_limbs(data[0], cap, limbs)
                    res = res4 + ([0] if L == 5 else [])
                    latch, skip = c & 7, (c >> 4) & 3
                    if latch and len(limbs) >= 1:
                        cur = list(reg[latch])
                        for pos in range(L):
                            src = len(limbs) - skip - L + pos
                            if src >= 0:
                                cur[pos] = limbs[src]
                        reg[latch] = cur
                    reg[R_T0] = list(res)
                    if a & 7:
                        reg[a & 7] = list(res)
            elif hop in (H_EMUL, H_EADD, H_ESUB):
                if fp5_mode:
                    f = {H_EMUL: q.fp5_mul, H_EADD: q.fp5_add, H_ESUB: q.fp5_sub}[hop]
                else:
                    f = {H_EMUL: q.ext4_mul, H_EADD: q.ext4_add, H_ESUB: q.ext4_sub}[hop]
                reg[a & 7] = f(reg[b & 7], reg[c & 7])
            elif hop == H_LOAD:
                if n != L or (pin_mode and (a & 7) == R_CH):
                    bad = True
                else:
                    bound(L)
                    canon_chk(data, 0)
                    reg[a & 7] = [x % P for x in data]
            elif hop == H_ASSERT_EQ:
                has_assert = True
                bad = reg[b & 7] != reg[c & 7]
            elif hop == H_ASSERT_POW:
                has_assert = True
                bits = min(c & 63, 32)
                bad = (reg[b & 7][0] & ((1 << bits) - 1)) != 0
            elif hop == H_MERKLE:
                has_assert = True
                depth = a & 63
                if depth == 0 or depth > 32 or n != 1 + 4 * depth:
                    bad = True
                else:
                    idx = data[0]
                    if (idx >> 32) != 0 or (armed and idx != lidx):
                        bad = True
                    armed = False
                    sibs = [data[1 + 4 * j:5 + 4 * j] for j in range(depth)]
                    for sgl in sibs:
                        if any(v >= P for v in sgl):
                            noncanon = True
                    out4 = q.p2_canopy_path(reg[R_X][:4], sibs, reg[b & 7][:3], idx & 0xFFFFFFFF)
                    reg[R_X][:4] = out4
                    reg[R_Y][:4] = [x % P for x in sibs[-1]]
            elif hop == H_BIND_IDX:
                bits = min(c & 63, 32)
                lidx = reg[b & 7][a & 3] & ((1 << bits) - 1)
                armed = True
            else:
                bad = True
            if bad:
                fail = True
            if fail and not fidx:
                fidx = recidx

        verdict = (not fail) and (not noncanon) and has_assert and (recidx != 0)
        ch = reg[R_CH]
        if pin_mode and verdict:
            ch_p0 = ch[0] ^ ch[2] ^ (ch[4] if L == 5 else 0)
            ch_p1 = ch[1] ^ ch[3]
            dev.zk_pin = [pdig & M64, pdig >> 64, ch_p0, ch_p1]
        stat = int(verdict) | (int(noncanon) << 1) | (int(keyed) << 2) | (fidx << 16) | (recidx << 32) | (self.op << 48)
        msg = kmac + stat.to_bytes(8, "little") + pdig.to_bytes(16, "little") + bytes_of(ch)
        receipt = q.turboshake256(msg, 32)
        return [rhdr(self.op, 8 * (5 + L), verdict), stat] + words_of(receipt) + list(ch)
