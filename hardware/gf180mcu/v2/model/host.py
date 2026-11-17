"""Host side of QSAG-Wire as the v2 model speaks it: request builders, the references the tests compare
against, and the off-chip parties (owner root, authority, committee members, the enrolment station).

The FIPS 205 code here (SLH-DSA-SHAKE, n = 16) is built on hashlib and written from the standard's
algorithms; it shares nothing with the microcode. It has not been compared with `crates/qsag-core`.
"""
import functools
import hashlib
import os
import sys

sys.path.insert(0, os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "model")))
import qsag_prims as q  # noqa: E402

(OP_PING, OP_P2, OP_MERKLE, OP_KECCAK, OP_CTH, OP_PRFMSG, OP_NONCE, OP_BOOT, OP_ENROL, OP_COMMIT, OP_REINIT, OP_LEASE,
 OP_GATE) = 0x01, 0x10, 0x11, 0x20, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49
(E_MAGIC, E_OPCODE, E_LEN, E_NOKEY, E_MAC, E_6, E_7, E_REUSE, E_RECORD_IO, E_10, E_TRNG, E_AUTH, E_CLASS, E_STATE,
 E_LEASE, E_PUF, E_RETIRED, E_ARG) = range(1, 19)
# TurboSHAKE256 domain bytes
(D_FRAM, D_REQ, D_STMT, D_KDF, D_LEAF, D_NODE, D_CH, D_PT, D_NONCE, D_PUFCHK, D_KDEV) = (
    0x1F, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A)
M64 = (1 << 64) - 1
# lifecycle states and policy flags (ARCHITECTURE.md 3.1, 3.2)
LC_RESET, LC_BLANK, LC_ORPHAN, LC_LEASE, LC_READY, LC_LOCKED = range(6)
F_VAT, F_LEASED, F_COUNTED, F_MINTLOCK, F_RETIRED = 1, 2, 4, 8, 16
T_LEASE, T_EPOCH, T_RETIRE, T_ROTATE = 1, 2, 3, 4


def label(text):
    assert len(text) == 8
    return int.from_bytes(text.encode(), "little")


L_TR, L_CM, L_RI, L_REC = label("DREGG.TR"), label("DREGG.CM"), label("DREGG.RI"), label("DREGGREC")
L_HOST, L_SEED, L_PRF, L_PUFCHK, L_KDEV = (label("DREGGKHO"), label("DREGGSKS"), label("DREGGSKP"), label("DREGGPCK"),
                                           label("DREGGKDV"))


def hdr(op, flags=0, length=0, arg=0):
    return 0x51 | (op << 8) | (flags << 16) | (length << 24) | (arg << 48)


def rhdr(op, length=0, ok=True, err=0):
    flags = (0x80 if err else 0) | (1 if (ok and not err) else 0)
    return 0x51 | ((op | 0x80) << 8) | (flags << 16) | (length << 24) | (err << 48)


def err(op, code):
    return [rhdr(op, 0, False, code)]


def words_of(b):
    b = bytes(b) + bytes(-len(b) % 8)
    return [int.from_bytes(b[i:i + 8], "little") for i in range(0, len(b), 8)]


def bytes_of(ws):
    return b"".join((w & M64).to_bytes(8, "little") for w in ws)


def ts(words, domain, nbytes=16):
    """TurboSHAKE256 over whole words, as the microcode builds it in the lanes. Returns words."""
    return words_of(q.turboshake256(bytes_of(words), nbytes, domain))


def cmd(op, payload=(), flags=0, arg=0):
    return [hdr(op, flags, 8 * len(payload), arg)] + list(payload)


def keccak(msg, out_words, suffix=0x1F, turbo=True):
    return [hdr(OP_KECCAK, 1 if turbo else 0, len(msg), suffix | (out_words << 8))] + words_of(msg)


# ---------------------------------------------------------------- keys the chip derives
def puf_tag(w):
    return ts(list(w) + [L_PUFCHK], D_PUFCHK)


def k_dev(w, nonce):
    return ts(list(w) + [L_KDEV] + list(nonce), D_KDEV, 32)


def derive(kdev, lab):
    """A key derived on use: TurboSHAKE256(K_dev || label)[0..15], as bytes."""
    return bytes_of(ts(list(kdev) + [lab], D_KDF))


def record_tag(kdev, rec5):
    return ts(list(kdev) + [L_REC] + list(rec5), D_FRAM)


def record_bytes(kdev, rec5):
    return bytes_of(list(rec5) + record_tag(kdev, rec5))


def commit_word(u0=0, gen=0, flags=0, k=1):
    return (u0 & 0xFFFFFFFF) | (gen << 32) | (flags << 48) | (k << 56)


def rec0(seq, gen, flags, k):
    return seq | (gen << 32) | (flags << 48) | (k << 56)


# ---------------------------------------------------------------- statements
def stmt_transition(tag, r0, typ, nonce, args):
    """tag: the chip's PUF check tag (2 words), its public identifier."""
    args = (list(args) + [0, 0, 0])[:3]
    return bytes_of(ts([L_TR] + list(tag) + [r0, typ] + list(nonce) + args, D_STMT, 32))


def stmt_owner(lab, nonce, syn, tag, cw, pin):
    return bytes_of(ts([lab] + list(nonce) + list(syn) + list(tag) + [cw] + list(pin), D_STMT, 32))


# ---------------------------------------------------------------- signer requests
def prf_msg(payload):
    return [hdr(OP_PRFMSG, 0, len(payload))] + words_of(payload)


def request_tag(k_host, words):
    """Tag of a CTH request: TurboSHAKE256(K_host || header || s0..s8, D = 0x21)[0..15]."""
    return words_of(q.turboshake256(bytes(k_host) + bytes_of(words), 16, D_REQ))


def cth(k_host, leaf, layer, tree, adrs_type, keypair, pk_seed, body, n, first=0, pubgen=False):
    """body: four words (WOTS: the 16-byte message in the first two; FORS: 16-bit leaf indices)."""
    a1 = int.from_bytes(tree.to_bytes(8, "big"), "little")
    a2 = int.from_bytes(adrs_type.to_bytes(4, "big") + keypair.to_bytes(4, "big"), "little")
    flags = 1 if pubgen else 0
    req = [hdr(OP_CTH, flags, 88, n | (first << 8)), leaf | (layer << 32)] + words_of(pk_seed) + [a1, a2] + list(body)
    assert len(req) == 10
    return req + (request_tag(k_host, req) if k_host is not None else [0, 0])


def cth_wots(k_host, leaf, layer, tree, keypair, pk_seed, msg16, n, first=0, **kw):
    assert len(msg16) == 16
    return cth(k_host, leaf, layer, tree, 0, keypair, pk_seed, words_of(msg16) + [0, 0], n, first, **kw)


def cth_fors(k_host, leaf, layer, tree, keypair, pk_seed, indices, **kw):
    assert len(indices) <= 16 and all(0 <= i < 65536 for i in indices)
    body = [0, 0, 0, 0]
    for i, v in enumerate(indices):
        body[i // 4] |= v << (16 * (i % 4))
    return cth(k_host, leaf, layer, tree, 3, keypair, pk_seed, body, len(indices), **kw)


# ---------------------------------------------------------------- FIPS 205 reference (hashlib)
def adrs(layer, tree, typ, keypair, chain, hash_):
    return (layer.to_bytes(4, "big") + tree.to_bytes(12, "big") + typ.to_bytes(4, "big") + keypair.to_bytes(4, "big")
            + chain.to_bytes(4, "big") + hash_.to_bytes(4, "big"))


def slh_prf(pk_seed, sk_seed, a):
    return hashlib.shake_256(pk_seed + a + sk_seed).digest(16)


def slh_f(pk_seed, a, m):
    return hashlib.shake_256(pk_seed + a + m).digest(16)


def wots_digits(msg16):
    """FIPS 205 Algorithm 7 lines 1-7 for n = 16, lg_w = 4: 32 message digits and 3 checksum digits."""
    d = []
    for byte in msg16:
        d += [byte >> 4, byte & 15]
    csum = sum(15 - x for x in d) << 4
    for byte in csum.to_bytes(2, "big"):
        d += [byte >> 4, byte & 15]
    return d[:35]


def wots_chain(pk_seed, sk_seed, layer, tree, keypair, i, steps, start=0, value=None):
    x = slh_prf(pk_seed, sk_seed, adrs(layer, tree, 5, keypair, i, 0)) if value is None else value
    for j in range(start, start + steps):
        x = slh_f(pk_seed, adrs(layer, tree, 0, keypair, i, j), x)
    return x


def fors_leaf(pk_seed, sk_seed, layer, tree, keypair, idx, public=False):
    x = slh_prf(pk_seed, sk_seed, adrs(layer, tree, 6, keypair, 0, idx))
    return slh_f(pk_seed, adrs(layer, tree, 3, keypair, 0, idx), x) if public else x


SLH = {"128s": dict(k=14, a=12, d=7, hp=9), "small": dict(k=6, a=8, d=2, hp=3),
       "tiny": dict(k=4, a=4, d=1, hp=2)}                                           # as chip.SLH


class Slh:
    """SLH-DSA-SHAKE with n = 16 for one key (FIPS 205 algorithms 18 to 20, deterministic variant)."""

    def __init__(self, seed, slh="128s", pk_seed=None):
        """pk_seed: use this public seed (it is public: anyone may make a key with someone else's)."""
        p = SLH[slh]
        self.k, self.a, self.d, self.hp = p["k"], p["a"], p["d"], p["hp"]
        self.slh = slh
        m = hashlib.shake_256(b"dregg180-v2-model-slh-key" + bytes(seed)).digest(48)
        self.sk_seed, self.sk_prf, self.pk_seed = m[:16], m[16:32], pk_seed or m[32:]
        self.pk_root = self._tree(self.d - 1, 0)[-1][0]
        self.pk = self.pk_seed + self.pk_root

    # --- hashes
    def _h(self, a, m):
        return hashlib.shake_256(self.pk_seed + a + m).digest(16)

    def _digest(self, r, pk_root, m):
        d = hashlib.shake_256(r + self.pk_seed + pk_root + m).digest(30)
        md = d[:21]
        tree = int.from_bytes(d[21:28], "big") & ((1 << (self.hp * (self.d - 1))) - 1)
        leaf = int.from_bytes(d[28:30], "big") & ((1 << self.hp) - 1)
        bits = int.from_bytes(md, "big")
        idx = [(bits >> (168 - self.a * (i + 1))) & ((1 << self.a) - 1) for i in range(self.k)]
        return idx, tree, leaf

    # --- WOTS and XMSS
    def _wots_pk(self, layer, tree, kp):
        ends = b"".join(wots_chain(self.pk_seed, self.sk_seed, layer, tree, kp, i, 15) for i in range(35))
        return self._h(adrs(layer, tree, 1, kp, 0, 0), ends)

    @functools.lru_cache(maxsize=None)
    def _tree(self, layer, tree):
        levels = [[self._wots_pk(layer, tree, i) for i in range(1 << self.hp)]]
        for z in range(1, self.hp + 1):
            prev = levels[-1]
            levels.append([self._h(adrs(layer, tree, 2, 0, z, i), prev[2 * i] + prev[2 * i + 1]) for i in range(len(prev) // 2)])
        return levels

    # --- FORS
    @functools.lru_cache(maxsize=None)
    def _fors_tree(self, tree, kp, i):
        base = i << self.a
        levels = [[fors_leaf(self.pk_seed, self.sk_seed, 0, tree, kp, base + j, True) for j in range(1 << self.a)]]
        for z in range(1, self.a + 1):
            prev = levels[-1]
            levels.append([self._h(adrs(0, tree, 3, kp, z, (base >> z) + j), prev[2 * j] + prev[2 * j + 1])
                           for j in range(len(prev) // 2)])
        return levels

    def sign(self, m, digest_root=None):
        """Signature as a list of 16-byte values in FIPS 205 order: R, FORS, then per layer WOTS and path.
        digest_root: compute the message digest under this PK.root instead of the key's own (not FIPS 205;
        for refusal tests)."""
        r = hashlib.shake_256(self.sk_prf + self.pk_seed + m).digest(16)
        idx, tree, leaf = self._digest(r, digest_root or self.pk_root, m)
        sig, roots = [r], []
        for i, ix in enumerate(idx):
            lv = self._fors_tree(tree, leaf, i)
            sig.append(fors_leaf(self.pk_seed, self.sk_seed, 0, tree, leaf, (i << self.a) + ix))
            sig += [lv[z][(ix >> z) ^ 1] for z in range(self.a)]
            roots.append(lv[-1][0])
        node = self._h(adrs(0, tree, 4, leaf, 0, 0), b"".join(roots))
        for layer in range(self.d):
            dg = wots_digits(node)
            sig += [wots_chain(self.pk_seed, self.sk_seed, layer, tree, leaf, i, dg[i]) for i in range(35)]
            lv = self._tree(layer, tree)
            sig += [lv[z][(leaf >> z) ^ 1] for z in range(self.hp)]
            node = lv[-1][0]
            leaf, tree = tree & ((1 << self.hp) - 1), tree >> self.hp
        return sig


def slh_walk(pk, m, sig, slh="128s"):
    """FIPS 205 verification of a signature (list of 16-byte values). Returns (ok, FORS roots, per layer
    the chain ends) so that the stated values of ARCHITECTURE.md 4.3 can be produced."""
    v = Slh.__new__(Slh)
    p = SLH[slh]
    v.k, v.a, v.d, v.hp, v.pk_seed = p["k"], p["a"], p["d"], p["hp"], pk[:16]
    it = iter(sig)
    idx, tree, leaf = v._digest(next(it), pk[16:], m)
    roots = []
    for i, ix in enumerate(idx):
        t = (i << v.a) + ix
        node = slh_f(v.pk_seed, adrs(0, tree, 3, leaf, 0, t), next(it))
        for z in range(v.a):
            sib = next(it)
            node = v._h(adrs(0, tree, 3, leaf, z + 1, t >> (z + 1)), (node + sib) if not (t >> z) & 1 else (sib + node))
        roots.append(node)
    node = v._h(adrs(0, tree, 4, leaf, 0, 0), b"".join(roots))
    ends = []
    for layer in range(v.d):
        dg = wots_digits(node)
        e = [wots_chain(v.pk_seed, None, layer, tree, leaf, i, 15 - dg[i], dg[i], next(it)) for i in range(35)]
        ends.append(e)
        node = v._h(adrs(layer, tree, 1, leaf, 0, 0), b"".join(e))
        for z in range(v.hp):
            sib = next(it)
            node = v._h(adrs(layer, tree, 2, 0, z + 1, leaf >> (z + 1)), (node + sib) if not (leaf >> z) & 1 else (sib + node))
        leaf, tree = tree & ((1 << v.hp) - 1), tree >> v.hp
    return node == pk[16:], roots, ends


def package(pk, m, sig, slh="128s"):
    """The signature as the chip reads it (ARCHITECTURE.md 4.3): R; the FORS values; the FORS roots twice;
    per layer the signature values, the chain ends twice, the authentication path. Returns words."""
    p = SLH[slh]
    _, roots, ends = slh_walk(pk, m, sig, slh)
    nf = p["k"] * (1 + p["a"])
    out = [sig[0]] + sig[1:1 + nf] + roots + roots
    pos = 1 + nf
    for layer in range(p["d"]):
        out += sig[pos:pos + 35] + ends[layer] + ends[layer] + sig[pos + 35:pos + 35 + p["hp"]]
        pos += 35 + p["hp"]
    return words_of(b"".join(out))


def package_layout(slh="128s"):
    """Word offsets of the parts of a package, for tests that tamper with one: name -> (offset, words)."""
    p = SLH[slh]
    nf = 2 * p["k"] * (1 + p["a"])
    lay = {"R": (0, 2), "fors": (2, nf), "roots_a": (2 + nf, 2 * p["k"]), "roots_b": (2 + nf + 2 * p["k"], 2 * p["k"])}
    pos = 2 + nf + 4 * p["k"]
    for layer in range(p["d"]):
        lay[f"wots{layer}"] = (pos, 70)
        lay[f"ends_a{layer}"] = (pos + 70, 70)
        lay[f"ends_b{layer}"] = (pos + 140, 70)
        lay[f"path{layer}"] = (pos + 210, 2 * p["hp"])
        pos += 210 + 2 * p["hp"]
    lay["end"] = (pos, 0)
    return lay


# ---------------------------------------------------------------- committee (ARCHITECTURE.md 4.6)
def leaf_hash(index, pk):
    return ts([index] + words_of(pk), D_LEAF)


def node_hash(left, right):
    return ts(list(left) + list(right), D_NODE)


class Committee:
    """Members with SLH-DSA keys under a Merkle root of 16-byte nodes. A single authority key is the
    committee of one member with an empty path (G1)."""

    def __init__(self, members, k=None, indices=None):
        """indices: the index word hashed into each leaf, by position (default: the position)."""
        self.members = list(members)
        n = len(self.members)
        self.indices = list(indices) if indices else list(range(n))
        self.depth = max(0, (n - 1).bit_length())
        self.k = n if k is None else k
        level = [leaf_hash(self.indices[i], m.pk) for i, m in enumerate(self.members)]
        level += [[0, 0]] * ((1 << self.depth) - n)
        self.levels = [level]
        while len(self.levels[-1]) > 1:
            prev = self.levels[-1]
            self.levels.append([node_hash(prev[2 * i], prev[2 * i + 1]) for i in range(len(prev) // 2)])
        self.root = self.levels[-1][0]

    def path(self, i):
        out = []
        for z in range(self.depth):
            out += self.levels[z][(i >> z) ^ 1]
        return out

    def item(self, i, m, sig=None, depth=None):
        """One member's part of a statement: index word, public key, path, package, path again."""
        mem = self.members[i]
        depth = self.depth if depth is None else depth
        sig = mem.sign(m) if sig is None else sig
        return ([self.indices[i] | (depth << 32)] + words_of(mem.pk) + self.path(i) + package(mem.pk, m, sig, mem.slh) + self.path(i))

    def statement(self, m, who=None):
        who = range(self.k) if who is None else who
        out = []
        for i in who:
            out += self.item(i, m)
        return out


OWNER_SEED = b"dregg180 model owner root"


@functools.lru_cache(maxsize=None)
def signer(seed, slh="128s"):
    return Slh(seed, slh)


def default_owner_pin(slh):
    """The mask constant of the shipped model ROM: the leaf hash of the model owner root's public key."""
    return tuple(leaf_hash(0, signer(OWNER_SEED, slh).pk))


def owner_item(owner, m):
    """The owner root's statement: a committee of one with an empty path."""
    return words_of(owner.pk) + package(owner.pk, m, owner.sign(m), owner.slh)


# ---------------------------------------------------------------- lifecycle flows (the enrolment station, the host)
def boot(chip, helper_sig=()):
    """BOOT. Returns the response: header, lifecycle state, chip id, record word 0, nonce (2)."""
    return chip.transact(cmd(OP_BOOT, helper_sig))


def enrol(chip):
    """ENROL on a blank chip. Returns (syndromes, tag, nonce) or the error response."""
    rsp = chip.transact(cmd(OP_ENROL))
    if len(rsp) != 7:
        return rsp
    return rsp[1:3], rsp[3:5], rsp[5:7]


def commit_request(owner, syn, tag, nonce, cw, pin):
    m = stmt_owner(L_CM, nonce, syn, tag, cw, pin)
    return cmd(OP_COMMIT, list(tag) + [cw] + list(pin) + owner_item(owner, m))


def provision(chip, owner, pin, flags=0, k=1, u0=0, gen=0):
    """BOOT (blank), ENROL, COMMIT. Returns dict(rsp, helper_sig, k_host, tag, nonce, syn)."""
    r = boot(chip)
    assert r[1] == LC_BLANK, r
    syn, tag, nonce = enrol(chip)
    cw = commit_word(u0, gen, flags, k)
    req = commit_request(owner, syn, tag, nonce, cw, pin)
    rsp = chip.transact(req)
    return dict(rsp=rsp, helper_sig=req[6:], k_host=bytes_of(rsp[1:3]) if len(rsp) == 3 else None, tag=tag, nonce=nonce,
                syn=syn, cw=cw)


def reinit_request(owner, nonce, syn, tag, cw, pin):
    m = stmt_owner(L_RI, nonce, syn, tag, cw, pin)
    return cmd(OP_REINIT, [cw] + list(pin) + owner_item(owner, m))


def gate_request(committee, chip_id, r0, typ, args, nonce=(0, 0), who=None, op=OP_GATE):
    args = (list(args) + [0, 0, 0])[:3]
    m = stmt_transition(chip_id, r0, typ, nonce, args)
    return cmd(op, args + committee.statement(m, who), arg=typ)


def lease_request(committee, chip_id, r0, nonce, base, bound, who=None):
    return gate_request(committee, chip_id, r0, T_LEASE, [base | (bound << 32)], nonce, who, OP_LEASE)
