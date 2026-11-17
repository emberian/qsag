"""Host side of QSAG-Wire as the v2 model speaks it: request builders and an independent FIPS 205
(SLH-DSA-SHAKE, n = 16) reference built on hashlib. Used by the tests; the seed of the host library.
"""
import hashlib
import os
import sys

sys.path.insert(0, os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "model")))
import qsag_prims as q  # noqa: E402

OP_PING, OP_P2, OP_MERKLE, OP_KECCAK, OP_KEYLOAD, OP_CTH, OP_PRFMSG, OP_NONCE = 0x01, 0x10, 0x11, 0x20, 0x40, 0x41, 0x42, 0x43
(E_MAGIC, E_OPCODE, E_LEN, E_NOKEY, E_MAC, E_ANCHOR_EMPTY, E_ROLLBACK, E_REUSE, E_ANCHOR_IO, E_KEYSET, E_TRNG, E_AUTH,
 E_CLASS) = range(1, 14)
D_FRAM, D_REQ, D_PROV = 0x1F, 0x21, 0x22
M64 = (1 << 64) - 1


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


def keccak(msg, out_words, suffix=0x1F, turbo=True):
    return [hdr(OP_KECCAK, 1 if turbo else 0, len(msg), suffix | (out_words << 8))] + words_of(msg)


def provision_nonce():
    return [hdr(OP_NONCE)]


def keyload_body(k_host, sk_seed, sk_prf, anchor_init=True, counted=False):
    """The request without its two authorisation words."""
    flags = 1 | (2 if anchor_init else 0) | (4 if counted else 0)
    return [hdr(OP_KEYLOAD, flags, 64)] + words_of(k_host) + words_of(sk_seed) + words_of(sk_prf)


def provisioning_digest(body):
    """What the owner root authorises together with the nonce: 4 words."""
    return words_of(q.turboshake256(bytes_of(body), 32, D_PROV))


class Owner:
    """Stand-in for the owner root (stage 4: an SLH-DSA key whose public-key digest is a mask constant).
    Here the authorisation is a 128-bit keyed hash and the chip model is handed `verify` as a black box;
    the interface (nonce, statement digest, authorisation words) is the one the signature will use."""

    def __init__(self, key=b"model owner root"):
        self.key = bytes(key)

    def authorise(self, nonce, body):
        return words_of(q.turboshake256(self.key + bytes_of(nonce) + bytes_of(provisioning_digest(body)), 16, 0x23))

    def verify(self, nonce, digest, sig):
        return words_of(q.turboshake256(self.key + bytes_of(nonce) + bytes_of(digest), 16, 0x23)) == list(sig)


def provision(chip, owner, k_host, sk_seed, sk_prf, anchor_init=True, counted=False):
    """Nonce round trip and authorised key load. Returns the KEYLOAD response."""
    rsp = chip.transact(provision_nonce())
    if len(rsp) != 3:
        return rsp
    body = keyload_body(k_host, sk_seed, sk_prf, anchor_init, counted)
    return chip.transact(body + owner.authorise(rsp[1:], body))


def fram_record(k_dev, ctr):
    """Anchor record: counter and TurboSHAKE256(K_dev || counter || "QSAGNIFR")[0..15]."""
    c = ctr.to_bytes(8, "little")
    return c + q.turboshake256(bytes(k_dev) + c + b"QSAGNIFR", 16, D_FRAM)


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
