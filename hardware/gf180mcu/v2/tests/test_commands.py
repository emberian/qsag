"""Command behaviour beyond the reference script: provisioning and its refusals, the signer against an
independent FIPS 205 reference (hashlib), the request tag on every request type, counted keys and the
anchor across resets, framing."""
import hashlib
import unittest

import common
import host
import isa
import units
from chip import Chip
from framing import LinkError
from link import SpiLink

q = units.q
K = bytes.fromhex("a1b2c3d4e5f60718293a4b5c6d7e8f90")
SEED = bytes.fromhex("000102030405060708090a0b0c0d0e0f")
PRF = bytes.fromhex("f0e1d2c3b4a5968778695a4b3c2d1e0f")
PK = bytes.fromhex("5ca1ab1e5ca1ab1e0123456789abcdef")
LAYER, TREE, KEYPAIR = 3, 0x0123456789AB, 7
OK_LOAD = [host.rhdr(host.OP_KEYLOAD, 0)]


def err(op, code):
    return [host.rhdr(op, 0, False, code)]


def chip_with_keys(config="S", anchor=True, counted=False, **kw):
    c = common.new_chip(config, **kw)
    assert host.provision(c, c.owner, K, SEED, PRF, anchor, counted) == OK_LOAD
    return c


def values(rsp):
    b = host.bytes_of(rsp[1:])
    return [b[i:i + 16] for i in range(0, len(b), 16)]


class Provisioning(unittest.TestCase):
    def test_interfaces_absent_means_refused(self):
        """The default chip has no device secret, no entropy and no owner verifier."""
        c = Chip("S")
        self.assertEqual(c.transact(host.provision_nonce()), err(host.OP_NONCE, host.E_NOKEY))
        self.assertEqual(c.transact(host.keyload_body(K, SEED, PRF) + [0, 0]), err(host.OP_KEYLOAD, host.E_NOKEY))
        self.assertEqual(c.transact(host.prf_msg(b"")), err(host.OP_PRFMSG, host.E_NOKEY))
        self.assertEqual(c.transact([host.hdr(host.OP_PING)])[2] & 0xF, 0)
        c = Chip("S", puf=units.PufUnit(common.DEV))                       # device secret, no entropy
        self.assertEqual(c.transact(host.provision_nonce()), err(host.OP_NONCE, host.E_TRNG))
        self.assertEqual(c.transact(host.keyload_body(K, SEED, PRF) + [0, 0]), err(host.OP_KEYLOAD, host.E_AUTH))
        c = Chip("S", puf=units.PufUnit(common.DEV), entropy=units.EntropyUnit(3))   # no owner verifier
        owner = host.Owner()
        self.assertEqual(host.provision(c, owner, K, SEED, PRF), err(host.OP_KEYLOAD, host.E_AUTH))
        self.assertEqual(c.transact(host.prf_msg(b"")), err(host.OP_PRFMSG, host.E_NOKEY))

    def test_authorised_load(self):
        c = chip_with_keys()
        self.assertEqual(host.bytes_of(c.transact(host.prf_msg(b""))[1:]), hashlib.shake_256(PRF).digest(16))
        self.assertEqual(c.transact([host.hdr(host.OP_PING)])[2] & 0x1F, 0b01001)   # key valid, device ok, uncounted
        c = chip_with_keys(counted=True)
        self.assertEqual(c.transact([host.hdr(host.OP_PING)])[2] & 0x1F, 0b11001)

    def load(self, c, mutate=None, nonce=None, owner=None, **kw):
        if nonce is None:
            nonce = c.transact(host.provision_nonce())[1:]
        body = host.keyload_body(K, SEED, PRF, **kw)
        req = body + (owner or c.owner).authorise(nonce, body)
        if mutate:
            mutate(req)
        return c.transact(req)

    def refused(self, c, rsp, code=host.E_AUTH):
        self.assertEqual(rsp, err(host.OP_KEYLOAD, code))
        self.assertFalse(c.m.key_valid)
        self.assertEqual(c.transact(host.prf_msg(b"")), err(host.OP_PRFMSG, host.E_NOKEY))
        self.assertFalse(set(host.words_of(K + SEED + PRF)) & c.m.rf.key_values())

    def test_load_without_a_nonce_is_refused(self):
        for nonce in ([1, 2], [0, 0]):
            c = common.new_chip()
            self.refused(c, self.load(c, nonce=nonce))

    def test_every_word_of_the_request_is_authorised(self):
        for i in range(9):
            for bit in (0, 31, 63) if i else (17, 18):        # header: anchor-init and counted flags
                c = common.new_chip()

                def flip(req, i=i, bit=bit):
                    req[i] ^= 1 << bit
                self.refused(c, self.load(c, flip))

    def test_authorisation_by_another_owner_is_refused(self):
        c = common.new_chip()
        self.refused(c, self.load(c, owner=host.Owner(b"someone else")))

    def test_an_authorisation_is_good_for_one_nonce(self):
        c = common.new_chip()
        nonce = c.transact(host.provision_nonce())[1:]
        body = host.keyload_body(K, SEED, PRF)
        req = body + c.owner.authorise(nonce, body)
        self.assertEqual(c.transact(req), OK_LOAD)
        c.reset()
        self.refused(c, c.transact(req))                       # replay with no nonce drawn
        fresh = c.transact(host.provision_nonce())[1:]
        self.assertNotEqual(fresh, nonce)
        self.refused(c, c.transact(req))                       # replay against a fresh nonce
        c.transact(host.provision_nonce())
        bad = list(req)
        bad[-1] ^= 1
        self.refused(c, c.transact(bad))
        self.refused(c, c.transact(req[:7] + c.owner.authorise(fresh, body)))   # the nonce was spent by the attempt
        n3 = c.transact(host.provision_nonce())[1:]
        good = body + c.owner.authorise(n3, body)
        self.refused(c, c.transact(good[:-1] + [good[-1] ^ 1]))                 # a wrong attempt spends n3
        self.refused(c, c.transact(good))                                       # so the right one is too late
        n4 = c.transact(host.provision_nonce())[1:]
        self.assertEqual(c.transact(body + c.owner.authorise(n4, body)), OK_LOAD)

    def test_no_reprovisioning_while_a_key_is_valid(self):
        c = chip_with_keys()
        self.assertEqual(c.transact(host.provision_nonce()), err(host.OP_NONCE, host.E_KEYSET))
        self.assertEqual(self.load(c, nonce=[0, 0]), err(host.OP_KEYLOAD, host.E_KEYSET))
        self.assertEqual(host.bytes_of(c.transact(host.prf_msg(b""))[1:]), hashlib.shake_256(PRF).digest(16))

    def test_reset_clears_keys_and_reprovisioning_needs_the_owner_again(self):
        c = chip_with_keys()
        c.reset()
        self.assertEqual(c.transact(host.prf_msg(b"")), err(host.OP_PRFMSG, host.E_NOKEY))
        self.assertFalse(set(host.words_of(K + SEED + PRF)) & c.m.rf.key_values())
        self.refused(c, self.load(c, owner=host.Owner(b"not the owner")))
        self.assertEqual(self.load(c), OK_LOAD)

    def test_shape_refusals(self):
        c = common.new_chip()
        w = host.words_of(K + SEED + PRF)
        self.assertEqual(c.transact([host.hdr(host.OP_KEYLOAD, 1, 48)] + w), err(host.OP_KEYLOAD, host.E_LEN))
        self.assertEqual(c.transact([host.hdr(host.OP_KEYLOAD, 0, 64)] + w + [0, 0]), err(host.OP_KEYLOAD, host.E_OPCODE))
        self.assertEqual(c.transact([host.hdr(host.OP_KEYLOAD, 9, 64)] + w + [0, 0]), err(host.OP_KEYLOAD, host.E_OPCODE))
        self.assertEqual(c.transact([host.hdr(host.OP_NONCE, 0, 8), 0]), err(host.OP_NONCE, host.E_LEN))

    def test_anchor_write_is_verified_at_provisioning(self):
        for fram in (DeadFram(64), FlakyFram(64, word=0), FlakyFram(64, word=1), FlakyFram(64, word=2),
                     FlakyFram(64, word=5)):
            c = common.new_chip(fram=fram)
            self.refused(c, self.load(c), host.E_ANCHOR_IO)

    def test_anchor_records_are_under_the_device_secret(self):
        c = chip_with_keys()
        self.assertEqual(bytes(c.fram[0:24]), host.fram_record(common.DEV, 0))
        self.assertEqual(bytes(c.fram[32:56]), host.fram_record(common.DEV, 0))
        self.assertNotEqual(bytes(c.fram[0:24]), host.fram_record(K + K, 0))
        other = Chip("S", puf=units.PufUnit(bytes(32)), entropy=units.EntropyUnit(1), owner=c.owner.verify)
        host.provision(other, c.owner, K, SEED, PRF)
        self.assertNotEqual(bytes(other.fram[0:24]), bytes(c.fram[0:24]))   # same host keys, another device


class DeadFram(bytearray):
    """A FRAM that ignores writes."""

    def __setitem__(self, k, v):
        pass


class FlakyFram(bytearray):
    """A FRAM that stores one word of each record (0 counter, 1 or 2 tag) with a flipped bit;
    word 3 + n: the same for slot 1 only."""

    def __init__(self, n, word):
        super().__init__(n)
        self.word = word

    def __setitem__(self, k, v):
        start = k.start
        slot, w = start // 32, (start % 32) // 8
        if w == self.word or (slot == 1 and w + 3 == self.word):
            v = bytes([v[0] ^ 1]) + bytes(v[1:])
        super().__setitem__(k, v)


class Wots(unittest.TestCase):
    def setUp(self):
        self.c = chip_with_keys()

    def sign(self, msg, n=35, first=0, **kw):
        return self.c.transact(host.cth_wots(K, 0, LAYER, TREE, KEYPAIR, PK, msg, n, first, **kw))

    def test_full_signature_matches_fips205(self):
        for msg in (bytes(range(16)), bytes(16), b"\xff" * 16, hashlib.sha256(b"m").digest()[:16]):
            rsp = self.sign(msg)
            self.assertEqual(rsp[0], host.rhdr(host.OP_CTH, 16 * 35))
            d = host.wots_digits(msg)
            want = [host.wots_chain(PK, SEED, LAYER, TREE, KEYPAIR, i, d[i]) for i in range(35)]
            self.assertEqual(values(rsp), want)

    def test_digit_rule_edges(self):
        self.assertEqual(host.wots_digits(bytes(16))[32:], [1, 14, 0])          # checksum 480 = 0x1E0
        self.assertEqual(host.wots_digits(b"\xff" * 16)[32:], [0, 0, 0])
        self.assertEqual(host.wots_digits(bytes([0x01, 0xF7, 0x32]) + bytes(13))[:6], [0, 1, 15, 7, 3, 2])

    def test_chain_window(self):
        msg = bytes(range(0x30, 0x40))
        full = values(self.sign(msg))
        for first, n in ((0, 1), (5, 4), (15, 3), (30, 5), (34, 1), (31, 2)):
            self.assertEqual(values(self.sign(msg, n, first)), full[first:first + n], (first, n))

    def test_public_key_window(self):
        ends = [host.wots_chain(PK, SEED, LAYER, TREE, KEYPAIR, i, 15) for i in range(35)]
        self.assertEqual(values(self.sign(bytes(16), pubgen=True)), ends)
        for first, n in ((1, 1), (7, 3), (33, 2), (34, 1)):
            self.assertEqual(values(self.sign(bytes(16), n, first, pubgen=True)), ends[first:first + n], (first, n))
        self.assertEqual(values(self.sign(b"\xa5" * 16, 2, 9, pubgen=True)), ends[9:11])    # the message plays no part

    def test_signature_completes_to_the_public_key(self):
        msg = bytes(range(0x50, 0x60))
        d = host.wots_digits(msg)
        sig, ends = values(self.sign(msg)), values(self.sign(bytes(16), pubgen=True))
        for i in range(35):
            self.assertEqual(host.wots_chain(PK, SEED, LAYER, TREE, KEYPAIR, i, 15 - d[i], d[i], sig[i]), ends[i])

    def test_shape_refusals(self):
        e_len = err(host.OP_CTH, host.E_LEN)
        self.assertEqual(self.sign(bytes(16), 0), e_len)
        self.assertEqual(self.sign(bytes(16), 1, 35), e_len)
        self.assertEqual(self.sign(bytes(16), 35, 1), e_len)
        self.assertEqual(self.sign(bytes(16), 36), e_len)
        bad_type = host.cth(K, 0, LAYER, TREE, 5, KEYPAIR, PK, [0, 0, 0, 0], 1)     # WOTS_PRF is not requestable
        self.assertEqual(self.c.transact(bad_type), e_len)
        for flags in (2, 3, 4, 0x80):                                               # no flag but PUBGEN exists
            req = host.cth_wots(None, 0, LAYER, TREE, KEYPAIR, PK, bytes(16), 1)[:10]
            req[0] |= flags << 16
            self.assertEqual(self.c.transact(req + host.request_tag(K, req)), e_len)
        self.assertEqual(self.c.pins["FAULT"], 0)


class Fors(unittest.TestCase):
    def test_leaves_match_fips205(self):
        c = chip_with_keys()
        idx = [0, 1, 4095, 4096, 12345, 57343, 65535, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        for pub in (False, True):
            rsp = c.transact(host.cth_fors(K, 0, 0, TREE, KEYPAIR, PK, idx, pubgen=pub))
            self.assertEqual(values(rsp), [host.fors_leaf(PK, SEED, 0, TREE, KEYPAIR, i, pub) for i in idx])
        for n in (1, 4, 5):
            rsp = c.transact(host.cth_fors(K, 0, 0, TREE, KEYPAIR, PK, idx[:n]))
            self.assertEqual(values(rsp), [host.fors_leaf(PK, SEED, 0, TREE, KEYPAIR, i) for i in idx[:n]])

    def test_too_many_leaves(self):
        c = chip_with_keys()
        req = host.cth(K, 0, 0, TREE, 3, KEYPAIR, PK, [0, 0, 0, 0], 17)
        self.assertEqual(c.transact(req), err(host.OP_CTH, host.E_LEN))


REQUESTS = {
    "wots": lambda k: host.cth_wots(k, 0, LAYER, TREE, KEYPAIR, PK, bytes(range(16)), 2),
    "wots window": lambda k: host.cth_wots(k, 0, LAYER, TREE, KEYPAIR, PK, bytes(range(16)), 3, 30),
    "wots pubgen": lambda k: host.cth_wots(k, 0, LAYER, TREE, KEYPAIR, PK, bytes(16), 2, pubgen=True),
    "fors": lambda k: host.cth_fors(k, 0, 0, TREE, KEYPAIR, PK, [1, 2, 3, 4, 5]),
    "fors pubgen": lambda k: host.cth_fors(k, 0, 0, TREE, KEYPAIR, PK, [1, 2], pubgen=True),
    "counted wots": lambda k: host.cth_wots(k, 6, 0, 9, 6, PK, bytes(range(16)), 2),
}


class RequestTag(unittest.TestCase):
    """Every signer request type: served with its tag, refused when any bit of the request or of either
    tag word changes. Each refusal is checked on a fresh chip, so the FAULT pin assertion is not sticky."""

    def fresh(self, name):
        return chip_with_keys(counted=name.startswith("counted"))

    def refused(self, name, req):
        c = self.fresh(name)
        fram = bytes(c.fram)
        self.assertEqual(c.pins["FAULT"], 0)
        self.assertEqual(c.transact(req), err(host.OP_CTH, host.E_MAC), name)
        self.assertEqual(c.pins["FAULT"], 1)
        self.assertEqual(c.log[-1]["unit_calls"]["keccak"], 1)       # the tag check and nothing else
        self.assertEqual(bytes(c.fram), fram)

    def test_good_requests_are_served(self):
        for name, build in REQUESTS.items():
            c = self.fresh(name)
            rsp = c.transact(build(K))
            self.assertEqual(rsp[0] & 0xFF0000, 0x010000, name)
            self.assertEqual(c.pins["FAULT"], 0)

    def test_every_body_word_is_bound(self):
        for name, build in REQUESTS.items():
            good = build(K)
            for i in range(1, 10):
                for bit in (0, 37):
                    req = list(good)
                    req[i] ^= 1 << bit
                    self.refused(name, req)

    def test_both_tag_words_are_checked(self):
        for name, build in REQUESTS.items():
            good = build(K)
            for i in (10, 11):
                for bit in (0, 63):
                    req = list(good)
                    req[i] ^= 1 << bit
                    self.refused(name, req)
            self.refused(name, good[:10] + [good[10], 0])
            self.refused(name, good[:10] + [0, good[11]])
            self.refused(name, good[:10] + [good[11], good[10]])

    def test_header_fields_are_bound(self):
        for name, build in REQUESTS.items():
            for bit in (16, 48, 56):                                 # PUBGEN, n, first chain
                req = build(K)
                req[0] ^= 1 << bit
                self.refused(name, req)

    def test_public_key_generation_needs_the_tag(self):
        for name in ("wots pubgen", "fors pubgen"):
            self.refused(name, REQUESTS[name](K)[:-2] + [0, 0])

    def test_tag_under_another_key(self):
        for name, build in REQUESTS.items():
            self.refused(name, build(bytes(16)))

    def test_reference_format_request_is_refused(self):
        """A request in the reference chip's CTH format (length 80, host-chosen digits) is not served."""
        import os
        import sys
        sys.path.insert(0, os.path.join(common.CHIPDIR, "model"))
        import qsag_ni_model as ref
        dev = ref.Device()
        dev.keyload_host(SEED, PRF, K)
        c = chip_with_keys()
        for kw in (dict(), dict(pubgen=True), dict(stateful=True)):
            req, _ = dev.cth(0, LAYER, TREE, 0, KEYPAIR, PK, [0, 0, 0], 4, **kw)
            self.assertEqual(c.transact(req), err(host.OP_CTH, host.E_LEN))


class PrfMsg(unittest.TestCase):
    def test_against_hashlib(self):
        c = chip_with_keys()
        for n in (0, 1, 16, 119, 120, 121, 127, 128, 255, 256, 400):
            m = bytes((5 * i + 1) & 0xFF for i in range(n))
            rsp = c.transact(host.prf_msg(m))
            self.assertEqual(host.bytes_of(rsp[1:]), hashlib.shake_256(PRF + m).digest(16), n)

    def test_trailing_bytes_of_the_last_word_do_not_count(self):
        c = chip_with_keys()
        req = host.prf_msg(b"abc")
        dirty = [req[0], req[1] | (0xDEADBEEF << 24)]
        self.assertEqual(c.transact(dirty), c.transact(req))

    def test_refusals(self):
        c = common.new_chip()
        self.assertEqual(c.transact(host.prf_msg(b"abc")), err(host.OP_PRFMSG, host.E_NOKEY))
        c = chip_with_keys()
        self.assertEqual(c.transact([host.hdr(host.OP_PRFMSG, 1, 0)]), err(host.OP_PRFMSG, host.E_LEN))


class CountedKeys(unittest.TestCase):
    """Whether the counter applies is a property of the key, fixed at provisioning."""

    def sign(self, c, leaf, msg=bytes(16), keypair=None, n=1, **kw):
        return c.transact(host.cth_wots(K, leaf, 0, 9, leaf if keypair is None else keypair, PK, msg, n, **kw))

    def test_counter_only_moves_forward(self):
        c = chip_with_keys(counted=True)
        self.assertEqual(len(self.sign(c, 0)), 3)
        self.assertEqual(self.sign(c, 0, b"\x01" * 16), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(len(self.sign(c, 9)), 3)
        for leaf in (0, 5, 9):
            self.assertEqual(self.sign(c, leaf), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(self.sign(c, 0xFFFFFFFF), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(len(self.sign(c, 10)), 3)

    def test_a_request_cannot_opt_out_of_the_counter(self):
        """On a counted key there is no stateless signing: the same leaf is refused whatever the request says."""
        c = chip_with_keys(counted=True)
        self.assertEqual(len(self.sign(c, 4)), 3)
        self.assertEqual(self.sign(c, 4, b"\x02" * 16), err(host.OP_CTH, host.E_REUSE))
        for flags in (2, 4):                                    # the old STATEFUL bit, set or clear, is not a choice
            req = host.cth_wots(None, 4, 0, 9, 4, PK, b"\x02" * 16, 1)[:10]
            req[0] |= flags << 16
            self.assertEqual(c.transact(req + host.request_tag(K, req)), err(host.OP_CTH, host.E_LEN))
        self.assertEqual(self.sign(c, 4, b"\x02" * 16, n=2), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(c.transact(host.cth_fors(K, 4, 0, 9, 4, PK, [1])), err(host.OP_CTH, host.E_CLASS))

    def test_counter_is_bound_to_the_key_pair(self):
        c = chip_with_keys(counted=True)
        before = bytes(c.fram)
        for leaf, keypair in ((5, 2), (5, 6), (0, 5), (5, 0x01000005)):
            self.assertEqual(self.sign(c, leaf, keypair=keypair), err(host.OP_CTH, host.E_CLASS))
        self.assertEqual(bytes(c.fram), before)
        self.assertEqual(len(self.sign(c, 5)), 3)

    def test_public_values_do_not_move_the_counter(self):
        c = chip_with_keys(counted=True)
        before = bytes(c.fram)
        self.assertEqual(len(self.sign(c, 5, pubgen=True)), 3)
        self.assertEqual(len(self.sign(c, 5, keypair=2, pubgen=True)), 3)
        self.assertEqual(len(c.transact(host.cth_fors(K, 5, 0, 9, 5, PK, [1], pubgen=True))), 3)
        self.assertEqual(bytes(c.fram), before)

    def test_uncounted_key_never_touches_the_anchor(self):
        c = chip_with_keys(counted=False)
        before = bytes(c.fram)
        self.assertEqual(len(self.sign(c, 3)), 3)
        self.assertEqual(len(self.sign(c, 3, b"\x05" * 16)), 3)
        self.assertEqual(c.log[-1]["unit_cycles"]["fram"], 0)
        self.assertEqual(bytes(c.fram), before)

    def test_counter_survives_reset_through_the_fram(self):
        c = chip_with_keys(counted=True)
        self.assertEqual(len(self.sign(c, 4)), 3)
        c.reset()
        self.assertEqual(host.provision(c, c.owner, K, SEED, PRF, anchor_init=False, counted=True), OK_LOAD)
        self.assertEqual(self.sign(c, 4), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(len(self.sign(c, 5)), 3)

    def test_refused_before_any_secret_is_touched(self):
        c = chip_with_keys(counted=True)
        self.sign(c, 3)
        self.sign(c, 3)
        self.assertEqual(c.log[-1]["unit_calls"]["keccak"], 3)        # request tag + two record tags

    def test_record_format_and_slot_alternation(self):
        c = chip_with_keys(counted=True)
        self.sign(c, 2)
        self.assertEqual({bytes(c.fram[0:24]), bytes(c.fram[32:56])},
                         {host.fram_record(common.DEV, 0), host.fram_record(common.DEV, 3)})
        self.sign(c, 3)
        self.assertEqual({bytes(c.fram[0:24]), bytes(c.fram[32:56])},
                         {host.fram_record(common.DEV, 4), host.fram_record(common.DEV, 3)})

    def test_empty_and_forged_anchor(self):
        c = chip_with_keys(anchor=False, counted=True)
        self.assertEqual(self.sign(c, 0), err(host.OP_CTH, host.E_ANCHOR_EMPTY))
        good = host.fram_record(common.DEV, 7)
        self.assertEqual(len(good), 24)
        forgeries = [(7).to_bytes(8, "little") + bytes(16),                      # no tag
                     good[:8] + good[8:16] + bytes(8),                            # first tag word only
                     good[:8] + bytes(8) + good[16:24],                           # second tag word only
                     good[:8] + good[8:23] + bytes([good[23] ^ 0x80]),            # one bit of the second word
                     good[:8] + bytes([good[8] ^ 1]) + good[9:24],                # one bit of the first word
                     (6).to_bytes(8, "little") + good[8:24],                      # tag of another counter
                     host.fram_record(K + K, 7),                                  # tag under the host's key
                     ((1 << 32) | 7).to_bytes(8, "little") + good[8:24],          # counter above 32 bits, tag of 7
                     host.fram_record(common.DEV, (1 << 32) | 7),                 # counter above 32 bits, its own tag
                     host.fram_record(common.DEV, 1 << 63)]
        for slot in (0, 1):
            c = chip_with_keys(anchor=False, counted=True)
            for rec in forgeries:
                c.fram[:] = bytes(64)
                c.fram[32 * slot:32 * slot + 24] = rec
                image = bytes(c.fram)
                self.assertEqual(self.sign(c, 8), err(host.OP_CTH, host.E_ANCHOR_EMPTY), (slot, rec.hex()))
                self.assertEqual(bytes(c.fram), image)                         # nothing was written
            c.fram[:] = bytes(64)
            c.fram[32 * slot:32 * slot + 24] = good                            # the authentic record, either slot
            self.assertEqual(self.sign(c, 6), err(host.OP_CTH, host.E_REUSE))
            self.assertEqual(len(self.sign(c, 7)), 3)

    def test_the_larger_authentic_counter_wins_in_either_slot(self):
        for hi_slot in (0, 1):
            c = chip_with_keys(anchor=False, counted=True)
            c.fram[32 * hi_slot:32 * hi_slot + 24] = host.fram_record(common.DEV, 9)
            c.fram[32 * (1 - hi_slot):32 * (1 - hi_slot) + 24] = host.fram_record(common.DEV, 4)
            self.assertEqual(self.sign(c, 8), err(host.OP_CTH, host.E_REUSE), hi_slot)
            self.assertEqual(len(self.sign(c, 9)), 3)
            self.assertEqual(bytes(c.fram[32 * hi_slot:32 * hi_slot + 24]), host.fram_record(common.DEV, 9))
            self.assertEqual(bytes(c.fram[32 * (1 - hi_slot):32 * (1 - hi_slot) + 24]), host.fram_record(common.DEV, 10))

    def test_one_damaged_slot_is_tolerated_either_way(self):
        for damaged in (0, 1):
            c = chip_with_keys(anchor=False, counted=True)
            c.fram[32 * (1 - damaged):32 * (1 - damaged) + 24] = host.fram_record(common.DEV, 3)
            c.fram[32 * damaged:32 * damaged + 24] = host.fram_record(common.DEV, 50)[:23] + b"\x00"
            self.assertEqual(self.sign(c, 2), err(host.OP_CTH, host.E_REUSE), damaged)
            self.assertEqual(len(self.sign(c, 3)), 3)
            self.assertEqual(bytes(c.fram[32 * damaged:32 * damaged + 24]), host.fram_record(common.DEV, 4))

    def test_nothing_is_released_unless_the_new_counter_reads_back(self):
        """A FRAM that drops or corrupts the write: the request is refused and no chain value leaves."""
        for make in (lambda: DeadFram(64), lambda: FlakyFram(64, 0), lambda: FlakyFram(64, 1), lambda: FlakyFram(64, 2)):
            fram = make()
            bytearray.__setitem__(fram, slice(0, 24), host.fram_record(common.DEV, 0))
            bytearray.__setitem__(fram, slice(32, 56), host.fram_record(common.DEV, 0))
            c = chip_with_keys(anchor=False, counted=True, fram=fram)
            rsp = self.sign(c, 1)
            self.assertEqual(rsp, err(host.OP_CTH, host.E_ANCHOR_IO), type(fram).__name__)
            self.assertEqual(c.log[-1]["unit_calls"]["keccak"], 4)    # tag, two record tags, the new record's tag; no PRF
            self.assertEqual(c.log[-1]["key_words_emitted"], [])

    def test_rollback_in_session_is_a_fault(self):
        c = chip_with_keys(counted=True)
        self.sign(c, 1)
        image = bytes(c.fram)
        self.sign(c, 2)
        self.assertEqual(c.pins["FAULT"], 0)
        c.fram[:] = image
        self.assertEqual(self.sign(c, 7), err(host.OP_CTH, host.E_ROLLBACK))
        self.assertEqual(c.pins["FAULT"], 1)


class Framing(unittest.TestCase):
    def test_errors(self):
        c = common.new_chip()
        self.assertEqual(c.transact([0x52 | (1 << 8)]), err(1, host.E_MAGIC))
        self.assertEqual(c.transact([host.hdr(0x7E, 0, 16), 1, 2]), err(0x7E, host.E_OPCODE))
        self.assertEqual(c.transact([host.hdr(host.OP_PING, 0, 8), 1]), err(host.OP_PING, host.E_LEN))
        for op in (0x02, 0x03, 0x30, 0x31, 0x50, 0x51, 0x52, 0x53):      # not in stage 1
            self.assertEqual(c.transact([host.hdr(op)]), err(op, host.E_OPCODE))
        with self.assertRaises(LinkError):
            c.transact([host.hdr(host.OP_KECCAK, 0, 16), 1])

    def test_unread_payload_is_drained_before_the_next_command(self):
        c = chip_with_keys()
        for req in ([host.hdr(0x7E, 0, 24), 1, 2, 3], [host.hdr(host.OP_PING, 0, 16), 1, 2],
                    [host.hdr(host.OP_CTH, 0, 80)] + [0] * 10, host.cth_wots(bytes(16), 0, 0, 1, 2, PK, bytes(16), 1)):
            self.assertEqual(c.transact(req)[0] & 0x800000, 0x800000)
            self.assertEqual(c.transact([host.hdr(host.OP_PING)])[1], int.from_bytes(b"QSAGNI18", "little"))

    def test_lifecycle_gate(self):
        """Before a key is valid only diagnostics and provisioning decode; signer opcodes never start."""
        c = common.new_chip()
        for req in (host.prf_msg(b"x"), host.cth_wots(K, 0, 0, 1, 2, PK, bytes(16), 1), [host.hdr(host.OP_CTH, 0, 8), 0]):
            self.assertEqual(c.transact(req), err((req[0] >> 8) & 0xFF, host.E_NOKEY))
            self.assertEqual(c.log[-1]["steps"], 1)                     # the dispatcher refused; no routine ran
        self.assertEqual(len(c.transact(host.keccak(b"abc", 4))), 5)

    def test_configuration_S_has_no_field_commands(self):
        c = common.new_chip("S")
        for op in (host.OP_P2, host.OP_MERKLE):
            self.assertEqual(c.transact([host.hdr(op, 1, 96)] + [0] * 12), err(op, host.E_OPCODE))

    def test_ping_reports_status_and_no_secret(self):
        c = chip_with_keys()
        rsp = c.transact([host.hdr(host.OP_PING)])
        self.assertEqual(rsp[1], int.from_bytes(b"QSAGNI18", "little"))
        self.assertEqual(rsp[2] & 1, 1)
        self.assertEqual(rsp[3:], [0, 0])

    def test_spi_link(self):
        c = common.new_chip()
        msg = b"link test"
        frame = host.bytes_of(host.keccak(msg, 4, 0x1F, False))
        self.assertEqual(SpiLink(c).exchange(frame)[8:], hashlib.shake_256(msg).digest(32))
        with self.assertRaises(ValueError):
            SpiLink(c).exchange(b"\x51\x01\x00")


class FieldCommands(unittest.TestCase):
    """Configuration L. The reference script covers accept and one reject; these add shapes."""

    def test_merkle_depths_and_sides(self):
        import random
        rng = random.Random(7)
        c = common.new_chip("L")
        P = q.P
        for depth in (1, 2, 5, 33, 62):
            key3 = [rng.randrange(P) for _ in range(3)]
            leaf = [rng.randrange(P) for _ in range(4)]
            sibs = [[rng.randrange(P) for _ in range(4)] for _ in range(depth)]
            idx = rng.randrange(1 << depth)
            root = q.p2_canopy_path(leaf, sibs, key3, idx)
            req = [host.hdr(host.OP_MERKLE, 0, 96 + 32 * depth, depth)] + key3 + [idx] + leaf + [x for s in sibs for x in s]
            self.assertEqual(c.transact(req + root), [host.rhdr(host.OP_MERKLE, 40, True), 1] + root)
            self.assertEqual(c.pins["VERIFY_OK"], 1)
            for k in range(4):
                bad = list(root)
                bad[k] = (bad[k] + 1) % P
                self.assertEqual(c.transact(req + bad), [host.rhdr(host.OP_MERKLE, 40, False), 0] + root)
                self.assertEqual(c.pins["VERIFY_OK"], 0)
            wrong_side = list(req)
            wrong_side[4] ^= 1
            self.assertEqual(c.transact(wrong_side + root)[1], 0)

    def test_merkle_shape_refusals(self):
        c = common.new_chip("L")
        e = err(host.OP_MERKLE, host.E_LEN)
        self.assertEqual(c.transact([host.hdr(host.OP_MERKLE, 0, 96, 0)] + [0] * 12), e)
        self.assertEqual(c.transact([host.hdr(host.OP_MERKLE, 0, 96 + 32 * 63, 63)] + [0] * (12 + 4 * 63)), e)
        self.assertEqual(c.transact([host.hdr(host.OP_MERKLE, 0, 96 + 32, 2)] + [0] * 16), e)
        self.assertEqual(c.transact([host.hdr(host.OP_MERKLE, 0, 96 + 31, 1)] + [0] * 16), e)   # not whole words

    def test_p2_shape_refusals(self):
        c = common.new_chip("L")
        e = err(host.OP_P2, host.E_LEN)
        self.assertEqual(c.transact([host.hdr(host.OP_P2, 1, 88)] + [0] * 11), e)
        self.assertEqual(c.transact([host.hdr(host.OP_P2, 0, 32)] + [0] * 4), e)
        self.assertEqual(c.transact([host.hdr(host.OP_P2, 0, 41)] + [0] * 6), e)


class Invariants(unittest.TestCase):
    def test_working_rows_are_clear_after_every_command_and_no_key_word_leaves(self):
        for counted in (False, True):
            c = chip_with_keys("L", counted=counted)
            dev = set(host.words_of(common.DEV))
            reqs = [host.prf_msg(b"x" * 300), host.cth_wots(K, 0, LAYER, TREE, KEYPAIR, PK, bytes(range(16)), 35),
                    host.cth_fors(K, 0, 0, TREE, KEYPAIR, PK, list(range(16)), pubgen=True),
                    host.cth_wots(K, 1, 0, 9, 1, PK, bytes(16), 3), host.cth_wots(K, 0, 0, 9, 0, PK, bytes(16), 3),
                    host.cth_wots(K, 0, 0, 9, 1, PK, bytes(16), 3)[:-1] + [0],
                    host.keccak(b"y" * 500, 40), [host.hdr(host.OP_PING)], host.keyload_body(K, SEED, PRF) + [0, 0]]
            for r in reqs:
                rsp = c.transact(r)
                self.assertTrue(common.working_rows_clear(c))
                self.assertEqual(c.log[-1]["key_words_emitted"], [])
                self.assertFalse(dev & set(rsp))
            self.assertFalse(any(common.DEV[i:i + 8] in bytes(c.fram) for i in range(0, 32, 8)))

    def test_cycle_counts_do_not_depend_on_the_keys(self):
        """The same requests under different key material take the same number of clocks."""
        seen = []
        for salt in (b"a", b"b", b"c"):
            k, seed, prf = (hashlib.sha256(salt + t).digest()[:16] for t in (b"k", b"s", b"p"))
            c = common.new_chip()
            assert host.provision(c, c.owner, k, seed, prf, True, True) == OK_LOAD
            run = []
            for req in (host.cth_wots(k, 2, 0, 9, 2, PK, bytes(range(16)), 35), host.cth_fors(k, 0, 0, 9, 1, PK, [3, 4], pubgen=True),
                        host.prf_msg(b"m" * 200), host.cth_wots(k, 2, 0, 9, 2, PK, bytes(16), 1),
                        host.cth_wots(bytes(16), 5, 0, 9, 5, PK, bytes(16), 1)):
                c.transact(req)
                run.append(c.log[-1]["cycles"])
            seen.append(run)
        self.assertEqual(seen[0], seen[1])
        self.assertEqual(seen[0], seen[2])


if __name__ == "__main__":
    unittest.main()
