"""Command behaviour beyond the reference script: the signer against an independent FIPS 205 reference
(hashlib), the request tag on every request type, counted keys and the use counter across resets,
framing. The chips are provisioned through ENROL and COMMIT and booted (common.provisioned); the keys
the signer uses are derived on the chip from the PUF-derived device key, and the tests compute the same
derivations from the model die's response (lifecycle and gate: test_lifecycle.py)."""
import hashlib
import unittest

import common
import host
import isa
import units
from framing import LinkError
from link import SpiLink

q = units.q
_D = common.provisioned()
K, SEED, PRF = _D.k_host, _D.seed, _D.prf           # K_host as COMMIT released it; SK.seed, SK.prf as derived
PK = bytes.fromhex("5ca1ab1e5ca1ab1e0123456789abcdef")
LAYER, TREE, KEYPAIR = 3, 0x0123456789AB, 7
err = host.err


def chip_with_keys(config="S", counted=False):
    d = common.provisioned(host.F_COUNTED if counted else 0, config=config)
    assert (d.k_host, d.seed, d.prf) == (K, SEED, PRF)
    return d.chip


def values(rsp):
    b = host.bytes_of(rsp[1:])
    return [b[i:i + 16] for i in range(0, len(b), 16)]


class DerivedKeys(unittest.TestCase):
    def test_the_host_key_is_the_one_commit_released_and_the_others_never_leave(self):
        self.assertEqual(_D.info["k_host"], K)
        self.assertEqual(len({K, SEED, PRF}), 3)
        c = chip_with_keys()
        self.assertEqual(c.m.rf.key_values(), set(_D.k_dev))            # the only stored key is K_dev
        self.assertEqual(host.bytes_of(c.transact(host.prf_msg(b""))[1:]), hashlib.shake_256(PRF).digest(16))

    def test_vat_mode_has_no_signing_coprocessor(self):
        d = common.provisioned(host.F_VAT)
        self.assertEqual(d.info["rsp"][1:], [0, 0])                     # and COMMIT released no K_host
        self.assertEqual(d.chip.transact(host.prf_msg(b"x")), err(host.OP_PRFMSG, host.E_CLASS))
        self.assertEqual(d.chip.transact(host.cth_wots(K, 0, 0, 1, 2, PK, bytes(16), 1)), err(host.OP_CTH, host.E_CLASS))
        self.assertEqual(d.chip.log[-1]["unit_calls"]["keccak"], 0)     # refused before any key is derived


class DeadFram(bytearray):
    """A FRAM that ignores writes."""

    def __setitem__(self, k, v):
        pass


class FlakyFram(bytearray):
    """A FRAM that stores one word of each record (0..4 data, 5 or 6 tag) with a flipped bit."""

    def __init__(self, data, word):
        super().__init__(data)
        self.word = word

    def __setitem__(self, k, v):
        if (k.start % 128) // 8 == self.word:
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
        self.assertEqual(c.log[-1]["unit_calls"]["keccak"], 2)       # K_host and the tag check, nothing else
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
    """Whether the counter applies is a policy flag fixed at COMMIT. The counter is the use counter u of
    the lifecycle record (leases: test_lifecycle.py)."""

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

    def test_uncounted_key_never_touches_the_record(self):
        c = chip_with_keys(counted=False)
        before = bytes(c.fram)
        self.assertEqual(len(self.sign(c, 3)), 3)
        self.assertEqual(len(self.sign(c, 3, b"\x05" * 16)), 3)
        self.assertEqual(c.log[-1]["unit_cycles"]["fram"], 0)
        self.assertEqual(bytes(c.fram), before)

    def test_counter_survives_reset_through_the_fram(self):
        d = common.provisioned(host.F_COUNTED)
        self.assertEqual(len(self.sign(d.chip, 4)), 3)
        self.assertEqual(d.reboot()[1], host.LC_READY)
        self.assertEqual(self.sign(d.chip, 4), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(len(self.sign(d.chip, 5)), 3)

    def test_first_use_counter_comes_from_the_commit_word(self):
        d = common.provisioned(host.F_COUNTED, u0=40)
        self.assertEqual(self.sign(d.chip, 39), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(len(self.sign(d.chip, 40)), 3)

    def test_refused_before_any_secret_is_touched(self):
        c = chip_with_keys(counted=True)
        self.sign(c, 3)
        self.sign(c, 3)
        self.assertEqual(c.log[-1]["unit_calls"]["keccak"], 2)        # K_host and the request tag; no record, no SK.seed
        self.assertEqual(c.log[-1]["unit_cycles"]["fram"], 0)

    def test_record_format_and_slot_alternation(self):
        d = common.provisioned(host.F_COUNTED)
        c, root = d.chip, d.com.root

        def rec(seq, u):
            return host.record_bytes(d.k_dev, [host.rec0(seq, 0, host.F_COUNTED, 1), u, 0] + root)
        self.assertEqual((bytes(c.fram[128:184]), bytes(c.fram[256:312])), (rec(0, 0), rec(1, 0)))    # as COMMIT left them
        self.sign(c, 2)
        self.assertEqual((bytes(c.fram[128:184]), bytes(c.fram[256:312])), (rec(2, 3), rec(1, 0)))
        self.sign(c, 3)
        self.assertEqual((bytes(c.fram[128:184]), bytes(c.fram[256:312])), (rec(2, 3), rec(3, 4)))
        self.assertNotIn(K, bytes(c.fram))
        self.assertNotEqual(bytes(c.fram[168:184]), host.bytes_of(host.ts([0] * 4 + [host.L_REC] + [host.rec0(2, 0, host.F_COUNTED, 1), 3, 0] + root, host.D_FRAM)))

    def test_nothing_is_released_unless_the_new_record_reads_back(self):
        """A FRAM that drops or corrupts the write: the request is refused and no chain value leaves."""
        for make in [lambda b: DeadFram(b)] + [lambda b, w=w: FlakyFram(b, w) for w in range(7)]:
            d = common.provisioned(host.F_COUNTED)
            d.chip.m.fram.mem = make(bytes(d.chip.fram))
            rsp = self.sign(d.chip, 1)
            self.assertEqual(rsp, err(host.OP_CTH, host.E_RECORD_IO), type(d.chip.fram).__name__)
            self.assertEqual(d.chip.log[-1]["unit_calls"]["keccak"], 3)     # K_host, request tag, record tag; no SK.seed
            self.assertEqual(d.chip.log[-1]["key_words_emitted"], [])

    def test_the_fram_is_not_consulted_within_a_session(self):
        """An older image put back while the chip runs changes nothing: the counter the chip holds is the
        one it advanced. (After a reset the older image is taken: ARCHITECTURE.md 3.4, test_lifecycle.py.)"""
        c = chip_with_keys(counted=True)
        self.sign(c, 1)
        image = bytes(c.fram)
        self.assertEqual(len(self.sign(c, 2)), 3)
        c.fram[:] = image
        self.assertEqual(self.sign(c, 2), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(len(self.sign(c, 3)), 3)


class Framing(unittest.TestCase):
    def test_errors(self):
        c = common.new_chip()
        self.assertEqual(c.transact([0x52 | (1 << 8)]), err(1, host.E_MAGIC))
        self.assertEqual(c.transact([host.hdr(0x7E, 0, 16), 1, 2]), err(0x7E, host.E_OPCODE))
        self.assertEqual(c.transact([host.hdr(host.OP_PING, 0, 8), 1]), err(host.OP_PING, host.E_LEN))
        for op in (0x02, 0x03, 0x30, 0x31, 0x40, 0x50, 0x51, 0x52, 0x53):      # not implemented; 0x40 was the key import
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
        """Before boot only diagnostics and BOOT decode; signer opcodes never start."""
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
            dev = set(_D.k_dev)
            reqs = [host.prf_msg(b"x" * 300), host.cth_wots(K, 0, LAYER, TREE, KEYPAIR, PK, bytes(range(16)), 35),
                    host.cth_fors(K, 0, 0, TREE, KEYPAIR, PK, list(range(16)), pubgen=True),
                    host.cth_wots(K, 1, 0, 9, 1, PK, bytes(16), 3), host.cth_wots(K, 0, 0, 9, 0, PK, bytes(16), 3),
                    host.cth_wots(K, 0, 0, 9, 1, PK, bytes(16), 3)[:-1] + [0],
                    host.keccak(b"y" * 500, 40), [host.hdr(host.OP_PING)], host.cmd(host.OP_NONCE), host.cmd(host.OP_BOOT)]
            for r in reqs:
                rsp = c.transact(r)
                self.assertTrue(common.working_rows_clear(c))
                self.assertEqual(c.log[-1]["key_words_emitted"], [])
                self.assertFalse(dev & set(rsp))
            self.assertFalse(any(w.to_bytes(8, "little") in bytes(c.fram) for w in _D.k_dev))

    def test_cycle_counts_do_not_depend_on_the_keys(self):
        """The same requests on dies with different PUF responses, hence different keys, take the same
        number of clocks."""
        seen = []
        com = common.committee()
        for salt in (b"a", b"b", b"c"):
            c = common.new_chip(puf=salt * 32)
            info = host.provision(c, common.owner(), com.root, host.F_COUNTED)
            c.reset()
            self.assertEqual(host.boot(c, info["helper_sig"])[1], host.LC_READY)
            k = info["k_host"]
            run = []
            for req in (host.cth_wots(k, 2, 0, 9, 2, PK, bytes(range(16)), 35), host.cth_fors(k, 0, 0, 9, 1, PK, [3, 4], pubgen=True),
                        host.prf_msg(b"m" * 200), host.cth_wots(k, 2, 0, 9, 2, PK, bytes(16), 1),
                        host.cth_wots(bytes(16), 5, 0, 9, 5, PK, bytes(16), 1)):
                c.transact(req)
                run.append(c.log[-1]["cycles"])
            seen.append(run)
        self.assertEqual(seen[0], seen[1])
        self.assertEqual(seen[0], seen[2])
        self.assertNotEqual(info["k_host"], K)


if __name__ == "__main__":
    unittest.main()
