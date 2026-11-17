"""Lifecycle, rollback, gate, entropy source and PUF (ARCHITECTURE.md 3, 4, 6.1, 6.5; the rows of 8.3).
Every refusal here is a guard of the microcode or the decoder; tests/mutation.py removes each in turn.
Signatures use the reduced parameter set (common.SLH); test_slh128s.py runs the real one."""
import copy
import unittest

import common
import host
import isa
import units
from chip import package_words
from machine import ControlFault

err = host.err
PKG = package_words(common.SLH)
LAY = host.package_layout(common.SLH)
PK = bytes(range(16))
ST = isa.STATE0


def state(c, i):
    return c.m.rf[ST + i]


def no_keys(c):
    return c.m.rf.key_values() == set()


def signs(d, leaf=0):
    """Does the chip serve a signer request?"""
    return d.chip.transact(host.cth_wots(d.k_host, leaf, 0, 1, leaf, PK, bytes(16), 1))


def fresh(**kw):
    """A blank chip after BOOT and ENROL: (chip, syndromes, tag, nonce)."""
    c = common.new_chip(**kw)
    assert host.boot(c)[1] == host.LC_BLANK
    return (c,) + host.enrol(c)


class Enrolment(unittest.TestCase):
    def test_blank_chip(self):
        c = common.new_chip()
        self.assertEqual(c.transact(host.prf_msg(b"")), err(host.OP_PRFMSG, host.E_NOKEY))      # RESET: nothing but BOOT
        for op in (host.OP_ENROL, host.OP_COMMIT, host.OP_NONCE, host.OP_REINIT, host.OP_LEASE):
            self.assertEqual(c.transact(host.cmd(op)), err(op, host.E_STATE))
        self.assertEqual(host.boot(c), [host.rhdr(host.OP_BOOT, 40), host.LC_BLANK, 0, 0, 0, 0])
        self.assertEqual(c.log[-1]["unit_cycles"]["puf"], 0)
        self.assertEqual(host.boot(c), err(host.OP_BOOT, host.E_STATE))                         # BOOT decodes in RESET only
        for op in (host.OP_PRFMSG, host.OP_CTH, host.OP_GATE):
            self.assertEqual(c.transact(host.cmd(op)), err(op, host.E_NOKEY))
        for op in (host.OP_NONCE, host.OP_REINIT, host.OP_LEASE):
            self.assertEqual(c.transact(host.cmd(op)), err(op, host.E_STATE))
        self.assertEqual(common.new_chip().transact(host.cmd(host.OP_BOOT, [1])), err(host.OP_BOOT, host.E_LEN))

    def test_enrol_emits_helper_data_and_writes_nothing(self):
        c, syn, tag, nonce = fresh()
        self.assertEqual(tag, host.puf_tag(c.m.puf.ideal))
        self.assertEqual(syn, [units.bch_syndrome(c.m.puf.ideal[0]) | (units.bch_syndrome(c.m.puf.ideal[1]) << 27),
                               units.bch_syndrome(c.m.puf.ideal[2]) | (units.bch_syndrome(c.m.puf.ideal[3]) << 27)])
        self.assertNotEqual(nonce, [0, 0])
        self.assertEqual(bytes(c.fram), bytes(len(c.fram)))
        self.assertTrue(no_keys(c))
        self.assertEqual(c.log[-1]["key_words_emitted"], [])
        self.assertFalse(set(c.m.puf.ideal) & set(c.log and syn + tag + nonce))
        self.assertEqual(c.transact(host.cmd(host.OP_ENROL, [0])), err(host.OP_ENROL, host.E_LEN))
        c.reset()                                                # an enrolment that is never committed leaves the chip blank
        self.assertEqual(host.boot(c)[1], host.LC_BLANK)
        self.assertNotEqual(host.enrol(c)[2], nonce)

    def test_commit_then_boot_gives_the_same_keys_every_time(self):
        d = common.provisioned(booted=False)
        c = d.chip
        self.assertEqual(d.info["rsp"][0], host.rhdr(host.OP_COMMIT, 16))
        self.assertEqual(d.info["k_host"], host.derive(d.k_dev, host.L_HOST))
        self.assertEqual(c.m.lc, isa.LC_LOCKED)                  # provisioned; this session is over
        self.assertEqual(signs(d), err(host.OP_CTH, host.E_NOKEY))
        self.assertEqual(c.transact(host.cmd(host.OP_ENROL)), err(host.OP_ENROL, host.E_STATE))
        for _ in range(2):
            rsp = d.reboot()
            self.assertEqual(rsp[1:], [host.LC_READY, d.chip_id, host.rec0(1, 0, 0, 1), 0, 0])
            self.assertEqual([c.m.rf[isa.KEY0 + i] for i in range(4)], d.k_dev)
            self.assertEqual(len(signs(d)), 3)
        self.assertEqual([state(c, i) for i in range(5)], [host.rec0(1, 0, 0, 1), 0, 0] + d.com.root)
        helper = host.words_of(bytes(c.fram[:72]))
        self.assertEqual(helper, [d.info["cw"]] + d.info["syn"] + d.com.root + d.info["tag"] + d.info["nonce"])
        self.assertFalse(any(w.to_bytes(8, "little") in bytes(c.fram) for w in d.k_dev + c.m.puf.ideal))

    def test_commit_needs_the_owner_root_over_this_enrolment(self):
        own, com = common.owner(), common.committee()
        cw = host.commit_word()

        def attempt(build, code=host.E_AUTH):
            c, syn, tag, nonce = fresh()
            self.assertEqual(c.transact(build(syn, tag, nonce)), err(host.OP_COMMIT, code))
            self.assertTrue(no_keys(c))
            self.assertEqual(bytes(c.fram), bytes(len(c.fram)))
            self.assertEqual(c.m.lc, isa.LC_BLANK)
            good = host.commit_request(own, syn, tag, nonce, cw, com.root)      # the nonce was spent by the attempt
            self.assertEqual(c.transact(good), err(host.OP_COMMIT, host.E_STATE))
            return c

        good = lambda s, t, n: host.commit_request(own, s, t, n, cw, com.root)  # noqa: E731
        attempt(lambda s, t, n: host.commit_request(host.signer(b"not the owner", common.SLH), s, t, n, cw, com.root))
        attempt(lambda s, t, n: host.commit_request(own, s, t, [n[0] ^ 1, n[1]], cw, com.root))     # another nonce
        attempt(lambda s, t, n: host.commit_request(own, s, t, [n[0], n[1] ^ 1], cw, com.root))
        attempt(lambda s, t, n: host.commit_request(own, [s[0] ^ 1, s[1]], t, n, cw, com.root))     # other syndromes
        attempt(lambda s, t, n: host.commit_request(own, [s[0], s[1] ^ 1], t, n, cw, com.root))
        for i in range(1, 6):                                    # tag, commit word, root: each word is signed
            def bent(s, t, n, i=i):
                req = good(s, t, n)
                req[i] ^= 1 << 40
                return req
            attempt(bent)
        for i in (6, 7, 8, 9, 10 + LAY["fors"][0], 10 + LAY["ends_a0"][0], 10 + LAY["end"][0] - 1):   # key, signature
            def bent(s, t, n, i=i):
                req = good(s, t, n)
                req[i] ^= 2
                return req
            attempt(bent)
        # signed, but not for this die: the check tag must be the one the PUF reconstructs to
        attempt(lambda s, t, n: host.commit_request(own, s, [t[0] ^ 1, t[1]], n, cw, com.root), host.E_PUF)
        attempt(lambda s, t, n: host.commit_request(own, s, [t[0], t[1] ^ 1], n, cw, com.root), host.E_PUF)
        # signed, but not a first record
        attempt(lambda s, t, n: host.commit_request(own, s, t, n, host.commit_word(k=0), com.root), host.E_ARG)
        attempt(lambda s, t, n: host.commit_request(own, s, t, n, host.commit_word(flags=host.F_RETIRED), com.root), host.E_ARG)
        c, syn, tag, nonce = fresh()
        self.assertEqual(c.transact(host.cmd(host.OP_COMMIT, good(syn, tag, nonce)[1:-1])), err(host.OP_COMMIT, host.E_LEN))
        self.assertEqual(len(c.transact(good(syn, tag, nonce))), 3)             # a length error spends nothing

    def test_commit_needs_an_enrolment_in_the_same_power_session(self):
        own, com = common.owner(), common.committee()
        c, syn, tag, nonce = fresh()
        req = host.commit_request(own, syn, tag, nonce, host.commit_word(), com.root)
        c.reset()
        self.assertEqual(host.boot(c)[1], host.LC_BLANK)
        self.assertEqual(c.transact(req), err(host.OP_COMMIT, host.E_STATE))    # no nonce in this session
        syn2, tag2, nonce2 = host.enrol(c)
        self.assertEqual((syn2, tag2), (syn, tag))
        self.assertEqual(c.transact(req), err(host.OP_COMMIT, host.E_AUTH))     # the old statement, a fresh nonce
        self.assertTrue(no_keys(c))

    def test_commit_reads_back_what_it_writes(self):
        import test_commands as tc
        own, com = common.owner(), common.committee()
        for make in [lambda b: tc.DeadFram(b)] + [lambda b, w=w: tc.FlakyFram(b, w) for w in range(9)]:
            c, syn, tag, nonce = fresh()
            c.m.fram.mem = make(bytes(c.fram))
            self.assertEqual(c.transact(host.commit_request(own, syn, tag, nonce, host.commit_word(), com.root)),
                             err(host.OP_COMMIT, host.E_RECORD_IO))
            self.assertTrue(no_keys(c))

    def test_no_enrolment_once_provisioned(self):
        d = common.provisioned()
        for op in (host.OP_ENROL, host.OP_COMMIT, host.OP_BOOT, host.OP_NONCE, host.OP_REINIT, host.OP_LEASE):
            self.assertEqual(d.chip.transact(host.cmd(op)), err(op, host.E_STATE))
        d.chip.reset()
        self.assertEqual(d.chip.transact(host.cmd(host.OP_ENROL)), err(host.OP_ENROL, host.E_STATE))
        # an erased FRAM is a blank chip again, and enrolling it again still needs the owner root
        d.chip.fram[:] = bytes(len(d.chip.fram))
        self.assertEqual(host.boot(d.chip)[1], host.LC_BLANK)
        syn, tag, nonce = host.enrol(d.chip)
        bad = host.commit_request(host.signer(b"not the owner", common.SLH), syn, tag, nonce, host.commit_word(), d.com.root)
        self.assertEqual(d.chip.transact(bad), err(host.OP_COMMIT, host.E_AUTH))


class Boot(unittest.TestCase):
    def refused(self, d, payload, code, puf_ran=False):
        c = d.chip
        c.reset()
        fram = bytes(c.fram)
        self.assertEqual(c.transact(host.cmd(host.OP_BOOT, payload)), err(host.OP_BOOT, code))
        self.assertEqual(c.log[-1]["unit_cycles"]["puf"] > 0, puf_ran)
        self.assertTrue(no_keys(c))
        self.assertEqual(bytes(c.fram), fram)                    # a failed boot writes nothing
        if code != host.E_LEN:
            self.assertEqual(c.m.lc, isa.LC_LOCKED)
            self.assertEqual(c.pins["FAULT"], 1)
            self.assertEqual(signs(d), err(host.OP_CTH, host.E_NOKEY))
            self.assertEqual(host.boot(c), err(host.OP_BOOT, host.E_STATE))
        self.assertEqual(d.reboot()[1], host.LC_READY)           # and the part is not bricked

    def test_the_helper_record_is_authenticated_before_the_puf_runs(self):
        d = common.provisioned()
        sig = d.info["helper_sig"]
        self.refused(d, [], host.E_LEN)
        self.refused(d, sig[:-1], host.E_LEN)
        self.refused(d, sig + [0], host.E_LEN)
        for i in (0, 1, 2, 3, 4, 4 + LAY["fors"][0] + 3, 4 + LAY["roots_a"][0], 4 + LAY["roots_b"][0] + 5,
                  4 + LAY["wots0"][0] + 1, 4 + LAY["ends_a0"][0] + 9, 4 + LAY["ends_b0"][0] + 9, 4 + LAY["path0"][0], 4 + PKG - 1):
            bad = list(sig)
            bad[i] ^= 1 << 13
            self.refused(d, bad, host.E_AUTH)
        other = host.signer(b"not the owner", common.SLH)
        m = host.stmt_owner(host.L_CM, d.info["nonce"], d.info["syn"], d.info["tag"], d.info["cw"], d.com.root)
        self.refused(d, host.owner_item(other, m), host.E_AUTH)
        self.refused(d, host.owner_item(common.owner(), bytes(32)), host.E_AUTH)
        # The owner's public seed is public. A key made with it by someone else, signing as if under the
        # owner's root, states the owner's key and passes everything but the root its signature leads to.
        own = common.owner()
        imp = host.Slh(b"impostor", common.SLH, pk_seed=own.pk_seed)
        sig = imp.sign(m, digest_root=own.pk_root)
        self.refused(d, host.words_of(own.pk) + host.package(own.pk, m, sig, common.SLH), host.E_AUTH)
        # The owner's own signature computed under a root that is not its key's: the stated key is refused.
        other_root = bytes(range(16))
        stated = own.pk_seed + other_root
        sig = own.sign(m, digest_root=other_root)
        self.assertEqual(host.slh_walk(stated, m, sig, common.SLH)[0], False)
        self.refused(d, host.words_of(stated) + host.package(stated, m, sig, common.SLH), host.E_AUTH)

    def test_every_word_of_the_helper_record_is_signed(self):
        for word in range(9):
            d = common.provisioned()
            good = bytes(d.chip.fram)
            d.chip.fram[8 * word] ^= 1
            c = d.chip
            c.reset()
            self.assertEqual(host.boot(c, d.info["helper_sig"]), err(host.OP_BOOT, host.E_AUTH), word)
            self.assertEqual(c.log[-1]["unit_cycles"]["puf"], 0)
            self.assertTrue(no_keys(c))
            c.fram[:] = good
            self.assertEqual(d.reboot()[1], host.LC_READY)

    def test_a_helper_record_boots_only_the_die_it_was_made_on(self):
        d = common.provisioned()
        other = common.new_chip(puf=b"\x55" * 32)
        other.fram[:] = d.chip.fram
        self.assertEqual(host.boot(other, d.info["helper_sig"]), err(host.OP_BOOT, host.E_PUF))
        self.assertTrue(no_keys(other))
        self.assertEqual(other.m.lc, isa.LC_LOCKED)

    def test_reconstruction_corrects_five_bits_a_block_and_fails_safe_on_six(self):
        d = common.provisioned()
        d.chip.m.puf.flips = {0, 9, 30, 44, 62, 63, 64, 65, 66, 67, 130, 200, 210, 220, 230, 251}
        self.assertEqual(d.reboot()[1], host.LC_READY)
        self.assertEqual([d.chip.m.rf[isa.KEY0 + i] for i in range(4)], d.k_dev)
        self.assertEqual(len(signs(d)), 3)
        for block in range(4):
            d.chip.m.puf.flips = {63 * block + i for i in (1, 2, 3, 5, 8, 13)}
            d.chip.reset()
            self.assertEqual(host.boot(d.chip, d.info["helper_sig"]), err(host.OP_BOOT, host.E_PUF))
            self.assertTrue(no_keys(d.chip))
            self.assertEqual((d.chip.m.lc, d.chip.pins["FAULT"]), (isa.LC_LOCKED, 1))
        d.chip.m.puf.flips = set()
        self.assertEqual(d.reboot()[1], host.LC_READY)           # a noisy read is not held against the part

    def test_boot_without_a_puf_or_a_fram(self):
        d = common.provisioned()
        d.chip.m.puf = None
        d.chip.reset()
        self.assertEqual(host.boot(d.chip, d.info["helper_sig"])[0] & 0x800000, 0x800000)
        self.assertTrue(no_keys(d.chip))
        self.assertEqual(d.chip.m.lc, isa.LC_LOCKED)
        c = common.new_chip()
        c.m.fram.mem = bytearray(b"\xff" * len(c.fram))          # a bus that reads all ones is not a blank chip
        self.assertEqual(host.boot(c), err(host.OP_BOOT, host.E_LEN))
        self.assertEqual(host.boot(c, [0] * (PKG + 4)), err(host.OP_BOOT, host.E_AUTH))
        self.assertTrue(no_keys(c))

    def test_boot_needs_no_entropy_source(self):
        """Survival: an unleased chip boots, signs and takes gate statements with the TRNG dead."""
        d = common.provisioned()
        d.chip.m.trng = None
        self.assertEqual(d.reboot()[1], host.LC_READY)
        self.assertEqual(len(signs(d)), 3)
        self.assertEqual(len(d.gate(host.T_EPOCH, [3])), 2)
        self.assertEqual(d.chip.log[-1]["unit_cycles"]["trng"], 0)


class Records(unittest.TestCase):
    """The lifecycle record in the FRAM: authentic or ignored; the newer one wins; no record is an orphan."""

    def slots(self, d):
        return bytes(d.chip.fram[128:184]), bytes(d.chip.fram[256:312])

    def boot_with(self, d, slot1, slot2):
        d.chip.fram[128:184] = slot1
        d.chip.fram[256:312] = slot2
        return d.reboot()

    def rec(self, d, seq, u=0, flags=host.F_COUNTED, key=None, gen=0):
        return host.record_bytes(key or d.k_dev, [host.rec0(seq, gen, flags, 1), u, 0] + d.com.root)

    def test_forged_records_are_not_loaded(self):
        d = common.provisioned(host.F_COUNTED)
        good = self.rec(d, 9, 7)
        forgeries = [good[:40] + bytes(16), good[:40] + good[40:48] + bytes(8), good[:40] + bytes(8) + good[48:],
                     good[:55] + bytes([good[55] ^ 0x80]), good[:40] + bytes([good[40] ^ 1]) + good[41:],
                     self.rec(d, 9, 7, key=[0, 0, 0, 0]), self.rec(d, 9, 7, key=host.words_of(d.k_host + d.k_host))]
        forgeries += [good[:8 * w] + bytes([good[8 * w] ^ 1]) + good[8 * w + 1:] for w in range(5)]   # each data word
        for f in forgeries:
            for slot in (0, 1):
                d = common.provisioned(host.F_COUNTED)
                s = [bytes(56), bytes(56)]
                s[slot] = f
                self.assertEqual(self.boot_with(d, *s)[1], host.LC_ORPHAN, f.hex())
                self.assertEqual(signs(d), err(host.OP_CTH, host.E_NOKEY))
                s[1 - slot] = self.rec(d, 3, 2)                  # beside an authentic record the forgery is ignored
                self.assertEqual(self.boot_with(d, *s)[1:4], [host.LC_READY, d.chip_id, host.rec0(3, 0, host.F_COUNTED, 1)])

    def test_the_newer_authentic_record_wins_in_either_slot(self):
        for hi in (0, 1):
            d = common.provisioned(host.F_COUNTED)
            s = [None, None]
            s[hi], s[1 - hi] = self.rec(d, 9, 7), self.rec(d, 4, 2)
            self.assertEqual(self.boot_with(d, *s)[3], host.rec0(9, 0, host.F_COUNTED, 1))
            self.assertEqual(signs(d, 6), err(host.OP_CTH, host.E_REUSE))
            self.assertEqual(len(signs(d, 7)), 3)
            s[1 - hi] = self.rec(d, 9, 5)                        # equal sequence numbers: slot 1 is read first and stays
            self.assertEqual(self.boot_with(d, *s)[3], host.rec0(9, 0, host.F_COUNTED, 1))
            self.assertEqual(d.rec1 & 0xFFFFFFFF, 5 if hi else 7)

    def test_a_single_record_with_sequence_number_0_boots(self):
        d = common.provisioned()
        d.chip.fram[256:] = bytes(len(d.chip.fram) - 256)        # the slot with sequence number 1 is lost
        self.assertEqual(d.reboot()[1:4], [host.LC_READY, d.chip_id, host.rec0(0, 0, 0, 1)])

    def test_unleased_rollback_is_the_documented_residual(self):
        """ARCHITECTURE.md 3.4: an older authentic image restored across a reset is accepted on an unleased
        chip, and a one-time key can then be used again. This asserts the residual, not a guarantee."""
        d = common.provisioned(host.F_COUNTED)
        image = bytes(d.chip.fram)
        self.assertEqual(len(signs(d, 0)), 3)
        self.assertEqual(signs(d, 0), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(d.reboot()[1], host.LC_READY)
        self.assertEqual(signs(d, 0), err(host.OP_CTH, host.E_REUSE))            # across a reset, with the FRAM left alone
        d.chip.fram[:] = image
        d.reboot()
        self.assertEqual(len(signs(d, 0)), 3)

    def test_orphan_and_reinitialisation(self):
        d = common.provisioned(host.F_COUNTED)
        c, own = d.chip, common.owner()
        c.fram[128:] = bytes(len(c.fram) - 128)                  # the helper record survives, the lifecycle slots do not
        self.assertEqual(d.reboot()[1:], [host.LC_ORPHAN, d.chip_id, 0, 0, 0])
        self.assertEqual([c.m.rf[isa.KEY0 + i] for i in range(4)], d.k_dev)
        for op in (host.OP_PRFMSG, host.OP_CTH, host.OP_GATE):
            self.assertEqual(c.transact(host.cmd(op)), err(op, host.E_NOKEY))
        for op in (host.OP_ENROL, host.OP_COMMIT, host.OP_LEASE, host.OP_BOOT):
            self.assertEqual(c.transact(host.cmd(op)), err(op, host.E_STATE))
        cw = host.commit_word(u0=20, gen=3, flags=host.F_COUNTED)
        syn, tag = d.info["syn"], d.info["tag"]

        def reinit(nonce, who=own, **kw):
            return c.transact(host.reinit_request(who, nonce, kw.get("syn", syn), kw.get("tag", tag), kw.get("cw", cw), d.com.root))
        self.assertEqual(reinit([0, 0]), err(host.OP_REINIT, host.E_STATE))      # no nonce drawn
        n1 = c.transact(host.cmd(host.OP_NONCE))[1:]
        self.assertEqual(reinit(n1, host.signer(b"not the owner", common.SLH)), err(host.OP_REINIT, host.E_AUTH))
        self.assertEqual(reinit(n1), err(host.OP_REINIT, host.E_STATE))          # the attempt spent the nonce
        n2 = c.transact(host.cmd(host.OP_NONCE))[1:]
        self.assertNotEqual(n1, n2)
        self.assertEqual(reinit(n1), err(host.OP_REINIT, host.E_AUTH))           # a statement over the old nonce
        n3 = c.transact(host.cmd(host.OP_NONCE))[1:]
        self.assertEqual(reinit(n3, tag=[tag[0] ^ 1, tag[1]]), err(host.OP_REINIT, host.E_AUTH))    # for another chip
        n4 = c.transact(host.cmd(host.OP_NONCE))[1:]
        commit_stmt = host.cmd(host.OP_REINIT, [cw] + d.com.root + host.owner_item(
            own, host.stmt_owner(host.L_CM, n4, syn, tag, cw, d.com.root)))
        self.assertEqual(c.transact(commit_stmt), err(host.OP_REINIT, host.E_AUTH))                # a COMMIT statement
        n5 = c.transact(host.cmd(host.OP_NONCE))[1:]
        self.assertEqual(reinit(n5, cw=host.commit_word(k=0)), err(host.OP_REINIT, host.E_ARG))
        self.assertEqual(bytes(c.fram[128:]), bytes(len(c.fram) - 128))
        import test_commands as tc
        n6 = c.transact(host.cmd(host.OP_NONCE))[1:]
        live = c.m.fram.mem
        c.m.fram.mem = tc.DeadFram(bytes(live))
        self.assertEqual(reinit(n6), err(host.OP_REINIT, host.E_RECORD_IO))      # the new records must read back
        self.assertTrue(no_keys(c))
        c.m.fram.mem = live
        self.assertEqual(d.reboot()[1], host.LC_ORPHAN)
        n6 = c.transact(host.cmd(host.OP_NONCE))[1:]
        self.assertEqual(reinit(n6), [host.rhdr(host.OP_REINIT, 0)])
        self.assertEqual(c.m.lc, isa.LC_LOCKED)
        self.assertEqual(d.reboot()[1:4], [host.LC_READY, d.chip_id, host.rec0(1, 3, host.F_COUNTED, 1)])
        self.assertEqual(signs(d, 19), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(len(signs(d, 20)), 3)
        self.assertEqual(c.transact(host.cmd(host.OP_REINIT)), err(host.OP_REINIT, host.E_STATE))  # READY: not an orphan


class Lease(unittest.TestCase):
    FL = host.F_LEASED | host.F_COUNTED

    def test_a_leased_chip_waits_for_its_lease(self):
        d = common.provisioned(self.FL)
        c = d.chip
        rsp = d.reboot()
        self.assertEqual(rsp[1:4], [host.LC_LEASE, d.chip_id, host.rec0(1, 0, self.FL, 1)])
        nonce = rsp[4:]
        self.assertNotEqual(nonce, [0, 0])
        self.assertEqual(signs(d), err(host.OP_CTH, host.E_NOKEY))
        self.assertEqual(c.transact(host.cmd(host.OP_GATE, [0, 0, 0], arg=host.T_EPOCH)), err(host.OP_GATE, host.E_NOKEY))
        self.assertEqual(d.lease(5, 8, nonce), [host.rhdr(host.OP_LEASE, 16), host.rec0(2, 0, self.FL, 1), 5])
        self.assertEqual((c.m.lc, c.pins["VERIFY_OK"]), (isa.LC_READY, 1))
        self.assertEqual([state(c, 7), state(c, 8), state(c, 9)], [0, 0, 8])
        self.assertEqual(signs(d, 4), err(host.OP_CTH, host.E_REUSE))            # below the granted base
        for leaf in (5, 7):
            self.assertEqual(len(signs(d, leaf)), 3)
        for leaf in (8, 9, 1000):
            self.assertEqual(signs(d, leaf), err(host.OP_CTH, host.E_LEASE))     # at or past the session bound
        self.assertEqual(signs(d, 6), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(c.transact(host.cmd(host.OP_LEASE)), err(host.OP_LEASE, host.E_STATE))    # one lease a session
        self.assertEqual(d.reboot()[1], host.LC_LEASE)
        self.assertNotEqual([state(c, 7), state(c, 8)], nonce)

    def test_a_lease_closes_rollback(self):
        """The authority's ledger, not the FRAM, says where the counter starts."""
        d = common.provisioned(self.FL)
        old = bytes(d.chip.fram)
        self.assertEqual(len(d.lease(0, 4)), 3)
        self.assertEqual(len(signs(d, 0)), 3)
        d.chip.fram[:] = old                                     # the image from before any use
        rsp = d.reboot()
        self.assertEqual(rsp[3], host.rec0(1, 0, self.FL, 1))    # the chip reports the old sequence number
        self.assertEqual(len(d.lease(4, 8, rsp[4:])), 3)         # the ledger has moved past what it granted
        for leaf in (0, 1, 3):
            self.assertEqual(signs(d, leaf), err(host.OP_CTH, host.E_REUSE))
        self.assertEqual(len(signs(d, 4)), 3)

    def refused(self, d, req, code=host.E_AUTH):
        c = d.chip
        fram = bytes(c.fram)
        self.assertEqual(c.transact(req), err(host.OP_LEASE, code))
        self.assertEqual((c.m.lc, bytes(c.fram)), (isa.LC_LEASE, fram))
        self.assertEqual(signs(d), err(host.OP_CTH, host.E_NOKEY))
        self.assertEqual([state(c, 7), state(c, 8)], [0, 0])                     # the nonce is spent by the attempt

    def test_a_lease_is_for_this_nonce_this_chip_this_generation(self):
        d = common.provisioned(self.FL)
        nonce = [state(d.chip, 7), state(d.chip, 8)]
        good = host.lease_request(d.com, d.tag, d.rec0, nonce, 2, 6)
        cases = [host.lease_request(d.com, d.tag, d.rec0, [nonce[0] ^ 1, nonce[1]], 2, 6),
                 host.lease_request(d.com, d.tag, d.rec0, [nonce[0], nonce[1] ^ 1], 2, 6),
                 host.lease_request(d.com, [d.tag[0] ^ 1, d.tag[1]], d.rec0, nonce, 2, 6),
                 host.lease_request(d.com, d.tag, d.rec0 ^ (1 << 32), nonce, 2, 6),            # another generation
                 host.lease_request(d.com, d.tag, d.rec0 ^ 1, nonce, 2, 6),                    # another sequence number
                 host.lease_request(common.committee(tag=b"outsider"), d.tag, d.rec0, nonce, 2, 6),
                 host.gate_request(d.com, d.tag, d.rec0, host.T_EPOCH, [2 | (6 << 32)], nonce, op=host.OP_LEASE)[:1]
                 + good[1:],                                                                       # header says EPOCH
                 good[:1] + [3 | (6 << 32)] + good[2:], good[:1] + [2 | (7 << 32)] + good[2:],     # other base, other bound
                 good[:2] + [1] + good[3:], good[:3] + [1] + good[4:]]                             # the unused arguments
        for i, req in enumerate(cases):
            d2 = copy.deepcopy(d)
            code = host.E_ARG if i == 6 else host.E_AUTH
            if i == 6:                                           # refused by the command before anything is read
                self.assertEqual(d2.chip.transact(req), err(host.OP_LEASE, code))
                continue
            self.refused(d2, req, code)
            self.assertEqual(d2.chip.transact(good), err(host.OP_LEASE, host.E_STATE))             # too late: no nonce
            fresh_nonce = d2.chip.transact(host.cmd(host.OP_NONCE))[1:]
            self.refused(d2, good)                               # the old lease against a fresh nonce
            n = d2.chip.transact(host.cmd(host.OP_NONCE))[1:]
            self.assertNotIn(n, (nonce, fresh_nonce))
            self.assertEqual(len(d2.lease(2, 6, n)), 3)
        self.refused(copy.deepcopy(d), host.lease_request(d.com, d.tag, d.rec0, nonce, 6, 5), host.E_ARG)
        self.assertEqual(len(d.chip.transact(host.lease_request(d.com, d.tag, d.rec0, nonce, 6, 6))), 3)   # an empty grant

    def test_a_lease_from_an_earlier_session_is_not_accepted(self):
        d = common.provisioned(self.FL)
        nonce = [state(d.chip, 7), state(d.chip, 8)]
        old = host.lease_request(d.com, d.tag, d.rec0, nonce, 0, 4)
        image = bytes(d.chip.fram)
        self.assertEqual(len(d.chip.transact(old)), 3)
        d.chip.fram[:] = image                                   # so that the sequence number is the old one too
        d.reboot()
        self.refused(d, old)

    def test_a_lease_names_the_authority_generation(self):
        d = common.provisioned(self.FL, lease=(0, 4))
        old_rec0 = d.rec0
        new = common.committee(tag=b"successor")
        self.assertEqual(len(d.gate(host.T_ROTATE, new.root + [1])), 2)
        rsp = d.reboot()
        self.assertEqual((rsp[3] >> 32) & 0xFFFF, 1)
        nonce = rsp[4:]
        self.refused(d, host.lease_request(d.com, d.tag, rsp[3], nonce, 4, 8))                 # the replaced authority
        nonce = d.chip.transact(host.cmd(host.OP_NONCE))[1:]
        self.refused(d, host.lease_request(new, d.tag, old_rec0, nonce, 4, 8))                 # the superseded generation
        nonce = d.chip.transact(host.cmd(host.OP_NONCE))[1:]
        self.assertEqual(len(d.chip.transact(host.lease_request(new, d.tag, rsp[3], nonce, 4, 8))), 3)

    def test_no_lease_without_entropy(self):
        d = common.provisioned(self.FL)
        c = d.chip
        for dead in (None, units.TrngUnit(3, kappa=0.0)):
            c.m.trng = dead
            self.assertEqual(d.reboot()[1:], [host.LC_LEASE, d.chip_id, host.rec0(1, 0, self.FL, 1), 0, 0])
            self.assertEqual([c.m.rf[isa.KEY0 + i] for i in range(4)], d.k_dev)                    # booted, not usable
            self.assertEqual(c.transact(host.lease_request(d.com, d.tag, d.rec0, [0, 0], 0, 4)), err(host.OP_LEASE, host.E_STATE))
            self.assertEqual(c.transact(host.cmd(host.OP_NONCE)), err(host.OP_NONCE, host.E_TRNG))
            self.assertEqual((c.m.lc, signs(d)), (isa.LC_LEASE, err(host.OP_CTH, host.E_NOKEY)))
        c.m.trng = units.TrngUnit(4)                             # the source recovers: nothing was lost
        nonce = c.transact(host.cmd(host.OP_NONCE))[1:]
        self.assertEqual(len(d.lease(0, 4, nonce)), 3)

    def test_lease_record_is_read_back(self):
        import test_commands as tc
        d = common.provisioned(self.FL)
        d.chip.m.fram.mem = tc.DeadFram(bytes(d.chip.fram))
        self.assertEqual(d.lease(0, 4), err(host.OP_LEASE, host.E_RECORD_IO))
        self.assertEqual(d.chip.m.lc, isa.LC_LEASE)


class Gate(unittest.TestCase):
    """A transition happens only on a statement by the pinned authority for exactly that transition."""

    def refused(self, d, req, code=host.E_AUTH):
        c = d.chip
        before = ([state(c, i) for i in range(5)], bytes(c.fram))
        self.assertEqual(c.transact(req), err(host.OP_GATE, code))
        self.assertEqual(([state(c, i) for i in range(5)], bytes(c.fram)), before)
        if code == host.E_AUTH:
            self.assertEqual(c.pins["VERIFY_OK"], 0)

    def test_epoch(self):
        d = common.provisioned()
        self.assertEqual(d.gate(host.T_EPOCH, [5]), [host.rhdr(host.OP_GATE, 8), host.rec0(2, 0, 0, 1)])
        self.assertEqual((d.rec1 >> 32, d.chip.pins["VERIFY_OK"]), (5, 1))
        self.assertEqual(bytes(d.chip.fram[128:184]), host.record_bytes(d.k_dev, [host.rec0(2, 0, 0, 1), 5 << 32, 0] + d.com.root))
        for e in (5, 4, 0):                                      # signed, and still not a step forward
            self.refused(d, host.gate_request(d.com, d.tag, d.rec0, host.T_EPOCH, [e]), host.E_ARG)
        self.assertEqual(len(d.gate(host.T_EPOCH, [6])), 2)
        self.assertEqual(d.reboot()[1], host.LC_READY)
        self.assertEqual(d.rec1 >> 32, 6)

    def test_a_statement_is_for_one_transition_of_one_chip_once(self):
        d = common.provisioned()
        r0 = d.rec0
        good = host.gate_request(d.com, d.tag, r0, host.T_EPOCH, [5])
        self.refused(common.provisioned(n=1, k=1, flags=host.F_COUNTED), good)                     # another record word
        other = common.new_chip(puf=b"\x66" * 32)
        info = host.provision(other, common.owner(), d.com.root)
        other.reset()
        self.assertEqual(host.boot(other, info["helper_sig"])[1:4], [host.LC_READY, info["tag"][0], r0])
        self.assertEqual(other.transact(good), err(host.OP_GATE, host.E_AUTH))                     # a second chip
        for req in (good[:1] + [6] + good[2:], good[:2] + [1] + good[3:], good[:3] + [1] + good[4:],   # other arguments
                    [good[0] ^ ((host.T_EPOCH ^ host.T_RETIRE) << 48)] + good[1:],                 # another type
                    host.gate_request(common.committee(tag=b"outsider"), d.tag, r0, host.T_EPOCH, [5]),
                    host.gate_request(d.com, d.tag, r0, host.T_EPOCH, [5], nonce=(1, 0))):     # as if a lease were pending
            self.refused(d, req)
        self.assertEqual(len(d.chip.transact(good)), 2)
        self.refused(d, good)                                    # replay: the sequence number has advanced
        for tag in ([d.tag[0] ^ 1, d.tag[1]], [d.tag[0], d.tag[1] ^ 1]):           # either word of the chip identifier
            self.refused(d, host.gate_request(d.com, tag, d.rec0, host.T_EPOCH, [9]))
        self.refused(d, host.gate_request(d.com, d.tag, r0, host.T_EPOCH, [9]))
        self.assertEqual(len(d.gate(host.T_EPOCH, [9])), 2)

    def test_types_and_shape(self):
        d = common.provisioned()
        self.assertEqual(d.chip.transact(host.cmd(host.OP_GATE, [0, 0], arg=host.T_EPOCH)), err(host.OP_GATE, host.E_LEN))
        self.assertEqual(d.chip.transact(host.cmd(host.OP_GATE, [0, 0, 0], arg=host.T_LEASE)), err(host.OP_GATE, host.E_ARG))
        self.refused(d, host.gate_request(d.com, d.tag, d.rec0, 9, [1]), host.E_ARG)           # signed, unknown type
        self.refused(d, host.cmd(host.OP_GATE, [1, 0, 0], arg=host.T_EPOCH))                       # no statement at all
        good = host.gate_request(d.com, d.tag, d.rec0, host.T_EPOCH, [5])
        for cut in (4, 5, 9, 9 + PKG // 2, len(good) - 1):       # a short statement is refused, not a fault
            self.refused(d, host.cmd(host.OP_GATE, good[1:cut], arg=host.T_EPOCH))
        self.assertEqual(len(d.chip.transact(host.cmd(host.OP_GATE, good[1:] + [7, 7], arg=host.T_EPOCH))), 2)   # trailing words are drained

    def test_every_part_of_the_signature_is_checked(self):
        d = common.provisioned()
        good = host.gate_request(d.com, d.tag, d.rec0, host.T_EPOCH, [5])
        base = 1 + 3 + 5                                         # header, arguments, index word and public key
        for name, (off, n) in LAY.items():
            for i in {0, n // 2, n - 1} if n else ():
                bad = list(good)
                bad[base + off + i] ^= 1 << 31
                self.refused(d, bad)
        for i in (5, 6, 7, 8):                                   # the stated public key: seed and root
            bad = list(good)
            bad[i] ^= 1
            self.refused(d, bad)
        self.assertEqual(len(d.chip.transact(good)), 2)

    def test_stated_values_must_be_the_computed_ones_in_both_passes(self):
        """ARCHITECTURE.md 4.3: the chain ends (and FORS roots) the host states are bound to the ones the
        chip computed by the hash chain in pass 2a and to the ones T absorbs by the fingerprint."""
        d = common.provisioned()
        good = host.gate_request(d.com, d.tag, d.rec0, host.T_EPOCH, [5])
        base = 9
        for a, b in (("roots_a", "roots_b"), ("ends_a0", "ends_b0")):
            (oa, n), (ob, _) = LAY[a], LAY[b]
            for word in (0, 1, n - 2, n - 1, n // 2):
                for where in ((oa,), (ob,), (oa, ob)):           # 2a only; 2b only; the same wrong value in both
                    bad = list(good)
                    for o in where:
                        bad[base + o + word] ^= 1 << 7
                    self.refused(d, bad)
            bad = list(good)                                     # two values exchanged, in both passes
            for o in (oa, ob):
                bad[base + o:base + o + 2], bad[base + o + 2:base + o + 4] = bad[base + o + 2:base + o + 4], bad[base + o:base + o + 2]
            self.refused(d, bad)
            bad = list(good)                                     # words exchanged between the two halves of one value
            for o in (oa, ob):
                bad[base + o], bad[base + o + 1] = bad[base + o + 1], bad[base + o]
            self.refused(d, bad)
        self.assertEqual(len(d.chip.transact(good)), 2)

    def test_retire(self):
        d = common.provisioned()
        self.assertEqual(len(d.gate(host.T_RETIRE, [])), 2)
        self.assertEqual(d.chip.m.lc, isa.LC_LOCKED)
        self.assertTrue(no_keys(d.chip))
        self.assertEqual(signs(d), err(host.OP_CTH, host.E_NOKEY))
        d.chip.reset()
        self.assertEqual(host.boot(d.chip, d.info["helper_sig"]), err(host.OP_BOOT, host.E_RETIRED))
        self.assertTrue(no_keys(d.chip))
        self.assertEqual(d.chip.m.lc, isa.LC_LOCKED)

    def test_rotate(self):
        d = common.provisioned()
        new = common.committee(3, 2, tag=b"successor")
        self.refused(d, host.gate_request(d.com, d.tag, d.rec0, host.T_ROTATE, new.root + [0]), host.E_ARG)
        self.refused(d, host.gate_request(new, d.tag, d.rec0, host.T_ROTATE, new.root + [2]))  # the successor cannot let itself in
        self.assertEqual(d.gate(host.T_ROTATE, new.root + [2])[1], host.rec0(2, 1, 0, 2))
        self.assertEqual([state(d.chip, 3), state(d.chip, 4)], new.root)
        self.refused(d, host.gate_request(d.com, d.tag, d.rec0, host.T_EPOCH, [1]))            # the old authority is out
        d.com = new
        self.assertEqual(len(d.gate(host.T_EPOCH, [1])), 2)
        self.assertEqual(d.reboot()[3], host.rec0(3, 1, 0, 2))
        self.assertEqual(len(d.gate(host.T_EPOCH, [2])), 2)

    def test_transition_record_is_read_back(self):
        import test_commands as tc
        for typ, args in ((host.T_EPOCH, [5]), (host.T_RETIRE, []), (host.T_ROTATE, common.committee(tag=b"x").root + [1])):
            d = common.provisioned()
            req = host.gate_request(d.com, d.tag, d.rec0, typ, args)
            d.chip.m.fram.mem = tc.DeadFram(bytes(d.chip.fram))
            self.assertEqual(d.chip.transact(req), err(host.OP_GATE, host.E_RECORD_IO))
            self.assertEqual(d.chip.m.lc, isa.LC_READY)


class Committee(unittest.TestCase):
    """G3: k signatures by distinct members of the pinned committee."""

    def setUp(self):
        self.d = common.provisioned(n=5, k=3)
        self.m = host.stmt_transition(self.d.tag, self.d.rec0, host.T_EPOCH, (0, 0), [5, 0, 0])

    def req(self, items):
        return host.cmd(host.OP_GATE, [5, 0, 0] + [w for it in items for w in it], arg=host.T_EPOCH)

    def refused(self, items):
        c = self.d.chip
        before = ([state(c, i) for i in range(5)], bytes(c.fram))
        self.assertEqual(c.transact(self.req(items)), err(host.OP_GATE, host.E_AUTH))
        self.assertEqual(([state(c, i) for i in range(5)], bytes(c.fram), c.pins["VERIFY_OK"]), before + (0,))

    def test_threshold_of_distinct_members(self):
        com, m = self.d.com, self.m
        it = [com.item(i, m) for i in range(5)]
        self.assertEqual(self.d.rec0 >> 56, 3)
        self.refused([it[0], it[1]])                             # k - 1
        self.refused([it[0], it[0], it[0]])                      # one member three times
        self.refused([it[0], it[1], it[1]])
        self.refused([it[1], it[0], it[2]])                      # not in increasing order
        self.refused([it[0], it[2], it[1]])
        self.refused([it[4], it[4], it[4]])
        self.refused([])
        self.assertEqual(len(self.d.chip.transact(self.req([it[0], it[2], it[4]]))), 2)
        self.assertEqual(self.d.rec1 >> 32, 5)

    def test_members_are_the_pinned_ones(self):
        com, m = self.d.com, self.m
        it = [com.item(i, m) for i in range(5)]
        outsider = host.Committee([host.signer(b"x%d" % i, common.SLH) for i in range(5)], 3)      # a tree of its own
        self.refused([outsider.item(i, m) for i in range(3)])
        self.refused([it[0], it[1], outsider.item(2, m)])
        mixed = outsider.item(2, m)
        mixed[5:5 + 2 * com.depth] = com.path(2)                 # an outsider's key under a member's path
        mixed[-2 * com.depth:] = com.path(2)
        self.refused([it[0], it[1], mixed])
        relabel = list(it[1])
        relabel[0] = 2 | (com.depth << 32)                       # member 1 presenting itself as index 2
        self.refused([it[0], relabel, it[3]])
        short = com.item(2, m, depth=com.depth - 1)              # a path that stops below the root
        self.refused([it[0], it[1], short])
        long = [2 | (17 << 32)] + it[2][1:]                      # a path length the chip does not accept
        self.refused([it[0], it[1], long])
        for pos in (5, 5 + 2 * com.depth - 1, len(it[2]) - 1, len(it[2]) - 2 * com.depth):         # either copy of the path
            bad = list(it[2])
            bad[pos] ^= 1
            self.refused([it[0], it[1], bad])
        self.assertEqual(len(self.d.chip.transact(self.req(it[:3]))), 2)

    def test_stated_key_and_signature_root_are_both_checked(self):
        com, m = self.d.com, self.m
        it = [com.item(i, m) for i in range(5)]
        mem = com.members[2]
        head, path = [2 | (com.depth << 32)], com.path(2)
        imp = host.Slh(b"impostor", common.SLH, pk_seed=mem.pk_seed)             # the member's public seed, another secret
        sig = imp.sign(m, digest_root=mem.pk_root)
        self.refused([it[0], it[1], head + host.words_of(mem.pk) + path + host.package(mem.pk, m, sig, common.SLH) + path])
        other_root = bytes(range(16))                                            # the member's signature under a root not its own
        stated = mem.pk_seed + other_root
        sig = mem.sign(m, digest_root=other_root)
        self.refused([it[0], it[1], head + host.words_of(stated) + path + host.package(stated, m, sig, common.SLH) + path])
        self.assertEqual(len(self.d.chip.transact(self.req(it[:3]))), 2)

    def test_path_length_is_bounded(self):
        mem = host.signer(b"deep", common.SLH)
        for depth, accepted in ((16, True), (17, False)):
            sibs = [[i + 1, i + 2] for i in range(depth)]
            root = host.leaf_hash(0, mem.pk)
            for s in sibs:
                root = host.node_hash(root, s)
            c = common.new_chip()
            info = host.provision(c, common.owner(), root)
            c.reset()
            rsp = host.boot(c, info["helper_sig"])
            m = host.stmt_transition(info["tag"], rsp[3], host.T_EPOCH, (0, 0), [5, 0, 0])
            path = [w for s in sibs for w in s]
            item = [depth << 32] + host.words_of(mem.pk) + path + host.package(mem.pk, m, mem.sign(m), common.SLH) + path
            got = c.transact(host.cmd(host.OP_GATE, [5, 0, 0] + item, arg=host.T_EPOCH))
            self.assertEqual(len(got) == 2, accepted, depth)

    def test_an_index_that_would_wrap_the_order_check_is_refused(self):
        """A leaf hashed with index 2^32 - 1: after it the lowest index allowed next would wrap to 0."""
        mems = [host.signer(b"w%d" % i, common.SLH) for i in range(8)]
        com = host.Committee(mems, 3, indices=list(range(7)) + [0xFFFFFFFF])
        c = common.new_chip()
        info = host.provision(c, common.owner(), com.root, k=3)
        c.reset()
        rsp = host.boot(c, info["helper_sig"])
        m = host.stmt_transition(info["tag"], rsp[3], host.T_EPOCH, (0, 0), [5, 0, 0])
        last = com.item(7, m)
        for items in ([last, last, last], [last, com.item(0, m), com.item(0, m)], [com.item(0, m), last, last]):
            self.assertEqual(c.transact(host.cmd(host.OP_GATE, [5, 0, 0] + [w for it in items for w in it], arg=host.T_EPOCH)),
                             err(host.OP_GATE, host.E_AUTH))
        ok = [com.item(i, m) for i in (0, 3, 6)]
        self.assertEqual(len(c.transact(host.cmd(host.OP_GATE, [5, 0, 0] + [w for it in ok for w in it], arg=host.T_EPOCH))), 2)

    def test_the_signature_is_the_members_own(self):
        com, m = self.d.com, self.m
        it = [com.item(i, m) for i in range(5)]
        other = host.stmt_transition(self.d.tag, self.d.rec0, host.T_EPOCH, (0, 0), [6, 0, 0])
        self.refused([it[0], it[1], com.item(2, other)])         # a member's signature on another transition
        swapped = it[2][:5 + 2 * com.depth] + it[3][5 + 2 * com.depth:-2 * com.depth] + it[2][-2 * com.depth:]
        self.refused([it[0], it[1], swapped])                    # member 2's key, member 3's signature
        lying = list(it[2])
        lying[3] ^= 1                                            # the stated root is not the key's
        self.refused([it[0], it[1], lying])
        self.assertEqual(len(self.d.chip.transact(self.req(it[2:]))), 2)


class EntropySource(unittest.TestCase):
    def enrol(self, **kw):
        c = common.new_chip(trng=None)
        c.m.trng = units.TrngUnit(5, **kw) if kw.get("present", True) else None
        host.boot(c)
        return c, c.transact(host.cmd(host.OP_ENROL))

    def test_a_working_source(self):
        c, rsp = self.enrol()
        self.assertEqual(len(rsp), 7)
        t = c.m.trng
        self.assertTrue(t.armed)
        a, b = units.TRNG_PAIRS[t.pair]
        self.assertEqual(round(abs(t.offsets[a] - t.offsets[b]), 2), 0.15)       # the qualifying pair with the shortest beat
        first = c.log[-1]["unit_cycles"]["trng"]
        c.reset()
        host.boot(c)
        n2 = c.transact(host.cmd(host.OP_ENROL))[5:]
        self.assertNotEqual(n2, rsp[5:])
        self.assertGreater(first, 200_000)                       # start-up: 28 pairs, then 1,024 counts, then the nonce
        self.assertLess(first, 3_000_000)                        # at most 0.12 s
        self.assertGreater(c.log[-1]["unit_cycles"]["trng"], 200_000)            # a reset disarms the source
        d = common.provisioned(host.F_LEASED)                    # second use in one session: no start-up
        d.chip.transact(host.cmd(host.OP_NONCE))
        self.assertLess(d.chip.log[-1]["unit_cycles"]["trng"], 120_000)          # 512 counts: at most 4.8 ms

    def test_sources_that_must_be_refused(self):
        far = (0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5)             # every pair beats too fast: no jitter to see
        close = (0, 0.003, 0.006, 0.009, 0.012, 0.015, 0.018, 0.021)             # every pair beats too slowly
        for kw in (dict(present=False), dict(kappa=0.0), dict(kappa=0.3), dict(locked=range(28)),
                   dict(flicker=1.5, kappa=0.3), dict(offsets=far), dict(offsets=close)):
            c, rsp = self.enrol(**kw)
            self.assertEqual(rsp, err(host.OP_ENROL, host.E_TRNG), kw)
            self.assertEqual(c.m.lc, isa.LC_BLANK)
            self.assertFalse(c.m.trng and c.m.trng.armed)
            self.assertLess(c.log[-1]["unit_cycles"]["trng"], 3_600_000)         # slow pairs are abandoned early

    def test_selection_avoids_bad_pairs(self):
        good = units.TRNG_PAIRS.index((5, 6))                    # in the second half of the 28 pairs
        c, rsp = self.enrol(locked=set(range(28)) - {good}, offsets=(0, 0.11, 0.37, 0.52, 0.80, 0.95, 1.07, 1.71))
        self.assertEqual(len(rsp), 7)
        self.assertEqual(c.m.trng.pair, good)
        # the pair with the shortest beat wins, wherever it comes in the order
        c, rsp = self.enrol(offsets=(0, 0.16, 0.27, 0.80, 1.2, 1.6, 2.0, 2.4))
        self.assertEqual(units.TRNG_PAIRS[c.m.trng.pair], (0, 1))
        # a pair that qualifies on variance and beat length but fails a health test is passed over
        P = units.TRNG_PAIRS
        c, rsp = self.enrol(flicker=1.5, nonwhite={P.index((2, 3)), P.index((4, 5))})
        self.assertEqual((len(rsp), P[c.m.trng.pair]), (7, (0, 1)))

    def test_each_threshold_decides_alone(self):
        """Sources that only one test stands against."""
        # variance between the health limit (1.25) and the selection limit (2.0) on every pair that beats
        c, rsp = self.enrol(offsets=(0, 0, 0, 0, 0.2, 0.2, 0.2, 0))
        self.assertEqual(rsp, err(host.OP_ENROL, host.E_TRNG))
        # strong jitter on beats that are too short to resolve it
        c, rsp = self.enrol(kappa=3, offsets=(0, 0.3, 0.6, 0.9, 1.2, 1.5, 1.8, 2.1))
        self.assertEqual(rsp, err(host.OP_ENROL, host.E_TRNG))
        # run() calls of a first use: 0..111 selection (28 pairs x 4), 112..127 start-up test, 128..135 the nonce
        for script in ({113: dict(timeout=True)},                              # one missing beat in the start-up test
                       {r: dict(kappa=0.3) for r in range(116, 128)},          # jitter gone after the first test block
                       {r: dict(kappa=0.3) for r in range(112, 128)},          # ... during the whole start-up test only
                       {130: dict(timeout=True)}, {130: dict(short=True)}):    # a bad beat while the nonce is drawn
            c, rsp = self.enrol(script=script)
            self.assertEqual(rsp, err(host.OP_ENROL, host.E_TRNG), script)

    def test_a_bad_beat_on_an_armed_source_restarts_it(self):
        for ev in (dict(timeout=True), dict(short=True)):
            d = common.provisioned(host.F_LEASED)
            t = d.chip.m.trng
            t.script = {t.runs + 5: ev}
            self.assertEqual(len(d.chip.transact(host.cmd(host.OP_NONCE))), 3)
            self.assertGreater(d.chip.log[-1]["unit_cycles"]["trng"], 200_000)   # the start-up ran again

    def test_the_nonce_is_the_conditioned_raw_words(self):
        d = common.provisioned(host.F_LEASED)
        twin = copy.deepcopy(d.chip.m)
        raw = []
        for _ in range(2):
            twin.trng.clear()
            for _ in range(4):
                twin.trng.run()
                raw.append(twin.trng.raw)
        want = host.ts(raw + [twin.puf.noise()], host.D_NONCE)
        self.assertEqual(d.chip.transact(host.cmd(host.OP_NONCE))[1:], want)
        self.assertEqual(len(set(raw)), 8)

    def test_a_source_that_degrades_after_start_up(self):
        d = common.provisioned(host.F_LEASED)
        c = d.chip
        self.assertTrue(c.m.trng.armed)
        c.m.trng.kappa = 0.0                                     # the jitter goes away
        self.assertEqual(c.transact(host.cmd(host.OP_NONCE)), err(host.OP_NONCE, host.E_TRNG))
        self.assertFalse(c.m.trng.armed)
        self.assertEqual([state(c, 7), state(c, 8)], [state(d.chip, 7), state(d.chip, 8)])
        c.m.trng.kappa = 1.0
        self.assertEqual(len(c.transact(host.cmd(host.OP_NONCE))), 3)
        c.m.trng.locked = {c.m.trng.pair}                        # the selected pair locks: another one is found
        self.assertEqual(len(c.transact(host.cmd(host.OP_NONCE))), 3)
        self.assertNotIn(c.m.trng.pair, c.m.trng.locked)
        c.m.trng.flicker = 2.0
        c.m.trng.kappa = 0.2
        self.assertEqual(c.transact(host.cmd(host.OP_NONCE)), err(host.OP_NONCE, host.E_TRNG))

    def test_nonces_use_both_sources(self):
        a = common.provisioned(host.F_LEASED)
        b = copy.deepcopy(a)
        b.chip.m.puf._noise = (99, 0)                            # the same TRNG stream, other counter noise
        self.assertNotEqual(a.chip.transact(host.cmd(host.OP_NONCE)), b.chip.transact(host.cmd(host.OP_NONCE)))
        self.assertEqual(a.chip.transact(host.cmd(host.OP_NONCE, [1])), err(host.OP_NONCE, host.E_LEN))

    def test_enrolment_needs_the_puf(self):
        c = common.new_chip(puf=None)
        host.boot(c)
        self.assertEqual(c.transact(host.cmd(host.OP_ENROL)), err(host.OP_ENROL, host.E_PUF))


class ParameterSets(unittest.TestCase):
    def test_two_layers(self):
        """The reduced set used everywhere else has one hypertree layer; this one has two, so the step
        from a layer to the next (tree index, leaf index, layer address) is exercised and refused when bent."""
        d = common.provisioned(slh="small")
        self.assertEqual(d.lc, isa.LC_READY)
        lay = host.package_layout("small")
        good = host.gate_request(d.com, d.tag, d.rec0, host.T_EPOCH, [5])
        for name in ("wots1", "ends_a1", "ends_b1", "path1", "path0"):
            bad = list(good)
            bad[9 + lay[name][0] + 3] ^= 1
            self.assertEqual(d.chip.transact(bad), err(host.OP_GATE, host.E_AUTH), name)
        self.assertEqual(len(d.chip.transact(good)), 2)
        for i in range(12):                                      # other messages: other tree and leaf indices
            self.assertEqual(len(d.gate(host.T_EPOCH, [6 + i])), 2, i)

    @unittest.skipIf(common.FAST, "skipped in mutation runs: the real parameter set takes about 10 s")
    def test_slh_dsa_shake_128s(self):
        """The real parameter set: enrolment, commit and boot under an owner root with a FIPS 205
        SLH-DSA-SHAKE-128s key, and the measured clocks of one verification."""
        d = common.provisioned(slh="128s")
        self.assertEqual(d.lc, isa.LC_READY)
        log = [x for x in d.chip.log if x["op"] == host.OP_BOOT][-1]
        self.assertEqual(len(d.info["helper_sig"]), 4 + 2018)
        self.assertTrue(2_000 < log["unit_calls"]["keccak"] < 4_500)
        self.assertLess(log["cycles"] - log["unit_cycles"]["puf"], 5_000_000)
        bad = list(d.info["helper_sig"])
        bad[4 + host.package_layout("128s")["ends_b6"][0] + 69] ^= 1
        d.chip.reset()
        self.assertEqual(host.boot(d.chip, bad), err(host.OP_BOOT, host.E_AUTH))


class Invariants(unittest.TestCase):
    def test_working_rows_are_clear_and_no_key_word_leaves(self):
        d = common.provisioned(host.F_LEASED | host.F_COUNTED, n=3, k=2, booted=False)
        c = d.chip
        secret = set(d.k_dev) | set(c.m.puf.ideal) | set(host.words_of(d.seed + d.prf))
        c.reset()
        steps = [lambda: d.boot(), lambda: c.transact(host.cmd(host.OP_NONCE)), lambda: d.lease(0, 9),
                 lambda: d.gate(host.T_EPOCH, [2]), lambda: signs(d, 1), lambda: d.gate(host.T_EPOCH, [1]),
                 lambda: d.gate(host.T_ROTATE, d.com.root + [2]), lambda: d.gate(host.T_RETIRE, [])]
        for f in steps:
            rsp = f()
            self.assertTrue(common.working_rows_clear(c))
            self.assertEqual(c.log[-1]["key_words_emitted"], [])
            self.assertFalse(secret & set(rsp))
            self.assertIsNone(c.m.puf.rsp)
        self.assertFalse(any(w.to_bytes(8, "little") in bytes(c.fram) for w in secret))

    def test_verification_is_public_computation(self):
        """No key is in the lanes while a statement is verified: the verifier could run on a blank chip."""
        d = common.provisioned()
        seen = []

        def trace(pc, w, m):
            seen.append(m.keyed or m.t_lanes or m.t_h)
        d.chip.m.trace = trace
        d.gate(host.T_EPOCH, [4])
        sv = d.chip.rom.labels
        self.assertGreater(len(seen), 100_000)
        d.chip.m.trace = None
        keyed_steps = sum(seen)
        self.assertLess(keyed_steps, 200)                        # only the record write at the very end
        self.assertEqual(seen[:len(seen) - 200].count(True), 0)
        self.assertIn("sv", sv)


if __name__ == "__main__":
    unittest.main()
