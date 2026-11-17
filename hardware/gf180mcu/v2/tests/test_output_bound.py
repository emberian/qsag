"""The structural rules of model/machine.py (R1..R12), each with a microprogram the decoder refuses, and
the static ROM checks. Fixtures are in fixtures.py; none of them is in the ROM.

Layers:
  1. static   the ROM's response writers and declassification points are exactly the reviewed manifest,
              and the image matches the hardwired layout;
  2. decoder  key rows, key-derived data (taint), the response bound, the FRAM path, the end action
              and the lifecycle gate;
  3. values   no word of any response in the regression equals a key row (test_commands, replay).
"""
import unittest

import common
import chip
import host
import isa
import romcheck
import uasm
from fixtures import K, PRF, SEED, TEST_OP, rom_with, run
from framing import LinkError
from machine import ControlFault, Machine

KEYED = " KMOV k_seed0 > l0\n KEC 12\n"                # a completed keyed permutation: lanes are key-derived


class Base(unittest.TestCase):
    def fault(self, body, needle, **kw):
        with self.assertRaises(ControlFault) as cm:
            run(body, **kw)
        self.assertIn(needle, str(cm.exception))

    def ok(self, body, **kw):
        return run(body, **kw)


class StaticManifest(unittest.TestCase):
    def findings(self, old, new, config="S", count=1):
        src = chip.read_sources(config)
        self.assertEqual(sum(t.count(old) for _, t in src), count, old)
        return romcheck.check(uasm.assemble([(n, t.replace(old, new)) for n, t in src]), romcheck.load_manifest())

    def test_shipped_roms_pass(self):
        for cfg in "SL":
            self.assertEqual(romcheck.check(chip.build_rom(cfg), romcheck.load_manifest()), [])

    def test_manifest_covers_both_configurations(self):
        places = {p for cfg in "SL" for p, _ in chip.build_rom(cfg).pushes() + chip.build_rom(cfg).releases()}
        self.assertEqual(places, set(romcheck.load_manifest()))

    def test_unlisted_push_is_found(self):
        f = self.findings("            PUSH H\n            PUSH H\n            END", "            PUSH H\n            PUSH H\n            PUSH t1\n            END")
        self.assertTrue(any("is not in the manifest" in x and "r33" in x for x in f), f)

    def test_unlisted_release_is_found(self):
        f = self.findings("w_emit:     REL  l0", "w_emit:     REL  l2\n            REL  l0")
        self.assertTrue(any("rel:r2" in x for x in f), f)

    def test_changed_source_row_is_found(self):
        f = self.findings("w_emit:     REL  l0", "w_emit:     REL  l6")
        self.assertTrue(any("w_emit+0" in x for x in f), f)

    def test_push_turned_into_release_is_found(self):
        f = self.findings("kq_loop:    PUSH l0+X x+", "kq_loop:    REL  l0+X x+")
        self.assertTrue(any("kq_loop+0" in x for x in f), f)

    def test_removed_push_is_found(self):
        f = self.findings("fo_emit:    REL  l0\n            REL  l1", "fo_emit:    REL  l0")
        self.assertTrue(any("fo_emit+1 has no such instruction" in x for x in f), f)

    def test_unlisted_tag_compare_and_fram_write_are_found(self):
        f = self.findings("            CMPT l0\n            DIN\n            CMPT l1\n            BR   Z e_mac", "            CMPT l0\n            CMPT l2\n            DIN\n            CMPT l1\n            BR   Z e_mac")
        self.assertTrue(any("cmpt:r2" in x for x in f), f)
        f = self.findings("            FRAM WWORD l1\n", "            FRAM WWORD l1\n            FRAM WWORD l0\n")
        self.assertTrue(any("fram:r0" in x and "fram_write+4" in x for x in f), f)


class StaticShape(unittest.TestCase):
    """One refusing image per rule of romcheck.py."""

    def findings_for(self, body, where="rom", end=True):
        return romcheck.check(rom_with(body, where, end=end), romcheck.load_manifest())

    def expect(self, needle, body, **kw):
        f = self.findings_for(body, **kw)
        self.assertTrue(any(needle in x for x in f), (needle, body, f))

    def test_transfers(self):
        self.expect("transfer to 0", " BR idle")
        self.expect("transfer to 0", " CALL idle")
        self.expect("transfer to", " BR @2000")
        self.expect("transfer to 60", " BR @60")                       # a trap word of the key range

    def test_key_instructions_outside_the_key_range(self):
        for ins in (" KEYWR > k_host0", " CTL SETKV", " CTL AUTH", " CTL NONCE"):
            self.expect("key instruction outside the key range", ins)
        self.assertEqual([x for x in self.findings_for(" CTL NONCE", where="key") if "key instruction" in x], [])

    def test_fram_instructions_outside_the_record_range(self):
        for ins in (" FRAM RSTART", " FRAM WWORD A0", " FRAM DONE"):
            self.expect("FRAM instruction outside the record range", ins)
        self.assertEqual([x for x in self.findings_for(" FRAM DONE", where="rec") if "record range" in x], [])

    def test_fram_write_source(self):
        self.expect("FRAM WWORD of row", " FRAM WWORD t0", where="rec")
        self.expect("FRAM WWORD of row", " FRAM WWORD l2", where="rec")
        self.expect("FRAM WWORD of row", " FRAM WWORD A0+X", where="rec")

    def test_rows_named_directly(self):
        self.expect("read of key row", " LD k_seed0")
        self.expect("write of out row", " ST out0")
        self.expect("read of out row", " LD #1\n HDR #1\n PUSH out0")
        self.expect("write of kwork row", " ST r25")
        self.expect("write of key row", " FRAM RWORD > k_dev0", where="rec")

    def test_kmov_operands(self):
        self.expect("KMOV operands", " KMOV t0 > l0")
        self.expect("KMOV operands", " KMOV k_seed0 > l17")
        self.expect("KMOV operands", " KMOV k_seed0 > l0+X")

    def test_release_operands(self):
        self.expect("not a rate lane", " REL l17")
        self.expect("not a rate lane", " CMPT t0")

    def test_disp_only_at_address_0(self):
        self.expect("DISP must be at address 0", " DISP")
        rom = chip.build_rom("S")
        bad = uasm.assemble(chip.read_sources("S"))
        bad.words[0] = isa.encode(isa.OP["NOP"])
        self.assertTrue(any("DISP must be at address 0" in x for x in romcheck.check(bad, romcheck.load_manifest())))
        self.assertEqual(rom.words[0], isa.encode(isa.OP["DISP"]))

    def test_trap_words(self):
        self.expect("illegal instruction", " ILL")
        bad = uasm.assemble(chip.read_sources("S"))
        pad = min(bad.padding)
        bad.words[pad] = isa.encode(isa.OP["NOP"])
        self.assertTrue(any("padding is not a trap word" in x for x in romcheck.check(bad, romcheck.load_manifest())))

    def test_canonical_encoding(self):
        bad = uasm.assemble(chip.read_sources("S"))
        a = bad.labels["ping"]
        bad.words[a] |= 1 << 9                                             # a stray bit in an unused field of LDF
        self.assertTrue(any("non-canonical encoding" in x for x in romcheck.check(bad, romcheck.load_manifest())))
        bad = uasm.assemble(chip.read_sources("S"))
        bad.words[a] = isa.encode(isa.OP["UN"], a=100)                     # a function code that does not exist
        self.assertTrue(any("does not disassemble" in x for x in romcheck.check(bad, romcheck.load_manifest())))

    def test_code_must_not_run_off_its_end(self):
        self.expect("runs past the end of the code", " NOP", end=False)                    # last word of the image
        self.expect("runs past the end of the code", " NOP", where="key", end=False)       # into the trap words
        self.assertEqual([x for x in self.findings_for(" NOP") if "runs past" in x], [])

    def test_entries_match_the_layout(self):
        bad = uasm.assemble(chip.read_sources("S"))
        bad.entries[host.OP_KEYLOAD] = (bad.entries[host.OP_KEYLOAD][0], isa.D_DIAG)
        self.assertTrue(any("provisioning class and key range disagree" in x for x in romcheck.check(bad, romcheck.load_manifest())))
        bad = uasm.assemble(chip.read_sources("S"))
        bad.entries[0x55] = (min(bad.padding), isa.D_DIAG)
        self.assertTrue(any("outside the code" in x for x in romcheck.check(bad, romcheck.load_manifest())))

    def test_image_has_an_end(self):
        rom = uasm.assemble([("t", "idle: DISP\nx: NOP\n BR x\n")])
        self.assertTrue(any("no END or FAIL" in x for x in romcheck.check(rom, {})))

    def test_layout_is_hardwired_not_read_from_the_image(self):
        """Moving the provisioning code out of its range does not move the range."""
        src = [(n, t.replace(".org KEY_END", ".org 40") if n == "fram.uc" else t) for n, t in chip.read_sources("S")]
        with self.assertRaises(uasm.AsmError):
            uasm.assemble(src)                                             # provisioning code no longer fits
        self.assertEqual((isa.KEY_LO, isa.KEY_HI, isa.REC_LO, isa.REC_HI, isa.ROM_BASE), (1, 63, 64, 127, 128))
        rom = chip.build_rom("S")
        self.assertEqual((rom.labels["fram_tag"], rom.labels["e_opcode"]), (isa.REC_LO, isa.ROM_BASE))
        self.assertFalse(hasattr(rom, "keyrange") or hasattr(rom, "epilogue"))


class KeyRows(Base):
    def test_baseline_fixture_runs(self):
        c, rsp = self.ok(" LD #2\n HDR #2\n LD #7\n PUSH H\n ST t0\n PUSH t0")
        self.assertEqual(rsp, [host.rhdr(TEST_OP, 16), 7, 7])
        self.assertTrue(common.working_rows_clear(c))

    def test_key_rows_are_not_readable(self):
        pre = " LD #1\n HDR #1\n SETX #%d\n" % (isa.KEY0 + 6 - isa.SCRATCH0)
        for ins in ("LD k_seed0", "XOR k_host1", "CMP k_prf0", "LD k_dev0", "PUSH k_seed0", "LD t0+X", "FADD k_dev1"):
            self.fault(pre + " " + ins, "key row", config="L")
        self.fault(" LD #1\n HDR #1\n REL k_seed0", "not a rate lane")
        self.fault(" CMPT k_seed0", "key row")
        self.fault(" FRAM WSTART\n FRAM WWORD k_seed0", "FRAM WWORD of row", where="rec")

    def test_key_rows_are_written_only_in_the_key_range_after_authorisation(self):
        self.fault(" LD #1\n ST k_seed0", "write of key row")
        self.fault(" LD #1\n KEYWR > k_seed0", "KEYWR outside the key range")
        self.fault(" CTL SETKV", "SETKV outside the key range")
        self.fault(" CTL AUTH", "AUTH outside the key range")
        self.fault(" CTL NONCE", "NONCE outside the key range")
        self.fault(" LD #1\n KEYWR > k_seed0", "KEYWR without authorisation", where="key")
        self.fault(" CTL SETKV", "SETKV without authorisation", where="key")
        self.fault(" CTL AUTH", "AUTH past the end of the payload", where="key")
        # a refused authorisation leaves the latch clear
        self.fault(" CTL AUTH\n LD #1\n KEYWR > k_seed0", "KEYWR without authorisation", where="key", payload=(1, 2))

    def test_authorised_key_write(self):
        """The positive path of the same fixture mechanism: nonce, authorisation, key write."""
        body = (" CTL NONCE\n LD #1\n ST l0\n LDF NONCE0 > t0\n LDF NONCE1 > t1\n CTL AUTH\n BR Z t_no\n"
                " LD #5\n KEYWR > k_seed0\n LD #0\n HDR #0\n END\nt_no: FAIL #12")
        owner = host.Owner()
        c = common.new_chip("S", owner=owner, rom=rom_with(body, "key"))
        nonce = c.m.entropy.__class__(1).draw()                           # same seed: the nonce the chip will draw
        sig = host.words_of(host.q.turboshake256(owner.key + host.bytes_of(nonce) + host.bytes_of([1, 0, 0, 0]), 16, 0x23))
        self.assertEqual(c.transact([host.hdr(TEST_OP, 0, 16)] + sig), [host.rhdr(TEST_OP, 0)])
        self.assertEqual(c.m.rf[isa.KEY0 + 6], 5)
        c = common.new_chip("S", owner=owner, rom=rom_with(body, "key"))
        self.assertEqual(c.transact([host.hdr(TEST_OP, 0, 16), sig[0], sig[1] ^ 1]), [host.rhdr(TEST_OP, 0, False, 12)])
        self.assertEqual(c.m.rf[isa.KEY0 + 6], 0)
        # with the authorisation given, the key write still goes to key rows only, and the attribute is not key-derived
        for tail, needle in ((" LD #5\n KEYWR > t0", "KEYWR destination is not a key row"),
                             (" LD #5\n KEYWR > l3", "KEYWR destination is not a key row"),
                             (" WIPE #3\n KMOV k_dev0 > l0\n KEC 12\n LD l0\n CTL SETKV", "key attribute from key-derived data")):
            c = common.new_chip("S", owner=owner, rom=rom_with(body.replace(" LD #5\n KEYWR > k_seed0", tail), "key"))
            with self.assertRaises(ControlFault) as cm:
                c.transact([host.hdr(TEST_OP, 0, 16)] + sig)
            self.assertIn(needle, str(cm.exception))

    def test_out_and_work_rows_are_not_addressable(self):
        self.fault(" LD #1\n ST out0", "write of out row")
        self.fault(" LD out1", "read of out row")
        self.fault(" LD #1\n HDR #1\n PUSH out0", "PUSH of out row")
        self.fault(" KEC 24\n LD r25", "read of kwork row")
        self.fault(" LD #1\n ST r31", "write of kwork row")
        self.fault(" LD r64", "read of none row")                         # configuration S has 64 rows

    def test_key_in_lanes_cannot_be_moved_or_emitted(self):
        self.fault(" LD #1\n HDR #1\n KMOV k_seed0 > l0\n PUSH l0", "while a key is in the lanes")
        self.fault(" LD #1\n HDR #1\n KMOV k_seed0 > l0\n REL l0", "while a key is in the lanes")
        self.fault(" KMOV k_seed0 > l0\n LD l0", "while a key is in the lanes")
        self.fault(" KMOV k_seed0 > l0\n LD #0\n CMP l0", "while a key is in the lanes")
        self.fault(" KMOV k_seed0 > l0\n LD #0\n CMPT l0", "while a key is in the lanes")
        self.fault(" KMOV k_seed0 > l0\n LD #0\n XOR l0 > t0", "while a key is in the lanes")
        self.fault(" KMOV k_seed0 > l0\n LD #0\n XOR l0 > l1", "while a key is in the lanes")
        for op in ("ADD", "SUB", "AND", "OR", "LD"):                      # only absorption may touch the lane
            self.fault(" KMOV k_seed0 > l0\n LD #0\n %s l0 > l0" % op, "while a key is in the lanes")
        self.fault(" KMOV k_seed0 > l0\n LD #0\n FADD l0 > l0", "while a key is in the lanes", config="L")
        self.fault(" KMOV k_seed0 > l0\n WIPE #2\n LD l0", "while a key is in the lanes")     # a partial wipe does not clear it
        self.fault(" KMOV k_dev0 > l0\n FRAM WSTART\n FRAM WWORD l0", "while a key is in the lanes", where="rec")
        self.fault(" KMOV k_seed0 > l17", "not a rate lane")
        self.fault(" KMOV t0 > l0", "not a key row")

    def test_hold_register_is_cleared_after_touching_a_key(self):
        c, rsp = self.ok(" LD #2\n HDR #2\n KMOV k_seed0 > l0\n ST t0\n LD #0\n XOR l0 > l0\n ST t1\n KEC 24\n PUSH t0\n PUSH t1")
        self.assertEqual(rsp[1:], [0, 0])               # without the clear the stores would be refused (R6)
        self.assertEqual(c.log[-1]["key_words_emitted"], [])

    def test_capacity_is_not_readable_in_a_keyed_command(self):
        c, rsp = self.ok(" LD #17\n HDR #17\n" + KEYED + " SETX #0\nq: REL l0+X x+\n BXNE #17 q")
        self.assertEqual(len(rsp), 18)
        for lane in (17, 20, 24):
            self.fault(KEYED + " LD l%d" % lane, "capacity lane")
            self.fault(" LD #1\n HDR #1\n" + KEYED + " PUSH l%d" % lane, "capacity lane")
            self.fault(" LD #1\n HDR #1\n" + KEYED + " REL l%d" % lane, "not a rate lane")
        self.fault(" LD #18\n HDR #18\n" + KEYED + " SETX #0\nq: REL l0+X x+\n BXNE #18 q", "not a rate lane")
        self.fault(KEYED + " WIPE #3\n KEC 12\n LD l17", "capacity lane")       # keyed lasts until the command ends
        c, rsp = self.ok(" LD #1\n HDR #1\n KEC 12\n PUSH l24", keys=False)    # no key in the command: the state is public
        self.assertEqual(len(rsp), 2)


class Taint(Base):
    """R5..R8: key-derived data reaches nothing outside the lanes except through REL, CMPT and the record tag."""

    def test_key_derived_data_cannot_reach_the_response(self):
        self.fault(" LD #1\n HDR #1\n" + KEYED + " PUSH l0", "PUSH of key-derived data")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " LD l0\n PUSH H", "PUSH of key-derived data")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " LD l0\n UN NIB\n PUSH H", "PUSH of key-derived data")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " LD #5\n XOR l3\n PUSH H", "PUSH of key-derived data")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " LD l0\n ADD #1\n PUSH H", "PUSH of key-derived data")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " LD l0\n FADD l1\n PUSH H", "PUSH of key-derived data", config="L")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " LD #1\n FADD l1\n PUSH H", "PUSH of key-derived data", config="L")

    def test_key_derived_data_cannot_leave_the_lanes(self):
        for dst in ("t0", "pin0", "st1"):
            self.fault(KEYED + " LD l0\n ST %s" % dst, "store of key-derived data")
        self.fault(KEYED + " LD #1\n XOR l0 > t3", "store of key-derived data")
        self.fault(KEYED + " LD l1\n UN SHR8 > t0", "store of key-derived data")
        self.fault(KEYED + " LD l0\n ST c5", "store of key-derived data", config="L")
        self.fault(KEYED + " LD l0\n FLD RED > t0", "store of key-derived data", config="L")

    def test_lane_to_lane_moves_stay_tainted(self):
        """What the signer does between chain steps is allowed, and the result is still key-derived."""
        move = KEYED + " LD l0\n ST l6\n WIPE #2\n"
        self.fault(" LD #1\n HDR #1\n" + move + " PUSH l6", "PUSH of key-derived data")
        self.fault(move + " LD l6\n ST t0", "store of key-derived data")
        c, rsp = self.ok(" LD #1\n HDR #1\n" + move + " KEC 24\n REL l0")
        self.assertEqual(len(rsp), 2)

    def test_key_derived_data_cannot_set_length_counts_or_index(self):
        self.fault(KEYED + " LD l0\n AND #7\n HDR #8", "response length from key-derived data")
        self.fault(KEYED + " LD l0\n SETC 0 H", "loop count from key-derived data")
        self.fault(KEYED + " LD l0\n SETC 1 H", "loop count from key-derived data")
        self.fault(KEYED + " LD l0\n SETX H", "index from key-derived data")

    def test_key_derived_data_cannot_steer_a_branch(self):
        self.fault(KEYED + " LD l0\nx: BR HZ x", "branch on key-derived data")
        self.fault(KEYED + " LD l0\nx: BR HNZ x", "branch on key-derived data")
        self.fault(KEYED + " LD #0\n CMP l0\nx: BR Z x", "branch on a key-derived compare result")
        self.fault(KEYED + " LD l0\n CMP #0\nx: BR NZ x", "branch on a key-derived compare result")
        self.fault(KEYED + " LD l0\n ADD #1\nx: BR CY x", "branch on a key-derived carry")
        self.fault(KEYED + " LD #1\n SUB l0\nx: BR NC x", "branch on a key-derived carry")
        self.fault(KEYED + " LD #0\n CMP l0\n CTL VOK", "verdict pin from a key-derived compare result")
        self.fault(KEYED + " LD #0\n CMP l0\n LD #0\n HDR #0 okz", "response flag from a key-derived compare result")

    def test_key_derived_data_cannot_reach_the_fram_or_the_key_attribute(self):
        self.fault(KEYED + " LD l0\n FRAM WSTART", "FRAM slot from key-derived data", where="rec")
        self.fault(KEYED + " LD l0\n FRAM RSTART", "FRAM slot from key-derived data", where="rec")
        self.fault(KEYED + " LD l0\n ST A0", "store of key-derived data", where="rec")

    def test_taint_is_cleared_only_by_wiping_all_lanes(self):
        self.fault(" LD #1\n HDR #1\n" + KEYED + " WIPE #1\n PUSH l9", "PUSH of key-derived data")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " WIPE #2\n PUSH l0", "PUSH of key-derived data")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " KEC 12\n KEC 24\n PUSH l0", "PUSH of key-derived data")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " LD #9\n ST l0\n PUSH l0", "PUSH of key-derived data")   # coarse on purpose
        c, rsp = self.ok(" LD #1\n HDR #1\n" + KEYED + " WIPE #3\n LD #9\n ST l0\n PUSH l0")
        self.assertEqual(rsp[1], 9)
        c, rsp = self.ok(" LD #1\n HDR #1\n" + KEYED + " LD l0\n LD #4\n PUSH H")              # H reloaded: clean
        self.assertEqual(rsp[1], 4)
        c, rsp = self.ok(KEYED + " LD #0\n CMP l0\n CTL CLRZ\n LD #0\n HDR #0\nx: BR Z x")     # flag cleared: clean
        self.assertEqual(rsp, [host.rhdr(TEST_OP, 0)])

    def test_release_is_the_only_way_out_and_needs_a_permutation(self):
        c, rsp = self.ok(" LD #2\n HDR #2\n" + KEYED + " REL l0\n REL l16")
        self.assertEqual(len(rsp), 3)
        self.assertEqual(c.log[-1]["key_words_emitted"], [])
        self.fault(" LD #1\n HDR #1\n" + KEYED + " REL t0", "not a rate lane")
        self.fault(KEYED + " REL l0", "PUSH before the response header")
        self.fault(" LD #1\n HDR #1\n" + KEYED + " REL l0\n REL l1", "beyond the declared response length")

    def test_tag_compare_verdict_is_declassified(self):
        for word, want in ((0, True), (1, False)):
            c, rsp = self.ok(" KMOV k_host0 > l0\n LD #1\n XOR l1 > l1\n KEC 12\n DIN\n CMPT l0\n BR Z t_bad\n LD #0\n HDR #0\n END\nt_bad: FAIL #5",
                             payload=(self._mac(word),))
            self.assertEqual(rsp == [host.rhdr(TEST_OP, 0)], want)
        self.fault(KEYED + " LD l1\n CMPT l0", "CMPT with key-derived data in H")
        self.fault(KEYED + " LD #0\n CMPT t0", "CMPT operand is not a rate lane")
        self.fault(KEYED + " LD #0\n CMPT l17", "capacity lane")

    @staticmethod
    def _mac(flip):
        st = [0] * 25
        st[0] = host.words_of(K)[0]
        st[1] = 1
        return host.q.keccak_p(st, 12)[0] ^ flip


class FramPath(Base):
    """R11."""

    def test_fram_decodes_only_in_the_record_range(self):
        for ins in ("FRAM RSTART", "FRAM WSTART", "FRAM RWORD", "FRAM WWORD A0", "FRAM DONE"):
            self.fault(" LD #0\n " + ins, "FRAM instruction outside the record range")
            self.fault(" LD #0\n " + ins, "FRAM instruction outside the record range", where="key")

    def test_only_the_record_rows_can_be_written(self):
        pre = " LD #0\n FRAM WSTART\n"
        for row in ("t0", "t8", "t10", "l2", "l16", "pin0", "st0"):
            self.fault(pre + " FRAM WWORD %s" % row, "FRAM WWORD of row", where="rec")
        self.fault(" SETX #1\n" + pre + " FRAM WWORD A0+X", "FRAM WWORD of row", where="rec")
        c, rsp = self.ok(" LD #7\n ST A0\n LD #8\n ST l0\n LD #9\n ST l1\n LD #1\n FRAM WSTART\n FRAM WWORD A0\n FRAM WWORD l0\n FRAM WWORD l1\n FRAM DONE\n LD #0\n HDR #0",
                         where="rec", keys=False)
        self.assertEqual([int.from_bytes(c.fram[32 + 8 * i:40 + 8 * i], "little") for i in range(3)], [7, 8, 9])
        self.assertEqual(bytes(c.fram[:32]), bytes(32))

    def test_a_transaction_is_three_words_one_way(self):
        w = " LD #0\n FRAM WSTART\n"
        r = " LD #0\n FRAM RSTART\n"
        self.fault(" FRAM RWORD", "outside a matching three-word transaction", where="rec")
        self.fault(" FRAM WWORD A0", "outside a matching three-word transaction", where="rec")
        self.fault(" FRAM DONE", "FRAM DONE without a transaction", where="rec")
        self.fault(w + " FRAM RWORD", "outside a matching three-word transaction", where="rec")
        self.fault(r + " FRAM WWORD A0", "outside a matching three-word transaction", where="rec")
        self.fault(w + " FRAM WWORD A0\n" * 4, "outside a matching three-word transaction", where="rec")
        self.fault(r + " FRAM RWORD\n" * 4, "outside a matching three-word transaction", where="rec")
        self.fault(w + " FRAM WSTART", "already open", where="rec")

    def test_the_record_tag_is_the_one_key_derived_value_that_may_be_written(self):
        c, rsp = self.ok(" LD #3\n ST A0\n KMOV k_dev0 > l0\n KEC 12\n LD #0\n FRAM WSTART\n FRAM WWORD A0\n FRAM WWORD l0\n FRAM WWORD l1\n FRAM DONE\n LD #0\n HDR #0",
                         where="rec", keys=False)
        self.assertEqual(int.from_bytes(c.fram[0:8], "little"), 3)
        self.assertNotIn(bytes(c.fram[8:16]), (bytes(8), common.DEV[:8]))


class ResponseAndEnd(Base):
    """R9, R10."""

    def test_response_length_is_bounded(self):
        self.fault(" LD #7\n PUSH H", "PUSH before the response header")
        self.fault(" LD #1\n HDR #4\n PUSH H\n PUSH H", "beyond the declared response length")
        self.fault(" LD #5\n HDR #4", "longer than the routine's cap")
        self.fault(" LD #1\n HDR #4\n HDR #4", "second response header")
        self.fault(" LD #1\n HDR #4\n FAIL #3", "FAIL after the response header")
        c, rsp = self.ok(" LD #3\n HDR #4\n LD #9\n PUSH H")              # short routine: padded, link stays in step
        self.assertEqual(rsp, [host.rhdr(TEST_OP, 24), 9, 0, 0])

    def test_a_command_must_answer(self):
        self.fault(" NOP", "command ended without a response header")
        self.fault(" LD #1\n ST t0", "command ended without a response header")

    def test_end_wipes_and_drains_in_hardware(self):
        """The fixture leaves values in lanes, scratch and unread payload; the end action clears them all."""
        body = " LD #5\n ST l3\n ST l20\n ST t7\n KEC 24\n DIN\n LD #0\n HDR #0"
        c, rsp = self.ok(body, payload=(1, 2, 3), keys=False)
        self.assertTrue(common.working_rows_clear(c))
        self.assertEqual(c.m.framer.remaining, 0)
        self.assertEqual(c.transact([host.hdr(host.OP_PING)])[1], int.from_bytes(b"QSAGNI18", "little"))
        c, rsp = self.ok(" DIN\n FAIL #9", payload=(1, 2, 3), keys=False)          # the FAIL path ends the same way
        self.assertEqual(c.m.framer.remaining, 0)
        self.assertTrue(common.working_rows_clear(c))

    def test_undrained_payload_would_desynchronise_the_link(self):
        """What the drain protects against, shown on the framer: a new request while words are pending."""
        c = common.new_chip("S")
        c.m.framer.begin([host.hdr(0x7E, 0, 16), 1, 2])
        with self.assertRaises(LinkError):
            c.m.framer.begin([host.hdr(host.OP_PING)])

    def test_idle_is_reached_only_by_the_end_action(self):
        self.fault(" BR idle", "transfer to the idle address")
        self.fault(" CALL idle", "transfer to the idle address")
        self.fault(" LD #0\n HDR #0\n DISP", "DISP away from address 0")
        self.fault(" CALL t_a\nt_a: CALL t_b\nt_b: CALL t_c\nt_c: NOP", "return stack overflow")
        self.fault(" RET", "return with an empty stack")
        self.fault(" ILL", "illegal instruction")
        self.fault(" BR @60", "illegal instruction")                             # a trap word of the key range

    def test_falling_off_the_rom_is_a_fault(self):
        self.fault(" LD #0\n HDR #0\n NOP", "fell off the end of the ROM", end=False)

    def test_reading_past_the_payload_is_a_fault(self):
        self.fault(" DIN", "DIN past the end of the payload")
        self.fault(" DIN\n DIN", "DIN past the end of the payload", payload=(1,))

    def test_runaway_microprogram_is_a_fault(self):
        saved = Machine.MAX_STEPS
        Machine.MAX_STEPS = 2000
        try:
            self.fault("x: BR x", "runaway microprogram")
        finally:
            Machine.MAX_STEPS = saved

    def test_field_unit_absent_in_configuration_S(self):
        self.fault(" FLD PERM", "configuration S")
        c, rsp = self.ok(" LD #0\n HDR #0\n FLD PERM", config="L", keys=False)
        self.assertEqual(rsp, [host.rhdr(TEST_OP, 0)])
        self.fault(" KMOV k_seed0 > l0\n FLD PERM", "Poseidon2 in a keyed command", config="L")

    def test_fault_clears_secrets_and_raises_the_pin(self):
        c = common.new_chip("S", rom=rom_with(" LD k_seed0"))
        self.assertEqual(host.provision(c, c.owner, K, SEED, PRF), [host.rhdr(host.OP_KEYLOAD, 0)])
        self.assertTrue(set(host.words_of(SEED)) <= c.m.rf.key_values())
        with self.assertRaises(ControlFault):
            c.transact([host.hdr(TEST_OP)])
        self.assertFalse(set(host.words_of(K + SEED + PRF)) & c.m.rf.key_values())
        self.assertFalse(any(c.m.rf[r] for r in range(isa.KEY0)))
        self.assertEqual(c.pins["FAULT"], 1)
        self.assertEqual(c.transact(host.prf_msg(b"abc")), [host.rhdr(host.OP_PRFMSG, 0, False, host.E_NOKEY)])


if __name__ == "__main__":
    unittest.main()
