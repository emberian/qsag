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
from fixtures import KDEV, TEST_OP, rom_with, run
from framing import LinkError
from machine import ControlFault, Machine

KEYED = " KMOV k_dev0 > l0\n KEC 12\n"                # a completed keyed permutation: lanes are key-derived


class Base(unittest.TestCase):
    def fault(self, body, needle, **kw):
        with self.assertRaises(ControlFault) as cm:
            run(body, **kw)
        self.assertIn(needle, str(cm.exception))

    def ok(self, body, **kw):
        return run(body, **kw)


class StaticManifest(unittest.TestCase):
    def findings(self, old, new, config="S", count=1):
        src = chip.read_sources(config, common.SLH)
        self.assertEqual(sum(t.count(old) for _, t in src), count, old)
        return romcheck.check(uasm.assemble([(n, t.replace(old, new)) for n, t in src]), romcheck.load_manifest())

    def test_shipped_roms_pass(self):
        for cfg in "SL":
            self.assertEqual(romcheck.check(chip.build_rom(cfg, common.SLH), romcheck.load_manifest()), [])

    def test_manifest_covers_both_configurations(self):
        places = {p for cfg in "SL" for p, _ in chip.build_rom(cfg, common.SLH).pushes() + chip.build_rom(cfg, common.SLH).releases()}
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
        self.assertTrue(any("fram:r0" in x and "rec_store+13" in x for x in f), f)


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
        self.expect("transfer to %d" % (isa.KEY_HI - 1), " BR @%d" % (isa.KEY_HI - 1))     # a trap word of the key range

    def test_key_instructions_outside_the_key_range(self):
        for ins in (" KEYWR > k_dev0", " CTL LC #5", " CTL AUTH", " CTL PUFE", " CTL PUFR", " CTL SYNW #0", " PMOV #0 > l0"):
            self.expect("key instruction outside the key range", ins)
        self.assertEqual([x for x in self.findings_for(" CTL AUTH", where="key") if "key instruction" in x], [])

    def test_fram_instructions_outside_the_record_range(self):
        for ins in (" FRAM RSTART", " FRAM WWORD st0", " FRAM DONE"):
            self.expect("FRAM instruction outside the record range", ins)
        self.assertEqual([x for x in self.findings_for(" FRAM DONE", where="rec") if "record range" in x], [])

    def test_fram_write_source(self):
        self.expect("FRAM WWORD of row", " FRAM WWORD t0", where="rec")
        self.expect("FRAM WWORD of row", " FRAM WWORD l2", where="rec")
        self.expect("FRAM WWORD of row", " FRAM WWORD st0+X", where="rec")
        self.assertEqual([x for x in self.findings_for(" FRAM WWORD st9", where="rec") if "FRAM WWORD" in x], [])

    def test_state_rows_are_written_only_in_the_record_range(self):
        for ins in (" ST st0", " LD t0 > st9", " DIN > st4", " LDF LC > st2", " ST st0+X"):
            self.expect("outside the record range", ins)
        self.expect("outside the record range", " ST st0", where="key")
        self.assertEqual([x for x in self.findings_for(" ST st0", where="rec") if "record range" in x], [])

    def test_rows_named_directly(self):
        self.expect("read of key row", " LD k_dev0")
        self.expect("write of out row", " ST out0")
        self.expect("read of out row", " LD #1\n HDR #1\n PUSH out0")
        self.expect("write of kwork row", " ST r25")
        self.expect("write of key row", " FRAM RWORD > k_dev0", where="rec")

    def test_kmov_operands(self):
        self.expect("KMOV operands", " KMOV t0 > l0")
        self.expect("KMOV operands", " KMOV k_dev0 > l17")
        self.expect("KMOV operands", " KMOV k_dev0 > l0+X")
        self.expect("PMOV operands", " PMOV #4 > l0", where="key")
        self.expect("PMOV operands", " PMOV #0 > l17", where="key")
        self.expect("PMOV operands", " PMOV #0 > l0+X", where="key")

    def test_release_operands(self):
        self.expect("not a rate lane", " REL l17")
        self.expect("not a rate lane", " CMPT t0")

    def test_disp_only_at_address_0(self):
        self.expect("DISP must be at address 0", " DISP")
        rom = chip.build_rom("S", common.SLH)
        bad = uasm.assemble(chip.read_sources("S", common.SLH))
        bad.words[0] = isa.encode(isa.OP["NOP"])
        self.assertTrue(any("DISP must be at address 0" in x for x in romcheck.check(bad, romcheck.load_manifest())))
        self.assertEqual(rom.words[0], isa.encode(isa.OP["DISP"]))

    def test_trap_words(self):
        self.expect("illegal instruction", " ILL")
        bad = uasm.assemble(chip.read_sources("S", common.SLH))
        pad = min(bad.padding)
        bad.words[pad] = isa.encode(isa.OP["NOP"])
        self.assertTrue(any("padding is not a trap word" in x for x in romcheck.check(bad, romcheck.load_manifest())))

    def test_canonical_encoding(self):
        bad = uasm.assemble(chip.read_sources("S", common.SLH))
        a = bad.labels["ping"]
        bad.words[a] |= 1 << 9                                             # a stray bit in an unused field of LDF
        self.assertTrue(any("non-canonical encoding" in x for x in romcheck.check(bad, romcheck.load_manifest())))
        bad = uasm.assemble(chip.read_sources("S", common.SLH))
        bad.words[a] = isa.encode(isa.OP["UN"], a=100)                     # a function code that does not exist
        self.assertTrue(any("does not disassemble" in x for x in romcheck.check(bad, romcheck.load_manifest())))

    def test_code_must_not_run_off_its_end(self):
        self.expect("runs past the end of the code", " NOP", end=False)                    # last word of the image
        self.expect("runs past the end of the code", " NOP", where="key", end=False)       # into the trap words
        self.assertEqual([x for x in self.findings_for(" NOP") if "runs past" in x], [])

    def test_entries_match_the_layout(self):
        bad = uasm.assemble(chip.read_sources("S", common.SLH))
        bad.entries[host.OP_CTH] = (bad.entries[host.OP_CTH][0], 0)
        self.assertTrue(any("decodes in no lifecycle state" in x for x in romcheck.check(bad, romcheck.load_manifest())))
        bad = uasm.assemble(chip.read_sources("S", common.SLH))
        bad.entries[0x55] = (min(bad.padding), isa.LC_ANY)
        self.assertTrue(any("outside the ordinary code" in x for x in romcheck.check(bad, romcheck.load_manifest())))
        bad = uasm.assemble(chip.read_sources("S", common.SLH))
        bad.entries[0x55] = (bad.labels["lc_ready"], isa.LC_ANY)        # a command must not start inside the key range
        self.assertTrue(any("outside the ordinary code" in x for x in romcheck.check(bad, romcheck.load_manifest())))

    def test_image_has_an_end(self):
        rom = uasm.assemble([("t", "idle: DISP\nx: NOP\n BR x\n")])
        self.assertTrue(any("no END or FAIL" in x for x in romcheck.check(rom, {})))

    def test_layout_is_hardwired_not_read_from_the_image(self):
        """Moving the key-range code out of its range does not move the range."""
        src = [(n, t.replace(".org KEY_END", ".org 40") if n == "rec.uc" else t) for n, t in chip.read_sources("S", common.SLH)]
        with self.assertRaises(uasm.AsmError):
            uasm.assemble(src)                                             # the key-range code no longer fits
        self.assertEqual((isa.KEY_LO, isa.REC_LO, isa.ROM_BASE), (1, isa.KEY_HI + 1, isa.REC_HI + 1))
        rom = chip.build_rom("S", common.SLH)
        self.assertEqual((rom.labels["lc_blank"], rom.labels["nonce_put"], rom.labels["e_opcode"]), (isa.KEY_LO, isa.REC_LO, isa.ROM_BASE))
        self.assertFalse(hasattr(rom, "keyrange") or hasattr(rom, "epilogue"))


class KeyRows(Base):
    def test_baseline_fixture_runs(self):
        c, rsp = self.ok(" LD #2\n HDR #2\n LD #7\n PUSH H\n ST t0\n PUSH t0")
        self.assertEqual(rsp, [host.rhdr(TEST_OP, 16), 7, 7])
        self.assertTrue(common.working_rows_clear(c))

    def test_key_rows_are_not_readable(self):
        pre = " LD #1\n HDR #1\n SETX #%d\n" % (isa.KEY0 + 2 - isa.SCRATCH0)
        for ins in ("LD k_dev0", "XOR k_dev2", "CMP k_dev3", "LD k_dev1", "PUSH k_dev0", "LD t0+X", "FADD k_dev1"):
            self.fault(pre + " " + ins, "key row", config="L")
        self.fault(" LD #1\n HDR #1\n REL k_dev0", "not a rate lane")
        self.fault(" CMPT k_dev0", "key row")
        self.fault(" FRAM WSTART\n FRAM WWORD k_dev0", "FRAM WWORD of row", where="rec")

    def test_key_rows_are_written_only_in_the_key_range_under_the_verdict_latch(self):
        self.fault(" LD #1\n ST k_dev0", "write of key row")
        self.fault(" LD #1\n KEYWR > k_dev0", "KEYWR outside the key range")
        self.fault(" LD #1\n KEYWR > k_dev0", "KEYWR outside the key range", where="rec")
        self.fault(" LD #1\n KEYWR > k_dev0", "KEYWR without the verdict latch", where="key")
        # the latch is set only by CTL AUTH, in the key range, from a clear compare flag that is not key-derived
        self.fault(" CTL AUTH", "key-range CTL outside the key range")
        self.fault(" LD #1\n CMP #0\n CTL AUTH\n LD #1\n KEYWR > k_dev0", "KEYWR without the verdict latch", where="key")
        self.fault(KEYED + " LD #0\n CMP l0\n CTL AUTH", "verdict latch from a key-derived compare result", where="key")
        c, rsp = self.ok(" CTL AUTH\n LD #5\n KEYWR > k_dev2\n LD #0\n HDR #0", where="key", keys=False)
        self.assertEqual(c.m.rf[isa.KEY0 + 2], 5)
        for tail, needle in ((" LD #5\n KEYWR > t0", "KEYWR destination is not a key row"),
                             (" LD #5\n KEYWR > l3", "KEYWR destination is not a key row"),
                             (" LD #5\n KEYWR > st0", "KEYWR destination is not a key row")):
            self.fault(" CTL AUTH\n" + tail, needle, where="key")
        # the latch does not outlive the command
        c, rsp = self.ok(" CTL AUTH\n LD #0\n HDR #0", where="key", keys=False)
        self.assertFalse(c.m.auth_ok)

    def test_key_rows_can_be_cleared_anywhere(self):
        c, rsp = self.ok(" CTL ZKEY\n LD #0\n HDR #0")
        self.assertEqual(c.m.rf.key_values(), set())

    def test_out_and_work_rows_are_not_addressable(self):
        self.fault(" LD #1\n ST out0", "write of out row")
        self.fault(" LD out1", "read of out row")
        self.fault(" LD #1\n HDR #1\n PUSH out0", "PUSH of out row")
        self.fault(" KEC 24\n LD r25", "read of kwork row")
        self.fault(" LD #1\n ST r31", "write of kwork row")
        self.fault(" LD r%d" % isa.ROWS_S, "read of none row")            # one past the last row of configuration S

    def test_key_in_lanes_cannot_be_moved_or_emitted(self):
        self.fault(" LD #1\n HDR #1\n KMOV k_dev0 > l0\n PUSH l0", "while a key is in the lanes")
        self.fault(" LD #1\n HDR #1\n KMOV k_dev0 > l0\n REL l0", "while a key is in the lanes")
        self.fault(" KMOV k_dev0 > l0\n LD l0", "while a key is in the lanes")
        self.fault(" KMOV k_dev0 > l0\n LD #0\n CMP l0", "while a key is in the lanes")
        self.fault(" KMOV k_dev0 > l0\n LD #0\n CMPT l0", "while a key is in the lanes")
        self.fault(" KMOV k_dev0 > l0\n LD #0\n XOR l0 > t0", "while a key is in the lanes")
        self.fault(" KMOV k_dev0 > l0\n LD #0\n XOR l0 > l1", "while a key is in the lanes")
        for op in ("ADD", "SUB", "AND", "OR", "LD"):                      # only absorption may touch the lane
            self.fault(" KMOV k_dev0 > l0\n LD #0\n %s l0 > l0" % op, "while a key is in the lanes")
        self.fault(" KMOV k_dev0 > l0\n LD #0\n FADD l0 > l0", "while a key is in the lanes", config="L")
        self.fault(" KMOV k_dev0 > l0\n WIPE #2\n LD l0", "while a key is in the lanes")     # a partial wipe does not clear it
        self.fault(" KMOV k_dev0 > l0\n FRAM WSTART\n FRAM WWORD l0", "while a key is in the lanes", where="rec")
        self.fault(" KMOV k_dev0 > l17", "not a rate lane")
        self.fault(" KMOV t0 > l0", "not a key row")

    def test_hold_register_is_cleared_after_touching_a_key(self):
        c, rsp = self.ok(" LD #2\n HDR #2\n KMOV k_dev0 > l0\n ST t0\n LD #0\n XOR l0 > l0\n ST t1\n KEC 24\n PUSH t0\n PUSH t1")
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
        self.fault(KEYED + " LD l0\n ST t0", "store of key-derived data")
        self.fault(KEYED + " LD l0\n ST st1", "store of key-derived data", where="rec")
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
        self.fault(KEYED + " LD l0\n UN SHL1C\n LD #0\nx: BR CY x", "branch on a key-derived carry")
        self.fault(KEYED + " LD #0\n CMP l0\n CTL VOK", "verdict pin from a key-derived compare result")
        self.fault(KEYED + " LD #0\n CMP l0\n LD #0\n HDR #0 okz", "response flag from a key-derived compare result")

    def test_key_derived_data_cannot_reach_the_fram_or_the_key_attribute(self):
        self.fault(KEYED + " LD l0\n FRAM WSTART", "FRAM record index from key-derived data", where="rec")
        self.fault(KEYED + " LD l0\n FRAM RSTART", "FRAM record index from key-derived data", where="rec")
        self.fault(KEYED + " LD l0\n CTL SYNW #0", "syndrome from key-derived data", where="key")
        self.fault(KEYED + " LD l0\n CTL TSEL", "TRNG pair from key-derived data")
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
            c, rsp = self.ok(" KMOV k_dev1 > l0\n LD #1\n XOR l1 > l1\n KEC 12\n DIN\n CMPT l0\n BR Z t_bad\n LD #0\n HDR #0\n END\nt_bad: FAIL #5",
                             payload=(self._mac(word),))
            self.assertEqual(rsp == [host.rhdr(TEST_OP, 0)], want)
        self.fault(KEYED + " LD l1\n CMPT l0", "CMPT with key-derived data in H")
        self.fault(KEYED + " LD #0\n CMPT t0", "CMPT operand is not a rate lane")
        self.fault(KEYED + " LD #0\n CMPT l17", "capacity lane")

    @staticmethod
    def _mac(flip):
        st = [0] * 25
        st[0] = KDEV[1]
        st[1] = 1
        return host.q.keccak_p(st, 12)[0] ^ flip


class FramPath(Base):
    """R11."""

    def test_fram_decodes_only_in_the_record_range(self):
        for ins in ("FRAM RSTART", "FRAM WSTART", "FRAM RWORD", "FRAM WWORD st0", "FRAM DONE"):
            self.fault(" LD #0\n " + ins, "FRAM instruction outside the record range")
            self.fault(" LD #0\n " + ins, "FRAM instruction outside the record range", where="key")

    def test_only_state_rows_and_the_tag_lanes_can_be_written(self):
        pre = " LD #0\n FRAM WSTART\n"
        for row in ("t0", "t9", "t23", "l2", "l16", "k_dev0", "out0"):
            self.fault(pre + " FRAM WWORD %s" % row, "FRAM WWORD of row", where="rec")
        self.fault(" SETX #1\n" + pre + " FRAM WWORD st0+X", "FRAM WWORD of row", where="rec")
        c, rsp = self.ok(" LD #7\n ST st0\n LD #8\n ST l0\n LD #9\n ST l1\n LD #2\n FRAM WSTART\n FRAM WWORD st0\n FRAM WWORD l0\n FRAM WWORD l1\n FRAM DONE\n LD #0\n HDR #0",
                         where="rec", keys=False)
        self.assertEqual([int.from_bytes(c.fram[256 + 8 * i:264 + 8 * i], "little") for i in range(3)], [7, 8, 9])
        self.assertEqual(bytes(c.fram[:256]), bytes(256))

    def test_a_transaction_is_sixteen_words_one_way_inside_three_records(self):
        w = " LD #0\n FRAM WSTART\n"
        r = " LD #0\n FRAM RSTART\n"
        self.fault(" FRAM RWORD", "outside a matching transaction", where="rec")
        self.fault(" FRAM WWORD st0", "outside a matching transaction", where="rec")
        self.fault(" FRAM DONE", "FRAM DONE without a transaction", where="rec")
        self.fault(w + " FRAM RWORD", "outside a matching transaction", where="rec")
        self.fault(r + " FRAM WWORD st0", "outside a matching transaction", where="rec")
        self.fault(w + " SETC 0 #17\nq: FRAM WWORD st0\n DBNZ 0 q", "outside a matching transaction", where="rec")
        self.fault(r + " SETC 0 #17\nq: FRAM RWORD\n DBNZ 0 q", "outside a matching transaction", where="rec")
        self.fault(w + " FRAM WSTART", "already open", where="rec")
        self.fault(" LD #3\n FRAM RSTART", "record index out of range", where="rec")
        c, rsp = self.ok(r + " SETC 0 #16\nq: FRAM RWORD\n DBNZ 0 q\n FRAM DONE\n LD #0\n HDR #0", where="rec", keys=False)

    def test_the_record_tag_is_the_one_key_derived_value_that_may_be_written(self):
        c, rsp = self.ok(" LD #3\n ST st0\n KMOV k_dev0 > l0\n KEC 12\n LD #1\n FRAM WSTART\n FRAM WWORD st0\n FRAM WWORD l0\n FRAM WWORD l1\n FRAM DONE\n LD #0\n HDR #0",
                         where="rec")
        self.assertEqual(int.from_bytes(c.fram[128:136], "little"), 3)
        self.assertNotIn(bytes(c.fram[136:144]), (bytes(8), KDEV[0].to_bytes(8, "little")))


class StateAndLifecycle(Base):
    """R13, R14, R15."""

    def test_state_rows_are_written_only_in_the_record_range(self):
        for ins in (" LD #1\n ST st0", " DIN > st9", " LD #1\n SETX #3\n ST st0+X", " LDF LC > st5"):
            self.fault(ins, "write of a state row outside the record range", payload=(1,))
            self.fault(ins, "write of a state row outside the record range", payload=(1,), where="key")
        self.fault(" SETX #%d\n LD #1\n ST t0+X" % (isa.STATE0 - isa.SCRATCH0), "write of a state row outside the record range")
        c, rsp = self.ok(" LD #6\n ST st3\n LD #0\n HDR #0", where="rec")
        self.assertEqual(c.m.rf[isa.STATE0 + 3], 6)
        c.transact([host.hdr(host.OP_PING)])
        self.assertEqual(c.m.rf[isa.STATE0 + 3], 6)                        # state rows outlive the command

    def test_state_rows_are_public(self):
        c, rsp = self.ok(" LD #1\n HDR #1\n PUSH st0", keys=False)
        self.assertEqual(len(rsp), 2)

    def test_lifecycle_register_is_written_only_in_the_key_range(self):
        for st in range(1, 6):
            self.fault(" CTL LC #%d" % st, "key-range CTL outside the key range", keys=False)
            self.fault(" CTL LC #%d" % st, "key-range CTL outside the key range", keys=False, where="rec")
        c, rsp = self.ok(" CTL LC #2\n LD #0\n HDR #0", where="key", keys=False)
        self.assertEqual(c.m.lc, isa.LC_ORPHAN)
        self.fault(" CTL LC #0", "lifecycle state out of range", where="key", keys=False)
        self.fault(" CTL LC #6", "lifecycle state out of range", where="key", keys=False)

    def test_ready_needs_the_verdict_latch_and_a_state_that_can_boot(self):
        self.fault(" CTL LC #4", "READY without the verdict latch", where="key", keys=False)
        self.fault(" LD #1\n CMP #0\n CTL AUTH\n CTL LC #4", "READY without the verdict latch", where="key", keys=False)
        c, rsp = self.ok(" CTL AUTH\n CTL LC #4\n LD #0\n HDR #0", where="key", keys=False)
        self.assertEqual(c.m.lc, isa.LC_READY)
        c, rsp = self.ok(" CTL LC #3\n CTL AUTH\n CTL LC #4\n LD #0\n HDR #0", where="key", keys=False)
        self.assertEqual(c.m.lc, isa.LC_READY)
        for st in (isa.LC_BLANK, isa.LC_ORPHAN):
            self.fault(" CTL LC #%d\n CTL AUTH\n CTL LC #4" % st, "READY from a state that cannot boot", where="key", keys=False)

    def test_nothing_leaves_locked(self):
        for st in range(1, 6):
            self.fault(" CTL LC #5\n CTL AUTH\n CTL LC #%d" % st, "lifecycle change out of LOCKED", where="key", keys=False)

    def test_puf_response_leaves_only_as_a_key(self):
        pre = " CTL PUFE\n"
        self.fault(" PMOV #0 > l0", "PMOV outside the key range")
        self.fault(" CTL PUFE", "key-range CTL outside the key range")
        self.fault(" CTL PUFR", "key-range CTL outside the key range")
        self.fault(" LD #1\n CTL SYNW #0", "key-range CTL outside the key range")
        self.fault(" PMOV #0 > l0", "PMOV without a PUF response", where="key")            # nothing measured in this command
        self.fault(pre + " PMOV #0 > l17", "not a rate lane", where="key")
        self.fault(pre + " PMOV #0 > t0", "not a rate lane", where="key")
        self.fault(pre + " PMOV #0 > l0\n LD l0", "while a key is in the lanes", where="key")
        self.fault(pre + " LD #1\n HDR #1\n PMOV #0 > l0\n PUSH l0", "while a key is in the lanes", where="key")
        self.fault(pre + " LD #1\n HDR #1\n PMOV #0 > l0\n KEC 12\n PUSH l0", "PUSH of key-derived data", where="key")
        self.fault(pre + " PMOV #0 > l0\n KEC 12\n LD l0\n ST t0", "store of key-derived data", where="key")
        c, rsp = self.ok(pre + " PMOV #3 > l0\n ST t0\n KEC 12\n LD #1\n HDR #1\n PUSH t0", where="key")
        self.assertEqual(rsp[1], 0)                                        # H is cleared, as after KMOV

    def test_puf_response_register_is_cleared_at_command_end(self):
        c, rsp = self.ok(" CTL PUFE\n LD #0\n HDR #0", where="key")
        self.assertIsNone(c.m.puf.rsp)
        c = common.new_chip(rom=rom_with(" PMOV #0 > l0", "key"))
        c.transact(host.cmd(host.OP_BOOT))
        c.transact(host.cmd(host.OP_ENROL))                                # measures; the register is cleared at its end
        with self.assertRaises(ControlFault) as cm:
            c.transact([host.hdr(TEST_OP)])
        self.assertIn("PMOV without a PUF response", str(cm.exception))

    def test_syndromes_are_public(self):
        c, rsp = self.ok(" CTL PUFE\n LD #2\n HDR #2\n LDF SYN0\n PUSH H\n LDF SYN1\n PUSH H", where="key")
        self.assertEqual(rsp[1:], c.m.puf.syn)
        self.assertNotEqual(rsp[1:], [0, 0])


def gf_mul(a, b):
    """Product in GF(2^64) modulo x^64 + x^4 + x^3 + x + 1, bit by bit."""
    r = 0
    for i in range(64):
        if (b >> i) & 1:
            r ^= a << i
    for i in range(127, 63, -1):
        if (r >> i) & 1:
            r ^= (0x1B | (1 << 64)) << (i - 64)
    return r


class Fingerprint(Base):
    """The `stated` routine of slh.uc on its own (ARCHITECTURE.md 4.3): hash chain, points, the two folds."""
    BODY = (" DIN > FD0\n DIN > FD1\n LD #3\n CALL stated\n LD #8\n HDR #8 okz\n PUSH FR0\n PUSH FR1\n PUSH FD0\n PUSH FD1\n"
            " PUSH FA0\n PUSH FA1\n PUSH l0\n PUSH l1")
    V = [0x0123456789ABCDEF, 0xFEDCBA9876543210, 0x8000000000000001, 0x1B, 0xFFFFFFFFFFFFFFFF, 0x5555AAAA3333CCCC]

    @staticmethod
    def chain(words):
        d = [0, 0]
        for i in range(0, len(words), 2):
            d = host.ts(d + words[i:i + 2], host.D_CH)
        return d

    @staticmethod
    def fold(words, points):
        acc = [0, 0]
        for w in words:
            acc = [gf_mul(acc[j] ^ w, points[j]) for j in (0, 1)]
        return acc

    def run_stated(self, d, a, b):
        c, rsp = self.ok(self.BODY, payload=tuple(d + a + b), keys=False)
        return bool(rsp[0] & 0x10000), rsp[1:]

    def test_equal_passes_and_the_values_the_chip_holds(self):
        import hashlib
        d = self.chain(self.V)
        ok, out = self.run_stated(d, self.V, self.V)
        self.assertTrue(ok)
        points = host.ts(d, host.D_PT)
        self.assertEqual(out[0:2], points)                      # points: a hash of the computed values' chain
        self.assertNotEqual(points[0], points[1])
        self.assertEqual(out[2:4], self.fold(self.V, points))   # pass 2a
        self.assertEqual(out[4:6], out[2:4])                    # pass 2b
        t = hashlib.shake_256(bytes(48) + host.bytes_of(self.V)).digest(16)     # T over PK.seed, ADRS (all zero here), values
        self.assertEqual(host.bytes_of(out[6:8]), t)

    def test_what_is_refused(self):
        d = self.chain(self.V)
        swapped = [self.V[1], self.V[0]] + self.V[2:]           # same words, same XOR, another order
        moved = [self.V[2], self.V[1], self.V[0]] + self.V[3:]
        other = [w ^ 1 for w in self.V]
        self.assertFalse(self.run_stated(d, self.V, swapped)[0])                # pass 2b differs
        self.assertFalse(self.run_stated(d, self.V, moved)[0])
        self.assertFalse(self.run_stated(d, self.V, other)[0])
        self.assertFalse(self.run_stated(d, other, other)[0])                   # both differ from the computed values alike
        self.assertFalse(self.run_stated(d, swapped, swapped)[0])
        self.assertFalse(self.run_stated([d[0] ^ 1, d[1]], self.V, self.V)[0])
        self.assertTrue(self.run_stated(self.chain(other), other, other)[0])


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
        self.fault(" CALL t_a\nt_a: CALL t_b\nt_b: CALL t_c\nt_c: CALL t_d\nt_d: CALL t_e\nt_e: NOP", "return stack overflow")
        c, rsp = self.ok(" CALL t_a\n LD #0\n HDR #0\n END\nt_a: CALL t_b\n RET\nt_b: CALL t_c\n RET\nt_c: CALL t_d\n RET\nt_d: RET", keys=False)
        self.assertEqual(rsp, [host.rhdr(TEST_OP, 0)])                     # four entries
        self.fault(" RET", "return with an empty stack")
        self.fault(" ILL", "illegal instruction")
        self.fault(" BR @%d" % (isa.KEY_HI - 1), "illegal instruction")          # a trap word of the key range

    def test_undefined_codes_are_faults(self):
        def raw(word, where="rom"):
            rom = rom_with(" NOP", where)
            rom.words[rom.labels["t_body" if where != "rom" else "t_entry"]] = word
            c = common.new_chip(rom=rom)
            with self.assertRaises(ControlFault) as cm:
                c.transact([host.hdr(TEST_OP)])
            return str(cm.exception)
        e = isa.encode
        for word in (e(isa.OP["UN"], a=len(isa.UN)), e(isa.OP["LDF"], a=len(isa.LDF)), e(isa.OP["CTL"], a=len(isa.CTL)),
                     e(isa.OP["BR"], a=len(isa.COND), b=20)):
            self.assertIn("undefined function code", raw(word))
        self.assertIn("undefined function code", raw(e(isa.OP["FRAM"], a=len(isa.FRAM)), "rec"))
        self.assertIn("undefined constant", raw(e(isa.OP["LDC"], a=100)))

    def test_a_command_cannot_start_below_the_ordinary_code(self):
        for target in ("idle", "lc_ready", "rec_store"):
            rom = rom_with(" NOP")
            rom.entries[0x55] = (rom.labels[target], isa.LC_ANY)
            c = common.new_chip(rom=rom)
            with self.assertRaises(ControlFault) as cm:
                c.transact([host.hdr(0x55)])
            self.assertIn("dispatch entry below the ordinary code", str(cm.exception))

    def test_the_hold_register_does_not_survive_a_permutation_or_a_row_push(self):
        """One hold register: the Keccak unit writes through it, and a pushed row passes through it."""
        c, rsp = self.ok(" LD #5\n HDR #5\n LD #7\n KEC 12\n PUSH H\n LD #7\n ST t0\n LD #9\n PUSH t0\n PUSH H\n LD #9\n REL l0\n PUSH H", keys=False)
        self.assertEqual([rsp[1], rsp[2], rsp[3], rsp[5]], [0, 7, 0, 0])

    def test_rows_written_in_the_previous_clock_cost_a_stall(self):
        def clocks(body, **kw):
            c, _ = self.ok(body + "\n LD #0\n HDR #0", **kw)
            return c.log[-1]["cycles"], c.log[-1]["stalls"]
        base = clocks(" LD #1\n ST t0\n LD #2\n LD t0", keys=False)
        self.assertEqual(clocks(" LD #1\n LD #2\n ST t0\n LD t0", keys=False), (base[0] + 1, base[1] + 1))
        k = clocks(" KEC 12\n LD l23", keys=False)
        self.assertEqual(clocks(" KEC 12\n LD l24", keys=False), (k[0] + 1, k[1] + 1))       # the unit writes lane 24 last
        w = clocks(" WIPE #2\n LD l0", keys=False)                                             # lane 0 is not in class 2
        for mask, row in ((1, "l0"), (2, "l8"), (2, "l24"), (4, "t0"), (4, "t23"), (3, "l7")):
            self.assertEqual(clocks(" WIPE #%d\n LD %s" % (mask, row), keys=False), (w[0] + 1, w[1] + 1), (mask, row))
        self.assertEqual(clocks(" WIPE #4\n LD st0", keys=False), w)                           # state rows are not wiped
        self.assertEqual(clocks(" WIPE #2\n LD #0\n LD l8", keys=False), (w[0] + 1, w[1]))    # one clock later: no stall
        a = clocks(" CTL AUTH\n LD #5\n KEYWR > k_dev0\n KMOV k_dev1 > l0\n KEC 12", where="key", keys=False)
        b = clocks(" CTL AUTH\n LD #5\n KEYWR > k_dev0\n KMOV k_dev0 > l0\n KEC 12", where="key", keys=False)
        self.assertEqual(b, (a[0] + 1, a[1] + 1))

    def test_a_fault_cuts_the_response_frame_short(self):
        from link import SpiLink
        body = " LD #3\n HDR #3\n LD #7\n PUSH H\n LD k_dev0"
        with self.assertRaises(ControlFault) as cm:
            run(body)
        self.assertEqual(cm.exception.sent, [host.rhdr(TEST_OP, 24), 7])            # what the link had carried
        c = common.new_chip(rom=rom_with(body))
        frame = SpiLink(c).exchange(host.bytes_of([host.hdr(TEST_OP)]))
        self.assertEqual(len(frame), 16)                                            # header says 3 words, 1 came
        self.assertEqual(c.pins["FAULT"], 1)

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
        self.fault(" KMOV k_dev0 > l0\n FLD PERM", "Poseidon2 in a keyed command", config="L")

    def test_fault_clears_secrets_and_raises_the_pin(self):
        d = common.provisioned()
        d.chip.rom = rom_with(" LD k_dev0")
        d.chip.m.rom, d.chip.m.dec = d.chip.rom, [(isa.decode(w), isa.OPS[w >> 23]) for w in d.chip.rom.words]
        self.assertEqual(len(d.chip.m.rf.key_values()), 4)
        with self.assertRaises(ControlFault):
            d.chip.transact([host.hdr(TEST_OP)])
        self.assertEqual(d.chip.m.rf.key_values(), set())
        self.assertFalse(any(d.chip.m.rf.rows))                            # every row, the state rows included
        self.assertEqual(d.chip.m.lc, isa.LC_RESET)
        self.assertEqual(d.chip.pins["FAULT"], 1)
        self.assertEqual(d.chip.transact(host.prf_msg(b"abc")), host.err(host.OP_PRFMSG, host.E_NOKEY))


if __name__ == "__main__":
    unittest.main()
