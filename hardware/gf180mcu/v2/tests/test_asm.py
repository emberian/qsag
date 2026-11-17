"""Assembler: field encoding round trips, canonical disassembly, error reporting."""
import random
import unittest

import common  # noqa: F401
import chip
import isa
import uasm


class Encoding(unittest.TestCase):
    def test_field_round_trip(self):
        rng = random.Random(1)
        for _ in range(5000):
            f = dict(op=rng.randrange(32), a=rng.randrange(128), b=rng.randrange(128), fn=rng.randrange(16),
                     ia=rng.randrange(2), ib=rng.randrange(2), xi=rng.randrange(2), seq=rng.randrange(4))
            w = isa.encode(**f)
            self.assertLess(w, 1 << isa.WIDTH)
            self.assertEqual(isa.decode(w), f)

    def test_immediates_and_targets(self):
        for v in (0, 1, 0x7F, 0x80, 0x3FFF, 0x4000, 0xFFFF):
            a, b, fn = isa.imm_fields(v)
            self.assertEqual(isa.imm16(dict(a=a, b=b, fn=fn)), v)
        for t in (1, 15, 16, 2047):
            b, fn = isa.target_fields(t)
            self.assertEqual(isa.target(dict(b=b, fn=fn)), t)

    def test_known_words(self):
        """Hand-encoded words pin the bit layout."""
        one = lambda s: uasm.assemble([("t", s)]).words[0]  # noqa: E731
        self.assertEqual(one("NOP"), 0)
        self.assertEqual(one("LD l3"), (1 << 23) | (3 << 16))
        self.assertEqual(one("XOR l0+X > l0+X x+"), (2 << 23) | (1 << 5) | (1 << 4) | (1 << 3) | (1 << 2))
        self.assertEqual(one("LD #0x1F"), (1 << 23) | (0x1F << 9) | (2 << 5))
        self.assertEqual(one("LD #0xFFFF"), (1 << 23) | (127 << 16) | (127 << 9) | (0xE << 5))
        self.assertEqual(one("ST t0"), (8 << 23) | (isa.SCRATCH0 << 9) | (1 << 5))
        self.assertEqual(one("KEC 12 ret"), (19 << 23) | (1 << 16) | 1)
        self.assertEqual(one("x: BXNE #17 x"), (26 << 23) | (17 << 16))
        self.assertEqual(one("KMOV k_dev2 > l0"), (15 << 23) | ((isa.KEY0 + 2) << 16))
        self.assertEqual(one("PMOV #3 > l5"), (15 << 23) | (3 << 16) | (5 << 9) | (1 << 5))
        self.assertEqual(one("CTL LC #4"), (17 << 23) | (1 << 16) | (4 << 9))
        self.assertEqual(one("UN XT"), (8 << 23) | (13 << 16))
        self.assertEqual(one("UN SHL1C > t0"), (8 << 23) | (14 << 16) | (isa.SCRATCH0 << 9) | (1 << 5))
        self.assertEqual(one("PUSH l2"), (12 << 23) | (2 << 16))
        self.assertEqual(one("REL l2"), (12 << 23) | (2 << 16) | (1 << 5))
        self.assertEqual(one("PUSH H"), (12 << 23) | (2 << 5))
        self.assertEqual(one("CMP l1"), (7 << 23) | (1 << 16))
        self.assertEqual(one("CMPT l1"), (7 << 23) | (1 << 16) | (1 << 5))
        self.assertEqual(one("FRAM WWORD l1"), (22 << 23) | (3 << 16) | (1 << 9))
        self.assertEqual(one("END"), 30 << 23)
        self.assertEqual(one("ILL"), 31 << 23)

    def test_org_pads_with_trap_words(self):
        rom = uasm.assemble([("t", "a: NOP\n.org 4\nb: END\n")])
        self.assertEqual(rom.words, [0, 31 << 23, 31 << 23, 31 << 23, 30 << 23])
        self.assertEqual((rom.padding, rom.labels["b"], rom.used), ({1, 2, 3}, 4, 2))
        with self.assertRaises(uasm.AsmError):
            uasm.assemble([("t", "NOP\nNOP\n.org 1\n")])

    def test_entries_carry_the_lifecycle_states_they_decode_in(self):
        rom = uasm.assemble([("t", "a: NOP\n.entry 0x40 a blank\n.entry 1 a any\n.entry 2 a ready\n.entry 3 a orphan|lease\n")])
        self.assertEqual(rom.entries, {0x40: (0, 1 << isa.LC_BLANK), 1: (0, isa.LC_ANY), 2: (0, 1 << isa.LC_READY),
                                       3: (0, (1 << isa.LC_ORPHAN) | (1 << isa.LC_LEASE))})
        with self.assertRaises(uasm.AsmError):
            uasm.assemble([("t", "a: NOP\n.entry 1 a sometimes\n")])
        with self.assertRaises(uasm.AsmError):
            uasm.assemble([("t", "a: NOP\n.entry 0x40 a\n")])

    def test_rom_images_disassemble_to_themselves(self):
        for cfg in "SL":
            rom = chip.build_rom(cfg)
            text = "\n".join(uasm.disasm(w) for w in rom.words)
            self.assertEqual(uasm.assemble([("d", text)]).words, rom.words)

    def test_every_operation_round_trips(self):
        src = """
        a: NOP
           LD l1
           XOR t3+X > l2+X x+
           AND #0xFFFF
           OR t0 > t1
           ADD #1
           SUB st0
           CMP l0
           UN NIB > t5
           UN SHL8
           DIN > t0+X
           LDF ARGHI
           LDC k1 > l16
           PUSH H
           PUSH l0+X x+
           REL l0+X x+
           CMPT l1
           HDR #70
           HDR #5 okz
           FAIL #5
           KMOV k_dev0 > l6
           PMOV #2 > l3
           KEYWR > k_dev0+X x+
           CTL SETFM
           WIPE #15
           KEC 24
           KEC 12 ret
           FLD PERM
           FLD RED > l0+X x+
           FADD l16+X > l16+X
           FRAM RWORD > t9
           FRAM WWORD l1
           FRAM WSTART
           CTL AUTH
           LDF TRAW
           LDF SYN1 > t2
           CTL LC #5
           CTL SYNW #1
           CTL TRUN
           UN XT > t1
           UN SHL1C
           END
           SETX #9
           SETX H
           SETC 1 #15
           SETC 0 H
           BR a
           BR HNZ a
           BXNE #17 a
           DBNZ 1 a
           CALL a
           INCX
           RET
           ST t0 ret
        """
        rom = uasm.assemble([("t", src)])
        self.assertEqual(len(rom.words), 54)
        again = uasm.assemble([("d", "\n".join(uasm.disasm(w) for w in rom.words))])
        self.assertEqual(again.words, rom.words)

    def test_errors(self):
        for bad in ("BR nowhere", "LD #0x10000", "FROB t0", "x: NOP\nx: NOP", "LD t0 > ", "KMOV k_dev0", "PMOV #1", "CTL LC", "CTL AUTH #1",
                    "PUSH l0 > t0", "LD r200", ".const C \"short\"", "SETC 0", "REL l0 > t0", "CMPT #5", "CMP l0 > t0",
                    "END ret", "FRAM WWORD", "FRAM WSTART > t0", "x: NOP\n.entry 1 x nobody", ".keyrange"):
            with self.assertRaises(uasm.AsmError, msg=bad):
                uasm.assemble([("t", bad)])

    def test_rom_fits_the_sequencer(self):
        for cfg in "SL":
            self.assertLessEqual(len(chip.build_rom(cfg).words), 1 << 11)


if __name__ == "__main__":
    unittest.main()
