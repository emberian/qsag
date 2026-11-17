"""Unit models against known answers that do not come from the model itself."""
import hashlib
import json
import unittest

import common
import isa
import units
from regfile import RegFile

q = units.q
U = {n: i for i, n in enumerate(isa.UN)}


class WordUnit(unittest.TestCase):
    def test_unary(self):
        h = 0x0123456789ABCDEF
        want = {"ID": h, "NIB": 0x1032547698BADCFE, "BE32": 0x67452301EFCDAB89, "HSWAP": 0x89ABCDEF01234567,
                "LO32": 0x89ABCDEF, "HI32": 0x0123456700000000, "SHR1": h >> 1, "SHR4": 0x00123456789ABCDE,
                "SHR8": 0x000123456789ABCD, "SHR16": 0x00000123456789AB, "SHL1": 0x02468ACF13579BDE,
                "SHL4": 0x123456789ABCDEF0, "SHL8": 0x23456789ABCDEF00, "XT": 0x02468ACF13579BDE,
                "SHL1C": 0x02468ACF13579BDE}
        self.assertEqual(set(want), set(isa.UN))
        for n, v in want.items():
            self.assertEqual(units.unary(U[n], h), v, n)

    def test_multiply_by_x_in_gf_2_64(self):
        """XT against a bit-serial product modulo x^64 + x^4 + x^3 + x + 1 (the GHASH-style reference below)."""
        def mul(a, b):
            r = 0
            for i in range(64):
                if (b >> i) & 1:
                    r ^= a << i
            for i in range(127, 63, -1):
                if (r >> i) & 1:
                    r ^= (0x1B | (1 << 64)) << (i - 64)
            return r
        for h in (1, 1 << 63, 0x8000000000000001, 0xFFFFFFFFFFFFFFFF, 0x0123456789ABCDEF):
            self.assertEqual(units.unary(U["XT"], h), mul(h, 2))
        self.assertEqual(units.unary(U["XT"], 1 << 63), 0x1B)

    def test_byte_order_helpers_against_struct(self):
        import struct
        for v in (0, 1, 5, 0x12345678, 0xFFFFFFFF):
            self.assertEqual(units.unary(U["BE32"], v), struct.unpack("<I", struct.pack(">I", v))[0])

    def test_alu(self):
        a = units.alu
        self.assertEqual(a("LD", 5, 9), (9, None, None))
        self.assertEqual(a("XOR", 0xF0, 0xFF), (0x0F, None, None))
        self.assertEqual(a("AND", 0xF0, 0x3C), (0x30, None, None))
        self.assertEqual(a("OR", 0xF0, 0x0F), (0xFF, None, None))
        self.assertEqual(a("ADD", 0xFFFFFFFF, 1), (0, 1, None))
        self.assertEqual(a("ADD", 2, 3), (5, 0, None))
        self.assertEqual(a("ADD", 0x1_00000002, 3), (5, 0, None))          # 32-bit: upper halves ignored
        self.assertEqual(a("SUB", 3, 5), (0xFFFFFFFE, 1, None))
        self.assertEqual(a("SUB", 5, 5), (0, 0, None))
        self.assertEqual(a("SUB", 5, (1 << 32) | 3), (2, 0, None))
        self.assertEqual(a("CMP", 7, 7), (7, None, 0))
        self.assertEqual(a("CMP", 7, 7 | (1 << 63)), (7, None, 1))


class Keccak(unittest.TestCase):
    def _sponge(self, msg, suffix, outlen, rounds):
        """A sponge built on the unit only (padding done here), rate 136."""
        rf, k = RegFile(isa.ROWS_S), units.KeccakUnit()
        blk = bytearray(msg) + bytes(-(len(msg) + 1) % 136 + 1)
        blk[len(msg)] ^= suffix
        blk[-1] ^= 0x80
        clocks = 0
        for off in range(0, len(blk), 136):
            for i in range(17):
                rf[i] = rf[i] ^ int.from_bytes(blk[off + 8 * i:off + 8 * i + 8], "little")
            clocks += k.run(rf, rounds)
        return b"".join(rf[i].to_bytes(8, "little") for i in range(17))[:outlen], clocks

    def test_shake256_and_sha3_against_hashlib(self):
        for n in (0, 1, 135, 136, 137, 300):
            m = bytes((7 * i + 3) & 0xFF for i in range(n))
            self.assertEqual(self._sponge(m, 0x1F, 64, 24)[0], hashlib.shake_256(m).digest(64))
        # Keccak-f[1600] of the all-zero state: published first lane
        rf, k = RegFile(isa.ROWS_S), units.KeccakUnit()
        self.assertEqual(k.run(rf, 24), 721)
        self.assertEqual(rf[0], 0xF1258F7940E1DDE7)

    def test_turboshake256_rfc9861(self):
        out, clocks = self._sponge(b"", 0x1F, 64, 12)
        self.assertTrue(out.hex().startswith("367a329dafea871c7802ec67f905ae13"))
        self.assertEqual(clocks, 373)

    def test_work_rows_do_not_hold_zero(self):
        rf, k = RegFile(isa.ROWS_S), units.KeccakUnit()
        k.run(rf, 24)
        self.assertTrue(any(rf[isa.KWORK0 + i] for i in range(isa.N_KWORK)))


class Field(unittest.TestCase):
    def setUp(self):
        with open(common.FIXTURE) as fh:
            self.fx = json.load(fh)

    def test_poseidon2_against_lean_oracle(self):
        f = units.FieldUnit()
        for e in self.fx["poseidon2_12"]:
            rf = RegFile(isa.ROWS_L)
            for i, v in enumerate(e["input"]):
                rf[i] = f.red(int(v))
            self.assertEqual(f.perm(rf), 3074)
            self.assertEqual([rf[i] for i in range(12)], [int(v) for v in e["perm"]])

    def test_add_and_reduce_against_lean_oracle(self):
        f = units.FieldUnit()
        for e in self.fx["goldilocks_edges"]:
            a, b = int(e["a_raw"]), int(e["b_raw"])
            self.assertEqual(f.red(a), int(e["a_canon"]))
            self.assertEqual(f.add(f.red(a), f.red(b)), int(e["add"]))


class Fram(unittest.TestCase):
    def test_record_round_trip_and_layout(self):
        u = units.FramUnit()
        clocks = u.start(1, True)
        for w in (0x1122334455667788, 2, 3):
            clocks += u.wword(w)
        clocks += u.done()
        self.assertEqual(bytes(u.mem[128:136]).hex(), "8877665544332211")     # least significant byte first
        self.assertEqual(bytes(u.mem[:128]), bytes(128))
        u.start(1, False)
        self.assertEqual([u.rword()[0] for _ in range(3)], [0x1122334455667788, 2, 3])
        for _ in range(13):
            u.rword()
        with self.assertRaises(units.FramMisuse):
            u.rword()                                                          # a seventeenth word
        with self.assertRaises(units.FramMisuse):
            u.start(0, True)                                                   # transaction still open
        u.done()
        with self.assertRaises(units.FramMisuse):
            u.done()
        with self.assertRaises(units.FramMisuse):
            u.wword(1)
        with self.assertRaises(units.FramMisuse):
            u.start(3, False)                                                  # three records: helper and two slots
        u.start(0, True)
        with self.assertRaises(units.FramMisuse):
            u.rword()
        self.assertEqual(len(u.mem), 384)
        self.assertEqual(clocks, units.FRAM_WSTART + 3 * units.FRAM_WORD + units.FRAM_DONE)


class Bch(unittest.TestCase):
    """The decoder of the PUF organ model: BCH(63,36,5)."""

    def test_generator_is_the_one_of_the_existing_rtl(self):
        self.assertEqual(units.BCH_G, 0x86E8113)                # G_MASK of rtl/dregg_ro_puf_bch.sv

    def test_up_to_five_errors_are_found_and_six_are_not_miscorrected_silently(self):
        import random
        r = random.Random(7)
        for trial in range(200):
            w = r.getrandbits(63)
            k = trial % 8
            e = sum(1 << p for p in r.sample(range(63), k))
            got = units.bch_error(units.bch_syndrome(w) ^ units.bch_syndrome(w ^ e))
            if k <= 5:
                self.assertEqual(got, e)
            else:                                               # beyond the radius: no pattern, or another codeword's
                self.assertTrue(got is None or (got != e and bin(got).count("1") <= 5))

    def test_syndrome_is_linear_and_27_bits(self):
        a, b = 0x1234567890ABCDE, 0x7EDCBA098765432
        self.assertEqual(units.bch_syndrome(a) ^ units.bch_syndrome(b), units.bch_syndrome(a ^ b))
        self.assertLess(units.bch_syndrome(a), 1 << 27)


class PufOrgan(unittest.TestCase):
    def test_enrol_then_reconstruct(self):
        p = units.PufUnit(bytes(range(32)))
        p.enrol()
        w, syn = list(p.rsp), list(p.syn)
        self.assertEqual(w, p.ideal)
        self.assertTrue(all(0 < x < (1 << 54) for x in syn))
        p.clear()
        p.flips = {0, 5, 20, 40, 62, 63 + 7, 126 + 1, 126 + 2, 126 + 3, 126 + 4, 126 + 5, 251}      # at most five a block
        p.reconstruct()
        self.assertEqual(p.rsp, w)
        p.flips = {0, 1, 2, 3, 4, 5}                            # six in block 0
        p.reconstruct()
        self.assertNotEqual(p.rsp, w)
        self.assertEqual(p.rsp[1:], w[1:])
        p.power_on()
        self.assertEqual((p.syn, p.rsp), ([0, 0], None))

    def test_reconstruction_uses_the_syndrome_register(self):
        p = units.PufUnit(bytes(range(32)))
        p.enrol()
        w = list(p.rsp)
        p.syn = [p.syn[0] ^ 1, p.syn[1]]                        # helper data for another response
        p.reconstruct()
        self.assertNotEqual(p.rsp, w)

    def test_different_dies_differ(self):
        self.assertNotEqual(units.PufUnit(bytes(32)).ideal, units.PufUnit(bytes([1]) + bytes(31)).ideal)


class TrngOrgan(unittest.TestCase):
    """The stochastic model against the figures of the physics report (trng/coso_model.py)."""

    def stats(self, pair, **kw):
        t = units.TrngUnit(11, **kw)
        t.select(pair)
        t.clear()
        clocks = sum(t.run() for _ in range(4))
        return t, clocks

    def test_variance_statistic_tracks_the_simulated_table(self):
        t, clocks = self.stats(units.TRNG_PAIRS.index((0, 1)), offsets=(0, 0.10, 1, 2, 3, 4, 5, 6))
        self.assertTrue(6.0 < t.s1 / 510 < 15.0, t.s1 / 510)       # d = 0.10 %: V = 10.1 [S]
        self.assertTrue(950 < t.total / 256 < 1050)
        self.assertEqual(t.flags, 0)
        self.assertTrue(20_000 < clocks < 40_000)                  # 256 beats of 1,000 periods of 4.7 ns
        t, _ = self.stats(units.TRNG_PAIRS.index((0, 1)), offsets=(0, 0.20, 1, 2, 3, 4, 5, 6))
        self.assertTrue(0.8 < t.s1 / 510 < 2.5, t.s1 / 510)        # d = 0.20 %: V = 1.48 [S]

    def test_a_noise_free_source_has_no_variance(self):
        for d in (0.07, 0.11, 0.15, 0.21):
            t, _ = self.stats(0, offsets=(0, d, 1, 2, 3, 4, 5, 6), kappa=0.0)
            self.assertLess(t.s1 / 510, 0.5)                       # at most 0.33 [S]

    def test_locked_and_distant_pairs_raise_flags(self):
        t, clocks = self.stats(0, locked={0})
        self.assertEqual(t.flags & units.TF_TIMEOUT, units.TF_TIMEOUT)
        t, _ = self.stats(units.TRNG_PAIRS.index((0, 7)))          # d = 1.71 %: beats of 58 periods
        self.assertEqual(t.flags & units.TF_SHORT, units.TF_SHORT)

    def test_slow_jitter_shows_in_the_sums_of_four(self):
        t, _ = self.stats(0, flicker=1.5, kappa=0.3)
        self.assertGreater(85 * t.s4, 168 * t.s1)                  # V4 > 8 V
        t, _ = self.stats(0)
        self.assertLess(85 * t.s4, 168 * t.s1)                     # white: V4 is about 4 V


class Registers(unittest.TestCase):
    def test_row_map(self):
        self.assertEqual(isa.ROWS_S, 72)
        cls = [isa.row_class(r) for r in range(72)]
        self.assertEqual({c: cls.count(c) for c in set(cls)},
                         {"lane": 25, "kwork": 7, "scratch": 24, "key": 4, "state": 10, "out": 2})
        self.assertEqual(isa.row_class(72), "none")
        self.assertEqual(isa.row_class(72, isa.ROWS_L), "chal")

    def test_wipe_classes(self):
        rf = RegFile(isa.ROWS_S)
        for r in range(72):
            rf[r] = r + 1
        rf.wipe(isa.W_LANES_HI)
        self.assertEqual([r for r in range(72) if rf[r] == 0], list(range(8, 32)))
        rf.wipe(15)
        self.assertEqual([r for r in range(72) if rf[r]], list(range(isa.KEY0, isa.OUT0)))     # keys and state stay
        rf.secret_reset()
        self.assertFalse(any(rf.rows))


if __name__ == "__main__":
    unittest.main()
