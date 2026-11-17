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
                "SHL4": 0x123456789ABCDEF0, "SHL8": 0x23456789ABCDEF00}
        self.assertEqual(set(want), set(isa.UN))
        for n, v in want.items():
            self.assertEqual(units.unary(U[n], h), v, n)

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
        self.assertEqual(bytes(u.mem[32:40]).hex(), "8877665544332211")       # least significant byte first
        self.assertEqual(bytes(u.mem[:32]), bytes(32))
        u.start(1, False)
        self.assertEqual([u.rword()[0] for _ in range(3)], [0x1122334455667788, 2, 3])
        with self.assertRaises(units.FramMisuse):
            u.rword()                                                          # a fourth word
        with self.assertRaises(units.FramMisuse):
            u.start(0, True)                                                   # transaction still open
        u.done()
        with self.assertRaises(units.FramMisuse):
            u.done()
        with self.assertRaises(units.FramMisuse):
            u.wword(1)
        u.start(0, True)
        with self.assertRaises(units.FramMisuse):
            u.rword()
        self.assertEqual(len(u.mem), 64)
        self.assertEqual(clocks, units.FRAM_WSTART + 3 * units.FRAM_WORD + units.FRAM_DONE)


class Interfaces(unittest.TestCase):
    def test_puf_and_entropy_stand_ins(self):
        p = units.PufUnit(bytes(range(32)))
        self.assertEqual(p.reconstruct(), [0x0706050403020100, 0x0F0E0D0C0B0A0908, 0x1716151413121110, 0x1F1E1D1C1B1A1918])
        e = units.EntropyUnit(5)
        a, b = e.draw(), e.draw()
        self.assertNotEqual(a, b)
        self.assertEqual(units.EntropyUnit(5).draw(), a)
        self.assertNotEqual(units.EntropyUnit(6).draw(), a)


class Registers(unittest.TestCase):
    def test_row_map(self):
        self.assertEqual(isa.ROWS_S, 64)
        cls = [isa.row_class(r) for r in range(64)]
        self.assertEqual({c: cls.count(c) for c in set(cls)},
                         {"lane": 25, "kwork": 7, "scratch": 12, "key": 10, "pin": 6, "state": 2, "out": 2})
        self.assertEqual(isa.row_class(64), "none")
        self.assertEqual(isa.row_class(64, isa.ROWS_L), "chal")

    def test_wipe_classes(self):
        rf = RegFile(isa.ROWS_S)
        for r in range(64):
            rf[r] = r + 1
        rf.wipe(isa.W_LANES_HI)
        self.assertEqual([r for r in range(64) if rf[r] == 0], list(range(8, 32)))
        rf.wipe(15)
        self.assertEqual([r for r in range(64) if rf[r]], list(range(isa.KEY0, isa.OUT0)))
        rf.secret_reset()
        self.assertFalse(any(rf.rows))


if __name__ == "__main__":
    unittest.main()
