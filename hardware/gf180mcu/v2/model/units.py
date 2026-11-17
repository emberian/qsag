"""Unit models: word unit, Keccak unit, field unit, FRAM master. Primitives come from the
reference model's qsag_prims.py (imported, not copied).

Clock counts:
  KECCAK_F / KECCAK_P12   measured on the existing lane-serial RTL (tb/run_unit_dp.sh, state report 1.1)
  P2_PERM                 measured on the existing RTL (same run)
  FIELD_ADD / FIELD_RED   estimate: one pass through the Goldilocks unit's adder and reduction
  FRAM_*                  estimate from qsag_anchor_spi.sv: SCK = clk / (2 (div + 1)), div = 1
  PUF_BOOT / NONCE_DRAW / AUTH_VERIFY   estimates for the stage 3 and 4 interfaces (end of this file)
"""
import os
import sys

import isa

sys.path.insert(0, os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "model")))
import qsag_prims as q  # noqa: E402

P = q.P
KECCAK_F, KECCAK_P12 = 721, 373
P2_PERM = 3074
FIELD_ADD = FIELD_RED = 1
FRAM_DIV = 1
FRAM_BIT = 2 * (FRAM_DIV + 1)
FRAM_RSTART = 24 * FRAM_BIT                 # 0x03, two address bytes
FRAM_WSTART = (8 + 24) * FRAM_BIT + 4       # WREN, chip-select gap, 0x02, two address bytes
FRAM_WORD = 64 * FRAM_BIT
FRAM_DONE = 4


# ---------------------------------------------------------------- word unit
def _bswap32(x):
    return int.from_bytes((x & isa.M32).to_bytes(4, "little"), "big")


def unary(fn, h):
    """Wiring-only transforms of H (function names in isa.UN)."""
    n = isa.UN[fn]
    if n == "ID":
        return h
    if n == "NIB":          # swap the two nibbles of every byte
        return ((h >> 4) & 0x0F0F0F0F0F0F0F0F) | ((h & 0x0F0F0F0F0F0F0F0F) << 4)
    if n == "BE32":         # byte-reverse each 32-bit half
        return _bswap32(h) | (_bswap32(h >> 32) << 32)
    if n == "HSWAP":        # swap the 32-bit halves
        return ((h >> 32) | (h << 32)) & isa.M64
    if n == "LO32":
        return h & isa.M32
    if n == "HI32":
        return h & (isa.M32 << 32)
    if n.startswith("SHR"):
        return h >> int(n[3:])
    if n.startswith("SHL"):
        return (h << int(n[3:])) & isa.M64
    raise ValueError(n)


def alu(mn, h, x):
    """Two-operand word-unit functions. Returns (H', carry or None, mismatch or None)."""
    if mn == "LD":
        return x, None, None
    if mn == "XOR":
        return h ^ x, None, None
    if mn == "AND":
        return h & x, None, None
    if mn == "OR":
        return h | x, None, None
    if mn == "ADD":         # 32-bit; carry out of bit 31
        s = (h & isa.M32) + (x & isa.M32)
        return s & isa.M32, s >> 32, None
    if mn == "SUB":         # 32-bit; carry = borrow
        return ((h & isa.M32) - (x & isa.M32)) & isa.M32, int((h & isa.M32) < (x & isa.M32)), None
    if mn == "CMP":         # compare accumulator: Z |= (H != x); H unchanged
        return h, None, int(h != x)
    raise ValueError(mn)


# ---------------------------------------------------------------- Keccak unit
class KeccakUnit:
    """Lane-serial Keccak-f[1600] / Keccak-p[1600, 12] in place on lane rows 0..24.

    The seven work rows (column parities, saved lanes) are left holding values that are functions
    of the state; microcode must not depend on them and the decoder refuses to read them."""

    def run(self, rf, rounds):
        st = q.keccak_p([rf[isa.LANE0 + i] for i in range(25)], rounds)
        for i in range(25):
            rf[isa.LANE0 + i] = st[i]
        for i in range(5):
            rf[isa.KWORK0 + i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20]
        rf[isa.KWORK0 + 5], rf[isa.KWORK0 + 6] = st[23], st[24]
        return KECCAK_F if rounds == 24 else KECCAK_P12


# ---------------------------------------------------------------- field unit (configuration L)
class FieldUnit:
    """Goldilocks unit with the Poseidon2 micro-sequencer; the permutation is over lane rows 0..11."""

    def perm(self, rf):
        st = q.p2_perm([rf[isa.LANE0 + i] % P for i in range(12)])
        for i in range(12):
            rf[isa.LANE0 + i] = st[i]
        return P2_PERM

    @staticmethod
    def red(h):
        return h % P

    @staticmethod
    def add(h, x):
        return (h + x) % P


# ---------------------------------------------------------------- FRAM master
class FramMisuse(Exception):
    """A FRAM instruction out of sequence; the decoder turns it into a control fault."""


class FramUnit:
    """SPI master for the external anchor FRAM: one transaction moves a 24-byte record (three words,
    least significant byte first), record `slot` at byte address 32 * slot. The memory itself is
    outside the chip; tests may rewrite it."""

    def __init__(self, mem=None):
        self.mem = mem if mem is not None else bytearray(64)
        self.pos = None
        self.left = 0
        self.writing = False

    def start(self, slot, write):
        if self.pos is not None:
            raise FramMisuse("FRAM transaction already open")
        self.pos, self.left, self.writing = 32 * (slot & 1), 3, write
        return FRAM_WSTART if write else FRAM_RSTART

    def _word(self, write):
        if self.pos is None or self.writing != write or self.left == 0:
            raise FramMisuse("FRAM word outside a matching three-word transaction")
        self.left -= 1

    def rword(self):
        self._word(False)
        v = int.from_bytes(self.mem[self.pos:self.pos + 8], "little")
        self.pos += 8
        return v, FRAM_WORD

    def wword(self, v):
        self._word(True)
        self.mem[self.pos:self.pos + 8] = (v & isa.M64).to_bytes(8, "little")
        self.pos += 8
        return FRAM_WORD

    def done(self):
        if self.pos is None:
            raise FramMisuse("FRAM DONE without a transaction")
        self.pos = None
        return FRAM_DONE

    def abort(self):
        self.pos = None


# ---------------------------------------------------------------- interfaces to stage 3 and 4 machinery
# These stand in for organs that do not exist in stage 1. Each is absent by default, and the chip then
# refuses whatever needs it.
PUF_BOOT = 400_000          # estimate: PUF measurement and decoding, 16 ms at 25 MHz (ARCHITECTURE.md 3.3)
NONCE_DRAW = 8              # estimate
AUTH_VERIFY = 3_900_000     # upper bound of one SLH-DSA-128s verification (ARCHITECTURE.md 4.3)


class PufUnit:
    """Stage 3 interface: the device secret K_dev as PUF reconstruction would deliver it at boot.
    The secret is a parameter of the model; it never crosses the host link."""

    def __init__(self, secret32):
        assert len(secret32) == 32
        self._w = [int.from_bytes(secret32[i:i + 8], "little") for i in range(0, 32, 8)]

    def reconstruct(self):
        return list(self._w)


class EntropyUnit:
    """Stage 3 interface: a conditioned 128-bit nonce. Deterministic here, from a seed."""

    def __init__(self, seed=0):
        self.seed, self.n = seed, 0

    def draw(self):
        import hashlib
        d = hashlib.sha256(b"dregg180-v2-model-entropy" + self.seed.to_bytes(8, "little") + self.n.to_bytes(8, "little")).digest()
        self.n += 1
        return [int.from_bytes(d[0:8], "little"), int.from_bytes(d[8:16], "little")]
