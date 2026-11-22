"""Unit models: word unit, Keccak unit, field unit, FRAM master. Primitives come from the
reference model's qsag_prims.py (imported, not copied).

Clock counts:
  KECCAK_F / KECCAK_P12   measured on the existing lane-serial RTL (tb/run_unit_dp.sh, state report 1.1)
  P2_PERM                 measured on the existing RTL (same run)
  FIELD_ADD / FIELD_RED   estimate: one pass through the Goldilocks unit's adder and reduction
  FRAM_*                  estimate from qsag_anchor_spi.sv: SCK = clk / (2 (div + 1)), div = 1
  PUF_MEASURE             derived: 252 quads x 4 rings x 3 measurements x 15 us at 25 MHz, plus the decoder
  TRNG                    derived from the count values and the simulated ring period (physics/trng)
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
    if n == "XT":           # multiply by x in GF(2^64), modulus x^64 + x^4 + x^3 + x + 1
        return ((h << 1) & isa.M64) ^ (0x1B if h >> 63 else 0)
    if n == "SHL1C":        # as SHL1; the decoder also puts the bit shifted out in the carry
        return (h << 1) & isa.M64
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

    _memo = {}                      # the permutation is a pure function; tests repeat many calls

    def run(self, rf, rounds):
        key = (rounds, tuple(rf.rows[isa.LANE0:isa.LANE0 + 25]))
        st = self._memo.get(key)
        if st is None:
            if len(self._memo) > 400_000:
                self._memo.clear()
            st = self._memo[key] = q.keccak_p(list(key[1]), rounds)
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


FRAM_BYTES = 3 * 8 * isa.FRAM_REC_WORDS


class FramUnit:
    """SPI master for the FRAM on the carrier board. A transaction moves up to 16 words in one direction,
    least significant byte first, starting at byte address 128 * index: index 0 is the helper record,
    1 and 2 the two lifecycle slots. The memory itself is outside the chip; tests may rewrite it."""

    def __init__(self, mem=None):
        self.mem = mem if mem is not None else bytearray(FRAM_BYTES)
        self.pos = None
        self.left = 0
        self.writing = False

    def start(self, index, write):
        if self.pos is not None:
            raise FramMisuse("FRAM transaction already open")
        if index > 2:
            raise FramMisuse("FRAM record index out of range")
        self.pos, self.left, self.writing = 8 * isa.FRAM_REC_WORDS * index, isa.FRAM_REC_WORDS, write
        return FRAM_WSTART if write else FRAM_RSTART

    def _word(self, write):
        if self.pos is None or self.writing != write or self.left == 0:
            raise FramMisuse("FRAM word outside a matching transaction")
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


# ---------------------------------------------------------------- BCH(63,36,5) over GF(64)
GF_EXP, GF_LOG = [0] * 126, [0] * 64
_x = 1
for _i in range(63):                      # primitive polynomial x^6 + x + 1
    GF_EXP[_i] = GF_EXP[_i + 63] = _x
    GF_LOG[_x] = _i
    _x <<= 1
    if _x & 64:
        _x ^= 0x43


def _gmul(a, b):
    return GF_EXP[GF_LOG[a] + GF_LOG[b]] if a and b else 0


def _bch_generator():
    """lcm of the minimal polynomials of alpha^1 .. alpha^10: degree 27."""
    g, seen = 1, set()
    for j in range(1, 11):
        coset = set()
        e = j
        while e not in coset:
            coset.add(e)
            e = (2 * e) % 63
        if coset & seen:
            continue
        seen |= coset
        m = [1]                                          # product of (x + alpha^e), coefficients in GF(64)
        for e in coset:
            m = [(m[i - 1] if i else 0) ^ _gmul(m[i] if i < len(m) else 0, GF_EXP[e]) for i in range(len(m) + 1)]
        mb = sum((c & 1) << i for i, c in enumerate(m))
        assert all(c in (0, 1) for c in m)
        prod = 0
        for i in range(mb.bit_length()):
            if (mb >> i) & 1:
                prod ^= g << i
        g = prod
    return g


BCH_G = _bch_generator()
BCH_N, BCH_R, BCH_T = 63, 27, 5
assert BCH_G.bit_length() == BCH_R + 1


def bch_syndrome(w):
    """Remainder of the 63-bit word modulo the generator: the 27 helper bits of one block."""
    for i in range(BCH_N - 1, BCH_R - 1, -1):
        if (w >> i) & 1:
            w ^= BCH_G << (i - BCH_R)
    return w


def bch_error(rem):
    """Error pattern of weight <= 5 with this remainder, or None (Berlekamp-Massey, Chien search)."""
    if rem == 0:
        return 0
    syn = []
    for j in range(1, 2 * BCH_T + 1):
        v = 0
        for i in range(BCH_R):
            if (rem >> i) & 1:
                v ^= GF_EXP[(i * j) % 63]
        syn.append(v)
    c, b, big_l, m, bb = [1], [1], 0, 1, 1
    for n in range(2 * BCH_T):
        d = syn[n]
        for i in range(1, big_l + 1):
            if i < len(c):
                d ^= _gmul(c[i], syn[n - i])
        if d == 0:
            m += 1
            continue
        coef = _gmul(d, GF_EXP[63 - GF_LOG[bb]])
        t = list(c)
        c = c + [0] * (len(b) + m - len(c))
        for i, v in enumerate(b):
            c[i + m] ^= _gmul(coef, v)
        if 2 * big_l <= n:
            big_l, b, bb, m = n + 1 - big_l, t, d, 1
        else:
            m += 1
    if big_l > BCH_T:
        return None
    e = 0
    for pos in range(BCH_N):                             # root alpha^(-pos) marks an error at pos
        v = 0
        for i, ci in enumerate(c[:big_l + 1]):
            if ci:
                v ^= GF_EXP[(GF_LOG[ci] + i * (63 - pos)) % 63]
        if v == 0:
            e |= 1 << pos
    if bin(e).count("1") != big_l or bch_syndrome(e) != rem:
        return None
    return e


# ---------------------------------------------------------------- PUF organ (ARCHITECTURE.md 6.1)
PUF_BLOCKS = 4
PUF_MEASURE = 252 * 4 * 3 * 375 + 4 * 2000      # 15 us windows at 25 MHz; fixed-time decoder, estimate
M63 = (1 << 63) - 1
M27 = (1 << 27) - 1


class PufUnit:
    """252 response bits in four 63-bit blocks, the syndrome register, and the fixed-time decoder.

    `ideal` is the die's response (a parameter of the model: 32 bytes of seed); `flips` is the set of
    bit positions (0..251) that the next measurements read wrong. The response register is written by
    enrol() and reconstruct() and cleared at the end of every command; it is readable only through the
    decoder's PMOV rule. The syndrome register is public and lasts until reset."""

    def __init__(self, seed32, noise_seed=0):
        import hashlib
        d = hashlib.shake_256(b"dregg180-v2-model-puf" + bytes(seed32)).digest(32)
        v = int.from_bytes(d, "little")
        self.ideal = [(v >> (63 * i)) & M63 for i in range(PUF_BLOCKS)]
        self.flips = set()
        self.syn = [0, 0]
        self.rsp = None
        self._noise = (noise_seed, 0)

    def _measure(self):
        w = list(self.ideal)
        for p in self.flips:
            w[p // 63] ^= 1 << (p % 63)
        return w

    def enrol(self):
        self.rsp = self._measure()
        s = [bch_syndrome(w) for w in self.rsp]
        self.syn = [s[0] | (s[1] << 27), s[2] | (s[3] << 27)]
        return PUF_MEASURE

    def reconstruct(self):
        s = [self.syn[0] & M27, (self.syn[0] >> 27) & M27, self.syn[1] & M27, (self.syn[1] >> 27) & M27]
        out = []
        for w, h in zip(self._measure(), s):
            e = bch_error(bch_syndrome(w) ^ h)
            out.append(w ^ (e or 0))                     # undecodable: the word goes on as measured
        self.rsp = out
        return PUF_MEASURE

    def clear(self):
        self.rsp = None

    def power_on(self):
        self.syn, self.rsp = [0, 0], None

    def noise(self):
        """Counter noise from the characterisation rings (second source of the nonces). Not key material."""
        import hashlib
        seed, n = self._noise
        self._noise = (seed, n + 1)
        return int.from_bytes(hashlib.sha256(b"puf-noise" + seed.to_bytes(8, "little") + n.to_bytes(8, "little")).digest()[:8], "little")


# ---------------------------------------------------------------- TRNG organ (ARCHITECTURE.md 6.5)
TRNG_RINGS = 8
TRNG_PAIRS = [(a, b) for a in range(TRNG_RINGS) for b in range(a + 1, TRNG_RINGS)]      # 28
TRNG_RUN = 64                       # counts per TRUN
TRNG_T_OVER_CLK = 4.706 / 40.0      # one ring period in core clocks [S: 17 stages, 212 MHz]
TRNG_TIMEOUT = 1 << 14              # ring periods without a beat
TRNG_VAR1 = 9.79                    # count variance at d = 0.1 % [S: 2 kappa^2 / (d^3 T), kappa 4.8e-9]
TF_TIMEOUT, TF_SHORT, TF_RCT, TF_APT, TF_ARMED = 1, 2, 4, 8, 16
RCT_CUTOFF, APT_WINDOW, APT_CUTOFF = 41, 256, 218           # for a claim of 0.5 bit per raw bit


class TrngUnit:
    """Coherent-sampling source: eight rings, one selected pair, the beat counter, and the statistics the
    health tests of the microcode read. A stochastic model, not the circuit:

      offsets   relative period offset of each ring, in percent (the pair's d is the difference)
      kappa     jitter relative to the simulated thermal value (0: a noise-free source)
      flicker   slow random walk of the beat length, in counts per count (jitter that is not white)
      locked    pairs (indices into TRNG_PAIRS) whose rings lock: no beat
      nonwhite  pairs to which the flicker applies (None: all)
      script    per call of run() since reset (64 counts each), by index: dict(kappa=..) for that call,
                dict(timeout=True) a beat that never comes, dict(short=True) one beat of 10 periods

    The statistics accumulate from TCLR on: S1, the sum of squared differences of consecutive counts;
    S4, the same for sums of four counts; SUM; the flags; and the raw bits of the last 64 counts."""

    def __init__(self, seed=0, offsets=(0.00, 0.11, 0.37, 0.52, 0.80, 0.95, 1.30, 1.71), kappa=1.0, flicker=0.0, locked=(),
                 nonwhite=None, script=None):
        import random
        self.rng = random.Random(seed)
        self.offsets, self.kappa, self.flicker, self.locked = list(offsets), kappa, flicker, set(locked)
        self.nonwhite, self.script = nonwhite, dict(script or {})
        self.power_on()

    def power_on(self):
        self.pair, self.armed = 0, False
        self.t = self.walk = 0.0
        self.runs = 0
        self.clear()

    def clear(self):
        self.s1 = self.s4 = self.total = 0
        self.flags = 0
        self.prev = self.prev4 = None
        self.n = self.acc4 = 0
        self.raw = 0
        self.run_len, self.last_bit, self.ones, self.apt_n = 0, None, 0, 0

    def select(self, pair):
        self.pair = pair % len(TRNG_PAIRS)
        self.armed = False
        self.walk = 0.0

    def _count(self, kappa):
        a, b = TRNG_PAIRS[self.pair]
        d = abs(self.offsets[a] - self.offsets[b]) / 100.0
        if self.pair in self.locked or d < 1.0 / TRNG_TIMEOUT:
            return None
        mean = 1.0 / d
        sd = kappa * (TRNG_VAR1 * (1e-3 / d) ** 3) ** 0.5
        if self.nonwhite is None or self.pair in self.nonwhite:
            self.walk += self.flicker * self.rng.gauss(0.0, 1.0)
        t1 = self.t + max(1.0, mean + self.walk + sd * self.rng.gauss(0.0, 1.0))
        c = int(t1) - int(self.t)
        self.t = t1 % 1.0 + (int(t1) & 1)                 # keep the phase; the magnitude does not matter
        return max(c, 1)

    def run(self):
        """64 more counts (or a time-out). Returns core clocks."""
        clocks, self.raw = 0, 0
        ev = self.script.get(self.runs, {})
        self.runs += 1
        for i in range(TRNG_RUN):
            c = 10 if ev.get("short") and i == 0 else self._count(ev.get("kappa", self.kappa))
            if c is None or (ev.get("timeout") and i == 0):
                self.flags |= TF_TIMEOUT
                return clocks + int(TRNG_TIMEOUT * TRNG_T_OVER_CLK)
            clocks += max(1, int(c * TRNG_T_OVER_CLK))
            if c < 64:
                self.flags |= TF_SHORT
            if self.prev is not None:
                self.s1 = min(self.s1 + (c - self.prev) ** 2, (1 << 24) - 1)
            self.prev = c
            self.total = min(self.total + c, (1 << 24) - 1)
            self.acc4 += c
            self.n += 1
            if self.n % 4 == 0:
                if self.prev4 is not None:
                    self.s4 = min(self.s4 + (self.acc4 - self.prev4) ** 2, (1 << 24) - 1)
                self.prev4, self.acc4 = self.acc4, 0
            bit = c & 1
            self.raw |= bit << i
            self.run_len = self.run_len + 1 if bit == self.last_bit else 1
            self.last_bit = bit
            if self.run_len >= RCT_CUTOFF:
                self.flags |= TF_RCT
            self.ones += bit
            self.apt_n += 1
            if self.apt_n == APT_WINDOW:
                if max(self.ones, APT_WINDOW - self.ones) >= APT_CUTOFF:
                    self.flags |= TF_APT
                self.ones = self.apt_n = 0
        return clocks

    def flag_word(self):
        return self.flags | (TF_ARMED if self.armed else 0)
