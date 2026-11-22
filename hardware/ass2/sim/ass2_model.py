#!/usr/bin/env python3
"""ASS2 / Dregg-64 golden model for the lockstep cosim (Sub-Lane 3).

Instruction semantics follow `ass2-dregg64-canonical-spec.md`, independently of `crates/qsag-ass2`
(Sub-Lane 1A) and of `hardware/ass2/rtl` (Sub-Lane 2), so that a three-way agreement
(this model / Rust `Ass2Vm` / RTL) means something. Places where the spec leaves a
choice open are `Knobs` fields, each with the spec line it comes from; the defaults are
this author's reading and get aligned to the Rust VM only by an explicit knob change
that is recorded in the vector file header.
"""
from dataclasses import dataclass, field

M64 = (1 << 64) - 1
P = (1 << 64) - (1 << 32) + 1  # Goldilocks

ECAUSE_ILLEGAL, ECAUSE_ENVCALL, ECAUSE_MISPC, ECAUSE_MISMEM, ECAUSE_MEMFAULT = 1, 2, 3, 4, 5

CSR_ARCH_ID, CSR_WORD_BITS, CSR_EVEC, CSR_POWER, CSR_INSTRET, CSR_CYCLES = 0, 1, 2, 3, 4, 5
CSR_FEATURES, CSR_EPC, CSR_ECAUSE, CSR_DBG_OUT, CSR_EXC_EN, CSR_DIT, CSR_ZEROIZE = (
    6, 8, 9, 0x0A, 0x3F, 0x40, 0x41)
ARCH_ID = 0x4153_5332_0000_0001
FEATURES = 0xF


# --------------------------------------------------------------------------- knobs
@dataclass
class Knobs:
    """Choices the canonical spec does not pin down."""
    # Spec 0x04/0x05: INSTRET counts "retired non-trapping" instructions; CYCLES adds
    # cycle_cost(op, sub). Nothing says what CYCLES does on a trap.
    trap_cycle_cost: int = 1  # Rust Ass2Vm and RTL trap entry
    # Spec SYS/EXC: "Software trap (1 cycle)". Taken (EXC_EN=1) it redirects to EVEC;
    # untaken it is "PC := PC + 4". Does it count in INSTRET / CYCLES?
    exc_taken_retires: bool = False      # EXC_EN=1: counts as an instruction?
    exc_taken_cycles: int = 1            # EXC_EN=1: CYCLES += this
    exc_untaken_retires: bool = True     # EXC_EN=0: behaves as a 1-cycle NOP
    # CSRR of a write-only / unassigned CSR, CSRW of a read-only / unassigned CSR.
    csr_bad_read: str = "trap"           # "trap" | "zero"
    csr_bad_write: str = "trap"          # "trap" | "ignore"
    # CSRR INSTRET / CYCLES: value before or after this instruction's own increment.
    csr_counter_read_post: bool = False
    # Reset values.
    reset_pc: int = 0
    reset_exc_en: int = 0


# --------------------------------------------------------------------------- field / hash kernels
def gl(x):
    return x % P


def gl_pow7(x):
    x %= P
    x2 = x * x % P
    x3 = x2 * x % P
    return x3 * x3 % P * x % P


def fp5_mul(a, b):
    a = [x % P for x in a]
    b = [x % P for x in b]
    c = [0] * 9
    for i in range(5):
        for j in range(5):
            c[i + j] += a[i] * b[j]
    return [(c[k] + 3 * (c[k + 5] if k + 5 < 9 else 0)) % P for k in range(5)]


def gf128_mul(a, b):
    """Polynomial basis, bit i = x^i, modulus x^128 + x^7 + x^2 + x + 1."""
    r = 0
    for i in range(128):
        if (b >> i) & 1:
            r ^= a << i
    for i in range(254, 127, -1):
        if (r >> i) & 1:
            r ^= (1 << i) ^ (0x87 << (i - 128))
    return r & ((1 << 128) - 1)


KECCAK_RC = []
KECCAK_ROT = [[0] * 5 for _ in range(5)]  # [x][y]


def _keccak_init():
    r = 1
    for _ in range(24):
        rc = 0
        for j in range(7):
            r = ((r << 1) ^ ((r >> 7) * 0x71)) & 0xFF
            if r & 2:
                rc ^= 1 << ((1 << j) - 1)
        KECCAK_RC.append(rc)
    x, y = 1, 0
    for t in range(24):
        KECCAK_ROT[x][y] = ((t + 1) * (t + 2) // 2) % 64
        x, y = y, (2 * x + 3 * y) % 5


_keccak_init()


def _rol(v, n):
    n &= 63
    return ((v << n) | (v >> (64 - n))) & M64 if n else v


def keccak_f1600(s, rounds):
    """Last `rounds` rounds of Keccak-f[1600]; lane index = x + 5*y."""
    a = list(s)
    for rnd in range(24 - rounds, 24):
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rol(a[x + 5 * y], KECCAK_ROT[x][y])
        a = [b[i] ^ ((~b[(i % 5 + 1) % 5 + 5 * (i // 5)]) & b[(i % 5 + 2) % 5 + 5 * (i // 5)])
             for i in range(25)]
        a[0] ^= KECCAK_RC[rnd]
    return [v & M64 for v in a]


# Poseidon2 width 12 ("POS2_GL1", Stafford-13 constants; qsag-accel poseidon2_perm12)
P2_IV = 0x504F_5332_5F47_4C31


def _rc_bij(x):
    z = (x + 0x9E37_79B9_7F4A_7C15) & M64
    z = ((z ^ (z >> 30)) * 0xBF58_476D_1CE4_E5B9) & M64
    z = ((z ^ (z >> 27)) * 0x94D0_49BB_1331_11EB) & M64
    return z ^ (z >> 31)


def p2_const(tag, rnd, lane):
    return _rc_bij(_rc_bij(_rc_bij(P2_IV ^ tag) ^ rnd) ^ lane) % P


def _m4(b):
    s = (b[0] + b[1] + b[2] + b[3]) % P
    return [(s + b[i] + 2 * b[(i + 1) % 4]) % P for i in range(4)]


def _p2_12_me(st):
    t = [st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11]]
    y = [_m4(t[0:4]), _m4(t[4:8]), _m4(t[8:12])]
    o = [0] * 12
    for i in range(4):
        s = (y[0][i] + y[1][i] + y[2][i]) % P
        for k in range(3):
            o[4 * k + i] = (y[k][i] + s) % P
    return [o[0], o[4], o[8], o[1], o[5], o[9], o[2], o[6], o[10], o[3], o[7], o[11]]


def _p2_12_mi(st):
    s = sum(st) % P
    o = [(s - 64 * st[0]) % P, (st[1] + s) % P]
    d = 2
    for x in st[2:]:
        o.append((d * x + s) % P)
        d *= 2
    return o


def poseidon2_gl12(st):
    st = _p2_12_me([x % P for x in st])
    for r in range(4):
        st = _p2_12_me([gl_pow7(st[i] + p2_const(0, r, i)) for i in range(12)])
    for r in range(22):
        st[0] = gl_pow7(st[0] + p2_const(1, r, 0))
        st = _p2_12_mi(st)
    for r in range(4):
        st = _p2_12_me([gl_pow7(st[i] + p2_const(2, r, i)) for i in range(12)])
    return st


# Poseidon2 width 24 (Grain constants; qsag-accel poseidon2_gl24_perm). Table in p2gl24_rc.py
from p2gl24_rc import POSEIDON2_GL24_RC  # noqa: E402


def _p2_24_me(st):
    st = [x % P for x in st]
    y = [_m4([st[c], st[6 + c], st[12 + c], st[18 + c]]) for c in range(6)]
    o = [0] * 24
    for g in range(4):
        s = sum(y[c][g] for c in range(6)) % P
        for c in range(6):
            o[6 * g + c] = (y[c][g] + s) % P
    return o


def _p2_24_mi(st):
    s = sum(st) % P
    o = [(s - (st[0] << 23)) % P, (s + st[1]) % P]
    for j in range(2, 24):
        o.append((s + (st[j] << (j - 1))) % P)
    return o


def poseidon2_gl24(st):
    rc = POSEIDON2_GL24_RC
    st = _p2_24_me(st)
    for r in range(4):
        st = _p2_24_me([gl_pow7(st[i] + rc[24 * r + i]) for i in range(24)])
    for r in range(44):
        st[0] = gl_pow7(st[0] + rc[96 + r])
        st = _p2_24_mi(st)
    for r in range(4):
        st = _p2_24_me([gl_pow7(st[i] + rc[140 + 24 * r + i]) for i in range(24)])
    return st


# --------------------------------------------------------------------------- helpers
def sext(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def s64(v):
    return v - (1 << 64) if v >> 63 else v


class Trap(Exception):
    def __init__(self, cause):
        self.cause = cause


class Memory:
    """Byte-addressed little-endian memory made of (base, size) regions."""

    def __init__(self, regions):
        self.regions = [(b, s, bytearray(s)) for b, s in regions]

    def _find(self, addr, n):
        for b, s, buf in self.regions:
            if b <= addr and addr + n <= b + s:
                return buf, addr - b
        return None, 0

    def ok(self, addr, n):
        return self._find(addr, n)[0] is not None

    def read(self, addr, n):
        buf, o = self._find(addr, n)
        if buf is None:
            raise Trap(ECAUSE_MEMFAULT)
        return int.from_bytes(buf[o:o + n], "little")

    def write(self, addr, n, val):
        buf, o = self._find(addr, n)
        if buf is None:
            raise Trap(ECAUSE_MEMFAULT)
        buf[o:o + n] = (val & ((1 << (8 * n)) - 1)).to_bytes(n, "little")

    def poke_bytes(self, addr, data):
        buf, o = self._find(addr, len(data))
        assert buf is not None, hex(addr)
        buf[o:o + len(data)] = data


def cycle_cost(w):
    """Fixed architectural latency of a *valid* instruction word (spec section 2)."""
    op, sub, imm8 = w >> 28, (w >> 16) & 0xF, (w >> 20) & 0xFF
    if op == 0x2:
        return 4 if sub in (7, 8) else 1
    if op in (0x7, 0x8):
        return 2
    if op == 0xC:
        return 2 if ((w >> 8) & 0xF) in (4, 5) else 1
    if op == 0xD:
        return {0: 4, 1: 1, 2: 1, 3: 12, 4: 104, 5: 5, 6: 5}[sub]
    if op == 0xE:
        return 4 if sub == 0 else 1
    if op == 0xF:
        return {0: imm8, 1: 216, 2: 120}[sub]
    return 1


@dataclass
class StepInfo:
    pc: int
    insn: int            # fetched word (0 when the fetch itself trapped)
    trapped: int = 0     # 0 = retired normally, else ECAUSE of the trap taken
    reg_writes: dict = field(default_factory=dict)   # 0..15 = R, 16..40 = S
    mem_writes: list = field(default_factory=list)   # (addr, byte)
    dbg_out: list = field(default_factory=list)


class Ass2:
    def __init__(self, regions, knobs=None):
        self.k = knobs or Knobs()
        self.mem = Memory(regions)
        self.reset()

    def reset(self):
        self.pc = self.k.reset_pc
        self.r = [0] * 16
        self.s = [0] * 25
        self.evec = self.epc = self.ecause = 0
        self.instret = self.cycles = 0
        self.exc_en = self.k.reset_exc_en
        self.halted = False

    # -- register access with write logging
    def _wr(self, rd, v):
        if rd:
            self.r[rd] = v & M64
            self._info.reg_writes[rd] = self.r[rd]

    def _ws(self, i, v):
        self.s[i] = v & M64
        self._info.reg_writes[16 + i] = self.s[i]

    def _mw(self, addr, n, v):
        self.mem.write(addr, n, v)
        for i in range(n):
            self._info.mem_writes.append((addr + i, (v >> (8 * i)) & 0xFF))

    def _zeroize(self):
        for i in range(1, 16):
            self._wr(i, 0)
        for i in range(25):
            self._ws(i, 0)

    # -- CSRs
    def _csr_read(self, a):
        if a == CSR_ARCH_ID:
            return ARCH_ID
        if a == CSR_WORD_BITS:
            return 64
        if a == CSR_EVEC:
            return self.evec
        if a == CSR_INSTRET:
            return (self.instret + (1 if self.k.csr_counter_read_post else 0)) & M64
        if a == CSR_CYCLES:
            return (self.cycles + (1 if self.k.csr_counter_read_post else 0)) & M64
        if a == CSR_FEATURES:
            return FEATURES
        if a == CSR_EPC:
            return self.epc
        if a == CSR_ECAUSE:
            return self.ecause
        if a == CSR_EXC_EN:
            return self.exc_en
        if a == CSR_DIT:
            return 1
        if self.k.csr_bad_read == "trap":
            raise Trap(ECAUSE_ILLEGAL)
        return 0

    def _csr_write(self, a, v):
        """Returns (instret_overridden, cycles_overridden)."""
        if a == CSR_EVEC:
            self.evec = v & ~3 & M64
        elif a == CSR_POWER:
            if v & 1:
                self.halted = True
        elif a == CSR_INSTRET:
            self.instret = v
            return True, False
        elif a == CSR_CYCLES:
            self.cycles = v
            return False, True
        elif a == CSR_EPC:
            self.epc = v
        elif a == CSR_ECAUSE:
            self.ecause = v
        elif a == CSR_DBG_OUT:
            self._info.dbg_out.append(v & 0xFF)
        elif a == CSR_EXC_EN:
            self.exc_en = v & 1
        elif a == CSR_ZEROIZE:
            if v & 1:
                self._zeroize()
        elif self.k.csr_bad_write == "trap":
            raise Trap(ECAUSE_ILLEGAL)
        return False, False

    # -- one instruction
    def step(self):
        if self.halted:
            return None
        pc0 = self.pc
        info = self._info = StepInfo(pc=pc0, insn=0)
        try:
            if pc0 & 3:
                raise Trap(ECAUSE_MISPC)
            w = info.insn = self.mem.read(pc0, 4)
            npc, ir_over, cy_over, retire, cost = self._exec(w, pc0)
        except Trap as t:
            info.trapped = t.cause
            info.reg_writes.clear()
            info.mem_writes.clear()
            info.dbg_out.clear()
            self._trap(t.cause, pc0)
            self.cycles = (self.cycles + self.k.trap_cycle_cost) & M64
            return info
        self.pc = npc & M64
        if retire and not ir_over:
            self.instret = (self.instret + 1) & M64
        if not cy_over:
            self.cycles = (self.cycles + cost) & M64
        return info

    def _trap(self, cause, epc):
        if self.exc_en:
            self.epc, self.ecause, self.exc_en, self.pc = epc & M64, cause, 0, self.evec
        else:
            self.halted, self.ecause = True, cause

    def _exec(self, w, pc):
        """Decode + execute. All traps are raised before any architectural write."""
        r = self.r
        op = w >> 28
        rd, ra, rb, rc = w & 0xF, (w >> 4) & 0xF, (w >> 8) & 0xF, (w >> 12) & 0xF
        sub, imm8 = (w >> 16) & 0xF, (w >> 20) & 0xFF
        npc = pc + 4
        ill = Trap(ECAUSE_ILLEGAL)
        ir_over = cy_over = False
        retire = True

        if op == 0x0:
            if w == 0:  # EXC
                if self.exc_en:
                    self._info.trapped = ECAUSE_ENVCALL
                    self.epc, self.ecause, self.exc_en = (pc + 4) & M64, ECAUSE_ENVCALL, 0
                    return self.evec, False, False, self.k.exc_taken_retires, self.k.exc_taken_cycles
                return npc, False, False, self.k.exc_untaken_retires, 1
            if sub == 1:
                if w & 0x0FF0_FFFF:
                    raise ill
                npc = self.epc & ~3
                self.exc_en = 1
            elif sub == 2:
                if ra or rb or rc:
                    raise ill
                self._wr(rd, self._csr_read(imm8))
            elif sub == 3:
                if rd or rb or rc:
                    raise ill
                ir_over, cy_over = self._csr_write(imm8, r[ra])
            elif sub == 4:
                if w & 0x0FF0_FFFF:
                    raise ill
                self._zeroize()
            elif sub == 5:
                if w & 0x0FF0_FFFF:
                    raise ill
                self.halted = True
            elif sub == 6:
                if w != 0x0006_0000:
                    raise ill
            else:
                raise ill

        elif op == 0x1:  # LUT4
            if rc or imm8:
                raise ill
            a, b, m = r[ra], r[rb], sub
            na, nb = a ^ M64, b ^ M64
            out = ((na & nb) if m & 1 else 0) | ((na & b) if m & 2 else 0) | \
                  ((a & nb) if m & 4 else 0) | ((a & b) if m & 8 else 0)
            self._wr(rd, out)

        elif op == 0x2:  # ALU
            if rc or imm8 or sub > 8:
                raise ill
            a, b = r[ra], r[rb]
            if sub == 0:
                v = a + b
            elif sub == 1:
                v = a - b
            elif sub == 2:
                v = 0 if b >= 64 else a << b
            elif sub == 3:
                v = 0 if b >= 64 else a >> b
            elif sub == 4:
                v = (M64 if a >> 63 else 0) if b >= 64 else s64(a) >> b
            elif sub == 5:
                v = _rol(a, b & 63)
            elif sub == 6:
                v = _rol(a, (64 - (b & 63)) & 63)
            elif sub == 7:
                v = a * b
            else:
                v = (a * b) >> 64
            self._wr(rd, v)

        elif op == 0x3:  # ALUI
            fn, imm16, a = rb, (w >> 12) & 0xFFFF, r[ra]
            if fn > 9 or (5 <= fn <= 8 and imm16 >> 6):
                raise ill
            k = imm16 & 63
            v = [a + sext(imm16, 16), a + imm16, a ^ imm16, a & imm16, a | imm16, a << k, a >> k,
                 s64(a) >> k, _rol(a, k), (a << 16) | imm16][fn]
            self._wr(rd, v)

        elif op == 0x4:  # IMM20
            mode, imm20 = ra, (w >> 8) & 0xFFFFF
            if mode > 2:
                raise ill
            self._wr(rd, [imm20, sext(imm20, 20), pc + (sext(imm20, 20) << 2)][mode])

        elif op == 0x5:  # CMP
            if sub or imm8:
                raise ill
            a, b, f = r[ra], r[rb], rc
            e = bool(f & 1) and a == b
            g = bool(f & 2) and ((s64(a) > s64(b)) if f & 4 else (a > b))
            c = e or g
            self._wr(rd, int((not c) if f & 8 else c))

        elif op == 0x6:  # SEL / byte
            if imm8 or sub > 3:
                raise ill
            if sub == 0:
                self._wr(rd, r[ra] if r[rc] == 0 else r[rb])
            elif sub in (1, 2):
                if (rb >> 3) or (rc >> 3):
                    raise ill
                bi, bl = rb & 7, (rc & 7) or 8
                v = (r[ra] >> (8 * bi)) & ((1 << (8 * bl)) - 1)
                if sub == 2 and bl < 8:
                    v = sext(v, 8 * bl)
                self._wr(rd, v)
            else:
                if rb or rc:
                    raise ill
                self._wr(rd, int.from_bytes(r[ra].to_bytes(8, "little"), "big"))

        elif op in (0x7, 0x8):  # LOAD / STORE
            mode, simm = rb, sext((w >> 12) & 0xFFFF, 16)
            if mode > 1:
                raise ill
            if mode == 0:
                ea = (r[ra] + (simm << 3)) & M64
                if ea & 7:
                    raise Trap(ECAUSE_MISMEM)
                n = 8
            else:
                ea = (r[ra] + simm) & M64
                n = 1
            if op == 0x7:
                self._wr(rd, self.mem.read(ea, n))
            else:
                self._mw(ea, n, r[rd])

        elif op == 0x9:  # BR
            bop, off, c = ra, sext((w >> 8) & 0xFFFFF, 20), r[rd]
            if bop > 3:
                raise ill
            if [c == 0, c != 0, s64(c) < 0, s64(c) >= 0][bop]:
                npc = pc + 4 + (off << 2)

        elif op == 0xA:  # JAL
            off = sext((w >> 4) & 0xFFFFFF, 24)
            self._wr(rd, pc + 4)
            npc = pc + 4 + (off << 2)

        elif op == 0xB:  # JALR
            if rb:
                raise ill
            t = (r[ra] + (sext((w >> 12) & 0xFFFF, 16) << 2)) & M64
            if t & 3:
                raise Trap(ECAUSE_MISPC)
            self._wr(rd, pc + 4)
            npc = t

        elif op == 0xC:  # SPG
            ssub, sidx, off8 = rb, (w >> 12) & 0xFF, imm8
            if ssub > 5 or sidx >= 25:
                raise ill
            if ssub == 0:
                if off8 or ra:
                    raise ill
                self._wr(rd, self.s[sidx])
            elif ssub in (1, 2):
                if off8 or rd:
                    raise ill
                self._ws(sidx, r[ra] ^ (self.s[sidx] if ssub == 2 else 0))
            elif ssub == 3:
                if rd or ra or sidx or off8:
                    raise ill
                for i in range(25):
                    self._ws(i, 0)
            else:
                if rd:
                    raise ill
                ea = (r[ra] + (sext(off8, 8) << 3)) & M64
                if ea & 7:
                    raise Trap(ECAUSE_MISMEM)
                if ssub == 4:
                    self._ws(sidx, self.mem.read(ea, 8))
                else:
                    self._mw(ea, 8, self.s[sidx])

        elif op == 0xD:  # GL64 / FP5
            if imm8 or sub > 6:
                raise ill
            if sub == 0:
                self._wr(rd, (gl(r[ra]) * gl(r[rb]) + gl(r[rc])) % P)
            elif sub in (1, 2):
                if rc:
                    raise ill
                self._wr(rd, (gl(r[ra]) + (gl(r[rb]) if sub == 1 else P - gl(r[rb]))) % P)
            elif sub == 3:
                if rb or rc:
                    raise ill
                self._wr(rd, gl_pow7(r[ra]))
            else:
                if rd >= 5 or ra >= 5 or rb >= 5 or rc:
                    raise ill
                a, b = self.s[5 * ra:5 * ra + 5], self.s[5 * rb:5 * rb + 5]
                if sub == 4:
                    o = fp5_mul(a, b)
                elif sub == 5:
                    o = [(gl(x) + gl(y)) % P for x, y in zip(a, b)]
                else:
                    o = [(gl(x) + P - gl(y)) % P for x, y in zip(a, b)]
                for i in range(5):
                    self._ws(5 * rd + i, o[i])

        elif op == 0xE:  # GF128
            if imm8 or sub > 1 or rd >= 12 or ra >= 12 or rb >= 12 or rc:
                raise ill
            a = self.s[2 * ra] | (self.s[2 * ra + 1] << 64)
            b = self.s[2 * rb] | (self.s[2 * rb + 1] << 64)
            o = gf128_mul(a, b) if sub == 0 else a ^ b
            self._ws(2 * rd, o & M64)
            self._ws(2 * rd + 1, o >> 64)

        else:  # 0xF PERM
            if rd or ra or rb or rc or sub > 2:
                raise ill
            if sub == 0:
                if imm8 not in (12, 24):
                    raise ill
                o = keccak_f1600(self.s, imm8)
            elif imm8:
                raise ill
            elif sub == 1:
                o = poseidon2_gl24(self.s[:24]) + self.s[24:]
            else:
                o = poseidon2_gl12(self.s[:12]) + self.s[12:]
            for i in range(25):
                self._ws(i, o[i])

        return npc, ir_over, cy_over, retire, cycle_cost(w)


# --------------------------------------------------------------------------- encoders
def _r4(op, rd=0, ra=0, rb=0, rc=0, sub=0, imm8=0):
    return (op << 28) | ((imm8 & 0xFF) << 20) | ((sub & 0xF) << 16) | ((rc & 0xF) << 12) | \
        ((rb & 0xF) << 8) | ((ra & 0xF) << 4) | (rd & 0xF)


EXC, ERET, ZEROIZE, HALT, NOP = 0, 0x0001_0000, 0x0004_0000, 0x0005_0000, 0x0006_0000


def CSRR(rd, csr): return _r4(0, rd=rd, sub=2, imm8=csr)
def CSRW(ra, csr): return _r4(0, ra=ra, sub=3, imm8=csr)
def LUT4(rd, ra, rb, m): return _r4(1, rd, ra, rb, sub=m)
def ALU(rd, ra, rb, sub): return _r4(2, rd, ra, rb, sub=sub)
def ALUI(rd, ra, imm16, fn): return (3 << 28) | ((imm16 & 0xFFFF) << 12) | (fn << 8) | (ra << 4) | rd
def IMM20(rd, mode, imm20): return (4 << 28) | ((imm20 & 0xFFFFF) << 8) | (mode << 4) | rd
def CMP(rd, ra, rb, flags): return _r4(5, rd, ra, rb, rc=flags)
def SEL(rd, ra, rb, rc): return _r4(6, rd, ra, rb, rc, sub=0)
def BEXT(rd, ra, bidx, blen, signed): return _r4(6, rd, ra, bidx, blen, sub=2 if signed else 1)
def BSWAP64(rd, ra): return _r4(6, rd, ra, sub=3)
def LOAD(rd, ra, simm16, mode): return (7 << 28) | ((simm16 & 0xFFFF) << 12) | (mode << 8) | (ra << 4) | rd
def STORE(rsrc, ra, simm16, mode): return (8 << 28) | ((simm16 & 0xFFFF) << 12) | (mode << 8) | (ra << 4) | rsrc
def BR(rcond, bop, off20): return (9 << 28) | ((off20 & 0xFFFFF) << 8) | (bop << 4) | rcond
def JAL(rd, off24): return (0xA << 28) | ((off24 & 0xFFFFFF) << 4) | rd
def JALR(rd, ra, simm16): return (0xB << 28) | ((simm16 & 0xFFFF) << 12) | (ra << 4) | rd
def SPG(sub, sidx=0, rd=0, ra=0, off8=0): return (0xC << 28) | ((off8 & 0xFF) << 20) | ((sidx & 0xFF) << 12) | (sub << 8) | (ra << 4) | rd
def GL(sub, rd=0, ra=0, rb=0, rc=0): return _r4(0xD, rd, ra, rb, rc, sub=sub)
def GF128(sub, pd, pa, pb): return _r4(0xE, pd, pa, pb, sub=sub)
def PERM(sub, imm8=0): return _r4(0xF, sub=sub, imm8=imm8)


def LI64(rd, v):
    """MOVZ20 + 3x SLK16 (spec ALUI fn 9)."""
    v &= M64
    return [IMM20(rd, 0, (v >> 48) & 0xFFFF), ALUI(rd, rd, (v >> 32) & 0xFFFF, 9),
            ALUI(rd, rd, (v >> 16) & 0xFFFF, 9), ALUI(rd, rd, v & 0xFFFF, 9)]


# --------------------------------------------------------------------------- self test
def selftest():
    import hashlib
    # Keccak-f[1600] x24 on the zero state == SHA3/SHAKE internals; check via SHAKE256("")
    st = [0] * 25
    st[0] ^= 0x1F
    st[16] ^= 1 << 63
    out = keccak_f1600(st, 24)
    sq = b"".join(x.to_bytes(8, "little") for x in out[:17])
    assert sq[:32] == hashlib.shake_256(b"").digest(32), "keccak24"
    # TurboSHAKE256(M = empty, D = 0x1F) first bytes, RFC 9861 test vector
    st = [0] * 25
    st[0] ^= 0x1F
    st[16] ^= 1 << 63
    out = keccak_f1600(st, 12)
    sq = b"".join(x.to_bytes(8, "little") for x in out[:17])
    assert sq[:8].hex() == "367a329dafea871c", sq[:8].hex()
    # Poseidon2 width 12 / 24 canonical KATs (qsag-accel tests)
    k12 = poseidon2_gl12(list(range(12)))
    assert k12 == [
        13782584570844608145, 13136387643152332171, 7171133015474200819,
        7643370872200861694, 14144755201299840503, 16470027036684692562,
        1748465969625202405, 1718729118078964347, 6141020819996733037,
        16322330185628708898, 11650380702735067362, 2734959974607798415,
    ]
    k24 = poseidon2_gl24(list(range(24)))
    assert k24 == [
        9262813872168818283, 14473920968081642809, 3132432025506878070,
        739327372316014541, 13930273445042610257, 9887230855574303117,
        10411529172945029295, 2610146355123527807, 15800955794096892263,
        126337761019280528, 15741922631823646152, 12261346758669164007,
        2093389069744887410, 3165987204040455923, 14526830091420603371,
        2537012170462392522, 17818886402825694850, 14929111493621950133,
        16221575831479706027, 10965213893411960579, 16472025002487739980,
        12534132784495569014, 13110610053613593246, 5468252370409873572,
    ]
    z24 = poseidon2_gl24([0] * 24)
    assert z24[:7] == [17732809615181082052, 5992241717688655734, 5659530038547088535,
                       14879928265562365873, 9090045152854863079, 17692364117337720896,
                       8104590373471715238]
    # Jive Merkle compression KAT (poseidon2_gl24_compress_merkle)
    left, right, tweak = [1, 2, 3, 4, 5, 6, 7], [8, 9, 10, 11, 12, 13, 14], [100, 200]
    st = left + right + tweak + [16, 8, 7, 0x4D52_4B4C_474C_3234 % P, 0, 0, 0, 0x504F_5332_474C_3234 % P]
    m = Ass2([(0, 8)])
    m.s[:] = st + [M64]
    m.mem.write(0, 4, PERM(1))
    m.step()
    assert (m.pc, m.instret, m.cycles, m.s[24]) == (4, 1, 216, M64)
    pm = m.s
    jive = [(pm[i] + left[i] + 2 * right[i] + (4 * tweak[i] if i < 2 else 0)) % P for i in range(7)]
    assert jive == [1170443848852734659, 833485916214919520, 373819593114229865,
                    2500389336842599945, 2668122737528357675, 15131165148025152836,
                    573418327208874869], jive
    # GF(2^128): x * x^127 = x^128 = x^7 + x^2 + x + 1
    assert gf128_mul(2, 1 << 127) == 0x87
    assert gf128_mul(0x87, 1) == 0x87
    # Fp5: u * u^4 = 3
    assert fp5_mul([0, 1, 0, 0, 0], [0, 0, 0, 0, 1]) == [3, 0, 0, 0, 0]
    m = Ass2([(0, 8)])
    m.s[:10] = range(1, 11)
    m.mem.write(0, 4, GL(4, 1, 0, 1))
    m.step()
    assert m.s[:10] == [1, 2, 3, 4, 5, 348, 337, 295, 220, 110]
    assert (m.pc, m.instret, m.cycles) == (4, 1, 104)
    # LI64 round trip through the model
    m = Ass2([(0, 4096)])
    prog = LI64(5, 0xDEAD_BEEF_0123_4567) + [HALT]
    for i, w in enumerate(prog):
        m.mem.write(4 * i, 4, w)
    while m.step():
        pass
    assert m.r[5] == 0xDEAD_BEEF_0123_4567 and m.halted and m.instret == 5 and m.cycles == 5
    print("ass2_model selftest OK", "jive0=%d" % jive[0])


if __name__ == "__main__":
    selftest()
