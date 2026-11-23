#!/usr/bin/env python3
"""Documentation-side reference assembler and VM for ASS2 / Dregg-64.

Implements `ass2-dregg64-canonical-spec.md`: the ISA of sections 1 and 2 and the ASS2-0P5
platform of section 3 (memory map, access rights, the SYS_MMIO fence, the debug CSRs). The listings
printed in the datasheet and the programming guide are assembled and run here.

Python 3 standard library only.
"""
from copy import deepcopy
import re

from p2gl24_rc import POSEIDON2_GL24_RC

M64 = (1 << 64) - 1
P = (1 << 64) - (1 << 32) + 1

# ---------------------------------------------------------------------------------------------
# Reference primitives
# ---------------------------------------------------------------------------------------------
_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
_ROT = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]


def _rol(x, n):
    n &= 63
    return ((x << n) | (x >> (64 - n))) & M64 if n else x


def keccak_p1600(st, rounds):
    """The last `rounds` rounds of Keccak-f[1600] on 25 lanes, lane (x, y) at index x + 5 y."""
    a = list(st)
    for rnd in range(24 - rounds, 24):
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rol(a[x + 5 * y], _ROT[x + 5 * y])
        a = [b[i] ^ ((~b[(i % 5 + 1) % 5 + 5 * (i // 5)]) & b[(i % 5 + 2) % 5 + 5 * (i // 5)]) & M64
             for i in range(25)]
        a[0] ^= _RC[rnd]
    return a


# Width-24 permutation shared with the staged ASS2 cosimulation model.
def gl_pow7(x):
    x %= P
    x2 = x * x % P
    x3 = x2 * x % P
    return x3 * x3 % P * x % P


def _m4(b):
    s = (b[0] + b[1] + b[2] + b[3]) % P
    return [(s + b[i] + 2 * b[(i + 1) % 4]) % P for i in range(4)]


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


def fp5_mul(a, b):
    """Product in F_p[u]/(u^5 - 3), limbs in the power basis."""
    out = [0] * 5
    for i in range(5):
        for j in range(5):
            t = (a[i] % P) * (b[j] % P)
            if i + j >= 5:
                out[i + j - 5] += 3 * t
            else:
                out[i + j] += t
    return [x % P for x in out]


def gf128_mul(a, b):
    """Product in F_2[x]/(x^128 + x^7 + x^2 + x + 1); bit i is the coefficient of x^i."""
    r = 0
    for i in range(128):
        if (b >> i) & 1:
            r ^= a << i
    for i in range(254, 127, -1):
        if (r >> i) & 1:
            r ^= (1 << i) | (0x87 << (i - 128))
    return r & ((1 << 128) - 1)


# ---------------------------------------------------------------------------------------------
# Assembler
# ---------------------------------------------------------------------------------------------
REG = {f"R{i}": i for i in range(16)}
REG.update({"ZERO": 0, "SP": 1, "FP": 2, "RA": 3})
REG.update({f"A{i}": 4 + i for i in range(6)})
REG.update({f"T{i}": 10 + i for i in range(6)})

CSR = {"ARCH_ID": 0x00, "WORD_BITS": 0x01, "EVEC": 0x02, "POWER": 0x03, "INSTRET": 0x04,
       "CYCLES": 0x05, "FEATURES": 0x06, "EPC": 0x08, "ECAUSE": 0x09, "DBG_OUT": 0x0A,
       "DBG_IN": 0x0B, "EXC_EN": 0x3F, "DIT": 0x40, "ZEROIZE": 0x41}

# ASS2-0P5 single-SRAM Two-Ring W^X memory map (Rev. 2.3, canonical spec section 3).
# Ring 0 (`applet_exec = False`): I_ROM (0x0000..0x0FFF) R+X,!W; D_SRAM (0x10000..0x101FF) R+W,!X; SYS_MMIO R+W,!X.
# Ring 3 (`applet_exec = True`):  0x10000..0x100FF R+X,!W (<= 64 words); 0x10100..0x101FF R+W,!X; I_ROM & SYS_MMIO MemFault.
I_ROM, RETIRED_I_SRAM, D_SRAM, SYS_MMIO = 0x0000_0000, 0x0000_1000, 0x0001_0000, 0xFFFF_0000
APPLET_CODE, APPLET_DATA = D_SRAM, D_SRAM + 0x100
RX_MBOX, TX_MBOX = D_SRAM + 0x100, D_SRAM + 0x180
REGIONS = ((I_ROM, 0x1000, "xr"), (D_SRAM, 0x200, "rw"), (SYS_MMIO, 0x80, "rw"))
MMIO = {"FRAM_XFER": 0x00, "FRAM_STATUS": 0x08, "PUF_SYNDROME0": 0x20, "PUF_SYNDROME1": 0x28,
        "PUF_SYNDROME2": 0x30, "PUF_SYNDROME3": 0x38, "TRNG_DATA": 0x40, "TRNG_HEALTH": 0x48,
        "VERDICT_CTRL": 0x60, "GPIO_IO": 0x68, "DBG_UART_DIV": 0x70}
DBG_FIFO_DEPTH = 2          # 10-bit active UART shift register + 1-byte tx_hold_q
HALT_WORD = 0x0005_0000
EXIT_STUB = 0x0FF8          # resident HALT: the return address handed to resident entrypoints
E_BAD_OP, E_LEN, E_CAP, E_LOCKED, E_BUDGET, E_TRAP = 2, 3, 13, 14, 15, 16
# Clock accounting for synchronous ROM fetch, 4B Ring-3 SRAM fetch, byte-serial D-SRAM words and full 512B erasure.
FETCH_ROM, FETCH_SRAM, WORD_SERIAL, SWEEP = 2, 5, 8, 512

CMP_PRED = {"F": 0, "EQ": 1, "GTU": 2, "GEU": 3, "GTS": 6, "GES": 7, "T": 8, "NE": 9,
            "LEU": 10, "LTU": 11, "LES": 14, "LTS": 15}

LUT_ALIAS = {"XOR": 6, "AND": 8, "OR": 14, "XNOR": 9, "ANDN": 4, "NOR": 1, "NAND": 7, "ORN": 13}
ALU_SUB = {"ADD": 0, "SUB": 1, "SHL": 2, "SHR": 3, "ASR": 4, "ROL": 5, "ROR": 6, "MUL64": 7,
           "MULHU64": 8}
ALUI_FN = {"ADDI": 0, "ADDIU": 1, "XORI": 2, "ANDI": 3, "ORI": 4, "SHLI": 5, "SHRI": 6,
           "ASRI": 7, "ROLI": 8, "SLK16": 9}
BR_OP = {"BEQZ": 0, "BNEZ": 1, "BLTZ": 2, "BGEZ": 3}


class AsmError(Exception):
    pass


def _split_operands(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


class Assembler:
    def __init__(self, base=0):
        self.base = base

    def _num(self, tok, labels=None, pc=None, rel=None):
        t = tok.strip().replace("_", "")
        try:
            return int(t, 0)
        except ValueError:
            pass
        if labels is not None and tok.strip() in labels:
            v = labels[tok.strip()]
            if rel is None:
                return v
            d = v - (pc + rel)
            if d % 4:
                raise AsmError(f"label {tok} not word aligned relative to PC")
            return d // 4
        raise AsmError(f"bad number or unknown label: {tok}")

    def _reg(self, tok):
        t = tok.strip().upper()
        if t not in REG:
            raise AsmError(f"bad register: {tok}")
        return REG[t]

    def _lane(self, tok):
        m = re.fullmatch(r"S\[?\s*(\d+)\s*\]?", tok.strip().upper())
        if not m or int(m.group(1)) > 255:
            raise AsmError(f"bad lane: {tok}")
        return int(m.group(1))

    def _idx(self, tok, letter, limit):
        m = re.fullmatch(letter + r"(\d+)", tok.strip().upper())
        if not m or int(m.group(1)) >= limit:
            raise AsmError(f"bad {letter} register: {tok}")
        return int(m.group(1))

    def _mem(self, tok):
        m = re.fullmatch(r"\[\s*(\w+)\s*(?:([+-])\s*(\w+))?\s*\]", tok.strip())
        if not m:
            raise AsmError(f"bad memory operand: {tok}")
        off = int(m.group(3).replace("_", ""), 0) if m.group(3) else 0
        return self._reg(m.group(1)), (-off if m.group(2) == "-" else off)

    @staticmethod
    def _rng(v, lo, hi, what):
        if not lo <= v <= hi:
            raise AsmError(f"{what} out of range: {v}")
        return v

    def _statements(self, text):
        for ln, raw in enumerate(text.splitlines(), 1):
            line = re.split(r";|#|//", raw, maxsplit=1)[0].strip()
            while True:
                m = re.match(r"^([A-Za-z_.][\w.]*):\s*", line)
                if not m:
                    break
                yield ln, "label", m.group(1), []
                line = line[m.end():]
            if not line:
                continue
            parts = line.split(None, 1)
            yield ln, "insn", parts[0].upper(), _split_operands(parts[1]) if len(parts) > 1 else []

    def _size(self, mn, pc):
        if mn == ".WORD64":
            return 8
        if mn == ".ALIGN8":
            return (-pc) % 8
        if mn == "LI64":
            return 16
        return 4

    def assemble(self, text):
        """Returns (bytes, labels, listing); listing rows are (addr, [words], source line no)."""
        labels, pc = {}, self.base
        stmts = list(self._statements(text))
        for ln, kind, mn, ops in stmts:
            if kind == "label":
                if mn in labels:
                    raise AsmError(f"line {ln}: duplicate label {mn}")
                labels[mn] = pc
            else:
                if mn == ".WORD64" and pc % 8:
                    raise AsmError(f"line {ln}: .WORD64 at an address that is not 8-aligned")
                pc += self._size(mn, pc)
        out, listing, pc = bytearray(), [], self.base
        for ln, kind, mn, ops in stmts:
            if kind == "label":
                continue
            try:
                if mn == ".WORD64":
                    v = self._num(ops[0], labels) & M64
                    out += v.to_bytes(8, "little")
                    listing.append((pc, [v & 0xFFFFFFFF, v >> 32], ln))
                    pc += 8
                    continue
                if mn == ".ALIGN8":
                    words = [0x00060000] * (((-pc) % 8) // 4)
                else:
                    words = self._encode(mn, ops, labels, pc)
            except (AsmError, IndexError) as e:
                raise AsmError(f"line {ln}: {mn} {ops}: {e}") from None
            for w in words:
                out += w.to_bytes(4, "little")
            if words:
                listing.append((pc, words, ln))
            pc += 4 * len(words)
        return bytes(out), labels, listing

    def _encode(self, mn, ops, labels, pc):
        r, n, rng = self._reg, self._num, self._rng

        def need(k):
            if len(ops) != k:
                raise AsmError(f"expects {k} operands")

        if mn in ("EXC", "ERET", "ZEROIZE", "HALT", "NOP"):
            need(0)
            return [{"EXC": 0, "ERET": 1, "ZEROIZE": 4, "HALT": 5, "NOP": 6}[mn] << 16]
        if mn in ("CSRR", "CSRW"):
            need(2)
            c = CSR.get(ops[1].strip().upper())
            c = rng(n(ops[1]) if c is None else c, 0, 255, "csr")
            return [(c << 20) | (2 << 16) | r(ops[0])] if mn == "CSRR" else \
                   [(c << 20) | (3 << 16) | (r(ops[0]) << 4)]
        if mn == "LUT4":
            need(4)
            return [(1 << 28) | (rng(n(ops[3]), 0, 15, "M") << 16) | (r(ops[2]) << 8)
                    | (r(ops[1]) << 4) | r(ops[0])]
        if mn in LUT_ALIAS:
            need(3)
            return [(1 << 28) | (LUT_ALIAS[mn] << 16) | (r(ops[2]) << 8) | (r(ops[1]) << 4) | r(ops[0])]
        if mn == "MOV":
            need(2)
            return [(1 << 28) | (12 << 16) | (r(ops[1]) << 4) | r(ops[0])]
        if mn == "NOT":
            need(2)
            return [(1 << 28) | (3 << 16) | (r(ops[1]) << 4) | r(ops[0])]
        if mn in ALU_SUB:
            need(3)
            return [(2 << 28) | (ALU_SUB[mn] << 16) | (r(ops[2]) << 8) | (r(ops[1]) << 4) | r(ops[0])]
        if mn in ALUI_FN:
            need(3)
            fn, v = ALUI_FN[mn], n(ops[2], labels)
            if fn == 0:
                v = rng(v, -32768, 32767, "simm16") & 0xFFFF
            elif fn in (5, 6, 7, 8):
                v = rng(v, 0, 63, "shift")
            else:
                v = rng(v, 0, 0xFFFF, "imm16")
            return [(3 << 28) | (v << 12) | (fn << 8) | (r(ops[1]) << 4) | r(ops[0])]
        if mn in ("MOVZ20", "MOVS20", "AUIPC"):
            need(2)
            if mn == "MOVZ20":
                mode, v = 0, rng(n(ops[1], labels), 0, 0xFFFFF, "imm20")
            elif mn == "MOVS20":
                mode, v = 1, rng(n(ops[1], labels), -(1 << 19), (1 << 19) - 1, "simm20") & 0xFFFFF
            else:
                mode = 2
                v = rng(n(ops[1], labels, pc, 0), -(1 << 19), (1 << 19) - 1, "simm20") & 0xFFFFF
            return [(4 << 28) | (v << 8) | (mode << 4) | r(ops[0])]
        if mn == "LI64":
            need(2)
            v, rd = n(ops[1], labels) & M64, r(ops[0])
            ws = [(4 << 28) | ((v >> 48) << 8) | rd]
            for sh in (32, 16, 0):
                ws.append((3 << 28) | (((v >> sh) & 0xFFFF) << 12) | (9 << 8) | (rd << 4) | rd)
            return ws
        if mn == "CMP":
            need(4)
            f = CMP_PRED.get(ops[3].strip().upper())
            f = rng(n(ops[3]) if f is None else f, 0, 15, "flags4")
            return [(5 << 28) | (f << 12) | (r(ops[2]) << 8) | (r(ops[1]) << 4) | r(ops[0])]
        if mn == "SEL":
            need(4)
            return [(6 << 28) | (r(ops[3]) << 12) | (r(ops[2]) << 8) | (r(ops[1]) << 4) | r(ops[0])]
        if mn in ("BEXTU", "BEXTS"):
            need(4)
            bi, bl = rng(n(ops[2]), 0, 7, "byte_idx"), rng(n(ops[3]), 1, 8, "byte_len")
            return [(6 << 28) | ((1 if mn == "BEXTU" else 2) << 16) | ((bl & 7) << 12) | (bi << 8)
                    | (r(ops[1]) << 4) | r(ops[0])]
        if mn == "BSWAP64":
            need(2)
            return [(6 << 28) | (3 << 16) | (r(ops[1]) << 4) | r(ops[0])]
        if mn in ("LD64", "LDBU"):
            need(2)
            ra, off = self._mem(ops[1])
            if mn == "LD64":
                if off % 8:
                    raise AsmError("LD64 offset must be a multiple of 8")
                off //= 8
            off = rng(off, -32768, 32767, "offset") & 0xFFFF
            return [(7 << 28) | (off << 12) | ((0 if mn == "LD64" else 1) << 8) | (ra << 4) | r(ops[0])]
        if mn in ("ST64", "STB"):
            need(2)
            ra, off = self._mem(ops[0])
            if mn == "ST64":
                if off % 8:
                    raise AsmError("ST64 offset must be a multiple of 8")
                off //= 8
            off = rng(off, -32768, 32767, "offset") & 0xFFFF
            return [(8 << 28) | (off << 12) | ((0 if mn == "ST64" else 1) << 8) | (ra << 4) | r(ops[1])]
        if mn in BR_OP:
            need(2)
            off = rng(n(ops[1], labels, pc, 4), -(1 << 19), (1 << 19) - 1, "off20") & 0xFFFFF
            return [(9 << 28) | (off << 8) | (BR_OP[mn] << 4) | r(ops[0])]
        if mn in ("JAL", "CALL", "J"):
            if mn == "JAL":
                need(2)
                rd, tgt = r(ops[0]), ops[1]
            else:
                need(1)
                rd, tgt = (3 if mn == "CALL" else 0), ops[0]
            off = rng(n(tgt, labels, pc, 4), -(1 << 23), (1 << 23) - 1, "off24") & 0xFFFFFF
            return [(0xA << 28) | (off << 4) | rd]
        if mn == "JALR":
            need(3)
            off = rng(n(ops[2]), -32768, 32767, "simm16") & 0xFFFF
            return [(0xB << 28) | (off << 12) | (r(ops[1]) << 4) | r(ops[0])]
        if mn == "RET":
            need(0)
            return [(0xB << 28) | (3 << 4)]
        if mn == "SGET":
            need(2)
            return [(0xC << 28) | (rng(self._lane(ops[1]), 0, 24, "lane") << 12) | r(ops[0])]
        if mn in ("SPUT", "SXOR"):
            need(2)
            return [(0xC << 28) | (rng(self._lane(ops[0]), 0, 24, "lane") << 12)
                    | ((1 if mn == "SPUT" else 2) << 8) | (r(ops[1]) << 4)]
        if mn == "SZERO":
            need(0)
            return [(0xC << 28) | (3 << 8)]
        if mn in ("SLD64", "SST64"):
            need(2)
            lane_tok, mem_tok = (ops[0], ops[1]) if mn == "SLD64" else (ops[1], ops[0])
            ra, off = self._mem(mem_tok)
            if off % 8:
                raise AsmError("lane load/store offset must be a multiple of 8")
            off = rng(off // 8, -128, 127, "off8") & 0xFF
            return [(0xC << 28) | (off << 20) | (rng(self._lane(lane_tok), 0, 24, "lane") << 12)
                    | ((4 if mn == "SLD64" else 5) << 8) | (ra << 4)]
        if mn == "GL.MAC":
            need(4)
            return [(0xD << 28) | (r(ops[3]) << 12) | (r(ops[2]) << 8) | (r(ops[1]) << 4) | r(ops[0])]
        if mn in ("GL.ADD", "GL.SUB"):
            need(3)
            return [(0xD << 28) | ((1 if mn == "GL.ADD" else 2) << 16) | (r(ops[2]) << 8)
                    | (r(ops[1]) << 4) | r(ops[0])]
        if mn == "GL.SBOX7":
            need(2)
            return [(0xD << 28) | (3 << 16) | (r(ops[1]) << 4) | r(ops[0])]
        if mn in ("FP5.MUL", "FP5.ADD", "FP5.SUB"):
            need(3)
            e = [self._idx(o, "E", 5) for o in ops]
            return [(0xD << 28) | ({"FP5.MUL": 4, "FP5.ADD": 5, "FP5.SUB": 6}[mn] << 16)
                    | (e[2] << 8) | (e[1] << 4) | e[0]]
        if mn in ("GF128.MUL", "GF128.XOR"):
            need(3)
            p = [self._idx(o, "P", 12) for o in ops]
            return [(0xE << 28) | ((0 if mn == "GF128.MUL" else 1) << 16) | (p[2] << 8) | (p[1] << 4) | p[0]]
        if mn == "KECCAK.F1600":
            need(1)
            rounds = n(ops[0])
            if rounds not in (12, 24):
                raise AsmError("rounds must be 12 or 24")
            return [(0xF << 28) | (rounds << 20)]
        if mn == "POSEIDON2.GL24":
            need(0)
            return [(0xF << 28) | (1 << 16)]
        if mn == "POSEIDON2.GL12":
            need(0)
            return [(0xF << 28) | (2 << 16)]
        raise AsmError("unknown mnemonic")


def assemble(text, base=0):
    return Assembler(base).assemble(text)


# ---------------------------------------------------------------------------------------------
# VM
# ---------------------------------------------------------------------------------------------
ILLEGAL, ENVCALL, MISALIGNED_PC, MISALIGNED_MEM, MEMFAULT = 1, 2, 3, 4, 5


class _Trap(Exception):
    def __init__(self, cause):
        self.cause = cause


class DitViolation(Exception):
    pass


def _sx(v, bits):
    return v - (1 << bits) if v >> (bits - 1) else v


def _s64(v):
    return _sx(v & M64, 64)


class Vm:
    """Total operational semantics of the canonical spec, with cycle accounting and a coarse
    taint audit: a secret-tainted value may not decide a branch, a JALR target or an address."""

    def __init__(self, perm24=poseidon2_gl24, perm12=None):
        self.regions = [(base, bytearray(size), rights) for base, size, rights in REGIONS]
        self.mt = {}                 # taint of each 64-bit memory word, by word address
        self.w64(SYS_MMIO + MMIO["DBG_UART_DIV"], 25)   # 1.0 Mbaud at 25 MHz
        self.post_running = False    # cold-boot FIPS POST KAT fences both D_SRAM and SYS_MMIO
        self.applet_exec = False     # Two-Ring Hardware W^X: Ring 0 (False) vs Ring 3 (True)
        self.rom_lock = False        # sticky / gated ROM lock (blocks 0x30 & applet 0x31)
        self.dbg_live = True         # BOOT_MODE = 10 and lifecycle BLANK
        self.dbg_overflow = False
        self.dbg_in = 0              # [8] rx_valid, [7:0] rx_byte
        self.clocks = 0              # core clocks, fetch and memory serialisation included
        self.R = [0] * 16
        self.S = [0] * 25
        self.rt = [False] * 16
        self.st = [False] * 25
        self.pc = 0
        self.halted = False
        self.evec = self.epc = self.ecause = 0
        self.exc_en = 0
        self.instret = self.cycles = 0
        self.dbg = bytearray()
        self.perm24, self.perm12 = perm24, perm12
        self.trace = []

    # memory ---------------------------------------------------------------------------------
    def _span(self, addr, size, right=None):
        """Backing store and offset of [addr, addr + size). A core access names its right."""
        if right is not None and self.applet_exec:
            in_code = APPLET_CODE <= addr and addr + size <= APPLET_CODE + 0x100
            in_data = APPLET_DATA <= addr and addr + size <= APPLET_DATA + 0x100
            allowed = (in_code and right in "xr") or (in_data and right in "rw")
            if not allowed:
                raise _Trap(MEMFAULT)
            store = self.regions[1][1]
            if right == "r" or (right == "w" and size == 8):
                self.clocks += WORD_SERIAL
            return store, addr - D_SRAM
        for base, store, rights in self.regions:
            if base <= addr and addr + size <= base + len(store):
                if right is None or (right in rights and not (
                        self.post_running and base in (D_SRAM, SYS_MMIO))):
                    if base == D_SRAM and (right == "r" or (right == "w" and size == 8)):
                        self.clocks += WORD_SERIAL
                    return store, addr - base
                break
        if right is None:
            raise ValueError(f"{addr:#x}: outside the ASS2-0P5 memory map")
        raise _Trap(MEMFAULT)

    def load(self, addr, data):
        store, off = self._span(addr, len(data))
        store[off:off + len(data)] = data

    def w64(self, addr, v, taint=False):
        self.load(addr, (v & M64).to_bytes(8, "little"))
        if taint is not None:
            self.mt[addr // 8] = taint

    def r64(self, addr):
        store, off = self._span(addr, 8)
        return int.from_bytes(store[off:off + 8], "little")

    def zeroize_sram(self, words=64):
        """Clear the specified number of logical 64-bit words from the start of SRAM0."""
        self.load(D_SRAM, bytes(8 * words))
        for a in range(D_SRAM // 8, D_SRAM // 8 + words):
            self.mt.pop(a, None)

    # registers ------------------------------------------------------------------------------
    def _wr(self, rd, v, taint=False):
        if rd:
            self.R[rd] = v & M64
            self.rt[rd] = taint

    def _csr_read(self, c):
        if c == 0x0B:
            v, self.dbg_in = self.dbg_in, 0
            return v if self.dbg_live else 0
        return {0x00: 0x4153533200000001, 0x01: 64, 0x02: self.evec, 0x04: self.instret,
                0x05: self.cycles, 0x06: 0xF, 0x08: self.epc, 0x09: self.ecause,
                0x3F: self.exc_en, 0x40: 1}.get(c)

    # one instruction ------------------------------------------------------------------------
    def step(self):
        if self.halted:
            return
        pc = self.pc
        skip_ir = skip_cy = False
        cost = 1
        try:
            if pc & 3:
                raise _Trap(MISALIGNED_PC)
            store, off = self._span(pc, 4, "x")
            self.clocks += FETCH_SRAM if self.applet_exec else FETCH_ROM
            w = int.from_bytes(store[off:off + 4], "little")
            op = w >> 28
            rd, ra, rb, rc = w & 15, (w >> 4) & 15, (w >> 8) & 15, (w >> 12) & 15
            sub, imm8 = (w >> 16) & 15, (w >> 20) & 255
            imm16 = (w >> 12) & 0xFFFF
            R, S, rt, st = self.R, self.S, self.rt, self.st
            npc = pc + 4

            def ill(cond=True):
                if cond:
                    raise _Trap(ILLEGAL)

            if op == 0x0:
                if w == 0:
                    if self.exc_en:
                        self.epc, self.ecause, self.exc_en = pc + 4, ENVCALL, 0
                        npc = self.evec
                        skip_ir = True
                elif sub == 1:
                    ill(w & 0x0FF0FFFF)
                    npc, self.exc_en = self.epc & ~3, 1
                elif sub == 2:
                    ill(ra or rb or rc)
                    v = self._csr_read(imm8)
                    ill(v is None)
                    self._wr(rd, v)
                elif sub == 3:
                    ill(rd or rb or rc)
                    v = R[ra]
                    if rt[ra] and imm8 != 0x41:
                        raise DitViolation(f"pc={pc:#x}: secret written to CSR {imm8:#x}")
                    if imm8 == 0x02:
                        ill(self.applet_exec)
                        self.evec = v & ~3 & M64
                    elif imm8 == 0x03:
                        self.halted = bool(v & 1) or self.halted
                    elif imm8 == 0x04:
                        self.instret, skip_ir = v, True
                    elif imm8 == 0x05:
                        self.cycles, skip_cy = v, True
                    elif imm8 == 0x08:
                        self.epc = v
                    elif imm8 == 0x09:
                        self.ecause = v
                    elif imm8 == 0x0A:
                        if self.dbg_live and len(self.dbg) < DBG_FIFO_DEPTH:
                            self.dbg.append(v & 0xFF)
                        elif self.dbg_live:
                            self.dbg_overflow = True
                    elif imm8 == 0x3F:
                        ill(self.applet_exec)
                        self.exc_en = v & 1
                    elif imm8 == 0x41:
                        if v & 1:
                            self._zeroize()
                    else:
                        ill()
                elif sub == 4:
                    ill(w & 0x0FF0FFFF)
                    self._zeroize()
                elif sub == 5:
                    ill(w & 0x0FF0FFFF)
                    self.halted = True
                elif sub == 6:
                    ill(w != 0x00060000)
                else:
                    ill()
            elif op == 0x1:
                ill(rc or imm8)
                a, b, out = R[ra], R[rb], 0
                for idx in range(4):
                    if (sub >> idx) & 1:
                        out |= (a if idx & 2 else ~a) & (b if idx & 1 else ~b)
                self._wr(rd, out, rt[ra] or rt[rb])
            elif op == 0x2:
                ill(rc or imm8 or sub > 8)
                a, b = R[ra], R[rb]
                if sub == 0:
                    v = a + b
                elif sub == 1:
                    v = a - b
                elif sub == 2:
                    v = 0 if b >= 64 else a << b
                elif sub == 3:
                    v = 0 if b >= 64 else a >> b
                elif sub == 4:
                    v = (M64 if a >> 63 else 0) if b >= 64 else _s64(a) >> b
                elif sub == 5:
                    v = _rol(a, b & 63)
                elif sub == 6:
                    v = _rol(a, (64 - (b & 63)) & 63)
                elif sub == 7:
                    v = a * b
                else:
                    v = (a * b) >> 64
                cost = 4 if sub >= 7 else 1
                self._wr(rd, v, rt[ra] or rt[rb])
            elif op == 0x3:
                fn, a = rb, R[ra]
                ill(fn > 9 or (5 <= fn <= 8 and imm16 >> 6))
                k = imm16 & 63
                v = [a + _sx(imm16, 16), a + imm16, a ^ imm16, a & imm16, a | imm16, a << k, a >> k,
                     _s64(a) >> k, _rol(a, k), (a << 16) | imm16][fn]
                self._wr(rd, v, rt[ra])
            elif op == 0x4:
                imm20 = (w >> 8) & 0xFFFFF
                ill(ra > 2)
                self._wr(rd, [imm20, _sx(imm20, 20), pc + (_sx(imm20, 20) << 2)][ra])
            elif op == 0x5:
                ill(sub or imm8)
                a, b, f = R[ra], R[rb], rc
                e = bool(f & 1) and a == b
                g = bool(f & 2) and ((_s64(a) > _s64(b)) if f & 4 else a > b)
                self._wr(rd, int((e or g) != bool(f & 8)), rt[ra] or rt[rb])
            elif op == 0x6:
                ill(imm8 or sub > 3)
                if sub == 0:
                    self._wr(rd, R[ra] if R[rc] == 0 else R[rb], rt[ra] or rt[rb] or rt[rc])
                elif sub in (1, 2):
                    ill(rb >> 3 or rc >> 3)
                    bl = (rc & 7) or 8
                    v = (R[ra] >> (8 * rb)) & ((1 << (8 * bl)) - 1)
                    if sub == 2 and bl < 8:
                        v = _sx(v, 8 * bl)
                    self._wr(rd, v, rt[ra])
                else:
                    ill(rb or rc)
                    self._wr(rd, int.from_bytes(R[ra].to_bytes(8, "little"), "big"), rt[ra])
            elif op == 0x7:
                ill(rb > 1)
                cost = 2
                self._addr(ra, pc)
                if rb == 0:
                    ea = (R[ra] + (_sx(imm16, 16) << 3)) & M64
                    self._span(ea, 8, "r")
                    if ea & 7:
                        raise _Trap(MISALIGNED_MEM)
                    self._wr(rd, self.r64(ea), bool(self.mt.get(ea // 8)))
                else:
                    ea = (R[ra] + _sx(imm16, 16)) & M64
                    store, off = self._span(ea, 1, "r")
                    self._wr(rd, store[off], bool(self.mt.get(ea // 8)))
            elif op == 0x8:
                ill(rb > 1)
                cost = 2
                self._addr(ra, pc)
                if rb == 0:
                    ea = (R[ra] + (_sx(imm16, 16) << 3)) & M64
                    self._span(ea, 8, "w")
                    if ea & 7:
                        raise _Trap(MISALIGNED_MEM)
                    self.w64(ea, R[rd], rt[rd])
                else:
                    ea = (R[ra] + _sx(imm16, 16)) & M64
                    store, off = self._span(ea, 1, "w")
                    store[off] = R[rd] & 0xFF
                    self.mt[ea // 8] = bool(self.mt.get(ea // 8)) or rt[rd]
            elif op == 0x9:
                ill(ra > 3)
                if rt[rd]:
                    raise DitViolation(f"pc={pc:#x}: branch on a secret")
                v = R[rd]
                take = [v == 0, v != 0, _s64(v) < 0, _s64(v) >= 0][ra]
                if take:
                    npc = (pc + 4 + (_sx((w >> 8) & 0xFFFFF, 20) << 2)) & M64
            elif op == 0xA:
                self._wr(rd, pc + 4)
                npc = (pc + 4 + (_sx((w >> 4) & 0xFFFFFF, 24) << 2)) & M64
            elif op == 0xB:
                ill(rb)
                if rt[ra]:
                    raise DitViolation(f"pc={pc:#x}: JALR target is secret")
                t = (R[ra] + (_sx(imm16, 16) << 2)) & M64
                if t & 3:
                    raise _Trap(MISALIGNED_PC)
                self._wr(rd, pc + 4)
                npc = t
            elif op == 0xC:
                sidx, s = (w >> 12) & 0xFF, rb
                ill(s > 5)
                if s == 3:
                    ill(rd or ra or sidx or imm8)
                    self.S, self.st = [0] * 25, [False] * 25
                else:
                    ill(sidx >= 25)
                    if s == 0:
                        ill(imm8 or ra)
                        self._wr(rd, S[sidx], st[sidx])
                    elif s == 1:
                        ill(imm8 or rd)
                        S[sidx], st[sidx] = R[ra], rt[ra]
                    elif s == 2:
                        ill(imm8 or rd)
                        S[sidx] ^= R[ra]
                        st[sidx] = st[sidx] or rt[ra]
                    else:
                        ill(rd)
                        cost = 2
                        self._addr(ra, pc)
                        ea = (R[ra] + (_sx(imm8, 8) << 3)) & M64
                        if ea & 7:
                            raise _Trap(MISALIGNED_MEM)
                        self._span(ea, 8, "r" if s == 4 else "w")
                        if s == 4:
                            S[sidx], st[sidx] = self.r64(ea), bool(self.mt.get(ea // 8))
                        else:
                            self.w64(ea, S[sidx], st[sidx])
            elif op == 0xD:
                ill(imm8 or sub > 6)
                if sub == 0:
                    cost = 4
                    self._wr(rd, ((R[ra] % P) * (R[rb] % P) + R[rc] % P) % P, rt[ra] or rt[rb] or rt[rc])
                elif sub in (1, 2):
                    ill(rc)
                    b = R[rb] % P
                    self._wr(rd, (R[ra] % P + (b if sub == 1 else P - b)) % P, rt[ra] or rt[rb])
                elif sub == 3:
                    ill(rb or rc)
                    cost = 12
                    self._wr(rd, pow(R[ra] % P, 7, P), rt[ra])
                else:
                    ill(rc or rd >= 5 or ra >= 5 or rb >= 5)
                    a, b = S[5 * ra:5 * ra + 5], S[5 * rb:5 * rb + 5]
                    t = any(st[5 * ra:5 * ra + 5]) or any(st[5 * rb:5 * rb + 5])
                    if sub == 4:
                        cost, v = 104, fp5_mul(a, b)
                    elif sub == 5:
                        cost, v = 5, [(x % P + y % P) % P for x, y in zip(a, b)]
                    else:
                        cost, v = 5, [(x % P + P - y % P) % P for x, y in zip(a, b)]
                    S[5 * rd:5 * rd + 5] = v
                    st[5 * rd:5 * rd + 5] = [t] * 5
            elif op == 0xE:
                ill(imm8 or rc or sub > 1 or rd >= 12 or ra >= 12 or rb >= 12)
                a = S[2 * ra] | (S[2 * ra + 1] << 64)
                b = S[2 * rb] | (S[2 * rb + 1] << 64)
                t = st[2 * ra] or st[2 * ra + 1] or st[2 * rb] or st[2 * rb + 1]
                cost, v = (4, gf128_mul(a, b)) if sub == 0 else (1, a ^ b)
                S[2 * rd], S[2 * rd + 1] = v & M64, v >> 64
                st[2 * rd] = st[2 * rd + 1] = t
            else:
                ill(rd or ra or rb or rc or sub > 2)
                if sub == 0:
                    ill(imm8 not in (12, 24))
                    cost = imm8
                    self.S = keccak_p1600(S, imm8)
                    self.st = [any(st)] * 25
                else:
                    ill(imm8)
                    width, fn = (24, self.perm24) if sub == 1 else (12, self.perm12)
                    cost = 216 if sub == 1 else 120
                    if fn is None:
                        raise NotImplementedError("no Poseidon2 permutation supplied to the VM")
                    S[:width] = fn(S[:width])
                    st[:width] = [any(st[:width])] * width
            self.pc = npc
            if not skip_ir:
                self.instret = (self.instret + 1) & M64
        except _Trap as t:
            cost = 1  # Trap-entry cost used by the staged VM and RTL.
            if self.exc_en:
                self.epc, self.ecause, self.exc_en, self.pc = pc, t.cause, 0, self.evec
            else:
                self.halted, self.ecause = True, t.cause
        self.clocks += cost
        if not skip_cy:
            self.cycles = (self.cycles + cost) & M64
        self.trace.append((pc, cost))

    def _addr(self, ra, pc):
        if self.rt[ra]:
            raise DitViolation(f"pc={pc:#x}: memory address depends on a secret")

    def _zeroize(self):
        """Clear both banks and all 512 bytes of SRAM0."""
        self.R = [0] * 16
        self.rt = [False] * 16
        self.S, self.st = [0] * 25, [False] * 25
        self.zeroize_sram()
        self.clocks += SWEEP

    # host command fixtures, Two-Ring Hardware W^X architecture -----------------------------
    def load_code(self, words, lc="BLANK", signed_ok=False, applet_key=(0, 0)):
        """CMD_LOAD_CODE (0x30): open in BLANK, WOTS+C signed in READY/PROVISIONED, E_LOCKED if rom_lock."""
        if self.rom_lock:
            return E_LOCKED
        if not 1 <= len(words) <= 64:
            return E_LEN
        if lc == "BLANK":
            k0, k1, kt = 0, 0, False
        elif lc in ("PROVISIONED", "READY"):
            if not signed_ok:
                return E_CAP
            k0, k1, kt = applet_key[0] & M64, applet_key[1] & M64, True
        else:
            return E_CAP
        self.zeroize_sram()
        self.load(APPLET_CODE, b"".join((w & 0xFFFFFFFF).to_bytes(4, "little") for w in words))
        self.R = [0, k0, k1] + [0] * 13
        self.rt = [False, kt, kt] + [False] * 13
        self.S, self.st = [0] * 25, [False] * 25
        self.evec = self.epc = self.ecause = self.exc_en = 0
        self.applet_exec = True
        self.pc, self.halted = APPLET_CODE, False
        return 0

    def exec(self, entry, payload, budget, cap_ok=True):
        """Exercise a resident I_ROM service at `entry` with the mailbox ABI and 16-bit budget."""
        if len(payload) > 128 or not 0 <= budget <= 0xffff:
            return E_LEN, b"", 0, 0
        if not cap_ok:
            return E_CAP, b"", 0, 0
        self.zeroize_sram()
        self.R, self.rt = [0] * 16, [False] * 16
        self.S, self.st = [0] * 25, [False] * 25
        self.dbg_live = False  # CMD_EXEC runs in READY.
        self.load(RX_MBOX, payload)
        self.R[1], self.R[3] = RX_MBOX, EXIT_STUB
        self.R[4], self.R[5], self.R[6] = RX_MBOX, len(payload), TX_MBOX
        self.load(EXIT_STUB, HALT_WORD.to_bytes(4, "little"))
        self.pc, self.halted = entry, False
        self.exc_en = self.ecause = self.instret = self.cycles = 0
        deadline = self.clocks + (budget or 0xffff)
        err = E_BUDGET
        while self.clocks < deadline:
            # Preview one instruction atomically. An expired watchdog must not commit
            # a store, CSR write, trap, UART byte or software-writable counter.
            trial = deepcopy(self, {id(self.trace): []})
            trial.step()
            if trial.clocks > deadline:
                self.clocks = deadline
                break
            history = self.trace
            history.extend(trial.trace)
            self.__dict__.update(trial.__dict__)
            self.trace = history
            if self.halted:
                err = E_TRAP if self.ecause else E_LEN if self.R[4] > 128 else 0
                break
        n, counters = self.R[4], (self.instret, self.cycles)
        tx = b"" if err else bytes(self._span(TX_MBOX, n)[0][0x180:0x180 + n])
        self._zeroize()
        self.halted = True
        return err, tx, *counters

    def call(self, entry, ret=0x0FFC, max_steps=1_000_000):
        """Run from `entry` with RA = `ret` until PC == `ret` (or the machine halts)."""
        self.R[3], self.rt[3], self.pc = ret, False, entry
        c0, i0 = self.cycles, self.instret
        for _ in range(max_steps):
            if self.halted or self.pc == ret:
                break
            self.step()
        else:
            raise RuntimeError("step limit")
        return self.cycles - c0, self.instret - i0
