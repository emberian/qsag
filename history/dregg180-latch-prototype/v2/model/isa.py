"""Dregg-180 v2 micro-instruction set: field layout, operation tables, row map.

One micro-word is 28 bits:

    [27:23] op    operation
    [22:16] A     source row | function code | condition | constant index | immediate bits [13:7]
    [15:9]  B     destination row | immediate bits [6:0] | branch target [10:4]
    [8:5]   fn    flags (bit 0 = W: store H to row B; bit 1 = I: operand is the immediate) |
                  immediate bits [15:14] in fn[3:2] | branch target [3:0]
                  CMP: bit 0 = tag compare (CMPT).  PUSH: bit 0 = release (REL), bit 1 = source is H.
                  KMOV: bit 0 = the source is word A of the PUF response (PMOV).
    [4]     ia    row A is indexed: A + X (mod 128)
    [3]     ib    row B is indexed: B + X (mod 128)
    [2]     xi    X is incremented after the instruction
    [1:0]   seq   0 = next, 1 = return after this instruction

`H` is the 64-bit hold register of the register file's write path; it is also the accumulator of
the word unit. Every data instruction computes H' = f(H, operand) and may store H' to one row.
"""

WIDTH = 28
M64 = (1 << 64) - 1
M32 = (1 << 32) - 1

OPS = ["NOP", "LD", "XOR", "AND", "OR", "ADD", "SUB", "CMP", "UN", "DIN", "LDF", "LDC", "PUSH", "HDR", "FAIL",
       "KMOV", "KEYWR", "CTL", "WIPE", "KEC", "FLD", "FADD", "FRAM", "SETX", "SETC", "BR", "BXNE", "DBNZ",
       "CALL", "DISP", "END", "ILL"]
OP = {n: i for i, n in enumerate(OPS)}
ALU2 = ("LD", "XOR", "AND", "OR", "ADD", "SUB", "CMP")      # operand: row A or imm16
BRANCH = ("BR", "BXNE", "DBNZ", "CALL")                     # target in {B, fn}

UN = ["ID", "NIB", "BE32", "HSWAP", "LO32", "HI32", "SHR1", "SHR4", "SHR8", "SHR16", "SHL1", "SHL4", "SHL8",
      "XT", "SHL1C"]      # XT: multiply by x in GF(2^64); SHL1C: shift left 1, carry = the bit shifted out
# CTL: codes 1 and 6 were SETKV and NONCE in stage 1. LC and SYNW take a small operand in field B.
CTL = ["CLRZ", "LC", "SETFM", "SETFA", "VOK", "AUTH", "ZKEY", "PUFE", "PUFR", "SYNW", "TSEL", "TRUN", "TCLR", "TARM"]
CTL_ARG = ("LC", "SYNW")
CTL_KEY = ("LC", "AUTH", "PUFE", "PUFR", "SYNW")          # decode only in the key range
# LDF: codes 9..11 were NONCE0, NONCE1, KATTR in stage 1.
LDF = ["HDRW", "FLAGS", "LEN", "NWORDS", "ARG", "ARGLO", "ARGHI", "X", "STATUS", "LC", "SYN0", "SYN1", "PNOISE",
       "TS1", "TS4", "TSUM", "TFLAGS", "TRAW"]
FLD = ["PERM", "RED"]
FRAM = ["RSTART", "WSTART", "RWORD", "WWORD", "DONE"]
COND = ["AL", "Z", "NZ", "CY", "NC", "HZ", "HNZ", "MORE", "NOMORE", "KV", "NKV", "C1Z", "C1NZ"]
KEC = {"24": 0, "12": 1}

W_LANES_LO, W_LANES_HI, W_SCRATCH, W_OUT = 1, 2, 4, 8       # WIPE mask bits

# ---------------------------------------------------------------- hardwired sequencer constants
# These are constants of the decoder, not data of the ROM image. The assembler lays the image out to
# match them (.org) and romcheck.py fails an image that does not.
IDLE_ADDR = 0                       # the one DISP
KEY_LO, KEY_HI = 1, 79              # key range: KEYWR, PMOV and the CTL functions of CTL_KEY decode only here
REC_LO, REC_HI = 80, 287            # record range: FRAM instructions and writes of state rows decode only here
ROM_BASE = 288                      # everything else
END_CLOCKS = 3                      # END: decode, pad and wipe, return to idle
STACK_DEPTH = 4                     # return stack entries
# lifecycle states (ARCHITECTURE.md 3.2): a register of the sequencer, written by CTL LC in the key range
LC = ["RESET", "BLANK", "ORPHAN", "LEASE", "READY", "LOCKED"]
LC_RESET, LC_BLANK, LC_ORPHAN, LC_LEASE, LC_READY, LC_LOCKED = range(6)
LC_ANY = (1 << len(LC)) - 1
LCMASK = {n.lower(): 1 << i for i, n in enumerate(LC)}      # dispatch-table entry: the states a command decodes in
LCMASK["any"] = LC_ANY
E_MAGIC, E_OPCODE, E_LEN, E_NOKEY, E_STATE = 1, 2, 3, 4, 14    # error codes the hardware itself issues
FRAM_REC_WORDS = 16                 # one FRAM record: 16 words at byte address 128 * index; index 0..2

# ---------------------------------------------------------------- register-file row map
N_LANES, N_KWORK, N_SCRATCH, N_KEYS, N_PINS, N_STATE, N_OUT = 25, 7, 24, 4, 0, 10, 2
LANE0 = 0
KWORK0 = LANE0 + N_LANES          # 25
SCRATCH0 = KWORK0 + N_KWORK       # 32
KEY0 = SCRATCH0 + N_SCRATCH       # 44
PIN0 = KEY0 + N_KEYS              # 54
STATE0 = PIN0 + N_PINS            # 60
OUT0 = STATE0 + N_STATE           # 70
ROWS_S = OUT0 + N_OUT             # 72
ROWS_L = 128                      # rows 72..127: challenge rows (configuration L)
RATE_LANES = 17                   # SHAKE256 / TurboSHAKE256 rate, in lanes
FRAM_LANES = (LANE0, LANE0 + 1)   # FRAM WWORD may send a state row, or the record tag in these lanes


def row_class(r, nrows=ROWS_S):
    if r < 0 or r >= nrows:
        return "none"
    if r < KWORK0:
        return "lane"
    if r < SCRATCH0:
        return "kwork"
    if r < KEY0:
        return "scratch"
    if r < PIN0:
        return "key"
    if r < STATE0:
        return "pin"
    if r < OUT0:
        return "state"
    if r < ROWS_S:
        return "out"
    return "chal"


def row_symbols():
    s = {}
    for i in range(N_LANES):
        s[f"l{i}"] = LANE0 + i
    s["lm1"] = 127                # with +X: lane X - 1
    for i in range(N_SCRATCH):
        s[f"t{i}"] = SCRATCH0 + i
    for i in range(N_KEYS):
        s[f"k_dev{i}"] = KEY0 + i
    for i in range(N_PINS):
        s[f"pin{i}"] = PIN0 + i
    for i in range(N_STATE):
        s[f"st{i}"] = STATE0 + i
    for i in range(N_OUT):
        s[f"out{i}"] = OUT0 + i
    for i in range(ROWS_L - ROWS_S):
        s[f"c{i}"] = ROWS_S + i
    return s


# ---------------------------------------------------------------- encoding
def encode(op, a=0, b=0, fn=0, ia=0, ib=0, xi=0, seq=0):
    assert 0 <= op < 32 and 0 <= a < 128 and 0 <= b < 128 and 0 <= fn < 16 and seq < 4
    return (op << 23) | (a << 16) | (b << 9) | (fn << 5) | (ia << 4) | (ib << 3) | (xi << 2) | seq


def decode(w):
    assert 0 <= w < (1 << WIDTH)
    return dict(op=w >> 23, a=(w >> 16) & 127, b=(w >> 9) & 127, fn=(w >> 5) & 15, ia=(w >> 4) & 1, ib=(w >> 3) & 1,
                xi=(w >> 2) & 1, seq=w & 3)


def imm16(d):
    return ((d["fn"] >> 2) << 14) | (d["a"] << 7) | d["b"]


def imm_fields(v):
    assert 0 <= v < (1 << 16), v
    return (v >> 7) & 127, v & 127, (v >> 14) << 2          # a, b, fn[3:2]


def target(d):
    return (d["b"] << 4) | d["fn"]


def target_fields(t):
    assert 0 <= t < (1 << 11), t
    return t >> 4, t & 15                                   # b, fn
