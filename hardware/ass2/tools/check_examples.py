#!/usr/bin/env python3
"""Assemble and run the listings of the datasheet on the documentation-side reference VM and compare
each with a reference written independently of the assembly (byte-oriented hashing, schoolbook
polynomial arithmetic). Check cycle counts and listing parity. --listings writes annotated listings.

    python3 -B -I hardware/ass2/tools/check_examples.py [--listings DIR]

Every routine runs inside the ASS2-0P5 single-SRAM W^X memory map: code and constants in immutable
4 KiB mask I_ROM, operands in RX_MBOX or the scratch half of the 512 B D_SRAM, results in TX_MBOX.
"""
import hashlib
import os
import random
from pathlib import Path
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ass2_ref as A  # noqa: E402

EX = os.path.join(HERE, "..", "examples")
P, M64 = A.P, A.M64
rnd = random.Random(0xA552)
CODE, DATA, RX, TX = A.I_ROM, A.D_SRAM, A.RX_MBOX, A.TX_MBOX
ROM_CONST = 0x0E00      # public constants of the resident image: the Canopy tree midstate
STACK_TOP = RX          # the stack grows down from the top of the scratch half
results = []


def src(name):
    with open(os.path.join(EX, name)) as f:
        return f.read()


def fresh(text, base=CODE, **kw):
    img, labels, listing = A.assemble(text, base)
    vm = A.Vm(**kw)
    vm.load(base, img)
    return vm, labels, listing, len(img) // 4


def ok(name, cond, detail=""):
    results.append((name, bool(cond), detail))
    print(f"  {'PASS' if cond else 'FAIL'}  {name}  {detail}")


# ---- primitives against published vectors ---------------------------------------------------
def sponge(rate_state, msg, dsep, rounds, outlen):
    st = list(rate_state)
    blocks = [msg[i:i + 136] for i in range(0, len(msg), 136)] or [b""]
    if len(blocks[-1]) == 136:
        blocks.append(b"")
    for i, blk in enumerate(blocks):
        b = bytearray(136)
        b[:len(blk)] = blk
        if i == len(blocks) - 1:
            b[len(blk)] ^= dsep
            b[135] ^= 0x80
        for j in range(17):
            st[j] ^= int.from_bytes(b[8 * j:8 * j + 8], "little")
        st = A.keccak_p1600(st, rounds)
    out = b""
    while len(out) < outlen:
        out += b"".join(x.to_bytes(8, "little") for x in st[:17])
        if len(out) < outlen:
            st = A.keccak_p1600(st, rounds)
    return out[:outlen]


print("primitives")
for m in (b"", b"abc", bytes(range(200))):
    ok(f"Keccak-f[1600] x24 == hashlib.shake_256 ({len(m)} B)",
       sponge([0] * 25, m, 0x1F, 24, 64) == hashlib.shake_256(m).digest(64))
RFC9861 = bytes.fromhex("367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db"
                        "11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0")
ok("TurboSHAKE256(empty, D=1F, 64) == RFC 9861 vector", sponge([0] * 25, b"", 0x1F, 12, 64) == RFC9861)
x = rnd.getrandbits(128)
ok("GF(2^128): x * 1 == x and x * x^127 * x == reduction identity",
   A.gf128_mul(x, 1) == x and A.gf128_mul(1 << 127, 2) == 0x87)
a5 = [rnd.randrange(P) for _ in range(5)]
ok("Fp5: u^4 * u == 3", A.fp5_mul([0, 0, 0, 0, 1], [0, 1, 0, 0, 0]) == [3, 0, 0, 0, 0]
   and A.fp5_mul(a5, [1, 0, 0, 0, 0]) == a5)

# ---- 1. Fp5 Horner ----------------------------------------------------------------------------
print("fp5_horner.s")
text = src("fp5_horner.s")
# Degrees 0..2 fit RX_MBOX (three 40-byte coefficients); degree 5 uses the 256-byte scratch half.
for d, buf in ((0, RX), (1, RX), (2, RX), (5, DATA)):
    vm, labels, listing, nins = fresh(text, CODE)
    coeffs = [[rnd.randrange(P) for _ in range(5)] for _ in range(d + 1)]
    r = [rnd.randrange(P) for _ in range(5)]
    for i, c in enumerate(coeffs):
        for j, limb in enumerate(c):
            vm.w64(buf + 40 * i + 8 * j, limb, taint=True)
    vm.S[5:10], vm.st[5:10] = r, [True] * 5
    vm.R[4], vm.R[5] = buf + 40 * d, d
    cyc, ins = vm.call(labels["fp5_horner"])
    # reference: sum c_i r^i with explicit powers, not Horner
    acc, pw = [0] * 5, [1, 0, 0, 0, 0]
    for c in coeffs:
        t = A.fp5_mul(c, pw)
        acc = [(x + y) % P for x, y in zip(acc, t)]
        pw = A.fp5_mul(pw, r)
    ok(f"degree {d}: E0 == sum c_i r^i", vm.S[0:5] == acc, f"cycles {cyc} (= 12 + 122*{d}), insns {ins}")
    ok(f"degree {d}: cycle formula", cyc == 12 + 122 * d)
HORNER = (listing, nins)

# ---- 2. Canopy 50-byte node ---------------------------------------------------------------------
print("canopy50_node.s")
TREE_CUSTOM = b"QSAG.ZKHEM2.TREE/v1"


def turbo_midstate(custom):
    blk = bytearray(136)
    blk[0:4] = bytes([1, 136, 1, 0])
    blk[4], blk[5] = 1, 8 * len(custom)
    blk[6:6 + len(custom)] = custom
    st = [int.from_bytes(blk[8 * j:8 * j + 8], "little") for j in range(17)] + [0] * 8
    return A.keccak_p1600(st, 12)


MID = turbo_midstate(TREE_CUSTOM)


def node_ref(idx, left, right):
    buf = bytes([0]) + idx.to_bytes(4, "little") + left + right
    assert len(buf) == 105
    return sponge(MID, buf, 0x07, 12, 50)


def run_node(vm, labels, cur, sib, direction, idx):
    MIDP, CUR, SIB, OUT = ROM_CONST, RX, RX + 0x40, TX
    for j, v in enumerate(MID):
        vm.w64(MIDP + 8 * j, v)
    for base, dg, secret in ((CUR, cur, True), (SIB, sib, False)):
        padded = dg + bytes(6)
        for j in range(7):
            vm.w64(base + 8 * j, int.from_bytes(padded[8 * j:8 * j + 8], "little"), taint=secret)
    vm.R[4:10] = [CUR, SIB, direction, idx, MIDP, OUT]
    vm.R[1] = STACK_TOP
    saved = [0x1122334455667700 + j for j in range(6)]
    vm.R[10:] = saved
    vm.rt[6] = True                       # the direction bit is treated as a secret
    cyc, ins = vm.call(labels["canopy50_node"])
    assert vm.pc == 0x0ffc and vm.R[10:] == saved and vm.R[1] == STACK_TOP
    assert vm.r64(STACK_TOP - 8) == 0
    return b"".join(vm.r64(OUT + 8 * j).to_bytes(8, "little") for j in range(7)), cyc, ins


text = src("canopy50_node.s")
cycles_seen = set()
for trial in range(8):
    vm, labels, listing, nins = fresh(text)
    cur, sib = rnd.randbytes(50), rnd.randbytes(50)
    direction, idx = [0, 1, 0, 0xFFFFFFFFFFFFFFFF][trial % 4], rnd.getrandbits(32)
    out, cyc, ins = run_node(vm, labels, cur, sib, direction, idx)
    cycles_seen.add((cyc, ins))
    want = node_ref(idx, cur, sib) if direction == 0 else node_ref(idx, sib, cur)
    ok(f"trial {trial} dir={direction & 1}: digest == TurboSHAKE256 reference", out[:50] == want and out[50:] == bytes(6))
ok("cycle and instruction count independent of inputs", cycles_seen == {(190, 130)}, str(cycles_seen))
vm, labels, listing, nins = fresh(text)
cur, sib = rnd.randbytes(50), rnd.randbytes(50)
good, _, _ = run_node(vm, labels, cur, sib, 0, 77)
bad_cur = cur[:49] + bytes([cur[49] ^ 1])
vm, labels, _, _ = fresh(text)
bad, _, _ = run_node(vm, labels, bad_cur, sib, 0, 77)
ok("one flipped bit in byte 49 changes the node", good != bad and bad[:50] == node_ref(77, bad_cur, sib))
NODE = (listing, nins, cycles_seen.pop())

# ---- 3. Poseidon2-GL-w24 Jive, staged firmware known-answer vector ---------------------------
print("p2gl24_jive.s")
text = src("p2gl24_jive.s")
for known in (True, False):
    vm, labels, listing, nins = fresh(text, CODE)
    left = list(range(1, 8)) if known else [rnd.randrange(P) for _ in range(7)]
    right = list(range(8, 15)) if known else [rnd.randrange(P) for _ in range(7)]
    tw = [100, 200] if known else [P-1, P-2]
    for i, (l, r) in enumerate(zip(left, right)):
        vm.w64(RX + 8*i, l, taint=True)
        vm.w64(RX + 0x40 + 8*i, r, taint=True)
    vm.R[4:9] = [RX, RX + 0x40, TX, *tw]
    vm.rt[7:9] = [True, True]
    cyc, ins = vm.call(labels["p2gl24_jive"])
    if known:
        # crates/qsag-ass2/tests/common/fixtures.rs::jive_kat
        want = [1170443848852734659, 833485916214919520, 373819593114229865,
                2500389336842599945, 2668122737528357675, 15131165148025152836,
                573418327208874869]
    else:
        state = left + right + tw + [16, 8, 7, 0x4d524b4c474c3234, 0, 0, 0, 0x504f5332474c3234]
        out = A.poseidon2_gl24(state)
        want = [(out[i] + left[i] + 2 * right[i] + (4 * tw[i] if i < 2 else 0)) % P
                for i in range(7)]
    got = [vm.r64(TX + 8*i) for i in range(7)]
    ok("firmware Jive KAT" if known else "Jive with near-modulus tweaks", got == want,
       f"cycles {cyc}, insns {ins}")
    ok("Jive returned in 347 cycles, state scrubbed", vm.pc == 0x0ffc and vm.S == [0] * 25 and (cyc, ins) == (347, 73))
JIVE = (listing, nins, cyc)

# ---- 4. Cut-the-Hash dual MAC -------------------------------------------------------------------
print("cth_dualmac.s")
text = src("cth_dualmac.s")
seen = set()
# Two 48-byte records fit RX_MBOX; five fit the scratch half.
for n, tamper, buf in ((1, False, RX), (2, False, RX), (2, True, RX),
                       (5, False, DATA), (5, True, DATA)):
    vm, labels, listing, nins = fresh(text, CODE)
    r = rnd.getrandbits(128)
    recs = []
    for k in range(n):
        a, z = rnd.getrandbits(128), rnd.getrandbits(128)
        recs.append([a, z, A.gf128_mul(r, z)])
    if tamper:
        recs[n // 2][2] ^= 1 << rnd.randrange(128)
    for k, rec in enumerate(recs):
        for j, v in enumerate(rec):
            vm.w64(buf + 48 * k + 16 * j, v & M64, taint=(j > 0))
            vm.w64(buf + 48 * k + 16 * j + 8, v >> 64, taint=(j > 0))
    vm.S[0], vm.S[1], vm.st[0], vm.st[1] = r & M64, r >> 64, True, True
    vm.R[4], vm.R[5] = buf, n
    cyc, ins = vm.call(labels["cth_dualmac"])
    seen.add((n, cyc))
    ok(f"n={n} tampered={tamper}: verdict", vm.R[4] == (0 if tamper else 1), f"cycles {cyc} (= 13 + 25*{n})")
    ok(f"n={n}: cycle formula, state scrubbed", cyc == 13 + 25 * n and vm.S == [0] * 25)
MAC = (listing, nins)

# ---- encodings quoted in the documents ----------------------------------------------------------
print("encodings")
enc = {
    "EXC": 0, "NOP": 0x00060000, "HALT": 0x00050000, "ERET": 0x00010000, "ZEROIZE": 0x00040000,
    "CSRR A0, CYCLES": 0x00520004, "CSRW T0, EVEC": 0x002300A0,
    "XOR A0, A1, A2": 0x10060654, "ADD A0, A1, A2": 0x20000654, "MUL64 T0, A0, A1": 0x2007054A,
    "ADDI SP, SP, -16": 0x3FFF0011, "SLK16 T0, T0, 0xBEEF": 0x3BEEF9AA, "MOVZ20 T0, 0x12345": 0x4123450A,
    "CMP T0, A0, A1, LTU": 0x5000B54A, "SEL A0, A1, A2, T0": 0x6000A654,
    "LD64 T0, [SP+16]": 0x7000201A, "ST64 [SP+16], T0": 0x8000201A, "RET": 0xB0000030,
    "SGET T0, S[6]": 0xC000600A, "SXOR S[13], T0": 0xC000D2A0, "SLD64 S[24], [A4+192]": 0xC1818480,
    "GL.MAC A0, A1, A2, A3": 0xD0007654, "FP5.MUL E0, E0, E1": 0xD0040100, "GF128.MUL P4, P0, P4": 0xE0000404,
    "FP5.ADD E0, E0, E2": 0xD0050200, "GF128.XOR P4, P4, P4": 0xE0010444,
    "BNEZ A1, -13": 0x9FFFF315, "POSEIDON2.GL12": 0xF0020000,
    "KECCAK.F1600 12": 0xF0C00000, "KECCAK.F1600 24": 0xF1800000, "POSEIDON2.GL24": 0xF0010000,
}
for text_, want in enc.items():
    img, _, _ = A.assemble(text_)
    got = int.from_bytes(img, "little")
    ok(f"{text_:28s} = {want:#010x}", got == want, "" if got == want else f"got {got:#010x}")
img, _, _ = A.assemble("LI64 T0, 0x0123456789ABCDEF")
ws = [int.from_bytes(img[i:i + 4], "little") for i in range(0, 16, 4)]
vm = A.Vm()
vm.load(0, img + (0x00050000).to_bytes(4, "little"))
while not vm.halted:
    vm.step()
ok("LI64 T0, 0x0123456789ABCDEF -> 4 words, 4 cycles", vm.R[10] == 0x0123456789ABCDEF and vm.cycles == 5
   and ws == [0x4001230a, 0x345679aa, 0x389ab9aa, 0x3cdef9aa],
   " ".join(f"{w:08x}" for w in ws))
vm = A.Vm()
vm.step()
ok("all-zero memory with EXC_EN = 0: EXC falls through", vm.pc == 4 and not vm.halted)
vm = A.Vm()
vm.evec, vm.exc_en = 0x100, 1
vm.step()
ok("enabled EXC saves continuation without retiring",
   (vm.epc, vm.ecause, vm.exc_en, vm.pc, vm.instret, vm.cycles) == (4, 2, 0, 0x100, 0, 1))
vm = A.Vm()
vm.R[4] = 1
vm.load(0, A.assemble("LD64 A0, [A0]")[0])
vm.step()
ok("misaligned load takes fault-entry cost without retirement",
   (vm.halted, vm.ecause, vm.instret, vm.cycles, vm.R[4]) == (True, 4, 0, 1, 1))
vm = A.Vm()
vm.load(0, (0x1FF00000).to_bytes(4, "little"))
vm.step()
ok("reserved field set, EXC_EN = 0: halts with ECAUSE = 1", vm.halted and vm.ecause == 1)

# ---- ASS2-0P5 platform: memory map, rights, fence, debug CSRs ------------------------------------
print("platform")


def run(text, base=CODE, setup=None, steps=64):
    vm, labels, _, _ = fresh(text, base)
    if setup:
        setup(vm)
    vm.pc = base
    for _ in range(steps):
        if vm.halted:
            break
        vm.step()
    return vm


LI_MMIO = "MOVZ20 T0, 0xFFFF\nSHLI T0, T0, 16\n"       # T0 = 0xFFFF_0000
vm = run(LI_MMIO + "LD64 A0, [T0+0x70]\nMOVZ20 A1, 1\nST64 [T0+0x60], A1\nLD64 A2, [T0+0x60]\nHALT")
ok("I_ROM code reads DBG_UART_DIV = 25 and writes VERDICT_CTRL",
   (vm.R[4], vm.R[6], vm.ecause) == (25, 1, 0))
vm = run(LI_MMIO + "LD64 A0, [T0+0x70]\nHALT", setup=lambda v: setattr(v, "post_running", True))
ok("cold-boot POST KAT: SYS_MMIO read is fenced, MemFault", (vm.halted, vm.ecause, vm.R[4]) == (True, 5, 0))
vm = run("MOVZ20 T0, 0x10000\nLD64 A0, [T0+0]\nHALT", setup=lambda v: setattr(v, "post_running", True))
ok("cold-boot POST KAT: D_SRAM access is fenced while scrub runs, MemFault", (vm.halted, vm.ecause) == (True, 5))
vm = run("MOVZ20 T0, 0x1000\nJALR ZERO, T0, 0")
ok("fetch from retired 0x0000_1000 (former I_SRAM): MemFault", (vm.ecause, vm.pc) == (5, A.RETIRED_I_SRAM))
vm = run("MOVZ20 T0, 0x1000\nST64 [T0+0], T0\nHALT")
ok("store to retired 0x0000_1000: MemFault", vm.ecause == 5)
vm = run("ST64 [ZERO+0x800], SP\nHALT")
ok("store to I_ROM: MemFault", vm.ecause == 5)
vm = run("MOVZ20 T0, 0x10000\nJALR ZERO, T0, 0")
ok("fetch from D_SRAM: MemFault (strict hardware W^X)", (vm.ecause, vm.pc) == (5, A.D_SRAM))
for name, addr in (("above D_SRAM", A.D_SRAM + 0x200), ("above I_ROM", A.I_ROM + 0x1000),
                   ("above SYS_MMIO", A.SYS_MMIO + 0x80), ("old mailbox window", 0x20000)):
    vm = run("LD64 A0, [T0+0]\nHALT", setup=lambda v: v.R.__setitem__(10, addr))
    ok(f"unmapped load, {name}: MemFault", vm.ecause == 5)
vm = run("MOVZ20 T0, 0x101F8\nMOVZ20 A0, 0x5A\nST64 [T0+0], A0\nLD64 A1, [T0+0]\nLDBU A2, [T0+0]\nHALT")
ok("last D_SRAM word (TX_MBOX top) loads and stores", (vm.R[5], vm.R[6], vm.ecause) == (0x5A, 0x5A, 0))
vm = run("LD64 A0, [ZERO+0xE00]\nHALT", setup=lambda v: v.w64(ROM_CONST, 0xC0FFEE))
ok("I_ROM constants are readable data", vm.R[4] == 0xC0FFEE and vm.ecause == 0)
vm = A.Vm()
for a in range(A.D_SRAM, A.D_SRAM + 0x200, 8):
    vm.w64(a, M64, taint=True)
vm.zeroize_sram(48)
ok("48-word sweep clears scratch and RX_MBOX, keeps TX_MBOX",
   all(vm.r64(a) == 0 for a in range(DATA, TX, 8)) and all(vm.r64(a) == M64 for a in range(TX, TX + 0x80, 8)))
vm.zeroize_sram()
ok("64-word sweep clears all of D_SRAM", all(vm.r64(a) == 0 for a in range(DATA, DATA + 0x200, 8)))
many = "MOVZ20 A0, 0x41\n" + "CSRW A0, DBG_OUT\n" * 4 + "CSRR A1, DBG_IN\nCSRR A2, DBG_IN\nHALT"
vm = run(many, setup=lambda v: setattr(v, "dbg_in", 0x155))
ok("DBG_OUT: shift+1-byte hold buffer accepts 2 back-to-back bytes, sets overflow on 3rd",
   (bytes(vm.dbg), vm.dbg_overflow, vm.cycles) == (b"AA", True, 8))
ok("DBG_IN: [8] rx_valid, [7:0] byte, cleared by the read", (vm.R[5], vm.R[6]) == (0x155, 0))
vm = run(many, setup=lambda v: (setattr(v, "dbg_live", False), setattr(v, "dbg_in", 0x155)))
ok("DBG_OUT muted outside BOOT_MODE = 10 / BLANK: same cycles, no output, DBG_IN reads 0",
   (bytes(vm.dbg), vm.dbg_overflow, vm.cycles, vm.R[5]) == (b"", False, 8, 0))
total_ex_words = sum(len(A.assemble(src(n + ".s"))[0]) // 4
                     for n in ("fp5_horner", "cth_dualmac", "p2gl24_jive", "canopy50_node"))
ok("all four crypto kernels fit comfortably inside 1,024-word I_ROM", total_ex_words < 512, f"{total_ex_words} words")

# ---- Two-Ring Hardware W^X CMD_LOAD_CODE (0x30) and resident I_ROM CMD_EXEC (0x31) ----------------
print("exec")
SERVICE_ENTRY = 0x0200
SERVICE = """
    LD64    A3, [A0+0x38]       ; tweak t0: the pad word after the left child
    LD64    A4, [A0+0x78]       ; tweak t1: the pad word after the right child
    ADDI    A1, A0, 0x40        ; right child
    CALL    p2gl24_jive         ; A0 = RX_MBOX and A2 = TX_MBOX on entry
    MOVZ20  A0, 56              ; response length in bytes
    HALT
""" + src("p2gl24_jive.s")
img, _, _ = A.assemble(SERVICE, SERVICE_ENTRY)
payload = b"".join(v.to_bytes(8, "little") for v in [*range(1, 8), 100, *range(8, 15), 200])
JIVE_KAT = [1170443848852734659, 833485916214919520, 373819593114229865, 2500389336842599945,
            2668122737528357675, 15131165148025152836, 573418327208874869]
vm_r3 = A.Vm()
ok("0x30 >64 words rejected with E_LEN", vm_r3.load_code([A.HALT_WORD] * 65) == A.E_LEN)
ok("0x30 in READY without WOTS+C signature rejected with E_CAP",
   vm_r3.load_code([A.HALT_WORD], lc="READY", signed_ok=False) == A.E_CAP)
ok("0x30 in READY with WOTS+C signature injects applet_key in R1..R2 & scrubs R3..R15/S",
   vm_r3.load_code([A.HALT_WORD], lc="READY", signed_ok=True, applet_key=(11, 22)) == 0
   and (vm_r3.applet_exec, vm_r3.R[1], vm_r3.R[2], vm_r3.R[3:]) == (True, 11, 22, [0] * 13))
vm_r3.rom_lock = True
ok("0x30 under rom_lock hard-rejected with E_LOCKED",
   vm_r3.load_code([A.HALT_WORD], lc="READY", signed_ok=True) == A.E_LOCKED)
vm = A.Vm()
vm.load(SERVICE_ENTRY, img)
ok("EXEC without valid capability tag: E_CAP", vm.exec(SERVICE_ENTRY, payload, 1000, cap_ok=False)[0] == A.E_CAP)
err, tx, instret, cycles = vm.exec(SERVICE_ENTRY, payload, 65535)
ok("EXEC resident Jive service: seven KAT limbs from TX_MBOX, INSTRET 79, CYCLES 355",
   (err, tx, instret, cycles) == (0, b"".join(v.to_bytes(8, "little") for v in JIVE_KAT), 79, 355))
ok("exit: response captured before all 512 bytes are swept",
   vm.R == [0] * 16 and vm.S == [0] * 25 and all(vm.r64(a) == 0 for a in range(DATA, TX, 8))
   and all(vm.r64(a) == 0 for a in range(TX, TX + 128, 8)))
err, tx, instret, cycles = vm.exec(SERVICE_ENTRY, payload, 2)
ok("EXEC, two clocks cannot retire the first 11-clock LD64",
   (err, tx, instret, cycles) == (A.E_BUDGET, b"", 0, 0))
ok("E_BUDGET exit sweeps all 64 words", all(vm.r64(a) == 0 for a in range(DATA, DATA + 0x200, 8)))
vm.load(SERVICE_ENTRY, A.assemble("MOVZ20 T0, 0x1000\nLD64 A0, [T0+0]\nHALT", SERVICE_ENTRY)[0])
err, tx, instret, cycles = vm.exec(SERVICE_ENTRY, b"", 100)
ok("unmapped load traps cleanly: E_TRAP, ECAUSE 5, one instruction retired",
   (err, tx, instret, cycles, vm.ecause) == (A.E_TRAP, b"", 1, 2, 5))
vm.load(SERVICE_ENTRY, A.assemble("LDBU A3, [A0+0]\nSTB [A2+0], A3\nMOVZ20 A0, 1\nRET", SERVICE_ENTRY)[0])
ok("RET to the resident exit stub ends the service like HALT", vm.exec(SERVICE_ENTRY, b"Z", 100) == (0, b"Z", 5, 7))
vm.load(SERVICE_ENTRY, b"".join(w.to_bytes(4, "little") for w in (0x40008104, A.HALT_WORD)))  # MOVZ20 A0, 129; HALT
ok("response longer than TX_MBOX: E_LEN", vm.exec(SERVICE_ENTRY, b"", 100)[0] == A.E_LEN)

# One I_ROM NOP fetches in 2 clocks and executes in 1 clock (3 core clocks).
vm.load(SERVICE_ENTRY, b"".join(w.to_bytes(4, "little") for w in (0x00060000, A.HALT_WORD)))
ok("watchdog stops exactly after a complete 3-clock I-ROM NOP", vm.exec(SERVICE_ENTRY, b"", 3) == (A.E_BUDGET, b"", 1, 1))
vm.load(SERVICE_ENTRY, b"".join(w.to_bytes(4, "little") for w in (0x40000004, A.HALT_WORD)))  # MOVZ20 A0, 0; HALT
ok("zero budget selects 65,535 core clocks", vm.exec(SERVICE_ENTRY, b"", 0) == (0, b"", 2, 2))
vm = A.Vm()
vm.load(A.D_SRAM, bytes([0xa5]) * 512)
vm.load(0, A.assemble("ZEROIZE")[0])
vm.step()
ok("ZEROIZE clears all 512 bytes including TX_MBOX", bytes(vm.regions[1][1]) == bytes(512))
ok("full wipe costs 512 byte-write clocks plus fetch and instruction", vm.clocks == 515)

# ---- reference clock model for resident I_ROM routines ------------------------------------------
print("clocks")


def clocks(name, setup, base=CODE):
    vm, labels, _, _ = fresh(src(name + ".s"), base)
    setup(vm)
    c0 = vm.clocks
    cyc, ins = vm.call(labels[name])
    return cyc, ins, vm.clocks - c0


def horner_args(d):
    return lambda v: v.R.__setitem__(slice(4, 6), [DATA + 40 * d, d])


def canopy_args(v):
    v.R[4:10] = [RX, RX + 0x40, 0, 0, ROM_CONST, TX]
    v.R[1] = STACK_TOP


CLOCKS = {
    "fp5_horner d=0": clocks("fp5_horner", horner_args(0)),
    "fp5_horner d=5": clocks("fp5_horner", horner_args(5)),
    "cth_dualmac n=2": clocks("cth_dualmac", lambda v: v.R.__setitem__(slice(4, 6), [RX, 2])),
    "p2gl24_jive": clocks("p2gl24_jive", lambda v: v.R.__setitem__(slice(4, 7), [RX, RX + 0x40, TX])),
    "canopy50_node": clocks("canopy50_node", canopy_args),
}
for k, v in CLOCKS.items():
    print(f"  {k}: cycles {v[0]}, instructions {v[1]}, core clocks {v[2]}")
WANT = {"fp5_horner d=0": 12 + 7*2 + 5*8, "fp5_horner d=5": 622 + 57*2 + 30*8,
        "cth_dualmac n=2": 63 + 36*2 + 12*8, "p2gl24_jive": 347 + 73*2 + 35*8,
        "canopy50_node": 190 + 130*2 + 24*8}
ok("byte-port timing model reproduces the routine clock counts", {k: v[2] for k, v in CLOCKS.items()} == WANT, str(WANT))

# ---- DIT audit has teeth --------------------------------------------------------------------------
print("audit")
img, labels, _ = A.assemble("LD64 T0, [A0+0]\nBNEZ T0, 8\nNOP\nHALT")
vm = A.Vm()
vm.load(0, img)
vm.w64(DATA, 1, taint=True)
vm.R[4] = DATA
try:
    while not vm.halted:
        vm.step()
    ok("a branch on a secret is reported by the audit", False)
except A.DitViolation:
    ok("a branch on a secret is reported by the audit", True)

# ---- listings -------------------------------------------------------------------------------------
# Normal runs compare fresh output to the shipped listings. --listings writes a new set.
generate = "--listings" in sys.argv
out_dir = (Path(sys.argv[sys.argv.index("--listings") + 1]) if generate else
           Path(__file__).resolve().parents[3] / "build/listings")
if generate:
    out_dir.mkdir(parents=True, exist_ok=True)
for name in ("fp5_horner", "canopy50_node", "p2gl24_jive", "cth_dualmac"):
    source = src(name + ".s")
    _, _, listing = A.assemble(source, CODE)
    by_line = {ln: (addr, words) for addr, words, ln in listing}
    lines = []
    for i, line in enumerate(source.splitlines(), 1):
        prefix = " " * 14
        if i in by_line:
            addr, words = by_line[i]
            prefix = f"{addr:04x}  " + " ".join(f"{w:08x}" for w in words)
        lines.append(f"{prefix}  {line}\n")
    expected = "".join(lines).encode("utf-8")
    path = out_dir / (name + ".lst")
    if generate:
        path.write_bytes(expected)
    else:
        ok(name + ".lst matches fresh assembly", path.is_file() and path.read_bytes() == expected)

print()
print(f"instructions: horner {HORNER[1]}, node {NODE[1]} ({NODE[2][0]} cycles), jive {JIVE[1]} ({JIVE[2]} cycles), mac {MAC[1]}")
bad = [r for r in results if not r[1]]
print(f"{len(results) - len(bad)} of {len(results)} checks passed")
sys.exit(1 if bad else 0)
