#!/usr/bin/env python3
"""Generate replayable instruction-level ASS2 traces. Numeric fields are hexadecimal."""
import argparse
from dataclasses import asdict
import json
from pathlib import Path
import random
import sys

import ass2_model as m

SIZE, DATA, HANDLER = 8192, 4096, 2048
EDGE = (0, 1, 63, 64, 65, 1 << 63, m.P - 1, m.P, m.M64)
# The Rust VM charges one architectural cycle for a fault; EXC has its own rule.
PROFILE = m.Knobs()


def words(seq):
    return b"".join(x.to_bytes(4, "little") for x in seq)


def program(case, rng):
    # Execute all setup on the DUT. R14 points into the middle of the data image.
    base = DATA + 128
    data = bytes(rng.getrandbits(8) for _ in range(256))
    p = [m.IMM20(14, 0, base)]
    for reg in range(1, 5):
        value = rng.choice(EDGE) if reg == 3 else rng.getrandbits(64)
        p.extend(m.LI64(reg, value))
    # Exercise both shift boundaries and arithmetic signs in the directed prefix.
    count = (0, 1, 63, 64, 65, m.M64)[(case // 9) % 6]
    p.extend(m.LI64(5, count))
    p.extend([m.ALU(6, 1, 5, case % 9), m.LUT4(7, 1, 2, case % 16),
              m.CMP(8, 1, 1 if case & 16 else 2, case % 16)])
    for i in range(25):
        p.append(m.SPG(4, i, ra=14, off8=i-16))
    # The random body retains live dependencies, including writes to R0.
    for _ in range(rng.randrange(6, 19)):
        rd, ra, rb = (rng.randrange(14) for _ in range(3))
        choice = rng.randrange(6)
        if choice == 0:
            w = m.ALU(rd, ra, rb, rng.randrange(9))
        elif choice == 1:
            w = m.LUT4(rd, ra, rb, rng.randrange(16))
        elif choice == 2:
            w = m.CMP(rd, ra, rb, rng.randrange(16))
        elif choice == 3:
            w = m.SEL(rd, ra, rb, rng.randrange(14))
        elif choice == 4:
            w = m.GL(0, rd, ra, rb, rng.randrange(14))
        else:
            w = m.SPG(2, rng.randrange(25), ra=ra)
        p.append(w)

    fn = case % 10
    imm = rng.randrange(64 if 5 <= fn <= 8 else 65536)
    p.extend([m.ALUI(7, 1, imm, fn), m.IMM20(8, case % 3, rng.getrandbits(20)),
              m.BEXT(6, 2, case % 8, (case // 8) % 8, (case // 64) % 2),
              m.BSWAP64(9, 1), m.SEL(10, 1, 2, case % 4)])
    off = rng.randrange(-12, 12)
    p.extend([m.STORE(1, 14, off, 0), m.LOAD(6, 14, off, 0),
              m.STORE(2, 14, off * 8 + case % 8, 1),
              m.LOAD(7, 14, off * 8 + case % 8, 1),
              m.SPG(1, case % 25, ra=1), m.SPG(2, case % 25, ra=2),
              m.SPG(0, case % 25, rd=6), m.SPG(5, case % 25, ra=14, off8=off)])
    sub = case % 4
    p.append(m.GL(sub, 6, 1, 2 if sub != 3 else 0, 3 if sub == 0 else 0))
    ea, eb = rng.sample(range(5), 2)
    pa, pb = rng.sample(range(12), 2)
    p.extend([m.GL(4 + case % 3, (ea, eb)[case % 2], ea, eb),
              m.GF128(case % 2, (pa, pb)[(case // 2) % 2], pa, pb)])
    perm = (m.PERM(0, 12), m.PERM(0, 24), m.PERM(1), m.PERM(2))[case % 4]
    p.extend([perm, m.BR(case % 2, case % 4, 1), m.NOP, m.JAL(10, 1), m.HALT])
    target = 4 * (len(p) + 3)
    p.extend([m.IMM20(11, 0, target + 4), m.JALR(11, 11, -1), m.HALT])
    # Backward conditional displacement, taken once and untaken once.
    p.extend([m.IMM20(5, 0, 2), m.ALUI(5, 5, -1, 0), m.BR(5, 1, -2)])
    p.extend([m.CSRW(1, m.CSR_INSTRET), m.CSRW(2, m.CSR_CYCLES),
              m.CSRR(6, m.CSR_INSTRET), m.CSRR(7, m.CSR_CYCLES),
              m.CSRR(8, (0, 1, 2, 6, 8, 9, 63, 64)[case % 8])])
    end = case % 18
    handler = [m.CSRR(12, m.CSR_EPC), m.CSRR(13, m.CSR_ECAUSE)]
    if end in (0, 1):
        p += [m.IMM20(6, 0, HANDLER + 3), m.CSRW(6, m.CSR_EVEC),
              m.IMM20(6, 0, 1), m.CSRW(6, m.CSR_EXC_EN)]
        if end == 1:
            handler += [m.ALUI(12, 12, 4, 0), m.CSRW(12, m.CSR_EPC)]
        handler.append(m.ERET)
        p.append(m.EXC if end == 0 else 0xffffffff)
    elif end == 2:
        p.append(m.EXC)  # disabled software trap
    elif end in (3, 4):
        p += [m.IMM20(6, 0, 1), m.ZEROIZE if end == 3 else m.CSRW(6, m.CSR_ZEROIZE)]
    elif end == 5:
        p.append(m.SPG(3))
    elif end == 6:
        p += [m.IMM20(6, 0, base + 1), m.LOAD(7, 6, 0, 0)]
    elif end == 7:
        p += [m.IMM20(6, 0, base + 7), m.STORE(7, 6, 0, 0)]
    elif end == 8:
        p += [m.IMM20(7, 0, 3), m.JALR(7, 7, 0)]
    elif end == 9:
        p.append(m.JAL(7, SIZE // 4))
    elif end == 10:
        p.append(m.LOAD(7, 0, -1, 1))
    elif end == 11:
        p.append(m.STORE(1, 0, SIZE // 8, 0))
    elif end == 12:
        invalid = (m.NOP | 1, m.LUT4(1, 2, 3, 4) | (1 << 12), m.ALU(0, 0, 0, 9),
                   m.ALUI(0, 0, 64, 5), m.IMM20(0, 3, 0), m.CMP(0, 0, 0, 0) | (1 << 20),
                   m.BEXT(1, 1, 8, 0, False), m.LOAD(1, 0, 0, 2), m.STORE(1, 0, 0, 2),
                   m.BR(0, 4, 0), m.JALR(0, 0, 0) | 256, m.SPG(0, 25),
                   m.GL(4, 5, 0, 0), m.GF128(0, 12, 0, 0), m.PERM(0, 13))
        p.append(invalid[(case // 18) % len(invalid)])
    elif end == 13:
        p.append(m.CSRW(1, m.CSR_DIT))
    elif end == 14:
        p.append(m.CSRR(1, m.CSR_DBG_OUT))
    elif end == 15:
        p += [m.CSRW(2, m.CSR_DBG_OUT), m.IMM20(6, 0, 1), m.CSRW(6, m.CSR_POWER)]
    elif end == 16:
        p += [m.CSRW(2, m.CSR_ECAUSE), m.CSRR(7, m.CSR_ECAUSE)]
    p.append(m.HALT)
    return [(0, words(p)), (HANDLER, words(handler)), (DATA, data)]


def emit(out, name, images, size, max_steps):
    cpu = m.Ass2([(0, size)], PROFILE)
    print("CASE", name, f"{size:x}", file=out)
    for addr, data in images:
        cpu.mem.poke_bytes(addr, data)
        print("LOAD", f"{addr:x}", data.hex(), file=out)
    for count in range(1, max_steps + 1):
        s = cpu.step()
        fields = (s.pc, s.insn, s.trapped, cpu.pc, int(cpu.halted), cpu.ecause,
                  cpu.instret, cpu.cycles, *cpu.r, *cpu.s, len(s.mem_writes))
        record = [f"{v:x}" for v in fields]
        for addr, byte in s.mem_writes:
            record.extend((f"{addr:x}", f"{byte:x}"))
        print("STEP", *record, file=out)
        if cpu.halted:
            print("END", cpu.mem.regions[0][2].hex(), file=out)
            return count
    raise ValueError(f"{name} exceeded {max_steps} steps at PC {cpu.pc:#x}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--seed", type=lambda v: int(v, 0), default=0x41535332)
    parser.add_argument("--count", type=int, default=1024)
    parser.add_argument("--firmware", type=Path, action="append", default=[],
                        help="append a flat SRAM image with entry PC zero")
    args = parser.parse_args()
    if args.count < 0 or not (args.count or args.firmware):
        parser.error("select at least one program")
    steps = 0
    with args.output.open("w") as out:
        print("ASS2-V1", args.count + len(args.firmware), file=out)
        print("# seed", hex(args.seed), "profile", json.dumps(asdict(PROFILE)), file=out)
        for i in range(args.count):
            steps += emit(out, f"random-{i:04}", program(i, random.Random((args.seed << 32) + i)),
                          SIZE, 512)
        for i, path in enumerate(args.firmware):
            steps += emit(out, f"firmware-{i}", [(0, path.read_bytes())], SIZE, 1000000)
    print(f"{args.count} random + {len(args.firmware)} firmware programs, {steps} steps", file=sys.stderr)


if __name__ == "__main__":
    main()
