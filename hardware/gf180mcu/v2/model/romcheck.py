"""Static checks on a ROM image (ARCHITECTURE.md 8.2, the script-over-the-image part).

    python3 romcheck.py [S|L]

check(rom, manifest) returns a list of findings; an empty list is a pass. The decoder enforces most of
these at run time as control faults; the point here is to fail the build instead.
"""
import os
import sys

import isa
import uasm

MANIFEST = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "ucode", "push_manifest.txt"))
KEY_OPS = ("KEYWR",)
KEY_CTL = ("SETKV", "AUTH", "NONCE")


def load_manifest(path=MANIFEST):
    out = {}
    with open(path) as fh:
        for ln in fh:
            ln = ln.split("#", 1)[0].split()
            if ln:
                out[ln[0]] = ln[1]
    return out


def check(rom, manifest):
    f = []
    words = rom.words
    op_of = lambda w: isa.OPS[isa.decode(w)["op"]]  # noqa: E731
    # 1. response writers and declassification points = the reviewed list
    pushes = dict(rom.pushes() + rom.releases())
    for place, src in pushes.items():
        if manifest.get(place) != src:
            f.append(f"output {src} at {place} is not in the manifest")
    labels = set(rom.labels)
    for place in manifest:
        if place not in pushes and place.split("+")[0] in labels:
            f.append(f"manifest entry {place} has no such instruction in the ROM")
    # 2. the idle point and the hardwired layout
    if [a for a, w in enumerate(words) if op_of(w) == "DISP"] != [isa.IDLE_ADDR]:
        f.append("DISP must be at address 0 and nowhere else")
    if not any(op_of(w) in ("END", "FAIL") for w in words):
        f.append("the ROM has no END or FAIL")
    for op, (addr, cls) in rom.entries.items():
        if not 0 < addr < len(words) or addr in rom.padding:
            f.append(f"entry of opcode {op:#x} is outside the code")
        if (cls == isa.D_PROV) != (isa.KEY_LO <= addr <= isa.KEY_HI):
            f.append(f"entry of opcode {op:#x}: provisioning class and key range disagree")
    for a, w in enumerate(words):
        d = isa.decode(w)
        mn = isa.OPS[d["op"]]
        where = rom.place(a)
        # 3. transfers
        if mn in isa.BRANCH:
            t = isa.target(d)
            if t == isa.IDLE_ADDR or t >= len(words) or t in rom.padding:
                f.append(f"{where}: transfer to {t}")
        # 4. key and record instructions only in their hardwired ranges
        keyish = mn in KEY_OPS or (mn == "CTL" and isa.CTL[d["a"]] in KEY_CTL)
        if keyish and not isa.KEY_LO <= a <= isa.KEY_HI:
            f.append(f"{where}: key instruction outside the key range")
        if mn == "FRAM":
            if not isa.REC_LO <= a <= isa.REC_HI:
                f.append(f"{where}: FRAM instruction outside the record range")
            if isa.FRAM[d["a"]] == "WWORD" and (d["ib"] or d["b"] not in isa.FRAM_SRC):
                f.append(f"{where}: FRAM WWORD of row {d['b']}")
        # 5. rows named directly
        reads_row = (mn in isa.ALU2 or mn == "PUSH") and not d["fn"] & 2 or mn == "FADD"
        rd = d["a"] if reads_row else None
        wr = d["b"] if d["fn"] & 1 and mn in ("LD", "XOR", "AND", "OR", "ADD", "SUB", "UN", "DIN", "LDF", "LDC", "FLD", "FADD") else None
        if mn == "FRAM" and isa.FRAM[d["a"]] == "RWORD" and d["fn"] & 1:
            wr = d["b"]
        for r, kind in ((rd, "read"), (wr, "write")):
            if r is not None and not (d["ia"] if kind == "read" else d["ib"]):
                if isa.row_class(r, isa.ROWS_L) in ("key", "out", "kwork", "none"):
                    f.append(f"{where}: {kind} of {isa.row_class(r, isa.ROWS_L)} row {r}")
        if mn == "KMOV" and (isa.row_class(d["a"]) != "key" or d["b"] >= isa.RATE_LANES or d["ia"] or d["ib"]):
            f.append(f"{where}: KMOV operands")
        if (mn == "PUSH" and d["fn"] & 1 and not d["fn"] & 2) or (mn == "CMP" and d["fn"] & 1 and not d["fn"] & 2):
            if not d["ia"] and d["a"] >= isa.RATE_LANES:
                f.append(f"{where}: REL or CMPT of row {d['a']}, not a rate lane")
        # 6. trap words only where .org put them
        if mn == "ILL" and a not in rom.padding:
            f.append(f"{where}: illegal instruction")
        if a in rom.padding and w != isa.encode(isa.OP["ILL"]):
            f.append(f"{where}: padding is not a trap word")
        # 7. canonical encoding
        try:
            back = uasm.assemble([("x", uasm.disasm(w))]).words[0]
        except (uasm.AsmError, IndexError, KeyError, ValueError) as e:
            back = None
            f.append(f"{where}: does not disassemble ({e!r})")
        if back is not None and back != w:
            f.append(f"{where}: non-canonical encoding {w:07x}")
    # 8. nothing falls off the end of the image or into a trap word
    for a, w in enumerate(words):
        d = isa.decode(w)
        mn = isa.OPS[d["op"]]
        ends = mn in ("FAIL", "END", "ILL") or d["seq"] & 1 or (mn == "BR" and d["a"] == 0)
        nxt = a + 1
        if not ends and (nxt >= len(words) or nxt in rom.padding) and a not in rom.padding:
            f.append(f"{rom.place(a)}: execution runs past the end of the code")
    return f


if __name__ == "__main__":
    import chip
    cfg = sys.argv[1] if len(sys.argv) > 1 else "S"
    rom = chip.build_rom(cfg)
    findings = check(rom, load_manifest())
    print(f"configuration {cfg}: {rom.bits()}")
    for x in findings:
        print("FINDING:", x)
    sys.exit(1 if findings else 0)
