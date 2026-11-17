"""Microcode assembler and disassembler for the Dregg-180 v2 sequencer (see isa.py).

Source syntax, one instruction per line, `;` starts a comment:

    label:
        LD   t0                 H = row            LD #0x1F        H = immediate (16 bits)
        XOR  l0+X > l0+X x+     H ^= row[A+X]; store H to row[B+X]; X += 1
        ST   l8                 store H            UN BE32 > l5    unary function, optional store
        DIN  > t0               next payload word  LDF ARGLO       framer field     LDC C_PAD   constant
        PUSH l0 | PUSH H        append to the response
        HDR  #cap [okz]         response header, length H words (<= cap); okz: ok flag = not Z
        FAIL #code              error response, then the hardware end action
        REL  l0                 append a rate lane to the response (declassification point)
        CMPT l0                 tag compare: payload word in H against a MAC lane (declassified verdict)
        END                     end of command: pad, wipe all working rows, drain, return to idle
        KMOV k_host0 > l0       key row to a rate lane          KEYWR > k_host0+X
        CTL  name               WIPE #mask      KEC 24|12      FLD PERM|RED [> row]     FADD row [> row]
        FRAM RSTART|WSTART|DONE   FRAM RWORD [> row]   FRAM WWORD row
        SETX #k | SETX H        SETC 0|1 #n | SETC 0|1 H        INCX
        BR [cond] label         BXNE #k label   DBNZ 0|1 label  CALL label   RET   DISP   ILL
    any instruction may end with `ret`.

Directives: .equ NAME value|row   .const NAME value64|"8 bytes"   .entry opcode label diag|prov|keyed
            .org address (fills with ILL up to a hardwired boundary of isa.py)
"""
import re

import isa


class AsmError(Exception):
    pass


class Rom:
    def __init__(self):
        self.words = []
        self.consts = []            # 64-bit constant table
        self.const_names = {}
        self.entries = {}           # request opcode -> (address, dispatch class)
        self.padding = set()        # addresses filled by .org
        self.labels = {}
        self.where = []             # per address: (file, line number, source text)

    def place(self, addr):
        """'label+offset' of an address (stable against code moving elsewhere)."""
        best = None
        for name, a in self.labels.items():
            if a <= addr and (best is None or a > best[1] or (a == best[1] and name < best[0])):
                best = (name, a)
        return f"{best[0]}+{addr - best[1]}" if best else f"@{addr}"

    def pushes(self):
        """Every instruction that writes the response: (place, source). A release reads 'rel:rN'."""
        out = []
        for a, w in enumerate(self.words):
            d = isa.decode(w)
            if d["op"] == isa.OP["PUSH"]:
                src = "H" if d["fn"] & 2 else f"r{d['a']}" + ("+X" if d["ia"] else "")
                out.append((self.place(a), ("rel:" if d["fn"] & 1 else "") + src))
        return out

    def releases(self):
        """The other declassification points: tag compares and record-tag writes to the FRAM."""
        out = []
        for a, w in enumerate(self.words):
            d = isa.decode(w)
            mn = isa.OPS[d["op"]]
            if mn == "CMP" and d["fn"] & 1 and not d["fn"] & 2:
                out.append((self.place(a), f"cmpt:r{d['a']}" + ("+X" if d["ia"] else "")))
            elif mn == "FRAM" and isa.FRAM[d["a"]] == "WWORD" and isa.row_class(d["b"]) == "lane":
                out.append((self.place(a), f"fram:r{d['b']}"))
        return out

    @property
    def used(self):
        return len(self.words) - len(self.padding)

    def bits(self):
        disp = len(self.entries) * (8 + 11 + 2)
        return dict(words=len(self.words), used=self.used, word_bits=len(self.words) * isa.WIDTH, const_bits=64 * len(self.consts),
                    dispatch_bits=disp, total_bits=len(self.words) * isa.WIDTH + 64 * len(self.consts) + disp)


def _int(tok, syms):
    if tok in syms:
        return syms[tok]
    try:
        return int(tok, 0)
    except ValueError:
        raise AsmError(f"unknown value '{tok}'")


def assemble(sources):
    """sources: list of (name, text). Returns a Rom."""
    rom = Rom()
    syms = dict(isa.row_symbols())
    lines = []
    for fname, text in sources:
        for ln, raw in enumerate(text.splitlines(), 1):
            s = raw.split(";", 1)[0].strip()
            while s:
                m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):\s*", s)
                if not m:
                    break
                lines.append((fname, ln, ("label", m.group(1))))
                s = s[m.end():]
            if s:
                lines.append((fname, ln, ("stmt", s)))
    # pass 1: addresses of labels, symbols
    addr = 0
    stmts = []
    for fname, ln, (kind, s) in lines:
        try:
            if kind == "label":
                if s in rom.labels or s in syms:
                    raise AsmError(f"duplicate symbol '{s}'")
                rom.labels[s] = addr
                continue
            tok = s.replace(",", " ").split()
            if tok[0] == ".equ":
                syms[tok[1]] = _int(tok[2], syms)
            elif tok[0] == ".const":
                rom.const_names[tok[1]] = len(rom.consts)
                if tok[2].startswith('"'):            # eight ASCII bytes, first byte least significant
                    text = tok[2].strip('"').encode()
                    if len(text) != 8:
                        raise AsmError("a string constant is eight bytes")
                    rom.consts.append(int.from_bytes(text, "little"))
                else:
                    rom.consts.append(_int(tok[2], syms) & isa.M64)
            elif tok[0] == ".org":
                to = _int(tok[1], syms)
                if to < addr:
                    raise AsmError(f".org {to}: the code before it ends at {addr}")
                for a in range(addr, to):
                    rom.padding.add(a)
                    stmts.append((fname, ln, "ILL", ["ILL"], a))
                addr = to
            elif tok[0].startswith("."):
                stmts.append((fname, ln, s, tok, None))
            else:
                stmts.append((fname, ln, s, tok, addr))
                addr += 1
        except AsmError as e:
            raise AsmError(f"{fname}:{ln}: {e}") from None
    if addr > (1 << 11):
        raise AsmError("ROM exceeds the 11-bit micro-PC")
    # pass 2
    for fname, ln, s, tok, a in stmts:
        try:
            if a is None:
                if tok[0] == ".entry" and len(tok) == 4:
                    rom.entries[_int(tok[1], syms)] = (rom.labels[tok[2]], isa.DCLASS[tok[3]])
                else:
                    raise AsmError(f"bad directive {tok[0]}")
                continue
            rom.words.append(_encode(tok, syms, rom))
            rom.where.append((fname, ln, s))
        except (AsmError, KeyError, IndexError, AssertionError) as e:
            raise AsmError(f"{fname}:{ln}: {s!r}: {e!r}") from None
    return rom


def _row(tok, syms):
    """'name', 'name+X', 'r12' -> (row, indexed)"""
    idx = 0
    if tok.endswith("+X"):
        tok, idx = tok[:-2], 1
    if re.fullmatch(r"r\d+", tok):
        r = int(tok[1:])
    else:
        r = _int(tok, syms)
    if not 0 <= r < 128:
        raise AsmError(f"row out of range: {tok}")
    return r, idx


def _target(tok, rom):
    if tok.startswith("@"):
        return int(tok[1:])
    if tok not in rom.labels:
        raise AsmError(f"unknown label '{tok}'")
    return rom.labels[tok]


def _encode(tok, syms, rom):
    tok = list(tok)
    seq = xi = 0
    while tok[-1] in ("ret", "x+"):
        if tok.pop() == "ret":
            seq = 1
        else:
            xi = 1
    dst = None
    if ">" in tok:
        i = tok.index(">")
        dst = _row(tok[i + 1], syms)
        if len(tok) != i + 2:
            raise AsmError("text after the destination")
        tok = tok[:i]
    mn, args = tok[0].upper(), tok[1:]
    f = dict(a=0, b=0, fn=0, ia=0, ib=0, xi=xi, seq=seq)

    def store():
        if dst is not None:
            f["b"], f["ib"] = dst
            f["fn"] |= 1

    def need(n):
        if len(args) != n:
            raise AsmError(f"{mn} takes {n} operand(s)")

    def no_store():
        if dst is not None:
            raise AsmError(f"{mn} cannot store")

    if mn == "ST":
        need(1)
        no_store()
        dst = _row(args[0], syms)
        mn, args = "UN", ["ID"]
    elif mn == "INCX":
        need(0)
        mn, f["xi"] = "NOP", 1
    elif mn == "RET":
        need(0)
        mn, f["seq"] = "NOP", 1
    op = isa.OP.get(mn)
    if mn == "REL":
        need(1)
        no_store()
        f["a"], f["ia"] = _row(args[0], syms)
        f["fn"] = 1
        return isa.encode(isa.OP["PUSH"], **f)
    if mn == "CMPT":
        need(1)
        no_store()
        f["a"], f["ia"] = _row(args[0], syms)
        f["fn"] = 1
        return isa.encode(isa.OP["CMP"], **f)
    if op is None:
        raise AsmError(f"unknown mnemonic {mn}")
    if mn in ("END", "ILL") and (seq or xi):
        raise AsmError(f"{mn} takes no modifier")
    if mn == "CMP" and dst is not None:
        raise AsmError("CMP cannot store")
    if mn in ("NOP", "DISP", "END", "ILL"):
        need(0)
        no_store()
    elif mn in isa.ALU2:
        need(1)
        if args[0].startswith("#"):
            no_store()
            f["a"], f["b"], hi = isa.imm_fields(_int(args[0][1:], syms))
            f["fn"] = hi | 2
        else:
            f["a"], f["ia"] = _row(args[0], syms)
            store()
    elif mn == "UN":
        need(1)
        f["a"] = isa.UN.index(args[0])
        store()
    elif mn == "DIN":
        need(0)
        store()
    elif mn == "LDF":
        need(1)
        f["a"] = isa.LDF.index(args[0])
        store()
    elif mn == "LDC":
        need(1)
        f["a"] = int(args[0][1:]) if re.fullmatch(r"k\d+", args[0]) else rom.const_names[args[0]]
        store()
    elif mn == "PUSH":
        need(1)
        no_store()
        if args[0] == "H":
            f["fn"] = 2
        else:
            f["a"], f["ia"] = _row(args[0], syms)
    elif mn in ("HDR", "FAIL"):
        no_store()
        if not args or not args[0].startswith("#"):
            raise AsmError(f"{mn} takes an immediate")
        f["a"], f["b"], hi = isa.imm_fields(_int(args[0][1:], syms))
        f["fn"] = hi
        if mn == "HDR" and args[1:] == ["okz"]:
            f["fn"] |= 1
        elif len(args) != 1:
            raise AsmError("bad operands")
    elif mn == "KMOV":
        need(1)
        if dst is None:
            raise AsmError("KMOV needs a destination")
        f["a"], f["ia"] = _row(args[0], syms)
        f["b"], f["ib"] = dst
    elif mn == "KEYWR":
        need(0)
        if dst is None:
            raise AsmError("KEYWR needs a destination")
        f["b"], f["ib"] = dst
    elif mn == "CTL":
        need(1)
        no_store()
        f["a"] = isa.CTL.index(args[0])
    elif mn == "WIPE":
        need(1)
        no_store()
        f["a"] = _int(args[0].lstrip("#"), syms)
    elif mn == "KEC":
        need(1)
        no_store()
        f["a"] = isa.KEC[args[0]]
    elif mn == "FLD":
        need(1)
        f["a"] = isa.FLD.index(args[0])
        store()
    elif mn == "FADD":
        need(1)
        f["a"], f["ia"] = _row(args[0], syms)
        store()
    elif mn == "FRAM":
        f["a"] = isa.FRAM.index(args[0])
        if args[0] == "WWORD":
            need(2)
            no_store()
            f["b"], f["ib"] = _row(args[1], syms)
        else:
            need(1)
            if dst is not None and args[0] != "RWORD":
                raise AsmError("only FRAM RWORD stores")
            store()
    elif mn == "SETX":
        need(1)
        no_store()
        if args[0] == "H":
            f["fn"] = 1
        else:
            f["a"] = _int(args[0].lstrip("#"), syms)
    elif mn == "SETC":
        need(2)
        no_store()
        f["a"] = int(args[0])
        if args[1] == "H":
            f["a"] |= 2
        else:
            f["b"], f["fn"] = isa.target_fields(_int(args[1].lstrip("#"), syms))
    elif mn in isa.BRANCH:
        no_store()
        if mn == "BR":
            if len(args) == 2:
                f["a"] = isa.COND.index(args[0])
            elif len(args) != 1:
                raise AsmError("BR [cond] label")
        elif mn == "BXNE":
            need(2)
            f["a"] = _int(args[0].lstrip("#"), syms)
        elif mn == "DBNZ":
            need(2)
            f["a"] = int(args[0])
        else:
            need(1)
        f["b"], f["fn"] = isa.target_fields(_target(args[-1], rom))
    else:
        raise AsmError(f"no encoder for {mn}")
    return isa.encode(op, **f)


def disasm(w):
    """Canonical text of one micro-word; assemble() of it gives the same word back."""
    d = isa.decode(w)
    mn = isa.OPS[d["op"]]
    ra = f"r{d['a']}" + ("+X" if d["ia"] else "")
    rb = f"r{d['b']}" + ("+X" if d["ib"] else "")
    st = f" > {rb}" if d["fn"] & 1 else ""
    t = f"@{isa.target(d)}"
    if mn == "CMP" and d["fn"] & 1 and not d["fn"] & 2:
        s = f"CMPT {ra}"
    elif mn in isa.ALU2:
        s = f"{mn} #{isa.imm16(d)}" if d["fn"] & 2 else f"{mn} {ra}{st}"
    elif mn == "UN":
        s = f"UN {isa.UN[d['a']]}{st}"
    elif mn == "DIN":
        s = f"DIN{st}"
    elif mn == "LDF":
        s = f"LDF {isa.LDF[d['a']]}{st}"
    elif mn == "LDC":
        s = f"LDC k{d['a']}{st}"
    elif mn == "PUSH":
        s = "PUSH H" if d["fn"] & 2 else (f"REL {ra}" if d["fn"] & 1 else f"PUSH {ra}")
    elif mn == "HDR":
        s = f"HDR #{isa.imm16(d)}" + (" okz" if d["fn"] & 1 else "")
    elif mn == "FAIL":
        s = f"FAIL #{isa.imm16(d)}"
    elif mn == "KMOV":
        s = f"KMOV {ra} > {rb}"
    elif mn == "KEYWR":
        s = f"KEYWR > {rb}"
    elif mn == "CTL":
        s = f"CTL {isa.CTL[d['a']]}"
    elif mn == "WIPE":
        s = f"WIPE #{d['a']}"
    elif mn == "KEC":
        s = "KEC 12" if d["a"] else "KEC 24"
    elif mn == "FLD":
        s = f"FLD {isa.FLD[d['a']]}{st}"
    elif mn == "FADD":
        s = f"FADD {ra}{st}"
    elif mn == "FRAM":
        s = f"FRAM WWORD {rb}" if isa.FRAM[d["a"]] == "WWORD" else f"FRAM {isa.FRAM[d['a']]}{st}"
    elif mn == "SETX":
        s = "SETX H" if d["fn"] & 1 else f"SETX #{d['a']}"
    elif mn == "SETC":
        s = f"SETC {d['a'] & 1} " + ("H" if d["a"] & 2 else f"#{isa.target(d)}")
    elif mn == "BR":
        s = f"BR {isa.COND[d['a']]} {t}"
    elif mn == "BXNE":
        s = f"BXNE #{d['a']} {t}"
    elif mn == "DBNZ":
        s = f"DBNZ {d['a']} {t}"
    elif mn == "CALL":
        s = f"CALL {t}"
    else:
        s = mn
    return s + (" x+" if d["xi"] else "") + (" ret" if d["seq"] & 1 else "")
