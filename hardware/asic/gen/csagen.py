#!/usr/bin/env python3
"""Carry-save generator for Goldilocks datapaths.

A `Csa` holds bits in columns of weight 2^w. `bit()` folds any weight 2^k into
columns 0..63 with 2^64 = 2^32 - 1 and 2^96 = -1 (mod p); a negative bit -x*2^w
becomes (~x)*2^w with -2^w added to a constant, which is reduced mod p and
entered as constant bits. `compress()` is a Dadda tree (full and half adders) that
keeps every carry (exact integer sum), so the two output rows X, Y satisfy
X + Y = (sum of all entered terms) + n*p for a known n, as integers.
`bound` is an exact upper bound of that integer.
"""
from collections import defaultdict

P = 2**64 - 2**32 + 1


class Mod:
    def __init__(self, name, ports):
        self.name, self.ports, self.lines, self.n = name, ports, [], 0

    def w(self, expr, width=1):
        self.n += 1
        nm = f"n{self.n}"
        rng = f"[{width - 1}:0] " if width > 1 else ""
        self.lines.append(f"  wire {rng}{nm} = {expr};")
        return nm

    def raw(self, line):
        self.lines.append("  " + line)

    def text(self):
        return f"module {self.name} (\n  " + ",\n  ".join(self.ports) + "\n);\n" + "\n".join(self.lines) + "\nendmodule\n"


def fold(k, sign):
    """2^k * sign as a list of (w, sign) with w < 64, mod p."""
    if k < 64:
        return [(k, sign)]
    if k < 96:
        return fold(k - 32, sign) + fold(k - 64, -sign)
    return fold(k - 96, -sign)


class Csa:
    def __init__(self, m):
        self.m, self.cols, self.const, self.fas = m, defaultdict(list), 0, 0
        self.has, self.stages = 0, 0

    def raw(self, expr, w):
        self.cols[w].append(expr)

    def bit(self, expr, k, sign=1):
        for w, s in fold(k, sign):
            if s > 0:
                self.cols[w].append(expr)
            else:
                self.cols[w].append(f"(~{expr})")
                self.const -= 1 << w

    def term(self, sig, width, shift=0, sign=1):
        for b in range(width):
            self.bit(f"{sig}[{b}]", shift + b, sign)

    def term_exact(self, sig, width, shift=0, sign=1):
        """sign * sig * 2^shift as integer bits, no modular folding (the rows stay an exact integer
        sum up to the constant); a negative term enters as its complement plus a constant."""
        for b in range(width):
            if sign > 0:
                self.cols[shift + b].append(f"{sig}[{b}]")
            else:
                self.cols[shift + b].append(f"(~{sig}[{b}])")
                self.const -= 1 << (shift + b)

    def flush_const(self):
        k = self.const % P
        self.const = 0
        for w in range(64):
            if (k >> w) & 1:
                self.cols[w].append("1'b1")

    @property
    def bound(self):
        return sum(len(v) << w for w, v in self.cols.items())

    def compress(self):
        """Dadda reduction to height 2. Height targets 2, 3, 4, 6, 9, 13, ...; each stage brings every
        column (old bits plus the carries this stage sends into it) down to the target with full and
        half adders on the old bits only, so a stage is one adder deep. Every adder preserves the
        integer sum (a + b + c = s + 2*carry, a + b = s + 2*carry)."""
        while True:
            maxh = max((len(v) for v in self.cols.values()), default=0)
            if maxh <= 2:
                return
            d = 2
            while d * 3 // 2 < maxh:
                d = d * 3 // 2
            new = defaultdict(list)
            w = min(self.cols)
            top = max(self.cols)
            while w <= top or len(new.get(w, [])) > 0:
                bits = self.cols.get(w, [])
                cin = new[w]
                h = len(bits) + len(cin)
                i = 0
                made = []
                while h > d and len(bits) - i >= 2:
                    if h - d >= 2 and len(bits) - i >= 3:
                        a, b, c = bits[i:i + 3]
                        made.append(self.m.w(f"{a} ^ {b} ^ {c}"))
                        new[w + 1].append(self.m.w(f"({a} & {b}) | ({a} & {c}) | ({b} & {c})"))
                        self.fas += 1
                        i += 3
                        h -= 2
                    else:
                        a, b = bits[i:i + 2]
                        made.append(self.m.w(f"{a} ^ {b}"))
                        new[w + 1].append(self.m.w(f"{a} & {b}"))
                        self.has += 1
                        i += 2
                        h -= 1
                new[w] = bits[i:] + cin + made
                w += 1
            self.cols = defaultdict(list, {k: v for k, v in new.items() if v})
            self.stages += 1

    def refold_high(self):
        hi = {w: v for w, v in self.cols.items() if w >= 64}
        for w in hi:
            del self.cols[w]
        for w, v in hi.items():
            for e in v:
                self.bit(e, w, 1)
        self.flush_const()

    def rows(self, prefix, max_quot=None):
        """Compress to two rows; with max_quot, refold until bound < (max_quot+1)*p.
        Returns (xname, yname, width, quotient_bound)."""
        self.flush_const()
        bound = self.bound
        self.compress()
        while max_quot is not None and bound // P > max_quot:
            self.refold_high()
            nb = self.bound
            assert nb < bound, "refold does not converge"
            bound = nb
            self.compress()
        width = max(bound.bit_length(), 64)
        xs = [self.cols[w][0] if len(self.cols.get(w, [])) > 0 else "1'b0" for w in range(width)]
        ys = [self.cols[w][1] if len(self.cols.get(w, [])) > 1 else "1'b0" for w in range(width)]
        assert all(len(v) == 0 for w, v in self.cols.items() if w >= width), "bits above the value bound"
        x = f"{prefix}x"
        y = f"{prefix}y"
        self.m.raw(f"wire [{width - 1}:0] {x} = {{{', '.join(reversed(xs))}}};")
        self.m.raw(f"wire [{width - 1}:0] {y} = {{{', '.join(reversed(ys))}}};")
        return x, y, width, bound // P


def final(m, inst, x, y, width, quot, out, par):
    """Instantiate the final canonicalizing adder. par: parallel compound adders (quot+1 candidates)."""
    if par:
        m.raw(f"qsag_gl64_final_par #(.W({width}), .NJ({quot + 1})) {inst} (.x({x}), .y({y}), .r({out}));")
    else:
        m.raw(f"qsag_gl64_final_seq #(.W({width})) {inst} (.x({x}), .y({y}), .r({out}));")
