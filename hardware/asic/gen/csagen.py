#!/usr/bin/env python3
"""Carry-save generator for Goldilocks datapaths.

A `Csa` holds bits in columns of weight 2^w. `bit()` folds any weight 2^k into
columns 0..63 with 2^64 = 2^32 - 1 and 2^96 = -1 (mod p); a negative bit -x*2^w
becomes (~x)*2^w with -2^w added to a constant, which is reduced mod p and
entered as constant bits. `compress()` is a level-synchronous 3:2 tree that
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
        while max((len(v) for v in self.cols.values()), default=0) > 2:
            new = defaultdict(list)
            for w in sorted(self.cols):
                bits = self.cols[w]
                i = 0
                made = []
                while len(bits) - i >= 3:
                    a, b, c = bits[i:i + 3]
                    made.append(self.m.w(f"{a} ^ {b} ^ {c}"))
                    new[w + 1].append(self.m.w(f"({a} & {b}) | ({a} & {c}) | ({b} & {c})"))
                    self.fas += 1
                    i += 3
                new[w] = bits[i:] + new[w] + made
            self.cols = new

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
