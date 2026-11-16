#!/usr/bin/env python3
"""Write a mutated copy of an RTL file: mutate.py <src> <dst> <mutation>. Exits non-zero unless
exactly one site was changed."""
import sys

MUT = {
    # Goldilocks unit
    "kmul": ("PRIME - (LW'(1) << (W + 1)) + LW'(2);", "PRIME - (LW'(1) << (W + 1)) + LW'(3);"),
    "m2": ("r2 = AW'({hi, {(W-2){1'b0}}, ~m2});", "r2 = AW'({hi, {(W-2){1'b0}}, m2});"),
    "canon": ("assign r = (u[LW] | v[LW]) ? v[LW-1:0] : u[LW-1:0];", "assign r = u[LW] ? v[LW-1:0] : u[LW-1:0];"),
    # GF(2^128) unit
    "poly": ("(D + 8)'(8'h87)", "(D + 8)'(8'h86)"),
    "digit": ("if (d[i]) t = t ^ ({{D{1'b0}}, h} << i);", "if (d[D-1-i]) t = t ^ ({{D{1'b0}}, h} << i);"),
}
src, dst, name = sys.argv[1:4]
a, b = MUT[name]
s = open(src).read()
if s.count(a) != 1:
    sys.exit(f"mutation {name}: {s.count(a)} sites")
open(dst, "w").write(s.replace(a, b))
