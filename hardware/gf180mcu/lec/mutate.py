#!/usr/bin/env python3
"""Write a mutated copy of an RTL file: mutate.py <src> <dst> <mutation>. Exits non-zero unless
exactly one site was changed."""
import sys

MUT = {
    # Goldilocks unit
    "kmul": ("localparam logic [AW-1:0] K_FOLD = AW'(4);", "localparam logic [AW-1:0] K_FOLD = AW'(5);"),
    "m2": ("assign r3 = AW'({{(W-1){1'b1}}, 2'b00, ~p3});", "assign r3 = AW'({{(W-1){1'b1}}, 2'b00, p3});"),
    "canon": ("assign r = (u[LW] | v_raw[LW]) ? v_raw[LW-1:0] : u[LW-1:0];", "assign r = u[LW] ? v_raw[LW-1:0] : u[LW-1:0];"),
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
