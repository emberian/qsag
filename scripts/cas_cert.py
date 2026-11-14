#!/usr/bin/env python3
"""Compute exact constructive ring / Groebner cofactor witnesses for Qsag Lean 4.35."""
import json, sys, sympy as sp

def emit_ideal_cert(vars_list: list[str], gens: list[str], target: str, modulus: int | None = None):
    syms = sp.symbols(vars_list)
    env = dict(zip(vars_list, syms))
    G = [sp.sympify(g, locals=env) for g in gens]
    if modulus is not None:
        G = G + [sp.Integer(modulus)]
    T = sp.expand(sp.sympify(target, locals=env))
    # Express T = sum(c_i * G_i) over ZZ via Groebner + lift
    gb = sp.groebner(G, *syms, domain=sp.ZZ, method="f5b")
    # Direct polynomial division / lift over ZZ:
    M_poly = sp.Matrix([G])
    # Use sympy's reduced() when G is already a Groebner basis (common for [u**4 - 7, p]):
    cofactors, rem = sp.reduced(T, G, *syms, domain=sp.ZZ)
    assert sp.expand(rem) == 0, f"Target not in ideal over ZZ (rem={rem})"
    terms = [f"({sp.sstr(c)}) * ({g})" for c, g in zip(cofactors, gens + ([str(modulus)] if modulus else [])) if c != 0]
    return " + ".join(terms) if terms else "0"

if __name__ == "__main__":
    spec = json.loads(sys.stdin.read())
    print(emit_ideal_cert(spec["vars"], spec["gens"], spec["target"], spec.get("modulus")))
