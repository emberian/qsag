#!/usr/bin/env python3
"""Exact algebraic-normal-form equivalence of Yosys-elaborated GF(2^128) & Wiedemann T_7 RTL.
Each polynomial bit is an integer bitset of square-free monomials. Inputs a_i,
b_j and a_i*b_j occupy disjoint slots. AND accepts only opposite linear input
spaces; hence the evaluator also proves bilinearity, rather than assuming it.
"""
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[1]
os.chdir(root)
sys.path.insert(0, str(root / "gen"))
import qsag_ref as ref  # noqa: E402

os.environ["PATH"] = os.environ.get("OSS_CAD_BIN", "/opt/oss-cad-suite/bin") + ":" + os.environ["PATH"]
w = root / "lec/work/anf"
w.mkdir(parents=True, exist_ok=True)
os.environ["TMPDIR"] = str(w)
run = ["timeout", "--kill-after=10s", "600s"]


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def multiply(a, b):
    if a == 0 or b == 0:
        return 0
    if a == 1:
        return b
    if b == 1:
        return a
    if a.bit_length() > 129 and b.bit_length() <= 129:
        a, b = b, a
    assert a >> 129 == 0 and (a & 1) == 0 and b >> 257 == 0 and b & ((1 << 129) - 1) == 0, "non-bilinear AND"
    bm = b >> 129
    result = 0
    for i in bits(a >> 1):
        result ^= bm << (257 + 128 * i)
    return result


def evaluate(mod):
    path = w / (mod + ".json")
    cmd = (
        f"plugin -i slang; read_slang -Irtl rtl/qsag_asic_keccak_clmul.sv rtl/qsag_asic_tower_maps_gen.sv "
        f"--top {mod}; proc; flatten; opt; techmap; opt; write_json {path}"
    )
    with (w / (mod + ".anf.log")).open("w") as f:
        subprocess.run(run + ["yosys", "-Q", "-T", "-p", cmd], stdout=f, stderr=subprocess.STDOUT, check=True)
    module = json.loads(path.read_text())["modules"][mod]
    val = {"0": 0, "1": 1}
    n = 0
    for port in ["a", "b"] if "a" in module["ports"] else ["x"]:
        for i, bit in enumerate(module["ports"][port]["bits"]):
            val[bit] = 1 << (1 + (128 if port == "b" else 0) + i)
    cells = list(module["cells"].values())
    while cells:
        remain = []
        progress = False
        for c in cells:
            conn = c["connections"]
            typ = c["type"]
            ins = [b for p, v in conn.items() if c["port_directions"][p] == "input" for b in v]
            if not all(b in val for b in ins):
                remain.append(c)
                continue
            y = conn["Y"]
            assert len(y) == 1
            a = val[conn["A"][0]]
            if typ == "$_XOR_":
                o = a ^ val[conn["B"][0]]
            elif typ == "$_AND_":
                o = multiply(a, val[conn["B"][0]])
            elif typ == "$_NOT_":
                o = a ^ 1
            elif typ == "$_OR_":
                o = a ^ val[conn["B"][0]] ^ multiply(a, val[conn["B"][0]])
            else:
                raise ValueError(typ)
            val[y[0]] = o
            progress = True
            n += 1
        assert progress or not remain, "cycle or unresolved input"
        cells = remain
    output = next(p for p, v in module["ports"].items() if v["direction"] == "output")
    return [val[b] for b in module["ports"][output]["bits"]], n, hashlib.sha256(path.read_bytes()).hexdigest()


results = []
t7_cols, poly_cols = ref.tower_basis()
for mod in ["qsag_clmul64", "qsag_gf128_mul", "qsag_tower128_to_poly", "qsag_poly_to_tower128", "qsag_tower128_mul"]:
    got, n, digest = evaluate(mod)
    expected = [0] * len(got)
    if mod == "qsag_clmul64":
        for i in range(64):
            for j in range(64):
                expected[i + j] ^= 1 << (257 + 128 * i + j)
    elif mod == "qsag_gf128_mul":
        for i in range(128):
            for j in range(128):
                for k in bits(ref.gf128_reduce(1 << (i + j))):
                    expected[k] ^= 1 << (257 + 128 * i + j)
    elif mod == "qsag_tower128_mul":
        for i in range(128):
            for j in range(128):
                prod = ref.tower128_mul(1 << i, 1 << j)
                for k in bits(prod):
                    expected[k] ^= 1 << (257 + 128 * i + j)
    else:
        cols = t7_cols if mod == "qsag_tower128_to_poly" else poly_cols
        for i, col in enumerate(cols):
            for k in bits(col):
                expected[k] ^= 1 << (i + 1)
    assert got == expected, mod
    mutated = got.copy()
    mutated[0] ^= 1 << (257 if mod in ["qsag_clmul64", "qsag_gf128_mul", "qsag_tower128_mul"] else 1)
    assert mutated != expected
    results.append({"module": mod, "gates": n, "result": "ANF equal", "mutation": "rejected", "netlist_sha256": digest})
    print(f"ANF {mod}: {n} gates, exact ANF equal, mutation rejected", flush=True)

shutil.rmtree(w, ignore_errors=True)
(root / "logs").mkdir(exist_ok=True)
(root / "logs/lec_anf.json").write_text(json.dumps(results, indent=2) + "\n")
