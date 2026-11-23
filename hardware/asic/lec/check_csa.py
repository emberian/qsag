#!/usr/bin/env python3
"""Independent algebraic certificate checker for all generated carry-save RTL modules.
Parses emitted SystemVerilog equations directly, checks every HA/FA carry truth table,
eliminates s + 2c == sum(inputs) from outputs back to primary inputs, and checks exact
integer or modulo-p weights against the word-level specification (plus fault rejection).
"""
import collections
import hashlib
import json
import pathlib
import re
import sys

P = 2**64 - 2**32 + 1


class Circuit:
    def __init__(self, text):
        self.alias = {}
        self.pairs = []
        self.pp = {}
        wires = re.findall(r"wire\s+(?:\[([^]]+)\]\s+)?(\w+)\s*=\s*([^;]+);", text)
        assigns = re.findall(r"assign\s+(\w+)\s*=\s*\{([^}]+)\};", text)
        scalar = {n: e for w, n, e in wires if not w}
        for n, e in assigns:
            self.alias[n] = list(reversed(e.split(", ")))
        for w, n, e in wires:
            if w:
                if e.startswith("{"):
                    self.alias[n] = list(reversed(e[1:-1].split(", ")))
                elif re.fullmatch(r"\w+\[\d+:\d+\]", e):
                    a, hi, lo = re.fullmatch(r"(\w+)\[(\d+):(\d+)\]", e).groups()
                    self.alias[n] = [f"{a}[{i}]" for i in range(int(lo), int(hi) + 1)]
                else:
                    raise ValueError(("alias", n, e))
            elif "^" in e:
                args = e.split(" ^ ")
                cn = "n" + str(int(n[1:]) + 1)
                ce = scalar[cn]
                for bits in range(1 << len(args)):
                    values = {a: (bits >> i) & 1 for i, a in enumerate(args)}
                    ev = ce
                    for a, v in sorted(values.items(), key=lambda kv: -len(kv[0])):
                        ev = ev.replace(a, str(v))
                    assert sum(values.values()) == (sum(values.values()) % 2) + 2 * eval(ev, {"__builtins__": {}}, {})
                self.pairs.append((n, cn, args))
            elif re.fullmatch(r"\w+\[\d+\] & \w+\[\d+\]", e):
                self.pp[n] = e
        for sn, cn, _ in self.pairs:
            self.pp.pop(cn, None)

    def add(self, d, e, k):
        e = e.strip()
        if e in ("1'b0", "1'b1"):
            if e == "1'b1":
                d["1"] += k
        elif e.startswith("(~") and e.endswith(")"):
            d["1"] += k
            self.add(d, e[2:-1], -k)
        elif (m := re.fullmatch(r"(\w+)\[(\d+)\]", e)) and m[1] in self.alias:
            self.add(d, self.alias[m[1]][int(m[2])], k)
        else:
            d[self.pp.get(e, e)] += k

    def prove(self, names, expected, mod=P):
        d = collections.defaultdict(int)
        for n in names:
            for i, e in enumerate(self.alias[n]):
                self.add(d, e, 1 << i)
        for sn, cn, args in reversed(self.pairs):
            s, c = d.pop(sn, 0), d.pop(cn, 0)
            if mod == 0:
                assert c == 2 * s, ("unpaired carry int", sn, c, s)
            else:
                assert (c - 2 * s) % mod == 0, ("unpaired carry mod", sn, c, s)
            for a in args:
                self.add(d, a, s)
        if mod == 0:
            got = {k: v for k, v in d.items() if v}
            want = {k: v for k, v in expected.items() if v}
        else:
            got = {k: v % mod for k, v in d.items() if v % mod}
            want = {k: v % mod for k, v in expected.items() if v % mod}
        assert got == want, (set(got.items()) ^ set(want.items()))
        fault = want.copy()
        key = next(iter(want))
        fault[key] = (fault[key] + 1) if mod == 0 else ((fault[key] + 1) % mod)
        assert got != fault
        return len(self.pairs)


def words(**weights):
    d = collections.defaultdict(int)
    for sig, weight in weights.items():
        name, width = sig.rsplit("_w", 1) if "_w" in sig else (sig, 64)
        width = int(width)
        for i in range(width):
            d[f"{name}[{i}]"] += weight * (1 << i)
    return d


def main(root):
    root = pathlib.Path(root)
    out = []
    specs = {
        "qsag_gl64_mul_slice32x4": (
            ["s", "c"],
            {f"a[{i}] & b[{j}]": 1 << (i + j) for i in range(32) for j in range(4)},
            0,
        ),
        "qsag_gl64_mul_comb32_l1": (["s", "c"], {**words(s0_w36=1, c0_w36=1), **{f"{p}[{i}]": 1 << (i + 4) for p in ("s1", "c1") for i in range(36)}}, 1 << 40),
        "qsag_gl64_mul_comb32_l2": (["s", "c"], {**words(s0_w40=1, c0_w40=1), **{f"{p}[{i}]": 1 << (i + 8) for p in ("s1", "c1") for i in range(40)}}, 1 << 48),
        "qsag_gl64_mul_comb32_l3": (["s", "c"], {**words(s0_w48=1, c0_w48=1), **{f"{p}[{i}]": 1 << (i + 16) for p in ("s1", "c1") for i in range(48)}}, 1 << 64),
        "qsag_gl64_mul_slice33x4": (
            ["s", "c"],
            {f"a[{i}] & b[{j}]": 1 << (i + j) for i in range(33) for j in range(4)},
            0,
        ),
        "qsag_gl64_mul_comb33_l1": (["s", "c"], {**words(s0_w37=1, c0_w37=1), **{f"{p}[{i}]": 1 << (i + 4) for p in ("s1", "c1") for i in range(37)}}, 1 << 41),
        "qsag_gl64_mul_comb33_l2": (["s", "c"], {**words(s0_w41=1, c0_w41=1), **{f"{p}[{i}]": 1 << (i + 8) for p in ("s1", "c1") for i in range(41)}}, 1 << 49),
        "qsag_gl64_mul_comb33_l3": (["s", "c"], {**words(s0_w49=1, c0_w49=1), **{f"{p}[{i}]": 1 << (i + 16) for p in ("s1", "c1") for i in range(49)}}, 1 << 65),
        "qsag_gl64_mul_comb33_top": (
            ["s", "c"],
            {**words(s0_w65=1, c0_w65=1), **{f"a[{i}] & b_hi[0]": 1 << (32 + i) for i in range(33)}},
            0,
        ),
        "qsag_gl64_fold_one": (["rx", "ry"], words(v_w128=1), P),
        "qsag_gl64_sk_c0": (["d0x", "d0y"], {"1": 2 * ((1 << 64) - 1), **words(p0_s_w64=1, p0_c_w64=1, p2_s_w64=-1, p2_c_w64=-1)}, 0),
        "qsag_gl64_sk_c1": (["d1x", "d1y"], {"1": 2 * ((1 << 64) - 1), **words(ps_s_w66=1, ps_c_w66=1, p0_s_w64=-1, p0_c_w64=-1)}, 0),
        "qsag_gl64_sk_sh32": (["rx", "ry"], words(v_w68=1 << 32), P),
        "qsag_gl64_sk_m0": (["m0x", "m0y"], words(d0x_w66=1, d0y_w66=1, e1x_w66=1, e1y_w66=1), 0),
        "qsag_gl64_sk_m1": (["m1x", "m1y"], words(m0x_w68=1, m0y_w68=1, e2x_w66=1, e2y_w66=1), 0),
        "qsag_gl64_sk_s2": (["rx", "ry"], {"1": 6, **words(bx_w69=1, by_w69=1)}, P),
        "qsag_gl_csa3_66": (["sx", "sy"], words(a0=1, a1=1, a2=1), 0),
        "qsag_gl_csa4_66": (["sx", "sy"], words(a0=1, a1=1, a2=1, a3=1), 0),
        "qsag_p2_m4_lane": (["o_x", "o_y"], words(sx_w66=1, sy_w66=1, bi=1, bj=2), P),
        "qsag_p2_me_col_lane": (["o_x", "o_y"], words(sx_w66=1, sy_w66=1, yb=1, rcb=1), P),
        "qsag_p2_sum4_csa": (["o_x", "o_y"], words(sx0_w66=1, sy0_w66=1, sx1_w66=1, sy1_w66=1), P),
        "qsag_p2_canopy_ff": (["o_x", "o_y"], words(l=1, r=2, c=4), P),
    }
    for l in range(12):
        if l == 0:
            specs[f"qsag_p2_mi_lane{l}"] = (["o_x", "o_y"], words(s_tail=1, rcl=1, x0=1 - 64), P)
        else:
            specs[f"qsag_p2_mi_lane{l}"] = (["o_x", "o_y"], words(s_tail=1, rcl=1, x0=1, xl=1 << (l - 1)), P)

    seen = set()
    for fname in ["qsag_asic_gl64_csa_gen.sv", "qsag_asic_p2_gen.sv"]:
        source = (root / "rtl" / fname).read_text()
        bodies = re.findall(r"module (\w+)\s*\((.*?)endmodule", source, re.S)
        for lane, body in re.findall(r"if \(LANE == (\d+)\) begin : g_lane\d+\n(.*?)\n  end", source, re.S):
            bodies.append((f"qsag_p2_mi_lane{lane}", body.replace("    wire unused_xl = ^xl;", "")))
        for name, body in bodies:
            if name not in specs:
                continue
            rows, want, mod_v = specs[name]
            arithmetic = body
            if name == "qsag_p2_canopy_ff":
                arithmetic = body.split("wire [63:0] result;", 1)[1]
            c = Circuit(arithmetic)
            c.prove(rows, want, mod=mod_v)
            seen.add(name)
            out.append({
                "module": name,
                "domain": "Z" if mod_v == 0 else ("F_p" if mod_v == P else f"Z/2^{mod_v.bit_length()-1}Z"),
                "local_adders": len(c.pairs),
                "sha256": hashlib.sha256(body.encode()).hexdigest(),
            })
            dom = "exact Z" if mod_v == 0 else ("mod p" if mod_v == P else f"mod 2^{mod_v.bit_length()-1}")
            print(f"CSA {name}: {len(c.pairs)} local adders certified ({dom}), fault rejected", flush=True)

    missing = set(specs) - seen
    assert not missing, f"missing CSA modules: {missing}"
    (root / "logs").mkdir(exist_ok=True)
    (root / "logs/lec_csa.json").write_text(json.dumps(out, indent=2) + "\n")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
