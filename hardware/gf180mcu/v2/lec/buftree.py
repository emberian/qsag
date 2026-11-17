#!/usr/bin/env python3
"""Fanout trees on a synthesized netlist (Yosys write_verilog -noattr), before placement.

    python3 buftree.py <liberty> <in.v> <out.v> [--frac 0.35] [--wire-ff 5]

abc buffers and sizes the logic it maps. It does not see nets driven by flops, by module ports, by
cells instantiated in the RTL, or nets that cross a kept module boundary: the secret reset (5,800 pins),
the hold register's outputs, decoded control. This pass gives every such net a tree of buf_8 cells so
that no driver sees more than `frac` of its liberty max_capacitance, counting pin capacitance plus
`wire-ff` fF of wire per load pin (the same estimate as sta_gate.sh). It only inserts buffers; it never
changes a function, a cell that is there, or a name.

Not touched, on purpose:
  - clock nets (any net with a flop CLK, clock-gate CLK or latch E load): flop clocks belong to clock-tree
    synthesis; latch enables are driven by the sized per-row gates instantiated in dregg_regfile.sv;
  - every net driven by a cell instantiated by name in dregg_regfile.sv (the placed array: word lines,
    select lines, bit lines, clear lines, column tree). If one of those is overloaded the RTL is wrong, and
    sta_gate.sh reports it.
Modules are processed bottom-up; a submodule's port capacitance and output drive are carried to its parent.
"""
import re
import sys

P = "gf180mcu_fd_sc_mcu7t5v0__"
BUF = P + "buf_8"
RTL_OWNED_MODULES = ("dregg_regfile",)


def read_liberty(path):
    cells, cell, pin = {}, None, None
    for ln in open(path):
        m = re.match(r"\s*cell\s*\(\s*\"?([\w$]+)\"?\s*\)", ln)
        if m:
            cell = cells.setdefault(m.group(1), {})
            pin = None
            continue
        m = re.match(r"\s*pin\s*\(\s*\"?(\w+)\"?\s*\)", ln)
        if m and cell is not None:
            pin = cell.setdefault(m.group(1), {})
            continue
        if pin is not None:
            m = re.match(r"\s*(direction|capacitance|max_capacitance)\s*:\s*\"?([\w.+-]+)\"?\s*;", ln)
            if m and m.group(1) not in pin:
                pin[m.group(1)] = m.group(2) if m.group(1) == "direction" else float(m.group(2))
    return cells


def norm(e):
    return re.sub(r"\s+", "", e)


class Module:
    def __init__(self, name, text):
        self.name, self.text = name, text
        self.width = {}                    # wire / port name -> (msb, lsb)
        self.dir = {}                      # port name -> input | output
        for kind, rng, nm in re.findall(r"^\s*(input|output|inout|wire)\s*(\[\s*-?\d+\s*:\s*-?\d+\s*\])?\s*(\\\S+|[\w$]+)\s*;", text, re.M):
            nm = norm(nm)
            if rng:
                a, b = (int(x) for x in re.findall(r"-?\d+", rng))
                self.width[nm] = (a, b)
            else:
                self.width.setdefault(nm, None)
            if kind != "wire":
                self.dir[nm] = kind
        self.inst = []                     # [type, name, [[pin, expr], ...]]
        pat = re.compile(r"^  ([\w$\\]+) (\\\S+ |[\w$]+) ?\(\n((?:    \..*\n)*)  \);\n", re.M)
        self.spans = []
        for m in pat.finditer(text):
            pins = [[p, e] for p, e in re.findall(r"^\s*\.(\w+)\((.*?)\),?\s*$", m.group(3), re.M)]
            self.inst.append([m.group(1), m.group(2), pins])
            self.spans.append((m.start(), m.end()))
        self.assigns = re.findall(r"^\s*assign\s+(.*?)\s*=\s*(.*?);", text, re.M)
        self.new_wires, self.new_inst = [], []
        self.expr = {}                     # net key -> Verilog text

    def bits(self, expr):
        """Expression -> list of net keys (None for constant bits), most significant first."""
        e = expr.strip()
        if e.startswith("{"):
            out, depth, cur = [], 0, ""
            for ch in e[1:-1]:
                if ch == "{":
                    depth += 1
                if ch == "}":
                    depth -= 1
                if ch == "," and depth == 0:
                    out += self.bits(cur)
                    cur = ""
                else:
                    cur += ch
            return out + self.bits(cur)
        m = re.match(r"^(\d+)'", e)
        if m:
            return [None] * int(m.group(1))
        m = re.match(r"^(\\\S+|[\w$]+)\s*(?:\[\s*(-?\d+)\s*(?::\s*(-?\d+)\s*)?\])?$", e)
        if not m:
            raise ValueError(f"cannot parse net expression {expr!r}")
        nm = m.group(1)
        if m.group(2) is None:
            w = self.width.get(nm)
            if w is None:
                self.expr[nm] = nm + " "
                return [nm]
            a, b = w
        elif m.group(3) is None:
            a = b = int(m.group(2))
        else:
            a, b = int(m.group(2)), int(m.group(3))
        step = -1 if a >= b else 1
        out = []
        for i in range(a, b + step, step):
            k = f"{nm} [{i}]"
            self.expr[k] = k
            out.append(k)
        return out

    def emit(self):
        body, last = [], 0
        for (a, b), (typ, name, pins) in zip(self.spans, self.inst):
            body.append(self.text[last:a])
            body.append(f"  {typ} {name}(\n" + ",\n".join(f"    .{p}({e})" for p, e in pins) + "\n  );\n")
            last = b
        body.append(self.text[last:])
        t = "".join(body)
        i = t.rindex("endmodule")
        add = "".join(f"  wire {w};\n" for w in self.new_wires)
        add += "".join(f"  {BUF} {n} (\n    .I({a}),\n    .Z({z})\n  );\n" for n, a, z in self.new_inst)
        return t[:i] + add + t[i:]


def process(mod, lib, summ, frac, wire):
    """Insert trees in one module. Returns its port summary: input caps, output (max_cap, internal cap)."""
    find = {}

    def root(k):
        while find.get(k, k) != k:
            find[k] = find.get(find[k], find[k])
            k = find[k]
        return k
    for lhs, rhs in mod.assigns:
        try:
            a, b = mod.bits(lhs), mod.bits(rhs)
        except ValueError:
            continue
        if len(a) == len(b):
            for x, y in zip(a, b):
                if x is not None and y is not None:
                    find[root(x)] = root(y)
    nets = {}

    def net(k):
        return nets.setdefault(root(k), dict(loads=[], fixed=0.0, drv=None, clock=False, owned=False, key=k))
    bufpin = lib[BUF]
    for nm, d in mod.dir.items():
        for k in mod.bits(nm):
            n = net(k)
            if d == "input":
                n["drv"] = ("port", lib[P + "buf_2"]["Z"]["max_capacitance"])
            else:
                n["fixed"] += 0.02
    owned_mod = mod.name in RTL_OWNED_MODULES
    for ii, (typ, name, pins) in enumerate(mod.inst):
        if typ in lib:
            rtl_cell = owned_mod and not re.match(r"^_\d+_$", name.strip())
            for pi, (p, e) in enumerate(pins):
                b = mod.bits(e)
                if len(b) != 1 or b[0] is None:
                    continue
                n = net(b[0])
                info = lib[typ].get(p, {})
                if info.get("direction") == "output":
                    n["drv"] = (typ, info.get("max_capacitance", 0.1))
                    n["owned"] = rtl_cell
                elif info.get("direction") == "input":
                    n["loads"].append((ii, pi, info.get("capacitance", 0.005)))
                    if p == "CLK" or (p == "E" and "__lat" in typ):
                        n["clock"] = True
        elif typ in summ:
            for p, e in pins:
                s = summ[typ]
                for j, k in enumerate(mod.bits(e)):
                    if k is None:
                        continue
                    n = net(k)
                    if p in s["in"]:
                        n["fixed"] += s["in"][p][j]
                        n["clock"] = n["clock"] or s["clk"].get(p, False)
                    elif p in s["out"]:
                        mc, inner = s["out"][p][j]
                        n["drv"] = ("sub", mc)
                        n["fixed"] += inner
        else:
            raise SystemExit(f"buftree: unknown cell or module {typ}")
    count = 0
    for key, n in nets.items():
        if n["drv"] is None or n["clock"] or n["owned"]:
            continue
        loads = [(ii, pi, c) for ii, pi, c in n["loads"]]
        limit = frac * n["drv"][1]
        src = n["key"]
        total = lambda ls: sum(c for _, _, c in ls) + wire * len(ls) + n["fixed"]   # noqa: E731
        while total(loads) > limit and len(loads) > 1:
            cap_leaf = frac * bufpin["Z"]["max_capacitance"]
            groups, cur, cc = [], [], 0.0
            for ld in loads:
                c = ld[2] + wire
                if cur and cc + c > cap_leaf:
                    groups.append(cur)
                    cur, cc = [], 0.0
                cur.append(ld)
                cc += c
            groups.append(cur)
            if len(groups) >= len(loads):
                break
            loads = []
            for g in groups:
                w = f"_bt{mod.name[-3:]}{len(mod.new_wires)}_"
                mod.new_wires.append(w)
                mod.new_inst.append([f"_btc{mod.name[-3:]}{len(mod.new_inst)}_", None, w])
                bi = len(mod.new_inst) - 1
                for ii, pi, _ in g:
                    if ii < 0:
                        mod.new_inst[-ii - 1][1] = w            # a buffer of the level below
                    else:
                        mod.inst[ii][2][pi][1] = w
                loads.append((-bi - 1, 0, bufpin["I"]["capacitance"]))
                count += 1
        for ii, pi, _ in loads:
            if ii < 0:
                mod.new_inst[-ii - 1][1] = mod.expr[src]
        n["final"] = total(loads)
    # port summary
    s = dict(**{"in": {}, "out": {}, "clk": {}})
    for nm, d in mod.dir.items():
        ks = mod.bits(nm)
        if d == "input":
            s["in"][nm] = [nets[root(k)].get("final", sum(c for _, _, c in nets[root(k)]["loads"]) + wire * len(nets[root(k)]["loads"])) for k in ks]
            s["clk"][nm] = any(nets[root(k)]["clock"] for k in ks)
        else:
            s["out"][nm] = [((nets[root(k)]["drv"] or ("", 0.1))[1],
                             sum(c for _, _, c in nets[root(k)]["loads"]) + wire * len(nets[root(k)]["loads"])) for k in ks]
    return s, count


def main():
    args = sys.argv[1:]
    frac, wire = 0.35, 0.005
    pos = []
    while args:
        a = args.pop(0)
        if a == "--frac":
            frac = float(args.pop(0))
        elif a == "--wire-ff":
            wire = float(args.pop(0)) * 0.001
        else:
            pos.append(a)
    lib = read_liberty(pos[0])
    text = open(pos[1]).read()
    parts = re.split(r"(?m)^(?=module )", text)
    mods = []
    for part in parts:
        m = re.match(r"module\s+(\\\S+|[\w$]+)", part)
        mods.append(Module(norm(m.group(1)), part) if m else part)
    summ, todo = {}, [m for m in mods if isinstance(m, Module)]
    while todo:
        progress = False
        for m in list(todo):
            if all(t in lib or t in summ for t, _, _ in m.inst):
                summ[m.name], n = process(m, lib, summ, frac, wire)
                print(f"buftree {m.name}: {n} buffers")
                todo.remove(m)
                progress = True
        if not progress:
            raise SystemExit("buftree: unresolved modules: " + ", ".join(m.name for m in todo))
    with open(pos[2], "w") as fh:
        fh.write("".join(m.emit() if isinstance(m, Module) else m for m in mods))


if __name__ == "__main__":
    main()
