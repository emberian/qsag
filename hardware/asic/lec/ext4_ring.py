#!/usr/bin/env python3
"""Connect the nine-product arithmetic reference to schoolbook v^4=7."""
from pathlib import Path
import json
import re
import subprocess

work = Path("formal/ring")
work.mkdir(parents=True, exist_ok=True)
source = Path("rtl/qsag_asic_ext4_p2_gen.sv").read_text()
primitives = ["qsag_fp2_kara_re", "qsag_fp2_kara_im"] + [
    f"qsag_ext4_kara_r{i}" for i in range(4)
]
declarations = []
for name in primitives:
    head = re.search(rf"module {name}\s*\(.*?\);", source, re.S).group()
    declarations.append("(* blackbox *) " + head + "\nendmodule")
combine = re.search(r"module qsag_ext4_kara_combine\s*\(.*?endmodule", source, re.S).group()
(work / "combine.sv").write_text("\n".join(declarations + [combine]))
subprocess.run(["yosys","-Q","-q","-p",
    f"read_verilog -sv {work}/combine.sv; hierarchy -top qsag_ext4_kara_combine; write_json {work}/net.json"],check=True)
net = json.loads((work/"net.json").read_text())["modules"]["qsag_ext4_kara_combine"]
query = ["(set-logic QF_NIA)"]
for v in "abz":
    query.extend(f"(declare-const {v}{i} Int)" for i in range(4))
    if v != "z":
        # Input layout in the baseline lec_kara_in_gold equivalence.
        sums = [[0],[1],[0,1],[2],[3],[2,3],[0,2],[1,3],[0,1,2,3]]
        for i,group in enumerate(sums):
            terms = " ".join(f"{v}{k}" for k in group)
            query.append(f"(define-fun {v}q{i} () Int (+ {terms}))")
wire = {}
for name,width in [("p",9),("z",4)]:
    bits=net["ports"][name]["bits"]
    for i in range(width):
        value=f"(* aq{i} bq{i})" if name=="p" else f"z{i}"
        wire[tuple(bits[64*i:64*i+64])]=value
# These are the canonical-field contracts of the individually mitered leaves.
contract = {
    "qsag_fp2_kara_re":"(+ {m0} (* 7 {m1}))",
    "qsag_fp2_kara_im":"(- {m2} {m0} {m1})",
    "qsag_ext4_kara_r0":"(+ {re_a} (* 7 {im_b}) {z0})",
    "qsag_ext4_kara_r1":"(+ {im_a} {re_b} {z1})",
    "qsag_ext4_kara_r2":"(+ (- {re_m} {re_a} {re_b}) {z2})",
    "qsag_ext4_kara_r3":"(+ (- {im_m} {im_a} {im_b}) {z3})",
}
pending = dict(net["cells"])
while pending:
    before=len(pending)
    for inst,cell in list(pending.items()):
        connections=cell["connections"]
        pins={k:tuple(b) for k,b in connections.items() if k!="r"}
        if not all(b in wire for b in pins.values()):
            continue
        expression=contract[cell["type"]].format(**{k:wire[b] for k,b in pins.items()})
        wire[tuple(connections["r"])]=expression
        del pending[inst]
    assert len(pending)<before
physical = [0,2,1,3]
differences=[]
for k in range(4):
    terms=[f"z{physical[k]}"]
    for i in range(4):
        j=(k-i)%4
        terms.append(f"(* {7 if i+j>=4 else 1} a{physical[i]} b{physical[j]})")
    start=64*physical[k]
    actual=wire[tuple(net["ports"]["r"]["bits"][start:start+64])]
    differences.append(f"(distinct {actual} (+ {' '.join(terms)}))")
query += ["(assert (or "+" ".join(differences)+"))",
          "(check-sat-using (then (using-params simplify :som true) smt))"]
path = work/"identity.smt2"
path.write_text("\n".join(query))
r=subprocess.run(["z3",str(path)],capture_output=True,text=True,check=True)
print("Ext4 schoolbook vs nine products and RTL reconstruction:",r.stdout.strip())
assert r.stdout.strip()=="unsat"
