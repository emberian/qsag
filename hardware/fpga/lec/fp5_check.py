"""Compact quintic issue schedule and coefficient arithmetic cutpoints."""
from pathlib import Path
import subprocess


def run(L):
    root, out = Path(L.ROOT), Path(L.OUT)
    rtl = (root / "rtl/qsag_fp5_compact_bfly.sv").read_text()
    # Use the exact load-side function in a combinational cut. The oracle triples
    # by modular doubling followed by modular addition, in 65-bit arithmetic.
    start = rtl.index("    function automatic [63:0] triple")
    function = rtl[start:rtl.index("endfunction", start)+11]
    for mutant in (False, True):
        name = "fp5_triple" + ("_mutant" if mutant else "")
        f = function.replace("{1'b0,x,1'b0}", "{2'b0,x}") if mutant else function
        top = out / (name + ".sv")
        top.write_text("module probe(input [63:0] x,output [63:0] y);\n"
                       "localparam [63:0] P=qsag_ni_pkg::GL_P;\n" + f + "\nassign y=triple(x); endmodule\n")
        design = L.yosys_smt2(name,"probe",[L.PKG,str(top)])
        x, y = L.acc("x","s0"), L.acc("y","s0")
        p = L.bv(L.P,65)
        query = (design + "(declare-const s0 |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                 + f"(assert (bvult {x} {L.bv(L.P,64)}))\n"
                 + f"(define-fun norm ((a (_ BitVec 65))) (_ BitVec 65) (ite (bvuge a {p}) (bvsub a {p}) a))\n"
                 + f"(define-fun v () (_ BitVec 65) ((_ zero_extend 1) {x}))\n"
                 + f"(assert (distinct ((_ zero_extend 1) {y}) (norm (bvadd v (norm (bvadd v v))))))\n(check-sat)\n")
        for solver in ("bitwuzla","z3"):
            if not L.record(name+"_"+solver,"RTL triple against canonical modular addition",
                            "sat" if mutant else "unsat",query,prefer_bitwuzla=solver=="bitwuzla"):
                raise RuntimeError(name)
    # Check the accumulator's actual combinational reduction. For canonical
    # inputs, congruence and the canonical bound uniquely determine its output.
    acc_src = rtl[rtl.index("        wire [64:0] sum ="):rtl.index("        always_ff",rtl.index("        wire [64:0] sum ="))]
    probe = out / "fp5_acc.sv"
    probe.write_text("module probe(input [63:0] prev,product,output [63:0] y);\n"
                     "localparam [63:0] P=qsag_ni_pkg::GL_P;\n"+acc_src+"assign y=reduced; endmodule\n")
    ys = L.yosys_smt2("fp5_acc","probe",[L.PKG,str(probe)])
    a,b,y = (L.acc(w,"s0") for w in ("prev","product","y"))
    q = (ys+"(declare-const s0 |lec_top_s|)\n(assert (|lec_top_h| s0))\n"+
         f"(assert (and (bvult {a} {L.bv(L.P,64)}) (bvult {b} {L.bv(L.P,64)})))\n"+
         f"(define-fun s () (_ BitVec 65) (bvadd {L.zext(a,64,65)} {L.zext(b,64,65)}))\n"+
         f"(assert (not (and (bvult {y} {L.bv(L.P,64)}) (or (= s {L.zext(y,64,65)}) "+
         f"(= s (bvadd {L.zext(y,64,65)} {L.bv(L.P,65)}))))))\n(check-sat)\n")
    if not L.record("fp5_acc","RTL lane accumulator is canonical and congruent to prev+product","unsat",q):
        raise RuntimeError("fp5_acc")

    module = "qsag_fp5_compact_bfly"
    srcs = (root / "synth/srcs.txt").read_text().splitlines()
    for parallel in (0,1):
        for mutant in (False,True):
            name = f"fp5_issue_{1 if not parallel else 5}" + ("_mutant" if mutant else "")
            sources = list(srcs)
            if mutant:
                bad = out / "fp5_bad_wrap.sv"
                bad.write_text(rtl.replace("wire wrap = dest < j;", "wire wrap = dest <= j;"))
                sources[sources.index("rtl/"+module+".sv")] = str(bad)
            lanes = 5 if parallel else 1
            signals = ["issue","j","last_issue"]
            for n in range(lanes):
                signals += [f"g_mul[{n}].{w}" for w in ("i","wrap","dest")]
            smt = out / (name+".yosys.smt2")
            harness = out / "fp5_schedule_top.sv"
            harness.write_text(f"""module probe(input clk,rst,mac_valid,fold_start,output mac_done);
                {module} #(.TAW(3),.PARALLEL_5({parallel})) dut
                    (.clk,.rst,.mac_valid,.fold_start,.mac_done,.fold_log2n(6'd2),
                     .tw_en(1'b0),.tw_idx(3'd0),.tw_data(320'd0),
                     .in_lane_we(1'b0),.in_sel(2'd0),.in_lane_idx(3'd0),.in_lane_data(64'd0));
                endmodule""")
            cmds = ["read_verilog -sv "+" ".join(sources+[str(harness)]), "hierarchy -top probe",
                    "proc","flatten","delete -output probe/o:*",
                    "expose "+" ".join(f"probe/w:dut.{w}" for w in signals),
                    "opt_clean","rename -top lec_top",f"write_smt2 -wires {smt}"]
            subprocess.run(["yosys","-qp","; ".join(cmds)],cwd=root,check=True)
            steps = 25//lanes
            query = smt.read_text() + L.unroll(steps+2)
            eqs = []
            for t in range(steps+3):
                for pin,value in (("rst",t==0),("mac_valid",t==1),("fold_start",False)):
                    query += f"(assert (= {L.acc(pin,'s'+str(t))} {str(value).lower()}))\n"
            # For each issue tick and physical lane, the actual RTL must select
            # precisely the monomial reducing to output k in Fp[X]/(X^5-3).
            for step in range(steps):
                t = "s"+str(step+2)
                j = step%5
                eqs += [L.acc("dut.issue",t), f"(= {L.acc('dut.j',t)} {L.bv(j,3)})",
                        f"(= {L.acc('dut.last_issue',t)} {str(step==steps-1).lower()})"]
                for n in range(lanes):
                    k = n if parallel else step//5
                    i = (k-j)%5
                    for w,ref in (("i",L.bv(i,3)),("dest",L.bv(k,3)),("wrap",str(i+j>=5).lower())):
                        eqs.append(f"(= {L.acc(f'dut.g_mul[{n}].{w}',t)} {ref})")
            eqs.append(f"(not {L.acc('dut.issue','s'+str(steps+2))})")
            query += "(assert (not (and "+" ".join(eqs)+")))\n(check-sat)\n"
            if not L.record(name,"unrolled RTL issue sequence, cyclic indices and wrapped monomial weights",
                            "sat" if mutant else "unsat",query,prefer_bitwuzla=True):
                raise RuntimeError(name)


        # Independent unreduced degree-eight convolution, with one symbolic
        # monomial per input pair. Quotients allow any canonical multiply/add
        # implementation satisfying the preceding residue contracts.
        for k in range(5):
            decl = "(set-logic QF_LIA)\n(declare-const c Int)\n"
            folded = ["c"]
            terms = ["c"]
            for i in range(5):
                for j in range(5):
                    if (i+j)%5 != k: continue
                    m = f"m{i}{j}"
                    decl += f"(declare-const {m} Int)\n"
                    folded.append(m if i+j<5 else f"(* 3 {m})")
            for j in range(5):
                i=(k-j)%5
                weight = 3 if k<j else 1
                decl += f"(declare-const q{j} Int)\n"
                terms.append(f"(- (* {weight} m{i}{j}) (* {L.P} q{j}))")
            q = decl+f"(assert (distinct (mod (+ {' '.join(terms)}) {L.P}) (mod (+ {' '.join(folded)}) {L.P})))\n(check-sat)\n"
            if not L.record(f"fp5_convolution_{lanes}_{k}","schoolbook congruence modulo X^5-3 and p","unsat",q):
                raise RuntimeError("convolution")
