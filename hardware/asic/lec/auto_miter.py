#!/usr/bin/env python3
"""Prove local transition contracts of the three control units used by the ROM.

Insertion uses induction over the unread suffix. At entry the emitted prefix is
strictly sorted, smaller than both candidates, and its union with the carry and
unread suffix equals the original set plus the draw. A continuing step emits
one element, preserves this invariant, and shortens the suffix. Only append
increases the live count. The SMT witness w quantifies membership of *any*
32-bit index. The base case is the empty prefix. Every run has at most n+1
steps. Full-controller transactional behaviour is exercised in Verilator.
"""
from pathlib import Path
import re
import subprocess
import os

OUT = Path(os.environ["TMPDIR"]) / "auto-lec"
OUT.mkdir(exist_ok=True)
RTL = Path("rtl/qsag_auto_steps.sv")

def yosys(name, cmds):
    result = subprocess.run(["yosys", "-Q", "-T", "-p", cmds], capture_output=True, text=True, check=True)
    (OUT/f"{name}.log").write_text(result.stdout+result.stderr)
    return result.stdout

def net(top):
    p = OUT/f"{top}.smt2"
    yosys(top, f"read_verilog -sv {RTL}; prep -top {top}; write_smt2 -stbv {p}")
    return p.read_text()

def verify(name, smt, fault):
    for bad, expect in [(False, "unsat"), (True, "sat")]:
        query = OUT/f"{name}_{expect}.smt2"
        query.write_text((smt+fault).replace("FAULT", "true" if bad else "false")+"\n(check-sat)\n")
        for solver in ["z3", "bitwuzla"]:
            r = subprocess.run(["timeout", "60s", solver, str(query)], capture_output=True, timeout=65, text=True)
            if r.stdout.strip()!=expect or r.returncode not in (0,10,20):
                raise RuntimeError((name,solver,expect,r.stdout,r.stderr))
            print(f"{name} {'planted fault' if bad else 'RTL'} {solver} {expect.upper()}",flush=True)

def controls(top, ports):
    t=net(top)+f"\n(declare-const s |{top}_s|)\n"
    for name,typ in ports.items():
        t+=f"(define-fun {name} () {typ} (|{top}_n {name}| s))\n"
    return t

bv32="(_ BitVec 32)"
s=controls("qsag_auto_insert_step", {**dict.fromkeys(["carry","item","stored","next_carry"],bv32),
                                     **dict.fromkeys(["at_end","write_item","stop","grow"],"Bool")})
verify("sorted_insertion",s,"""
(declare-const w (_ BitVec 32))
(declare-const pre (_ BitVec 32))
(declare-const later (_ BitVec 32))
(declare-const count (_ BitVec 32))
(define-fun emit () (_ BitVec 32) (ite write_item stored item))
(define-fun output_carry () (_ BitVec 32) (ite FAULT item next_carry))
(define-fun delta () (_ BitVec 32) (ite grow #x00000001 #x00000000))
(assert (not (and
  (= stop (or at_end (= carry item)))
  (= (bvadd count delta) (ite at_end (bvadd count #x00000001) count))
  (=> at_end (and write_item (= emit carry) stop))
  (=> (and (not at_end) (= carry item)) (and stop (not write_item) (not grow)))
  (=> (not stop) (and
    (bvult emit output_carry)
    (=> (and (bvult pre item) (bvult pre carry)) (bvult pre emit))
    (=> (bvult item later) (bvult emit later))
    (= (or (= w carry) (= w item)) (or (= w emit) (= w output_carry))))))))
""")
s=controls("qsag_auto_canopy_step",{**dict.fromkeys(["node","next_node","parent"],bv32),
                                   **dict.fromkeys(["remaining","pair_nodes","consume","swap","bad"],"Bool")})
verify("steiner_step",s,"""
(declare-const cursor (_ BitVec 32))
(declare-const count (_ BitVec 32))
(declare-const active_digest (_ BitVec 400))
(declare-const adjacent_digest (_ BitVec 400))
(declare-const proof_digest (_ BitVec 400))
(assert (bvule cursor count))
(assert (= remaining (bvult cursor count)))
(define-fun pair () Bool (and (= ((_ extract 0 0) node) #b0)
                             (= next_node (bvadd node #x00000001))))
(define-fun valid () Bool (and (bvugt node #x00000001)
      (or (= next_node #x00000000) (bvugt next_node node))
      (or pair (bvult cursor count))))
(define-fun chosen () (_ BitVec 400) (ite pair_nodes adjacent_digest proof_digest))
(define-fun sibling () (_ BitVec 400) (ite pair adjacent_digest proof_digest))
(define-fun odd () Bool (= ((_ extract 0 0) node) #b1))
(define-fun increment () Bool (ite FAULT (not consume) consume))
(assert (not (and (= (not bad) valid)
 (=> valid (and (= parent (bvlshr node #x00000001))
   (= pair_nodes pair)
   (= (ite increment (bvadd cursor #x00000001) cursor) (ite pair cursor (bvadd cursor #x00000001)))
   (= (ite swap chosen active_digest) (ite odd sibling active_digest))
   (= (ite swap active_digest chosen) (ite odd active_digest sibling)))))))
""")
# Elaborate constant addresses through actual RTL. A single ROM produces all
# control words. Interpret the selected datapath operations over Fp[u]/(u^5-3).
top="qsag_auto_butterfly_step"
out=yosys(top,f"read_verilog -sv {RTL}; prep -top {top}; memory_map; opt; "+
          "; ".join(f"eval -set step {i} -show control" for i in range(12)))
words=[int(x,2) for x in re.findall(r"Eval result: .*?= 14'([01]+)",out)]
assert len(words)==12, out[-1200:]
P=0xffffffff00000001
s="(set-logic QF_BV)\n"
T="(_ BitVec 64)"
s+=f"(define-fun add ((a {T})(b {T})) {T} ((_ extract 63 0) (bvurem (bvadd ((_ zero_extend 1) a) ((_ zero_extend 1) b)) (_ bv{P} 65))))\n"
s+=f"(define-fun sub ((a {T})(b {T})) {T} (ite (bvult a b) (bvadd (bvsub a b) (_ bv{P} 64)) (bvsub a b)))\n"
s+=f"(define-fun mul ((a {T})(b {T})) {T} ((_ extract 63 0) (bvurem (bvmul ((_ zero_extend 64) a) ((_ zero_extend 64) b)) (_ bv{P} 128))))\n"
serial=0
def define(expr):
    global s,serial
    serial+=1
    name=f"v{serial}";s+=f"(define-fun {name} () {T} {expr})\n"
    return name
def elem(op,a,b):
    if op==2:
        result=[]
        for k in range(5):
            v="#x0000000000000000"
            for i in range(5):
                j=(k-i)%5
                prod=define(f"(mul {a[i]} {b[j]})")
                for _ in range(3 if i+j>=5 else 1):
                    v=define(f"(add {v} {prod})")
            result.append(v)
        return result
    fn=["add","sub",None,"mul"][op]
    return [define(f"({fn} {v} {b[0] if op==3 else b[i]})") for i,v in enumerate(a)]
regs=[]
for i in range(7):
    e=[]
    for j in range(5):
        if i>=5 and j: e.append("#x0000000000000000");continue
        v=f"in{i}_{j}";s+=f"(declare-const {v} {T})\n(assert (bvult {v} (_ bv{P} 64)))\n"
        e.append(v)
    regs.append(e)
a,b,theta,alpha,beta,x,inv=regs
half=["#x7fffffff80000001"]+["#x0000000000000000"]*4
regs=regs+[half,None,None]
for step,word in enumerate(words):
    op,d,l,r=word>>12,(word>>8)&15,(word>>4)&15,word&15
    rhs=regs[r]
    if step==5:
        # Misroute the second x operand to the inverse slot in the x^2 operation.
        rhs=[define(f"(ite FAULT {other} {correct})") for other,correct in zip(regs[6],rhs)]
    regs[d]=elem(op,regs[l],rhs)
f=elem(3,elem(0,a,b),half)
g=elem(3,elem(1,a,b),elem(3,inv,half))
v=elem(0,g,elem(2,elem(0,alpha,elem(3,beta,elem(3,x,x))),elem(0,f,elem(2,theta,g))))
# Use a canonical field witness with x=7 and x*x_inv=1 for the faulty circuit.
# The positive circuit is quantified over all canonical inputs.
for i,scalar in enumerate([3,7,1,2,1,7,pow(7,-1,P)]):
    for j in range(1 if i>=5 else 5):
        s+=f"(assert (=> FAULT (= in{i}_{j} (_ bv{scalar if j==0 else 0} 64))))\n"
verify("shifted_coset_butterfly",s,"(assert (or "+" ".join(
    f"(distinct {u} {z})" for u,z in zip(regs[0],v))+"))")

# Close the induction over the actual SRAM controller. Instruction ROM output
# is symbolic: all encodings of the source and destination register indices can
# issue the custom instruction. No firmware or particular run is assumed.
engine="qsag_v2_auto_engine"
rom_stub=OUT/"symbolic_rom.sv"
rom_header = Path("rtl/qsag_auto_rom.sv").read_text().split("module qsag_auto_rom", 1)[1].split(";", 1)[0]
rom_stub.write_text("module qsag_auto_rom" + rom_header + "; "
                    "(* anyseq *) wire [63:0] anyword; assign word_o=anyword; endmodule\n")
netfile=OUT/"index_controller.smt2"
yosys("index_controller", f"read_verilog -formal -sv -Irtl {rom_stub} {RTL} rtl/{engine}.sv; "
      f"prep -flatten -top {engine}; memory_map; opt; dffunmap; write_smt2 -wires -stbv {netfile}")
s=netfile.read_text()
states=re.search(r'typedef enum logic \[4:0\] \{([^}}]+)\} state_t',Path(f"rtl/{engine}.sv").read_text(),re.S)
ids={name.strip():i for i,name in enumerate(states[1].split(","))}
def at(signal,t):return f"(|{engine}_n {signal}| {t})"
def runtime(state,t):return f"(= {at('state',t)} (_ bv{ids[state]} 5))"
for t in ("issue","read","write","after"):
    s+=f"\n(declare-const {t} |{engine}_s|)\n(assert (not {at('rst',t)}))\n"
    s+=f"(assert (not {at('page_abort',t)}))\n"
def transition(a,b):return f"(|{engine}_t| {a} {b})"
# The issue and loop queries have separate start states. This lets the loop
# proof quantify over *every* reachable cursor, including the last of 267.
s+=f"""
(assert {runtime('EXEC','issue')})
(assert (= {at('op','issue')} (_ bv11 7)))
(assert (= {at('f7','issue')} (_ bv11 7)))
(assert (bvuge {at('x','issue')} {at('lower','issue')}))
(assert (= ((_ extract 2 0) {at('x','issue')}) #b000))
(assert (bvule {at('x','issue')} (_ bv524280 64)))
(assert (bvult ((_ extract 63 32) {at('y','issue')}) (_ bv267 32)))
(assert (bvule (bvadd {at('x','issue')} (bvshl (bvadd #x0000000000000001 ((_ zero_extend 32)
              ((_ extract 63 32) {at('y','issue')}))) #x0000000000000003)) (_ bv524288 64)))
(declare-const first |{engine}_s|)
(assert {transition('issue','first')})
(assert {runtime('INDEX_READ','read')})
(assert {transition('read','write')})
(assert {transition('write','after')})
(assert (= {at('rf_lanes','read')} {at('rf_lanes','write')}))
(define-fun len () (_ BitVec 32) ((_ extract 63 32) {at('y','read')}))
(define-fun pos () (_ BitVec 32) ((_ zero_extend 23) {at('index_pos','read')}))
(define-fun key () (_ BitVec 32) {at('carry','read')})
(define-fun item () (_ BitVec 32) ((_ extract 31 0) {at('aq','write')}))
(assert (bvult len (_ bv267 32)))
(assert (bvule pos len))
(define-fun last () Bool (= pos len))
(define-fun stop () Bool (or last (= key item)))
(define-fun do_write () Bool (or last (bvult key item)))
(define-fun location () (_ BitVec 16) (bvadd ((_ extract 18 3) {at('x','read')}) ((_ extract 15 0) pos)))
"""
properties=[
    runtime("INDEX_READ","first"),
    f"(= {at('index_pos','first')} (_ bv0 9))",
    f"(= {at('carry','first')} ((_ extract 31 0) {at('y','issue')}))",
    f"(= {at('saved','first')} {at('ins','issue')})",
    runtime("INDEX_WRITE","write"),
    f"(= {at('ae','read')} (not last))",
    f"(not {at('aw','read')})",
    f"(= {at('aa','read')} location)",
    f"(not {at('rf_write','read')})",
    f"(= {at('ae','write')} do_write)",
    f"(= {at('aw','write')} do_write)",
    f"(=> do_write (= (bvxor {at('aa','write')} (ite FAULT #x0001 #x0000)) location))",
    f"(=> do_write (= {at('ad','write')} ((_ zero_extend 32) key)))",
    f"(= {at('rf_write','write')} stop)",
    f"(=> stop (= {at('rf_index','write')} {at('rd','read')}))",
    f"(=> stop (= {at('rf_value','write')} ((_ zero_extend 32) (bvadd len (ite last #x00000001 #x00000000)))))",
    f"(=> stop {runtime('EXEC','after')})",
    f"(=> (not stop) {runtime('INDEX_READ','after')})",
    f"(=> (not stop) (= {at('carry','after')} (ite (bvult key item) item key)))",
    f"(=> (not stop) (= {at('index_pos','after')} (bvadd {at('index_pos','read')} (_ bv1 9))))",
]
verify("sorted_insertion_sram_controller",s,"(assert (not (and "+" ".join(properties)+")))")
