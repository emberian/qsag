#!/usr/bin/env python3
"""Unroll the actual clocked RTL, constant-fold controls, then ask SMT for a mismatch."""
import json
import re
from pathlib import Path
import subprocess
import sys

W=Path("formal") / sys.argv[1]
W.mkdir(parents=True,exist_ok=True)
RTL="rtl/qsag_asic_gl64_csa.sv rtl/qsag_asic_gl64_csa_gen.sv rtl/qsag_asic_ext4_p2_gen.sv"
def yosys(tag,commands):
    with (W/f"{tag}.log").open("w") as log:
        subprocess.run(["yosys","-Q","-T","-p",commands],stdout=log,stderr=subprocess.STDOUT,check=True)
def transition(top,files):
    net=W/f"{top}.json"
    options = "--no-implicit-memories" if top == "qsag_asic_ext4_p2_shared" else ""
    yosys(top,f"plugin -i slang; read_slang {options} -Irtl {files} --top {top}; proc; memory; opt; dffunmap; opt_clean; write_json {net}")
    design=json.loads(net.read_text())
    module=design["modules"][top]
    # Turn each DFF Q into this cycle's state input and its D into the
    # next-state output. Keep every combinational cell and all bit connections.
    regs=[]
    for name,c in list(module["cells"].items()):
        if c["type"]!="$dff":
            assert not any(x in c["type"] for x in ("dff","latch","mem")),c["type"]
            continue
        i=len(regs)
        assert int(c["parameters"]["CLK_POLARITY"],2)==1
        assert c["connections"]["CLK"]==module["ports"]["clk"]["bits"]
        for pin,direction in [("Q","input"),("D","output")]:
            bits=c["connections"][pin]
            module["ports"][f"{pin}{i}"]={"direction":direction,"bits":bits}
            module["netnames"][f"{pin}{i}"]={"hide_name":0,"bits":bits,"attributes":{}}
        regs.append(len(bits))
        del module["cells"][name]
    assert regs
    module["attributes"].pop("top",None)
    (W/"transition.json").write_text(json.dumps(design))
    return module["ports"],regs

def decl(w,name):return f"wire [{w-1}:0] {name};"
def instance(top,ports,regs,t,inputs,body):
    pins=[]
    for port,info in ports.items():
        width=len(info["bits"])
        if port.startswith("Q") and port[1:].isdigit():
            name=f"d{t-1}_{port[1:]}" if t else f"init_{port[1:]}"
        elif port.startswith("D") and port[1:].isdigit():
            name=f"d{t}_{port[1:]}";body.append(decl(width,name))
        elif info["direction"]=="output":
            name=f"{port}_{t}";body.append(decl(width,name))
        else:
            name=inputs.get(port,f"{width}'d0")
        pins.append(f".{port}({name})")
    body.append(f"{top} s{t}("+",".join(pins)+");")
def leaf_ports():
    # All these leaves are deterministic combinational RTL. Preserve the
    # complete ordered input tuple; do not approximate arithmetic by XOR.
    names = ("qsag_ext4_kara_inputs", "qsag_ext4_kara_combine", "qsag_gl64_mul_csa",
             "qsag_gl64_addsub", "qsag_p2_me", "qsag_p2_mi_apply", "qsag_p2_mi_tail",
             "qsag_p2_canopy_ff", "qsag_p2_rc")
    rtl = "\n".join(Path(f).read_text() for f in RTL.split())
    declarations = []
    for name in names:
        head = re.search(rf"module {name}\s*\(.*?\);", rtl, re.S).group()
        declarations.append("(* blackbox *) " + head + "\nendmodule")
    path = W/"leaves.sv"
    path.write_text("\n".join(declarations))
    return path, set(names)

def bind_leaves(names):
    # After unrolling the scheduler, cut each leaf at its actual ports.
    # The same SMT function interprets a leaf in both gate and gold circuits.
    net = json.loads((W/"network.json").read_text())
    module = net["modules"]["harness"]
    definitions = {}
    assumptions = []
    for n,(name,cell) in enumerate(list(module["cells"].items())):
        kind=cell["type"]
        if kind not in names:
            continue
        args=[]; types=[]; outputs=[]
        for pin in sorted(cell["connections"]):
            bits=cell["connections"][pin]
            width=len(bits); port=f"leaf{n}_{pin}"
            leaf_out=cell["port_directions"][pin]=="output"
            module["ports"][port]={"direction":"input" if leaf_out else "output","bits":bits}
            module["netnames"][port]={"hide_name":0,"bits":bits,"attributes":{}}
            sig=f"(|harness_n {port}| s)"
            if width==1: sig=f"(ite {sig} #b1 #b0)"
            if leaf_out: outputs.append((sig,width))
            else: args.append(sig);types.append(f"(_ BitVec {width})")
        assert len(outputs)==1
        result,width=outputs[0]
        definitions[kind]=f"(declare-fun {kind} ({' '.join(types)}) (_ BitVec {width}))"
        assumptions.append(f"(assert (= {result} ({kind} {' '.join(args)})))")
        del module["cells"][name]
    assert "qsag_gl64_mul_csa" in definitions
    (W/"cut.json").write_text(json.dumps(net))
    return "\n".join(definitions.values())+"\n"+"\n".join(assumptions)+"\n"

def make(mode):
    shared=mode=="shared"
    top="qsag_asic_ext4_p2_shared" if shared else "qsag_fp5_seq"
    files=(RTL if shared else "rtl/qsag_asic_gl64_csa.sv")+f" rtl/{top}.sv"
    if shared:
        leaf_file, names = leaf_ports()
        files = f"{leaf_file} rtl/{top}.sv"
    ports,regs=transition(top,files)
    args=[f"input wire [{w-1}:0] init_{i}" for i,w in enumerate(regs)]
    body=[];bad=[]
    if shared:
        args+=["input wire [767:0] basis","input wire [2:0] op","input wire [63:0] side_a,side_b"]
        for t in range(4):
            control={"rst":str(int(t==0)),"wr_data":"basis","wr_en":"12'hfff" if t==1 else "0"}
            if t==2:
                control.update(fp5_active="(op==5)",fp5_a="side_a",fp5_b="side_b")
                for i,name in enumerate(["emuladd","eadd","esub","emulbase","glmul"]):
                    control["op_"+name]=f"(op==3'd{i})"
            instance(top,ports,regs,t,control,body)
        body+=["wire [767:0] gold; shared_gold refmath(basis,op,gold);"]
        body+=["wire [63:0] scalar_side; qsag_gl64_mul_csa side(side_a,side_b,scalar_side);"]
        bad=["st_o_3 != gold","busy_3","done_3","(op==5 && fp5_product_2!=scalar_side)"]
    else:
        args += ["input wire [319:0] a,r,z","input wire [1599:0] terms","input wire [15:0] base"]
        t=0
        def step(**ctl):
            nonlocal t
            instance(top,ports,regs,t,dict(a="a",r="r",base="base",**ctl),body)
            t+=1
            return t-1
        step(rst="1");step(start="1")
        for k in range(5):
            rd=step()
            bad += [f"!rd_a_{rd}",f"addr_a_{rd} != 16'(base+{k})"]
            step(qa=f"z[{64*k}+:64]")
            prev=f"z[{64*k}+:64]"
            for i in range(5):
                j=(k-i)%5
                prod=f"terms[{64*(5*i+j)}+:64]"
                for rep in range(3 if i+j>=5 else 1):
                    n=step(product=prod)
                    bad += [f"mul_a_{n} != a[{64*i}+:64]",f"mul_b_{n} != r[{64*j}+:64]"]
                    name=f"sum_{k}_{i}_{rep}"
                    body.append(f"wire [63:0] {name}; qsag_gl64_addsub ref_{n}({prev},{prod},1'b0,{name});")
                    prev=name
            body.append(f"wire [63:0] gold{k} = {prev};")
        n=step()
        bad += [f"lane_we_{n} != 5'h1f",f"lane_data_{n} != {{gold4,gold3,gold2,gold1,gold0}}"]
        for tick in range(n):
            bad.extend([f"|lane_we_{tick}",f"done_{tick}"] if tick else [])
        n=step();bad += [f"!done_{n}",f"checked_{n}"]
    args.append("output wire bad")
    body.append("assign bad = "+" || ".join("("+x+")" for x in bad)+";")
    (W/"harness.sv").write_text("module harness("+",".join(args)+");\n"+"\n".join(body)+"\nendmodule\n")
    # read_slang resolves all references at elaboration. Use the ordinary
    # Yosys frontend for the simple structural harness after loading the core.
    if shared:
        yosys("shared_network", f"read_json {W}/transition.json; read_verilog -sv lec/shared_gold.sv {W}/harness.sv; hierarchy -top harness; proc; flatten; opt -full; opt_clean -purge; write_json {W}/network.json")
        assumptions = bind_leaves(names)
        yosys("shared_smt", f"read_json {W}/cut.json; hierarchy -top harness; write_smt2 -stbv {W}/{mode}.smt2")
    else:
        assumptions = ""
        yosys(mode+"_core",f"read_json {W}/transition.json; write_verilog -noattr {W}/step.v")
        yosys(mode+"_smt",f"read_verilog {W}/step.v; read_verilog -sv -Irtl rtl/qsag_asic_gl64_csa.sv {W}/harness.sv; hierarchy -top harness; proc; flatten; opt -full; opt_clean -purge; write_smt2 -stbv {W}/{mode}.smt2")
    smt=(W/f"{mode}.smt2").read_text()
    cases=range(6) if shared else [None]
    for op in cases:
        query=smt+"\n(declare-const s |harness_s|)\n"
        query+=assumptions
        if op is not None:query+=f"(assert (= (|harness_n op| s) (_ bv{op} 3)))\n"
        if shared:
            witness = subprocess.run(["z3", "-in"], input=query+"(check-sat)\n",
                                     capture_output=True, text=True, timeout=180, check=True)
            assert witness.stdout.strip() == "sat", "unreachable opcode or inconsistent leaf contracts"
            print(mode,op,"reachability",witness.stdout.strip(),flush=True)
        query+="(assert (|harness_n bad| s))\n(check-sat)\n"
        path=W/f"query_{mode}_{op}.smt2";path.write_text(query)
        for solver in ["z3","bitwuzla"]:
            result=subprocess.run([solver,str(path)],capture_output=True,text=True,timeout=180)
            print(mode,op,solver,result.stdout.strip(),result.stderr[:150],flush=True)
            assert result.stdout.strip()=="unsat"
if __name__=="__main__":make(sys.argv[1])
