#!/usr/bin/env bash
# Regenerate both documents from accepted routes and completed verification runs.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 - <<'PY'
import hashlib
import json
import re
from pathlib import Path

build = Path("build")
logs = build / "verif_logs"
targets = {"gl64_dsp_mul":50, "p2_sbox7":50, "gf128_clmul":65, "keccak_compact":30,
           "p2_linear":45, "ext5_mac":25, "compact_top":20, "ecp5_fullrate_top":20}
evidence = []
summary = ["All frequencies below are final routed clock estimates on the LFE5U-85F-6BG381C, CABGA381, speed 6.",
           "", "| Timing wrapper | Constraint MHz | Routed MHz | Logic LUT4 | COMB | FF | DSP | BRAM | Packed bytes | Overused |",
           "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
for name, freq in targets.items():
    tag = "fmax_"+name
    prefix = build/"synth"/(tag+".pnr")
    report = json.loads(Path(str(prefix)+".report.json").read_text())
    route = Path(str(prefix)+".log").read_text()
    bit = Path(str(prefix)+".bit")
    size = bit.stat().st_size
    clock, = report["fmax"].values()
    overused = int(re.findall(r"\boverused=(\d+)",route)[-1])
    assert size and not overused and clock["achieved"] >= clock["constraint"] == freq
    assert Path(str(prefix)+".route-key").read_text().strip()
    used = [report["utilization"][k]["used"] for k in ("TRELLIS_COMB","TRELLIS_FF","MULT18X18D","DP16KD")]
    lut = int(re.search(r"logic LUTs:\s+(\d+)",route)[1])
    row = [f"[{tag}]({bit})",freq,f"{clock['achieved']:.6f}",lut,*used,size,overused]
    summary.append("| "+" | ".join(map(str,row))+" |")
    evidence.extend(Path(str(prefix)+suffix) for suffix in (".bit",".report.json",".log",".json",".yosys.log"))
summary += ["","| Verilator suite | Checks | Mismatches | Simulated clocks | Connected workload TOTAL_CYCLES |",
            "|---|---:|---:|---:|---:|"]
ops = {}
profiles = [("units","UNITS"),("compact","COMPACT"),("ecp5_fullrate","ECP5_FULLRATE"),("top","TOP"),("pipe","PIPE")]
for step,tag in profiles:
    log = logs/f"verify_{step}.log"
    checks,bad,cycles = map(int,re.search(r"(?:TOP|UNITS): (\d+) checks, (\d+) mismatches, (\d+) clocks simulated",log.read_text()).groups())
    assert checks and not bad
    total = "—"
    if step!="units":
        report = (build/f"trace_report_{tag}.txt").read_text()
        total = re.search(r"TOTAL_CYCLES (\d+)",report)[1]
        ops[tag] = dict(re.findall(r"(0x\w+) OP_CYCLES (\d+)", report))
    evidence.append(log)
    summary.append(f"| [{tag}]({log}) | {checks:,} | {bad} | {cycles:,} | {total} |")

formal = (logs/"lec_all.log").read_text()
counts = []
for group in ("gl","glmut","ext5","gf","comp","tower","anf","xbank"):
    rows = (build/"lec"/f"results_{group}.txt").read_text().splitlines()
    assert rows and all(r.startswith("PASS\t") for r in rows), group
    if group!="anf": assert f"LEC {group}: {len(rows)} passed, 0 non-PASS" in formal,group
    counts.append((group,len(rows)))
formal_total = sum(n for _,n in counts)
lint = (logs/"lint.log").read_text()
assert "FAILED" not in lint and "%Warning" not in lint and "0 warnings" in lint
equiv = (logs/"ecp5_opt_equiv.log").read_text()
for tag in ("ext5_mac","compact_top","ecp5_fullrate_top"): assert f"[PASS] fmax_{tag}:" in equiv
summary += ["",f"Verilator lint passed. All {formal_total} formal and ANF checks returned their expected result, including deliberately faulty designs. "
            "The DSP register-packing checks passed on all three optimized wrappers. "
            f"[Lint]({logs}/lint.log) · [Formal]({logs}/lec_all.log) · [ANF]({logs}/anf_check.log) · [Packing equivalence]({logs}/ecp5_opt_equiv.log)"]
readme = Path("README.md")
text = readme.read_text()
a,b = "<!-- measured:start -->","<!-- measured:end -->"
readme.write_text(text[:text.index(a)+len(a)]+"\n"+"\n".join(summary)+"\n"+text[text.index(b):])

doc = ["# FPGA implementation results","",*summary,"","## Placement comparison","",
       "Each paired trial used seed 1, a 20 MHz clock, HeAP beta 0.65 and timing-driven router2. The unconstrained trials used two threads and the floorplanned trials used one. The floorplanner groups local DSP registers and assigns EBR sites. A stopped trial has no routed Fmax.","",
       "| Wrapper | Placement | Last router iteration | Overused | Routed MHz |","|---|---|---:|---:|---:|"]
for tag in ("fmax_compact_top","fmax_ecp5_fullrate_top"):
    for mode in ("heap","plan"):
        stem = build/"synth"/"bench"/(tag+"-"+mode+".pnr")
        log = logs/(tag+"-heap.log") if mode=="heap" else Path(str(stem)+".log")
        report = Path(str(stem)+".report.json")
        last, over = re.findall(r"iter=(\d+) wires=\d+ overused=(\d+)",log.read_text())[-1]
        mhz = "stopped" if not report.exists() else f"{next(iter(json.loads(report.read_text())['fmax'].values()))['achieved']:.6f}"
        doc.append(f"| {tag} | [{mode}]({log}) | {last} | {over} | {mhz} |")
doc += ["","## Differential workload","","The deterministic connected workload starts with 16 quintic gate evaluations. Its transcript supplies challenges for an in-place four-variable fold and four linked sumcheck rounds. The openings feed TurboSHAKE256 and Poseidon2 root checks. This measures the generated fixture. A serialized production proof and independently supplied public root are required for a production replay.","",
        "| Opcode | "+" | ".join(ops)+" |","|---|"+"---:|"*len(ops)]
for op in sorted(set().union(*ops.values())):
    doc.append("| "+op+" | "+" | ".join(table.get(op,"0") for table in ops.values())+" |")
doc += ["","OP_CYCLES sums completed commands by opcode. TOTAL_CYCLES counts clocks with active engines, including background chain work.",
        "","## Formal coverage","","| Group | Passing obligations |","|---|---:|"]
for group,n in counts: doc.append(f"| [{group}](build/lec/results_{group}.txt) | {n} |")
doc += ["","The compact arithmetic checks cover modular tripling, canonical accumulation and all 25 monomial issue positions in each schedule. Mutants change the wrap comparison or the triple and must produce counterexamples. GF(2) ANF compares the pipeline against the polynomial definition across every input coefficient.","",
        "The DSP equivalence gate checks a ten-clock sequential primitive miter with Z3 and Bitwuzla. For each optimized wrapper it checks the complete mapped netlist at the register cutpoints, including clock, enable, reset, deleted FF fanout and every surviving non-DSP cell.",""]
evidence += [logs/f for f in ("lint.log","lec_all.log","anf_check.log","ecp5_opt_equiv.log")]
manifest = logs/"signoff.sha256"
manifest.write_text("".join(hashlib.sha256(path.read_bytes()).hexdigest()+"  "+str(path)+"\n" for path in evidence))
doc += [f"[SHA-256 checksums of the eight mapped netlists, packed images, reports and verification logs]({manifest})",""]
Path("RESULTS.md").write_text("\n".join(doc))
PY
