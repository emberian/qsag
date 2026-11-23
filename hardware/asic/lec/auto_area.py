#!/usr/bin/env python3
"""Autonomous-verifier area delta on the IHP SG13G2 typical-corner foundry library.

The SRAM and pre-existing datapath instances have identical implementations
in both builds. Keep those cells hierarchical. auto_regs is a wiring-only
view of pre-existing Q outputs. Both top controllers, domain ROM, side adders
and the complete autonomous engine are flattened and mapped to standard cells.
"""
from pathlib import Path
import os
import re
import subprocess

work = Path(os.environ["TMPDIR"]) / "d1-area"
work.mkdir(exist_ok=True)
lib = Path(os.environ.get("IHP_LIB", os.environ.get("PDK_ROOT", "/opt/pdk") + "/sg13g2_stdcell_typ_1p20V_25C.lib"))
rtl = Path("rtl")
fixed = ["qsag_asic_p2_shared", "qsag_fp5_seq", "qsag_keccak_2rpc", "qsag_sram_512k_4bank",
         "qsag_tower128_to_poly", "qsag_gf128_mul", "qsag_poly_to_tower128"]
texts = "\n".join(p.read_text() for p in rtl.glob("*.sv"))
texts=re.sub(r"//[^\n]*","",texts)
stubs = work/"fixed.sv"
stubs.write_text("\n".join("(* blackbox *) "+re.search(rf"\bmodule {name}\s*\(.*?\);",texts,re.S).group()
                           +"\nendmodule" for name in fixed))
files = " ".join(str(rtl/f) for f in ["qsag_asic_gl64_csa.sv","qsag_v2_domain.sv","qsag_auto_rom.sv",
                                      "qsag_auto_steps.sv","qsag_v2_auto_engine.sv","qsag_ni_asic_top.sv"])
def mapped(enable):
    log=work/f"area_{enable}.log"
    script=(f"plugin -i slang; read_slang -Irtl {stubs} {files} --top qsag_ni_asic_top -G AUTO_VERIFY={enable}; "
            f"synth -flatten -top qsag_ni_asic_top -noabc; dfflibmap -liberty {lib}; "
            f"abc -liberty {lib}; stat -liberty {lib}")
    with log.open("w") as f:
        subprocess.run(["yosys","-Q","-T","-p",script],stdout=f,stderr=subprocess.STDOUT,check=True)
    area=float(re.findall(r"Chip area for module .*?:\s*([\d.]+)", log.read_text())[-1])
    print(f"AUTO_VERIFY={enable} mapped hierarchical controller area {area:.3f} um^2",flush=True)
    return area
base=mapped(0)
full=mapped(1)
nand=float(re.search(r"\bcell\s*\(\s*\"?sg13g2_nand2_1\"?\s*\)\s*\{.*?\barea\s*:\s*([\d.]+)",lib.read_text(),re.S)[1])
delta=(full-base)/nand/1000
print(f"sg13g2_nand2_1 {nand:.3f} um^2. Enabled minus disabled {delta:.3f} kGE.")
if delta>=70:raise SystemExit("Exceeds 70 kGE.")
