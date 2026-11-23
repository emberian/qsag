"""Map both complete controller configurations and time the mapped hierarchical nets.

Only the four dual-port SRAM banks are black boxes. The initialized synchronous
ROM is mapped to standard cells and included in both area and timing.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
WORK = Path(os.environ["TMPDIR"]) / "d1-foundry"
WORK.mkdir(exist_ok=True)
PDK = Path(os.environ.get("PDK_ROOT", "/opt/pdk"))
TOP = "qsag_ni_asic_top"
SRAM = "sram_dp_64x16384_bank"
STA = os.environ.get("OPENSTA_BIN", "sta")
CORNERS = {
    "ihp": ["sg13g2_stdcell_typ_1p20V_25C", "sg13g2_stdcell_fast_1p32V_m40C",
            "sg13g2_stdcell_slow_1p08V_125C"],
    "sky": ["sky130_fd_sc_hd__tt_025C_1v80"],
}
os.chdir(ROOT)

def run(tool, script, output):
    path = output.with_suffix(".ys" if tool == "yosys" else ".tcl")
    path.write_text(script)
    cmd = [tool, "-Q", "-T", "-s"] if tool == "yosys" else [tool, "-exit"]
    with output.open("w") as f:
        p = subprocess.run([*cmd, str(path)],
                           stdout=f, stderr=subprocess.STDOUT)
    log = output.read_text()
    if p.returncode or "Error:" in log:
        raise RuntimeError(log[-3000:])

def report_area(stats, nand):
    modules = {k.lstrip("\\"): v for k, v in stats["modules"].items()}
    # With linked Liberty cells, Yosys reports inclusive module areas.
    total = modules[TOP]["area"] / nand / 1000
    rom = modules.get(ROM, {}).get("area", 0) / nand / 1000
    engine = modules[ENGINE]["area"] / nand / 1000 - rom if ENGINE in modules else 0
    assert abs(modules[TOP]["area"] - stats["design"]["area"]) < 1
    assert stats["design"]["num_cells_by_type"][SRAM] == 4
    return total, engine, rom

# Bound hierarchy at reusable arithmetic blocks. This lets ABC optimize each
# complete arithmetic cone once, including its generated internal hierarchy.
ENGINE = "qsag_v2_auto_engine"
ROM = "qsag_auto_rom"
LEAVES = ["qsag_gl64_mul_csa", "qsag_p2_me", "qsag_p2_mi_tail", "qsag_p2_mi_apply",
          "qsag_p2_canopy_ff",
          "qsag_keccak_round", "qsag_gf128_mul", "qsag_tower128_to_poly", "qsag_poly_to_tower128"]

def map_module(name, enable, lib, folder):
    prefix = folder / (name + (str(enable) if name == TOP else ""))
    net = prefix.with_suffix(".v")
    gl = ["qsag_asic_gl64_csa.sv", "qsag_asic_gl64_csa_gen.sv"]
    if name == TOP:
        files = sorted(Path("rtl").glob("*.sv"))
        cuts = LEAVES + [ENGINE, SRAM]
    elif name == ENGINE:
        files = [Path("rtl") / f for f in ["qsag_auto_steps.sv", ROM + ".sv", ENGINE + ".sv"]]
        cuts = [ROM]
    elif name == ROM:
        files, cuts = [Path("rtl") / (ROM + ".sv")], []
    else:
        files = [Path("rtl") / f for f in gl + ["qsag_asic_p2_gen.sv",
                 "qsag_asic_keccak_clmul.sv", "qsag_asic_tower_maps_gen.sv"]]
        cuts = []
    options = " ".join("--blackboxed-module " + m for m in cuts)
    param = f"-G AUTO_VERIFY={enable}" if name == TOP else ""
    # Skip FRAIG on the generated partial-product and carry-save networks.
    # Their Boolean structure already comes from the arithmetic generator.
    abc_script = "" if name in (ENGINE, ROM) else " -script +strash;&get,-n;&dch,-f;&nf;&put"
    script = f"""plugin -i slang
read_slang -Irtl {options} {' '.join(map(str, files))} --top {name} {param}
synth -top {name} -flatten -noabc
dfflibmap -liberty {lib}
abc -liberty {lib}{abc_script}
setundef -zero
opt_clean
select {name}
write_verilog -noattr -noexpr -nodec -selected {net}
"""
    digest = hashlib.sha256(script.encode())
    for path in [*files, *sorted(Path("rtl").glob("*.svh")), lib]:
        digest.update(path.read_bytes())
    stamp = prefix.with_suffix(".sha256")
    if not (net.exists() and stamp.exists() and stamp.read_text() == digest.hexdigest()):
        run("yosys", script, prefix.with_suffix(".log"))
        stamp.write_text(digest.hexdigest())
    return net

def main():
    print(subprocess.check_output(["yosys", "-V"], text=True).strip())
    print("OpenSTA", subprocess.check_output([STA, "-version"], text=True).strip())
    print("TT mapping, 100 ns ideal clock, zero I/O delays, four SRAM timing/area black boxes.")
    exceeded = []
    for name, corners in CORNERS.items():
        folder = WORK / name
        folder.mkdir(exist_ok=True)
        lib = PDK / (corners[0] + ".lib")
        cell = "sg13g2_nand2_1" if name == "ihp" else "sky130_fd_sc_hd__nand2_1"
        nand = float(re.search(rf'cell\s*\(\s*"?{cell}"?\s*\).*?\barea\s*:\s*([\d.]+)',
                               lib.read_text(), re.S)[1])
        nets = [map_module(m, 1, lib, folder) for m in [ENGINE, ROM, *LEAVES]]
        for enable in [1, 0]:
            top = map_module(TOP, enable, lib, folder)
            prefix = folder / f"linked{enable}"
            stats = prefix.with_suffix(".json")
            gates = prefix.with_suffix(".v")
            # Read the explicit interface of the SRAM black box. Its four
            # instances are counted and excluded from standard-cell area.
            stub = re.search(r"module sram_dp_64x16384_bank .*?endmodule",
                             Path("rtl/sram_dp_blackbox.sv").read_text(), re.S)[0]
            bb = prefix.with_suffix(".bb.v")
            bb.write_text(stub + "\n")
            # The top carries AW on the hierarchical instance. Verify it matches
            # the specialized 16-bit engine before linking the mapped module.
            reads = "\n".join(f"read_verilog {path}" for path in [*nets, top])
            run("yosys", f"""read_liberty -lib {lib}
read_verilog -lib {bb}
{reads}
select -assert-count {enable} t:{ENGINE} r:AW=16 %i
setparam -unset AW t:{ENGINE}
hierarchy -check -top {TOP}
tee -o {stats} stat -json -liberty {lib}
write_verilog -noattr -noexpr -nodec {gates}
""", prefix.with_suffix(".log"))
            total, engine, rom = report_area(json.loads(stats.read_text()), nand)
            print(f"{name} AUTO_VERIFY={enable} NAND2={nand} um^2 total={total:.3f} kGE "
                  f"ROM={rom:.3f} kGE engine_excluding_ROM={engine:.3f} kGE", flush=True)
            if bool(engine) != bool(enable) or bool(rom) != bool(enable):
                raise RuntimeError("Engine/ROM presence disagrees with AUTO_VERIFY")
            if total >= 954 or engine >= 25:
                exceeded.append((name, enable, total, engine))
            for corner in corners:
                out = WORK / f"{corner}_{enable}.log"
                run(STA, f"""read_liberty {PDK}/{corner}.lib
read_verilog {prefix}.bb.v
read_verilog {gates}
link_design {TOP}
create_clock -name core -period 100 [get_ports clk]
set_input_delay 0 -clock core [get_ports {{cmd_valid cmd_op* cmd_idx* cmd_addr* cmd_data*}}]
set_output_delay 0 -clock core [get_ports {{cmd_ready rsp_valid rsp_data*}}]
set_false_path -from [get_ports rst]
report_clock_min_period -digits 4
report_worst_slack -max -digits 4
report_checks -path_delay max -group_path_count 1 -digits 4
exit
""", out)
                result = out.read_text()
                if "period_min" not in result or "black box" in result.lower():
                    raise RuntimeError(f"Check clock paths and linkage in {out}")
                print(corner, f"AUTO_VERIFY={enable}", *[line for line in result.splitlines()
                      if "period_min" in line or "worst slack" in line], flush=True)
                print("\n".join(line for line in result.splitlines() if
                                line.startswith(("Startpoint:", "Endpoint:"))), flush=True)
    if exceeded:
        raise SystemExit(f"Area target exceeded: {exceeded}")

if __name__ == "__main__":
    main()
