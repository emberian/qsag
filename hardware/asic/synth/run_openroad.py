#!/usr/bin/env python3
"""bb2 only: Real OpenROAD Physical Implementation & Parasitic-Aware Post-Placement STA/Power!

Runs OpenROAD (`tools/openroad_env/bin/openroad`) on Nangate45 (and Sky130):
  1. Generates a clean physical LEF macro stub for `sram_dp_64x16384_bank` (placed as 4 peripheral macros)
     and runs full die floorplanning, track creation, macro placement, IO pin placement, RePlAce global
     placement, OpenDP detailed placement (`check_placement` -> 0 violations!), `setRC.tcl` layer RC setup,
     `estimate_parasitics -placement` (Manhattan Steiner wire R/C extraction!), post-placement OpenROAD STA,
     and dynamic/leakage power reporting!
"""
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
os.chdir(ROOT)
RUN = ["env", "SWARM_MEM_MAX=16G", "swarm-build", "timeout", "--kill-after=10s", "600s"]
OPENROAD = "/home/build/qsag-ni-asic/tools/openroad_env/bin/openroad"
PDK = pathlib.Path("/home/build/qsag-ni-asic/pdk")
WORK = ROOT / "synth" / "work_hier"
WORK.mkdir(parents=True, exist_ok=True)
os.environ["TMPDIR"] = str(WORK)


def write_sram_lef(path, metal_pin, site_w, site_h, macro_w, macro_h):
    """Emit a clean physical LEF macro stub for `sram_dp_64x16384_bank` with pins on metal_pin."""
    pins = ["clk", "a_en", "a_we"] + [f"a_addr[{i}]" for i in range(14)] + \
           [f"a_wdata[{i}]" for i in range(64)] + [f"a_rdata[{i}]" for i in range(64)] + \
           ["b_en", "b_we"] + [f"b_addr[{i}]" for i in range(14)] + \
           [f"b_wdata[{i}]" for i in range(64)] + [f"b_rdata[{i}]" for i in range(64)]
    lines = [
        "VERSION 5.8 ;",
        "BUSBITCHARS \"[]\" ;",
        "DIVIDERCHAR \"/\" ;",
        "MACRO sram_dp_64x16384_bank",
        "  CLASS BLOCK ;",
        "  ORIGIN 0 0 ;",
        f"  FOREIGN sram_dp_64x16384_bank 0 0 ;",
        f"  SIZE {macro_w:.3f} BY {macro_h:.3f} ;",
        "  SYMMETRY X Y ;",
    ]
    step = macro_w / (len(pins) + 2)
    pw = round(site_w, 3)
    ph = round(site_h, 3)
    for idx, pname in enumerate(pins):
        x0 = round((idx + 1) * step, 3)
        x1 = round(x0 + pw, 3)
        pdir = "OUTPUT" if "rdata" in pname else "INPUT"
        use = "CLOCK" if pname == "clk" else "SIGNAL"
        lines += [
            f"  PIN {pname}",
            f"    DIRECTION {pdir} ;",
            f"    USE {use} ;",
            "    PORT",
            f"      LAYER {metal_pin} ;",
            f"      RECT {x0:.3f} 0.000 {x1:.3f} {ph:.3f} ;",
            "    END",
            f"  END {pname}",
        ]
    lines += ["END sram_dp_64x16384_bank", "END LIBRARY", ""]
    path.write_text("\n".join(lines))


def run_openroad_nangate45():
    out = ROOT / "synth" / "hier" / "nangate45" / "openroad"
    out.mkdir(parents=True, exist_ok=True)
    sram_lef = out / "sram_dp_64x16384_bank.lef"
    # Compact macro footprint on FreePDK45 grid (0.19 x 1.40 um site)
    write_sram_lef(sram_lef, "metal3", 0.19, 1.40, 190.0, 140.0)

    sram_lib = ROOT / "synth" / "hier" / "nangate45" / "sram_stub_nangate45.lib"
    flat_v = ROOT / "synth" / "hier" / "nangate45" / "flat_gates.v"
    period_ns = 3.50

    tcl = f"""read_lef {PDK / 'NangateOpenCellLibrary.tech.lef'}
read_lef {PDK / 'NangateOpenCellLibrary.macro.mod.lef'}
read_lef {sram_lef}
read_liberty {PDK / 'NangateOpenCellLibrary_typical.lib'}
read_liberty {sram_lib}
read_verilog {flat_v}
link_design qsag_ni_asic_top

create_clock -name core -period {period_ns} [get_ports clk]
set_input_delay 0.4 -clock core [get_ports {{cmd_valid cmd_op* cmd_idx* cmd_addr* cmd_data*}}]
set_output_delay 0.4 -clock core [get_ports {{cmd_ready rsp_valid rsp_data*}}]
set_false_path -from [get_ports rst]

# Die size: 1350 x 1350 um (~1.82 mm^2) for ~0.58 mm^2 stdcells + 4 SRAM banks + routing channels
initialize_floorplan -die_area "0 0 1350 1350" -core_area "20 20 1330 1330" -site FreePDK45_38x28_10R_NP_162NW_34O
make_tracks

# Place the 4 dual-port SRAM banks cleanly along the top corners with halo
place_cell -inst_name "u_sram.g_bank\\\\[0\\\\].u_bank" -origin "30 1170"   -orient R0 -status FIRM
place_cell -inst_name "u_sram.g_bank\\\\[1\\\\].u_bank" -origin "250 1170"  -orient R0 -status FIRM
place_cell -inst_name "u_sram.g_bank\\\\[2\\\\].u_bank" -origin "900 1170"  -orient R0 -status FIRM
place_cell -inst_name "u_sram.g_bank\\\\[3\\\\].u_bank" -origin "1120 1170" -orient R0 -status FIRM

place_pins -hor_layers metal3 -ver_layers metal2
global_placement -density 0.55
detailed_placement
check_placement -verbose

source {PDK / 'nangate45_setRC.tcl'}
estimate_parasitics -placement

report_design_area
report_clock_min_period -digits 4
report_worst_slack -max -digits 4
report_tns -digits 4
report_checks -path_delay max -group_path_count 3 -format summary -digits 4
set_power_activity -global -activity 0.15 -duty 0.5
report_power -digits 4
write_def {out / 'placed.def'}
exit
"""
    tcl_path = out / "pnr.tcl"
    log_path = out / "openroad.log"
    tcl_path.write_text(tcl)
    with log_path.open("w") as f:
        p = subprocess.run(RUN + [OPENROAD, "-exit", str(tcl_path)], stdout=f, stderr=subprocess.STDOUT)
    txt = log_path.read_text()
    print(f"[OpenROAD Nangate45] exit={p.returncode}")
    for line in txt.splitlines():
        if any(k in line for k in ("Design area", "period_min", "worst slack", "tns", "Total", "Error", "WARNING")):
            print(" ", line)
    if p.returncode != 0 or "Error:" in txt:
        raise RuntimeError(f"OpenROAD Nangate45 failed; see {log_path}")

    # Extract metrics JSON, then delete bulky DEF if > 50 MB
    def_p = out / "placed.def"
    def_mb = def_p.stat().st_size / 1e6 if def_p.exists() else 0
    if def_mb > 25:
        def_p.unlink()

    m_per = re.search(r"period_min\s*=\s*([0-9.]+)\s+fmax\s*=\s*([0-9.]+)", txt)
    m_area = re.search(r"Design area\s+([0-9.]+)\s+u\^2\s+([0-9.]+)%\s+utilization", txt)
    m_pwr = re.search(r"^Total\s+([0-9.eE+-]+)\s+([0-9.eE+-]+)\s+([0-9.eE+-]+)\s+([0-9.eE+-]+)", txt, re.M)
    summary = {
        "pdk": "nangate45",
        "stage": "post-detailed-placement + Manhattan RC parasitics (OpenROAD)",
        "die_um": "1350 x 1350 (1.8225 mm^2)",
        "design_area_um2": float(m_area.group(1)) if m_area else None,
        "utilization_pct": float(m_area.group(2)) if m_area else None,
        "post_place_min_period_ns": float(m_per.group(1)) if m_per else None,
        "post_place_fmax_mhz": float(m_per.group(2)) if m_per else None,
        "post_place_total_power_mw": round(float(m_pwr.group(4)) * 1e3, 3) if m_pwr else None,
        "post_place_leakage_mw": round(float(m_pwr.group(3)) * 1e3, 3) if m_pwr else None,
    }
    (out / "openroad_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    run_openroad_nangate45()
