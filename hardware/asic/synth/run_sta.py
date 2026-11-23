#!/usr/bin/env python3
"""Hierarchical OpenSTA timing and power sweep on the manufacturable IHP SG13G2 and
Sky130 HD libraries. The v2 foundry flow is run_foundry_v2.py.
"""
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
os.chdir(ROOT)
RUN = ["timeout", "--kill-after=10s", "600s"]
PDK = pathlib.Path(os.environ.get("PDK_ROOT", "/opt/pdk"))
STA = pathlib.Path(os.environ.get("OPENSTA_BIN", "sta"))
os.environ["TMPDIR"] = str(ROOT / "synth" / "work_hier")

# (netlist_lib_dir, corner_tag, stdcell_lib, wire_load_name_or_None, nom_period_in_lib_units, unit_to_ns)
CORNERS = [
    ("sky130",    "tt_025C_1v80",      "sky130_fd_sc_hd__tt_025C_1v80.lib",     None,              15.0,   1.0),
    ("ihp130",    "ff_m40C_1v32",      "sg13g2_stdcell_fast_1p32V_m40C.lib",    None,              10.0,   1.0),
    ("ihp130",    "tt_025C_1v20",      "sg13g2_stdcell_typ_1p20V_25C.lib",      None,              12.0,   1.0),
    ("ihp130",    "ss_125C_1v08",      "sg13g2_stdcell_slow_1p08V_125C.lib",    None,              18.0,   1.0),
]


def run_corner(lib, tag, lf, wlm, period, unit_to_ns):
    out = ROOT / "synth" / "hier" / lib
    sram_lib = out / f"sram_stub_{lib}.lib"
    netlist = out / "linked.v"
    if not (PDK / lf).exists():
        print(f"SKIP {lib}/{tag}: missing {lf}")
        return None

    wlm_cmd = f"set_wire_load_model -name {wlm}\nset_wire_load_mode top\n" if wlm else ""
    io_del = round(0.15 * period, 3)
    tcl = f"""read_liberty {PDK / lf}
read_liberty {sram_lib}
read_verilog {netlist}
link_design qsag_ni_asic_top
{wlm_cmd}create_clock -name core -period {period} [get_ports clk]
set_input_delay {io_del} -clock core [get_ports {{cmd_valid cmd_op* cmd_idx* cmd_addr* cmd_data*}}]
set_output_delay {io_del} -clock core [get_ports {{cmd_ready rsp_valid rsp_data*}}]
set_false_path -from [get_ports rst]
set_power_activity -global -activity 0.15 -duty 0.5
report_units
report_clock_min_period -digits 4
report_worst_slack -max -digits 4
report_worst_slack -min -digits 4
report_checks -path_delay max -group_path_count 3 -format summary -digits 4
report_power -digits 4
exit
"""
    tcl_path = out / f"sta_{tag}.tcl"
    log_path = out / f"sta_{tag}.log"
    tcl_path.write_text(tcl)
    with log_path.open("w") as f:
        p = subprocess.run(RUN + [str(STA), "-exit", str(tcl_path)], stdout=f, stderr=subprocess.STDOUT)
    txt = log_path.read_text()
    if p.returncode != 0 or "Error:" in txt:
        raise RuntimeError(f"OpenSTA failed on {lib}/{tag}:\n" + "\n".join(txt.splitlines()[-25:]))

    # Parse min_period & power
    m_per = re.search(r"period_min\s*=\s*([0-9.]+)\s+fmax\s*=\s*([0-9.]+)", txt)
    min_p_ns = float(m_per.group(1)) * unit_to_ns if m_per else None
    fmax_mhz = (1000.0 / min_p_ns) if min_p_ns else None

    # Parse Total power row: Group Internal Switching Leakage Total
    m_pwr = re.search(r"^Total\s+([0-9.eE+-]+)\s+([0-9.eE+-]+)\s+([0-9.eE+-]+)\s+([0-9.eE+-]+)", txt, re.M)
    pwr_mw = None
    leak_mw = None
    if m_pwr:
        leak_mw = float(m_pwr.group(3)) * 1e3
        pwr_mw = float(m_pwr.group(4)) * 1e3

    rec = {
        "library": lib,
        "corner": tag,
        "wire_load_model": wlm or "ideal",
        "min_period_ns": round(min_p_ns, 4) if min_p_ns else None,
        "fmax_mhz": round(fmax_mhz, 2) if fmax_mhz else None,
        "power_at_target_period_ns": round(period * unit_to_ns, 3),
        "total_power_mw": round(pwr_mw, 3) if pwr_mw is not None else None,
        "leakage_power_mw": round(leak_mw, 4) if leak_mw is not None else None,
    }
    print(f"[OpenSTA] {lib:10s} {tag:18s}: Tmin={rec['min_period_ns']} ns  Fmax={rec['fmax_mhz']} MHz  Ptot={rec['total_power_mw']} mW (leak={rec['leakage_power_mw']} mW)", flush=True)
    return rec


if __name__ == "__main__":
    results = []
    for args in CORNERS:
        r = run_corner(*args)
        if r:
            results.append(r)
    out_json = ROOT / "synth" / "hier" / "opensta_summary.json"
    out_json.write_text(json.dumps(results, indent=2) + "\n")
