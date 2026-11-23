#!/usr/bin/env python3
"""Delay-driven hierarchical Liberty synthesis for Sky130 HD and IHP SG13G2.

Maps the reusable datapath macros and the top-level controller independently with
ABC delay-driven technology mapping, fanout buffering, and gate sizing (`&dch -f; &nf; buffer -c; upsize; dnsize`),
then links all mapped netlists (zero unmapped logic; only the 4-bank 128 KiB foundry SRAM macro
`sram_dp_64x16384_bank` remains a parameter-free black box) to estimate standard-cell area and pre-layout timing.
"""
import concurrent.futures
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
os.chdir(ROOT)
os.environ["PATH"] = os.environ.get("OSS_CAD_BIN", "/opt/oss-cad-suite/bin") + ":" + os.environ["PATH"]
WORK = pathlib.Path(os.environ["TMPDIR"]) / "work_hier"
WORK.mkdir(parents=True, exist_ok=True)

RUN = ["timeout", "--kill-after=10s", "600s"]
PDK = os.environ.get("PDK_ROOT", "/opt/pdk").rstrip("/") + "/"

# (liberty_file, nand2_area_um2, abc_target_ps, lib_time_unit)
LIBS = {
    "sky130":    ("sky130_fd_sc_hd__tt_025C_1v80.lib",    3.7536,  10500, "ns"),
    "ihp130":    ("sg13g2_stdcell_typ_1p20V_25C.lib",     7.2576,   8500, "ns"),
}

MACROS = [
    "qsag_gl64_mul_csa",
    "qsag_p2_me",
    "qsag_p2_mi_tail",
    "qsag_p2_mi_apply",
    "qsag_p2_canopy_ff",
    "qsag_keccak_round",
    "qsag_gf128_mul",
    "qsag_tower128_to_poly",
    "qsag_poly_to_tower128",
]

RTL = " ".join(str(p) for p in sorted(pathlib.Path("rtl").glob("*.sv")))
ABC = "+strash;dretime;&get,-n;&dch,-f;&nf,{D};&put;buffer,-N,16;topo;upsize,{D};dnsize,{D};stime,-p"


def write_sram_stub_lib(lib_name, out_dir):
    """Emit a clean Liberty timing model for the 64x16384 foundry dual-port SRAM bank (area = 0 so
    stdcell logic kGE is unpolluted, while setup & clk-to-Q arcs are timed by OpenSTA/OpenROAD)."""
    _, _, _, tunit = LIBS[lib_name]
    # Realistic foundry SRAM macro setup / clk-to-q in library time units
    if lib_name == "ihp130":    # ns
        t_setup, t_ckq, cap = 0.55, 1.10, "0.010"
        cunit, v_nom = "1pf", 1.2
    else:                         # sky130, ns
        t_setup, t_ckq, cap = 0.70, 1.40, "0.012"
        cunit, v_nom = "1pf", 1.8

    t_unit_str = "1ps" if tunit == "ps" else "1ns"
    lines = [
        f"library(sram_dp_64x16384_bank_{lib_name}) {{",
        "  delay_model : table_lookup;",
        f"  time_unit : \"{t_unit_str}\";",
        f"  voltage_unit : \"1V\";",
        f"  current_unit : \"1mA\";",
        f"  capacitive_load_unit (1, {cunit[1:]});",
        "  leakage_power_unit : \"1nW\";",
        "  input_threshold_pct_rise : 50.0;",
        "  output_threshold_pct_rise : 50.0;",
        "  slew_lower_threshold_pct_rise : 20.0;",
        "  slew_upper_threshold_pct_rise : 80.0;",
        "  input_threshold_pct_fall : 50.0;",
        "  output_threshold_pct_fall : 50.0;",
        "  slew_lower_threshold_pct_fall : 20.0;",
        "  slew_upper_threshold_pct_fall : 80.0;",
        "  slew_derate_from_library : 1.0;",
        f"  nom_process : 1.0; nom_temperature : 25.0; nom_voltage : {v_nom};",
        "  type (bus14) { base_type : array; data_type : bit; bit_width : 14; bit_from : 13; bit_to : 0; }",
        "  type (bus64) { base_type : array; data_type : bit; bit_width : 64; bit_from : 63; bit_to : 0; }",
        "  lu_table_template(scalar_t) { variable_1 : total_output_net_capacitance; index_1 (\"0.0\"); }",
        "  lu_table_template(con_t) { variable_1 : constrained_pin_transition; index_1 (\"0.0\"); }",
        "  cell (sram_dp_64x16384_bank) {",
        "    area : 0.0;",
        "    is_memory_cell : true;",
        f"    pin (clk) {{ direction : input; clock : true; capacitance : {cap}; }}",
    ]
    for p in ("a", "b"):
        for sig in (f"{p}_en", f"{p}_we"):
            lines += [
                f"    pin ({sig}) {{ direction : input; capacitance : {cap};",
                "      timing () { related_pin : \"clk\"; timing_type : setup_rising;",
                f"        rise_constraint(con_t) {{ values(\"{t_setup}\"); }}",
                f"        fall_constraint(con_t) {{ values(\"{t_setup}\"); }} }} }}",
            ]
        for bus, btype in ((f"{p}_addr", "bus14"), (f"{p}_wdata", "bus64")):
            lines += [
                f"    bus ({bus}) {{ bus_type : {btype}; direction : input; capacitance : {cap};",
                "      timing () { related_pin : \"clk\"; timing_type : setup_rising;",
                f"        rise_constraint(con_t) {{ values(\"{t_setup}\"); }}",
                f"        fall_constraint(con_t) {{ values(\"{t_setup}\"); }} }} }}",
            ]
        lines += [
            f"    bus ({p}_rdata) {{ bus_type : bus64; direction : output;",
            "      timing () { related_pin : \"clk\"; timing_type : rising_edge;",
            f"        cell_rise(scalar_t) {{ values(\"{t_ckq}\"); }}",
            f"        rise_transition(scalar_t) {{ values(\"{t_setup}\"); }}",
            f"        cell_fall(scalar_t) {{ values(\"{t_ckq}\"); }}",
            f"        fall_transition(scalar_t) {{ values(\"{t_setup}\"); }} }} }}",
        ]
    lines += ["  }", "}", ""]
    path = out_dir / f"sram_stub_{lib_name}.lib"
    path.write_text("\n".join(lines))
    return path


def synth_one(lib, mod):
    lf, _, period, _ = LIBS[lib]
    out = ROOT / "synth" / "hier" / lib
    out.mkdir(parents=True, exist_ok=True)
    log = out / f"{mod}.log"
    sv = out / f"{mod}.v"
    cuts = ""
    if mod == "qsag_ni_asic_top":
        cuts = " ".join(f"--blackboxed-module {m}" for m in MACROS + ["sram_dp_64x16384_bank"])

    script = f"""plugin -i slang
read_slang -Irtl {cuts} {RTL} --top {mod}
hierarchy -check -top {mod}
synth -top {mod} -flatten -noabc
dfflibmap -liberty {PDK + lf}
abc -liberty {PDK + lf} -D {period} -script {ABC}
setundef -zero
opt_clean -purge
check
tee -o {out / mod}.json stat -json -liberty {PDK + lf}
select {mod}
write_verilog -noattr -noexpr -nodec -selected {sv}
"""
    ys_path = out / f"{mod}.ys"
    ys_path.write_text(script)
    with log.open("w") as f:
        p = subprocess.run(RUN + ["yosys", "-T", "-s", str(ys_path)], stdout=f, stderr=subprocess.STDOUT)
    print(f"[{lib}] {mod:26s} exit={p.returncode}", flush=True)
    if p.returncode != 0:
        raise RuntimeError(f"Synthesis failed: {log}")
    return str(sv)


def link_lib(lib):
    lf, ge, period, _ = LIBS[lib]
    out = ROOT / "synth" / "hier" / lib
    sram_lib = write_sram_stub_lib(lib, out)

    reads = "\n".join(f"read_verilog {out / (m + '.v')}" for m in MACROS + ["qsag_ni_asic_top"])
    script = f"""read_liberty -lib {PDK + lf}
read_liberty -lib {sram_lib}
{reads}
hierarchy -check -top qsag_ni_asic_top
setundef -zero
opt_clean -purge
check
tee -o {out / 'linked.json'} stat -json -liberty {PDK + lf}
write_verilog -noattr -noexpr {out / 'linked.v'}
flatten
setundef -zero
opt_clean -purge
write_verilog -noattr -noexpr {out / 'flat_gates.v'}
"""
    (out / "link.ys").write_text(script)
    with (out / "link.log").open("w") as f:
        subprocess.run(RUN + ["yosys", "-T", "-s", str(out / "link.ys")], stdout=f, stderr=subprocess.STDOUT, check=True)

    d = json.loads((out / "linked.json").read_text())
    area = d["design"]["area"]
    seq_area = d["design"].get("sequential_area", 0.0)
    num_cells = d["design"]["num_cells"]
    macros_info = {}
    for m in MACROS + ["qsag_ni_asic_top"]:
        mj = json.loads((out / f"{m}.json").read_text())
        ma = mj["design"]["area"]
        txt = (out / f"{m}.log").read_text()
        delays = re.findall(r"Delay\s*=\s*([0-9.]+)\s*ps", txt)
        macros_info[m] = {
            "area_um2": round(ma, 3),
            "kGE": round(ma / ge / 1000.0, 2),
            "abc_delay_ps": float(delays[-1]) if delays else None,
        }
    res = {
        "library": lib,
        "nand2_um2": ge,
        "abc_target_ps": period,
        "area_um2": round(area, 2),
        "seq_area_um2": round(seq_area, 2),
        "kGE": round(area / ge / 1000.0, 2),
        "seq_kGE": round(seq_area / ge / 1000.0, 2),
        "num_cells": num_cells,
        "sram_banks": "4 x sram_dp_64x16384_bank (512 KiB total, foundry macro excluded from stdcell kGE)",
        "macros": macros_info,
    }
    (out / "result.json").write_text(json.dumps(res, indent=2) + "\n")
    print(f"[{lib}] LINKED TOTAL: {res['kGE']:.2f} kGE ({res['area_um2']:.1f} um^2, {num_cells} cells, seq={res['seq_kGE']:.2f} kGE)", flush=True)
    return res


if __name__ == "__main__":
    libs = [sys.argv[1]] if len(sys.argv) > 1 and sys.argv[1] != "all" else list(LIBS.keys())
    for lib in libs:
        mods = MACROS + ["qsag_ni_asic_top"]
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
            list(ex.map(lambda m: synth_one(lib, m), mods))
        link_lib(lib)
