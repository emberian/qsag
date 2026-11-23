"""Prepare post-route final/nl/chip_top.nl.v for 4-state Icarus -gspecify simulation and Yosys LEC."""
import re
import sys
from collections import Counter
from pathlib import Path

cells_v, nl_v, out_dir, sram_v, io_v = map(Path, sys.argv[1:])
sc = "gf180mcu_fd_sc_mcu7t5v0__"
ram = "gf180mcu_fd_ip_sram__sram512x8m8wm1"

raw = nl_v.read_text()

# Strip physical-only layout cells (fill, endcap, decap, antenna/diode/tap, ws_ip logos/markers)
# Note: diodes (antenna) have single input pin .I(...) with no functional output; stripping physical-only
# layout cells avoids missing-module errors while keeping EVERY functional buffer, CTS cell, flop, latch, pad & SRAM!
phys_prefixes = (
    sc + "fill",
    sc + "endcap",
    sc + "filltie",
    sc + "antenna",
    "gf180mcu_fd_io__fill",
    "gf180mcu_fd_io__cor",
    "gf180mcu_fd_io__dvdd",
    "gf180mcu_fd_io__dvss",
    "gf180mcu_fd_io__asig_5p0",
    "gf180mcu_ws_ip__",
)

stmt_pat = re.compile(r"^\s*(gf180mcu_\w+)\s+(\S+)\s*\(.*?\);\s*$", re.M | re.S)
stripped_counts = Counter()
kept_instances = []

def filter_stmt(m):
    cell, inst = m.group(1), m.group(2)
    if cell.startswith(phys_prefixes):
        stripped_counts[cell] += 1
        return ""
    kept_instances.append((cell, inst))
    return m.group(0)

clean_nl = stmt_pat.sub(filter_stmt, raw)
(out_dir / "chip_top_func.nl.v").write_text(clean_nl)

census = Counter(cell for cell, _ in kept_instances)
if census[ram] != 1:
    raise ValueError(f"Expected 1 SRAM in post-route netlist, got {census[ram]}")

all_latches = {inst for cell, inst in kept_instances if cell == sc + "latrnq_1"}
regbank_latches = {inst for inst in all_latches if "u_regbank" in inst}
vault_latches = sorted(inst for inst in all_latches if "g_vault" in inst)
flops = [inst for cell, inst in kept_instances if cell.startswith(sc + "dff")]

# Match post-route escaped hierarchical names (e.g. \i_chip_core.u_core.u_regbank.g_gpr[1].g_bit[0].u_lat )
def find_latch(sub):
    matches = [inst for inst in all_latches if sub in inst]
    if len(matches) != 1:
        raise ValueError(f"Expected 1 post-route latch matching {sub}, got {len(matches)}: {matches[:3]}")
    return matches[0]

rows = [f"u_regbank.g_gpr[{r}]" for r in range(1, 16)] + [f"u_regbank.g_spg[{s}]" for s in range(25)]
bits = [find_latch(f"{row}.g_bit[{k}].u_lat") for row in rows for k in range(64)]
if len(regbank_latches) != 2560 or len(vault_latches) != 448:
    raise ValueError(f"Latch count mismatch: regbank={len(regbank_latches)}, vault={len(vault_latches)}")

gates = [inst for cell, inst in kept_instances if cell == sc + "nand2_1" and inst.endswith(".u_gate")]
if len(gates) != 514:
    raise ValueError(f"Expected 514 physical RO gates in post-route netlist, got {len(gates)}")

dsram_inst = [inst for cell, inst in kept_instances if cell == ram and "u_dsram" in inst]
if len(dsram_inst) != 1:
    raise ValueError(f"Expected u_dsram macro, got {dsram_inst}")

fast_gate = [g for g in gates if "u_trng.u_fast" in g]
slow_gate = [g for g in gates if "u_trng.u_slow" in g]
if len(fast_gate) != 1 or len(slow_gate) != 1:
    raise ValueError("Missing CoSO fast/slow gate in post-route netlist")

print(f"Post-route functional netlist: {sum(census.values())} active instances "
      f"(stripped {sum(stripped_counts.values())} physical-only filler/tap/power cells), "
      f"{len(flops)} FFs, 2560 regbank latches, 448 vault latches, 514 RO gates, 1 SRAM")

with (out_dir / "postroute_probes.svh").open("w") as f:
    print(f"`define POST_DRAM dut.{dsram_inst[0]} ", file=f)
    print(f"`define POST_TRNG_FAST dut.{fast_gate[0]} ", file=f)
    print(f"`define POST_TRNG_SLOW dut.{slow_gate[0]} ", file=f)
    print("function automatic bit all_ffs_x(); begin all_ffs_x = 1'b1;", file=f)
    for name in flops:
        print(f"  if (dut.{name} .Q !== 1'bx) return 1'b0;", file=f)
    print("end endfunction", file=f)
    print("function automatic bit all_ros_one(); begin all_ros_one = 1'b1;", file=f)
    for name in gates:
        print(f"  if (dut.{name} .ZN !== 1'b1) return 1'b0;", file=f)
    print("end endfunction", file=f)
    print("wire [2559:0] secret_q;", file=f)
    for i, name in enumerate(bits):
        print(f"assign secret_q[{i}] = dut.{name} .Q;", file=f)
    print("wire [447:0] vault_q;", file=f)
    for i, name in enumerate(vault_latches):
        print(f"assign vault_q[{i}] = dut.{name} .Q;", file=f)

pattern = (r"ifnone\s*\n\s*//[^\n]*\n\s*\((?:posedge|negedge)\s+"
           r"(\w+)\s*=>\s*\((\w+)\s*:\s*\w+\)\)\s*=\s*\(1\.0,1\.0\);")
timed, _ = re.subn(pattern, r"ifnone (\1 => \2) = (1.0,1.0);", cells_v.read_text())
(out_dir / "timed.v").write_text("`timescale 100ps/1ps\n" + timed)

source = sram_v.read_text()
arcs = [f"if ((CEN == 1'b0) && (GWEN == 1'b1)) (posedge CLK => (Q[{i}]  : 1'bx)) = (ta, ta);" for i in range(8)]
(out_dir / "sram.v").write_text(source.replace("\n".join(arcs), arcs[0].replace("=> (Q[0]", "*> (Q")))

# Normalize IO pad model timescale for Icarus
io_src = io_v.read_text()
(out_dir / "io_pads.v").write_text("`timescale 1ns/1ps\n" + io_src)
