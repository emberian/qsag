"""Post-ABC GF180 netlist cleanup, ICG sink clustering (`<= 16` sinks/ICG), & async-reset fanout tree builder:
  1. Replaces redundant internal low-fanout (`<= 2` loads) `buf_1` wire-alias cells with `assign`
     so Yosys `opt_clean -purge` folds them cleanly.
  2. Splits auto-generated high-fanout (`> 16` sinks) `icgtp_2` cells into balanced `<= 16`-sink
     local `icgtp_2` clusters (eliminating 64..80-sink ICG insertion skew in FF/TT/SS & CTS).
  3. Bounds GF180 async-reset (`RN`) loads with balanced `buf_4` trees (`<= 32` pins/leaf).
"""
from collections import Counter, defaultdict
from pathlib import Path
import re
import sys

path = Path(sys.argv[1])
netlist = path.read_text()

# 1. Strip redundant internal `buf_1` cells whose output `_NNN_` has <= 2 loads (`<= 4` total token occurrences)
tok_counts = Counter(re.findall(r"_\d+_", netlist))
buf1_pat = re.compile(
    r"^[ \t]*gf180mcu_fd_sc_mcu7t5v0__buf_1\s+_\d+_\s*\(\s*\.I\(([^)]+)\),\s*\.Z\((_\d+_)\)\s*\);",
    re.M,
)
removed_buf1 = 0
def repl_buf1(m):
    global removed_buf1
    src, dst = m.group(1).strip(), m.group(2).strip()
    if tok_counts[dst] <= 4:
        removed_buf1 += 1
        return f"  assign {dst} = {src};"
    return m.group(0)

netlist = buf1_pat.sub(repl_buf1, netlist)

# 2. Split auto-generated `icgtp_2` (`_NNN_`) cells driving > 16 `.CLK(...)` pins into `<= 16`-sink clusters
clk_pin_pat = re.compile(r"\.CLK\(([^)]+)\)")
clk_counts = Counter(m.group(1).strip() for m in clk_pin_pat.finditer(netlist))

icg_stmt_pat = re.compile(
    r"^[ \t]*gf180mcu_fd_sc_mcu7t5v0__icgtp_2\s+(_\d+_)\s*\((.*?)\);\s*$",
    re.M | re.S,
)
port_pat = re.compile(r"\.(\w+)\(([^)]+)\)")

icg_branches = {}
icg_wires = []
icg_cells = []

for m in icg_stmt_pat.finditer(netlist):
    ports = {k: v.strip() for k, v in port_pat.findall(m.group(2))}
    qnet = ports.get("Q", "")
    n_sinks = clk_counts.get(qnet, 0)
    if n_sinks > 16 and qnet:
        n_ways = (n_sinks + 15) // 16
        en_buf = f"ass2_icg_en_{len(icg_wires)}"
        icg_wires.append(f"  wire {en_buf};")
        icg_cells.append(
            f"  gf180mcu_fd_sc_mcu7t5v0__buf_4 {en_buf}_buf ("
            f".I( {ports['E']} ), .Z( {en_buf} ));"
        )
        outs = [qnet]
        for _ in range(1, n_ways):
            wname = f"ass2_icg_clk_{len(icg_wires)}"
            icg_wires.append(f"  wire {wname};")
            icg_cells.append(
                f"  gf180mcu_fd_sc_mcu7t5v0__icgtp_2 {wname}_icg ("
                f".CLK( {ports['CLK']} ), .E( {en_buf} ), .TE( {ports['TE']} ), .Q( {wname} ));"
            )
            outs.append(wname)
        icg_branches[qnet] = outs

icg_used = Counter()
def rewrite_clk_pin(m):
    net = m.group(1).strip()
    if net not in icg_branches:
        return m.group(0)
    outs = icg_branches[net]
    idx = icg_used[net] // 16
    icg_used[net] += 1
    return f".CLK({outs[min(idx, len(outs) - 1)]})"

if icg_branches:
    netlist = clk_pin_pat.sub(rewrite_clk_pin, netlist)

# 3. Build coarse `buf_8` fanout trees (`<= 64` pins/leaf) on high-fanout `.RN(...)` nets
#    so pre-layout STA stays clean while OpenROAD `repair_design` (`MAX_FANOUT_CONSTRAINT: 20`)
#    re-clusters every 64-load leaf spatially by `(x, y)` Steiner coordinates after GPL!
rn = re.compile(r"\.RN\(([^)]+)\)")
counts = Counter(rn.findall(netlist))
leaves = defaultdict(list)
cells = list(icg_cells)
wires = list(icg_wires)

def buffer(source):
    name = f"ass2_reset_branch_{len(wires)}"
    wires.append(f"  wire {name};")
    cells.append(f"  gf180mcu_fd_sc_mcu7t5v0__buf_8 {name}_buf (.I({source}), .Z({name}));")
    return name

def tree(source, size):
    if size <= 16:
        return [buffer(source) for _ in range(size)]
    parents = tree(source, (size + 15) // 16)
    return [buffer(parents[i // 16]) for i in range(size)]

for net, count in counts.items():
    if count > 64:
        leaves[net] = tree(net, (count + 63) // 64)

used = Counter()
def reset_pin(match):
    net = match[1]
    if net not in leaves:
        return match[0]
    leaf = leaves[net][used[net] // 64]
    used[net] += 1
    return f".RN({leaf})"

netlist = rn.sub(reset_pin, netlist)
assert netlist.count("endmodule") == 1
first = netlist.index("  wire ")
netlist = netlist[:first] + "\n".join(wires) + "\n" + netlist[first:]
path.write_text(netlist.replace("endmodule", "\n".join(cells) + "\nendmodule"))
print(
    f"Folded {removed_buf1} redundant buf_1 cells; "
    f"added {len(icg_cells)} ICG cluster clones across {len(icg_branches)} nets; "
    f"added {len(cells) - len(icg_cells)} reset buffers on {len(used)} nets ({sum(used.values())} RN pins)"
)
