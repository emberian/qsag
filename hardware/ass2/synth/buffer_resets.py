"""Post-ABC GF180 netlist cleanup & async-reset fanout tree builder:
  1. Replaces redundant internal low-fanout (`<= 2` loads) `buf_1` wire-alias cells with `assign`
     so Yosys `opt_clean -purge` folds them cleanly (saving ~35k um^2 and ~2,800 cells with 0 assigns).
  2. Bounds GF180 async-reset (`RN`) loads with balanced `buf_4` trees (`<= 32` pins/leaf).
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

# 2. Build balanced `buf_4` fanout trees on high-fanout `.RN(...)` nets
rn = re.compile(r"\.RN\(([^)]+)\)")
counts = Counter(rn.findall(netlist))
leaves = defaultdict(list)
cells = []
wires = []

def buffer(source):
    name = f"ass2_reset_branch_{len(wires)}"
    wires.append(f"  wire {name};")
    cells.append(f"  gf180mcu_fd_sc_mcu7t5v0__buf_4 {name}_buf (.I({source}), .Z({name}));")
    return name

def tree(source, size):
    if size <= 16:
        return [buffer(source) for _ in range(size)]
    parents = tree(source, (size + 15) // 16)
    return [buffer(parents[i // 16]) for i in range(size)]

for net, count in counts.items():
    if count > 40:
        leaves[net] = tree(net, (count + 31) // 32)

used = Counter()
def reset_pin(match):
    net = match[1]
    if net not in leaves:
        return match[0]
    leaf = leaves[net][used[net] // 32]
    used[net] += 1
    return f".RN({leaf})"

netlist = rn.sub(reset_pin, netlist)
assert netlist.count("endmodule") == 1
first = netlist.index("  wire ")
netlist = netlist[:first] + "\n".join(wires) + "\n" + netlist[first:]
path.write_text(netlist.replace("endmodule", "\n".join(cells) + "\nendmodule"))
print(f"Folded {removed_buf1} redundant buf_1 cells; added {len(cells)} reset buffers on {len(used)} nets ({sum(used.values())} RN pins)")
