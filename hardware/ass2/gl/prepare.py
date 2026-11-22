"""Prepare the E11 Icarus timing view and bind probes to an identified Yosys map."""
import re
import sys
from collections import Counter
from pathlib import Path

cells, mapped, stat, out, sram = map(Path, sys.argv[1:])
sc = "gf180mcu_fd_sc_mcu7t5v0__"
ram = "gf180mcu_fd_ip_sram__sram512x8m8wm1"
net = mapped.read_text()
instances = re.findall(r"^  (gf180mcu_\w+) (\S+) +\(", net, re.M)
census = Counter(cell for cell, _ in instances)
expected = {cell: int(n) for n, cell in re.findall(
    r"^\s*(\d+)\s+\S+\s+(gf180mcu_\w+)$", stat.read_text(), re.M)}
if census != expected or census[ram] != 2:
    raise ValueError("Mapped instance census disagrees with synthesis results")
latches = {inst for cell, inst in instances if cell == sc + "latrnq_1"}
flops = [inst for cell, inst in instances if cell.startswith(sc + "dff")]
rows = [f"\\u_core.u_regbank.g_gpr[{r}]" for r in range(1, 16)]
rows += [f"\\u_core.u_regbank.g_spg[{s}]" for s in range(25)]
bits = [f"{row}.g_bit[{k}].u_lat" for row in rows for k in range(64)]
if set(bits) != latches:
    raise ValueError("Secret row/bit mapping does not cover exactly the physical latches")
print(f"Mapped {sum(census.values()) - 2} standard cells, 2 SRAMs, "
      f"{len(flops)} flip-flops, {len(bits)} named secret bits")
with (out / "physical.svh").open("w") as f:
    print(f"wire [{len(flops)-1}:0] ff_q;", file=f)
    for i, name in enumerate(flops):
        print(f"assign ff_q[{i}] = dut.{name} .Q;", file=f)
    gates = [name for cell,name in instances if cell == sc+"nand2_1" and name.endswith(".u_gate")]
    if len(gates) != 514:
        raise ValueError(f"Expected 512 PUF and two CoSO feedback gates, got {len(gates)}")
    print("wire [513:0] ro_gate;", file=f)
    for i,name in enumerate(gates):
        print(f"assign ro_gate[{i}] = dut.{name} .ZN;", file=f)
    print("wire [2559:0] secret_q;", file=f)
    for i, name in enumerate(bits):
        print(f"assign secret_q[{i}] = dut.{name} .Q;", file=f)
# Predict the exact resident retirement sequence from the built ROM using the
# independent ISA model. The pin bench checks the mapped processor against it.
root = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(root/"tools"),str(root/"sim")]
from ass2_ref import Vm, SYS_MMIO, RX_MBOX
image = bytearray(4096)
for address, value in re.findall(r"9'd(\d+): rdata <= 64'h([0-9a-f]+)", (root/"rtl/qsag_ass2_irom.sv").read_text()):
    i = 8*int(address)
    image[i:i+8] = int(value,16).to_bytes(8,"little")
vm = Vm()
vm.load(0,image)
vm.w64(SYS_MMIO+16, 0x31 | (8<<16))
pcs = []
while not vm.halted and len(pcs) < 1024:
    pcs.append(vm.pc)
    vm.step()
assert vm.halted and vm.R[4] == 1
with (out/"rom_oracle.svh").open("w") as f:
    print(f"localparam integer IDENT_RETIRED={vm.instret}, IDENT_CYCLES={vm.cycles};",file=f)
    print("function automatic integer ident_pc(input integer n); case(n)",file=f)
    for i,pc in enumerate(pcs): print(f"{i}:ident_pc={pc};",file=f)
    print("default:ident_pc=-1; endcase endfunction",file=f)
# Icarus rejects edge-sensitive ifnone paths with a data-source expression.
pattern = (r"ifnone\s*\n\s*//[^\n]*\n\s*\((?:posedge|negedge)\s+"
           r"(\w+)\s*=>\s*\((\w+)\s*:\s*\w+\)\)\s*=\s*\(1\.0,1\.0\);")
timed, matches = re.subn(pattern, r"ifnone (\1 => \2) = (1.0,1.0);", cells.read_text())
print(f"Normalized {matches} unit-delay ifnone paths for Icarus")
(out / "timed.v").write_text("`timescale 100ps/1ps\n" + timed)

# The eight read arcs have the same condition and ta. Icarus widens a
# destination bit-select to Q[7:0], so use one scalar-to-vector full path.
source = sram.read_text()
arcs = [f"if ((CEN == 1'b0) && (GWEN == 1'b1)) (posedge CLK => (Q[{i}]  : 1'bx)) = (ta, ta);" for i in range(8)]
if "\n".join(arcs) not in source:
    raise ValueError("Unknown SRAM read timing view")
(out / "sram.v").write_text(source.replace("\n".join(arcs), arcs[0].replace("=> (Q[0]", "*> (Q")))
