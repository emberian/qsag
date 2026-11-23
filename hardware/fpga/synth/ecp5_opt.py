"""ECP5 netlist post-map pass:
Absorbs unconditional same-clock fabric TRELLIS_FFs into MULT18X18D hardware
REG_INPUTA_CLK / REG_INPUTB_CLK / REG_OUTPUT_CLK pipeline registers.
"""
import collections
import json
import sys


def pack_dsp_regs(module):
    cells = module["cells"]
    consumers = collections.defaultdict(list)
    drivers = {}
    for name, cell in cells.items():
        for port, bits in cell["connections"].items():
            for bit in bits:
                if not isinstance(bit, int):
                    continue
                if cell["port_directions"][port] == "input":
                    consumers[bit].append((name, port))
                else:
                    drivers[bit] = (name, port)
    for port in module["ports"].values():
        if port["direction"] != "input":
            for bit in port["bits"]:
                if isinstance(bit, int):
                    consumers[bit].append((None, "PAD"))

    def is_plain_ff(name):
        if name is None:
            return False
        c = cells[name]
        p, io = c["parameters"], c["connections"]
        return (
            c["type"] == "TRELLIS_FF"
            and p.get("CEMUX", "").strip() == "1"
            and p.get("CLKMUX") == "CLK"
            and p.get("GSR") == "DISABLED"
            and p.get("LSRMUX") == "LSR"
            and p.get("SRVAL", "ZERO") == "ZERO"
            and io.get("LSR") == ["0"]
            and set(io) == {"CLK", "LSR", "DI", "Q"}
        )

    removed = set()
    moved_inputs = set()
    counts = collections.Counter()
    for dsp in cells.values():
        if dsp["type"] != "MULT18X18D":
            continue
        io, params = dsp["connections"], dsp["parameters"]
        if params or not all(io.get(k) == ["0"] for k in ("SIGNEDA", "SIGNEDB", "SOURCEA", "SOURCEB")):
            continue
        clock = None
        for bus in ("A", "B", "P"):
            pins = [
                p
                for p, b in io.items()
                if p.startswith(bus)
                and p[1:].isdigit()
                and isinstance(b[0], int)
                and (bus != "P" or consumers[b[0]])
            ]
            if not pins:
                continue
            ffs = {}
            for pin in pins:
                (bit,) = io[pin]
                if bus == "P":
                    users = consumers[bit]
                    if len(users) != 1 or users[0][1] != "DI":
                        break
                    ff = users[0][0]
                else:
                    ff, port = drivers.get(bit, (None, None))
                    if port != "Q":
                        break
                if not is_plain_ff(ff):
                    break
                ffs[pin] = ff
            if len(ffs) != len(pins):
                continue
            clocks = {cells[f]["connections"]["CLK"][0] for f in ffs.values()}
            if len(clocks) != 1 or (clock is not None and clock not in clocks):
                continue
            (clock,) = clocks
            stage = {"A": "INPUTA", "B": "INPUTB", "P": "OUTPUT"}[bus]
            params["REG_" + stage + "_CLK"] = "CLK0"
            for pin, ff in ffs.items():
                if bus == "P":
                    io[pin] = cells[ff]["connections"]["Q"]
                    removed.add(ff)
                else:
                    io[pin] = cells[ff]["connections"]["DI"]
                    moved_inputs.add(ff)
            counts[stage] += 1
        if clock is not None:
            params["GSR"] = "DISABLED"
            for p, b in (("CLK0", clock), ("CE0", "1"), ("RST0", "0")):
                dsp["port_directions"][p] = "input"
                io[p] = [b]
    for f in removed:
        del cells[f]
    live = {
        bit
        for c in cells.values()
        for p, bits in c["connections"].items()
        if c["port_directions"][p] == "input"
        for bit in bits
        if isinstance(bit, int)
    }
    live.update(
        b for p in module["ports"].values() if p["direction"] != "input" for b in p["bits"] if isinstance(b, int)
    )
    for f in moved_inputs - removed:
        if cells[f]["connections"]["Q"][0] not in live:
            del cells[f]
            removed.add(f)
    print(f"ecp5_opt ({len(removed)} DSP FFs packed): {dict(counts)}", flush=True)


def main():
    source, top, dest = sys.argv[1:]
    with open(source) as fp:
        design = json.load(fp)
    module = design["modules"][top]
    pack_dsp_regs(module)
    expected = {"fmax_ext5_mac": 126, "fmax_compact_top": 18, "fmax_ecp5_fullrate_top": 81}
    if top in expected:
        dsps = [cell for cell in module["cells"].values() if cell["type"] == "MULT18X18D"]
        if len(dsps) != expected[top]:
            raise ValueError(f"{top}: expected {expected[top]} DSPs, mapped {len(dsps)}")
        for cell in dsps:
            if any(cell["parameters"].get("REG_"+stage+"_CLK") != "CLK0"
                   for stage in ("INPUTA","INPUTB","OUTPUT")):
                raise ValueError(f"{top}: incomplete DSP pipeline register absorption")
    with open(dest, "w") as fp:
        json.dump(design, fp, separators=(",", ":"))


if __name__ == "__main__":
    main()
