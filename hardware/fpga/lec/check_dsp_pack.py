"""Check the complete mapped design by expanding each changed DSP port by one DFF.

The adjacent temporal miter checks the hard-register clock semantics. Here the
cutpoints are actual net IDs. No combinational cell outside those cuts may change.
"""
from collections import Counter
import json
from pathlib import Path
import sys


def verify(before, after, top):
    pre, post = (d["modules"][top] for d in (before, after))
    assert pre["ports"] == post["ports"]
    cells, gates = pre["cells"], post["cells"]
    assert gates.keys() <= cells.keys()
    drivers, users = {}, Counter()
    for name, cell in cells.items():
        for pin, bits in cell["connections"].items():
            for bit in bits:
                if isinstance(bit, int):
                    if cell["port_directions"][pin] == "output":
                        assert bit not in drivers
                        drivers[bit] = (name, pin)
                    else:
                        users[bit] += 1
    for port in pre["ports"].values():
        if port["direction"] != "input":
            users.update(port["bits"])
    absorbed, replaced = set(), set()
    counts = Counter()
    for name, cell in gates.items():
        original = cells[name]
        if original == cell:
            continue
        assert original["type"] == cell["type"] == "MULT18X18D"
        a, b = original["connections"], cell["connections"]
        assert set(b) == set(a) | {"CLK0","RST0","CE0"}
        assert not original["parameters"] and cell["parameters"]["GSR"] == "DISABLED"
        assert b["RST0"] == ["0"] and b["CE0"] == ["1"] and len(b["CLK0"]) == 1
        params = dict(cell["parameters"])
        del params["GSR"]
        for port, stage in [("A","INPUTA"),("B","INPUTB"),("P","OUTPUT")]:
            if params.pop("REG_"+stage+"_CLK",None) is None:
                assert all(a[k]==b[k] for k in a if k.startswith(port) and k[1:].isdigit())
                continue
            assert cell["parameters"]["REG_"+stage+"_CLK"]=="CLK0"
            counts[stage] += 1
            for pin in a:
                if not (pin.startswith(port) and pin[1:].isdigit()):
                    continue
                old, new = a[pin][0], b[pin][0]
                if not isinstance(old,int) or (port=="P" and users[old]==0):
                    assert new == old
                    continue
                q, d = (new,old) if port=="P" else (old,new)
                ffname, ffpin = drivers[q]
                ff = cells[ffname]
                assert ffpin == "Q" and ff["type"] == "TRELLIS_FF"
                assert ff["connections"] == {"Q":[q],"DI":[d],"LSR":["0"],"CLK":b["CLK0"]}
                cfg = ff["parameters"]
                assert cfg["CEMUX"].strip()=="1" and cfg["CLKMUX"]=="CLK"
                assert cfg["LSRMUX"]=="LSR" and cfg["GSR"]=="DISABLED" and cfg.get("SRVAL","ZERO")=="ZERO"
                if port=="P":
                    assert users[old]==1 and ffname not in gates
                    replaced.add(q)
                absorbed.add(ffname)
        assert not params
        for pin in a:
            if not (pin[0] in "ABP" and pin[1:].isdigit()):
                assert b[pin]==a[pin]
    missing = cells.keys()-gates.keys()
    assert missing <= absorbed
    # A deleted input register may have been shared. Every surviving use must
    # still have a driver; output registers now get their Q directly from DSPs.
    used = {bit for cell in gates.values() for p,bits in cell["connections"].items()
            if cell["port_directions"][p]=="input" for bit in bits}
    used.update(bit for p in post["ports"].values() if p["direction"]!="input" for bit in p["bits"])
    for ff in missing:
        q = cells[ff]["connections"]["Q"][0]
        assert q in replaced or q not in used
    dsps = sum(c["type"]=="MULT18X18D" for c in cells.values())
    assert counts == {"INPUTA":dsps,"INPUTB":dsps,"OUTPUT":dsps}
    print(f"[PASS] {top}: {dsps} DSPs, {len(missing)} removed FFs, complete mapped connectivity checked")


if __name__=="__main__":
    pre,post,top=sys.argv[1:]
    verify(json.loads(Path(pre).read_text()),json.loads(Path(post).read_text()),top)

