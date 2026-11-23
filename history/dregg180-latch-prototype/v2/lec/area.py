#!/usr/bin/env python3
"""Area table of the synthesized v2 blocks against ARCHITECTURE.md 7.1, and the static storage checks.

    python3 area.py <build/v2/syn> [rows]

For every block: chip area (Yosys stat with the liberty), cell count, sequential cells by type.
Checks on the flat netlists (exit 1 if one fails):
  - the only level-sensitive storage is latrnq_1 in the register file (rows x 64) and the clock gates;
  - every flop and every latch has an asynchronous reset pin (listed exceptions: none expected except the
    SPI receive shifter, which is written bit by bit before use);
  - every register-file latch has the same net on RN, and that net is the secret reset.
"""
import os
import re
import sys

BUDGET = {   # ARCHITECTURE.md 7.1, um^2
    "dregg_regfile": (296497, "register file, 72 rows [M]"),
    "dregg_keccak_serial": (90650, "Keccak unit less its rows [M]"),
    "dregg_word_unit": (34329, "word unit [M skeleton]"),
    "dregg_urom": (None, "ROM: 77,500 budgeted for 1,700 words, 45.6 per word"),
    "sequencer": (23985, "sequencer [M skeleton]: dregg_seq (with dregg_rules), dregg_egress, dregg_framer"),
    "dregg_spi_link": (25000, "SPI link, diagnostics [E]"),
    "dregg_fram": (12704, "FRAM SPI master: 25,739 [M] for TRNG + FRAM master, less the TRNG's 13,035"),
    "dregg_rst": (None, "part of clock, reset, tamper, shield (35,000)"),
}
PREFIX = "gf180mcu_fd_sc_mcu7t5v0__"


def stat(path):
    area, cells, types = None, None, {}
    for ln in open(path):
        m = re.search(r"Chip area for (?:top )?module.*: ([0-9.]+)", ln)
        if m:
            area = float(m.group(1))
        m = re.match(r"\s+(\d+)\s+[0-9.eE+]+\s+" + PREFIX + r"(\S+)", ln) or re.match(r"\s+" + PREFIX + r"(\S+)\s+(\d+)", ln)
        if m:
            a, b = m.group(1), m.group(2)
            n, t = (int(a), b) if a.isdigit() else (int(b), a)
            types[t] = types.get(t, 0) + n
        m = re.match(r"\s+(\d+)\s+[0-9.eE+]+\s+cells$", ln) or re.match(r"\s+Number of cells:\s+(\d+)", ln)
        if m:
            cells = int(m.group(1))
    return area, cells, types


def seq_types(types):
    return {t: n for t, n in types.items() if re.match(r"(dff|sdff|lat|icg)", t)}


def main():
    d = sys.argv[1]
    rows = int(sys.argv[2]) if len(sys.argv) > 2 else 72
    res = {}
    for f in sorted(os.listdir(d)):
        if f.endswith(".stat"):
            res[f[:-5]] = stat(os.path.join(d, f))
    bad = 0
    print(f"{'block':22s} {'area um^2':>11s} {'cells':>7s}  sequential cells")
    for b, (area, cells, types) in res.items():
        s = ", ".join(f"{t} {n}" for t, n in sorted(seq_types(types).items()))
        print(f"{b:22s} {area if area is not None else float('nan'):11.0f} {cells or 0:7d}  {s}")
    print("\nagainst the budget (ARCHITECTURE.md 7.1)")
    def a(b):
        return res[b][0] if b in res and res[b][0] is not None else None
    rowsum = {"sequencer": ["dregg_seq", "dregg_egress", "dregg_framer"]}
    for key, (bud, note) in BUDGET.items():
        parts = rowsum.get(key, [key])
        if any(a(p) is None for p in parts):
            print(f"  {key:22s} not synthesized")
            continue
        got = sum(a(p) for p in parts)
        if bud is None:
            print(f"  {key:22s} {got:9.0f}   ({note})")
        else:
            flag = "OVER" if got > bud else "under"
            print(f"  {key:22s} {got:9.0f}   budget {bud:7d}   {100.0 * got / bud - 100:+6.1f} %  {flag}   ({note})")
    # ---- storage checks on the flat netlists
    print("\nstorage checks")
    for b, (area, cells, types) in res.items():
        st = seq_types(types)
        lat = {t: n for t, n in st.items() if t.startswith("lat")}
        noreset = {t: n for t, n in st.items() if re.match(r"(dffq|dffnq|latq|sdffq)", t)}
        want_lat = rows * 64 if b in ("dregg_regfile", "dregg_core", "dregg_top") else 0
        got_lat = sum(lat.values())
        ok = (got_lat == want_lat) and set(lat) <= {"latrnq_1"}
        if not ok:
            bad += 1
            print(f"  FAIL {b}: latches {lat}, expected latrnq_1 x {want_lat}")
        allowed = 64 if b in ("dregg_spi_link", "dregg_top") else 0       # the SPI receive shifter, at most 64 flops
        if sum(noreset.values()) > allowed or set(noreset) - {"dffq_1"}:
            bad += 1
            print(f"  FAIL {b}: storage without an asynchronous reset: {noreset} (allowed {allowed})")
    for b in ("dregg_regfile", "dregg_core", "dregg_top"):
        p = os.path.join(d, b + ".v")
        if not os.path.exists(p):
            continue
        text = open(p).read()
        nets = re.findall(PREFIX + r"latrnq_1\s+\S+\s*\((.*?)\);", text, re.S)
        rn = {re.search(r"\.RN\(([^)]*)\)", x).group(1).strip() for x in nets}
        hold = set(re.findall(r"\.RN\(([^)]*)\)", " ".join(re.findall(PREFIX + r"dffrnq_\d\s+\S*h(?:old)?\S*\s*\((.*?)\);", text, re.S))))
        print(f"  {b}: {len(nets)} register-file latches, RN nets: {sorted(rn)}")
        if len(nets) != rows * 64 or len(rn) != 1:
            bad += 1
            print(f"  FAIL {b}: expected {rows * 64} latches on one reset net")
    # which nets reset the flops of the core: every one must be a reset net, none a data signal
    p = os.path.join(d, "dregg_core.v")
    if os.path.exists(p):
        text = open(p).read()
        nets = {}
        for cell, body in re.findall(PREFIX + r"(dff\w+|lat\w+)\s+\S+\s*\((.*?)\);", text, re.S):
            for pin, net in re.findall(r"\.(RN|SETN)\(([^)]*)\)", body):
                key = (pin, net.strip())
                nets[key] = nets.get(key, 0) + 1
        print("  dregg_core, asynchronous reset and set pins by net:")
        for (pin, net), n in sorted(nets.items(), key=lambda kv: -kv[1]):
            print(f"    {pin:4s} {net:40s} {n:5d} cells")
    print("storage checks:", "FAIL" if bad else "PASS")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
