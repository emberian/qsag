"""Measured figures for v2/README.md and ARCHITECTURE.md 7.4: ROM size and clocks per command, from the
interpreter. Signature figures are for SLH-DSA-SHAKE-128s (the chips in the tests use reduced sets).

    python3 -B v2/tests/report.py
"""
import collections

import common
import chip
import host
import isa
import replay
import units

PK = bytes(range(48, 64))
CLK_MHZ = 25


def ms(clocks):
    return clocks / (CLK_MHZ * 1000.0)


def one(c, req):
    c.transact(req)
    return c.log[-1]


def main():
    for cfg in "SL":
        r = chip.build_rom(cfg)
        b = r.bits()
        print(f"ROM {cfg}: {b['used']} words of code in a {b['words']}-word image x 28 = {b['word_bits']} bits; constants {len(r.consts)} x 64; "
              f"dispatch {len(r.entries)} entries; total {b['total_bits']} bits")
    r = chip.build_rom("L")
    files = collections.OrderedDict()
    for a, (f, _, _) in enumerate(r.where):
        if a not in r.padding:
            files[f] = files.get(f, 0) + 1
    print("words per source file:", dict(files))
    print("free words: key range", sum(a in r.padding for a in range(isa.KEY_LO, isa.KEY_HI + 1)),
          "record range", sum(a in r.padding for a in range(isa.REC_LO, isa.REC_HI + 1)))

    rows, failures, inserted = replay.replay("L")
    assert not failures
    print("\nreference script, configuration L:", dict(collections.Counter(x["cls"] for x in rows)))

    print("\nper-operation figures (clocks from dispatch to idle, link waits excluded)")
    d = common.provisioned(config="L")
    c, K = d.chip, d.k_host
    print(f"  PING                                   {one(c, [host.hdr(host.OP_PING)])['cycles']:9d}")
    for turbo, name in ((True, "TurboSHAKE256"), (False, "SHAKE256")):
        a = one(c, host.keccak(b"", 4, 0x1F, turbo))["cycles"]
        b = one(c, host.keccak(bytes(136), 4, 0x1F, turbo))["cycles"]
        print(f"  {name:14s} one block / per extra block {a:6d} / {b - a:5d}")
    p = one(c, [host.hdr(host.OP_P2, 1, 96)] + [1] * 12)
    print(f"  Poseidon2 raw permutation command      {p['cycles']:9d}")
    print(f"  PRF_MSG, 32-byte payload               {one(c, host.prf_msg(bytes(32)))['cycles']:9d}")

    def wots(msg, n, first=0, **kw):
        return one(c, host.cth_wots(K, 0, 0, 1, 2, PK, msg, n, first, **kw))
    refused = one(c, host.cth_wots(bytes(16), 0, 0, 1, 2, PK, bytes(16), 1))
    print(f"  CTH refused for its tag                {refused['cycles']:9d}")
    base = wots(b"\x00" * 16, 1)                 # digit 0: tag + one PRF
    step = wots(b"\x10" + bytes(15), 1)          # digit 1: one F more
    two = wots(b"\x00" * 16, 2)
    per_f, per_prf = step["cycles"] - base["cycles"], two["cycles"] - base["cycles"]
    print(f"  one F step (lane build + Keccak-f)     {per_f:9d}")
    print(f"  one chain start (digit, SK.seed derivation, PRF) {per_prf}")
    print(f"  CTH fixed part (request less its one chain start) {base['cycles'] - per_prf}")
    pub = wots(bytes(16), 35, pubgen=True)
    print(f"  WOTS public key, 35 chains x 15 steps  {pub['cycles']:9d}  ({pub['unit_calls']['keccak']} Keccak calls, {ms(pub['cycles']):.1f} ms)")
    worst = wots(b"\xff" * 16, 35)
    avg = wots(bytes.fromhex("0123456789abcdeffedcba9876543210"), 35)
    print(f"  WOTS signature, all digits 15          {worst['cycles']:9d}  ({worst['unit_calls']['keccak']} calls, {ms(worst['cycles']):.1f} ms)")
    print(f"  WOTS signature, digits 0..15 evenly    {avg['cycles']:9d}  ({avg['unit_calls']['keccak']} calls, {ms(avg['cycles']):.1f} ms)")
    f14 = one(c, host.cth_fors(K, 0, 0, 1, 2, PK, list(range(14))))
    f14p = one(c, host.cth_fors(K, 0, 0, 1, 2, PK, list(range(14)), pubgen=True))
    print(f"  FORS 14 secret leaves / 14 public      {f14['cycles']:6d} / {f14p['cycles']:6d}")
    dc = common.provisioned(host.F_COUNTED)
    s1 = one(dc.chip, host.cth_wots(K, 3, 0, 1, 3, PK, bytes(16), 1))
    print(f"  counted-key overhead (record tag, write, read-back) {s1['cycles'] - base['cycles']}  (FRAM {s1['unit_cycles']['fram']})")

    print("\nlifecycle and gate, SLH-DSA-SHAKE-128s")
    d = common.provisioned(host.F_LEASED | host.F_COUNTED, slh="128s", booted=False)
    log = {x["op"]: x for x in d.chip.log}
    en, cm = log[host.OP_ENROL], log[host.OP_COMMIT]
    print(f"  BOOT of a blank chip                   {log[host.OP_BOOT]['cycles']:9d}  (FRAM {log[host.OP_BOOT]['unit_cycles']['fram']})")
    print(f"  ENROL                                  {en['cycles']:9d}  (PUF {en['unit_cycles']['puf']}, TRNG start-up and nonce {en['unit_cycles']['trng']})")
    print(f"  COMMIT                                 {cm['cycles']:9d}  (PUF {cm['unit_cycles']['puf']}, FRAM {cm['unit_cycles']['fram']}, {cm['unit_calls']['keccak']} Keccak calls)")
    d.chip.reset()
    d.boot()
    bt = d.chip.log[-1]
    rest = bt["cycles"] - bt["unit_cycles"]["puf"] - bt["unit_cycles"]["trng"] - bt["unit_cycles"]["fram"]
    print(f"  BOOT, leased                           {bt['cycles']:9d}  = PUF {bt['unit_cycles']['puf']} + TRNG {bt['unit_cycles']['trng']} + FRAM {bt['unit_cycles']['fram']} "
          f"+ {rest} ({bt['unit_calls']['keccak']} Keccak calls; {ms(bt['cycles']):.0f} ms)")
    d.lease(0, 100)
    ls = d.chip.log[-1]
    print(f"  LEASE, one authority signature         {ls['cycles']:9d}  ({ls['unit_calls']['keccak']} Keccak calls, {ms(ls['cycles']):.0f} ms; {8 * (len(host.lease_request(d.com, [0, 0], 0, [0, 0], 0, 1)) - 1)} bytes)")
    d.gate(host.T_EPOCH, [1])
    g = d.chip.log[-1]
    print(f"  GATE, one authority signature          {g['cycles']:9d}  ({g['unit_calls']['keccak']} Keccak calls, {g['steps']} micro-instructions, {ms(g['cycles']):.0f} ms)")
    one(d.chip, host.cmd(host.OP_NONCE))
    # the fingerprint: clocks of one fold_w call, from a trace
    span = {}
    rom = d.chip.rom
    lo, hi = rom.labels["fold_w"], rom.labels["fw_1n"] + 2

    def trace(pc, w, m):
        if lo <= pc < hi:
            span["n"] = span.get("n", 0) + 1
            span.setdefault("c0", m.cycles)
            span["c1"] = m.cycles
        if pc == lo:
            span["calls"] = span.get("calls", 0) + 1
    d.chip.m.trace = trace
    d.gate(host.T_EPOCH, [2])
    d.chip.m.trace = None
    g2 = d.chip.log[-1]
    print(f"  fingerprint: {span['calls']} words folded, {span['n'] / span['calls'] / 2:.0f} micro-instructions per GF(2^64) product, "
          f"{span['n']} of {g2['steps']} micro-instructions")
    d3 = common.provisioned(n=5, k=3, slh="128s")
    d3.gate(host.T_EPOCH, [1])
    g3 = d3.chip.log[-1]
    print(f"  GATE, 3 of 5                           {g3['cycles']:9d}  ({ms(g3['cycles']):.0f} ms; {8 * (len(host.gate_request(d3.com, [0, 0], 0, 2, [1])) - 1)} bytes)")


if __name__ == "__main__":
    main()
