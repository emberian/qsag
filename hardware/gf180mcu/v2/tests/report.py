"""Measured figures for v2/README.md: ROM size and clocks per command, from the interpreter.

    python3 -B v2/tests/report.py
"""
import collections

import common  # noqa: F401
import chip
import host
import replay
import units

K, SEED, PRF, PK = bytes(range(16)), bytes(range(16, 32)), bytes(range(32, 48)), bytes(range(48, 64))
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

    print("\nreference script, configuration L (clocks from dispatch to idle, link waits excluded)")
    rows, failures, inserted = replay.replay("L")
    assert not failures
    print("  inserted:", inserted)
    for x in rows:
        print(f"  {x['op']:02x} {x['cls']:10s} {x['cycles']:7d}  keccak {x['keccak']:3d}  p2 {x['field']:2d}  "
              f"fram {x['fram']:5d}  {x['name'][:64]}")

    print("\nper-operation figures")
    c = common.new_chip("L")
    print(f"  PING                                   {one(c, [host.hdr(host.OP_PING)])['cycles']:9d}")
    for turbo, name in ((True, "TurboSHAKE256"), (False, "SHAKE256")):
        a = one(c, host.keccak(b"", 4, 0x1F, turbo))["cycles"]
        b = one(c, host.keccak(bytes(136), 4, 0x1F, turbo))["cycles"]
        print(f"  {name:14s} one block / per extra block {a:6d} / {b - a:5d}")
    p = one(c, [host.hdr(host.OP_P2, 1, 96)] + [1] * 12)
    print(f"  Poseidon2 raw permutation command      {p['cycles']:9d}")
    nn = one(c, host.provision_nonce())
    nonce = c.m.nonce
    body = host.keyload_body(K, SEED, PRF)
    kl = one(c, body + c.owner.authorise(nonce, body))
    print(f"  PROVISION_NONCE                        {nn['cycles']:9d}")
    print(f"  KEYLOAD with anchor initialisation     {kl['cycles'] - kl['unit_cycles']['auth']:9d}  (FRAM {kl['unit_cycles']['fram']}), "
          f"plus the owner-root verification stand-in {kl['unit_cycles']['auth']}")
    print(f"  PRF_MSG, 32-byte payload               {one(c, host.prf_msg(bytes(32)))['cycles']:9d}")

    def wots(msg, n, first=0, **kw):
        return one(c, host.cth_wots(K, 0, 0, 1, 2, PK, msg, n, first, **kw))
    refused = one(c, host.cth_wots(bytes(16), 0, 0, 1, 2, PK, bytes(16), 1))
    print(f"  CTH refused for its tag                {refused['cycles']:9d}")
    base = wots(b"\x00" * 16, 1)                 # digit 0: tag + one PRF
    step = wots(b"\x10" + bytes(15), 1)          # digit 1: one F more
    two = wots(b"\x00" * 16, 2)
    print(f"  CTH with one chain of 0 steps          {base['cycles']:9d}")
    print(f"  one F step (lane build + Keccak-f)     {step['cycles'] - base['cycles']:9d}")
    print(f"  one chain start (digit + PRF)          {two['cycles'] - base['cycles']:9d}")
    pub = wots(bytes(16), 35, pubgen=True)
    print(f"  WOTS public key, 35 chains x 15 steps  {pub['cycles']:9d}  ({pub['unit_calls']['keccak']} Keccak calls, {ms(pub['cycles']):.1f} ms at {CLK_MHZ} MHz)")
    worst = wots(b"\xff" * 16, 35)
    avg = wots(bytes.fromhex("0123456789abcdeffedcba9876543210"), 35)
    print(f"  WOTS signature, all digits 15 (most steps in the message chains) {worst['cycles']}  ({worst['unit_calls']['keccak']} calls, {ms(worst['cycles']):.1f} ms)")
    print(f"  WOTS signature, digits 0..15 evenly    {avg['cycles']:9d}  ({avg['unit_calls']['keccak']} calls, {ms(avg['cycles']):.1f} ms)")
    f14 = one(c, host.cth_fors(K, 0, 0, 1, 2, PK, list(range(14))))
    f14p = one(c, host.cth_fors(K, 0, 0, 1, 2, PK, list(range(14)), pubgen=True))
    print(f"  FORS 14 secret leaves / 14 public      {f14['cycles']:6d} / {f14p['cycles']:6d}")
    cc = common.new_chip("L")
    assert len(host.provision(cc, cc.owner, K, SEED, PRF, True, True)) == 1
    s1 = one(cc, host.cth_wots(K, 3, 0, 1, 3, PK, bytes(16), 1))
    print(f"  counted-key overhead (2 record reads, write, read-back) {s1['cycles'] - base['cycles']}  (FRAM {s1['unit_cycles']['fram']})")
    per_call_f = step['cycles'] - base['cycles']
    per_call_prf = two['cycles'] - base['cycles']
    print(f"  CTH fixed part (request less its one PRF call) {base['cycles'] - per_call_prf}")
    print(f"\n  clocks per hash call as the signer uses it: F {per_call_f}, PRF {per_call_prf} "
          f"(Keccak-f itself {units.KECCAK_F}); ARCHITECTURE.md 7.4 assumed 760")


if __name__ == "__main__":
    main()
