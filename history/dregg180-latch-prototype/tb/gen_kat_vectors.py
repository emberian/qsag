#!/usr/bin/env python3
"""FIPS 202 known-answer vectors for the Keccak engine (tb/unit_dp.cpp, tag H).

Usage: gen_kat_vectors.py <out.txt>

Each line: H <rate bytes> <suffix hex> <rounds> <message hex or -> <expected output hex>
The testbench runs the sponge itself (absorb into the register file, permute with the RTL engine,
squeeze) and compares the output bytes. Expected values come from hashlib (OpenSSL's SHA-3, not
this repository's model); the empty-message digests are additionally pinned to the constants
printed in FIPS 202 / the NIST example files, and TurboSHAKE256 to RFC 9861."""
import hashlib
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "model"))
import qsag_prims as q  # noqa: E402  (TurboSHAKE256 only: hashlib has no 12-round variant)

PINNED = {
    "sha3_256": "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
    "sha3_512": "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a6"
                "15b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26",
    "shake_128": "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26",
    "shake_256": "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f",
}
for name, want in PINNED.items():
    h = hashlib.new(name, b"")
    got = h.hexdigest(32) if name.startswith("shake") else h.hexdigest()
    assert got == want, name
assert q.turboshake256(b"", 8).hex() == "367a329dafea871c"   # RFC 9861, TurboSHAKE256(M = empty, D = 1F)

rng = random.Random(0xF1B5202)
lines = []


def emit(rate, suffix, rounds, msg, out):
    lines.append(f"H {rate} {suffix:02x} {rounds} {msg.hex() or '-'} {out.hex()}")


FIXED = [("sha3_224", 144), ("sha3_256", 136), ("sha3_384", 104), ("sha3_512", 72)]
for name, rate in FIXED:
    msgs = [b"", b"abc", bytes([0xA3]) * 200]
    msgs += [bytes(rng.randrange(256) for _ in range(n)) for n in (1, rate - 1, rate, rate + 1, 2 * rate + 5)]
    for m in msgs:
        emit(rate, 0x06, 24, m, hashlib.new(name, m).digest())
for name, rate in (("shake_128", 168), ("shake_256", 136)):
    msgs = [b"", b"abc", bytes([0xA3]) * 200]
    msgs += [bytes(rng.randrange(256) for _ in range(n)) for n in (rate - 1, rate, rate + 1, 3 * rate + 17)]
    for m in msgs:
        emit(rate, 0x1F, 24, m, hashlib.new(name, m).digest(32))
    emit(rate, 0x1F, 24, b"abc", hashlib.new(name, b"abc").digest(2 * rate + 40))   # three squeeze blocks
for n in (0, 1, 135, 136, 137, 400):
    m = bytes(rng.randrange(256) for _ in range(n))
    emit(136, 0x1F, 12, m, q.turboshake256(m, 64))
open(sys.argv[1], "w").write("\n".join(lines) + "\n")
print("wrote", len(lines), "FIPS 202 / RFC 9861 known-answer vectors")
