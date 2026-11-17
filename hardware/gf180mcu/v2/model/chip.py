"""Dregg-180 v2 golden model, top level: ROM image + machine + pins.

    chip = Chip("S")                      # or "L"
    response_words = chip.transact(request_words)

A ROM image is built for a signature parameter set and an owner root:

    build_rom("S")                        SLH-DSA-SHAKE-128s, the owner root of host.OWNER_SEED
    build_rom("S", slh="tiny", owner_pin=(w0, w1))

`slh="tiny"` is a reduced parameter set for tests (same n, same digest layout, small trees; see SLH).
The microcode is the same text; only the constants of the generated `params` source differ.
"""
import os

import uasm
from machine import ControlFault, Machine

UCODE = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "ucode"))
# main.uc: address 0; key.uc: the key range; rec.uc: the record range; the rest from ROM_BASE
_S = ["defs.uc", "main.uc", "key.uc", "rec.uc", "ping.uc", "keccak.uc", "hash.uc", "trng.uc", "slh.uc", "life.uc",
      "sign.uc"]
SOURCES = {"S": _S, "L": _S + ["field.uc"]}

# Signature parameter sets: n = 16 and lg_w = 4 in all. k trees of height a (a multiple of 4), d layers of
# height hp. The message digest is always 30 bytes: 21 of FORS indices (the first k * a bits are used), 7 of
# tree index, 2 of leaf index. "small" and "tiny" exist for the tests only.
SLH = {
    "128s": dict(k=14, a=12, d=7, hp=9),
    "small": dict(k=6, a=8, d=2, hp=3),
    "tiny": dict(k=4, a=4, d=1, hp=2),
}
_roms = {}


def package_words(slh):
    """Words of one signature package (ARCHITECTURE.md 4.3): R, FORS values, roots twice, and per layer
    signature values, chain ends twice, path."""
    p = SLH[slh]
    return 2 + 2 * p["k"] * (1 + p["a"]) + 4 * p["k"] + p["d"] * (210 + 2 * p["hp"])


def params_source(slh, owner_pin):
    p = SLH[slh]
    assert p["k"] * p["a"] <= 168 and p["a"] % 4 == 0 and p["hp"] <= 9
    tree_bits = p["hp"] * (p["d"] - 1)
    tree_mask_be = (1 << tree_bits) - 1
    tree_mask = int.from_bytes(tree_mask_be.to_bytes(8, "big"), "little")       # mask of ADRS bytes 8..15
    pkg = package_words(slh)
    return ("params",
            f".equ SLH_K {p['k']}\n.equ SLH_A {p['a']}\n.equ SLH_ANIB {p['a'] // 4}\n.equ SLH_D {p['d']}\n"
            f".equ SLH_HP {p['hp']}\n.equ SLH_LEAFM {(1 << p['hp']) - 1}\n"
            f".equ MB_WORDS {pkg + 4}\n.equ BT_LEN {8 * (pkg + 4)}\n.equ CM_LEN {8 * (pkg + 9)}\n.equ RI_LEN {8 * (pkg + 7)}\n"
            f".const C_TREEM {tree_mask:#x}\n.const C_OWN0 {owner_pin[0]:#x}\n.const C_OWN1 {owner_pin[1]:#x}\n")


def read_sources(config, slh="128s", owner_pin=None):
    if owner_pin is None:
        import host
        owner_pin = host.default_owner_pin(slh)
    out = [params_source(slh, owner_pin)]
    for f in SOURCES[config]:
        with open(os.path.join(UCODE, f)) as fh:
            out.append((f, fh.read()))
    return out


def build_rom(config, slh="128s", owner_pin=None):
    key = (config, slh, tuple(owner_pin) if owner_pin else None)
    if key not in _roms:
        _roms[key] = uasm.assemble(read_sources(config, slh, owner_pin))
    return _roms[key]


class Chip:
    def __init__(self, config="S", rom=None, fram=None, puf=None, trng=None, slh="128s", owner_pin=None):
        """puf, trng: the organ models (units.PufUnit, units.TrngUnit). Each is absent by default, and the
        chip then refuses what needs it: no PUF, no enrolment and no boot; no TRNG, no nonce."""
        self.config, self.slh = config, slh
        self.rom = rom or build_rom(config, slh, owner_pin)
        self.m = Machine(self.rom, config, fram, puf, trng)
        self.log = []                       # per command: dict(op, cycles, ...)

    fram = property(lambda s: s.m.fram.mem)

    def transact(self, words):
        """One request in, one response out. A control fault clears every secret and answers nothing."""
        m = self.m
        op = (words[0] >> 8) & 0xFF
        try:
            rsp = m.run(list(words))
        except ControlFault:
            self.log.append(dict(op=op, fault=True))
            raise
        self.log.append(dict(op=op, cycles=m.cycles, steps=m.steps, stalls=m.stalls,
                             unit_cycles=dict(m.unit_cycles), unit_calls=dict(m.unit_calls),
                             key_words_emitted=list(m.key_words_emitted)))
        return rsp

    def reset(self):
        """Pad reset or power cycle: all chip state is volatile; the FRAM keeps its contents."""
        self.m.power_on()

    @property
    def pins(self):
        m = self.m
        return dict(VERIFY_OK=int(m.verify_ok), FAULT=int(m.fault_mac or m.fault_anchor or m.fault_control))
