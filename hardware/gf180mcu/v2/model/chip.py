"""Dregg-180 v2 golden model, top level: ROM image + machine + pins.

    chip = Chip("S")                      # or "L"
    response_words = chip.transact(request_words)
"""
import os

import uasm
from machine import ControlFault, Machine

UCODE = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "ucode"))
SOURCES = {
    # main.uc: address 0; provision.uc: the key range; fram.uc: the record range; the rest from ROM_BASE
    "S": ["defs.uc", "main.uc", "provision.uc", "fram.uc", "ping.uc", "keccak.uc", "sign.uc"],
    "L": ["defs.uc", "main.uc", "provision.uc", "fram.uc", "ping.uc", "keccak.uc", "sign.uc", "field.uc"],
}
_roms = {}


def read_sources(config):
    out = []
    for f in SOURCES[config]:
        with open(os.path.join(UCODE, f)) as fh:
            out.append((f, fh.read()))
    return out


def build_rom(config):
    if config not in _roms:
        _roms[config] = uasm.assemble(read_sources(config))
    return _roms[config]


class Chip:
    def __init__(self, config="S", rom=None, fram=None, puf=None, entropy=None, owner=None):
        """puf, entropy, owner: the stage 3 and 4 interfaces (units.PufUnit, units.EntropyUnit, and a
        callable owner(nonce, digest, signature) -> bool). Each is absent by default, and the chip then
        refuses what needs it: no device secret, no provisioning; no entropy, no nonce; no owner
        verifier, no authorisation."""
        self.config = config
        self.rom = rom or build_rom(config)
        self.m = Machine(self.rom, config, fram, puf, entropy, owner)
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
