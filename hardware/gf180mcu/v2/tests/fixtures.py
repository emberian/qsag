"""Fixture microprograms for the decoder-rule tests. They are run on the model; none is in the ROM.

rom_with(body, where) builds the shipped ROM with one extra routine at opcode 0x7A:
    where = "rom"   appended after the shipped code (ordinary address range)
    where = "key"   in place of provision.uc (the hardwired key range)
    where = "rec"   appended to fram.uc (the hardwired record range)
"""
import common  # noqa: F401
import chip
import host
import isa
import uasm

K = bytes(range(0x40, 0x50))
SEED = bytes(range(0x10, 0x20))
PRF = bytes(range(0x20, 0x30))
TEST_OP = 0x7A


def rom_with(body, where="rom", config="S", end=True):
    text = f".entry {TEST_OP} t_entry diag\nt_entry:\n" + body + ("\n END\n" if end else "\n")
    src = chip.read_sources(config)
    if where == "rom":
        src = src + [("fixture", text)]
    elif where == "key":
        src = [(n, text if n == "provision.uc" else t) for n, t in src]
    elif where == "rec":
        src = [(n, t + text if n == "fram.uc" else t) for n, t in src]
    else:
        raise ValueError(where)
    return uasm.assemble(src)


def run(body, payload=(), keys=True, where="rom", config="S", end=True, **chip_kw):
    c = common.new_chip(config, rom=rom_with(body, where, config, end), **chip_kw)
    if keys:
        # keys are placed directly: the fixture ROM may have no provisioning routine
        for i, w in enumerate(host.words_of(K + SEED + PRF)):
            c.m.rf[isa.KEY0 + 4 + i] = w
        c.m.key_valid = True
    rsp = c.transact([host.hdr(TEST_OP, 0, 8 * len(payload))] + list(payload))
    return c, rsp
