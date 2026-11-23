"""Fixture microprograms for the decoder-rule tests. They are run on the model; none is in the ROM.

rom_with(body, where) builds the shipped ROM with one extra routine at opcode 0x7A:
    where = "rom"   appended after the shipped code (ordinary address range)
    where = "key"   appended to key.uc (the hardwired key range; about 20 words are free)
    where = "rec"   appended to rec.uc (the hardwired record range; about 15 words are free)
"""
import common  # noqa: F401
import chip
import host
import isa
import uasm

KDEV = [0x1111111111111111 * (i + 1) for i in range(4)]
TEST_OP = 0x7A


def rom_with(body, where="rom", config="S", end=True, slh=common.SLH):
    src = chip.read_sources(config, slh)
    tail = "\n END\n" if end else "\n"
    name = {"rom": None, "key": "key.uc", "rec": "rec.uc"}[where]
    if name is None:
        return uasm.assemble(src + [("fixture", f"\n.entry {TEST_OP} t_entry any\nt_entry:\n" + body + tail)])
    # a command starts in the ordinary code (the dispatcher refuses anything else) and branches into the range
    src = [(n, t + "\nt_body:\n" + body + tail if n == name else t) for n, t in src]
    return uasm.assemble(src + [("fixture", f"\n.entry {TEST_OP} t_entry any\nt_entry: BR t_body\n")])


def run(body, payload=(), keys=True, where="rom", config="S", end=True, **chip_kw):
    c = common.new_chip(config, rom=rom_with(body, where, config, end), **chip_kw)
    if keys:
        # the device key is placed directly and the chip is put in READY: the fixture is not a boot
        for i, w in enumerate(KDEV):
            c.m.rf[isa.KEY0 + i] = w
        c.m.lc = isa.LC_READY
    rsp = c.transact([host.hdr(TEST_OP, 0, 8 * len(payload))] + list(payload))
    return c, rsp
