"""Shared test support: import paths, the reference script, row checks."""
import os
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
V2 = os.path.normpath(os.path.join(HERE, ".."))
CHIPDIR = os.path.normpath(os.path.join(V2, ".."))
sys.path.insert(0, os.path.join(V2, "model"))
FIXTURE = os.path.join(CHIPDIR, "tb", "fixtures", "lean_external_oracle_vectors.json")

import isa  # noqa: E402

_script = {}


def reference_script(quick=False):
    """The directives tb/gen_script.py writes from the reference golden model, unmodified.
    Returns a list of (kind, payload): ('note', text), ('xfer', (name, tx, rx)), ('pin', (name, value)),
    ('framchk', (slot, bytes)), ('framsave', None), ('framrestore', None). rx words are int or None."""
    if quick in _script:
        return _script[quick]
    with tempfile.TemporaryDirectory() as d:
        out = os.path.join(d, "script.txt")
        cmd = [sys.executable, os.path.join(CHIPDIR, "tb", "gen_script.py"), FIXTURE, out] + (["quick"] if quick else [])
        subprocess.run(cmd, check=True, capture_output=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        with open(out) as fh:
            lines = fh.read().splitlines()
    items, note, tx = [], "", None
    for ln in lines:
        tag, _, rest = ln.partition(" ")
        if tag == "#":
            note = rest
            items.append(("note", rest))
        elif tag == "TX":
            tx = [int(w, 16) for w in rest.split()]
        elif tag == "RX":
            items.append(("xfer", (note, tx, [None if w == "-" else int(w, 16) for w in rest.split()])))
        elif tag == "PIN":
            n, v = rest.split()
            items.append(("pin", (n, int(v))))
        elif tag == "FRAMCHK":
            s, hx = rest.split()
            items.append(("framchk", (int(s), bytes.fromhex(hx))))
        elif tag == "FRAMSAVE":
            items.append(("framsave", None))
        elif tag == "FRAMRESTORE":
            items.append(("framrestore", None))
        else:
            raise ValueError(ln)
    _script[quick] = items
    return items


# ---------------------------------------------------------------- chips for the tests
# Most tests use the reduced signature parameter set "tiny" (model/chip.py SLH): the microcode is the
# same text, a verification is 0.2 s instead of 3. A few use "small" (two layers) and one uses 128s.
SLH = "tiny"
FAST = bool(os.environ.get("DREGG_FAST"))           # set by mutation.py
DEV = bytes(range(0xD0, 0xF0))                      # seed of the PUF response of the model die
_cache = {}


def owner(slh=SLH):
    import host
    return host.signer(host.OWNER_SEED, slh)


def committee(n=1, k=None, slh=SLH, tag=b"member"):
    """A committee of n model members; n = 1 is the single authority key."""
    import host
    key = ("committee", n, k, slh, tag)
    if key not in _cache:
        _cache[key] = host.Committee([host.signer(tag + bytes([i]), slh) for i in range(n)], k)
    return _cache[key]


def new_chip(config="S", slh=SLH, puf=DEV, trng=1, **kw):
    """An unprovisioned chip with the PUF and TRNG organ models present (puf, trng: seeds, or None)."""
    import units
    from chip import Chip
    return Chip(config, slh=slh, puf=None if puf is None else units.PufUnit(puf),
                trng=None if trng is None else units.TrngUnit(trng), **kw)


class Dev:
    """A provisioned chip and what the parties outside it know."""

    def __init__(self, chip, info, com, slh):
        import host
        self.chip, self.info, self.com, self.slh = chip, info, com, slh
        self.k_dev = host.k_dev(chip.m.puf.ideal, info["nonce"])
        self.k_host, self.seed, self.prf = (host.derive(self.k_dev, x) for x in (host.L_HOST, host.L_SEED, host.L_PRF))
        self.tag = list(info["tag"])
        self.chip_id = self.tag[0]                  # the word BOOT reports

    rec0 = property(lambda s: s.chip.m.rf[isa.STATE0])
    rec1 = property(lambda s: s.chip.m.rf[isa.STATE0 + 1])
    lc = property(lambda s: s.chip.m.lc)

    def boot(self):
        import host
        return host.boot(self.chip, self.info["helper_sig"])

    def reboot(self):
        self.chip.reset()
        return self.boot()

    def gate(self, typ, args, who=None, **kw):
        import host
        return self.chip.transact(host.gate_request(self.com, self.tag, self.rec0, typ, args, who=who, **kw))

    def lease(self, base, bound, nonce=None, who=None):
        import host
        if nonce is None:
            nonce = [self.chip.m.rf[isa.STATE0 + 7], self.chip.m.rf[isa.STATE0 + 8]]
        return self.chip.transact(host.lease_request(self.com, self.tag, self.rec0, nonce, base, bound, who))


def provisioned(flags=0, n=1, k=None, slh=SLH, config="S", booted=True, u0=0, lease=None):
    """A fresh copy of a chip that has been enrolled and committed (and, by default, reset and booted;
    lease = (base, bound) also takes a leased chip to READY). Built once per argument set and copied."""
    import copy
    import host
    key = ("dev", flags, n, k, slh, config, booted, u0, lease)
    if key not in _cache:
        com = committee(n, k, slh)
        c = new_chip(config, slh)
        info = host.provision(c, owner(slh), com.root, flags, com.k, u0)
        assert len(info["rsp"]) == 3, info["rsp"]
        d = Dev(c, info, com, slh)
        if booted:
            c.reset()
            rsp = d.boot()
            assert rsp[1] == (host.LC_LEASE if flags & host.F_LEASED else host.LC_READY), rsp
            if lease:
                assert len(d.lease(*lease)) == 3
        _cache[key] = d
    return copy.deepcopy(_cache[key])


def working_rows_clear(chip):
    rf = chip.m.rf
    return all(rf[r] == 0 for r in list(range(0, isa.KEY0)) + list(range(isa.OUT0, isa.OUT0 + isa.N_OUT)))


def match(got, exp):
    return len(got) == len(exp) and all(e is None or g == e for g, e in zip(got, exp))
