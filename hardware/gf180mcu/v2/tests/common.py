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


# model stand-ins for the stage 3 and 4 interfaces
DEV = bytes(range(0xD0, 0xF0))                      # device secret (PUF interface)


def new_chip(config="S", owner=None, **kw):
    """A chip with the device-secret, entropy and owner-verifier interfaces present."""
    import host
    import units
    from chip import Chip
    owner = owner or host.Owner()
    c = Chip(config, puf=units.PufUnit(DEV), entropy=units.EntropyUnit(1), owner=owner.verify, **kw)
    c.owner = owner
    return c


def working_rows_clear(chip):
    rf = chip.m.rf
    return all(rf[r] == 0 for r in list(range(0, isa.KEY0)) + list(range(isa.OUT0, isa.OUT0 + isa.N_OUT)))


def match(got, exp):
    return len(got) == len(exp) and all(e is None or g == e for g, e in zip(got, exp))
