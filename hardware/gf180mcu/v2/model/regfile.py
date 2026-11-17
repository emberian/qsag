"""The single 64-bit register file (ARCHITECTURE.md 5.2): storage only.

Access rules (which instruction may read or write which row class) are a property of the
instruction decoder and live in machine.py; this class is the latch array and its clears.
"""
import isa


class RegFile:
    def __init__(self, nrows):
        self.nrows = nrows
        self.rows = [0] * nrows

    def __getitem__(self, r):
        return self.rows[r]

    def __setitem__(self, r, v):
        self.rows[r] = v & isa.M64

    def wipe(self, mask):
        """Write-path clear of whole row classes (one clock: every selected row gate opens on a zero hold)."""
        if mask & isa.W_LANES_LO:
            for r in range(0, 8):
                self.rows[r] = 0
        if mask & isa.W_LANES_HI:
            for r in range(8, isa.SCRATCH0):          # lanes 8..24 and the Keccak work rows
                self.rows[r] = 0
        if mask & isa.W_SCRATCH:
            for r in range(isa.SCRATCH0, isa.KEY0):
                self.rows[r] = 0
        if mask & isa.W_OUT:
            for r in range(isa.OUT0, isa.OUT0 + isa.N_OUT):
                self.rows[r] = 0

    def secret_reset(self):
        """Asynchronous clear of every latch (pad reset, tamper, zeroise, control fault)."""
        self.rows = [0] * self.nrows

    def key_values(self):
        return {v for v in self.rows[isa.KEY0:isa.KEY0 + isa.N_KEYS] if v}
