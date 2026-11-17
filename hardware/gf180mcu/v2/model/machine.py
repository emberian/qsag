"""Microcode interpreter: the sequencer, the instruction decoder with its structural rules, the
egress, and clock accounting. One call of run() executes one command, from the dispatch at
address 0 to the hardware end action.

Structural rules. Each is a decoder or sequencer check that uses only hardwired constants (isa.py)
and state of the sequencer; none reads a property of the ROM image. A violation is a control fault:
every latch is cleared and nothing is answered.

  Key rows
  R1  key rows are read only by KMOV and written only by KEYWR. KEYWR, CTL SETKV, CTL AUTH and
      CTL NONCE decode only at addresses KEY_LO..KEY_HI. KEYWR and SETKV also need the authorisation
      latch, which only CTL AUTH sets, in the same command.
  R2  KMOV writes a rate lane (0..16), sets `keyed`, `dirty` and the lane taint, and clears H.
  R3  while `dirty` (a key was copied into the lanes and no permutation has run since), a lane is
      read only by an XOR that stores back to the same lane, and H is cleared afterwards.
  R4  while `keyed` (until the command ends), capacity lanes 17..24 are never read by the word unit.
      The Keccak work rows are never read or written by the word unit.

  Taint (key-derived data)
  R5  four flags: T_lanes (the lanes hold key-derived data), T_H, T_Z, T_CY. KMOV sets T_lanes; only a
      wipe of all lanes clears it. Reading a lane while T_lanes taints H; H's taint follows it through
      the word unit; CMP taints Z, ADD and SUB taint the carry.
  R6  a tainted H is stored only to a lane or (KEYWR) a key row. Scratch, pin, state and challenge
      rows, the index register and the loop counters therefore never hold key-derived data.
  R7  refused when the value is tainted: PUSH, HDR (length), SETX H, SETC H, FRAM RSTART / WSTART
      (slot), CTL SETKV, CTL VOK, and every branch on a tainted flag (Z, carry, H = 0).
  R8  declassification points, the only ways key-derived data crosses R7:
        REL lane   a rate lane, after a permutation, to the response
        CMPT lane  compares an untainted H (a word the host or the FRAM supplied) with a rate lane
                   after a permutation; the verdict in Z is not tainted
        FRAM WWORD lane 0 | lane 1   a record tag to the FRAM (R11)

  Response
  R9  the response is written only by PUSH and REL, after the one HDR of the command. HDR's length is
      at most the cap in the instruction; the egress stops at that length and the end action pads to
      it. Out rows are not addressable. FAIL is refused after HDR.
  R10 a command ends only by END or FAIL (or a hardware refusal in DISP). The end action is hardware:
      pad the response, clear every working row and the session flags, discard unread payload, go to
      address 0. No instruction can branch to address 0, and DISP decodes only there.

  FRAM
  R11 FRAM instructions decode only at addresses REC_LO..REC_HI. FRAM WWORD sends one of three rows:
      the record counter row (scratch 9) or lane 0 or 1 after a permutation. A transaction is three
      words in one direction.

  Lifecycle
  R12 DISP refuses by class: provisioning commands need the device secret and no key yet; keyed
      commands need a valid key. Bad magic and unknown opcodes are refused by DISP itself.
"""
import isa
import units
from framing import Framer
from regfile import RegFile


class ControlFault(Exception):
    def __init__(self, msg, pc, place):
        super().__init__(f"{msg} at {place} (address {pc})")
        self.msg, self.pc, self.place = msg, pc, place


class Machine:
    MAX_STEPS = 20_000_000

    def __init__(self, rom, config="S", fram=None, puf=None, entropy=None, owner=None):
        assert config in ("S", "L")
        self.rom, self.config = rom, config
        self.rf = RegFile(isa.ROWS_L if config == "L" else isa.ROWS_S)
        self.keccak, self.field, self.fram = units.KeccakUnit(), units.FieldUnit(), units.FramUnit(fram)
        self.puf, self.entropy, self.owner = puf, entropy, owner
        self.framer = Framer()
        self.trace = None                   # optional callback(pc, word, machine)
        self.boot_cycles = 0
        self.power_on()

    # ------------------------------------------------------------ state
    def power_on(self):
        """Reset, power cycle or control fault: everything on the chip is volatile. The FRAM is not
        part of the chip. Boot then re-derives the device secret if the PUF interface is present."""
        self.rf.secret_reset()
        self.key_valid = False
        self.key_attr = 0
        self.nonce = None
        self.fault_mac = self.fault_anchor = self.fault_control = False
        self.verify_ok = False
        self.fram.abort()
        self.framer = Framer()
        self.dev_ok = False
        if self.puf is not None:
            for i, w in enumerate(self.puf.reconstruct()):
                self.rf[isa.KEY0 + i] = w
            self.dev_ok = True
            self.boot_cycles = units.PUF_BOOT
        self._session()

    def _session(self):
        self.pc = isa.IDLE_ADDR
        self.h = 0
        self.z = self.cy = 0
        self.x = 0
        self.c = [0, 0]
        self.stack = []
        self.keyed = self.dirty = False
        self.t_lanes = self.t_h = self.t_z = self.t_cy = False
        self.hdr_done = self.failed = False
        self.auth_ok = False
        self.limit = 0
        self.last_w = None

    def status_word(self):
        return (int(self.key_valid) | (int(self.fault_mac) << 1) | (int(self.fault_anchor) << 2)
                | (int(self.dev_ok) << 3) | ((self.key_attr & 0xF) << 4)
                | (int(self.config == "L") << 8) | (self.rom.used << 32))

    # ------------------------------------------------------------ decoder helpers
    def _fault(self, msg):
        raise ControlFault(msg, self.cur_pc, self.rom.place(self.cur_pc))

    def _rd(self, row, same=None):
        """Value and taint of a row as the word unit reads it."""
        cls = isa.row_class(row, self.rf.nrows)
        if cls in ("none", "key", "out", "kwork"):
            self._fault(f"read of {cls} row {row}")
        tainted = False
        if cls == "lane":
            if self.dirty and row != same:
                self._fault(f"read of lane {row} while a key is in the lanes")
            if self.keyed and row >= isa.RATE_LANES:
                self._fault(f"read of capacity lane {row} in a keyed command")
            tainted = self.t_lanes
        if row == self.last_w:
            self.cycles += 1                # the row is transparent this clock: one stall
            self.stalls += 1
        return self.rf[row], tainted

    def _wr(self, row, v, tainted):
        cls = isa.row_class(row, self.rf.nrows)
        if cls in ("none", "key", "out", "kwork"):
            self._fault(f"write of {cls} row {row}")
        if tainted:
            if cls != "lane":
                self._fault(f"store of key-derived data to {cls} row {row}")
            self.t_lanes = True
        self.rf[row] = v
        self.cur_w = row

    def _goto(self, t):
        if t == isa.IDLE_ADDR:
            self._fault("transfer to the idle address")
        if not 0 <= t < len(self.rom.words):
            self._fault("transfer outside the ROM")
        self.pc = t

    def _in_key_range(self):
        return isa.KEY_LO <= self.cur_pc <= isa.KEY_HI

    def _cond(self, c):
        n = isa.COND[c]
        if n in ("Z", "NZ") and self.t_z:
            self._fault("branch on a key-derived compare result")
        if n in ("CY", "NC") and self.t_cy:
            self._fault("branch on a key-derived carry")
        if n in ("HZ", "HNZ") and self.t_h:
            self._fault("branch on key-derived data")
        return {"AL": True, "Z": bool(self.z), "NZ": not self.z, "CY": bool(self.cy), "NC": not self.cy,
                "HZ": self.h == 0, "HNZ": self.h != 0, "MORE": self.framer.remaining > 0,
                "NOMORE": self.framer.remaining == 0, "KV": self.key_valid, "NKV": not self.key_valid,
                "C1Z": self.c[1] == 0, "C1NZ": self.c[1] != 0}[n]

    def _emit(self, v):
        if not self.hdr_done or self.failed:
            self._fault("PUSH before the response header")
        if self.sent >= self.limit:
            self._fault("PUSH beyond the declared response length")
        self.rf[isa.OUT0 + self.sent % isa.N_OUT] = v      # the out rows are the egress FIFO
        self.response.append(self.rf[isa.OUT0 + self.sent % isa.N_OUT])
        self.sent += 1
        if v and v in self.rf.key_values():
            self.key_words_emitted.append((self.cur_pc, v))

    def _end(self):
        """The hardware end action (R10)."""
        if not (self.hdr_done or self.failed):
            self._fault("command ended without a response header")
        while self.sent < self.limit:               # a short routine cannot desynchronise the link
            self.response.append(0)
            self.sent += 1
        self.rf.wipe(isa.W_LANES_LO | isa.W_LANES_HI | isa.W_SCRATCH | isa.W_OUT)
        self.framer.drain()
        self.fram.abort()
        self.cycles += isa.END_CLOCKS - 1
        self._session()

    def _refuse(self, code):
        self.failed, self.limit = True, 0
        self.response.append(self.framer.response_header(0, False, code))
        self._end()

    # ------------------------------------------------------------ one command
    def run(self, words):
        """Execute one request (list of 64-bit words). Returns the response words."""
        self.framer.begin(words)
        self._session()
        self.response = []
        self.sent = 0
        self.cycles = self.steps = self.stalls = 0
        self.unit_cycles = {"keccak": 0, "field": 0, "fram": 0, "auth": 0}
        self.unit_calls = {"keccak": 0, "field": 0}
        self.key_words_emitted = []
        self.verify_ok = False
        try:
            while self._step():
                if self.steps > self.MAX_STEPS:
                    self._fault("runaway microprogram")
        except ControlFault:
            self.power_on()
            self.fault_control = True
            raise
        return self.response

    def _step(self):
        rom = self.rom
        pc = self.cur_pc = self.pc
        if pc >= len(rom.words):
            self._fault("fell off the end of the ROM")
        w = rom.words[pc]
        d = isa.decode(w)
        mn = isa.OPS[d["op"]]
        if self.trace:
            self.trace(pc, w, self)
        self.steps += 1
        self.cycles += 1
        self.cur_w = None
        self.pc = pc + 1
        fr = self.framer
        a = (d["a"] + self.x) & 127 if d["ia"] else d["a"]
        b = (d["b"] + self.x) & 127 if d["ib"] else d["b"]
        store = d["fn"] & 1
        taken = False
        clear_h = False

        if mn == "NOP":
            pass
        elif mn == "CMP":
            if d["fn"] & 2:
                x, tx = isa.imm16(d), False
            else:
                x, tx = self._rd(a)
            if store and not d["fn"] & 2:           # CMPT: the declassified tag verdict (R8)
                if self.t_h:
                    self._fault("CMPT with key-derived data in H")
                if isa.row_class(a, self.rf.nrows) != "lane" or a >= isa.RATE_LANES:
                    self._fault("CMPT operand is not a rate lane")
                if self.h != x:
                    self.z = 1
            else:
                if self.h != x:
                    self.z = 1
                self.t_z = self.t_z or self.t_h or tx
        elif mn in isa.ALU2:
            if d["fn"] & 2:
                x, tx = isa.imm16(d), False
                store = 0
            else:
                x, tx = self._rd(a, same=b if store and mn == "XOR" else None)
                if self.dirty and isa.row_class(a, self.rf.nrows) == "lane":
                    clear_h = True
            self.h, cy, _ = units.alu(mn, self.h, x)
            self.t_h = tx if mn == "LD" else (self.t_h or tx)
            if cy is not None:
                self.cy, self.t_cy = cy, self.t_h
            if store:
                self._wr(b, self.h, self.t_h or clear_h)
        elif mn == "UN":
            self.h = units.unary(d["a"], self.h)
            if store:
                self._wr(b, self.h, self.t_h)
        elif mn == "DIN":
            if fr.remaining == 0:
                self._fault("DIN past the end of the payload")
            self.h, self.t_h = fr.din(), False
            if store:
                self._wr(b, self.h, False)
        elif mn == "LDF":
            n = isa.LDF[d["a"]]
            nonce = self.nonce or [0, 0]
            self.h = {"HDRW": fr.hdr, "FLAGS": fr.flags, "LEN": fr.length, "NWORDS": fr.remaining, "ARG": fr.arg,
                      "ARGLO": fr.arg & 0xFF, "ARGHI": fr.arg >> 8, "X": self.x, "STATUS": self.status_word(),
                      "NONCE0": nonce[0], "NONCE1": nonce[1], "KATTR": self.key_attr}[n]
            self.t_h = False
            if store:
                self._wr(b, self.h, False)
        elif mn == "LDC":
            self.h, self.t_h = rom.consts[d["a"]], False
            if store:
                self._wr(b, self.h, False)
        elif mn == "PUSH":
            if d["fn"] & 2:
                if self.t_h:
                    self._fault("PUSH of key-derived data")
                self._emit(self.h)
            elif d["fn"] & 1:                       # REL (R8)
                if isa.row_class(a, self.rf.nrows) != "lane" or a >= isa.RATE_LANES:
                    self._fault("REL operand is not a rate lane")
                v, _ = self._rd(a)
                self._emit(v)
            else:
                if isa.row_class(a, self.rf.nrows) not in ("lane", "scratch", "pin", "state", "chal"):
                    self._fault(f"PUSH of {isa.row_class(a, self.rf.nrows)} row {a}")
                v, tx = self._rd(a)
                if tx:
                    self._fault("PUSH of key-derived data")
                self._emit(v)
        elif mn == "HDR":
            if self.hdr_done or self.failed:
                self._fault("second response header")
            if self.t_h:
                self._fault("response length from key-derived data")
            if d["fn"] & 1 and self.t_z:
                self._fault("response flag from a key-derived compare result")
            n = self.h & 0xFFFFFF
            if n > isa.imm16(d):
                self._fault("response longer than the routine's cap")
            self.hdr_done, self.limit = True, n
            self.response.append(fr.response_header(n, (not self.z) if d["fn"] & 1 else True, 0))
        elif mn == "FAIL":
            if self.hdr_done or self.failed:
                self._fault("FAIL after the response header")
            self._refuse(isa.imm16(d))
            return False
        elif mn == "KMOV":
            if isa.row_class(a, self.rf.nrows) != "key":
                self._fault("KMOV source is not a key row")
            if not 0 <= b < isa.RATE_LANES:
                self._fault("KMOV destination is not a rate lane")
            self.rf[b] = self.rf[a]
            self.cur_w = b
            self.keyed = self.dirty = self.t_lanes = True
            clear_h = True
            self.cycles += 1
        elif mn == "KEYWR":
            if not self._in_key_range():
                self._fault("KEYWR outside the key range")
            if not self.auth_ok:
                self._fault("KEYWR without authorisation")
            if isa.row_class(b, self.rf.nrows) != "key":
                self._fault("KEYWR destination is not a key row")
            self.rf[b] = self.h
            self.cur_w = b
            clear_h = True
        elif mn == "CTL":
            n = isa.CTL[d["a"]]
            if n == "CLRZ":
                self.z, self.t_z = 0, False
            elif n == "SETKV":
                if not self._in_key_range():
                    self._fault("SETKV outside the key range")
                if not self.auth_ok:
                    self._fault("SETKV without authorisation")
                if self.t_h:
                    self._fault("key attribute from key-derived data")
                self.key_valid, self.key_attr = True, self.h & 0xF
            elif n == "SETFM":
                self.fault_mac = True
            elif n == "SETFA":
                self.fault_anchor = True
            elif n == "VOK":
                if self.t_z:
                    self._fault("verdict pin from a key-derived compare result")
                self.verify_ok = not self.z
            elif n == "NONCE":
                if not self._in_key_range():
                    self._fault("NONCE outside the key range")
                if self.entropy is None:
                    self.nonce, self.z = None, 1
                else:
                    self.nonce = self.entropy.draw()
                    self.cycles += units.NONCE_DRAW
            elif n == "AUTH":
                # Owner-root authorisation of the statement (nonce, lanes 0..3), read from the next two
                # payload words. Stage 4 replaces the two words by a signature stream and this call by
                # the signature-verification routine; the interface is the same. One attempt per nonce.
                if not self._in_key_range():
                    self._fault("AUTH outside the key range")
                if fr.remaining < 2:
                    self._fault("AUTH past the end of the payload")
                sig = [fr.din(), fr.din()]
                nonce, self.nonce = self.nonce, None
                digest = [self.rf[isa.LANE0 + i] for i in range(4)]
                ok = (nonce is not None and self.owner is not None and not self.t_lanes
                      and self.owner(nonce, digest, sig))
                self.cycles += units.AUTH_VERIFY
                self.unit_cycles["auth"] += units.AUTH_VERIFY
                if ok:
                    self.auth_ok = True
                else:
                    self.z = 1
        elif mn == "WIPE":
            self.rf.wipe(d["a"])
            if d["a"] & 3 == 3:
                self.dirty = self.t_lanes = False
        elif mn == "KEC":
            if self.last_w is not None:
                self.cycles += 1
            n = self.keccak.run(self.rf, 12 if d["a"] else 24)
            self.cycles += n
            self.unit_cycles["keccak"] += n
            self.unit_calls["keccak"] += 1
            self.dirty = False
        elif mn in ("FLD", "FADD"):
            if self.config != "L":
                self._fault("field unit instruction in configuration S")
            if mn == "FADD":
                x, tx = self._rd(a)
                self.h, self.t_h = self.field.add(self.h, x), self.t_h or tx
                self.cycles += units.FIELD_ADD - 1
            elif isa.FLD[d["a"]] == "RED":
                self.h = self.field.red(self.h)
                self.cycles += units.FIELD_RED - 1
            else:
                if self.dirty or self.keyed:
                    self._fault("Poseidon2 in a keyed command")
                if self.last_w is not None:
                    self.cycles += 1
                n = self.field.perm(self.rf)
                self.cycles += n
                self.unit_cycles["field"] += n
                self.unit_calls["field"] += 1
                store = 0
            if store:
                self._wr(b, self.h, self.t_h)
        elif mn == "FRAM":
            if not isa.REC_LO <= pc <= isa.REC_HI:
                self._fault("FRAM instruction outside the record range")
            n = isa.FRAM[d["a"]]
            try:
                if n in ("RSTART", "WSTART"):
                    if self.t_h:
                        self._fault("FRAM slot from key-derived data")
                    k = self.fram.start(self.h & 1, n == "WSTART")
                elif n == "RWORD":
                    self.h, k = self.fram.rword()
                    self.t_h = False
                    if store:
                        self._wr(b, self.h, False)
                elif n == "WWORD":
                    if d["ib"] or d["b"] not in isa.FRAM_SRC:
                        self._fault(f"FRAM WWORD of row {b}")
                    v, _ = self._rd(d["b"])         # lanes: refused while dirty (R3); tag lanes are released (R8)
                    k = self.fram.wword(v)
                else:
                    k = self.fram.done()
            except units.FramMisuse as e:
                self._fault(str(e))
            self.cycles += k
            self.unit_cycles["fram"] += k
        elif mn == "SETX":
            if d["fn"] & 1 and self.t_h:
                self._fault("index from key-derived data")
            self.x = (self.h if d["fn"] & 1 else d["a"]) & 127
        elif mn == "SETC":
            if d["a"] & 2 and self.t_h:
                self._fault("loop count from key-derived data")
            self.c[d["a"] & 1] = (self.h if d["a"] & 2 else isa.target(d)) & 0xFFF
        elif mn == "BR":
            if self._cond(d["a"]):
                self._goto(isa.target(d))
                taken = True
        elif mn == "BXNE":
            if self.x != d["a"]:
                self._goto(isa.target(d))
                taken = True
        elif mn == "DBNZ":
            i = d["a"] & 1
            self.c[i] = (self.c[i] - 1) & 0xFFF
            if self.c[i]:
                self._goto(isa.target(d))
                taken = True
        elif mn == "CALL":
            if len(self.stack) >= 2:
                self._fault("return stack overflow")
            self.stack.append(pc + 1)
            self._goto(isa.target(d))
            taken = True
        elif mn == "DISP":
            if pc != isa.IDLE_ADDR:
                self._fault("DISP away from address 0")
            code = 0
            if not fr.magic_ok:
                code = isa.E_MAGIC
            elif fr.op not in rom.entries:
                code = isa.E_OPCODE
            else:
                addr, cls = rom.entries[fr.op]
                if cls == isa.D_PROV and not self.dev_ok:
                    code = isa.E_NOKEY
                elif cls == isa.D_PROV and self.key_valid:
                    code = isa.E_KEYSET
                elif cls == isa.D_KEYED and not self.key_valid:
                    code = isa.E_NOKEY
            if code:
                self._refuse(code)
                return False
            self.pc = addr
        elif mn == "END":
            self._end()
            return False
        else:
            self._fault("illegal instruction")

        if clear_h:
            self.h, self.t_h = 0, False
        if d["xi"]:
            self.x = (self.x + 1) & 127
        if d["seq"] & 1 and not taken:
            if not self.stack:
                self._fault("return with an empty stack")
            self._goto(self.stack.pop())
        self.last_w = self.cur_w
        return True
