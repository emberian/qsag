"""Microcode interpreter: the sequencer, the instruction decoder with its structural rules, the
egress, and clock accounting. One call of run() executes one command, from the dispatch at
address 0 to the hardware end action.

Structural rules. Each is a decoder or sequencer check that uses only hardwired constants (isa.py)
and state of the sequencer; none reads a property of the ROM image. A violation is a control fault:
every latch is cleared and nothing is answered.

  Key rows
  R1  key rows are read only by KMOV and written only by KEYWR. KEYWR decodes only at addresses
      KEY_LO..KEY_HI and needs the verdict latch, which only CTL AUTH sets (in the key range, from an
      untainted and clear compare flag), in the same command.
  R2  KMOV writes a rate lane (0..16), sets `keyed`, `dirty` and the lane taint, and clears H.
  R3  while `dirty` (a key was copied into the lanes and no permutation has run since), a lane is
      read only by an XOR that stores back to the same lane, and H is cleared afterwards.
  R4  while `keyed` (until the command ends), capacity lanes 17..24 are never read by the word unit.
      The Keccak work rows are never read or written by the word unit.

  Taint (key-derived data)
  R5  four flags: T_lanes (the lanes hold key-derived data), T_H, T_Z, T_CY. KMOV sets T_lanes; only a
      wipe of all lanes clears it. Reading a lane while T_lanes taints H; H's taint follows it through
      the word unit; CMP taints Z, ADD, SUB and SHL1C taint the carry.
  R6  a tainted H is stored only to a lane or (KEYWR) a key row. Scratch, state and challenge rows, the
      index register and the loop counters therefore never hold key-derived data.
  R7  refused when the value is tainted: PUSH, HDR (length), SETX H, SETC H, FRAM RSTART / WSTART
      (record index), CTL AUTH, CTL VOK, CTL SYNW, CTL TSEL, and every branch on a tainted flag.
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
      pad the response, clear every working row, the PUF response register and the session flags,
      discard unread payload, go to address 0. No instruction can branch to address 0, and DISP decodes
      only there.

  FRAM and lifecycle state
  R11 FRAM instructions decode only at addresses REC_LO..REC_HI. FRAM WWORD sends a state row, or lane
      0 or 1 after a permutation. A transaction is at most 16 words in one direction.
  R12 DISP decodes a command only in the lifecycle states its dispatch entry names. Bad magic and
      unknown opcodes are refused by DISP itself.
  R13 the PUF organ: CTL PUFE, PUFR, SYNW and PMOV decode only in the key range. PMOV moves a word of
      the response register to a rate lane under the rules of KMOV (R2). Nothing else reads it.
  R14 state rows (the loaded lifecycle record, lease, nonce) are written only at addresses
      REC_LO..REC_HI.
  R15 the lifecycle register is written only by CTL LC in the key range; READY only with the verdict
      latch set, and only from RESET or LEASE; nothing leaves LOCKED.
"""
import isa
import units
from framing import Framer
from regfile import RegFile


class ControlFault(Exception):
    """`sent` is what the link had already carried when the fault struck: the response header and the
    words pushed before it. Hardware cannot take them back; the frame is cut short (link.py)."""

    def __init__(self, msg, pc, place):
        super().__init__(f"{msg} at {place} (address {pc})")
        self.msg, self.pc, self.place = msg, pc, place
        self.sent = []


class Machine:
    MAX_STEPS = 1 << 28                 # a 28-bit step counter: a statement of 256 members is about 2^27.4

    def __init__(self, rom, config="S", fram=None, puf=None, trng=None):
        assert config in ("S", "L")
        self.rom, self.config = rom, config
        self.dec = [(isa.decode(w), isa.OPS[w >> 23]) for w in rom.words]
        self.rf = RegFile(isa.ROWS_L if config == "L" else isa.ROWS_S)
        self.cls = [isa.row_class(r, self.rf.nrows) for r in range(128)]
        self.keccak, self.field, self.fram = units.KeccakUnit(), units.FieldUnit(), units.FramUnit(fram)
        self.puf, self.trng = puf, trng
        self.framer = Framer()
        self.trace = None                   # optional callback(pc, word, machine)
        self.power_on()

    # ------------------------------------------------------------ state
    def power_on(self):
        """Reset, power cycle or control fault: everything on the chip is volatile, the lifecycle
        register included. The FRAM is not part of the chip."""
        self.rf.secret_reset()
        self.lc = isa.LC_RESET
        self.fault_mac = self.fault_anchor = self.fault_control = False
        self.verify_ok = False
        self.fram.abort()
        self.framer = Framer()
        if self.puf is not None:
            self.puf.power_on()
        if self.trng is not None:
            self.trng.power_on()
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
        self.last_wipe = self.cur_wipe = 0

    def status_word(self):
        return (int(self.lc == isa.LC_READY) | (int(self.fault_mac) << 1) | (int(self.fault_anchor) << 2)
                | (self.lc << 4) | (int(self.config == "L") << 8) | (self.rom.used << 32))

    # ------------------------------------------------------------ decoder helpers
    def _fault(self, msg):
        raise ControlFault(msg, self.cur_pc, self.rom.place(self.cur_pc))

    def _rd(self, row, same=None):
        """Value and taint of a row as the word unit reads it."""
        cls = self.cls[row]
        if cls in ("none", "key", "out", "kwork"):
            self._fault(f"read of {cls} row {row}")
        tainted = False
        if cls == "lane":
            if self.dirty and row != same:
                self._fault(f"read of lane {row} while a key is in the lanes")
            if self.keyed and row >= isa.RATE_LANES:
                self._fault(f"read of capacity lane {row} in a keyed command")
            tainted = self.t_lanes
        self._stall(row)
        return self.rf[row], tainted

    def _stall(self, row):
        """A row written in the previous clock (by a store, the last lane of a permutation, or a wipe of
        its class) is still transparent: reading it costs one clock."""
        if row == self.last_w or (self.last_wipe and self._wiped(row)):
            self.cycles += 1
            self.stalls += 1

    def _wiped(self, row):
        m = self.last_wipe
        return ((m & isa.W_LANES_LO and row < 8) or (m & isa.W_LANES_HI and 8 <= row < isa.SCRATCH0)
                or (m & isa.W_SCRATCH and isa.SCRATCH0 <= row < isa.KEY0) or (m & isa.W_OUT and row >= isa.OUT0))

    def _wr(self, row, v, tainted):
        cls = self.cls[row]
        if cls in ("none", "key", "out", "kwork"):
            self._fault(f"write of {cls} row {row}")
        if cls in ("pin", "state") and not isa.REC_LO <= self.cur_pc <= isa.REC_HI:
            self._fault("write of a state row outside the record range")
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
        if c >= len(isa.COND):
            self._fault("undefined function code")
        n = isa.COND[c]
        if n in ("Z", "NZ") and self.t_z:
            self._fault("branch on a key-derived compare result")
        if n in ("CY", "NC") and self.t_cy:
            self._fault("branch on a key-derived carry")
        if n in ("HZ", "HNZ") and self.t_h:
            self._fault("branch on key-derived data")
        if n == "AL":
            return True
        if n in ("Z", "NZ"):
            return bool(self.z) == (n == "Z")
        if n in ("CY", "NC"):
            return bool(self.cy) == (n == "CY")
        if n in ("HZ", "HNZ"):
            return (self.h == 0) == (n == "HZ")
        if n in ("MORE", "NOMORE"):
            return (self.framer.remaining > 0) == (n == "MORE")
        if n in ("KV", "NKV"):
            return (self.lc == isa.LC_READY) == (n == "KV")
        return (self.c[1] == 0) == (n == "C1Z")

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
        if self.puf is not None:
            self.puf.clear()
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
        self.unit_cycles = {"keccak": 0, "field": 0, "fram": 0, "puf": 0, "trng": 0}
        self.unit_calls = {"keccak": 0, "field": 0}
        self.key_words_emitted = []
        self.verify_ok = False
        try:
            while self._step():
                if self.steps > self.MAX_STEPS:
                    self._fault("runaway microprogram")
        except ControlFault as e:
            e.sent = list(self.response)
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
        d, mn = self.dec[pc]
        if self.trace:
            self.trace(pc, w, self)
        self.steps += 1
        self.cycles += 1
        self.cur_w = None
        self.cur_wipe = 0
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
            if d["a"] >= len(isa.UN):
                self._fault("undefined function code")
            if isa.UN[d["a"]] == "SHL1C":
                self.cy, self.t_cy = self.h >> 63, self.t_h
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
            if d["a"] >= len(isa.LDF):
                self._fault("undefined function code")
            n = isa.LDF[d["a"]]
            if n in ("HDRW", "FLAGS", "LEN", "NWORDS", "ARG", "ARGLO", "ARGHI", "X", "STATUS", "LC"):
                self.h = {"HDRW": fr.hdr, "FLAGS": fr.flags, "LEN": fr.length, "NWORDS": fr.remaining, "ARG": fr.arg,
                          "ARGLO": fr.arg & 0xFF, "ARGHI": fr.arg >> 8, "X": self.x, "STATUS": self.status_word(),
                          "LC": self.lc}[n]
            elif n in ("SYN0", "SYN1", "PNOISE"):       # public outputs of the PUF organ
                p = self.puf
                self.h = 0 if p is None else p.noise() if n == "PNOISE" else p.syn[int(n[3])]
            else:                                       # statistics and raw word of the TRNG organ
                t = self.trng
                self.h = 0 if t is None else {
                    "TS1": t.s1, "TS4": t.s4, "TSUM": t.total, "TFLAGS": t.flag_word(), "TRAW": t.raw}[n]
            self.t_h = False
            if store:
                self._wr(b, self.h, False)
        elif mn == "LDC":
            if d["a"] >= len(rom.consts):
                self._fault("undefined constant")
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
                clear_h = True                      # the row passes through the hold register
            else:
                if isa.row_class(a, self.rf.nrows) not in ("lane", "scratch", "pin", "state", "chal"):
                    self._fault(f"PUSH of {isa.row_class(a, self.rf.nrows)} row {a}")
                v, tx = self._rd(a)
                if tx:
                    self._fault("PUSH of key-derived data")
                self._emit(v)
                clear_h = True
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
            if d["fn"] & 1:                         # PMOV: a word of the PUF response register (R13)
                if not self._in_key_range():
                    self._fault("PMOV outside the key range")
                if self.puf is None or self.puf.rsp is None or d["ia"] or d["a"] >= units.PUF_BLOCKS:
                    self._fault("PMOV without a PUF response")
                v = self.puf.rsp[d["a"]]
            else:
                if isa.row_class(a, self.rf.nrows) != "key":
                    self._fault("KMOV source is not a key row")
                self._stall(a)
                v = self.rf[a]
            if not 0 <= b < isa.RATE_LANES:
                self._fault("KMOV destination is not a rate lane")
            self.rf[b] = v
            self.cur_w = b
            self.keyed = self.dirty = self.t_lanes = True
            clear_h = True
            self.cycles += 1
        elif mn == "KEYWR":
            if not self._in_key_range():
                self._fault("KEYWR outside the key range")
            if not self.auth_ok:
                self._fault("KEYWR without the verdict latch")
            if isa.row_class(b, self.rf.nrows) != "key":
                self._fault("KEYWR destination is not a key row")
            self.rf[b] = self.h
            self.cur_w = b
            clear_h = True
        elif mn == "CTL":
            if d["a"] >= len(isa.CTL):
                self._fault("undefined function code")
            n = isa.CTL[d["a"]]
            if n == "CLRZ":
                self.z, self.t_z = 0, False
            elif n == "SETFM":
                self.fault_mac = True
            elif n == "SETFA":
                self.fault_anchor = True
            elif n == "VOK":
                if self.t_z:
                    self._fault("verdict pin from a key-derived compare result")
                self.verify_ok = not self.z
            elif n == "ZKEY":
                for r in range(isa.KEY0, isa.KEY0 + isa.N_KEYS):
                    self.rf[r] = 0
            elif n in isa.CTL_KEY and not self._in_key_range():
                self._fault("key-range CTL outside the key range")
            elif n == "AUTH":                       # the verdict latch (R1): from a clear, untainted Z
                if self.t_z:
                    self._fault("verdict latch from a key-derived compare result")
                if not self.z:
                    self.auth_ok = True
            elif n == "LC":                         # the lifecycle register (R15)
                to = d["b"]
                if to >= len(isa.LC) or to == isa.LC_RESET:
                    self._fault("lifecycle state out of range")
                if self.lc == isa.LC_LOCKED:
                    self._fault("lifecycle change out of LOCKED")
                if to == isa.LC_READY and not self.auth_ok:
                    self._fault("READY without the verdict latch")
                if to == isa.LC_READY and self.lc not in (isa.LC_RESET, isa.LC_LEASE):
                    self._fault("READY from a state that cannot boot")
                self.lc = to
            elif n in ("PUFE", "PUFR"):
                if self.puf is None:
                    self.z = 1
                else:
                    k = self.puf.enrol() if n == "PUFE" else self.puf.reconstruct()
                    self.cycles += k
                    self.unit_cycles["puf"] += k
            elif n == "SYNW":
                if self.t_h:
                    self._fault("syndrome from key-derived data")
                if self.puf is not None:
                    self.puf.syn[d["b"] & 1] = self.h
            elif n == "TSEL":
                if self.t_h:
                    self._fault("TRNG pair from key-derived data")
                if self.trng is not None:
                    self.trng.select(self.h & 31)
            elif n == "TRUN":
                if self.trng is not None:
                    k = self.trng.run()
                    self.cycles += k
                    self.unit_cycles["trng"] += k
            elif n == "TCLR":
                if self.trng is not None:
                    self.trng.clear()
            elif n == "TARM":
                if self.trng is not None:
                    self.trng.armed = True
        elif mn == "WIPE":
            self.rf.wipe(d["a"])
            self.cur_wipe = d["a"]
            if d["a"] & 3 == 3:
                self.dirty = self.t_lanes = False
        elif mn == "KEC":
            n = self.keccak.run(self.rf, 12 if d["a"] else 24)
            self.cur_w = isa.LANE0 + 24             # the unit writes lane 24 last
            clear_h = True                          # the hold register is the unit's write path
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
            if d["a"] >= len(isa.FRAM):
                self._fault("undefined function code")
            n = isa.FRAM[d["a"]]
            try:
                if n in ("RSTART", "WSTART"):
                    if self.t_h:
                        self._fault("FRAM record index from key-derived data")
                    k = self.fram.start(self.h & 3, n == "WSTART")
                elif n == "RWORD":
                    self.h, k = self.fram.rword()
                    self.t_h = False
                    if store:
                        self._wr(b, self.h, False)
                elif n == "WWORD":
                    if d["ib"] or not (d["b"] in isa.FRAM_LANES or isa.row_class(d["b"], self.rf.nrows) in ("pin", "state")):
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
            if len(self.stack) >= isa.STACK_DEPTH:
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
                addr, mask = rom.entries[fr.op]
                if addr < isa.ROM_BASE:
                    self._fault("dispatch entry below the ordinary code")
                if not (mask >> self.lc) & 1:       # R12: not in a state this command decodes in
                    code = isa.E_NOKEY if mask == 1 << isa.LC_READY else isa.E_STATE
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
        self.last_w, self.last_wipe = self.cur_w, self.cur_wipe
        return True
