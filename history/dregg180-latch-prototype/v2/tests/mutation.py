"""Mutation harness: every guard has a test that fails without it.

    python3 -B hardware/gf180mcu/v2/tests/mutation.py [-j N] [-k substring]

Each mutant is one textual change applied to a temporary copy of v2/ (the reference model and tb/ are
linked in read-only); the whole test suite is then run on the copy, with DREGG_FAST=1 (which skips the one
test of the real SLH-DSA parameter set: it guards no mutated line). A mutant is killed if the suite fails
(or does not finish within 20 minutes; the suite takes about one). The script exits non-zero if any mutant survives that is not in EQUIVALENT.

Mutants:
  generated   every decoder fault in model/machine.py removed, one at a time
              every finding of model/romcheck.py removed, one at a time
              every conditional branch and every compare of the lifecycle, gate, verifier, TRNG, record
              and signer microcode removed, one at a time (FULL); in the other files every branch to an
              error exit
  listed      MANUAL below: guards that are not a fault, a finding or an error branch
"""
import argparse
import concurrent.futures
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
V2 = os.path.normpath(os.path.join(HERE, ".."))
CHIPDIR = os.path.normpath(os.path.join(V2, ".."))
TIMEOUT = 1200            # a mutant that is only slow must not count as killed

# (name, file, old, new). `old` must occur exactly once.
MANUAL = [
    # ---- decoder: taint propagation (the sinks are generated)
    ("KMOV does not taint the lanes", "model/machine.py", "            self.keyed = self.dirty = self.t_lanes = True", "            self.keyed = self.dirty = True"),
    ("reading a lane does not taint H", "model/machine.py", "            tainted = self.t_lanes\n", "            tainted = False\n"),
    ("word unit drops H's taint", "model/machine.py", "            self.t_h = tx if mn == \"LD\" else (self.t_h or tx)", "            self.t_h = tx"),
    ("CMP does not taint Z", "model/machine.py", "                self.t_z = self.t_z or self.t_h or tx\n", ""),
    ("ADD and SUB do not taint the carry", "model/machine.py", "                self.cy, self.t_cy = cy, self.t_h\n", "                self.cy = cy\n"),
    ("SHL1C does not taint the carry", "model/machine.py", "                self.cy, self.t_cy = self.h >> 63, self.t_h", "                self.cy = self.h >> 63"),
    ("FADD drops taint", "model/machine.py", "self.field.add(self.h, x), self.t_h or tx", "self.field.add(self.h, x), self.t_h"),
    ("partial wipe clears taint", "model/machine.py", "            if d[\"a\"] & 3 == 3:\n                self.dirty = self.t_lanes = False", "            if d[\"a\"] & 3:\n                self.dirty = self.t_lanes = False"),
    ("tainted store allowed outside the lanes", "model/machine.py", "            if cls != \"lane\":\n                self._fault(f\"store of key-derived data to {cls} row {row}\")\n", ""),
    ("H not cleared after touching a key lane", "model/machine.py", "        if clear_h:\n            self.h, self.t_h = 0, False\n", ""),
    ("KEC leaves the dirty flag", "model/machine.py", "            self.unit_calls[\"keccak\"] += 1\n            self.dirty = False\n", "            self.unit_calls[\"keccak\"] += 1\n"),
    ("PMOV is not treated as a key", "model/machine.py", "            self.rf[b] = v\n            self.cur_w = b\n            self.keyed = self.dirty = self.t_lanes = True\n            clear_h = True", "            self.rf[b] = v\n            self.cur_w = b\n            self.keyed = self.dirty = self.t_lanes = not d[\"fn\"] & 1\n            clear_h = True"),
    # ---- decoder: verdict latch, lifecycle register, reset, end action
    ("verdict latch set whatever the compare flag", "model/machine.py", "                if not self.z:\n                    self.auth_ok = True", "                self.auth_ok = True"),
    ("verdict latch outlives the command", "model/machine.py", "        self.hdr_done = self.failed = False\n        self.auth_ok = False\n", "        self.hdr_done = self.failed = False\n        self.auth_ok = getattr(self, \"auth_ok\", False)\n"),
    ("reset keeps the lifecycle state", "model/machine.py", "        self.rf.secret_reset()\n        self.lc = isa.LC_RESET\n", "        self.rf.secret_reset()\n        self.lc = getattr(self, \"lc\", isa.LC_RESET)\n"),
    ("reset keeps the key and state rows", "model/machine.py", "        self.rf.secret_reset()\n        self.lc = isa.LC_RESET\n", "        self.rf.wipe(15)\n        self.lc = isa.LC_RESET\n"),
    ("reset keeps the syndrome register", "model/units.py", "    def power_on(self):\n        self.syn, self.rsp = [0, 0], None", "    def power_on(self):\n        self.rsp = None"),
    ("PUF response register survives the command", "model/machine.py", "        if self.puf is not None:\n            self.puf.clear()\n", ""),
    ("end action does not wipe", "model/machine.py", "        self.rf.wipe(isa.W_LANES_LO | isa.W_LANES_HI | isa.W_SCRATCH | isa.W_OUT)\n        self.framer.drain()", "        self.framer.drain()"),
    ("end action wipes lanes only", "model/machine.py", "        self.rf.wipe(isa.W_LANES_LO | isa.W_LANES_HI | isa.W_SCRATCH | isa.W_OUT)\n        self.framer.drain()", "        self.rf.wipe(isa.W_LANES_LO | isa.W_LANES_HI)\n        self.framer.drain()"),
    ("end action does not drain", "model/machine.py", "        self.framer.drain()\n", ""),
    ("end action does not pad", "model/machine.py", "        while self.sent < self.limit:               # a short routine cannot desynchronise the link\n            self.response.append(0)\n            self.sent += 1\n", ""),
    ("runaway guard removed", "model/machine.py", "                if self.steps > self.MAX_STEPS:", "                if False:"),
    ("dispatch ignores the lifecycle state", "model/machine.py", "                if not (mask >> self.lc) & 1:       # R12: not in a state this command decodes in", "                if False:"),
    ("ZKEY leaves a key row", "model/machine.py", "                for r in range(isa.KEY0, isa.KEY0 + isa.N_KEYS):\n                    self.rf[r] = 0", "                for r in range(isa.KEY0, isa.KEY0 + isa.N_KEYS - 1):\n                    self.rf[r] = 0"),
    # ---- hold register and stalls (as the RTL has them)
    ("H survives KEC", "model/machine.py", "            self.cur_w = isa.LANE0 + 24             # the unit writes lane 24 last\n            clear_h = True", "            self.cur_w = isa.LANE0 + 24             # the unit writes lane 24 last"),
    ("H survives REL", "model/machine.py", "                self._emit(v)\n                clear_h = True                      # the row passes through the hold register", "                self._emit(v)"),
    ("H survives PUSH row", "model/machine.py", "                    self._fault(\"PUSH of key-derived data\")\n                self._emit(v)\n                clear_h = True", "                    self._fault(\"PUSH of key-derived data\")\n                self._emit(v)"),
    ("no stall after KEC", "model/machine.py", "            self.cur_w = isa.LANE0 + 24             # the unit writes lane 24 last\n", "            pass\n"),
    ("no stall after WIPE", "model/machine.py", "            self.cur_wipe = d[\"a\"]\n", ""),
    ("no stall on KMOV of a row just written", "model/machine.py", "                self._stall(a)\n                v = self.rf[a]", "                v = self.rf[a]"),
    ("no stall after a store", "model/machine.py", "        if row == self.last_w or (self.last_wipe and self._wiped(row)):", "        if self.last_wipe and self._wiped(row):"),
    ("fault forgets what was sent", "model/machine.py", "            e.sent = list(self.response)\n", ""),
    # ---- FRAM path and hardwired layout
    ("FRAM WWORD takes any row", "model/machine.py", "                    if d[\"ib\"] or not (d[\"b\"] in isa.FRAM_LANES or isa.row_class(d[\"b\"], self.rf.nrows) in (\"pin\", \"state\")):\n                        self._fault(f\"FRAM WWORD of row {b}\")\n", ""),
    ("FRAM transaction length not enforced", "model/units.py", "        if self.pos is None or self.writing != write or self.left == 0:", "        if self.pos is None or self.writing != write:"),
    ("FRAM direction not enforced", "model/units.py", "        if self.pos is None or self.writing != write or self.left == 0:", "        if self.pos is None or self.left == 0:"),
    ("key range widened", "model/isa.py", "KEY_LO, KEY_HI = 1, 79 ", "KEY_LO, KEY_HI = 1, 2047 "),
    ("record range widened", "model/isa.py", "REC_LO, REC_HI = 80, 287 ", "REC_LO, REC_HI = 1, 2047 "),
    ("FRAM lane set widened", "model/isa.py", "FRAM_LANES = (LANE0, LANE0 + 1)", "FRAM_LANES = (LANE0, LANE0 + 1, LANE0 + 2)"),
    ("return stack deeper", "model/isa.py", "STACK_DEPTH = 4 ", "STACK_DEPTH = 5 "),
    ("framer accepts a request over pending payload", "model/framing.py", "        if self.remaining:\n            raise LinkError(\"the previous command left payload words undrained: the link is out of step\")\n", ""),
    # ---- PUF organ model
    ("decoder corrects nothing", "model/units.py", "            out.append(w ^ (e or 0))", "            out.append(w)"),
    ("syndromes not taken from the register", "model/units.py", "        for w, h in zip(self._measure(), s):\n            e = bch_error(bch_syndrome(w) ^ h)", "        for w, h in zip(self._measure(), s):\n            e = bch_error(bch_syndrome(w) ^ bch_syndrome(self.ideal[len(out)]))"),
    # ---- signer
    ("request tag does not cover the header", "ucode/sign.uc", "            LDF  HDRW\n            ST   l2\n", "            LD   #0\n            ST   l2\n"),
    ("request tag under SK.prf", "ucode/sign.uc", "            LDC  C_LHOST             ; request tag under K_host\n", "            LDC  C_LPRF\n"),
    ("first-chain field ignored", "ucode/sign.uc", "            LDF  ARGHI\n            BR   HZ w_count\n", "            LD   #0\n            BR   HZ w_count\n"),
    ("PUBGEN returns the signature value", "ucode/sign.uc", "            SETC 1 #15               ; PUBGEN: the chain end\n", "            NOP\n"),
    ("capacity not wiped between chain steps", "ucode/hash.uc", "f_step:     LD   l0 > l6\n            LD   l1 > l7\n            WIPE #W_HI\n", "f_step:     LD   l0 > l6\n            LD   l1 > l7\n            NOP\n"),
    ("counter written is the leaf, not leaf + 1", "ucode/sign.uc", "            UN   LO32\n            ADD  #1\n            BR   CY e_reuse          ; counter would wrap\n", "            UN   LO32\n            ADD  #0\n            BR   CY e_reuse          ; counter would wrap\n"),
    ("counter advanced but not stored", "ucode/sign.uc", "            CALL u_set               ; the record with u = leaf + 1, written and read back\n", "            NOP\n"),
    ("counted flag read from another bit", "ucode/sign.uc", "            AND  #F_COUNTED\n", "            AND  #F_MINTLOCK\n"),
    ("lease bound applies to unleased chips only", "ucode/sign.uc", "            AND  #F_LEASED\n            BR   HZ cth_adv\n", "            AND  #F_LEASED\n            BR   HNZ cth_adv\n"),
    ("derived keys share a label", "ucode/defs.uc", ".const C_LSEED  \"DREGGSKS\"", ".const C_LSEED  \"DREGGKHO\""),
    ("key derivation without K_dev word 3", "ucode/hash.uc", "            KMOV k_dev3 > l3\n            KEC  12 ret\n\n; SHAKE256", "            NOP\n            KEC  12 ret\n\n; SHAKE256"),
    # ---- records
    ("record tag without K_dev word 3", "ucode/rec.uc", "            KMOV k_dev3 > l3\n", "            NOP\n"),
    ("record tag has no label", "ucode/rec.uc", "rec_mac:    LDC  C_LREC\n", "rec_mac:    LD   #0\n"),
    ("record written to the other slot", "ucode/rec.uc", "            LD   REC0\n            AND  #1\n            ADD  #1\n            ST   A0\n            FRAM WSTART", "            LD   REC0\n            AND  #1\n            XOR  #1\n            ADD  #1\n            ST   A0\n            FRAM WSTART"),
    ("sequence number not advanced", "ucode/rec.uc", "            LD   REC0\n            ADD  #1\n            OR   A0 > REC0\n", "            LD   REC0\n            ADD  #0\n            OR   A0 > REC0\n"),
    ("older record replaces the newer on load", "ucode/rec.uc", "            BR   NC rl_ret           ; the loaded sequence number is not smaller\n", "            BR   CY rl_ret\n"),
    ("helper record written without its nonce", "ucode/rec.uc", "            FRAM WWORD st7\n            FRAM WWORD st8\n            FRAM DONE\n", "            FRAM WWORD st7\n            FRAM WWORD st7\n            FRAM DONE\n"),
    ("first record keeps no use counter", "ucode/rec.uc", "            LD   ARG2\n            UN   LO32 > REC1\n", "            LD   #0\n            ST   REC1\n"),
    ("lease does not move the counter", "ucode/rec.uc", "            LD   ARG0\n            UN   LO32 > A1\n            BR   u_set", "            LD   REC1\n            UN   LO32 > A1\n            BR   u_set"),
    ("lease bound not stored", "ucode/rec.uc", "            UN   LO32 > LEASE\n", "            UN   LO32\n"),
    ("rotation keeps the old root", "ucode/rec.uc", "t_rotate:   LD   ARG0\n            ST   ROOT0\n", "t_rotate:   LD   ARG0\n            NOP\n"),
    ("rotation keeps the generation", "ucode/rec.uc", "            AND  #0xFFFF\n            ADD  #1\n            AND  #0xFFFF\n            ST   A0                  ; generation + 1", "            AND  #0xFFFF\n            ADD  #0\n            AND  #0xFFFF\n            ST   A0                  ; generation + 1"),
    ("rotation keeps the old threshold", "ucode/rec.uc", "            LD   ARG2\n            AND  #0xFF\n            UN   SHL8\n            UN   SHL8\n            UN   SHL8\n            OR   A0\n", "            LD   REC0\n            UN   HSWAP\n            UN   SHR16\n            UN   SHR8\n            UN   SHL8\n            UN   SHL8\n            UN   SHL8\n            OR   A0\n"),
    # ---- PUF and boot
    ("check tag has no label", "ucode/key.uc", "puf_tag:    WIPE #W_LANES\n            LDC  C_LPCK\n", "puf_tag:    WIPE #W_LANES\n            LD   #0\n"),
    ("check tag omits response word 3", "ucode/key.uc", "            PMOV #3 > l3\n            KEC  12 ret", "            NOP\n            KEC  12 ret"),
    ("K_dev omits the enrolment nonce", "ucode/key.uc", "            LD   NONCE0\n            ST   l5\n", "            LD   #0\n            ST   l5\n"),
    ("K_dev equals the check tag preimage domain", "ucode/key.uc", "            LD   #D_KDEV\n", "            LD   #D_PUFCHK\n"),
    ("K_dev written without the tag check latch", "ucode/key.uc", "            BR   Z pk_ret\n            CTL  AUTH\n            WIPE #W_LANES\n            LDC  C_LKDV", "            NOP\n            CTL  CLRZ\n            CTL  AUTH\n            WIPE #W_LANES\n            LDC  C_LKDV"),
    ("syndromes of the helper record not loaded", "ucode/life.uc", "boot:       CALL hlp_read\n            CALL syn_load\n", "boot:       CALL hlp_read\n            NOP\n"),
    ("retired chip keeps its key", "ucode/life.uc", "bt_retired: CTL  ZKEY\n", "bt_retired: NOP\n"),
    ("retiring leaves the key in place", "ucode/life.uc", "            CTL  ZKEY                ; a retired chip holds no key\n", "            NOP\n"),
    ("retiring leaves the chip running", "ucode/life.uc", "            CTL  ZKEY                ; a retired chip holds no key\n            CALL lc_locked\n", "            CTL  ZKEY                ; a retired chip holds no key\n            NOP\n"),
    ("failed boot does not lock", "ucode/life.uc", "bt_noauth:  CTL  SETFM\n            CALL lc_locked\n", "bt_noauth:  CTL  SETFM\n            NOP\n"),
    ("failed reconstruction does not lock", "ucode/life.uc", "bt_nopuf:   CTL  SETFA\n            CALL lc_locked\n", "bt_nopuf:   CTL  SETFA\n            NOP\n"),
    ("commit leaves the session open", "ucode/life.uc", "cm_done:    CALL nonce_clr\n            CALL lc_locked           ; provisioned: the next power session boots\n", "cm_done:    CALL nonce_clr\n            NOP\n"),
    ("reinit leaves the session open", "ucode/life.uc", "            CALL nonce_clr\n            CALL lc_locked\n            LD   #0\n            HDR  #0\n", "            CALL nonce_clr\n            NOP\n            LD   #0\n            HDR  #0\n"),
    ("commit failure keeps the key", "ucode/life.uc", "cm_io:      CTL  ZKEY\n", "cm_io:      NOP\n"),
    ("failed attempt keeps the nonce (commit, reinit)", "ucode/life.uc", "cm_fail:    CALL nonce_clr           ; a nonce is good for one attempt\n", "cm_fail:    NOP\n"),
    ("failed attempt keeps the nonce (lease)", "ucode/life.uc", "ls_fail:    CALL nonce_clr           ; a nonce is good for one attempt\n", "ls_fail:    NOP\n"),
    ("accepted lease keeps the nonce", "ucode/life.uc", "            BR   Z ls_io\n            CALL nonce_clr\n", "            BR   Z ls_io\n            NOP\n"),
    ("boot keeps the enrolment nonce as session nonce", "ucode/life.uc", "            CALL nonce_clr           ; the enrolment nonce has done its work\n", "            NOP\n"),
    ("K_host released in vat mode", "ucode/life.uc", "            BR   HNZ cm_done         ; vat mode has no K_host\n", "            NOP\n"),
    ("coprocessor check removed", "ucode/sign.uc", "            BR   HNZ e_class\n            RET\n", "            RET\n"),
    # ---- statements: every field is bound
    ("owner statement: label shared by COMMIT and REINIT", "ucode/life.uc", "so_ri:      LDC  C_LRI\n", "so_ri:      LDC  C_LCM\n"),
    ("owner statement omits nonce word 0", "ucode/life.uc", "so_go:      ST   l0\n            LD   NONCE0 > l1\n", "so_go:      ST   l0\n            NOP\n"),
    ("owner statement omits nonce word 1", "ucode/life.uc", "            LD   NONCE1 > l2\n            LDF  SYN0\n", "            NOP\n            LDF  SYN0\n"),
    ("owner statement omits syndrome word 0", "ucode/life.uc", "            LDF  SYN0\n            ST   l3\n", "            LDF  SYN0\n            NOP\n"),
    ("owner statement omits syndrome word 1", "ucode/life.uc", "            LDF  SYN1\n            ST   l4\n            LD   TAG0 > l5", "            LDF  SYN1\n            NOP\n            LD   TAG0 > l5"),
    ("owner statement omits tag word 0", "ucode/life.uc", "            LD   TAG0 > l5\n", "            NOP\n"),
    ("owner statement omits tag word 1", "ucode/life.uc", "            LD   TAG1 > l6\n", "            NOP\n"),
    ("owner statement omits the commit word", "ucode/life.uc", "            LD   ARG2 > l7\n", "            NOP\n"),
    ("owner statement omits root word 0", "ucode/life.uc", "            LD   ARG0 > l8\n            LD   ARG1 > l9\n            LD   #D_STMT\n            ST   l10", "            NOP\n            LD   ARG1 > l9\n            LD   #D_STMT\n            ST   l10"),
    ("owner statement omits root word 1", "ucode/life.uc", "            LD   ARG0 > l8\n            LD   ARG1 > l9\n            LD   #D_STMT\n            ST   l10", "            LD   ARG0 > l8\n            NOP\n            LD   #D_STMT\n            ST   l10"),
    ("transition message omits chip tag word 0", "ucode/life.uc", "            LD   TAG0 > l1\n            LD   TAG1 > l2\n            LD   REC0 > l3\n", "            NOP\n            LD   TAG1 > l2\n            LD   REC0 > l3\n"),
    ("transition message omits chip tag word 1", "ucode/life.uc", "            LD   TAG0 > l1\n            LD   TAG1 > l2\n", "            LD   TAG0 > l1\n            NOP\n"),
    ("transition message omits the record word", "ucode/life.uc", "            LD   TAG1 > l2\n            LD   REC0 > l3\n", "            LD   TAG1 > l2\n            NOP\n"),
    ("transition message omits the type", "ucode/life.uc", "            LDF  ARGLO\n            ST   l4\n            LD   NONCE0 > l5", "            LD   #0\n            ST   l4\n            LD   NONCE0 > l5"),
    ("transition message omits nonce word 0", "ucode/life.uc", "            LD   NONCE0 > l5\n            LD   NONCE1 > l6\n", "            NOP\n            LD   NONCE1 > l6\n"),
    ("transition message omits nonce word 1", "ucode/life.uc", "            LD   NONCE0 > l5\n            LD   NONCE1 > l6\n", "            LD   NONCE0 > l5\n            NOP\n"),
    ("transition message omits argument 0", "ucode/life.uc", "            LD   ARG0 > l7\n            LD   ARG1 > l8\n            LD   ARG2 > l9\n", "            NOP\n            LD   ARG1 > l8\n            LD   ARG2 > l9\n"),
    ("transition message omits argument 1", "ucode/life.uc", "            LD   ARG0 > l7\n            LD   ARG1 > l8\n            LD   ARG2 > l9\n", "            LD   ARG0 > l7\n            NOP\n            LD   ARG2 > l9\n"),
    ("transition message omits argument 2", "ucode/life.uc", "            LD   ARG0 > l7\n            LD   ARG1 > l8\n            LD   ARG2 > l9\n", "            LD   ARG0 > l7\n            LD   ARG1 > l8\n            NOP\n"),
    ("transition and owner statements share a domain", "ucode/life.uc", "            LD   ARG2 > l9\n            LD   #D_STMT\n            ST   l10", "            LD   ARG2 > l9\n            LD   #D_KDF\n            ST   l10"),
    # ---- committee
    ("leaf omits the member index", "ucode/life.uc", "mroot:      WIPE #W_LANES\n            LD   ARG3\n            UN   LO32 > l0\n", "mroot:      WIPE #W_LANES\n            LD   #0\n            UN   LO32 > l0\n"),
    ("leaf omits PK.seed word 1", "ucode/life.uc", "            LD   PK1 > l2\n            LD   NODE0 > l3\n", "            NOP\n            LD   NODE0 > l3\n"),
    ("leaf omits PK.root word 1", "ucode/life.uc", "            LD   NODE1 > l4\n            LD   #D_LEAF\n", "            NOP\n            LD   #D_LEAF\n"),
    ("leaf and node share a domain", "ucode/life.uc", "mr_go:      LD   #D_NODE\n", "mr_go:      LD   #D_LEAF\n"),
    ("path side not taken from the index", "ucode/life.uc", "            AND  #1\n            BR   HNZ mr_right\n", "            AND  #0\n            BR   HNZ mr_right\n"),
    ("next index not raised past this member", "ucode/life.uc", "            LD   ARG3\n            UN   LO32\n            ADD  #1\n            BR   CY g_bad\n", "            LD   ARG3\n            UN   LO32\n            ADD  #0\n            BR   CY g_bad\n"),
    ("one member fewer than the threshold", "ucode/life.uc", "            UN   LO32\n            SUB  #1\n            UN   HSWAP > A1\n            LD   ARG3", "            UN   LO32\n            SUB  #2\n            UN   HSWAP > A1\n            LD   ARG3"),
    ("root after the signature not recomputed", "ucode/life.uc", "            CALL sv\n            CALL mroot               ; and the root its signature leads to is that member's\n", "            CALL sv\n            NOP\n"),
    ("owner root after the signature not recomputed", "ucode/life.uc", "            CALL stmt_own\n            CALL sv\n            CALL mroot\n", "            CALL stmt_own\n            CALL sv\n            NOP\n"),
    # ---- signature verification
    ("H_msg omits R", "ucode/slh.uc", "            DIN  > l0\n            DIN  > l1\n            LD   PK0 > l2", "            DIN\n            DIN  > l1\n            LD   PK0 > l2"),
    ("H_msg omits PK.root", "ucode/slh.uc", "            LD   NODE0 > l4\n            LD   NODE1 > l5\n            LD   #0x1F\n            ST   l10", "            LD   NODE0 > l4\n            NOP\n            LD   #0x1F\n            ST   l10"),
    ("H_msg omits the message", "ucode/slh.uc", "            LD   l2 > l8             ; H_msg", "            LD   #0\n            ST   l8"),
    ("hash chain does not chain", "ucode/slh.uc", "            LD   FD0 > l0\n            LD   FD1 > l1\n            LD   #D_CH\n            CALL dom_kec\n            LD   l0 > FD0", "            LD   #0\n            ST   l0\n            ST   l1\n            LD   #D_CH\n            CALL dom_kec\n            LD   l0 > FD0"),
    ("points do not depend on the computed values", "ucode/slh.uc", "            WIPE #W_LANES\n            LD   FD0 > l0\n            LD   FD1 > l1\n            LD   #D_PT", "            WIPE #W_LANES\n            LD   #1\n            ST   l0\n            LD   #D_PT"),
    ("one point used for both accumulators", "ucode/slh.uc", "            LD   l0 > FR0\n            LD   l1 > FR1\n", "            LD   l0 > FR0\n            LD   l0 > FR1\n"),
    ("pass 2a does not fold word 1", "ucode/slh.uc", "            DIN  > l3\n            CALL fold_w\n            LD   #D_CH", "            DIN  > l3\n            NOP\n            LD   #D_CH"),
    ("pass 2b does not fold word 1", "ucode/slh.uc", "st_b1:      DIN\n            CALL fold_w\n", "st_b1:      DIN\n            ST   A0\n"),
    ("accumulators not reset between the passes", "ucode/slh.uc", "            LD   FA1 > FD1\n            LD   #0\n            ST   FA0\n            ST   FA1\n", "            LD   FA1 > FD1\n            LD   #0\n            NOP\n            NOP\n"),
    ("fold is an XOR, not a product", "ucode/slh.uc", "fw_0n:      DBNZ 1 fw_0\n            LD   TMP > FA0\n", "fw_0n:      DBNZ 1 fw_0\n            LD   FA0 > FA0\n"),
    ("second accumulator is an XOR", "ucode/slh.uc", "fw_1n:      DBNZ 1 fw_1\n            LD   TMP > FA1 ret", "fw_1n:      DBNZ 1 fw_1\n            LD   FA1 > FA1 ret"),
    ("T absorbs under another address type", "ucode/slh.uc", "            LD   #1                  ; WOTS_PK\n", "            LD   #2\n"),
    ("chain ends hashed without the chain index", "ucode/hash.uc", "            LDF  X\n            XOR  l5\n            UN   BE32 > l5\n            LD   TMP\n            ADD  #1", "            LD   #0\n            XOR  l5\n            UN   BE32 > l5\n            LD   TMP\n            ADD  #1"),
    ("tree index not masked", "ucode/slh.uc", "            LDC  C_TREEM\n            AND  TREE > TREE\n", "            LDC  C_TREEM\n            OR   TREE\n"),
    ("leaf index not masked", "ucode/slh.uc", "            UN   SHR16\n            AND  #SLH_LEAFM\n            UN   BE32\n            UN   HSWAP > KP\n            LD   #0", "            UN   SHR16\n            AND  #0xFFFF\n            UN   BE32\n            UN   HSWAP > KP\n            LD   #0"),
    ("path side not taken from the leaf index", "ucode/slh.uc", "path_level: WIPE #W_HI\n            LD   A0\n            AND  #1\n", "path_level: WIPE #W_HI\n            LD   A0\n            AND  #0\n"),
    ("next layer keeps the layer address", "ucode/slh.uc", "            LD   A1\n            UN   BE32 > S0\n", "            LD   A1\n            UN   BE32\n"),
    ("next layer keeps the tree index", "ucode/slh.uc", "sv_tsh:     UN   SHR1\n", "sv_tsh:     UN   ID\n"),
    # ---- TRNG microcode: thresholds and selection
    ("selection threshold halved", "ucode/defs.uc", ".equ T_VSEL     1020 ", ".equ T_VSEL     100 "),
    ("health threshold removed", "ucode/defs.uc", ".equ T_VMIN     638 ", ".equ T_VMIN     0 "),
    ("flag mask ignores the time-out", "ucode/defs.uc", ".equ TF_BAD     0x0F ", ".equ TF_BAD     0x0E "),
    ("flag mask ignores short beats", "ucode/defs.uc", ".equ TF_BAD     0x0F ", ".equ TF_BAD     0x0D "),
    ("mean window has no lower end", "ucode/defs.uc", ".equ T_MEANLO   400", ".equ T_MEANLO   0"),
    ("mean window has no upper end", "ucode/defs.uc", ".equ T_MEANHI   3601", ".equ T_MEANHI   65535"),
    ("only half the pairs are tried", "ucode/defs.uc", ".equ T_PAIRS    28", ".equ T_PAIRS    14"),
    ("nonce without the second source", "ucode/trng.uc", "            LDF  PNOISE\n            ST   l8\n", "            LD   #0\n            ST   l8\n"),
    ("nonce from one raw word", "ucode/trng.uc", "            LDF  TRAW\n            XOR  l0+X > l0+X x+\n", "            LDF  TRAW\n            XOR  l0 > l0\n"),
    ("one bad block is enough to pass H1", "ucode/trng.uc", "            LD   MW3\n            XOR  #2\n            BR   HZ tg_bad\n", "            LD   MW3\n            XOR  #3\n            BR   HZ tg_bad\n"),
    ("start-up test is one block", "ucode/trng.uc", "            CTL  TSEL\n            SETC 0 #4\nts_test:", "            CTL  TSEL\n            SETC 0 #1\nts_test:"),
    ("source armed without the start-up test", "ucode/trng.uc", "            DBNZ 0 ts_test\n            CTL  TARM\n", "            DBNZ 0 ts_test\n            NOP\n"),
    ("selection keeps the first qualifying pair", "ucode/trng.uc", "            BR   NC ts_next          ; not shorter than the best so far\n", "            BR   ts_next\n"),
    ("TRNG organ: statistics not cleared", "model/units.py", "    def clear(self):\n        self.s1 = self.s4 = self.total = 0\n        self.flags = 0\n", "    def clear(self):\n        self.s1 = self.s4 = self.total = 0\n"),
    ("TRNG organ: selecting a pair keeps it armed", "model/units.py", "        self.pair = pair % len(TRNG_PAIRS)\n        self.armed = False\n", "        self.pair = pair % len(TRNG_PAIRS)\n"),
    ("TRNG organ: reset keeps it armed", "model/units.py", "    def power_on(self):\n        self.pair, self.armed = 0, False\n", "    def power_on(self):\n        self.pair, self.armed = 0, getattr(self, \"armed\", False)\n"),
]

# Mutants known to change nothing observable, each with the reason. Keep this short.
EQUIVALENT = {
    "machine.py fault: transfer outside the ROM": "the next fetch faults instead (fell off the end of the ROM)",
}

# Microcode files whose every conditional branch and every compare is removed in turn; in the others
# (ping, keccak, field: unchanged since stage 1) only the branches to error exits are.
FULL = ("key.uc", "rec.uc", "hash.uc", "trng.uc", "slh.uc", "life.uc", "sign.uc")


def generated():
    out = []
    src = open(os.path.join(V2, "model", "machine.py")).read()
    for m in re.finditer(r"self\._fault\((f?\"[^\"]*\")\)", src):
        msg = re.sub(r"\{[^}]*\}", "..", m.group(1).lstrip("f").strip('"'))
        out.append((f"machine.py fault: {msg}", "model/machine.py", m.start(), m.end(), "pass"))
    src = open(os.path.join(V2, "model", "romcheck.py")).read()
    for m in re.finditer(r"f\.append\((f?\"[^\"]*\")\)", src):
        msg = re.sub(r"\{[^}]*\}", "..", m.group(1).lstrip("f").strip('"'))
        out.append((f"romcheck.py finding: {msg}", "model/romcheck.py", m.start(), m.end(), "pass"))
    for name in sorted(os.listdir(os.path.join(V2, "ucode"))):
        if not name.endswith(".uc"):
            continue
        src = open(os.path.join(V2, "ucode", name)).read()
        pat = r"BR   (\w+) (\w+)(?=\s)" if name in FULL else r"BR   (\w+) (e_\w+)(?=\s)"
        for m in re.finditer(pat, src):
            line = src.count("\n", 0, m.start()) + 1
            out.append((f"{name}:{line} branch removed: BR {m.group(1)} {m.group(2)}", f"ucode/{name}", m.start(), m.end(), "NOP"))
        if name in FULL:
            # A tag compare (CMPT) is mutated word by word: the tests can forge half a tag. A compare of a
            # public 128-bit hash is two CMP instructions two lines apart; they are removed together,
            # because no test can make the halves disagree without a 64-bit partial collision.
            hits = [(src.count("\n", 0, m.start()) + 1, m) for m in re.finditer(r"(CMPT|CMP ) (\S+)(?=\s)", src)]
            used = set()
            for i, (line, m) in enumerate(hits):
                if i in used:
                    continue
                kind = m.group(1).strip()
                if kind == "CMP" and i + 1 < len(hits) and hits[i + 1][0] == line + 2 and hits[i + 1][1].group(1).strip() == "CMP":
                    m2 = hits[i + 1][1]
                    used.add(i + 1)
                    out.append((f"{name}:{line} comparison removed: CMP {m.group(2)}, CMP {m2.group(2)}", f"ucode/{name}",
                                m.start(), m2.end(), "NOP" + src[m.end():m2.start()] + "NOP"))
                else:
                    out.append((f"{name}:{line} compare removed: {kind} {m.group(2)}", f"ucode/{name}", m.start(), m.end(), "NOP"))
    return out


def all_mutants():
    muts = []
    for name, path, a, b, new in generated():
        muts.append((name, path, ("span", a, b), new))
    for name, path, old, new in MANUAL:
        muts.append((name, path, ("text", old), new))
    return muts


def run_one(mut):
    name, path, where, new = mut
    tmp = tempfile.mkdtemp(prefix="dregg180-mut-")
    try:
        root = os.path.join(tmp, "gf180mcu")
        os.mkdir(root)
        shutil.copytree(V2, os.path.join(root, "v2"), ignore=shutil.ignore_patterns("__pycache__"))
        for d in ("model", "tb"):
            os.symlink(os.path.join(CHIPDIR, d), os.path.join(root, d))
        target = os.path.join(root, "v2", path)
        src = open(target).read()
        if where[0] == "span":
            src = src[:where[1]] + new + src[where[2]:]
        else:
            if src.count(where[1]) != 1:
                return name, "BROKEN", f"pattern occurs {src.count(where[1])} times"
            src = src.replace(where[1], new)
        with open(target, "w") as fh:
            fh.write(src)
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", DREGG_FAST="1")
        try:
            p = subprocess.run([sys.executable, "-B", "-m", "unittest", "discover", "-f", "-s", os.path.join(root, "v2", "tests")],
                               capture_output=True, text=True, timeout=TIMEOUT, env=env, cwd=root)
        except subprocess.TimeoutExpired:
            return name, "killed", "suite did not finish"
        if p.returncode == 0:
            return name, "SURVIVED", ""
        first = re.search(r"^(FAIL|ERROR): (\S+) \((\S+)\)", p.stderr, re.M)
        return name, "killed", f"{first.group(3)}" if first else p.stderr.strip().splitlines()[-1][:80]
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-j", type=int, default=max(1, min(8, (os.cpu_count() or 2) // 2)))
    ap.add_argument("-k", default="")
    args = ap.parse_args()
    base = subprocess.run([sys.executable, "-B", "-m", "unittest", "discover", "-s", HERE], capture_output=True, text=True,
                          env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    if base.returncode != 0:
        print("the unmutated suite fails; nothing to measure")
        return 2
    muts = [m for m in all_mutants() if args.k in m[0]]
    with concurrent.futures.ThreadPoolExecutor(args.j) as ex:
        results = list(ex.map(run_one, muts))
    killed = [r for r in results if r[1] == "killed"]
    survived = [r for r in results if r[1] == "SURVIVED"]
    broken = [r for r in results if r[1] == "BROKEN"]
    for name, status, note in results:
        tag = "equivalent" if status == "SURVIVED" and name in EQUIVALENT else status
        print(f"{tag:10s} {name}" + (f"   [{note}]" if note else "") + (f"   [{EQUIVALENT[name]}]" if tag == "equivalent" else ""))
    unexpected = [r for r in survived if r[0] not in EQUIVALENT]
    stale = [n for n in EQUIVALENT if not args.k and n not in {r[0] for r in survived}]
    print(f"\n{len(results)} mutants: {len(killed)} killed, {len(survived) - len(unexpected)} equivalent (listed), "
          f"{len(unexpected)} surviving, {len(broken)} broken patterns, {len(stale)} stale equivalence entries")
    for n in stale:
        print("stale equivalence entry (the mutant is now killed or gone):", n)
    return 1 if unexpected or broken or stale else 0


if __name__ == "__main__":
    sys.exit(main())
