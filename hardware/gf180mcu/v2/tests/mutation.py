"""Mutation harness: every guard has a test that fails without it.

    python3 -B hardware/gf180mcu/v2/tests/mutation.py [-j N] [-k substring]

Each mutant is one textual change applied to a temporary copy of v2/ (the reference model and tb/ are
linked in read-only); the whole test suite is then run on the copy. A mutant is killed if the suite
fails (or does not finish). The script exits non-zero if any mutant survives that is not in EQUIVALENT.

Mutants:
  generated   every decoder fault in model/machine.py removed, one at a time
              every finding of model/romcheck.py removed, one at a time
              every branch to an error exit in ucode/*.uc removed, one at a time
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
TIMEOUT = 90

# (name, file, old, new). `old` must occur exactly once.
MANUAL = [
    # anchor: read-back and record authentication, word by word
    ("fram_check ignores the counter word", "ucode/fram.uc", "            FRAM RWORD\n            CMP  A0\n", "            FRAM RWORD\n            NOP\n"),
    ("fram_check ignores tag word 0", "ucode/fram.uc", "            CMP  A0\n            FRAM RWORD\n            CMPT l0\n", "            CMP  A0\n            FRAM RWORD\n            NOP\n"),
    ("fram_check ignores tag word 1", "ucode/fram.uc", "            CMPT l1\n            FRAM DONE ret", "            NOP\n            FRAM DONE ret"),
    ("anchor_read ignores tag word 0", "ucode/fram.uc", "            CTL  CLRZ\n            FRAM RWORD\n            CMPT l0\n", "            CTL  CLRZ\n            FRAM RWORD\n            NOP\n"),
    ("anchor_read ignores tag word 1", "ucode/fram.uc", "            CMPT l1\n            FRAM DONE\n            LD   A0", "            NOP\n            FRAM DONE\n            LD   A0"),
    ("anchor_read accepts counters above 32 bits", "ucode/fram.uc", "            CMP  #0                 ; a counter above 32 bits is not a record\n", "            NOP\n"),
    ("anchor: slot 1 taken as valid", "ucode/sign.uc", "            BR   HZ an_use0          ; slot 1 is not a record\n", "            NOP\n"),
    ("anchor: counters not compared", "ucode/sign.uc", "            BR   CY an_use0          ; counter 1 < counter 0\n", "            NOP\n"),
    ("anchor: new record written to the newer slot", "ucode/sign.uc", "            LD   #0\n            ST   A1                  ; slot to write\n", "            LD   #1\n            ST   A1                  ; slot to write\n"),
    ("anchor: counter written is the leaf, not leaf + 1", "ucode/sign.uc", "            UN   LO32\n            ADD  #1\n            BR   CY e_reuse          ; counter would wrap\n", "            UN   LO32\n            ADD  #0\n            BR   CY e_reuse          ; counter would wrap\n"),
    ("anchor: high-water mark not kept", "ucode/sign.uc", "            XOR  A0\n            ST   ST_HWM\n", "            XOR  A0\n            NOP\n"),
    ("provisioning: slot 1 not initialised", "ucode/provision.uc", "            LD   #1\n            CALL fram_write\n", "            LD   #0\n            CALL fram_write\n"),
    ("record tag not under the device secret (word 3)", "ucode/fram.uc", "            KMOV k_dev3 > l3\n", "            NOP\n"),
    ("record tag under the host key", "ucode/fram.uc", "            KMOV k_dev0 > l0\n", "            KMOV k_host0 > l0\n"),
    # signer
    ("request tag ignores word 0", "ucode/sign.uc", "            DIN\n            CMPT l0\n            DIN\n", "            DIN\n            NOP\n            DIN\n"),
    ("request tag ignores word 1", "ucode/sign.uc", "            CMPT l1\n            BR   Z e_mac\n", "            NOP\n            BR   Z e_mac\n"),
    ("request tag does not cover the header", "ucode/sign.uc", "            LDF  HDRW\n            ST   l2\n", "            LD   #0\n            ST   l2\n"),
    ("first-chain field ignored", "ucode/sign.uc", "            LDF  ARGHI\n            BR   HZ w_count\n", "            LD   #0\n            BR   HZ w_count\n"),
    ("counted attribute ignored", "ucode/sign.uc", "            AND  #KA_COUNTED\n            BR   HZ cth_go           ; uncounted key\n", "            AND  #0\n            BR   HZ cth_go           ; uncounted key\n"),
    ("PUBGEN moves the counter", "ucode/sign.uc", "            BR   HNZ cth_go          ; PUBGEN releases public values only\n", "            NOP\n"),
    ("PUBGEN returns the signature value", "ucode/sign.uc", "            SETC 1 #15               ; PUBGEN: the chain end\n", "            NOP\n"),
    ("lanes not wiped between chains", "ucode/sign.uc", "w_start:    WIPE #W_LANES\n", "w_start:    NOP\n"),
    ("capacity not wiped between chain steps", "ucode/sign.uc", "            WIPE #W_HI\n", "            NOP\n"),
    # provisioning
    ("statement does not cover the header", "ucode/provision.uc", "            LDF  HDRW                ; statement digest\n", "            LD   #0\n"),
    ("counted flag not stored with the key", "ucode/provision.uc", "            AND  #KA_COUNTED\n", "            AND  #0\n"),
    ("nonce not consumed by an attempt", "model/machine.py", "                nonce, self.nonce = self.nonce, None\n", "                nonce = self.nonce\n"),
    ("authorisation not bound to the nonce", "model/machine.py", "self.owner(nonce, digest, sig))", "self.owner(nonce and [0, 0], digest, sig))"),
    ("authorisation without a nonce", "model/machine.py", "ok = (nonce is not None and self.owner is not None", "nonce = nonce or [0, 0]\n                ok = (self.owner is not None"),
    ("authorisation latch set on refusal", "model/machine.py", "                if ok:\n                    self.auth_ok = True\n", "                self.auth_ok = True\n                if ok:\n                    pass\n"),
    ("reset keeps the key valid", "model/machine.py", "        self.key_valid = False\n        self.key_attr = 0\n", "        self.key_attr = 0\n"),
    ("reset keeps the key rows", "model/machine.py", "        self.rf.secret_reset()\n        self.key_valid = False\n", "        self.rf.wipe(15)\n        self.key_valid = False\n"),
    # lifecycle gate
    ("dispatch: provisioning allowed while a key is valid", "model/machine.py", "                elif cls == isa.D_PROV and self.key_valid:\n                    code = isa.E_KEYSET\n", ""),
    ("dispatch: provisioning allowed without the device secret", "model/machine.py", "                if cls == isa.D_PROV and not self.dev_ok:\n                    code = isa.E_NOKEY\n                elif cls == isa.D_PROV and self.key_valid:", "                if cls == isa.D_PROV and self.key_valid:"),
    ("dispatch: keyed commands allowed without a key", "model/machine.py", "                elif cls == isa.D_KEYED and not self.key_valid:\n                    code = isa.E_NOKEY\n", ""),
    # end action
    ("end action does not wipe", "model/machine.py", "        self.rf.wipe(isa.W_LANES_LO | isa.W_LANES_HI | isa.W_SCRATCH | isa.W_OUT)\n        self.framer.drain()", "        self.framer.drain()"),
    ("end action wipes lanes only", "model/machine.py", "        self.rf.wipe(isa.W_LANES_LO | isa.W_LANES_HI | isa.W_SCRATCH | isa.W_OUT)\n        self.framer.drain()", "        self.rf.wipe(isa.W_LANES_LO | isa.W_LANES_HI)\n        self.framer.drain()"),
    ("end action does not drain", "model/machine.py", "        self.framer.drain()\n", ""),
    ("end action does not pad", "model/machine.py", "        while self.sent < self.limit:               # a short routine cannot desynchronise the link\n            self.response.append(0)\n            self.sent += 1\n", ""),
    ("runaway guard removed", "model/machine.py", "                if self.steps > self.MAX_STEPS:", "                if False:"),
    # taint propagation (the sinks are generated)
    ("KMOV does not taint the lanes", "model/machine.py", "            self.keyed = self.dirty = self.t_lanes = True", "            self.keyed = self.dirty = True"),
    ("reading a lane does not taint H", "model/machine.py", "            tainted = self.t_lanes\n", "            tainted = False\n"),
    ("word unit drops H's taint", "model/machine.py", "            self.t_h = tx if mn == \"LD\" else (self.t_h or tx)", "            self.t_h = tx"),
    ("CMP does not taint Z", "model/machine.py", "                self.t_z = self.t_z or self.t_h or tx\n", ""),
    ("ADD and SUB do not taint the carry", "model/machine.py", "                self.cy, self.t_cy = cy, self.t_h", "                self.cy = cy"),
    ("FADD drops taint", "model/machine.py", "self.field.add(self.h, x), self.t_h or tx", "self.field.add(self.h, x), self.t_h"),
    ("partial wipe clears taint", "model/machine.py", "            if d[\"a\"] & 3 == 3:\n                self.dirty = self.t_lanes = False", "            if d[\"a\"] & 3:\n                self.dirty = self.t_lanes = False"),
    ("tainted store allowed outside the lanes", "model/machine.py", "            if cls != \"lane\":\n                self._fault(f\"store of key-derived data to {cls} row {row}\")\n", ""),
    ("H not cleared after touching a key lane", "model/machine.py", "        if clear_h:\n            self.h, self.t_h = 0, False\n", ""),
    ("KEC leaves the dirty flag", "model/machine.py", "            self.unit_calls[\"keccak\"] += 1\n            self.dirty = False\n", "            self.unit_calls[\"keccak\"] += 1\n"),
    # FRAM path
    ("FRAM WWORD takes any row", "model/machine.py", "                    if d[\"ib\"] or d[\"b\"] not in isa.FRAM_SRC:\n                        self._fault(f\"FRAM WWORD of row {b}\")\n", ""),
    ("FRAM transaction length not enforced", "model/units.py", "        if self.pos is None or self.writing != write or self.left == 0:", "        if self.pos is None or self.writing != write:"),
    ("FRAM direction not enforced", "model/units.py", "        if self.pos is None or self.writing != write or self.left == 0:", "        if self.pos is None or self.left == 0:"),
    # hardwired layout
    ("key range widened", "model/isa.py", "KEY_LO, KEY_HI = 1, 63 ", "KEY_LO, KEY_HI = 1, 2047 "),
    ("record range widened", "model/isa.py", "REC_LO, REC_HI = 64, 127 ", "REC_LO, REC_HI = 1, 2047 "),
    ("FRAM source set widened", "model/isa.py", "FRAM_SRC = (SCRATCH0 + 9, LANE0, LANE0 + 1)", "FRAM_SRC = (SCRATCH0 + 9, LANE0, LANE0 + 1, LANE0 + 2, SCRATCH0)"),
    # framing
    ("framer accepts a request over pending payload", "model/framing.py", "        if self.remaining:\n            raise LinkError(\"the previous command left payload words undrained: the link is out of step\")\n", ""),
]

# Mutants known to change nothing observable, each with the reason. Keep this short.
EQUIVALENT = {
    "machine.py fault: transfer outside the ROM": "the next fetch faults instead (fell off the end of the ROM)",
}


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
        for m in re.finditer(r"BR   (\w+) (e_\w+)(?=\s)", src):
            line = src.count("\n", 0, m.start()) + 1
            out.append((f"{name}:{line} branch removed: BR {m.group(1)} {m.group(2)}", f"ucode/{name}", m.start(), m.end(), "NOP"))
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
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
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
