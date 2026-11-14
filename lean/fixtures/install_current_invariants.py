#!/usr/bin/env python3
"""Install untrusted invariant proposals; ElfFixtureVerify supplies the proofs.

Run GenerateCurrentInvs.lean on the designated Linux build host first. This emitter interns equal abstract
states, keeping kernel reduction explicit while avoiding repeated elaboration.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
MARKER = "/-! Fresh source-build certificates; checked in ElfFixtureVerify. -/"

def install(proposals):
    states = {}
    def compress(match):
        ty = match[1].split("PcMap ")[1].split(" :=")[0]
        definitions = []
        def intern(record):
            value = " ".join(record[1].split())
            key = (ty, value)
            if key not in states:
                name = f"currentInvariantState{len(states):04}"
                states[key] = name
                definitions.append(f"def {name} : {ty} :=\n  {value}\n\n")
            return "some " + states[key]
        body = re.sub(r"some \((\{.*?\})\)", intern, match[2], flags=re.S)
        return "".join(definitions) + match[1] + "\n  " + " ".join(body.split()) + "\n\n"
    pattern = r"(def qsag_asm_\w+_currentInv : PcMap \w+ :=)\n(.*?)(?=\n\ndef |\Z)"
    emitted = re.sub(pattern, compress, proposals, flags=re.S)
    slices = (ROOT / "lean/Qsag/ElfFixtureSlices.lean").read_text()
    for prefix, kind, expected in [("currentX86", "x86", 19), ("currentAarch64", "arm", 9)]:
        part = slices.split(f"def {prefix}ExtractedSlices")[1].split("]\n\n")[0]
        names = re.findall(r'name := "([^"]+)"', part)
        if len(names) != expected or any(f"def {name}_currentInv " not in emitted for name in names):
            raise ValueError(f"missing or unexpected {prefix} certificate inventory")
        emitted += f"def {prefix}InvCerts : List InvCert := [\n"
        emitted += ",\n".join(f"  .{kind} {name}_currentInv" for name in names) + "\n]\n\n"
    path = ROOT / "lean/Qsag/ElfInvCerts.lean"
    old = path.read_text()
    if old.count(MARKER) != 1:
        raise ValueError("missing or ambiguous current-certificate boundary")
    path.write_text(old.split(MARKER)[0] + MARKER + "\n" + emitted + "end Qsag\n")
    print(f"Installed 28 proposals using {len(states)} shared states; run the kernel certificate gate.")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: install_current_invariants.py PROPOSALS.inc")
    install(Path(sys.argv[1]).read_text())

