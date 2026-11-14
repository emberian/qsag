#!/usr/bin/env python3
"""Fail if a proof source has no explicit import-all axiom gate."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent
gates = ("AuditMirAxioms.lean", "QsagCustodyWeld.lean")
covered = set()
for gate in gates:
    covered.update(re.findall(r"^import all (\S+)$", (root / gate).read_text(), re.M))
modules = {
    ".".join(p.relative_to(root).with_suffix("").parts)
    for p in (root / "QsagVerified" / "Proofs").rglob("*.lean")
}
missing = sorted(modules - covered)
if missing:
    raise SystemExit("Proof modules missing an axiom gate: " + ", ".join(missing))
print(f"Axiom import coverage: {len(modules)} proof modules; zero missing")

whir = root.parent / "lean-whir"
whir_covered = set(re.findall(r"^import all (\S+)$", (whir / "AuditWhirMirAxioms.lean").read_text(), re.M))
whir_modules = {"QsagWhirVerified"} | {
    ".".join(p.relative_to(whir).with_suffix("").parts)
    for p in (whir / "QsagWhirVerified").rglob("*.lean")
}
missing = sorted(whir_modules - whir_covered)
if missing:
    raise SystemExit("WHIR modules missing an axiom gate: " + ", ".join(missing))
print(f"WHIR import coverage: {len(whir_modules)} modules; zero missing")
