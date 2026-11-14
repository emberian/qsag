#!/usr/bin/env python3
"""Fail if a proof source has no explicit import-all axiom gate."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent
gates = ("AuditMirAxioms.lean",)
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
