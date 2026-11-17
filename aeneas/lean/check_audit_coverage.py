#!/usr/bin/env python3
"""Fail if any proof module lacks an explicit axiom gate (via `import all` or
`public import` paired with module-census registration and 100% public-theorem anchoring)."""
from pathlib import Path
import re


def strip_lean_comments(source: str) -> str:
    """Remove nested `/- ... -/` block comments and `-- ...` line comments."""
    out = []
    i = depth = 0
    n = len(source)
    while i < n:
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = n if end < 0 else end
        elif source[i] == '"':
            out.append('"')
            i += 1
            while i < n:
                ch = source[i]
                out.append(ch)
                if ch == "\\" and i + 1 < n:
                    out.append(source[i + 1])
                    i += 2
                elif ch == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


PUB_THM_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?!private\b)(?:public[ \t]+)?(?:protected[ \t]+)?"
    r"(?:noncomputable[ \t]+)?(?:theorem|lemma)[ \t]+([A-Za-z_][A-Za-z0-9_'.]*)"
)


def public_theorems_of(path: Path) -> list[str]:
    clean = strip_lean_comments(path.read_text())
    return [m.group(1) for m in PUB_THM_RE.finditer(clean)]


def check_public_import_audited(gate_clean: str, mod: str, mod_path: Path) -> list[str]:
    """Verify a `public import` module is registered in `requiredModules` and every
    non-private theorem in `mod_path` is explicitly audited in `gate_clean`."""
    problems = []
    if f'"{mod}"' not in gate_clean:
        problems.append(f"{mod}: missing from requiredModules census list")
    thms = public_theorems_of(mod_path)
    if not thms:
        problems.append(f"{mod}: has no public theorems; must use `import all`")
    for thm in thms:
        leaf = thm.rsplit(".", 1)[-1]
        has_name_anchor = bool(re.search(rf"``(?:[\w.]+\.)?{re.escape(leaf)}\b", gate_clean))
        has_constructive = bool(
            re.search(rf"#verify_constructive\s+(?:[\w.]+\.)?{re.escape(leaf)}\b", gate_clean)
        )
        if not (has_name_anchor and has_constructive):
            problems.append(
                f"{mod}.{leaf}: missing explicit theorem anchor or #verify_constructive in gate"
            )
    return problems


# Self-test negative controls so theorem-list auditing cannot silently regress.
if check_public_import_audited('public import Foo\n"Foo"\n', "Foo", Path(__file__)) == []:
    raise RuntimeError("check_audit_coverage negative control unexpectedly passed")

root = Path(__file__).resolve().parent
gates = ("AuditMirAxioms.lean", "QsagCustodyWeld.lean")
covered = set()
public_import_candidates: dict[str, list[str]] = {}

for gate in gates:
    gate_clean = strip_lean_comments((root / gate).read_text())
    covered.update(re.findall(r"(?m)^[ \t]*import all (\S+)[ \t]*$", gate_clean))
    for pub_mod in re.findall(r"(?m)^[ \t]*public import (\S+)[ \t]*$", gate_clean):
        public_import_candidates.setdefault(pub_mod, []).append(gate_clean)

modules = {
    ".".join(p.relative_to(root).with_suffix("").parts): p
    for p in (root / "QsagVerified" / "Proofs").rglob("*.lean")
}

audit_errors = []
public_audited = set()
for mod, mod_path in sorted(modules.items()):
    if mod in covered:
        continue
    if mod in public_import_candidates:
        gate_attempt_errors = []
        for gate_clean in public_import_candidates[mod]:
            errs = check_public_import_audited(gate_clean, mod, mod_path)
            if not errs:
                public_audited.add(mod)
                break
            gate_attempt_errors.extend(errs)
        else:
            audit_errors.extend(gate_attempt_errors)

missing = sorted(set(modules) - covered - public_audited)
if missing or audit_errors:
    details = []
    if missing:
        details.append("Proof modules missing an axiom gate: " + ", ".join(missing))
    if audit_errors:
        details.append("Incomplete public-import theorem audit: " + "; ".join(audit_errors))
    raise SystemExit("\n".join(details))

print(
    f"Axiom import coverage: {len(modules)} proof modules "
    f"({len(covered & set(modules))} import-all, {len(public_audited)} explicit theorem-audited); "
    "zero missing"
)

whir = root.parent / "lean-whir"
whir_clean = strip_lean_comments((whir / "AuditWhirMirAxioms.lean").read_text())
whir_covered = set(re.findall(r"(?m)^[ \t]*import all (\S+)[ \t]*$", whir_clean))
whir_modules = {"QsagWhirVerified"} | {
    ".".join(p.relative_to(whir).with_suffix("").parts)
    for p in (whir / "QsagWhirVerified").rglob("*.lean")
}
missing = sorted(whir_modules - whir_covered)
if missing:
    raise SystemExit("WHIR modules missing an axiom gate: " + ", ".join(missing))
print(f"WHIR import coverage: {len(whir_modules)} modules; zero missing")
