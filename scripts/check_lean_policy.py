#!/usr/bin/env python3
"""Check source policy; compiled dependency audits remain authoritative."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[1]
def code(source):
    """Remove comments and literals, preserving line numbers for diagnostics."""
    out = []
    i = depth = 0
    while i < len(source):
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
            i = len(source) if end < 0 else end
        elif source[i] == "'" and (char := re.match(r"'(?:\\.|[^'\\\n])'", source[i:])):
            out.append(" ")
            i += len(char[0])
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    if source[i] == "\n":
                        out.append("\n")
                    i += 1
            out.append(" ")
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


files = sorted(
    p for base in ("lean", "aeneas/lean", "aeneas/lean-whir")
    for p in (root / base).rglob("*.lean")
    if ".lake" not in p.parts
)
errors = []
challenge_paths = {"lean/QsagChallenge.lean", "aeneas/lean/QsagVerifiedChallenge.lean"}
for path in files:
    raw = path.read_text()
    source = code(raw)
    relative = str(path.relative_to(root))
    exposed = sum(bool(re.search(r"\bexpose\b", attrs))
                  for attrs in re.findall(r"@\[([^]]*)\]", source))
    if len(raw.splitlines()) > 80:
        for section in re.finditer(r"@\[[^]]*\bexpose\b[^]]*\]\s*public\s+section\b", source):
            line = source[:section.start()].count("\n") + 1
            errors.append(f"{relative}:{line}: file-wide expose section in module over 80 lines")
    if exposed > 12:
        errors.append(f"{relative}: {exposed} expose annotations")
    if relative.startswith("lean/Qsag/"):
        for escape in re.finditer(r"@\[[^]]*\b(?:implemented_by|extern)\b", source):
            errors.append(f"{relative}: executable substitution: {escape[0]}")
    for match in re.finditer(r"\baxiom\b|\bsorry\b|\bnative_decide\b|\bbv_decide\b|\bClassical\.choice\b", source):
        if match[0] == "sorry" and relative in challenge_paths:
            continue
        # Quoted declaration names in rejection checks do not invoke the axiom.
        if match[0] == "Classical.choice" and source[max(0, match.start() - 2):match.start()] == "``":
            continue
        line = source[:match.start()].count("\n") + 1
        errors.append(f"{relative}:{line}: {match[0]}")
for manifest, import_pattern in (
    ("lean/Qsag.lean", r"(?:public )?import (Qsag\.[\w.]+)"),
    ("lean/AuditAxioms.lean", r"import all (Qsag\.[\w.]+)"),
):
    imported = set(re.findall(import_pattern, code((root / manifest).read_text())))
    required = {"Qsag." + ".".join(p.relative_to(root / "lean/Qsag").with_suffix("").parts)
                for p in (root / "lean/Qsag").rglob("*.lean")}
    for missing in sorted(required - imported):
        errors.append(f"{manifest}: missing {missing}")
print('\n'.join(errors) if errors else f'PASS: {len(files)} library/support/challenge source files; no forbidden proof escapes; expose limit 12')
raise SystemExit(bool(errors))
