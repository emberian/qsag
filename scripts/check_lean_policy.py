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
challenge_paths = {
    "lean/QsagChallenge.lean",
    "aeneas/lean/QsagVerifiedChallenge.lean",
    "aeneas/lean-whir/QsagWhirVerifiedChallenge.lean",
}
library_prefixes = (
    "lean/Qsag/",
    "aeneas/lean/QsagVerified/",
    "aeneas/lean-whir/QsagWhirVerified/",
)
forbidden_tokens = re.compile(
    r"\baxiom\b|\bsorry\b|\bnative_decide\b|\bbv_decide\b"
    r"|\bClassical\.choice\b|\bLean\.ofReduceBool\b|\bLean\.ofReduceNat\b|\bLean\.trustCompiler\b"
)
declaration_pattern = re.compile(
    r"(?m)^\s*(?:@\[[^]]*\]\s*)?(?:public\s+)?(?:private\s+)?(?:protected\s+)?"
    r"(?:noncomputable\s+)?(?:partial\s+)?(?:unsafe\s+)?"
    r"(?:theorem|lemma|def|abbrev|opaque|constant|structure|inductive|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
citation_pattern = re.compile(
    r"(?i)\b(?:theorem|lemma|proof|proved|proves|via|see|by)\s+"
    r"(?:the\s+)?`([A-Za-z_][A-Za-z0-9_'.]*)`"
)
project_citation_prefixes = ("Qsag.", "Aeneas.", "qsag_verified.", "qsag_whir_verified.")
declarations = {
    match[1]
    for path in files
    for match in declaration_pattern.finditer(code(path.read_text()))
}
declaration_leaves = {name.rsplit(".", 1)[-1] for name in declarations}


def ghost_citations(raw):
    """Return cited project declarations absent from the source declaration index."""
    ghosts = []
    for comment in re.finditer(r"/-(?:!|-)(.*?)-/", raw, re.S):
        for citation in citation_pattern.finditer(comment[1]):
            name = citation[1]
            if name not in declarations and name.rsplit(".", 1)[-1] not in declaration_leaves:
                if "." not in name and "_" not in name:
                    continue
                if "." not in name or name.startswith(project_citation_prefixes):
                    line = raw[:comment.start()].count("\n") + comment[1][:citation.start()].count("\n") + 1
                    ghosts.append((line, name))
    return ghosts


if ghost_citations("/-- See `citation_negative_control_missing`. -/") != [(1, "citation_negative_control_missing")]:
    raise RuntimeError("docstring citation negative control unexpectedly passed")

for path in files:
    raw = path.read_text()
    source = code(raw)
    relative = str(path.relative_to(root))
    exposed = sum(
        bool(re.search(r"\bexpose\b", attrs))
        for attrs in re.findall(r"@\[([^]]*)\]", source)
    )
    if len(raw.splitlines()) > 80:
        for section in re.finditer(r"@\[[^]]*\bexpose\b[^]]*\]\s*public\s+section\b", source):
            line = source[:section.start()].count("\n") + 1
            errors.append(f"{relative}:{line}: LAW-M1: file-wide expose section in module over 80 lines")
    if exposed > 12:
        errors.append(f"{relative}: LAW-M1: {exposed} expose annotations")
    if relative.startswith(library_prefixes):
        for escape in re.finditer(r"@\[[^]]*\b(?:implemented_by|extern)\b", source):
            line = source[:escape.start()].count("\n") + 1
            errors.append(f"{relative}:{line}: executable substitution: {escape[0]}")
    if "Tactic" not in path.parts and "Elab" not in path.parts:
        for meta_imp in re.finditer(r"\bpublic\s+meta\s+import\s+Lean\b", source):
            line = source[:meta_imp.start()].count("\n") + 1
            errors.append(f"{relative}:{line}: LAW-M2: public meta import Lean outside Tactic/ or Elab/")
    for match in forbidden_tokens.finditer(source):
        tok = match[0]
        if tok == "sorry" and relative in challenge_paths:
            continue
        # Quoted declaration names (`Name or ``Name) in rejection/negative-control checks do not invoke the axiom.
        if tok in {"Classical.choice", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"} and (
            match.start() > 0 and source[match.start() - 1] == "`"
        ):
            continue
        line = source[:match.start()].count("\n") + 1
        errors.append(f"{relative}:{line}: {tok}")
    for line, citation in ghost_citations(raw):
        errors.append(f"{relative}:{line}: docstring cites missing declaration: {citation}")

for manifest, import_pattern, base_dir, prefix in (
    ("lean/Qsag.lean", r"(?:public )?import (Qsag\.[\w.]+)", "lean/Qsag", "Qsag"),
    ("lean/AuditAxioms.lean", r"import all (Qsag\.[\w.]+)", "lean/Qsag", "Qsag"),
    (
        "aeneas/lean-whir/QsagWhirVerified.lean",
        r"(?:public )?import (QsagWhirVerified\.[\w.]+)",
        "aeneas/lean-whir/QsagWhirVerified",
        "QsagWhirVerified",
    ),
    (
        "aeneas/lean-whir/AuditWhirMirAxioms.lean",
        r"import all (QsagWhirVerified\.[\w.]+)",
        "aeneas/lean-whir/QsagWhirVerified",
        "QsagWhirVerified",
    ),
    (
        "aeneas/lean-whir/AuditWhirMirAxioms.lean",
        r"import all (Aeneas\.[\w.]+)",
        "aeneas/lean-whir/Aeneas",
        "Aeneas",
    ),
):
    imported = set(re.findall(import_pattern, code((root / manifest).read_text())))
    required = {
        prefix + "." + ".".join(p.relative_to(root / base_dir).with_suffix("").parts)
        for p in (root / base_dir).rglob("*.lean")
    }
    for missing in sorted(required - imported):
        errors.append(f"{manifest}: missing {missing}")

print(
    "\n".join(errors)
    if errors
    else f"PASS: {len(files)} library/support/challenge source files; no forbidden proof escapes; expose limit 12"
)
raise SystemExit(bool(errors))
