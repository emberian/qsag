#!/usr/bin/env python3
"""Check source policy; compiled dependency audits remain authoritative.

Source-level gates over `lean/`, `aeneas/lean/` and `aeneas/lean-whir/`:
  * no `axiom`, `sorry`, `native_decide`, `bv_decide`, `grind`, `Classical.choice` or compiler-trust
    escapes; LAW-M1 expose budget; LAW-M2 meta imports; docstring citations resolve;
  * every on-disk module is registered in its root umbrella and its axiom-audit manifest;
  * `lean/Qsag/` is layered (see `LAYER_RANK`): imports only go down, every library module is
    reachable from `Qsag/Top/`, and `import all` does not occur inside the library.
There are no opt-outs: a tree that is mid-migration fails with the list of what is left.
"""
from collections import Counter
import json
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
rust_files = sorted(
    p for base in ("crates", "aeneas")
    for p in (root / base).rglob("*.rs")
    if "target" not in p.parts
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
    r"\baxiom\b|\bsorry\b|\bnative_decide\b|\bbv_decide\b|\bgrind\b"
    r"|\bClassical\.choice\b|\bLean\.ofReduceBool\b|\bLean\.ofReduceNat\b|\bLean\.trustCompiler\b"
)
declaration_pattern = re.compile(
    r"(?m)^\s*(?:@\[[^]]*\]\s*)?(?:public\s+)?(?:private\s+)?(?:protected\s+)?"
    r"(?:noncomputable\s+)?(?:partial\s+)?(?:unsafe\s+)?"
    r"(?:theorem|lemma|def|abbrev|opaque|constant|structure|inductive|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
rust_declaration_pattern = re.compile(
    r"\b(?:fn|const|static|struct|enum|type|trait)\s+([A-Za-z_][A-Za-z0-9_]*)\b"
)
posix_flag_pattern = re.compile(
    r"^(?:O|F|MAP|PROT|MADV|LOCK|AT|CLOCK|SEEK|MS)_[A-Z0-9_]+$"
)
citation_pattern = re.compile(
    r"(?i)\b(?:"
    r"(?:proved|proven|discharged|established|verified|certified|justified)\s+(?:in|by|via)|"
    r"theorem|lemma|corollary|proof|proved|proven|proves|via|see(?:\s+also)?"
    r")\s+(?:the\s+)?`([A-Za-z_][A-Za-z0-9_'.]*)`"
)
project_citation_prefixes = ("Qsag.", "Aeneas.", "qsag_verified.", "qsag_whir_verified.")
declarations = {
    match[1]
    for path in files
    for match in declaration_pattern.finditer(code(path.read_text()))
}
declaration_leaves = {name.rsplit(".", 1)[-1] for name in declarations}
rust_declarations = {
    match[1]
    for path in rust_files
    for match in rust_declaration_pattern.finditer(path.read_text())
}


def ghost_citations(raw):
    """Return cited project declarations absent from the Lean/Rust declaration index."""
    ghosts = []
    for comment in re.finditer(r"/-(?:!|-)(.*?)-/", raw, re.S):
        for citation in citation_pattern.finditer(comment[1]):
            name = citation[1]
            leaf = name.rsplit(".", 1)[-1]
            if (
                name not in declarations
                and leaf not in declaration_leaves
                and leaf not in rust_declarations
                and not ("." not in name and posix_flag_pattern.match(name))
            ):
                if "." not in name and "_" not in name:
                    continue
                if "." not in name or name.startswith(project_citation_prefixes):
                    line = (
                        raw[: comment.start()].count("\n")
                        + comment[1][: citation.start()].count("\n")
                        + 1
                    )
                    ghosts.append((line, name))
    return ghosts


if ghost_citations("/-- See `citation_negative_control_missing`. -/") != [
    (1, "citation_negative_control_missing")
]:
    raise RuntimeError("docstring citation negative control (See) unexpectedly passed")
if ghost_citations("/-- Proved by `citation_negative_control_missing`. -/") != [
    (1, "citation_negative_control_missing")
]:
    raise RuntimeError("docstring citation negative control (Proved by) unexpectedly passed")
if ghost_citations("/-- Values tested by `z_ood` remain bounded. -/") != []:
    raise RuntimeError("docstring citation passive-variable control unexpectedly failed")

strawman_verifier_patterns = (
    re.compile(
        r"(?:def|abbrev)\s+[A-Za-z_][A-Za-z0-9_'.]*[Vv]erif[A-Za-z0-9_'.]*[^:=\n]*:=\s*fun\b[^;\n]*=>\s*true\b"
    ),
    re.compile(r":\s*(?:[A-Za-z0-9_'.]+\.)?Verifier\s*:=\s*fun\b[^;\n]*=>\s*true\b"),
    re.compile(r"\bverify\b[^:=\n]*:=\s*(?:fun\b[^;\n]*=>\s*)?true\b"),
)


def strawman_verifiers(clean_source):
    hits = []
    for pat in strawman_verifier_patterns:
        for match in pat.finditer(clean_source):
            line = clean_source[: match.start()].count("\n") + 1
            hits.append((line, match[0].strip()))
    return sorted(set(hits))


if not strawman_verifiers("def brokenClassical : Verifier := fun _ _ _ => true"):
    raise RuntimeError("strawman verifier negative control (Verifier := fun ... => true) unexpectedly passed")
if not strawman_verifiers("def acceptAll : SigScheme Unit Unit Unit where\n  verify _ _ _ := true"):
    raise RuntimeError("strawman verifier negative control (verify := true) unexpectedly passed")
if strawman_verifiers("def realVerifier : Verifier := fun pk t sig => decide (sig = sign pk t)"):
    raise RuntimeError("strawman verifier positive control unexpectedly failed")

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
        # A local binder or `match` scrutinee named `grind` (the WOTS+C grinding counter) is not the tactic.
        if tok == "grind" and re.match(r"\s*(?::=|with\b)", source[match.end():]):
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
    for line, snippet in strawman_verifiers(source):
        errors.append(f"{relative}:{line}: constant-true strawman verifier banned: {snippet}")

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


# Layered architecture of `lean/Qsag/`. A module may import its own directory and any directory of
# strictly lower rank. The ranks refine the tiers
#   Spec <- {Math, Coding, Oracle} <- {Protocol, Custody} <- {Exec, Machine} <- Top <- Tests
# with the one-way edges inside a tier that keep the directory graph acyclic: Coding and Oracle sit on
# Math and do not import each other, Custody sits on Protocol, Machine sits on Exec. `Tactic` is
# proof support below everything and imports no library layer.
LAYER_RANK = {
    "Tactic": 0, "Spec": 1, "Math": 2, "Coding": 3, "Oracle": 3,
    "Protocol": 4, "Custody": 5, "Exec": 6, "Machine": 7, "Top": 8, "Tests": 9,
}
module_import_pattern = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private)[ \t]+)?(?:meta[ \t]+)?import[ \t]+(all[ \t]+)?([A-Za-z_][\w.]*)"
)


def layer_of(module):
    """`Qsag.<Layer>.…` -> `<Layer>`; a module sitting directly in `lean/Qsag/` has no layer."""
    parts = module.split(".")
    return parts[1] if len(parts) > 2 else None


def layer_violation(source, target):
    """Why `source` may not import `target`, or None. Unplaced modules are reported separately."""
    s, t = layer_of(source), layer_of(target)
    if s not in LAYER_RANK or t not in LAYER_RANK or s == t or LAYER_RANK[t] < LAYER_RANK[s]:
        return None
    if LAYER_RANK[t] == LAYER_RANK[s]:
        return f"{s} and {t} are peers and must not import each other"
    return f"{s} must not import the higher layer {t}"


for source, target, legal in (
    ("Qsag.Top.A", "Qsag.Spec.B", True),
    ("Qsag.Tests.A", "Qsag.Top.B", True),
    ("Qsag.Coding.A", "Qsag.Coding.B", True),
    ("Qsag.Custody.A", "Qsag.Protocol.Signing.B", True),
    ("Qsag.Math.A", "Qsag.Protocol.Signing.B", False),
    ("Qsag.Spec.A", "Qsag.Math.B", False),
    ("Qsag.Coding.A", "Qsag.Oracle.B", False),
    ("Qsag.Exec.A", "Qsag.Machine.B", False),
    ("Qsag.Top.A", "Qsag.Tests.B", False),
    ("Qsag.Tactic.A", "Qsag.Math.B", False),
):
    if (layer_violation(source, target) is None) != legal:
        raise RuntimeError(f"layer rule control failed: {source} -> {target}")

qsag_dir = root / "lean/Qsag"
file_imports = {}  # relative path -> [(line, is `import all`, imported module)]
qsag_imports = {}  # Qsag module -> (relative path, the same list)
for path in files:
    relative = str(path.relative_to(root))
    source = code(path.read_text())
    file_imports[relative] = [
        (source[: m.start()].count("\n") + 1, bool(m[1]), m[2])
        for m in module_import_pattern.finditer(source)
    ]
    if relative.startswith("lean/Qsag/"):
        module = "Qsag." + ".".join(path.relative_to(qsag_dir).with_suffix("").parts)
        qsag_imports[module] = (relative, file_imports[relative])
qsag_modules = set(qsag_imports) | {"Qsag"}
layer_counts = Counter()

# Out-of-package consumers of the library (`lake env lean --run`) get the import check only.
for path in sorted((root / "validation/lean").rglob("*.lean")):
    source = code(path.read_text())
    file_imports[str(path.relative_to(root))] = [
        (source[: m.start()].count("\n") + 1, bool(m[1]), m[2])
        for m in module_import_pattern.finditer(source)
    ]

for relative, imports in file_imports.items():
    for line, _, target in imports:
        if target.startswith("Qsag.") and target not in qsag_modules:
            layer_counts["dangling"] += 1
            errors.append(f"{relative}:{line}: imports missing module {target}")

for module, (relative, imports) in sorted(qsag_imports.items()):
    if layer_of(module) not in LAYER_RANK:
        layer_counts["unplaced"] += 1
        errors.append(
            f"{relative}: layering: module is not under one of lean/Qsag/{{{','.join(LAYER_RANK)}}}/"
        )
    import_all = sum(is_all for _, is_all, _ in imports)
    if import_all:
        layer_counts["import_all_files"] += 1
        layer_counts["import_all_edges"] += import_all
        errors.append(f"{relative}: LAW-M1: {import_all} `import all` inside lean/Qsag/")
    for line, _, target in imports:
        if target in qsag_imports and (why := layer_violation(module, target)):
            layer_counts["layer_order"] += 1
            errors.append(f"{relative}:{line}: layering: imports {target}: {why}")

# Zero islands: every library module is in the import closure of `Qsag/Top/`.
reached, frontier = set(), [m for m in qsag_imports if layer_of(m) == "Top"]
if not frontier:
    errors.append("lean/Qsag/Top: layering: no Top modules; nothing composes the library")
while frontier:
    module = frontier.pop()
    if module not in reached and module in qsag_imports:
        reached.add(module)
        frontier.extend(target for _, _, target in qsag_imports[module][1])
for module, (relative, _) in sorted(qsag_imports.items()):
    if module not in reached and layer_of(module) not in ("Top", "Tests"):
        layer_counts["islands"] += 1
        errors.append(f"{relative}: layering: not reachable from any Qsag.Top module")


# Mechanical 100% symbol-coverage gate for extracted `aeneas/lean-whir/QsagWhirVerified/Funs.lean`.
funs_def_pattern = re.compile(
    r"(?m)^(?:\s*@\[[^]]*\]\s*)*\s*def\s+([A-Za-z_][A-Za-z0-9_'.]*)\b(.*?)(?=^(?:\s*@\[[^]]*\]\s*)*\s*(?:def|end)\b|\Z)",
    re.S,
)
theorem_stmt_pattern = re.compile(
    r"(?m)^\s*(?:@\[[^]]*\]\s*)*(?:public\s+)?(?:protected\s+)?(?:theorem|lemma)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b(.*?):=\s*(?:by\b|sorry\b|\S)",
    re.S,
)
ident_token_pattern = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def extract_funs_defs(funs_source):
    defs = {}
    for match in funs_def_pattern.finditer(funs_source):
        defs[match[1]] = set(ident_token_pattern.findall(match[2]))
    return defs


def extract_public_theorem_statements(lean_sources):
    stmts = {}
    for src in lean_sources:
        for match in theorem_stmt_pattern.finditer(src):
            name = match[1]
            stmts[name] = set(ident_token_pattern.findall(match[2]))
    return stmts


def whir_uncovered_symbols(funs_defs, theorem_stmts, allowed_theorems=None):
    mentioned = set()
    for thm_name, used in theorem_stmts.items():
        short_name = thm_name.rsplit(".", 1)[-1]
        if short_name.startswith("tooth_"):
            continue
        if allowed_theorems is not None and short_name not in allowed_theorems:
            continue
        for tok in used:
            cleaned = tok.removeprefix("qsag_whir_verified.")
            for suffix in (".val", ".bv"):
                if cleaned.endswith(suffix):
                    cleaned = cleaned[: -len(suffix)]
            mentioned.add(cleaned)
    uncovered = []
    for sym in sorted(funs_defs):
        loop_name = sym[:-5] if sym.endswith(".body") else sym
        if loop_name.endswith("_loop") and len(loop_name) > 5:
            origin = loop_name[:-5]
            covered = (
                origin in funs_defs
                and origin in mentioned
                and loop_name in funs_defs[origin]
                and (sym == loop_name or sym in funs_defs.get(loop_name, set()))
            )
        else:
            covered = sym in mentioned
        if not covered:
            uncovered.append(sym)
    return uncovered


whir_funs_src = code((root / "aeneas/lean-whir/QsagWhirVerified/Funs.lean").read_text())
whir_funs_defs = extract_funs_defs(whir_funs_src)
whir_proof_stmts = extract_public_theorem_statements(
    [
        code((root / "aeneas/lean-whir/QsagWhirVerified/Arithmetic.lean").read_text()),
        code((root / "aeneas/lean-whir/QsagWhirVerified/Proofs.lean").read_text()),
    ]
)
whir_challenge_stmts = extract_public_theorem_statements(
    [code((root / "aeneas/lean-whir/QsagWhirVerifiedChallenge.lean").read_text())]
)
whir_comparator = json.loads((root / "aeneas/lean-whir/comparator.json").read_text())
whir_comparator_short = {
    name.removeprefix("qsag_whir_verified.proofs.")
    for name in whir_comparator["theorem_names"]
}
whir_audit_src = code((root / "aeneas/lean-whir/AuditWhirMirAxioms.lean").read_text())
whir_anchored_short = set(
    re.findall(r"``qsag_whir_verified\.proofs\.([A-Za-z0-9_'.]+)", whir_audit_src)
)

# Negative controls for the `Funs.lean` symbol-coverage gate.
if not whir_funs_defs or whir_uncovered_symbols(whir_funs_defs, {}) != sorted(whir_funs_defs):
    raise RuntimeError("WHIR Funs.lean empty-theorem coverage negative control unexpectedly passed")
if "checked_quorum_sum" not in whir_uncovered_symbols(
    whir_funs_defs,
    {
        k: v
        for k, v in whir_proof_stmts.items()
        if "checked_quorum_sum" not in v and "qsag_whir_verified.checked_quorum_sum" not in v
    },
):
    raise RuntimeError("WHIR Funs.lean dropped-symbol negative control unexpectedly passed")

for sym in whir_uncovered_symbols(whir_funs_defs, whir_proof_stmts):
    errors.append(
        f"aeneas/lean-whir/QsagWhirVerified/Funs.lean: symbol `{sym}` uncovered by non-tooth theorem in Arithmetic.lean/Proofs.lean"
    )
for sym in whir_uncovered_symbols(
    whir_funs_defs, whir_challenge_stmts, allowed_theorems=whir_comparator_short & whir_anchored_short
):
    errors.append(
        f"aeneas/lean-whir/QsagWhirVerifiedChallenge.lean: symbol `{sym}` uncovered by replayed & anchored non-tooth theorem"
    )
for missing_in_comparator in sorted(set(whir_challenge_stmts) - whir_comparator_short):
    errors.append(
        f"aeneas/lean-whir/comparator.json: missing challenge theorem `{missing_in_comparator}`"
    )
for missing_in_challenge in sorted(whir_comparator_short - set(whir_challenge_stmts)):
    errors.append(
        f"aeneas/lean-whir/QsagWhirVerifiedChallenge.lean: missing comparator theorem `{missing_in_challenge}`"
    )
for unanchored in sorted(whir_comparator_short - whir_anchored_short):
    errors.append(
        f"aeneas/lean-whir/AuditWhirMirAxioms.lean: comparator theorem `{unanchored}` missing from requiredWhirMirTheorems"
    )

if errors:
    print("\n".join(errors))
    print(
        f"FAIL: {len(errors)} policy violations; layering: "
        f"{layer_counts['import_all_edges']} `import all` in {layer_counts['import_all_files']} files, "
        f"{layer_counts['layer_order']} upward or peer imports, {layer_counts['islands']} islands, "
        f"{layer_counts['unplaced']} unplaced modules, {layer_counts['dangling']} dangling imports"
    )
else:
    print(
        f"PASS: {len(files)} library/support/challenge source files; no forbidden proof escapes; "
        f"expose limit 12; {len(qsag_imports)} Qsag modules layered, reachable from Top, no `import all`; "
        f"{len(whir_funs_defs)}/{len(whir_funs_defs)} WHIR Funs.lean definitions covered"
    )
raise SystemExit(bool(errors))
