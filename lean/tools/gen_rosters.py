#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Regenerate the module rosters in `lean/Qsag.lean` and `lean/AuditAxioms.lean` from disk.

Both rosters must list every `lean/Qsag/**/*.lean` module: `scripts/check_lean_policy.py` and the
`AuditAxioms` disk-inventory check reject a gap. Run from anywhere:

    python3 lean/tools/gen_rosters.py [--exclude Module.Name ...]

`--exclude` drops a module that does not compile yet (it then shows up as unregistered in the
policy check, which is the intended signal). Only the import block of `Qsag.lean` and the
import block and the three audit manifest arrays of `AuditAxioms.lean` are rewritten.
"""
import re
import sys
from pathlib import Path

lean = Path(__file__).resolve().parents[1]
qsag = lean / "Qsag"
# Proof-automation modules: any module with a `Tactic` path component (see `AxiomAuditSupport`).
def is_infrastructure(m):
    return "Tactic" in m.split(".")


ORDER = ["Tactic", "Spec", "Math", "Coding", "Oracle", "Protocol", "Custody", "Exec", "Machine", "Top", "Tests"]

excluded = set()
args = sys.argv[1:]
while args:
    if args[0] == "--exclude" and len(args) > 1:
        excluded.add(args[1]); args = args[2:]
    else:
        raise SystemExit(__doc__)

modules = sorted(
    "Qsag." + ".".join(p.relative_to(qsag).with_suffix("").parts) for p in qsag.rglob("*.lean")
)
modules = [m for m in modules if m not in excluded]


def group(m):
    parts = m.split(".")
    return "/".join(parts[1:-1])


def rank(g):
    top = g.split("/")[0] if g else ""
    return (ORDER.index(top) if top in ORDER else len(ORDER), g)


groups = sorted({group(m) for m in modules}, key=rank)

# --- Qsag.lean: keep the header through the first closing `-/`, regenerate the imports.
root = lean / "Qsag.lean"
text = root.read_text()
header = text[: text.index("-/") + 2]
body = []
for g in groups:
    body.append(f"\n-- {'Qsag/' + g if g else 'Qsag (unsorted)'}")
    body += [f"public import {m}" for m in modules if group(m) == g]
root.write_text(header + "\n" + "\n".join(body) + "\n")

# --- AuditAxioms.lean: regenerate `import all` lines and the three module manifests.
def is_reexport(m):
    """Import-only umbrella: nothing but `module`, imports and comments."""
    src = (qsag / Path(*m.split(".")[1:])).with_suffix(".lean").read_text()
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    src = re.sub(r"--.*", "", src)
    line = r"\s*(module|(public |private )?(meta )?import (all )?[\w.]+)?\s*"
    return all(re.fullmatch(line, l) for l in src.splitlines())


def set_array(text, name, entries):
    marker = f"  let {name} : Array Name := #[\n"
    a = text.index(marker) + len(marker)
    b = text.index("  ]\n", a)
    return text[:a] + "".join(f"    `{m}{',' if k + 1 < len(entries) else ''}\n" for k, m in enumerate(entries)) + text[b:]


audit = lean / "AuditAxioms.lean"
text = audit.read_text()
start = text.index("import Qsag\n") + len("import Qsag\n")
end = text.index("import Lean\n")
ordered = [m for g in groups for m in modules if group(m) == g]
text = text[:start] + "".join(f"import all {m}\n" for m in ordered) + text[end:]
infra = [m for m in ordered if is_infrastructure(m)]
# These modules run assurance commands over imports. AuditAxioms verifies that
# every re-export module owns zero declarations in the compiled environment.
check_only = {
    "Qsag.Tests.ApologyRetirementTeeth",
    "Qsag.Tests.RecursiveAggregationTeeth",
}
reexport = [m for m in ordered if not is_infrastructure(m) and (m in check_only or is_reexport(m))]
proof = [m for m in ordered if m not in infra and m not in reexport]
text = set_array(text, "infrastructureModules", infra)
text = set_array(text, "reexportModules", reexport)
text = set_array(text, "auditedProofModules", proof)
audit.write_text(text)
print(f"{len(modules)} modules registered ({len(proof)} proof, {len(infra)} tactic, {len(reexport)} re-export, {len(excluded)} excluded)")
