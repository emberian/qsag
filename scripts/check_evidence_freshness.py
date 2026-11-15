#!/usr/bin/env python3
"""Report which recorded checks still describe the current source tree.

Inputs (all under docs/):
  CONVERGENCE_SOURCE.json    path -> sha256 pinned by the recorded acceptance snapshot
  CONVERGENCE_EVIDENCE.json  recorded gates (log digest, exit code) of that snapshot
  CURRENT_SCOPED_CHECKS.json later scoped checks, each with its own explicit input hashes,
                             plus the gate -> source-scope map used below

Nothing here re-executes a check or rewrites a recorded hash. A gate is `fresh` only if every
pinned file in its scope is byte-identical and the scope contains no file the snapshot never
pinned; a scoped check is `fresh` only if every input it recorded is byte-identical and its
scope gained no file. Each Lean module is also reported on its own: it keeps a scoped check
exactly while its bytes and its whole import closure are the recorded ones, because an
unchanged module whose import changed was not checked in its current meaning.

Exit status: 0 for a report, 1 with --strict when anything is stale, 2 for malformed manifests.
"""
import argparse
import fnmatch
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
SKIP_PARTS = {".lake", "target", "__pycache__", ".git"}
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(Qsag(?:\.[\w']+)*)\s*$", re.M)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree_files(root):
    return sorted(
        str(p.relative_to(root)) for p in root.rglob("*")
        if p.is_file() and not SKIP_PARTS & set(p.relative_to(root).parts)
    )


def in_scope(path, patterns):
    return any(fnmatch.fnmatchcase(path, pat) for pat in patterns)


def drift(pinned, current_hash, existing, patterns):
    """Classify a scope: pinned files that changed or vanished, and files never pinned."""
    changed = sorted(p for p, h in pinned.items() if in_scope(p, patterns) and current_hash(p) not in (h, None))
    missing = sorted(p for p, h in pinned.items() if in_scope(p, patterns) and current_hash(p) is None)
    unpinned = sorted(p for p in existing if in_scope(p, patterns) and p not in pinned)
    return {"changed": changed, "missing": missing, "unpinned": unpinned}


def lean_modules(root, existing):
    """Module name -> (path, direct Qsag imports) for the main library."""
    mods = {}
    for path in existing:
        if path == "lean/Qsag.lean" or (path.startswith("lean/Qsag/") and path.endswith(".lean")):
            name = ".".join(Path(path).relative_to("lean").with_suffix("").parts)
            mods[name] = (path, sorted(set(IMPORT.findall((root / path).read_text()))))
    return mods


def closure(mods, name, seen=None):
    seen = set() if seen is None else seen
    for dep in mods.get(name, ("", []))[1]:
        if dep not in seen:
            seen.add(dep)
            closure(mods, dep, seen)
    return seen


def evaluate(root, pinned, evidence, scoped):
    existing = tree_files(root)
    cache = {}

    def current_hash(path):
        if path not in cache:
            full = root / path
            cache[path] = sha256(full) if full.is_file() else None
        return cache[path]

    report = {"format": 1, "snapshot": {
        "date": evidence.get("date"),
        "pinned_files": len(pinned),
        **{k: len(v) for k, v in drift(pinned, current_hash, [], ["*"]).items() if k != "unpinned"},
    }}

    scopes = scoped.get("recorded_gate_scopes", {})
    gates = {}
    for gate, record in evidence.get("gates", {}).items():
        if gate not in scopes:
            gates[gate] = {"status": "unscoped", "recorded_exit_code": record.get("exit_code")}
            continue
        d = drift(pinned, current_hash, existing, scopes[gate])
        stale = any(d.values())
        gates[gate] = {
            "status": "stale" if stale else "fresh",
            "recorded_exit_code": record.get("exit_code"),
            "recorded_log_sha256": record.get("sha256"),
            **{k: len(v) for k, v in d.items()},
            "examples": (d["changed"] + d["missing"] + d["unpinned"])[:5],
        }
    report["recorded_gates"] = gates

    checks = {}
    for check in scoped.get("checks", []):
        inputs = check.get("inputs", {})
        changed = sorted(p for p, h in inputs.items() if current_hash(p) != h)
        excluded = {e["path"] for e in check.get("excluded_modules", [])}
        unlisted = sorted(
            p for p in existing
            if in_scope(p, check.get("input_scope", [])) and p not in inputs and p not in excluded
        )
        checks[check["id"]] = {
            "status": "stale" if changed or unlisted or not inputs else "fresh",
            "result": check.get("result"),
            "exit_code": check.get("exit_code"),
            "inputs": len(inputs),
            "changed": changed,
            "unlisted_in_scope": unlisted,
            "excluded_modules": [e["module"] for e in check.get("excluded_modules", [])],
        }
    report["scoped_checks"] = checks

    mods = lean_modules(root, existing)
    covered = {}
    for check in scoped.get("checks", []):
        inputs = check.get("inputs", {})
        if any(current_hash(p) != inputs.get(p) for p in check.get("global_inputs", [])):
            continue
        for mod in check.get("modules_checked", []):
            # A module keeps its check while its own bytes and its whole import closure are the
            # recorded ones, even if unrelated files moved and made the check as a whole stale.
            files = [mods[m][0] for m in {mod} | closure(mods, mod) if m in mods]
            if mod in mods and all(f in inputs and current_hash(f) == inputs[f] for f in files):
                covered.setdefault(mod, []).append(check["id"])
    lean = {}
    for name, (path, _) in sorted(mods.items()):
        own = "unpinned" if path not in pinned else ("unchanged" if current_hash(path) == pinned[path] else "changed")
        deps = sorted(
            dep for dep in closure(mods, name)
            if dep in mods and (mods[dep][0] not in pinned or current_hash(mods[dep][0]) != pinned[mods[dep][0]])
        )
        lean[name] = {
            "path": path,
            "sha256": current_hash(path),
            "vs_snapshot": own,
            "snapshot_closure_fresh": own == "unchanged" and not deps,
            "drifted_imports": len(deps),
            "fresh_scoped_checks": covered.get(name, []),
        }
    report["lean_modules"] = lean
    report["summary"] = {
        "recorded_gates_fresh": sum(g["status"] == "fresh" for g in gates.values()),
        "recorded_gates_total": len(gates),
        "scoped_checks_fresh": sum(c["status"] == "fresh" for c in checks.values()),
        "scoped_checks_total": len(checks),
        "lean_modules_total": len(lean),
        "lean_modules_snapshot_closure_fresh": sum(m["snapshot_closure_fresh"] for m in lean.values()),
        "lean_modules_with_fresh_scoped_check": sum(bool(m["fresh_scoped_checks"]) for m in lean.values()),
        "lean_modules_without_current_check": sorted(
            n for n, m in lean.items() if not m["snapshot_closure_fresh"] and not m["fresh_scoped_checks"]
        ),
    }
    return report


def self_test():
    """A changed pinned byte, a never-pinned file and a changed scoped input must each read stale."""
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "lean/Qsag").mkdir(parents=True)
        (root / "lean/Qsag/A.lean").write_text("module\n")
        (root / "lean/Qsag/B.lean").write_text("module\npublic import Qsag.A\n")
        pinned = {p: sha256(root / p) for p in ("lean/Qsag/A.lean", "lean/Qsag/B.lean")}
        evidence = {"gates": {"g": {"exit_code": 0, "sha256": "0"}}}
        scoped = {"recorded_gate_scopes": {"g": ["lean/*"]}, "checks": [{
            "id": "c", "inputs": dict(pinned), "input_scope": ["lean/*"],
            "modules_checked": ["Qsag.A", "Qsag.B"], "exit_code": 0,
        }]}
        base = evaluate(root, pinned, evidence, scoped)
        ok = base["recorded_gates"]["g"]["status"] == "fresh" and base["scoped_checks"]["c"]["status"] == "fresh"
        (root / "lean/Qsag/A.lean").write_text("module\n-- edit\n")
        edited = evaluate(root, pinned, evidence, scoped)
        ok &= edited["recorded_gates"]["g"]["status"] == "stale"
        ok &= edited["scoped_checks"]["c"]["status"] == "stale"
        ok &= not edited["lean_modules"]["Qsag.B"]["snapshot_closure_fresh"]
        ok &= edited["lean_modules"]["Qsag.B"]["fresh_scoped_checks"] == []
        ok &= edited["lean_modules"]["Qsag.B"]["vs_snapshot"] == "unchanged"
        (root / "lean/Qsag/A.lean").write_text("module\n")
        (root / "lean/Qsag/C.lean").write_text("module\n")
        added = evaluate(root, pinned, evidence, scoped)
        ok &= added["recorded_gates"]["g"]["status"] == "stale"
        ok &= added["scoped_checks"]["c"]["unlisted_in_scope"] == ["lean/Qsag/C.lean"]
        ok &= added["scoped_checks"]["c"]["status"] == "stale"
        ok &= added["lean_modules"]["Qsag.B"]["fresh_scoped_checks"] == ["c"]
        ok &= "Qsag.C" in added["summary"]["lean_modules_without_current_check"]
    if not ok:
        raise RuntimeError("freshness negative controls did not behave as specified")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--json", metavar="FILE", help="write the full machine-readable report ('-' for stdout)")
    parser.add_argument("--strict", action="store_true", help="exit 1 if any recorded gate or scoped check is stale")
    args = parser.parse_args()
    self_test()
    try:
        pinned = json.loads((DOCS / "CONVERGENCE_SOURCE.json").read_text())
        evidence = json.loads((DOCS / "CONVERGENCE_EVIDENCE.json").read_text())
        scoped_path = DOCS / "CURRENT_SCOPED_CHECKS.json"
        scoped = json.loads(scoped_path.read_text()) if scoped_path.exists() else {}
    except (OSError, ValueError) as exc:
        print(f"malformed evidence manifest: {exc}", file=sys.stderr)
        return 2
    report = evaluate(ROOT, pinned, evidence, scoped)
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.json == "-":
        sys.stdout.write(text)
    elif args.json:
        Path(args.json).write_text(text)
    if args.json != "-":
        snap, summary = report["snapshot"], report["summary"]
        print(f"snapshot {snap['date']}: {snap['pinned_files']} pinned files, "
              f"{snap['changed']} changed, {snap['missing']} missing")
        for gate, g in sorted(report["recorded_gates"].items()):
            detail = "" if g["status"] != "stale" else (
                f" ({g['changed']} changed, {g['missing']} missing, {g['unpinned']} unpinned in scope)")
            print(f"  recorded gate {gate}: {g['status'].upper()}{detail}")
        for cid, c in sorted(report["scoped_checks"].items()):
            detail = "" if c["status"] == "fresh" else (
                f" ({len(c['changed'])} inputs changed, {len(c['unlisted_in_scope'])} new files in scope)")
            print(f"  scoped check {cid}: {c['status'].upper()}{detail}")
        print(f"Lean main library: {summary['lean_modules_total']} modules; "
              f"{summary['lean_modules_snapshot_closure_fresh']} with an unchanged snapshot import closure; "
              f"{summary['lean_modules_with_fresh_scoped_check']} covered by a fresh scoped check; "
              f"{len(summary['lean_modules_without_current_check'])} with no current check")
    stale = (summary_stale := report["summary"])["recorded_gates_fresh"] < summary_stale["recorded_gates_total"] \
        or summary_stale["scoped_checks_fresh"] < summary_stale["scoped_checks_total"]
    return 1 if args.strict and stale else 0


if __name__ == "__main__":
    raise SystemExit(main())
