#!/usr/bin/env python3
"""Call-site coverage manifest for the Aeneas-extracted crate `aeneas/qsag-verified`.

For every `pub fn` in `aeneas/qsag-verified/src/**` this records where production code in
`crates/**` calls it, and what stands behind it when nothing does: a Lean weld to a `Qsag`
specification, a differential parity test, a same-named production implementation.

A proof about an extracted function says something about production only through one of
those links, so each function gets exactly one status:

  direct                 a non-test call site in `crates/**` names the function
  direct-lexical         only `.method(` call sites, in files whose `use` imports the receiver type
  reached                not called from `crates/**`, but called (transitively, inside
                         `qsag-verified`) by a function that is
  spec-welded            no production path; a Lean weld module refers to the extracted
                         definition, so production is related to it only through the shared
                         specification (and its own, separate implementation)
  proof-only             no production path and no weld; only Lean proofs refer to it
  test-only              referred to by tests alone
  unreferenced           nothing refers to it

The analysis is lexical (comments and string literals are blanked, `use` trees and aliases
are resolved, `#[cfg(test)]` modules are separated). It does not type-check: `direct-lexical`
and `reached` through a `.method(` edge are over-approximations and are labelled as such.

  gen_extraction_coverage.py            write the JSON and Markdown manifests
  gen_extraction_coverage.py --check    exit 1 if the manifests on disk are stale
"""
import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CRATE = ROOT / "aeneas" / "qsag-verified"
LEAN = ROOT / "aeneas" / "lean"
OUT_JSON = CRATE / "extraction-coverage.json"
OUT_MD = CRATE / "extraction-coverage.md"
STATUSES = ("direct", "direct-lexical", "reached", "spec-welded", "proof-only", "test-only",
            "unreferenced")
WORD = r"[A-Za-z_][A-Za-z0-9_]*"


def blank(src):
    """Replace comments, string and char literals with spaces, keeping every newline."""
    out = []
    i, n = 0, len(src)

    def keep(text):
        out.append("".join(c if c == "\n" else " " for c in text))

    while i < n:
        c = src[i]
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            keep(src[i:j])
            i = j
        elif src.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            keep(src[i:j])
            i = j
        elif c == '"' or (c in "br" and re.match(r'b?r?#*"', src[i:i + 8])):
            m = re.match(r'(b?)(r?)(#*)"', src[i:])
            raw, hashes = bool(m[2]), m[3]
            j = i + m.end()
            close = '"' + hashes
            while j < n:
                if not raw and src[j] == "\\":
                    j += 2
                elif src.startswith(close, j):
                    j += len(close)
                    break
                else:
                    j += 1
            keep(src[i:j])
            i = j
        elif c == "'":
            m = re.match(r"'(\\.[^']*|[^'\\])'", src[i:])
            if m:  # a char literal, not a lifetime
                keep(m[0])
                i += m.end()
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def scan_blocks(text):
    """Yield (header, open_pos, close_pos, enclosing_stack) for every brace block."""
    stack, blocks = [], []
    seg_start = 0
    depth = 0  # inside `[...]` or `(...)`, where `;` belongs to an array type
    for m in re.finditer(r"[{};()\[\]]", text):
        ch, pos = m[0], m.start()
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth = max(0, depth - 1)
        elif ch == ";" and depth:
            continue
        elif ch == "{":
            header = text[seg_start:pos]
            stack.append([header, pos])
            seg_start = pos + 1
        elif ch == "}":
            if stack:
                header, start = stack.pop()
                blocks.append((header, start, pos, [h for h, _ in stack]))
            seg_start = pos + 1
        else:
            seg_start = pos + 1
    return blocks


IMPL_RE = re.compile(r"\bimpl\b(?:\s*<[^{]*?>)?\s+(?:(?P<trait>[\w:<>, ]+?)\s+for\s+)?(?P<ty>" + WORD + ")")
FN_RE = re.compile(r"\bfn\s+(" + WORD + r")")
PUB_FN_RE = re.compile(r"\bpub\s+(?:const\s+)?(?:unsafe\s+)?fn\s+(" + WORD + r")")
MOD_RE = re.compile(r"\bmod\s+(" + WORD + r")\s*$")


def is_test_header(header):
    return bool(re.search(r"#\[cfg\((?:all\()?test\b", header)) or "#[test]" in header


def test_spans(text):
    return [(start, end) for header, start, end, _ in scan_blocks(text)
            if is_test_header(header) and (MOD_RE.search(header) or FN_RE.search(header))]


def verified_functions():
    """Every `pub fn` of the extracted crate with its impl type, body and module."""
    functions = []
    for path in sorted((CRATE / "src").rglob("*.rs")):
        if path.name == "lib.rs":
            continue
        module = ".".join(path.relative_to(CRATE / "src").with_suffix("").parts)
        text = blank(path.read_text())
        for header, start, end, outer in scan_blocks(text):
            m = PUB_FN_RE.search(header)
            if not m or any(FN_RE.search(h) for h in outer):
                continue
            if is_test_header(header) or any(is_test_header(h) for h in outer):
                continue
            impl = next((IMPL_RE.search(h) for h in reversed(outer) if IMPL_RE.search(h)), None)
            if impl and impl["trait"]:
                continue
            owner = impl["ty"] if impl else None
            functions.append({
                "module": module,
                "owner": owner,
                "name": m[1],
                "rust": "::".join(x for x in ("qsag_verified", module.replace(".", "::"), owner, m[1]) if x),
                "lean": ".".join(x for x in (module, owner, m[1]) if x),
                "file": str(path.relative_to(ROOT)),
                "line": line_of(text, text.rfind(m[0], 0, start) if m[0] in header else start),
                "body": text[start:end],
            })
    return functions


def expand_use(tree, prefix=()):
    """Expand a `use` tree into (path-tuple, local-name) pairs."""
    tree = tree.strip()
    if not tree:
        return []
    depth, split = 0, None
    for i, c in enumerate(tree):
        if c == "{":
            if depth == 0 and split is None:
                split = i
            depth += 1
        elif c == "}":
            depth -= 1
    if split is not None and tree.endswith("}"):
        head = tuple(p for p in tree[:split].strip().rstrip(":").split("::") if p)
        inner, parts, depth, cur = tree[split + 1:-1], [], 0, ""
        for c in inner:
            if c == "," and depth == 0:
                parts.append(cur)
                cur = ""
            else:
                depth += (c == "{") - (c == "}")
                cur += c
        parts.append(cur)
        pairs = []
        for part in parts:
            pairs += expand_use(part, prefix + head)
        return pairs
    m = re.fullmatch(r"(.+?)(?:\s+as\s+(" + WORD + r"|_))?", tree, re.S)
    path = tuple(p.strip() for p in m[1].split("::") if p.strip())
    if not path:
        return []
    full = prefix + path
    if full[-1] == "self":
        full = full[:-1]
    return [(full, m[2] or full[-1])]


def crate_files():
    for path in sorted((ROOT / "crates").rglob("*.rs")):
        if "target" in path.parts:
            continue
        yield path


def find_sites(functions):
    """Lexical call sites of the verified crate in `crates/**`."""
    free = defaultdict(list)
    methods = defaultdict(list)
    owners = set()
    for f in functions:
        if f["owner"]:
            methods[(f["owner"], f["name"])].append(f)
            owners.add(f["owner"])
        else:
            free[f["name"]].append(f)
    sites = defaultdict(list)
    for path in crate_files():
        raw = path.read_text()
        if "qsag_verified" not in raw:
            continue
        text = blank(raw)
        rel = str(path.relative_to(ROOT))
        tests = test_spans(text)
        path_is_test = bool({"tests", "benches", "examples"} & set(path.relative_to(ROOT).parts))

        def add(f, pos, kind):
            in_test = path_is_test or any(a <= pos <= b for a, b in tests)
            sites[f["rust"]].append({"file": rel, "line": line_of(text, pos), "kind": kind,
                                     "test": in_test})

        local_fns, local_types, use_spans = {}, {}, []
        for m in re.finditer(r"\b(pub(?:\([^)]*\))?\s+)?use\s+((?:::)?qsag_verified\b[^;]*);", text):
            use_spans.append((m.start(), m.end()))
            for full, local in expand_use(m[2].lstrip(":")):
                item = full[-1]
                if item == "*":
                    for name in free:
                        local_fns.setdefault(name, name)
                    for owner in owners:
                        local_types.setdefault(owner, owner)
                    continue
                if item in free:
                    local_fns[local] = item
                    if m[1]:
                        for f in free[item]:
                            add(f, m.start(), "re-export")
                if item in owners:
                    local_types[local] = item
        in_use = lambda pos: any(a <= pos < b for a, b in use_spans)
        # Fully qualified paths.
        for m in re.finditer(r"\bqsag_verified((?:\s*::\s*" + WORD + r")+)", text):
            if in_use(m.start()):
                continue
            parts = [p.strip() for p in m[1].split("::") if p.strip()]
            if parts[-1] in free and (len(parts) == 1 or parts[-2] not in owners):
                for f in free[parts[-1]]:
                    add(f, m.start(), "path")
            if len(parts) >= 2 and (parts[-2], parts[-1]) in methods:
                for f in methods[(parts[-2], parts[-1])]:
                    add(f, m.start(), "path")
        for local, item in local_fns.items():
            for m in re.finditer(r"(?<![\w:.])" + re.escape(local) + r"\s*(?:::\s*<[^>]*>\s*)?\(", text):
                if not in_use(m.start()) and not re.search(r"\bfn\s+$", text[max(0, m.start() - 8):m.start()]):
                    for f in free[item]:
                        add(f, m.start(), "call")
            # Passed as a value, e.g. `.map(name)`.
            for m in re.finditer(r"[(,]\s*" + re.escape(local) + r"\s*[,)]", text):
                if not in_use(m.start()):
                    for f in free[item]:
                        add(f, m.start(), "fn-value")
        for local, owner in local_types.items():
            for (ty, name), fs in methods.items():
                if ty != owner:
                    continue
                for m in re.finditer(r"(?<![\w:])" + re.escape(local) + r"\s*::\s*" + re.escape(name) + r"\b", text):
                    if not in_use(m.start()) and not text[max(0, m.start() - 16):m.start()].rstrip().endswith("::"):
                        for f in fs:
                            add(f, m.start(), "assoc")
                for m in re.finditer(r"\.\s*" + re.escape(name) + r"\s*\(", text):
                    for f in fs:
                        add(f, m.start(), "method-lexical")
    for key in sites:
        seen, unique = set(), []
        for s in sorted(sites[key], key=lambda s: (s["file"], s["line"], s["kind"])):
            if (s["file"], s["line"]) not in seen or s["kind"] == "path":
                if (s["file"], s["line"], s["kind"]) not in seen:
                    unique.append(s)
                seen.add((s["file"], s["line"]))
                seen.add((s["file"], s["line"], s["kind"]))
        sites[key] = unique
    return sites


def call_graph(functions):
    """Intra-crate edges caller -> callee (definite and lexical)."""
    free = defaultdict(list)
    methods = defaultdict(list)
    by_method_name = defaultdict(list)
    for f in functions:
        if f["owner"]:
            methods[(f["owner"], f["name"])].append(f)
            by_method_name[f["name"]].append(f)
        else:
            free[f["name"]].append(f)
    edges = defaultdict(dict)
    for f in functions:
        body = f["body"]
        for name, fs in free.items():
            if re.search(r"(?<![\w.])" + re.escape(name) + r"\s*\(", body):
                for g in fs:
                    edges[f["rust"]][g["rust"]] = "definite"
        for (owner, name), fs in methods.items():
            pattern = r"\b(?:" + re.escape(owner) + (r"|Self" if f["owner"] == owner else "") + r")\s*::\s*" + re.escape(name) + r"\b"
            if re.search(pattern, body):
                for g in fs:
                    edges[f["rust"]][g["rust"]] = "definite"
        for name, fs in by_method_name.items():
            if re.search(r"\.\s*" + re.escape(name) + r"\s*\(", body):
                for g in fs:
                    edges[f["rust"]].setdefault(g["rust"], "lexical")
    return edges


def lean_references(functions):
    funs = (LEAN / "QsagVerified" / "Funs.lean").read_text()
    extracted = set(re.findall(r"^(?:@\[[^\]]*\]\s*)?def\s+(\S+)", funs, re.M))
    proof_files = [p for p in sorted(LEAN.rglob("*.lean"))
                   if ".lake" not in p.parts and p.name not in ("Funs.lean", "Types.lean")
                   and not p.name.startswith("QsagVerifiedChallenge")
                   and p.relative_to(LEAN).parts[0] != "Aeneas" and p.name != "Aeneas.lean"]
    texts = {str(p.relative_to(ROOT)): re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", " ", p.read_text(), flags=re.S))
             for p in proof_files}
    refs = {}
    for f in functions:
        # A method that shares its name with a field is emitted as `Type.impl.name`.
        clash = ".".join(x for x in (f["module"], f["owner"], "impl", f["name"]) if x)
        if f["owner"] and f["lean"] not in extracted and clash in extracted:
            f["lean"] = clash
        pattern = re.compile(r"(?<![\w.])" + re.escape(f["lean"]) + r"(?![\w])")
        files = [name for name, text in texts.items() if pattern.search(text)]
        refs[f["rust"]] = {
            "extracted": f["lean"] in extracted,
            "proofs": [n for n in files if "Weld" not in Path(n).name],
            "welds": [n for n in files if "Weld" in Path(n).name],
        }
    return refs


def production_twins(functions):
    """Same-named non-test `fn` definitions in `crates/**` for free functions."""
    names = {f["name"] for f in functions if not f["owner"]}
    twins = defaultdict(list)
    for path in crate_files():
        if {"tests", "benches", "examples"} & set(path.relative_to(ROOT).parts):
            continue
        text = blank(path.read_text())
        tests = test_spans(text)
        for m in re.finditer(r"\bfn\s+(" + WORD + r")\b", text):
            if m[1] in names and not any(a <= m.start() <= b for a, b in tests):
                twins[m[1]].append(f"{path.relative_to(ROOT)}:{line_of(text, m.start())}")
    return twins


def parity_references(functions):
    hits = {}
    tests = {p.name: blank(p.read_text()) for p in sorted((CRATE / "tests").glob("*.rs"))}
    for f in functions:
        if f["owner"]:
            pattern = re.compile(r"\b" + re.escape(f["owner"]) + r"\s*::\s*" + re.escape(f["name"]) + r"\b|\.\s*"
                                 + re.escape(f["name"]) + r"\s*\(")
        else:
            pattern = re.compile(r"(?<![\w.])" + re.escape(f["name"]) + r"\b")
        hits[f["rust"]] = [f"aeneas/qsag-verified/tests/{name}" for name, text in tests.items()
                           if pattern.search(text)]
    return hits


def build():
    functions = verified_functions()
    sites = find_sites(functions)
    edges = call_graph(functions)
    lean = lean_references(functions)
    twins = production_twins(functions)
    parity = parity_references(functions)
    status = {}
    for f in functions:
        prod = [s for s in sites.get(f["rust"], []) if not s["test"]]
        if any(s["kind"] != "method-lexical" for s in prod):
            status[f["rust"]] = "direct"
        elif prod:
            status[f["rust"]] = "direct-lexical"
    # Transitive reach inside the verified crate from production-called functions.
    via = {}
    frontier = sorted(status)
    while frontier:
        nxt = []
        for caller in frontier:
            for callee, kind in sorted(edges.get(caller, {}).items()):
                if callee not in status:
                    status[callee] = "reached"
                    via[callee] = {"caller": caller, "edge": kind}
                    nxt.append(callee)
        frontier = nxt
    records = []
    for f in functions:
        key = f["rust"]
        all_sites = sites.get(key, [])
        if key not in status:
            if lean[key]["welds"]:
                status[key] = "spec-welded"
            elif lean[key]["proofs"]:
                status[key] = "proof-only"
            elif all_sites or parity[key]:
                status[key] = "test-only"
            else:
                status[key] = "unreferenced"
        record = {
            "function": key,
            "defined_at": f"{f['file']}:{f['line']}",
            "lean_definition": f["lean"],
            "extracted": lean[key]["extracted"],
            "status": status[key],
            "production_call_sites": [f"{s['file']}:{s['line']} ({s['kind']})" for s in all_sites if not s["test"]],
            "test_call_sites": [f"{s['file']}:{s['line']} ({s['kind']})" for s in all_sites if s["test"]],
            "lean_weld_modules": lean[key]["welds"],
            "lean_proof_modules": lean[key]["proofs"],
            "verified_crate_tests": parity[key],
            "same_named_production_fns": sorted(twins.get(f["name"], [])) if not f["owner"] else [],
        }
        if key in via:
            record["reached_via"] = via[key]
        records.append(record)
    records.sort(key=lambda r: r["function"])
    summary = {s: sum(r["status"] == s for r in records) for s in STATUSES}
    summary["total"] = len(records)
    summary["not_extracted"] = sum(not r["extracted"] for r in records)
    return {"format": 1, "crate": "aeneas/qsag-verified", "method": "lexical; see scripts/gen_extraction_coverage.py",
            "summary": summary, "functions": records}


def markdown(manifest):
    s = manifest["summary"]
    lines = [
        "# Extraction call-site coverage: `aeneas/qsag-verified`",
        "",
        "Generated by `scripts/gen_extraction_coverage.py`; do not edit. `--check` fails when stale.",
        "The analysis is lexical. Statuses are defined in the script docstring.",
        "",
        "| Status | Functions |",
        "|---|---|",
    ]
    lines += [f"| {name} | {s[name]} |" for name in STATUSES]
    lines += [f"| **total** | **{s['total']}** |", "",
              f"`pub fn`s with no definition in `Funs.lean`: {s['not_extracted']}.", ""]
    for name in STATUSES:
        rows = [r for r in manifest["functions"] if r["status"] == name]
        if not rows:
            continue
        lines += [f"## {name} ({len(rows)})", ""]
        if name in ("direct", "direct-lexical"):
            lines += ["| Function | Production call sites | First |", "|---|---|---|"]
            for r in rows:
                first = r["production_call_sites"][0].split(" ")[0]
                lines.append(f"| `{r['function']}` | {len(r['production_call_sites'])} | `{first}` |")
        elif name == "reached":
            lines += ["| Function | Reached from | Edge |", "|---|---|---|"]
            for r in rows:
                lines.append(f"| `{r['function']}` | `{r['reached_via']['caller']}` | {r['reached_via']['edge']} |")
        else:
            lines += ["| Function | Lean welds | Lean proofs | Crate tests | Same-named production fns |",
                      "|---|---|---|---|---|"]
            for r in rows:
                lines.append(f"| `{r['function']}` | {len(r['lean_weld_modules'])} | {len(r['lean_proof_modules'])} | "
                             f"{len(r['verified_crate_tests'])} | {len(r['same_named_production_fns'])} |")
        lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--check", action="store_true", help="fail if the manifests on disk are stale")
    args = parser.parse_args()
    manifest = build()
    text_json = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    text_md = markdown(manifest) + "\n"
    if manifest["summary"]["not_extracted"]:
        missing = [r["function"] for r in manifest["functions"] if not r["extracted"]]
        print(f"warning: {len(missing)} pub fn(s) without a Funs.lean definition "
              "(`extracted: false` in the manifest)", file=sys.stderr)
    if args.check:
        stale = [str(p.relative_to(ROOT)) for p, text in ((OUT_JSON, text_json), (OUT_MD, text_md))
                 if not p.exists() or p.read_text() != text]
        if stale:
            raise SystemExit("extraction coverage manifest is stale: " + ", ".join(stale))
        print(f"extraction coverage manifest current ({manifest['summary']['total']} functions)")
        return
    OUT_JSON.write_text(text_json)
    OUT_MD.write_text(text_md)
    print(json.dumps(manifest["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
