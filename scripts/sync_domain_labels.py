#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Keep the Lean domain-label inventory equal to the `QSAG*` literals in the Rust sources.

Scans `crates/<crate>/src/**/*.rs` and `aeneas/<crate>/src/**/*.rs` for production string and
byte-string literals that start with `QSAG`, plus eight-byte `0x51534147........` integer tags,
and compares the result with the generated block of
`lean/Qsag/Protocol/Aggregation/CrossProtocolAndDualOracleComposition.lean`.

What counts as a label:
  * a `"..."`, `b"..."`, `r"..."`, `br"..."` (any `#` count) literal whose decoded value starts
    with `QSAG` and does not start with `QSAG_` (environment-variable names);
  * an integer literal `0x51534147XXXXXXXX` (underscores allowed), read as its eight bytes;
  * outside comments and attributes, and outside anything guarded by a test-only attribute
    (`#[cfg(test)]`, `#[cfg(all(test, ..))]`, `#[test]`), including files declared by
    `#[cfg(test)] mod name;`.
Labels completed at run time by `format!` or by appended bytes appear as written in the source.

A label that occurs in more than one crate must be listed in `SHARED`, with the reason it is
shared. A shared label missing from `SHARED` is a failure (a new collision between crates), and
so is a `SHARED` entry that is no longer shared (a stale allowlist entry).

    sync_domain_labels.py            check; exit 1 on any difference
    sync_domain_labels.py --write    rewrite the generated block in the Lean file
    sync_domain_labels.py --json     print the scanned inventory
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_FILE = ROOT / "lean/Qsag/Protocol/Aggregation/CrossProtocolAndDualOracleComposition.lean"
BEGIN = "-- BEGIN GENERATED (scripts/sync_domain_labels.py --write)"
END = "-- END GENERATED (scripts/sync_domain_labels.py)"

SCAN_ROOTS = ["crates", "aeneas"]

# Labels that two or more crates use on purpose, with the reason. Hand-maintained: the scan
# fails when the set of labels actually shared between crates differs from this.
SHARED: dict[str, str] = {
    "QSAG.FIRST_SIGNED.V1": "durable first-signed ledger tag: qsag-core (baggy) and the "
                            "qsag-quorum durable custody open the same ledger format",
    "QSAG.HYBRID.V2": "hybrid address tag: aeneas/qsag-verified is the extraction copy of the "
                      "qsag-addr function",
    "QSAG.MU/v2": "message-representative frame: hashed by qsag-agg, rebuilt by the qsag-core "
                  "MPC signer",
    "QSAG.POLICY.CTX.V1": "policy signing-context digest: qsag-policy computes it, qsag-cli "
                          "recomputes it for its ledger",
    "QSAG.SEED_BURN.V1": "durable seed-burn ledger tag: qsag-core (pcg_dense) and the "
                         "qsag-quorum durable custody open the same ledger format",
    "QSAGFNOD": "Poseidon2 FORS node domain: one constant in qsag-agg and qsag-accel",
    "QSAGHMS1": "stateful H_msg domain: qsag-agg signature, qsag-core Poseidon2 MPC",
    "QSAGMRKL": "Poseidon2 Merkle node domain: qsag-agg, qsag-accel and qsag-core",
    "QSAGPRFM": "PRF_msg domain: qsag-agg signature, qsag-core Poseidon2 MPC",
    "QSAGWPK1": "WOTS public-key compression domain: qsag-agg signature, qsag-core MPC",
    "QSAGWPRF": "WOTS PRF domain: qsag-agg signature, qsag-core MPC",
    "QSAGWSTP": "WOTS chain-step domain: qsag-agg signature, qsag-core MPC",
}

SIMPLE_ESCAPES = {"n": "\n", "r": "\r", "t": "\t", "\\": "\\", "0": "\0", "'": "'", '"': '"'}


def decode_escapes(body: str) -> str:
    out = []
    i = 0
    while i < len(body):
        ch = body[i]
        if ch != "\\":
            out.append(ch)
            i += 1
            continue
        nxt = body[i + 1] if i + 1 < len(body) else ""
        if nxt == "x":
            out.append(chr(int(body[i + 2:i + 4], 16)))
            i += 4
        elif nxt == "u":
            close = body.index("}", i)
            out.append(chr(int(body[i + 3:close].replace("_", ""), 16)))
            i = close + 1
        elif nxt == "\n":
            i += 2
            while i < len(body) and body[i] in " \t\r\n":
                i += 1
        elif nxt in SIMPLE_ESCAPES:
            out.append(SIMPLE_ESCAPES[nxt])
            i += 2
        else:
            out.append(nxt)
            i += 2
    return "".join(out)


HEX_TAG = re.compile(r"0x5153_?4147(?:_?[0-9A-Fa-f]{4}){2}(?![0-9A-Fa-f_])")
RAW_OPEN = re.compile(r"b?r(#*)\"")
TEST_MOD = re.compile(
    r"\s*(?:#\[[^\]]*\]\s*)*(?:pub(?:\s*\([^)]*\))?\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;")


def split_top(args: str) -> list[str]:
    parts, depth, cur = [], 0, []
    for ch in args:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    parts.append("".join(cur).strip())
    return [p for p in parts if p]


def pred_is_test_only(pred: str) -> bool:
    """`test`, or an `all(...)` with a test-only conjunct. `any(test, ..)` and `not(test)` are
    compiled into production builds and are not test-only."""
    pred = pred.strip()
    if pred == "test":
        return True
    if pred.startswith("all(") and pred.endswith(")"):
        return any(pred_is_test_only(p) for p in split_top(pred[4:-1]))
    return False


def attr_is_test_only(attr: str) -> bool:
    body = attr.strip()
    if body == "test" or body.endswith("::test"):
        return True
    if body.startswith("cfg(") and body.endswith(")"):
        return pred_is_test_only(body[4:-1])
    return False


def lex(src: str):
    """Tokens of a Rust source file, comments and character literals dropped:
    ('str', value), ('hex', value) for eight-byte QSAG tags, ('attr', text, inner, end) for
    `#[..]` / `#![..]` (strings inside an attribute are part of it and are never labels), and
    ('punct', ch) for brackets, braces, parentheses, `;` and `,`."""
    i, n = 0, len(src)

    def word_start(k: int) -> bool:
        return k == 0 or not (src[k - 1].isalnum() or src[k - 1] == "_")

    while i < n:
        ch = src[i]
        if src.startswith("//", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src.startswith("/*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith("/*", i):
                    depth += 1
                    i += 2
                elif src.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        m = RAW_OPEN.match(src, i)
        if m and word_start(i):
            closer = '"' + m.group(1)
            j = src.find(closer, m.end())
            if j < 0:
                return
            yield ("str", src[m.end():j])
            i = j + len(closer)
            continue
        if ch == '"' or (src.startswith('b"', i) and word_start(i)):
            j = i + (2 if ch == "b" else 1)
            start = j
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            yield ("str", decode_escapes(src[start:j]))
            i = j + 1
            continue
        if ch == "'":
            # char literal ('x', '\n', '\u{..}') or a lifetime ('a)
            if src.startswith("'\\", i):
                j = src.find("'", i + 2)
                i = (j + 1) if j > 0 else i + 1
            elif i + 2 < n and src[i + 2] == "'":
                i += 3
            else:
                i += 1
            continue
        if ch == "#" and (src.startswith("#[", i) or src.startswith("#![", i)):
            inner = src.startswith("#![", i)
            j = i + (3 if inner else 2)
            start, depth = j, 1
            while j < n and depth:
                c = src[j]
                if c == '"':
                    j += 1
                    while j < n and src[j] != '"':
                        j += 2 if src[j] == "\\" else 1
                elif c == "[":
                    depth += 1
                elif c == "]":
                    depth -= 1
                j += 1
            yield ("attr", src[start:j - 1], inner, j)
            i = j
            continue
        if ch == "0" and word_start(i):
            m = HEX_TAG.match(src, i)
            if m:
                yield ("hex", bytes.fromhex(m.group(0)[2:].replace("_", "")).decode("latin-1"))
                i = m.end()
                continue
        if ch in "{}()[];,":
            yield ("punct", ch)
        i += 1


def labels_in(src: str) -> tuple[set[str], set[str]]:
    """(labels, test-only child modules) of one file.

    A test-only attribute (`#[cfg(test)]`, `#[cfg(all(test, ..))]`, `#[test]`) guards the next
    item, field, parameter, statement or expression. Its tokens are dropped up to the first of:
    a `;` or `,` at the guarded thing's own nesting level, the `}` that closes its body, or a
    closer that belongs to the enclosing scope. Ending early is the safe direction: it can only
    add a test literal to the inventory, never hide a production one. `#![cfg(test)]` drops the
    rest of the file, and `#[cfg(test)] mod name;` names a file to leave out."""
    found: set[str] = set()
    test_mods: set[str] = set()
    skipping = False
    depth = 0
    for tok in lex(src):
        kind = tok[0]
        if kind == "attr":
            _, text, inner, end = tok
            if attr_is_test_only(text):
                if inner:
                    break
                m = TEST_MOD.match(src, end)
                if m:
                    test_mods.add(m.group(1))
                if not skipping:
                    skipping, depth = True, 0
            continue
        if skipping:
            if kind != "punct":
                continue
            ch = tok[1]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                if depth == 0:
                    skipping = False
                else:
                    depth -= 1
                    if depth == 0 and ch == "}":
                        skipping = False
            elif depth == 0:
                skipping = False
            continue
        if kind in ("str", "hex"):
            value = tok[1]
            if value.startswith("QSAG") and not value.startswith("QSAG_"):
                found.add(value)
    return found, test_mods


def crate_labels(src_dir: Path) -> set[str]:
    per_file: dict[Path, set[str]] = {}
    excluded: list[Path] = []
    for path in sorted(src_dir.rglob("*.rs")):
        labels, test_mods = labels_in(path.read_text(encoding="utf-8"))
        per_file[path] = labels
        home = path.parent if path.name in ("lib.rs", "main.rs", "mod.rs") \
            else path.parent / path.stem
        for name in test_mods:
            excluded += [home / f"{name}.rs", home / name]
    out: set[str] = set()
    for path, labels in per_file.items():
        if any(path == e or e in path.parents for e in excluded):
            continue
        out |= labels
    return out


def scan() -> dict[str, list[str]]:
    inventory: dict[str, list[str]] = {}
    for root in SCAN_ROOTS:
        base = ROOT / root
        for crate_dir in sorted(p for p in base.iterdir() if (p / "src").is_dir()):
            name = crate_dir.name if root == "crates" else f"{root}/{crate_dir.name}"
            labels = crate_labels(crate_dir / "src")
            if labels:
                inventory[name] = sorted(labels)
    return inventory


def shared_labels(inventory: dict[str, list[str]]) -> list[str]:
    owners: dict[str, int] = {}
    for labels in inventory.values():
        for label in labels:
            owners[label] = owners.get(label, 0) + 1
    return sorted(l for l, k in owners.items() if k > 1)


def lean_string(label: str) -> str:
    out = ['"']
    for ch in label:
        if ch in '"\\':
            out.append("\\" + ch)
        elif 0x20 <= ord(ch) < 0x7F:
            out.append(ch)
        elif ord(ch) < 0x100:
            out.append(f"\\x{ord(ch):02x}")
        else:
            out.append(f"\\u{{{ord(ch):x}}}")
    out.append('"')
    return "".join(out)


def label_code(label: str) -> int:
    code = 1
    for byte in label.encode("utf-8"):
        code = code * 256 + byte
    return code


def wrap(items: list[str], indent: str, first: str | None = None, width: int = 100) -> str:
    """Comma-separated items, wrapped; `first` opens the first line, `indent` the others."""
    lines, cur = [], indent if first is None else first
    fresh = True
    for k, item in enumerate(items):
        piece = item + ("," if k + 1 < len(items) else "")
        if not fresh and len(cur) + 1 + len(piece) > width:
            lines.append(cur.rstrip())
            cur = indent
        cur += piece + " "
        fresh = False
    lines.append(cur.rstrip())
    return "\n".join(lines)


def render(inventory: dict[str, list[str]]) -> str:
    shared = shared_labels(inventory)
    total = sum(len(v) for v in inventory.values())
    crates = list(inventory.items())
    out = [BEGIN, ""]
    out += [
        f"/-- Source literal inventory, {len(inventory)} crates and {total} labels: every "
        "production string or",
        "    byte-string literal of `crates/<crate>/src/**/*.rs` and "
        "`aeneas/<crate>/src/**/*.rs` that",
        "    starts with `QSAG` (and every eight-byte `0x51534147........` tag), other than "
        "`QSAG_*`",
        "    environment-variable names and code guarded by a test-only attribute. Includes "
        "wire magics,",
        "    transcript labels and fragments completed at run time; membership does not imply "
        "that a",
        "    label is a cSHAKE customization. Generated: `scripts/sync_domain_labels.py` fails "
        "when this",
        "    list differs from the sources. -/",
        "@[expose] def auditedByteLabels : List (String × List String) := [",
    ]
    for k, (crate, labels) in enumerate(crates):
        out.append(f"  ({lean_string(crate)}, [")
        out.append(wrap([lean_string(l) for l in labels], "    ") + "])"
                   + ("," if k + 1 < len(crates) else ""))
    out += [
        "]",
        "",
        "/-- `labelCode` of every label of `auditedByteLabels`, crate by crate in the same "
        "order: the",
        "    UTF-8 bytes read base 256 after a leading `1`. The quadratic checks run on these "
        "numbers;",
        "    `auditedLabelCodes_eq` proves they are the codes of the strings above. -/",
        "def auditedLabelCodes : List (List Nat) := [",
    ]
    for k, (_crate, labels) in enumerate(crates):
        out.append(wrap([str(label_code(l)) for l in labels], "   ", first="  [") + "]"
                   + ("," if k + 1 < len(crates) else ""))
    out += [
        "]",
        "",
        "/-- The labels that two or more crates use on purpose. Hand-maintained in",
        "    `scripts/sync_domain_labels.py` with a reason per entry; the script fails when the "
        "labels",
        "    actually shared between crates differ from this list. -/",
        "@[expose] def sharedCrossCrateLabels : List String :=",
        wrap([lean_string(l) for l in shared], "   ", first="  [") + "]",
        "",
        END,
    ]
    return "\n".join(out)


def problems(inventory: dict[str, list[str]]) -> list[str]:
    shared = shared_labels(inventory)
    errs = []
    for label in shared:
        if label not in SHARED:
            owners = [c for c, ls in inventory.items() if label in ls]
            errs.append(f"label {label!r} is shared by {owners} and is not in SHARED")
    for label in SHARED:
        if label not in shared:
            errs.append(f"SHARED entry {label!r} is not shared between crates")
    for crate, labels in inventory.items():
        for label in labels:
            n = len(label.encode("utf-8"))
            if not 1 <= n <= 64:
                errs.append(f"{crate}: label {label!r} is {n} bytes (expected 1..64)")
    return errs


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--write", action="store_true", help="rewrite the generated Lean block")
    ap.add_argument("--json", action="store_true", help="print the scanned inventory")
    args = ap.parse_args()

    inventory = scan()
    if args.json:
        json.dump(inventory, sys.stdout, indent=1, ensure_ascii=True)
        print()
        return 0

    errs = problems(inventory)
    block = render(inventory)
    text = LEAN_FILE.read_text(encoding="utf-8")
    if BEGIN not in text or END not in text:
        errs.append(f"{LEAN_FILE.relative_to(ROOT)}: generated-block markers not found")
        current = None
    else:
        a, b = text.index(BEGIN), text.index(END) + len(END)
        current = text[a:b]

    if errs and not args.write:
        for e in errs:
            print(f"FAIL: {e}")
    if args.write:
        if any("SHARED" in e or "bytes" in e for e in errs):
            for e in errs:
                print(f"FAIL: {e}")
            return 1
        if current is None:
            print("FAIL: add the BEGIN/END GENERATED markers to the Lean file first")
            return 1
        if current != block:
            LEAN_FILE.write_text(text[:a] + block + text[b:], encoding="utf-8")
            print(f"wrote {LEAN_FILE.relative_to(ROOT)}")
        else:
            print("unchanged")
        return 0

    if current is not None and current != block:
        old = set(re.findall(r'"((?:[^"\\]|\\.)*)"', current))
        new = set(re.findall(r'"((?:[^"\\]|\\.)*)"', block))
        for label in sorted(new - old):
            print(f"FAIL: missing from Lean: {label}")
        for label in sorted(old - new):
            print(f"FAIL: in Lean but not in the sources: {label}")
        if old == new:
            print("FAIL: generated block differs (ownership, order or codes); run --write")
        errs.append("generated block is stale")
    if errs:
        return 1
    total = sum(len(v) for v in inventory.values())
    print(f"PASS: {len(inventory)} crates, {total} labels, "
          f"{len(shared_labels(inventory))} shared between crates; Lean block current")
    return 0


if __name__ == "__main__":
    sys.exit(main())
