#!/usr/bin/env python3
"""Refresh the four annotated Markdown listings and the two-column PDF listings.

Run sync_listings.py LISTINGS_DIR [--check]. PDF markers can select an inclusive
range of word indices to split a routine across columns. Every word must appear
exactly once in each document. Rust markers select one inclusive line range or 'full'.
"""
import argparse
from collections import defaultdict
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DOCS = (ROOT / "datasheet/dregg64-ass2-datasheet.typ", ROOT / "PROGRAMMING_GUIDE.md")
MARK = re.compile(r"\s*(?://|<!--) @(listing|rust) ([\w.-]+)(?: (full|print)(?: (\d+)-(\d+))?)?(?: -->)?\s*$")
END = re.compile(r"\s*(?://|<!--) @end(?: -->)?\s*$")
WORD = re.compile(r"^([0-9a-f]{4})  ([0-9a-f]{8})  (.+)$")


def render(doc, listings):
    lines = iter(doc.read_text().splitlines())
    rust = (ROOT / "examples/host_driver.rs").read_text().splitlines()
    out = []
    coverage = defaultdict(list)
    rust_blocks = 0
    for line in lines:
        out.append(line)
        m = MARK.fullmatch(line)
        if not m:
            continue
        kind, name, mode, lo, hi = m.groups()
        if kind == "rust":
            rust_blocks += 1
            if name == "full":
                body = rust
            else:
                a, b = map(int, name.split("-"))
                if not 1 <= a <= b <= len(rust):
                    raise ValueError(f"invalid Rust excerpt {name}")
                body = rust[a - 1:b]
        else:
            full, words = listings[name]
            a, b = (int(lo), int(hi) + 1) if lo else (0, len(words))
            coverage[name].extend(range(a, b))
            if mode == "full":
                body = full
            elif mode == "print":
                body = [f"{addr}  {w}  {asm.split(';')[0].strip()}" for addr, w, asm in words[a:b]]
            else:
                raise ValueError(f"unknown listing format in {line}")
        out += ["```" + ("rust" if kind == "rust" else "text"), *body, "```"]
        for line in lines:
            if END.fullmatch(line):
                out.append(line)
                break
        else:
            raise ValueError(f"{doc}: missing @end")
    if rust_blocks != 1:
        raise ValueError(f"{doc}: expected one Rust listing")
    for name, (_, words) in listings.items():
        if coverage[name] != list(range(len(words))):
            raise ValueError(f"{doc}: incomplete, duplicated or unordered {name} listing")
    return "\n".join(out) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("listings", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    listings = {}
    for source in sorted((ROOT / "examples").glob("*.s")):
        full = (args.listings / (source.stem + ".lst")).read_text().splitlines()
        words = [m.groups() for line in full if (m := WORD.match(line))]
        if not words or [int(w[0], 16) for w in words] != list(range(0, 4 * len(words), 4)):
            raise ValueError(f"expected contiguous single-word listing for {source.name}")
        listings[source.stem] = full, words
    for doc in DOCS:
        updated = render(doc, listings)
        if doc.read_text() != updated:
            if args.check:
                raise SystemExit(f"listing drift: {doc}")
            doc.write_text(updated)
        print(f"{doc.name}: {sum(len(w) for _, w in listings.values())} words, Rust block current")


if __name__ == "__main__":
    main()
