#!/usr/bin/env python3
"""Concatenate the cell groups of several Liberty files into the first file's library group."""
import re
import sys

out, first, rest = sys.argv[1], sys.argv[2], sys.argv[3:]


def cells(text):
    """Text of every top-level `cell (...) { ... }` group."""
    res, i = [], 0
    for m in re.finditer(r"^\s*cell\s*\(", text, re.M):
        if m.start() < i:
            continue
        j = text.index("{", m.end())
        depth, k = 1, j + 1
        while depth:
            c = text[k]
            depth += (c == "{") - (c == "}")
            k += 1
        res.append(text[m.start():k])
        i = k
    return res


base = open(first).read()
end = base.rstrip().rfind("}")
extra = "\n".join(c for f in rest for c in cells(open(f).read()))
open(out, "w").write(base[:end] + "\n" + extra + "\n}\n")
