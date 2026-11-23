#!/usr/bin/env python3
"""Add up the per-shard summaries of a co-simulation run (v2/tb/cosim.cpp) and print one table."""
import re
import sys

text = open(sys.argv[1]).read()
tot = {}
order = []
for ln in text.splitlines():
    m = re.match(r"  (scenario \S+|start state:|[a-zA-Z][a-zA-Z ,-]*?)\s+((?:continued|\d).*)$", ln)
    if not m or ln.startswith("RESULT"):
        continue
    key = m.group(1).strip()
    nums = [int(x) for x in re.findall(r"\d+", m.group(2))]
    if key not in tot:
        tot[key] = [0] * len(nums)
        order.append((key, re.sub(r"\d+", "{}", m.group(2))))
    tot[key] = [a + b for a, b in zip(tot[key], nums)]
for key, fmt in order:
    print(f"  {key:26s} {fmt.format(*tot[key])}")
res = re.findall(r"RESULT shard \d+: (\w+) \((\d+) errors\)", text)
errs = [ln for ln in text.splitlines() if "ERROR" in ln or "ASSERT" in ln or "LOCKSTEP" in ln]
for ln in errs[:25]:
    print(ln)
print(f"shards: {len(res)} finished, {sum(1 for r in res if r[0] == 'PASS')} passed, {sum(1 for r in res if r[0] == 'EMPTY')} without "
      f"transactions, {sum(1 for r in res if r[0] == 'FAIL')} failed, {sum(int(r[1]) for r in res)} errors in all")
