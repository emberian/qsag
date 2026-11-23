"""Applies the precomputed PyMetis + Hungarian EBR/DSP/region placement plan (`QSAG_ECP5_PLAN`)
inside `nextpnr-ecp5 --pre-place`. Uses only Python stdlib modules so nextpnr's embedded Python
never requires external packages.
"""
import json
import os

plan = json.load(open(os.environ["QSAG_ECP5_PLAN"]))
for i, box in enumerate(plan["regions"]):
    ctx.createRectangularRegion(f"tile{i}", *box)

hard = 0
soft = 0
for name, cell in ctx.cells:
    if name in plan["hard"]:
        ctx.bindBel(plan["hard"][name], cell, STRENGTH_USER)
        hard += 1
    elif name in plan["soft"]:
        ctx.constrainCellToRegion(name, f"tile{plan['soft'][name]}")
        soft += 1

assert hard == len(plan["hard"]), (hard, len(plan["hard"]))
print(f"ecp5_top_place: bound {hard} hard BELs and {soft} FF region guides", flush=True)
