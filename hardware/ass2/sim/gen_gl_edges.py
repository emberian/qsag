"""Directed Goldilocks reduction replay for full-width, noncanonical operands."""
import sys
from itertools import product
from pathlib import Path

from gen_cosim_vectors import SIZE, emit, m, words

values = [0, 1, m.P - 1, m.P, m.P + 1, m.M64]
program = []
for register, value in enumerate(values, start=1):
    program.extend(m.LI64(register, value))
registers = range(1, len(values) + 1)
for a, b, c in product(registers, repeat=3):
    program.append(m.GL(0, 7, a, b, c))
for a, b in product(registers, repeat=2):
    program.extend([m.GL(1, 7, a, b), m.GL(2, 7, a, b)])
program.append(m.HALT)
with Path(sys.argv[1]).open("w") as output:
    print("ASS2-V1 1", file=output)
    steps = emit(output, "goldilocks-full-width", [(0, words(program))], SIZE, len(program))
print(f"{steps} steps covering 216 multiply-add triples and 72 add/subtract pairs")
