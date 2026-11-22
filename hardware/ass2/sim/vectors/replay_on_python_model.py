#!/usr/bin/env python3
"""Replay an ASS2-COSIM-V1 suite on the Python model in ../ass2_model.py.

    python3 replay_on_python_model.py cosim_suite.txt

The format is documented at the top of crates/qsag-ass2/examples/export_cosim_vectors.rs.
Every number in a record is hexadecimal. Exit status 0 means every case matched.
"""
import collections
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
import ass2_model as model  # noqa: E402


def records(path):
    with open(path) as source:
        for line in source:
            if not line.startswith("#"):
                tag, *fields = line.split()
                yield tag, fields


def replay(path):
    stream = records(path)
    tag, (cases, words) = next(stream)
    assert tag == "ASS2-COSIM-V1", tag
    cases, words = int(cases, 16), int(words, 16)
    failures, steps_total = [], 0
    endings = collections.Counter()
    for index in range(cases):
        tag, (number, name) = next(stream)
        assert tag == "CASE" and int(number, 16) == index, (tag, number)
        cpu = model.Ass2([(0, 8 * words)])
        initial = bytearray(8 * words)
        want, final_words = {}, {}
        for tag, fields in stream:
            values = [int(field, 16) for field in fields]
            if tag == "IM":
                initial[8 * values[0]:8 * values[0] + 8] = values[1].to_bytes(8, "little")
            elif tag == "XM":
                final_words[values[0]] = values[1]
            elif tag == "END":
                assert values == [index]
                break
            else:
                want[tag] = values
        cpu.mem.poke_bytes(0, bytes(initial))
        cpu.pc = want["IPC"][0]
        cpu.r = list(want["IR"])
        cpu.s = list(want["IS"])
        steps = 0
        while not cpu.halted and steps <= want["STEPS"][0]:
            cpu.step()
            steps += 1
        steps_total += steps
        final = bytearray(initial)
        for word, value in final_words.items():
            final[8 * word:8 * word + 8] = value.to_bytes(8, "little")
        got = {
            "STEPS": [steps],
            "XPC": [cpu.pc],
            "XHALT": [int(cpu.halted)],
            "XECAUSE": [cpu.ecause],
            "XINSTRET": [cpu.instret],
            "XCYCLES": [cpu.cycles],
            "XR": list(cpu.r),
            "XS": list(cpu.s),
        }
        wrong = [tag for tag, value in got.items() if want[tag] != value]
        if bytes(cpu.mem.regions[0][2]) != bytes(final):
            wrong.append("XM")
        if wrong:
            failures.append((index, name, wrong))
        endings[want["XECAUSE"][0]] += 1
    tag, (count,) = next(stream)
    assert tag == "EOF" and int(count, 16) == cases and next(stream, None) is None
    return cases, steps_total, failures, endings


def main():
    cases, steps, failures, endings = replay(sys.argv[1])
    for index, name, wrong in failures[:20]:
        print(f"case {index:x} {name}: mismatch in {' '.join(wrong)}")
    print(f"{cases} cases, {steps} instruction attempts, {len(failures)} mismatching cases")
    print("final ECAUSE histogram:", dict(sorted(endings.items())))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
