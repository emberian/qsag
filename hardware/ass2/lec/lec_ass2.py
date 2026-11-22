#!/usr/bin/env python3
"""Prove ASS2 ALU semantics against the Yosys SMT2 netlist using the Z3 CLI."""
from pathlib import Path
import subprocess
import tempfile

TOP = "qsag_ass2_alu"
RTL = Path(__file__).resolve().parents[1] / "rtl"


def bv(n, width=64):
    return f"(_ bv{n} {width})"


def cases():
    for mask in range(16):
        terms = [f"(bvand {a} {b})" for i, (a, b) in enumerate(
            (("(bvnot ra)", "(bvnot rb)"), ("(bvnot ra)", "rb"),
             ("ra", "(bvnot rb)"), ("ra", "rb"))) if mask & (1 << i)]
        yield f"LUT4/{mask}", 1, {"fn": mask}, fold("bvor", terms, bv(0))

    for i, op in enumerate(("bvadd", "bvsub", "bvshl", "bvlshr", "bvashr",
                            "ext_rotate_left", "ext_rotate_right")):
        yield f"ALU/{i}", 2, {"fn": i}, f"({op} ra rb)"

    u16 = "((_ zero_extend 48) ((_ extract 15 0) imm))"
    s16 = u16.replace("zero_extend", "sign_extend")
    count = "((_ zero_extend 58) ((_ extract 5 0) imm))"
    for i, expr in enumerate([f"(bvadd ra {s16})", f"(bvadd ra {u16})",
                              f"(bvxor ra {u16})", f"(bvand ra {u16})",
                              f"(bvor ra {u16})", f"(bvshl ra {count})",
                              f"(bvlshr ra {count})", f"(bvashr ra {count})",
                              f"(ext_rotate_left ra {count})",
                              "(concat ((_ extract 47 0) ra) ((_ extract 15 0) imm))"]):
        yield f"ALUI/{i}", 3, {"fn": i}, expr

    for i, expr in enumerate(("((_ zero_extend 44) imm)", "((_ sign_extend 44) imm)",
                              "(bvadd pc (bvshl ((_ sign_extend 44) imm) (_ bv2 64)))")):
        yield f"IMM20/{i}", 4, {"fn": i}, expr

    for f in range(16):
        pred = []
        if f & 1:
            pred.append("(= ra rb)")
        if f & 2:
            pred.append("(bvsgt ra rb)" if f & 4 else "(bvugt ra rb)")
        test = fold("or", pred, "false")
        if f & 8:
            test = f"(not {test})"
        yield f"CMP/{f}", 5, {"flags": f}, f"(ite {test} {bv(1)} {bv(0)})"

    yield "SEL", 6, {"fn": 0}, f"(ite (= rc {bv(0)}) ra rb)"
    for fn in [1, 2]:
        for idx in range(8):
            for length in range(8):
                bits = (length or 8) * 8
                extend = "sign_extend" if fn == 2 else "zero_extend"
                expr = f"(bvlshr ra {bv(8 * idx)})"
                expr = f"((_ {extend} {64-bits}) ((_ extract {bits-1} 0) {expr}))"
                yield f"BEXT{'S' if fn == 2 else 'U'}/{idx}/{length or 8}", 6, {
                    "fn": fn, "flags": length, "byte_idx": idx}, expr
    yield "BSWAP64", 6, {"fn": 3}, fold("concat", [
        f"((_ extract {i+7} {i}) ra)" for i in range(0, 64, 8)], None)


def fold(op, terms, empty):
    if not terms:
        return empty
    result = terms[0]
    for term in terms[1:]:
        result = f"({op} {result} {term})"
    return result


def main():
    for command in (["yosys", "-V"], ["z3", "--version"]):
        print(subprocess.check_output(command, text=True).strip(), flush=True)
    with tempfile.TemporaryDirectory() as tmp:
        netlist = Path(tmp) / "alu.smt2"
        script = (f"read_slang --top {TOP} qsag_ass2_pkg.sv {TOP}.sv; "
                  f"synth -top {TOP} -noabc; check -assert; write_smt2 {netlist}")
        subprocess.run(["yosys", "-Q", "-q", "-m", "slang", "-p", script], cwd=RTL, check=True)
        widths = dict(op=4, fn=4, flags=4, byte_idx=4, imm=20, ra=64, rb=64,
                      rc=64, pc=64, result=64)
        with subprocess.Popen(["z3", "-in"], stdin=subprocess.PIPE,
                              stdout=subprocess.PIPE, text=True) as z3:
            def send(command):
                z3.stdin.write(command + "\n")
                z3.stdin.flush()

            send(netlist.read_text())
            send(f"(declare-const chip |{TOP}_s|)")
            for port, width in widths.items():
                send(f"(define-fun {port} () (_ BitVec {width}) (|{TOP}_n {port}| chip))")
            count = 0
            for name, opcode, fields, expr in cases():
                send("(push)")
                for field, value in dict(op=opcode, **fields).items():
                    send(f"(assert (= {field} {bv(value, widths[field])}))")
                send(f"(assert (distinct result {expr}))")
                send("(check-sat)")
                answer = z3.stdout.readline().strip()
                if answer != "unsat":
                    if answer == "sat":
                        send("(get-value (op fn flags byte_idx imm pc ra rb rc result))")
                    send("(exit)")
                    raise SystemExit(f"{name}: {answer}\n{z3.stdout.read()}")
                print(f"{name} UNSAT", flush=True)
                send("(pop)")
                count += 1
            send("(exit)")
            if z3.wait():
                raise SystemExit("Z3 failed")
            print(f"{count} UNSAT, 0 counterexamples")


if __name__ == "__main__":
    main()
