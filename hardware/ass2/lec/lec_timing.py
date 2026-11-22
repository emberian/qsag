#!/usr/bin/env python3
"""One-step relational invariant on the synthesized core's physical sequencer.

Compare two executions of the same fetched encoding, in the same public
microstep, with unconstrained registers, sponge, arithmetic, CSR values, SRAM
responses and fault inputs. Completion includes traps. Equality of the control
successor on every nonterminal edge extends the result to the whole instruction.
Fetch takes a request and a capture edge on a successful, aligned instruction.
External halt/reset/tamper and differing program paths are outside this property.
"""
from pathlib import Path
import re
import subprocess
import tempfile

TOP = "qsag_ass2_core"
RTL = Path(__file__).resolve().parents[1] / "rtl"
CONTROL = ["phase", "ir", "round_q", "debug_count",
           *["crypto."+name for name in ("phase", "lane", "col", "term", "limb",
                                          "box_step", "group_idx", "doubles",
                                          "round_q", "rc_addr", "mul.mph")]]


def port(name, s):
    return f"(|{TOP}_n {name}| {s})"


def same(a, b):
    return "(and " + " ".join(f"(= {port(n,a)} {port(n,b)})" for n in CONTROL) + ")"


def finished(s):
    return f"(or {port('retire',s)} (distinct {port('trap_cause',s)} #b000))"


def control_model(model):
    """Relax the transition relation by dropping only data-flop updates.

    Each retained conjunct is copied directly from write_smt2. Dropping a
    constraint enlarges the set of possible counterexamples. Do not assume a
    relationship between the two datapaths or a value for disconnected inputs.
    """
    prefix, relation = model.split(f"(define-fun |{TOP}_t|", 1)
    drivers = {}
    for line in relation.splitlines():
        match = re.fullmatch(r"  (\(=.*\)) ; \$driver\$(\S+) .*", line)
        if match and match[2] in CONTROL:
            drivers[match[2]] = match[1]
    if set(drivers) != set(CONTROL):
        raise ValueError(f"unrecognized sequential drivers: {set(CONTROL)-drivers.keys()}")
    return prefix + (f"(define-fun |{TOP}_t| ((state |{TOP}_s|) "
                     f"(next_state |{TOP}_s|)) Bool (and "
                     + " ".join(drivers.values()) + "))\n")


def slice_query(model, assertions):
    """Remove unused SMT definitions before passing the timing cone to Z3."""
    names = lambda text: set(re.findall(r"\|[^|]+\|", text))
    wanted = names(assertions)
    kept = []
    for raw in reversed(model.splitlines()):
        line = raw.partition(";")[0].strip()
        if not line:
            continue
        m = re.match(r"^\((?:define-fun|declare-fun|declare-sort) (\|[^|]+\|)", line)
        if not m:
            raise ValueError(f"unexpected SMT record: {line[:60]}")
        if m[1] in wanted:
            kept.append(line)
            wanted.update(names(line))
    return "\n".join(reversed(kept)) + "\n" + assertions


def main():
    with tempfile.TemporaryDirectory() as tmp:
        net = Path(tmp) / "core.smt2"
        sources = ["qsag_ass2_pkg.sv", *(p.name for p in sorted(RTL.glob("*.sv"))
                                         if p.stem != "qsag_ass2_pkg")]
        script = (f"read_slang --top {TOP} -GDBG_HOLD_CLOCKS=400 {' '.join(sources)}; "
                  f"prep -top {TOP}; memory_map; opt_clean; async2sync; dffunmap; write_smt2 -wires {net}")
        subprocess.run(["yosys","-q","-m","slang","-p",script],cwd=RTL,check=True)
        model = control_model(net.read_text())
        smt = ""
        for state in ("a","b","an","bn"):
            smt += f"(declare-const {state} |{TOP}_s|)\n(assert {port('srst_n',state)})\n"
        smt += f"(assert {same('a','b')})\n"
        # STOP, FETCH and CAPTURE precede the execution of the decoded word.
        smt += f"(assert (bvuge {port('phase','a')} #b011))\n"
        smt += f"(assert (|{TOP}_t| a an))\n(assert (|{TOP}_t| b bn))\n"
        checks = [
            ("invariant hypotheses are satisfiable", "true", "sat"),
            ("same completion edge", f"(xor {finished('a')} {finished('b')})", "unsat"),
            ("same nonterminal successor",
             f"(and (not {finished('a')}) (not {same('an','bn')}))", "unsat")]
        for name, claim, expected in checks:
            query = smt + f"(assert {claim})\n(check-sat)\n"
            result = subprocess.run(["z3","-in"],input=slice_query(model,query),text=True,
                                    capture_output=True,check=True)
            if result.stdout.strip() != expected:
                raise SystemExit(f"{name}: expected {expected}, got {result.stdout} {result.stderr}")
            print(f"{name}: {expected.upper()}",flush=True)


if __name__ == "__main__":
    main()
