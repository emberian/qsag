#!/usr/bin/env python3
"""Inductive relational constant-time proof (`DIT = 1`) on `qsag_ass2_core`.

Compares two executions of the same fetched instruction (`u_ir.q`) across all
reachable microarchitectural steps (`CAPTURE -> CAP_A -> ... -> retire / trap`),
leaving registers, sponge lanes, ALU/crypto operands, CSR data, and memory read
data completely unconstrained between the two executions. External `dbg_halt_i`,
reset/tamper, and `mem_ready_i` / `mem_fault_i` bus handshakes are public
environmental inputs shared between the two lockstep traces.

Z3 formally verifies:
  1. Inductive structural control invariant (`inv`) from `CAPTURE` entry,
  2. Identical completion edge (`finished(a) <=> finished(b)`), and
  3. Identical nonterminal control successor (`same(an, bn)`), including the
     public Grain LFSR state during `POSEIDON2.GL24`.
"""
from pathlib import Path
import re
import subprocess
import tempfile

TOP = "qsag_ass2_core"
RTL = Path(__file__).resolve().parents[1] / "rtl"
ALWAYS_EQ = [
    "phase", "u_ir.q", "crypto_kicked_q",
    "crypto.phase", "crypto.lane_ready_q", "crypto.add_stage_q", "crypto.mul.step_q"
]
CRYPTO_EQ = [
    "crypto." + name for name in (
        "ret_phase", "lane", "col", "gf_cnt", "term", "limb",
        "box_step", "group_idx", "doubles", "round_q", "sbox_cnt", "w12_pass"
    )
]
DRIVERS = [*ALWAYS_EQ, "legal_q", *CRYPTO_EQ, "crypto.u_grain.q"]
SHARED_INPUTS = ["dbg_halt_i", "mem_ready_i", "mem_fault_i", "mem_aligned", "applet_exec_i"]


def port(name, s):
    return f"(|{TOP}_n {name}| {s})"


def is_p2_gl24(s):
    ir = port("u_ir.q", s)
    return f"(and (= ((_ extract 31 28) {ir}) #xf) (= ((_ extract 19 16) {ir}) #x1))"


def inv(s):
    ph = port("phase", s)
    ir = port("u_ir.q", s)
    op = f"((_ extract 31 28) {ir})"
    sub = f"((_ extract 19 16) {ir})"
    cph = port("crypto.phase", s)
    rph = port("crypto.ret_phase", s)
    mst = port("crypto.mul.step_q", s)
    kicked = f"(= {port('crypto_kicked_q', s)} (= {ph} #b1001))"
    crypto_legal = f"(=> (= {ph} #b1001) (and {port('legal_q', s)} {port('is_crypto', s)}))"
    idle_outside = (
        f"(=> (distinct {ph} #b1001) "
        f"(and (= {cph} (_ bv0 6)) (not {port('crypto.lane_ready_q', s)}) "
        f"(= {port('crypto.add_stage_q', s)} #b00) (= {mst} (_ bv0 7))))"
    )
    fold_gl64 = f"(=> (or (= {cph} (_ bv4 6)) (= {cph} (_ bv5 6))) (or (= {rph} (_ bv2 6)) (= {rph} (_ bv7 6)) (= {rph} (_ bv12 6))))"
    fold_box = f"(=> (or (= {cph} (_ bv4 6)) (= {cph} (_ bv5 6))) (= {rph} (_ bv7 6)))"
    alu_set = f"(or (= {cph} (_ bv2 6)) (= {cph} (_ bv3 6)))"
    gl_set = f"(and (bvuge {cph} (_ bv1 6)) (bvule {cph} (_ bv15 6)) {fold_gl64})"
    gf_set = f"(or (= {cph} (_ bv3 6)) (and (bvuge {cph} (_ bv16 6)) (bvule {cph} (_ bv22 6))))"
    k_set = f"(or (= {cph} (_ bv3 6)) (and (bvuge {cph} (_ bv41 6)) (bvule {cph} (_ bv47 6))))"
    p2_24_set = (
        f"(and (or (and (bvuge {cph} (_ bv3 6)) (bvule {cph} (_ bv7 6))) "
        f"         (and (bvuge {cph} (_ bv23 6)) (bvule {cph} (_ bv30 6))) "
        f"         (and (bvuge {cph} (_ bv36 6)) (bvule {cph} (_ bv40 6)))) {fold_box})"
    )
    p2_12_set = (
        f"(and (or (and (bvuge {cph} (_ bv3 6)) (bvule {cph} (_ bv7 6))) "
        f"         (and (bvuge {cph} (_ bv23 6)) (bvule {cph} (_ bv29 6))) "
        f"         (and (bvuge {cph} (_ bv31 6)) (bvule {cph} (_ bv40 6)))) {fold_box})"
    )
    perm_set = f"(ite (= {sub} #x0) {k_set} (ite (= {sub} #x1) {p2_24_set} {p2_12_set}))"
    by_op = (
        f"(=> (= {ph} #b1001) "
        f"(ite (= {op} #x2) {alu_set} "
        f"(ite (= {op} #xd) {gl_set} "
        f"(ite (= {op} #xe) {gf_set} {perm_set}))))"
    )
    mul_bound = f"(bvule {mst} (_ bv65 7))"
    return f"(and {kicked} {crypto_legal} {idle_outside} {by_op} {mul_bound})"


def same(a, b):
    ph = port("phase", a)
    eqs = [f"(= {port(n, a)} {port(n, b)})" for n in ALWAYS_EQ]
    eqs.append(f"(=> (bvuge {ph} #b0100) (= {port('legal_q', a)} {port('legal_q', b)}))")
    for n in CRYPTO_EQ:
        eqs.append(f"(=> (= {ph} #b1001) (= {port(n, a)} {port(n, b)}))")
    eqs.append(
        f"(=> (and (= {ph} #b1001) {is_p2_gl24(a)}) "
        f"(= {port('crypto.u_grain.q', a)} {port('crypto.u_grain.q', b)}))"
    )
    return "(and " + " ".join(eqs) + ")"


def finished(s):
    return f"(or {port('retire', s)} (distinct {port('trap_cause', s)} #b000) {port('dbg_halt_i', s)})"


def control_model(model):
    prefix, relation = model.split(f"(define-fun |{TOP}_t|", 1)
    drivers = {}
    for line in relation.splitlines():
        match = re.fullmatch(r"  (\(=.*\)) ; \$driver\$(\S+) .*", line)
        if match and match[2] in DRIVERS:
            drivers[match[2]] = match[1]
    if set(drivers) != set(DRIVERS):
        raise ValueError(f"unrecognized sequential drivers: {set(DRIVERS) - drivers.keys()} (found {sorted(drivers)})")
    return prefix + (f"(define-fun |{TOP}_t| ((state |{TOP}_s|) "
                     f"(next_state |{TOP}_s|)) Bool (and "
                     + " ".join(drivers.values()) + "))\n")


def slice_query(model, assertions):
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
        script = (f"read_slang --top {TOP} {' '.join(sources)}; "
                  f"prep -top {TOP}; memory_map; opt_clean; async2sync; dffunmap; write_smt2 -wires {net}")
        subprocess.run(["yosys", "-q", "-m", "slang", "-p", script], cwd=RTL, check=True)
        model = control_model(net.read_text())

        base = ""
        for state in ("a", "b", "an", "bn"):
            base += f"(declare-const {state} |{TOP}_s|)\n(assert {port('srst_n', state)})\n"
        for inp in SHARED_INPUTS:
            base += f"(assert (= {port(inp, 'a')} {port(inp, 'b')}))\n"
        base += f"(assert (|{TOP}_t| a an))\n(assert (|{TOP}_t| b bn))\n"

        entry_hyp = (
            f"(and (= {port('phase', 'a')} #b0010) (= {port('phase', 'b')} #b0010) "
            f"(not {port('dbg_halt_i', 'a')}) "
            f"{inv('a')} {inv('b')} "
            f"(= {port('u_ir.q', 'an')} {port('u_ir.q', 'bn')}))"
        )
        step_hyp = (
            f"(and (bvuge {port('phase', 'a')} #b0011) (bvule {port('phase', 'a')} #b1001) "
            f"{inv('a')} {inv('b')} {same('a', 'b')})"
        )

        checks = [
            ("invariant hypotheses are satisfiable", f"{step_hyp}", "sat"),
            ("CAPTURE entry establishes invariant & same(an,bn)",
             f"(and {entry_hyp} (not (and {inv('an')} {inv('bn')} {same('an', 'bn')})))", "unsat"),
            ("inductive invariant preserved across nonterminal steps",
             f"(and {step_hyp} (not {finished('a')}) (not {inv('an')}))", "unsat"),
            ("same completion edge",
             f"(and {step_hyp} (xor {finished('a')} {finished('b')}))", "unsat"),
            ("same nonterminal successor",
             f"(and {step_hyp} (not {finished('a')}) (not {same('an', 'bn')}))", "unsat"),
        ]
        for name, claim, expected in checks:
            query = base + f"(assert {claim})\n(check-sat)\n"
            result = subprocess.run(["z3", "-in"], input=slice_query(model, query), text=True,
                                    capture_output=True, check=True)
            if result.stdout.strip() != expected:
                vals = " ".join(f"{port(d, st)}" for st in ("a", "b", "an", "bn")
                                for d in ("phase", "u_ir.q", "legal_q", "mem_aligned", "mem_ready_i", "mem_fault_i", "crypto.phase", "crypto.ret_phase"))
                dbg = subprocess.run(["z3", "-in"], input=slice_query(model, base + f"(assert {claim})\n(check-sat)\n(get-value ({vals}))\n"),
                                     text=True, capture_output=True)
                raise SystemExit(f"{name}: expected {expected}, got:\n{dbg.stdout}\n{dbg.stderr}")
            print(f"{name}: {expected.upper()}", flush=True)


if __name__ == "__main__":
    main()
