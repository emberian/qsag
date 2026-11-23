"""One-step induction on the compact fixed Poseidon lanes and scalar X RAM in the synthesized RTL cone.

The previous architectural bank had no reset value. Relate its arbitrary initial
contents to identical contents in each copy. Preservation for every transition
extends the relation to any number of accepted/rejected, possibly partial writes.
Read addresses are independent symbolic cutpoints at the memory interface.
"""
from pathlib import Path
import subprocess
import time


def run(root, out, timeout, results):
    root, out = Path(root), Path(out)
    top = "qsag_ni_fpga_top"
    sources = (root / "synth/srcs.txt").read_text().splitlines()
    inputs = ("xs_ra select_eng eng_job_state wr_fire op_busy "
              "wr_word wr_strb wr_data").split()

    def net(name, t=0):
        return f"(|xbank_n {name}| s{t})"

    def mem(port, word, t):
        if port == "s":
            return net(f"u_xs.g_lane[0].mem[{word}]",t)
        return extract(net("g_fixed_x.words",t),64*word+63,64*word)

    def extract(name, hi, lo):
        return f"((_ extract {hi} {lo}) {name})"

    def concat(parts):
        value = parts[-1]
        for low in reversed(parts[:-1]):
            value = f"(concat {value} {low})"
        return value

    def prove(name, design, assertion, expected):
        path = out / f"xbank_{name}.smt2"
        path.write_text("(set-logic QF_BV)\n" + design + relation + assertion + "\n(check-sat)\n")
        for solver in ("bitwuzla", "z3"):
            start = time.monotonic()
            res = subprocess.run(["timeout","60s",solver, str(path)], capture_output=True, text=True, timeout=timeout)
            answer = res.stdout.strip()
            passed = answer == expected and res.returncode in (0, 10, 20)
            tag = "PASS" if passed else "FAIL"
            dt = time.monotonic() - start
            results.append((tag, f"xbank_{name}_{solver}", name, expected, answer, dt))
            print(f"[{tag}] xbank {name} ({solver}): {answer} in {dt:.1f}s", flush=True)
            if not passed:
                raise RuntimeError(f"{solver}: {res.stderr or answer}")

    def design(mutant):
        files = list(sources)
        if mutant:
            orig = "rtl/qsag_x_window.sv"
            rtl = (root / orig).read_text()
            needle = "wd[8*(b%4) +: 8]"
            assert rtl.count(needle) == 1
            fault = out / "mut_xbank_byte.sv"
            fault.write_text(rtl.replace(needle, "wd[8*((b+1)%4) +: 8]"))
            files[files.index(orig)] = str(fault)
        smt = out / ("xbank_mut.yosys.smt2" if mutant else "xbank.yosys.smt2")
        # Cut only upstream controls. Retain the actual write decode, every
        # memory instance, scalar output and 768-bit Poseidon operand join.
        commands = [
            "read_verilog -sv " + " ".join(files),
            f"hierarchy -top {top} -chparam PROFILE_COMPACT 1", "proc",
            f"delete -output {top}/o:*",
            "expose -input " + " ".join(f"{top}/w:{n}" for n in inputs),
            f"expose {top}/w:p2_in_state {top}/w:x_scalar",
            "opt_clean", "flatten", "opt_clean", "memory", "opt -full", "dffunmap",
            "rename -top xbank", f"write_smt2 -wires -stbv {smt}",
        ]
        subprocess.run(["yosys", "-q", "-p", "; ".join(commands)], cwd=root, check=True)
        return smt.read_text()

    wa, wd, strobe = (net(n) for n in ("wr_word", "wr_data", "wr_strb"))
    lines = ["(declare-const s0 |xbank_s|)", "(declare-const s1 |xbank_s|)",
             "(assert (|xbank_h| s0))", "(assert (|xbank_h| s1))",
             "(assert (|xbank_t| s0 s1))",
             f"(define-fun writeX () Bool (and {net('wr_fire')} (not {net('op_busy')}) "
             f"(= {extract(wa,9,6)} #x1)))"]
    updates = []
    for word in range(32):
        ref = f"r{word}"
        lines.append(f"(declare-const {ref} (_ BitVec 64))")
        ports = "fs" if word < 12 else "s"
        for port in ports:
            lines.append(f"(assert (= {mem(port, word, 0)} {ref}))")
        octets = []
        for b in range(8):
            addr = 2 * word + b // 4
            bit = b % 4
            enable = f"(and writeX (= {extract(wa,5,0)} (_ bv{addr} 6)) (= {extract(strobe,bit,bit)} #b1))"
            octets.append(f"(ite {enable} {extract(wd,8*bit+7,8*bit)} {extract(ref,8*b+7,8*b)})")
        lines.append(f"(define-fun next{word} () (_ BitVec 64) {concat(octets)})")
        updates.extend(f"(= {mem(p, word, 1)} next{word})" for p in ports)
    relation = "\n".join(lines) + "\n"
    induction = "(assert (not (and " + " ".join(updates) + ")))"
    actual = design(False)
    prove("write_induction", actual, induction, "unsat")

    def read_group(port, width):
        groups = [concat([f"r{i+j}" for j in range(width)]) for i in range(0, 32, width)]
        result = groups[-1]
        bits = (len(groups) - 1).bit_length()
        for i in reversed(range(len(groups)-1)):
            result = f"(ite (= {net('x'+port+'_ra')} (_ bv{i} {bits})) {groups[i]} {result})"
        return result

    # Every individual 256-bit window is a slice of this actual 768-bit join.
    wide = concat([f"r{word}" for word in range(12)])
    observation = (f"(assert (not writeX))\n(assert (not {net('select_eng', 1)}))\n"
                   f"(assert (not (and (= {net('p2_in_state',1)} {wide}) "
                   f"(= {net('x_scalar',1)} {read_group('s',1)}))))")
    prove("registered_operands", actual, observation, "unsat")
    prove("swapped_write_bytes", design(True), induction, "sat")
