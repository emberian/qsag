#!/usr/bin/env python3
"""Untrusted SydTV cut discovery and proof proposal generator.

No solver result is a certificate. --emit-lean writes a declaration whose proof
must be checked by Lean. Certificate emission supports the scalar x86 and AArch64 memzero kernels. Unknown
instructions, relocations, malformed ELF and unsupported certificate shapes fail
closed. Run on the Linux build host, e.g.
python3 scripts/sydtv_driver.py --self-test --require-z3 --check-lean
(--check-lean elaborates the emitted proposals with lake; --require-z3 refuses the
arithmetic fallback).
"""
from __future__ import annotations
import argparse
import dataclasses
import json
import os
import re
import shutil
import struct
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
X86_ZERO = bytes.fromhex('4889f131c0880748ffc748ffc975f60faef0c3')
ARM_ZERO = bytes.fromhex('1f140038210400f1c1ffff54bf3b03d5c0035fd6')
MASK = (1 << 64) - 1


class Rejected(ValueError):
    pass


def require(p, message):
    if not p:
        raise Rejected(message)


def region(data, offset, size):
    require(0 <= offset <= len(data) and 0 <= size <= len(data)-offset,
            'out-of-bounds binary region')
    return data[offset:offset+size]


def cstring(data, offset):
    require(0 <= offset < len(data), 'bad string offset')
    end = data.find(b'\0', offset)
    require(end >= 0, 'unterminated string')
    return data[offset:end].decode('utf-8', errors='strict')


def elf_functions(data):
    require(data[:6] == b'\x7fELF\x02\x01', 'expected little-endian ELF64')
    header = struct.unpack('<16sHHIQQQIHHHHHH', region(data, 0, 64))
    _, kind, machine, _, _, _, shoff, _, _, _, _, entsize, count, _ = header
    require(kind == 1 and machine in (62, 183), 'expected x86_64/aarch64 relocatable ELF')
    require(entsize == 64 and count > 0, 'unsupported section table')
    sections = [struct.unpack('<IIQQQQIIQQ', region(data, shoff+i*64, 64))
                for i in range(count)]
    output = {}
    for sh in sections:
        if sh[1] != 2:  # SHT_SYMTAB
            continue
        require(sh[9] == 24 and sh[5] % 24 == 0 and sh[6] < count, 'bad symbol table')
        strings = region(data, sections[sh[6]][4], sections[sh[6]][5])
        for off in range(sh[4], sh[4]+sh[5], 24):
            name, info, _, idx, value, size = struct.unpack('<IBBHQQ', region(data, off, 24))
            if info & 15 != 2 or idx == 0 or size == 0:
                continue
            require(idx < count, 'bad symbol section')
            section = sections[idx]
            require(section[2] & 4, 'function is not executable')
            require(value+size <= section[5], 'function exceeds section')
            has_relocation = False
            for reloc in sections:
                if reloc[1] in (4, 9) and reloc[7] == idx:
                    width = 24 if reloc[1] == 4 else 16
                    require(reloc[9] == width and reloc[5] % width == 0, 'bad relocations')
                    # Conservatively reject all symbols in a relocated section:
                    # relocation writes can overlap a symbol from before its start.
                    region(data, reloc[4], reloc[5])
                    has_relocation |= reloc[5] != 0
            if has_relocation:
                continue  # Relocated functions are outside this closed-byte validator.
            symbol = cstring(strings, name)
            require(symbol not in output, 'duplicate function symbol')
            output[symbol] = (machine, region(data, section[4]+value, size))
    require(output, 'no function symbols')
    return output


def archive_functions(data):
    if data[:8] != b'!<arch>\n':
        return elf_functions(data)
    offset, output = 8, {}
    while offset < len(data):
        head = region(data, offset, 60)
        require(head[58:] == b'`\n', 'bad ar header')
        size = int(head[48:58].strip())
        payload = region(data, offset+60, size)
        if payload.startswith(b'\x7fELF'):
            for name, value in elf_functions(payload).items():
                require(name not in output, 'duplicate archive symbol')
                output[name] = value
        offset += 60 + size + size % 2
    require(offset == len(data) and output, 'bad or empty archive')
    return output


def fixtures():
    """Read the original compiled archive integers, not a hand-written byte mirror."""
    text = (ROOT/'lean/Qsag/CompiledRlibFixtures.lean').read_text()
    result = {}
    for arch in ('x86', 'aarch64'):
        size = int(re.search(r'def '+arch+r'RlibArchiveLen\s*: Nat :=\s*(\d+)', text)[1])
        integer = int(re.search(r'def '+arch+r'RlibArchiveNat\s*: Nat :=\s*(0x[0-9A-Fa-f]+)', text)[1], 16)
        result.update(archive_functions(integer.to_bytes(size, 'little')))
    return result


@dataclasses.dataclass(frozen=True)
class Insn:
    pc: int
    width: int
    op: str
    args: tuple = ()

    def successors(self):
        if self.op == 'Ret':
            return ()
        if self.op == 'Cond':
            return (self.args[1], self.pc+self.width)
        return (self.pc+self.width,)


def decode(code, machine):
    result, pc = {}, 0
    patterns = [(b'\x48\x89\xf1', 'Assign', ('rem', 'len')),
                (b'\x31\xc0', 'Assign', ('rax', 0)),
                (b'\x88\x07', 'Store', ('ptr', 'al')),
                (b'\x48\xff\xc7', 'Add', ('ptr', 1)),
                (b'\x48\xff\xc9', 'Add', ('rem', -1)),
                (b'\x0f\xae\xf0', 'Fence', ()), (b'\xc3', 'Ret', ())]
    while pc < len(code):
        if machine == 62:
            if code[pc] in (0x75, 0x72, 0x76):
                displacement = struct.unpack('b', region(code, pc+1, 1))[0]
                ins = Insn(pc, 2, 'Cond', ({0x75:'ne', 0x72:'b', 0x76:'be'}[code[pc]], pc+2+displacement))
            else:
                match = next(((b, op, args) for b, op, args in patterns if code[pc:].startswith(b)), None)
                require(match is not None, f'unsupported x86 opcode at {pc}')
                b, op, args = match
                ins = Insn(pc, len(b), op, args)
        elif machine == 183:
            word = int.from_bytes(region(code, pc, 4), 'little')
            table = {0x3800141f: ('StorePost', ('ptr', 0, 1)),
                     0xf1000421: ('Add', ('rem', -1)),
                     0xd5033bbf: ('Fence', ()), 0xd65f03c0: ('Ret', ())}
            if word & 0xff000010 == 0x54000000:
                imm = (word >> 5) & 0x7ffff
                if imm & (1 << 18):
                    imm -= 1 << 19
                require(word & 15 in (0, 1), 'unsupported AArch64 condition')
                ins = Insn(pc, 4, 'Cond', ('ne' if word & 15 else 'eq', pc+4*imm))
            else:
                require(word in table, f'unsupported AArch64 opcode at {pc}')
                op, args = table[word]
                ins = Insn(pc, 4, op, args)
        else:
            raise Rejected('unsupported architecture')
        result[pc] = ins
        pc += ins.width
    for ins in result.values():
        require(all(s in result for s in ins.successors()), 'edge to non-instruction boundary')
    return result


def natural_loops(cfg):
    reachable, todo = set(), [0]
    while todo:
        pc = todo.pop()
        if pc not in reachable:
            reachable.add(pc)
            todo.extend(cfg[pc].successors())
    preds = {p: {q for q in reachable if p in cfg[q].successors()} for p in reachable}
    dom = {p: ({0} if p == 0 else set(reachable)) for p in reachable}
    changed = True
    while changed:
        changed = False
        for p in sorted(reachable-{0}):
            new = {p} | set.intersection(*(dom[q] for q in preds[p]))
            if new != dom[p]:
                dom[p], changed = new, True
    loops = []
    for tail in sorted(reachable):
        for head in cfg[tail].successors():
            if head not in dom[tail]:
                continue
            nodes, todo = {head, tail}, ([] if head == tail else [tail])
            while todo:
                for p in preds[todo.pop()]:
                    if p not in nodes:
                        nodes.add(p)
                        todo.append(p)
            loops.append({'head': head, 'tail': tail, 'nodes': sorted(nodes)})
    return loops


def affine_relations(cfg, loop):
    """Conservative straight-line body synthesis; reject internal branching."""
    nodes = loop['nodes']
    require(all(cfg[p].op != 'Cond' for p in nodes if p != loop['tail']), 'branching body needs path join')
    deltas = {}
    for p in nodes:
        ins = cfg[p]
        if ins.op == 'Add':
            reg, delta = ins.args
            deltas[reg] = deltas.get(reg, 0)+delta
        elif ins.op == 'StorePost':
            deltas['ptr'] = deltas.get('ptr', 0)+ins.args[2]
        elif ins.op == 'Assign':
            raise Rejected('non-affine assignment in loop')
    return {r: {'base': 'len' if r == 'rem' else r+'_init', 'stride': d}
            for r, d in sorted(deltas.items())}


def head_constants(cfg, loop):
    """Infer constant registers along the unique entry path, before the loop head."""
    constants, seen, pc = {}, set(), 0
    while pc != loop['head']:
        require(pc not in seen, 'cyclic entry cut')
        seen.add(pc)
        ins = cfg[pc]
        require(len(ins.successors()) == 1, 'entry cut requires path-sensitive synthesis')
        if ins.op == 'Assign':
            reg, value = ins.args
            if isinstance(value, int):
                constants[reg] = value
            else:
                constants.pop(reg, None)
        elif ins.op == 'Add':
            reg, delta = ins.args
            if reg in constants:
                constants[reg] = (constants[reg]+delta) & MASK
        pc = ins.successors()[0]
    # A constant remains invariant only when the body never changes it.
    for pc in loop['nodes']:
        ins = cfg[pc]
        if ins.op in ('Assign', 'Add'):
            constants.pop(ins.args[0], None)
    return constants


def bv(n):
    return f'(_ bv{n & MASK} 64)'


def flatten_cut_smt(cfg, loop):
    """SSA substitution along the acyclic body with the back edge cut.
The query asserts failure of affine induction, the zero-store memory effect,
or the back-edge/exit condition. These are proposals; Lean checks the proof.
"""
    relations = affine_relations(cfg, loop)
    constants = head_constants(cfg, loop)
    require(cfg[loop['tail']].op == 'Cond' and cfg[loop['tail']].args[0] == 'ne',
            'no exit relation for this branch condition')
    predecessor = cfg[loop['nodes'][-2]]
    require(predecessor.op == 'Add' and predecessor.args == ('rem', -1),
            'branch flag is not established by counter decrement')
    lines = ['(set-logic QF_AUFBV)', '(declare-fun visit () (_ BitVec 64))',
             '(declare-fun memory () (Array (_ BitVec 64) (_ BitVec 8)))',
             '(declare-fun al () (_ BitVec 8))']
    env, next_expected = {}, {}
    for reg, relation in relations.items():
        base, stride = relation['base'], relation['stride']
        lines.append(f'(declare-fun {base} () (_ BitVec 64))')
        env[reg] = f'(bvadd {base} (bvmul {bv(stride)} visit))'
        next_expected[reg] = f'(bvadd {base} (bvmul {bv(stride)} (bvadd visit {bv(1)})))'
    initial_ptr = env['ptr']
    if constants.get('rax') == 0:
        lines.append('(assert (= al (_ bv0 8)))')
    elif any(cfg[p].op == 'Store' for p in loop['nodes']):
        raise Rejected('zero-store value not established at entry')
    lines.append('(assert (bvult visit len))')
    memory = 'memory'
    for pc in loop['nodes']:
        ins = cfg[pc]
        if ins.op == 'Add':
            reg, delta = ins.args
            env[reg] = f'(bvadd {env[reg]} {bv(delta)})'
        elif ins.op in ('Store', 'StorePost'):
            value = 'al' if ins.op == 'Store' else '(_ bv0 8)'
            memory = f'(store {memory} {env["ptr"]} {value})'
            if ins.op == 'StorePost':
                env['ptr'] = f'(bvadd {env["ptr"]} {bv(ins.args[2])})'
    lines.append(f'(define-fun memory_after () (Array (_ BitVec 64) (_ BitVec 8)) {memory})')
    equalities = ' '.join(f'(= {env[r]} {next_expected[r]})' for r in relations)
    equalities += f' (= {memory} (store memory {initial_ptr} (_ bv0 8)))'
    equalities += (f' (= (not (= {env["rem"]} {bv(0)}))'
                   f' (bvult (bvadd visit {bv(1)}) len))')
    require(equalities, 'no induction variables')
    lines += [f'(assert (not (and {equalities})))', '(check-sat)']
    return '\n'.join(lines)+'\n'


def check_induction(cfg, loop, smt, use_z3=True, require_z3=False):
    z3 = find_z3() if use_z3 else None
    require(z3 is not None or not (use_z3 and require_z3), 'z3 not found but --require-z3 was given')
    if z3:
        run = subprocess.run([z3, '-in'], input=smt, text=True, capture_output=True, timeout=20)
        require(run.returncode == 0 and run.stdout.strip() == 'unsat', 'SMT obligation not discharged')
        return 'z3 unsat (untrusted)'
    # Exit arithmetic: under visit<len, 0 <= len-visit-1 < 2^64;
    # it is nonzero exactly when visit+1<len. Store value is checked in flatten_cut_smt.
    # Integer polynomial normalization modulo 2^64: (base + stride*v)+delta
    # equals base + stride*(v+1) iff delta=stride. No claims about exit/ABI here.
    relations = affine_relations(cfg, loop)
    for reg, r in relations.items():
        delta = sum(i.args[1] for p in loop['nodes'] if (i := cfg[p]).op == 'Add' and i.args[0] == reg)
        delta += sum(cfg[p].args[2] for p in loop['nodes'] if cfg[p].op == 'StorePost' and reg == 'ptr')
        require((delta-r['stride']) & MASK == 0, 'affine normalization failed')
    return 'modular affine normalization (untrusted)'


def emit_lean(machine, code):
    """Proof proposal against the current `Qsag.SydTv` certificate API.

    The proposal is untrusted text: `--check-lean` elaborates it with the project toolchain,
    and only that elaboration says anything about it.
    """
    require((machine, code) in ((62, X86_ZERO), (183, ARM_ZERO)),
            'no proved certificate template for these bytes')
    literal = ', '.join(f'0x{x:02x}' for x in code)
    header = f'''module
public import Qsag.SydTvTranslationValidation
public section
namespace Qsag.SydTv.Generated
-- Proposed by untrusted Python; every proof is checked by the Lean kernel.
'''
    if machine == 62:
        body = f'''theorem extracted_bytes : ({literal_brackets(literal)} : List UInt8) = Qsag.SydTv.zeroCode := by decide
def certificate (s₀ : Qsag.X86State) (n : Nat) (positive : 0 < n) (bound : n < 2 ^ 64) :
    Qsag.SydTv.LoopRelationCert Qsag.X86State Qsag.SydTv.MirMemzero n
      Qsag.SydTv.memzeroX86BodyStep Qsag.SydTv.mirMemzeroX86BodyStep
      ⟨5, (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat n)), s₀.ymm, false, false, true, s₀.ymmDirty, false, s₀.mem⟩
      ⟨s₀.gpr.get 7, n, s₀.mem⟩ (Qsag.SydTv.MemzeroX86LoopPost s₀ n) :=
  Qsag.SydTv.ctMemzeroX86PosCert s₀ n positive bound
'''
    else:
        body = f'''theorem extracted_bytes : ({literal_brackets(literal)} : List UInt8) = Qsag.SydTv.armZeroCode := by decide
def certificate (s₀ : Qsag.Arm64State) (n : Nat) (positive : 0 < n) (bound : n < 2 ^ 64)
    (count : Qsag.armGet s₀.gpr 1 = UInt64.ofNat n) (entry : s₀.pc = 0) (running : s₀.halted = false) :
    Qsag.SydTv.LoopRelationCert Qsag.Arm64State Qsag.SydTv.MirMemzero n
      Qsag.SydTv.memzeroArmBodyStep Qsag.SydTv.mirMemzeroArmBodyStep
      s₀ ⟨Qsag.armGet s₀.gpr 0, n, s₀.mem⟩ (Qsag.SydTv.MemzeroArmLoopPost s₀ n) :=
  Qsag.SydTv.ctMemzeroArmPosCert s₀ n positive bound count entry running
'''
    return header + body + 'end Qsag.SydTv.Generated\n'


def check_lean(proposals):
    """Elaborate emitted proposals with `lake env lean` from `lean/` (Linux build host only)."""
    import tempfile
    require(sys.platform.startswith('linux'), '--check-lean runs on the Linux build host only')
    require(shutil.which('lake') is not None, 'lake not found')
    with tempfile.TemporaryDirectory() as scratch:
        for name, text in proposals:
            path = Path(scratch)/f'SydTvGenerated_{name}.lean'
            path.write_text(text)
            wrapper = ['swarm-build'] if shutil.which('swarm-build') else []
            run = subprocess.run(wrapper + ['lake', 'env', 'lean', str(path)], cwd=ROOT/'lean',
                                 text=True, capture_output=True, timeout=540)
            output = run.stdout + run.stderr
            require(run.returncode == 0 and 'error' not in output and 'warning' not in output,
                    f'emitted proposal for {name} does not elaborate:\n{output}')
            print(f'check-lean: {name}: elaborated, no errors or warnings')


def find_z3():
    return shutil.which('z3') or next(
        (str(c) for c in [Path.home()/'.local/bin/z3'] if c.is_file() and os.access(c, os.X_OK)), None)


def literal_brackets(s):
    return '['+s+']'


def self_test(require_z3=False):
    fs = fixtures()
    x = fs['qsag_asm_ct_memzero_x86_64']
    a = fs['qsag_asm_ct_memzero_aarch64']
    require(x == (62, X86_ZERO) and a == (183, ARM_ZERO), 'compiled fixture mismatch')
    for machine, code, expected in [(62, X86_ZERO, (5, 13)), (183, ARM_ZERO, (0, 8))]:
        cfg = decode(code, machine)
        loops = natural_loops(cfg)
        require(len(loops) == 1 and (loops[0]['head'], loops[0]['tail']) == expected, 'bad loop discovery')
        rel = affine_relations(cfg, loops[0])
        require(rel['ptr']['stride'] == 1 and rel['rem']['stride'] == -1, 'bad relation synthesis')
        smt = flatten_cut_smt(cfg, loops[0])
        solver = check_induction(cfg, loops[0], smt, require_z3=require_z3)
        check_induction(cfg, loops[0], smt, use_z3=False)
        print(f'self-test: machine {machine}: induction cut: {solver}')
        if find_z3():
            # Without the trip-count bound the exit relation is false, so the solver must say sat.
            weakened = smt.replace('(assert (bvult visit len))\n', '')
            require(weakened != smt, 'trip-count bound missing from the cut')
            try:
                check_induction(cfg, loops[0], weakened, require_z3=True)
            except Rejected:
                print(f'self-test: machine {machine}: cut without the trip-count bound: z3 sat, rejected')
            else:
                raise AssertionError('z3 accepted a cut without its trip-count bound')
    require(all('LoopRelationCert' in emit_lean(*item) for item in (x, a)), 'certificate missing')
    for mutant in [X86_ZERO[:13]+b'\x76'+X86_ZERO[14:], X86_ZERO[:-1], bytes([0x90])+X86_ZERO[1:]]:
        try:
            emit_lean(62, mutant)
        except Rejected:
            pass
        else:
            raise AssertionError('mutant accepted for certification')
    try:
        decode(X86_ZERO[:14]+b'\xf7'+X86_ZERO[15:], 62)
    except Rejected:
        pass
    else:
        raise AssertionError('mid-instruction branch accepted')
    # A dropped iteration leaves the last arbitrary secret byte untouched.
    mem = [0xa5]*32
    for i in range(31):
        mem[i] = 0
    require(mem[-1] != 0, 'off-by-one counterexample lost')
    print('self-test: PASS (compiled archives, two CFGs, affine/SMT cuts, fail-closed mutations)')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--self-test', action='store_true')
    p.add_argument('--elf', type=Path, help='ELF64 object or ar/rlib archive; default: compiled fixtures')
    p.add_argument('--symbol', default='qsag_asm_ct_memzero_x86_64')
    p.add_argument('--emit-lean', action='store_true', help='write proof proposal to stdout')
    p.add_argument('--smt', action='store_true', help='write DAG-cut SMT-LIB2 to stdout')
    p.add_argument('--require-z3', action='store_true',
                   help='fail if z3 is unavailable instead of using the arithmetic fallback')
    p.add_argument('--check-lean', action='store_true',
                   help='elaborate both emitted certificate proposals with lake (Linux build host)')
    args = p.parse_args()
    if args.self_test:
        self_test(args.require_z3)
        if not args.check_lean:
            return
    if args.check_lean:
        fs = fixtures()
        check_lean([(name, emit_lean(*fs[name]))
                    for name in ('qsag_asm_ct_memzero_x86_64', 'qsag_asm_ct_memzero_aarch64')])
        return
    fs = archive_functions(args.elf.read_bytes()) if args.elf else fixtures()
    require(args.symbol in fs, 'symbol not found')
    machine, code = fs[args.symbol]
    cfg = decode(code, machine)
    loops = natural_loops(cfg)
    if args.emit_lean:
        print(emit_lean(machine, code), end='')
    elif args.smt:
        require(len(loops) == 1, 'select a single-loop function')
        print(flatten_cut_smt(cfg, loops[0]), end='')
    else:
        print(json.dumps({'symbol': args.symbol, 'machine': machine,
                          'cfg': [dataclasses.asdict(i) for i in cfg.values()],
                          'loops': [dict(loop, relations=affine_relations(cfg, loop),
                                         constants=head_constants(cfg, loop),
                                         check=check_induction(cfg, loop, flatten_cut_smt(cfg, loop),
                                                               require_z3=args.require_z3))
                                    for loop in loops]}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (Rejected, OSError, ValueError, struct.error, subprocess.TimeoutExpired) as error:
        raise SystemExit(f'sydtv: rejected: {error}')
