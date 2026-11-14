#!/usr/bin/env python3
"""Physical Linux x86-64 differential tests of the Lean byte decoder.

The C runner uses ptrace single stepping: all 16 GPRs, all 16 YMMs, RFLAGS
and shared memory are installed and captured outside the tested instruction
stream. No compiler-generated register setup occurs inside that stream.
All scalar/vector cases compare every GPR (including SP), YMM and the entire
4 KiB scratch page. Arithmetic flags CF/PF/AF/ZF/SF/OF are tracked by the Lean
adapter; only architecturally undefined bits are excluded, never entire cases.
--kernel-elf adds pre-RET kernel comparisons with unrestricted status flags.
VPCLMUL uses the 128-bit AVX encoding, available on EPYC Milan. mmap/mprotect,
ptrace, fork/wait and exit use native Linux syscalls; no instruction emulator.
"""
import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import struct
import subprocess
import tempfile
import time
import re

HARNESS = r'''
#define _GNU_SOURCE
#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/user.h>
#include <sys/uio.h>
#include <sys/mman.h>
#include <signal.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <stdlib.h>

void *alloc_mem(void) {
  void *p = mmap(0,4096,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS|MAP_32BIT,-1,0);
  return p == MAP_FAILED ? 0 : p;
}
int execute(const unsigned char *code, size_t len, unsigned steps,
            uint64_t *g, unsigned char *ymm, uint64_t *flags) {
  if (len > 4096) return -1;
  void *text = mmap(0,4096,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  if (text == MAP_FAILED) return -2;
  memcpy(text,code,len);
  if (mprotect(text,4096,PROT_READ|PROT_EXEC)) { munmap(text,4096); return -3; }
  pid_t pid = fork();
  if (!pid) {
    if (ptrace(PTRACE_TRACEME,0,0,0)) _exit(120);
    raise(SIGSTOP);
    _exit(121);
  }
  int status, result = 0;
  if (pid < 0) { munmap(text,4096); return -4; }
  if (waitpid(pid,&status,0) != pid || !WIFSTOPPED(status)) { result=-5; goto done; }
  if (ptrace(PTRACE_SETOPTIONS,pid,0,PTRACE_O_EXITKILL)) { result=-12; goto done; }
  struct user_regs_struct r;
  unsigned char xs[16384] __attribute__((aligned(64)));
  struct iovec iov = {xs,sizeof xs};
  if (ptrace(PTRACE_GETREGS,pid,0,&r) || ptrace(PTRACE_GETREGSET,pid,(void*)0x202,&iov)) {
    result=-6; goto done;
  }
  if (iov.iov_len < 832) { result=-7; goto done; }
  for (int i=0;i<16;i++) {
    memcpy(xs+160+16*i,ymm+32*i,16);
    memcpy(xs+576+16*i,ymm+32*i+16,16);
  }
  *(uint64_t*)(xs+512) |= 6;
  r.rax=g[0]; r.rcx=g[1]; r.rdx=g[2]; r.rbx=g[3];
  r.rsp=g[4]; r.rbp=g[5]; r.rsi=g[6]; r.rdi=g[7];
  r.r8=g[8]; r.r9=g[9]; r.r10=g[10]; r.r11=g[11];
  r.r12=g[12]; r.r13=g[13]; r.r14=g[14]; r.r15=g[15];
  r.rip=(uintptr_t)text; r.eflags=*flags;
  if (ptrace(PTRACE_SETREGSET,pid,(void*)0x202,&iov) || ptrace(PTRACE_SETREGS,pid,0,&r)) {
    result=-8; goto done;
  }
  for (unsigned i=0;i<steps;i++) {
    if (ptrace(PTRACE_SINGLESTEP,pid,0,0) || waitpid(pid,&status,0)!=pid) { result=-9; goto done; }
    if (!WIFSTOPPED(status) || WSTOPSIG(status)!=SIGTRAP) {
      result=WIFSTOPPED(status) ? -100-WSTOPSIG(status) : -10; goto done;
    }
  }
  iov.iov_len=sizeof xs;
  if (ptrace(PTRACE_GETREGS,pid,0,&r) || ptrace(PTRACE_GETREGSET,pid,(void*)0x202,&iov)) {
    result=-11; goto done;
  }
  g[0]=r.rax; g[1]=r.rcx; g[2]=r.rdx; g[3]=r.rbx;
  g[4]=r.rsp; g[5]=r.rbp; g[6]=r.rsi; g[7]=r.rdi;
  g[8]=r.r8; g[9]=r.r9; g[10]=r.r10; g[11]=r.r11;
  g[12]=r.r12; g[13]=r.r13; g[14]=r.r14; g[15]=r.r15;
  *flags=r.eflags;
  for (int i=0;i<16;i++) {
    memcpy(ymm+32*i,xs+160+16*i,16);
    memcpy(ymm+32*i+16,xs+576+16*i,16);
  }
done:
  kill(pid,SIGKILL); waitpid(pid,&status,0); munmap(text,4096);
  return result;
}
'''


def cases(base, scalar):
    # These bytes, rather than a second implementation of their arithmetic,
    # are supplied unchanged to both the hardware and Lean decoders.
    out = []
    for imm in (0, 1, 7, 8, 9, 15, 16, 31, 255):
        out += [(f'vpslldq/{imm}', bytes.fromhex('c5fd73f9') + bytes([imm]), 1),
                (f'vpsrldq/{imm}', bytes.fromhex('c5fd73d9') + bytes([imm]), 1)]
    for imm in (0, 1, 0x10, 0x11):
        out.append((f'vpclmulqdq/{imm}', bytes.fromhex('c4e37144c2') + bytes([imm]), 1))
    for imm in (0, 1, 0x1b, 0x4e, 0xff):
        out.append((f'vpshufd/{imm}', bytes.fromhex('c5fd70c1') + bytes([imm]), 1))
    out += [('vextracti128/low', bytes.fromhex('c4e37d39c800'), 1),
            ('vextracti128/high', bytes.fromhex('c4e37d39c801'), 1),
            ('vpshufb', bytes.fromhex('c4e27500c2'), 1),
            ('vpxor/register', bytes.fromhex('c5f5efc2'), 1),
            ('vpxor/memory', bytes.fromhex('c5f5ef07'), 1),
            ('vzeroupper', bytes.fromhex('c5f877'), 1),
            ('vzeroall', bytes.fromhex('c5fc77'), 1),
            ('sib/absolute/nonzero-rax', bytes.fromhex('488b0c25') + base.to_bytes(4,'little'), 1),
            ('sib/scaled', bytes.fromhex('488b0c57'), 1),
            ('vector/block', bytes.fromhex('c5f5efc2c5fd73f808c5f877'), 3)]
    if scalar:
        out += [('mul/flags', bytes.fromhex('48f7e1'), 1),
                ('shl/flags', bytes.fromhex('48c1e001'), 1),
                ('shr/flags', bytes.fromhex('48c1e801'), 1),
                ('ror/flags', bytes.fromhex('48c1c801'), 1)]
    for prefix, width in (('48', 64), ('', 32)):
        for name, opcode in (('add', '01c8'), ('adc', '11c8'), ('sub', '29c8'),
                             ('sbb', '19c8'), ('and', '21c8'), ('or', '09c8'),
                             ('xor', '31c8'), ('imul', '0fafc1'), ('bswap', '0fc8')):
            out.append((f'{name}/{width}', bytes.fromhex(prefix+opcode), 1))
        for name, opcode in (('rol', 'c0'), ('ror', 'c8'), ('shl', 'e0'), ('shr', 'e8'), ('sar', 'f8')):
            for count in (0, 1, 2, 31, 32, 63, 64, 65, 255):
                out.append((f'{name}/{width}/{count}', bytes.fromhex(prefix+'c1'+opcode)+bytes([count]), 1))
        for cc in range(16):
            out.append((f'cmov/{width}/{cc}', bytes.fromhex(prefix+'0f')+bytes([0x40+cc, 0xc1]), 1))
    for cc in range(16):
        out.append((f'setcc/{cc}', bytes([0x0f, 0x90+cc, 0xc0]), 1))
        out.append((f'flags/block/{cc}', bytes.fromhex('4801c8')+bytes([0x0f, 0x90+cc, 0xc3]), 2))
    for imm in (0, 1, 16, 17):
        out.append((f'pclmulqdq/{imm}', bytes.fromhex('660f3a44c1')+bytes([imm]), 1))
    out += [('imul/one64', bytes.fromhex('48f7e9'), 1),
            ('imul/one32', bytes.fromhex('f7e9'), 1),
            ('mul/one32', bytes.fromhex('f7e1'), 1),
            ('neg', bytes.fromhex('48f7d8'), 1),
            ('inc', bytes.fromhex('48ffc0'), 1),
            ('dec', bytes.fromhex('48ffc8'), 1),
            ('adcx', bytes.fromhex('66480f38f6c1'), 1),
            ('adox', bytes.fromhex('f3480f38f6c1'), 1),
            ('mulx', bytes.fromhex('c4e2fbf6d9'), 1),
            ('carry/block', bytes.fromhex('4801c84811d84819c8'), 3),
            ('stack/push-pop', bytes.fromhex('50535859'), 4),
            ('stack/frame-scratch', bytes.fromhex('4883ec2048890424488b5c24004883c420'), 4),
            ('stack/push-rsp', bytes.fromhex('5458'), 2),
            ('scratch/vector', bytes.fromhex('c5fe7f4424c0c5fe6f4c24c0c5f877'), 3)]
    return out


def kernel_cases(path, selected=None):
    """Extract retained linked symbols independently of the Lean ELF reader.

    Compare at the pre-RET boundary: RET itself is deliberately excluded,
    because the proof model treats it as a function boundary, not a stack pop.
    """
    data = path.read_bytes()
    if data[:6] != b'\x7fELF\x02\x01':
        raise ValueError('kernel input must be little-endian ELF64')
    shoff = struct.unpack_from('<Q', data, 40)[0]
    size, count = struct.unpack_from('<HH', data, 58)
    sections = [struct.unpack_from('<IIQQQQIIQQ', data, shoff+i*size) for i in range(count)]
    wanted = {'qsag_asm_goldilocks_mul_ct_x86_64', 'qsag_asm_transpose64x256_avx2',
              'qsag_asm_gf2_128_mul_acc_pclmul', 'qsag_asm_gf2_128_mul_acc_vpclmul',
              'qsag_asm_keccak_f1600_avx2_4x'}
    if selected:
        if set(selected) - wanted:
            raise ValueError(f'unknown kernel selections: {set(selected)-wanted}')
        wanted = set(selected)
    found = {}
    for sec in sections:
        if sec[1] != 2:
            continue
        names = sections[sec[6]]
        strings = data[names[4]:names[4]+names[5]]
        for offset in range(sec[4], sec[4]+sec[5], sec[9]):
            nm, info, _, ndx, value, length = struct.unpack_from('<IBBHQQ', data, offset)
            name = strings[nm:strings.find(b'\0', nm)].decode()
            if name not in wanted or info & 15 != 2:
                continue
            text = sections[ndx]
            start = text[4] + value - text[3]
            code = data[start:start+length]
            if not code or code[-1] != 0xc3:
                raise ValueError(f'{name}: expected final near RET')
            found[name] = (f'kernel/{name}', code[:-1], 0)
    if found.keys() != wanted:
        raise ValueError(f'missing kernel symbols: {wanted-found.keys()}')
    return [found[name] for name in sorted(found)]


# The original 82-case seed=0x51a run failed exactly these eight cases.
# Keep inputs explicit so changes to scheduling or PRNG consumption cannot erase them.
RFLAGS_REGRESSIONS = [
    (37, '48f7e1', 0xffffffffffffffff, 0x8000000000000000, 0x203),
    (38, '48c1e001', 0x8000000000000000, 0xffffffff00000000, 0xa42),
    (39, '48c1e801', 0xffffffff00000000, 0xffffffff00000001, 0x202),
    (40, '48c1c801', 0xffffffff00000001, 1, 0xa02),
    (78, '48f7e1', 0, 0xffffffffffffffff, 0xa42),
    (79, '48c1e001', 0xffffffffffffffff, 0x8000000000000000, 0x242),
    (80, '48c1e801', 0x8000000000000000, 0xffffffff00000000, 0x243),
    (81, '48c1c801', 0xffffffff00000000, 0xffffffff00000001, 0x243),
]

# Branch policy is about fixed-work kernels, not public-length APIs or dispatch.
# Every selected symbol still gets divider and control-flow YMM exit checks.
CORE_CT = ('::wipe::ct_', '::bs_gf256_mul_planes_ct', '::bs_gf256_scale_secret_ct',
           '::ct_select_', '::ct_eq', '::ct_inv', '::rlwe_decode_bit_ct',
           '::ct_reduce_mod_q_', '::mod_q_mul', '::mod_q_add', '::mod_q_sub')
STRAIGHT = ('clmul64_portable', 'clmul128_wide_portable', 'clmul256_reduce_0x87',
            'wiedemann_mul_t', 'wiedemann_scale_t', 'tower128_to_poly128_ct',
            'poly128_to_tower128_ct', 'goldilocks_canonicalize_ct',
            'goldilocks_add_ct_portable', 'goldilocks_sub_ct_portable',
            'goldilocks_mul_ct_portable', 'ct_eq_32_portable')


def disassemble_artifact(path):
    """Read ALL executable sections, including .text.* and every archive member.

    Keep duplicate symbol names as separate entries; no dictionary overwrite can
    hide a second definition. objdump must decode x86-64, not silently accept a
    different target or bitcode-only archive.
    """
    output = subprocess.check_output(['objdump', '-d', '-C', '-M', 'intel',
                                      '--no-show-raw-insn', str(path)], text=True)
    if 'file format elf64-x86-64' not in output:
        raise ValueError(f'{path}: expected native x86-64 ELF code')
    functions = []
    current = None
    for line in output.splitlines():
        match = re.match(r'^([0-9a-f]+) <(.+)>:$', line)
        if match:
            current = (match[2], [])
            functions.append(current)
        elif line.startswith('Disassembly of section') or 'file format' in line:
            current = None
        elif current is not None:
            match = re.match(r'^\s*([0-9a-f]+):\s+(\S+)(?:\s+(.*))?$', line)
            if match:
                current[1].append((int(match[1], 16), match[2].lower(), match[3] or ''))
    return functions


def conditional(mnemonic):
    return (mnemonic.startswith('j') and mnemonic not in ('jmp', 'jmpq')) or mnemonic.startswith('loop')


def instruction_gate(symbol, instructions, straight):
    errors = []
    if not instructions:
        return [f'{symbol}: empty code']
    for address, mnemonic, operands in instructions:
        if mnemonic in ('div', 'idiv', 'divq', 'idivq') or mnemonic.startswith(('fdiv', 'vdiv')):
            errors.append(f'{symbol}+{address:x}: divider {mnemonic}')
        if mnemonic in ('(bad)', '.byte'):
            errors.append(f'{symbol}+{address:x}: undecoded instruction')
        if straight and conditional(mnemonic):
            errors.append(f'{symbol}+{address:x}: conditional branch {mnemonic}')
    # Work-list CFG analysis, joining dirty state with OR. A wipe on one path
    # cannot justify a RET reached through another path that bypasses it.
    by_address = {row[0]: i for i, row in enumerate(instructions)}
    pending, visited = [(0, False)], set()
    while pending:
        i, dirty = pending.pop()
        if (i, dirty) in visited:
            continue
        visited.add((i, dirty))
        address, mnemonic, operands = instructions[i]
        dirty = dirty or bool(re.search(r'\bymm[0-9]+\b', operands))
        if mnemonic in ('vzeroupper', 'vzeroall'):
            dirty = False
        if mnemonic.startswith('ret'):
            if dirty:
                errors.append(f'{symbol}+{address:x}: RET with dirty upper YMM')
            continue
        if mnemonic.startswith('call') and dirty:
            errors.append(f'{symbol}+{address:x}: CALL with dirty upper YMM')
        is_jump = conditional(mnemonic) or mnemonic in ('jmp', 'jmpq')
        if is_jump:
            target = re.match(r'([0-9a-f]+)\s', operands)
            target = int(target[1], 16) if target else None
            if target in by_address:
                pending.append((by_address[target], dirty))
            elif dirty:
                errors.append(f'{symbol}+{address:x}: external/indirect exit with dirty upper YMM')
        if mnemonic not in ('jmp', 'jmpq', 'ud2') and i+1 < len(instructions):
            pending.append((i+1, dirty))
    return errors


def gate_teeth():
    """#tooth: assemble real negative controls and feed the SAME disassembler/gate."""
    sources = {
        'div': 'div rcx; ret',
        'jne': 'test rax, rax; jne 1f; nop; 1: ret',
        'dirty': 'vpxor ymm0, ymm0, ymm0; ret',
        'bypass': 'vpxor ymm0, ymm0, ymm0; test rax, rax; jne 1f; vzeroupper; 1: ret',
        'clean': 'vpxor ymm0, ymm0, ymm0; vzeroupper; ret',
    }
    with tempfile.TemporaryDirectory(prefix='isa-ct-tooth-') as directory:
        for name, body in sources.items():
            src, obj = Path(directory)/'tooth.s', Path(directory)/'tooth.o'
            src.write_text('.intel_syntax noprefix\n.text\n.globl tooth\n.type tooth,@function\ntooth:\n'+body+'\n.size tooth,.-tooth\n')
            subprocess.run(['gcc', '-c', str(src), '-o', str(obj)], check=True)
            rows = next(rows for symbol, rows in disassemble_artifact(obj) if symbol == 'tooth')
            errors = instruction_gate('tooth', rows, name != 'bypass')
            expected = {'div': 'divider', 'jne': 'conditional branch', 'dirty': 'dirty upper YMM',
                        'bypass': 'dirty upper YMM'}
            if name == 'clean':
                if errors:
                    raise RuntimeError(f'#tooth clean control rejected: {errors}')
            elif not any(expected[name] in error for error in errors):
                raise RuntimeError(f'#tooth {name} was not caught: {errors}')
    return len(sources)


def whole_artifact_gate(paths):
    """Whole-Artifact Compiled .text Constant-Time Gate.

    This instruction policy does not claim whole-program noninterference:
    public-length loops and dispatch wrappers are not straight-line kernels.
    Inlining is reflected in the emitted symbol inventory, never source counts.
    """
    started = time.monotonic()
    teeth = gate_teeth()
    errors, inventory = [], []
    asm_names, core_names = set(), set()
    import audit_elf_ct as existing
    for path in paths:
        for symbol, rows in disassemble_artifact(path):
            asm = symbol.startswith('qsag_asm_') or 'qsag_asm::' in symbol
            core = 'qsag_core::' in symbol and any(token in symbol for token in CORE_CT)
            if not (asm or core):
                continue
            straight = (core and '::ct_eq_bytes>' not in symbol and '::ct_eq_bytes::' not in symbol) or any(token in symbol for token in STRAIGHT)
            errors.extend(instruction_gate(symbol, rows, straight))
            if symbol.startswith('qsag_asm_'):
                # Existing kernel ABI/taint policy recognizes public loop counters.
                errors.extend(error for error in existing.audit_x86_symbol(
                    symbol, [(m, o) for _, m, o in rows]) if 'branch' in error or 'loop counter' in error)
            (asm_names if asm else core_names).add(symbol)
            inventory.append(dict(artifact=str(path), symbol=symbol, instructions=len(rows),
                                  branch_policy='straight-line' if straight else 'kernel-public-loop' if symbol.startswith('qsag_asm_') else 'public-control-wrapper'))
    required = set(existing.EXPECTED_X86_SYMBOLS + existing.EXPECTED_X86_BITSLICE_SYMBOLS)
    if required - asm_names:
        errors.append(f'missing assembly kernels: {sorted(required-asm_names)}')
    for required_core in ('qsag_core::wipe::ct_eq_bytes32', 'qsag_core::field::tower::bs_gf256_mul_planes_ct'):
        if not any(required_core in name for name in core_names):
            errors.append(f'missing critical CT symbol: {required_core}')
    result = dict(stage='whole-artifact-text-ct', artifacts=[dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
                  symbols=len(inventory), asm_symbols=sum('qsag_asm' in row['symbol'] for row in inventory),
                  core_symbols=sum(row['symbol'] in core_names for row in inventory),
                  instructions=sum(row['instructions'] for row in inventory),
                  teeth=teeth, violations=errors, inventory=inventory,
                  seconds=round(time.monotonic()-started, 3))
    print(json.dumps(result, indent=2))
    if errors:
        raise RuntimeError(f'whole-artifact CT gate failed: {len(errors)} violations')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--count', type=int, default=4096)
    parser.add_argument('--seed', type=int, default=0x51A)
    parser.add_argument('--scalar-probes', action='store_true', help='compatibility: scalar coverage is now always enabled')
    parser.add_argument('--ct-only', action='store_true', help='run only the whole-artifact CT gate')
    parser.add_argument('--ct-artifact', type=Path, action='append', default=[], help='audit every executable symbol in release ELF/rlib (repeatable)')
    parser.add_argument('--kernel-elf', type=Path, help='also compare five current kernel bodies before RET')
    parser.add_argument('--kernel-symbol', action='append', help='explicit kernel subset; default requires all five')
    parser.add_argument('--kernel-rounds', type=int, default=2)
    parser.add_argument('--oracle', type=Path, default=Path(__file__).resolve().parents[1] / 'lean/.lake/build/bin/isa-cosim')
    args = parser.parse_args()
    started = time.monotonic()
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        parser.error('requires physical Linux x86_64 execution')
    if args.ct_only:
        whole_artifact_gate(args.ct_artifact)
        return 0
    if args.count < 1:
        parser.error('--count must be positive')
    if args.kernel_rounds < 1:
        parser.error('--kernel-rounds must be positive')
    flags = next(line.split(':', 1)[1].split() for line in Path('/proc/cpuinfo').read_text().splitlines()
                 if line.split(':', 1)[0].strip() == 'flags')
    for required in ('avx2', 'pclmulqdq', 'bmi2', 'adx'):
        if required not in flags:
            parser.error(f'CPU missing {required}')
    with tempfile.TemporaryDirectory(prefix='isa-cosim-') as directory:
        path = Path(directory)
        (path/'runner.c').write_text(HARNESS)
        subprocess.run(['gcc', '-O2', '-Wall', '-Wextra', '-Werror', '-shared', '-fPIC',
                        '-mavx2', '-mpclmul', '-mvpclmulqdq', '-mbmi2', '-madx',
                        str(path/'runner.c'), '-o', str(path/'runner.so')], check=True)
        lib = ctypes.CDLL(str(path/'runner.so'))
        lib.alloc_mem.restype = ctypes.c_void_p
        base = lib.alloc_mem()
        if not base:
            raise RuntimeError('MAP_32BIT shared memory allocation failed')
        lib.execute.argtypes = [ctypes.c_char_p, ctypes.c_size_t, ctypes.c_uint,
                                ctypes.POINTER(ctypes.c_uint64), ctypes.POINTER(ctypes.c_ubyte),
                                ctypes.POINTER(ctypes.c_uint64)]
        rng = random.Random(args.seed)
        edge = [0, 2**64-1, 2**63, 0xffffffff00000000, 0xffffffff00000001, 1,
                2**63-1, 0x7fffffff, 0x80000000, 0xffffffff, 2**64-2]
        coverage = {}
        instructions_executed = 0
        flag_checks = {name: 0 for name in ('CF', 'PF', 'AF', 'ZF', 'SF', 'OF')}
        flag_bits = dict(zip(flag_checks, (0, 2, 4, 6, 7, 11)))
        mismatches = []
        with subprocess.Popen([str(args.oracle)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              text=True, bufsize=1) as oracle:
            try:
                suite = cases(base, True)
                scheduled = [suite[i % len(suite)] for i in range(args.count)]
                scheduled += [(f'regression/{old}', bytes.fromhex(code), 1) for old, code, _, _, _ in RFLAGS_REGRESSIONS]
                for cc in range(16):
                    for status in range(64):
                        for kind, code in (('cmov64', bytes([0x48, 0x0f, 0x40+cc, 0xc1])),
                                           ('cmov32', bytes([0x0f, 0x40+cc, 0xc1])),
                                           ('setcc', bytes([0x0f, 0x90+cc, 0xc0]))):
                            scheduled.append((f'conditions/{kind}/{cc}/{status}', code, 1))
                if args.kernel_elf:
                    if 'vpclmulqdq' not in flags and (not args.kernel_symbol or 'qsag_asm_gf2_128_mul_acc_vpclmul' in args.kernel_symbol):
                        raise RuntimeError('selected 256-bit VPCLMUL kernel requires CPUID vpclmulqdq; select supported kernels explicitly')
                    scheduled += kernel_cases(args.kernel_elf, args.kernel_symbol) * args.kernel_rounds
                for i, (name, code, steps) in enumerate(scheduled):
                    g = [edge[(i//len(suite)+j) % len(edge)] if i < len(suite)*len(edge) else rng.getrandbits(64) for j in range(16)]
                    g[4], g[7] = base+2048, base
                    if name == 'sib/scaled':
                        g[2] = 3
                    ys = [sum((edge[(i+j+k) % len(edge)] if i < len(suite)*len(edge) else rng.getrandbits(64)) << (64*k)
                              for k in range(4)) for j in range(16)]
                    memory = rng.randbytes(4096)
                    f = 0x202 | (rng.getrandbits(12) & 0x8d5)
                    if name.startswith('conditions/'):
                        status = int(name.rsplit('/', 1)[1])
                        f = 0x202 | sum(((status >> k) & 1) << bit for k, bit in enumerate((0, 2, 4, 6, 7, 11)))
                    if name.startswith('regression/'):
                        _, _, g[0], g[1], f = next(row for row in RFLAGS_REGRESSIONS if name == f'regression/{row[0]}')
                    if name.startswith('kernel/'):
                        memory = rng.randbytes(4096)
                        g[4] = base + 4000
                        if 'goldilocks' in name:
                            g[7], g[6] = rng.getrandbits(64), rng.getrandbits(64)
                        else:
                            g[7], g[6], g[2], g[1] = base, base+1024, base+1536, 2
                    case = dict(insn_bytes_or_kernel=code.hex(), initial_gprs=[f'{v:016x}' for v in g],
                                initial_ymms=[f'{v:064x}' for v in ys], initial_rflags=f'{f:016x}',
                                stack_base=f'{base:016x}', stack_mem=memory.hex())
                    oracle.stdin.write(json.dumps(case)+'\n'); oracle.stdin.flush()
                    line = oracle.stdout.readline()
                    if not line:
                        raise RuntimeError(f'oracle exited at {name}')
                    expected = json.loads(line)
                    if 'error' in expected:
                        raise RuntimeError(f'{name}: {expected["error"]}')
                    if steps and steps != expected['steps']:
                        raise RuntimeError(f'{name}: unexpected model step count')
                    steps = expected['steps']
                    ctypes.memmove(base, memory, len(memory))
                    gs = (ctypes.c_uint64*16)(*g)
                    ym = (ctypes.c_ubyte*512).from_buffer_copy(b''.join(v.to_bytes(32,'little') for v in ys))
                    fs = ctypes.c_uint64(f)
                    status = lib.execute(code, len(code), steps, gs, ym, ctypes.byref(fs))
                    if status:
                        raise RuntimeError(f'{name}: hardware runner error {status}')
                    actual = dict(gprs=[f'{v:016x}' for v in gs],
                                  ymms=[f'{int.from_bytes(bytes(ym[j*32:j*32+32]), "little"):064x}' for j in range(16)],
                                  rflags=f'{fs.value:016x}', stack_mem=ctypes.string_at(base,len(memory)).hex())
                    instructions_executed += steps
                    mask = int(expected['modeled_rflags_mask'], 16)
                    for flag, bit in flag_bits.items():
                        flag_checks[flag] += bool(mask & (1 << bit))
                    differences = [key for key in actual if key != 'rflags' and actual[key] != expected[key]]
                    if (fs.value ^ int(expected['rflags'], 16)) & mask:
                        differences.append('rflags')
                    if differences:
                        mismatches.append(dict(index=i, instruction=name, fields=differences,
                                               input=case, expected=expected, actual=actual))
                    coverage[name] = coverage.get(name,0)+1
            finally:
                oracle.stdin.close()
                oracle.wait(timeout=10)
        print(json.dumps(dict(vectors=len(scheduled), mismatches=len(mismatches), seed=args.seed,
                              coverage=coverage, skipped_rflags_cases=0,
                              instructions_executed=instructions_executed, flag_checks=flag_checks,
                              seconds=round(time.monotonic()-started, 3),
                              host=platform.node(), hypervisor='hypervisor' in flags), indent=2))
        if mismatches:
            print(json.dumps(mismatches[0], indent=2))
            return 1
        if args.ct_artifact:
            whole_artifact_gate(args.ct_artifact)
        return 0


if __name__ == '__main__':
    raise SystemExit(main())
