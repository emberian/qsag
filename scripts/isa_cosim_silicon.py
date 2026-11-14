#!/usr/bin/env python3
"""Physical Linux x86-64 differential tests of the Lean byte decoder.

The C runner uses ptrace single stepping: all 16 GPRs, all 16 YMMs, RFLAGS
and shared memory are installed and captured outside the tested instruction
stream. No compiler-generated register setup occurs inside that stream.
Default coverage is vector/memory instructions, whose RFLAGS are unchanged.
Arithmetic flags are not yet completely modeled by X86State. --scalar-probes
exposes those gaps as failing cases rather than masking mismatched flags.
--kernel-elf adds pre-RET kernel-body comparisons with restricted initial
flags; it does not certify arithmetic flags at intermediate instructions.
"""
import argparse
import ctypes
import json
import os
from pathlib import Path
import platform
import random
import struct
import subprocess
import tempfile

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
        out.append((f'vpclmulqdq/{imm}', bytes.fromhex('c4e37544c2') + bytes([imm]), 1))
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
    return out


def kernel_cases(path):
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--count', type=int, default=2304)
    parser.add_argument('--seed', type=int, default=0x51A)
    parser.add_argument('--scalar-probes', action='store_true')
    parser.add_argument('--kernel-elf', type=Path, help='also compare five current kernel bodies before RET')
    parser.add_argument('--kernel-rounds', type=int, default=2)
    parser.add_argument('--oracle', type=Path, default=Path(__file__).resolve().parents[1] / 'lean/.lake/build/bin/isa-cosim')
    args = parser.parse_args()
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        parser.error('requires physical Linux x86_64 execution')
    if args.count < 1:
        parser.error('--count must be positive')
    if args.kernel_rounds < 1:
        parser.error('--kernel-rounds must be positive')
    flags = next(line.split(':', 1)[1].split() for line in Path('/proc/cpuinfo').read_text().splitlines()
                 if line.split(':', 1)[0].strip() == 'flags')
    for required in ('avx2', 'pclmulqdq', 'vpclmulqdq', 'bmi2', 'adx'):
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
        edge = [0, 2**64-1, 2**63, 0xffffffff00000000, 0xffffffff00000001, 1]
        coverage = {}
        mismatches = []
        with subprocess.Popen([str(args.oracle)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              text=True, bufsize=1) as oracle:
            try:
                suite = cases(base, args.scalar_probes)
                scheduled = [suite[i % len(suite)] for i in range(args.count)]
                if args.kernel_elf:
                    scheduled += kernel_cases(args.kernel_elf) * args.kernel_rounds
                for i, (name, code, steps) in enumerate(scheduled):
                    g = [edge[(i+j) % len(edge)] if i < len(suite)*len(edge) else rng.getrandbits(64) for j in range(16)]
                    g[4], g[7], g[2] = base+2048, base, 3
                    ys = [sum((edge[(i+j+k) % len(edge)] if i < len(suite)*len(edge) else rng.getrandbits(64)) << (64*k)
                              for k in range(4)) for j in range(16)]
                    memory = rng.randbytes(256)
                    f = 0x202 | (rng.getrandbits(1) << 11) | (rng.getrandbits(1) << 6) | rng.getrandbits(1)
                    if name.startswith('kernel/'):
                        memory = rng.randbytes(4096)
                        g[4] = base + 4000
                        # Kernel bodies finish with XOR-zero: unmodeled PF/SF/AF
                        # are initialized to that final silicon value. This
                        # restricts initial flag coverage; scalar probes above
                        # remain necessary and are never masked.
                        f |= 4
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
                    differences = [key for key in actual if actual[key] != expected[key]]
                    if differences:
                        mismatches.append(dict(index=i, instruction=name, fields=differences,
                                               input=case, expected=expected, actual=actual))
                    coverage[name] = coverage.get(name,0)+1
            finally:
                oracle.stdin.close()
                oracle.wait(timeout=10)
        print(json.dumps(dict(vectors=len(scheduled), mismatches=len(mismatches), seed=args.seed,
                              coverage=coverage), indent=2))
        if mismatches:
            print(json.dumps(mismatches[0], indent=2))
            return 1
        return 0


if __name__ == '__main__':
    raise SystemExit(main())
