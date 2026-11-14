#!/usr/bin/env python3
"""Physical Linux x86-64 differential tests of the shared Lean byte decoder & executor.

The C runner uses ptrace single stepping: all 16 GPRs, all 16 YMMs, RFLAGS,
normalized per-step RIP (pc_trace), and shared memory are installed and captured
outside the tested instruction stream. Hardware steps independently until RIP
reaches the slice boundary (recording normalized RIP after every single step),
so termination, step count, final PC, and every intermediate branch PC are
verified against Lean (`ElfBinaryVerify.decodeX86InstrAt` + `stepX86`) without
relying on oracle-supplied step counts.

All scalar/vector cases compare every GPR (including SP), YMM, per-step PC
trace, and the entire 4 KiB scratch page. Arithmetic flags CF/PF/AF/ZF/SF/OF
are tracked alongside `stepX86` (which `IsaCosim` asserts agrees on all defined
CF/ZF/OF bits without overriding any GPR/YMM/memory/PC output); only
architecturally undefined bits are excluded, never entire cases.
--kernel-elf adds pre-RET kernel comparisons with unrestricted status flags,
relocation/position-independence validation, and independent System V AMD64 ABI
assertions (callee-saved GPRs, RSP, return-slot & below-red-zone canaries, and
clean upper YMM halves).
"""
import argparse
import ctypes
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import random
import re
import struct
import subprocess
import sys
import tempfile
import time

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
int execute(const unsigned char *code, size_t len, unsigned max_steps,
            uint64_t *g, unsigned char *ymm, uint64_t *flags,
            uint64_t *pc_trace, unsigned *out_steps, uint64_t *out_final_pc) {
  if (len > 4095) return -1;
  void *text = mmap(0,4096,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  if (text == MAP_FAILED) return -2;
  memset(text, 0xcc, 4096);
  memcpy(text, code, len);
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
  uintptr_t base_rip = (uintptr_t)text;
  r.rip = base_rip;
  r.eflags = *flags;
  if (ptrace(PTRACE_SETREGSET,pid,(void*)0x202,&iov) || ptrace(PTRACE_SETREGS,pid,0,&r)) {
    result=-8; goto done;
  }
  unsigned step_count = 0;
  while ((uintptr_t)r.rip != base_rip + len) {
    if ((uintptr_t)r.rip < base_rip || (uintptr_t)r.rip > base_rip + len) {
      result = -14; goto done;
    }
    if (step_count >= max_steps) {
      result = -13; goto done;
    }
    if (ptrace(PTRACE_SINGLESTEP,pid,0,0) || waitpid(pid,&status,0)!=pid) { result=-9; goto done; }
    if (!WIFSTOPPED(status) || WSTOPSIG(status)!=SIGTRAP) {
      result=WIFSTOPPED(status) ? -100-WSTOPSIG(status) : -10; goto done;
    }
    if (ptrace(PTRACE_GETREGS,pid,0,&r)) { result=-11; goto done; }
    if ((uintptr_t)r.rip < base_rip || (uintptr_t)r.rip > base_rip + len) {
      result = -14; goto done;
    }
    pc_trace[step_count++] = (uint64_t)((uintptr_t)r.rip - base_rip);
  }
  iov.iov_len=sizeof xs;
  if (ptrace(PTRACE_GETREGSET,pid,(void*)0x202,&iov)) {
    result=-11; goto done;
  }
  g[0]=r.rax; g[1]=r.rcx; g[2]=r.rdx; g[3]=r.rbx;
  g[4]=r.rsp; g[5]=r.rbp; g[6]=r.rsi; g[7]=r.rdi;
  g[8]=r.r8; g[9]=r.r9; g[10]=r.r10; g[11]=r.r11;
  g[12]=r.r12; g[13]=r.r13; g[14]=r.r14; g[15]=r.r15;
  *flags=r.eflags;
  *out_steps = step_count;
  *out_final_pc = (uint64_t)((uintptr_t)r.rip - base_rip);
  for (int i=0;i<16;i++) {
    memcpy(ymm+32*i,xs+160+16*i,16);
    memcpy(ymm+32*i+16,xs+576+16*i,16);
  }
done:
  kill(pid,SIGKILL); waitpid(pid,&status,0); munmap(text,4096);
  return result;
}
'''


def cases(base, scalar, has_vpclmul256=False):
    # Machine-code bytes supplied unchanged to both physical silicon and Lean.
    out = []
    for imm in (0, 1, 7, 8, 9, 15, 16, 31, 255):
        out += [(f'vpslldq/{imm}', bytes.fromhex('c5fd73f9') + bytes([imm]), 1),
                (f'vpsrldq/{imm}', bytes.fromhex('c5fd73d9') + bytes([imm]), 1)]
    for imm in (0, 1, 0x10, 0x11):
        out.append((f'vpclmulqdq/{imm}', bytes.fromhex('c4e37144c2') + bytes([imm]), 1))
        if has_vpclmul256:
            out.append((f'vpclmulqdq256/{imm}', bytes.fromhex('c4e37544c2') + bytes([imm]), 1))
    for imm in (0, 1, 0x1b, 0x4e, 0xff):
        out.append((f'vpshufd/{imm}', bytes.fromhex('c5fd70c1') + bytes([imm]), 1))
    out += [('vextracti128/low', bytes.fromhex('c4e37d39c800'), 1),
            ('vextracti128/high', bytes.fromhex('c4e37d39c801'), 1),
            ('vpshufb', bytes.fromhex('c4e27500c2'), 1),
            ('vpshufb/lane-msb', bytes.fromhex('c4e26d00d1'), 1),
            ('vpxor/register', bytes.fromhex('c5f5efc2'), 1),
            ('vpxor/memory', bytes.fromhex('c5f5ef07'), 1),
            ('vzeroupper', bytes.fromhex('c5f877'), 1),
            ('vzeroall', bytes.fromhex('c5fc77'), 1),
            ('movzx/r64-m8', bytes.fromhex('480fb607'), 1),
            ('movzx/r32-m8', bytes.fromhex('0fb607'), 1),
            ('movzx/rex-sil-m8', bytes.fromhex('480fb637'), 1),
            ('sse/movdqu-load', bytes.fromhex('f30f6f07'), 1),
            ('sse/pcmpeqb', bytes.fromhex('660f74c1'), 1),
            ('sse/pand', bytes.fromhex('660fdbc1'), 1),
            ('sse/pmovmskb', bytes.fromhex('660fd7c1'), 1),
            ('sib/absolute/nonzero-rax', bytes.fromhex('488b0c25') + base.to_bytes(4,'little'), 1),
            ('sib/scaled', bytes.fromhex('488b0c57'), 1),
            ('lea/sib-disp8', bytes.fromhex('488d4457f8'), 1),
            ('storeImm8/mem', bytes.fromhex('c6075a'), 1),
            ('vector/block', bytes.fromhex('c5f5efc2c5fd73f808c5f877'), 3)]
    if scalar:
        out += [('mul/flags', bytes.fromhex('48f7e1'), 1),
                ('shl/flags', bytes.fromhex('48c1e001'), 1),
                ('shr/flags', bytes.fromhex('48c1e801'), 1),
                ('ror/flags', bytes.fromhex('48c1c801'), 1),
                ('shl/d1-64', bytes.fromhex('48d1e0'), 1),
                ('shr/d1-64', bytes.fromhex('48d1e8'), 1),
                ('rol/d1-64', bytes.fromhex('48d1c0'), 1),
                ('ror/d1-64', bytes.fromhex('48d1c8'), 1),
                ('shl/d1-32', bytes.fromhex('d1e0'), 1),
                ('shr/d1-32', bytes.fromhex('d1e8'), 1),
                ('test/64', bytes.fromhex('4885c8'), 1),
                ('test/32', bytes.fromhex('85c8'), 1),
                ('cmp/64', bytes.fromhex('4839c8'), 1),
                ('cmp/32', bytes.fromhex('39c8'), 1),
                ('cmp/imm8-64', bytes.fromhex('4883f801'), 1),
                ('not/64', bytes.fromhex('48f7d0'), 1),
                ('not/32', bytes.fromhex('f7d0'), 1)]
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
    # Convergent branch blocks: both taken and untaken paths finish with eax=0, CF=0, OF=0, ZF=1,
    # so only per-step pc_trace and hardware step count distinguish the taken vs untaken path.
    out += [('jcc/je-convergent', bytes.fromhex('7402909031c0'), 0),
            ('jcc/jne-convergent', bytes.fromhex('7502909031c0'), 0),
            ('jcc/jb-convergent', bytes.fromhex('7202909031c0'), 0),
            ('jcc/jae-convergent', bytes.fromhex('7302909031c0'), 0),
            ('imul/one64', bytes.fromhex('48f7e9'), 1),
            ('imul/one32', bytes.fromhex('f7e9'), 1),
            ('mul/one32', bytes.fromhex('f7e1'), 1),
            ('neg', bytes.fromhex('48f7d8'), 1),
            ('inc', bytes.fromhex('48ffc0'), 1),
            ('dec', bytes.fromhex('48ffc8'), 1),
            ('adcx', bytes.fromhex('66480f38f6c1'), 1),
            ('adox', bytes.fromhex('f3480f38f6c1'), 1),
            ('mulx', bytes.fromhex('c4e2fbf6d9'), 1),
            ('mulx/hi-lo-alias', bytes.fromhex('c4e2f3f6c9'), 1),
            ('mulx/rdx-hi-alias', bytes.fromhex('c4e2ebf6d1'), 1),
            ('mulx/rdx-lo-alias', bytes.fromhex('c4e2ebf6c9'), 1),
            ('carry/block', bytes.fromhex('4801c84811d84819c8'), 3),
            ('stack/push-pop', bytes.fromhex('50535859'), 4),
            ('stack/frame-scratch', bytes.fromhex('4883ec2048890424488b5c24004883c420'), 4),
            ('stack/push-rsp', bytes.fromhex('5458'), 2),
            ('scratch/vector', bytes.fromhex('c5fe7f4424c0c5fe6f4c24c0c5f877'), 3)]
    return out


X86_64_RELOC_WIDTHS = {
    0: 0,   # R_X86_64_NONE
    1: 8,   # R_X86_64_64
    2: 4,   # R_X86_64_PC32
    3: 4,   # R_X86_64_GOT32
    4: 4,   # R_X86_64_PLT32
    9: 4,   # R_X86_64_GOTPCREL
    10: 4,  # R_X86_64_32
    11: 4,  # R_X86_64_32S
    12: 2,  # R_X86_64_16
    13: 2,  # R_X86_64_PC16
    14: 1,  # R_X86_64_8
    15: 1,  # R_X86_64_PC8
    24: 8,  # R_X86_64_PC64
    41: 4,  # R_X86_64_GOTPCRELX
    42: 4,  # R_X86_64_REX_GOTPCRELX
}


def iter_elf_blobs(path: Path):
    raw = path.read_bytes()
    if raw.startswith(b'!<arch>\n'):
        pos = 8
        while pos + 60 <= len(raw):
            hdr = raw[pos:pos+60]
            size = int(hdr[48:58].decode('ascii', errors='replace').strip() or '0')
            body = raw[pos+60:pos+60+size]
            pos += 60 + size + (size % 2)
            if body.startswith(b'\x7fELF'):
                yield body
    else:
        yield raw


def verify_position_independent_closure(name: str, body_without_ret: bytes):
    with tempfile.TemporaryDirectory(prefix='isa-kclosure-') as td:
        bin_path = Path(td) / 'slice.bin'
        bin_path.write_bytes(body_without_ret)
        out = subprocess.check_output(
            ['objdump', '-D', '-b', 'binary', '-m', 'i386:x86-64', '-M', 'intel', str(bin_path)],
            text=True,
        )
    by_addr = set()
    parsed = []
    for line in out.splitlines():
        m = re.match(r'^\s*([0-9a-f]+):\s+[0-9a-f ]+\t\s*(\S+)(?:\s+(.*))?$', line)
        if m:
            addr = int(m.group(1), 16)
            mnem = m.group(2).lower()
            ops = (m.group(3) or '').strip()
            by_addr.add(addr)
            parsed.append((addr, mnem, ops))
    for addr, mnem, ops in parsed:
        if mnem in ('(bad)', '.byte'):
            raise ValueError(f'{name}+{addr:x}: undecoded byte in extracted kernel')
        if 'rip' in ops.lower():
            raise ValueError(f'{name}+{addr:x}: position-dependent RIP-relative access `{mnem} {ops}`')
        if mnem.startswith('call'):
            raise ValueError(f'{name}+{addr:x}: external/internal CALL `{mnem} {ops}` breaks flat closure')
        if conditional(mnem) or mnem in ('jmp', 'jmpq'):
            m_tgt = re.match(r'^(?:0x)?([0-9a-f]+)\b', ops)
            if not m_tgt:
                raise ValueError(f'{name}+{addr:x}: indirect branch `{mnem} {ops}` in kernel')
            tgt = int(m_tgt.group(1), 16)
            if tgt not in by_addr and tgt != len(body_without_ret):
                raise ValueError(f'{name}+{addr:x}: branch target 0x{tgt:x} escapes kernel closure')


def kernel_cases(path, selected=None):
    """Extract retained ELF symbols with full machine, executable, duplicate,
    relocation-overlap, and position-independence validation.

    Compare at the pre-RET boundary: RET itself is deliberately excluded,
    because the small-step model treats it as a function boundary, while
    callee-saved GPRs, RSP, and return-slot integrity are asserted separately.
    """
    wanted = {'qsag_asm_goldilocks_mul_ct_x86_64', 'qsag_asm_transpose64x256_avx2',
              'qsag_asm_gf2_128_mul_acc_pclmul', 'qsag_asm_gf2_128_mul_acc_vpclmul',
              'qsag_asm_keccak_f1600_avx2_4x'}
    if selected:
        if set(selected) - wanted:
            raise ValueError(f'unknown kernel selections: {set(selected)-wanted}')
        wanted = set(selected)
    found = {}
    saw_elf = False
    for data in iter_elf_blobs(path):
        saw_elf = True
        if data[:6] != b'\x7fELF\x02\x01':
            raise ValueError('kernel input must be little-endian ELF64')
        e_type, e_machine = struct.unpack_from('<HH', data, 16)
        if e_type not in (1, 2, 3) or e_machine != 62:
            raise ValueError(f'expected x86-64 ELF64 (EM_X86_64=62), got type={e_type} machine={e_machine}')
        shoff = struct.unpack_from('<Q', data, 40)[0]
        size, count = struct.unpack_from('<HH', data, 58)
        sections = [struct.unpack_from('<IIQQQQIIQQ', data, shoff+i*size) for i in range(count)]

        relocs_by_sec = {}
        for sec in sections:
            sh_type, _, _, _, sh_offset, sh_size, _, sh_info, _, sh_entsize = sec
            if sh_type not in (4, 9) or sh_size == 0:
                continue
            ent = sh_entsize or (24 if sh_type == 4 else 16)
            for roff in range(sh_offset, sh_offset + sh_size, ent):
                r_offset, r_info = struct.unpack_from('<QQ', data, roff)
                r_type = r_info & 0xffffffff
                if r_type not in X86_64_RELOC_WIDTHS:
                    raise ValueError(f'unsupported ELF relocation type {r_type} on section {sh_info}')
                r_width = X86_64_RELOC_WIDTHS[r_type]
                if r_width > 0:
                    relocs_by_sec.setdefault(sh_info, []).append((r_offset, r_offset + r_width))

        for sec in sections:
            if sec[1] != 2 or sec[9] == 0:
                continue
            names = sections[sec[6]]
            strings = data[names[4]:names[4]+names[5]]
            for offset in range(sec[4], sec[4]+sec[5], sec[9]):
                nm, info, _, ndx, value, length = struct.unpack_from('<IBBHQQ', data, offset)
                if ndx == 0 or ndx >= len(sections):
                    continue
                name = strings[nm:strings.find(b'\0', nm)].decode()
                if name not in wanted or info & 15 != 2:
                    continue
                if name in found:
                    raise ValueError(f'duplicate kernel symbol definition: {name}')
                text = sections[ndx]
                if (text[2] & 0x4) == 0:
                    raise ValueError(f'{name}: symbol resides in non-executable section {ndx}')
                sym_sec_off = value - text[3]
                if sym_sec_off < 0 or sym_sec_off + length > text[5]:
                    raise ValueError(f'{name}: symbol range [{sym_sec_off}, {sym_sec_off+length}) out of section bounds')
                # Relocations in ET_REL use section-relative offsets; in ET_EXEC/ET_DYN use virtual addresses.
                sym_rel_lo = sym_sec_off if e_type == 1 else value
                sym_rel_hi = sym_rel_lo + length
                for r_lo, r_hi in relocs_by_sec.get(ndx, []):
                    if r_lo < sym_rel_hi and sym_rel_lo < r_hi:
                        raise ValueError(
                            f'{name}: overlapping relocation [{r_lo:#x}, {r_hi:#x}) intersects symbol [{sym_rel_lo:#x}, {sym_rel_hi:#x})'
                        )
                start = text[4] + sym_sec_off
                code = data[start:start+length]
                if not code or code[-1] != 0xc3:
                    raise ValueError(f'{name}: expected final near RET')
                verify_position_independent_closure(name, code[:-1])
                found[name] = (f'kernel/{name}', code[:-1], 0)
    if not saw_elf:
        raise ValueError(f'{path}: no ELF objects found')
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

CORE_CT = ('::wipe::ct_', '::bs_gf256_mul_planes_ct', '::bs_gf256_scale_secret_ct',
           '::ct_select_', '::ct_eq', '::ct_inv', '::rlwe_decode_bit_ct',
           '::ct_reduce_mod_q_', '::mod_q_mul', '::mod_q_add', '::mod_q_sub')
STRAIGHT = ('clmul64_portable', 'clmul128_wide_portable', 'clmul256_reduce_0x87',
            'wiedemann_mul_t', 'wiedemann_scale_t', 'tower128_to_poly128_ct',
            'poly128_to_tower128_ct', 'goldilocks_canonicalize_ct',
            'goldilocks_add_ct_portable', 'goldilocks_sub_ct_portable',
            'goldilocks_mul_ct_portable', 'ct_eq_32_portable')

VAR_SHIFT_MNEMONICS = {'shl', 'shr', 'sar', 'sal', 'rol', 'ror', 'rcl', 'rcr', 'shld', 'shrd'}
BMI2_VAR_SHIFT_MNEMONICS = {'shlx', 'shrx', 'sarx'}
GATHER_PREFIXES = ('vpgather', 'vgather')
GPR_INDEX_RE = re.compile(
    r'\[[^\]]*(?:\*|\+\s*(?:r(?:[89]|1[0-5])[dwb]?|[er]?[abcd]x|[er]?[sb]p|[er]?[sd]i|[abcd][hl]|spl|bpl|sil|dil)\b)'
)


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
        ops_l = operands.lower()
        if mnemonic in ('div', 'idiv', 'divq', 'idivq') or mnemonic.startswith(('fdiv', 'vdiv')):
            errors.append(f'{symbol}+{address:x}: divider {mnemonic}')
        if mnemonic in ('(bad)', '.byte'):
            errors.append(f'{symbol}+{address:x}: undecoded instruction')
        if mnemonic.startswith(GATHER_PREFIXES):
            errors.append(f'{symbol}+{address:x}: secret-indexed gather {mnemonic}')
        if mnemonic in BMI2_VAR_SHIFT_MNEMONICS:
            errors.append(f'{symbol}+{address:x}: register-variable shift {mnemonic}')
        if mnemonic in VAR_SHIFT_MNEMONICS:
            parts = [p.strip() for p in ops_l.split(',')]
            if len(parts) >= 2 and parts[-1] == 'cl':
                errors.append(f'{symbol}+{address:x}: variable cl shift {mnemonic}')
        if straight:
            if conditional(mnemonic):
                errors.append(f'{symbol}+{address:x}: conditional branch {mnemonic}')
            if mnemonic.startswith('cmov'):
                errors.append(f'{symbol}+{address:x}: unguarded conditional move {mnemonic}')
            if not mnemonic.startswith('lea') and GPR_INDEX_RE.search(ops_l):
                errors.append(f'{symbol}+{address:x}: indexed memory operand `{mnemonic} {operands}`')
        is_ct_kernel = straight or symbol.startswith('qsag_asm_')
        if is_ct_kernel and (mnemonic in ('jmp', 'jmpq') or mnemonic.startswith('call')):
            if not re.match(r'^(?:0x)?[0-9a-f]+\b', ops_l):
                errors.append(f'{symbol}+{address:x}: indirect control transfer `{mnemonic} {operands}`')
    # Work-list CFG analysis, joining dirty state with OR.
    is_ct_kernel = straight or symbol.startswith('qsag_asm_')
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
            target = re.match(r'^(?:0x)?([0-9a-f]+)\b', operands.strip())
            target = int(target[1], 16) if target else None
            if target in by_address:
                pending.append((by_address[target], dirty))
            else:
                if is_ct_kernel or conditional(mnemonic):
                    errors.append(f'{symbol}+{address:x}: unresolved/external jump target `{mnemonic} {operands}`')
                if dirty:
                    errors.append(f'{symbol}+{address:x}: external/indirect exit with dirty upper YMM')
        if mnemonic not in ('jmp', 'jmpq', 'ud2') and i+1 < len(instructions):
            pending.append((i+1, dirty))
    return errors


def gate_teeth():
    """#tooth: assemble real negative controls and feed the SAME disassembler/gate."""
    sources = {
        'div': ('div rcx; ret', True, 'divider'),
        'jne': ('test rax, rax; jne 1f; nop; 1: ret', True, 'conditional branch'),
        'dirty': ('vpxor ymm0, ymm0, ymm0; ret', True, 'dirty upper YMM'),
        'bypass': ('vpxor ymm0, ymm0, ymm0; test rax, rax; jne 1f; vzeroupper; 1: ret', False, 'dirty upper YMM'),
        'tail_dirty': ('vpxor ymm0, ymm0, ymm0; jmp rax', False, 'dirty upper YMM'),
        'var_shift': ('shl rax, cl; ret', True, 'variable cl shift'),
        'bmi2_shift': ('shrx rax, rdi, rcx; ret', True, 'register-variable shift'),
        'gather': ('vpcmpeqd ymm2, ymm2, ymm2; vpxor ymm1, ymm1, ymm1; vpgatherdq ymm0, [rdi+xmm1*8], ymm2; vzeroupper; ret', True, 'gather'),
        'indexed_mem': ('mov rax, [rdi+rax*8]; ret', True, 'indexed memory'),
        'cmov_unguarded': ('cmovne rax, rcx; ret', True, 'conditional move'),
        'indirect_jmp': ('jmp rax', True, 'indirect control transfer'),
        'clean': ('vpxor ymm0, ymm0, ymm0; vzeroupper; ret', True, None),
    }
    with tempfile.TemporaryDirectory(prefix='isa-ct-tooth-') as directory:
        for name, (body, straight, expected) in sources.items():
            src, obj = Path(directory)/'tooth.s', Path(directory)/'tooth.o'
            src.write_text('.intel_syntax noprefix\n.text\n.globl tooth\n.type tooth,@function\ntooth:\n'+body+'\n.size tooth,.-tooth\n')
            subprocess.run(['gcc', '-mavx2', '-mbmi2', '-c', str(src), '-o', str(obj)], check=True)
            rows = next(rows for symbol, rows in disassemble_artifact(obj) if symbol == 'tooth')
            errors = instruction_gate('tooth', rows, straight)
            if expected is None:
                if errors:
                    raise RuntimeError(f'#tooth clean control rejected: {errors}')
            elif not any(expected in error for error in errors):
                raise RuntimeError(f'#tooth {name} was not caught: {errors}')
    return len(sources)


def whole_artifact_gate(paths):
    """Whole-Artifact Compiled .text Constant-Time Gate.

    Propagates 100% of `audit_elf_ct.audit_x86_symbol` diagnostics on every
    `qsag_asm_*` symbol without filtering, plus CFG upper-YMM, divider,
    variable-shift, gather, indirect-branch, and straight-line address/CMOV
    checks across all selected symbols.
    """
    started = time.monotonic()
    teeth = gate_teeth()
    errors, inventory = [], []
    asm_names, core_names = set(), set()
    sys.path.insert(0, str(Path(__file__).resolve().parent))
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
                errors.extend(existing.audit_x86_symbol(
                    symbol, [(m, re.sub(r'\s+(?:#\s|//).*$', '', re.sub(r'\s+<.+>$', '', o)).strip()) for _, m, o in rows]
                ))
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


CALLEE_SAVED_GPR_INDICES = (3, 5, 12, 13, 14, 15)  # rbx, rbp, r12..r15


def check_kernel_abi_obligations(name: str, init_gprs, actual_gprs, actual_ymms_raw, init_mem: bytes, actual_mem: bytes):
    violations = []
    for idx in CALLEE_SAVED_GPR_INDICES:
        if actual_gprs[idx] != init_gprs[idx]:
            violations.append(f'callee-saved gpr[{idx}] clobbered: {actual_gprs[idx]:016x} != {init_gprs[idx]:016x}')
    if actual_gprs[4] != init_gprs[4]:
        violations.append(f'pre-RET RSP changed: {actual_gprs[4]:016x} != {init_gprs[4]:016x}')
    # RSP = base + 3968: [3968:3976) is return-address slot, [3976:4096) is caller frame.
    # Frameless leaf kernels may use at most the 128B System V red zone [3840:3968);
    # `keccak_f1600_avx2_4x` allocates `push rbp; and rsp,-32; sub rsp,0x340` ([3104:3968))
    # and must zeroize its 800B spilled state [3104:3904) while never touching below min_rsp-128.
    if actual_mem[3968:3976] != init_mem[3968:3976]:
        violations.append('return-address slot [rsp, rsp+8) overwritten')
    if actual_mem[3976:4096] != init_mem[3976:4096]:
        violations.append('caller stack frame [rsp+8, end) overwritten')
    if 'keccak_f1600_avx2_4x' in name:
        if actual_mem[2048:2976] != init_mem[2048:2976]:
            violations.append('stack write below allocated frame + 128B red zone [2048, min_rsp-128)')
        if any(actual_mem[3104:3904]):
            violations.append('spilled Keccak stack frame [min_rsp, min_rsp+800) not zeroized before RET')
    else:
        if actual_mem[2048:3840] != init_mem[2048:3840]:
            violations.append('stack write below 128B System V red zone [2048, rsp-128)')
    for j in range(16):
        upper = bytes(actual_ymms_raw[j*32+16:j*32+32])
        if any(upper):
            violations.append(f'dirty upper YMM{j} at pre-RET: {upper.hex()}')
    return violations


def abi_teeth():
    """#tooth: verify System V AMD64 ABI postcondition checker catches all 5 ABI violations."""
    g0 = [0x1111 * (k + 1) for k in range(16)]
    mem0 = bytes((k & 0xff) for k in range(4096))
    ym0 = bytearray(512)
    if check_kernel_abi_obligations('clean', g0, list(g0), ym0, mem0, mem0):
        raise RuntimeError('#tooth clean ABI state rejected')
    g_rbx = list(g0); g_rbx[3] ^= 1
    assert any('callee-saved gpr[3]' in e for e in check_kernel_abi_obligations('rbx', g0, g_rbx, ym0, mem0, mem0))
    g_rsp = list(g0); g_rsp[4] -= 8
    assert any('pre-RET RSP changed' in e for e in check_kernel_abi_obligations('rsp', g0, g_rsp, ym0, mem0, mem0))
    m_ret = bytearray(mem0); m_ret[3968] ^= 0xff
    assert any('return-address slot' in e for e in check_kernel_abi_obligations('ret', g0, list(g0), ym0, mem0, bytes(m_ret)))
    m_rz = bytearray(mem0); m_rz[3800] ^= 0xff
    assert any('below 128B System V red zone' in e for e in check_kernel_abi_obligations('rz', g0, list(g0), ym0, mem0, bytes(m_rz)))
    ym_dirty = bytearray(512); ym_dirty[16] = 1
    assert any('dirty upper YMM0' in e for e in check_kernel_abi_obligations('ymm', g0, list(g0), ym_dirty, mem0, mem0))


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
    abi_teeth()
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
    has_vpclmul256 = 'vpclmulqdq' in flags
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
        lib.execute.argtypes = [
            ctypes.c_char_p, ctypes.c_size_t, ctypes.c_uint,
            ctypes.POINTER(ctypes.c_uint64), ctypes.POINTER(ctypes.c_ubyte),
            ctypes.POINTER(ctypes.c_uint64),
            ctypes.POINTER(ctypes.c_uint64), ctypes.POINTER(ctypes.c_uint),
            ctypes.POINTER(ctypes.c_uint64),
        ]
        rng = random.Random(args.seed)
        edge = [0, 2**64-1, 2**63, 0xffffffff00000000, 0xffffffff00000001, 1,
                2**63-1, 0x7fffffff, 0x80000000, 0xffffffff, 2**64-2]
        coverage = {}
        instructions_executed = 0
        abi_checks = 0
        flag_checks = {name: 0 for name in ('CF', 'PF', 'AF', 'ZF', 'SF', 'OF')}
        flag_bits = dict(zip(flag_checks, (0, 2, 4, 6, 7, 11)))
        mismatches = []
        max_trace = 100000
        pc_buf = (ctypes.c_uint64 * max_trace)()
        with subprocess.Popen([str(args.oracle)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              text=True, bufsize=1) as oracle:
            try:
                suite = cases(base, True, has_vpclmul256=has_vpclmul256)
                # Mandatory baseline: every suite case runs at least once regardless of --count.
                total_base = max(args.count, len(suite))
                scheduled = [suite[i % len(suite)] for i in range(total_base)]
                scheduled += [(f'regression/{old}', bytes.fromhex(code), 1) for old, code, _, _, _ in RFLAGS_REGRESSIONS]
                for br_name, br_hex in (('je', '7402909031c0'), ('jne', '7502909031c0'),
                                        ('jb', '7202909031c0'), ('jae', '7302909031c0')):
                    for fbit in (0, 1):
                        scheduled.append((f'branch-path/{br_name}/{fbit}', bytes.fromhex(br_hex), 0))
                for cc in range(16):
                    for status in range(64):
                        for kind, code in (('cmov64', bytes([0x48, 0x0f, 0x40+cc, 0xc1])),
                                           ('cmov32', bytes([0x0f, 0x40+cc, 0xc1])),
                                           ('setcc', bytes([0x0f, 0x90+cc, 0xc0]))):
                            scheduled.append((f'conditions/{kind}/{cc}/{status}', code, 1))
                if args.kernel_elf:
                    k_syms = args.kernel_symbol
                    if not has_vpclmul256 and k_syms is None:
                        k_syms = ['qsag_asm_goldilocks_mul_ct_x86_64', 'qsag_asm_transpose64x256_avx2',
                                  'qsag_asm_gf2_128_mul_acc_pclmul', 'qsag_asm_keccak_f1600_avx2_4x']
                    elif not has_vpclmul256 and 'qsag_asm_gf2_128_mul_acc_vpclmul' in k_syms:
                        raise RuntimeError('selected 256-bit VPCLMUL kernel requires CPUID vpclmulqdq; select supported kernels explicitly')
                    scheduled += kernel_cases(args.kernel_elf, k_syms) * args.kernel_rounds
                for i, (name, code, steps) in enumerate(scheduled):
                    g = [edge[(i//len(suite)+j) % len(edge)] if i < len(suite)*len(edge) else rng.getrandbits(64) for j in range(16)]
                    g[4], g[7] = base+2048, base
                    if name in ('sib/scaled', 'lea/sib-disp8'):
                        g[2] = 3
                    ys = [sum((edge[(i+j+k) % len(edge)] if i < len(suite)*len(edge) else rng.getrandbits(64)) << (64*k)
                              for k in range(4)) for j in range(16)]
                    memory = rng.randbytes(4096)
                    f = 0x202 | (rng.getrandbits(12) & 0x8d5)
                    if name.startswith('branch-path/'):
                        _, br_kind, fbit_s = name.split('/')
                        fbit = int(fbit_s)
                        if br_kind in ('je', 'jne'):
                            f = 0x202 | (0x40 if fbit else 0)
                        else:
                            f = 0x202 | (0x01 if fbit else 0)
                    if name.startswith('conditions/'):
                        status = int(name.rsplit('/', 1)[1])
                        f = 0x202 | sum(((status >> k) & 1) << bit for k, bit in enumerate((0, 2, 4, 6, 7, 11)))
                    if name.startswith('regression/'):
                        _, _, g[0], g[1], f = next(row for row in RFLAGS_REGRESSIONS if name == f'regression/{row[0]}')
                    if name.startswith('kernel/'):
                        memory = rng.randbytes(4096)
                        g[4] = base + 3968  # 16-byte aligned RSP with return-slot & red-zone canaries
                        # System V AMD64 ABI entry: clean upper YMM[255:128], arbitrary caller XMM[127:0]
                        ys = [rng.getrandbits(128) for _ in range(16)]
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
                    ctypes.memmove(base, memory, len(memory))
                    gs = (ctypes.c_uint64*16)(*g)
                    ym = (ctypes.c_ubyte*512).from_buffer_copy(b''.join(v.to_bytes(32,'little') for v in ys))
                    fs = ctypes.c_uint64(f)
                    hw_steps = ctypes.c_uint(0)
                    hw_final_pc = ctypes.c_uint64(0)
                    status = lib.execute(code, len(code), max_trace, gs, ym, ctypes.byref(fs),
                                         pc_buf, ctypes.byref(hw_steps), ctypes.byref(hw_final_pc))
                    if status:
                        raise RuntimeError(f'{name}: hardware runner error {status}')
                    actual_mem_bytes = ctypes.string_at(base, len(memory))
                    actual = dict(
                        steps=int(hw_steps.value),
                        final_pc=f'{hw_final_pc.value:016x}',
                        pc_trace=[f'{pc_buf[k]:016x}' for k in range(hw_steps.value)],
                        gprs=[f'{v:016x}' for v in gs],
                        ymms=[f'{int.from_bytes(bytes(ym[j*32:j*32+32]), "little"):064x}' for j in range(16)],
                        rflags=f'{fs.value:016x}',
                        stack_mem=actual_mem_bytes.hex(),
                    )
                    instructions_executed += int(hw_steps.value)
                    mask = int(expected['modeled_rflags_mask'], 16)
                    for flag, bit in flag_bits.items():
                        flag_checks[flag] += bool(mask & (1 << bit))
                    differences = [key for key in ('steps', 'final_pc', 'pc_trace', 'gprs', 'ymms', 'stack_mem')
                                   if actual[key] != expected[key]]
                    if (fs.value ^ int(expected['rflags'], 16)) & mask:
                        differences.append('rflags')
                    if name.startswith('kernel/'):
                        abi_checks += 1
                        abi_errs = check_kernel_abi_obligations(name, g, list(gs), ym, memory, actual_mem_bytes)
                        if abi_errs:
                            differences.append(f'abi:{abi_errs}')
                    if differences:
                        mismatches.append(dict(index=i, instruction=name, fields=differences,
                                               input=case, expected=expected, actual=actual))
                    coverage[name] = coverage.get(name,0)+1
            finally:
                oracle.stdin.close()
                oracle.wait(timeout=10)
        print(json.dumps(dict(vectors=len(scheduled), mismatches=len(mismatches), seed=args.seed,
                              coverage=coverage, skipped_rflags_cases=0,
                              instructions_executed=instructions_executed,
                              abi_kernel_checks=abi_checks,
                              flag_checks=flag_checks,
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
