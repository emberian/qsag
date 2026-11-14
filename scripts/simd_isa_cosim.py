#!/usr/bin/env python3
"""Release ELF SIMD extraction and native differential tests.

No assembler substitutes are used for kernel tests. --pin refreshes only the
fixtures and coverage certificates in SimdBinaryEquiv.lean. Default mode checks those pinned bytes
against a fresh release static library, then executes the extracted symbols.
All feature probes run in children; unsupported instructions fail the run.
The reference uses polynomial long division, independently of the kernels'
Karatsuba accumulation and two-stage reduction. No timing claim follows from
these functional tests; DOIT/DIT are assumptions of the formal leakage model.
"""
from __future__ import annotations
import argparse
import ctypes
import hashlib
import mmap
import os
from pathlib import Path
import platform
import random
import re
import resource
import shutil
import struct
import subprocess
import sys
import tempfile

from extract_rlib_elf import parse_ar_archive, parse_elf64_object

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean/Qsag/SimdBinaryEquiv.lean'
NAMES = ('gf2_128_mul_acc_pclmul', 'gf2_128_mul_acc_vpclmul', 'transpose64x256_avx2')
EXTRA_NAMES = ('keccak_f1600_avx2_4x', 'keccak_chi_mpc_avx2',
               'gf256_shamir_mul_gfni', 'gf256_shamir_mac_gfni',
               'gf256_shamir_mul_avx2', 'gf256_shamir_mac_avx2',
               'tower128_bdoz_mac_vpclmul', 'tower128_bdoz_mac_pclmul')
MASK64 = (1 << 64) - 1
MASK128 = (1 << 128) - 1


def clmul(a: int, b: int) -> int:
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
    return result


def remainder(p: int) -> int:
    modulus = (1 << 128) | 0x87
    while p.bit_length() > 128:
        p ^= modulus << (p.bit_length() - 129)
    return p


def reduce_two_phase(hi: int, lo: int) -> int:
    t = clmul(hi >> 64, 0x87)
    return lo ^ ((t << 64) & MASK128) ^ clmul((hi & MASK64) ^ (t >> 64), 0x87)


def transpose(rows: list[int]) -> list[int]:
    # Direct bit matrix definition, independent of butterfly implementation.
    return [sum(((rows[4*r+q] >> c) & 1) << r for r in range(64))
            for c in range(64) for q in range(4)]


def extract(target: str) -> dict:
    env = dict(os.environ, CARGO_TARGET_DIR=str(ROOT / 'target'))
    subprocess.run(['cargo', 'rustc', '--release', '-p', 'qsag-asm',
                    '--target', target, '--crate-type', 'staticlib'],
                   cwd=ROOT, env=env, check=True)
    archive = ROOT / 'target' / target / 'release/libqsag_asm.a'
    result = {}
    for member in parse_ar_archive(archive.read_bytes()):
        if member.payload[:4] != b'\x7fELF' or b'qsag_asm_gf2_128_mul_acc' not in member.payload:
            continue
        obj = parse_elf64_object(member.name, member.payload)
        if obj.machine != (62 if target.startswith('x86_64') else 183):
            raise RuntimeError('unexpected ELF machine architecture')
        # Relocations inside executable symbols would make raw execution unsound.
        shoff = struct.unpack_from('<Q', member.payload, 40)[0]
        shnum = struct.unpack_from('<H', member.payload, 60)[0]
        sections = [struct.unpack_from('<IIQQQQIIQQ', member.payload, shoff+64*i)
                    for i in range(shnum)]
        for symbol in obj.qsag_symbols:
            short = symbol.name.removeprefix('qsag_asm_')
            if short not in NAMES + EXTRA_NAMES + ('gf2_128_mul_acc_pmull', 'transpose64x256_neon'):
                continue
            for sh in sections:
                if sh[1] in (4, 9) and sh[7] == symbol.shndx and sh[5]:
                    # A write starting before the symbol can overlap its bytes.
                    # Reject the entire relocated section until widths are modeled.
                    raise RuntimeError(f'{short}: relocation in executable section')
            if short in result:
                raise RuntimeError(f'duplicate symbol {short}')
            result[short] = dict(code=symbol.code, sha256=hashlib.sha256(symbol.code).hexdigest(),
                                 object_sha256=obj.sha256, offset=symbol.value)
    required = NAMES + EXTRA_NAMES if target.startswith('x86_64') else ('gf2_128_mul_acc_pmull', 'transpose64x256_neon')
    if set(result) != set(required):
        raise RuntimeError(f'missing or extra symbols: {set(result)}')
    return result


def transpose_certificates(offsets: list[int]) -> str:
    name = 'transpose64x256_avx2'
    lines = ['-- BEGIN TRANSPOSE CERTIFICATES',
             '-- Generated instruction coverage certificates; each proof checks at most 24 instructions.']
    last = len(offsets)-1
    for start in reversed(range(0, last, 24)):
        end = min(start+24, last)
        lines += ['set_option maxRecDepth 60000 in', 'set_option maxHeartbeats 4000000 in',
                  f'private theorem transpose_suffix_{start} :',
                  f'    checkBoundaries {name}_code {name}_offsets ({name}_offsets.drop {start}) = true := by',
                  f'  change checkBoundaries {name}_code {name}_offsets [' +
                  ', '.join(map(str, offsets[start:])) + '] = true']
        for _ in range(start, end):
            lines += ['  rw [checkBoundaries]', '  apply Bool.and_eq_true_iff.mpr',
                      '  refine ⟨by decide, ?_⟩']
        lines += ['  decide' if end == last else f'  exact transpose_suffix_{end}', '']
    lines += ['theorem compiled_transpose_decodes :',
              f'    accepted {name}_code {name}_offsets = true := by', '  unfold accepted',
              '  exact Bool.and_eq_true_iff.mpr ⟨by decide, transpose_suffix_0⟩',
              '-- END TRANSPOSE CERTIFICATES']
    return '\n'.join(lines)


def pin_or_check(fixtures: dict, pin: bool) -> None:
    source = LEAN.read_text()
    if pin:
        version = subprocess.check_output(['rustc', '-V'], text=True).strip()
        block = ['-- BEGIN RELEASE SIMD FIXTURES', f'-- {version}; release staticlib; thin LTO.',
                 '-- Digests identify symbol bytes and their containing ELF object.',
                 'def bitsliceSourceSha256 : String := "' + hashlib.sha256(
                     (ROOT/'crates/qsag-asm/src/bitslice.rs').read_bytes()).hexdigest() + '"']
        transpose_offsets = None
        for name, f in fixtures.items():
            chunks = [f['code'][i:i+32] for i in range(0, len(f['code']), 32)]
            code_array = '#[' + ', '.join('#[' + ', '.join(str(x) for x in c) + ']' for c in chunks) + ']'
            block += [f'def {name}_code : ByteCode := ⟨{len(f["code"])}, {code_array}⟩']
            if name in NAMES:
                with tempfile.TemporaryDirectory(dir=ROOT/'target') as scratch:
                    raw = Path(scratch)/'kernel.bin'
                    raw.write_bytes(f['code'])
                    dis = subprocess.check_output(['objdump', '-D', '-b', 'binary', '-m', 'i386:x86-64',
                                                   '--insn-width=16', str(raw)], text=True)
                offsets = [int(m[1], 16) for m in re.finditer(r'^\s*([0-9a-f]+):\s+[0-9a-f]{2} ', dis, re.M)]
                offsets.append(len(f['code']))
                if name == 'transpose64x256_avx2':
                    transpose_offsets = offsets
                block += [f'def {name}_offsets : List Nat := [{", ".join(map(str, offsets))}]']
            block += [f'def {name}_hex : String := "{f["code"].hex()}"',
                      f'def {name}_bytes : Array Nat := #[{", ".join(str(x) for x in f["code"])}]',
                      f'def {name}_sha256 : String := "{f["sha256"]}"',
                      f'def {name}_object_sha256 : String := "{f["object_sha256"]}"',
                      f'def {name}_text_offset : Nat := {f["offset"]}']
        block += ['-- END RELEASE SIMD FIXTURES']
        source = re.sub(r'-- BEGIN RELEASE SIMD FIXTURES.*?-- END RELEASE SIMD FIXTURES',
                        '\n'.join(block), source, flags=re.S)
        if transpose_offsets is None:
            raise RuntimeError('transpose coverage was not extracted')
        source = re.sub(r'-- BEGIN TRANSPOSE CERTIFICATES.*?-- END TRANSPOSE CERTIFICATES',
                        lambda _: transpose_certificates(transpose_offsets), source, flags=re.S)
        LEAN.write_text(source)
    match = re.search(r'def bitsliceSourceSha256 : String := "([0-9a-f]+)"', source)
    if not match or match[1] != hashlib.sha256((ROOT/'crates/qsag-asm/src/bitslice.rs').read_bytes()).hexdigest():
        raise RuntimeError('pinned source provenance differs')
    for name, f in fixtures.items():
        for suffix, value in [('hex', f['code'].hex()), ('sha256', f['sha256']), ('object_sha256', f['object_sha256'])]:
            match = re.search(r'def '+name+'_'+suffix+r' : String := "([0-9a-f]+)"', source)
            if not match or match[1] != value:
                raise RuntimeError(f'{name}: pinned {suffix} differs from release ELF')
        match = re.search(r'def '+name+r'_bytes : Array Nat := #\[([^\]]*)\]', source)
        if not match or bytes(int(x.strip()) for x in match[1].split(',')) != f['code']:
            raise RuntimeError(f'{name}: Lean byte array differs from release ELF')
        match = re.search(r'def '+name+r'_code : ByteCode := ⟨(\d+), (#\[.*?\])⟩', source)
        if not match or int(match[1]) != len(f['code']) or bytes(map(int, re.findall(r'\d+', match[2]))) != f['code']:
            raise RuntimeError(f'{name}: chunked Lean bytes differ from release ELF')
        match = re.search(r'def '+name+r'_text_offset : Nat := (\d+)', source)
        if not match or int(match[1]) != f['offset']:
            raise RuntimeError(f'{name}: pinned object offset differs')
        print(f'{name}: {len(f["code"])} bytes sha256={f["sha256"]}', flush=True)


class Native:
    def __init__(self, code: bytes, argc: int):
        self.mem = mmap.mmap(-1, len(code), prot=mmap.PROT_READ | mmap.PROT_WRITE)
        self.mem.write(code)
        address = ctypes.addressof(ctypes.c_char.from_buffer(self.mem))
        libc = ctypes.CDLL(None, use_errno=True)
        libc.mprotect.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int]
        if libc.mprotect(address, len(code), mmap.PROT_READ | mmap.PROT_EXEC):
            raise OSError(ctypes.get_errno(), 'mprotect')
        types = [ctypes.c_void_p] * argc
        self.call = ctypes.CFUNCTYPE(None, *types)(address)


def isolated(label, work):
    sys.stdout.flush()
    pid = os.fork()
    if pid == 0:
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        try:
            work()
        except BaseException:
            import traceback
            traceback.print_exc()
            os._exit(1)
        sys.stdout.flush()
        os._exit(0)
    _, status = os.waitpid(pid, 0)
    if os.WIFSIGNALED(status):
        raise RuntimeError(f'{label}: native child received signal {os.WTERMSIG(status)}')
    if os.WEXITSTATUS(status):
        raise RuntimeError(f'{label}: native comparison failed')


def test_multiply(name: str, code: bytes, cases: int):
    native = Native(code, 4)
    rng = random.Random(0x53494D44)
    edges = [0, 1, 2, 0x87, 1 << 63, 1 << 64, 1 << 127, MASK128]
    pairs = 2 if name.endswith('vpclmul') else 1
    for case in range(cases):
        count = 1 + case % 17
        n = pairs * count
        a = [rng.getrandbits(128) for _ in range(n)]
        b = [rng.getrandbits(128) for _ in range(n)]
        if case < 64:
            a[0], b[0] = edges[case//8], edges[case%8]
        seed = rng.getrandbits(128)
        expected = seed
        for x, y in zip(a, b):
            wide = clmul(x, y)
            assert reduce_two_phase(wide >> 128, wide & MASK128) == remainder(wide)
            expected ^= remainder(wide)
        # Guard both ends of all buffers, including the accumulator.
        def buf(values):
            raw = b'\xa5'*16 + b''.join(x.to_bytes(16, 'little') for x in values) + b'\x5a'*16
            return ctypes.create_string_buffer(raw, len(raw)), raw
        aa, ar = buf(a)
        bb, br = buf(b)
        acc, ac = buf([seed])
        native.call(ctypes.addressof(acc)+16, ctypes.addressof(aa)+16, ctypes.addressof(bb)+16, count)
        assert bytes(acc) == ac[:16] + expected.to_bytes(16, 'little') + ac[-16:], (name, case)
        assert bytes(aa) == ar and bytes(bb) == br, (name, case, 'input corruption')
    print(f'{name}: {cases} native positive-count batches, zero discrepancies', flush=True)


def test_transpose(code: bytes, cases: int):
    native = Native(code, 1)
    rng = random.Random(0x594D4D)
    for case in range(cases):
        rows = [rng.getrandbits(64) for _ in range(256)]
        if case == 0:
            rows = [0]*256
        elif case == 1:
            rows = [MASK64]*256
        elif case < 258:
            rows = [0]*256
            rows[case-2] = 1 << ((case-2)//4)
        raw = b'\xa5'*32 + struct.pack('<256Q', *rows) + b'\x5a'*32
        data = ctypes.create_string_buffer(raw, len(raw))
        expected = transpose(rows)
        native.call(ctypes.addressof(data)+32)
        assert bytes(data) == raw[:32] + struct.pack('<256Q', *expected) + raw[-32:], case
        native.call(ctypes.addressof(data)+32)
        assert bytes(data) == raw, (case, 'involution')
    print(f'transpose64x256_avx2: {cases} native matrices, all 256 lanes agree', flush=True)


def guarded_buffer(raw: bytes):
    """32-byte aligned payload with checked prefix/suffix and stable allocation."""
    storage = ctypes.create_string_buffer(len(raw) + 128)
    address = (ctypes.addressof(storage) + 63) & ~31
    ctypes.memset(address - 32, 0xa5, 32)
    ctypes.memmove(address, raw, len(raw))
    ctypes.memset(address + len(raw), 0x5a, 32)
    def check(expected=raw):
        assert ctypes.string_at(address - 32, 32) == b'\xa5' * 32
        assert ctypes.string_at(address + len(raw), 32) == b'\x5a' * 32
        assert ctypes.string_at(address, len(raw)) == expected
    return storage, address, check


def tower_scale(a, level):
    if level == 0:
        return a & 1
    half = 1 << (level - 1)
    lo, hi = a & ((1 << half) - 1), a >> half
    return hi | ((lo ^ tower_scale(hi, level - 1)) << half)


def tower_mul(a, b, level=3):
    if level == 0:
        return a & b & 1
    half = 1 << (level - 1)
    mask = (1 << half) - 1
    al, ah, bl, bh = a & mask, a >> half, b & mask, b >> half
    p, q = tower_mul(al, bl, level - 1), tower_mul(ah, bh, level - 1)
    r = tower_mul(al ^ ah, bl ^ bh, level - 1)
    return (p ^ q) | ((r ^ p ^ q ^ tower_scale(q, level - 1)) << half)


def affine(byte, matrix):
    return sum(((byte & (matrix >> (8 * (7 - i)) & 255)).bit_count() % 2) << i
               for i in range(8))


def test_extra(name, code, cases):
    rng = random.Random(0x43544d)
    is_avx_mul = name.startswith('gf256') and name.endswith('avx2')
    native = Native(code, 5 if is_avx_mul else (2 if 'f1600' in name else 4))
    tables = b''.join(bytes(affine(x << shift, matrix) for x in range(16)) * 2
                      for matrix in (0x71500A8A86BE78CE, 0xA1E4F8E072A2700C)
                      for shift in (0, 4)) + bytes(range(16)) + bytes(x << 4 for x in range(16))
    lut = guarded_buffer(tables)
    for case in range(cases):
        count = 1 + case % 17
        if name.startswith('gf256'):
            a, b, seed = (rng.randbytes(32 * count) for _ in range(3))
            scalar = rng.randrange(256)
            mac = '_mac_' in name
            expected = bytes((seed[i] ^ tower_mul(a[i], scalar)) if mac else tower_mul(a[i], b[i])
                             for i in range(len(a)))
            out, aa, bb = guarded_buffer(seed), guarded_buffer(a), guarded_buffer(b)
            args = [out[1], aa[1], scalar if mac else bb[1], count]
            if is_avx_mul:
                args.append(lut[1])
            native.call(*args)
            out[2](expected); aa[2](); bb[2](); lut[2]()
        elif name.startswith('tower128'):
            a = [rng.getrandbits(128) for _ in range(2 * count)]
            b = [rng.getrandbits(128) for _ in range(2 * count)]
            expected = [0, 0]
            for i, (x, y) in enumerate(zip(a, b)):
                expected[i % 2] ^= remainder(clmul(x, y))
            pack = lambda xs: b''.join(x.to_bytes(16, 'little') for x in xs)
            out, aa, bb = guarded_buffer(rng.randbytes(32)), guarded_buffer(pack(a)), guarded_buffer(pack(b))
            native.call(out[1], aa[1], bb[1], count)
            out[2](pack(expected)); aa[2](); bb[2]()
        elif 'chi' in name:
            a, b, mask = ([rng.getrandbits(64) for _ in range(20)] for _ in range(3))
            expected = []
            for x in range(5):
                for lane in range(4):
                    j, k, i = 4 * ((x+1)%5) + lane, 4 * ((x+2)%5) + lane, 4*x + lane
                    expected.append(a[i] ^ ((~a[j] & MASK64) & a[k]) ^
                                    (a[j] & b[k]) ^ (b[j] & a[k]) ^ mask[i])
            pack = lambda xs: struct.pack('<20Q', *xs)
            out, aa, bb, mm = (guarded_buffer(pack(xs)) for xs in ([0]*20, a, b, mask))
            native.call(out[1], aa[1], bb[1], mm[1])
            out[2](pack(expected)); aa[2](); bb[2](); mm[2]()
        else:
            # Independent FIPS 202 permutation, applied to each of four interleaved states.
            rc = [0x1,0x8082,0x800000000000808a,0x8000000080008000,0x808b,0x80000001,
                  0x8000000080008081,0x8000000000008009,0x8a,0x88,0x80008009,0x8000000a,
                  0x8000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,
                  0x8000000000008002,0x8000000000000080,0x800a,0x800000008000000a,
                  0x8000000080008081,0x8000000000008080,0x80000001,0x8000000080008008]
            rho = [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14]
            rol = lambda x, n: ((x << n) | (x >> ((64-n)%64))) & MASK64
            values = [rng.getrandbits(64) for _ in range(100)]
            expected = values.copy()
            for lane in range(4):
                a = values[lane::4]
                for r in rc:
                    c = [a[x] ^ a[x+5] ^ a[x+10] ^ a[x+15] ^ a[x+20] for x in range(5)]
                    d = [c[(x-1)%5] ^ rol(c[(x+1)%5], 1) for x in range(5)]
                    b = [0]*25
                    for y in range(5):
                        for x in range(5):
                            b[y + 5*((2*x+3*y)%5)] = rol(a[x+5*y] ^ d[x], rho[x+5*y])
                    a = [b[x+5*y] ^ ((~b[(x+1)%5+5*y] & MASK64) & b[(x+2)%5+5*y])
                         for y in range(5) for x in range(5)]
                    a[0] ^= r
                expected[lane::4] = a
            out = guarded_buffer(struct.pack('<100Q', *values))
            constants = guarded_buffer(struct.pack('<24Q', *rc))
            native.call(out[1], constants[1])
            out[2](struct.pack('<100Q', *expected)); constants[2]()
    print(f'{name}: {cases} independent algebra comparisons; all canaries intact', flush=True)


def test_aarch64(fixtures, cases):
    emulator = shutil.which('qemu-aarch64')
    compiler = shutil.which('aarch64-linux-gnu-gcc')
    if not emulator or not compiler:
        missing = ', '.join(name for name, found in (('qemu-aarch64', emulator),
                           ('aarch64-linux-gnu-gcc', compiler)) if not found)
        print(f'SKIP: AArch64 execution: unavailable {missing}; provenance checked separately')
        return
    # Cross-compiled transport only: Python supplies independent algebra and expected bytes.
    harness = r"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <assert.h>
static const unsigned char multiply_code[] = {MULTIPLY};
static const unsigned char transpose_code[] = {TRANSPOSE};
static void *executable(const void *bytes, size_t n) {
    void *p = mmap(NULL, n, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    assert(p != MAP_FAILED); memcpy(p, bytes, n);
    __builtin___clear_cache(p, (char *)p+n);
    assert(mprotect(p, n, PROT_READ|PROT_EXEC) == 0); return p;
}
int main(void) {
    void (*mul)(void *, const void *, const void *, size_t) = executable(multiply_code, sizeof multiply_code);
    void (*trans)(void *) = executable(transpose_code, sizeof transpose_code);
    uint32_t header[2];
    while (fread(header, sizeof header, 1, stdin) == 1) {
        unsigned char a[2112] __attribute__((aligned(32)));
        unsigned char b[2112] __attribute__((aligned(32)));
        unsigned char out[96] __attribute__((aligned(32)));
        unsigned char aa[2112], bb[2112], oo[96];
        memset(a, 0xa5, sizeof a); memset(b, 0x5a, sizeof b); memset(out, 0xc3, sizeof out);
        size_t n = header[0] == 0 ? header[1]*16 : 2048;
        assert(n <= 2048 && header[0] <= 1 && header[1] > 0);
        assert(fread(a+32, n, 1, stdin) == 1);
        if (header[0] == 0) {
            assert(fread(b+32, n, 1, stdin) == 1);
            assert(fread(out+32, 16, 1, stdin) == 1);
        }
        memcpy(aa, a, sizeof a); memcpy(bb, b, sizeof b); memcpy(oo, out, sizeof out);
        if (header[0] == 0) {
            mul(out+32, a+32, b+32, header[1]);
            assert(memcmp(a, aa, sizeof a) == 0 && memcmp(b, bb, sizeof b) == 0);
            assert(memcmp(out, oo, 32) == 0 && memcmp(out+48, oo+48, 48) == 0);
            assert(fwrite(out+32, 16, 1, stdout) == 1);
        } else {
            trans(a+32);
            assert(memcmp(a, aa, 32) == 0 && memcmp(a+2080, aa+2080, 32) == 0);
            assert(fwrite(a+32, 2048, 1, stdout) == 1);
        }
    }
    return ferror(stdin) || ferror(stdout);
}
"""
    harness = harness.replace('MULTIPLY', ','.join(map(str, fixtures['gf2_128_mul_acc_pmull']['code'])))
    harness = harness.replace('TRANSPOSE', ','.join(map(str, fixtures['transpose64x256_neon']['code'])))
    rng = random.Random(0xAA64)
    requests, expected = bytearray(), bytearray()
    for case in range(cases):
        count = 1 + case % 17
        a, b = ([rng.getrandbits(128) for _ in range(count)] for _ in range(2))
        seed = rng.getrandbits(128)
        result = seed
        for x, y in zip(a, b):
            result ^= remainder(clmul(x, y))
        requests += struct.pack('<II', 0, count)
        requests += b''.join(x.to_bytes(16, 'little') for x in a+b+[seed])
        expected += result.to_bytes(16, 'little')
        rows = [rng.getrandbits(64) for _ in range(256)]
        requests += struct.pack('<II', 1, 1) + struct.pack('<256Q', *rows)
        expected += struct.pack('<256Q', *transpose(rows))
    with tempfile.TemporaryDirectory(prefix='simd-arm-', dir=ROOT/'target') as directory:
        source, binary = Path(directory)/'runner.c', Path(directory)/'runner'
        source.write_text(harness)
        subprocess.run([compiler, '-O2', '-static', '-Wall', '-Wextra', '-Werror',
                        str(source), '-o', str(binary)], check=True)
        actual = subprocess.check_output([emulator, '-cpu', 'max', str(binary)], input=bytes(requests))
    assert actual == expected, 'AArch64 polynomial/transpose discrepancy'
    print(f'AArch64 PMULL and NEON transpose: {cases} cases each; all canaries intact')


def run_rust_test(name):
    result = subprocess.run(['cargo', 'test', '--release', '-p', 'qsag-asm', '--lib',
                             name, '--', '--exact'], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end='', flush=True)
    result.check_returncode()
    if 'test result: ok. 1 passed; 0 failed;' not in result.stdout:
        raise RuntimeError(f'{name}: required production test did not execute exactly once')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pin', action='store_true')
    parser.add_argument('--cases', type=int, default=512)
    args = parser.parse_args()
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        parser.error('requires native Linux x86_64')
    if not __debug__:
        parser.error('Python optimization disables comparisons; run without -O')
    if args.cases < 512:
        parser.error('at least 512 cases are required')
    fixtures = extract('x86_64-unknown-linux-gnu')
    installed = subprocess.check_output(['rustup', 'target', 'list', '--installed'], text=True)
    if 'aarch64-unknown-linux-gnu' not in installed:
        parser.error('required AArch64 target is not installed')
    fixtures.update(extract('aarch64-unknown-linux-gnu'))
    provenance_error = None
    try:
        pin_or_check({k: v for k, v in fixtures.items() if k not in EXTRA_NAMES}, args.pin)
    except RuntimeError as error:
        provenance_error = error
        print(f'FAIL: fixture provenance: {error}; continuing independent execution checks', flush=True)
    # This production Rust test calls the actual public wrapper for every backend
    # at lengths 0, 1, 2, 3, 16, 17, 40, 41. Raw assembly requires positive counts.
    run_rust_test('bitslice::tests::gf2_128_mul_acc_batch_matches_schoolbook_reference_on_every_backend')
    print('production Rust wrapper: n=0 and boundary counts passed', flush=True)
    for name in NAMES[:2]:
        isolated(name, lambda name=name: test_multiply(name, fixtures[name]['code'], args.cases))
    isolated(NAMES[2], lambda: test_transpose(fixtures[NAMES[2]]['code'], args.cases))
    for name in EXTRA_NAMES:
        isolated(name, lambda name=name: test_extra(name, fixtures[name]['code'], args.cases))
    for test in ('gf256_every_simd_tail_matches_portable_and_preserves_sentinels',
                 'tower128_bdoz_2lane_mac_vpclmul_pclmul_wiedemann_parity',
                 'keccak_batch_tails_match_independent_portable_states',
                 'bitsliced_basis_change_matches_scalar_and_tower_mac_matches_wiedemann_at_every_length'):
        run_rust_test('tests::' + test)
    test_aarch64(fixtures, args.cases)
    if provenance_error is not None:
        raise provenance_error
    print('PASS: release bytes pinned; all native differential comparisons passed')


if __name__ == '__main__':
    main()
