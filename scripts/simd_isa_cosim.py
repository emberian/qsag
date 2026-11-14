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
import struct
import subprocess
import sys
import tempfile

from extract_rlib_elf import parse_ar_archive, parse_elf64_object

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean/Qsag/SimdBinaryEquiv.lean'
NAMES = ('gf2_128_mul_acc_pclmul', 'gf2_128_mul_acc_vpclmul', 'transpose64x256_avx2')
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
            if short not in NAMES + ('gf2_128_mul_acc_pmull', 'transpose64x256_neon'):
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
    required = NAMES if target.startswith('x86_64') else ('gf2_128_mul_acc_pmull', 'transpose64x256_neon')
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
        types = [ctypes.c_void_p] * min(argc, 3) + ([ctypes.c_size_t] if argc == 4 else [])
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
    pin_or_check(fixtures, args.pin)
    # This production Rust test calls the actual public wrapper for every backend
    # at lengths 0, 1, 2, 3, 16, 17, 40, 41. Raw assembly requires positive counts.
    subprocess.run(['cargo', 'test', '--release', '-p', 'qsag-asm', '--lib',
                    'bitslice::tests::gf2_128_mul_acc_batch_matches_schoolbook_reference_on_every_backend',
                    '--', '--exact'], cwd=ROOT, check=True)
    print('production Rust wrapper: n=0 and boundary counts passed', flush=True)
    for name in NAMES[:2]:
        isolated(name, lambda name=name: test_multiply(name, fixtures[name]['code'], args.cases))
    isolated(NAMES[2], lambda: test_transpose(fixtures[NAMES[2]]['code'], args.cases))
    print('PASS: release bytes pinned; all native differential comparisons passed')


if __name__ == '__main__':
    main()
