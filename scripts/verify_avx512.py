#!/usr/bin/env python3
"""Run production SIMD differential tests with mandatory AVX-512 capabilities.

Linux x86-64 only. Use --runner '/path/to/sde64 -spr --' for software emulation,
or omit it for native hardware. The capability probe executes under the same
runner as the tests and fails instead of accepting a portable backend fallback.
These are functional tests; they do not establish constant-time execution.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TESTS = (
    'tests::keccak_x8_and_batch_tails_match_independent_portable_states',
    'tests::exhaustive_65536_gf256_wiedemann_t3_mul_and_mac_across_all_backends',
    'tests::gf256_every_simd_tail_matches_portable_and_preserves_sentinels',
    'tests::tower128_bdoz_2lane_mac_vpclmul_pclmul_wiedemann_parity',
    'bitslice::tests::gf2_128_mul_acc_batch_matches_schoolbook_reference_on_every_backend',
    'bitslice::tests::polynomial_scale_xor_matches_schoolbook_and_preserves_boundaries',
    'tests::seiler_mldsa_ntt_inv_ntt_and_negacyclic_convolution_parity',
    'tests::sha256_hw_compress_matches_portable_and_nist_vectors',
)
# This checks OS vector state as well as CPUID. Each feature is also required by
# the corresponding production dispatcher; AVX512F alone is insufficient.
PROBE = '''fn main() {
    macro_rules! require { ($feature:tt) => {
        assert!(std::arch::is_x86_feature_detected!($feature),
                "required SIMD feature unavailable: {}", $feature);
        println!("required feature present: {}", $feature);
    }; }
    require!("avx512f"); require!("avx512dq"); require!("avx512bw");
    require!("avx512vl"); require!("gfni"); require!("vpclmulqdq");
    require!("avx2"); require!("pclmulqdq"); require!("sha");
}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runner', default='', help='runner executable and arguments, shell-quoted')
    args = parser.parse_args()
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        parser.error('requires a Linux x86-64 build host')
    runner = shlex.split(args.runner)
    target = Path(os.environ.get('CARGO_TARGET_DIR', ROOT / 'target'))
    target.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='avx512-probe-', dir=target) as directory:
        source, binary = Path(directory) / 'probe.rs', Path(directory) / 'probe'
        source.write_text(PROBE)
        subprocess.run(['rustc', '--edition=2024', str(source), '-o', str(binary)],
                       cwd=ROOT, check=True)
        subprocess.run(runner + [str(binary)], cwd=ROOT, check=True)
    built = subprocess.run(['cargo', 'test', '--release', '--locked', '-p', 'qsag-asm',
                            '--lib', '--no-run', '--message-format=json'],
                           cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE)
    artifacts = [json.loads(line) for line in built.stdout.splitlines() if line.startswith('{')]
    binaries = {a['executable'] for a in artifacts if a.get('reason') == 'compiler-artifact'
                and a.get('target', {}).get('name') == 'qsag_asm'
                and a.get('profile', {}).get('test') and a.get('executable')}
    if len(binaries) != 1:
        raise RuntimeError(f'expected one production library test binary, got {binaries}')
    binary = binaries.pop()
    for name in TESTS:
        result = subprocess.run(runner + [binary, name, '--exact', '--nocapture'],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        print(result.stdout, end='', flush=True)
        result.check_returncode()
        if 'test result: ok. 1 passed; 0 failed; 0 ignored;' not in result.stdout:
            raise RuntimeError(f'{name}: required production test did not execute exactly once')
    print(f'PASS: {len(TESTS)} production differential tests with required AVX-512 features')


if __name__ == '__main__':
    main()
