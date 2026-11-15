#!/usr/bin/env python3
"""Dependency-free sizing model, not a prover benchmark. See the companion report."""
import argparse
from dataclasses import dataclass
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / 'docs/QUORUM_AND_CONSENSUS_SCALING.md'
BEGIN = '<!-- BEGIN GENERATED SCALING TABLES -->'
END = '<!-- END GENERATED SCALING TABLES -->'

@dataclass(frozen=True)
class Measurement:
    name: str
    size: int
    prove_ms: float
    verify_ms: float

# Historical paper protobench snapshot, affine v6, K=8, i9-12900.
# These calibration constants are retained; current paper edits do not remeasure them.
MEASUREMENTS = (
    Measurement('Jorts / Habr24', 161112, 4300, 13.55),
    Measurement('Jorts / Johnson', 291352, 4900, 26.69),
    Measurement('Corduroy / Habr24', 240014, 49200, 18.88),
    Measurement('Corduroy / Johnson', 446254, 48840, 35.33),
)

@dataclass(frozen=True)
class Assumptions:
    # A sizing hypothesis, NOT a fitted large-batch proof-size curve.
    batch: int = 2048
    proof_bytes: int = 1_000_000
    verify_ms: float = 50.0
    gpu_fraction: float = 0.8
    gpu_kernel_speedup: float = 10.0
    gpu_overhead_ms: float = 2.0
    cpu_relative_speedup: float = 4.0

    def validate(self):
        if self.batch < 1 or self.batch > 2048 or self.batch & (self.batch - 1):
            raise ValueError('batch must be a power of two in [1, 2048] for Jorts')
        if self.proof_bytes <= 0 or not math.isfinite(self.verify_ms) or self.verify_ms <= 0:
            raise ValueError('proof bytes and verification time must be positive')
        if not 0 <= self.gpu_fraction <= 1:
            raise ValueError('GPU fraction must be in [0, 1]')
        for value in (self.gpu_kernel_speedup, self.cpu_relative_speedup):
            if not math.isfinite(value) or value <= 0:
                raise ValueError('speedups must be positive and finite')
        if not math.isfinite(self.gpu_overhead_ms) or self.gpu_overhead_ms < 0:
            raise ValueError('GPU overhead must be nonnegative and finite')

def ceildiv(n, d):
    return (n + d - 1) // d

def hierarchy_bytes(children):
    """Exact outer framing; supplied child lengths must already include all inner bytes."""
    return 76 + sum(124 + b for b in children)

def gpu_time(cpu_ms, a):
    return cpu_ms * (1 - a.gpu_fraction + a.gpu_fraction / a.gpu_kernel_speedup) + a.gpu_overhead_ms

def fmt(x):
    return f'{x:,}' if isinstance(x, int) else f'{x:,.3f}'

def table(headers, rows):
    return '\n'.join(['| ' + ' | '.join(headers) + ' |',
                      '| ' + ' | '.join(['---'] * len(headers)) + ' |'] +
                     ['| ' + ' | '.join(fmt(x) if isinstance(x, (int, float)) else x for x in r) + ' |' for r in rows])

def generated(a=Assumptions()):
    a.validate()
    sections = [BEGIN, '### Reported calibration (not rerun here)', table(
        ['Profile / regime', 'K', 'Proof B', 'Prove ms', 'Verify ms'],
        [(m.name, 8, m.size, m.prove_ms, m.verify_ms) for m in MEASUREMENTS])]
    sections += ['### Raw signatures and trace storage', table(
        ['Signers', 'ML-DSA-44 B', 'Jorts B', 'Corduroy B', 'Jorts base trace GiB'],
        [(n, n*2420, n*4328, n*76896, n*512*256*8/2**30)
         for n in (1000, 1500, 8192, 131072, 1048576)])]
    sections += ['### Repeated K=8 Johnson calibration: payload/work envelope', table(
        ['Signers', 'K=8 jobs', 'Sum standalone proof B', 'Reference-host work s', 'Serial verify ms'],
        [(n, ceildiv(n,8), ceildiv(n,8)*291352, ceildiv(n,8)*4.9, ceildiv(n,8)*26.69)
         for n in (1000, 8192, 131072, 1048576)])]
    sections += ['### Hypothetical Jorts batch parameters', table(
        ['Batch cap', 'Proof B/batch', 'Verify ms/batch', 'CPU relative speedup', 'GPU fraction', 'GPU kernel speedup', 'GPU overhead ms/batch'],
        [(a.batch,a.proof_bytes,a.verify_ms,a.cpu_relative_speedup,a.gpu_fraction,a.gpu_kernel_speedup,a.gpu_overhead_ms)])]
    rows=[]
    for n in (1000,8192,131072,1048576):
        regions=ceildiv(n,8192)
        sizes=[min(8192,n-i*8192) for i in range(regions)]
        jobs=[ceildiv(s,a.batch) for s in sizes]
        # A per-batch budget includes its bitmap and header. Merging removes repeated
        # 41B headers and adds one branch tag per join; this part is source-derived.
        child=[j*a.proof_bytes-40*(j-1) for j in jobs]
        root=hierarchy_bytes(child)
        rows.append((n,regions,sum(jobs),root,root/4,n*2420/root,sum(jobs)*a.verify_ms))
    sections += ['### Hypothetical hierarchy bandwidth (one copy, four-second slot)', table(
        ['Signers', 'Regions', 'Batch proofs', 'Root B', 'Root B/s', 'ML-DSA/raw to root ratio', 'Serial verify ms'], rows)]
    rows=[]
    for n in (1000,8192):
        jobs=ceildiv(n,a.batch)
        # Linear-work extrapolation from the entire reference host, no implied core count.
        ref=n/8*4900
        cpu=ref/a.cpu_relative_speedup
        gpu=gpu_time(ref/jobs,a)*jobs
        deadline=150 if n==1000 else 4000
        rows.append((n,jobs,ref/1000,cpu/1000,gpu/1000,ref/deadline,
                     ceildiv(math.ceil(ref),deadline)))
    sections += ['### Hypothetical aggregation latency and capacity requirements', table(
        ['Signers', 'Batches', 'Reference work s', 'Faster CPU s', 'GPU scenario s', 'Required speedup to deadline', 'Ideal reference-host equivalents'], rows)]
    sections += ['### Trace geometry and verifier chain work', table(
        ['Profile', 'w', 'Chains', 'Target sum', 'Verifier chain steps', 'Rows/signer', 'Max signers/shard'],
        [('Hem Jorts',4,128,192,128*3-192,512,128),
         ('Hem Corduroy (per WOTS layer)',4,128,192,128*3-192,8192,8),
         ('Custody base-16 (per WOTS layer)',16,64,480,64*15-480,'not Hem','not Hem')])]
    sections += ['### Johnson QROM query schedule', table(['log2 blowup','Queries'],
        [(b,ceildiv(512,b)+2) for b in (2,4,6,8)]), END]
    return '\n\n'.join(sections)

def self_test():
    assert [ceildiv(512,b)+2 for b in (2,4,6,8)] == [258,130,88,66]
    assert 2420*1000 == 2420000
    assert 32+4+4+128*32+6*32 == 4328
    assert 32+32*9*32+16*(4+128*32+4*32) == 76896
    assert 2**24//(512*256) == 128
    assert 2**24//(8192*256) == 8
    assert hierarchy_bytes([100,200]) == 624
    assert ceildiv(1001,8) == 126
    assert gpu_time(100,Assumptions(gpu_fraction=0,gpu_overhead_ms=0)) == 100
    assert gpu_time(100,Assumptions(gpu_fraction=1,gpu_kernel_speedup=10,gpu_overhead_ms=0)) == 10
    for bad in (Assumptions(batch=0),Assumptions(batch=4096),Assumptions(batch=3),
                Assumptions(gpu_fraction=2),Assumptions(cpu_relative_speedup=0)):
        try:
            bad.validate()
        except ValueError:
            pass
        else:
            raise AssertionError('invalid assumptions accepted')
    # Fast drift checks on load-bearing source facts, not a security proof or Rust test.
    checks = {
        'crates/qsag-agg/src/sig.rs': ['WOTS_CHAINS: usize = 128', 'WOTS_TARGET_SUM: usize = 192', 'JORTS_XMSS_HEIGHT: usize = 6'],
        'crates/qsag-agg/src/lib.rs': ['this crate has no recursive', 'MAX_MERGE_TREE_DEPTH: usize = 16'],
        'crates/qsag-agg/src/recursive.rs': ['pub struct VerifiedHierarchicalHemEvidence', 'evidence: &VerifiedHierarchicalHemEvidence', 'checked_add(124)', 'bytes.len() < 76'],
    }
    for path, tokens in checks.items():
        content=(ROOT/path).read_text()
        for token in tokens:
            assert token in content, f'source drift: {path}: {token}'
    content=DOC.read_text()
    assert content.count(BEGIN)==content.count(END)==1
    actual=content[content.index(BEGIN):content.index(END)+len(END)]
    assert actual==generated(), 'documentation table drift: regenerate using --write-tables'
    return 'PASS: arithmetic, boundary cases, source guards, and all generated documentation tables match.'

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--self-test',action='store_true')
    p.add_argument('--write-tables',action='store_true',help='replace the marked tables in the companion report')
    p.add_argument('-o','--output',type=Path,help='write the report summary and tables here; use ./-o for a literal -o filename')
    p.add_argument('--batch',type=int,default=2048)
    p.add_argument('--proof-bytes',type=int,default=1000000)
    p.add_argument('--verify-ms',type=float,default=50)
    p.add_argument('--cpu-relative-speedup',type=float,default=4)
    p.add_argument('--gpu-fraction',type=float,default=.8)
    p.add_argument('--gpu-kernel-speedup',type=float,default=10)
    p.add_argument('--gpu-overhead-ms',type=float,default=2)
    args=p.parse_args()
    a=Assumptions(args.batch,args.proof_bytes,args.verify_ms,args.gpu_fraction,args.gpu_kernel_speedup,args.gpu_overhead_ms,args.cpu_relative_speedup)
    try:
        a.validate()
    except ValueError as exc:
        p.error(str(exc))
    if args.write_tables:
        if a != Assumptions():
            p.error('--write-tables requires default assumptions to preserve self-test reproducibility')
        content=DOC.read_text()
        start=content.index(BEGIN); end=content.index(END)+len(END)
        DOC.write_text(content[:start]+generated()+content[end:])
    status=self_test() if args.self_test else 'Sizing model only; no benchmarks executed.'
    summary=(status+'\n\nQSAG supports independent-validator aggregation and separate threshold custody. '
             'Current hierarchy retains child proofs; succinct recursion, sub-ms Hem verification, '
             'and RX 6750 XT end-to-end proving latency are not established. '
             'K=8 affine Johnson Jorts: 291,352 B, 4.90 s prove, 26.69 ms verify (paper-reported). '
             'The large-batch CPU/GPU tables are explicit sensitivity scenarios, not measurements.\n\n')
    if args.output:
        if args.output.resolve() in (DOC.resolve(),Path(__file__).resolve()):
            p.error('output must not overwrite either owned source file')
        args.output.write_text(summary+generated(a)+'\n')
    print(status if args.self_test else summary+generated(a))

if __name__=='__main__':
    main()
