#!/usr/bin/env python3
"""Dependency-free consensus scaling model calibrated on measured QSAG runs.

It executes no prover. Measured constants are copied from recorded release runs and
are labelled as such; every other number is arithmetic on them. See
docs/QUORUM_AND_CONSENSUS_SCALING.md for what each table does and does not claim.
"""
import argparse
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / 'docs/QUORUM_AND_CONSENSUS_SCALING.md'
BEGIN = '<!-- BEGIN GENERATED SCALING TABLES -->'
END = '<!-- END GENERATED SCALING TABLES -->'

# --- Wire sizes fixed by the formats -------------------------------------------------
ML_DSA_44_B = 2_420
JORTS_SIG_B = 32 + 4 + 4 + 128 * 32 + 6 * 32       # 4,328
CORDUROY_SIG_B = 32 + 32 * 9 * 32 + 16 * (4 + 128 * 32 + 4 * 32)  # 76,896
COMPACT1122_B = 1_122
VOTE_HEADER_B = 96
PACKET_PAYLOAD_B = 1_232          # IPv6 minimum MTU 1,280 minus 48; Solana PACKET_DATA_SIZE
QUIC_FLOOR_PAYLOAD_B = 1_200      # RFC 9000 minimum datagram
SHARD_SIGNERS = 2**24 // (512 * 256)               # 128 Jorts signers in a 24-variable shard


@dataclass(frozen=True)
class Shard:
    """One full 128-signer JortsPoseidon2 shard, 24 PCS variables, one release run each."""
    regime: str
    tag: int
    proof_b: int
    cpu_prove_s: float
    gpu_prove_s: float | None
    verify_ms: float          # all workers
    verify_1core_ms: float


# Intel Core i9-12900 (22 workers) and AMD Radeon RX 6750 XT (RADV NAVI22, Vulkan).
# The default regime is the calibration; the Poseidon2 Canopy row predates the last
# row-sumcheck speedup and has no GPU measurement.
SHARD = Shard('BciksJohnsonQrom128 (cSHAKE256 Canopy, default)', 4, 445_566, 3.67, 1.56, 3.00, 6.21)
SHARD_P2 = Shard('Poseidon2Cdhz25JohnsonQrom128 (Poseidon2-12 Canopy, Q <= 2^38)', 7, 360_702, 7.24, None, 6.84, 13.21)


@dataclass(frozen=True)
class Merge:
    """Fixed-path WHIR opening merge of `arity` children, each a 4,096-cell oracle (12
    variables), regime tag 8 (Poseidon2-12, no PoW, Q + 1 <= 2^40). Same CPU host."""
    arity: int
    prove_s: float
    verify_ms: float
    parent_b: int
    children_b: int


MERGES = {2: Merge(2, 1.002, 123.0, 302_547, 527_872),
          4: Merge(4, 1.876, 246.0, 339_643, 1_055_744)}
MERGE_CHILD_VARS = 12
MAX_MERGE_CHILDREN = 16

# Compact1122 batch verification, 1,200 votes: one core with SIMD multibuffering.
FTS_VERIFY_1CORE_MS_PER_VOTE = 1_230.0 / 1_200

SOLANA_SLOT_MS = 400.0
BEAM_SLOT_S = 4.0
ETH_SLOT_S = 12.0
ETH_EPOCH_S = 384.0


def ceildiv(n, d):
    return (n + d - 1) // d


def shards_for(n):
    return ceildiv(n, SHARD_SIGNERS)


def hierarchy_bytes(children):
    """Exact outer framing of `HierarchicalHemAggregate`; children are full proof lengths."""
    return 76 + sum(124 + b for b in children)


def merge_levels(leaves, arity):
    """Node count per level of an `arity`-ary tree over `leaves`, leaves excluded."""
    levels = []
    while leaves > 1:
        leaves = ceildiv(leaves, arity)
        levels.append(leaves)
    return levels


def fmt(x):
    if isinstance(x, str):
        return x
    if isinstance(x, int):
        return f'{x:,}'
    return f'{x:,.2f}'


def table(headers, rows):
    return '\n'.join(['| ' + ' | '.join(headers) + ' |',
                      '| ' + ' | '.join(['---'] * len(headers)) + ' |'] +
                     ['| ' + ' | '.join(fmt(x) for x in r) + ' |' for r in rows])


def generated(link_mbps=100.0, arity=4):
    m = MERGES[arity]
    s = SHARD
    out = [BEGIN]

    out += ['### Measured: one 128-signer Jorts shard (24 variables)', table(
        ['Regime', 'Tag', 'Proof B', 'CPU prove s', 'GPU prove s', 'Verify ms (all workers)', 'Verify ms (1 core)'],
        [(x.regime, x.tag, x.proof_b, x.cpu_prove_s,
          'not measured' if x.gpu_prove_s is None else x.gpu_prove_s, x.verify_ms, x.verify_1core_ms)
         for x in (SHARD, SHARD_P2)])]

    out += [f'### Measured: fixed-path WHIR opening merge ({2**MERGE_CHILD_VARS:,}-cell children, tag 8)', table(
        ['Children', 'Prove s', 'Verify ms', 'Parent B', 'Children B', 'Parent / children'],
        [(x.arity, x.prove_s, x.verify_ms, x.parent_b, x.children_b, x.parent_b / x.children_b)
         for x in MERGES.values()])]

    populations = (1_000, 1_200, 1_500, 2_048, 8_192, 131_072, 1_048_576)
    out += ['### Exact: raw signature payload and Hem base trace', table(
        ['Signers', 'Compact1122 B', 'ML-DSA-44 B', 'Jorts B', 'Shards', 'Jorts base trace GiB'],
        [(n, n * COMPACT1122_B, n * ML_DSA_44_B, n * JORTS_SIG_B, shards_for(n),
          n * 512 * 256 * 8 / 2**30) for n in populations])]

    vote_b = COMPACT1122_B + VOTE_HEADER_B
    rows = []
    for n in (1_000, 1_200, 1_500):
        one_core = n * FTS_VERIFY_1CORE_MS_PER_VOTE
        rows.append((n, vote_b, n * vote_b, n * vote_b * 8 / (SOLANA_SLOT_MS / 1000) / 1e6,
                     one_core, ceildiv(int(one_core + 0.999), int(SOLANA_SLOT_MS))))
    out += [f'### Solana / Alpenglow live vote path ({SOLANA_SLOT_MS:.0f} ms slot, Compact1122)', table(
        ['Votes', 'Datagram B', 'Ingress B / recipient', f'Mbps over {SOLANA_SLOT_MS:.0f} ms',
         '1-core SIMD verify ms', 'Cores to verify inside the slot (ideal)'], rows)]

    rows = []
    for n in (1_000, 1_200, 1_500):
        k = shards_for(n)
        agg = hierarchy_bytes([s.proof_b] * k)
        rows.append((n, k, agg, n * JORTS_SIG_B / agg, n * COMPACT1122_B / agg,
                     k * s.cpu_prove_s, k * s.gpu_prove_s, k * s.verify_1core_ms))
    out += ['### Solana / Alpenglow asynchronous checkpoint (full shard proofs retained)', table(
        ['Signers', 'Shards', 'Hierarchy B', 'Raw Jorts / hierarchy', 'Raw Compact1122 / hierarchy',
         'CPU prove s (one host, serial)', 'GPU prove s (one GPU, serial)', 'Verify core-ms'], rows)]

    rows = []
    for n in (2_048, 8_192):
        k = shards_for(n)
        agg = hierarchy_bytes([s.proof_b] * k)
        rows.append((n, k, agg, agg * 8 / (link_mbps * 1e6), s.gpu_prove_s, s.cpu_prove_s,
                     k * s.gpu_prove_s, k * s.verify_ms, k * s.verify_1core_ms))
    out += [f'### Lean-Ethereum / Beam subnets ({BEAM_SLOT_S:.0f} s slot, direct verification of every shard)', table(
        ['Validators', 'Subnets of 128', 'Hierarchy B', f'Transfer s at {link_mbps:.0f} Mbps',
         'GPU prove s (parallel, per subnet)', 'CPU prove s (parallel, per subnet)', 'Total GPU-s',
         'Verify ms (serial, all workers)', 'Verify core-ms'], rows)]

    rows = []
    for n in (2_048, 8_192, 131_072, 1_048_576):
        k = shards_for(n)
        levels = merge_levels(k, arity)
        depth, nodes = len(levels), sum(levels)
        rows.append((n, k, depth, nodes, s.gpu_prove_s + depth * m.prove_s,
                     s.cpu_prove_s + depth * m.prove_s, nodes * m.prove_s, m.parent_b, ceildiv(n, 8)))
    out += [f'### Projection: pipelined k={arity} opening-merge tree (per-level cost from {2**MERGE_CHILD_VARS:,}-cell children)', table(
        ['Validators', 'Shards', 'Tree depth', 'Merge provers', 'Pipelined s (GPU shards)',
         'Pipelined s (CPU shards)', 'Total merge prover-s', 'Root opening proof B', 'Signer bitmap B'], rows)]

    rows = []
    for n in (131_072, 1_048_576):
        k = shards_for(n)
        gpu_s = k * s.gpu_prove_s
        rows.append((n, k, k * s.proof_b, gpu_s, ceildiv(int(gpu_s + 0.999), int(ETH_SLOT_S)),
                     ceildiv(int(gpu_s + 0.999), int(ETH_EPOCH_S)), k * s.verify_1core_ms / 1000,
                     k * s.proof_b * 8 / (link_mbps * 1e6)))
    out += [f'### Epoch / finality scale ({ETH_SLOT_S:.0f} s slots, {ETH_EPOCH_S:.0f} s epochs)', table(
        ['Validators', 'Shards', 'Sum of shard proofs B', 'Total GPU-s',
         f'GPUs to prove in {ETH_SLOT_S:.0f} s (ideal)', f'GPUs to prove in {ETH_EPOCH_S:.0f} s (ideal)',
         'Direct verify core-s', f'Evidence transfer s at {link_mbps:.0f} Mbps'], rows)]

    out += ['### Trace geometry and verifier chain work', table(
        ['Profile', 'w', 'Chains', 'Target sum', 'Verifier chain steps', 'Rows/signer', 'Signers per 24-variable shard'],
        [('Hem Jorts', 4, 128, 192, 128 * 3 - 192, 512, 2**24 // (512 * 256)),
         ('Hem Corduroy (per WOTS layer)', 4, 128, 192, 128 * 3 - 192, 8192, 2**24 // (8192 * 256)),
         ('Custody base-16 (per WOTS layer)', 16, 64, 480, 64 * 15 - 480, 'not Hem', 'not Hem')])]

    out += ['### WHIR query schedules', table(
        ['log2 blowup', 'Tag 4 (default)', 'Tags 5, 7', 'Tags 6, 8'],
        [(b, ceildiv(512, b) + 2, q57, q68)
         for b, q57, q68 in ((2, 202, 216), (4, 102, 109), (6, 70, 74), (8, 52, 56))]), END]
    return '\n\n'.join(out)


def self_test():
    # Arithmetic identities.
    assert JORTS_SIG_B == 4_328 and CORDUROY_SIG_B == 76_896
    assert SHARD_SIGNERS == 128 and 2**24 // (8192 * 256) == 8
    assert COMPACT1122_B + VOTE_HEADER_B == 1_218 <= PACKET_PAYLOAD_B
    assert COMPACT1122_B + VOTE_HEADER_B > QUIC_FLOOR_PAYLOAD_B
    assert [ceildiv(512, b) + 2 for b in (2, 4, 6, 8)] == [258, 130, 88, 66]
    assert hierarchy_bytes([100, 200]) == 624
    assert [shards_for(n) for n in (1_000, 1_500, 2_048, 8_192, 131_072, 1_048_576)] == [8, 12, 16, 64, 1_024, 8_192]
    # Tree shapes.
    assert merge_levels(16, 4) == [4, 1] and merge_levels(64, 4) == [16, 4, 1]
    assert merge_levels(1_024, 4) == [256, 64, 16, 4, 1]
    assert merge_levels(8_192, 4) == [2_048, 512, 128, 32, 8, 2, 1]
    assert merge_levels(1, 4) == [] and merge_levels(5, 4) == [2, 1]
    assert sum(merge_levels(1_024, 4)) == 341 and sum(merge_levels(8_192, 4)) == 2_731
    # Measured ratios quoted in prose.
    assert MERGES[2].children_b * 2 == MERGES[4].children_b
    assert round(MERGES[2].parent_b / MERGES[2].children_b, 2) == 0.57
    assert round(MERGES[4].parent_b / MERGES[4].children_b, 2) == 0.32
    assert round(64 * SHARD.verify_ms) == 192 and round(64 * SHARD.verify_1core_ms) == 397
    # Pipelined projections quoted in prose (GPU shard proving plus one merge per level).
    assert round(SHARD.gpu_prove_s + 5 * MERGES[4].prove_s, 2) == 10.94
    assert round(SHARD.gpu_prove_s + 7 * MERGES[4].prove_s, 2) == 14.69
    # The shard proofs are larger than the Compact1122 votes they would summarize.
    assert hierarchy_bytes([SHARD.proof_b] * 12) > 1_500 * COMPACT1122_B
    assert hierarchy_bytes([SHARD.proof_b] * 12) < 1_500 * JORTS_SIG_B
    # Source drift guards on load-bearing facts. Not a security proof or a Rust test.
    checks = {
        'crates/qsag-agg/src/sig.rs': ['WOTS_CHAINS: usize = 128', 'WOTS_TARGET_SUM: usize = 192', 'JORTS_XMSS_HEIGHT: usize = 6'],
        'crates/qsag-agg/src/arithmetize.rs': ['DEFAULT_SHARD_PCS_NUM_VARS: usize = 24'],
        'crates/qsag-agg/src/lib.rs': ['Across shard batches nothing is compressed', 'MAX_MERGE_TREE_DEPTH: usize = 16'],
        'crates/qsag-agg/src/recursive.rs': [
            'pub struct VerifiedHierarchicalHemEvidence', 'evidence: &VerifiedHierarchicalHemEvidence',
            'evidence.regime() == regime', 'let nv = 12usize', 'checked_add(124)', 'bytes.len() < 76'],
        'crates/qsag-agg/src/zk_hem/recursive_whir.rs': [
            'MAX_MERGE_CHILDREN: usize = 16', 'measure_children(12, 4)',
            'REGIME: WhirSecurityRegime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128'],
        'crates/qsag-agg/src/pcs.rs': ['by_blowup([202, 102, 70, 52])', 'by_blowup([216, 109, 74, 56])'],
        'crates/qsag-agg/examples/mock_solana_alpenglow.rs': [
            'const VOTOR_HEADER_BYTES: usize = 96', 'const IPV6_PAYLOAD_BYTES: usize = 1_232',
            'const QUIC_PAYLOAD_MTU_BYTES: usize = 1_200'],
        'crates/qsag-fts/src/lib.rs': ['Compact1122.signature_bytes(), 1122'],
    }
    for path, tokens in checks.items():
        content = (ROOT / path).read_text()
        for token in tokens:
            assert token in content, f'source drift: {path}: {token}'
    content = DOC.read_text()
    assert content.count(BEGIN) == content.count(END) == 1
    actual = content[content.index(BEGIN):content.index(END) + len(END)]
    assert actual == generated(), 'documentation table drift: regenerate using --write-tables'
    return 'PASS: arithmetic, tree shapes, source guards, and all generated documentation tables match.'


SUMMARY = (
    'One 128-signer Jorts shard under the default BciksJohnsonQrom128 regime: 445,566 B, '
    '3.67 s CPU prove (Intel Core i9-12900), 1.56 s GPU prove (AMD Radeon RX 6750 XT), '
    '3.00 ms verify on all workers, 6.21 ms on one core. '
    'The fixed-path WHIR opening merge is measured on 4,096-cell children only '
    '(k=2: 1.00 s, 302,547 B; k=4: 1.88 s, 339,643 B) and certifies openings, not signatures: '
    'authorization still needs VerifiedHierarchicalHemEvidence from verifying every shard proof. '
    'Merge-tree rows are projections, not measurements.\n\n')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--self-test', action='store_true')
    p.add_argument('--write-tables', action='store_true', help='replace the marked tables in the companion report')
    p.add_argument('-o', '--output', type=Path, help='write the summary and tables here; use ./-o for a literal -o filename')
    p.add_argument('--link-mbps', type=float, default=100.0, help='link rate for the transfer columns')
    p.add_argument('--merge-arity', type=int, default=4, choices=sorted(MERGES), help='fan-in of the projected merge tree')
    args = p.parse_args()
    if not args.link_mbps > 0:
        p.error('--link-mbps must be positive')
    defaults = args.link_mbps == 100.0 and args.merge_arity == 4
    if args.write_tables:
        if not defaults:
            p.error('--write-tables requires default parameters to preserve self-test reproducibility')
        content = DOC.read_text()
        start = content.index(BEGIN)
        end = content.index(END) + len(END)
        DOC.write_text(content[:start] + generated() + content[end:])
    status = self_test() if args.self_test else 'Scaling model only; no prover executed.'
    tables = generated(args.link_mbps, args.merge_arity)
    if args.output:
        if args.output.resolve() in (DOC.resolve(), Path(__file__).resolve()):
            p.error('output must not overwrite either owned source file')
        args.output.write_text(status + '\n\n' + SUMMARY + tables + '\n')
    print(status if args.self_test else status + '\n\n' + SUMMARY + tables)


if __name__ == '__main__':
    main()
