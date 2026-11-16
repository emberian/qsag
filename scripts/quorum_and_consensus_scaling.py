#!/usr/bin/env python3
"""Dependency-free consensus scaling model for QSAG.

It executes no prover. Every constant below carries one of three provenance tags:

  exact     fixed by a wire format or by arithmetic on one
  measured  copied from a recorded release run on the named hardware
  model     a projection; its inputs and formula are stated where it is defined

Tables in docs/QUORUM_AND_CONSENSUS_SCALING.md are generated from this file and the
self-test fails if they drift. See that document for what each table claims.
"""
import argparse
import math
from dataclasses import dataclass
from itertools import combinations_with_replacement
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / 'docs/QUORUM_AND_CONSENSUS_SCALING.md'
BEGIN = '<!-- BEGIN GENERATED SCALING TABLES -->'
END = '<!-- END GENERATED SCALING TABLES -->'

# --- exact: wire sizes ---------------------------------------------------------------
ML_DSA_44_B = 2_420
JORTS_MIN_HEIGHT, JORTS_MAX_HEIGHT = 6, 20
CORDUROY_SIG_B = 32 + 32 * 9 * 32 + 16 * (4 + 128 * 32 + 4 * 32)  # 76,896
COMPACT1122_B = 1_122
VOTE_HEADER_B = 96
PACKET_PAYLOAD_B = 1_232          # IPv6 minimum MTU 1,280 minus 48; Solana PACKET_DATA_SIZE
QUIC_FLOOR_PAYLOAD_B = 1_200      # RFC 9000 minimum datagram
BLS_SIG_B = 96
VALIDATOR_PK_B = 65               # profile byte, 32-byte seed, 32-byte root
ROSTER_ROOT_B = 32
NODE_B = 32
SUBTREE_PUBLIC_WORDS = 14
SUBTREE_HEADER_B = 8 + 8 + 3 * 8  # magic, signer count, min/max key index, weight
TRACE_COLUMNS = 256
ROWS_PER_SIGNER = 512
SBOXES_PER_PERMUTATION = 8 * 12 + 22  # width-12 Poseidon2: 8 full rounds, 22 partial


def jorts_sig_bytes(height=JORTS_MIN_HEIGHT):
    """randomizer, epoch, counter, 128 chain nodes, `height` authentication nodes"""
    return 32 + 4 + 4 + 128 * NODE_B + height * NODE_B


def jorts_active_rows(height=JORTS_MIN_HEIGHT):
    """8 message rows, 1 + 64 * 7 + 1 chain rows, 2 Merkle rows per level"""
    return 8 + 1 + 64 * 7 + 1 + 2 * height


JORTS_SIG_B = jorts_sig_bytes(6)      # 4,328
JORTS_H20_SIG_B = jorts_sig_bytes(20)  # 4,776


def ceildiv(n, d):
    return (n + d - 1) // d


# --- measured: single-WHIR shard proofs ----------------------------------------------
@dataclass(frozen=True)
class Shard:
    """One JortsPoseidon2 shard proved as a single WHIR instance, one release run each."""
    regime: str
    tag: int
    signers: int
    num_vars: int
    proof_b: int
    cpu_prove_s: float
    gpu_prove_s: float | None
    verify_ms: float          # all workers
    verify_1core_ms: float


# Intel Core i9-12900 (22 workers) and AMD Radeon RX 6750 XT (RADV, Vulkan).
SHARD = Shard('BciksJohnsonQrom128 (cSHAKE256 Canopy, default)', 4, 128, 24, 445_566, 3.67, 1.56, 3.00, 6.21)
SHARD_P2 = Shard('Poseidon2Cdhz25JohnsonQrom128 (Poseidon2-12 Canopy, Q <= 2^38)', 7, 128, 24, 360_702, 7.24, None, 6.84, 13.21)
# AMD Ryzen 9 9950X, tag 4, one polynomial per shard; sizes are byte-identical on every host.
SHARD_K256 = Shard('BciksJohnsonQrom128', 4, 256, 25, 480_342, 5.68, None, 2.8, 6.2)
SHARD_K512 = Shard('BciksJohnsonQrom128', 4, 512, 26, 556_830, 11.08, None, 3.6, 8.9)
DIRECT_SHARD_B = {128: SHARD.proof_b, 256: SHARD_K256.proof_b, 512: SHARD_K512.proof_b}

# measured: Compact1122 batch verification, 1,200 votes, one core with SIMD multibuffering.
FTS_VERIFY_1CORE_MS_PER_VOTE = 1_230.0 / 1_200

# measured: native verification of one hologram root proof, one core.
HOLOGRAM_VERIFY_MS = 11.5
HOLOGRAM_VERIFY_GATE_MS = 15.0

SOLANA_SLOT_MS = 400.0
BEAM_SLOT_S = 4.0


# --- Subtree recursion ---------------------------------------------------------------
@dataclass(frozen=True)
class Leaf:
    """A recursive shard of `signers` validators (`2^num_vars` trace cells).

    measured  cpu_child_s   recursive-shard child prove, Ryzen 9 9950X (tag 8)
    measured  commit0_s     GPU round-0 commit at this size, RX 6750 XT; None where the
                            only measurement is the whole 1.33 s single-WHIR shard
    measured  vram_gib      prover arena resident in 12 GiB of VRAM
    model     gpu_s         full recursive-shard prove with both commitments on the GPU:
                            the measured K=128 shard scaled by the measured commit ratio,
                            plus the measured Poseidon2 Canopy build for the second witness
    """
    signers: int
    num_vars: int
    cpu_child_s: float
    commit0_s: float | None
    vram_gib: float
    gpu_s: float


@dataclass(frozen=True)
class MergeNode:
    """One hologram merge of `arity` children.

    exact  log_rows, var_bits, ell_nz   padded relation geometry
    model  cpu_s, gpu_s                 prove time, linear in padded rows from the
                                        quaternary point
    """
    arity: int
    log_rows: int
    var_bits: int
    ell_nz: int
    cpu_s: float
    gpu_s: float


class SubtreeHologramModel:
    """Arbitrary-depth `Merge -> Merge` recursion to one `SuccinctSubtreeAggregate`.

    Leaves are recursive shard proofs. A leaf merge verifies up to `arity` shards and an
    internal merge verifies up to `arity` child merges; both expose the same 14-word public
    statement, so the root proof has one size per arity whatever the depth, and the
    verifier holds only a 32-byte roster root and a verifier key under 256 bytes.
    """

    LEAVES = {
        128: Leaf(128, 24, 4.44, None, 2.8, 1.62),
        256: Leaf(256, 25, 8.73, 1.65, 5.3, 3.15),
        512: Leaf(512, 26, 17.02, 3.44, 9.9, 6.35),
    }
    MERGES = {
        2: MergeNode(2, 17, 18, 19, 0.85, 0.22),
        4: MergeNode(4, 18, 19, 20, 1.65, 0.38),
        8: MergeNode(8, 19, 20, 21, 3.25, 0.68),
        16: MergeNode(16, 20, 21, 22, 6.40, 1.25),
    }
    ARITIES = tuple(MERGES)
    # model: three Steiner-deduplicated WHIR openings, linear in ell_nz around the binary point.
    WHIR_OPENINGS_B = 282_000
    WHIR_OPENINGS_PER_VAR_B = 6_400
    # model: one-thread Poseidon2 permutation, used only for the per-epoch roster build.
    PERMUTATION_NS = 210.0

    @classmethod
    def logup_gkr_bytes(cls, arity):
        """exact: quartic extension elements of the lookup GKR transcript."""
        m = cls.MERGES[arity]
        return sum(4 * layer + 4 for layer in range(m.ell_nz + 2)) * 32

    @classmethod
    def root_proof_bytes(cls, arity):
        """Sumcheck, lookup and header terms are exact element counts; the opening term is
        the fitted model above."""
        m = cls.MERGES[arity]
        commitments = 8 + 2 * 104
        row = (4 * m.log_rows + 3) * 32
        column = (3 * m.var_bits + 1) * 32
        matrix = (1 + 4 * m.ell_nz + 7 + 8 + 1) * 32
        lookup = cls.logup_gkr_bytes(arity) + (7 + 8) * 32
        openings = cls.WHIR_OPENINGS_B + (m.ell_nz - 19) * cls.WHIR_OPENINGS_PER_VAR_B
        return SUBTREE_HEADER_B + commitments + row + column + matrix + lookup + openings

    @classmethod
    def uniform_schedule(cls, leaves, arity):
        """Every level uses `arity` (the LAN, latency-optimal choice at arity 4)."""
        depth = 1
        while arity ** depth < leaves:
            depth += 1
        return (arity,) * depth

    @classmethod
    def min_hop_schedule(cls, leaves, max_arity=16):
        """Fewest levels with arity <= max_arity, then least total GPU merge time; wider
        nodes sit nearer the leaves. This is the WAN choice: each level is a network hop."""
        allowed = [a for a in cls.ARITIES if a <= max_arity]
        depth = len(cls.uniform_schedule(leaves, max(allowed)))
        best = min((s for s in combinations_with_replacement(sorted(allowed, reverse=True), depth)
                    if math.prod(s) >= leaves),
                   key=lambda s: (sum(cls.MERGES[a].gpu_s for a in s), s))
        return tuple(best)

    @classmethod
    def plan(cls, validators, shard_signers, schedule=None, max_arity=16):
        leaf = cls.LEAVES[shard_signers]
        leaves = ceildiv(validators, shard_signers)
        schedule = schedule or cls.min_hop_schedule(leaves, max_arity)
        assert math.prod(schedule) >= leaves
        merge_gpu = sum(cls.MERGES[a].gpu_s for a in schedule)
        merge_cpu = sum(cls.MERGES[a].cpu_s for a in schedule)
        nodes, level, cluster = 0, leaves, leaves * leaf.gpu_s
        for a in schedule:
            level = ceildiv(level, a)
            nodes += level
            cluster += level * cls.MERGES[a].gpu_s
        return {
            'validators': validators, 'shard_signers': shard_signers, 'num_vars': leaf.num_vars,
            'leaves': leaves, 'schedule': schedule, 'depth': len(schedule), 'merge_nodes': nodes,
            'root_b': cls.root_proof_bytes(schedule[-1]),
            'critical_gpu_s': leaf.gpu_s + merge_gpu,
            'critical_cpu_merge_s': leaf.gpu_s + merge_cpu,
            'critical_cpu_s': leaf.cpu_child_s + merge_cpu,
            'cluster_gpu_s': cluster,
            'raw_sig_b': validators * JORTS_H20_SIG_B,
            'direct_b': leaves * DIRECT_SHARD_B[shard_signers],
            'roster_build_ms': cls.roster_build_ms(validators),
        }

    @classmethod
    def roster_build_ms(cls, keys):
        """model: hashing every 65-byte key into the roster tree once per epoch, one core."""
        permutations = 3 * keys + 2 * max(1, keys // 128)
        return permutations * cls.PERMUTATION_NS / 1e6

    @staticmethod
    def sparse_leaf_rows(signers, directory_height):
        """exact: structured S-box rows a sparse leaf merge spends on roster paths."""
        return signers * directory_height * SBOXES_PER_PERMUTATION


POPULATIONS = (1_500, 2_048, 8_192, 10_000, 16_384, 50_000, 100_000, 131_072, 1_000_000, 1_048_576)
BRIEF_POPULATIONS = (1_500, 10_000, 50_000, 100_000, 1_048_576)


# --- Dual-path consensus -------------------------------------------------------------
def bitmap_certificate_bytes(validators):
    """exact: one aggregate BLS signature plus an N-bit signer bitmap."""
    return BLS_SIG_B + ceildiv(validators, 8)


BITMAP_MTU_CROSSOVER = (PACKET_PAYLOAD_B - BLS_SIG_B) * 8  # largest N whose bitmap certificate fits


# --- Hyperweb and silicon models -----------------------------------------------------
HUMANS, AGENTS = 8 * 10**9, 80 * 10**9
PRINCIPALS = HUMANS + AGENTS
HYPERWEB_DEPTH = math.ceil(math.log2(PRINCIPALS))  # 37
GOLDILOCKS_P = 2**64 - 2**32 + 1

# exact, on the specified streaming-fold format: 16 sumcheck rounds of 4 extension
# elements, a running commitment with two out-of-domain claims, a 22-variable folded
# point, and the 16-word cut statement padded to 256 bytes.
EDGE_FOLD_B = 16 * 4 * 32 + 96 + 22 * 32 + 256

# model: logic blocks of the QSAG-NI verifier in thousands of gate equivalents.
SILICON_BLOCKS_KGE = (
    ('4-lane GoldilocksExt4 sumcheck / NTT array (36 multipliers)', 524.0),
    ('Width-12 Poseidon2, 30-stage pipeline (1 permutation per clock)', 245.0),
    ('Keccak-f[1600], 2 rounds per clock', 82.0),
    ('Instruction decode, canonical-range checks, transcript control', 65.0),
    ('GF(2^128) carry-less multiplier and tower isomorphism', 38.0),
)
SILICON_LOGIC_KGE = sum(k for _, k in SILICON_BLOCKS_KGE)
# model: (node, effective MGE/mm^2, mm^2 per 128 KiB dual-port SRAM, GHz, active mW)
SILICON_NODES = (
    ('28 nm', 1.40, 0.210, 1.0, 185.0),
    ('7 nm', 7.50, 0.042, 1.6, 110.0),
    ('5 nm', 11.50, 0.026, 2.0, 85.0),
    ('3 nm', 15.00, 0.020, 2.2, 72.0),
)
# model: clock cycles on that datapath.
VERIFY_CYCLES_KECCAK_ROOT = 34_000
VERIFY_CYCLES_POSEIDON2_ROOT = 15_000
EDGE_FOLD_CYCLES = 180_000
MERGE_PROVE_CYCLES = 2_800_000


def silicon_row(node):
    name, density, sram, ghz, mw = node
    logic = SILICON_LOGIC_KGE / 1000 / density
    us = lambda cycles: cycles / (ghz * 1e3)
    slow, fast = us(VERIFY_CYCLES_KECCAK_ROOT), us(VERIFY_CYCLES_POSEIDON2_ROOT)
    return {'node': name, 'area_small': logic + sram, 'area_large': logic + 4 * sram, 'ghz': ghz,
            'mw': mw, 'verify_slow_us': slow, 'verify_fast_us': fast,
            'energy_slow_uj': mw * slow / 1e3, 'energy_fast_uj': mw * fast / 1e3,
            'fold_us': us(EDGE_FOLD_CYCLES), 'merge_ms': MERGE_PROVE_CYCLES / (ghz * 1e6)}


# --- Rendering -----------------------------------------------------------------------
def fmt(x):
    if isinstance(x, str):
        return x
    if isinstance(x, int):
        return f'{x:,}'
    return f'{x:,.2f}'


def kib(b):
    return f'{b / 1024:,.1f}'


def mib(b):
    return f'{b / 2**20:,.1f}'


def binary_size(b):
    for unit in ('B', 'KiB', 'MiB', 'GiB', 'TiB', 'PiB'):
        if b < 1024 or unit == 'PiB':
            return f'{b:,.0f} {unit}'
        b /= 1024


def sched(s):
    return ' x '.join(str(a) for a in s)


def table(headers, rows):
    return '\n'.join(['| ' + ' | '.join(headers) + ' |',
                      '| ' + ' | '.join(['---'] * len(headers)) + ' |'] +
                     ['| ' + ' | '.join(fmt(x) for x in r) + ' |' for r in rows])


PLAN_HEADERS = ['Validators', 'Shard signers', 'Shards', 'Merge schedule', 'Raw signatures MiB',
                'Direct shard proofs MiB', 'Root proof KiB', 'Critical path s (GPU)',
                'Critical path s (GPU shards, CPU merges)', 'Cluster GPU-s', 'Verify ms']


def plan_row(p):
    return (p['validators'], p['shard_signers'], p['leaves'], sched(p['schedule']), mib(p['raw_sig_b']),
            mib(p['direct_b']), kib(p['root_b']), p['critical_gpu_s'], p['critical_cpu_merge_s'],
            f"{p['cluster_gpu_s']:,.1f}", f'{HOLOGRAM_VERIFY_MS}')


def regime_shard(n):
    return 128 if n <= 1_500 else 256 if n <= 16_384 else 512


def subtree_tables():
    M = SubtreeHologramModel
    out = ['### Model: one hologram merge node, by arity', table(
        ['Arity', 'Padded rows', 'Lookup variables', 'Lookup transcript KiB', 'Root proof B',
         'Root proof KiB', 'Prove s (CPU)', 'Prove s (GPU)'],
        [(a, 2**m.log_rows, m.ell_nz, kib(M.logup_gkr_bytes(a)), M.root_proof_bytes(a),
          kib(M.root_proof_bytes(a)), m.cpu_s, m.gpu_s) for a, m in M.MERGES.items()])]

    out += ['### Leaf shards: measured anchors and the modelled GPU prove', table(
        ['Signers', 'Variables', 'Child prove s (CPU, measured)', 'GPU round-0 commit s (measured)',
         'VRAM GiB (measured)', 'Recursive shard prove s (GPU, model)', 'Direct shard proof B (measured)'],
        [(l.signers, l.num_vars, l.cpu_child_s, 'within 1.33 s shard' if l.commit0_s is None else l.commit0_s,
          f'{l.vram_gib}', l.gpu_s, DIRECT_SHARD_B[k]) for k, l in M.LEAVES.items()])]

    out += ['### LAN schedule: 128-signer shards, arity 4 at every level', table(
        PLAN_HEADERS, [plan_row(M.plan(n, 128, M.uniform_schedule(ceildiv(n, 128), 4))) for n in POPULATIONS])]

    out += ['### WAN schedule: 512-signer shards, fewest hops with arity at most 16', table(
        PLAN_HEADERS, [plan_row(M.plan(n, 512)) for n in POPULATIONS])]

    out += ['### Shard size chosen by regime (128 to 1,500; 256 to 16,384; 512 above)', table(
        PLAN_HEADERS, [plan_row(M.plan(n, regime_shard(n))) for n in POPULATIONS])]

    out += ['### Verifier state and per-epoch roster build', table(
        ['Validators', 'Public keys B', 'Signer bitmap B', 'Roster root B', 'Roster build ms (once per epoch, model)',
         'Aggregate verify ms (every proof, measured)'],
        [(n, n * VALIDATOR_PK_B, ceildiv(n, 8), ROSTER_ROOT_B, M.roster_build_ms(n), f'{HOLOGRAM_VERIFY_MS}')
         for n in BRIEF_POPULATIONS])]

    out += ['### Sparse signer sets: roster paths inside one 128-signer leaf merge', table(
        ['Directory height', 'Directory capacity', 'Path B per signer', 'Roster permutations', 'Structured S-box rows',
         'Bitmap over the directory B'],
        [(h, 2**h, h * NODE_B, 128 * h, M.sparse_leaf_rows(128, h), ceildiv(2**h, 8)) for h in (20, 37, 40)])]
    return out


def dual_path_tables():
    vote_b = COMPACT1122_B + VOTE_HEADER_B
    out = ['### Live path: bitmap certificates against the datagram limit', table(
        ['Validators', 'BLS aggregate + bitmap B', f'Fits {PACKET_PAYLOAD_B:,} B', 'Compact1122 vote B'],
        [(n, bitmap_certificate_bytes(n), 'yes' if bitmap_certificate_bytes(n) <= PACKET_PAYLOAD_B else 'no', vote_b)
         for n in (1_500, 8_192, BITMAP_MTU_CROSSOVER, 10_000, 100_000, 1_048_576)])]
    rows = []
    for s in (512, 1_000, 1_200, 1_500):
        one_core = s * FTS_VERIFY_1CORE_MS_PER_VOTE
        rows.append((s, s * vote_b, s * vote_b * 8 / (SOLANA_SLOT_MS / 1000) / 1e6, one_core,
                     ceildiv(math.ceil(one_core), int(SOLANA_SLOT_MS)), ceildiv(math.ceil(one_core), 150)))
    out += ['### Live path: sampled Compact1122 quorum (one datagram per vote)', table(
        ['Sampled votes', 'Ingress B per recipient', f'Mbps over {SOLANA_SLOT_MS:.0f} ms', '1-core SIMD verify ms',
         f'Cores for {SOLANA_SLOT_MS:.0f} ms (ideal)', 'Cores for 150 ms (ideal)'], rows)]
    M = SubtreeHologramModel
    rows = []
    for n in BRIEF_POPULATIONS:
        lan = M.plan(n, 128, M.uniform_schedule(ceildiv(n, 128), 4))
        wan = M.plan(n, 512)
        rows.append((n, kib(lan['root_b']), lan['critical_gpu_s'], lan['depth'], kib(wan['root_b']),
                     wan['critical_gpu_s'], wan['depth'], f'{HOLOGRAM_VERIFY_MS}'))
    out += ['### Finality path: one transferable certificate for the whole validator set', table(
        ['Validators', 'LAN root KiB', 'LAN critical path s', 'LAN levels', 'WAN root KiB', 'WAN critical path s',
         'WAN levels', 'Verify ms'], rows)]
    return out


def hyperweb_tables():
    out = ['### Hyperweb: directory and revocation trees', table(
        ['Depth', 'Capacity', 'Flat bitmap', 'Membership path B', 'Non-membership permutations',
         'Non-membership S-box constraints', 'Index increment cannot wrap'],
        [(d, f'{2**d:.2e}', binary_size(2**d // 8), d * NODE_B, 2 * d, 2 * d * SBOXES_PER_PERMUTATION, 'yes' if 2**d + 1 < GOLDILOCKS_P else 'no')
         for d in (20, HYPERWEB_DEPTH, 40, 62)])]
    M = SubtreeHologramModel
    lo, hi = M.root_proof_bytes(2), M.root_proof_bytes(16)
    five, three = silicon_row(SILICON_NODES[2]), silicon_row(SILICON_NODES[3])
    out += ['### Hyperweb: three accumulation tiers', table(
        ['Tier', 'Object', 'Wire', 'CPU verify', 'Silicon verify (model)'],
        [('0, session', 'SpongeMacaroon or Compact1122 with key', '161 B to 1,218 B', '1.8 us (macaroon, measured)', 'under 1 us'),
         ('1, streaming edge', 'affine fold of a running claim, opening deferred', f'{EDGE_FOLD_B:,} B', 'not built',
          f"{three['fold_us']:.0f} to {five['fold_us']:.0f} us"),
         ('2, checkpoint', 'SuccinctSubtreeAggregate over a causal cut', f'{kib(lo)} to {kib(hi)} KiB',
          f'{HOLOGRAM_VERIFY_MS} ms (measured)', f"{three['verify_fast_us']:.1f} to {five['verify_slow_us']:.1f} us")])]
    return out


def silicon_tables():
    out = ['### QSAG-NI: logic budget (model)', table(
        ['Block', 'kGE', 'Share'],
        [(name, f'{k:.0f}', f'{100 * k / SILICON_LOGIC_KGE:.1f}%') for name, k in SILICON_BLOCKS_KGE] +
        [('Total logic', f'{SILICON_LOGIC_KGE:.0f}', '100.0%')])]
    rows = []
    for node in SILICON_NODES:
        r = silicon_row(node)
        rows.append((r['node'], f"{r['area_small']:.2f} / {r['area_large']:.2f}", f"{r['ghz']}", f"{r['mw']:.0f}",
                     f"{r['verify_slow_us']:.1f} / {r['verify_fast_us']:.1f}",
                     f"{r['energy_slow_uj']:.2f} / {r['energy_fast_uj']:.2f}", f"{r['fold_us']:.0f}", r['merge_ms']))
    out += ['### QSAG-NI: area, latency and energy by process node (model)', table(
        ['Node', 'Area mm2 (128 / 512 KiB SRAM)', 'Clock GHz', 'Active mW',
         'Verify one aggregate us (Keccak / Poseidon2 root)', 'Energy uJ', 'Edge fold us', 'Merge prove ms'], rows)]
    return out


def generated(link_mbps=100.0):
    out = [BEGIN]
    out += ['### Measured: one JortsPoseidon2 shard as a single WHIR instance', table(
        ['Signers', 'Variables', 'Regime', 'Tag', 'Proof B', 'CPU prove s', 'GPU prove s',
         'Verify ms (all workers)', 'Verify ms (1 core)'],
        [(x.signers, x.num_vars, x.regime, x.tag, x.proof_b, x.cpu_prove_s,
          'not measured' if x.gpu_prove_s is None else x.gpu_prove_s, x.verify_ms, x.verify_1core_ms)
         for x in (SHARD, SHARD_P2, SHARD_K256, SHARD_K512)])]

    out += ['### Exact: signature and trace geometry by Jorts tree height', table(
        ['Height', 'Signatures per key', 'Signature B', 'Active trace rows', 'Rows per signer', 'Signers at 24 / 25 / 26 variables'],
        [(h, 2**h, jorts_sig_bytes(h), jorts_active_rows(h), ROWS_PER_SIGNER,
          ' / '.join(str(2**v // (ROWS_PER_SIGNER * TRACE_COLUMNS)) for v in (24, 25, 26)))
         for h in (6, 10, 16, 20)])]

    out += subtree_tables() + dual_path_tables()

    rows = []
    for n in (2_048, 8_192, 131_072, 1_048_576):
        k = ceildiv(n, 128)
        total = k * SHARD.proof_b
        rows.append((n, k, total, total * 8 / (link_mbps * 1e6), k * SHARD.gpu_prove_s, k * SHARD.verify_1core_ms,
                     f"{total / SubtreeHologramModel.plan(n, 512)['root_b']:,.0f}x"))
    out += ['### Baseline: direct verification of every 128-signer shard proof', table(
        ['Validators', 'Shards', 'Sum of shard proofs B', f'Transfer s at {link_mbps:.0f} Mbps', 'Total GPU-s',
         'Verify core-ms', 'Against the WAN root proof'], rows)]

    out += hyperweb_tables() + silicon_tables()

    out += ['### WHIR query schedules', table(
        ['log2 blowup', 'Tags 4, 9 (unbounded queries)', 'Tags 5, 7, 10', 'Tags 6, 8'],
        [(b, ceildiv(512, b) + 2, q57, q68)
         for b, q57, q68 in ((2, 202, 216), (4, 102, 109), (6, 70, 74), (8, 52, 56))]), END]
    return '\n\n'.join(out)


def self_test():
    M = SubtreeHologramModel
    # Wire and trace arithmetic.
    assert JORTS_SIG_B == 4_328 and JORTS_H20_SIG_B == 4_776 and CORDUROY_SIG_B == 76_896
    assert jorts_active_rows(6) == 470 and jorts_active_rows(20) == 498 < ROWS_PER_SIGNER
    assert [2**v // (ROWS_PER_SIGNER * TRACE_COLUMNS) for v in (24, 25, 26)] == [128, 256, 512]
    assert COMPACT1122_B + VOTE_HEADER_B == 1_218 <= PACKET_PAYLOAD_B
    assert COMPACT1122_B + VOTE_HEADER_B > QUIC_FLOOR_PAYLOAD_B
    assert [ceildiv(512, b) + 2 for b in (2, 4, 6, 8)] == [258, 130, 88, 66]
    assert SUBTREE_HEADER_B == 40 and SUBTREE_PUBLIC_WORDS * 8 == 112
    assert SBOXES_PER_PERMUTATION == 118
    # Root proof size is a function of the last arity only, and grows by under 10 KiB per doubling.
    sizes = {a: M.root_proof_bytes(a) for a in M.ARITIES}
    assert [kib(sizes[a]) for a in M.ARITIES] == ['311.8', '321.2', '330.6', '340.2'], sizes
    assert all(0 < sizes[2 * a] - sizes[a] < 10 * 1024 for a in (2, 4, 8))
    assert [kib(M.logup_gkr_bytes(a)) for a in M.ARITIES] == ['28.9', '31.6', '34.5', '37.5']
    # Schedules.
    assert M.uniform_schedule(12, 4) == (4, 4) and M.uniform_schedule(7_813, 4) == (4,) * 7
    assert M.uniform_schedule(1, 4) == (4,) and M.uniform_schedule(782, 4) == (4,) * 5
    assert M.min_hop_schedule(8) == (8,) and M.min_hop_schedule(32) == (8, 4)
    assert M.min_hop_schedule(40) == (8, 8) and M.min_hop_schedule(196) == (16, 16)
    assert M.min_hop_schedule(1_954) == M.min_hop_schedule(2_048) == (16, 16, 8)
    assert M.min_hop_schedule(98) == (16, 8)
    # Two quaternary levels beat one 16-ary level in time and in root size.
    assert 2 * M.MERGES[4].gpu_s < M.MERGES[16].gpu_s and sizes[4] < sizes[16]
    # Headline critical paths.
    lan = lambda n: M.plan(n, 128, M.uniform_schedule(ceildiv(n, 128), 4))
    assert [round(lan(n)['critical_gpu_s'], 2) for n in (1_500, 10_000, 100_000, 1_000_000)] == [2.38, 3.14, 3.52, 4.28]
    assert round(lan(1_048_576)['critical_gpu_s'], 2) == 4.28 and round(lan(1_000_000)['critical_cpu_merge_s'], 2) == 13.17
    assert [round(M.plan(n, 512)['critical_gpu_s'], 2) for n in (100_000, 131_072, 1_000_000, 1_048_576)] == [8.85, 8.85, 9.53, 9.53]
    assert round(M.plan(2_048, 256)['critical_gpu_s'], 2) == 3.83 < BEAM_SLOT_S
    assert round(M.plan(16_384, 256)['critical_gpu_s'], 2) == 4.51
    wan = M.plan(1_048_576, 512)
    assert wan['leaves'] == 2_048 and wan['depth'] == 3 and kib(wan['root_b']) == '330.6'
    assert round(wan['direct_b'] / wan['root_b']) == 3_368
    assert round(1_048_576 // 128 * SHARD.proof_b / wan['root_b']) == 10_781
    assert HOLOGRAM_VERIFY_MS < HOLOGRAM_VERIFY_GATE_MS
    # Leaf model stays inside its measured anchors: slower than the round-0 commit alone,
    # faster than the measured CPU child.
    for leaf in M.LEAVES.values():
        assert (leaf.commit0_s or 0) < leaf.gpu_s < leaf.cpu_child_s and leaf.vram_gib < 12
    # Live path.
    assert BITMAP_MTU_CROSSOVER == 9_088
    assert bitmap_certificate_bytes(9_088) == PACKET_PAYLOAD_B < bitmap_certificate_bytes(9_089)
    assert ceildiv(10_000, 8) > PACKET_PAYLOAD_B
    # Hyperweb.
    assert PRINCIPALS == 88 * 10**9 and HYPERWEB_DEPTH == 37 and 2**37 > PRINCIPALS > 2**36
    assert round(math.log2(PRINCIPALS), 2) == 36.36
    assert EDGE_FOLD_B == 3_104 and round(EDGE_FOLD_B / 1024, 2) == 3.03
    assert 2 * 37 == 74 and 74 * SBOXES_PER_PERMUTATION == 8_732
    assert 2**62 + 1 < GOLDILOCKS_P < 2**64
    assert M.sparse_leaf_rows(128, 37) == 558_848 and 37 * NODE_B == 1_184
    # Silicon.
    assert SILICON_LOGIC_KGE == 954.0 < 1_000
    rows = {n[0]: silicon_row(n) for n in SILICON_NODES}
    assert round(rows['3 nm']['area_small'], 2) == 0.08 and round(rows['5 nm']['area_large'], 2) == 0.19
    assert round(rows['28 nm']['area_small'], 2) == 0.89 and round(rows['28 nm']['area_large'], 2) == 1.52
    assert round(rows['3 nm']['verify_fast_us'], 1) == 6.8 and round(rows['5 nm']['verify_slow_us'], 1) == 17.0
    assert round(rows['3 nm']['energy_fast_uj'], 2) == 0.49 and round(rows['5 nm']['energy_slow_uj'], 2) == 1.45  # 1.445
    assert round(rows['3 nm']['fold_us']) == 82 and round(rows['5 nm']['fold_us']) == 90
    # Source drift guards on load-bearing facts. Not a security proof or a Rust test.
    checks = {
        'crates/qsag-agg/src/sig.rs': ['WOTS_CHAINS: usize = 128', 'WOTS_TARGET_SUM: usize = 192',
                                       'JORTS_XMSS_HEIGHT: usize = 6', 'JortsPoseidon2H20'],
        'crates/qsag-agg/src/arithmetize.rs': ['DEFAULT_SHARD_PCS_NUM_VARS: usize = 24'],
        'crates/qsag-agg/src/recursive.rs': [
            'pub const SUBTREE_PUBLIC_WORDS: usize = 14', 'b"QSAGSTA1"', 'pub struct SuccinctSubtreeAggregate',
            'pub struct SubtreeLeafMergeRelation', 'pub struct SubtreeInternalMergeRelation',
            'pub struct RosterRootStatement', 'pub fn verify_succinct_subtree_aggregate_against_roster_root',
            'matches!(fan_in, 2 | 4 | 8 | 16)', 'c[0].0.max_key_idx >= c[1].0.min_key_idx', 'fn with_sparse_roster'],
        'crates/qsag-agg/src/pcs.rs': ['MAX_GPU_PCS_NUM_VARS: usize = 26', 'by_blowup([202, 102, 70, 52])',
                                       'by_blowup([216, 109, 74, 56])'],
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
    return 'PASS: arithmetic, schedules, model anchors, source guards, and all generated documentation tables match.'


SUMMARY = (
    'Measured: a 128-signer shard is 445,566 B, 3.67 s on a Core i9-12900, 1.56 s on a Radeon RX 6750 XT; '
    f'one hologram root proof verifies in {HOLOGRAM_VERIFY_MS} ms on one core. '
    'Model: subtree recursion folds any number of shards into one root proof of 312 to 340 KiB; '
    'a million validators take 4.28 s (128-signer shards, arity 4, seven levels) or 9.53 s '
    '(512-signer shards, three levels) of critical-path proving with every stage on a GPU. '
    'Merge-node and GPU-leaf times, the hyperweb tiers and the silicon budget are projections.\n\n')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--self-test', action='store_true')
    p.add_argument('--write-tables', action='store_true', help='replace the marked tables in the companion report')
    p.add_argument('--subtree-hologram', action='store_true', help='print only the subtree recursion tables')
    p.add_argument('-o', '--output', type=Path, help='write the summary and tables here; use ./-o for a literal -o filename')
    p.add_argument('--link-mbps', type=float, default=100.0, help='link rate for the transfer column')
    args = p.parse_args()
    if not args.link_mbps > 0:
        p.error('--link-mbps must be positive')
    if args.write_tables:
        if args.link_mbps != 100.0:
            p.error('--write-tables requires default parameters to preserve self-test reproducibility')
        content = DOC.read_text()
        start = content.index(BEGIN)
        end = content.index(END) + len(END)
        DOC.write_text(content[:start] + generated() + content[end:])
    status = self_test() if args.self_test else 'Scaling model only; no prover executed.'
    tables = '\n\n'.join(subtree_tables()) if args.subtree_hologram else generated(args.link_mbps)
    if args.output:
        if args.output.resolve() in (DOC.resolve(), Path(__file__).resolve()):
            p.error('output must not overwrite either owned source file')
        args.output.write_text(status + '\n\n' + SUMMARY + tables + '\n')
    print(status if args.self_test else status + '\n\n' + SUMMARY + tables)


if __name__ == '__main__':
    main()
