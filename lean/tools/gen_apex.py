"""Generate the apex roster: Qsag/Apex.lean, QsagChallenge.lean and comparator.json.

Each roster entry names an existing theorem. Its signature is copied verbatim from the source file
into a restatement `Qsag.Apex.<name>`, proved by citing the original. The same restatements go to
both the solution-side module (`Qsag/Apex.lean`) and the challenge (`QsagChallenge.lean`), so the
comparator checks that the solution's apex statements are exactly the challenge's, and replays the
whole dependency closure through every kernel. No prover is invoked here.

  python3 tools/gen_apex.py
"""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]

# (tier, source module, theorem name as written after `theorem`, namespace of the source theorem
#  relative to `Qsag` ('' for top level))
ROSTER = [
    # Tier 1: field / tower / Poseidon2 / Keccak algebra and sponge framing
    (1, 'Goldilocks', 'goldilocksReduce128Spec_sound', ''),
    (1, 'Goldilocks', 'Goldilocks.mul_inv_cancel', ''),
    (1, 'BinaryTower', 'towerMul_cancel_left', ''),
    (1, 'BinaryTower', 'ghashDiff_roots_bound', ''),
    (1, 'BinaryTower', 'packTowerLenBlock_injective', ''),
    (1, 'Keccak', 'be_injective', ''),
    (1, 'Keccak', 'encodeMultiFrame_injective', ''),
    (1, 'Keccak', 'chiWordBit_eq_keccakChiBit', ''),
    (1, 'Keccak', 'cshake256Xof_empty_eq_shake256Xof', ''),
    (1, 'Poseidon2', 'poseidon2Perm12Inv_left_inv', ''),
    (1, 'Poseidon2', 'poseidon2Perm12Inv_right_inv', ''),
    (1, 'Poseidon2', 'bytesToLimbs56_injective', ''),
    # Tier 2: threshold approval, BDOZ MAC-before-open, KOS
    (2, 'IdealTsig', 'thresholdApproval_requires_honest_party', ''),
    (2, 'IdealTsig', 'corrupt_threshold_allows_unilateral_sign', ''),
    (2, 'IdealTsig', 'duplicate_corrupt_parties_rejected', ''),
    (2, 'IdealTsig', 'out_of_range_corrupt_parties_rejected', ''),
    (2, 'UcGames', 'ratLe_zero_den_false', ''),
    (2, 'MaliciousSecurity', 'bdoz_pair_key_recovery', ''),
    (2, 'MaliciousSecurity', 'bdoz_2lane_mac_soundness', ''),
    (2, 'MaliciousSecurity', 'mac_before_open_released_origin', ''),
    (2, 'MaliciousSecurity', 'mac_before_open_blocks_faulted_cut_leakage', ''),
    (2, 'Preprocessing', 'kos_interactive_check_sound', ''),
    (2, 'Preprocessing', 'kos_single_bit_does_not_pin_key', ''),
    # Tier 3: hypertree EUF-CMA and threshold-to-single-signer indistinguishability
    (3, 'HypertreeEufCma', 'hypertree_forgery_break_of_signingLog', ''),
    (3, 'HypertreeEufCma', 'hypertree_euf_cma_advantage_bound', ''),
    (3, 'HypertreeEufCma', 'forsItsrBreak_empty_log', ''),
    (3, 'HypertreeEufCma', 'eufCmaWin_rejects_signed_message', ''),
    (3, 'ThresholdMpc', 'thresholdStatelessCheckedSign_eq_evalStatelessCheckedSign', ''),
    (3, 'ThresholdMpc', 'threshold_sig_perfectly_indistinguishable_from_single_signer', ''),
    (3, 'ThresholdMpc', 'rss_threshold_sig_independent_of_quorum_and_sharing', ''),
    (3, 'ThresholdMpc', 'shamir_threshold_sig_independent_of_threshold_quorum_and_sharing', ''),
    (3, 'ThresholdMpc', 'threshold_sig_hedged_statistical_distance_zero', ''),
    # Tier 4: concrete UC simulator
    (4, 'UcGames', 'shamir_share_pad_rebalance', ''),
    (4, 'MaliciousSecurity', 'bdoz_tampered_opening_accepting_keys_le_one', ''),
    (4, 'MaliciousSecurity', 'bdoz_tag_tamper_rejected', ''),
    (4, 'IdealTsig', 'ucSimulatorTsig_hop1_perfect', ''),
    (4, 'IdealTsig', 'tsig_real_eq_ideal_or_forgery', ''),
    (4, 'IdealTsig', 'tsigForgery_keys_le', ''),
    (4, 'IdealTsig', 'ucSimulatorTsig_advantage_bound', ''),
    (4, 'IdealTsig', 'ucSimulatorTsig_distinguisher_breaks_generator', ''),
    (4, 'IdealTsig', 'ucSimulatorTsig_advantage_bound_gf4', ''),
    (4, 'IdealTsig', 'tsigRealOutcome_gf4_signs_and_rejects', ''),
    # Tier 5: succinct aggregation
    (5, 'Aggregation', 'sumcheck_false_claim_accepting_without_hit_count_zero', ''),
    (5, 'Aggregation', 'sumcheck_false_claim_accepting_challenges_le', ''),
    (5, 'Aggregation', 'sumcheck_production_error_lt', ''),
    (5, 'Aggregation', 'basefold_query_miss_bound', ''),
    (5, 'Aggregation', 'basefold_production_query_miss_lt', ''),
    (5, 'Aggregation', 'succinct_aggregation_soundness_error_bound', ''),
    (5, 'Aggregation', 'merge_tree_all_nodes_sound', ''),
    (5, 'Aggregation', 'succinct_degree9_round_rejected', ''),
    (5, 'Aggregation', 'succinct_duplicate_query_rejected', ''),
    # Tier 6: compiled-archive extraction, constant-time noninterference, mutation teeth
    (6, 'ElfParse', 'parseArMember_subslice', ''),
    (6, 'ElfParse', 'extractAllRlibFuncs_provenance', ''),
    (6, 'ElfParse', 'x86_rlib_extracted_slices', ''),
    (6, 'ElfParse', 'aarch64_rlib_extracted_slices', ''),
    (6, 'ElfParse', 'x86_rlib_extraction_detects_code_flip', ''),
    (6, 'ElfBinaryVerify', 'checkElfSliceWithCert_sound', ''),
    (6, 'ElfBinaryVerify', 'mutant_secret_branch_rejected', ''),
    (6, 'ElfBinaryVerify', 'mutant_secret_lut_rejected', ''),
    (6, 'ElfBinaryVerify', 'mutant_variable_shift_rejected', ''),
    (6, 'ElfFixtureVerify', 'rlib_x86_every_symbol_three_way_ni_sound', ''),
    (6, 'ElfFixtureVerify', 'rlib_aarch64_every_symbol_three_way_ni_sound', ''),
    (6, 'ElfFixtureVerify', 'genuine_certificate_rejects_unwiped_neon_mutant', ''),
    (6, 'ElfFixtureVerify', 'certificate_not_transferable', ''),
    (6, 'McRefine', 'ct_eq_32_x86_64_mc_refines', ''),
    (6, 'McRefine', 'ct_eq_32_aarch64_mc_refines', ''),
    (6, 'McRefine', 'ct_memzero_x86_64_mc_refines', ''),
    (6, 'McRefine', 'ct_memzero_aarch64_mc_refines', ''),
    (6, 'McRefine', 'ct_eq_bytes_x86_64_mc_refines', ''),
    (6, 'McRefine', 'goldilocks_add_ct_x86_64_mc_refines', ''),
    (6, 'McRefine', 'goldilocks_sub_ct_x86_64_mc_refines', ''),
    (6, 'McRefine', 'goldilocks_mul_ct_x86_64_mc_refines', ''),
    (6, 'McRefine', 'goldilocks_mul_ct_aarch64_mc_refines', ''),
    (6, 'McRefine', 'ct_eq_32_x86_64_mutant_refuted', ''),
    (6, 'McRefine', 'ct_eq_32_x86_64_secret_branch_rejected', ''),
    (6, 'McRefine', 'goldilocks_mul_ct_x86_64_mutant_refuted', ''),
    (6, 'McRefine', 'goldilocks_mul_ct_aarch64_secret_branch_rejected', ''),
]
EXTRA = root / 'tools' / 'apex_roster_extra.json'
if EXTRA.exists():
    ROSTER += [tuple(e) for e in json.loads(EXTRA.read_text())]

TIERS = {
    1: 'Field, tower, Poseidon2 and Keccak algebra and sponge framing',
    2: 'Threshold approval, BDOZ MAC-before-open and key-recovery alternative, KOS correlation check',
    3: 'Hypertree EUF-CMA extraction and bound; threshold-to-single-signer indistinguishability',
    4: 'Concrete UC simulator',
    5: 'Succinct aggregation soundness',
    6: 'Compiled-archive extraction, constant-time noninterference and machine-code refinement',
}

# Namespaces the source module has open around its theorems.
OPENS = {'IdealTsig': 'CommRingOps', 'UcGames': 'CommRingOps'}

OPEN = {'(': ')', '[': ']', '{': '}', '⟨': '⟩'}
CLOSE = set(OPEN.values())


def top_level_positions(text, token):
    depth = 0
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif depth == 0 and text.startswith(token, i):
            yield i
        i += 1


def signature(module, name):
    src = (root / 'Qsag' / f'{module}.lean').read_text()
    m = re.search(rf'^(?:protected )?theorem {re.escape(name)}(?=[\s:({{\[])', src, re.M)
    assert m, (module, name)
    rest = src[m.end():]
    end = None
    for pos in top_level_positions(rest, ':='):
        after = rest[pos + 2:]
        if after.startswith(' by') or after.startswith('\n') or after.startswith(' by\n'):
            end = pos
            break
    if end is None:
        end = next(top_level_positions(rest, ':='))
    # Theorems written with pattern-matching equations have no `:=` before the first `|` arm.
    for pos in top_level_positions(rest[:end], '\n'):
        if re.match(r'\n\s*\| ', rest[pos:]):
            end = pos
            break
    sig = rest[:end].rstrip()
    colon = next(top_level_positions(sig, ':'))
    binders = sig[:colon]
    explicit = []
    for group in re.findall(r'\(([^()]*?):', binders):
        explicit += group.split()
    return sig, explicit


def apex_name(name):
    return name.replace('.', '_')


def body():
    out = []
    names = []
    for tier in sorted(TIERS):
        entries = [e for e in ROSTER if e[0] == tier]
        if not entries:
            continue
        out.append(f'/-! ## Tier {tier}. {TIERS[tier]} -/\n')
        for _, module, name, ns in entries:
            sig, explicit = signature(module, name)
            qual = 'Qsag.' + (ns + '.' if ns else '') + name
            apex = apex_name(name)
            names.append(f'Qsag.Apex.{apex}')
            args = ''.join(' ' + a for a in explicit)
            prefix = f'open {ns} in\n' if ns else ''
            if module in OPENS:
                prefix += f'open {OPENS[module]} in\n'
            out.append(f'{prefix}theorem {apex}{sig} :=\n  _root_.{qual}{args}\n')
    return '\n'.join(out), names


def modules():
    seen = []
    for _, module, _, _ in ROSTER:
        if module not in seen:
            seen.append(module)
    return seen


HEADER = '''module
/-
# {title}

{blurb}

Every theorem below restates, with its full type, a theorem proved in the imported modules, and
is proved by citing it. The definitions the statements mention are the ones in those modules;
`comparator.json` lists the names, and the comparator checks statement equality, definitional
agreement, the axiom policy (`propext`, `Quot.sound`) and replays the dependency closure.
Generated by tools/gen_apex.py; edit the roster there.
-/

{imports}

public section
namespace Qsag.Apex
open Qsag
set_option autoImplicit false

'''

text, names = body()
imports = '\n'.join(f'public import Qsag.{m}' for m in modules())
(root / 'Qsag' / 'Apex.lean').write_text(HEADER.format(
    title='Qsag.Apex — apex theorem roster (solution side)',
    blurb='Solution-side restatements of the apex roster. `QsagChallenge` carries the same statements.',
    imports=imports) + text + '\nend Qsag.Apex\n')
(root / 'QsagChallenge.lean').write_text(HEADER.format(
    title='QsagChallenge — apex theorem roster (challenge side)',
    blurb='Challenge-side statements of the apex roster. This module does not import `Qsag.Apex`.',
    imports=imports) + text + '\nend Qsag.Apex\n')
(root / 'comparator.json').write_text(json.dumps({
    'challenge_module': 'QsagChallenge',
    'solution_module': 'Qsag',
    'theorem_names': names,
    'definition_names': [],
    'permitted_axioms': ['propext', 'Quot.sound'],
}, indent=2) + '\n')
print(f'{len(names)} apex theorems across tiers {sorted(set(e[0] for e in ROSTER))}')
