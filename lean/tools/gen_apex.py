"""Generate the apex roster: Qsag/Apex.lean, QsagChallenge.lean and comparator.json.

Each roster entry names an existing theorem. Its signature is copied verbatim from the source file
into a restatement `Qsag.Apex.<name>`, proved by citing the original. The same restatements go to
both the solution-side module (`Qsag/Apex.lean`) and the challenge (`QsagChallenge.lean`).
The latter uses intentional `by sorry` bodies, so the
comparator checks that the solution's apex statements are exactly the challenge's, and replays the
whole dependency closure through every kernel. No prover is invoked here.

  python3 tools/gen_apex.py
"""
from pathlib import Path
import json
import re
import sys

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
    (2, 'IdealTsig', 'unilateral_empty_quorum_rejected', ''),
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
    # Tier 4: concrete UC simulator over 128-bit BinaryTower
    (4, 'UcGames', 'shamir_share_pad_rebalance', ''),
    (4, 'MaliciousSecurity', 'bdoz_tampered_opening_accepting_keys_le_one', ''),
    (4, 'MaliciousSecurity', 'bdoz_tag_tamper_rejected', ''),
    (4, 'IdealTsig', 'ucSimulatorTsig_hop1_perfect', ''),
    (4, 'IdealTsig', 'tsig_real_eq_ideal_or_forgery', ''),
    (4, 'IdealTsig', 'tsigForgery_keys_le', ''),
    (4, 'IdealTsig', 'ucSimulatorTsig_advantage_bound', ''),
    (4, 'IdealTsig', 'ucSimulatorTsig_distinguisher_breaks_generator', ''),
    (4, 'IdealTsig', 'ucSimulatorTsig_advantage_bound_tower128', ''),
    (4, 'IdealTsig', 'ucSimulatorTsig_nonvacuous_sub_unity_tower128', ''),
    (4, 'IdealTsig', 'tsigRealOutcome_tower128_signs_and_rejects', ''),
    # Tier 5: GoldilocksExt4 multi-stage WHIR succinct aggregation and unforgeability
    (5, 'Aggregation', 'popcount_union_disjoint_eq_add', ''),
    (5, 'Aggregation', 'goldilocksExt4_mul_inv_cancel', 'Aggregation'),
    (5, 'Aggregation', 'goldilocksExt4_encodeBytes32_injective', 'Aggregation'),
    (5, 'Aggregation', 'sumcheck_degree8_ext4_roots_le_eight', 'Aggregation'),
    (5, 'Aggregation', 'whir_ood_pin_roots_le_degree', 'Aggregation'),
    (5, 'Aggregation', 'aggregateInstanceFrame_injective', 'Aggregation'),
    (5, 'Aggregation', 'bciksJohnsonQrom128_positive_slack', 'Aggregation'),
    (5, 'Aggregation', 'bciksJohnson_schedules_eq_minimum_queries', 'Aggregation'),
    (5, 'Aggregation', 'productionAggParams_queries_match_schedule', ''),
    (5, 'Aggregation', 'whir_query_miss_bound', ''),
    (5, 'Aggregation', 'whir_bciksJohnsonQrom128_query_miss_lt', 'Aggregation'),
    (5, 'Aggregation', 'whir_bciksJohnsonClassical128_total_error_bound', 'Aggregation'),
    (5, 'Aggregation', 'whir_bciksJohnsonQrom128_total_error_bound', 'Aggregation'),
    (5, 'Aggregation', 'succinct_aggregation_knowledge_soundness_thm', 'Aggregation'),
    (5, 'Aggregation', 'succinct_merge_tree_knowledge_soundness_thm', 'Aggregation'),
    (5, 'Aggregation', 'qsag_aggregate_unforgeability_reduction_thm', 'Aggregation'),
    (5, 'Aggregation', 'qsag_aggregate_unforgeability_reduction_of_statelessLog_thm', 'Aggregation'),
    (5, 'Aggregation', 'qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog_thm', 'Aggregation'),
    (5, 'Aggregation', 'rsSbox7TraceArith_lawful', 'Aggregation'),
    (5, 'Aggregation', 'honestSbox7WhirProof_accepts', 'Aggregation'),
    (5, 'Aggregation', 'succinct_knowledge_soundness_hypotheses_satisfiable', 'Aggregation'),
    (5, 'Aggregation', 'tooth_corrupted_round0_symbol_rejected', 'Aggregation'),
    (5, 'Aggregation', 'succinct_degree9_round_rejected', 'Aggregation'),
    (5, 'Aggregation', 'succinct_duplicate_query_rejected', 'Aggregation'),
    (5, 'Aggregation', 'tooth_whir_wrong_ood_challenge_rejected', 'Aggregation'),
    (5, 'Aggregation', 'tooth_whir_bad_pow_rejected', 'Aggregation'),
    (5, 'Aggregation', 'tooth_whir_wrong_params_rejected', 'Aggregation'),
    (5, 'Aggregation', 'aggregate_message_substitution_rejected', 'Aggregation'),
    (5, 'Aggregation', 'checkSbox7Trace_sound', 'Aggregation'),
    (5, 'Aggregation', 'checkSbox7Trace_complete', 'Aggregation'),
    (5, 'Aggregation', 'nineRoundSbox7Trace_sound', 'Aggregation'),
    (5, 'Aggregation', 'nineRoundSbox7Trace_complete', 'Aggregation'),
    (5, 'Aggregation', 'sbox7Trace_wrong_root_rejected', 'Aggregation'),
    (5, 'Aggregation', 'sbox7Trace_head_signature', 'Aggregation'),
    (5, 'Aggregation', 'sbox7WhirChain_sound', 'Aggregation'),
    (5, 'Aggregation', 'sbox7WhirChain_complete', 'Aggregation'),
    (5, 'Aggregation', 'buildSbox7WhirChain_seeds', 'Aggregation'),
    (5, 'Aggregation', 'nineRoundSbox7Whir_sound', 'Aggregation'),
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
    4: 'Concrete UC simulator over 128-bit BinaryTower',
    5: 'GoldilocksExt4 multi-stage WHIR succinct aggregation and unforgeability',
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


def explicit_binder_names(binders):
    explicit = []
    depth = 0
    start = None
    for i, ch in enumerate(binders):
        if depth == 0 and ch == '(':
            start = i + 1
            depth = 1
        elif ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
            if depth == 0 and start is not None:
                group = binders[start:i]
                start = None
                for pos in top_level_positions(group, ':'):
                    if not group.startswith(':=', pos):
                        explicit += group[:pos].split()
                        break
    return explicit


def signature(module, name):
    mod_path = root / 'Qsag' / f'{module}.lean'
    if not mod_path.exists():
        raise FileNotFoundError(f'Missing source module {mod_path} for {name}')
    src = mod_path.read_text()
    m = re.search(rf'^(?:protected )?theorem {re.escape(name)}(?=[\s:({{\[])', src, re.M)
    if not m:
        raise ValueError(f'Missing theorem `{name}` in Qsag/{module}.lean')
    rest = src[m.end():]
    candidates = []
    for pos in top_level_positions(rest, ':='):
        line_start = rest.rfind('\n', 0, pos) + 1
        if rest[line_start:pos].lstrip().startswith('let '):
            continue
        after = rest[pos + 2:]
        if after.startswith(' by') or after.startswith('\n') or after.startswith(' by\n'):
            candidates.append(pos)
            break
    if not candidates:
        for pos in top_level_positions(rest, ':='):
            line_start = rest.rfind('\n', 0, pos) + 1
            if not rest[line_start:pos].lstrip().startswith('let '):
                candidates.append(pos)
                break
    for tok in (' where\n', '\nwhere\n', ' where '):
        pos = next(top_level_positions(rest[:min(candidates)] if candidates else rest, tok), None)
        if pos is not None:
            candidates.append(pos)
    if not candidates:
        raise ValueError(f'Could not locate theorem body start for `{module}.{name}`')
    end = min(candidates)
    # Theorems written with pattern-matching equations have no `:=` before the first `|` arm.
    for pos in top_level_positions(rest[:end], '\n'):
        if re.match(r'\n\s*\| ', rest[pos:]):
            end = pos
            break
    sig = rest[:end].rstrip()
    colon = next(
        (p for p in top_level_positions(sig, ':') if not sig.startswith(':=', p)),
        None,
    )
    if colon is None:
        raise ValueError(f'Missing return-type colon in `{module}.{name}`')
    binders = sig[:colon]
    return sig, explicit_binder_names(binders)


def apex_name(name):
    return name.replace('.', '_')


def verify_roster():
    seen_apex = set()
    for tier, module, name, ns in ROSTER:
        if tier not in TIERS:
            raise ValueError(f'Unknown tier {tier} for {module}.{name}')
        mod_src = (root / 'Qsag' / f'{module}.lean').read_text()
        if ns and not re.search(rf'^namespace {re.escape(ns)}\b', mod_src, re.M):
            raise ValueError(f'Missing namespace `{ns}` in Qsag/{module}.lean for {name}')
        signature(module, name)
        apx = apex_name(name)
        if apx in seen_apex:
            raise ValueError(f'Duplicate apex theorem identifier `{apx}`')
        seen_apex.add(apx)


def body(challenge=False):
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
            proof = 'by sorry' if challenge else f'_root_.{qual}{args}'
            out.append(f'{prefix}theorem {apex}{sig} :=\n  {proof}\n')
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
uses the appropriate solution or challenge body. The definitions the statements mention are the ones in those modules;
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

def generated_files():
    verify_roster()
    text, names = body()
    imports = '\n'.join(f'public import Qsag.{m}' for m in modules())
    outputs = {'Qsag/Apex.lean': HEADER.format(
        title='Qsag.Apex — apex theorem roster (solution side)',
        blurb='Solution-side proofs. `QsagChallenge` carries identical statements with stub bodies.',
        imports=imports) + text + '\nend Qsag.Apex\n'}
    if '--apex-only' not in sys.argv[1:]:
        outputs['QsagChallenge.lean'] = HEADER.format(
            title='QsagChallenge — apex theorem roster (challenge side)',
            blurb='Intentional `by sorry` comparator problems. This module does not import `Qsag.Apex`.',
            imports=imports) + body(challenge=True)[0] + '\nend Qsag.Apex\n'
        outputs['comparator.json'] = json.dumps({
            'challenge_module': 'QsagChallenge',
            'solution_module': 'Qsag',
            'theorem_names': names,
            'definition_names': [],
            'permitted_axioms': ['propext', 'Quot.sound'],
        }, indent=2) + '\n'
        # One disk inventory drives the public import cone and the private axiom inventory.
        proof_modules = sorted(p.stem for p in (root / 'Qsag').glob('*.lean'))
        public_root = (root / 'Qsag.lean').read_text()
        public_root = re.sub(r'^public import Qsag\.[^\n]+\n', '', public_root, flags=re.M)
        outputs['Qsag.lean'] = public_root.rstrip() + '\n\n' + ''.join(
            f'public import Qsag.{m}\n' for m in proof_modules)
        audit = (root / 'AuditAxioms.lean').read_text()
        audit = re.sub(r'^import all Qsag\.[^\n]+\n', '', audit, flags=re.M)
        audit = audit.replace('import Qsag\n', 'import Qsag\n' + ''.join(
            f'import all Qsag.{m}\n' for m in proof_modules))
        audit = re.sub(r'  let auditedProofModules : Array Name := #\[.*?\n  \]',
            '  let auditedProofModules : Array Name := #[\n' +
            ',\n'.join(f'    `Qsag.{m}' for m in proof_modules) + '\n  ]', audit, flags=re.S)
        outputs['AuditAxioms.lean'] = audit
    return outputs, names


outputs, names = generated_files()
stale = [name for name, content in outputs.items() if (root / name).read_text() != content]
if '--check' in sys.argv[1:]:
    if stale:
        raise SystemExit('Stale generated files: ' + ', '.join(stale))
else:
    for name, content in outputs.items():
        (root / name).write_text(content)
print(f'{len(names)} apex theorems across tiers {sorted(set(e[0] for e in ROSTER))}')
