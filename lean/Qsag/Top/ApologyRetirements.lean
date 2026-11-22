module
/-
# Qsag.Top.ApologyRetirements — top-level index of the theorems that replace four header gaps

This module makes four additive modules reachable from `Qsag.Top` and re-audits their headline
theorems through the owning modules' certificates. It states nothing new.

1. `Qsag.Oracle.Sponge`, scope paragraph (encodings only, no statement about permutation
   queries): `Qsag.Oracle.SpongeDomainSeparation`.
2. `Qsag.Spec.IdealSign`, item 7 (no machine with a key-reveal output refines the behaviour
   after `.corrupt`): `Qsag.Spec.CorruptibleSignSimulation`.
3. `Qsag.Top.Credentials` (the SPDZ gate model returns `cfg.oprf` by fiat, issuance stores
   attributes without a transcript, MAC-key secrecy not modelled):
   `Qsag.Protocol.Credentials.ToprfSpdzArithmeticRefinement`.
4. `Qsag.Top.Custody` (no `Spec.Refines` witness packaged for the machine equalities, the toy
   certificate tag reveals the key, the two violation probabilities are not bounded):
   `Qsag.Custody.KeyHidingAuthCustodyBound` and `Qsag.Top.CustodyKeyHidingBound`.

What each module proves and what it leaves open is stated in its own header; the falsifiability
witnesses are paired in `Qsag.Tests.ApologyRetirementTeeth`.
-/

public import Qsag.Oracle.SpongeTwoWayIndifferentiability
public import Qsag.Spec.CorruptibleSignSimulation
public import Qsag.Protocol.Credentials.ToprfSpdzArithmeticRefinement
public import Qsag.Top.CustodyKeyHidingBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

#verify_constructive
  Qsag.sponge_distinct_inputs_terminal_disjoint_or_cap_collision
  Qsag.sponge_output_queries_disjoint_or_cap_collision
  Qsag.absorbPayload_output_queries_disjoint_or_cap_collision
  Qsag.cshake256_output_queries_disjoint_or_cap_collision
  Qsag.keccak_qsag_tags_output_queries_disjoint_or_cap_collision
  Qsag.evalSponge_congr_on_queries
  Qsag.spongeReal_eq_ideal_of_no_cap_bad
  Qsag.sponge_cap_bad_bound
  Qsag.sponge_multi_domain_ro_indistinguishability_bound
  Qsag.keccak_cshake_tags_ro_indistinguishability_bound
  Qsag.keccak_cshake_tags_ro_bound_430_bits_at_q2pow40
  Qsag.Spec.latchedCorruptibleSigner_adaptive_view_eq_simulator
  Qsag.Spec.latchedCorruptibleSigner_simulated_by_idealSignCorruptible
  Qsag.Spec.latchedCorruptibleSigner_run_projects_to_ideal
  Qsag.Spec.latchedCorruptibleSigner_unexposed_run_safe
  Qsag.SpdzToprf.spdzEval_sound_or_mac_forgery
  Qsag.SpdzToprf.piToprfRealSpdz_sound_or_mac_forgery
  Qsag.SpdzToprf.evalFooled_macKey_unique
  Qsag.SpdzToprf.spdz_mac_forgery_game_bound
  Qsag.SpdzToprf.goldilocksExt2_card_bits
  Qsag.SpdzToprf.spdzEval_macKey_zero_leakage
  Qsag.SpdzToprf.piToprfRealSpdz_macKey_zero_leakage
  Qsag.SpdzToprf.spdzEval_honest_complete
  Qsag.SpdzToprf.piToprfRealSpdz_issue_accept_checks
  Qsag.SpdzToprf.piToprfRealSpdz_issue_binding_or_collision
  Qsag.KeyHidingCustody.tagForge_prf_hop
  Qsag.KeyHidingCustody.encFreshTagGame_random_function_bound
  Qsag.KeyHidingCustody.prfCustodyTag_unforgeable
  Qsag.KeyHidingCustody.custodianKeys_forgery_union_bound
  Qsag.KeyHidingCustody.prfTag_view_key_hiding
  Qsag.Top.rssSharedRelease_admits_reference_traces
  Qsag.Top.thresholdServiceShared_prefixEquivalent_ideal
  Qsag.Top.thresholdDurableShared_prefixEquivalent_ideal

#verify_kernel
  Qsag.Spec.latchedCorruptibleSigner_refines_simulator
  Qsag.SpdzToprf.piToprfRealSpdzGuarded_dataRefines
  Qsag.Top.rssSharedRelease_refines_reference
  Qsag.Top.thresholdServiceShared_refines_ideal
  Qsag.Top.thresholdDurableShared_refines_ideal

end Qsag.Top
end
