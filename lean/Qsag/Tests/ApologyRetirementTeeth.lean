module
/-
# Qsag.Tests.ApologyRetirementTeeth — falsifiability pairs for the four apology-retirement modules

Every pair is a security theorem and a counterexample or refusal theorem of the same module,
audited here across the import boundary through the owning module's certificates
(`#verify_constructive` in the owning module; `#tooth_pair` checks that both are constructive,
share a domain operation and that the tooth has a refutation-shaped conclusion).

* Sponge (`Qsag.Oracle.SpongeDomainSeparation`): with no capacity every one-block input has a
  two-block state collision; without the padding property two different
  `(blocks, output block)` pairs share a terminal query with no capacity event; at one capacity
  value the bad event is certain and an explicit adaptive distinguisher has advantage `1/2`.
* Corruptible signer (`Qsag.Spec.CorruptibleSignSimulation`): a simulator holding a different
  key is told apart by one `.exposeKey`, also when the public keys agree; before `.corrupt`
  every `.inject` is rejected; an exposed run reuses an epoch; no `DataRefines` exists through
  the simulator's interface maps for the burn-scheme instance.
* SPDZ TOPRF (`Qsag.Protocol.Credentials.ToprfSpdzArithmeticRefinement`): a tampered output
  share is rejected by the blinded MAC check, at the evaluation and at the machine; the same
  tampered run released without the check is not the PRF value; a forged issuance commitment
  and a failed opening are refused.
* Custody tags (`Qsag.Custody.KeyHidingAuthCustodyBound`, `Qsag.Top.CustodyKeyHidingBound`):
  a tag equal to the key is forged with probability one after one honest tag; the counting
  bound fails for a one-function support; a certificate with a wrong PRF tag is refused.
-/

public import Qsag.Top.Signing
public import Qsag.Top.Credentials
public import Qsag.Top.CustodyKeyHidingBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ApologyRetirementTeeth

set_option autoImplicit false

/-! ## 1. Sponge permutation-query disjointness and the random-function bound -/

#tooth_pair Qsag.sponge_terminal_query_ne_or_cap_event vs
  Qsag.tooth_zero_capacity_state_collision
#tooth_pair Qsag.sponge_output_queries_disjoint_or_cap_collision vs
  Qsag.tooth_unpadded_length_extension_shares_output_query
#tooth_pair Qsag.sponge_cap_bad_bound vs Qsag.tooth_zero_capacity_bad_event_certain
#tooth_pair Qsag.sponge_multi_domain_ro_indistinguishability_bound vs
  Qsag.tooth_zero_capacity_distinguisher_advantage_half
#verify_inhabited Qsag.keccak_qsag_tags_output_queries_disjoint_or_cap_collision
  Qsag.witness_keccak_qsag_tags_distinct

/-! ## 2. Key-reveal simulation of the corruptible signer -/

#tooth_pair Qsag.Spec.latchedCorruptibleSigner_adaptive_view_eq_simulator vs
  Qsag.Spec.corruptibleSignSimulator_wrong_key_view_differs
#tooth_pair Qsag.Spec.latchedCorruptibleSigner_adaptive_view_eq_simulator vs
  Qsag.Spec.corruptToyTwoKey_same_pk_wrong_key_view_differs
#tooth_pair Qsag.Spec.latchedCorruptibleSigner_simulated_by_idealSignCorruptible vs
  Qsag.Spec.idealSignCorruptible_inject_rejected_before_corrupt
#tooth_pair Qsag.Spec.latchedCorruptibleSigner_simulated_by_idealSignCorruptible vs
  Qsag.Spec.corruptibleSignSimulator_wrong_key_not_refinement
#tooth_pair Qsag.Spec.latchedCorruptibleSigner_run_projects_to_ideal vs
  Qsag.Spec.corruptibleSignSimulator_register_rejected_unexposed
#tooth_pair Qsag.Spec.latchedCorruptibleSigner_unexposed_run_safe vs
  Qsag.Spec.latchedCorruptibleSigner_exposed_run_reuses_epoch
#tooth_pair Qsag.Spec.latchedCorruptibleSigner_run_projects_to_ideal vs
  Qsag.Spec.latchedCorruptibleSigner_no_dataRefines_to_ideal
#verify_inhabited Qsag.Spec.latchedCorruptibleSigner_simulated_by_idealSignCorruptible
  Qsag.Spec.witness_latchedCorruptibleSigner_exposed_run

/-! ## 3. Share-level SPDZ arithmetic of the TOPRF -/

#tooth_pair Qsag.SpdzToprf.spdzEval_sound_or_mac_forgery vs
  Qsag.SpdzToprf.tooth_tampered_output_share_rejected
#tooth_pair Qsag.SpdzToprf.spdzEval_sound_or_mac_forgery vs
  Qsag.SpdzToprf.tooth_unchecked_release_is_wrong


#verify_inhabited Qsag.SpdzToprf.spdzEval_sound_or_mac_forgery
  Qsag.SpdzToprf.witness_spdzEval_accepted
#verify_inhabited Qsag.SpdzToprf.spdz_mac_forgery_game_bound
  Qsag.SpdzToprf.witness_spdz_mac_forgery_game
#verify_inhabited Qsag.SpdzToprf.tooth_tampered_output_share_rejected
  Qsag.SpdzToprf.witness_tamper_teeth

/-! ## 4. Key-hiding custody tags -/

#tooth_pair Qsag.KeyHidingCustody.prfTag_forgery_bound vs
  Qsag.KeyHidingCustody.tooth_toyCustodyTag_one_query_forgery
#tooth_pair Qsag.KeyHidingCustody.prfCustodyTag_unforgeable vs
  Qsag.KeyHidingCustody.tooth_toyPermitTag_one_query_forgery
#tooth_pair Qsag.KeyHidingCustody.encFreshTagGame_random_function_bound vs
  Qsag.KeyHidingCustody.tooth_singleFunction_support_forged
#tooth_pair Qsag.Top.prfCertCustody_forgery_carries_prf_tag vs
  Qsag.Top.tooth_prfCertLayer_wrong_tag_rejected

end Qsag.ApologyRetirementTeeth
end
