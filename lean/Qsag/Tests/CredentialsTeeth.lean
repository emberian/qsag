module
public import Qsag.Protocol.Threshold.ThresholdMlDsaSecurity
public import Qsag.Math.MlDsaField
public import Qsag.Math.MlDsaNtt
public import Qsag.Math.CyclotomicRlwe
public import Qsag.Math.GoldilocksBase
/-
# Qsag.Tests.CredentialsTeeth — teeth and witnesses for the credential modules

* Root attestation (`BlindVcQromSecurity`): a signature that verifies when the raw 142-byte
  attestation message is used as the ML-DSA message representative is rejected by the FIPS 204
  check; an encoding without the issuer key digest is not injective.
* Hidden-party opening (`AdvancedMpcAndCreds`, `RepetitionCutAndChoose`): with an all-zero
  table of check values all 256 hidden parties pass.
* Ternary model: tightness of the two-of-three count, witnesses, and the constant-hash
  collision instances of the rewound-view extractor.
-/

public import Qsag.Protocol.Credentials.BlindVcCollisionFinder
public import Qsag.Protocol.Credentials.RepetitionCutAndChoose
public import Qsag.Math.Counting
public import Qsag.Math.Goldilocks
public import Qsag.Math.Lattices
public import Qsag.Oracle.FrozenChallengeGame
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
public import Qsag.Protocol.Credentials.BlindVcQromSecurity
public import Qsag.Spec.IdealCred
public import Qsag.Top.Credentials
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## Root attestation -/

/-- Challenge hash that returns its message-representative argument: it separates message
representatives. -/
def teethEchoChalHash (mu : List UInt8) (_w1 : Fin 4 → NatTree 8) : List UInt8 := mu

/-- The all-zero response with the raw attestation message as challenge bytes. -/
def teethRawMessageSig : ThresholdSignSig :=
  ⟨teethZeroFields.message, fun _ => PolyTree.zero 8, mldsaZeroHints204, 0⟩

/-- The check that feeds the raw message directly to the algebraic core as `μ` (bypassing
message-representative hashing) accepts `teethRawMessageSig`. -/
theorem teeth_raw_message_check_accepts :
    mldsaVerify teethEchoChalHash (fun _ => PolyTree.zero 8) (fun _ _ => PolyTree.zero 8)
      (fun _ => PolyTree.zero 8) teethZeroFields.message
      teethRawMessageSig.cTilde teethRawMessageSig.z teethRawMessageSig.h = true :=
  mldsaVerify_echo_zero_accepts teethZeroFields.message

/-- **Message-representative tooth.** A concrete signature accepted when the raw message stands in for the
message representative is rejected once the FIPS 204 representative is computed, for every
issuer key. -/
theorem tooth_raw_message_signature_rejected_by_fips204_check :
    ∃ (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
      (sampleInBall : List UInt8 → Poly256) (A : PolyMat4) (t1 : PolyVec4)
      (f : IssuerRootAttestationFields) (sig : ThresholdSignSig),
      mldsaVerify chalHash sampleInBall A t1 f.message sig.cTilde sig.z sig.h = true ∧
      ∀ issuerPk : List UInt8,
        verifyIssuerRootAttestation chalHash sampleInBall A t1 issuerPk f sig = false :=
  ⟨teethEchoChalHash, fun _ => PolyTree.zero 8, fun _ _ => PolyTree.zero 8,
    fun _ => PolyTree.zero 8, teethZeroFields, teethRawMessageSig,
    teeth_raw_message_check_accepts,
    fun issuerPk => verifyIssuerRootAttestation_rejects_raw_message_signature issuerPk
      (fun _ _ _ h => h) teeth_raw_message_check_accepts⟩

#verify_constructive teeth_raw_message_check_accepts
  tooth_raw_message_signature_rejected_by_fips204_check
  tooth_attestation_msg_without_key_digest_not_injective
#tooth_pair verifyIssuerRootAttestationBytes_accepts_core vs
  tooth_raw_message_signature_rejected_by_fips204_check
-- `teethZeroFields`, `teethLegacyAttestationMsg` and
-- `tooth_attestation_msg_without_key_digest_not_injective` are proved in
-- `Protocol/Credentials/BlindVcQromSecurity` and paired there with
-- `IssuerRootAttestationFields.message_injective`: the shared field projections sit under the
-- sealed body of `IssuerRootAttestationFields.message`.

/-! ## Hidden-party opening of the `N = 256` presentation -/

/-- With no nonzero check value the opening check passes for all 256 hidden parties. -/
theorem tooth_zero_defect_table_all_parties_pass :
    ¬ (FrozenChallenge.countIf
        (fun h => credentialGgmCheckDefects (fun _ : Fin credentialSdParties => credentialFp5Zero) h)
        CutAndChoose.limboParties ≤ 1) := by
  have hAll : (fun h => credentialGgmCheckDefects
      (fun _ : Fin credentialSdParties => credentialFp5Zero) h) = (fun _ => true) :=
    funext (fun h => credentialGgmCheckDefects_zero h)
  rw [hAll, FrozenChallenge.countIf_true, CutAndChoose.limboParties_length]
  decide

#verify_constructive tooth_zero_defect_table_all_parties_pass
#tooth_pair CutAndChoose.DefectChecker.open_count_le_one vs tooth_zero_defect_table_all_parties_pass

/-- With all check values zero, every one of the 256 challenge bytes of a one-repetition
opening round is accepted: the bound `≤ 1` needs the nonzero check value. -/
theorem tooth_opening_round_zero_defects_all_bytes_accepted :
    ¬ (qsum (256 ^ 1) (fun ch =>
        if credentialSdOpeningAccepts 1 (fun _ _ => credentialFp5Zero) ch.val = true
        then 1 else 0) ≤ 1) := by
  have hAll : ∀ ch : Nat,
      credentialSdOpeningAccepts 1 (fun _ _ => credentialFp5Zero) ch = true := by
    intro ch
    exact credentialSdOpeningAccepts_zero 1 ch
  rw [qsum_congr (fun ch => by rw [hAll ch.val])]
  simp only [↓reduceIte, qsum_const]
  decide

-- `inhabited_opening_round_nonzero_defect` is proved in `Protocol/Credentials/BlindVcQromSecurity`,
-- which also certifies its inhabitedness pair (cited below).
#verify_constructive tooth_opening_round_zero_defects_all_bytes_accepted
  inhabited_opening_round_nonzero_defect
#tooth_pair credentialSd_opening_bad_count_le_one vs
  tooth_opening_round_zero_defects_all_bytes_accepted
#verify_inhabited credentialSd_opening_bad_count_le_one inhabited_opening_round_nonzero_defect

/-! ## TOPRF group roles -/

/-! `toprfRotation204_not_constant` (the third role of group `(0, 1)` is not the fixed third
holder) is proved in `Protocol/Threshold/ThresholdMlDsaAndToprf`, the module that owns
`toprfGroupRoles204` and `toprfHolders`; it is audited here. -/


/-! ## Ternary model -/

theorem tooth_single_rep_two_of_three_tight :
    ∃ p : Fin 3 → Bool, fin3AllTrue p = false ∧
      qsum 3 (fun e => if p e = true then 1 else 0) = 2 ∧ ¬ (2 ^ 1 * 2 ^ 1 < 3 ^ 1) :=
  ⟨fun e => decide (e.1 < 2), by rw [fin3AllTrue_eq]; decide, by decide, by decide⟩

theorem fin3_not_all_count_witness :
    ∃ p : Fin 3 → Bool, fin3AllTrue p = false ∧
      qsum 3 (fun e => if p e = true then 1 else 0) ≤ 2 :=
  ⟨fun e => decide (e.1 < 2), by rw [fin3AllTrue_eq]; decide, by decide⟩

theorem vcMerkleTree_opening_witness :
    ∃ (epoch : UInt64) (tree : VcMerkleTree 0) (layer : Nat) (leaf : Lane6) (steps : List (Bool × Lane6)),
      steps.length = 0 ∧ evalVcMerklePathBool epoch layer leaf steps = vcMerkleTreeRoot epoch layer tree :=
  let z6 : Lane6 :=
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  ⟨0, .leaf z6, 0, z6, [], rfl,
    by rw [evalVcMerklePathBool_nil, vcMerkleTreeRoot.public_eq_1]⟩

/-- The repaired language has false instances even for a constant hash. The previous
collision-in-language disjunct made every statement true for that hash. -/
theorem blindVcParallelIop_false_statement_witness
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D) (k : Nat) :
    ∃ stmt, ¬ (blindVcParallelIop H prgExpand k).inLang stmt := by
  let z6 : Lane6 := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
    Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let z4 : Lane4 := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let stmt : BlindVcPublicStatement :=
    { schema := ⟨0, 1, by decide, by rw [vcSmallMaxAttrs_eq]; decide⟩, treeDepth := 0,
      presNonce := Vec.replicate 32 0, issuerEpoch := 0, accumulatorRoot := z6,
      presCommit := z6, scopeTag := z6, verifierScopeLimbs := z4,
      disclosedAttrs := [(0, Goldilocks.zero), (0, Goldilocks.zero)] }
  refine ⟨stmt, ?_⟩
  intro hLang
  obtain ⟨wit, hw⟩ := (blindVcParallelIop_inLang_iff H prgExpand k stmt).mp hLang
  have hNd := (vcCheckDisclosedStrictAsc_bounds_and_nodup hw.strictAsc).2
  exact absurd hNd (by decide)

/-- A constant hash and two concretely different views do trigger the event. The
candidate table is retained, rather than replacing it by an unrelated global collision. -/
theorem vcRewoundCommitConflict_constant_hash
    (nonce : Vec UInt8 32) (idx : Nat) (o : OpenedBlindVcRep) :
    let bad := { o with
      viewE := { o.viewE with attrShares := [] }
      viewE1 := { o.viewE with attrShares := [Goldilocks.zero] } }
    VcRewoundCommitConflict (fun _ => []) nonce idx bad bad bad := by
  intro bad
  apply Or.inl
  refine ⟨?_, by simp only [vcCommitPartyView.public_eqs]⟩
  intro he
  have hh := congrArg PartyVcRepView.attrShares he
  change [Goldilocks.zero] = [] at hh
  cases hh

/-- The concrete conflicting-view construction returns an actual collision. -/
theorem vcRewoundCollisionFinder_constant_hash
    (nonce : Vec UInt8 32) (idx : Nat) (o : OpenedBlindVcRep) :
    let bad := { o with
      viewE := { o.viewE with attrShares := [] }
      viewE1 := { o.viewE with attrShares := [Goldilocks.zero] } }
    (vcRewoundCollisionFinder (fun _ => []) (by intro _; decide)
      nonce idx bad bad bad).isSome = true := by
  intro bad
  rw [vcRewoundCollisionFinder_isSome]
  exact decide_eq_true (vcRewoundCommitConflict_constant_hash nonce idx o)

#verify_constructive tooth_single_rep_two_of_three_tight fin3_not_all_count_witness
  vcMerkleTree_opening_witness blindVcParallelIop_false_statement_witness
  vcRewoundCommitConflict_constant_hash vcRewoundCollisionFinder_constant_hash
#tooth_pair fin3_not_all_count_le_two vs tooth_single_rep_two_of_three_tight
#verify_inhabited fin3_not_all_count_le_two fin3_not_all_count_witness
#tooth_pair word64_mod3_bad_count_le vs tooth_single_rep_two_of_three_tight
#verify_inhabited word64_mod3_bad_count_le fin3_not_all_count_witness
#verify_inhabited vcMerkleTree_opening_sound vcMerkleTree_opening_witness

end Qsag

public section
namespace Qsag
theorem tooth_rss3_unverified_shift_corrupts_recon :
    ∃ zSh : Rss3Share,
      rss3Recon (rss3MulStep zSh zSh Fq204.zero Fq204.zero Fq204.one) ≠
        Fq204.mul (rss3Recon zSh) (rss3Recon zSh) ∧
      sacAcceptRepeated [ext6Zero]
        (rss3ToSacGate zSh zSh Fq204.zero Fq204.zero Fq204.one ext6Zero zSh
          (ext6EmbedFq Fq204.one)) = false :=
  ⟨⟨Fq204.zero, Fq204.zero, Fq204.zero⟩,
    by
      rw [rss3MulStep_recon]
      simp only [rss3Recon.public_eqs]
      decide,
    by
      rw [sacAcceptRepeated.public_eqs, List.all_cons, List.all_nil, Bool.and_true,
        Bool.eq_false_iff]
      intro hAcc
      rw [sacAccept204_iff_tau_eq, rss3ToSacGate_error_eq_delta, sacTripleError204_eq] at hAcc
      have h0 := congrArg Ext6Fq204.a0 hAcc
      simp only [rss3ToSacGate.public_eqs, rss3Recon.public_eqs, ext6Sub_eq, ext6Scale_eq,
        ext6Add.public_eqs, ext6EmbedFq.public_eqs, ext6Zero_eq] at h0
      exact absurd h0 (by decide)⟩

theorem rss3_repeated_sacrifice_witness :
    ∃ (x y : Rss3Share) (r0 r1 deltaZ : Fq204)
      (a : Ext6Fq204) (b : Rss3Share) (deltaC : Ext6Fq204) (chis : List Ext6Fq204),
      deltaZ ≠ Fq204.zero ∧
      sacAcceptRepeated chis (rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = true :=
  ⟨⟨Fq204.zero, Fq204.zero, Fq204.zero⟩, ⟨Fq204.zero, Fq204.zero, Fq204.zero⟩,
   Fq204.zero, Fq204.zero, Fq204.one, ext6Zero,
   ⟨Fq204.zero, Fq204.zero, Fq204.zero⟩, ext6Zero, [ext6Zero], by decide,
   by
     rw [sacAcceptRepeated.public_eqs, List.all_cons, List.all_nil, Bool.and_true,
       sacAccept204_iff_tau_eq, rss3ToSacGate_error_eq_delta, sacTripleError204_eq]
     simp only [rss3ToSacGate.public_eqs, rss3Recon.public_eqs, ext6Sub_eq, ext6Scale_eq,
       ext6Add.public_eqs, ext6Zero_eq, Ext6Fq204.mk.injEq]
     decide⟩


#tooth_pair rss3_repeated_sacrifice_pq256 vs tooth_rss3_unverified_shift_corrupts_recon
#verify_inhabited rss3_repeated_sacrifice_pq256 rss3_repeated_sacrifice_witness


/-- Concrete honest channel run witness for `Top.credPort_authenticated_by_channel_contract`
    backed by `Spec.checkedChannel_contract` (`0` adversary spoofing, `1` honest issuer message). -/
theorem inhabited_credPort_channel_contract :
    ∃ (admits : List Spec.ChannelEvent → Prop),
      Spec.AuthenticatedChannelContract admits ∧
      ∃ (adversaryIds : List Nat) (tr pre post : List Spec.ChannelEvent)
        (m : Spec.ChannelMsg) (party : Spec.CredParty),
        admits tr ∧
        tr = pre ++ .deliver m :: post ∧
        Top.CredPartyInCommittee party ∧
        Top.credChannelEndpointPort adversaryIds m.sender = party.port := by
  let m : Spec.ChannelMsg := ⟨0, 1, 0, [0x01]⟩
  have hCommittee : Top.CredPartyInCommittee Spec.CredParty.issuer := by
    rw [Top.CredPartyInCommittee.public_eq_1]; exact trivial
  have hPort : Top.credChannelEndpointPort [99] m.sender = Spec.CredParty.issuer.port := by
    have hRound := Top.credChannelEndpointPort_roundtrip [99] .issuer hCommittee
      (by rw [Top.credPartyEndpointId.public_eq_1]; decide)
    rw [Top.credPartyEndpointId.public_eq_1] at hRound
    exact hRound
  refine ⟨fun tr => Spec.channelRun tr [] [] = true, Spec.checkedChannel_contract,
    [99], [.send m, .deliver m], [.send m], [], m, .issuer, ?_, rfl, hCommittee, hPort⟩
  have hRun := Spec.checkedChannel_contract.honestRunsAdmitted [m] (by decide)
  rw [Spec.honestChannelRun.public_eqs] at hRun
  exact hRun

#verify_constructive Qsag.inhabited_credPort_channel_contract


#verify_inhabited Qsag.Top.credPort_authenticated_by_channel_contract
  Qsag.inhabited_credPort_channel_contract


/-! ## Independent verifier ledger regression roster

These executable witnesses are proved next to the machine so its non-exposed implementation
remains private; importing this module builds and constructively audits the witnesses.
-/
export Spec (tooth_verifiers_independent_and_replay_refused
  tooth_invalid_proof_does_not_consume_challenge
  tooth_ledger_capacity_expiry_and_fresh_issuance
  tooth_capacity_shared_by_scopes_not_verifiers
  tooth_failed_issue_retains_pruning
  tooth_global_challenge_blacklist_wrong
  tooth_consume_before_verify_wrong
  tooth_reissue_resurrects_consumed_nonce_wrong
  tooth_replay_not_prevented_really_replays)

#verify_constructive Spec.idealCredMachine_challenge_at_most_once_trace
  Spec.idealCredMachine_presentation_preserves_other_verdict
  Spec.tooth_verifiers_independent_and_replay_refused
  Spec.tooth_invalid_proof_does_not_consume_challenge
  Spec.tooth_ledger_capacity_expiry_and_fresh_issuance
  Spec.tooth_capacity_shared_by_scopes_not_verifiers
  Spec.tooth_failed_issue_retains_pruning
  Spec.tooth_global_challenge_blacklist_wrong
  Spec.tooth_consume_before_verify_wrong
  Spec.tooth_reissue_resurrects_consumed_nonce_wrong
  Spec.tooth_replay_not_prevented_really_replays

end Qsag
end
