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
public import Qsag.Protocol.Credentials.ToprfMachine
public import Qsag.Top.Credentials
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## Root attestation -/

/-- Challenge hash that returns its message-representative argument: it separates message
representatives. -/
def teethEchoChalHash (mu : List UInt8) (_w1 : Fin 4 → NatTree 8) : List UInt8 := mu

def teethZeroFields : IssuerRootAttestationFields :=
  ⟨Vec.replicate 32 0, 0, lane6Zero, Vec.replicate 32 0⟩

/-- The hint tree with no hint bit set. -/
def teethZeroHint : (d : Nat) → HintTree d
  | 0 => .leaf false
  | d + 1 => .branch (teethZeroHint d) (teethZeroHint d)

theorem teethZeroHint_weight : ∀ d : Nat, HintTree.weight (teethZeroHint d) = 0
  | 0 => by rw [teethZeroHint]; exact (HintTree.weight_leaf false).trans rfl
  | d + 1 => by rw [teethZeroHint, HintTree.weight_branch, teethZeroHint_weight d]

/-- The all-zero response with the raw attestation message as challenge bytes. -/
def teethRawMessageSig : ThresholdSignSig :=
  ⟨teethZeroFields.message, fun _ => PolyTree.zero 8, fun _ => teethZeroHint 8, 0⟩

/-- The check that feeds the raw message to the algebraic core as `μ` (the wrapper before this
stage) accepts `teethRawMessageSig`. -/
theorem teeth_raw_message_check_accepts :
    mldsaVerify teethEchoChalHash (fun _ => PolyTree.zero 8) (fun _ _ => PolyTree.zero 8)
      (fun _ => PolyTree.zero 8) teethZeroFields.message
      teethRawMessageSig.cTilde teethRawMessageSig.z teethRawMessageSig.h = true := by
  have hz : infNormVec4 teethRawMessageSig.z < mldsa44Gamma1 - mldsa44Beta := by
    rw [infNormVec4_eq]
    decide +kernel
  have hh : hintWeightVec4 teethRawMessageSig.h ≤ mldsa44Omega := by
    rw [hintWeightVec4_eq]
    show HintTree.weight (teethZeroHint 8) + HintTree.weight (teethZeroHint 8) +
      HintTree.weight (teethZeroHint 8) + HintTree.weight (teethZeroHint 8) ≤ mldsa44Omega
    rw [teethZeroHint_weight]
    decide
  simp only [mldsaVerify, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hz, hh⟩, rfl⟩

/-- **BACKLOG-57 tooth.** A concrete signature accepted when the raw message stands in for the
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

/-- The attestation bytes of the model before this stage: `QSAG.ROOT`, root tag, epoch, root.
The issuer key digest is absent. -/
def teethLegacyAttestationMsg (f : IssuerRootAttestationFields) : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x4F, 0x4F, 0x54] ++
  f.issuerRootTag.toList ++ encodeNatLeBytes 8 f.issuerEpoch.toNat ++
  encodeGoldilocksVecLe [f.accumulatorRoot.x0, f.accumulatorRoot.x1, f.accumulatorRoot.x2,
    f.accumulatorRoot.x3, f.accumulatorRoot.x4, f.accumulatorRoot.x5]

/-- Without the issuer key digest two different field tuples have the same bytes; the
attestation message with the digest separates them. -/
theorem tooth_attestation_msg_without_key_digest_not_injective :
    ∃ f g : IssuerRootAttestationFields,
      ¬ (f = g) ∧ teethLegacyAttestationMsg f = teethLegacyAttestationMsg g ∧
        ¬ (f.message = g.message) :=
  have hne : ¬ (teethZeroFields =
      { teethZeroFields with issuerPkDigest := Vec.replicate 32 1 }) := fun h => by
    have hd : (Vec.replicate 32 (0 : UInt8)).toList = (Vec.replicate 32 (1 : UInt8)).toList :=
      congrArg (fun x => x.issuerPkDigest.toList) h
    rw [Vec.toList_replicate, Vec.toList_replicate] at hd
    have hh := congrArg List.head? hd
    revert hh; decide
  ⟨teethZeroFields, { teethZeroFields with issuerPkDigest := Vec.replicate 32 1 },
    hne, rfl, fun hm => hne (IssuerRootAttestationFields.message_injective hm)⟩

#verify_constructive teeth_raw_message_check_accepts
  tooth_raw_message_signature_rejected_by_fips204_check
  tooth_attestation_msg_without_key_digest_not_injective
#tooth_pair verifyIssuerRootAttestationBytes_accepts_core vs
  tooth_raw_message_signature_rejected_by_fips204_check
#tooth_pair IssuerRootAttestationFields.message_injective vs
  tooth_attestation_msg_without_key_digest_not_injective

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
    rw [credentialSdOpeningAccepts_eq]
    apply List.all_eq_true.mpr
    intro idx _
    exact credentialGgmCheckDefects_zero _
  rw [qsum_congr (fun ch => by rw [hAll ch.val])]
  simp only [↓reduceIte, qsum_const]
  decide

/-- The hypothesis of the opening-round bound is satisfiable, and its bound is attained: with
one nonzero check value, at party 255, hiding party 255 passes, so the one-repetition opening
accepts the challenge byte 255. -/
theorem inhabited_opening_round_nonzero_defect :
    ∃ defect : Nat → Fin 256 → CredentialFp5,
      (∀ idx < 33, ∃ bad, defect idx bad ≠ credentialFp5Zero) ∧
      credentialGgmCheckDefects (defect 0) ⟨255, by decide⟩ = true ∧
      credentialSdOpeningAccepts 1 defect 255 = true := by
  have hGood : credentialGgmCheckDefects
      ((fun (_ : Nat) (p : Fin 256) (_ : Fin 5) =>
        if p.val = 255 then Goldilocks.one else Goldilocks.zero) 0) ⟨255, by decide⟩ = true := by
    apply (credentialGgmCheckDefects_eq_true_iff _ _).mpr
    intro p
    by_cases hp : p = ⟨255, by decide⟩
    · exact Or.inl hp
    · refine Or.inr (funext (fun i => ?_))
      have hv : ¬ (p.val = 255) := fun h => hp (Fin.ext h)
      rw [credentialFp5Zero_apply]
      show (if p.val = 255 then Goldilocks.one else Goldilocks.zero) = Goldilocks.zero
      exact ite_eq_right hv
  refine ⟨fun _ p _ => if p.val = 255 then Goldilocks.one else Goldilocks.zero,
    fun _ _ => ⟨⟨255, by decide⟩, fun he => ?_⟩, hGood, ?_⟩
  · have hc : Goldilocks.one = Goldilocks.zero :=
      (congrFun he 0).trans (credentialFp5Zero_apply 0)
    exact absurd hc (by decide)
  · rw [credentialSdOpeningAccepts_eq]
    apply List.all_eq_true.mpr
    intro idx hidx
    have h0 : idx = 0 := Nat.lt_one_iff.mp (List.mem_range.mp hidx)
    subst h0
    exact hGood

#verify_constructive tooth_opening_round_zero_defects_all_bytes_accepted
  inhabited_opening_round_nonzero_defect
#tooth_pair credentialSd_opening_bad_count_le_one vs
  tooth_opening_round_zero_defects_all_bytes_accepted
#verify_inhabited credentialSd_opening_bad_count_le_one inhabited_opening_round_nonzero_defect

/-! ## TOPRF group roles -/

/-- The third role of group `(0, 1)` is not the fixed third holder: roles rotate. (Moved from
`Protocol/Migration/HdToprfAndMigrationSecurity`, where it needed the bodies of the threshold
module.) -/
theorem toprfRotation204_not_constant :
    (toprfGroupRoles204 0 1).2.2 ≠ (toprfHolders 0 1).getD 2 0 := by
  rw [toprfGroupRoles204_digest, toprfHolders_zero_one]
  decide

#verify_constructive toprfRotation204_not_constant

/-! ## Ternary model -/

theorem tooth_single_rep_two_of_three_tight :
    ∃ p : Fin 3 → Bool, fin3AllTrue p = false ∧
      qsum 3 (fun e => if p e = true then 1 else 0) = 2 ∧ ¬ (2 ^ 1 * 2 ^ 1 < 3 ^ 1) :=
  ⟨fun e => decide (e.1 < 2), (fin3AllTrue_eq _).trans (by decide), by decide, by decide⟩

theorem fin3_not_all_count_witness :
    ∃ p : Fin 3 → Bool, fin3AllTrue p = false ∧
      qsum 3 (fun e => if p e = true then 1 else 0) ≤ 2 :=
  ⟨fun e => decide (e.1 < 2), (fin3AllTrue_eq _).trans (by decide), by decide⟩

theorem vcMerkleTree_opening_witness :
    ∃ (epoch : UInt64) (tree : VcMerkleTree 0) (layer : Nat) (leaf : Lane6) (steps : List (Bool × Lane6)),
      steps.length = 0 ∧ evalVcMerklePathBool epoch layer leaf steps = vcMerkleTreeRoot epoch layer tree :=
  let z6 : Lane6 :=
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  ⟨0, .leaf z6, 0, z6, [], rfl,
    (evalVcMerklePathBool_nil 0 0 z6).trans (vcMerkleTreeRoot_leaf 0 0 z6).symm⟩

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
  obtain ⟨wit, hw⟩ := (blindVcParallelIop_inLang H prgExpand k stmt).mp hLang
  have h : vcCheckDisclosedStrictAsc 1 [(0, Goldilocks.zero), (0, Goldilocks.zero)] = true :=
    BlindVcWitnessValid.disclosed_strictAsc hw
  rw [vcCheckDisclosedStrictAsc_repeated_index] at h
  cases h

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
  have h1 := vcCommitPartyView_eq (fun _ => ([] : List UInt8)) nonce idx 1 bad.viewE1
    (vcPartyFinalOutAt bad.finalOuts 1)
  have h2 := vcCommitPartyView_eq (fun _ => ([] : List UInt8)) nonce idx 1 bad.viewE
    (vcPartyFinalOutAt bad.finalOuts 1)
  refine ⟨?_, h1.trans h2.symm⟩
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
  ⟨⟨Fq204.zero, Fq204.zero, Fq204.zero⟩, rss3_zero_shares_unit_shift_recon_ne,
    rss3_zero_shares_unit_shift_sacrifice_rejected⟩

theorem rss3_repeated_sacrifice_witness :
    ∃ (x y : Rss3Share) (r0 r1 deltaZ : Fq204)
      (a : Ext6Fq204) (b : Rss3Share) (deltaC : Ext6Fq204) (chis : List Ext6Fq204),
      deltaZ ≠ Fq204.zero ∧
      sacAcceptRepeated chis (rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = true :=
  ⟨⟨Fq204.zero, Fq204.zero, Fq204.zero⟩, ⟨Fq204.zero, Fq204.zero, Fq204.zero⟩,
   Fq204.zero, Fq204.zero, Fq204.one, ext6Zero,
   ⟨Fq204.zero, Fq204.zero, Fq204.zero⟩, ext6Zero, [ext6Zero], by decide,
   rss3_zero_shares_unit_shift_sacrifice_accepted⟩


#tooth_pair rss3_repeated_sacrifice_pq256 vs tooth_rss3_unverified_shift_corrupts_recon
#verify_inhabited rss3_repeated_sacrifice_pq256 rss3_repeated_sacrifice_witness

/-! ## `ToprfMachine`, `toprfCredentialImplementation`, Concrete `GF(p^5)` `GameBound` & `CredPort` Channel Contract -/

/-- Inhabitedness witness for `Top.blindVc_cut_and_choose_gameBound`: `faultyBlindVcProver`
    genuinely exhibits a nonzero gate defect `1 * 1 - 0 = 1 ≠ 0` at gate `0` in every repetition! -/
theorem inhabited_blindVc_cut_and_choose_gameBound :
    ∃ P : CutAndChoose.Prover BlindVcCommittedProof BlindVcFp5 BlindVcR2aMsg BlindVcFp5 BlindVcR2bMsg,
      ∀ j : Nat, BlindVcRepHasGateFault P.commit j :=
  ⟨faultyBlindVcProver, faultyBlindVcProver_has_gate_fault⟩

/-- Concrete honest issuance witness for `Top.piToprfCredService_issuance_authenticated` on `Spec.idealCredDemoConfig false`. -/
theorem inhabited_piToprfCredService_issuance :
    ∃ (cfg : Spec.IdealCredConfig Nat)
      (c₀ c' : PiToprfCredState Nat Nat)
      (tr : List ((Spec.CredPort × ToprfCredWire Nat) × Spec.IdealCredOutput Nat))
      (w : ToprfCredWire Nat),
      (piToprfCredService cfg).Init c₀ ∧
      (piToprfCredService cfg).ValidTrace c₀ tr c₀ ∧
      (piToprfCredService cfg).step c₀ (.issuer, w) = some (c', .issued 0) := by
  let cfg := Spec.idealCredDemoConfig false
  obtain ⟨c', hInit, hStep⟩ :=
    piToprfCredService_issuer_issues_at_init (Attr := Nat) cfg 1 11 1#256 0xCAFE#256
  exact ⟨cfg, PiToprfCredState.init cfg, c', [], .issueWire 1 [11] 1#256 0xCAFE#256,
    hInit, .nil _, hStep⟩

/-- Concrete 3-of-5 quorum witness for `partial_reserve_burns_without_recycle` where server 0
    durably commits `counter = 7` and server 1 fails I/O partway through `reserve_counters`. -/
theorem inhabited_partial_reserve_burns_without_recycle :
    ∃ (cfg : SpdzConfig) (pre : List SpdzCounterSlot) (failSlot : SpdzCounterSlot)
      (post : List SpdzCounterSlot) (counter items : Nat),
      cfg.Valid = true ∧
      cfg.threshold ≤ (pre ++ failSlot :: post).length ∧
      (pre ++ failSlot :: post).length ≤ cfg.servers ∧
      (∀ s ∈ pre ++ failSlot :: post, s.party < cfg.servers) ∧
      ((pre ++ failSlot :: post).map SpdzCounterSlot.party).Pairwise (· < ·) ∧
      (1 ≤ items ∧ items ≤ Spec.pqCredentialProfile.toprfMaxBatch) ∧
      (∀ s ∈ pre ++ failSlot :: post, spdzAdmitCounter s.lastCounter s.storeHighWater counter = true) ∧
      (∀ s ∈ pre, s.ioSucceeds = true) ∧
      failSlot.ioSucceeds = false :=
  spdz_partial_reserve_burns_witness

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
  have hRound := Top.credChannelEndpointPort_roundtrip [99] .issuer
    Top.credPartyInCommittee_issuer (by rw [Top.credPartyEndpointId_issuer]; decide)
  rw [Top.credPartyEndpointId_issuer] at hRound
  have hPort : Top.credChannelEndpointPort [99] m.sender = Spec.CredParty.issuer.port := hRound
  have hRun := Spec.checkedChannel_contract.honestRunsAdmitted [m] (by decide)
  rw [Spec.honestChannelRun_singleton] at hRun
  exact ⟨fun tr => Spec.channelRun tr [] [] = true, Spec.checkedChannel_contract,
    [99], [.send m, .deliver m], [.send m], [], m, .issuer, hRun, rfl,
    Top.credPartyInCommittee_issuer, hPort⟩

/-- The unauthenticated service has no `CredentialImplementation` for an honest issuer, while
`piToprfCredService` has `Top.toprfCredentialImplementation`. -/
theorem tooth_unauthenticated_service_lacks_the_piToprf_implementation {Attr O : Type}
    [DecidableEq Attr] (cfg : Spec.IdealCredConfig O) (hHonest : cfg.issuerCorrupt = false)
    (attr : Attr) :
    ∃ _impl : Top.CredentialImplementation Attr cfg (piToprfCredService (Attr := Attr) cfg),
      ¬ Nonempty (Top.CredentialImplementation Attr cfg
        (Top.unauthenticatedCredService (Attr := Attr) cfg)) :=
  ⟨Top.toprfCredentialImplementation Attr cfg,
    Top.unauthenticatedCredService_not_implementation cfg hHonest attr⟩

#verify_constructive
  Qsag.inhabited_blindVc_cut_and_choose_gameBound
  Qsag.inhabited_piToprfCredService_issuance
  Qsag.inhabited_partial_reserve_burns_without_recycle
  Qsag.tooth_unratcheted_failed_slot_recycles_counter
  Qsag.inhabited_credPort_channel_contract

#verify_inhabited Qsag.Top.blindVc_cut_and_choose_gameBound
  Qsag.inhabited_blindVc_cut_and_choose_gameBound
#verify_inhabited Qsag.Top.piToprfCredService_issuance_authenticated
  Qsag.inhabited_piToprfCredService_issuance
#verify_inhabited Qsag.partial_reserve_burns_without_recycle
  Qsag.spdz_partial_reserve_burns_witness
#verify_inhabited Qsag.Top.credPort_authenticated_by_channel_contract
  Qsag.inhabited_credPort_channel_contract

#tooth_pair Qsag.partial_reserve_burns_without_recycle vs
  Qsag.tooth_unratcheted_failed_slot_recycles_counter
#tooth_pair Qsag.Top.piToprfCredService_issuance_authenticated vs
  Qsag.tooth_unauthenticated_service_lacks_the_piToprf_implementation
end Qsag
end
