module
import all Qsag.Math.GoldilocksBase
/-
Nondegenerate instances, negative controls and consumer bridges for
`ComposedQsAgAndMergeSecurity`, `CrossProtocolAndDualOracleComposition` and
`HybridAddrPolicyAndFullPresetSecurity`.

The generic reductions in those modules are witnessed there by fixtures chosen for brevity
(`bad := True`, constant verifiers, the identity permutation, the constant-zero hash). Those
fixtures show that the hypotheses are jointly satisfiable. This module adds fixtures in which
the bad and forgery events are FALSE, the checked objects are computed by the modelled
constructions (`signAggNative` / `verifyAggNativeSig`, `poseidon2Perm12`, `cshakePrefix`), and
wrong-context or invalid constituents are rejected.

What the fixtures are and are not. `transparentVerify` is a non-succinct reference aggregator
(its "proof" is the signature table) retained for negative-control rejection tests; alongside it,
`boundary_of_hem_opening_batch` (proved in `ComposedQsAgAndMergeSecurity`) and
`hemOpeningShardVerify` connect `ExtractionBoundary` directly
to `HemExtractedOpeningBridge.verifyHemOpeningBatch` (`verifyOpeningBatch` + `verifyHemAffineWhir`)
composed with `SuccinctAggregationIop`. Similarly, alongside the lightweight `toyHash` /
`toyVerifier` negative controls, `cshakeHybridHash` (`evalCshake256Sponge keccakF1600`) and
`jortsNativeVerifier` (`verifyAggNativeSig compactAuditGeom`) instantiate `HybridSecurity` over
modelled cryptographic primitives (`real_hybrid_keybound_instance`).
-/
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
public import Qsag.Protocol.Aggregation.CrossProtocolAndDualOracleComposition
public import Qsag.Protocol.Signing.HybridAddrPolicyAndFullPresetSecurity
public import Qsag.Protocol.Aggregation.HemOpening
import all Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
import all Qsag.Protocol.Aggregation.CrossProtocolAndDualOracleComposition
import all Qsag.Protocol.Signing.HybridAddrPolicyAndFullPresetSecurity
import all Qsag.Protocol.Aggregation.HemOpening
import all Qsag.Oracle.Qrom
import all Qsag.Protocol.Aggregation.MultiRoundFsQrom
import all Qsag.Protocol.Aggregation.SuccinctAggregationIop
import all Qsag.Protocol.Threshold.ThresholdApproval
import all Qsag.Protocol.Aggregation.Aggregation
import all Qsag.Oracle.Sponge
import all Qsag.Oracle.Poseidon2
import all Qsag.Math.Goldilocks
import all Qsag.Math.Gf2Pow128
import all Qsag.Oracle.Keccak
import all Qsag.Protocol.Signing.Fips205
import all Qsag.Protocol.Aggregation.UcGames
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.CompositionInstances
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 1000000

theorem not_true_of_false {b : Bool} (h : b = false) : ¬ (b = true) :=
  fun h' => Bool.noConfusion (h'.symm.trans h)

/-! ## 1. Composed aggregation: accepted, approved, no bad event -/
section Composed
open Qsag.Composed

/-- Reference aggregator whose proof object is the signature table itself. Every active bit is
checked with the native verifier against the header's message for that validator. -/
def transparentVerify {n : Nat} (geom : AggSigGeometry) (pk : Fin n → AggValidatorPk)
    (sigs : Fin n → AggNativeSignature) (s : Shard n) : Bool :=
  (List.finRange n).all fun v =>
    !s.bitmap.getLsbD v.val ||
      verifyAggNativeSig geom (pk v) (s.header.mode.message v.val) (sigs v)

/-- The reference aggregator meets `ExtractionBoundary` for every `bad`, in particular for
`bad := fun _ => False`: extraction reads the table. -/
theorem transparent_boundary {n : Nat} (geom : AggSigGeometry) (custody : Fin n → Custody)
    (sigs : Fin n → AggNativeSignature) (bad : Shard n → Prop) :
    ExtractionBoundary geom custody
      (transparentVerify geom (fun v => (custody v).state.pk) sigs) bad := by
  refine ⟨fun s h => .inr fun v hv => ⟨sigs v, ?_⟩⟩
  unfold transparentVerify at h
  have hall := List.all_eq_true.mp h v (List.mem_finRange v)
  rw [hv] at hall
  simp only [Bool.not_true, Bool.false_or] at hall
  exact hall

/-- Two distinct secret seeds. -/
def skOf (v : Fin 2) : Digest4 :=
  if v.val = 0 then auditSkSeed
  else ⟨Goldilocks.ofNat 12, Goldilocks.ofNat 23, Goldilocks.ofNat 34, Goldilocks.ofNat 45⟩
def lane (a b c d : Nat) : Digest4 :=
  ⟨Goldilocks.ofNat a, Goldilocks.ofNat b, Goldilocks.ofNat c, Goldilocks.ofNat d⟩
/-- Public keys and signatures are literals so that each later check runs only the verifier;
`fixtures_are_modelled_outputs` ties them to the modelled key generation and signer. -/
def pkOf (v : Fin 2) : AggValidatorPk :=
  ⟨.xmssPoseidon2, auditPkSeed,
    if v.val = 0 then
      lane 4411130677596272051 12386187803866016865 4846206855630815541 13194810747827022671
    else
      lane 17576564533966561130 16051823357764822570 14727583026633534692 1732328166828656438⟩
def sigOf (v : Fin 2) : AggNativeSignature :=
  if v.val = 0 then
    ⟨.xmssPoseidon2, auditRRand, 0, [], [⟨37,
      [lane 8311586201798180139 8396487982263648832 16278201376156863497 5873789825944876137,
       lane 11009790873695555519 14395406594536956999 11951049901538821830 10044662254597907680],
      [lane 5524291857455771020 16376422686410664307 15963494650740044646
        18098363549869475062]⟩]⟩
  else
    ⟨.xmssPoseidon2, auditRRand, 1, [], [⟨45,
      [lane 7345396832099288313 5628321512706338704 2904634915904338214 11778081422095187519,
       lane 6519691662884691569 6995657412139860735 8574290930621241436 12609139020484668794],
      [lane 13388180661509288011 5130805258596798721 8406673262598715289
        15360960474733464499]⟩]⟩
/-- The literals are the outputs of `deriveAggPublicKey` and of the honest signer
`signAggNative` on `auditMsg` ("QSAG"), validator `v` at leaf `v`, with the target-sum
counters `37` and `45` found by search. -/
theorem fixtures_are_modelled_outputs : ∀ v : Fin 2,
    pkOf v = deriveAggPublicKey compactAuditGeom (skOf v) auditPkSeed ∧
    sigOf v = signAggNative compactAuditGeom (skOf v) (pkOf v) auditMsg auditRRand v.val
      (if v.val = 0 then 37 else 45) [] := by decide +kernel
def otherMsg : List UInt8 := [0x51, 0x53, 0x41, 0x48]

theorem native_accepts : ∀ v : Fin 2,
    verifyAggNativeSig compactAuditGeom (pkOf v) auditMsg (sigOf v) = true := by decide +kernel
theorem native_rejects_other_message : ∀ v : Fin 2,
    verifyAggNativeSig compactAuditGeom (pkOf v) otherMsg (sigOf v) = false := by decide +kernel
theorem native_rejects_other_key :
    verifyAggNativeSig compactAuditGeom (pkOf 1) auditMsg (sigOf 0) = false := by decide +kernel
theorem native_rejects_tampered_randomizer :
    verifyAggNativeSig compactAuditGeom (pkOf 0) auditMsg
      { sigOf 0 with rRand := auditPkSeed } = false := by decide +kernel

/-- 2-of-3 custody with one corrupt party; honest party `1` logged `auditMsg` in epoch 7. -/
def custodyOf (v : Fin 2) : Custody :=
  ⟨⟨pkOf v, 2, 3, [0], [auditMsg], []⟩, 7, [1],
    fun p ep msg => decide (p = 1 ∧ ep = 7 ∧ msg = auditMsg)⟩
def goodVerify : Shard 2 → Bool :=
  transparentVerify compactAuditGeom (fun v => (custodyOf v).state.pk) sigOf
def headerFor (mode : SigningMode) : Header :=
  ⟨[0xC0], .xmssPoseidon2, .bciksJohnsonQrom128, mode⟩
def goodHeader : Header := headerFor (.shared auditMsg)
def shardFor (h : Header) (b : BitVec 2) : Shard 2 :=
  ⟨h, b, [], 2, (Qsag.WhirSecurityRegime.bciksJohnsonQrom128).schedule 2⟩
def fullShard : Shard 2 := shardFor goodHeader 3#2
def goodTree : MergeTree 2 :=
  .branch (.leaf (shardFor goodHeader 1#2)) (.leaf (shardFor goodHeader 2#2)) 3#2

theorem good_full_accepts : goodVerify fullShard = true := by decide +kernel
theorem good_tree_accepts : checkTree goodHeader goodVerify 16 goodTree = true := by
  decide +kernel
theorem good_bits : ∀ v : Fin 2, goodTree.bitmap.getLsbD v.val = true := by decide +kernel
theorem good_participation : ∀ v : Fin 2,
    quorumParticipated (custodyOf v) auditMsg = true := by decide +kernel

theorem good_no_forgery (v : Fin 2) :
    ¬ QuorumForgery compactAuditGeom (custodyOf v) auditMsg := by
  rintro ⟨_, _, hq⟩
  rw [good_participation v] at hq
  cases hq

/-- Good regime of `merged_quorum_reduction`: the tree is accepted, no leaf is bad, no quorum
forgery exists, and the reduction resolves to the approval branch for both validators. -/
theorem good_regime_resolves (v : Fin 2) :
    quorumParticipated (custodyOf v) (goodHeader.mode.message v.val) = true ∧
    ¬ QuorumForgery compactAuditGeom (custodyOf v) (goodHeader.mode.message v.val) ∧
    ¬ ∃ s ∈ goodTree.leaves, False := by
  have hbad : ¬ ∃ s ∈ goodTree.leaves, False := fun ⟨_, _, h⟩ => h
  have hnf : ¬ QuorumForgery compactAuditGeom (custodyOf v)
      (goodHeader.mode.message v.val) := good_no_forgery v
  rcases merged_quorum_reduction compactAuditGeom custodyOf goodVerify (fun _ => False)
      (transparent_boundary compactAuditGeom custodyOf sigOf _) goodHeader goodTree
      good_tree_accepts v (good_bits v) with hb | hf | hq
  · exact absurd hb hbad
  · exact absurd hf hnf
  · exact ⟨hq, hnf, hbad⟩

theorem good_regime_instance : ∃ geom custody verify bad,
    ExtractionBoundary (n := 2) geom custody verify bad ∧
    ∃ s : Shard 2, ∃ v : Fin 2, verify s = true ∧ s.bitmap.getLsbD v.val = true ∧
    ∃ root tree, checkTree root verify 16 tree = true ∧ tree.bitmap.getLsbD v.val = true :=
  ⟨compactAuditGeom, custodyOf, goodVerify, fun _ => False,
    transparent_boundary compactAuditGeom custodyOf sigOf _, fullShard, 0,
    good_full_accepts, good_bits 0, goodHeader, goodTree, good_tree_accepts, good_bits 0⟩

/-- The bridge premises hold with `bad := fun _ => False` on the row-committed AIR: the
verifier is restricted to the shared-message mode, the statement is the two-key committee,
and the extracted trace is the honest one. Knowledge extraction is trivial here because the
verifier holds the signatures; a succinct verifier needs WHIR knowledge soundness instead. -/
def sharedVerify (s : Shard 2) : Bool :=
  goodVerify s && decide (s.header.mode = .shared auditMsg)
def committeeStmt : AggArithPublicStmt := ⟨compactAuditGeom, auditMsg, [pkOf 0, pkOf 1], 1⟩
theorem committee_trace_satisfied :
    traceSatisfiesAllConstraints committeeStmt
      (buildHonestAggExecutionTrace committeeStmt [sigOf 0, sigOf 1]) = true :=
  buildHonestAggExecutionTrace_satisfies_constraints committeeStmt _ (by decide +kernel) rfl
    (fun k hkP hkS => match k, hkP, hkS with
      | 0, _, _ => native_accepts 0
      | 1, _, _ => native_accepts 1
      | k + 2, h, _ => absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))
          (Nat.not_succ_le_zero k))
theorem committee_slots : ∀ v : Fin 2,
    committeeStmt.committeePks[v.val]? = some (custodyOf v).state.pk := by decide +kernel
theorem committee_trace_boundary :
    ExtractionBoundary compactAuditGeom custodyOf sharedVerify (fun _ => False) :=
  boundary_of_committee_trace compactAuditGeom custodyOf sharedVerify _
    (fun _ => committeeStmt) (fun v => v.val)
    (fun _ _ => .inr ⟨_, committee_trace_satisfied⟩)
    (fun s h => ⟨rfl, fun v _ => ⟨committee_slots v, by
      have h' : (goodVerify s && decide (s.header.mode = .shared auditMsg)) = true := h
      rw [of_decide_eq_true (Bool.and_eq_true_iff.mp h').2]
      rfl⟩⟩)
theorem shared_verify_accepts : sharedVerify fullShard = true := by decide +kernel
theorem shared_verify_rejects_per_signer_mode :
    sharedVerify (shardFor (headerFor (.perSigner [auditMsg, auditMsg])) 3#2) = false := by
  decide +kernel

/-- Concrete 1-level 8-bit `MerkleAddressLayout` (`65536` addresses = `u || v`) exercising both
`verifyOpeningBatch` path verification and `verifyHemAffineWhir` transcript verification without
storing native signatures in `Shard.proof`. -/
def compactMerkleLayout : MerkleAddressLayout 65536 8 where
  encode _ _ u v := ⟨u.toNat * 256 + v.toNat, by
    have hu : u.toNat < 256 := u.isLt
    have hv : v.toNat < 256 := v.isLt
    omega⟩
  decode x := some (0, 0, BitVec.ofNat 8 (x.val / 256), BitVec.ofNat 8 (x.val % 256))
  levels := 1
  nodes := 1
  decode_sound x l n u v h := by
    injection h with hTuple
    rcases Prod.mk.inj hTuple with ⟨_, hRest1⟩
    rcases Prod.mk.inj hRest1 with ⟨_, hUV⟩
    rcases Prod.mk.inj hUV with ⟨hu, hv⟩
    subst hu; subst hv
    apply Fin.ext
    have hx : x.val < 65536 := x.isLt
    have hDiv : (BitVec.ofNat 8 (x.val / 256)).toNat = x.val / 256 := by
      rw [BitVec.toNat_ofNat]; change (x.val / 256) % 256 = x.val / 256; omega
    have hMod : (BitVec.ofNat 8 (x.val % 256)).toNat = x.val % 256 := by
      rw [BitVec.toNat_ofNat]; change (x.val % 256) % 256 = x.val % 256; omega
    dsimp only; rw [hDiv, hMod]; omega
  decode_encode l n u v hl hn := by
    have hl0 : l = 0 := by omega
    have hn0 : n = 0 := by omega
    subst hl0; subst hn0
    have hu : u.toNat < 256 := u.isLt
    have hv : v.toNat < 256 := v.isLt
    have hDiv : (u.toNat * 256 + v.toNat) / 256 = u.toNat := by omega
    have hMod : (u.toNat * 256 + v.toNat) % 256 = v.toNat := by omega
    dsimp only
    rw [hDiv, hMod, BitVec.ofNat_toNat, BitVec.ofNat_toNat]
    rfl

def compactHemOracle : Fin 65536 → BitVec 8 := fun x => BitVec.ofNat 8 ((x.val + 0x5A) % 256)

def compactHemSlot : MerkleOpeningSlot 65536 8 where
  level := 0
  depth := 1
  readout := fun _ =>
    { rt := compactHemOracle (compactMerkleLayout.encode 0 0 0x11#8 0x22#8)
      idx := 0
      leaf := 0x11#8
      path := [0x22#8] }

def compactHemInst : HemWhirInstance QuarticGoldilocks where
  batchOracles := [fun _ => CommRingOps.one]
  batchClaims := [CommRingOps.one]
  initDomainPts := [CommRingOps.zero, CommRingOps.one]
  initDegBound := 0
  initMinAgree := 2
  initKernel := [CommRingOps.one]
  stages := []

def compactHemDecode : Fin 65536 → List (Option (MerkleOpeningValue 8)) →
    List (HemTranscriptRound QuarticGoldilocks)
  | _, [some _] =>
    [.cascade [CommRingOps.zero] [(CommRingOps.one, CommRingOps.zero)] [[CommRingOps.one]],
     .finalQuery [CommRingOps.one]]
  | _, _ => []

/-- Shard verifier backed by `verifyHemOpeningBatch` (`fullShard.proof = []`, zero signature table). -/
def hemOpeningShardVerify (s : Shard 2) : Bool :=
  verifyHemOpeningBatch compactMerkleLayout [compactHemSlot] compactHemInst compactHemDecode
    compactHemOracle ⟨0, by decide⟩ &&
  decide (s.header = goodHeader)

theorem compactHemInst_valid : HemStatementValid compactHemInst :=
  ⟨by decide, ⟨[CommRingOps.one], by decide +kernel⟩, trivial⟩

theorem hemOpeningShardVerify_accepts : hemOpeningShardVerify fullShard = true := by decide +kernel

theorem hemOpeningShardVerify_tree_accepts :
    checkTree goodHeader hemOpeningShardVerify 16 goodTree = true := by decide +kernel

theorem hemOpeningShardVerify_rejects_per_signer :
    hemOpeningShardVerify (shardFor (headerFor (.perSigner [auditMsg, auditMsg])) 3#2) = false := by
  decide +kernel

theorem hemOpeningShardVerify_boundary :
    ExtractionBoundary compactAuditGeom custodyOf hemOpeningShardVerify (fun _ => False) :=
  boundary_of_hem_opening_batch compactAuditGeom custodyOf (fun _ => False)
    compactMerkleLayout [compactHemSlot]
    (fun _ => compactHemInst) (fun _ => compactHemDecode)
    (fun _ => compactHemOracle) (fun _ => ⟨0, by decide⟩)
    (fun s => decide (s.header = goodHeader))
    (fun _ => committeeStmt) (fun v => v.val)
    (fun _ _ _ => .inr compactHemInst_valid)
    (fun _ _ _ => ⟨_, committee_trace_satisfied⟩)
    (fun s hMode => ⟨rfl, fun v _ => ⟨committee_slots v, by
      rw [of_decide_eq_true hMode]; rfl⟩⟩)

theorem hem_opening_regime_instance : ∃ geom custody verify bad,
    ExtractionBoundary (n := 2) geom custody verify bad ∧
    ∃ s : Shard 2, ∃ v : Fin 2, verify s = true ∧ s.bitmap.getLsbD v.val = true ∧
    ∃ root tree, checkTree root verify 16 tree = true ∧ tree.bitmap.getLsbD v.val = true :=
  ⟨compactAuditGeom, custodyOf, hemOpeningShardVerify, fun _ => False,
    hemOpeningShardVerify_boundary, fullShard, 0,
    hemOpeningShardVerify_accepts, good_bits 0,
    goodHeader, goodTree, hemOpeningShardVerify_tree_accepts, good_bits 0⟩

/-- Validator `1` is assigned a message it did not sign: the leaf is rejected. -/
theorem rejects_unsigned_per_signer_message :
    checkTree (headerFor (.perSigner [auditMsg, otherMsg])) goodVerify 16
      (.leaf (shardFor (headerFor (.perSigner [auditMsg, otherMsg])) 3#2)) = false := by
  decide +kernel
/-- The same per-signer header with the signed message in both slots is accepted. -/
theorem accepts_signed_per_signer_messages :
    checkTree (headerFor (.perSigner [auditMsg, auditMsg])) goodVerify 16
      (.leaf (shardFor (headerFor (.perSigner [auditMsg, auditMsg])) 3#2)) = true := by
  decide +kernel
theorem rejects_swapped_signature_table :
    transparentVerify compactAuditGeom pkOf (fun v => sigOf (if v.val = 0 then 1 else 0))
      fullShard = false := by decide +kernel
/-- A leaf under another committee root cannot be merged, although its signature verifies. -/
theorem rejects_foreign_committee_leaf :
    checkTree goodHeader goodVerify 16
      (.branch (.leaf (shardFor { goodHeader with committeeRoot := [0xC1] } 1#2))
        (.leaf (shardFor goodHeader 2#2)) 3#2) = false := by
  decide +kernel
theorem foreign_committee_leaf_not_accepted :
    ¬ (checkTree goodHeader goodVerify 16
      (.branch (.leaf (shardFor { goodHeader with committeeRoot := [0xC1] } 1#2))
        (.leaf (shardFor goodHeader 2#2)) 3#2) = true) :=
  not_true_of_false rejects_foreign_committee_leaf
theorem unsigned_per_signer_message_not_accepted :
    ¬ (checkTree (headerFor (.perSigner [auditMsg, otherMsg])) goodVerify 16
      (.leaf (shardFor (headerFor (.perSigner [auditMsg, otherMsg])) 3#2)) = true) :=
  not_true_of_false rejects_unsigned_per_signer_message
theorem other_key_not_accepted :
    ¬ (verifyAggNativeSig compactAuditGeom (pkOf 1) auditMsg (sigOf 0) = true) :=
  not_true_of_false native_rejects_other_key

/-- Same keys and signatures, but no custodian logged an approval. -/
def rogueCustody (v : Fin 2) : Custody := { custodyOf v with approvalLog := fun _ _ _ => false }
theorem rogue_not_participated : ∀ v : Fin 2,
    quorumParticipated (rogueCustody v) auditMsg = false := by decide +kernel
/-- The forgery event is witnessed by a real accepted signature. -/
theorem unapproved_signature_is_forgery (v : Fin 2) :
    QuorumForgery compactAuditGeom (rogueCustody v) auditMsg :=
  ⟨sigOf v, native_accepts v, rogue_not_participated v⟩

def mixedCustody (v : Fin 2) : Custody := if v.val = 0 then custodyOf v else rogueCustody v
def mixedVerify : Shard 2 → Bool :=
  transparentVerify compactAuditGeom (fun v => (mixedCustody v).state.pk) sigOf
theorem mixed_accepts : mixedVerify fullShard = true := by decide +kernel
theorem mixed_unapproved_is_one : ∀ v : Fin 2,
    quorumParticipated (mixedCustody v) auditMsg = false → decide (v.val = 1) = true := by
  decide +kernel
theorem mixed_one_unapproved : quorumParticipated (mixedCustody 1) auditMsg = false := by
  decide +kernel

/-- `quorum_advantage_from_extraction` with the outer event identically false: the whole
attack mass is carried by the forgery term of the one validator whose custody did not approve. -/
theorem forgery_regime_instance : ∃ (geom : AggSigGeometry) (custody : Fin 2 → Custody)
    (verify outer : Shard 2 → Bool),
    ExtractionBoundary (n := 2) geom custody verify (fun s => outer s = true) ∧
    ∃ shards : Fin 1 → Shard 2, ∃ attack : Fin 1 → Bool, ∃ B : BitVec 2,
    ∃ forgery : Fin 1 → Fin 2 → Bool,
    (∀ ω, attack ω = true → verify (shards ω) = true ∧
      ∃ v : Fin 2, B.getLsbD v.val = true ∧ (shards ω).bitmap.getLsbD v.val = true ∧
        quorumParticipated (custody v) ((shards ω).header.mode.message v.val) = false) ∧
    (∀ ω v, QuorumForgery geom (custody v)
      ((shards ω).header.mode.message v.val) → forgery ω v = true) :=
  ⟨compactAuditGeom, mixedCustody, mixedVerify, fun _ => false,
    transparent_boundary compactAuditGeom mixedCustody sigOf _,
    fun _ => fullShard, fun _ => true, 2#2, fun _ v => decide (v.val = 1),
    fun _ _ => ⟨mixed_accepts, 1, good_bits 1, good_bits 1, mixed_one_unapproved⟩,
    fun _ v ⟨_, _, hq⟩ => mixed_unapproved_is_one v hq⟩

/-- The three masses of that instance: attack `1`, outer `0`, forgery `1`. -/
theorem forgery_regime_masses :
    (qsum 1 fun _ : Fin 1 => if true then 1 else 0) = 1 ∧
    (qsum 1 fun _ : Fin 1 => if false then 1 else 0) = 0 ∧
    qsum 2 (fun v : Fin 2 => if (2#2 : BitVec 2).getLsbD v.val then
      qsum 1 (fun _ : Fin 1 => if decide (v.val = 1) then 1 else 0) else 0) = 1 := by
  decide +kernel
end Composed

/-! ## 2. Hybrid envelope and policy release -/
section Hybrid
open Qsag.HybridSecurity

def mix (bs : Bytes) : Nat :=
  bs.foldl (fun acc b => (acc * 257 + b.toNat + 1) % 256 ^ 32) 0
def encodePre : Preimage → Bytes
  | .key pq s pk => (if pq then 2 else 1) :: (suiteBytes s ++ pk)
  | .identity s c p => 3 :: (suiteBytes s ++ (be 32 c.val ++ be 32 p.val))
  | .address hrp v s id =>
    4 :: (be 8 hrp.length ++ (hrp ++ (be 8 v ++ (suiteBytes s ++ be 32 id.val))))
/-- Input-dependent stand-in for the domain-separated hash. Not collision resistant. -/
def toyHash : HybridSecurity.Hash := fun x =>
  ⟨mix (encodePre x) % 256 ^ 32, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩
/-- The V2 transcript field layout without its constant ASCII label (`String.toUTF8` did not
reduce under `decide` here); the label is the same for every transcript. -/
def transcriptFields (t : Transcript) : Bytes :=
  (if t.pq then 2 else 1) :: (suiteBytes t.suite ++ (be 32 t.id.val ++
    (be 32 t.classicalDigest.val ++ (be 32 t.pqDigest.val ++ (be 8 t.msg.length ++ t.msg)))))
def toySign (pk : Bytes) (t : Transcript) : Bytes := be 32 (mix (pk ++ transcriptFields t))
/-- Key- and transcript-bound checksum verifier. Publicly computable, hence forgeable. -/
def toyVerifier : Verifier := fun pk t sig => decide (sig = toySign pk t)
def envelopeFor (k : Keys) (m : Bytes) : HybridPinnedEnvelope :=
  ⟨k, toySign k.classical (transcript toyHash k false m),
    toySign k.pq (transcript toyHash k true m)⟩

def hk : Keys := ⟨.secpMl44, [2, 0xA1, 0xA2], [0xB1, 0xB2, 0xB3]⟩
def hrpQs : Bytes := [113, 115]
def paid : Bytes := [0x70, 0x61, 0x79]
def unpaid : Bytes := [0x70, 0x61, 0x7A]

theorem hybrid_honest_accepts :
    validateForAddress toyHash (envelopeFor hk paid) (addressOf toyHash hk hrpQs 1) ∧
    verifyWith toyHash toyVerifier toyVerifier (envelopeFor hk paid) paid := by
  unfold validateForAddress verifyWith; decide +kernel
theorem hybrid_rejects_other_message :
    ¬ verifyWith toyHash toyVerifier toyVerifier (envelopeFor hk paid) unpaid := by
  unfold verifyWith; decide +kernel
/-- The envelope carries no HRP or version, so it validates for every address derived from the
same keys. Network exclusivity has to be bound in the message, as the source module states. -/
theorem hybrid_envelope_valid_for_every_network :
    validateForAddress toyHash (envelopeFor hk paid) (addressOf toyHash hk [113, 116] 1) ∧
    validateForAddress toyHash (envelopeFor hk paid) (addressOf toyHash hk hrpQs 2) := by
  unfold validateForAddress; decide +kernel
/-- Address metadata is bound by the commitment: relabelling the HRP or the version without
recomputing the commitment is rejected. -/
theorem hybrid_rejects_relabelled_hrp :
    ¬ validateForAddress toyHash (envelopeFor hk paid)
      { addressOf toyHash hk hrpQs 1 with hrp := [113, 116] } := by
  unfold validateForAddress; decide +kernel
theorem hybrid_rejects_relabelled_version :
    ¬ validateForAddress toyHash (envelopeFor hk paid)
      { addressOf toyHash hk hrpQs 1 with version := 2 } := by
  unfold validateForAddress; decide +kernel
theorem hybrid_address_commitments_differ :
    (addressOf toyHash hk [113, 116] 1).commitment ≠ (addressOf toyHash hk hrpQs 1).commitment ∧
    (addressOf toyHash hk hrpQs 2).commitment ≠ (addressOf toyHash hk hrpQs 1).commitment := by
  decide +kernel
theorem hybrid_rejects_other_keys_address :
    ¬ validateForAddress toyHash (envelopeFor hk paid)
      (addressOf toyHash { hk with classical := [3, 0xA1, 0xA2] } hrpQs 1) := by
  unfold validateForAddress; decide +kernel
/-- Identical component keys and one verification algorithm: the role flag in the transcript
alone keeps a classical-role signature from being accepted in the PQ role. -/
def twin : Keys := ⟨.secpMl44, [9], [9]⟩
theorem hybrid_rejects_swapped_roles :
    verifyWith toyHash toyVerifier toyVerifier (envelopeFor twin paid) paid ∧
    ¬ verifyWith toyHash toyVerifier toyVerifier
      ⟨twin, (envelopeFor twin paid).pqSignature, (envelopeFor twin paid).classicalSignature⟩
      paid := by
  unfold verifyWith; decide +kernel
/-- An honest PQ signature is not accepted next to a substituted classical key. -/
theorem hybrid_rejects_rogue_partner :
    ¬ (toyVerifier hk.pq (transcript toyHash { hk with classical := [0xEE] } true paid)
      (envelopeFor hk paid).pqSignature = true) := by decide +kernel

theorem hybrid_keybound_instance : ∃ (H : HybridSecurity.Hash) (vc vp : Verifier) (k : Keys) (hrp : Bytes)
    (v : Nat) (e : HybridPinnedEnvelope) (m : Bytes) (qs : List Bytes),
    validateForAddress H e (addressOf H k hrp v) ∧ verifyWith H vc vp e m ∧ m ∉ qs :=
  ⟨toyHash, toyVerifier, toyVerifier, hk, hrpQs, 1, envelopeFor hk paid, paid, [unpaid],
    hybrid_honest_accepts.1, hybrid_honest_accepts.2, by decide⟩

def brokenClassical : Verifier := fun _ _ _ => true
/-- Output `0`: junk signatures on a fresh message. Output `1`: replay of a queried message. -/
def advOut (j : Fin 2) : HybridPinnedEnvelope × Bytes :=
  if j.val = 0 then (⟨hk, [0], [0]⟩, unpaid) else (envelopeFor hk paid, paid)
/-- Classical component accepting everything, PQ component binding: the hybrid win mass is
`0` while the classical component game is won with mass `1`. -/
theorem robust_combiner_instance :
    mass (fun _ : Fin 2 => 1) (fun j =>
      hybridWins toyHash brokenClassical toyVerifier hk hrpQs 1 [paid] (advOut j)) = 0 ∧
    mass (fun _ : Fin 2 => 1) (fun j =>
      brokenClassical hk.classical (transcript toyHash hk false (advOut j).2)
        (advOut j).1.classicalSignature && decide ((advOut j).2 ∉ [paid])) = 1 ∧
    mass (fun _ : Fin 2 => 1) (fun j =>
      toyVerifier hk.pq (transcript toyHash hk true (advOut j).2)
        (advOut j).1.pqSignature && decide ((advOut j).2 ∉ [paid])) = 0 := by
  decide +kernel
/-- Both components accepting everything: the fresh junk output wins. -/
theorem both_components_broken_instance :
    mass (fun _ : Fin 2 => 1) (fun j =>
      hybridWins toyHash brokenClassical brokenClassical hk hrpQs 1 [paid] (advOut j)) = 1 := by
  decide +kernel

/-! ### Real `cSHAKE256` (`keccakF1600`) + `verifyAggNativeSig` (`Poseidon2` Jorts) Hybrid Envelope -/

/-- ASCII customization string `"QSAG.HYBRID.V2"` for `cSHAKE256` envelope hashing. -/
