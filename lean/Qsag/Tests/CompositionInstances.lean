module
public import Qsag.Math.GoldilocksBase
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
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Oracle.Sponge
public import Qsag.Oracle.Poseidon2
public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Oracle.Keccak
public import Qsag.Protocol.Signing.Fips205
public import Qsag.Protocol.Aggregation.UcGames
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

/-- Unfold the hybrid-envelope predicates of `HybridSecurity` through their exported equations,
together with the fixtures of this section that mention them. -/
local macro "hybrid_unfold" : tactic => `(tactic| simp only [
  verifyWith.public_eq_1, validateForAddress.public_eq_1, addressOf.public_eq_1,
  transcript.public_eq_1, idCommit.public_eq_1, idInput.public_eq_1, keyHash.public_eq_1,
  hybridWins_eq, mass.public_eq_1, suiteBytes_secpMl44, suiteBytes_edMl65,
  toyHash, encodePre, transcriptFields, toySign, toyVerifier, envelopeFor, hk])

theorem hybrid_honest_accepts :
    validateForAddress toyHash (envelopeFor hk paid) (addressOf toyHash hk hrpQs 1) ∧
    verifyWith toyHash toyVerifier toyVerifier (envelopeFor hk paid) paid := by
  hybrid_unfold; decide +kernel
theorem hybrid_rejects_other_message :
    ¬ verifyWith toyHash toyVerifier toyVerifier (envelopeFor hk paid) unpaid := by
  hybrid_unfold; decide +kernel
/-- The envelope carries no HRP or version, so it validates for every address derived from the
same keys. Network exclusivity has to be bound in the message, as the source module states. -/
theorem hybrid_envelope_valid_for_every_network :
    validateForAddress toyHash (envelopeFor hk paid) (addressOf toyHash hk [113, 116] 1) ∧
    validateForAddress toyHash (envelopeFor hk paid) (addressOf toyHash hk hrpQs 2) := by
  hybrid_unfold; decide +kernel
/-- Address metadata is bound by the commitment: relabelling the HRP or the version without
recomputing the commitment is rejected. -/
theorem hybrid_rejects_relabelled_hrp :
    ¬ validateForAddress toyHash (envelopeFor hk paid)
      { addressOf toyHash hk hrpQs 1 with hrp := [113, 116] } := by
  hybrid_unfold; decide +kernel
theorem hybrid_rejects_relabelled_version :
    ¬ validateForAddress toyHash (envelopeFor hk paid)
      { addressOf toyHash hk hrpQs 1 with version := 2 } := by
  hybrid_unfold; decide +kernel
theorem hybrid_address_commitments_differ :
    (addressOf toyHash hk [113, 116] 1).commitment ≠ (addressOf toyHash hk hrpQs 1).commitment ∧
    (addressOf toyHash hk hrpQs 2).commitment ≠ (addressOf toyHash hk hrpQs 1).commitment := by
  hybrid_unfold; decide +kernel
theorem hybrid_rejects_other_keys_address :
    ¬ validateForAddress toyHash (envelopeFor hk paid)
      (addressOf toyHash { hk with classical := [3, 0xA1, 0xA2] } hrpQs 1) := by
  hybrid_unfold; decide +kernel
/-- Identical component keys and one verification algorithm: the role flag in the transcript
alone keeps a classical-role signature from being accepted in the PQ role. -/
def twin : Keys := ⟨.secpMl44, [9], [9]⟩
theorem hybrid_rejects_swapped_roles :
    verifyWith toyHash toyVerifier toyVerifier (envelopeFor twin paid) paid ∧
    ¬ verifyWith toyHash toyVerifier toyVerifier
      ⟨twin, (envelopeFor twin paid).pqSignature, (envelopeFor twin paid).classicalSignature⟩
      paid := by
  hybrid_unfold; simp only [twin, suiteBytes_secpMl44]; decide +kernel
/-- An honest PQ signature is not accepted next to a substituted classical key. -/
theorem hybrid_rejects_rogue_partner :
    ¬ (toyVerifier hk.pq (transcript toyHash { hk with classical := [0xEE] } true paid)
      (envelopeFor hk paid).pqSignature = true) := by hybrid_unfold; decide +kernel

theorem hybrid_keybound_instance : ∃ (H : HybridSecurity.Hash) (vc vp : Verifier) (k : Keys) (hrp : Bytes)
    (v : Nat) (e : HybridPinnedEnvelope) (m : Bytes) (qs : List Bytes),
    validateForAddress H e (addressOf H k hrp v) ∧ verifyWith H vc vp e m ∧ m ∉ qs :=
  ⟨toyHash, toyVerifier, toyVerifier, hk, hrpQs, 1, envelopeFor hk paid, paid, [unpaid],
    hybrid_honest_accepts.1, hybrid_honest_accepts.2, by decide⟩

def brokenClassical : Verifier := fun _ _ _ => true
/-- Output `0`: junk signatures on a fresh message. Output `1`: replay of a queried message. -/
def advOut (j : Fin 2) : HybridPinnedEnvelope × Bytes :=
  if j.val = 0 then (⟨hk, [0], [0]⟩, unpaid) else (envelopeFor hk paid, paid)
theorem advOut_zero (h : 0 < 2) : advOut ⟨0, h⟩ = (⟨hk, [0], [0]⟩, unpaid) := by rfl
theorem advOut_one (h : 0 + 1 < 2) : advOut ⟨0 + 1, h⟩ = (envelopeFor hk paid, paid) := by rfl
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
  simp only [mass.public_eq_1, hybridWins_eq, qsum_succ, qsum_zero, advOut_zero, advOut_one]
  hybrid_unfold
  simp only [decide_true, Bool.true_and]
  decide +kernel
/-- Both components accepting everything: the fresh junk output wins. -/
theorem both_components_broken_instance :
    mass (fun _ : Fin 2 => 1) (fun j =>
      hybridWins toyHash brokenClassical brokenClassical hk hrpQs 1 [paid] (advOut j)) = 1 := by
  simp only [mass.public_eq_1, hybridWins_eq, qsum_succ, qsum_zero, advOut_zero, advOut_one]
  hybrid_unfold
  simp only [decide_true, Bool.true_and]
  decide +kernel

/-! ### Real `cSHAKE256` (`keccakF1600`) + `verifyAggNativeSig` (`Poseidon2` Jorts) Hybrid Envelope -/

/-- ASCII customization string `"QSAG.HYBRID.V2"` for `cSHAKE256` envelope hashing. -/
def hybridCshakeTag : Bytes :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x48, 0x59, 0x42, 0x52, 0x49, 0x44, 0x2E, 0x56, 0x32]

def beNat (bs : Bytes) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Real 256-bit `cSHAKE256` (`evalCshake256Sponge keccakF1600`) domain-separated hash for
`HybridSecurity.Hash`, replacing the polynomial checksum `toyHash`. -/
def cshakeHybridHash : HybridSecurity.Hash := fun x =>
  ⟨beNat (evalCshake256Sponge keccakF1600 zeroKState xorRate136 rateBlockBytes
      [] hybridCshakeTag (encodePre x) 32) % 256 ^ 32,
   Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

def encodeLane4Bytes (d : Digest4) : Bytes :=
  be 8 d.x0.val ++ (be 8 d.x1.val ++ (be 8 d.x2.val ++ be 8 d.x3.val))

def decodeLane4Bytes (bs : Bytes) : Option Digest4 :=
  if bs.length = 32 then
    some ⟨Goldilocks.ofNat (beNat (bs.take 8)),
          Goldilocks.ofNat (beNat ((bs.drop 8).take 8)),
          Goldilocks.ofNat (beNat ((bs.drop 16).take 8)),
          Goldilocks.ofNat (beNat ((bs.drop 24).take 8))⟩
  else none

def encodeCompactJortsPk (pk : AggValidatorPk) : Bytes :=
  encodeLane4Bytes pk.pkSeed ++ encodeLane4Bytes pk.pkRoot

def decodeCompactJortsPk (bs : Bytes) : Option AggValidatorPk :=
  if bs.length = 64 then
    match decodeLane4Bytes (bs.take 32), decodeLane4Bytes (bs.drop 32) with
    | some s, some r => some ⟨.xmssPoseidon2, s, r⟩
    | _, _ => none
  else none

def encodeCompactJortsSig (sig : AggNativeSignature) : Bytes :=
  match sig.layers with
  | [⟨ctr, [c0, c1], [s0]⟩] =>
    be 8 sig.statefulLeafIdx ++ (be 8 ctr ++
      (encodeLane4Bytes sig.rRand ++
        (encodeLane4Bytes c0 ++ (encodeLane4Bytes c1 ++ encodeLane4Bytes s0))))
  | _ => []

def decodeCompactJortsSig (bs : Bytes) : Option AggNativeSignature :=
  if bs.length = 144 then
    match decodeLane4Bytes ((bs.drop 16).take 32),
          decodeLane4Bytes ((bs.drop 48).take 32),
          decodeLane4Bytes ((bs.drop 80).take 32),
          decodeLane4Bytes ((bs.drop 112).take 32) with
    | some rR, some c0, some c1, some s0 =>
      some ⟨.xmssPoseidon2, rR, beNat (bs.take 8), [],
        [⟨beNat ((bs.drop 8).take 8), [c0, c1], [s0]⟩]⟩
    | _, _, _, _ => none
  else none

/-- Real `Poseidon2` Jorts signature verifier (`verifyAggNativeSig compactAuditGeom`) over decoded
public-key and signature bytes, replacing the publicly forgeable `toyVerifier`. -/
def jortsNativeVerifier : Verifier := fun pkBytes t sigBytes =>
  match decodeCompactJortsPk pkBytes, decodeCompactJortsSig sigBytes with
  | some pk, some sig => verifyAggNativeSig compactAuditGeom pk (transcriptFields t) sig
  | _, _ => false

def realHk : Keys :=
  ⟨.secpMl44, encodeCompactJortsPk (pkOf 0), encodeCompactJortsPk (pkOf 1)⟩

/-- Literal native signatures on the `cshakeHybridHash` classical/PQ transcripts for `paid`
(`tswCtr = 21` and `122`), tied to `signAggNative` by `real_hybrid_sigs_are_modelled_outputs`. -/
def realHybridSig0 : AggNativeSignature :=
  ⟨.xmssPoseidon2, auditRRand, 0, [], [⟨21,
    [lane 4152917893602010253 5344412802567744713 18406927796743773750 1962659585794765281,
     lane 12873018474816122043 2869910227242953051 3097284758269903553 18326636155894048790],
    [lane 5524291857455771020 16376422686410664307 15963494650740044646 18098363549869475062]⟩]⟩

def realHybridSig1 : AggNativeSignature :=
  ⟨.xmssPoseidon2, auditRRand, 1, [], [⟨122,
    [lane 10036846859147774993 15499800327978969217 15476824389852128619 15451031862181482938,
     lane 14010823692816899133 11663312065820974772 3799621797402719272 6812636063505864400],
    [lane 13388180661509288011 5130805258596798721 8406673262598715289 15360960474733464499]⟩]⟩

theorem real_hybrid_sigs_are_modelled_outputs :
    realHybridSig0 = signAggNative compactAuditGeom (skOf 0) (pkOf 0)
      (transcriptFields (transcript cshakeHybridHash realHk false paid)) auditRRand 0 21 [] ∧
    realHybridSig1 = signAggNative compactAuditGeom (skOf 1) (pkOf 1)
      (transcriptFields (transcript cshakeHybridHash realHk true paid)) auditRRand 1 122 [] := by
  decide +kernel

def realEnvelopePaid : HybridPinnedEnvelope :=
  ⟨realHk, encodeCompactJortsSig realHybridSig0, encodeCompactJortsSig realHybridSig1⟩

theorem real_hybrid_honest_accepts :
    validateForAddress cshakeHybridHash realEnvelopePaid (addressOf cshakeHybridHash realHk hrpQs 1) ∧
    verifyWith cshakeHybridHash jortsNativeVerifier jortsNativeVerifier realEnvelopePaid paid := by
  unfold validateForAddress verifyWith; decide +kernel

theorem real_hybrid_rejects_other_message :
    ¬ verifyWith cshakeHybridHash jortsNativeVerifier jortsNativeVerifier realEnvelopePaid unpaid := by
  unfold verifyWith; decide +kernel

theorem real_hybrid_rejects_rogue_partner :
    ¬ (jortsNativeVerifier realHk.pq
        (transcript cshakeHybridHash { realHk with classical := encodeCompactJortsPk (pkOf 1) } true paid)
        realEnvelopePaid.pqSignature = true) := by
  decide +kernel

attribute [local irreducible] cshakeHybridHash jortsNativeVerifier realEnvelopePaid

theorem real_hybrid_keybound_instance :
    ∃ (H : HybridSecurity.Hash) (vc vp : Verifier) (k : Keys) (hrp : Bytes)
      (v : Nat) (e : HybridPinnedEnvelope) (m : Bytes) (qs : List Bytes),
      validateForAddress H e (addressOf H k hrp v) ∧ verifyWith H vc vp e m ∧ m ∉ qs :=
  ⟨cshakeHybridHash, jortsNativeVerifier, jortsNativeVerifier, realHk, hrpQs, 1,
    realEnvelopePaid, paid, [unpaid],
    real_hybrid_honest_accepts.1, real_hybrid_honest_accepts.2, by decide⟩

def pol : TransactionPolicy := ⟨9, [7, 8], 100, 150, [⟨50, 1⟩, ⟨100, 2⟩]⟩
def intentHash (i : TransactionIntent) : Nat :=
  ((((i.recipient * 1000003 + i.amount) * 1000003 + i.reportedSpend) * 1000003 + i.nonce) *
    1000003 + i.session) * 1000003 + i.window
def payA : TransactionIntent := ⟨7, 60, 0, 1, 11, 5⟩
def payB : TransactionIntent := ⟨8, 80, 60, 2, 12, 5⟩
def genesis : Ledger := ⟨0, [], []⟩
def quorum01 (j : Fin 3) : Bool := decide (j.val < 2)
def corrupt0 (j : Fin 3) : Bool := decide (j.val = 0)
/-- The corrupt quorum member holds a token that was never minted for the intent. -/
def tokensA (j : Fin 3) : AuthorizedSignReleaseToken :=
  if j.val = 0 then ⟨0, 0, 0, 0, 0⟩ else minted intentHash pol payA

theorem only_honest_member : ∀ j : Fin 3,
    quorum01 j = true → corrupt0 j = false → j = 1 := by decide +kernel
theorem acceptsA : PolicyAccepts pol payA 2 := by
  rw [PolicyAccepts.public_eq_1]
  exact ⟨by decide +kernel, by decide +kernel, ⟨100, 2⟩, by rfl, by decide +kernel⟩
theorem acceptsB : PolicyAccepts pol payB 2 := by
  rw [PolicyAccepts.public_eq_1]
  exact ⟨by decide +kernel, by decide +kernel, ⟨100, 2⟩, by rfl, by decide +kernel⟩
theorem stepA : LedgerStep pol.maxWindowSpend 5 genesis payA (burn genesis payA) := by
  simp only [LedgerStep.public_eq_1, burn.public_eq_1, projected.public_eq_1]; decide +kernel
theorem stepB : LedgerStep pol.maxWindowSpend 5 (burn genesis payA) payB
    (burn (burn genesis payA) payB) := by
  simp only [LedgerStep.public_eq_1, burn.public_eq_1, projected.public_eq_1]; decide +kernel
theorem corrupt_token_not_minted : tokensA 0 ≠ minted intentHash pol payA := by
  intro h
  have h' := congrArg AuthorizedSignReleaseToken.policyDigest h
  rw [minted.public_eq_1] at h'
  exact absurd h' (by decide +kernel)

/-- `n = 3`, `t = 2`, `f = 1`: the quorum contains the corrupt party; the honest member alone
supplies the release. -/
theorem corrupt_quorum_instance : ∃ (n t f w : Nat) (p : TransactionPolicy)
    (H : TransactionIntent → Nat) (i : TransactionIntent) (q corrupt : Fin n → Bool)
    (before after : Fin n → Ledger) (tokens : Fin n → AuthorizedSignReleaseToken),
    cardinal q = t ∧ cardinal corrupt ≤ f ∧ f < t ∧
    (∀ j, q j = true → corrupt j = false →
      ValidRelease H p t w i (before j) (after j) (tokens j)) :=
  ⟨3, 2, 1, 5, pol, intentHash, payA, quorum01, corrupt0, fun _ => genesis,
    fun _ => burn genesis payA, tokensA, by rw [cardinal.public_eq_1]; decide +kernel,
    by rw [cardinal.public_eq_1]; decide +kernel, by decide,
    fun j hq hc => by
      obtain rfl := only_honest_member j hq hc
      rw [ValidRelease.public_eq_1]
      exact ⟨by rfl, acceptsA, stepA⟩⟩

def quorumOf (i : TransactionIntent) (j : Fin 3) : Bool :=
  if i = payA then decide (j.val < 2) else decide (0 < j.val)
def beforeOf (i : TransactionIntent) : Ledger := if i = payA then genesis else burn genesis payA

theorem payB_ne_payA : (payB = payA) = False :=
  eq_false fun h => absurd (congrArg TransactionIntent.recipient h) (by decide)
theorem beforeOf_payA : beforeOf payA = genesis := by
  simp only [beforeOf, eq_self, ite_true]
theorem beforeOf_payB : beforeOf payB = burn genesis payA := by
  simp only [beforeOf, payB_ne_payA, ite_false]

/-- Two intents, two different quorums sharing honest party `1`, one serialized ledger. -/
theorem two_intent_spending_instance : ∃ (n t f w : Nat) (p : TransactionPolicy)
    (H : TransactionIntent → Nat) (is : List TransactionIntent) (corrupt : Fin n → Bool)
    (q : TransactionIntent → Fin n → Bool) (before after : TransactionIntent → Fin n → Ledger)
    (tokens : TransactionIntent → Fin n → AuthorizedSignReleaseToken) (final : Ledger),
    cardinal corrupt ≤ f ∧ f < t ∧ (∀ i ∈ is, cardinal (q i) = t) ∧
    (∀ i ∈ is, ∀ j, q i j = true → corrupt j = false →
      ValidRelease H p t w i (before i j) (after i j) (tokens i j)) ∧
    LedgerTrace p.maxWindowSpend w ⟨0, [], []⟩ is final := by
  refine ⟨3, 2, 1, 5, pol, intentHash, [payA, payB], corrupt0, quorumOf,
    fun i _ => beforeOf i, fun i _ => burn (beforeOf i) i, fun i _ => minted intentHash pol i,
    burn (burn genesis payA) payB, by rw [cardinal.public_eq_1]; decide +kernel, by decide,
    ?_, ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [cardinal.public_eq_1]
      simp only [quorumOf, eq_self, ite_true]
      decide +kernel
    · obtain rfl := List.mem_singleton.mp hi
      rw [cardinal.public_eq_1]
      simp only [quorumOf, payB_ne_payA, ite_false]
      decide +kernel
  · intro i hi j _ _
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [ValidRelease.public_eq_1]
      dsimp only
      rw [beforeOf_payA]
      exact ⟨rfl, acceptsA, stepA⟩
    · obtain rfl := List.mem_singleton.mp hi
      rw [ValidRelease.public_eq_1]
      dsimp only
      rw [beforeOf_payB]
      exact ⟨rfl, acceptsB, stepB⟩
  · exact .cons stepA (.cons stepB (.nil _))

theorem rejects_over_per_tx_cap : ¬ PolicyAccepts pol ⟨7, 101, 0, 3, 13, 5⟩ 3 := by
  rw [PolicyAccepts.public_eq_1]
  exact fun h => absurd h.2.1 (by decide +kernel)
theorem rejects_unlisted_recipient : ¬ PolicyAccepts pol ⟨9, 10, 0, 3, 13, 5⟩ 3 := by
  rw [PolicyAccepts.public_eq_1]
  exact fun h => absurd h.1 (by decide +kernel)
theorem rejects_insufficient_approvals : ¬ PolicyAccepts pol payB 1 := by
  rw [PolicyAccepts.public_eq_1]
  rintro ⟨_, _, r, hr, hn⟩
  have e : pol.tiers.find? (fun r => decide (payB.amount ≤ r.cap)) = some ⟨100, 2⟩ := by
    rfl
  rw [e] at hr
  cases hr
  exact absurd hn (by decide +kernel)
theorem rejects_nonce_replay :
    ¬ LedgerStep pol.maxWindowSpend 5 (burn genesis payA) payA
      (burn (burn genesis payA) payA) := by
  rw [LedgerStep.public_eq_1]
  exact fun h => absurd h.2.1 (by rw [burn.public_eq_1]; decide +kernel)
/-- After `payA` and `payB` (140 of 150 spent) a further 20 has no ledger step at all. -/
theorem rejects_window_overspend (next : Ledger) :
    ¬ LedgerStep pol.maxWindowSpend 5 (burn (burn genesis payA) payB)
      ⟨7, 20, 0, 3, 13, 5⟩ next := by
  rw [LedgerStep.public_eq_1]
  exact fun h => absurd h.2.2.2.1 (by
    simp only [projected.public_eq_1, burn.public_eq_1]; decide +kernel)
theorem rejects_stale_window (next : Ledger) :
    ¬ LedgerStep pol.maxWindowSpend 6 genesis payA next := by
  rw [LedgerStep.public_eq_1]
  exact fun h => absurd h.1 (by decide +kernel)
theorem token_is_intent_specific :
    minted intentHash pol payA ≠ minted intentHash pol payB := by
  intro h
  have h' := congrArg AuthorizedSignReleaseToken.nonce h
  rw [minted.public_eq_1, minted.public_eq_1] at h'
  exact absurd h' (by decide +kernel)

def toyMac (policy old next : Nat) : Nat := (policy * 65537 + old) * 65537 + next + 0x5eed
theorem window_advance_accepts :
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 9 5 6⟩ = some ⟨0, [], []⟩ := by
  rw [advanceAuthorized.public_eq_1, advanceWindow.public_eq_1]; rfl
/-- Wrong tag, non-increasing epoch, tag for another policy, tag for another old epoch. -/
theorem window_advance_rejects :
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 9 5 6 + 1⟩ = none ∧
    advanceAuthorized toyMac 9 5 ⟨5, toyMac 9 5 5⟩ = none ∧
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 8 5 6⟩ = none ∧
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 9 4 6⟩ = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [advanceAuthorized.public_eq_1, advanceWindow.public_eq_1]; rfl)
theorem window_advance_rejects_wrong_tag :
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 9 5 6 + 1⟩ ≠ some ⟨0, [], []⟩ := by
  rw [window_advance_rejects.1]
  intro h
  cases h
end Hybrid

/-! ## 3. Cross-protocol: the modelled Poseidon2 permutation and real labels -/
section Cross
open Qsag.CrossProtocol

attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv

open CommRingOps LawfulCommRing in
/-- Componentwise Goldilocks arithmetic on a four-limb lane; `add` is `lane4Add`. -/
@[instance_reducible] def lane4Ring : LawfulCommRing Lane4 where
  zero := ⟨zero, zero, zero, zero⟩; one := ⟨one, one, one, one⟩
  add := fun a b => ⟨add a.x0 b.x0, add a.x1 b.x1, add a.x2 b.x2, add a.x3 b.x3⟩
  mul := fun a b => ⟨mul a.x0 b.x0, mul a.x1 b.x1, mul a.x2 b.x2, mul a.x3 b.x3⟩
  neg := fun a => ⟨neg a.x0, neg a.x1, neg a.x2, neg a.x3⟩
  sub := fun a b => ⟨sub a.x0 b.x0, sub a.x1 b.x1, sub a.x2 b.x2, sub a.x3 b.x3⟩
  add_assoc := fun _ _ _ => Lane4.ext (add_assoc _ _ _) (add_assoc _ _ _)
    (add_assoc _ _ _) (add_assoc _ _ _)
  add_comm := fun _ _ => Lane4.ext (add_comm _ _) (add_comm _ _) (add_comm _ _) (add_comm _ _)
  zero_add := fun _ => Lane4.ext (zero_add _) (zero_add _) (zero_add _) (zero_add _)
  add_zero := fun _ => Lane4.ext (add_zero _) (add_zero _) (add_zero _) (add_zero _)
  add_left_neg := fun _ => Lane4.ext (add_left_neg _) (add_left_neg _)
    (add_left_neg _) (add_left_neg _)
  sub_eq_add_neg := fun _ _ => Lane4.ext (sub_eq_add_neg _ _) (sub_eq_add_neg _ _)
    (sub_eq_add_neg _ _) (sub_eq_add_neg _ _)
  mul_assoc := fun _ _ _ => Lane4.ext (mul_assoc _ _ _) (mul_assoc _ _ _)
    (mul_assoc _ _ _) (mul_assoc _ _ _)
  mul_comm := fun _ _ => Lane4.ext (mul_comm _ _) (mul_comm _ _) (mul_comm _ _) (mul_comm _ _)
  one_mul := fun _ => Lane4.ext (one_mul _) (one_mul _) (one_mul _) (one_mul _)
  mul_one := fun _ => Lane4.ext (mul_one _) (mul_one _) (mul_one _) (mul_one _)
  left_distrib := fun _ _ _ => Lane4.ext (left_distrib _ _ _) (left_distrib _ _ _)
    (left_distrib _ _ _) (left_distrib _ _ _)
  right_distrib := fun _ _ _ => Lane4.ext (right_distrib _ _ _) (right_distrib _ _ _)
    (right_distrib _ _ _) (right_distrib _ _ _)
attribute [local instance] lane4Ring

def lane4State (s : Poseidon2State12) : State Lane4 := (s.b0, s.b1, s.b2)
/-- The modelled width-12 Poseidon2 permutation as the `SimpleEquiv` consumed by the
transcript and counting theorems. -/
def poseidonEquiv : SimpleEquiv (State Lane4) (State Lane4) where
  toFun x := lane4State (poseidon2Perm12 ⟨x.1, x.2.1, x.2.2⟩)
  invFun y := lane4State (poseidon2Perm12Inv ⟨y.1, y.2.1, y.2.2⟩)
  left_inv x := congrArg lane4State (poseidon2Perm12Inv_left_inv ⟨x.1, x.2.1, x.2.2⟩)
  right_inv y := congrArg lane4State (poseidon2Perm12Inv_right_inv ⟨y.1, y.2.1, y.2.2⟩)

/-- Input-dependent part of the deployed weighted feed-forward beyond `in0`:
`2·in1 + 4·tweak`. -/
def weightedJiveExtra (x : State Lane4) : Lane4 :=
  lane4Add (lane4Scale (Goldilocks.ofNat 2) x.2.1) (lane4Scale (Goldilocks.ofNat 4) x.2.2)

/-- Consumer bridge: `poseidon2_compress12_ff` of `sponge.rs`, as modelled by
`poseidon2Compress12FF` (`perm.b0 + in0 + 2·in1 + 4·tweak`), is `jiveCompress` with
`extra = weightedJiveExtra` over the modelled permutation. -/
theorem compress12FF_eq_jive (in0 in1 tweak : Lane4) :
    poseidon2Compress12FF in0 in1 tweak =
      jiveCompress weightedJiveExtra poseidonEquiv (in0, in1, tweak) := by
  show CommRingOps.add (poseidon2Perm12 ⟨in0, in1, tweak⟩).b0
      (CommRingOps.add (CommRingOps.add in0 (lane4Scale (Goldilocks.ofNat 2) in1))
        (lane4Scale (Goldilocks.ofNat 4) tweak)) =
    CommRingOps.add (poseidon2Perm12 ⟨in0, in1, tweak⟩).b0
      (CommRingOps.add in0 (CommRingOps.add (lane4Scale (Goldilocks.ofNat 2) in1)
        (lane4Scale (Goldilocks.ofNat 4) tweak)))
  rw [LawfulCommRing.add_assoc in0]

/-- `checked_preimage_is_transcript_hit` stated for the modelled deployed compression. -/
theorem deployed_compress_preimage_hits_transcript
    (t : List (State Lane4 × State Lane4)) (target : Lane4) (x y : State Lane4)
    (hc : Consistent poseidonEquiv t) (hm : (x, y) ∈ t)
    (hs : poseidon2Compress12FF x.1 x.2.1 x.2.2 = target) :
    relation weightedJiveExtra x y = target :=
  checked_preimage_is_transcript_hit weightedJiveExtra poseidonEquiv t target x y hc hm
    ((compress12FF_eq_jive x.1 x.2.1 x.2.2).symm.trans hs)

def realX : State Lane4 :=
  (⟨Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3, Goldilocks.ofNat 4⟩,
   ⟨Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7, Goldilocks.ofNat 8⟩,
   ⟨domainMerkleNode, Goldilocks.ofNat 9, Goldilocks.ofNat 10, poseidon2IvTag⟩)
def realY : State Lane4 :=
  (⟨Goldilocks.ofNat 7, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, lane4Zero, lane4Zero)
/-- One inverse and one forward query to the modelled permutation. -/
def realTranscript : List (State Lane4 × State Lane4) :=
  [(poseidonEquiv.invFun realY, realY), (realX, poseidonEquiv.toFun realX)]
theorem real_transcript_consistent : Consistent poseidonEquiv realTranscript :=
  inverse_extension _ _
    (forward_extension _ [] (fun _ _ h => absurd h List.not_mem_nil) realX) realY

theorem real_transcript_instance :
    ∃ p : SimpleEquiv (State Lane4) (State Lane4),
    ∃ t : List (State Lane4 × State Lane4), ∃ x y : State Lane4,
    ∃ target : Lane4, Consistent p t ∧ (x, y) ∈ t ∧
      jiveCompress weightedJiveExtra p x = target :=
  ⟨poseidonEquiv, realTranscript, realX, poseidonEquiv.toFun realX,
    poseidon2Compress12FF realX.1 realX.2.1 realX.2.2, real_transcript_consistent,
    List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl),
    (compress12FF_eq_jive realX.1 realX.2.1 realX.2.2).symm⟩

/-- The permutation moves the point and the compression output is nonzero. -/
theorem real_poseidon_nondegenerate :
    poseidonEquiv.toFun realX ≠ realX ∧
    poseidon2Compress12FF realX.1 realX.2.1 realX.2.2 ≠ lane4Zero := by decide +kernel
/-- On the modelled permutation: one inverse call hits a chosen raw-truncation target, and
the same point misses that target under feed-forward. -/
theorem real_poseidon_raw_vs_feedforward :
    rawTrunc poseidonEquiv (poseidonEquiv.invFun realY) = realY.1 ∧
    jiveCompress weightedJiveExtra poseidonEquiv (poseidonEquiv.invFun realY) ≠
      realY.1 :=
  ⟨raw_inverse poseidonEquiv _ _ _, by decide +kernel⟩
theorem real_poseidon_feedforward_misses :
    ¬ (jiveCompress weightedJiveExtra poseidonEquiv (poseidonEquiv.invFun realY) =
      realY.1) := real_poseidon_raw_vs_feedforward.2

/- `bidirectional_bad_count` on GF(4): of three available answers exactly one lands on the
target, contributing `1 · 2!` completions, within the bound `1 · 4² · 2!`. -/
section SmallField
local instance : LawfulCommRing (Bool × Bool) := towerRing 1
def smallAvail : List (State (Bool × Bool)) :=
  [((false, false), (false, false), (false, false)),
   ((true, false), (false, true), (false, false)),
   ((true, true), (true, false), (false, true))]
def smallChosen : State (Bool × Bool) := ((false, true), (true, true), (false, false))
theorem small_field_bad_count :
    ((smallAvail.filter (fun x => decide (queryValue false
        (fun _ _ => (CommRingOps.zero : Bool × Bool)) smallChosen x ∈
          [((true, true) : Bool × Bool)]))).flatMap
      (fun y => (extensions (smallAvail.length - 1) (smallAvail.erase y)).map (y :: ·))).length
      = 2 ∧
    ((smallAvail.filter (fun x => decide (queryValue false
        (fun _ _ => (CommRingOps.zero : Bool × Bool)) smallChosen x ∈
          ([] : List (Bool × Bool))))).flatMap
      (fun y => (extensions (smallAvail.length - 1) (smallAvail.erase y)).map (y :: ·))).length
      = 0 := by decide +kernel
end SmallField

/-- A hash that separates `[1]` from `[2]` and collides on `[0, 1]` and `[1]`. -/
def foldHash (m : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (m.foldl (fun a b => a * 256 + b.toNat) 0)
theorem digest_separates_distinct_hashes :
    digest5FromBitVec256 (foldHash [1]) ≠ digest5FromBitVec256 (foldHash [2]) := by
  decide +kernel
/-- Equal digests on distinct messages come from the hash, as `digest5_collision_iff` states. -/
theorem digest_collision_is_hash_collision :
    ([0, 1] : List UInt8) ≠ [1] ∧
    digest5FromBitVec256 (foldHash [0, 1]) = digest5FromBitVec256 (foldHash [1]) ∧
    foldHash [0, 1] = foldHash [1] := by decide +kernel

/-- ASCII `QSAG.MU/v2` and `QSAG.HEM.MSG/v2` from the audited qsag-agg label inventory. -/
def muLabel : List UInt8 := [0x51, 0x53, 0x41, 0x47, 0x2E, 0x4D, 0x55, 0x2F, 0x76, 0x32]
def hemMsgLabel : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x48, 0x45, 0x4D, 0x2E, 0x4D, 0x53, 0x47, 0x2F, 0x76, 0x32]

theorem real_label_partition_instance : ∃ a b x y : List UInt8,
    8 * a.length < 256 ^ 255 ∧ 8 * b.length < 256 ^ 255 ∧ a ≠ b ∧
      formatted a x ≠ formatted b y :=
  ⟨muLabel, hemMsgLabel, [0xAA, 0xBB], [0xAA, 0xBB], by decide, by decide, by decide,
    universal_customization_partition _ _ _ _ (by decide) (by decide) (by decide)⟩

def toyOracle (x : List UInt8) : Nat := x.foldl (fun a b => a * 257 + b.toNat + 1) 0
/-- A game that makes two adaptive-capable queries and returns both answers. -/
def twoQueryGame : OracleProgram (List UInt8) Nat Nat :=
  .ask [1] fun r1 => .ask [2, 3] fun r2 => .done (r1 * 1000003 + r2)

/-- Reprogramming a query under the other label leaves the `QSAG.MU/v2` game unchanged. -/
theorem foreign_label_reprogram_instance :
    runOracle (fun x => reprogramAt toyOracle (formatted hemMsgLabel [1]) 0
      (formatted muLabel x)) twoQueryGame =
    runOracle (fun x => toyOracle (formatted muLabel x)) twoQueryGame :=
  isolated_game_zero_drift toyOracle 0 muLabel hemMsgLabel [1] (by decide) (by decide)
    (by decide) twoQueryGame
/-- Reprogramming the same query under the game's own label changes its output. -/
theorem same_label_reprogram_changes_game :
    ¬ (runOracle (fun x => reprogramAt toyOracle (formatted muLabel [1]) 0
      (formatted muLabel x)) twoQueryGame =
    runOracle (fun x => toyOracle (formatted muLabel x)) twoQueryGame) := by decide +kernel
end Cross

#verify_constructive transparent_boundary boundary_of_committee_trace
  boundary_of_hem_opening_batch compactHemInst_valid
  hemOpeningShardVerify_accepts hemOpeningShardVerify_tree_accepts
  hemOpeningShardVerify_rejects_per_signer hemOpeningShardVerify_boundary
  hem_opening_regime_instance
  fixtures_are_modelled_outputs native_accepts
  native_rejects_other_message native_rejects_other_key native_rejects_tampered_randomizer
  good_full_accepts good_tree_accepts good_bits good_participation good_no_forgery
  good_regime_resolves good_regime_instance committee_trace_satisfied committee_slots
  committee_trace_boundary shared_verify_accepts shared_verify_rejects_per_signer_mode
  rejects_unsigned_per_signer_message
  accepts_signed_per_signer_messages rejects_swapped_signature_table
  rejects_foreign_committee_leaf foreign_committee_leaf_not_accepted
  unsigned_per_signer_message_not_accepted other_key_not_accepted rogue_not_participated unapproved_signature_is_forgery
  mixed_accepts mixed_unapproved_is_one mixed_one_unapproved forgery_regime_instance
  forgery_regime_masses
#verify_constructive hybrid_honest_accepts hybrid_rejects_other_message
  hybrid_envelope_valid_for_every_network hybrid_rejects_relabelled_hrp
  hybrid_rejects_relabelled_version hybrid_address_commitments_differ
  hybrid_rejects_other_keys_address hybrid_rejects_swapped_roles
  hybrid_rejects_rogue_partner hybrid_keybound_instance robust_combiner_instance
  both_components_broken_instance
  real_hybrid_sigs_are_modelled_outputs
  real_hybrid_honest_accepts real_hybrid_rejects_other_message
  real_hybrid_rejects_rogue_partner real_hybrid_keybound_instance
  only_honest_member acceptsA acceptsB stepA stepB
  corrupt_token_not_minted corrupt_quorum_instance two_intent_spending_instance
  rejects_over_per_tx_cap rejects_unlisted_recipient rejects_insufficient_approvals
  rejects_nonce_replay rejects_window_overspend rejects_stale_window token_is_intent_specific
  window_advance_accepts window_advance_rejects window_advance_rejects_wrong_tag
#verify_constructive compress12FF_eq_jive deployed_compress_preimage_hits_transcript
  real_transcript_consistent real_transcript_instance real_poseidon_nondegenerate
  real_poseidon_raw_vs_feedforward real_poseidon_feedforward_misses small_field_bad_count digest_separates_distinct_hashes
  digest_collision_is_hash_collision real_label_partition_instance
  foreign_label_reprogram_instance same_label_reprogram_changes_game
#verify_inhabited Qsag.Composed.merged_quorum_reduction good_regime_instance
#verify_inhabited Qsag.Composed.merged_quorum_reduction hem_opening_regime_instance
#verify_inhabited Qsag.Composed.quorum_aggregation_reduction good_regime_instance
#verify_inhabited Qsag.Composed.quorum_aggregation_reduction hem_opening_regime_instance
#verify_inhabited Qsag.Composed.quorum_advantage_from_extraction forgery_regime_instance
#verify_inhabited Qsag.HybridSecurity.dual_key_euf_cma hybrid_keybound_instance
#verify_inhabited Qsag.HybridSecurity.dual_key_euf_cma real_hybrid_keybound_instance
#verify_inhabited Qsag.HybridSecurity.threshold_policy_composition corrupt_quorum_instance
#verify_inhabited Qsag.HybridSecurity.threshold_spending_safety two_intent_spending_instance
#verify_inhabited Qsag.CrossProtocol.checked_preimage_is_transcript_hit real_transcript_instance
#verify_inhabited Qsag.CrossProtocol.universal_customization_partition
  real_label_partition_instance
#tooth_pair Qsag.Composed.merged_quorum_reduction vs foreign_committee_leaf_not_accepted
#tooth_pair Qsag.Composed.binary_merge_sound vs unsigned_per_signer_message_not_accepted
#tooth_pair Qsag.Composed.quorum_aggregation_reduction vs other_key_not_accepted
#tooth_pair Qsag.HybridSecurity.dual_key_euf_cma vs hybrid_rejects_other_message
#tooth_pair Qsag.HybridSecurity.address_binding vs hybrid_rejects_relabelled_hrp
#tooth_pair Qsag.HybridSecurity.rogue_partner_resistance vs hybrid_rejects_rogue_partner
#tooth_pair Qsag.HybridSecurity.threshold_policy_composition vs rejects_insufficient_approvals
#tooth_pair Qsag.HybridSecurity.ledger_trace_safety vs rejects_nonce_replay
#tooth_pair Qsag.HybridSecurity.threshold_spending_safety vs rejects_window_overspend
#tooth_pair Qsag.HybridSecurity.authorized_window_binding vs window_advance_rejects_wrong_tag
#tooth_pair Qsag.CrossProtocol.inverse_feedforward_relation vs real_poseidon_feedforward_misses
#tooth_pair Qsag.CrossProtocol.isolated_game_zero_drift vs same_label_reprogram_changes_game

end Qsag.CompositionInstances

/-! ## Evaluated `Composed` fixtures (moved from `ComposedQsAgAndMergeSecurity`) -/
namespace Qsag.Composed
set_option autoImplicit false

theorem inhabited_tree : ∃ root verify tree,
    checkTree (n := 2) root verify 16 tree = true ∧ tree.bitmap.getLsbD 0 = true ∧
    ∃ s ∈ tree.leaves, ∃ st : WhirStageSpec, st ∈ s.schedule.stages :=
  ⟨exampleHeader, exampleVerifier, exampleTree, by decide, by decide,
    exampleShard 1#2, by simp [exampleTree, MergeTree.leaves],
    (whirStageSchedule 2).stages.headD ⟨0,0,0⟩, by decide⟩
theorem tooth_overlap : ∃ a b : BitVec 2,
    a &&& b ≠ 0#2 ∧ weight (a ||| b) < weight a + weight b ∧
    checkTree exampleHeader exampleVerifier 16
      (.branch (.leaf (exampleShard a)) (.leaf (exampleShard b)) (a ||| b)) = false :=
  ⟨1#2, 1#2, by decide, by decide, by decide⟩
/-- The outer-bad branch is reachable; the honest approval branch has its own fixture. -/
theorem inhabited_reduction : ∃ geom custody verify bad,
    ExtractionBoundary (n := 2) geom custody verify bad ∧
    ∃ s : Shard 2, ∃ v : Fin 2, verify s = true ∧ s.bitmap.getLsbD v.val = true ∧
    ∃ root tree, checkTree root verify 16 tree = true ∧ tree.bitmap.getLsbD v.val = true := by
  refine ⟨compactAuditGeom, (fun _ => exampleCustody), exampleVerifier,
    (fun _ => True), ⟨fun _ _ => .inl trivial⟩, exampleShard 1#2, ⟨0, by decide⟩,
    by decide, by decide, exampleHeader, exampleTree, by decide, by decide⟩
theorem inhabited_shard_bound : ∃ root verify tree, ∃ bad : Fin 2 → Shard 2 → Bool,
    checkTree root verify 16 tree = true ∧
    (qsum 2 fun ω => if treeBad (bad ω) tree then 1 else 0) = 2 :=
  ⟨exampleHeader, exampleVerifier, exampleTree, (fun _ _ => true), by decide, by
    show (qsum 2 fun _ => 1) = 2
    rw [qsum_const]⟩
#verify_inhabited binary_merge_sound inhabited_tree
#verify_inhabited depth_sixteen inhabited_tree
#verify_inhabited selected_leaf inhabited_tree
#verify_inhabited schedule_floor inhabited_tree
#tooth_pair binary_merge_sound vs tooth_overlap
#tooth_pair additive_shard_bound vs tooth_overlap
#verify_inhabited quorum_aggregation_reduction inhabited_reduction
#verify_inhabited merged_quorum_reduction inhabited_reduction
#verify_inhabited additive_shard_bound inhabited_shard_bound
#verify_inhabited composed_advantage_bound inhabited_union
#tooth_pair composed_advantage_bound vs tooth_omit_outer
#tooth_pair quorum_advantage_from_extraction vs tooth_omit_outer

end Qsag.Composed
end
