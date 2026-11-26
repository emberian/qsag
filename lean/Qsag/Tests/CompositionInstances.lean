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
composed with `SuccinctAggregationIop`. Similarly, alongside the `envCshakeHash` /
`cshakeTranscriptVerifier` envelope controls, `cshakeHybridHash` (`evalCshake256Sponge keccakF1600`) and
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
      (if v.val = 0 then 37 else 45) [] := by
  intro v
  match v with
  | ⟨0, _⟩ =>
    simp only [pkOf, sigOf, skOf, lane, ↓reduceIte]
    rw [deriveAggPublicKey_compactAuditGeom, signAggNative_compactAuditGeom,
        auditSkSeed.public_eqs, auditPkSeed.public_eqs, auditRRand.public_eqs,
        auditMsg.public_eqs, compactJortsPkRoot_kat0, compactJortsSign1_audit0]
    exact ⟨rfl, rfl⟩
  | ⟨1, _⟩ =>
    have h10 : ¬ ((1 : Nat) = 0) := by decide
    dsimp only [pkOf, sigOf, skOf, lane]
    simp only [h10, ↓reduceIte]
    rw [deriveAggPublicKey_compactAuditGeom, signAggNative_compactAuditGeom,
        auditPkSeed.public_eqs, auditRRand.public_eqs, auditMsg.public_eqs,
        compactJortsPkRoot_kat1, compactJortsSign1_audit1]
    exact ⟨rfl, rfl⟩

def otherMsg : List UInt8 := [0x51, 0x53, 0x41, 0x48]

theorem native_accepts : ∀ v : Fin 2,
    verifyAggNativeSig compactAuditGeom (pkOf v) auditMsg (sigOf v) = true := by
  intro v
  match v with
  | ⟨0, _⟩ =>
    simp only [pkOf, sigOf, lane, ↓reduceIte]
    rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs,
        auditRRand.public_eqs, auditMsg.public_eqs]
    exact compactJortsVerify1_audit_accepts0
  | ⟨1, _⟩ =>
    have h10 : ¬ ((1 : Nat) = 0) := by decide
    dsimp only [pkOf, sigOf, lane]
    simp only [h10, ↓reduceIte]
    rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs,
        auditRRand.public_eqs, auditMsg.public_eqs]
    exact compactJortsVerify1_audit_accepts1

theorem native_rejects_other_message : ∀ v : Fin 2,
    verifyAggNativeSig compactAuditGeom (pkOf v) otherMsg (sigOf v) = false := by
  intro v
  match v with
  | ⟨0, _⟩ =>
    simp only [pkOf, sigOf, lane, otherMsg, ↓reduceIte]
    rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs, auditRRand.public_eqs]
    exact compactJortsVerify1_audit_rejects_otherMsg0
  | ⟨1, _⟩ =>
    have h10 : ¬ ((1 : Nat) = 0) := by decide
    dsimp only [pkOf, sigOf, lane, otherMsg]
    simp only [h10, ↓reduceIte]
    rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs, auditRRand.public_eqs]
    exact compactJortsVerify1_audit_rejects_otherMsg1

theorem native_rejects_other_key :
    verifyAggNativeSig compactAuditGeom (pkOf 1) auditMsg (sigOf 0) = false := by
  have h10 : ¬ ((1 : Nat) = 0) := by decide
  change verifyAggNativeSig compactAuditGeom (pkOf ⟨1, by decide⟩) auditMsg (sigOf ⟨0, by decide⟩) = false
  dsimp only [pkOf, sigOf, lane]
  simp only [h10, ↓reduceIte]
  rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs,
      auditRRand.public_eqs, auditMsg.public_eqs]
  exact compactJortsVerify1_audit_rejects_otherKey

theorem native_rejects_tampered_randomizer :
    verifyAggNativeSig compactAuditGeom (pkOf 0) auditMsg
      { sigOf 0 with rRand := auditPkSeed } = false := by
  change verifyAggNativeSig compactAuditGeom (pkOf ⟨0, by decide⟩) auditMsg
    { sigOf ⟨0, by decide⟩ with rRand := auditPkSeed } = false
  simp only [pkOf, sigOf, lane, ↓reduceIte]
  rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs, auditMsg.public_eqs]
  exact compactJortsVerify1_audit_rejects_tamperedRand

/-- 2-of-3 custody with one corrupt party; honest party `1` logged `auditMsg` in epoch 7. -/
def custodyOf (v : Fin 2) : Custody :=
  ⟨⟨pkOf v, 2, 3, [0], [auditMsg], []⟩, 7, [1],
    fun p ep msg => decide (p = 1 ∧ ep = 7 ∧ msg = auditMsg)⟩

private theorem finRange_two : List.finRange 2 = [0, 1] := rfl


/-- `SigningMode.message` on the shared mode, through its exported equation. -/
theorem shared_message (m : List UInt8) (v : Nat) : (SigningMode.shared m).message v = m := by
  simp only [SigningMode.message.public_eqs]
/-- The custody shape of `custodyOf`, over an arbitrary key and message: `quorumParticipated`
is run through its exported equation, the key and the message are not inspected. -/
theorem logged_custody_participates (pk : AggValidatorPk) (m : List UInt8) :
    quorumParticipated ⟨⟨pk, 2, 3, [0], [m], []⟩, 7, [1],
      fun p ep msg => decide (p = 1 ∧ ep = 7 ∧ msg = m)⟩ m = true := by
  rw [quorumParticipated.public_eqs]
  have hv : validThresholdApproval (⟨pk, 2, 3, [0], [m], []⟩ : IdealTsigState AggValidatorPk (List UInt8))
      [1] = true := rfl
  have hl : ([1] : List Nat).all (fun p => decide (p = 1 ∧ 7 = 7 ∧ m = m)) = true := by
    rw [List.all_cons, List.all_nil, Bool.and_true]
    exact decide_eq_true ⟨rfl, rfl, rfl⟩
  exact Bool.and_eq_true_iff.mpr ⟨hv, hl⟩
/-- The same custody with an empty approval log does not participate. -/
theorem unlogged_custody_not_participated (pk : AggValidatorPk) (m : List UInt8) :
    quorumParticipated ⟨⟨pk, 2, 3, [0], [m], []⟩, 7, [1], fun _ _ _ => false⟩ m = false := by
  rw [quorumParticipated.public_eqs]
  exact Bool.and_false _
theorem good_participation : ∀ v : Fin 2,
    quorumParticipated (custodyOf v) auditMsg = true :=
  fun v => logged_custody_participates (pkOf v) auditMsg

theorem good_no_forgery (v : Fin 2) :
    ¬ QuorumForgery compactAuditGeom (custodyOf v) auditMsg := by
  intro hf
  obtain ⟨_, _, hq⟩ := (quorumForgery_iff _ _ _).mp hf
  rw [good_participation v] at hq
  cases hq


def committeeStmt : AggArithPublicStmt := ⟨compactAuditGeom, auditMsg, [pkOf 0, pkOf 1], 1⟩
/-- Well-formedness of the two-key committee statement, from the owner's geometry fact, the
exported geometry fields and the inequality of the two literal keys. -/
theorem committeeStmt_wellFormed : committeeStmt.wellFormed = true := by
  have hg : compactAuditGeom.wellFormed = true := deployedAggGeometries_wellFormed.2.2
  have hp : compactAuditGeom.profile = AggSigProfile.xmssPoseidon2 := by
    rw [compactAuditGeom.public_eqs]
  have hne : pkOf 0 ≠ pkOf 1 := fun h =>
    absurd (congrArg (fun p : AggValidatorPk => p.pkRoot.x0.val) h) (by decide +kernel)
  have hnd : [pkOf 0, pkOf 1].Nodup :=
    List.Pairwise.cons (fun b hb => by
        cases hb with
        | head => exact hne
        | tail _ h => nomatch h)
      (List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil)
  show (compactAuditGeom.wellFormed && !([pkOf 0, pkOf 1] : List AggValidatorPk).isEmpty &&
      decide ([pkOf 0, pkOf 1].Nodup) &&
      decide (([pkOf 0, pkOf 1] : List AggValidatorPk).length ≤ 2 ^ 1) &&
      ((AggSigProfile.xmssPoseidon2 == compactAuditGeom.profile) &&
        ((AggSigProfile.xmssPoseidon2 == compactAuditGeom.profile) && true))) = true
  rw [hg, decide_eq_true hnd, hp, beq_self_eq_true]
  rfl
theorem committee_trace_satisfied :
    traceSatisfiesAllConstraints committeeStmt
      (buildHonestAggExecutionTrace committeeStmt [sigOf 0, sigOf 1]) = true :=
  buildHonestAggExecutionTrace_satisfies_constraints committeeStmt _ committeeStmt_wellFormed rfl
    (fun k hkP hkS => match k, hkP, hkS with
      | 0, _, _ => native_accepts 0
      | 1, _, _ => native_accepts 1
      | k + 2, h, _ => absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))
          (Nat.not_succ_le_zero k))
theorem committee_slots : ∀ v : Fin 2,
    committeeStmt.committeePks[v.val]? = some (custodyOf v).state.pk :=
  fun v => match v with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

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


theorem other_key_not_accepted :
    ¬ (verifyAggNativeSig compactAuditGeom (pkOf 1) auditMsg (sigOf 0) = true) :=
  not_true_of_false native_rejects_other_key

/-- Same keys and signatures, but no custodian logged an approval. -/
def rogueCustody (v : Fin 2) : Custody := { custodyOf v with approvalLog := fun _ _ _ => false }
theorem rogue_not_participated : ∀ v : Fin 2,
    quorumParticipated (rogueCustody v) auditMsg = false :=
  fun v => unlogged_custody_not_participated (pkOf v) auditMsg
/-- The forgery event is witnessed by a real accepted signature. -/
theorem unapproved_signature_is_forgery (v : Fin 2) :
    QuorumForgery compactAuditGeom (rogueCustody v) auditMsg :=
  (quorumForgery_iff _ _ _).mpr ⟨sigOf v, native_accepts v, rogue_not_participated v⟩

def mixedCustody (v : Fin 2) : Custody := if v.val = 0 then custodyOf v else rogueCustody v
theorem mixed_unapproved_is_one : ∀ v : Fin 2,
    quorumParticipated (mixedCustody v) auditMsg = false → decide (v.val = 1) = true := by
  intro v
  match v with
  | ⟨0, _⟩ =>
    intro h
    have h' : quorumParticipated (custodyOf 0) auditMsg = false := h
    rw [good_participation 0] at h'
    cases h'
  | ⟨1, _⟩ => intro _; rfl
theorem mixed_one_unapproved : quorumParticipated (mixedCustody 1) auditMsg = false :=
  unlogged_custody_not_participated (pkOf 1) auditMsg


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

/-! The `cSHAKE256` envelope fixtures (`envCshakeHash`, `cshakeTranscriptVerifier`, `envelopeFor`, `hk`, `paid`, …, the
`hybrid_*` and combiner instances) and the policy-release fixtures (`pol`, `payA`, `payB`, `acceptsA`,
…, `rejects_*`, `window_advance_*`) are proved in
`Protocol/Signing/HybridAddrPolicyAndFullPresetSecurity` under the same names. -/

/-! ### Real `cSHAKE256` (`keccakF1600`) + `verifyAggNativeSig` (`Poseidon2` Jorts) Hybrid Envelope -/

/-- ASCII customization string `"QSAG.HYBRID.V2"` for `cSHAKE256` envelope hashing. -/
def hybridCshakeTag : Bytes :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x48, 0x59, 0x42, 0x52, 0x49, 0x44, 0x2E, 0x56, 0x32]

def beNat (bs : Bytes) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Real 256-bit `cSHAKE256` (`evalCshake256Sponge keccakF1600`) domain-separated hash for
`HybridSecurity.Hash` under customization tag `"QSAG.HYBRID.V2"`. -/
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
public-key and signature bytes for the native Jorts hybrid envelope. -/
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

private theorem encodeLane4Bytes_length (d : Digest4) :
    (encodeLane4Bytes d).length = 32 := by
  simp only [encodeLane4Bytes, List.length_append, length_be]

private theorem decodeLane4Bytes_encodeLane4Bytes (d : Digest4) :
    decodeLane4Bytes (encodeLane4Bytes d) = some d := by
  have hLen : (encodeLane4Bytes d).length = 32 := encodeLane4Bytes_length d
  unfold decodeLane4Bytes
  simp only [hLen, ↓reduceIte]
  dsimp only [encodeLane4Bytes]
  have h8 : ∀ x : Nat, (be 8 x).length = 8 := length_be 8
  let tail1 := be 8 d.x1.val ++ (be 8 d.x2.val ++ be 8 d.x3.val)
  have ht0 : (be 8 d.x0.val ++ tail1).take 8 = be 8 d.x0.val := take_append_of_len_eq (h8 _)
  have hd8 : (be 8 d.x0.val ++ tail1).drop 8 = tail1 := drop_append_of_len_eq (h8 _)
  have ht1 : tail1.take 8 = be 8 d.x1.val := take_append_of_len_eq (h8 _)
  have hd16 : (be 8 d.x0.val ++ tail1).drop 16 = be 8 d.x2.val ++ be 8 d.x3.val := by
    have hdd : ((be 8 d.x0.val ++ tail1).drop 8).drop 8 = (be 8 d.x0.val ++ tail1).drop 16 := by
      rw [List.drop_drop]
    rw [← hdd, hd8]
    exact drop_append_of_len_eq (h8 _)
  have ht2 : (be 8 d.x2.val ++ be 8 d.x3.val).take 8 = be 8 d.x2.val :=
    take_append_of_len_eq (h8 _)
  have hd24 : (be 8 d.x0.val ++ tail1).drop 24 = be 8 d.x3.val := by
    have hdd : ((be 8 d.x0.val ++ tail1).drop 16).drop 8 = (be 8 d.x0.val ++ tail1).drop 24 := by
      rw [List.drop_drop]
    rw [← hdd, hd16]
    exact drop_append_of_len_eq (h8 _)
  have ht3 : (be 8 d.x3.val).take 8 = be 8 d.x3.val :=
    List.take_of_length_le (Nat.le_of_eq (h8 d.x3.val))
  rw [ht0, hd8, ht1, hd16, ht2, hd24, ht3]
  have hG : ∀ g : Goldilocks, Goldilocks.ofNat (beNat (be 8 g.val)) = g := fun g => by
    have hLt : g.val < 256 ^ 8 := Nat.lt_trans g.isLt (by decide)
    change Goldilocks.ofNat (ofBE (be 8 g.val)) = g
    rw [ofBE_be hLt]
    exact Goldilocks.ext (Nat.mod_eq_of_lt g.isLt)
  rw [hG, hG, hG, hG]

private theorem decodeCompactJortsPk_encode (s r : Digest4) :
    decodeCompactJortsPk (encodeCompactJortsPk ⟨.xmssPoseidon2, s, r⟩) =
      some ⟨.xmssPoseidon2, s, r⟩ := by
  have h32s : (encodeLane4Bytes s).length = 32 := encodeLane4Bytes_length s
  have h32r : (encodeLane4Bytes r).length = 32 := encodeLane4Bytes_length r
  have h64 : (encodeCompactJortsPk ⟨.xmssPoseidon2, s, r⟩).length = 64 := by
    simp only [encodeCompactJortsPk, List.length_append, h32s, h32r]
  unfold decodeCompactJortsPk
  simp only [h64, ↓reduceIte]
  dsimp only [encodeCompactJortsPk]
  rw [take_append_of_len_eq h32s, drop_append_of_len_eq h32s,
      decodeLane4Bytes_encodeLane4Bytes, decodeLane4Bytes_encodeLane4Bytes]

private theorem decodeCompactJortsSig_encode (rR c0 c1 s0 : Digest4) (idx ctr : Nat)
    (hIdx : idx < 256 ^ 8) (hCtr : ctr < 256 ^ 8) :
    decodeCompactJortsSig
      (encodeCompactJortsSig ⟨.xmssPoseidon2, rR, idx, [], [⟨ctr, [c0, c1], [s0]⟩]⟩) =
    some ⟨.xmssPoseidon2, rR, idx, [], [⟨ctr, [c0, c1], [s0]⟩]⟩ := by
  let body := encodeLane4Bytes rR ++
    (encodeLane4Bytes c0 ++ (encodeLane4Bytes c1 ++ encodeLane4Bytes s0))
  have h144 : (encodeCompactJortsSig
      ⟨.xmssPoseidon2, rR, idx, [], [⟨ctr, [c0, c1], [s0]⟩]⟩).length = 144 := by
    simp only [encodeCompactJortsSig, List.length_append, length_be, encodeLane4Bytes_length]
  unfold decodeCompactJortsSig
  simp only [h144, ↓reduceIte]
  dsimp only [encodeCompactJortsSig]
  have h8i : (be 8 idx).length = 8 := length_be 8 idx
  have h8c : (be 8 ctr).length = 8 := length_be 8 ctr
  let full := be 8 idx ++ (be 8 ctr ++ body)
  have ht0 : full.take 8 = be 8 idx := take_append_of_len_eq h8i
  have hd8 : full.drop 8 = be 8 ctr ++ body := drop_append_of_len_eq h8i
  have ht8 : (be 8 ctr ++ body).take 8 = be 8 ctr := take_append_of_len_eq h8c
  have hd16 : full.drop 16 = body := by
    have hdd : (full.drop 8).drop 8 = full.drop 16 := by rw [List.drop_drop]
    rw [← hdd, hd8]
    exact drop_append_of_len_eq h8c
  have hd48 : full.drop 48 =
      encodeLane4Bytes c0 ++ (encodeLane4Bytes c1 ++ encodeLane4Bytes s0) := by
    have hdd : (full.drop 16).drop 32 = full.drop 48 := by rw [List.drop_drop]
    rw [← hdd, hd16]
    exact drop_append_of_len_eq (encodeLane4Bytes_length rR)
  have hd80 : full.drop 80 = encodeLane4Bytes c1 ++ encodeLane4Bytes s0 := by
    have hdd : (full.drop 48).drop 32 = full.drop 80 := by rw [List.drop_drop]
    rw [← hdd, hd48]
    exact drop_append_of_len_eq (encodeLane4Bytes_length c0)
  have hd112 : full.drop 112 = encodeLane4Bytes s0 := by
    have hdd : (full.drop 80).drop 32 = full.drop 112 := by rw [List.drop_drop]
    rw [← hdd, hd80]
    exact drop_append_of_len_eq (encodeLane4Bytes_length c1)
  have htS : (encodeLane4Bytes s0).take 32 = encodeLane4Bytes s0 :=
    List.take_of_length_le (Nat.le_of_eq (encodeLane4Bytes_length s0))
  rw [ht0, hd8, ht8, hd16, take_append_of_len_eq (encodeLane4Bytes_length rR),
      hd48, take_append_of_len_eq (encodeLane4Bytes_length c0),
      hd80, take_append_of_len_eq (encodeLane4Bytes_length c1),
      hd112, htS,
      decodeLane4Bytes_encodeLane4Bytes, decodeLane4Bytes_encodeLane4Bytes,
      decodeLane4Bytes_encodeLane4Bytes, decodeLane4Bytes_encodeLane4Bytes]
  change some (⟨.xmssPoseidon2, rR, ofBE (be 8 idx), [],
    [⟨ofBE (be 8 ctr), [c0, c1], [s0]⟩]⟩ : AggNativeSignature) = _
  rw [ofBE_be hIdx, ofBE_be hCtr]

private theorem be32_cshakeHybridHash (x : Preimage) :
    be 32 (cshakeHybridHash x).val = cshake256Xof 32 hybridCshakeTag (encodePre x) := by
  dsimp only [cshakeHybridHash]
  rw [evalCshake256Sponge_keccak_eq_cshake256Xof]
  let out := cshake256Xof 32 hybridCshakeTag (encodePre x)
  have hLen : out.length = 32 := cshake256Xof_length 32 hybridCshakeTag (encodePre x)
  have hLt : ofBE out < 256 ^ 32 := hLen ▸ ofBE_lt out
  change be 32 (ofBE out % 256 ^ 32) = out
  rw [Nat.mod_eq_of_lt hLt]
  exact hLen ▸ be_ofBE out

private theorem encPre_keyCl0 :
    encodePre (.key false .secpMl44 (encodeCompactJortsPk (pkOf 0))) =
      [1, 5, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 66,
       0, 0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 88, 61, 55, 123, 250, 231, 244, 53, 179,
       171, 228, 148, 46, 202, 181, 172, 97, 67, 65, 47, 117, 121, 240, 1, 53,
       183, 29, 98, 119, 78, 188, 107, 79] := by
  rw [encodePre.public_eqs.1, suiteBytes.public_eqs.1]
  change (1 : UInt8) :: ([5, 1, 0, 1, 1, 1] ++ encodeCompactJortsPk (pkOf ⟨0, by decide⟩)) = _
  simp only [encodeCompactJortsPk, encodeLane4Bytes, pkOf, lane, ↓reduceIte]
  rw [auditPkSeed.public_eqs]
  decide +kernel

private theorem encPre_keyPq1 :
    encodePre (.key true .secpMl44 (encodeCompactJortsPk (pkOf 1))) =
      [2, 5, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 66,
       0, 0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 88, 243, 236, 128, 81, 170, 206, 95, 106,
       222, 195, 136, 76, 52, 227, 230, 42, 204, 98, 226, 187, 142, 144, 108, 228,
       24, 10, 119, 74, 26, 57, 199, 54] := by
  have h10 : ¬ ((1 : Nat) = 0) := by decide
  rw [encodePre.public_eqs.1, suiteBytes.public_eqs.1]
  change (2 : UInt8) :: ([5, 1, 0, 1, 1, 1] ++ encodeCompactJortsPk (pkOf ⟨1, by decide⟩)) = _
  dsimp only [encodeCompactJortsPk, encodeLane4Bytes, pkOf, lane]
  simp only [h10, ↓reduceIte]
  rw [auditPkSeed.public_eqs]
  decide +kernel

private theorem encPre_keyCl1 :
    encodePre (.key false .secpMl44 (encodeCompactJortsPk (pkOf 1))) =
      [1, 5, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 66,
       0, 0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 88, 243, 236, 128, 81, 170, 206, 95, 106,
       222, 195, 136, 76, 52, 227, 230, 42, 204, 98, 226, 187, 142, 144, 108, 228,
       24, 10, 119, 74, 26, 57, 199, 54] := by
  have h10 : ¬ ((1 : Nat) = 0) := by decide
  rw [encodePre.public_eqs.1, suiteBytes.public_eqs.1]
  change (1 : UInt8) :: ([5, 1, 0, 1, 1, 1] ++ encodeCompactJortsPk (pkOf ⟨1, by decide⟩)) = _
  dsimp only [encodeCompactJortsPk, encodeLane4Bytes, pkOf, lane]
  simp only [h10, ↓reduceIte]
  rw [auditPkSeed.public_eqs]
  decide +kernel

private theorem be32_keyHash_real_false :
    be 32 (keyHash cshakeHybridHash realHk false).val =
      [43, 75, 67, 27, 105, 156, 92, 201, 184, 206, 75, 28, 48, 223, 0, 28,
       57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39, 173, 45, 208, 180, 136] := by
  rw [keyHash.public_eqs]
  simp only [realHk, Bool.false_eq_true, ↓reduceIte]
  rw [be32_cshakeHybridHash, encPre_keyCl0]
  exact cshake256_hybridV2_keyCl0_kat

private theorem be32_keyHash_real_true :
    be 32 (keyHash cshakeHybridHash realHk true).val =
      [201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7, 149,
       86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127] := by
  rw [keyHash.public_eqs]
  simp only [realHk, ↓reduceIte]
  rw [be32_cshakeHybridHash, encPre_keyPq1]
  exact cshake256_hybridV2_keyPq1_kat

private theorem be32_idCommit_real :
    be 32 (idCommit cshakeHybridHash realHk).val =
      [206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
       216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21] := by
  rw [idCommit.public_eqs, idInput.public_eqs, be32_cshakeHybridHash, encodePre.public_eqs.2.1]
  have hs : realHk.suite = .secpMl44 := rfl
  rw [hs, suiteBytes.public_eqs.1, be32_keyHash_real_false, be32_keyHash_real_true]
  exact cshake256_hybridV2_idReal_kat

private theorem transcriptFields_real_paid_false :
    transcriptFields (transcript cshakeHybridHash realHk false paid) =
      [1, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
       216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
       92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
       173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
       149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121] := by
  rw [transcript.public_eqs, transcriptFields.public_eqs]
  have hs : realHk.suite = .secpMl44 := rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hs, suiteBytes.public_eqs.1,
    be32_idCommit_real, be32_keyHash_real_false, be32_keyHash_real_true, paid.public_eqs]
  rfl

private theorem transcriptFields_real_paid_true :
    transcriptFields (transcript cshakeHybridHash realHk true paid) =
      [2, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
       216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
       92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
       173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
       149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121] := by
  rw [transcript.public_eqs, transcriptFields.public_eqs]
  have hs : realHk.suite = .secpMl44 := rfl
  simp only [↓reduceIte, hs, suiteBytes.public_eqs.1,
    be32_idCommit_real, be32_keyHash_real_false, be32_keyHash_real_true, paid.public_eqs]
  rfl

private theorem transcriptFields_real_unpaid_false :
    transcriptFields (transcript cshakeHybridHash realHk false unpaid) =
      [1, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
       216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
       92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
       173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
       149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 122] := by
  rw [transcript.public_eqs, transcriptFields.public_eqs]
  have hs : realHk.suite = .secpMl44 := rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hs, suiteBytes.public_eqs.1,
    be32_idCommit_real, be32_keyHash_real_false, be32_keyHash_real_true, unpaid.public_eqs]
  rfl

private theorem transcriptFields_rogue_paid_true :
    transcriptFields
        (transcript cshakeHybridHash { realHk with classical := encodeCompactJortsPk (pkOf 1) } true paid) =
      [2, 5, 1, 0, 1, 1, 1, 120, 130, 148, 209, 221, 48, 122, 11, 201, 31, 97, 23, 207, 212, 76, 157,
       190, 150, 250, 193, 174, 105, 54, 248, 197, 104, 124, 130, 106, 159, 53, 46, 94, 59, 166, 234,
       77, 144, 26, 197, 209, 246, 48, 107, 133, 48, 181, 232, 37, 98, 85, 103, 78, 54, 227, 77, 248,
       234, 245, 170, 196, 166, 208, 0, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67,
       25, 7, 149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121] := by
  let rHk : Keys := { realHk with classical := encodeCompactJortsPk (pkOf 1) }
  have hCl : be 32 (keyHash cshakeHybridHash rHk false).val =
      [94, 59, 166, 234, 77, 144, 26, 197, 209, 246, 48, 107, 133, 48, 181, 232,
       37, 98, 85, 103, 78, 54, 227, 77, 248, 234, 245, 170, 196, 166, 208, 0] := by
    rw [keyHash.public_eqs]
    simp only [rHk, realHk, Bool.false_eq_true, ↓reduceIte]
    rw [be32_cshakeHybridHash, encPre_keyCl1]
    exact cshake256_hybridV2_keyCl1_kat
  have hPq : be 32 (keyHash cshakeHybridHash rHk true).val =
      [201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7, 149,
       86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127] := by
    rw [keyHash.public_eqs]
    simp only [rHk, realHk, ↓reduceIte]
    rw [be32_cshakeHybridHash, encPre_keyPq1]
    exact cshake256_hybridV2_keyPq1_kat
  have hId : be 32 (idCommit cshakeHybridHash rHk).val =
      [120, 130, 148, 209, 221, 48, 122, 11, 201, 31, 97, 23, 207, 212, 76, 157,
       190, 150, 250, 193, 174, 105, 54, 248, 197, 104, 124, 130, 106, 159, 53, 46] := by
    rw [idCommit.public_eqs, idInput.public_eqs, be32_cshakeHybridHash, encodePre.public_eqs.2.1]
    have hs : rHk.suite = .secpMl44 := rfl
    rw [hs, suiteBytes.public_eqs.1, hCl, hPq]
    exact cshake256_hybridV2_idRogue_kat
  change transcriptFields (transcript cshakeHybridHash rHk true paid) = _
  rw [transcript.public_eqs, transcriptFields.public_eqs]
  have hs : rHk.suite = .secpMl44 := rfl
  simp only [↓reduceIte, hs, suiteBytes.public_eqs.1, hId, hCl, hPq, paid.public_eqs]
  rfl

theorem real_hybrid_sigs_are_modelled_outputs :
    realHybridSig0 = signAggNative compactAuditGeom (skOf 0) (pkOf 0)
      (transcriptFields (transcript cshakeHybridHash realHk false paid)) auditRRand 0 21 [] ∧
    realHybridSig1 = signAggNative compactAuditGeom (skOf 1) (pkOf 1)
      (transcriptFields (transcript cshakeHybridHash realHk true paid)) auditRRand 1 122 [] := by
  refine ⟨?_, ?_⟩
  · rw [transcriptFields_real_paid_false]
    change realHybridSig0 = signAggNative compactAuditGeom (skOf ⟨0, by decide⟩)
      (pkOf ⟨0, by decide⟩) _ auditRRand 0 21 []
    simp only [realHybridSig0, skOf, pkOf, lane, ↓reduceIte]
    rw [signAggNative_compactAuditGeom, auditSkSeed.public_eqs, auditPkSeed.public_eqs,
        auditRRand.public_eqs, compactJortsSign1_hybrid0]
  · have h10 : ¬ ((1 : Nat) = 0) := by decide
    rw [transcriptFields_real_paid_true]
    change realHybridSig1 = signAggNative compactAuditGeom (skOf ⟨1, by decide⟩)
      (pkOf ⟨1, by decide⟩) _ auditRRand 1 122 []
    dsimp only [realHybridSig1, skOf, pkOf, lane]
    simp only [h10, ↓reduceIte]
    rw [signAggNative_compactAuditGeom, auditPkSeed.public_eqs,
        auditRRand.public_eqs, compactJortsSign1_hybrid1]

def realEnvelopePaid : HybridPinnedEnvelope :=
  ⟨realHk, encodeCompactJortsSig realHybridSig0, encodeCompactJortsSig realHybridSig1⟩

theorem real_hybrid_honest_accepts :
    validateForAddress cshakeHybridHash realEnvelopePaid (addressOf cshakeHybridHash realHk hrpQs 1) ∧
    verifyWith cshakeHybridHash jortsNativeVerifier jortsNativeVerifier realEnvelopePaid paid := by
  refine ⟨?_, ?_⟩
  · rw [validateForAddress.public_eqs, addressOf.public_eqs]
    exact ⟨rfl, rfl⟩
  · rw [verifyWith.public_eqs]
    dsimp only [realEnvelopePaid, jortsNativeVerifier]
    have hCl : realHk.classical = encodeCompactJortsPk (pkOf 0) := rfl
    have hPq : realHk.pq = encodeCompactJortsPk (pkOf 1) := rfl
    have hPk0 : decodeCompactJortsPk (encodeCompactJortsPk (pkOf 0)) = some (pkOf 0) :=
      decodeCompactJortsPk_encode _ _
    have hPk1 : decodeCompactJortsPk (encodeCompactJortsPk (pkOf 1)) = some (pkOf 1) :=
      decodeCompactJortsPk_encode _ _
    have hSig0 : decodeCompactJortsSig (encodeCompactJortsSig realHybridSig0) =
        some realHybridSig0 :=
      decodeCompactJortsSig_encode _ _ _ _ 0 21 (by decide) (by decide)
    have hSig1 : decodeCompactJortsSig (encodeCompactJortsSig realHybridSig1) =
        some realHybridSig1 :=
      decodeCompactJortsSig_encode _ _ _ _ 1 122 (by decide) (by decide)
    rw [hCl, hPq, hPk0, hPk1, hSig0, hSig1]
    dsimp only
    refine ⟨?_, ?_⟩
    · rw [transcriptFields_real_paid_false]
      change verifyAggNativeSig compactAuditGeom (pkOf ⟨0, by decide⟩) _ realHybridSig0 = true
      simp only [pkOf, realHybridSig0, lane, ↓reduceIte]
      rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs, auditRRand.public_eqs]
      exact compactJortsVerify1_hybrid_paid0
    · have h10 : ¬ ((1 : Nat) = 0) := by decide
      rw [transcriptFields_real_paid_true]
      change verifyAggNativeSig compactAuditGeom (pkOf ⟨1, by decide⟩) _ realHybridSig1 = true
      dsimp only [pkOf, realHybridSig1, lane]
      simp only [h10, ↓reduceIte]
      rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs, auditRRand.public_eqs]
      exact compactJortsVerify1_hybrid_paid1

theorem real_hybrid_rejects_other_message :
    ¬ verifyWith cshakeHybridHash jortsNativeVerifier jortsNativeVerifier realEnvelopePaid unpaid := by
  rw [verifyWith.public_eqs]
  rintro ⟨h0, _⟩
  dsimp only [realEnvelopePaid, jortsNativeVerifier] at h0
  have hCl : realHk.classical = encodeCompactJortsPk (pkOf 0) := rfl
  have hPk0 : decodeCompactJortsPk (encodeCompactJortsPk (pkOf 0)) = some (pkOf 0) :=
    decodeCompactJortsPk_encode _ _
  have hSig0 : decodeCompactJortsSig (encodeCompactJortsSig realHybridSig0) =
      some realHybridSig0 :=
    decodeCompactJortsSig_encode _ _ _ _ 0 21 (by decide) (by decide)
  rw [hCl, hPk0, hSig0] at h0
  dsimp only at h0
  rw [transcriptFields_real_unpaid_false] at h0
  change verifyAggNativeSig compactAuditGeom (pkOf ⟨0, by decide⟩) _ realHybridSig0 = true at h0
  simp only [pkOf, realHybridSig0, lane, ↓reduceIte] at h0
  rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs, auditRRand.public_eqs,
      compactJortsVerify1_hybrid_unpaid0] at h0
  exact Bool.noConfusion h0

theorem real_hybrid_rejects_rogue_partner :
    ¬ (jortsNativeVerifier realHk.pq
        (transcript cshakeHybridHash { realHk with classical := encodeCompactJortsPk (pkOf 1) } true paid)
        realEnvelopePaid.pqSignature = true) := by
  intro h1
  dsimp only [realEnvelopePaid, jortsNativeVerifier] at h1
  have hPk1 : decodeCompactJortsPk realHk.pq = some (pkOf 1) :=
    decodeCompactJortsPk_encode _ _
  have hSig1 : decodeCompactJortsSig (encodeCompactJortsSig realHybridSig1) =
      some realHybridSig1 :=
    decodeCompactJortsSig_encode _ _ _ _ 1 122 (by decide) (by decide)
  rw [hPk1, hSig1] at h1
  dsimp only at h1
  have h10 : ¬ ((1 : Nat) = 0) := by decide
  rw [transcriptFields_rogue_paid_true] at h1
  change verifyAggNativeSig compactAuditGeom (pkOf ⟨1, by decide⟩) _ realHybridSig1 = true at h1
  dsimp only [pkOf, realHybridSig1, lane] at h1
  simp only [h10, ↓reduceIte] at h1
  rw [verifyAggNativeSig_compactAuditGeom, auditPkSeed.public_eqs, auditRRand.public_eqs,
      compactJortsVerify1_hybrid_rogue1] at h1
  exact Bool.noConfusion h1

attribute [local irreducible] cshakeHybridHash jortsNativeVerifier realEnvelopePaid

theorem real_hybrid_keybound_instance :
    ∃ (H : HybridSecurity.Hash) (vc vp : Verifier) (k : Keys) (hrp : Bytes)
      (v : Nat) (e : HybridPinnedEnvelope) (m : Bytes) (qs : List Bytes),
      validateForAddress H e (addressOf H k hrp v) ∧ verifyWith H vc vp e m ∧ m ∉ qs :=
  ⟨cshakeHybridHash, jortsNativeVerifier, jortsNativeVerifier, realHk, hrpQs, 1,
    realEnvelopePaid, paid, [unpaid],
    real_hybrid_honest_accepts.1, real_hybrid_honest_accepts.2,
    fun h => paid_ne_unpaid (List.mem_singleton.mp h)⟩

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
  rw [poseidon2Compress12FF.public_eqs, poseidon2CompressWeighted_eq,
    poseidon2WeightedFeedForward_eq, jiveCompress.public_eqs, relation.public_eqs]
  simp only [weightedJiveExtra, lane4Add_eq]
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
    (forward_extension _ [] (by rw [Consistent.public_eqs]; exact fun _ _ h => absurd h List.not_mem_nil)
      realX) realY

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
    poseidon2Compress12FF realX.1 realX.2.1 realX.2.2 ≠ lane4Zero := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h0 := congrArg (fun s : State Lane4 => s.1.x0.val) h
    have h1 : (Goldilocks.ofNat 1).val = 1 := by decide
    dsimp only [poseidonEquiv, lane4State, realX] at h0
    rw [domainMerkleNode.public_eqs, poseidon2IvTag.public_eqs, h1] at h0
    exact poseidon2Perm12_realX_kat h0
  · have h0 := congrArg (fun d : Lane4 => d.x0.val) h
    have hz : Goldilocks.zero.val = 0 := rfl
    rw [poseidon2Compress12FF.public_eqs, lane4Zero_eq] at h0
    dsimp only [realX] at h0
    rw [domainMerkleNode.public_eqs, poseidon2IvTag.public_eqs, hz] at h0
    exact poseidon2CompressWeighted_realX_kat h0
/-- On the modelled permutation: one inverse call hits a chosen raw-truncation target, and
the same point misses that target under feed-forward. -/
theorem real_poseidon_raw_vs_feedforward :
    rawTrunc poseidonEquiv (poseidonEquiv.invFun realY) = realY.1 ∧
    jiveCompress weightedJiveExtra poseidonEquiv (poseidonEquiv.invFun realY) ≠
      realY.1 := by
  refine ⟨raw_inverse poseidonEquiv _ _ _, fun h => ?_⟩
  rw [jiveCompress.public_eqs, poseidonEquiv.right_inv realY, relation.public_eqs] at h
  have hLane : lane4Add realY.1
      (lane4Add (poseidonEquiv.invFun realY).1
        (weightedJiveExtra (poseidonEquiv.invFun realY))) = realY.1 := by
    rw [lane4Add_eq, lane4Add_eq]
    exact h
  have h0 := congrArg (fun d : Lane4 => d.x0.val) hLane
  have h7 : (Goldilocks.ofNat 7).val = 7 := by decide
  dsimp only [poseidonEquiv, lane4State, weightedJiveExtra, realY] at h0
  rw [h7] at h0
  exact poseidon2Inv_realY_feedforward_kat h0
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
      = 0 := by
  have hl : smallAvail.length - 1 = 2 := rfl
  simp only [hl, queryValue.public_eqs, relation.public_eqs, extensions.public_eqs,
    Bool.false_eq_true, ↓reduceIte]
  decide +kernel
end SmallField

/-- A hash that separates `[1]` from `[2]` and collides on `[0, 1]` and `[1]`. -/
def foldHash (m : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (m.foldl (fun a b => a * 256 + b.toNat) 0)
theorem digest_separates_distinct_hashes :
    digest5FromBitVec256 (foldHash [1]) ≠ digest5FromBitVec256 (foldHash [2]) :=
  fun h => absurd (congrArg (fun d : Digest5 => d.limb0.val) h) (by decide +kernel)
/-- Equal digests on distinct messages come from the hash, as `digest5_collision_iff` states. -/
theorem digest_collision_is_hash_collision :
    ([0, 1] : List UInt8) ≠ [1] ∧
    digest5FromBitVec256 (foldHash [0, 1]) = digest5FromBitVec256 (foldHash [1]) ∧
    foldHash [0, 1] = foldHash [1] :=
  ⟨by decide, congrArg digest5FromBitVec256 (by decide +kernel), by decide +kernel⟩

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
    runOracle (fun x => toyOracle (formatted muLabel x)) twoQueryGame) := by
  have h1 : formatted muLabel [2, 3] ≠ formatted muLabel [1] := by
    rw [formatted.public_eqs, formatted.public_eqs]
    intro h
    exact absurd (List.append_cancel_left h) (by decide)
  have hpos : toyOracle (formatted muLabel [1]) ≠ 0 := by
    rw [formatted.public_eqs]
    unfold toyOracle
    rw [List.foldl_append]
    exact Nat.succ_ne_zero _
  simp only [twoQueryGame, runOracle.public_eqs, reprogramAt.public_eqs, eq_self, h1, ↓reduceIte,
    Nat.zero_mul, Nat.zero_add]
  intro h
  generalize toyOracle (formatted muLabel [1]) = a at h hpos
  generalize toyOracle (formatted muLabel [2, 3]) = b at h
  omega
end Cross

-- Audited here and now: every instance that does not kernel-execute a sealed primitive.
#verify_constructive good_participation good_no_forgery
  committee_slots
  rogue_not_participated mixed_unapproved_is_one
  mixed_one_unapproved forgery_regime_masses shared_message
  logged_custody_participates unlogged_custody_not_participated committeeStmt_wellFormed
#verify_constructive hybrid_honest_accepts hybrid_rejects_other_message hybrid_envelope_valid_for_every_network
  hybrid_rejects_relabelled_hrp hybrid_rejects_relabelled_version
  hybrid_address_commitments_differ hybrid_rejects_other_keys_address
  hybrid_rejects_swapped_roles hybrid_rejects_rogue_partner hybrid_keybound_instance
  robust_combiner_instance both_components_broken_instance only_honest_member acceptsA
  acceptsB stepA stepB corrupt_token_not_minted corrupt_quorum_instance
  two_intent_spending_instance rejects_over_per_tx_cap rejects_unlisted_recipient
  rejects_insufficient_approvals rejects_nonce_replay rejects_window_overspend
  rejects_stale_window token_is_intent_specific window_advance_accepts
  window_advance_rejects window_advance_rejects_wrong_tag
#verify_constructive compress12FF_eq_jive deployed_compress_preimage_hits_transcript real_transcript_consistent
  real_transcript_instance small_field_bad_count digest_separates_distinct_hashes
  digest_collision_is_hash_collision real_label_partition_instance
  foreign_label_reprogram_instance same_label_reprogram_changes_game
-- Modelled primitive fixtures (native signature, HEM opening batch, cSHAKE, Poseidon2),
-- discharged via owner-evaluated KATs and `#export_eqns` with sealed primitive modules:
#verify_constructive fixtures_are_modelled_outputs
  native_accepts native_rejects_other_message native_rejects_other_key
  native_rejects_tampered_randomizer
  committee_trace_satisfied
  other_key_not_accepted
  unapproved_signature_is_forgery
#verify_constructive real_hybrid_sigs_are_modelled_outputs real_hybrid_honest_accepts
  real_hybrid_rejects_other_message real_hybrid_rejects_rogue_partner
  real_hybrid_keybound_instance
#verify_constructive real_poseidon_nondegenerate real_poseidon_raw_vs_feedforward
  real_poseidon_feedforward_misses


-- The toy-hash and policy instances are evaluated, audited (`#verify_inhabited`, `#tooth_pair`) in
-- `Protocol/Signing/HybridAddrPolicyAndFullPresetSecurity`, where the checked definitions unfold.
#verify_inhabited Qsag.HybridSecurity.dual_key_euf_cma real_hybrid_keybound_instance
#verify_inhabited Qsag.CrossProtocol.checked_preimage_is_transcript_hit real_transcript_instance
#verify_inhabited Qsag.CrossProtocol.universal_customization_partition
  real_label_partition_instance


#tooth_pair Qsag.CrossProtocol.inverse_feedforward_relation vs real_poseidon_feedforward_misses
#tooth_pair Qsag.CrossProtocol.isolated_game_zero_drift vs same_label_reprogram_changes_game

end Qsag.CompositionInstances

/-! ## Evaluated `Composed` fixtures (moved from `ComposedQsAgAndMergeSecurity`) -/
namespace Qsag.Composed
set_option autoImplicit false

theorem headD_mem_of_ne_nil {α : Type} (l : List α) (d : α) (h : l ≠ []) : l.headD d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.mem_cons_self


-- `composed_advantage_bound` / `inhabited_union` is certified in `ComposedQsAgAndMergeSecurity`, which owns both.
#tooth_pair composed_advantage_bound vs tooth_omit_outer


end Qsag.Composed
end
