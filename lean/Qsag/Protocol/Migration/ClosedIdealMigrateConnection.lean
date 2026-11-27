module
public import Qsag.Protocol.Aggregation.WhirAssignmentRecovery
public import Qsag.Protocol.Aggregation.ZkHemV2PackedFiberCerts
public import Qsag.Protocol.Migration.ZkHemV2Migration
public import Qsag.Protocol.Aggregation.ZkHemV2ComposedZkAndCerts
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ZkHemV2Migration
set_option autoImplicit false
set_option exponentiation.threshold 512
open Qsag

/-- The CLI discriminants. These classify the statement, independently of whether
    its circuit materializes a discrete logarithm for the legacy credential. -/
inductive StatementKind where
  | btcHash160 | btcUncompressed | btcP2shP2wpkh | btcTaproot | ethEoa
  | blsWithdrawal | ed25519 | slip10Ed25519 | bip32Secp | bip32P2sh | bip32Taproot
  | bip32Eth | btcTaprootTree | bip32TaprootTree | bip32Ed25519
  | ironwood | orchard | sapling | zcashTransparent
  deriving DecidableEq

def StatementKind.keyCurve : StatementKind → MigrationCurveKind
  | .blsWithdrawal => .bls12_381
  | .ed25519 | .slip10Ed25519 | .bip32Ed25519 => .ed25519
  | .ironwood | .orchard => .pallasIronwood03
  | .sapling => .jubjubSapling
  | .btcHash160 | .btcUncompressed | .btcP2shP2wpkh | .btcTaproot | .ethEoa
  | .bip32Secp | .bip32P2sh | .bip32Taproot | .bip32Eth | .btcTaprootTree
  | .bip32TaprootTree | .zcashTransparent => .secp256k1

/-- Read wires in order of *scalar significance*, including bits obtained from
    derived intermediate values. Missing or non-Boolean wires fail decoding. -/
def decodeScalarBits (z : List Goldilocks) : List Nat → Option Nat
  | [] => some 0
  | i :: is => do
    let b ← z[i]?
    if b.val > 1 then none else
      return b.val + 2 * (← decodeScalarBits z is)

theorem decodeScalarBits_lt {z : List Goldilocks} {indices : List Nat} {s : Nat}
    (h : decodeScalarBits z indices = some s) : s < 2 ^ indices.length := by
  induction indices generalizing s with
  | nil => have he : 0 = s := Option.some.inj h; subst s; decide
  | cons i rest ih =>
    cases hb : z[i]? with
    | none => simp [decodeScalarBits,hb] at h
    | some b =>
      by_cases hbit : b.val > 1
      · simp [decodeScalarBits,hb,hbit] at h
      · cases ht : decodeScalarBits z rest with
        | none => simp [decodeScalarBits,hb,ht] at h
        | some t =>
          have := ih ht
          simp [decodeScalarBits,hb,hbit,ht] at h
          rw [List.length_cons, Nat.pow_succ]
          omega

/-- A compiled Booleanity row yields a present bit at the same address consumed
    by the decoder. Both presence and the field equation follow from satisfaction. -/
theorem satisfiedScalarBit {shape : R1csShape} {pub priv : List Goldilocks} {i : Nat}
    (sat : r1csSatisfied shape pub priv = true) (row : r1csBitRow i ∈ shape.rows) :
    ∃ b, (r1csAssignment pub priv)[i]? = some b ∧
      (b = CommRingOps.zero ∨ b = CommRingOps.one) := by
  simp only [r1csSatisfied, Bool.and_eq_true] at sat
  have chk := Bool.and_eq_true_iff.mp (List.all_eq_true.mp sat.2 _ row)
  have bound := of_decide_eq_true (List.all_eq_true.mp chk.1 (i, Goldilocks.one)
    (by simp [r1csBitRow]))
  have bit := r1csBitConstraint_sound pub priv i (of_decide_eq_true chk.2)
  exact ⟨_, List.getElem?_eq_getElem bound, by simpa [List.getD, bound] using bit⟩


theorem satisfying_bit_rows_decode {shape : R1csShape} {pub priv : List Goldilocks}
    (sat : r1csSatisfied shape pub priv = true) (indices : List Nat)
    (rows : ∀ i ∈ indices, r1csBitRow i ∈ shape.rows) :
    ∃ s, decodeScalarBits (r1csAssignment pub priv) indices = some s ∧ s < 2 ^ indices.length := by
  suffices h : ∃ s, decodeScalarBits (r1csAssignment pub priv) indices = some s by
    obtain ⟨s,hs⟩ := h
    exact ⟨s,hs,decodeScalarBits_lt hs⟩
  induction indices with
  | nil => exact ⟨0,rfl⟩
  | cons i rest ih =>
    obtain ⟨s,hs⟩ := ih (fun j hj => rows j (.tail _ hj))
    obtain ⟨b,hb,h01⟩ := satisfiedScalarBit sat (rows i (.head _))
    have small : ¬ b.val > 1 := by rcases h01 with rfl | rfl <;> decide
    exact ⟨b.val + 2 * s,by simp [decodeScalarBits,hb,small,hs]⟩

/-- RFC 8032 and BIP32-Ed25519 feed 256-bit multipliers to the fixed-base
    gadget. Their canonical group scalars may be smaller than those integers. -/
def projectedScalar (k : MigrationCurveKind) (raw : Nat) : Nat :=
  if k = .ed25519 then raw % k.cert.scalarOrd else raw

private theorem projectedScalar_one (k : MigrationCurveKind) : projectedScalar k 1 = 1 := by
  unfold projectedScalar
  split
  · exact Nat.mod_eq_of_lt k.cert.scalarOrd_prime.1
  · rfl

/-- Checked projection at the assignment boundary. The original private wires are
    retained so that the ideal ownership scheme checks precisely this assignment. -/
def extractMigrationWitnessFromR1cs (shape : R1csShape) (pub z : List Goldilocks)
    (indices : List Nat) (claim : Spec.MigrationClaim LegacyCredential) :
    Option ExtractedR1csMigrationWitness := do
  let priv := z.drop (pub.length + 1)
  let raw ← decodeScalarBits z indices
  let c := claim.legacyPk
  let s := projectedScalar c.curve raw
  if decide (z = r1csAssignment pub priv) && r1csSatisfied shape pub priv && decide (0 < s ∧ s < c.curve.cert.scalarOrd) &&
      c.curve.cert.publicKeyMatches s c.pubKeyCoordX c.pubKeyCoordY then
    some ⟨s,priv,claim.pqDestinationPk⟩
  else none

theorem extracted_ownsKey (sh : MigrationCurveKind → R1csShape)
    (pub : Spec.MigrationClaim LegacyCredential → List Goldilocks)
    (nf : LegacyCredential → Spec.Digest256) (claim : Spec.MigrationClaim LegacyCredential)
    (z : List Goldilocks) (indices : List Nat) (w : ExtractedR1csMigrationWitness)
    (h : extractMigrationWitnessFromR1cs (sh claim.legacyPk.curve) (pub claim) z indices claim =
      some w) : (realCurveR1csScheme sh pub nf).ownsKey claim.legacyPk w claim := by
  unfold extractMigrationWitnessFromR1cs at h
  cases he : decodeScalarBits z indices with
  | none => simp [he] at h
  | some s =>
    simp only [he] at h
    dsimp only [Bind.bind, Option.bind] at h
    split at h
    · rename_i ok
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
      apply (realCurveR1csScheme_ownsKey_iff ..).mpr
      exact ⟨ok.1.2.1, ok.1.2.2, ok.2, rfl, ok.1.1.2⟩
    · cases h

/-- Reject a claim tagged for a different curve before decoding its wires. -/
def extractForStatementKind (kind : StatementKind) (shape : R1csShape)
    (pub z : List Goldilocks) (indices : List Nat) (claim : Spec.MigrationClaim LegacyCredential) :=
  if claim.legacyPk.curve = kind.keyCurve then
    extractMigrationWitnessFromR1cs shape pub z indices claim
  else none

theorem kind_projection_owns_key (kind : StatementKind) (sh : MigrationCurveKind → R1csShape)
    (pub : Spec.MigrationClaim LegacyCredential → List Goldilocks) (nf : LegacyCredential → Spec.Digest256)
    (claim : Spec.MigrationClaim LegacyCredential) (z : List Goldilocks) (indices : List Nat)
    (w : ExtractedR1csMigrationWitness) (h : extractForStatementKind kind (sh claim.legacyPk.curve)
      (pub claim) z indices claim = some w) :
    claim.legacyPk.curve = kind.keyCurve ∧ (realCurveR1csScheme sh pub nf).ownsKey claim.legacyPk w claim := by
  unfold extractForStatementKind at h
  split at h
  · exact ⟨by assumption,extracted_ownsKey sh pub nf claim z indices w h⟩
  · cases h

/-- The checked projection succeeds on every certified generator. The bit
    circuit has a real private wire, and the public point check is executed. -/
theorem bit_projection_generator (k : MigrationCurveKind) :
    let sh : R1csShape := ⟨16,0,1,[r1csBitRow 1]⟩
    let claim : Spec.MigrationClaim LegacyCredential := ⟨⟨k,0#256,k.cert.genX,k.cert.genY⟩,0#256,[]⟩
    extractMigrationWitnessFromR1cs sh [] (r1csAssignment [] [Goldilocks.one]) [1] claim =
      some ⟨1,[Goldilocks.one],[]⟩ := by
  intro sh claim
  have sat : r1csSatisfied sh [] [Goldilocks.one] = true := by decide +kernel
  simp [extractMigrationWitnessFromR1cs,r1csAssignment,decodeScalarBits,claim,projectedScalar_one,sat,
    k.cert.generator_matches,show 1 < k.cert.scalarOrd from k.cert.scalarOrd_prime.1]

/-- Openings supplied to the extractor carry a complete strided fiber and its
    path under the public stage-zero root. The Merkle setup binds the tree nonce. -/
def recoverCommittedAssignment {Salt D : Type} [DecidableEq D]
    (shape : R1csShape) (st : ClosedWhir.WhirStage)
    (setup : BitVec 256 → ClosedFs.MerkleSetup D (ZkHemV2Cert.PackedFiber Salt st.foldK))
    (sub : ZkHemV2MigrationSubmission D)
    (openings : List (Nat × ZkHemV2Cert.PackedFiber Salt st.foldK × List D)) :
    Option (List Goldilocks) := do
  guard ((ZkHemV2Cert.zkHemV2ProdSched shape.logCells).stages.head? = some st)
  guard (1 + shape.numPublic + shape.numPriv ≤ 2^shape.logCells)
  let fibers := openings.filterMap fun (i,v,path) =>
    if ClosedFs.openingOk (setup sub.proof.treeNonce) (fun _ => st.logDomain)
        (fun _ => sub.proof.initRoot) (0,i) (v,path) then some (i,List.ofFn v.z) else none
  let cs ← WhirAssignmentRecovery.decode shape.logCells st.logDomain st.foldK fibers
  return (List.range (1 + shape.numPublic + shape.numPriv)).map (WhirAssignmentRecovery.vertex cs)

def extractCommittedMigrationWitness {Salt D : Type} [DecidableEq D]
    (shape : R1csShape) (pub : List Goldilocks) (st : ClosedWhir.WhirStage)
    (setup : BitVec 256 → ClosedFs.MerkleSetup D (ZkHemV2Cert.PackedFiber Salt st.foldK))
    (sub : ZkHemV2MigrationSubmission D) (indices : List Nat)
    (openings : List (Nat × ZkHemV2Cert.PackedFiber Salt st.foldK × List D)) :=
  (recoverCommittedAssignment shape st setup sub openings).bind fun z =>
    extractMigrationWitnessFromR1cs shape pub z indices sub.claim

theorem committed_extraction_ownsKey {Salt D : Type} [DecidableEq D]
    (sh : MigrationCurveKind → R1csShape) (pub : Spec.MigrationClaim LegacyCredential → List Goldilocks)
    (nf : LegacyCredential → Spec.Digest256) (st : ClosedWhir.WhirStage)
    (setup : BitVec 256 → ClosedFs.MerkleSetup D (ZkHemV2Cert.PackedFiber Salt st.foldK))
    (sub : ZkHemV2MigrationSubmission D) (indices : List Nat)
    (openings : List (Nat × ZkHemV2Cert.PackedFiber Salt st.foldK × List D))
    (w : ExtractedR1csMigrationWitness)
    (success : extractCommittedMigrationWitness (sh sub.claim.legacyPk.curve) (pub sub.claim)
      st setup sub indices openings = some w) :
    (realCurveR1csScheme sh pub nf).ownsKey sub.claim.legacyPk w sub.claim := by
  obtain ⟨z,_,hz⟩ := Option.bind_eq_some_iff.mp success
  exact extracted_ownsKey sh pub nf sub.claim z indices w hz

/-- A nonempty satisfied bit circuit can encode scalar one while the asserted
    affine point differs from the certified generator on every curve. -/
theorem tooth_bit_rows_alone_do_not_bind_pk (k : MigrationCurveKind) :
    ∃ shape : R1csShape,
    let claim : Spec.MigrationClaim LegacyCredential :=
      ⟨⟨k,0#256,(k.cert.genX + 1) % k.cert.baseP,k.cert.genY⟩,0#256,[]⟩
    r1csSatisfied shape [] [Goldilocks.one] = true ∧
      decodeScalarBits (r1csAssignment [] [Goldilocks.one]) [1] = some 1 ∧
      extractMigrationWitnessFromR1cs shape [] (r1csAssignment [] [Goldilocks.one]) [1] claim = none := by
  let shape : R1csShape := ⟨16,0,1,[r1csBitRow 1]⟩
  refine ⟨shape, ?_⟩
  intro claim
  have hs : r1csSatisfied shape [] [Goldilocks.one] = true := by decide +kernel
  have hd : decodeScalarBits (r1csAssignment [] [Goldilocks.one]) [1] = some 1 := by decide +kernel
  exact ⟨hs, hd, by simp [extractMigrationWitnessFromR1cs, r1csAssignment, decodeScalarBits, claim, projectedScalar_one, k.cert.generator_rejects_changed_x]⟩

#tooth_pair extracted_ownsKey vs tooth_bit_rows_alone_do_not_bind_pk

/-- On each deployed first stage there is a received word whose *actual*
    bad-seed count under the mixed-radix decoder is nonzero and below 2^-277
    of all seeds. The word is fixed before counting the seeds. -/
theorem first_ood_positive_seed_mass (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : ClosedWhir.WhirStage) (first : (ZkHemV2Cert.zkHemV2ProdSched n).stages.head? = some st)
    (shift : QuinticGoldilocks) (nz : shift ≠ CommRingOps.zero) :
    ∃ word : QuinticGoldilocks → QuinticGoldilocks,
      let ps := gsDecodeList st.degBound st.agree (ZkHemV2.fiberRoots st.logDomain shift) word
      let bad := qsum (2^400) fun i => if ZkHemV2Packed.gsListHasOodCollision ps
        (ZkHemV2Packed.decodeQuintic400 i.val) then 1 else 0
      0 < bad ∧ RatBound.lt ⟨bad,2^400,Nat.two_pow_pos _⟩ (RatBound.invPow2 277) := by
  let env := {ZkHemV2Cert.zkHemV2QuinticEnv with chalField := fun c _ => ZkHemV2Packed.decodeQuintic400 c}
  let a : Fin (2^400) := ⟨0,Nat.two_pow_pos _⟩
  obtain ⟨word,P,hP,Q,hQ,ne,hit⟩ := ZkHemV2Cert.deployed_first_ood_list_collision n lo hi
    st first shift nz env a
  refine ⟨word,?_⟩
  intro ps bad
  have yes : ZkHemV2Packed.gsListHasOodCollision ps (ZkHemV2Packed.decodeQuintic400 a.val) = true :=
    ZkHemV2Packed.gsListHasOodCollision_of_pair ps P Q hP hQ ne _ (hit 0)
  have mem : st ∈ (ZkHemV2Packed.packedProdSched n).stages := by
    rw [ZkHemV2Packed.packedProdSched, ZkHemV2Packed.packedProdStages_eq n lo hi]
    rw [ZkHemV2Cert.zkHemV2ProdSched.public_eqs] at first
    change st ∈ ZkHemV2Cert.zkHemV2ProdStages n
    change (ZkHemV2Cert.zkHemV2ProdStages n).head? = some st at first
    cases h : ZkHemV2Cert.zkHemV2ProdStages n with
    | nil => simp [h] at first
    | cons head tail =>
      have eq : head = st := Option.some.inj (by simpa only [h, List.head?_cons] using first)
      exact eq ▸ List.mem_cons_self
  obtain ⟨_,_,bound,lt⟩ := ZkHemV2Packed.deployed_single_ood_gs_bad_lt_277 n lo hi st mem shift nz word
  constructor
  · calc
      1 = qsum (2^400) (fun i => if i = a then 1 else 0) := (qsum_eq_indicator _ _).symm
      _ ≤ bad := by
        apply qsum_le_qsum
        intro i
        by_cases eq : i = a
        · subst i; simp [yes]
        · simp [eq]
  · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2^277) bound) lt

/-- A 64-bit challenge admits a first-stage decode-list pair that collides on all
    five derived points with probability at least 2^-64. -/
theorem undersized_digest_ood_collision (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (st : ClosedWhir.WhirStage) (first : (ZkHemV2Cert.zkHemV2ProdSched n).stages.head? = some st)
    (shift : QuinticGoldilocks) (nz : shift ≠ CommRingOps.zero)
    (env : ClosedWhir.WhirEnv QuinticGoldilocks) :
    ∃ word : QuinticGoldilocks → QuinticGoldilocks, ∃ P ∈ gsDecodeList st.degBound st.agree (ZkHemV2.fiberRoots st.logDomain shift) word,
      ∃ Q ∈ gsDecodeList st.degBound st.agree (ZkHemV2.fiberRoots st.logDomain shift) word, P ≠ Q ∧
        RatBound.le (RatBound.invPow2 64) ⟨qsum (2^64) (fun i =>
          if (List.finRange 5).all (fun j => decide (RoundPoly.evalCoeffs P.coeffs
            (env.chalField i.val j.val) = RoundPoly.evalCoeffs Q.coeffs (env.chalField i.val j.val)))
          then 1 else 0), 2^64, Nat.two_pow_pos _⟩ := by
  obtain ⟨w,P,hP,Q,hQ,ne,hit⟩ := ZkHemV2Cert.deployed_first_ood_list_collision n lo hi st first
    shift nz env ⟨0,Nat.two_pow_pos _⟩
  refine ⟨w,P,hP,Q,hQ,ne,?_⟩
  let bad (i : Fin (2^64)) := (List.finRange 5).all (fun j => decide
    (RoundPoly.evalCoeffs P.coeffs (env.chalField i.val j.val) =
      RoundPoly.evalCoeffs Q.coeffs (env.chalField i.val j.val)))
  let a : Fin (2^64) := ⟨0,Nat.two_pow_pos _⟩
  have yes : bad a = true := List.all_eq_true.mpr (fun j _ => decide_eq_true (hit j))
  change 1 * 2^64 ≤ qsum (2^64) (fun i => if bad i then 1 else 0) * 2^64
  apply Nat.mul_le_mul_right
  calc
    1 = qsum (2^64) (fun i => if i = a then 1 else 0) := (qsum_eq_indicator _ _).symm
    _ ≤ _ := by
      apply qsum_le_qsum
      intro i
      by_cases eq : i = a
      · subst i; simp [yes]
      · simp [eq]

#tooth_pair first_ood_positive_seed_mass vs undersized_digest_ood_collision
#verify_constructive committed_extraction_ownsKey
end Qsag.ZkHemV2Migration
