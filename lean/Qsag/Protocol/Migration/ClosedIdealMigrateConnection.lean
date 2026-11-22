module
public import Qsag.Protocol.Migration.ZkHemV2Migration
public import Qsag.Protocol.Aggregation.ZkHemV2ComposedZkAndCerts
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ZkHemV2Migration
set_option autoImplicit false
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
def extractMigrationWitnessFromR1cs (shape : R1csShape) (pub priv : List Goldilocks)
    (indices : List Nat) (claim : Spec.MigrationClaim LegacyCredential) :
    Option ExtractedR1csMigrationWitness := do
  let raw ← decodeScalarBits (r1csAssignment pub priv) indices
  let c := claim.legacyPk
  let s := projectedScalar c.curve raw
  if r1csSatisfied shape pub priv && decide (0 < s ∧ s < c.curve.cert.scalarOrd) &&
      c.curve.cert.publicKeyMatches s c.pubKeyCoordX c.pubKeyCoordY then
    some ⟨s,priv,claim.pqDestinationPk⟩
  else none

theorem extracted_ownsKey (sh : MigrationCurveKind → R1csShape)
    (pub : Spec.MigrationClaim LegacyCredential → List Goldilocks)
    (nf : LegacyCredential → Spec.Digest256) (claim : Spec.MigrationClaim LegacyCredential)
    (priv : List Goldilocks) (indices : List Nat) (w : ExtractedR1csMigrationWitness)
    (h : extractMigrationWitnessFromR1cs (sh claim.legacyPk.curve) (pub claim) priv indices claim =
      some w) : (realCurveR1csScheme sh pub nf).ownsKey claim.legacyPk w claim := by
  unfold extractMigrationWitnessFromR1cs at h
  cases he : decodeScalarBits (r1csAssignment (pub claim) priv) indices with
  | none => simp [he] at h
  | some s =>
    simp only [he] at h
    dsimp only [Bind.bind, Option.bind] at h
    split at h
    · rename_i ok
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
      apply (realCurveR1csScheme_ownsKey_iff ..).mpr
      exact ⟨ok.1.2.1, ok.1.2.2, ok.2, rfl, ok.1.1⟩
    · cases h

/-- Reject a claim tagged for a different curve before decoding its wires. -/
def extractForStatementKind (kind : StatementKind) (shape : R1csShape)
    (pub priv : List Goldilocks) (indices : List Nat) (claim : Spec.MigrationClaim LegacyCredential) :=
  if claim.legacyPk.curve = kind.keyCurve then
    extractMigrationWitnessFromR1cs shape pub priv indices claim
  else none

theorem kind_projection_owns_key (kind : StatementKind) (sh : MigrationCurveKind → R1csShape)
    (pub : Spec.MigrationClaim LegacyCredential → List Goldilocks) (nf : LegacyCredential → Spec.Digest256)
    (claim : Spec.MigrationClaim LegacyCredential) (priv : List Goldilocks) (indices : List Nat)
    (w : ExtractedR1csMigrationWitness) (h : extractForStatementKind kind (sh claim.legacyPk.curve)
      (pub claim) priv indices claim = some w) :
    claim.legacyPk.curve = kind.keyCurve ∧ (realCurveR1csScheme sh pub nf).ownsKey claim.legacyPk w claim := by
  unfold extractForStatementKind at h
  split at h
  · exact ⟨by assumption,extracted_ownsKey sh pub nf claim priv indices w h⟩
  · cases h

/-- The checked projection succeeds on every certified generator. The bit
    circuit has a real private wire, and the public point check is executed. -/
theorem bit_projection_generator (k : MigrationCurveKind) :
    let sh : R1csShape := ⟨16,0,1,[r1csBitRow 1]⟩
    let claim : Spec.MigrationClaim LegacyCredential := ⟨⟨k,0#256,k.cert.genX,k.cert.genY⟩,0#256,[]⟩
    extractMigrationWitnessFromR1cs sh [] [Goldilocks.one] [1] claim =
      some ⟨1,[Goldilocks.one],[]⟩ := by
  intro sh claim
  have sat : r1csSatisfied sh [] [Goldilocks.one] = true := by decide +kernel
  have bit : decodeScalarBits (r1csAssignment [] [Goldilocks.one]) [1] = some 1 := by decide +kernel
  simp [extractMigrationWitnessFromR1cs,claim,bit,projectedScalar_one,sat,
    k.cert.generator_matches,show 1 < k.cert.scalarOrd from k.cert.scalarOrd_prime.1]

/-- This machine uses the assignment available to a checked decoder. Its visible
    step is the existing settlement step. A failed decode cannot mint a receipt. -/
def checkedAssignment_refines_idealMigrate {D : Type}
    (sh : MigrationCurveKind → R1csShape)
    (pub : Spec.MigrationClaim LegacyCredential → List Goldilocks)
    (nf : LegacyCredential → Spec.Digest256) (snapshot : Spec.EnrolledSnapshot LegacyCredential)
    (priv : ZkHemV2MigrationSubmission D → List Goldilocks)
    (indices : ZkHemV2MigrationSubmission D → List Nat) :
    let project := fun s : ZkHemV2MigrationSubmission D => extractMigrationWitnessFromR1cs
      (sh s.claim.legacyPk.curve) (pub s.claim) (priv s) (indices s) s.claim
    let witness := fun s => (project s).getD ⟨0,[],[]⟩
    Spec.DataRefines (zkHemV2MigrationMachine (fun s => (project s).isSome) nf snapshot)
      (Spec.idealMigrateMachine (realCurveR1csScheme sh pub nf) snapshot)
      (fun s => some (s.claim, witness s)) id := by
  intro project witness
  apply zkHemV2Migration_dataRefines_idealMigrate
  rw [ZkHemV2ExtractorSound.public_eq_1]
  intro s accepted
  cases he : project s with
  | none => simp [he] at accepted
  | some w =>
    have he' := extracted_ownsKey sh pub nf s.claim (priv s) (indices s) w he
    simpa only [witness, he, Option.getD_some] using he'

/-- A nonempty satisfied bit circuit can encode scalar one while the asserted
    affine point differs from the certified generator on every curve. -/
theorem tooth_bit_rows_alone_do_not_bind_pk (k : MigrationCurveKind) :
    ∃ shape : R1csShape,
    let claim : Spec.MigrationClaim LegacyCredential :=
      ⟨⟨k,0#256,(k.cert.genX + 1) % k.cert.baseP,k.cert.genY⟩,0#256,[]⟩
    r1csSatisfied shape [] [Goldilocks.one] = true ∧
      decodeScalarBits (r1csAssignment [] [Goldilocks.one]) [1] = some 1 ∧
      extractMigrationWitnessFromR1cs shape [] [Goldilocks.one] [1] claim = none := by
  let shape : R1csShape := ⟨16,0,1,[r1csBitRow 1]⟩
  refine ⟨shape, ?_⟩
  intro claim
  have hs : r1csSatisfied shape [] [Goldilocks.one] = true := by decide +kernel
  have hd : decodeScalarBits (r1csAssignment [] [Goldilocks.one]) [1] = some 1 := by decide +kernel
  exact ⟨hs, hd, by simp [extractMigrationWitnessFromR1cs, hd, claim, projectedScalar_one, k.cert.generator_rejects_changed_x]⟩

#tooth_pair extracted_ownsKey vs tooth_bit_rows_alone_do_not_bind_pk

/-- The exact seed budget obstructs a certificate that charges even one first-OOD
    transition. This specializes to each deployed migration relation size. -/
theorem first_ood_positive_charge_excludes_certificate
    (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) (env : ClosedWhir.WhirEnv QuinticGoldilocks) :
    ¬ ∃ c : ClosedWhir.WhirScheduleCert env (ZkHemV2Cert.zkHemV2ProdSched n) 400,
      0 < c.cert.bad ⟨_, (ZkHemV2Cert.deployed_first_ood_data n lo hi).1⟩ := by
  rintro ⟨c,h⟩
  rw [ZkHemV2Cert.deployed_cert_first_ood_zero n lo hi env c] at h
  exact Nat.lt_irrefl _ h
end Qsag.ZkHemV2Migration
