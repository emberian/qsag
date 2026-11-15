module
public import Qsag.HypertreeEufCma
public import Qsag.MaliciousSecurity
import Qsag.Tactic.AssuranceKit

/-! Spec-level custody approvals. This is NOT a threshold reconstruction of a signing key.
Each custodian has its own production Jorts key. The spine composes their approvals.
No public linear map is treated as a signature and no secrecy theorem is assumed.
The signer is partial: exhausted grinding burns its leaf without releasing a signature.
-/
public section
namespace Qsag.Custody
set_option autoImplicit false

structure Intent where
  session : Nat
  round : Nat
  leaf : Nat
  spend : Nat
  message : List UInt8
  deriving DecidableEq, Repr

/-- Unbounded integers use canonical LEB128, not truncating machine casts. -/
def payload (party : Nat) (r : Intent) : List UInt8 :=
  encodeMultiFrame ["QSAG.CUSTODY.APPROVAL/v2".toUTF8.toList, leb128 party,
    leb128 r.session, leb128 r.round, leb128 r.leaf, leb128 r.spend, r.message]

private theorem leb_inj {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (show leb128 a ++ [] = leb128 b ++ [] by simpa using h)).1

theorem payload_injective {i j : Nat} {r s : Intent}
    (h : payload i r = payload j s) : i = j ∧ r = s := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  obtain ⟨hi, hs, hr, hl, hv, hm⟩ :=
    ⟨leb_inj hf.2.1, leb_inj hf.2.2.1, leb_inj hf.2.2.2.1,
     leb_inj hf.2.2.2.2.1, leb_inj hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1⟩
  refine ⟨hi, ?_⟩
  cases r; cases s
  simp_all only [Intent.mk.injEq]

structure SigningConfig where
  suite : TweakableHashSuite
  params : PqHashParams
  randomness : List UInt8
  grindLimit : Nat

def query (cfg : SigningConfig) (party : Nat) (r : Intent) : ProdSigningQuery :=
  ⟨payload party r, cfg.randomness, r.leaf, cfg.grindLimit⟩

/-- The actual production specification, including its self-verification. -/
def sign (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat) (r : Intent) :
    Option PqHashSig :=
  evalProductionStatefulSign cfg.suite cfg.params sk (payload party r)
    cfg.randomness r.leaf cfg.grindLimit

def verify (cfg : SigningConfig) (pk : PqPublicKey) (party : Nat)
    (r : Intent) (sig : PqHashSig) : Bool :=
  verifyProductionPqHashSig cfg.suite cfg.params pk (payload party r) sig

theorem sign_verifies (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (r : Intent) (sig : PqHashSig) (h : sign cfg sk party r = some sig) :
    verify cfg (derivePublicKey cfg.suite cfg.params sk) party r sig = true :=
  verifyProductionPqHashSig_evalProductionStatefulSign _ _ _ _ _ _ _ _ h

theorem sign_eq_query (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (r : Intent) (hs : cfg.params.statefulJorts = true) :
    sign cfg sk party r = prodSignQuery cfg.suite cfg.params sk (query cfg party r) := by
  simp only [prodSignQuery, hs, ↓reduceIte, query, sign]

structure RoundOpening where
  session : Nat
  round : Nat
  opening : BdozPairOpening

/-- Pads are addressed by the full session/round. Independence and erasure of
these pads are implementation obligations; this type does not assert them. -/
structure RoundPolicy where
  keys : Nat → Nat → BdozVerifierKeys
  roster : List Nat
  digest : Nat → List UInt8

def checkRound (p : RoundPolicy) (r : Intent) (digest : List UInt8)
    (ops : List RoundOpening) : Bool :=
  decide (digest.length = 32 ∧ digest = p.digest r.session) &&
  decide (ops ≠ [] ∧ ops.map (fun o => o.opening.partyId) = p.roster ∧ p.roster.Nodup) &&
  ops.all (fun o => decide (o.session = r.session ∧ o.round = r.round) &&
    verifyBdozPairMac (p.keys r.session r.round) o.opening)

theorem checkRound_opening (p : RoundPolicy) (r : Intent) (digest : List UInt8)
    (ops : List RoundOpening) (o : RoundOpening) (hm : o ∈ ops)
    (h : checkRound p r digest ops = true) :
    (o.session = r.session ∧ o.round = r.round) ∧
      verifyBdozPairMac (p.keys r.session r.round) o.opening = true := by
  have ha := (Bool.and_eq_true_iff.mp h).2
  have ho := List.all_eq_true.mp ha o hm
  exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp ho).1,
    (Bool.and_eq_true_iff.mp ho).2⟩

theorem checkRound_wrong_session (p : RoundPolicy) (r : Intent) (digest : List UInt8)
    (ops : List RoundOpening) (o : RoundOpening) (hm : o ∈ ops)
    (hne : o.session ≠ r.session) : checkRound p r digest ops = false := by
  cases h : checkRound p r digest ops
  · rfl
  · exact False.elim (hne (checkRound_opening p r digest ops o hm h).1.1)

/-- A changed accepted share is tied to the existing two-lane key-recovery
reduction, not declared authentic by a caller-supplied judgement. -/
theorem checkRound_changed_share (p : RoundPolicy) (r : Intent) (digest : List UInt8)
    (ops : List RoundOpening) (o : RoundOpening) (hon : BdozPairOpening)
    (hm : o ∈ ops) (h : checkRound p r digest ops = true)
    (hslot : hon.partyId = o.opening.partyId) (hne : hon.shareX ≠ o.opening.shareX)
    (hh : verifyBdozPairMac (p.keys r.session r.round) hon = true) :
    BdozMacForgeryWitness (p.keys r.session r.round) hon o.opening :=
  ⟨hslot, hne, hh, (checkRound_opening p r digest ops o hm h).2⟩

/-- All verification keys are public. Custodian secret keys remain in separate
local states; there is no reconstructed master secret in the coordinator. -/
structure Certificate where
  party : Nat
  intent : Intent
  signature : PqHashSig

def verifyCertificate (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (expected : Intent) (c : Certificate) : Bool :=
  decide (c.intent = expected) && verify cfg (pks c.party) c.party c.intent c.signature

theorem certificate_wrong_session (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (r : Intent) (c : Certificate) (hne : c.intent.session ≠ r.session) :
    verifyCertificate cfg pks r c = false := by
  have hn : c.intent ≠ r := fun he => hne (congrArg Intent.session he)
  simp [verifyCertificate, hn]

theorem certificate_invalid_rejected (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (r : Intent) (c : Certificate)
    (h : verify cfg (pks c.party) c.party c.intent c.signature = false) :
    verifyCertificate cfg pks r c = false := by
  simp only [verifyCertificate, h, Bool.and_false]

end Qsag.Custody
end
#verify_constructive Qsag.Custody.payload_injective
#verify_constructive Qsag.Custody.sign_verifies
#verify_constructive Qsag.Custody.checkRound_changed_share
#verify_constructive Qsag.Custody.certificate_wrong_session
