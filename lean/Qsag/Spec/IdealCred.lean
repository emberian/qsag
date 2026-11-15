module
/-
# Qsag.Spec.IdealCred — Ideal Selective-Disclosure Anonymous Credential & TOPRF Specification

Layer-0 ideal specification aligned with `crates/qsag-cred/src/blind_vc.rs` (`PiBlindVc` `N = 256`
seed-tree GGM MPC-in-the-head `33`-repetition `GF(p^5)` selective-disclosure credentials and
threshold symmetric OPRF):
1. **Selective Disclosure Without Plaintext Witness Leakage**: Presentation inputs carry only a
   private ideal registry handle `credId : Nat` and a public `CredentialStatement Attr` (`issuerPk`,
   `epoch`, `accumulatorRoot`, `disclosed : List (Nat × Attr)`, `challengeNonce`). Undisclosed
   attribute values never cross the presentation statement or verifier output boundary, and
   `idealCredMachine_selective_disclosure_privacy` proves that two enrolled attribute vectors
   agreeing on `stmt.disclosed` induce identical verifier observations.
2. **Accumulator Pinning, Fresh Challenge Anti-Replay & Disclosed-Index Well-Formedness**:
   Accepting `.present credId stmt` requires matching `issuerPk` and `accumulatorRoot`, a fresh
   verifier `challengeNonce ∉ st.usedChallenges`, non-duplicate attribute indices `< maxAttrs` (`6`),
   and agreement with an enrolled credential (`idealCredMachine_presentation_sound`).
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-- Public selective-disclosure presentation statement pinned by the verifier (`blind_vc.rs`):
    contains only the disclosed `(index, value)` pairs, never the full hidden attribute vector. -/
structure CredentialStatement (Attr : Type) where
  issuerPk : Bytes
  epoch : Nat
  accumulatorRoot : Digest256
  disclosed : List (Nat × Attr)
  challengeNonce : Bytes
  deriving DecidableEq, Repr

/-- Disclosed attribute indices are strictly below `pqCredentialProfile.maxAttrs` (`6`) and duplicate-free
    (matching `InvalidDisclosedAttributeIndex` and `DuplicateDisclosedAttributeIndex` in `blind_vc.rs`). -/
@[expose] def DisclosedIndicesValid {Attr : Type} (stmt : CredentialStatement Attr) : Bool :=
  stmt.disclosed.all (fun p => decide (p.1 < pqCredentialProfile.maxAttrs)) &&
  decide (stmt.disclosed.map Prod.fst).Nodup

/-- Enrolled attribute vector `attrs` satisfies `stmt` when its length is within `maxAttrs` (`6`),
    `stmt`'s disclosed index list is valid, and every `(idx, val) ∈ stmt.disclosed` matches `attrs[idx]?`. -/
@[expose] def CredentialMatchesAttributes {Attr : Type} [DecidableEq Attr]
    (stmt : CredentialStatement Attr) (attrs : List Attr) : Bool :=
  decide (attrs.length ≤ pqCredentialProfile.maxAttrs) &&
  DisclosedIndicesValid stmt &&
  stmt.disclosed.all (fun (idx, val) => decide (attrs[idx]? = some val))

/-- Ideal credential registry tracking the pinned accumulator root, privately enrolled attribute
    vectors, consumed verifier challenge nonces, and evaluated TOPRF tags. -/
structure IdealCredState (Attr : Type) where
  issuerPk : Bytes
  accumulatorRoot : Digest256
  enrolledCredentials : List (List Attr)
  usedChallenges : List Bytes
  evaluatedOprfTags : List (Nat × Bytes)

@[expose] def IdealCredState.empty {Attr : Type} (pk : Bytes) (root₀ : Digest256) : IdealCredState Attr :=
  { issuerPk := pk
    accumulatorRoot := root₀
    enrolledCredentials := []
    usedChallenges := []
    evaluatedOprfTags := [] }

/-- Commands accepted by `IdealCred` (note `.present` takes an ideal handle `credId`, NOT plaintext attributes). -/
inductive IdealCredInput (Attr : Type) where
  | enroll (attrs : List Attr) (newAccumulatorRoot : Digest256)
  | present (credId : Nat) (stmt : CredentialStatement Attr)
  | evalToprf (epoch : Nat) (blindedTag : Bytes)

/-- Outputs emitted by `IdealCred`. -/
inductive IdealCredOutput where
  | enrolled (credId : Nat)
  | enrollmentRejected
  | presentationVerdict (ok : Bool)
  | toprfEvaluated (epoch : Nat)
  deriving DecidableEq, Repr

/-- Reactive `Machine` for `IdealCred`:
    - `.enroll` enforces `attrs.length ≤ maxAttrs` (`6`) and accumulator capacity `< 2^20`,
    - `.present credId stmt` checks `issuerPk`, `accumulatorRoot`, fresh `challengeNonce`, and
      selective-disclosure consistency against `st.enrolledCredentials[credId]?` without revealing
      any non-disclosed attribute! -/
@[expose] def idealCredMachine {Attr : Type} [DecidableEq Attr] (pk₀ : Bytes) (root₀ : Digest256) :
    Machine (IdealCredState Attr) (IdealCredInput Attr) IdealCredOutput where
  Init st := st = IdealCredState.empty pk₀ root₀
  step st inp :=
    match inp with
    | .enroll attrs newRoot =>
      if decide (attrs.length ≤ pqCredentialProfile.maxAttrs) &&
         decide (st.enrolledCredentials.length < 2 ^ pqCredentialProfile.accumulatorDepth) then
        let cid := st.enrolledCredentials.length
        some ({ st with enrolledCredentials := st.enrolledCredentials ++ [attrs]
                        accumulatorRoot := newRoot }, .enrolled cid)
      else
        some (st, .enrollmentRejected)
    | .present credId stmt =>
      match st.enrolledCredentials[credId]? with
      | none => some (st, .presentationVerdict false)
      | some attrs =>
        if decide (stmt.issuerPk = st.issuerPk) &&
           decide (stmt.accumulatorRoot = st.accumulatorRoot) &&
           decide (stmt.challengeNonce ∉ st.usedChallenges) &&
           CredentialMatchesAttributes stmt attrs then
          some ({ st with usedChallenges := stmt.challengeNonce :: st.usedChallenges },
                .presentationVerdict true)
        else
          some (st, .presentationVerdict false)
    | .evalToprf ep tag =>
      some ({ st with evaluatedOprfTags := (ep, tag) :: st.evaluatedOprfTags }, .toprfEvaluated ep)
  errStep st _ := st

/-- Ideal selective-disclosure presentation soundness: emitting `.presentationVerdict true`
    guarantees pinned `issuerPk` & `accumulatorRoot`, fresh un-replayed `challengeNonce` (now burned
    in `st'.usedChallenges`), valid non-duplicate disclosed indices `< 6`, and an enrolled attribute
    vector matching all disclosed pairs. -/
theorem idealCredMachine_presentation_sound {Attr : Type} [DecidableEq Attr]
    (pk₀ : Bytes) (root₀ : Digest256) (st st' : IdealCredState Attr)
    (credId : Nat) (stmt : CredentialStatement Attr)
    (hStep : (idealCredMachine pk₀ root₀).step st (.present credId stmt) =
      some (st', .presentationVerdict true)) :
    stmt.issuerPk = st.issuerPk ∧
    stmt.accumulatorRoot = st.accumulatorRoot ∧
    stmt.challengeNonce ∉ st.usedChallenges ∧
    stmt.challengeNonce ∈ st'.usedChallenges ∧
    DisclosedIndicesValid stmt = true ∧
    ∃ attrs, st.enrolledCredentials[credId]? = some attrs ∧
      CredentialMatchesAttributes stmt attrs = true := by
  unfold idealCredMachine at hStep
  dsimp only at hStep
  cases hLookup : st.enrolledCredentials[credId]? with
  | none =>
    simp only [hLookup] at hStep
    injection hStep with hPair
    injection hPair with _ hVer
    cases hVer
  | some attrs =>
    simp only [hLookup] at hStep
    cases hCond : (decide (stmt.issuerPk = st.issuerPk) &&
        decide (stmt.accumulatorRoot = st.accumulatorRoot) &&
        decide (stmt.challengeNonce ∉ st.usedChallenges) &&
        CredentialMatchesAttributes stmt attrs)
    · simp only [hCond, Bool.false_eq_true, ↓reduceIte] at hStep
      injection hStep with hPair
      injection hPair with _ hVer
      cases hVer
    · simp only [hCond, ↓reduceIte] at hStep
      injection hStep with hPair
      injection hPair with hSt _
      rcases Bool.and_eq_true_iff.mp hCond with ⟨hLeft3, hMatch⟩
      rcases Bool.and_eq_true_iff.mp hLeft3 with ⟨hLeft2, hFresh⟩
      rcases Bool.and_eq_true_iff.mp hLeft2 with ⟨hPk, hRoot⟩
      have hMatchUnf := hMatch
      unfold CredentialMatchesAttributes at hMatchUnf
      rcases Bool.and_eq_true_iff.mp hMatchUnf with ⟨hLenIdx, _⟩
      rcases Bool.and_eq_true_iff.mp hLenIdx with ⟨_, hIdxValid⟩
      have hInNext : stmt.challengeNonce ∈ st'.usedChallenges := by
        rw [← hSt]
        exact List.Mem.head _
      exact ⟨of_decide_eq_true hPk, of_decide_eq_true hRoot, of_decide_eq_true hFresh,
             hInNext, hIdxValid, ⟨attrs, rfl, hMatch⟩⟩

/-- **Ideal Selective-Disclosure Zero-Knowledge Privacy (`idealCredMachine_selective_disclosure_privacy`)**:
    If two ideal states `st₁, st₂` share the same public parameters (`issuerPk`, `accumulatorRoot`,
    `usedChallenges`) and their enrolled attribute vectors at `credId` have valid length `≤ 6` and
    agree on every disclosed index `idx ∈ stmt.disclosed.map Prod.fst` (differing arbitrarily on all
    undisclosed attributes!), then `.present credId stmt` produces the **exact same verifier verdict**
    in both executions! -/
theorem idealCredMachine_selective_disclosure_privacy {Attr : Type} [DecidableEq Attr]
    (pk₀ : Bytes) (root₀ : Digest256) (st₁ st₂ : IdealCredState Attr)
    (credId : Nat) (stmt : CredentialStatement Attr) (attrs₁ attrs₂ : List Attr)
    (hPk : st₁.issuerPk = st₂.issuerPk)
    (hRoot : st₁.accumulatorRoot = st₂.accumulatorRoot)
    (hUsed : st₁.usedChallenges = st₂.usedChallenges)
    (hCred₁ : st₁.enrolledCredentials[credId]? = some attrs₁)
    (hCred₂ : st₂.enrolledCredentials[credId]? = some attrs₂)
    (hLen₁ : attrs₁.length ≤ pqCredentialProfile.maxAttrs)
    (hLen₂ : attrs₂.length ≤ pqCredentialProfile.maxAttrs)
    (hAgreeDisclosed : ∀ p ∈ stmt.disclosed, attrs₁[p.1]? = attrs₂[p.1]?) :
    Prod.snd <$> (idealCredMachine pk₀ root₀).step st₁ (.present credId stmt) =
      Prod.snd <$> (idealCredMachine pk₀ root₀).step st₂ (.present credId stmt) := by
  have hAllAux : ∀ (xs : List (Nat × Attr)),
      (∀ p ∈ xs, attrs₁[p.1]? = attrs₂[p.1]?) →
      xs.all (fun (idx, val) => decide (attrs₁[idx]? = some val)) =
        xs.all (fun (idx, val) => decide (attrs₂[idx]? = some val)) := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons hd tl ih =>
      intro hSub
      have hHead := hSub hd (List.Mem.head _)
      have hTail := ih (fun p hp => hSub p (List.Mem.tail _ hp))
      simp only [List.all_cons, hHead, hTail]
  have hAllEq := hAllAux stmt.disclosed hAgreeDisclosed
  have hMatchEq :
      CredentialMatchesAttributes stmt attrs₁ = CredentialMatchesAttributes stmt attrs₂ := by
    unfold CredentialMatchesAttributes
    simp only [decide_eq_true hLen₁, decide_eq_true hLen₂, hAllEq]
  unfold idealCredMachine
  dsimp only
  simp only [hCred₁, hCred₂, hPk, hRoot, hUsed, hMatchEq]
  cases (decide (stmt.issuerPk = st₂.issuerPk) &&
      decide (stmt.accumulatorRoot = st₂.accumulatorRoot) &&
      decide (stmt.challengeNonce ∉ st₂.usedChallenges) &&
      CredentialMatchesAttributes stmt attrs₂) <;> rfl

/-- Statistical simulation / HVZK closeness record expressed directly in canonical `Spec.RatBound`. -/
structure CredHvzkBound where
  statisticalDistance : RatBound
  securityBits : Nat
  meetsBudget : statisticalDistance.atLeastBits securityBits

#verify_constructive
  Qsag.Spec.idealCredMachine_presentation_sound
  Qsag.Spec.idealCredMachine_selective_disclosure_privacy

end Qsag.Spec
end
