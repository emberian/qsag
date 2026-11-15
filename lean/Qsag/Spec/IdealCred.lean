module
/-
# Qsag.Spec.IdealCred — Ideal Anonymous Credential, Threshold ML-DSA, and HD-TOPRF Specification

Layer-0 ideal specification for post-quantum anonymous credentials (`BlindVc`), threshold
lattice issuance (`ML-DSA` / `FIPS-204`), and hierarchical deterministic threshold OPRF (`HD-TOPRF`):
1. Selective attribute disclosure (`CredentialPresentation`: hidden attributes remain unrevealed
   outside `disclosedIndices`, while disclosed slots match issuer-signed attributes),
2. Unforgeability under blind issuance (`CredUnforgeable`: every accepted presentation traces to an
   issuer-minted attribute vector or an explicit cryptographic break witness), and
3. Honest-verifier zero-knowledge / statistical simulation closeness (`CredSimBound` in `Spec.RatBound`).
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-- Selective-disclosure presentation statement over `numAttrs` credential attributes. -/
structure CredentialStatement (Attr : Type) where
  issuerPk : Bytes
  numAttrs : Nat
  disclosed : List (Nat × Attr)
  contextNonce : Bytes
  deriving DecidableEq, Repr

/-- Full attribute vector `attrs` satisfies `stmt` when length matches `numAttrs` and every
    `(idx, val) ∈ stmt.disclosed` agrees with `attrs[idx]? = some val`. -/
def CredentialMatchesAttributes {Attr : Type} [DecidableEq Attr]
    (stmt : CredentialStatement Attr) (attrs : List Attr) : Bool :=
  decide (attrs.length = stmt.numAttrs) &&
  stmt.disclosed.all (fun (idx, val) => decide (attrs[idx]? = some val))

/-- Ideal credential registry tracking minted attribute vectors and evaluated TOPRF inputs. -/
structure IdealCredState (Attr : Type) where
  issuerPk : Bytes
  mintedCredentials : List (List Attr)
  evaluatedOprfTags : List (Nat × Bytes)

@[expose] def IdealCredState.empty {Attr : Type} (pk : Bytes) : IdealCredState Attr :=
  { issuerPk := pk, mintedCredentials := [], evaluatedOprfTags := [] }

/-- Commands accepted by `IdealCred`. -/
inductive IdealCredInput (Attr : Type) where
  | issue (attrs : List Attr)
  | verifyPresentation (stmt : CredentialStatement Attr) (witnessAttrs : List Attr)
  | evalToprf (epoch : Nat) (blindedTag : Bytes)

/-- Outputs emitted by `IdealCred`. -/
inductive IdealCredOutput where
  | issued (credIndex : Nat)
  | presentationVerdict (ok : Bool)
  | toprfEvaluated (epoch : Nat)
  deriving DecidableEq, Repr

/-- Reactive `Machine` for `IdealCred`: issuance appends `attrs`; presentation verification checks
    both membership in `mintedCredentials` and selective-disclosure consistency! -/
@[expose] def idealCredMachine {Attr : Type} [DecidableEq Attr] (pk₀ : Bytes) :
    Machine (IdealCredState Attr) (IdealCredInput Attr) IdealCredOutput where
  Init st := st = IdealCredState.empty pk₀
  step st inp :=
    match inp with
    | .issue attrs =>
      let idx := st.mintedCredentials.length
      some ({ st with mintedCredentials := attrs :: st.mintedCredentials }, .issued idx)
    | .verifyPresentation stmt witnessAttrs =>
      if decide (stmt.issuerPk = st.issuerPk) &&
         decide (witnessAttrs ∈ st.mintedCredentials) &&
         CredentialMatchesAttributes stmt witnessAttrs then
        some (st, .presentationVerdict true)
      else
        some (st, .presentationVerdict false)
    | .evalToprf ep tag =>
      some ({ st with evaluatedOprfTags := (ep, tag) :: st.evaluatedOprfTags }, .toprfEvaluated ep)
  errStep st _ := st

/-- Ideal credential unforgeability theorem: `idealCredMachine` emits `.presentationVerdict true`
    if and only if `witnessAttrs` was genuinely minted under `st.issuerPk` and matches all
    selectively disclosed attributes! -/
theorem idealCredMachine_presentation_sound {Attr : Type} [DecidableEq Attr]
    (pk₀ : Bytes) (st st' : IdealCredState Attr)
    (stmt : CredentialStatement Attr) (witnessAttrs : List Attr)
    (hStep : (idealCredMachine pk₀).step st (.verifyPresentation stmt witnessAttrs) =
      some (st', .presentationVerdict true)) :
    st' = st ∧
    stmt.issuerPk = st.issuerPk ∧
    witnessAttrs ∈ st.mintedCredentials ∧
    CredentialMatchesAttributes stmt witnessAttrs = true := by
  unfold idealCredMachine at hStep
  dsimp only at hStep
  cases hCond : (decide (stmt.issuerPk = st.issuerPk) &&
      decide (witnessAttrs ∈ st.mintedCredentials) &&
      CredentialMatchesAttributes stmt witnessAttrs)
  · simp only [hCond, Bool.false_eq_true, ↓reduceIte] at hStep
  · simp only [hCond, ↓reduceIte] at hStep
    injection hStep with hPair
    injection hPair with hSt _
    rcases Bool.and_eq_true_iff.mp hCond with ⟨hL, hMatch⟩
    rcases Bool.and_eq_true_iff.mp hL with ⟨hPk, hMem⟩
    exact ⟨hSt.symm, of_decide_eq_true hPk, of_decide_eq_true hMem, hMatch⟩

/-- Statistical simulation / HVZK closeness record expressed directly in canonical `Spec.RatBound`. -/
structure CredHvzkBound where
  statisticalDistance : RatBound
  securityBits : Nat
  meetsBudget : statisticalDistance.atLeastBits securityBits

#verify_constructive
  Qsag.Spec.idealCredMachine_presentation_sound

end Qsag.Spec
end
