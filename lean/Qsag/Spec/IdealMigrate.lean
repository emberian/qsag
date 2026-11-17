module
/-
# Qsag.Spec.IdealMigrate — Ideal Post-Quantum Ownership Migration Specification

Layer-0 ideal specification for migrating legacy elliptic-curve accounts (`secp256k1`, `Pallas`,
`BLS12-381`) to post-quantum custody keys.

The functionality is parameterized by
* an enrolled snapshot (`EnrolledSnapshot`): the leaves `(legacyPk, entitlement)` of the committed
  snapshot tree, with `EnrolledEntitlement snapshot pk amount` the membership-and-amount relation;
* a `LegacyOwnershipScheme`: the cryptographic ownership relation
  `ownsKey : LegacyPk → Witness → MigrationClaim LegacyPk → Prop`, a Boolean checker deciding it
  (`check_iff`), and the deterministic 256-bit nullifier derivation `deriveNullifier`.
  Global injectivity of `deriveNullifier` is NOT assumed in `LegacyOwnershipScheme` (for
  `BLS12-381` with `p ≈ 2^381 > 2^256` global injectivity into `Digest256` is false by Pigeonhole,
  and for 256-bit curves under Poseidon2 or SHAKE256 it is collision-resistant rather than globally
  injective): all safety invariants hold unconditionally, while non-blocking liveness and lockstep
  equivalence with the key-indexed reference `idealKeyMigrateMachine` hold up to an explicit
  `NullifierCollision` (or under finite-snapshot `NullifierInjOn`).

`idealMigrateMachine` receives a claim together with the ownership witness itself and mints exactly
when `ValidLegacyOwnership` holds (the key is enrolled, the nullifier is the derived one, the witness
satisfies `ownsKey` for this claim) and the nullifier is unspent. The minted amount is the enrolled
entitlement of the key; a claim carries no amount.

Scope of the ownership guarantee. Every statement below is relative to the parameter `ownsKey`:
the machine guarantees that an accepted claim carries a witness satisfying `ownsKey`, and nothing
about what `ownsKey` means. `LegacyOwnershipScheme` states no law on `ownsKey`. For a scheme whose
`ownsKey` always holds, every enrolled key is claimable by any caller with any witness, exactly
once (`idealMigrateMachine_trivial_ownsKey_admits_any_witness`,
`tooth_idealMigrateOpen_any_witness_claims_enrolled_key`); enrollment, the derived nullifier,
single use per key and conservation still hold for that scheme.

Parties and corruption scope. The functionality has one interface, used by every caller including
the adversary: submit `(claim, witness)`. There are no party identities, no registrar interface
(the snapshot is fixed before the first step) and no corruption transition. A compromised legacy
key is a caller who can supply a witness satisfying `ownsKey` for that key: such a caller is
indistinguishable from the owner and can migrate the entitlement to a destination of its choice,
once; the functionality gives the original owner no recourse and no priority. A caller without
such a witness cannot move the entitlement of that key, cannot spend its nullifier and cannot
prevent its owner from claiming (`idealMigrateMachine_unclaimed_owner_accepts`). The destination is
bound only through the input: the receipt carries the destination of the claim that was submitted
together with the witness, and `ownsKey` receives the whole claim, so a scheme may make the witness
destination-specific.

Results:
1. `idealMigrateMachine_step_eq_some_iff`: exact characterization of acceptance.
2. `idealMigrateMachine_trace_ownership_sound`: every accepted claim of a valid trace satisfies
   `ValidLegacyOwnership` with the minted amount.
3. `idealMigrateMachine_trace_no_double_claim`: the legacy keys accepted along a valid trace are
   pairwise distinct.
4. `idealMigrateMachine_trace_minted_le_enrolled`: the amounts minted along an initialized trace sum
   to at most the total enrolled entitlement.
5. `idealMigrateMachine_unclaimed_owner_accepts_or_collision` and
   `idealMigrateMachine_unclaimed_owner_accepts`: an enrolled key that has not been settled is
   either accepted in every reachable state or exhibits an explicit `NullifierCollision` with a
   settled enrolled key (and is accepted unconditionally under `NullifierInjOn`).
6. `idealKeyMigrateMachine`, `idealMigrate_dataRefines_idealKeyMigrate`, and
   `idealMigrate_step_eq_idealKeyMigrate_or_collision`: pure key-indexed ideal reference where
   distinct keys never block each other, refined unconditionally by `idealMigrateMachine` and
   lockstep-equivalent up to `NullifierCollision`.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## 1. Enrolled Snapshot and Entitlements -/

/-- Leaves `(legacyPk, entitlement)` of the enrolled snapshot tree. -/
abbrev EnrolledSnapshot (LegacyPk : Type) : Type := List (LegacyPk × Nat)

/-- Entitlement recorded for `pk` by the first leaf of the snapshot carrying that key. -/
@[expose] def EnrolledSnapshot.entitlement {LegacyPk : Type} [DecidableEq LegacyPk] :
    EnrolledSnapshot LegacyPk → LegacyPk → Option Nat
  | [], _ => none
  | (k, amount) :: rest, pk =>
    if pk = k then some amount else EnrolledSnapshot.entitlement rest pk

/-- Sum of the entitlements of all snapshot leaves. -/
@[expose] def EnrolledSnapshot.total {LegacyPk : Type} : EnrolledSnapshot LegacyPk → Nat
  | [] => 0
  | (_, amount) :: rest => amount + EnrolledSnapshot.total rest

/-- `pk` is enrolled in `snapshot` with entitlement `amount`. -/
@[expose] def EnrolledEntitlement {LegacyPk : Type} [DecidableEq LegacyPk]
    (snapshot : EnrolledSnapshot LegacyPk) (pk : LegacyPk) (amount : Nat) : Prop :=
  EnrolledSnapshot.entitlement snapshot pk = some amount

private theorem entitlement_cons_eq {LegacyPk : Type} [DecidableEq LegacyPk]
    (k : LegacyPk) (a : Nat) (rest : EnrolledSnapshot LegacyPk) :
    EnrolledSnapshot.entitlement ((k, a) :: rest) k = some a := by
  simp only [EnrolledSnapshot.entitlement, ↓reduceIte]

private theorem entitlement_cons_ne {LegacyPk : Type} [DecidableEq LegacyPk]
    {pk k : LegacyPk} (h : ¬ pk = k) (a : Nat) (rest : EnrolledSnapshot LegacyPk) :
    EnrolledSnapshot.entitlement ((k, a) :: rest) pk =
      EnrolledSnapshot.entitlement rest pk := by
  simp only [EnrolledSnapshot.entitlement, h, ↓reduceIte]

/-- An enrolled entitlement is a leaf of the snapshot. -/
theorem EnrolledEntitlement.mem {LegacyPk : Type} [DecidableEq LegacyPk]
    {snapshot : EnrolledSnapshot LegacyPk} {pk : LegacyPk} {amount : Nat}
    (h : EnrolledEntitlement snapshot pk amount) : (pk, amount) ∈ snapshot := by
  induction snapshot with
  | nil => exact nomatch (show (none : Option Nat) = some amount from h)
  | cons e rest ih =>
    obtain ⟨k, a⟩ := e
    by_cases hk : pk = k
    · subst hk
      have hEq : some a = some amount := (entitlement_cons_eq pk a rest).symm.trans h
      injection hEq with hEq
      subst hEq
      exact .head _
    · exact .tail _ (ih ((entitlement_cons_ne hk a rest).symm.trans h))

/-- Snapshot with the first leaf of key `k` removed. -/
private def removeEnrolled {LegacyPk : Type} [DecidableEq LegacyPk] (k : LegacyPk) :
    EnrolledSnapshot LegacyPk → EnrolledSnapshot LegacyPk
  | [] => []
  | (k', a) :: rest => if k = k' then rest else (k', a) :: removeEnrolled k rest

private theorem total_removeEnrolled {LegacyPk : Type} [DecidableEq LegacyPk]
    (k : LegacyPk) (amount : Nat) :
    ∀ (snapshot : EnrolledSnapshot LegacyPk),
      EnrolledSnapshot.entitlement snapshot k = some amount →
      EnrolledSnapshot.total snapshot =
        amount + EnrolledSnapshot.total (removeEnrolled k snapshot)
  | [], h => nomatch (show (none : Option Nat) = some amount from h)
  | (k', a) :: rest, h => by
    by_cases hk : k = k'
    · subst hk
      have hEq : some a = some amount := (entitlement_cons_eq k a rest).symm.trans h
      injection hEq with hEq
      subst hEq
      simp only [removeEnrolled, ↓reduceIte, EnrolledSnapshot.total]
    · have ih := total_removeEnrolled k amount rest
        ((entitlement_cons_ne hk a rest).symm.trans h)
      simp only [removeEnrolled, hk, ↓reduceIte, EnrolledSnapshot.total]
      rw [ih]
      exact Nat.add_left_comm a amount _

private theorem entitlement_removeEnrolled_ne {LegacyPk : Type} [DecidableEq LegacyPk]
    {k pk : LegacyPk} (hNe : ¬ pk = k) :
    ∀ (snapshot : EnrolledSnapshot LegacyPk),
      EnrolledSnapshot.entitlement (removeEnrolled k snapshot) pk =
        EnrolledSnapshot.entitlement snapshot pk
  | [] => by rfl
  | (k', a) :: rest => by
    by_cases hk : k = k'
    · subst hk
      simp only [removeEnrolled, ↓reduceIte]
      exact (entitlement_cons_ne hNe a rest).symm
    · simp only [removeEnrolled, hk, ↓reduceIte]
      by_cases hp : pk = k'
      · subst hp
        rw [entitlement_cons_eq, entitlement_cons_eq]
      · rw [entitlement_cons_ne hp, entitlement_cons_ne hp]
        exact entitlement_removeEnrolled_ne hNe rest

/-! ## 2. Claims, Receipts and the Ownership Scheme -/

/-- Public migration claim: the legacy key whose entitlement is claimed, its nullifier, and the
    post-quantum destination key. The claim carries no amount. -/
structure MigrationClaim (LegacyPk : Type) where
  legacyPk : LegacyPk
  nullifier : Digest256
  pqDestinationPk : Bytes
  deriving DecidableEq, Repr

/-- Settlement receipt: the accepted claim and the amount minted for it. -/
structure MigrationReceipt (LegacyPk : Type) where
  claim : MigrationClaim LegacyPk
  amount : Nat
  deriving DecidableEq, Repr

/-- Sum of the amounts of a list of receipts. -/
@[expose] def MigrationReceipt.totalAmount {LegacyPk : Type} :
    List (MigrationReceipt LegacyPk) → Nat
  | [] => 0
  | r :: rest => r.amount + MigrationReceipt.totalAmount rest

/-- Cryptographic parameters of the ideal migration functionality: the legacy-key ownership
    relation over the whole claim, a Boolean checker deciding it, and the deterministic 256-bit
    nullifier derivation `deriveNullifier` (with NO global injectivity assumption). -/
structure LegacyOwnershipScheme (LegacyPk Witness : Type) where
  ownsKey : LegacyPk → Witness → MigrationClaim LegacyPk → Prop
  checkOwnership : LegacyPk → Witness → MigrationClaim LegacyPk → Bool
  check_iff : ∀ (pk : LegacyPk) (wit : Witness) (claim : MigrationClaim LegacyPk),
    checkOwnership pk wit claim = true ↔ ownsKey pk wit claim
  deriveNullifier : LegacyPk → Digest256

/-- Explicit distinct-key 256-bit nullifier collision under `deriveNullifier`. -/
@[expose] def NullifierCollision {LegacyPk : Type}
    (deriveNullifier : LegacyPk → Digest256) (pk₁ pk₂ : LegacyPk) : Prop :=
  pk₁ ≠ pk₂ ∧ deriveNullifier pk₁ = deriveNullifier pk₂

/-- Injectivity of `deriveNullifier` restricted to a finite list of keys `keys`
    (such as `snapshot.map Prod.fst`). -/
def NullifierInjOn {LegacyPk : Type}
    (deriveNullifier : LegacyPk → Digest256) (keys : List LegacyPk) : Prop :=
  ∀ ⦃pk₁ pk₂ : LegacyPk⦄, pk₁ ∈ keys → pk₂ ∈ keys →
    deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂

theorem NullifierInjOn_iff {LegacyPk : Type}
    (deriveNullifier : LegacyPk → Digest256) (keys : List LegacyPk) :
    NullifierInjOn deriveNullifier keys ↔
      ∀ ⦃pk₁ pk₂ : LegacyPk⦄, pk₁ ∈ keys → pk₂ ∈ keys →
        deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂ :=
  Iff.rfl

/-- Global injectivity of `deriveNullifier` across the key carrier `LegacyPk` (achievable when
    `|LegacyPk| ≤ 2^256`, e.g., `CanonicalSwPk Weierstrass.secp7Mod43`). -/
def NullifierInjective {LegacyPk : Type}
    (deriveNullifier : LegacyPk → Digest256) : Prop :=
  ∀ ⦃pk₁ pk₂ : LegacyPk⦄, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂

theorem NullifierInjective_iff {LegacyPk : Type}
    (deriveNullifier : LegacyPk → Digest256) :
    NullifierInjective deriveNullifier ↔
      ∀ ⦃pk₁ pk₂ : LegacyPk⦄, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂ :=
  Iff.rfl

theorem NullifierInjective.injOn {LegacyPk : Type}
    {deriveNullifier : LegacyPk → Digest256}
    (hInj : NullifierInjective deriveNullifier) (keys : List LegacyPk) :
    NullifierInjOn deriveNullifier keys :=
  fun _ _ _ _ hEq => hInj hEq

/-- Genuine legacy ownership of an enrolled entitlement: `claim.legacyPk` is enrolled with
    entitlement `amount`, `claim.nullifier` is the nullifier derived from that key, and `wit`
    satisfies the ownership relation for the key and this claim. -/
@[expose] def ValidLegacyOwnership {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (claim : MigrationClaim LegacyPk) (wit : Witness) (amount : Nat) : Prop :=
  EnrolledEntitlement snapshot claim.legacyPk amount ∧
  claim.nullifier = scheme.deriveNullifier claim.legacyPk ∧
  scheme.ownsKey claim.legacyPk wit claim

/-- Acceptance test apart from enrollment: derived nullifier, unspent nullifier, ownership. -/
@[expose] def LegacyOwnershipScheme.accepts {LegacyPk Witness : Type}
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (spent : List Digest256)
    (claim : MigrationClaim LegacyPk) (wit : Witness) : Bool :=
  decide (claim.nullifier = scheme.deriveNullifier claim.legacyPk) &&
    !decide (claim.nullifier ∈ spent) &&
    scheme.checkOwnership claim.legacyPk wit claim

theorem LegacyOwnershipScheme.accepts_iff {LegacyPk Witness : Type}
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (spent : List Digest256)
    (claim : MigrationClaim LegacyPk) (wit : Witness) :
    scheme.accepts spent claim wit = true ↔
      claim.nullifier = scheme.deriveNullifier claim.legacyPk ∧
      claim.nullifier ∉ spent ∧
      scheme.ownsKey claim.legacyPk wit claim := by
  unfold LegacyOwnershipScheme.accepts
  constructor
  · intro h
    have h1 := Bool.and_eq_true_iff.mp h
    have h2 := Bool.and_eq_true_iff.mp h1.1
    refine ⟨of_decide_eq_true h2.1, ?_, (scheme.check_iff _ _ _).mp h1.2⟩
    intro hMem
    have hDec : decide (claim.nullifier ∈ spent) = true := decide_eq_true hMem
    have hNot := h2.2
    rw [hDec] at hNot
    exact absurd hNot (by decide)
  · intro h
    obtain ⟨hNull, hFresh, hOwn⟩ := h
    refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hNull, ?_⟩,
      (scheme.check_iff _ _ _).mpr hOwn⟩
    rw [decide_eq_false hFresh]
    rfl

/-! ## 3. The Ideal Machine -/

/-- Persistent state of the ideal post-quantum migration registry. -/
structure IdealMigrateState (LegacyPk : Type) where
  totalMigrated : Nat
  spentNullifiers : List Digest256
  settledClaims : List (MigrationReceipt LegacyPk)

@[expose] def IdealMigrateState.init {LegacyPk : Type} : IdealMigrateState LegacyPk :=
  { totalMigrated := 0
    spentNullifiers := []
    settledClaims := [] }

/-- Settlement of `claim` given the snapshot lookup of its key and the acceptance verdict: mint the
    looked-up entitlement, spend the nullifier, record the receipt. -/
@[expose] def idealMigrateSettle {LegacyPk : Type}
    (st : IdealMigrateState LegacyPk) (claim : MigrationClaim LegacyPk) :
    Option Nat → Bool → Option (IdealMigrateState LegacyPk × MigrationReceipt LegacyPk)
  | some amount, true =>
    some ({ totalMigrated := st.totalMigrated + amount
            spentNullifiers := claim.nullifier :: st.spentNullifiers
            settledClaims := { claim := claim, amount := amount } :: st.settledClaims },
          { claim := claim, amount := amount })
  | some _, false => none
  | none, _ => none

/-- Reactive `Machine` for `IdealMigrate`. The input is a claim together with its ownership
    witness. It is accepted iff the claimed key is enrolled in `snapshot`, the nullifier equals
    `scheme.deriveNullifier claim.legacyPk` and is unspent, and the witness satisfies the ownership
    relation; the receipt mints the enrolled entitlement of the key. -/
@[expose] def idealMigrateMachine {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk) :
    Machine (IdealMigrateState LegacyPk) (MigrationClaim LegacyPk × Witness)
      (MigrationReceipt LegacyPk) where
  Init st := st = IdealMigrateState.init
  step st inp :=
    idealMigrateSettle st inp.1 (EnrolledSnapshot.entitlement snapshot inp.1.legacyPk)
      (scheme.accepts st.spentNullifiers inp.1 inp.2)
  errStep st _ := st

/-- Exact acceptance characterization: a step succeeds iff the claim has `ValidLegacyOwnership`
    for the minted amount and an unspent nullifier, and then the receipt and successor state are
    determined. -/
theorem idealMigrateMachine_step_eq_some_iff {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (st st' : IdealMigrateState LegacyPk) (claim : MigrationClaim LegacyPk) (wit : Witness)
    (out : MigrationReceipt LegacyPk) :
    (idealMigrateMachine scheme snapshot).step st (claim, wit) = some (st', out) ↔
      ValidLegacyOwnership scheme snapshot claim wit out.amount ∧
      claim.nullifier ∉ st.spentNullifiers ∧
      out.claim = claim ∧
      st' = { totalMigrated := st.totalMigrated + out.amount
              spentNullifiers := claim.nullifier :: st.spentNullifiers
              settledClaims := out :: st.settledClaims } := by
  constructor
  · intro h
    have h0 : idealMigrateSettle st claim (EnrolledSnapshot.entitlement snapshot claim.legacyPk)
        (scheme.accepts st.spentNullifiers claim wit) = some (st', out) := h
    cases hE : EnrolledSnapshot.entitlement snapshot claim.legacyPk with
    | none =>
      rw [hE] at h0
      exact nomatch (show (none : Option (IdealMigrateState LegacyPk ×
        MigrationReceipt LegacyPk)) = some (st', out) from h0)
    | some amount =>
      rw [hE] at h0
      cases hA : scheme.accepts st.spentNullifiers claim wit with
      | false =>
        rw [hA] at h0
        exact nomatch (show (none : Option (IdealMigrateState LegacyPk ×
          MigrationReceipt LegacyPk)) = some (st', out) from h0)
      | true =>
        rw [hA] at h0
        have h1 : some (({ totalMigrated := st.totalMigrated + amount
                           spentNullifiers := claim.nullifier :: st.spentNullifiers
                           settledClaims := { claim := claim, amount := amount } ::
                             st.settledClaims } : IdealMigrateState LegacyPk),
                        ({ claim := claim, amount := amount } : MigrationReceipt LegacyPk)) =
            some (st', out) := h0
        injection h1 with h1
        injection h1 with hSt hOut
        subst hSt
        subst hOut
        obtain ⟨hNull, hFresh, hOwn⟩ := (scheme.accepts_iff _ _ _).mp hA
        exact ⟨⟨hE, hNull, hOwn⟩, hFresh, rfl, rfl⟩
  · intro h
    obtain ⟨hValid, hFresh, hClaim, hSt⟩ := h
    obtain ⟨hEnt, hNull, hOwn⟩ := hValid
    obtain ⟨outClaim, outAmount⟩ := out
    have hClaim' : outClaim = claim := hClaim
    subst hClaim'
    have hA : scheme.accepts st.spentNullifiers outClaim wit = true :=
      (scheme.accepts_iff _ _ _).mpr ⟨hNull, hFresh, hOwn⟩
    have hE : EnrolledSnapshot.entitlement snapshot outClaim.legacyPk = some outAmount := hEnt
    show idealMigrateSettle st outClaim
        (EnrolledSnapshot.entitlement snapshot outClaim.legacyPk)
        (scheme.accepts st.spentNullifiers outClaim wit) = _
    rw [hE, hA, hSt]
    rfl

/-! ## 4. State Invariant -/

/-- Core invariant of `IdealMigrateState`: the spent nullifiers are exactly the nullifiers derived
    from the settled legacy keys and are pairwise distinct; every settled receipt mints the enrolled
    entitlement of its key under the derived nullifier; `totalMigrated` is the sum of the settled
    amounts. -/
@[expose] def IdealMigrateState.Inv {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (st : IdealMigrateState LegacyPk) : Prop :=
  st.spentNullifiers =
    (st.settledClaims.map (fun r => r.claim.legacyPk)).map scheme.deriveNullifier ∧
  st.spentNullifiers.Nodup ∧
  (∀ r ∈ st.settledClaims,
    EnrolledEntitlement snapshot r.claim.legacyPk r.amount ∧
    r.claim.nullifier = scheme.deriveNullifier r.claim.legacyPk) ∧
  st.totalMigrated = MigrationReceipt.totalAmount st.settledClaims

theorem IdealMigrateState.init_inv {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk) :
    (IdealMigrateState.init : IdealMigrateState LegacyPk).Inv scheme snapshot := by
  refine ⟨rfl, .nil, ?_, rfl⟩
  intro r hr
  cases hr

theorem idealMigrateMachine_step_preserves_inv {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk}
    {st st' : IdealMigrateState LegacyPk} {claim : MigrationClaim LegacyPk} {wit : Witness}
    {out : MigrationReceipt LegacyPk}
    (hInv : st.Inv scheme snapshot)
    (hStep : (idealMigrateMachine scheme snapshot).step st (claim, wit) = some (st', out)) :
    st'.Inv scheme snapshot ∧
      ValidLegacyOwnership scheme snapshot claim wit out.amount ∧ out.claim = claim := by
  obtain ⟨hValid, hFresh, hClaim, hSt⟩ :=
    (idealMigrateMachine_step_eq_some_iff scheme snapshot st st' claim wit out).mp hStep
  obtain ⟨hMap, hNd, hSettled, hTotal⟩ := hInv
  obtain ⟨hEnt, hNull, hOwn⟩ := hValid
  subst hSt
  refine ⟨⟨?_, .cons (fun x hx hEq => hFresh (hEq ▸ hx)) hNd, ?_, ?_⟩,
    ⟨hEnt, hNull, hOwn⟩, hClaim⟩
  · show claim.nullifier :: st.spentNullifiers =
      scheme.deriveNullifier out.claim.legacyPk ::
        (st.settledClaims.map (fun r => r.claim.legacyPk)).map scheme.deriveNullifier
    rw [hClaim, ← hNull, ← hMap]
  · intro r hr
    cases hr with
    | head =>
      rw [hClaim]
      exact ⟨hEnt, hNull⟩
    | tail _ hr' => exact hSettled r hr'
  · show st.totalMigrated + out.amount =
      out.amount + MigrationReceipt.totalAmount st.settledClaims
    rw [hTotal, Nat.add_comm]

theorem idealMigrateMachine_trace_preserves_inv {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk} :
    ∀ {s₀ s_final : IdealMigrateState LegacyPk}
      {tr : List ((MigrationClaim LegacyPk × Witness) × MigrationReceipt LegacyPk)},
      s₀.Inv scheme snapshot →
      (idealMigrateMachine scheme snapshot).ValidTrace s₀ tr s_final →
      s_final.Inv scheme snapshot
  | _, _, _, hInv, .nil _ => hInv
  | _, _, _, hInv, .accept hStep hRest =>
    idealMigrateMachine_trace_preserves_inv
      (idealMigrateMachine_step_preserves_inv hInv hStep).1 hRest
  | _, _, _, hInv, .reject _ _ hRest =>
    idealMigrateMachine_trace_preserves_inv hInv hRest

/-- Every reachable state of `idealMigrateMachine` satisfies `IdealMigrateState.Inv`. -/
theorem idealMigrateMachine_reachable_inv {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    {st : IdealMigrateState LegacyPk}
    (hReach : (idealMigrateMachine scheme snapshot).Reachable st) :
    st.Inv scheme snapshot := by
  rcases hReach with ⟨s₀, tr, hInit, hTrace⟩
  have hInit' : s₀ = IdealMigrateState.init := hInit
  rw [hInit'] at hTrace
  exact idealMigrateMachine_trace_preserves_inv (IdealMigrateState.init_inv scheme snapshot) hTrace

private theorem nodup_of_nodup_map {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => .nil
  | a :: l, h => by
    have h' : (f a :: l.map f).Nodup := h
    cases h' with
    | cons hHead hTail =>
      exact .cons (fun b hb hEq => hHead (f b) (List.mem_map_of_mem (f := f) hb) (congrArg f hEq))
        (nodup_of_nodup_map f hTail)

/-- Under the invariant each enrolled legacy identity is settled at most once. -/
theorem IdealMigrateState.Inv.settled_legacyPk_nodup {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk}
    {st : IdealMigrateState LegacyPk} (hInv : st.Inv scheme snapshot) :
    (st.settledClaims.map (fun r => r.claim.legacyPk)).Nodup := by
  obtain ⟨hMap, hNd, _, _⟩ := hInv
  rw [hMap] at hNd
  exact nodup_of_nodup_map scheme.deriveNullifier hNd

private theorem totalAmount_le_total {LegacyPk : Type} [DecidableEq LegacyPk] :
    ∀ (settled : List (MigrationReceipt LegacyPk)) (snapshot : EnrolledSnapshot LegacyPk),
      (settled.map (fun r => r.claim.legacyPk)).Nodup →
      (∀ r ∈ settled,
        EnrolledSnapshot.entitlement snapshot r.claim.legacyPk = some r.amount) →
      MigrationReceipt.totalAmount settled ≤ EnrolledSnapshot.total snapshot
  | [], _, _, _ => Nat.zero_le _
  | r :: rest, snapshot, hNd, hEnt => by
    have hNd' : (r.claim.legacyPk :: rest.map (fun r => r.claim.legacyPk)).Nodup := hNd
    cases hNd' with
    | cons hHead hTail =>
      have hr := hEnt r (.head _)
      have hRest : ∀ r' ∈ rest,
          EnrolledSnapshot.entitlement (removeEnrolled r.claim.legacyPk snapshot)
            r'.claim.legacyPk = some r'.amount := by
        intro r' hr'
        have hNe : ¬ r'.claim.legacyPk = r.claim.legacyPk := fun hEq =>
          hHead r'.claim.legacyPk
            (List.mem_map_of_mem (f := fun r => r.claim.legacyPk) hr') hEq.symm
        rw [entitlement_removeEnrolled_ne hNe]
        exact hEnt r' (.tail _ hr')
      have ih := totalAmount_le_total rest _ hTail hRest
      rw [total_removeEnrolled _ _ snapshot hr]
      exact Nat.add_le_add_left ih _

/-- Conservation: under the invariant the migrated total is at most the total enrolled
    entitlement. -/
theorem IdealMigrateState.Inv.totalMigrated_le_enrolled {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk}
    {st : IdealMigrateState LegacyPk} (hInv : st.Inv scheme snapshot) :
    st.totalMigrated ≤ EnrolledSnapshot.total snapshot := by
  have hNd := hInv.settled_legacyPk_nodup
  obtain ⟨_, _, hSettled, hTotal⟩ := hInv
  rw [hTotal]
  exact totalAmount_le_total st.settledClaims snapshot hNd (fun r hr => (hSettled r hr).1)

/-! ## 5. Trace-Level Ownership Soundness, Non-Double-Claim and Conservation -/

/-- Ownership soundness: every accepted input of a valid trace is a claim with
    `ValidLegacyOwnership` for exactly the amount its receipt mints. -/
theorem idealMigrateMachine_trace_ownership_sound {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk) :
    ∀ {s s' : IdealMigrateState LegacyPk}
      {tr : List ((MigrationClaim LegacyPk × Witness) × MigrationReceipt LegacyPk)},
      (idealMigrateMachine scheme snapshot).ValidTrace s tr s' →
      ∀ io ∈ tr,
        ValidLegacyOwnership scheme snapshot io.1.1 io.1.2 io.2.amount ∧ io.2.claim = io.1.1
  | _, _, _, .nil _, _, hMem => nomatch hMem
  | _, _, _, .accept (inp := inp) (out := out) hStep hRest, io, hMem => by
    cases hMem with
    | head =>
      obtain ⟨hValid, _, hClaim, _⟩ :=
        (idealMigrateMachine_step_eq_some_iff scheme snapshot _ _ inp.1 inp.2 out).mp hStep
      exact ⟨hValid, hClaim⟩
    | tail _ hMem' =>
      exact idealMigrateMachine_trace_ownership_sound scheme snapshot hRest io hMem'
  | _, _, _, .reject _ _ hRest, io, hMem =>
    idealMigrateMachine_trace_ownership_sound scheme snapshot hRest io hMem

/-- A nullifier accepted along a valid trace was unspent in the starting state. -/
theorem idealMigrateMachine_trace_nullifier_fresh {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk) :
    ∀ {s s' : IdealMigrateState LegacyPk}
      {tr : List ((MigrationClaim LegacyPk × Witness) × MigrationReceipt LegacyPk)},
      (idealMigrateMachine scheme snapshot).ValidTrace s tr s' →
      ∀ io ∈ tr, io.1.1.nullifier ∉ s.spentNullifiers
  | _, _, _, .nil _, _, hMem => nomatch hMem
  | _, _, _, .accept (inp := inp) (out := out) hStep hRest, io, hMem => by
    obtain ⟨_, hFresh, _, hSt⟩ :=
      (idealMigrateMachine_step_eq_some_iff scheme snapshot _ _ inp.1 inp.2 out).mp hStep
    cases hMem with
    | head => exact hFresh
    | tail _ hMem' =>
      have h := idealMigrateMachine_trace_nullifier_fresh scheme snapshot hRest io hMem'
      rw [hSt] at h
      exact fun hIn => h (.tail _ hIn)
  | _, _, _, .reject _ _ hRest, io, hMem =>
    idealMigrateMachine_trace_nullifier_fresh scheme snapshot hRest io hMem

/-- Non-double-claim: the legacy keys accepted along any valid trace are pairwise distinct, so
    each enrolled legacy identity is migrated at most once. -/
theorem idealMigrateMachine_trace_no_double_claim {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk) :
    ∀ {s s' : IdealMigrateState LegacyPk}
      {tr : List ((MigrationClaim LegacyPk × Witness) × MigrationReceipt LegacyPk)},
      (idealMigrateMachine scheme snapshot).ValidTrace s tr s' →
      (tr.map (fun io => io.1.1.legacyPk)).Nodup
  | _, _, _, .nil _ => .nil
  | _, _, _, .accept (inp := inp) (out := out) hStep hRest => by
    obtain ⟨hValid, _, _, hSt⟩ :=
      (idealMigrateMachine_step_eq_some_iff scheme snapshot _ _ inp.1 inp.2 out).mp hStep
    obtain ⟨_, hNull, _⟩ := hValid
    refine .cons ?_ (idealMigrateMachine_trace_no_double_claim scheme snapshot hRest)
    intro pk hpk hEq
    obtain ⟨io, hio, hioPk⟩ := List.exists_of_mem_map hpk
    obtain ⟨⟨_, hioNull, _⟩, _⟩ :=
      idealMigrateMachine_trace_ownership_sound scheme snapshot hRest io hio
    have hFresh := idealMigrateMachine_trace_nullifier_fresh scheme snapshot hRest io hio
    rw [hSt] at hFresh
    have hPk : io.1.1.legacyPk = inp.1.legacyPk := hioPk.trans hEq.symm
    have hNullEq : io.1.1.nullifier = inp.1.nullifier :=
      hioNull.trans ((congrArg scheme.deriveNullifier hPk).trans hNull.symm)
    apply hFresh
    rw [hNullEq]
    exact .head _
  | _, _, _, .reject _ _ hRest =>
    idealMigrateMachine_trace_no_double_claim scheme snapshot hRest

/-- The migrated total grows by exactly the amounts minted along a valid trace. -/
theorem idealMigrateMachine_trace_totalMigrated {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk) :
    ∀ {s s' : IdealMigrateState LegacyPk}
      {tr : List ((MigrationClaim LegacyPk × Witness) × MigrationReceipt LegacyPk)},
      (idealMigrateMachine scheme snapshot).ValidTrace s tr s' →
      s'.totalMigrated = s.totalMigrated + (tr.map (fun io => io.2.amount)).sum
  | _, _, _, .nil _ => by rfl
  | _, _, _, .accept (inp := inp) (out := out) hStep hRest => by
    obtain ⟨_, _, _, hSt⟩ :=
      (idealMigrateMachine_step_eq_some_iff scheme snapshot _ _ inp.1 inp.2 out).mp hStep
    have ih := idealMigrateMachine_trace_totalMigrated scheme snapshot hRest
    rw [hSt] at ih
    rw [ih, List.map_cons, List.sum_cons]
    exact Nat.add_assoc _ _ _
  | _, _, _, .reject _ _ hRest =>
    idealMigrateMachine_trace_totalMigrated scheme snapshot hRest

/-- Conservation along initialized traces: the amounts minted sum to at most the total enrolled
    entitlement. -/
theorem idealMigrateMachine_trace_minted_le_enrolled {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    {s₀ s : IdealMigrateState LegacyPk}
    {tr : List ((MigrationClaim LegacyPk × Witness) × MigrationReceipt LegacyPk)}
    (hInit : (idealMigrateMachine scheme snapshot).Init s₀)
    (hTrace : (idealMigrateMachine scheme snapshot).ValidTrace s₀ tr s) :
    (tr.map (fun io => io.2.amount)).sum ≤ EnrolledSnapshot.total snapshot := by
  have hInv := idealMigrateMachine_reachable_inv scheme snapshot ⟨s₀, tr, hInit, hTrace⟩
  have hLe := hInv.totalMigrated_le_enrolled
  rw [idealMigrateMachine_trace_totalMigrated scheme snapshot hTrace] at hLe
  exact Nat.le_trans (Nat.le_add_left _ _) hLe

private theorem settled_pk_mem_snapshot {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk}
    {st : IdealMigrateState LegacyPk} {pk : LegacyPk}
    (hInv : st.Inv scheme snapshot)
    (hpk : pk ∈ st.settledClaims.map (fun r => r.claim.legacyPk)) :
    pk ∈ snapshot.map Prod.fst := by
  obtain ⟨r, hrMem, hrEq⟩ := List.exists_of_mem_map hpk
  have hEnt := (hInv.2.2.1 r hrMem).1
  rw [← hrEq]
  exact List.mem_map_of_mem (f := Prod.fst) (EnrolledEntitlement.mem hEnt)

/-- Collision-branching non-blocking liveness (`0` injectivity assumptions): in a state satisfying
    `Inv`, a valid claim for an unsettled enrolled key is EITHER accepted and mints its entitlement
    OR exhibits an explicit `NullifierCollision` against an already-settled enrolled key. -/
theorem idealMigrateMachine_unclaimed_owner_accepts_or_collision {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk}
    {st : IdealMigrateState LegacyPk} {claim : MigrationClaim LegacyPk} {wit : Witness}
    {amount : Nat}
    (hInv : st.Inv scheme snapshot)
    (hValid : ValidLegacyOwnership scheme snapshot claim wit amount)
    (hUnclaimed : claim.legacyPk ∉ st.settledClaims.map (fun r => r.claim.legacyPk)) :
    (idealMigrateMachine scheme snapshot).step st (claim, wit) =
      some ({ totalMigrated := st.totalMigrated + amount
              spentNullifiers := claim.nullifier :: st.spentNullifiers
              settledClaims := { claim := claim, amount := amount } :: st.settledClaims },
            { claim := claim, amount := amount }) ∨
    ∃ pk_prev ∈ st.settledClaims.map (fun r => r.claim.legacyPk),
      pk_prev ∈ snapshot.map Prod.fst ∧
      NullifierCollision scheme.deriveNullifier pk_prev claim.legacyPk := by
  cases (inferInstance : Decidable (claim.nullifier ∈ st.spentNullifiers)) with
  | isFalse hFresh =>
    exact .inl ((idealMigrateMachine_step_eq_some_iff scheme snapshot st _ claim wit _).mpr
      ⟨hValid, hFresh, rfl, rfl⟩)
  | isTrue hMem =>
    have hMap := hInv.1
    rw [hMap] at hMem
    obtain ⟨pk_prev, hpk, hEq⟩ := List.exists_of_mem_map hMem
    have hNe : pk_prev ≠ claim.legacyPk := fun hSame => hUnclaimed (hSame ▸ hpk)
    exact .inr ⟨pk_prev, hpk, settled_pk_mem_snapshot hInv hpk, hNe, hEq.trans hValid.2.1⟩

/-- No blocking by other identities under finite-snapshot `NullifierInjOn`: in a state satisfying
    `Inv`, a claim with `ValidLegacyOwnership` whose legacy key is not yet settled is accepted and
    mints its entitlement. -/
theorem idealMigrateMachine_unclaimed_owner_accepts {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk}
    {st : IdealMigrateState LegacyPk} {claim : MigrationClaim LegacyPk} {wit : Witness}
    {amount : Nat}
    (hInj : NullifierInjOn scheme.deriveNullifier (snapshot.map Prod.fst))
    (hInv : st.Inv scheme snapshot)
    (hValid : ValidLegacyOwnership scheme snapshot claim wit amount)
    (hUnclaimed : claim.legacyPk ∉ st.settledClaims.map (fun r => r.claim.legacyPk)) :
    (idealMigrateMachine scheme snapshot).step st (claim, wit) =
      some ({ totalMigrated := st.totalMigrated + amount
              spentNullifiers := claim.nullifier :: st.spentNullifiers
              settledClaims := { claim := claim, amount := amount } :: st.settledClaims },
            { claim := claim, amount := amount }) := by
  rcases idealMigrateMachine_unclaimed_owner_accepts_or_collision hInv hValid hUnclaimed with
    hStep | ⟨pk_prev, _, hSnapPrev, hNe, hNullEq⟩
  · exact hStep
  · have hSnapClaim : claim.legacyPk ∈ snapshot.map Prod.fst :=
      List.mem_map_of_mem (f := Prod.fst) (EnrolledEntitlement.mem hValid.1)
    exact absurd (hInj hSnapPrev hSnapClaim hNullEq) hNe

/-- Corollary of `idealMigrateMachine_unclaimed_owner_accepts` when `deriveNullifier` is injective
    across the key carrier `LegacyPk`. -/
theorem idealMigrateMachine_unclaimed_owner_accepts_of_injective {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk}
    {st : IdealMigrateState LegacyPk} {claim : MigrationClaim LegacyPk} {wit : Witness}
    {amount : Nat}
    (hInj : NullifierInjective scheme.deriveNullifier)
    (hInv : st.Inv scheme snapshot)
    (hValid : ValidLegacyOwnership scheme snapshot claim wit amount)
    (hUnclaimed : claim.legacyPk ∉ st.settledClaims.map (fun r => r.claim.legacyPk)) :
    (idealMigrateMachine scheme snapshot).step st (claim, wit) =
      some ({ totalMigrated := st.totalMigrated + amount
              spentNullifiers := claim.nullifier :: st.spentNullifiers
              settledClaims := { claim := claim, amount := amount } :: st.settledClaims },
            { claim := claim, amount := amount }) :=
  idealMigrateMachine_unclaimed_owner_accepts (hInj.injOn _) hInv hValid hUnclaimed

/-! ## 5b. Key-Indexed Collision-Free Reference (`idealKeyMigrateMachine`) -/

/-- Pure key-indexed acceptance test: checks `!decide (claim.legacyPk ∈ settledKeys)` rather than
    `!decide (claim.nullifier ∈ spent)`, so distinct identities `pk₁ ≠ pk₂` never interfere even if
    `deriveNullifier` collides. -/
def LegacyOwnershipScheme.keyAccepts {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (settledKeys : List LegacyPk)
    (claim : MigrationClaim LegacyPk) (wit : Witness) : Bool :=
  decide (claim.nullifier = scheme.deriveNullifier claim.legacyPk) &&
    !decide (claim.legacyPk ∈ settledKeys) &&
    scheme.checkOwnership claim.legacyPk wit claim

theorem LegacyOwnershipScheme.keyAccepts_iff {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (settledKeys : List LegacyPk)
    (claim : MigrationClaim LegacyPk) (wit : Witness) :
    scheme.keyAccepts settledKeys claim wit = true ↔
      claim.nullifier = scheme.deriveNullifier claim.legacyPk ∧
      claim.legacyPk ∉ settledKeys ∧
      scheme.ownsKey claim.legacyPk wit claim := by
  unfold LegacyOwnershipScheme.keyAccepts
  constructor
  · intro h
    have h1 := Bool.and_eq_true_iff.mp h
    have h2 := Bool.and_eq_true_iff.mp h1.1
    refine ⟨of_decide_eq_true h2.1, ?_, (scheme.check_iff _ _ _).mp h1.2⟩
    intro hMem
    have hDec : decide (claim.legacyPk ∈ settledKeys) = true := decide_eq_true hMem
    have hNot := h2.2
    rw [hDec] at hNot
    exact absurd hNot (by decide)
  · intro h
    obtain ⟨hNull, hFresh, hOwn⟩ := h
    refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hNull, ?_⟩,
      (scheme.check_iff _ _ _).mpr hOwn⟩
    rw [decide_eq_false hFresh]
    rfl

/-- Pure key-indexed ideal migration machine: distinct keys never block one another regardless of
    256-bit nullifier collisions. -/
def idealKeyMigrateMachine {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk) :
    Machine (IdealMigrateState LegacyPk) (MigrationClaim LegacyPk × Witness)
      (MigrationReceipt LegacyPk) where
  Init st := st = IdealMigrateState.init
  step st inp :=
    idealMigrateSettle st inp.1 (EnrolledSnapshot.entitlement snapshot inp.1.legacyPk)
      (scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) inp.1 inp.2)
  errStep st _ := st

theorem idealKeyMigrateMachine_init_iff {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (st : IdealMigrateState LegacyPk) :
    (idealKeyMigrateMachine scheme snapshot).Init st ↔ st = IdealMigrateState.init :=
  Iff.rfl

theorem idealKeyMigrateMachine_step_eq_some_iff {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (st st' : IdealMigrateState LegacyPk) (claim : MigrationClaim LegacyPk) (wit : Witness)
    (out : MigrationReceipt LegacyPk) :
    (idealKeyMigrateMachine scheme snapshot).step st (claim, wit) = some (st', out) ↔
      ValidLegacyOwnership scheme snapshot claim wit out.amount ∧
      claim.legacyPk ∉ st.settledClaims.map (fun r => r.claim.legacyPk) ∧
      out.claim = claim ∧
      st' = { totalMigrated := st.totalMigrated + out.amount
              spentNullifiers := claim.nullifier :: st.spentNullifiers
              settledClaims := out :: st.settledClaims } := by
  constructor
  · intro h
    have h0 : idealMigrateSettle st claim (EnrolledSnapshot.entitlement snapshot claim.legacyPk)
        (scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit) =
        some (st', out) := h
    cases hE : EnrolledSnapshot.entitlement snapshot claim.legacyPk with
    | none =>
      rw [hE] at h0
      exact nomatch (show (none : Option (IdealMigrateState LegacyPk ×
        MigrationReceipt LegacyPk)) = some (st', out) from h0)
    | some amount =>
      rw [hE] at h0
      cases hA : scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit with
      | false =>
        rw [hA] at h0
        exact nomatch (show (none : Option (IdealMigrateState LegacyPk ×
          MigrationReceipt LegacyPk)) = some (st', out) from h0)
      | true =>
        rw [hA] at h0
        injection h0 with h1
        injection h1 with hSt hOut
        subst hSt; subst hOut
        obtain ⟨hNull, hFresh, hOwn⟩ := (scheme.keyAccepts_iff _ _ _).mp hA
        exact ⟨⟨hE, hNull, hOwn⟩, hFresh, rfl, rfl⟩
  · intro h
    obtain ⟨⟨hEnt, hNull, hOwn⟩, hFresh, hClaim, hSt⟩ := h
    obtain ⟨outClaim, outAmount⟩ := out
    subst hClaim
    have hA : scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) outClaim wit = true :=
      (scheme.keyAccepts_iff _ _ _).mpr ⟨hNull, hFresh, hOwn⟩
    have hE : EnrolledSnapshot.entitlement snapshot outClaim.legacyPk = some outAmount := hEnt
    show idealMigrateSettle st outClaim
        (EnrolledSnapshot.entitlement snapshot outClaim.legacyPk)
        (scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) outClaim wit) = _
    rw [hE, hA, hSt]
    rfl

/-- Unconditional `DataRefines` from `idealMigrateMachine` into the key-indexed reference
    `idealKeyMigrateMachine` (zero hash injectivity assumptions). -/
def idealMigrate_dataRefines_idealKeyMigrate {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk) :
    DataRefines (idealMigrateMachine scheme snapshot)
      (idealKeyMigrateMachine scheme snapshot) some id where
  Rel c a := c = a ∧ c.Inv scheme snapshot
  absInit _ := IdealMigrateState.init
  init_ok {c₀} hInit := by
    have hc : c₀ = IdealMigrateState.init := hInit
    subst hc
    exact ⟨rfl, rfl, IdealMigrateState.init_inv scheme snapshot⟩
  sim_visible {c c' a inp out j} hRel hStepC hVis := by
    rcases hRel with ⟨rfl, hInv⟩
    cases hVis
    obtain ⟨hInv', _⟩ := idealMigrateMachine_step_preserves_inv hInv hStepC
    obtain ⟨hValid, hFresh, hClaim, hSt⟩ :=
      (idealMigrateMachine_step_eq_some_iff scheme snapshot c c' inp.1 inp.2 out).mp hStepC
    have hKeyFresh : inp.1.legacyPk ∉ c.settledClaims.map (fun r => r.claim.legacyPk) := by
      intro hMem
      apply hFresh
      rw [hInv.1, hValid.2.1]
      exact List.mem_map_of_mem (f := scheme.deriveNullifier) hMem
    exact ⟨c', (idealKeyMigrateMachine_step_eq_some_iff scheme snapshot c c' inp.1 inp.2 out).mpr
      ⟨hValid, hKeyFresh, hClaim, hSt⟩, rfl, hInv'⟩
  sim_internal _ _ hVis := by cases hVis
  sim_reject hRel _ := hRel

theorem idealMigrate_dataRefines_idealKeyMigrate_rel_iff {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (c a : IdealMigrateState LegacyPk) :
    (idealMigrate_dataRefines_idealKeyMigrate scheme snapshot).Rel c a ↔
      c = a ∧ c.Inv scheme snapshot :=
  Iff.rfl

/-- Stepwise lockstep agreement or explicit `NullifierCollision`: in any state satisfying `Inv`,
    `idealMigrateMachine` and `idealKeyMigrateMachine` take the EXACT same step on `(claim, wit)`
    unless `claim.legacyPk` is enrolled and collides under `deriveNullifier` with an already-settled
    enrolled key `pk_prev ≠ claim.legacyPk`. -/
theorem idealMigrate_step_eq_idealKeyMigrate_or_collision {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk}
    {st : IdealMigrateState LegacyPk} (hInv : st.Inv scheme snapshot)
    (claim : MigrationClaim LegacyPk) (wit : Witness) :
    (idealMigrateMachine scheme snapshot).step st (claim, wit) =
      (idealKeyMigrateMachine scheme snapshot).step st (claim, wit) ∨
    (claim.legacyPk ∈ snapshot.map Prod.fst ∧
      ∃ pk_prev ∈ st.settledClaims.map (fun r => r.claim.legacyPk),
        pk_prev ∈ snapshot.map Prod.fst ∧
        NullifierCollision scheme.deriveNullifier pk_prev claim.legacyPk) := by
  show idealMigrateSettle st claim (EnrolledSnapshot.entitlement snapshot claim.legacyPk)
      (scheme.accepts st.spentNullifiers claim wit) =
    idealMigrateSettle st claim (EnrolledSnapshot.entitlement snapshot claim.legacyPk)
      (scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit) ∨ _
  cases hE : EnrolledSnapshot.entitlement snapshot claim.legacyPk with
  | none =>
    left
    cases scheme.accepts st.spentNullifiers claim wit <;>
      cases scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit <;> rfl
  | some amount =>
    cases (inferInstance : Decidable (claim.nullifier = scheme.deriveNullifier claim.legacyPk)) with
    | isFalse hNull =>
      left
      have hA : scheme.accepts st.spentNullifiers claim wit = false := by
        cases hb : scheme.accepts st.spentNullifiers claim wit with
        | false => rfl
        | true => exact absurd ((scheme.accepts_iff _ _ _).mp hb).1 hNull
      have hK : scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit = false := by
        cases hb : scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit with
        | false => rfl
        | true => exact absurd ((scheme.keyAccepts_iff _ _ _).mp hb).1 hNull
      rw [hA, hK]
    | isTrue hNull =>
      cases hChk : scheme.checkOwnership claim.legacyPk wit claim with
      | false =>
        left
        have hNotOwn : ¬ scheme.ownsKey claim.legacyPk wit claim := fun ho =>
          nomatch (hChk.symm.trans ((scheme.check_iff _ _ _).mpr ho))
        have hA : scheme.accepts st.spentNullifiers claim wit = false := by
          cases hb : scheme.accepts st.spentNullifiers claim wit with
          | false => rfl
          | true => exact absurd ((scheme.accepts_iff _ _ _).mp hb).2.2 hNotOwn
        have hK : scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit = false := by
          cases hb : scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit with
          | false => rfl
          | true => exact absurd ((scheme.keyAccepts_iff _ _ _).mp hb).2.2 hNotOwn
        rw [hA, hK]
      | true =>
        have hOwn : scheme.ownsKey claim.legacyPk wit claim := (scheme.check_iff _ _ _).mp hChk
        cases (inferInstance : Decidable
            (claim.legacyPk ∈ st.settledClaims.map (fun r => r.claim.legacyPk))) with
        | isTrue hSettled =>
          left
          have hSpent : claim.nullifier ∈ st.spentNullifiers := by
            rw [hInv.1, hNull]
            exact List.mem_map_of_mem (f := scheme.deriveNullifier) hSettled
          have hA : scheme.accepts st.spentNullifiers claim wit = false := by
            cases hb : scheme.accepts st.spentNullifiers claim wit with
            | false => rfl
            | true => exact absurd hSpent ((scheme.accepts_iff _ _ _).mp hb).2.1
          have hK : scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit = false := by
            cases hb : scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit with
            | false => rfl
            | true => exact absurd hSettled ((scheme.keyAccepts_iff _ _ _).mp hb).2.1
          rw [hA, hK]
        | isFalse hSettled =>
          cases (inferInstance : Decidable (claim.nullifier ∈ st.spentNullifiers)) with
          | isFalse hFresh =>
            left
            have hA : scheme.accepts st.spentNullifiers claim wit = true :=
              (scheme.accepts_iff _ _ _).mpr ⟨hNull, hFresh, hOwn⟩
            have hK : scheme.keyAccepts (st.settledClaims.map (fun r => r.claim.legacyPk)) claim wit = true :=
              (scheme.keyAccepts_iff _ _ _).mpr ⟨hNull, hSettled, hOwn⟩
            rw [hA, hK]
          | isTrue hMem =>
            right
            rw [hInv.1] at hMem
            obtain ⟨pk_prev, hpk, hEq⟩ := List.exists_of_mem_map hMem
            have hEnr : EnrolledEntitlement snapshot claim.legacyPk amount := hE
            exact ⟨List.mem_map_of_mem (f := Prod.fst) (EnrolledEntitlement.mem hEnr),
              pk_prev, hpk, settled_pk_mem_snapshot hInv hpk,
              fun hSame => hSettled (hSame ▸ hpk), hEq.trans hNull⟩

/-- Under finite-snapshot `NullifierInjOn`, `idealMigrateMachine` refines `idealKeyMigrateMachine`
    in exact lockstep (`⊑`). -/
def idealMigrate_refines_idealKeyMigrate_of_injOn {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (hInj : NullifierInjOn scheme.deriveNullifier (snapshot.map Prod.fst)) :
    idealMigrateMachine scheme snapshot ⊑ idealKeyMigrateMachine scheme snapshot :=
  LockstepSim.toRefines
    { Inv := fun st => st.Inv scheme snapshot
      abs := id
      init_inv := fun {c₀} hInit => by
        have hc : c₀ = IdealMigrateState.init := hInit
        subst hc
        exact ⟨IdealMigrateState.init_inv scheme snapshot, rfl⟩
      step_eq := fun {c} inp hInv => by
        rcases idealMigrate_step_eq_idealKeyMigrate_or_collision hInv inp.1 inp.2 with
          hEq | ⟨hSnapClaim, pk_prev, _, hSnapPrev, hNe, hNullEq⟩
        · cases hS : (idealMigrateMachine scheme snapshot).step c inp with
          | some pair =>
            rw [hS] at hEq
            exact ⟨(idealMigrateMachine_step_preserves_inv hInv hS).1, hEq.symm⟩
          | none =>
            rw [hS] at hEq
            exact ⟨hInv, hEq.symm, rfl⟩
        · exact False.elim (hNe (hInj hSnapPrev hSnapClaim hNullEq)) }

/-- Under finite-snapshot `NullifierInjOn`, `idealKeyMigrateMachine` also refines
    `idealMigrateMachine` in exact lockstep (`⊑`), establishing full bisimulation. -/
def idealKeyMigrate_refines_idealMigrate_of_injOn {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (hInj : NullifierInjOn scheme.deriveNullifier (snapshot.map Prod.fst)) :
    idealKeyMigrateMachine scheme snapshot ⊑ idealMigrateMachine scheme snapshot :=
  LockstepSim.toRefines
    { Inv := fun st => st.Inv scheme snapshot
      abs := id
      init_inv := fun {c₀} hInit => by
        have hc : c₀ = IdealMigrateState.init := hInit
        subst hc
        exact ⟨IdealMigrateState.init_inv scheme snapshot, rfl⟩
      step_eq := fun {c} inp hInv => by
        rcases idealMigrate_step_eq_idealKeyMigrate_or_collision hInv inp.1 inp.2 with
          hEq | ⟨hSnapClaim, pk_prev, _, hSnapPrev, hNe, hNullEq⟩
        · cases hK : (idealKeyMigrateMachine scheme snapshot).step c inp with
          | some pair =>
            have hM : (idealMigrateMachine scheme snapshot).step c inp = some pair :=
              hEq.trans hK
            exact ⟨(idealMigrateMachine_step_preserves_inv hInv hM).1, hM⟩
          | none =>
            exact ⟨hInv, hEq.trans hK, rfl⟩
        · exact False.elim (hNe (hInj hSnapPrev hSnapClaim hNullEq)) }

/-! ## 6. Rejection Teeth -/

private theorem step_none_of_not_accepts {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (st : IdealMigrateState LegacyPk) (claim : MigrationClaim LegacyPk) (wit : Witness)
    (h : ¬ (scheme.accepts st.spentNullifiers claim wit = true)) :
    (idealMigrateMachine scheme snapshot).step st (claim, wit) = none := by
  show idealMigrateSettle st claim (EnrolledSnapshot.entitlement snapshot claim.legacyPk)
    (scheme.accepts st.spentNullifiers claim wit) = none
  cases hA : scheme.accepts st.spentNullifiers claim wit with
  | false => cases EnrolledSnapshot.entitlement snapshot claim.legacyPk <;> rfl
  | true => exact absurd hA h

/-- `#tooth` A claim for a legacy key outside the enrolled snapshot is rejected, whatever its
    nullifier and witness. -/
theorem tooth_idealMigrate_unenrolled_legacyPk_rejected {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (st : IdealMigrateState LegacyPk) (claim : MigrationClaim LegacyPk) (wit : Witness)
    (hUnenrolled : EnrolledSnapshot.entitlement snapshot claim.legacyPk = none) :
    (idealMigrateMachine scheme snapshot).step st (claim, wit) = none := by
  show idealMigrateSettle st claim (EnrolledSnapshot.entitlement snapshot claim.legacyPk)
    (scheme.accepts st.spentNullifiers claim wit) = none
  rw [hUnenrolled]
  cases scheme.accepts st.spentNullifiers claim wit <;> rfl

/-- `#tooth` A claim whose nullifier is not the one derived from its legacy key is rejected. -/
theorem tooth_idealMigrate_underived_nullifier_rejected {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (st : IdealMigrateState LegacyPk) (claim : MigrationClaim LegacyPk) (wit : Witness)
    (hFreshNullifier : ¬ (claim.nullifier = scheme.deriveNullifier claim.legacyPk)) :
    (idealMigrateMachine scheme snapshot).step st (claim, wit) = none :=
  step_none_of_not_accepts scheme snapshot st claim wit
    (fun hA => hFreshNullifier ((scheme.accepts_iff _ _ _).mp hA).1)

/-- `#tooth` A claim whose witness does not satisfy the ownership relation is rejected. -/
theorem tooth_idealMigrate_unowned_witness_rejected {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    (st : IdealMigrateState LegacyPk) (claim : MigrationClaim LegacyPk) (wit : Witness)
    (hNotOwner : ¬ scheme.ownsKey claim.legacyPk wit claim) :
    (idealMigrateMachine scheme snapshot).step st (claim, wit) = none :=
  step_none_of_not_accepts scheme snapshot st claim wit
    (fun hA => hNotOwner ((scheme.accepts_iff _ _ _).mp hA).2.2)

/-- `#tooth` After a claim for a legacy key is accepted, every further claim for the same key is
    rejected, whatever nullifier, destination and witness it carries. -/
theorem tooth_idealMigrate_second_claim_same_legacyPk_rejected {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    {st st' : IdealMigrateState LegacyPk} {claim : MigrationClaim LegacyPk} {wit : Witness}
    {out : MigrationReceipt LegacyPk}
    (hStep : (idealMigrateMachine scheme snapshot).step st (claim, wit) = some (st', out))
    (claim' : MigrationClaim LegacyPk) (wit' : Witness)
    (hSame : claim'.legacyPk = claim.legacyPk) :
    (idealMigrateMachine scheme snapshot).step st' (claim', wit') = none := by
  obtain ⟨hValid, _, _, hSt⟩ :=
    (idealMigrateMachine_step_eq_some_iff scheme snapshot st st' claim wit out).mp hStep
  obtain ⟨_, hNull, _⟩ := hValid
  apply step_none_of_not_accepts
  intro hA
  obtain ⟨hNull', hFresh', _⟩ := (scheme.accepts_iff _ _ _).mp hA
  rw [hSt] at hFresh'
  apply hFresh'
  have hNullEq : claim'.nullifier = claim.nullifier :=
    hNull'.trans ((congrArg scheme.deriveNullifier hSame).trans hNull.symm)
  rw [hNullEq]
  exact .head _

/-- `#tooth` Tightness of the `NullifierCollision` branch: if two distinct enrolled keys `pk₁ ≠ pk₂`
    collide under `deriveNullifier`, settling `pk₁` causes `idealMigrateMachine` to reject `pk₂`
    even though `pk₂` is unsettled and `idealKeyMigrateMachine` accepts `pk₂`. -/
theorem tooth_idealMigrate_colliding_nullifier_blocks_second_key {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    (scheme : LegacyOwnershipScheme LegacyPk Witness) (snapshot : EnrolledSnapshot LegacyPk)
    {st st' : IdealMigrateState LegacyPk} {claim₁ claim₂ : MigrationClaim LegacyPk}
    {wit₁ wit₂ : Witness} {out₁ : MigrationReceipt LegacyPk} {amount₂ : Nat}
    (hStep₁ : (idealMigrateMachine scheme snapshot).step st (claim₁, wit₁) = some (st', out₁))
    (hValid₂ : ValidLegacyOwnership scheme snapshot claim₂ wit₂ amount₂)
    (hColl : NullifierCollision scheme.deriveNullifier claim₁.legacyPk claim₂.legacyPk) :
    (idealMigrateMachine scheme snapshot).step st' (claim₂, wit₂) = none := by
  obtain ⟨hValid₁, _, _, hSt⟩ :=
    (idealMigrateMachine_step_eq_some_iff scheme snapshot st st' claim₁ wit₁ out₁).mp hStep₁
  apply step_none_of_not_accepts
  intro hA
  obtain ⟨_, hFresh₂, _⟩ := (scheme.accepts_iff _ _ _).mp hA
  rw [hSt] at hFresh₂
  apply hFresh₂
  have hNullEq : claim₂.nullifier = claim₁.nullifier :=
    hValid₂.2.1.trans (hColl.2.symm.trans hValid₁.2.1.symm)
  rw [hNullEq]
  exact .head _

/-! ## 6b. Ownership Is Relative to `ownsKey` -/

/-- Caveat: the ownership guarantee is exactly as strong as `scheme.ownsKey`. If `ownsKey` holds
    for every key, witness and claim and `NullifierInjOn` holds on `snapshot`, then in every state
    satisfying the invariant a claim for an enrolled, not yet settled key under its derived
    nullifier is accepted with ANY witness and ANY destination. -/
theorem idealMigrateMachine_trivial_ownsKey_admits_any_witness {LegacyPk Witness : Type}
    [DecidableEq LegacyPk]
    {scheme : LegacyOwnershipScheme LegacyPk Witness} {snapshot : EnrolledSnapshot LegacyPk}
    (hInj : NullifierInjOn scheme.deriveNullifier (snapshot.map Prod.fst))
    (hTrivial : ∀ (pk : LegacyPk) (wit : Witness) (claim : MigrationClaim LegacyPk),
      scheme.ownsKey pk wit claim)
    {st : IdealMigrateState LegacyPk} (hInv : st.Inv scheme snapshot)
    {pk : LegacyPk} {amount : Nat} (hEnrolled : EnrolledEntitlement snapshot pk amount)
    (hUnclaimed : pk ∉ st.settledClaims.map (fun r => r.claim.legacyPk))
    (wit : Witness) (dest : Bytes) :
    (idealMigrateMachine scheme snapshot).step st (⟨pk, scheme.deriveNullifier pk, dest⟩, wit) =
      some ({ totalMigrated := st.totalMigrated + amount
              spentNullifiers := scheme.deriveNullifier pk :: st.spentNullifiers
              settledClaims := ⟨⟨pk, scheme.deriveNullifier pk, dest⟩, amount⟩ ::
                st.settledClaims },
            ⟨⟨pk, scheme.deriveNullifier pk, dest⟩, amount⟩) :=
  idealMigrateMachine_unclaimed_owner_accepts hInj hInv
    ⟨hEnrolled, rfl, hTrivial pk wit ⟨pk, scheme.deriveNullifier pk, dest⟩⟩ hUnclaimed

/-- Degenerate scheme over 256-bit keys whose ownership relation always holds. -/
def idealMigrateOpenScheme : LegacyOwnershipScheme Digest256 Digest256 where
  ownsKey _ _ _ := 0 = 0
  checkOwnership _ _ _ := true
  check_iff _ _ _ := ⟨fun _ => rfl, fun _ => rfl⟩
  deriveNullifier pk := pk

/-- `#tooth` Under the degenerate scheme the enrolled toy key is claimed from the initial state by
    every witness to every destination: no witness is rejected. -/
theorem tooth_idealMigrateOpen_any_witness_claims_enrolled_key (wit : Digest256) (dest : Bytes) :
    ¬ ((idealMigrateMachine idealMigrateOpenScheme [(6#256, 100)]).step
        IdealMigrateState.init (⟨6#256, 6#256, dest⟩, wit) = none) := by
  have hInj : NullifierInjOn idealMigrateOpenScheme.deriveNullifier
      (([(6#256, 100)] : EnrolledSnapshot Digest256).map Prod.fst) :=
    fun _ _ _ _ h => h
  have h := idealMigrateMachine_trivial_ownsKey_admits_any_witness
    (scheme := idealMigrateOpenScheme) (snapshot := [(6#256, 100)]) hInj (fun _ _ _ => rfl)
    (IdealMigrateState.init_inv idealMigrateOpenScheme [(6#256, 100)])
    (entitlement_cons_eq (6#256) 100 []) (fun h => nomatch h) wit dest
  intro hNone
  have h' : (idealMigrateMachine idealMigrateOpenScheme [(6#256, 100)]).step
      IdealMigrateState.init (⟨6#256, 6#256, dest⟩, wit) = some _ := h
  rw [hNone] at h'
  exact nomatch h'

/-! ## 7. Concrete Instance: the Audit's Pool-Drain Attempt -/

/-- Toy scheme over 256-bit keys: the witness `wit` owns `pk` when `pk = wit + wit`, and the
    nullifier of a key is the key itself. -/
def idealMigrateToyScheme : LegacyOwnershipScheme Digest256 Digest256 where
  ownsKey pk wit _ := pk = wit + wit
  checkOwnership pk wit _ := decide (pk = wit + wit)
  check_iff _ _ _ := decide_eq_true_iff
  deriveNullifier pk := pk

/-- Toy snapshot enrolling the single key `6` with entitlement `100`. -/
def idealMigrateToySnapshot : EnrolledSnapshot Digest256 := [(6#256, 100)]

/-- The owner of the enrolled toy key is accepted and mints exactly its entitlement. -/
theorem idealMigrateToy_owner_claim_accepted :
    (idealMigrateMachine idealMigrateToyScheme idealMigrateToySnapshot).step
        IdealMigrateState.init (⟨6#256, 6#256, []⟩, 3#256) =
      some ({ totalMigrated := 100
              spentNullifiers := [6#256]
              settledClaims := [⟨⟨6#256, 6#256, []⟩, 100⟩] },
            ⟨⟨6#256, 6#256, []⟩, 100⟩) := by
  have hInj : NullifierInjOn idealMigrateToyScheme.deriveNullifier
      (idealMigrateToySnapshot.map Prod.fst) :=
    fun _ _ _ _ h => h
  have hValid : ValidLegacyOwnership idealMigrateToyScheme idealMigrateToySnapshot
      ⟨6#256, 6#256, []⟩ (3#256) 100 :=
    ⟨entitlement_cons_eq (6#256) 100 [], rfl, (by decide : (6#256 : Digest256) = 3#256 + 3#256)⟩
  exact idealMigrateMachine_unclaimed_owner_accepts hInj
    (IdealMigrateState.init_inv idealMigrateToyScheme idealMigrateToySnapshot) hValid
    (fun h => nomatch h)

/-- `#tooth` The audit's attack on the former Boolean interface: claims for keys outside the
    snapshot under arbitrary fresh nullifiers, with any witness, in any state. All are rejected. -/
theorem tooth_idealMigrate_audit_fresh_nullifier_drain_rejected
    (st : IdealMigrateState Digest256) (pk nullifier wit : Digest256) (dest : Bytes)
    (hNotEnrolled : ¬ (pk = 6#256)) :
    (idealMigrateMachine idealMigrateToyScheme idealMigrateToySnapshot).step st
      (⟨pk, nullifier, dest⟩, wit) = none :=
  tooth_idealMigrate_unenrolled_legacyPk_rejected idealMigrateToyScheme idealMigrateToySnapshot
    st ⟨pk, nullifier, dest⟩ wit ((entitlement_cons_ne hNotEnrolled 100 []).trans (by rfl))

/-- `#tooth` Reusing the enrolled toy key under a fresh nullifier is rejected even with the
    owner's witness. -/
theorem tooth_idealMigrate_audit_enrolled_key_fresh_nullifier_rejected
    (st : IdealMigrateState Digest256) (nullifier : Digest256) (dest : Bytes)
    (hFreshNullifier : ¬ (nullifier = 6#256)) :
    (idealMigrateMachine idealMigrateToyScheme idealMigrateToySnapshot).step st
      (⟨6#256, nullifier, dest⟩, 3#256) = none :=
  tooth_idealMigrate_underived_nullifier_rejected idealMigrateToyScheme idealMigrateToySnapshot
    st ⟨6#256, nullifier, dest⟩ (3#256) hFreshNullifier

#tooth_pair Qsag.Spec.idealMigrateMachine_step_eq_some_iff vs
  Qsag.Spec.tooth_idealMigrate_unowned_witness_rejected
#tooth_pair Qsag.Spec.idealMigrateMachine_trace_ownership_sound vs
  Qsag.Spec.tooth_idealMigrate_underived_nullifier_rejected
#tooth_pair Qsag.Spec.idealMigrateMachine_trace_no_double_claim vs
  Qsag.Spec.tooth_idealMigrate_second_claim_same_legacyPk_rejected
#tooth_pair Qsag.Spec.idealMigrateMachine_trace_minted_le_enrolled vs
  Qsag.Spec.tooth_idealMigrate_unenrolled_legacyPk_rejected
#tooth_pair Qsag.Spec.idealMigrateToy_owner_claim_accepted vs
  Qsag.Spec.tooth_idealMigrate_audit_fresh_nullifier_drain_rejected
#tooth_pair Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts vs
  Qsag.Spec.tooth_idealMigrate_audit_enrolled_key_fresh_nullifier_rejected
#tooth_pair Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts_or_collision vs
  Qsag.Spec.tooth_idealMigrate_colliding_nullifier_blocks_second_key

#tooth_pair Qsag.Spec.idealMigrateMachine_trivial_ownsKey_admits_any_witness vs
  Qsag.Spec.tooth_idealMigrateOpen_any_witness_claims_enrolled_key

#verify_constructive
  Qsag.Spec.idealMigrateMachine_trivial_ownsKey_admits_any_witness
  Qsag.Spec.EnrolledEntitlement.mem
  Qsag.Spec.NullifierInjOn_iff
  Qsag.Spec.NullifierInjective_iff
  Qsag.Spec.NullifierInjective.injOn
  Qsag.Spec.LegacyOwnershipScheme.accepts_iff
  Qsag.Spec.LegacyOwnershipScheme.keyAccepts_iff
  Qsag.Spec.idealMigrateMachine_step_eq_some_iff
  Qsag.Spec.idealKeyMigrateMachine_step_eq_some_iff
  Qsag.Spec.IdealMigrateState.init_inv
  Qsag.Spec.idealMigrateMachine_step_preserves_inv
  Qsag.Spec.idealMigrateMachine_trace_preserves_inv
  Qsag.Spec.idealMigrateMachine_reachable_inv
  Qsag.Spec.IdealMigrateState.Inv.settled_legacyPk_nodup
  Qsag.Spec.IdealMigrateState.Inv.totalMigrated_le_enrolled
  Qsag.Spec.idealMigrateMachine_trace_ownership_sound
  Qsag.Spec.idealMigrateMachine_trace_nullifier_fresh
  Qsag.Spec.idealMigrateMachine_trace_no_double_claim
  Qsag.Spec.idealMigrateMachine_trace_totalMigrated
  Qsag.Spec.idealMigrateMachine_trace_minted_le_enrolled
  Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts_or_collision
  Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts
  Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts_of_injective
  Qsag.Spec.idealMigrate_step_eq_idealKeyMigrate_or_collision
  Qsag.Spec.tooth_idealMigrate_unenrolled_legacyPk_rejected
  Qsag.Spec.tooth_idealMigrate_underived_nullifier_rejected
  Qsag.Spec.tooth_idealMigrate_unowned_witness_rejected
  Qsag.Spec.tooth_idealMigrate_second_claim_same_legacyPk_rejected
  Qsag.Spec.tooth_idealMigrate_colliding_nullifier_blocks_second_key
  Qsag.Spec.idealMigrateToy_owner_claim_accepted
  Qsag.Spec.tooth_idealMigrate_audit_fresh_nullifier_drain_rejected
  Qsag.Spec.tooth_idealMigrate_audit_enrolled_key_fresh_nullifier_rejected

end Qsag.Spec
end
