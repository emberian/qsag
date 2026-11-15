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
  (`check_iff`), and the deterministic injective nullifier derivation `deriveNullifier`.

`idealMigrateMachine` receives a claim together with the ownership witness itself and mints exactly
when `ValidLegacyOwnership` holds (the key is enrolled, the nullifier is the derived one, the witness
satisfies `ownsKey` for this claim) and the nullifier is unspent. The minted amount is the enrolled
entitlement of the key; a claim carries no amount.

Results:
1. `idealMigrateMachine_step_eq_some_iff`: exact characterization of acceptance.
2. `idealMigrateMachine_trace_ownership_sound`: every accepted claim of a valid trace satisfies
   `ValidLegacyOwnership` with the minted amount.
3. `idealMigrateMachine_trace_no_double_claim`: the legacy keys accepted along a valid trace are
   pairwise distinct.
4. `idealMigrateMachine_trace_minted_le_enrolled`: the amounts minted along an initialized trace sum
   to at most the total enrolled entitlement.
5. `idealMigrateMachine_unclaimed_owner_accepts`: by injectivity of `deriveNullifier`, the owner of an
   enrolled key that has not been settled is accepted in every reachable state.
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
    relation over the whole claim, a Boolean checker deciding it, and the deterministic injective
    nullifier derivation. -/
structure LegacyOwnershipScheme (LegacyPk Witness : Type) where
  ownsKey : LegacyPk → Witness → MigrationClaim LegacyPk → Prop
  checkOwnership : LegacyPk → Witness → MigrationClaim LegacyPk → Bool
  check_iff : ∀ (pk : LegacyPk) (wit : Witness) (claim : MigrationClaim LegacyPk),
    checkOwnership pk wit claim = true ↔ ownsKey pk wit claim
  deriveNullifier : LegacyPk → Digest256
  deriveNullifier_injective : ∀ {pk₁ pk₂ : LegacyPk},
    deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂

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

/-- No blocking by other identities: in a state satisfying the invariant, a claim with
    `ValidLegacyOwnership` whose legacy key is not yet settled is accepted and mints its
    entitlement. Injectivity of `deriveNullifier` excludes a collision with a spent nullifier. -/
theorem idealMigrateMachine_unclaimed_owner_accepts {LegacyPk Witness : Type}
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
            { claim := claim, amount := amount }) := by
  refine (idealMigrateMachine_step_eq_some_iff scheme snapshot st _ claim wit _).mpr
    ⟨hValid, ?_, rfl, rfl⟩
  intro hMem
  obtain ⟨hMap, _, _, _⟩ := hInv
  rw [hMap] at hMem
  obtain ⟨pk, hpk, hEq⟩ := List.exists_of_mem_map hMem
  obtain ⟨_, hNull, _⟩ := hValid
  have hPk : pk = claim.legacyPk := scheme.deriveNullifier_injective (hEq.trans hNull)
  subst hPk
  exact hUnclaimed hpk

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

/-! ## 7. Concrete Instance: the Audit's Pool-Drain Attempt -/

/-- Toy scheme over 256-bit keys: the witness `wit` owns `pk` when `pk = wit + wit`, and the
    nullifier of a key is the key itself. -/
def idealMigrateToyScheme : LegacyOwnershipScheme Digest256 Digest256 where
  ownsKey pk wit _ := pk = wit + wit
  checkOwnership pk wit _ := decide (pk = wit + wit)
  check_iff _ _ _ := decide_eq_true_iff
  deriveNullifier pk := pk
  deriveNullifier_injective h := h

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
  have hValid : ValidLegacyOwnership idealMigrateToyScheme idealMigrateToySnapshot
      ⟨6#256, 6#256, []⟩ (3#256) 100 :=
    ⟨entitlement_cons_eq (6#256) 100 [], rfl, (by decide : (6#256 : Digest256) = 3#256 + 3#256)⟩
  exact idealMigrateMachine_unclaimed_owner_accepts
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

#verify_constructive
  Qsag.Spec.EnrolledEntitlement.mem
  Qsag.Spec.LegacyOwnershipScheme.accepts_iff
  Qsag.Spec.idealMigrateMachine_step_eq_some_iff
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
  Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts
  Qsag.Spec.tooth_idealMigrate_unenrolled_legacyPk_rejected
  Qsag.Spec.tooth_idealMigrate_underived_nullifier_rejected
  Qsag.Spec.tooth_idealMigrate_unowned_witness_rejected
  Qsag.Spec.tooth_idealMigrate_second_claim_same_legacyPk_rejected
  Qsag.Spec.idealMigrateToy_owner_claim_accepted
  Qsag.Spec.tooth_idealMigrate_audit_fresh_nullifier_drain_rejected
  Qsag.Spec.tooth_idealMigrate_audit_enrolled_key_fresh_nullifier_rejected

end Qsag.Spec
end
