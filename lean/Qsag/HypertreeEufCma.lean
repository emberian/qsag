module
/-
# Qsag.HypertreeEufCma — Checked Stateful `Jorts` `EpochLatch` & Multi-Layer Hypertree + FORS EUF-CMA Reduction

Formalization of checked stateful and stateless hypertree signing and constructive EUF-CMA witness extraction
in Lean 4.35 (`0 sorry`, `0` custom axioms, `0 Classical.choice`, `≤ 6` `@[expose]`):
1. **Checked Error-Aware Stateful `Jorts` `EpochLatch` (`checkedStatefulSignStep`, `execCheckedStatefulStrict`,
   `execCheckedStatefulOracle`, `checkedStatefulLog_one_message_per_leaf`, `checkedStatefulLog_unique_layer_codeword`)**:
   Enforces `checkedStatefulValid` parameter geometry, deterministic domain-separated per-epoch randomness
   (`QSAG.PQ.BAGGYSIG.DET/v1`), strict leaf budget `epoch < 2 ^ params.maxSigsLog2`, crash-retry idempotency,
   and explicit `Except CheckedStatefulError` abort on budget exhaustion, stale/out-of-order epochs,
   not-in-flight retries, equivocation, or TSW grind exhaustion, proving the multi-turn finite-log
   one-message / one-codeword per `(layer, tree, leaf)` invariant across all layers `0 ≤ i < d`.
2. **256-Bit `TSW` Base-4 & Base-16 Digit Bijections (`extractBaseWDigits_4_128_take32_eq`,
   `extractBaseWDigits_base16_prefix_injective`)**:
   Proves that for `(w, ℓ₁) ∈ {(4, 128), (16, 64)}`, `extractBaseWDigits` injectively determines the
   entire 32-byte first block `b0` of `thHashMsg`, eliminating modular/truncation collisions.
3. **Reachable-Layer & Finite-Log Constructive `PSum` EUF-CMA Extractors (`extractReachableHypertreeForgery`,
   `checked_stateful_hypertree_euf_cma_extract`, `checked_stateless_hypertree_euf_cma_extract`)**:
   Formulates `ReachableUpperHypertreePos` (`0 < l ∧ l < d ∧ g < 2 ^ ((d - l) * h)`) so all upper-layer
   oracle premises are constructively discharged from a finite signing log (`0` `UInt32`/`UInt64`
   wraparound), and connects multi-turn checked stateful and checked stateless transcripts end-to-end
   with `0 Classical.choice` to transcript-indexed collision / WOTS+C-TSW / FORS witnesses, paired with
   `#tooth` leaf-reuse forgery (`mutantUncheckedReuseSign`) and multi-signature inhabitedness witnesses.
-/

/-
Security boundary.
* `extractFullHypertreeForgery` preserves its legacy caller-supplied `QueriedWotsOracle` signature for
  downstream compatibility and delegates to `extractReachableHypertreeForgery`, whose bounded
  `ReachableUpperHypertreePos` (`0 < l ∧ l < d`) oracle premise is discharged from finite signing logs.
* Section 5 covers legacy stateless logs (`hypertree_forgery_break_of_signingLog`,
  `hypertree_euf_cma_advantage_bound`), while Section 6 covers checked stateful `Jorts` and checked
  stateless transcripts (`checked_stateful_hypertree_euf_cma_extract`,
  `checked_stateful_hypertree_euf_cma_advantage_bound`, `checked_stateless_hypertree_euf_cma_extract`)
  for `(w, ℓ₁) ∈ {(4, 128), (16, 64)}`.
* Extracted break events and `hitCount` union bounds classify witnesses over finite coins.
  Their factor-one coefficients do not establish resource-bounded primitive adversaries,
  challenge embedding, simulation cost, or a computational multi-target reduction.
* These extractors consume the legacy compatibility core. The separate production core in
  HashSigs is not yet the target of these EUF-CMA theorems.
-/

public import Qsag.Goldilocks
public import Qsag.Keccak
public import Qsag.Poseidon2
public import Qsag.UcGames
public import Qsag.HashSigs
import all Qsag.Keccak
import all Qsag.HashSigs

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-- Inputs to the executable signing oracle. Failed requests add no transcript entry. -/
structure PqSigningQuery where
  message : List UInt8
  randomness : List UInt8
  leaf : Nat
  grindLimit : Nat

def signingOracleLog (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) :
    List PqSigningQuery → List (List UInt8 × PqHashSig)
  | [] => []
  | q :: qs =>
    match evalSingleSign suite params sk q.message q.randomness q.leaf q.grindLimit with
    | none => signingOracleLog suite params sk qs
    | some sig => (q.message, sig) :: signingOracleLog suite params sk qs

/-- Every logged response has provenance in an actual successful signing-oracle query. -/
theorem signingOracleLog_generated (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List PqSigningQuery) (msg : List UInt8) (sig : PqHashSig)
    (h : (msg, sig) ∈ signingOracleLog suite params sk queries) :
    ∃ q ∈ queries, q.message = msg ∧
      evalSingleSign suite params sk q.message q.randomness q.leaf q.grindLimit = some sig := by
  induction queries with
  | nil => cases h
  | cons q qs ih =>
    unfold signingOracleLog at h
    cases he : evalSingleSign suite params sk q.message q.randomness q.leaf q.grindLimit with
    | none =>
      rw [he] at h
      obtain ⟨r, hr, hm, hs⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem q hr, hm, hs⟩
    | some out =>
      rw [he] at h
      rcases List.mem_cons.mp h with head | tail
      · have hp := Prod.mk.inj head
        exact ⟨q, List.mem_cons_self, hp.1.symm, hp.2 ▸ he⟩
      · obtain ⟨r, hr, hm, hs⟩ := ih tail
        exact ⟨r, List.mem_cons_of_mem q hr, hm, hs⟩

theorem signingOracleLog_accepts (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List PqSigningQuery) (msg : List UInt8) (sig : PqHashSig)
    (h : (msg, sig) ∈ signingOracleLog suite params sk queries) :
    verifyPqHashSig suite params (derivePublicKey suite params sk) msg sig = true := by
  obtain ⟨q, _, hm, hs⟩ := signingOracleLog_generated suite params sk queries msg sig h
  rw [← hm]
  exact verifyPqHashSig_evalSingleSign suite params sk q.message q.randomness q.leaf q.grindLimit sig hs

/-- Regression: an unsigned message cannot be inserted into a derived oracle log. -/
theorem signingOracleLog_no_unqueried_message (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List PqSigningQuery) (msg : List UInt8) (sig : PqHashSig)
    (fresh : ∀ q ∈ queries, q.message ≠ msg) :
    (msg, sig) ∉ signingOracleLog suite params sk queries := by
  intro h
  obtain ⟨q, hq, hm, _⟩ := signingOracleLog_generated suite params sk queries msg sig h
  exact fresh q hq hm

/-! ## 1. Stateful `Jorts` Monotonic `EpochLatch` & Crash-Retry Idempotency -/

/-- Persistent write-ahead-logged `EpochLatch` state for stateful `Jorts` validators. -/
structure EpochLatchState where
  nextEpoch   : Nat
  latchedLast : Option (Nat × List UInt8 × PqHashSig)
  deriving DecidableEq, Repr

/-- Well-formedness invariant: any cached `(ep, msg, sig)` in `latchedLast` has `ep < nextEpoch`. -/
def EpochLatchState.WellFormed (st : EpochLatchState) : Prop :=
  ∀ ep m s, st.latchedLast = some (ep, m, s) → ep < st.nextEpoch

/-- Crash-safe monotonic `Jorts` signing transition:
    1. Exact `(reqEpoch, msg)` matching `latchedLast` returns `(st, cachedSig)` idempotently;
    2. Fresh `reqEpoch = st.nextEpoch` signs once, advances `nextEpoch := reqEpoch + 1`, and latches `(reqEpoch, msg, sig)`;
    3. Every stale, out-of-order, or equivocating request (`reqEpoch ≠ st.nextEpoch` not matching `latchedLast`) returns `none`. -/
@[expose] def epochLatchSign (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind : Nat)
    (st : EpochLatchState) (reqEpoch : Nat) (msg : List UInt8) :
    Option (EpochLatchState × PqHashSig) :=
  match st.latchedLast with
  | some (ep, prevMsg, prevSig) =>
    if reqEpoch == ep && decide (msg = prevMsg) then
      some (st, prevSig)
    else if reqEpoch == st.nextEpoch then
      match evalSingleSign suite params sk msg optRand reqEpoch maxGrind with
      | none => none
      | some sig =>
        some ({ nextEpoch := reqEpoch + 1, latchedLast := some (reqEpoch, msg, sig) }, sig)
    else
      none
  | none =>
    if reqEpoch == st.nextEpoch then
      match evalSingleSign suite params sk msg optRand reqEpoch maxGrind with
      | none => none
      | some sig =>
        some ({ nextEpoch := reqEpoch + 1, latchedLast := some (reqEpoch, msg, sig) }, sig)
    else
      none

/-- **Stateful `Jorts` Crash-Retry Idempotency (`stateful_jorts_crash_retry_idempotent`)**:
    After a fresh epoch signature is persisted in `st'`, retrying the exact same `(reqEpoch, msg)`
    after a crash/network drop returns the **identical** `(st', sig)` without advancing `nextEpoch`! -/
theorem stateful_jorts_crash_retry_idempotent
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind : Nat)
    (reqEpoch : Nat) (msg : List UInt8) (sig : PqHashSig) :
    let st' : EpochLatchState := { nextEpoch := reqEpoch + 1, latchedLast := some (reqEpoch, msg, sig) }
    epochLatchSign suite params sk optRand maxGrind st' reqEpoch msg = some (st', sig) := by
  simp only [epochLatchSign, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]

/-- **`#tooth` Stateful `Jorts` Equivocation Refusal (`stateful_jorts_equivocation_rejected`)**:
    Once `(reqEpoch, msg, sig)` is latched in `st'`, attempting to sign ANY distinct message
    `msg' ≠ msg` at `reqEpoch` is unconditionally rejected (`= none`)! -/
theorem stateful_jorts_equivocation_rejected
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind : Nat)
    (reqEpoch : Nat) (msg msg' : List UInt8) (sig : PqHashSig)
    (hDiff : msg' ≠ msg) :
    let st' : EpochLatchState := { nextEpoch := reqEpoch + 1, latchedLast := some (reqEpoch, msg, sig) }
    epochLatchSign suite params sk optRand maxGrind st' reqEpoch msg' = none := by
  intro st'
  unfold epochLatchSign
  dsimp only [st']
  have hMsgBeq : decide (msg' = msg) = false := decide_eq_false hDiff
  have hEpBeq : (reqEpoch == reqEpoch + 1) = false := beq_false_of_ne (by omega)
  simp [hMsgBeq, hEpBeq]

/-- Execute a multi-turn sequence of `(reqEpoch, msg)` requests against `EpochLatchState`,
    recording all emitted `(epoch, msg, sig)` triples. -/
def execEpochLatchTrace (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind : Nat) :
    EpochLatchState → List (Nat × List UInt8) → EpochLatchState × List (Nat × List UInt8 × PqHashSig)
  | st, [] => (st, [])
  | st, (ep, msg) :: rest =>
    match epochLatchSign suite params sk optRand maxGrind st ep msg with
    | none => execEpochLatchTrace suite params sk optRand maxGrind st rest
    | some (st', sig) =>
      let (stFinal, logRest) := execEpochLatchTrace suite params sk optRand maxGrind st' rest
      (stFinal, (ep, msg, sig) :: logRest)

/-- Single-step invariant preservation & non-equivocation for `epochLatchSign`. -/
theorem epochLatchSign_preserves_wellFormed
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind : Nat)
    {st st' : EpochLatchState} {reqEpoch : Nat} {msg : List UInt8} {sig : PqHashSig}
    (hWf : st.WellFormed)
    (hStep : epochLatchSign suite params sk optRand maxGrind st reqEpoch msg = some (st', sig)) :
    st'.WellFormed ∧
    st.nextEpoch ≤ st'.nextEpoch ∧
    ((∃ s0, st.latchedLast = some (reqEpoch, msg, s0) ∧ st' = st) ∨
     (reqEpoch = st.nextEpoch ∧ st'.nextEpoch = reqEpoch + 1 ∧
      st'.latchedLast = some (reqEpoch, msg, sig))) := by
  unfold epochLatchSign at hStep
  cases hLat : st.latchedLast with
  | none =>
    rw [hLat] at hStep
    cases hEqEp : (reqEpoch == st.nextEpoch)
    · simp [hEqEp] at hStep
    · simp only [hEqEp, ↓reduceIte] at hStep
      have hEp : reqEpoch = st.nextEpoch := of_decide_eq_true (by simpa [beq_iff_eq] using hEqEp)
      cases hEv : evalSingleSign suite params sk msg optRand reqEpoch maxGrind with
      | none => simp [hEv] at hStep
      | some s =>
        simp only [hEv, Option.some.injEq, Prod.mk.injEq] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        refine ⟨?_, by dsimp only; omega, .inr ⟨hEp, rfl, rfl⟩⟩
        intro ep' m' s' hSome
        injection hSome with hTuple
        rcases Prod.mk.inj hTuple with ⟨rfl, _⟩
        dsimp only
        omega
  | some triple =>
    rcases triple with ⟨ep0, m0, s0⟩
    rw [hLat] at hStep
    cases hHit : (reqEpoch == ep0 && decide (msg = m0))
    · simp only [hHit, Bool.false_eq_true, ↓reduceIte] at hStep
      cases hEqEp : (reqEpoch == st.nextEpoch)
      · simp [hEqEp] at hStep
      · simp only [hEqEp, ↓reduceIte] at hStep
        have hEp : reqEpoch = st.nextEpoch := of_decide_eq_true (by simpa [beq_iff_eq] using hEqEp)
        cases hEv : evalSingleSign suite params sk msg optRand reqEpoch maxGrind with
        | none => simp [hEv] at hStep
        | some s =>
          simp only [hEv, Option.some.injEq, Prod.mk.injEq] at hStep
          rcases hStep with ⟨rfl, rfl⟩
          refine ⟨?_, by dsimp only; omega, .inr ⟨hEp, rfl, rfl⟩⟩
          intro ep' m' s' hSome
          injection hSome with hTuple
          rcases Prod.mk.inj hTuple with ⟨rfl, _⟩
          dsimp only
          omega
    · simp only [hHit, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
      rcases hStep with ⟨rfl, rfl⟩
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hHit
      rcases hHit with ⟨rfl, rfl⟩
      exact ⟨hWf, Nat.le_refl _, .inl ⟨s0, rfl, rfl⟩⟩

/-- **Multi-Turn `EpochLatch` Non-Equivocation (`epochLatch_trace_no_equivocation`)**:
    Starting from `{ nextEpoch := 0, latchedLast := none }`, along ANY multi-turn request trace
    `reqs`, every emitted `(ep₁, m₁, s₁)` and `(ep₂, m₂, s₂)` with `ep₁ = ep₂` has **`m₁ = m₂`**! -/
theorem epochLatch_trace_no_equivocation
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind : Nat)
    (reqs : List (Nat × List UInt8)) :
    let (_, emitted) := execEpochLatchTrace suite params sk optRand maxGrind ⟨0, none⟩ reqs
    ∀ ep m1 s1 m2 s2,
      (ep, m1, s1) ∈ emitted → (ep, m2, s2) ∈ emitted → m1 = m2 := by
  -- Strengthened inductive invariant over any well-formed state `st`:
  -- every `(ep, m, s) ∈ emitted` satisfies EITHER `∃ s0, st.latchedLast = some (ep, m, s0)` OR `st.nextEpoch ≤ ep`,
  -- AND no two entries in `emitted` equivocate on `ep`.
  have hGen :
      ∀ (rs : List (Nat × List UInt8)) (st : EpochLatchState),
        st.WellFormed →
        let (_, emitted) := execEpochLatchTrace suite params sk optRand maxGrind st rs
        (∀ ep m s, (ep, m, s) ∈ emitted →
          (∃ s0, st.latchedLast = some (ep, m, s0)) ∨ st.nextEpoch ≤ ep) ∧
        (∀ ep m1 s1 m2 s2, (ep, m1, s1) ∈ emitted → (ep, m2, s2) ∈ emitted → m1 = m2) := by
    intro rs
    induction rs with
    | nil =>
      intro st _
      simp [execEpochLatchTrace]
    | cons req rest ih =>
      rcases req with ⟨reqEp, reqMsg⟩
      intro st hWf
      simp only [execEpochLatchTrace]
      cases hSign : epochLatchSign suite params sk optRand maxGrind st reqEp reqMsg with
      | none => exact ih st hWf
      | some pair =>
        rcases pair with ⟨st', sig⟩
        dsimp only
        obtain ⟨hWf', hNextLe, hBranch⟩ := epochLatchSign_preserves_wellFormed suite params sk optRand maxGrind hWf hSign
        obtain ⟨hBoundRest, hNoEqRest⟩ := ih st' hWf'
        refine ⟨?_, ?_⟩
        · intro ep m s hMem
          rcases List.mem_cons.mp hMem with hHead | hTail
          · rcases Prod.mk.inj hHead with ⟨rfl, hMS⟩
            rcases Prod.mk.inj hMS with ⟨rfl, _⟩
            rcases hBranch with ⟨s0, hLat0, _⟩ | ⟨rfl, _, _⟩
            · exact .inl ⟨s0, hLat0⟩
            · exact .inr (Nat.le_refl _)
          · rcases hBoundRest ep m s hTail with ⟨s1, hLat1⟩ | hGeNext'
            · rcases hBranch with ⟨s0, _, rfl⟩ | ⟨rfl, _, hLatNew⟩
              · exact .inl ⟨s1, hLat1⟩
              · rw [hLatNew] at hLat1
                injection hLat1 with hTup
                rcases Prod.mk.inj hTup with ⟨rfl, _⟩
                exact .inr (Nat.le_refl _)
            · exact .inr (Nat.le_trans hNextLe hGeNext')
        · intro ep m1 s1 m2 s2 hM1 hM2
          rcases List.mem_cons.mp hM1 with hH1 | hT1 <;> rcases List.mem_cons.mp hM2 with hH2 | hT2
          · rcases Prod.mk.inj hH1 with ⟨_, hMS1⟩
            rcases Prod.mk.inj hMS1 with ⟨rfl, _⟩
            rcases Prod.mk.inj hH2 with ⟨_, hMS2⟩
            rcases Prod.mk.inj hMS2 with ⟨rfl, _⟩
            rfl
          · rcases Prod.mk.inj hH1 with ⟨rfl, hMS1⟩
            rcases Prod.mk.inj hMS1 with ⟨rfl, _⟩
            rcases hBoundRest ep m2 s2 hT2 with ⟨s1, hLat1⟩ | hGeNext'
            · rcases hBranch with ⟨s0, hLat0, rfl⟩ | ⟨_, _, hLatNew⟩
              · rw [hLat0] at hLat1
                injection hLat1 with hTup
                exact (Prod.mk.inj (Prod.mk.inj hTup).2).1
              · rw [hLatNew] at hLat1
                injection hLat1 with hTup
                exact (Prod.mk.inj (Prod.mk.inj hTup).2).1
            · rcases hBranch with ⟨s0, hLat0, rfl⟩ | ⟨rfl, hNextEq, _⟩
              · have hLt := hWf ep m1 s0 hLat0
                omega
              · omega
          · rcases Prod.mk.inj hH2 with ⟨rfl, hMS2⟩
            rcases Prod.mk.inj hMS2 with ⟨rfl, _⟩
            rcases hBoundRest ep m1 s1 hT1 with ⟨s1, hLat1⟩ | hGeNext'
            · rcases hBranch with ⟨s0, hLat0, rfl⟩ | ⟨_, _, hLatNew⟩
              · rw [hLat0] at hLat1
                injection hLat1 with hTup
                exact (Prod.mk.inj (Prod.mk.inj hTup).2).1.symm
              · rw [hLatNew] at hLat1
                injection hLat1 with hTup
                exact (Prod.mk.inj (Prod.mk.inj hTup).2).1.symm
            · rcases hBranch with ⟨s0, hLat0, rfl⟩ | ⟨rfl, hNextEq, _⟩
              · have hLt := hWf ep m2 s0 hLat0
                omega
              · omega
          · exact hNoEqRest ep m1 s1 m2 s2 hT1 hT2
  have hInitWf : (⟨0, none⟩ : EpochLatchState).WellFormed := fun _ _ _ h => by cases h
  exact (hGen reqs ⟨0, none⟩ hInitWf).2

/-- Explicit contract-violation predicate characterizing every `none` refusal of legacy `epochLatchSign`
    (`skip_implies_contract_violation` anti-narrowing completeness for `execEpochLatchTrace`). -/
inductive EpochLatchContractViolation (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind : Nat)
    (st : EpochLatchState) (reqEpoch : Nat) (msg : List UInt8) : Prop where
  | badEpochOrEquivocation :
      (∀ prevSig, st.latchedLast ≠ some (reqEpoch, msg, prevSig)) →
      reqEpoch ≠ st.nextEpoch →
      EpochLatchContractViolation suite params sk optRand maxGrind st reqEpoch msg
  | signFailed :
      (∀ prevSig, st.latchedLast ≠ some (reqEpoch, msg, prevSig)) →
      reqEpoch = st.nextEpoch →
      evalSingleSign suite params sk msg optRand reqEpoch maxGrind = none →
      EpochLatchContractViolation suite params sk optRand maxGrind st reqEpoch msg

/-- `epochLatchSign` returns `none` **if and only if** `EpochLatchContractViolation` holds (`0` silent valid-request drops). -/
theorem epochLatchSign_none_iff_violation
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind : Nat)
    (st : EpochLatchState) (reqEpoch : Nat) (msg : List UInt8) :
    epochLatchSign suite params sk optRand maxGrind st reqEpoch msg = none ↔
      EpochLatchContractViolation suite params sk optRand maxGrind st reqEpoch msg := by
  constructor
  · intro hNone
    unfold epochLatchSign at hNone
    cases hLat : st.latchedLast with
    | none =>
      rw [hLat] at hNone
      have hNoRetry : ∀ prevSig, st.latchedLast ≠ some (reqEpoch, msg, prevSig) := by
        intro _ hEq; rw [hLat] at hEq; cases hEq
      cases hEp : (reqEpoch == st.nextEpoch)
      · exact .badEpochOrEquivocation hNoRetry (by intro hE; subst hE; simp at hEp)
      · simp only [hEp, ↓reduceIte] at hNone
        have hEpEq : reqEpoch = st.nextEpoch := of_decide_eq_true (by simpa [beq_iff_eq] using hEp)
        cases hEv : evalSingleSign suite params sk msg optRand reqEpoch maxGrind with
        | none => exact .signFailed hNoRetry hEpEq hEv
        | some _ => rw [hEv] at hNone; cases hNone
    | some triple =>
      rcases triple with ⟨ep0, m0, s0⟩
      rw [hLat] at hNone
      cases hHit : (reqEpoch == ep0 && decide (msg = m0))
      · simp only [hHit, Bool.false_eq_true, ↓reduceIte] at hNone
        have hNoRetry : ∀ prevSig, st.latchedLast ≠ some (reqEpoch, msg, prevSig) := by
          intro prevSig hEq
          rw [hLat] at hEq
          injection hEq with hTup
          rcases Prod.mk.inj hTup with ⟨rfl, hMS⟩
          rcases Prod.mk.inj hMS with ⟨rfl, _⟩
          simp at hHit
        cases hEp : (reqEpoch == st.nextEpoch)
        · exact .badEpochOrEquivocation hNoRetry (by intro hE; subst hE; simp at hEp)
        · simp only [hEp, ↓reduceIte] at hNone
          have hEpEq : reqEpoch = st.nextEpoch := of_decide_eq_true (by simpa [beq_iff_eq] using hEp)
          cases hEv : evalSingleSign suite params sk msg optRand reqEpoch maxGrind with
          | none => exact .signFailed hNoRetry hEpEq hEv
          | some _ => rw [hEv] at hNone; cases hNone
      · dsimp only at hNone
        rw [hHit] at hNone
        simp at hNone
  · intro hViol
    unfold epochLatchSign
    rcases hViol with ⟨hNoRetry, hNeNext⟩ | ⟨hNoRetry, hEpEq, hEvNone⟩
    · have hEpFalse : (reqEpoch == st.nextEpoch) = false := beq_false_of_ne hNeNext
      cases hLat : st.latchedLast with
      | none => simp [hEpFalse]
      | some triple =>
        rcases triple with ⟨ep0, m0, s0⟩
        have hHitFalse : (reqEpoch == ep0 && decide (msg = m0)) = false := by
          cases hH : (reqEpoch == ep0 && decide (msg = m0))
          · rfl
          · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hH
            rcases hH with ⟨rfl, rfl⟩
            exact False.elim (hNoRetry s0 hLat)
        dsimp only
        rw [hHitFalse]
        simp [hEpFalse]
    · subst hEpEq
      cases hLat : st.latchedLast with
      | none => simp [hEvNone]
      | some triple =>
        rcases triple with ⟨ep0, m0, s0⟩
        have hHitFalse : (st.nextEpoch == ep0 && decide (msg = m0)) = false := by
          cases hH : (st.nextEpoch == ep0 && decide (msg = m0))
          · rfl
          · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hH
            rcases hH with ⟨hEpEq0, rfl⟩
            exact False.elim (hNoRetry s0 (hEpEq0 ▸ hLat))
        dsimp only
        rw [hHitFalse]
        simp [hEvNone]

/-- Anti-narrowing completeness for `execEpochLatchTrace`: if fewer signatures are emitted than
    requests submitted, some step along `reqs` triggered an explicit `EpochLatchContractViolation`. -/
theorem execEpochLatchTrace_skip_implies_contract_violation
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind : Nat) :
    ∀ (reqs : List (Nat × List UInt8)) (st : EpochLatchState),
      (execEpochLatchTrace suite params sk optRand maxGrind st reqs).2.length < reqs.length →
      ∃ stMid reqEp reqMsg, (reqEp, reqMsg) ∈ reqs ∧
        EpochLatchContractViolation suite params sk optRand maxGrind stMid reqEp reqMsg
  | [], _, hLt => absurd hLt (Nat.not_lt_zero _)
  | (ep, msg) :: rest, st, hLt => by
    simp only [execEpochLatchTrace] at hLt
    cases hStep : epochLatchSign suite params sk optRand maxGrind st ep msg with
    | none =>
      exact ⟨st, ep, msg, List.mem_cons_self,
        (epochLatchSign_none_iff_violation suite params sk optRand maxGrind st ep msg).mp hStep⟩
    | some pair =>
      rcases pair with ⟨st', sig⟩
      rw [hStep] at hLt
      dsimp only at hLt
      simp only [List.length_cons] at hLt
      obtain ⟨stMid, rEp, rMsg, hMem, hViol⟩ :=
        execEpochLatchTrace_skip_implies_contract_violation suite params sk optRand maxGrind
          rest st' (Nat.lt_of_succ_lt_succ hLt)
      exact ⟨stMid, rEp, rMsg, List.mem_cons_of_mem _ hMem, hViol⟩

/-! ## 2. 256-Bit Base-4 Digit Bijection on `thHashMsg` (`extractBaseWDigits_4_128_take32_eq`) -/

private theorem byte_eq_of_four_crumbs {x y : Nat} (hx : x < 256) (hy : y < 256)
    (h3 : (x / 64) % 4 = (y / 64) % 4)
    (h2 : (x / 16) % 4 = (y / 16) % 4)
    (h1 : (x / 4) % 4 = (y / 4) % 4)
    (h0 : (x / 1) % 4 = (y / 1) % 4) :
    x = y := by
  omega

/-- **256-Bit Base-4 Digit Bijection (`extractBaseWDigits_4_128_take32_eq`)**:
    When `w = 4` and `ell1 = 128` (`corduroyCustody128Params`, `baggy128fParams`, `jortsPoseidon2Params`),
    the 128 base-4 digits extracted from any 64-byte `thHashMsg` output uniquely and injectively
    reconstruct all 32 bytes (`256` bits) of the first block `b0`! -/
theorem extractBaseWDigits_base4_prefix_injective (n : Nat) {hm1 hm2 : List UInt8}
    (hLen1 : n ≤ hm1.length) (hLen2 : n ≤ hm2.length)
    (hDigits : extractBaseWDigits 4 (4 * n) hm1 = extractBaseWDigits 4 (4 * n) hm2) :
    hm1.take n = hm2.take n := by
  have hCrumbAt : ∀ (hm : List UInt8), n ≤ hm.length → ∀ (i k : Nat), i < n → k < 4 →
      (extractBaseWDigits 4 (4 * n) hm).getD (4 * i + k) 0 =
      ((hm.getD i 0).toNat / (2 ^ ((3 - k) * 2))) % 4 := by
    intro hm hL i k hi hk
    rw [extractBaseWDigits_eq]
    have hIdxLt : 4 * i + k < 4 * n := by omega
    rw [list_getD_map_range (4 * n) _ 0 hIdxLt]
    simp only [show ¬ (4 < 2) by decide, ↓reduceIte]
    have hDiv : (4 * i + k) / 4 = i := by omega
    have hMod : (4 * i + k) % 4 = k := by omega
    rw [hDiv, hMod]
  have hByteEq : ∀ i : Nat, i < n → hm1.getD i 0 = hm2.getD i 0 := by
    intro i hi
    have hc : ∀ k : Nat, k < 4 →
        ((hm1.getD i 0).toNat / (2 ^ ((3 - k) * 2))) % 4 =
        ((hm2.getD i 0).toNat / (2 ^ ((3 - k) * 2))) % 4 := by
      intro k hk
      rw [← hCrumbAt hm1 hLen1 i k hi hk, ← hCrumbAt hm2 hLen2 i k hi hk, hDigits]
    have hc0 := hc 0 (by decide)
    have hc1 := hc 1 (by decide)
    have hc2 := hc 2 (by decide)
    have hc3 := hc 3 (by decide)
    simp only [show (3 - 0) * 2 = 6 by decide, show 2 ^ 6 = 64 by decide] at hc0
    simp only [show (3 - 1) * 2 = 4 by decide, show 2 ^ 4 = 16 by decide] at hc1
    simp only [show (3 - 2) * 2 = 2 by decide, show 2 ^ 2 = 4 by decide] at hc2
    simp only [show (3 - 3) * 2 = 0 by decide, show 2 ^ 0 = 1 by decide] at hc3
    have hNatEq := byte_eq_of_four_crumbs
      (hm1.getD i 0).toBitVec.isLt (hm2.getD i 0).toBitVec.isLt hc0 hc1 hc2 hc3
    exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hNatEq)
  apply List.ext_getElem
  · simp only [List.length_take, Nat.min_eq_left hLen1, Nat.min_eq_left hLen2]
  · intro i hi1 hi2
    have hiLt32 : i < n := by have := List.length_take_le n hm1; omega
    have hiLt1 : i < hm1.length := by omega
    have hiLt2 : i < hm2.length := by omega
    rw [List.getElem_take, List.getElem_take,
        ← list_getD_eq_getElem hm1 0 hiLt1,
        ← list_getD_eq_getElem hm2 0 hiLt2]
    exact hByteEq i hiLt32

theorem extractBaseWDigits_4_128_take32_eq {hm1 hm2 : List UInt8}
    (hLen1 : hm1.length = 64) (hLen2 : hm2.length = 64)
    (hDigits : extractBaseWDigits 4 128 hm1 = extractBaseWDigits 4 128 hm2) :
    hm1.take 32 = hm2.take 32 :=
  extractBaseWDigits_base4_prefix_injective 32 (by omega) (by omega) hDigits

/-- Any number of complete bytes is recovered injectively from MSB-first base-16 digits. -/
theorem extractBaseWDigits_base16_prefix_injective (n : Nat) {a b : List UInt8}
    (ha : n ≤ a.length) (hb : n ≤ b.length)
    (hd : extractBaseWDigits 16 (2 * n) a = extractBaseWDigits 16 (2 * n) b) :
    a.take n = b.take n := by
  have digitAt : ∀ (bs : List UInt8) (i k : Nat), i < n → k < 2 →
      (extractBaseWDigits 16 (2 * n) bs).getD (2 * i + k) 0 =
      (bs.getD i 0).toNat / 2 ^ ((1 - k) * 4) % 16 := by
    intro bs i k hi hk
    rw [extractBaseWDigits_eq, list_getD_map_range (2 * n) _ 0 (by omega)]
    have hdiv : (2 * i + k) / 2 = i := by omega
    have hmod : (2 * i + k) % 2 = k := by omega
    simp only [show ¬ (16 < 2) by decide, show ¬ (16 = 4) by decide,
      ↓reduceIte, show Nat.log2 16 = 4 by decide, show 8 / 4 = 2 by decide,
      hdiv, hmod, show 2 - 1 = 1 by decide]
  apply List.ext_getElem
  · simp only [List.length_take, Nat.min_eq_left ha, Nat.min_eq_left hb]
  · intro i hi hi'
    have hin : i < n := by have := List.length_take_le n a; omega
    have hc : ∀ k, k < 2 →
        (a.getD i 0).toNat / 2 ^ ((1 - k) * 4) % 16 =
        (b.getD i 0).toNat / 2 ^ ((1 - k) * 4) % 16 := by
      intro k hk
      rw [← digitAt a i k hin hk, ← digitAt b i k hin hk, hd]
    have hc0 := hc 0 (by decide)
    have hc1 := hc 1 (by decide)
    have hna := (a.getD i 0).toBitVec.isLt
    have hnb := (b.getD i 0).toBitVec.isLt
    change (a.getD i 0).toNat < 256 at hna
    change (b.getD i 0).toNat < 256 at hnb
    have he : (a.getD i 0).toNat = (b.getD i 0).toNat := by
      simp only [Nat.sub_zero, Nat.one_mul, show 2 ^ 4 = 16 by decide,
        Nat.sub_self, Nat.zero_mul, Nat.pow_zero, Nat.div_one] at hc0 hc1
      omega
    rw [List.getElem_take, List.getElem_take,
      ← list_getD_eq_getElem a 0 (by omega), ← list_getD_eq_getElem b 0 (by omega)]
    exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq he)

/-- Both production radices preserve every complete byte, for arbitrary input length. -/
theorem extractBaseWDigits_production_prefix_injective (w n : Nat) {a b : List UInt8}
    (hw : w = 4 ∨ w = 16) (ha : n ≤ a.length) (hb : n ≤ b.length)
    (hd : extractBaseWDigits w ((8 / Nat.log2 w) * n) a =
      extractBaseWDigits w ((8 / Nat.log2 w) * n) b) : a.take n = b.take n := by
  rcases hw with rfl | rfl
  · exact extractBaseWDigits_base4_prefix_injective n ha hb hd
  · exact extractBaseWDigits_base16_prefix_injective n ha hb hd

/-! ## 3. Constructive Unqueried WOTS+C Endpoint Inversion & Multi-Layer Hypertree Extractor -/

/-- Find the first coordinate `r` in `digits` with `digits[r] < maxVal` (`0 Classical`). -/
def findDigitLt (maxVal : Nat) : List Nat → Option Nat
  | [] => none
  | d :: ds => if d < maxVal then some 0 else (findDigitLt maxVal ds).map (· + 1)

private theorem sumDigits_ge_mul_of_all_ge (bound : Nat) :
    ∀ (ds : List Nat), (∀ d ∈ ds, bound ≤ d) → bound * ds.length ≤ sumDigits ds
  | [], _ => by simp [sumDigits_nil]
  | d :: ds, hAll => by
    rw [sumDigits_cons, List.length_cons, Nat.mul_succ]
    have hd : bound ≤ d := hAll d (.head ds)
    have hRest := sumDigits_ge_mul_of_all_ge bound ds (fun x hx => hAll x (.tail d hx))
    omega

private theorem findDigitLt_none_all_ge (maxVal : Nat) :
    ∀ (ds : List Nat), findDigitLt maxVal ds = none → ∀ d ∈ ds, maxVal ≤ d
  | [], _, _, hMem => by cases hMem
  | d :: ds, hNone, x, hMem => by
    simp only [findDigitLt] at hNone
    by_cases hlt : d < maxVal
    · simp [hlt] at hNone
    · simp only [hlt, ↓reduceIte, Option.map_eq_none_iff] at hNone
      rcases List.mem_cons.mp hMem with rfl | hTail
      · omega
      · exact findDigitLt_none_all_ge maxVal ds hNone x hTail

theorem findDigitLt_sound (maxVal : Nat) :
    ∀ {ds : List Nat} {r : Nat},
      findDigitLt maxVal ds = some r →
      ∃ (hr : r < ds.length), ds[r]'hr < maxVal
  | [], _, h => by cases h
  | d :: ds, r, h => by
    simp only [findDigitLt] at h
    by_cases hlt : d < maxVal
    · simp only [hlt, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨Nat.zero_lt_succ _, hlt⟩
    · simp only [hlt, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨r', hr'Some, rfl⟩ := h
      obtain ⟨hr'Lt, hr'Val⟩ := findDigitLt_sound maxVal hr'Some
      exact ⟨Nat.succ_lt_succ hr'Lt, hr'Val⟩

/-- **Constructive Unqueried WOTS+C Forgery Extractor (`extractUnqueriedWotsBreak`)**:
    If an adversary produces `(digits, forgedChains)` recovering `computeWotsPk suite params sk layer tree kp`
    for an **unqueried** WOTS+C keypair (where only the chain endpoints at `step = w - 1` were ever
    committed in the Merkle tree, and `targetSum < (w - 1) * ell1`), constructively extracts
    `PSum (WotsBackwardInversionWitness suite sk.pkSeed) (HashCollisionWitness suite.rawHash)`. -/
def extractUnqueriedWotsBreak
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digits : List Nat) (forgedChains : List (List UInt8))
    (hValid : checkTargetSum params.w params.ell1 params.targetSum digits = true)
    (hStrictTarget : params.targetSum < (params.w - 1) * params.ell1)
    (hSamePk : recoverWotsPkFromSig suite params sk.pkSeed layer tree kp digits forgedChains =
               computeWotsPk suite params sk layer tree kp) :
    PSum (WotsBackwardInversionWitness suite sk.pkSeed) (HashCollisionWitness suite.rawHash) :=
  let endF := recoverWotsEndpoints suite params sk.pkSeed layer tree kp digits forgedChains
  let endH := (List.range params.ell1).map fun r =>
    wotsChainSteps suite sk.pkSeed layer tree kp r 0 (params.w - 1)
      (wotsSecretBase suite sk layer tree kp r)
  if hEndNe : endF ≠ endH then
    have hTlEq : thCall suite tagThTl sk.pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩ endF =
                 thCall suite tagThTl sk.pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩ endH := by
      rw [← thTweakTl_eq, ← thTweakTl_eq, ← recoverWotsPkFromSig_eq, ← computeWotsPk_eq]
      exact hSamePk
    match thCall_binds_or_collision suite hTlEq with
    | .inl ⟨_, _, _, hArgs⟩ => False.elim (hEndNe hArgs)
    | .inr col => .inr col
  else
    have hEndEq : endF = endH := Decidable.of_not_not hEndNe
    match hFind : findDigitLt (params.w - 1) digits with
    | none =>
      False.elim (by
        obtain ⟨hLen, _, hSum⟩ := (checkTargetSum_iff _ _ _ digits).mp hValid
        have hAllGe := findDigitLt_none_all_ge (params.w - 1) digits hFind
        have hGe := sumDigits_ge_mul_of_all_ge (params.w - 1) digits hAllGe
        rw [hLen, hSum] at hGe
        omega)
    | some r =>
      have hRLt : r < params.ell1 ∧ digits.getD r 0 < params.w - 1 := by
        obtain ⟨hrLen, hrVal⟩ := findDigitLt_sound (params.w - 1) hFind
        obtain ⟨hLen, _, _⟩ := (checkTargetSum_iff _ _ _ digits).mp hValid
        rw [list_getD_eq_getElem digits 0 hrLen]
        exact ⟨hLen ▸ hrLen, hrVal⟩
      let dr := digits.getD r 0
      let gap := (params.w - 1) - dr
      have hGapGe1 : 1 ≤ gap := by dsimp [gap, dr]; omega
      have hGapSplit : gap = (gap - 1) + 1 := (Nat.sub_add_cancel hGapGe1).symm
      let preStep := dr + (gap - 1)
      let sigR := forgedChains.getD r []
      let preVal := wotsChainSteps suite sk.pkSeed layer tree kp r dr (gap - 1) sigR
      let endpointVal := endH.getD r []
      .inl
        { layer := layer, tree := tree, kp := kp, chain := r
          step := preStep, revealedStep := params.w - 1
          step_lt := by
            have hDrLt := hRLt.2
            dsimp [preStep, gap, dr]
            omega
          preimage := preVal
          revealedVal := endpointVal
          invertsChain := by
            have hCompose := wotsChainSteps_add suite sk.pkSeed layer tree kp r (gap - 1) 1 dr sigR
            rw [← hGapSplit] at hCompose
            have hStep1 : thChainF suite sk.pkSeed
                ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat preStep⟩ preVal =
                wotsChainSteps suite sk.pkSeed layer tree kp r dr gap sigR := by
              have hSym := hCompose.symm
              rw [wotsChainSteps_succ, wotsChainSteps_zero] at hSym
              exact hSym.symm
            have hEndFR : endF.getD r [] = wotsChainSteps suite sk.pkSeed layer tree kp r dr gap sigR := by
              dsimp [endF]
              rw [recoverWotsEndpoints_eq]
              exact list_getD_map_range params.ell1 _ [] hRLt.1
            rw [hStep1, ← hEndFR, hEndEq] }

/-- Constructive `Type`-valued FORS one-way leaf inversion witness on an unrevealed leaf `(treeIdx, kpIdx, globalU)`. -/
structure ForsPreimageWitness (suite : TweakableHashSuite) (sk : PqSecretKey)
    (revealedFors : List (UInt64 × Nat × Nat)) where
  treeIdx     : UInt64
  kpIdx       : Nat
  globalU     : Nat
  forgedSec   : List UInt8
  unrevealed  : (treeIdx, kpIdx, globalU) ∉ revealedFors
  invertsLeaf : forsLeafHashFromSecret suite sk.pkSeed treeIdx kpIdx globalU forgedSec =
                forsLeafFn suite sk treeIdx kpIdx globalU

/-- Explicit stateless FORS subset-cover witness: occurs ONLY when all `k = params.forsTrees`
    FORS indices of `(msg*, rRand*)` were already opened by prior signing queries at `(treeIdx, kpIdx)`. -/
structure ForsSubsetCoverWitness (params : PqHashParams) (treeIdx : UInt64) (kpIdx : Nat)
    (hmsg0 : List UInt8) (revealedFors : List (UInt64 × Nat × Nat)) where
  allCovered : ∀ j, j < params.forsTrees →
    (treeIdx, kpIdx, j * (2 ^ params.forsHeight) +
      (deriveForsIndices params.forsTrees params.forsHeight hmsg0).getD j 0) ∈ revealedFors

/-- Whenever ≥ 1 FORS tree of `(msg*, rRand*)` lands on an unopened leaf, `ForsSubsetCoverWitness` is impossible! -/
theorem fors_uncovered_excludes_subset_cover
    {params : PqHashParams} {treeIdx : UInt64} {kpIdx : Nat}
    {hmsg0 : List UInt8} {revealedFors : List (UInt64 × Nat × Nat)}
    {j : Nat} (hj : j < params.forsTrees)
    (hFreshLeaf : (treeIdx, kpIdx, j * (2 ^ params.forsHeight) +
      (deriveForsIndices params.forsTrees params.forsHeight hmsg0).getD j 0) ∉ revealedFors) :
    ForsSubsetCoverWitness params treeIdx kpIdx hmsg0 revealedFors → False :=
  fun w => hFreshLeaf (w.allCovered j hj)

/-- Record of an honestly signed WOTS+C call `(honestLayerRand, honestCurRoot, honestCtr, honestChains)`
    at `(layerIdx, treeIdx, kpIdx)` (`none` if never queried). -/
abbrev QueriedWotsOracle := UInt32 → UInt64 → Nat → Option (List UInt8 × List UInt8 × Nat × List (List UInt8))

/-- Soundness invariant on `QueriedWotsOracle`: every recorded entry was validly signed under `sk`
    on `honestCurRoot` (so `recoverWotsPkFromSig` equals `computeWotsPk`). -/
def ValidQueriedWotsOracle (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot : List UInt8) (qOracle : QueriedWotsOracle) : Prop :=
  ∀ (layer : UInt32) (tree : UInt64) (kp : Nat) (hRand hCurRoot : List UInt8) (hCtr : Nat) (hChains : List (List UInt8)),
    qOracle layer tree kp = some (hRand, hCurRoot, hCtr, hChains) →
    let hmsg := thHashMsg suite hRand sk.pkSeed pkRoot hCurRoot layer tree (UInt32.ofNat kp) hCtr
    let digits := extractBaseWDigits params.w params.ell1 hmsg
    hCurRoot = (if layer.toNat = 0 then hCurRoot else computeXmssSubtreeRoot suite params sk (UInt32.ofNat (layer.toNat - 1)) (UInt64.ofNat kp)) ∧
    checkTargetSum params.w params.ell1 params.targetSum digits = true ∧
    recoverWotsPkFromSig suite params sk.pkSeed layer tree kp digits hChains =
      computeWotsPk suite params sk layer tree kp

/-- Single-layer WOTS+C + XMSS Merkle extraction at `(layerIdx, treeIdx, kpIdx)` when `curRoot ≠ honestCurRoot`
    yet `walkMerkleAuthPath ... wotsPk_forged authPath = some (computeXmssSubtreeRoot suite params sk layerU32 treeIdx)`! -/
def extractSingleLayerDivergence
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (pkRoot layer0Rand curRoot honestCurRoot : List UInt8)
    (layerIdx globalIdx : Nat) (lsig : LayerXmssSig)
    (qOracle : QueriedWotsOracle)
    (hParams4_128 : params.w = 4 ∧ params.ell1 = 128)
    (hSubLt : globalIdx % (2 ^ params.subtreeHeight) < 2 ^ params.subtreeHeight)
    (hDiffRoot : curRoot ≠ honestCurRoot)
    (hValidTsw : checkTargetSum params.w params.ell1 params.targetSum
      (extractBaseWDigits params.w params.ell1
        (thHashMsg suite layer0Rand sk.pkSeed pkRoot curRoot (UInt32.ofNat layerIdx)
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) lsig.tswCtr)) = true)
    (hWalkEq : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
        (globalIdx % 2 ^ params.subtreeHeight)
        (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat layerIdx)
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (globalIdx % 2 ^ params.subtreeHeight)
          (extractBaseWDigits params.w params.ell1
            (thHashMsg suite layer0Rand sk.pkSeed pkRoot curRoot (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) lsig.tswCtr))
          lsig.wotsChains)
        lsig.authPath =
      some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))))
    (hValidOracle : ∀ hRand hCtr hChains,
      qOracle (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight) = some (hRand, honestCurRoot, hCtr, hChains) →
      let hmH := thHashMsg suite hRand sk.pkSeed pkRoot honestCurRoot (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) hCtr
      let digH := extractBaseWDigits params.w params.ell1 hmH
      checkTargetSum params.w params.ell1 params.targetSum digH = true ∧
      recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight) digH hChains =
      computeWotsPk suite params sk (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight))
    (hOracleRoot : ∀ hRand hRoot hCtr hChains,
      qOracle (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
      hRoot = honestCurRoot) :
    PSum (WotsBackwardInversionWitness suite sk.pkSeed) (HashCollisionWitness suite.rawHash) :=
  let subLeaves := 2 ^ params.subtreeHeight
  let kpIdx := globalIdx % subLeaves
  let kpU32 := UInt32.ofNat kpIdx
  let treeIdx := UInt64.ofNat (globalIdx / subLeaves)
  let layerU32 := UInt32.ofNat layerIdx
  let hmF := thHashMsg suite layer0Rand sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 lsig.tswCtr
  let digF := extractBaseWDigits params.w params.ell1 hmF
  let wotsPkF := recoverWotsPkFromSig suite params sk.pkSeed layerU32 treeIdx kpIdx digF lsig.wotsChains
  let wotsPkH := computeWotsPk suite params sk layerU32 treeIdx kpIdx
  let pathH := buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
    (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx
  have hWalkH : walkMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree params.subtreeHeight 0 kpIdx wotsPkH pathH =
      some (computeXmssSubtreeRoot suite params sk layerU32 treeIdx) := by
    have hw := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
      (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx hSubLt
    simp only [Nat.zero_mul, Nat.zero_add] at hw
    rw [computeXmssSubtreeRoot_eq]
    exact hw
  if hMerkleDiff : wotsPkF ≠ wotsPkH ∨ lsig.authPath ≠ pathH then
    .inr (walkMerkleAuthPath_collision_extract suite sk.pkSeed layerU32 treeIdx .tree
      params.subtreeHeight 0 kpIdx hMerkleDiff hWalkEq hWalkH)
  else
    have hWotsEq : wotsPkF = wotsPkH := Decidable.of_not_not (fun hn => hMerkleDiff (.inl hn))
    have hStrictT : params.targetSum < (params.w - 1) * params.ell1 := by
      rw [PqHashParams.targetSum_eq, hParams4_128.1, hParams4_128.2]
      decide
    match hQ : qOracle layerU32 treeIdx kpIdx with
    | none =>
      extractUnqueriedWotsBreak suite params sk layerU32 treeIdx kpIdx digF lsig.wotsChains
        hValidTsw hStrictT hWotsEq
    | some (hRand, hRoot, hCtr, hChains) =>
      have hRootEq : hRoot = honestCurRoot := hOracleRoot hRand hRoot hCtr hChains hQ
      have hQ' : qOracle layerU32 treeIdx kpIdx = some (hRand, honestCurRoot, hCtr, hChains) :=
        hRootEq ▸ hQ
      let hmH := thHashMsg suite hRand sk.pkSeed pkRoot honestCurRoot layerU32 treeIdx kpU32 hCtr
      let digH := extractBaseWDigits params.w params.ell1 hmH
      have hHProps := hValidOracle hRand hCtr hChains hQ'
      if hDigNe : digH ≠ digF then
        extractPqHashForgery suite params sk.pkSeed layerU32 treeIdx kpIdx digH digF hChains lsig.wotsChains
          hHProps.1 hValidTsw hDigNe (hWotsEq.trans hHProps.2.symm)
      else
        have hDigEq : digF = digH := (Decidable.of_not_not hDigNe).symm
        have hDigEq4 : extractBaseWDigits 4 128 hmF = extractBaseWDigits 4 128 hmH := by
          simpa [digF, digH, hParams4_128.1, hParams4_128.2] using hDigEq
        have hTakeEq : hmF.take 32 = hmH.take 32 :=
          extractBaseWDigits_4_128_take32_eq (thHashMsg_length _ _ _ _ _ _ _ _ _)
            (thHashMsg_length _ _ _ _ _ _ _ _ _) hDigEq4
        have hB0Eq :
            thCall suite tagHMsg sk.pkSeed ⟨layerU32, treeIdx, .wotsHash, kpU32, 0, UInt32.ofNat lsig.tswCtr⟩
              [layer0Rand, pkRoot, curRoot, be 4 lsig.tswCtr] =
            thCall suite tagHMsg sk.pkSeed ⟨layerU32, treeIdx, .wotsHash, kpU32, 0, UInt32.ofNat hCtr⟩
              [hRand, pkRoot, honestCurRoot, be 4 hCtr] := by
          have hT1 : hmF.take 32 = thCall suite tagHMsg sk.pkSeed
              ⟨layerU32, treeIdx, .wotsHash, kpU32, 0, UInt32.ofNat lsig.tswCtr⟩
              [layer0Rand, pkRoot, curRoot, be 4 lsig.tswCtr] := by
            dsimp [hmF]; rw [thHashMsg_eq, List.take_left' (thCall_length _ _ _ _ _)]
          have hT2 : hmH.take 32 = thCall suite tagHMsg sk.pkSeed
              ⟨layerU32, treeIdx, .wotsHash, kpU32, 0, UInt32.ofNat hCtr⟩
              [hRand, pkRoot, honestCurRoot, be 4 hCtr] := by
            dsimp [hmH]; rw [thHashMsg_eq, List.take_left' (thCall_length _ _ _ _ _)]
          exact hT1.symm.trans (hTakeEq.trans hT2)
        match thCall_binds_or_collision suite hB0Eq with
        | .inl ⟨_, _, _, hArgsEq⟩ =>
          False.elim (by
            simp only [List.cons.injEq] at hArgsEq
            exact hDiffRoot hArgsEq.2.2.1)
        | .inr col => .inr col

/-- **Multi-Layer Hypertree Constructive `PSum` Extractor (`extractHypertreeLayersBreak`)**:
    Walks from `layerIdx` across all remaining `layerSigs` up to `topRoot = computeXmssSubtreeRoot ...`,
    pinpointing the exact layer where `curRoot ≠ honestCurRoot` merges into the honest XMSS tree! -/
def extractHypertreeLayersBreak
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (pkRoot : List UInt8) (qOracle : QueriedWotsOracle)
    (hParams4_128 : params.w = 4 ∧ params.ell1 = 128) :
    ∀ (layerSigs : List LayerXmssSig) (layerIdx globalIdx : Nat)
      (layer0Rand curRoot honestCurRoot : List UInt8),
      curRoot ≠ honestCurRoot →
      verifyHypertreeLayers suite params sk.pkSeed pkRoot layer0Rand layerIdx globalIdx curRoot layerSigs =
        some (if layerSigs.isEmpty then honestCurRoot
              else computeXmssSubtreeRoot suite params sk
                (UInt32.ofNat (layerIdx + layerSigs.length - 1))
                (UInt64.ofNat (globalIdx / 2 ^ (layerSigs.length * params.subtreeHeight)))) →
      (∀ (l : Nat) (g : Nat) (hRoot0 : List UInt8),
        (l = layerIdx ∧ g = globalIdx ∧ hRoot0 = honestCurRoot) ∨
        (layerIdx < l ∧ hRoot0 = computeXmssSubtreeRoot suite params sk (UInt32.ofNat (l - 1)) (UInt64.ofNat g)) →
        (∀ hRand hCtr hChains,
          qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) =
            some (hRand, hRoot0, hCtr, hChains) →
          let hmH := thHashMsg suite hRand sk.pkSeed pkRoot hRoot0 (UInt32.ofNat l)
            (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) hCtr
          let digH := extractBaseWDigits params.w params.ell1 hmH
          checkTargetSum params.w params.ell1 params.targetSum digH = true ∧
          recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat l)
            (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) digH hChains =
          computeWotsPk suite params sk (UInt32.ofNat l)
            (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight)) ∧
        (∀ hRand hR hCtr hChains,
          qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) =
            some (hRand, hR, hCtr, hChains) → hR = hRoot0)) →
      PSum (WotsBackwardInversionWitness suite sk.pkSeed) (HashCollisionWitness suite.rawHash)
  | [], layerIdx, globalIdx, layer0Rand, curRoot, honestCurRoot, hDiff, hVer, _ => by
    rw [verifyHypertreeLayers_nil] at hVer
    simp only [List.isEmpty_nil, ↓reduceIte, Option.some.injEq] at hVer
    exact False.elim (hDiff hVer)
  | lsig :: rest, layerIdx, globalIdx, layer0Rand, curRoot, honestCurRoot, hDiff, hVer, hOrc =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let kpU32 := UInt32.ofNat kpIdx
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    let hmsg := thHashMsg suite layer0Rand sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 lsig.tswCtr
    let digits := extractBaseWDigits params.w params.ell1 hmsg
    match hTsw : checkTargetSum params.w params.ell1 params.targetSum digits with
    | false =>
      False.elim (by
        rw [verifyHypertreeLayers_cons] at hVer
        dsimp only at hVer
        dsimp only [digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves] at hTsw
        rw [hTsw] at hVer
        simp at hVer)
    | true =>
      if hCLen : lsig.wotsChains.length ≠ params.ell1 then
        False.elim (by
          rw [verifyHypertreeLayers_cons] at hVer
          dsimp only at hVer
          dsimp only [digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves] at hTsw
          rw [hTsw] at hVer
          simp [hCLen] at hVer)
      else
        have hCLenEq : lsig.wotsChains.length = params.ell1 := Decidable.of_not_not hCLen
        let wotsPk := recoverWotsPkFromSig suite params sk.pkSeed layerU32 treeIdx kpIdx digits lsig.wotsChains
        match hWalk : walkMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree params.subtreeHeight 0 kpIdx wotsPk lsig.authPath with
        | none =>
          False.elim (by
            rw [verifyHypertreeLayers_cons] at hVer
            dsimp only at hVer
            dsimp only [wotsPk, digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves] at hTsw hWalk
            rw [hTsw, hWalk] at hVer
            simp [hCLenEq] at hVer)
        | some nextSubtreeRoot =>
          let honestNext := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
          if hNextEq : nextSubtreeRoot = honestNext then
            have hSubLt : globalIdx % (2 ^ params.subtreeHeight) < 2 ^ params.subtreeHeight :=
              Nat.mod_lt _ (Nat.two_pow_pos _)
            have hHere := hOrc layerIdx globalIdx honestCurRoot (.inl ⟨rfl, rfl, rfl⟩)
            extractSingleLayerDivergence suite params sk pkRoot layer0Rand curRoot honestCurRoot
              layerIdx globalIdx lsig qOracle hParams4_128 hSubLt hDiff hTsw
              (by
                dsimp only [wotsPk, digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves, honestNext] at hWalk hNextEq
                rw [← hNextEq]
                exact hWalk)
              hHere.1 hHere.2
          else
            have hRestVer :
                verifyHypertreeLayers suite params sk.pkSeed pkRoot [] (layerIdx + 1) treeIdxNat nextSubtreeRoot rest =
                some (if rest.isEmpty then honestNext
                      else computeXmssSubtreeRoot suite params sk
                        (UInt32.ofNat ((layerIdx + 1) + rest.length - 1))
                        (UInt64.ofNat (treeIdxNat / 2 ^ (rest.length * params.subtreeHeight)))) := by
              rw [verifyHypertreeLayers_cons] at hVer
              dsimp only at hVer
              have hTsw' := hTsw
              have hWalk' := hWalk
              dsimp only [wotsPk, digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves] at hTsw' hWalk'
              rw [hTsw'] at hVer
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                         hCLenEq, ne_eq, not_true_eq_false] at hVer
              rw [hWalk'] at hVer
              dsimp only [treeIdxNat, subLeaves, honestNext, layerU32, treeIdx]
              cases rest with
              | nil =>
                simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_singleton,
                           Nat.add_sub_cancel, Nat.one_mul, List.isEmpty_nil] at hVer ⊢
                exact hVer
              | cons r0 rs =>
                simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hVer ⊢
                have hIdxEq : (layerIdx + 1) + (rs.length + 1) - 1 = layerIdx + (rs.length + 1 + 1) - 1 := by omega
                have hDivEq : (globalIdx / 2 ^ params.subtreeHeight) / 2 ^ ((rs.length + 1) * params.subtreeHeight) =
                    globalIdx / 2 ^ ((rs.length + 1 + 1) * params.subtreeHeight) := by
                  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add,
                      show params.subtreeHeight + (rs.length + 1) * params.subtreeHeight =
                           (rs.length + 1 + 1) * params.subtreeHeight by
                        rw [Nat.succ_mul (rs.length + 1), Nat.add_comm]]
                rw [hIdxEq, hDivEq]
                exact hVer
            extractHypertreeLayersBreak suite params sk pkRoot qOracle hParams4_128
              rest (layerIdx + 1) treeIdxNat [] nextSubtreeRoot honestNext hNextEq hRestVer
              (fun l g hRoot0 hCond => by
                apply hOrc l g hRoot0
                rcases hCond with ⟨rfl, rfl, rfl⟩ | ⟨hGt, hR⟩
                · exact .inr ⟨by omega, by dsimp [honestNext, layerU32, treeIdx, treeIdxNat, subLeaves]⟩
                · exact .inr ⟨by omega, hR⟩)

/-! ## 4. Constructive FORS Tree Extractor & Unified Top-Level `extractFullHypertreeForgery` -/

private theorem list_range_succ_shift_local {α : Type} (rem : Nat) (f : Nat → α) :
    (List.range (rem + 1)).map f = f 0 :: (List.range rem).map (fun k => f (k + 1)) := by
  induction rem generalizing f with
  | zero => simp
  | succ r ih => rw [List.range_succ, List.map_append, ih f, List.range_succ, List.map_append]; simp

/-- Walk the `rem` FORS trees starting at tree index `j`:
    if `recoverForsTreeRoots` produces the honest FORS root list, constructively extracts either
    a `ForsPreimageWitness` (at an unrevealed leaf), a `HashCollisionWitness` (at a Merkle node),
    or a proof that all `rem` FORS indices in `[j, j + rem)` belong to `revealedFors`! -/
def extractForsTreeRootsWalk
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat) (openings : List ForsTreeOpening)
    (revealedFors : List (UInt64 × Nat × Nat))
    (hIdxs : idxs.length = params.forsTrees ∧ ∀ idx ∈ idxs, idx < 2 ^ params.forsHeight) :
    ∀ (rem j : Nat) (rootsF : List (List UInt8)),
      j + rem ≤ params.forsTrees →
      recoverForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs openings j rem = some rootsF →
      rootsF = ((List.range rem).map fun off =>
        computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree (forsLeafFn suite sk tree0 kp0) params.forsHeight (j + off)) →
      PSum (ForsPreimageWitness suite sk revealedFors)
           (PSum (HashCollisionWitness suite.rawHash)
                 (∀ off, off < rem → (tree0, kp0, (j + off) * (2 ^ params.forsHeight) + idxs.getD (j + off) 0) ∈ revealedFors))
  | 0, _, _, _, _, _ => .inr (.inr (fun _ hLt => by omega))
  | rem + 1, j, rootsF, hBound, hRec, hEqRoots =>
    let idxJ := idxs.getD j 0
    let op := openings.getD j ⟨[], []⟩
    let globalU := j * (2 ^ params.forsHeight) + idxJ
    let leafHF := forsLeafHashFromSecret suite sk.pkSeed tree0 kp0 globalU op.secretVal
    let leafFn := forsLeafFn suite sk tree0 kp0
    let leafHH := leafFn globalU
    let pathH := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j idxJ
    match hWalkF : walkMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree params.forsHeight j idxJ leafHF op.authPath with
    | none =>
      False.elim (by
        rw [recoverForsTreeRoots_succ] at hRec
        dsimp only at hRec
        dsimp only [leafHF, globalU, op, idxJ] at hWalkF
        rw [hWalkF] at hRec
        cases hRec)
    | some rJ =>
      match hRestF : recoverForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs openings (j + 1) rem with
      | none =>
        False.elim (by
          rw [recoverForsTreeRoots_succ] at hRec
          dsimp only at hRec
          dsimp only [leafHF, globalU, op, idxJ] at hWalkF
          rw [hWalkF, hRestF] at hRec
          cases hRec)
      | some rsF =>
        have hConsEq : rJ :: rsF =
            computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j ::
            ((List.range rem).map fun off =>
              computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight (j + 1 + off)) := by
          rw [recoverForsTreeRoots_succ] at hRec
          dsimp only at hRec
          have hWalkF' := hWalkF
          dsimp only [leafHF, globalU, op, idxJ] at hWalkF'
          rw [hWalkF', hRestF] at hRec
          injection hRec with hCons
          have hR := hCons.trans hEqRoots
          rw [list_range_succ_shift_local] at hR
          simp only [Nat.add_zero, List.cons.injEq] at hR
          refine List.cons_eq_cons.mpr ⟨hR.1, ?_⟩
          refine hR.2.trans (List.map_congr_left ?_)
          intro off _
          have hAdd : j + (off + 1) = j + 1 + off := by omega
          rw [hAdd]
        have hrJ : rJ = computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j :=
          (List.cons.inj hConsEq).1
        have hrsF : rsF = ((List.range rem).map fun off =>
            computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight ((j + 1) + off)) :=
          (List.cons.inj hConsEq).2
        have hIdxLt : idxJ < 2 ^ params.forsHeight := by
          have hjLt : j < idxs.length := by omega
          dsimp [idxJ]
          rw [list_getD_eq_getElem idxs 0 hjLt]
          exact hIdxs.2 _ (List.getElem_mem hjLt)
        have hWalkH : walkMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree params.forsHeight j idxJ leafHH pathH =
            some (computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j) :=
          walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j idxJ hIdxLt
        if hMerkleDiff : leafHF ≠ leafHH ∨ op.authPath ≠ pathH then
          .inr (.inl (walkMerkleAuthPath_collision_extract suite sk.pkSeed 0 tree0 .forsTree
            params.forsHeight j idxJ hMerkleDiff (hrJ ▸ hWalkF) hWalkH))
        else
          have hLeafEq : leafHF = leafHH := Decidable.of_not_not (fun hn => hMerkleDiff (.inl hn))
          if hUnrev : (tree0, kp0, globalU) ∉ revealedFors then
            .inl { treeIdx := tree0, kpIdx := kp0, globalU := globalU
                   forgedSec := op.secretVal, unrevealed := hUnrev, invertsLeaf := hLeafEq }
          else
            have hRevJ : (tree0, kp0, globalU) ∈ revealedFors := Decidable.of_not_not hUnrev
            match extractForsTreeRootsWalk suite params sk tree0 kp0 idxs openings revealedFors hIdxs
                    rem (j + 1) rsF (by omega) hRestF hrsF with
            | .inl pre => .inl pre
            | .inr (.inl col) => .inr (.inl col)
            | .inr (.inr hAllRest) =>
              .inr (.inr (fun off hOffLt => by
                cases off with
                | zero => simpa [globalU, idxJ] using hRevJ
                | succ off' =>
                  have hStep := hAllRest off' (by omega)
                  have hAdd : (j + 1) + off' = j + (off' + 1) := by omega
                  rwa [hAdd] at hStep))

/-- Constructive FORS public-key opening extractor (`extractForsBreak`):
    given `recoverForsPk ... openings = some (computeForsPk suite params sk tree0 kp0)`,
    extracts `ForsPreimageWitness ⊕ HashCollisionWitness ⊕ ForsSubsetCoverWitness` (`0 Classical`). -/
def extractForsBreak
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 : Nat) (hmsg0 : List UInt8) (openings : List ForsTreeOpening)
    (revealedFors : List (UInt64 × Nat × Nat))
    (hRecEq : recoverForsPk suite params sk.pkSeed tree0 kp0 hmsg0 openings =
              some (computeForsPk suite params sk tree0 kp0)) :
    PSum (ForsPreimageWitness suite sk revealedFors)
         (PSum (HashCollisionWitness suite.rawHash)
               (ForsSubsetCoverWitness params tree0 kp0 hmsg0 revealedFors)) :=
  if hLenNe : openings.length ≠ params.forsTrees then
    False.elim (by rw [recoverForsPk_eq] at hRecEq; simp [hLenNe] at hRecEq)
  else
    let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg0
    match hRootsF : recoverForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs openings 0 params.forsTrees with
    | none =>
      False.elim (by
        have hLenEq := Decidable.of_not_not hLenNe
        rw [recoverForsPk_eq] at hRecEq
        simp [hLenEq, idxs, hRootsF] at hRecEq)
    | some rootsF =>
      let rootsH := (List.range params.forsTrees).map fun j =>
        computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree (forsLeafFn suite sk tree0 kp0) params.forsHeight j
      if hRootsNe : rootsF ≠ rootsH then
        have hTlEq : thCall suite tagThTl sk.pkSeed ⟨0, tree0, .forsRoots, UInt32.ofNat kp0, 0, 0⟩ rootsF =
                     thCall suite tagThTl sk.pkSeed ⟨0, tree0, .forsRoots, UInt32.ofNat kp0, 0, 0⟩ rootsH := by
          have hLenEq := Decidable.of_not_not hLenNe
          rw [recoverForsPk_eq, computeForsPk_eq] at hRecEq
          simp only [hLenEq, ne_eq, not_true_eq_false, ↓reduceIte, idxs, hRootsF, Option.some.injEq] at hRecEq
          rw [← thTweakTl_eq, ← thTweakTl_eq]
          exact hRecEq
        match thCall_binds_or_collision suite hTlEq with
        | .inl ⟨_, _, _, hArgsEq⟩ => False.elim (hRootsNe hArgsEq)
        | .inr col => .inr (.inl col)
      else
        have hRootsEq : rootsF = ((List.range params.forsTrees).map fun off =>
            computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree (forsLeafFn suite sk tree0 kp0) params.forsHeight (0 + off)) := by
          simpa [rootsH] using (Decidable.of_not_not hRootsNe)
        match extractForsTreeRootsWalk suite params sk tree0 kp0 idxs openings revealedFors
                (deriveForsIndices_bounds params.forsTrees params.forsHeight hmsg0)
                params.forsTrees 0 rootsF (Nat.zero_add _ ▸ Nat.le_refl _) hRootsF hRootsEq with
        | .inl pre => .inl pre
        | .inr (.inl col) => .inr (.inl col)
        | .inr (.inr hAllCov) =>
          .inr (.inr { allCovered := fun j hj => by simpa [idxs] using hAllCov j hj })

/-- Constructive `Type`-valued outcome of `extractFullHypertreeForgery` (`0 Classical.choice`). -/
inductive HypertreeForgeryBreak (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msgStar : List UInt8) (sig : PqHashSig)
    (revealedFors : List (UInt64 × Nat × Nat)) : Type where
  | wotsInversion (w : WotsBackwardInversionWitness suite sk.pkSeed)
  | forsPreimage  (w : ForsPreimageWitness suite sk revealedFors)
  | hashCollision (w : HashCollisionWitness suite.rawHash)
  | statelessForsSubsetCover
      (hStateless : params.statefulJorts = false)
      (w : ForsSubsetCoverWitness params
             (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
             (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)
             (thHashMsg suite sig.rRand sk.pkSeed (derivePublicKey suite params sk).pkRoot
               (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msgStar)
               0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
               (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) sig.msgTswCtr)
             revealedFors)

/-- Constructive `0 Classical.choice` list search avoiding `List.find?_eq_none`. -/
private def findPreHashMatch (f : List UInt8 → List UInt8) (target : List UInt8) :
    (ms : List (List UInt8)) →
    PSum { m : List UInt8 // m ∈ ms ∧ f m = target } (∀ m ∈ ms, f m ≠ target)
  | [] => .inr (fun _ hm => by cases hm)
  | m :: rest =>
    if hEq : f m = target then
      .inl ⟨m, .head _, hEq⟩
    else
      match findPreHashMatch f target rest with
      | .inl ⟨w, hwMem, hwEq⟩ => .inl ⟨w, .tail _ hwMem, hwEq⟩
      | .inr hNone => .inr (fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hTl
          · exact hEq
          · exact hNone z hTl)

/-- Reachable upper-layer hypertree position `(l, g)` visited during a `d = params.numLayers`
    verification walk from `leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)`:
    `0 < l`, `l < params.numLayers`, and `g < 2 ^ ((params.numLayers - l) * params.subtreeHeight)`. -/
def ReachableUpperHypertreePos (params : PqHashParams) (l g : Nat) : Prop :=
  0 < l ∧ l < params.numLayers ∧ g < 2 ^ ((params.numLayers - l) * params.subtreeHeight)

/-- Single-layer WOTS+C + XMSS Merkle extraction supporting both production geometries
    `(w, ℓ₁) ∈ {(4, 128), (16, 64)}` (`0 Classical.choice`). -/
def extractSingleLayerDivergenceGeom
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (pkRoot layer0Rand curRoot honestCurRoot : List UInt8)
    (layerIdx globalIdx : Nat) (lsig : LayerXmssSig)
    (qOracle : QueriedWotsOracle)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hSubLt : globalIdx % (2 ^ params.subtreeHeight) < 2 ^ params.subtreeHeight)
    (hDiffRoot : curRoot ≠ honestCurRoot)
    (hValidTsw : checkTargetSum params.w params.ell1 params.targetSum
      (extractBaseWDigits params.w params.ell1
        (thHashMsg suite layer0Rand sk.pkSeed pkRoot curRoot (UInt32.ofNat layerIdx)
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) lsig.tswCtr)) = true)
    (hWalkEq : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
        (globalIdx % 2 ^ params.subtreeHeight)
        (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat layerIdx)
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (globalIdx % 2 ^ params.subtreeHeight)
          (extractBaseWDigits params.w params.ell1
            (thHashMsg suite layer0Rand sk.pkSeed pkRoot curRoot (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) lsig.tswCtr))
          lsig.wotsChains)
        lsig.authPath =
      some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))))
    (hValidOracle : ∀ hRand hCtr hChains,
      qOracle (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight) = some (hRand, honestCurRoot, hCtr, hChains) →
      let hmH := thHashMsg suite hRand sk.pkSeed pkRoot honestCurRoot (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) hCtr
      let digH := extractBaseWDigits params.w params.ell1 hmH
      checkTargetSum params.w params.ell1 params.targetSum digH = true ∧
      recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight) digH hChains =
      computeWotsPk suite params sk (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight))
    (hOracleRoot : ∀ hRand hRoot hCtr hChains,
      qOracle (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
      hRoot = honestCurRoot) :
    PSum (WotsBackwardInversionWitness suite sk.pkSeed) (HashCollisionWitness suite.rawHash) :=
  let subLeaves := 2 ^ params.subtreeHeight
  let kpIdx := globalIdx % subLeaves
  let kpU32 := UInt32.ofNat kpIdx
  let treeIdx := UInt64.ofNat (globalIdx / subLeaves)
  let layerU32 := UInt32.ofNat layerIdx
  let hmF := thHashMsg suite layer0Rand sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 lsig.tswCtr
  let digF := extractBaseWDigits params.w params.ell1 hmF
  let wotsPkF := recoverWotsPkFromSig suite params sk.pkSeed layerU32 treeIdx kpIdx digF lsig.wotsChains
  let wotsPkH := computeWotsPk suite params sk layerU32 treeIdx kpIdx
  let pathH := buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
    (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx
  have hWalkH : walkMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree params.subtreeHeight 0 kpIdx wotsPkH pathH =
      some (computeXmssSubtreeRoot suite params sk layerU32 treeIdx) := by
    have hw := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
      (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx hSubLt
    simp only [Nat.zero_mul, Nat.zero_add] at hw
    rw [computeXmssSubtreeRoot_eq]
    exact hw
  if hMerkleDiff : wotsPkF ≠ wotsPkH ∨ lsig.authPath ≠ pathH then
    .inr (walkMerkleAuthPath_collision_extract suite sk.pkSeed layerU32 treeIdx .tree
      params.subtreeHeight 0 kpIdx hMerkleDiff hWalkEq hWalkH)
  else
    have hWotsEq : wotsPkF = wotsPkH := Decidable.of_not_not (fun hn => hMerkleDiff (.inl hn))
    have hStrictT : params.targetSum < (params.w - 1) * params.ell1 := by
      rw [PqHashParams.targetSum_eq]
      rcases hGeom with ⟨hw, hell⟩ | ⟨hw, hell⟩ <;> rw [hw, hell] <;> decide
    match hQ : qOracle layerU32 treeIdx kpIdx with
    | none =>
      extractUnqueriedWotsBreak suite params sk layerU32 treeIdx kpIdx digF lsig.wotsChains
        hValidTsw hStrictT hWotsEq
    | some (hRand, hRoot, hCtr, hChains) =>
      have hRootEq : hRoot = honestCurRoot := hOracleRoot hRand hRoot hCtr hChains hQ
      have hQ' : qOracle layerU32 treeIdx kpIdx = some (hRand, honestCurRoot, hCtr, hChains) :=
        hRootEq ▸ hQ
      let hmH := thHashMsg suite hRand sk.pkSeed pkRoot honestCurRoot layerU32 treeIdx kpU32 hCtr
      let digH := extractBaseWDigits params.w params.ell1 hmH
      have hHProps := hValidOracle hRand hCtr hChains hQ'
      if hDigNe : digH ≠ digF then
        extractPqHashForgery suite params sk.pkSeed layerU32 treeIdx kpIdx digH digF hChains lsig.wotsChains
          hHProps.1 hValidTsw hDigNe (hWotsEq.trans hHProps.2.symm)
      else
        have hDigEq : digF = digH := (Decidable.of_not_not hDigNe).symm
        have hTakeEq : hmF.take 32 = hmH.take 32 := by
          have hLenF := thHashMsg_length suite layer0Rand sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 lsig.tswCtr
          have hLenH := thHashMsg_length suite hRand sk.pkSeed pkRoot honestCurRoot layerU32 treeIdx kpU32 hCtr
          rcases hGeom with ⟨hw, hell⟩ | ⟨hw, hell⟩
          · have hDigEq4 : extractBaseWDigits 4 128 hmF = extractBaseWDigits 4 128 hmH := by
              simpa [digF, digH, hw, hell] using hDigEq
            exact extractBaseWDigits_4_128_take32_eq hLenF hLenH hDigEq4
          · have hDigEq16 : extractBaseWDigits 16 (2 * 32) hmF = extractBaseWDigits 16 (2 * 32) hmH := by
              simpa [digF, digH, hw, hell] using hDigEq
            exact extractBaseWDigits_base16_prefix_injective 32
              (by rw [hLenF]; decide) (by rw [hLenH]; decide) hDigEq16
        have hB0Eq :
            thCall suite tagHMsg sk.pkSeed ⟨layerU32, treeIdx, .wotsHash, kpU32, 0, UInt32.ofNat lsig.tswCtr⟩
              [layer0Rand, pkRoot, curRoot, be 4 lsig.tswCtr] =
            thCall suite tagHMsg sk.pkSeed ⟨layerU32, treeIdx, .wotsHash, kpU32, 0, UInt32.ofNat hCtr⟩
              [hRand, pkRoot, honestCurRoot, be 4 hCtr] := by
          have hT1 : hmF.take 32 = thCall suite tagHMsg sk.pkSeed
              ⟨layerU32, treeIdx, .wotsHash, kpU32, 0, UInt32.ofNat lsig.tswCtr⟩
              [layer0Rand, pkRoot, curRoot, be 4 lsig.tswCtr] := by
            dsimp [hmF]; rw [thHashMsg_eq, List.take_left' (thCall_length _ _ _ _ _)]
          have hT2 : hmH.take 32 = thCall suite tagHMsg sk.pkSeed
              ⟨layerU32, treeIdx, .wotsHash, kpU32, 0, UInt32.ofNat hCtr⟩
              [hRand, pkRoot, honestCurRoot, be 4 hCtr] := by
            dsimp [hmH]; rw [thHashMsg_eq, List.take_left' (thCall_length _ _ _ _ _)]
          exact hT1.symm.trans (hTakeEq.trans hT2)
        match thCall_binds_or_collision suite hB0Eq with
        | .inl ⟨_, _, _, hArgsEq⟩ =>
          False.elim (by
            simp only [List.cons.injEq] at hArgsEq
            exact hDiffRoot hArgsEq.2.2.1)
        | .inr col => .inr col

/-- Bounded multi-layer hypertree `PSum` extractor (`0 Classical.choice`):
    invokes `hOrc` **strictly** on reachable positions `(l, g)` (`layerIdx ≤ l < params.numLayers`
    and `g < 2 ^ ((params.numLayers - l) * params.subtreeHeight)`), avoiding unbounded layer/tree wraparound. -/
def extractBoundedHypertreeLayersBreak
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (pkRoot : List UInt8) (qOracle : QueriedWotsOracle)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64)) :
    ∀ (layerSigs : List LayerXmssSig) (layerIdx globalIdx : Nat)
      (layer0Rand curRoot honestCurRoot : List UInt8),
      layerIdx + layerSigs.length = params.numLayers →
      globalIdx < 2 ^ (layerSigs.length * params.subtreeHeight) →
      curRoot ≠ honestCurRoot →
      verifyHypertreeLayers suite params sk.pkSeed pkRoot layer0Rand layerIdx globalIdx curRoot layerSigs =
        some (if layerSigs.isEmpty then honestCurRoot
              else computeXmssSubtreeRoot suite params sk
                (UInt32.ofNat (layerIdx + layerSigs.length - 1))
                (UInt64.ofNat (globalIdx / 2 ^ (layerSigs.length * params.subtreeHeight)))) →
      (∀ (l : Nat) (g : Nat) (hRoot0 : List UInt8),
        (l = layerIdx ∧ g = globalIdx ∧ hRoot0 = honestCurRoot) ∨
        (layerIdx < l ∧ ReachableUpperHypertreePos params l g ∧
         hRoot0 = computeXmssSubtreeRoot suite params sk (UInt32.ofNat (l - 1)) (UInt64.ofNat g)) →
        (∀ hRand hCtr hChains,
          qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) =
            some (hRand, hRoot0, hCtr, hChains) →
          let hmH := thHashMsg suite hRand sk.pkSeed pkRoot hRoot0 (UInt32.ofNat l)
            (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) hCtr
          let digH := extractBaseWDigits params.w params.ell1 hmH
          checkTargetSum params.w params.ell1 params.targetSum digH = true ∧
          recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat l)
            (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) digH hChains =
          computeWotsPk suite params sk (UInt32.ofNat l)
            (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight)) ∧
        (∀ hRand hR hCtr hChains,
          qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) =
            some (hRand, hR, hCtr, hChains) → hR = hRoot0)) →
      PSum (WotsBackwardInversionWitness suite sk.pkSeed) (HashCollisionWitness suite.rawHash)
  | [], _, _, _, curRoot, honestCurRoot, _, _, hDiff, hVer, _ => by
    rw [verifyHypertreeLayers_nil] at hVer
    simp only [List.isEmpty_nil, ↓reduceIte, Option.some.injEq] at hVer
    exact False.elim (hDiff hVer)
  | lsig :: rest, layerIdx, globalIdx, layer0Rand, curRoot, honestCurRoot, hLenSum, hGlobalLt, hDiff, hVer, hOrc =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let kpU32 := UInt32.ofNat kpIdx
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    let hmsg := thHashMsg suite layer0Rand sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 lsig.tswCtr
    let digits := extractBaseWDigits params.w params.ell1 hmsg
    match hTsw : checkTargetSum params.w params.ell1 params.targetSum digits with
    | false =>
      False.elim (by
        rw [verifyHypertreeLayers_cons] at hVer
        dsimp only at hVer
        dsimp only [digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves] at hTsw
        rw [hTsw] at hVer
        simp at hVer)
    | true =>
      if hCLen : lsig.wotsChains.length ≠ params.ell1 then
        False.elim (by
          rw [verifyHypertreeLayers_cons] at hVer
          dsimp only at hVer
          dsimp only [digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves] at hTsw
          rw [hTsw] at hVer
          simp [hCLen] at hVer)
      else
        have hCLenEq : lsig.wotsChains.length = params.ell1 := Decidable.of_not_not hCLen
        let wotsPk := recoverWotsPkFromSig suite params sk.pkSeed layerU32 treeIdx kpIdx digits lsig.wotsChains
        match hWalk : walkMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree params.subtreeHeight 0 kpIdx wotsPk lsig.authPath with
        | none =>
          False.elim (by
            rw [verifyHypertreeLayers_cons] at hVer
            dsimp only at hVer
            dsimp only [wotsPk, digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves] at hTsw hWalk
            rw [hTsw, hWalk] at hVer
            simp [hCLenEq] at hVer)
        | some nextSubtreeRoot =>
          let honestNext := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
          if hNextEq : nextSubtreeRoot = honestNext then
            have hSubLt : globalIdx % (2 ^ params.subtreeHeight) < 2 ^ params.subtreeHeight :=
              Nat.mod_lt _ (Nat.two_pow_pos _)
            have hHere := hOrc layerIdx globalIdx honestCurRoot (.inl ⟨rfl, rfl, rfl⟩)
            extractSingleLayerDivergenceGeom suite params sk pkRoot layer0Rand curRoot honestCurRoot
              layerIdx globalIdx lsig qOracle hGeom hSubLt hDiff hTsw
              (by
                dsimp only [wotsPk, digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves, honestNext] at hWalk hNextEq
                rw [← hNextEq]
                exact hWalk)
              hHere.1 hHere.2
          else
            match rest with
            | [] =>
              False.elim (by
                rw [verifyHypertreeLayers_cons] at hVer
                dsimp only at hVer
                have hTsw' := hTsw
                have hWalk' := hWalk
                dsimp only [wotsPk, digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves] at hTsw' hWalk'
                rw [hTsw'] at hVer
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                           hCLenEq, ne_eq, not_true_eq_false] at hVer
                rw [hWalk'] at hVer
                dsimp only at hVer
                rw [verifyHypertreeLayers_nil] at hVer
                simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_singleton,
                           Nat.add_sub_cancel, Nat.one_mul, Option.some.injEq] at hVer
                exact hNextEq hVer)
            | r0 :: rs =>
              have hLenRest : (layerIdx + 1) + (r0 :: rs).length = params.numLayers := by
                simp only [List.length_cons] at hLenSum ⊢
                omega
              have hDivLt : treeIdxNat < 2 ^ ((r0 :: rs).length * params.subtreeHeight) := by
                dsimp only [treeIdxNat, subLeaves]
                rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
                have hMulEq : (r0 :: rs).length * params.subtreeHeight + params.subtreeHeight =
                    (lsig :: r0 :: rs).length * params.subtreeHeight := by
                  simp only [List.length_cons]
                  exact (Nat.succ_mul (rs.length + 1) params.subtreeHeight).symm
                rwa [hMulEq]
              have hRestVer :
                  verifyHypertreeLayers suite params sk.pkSeed pkRoot [] (layerIdx + 1) treeIdxNat nextSubtreeRoot (r0 :: rs) =
                  some (if (r0 :: rs).isEmpty then honestNext
                        else computeXmssSubtreeRoot suite params sk
                          (UInt32.ofNat ((layerIdx + 1) + (r0 :: rs).length - 1))
                          (UInt64.ofNat (treeIdxNat / 2 ^ ((r0 :: rs).length * params.subtreeHeight)))) := by
                rw [verifyHypertreeLayers_cons] at hVer
                dsimp only at hVer
                have hTsw' := hTsw
                have hWalk' := hWalk
                dsimp only [wotsPk, digits, hmsg, kpU32, kpIdx, treeIdx, treeIdxNat, layerU32, subLeaves] at hTsw' hWalk'
                rw [hTsw'] at hVer
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                           hCLenEq, ne_eq, not_true_eq_false] at hVer
                rw [hWalk'] at hVer
                dsimp only [treeIdxNat, subLeaves, honestNext, layerU32, treeIdx]
                simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hVer ⊢
                have hIdxEq : (layerIdx + 1) + (rs.length + 1) - 1 = layerIdx + (rs.length + 1 + 1) - 1 := by omega
                have hDivEq : (globalIdx / 2 ^ params.subtreeHeight) / 2 ^ ((rs.length + 1) * params.subtreeHeight) =
                    globalIdx / 2 ^ ((rs.length + 1 + 1) * params.subtreeHeight) := by
                  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add,
                      show params.subtreeHeight + (rs.length + 1) * params.subtreeHeight =
                           (rs.length + 1 + 1) * params.subtreeHeight by
                        rw [Nat.succ_mul (rs.length + 1), Nat.add_comm]]
                rw [hIdxEq, hDivEq]
                exact hVer
              extractBoundedHypertreeLayersBreak suite params sk pkRoot qOracle hGeom
                (r0 :: rs) (layerIdx + 1) treeIdxNat [] nextSubtreeRoot honestNext hLenRest hDivLt hNextEq hRestVer
                (fun l g hRoot0 hCond => by
                  apply hOrc l g hRoot0
                  rcases hCond with ⟨rfl, rfl, rfl⟩ | ⟨hGt, hReach, hR⟩
                  · refine .inr ⟨by omega, ⟨by omega, ?_, ?_⟩, by dsimp [honestNext, layerU32, treeIdx, treeIdxNat, subLeaves]⟩
                    · simp only [List.length_cons] at hLenRest
                      omega
                    · have hSub : params.numLayers - (layerIdx + 1) = (r0 :: rs).length := by omega
                      rwa [hSub]
                  · exact .inr ⟨by omega, hReach, hR⟩)

/-- **Reachable-Layer Multi-Layer Hypertree + FORS Constructive EUF-CMA Extractor (`extractReachableHypertreeForgery`)**:
    Quantifies `hUpperOracle` strictly over `ReachableUpperHypertreePos params l g` (`0 < l < params.numLayers`
    and `g < 2 ^ ((params.numLayers - l) * params.subtreeHeight)`), eliminating unbounded layer/tree wraparound
    so that every oracle hypothesis is constructively dischargeable from a finite signing log! -/
def extractReachableHypertreeForgery
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (msgStar : List UInt8) (sig : PqHashSig)
    (queriedMsgs : List (List UInt8))
    (qOracle : QueriedWotsOracle)
    (revealedFors : List (UInt64 × Nat × Nat))
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hFreshMsg : msgStar ∉ queriedMsgs)
    (hAccept : verifyPqHashSig suite params (derivePublicKey suite params sk) msgStar sig = true)
    (hStatefulLeaf0Msg : params.statefulJorts = true →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        ∃ mPrev ∈ queriedMsgs,
          hRoot = thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot mPrev)
    (hStatelessLayer0Root : params.statefulJorts = false →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        hRoot = computeForsPk suite params sk
          (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ params.subtreeHeight))
    (hUpperOracle : ∀ (l : Nat) (g : Nat), ReachableUpperHypertreePos params l g →
      let hRoot0 := computeXmssSubtreeRoot suite params sk (UInt32.ofNat (l - 1)) (UInt64.ofNat g)
      (∀ hRand hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) =
          some (hRand, hRoot0, hCtr, hChains) →
        let hmH := thHashMsg suite hRand sk.pkSeed (derivePublicKey suite params sk).pkRoot hRoot0
          (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) hCtr
        let digH := extractBaseWDigits params.w params.ell1 hmH
        checkTargetSum params.w params.ell1 params.targetSum digH = true ∧
        recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) digH hChains =
        computeWotsPk suite params sk (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight)) ∧
      (∀ hRand hR hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) =
          some (hRand, hR, hCtr, hChains) → hR = hRoot0))
    (hLayer0Valid : ∀ hRand hRoot0 hCtr hChains,
      qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) = some (hRand, hRoot0, hCtr, hChains) →
      let hmH := thHashMsg suite hRand sk.pkSeed (derivePublicKey suite params sk).pkRoot hRoot0
        0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) hCtr
      let digH := extractBaseWDigits params.w params.ell1 hmH
      checkTargetSum params.w params.ell1 params.targetSum digH = true ∧
      recoverWotsPkFromSig suite params sk.pkSeed 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) digH hChains =
      computeWotsPk suite params sk 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) :
    HypertreeForgeryBreak suite params sk msgStar sig revealedFors :=
  let pk := derivePublicKey suite params sk
  let muStar := thPreHash suite sk.pkSeed pk.pkRoot msgStar
  have hPkSeed : pk.pkSeed = sk.pkSeed := rfl
  have hGuards : params.wellFormed = true ∧ sig.layerSigs.length = params.numLayers ∧
      sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) ∧ 0 < params.numLayers := by
    unfold verifyPqHashSig at hAccept
    cases hWf0 : params.wellFormed
    · simp [hWf0] at hAccept
    · cases hLen : decide (sig.layerSigs.length = params.numLayers)
      · have hNe : sig.layerSigs.length ≠ params.numLayers := of_decide_eq_false hLen
        simp [hWf0, hNe] at hAccept
      · cases hIdx : decide (sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
        · have hNotLt : ¬ (sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) := of_decide_eq_false hIdx
          simp [hWf0, of_decide_eq_true hLen, hNotLt] at hAccept
        · have hDPos : 0 < params.numLayers := by
            have hWf' := hWf0
            rw [PqHashParams.wellFormed_eq] at hWf'
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hWf'
            omega
          exact ⟨rfl, of_decide_eq_true hLen, of_decide_eq_true hIdx, hDPos⟩
  have hWf : params.wellFormed = true := hGuards.1
  have hSigLen : sig.layerSigs.length = params.numLayers := hGuards.2.1
  have hIdxLt : sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) := hGuards.2.2.1
  have hDPos : 0 < params.numLayers := hGuards.2.2.2
  have hLen0 : 0 + sig.layerSigs.length = params.numLayers := by rw [Nat.zero_add, hSigLen]
  have hIdxLt0 : sig.leafGlobalIdx < 2 ^ (sig.layerSigs.length * params.subtreeHeight) := by rwa [hSigLen]
  have hTopTarget : ∀ honest0 : List UInt8,
      (if sig.layerSigs.isEmpty then honest0
       else computeXmssSubtreeRoot suite params sk
         (UInt32.ofNat (0 + sig.layerSigs.length - 1))
         (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ (sig.layerSigs.length * params.subtreeHeight)))) = pk.pkRoot := by
    intro honest0
    have hNonEmpty : sig.layerSigs.isEmpty = false := by
      cases hs : sig.layerSigs with
      | nil => have hl := hSigLen; rw [hs] at hl; simp only [List.length_nil] at hl; omega
      | cons _ _ => rfl
    rw [hNonEmpty]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hSigLen, Nat.zero_add, Nat.div_eq_of_lt hIdxLt]
    rfl
  if hMode : params.statefulJorts = true then
    have hHtVer : verifyHypertreeLayers suite params sk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx muStar sig.layerSigs =
        some pk.pkRoot := by
      change verifyPqHashSig suite params pk msgStar sig = true at hAccept
      unfold verifyPqHashSig at hAccept
      simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                 hSigLen, ne_eq, not_true_eq_false, hIdxLt, decide_true, hMode, hPkSeed] at hAccept
      cases hPre : (!sig.forsOpenings.isEmpty || decide (sig.msgTswCtr ≠ 0))
      · simp only [hPre, Bool.false_eq_true, ↓reduceIte] at hAccept
        have hvGoal : verifyHypertreeLayers suite params sk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx
            (thPreHash suite sk.pkSeed pk.pkRoot msgStar) sig.layerSigs = some pk.pkRoot := by
          cases hv : verifyHypertreeLayers suite params sk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx
              (thPreHash suite sk.pkSeed pk.pkRoot msgStar) sig.layerSigs with
          | none => rw [hv] at hAccept; cases hAccept
          | some r =>
            rw [hv] at hAccept
            simp only [decide_eq_true_eq] at hAccept
            exact congrArg some hAccept
        exact hvGoal
      · rcases Bool.or_eq_true_iff.mp hPre with hF | hD
        · simp [hF] at hAccept
        · simp [of_decide_eq_true hD] at hAccept
    let tree0 := UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight)
    let kp0 := sig.leafGlobalIdx % 2 ^ params.subtreeHeight
    match hQ0 : qOracle 0 tree0 kp0 with
    | none =>
      let dummyHonest0 := (0 : UInt8) :: muStar
      have hNeDummy : muStar ≠ dummyHonest0 := by
        intro hEq
        have hLen := congrArg List.length hEq
        simp only [dummyHonest0, List.length_cons] at hLen
        omega
      match extractBoundedHypertreeLayersBreak suite params sk pk.pkRoot qOracle hGeom
              sig.layerSigs 0 sig.leafGlobalIdx sig.rRand muStar dummyHonest0 hLen0 hIdxLt0 hNeDummy
              (by rw [hTopTarget dummyHonest0]; exact hHtVer)
              (fun l g hRootArg hCond => by
                rcases hCond with ⟨rfl, rfl, rfl⟩ | ⟨_, hReach, rfl⟩
                · refine ⟨fun _ _ _ hSome => (by
                            change qOracle 0 tree0 kp0 = _ at hSome
                            rw [hQ0] at hSome; cases hSome),
                          fun _ _ _ _ hSome => (by
                            change qOracle 0 tree0 kp0 = _ at hSome
                            rw [hQ0] at hSome; cases hSome)⟩
                · exact hUpperOracle l g hReach) with
      | .inl w => .wotsInversion w
      | .inr col => .hashCollision col
    | some (hRand0, hRoot0, hCtr0, hChains0) =>
      if hMuEq : muStar = hRoot0 then
        match findPreHashMatch (thPreHash suite sk.pkSeed pk.pkRoot) hRoot0 queriedMsgs with
        | .inr hAllNe =>
          False.elim (by
            obtain ⟨mPrev, hmMem, hmPre⟩ := hStatefulLeaf0Msg hMode hRand0 hRoot0 hCtr0 hChains0 hQ0
            exact hAllNe mPrev hmMem hmPre.symm)
        | .inl ⟨mPrev, hmMem, hmPre⟩ =>
          have hCallEq : thCall suite tagHPre sk.pkSeed zeroAdrs [pk.pkRoot, msgStar] =
                         thCall suite tagHPre sk.pkSeed zeroAdrs [pk.pkRoot, mPrev] := by
            rw [← thPreHash_eq, ← thPreHash_eq]
            exact hMuEq.trans hmPre.symm
          match thCall_binds_or_collision suite hCallEq with
          | .inl ⟨_, _, _, hArgsEq⟩ =>
            False.elim (by
              simp only [List.cons.injEq, and_true] at hArgsEq
              exact hFreshMsg (hArgsEq.2 ▸ hmMem))
          | .inr col => .hashCollision col
      else
        match extractBoundedHypertreeLayersBreak suite params sk pk.pkRoot qOracle hGeom
                sig.layerSigs 0 sig.leafGlobalIdx sig.rRand muStar hRoot0 hLen0 hIdxLt0 hMuEq
                (by rw [hTopTarget hRoot0]; exact hHtVer)
                (fun l g hRootArg hCond => by
                  rcases hCond with ⟨rfl, rfl, hEqR⟩ | ⟨_, hReach, rfl⟩
                  · rw [hEqR]
                    refine ⟨fun r c ch hS => hLayer0Valid r hRoot0 c ch hS,
                            fun r hr c ch hS => (by
                              change qOracle 0 tree0 kp0 = some (r, hr, c, ch) at hS
                              rw [hQ0] at hS
                              injection hS with hT
                              rcases Prod.mk.inj hT with ⟨_, hT2⟩
                              exact (Prod.mk.inj hT2).1.symm)⟩
                  · exact hUpperOracle l g hReach) with
        | .inl w => .wotsInversion w
        | .inr col => .hashCollision col
  else
    have hModeFalse : params.statefulJorts = false := Bool.eq_false_iff.mpr hMode
    let subLeaves := 2 ^ params.subtreeHeight
    let kp0 := sig.leafGlobalIdx % subLeaves
    let kp0U32 := UInt32.ofNat kp0
    let tree0 := UInt64.ofNat (sig.leafGlobalIdx / subLeaves)
    let hmsg0 := thHashMsg suite sig.rRand sk.pkSeed pk.pkRoot muStar 0 tree0 kp0U32 sig.msgTswCtr
    let digits0 := extractBaseWDigits params.w params.ell1 hmsg0
    match hForsRec : recoverForsPk suite params sk.pkSeed tree0 kp0 hmsg0 sig.forsOpenings with
    | none =>
      False.elim (by
        change verifyPqHashSig suite params pk msgStar sig = true at hAccept
        unfold verifyPqHashSig at hAccept
        simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                   hSigLen, ne_eq, not_true_eq_false, hIdxLt, decide_true, hModeFalse, hPkSeed] at hAccept
        dsimp only [digits0, hmsg0, muStar, kp0U32, kp0, tree0, subLeaves] at hForsRec
        cases hC0 : checkTargetSum params.w params.ell1 params.targetSum
            (extractBaseWDigits params.w params.ell1
              (thHashMsg suite sig.rRand sk.pkSeed pk.pkRoot
                (thPreHash suite sk.pkSeed pk.pkRoot msgStar) 0
                (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) sig.msgTswCtr))
        · rw [hC0] at hAccept; simp at hAccept
        · rw [hC0] at hAccept
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAccept
          rw [hForsRec] at hAccept; cases hAccept)
    | some forsPkF =>
      have hHtVerS : verifyHypertreeLayers suite params sk.pkSeed pk.pkRoot [] 0 sig.leafGlobalIdx forsPkF sig.layerSigs =
          some pk.pkRoot := by
        change verifyPqHashSig suite params pk msgStar sig = true at hAccept
        unfold verifyPqHashSig at hAccept
        simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                   hSigLen, ne_eq, not_true_eq_false, hIdxLt, decide_true, hModeFalse, hPkSeed] at hAccept
        have hForsRec' := hForsRec
        dsimp only [digits0, hmsg0, muStar, kp0U32, kp0, tree0, subLeaves] at hForsRec'
        cases hC0 : checkTargetSum params.w params.ell1 params.targetSum
            (extractBaseWDigits params.w params.ell1
              (thHashMsg suite sig.rRand sk.pkSeed pk.pkRoot
                (thPreHash suite sk.pkSeed pk.pkRoot msgStar) 0
                (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) sig.msgTswCtr))
        · rw [hC0] at hAccept; simp at hAccept
        · rw [hC0] at hAccept
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAccept
          rw [hForsRec'] at hAccept
          dsimp only at hAccept
          cases hv : verifyHypertreeLayers suite params sk.pkSeed pk.pkRoot [] 0 sig.leafGlobalIdx forsPkF sig.layerSigs with
          | none => rw [hv] at hAccept; cases hAccept
          | some r =>
            rw [hv] at hAccept
            simp only [decide_eq_true_eq] at hAccept
            exact congrArg some hAccept
      let forsPkH := computeForsPk suite params sk tree0 kp0
      if hForsDiff : forsPkF ≠ forsPkH then
        match extractBoundedHypertreeLayersBreak suite params sk pk.pkRoot qOracle hGeom
                sig.layerSigs 0 sig.leafGlobalIdx [] forsPkF forsPkH hLen0 hIdxLt0 hForsDiff
                (by rw [hTopTarget forsPkH]; exact hHtVerS)
                (fun l g hRootArg hCond => by
                  rcases hCond with ⟨rfl, rfl, rfl⟩ | ⟨_, hReach, rfl⟩
                  · refine ⟨fun r c ch hS => hLayer0Valid r forsPkH c ch hS,
                            fun r hr c ch hS => hStatelessLayer0Root hModeFalse r hr c ch hS⟩
                  · exact hUpperOracle l g hReach) with
        | .inl w => .wotsInversion w
        | .inr col => .hashCollision col
      else
        have hForsEq : forsPkF = forsPkH := Decidable.of_not_not hForsDiff
        match extractForsBreak suite params sk tree0 kp0 hmsg0 sig.forsOpenings revealedFors
                (by dsimp only [forsPkH] at hForsEq; rw [← hForsEq]; exact hForsRec) with
        | .inl pre => .forsPreimage pre
        | .inr (.inl col) => .hashCollision col
        | .inr (.inr cov) => .statelessForsSubsetCover hModeFalse cov

/-- **Full Multi-Layer Hypertree + FORS Constructive EUF-CMA Extractor (`extractFullHypertreeForgery`)**:
    Preserves the exact signature relied on by downstream `Aggregation.lean` while delegating to
    `extractReachableHypertreeForgery` (`0 Classical.choice`). -/
def extractFullHypertreeForgery
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (msgStar : List UInt8) (sig : PqHashSig)
    (queriedMsgs : List (List UInt8))
    (qOracle : QueriedWotsOracle)
    (revealedFors : List (UInt64 × Nat × Nat))
    (hParams4_128 : params.w = 4 ∧ params.ell1 = 128)
    (hFreshMsg : msgStar ∉ queriedMsgs)
    (hAccept : verifyPqHashSig suite params (derivePublicKey suite params sk) msgStar sig = true)
    (hStatefulLeaf0Msg : params.statefulJorts = true →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        ∃ mPrev ∈ queriedMsgs,
          hRoot = thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot mPrev)
    (hStatelessLayer0Root : params.statefulJorts = false →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        hRoot = computeForsPk suite params sk
          (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ params.subtreeHeight))
    (hUpperOracle : ∀ (l : Nat) (g : Nat), 0 < l →
      let hRoot0 := computeXmssSubtreeRoot suite params sk (UInt32.ofNat (l - 1)) (UInt64.ofNat g)
      (∀ hRand hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) =
          some (hRand, hRoot0, hCtr, hChains) →
        let hmH := thHashMsg suite hRand sk.pkSeed (derivePublicKey suite params sk).pkRoot hRoot0
          (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) hCtr
        let digH := extractBaseWDigits params.w params.ell1 hmH
        checkTargetSum params.w params.ell1 params.targetSum digH = true ∧
        recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) digH hChains =
        computeWotsPk suite params sk (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight)) ∧
      (∀ hRand hR hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) =
          some (hRand, hR, hCtr, hChains) → hR = hRoot0))
    (hLayer0Valid : ∀ hRand hRoot0 hCtr hChains,
      qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) = some (hRand, hRoot0, hCtr, hChains) →
      let hmH := thHashMsg suite hRand sk.pkSeed (derivePublicKey suite params sk).pkRoot hRoot0
        0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) hCtr
      let digH := extractBaseWDigits params.w params.ell1 hmH
      checkTargetSum params.w params.ell1 params.targetSum digH = true ∧
      recoverWotsPkFromSig suite params sk.pkSeed 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) digH hChains =
      computeWotsPk suite params sk 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) :
    HypertreeForgeryBreak suite params sk msgStar sig revealedFors :=
  extractReachableHypertreeForgery suite params sk msgStar sig queriedMsgs qOracle revealedFors
    (.inl hParams4_128) hFreshMsg hAccept hStatefulLeaf0Msg hStatelessLayer0Root
    (fun l g hReach => hUpperOracle l g hReach.1) hLayer0Valid


/-! ## 5. Break witnesses derived from an actual signing log (stateless profiles)

Everything below is stated for `params.statefulJorts = false`. Revealed material is read off the
log returned by `signingOracleLog`; no caller-supplied oracle or revealed-leaf list appears. -/

theorem thCall_eq_cases (suite : TweakableHashSuite)
    {t₁ p₁ : List UInt8} {a₁ : HashAdrs} {xs₁ : List (List UInt8)}
    {t₂ p₂ : List UInt8} {a₂ : HashAdrs} {xs₂ : List (List UInt8)}
    (hEq : thCall suite t₁ p₁ a₁ xs₁ = thCall suite t₂ p₂ a₂ xs₂) :
    (t₁ = t₂ ∧ p₁ = p₂ ∧ a₁ = a₂ ∧ xs₁ = xs₂) ∨
    (thPreimage t₁ p₁ a₁ xs₁ ≠ thPreimage t₂ p₂ a₂ xs₂ ∧
      suite.rawHash (thPreimage t₁ p₁ a₁ xs₁) = suite.rawHash (thPreimage t₂ p₂ a₂ xs₂)) := by
  by_cases hPre : thPreimage t₁ p₁ a₁ xs₁ = thPreimage t₂ p₂ a₂ xs₂
  · exact .inl (thPreimage_injective hPre)
  · rw [thCall_eq, thCall_eq] at hEq
    exact .inr ⟨hPre, hEq⟩

theorem bounded_search (p : Nat → Prop) (hDec : ∀ i, p i ∨ ¬ p i) :
    ∀ n, (∃ i, i < n ∧ p i) ∨ (∀ i, i < n → ¬ p i)
  | 0 => .inr (fun i hi => absurd hi (Nat.not_lt_zero i))
  | n + 1 =>
    match bounded_search p hDec n with
    | .inl ⟨i, hi, hp⟩ => .inl ⟨i, Nat.lt_succ_of_lt hi, hp⟩
    | .inr hNone =>
      match hDec n with
      | .inl hp => .inl ⟨n, Nat.lt_succ_self n, hp⟩
      | .inr hn => .inr (fun i hi => by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
          · exact hNone i hlt
          · rw [heq]; exact hn)

theorem list_search {α : Type} (p : α → Prop) (hDec : ∀ a, p a ∨ ¬ p a) :
    ∀ l : List α, (∃ a, a ∈ l ∧ p a) ∨ (∀ a, a ∈ l → ¬ p a)
  | [] => .inr (fun _ h => by cases h)
  | x :: xs =>
    match hDec x with
    | .inl hp => .inl ⟨x, List.mem_cons_self, hp⟩
    | .inr hn =>
      match list_search p hDec xs with
      | .inl ⟨a, ha, hp⟩ => .inl ⟨a, List.mem_cons_of_mem x ha, hp⟩
      | .inr hNone => .inr (fun a ha => by
          rcases List.mem_cons.mp ha with heq | hTl
          · rw [heq]; exact hn
          · exact hNone a hTl)

theorem uint32_ofNat_inj {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    (h : UInt32.ofNat a = UInt32.ofNat b) : a = b := by
  have h' := congrArg UInt32.toNat h
  change a % 4294967296 = b % 4294967296 at h'
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact h'

theorem uint64_ofNat_inj {a b : Nat} (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (h : UInt64.ofNat a = UInt64.ofNat b) : a = b := by
  have h' := congrArg UInt64.toNat h
  change a % 18446744073709551616 = b % 18446744073709551616 at h'
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact h'

theorem PqHashParams.wellFormed_facts (p : PqHashParams) (h : p.wellFormed = true) :
    0 < p.numLayers ∧ 2 ≤ p.w ∧ p.subtreeHeight ≤ 30 ∧ p.forsHeight ≤ 30 ∧
    p.numLayers * p.subtreeHeight ≤ 62 ∧ (p.statefulJorts = false → 0 < p.forsTrees) := by
  rw [PqHashParams.wellFormed_eq] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, h6⟩, h7⟩, _⟩, h9⟩, h10⟩ := h
  refine ⟨h1, h2, h6, h7, h9, ?_⟩
  intro hs
  rcases h10 with hst | ⟨hk, _⟩
  · rw [hs] at hst; cases hst
  · exact hk

theorem div_pow_mul_pow_mul (L a b h : Nat) :
    L / 2 ^ (a * h) / 2 ^ (b * h) = L / 2 ^ ((a + b) * h) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.add_mul]

/-- Honest chain node at `step` of chain `r` of the WOTS key at `(layer, tree, kp)`. -/
def honestChainNode (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp r step : Nat) : List UInt8 :=
  wotsChainSteps suite sk.pkSeed layer tree kp r 0 step (wotsSecretBase suite sk layer tree kp r)

theorem honestChainNode_eq (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp r step : Nat) :
    honestChainNode suite sk layer tree kp r step =
      wotsChainSteps suite sk.pkSeed layer tree kp r 0 step
        (wotsSecretBase suite sk layer tree kp r) := by rfl

theorem honestChainNode_succ (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp r step : Nat) :
    thChainF suite sk.pkSeed
      ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat step⟩
      (honestChainNode suite sk layer tree kp r step) =
    honestChainNode suite sk layer tree kp r (step + 1) := by
  unfold honestChainNode
  have h := wotsChainSteps_add suite sk.pkSeed layer tree kp r step 1 0
    (wotsSecretBase suite sk layer tree kp r)
  rw [Nat.zero_add] at h
  rw [← h]
  simp only [wotsChainSteps]

/-- Message signed by the honest WOTS key at hypertree position `(i, g)` in stateless mode:
    the FORS public key at layer `0`, the subtree root below otherwise. -/
def honestLayerRoot (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (i g : Nat) : List UInt8 :=
  if i = 0 then
    computeForsPk suite params sk (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
      (g % 2 ^ params.subtreeHeight)
  else computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1)) (UInt64.ofNat g)

theorem honestLayerRoot_eq (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (i g : Nat) :
    honestLayerRoot suite params sk i g =
      if i = 0 then
        computeForsPk suite params sk (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
          (g % 2 ^ params.subtreeHeight)
      else computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1)) (UInt64.ofNat g) := by rfl

/-- Digits whose chain values a logged stateless signature discloses at layer `i`. -/
def logLayerDigits (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (sig : PqHashSig) (i : Nat) : List Nat :=
  extractBaseWDigits params.w params.ell1
    (thHashMsg suite [] sk.pkSeed (derivePublicKey suite params sk).pkRoot
      (honestLayerRoot suite params sk i (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))
      (UInt32.ofNat i)
      (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
      (UInt32.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
      (sig.layerSigs.getD i ⟨0, [], []⟩).tswCtr)

theorem logLayerDigits_eq (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (sig : PqHashSig) (i : Nat) :
    logLayerDigits suite params sk sig i =
      extractBaseWDigits params.w params.ell1
        (thHashMsg suite [] sk.pkSeed (derivePublicKey suite params sk).pkRoot
          (honestLayerRoot suite params sk i (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))
          (UInt32.ofNat i)
          (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
          (sig.layerSigs.getD i ⟨0, [], []⟩).tswCtr) := by rfl

/-- `HashAdrs` coordinates `(layer, tree, keypair)` of the WOTS key that the signature with
    hypertree leaf `leaf` uses at layer `i`. -/
def wotsPosAddr (params : PqHashParams) (leaf i : Nat) : UInt32 × UInt64 × UInt32 :=
  (UInt32.ofNat i,
   UInt64.ofNat (leaf / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight),
   UInt32.ofNat (leaf / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))

theorem wotsPosAddr_eq (params : PqHashParams) (leaf i : Nat) :
    wotsPosAddr params leaf i =
      (UInt32.ofNat i,
       UInt64.ofNat (leaf / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight),
       UInt32.ofNat (leaf / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)) := by rfl

/-- Within the well-formed range and at most `2^32` layers, address coordinates determine the
    hypertree position. -/
theorem wotsPosAddr_inj (params : PqHashParams) (hWf : params.wellFormed = true)
    (hLayers : params.numLayers ≤ 2 ^ 32) {L L' i i' : Nat}
    (hL : L < 2 ^ (params.numLayers * params.subtreeHeight))
    (hL' : L' < 2 ^ (params.numLayers * params.subtreeHeight))
    (hi : i < params.numLayers) (hi' : i' < params.numLayers)
    (h : wotsPosAddr params L i = wotsPosAddr params L' i') :
    i = i' ∧ L / 2 ^ (i * params.subtreeHeight) = L' / 2 ^ (i' * params.subtreeHeight) := by
  obtain ⟨_, _, hH, _, hDH, _⟩ := params.wellFormed_facts hWf
  rw [wotsPosAddr_eq, wotsPosAddr_eq] at h
  obtain ⟨h1, h23⟩ := Prod.mk.inj h
  obtain ⟨h2, h3⟩ := Prod.mk.inj h23
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  rw [h32] at hLayers
  have hii : i = i' := uint32_ofNat_inj (Nat.lt_of_lt_of_le hi hLayers)
    (Nat.lt_of_lt_of_le hi' hLayers) h1
  subst hii
  refine ⟨rfl, ?_⟩
  have hP : 2 ^ params.subtreeHeight ≤ 1073741824 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) hH) (by decide)
  have hPpos : 0 < 2 ^ params.subtreeHeight := Nat.two_pow_pos _
  have hB : 2 ^ (params.numLayers * params.subtreeHeight) ≤ 4611686018427387904 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) hDH) (by decide)
  have hG : L / 2 ^ (i * params.subtreeHeight) ≤ L := Nat.div_le_self _ _
  have hG' : L' / 2 ^ (i * params.subtreeHeight) ≤ L' := Nat.div_le_self _ _
  have hT : L / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight ≤
      L / 2 ^ (i * params.subtreeHeight) := Nat.div_le_self _ _
  have hT' : L' / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight ≤
      L' / 2 ^ (i * params.subtreeHeight) := Nat.div_le_self _ _
  have hK := Nat.mod_lt (L / 2 ^ (i * params.subtreeHeight)) hPpos
  have hK' := Nat.mod_lt (L' / 2 ^ (i * params.subtreeHeight)) hPpos
  have e2 := uint64_ofNat_inj (Nat.lt_of_le_of_lt hT (by omega)) (Nat.lt_of_le_of_lt hT' (by omega)) h2
  have e3 := uint32_ofNat_inj (Nat.lt_of_lt_of_le hK (by omega)) (Nat.lt_of_lt_of_le hK' (by omega)) h3
  have d1 := Nat.div_add_mod (L / 2 ^ (i * params.subtreeHeight)) (2 ^ params.subtreeHeight)
  have d2 := Nat.div_add_mod (L' / 2 ^ (i * params.subtreeHeight)) (2 ^ params.subtreeHeight)
  rw [e2, e3] at d1
  exact d1.symm.trans d2

/-- `H_msg` digest that selects the FORS leaves of `(msg, sig)`. -/
def sigForsDigest (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) : List UInt8 :=
  thHashMsg suite sig.rRand pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot msg) 0
    (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
    (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) sig.msgTswCtr

/-- Flattened FORS leaf index opened by `(msg, sig)` in FORS tree `j`. -/
def sigForsLeafIdx (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) (j : Nat) : Nat :=
  j * 2 ^ params.forsHeight +
    (deriveForsIndices params.forsTrees params.forsHeight
      (sigForsDigest suite params pk msg sig)).getD j 0

/-- FORS leaf addresses `(tree, keypair, leaf)` opened by one signature, as encoded in `HashAdrs`. -/
def sigForsLeafAddrs (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) : List (UInt64 × UInt32 × UInt32) :=
  (List.range params.forsTrees).map fun j =>
    (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight),
     UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight),
     UInt32.ofNat (sigForsLeafIdx suite params pk msg sig j))

/-- Every FORS leaf address opened anywhere in the signing log. -/
def logForsLeafAddrs (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey) :
    List (List UInt8 × PqHashSig) → List (UInt64 × UInt32 × UInt32)
  | [] => []
  | e :: rest => sigForsLeafAddrs suite params pk e.1 e.2 ++ logForsLeafAddrs suite params pk rest

/-- **FORS interleaved target-subset-resilience break.** The forged message is absent from the log,
    the profile has at least one FORS tree, and every FORS leaf address selected by the forged
    `(R, message, counter, leaf)` digest was already opened by a logged signature. -/
structure ForsItsrBreak (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig) : Prop where
  fresh : ∀ e ∈ log, e.1 ≠ msgStar
  trees_pos : 0 < params.forsTrees
  covered : ∀ a ∈ sigForsLeafAddrs suite params pk msgStar sigStar,
    a ∈ logForsLeafAddrs suite params pk log

/-- Hash inputs fixed by the honest key and the signing log: Merkle nodes of every XMSS and FORS
    tree, WOTS public-key and FORS-root compressions, every honest chain step, and the `H_msg`
    inputs of the layers of logged signatures. -/
inductive HonestHashTarget (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) : List UInt8 → Prop where
  | xmssNode (layer : UInt32) (tree : UInt64) (h n : Nat) :
      HonestHashTarget suite params sk log
        (thPreimage tagThH sk.pkSeed ⟨layer, tree, .tree, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
          [computeMerkleNode suite sk.pkSeed layer tree .tree
             (computeWotsPk suite params sk layer tree) h (2 * n),
           computeMerkleNode suite sk.pkSeed layer tree .tree
             (computeWotsPk suite params sk layer tree) h (2 * n + 1)])
  | forsNode (tree : UInt64) (kp h n : Nat) :
      HonestHashTarget suite params sk log
        (thPreimage tagThH sk.pkSeed ⟨0, tree, .forsTree, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
          [computeMerkleNode suite sk.pkSeed 0 tree .forsTree (forsLeafFn suite sk tree kp) h (2 * n),
           computeMerkleNode suite sk.pkSeed 0 tree .forsTree (forsLeafFn suite sk tree kp) h (2 * n + 1)])
  | wotsPk (layer : UInt32) (tree : UInt64) (kp : Nat) :
      HonestHashTarget suite params sk log
        (thPreimage tagThTl sk.pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
          ((List.range params.ell1).map fun r =>
            honestChainNode suite sk layer tree kp r (params.w - 1)))
  | forsRoots (tree : UInt64) (kp : Nat) :
      HonestHashTarget suite params sk log
        (thPreimage tagThTl sk.pkSeed ⟨0, tree, .forsRoots, UInt32.ofNat kp, 0, 0⟩
          ((List.range params.forsTrees).map fun j =>
            computeMerkleNode suite sk.pkSeed 0 tree .forsTree (forsLeafFn suite sk tree kp)
              params.forsHeight j))
  | chainStep (layer : UInt32) (tree : UInt64) (kp r step : Nat) :
      HonestHashTarget suite params sk log
        (thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat step⟩
          [honestChainNode suite sk layer tree kp r step])
  | signedDigest (e : List UInt8 × PqHashSig) (he : e ∈ log) (i : Nat) (hi : i < params.numLayers) :
      HonestHashTarget suite params sk log
        (thPreimage tagHMsg sk.pkSeed
          ⟨UInt32.ofNat i,
           UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight),
           .wotsHash,
           UInt32.ofNat (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight),
           0, UInt32.ofNat (e.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr⟩
          [[], (derivePublicKey suite params sk).pkRoot,
           honestLayerRoot suite params sk i (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)),
           be 4 (e.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr])

/-- **Target-collision break.** A hash input different from an honest target (as fixed by the key
    and the log) with the same raw hash value. The winning condition does not constrain where the
    second input comes from; the proofs below compute it from the forged signature. For the
    `signedDigest` targets the colliding input may carry a different counter tweak, so that case is
    a collision on the keyed message hash rather than a same-tweak second preimage. -/
inductive SmTcrBreak (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) : Prop where
  | mk (target forged : List UInt8) (honest : HonestHashTarget suite params sk log target)
      (ne : forged ≠ target) (collides : suite.rawHash forged = suite.rawHash target)

/-- **One-way preimage break carried by the forged signature itself.**
    `fors`: the secret opened in FORS tree `j` of the forgery hashes to the honest leaf hash at an
    address that no logged signature opened.
    `wots`: the chain value in layer `i`, chain `r` of the forgery hashes (at step `step`) to the
    honest chain node `step + 1`, and every logged signature that used a WOTS key with the same
    address disclosed that chain only at a strictly later step. -/
inductive PreimageBreak (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig) : Prop where
  | fors (j : Nat) (hj : j < params.forsTrees)
      (unrevealed :
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight),
         UInt32.ofNat (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight),
         UInt32.ofNat (sigForsLeafIdx suite params (derivePublicKey suite params sk) msgStar sigStar j)) ∉
          logForsLeafAddrs suite params (derivePublicKey suite params sk) log)
      (inverts :
        forsLeafHashFromSecret suite sk.pkSeed
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)
          (sigForsLeafIdx suite params (derivePublicKey suite params sk) msgStar sigStar j)
          (sigStar.forsOpenings.getD j ⟨[], []⟩).secretVal =
        forsLeafFn suite sk (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)
          (sigForsLeafIdx suite params (derivePublicKey suite params sk) msgStar sigStar j))
  | wots (i : Nat) (hi : i < params.numLayers) (r : Nat) (hr : r < params.ell1)
      (step : Nat) (hstep : step + 1 ≤ params.w - 1)
      (inverts :
        thChainF suite sk.pkSeed
          ⟨UInt32.ofNat i,
           UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight),
           .wotsHash,
           UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight),
           UInt32.ofNat r, UInt32.ofNat step⟩
          ((sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r []) =
        honestChainNode suite sk (UInt32.ofNat i)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight) r (step + 1))
      (unrevealed : ∀ e ∈ log, ∀ i', i' < params.numLayers →
        wotsPosAddr params e.2.leafGlobalIdx i' = wotsPosAddr params sigStar.leafGlobalIdx i →
        step < (logLayerDigits suite params sk e.2 i').getD r 0)

/-- Regression: with nothing signed, no FORS leaf is covered, so the ITSR branch is empty. -/
theorem forsItsrBreak_empty_log (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msgStar : List UInt8) (sigStar : PqHashSig) :
    ¬ ForsItsrBreak suite params pk [] msgStar sigStar := by
  intro hB
  have hMem : (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight),
      UInt32.ofNat (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight),
      UInt32.ofNat (sigForsLeafIdx suite params pk msgStar sigStar 0)) ∈
      sigForsLeafAddrs suite params pk msgStar sigStar :=
    List.mem_map.mpr ⟨0, List.mem_range.mpr hB.trees_pos, rfl⟩
  have hIn := hB.covered _ hMem
  cases hIn

/-! ### Structure of logged signatures -/

theorem grindTswCounterAux_det {suite : TweakableHashSuite} {w ell1 target : Nat}
    {rRand pkSeed pkRoot mu : List UInt8} {layerIdx : UInt32} {treeIdx : UInt64} {kpIdx : UInt32} :
    ∀ (fuel fuel' curCtr : Nat) {a b : Nat × List Nat × List UInt8},
      grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr fuel = some a →
      grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr fuel' = some b →
      a = b
  | 0, _, _, _, _, h, _ => by cases h
  | _ + 1, 0, _, _, _, _, h' => by cases h'
  | fuel + 1, fuel' + 1, curCtr, a, b, h, h' => by
    simp only [grindTswCounterAux] at h h'
    cases hChk : checkTargetSum w ell1 target
        (extractBaseWDigits w ell1 (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr))
    · rw [hChk] at h h'
      simp only [Bool.false_eq_true, ↓reduceIte] at h h'
      exact grindTswCounterAux_det fuel fuel' (curCtr + 1) h h'
    · rw [hChk] at h h'
      simp only [↓reduceIte, Option.some.injEq] at h h'
      exact h.symm.trans h'

/-- Layer `j` of a successful `signHypertreeLayers` run: its counter is the grinder's output on the
    honest message of that layer and its chain values are the honest nodes at the ground digits. -/
theorem signHypertreeLayers_layer (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot : List UInt8) (maxGrind : Nat) :
    ∀ (rem i0 g0 : Nat) (rand cur : List UInt8) (sigs : List LayerXmssSig),
      signHypertreeLayers suite params sk pkRoot rand maxGrind i0 g0 cur rem = some sigs →
      ∀ j, j < rem →
        ∃ digits hm,
          grindTswCounterAux suite params.w params.ell1 params.targetSum
            (if j = 0 then rand else []) sk.pkSeed pkRoot
            (if j = 0 then cur else computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i0 + j - 1))
              (UInt64.ofNat (g0 / 2 ^ (j * params.subtreeHeight))))
            (UInt32.ofNat (i0 + j))
            (UInt64.ofNat (g0 / 2 ^ (j * params.subtreeHeight) / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (g0 / 2 ^ (j * params.subtreeHeight) % 2 ^ params.subtreeHeight)) 0 maxGrind =
            some ((sigs.getD j ⟨0, [], []⟩).tswCtr, digits, hm) ∧
          (sigs.getD j ⟨0, [], []⟩).wotsChains = (List.range params.ell1).map fun r =>
            honestChainNode suite sk (UInt32.ofNat (i0 + j))
              (UInt64.ofNat (g0 / 2 ^ (j * params.subtreeHeight) / 2 ^ params.subtreeHeight))
              (g0 / 2 ^ (j * params.subtreeHeight) % 2 ^ params.subtreeHeight) r (digits.getD r 0)
  | 0, _, _, _, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | rem + 1, i0, g0, rand, cur, sigs, h, j, hj => by
    rw [signHypertreeLayers_succ] at h
    dsimp only at h
    split at h
    · cases h
    · rename_i ctr digits hm hG
      split at h
      · cases h
      · rename_i restSigs hRest
        simp only [Option.some.injEq] at h
        subst h
        cases j with
        | zero =>
          refine ⟨digits, hm, ?_, ?_⟩
          · simpa only [↓reduceIte, Nat.zero_mul, Nat.pow_zero, Nat.div_one, Nat.add_zero,
              List.getD_cons_zero] using hG
          · simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one, Nat.add_zero, List.getD_cons_zero]
            rfl
        | succ j =>
          obtain ⟨dg, hm', hG', hC'⟩ := signHypertreeLayers_layer suite params sk pkRoot maxGrind rem
            (i0 + 1) (g0 / 2 ^ params.subtreeHeight) [] _ restSigs hRest j (Nat.lt_of_succ_lt_succ hj)
          have hDiv : g0 / 2 ^ params.subtreeHeight / 2 ^ (j * params.subtreeHeight) =
              g0 / 2 ^ ((j + 1) * params.subtreeHeight) := by
            rw [Nat.div_div_eq_div_mul, ← Nat.pow_add,
              show params.subtreeHeight + j * params.subtreeHeight = (j + 1) * params.subtreeHeight by
                rw [Nat.succ_mul, Nat.add_comm]]
          have hIdx : i0 + 1 + j = i0 + (j + 1) := by omega
          have hRoot :
              (if j = 0 then
                computeXmssSubtreeRoot suite params sk (UInt32.ofNat i0)
                  (UInt64.ofNat (g0 / 2 ^ params.subtreeHeight))
               else computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i0 + 1 + j - 1))
                  (UInt64.ofNat (g0 / 2 ^ params.subtreeHeight / 2 ^ (j * params.subtreeHeight)))) =
              computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i0 + (j + 1) - 1))
                (UInt64.ofNat (g0 / 2 ^ ((j + 1) * params.subtreeHeight))) := by
            cases j with
            | zero => simp only [↓reduceIte, Nat.zero_add, Nat.one_mul, Nat.add_sub_cancel]
            | succ j' =>
              rw [hDiv]
              simp only [Nat.add_one_ne_zero, ↓reduceIte]
              rw [show i0 + 1 + (j' + 1) - 1 = i0 + (j' + 1 + 1) - 1 by omega]
          rw [hRoot] at hG'
          rw [hDiv, hIdx] at hG' hC'
          refine ⟨dg, hm', ?_, ?_⟩
          · simpa only [Nat.add_one_ne_zero, ↓reduceIte, ite_self, List.getD_cons_succ] using hG'
          · simpa only [List.getD_cons_succ] using hC'

/-- What a stateless signing log guarantees about one logged signature. -/
structure StatelessLogEntryOk (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (sig : PqHashSig) : Prop where
  leaf_lt : sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)
  layer : ∀ i, i < params.numLayers → ∃ fuel digits hm,
    grindTswCounterAux suite params.w params.ell1 params.targetSum [] sk.pkSeed
      (derivePublicKey suite params sk).pkRoot
      (honestLayerRoot suite params sk i (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))
      (UInt32.ofNat i)
      (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
      (UInt32.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
      0 fuel = some ((sig.layerSigs.getD i ⟨0, [], []⟩).tswCtr, digits, hm) ∧
    (sig.layerSigs.getD i ⟨0, [], []⟩).wotsChains = (List.range params.ell1).map fun r =>
      honestChainNode suite sk (UInt32.ofNat i)
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
        (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight) r (digits.getD r 0)

theorem signingOracleLog_entryOk (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List PqSigningQuery) (hStateless : params.statefulJorts = false)
    (e : List UInt8 × PqHashSig) (he : e ∈ signingOracleLog suite params sk queries) :
    StatelessLogEntryOk suite params sk e.2 := by
  obtain ⟨q, _, _, hs⟩ := signingOracleLog_generated suite params sk queries e.1 e.2 he
  obtain ⟨_, hLt, _, hL, _, hLs⟩ :=
    evalSingleSign_stateless_inv suite params sk q.message q.randomness q.leaf q.grindLimit e.2 hStateless hs
  refine ⟨hL ▸ hLt, ?_⟩
  intro i hi
  obtain ⟨dg, hm, hG, hC⟩ := signHypertreeLayers_layer suite params sk _ q.grindLimit
    params.numLayers 0 q.leaf [] _ e.2.layerSigs hLs i hi
  rw [← hL] at hG hC
  simp only [Nat.zero_add, ite_self] at hG hC
  have hRootEq :
      (if i = 0 then
        computeForsPk suite params sk (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (e.2.leafGlobalIdx % 2 ^ params.subtreeHeight)
       else computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1))
          (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))) =
      honestLayerRoot suite params sk i (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) := by
    rw [honestLayerRoot_eq]
    cases i with
    | zero => simp only [↓reduceIte, Nat.zero_mul, Nat.pow_zero, Nat.div_one]
    | succ i => simp only [Nat.add_one_ne_zero, ↓reduceIte]
  rw [hRootEq] at hG
  exact ⟨q.grindLimit, dg, hm, hG, hC⟩

theorem logLayerDigits_valid {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {sig : PqHashSig} (hOk : StatelessLogEntryOk suite params sk sig)
    (i : Nat) (hi : i < params.numLayers) :
    checkTargetSum params.w params.ell1 params.targetSum (logLayerDigits suite params sk sig i) = true := by
  obtain ⟨fuel, dg, hm, hG, _⟩ := hOk.layer i hi
  obtain ⟨hmEq, hdEq, hChk⟩ := grindTswCounterAux_sound hG
  rw [logLayerDigits_eq, ← hmEq, ← hdEq]
  exact hChk

/-- The log discloses exactly the honest chain nodes at `logLayerDigits`. -/
theorem logLayer_chains_revealed {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {sig : PqHashSig} (hOk : StatelessLogEntryOk suite params sk sig)
    (i : Nat) (hi : i < params.numLayers) (r : Nat) (hr : r < params.ell1) :
    (sig.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r [] =
      honestChainNode suite sk (UInt32.ofNat i)
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
        (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight) r
        ((logLayerDigits suite params sk sig i).getD r 0) := by
  obtain ⟨fuel, dg, hm, hG, hC⟩ := hOk.layer i hi
  obtain ⟨hmEq, hdEq, _⟩ := grindTswCounterAux_sound hG
  rw [hC, list_getD_map_range params.ell1 _ [] hr, logLayerDigits_eq, ← hmEq, ← hdEq]

/-- Two logged signatures through the same hypertree position disclose the same digits there. -/
theorem logLayerDigits_consistent {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {sig₁ sig₂ : PqHashSig}
    (hOk₁ : StatelessLogEntryOk suite params sk sig₁) (hOk₂ : StatelessLogEntryOk suite params sk sig₂)
    (i : Nat) (hi : i < params.numLayers)
    (hPos : sig₁.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) =
      sig₂.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) :
    logLayerDigits suite params sk sig₁ i = logLayerDigits suite params sk sig₂ i := by
  obtain ⟨f₁, dg₁, hm₁, hG₁, _⟩ := hOk₁.layer i hi
  obtain ⟨f₂, dg₂, hm₂, hG₂, _⟩ := hOk₂.layer i hi
  rw [hPos] at hG₁
  have hEq := grindTswCounterAux_det f₁ f₂ 0 hG₁ hG₂
  have hCtr := (Prod.mk.inj hEq).1
  rw [logLayerDigits_eq, logLayerDigits_eq, hPos, hCtr]


/-! ### Forgery-side lemmas -/

/-- An authentication path that reaches the honest Merkle node starts from the honest leaf, or
    exhibits a second input colliding with an honest node input (reported through `hCol`). -/
theorem walkMerkle_meets_honest (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (leafFn : Nat → List UInt8) (P : Prop)
    (hCol : ∀ (h n : Nat) (forged : List UInt8),
      forged ≠ thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
        [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
         computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)] →
      suite.rawHash forged = suite.rawHash
        (thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
          [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
           computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)]) → P) :
    ∀ (h nodeIdx localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8)),
      localIdx < 2 ^ h →
      walkMerkleAuthPath suite pkSeed layer tree kind h nodeIdx localIdx leaf path =
        some (computeMerkleNode suite pkSeed layer tree kind leafFn h nodeIdx) →
      leaf = leafFn (nodeIdx * 2 ^ h + localIdx) ∨ P
  | 0, nodeIdx, localIdx, leaf, path, hLt, hW => by
    cases path with
    | nil =>
      simp only [walkMerkleAuthPath, computeMerkleNode, Option.some.injEq] at hW
      have h0 : localIdx = 0 := by
        rw [Nat.pow_zero] at hLt
        omega
      rw [h0, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
      exact .inl hW
    | cons _ _ => simp [walkMerkleAuthPath] at hW
  | h + 1, nodeIdx, localIdx, leaf, path, hLt, hW => by
    cases path with
    | nil => simp [walkMerkleAuthPath] at hW
    | cons sib rest =>
      have hMul : nodeIdx * 2 ^ (h + 1) = (2 * nodeIdx) * 2 ^ h := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (nodeIdx * 2 ^ h) 2, Nat.mul_assoc]
      rw [computeMerkleNode_succ] at hW
      by_cases hHalf : localIdx < 2 ^ h
      · simp only [walkMerkleAuthPath, hHalf, ↓reduceIte] at hW
        cases hSub : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx) localIdx leaf rest with
        | none => rw [hSub] at hW; cases hW
        | some sub =>
          rw [hSub] at hW
          simp only [Option.some.injEq] at hW
          rcases thCall_eq_cases suite hW with ⟨_, _, _, hArgs⟩ | ⟨hNe, hHash⟩
          · simp only [List.cons.injEq, and_true] at hArgs
            rw [hArgs.1] at hSub
            rcases walkMerkle_meets_honest suite pkSeed layer tree kind leafFn P hCol h (2 * nodeIdx)
              localIdx leaf rest hHalf hSub with hLeaf | hP
            · left; rw [hMul]; exact hLeaf
            · exact .inr hP
          · exact .inr (hCol h nodeIdx _ hNe hHash)
      · simp only [walkMerkleAuthPath, hHalf, ↓reduceIte] at hW
        cases hSub : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx + 1)
            (localIdx - 2 ^ h) leaf rest with
        | none => rw [hSub] at hW; cases hW
        | some sub =>
          rw [hSub] at hW
          simp only [Option.some.injEq] at hW
          have hSubLt : localIdx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hLt; omega
          have hIdxEq : nodeIdx * 2 ^ (h + 1) + localIdx =
              (2 * nodeIdx + 1) * 2 ^ h + (localIdx - 2 ^ h) := by
            rw [hMul, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_not_lt hHalf)]
          rcases thCall_eq_cases suite hW with ⟨_, _, _, hArgs⟩ | ⟨hNe, hHash⟩
          · simp only [List.cons.injEq, and_true] at hArgs
            rw [hArgs.2] at hSub
            rcases walkMerkle_meets_honest suite pkSeed layer tree kind leafFn P hCol h (2 * nodeIdx + 1)
              (localIdx - 2 ^ h) leaf rest hSubLt hSub with hLeaf | hP
            · left; rw [hIdxEq]; exact hLeaf
            · exact .inr hP
          · exact .inr (hCol h nodeIdx _ hNe hHash)

/-- A chain segment that reaches the honest node `s + k` starts at the honest node `s`, or some
    step collides with an honest chain-step input. -/
theorem wotsChain_meets_honest (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig))
    (layer : UInt32) (tree : UInt64) (kp r : Nat) :
    ∀ (k s : Nat) (x : List UInt8),
      wotsChainSteps suite sk.pkSeed layer tree kp r s k x =
        honestChainNode suite sk layer tree kp r (s + k) →
      x = honestChainNode suite sk layer tree kp r s ∨ SmTcrBreak suite params sk log
  | 0, s, x, h => by
    rw [wotsChainSteps_zero, Nat.add_zero] at h
    exact .inl h
  | k + 1, s, x, h => by
    rw [wotsChainSteps_succ] at h
    dsimp only at h
    rw [show s + (k + 1) = (s + 1) + k by omega] at h
    rcases wotsChain_meets_honest suite params sk log layer tree kp r k (s + 1) _ h with hF | hB
    · rw [← honestChainNode_succ, thChainF_eq, thChainF_eq] at hF
      rcases thCall_eq_cases suite hF with ⟨_, _, _, hArgs⟩ | ⟨hNe, hHash⟩
      · exact .inl (List.cons.inj hArgs).1
      · exact .inr (SmTcrBreak.mk _ _ (.chainStep layer tree kp r s) hNe hHash)
    · exact .inr hB

/-- One hypertree layer of an accepted forgery whose signed message differs from the honest one
    while its XMSS root is the honest one. -/
theorem layer_divergence_break (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8)
    (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64)) (hWf : params.wellFormed = true)
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (hLog : ∀ e ∈ log, StatelessLogEntryOk suite params sk e.2)
    (hStarLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    (i : Nat) (hi : i < params.numLayers) (cur : List UInt8)
    (G : Nat) (hG : G = sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight))
    (T : UInt64) (hT : T = UInt64.ofNat (G / 2 ^ params.subtreeHeight))
    (KP : Nat) (hKP : KP = G % 2 ^ params.subtreeHeight)
    (ls : LayerXmssSig) (hLs : ls = sigStar.layerSigs.getD i ⟨0, [], []⟩)
    (digF : List Nat)
    (hDigF : digF = extractBaseWDigits params.w params.ell1
      (thHashMsg suite [] sk.pkSeed (derivePublicKey suite params sk).pkRoot cur (UInt32.ofNat i) T
        (UInt32.ofNat KP) ls.tswCtr))
    (hDiff : cur ≠ honestLayerRoot suite params sk i G)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hWalk : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) T .tree params.subtreeHeight 0 KP
        (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) T KP digF ls.wotsChains)
        ls.authPath =
      some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat i) T)) :
    SmTcrBreak suite params sk log ∨ PreimageBreak suite params sk log msgStar sigStar := by
  have hStrict : params.targetSum < (params.w - 1) * params.ell1 := by
    rw [PqHashParams.targetSum_eq]
    rcases hGeom with ⟨hw, hell⟩ | ⟨hw, hell⟩ <;> rw [hw, hell] <;> decide
  have hInj : ∀ {a b : List UInt8}, a.length = 64 → b.length = 64 →
      extractBaseWDigits params.w params.ell1 a = extractBaseWDigits params.w params.ell1 b →
      a.take 32 = b.take 32 := by
    intro a b ha hb hd
    rcases hGeom with ⟨hw, hell⟩ | ⟨hw, hell⟩
    · rw [hw, hell] at hd
      exact extractBaseWDigits_4_128_take32_eq ha hb hd
    · rw [hw, hell] at hd
      exact extractBaseWDigits_base16_prefix_injective 32 (by omega) (by omega) hd
  have hKpLt : KP < 2 ^ params.subtreeHeight := by
    rw [hKP]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [computeXmssSubtreeRoot_eq] at hWalk
  refine (walkMerkle_meets_honest suite sk.pkSeed (UInt32.ofNat i) T .tree
      (computeWotsPk suite params sk (UInt32.ofNat i) T) (SmTcrBreak suite params sk log)
      (fun h n forged hNe hHash =>
        SmTcrBreak.mk _ forged (.xmssNode (UInt32.ofNat i) T h n) hNe hHash)
      params.subtreeHeight 0 KP _ _ hKpLt hWalk).elim (fun hPk => ?_) (fun hB => .inl hB)
  rw [Nat.zero_mul, Nat.zero_add, recoverWotsPkFromSig_eq, computeWotsPk_eq, thTweakTl_eq,
    thTweakTl_eq] at hPk
  refine (thCall_eq_cases suite hPk).elim (fun hAll => ?_)
    (fun hc => .inl (SmTcrBreak.mk _ _ (.wotsPk (UInt32.ofNat i) T KP) hc.1 hc.2))
  obtain ⟨_, _, _, hEnds⟩ := hAll
  rw [recoverWotsEndpoints_eq] at hEnds
  obtain ⟨hLenF, hBoundF, hSumF⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
  have hChain : ∀ r, r < params.ell1 →
      ls.wotsChains.getD r [] =
        honestChainNode suite sk (UInt32.ofNat i) T KP r (digF.getD r 0) ∨
      SmTcrBreak suite params sk log := by
    intro r hr
    have hAt := congrArg (fun l => l.getD r []) hEnds
    rw [list_getD_map_range params.ell1 _ [] hr, list_getD_map_range params.ell1 _ [] hr] at hAt
    have hrLen : r < digF.length := by rw [hLenF]; exact hr
    have hdLt : digF.getD r 0 < params.w := by
      rw [list_getD_eq_getElem digF 0 hrLen]
      exact hBoundF _ (List.getElem_mem hrLen)
    have hSum : digF.getD r 0 + (params.w - 1 - digF.getD r 0) = params.w - 1 := by omega
    exact wotsChain_meets_honest suite params sk log (UInt32.ofNat i) T KP r _ _ _
      (by rw [hSum, honestChainNode_eq]; exact hAt)
  have hInv : ∀ r, ls.wotsChains.getD r [] =
        honestChainNode suite sk (UInt32.ofNat i) T KP r (digF.getD r 0) →
      thChainF suite sk.pkSeed
        ⟨UInt32.ofNat i,
         UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight),
         .wotsHash,
         UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight),
         UInt32.ofNat r, UInt32.ofNat (digF.getD r 0)⟩
        ((sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r []) =
      honestChainNode suite sk (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight) r
        (digF.getD r 0 + 1) := by
    intro r hVal
    rw [← hLs, ← hG, ← hKP, ← hT, hVal]
    exact honestChainNode_succ suite sk (UInt32.ofNat i) T KP r (digF.getD r 0)
  have hSearch := list_search
    (fun e : List UInt8 × PqHashSig => ∃ i', i' < params.numLayers ∧
      wotsPosAddr params e.2.leafGlobalIdx i' = wotsPosAddr params sigStar.leafGlobalIdx i)
    (fun e => by
      rcases bounded_search
        (fun i' => wotsPosAddr params e.2.leafGlobalIdx i' = wotsPosAddr params sigStar.leafGlobalIdx i)
        (fun i' => Decidable.em _) params.numLayers with ⟨i', h1, h2⟩ | hNone
      · exact .inl ⟨i', h1, h2⟩
      · exact .inr (fun ⟨i', h1, h2⟩ => hNone i' h1 h2)) log
  rcases hSearch with ⟨e, he, i', hi', hAddr⟩ | hNoUse
  · have hOk := hLog e he
    obtain ⟨hii, hPos⟩ := wotsPosAddr_inj params hWf hLayers hOk.leaf_lt hStarLt hi' hi hAddr
    rw [hii, ← hG] at hPos
    have hValidH := logLayerDigits_valid hOk i hi
    by_cases hDigEq : digF = logLayerDigits suite params sk e.2 i
    · left
      rw [hDigF, logLayerDigits_eq] at hDigEq
      have hTake := hInj (thHashMsg_length _ _ _ _ _ _ _ _ _)
        (thHashMsg_length _ _ _ _ _ _ _ _ _) hDigEq
      rw [thHashMsg_eq, thHashMsg_eq, List.take_left' (thCall_length _ _ _ _ _),
        List.take_left' (thCall_length _ _ _ _ _)] at hTake
      rcases thCall_eq_cases suite hTake with ⟨_, _, _, hArgs⟩ | ⟨hNe, hHash⟩
      · simp only [List.cons.injEq] at hArgs
        rw [hPos] at hArgs
        exact absurd hArgs.2.2.1 hDiff
      · exact SmTcrBreak.mk _ _ (.signedDigest e he i hi) hNe hHash
    · obtain ⟨r, hr2, hr1, hlt, hbw⟩ :=
        (tsw_incomparable_no_chain_forgery hValidH hTsw (fun hEq => hDigEq hEq.symm)).2
      have hr : r < params.ell1 := by rw [← hLenF]; exact hr2
      refine (hChain r hr).elim (fun hVal => ?_) (fun hB => .inl hB)
      right
      have hF : digF.getD r 0 = digF[r] := list_getD_eq_getElem digF 0 hr2
      have hH : (logLayerDigits suite params sk e.2 i).getD r 0 =
          (logLayerDigits suite params sk e.2 i)[r] := list_getD_eq_getElem _ 0 hr1
      refine PreimageBreak.wots i hi r hr (digF.getD r 0) (by omega) (hInv r hVal) ?_
      intro e' he' i'' hi'' hAddr'
      obtain ⟨hii', hPos'⟩ :=
        wotsPosAddr_inj params hWf hLayers (hLog e' he').leaf_lt hStarLt hi'' hi hAddr'
      rw [hii', ← hG] at hPos'
      rw [hii', logLayerDigits_consistent (hLog e' he') hOk i hi (hPos'.trans hPos.symm)]
      omega
  · cases hFind : findDigitLt (params.w - 1) digF with
    | none =>
      exfalso
      have hAllGe := findDigitLt_none_all_ge (params.w - 1) digF hFind
      have hGe := sumDigits_ge_mul_of_all_ge (params.w - 1) digF hAllGe
      rw [hLenF, hSumF] at hGe
      omega
    | some r =>
      obtain ⟨hrLen, hrVal⟩ := findDigitLt_sound (params.w - 1) hFind
      have hr : r < params.ell1 := by rw [← hLenF]; exact hrLen
      refine (hChain r hr).elim (fun hVal => ?_) (fun hB => .inl hB)
      right
      have hF : digF.getD r 0 = digF[r] := list_getD_eq_getElem digF 0 hrLen
      refine PreimageBreak.wots i hi r hr (digF.getD r 0) (by omega) (hInv r hVal) ?_
      intro e' he' i'' hi'' hAddr'
      exact absurd ⟨i'', hi'', hAddr'⟩ (hNoUse e' he')

theorem bool_of_not_not_true {b : Bool} (h : ¬ (!b) = true) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

/-- Walk of the hypertree layers of an accepted forgery from layer `i` upward. -/
theorem hypertree_walk_break (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8)
    (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64)) (hWf : params.wellFormed = true)
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (hLog : ∀ e ∈ log, StatelessLogEntryOk suite params sk e.2)
    (hStarLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) :
    ∀ (sigs : List LayerXmssSig) (i : Nat) (cur : List UInt8),
      sigs ≠ [] →
      (∀ j, sigs.getD j ⟨0, [], []⟩ = sigStar.layerSigs.getD (i + j) ⟨0, [], []⟩) →
      i + sigs.length = params.numLayers →
      verifyHypertreeLayers suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot [] i
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) cur sigs =
        some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight)))) →
      cur = honestLayerRoot suite params sk i (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) ∨
      SmTcrBreak suite params sk log ∨ PreimageBreak suite params sk log msgStar sigStar
  | [], _, _, hNe, _, _, _ => absurd rfl hNe
  | lsig :: rest, i, cur, _, hAlign, hLenEq, hVer => by
    have hi : i < params.numLayers := by
      rw [← hLenEq, List.length_cons]
      omega
    have hStep : sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight =
        sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight) := by
      have h := div_pow_mul_pow_mul sigStar.leafGlobalIdx i 1 params.subtreeHeight
      rw [Nat.one_mul] at h
      exact h
    rw [verifyHypertreeLayers_cons] at hVer
    dsimp only at hVer
    split at hVer
    · cases hVer
    · rename_i hTswN
      have hTsw := bool_of_not_not_true hTswN
      split at hVer
      · cases hVer
      · split at hVer
        · cases hVer
        · rename_i next hWalk
          have hNext : next = computeXmssSubtreeRoot suite params sk (UInt32.ofNat i)
              (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight)) ∨
              SmTcrBreak suite params sk log ∨ PreimageBreak suite params sk log msgStar sigStar := by
            cases rest with
            | nil =>
              rw [verifyHypertreeLayers_nil] at hVer
              simp only [Option.some.injEq] at hVer
              have hD : params.numLayers = i + 1 := by
                rw [← hLenEq, List.length_cons, List.length_nil]
              rw [hD, Nat.add_sub_cancel] at hVer
              rw [hStep]
              exact .inl hVer
            | cons r0 rs =>
              rw [hStep] at hVer
              rcases hypertree_walk_break suite params sk log msgStar sigStar hGeom hWf hLayers hLog
                  hStarLt (r0 :: rs) (i + 1) next (List.cons_ne_nil r0 rs)
                  (fun j => by
                    have h := hAlign (j + 1)
                    rw [List.getD_cons_succ] at h
                    rw [h, show i + (j + 1) = i + 1 + j by omega])
                  (by rw [← hLenEq, List.length_cons, List.length_cons, List.length_cons]; omega)
                  hVer with hEq | hB
              · left
                rw [hEq, honestLayerRoot_eq, hStep]
                simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
              · exact .inr hB
          rcases hNext with hNext | hB
          · by_cases hCur : cur = honestLayerRoot suite params sk i
                (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight))
            · exact .inl hCur
            · right
              rw [hNext] at hWalk
              have hLs : lsig = sigStar.layerSigs.getD i ⟨0, [], []⟩ := by
                have h := hAlign 0
                rw [List.getD_cons_zero, Nat.add_zero] at h
                exact h
              exact layer_divergence_break suite params sk log msgStar sigStar hGeom hWf hLayers
                hLog hStarLt i hi cur _ rfl _ rfl _ rfl lsig hLs _ rfl hCur hTsw hWalk
          · exact .inr hB

/-- FORS trees of an accepted forgery whose roots are the honest roots: every opened secret hashes
    to the honest leaf hash, or a Merkle input collides with an honest one. -/
theorem forsRoots_meet_honest (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig))
    (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat) (ops : List ForsTreeOpening)
    (hIdxs : ∀ J, J < params.forsTrees → idxs.getD J 0 < 2 ^ params.forsHeight) :
    ∀ (rem j : Nat) (rootsF : List (List UInt8)),
      j + rem ≤ params.forsTrees →
      recoverForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops j rem = some rootsF →
      rootsF = (List.range rem).map (fun off =>
        computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree (forsLeafFn suite sk tree0 kp0)
          params.forsHeight (j + off)) →
      (∀ off, off < rem →
        forsLeafHashFromSecret suite sk.pkSeed tree0 kp0
          ((j + off) * 2 ^ params.forsHeight + idxs.getD (j + off) 0)
          (ops.getD (j + off) ⟨[], []⟩).secretVal =
        forsLeafFn suite sk tree0 kp0 ((j + off) * 2 ^ params.forsHeight + idxs.getD (j + off) 0)) ∨
      SmTcrBreak suite params sk log
  | 0, _, _, _, _, _ => .inl (fun off h => absurd h (Nat.not_lt_zero off))
  | rem + 1, j, rootsF, hB, hRec, hEq => by
    rw [recoverForsTreeRoots_succ] at hRec
    dsimp only at hRec
    split at hRec
    · cases hRec
    · rename_i rJ hWalk
      split at hRec
      · cases hRec
      · rename_i rsF hRest
        simp only [Option.some.injEq] at hRec
        subst hRec
        rw [list_range_succ_shift_local] at hEq
        simp only [Nat.add_zero, List.cons.injEq] at hEq
        obtain ⟨hrJ, hrs⟩ := hEq
        have hrs' : rsF = (List.range rem).map (fun off =>
            computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree (forsLeafFn suite sk tree0 kp0)
              params.forsHeight (j + 1 + off)) := by
          rw [hrs]
          apply List.map_congr_left
          intro off _
          rw [show j + (off + 1) = j + 1 + off by omega]
        rw [hrJ] at hWalk
        rcases walkMerkle_meets_honest suite sk.pkSeed 0 tree0 .forsTree
            (forsLeafFn suite sk tree0 kp0) (SmTcrBreak suite params sk log)
            (fun h n forged hNe hHash =>
              SmTcrBreak.mk _ forged (.forsNode tree0 kp0 h n) hNe hHash)
            params.forsHeight j (idxs.getD j 0) _ _ (hIdxs j (by omega)) hWalk with hLeaf | hB'
        · rcases forsRoots_meet_honest suite params sk log tree0 kp0 idxs ops hIdxs rem (j + 1) rsF
              (by omega) hRest hrs' with hAll | hB''
          · left
            intro off hoff
            cases off with
            | zero => rw [Nat.add_zero]; exact hLeaf
            | succ off' =>
              have h := hAll off' (by omega)
              rw [show j + 1 + off' = j + (off' + 1) by omega] at h
              exact h
          · exact .inr hB''
        · exact .inr hB'

/-- FORS part of an accepted forgery whose FORS public key is the honest one. -/
theorem fors_break (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hTrees : 0 < params.forsTrees) (hFresh : ∀ e ∈ log, e.1 ≠ msgStar)
    (hRec : recoverForsPk suite params sk.pkSeed
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)
        (sigForsDigest suite params (derivePublicKey suite params sk) msgStar sigStar)
        sigStar.forsOpenings =
      some (computeForsPk suite params sk
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight))) :
    ForsItsrBreak suite params (derivePublicKey suite params sk) log msgStar sigStar ∨
    SmTcrBreak suite params sk log ∨ PreimageBreak suite params sk log msgStar sigStar := by
  rw [recoverForsPk_eq] at hRec
  split at hRec
  · cases hRec
  · dsimp only at hRec
    split at hRec
    · cases hRec
    · rename_i rootsF hRoots
      simp only [Option.some.injEq] at hRec
      rw [computeForsPk_eq] at hRec
      dsimp only at hRec
      rw [thTweakTl_eq, thTweakTl_eq] at hRec
      rcases thCall_eq_cases suite hRec with ⟨_, _, _, hArgs⟩ | ⟨hNe, hHash⟩
      · have hBounds := deriveForsIndices_bounds params.forsTrees params.forsHeight
          (sigForsDigest suite params (derivePublicKey suite params sk) msgStar sigStar)
        have hIdxs : ∀ J, J < params.forsTrees →
            (deriveForsIndices params.forsTrees params.forsHeight
              (sigForsDigest suite params (derivePublicKey suite params sk) msgStar sigStar)).getD J 0 <
              2 ^ params.forsHeight := by
          intro J hJ
          have hJLen : J < (deriveForsIndices params.forsTrees params.forsHeight
              (sigForsDigest suite params (derivePublicKey suite params sk) msgStar sigStar)).length := by
            rw [hBounds.1]; exact hJ
          rw [list_getD_eq_getElem _ 0 hJLen]
          exact hBounds.2 _ (List.getElem_mem hJLen)
        rcases forsRoots_meet_honest suite params sk log _ _ _ _ hIdxs params.forsTrees 0 rootsF
            (by omega) hRoots
            (by
              rw [hArgs]
              apply List.map_congr_left
              intro off _
              rw [Nat.zero_add]) with hAll | hB
        · rcases bounded_search
              (fun j =>
                (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight),
                 UInt32.ofNat (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight),
                 UInt32.ofNat (sigForsLeafIdx suite params (derivePublicKey suite params sk) msgStar sigStar j)) ∉
                  logForsLeafAddrs suite params (derivePublicKey suite params sk) log)
              (fun j => Decidable.em _) params.forsTrees with ⟨j, hj, hUn⟩ | hCov
          · right; right
            have h := hAll j hj
            rw [Nat.zero_add] at h
            exact PreimageBreak.fors j hj hUn h
          · left
            refine ⟨hFresh, hTrees, ?_⟩
            intro a ha
            obtain ⟨j, hj, hEq⟩ := List.mem_map.mp ha
            rw [← hEq]
            exact Decidable.of_not_not (hCov j (List.mem_range.mp hj))
        · exact .inr (.inl hB)
      · exact .inr (.inl (SmTcrBreak.mk _ _
          (.forsRoots (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
            (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)) hNe hHash))

/-- Unpacking of an accepting stateless verification. -/
theorem verifyPqHashSig_stateless_inv (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (hMode : params.statefulJorts = false)
    (h : verifyPqHashSig suite params pk msg sig = true) :
    params.wellFormed = true ∧ sig.layerSigs.length = params.numLayers ∧
    sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) ∧
    ∃ forsPkF,
      recoverForsPk suite params pk.pkSeed
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)
        (sigForsDigest suite params pk msg sig) sig.forsOpenings = some forsPkF ∧
      verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot [] 0 sig.leafGlobalIdx forsPkF
        sig.layerSigs = some pk.pkRoot := by
  unfold verifyPqHashSig at h
  cases hWf : params.wellFormed
  · simp [hWf] at h
  · simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hLen : sig.layerSigs.length = params.numLayers
    · by_cases hLt : sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)
      · simp only [hLen, ne_eq, not_true_eq_false, ↓reduceIte, hLt, decide_true, Bool.not_true,
          Bool.false_eq_true, hMode] at h
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i forsPk hFors
            split at h
            · rename_i top hTop
              exact ⟨rfl, hLen, hLt, forsPk, hFors, by rw [hTop, of_decide_eq_true h]⟩
            · cases h
      · simp [hLt] at h
    · simp [hLen] at h

/-- **Break extraction from an actual signing log** (stateless profiles with
    `(w, ℓ₁) = (4, 128)` or `(16, 64)` and at most `2^32` layers).
    Let `log` be the transcript of the signing oracle under `sk` on arbitrary queries (the caller
    chooses the leaf in this legacy interface). Any accepted signature on a message absent from the
    log yields an ITSR break, a target-collision break, or a preimage break, each stated against
    that same key, log and forgery. This is a `Prop`-level statement proved directly from the
    verifier; it is not a statement about the term `extractFullHypertreeForgery`, whose
    `hUpperOracle` premise ranges over unbounded layer numbers and is not derivable for a
    log-derived oracle (at layer `2^32` it would force a layer-0 entry to carry an XMSS root). -/
theorem hypertree_forgery_break_of_signingLog (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List PqSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hStateless : params.statefulJorts = false)
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (hFresh : ∀ e ∈ signingOracleLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    ForsItsrBreak suite params (derivePublicKey suite params sk)
      (signingOracleLog suite params sk queries) msgStar sigStar ∨
    SmTcrBreak suite params sk (signingOracleLog suite params sk queries) ∨
    PreimageBreak suite params sk (signingOracleLog suite params sk queries) msgStar sigStar := by
  obtain ⟨hWf, hLen, hLt, forsPkF, hFors, hHt⟩ :=
    verifyPqHashSig_stateless_inv suite params _ msgStar sigStar hStateless hAccept
  obtain ⟨hDPos, _, _, _, _, hTrees⟩ := params.wellFormed_facts hWf
  have hLog : ∀ e ∈ signingOracleLog suite params sk queries, StatelessLogEntryOk suite params sk e.2 :=
    fun e he => signingOracleLog_entryOk suite params sk queries hStateless e he
  by_cases hForsEq : forsPkF = computeForsPk suite params sk
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
      (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)
  · rw [hForsEq] at hFors
    exact fors_break suite params sk _ msgStar sigStar (hTrees hStateless) hFresh hFors
  · right
    have h0 : sigStar.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) = sigStar.leafGlobalIdx := by
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
    have hTop : (derivePublicKey suite params sk).pkRoot =
        computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight))) := by
      rw [Nat.div_eq_of_lt hLt]
      rfl
    have hNe : sigStar.layerSigs ≠ [] := by
      intro hnil
      rw [hnil, List.length_nil] at hLen
      omega
    rcases hypertree_walk_break suite params sk _ msgStar sigStar hGeom hWf hLayers hLog hLt
        sigStar.layerSigs 0 forsPkF hNe (fun j => by rw [Nat.zero_add])
        (by rw [Nat.zero_add]; exact hLen) (by rw [h0, ← hTop]; exact hHt) with hEq | hB
    · exfalso
      apply hForsEq
      rw [hEq, honestLayerRoot_eq, h0]
      simp only [↓reduceIte]
    · exact hB

/-! ### Union bound over finitely many experiment outcomes -/

/-- Outcome of one EUF-CMA experiment: the key, the signing queries made, and the output. -/
structure EufCmaOutcome where
  sk : PqSecretKey
  queries : List PqSigningQuery
  msgStar : List UInt8
  sigStar : PqHashSig

/-- EUF-CMA winning condition: the output verifies and its message was never signed. -/
def eufCmaWin (suite : TweakableHashSuite) (params : PqHashParams) (o : EufCmaOutcome) : Bool :=
  verifyPqHashSig suite params (derivePublicKey suite params o.sk) o.msgStar o.sigStar &&
  decide (o.msgStar ∉ (signingOracleLog suite params o.sk o.queries).map Prod.fst)

theorem eufCmaWin_eq (suite : TweakableHashSuite) (params : PqHashParams) (o : EufCmaOutcome) :
    eufCmaWin suite params o =
      (verifyPqHashSig suite params (derivePublicKey suite params o.sk) o.msgStar o.sigStar &&
       decide (o.msgStar ∉ (signingOracleLog suite params o.sk o.queries).map Prod.fst)) := by rfl

/-- Regression: replaying a signed message is not a win. -/
theorem eufCmaWin_rejects_signed_message (suite : TweakableHashSuite) (params : PqHashParams)
    (o : EufCmaOutcome) (sig : PqHashSig)
    (hSigned : (o.msgStar, sig) ∈ signingOracleLog suite params o.sk o.queries) :
    eufCmaWin suite params o = false := by
  have hMem : o.msgStar ∈ (signingOracleLog suite params o.sk o.queries).map Prod.fst :=
    List.mem_map.mpr ⟨(o.msgStar, sig), hSigned, rfl⟩
  rw [eufCmaWin_eq, decide_eq_false (fun hn => hn hMem), Bool.and_false]

/-- Number of coins on which a Boolean event occurs. -/
def hitCount {Ω : Type} (p : Ω → Bool) : List Ω → Nat
  | [] => 0
  | ω :: rest => (if p ω then 1 else 0) + hitCount p rest

theorem hitCount_union_bound {Ω : Type} (win a b c : Ω → Bool)
    (h : ∀ ω, win ω = true → a ω = true ∨ b ω = true ∨ c ω = true) :
    ∀ coins : List Ω, hitCount win coins ≤ hitCount a coins + hitCount b coins + hitCount c coins
  | [] => Nat.le_refl 0
  | ω :: rest => by
    have ih := hitCount_union_bound win a b c h rest
    have hHead : (if win ω then 1 else 0) ≤
        (if a ω then 1 else 0) + (if b ω then 1 else 0) + (if c ω then 1 else 0) := by
      cases hw : win ω
      · exact Nat.zero_le _
      · rcases h ω hw with ha | hb | hc
        · rw [ha]
          exact Nat.le_trans (Nat.le_add_right 1 _) (Nat.le_add_right _ _)
        · rw [hb]
          exact Nat.le_trans (Nat.le_add_left 1 _) (Nat.le_add_right _ _)
        · rw [hc]
          exact Nat.le_add_left 1 _
    simp only [hitCount]
    generalize (if win ω then 1 else 0) = W at hHead ⊢
    generalize (if a ω then 1 else 0) = A at hHead ⊢
    generalize (if b ω then 1 else 0) = B at hHead ⊢
    generalize (if c ω then 1 else 0) = C at hHead ⊢
    omega

/-- **EUF-CMA union bound over explicit outcome counts.** `coins` enumerates the experiment's
    randomness and `game` maps a coin to the experiment outcome (adaptivity is absorbed: only the
    resulting key, query list and output matter). For any Boolean event indicators that fire
    whenever the corresponding break witness holds, the number of winning coins is at most the sum
    of the three event counts; dividing by `coins.length` gives
    `Adv_EUF-CMA ≤ Adv_ITSR + Adv_TCR + Adv_PRE` with all three factors equal to one. Indicators
    that over-approximate their witness only weaken the bound. -/
theorem hypertree_euf_cma_advantage_bound {Ω : Type} (suite : TweakableHashSuite)
    (params : PqHashParams)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hStateless : params.statefulJorts = false) (hLayers : params.numLayers ≤ 2 ^ 32)
    (coins : List Ω) (game : Ω → EufCmaOutcome) (isItsr isTcr isPre : Ω → Bool)
    (hItsr : ∀ ω, ForsItsrBreak suite params (derivePublicKey suite params (game ω).sk)
      (signingOracleLog suite params (game ω).sk (game ω).queries) (game ω).msgStar (game ω).sigStar →
      isItsr ω = true)
    (hTcr : ∀ ω, SmTcrBreak suite params (game ω).sk
      (signingOracleLog suite params (game ω).sk (game ω).queries) → isTcr ω = true)
    (hPre : ∀ ω, PreimageBreak suite params (game ω).sk
      (signingOracleLog suite params (game ω).sk (game ω).queries) (game ω).msgStar (game ω).sigStar →
      isPre ω = true) :
    hitCount (fun ω => eufCmaWin suite params (game ω)) coins ≤
      hitCount isItsr coins + hitCount isTcr coins + hitCount isPre coins := by
  apply hitCount_union_bound
  intro ω hWin
  rw [eufCmaWin_eq, Bool.and_eq_true] at hWin
  obtain ⟨hVer, hNotIn⟩ := hWin
  have hFresh : ∀ e ∈ signingOracleLog suite params (game ω).sk (game ω).queries,
      e.1 ≠ (game ω).msgStar := by
    intro e he hEq
    exact of_decide_eq_true hNotIn (List.mem_map.mpr ⟨e, he, hEq⟩)
  rcases hypertree_forgery_break_of_signingLog suite params (game ω).sk (game ω).queries
      (game ω).msgStar (game ω).sigStar hGeom hStateless hLayers hFresh hVer with h1 | h2 | h3
  · exact .inl (hItsr ω h1)
  · exact .inr (.inl (hTcr ω h2))
  · exact .inr (.inr (hPre ω h3))

/-- Query-count factor of the ITSR term: a log produced by `q` signing queries opens at most
    `q · k` FORS leaf addresses. -/
theorem logForsLeafAddrs_length_le (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pk : PqPublicKey) :
    ∀ queries : List PqSigningQuery,
      (logForsLeafAddrs suite params pk (signingOracleLog suite params sk queries)).length ≤
        queries.length * params.forsTrees
  | [] => by
    rw [List.length_nil, Nat.zero_mul]
    exact Nat.le_refl 0
  | q :: qs => by
    have ih := logForsLeafAddrs_length_le suite params sk pk qs
    rw [List.length_cons, Nat.succ_mul]
    unfold signingOracleLog
    split
    · omega
    · have hOne : (sigForsLeafAddrs suite params pk q.message ‹PqHashSig›).length = params.forsTrees := by
        simp [sigForsLeafAddrs]
      simp only [logForsLeafAddrs, List.length_append, hOne]
      omega

/-! ### Satisfiability witness -/

/-- Constant toy suite whose 32-byte output `0x1B…1B` has base-4 digit sum `192`, the target sum
    of `w = 4`, `ℓ₁ = 128`. Used only to show the hypotheses above are jointly satisfiable. -/
def crumbToySuite : TweakableHashSuite where
  suiteId := []
  rawHash := fun _ => List.replicate 32 0x1B
  rawHash_len := fun _ => List.length_replicate

/-- One layer of height one, one FORS tree of height one, `w = 4`, `ℓ₁ = 128`. -/
def crumbToyParams : PqHashParams := ⟨4, 128, 1, 1, 1, 1, 1, false⟩

/-- A well-shaped signature; under the constant suite it verifies for every message. -/
def crumbToyForgery : PqHashSig :=
  { rRand := [], msgTswCtr := 0, leafGlobalIdx := 0,
    forsOpenings := [⟨[], [[]]⟩],
    layerSigs := [⟨0, List.replicate 128 [], [[]]⟩] }

theorem crumbToyForgery_accepted :
    verifyPqHashSig crumbToySuite crumbToyParams
      (derivePublicKey crumbToySuite crumbToyParams ⟨[], [], []⟩) [] crumbToyForgery = true := by
  decide +kernel

/-- The premises of `hypertree_forgery_break_of_signingLog` hold on a concrete instance (empty
    query list), and there the ITSR branch is excluded, so a collision or preimage witness
    results; a constant hash is neither collision resistant nor one-way. -/
theorem hypertree_forgery_break_inhabited :
    SmTcrBreak crumbToySuite crumbToyParams ⟨[], [], []⟩ [] ∨
    PreimageBreak crumbToySuite crumbToyParams ⟨[], [], []⟩ [] [] crumbToyForgery := by
  rcases hypertree_forgery_break_of_signingLog crumbToySuite crumbToyParams ⟨[], [], []⟩ [] []
      crumbToyForgery (.inl ⟨rfl, rfl⟩) rfl (by decide) (fun _ he => by cases he)
      crumbToyForgery_accepted with h | h
  · exact absurd h (forsItsrBreak_empty_log _ _ _ _ _)
  · exact h

/-- The ITSR branch is inhabited on a genuine run: after one signing query on `[1]`, the same
    well-shaped signature on the unsigned message `[]` opens only FORS addresses already in the
    log (the constant suite sends both digests to the same leaf). -/
theorem forsItsrBreak_inhabited :
    ForsItsrBreak crumbToySuite crumbToyParams
      (derivePublicKey crumbToySuite crumbToyParams ⟨[], [], []⟩)
      (signingOracleLog crumbToySuite crumbToyParams ⟨[], [], []⟩ [⟨[1], [], 0, 1⟩])
      [] crumbToyForgery :=
  ⟨by decide +kernel, by decide, by decide +kernel⟩

/-! ## 6. Checked Error-Aware Stateful `Jorts` Signing & End-to-End Finite-Log EUF-CMA Reduction -/

/-- Domain tag matching Rust `TAG_JORTS_DET_RAND` (`crates/qsag-core/src/tsw_baggy.rs`):
    binds per-epoch deterministic randomness to `(epoch, pkSeed)` so crash-recovery retries never
    steer `optRand` into a second WOTS+C codeword on a spent leaf. -/
def tagStatefulDetRand : List UInt8 :=
  [81, 83, 65, 71, 46, 80, 81, 46, 66, 65, 71, 71, 89, 83, 73, 71, 46, 68, 69, 84, 47, 118, 49]

/-- Canonical length-framed deterministic `optRand` domain for stateful `Jorts` epoch `epoch`. -/
def buildStatefulDetOptDomain (epoch : Nat) (pkSeed : List UInt8) : List UInt8 :=
  encodeMultiFrame [tagStatefulDetRand, be 8 epoch, pkSeed]

theorem buildStatefulDetOptDomain_injective {ep₁ ep₂ : Nat} {p₁ p₂ : List UInt8}
    (h₁ : ep₁ < 2 ^ 64) (h₂ : ep₂ < 2 ^ 64)
    (hEq : buildStatefulDetOptDomain ep₁ p₁ = buildStatefulDetOptDomain ep₂ p₂) :
    ep₁ = ep₂ ∧ p₁ = p₂ := by
  have hFrames := encodeMultiFrame_injective hEq
  simp only [List.cons.injEq, and_true] at hFrames
  have h256 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  exact ⟨be_injective (h256 ▸ h₁) (h256 ▸ h₂) hFrames.2.1, hFrames.2.2⟩

/-- Parameter-set validity check for checked stateful `Jorts` hypertree signing:
    requires `wellFormed`, `statefulJorts = true`, `checkedDigitGeometry`, and a positive
    epoch budget `0 < maxSigsLog2 ≤ numLayers * subtreeHeight`. -/
def PqHashParams.checkedStatefulValid (p : PqHashParams) : Bool :=
  p.wellFormed && p.statefulJorts && p.checkedDigitGeometry &&
  decide (0 < p.maxSigsLog2) &&
  decide (p.maxSigsLog2 ≤ p.numLayers * p.subtreeHeight)

theorem PqHashParams.checkedStatefulValid_eq (p : PqHashParams) :
    p.checkedStatefulValid =
      (p.wellFormed && p.statefulJorts && p.checkedDigitGeometry &&
       decide (0 < p.maxSigsLog2) &&
       decide (p.maxSigsLog2 ≤ p.numLayers * p.subtreeHeight)) := by rfl

theorem PqHashParams.checkedStatefulValid_facts (p : PqHashParams)
    (h : p.checkedStatefulValid = true) :
    p.wellFormed = true ∧ p.statefulJorts = true ∧ p.checkedDigitGeometry = true ∧
    0 < p.maxSigsLog2 ∧ p.maxSigsLog2 ≤ p.numLayers * p.subtreeHeight ∧
    0 < p.numLayers ∧ 0 < p.subtreeHeight ∧ p.numLayers ≤ 2 ^ 32 := by
  rw [PqHashParams.checkedStatefulValid_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hWf, hSt⟩, hGeom⟩, hMaxPos⟩, hMaxLe⟩ := h
  obtain ⟨hDPos, _, _, _, hDHLe, _⟩ := p.wellFormed_facts hWf
  have hHPos : 0 < p.subtreeHeight := by
    cases hH0 : p.subtreeHeight with
    | zero => rw [hH0, Nat.mul_zero] at hMaxLe; omega
    | succ _ => omega
  have hLayersLe62 : p.numLayers ≤ 62 := by
    have hMulGe : p.numLayers * 1 ≤ p.numLayers * p.subtreeHeight :=
      Nat.mul_le_mul_left p.numLayers hHPos
    omega
  exact ⟨hWf, hSt, hGeom, hMaxPos, hMaxLe, hDPos, hHPos, Nat.le_trans hLayersLe62 (by decide)⟩

theorem jortsPoseidon2_checkedStatefulValid :
    jortsPoseidon2Params.checkedStatefulValid = true := by decide +kernel

/-- Checked verifier for stateful `Jorts` profiles: enforces `checkedStatefulValid`,
    epoch budget `sig.leafGlobalIdx < 2 ^ params.maxSigsLog2`, and `verifyPqHashSig`. -/
def verifyCheckedStateful (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) : Bool :=
  params.checkedStatefulValid &&
  decide (sig.leafGlobalIdx < 2 ^ params.maxSigsLog2) &&
  verifyPqHashSig suite params pk msg sig

theorem verifyCheckedStateful_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) :
    verifyCheckedStateful suite params pk msg sig =
      (params.checkedStatefulValid &&
       decide (sig.leafGlobalIdx < 2 ^ params.maxSigsLog2) &&
       verifyPqHashSig suite params pk msg sig) := by rfl

theorem verifyCheckedStateful_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (h : verifyCheckedStateful suite params pk msg sig = true) :
    params.checkedStatefulValid = true ∧
    sig.leafGlobalIdx < 2 ^ params.maxSigsLog2 ∧
    verifyPqHashSig suite params pk msg sig = true := by
  rw [verifyCheckedStateful_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Explicit error taxonomy for checked stateful `Jorts` signing (`0` silent `none` state freeze). -/
inductive CheckedStatefulError where
  | invalidParams
  | invalidState
  | budgetExhausted (requestedEpoch maxLeaves : Nat)
  | staleOrOutOfOrderEpoch (requestedEpoch expectedEpoch : Nat)
  | epochNotInFlight (requestedEpoch : Nat)
  | equivocationRefused (epoch : Nat)
  | grindExhausted (epoch maxGrind : Nat)
  deriving DecidableEq, Repr

/-- Checked durable `EpochLatch` state for stateful `Jorts` signing. -/
structure CheckedStatefulLatchState where
  nextEpoch   : Nat
  latchedLast : Option (Nat × List UInt8 × PqHashSig)
  deriving DecidableEq, Repr

/-- Canonical initial state at epoch `0` with no in-flight latched signature. -/
def initCheckedStatefulLatch : CheckedStatefulLatchState :=
  { nextEpoch := 0, latchedLast := none }

/-- Runtime state-integrity check enforced before every checked stateful transition. -/
def CheckedStatefulLatchState.validBounds (params : PqHashParams) (st : CheckedStatefulLatchState) : Bool :=
  decide (st.nextEpoch ≤ 2 ^ params.maxSigsLog2) &&
  match st.latchedLast with
  | none => true
  | some (ep0, _, _) => decide (ep0 < st.nextEpoch)

theorem initCheckedStatefulLatch_validBounds (params : PqHashParams) :
    initCheckedStatefulLatch.validBounds params = true := by
  simp [initCheckedStatefulLatch, CheckedStatefulLatchState.validBounds]

/-- Adversary / validator signing query against the checked stateful hypertree oracle. -/
inductive CheckedStatefulQuery where
  | signNext   (message : List UInt8) (grindLimit : Nat)
  | signEpoch  (reqEpoch : Nat) (message : List UInt8) (grindLimit : Nat)
  | retryEpoch (reqEpoch : Nat) (message : List UInt8)
  deriving DecidableEq, Repr

/-- Fresh-epoch checked stateful helper: enforces `ep < 2 ^ params.maxSigsLog2`, evaluates
    `evalSingleSign` under deterministic `(ep, pkSeed)` domain separation, and advances `nextEpoch`. -/
def checkedStatefulFreshEpochSign (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (ep : Nat) (msg : List UInt8) (maxGrind : Nat) :
    Except CheckedStatefulError (CheckedStatefulLatchState × Nat × List UInt8 × PqHashSig) :=
  if !(decide (ep < 2 ^ params.maxSigsLog2)) then
    .error (.budgetExhausted ep (2 ^ params.maxSigsLog2))
  else
    match evalSingleSign suite params sk msg (buildStatefulDetOptDomain ep sk.pkSeed) ep maxGrind with
    | none => .error (.grindExhausted ep maxGrind)
    | some sig =>
      .ok ({ nextEpoch := ep + 1, latchedLast := some (ep, msg, sig) }, ep, msg, sig)

/-- **Checked Error-Aware Stateful Signing Step (`checkedStatefulSignStep`)**:
    Returns `.ok (st', ep, msg, sig)` on a valid fresh epoch or exact idempotent crash retry, and
    otherwise aborts explicitly with `CheckedStatefulError` rather than silently dropping `none`. -/
def checkedStatefulSignStep (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (st : CheckedStatefulLatchState) (q : CheckedStatefulQuery) :
    Except CheckedStatefulError (CheckedStatefulLatchState × Nat × List UInt8 × PqHashSig) :=
  if !params.checkedStatefulValid then
    .error .invalidParams
  else if !(st.validBounds params) then
    .error .invalidState
  else
    match q with
    | .signNext msg maxGrind =>
      checkedStatefulFreshEpochSign suite params sk st.nextEpoch msg maxGrind
    | .retryEpoch reqEp msg =>
      match st.latchedLast with
      | none => .error (.epochNotInFlight reqEp)
      | some (ep0, prevMsg, prevSig) =>
        if reqEp != ep0 then .error (.epochNotInFlight reqEp)
        else if decide (msg = prevMsg) then .ok (st, ep0, msg, prevSig)
        else .error (.equivocationRefused ep0)
    | .signEpoch reqEp msg maxGrind =>
      match st.latchedLast with
      | none =>
        if reqEp == st.nextEpoch then
          checkedStatefulFreshEpochSign suite params sk reqEp msg maxGrind
        else
          .error (.staleOrOutOfOrderEpoch reqEp st.nextEpoch)
      | some (ep0, prevMsg, prevSig) =>
        if reqEp == ep0 then
          if decide (msg = prevMsg) then .ok (st, ep0, msg, prevSig)
          else .error (.equivocationRefused ep0)
        else if reqEp == st.nextEpoch then
          checkedStatefulFreshEpochSign suite params sk reqEp msg maxGrind
        else
          .error (.staleOrOutOfOrderEpoch reqEp st.nextEpoch)

/-- Multi-turn strict execution propagating the first `CheckedStatefulError` via `Except`. -/
def execCheckedStatefulStrict (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) :
    CheckedStatefulLatchState → List CheckedStatefulQuery →
      Except CheckedStatefulError (CheckedStatefulLatchState × List (Nat × List UInt8 × PqHashSig))
  | st, [] => .ok (st, [])
  | st, q :: rest =>
    match checkedStatefulSignStep suite params sk st q with
    | .error err => .error err
    | .ok (st', ep, msg, sig) =>
      match execCheckedStatefulStrict suite params sk st' rest with
      | .error err => .error err
      | .ok (stFinal, logRest) => .ok (stFinal, (ep, msg, sig) :: logRest)

/-- Multi-turn EUF-CMA oracle run: halts `activeState := none` and records `abortError := some err`
    on the first error (refusing all subsequent signing queries instead of silently continuing from
    a frozen state) while retaining every signature in `emittedLog` revealed prior to the abort. -/
structure CheckedStatefulOracleRun where
  activeState : Option CheckedStatefulLatchState
  abortError  : Option CheckedStatefulError
  emittedLog  : List (Nat × List UInt8 × PqHashSig)
  deriving DecidableEq, Repr

def execCheckedStatefulOracleAux (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) :
    Option CheckedStatefulLatchState → Option CheckedStatefulError → List CheckedStatefulQuery →
      CheckedStatefulOracleRun
  | none, errOpt, _ => { activeState := none, abortError := errOpt, emittedLog := [] }
  | some st, _, [] => { activeState := some st, abortError := none, emittedLog := [] }
  | some st, _, q :: rest =>
    match checkedStatefulSignStep suite params sk st q with
    | .error err => { activeState := none, abortError := some err, emittedLog := [] }
    | .ok (st', ep, msg, sig) =>
      let tailRun := execCheckedStatefulOracleAux suite params sk (some st') none rest
      { activeState := tailRun.activeState
        abortError  := tailRun.abortError
        emittedLog  := (ep, msg, sig) :: tailRun.emittedLog }

def execCheckedStatefulOracle (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (st0 : CheckedStatefulLatchState) (queries : List CheckedStatefulQuery) :
    CheckedStatefulOracleRun :=
  execCheckedStatefulOracleAux suite params sk (some st0) none queries

/-- Exact correspondence between `execCheckedStatefulStrict` and `execCheckedStatefulOracle`. -/
theorem execCheckedStatefulStrict_eq_oracle (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) :
    ∀ (queries : List CheckedStatefulQuery) (st : CheckedStatefulLatchState),
      (∀ stFinal log,
        execCheckedStatefulStrict suite params sk st queries = .ok (stFinal, log) ↔
        execCheckedStatefulOracle suite params sk st queries =
          { activeState := some stFinal, abortError := none, emittedLog := log }) ∧
      (∀ err,
        execCheckedStatefulStrict suite params sk st queries = .error err ↔
        (execCheckedStatefulOracle suite params sk st queries).abortError = some err)
  | [], st => by
    refine ⟨fun stFinal log => ?_, fun err => ?_⟩
    · simp [execCheckedStatefulStrict, execCheckedStatefulOracle, execCheckedStatefulOracleAux]
    · simp [execCheckedStatefulStrict, execCheckedStatefulOracle, execCheckedStatefulOracleAux]
  | q :: rest, st => by
    refine ⟨fun stFinal log => ?_, fun err => ?_⟩
    · simp only [execCheckedStatefulStrict, execCheckedStatefulOracle, execCheckedStatefulOracleAux]
      cases hStep : checkedStatefulSignStep suite params sk st q with
      | error e => simp
      | ok quad =>
        rcases quad with ⟨st', ep, msg, sig⟩
        dsimp only
        have ihOk := (execCheckedStatefulStrict_eq_oracle suite params sk rest st').1
        constructor
        · intro hStrict
          cases hSub : execCheckedStatefulStrict suite params sk st' rest with
          | error e => rw [hSub] at hStrict; cases hStrict
          | ok pr =>
            rcases pr with ⟨stF, logR⟩
            rw [hSub] at hStrict
            injection hStrict with hProd
            rcases Prod.mk.inj hProd with ⟨rfl, rfl⟩
            have hSubOrc := (ihOk stF logR).mp hSub
            unfold execCheckedStatefulOracle at hSubOrc
            rw [hSubOrc]
        · intro hOrc
          cases hLog : log with
          | nil => rw [hLog] at hOrc; injection hOrc with _ _ hCons; cases hCons
          | cons hd tl =>
            rw [hLog] at hOrc
            injection hOrc with hAct hAb hCons
            rcases List.cons.inj hCons with ⟨hHd, hTl⟩
            have hTailEq : execCheckedStatefulOracle suite params sk st' rest =
                { activeState := some stFinal, abortError := none, emittedLog := tl } := by
              unfold execCheckedStatefulOracle
              cases hRun : execCheckedStatefulOracleAux suite params sk (some st') none rest
              rw [hRun] at hAct hAb hTl
              dsimp only at hAct hAb hTl
              rw [hAct, hAb, hTl]
            rw [(ihOk stFinal tl).mpr hTailEq, hHd]
    · simp only [execCheckedStatefulStrict, execCheckedStatefulOracle, execCheckedStatefulOracleAux]
      cases hStep : checkedStatefulSignStep suite params sk st q with
      | error e => simp [Except.error.injEq, Option.some.injEq]
      | ok quad =>
        rcases quad with ⟨st', ep, msg, sig⟩
        dsimp only
        have ihErr := (execCheckedStatefulStrict_eq_oracle suite params sk rest st').2 err
        unfold execCheckedStatefulOracle at ihErr
        cases hSub : execCheckedStatefulStrict suite params sk st' rest with
        | error e =>
          rw [hSub] at ihErr
          simpa using ihErr
        | ok pr =>
          rcases pr with ⟨stF, logR⟩
          have hSubOrc := ((execCheckedStatefulStrict_eq_oracle suite params sk rest st').1 stF logR).mp hSub
          unfold execCheckedStatefulOracle at hSubOrc
          rw [hSubOrc]
          simp

/-- Shape of a successful stateful `evalSingleSign` invocation. -/
theorem evalSingleSign_stateful_inv (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (leaf maxGrind : Nat) (sig : PqHashSig)
    (hMode : params.statefulJorts = true)
    (h : evalSingleSign suite params sk msg optRand leaf maxGrind = some sig) :
    params.wellFormed = true ∧
    leaf < 2 ^ (params.numLayers * params.subtreeHeight) ∧
    sig.rRand = thPrfMsg suite sk.skPrf optRand
      (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg) ∧
    sig.msgTswCtr = 0 ∧
    sig.leafGlobalIdx = leaf ∧
    sig.forsOpenings = [] ∧
    signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot
      (thPrfMsg suite sk.skPrf optRand
        (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg))
      maxGrind 0 leaf
      (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg)
      params.numLayers = some sig.layerSigs := by
  unfold evalSingleSign at h
  cases hWf : params.wellFormed
  · simp [hWf] at h
  · cases hLeaf : decide (leaf < 2 ^ (params.numLayers * params.subtreeHeight))
    · simp [hWf, hLeaf] at h
    · simp only [hWf, hLeaf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hMode] at h
      split at h
      · cases h
      · rename_i layerSigs hLs
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, of_decide_eq_true hLeaf, rfl, rfl, rfl, rfl, hLs⟩

/-- Fuel-independent determinism of `signHypertreeLayers`: any two successful runs on the same
    inputs produce identical `LayerXmssSig` lists, regardless of `fuel₁` and `fuel₂`. -/
theorem signHypertreeLayers_det (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot : List UInt8) :
    ∀ (rem layerIdx globalIdx fuel₁ fuel₂ : Nat) (layer0Rand curRoot : List UInt8)
      {s₁ s₂ : List LayerXmssSig},
      signHypertreeLayers suite params sk pkRoot layer0Rand fuel₁ layerIdx globalIdx curRoot rem = some s₁ →
      signHypertreeLayers suite params sk pkRoot layer0Rand fuel₂ layerIdx globalIdx curRoot rem = some s₂ →
      s₁ = s₂
  | 0, _, _, _, _, _, _, _, _, h₁, h₂ => by
    rw [signHypertreeLayers_zero] at h₁ h₂
    injection h₁ with e₁
    injection h₂ with e₂
    exact e₁.symm.trans e₂
  | rem + 1, layerIdx, globalIdx, fuel₁, fuel₂, layer0Rand, curRoot, s₁, s₂, h₁, h₂ => by
    rw [signHypertreeLayers_succ] at h₁ h₂
    dsimp only at h₁ h₂
    split at h₁
    · cases h₁
    · rename_i ctr₁ dig₁ hm₁ hG₁
      split at h₂
      · cases h₂
      · rename_i ctr₂ dig₂ hm₂ hG₂
        have hEqG := grindTswCounterAux_det fuel₁ fuel₂ 0 hG₁ hG₂
        rcases Prod.mk.inj hEqG with ⟨rfl, hDigHm⟩
        rcases Prod.mk.inj hDigHm with ⟨rfl, _⟩
        split at h₁
        · cases h₁
        · rename_i rest₁ hR₁
          split at h₂
          · cases h₂
          · rename_i rest₂ hR₂
            have hRestEq := signHypertreeLayers_det suite params sk pkRoot rem (layerIdx + 1)
              (globalIdx / 2 ^ params.subtreeHeight) fuel₁ fuel₂ [] _ hR₁ hR₂
            subst hRestEq
            injection h₁ with e₁
            injection h₂ with e₂
            exact e₁.symm.trans e₂

/-- Fuel-independent determinism of stateful `evalSingleSign`. -/
theorem evalSingleSign_stateful_det (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (leaf fuel₁ fuel₂ : Nat)
    {sig₁ sig₂ : PqHashSig}
    (hMode : params.statefulJorts = true)
    (h₁ : evalSingleSign suite params sk msg optRand leaf fuel₁ = some sig₁)
    (h₂ : evalSingleSign suite params sk msg optRand leaf fuel₂ = some sig₂) :
    sig₁ = sig₂ := by
  obtain ⟨_, _, hr₁, hm₁, hl₁, hf₁, hLs₁⟩ :=
    evalSingleSign_stateful_inv suite params sk msg optRand leaf fuel₁ sig₁ hMode h₁
  obtain ⟨_, _, hr₂, hm₂, hl₂, hf₂, hLs₂⟩ :=
    evalSingleSign_stateful_inv suite params sk msg optRand leaf fuel₂ sig₂ hMode h₂
  have hLsEq := signHypertreeLayers_det suite params sk _ params.numLayers 0 leaf fuel₁ fuel₂ _ _ hLs₁ hLs₂
  cases sig₁; cases sig₂
  simp only [PqHashSig.mk.injEq] at hr₁ hm₁ hl₁ hf₁ hr₂ hm₂ hl₂ hf₂ hLsEq ⊢
  exact ⟨hr₁.trans hr₂.symm, hm₁.trans hm₂.symm, hl₁.trans hl₂.symm, hf₁.trans hf₂.symm, hLsEq⟩

/-- Layer-`i` randomness used by an honestly signed stateful entry `(ep, msg, sig)`. -/
def honestStatefulLayerRand (e : Nat × List UInt8 × PqHashSig) (i : Nat) : List UInt8 :=
  if i = 0 then e.2.2.rRand else []

/-- Layer-`i` signed root used by an honestly signed stateful entry at `(i, g)`:
    `thPreHash` of `msg` at layer `0`, or the lower XMSS subtree root at layer `i > 0`. -/
def honestStatefulLayerRoot (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (msg : List UInt8) (i g : Nat) : List UInt8 :=
  if i = 0 then
    thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg
  else
    computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1)) (UInt64.ofNat g)

theorem honestStatefulLayerRoot_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg : List UInt8) (i g : Nat) :
    honestStatefulLayerRoot suite params sk msg i g =
      if i = 0 then
        thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg
      else
        computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1)) (UInt64.ofNat g) := by rfl

/-- Base-`w` digits disclosed by a logged stateful signature `e = (ep, msg, sig)` at layer `i`. -/
def statefulLogLayerDigits (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (e : Nat × List UInt8 × PqHashSig) (i : Nat) : List Nat :=
  extractBaseWDigits params.w params.ell1
    (thHashMsg suite (honestStatefulLayerRand e i) sk.pkSeed (derivePublicKey suite params sk).pkRoot
      (honestStatefulLayerRoot suite params sk e.2.1 i (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))
      (UInt32.ofNat i)
      (UInt64.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
      (UInt32.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
      (e.2.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr)

theorem statefulLogLayerDigits_eq (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (e : Nat × List UInt8 × PqHashSig) (i : Nat) :
    statefulLogLayerDigits suite params sk e i =
      extractBaseWDigits params.w params.ell1
        (thHashMsg suite (honestStatefulLayerRand e i) sk.pkSeed (derivePublicKey suite params sk).pkRoot
          (honestStatefulLayerRoot suite params sk e.2.1 i (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))
          (UInt32.ofNat i)
          (UInt64.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
          (e.2.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr) := by rfl

/-- Structural soundness invariant guaranteed for every entry `e = (ep, msg, sig)` emitted by
    the checked stateful signing oracle. -/
structure StatefulLogEntryOk (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (e : Nat × List UInt8 × PqHashSig) : Prop where
  params_valid   : params.checkedStatefulValid = true
  leaf_eq_epoch  : e.2.2.leafGlobalIdx = e.1
  epoch_lt       : e.1 < 2 ^ params.maxSigsLog2
  leaf_lt        : e.2.2.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)
  eval_generated : ∃ fuel,
    evalSingleSign suite params sk e.2.1 (buildStatefulDetOptDomain e.1 sk.pkSeed) e.1 fuel = some e.2.2
  layer : ∀ i, i < params.numLayers → ∃ fuel digits hm,
    grindTswCounterAux suite params.w params.ell1 params.targetSum
      (honestStatefulLayerRand e i) sk.pkSeed (derivePublicKey suite params sk).pkRoot
      (honestStatefulLayerRoot suite params sk e.2.1 i (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))
      (UInt32.ofNat i)
      (UInt64.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
      (UInt32.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
      0 fuel = some ((e.2.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr, digits, hm) ∧
    (e.2.2.layerSigs.getD i ⟨0, [], []⟩).wotsChains = (List.range params.ell1).map fun r =>
      honestChainNode suite sk (UInt32.ofNat i)
        (UInt64.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
        (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight) r (digits.getD r 0)

theorem statefulLogEntryOk_of_eval (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) {ep maxGrind : Nat} {msg : List UInt8} {sig : PqHashSig}
    (hValid : params.checkedStatefulValid = true)
    (hEpLt : ep < 2 ^ params.maxSigsLog2)
    (hEv : evalSingleSign suite params sk msg (buildStatefulDetOptDomain ep sk.pkSeed) ep maxGrind = some sig) :
    StatefulLogEntryOk suite params sk (ep, msg, sig) := by
  obtain ⟨_, hSt, _, _, _, _, _, _⟩ := params.checkedStatefulValid_facts hValid
  obtain ⟨_, hLeafLt, hRandEq, _, hLeafEq, _, hLs⟩ :=
    evalSingleSign_stateful_inv suite params sk msg (buildStatefulDetOptDomain ep sk.pkSeed) ep maxGrind sig hSt hEv
  refine ⟨hValid, hLeafEq, hEpLt, hLeafEq ▸ hLeafLt, ⟨maxGrind, hEv⟩, ?_⟩
  intro i hi
  obtain ⟨dg, hm, hG, hC⟩ := signHypertreeLayers_layer suite params sk _ maxGrind
    params.numLayers 0 ep _ _ sig.layerSigs hLs i hi
  simp only [Nat.zero_add] at hG hC
  have hRandI :
      (if i = 0 then
        thPrfMsg suite sk.skPrf (buildStatefulDetOptDomain ep sk.pkSeed)
          (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg)
       else []) = honestStatefulLayerRand (ep, msg, sig) i := by
    unfold honestStatefulLayerRand
    dsimp only
    rw [hRandEq]
  rw [hRandI] at hG
  rw [← hLeafEq] at hG hC
  have hRootI :
      (if i = 0 then
        thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg
       else computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1))
         (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))) =
      honestStatefulLayerRoot suite params sk msg i (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) := rfl
  rw [hRootI] at hG
  exact ⟨maxGrind, dg, hm, hG, hC⟩

/-- State invariant preserved across arbitrarily many `checkedStatefulSignStep` calls. -/
def CheckedStatefulStateInv (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (st : CheckedStatefulLatchState) : Prop :=
  ∀ ep m s, st.latchedLast = some (ep, m, s) →
    ep < st.nextEpoch ∧ StatefulLogEntryOk suite params sk (ep, m, s)

theorem initCheckedStatefulLatch_inv (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) :
    CheckedStatefulStateInv suite params sk initCheckedStatefulLatch :=
  fun _ _ _ h => by cases h

private theorem checkedStatefulFreshEpochSign_step
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    {ep maxGrind : Nat} {msg : List UInt8}
    {st' : CheckedStatefulLatchState} {outEp : Nat} {outMsg : List UInt8} {sig : PqHashSig}
    (hValid : params.checkedStatefulValid = true)
    (hFresh : checkedStatefulFreshEpochSign suite params sk ep msg maxGrind = .ok (st', outEp, outMsg, sig)) :
    outEp = ep ∧ outMsg = msg ∧
    st' = { nextEpoch := ep + 1, latchedLast := some (ep, msg, sig) } ∧
    StatefulLogEntryOk suite params sk (ep, msg, sig) := by
  unfold checkedStatefulFreshEpochSign at hFresh
  cases hBud : decide (ep < 2 ^ params.maxSigsLog2)
  · simp [hBud] at hFresh
  · simp only [hBud, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hFresh
    cases hEv : evalSingleSign suite params sk msg (buildStatefulDetOptDomain ep sk.pkSeed) ep maxGrind with
    | none => rw [hEv] at hFresh; cases hFresh
    | some s =>
      rw [hEv] at hFresh
      injection hFresh with hTup
      rcases Prod.mk.inj hTup with ⟨rfl, hRest⟩
      rcases Prod.mk.inj hRest with ⟨rfl, hMS⟩
      rcases Prod.mk.inj hMS with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, statefulLogEntryOk_of_eval suite params sk hValid (of_decide_eq_true hBud) hEv⟩

theorem checkedStatefulSignStep_preserves_inv
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    {st st' : CheckedStatefulLatchState} {q : CheckedStatefulQuery}
    {ep : Nat} {msg : List UInt8} {sig : PqHashSig}
    (hInv : CheckedStatefulStateInv suite params sk st)
    (hStep : checkedStatefulSignStep suite params sk st q = .ok (st', ep, msg, sig)) :
    CheckedStatefulStateInv suite params sk st' ∧
    StatefulLogEntryOk suite params sk (ep, msg, sig) ∧
    st.nextEpoch ≤ st'.nextEpoch ∧
    ((st.latchedLast = some (ep, msg, sig) ∧ st' = st) ∨
     (ep = st.nextEpoch ∧ st'.nextEpoch = ep + 1 ∧ st'.latchedLast = some (ep, msg, sig))) := by
  unfold checkedStatefulSignStep at hStep
  cases hValid : params.checkedStatefulValid
  · simp [hValid] at hStep
  · cases hBnd : st.validBounds params
    · simp [hValid, hBnd] at hStep
    · simp only [hValid, hBnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
      cases q with
      | signNext m g =>
        obtain ⟨rfl, rfl, rfl, hOk⟩ := checkedStatefulFreshEpochSign_step suite params sk hValid hStep
        refine ⟨?_, hOk, by dsimp only; omega, .inr ⟨rfl, rfl, rfl⟩⟩
        intro ep' m' s' hSome
        injection hSome with hEq
        rcases Prod.mk.inj hEq with ⟨rfl, hMS⟩
        rcases Prod.mk.inj hMS with ⟨rfl, rfl⟩
        exact ⟨by dsimp only; omega, hOk⟩
      | retryEpoch reqEp m =>
        cases hLat : st.latchedLast with
        | none => rw [hLat] at hStep; cases hStep
        | some tr =>
          rcases tr with ⟨ep0, prevMsg, prevSig⟩
          rw [hLat] at hStep
          cases hNe : (reqEp != ep0)
          · simp only [hNe, Bool.false_eq_true, ↓reduceIte] at hStep
            cases hM : decide (m = prevMsg)
            · simp [hM] at hStep
            · simp only [hM, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hStep
              rcases hStep with ⟨rfl, rfl, rfl, rfl⟩
              have hM' : m = prevMsg := of_decide_eq_true hM
              subst hM'
              obtain ⟨_, hOk0⟩ := hInv ep0 m prevSig hLat
              exact ⟨hInv, hOk0, Nat.le_refl _, .inl ⟨rfl, rfl⟩⟩
          · simp [hNe] at hStep
      | signEpoch reqEp m g =>
        cases hLat : st.latchedLast with
        | none =>
          rw [hLat] at hStep
          cases hEp : (reqEp == st.nextEpoch)
          · simp [hEp] at hStep
          · simp only [hEp, ↓reduceIte] at hStep
            have hEpEq : reqEp = st.nextEpoch := of_decide_eq_true (by simpa [beq_iff_eq] using hEp)
            obtain ⟨rfl, rfl, rfl, hOk⟩ := checkedStatefulFreshEpochSign_step suite params sk hValid hStep
            refine ⟨?_, hOk, by dsimp only; omega, .inr ⟨hEpEq, rfl, rfl⟩⟩
            intro ep' m' s' hSome
            injection hSome with hEq
            rcases Prod.mk.inj hEq with ⟨rfl, hMS⟩
            rcases Prod.mk.inj hMS with ⟨rfl, rfl⟩
            exact ⟨by dsimp only; omega, hOk⟩
        | some tr =>
          rcases tr with ⟨ep0, prevMsg, prevSig⟩
          rw [hLat] at hStep
          cases hHitEp : (reqEp == ep0)
          · simp only [hHitEp, Bool.false_eq_true, ↓reduceIte] at hStep
            cases hEp : (reqEp == st.nextEpoch)
            · simp [hEp] at hStep
            · simp only [hEp, ↓reduceIte] at hStep
              have hEpEq : reqEp = st.nextEpoch := of_decide_eq_true (by simpa [beq_iff_eq] using hEp)
              obtain ⟨rfl, rfl, rfl, hOk⟩ := checkedStatefulFreshEpochSign_step suite params sk hValid hStep
              refine ⟨?_, hOk, by dsimp only; omega, .inr ⟨hEpEq, rfl, rfl⟩⟩
              intro ep' m' s' hSome
              injection hSome with hEq
              rcases Prod.mk.inj hEq with ⟨rfl, hMS⟩
              rcases Prod.mk.inj hMS with ⟨rfl, rfl⟩
              exact ⟨by dsimp only; omega, hOk⟩
          · simp only [hHitEp, ↓reduceIte] at hStep
            cases hM : decide (m = prevMsg)
            · simp [hM] at hStep
            · simp only [hM, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hStep
              rcases hStep with ⟨rfl, rfl, rfl, rfl⟩
              have hM' : m = prevMsg := of_decide_eq_true hM
              subst hM'
              obtain ⟨_, hOk0⟩ := hInv ep0 m prevSig hLat
              exact ⟨hInv, hOk0, Nat.le_refl _, .inl ⟨rfl, rfl⟩⟩

/-- Strengthened multi-turn inductive invariant for `execCheckedStatefulOracleAux`:
    every emitted signature satisfies `StatefulLogEntryOk` and no two entries at the same epoch
    can ever carry distinct messages or distinct signatures! -/
theorem checkedStatefulOracleAux_invariant
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) :
    ∀ (queries : List CheckedStatefulQuery) (stOpt : Option CheckedStatefulLatchState)
      (errOpt : Option CheckedStatefulError),
      (∀ st, stOpt = some st → CheckedStatefulStateInv suite params sk st) →
      let run := execCheckedStatefulOracleAux suite params sk stOpt errOpt queries
      (∀ e ∈ run.emittedLog, StatefulLogEntryOk suite params sk e) ∧
      (∀ st, stOpt = some st → ∀ e ∈ run.emittedLog,
        st.latchedLast = some e ∨ st.nextEpoch ≤ e.1) ∧
      (∀ e₁ ∈ run.emittedLog, ∀ e₂ ∈ run.emittedLog, e₁.1 = e₂.1 → e₁ = e₂)
  | _, none, errOpt, _ => by
    simp [execCheckedStatefulOracleAux]
  | [], some st, errOpt, _ => by
    simp [execCheckedStatefulOracleAux]
  | q :: rest, some st, errOpt, hOptInv => by
    have hInv := hOptInv st rfl
    simp only [execCheckedStatefulOracleAux]
    cases hStep : checkedStatefulSignStep suite params sk st q with
    | error err => simp
    | ok quad =>
      rcases quad with ⟨st', ep, msg, sig⟩
      dsimp only
      obtain ⟨hInv', hOkHead, hNextLe, hBranch⟩ :=
        checkedStatefulSignStep_preserves_inv suite params sk hInv hStep
      obtain ⟨hAllOkRest, hBoundRest, hUniqRest⟩ :=
        checkedStatefulOracleAux_invariant suite params sk rest (some st') none
          (fun s hs => by injection hs with hEq; exact hEq ▸ hInv')
      have hBndR := hBoundRest st' rfl
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | hTail
        · exact hOkHead
        · exact hAllOkRest e hTail
      · intro st0 hSome0 e he
        injection hSome0 with hStEq
        subst hStEq
        rcases List.mem_cons.mp he with rfl | hTail
        · rcases hBranch with ⟨hLat0, _⟩ | ⟨rfl, _, _⟩
          · exact .inl hLat0
          · exact .inr (Nat.le_refl _)
        · rcases hBndR e hTail with hLat1 | hGeNext'
          · rcases hBranch with ⟨_, rfl⟩ | ⟨rfl, _, hLatNew⟩
            · exact .inl hLat1
            · rw [hLatNew] at hLat1
              injection hLat1 with hEqE
              rw [← hEqE]
              exact .inr (Nat.le_refl _)
          · exact .inr (Nat.le_trans hNextLe hGeNext')
      · intro e₁ hM₁ e₂ hM₂ hEpEq
        have hHeadVsTail : ∀ e ∈ (execCheckedStatefulOracleAux suite params sk (some st') none rest).emittedLog,
            ep = e.1 → (ep, msg, sig) = e := by
          intro e hTail hEp
          rcases hBndR e hTail with hLat1 | hGeNext'
          · rcases hBranch with ⟨hLat0, rfl⟩ | ⟨_, _, hLatNew⟩
            · rw [hLat0] at hLat1; injection hLat1
            · rw [hLatNew] at hLat1; injection hLat1
          · rcases hBranch with ⟨hLat0, _⟩ | ⟨rfl, hNextEq, _⟩
            · obtain ⟨hLt, _⟩ := hInv ep msg sig hLat0
              omega
            · omega
        rcases List.mem_cons.mp hM₁ with rfl | hT₁ <;> rcases List.mem_cons.mp hM₂ with rfl | hT₂
        · rfl
        · exact hHeadVsTail e₂ hT₂ hEpEq
        · exact (hHeadVsTail e₁ hT₁ hEpEq.symm).symm
        · exact hUniqRest e₁ hT₁ e₂ hT₂ hEpEq

/-- Every signature in `(execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog`
    satisfies `StatefulLogEntryOk` and passes `verifyCheckedStateful`. -/
theorem checkedStatefulOracle_entryOk
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatefulQuery)
    {e : Nat × List UInt8 × PqHashSig}
    (he : e ∈ (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog) :
    StatefulLogEntryOk suite params sk e :=
  (checkedStatefulOracleAux_invariant suite params sk queries (some initCheckedStatefulLatch) none
    (fun s hs => by injection hs with hEq; exact hEq ▸ initCheckedStatefulLatch_inv suite params sk)).1 e he

theorem checkedStatefulOracle_accepts
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatefulQuery)
    {ep : Nat} {msg : List UInt8} {sig : PqHashSig}
    (he : (ep, msg, sig) ∈ (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog) :
    verifyCheckedStateful suite params (derivePublicKey suite params sk) msg sig = true := by
  have hOk := checkedStatefulOracle_entryOk suite params sk queries he
  obtain ⟨fuel, hEv⟩ := hOk.eval_generated
  have hVer := verifyPqHashSig_evalSingleSign suite params sk msg
    (buildStatefulDetOptDomain ep sk.pkSeed) ep fuel sig hEv
  rw [verifyCheckedStateful_eq, hOk.params_valid, hOk.leaf_eq_epoch]
  simp [hOk.epoch_lt, hVer]

/-- **Multi-Turn Checked Stateful Leaf Uniqueness (`checkedStatefulLog_one_message_per_leaf`)**:
    Across ANY sequence of `CheckedStatefulQuery` requests (including adversarial retries, stale epochs,
    equivocation attempts, varied `grindLimit`s, and budget-exhausting aborts), any two emitted
    entries `(ep₁, m₁, s₁)` and `(ep₂, m₂, s₂)` using the same leaf (`s₁.leafGlobalIdx = s₂.leafGlobalIdx`
    or `ep₁ = ep₂`) have **`ep₁ = ep₂ ∧ m₁ = m₂ ∧ s₁ = s₂`**! -/
theorem checkedStatefulLog_one_message_per_leaf
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatefulQuery)
    {e₁ e₂ : Nat × List UInt8 × PqHashSig}
    (he₁ : e₁ ∈ (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog)
    (he₂ : e₂ ∈ (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog)
    (hSameLeaf : e₁.2.2.leafGlobalIdx = e₂.2.2.leafGlobalIdx) :
    e₁ = e₂ := by
  have hOk₁ := checkedStatefulOracle_entryOk suite params sk queries he₁
  have hOk₂ := checkedStatefulOracle_entryOk suite params sk queries he₂
  have hEpEq : e₁.1 = e₂.1 := by rw [← hOk₁.leaf_eq_epoch, ← hOk₂.leaf_eq_epoch, hSameLeaf]
  exact (checkedStatefulOracleAux_invariant suite params sk queries (some initCheckedStatefulLatch) none
    (fun s hs => by injection hs with hEq; exact hEq ▸ initCheckedStatefulLatch_inv suite params sk)).2.2
    e₁ he₁ e₂ he₂ hEpEq

theorem statefulLogLayerDigits_valid {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {e : Nat × List UInt8 × PqHashSig}
    (hOk : StatefulLogEntryOk suite params sk e) (i : Nat) (hi : i < params.numLayers) :
    checkTargetSum params.w params.ell1 params.targetSum (statefulLogLayerDigits suite params sk e i) = true := by
  obtain ⟨fuel, dg, hm, hG, _⟩ := hOk.layer i hi
  obtain ⟨hmEq, hdEq, hChk⟩ := grindTswCounterAux_sound hG
  rw [statefulLogLayerDigits_eq, ← hmEq, ← hdEq]
  exact hChk

theorem statefulLogLayer_chains_revealed {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {e : Nat × List UInt8 × PqHashSig}
    (hOk : StatefulLogEntryOk suite params sk e) (i : Nat) (hi : i < params.numLayers)
    (r : Nat) (hr : r < params.ell1) :
    (e.2.2.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r [] =
      honestChainNode suite sk (UInt32.ofNat i)
        (UInt64.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
        (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight) r
        ((statefulLogLayerDigits suite params sk e i).getD r 0) := by
  obtain ⟨fuel, dg, hm, hG, hC⟩ := hOk.layer i hi
  obtain ⟨hmEq, hdEq, _⟩ := grindTswCounterAux_sound hG
  rw [hC, list_getD_map_range params.ell1 _ [] hr, statefulLogLayerDigits_eq, ← hmEq, ← hdEq]

/-- **Multi-Turn Checked Stateful One-Codeword-Per-`(layer, tree, leaf)` Invariant
    (`checkedStatefulLog_unique_layer_codeword`)**:
    For ANY two logged signatures `e₁, e₂` in a multi-turn checked stateful signing log and ANY
    layers `i₁, i₂ < params.numLayers` whose WOTS+C addresses `(layer, tree, keypair)` coincide,
    both signatures used the **exact same** layer index `i₁ = i₂`, subtree index, randomness,
    signed root, TSW counter, base-`w` digit codeword, and revealed WOTS+C chain values! -/
theorem checkedStatefulLog_unique_layer_codeword
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatefulQuery)
    {e₁ e₂ : Nat × List UInt8 × PqHashSig} {i₁ i₂ : Nat}
    (he₁ : e₁ ∈ (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog)
    (he₂ : e₂ ∈ (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog)
    (hi₁ : i₁ < params.numLayers) (hi₂ : i₂ < params.numLayers)
    (hAddr : wotsPosAddr params e₁.2.2.leafGlobalIdx i₁ = wotsPosAddr params e₂.2.2.leafGlobalIdx i₂) :
    i₁ = i₂ ∧
    e₁.2.2.leafGlobalIdx / 2 ^ (i₁ * params.subtreeHeight) =
      e₂.2.2.leafGlobalIdx / 2 ^ (i₂ * params.subtreeHeight) ∧
    honestStatefulLayerRand e₁ i₁ = honestStatefulLayerRand e₂ i₂ ∧
    honestStatefulLayerRoot suite params sk e₁.2.1 i₁
      (e₁.2.2.leafGlobalIdx / 2 ^ (i₁ * params.subtreeHeight)) =
      honestStatefulLayerRoot suite params sk e₂.2.1 i₂
        (e₂.2.2.leafGlobalIdx / 2 ^ (i₂ * params.subtreeHeight)) ∧
    (e₁.2.2.layerSigs.getD i₁ ⟨0, [], []⟩).tswCtr =
      (e₂.2.2.layerSigs.getD i₂ ⟨0, [], []⟩).tswCtr ∧
    statefulLogLayerDigits suite params sk e₁ i₁ =
      statefulLogLayerDigits suite params sk e₂ i₂ ∧
    (e₁.2.2.layerSigs.getD i₁ ⟨0, [], []⟩).wotsChains =
      (e₂.2.2.layerSigs.getD i₂ ⟨0, [], []⟩).wotsChains := by
  have hOk₁ := checkedStatefulOracle_entryOk suite params sk queries he₁
  have hOk₂ := checkedStatefulOracle_entryOk suite params sk queries he₂
  obtain ⟨hWf, _, _, _, _, _, _, hLayers⟩ := params.checkedStatefulValid_facts hOk₁.params_valid
  obtain ⟨hEqI, hPos⟩ := wotsPosAddr_inj params hWf hLayers hOk₁.leaf_lt hOk₂.leaf_lt hi₁ hi₂ hAddr
  subst hEqI
  cases i₁ with
  | zero =>
    have hSameLeaf : e₁.2.2.leafGlobalIdx = e₂.2.2.leafGlobalIdx := by
      simpa only [Nat.zero_mul, Nat.pow_zero, Nat.div_one] using hPos
    have hSameEntry := checkedStatefulLog_one_message_per_leaf suite params sk queries he₁ he₂ hSameLeaf
    subst hSameEntry
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k =>
    have hRandEq : honestStatefulLayerRand e₁ (k + 1) = honestStatefulLayerRand e₂ (k + 1) := rfl
    have hRootEq :
        honestStatefulLayerRoot suite params sk e₁.2.1 (k + 1)
          (e₁.2.2.leafGlobalIdx / 2 ^ ((k + 1) * params.subtreeHeight)) =
        honestStatefulLayerRoot suite params sk e₂.2.1 (k + 1)
          (e₂.2.2.leafGlobalIdx / 2 ^ ((k + 1) * params.subtreeHeight)) := by
      simp only [honestStatefulLayerRoot, Nat.add_one_ne_zero, ↓reduceIte, hPos]
    obtain ⟨f₁, dg₁, hm₁, hG₁, hC₁⟩ := hOk₁.layer (k + 1) hi₁
    obtain ⟨f₂, dg₂, hm₂, hG₂, hC₂⟩ := hOk₂.layer (k + 1) hi₁
    rw [hRandEq, hRootEq, hPos] at hG₁
    have hDet := grindTswCounterAux_det f₁ f₂ 0 hG₁ hG₂
    rcases Prod.mk.inj hDet with ⟨hCtrEq, hRestDet⟩
    rcases Prod.mk.inj hRestDet with ⟨hDgEq, _⟩
    have hLogDigEq :
        statefulLogLayerDigits suite params sk e₁ (k + 1) =
        statefulLogLayerDigits suite params sk e₂ (k + 1) := by
      rw [statefulLogLayerDigits_eq, statefulLogLayerDigits_eq, hRandEq, hRootEq, hPos, hCtrEq]
    have hChainsEq :
        (e₁.2.2.layerSigs.getD (k + 1) ⟨0, [], []⟩).wotsChains =
        (e₂.2.2.layerSigs.getD (k + 1) ⟨0, [], []⟩).wotsChains := by
      rw [hC₁, hC₂, hPos, hDgEq]
    exact ⟨rfl, hPos, hRandEq, hRootEq, hCtrEq, hLogDigEq, hChainsEq⟩

/-! ### Discharging `extractReachableHypertreeForgery` from Finite Signing Logs -/

/-- Address injectivity against a reachable upper-layer coordinate `(l, g)` (`0 < l < d`,
    `g < 2 ^ ((d - l) * h)`): eliminates both `UInt32` layer wraparound and `UInt64` tree wraparound. -/
theorem wotsPosAddr_eq_of_reachable (params : PqHashParams)
    (hWf : params.wellFormed = true) (hLayers : params.numLayers ≤ 2 ^ 32)
    {leaf i l g : Nat}
    (hLeaf : leaf < 2 ^ (params.numLayers * params.subtreeHeight))
    (hi : i < params.numLayers)
    (hReach : ReachableUpperHypertreePos params l g)
    (hAddr : wotsPosAddr params leaf i =
      (UInt32.ofNat l, UInt64.ofNat (g / 2 ^ params.subtreeHeight), UInt32.ofNat (g % 2 ^ params.subtreeHeight))) :
    i = l ∧ leaf / 2 ^ (i * params.subtreeHeight) = g := by
  obtain ⟨_, hlLt, hgLt⟩ := hReach
  obtain ⟨_, _, hH, _, hDH, _⟩ := params.wellFormed_facts hWf
  rw [wotsPosAddr_eq] at hAddr
  obtain ⟨h1, h23⟩ := Prod.mk.inj hAddr
  obtain ⟨h2, h3⟩ := Prod.mk.inj h23
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  rw [h32] at hLayers
  have hii : i = l := uint32_ofNat_inj (Nat.lt_of_lt_of_le hi hLayers)
    (Nat.lt_of_lt_of_le hlLt hLayers) h1
  subst hii
  refine ⟨rfl, ?_⟩
  have hP : 2 ^ params.subtreeHeight ≤ 1073741824 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) hH) (by decide)
  have hPpos : 0 < 2 ^ params.subtreeHeight := Nat.two_pow_pos _
  have hB : 2 ^ (params.numLayers * params.subtreeHeight) ≤ 4611686018427387904 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) hDH) (by decide)
  have hSubPowLe : 2 ^ ((params.numLayers - i) * params.subtreeHeight) ≤
      2 ^ (params.numLayers * params.subtreeHeight) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  have hgBound : g < 2 ^ (params.numLayers * params.subtreeHeight) :=
    Nat.lt_of_lt_of_le hgLt hSubPowLe
  have hG : leaf / 2 ^ (i * params.subtreeHeight) ≤ leaf := Nat.div_le_self _ _
  have hT : leaf / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight ≤
      leaf / 2 ^ (i * params.subtreeHeight) := Nat.div_le_self _ _
  have hTg : g / 2 ^ params.subtreeHeight ≤ g := Nat.div_le_self _ _
  have hK := Nat.mod_lt (leaf / 2 ^ (i * params.subtreeHeight)) hPpos
  have hKg := Nat.mod_lt g hPpos
  have e2 := uint64_ofNat_inj (Nat.lt_of_le_of_lt hT (by omega)) (Nat.lt_of_le_of_lt hTg (by omega)) h2
  have e3 := uint32_ofNat_inj (Nat.lt_of_lt_of_le hK (by omega)) (Nat.lt_of_lt_of_le hKg (by omega)) h3
  have d1 := Nat.div_add_mod (leaf / 2 ^ (i * params.subtreeHeight)) (2 ^ params.subtreeHeight)
  have d2 := Nat.div_add_mod g (2 ^ params.subtreeHeight)
  rw [e2, e3] at d1
  exact d1.symm.trans d2

/-- Search `0 .. params.numLayers - 1` for a layer `i` matching `(layer, tree, kp)`. -/
def findLayerMatchInRange (params : PqHashParams) (leaf : Nat)
    (layer : UInt32) (tree : UInt64) (kp : Nat) : List Nat → Option Nat
  | [] => none
  | i :: is =>
    if wotsPosAddr params leaf i == (layer, tree, UInt32.ofNat kp) then some i
    else findLayerMatchInRange params leaf layer tree kp is

private theorem findLayerMatchInRange_sound {params : PqHashParams} {leaf : Nat}
    {layer : UInt32} {tree : UInt64} {kp : Nat} :
    ∀ {is : List Nat} {i : Nat},
      findLayerMatchInRange params leaf layer tree kp is = some i →
      i ∈ is ∧ wotsPosAddr params leaf i = (layer, tree, UInt32.ofNat kp)
  | [], _, h => by cases h
  | x :: xs, i, h => by
    unfold findLayerMatchInRange at h
    cases hEq : (wotsPosAddr params leaf x == (layer, tree, UInt32.ofNat kp))
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hMem, hAddr⟩ := findLayerMatchInRange_sound h
      exact ⟨List.mem_cons_of_mem x hMem, hAddr⟩
    · simp only [hEq, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_self, of_decide_eq_true (by simpa [beq_iff_eq] using hEq)⟩

/-- Concrete `QueriedWotsOracle` built directly from a finite `(msg, sig)` signing log. -/
def logQueriedWotsOracle (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) : List (List UInt8 × PqHashSig) → QueriedWotsOracle
  | [], _, _, _ => none
  | (msg, sig) :: rest, layer, tree, kp =>
    if !(decide (kp < 2 ^ params.subtreeHeight)) then none
    else
      match findLayerMatchInRange params sig.leafGlobalIdx layer tree kp (List.range params.numLayers) with
      | some i =>
        let pkRoot := (derivePublicKey suite params sk).pkRoot
        let g := sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)
        let hRand := if params.statefulJorts && (i == 0) then sig.rRand else []
        let hRoot :=
          if i == 0 then
            if params.statefulJorts then thPreHash suite sk.pkSeed pkRoot msg
            else computeForsPk suite params sk (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
                   (g % 2 ^ params.subtreeHeight)
          else
            computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1)) (UInt64.ofNat g)
        let lsig := sig.layerSigs.getD i ⟨0, [], []⟩
        some (hRand, hRoot, lsig.tswCtr, lsig.wotsChains)
      | none => logQueriedWotsOracle suite params sk rest layer tree kp

private theorem logQueriedWotsOracle_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) :
    ∀ (entries : List (List UInt8 × PqHashSig)) {layer : UInt32} {tree : UInt64} {kp : Nat}
      {hRand hRoot : List UInt8} {hCtr : Nat} {hChains : List (List UInt8)},
      logQueriedWotsOracle suite params sk entries layer tree kp = some (hRand, hRoot, hCtr, hChains) →
      kp < 2 ^ params.subtreeHeight ∧
      ∃ msg sig i, (msg, sig) ∈ entries ∧ i < params.numLayers ∧
        wotsPosAddr params sig.leafGlobalIdx i = (layer, tree, UInt32.ofNat kp) ∧
        hRand = (if params.statefulJorts && (i == 0) then sig.rRand else []) ∧
        hRoot = (if i == 0 then
                   if params.statefulJorts then
                     thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg
                   else
                     computeForsPk suite params sk
                       (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
                       (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
                 else
                   computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1))
                     (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))) ∧
        hCtr = (sig.layerSigs.getD i ⟨0, [], []⟩).tswCtr ∧
        hChains = (sig.layerSigs.getD i ⟨0, [], []⟩).wotsChains
  | [], _, _, _, _, _, _, _, h => by cases h
  | (msg, sig) :: rest, layer, tree, kp, hRand, hRoot, hCtr, hChains, h => by
    unfold logQueriedWotsOracle at h
    cases hKp : decide (kp < 2 ^ params.subtreeHeight)
    · simp [hKp] at h
    · simp only [hKp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hFind : findLayerMatchInRange params sig.leafGlobalIdx layer tree kp (List.range params.numLayers) with
      | none =>
        rw [hFind] at h
        obtain ⟨hKpLt, m', s', i', hMem, hi', hAd, hR1, hR2, hC1, hC2⟩ :=
          logQueriedWotsOracle_sound suite params sk rest h
        exact ⟨hKpLt, m', s', i', List.mem_cons_of_mem _ hMem, hi', hAd, hR1, hR2, hC1, hC2⟩
      | some i =>
        rw [hFind] at h
        dsimp only at h
        injection h with hTup
        rcases Prod.mk.inj hTup with ⟨hR1, hT2⟩
        rcases Prod.mk.inj hT2 with ⟨hR2, hT3⟩
        rcases Prod.mk.inj hT3 with ⟨hC1, hC2⟩
        obtain ⟨hMemRange, hAddr⟩ := findLayerMatchInRange_sound hFind
        exact ⟨of_decide_eq_true hKp, msg, sig, i, List.mem_cons_self,
          List.mem_range.mp hMemRange, hAddr, hR1.symm, hR2.symm, hC1.symm, hC2.symm⟩

/-- Finite-log instantiation of `extractReachableHypertreeForgery` for checked stateful `Jorts`:
    constructively discharges **all** oracle hypotheses from
    `(execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog`! -/
def extractReachableHypertreeForgery_of_checkedStatefulLog
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatefulQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hValidParams : params.checkedStatefulValid = true)
    (hFreshMsg : msgStar ∉ ((execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog.map fun e => e.2.1))
    (hAccept : verifyPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    HypertreeForgeryBreak suite params sk msgStar sigStar [] :=
  let rawLog := (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog
  let entries := rawLog.map fun e => (e.2.1, e.2.2)
  let qOrc := logQueriedWotsOracle suite params sk entries
  have hFacts := params.checkedStatefulValid_facts hValidParams
  have hWf : params.wellFormed = true := hFacts.1
  have hSt : params.statefulJorts = true := hFacts.2.1
  have hDPos : 0 < params.numLayers := hFacts.2.2.2.2.2.1
  have hLayers : params.numLayers ≤ 2 ^ 32 := hFacts.2.2.2.2.2.2.2
  have hStarLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) := by
    unfold verifyPqHashSig at hAccept
    cases hIdx : decide (sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    · have hNot : ¬ (sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) := of_decide_eq_false hIdx
      cases hLen : (sigStar.layerSigs.length != params.numLayers)
      · simp [hWf, hNot] at hAccept
      · simp [hWf, hNot] at hAccept
    · exact of_decide_eq_true hIdx
  extractReachableHypertreeForgery suite params sk msgStar sigStar (entries.map Prod.fst) qOrc []
    hGeom
    (by simpa [entries, List.map_map] using hFreshMsg)
    hAccept
    (fun _ hRand hRoot hCtr hChains hQ => by
      obtain ⟨_, msg, sig, i, hMemE, hi, hAddr, _, hRootEq, _, _⟩ :=
        logQueriedWotsOracle_sound suite params sk entries hQ
      obtain ⟨e, heRaw, hPair⟩ := List.mem_map.mp hMemE
      rcases Prod.mk.inj hPair with ⟨hM, hS⟩
      subst hM; subst hS
      have hOk := checkedStatefulOracle_entryOk suite params sk queries heRaw
      have hAddr0 : wotsPosAddr params e.2.2.leafGlobalIdx i = wotsPosAddr params sigStar.leafGlobalIdx 0 := by
        rw [wotsPosAddr_eq params sigStar.leafGlobalIdx 0]
        simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
        exact hAddr
      obtain ⟨hI0, _⟩ := wotsPosAddr_inj params hWf hLayers hOk.leaf_lt hStarLt hi hDPos hAddr0
      subst hI0
      simp only [beq_self_eq_true, ↓reduceIte, hSt] at hRootEq
      exact ⟨e.2.1, List.mem_map.mpr ⟨(e.2.1, e.2.2), hMemE, rfl⟩, hRootEq⟩)
    (fun hStFalse => by rw [hSt] at hStFalse; cases hStFalse)
    (fun l g hReach => by
      refine ⟨?_, ?_⟩
      · intro hRand hCtr hChains hQ
        obtain ⟨_, msg, sig, i, hMemE, hi, hAddr, hRandEq, _, hCtrEq, hChainsEq⟩ :=
          logQueriedWotsOracle_sound suite params sk entries hQ
        obtain ⟨e, heRaw, hPair⟩ := List.mem_map.mp hMemE
        rcases Prod.mk.inj hPair with ⟨hM, hS⟩
        subst hM; subst hS
        have hOk := checkedStatefulOracle_entryOk suite params sk queries heRaw
        obtain ⟨hIL, hPosG⟩ := wotsPosAddr_eq_of_reachable params hWf hLayers hOk.leaf_lt hi hReach hAddr
        subst hIL
        have hINe0 : (i == 0) = false := beq_false_of_ne (Nat.ne_of_gt hReach.1)
        simp only [hINe0, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hRandEq
        obtain ⟨fuel, dg, hm, hG, hC⟩ := hOk.layer i hi
        obtain ⟨hmEq, hdEq, hChk⟩ := grindTswCounterAux_sound hG
        have hRandI : honestStatefulLayerRand e i = [] := by
          unfold honestStatefulLayerRand; simp [Nat.ne_of_gt hReach.1]
        have hRootI : honestStatefulLayerRoot suite params sk e.2.1 i
            (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) =
            computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1)) (UInt64.ofNat g) := by
          unfold honestStatefulLayerRoot; simp [Nat.ne_of_gt hReach.1, hPosG]
        rw [hRandI, hRootI, hPosG] at hmEq
        dsimp only
        rw [hRandEq, hCtrEq, hChainsEq, ← hmEq, ← hdEq]
        refine ⟨hChk, ?_⟩
        rw [hC, hPosG]
        exact recoverWotsPkFromSig_eq_computeWotsPk suite params sk (UInt32.ofNat i)
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) dg hChk
      · intro hRand hR hCtr hChains hQ
        obtain ⟨_, msg, sig, i, hMemE, hi, hAddr, _, hRootEq, _, _⟩ :=
          logQueriedWotsOracle_sound suite params sk entries hQ
        obtain ⟨e, heRaw, hPair⟩ := List.mem_map.mp hMemE
        rcases Prod.mk.inj hPair with ⟨hM, hS⟩
        subst hM; subst hS
        have hOk := checkedStatefulOracle_entryOk suite params sk queries heRaw
        obtain ⟨hIL, hPosG⟩ := wotsPosAddr_eq_of_reachable params hWf hLayers hOk.leaf_lt hi hReach hAddr
        subst hIL
        have hINe0 : (i == 0) = false := beq_false_of_ne (Nat.ne_of_gt hReach.1)
        simp only [hINe0, Bool.false_eq_true, ↓reduceIte, hPosG] at hRootEq
        exact hRootEq)
    (fun hRand hRoot0 hCtr hChains hQ => by
      obtain ⟨_, msg, sig, i, hMemE, hi, hAddr, hRandEq, hRootEq, hCtrEq, hChainsEq⟩ :=
        logQueriedWotsOracle_sound suite params sk entries hQ
      obtain ⟨e, heRaw, hPair⟩ := List.mem_map.mp hMemE
      rcases Prod.mk.inj hPair with ⟨hM, hS⟩
      subst hM; subst hS
      have hOk := checkedStatefulOracle_entryOk suite params sk queries heRaw
      have hAddr0 : wotsPosAddr params e.2.2.leafGlobalIdx i = wotsPosAddr params sigStar.leafGlobalIdx 0 := by
        rw [wotsPosAddr_eq params sigStar.leafGlobalIdx 0]
        simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
        exact hAddr
      obtain ⟨hI0, hPos0⟩ := wotsPosAddr_inj params hWf hLayers hOk.leaf_lt hStarLt hi hDPos hAddr0
      subst hI0
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one] at hPos0
      simp only [beq_self_eq_true, Bool.and_true, ↓reduceIte, hSt] at hRandEq hRootEq
      obtain ⟨fuel, dg, hm, hG, hC⟩ := hOk.layer 0 hi
      obtain ⟨hmEq, hdEq, hChk⟩ := grindTswCounterAux_sound hG
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one, honestStatefulLayerRand,
                 honestStatefulLayerRoot, ↓reduceIte] at hmEq hC
      rw [hPos0] at hmEq hC
      have hU0 : UInt32.ofNat 0 = (0 : UInt32) := rfl
      rw [hU0] at hmEq hC
      dsimp only
      rw [hRandEq, hRootEq, hCtrEq, hChainsEq, ← hmEq, ← hdEq]
      refine ⟨hChk, ?_⟩
      rw [hC]
      exact recoverWotsPkFromSig_eq_computeWotsPk suite params sk 0
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight) dg hChk)

/-- Finite-log instantiation of `extractReachableHypertreeForgery` for stateless profiles
    (`params.statefulJorts = false`), constructively discharging all four oracle hypotheses
    from `signingOracleLog suite params sk queries`. -/
def extractReachableHypertreeForgery_of_statelessLog
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List PqSigningQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hStateless : params.statefulJorts = false)
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (hFreshMsg : msgStar ∉ (signingOracleLog suite params sk queries).map Prod.fst)
    (hAccept : verifyPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    HypertreeForgeryBreak suite params sk msgStar sigStar
      ((signingOracleLog suite params sk queries).flatMap fun e =>
        (List.range params.forsTrees).map fun j =>
          (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ params.subtreeHeight),
           e.2.leafGlobalIdx % 2 ^ params.subtreeHeight,
           sigForsLeafIdx suite params (derivePublicKey suite params sk) e.1 e.2 j)) :=
  let entries := signingOracleLog suite params sk queries
  let qOrc := logQueriedWotsOracle suite params sk entries
  let revFors := entries.flatMap fun e =>
    (List.range params.forsTrees).map fun j =>
      (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ params.subtreeHeight),
       e.2.leafGlobalIdx % 2 ^ params.subtreeHeight,
       sigForsLeafIdx suite params (derivePublicKey suite params sk) e.1 e.2 j)
  have hWf : params.wellFormed = true := by
    unfold verifyPqHashSig at hAccept
    cases hw : params.wellFormed
    · simp [hw] at hAccept
    · rfl
  have hDPos : 0 < params.numLayers := (params.wellFormed_facts hWf).1
  have hStarLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) := by
    unfold verifyPqHashSig at hAccept
    cases hIdx : decide (sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    · have hNot : ¬ (sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) := of_decide_eq_false hIdx
      cases hLen : (sigStar.layerSigs.length != params.numLayers)
      · simp [hWf, hNot] at hAccept
      · simp [hWf, hNot] at hAccept
    · exact of_decide_eq_true hIdx
  extractReachableHypertreeForgery suite params sk msgStar sigStar (entries.map Prod.fst) qOrc revFors
    hGeom hFreshMsg hAccept
    (fun hStTrue => by rw [hStateless] at hStTrue; cases hStTrue)
    (fun _ hRand hRoot hCtr hChains hQ => by
      obtain ⟨_, msg, sig, i, hMemE, hi, hAddr, _, hRootEq, _, _⟩ :=
        logQueriedWotsOracle_sound suite params sk entries hQ
      have hOk := signingOracleLog_entryOk suite params sk queries hStateless (msg, sig) hMemE
      have hAddr0 : wotsPosAddr params sig.leafGlobalIdx i = wotsPosAddr params sigStar.leafGlobalIdx 0 := by
        rw [wotsPosAddr_eq params sigStar.leafGlobalIdx 0]
        simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
        exact hAddr
      obtain ⟨hI0, hPos0⟩ := wotsPosAddr_inj params hWf hLayers hOk.leaf_lt hStarLt hi hDPos hAddr0
      subst hI0
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one] at hPos0
      simp only [↓reduceIte, hStateless, Bool.false_eq_true, Nat.zero_mul, Nat.pow_zero, Nat.div_one, hPos0] at hRootEq
      exact hRootEq)
    (fun l g hReach => by
      refine ⟨?_, ?_⟩
      · intro hRand hCtr hChains hQ
        obtain ⟨_, msg, sig, i, hMemE, hi, hAddr, hRandEq, _, hCtrEq, hChainsEq⟩ :=
          logQueriedWotsOracle_sound suite params sk entries hQ
        have hOk := signingOracleLog_entryOk suite params sk queries hStateless (msg, sig) hMemE
        obtain ⟨hIL, hPosG⟩ := wotsPosAddr_eq_of_reachable params hWf hLayers hOk.leaf_lt hi hReach hAddr
        subst hIL
        have hINe0 : (i == 0) = false := beq_false_of_ne (Nat.ne_of_gt hReach.1)
        simp only [hINe0, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hRandEq
        obtain ⟨fuel, dg, hm, hG, hC⟩ := hOk.layer i hi
        obtain ⟨hmEq, hdEq, hChk⟩ := grindTswCounterAux_sound hG
        have hRootI : honestLayerRoot suite params sk i (sig.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) =
            computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1)) (UInt64.ofNat g) := by
          rw [honestLayerRoot_eq]; simp [Nat.ne_of_gt hReach.1, hPosG]
        rw [hRootI, hPosG] at hmEq
        dsimp only
        rw [hRandEq, hCtrEq, hChainsEq, ← hmEq, ← hdEq]
        refine ⟨hChk, ?_⟩
        rw [hC, hPosG]
        exact recoverWotsPkFromSig_eq_computeWotsPk suite params sk (UInt32.ofNat i)
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight) dg hChk
      · intro hRand hR hCtr hChains hQ
        obtain ⟨_, msg, sig, i, hMemE, hi, hAddr, _, hRootEq, _, _⟩ :=
          logQueriedWotsOracle_sound suite params sk entries hQ
        have hOk := signingOracleLog_entryOk suite params sk queries hStateless (msg, sig) hMemE
        obtain ⟨hIL, hPosG⟩ := wotsPosAddr_eq_of_reachable params hWf hLayers hOk.leaf_lt hi hReach hAddr
        subst hIL
        have hINe0 : (i == 0) = false := beq_false_of_ne (Nat.ne_of_gt hReach.1)
        simp only [hINe0, Bool.false_eq_true, ↓reduceIte, hPosG] at hRootEq
        exact hRootEq)
    (fun hRand hRoot0 hCtr hChains hQ => by
      obtain ⟨_, msg, sig, i, hMemE, hi, hAddr, hRandEq, hRootEq, hCtrEq, hChainsEq⟩ :=
        logQueriedWotsOracle_sound suite params sk entries hQ
      have hOk := signingOracleLog_entryOk suite params sk queries hStateless (msg, sig) hMemE
      have hAddr0 : wotsPosAddr params sig.leafGlobalIdx i = wotsPosAddr params sigStar.leafGlobalIdx 0 := by
        rw [wotsPosAddr_eq params sigStar.leafGlobalIdx 0]
        simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
        exact hAddr
      obtain ⟨hI0, hPos0⟩ := wotsPosAddr_inj params hWf hLayers hOk.leaf_lt hStarLt hi hDPos hAddr0
      subst hI0
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one] at hPos0
      simp only [hStateless, Bool.false_and, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte,
                 Nat.zero_mul, Nat.pow_zero, Nat.div_one] at hRandEq hRootEq
      obtain ⟨fuel, dg, hm, hG, hC⟩ := hOk.layer 0 hi
      obtain ⟨hmEq, hdEq, hChk⟩ := grindTswCounterAux_sound hG
      rw [honestLayerRoot_eq] at hmEq
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one, ↓reduceIte] at hmEq hC
      rw [hPos0] at hmEq hC hRootEq
      have hU0 : UInt32.ofNat 0 = (0 : UInt32) := rfl
      rw [hU0] at hmEq hC
      dsimp only
      rw [hRandEq, hRootEq, hCtrEq, hChainsEq, ← hmEq, ← hdEq]
      refine ⟨hChk, ?_⟩
      rw [hC]
      exact recoverWotsPkFromSig_eq_computeWotsPk suite params sk 0
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight) dg hChk)

/-! ### Transcript-Indexed Constructive (`PSum`, `0 Classical.choice`) Checked Stateful EUF-CMA Reduction -/

/-- Explicit `Type`-valued classification of every honest hash input fixed by `(sk, log)` in a
    checked stateful `Jorts` signing transcript. -/
inductive HonestStatefulTargetKind (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (Nat × List UInt8 × PqHashSig)) : List UInt8 → Type where
  | xmssNode (layer : UInt32) (tree : UInt64) (h n : Nat) :
      HonestStatefulTargetKind suite params sk log
        (thPreimage tagThH sk.pkSeed ⟨layer, tree, .tree, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
          [computeMerkleNode suite sk.pkSeed layer tree .tree
             (computeWotsPk suite params sk layer tree) h (2 * n),
           computeMerkleNode suite sk.pkSeed layer tree .tree
             (computeWotsPk suite params sk layer tree) h (2 * n + 1)])
  | wotsPk (layer : UInt32) (tree : UInt64) (kp : Nat) :
      HonestStatefulTargetKind suite params sk log
        (thPreimage tagThTl sk.pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
          ((List.range params.ell1).map fun r =>
            honestChainNode suite sk layer tree kp r (params.w - 1)))
  | chainStep (layer : UInt32) (tree : UInt64) (kp r step : Nat) :
      HonestStatefulTargetKind suite params sk log
        (thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat step⟩
          [honestChainNode suite sk layer tree kp r step])
  | layerDigest (e : Nat × List UInt8 × PqHashSig) (he : e ∈ log) (i : Nat) (hi : i < params.numLayers) :
      HonestStatefulTargetKind suite params sk log
        (thPreimage tagHMsg sk.pkSeed
          ⟨UInt32.ofNat i,
           UInt64.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight),
           .wotsHash,
           UInt32.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight),
           0,
           UInt32.ofNat (e.2.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr⟩
          [honestStatefulLayerRand e i,
           (derivePublicKey suite params sk).pkRoot,
           honestStatefulLayerRoot suite params sk e.2.1 i
             (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)),
           be 4 (e.2.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr])
  | messagePreHash (e : Nat × List UInt8 × PqHashSig) (he : e ∈ log) :
      HonestStatefulTargetKind suite params sk log
        (thPreimage tagHPre sk.pkSeed zeroAdrs [(derivePublicKey suite params sk).pkRoot, e.2.1])

/-- Transcript-indexed SM-TCR / second-preimage collision witness against an explicit honest
    preimage determined by `(sk, log)`. -/
structure CheckedStatefulCollisionWitness (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (Nat × List UInt8 × PqHashSig)) : Type where
  honestInput : List UInt8
  forgedInput : List UInt8
  targetKind  : HonestStatefulTargetKind suite params sk log honestInput
  distinct    : forgedInput ≠ honestInput
  collides    : suite.rawHash forgedInput = suite.rawHash honestInput

/-- Project a transcript-indexed `CheckedStatefulCollisionWitness` to `HashCollisionWitness`. -/
def CheckedStatefulCollisionWitness.toHashCollisionWitness
    {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {log : List (Nat × List UInt8 × PqHashSig)}
    (w : CheckedStatefulCollisionWitness suite params sk log) :
    HashCollisionWitness suite.rawHash :=
  { m1 := w.forgedInput, m2 := w.honestInput, ne := w.distinct, eq := w.collides }

/-- Transcript-indexed WOTS+C / TSW backward chain-inversion witness:
    exhibits a layer `layerIdx < params.numLayers` and chain `chainIdx < params.ell1` where the
    forgery `sigStar` supplies a preimage of the **honest** chain node `forgedDigit + 1` at a
    step `forgedDigit` strictly smaller than **every** step ever disclosed at that WOTS+C address
    across the entire multi-turn transcript `log`. -/
structure CheckedStatefulWotsTswWitness (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (Nat × List UInt8 × PqHashSig))
    (msgStar : List UInt8) (sigStar : PqHashSig) : Type where
  layerIdx          : Nat
  layer_lt          : layerIdx < params.numLayers
  chainIdx          : Nat
  chain_lt          : chainIdx < params.ell1
  signedLayerDigest : List UInt8
  layer0_digest     :
    layerIdx = 0 →
      signedLayerDigest = thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msgStar
  forgedDigit       : Nat
  forgedDigit_eq    :
    forgedDigit =
      (extractBaseWDigits params.w params.ell1
        (thHashMsg suite (if layerIdx = 0 then sigStar.rRand else []) sk.pkSeed
          (derivePublicKey suite params sk).pkRoot signedLayerDigest
          (UInt32.ofNat layerIdx)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (layerIdx * params.subtreeHeight) / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (layerIdx * params.subtreeHeight) % 2 ^ params.subtreeHeight))
          (sigStar.layerSigs.getD layerIdx ⟨0, [], []⟩).tswCtr)).getD chainIdx 0
  digit_lt          : forgedDigit < params.w - 1
  invertsHonest     :
    thChainF suite sk.pkSeed
      ⟨UInt32.ofNat layerIdx,
       UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (layerIdx * params.subtreeHeight) / 2 ^ params.subtreeHeight),
       .wotsHash,
       UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (layerIdx * params.subtreeHeight) % 2 ^ params.subtreeHeight),
       UInt32.ofNat chainIdx, UInt32.ofNat forgedDigit⟩
      ((sigStar.layerSigs.getD layerIdx ⟨0, [], []⟩).wotsChains.getD chainIdx []) =
    honestChainNode suite sk (UInt32.ofNat layerIdx)
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (layerIdx * params.subtreeHeight) / 2 ^ params.subtreeHeight))
      (sigStar.leafGlobalIdx / 2 ^ (layerIdx * params.subtreeHeight) % 2 ^ params.subtreeHeight)
      chainIdx (forgedDigit + 1)
  unrevealedInLog   :
    ∀ e ∈ log, ∀ i', i' < params.numLayers →
      wotsPosAddr params e.2.2.leafGlobalIdx i' = wotsPosAddr params sigStar.leafGlobalIdx layerIdx →
      forgedDigit < (statefulLogLayerDigits suite params sk e i').getD chainIdx 0

/-- Project a transcript-indexed `CheckedStatefulWotsTswWitness` to `WotsBackwardInversionWitness`. -/
def CheckedStatefulWotsTswWitness.toWotsBackwardInversionWitness
    {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {log : List (Nat × List UInt8 × PqHashSig)}
    {msgStar : List UInt8} {sigStar : PqHashSig}
    (w : CheckedStatefulWotsTswWitness suite params sk log msgStar sigStar) :
    WotsBackwardInversionWitness suite sk.pkSeed :=
  let g := sigStar.leafGlobalIdx / 2 ^ (w.layerIdx * params.subtreeHeight)
  let tree := UInt64.ofNat (g / 2 ^ params.subtreeHeight)
  let kp := g % 2 ^ params.subtreeHeight
  { layer := UInt32.ofNat w.layerIdx
    tree := tree
    kp := kp
    chain := w.chainIdx
    step := w.forgedDigit
    revealedStep := w.forgedDigit + 1
    step_lt := Nat.lt_succ_self w.forgedDigit
    preimage := (sigStar.layerSigs.getD w.layerIdx ⟨0, [], []⟩).wotsChains.getD w.chainIdx []
    revealedVal := honestChainNode suite sk (UInt32.ofNat w.layerIdx) tree kp w.chainIdx (w.forgedDigit + 1)
    invertsChain := w.invertsHonest }

private def thCall_eq_psum (suite : TweakableHashSuite)
    {t₁ p₁ : List UInt8} {a₁ : HashAdrs} {xs₁ : List (List UInt8)}
    {t₂ p₂ : List UInt8} {a₂ : HashAdrs} {xs₂ : List (List UInt8)}
    (hEq : thCall suite t₁ p₁ a₁ xs₁ = thCall suite t₂ p₂ a₂ xs₂) :
    PSum (t₁ = t₂ ∧ p₁ = p₂ ∧ a₁ = a₂ ∧ xs₁ = xs₂)
         (thPreimage t₁ p₁ a₁ xs₁ ≠ thPreimage t₂ p₂ a₂ xs₂ ∧
          suite.rawHash (thPreimage t₁ p₁ a₁ xs₁) = suite.rawHash (thPreimage t₂ p₂ a₂ xs₂)) :=
  if hPre : thPreimage t₁ p₁ a₁ xs₁ = thPreimage t₂ p₂ a₂ xs₂ then
    .inl (thPreimage_injective hPre)
  else
    .inr ⟨hPre, by rw [← thCall_eq, ← thCall_eq]; exact hEq⟩

private def boundedSearchPSum (p : Nat → Prop) (hDec : ∀ i, PSum (p i) (¬ p i)) :
    (n : Nat) → PSum { i : Nat // i < n ∧ p i } (∀ i, i < n → ¬ p i)
  | 0 => .inr (fun i hi => absurd hi (Nat.not_lt_zero i))
  | n + 1 =>
    match boundedSearchPSum p hDec n with
    | .inl ⟨i, hi, hp⟩ => .inl ⟨i, ⟨Nat.lt_succ_of_lt hi, hp⟩⟩
    | .inr hNone =>
      match hDec n with
      | .inl hp => .inl ⟨n, ⟨Nat.lt_succ_self n, hp⟩⟩
      | .inr hn => .inr (fun i hi => by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
          · exact hNone i hlt
          · rw [heq]; exact hn)

private def listSearchPSum {α : Type} (p : α → Prop) (hDec : ∀ a, PSum (p a) (¬ p a)) :
    (l : List α) → PSum { a : α // a ∈ l ∧ p a } (∀ a, a ∈ l → ¬ p a)
  | [] => .inr (fun _ h => by cases h)
  | x :: xs =>
    match hDec x with
    | .inl hp => .inl ⟨x, ⟨List.mem_cons_self, hp⟩⟩
    | .inr hn =>
      match listSearchPSum p hDec xs with
      | .inl ⟨a, ⟨ha, hp⟩⟩ => .inl ⟨a, ⟨List.mem_cons_of_mem x ha, hp⟩⟩
      | .inr hNone => .inr (fun a ha => by
          rcases List.mem_cons.mp ha with heq | hTl
          · rw [heq]; exact hn
          · exact hNone a hTl)

private def walkMerkle_meets_honest_psum (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (leafFn : Nat → List UInt8) (C : Type)
    (mkCol : ∀ (h n : Nat) (forged : List UInt8),
      forged ≠ thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
        [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
         computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)] →
      suite.rawHash forged = suite.rawHash
        (thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
          [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
           computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)]) → C) :
    ∀ (h nodeIdx localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8)),
      localIdx < 2 ^ h →
      walkMerkleAuthPath suite pkSeed layer tree kind h nodeIdx localIdx leaf path =
        some (computeMerkleNode suite pkSeed layer tree kind leafFn h nodeIdx) →
      PSum (leaf = leafFn (nodeIdx * 2 ^ h + localIdx)) C
  | 0, nodeIdx, localIdx, leaf, path, hLt, hW =>
    match path, hW with
    | [], hW => by
      simp only [walkMerkleAuthPath, computeMerkleNode, Option.some.injEq] at hW
      have h0 : localIdx = 0 := by rw [Nat.pow_zero] at hLt; omega
      exact .inl (by rw [h0, Nat.pow_zero, Nat.mul_one, Nat.add_zero]; exact hW)
    | _ :: _, hW => False.elim (by simp [walkMerkleAuthPath] at hW)
  | h + 1, nodeIdx, localIdx, leaf, path, hLt, hW =>
    match path, hW with
    | [], hW => False.elim (by simp [walkMerkleAuthPath] at hW)
    | sib :: rest, hW =>
      have hMul : nodeIdx * 2 ^ (h + 1) = (2 * nodeIdx) * 2 ^ h := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (nodeIdx * 2 ^ h) 2, Nat.mul_assoc]
      if hHalf : localIdx < 2 ^ h then
        match hSub : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx) localIdx leaf rest with
        | none =>
          False.elim (by simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub] at hW; cases hW)
        | some sub =>
          have hCallEq : thCall suite tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩ [sub, sib] =
              thCall suite tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
                [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx),
                 computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx + 1)] := by
            rw [computeMerkleNode_succ] at hW
            simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub, Option.some.injEq] at hW
            exact hW
          match thCall_eq_psum suite hCallEq with
          | .inl ⟨_, _, _, hArgs⟩ =>
            have hSubEq : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx) localIdx leaf rest =
                some (computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx)) := by
              simp only [List.cons.injEq, and_true] at hArgs
              rw [← hArgs.1]; exact hSub
            match walkMerkle_meets_honest_psum suite pkSeed layer tree kind leafFn C mkCol
                    h (2 * nodeIdx) localIdx leaf rest hHalf hSubEq with
            | .inl hLeaf => .inl (by rw [hMul]; exact hLeaf)
            | .inr c => .inr c
          | .inr ⟨hNe, hHash⟩ => .inr (mkCol h nodeIdx _ hNe hHash)
      else
        match hSub : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf rest with
        | none =>
          False.elim (by simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub] at hW; cases hW)
        | some sub =>
          have hSubLt : localIdx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hLt; omega
          have hIdxEq : nodeIdx * 2 ^ (h + 1) + localIdx =
              (2 * nodeIdx + 1) * 2 ^ h + (localIdx - 2 ^ h) := by
            rw [hMul, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_not_lt hHalf)]
          have hCallEq : thCall suite tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩ [sib, sub] =
              thCall suite tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
                [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx),
                 computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx + 1)] := by
            rw [computeMerkleNode_succ] at hW
            simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub, Option.some.injEq] at hW
            exact hW
          match thCall_eq_psum suite hCallEq with
          | .inl ⟨_, _, _, hArgs⟩ =>
            have hSubEq : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx + 1)
                (localIdx - 2 ^ h) leaf rest =
                some (computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx + 1)) := by
              simp only [List.cons.injEq, and_true] at hArgs
              rw [← hArgs.2]; exact hSub
            match walkMerkle_meets_honest_psum suite pkSeed layer tree kind leafFn C mkCol
                    h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf rest hSubLt hSubEq with
            | .inl hLeaf => .inl (by rw [hIdxEq]; exact hLeaf)
            | .inr c => .inr c
          | .inr ⟨hNe, hHash⟩ => .inr (mkCol h nodeIdx _ hNe hHash)

private def wotsChain_meets_honest_psum (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (Nat × List UInt8 × PqHashSig))
    (layer : UInt32) (tree : UInt64) (kp r : Nat) :
    ∀ (k s : Nat) (x : List UInt8),
      wotsChainSteps suite sk.pkSeed layer tree kp r s k x =
        honestChainNode suite sk layer tree kp r (s + k) →
      PSum (x = honestChainNode suite sk layer tree kp r s)
           (CheckedStatefulCollisionWitness suite params sk log)
  | 0, s, x, h => .inl (by rw [wotsChainSteps_zero, Nat.add_zero] at h; exact h)
  | k + 1, s, x, h =>
    have hNext : wotsChainSteps suite sk.pkSeed layer tree kp r (s + 1) k
        (thChainF suite sk.pkSeed ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ x) =
        honestChainNode suite sk layer tree kp r ((s + 1) + k) := by
      rw [wotsChainSteps_succ] at h
      dsimp only at h
      rw [show s + (k + 1) = (s + 1) + k by omega] at h
      exact h
    match wotsChain_meets_honest_psum suite params sk log layer tree kp r k (s + 1) _ hNext with
    | .inr col => .inr col
    | .inl hF =>
      have hCallEq :
          thCall suite tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x] =
          thCall suite tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
            [honestChainNode suite sk layer tree kp r s] := by
        rw [← thChainF_eq, ← thChainF_eq, honestChainNode_succ]
        exact hF
      match thCall_eq_psum suite hCallEq with
      | .inl ⟨_, _, _, hArgs⟩ => .inl (List.cons.inj hArgs).1
      | .inr ⟨hNe, hHash⟩ =>
        .inr { honestInput := _, forgedInput := _
               targetKind := .chainStep layer tree kp r s
               distinct := hNe, collides := hHash }

private def allChains_meet_honest_psum (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (Nat × List UInt8 × PqHashSig))
    (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digF : List Nat) (chains : List (List UInt8))
    (hEnds : recoverWotsEndpoints suite params sk.pkSeed layer tree kp digF chains =
      (List.range params.ell1).map fun r => honestChainNode suite sk layer tree kp r (params.w - 1))
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true) :
    ∀ (m : Nat), m ≤ params.ell1 →
      PSum (∀ r, r < m → chains.getD r [] = honestChainNode suite sk layer tree kp r (digF.getD r 0))
           (CheckedStatefulCollisionWitness suite params sk log)
  | 0, _ => .inl (fun _ hLt => by omega)
  | m + 1, hmLe =>
    match allChains_meet_honest_psum suite params sk log layer tree kp digF chains hEnds hTsw m (by omega) with
    | .inr col => .inr col
    | .inl hPrev =>
      have hmLt : m < params.ell1 := by omega
      have hStepEq :
          wotsChainSteps suite sk.pkSeed layer tree kp m (digF.getD m 0)
            (params.w - 1 - digF.getD m 0) (chains.getD m []) =
          honestChainNode suite sk layer tree kp m (digF.getD m 0 + (params.w - 1 - digF.getD m 0)) := by
        obtain ⟨hLenF, hBoundF, _⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
        have hmLen : m < digF.length := by rw [hLenF]; exact hmLt
        have hdLt : digF.getD m 0 < params.w := by
          rw [list_getD_eq_getElem digF 0 hmLen]
          exact hBoundF _ (List.getElem_mem hmLen)
        have hSum : digF.getD m 0 + (params.w - 1 - digF.getD m 0) = params.w - 1 := by omega
        have hAt := congrArg (fun l => l.getD m []) hEnds
        rw [recoverWotsEndpoints_eq, list_getD_map_range params.ell1 _ [] hmLt,
            list_getD_map_range params.ell1 _ [] hmLt] at hAt
        rw [hSum]
        exact hAt
      match wotsChain_meets_honest_psum suite params sk log layer tree kp m
              (params.w - 1 - digF.getD m 0) (digF.getD m 0) (chains.getD m []) hStepEq with
      | .inr col => .inr col
      | .inl hM =>
        .inl (fun r hr => by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hlt | rfl
          · exact hPrev r hlt
          · exact hM)

/-- Shared constructive layer extractor: from a valid XMSS Merkle walk at layer `i` reaching the
    honest subtree root, either extracts a `CheckedStatefulCollisionWitness` or proves that every
    chain `r < params.ell1` in `ls.wotsChains` equals `honestChainNode ... (digF.getD r 0)`. -/
private def statefulLayerChains_extract (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (Nat × List UInt8 × PqHashSig))
    (i G KP : Nat) (T : UInt64) (ls : LayerXmssSig) (digF : List Nat)
    (hKP : KP = G % 2 ^ params.subtreeHeight)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hWalk : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) T .tree params.subtreeHeight 0 KP
      (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) T KP digF ls.wotsChains)
      ls.authPath =
      some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat i) T)) :
    PSum (∀ r, r < params.ell1 →
            ls.wotsChains.getD r [] = honestChainNode suite sk (UInt32.ofNat i) T KP r (digF.getD r 0))
         (CheckedStatefulCollisionWitness suite params sk log) :=
  have hKpLt : KP < 2 ^ params.subtreeHeight := by
    rw [hKP]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hWalkNode : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) T .tree params.subtreeHeight 0 KP
      (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) T KP digF ls.wotsChains)
      ls.authPath =
      some (computeMerkleNode suite sk.pkSeed (UInt32.ofNat i) T .tree
        (computeWotsPk suite params sk (UInt32.ofNat i) T) params.subtreeHeight 0) := by
    rw [← computeXmssSubtreeRoot_eq]; exact hWalk
  match walkMerkle_meets_honest_psum suite sk.pkSeed (UInt32.ofNat i) T .tree
          (computeWotsPk suite params sk (UInt32.ofNat i) T)
          (CheckedStatefulCollisionWitness suite params sk log)
          (fun h n forged hNe hHash =>
            { honestInput := _, forgedInput := forged
              targetKind := .xmssNode (UInt32.ofNat i) T h n
              distinct := hNe, collides := hHash })
          params.subtreeHeight 0 KP _ _ hKpLt hWalkNode with
  | .inr col => .inr col
  | .inl hPk =>
    have hTlEq :
        thCall suite tagThTl sk.pkSeed ⟨UInt32.ofNat i, T, .wotsPk, UInt32.ofNat KP, 0, 0⟩
          (recoverWotsEndpoints suite params sk.pkSeed (UInt32.ofNat i) T KP digF ls.wotsChains) =
        thCall suite tagThTl sk.pkSeed ⟨UInt32.ofNat i, T, .wotsPk, UInt32.ofNat KP, 0, 0⟩
          ((List.range params.ell1).map fun r =>
            honestChainNode suite sk (UInt32.ofNat i) T KP r (params.w - 1)) := by
      rw [Nat.zero_mul, Nat.zero_add, recoverWotsPkFromSig_eq, computeWotsPk_eq,
          thTweakTl_eq, thTweakTl_eq] at hPk
      exact hPk
    match thCall_eq_psum suite hTlEq with
    | .inr ⟨hNe, hHash⟩ =>
      .inr { honestInput := _, forgedInput := _
             targetKind := .wotsPk (UInt32.ofNat i) T KP
             distinct := hNe, collides := hHash }
    | .inl ⟨_, _, _, hEnds⟩ =>
      allChains_meet_honest_psum suite params sk log (UInt32.ofNat i) T KP digF ls.wotsChains
        hEnds hTsw params.ell1 (Nat.le_refl _)

/-- Constructive single-layer divergence extractor for checked stateful `Jorts` at any layer
    `i < params.numLayers` (`i = 0` or `i > 0`) once we know `cur ≠ honestStatefulLayerRoot ... e_or_honest`. -/
private def statefulLayerDivergence_extract (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List CheckedStatefulQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hValid : params.checkedStatefulValid = true)
    (hStarLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    (i : Nat) (hi : i < params.numLayers)
    (cur : List UInt8)
    (hLayer0Cur : i = 0 → cur = thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msgStar)
    (hUpperDiff : 0 < i →
      cur ≠ computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1))
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight))))
    (hFreshMsg : msgStar ∉ ((execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog.map fun e => e.2.1))
    (ls : LayerXmssSig) (hLs : ls = sigStar.layerSigs.getD i ⟨0, [], []⟩)
    (digF : List Nat)
    (hDigF : digF = extractBaseWDigits params.w params.ell1
      (thHashMsg suite (if i = 0 then sigStar.rRand else []) sk.pkSeed
        (derivePublicKey suite params sk).pkRoot cur (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
        ls.tswCtr))
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hWalk : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i)
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
      .tree params.subtreeHeight 0
      (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
      (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
        digF ls.wotsChains)
      ls.authPath =
      some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight)))) :
    let log := (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog
    PSum (CheckedStatefulCollisionWitness suite params sk log)
         (CheckedStatefulWotsTswWitness suite params sk log msgStar sigStar) :=
  let log := (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog
  let G := sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)
  let T := UInt64.ofNat (G / 2 ^ params.subtreeHeight)
  let KP := G % 2 ^ params.subtreeHeight
  have hFacts := params.checkedStatefulValid_facts hValid
  have hWf : params.wellFormed = true := hFacts.1
  have hLayers : params.numLayers ≤ 2 ^ 32 := hFacts.2.2.2.2.2.2.2
  have hStrict : params.targetSum < (params.w - 1) * params.ell1 := by
    rw [PqHashParams.targetSum_eq]
    rcases hGeom with ⟨hw, hell⟩ | ⟨hw, hell⟩ <;> rw [hw, hell] <;> decide
  have hInj : ∀ {a b : List UInt8}, a.length = 64 → b.length = 64 →
      extractBaseWDigits params.w params.ell1 a = extractBaseWDigits params.w params.ell1 b →
      a.take 32 = b.take 32 := by
    intro a b ha hb hd
    rcases hGeom with ⟨hw, hell⟩ | ⟨hw, hell⟩
    · rw [hw, hell] at hd; exact extractBaseWDigits_4_128_take32_eq ha hb hd
    · rw [hw, hell] at hd; exact extractBaseWDigits_base16_prefix_injective 32 (by omega) (by omega) hd
  match statefulLayerChains_extract suite params sk log i G KP T ls digF rfl hTsw hWalk with
  | .inr col => .inl col
  | .inl hChainsEq =>
    have hInv : ∀ r, r < params.ell1 →
        thChainF suite sk.pkSeed
          ⟨UInt32.ofNat i, T, .wotsHash, UInt32.ofNat KP, UInt32.ofNat r, UInt32.ofNat (digF.getD r 0)⟩
          ((sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r []) =
        honestChainNode suite sk (UInt32.ofNat i) T KP r (digF.getD r 0 + 1) := by
      intro r hr
      rw [← hLs, hChainsEq r hr]
      exact honestChainNode_succ suite sk (UInt32.ofNat i) T KP r (digF.getD r 0)
    have hSearch := listSearchPSum
      (fun e : Nat × List UInt8 × PqHashSig =>
        ∃ i', i' < params.numLayers ∧
          wotsPosAddr params e.2.2.leafGlobalIdx i' = wotsPosAddr params sigStar.leafGlobalIdx i)
      (fun e =>
        match boundedSearchPSum
          (fun i' => wotsPosAddr params e.2.2.leafGlobalIdx i' = wotsPosAddr params sigStar.leafGlobalIdx i)
          (fun i' =>
            if hEqA : wotsPosAddr params e.2.2.leafGlobalIdx i' = wotsPosAddr params sigStar.leafGlobalIdx i then
              .inl hEqA else .inr hEqA)
          params.numLayers with
        | .inl ⟨i', ⟨h1, h2⟩⟩ => .inl ⟨i', h1, h2⟩
        | .inr hNone => .inr (fun ⟨i', h1, h2⟩ => hNone i' h1 h2))
      log
    match hSearch with
    | .inl ⟨e, ⟨he, hEx⟩⟩ =>
      match boundedSearchPSum
          (fun i' => wotsPosAddr params e.2.2.leafGlobalIdx i' = wotsPosAddr params sigStar.leafGlobalIdx i)
          (fun i' =>
            if hEqA : wotsPosAddr params e.2.2.leafGlobalIdx i' = wotsPosAddr params sigStar.leafGlobalIdx i then
              .inl hEqA else .inr hEqA)
          params.numLayers with
      | .inr hNone =>
        False.elim (let ⟨i', hi', hAddr⟩ := hEx; hNone i' hi' hAddr)
      | .inl ⟨i', ⟨hi', hAddr⟩⟩ =>
        have hOk := checkedStatefulOracle_entryOk suite params sk queries he
        have hInjRes := wotsPosAddr_inj params hWf hLayers hOk.leaf_lt hStarLt hi' hi hAddr
        have hPos : e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = G := by
          rw [← hInjRes.1]; exact hInjRes.2
        if hRootMatch : cur = honestStatefulLayerRoot suite params sk e.2.1 i G then
          if hI0 : i = 0 then
            have hPreEq :
                thCall suite tagHPre sk.pkSeed zeroAdrs [(derivePublicKey suite params sk).pkRoot, msgStar] =
                thCall suite tagHPre sk.pkSeed zeroAdrs [(derivePublicKey suite params sk).pkRoot, e.2.1] := by
              have hCur0 := hLayer0Cur hI0
              simp only [honestStatefulLayerRoot, hI0, ↓reduceIte] at hRootMatch
              rw [← thPreHash_eq, ← thPreHash_eq, ← hCur0]
              exact hRootMatch
            match thCall_eq_psum suite hPreEq with
            | .inl ⟨_, _, _, hArgs⟩ =>
              False.elim (by
                simp only [List.cons.injEq, and_true] at hArgs
                exact hFreshMsg (List.mem_map.mpr ⟨e, he, hArgs.2.symm⟩))
            | .inr ⟨hNe, hHash⟩ =>
              .inl { honestInput := _, forgedInput := _
                     targetKind := .messagePreHash e he
                     distinct := hNe, collides := hHash }
          else
            False.elim (by
              have hUp := hUpperDiff (Nat.pos_of_ne_zero hI0)
              simp only [honestStatefulLayerRoot, hI0, ↓reduceIte] at hRootMatch
              exact hUp hRootMatch)
        else
          have hValidH := statefulLogLayerDigits_valid hOk i hi
          if hDigEq : digF = statefulLogLayerDigits suite params sk e i then
            have hTake :
                (thHashMsg suite (if i = 0 then sigStar.rRand else []) sk.pkSeed
                  (derivePublicKey suite params sk).pkRoot cur (UInt32.ofNat i) T
                  (UInt32.ofNat KP) ls.tswCtr).take 32 =
                (thHashMsg suite (honestStatefulLayerRand e i) sk.pkSeed
                  (derivePublicKey suite params sk).pkRoot
                  (honestStatefulLayerRoot suite params sk e.2.1 i (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)))
                  (UInt32.ofNat i)
                  (UInt64.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
                  (UInt32.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
                  (e.2.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr).take 32 := by
              rw [hDigF, statefulLogLayerDigits_eq] at hDigEq
              exact hInj (thHashMsg_length _ _ _ _ _ _ _ _ _) (thHashMsg_length _ _ _ _ _ _ _ _ _) hDigEq
            have hCallEq :
                thCall suite tagHMsg sk.pkSeed
                  ⟨UInt32.ofNat i, T, .wotsHash, UInt32.ofNat KP, 0, UInt32.ofNat ls.tswCtr⟩
                  [if i = 0 then sigStar.rRand else [], (derivePublicKey suite params sk).pkRoot, cur, be 4 ls.tswCtr] =
                thCall suite tagHMsg sk.pkSeed
                  ⟨UInt32.ofNat i,
                   UInt64.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight),
                   .wotsHash,
                   UInt32.ofNat (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight),
                   0,
                   UInt32.ofNat (e.2.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr⟩
                  [honestStatefulLayerRand e i,
                   (derivePublicKey suite params sk).pkRoot,
                   honestStatefulLayerRoot suite params sk e.2.1 i (e.2.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)),
                   be 4 (e.2.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr] := by
              rw [thHashMsg_eq, thHashMsg_eq, List.take_left' (thCall_length _ _ _ _ _),
                  List.take_left' (thCall_length _ _ _ _ _)] at hTake
              exact hTake
            match thCall_eq_psum suite hCallEq with
            | .inl ⟨_, _, _, hArgs⟩ =>
              False.elim (by
                simp only [List.cons.injEq] at hArgs
                rw [hPos] at hArgs
                exact hRootMatch hArgs.2.2.1)
            | .inr ⟨hNe, hHash⟩ =>
              .inl { honestInput := _, forgedInput := _
                     targetKind := .layerDigest e he i hi
                     distinct := hNe, collides := hHash }
          else
            have hIncomp := (tsw_incomparable_no_chain_forgery hValidH hTsw (fun hEq => hDigEq hEq.symm)).2
            have hComplete := findBackwardCoord_complete
              (let ⟨r', hr2, hr1, hlt, _⟩ := hIncomp; ⟨r', hr2, hr1, hlt⟩)
            match hFind : findBackwardCoord (statefulLogLayerDigits suite params sk e i) digF with
            | none =>
              False.elim (by obtain ⟨_, _, _, hSome, _⟩ := hComplete; rw [hFind] at hSome; cases hSome)
            | some r =>
              have hBounds : r < params.ell1 ∧
                  digF.getD r 0 < (statefulLogLayerDigits suite params sk e i).getD r 0 ∧
                  (statefulLogLayerDigits suite params sk e i).getD r 0 < params.w := by
                obtain ⟨r0, hrF, hrH, hSome, hlt⟩ := hComplete
                rw [hFind] at hSome
                injection hSome with hEqR
                subst hEqR
                obtain ⟨hLenH, hBoundH, _⟩ := (checkTargetSum_iff _ _ _ _).mp hValidH
                have hFGet : digF.getD r 0 = digF[r]'hrF := list_getD_eq_getElem digF 0 hrF
                have hHGet : (statefulLogLayerDigits suite params sk e i).getD r 0 =
                    (statefulLogLayerDigits suite params sk e i)[r]'hrH := list_getD_eq_getElem _ 0 hrH
                exact ⟨hLenH ▸ hrH, by rw [hFGet, hHGet]; exact hlt,
                  by rw [hHGet]; exact hBoundH _ (List.getElem_mem hrH)⟩
              .inr { layerIdx := i
                     layer_lt := hi
                     chainIdx := r
                     chain_lt := hBounds.1
                     signedLayerDigest := cur
                     layer0_digest := hLayer0Cur
                     forgedDigit := digF.getD r 0
                     forgedDigit_eq := by rw [hDigF, hLs]
                     digit_lt := Nat.lt_of_lt_of_le hBounds.2.1 (Nat.le_sub_one_of_lt hBounds.2.2)
                     invertsHonest := hInv r hBounds.1
                     unrevealedInLog := fun e' he' i'' hi'' hAddr' => by
                       have hAddrE : wotsPosAddr params e.2.2.leafGlobalIdx i = wotsPosAddr params sigStar.leafGlobalIdx i := by
                         cases hInjRes.1; exact hAddr
                       obtain ⟨_, _, _, _, _, hDigConsistent, _⟩ :=
                         checkedStatefulLog_unique_layer_codeword suite params sk queries he' he hi'' hi
                           (hAddr'.trans hAddrE.symm)
                       rw [hDigConsistent]
                       exact hBounds.2.1 }
    | .inr hNoUse =>
      match hFind : findDigitLt (params.w - 1) digF with
      | none =>
        False.elim (by
          obtain ⟨hLenF, _, hSumF⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
          have hAllGe := findDigitLt_none_all_ge (params.w - 1) digF hFind
          have hGe := sumDigits_ge_mul_of_all_ge (params.w - 1) digF hAllGe
          rw [hLenF, hSumF] at hGe
          omega)
      | some r =>
        have hRLt : r < params.ell1 ∧ digF.getD r 0 < params.w - 1 := by
          obtain ⟨hLenF, _, _⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
          obtain ⟨hrLen, hrVal⟩ := findDigitLt_sound (params.w - 1) hFind
          rw [list_getD_eq_getElem digF 0 hrLen]
          exact ⟨hLenF ▸ hrLen, hrVal⟩
        .inr { layerIdx := i
               layer_lt := hi
               chainIdx := r
               chain_lt := hRLt.1
               signedLayerDigest := cur
               layer0_digest := hLayer0Cur
               forgedDigit := digF.getD r 0
               forgedDigit_eq := by rw [hDigF, hLs]
               digit_lt := hRLt.2
               invertsHonest := hInv r hRLt.1
               unrevealedInLog := fun e' he' i'' hi'' hAddr' =>
                 absurd ⟨i'', hi'', hAddr'⟩ (hNoUse e' he') }

/-- Constructive upward walk over upper hypertree layers (`i ≥ 1`) in checked stateful `Jorts`. -/
private def statefulUpperWalk_extract (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List CheckedStatefulQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hValid : params.checkedStatefulValid = true)
    (hFreshMsg : msgStar ∉ ((execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog.map fun e => e.2.1))
    (hStarLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) :
    ∀ (sigs : List LayerXmssSig) (i : Nat) (cur : List UInt8),
      0 < i →
      (∀ j, sigs.getD j ⟨0, [], []⟩ = sigStar.layerSigs.getD (i + j) ⟨0, [], []⟩) →
      i + sigs.length = params.numLayers →
      verifyHypertreeLayers suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot [] i
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) cur sigs =
        some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight)))) →
      let log := (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog
      PSum (cur = computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1))
              (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight))))
           (PSum (CheckedStatefulCollisionWitness suite params sk log)
                 (CheckedStatefulWotsTswWitness suite params sk log msgStar sigStar))
  | [], i, cur, _, _, hLenEq, hVer => by
    rw [verifyHypertreeLayers_nil] at hVer
    simp only [Option.some.injEq] at hVer
    have hIEq : i = params.numLayers := by rw [← hLenEq, List.length_nil, Nat.add_zero]
    subst hIEq
    exact .inl hVer
  | lsig :: rest, i, cur, hIPos, hAlign, hLenEq, hVer =>
    have hi : i < params.numLayers := by rw [← hLenEq, List.length_cons]; omega
    have hStep : sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight =
        sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight) := by
      have h := div_pow_mul_pow_mul sigStar.leafGlobalIdx i 1 params.subtreeHeight
      rw [Nat.one_mul] at h; exact h
    let G := sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)
    let T := UInt64.ofNat (G / 2 ^ params.subtreeHeight)
    let KP := G % 2 ^ params.subtreeHeight
    let digF := extractBaseWDigits params.w params.ell1
      (thHashMsg suite [] sk.pkSeed (derivePublicKey suite params sk).pkRoot cur
        (UInt32.ofNat i) T (UInt32.ofNat KP) lsig.tswCtr)
    if hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true then
      if hChLen : lsig.wotsChains.length = params.ell1 then
        match hWalkOpt : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) T .tree
                params.subtreeHeight 0 KP
                (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) T KP digF lsig.wotsChains)
                lsig.authPath with
        | none =>
          False.elim (by
            rw [verifyHypertreeLayers_cons] at hVer
            simp only [digF, G, T, KP, hTsw, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                       hChLen, ne_eq, not_true_eq_false] at hVer
            rw [hWalkOpt] at hVer; cases hVer)
        | some next =>
          have hRestVer :
              verifyHypertreeLayers suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot []
                (i + 1) (sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight)) next rest =
              some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
                (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight)))) := by
            rw [verifyHypertreeLayers_cons] at hVer
            simp only [digF, G, T, KP, hTsw, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                       hChLen, ne_eq, not_true_eq_false] at hVer
            rw [hWalkOpt] at hVer
            dsimp only at hVer
            rw [← hStep]
            exact hVer
          match statefulUpperWalk_extract suite params sk queries msgStar sigStar
                  hGeom hValid hFreshMsg hStarLt rest (i + 1) next (by omega)
                  (fun j => by
                    have h := hAlign (j + 1)
                    rw [List.getD_cons_succ, show i + (j + 1) = i + 1 + j by omega] at h
                    exact h)
                  (by rw [List.length_cons] at hLenEq; omega)
                  hRestVer with
          | .inr brk => .inr brk
          | .inl hNextEq =>
            if hCurEq : cur = computeXmssSubtreeRoot suite params sk (UInt32.ofNat (i - 1)) (UInt64.ofNat G) then
              .inl hCurEq
            else
              have hWalkHonest : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) T .tree
                  params.subtreeHeight 0 KP
                  (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) T KP digF lsig.wotsChains)
                  lsig.authPath =
                  some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat i) T) := by
                simp only [Nat.add_sub_cancel, ← hStep] at hNextEq
                rw [← hNextEq]
                exact hWalkOpt
              have hLs0 : lsig = sigStar.layerSigs.getD i ⟨0, [], []⟩ := by
                have h := hAlign 0
                simpa only [List.getD_cons_zero, Nat.add_zero] using h
              have hINe0 : i ≠ 0 := Nat.ne_of_gt hIPos
              .inr (statefulLayerDivergence_extract suite params sk queries msgStar sigStar
                hGeom hValid hStarLt i hi cur
                (fun h0 => absurd h0 hINe0)
                (fun _ => hCurEq)
                hFreshMsg lsig hLs0 digF
                (by simp [digF, G, T, KP, hINe0])
                hTsw hWalkHonest)
      else
        False.elim (by
          rw [verifyHypertreeLayers_cons] at hVer
          simp [digF, G, T, KP, hTsw, hChLen] at hVer)
    else
      False.elim (by
        rw [verifyHypertreeLayers_cons] at hVer
        have hF : checkTargetSum params.w params.ell1 params.targetSum digF = false :=
          Bool.eq_false_iff.mpr hTsw
        simp [digF, G, T, KP, hF] at hVer)

/-- Raw-verifier version of `checked_stateful_hypertree_euf_cma_extract` (`verifyPqHashSig = true`
    under `params.checkedStatefulValid = true`). -/
def checked_stateful_hypertree_euf_cma_extract_raw
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatefulQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hValidParams : params.checkedStatefulValid = true)
    (hFreshMsg : msgStar ∉ ((execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog.map fun e => e.2.1))
    (hAccept : verifyPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    let log := (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog
    PSum (CheckedStatefulCollisionWitness suite params sk log)
         (CheckedStatefulWotsTswWitness suite params sk log msgStar sigStar) :=
  have hFacts := params.checkedStatefulValid_facts hValidParams
  have hWf : params.wellFormed = true := hFacts.1
  have hSt : params.statefulJorts = true := hFacts.2.1
  have hDPos : 0 < params.numLayers := hFacts.2.2.2.2.2.1
  have hUnpack : sigStar.layerSigs.length = params.numLayers ∧
      sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) ∧
      verifyHypertreeLayers suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot
        sigStar.rRand 0 sigStar.leafGlobalIdx
        (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msgStar)
        sigStar.layerSigs =
      some (derivePublicKey suite params sk).pkRoot := by
    unfold verifyPqHashSig at hAccept
    cases hLen : decide (sigStar.layerSigs.length = params.numLayers)
    · have hNe : sigStar.layerSigs.length ≠ params.numLayers := of_decide_eq_false hLen
      simp [hWf, hNe] at hAccept
    · have hEqL := of_decide_eq_true hLen
      cases hIdx : decide (sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
      · have hNot : ¬ (sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) := of_decide_eq_false hIdx
        simp [hWf, hEqL, hNot] at hAccept
      · have hLt := of_decide_eq_true hIdx
        have hSeed : (derivePublicKey suite params sk).pkSeed = sk.pkSeed := rfl
        simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hEqL, ne_eq, not_true_eq_false,
                   hLt, decide_true, hSt, hSeed] at hAccept
        cases hPre : (!sigStar.forsOpenings.isEmpty || decide (sigStar.msgTswCtr ≠ 0))
        · simp only [hPre, Bool.false_eq_true, ↓reduceIte] at hAccept
          cases hV : verifyHypertreeLayers suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot
              sigStar.rRand 0 sigStar.leafGlobalIdx
              (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msgStar)
              sigStar.layerSigs with
          | none => rw [hV] at hAccept; cases hAccept
          | some top =>
            rw [hV] at hAccept
            simp only [decide_eq_true_eq] at hAccept
            exact ⟨hEqL, hLt, congrArg some hAccept⟩
        · rcases Bool.or_eq_true_iff.mp hPre with hF | hD
          · simp [hF] at hAccept
          · simp [of_decide_eq_true hD] at hAccept
  match hSigs : sigStar.layerSigs with
  | [] => False.elim (by have hL := hUnpack.1; rw [hSigs, List.length_nil] at hL; omega)
  | ls0 :: rest =>
    let muStar := thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msgStar
    let tree0 := UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight)
    let kp0 := sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight
    let digF0 := extractBaseWDigits params.w params.ell1
      (thHashMsg suite sigStar.rRand sk.pkSeed (derivePublicKey suite params sk).pkRoot
        muStar 0 tree0 (UInt32.ofNat kp0) ls0.tswCtr)
    have hVer0 : verifyHypertreeLayers suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot
        sigStar.rRand 0 sigStar.leafGlobalIdx muStar (ls0 :: rest) =
        some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight)))) := by
      have hDivTop : sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight) = 0 :=
        Nat.div_eq_of_lt hUnpack.2.1
      rw [hDivTop]
      change verifyHypertreeLayers suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot
          sigStar.rRand 0 sigStar.leafGlobalIdx muStar (ls0 :: rest) =
          some (derivePublicKey suite params sk).pkRoot
      rw [← hSigs]
      exact hUnpack.2.2
    if hTsw0 : checkTargetSum params.w params.ell1 params.targetSum digF0 = true then
      if hChLen0 : ls0.wotsChains.length = params.ell1 then
        match hWalk0 : walkMerkleAuthPath suite sk.pkSeed 0 tree0 .tree params.subtreeHeight 0 kp0
                (recoverWotsPkFromSig suite params sk.pkSeed 0 tree0 kp0 digF0 ls0.wotsChains)
                ls0.authPath with
        | none =>
          False.elim (by
            rw [verifyHypertreeLayers_cons] at hVer0
            have hU0 : UInt32.ofNat 0 = (0 : UInt32) := rfl
            simp only [hU0, digF0, tree0, kp0, hTsw0, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                       hChLen0, ne_eq, not_true_eq_false] at hVer0
            rw [hWalk0] at hVer0; cases hVer0)
        | some next0 =>
          have hRestVer0 :
              verifyHypertreeLayers suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot []
                1 (sigStar.leafGlobalIdx / 2 ^ (1 * params.subtreeHeight)) next0 rest =
              some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
                (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight)))) := by
            rw [verifyHypertreeLayers_cons] at hVer0
            have hU0 : UInt32.ofNat 0 = (0 : UInt32) := rfl
            simp only [hU0, digF0, tree0, kp0, hTsw0, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                       hChLen0, ne_eq, not_true_eq_false, Nat.zero_add] at hVer0
            rw [hWalk0] at hVer0
            dsimp only at hVer0
            rw [Nat.one_mul]
            exact hVer0
          match statefulUpperWalk_extract suite params sk queries msgStar sigStar
                  hGeom hValidParams hFreshMsg hUnpack.2.1 rest 1 next0 (by decide)
                  (fun j => by
                    have h : (ls0 :: rest).getD (j + 1) ⟨0, [], []⟩ =
                        sigStar.layerSigs.getD (1 + j) ⟨0, [], []⟩ := by
                      rw [hSigs, show 1 + j = j + 1 by omega]
                    simpa only [List.getD_cons_succ] using h)
                  (by have hL := hUnpack.1; rw [hSigs, List.length_cons] at hL; omega)
                  hRestVer0 with
          | .inr brk => brk
          | .inl hNextEq0 =>
            have hWalkHonest0 : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat 0)
                (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) / 2 ^ params.subtreeHeight))
                .tree params.subtreeHeight 0
                (sigStar.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) % 2 ^ params.subtreeHeight)
                (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat 0)
                  (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) / 2 ^ params.subtreeHeight))
                  (sigStar.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) % 2 ^ params.subtreeHeight)
                  digF0 ls0.wotsChains)
                ls0.authPath =
                some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 0)
                  (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) / 2 ^ params.subtreeHeight))) := by
              have hU0 : UInt32.ofNat 0 = (0 : UInt32) := rfl
              simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one, hU0]
              simp only [Nat.sub_self, Nat.one_mul, hU0] at hNextEq0
              rw [← hNextEq0]
              exact hWalk0
            statefulLayerDivergence_extract suite params sk queries msgStar sigStar
              hGeom hValidParams hUnpack.2.1 0 hDPos muStar
              (fun _ => rfl)
              (fun hPos0 => absurd hPos0 (Nat.not_lt_zero 0))
              hFreshMsg ls0
              (by rw [hSigs, List.getD_cons_zero])
              digF0
              (by
                have hU0 : UInt32.ofNat 0 = (0 : UInt32) := rfl
                simp [digF0, tree0, kp0, Nat.zero_mul, Nat.pow_zero, Nat.div_one, hU0])
              hTsw0 hWalkHonest0
      else
        False.elim (by
          rw [verifyHypertreeLayers_cons] at hVer0
          have hU0 : UInt32.ofNat 0 = (0 : UInt32) := rfl
          simp [hU0, digF0, tree0, kp0, hTsw0, hChLen0] at hVer0)
    else
      False.elim (by
        rw [verifyHypertreeLayers_cons] at hVer0
        have hU0 : UInt32.ofNat 0 = (0 : UInt32) := rfl
        have hF : checkTargetSum params.w params.ell1 params.targetSum digF0 = false :=
          Bool.eq_false_iff.mpr hTsw0
        simp [hU0, digF0, tree0, kp0, hF] at hVer0)

/-- **End-to-End Checked/Stateful Hypertree EUF-CMA Constructive Witness Extractor
    (`checked_stateful_hypertree_euf_cma_extract`, `0 Classical.choice`)**:
    Across ANY multi-turn sequence `queries : List CheckedStatefulQuery` (including retries,
    out-of-order epochs, equivocation attempts, and budget-exhausting aborts), if an adversary
    outputs a signature `sigStar` passing `verifyCheckedStateful` on a message `msgStar` absent
    from the emitted transcript `log`, this `Type`-valued algorithm constructively extracts
    EITHER a transcript-indexed SM-TCR hash collision (`CheckedStatefulCollisionWitness`) OR a
    transcript-indexed WOTS+C/TSW backward chain inversion (`CheckedStatefulWotsTswWitness`)! -/
def checked_stateful_hypertree_euf_cma_extract
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatefulQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hFreshMsg : msgStar ∉ ((execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog.map fun e => e.2.1))
    (hAccept : verifyCheckedStateful suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    let log := (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog
    PSum (CheckedStatefulCollisionWitness suite params sk log)
         (CheckedStatefulWotsTswWitness suite params sk log msgStar sigStar) :=
  let hSound := verifyCheckedStateful_sound suite params (derivePublicKey suite params sk) msgStar sigStar hAccept
  checked_stateful_hypertree_euf_cma_extract_raw suite params sk queries msgStar sigStar
    hGeom hSound.1 hFreshMsg hSound.2.2

/-- Strict-execution corollary of `checked_stateful_hypertree_euf_cma_extract`:
    applies directly when `execCheckedStatefulStrict suite params sk initCheckedStatefulLatch queries = .ok (stFinal, log)`. -/
def checked_stateful_strict_euf_cma_extract
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatefulQuery)
    (stFinal : CheckedStatefulLatchState)
    (log : List (Nat × List UInt8 × PqHashSig))
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hStrict : execCheckedStatefulStrict suite params sk initCheckedStatefulLatch queries = .ok (stFinal, log))
    (hFreshMsg : msgStar ∉ (log.map fun e => e.2.1))
    (hAccept : verifyCheckedStateful suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    PSum (CheckedStatefulCollisionWitness suite params sk log)
         (CheckedStatefulWotsTswWitness suite params sk log msgStar sigStar) :=
  have hLogEq : log = (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch queries).emittedLog :=
    congrArg CheckedStatefulOracleRun.emittedLog
      (((execCheckedStatefulStrict_eq_oracle suite params sk queries initCheckedStatefulLatch).1 stFinal log).mp hStrict).symm
  hLogEq ▸ checked_stateful_hypertree_euf_cma_extract suite params sk queries msgStar sigStar
    hGeom (hLogEq ▸ hFreshMsg) hAccept

/-- Outcome of one coin in the multi-turn checked stateful EUF-CMA experiment. -/
structure CheckedStatefulEufCmaOutcome where
  sk      : PqSecretKey
  queries : List CheckedStatefulQuery
  msgStar : List UInt8
  sigStar : PqHashSig

/-- Winning predicate for the multi-turn checked stateful EUF-CMA experiment. -/
def checkedStatefulEufCmaWin (suite : TweakableHashSuite) (params : PqHashParams)
    (o : CheckedStatefulEufCmaOutcome) : Bool :=
  verifyCheckedStateful suite params (derivePublicKey suite params o.sk) o.msgStar o.sigStar &&
  decide (o.msgStar ∉ ((execCheckedStatefulOracle suite params o.sk initCheckedStatefulLatch o.queries).emittedLog.map fun e => e.2.1))

theorem checkedStatefulEufCmaWin_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (o : CheckedStatefulEufCmaOutcome) :
    checkedStatefulEufCmaWin suite params o =
      (verifyCheckedStateful suite params (derivePublicKey suite params o.sk) o.msgStar o.sigStar &&
       decide (o.msgStar ∉ ((execCheckedStatefulOracle suite params o.sk initCheckedStatefulLatch o.queries).emittedLog.map fun e => e.2.1))) := by
  rfl

/-- Regression: replaying any message signed in the multi-turn checked stateful transcript is rejected. -/
theorem checkedStatefulEufCmaWin_rejects_signed_message
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : CheckedStatefulEufCmaOutcome) (ep : Nat) (sig : PqHashSig)
    (hSigned : (ep, o.msgStar, sig) ∈ (execCheckedStatefulOracle suite params o.sk initCheckedStatefulLatch o.queries).emittedLog) :
    checkedStatefulEufCmaWin suite params o = false := by
  have hMem : o.msgStar ∈ ((execCheckedStatefulOracle suite params o.sk initCheckedStatefulLatch o.queries).emittedLog.map fun e => e.2.1) :=
    List.mem_map.mpr ⟨(ep, o.msgStar, sig), hSigned, rfl⟩
  rw [checkedStatefulEufCmaWin_eq, decide_eq_false (fun hn => hn hMem), Bool.and_false]

/-- **Checked Stateful EUF-CMA Concrete Advantage Union Bound
    (`checked_stateful_hypertree_euf_cma_advantage_bound`)**:
    Over any finite coin space `coins : List Ω`, `Adv_EUF-CMA ≤ Adv_SM-TCR + Adv_WOTS-PRE`
    with exact factor `1` on both terms (no FORS ITSR term in stateful `Jorts`). -/
theorem checked_stateful_hypertree_euf_cma_advantage_bound {Ω : Type}
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (coins : List Ω) (game : Ω → CheckedStatefulEufCmaOutcome)
    (isCol isWotsPre : Ω → Bool)
    (hCol : ∀ ω,
      Nonempty (CheckedStatefulCollisionWitness suite params (game ω).sk
        (execCheckedStatefulOracle suite params (game ω).sk initCheckedStatefulLatch (game ω).queries).emittedLog) →
      isCol ω = true)
    (hWotsPre : ∀ ω,
      Nonempty (CheckedStatefulWotsTswWitness suite params (game ω).sk
        (execCheckedStatefulOracle suite params (game ω).sk initCheckedStatefulLatch (game ω).queries).emittedLog
        (game ω).msgStar (game ω).sigStar) →
      isWotsPre ω = true) :
    hitCount (fun ω => checkedStatefulEufCmaWin suite params (game ω)) coins ≤
      hitCount isCol coins + hitCount isWotsPre coins := by
  have hBound3 := hitCount_union_bound
    (fun ω => checkedStatefulEufCmaWin suite params (game ω))
    isCol isWotsPre (fun _ => false)
    (fun ω hWin => by
      rw [checkedStatefulEufCmaWin_eq, Bool.and_eq_true, decide_eq_true_eq] at hWin
      obtain ⟨hVer, hFresh⟩ := hWin
      cases checked_stateful_hypertree_euf_cma_extract suite params (game ω).sk (game ω).queries
              (game ω).msgStar (game ω).sigStar hGeom hFresh hVer with
      | inl col => exact .inl (hCol ω ⟨col⟩)
      | inr wots => exact .inr (.inl (hWotsPre ω ⟨wots⟩)))
    coins
  have hZero : ∀ cs : List Ω, hitCount (fun _ : Ω => false) cs = 0 := fun cs => by
    induction cs with
    | nil => rfl
    | cons _ _ ih => simp [hitCount, ih]
  rw [hZero coins, Nat.add_zero] at hBound3
  exact hBound3

/-! ### Checked Stateless Signing Oracle (`evalStatelessCheckedSign` / `verifyStatelessChecked`) -/

/-- Query to the HXOF-leaf-bound checked stateless signing oracle (`evalStatelessCheckedSign`). -/
structure CheckedStatelessQuery where
  message    : List UInt8
  randomness : List UInt8
  grindLimit : Nat
  deriving DecidableEq, Repr

/-- Transcript emitted by `evalStatelessCheckedSign` across a multi-turn query list. -/
def checkedStatelessOracleLog (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) : List CheckedStatelessQuery → List (List UInt8 × PqHashSig)
  | [] => []
  | q :: qs =>
    match evalStatelessCheckedSign suite params sk q.message q.randomness q.grindLimit with
    | none => checkedStatelessOracleLog suite params sk qs
    | some sig => (q.message, sig) :: checkedStatelessOracleLog suite params sk qs

/-- Lower HXOF-derived `CheckedStatelessQuery` list to the exact `PqSigningQuery` list executed by `evalSingleSign`. -/
def toLegacyStatelessQueries (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) : List CheckedStatelessQuery → List PqSigningQuery
  | [] => []
  | q :: qs =>
    if !params.checkedDigitGeometry then
      toLegacyStatelessQueries suite params sk qs
    else
      let pk := derivePublicKey suite params sk
      let mu := thPreHash suite pk.pkSeed pk.pkRoot q.message
      let rRand := thPrfMsg suite sk.skPrf q.randomness mu
      match deriveStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
      | none => toLegacyStatelessQueries suite params sk qs
      | some (leaf, _) =>
        ⟨q.message, q.randomness, leaf, q.grindLimit⟩ :: toLegacyStatelessQueries suite params sk qs

theorem checkedStatelessOracleLog_eq_signingOracleLog
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) :
    ∀ (qs : List CheckedStatelessQuery),
      checkedStatelessOracleLog suite params sk qs =
        signingOracleLog suite params sk (toLegacyStatelessQueries suite params sk qs)
  | [] => rfl
  | q :: qs => by
    unfold checkedStatelessOracleLog toLegacyStatelessQueries
    rw [evalStatelessCheckedSign_eq]
    cases hG : params.checkedDigitGeometry
    · simp only [Bool.not_false, ↓reduceIte]
      exact checkedStatelessOracleLog_eq_signingOracleLog suite params sk qs
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hSeed : (derivePublicKey suite params sk).pkSeed = sk.pkSeed := rfl
      simp only [hSeed]
      cases hD : deriveStatelessInputs suite params
          (thPrfMsg suite sk.skPrf q.randomness
            (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot q.message))
          sk.pkSeed (derivePublicKey suite params sk).pkRoot
          (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot q.message) with
      | none =>
        dsimp only
        exact checkedStatelessOracleLog_eq_signingOracleLog suite params sk qs
      | some pr =>
        rcases pr with ⟨leaf, idxs⟩
        dsimp only [signingOracleLog]
        cases evalSingleSign suite params sk q.message q.randomness leaf q.grindLimit <;>
          simp [checkedStatelessOracleLog_eq_signingOracleLog suite params sk qs]

/-- Constructive `Type`-valued witness extraction for HXOF-leaf-bound `evalStatelessCheckedSign` /
    `verifyStatelessChecked` over finite query logs (`0 Classical.choice`). -/
def checked_stateless_hypertree_euf_cma_extract
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatelessQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (hFreshMsg : msgStar ∉ (checkedStatelessOracleLog suite params sk queries).map Prod.fst)
    (hAccept : verifyStatelessChecked suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    HypertreeForgeryBreak suite params sk msgStar sigStar
      ((signingOracleLog suite params sk (toLegacyStatelessQueries suite params sk queries)).flatMap fun e =>
        (List.range params.forsTrees).map fun j =>
          (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ params.subtreeHeight),
           e.2.leafGlobalIdx % 2 ^ params.subtreeHeight,
           sigForsLeafIdx suite params (derivePublicKey suite params sk) e.1 e.2 j)) :=
  let hSound := verifyStatelessChecked_sound suite params (derivePublicKey suite params sk) msgStar sigStar hAccept
  extractReachableHypertreeForgery_of_statelessLog suite params sk
    (toLegacyStatelessQueries suite params sk queries) msgStar sigStar
    hGeom hSound.2.1 hLayers
    (by rwa [← checkedStatelessOracleLog_eq_signingOracleLog])
    hSound.2.2.1

/-- Every entry of `checkedStatelessOracleLog` is the answer to one of the listed queries. -/
theorem checkedStatelessOracleLog_mem_query (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) :
    ∀ (qs : List CheckedStatelessQuery) (e : List UInt8 × PqHashSig),
      e ∈ checkedStatelessOracleLog suite params sk qs →
      ∃ q ∈ qs, q.message = e.1 ∧
        evalStatelessCheckedSign suite params sk q.message q.randomness q.grindLimit = some e.2
  | [], _, h => by
    unfold checkedStatelessOracleLog at h
    cases h
  | q :: qs, e, h => by
    unfold checkedStatelessOracleLog at h
    cases hE : evalStatelessCheckedSign suite params sk q.message q.randomness q.grindLimit with
    | none =>
      simp only [hE] at h
      obtain ⟨q', hq', hRest⟩ := checkedStatelessOracleLog_mem_query suite params sk qs e h
      exact ⟨q', .tail _ hq', hRest⟩
    | some sig =>
      simp only [hE] at h
      rcases List.mem_cons.mp h with hHead | hTl
      · subst hHead
        exact ⟨q, .head _, rfl, hE⟩
      · obtain ⟨q', hq', hRest⟩ := checkedStatelessOracleLog_mem_query suite params sk qs e hTl
        exact ⟨q', .tail _ hq', hRest⟩

/-- `checked_stateless_hypertree_euf_cma_extract` with freshness stated on the query list itself: a
    message that was never submitted to the signing oracle cannot appear in the oracle log, so no
    log-level freshness premise and no upper-layer oracle premise remain for the caller. -/
def checked_stateless_hypertree_euf_cma_extract_of_fresh_queries
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatelessQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (hFreshQueries : ∀ q ∈ queries, q.message ≠ msgStar)
    (hAccept : verifyStatelessChecked suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    HypertreeForgeryBreak suite params sk msgStar sigStar
      ((signingOracleLog suite params sk (toLegacyStatelessQueries suite params sk queries)).flatMap fun e =>
        (List.range params.forsTrees).map fun j =>
          (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ params.subtreeHeight),
           e.2.leafGlobalIdx % 2 ^ params.subtreeHeight,
           sigForsLeafIdx suite params (derivePublicKey suite params sk) e.1 e.2 j)) :=
  checked_stateless_hypertree_euf_cma_extract suite params sk queries msgStar sigStar hGeom hLayers
    (fun hMem => by
      obtain ⟨e, he, hFst⟩ := List.mem_map.mp hMem
      obtain ⟨q, hq, hMsg, _⟩ := checkedStatelessOracleLog_mem_query suite params sk queries e he
      exact hFreshQueries q hq (hMsg.trans hFst))
    hAccept

/-- Transcript-indexed `Prop` EUF-CMA break theorem for `evalStatelessCheckedSign` / `verifyStatelessChecked`. -/
theorem checked_stateless_hypertree_euf_cma_break
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (queries : List CheckedStatelessQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (hFresh : ∀ e ∈ checkedStatelessOracleLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyStatelessChecked suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    let log := checkedStatelessOracleLog suite params sk queries
    ForsItsrBreak suite params (derivePublicKey suite params sk) log msgStar sigStar ∨
    SmTcrBreak suite params sk log ∨
    PreimageBreak suite params sk log msgStar sigStar := by
  obtain ⟨_, hStateless, hVerRaw, _⟩ :=
    verifyStatelessChecked_sound suite params (derivePublicKey suite params sk) msgStar sigStar hAccept
  have hLogEq := checkedStatelessOracleLog_eq_signingOracleLog suite params sk queries
  dsimp only
  rw [hLogEq]
  exact hypertree_forgery_break_of_signingLog suite params sk
    (toLegacyStatelessQueries suite params sk queries) msgStar sigStar
    hGeom hStateless hLayers
    (fun e he => hFresh e (hLogEq ▸ he))
    hVerRaw

/-! ### `#tooth` Mutation Witness (`mutantUncheckedReuseSign`) & Multi-Signature Inhabitedness Witness -/

/-- **`#tooth` Mutant Stateful Signer (`mutantUncheckedReuseSign`)**:
    Mutates `checkedStatefulSignStep` by omitting monotonic `nextEpoch` advancement and wrapping
    `reqEpoch` modulo the leaf budget `2 ^ params.maxSigsLog2` rather than aborting with
    `CheckedStatefulError.budgetExhausted` / `.staleOrOutOfOrderEpoch`. Even though deterministic
    per-epoch `optRand` (`buildStatefulDetOptDomain reqEpoch sk.pkSeed`) is kept intact, leaf
    wraparound / reuse exposes two distinct WOTS+C codewords on the same leaf and enables a
    purely public black-box WOTS+C forgery without any hash collision or preimage inversion! -/
def mutantUncheckedReuseSign (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (st : CheckedStatefulLatchState)
    (reqEpoch : Nat) (msg : List UInt8) (grindLimit : Nat) :
    Except CheckedStatefulError (CheckedStatefulLatchState × Nat × List UInt8 × PqHashSig) :=
  if !params.checkedStatefulValid then
    .error .invalidParams
  else
    let reusedLeaf := reqEpoch % (2 ^ params.maxSigsLog2)
    let detOpt := buildStatefulDetOptDomain reqEpoch sk.pkSeed
    match evalSingleSign suite params sk msg detOpt reusedLeaf grindLimit with
    | none => .error (.grindExhausted reusedLeaf grindLimit)
    | some sig => .ok (st, reusedLeaf, msg, sig)

/-- **Black-Box Two-Time WOTS+C Leaf-Reuse Forger (`forgeFromReusedLeafSigs`)**:
    Uses ONLY public `(pk, m₁, sig₁, m₂, sig₂, msgStar, rStar, ctrStar)` (zero `sk` access!)
    to step forward from whichever revealed chain value (`sig₁` or `sig₂`) sits at or below
    `digStar[r]`, reusing `sig₁`'s authentication path and upper hypertree layers. -/
def forgeFromReusedLeafSigs (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (m₁ : List UInt8) (sig₁ : PqHashSig)
    (m₂ : List UInt8) (sig₂ : PqHashSig)
    (msgStar rStar : List UInt8) (ctrStar : Nat) : PqHashSig :=
  let leaf := sig₁.leafGlobalIdx
  let subLeaves := 2 ^ params.subtreeHeight
  let kp0 := leaf % subLeaves
  let tree0 := UInt64.ofNat (leaf / subLeaves)
  let mu₁ := thPreHash suite pk.pkSeed pk.pkRoot m₁
  let mu₂ := thPreHash suite pk.pkSeed pk.pkRoot m₂
  let muStar := thPreHash suite pk.pkSeed pk.pkRoot msgStar
  let ls₁ := sig₁.layerSigs.getD 0 ⟨0, [], []⟩
  let ls₂ := sig₂.layerSigs.getD 0 ⟨0, [], []⟩
  let dig₁ := extractBaseWDigits params.w params.ell1
    (thHashMsg suite sig₁.rRand pk.pkSeed pk.pkRoot mu₁ 0 tree0 (UInt32.ofNat kp0) ls₁.tswCtr)
  let dig₂ := extractBaseWDigits params.w params.ell1
    (thHashMsg suite sig₂.rRand pk.pkSeed pk.pkRoot mu₂ 0 tree0 (UInt32.ofNat kp0) ls₂.tswCtr)
  let digStar := extractBaseWDigits params.w params.ell1
    (thHashMsg suite rStar pk.pkSeed pk.pkRoot muStar 0 tree0 (UInt32.ofNat kp0) ctrStar)
  let forgedChains0 := (List.range params.ell1).map fun r =>
    let dStarR := digStar.getD r 0
    let d1R := dig₁.getD r 0
    let d2R := dig₂.getD r 0
    if d1R ≤ dStarR then
      wotsChainSteps suite pk.pkSeed 0 tree0 kp0 r d1R (dStarR - d1R) (ls₁.wotsChains.getD r [])
    else
      wotsChainSteps suite pk.pkSeed 0 tree0 kp0 r d2R (dStarR - d2R) (ls₂.wotsChains.getD r [])
  let lsStar0 : LayerXmssSig := { tswCtr := ctrStar, wotsChains := forgedChains0, authPath := ls₁.authPath }
  { rRand := rStar
    msgTswCtr := 0
    leafGlobalIdx := leaf
    forsOpenings := []
    layerSigs := lsStar0 :: sig₁.layerSigs.drop 1 }

/-- **Universal `#tooth` Collision-Free Two-Signature Forgery Theorem
    (`mutantUncheckedReuseSign_collision_free_forgery`)**:
    For ANY `TweakableHashSuite` (including `poseidon2Suite` and `cshake256Suite`), ANY valid
    stateful parameter set, and ANY two `mutantUncheckedReuseSign` outputs on the same leaf
    whose codewords `dig₁, dig₂` cover `digStar` (`min(dig₁[r], dig₂[r]) ≤ digStar[r]`),
    `forgeFromReusedLeafSigs` (without `sk`) produces a signature `sigStar` such that:
    1. `verifyCheckedStateful suite params pk msgStar sigStar = true`;
    2. Every forged layer-0 chain value is **identically equal** to `honestChainNode` (zero hash
       collisions anywhere in WOTS+C or Merkle verification); and
    3. When `params.numLayers = 1`, `CheckedStatefulWotsTswWitness` over the 2-signature mutant
       log is **uninhabited (`→ False`)** — proving leaf uniqueness is mathematically necessary! -/
theorem mutantUncheckedReuseSign_collision_free_forgery
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    {st₁ st₁' st₂ st₂' : CheckedStatefulLatchState}
    {reqEp₁ reqEp₂ grind₁ grind₂ leaf₁ leaf₂ : Nat}
    {m₁ outM₁ m₂ outM₂ : List UInt8}
    {sig₁ sig₂ : PqHashSig}
    (msgStar rStar : List UInt8) (ctrStar : Nat)
    (hMut₁ : mutantUncheckedReuseSign suite params sk st₁ reqEp₁ m₁ grind₁ = .ok (st₁', leaf₁, outM₁, sig₁))
    (hMut₂ : mutantUncheckedReuseSign suite params sk st₂ reqEp₂ m₂ grind₂ = .ok (st₂', leaf₂, outM₂, sig₂))
    (hSameLeaf : reqEp₁ % (2 ^ params.maxSigsLog2) = reqEp₂ % (2 ^ params.maxSigsLog2))
    (hTswStar :
      let pk := derivePublicKey suite params sk
      let leaf := sig₁.leafGlobalIdx
      let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
      let kp0 := leaf % 2 ^ params.subtreeHeight
      checkTargetSum params.w params.ell1 params.targetSum
        (extractBaseWDigits params.w params.ell1
          (thHashMsg suite rStar pk.pkSeed pk.pkRoot
            (thPreHash suite pk.pkSeed pk.pkRoot msgStar) 0 tree0 (UInt32.ofNat kp0) ctrStar)) = true)
    (hDom :
      let pk := derivePublicKey suite params sk
      let leaf := sig₁.leafGlobalIdx
      let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
      let kp0 := leaf % 2 ^ params.subtreeHeight
      let dig₁ := extractBaseWDigits params.w params.ell1
        (thHashMsg suite sig₁.rRand pk.pkSeed pk.pkRoot
          (thPreHash suite pk.pkSeed pk.pkRoot m₁) 0 tree0 (UInt32.ofNat kp0)
          (sig₁.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
      let dig₂ := extractBaseWDigits params.w params.ell1
        (thHashMsg suite sig₂.rRand pk.pkSeed pk.pkRoot
          (thPreHash suite pk.pkSeed pk.pkRoot m₂) 0 tree0 (UInt32.ofNat kp0)
          (sig₂.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
      let digStar := extractBaseWDigits params.w params.ell1
        (thHashMsg suite rStar pk.pkSeed pk.pkRoot
          (thPreHash suite pk.pkSeed pk.pkRoot msgStar) 0 tree0 (UInt32.ofNat kp0) ctrStar)
      ∀ r, r < params.ell1 → dig₁.getD r 0 ≤ digStar.getD r 0 ∨ dig₂.getD r 0 ≤ digStar.getD r 0) :
    let pk := derivePublicKey suite params sk
    let sigStar := forgeFromReusedLeafSigs suite params pk m₁ sig₁ m₂ sig₂ msgStar rStar ctrStar
    let leaf := sig₁.leafGlobalIdx
    let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
    let kp0 := leaf % 2 ^ params.subtreeHeight
    let digStar := extractBaseWDigits params.w params.ell1
      (thHashMsg suite rStar pk.pkSeed pk.pkRoot
        (thPreHash suite pk.pkSeed pk.pkRoot msgStar) 0 tree0 (UInt32.ofNat kp0) ctrStar)
    verifyCheckedStateful suite params pk msgStar sigStar = true ∧
    (∀ r, r < params.ell1 →
      (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains.getD r [] =
        honestChainNode suite sk 0 tree0 kp0 r (digStar.getD r 0)) ∧
    (params.numLayers = 1 →
      CheckedStatefulWotsTswWitness suite params sk
        [(leaf₁, m₁, sig₁), (leaf₂, m₂, sig₂)] msgStar sigStar → False) := by
  unfold mutantUncheckedReuseSign at hMut₁ hMut₂
  cases hValid : params.checkedStatefulValid
  · simp [hValid] at hMut₁
  · simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hMut₁ hMut₂
    cases hEv₁ : evalSingleSign suite params sk m₁
        (buildStatefulDetOptDomain reqEp₁ sk.pkSeed) (reqEp₁ % 2 ^ params.maxSigsLog2) grind₁ with
    | none => rw [hEv₁] at hMut₁; cases hMut₁
    | some s1 =>
      rw [hEv₁] at hMut₁
      injection hMut₁ with hT1
      rcases Prod.mk.inj hT1 with ⟨_, hT1b⟩
      rcases Prod.mk.inj hT1b with ⟨hL1, hT1c⟩
      rcases Prod.mk.inj hT1c with ⟨_, hS1⟩
      subst leaf₁; subst s1
      cases hEv₂ : evalSingleSign suite params sk m₂
          (buildStatefulDetOptDomain reqEp₂ sk.pkSeed) (reqEp₂ % 2 ^ params.maxSigsLog2) grind₂ with
      | none => rw [hEv₂] at hMut₂; cases hMut₂
      | some s2 =>
        rw [hEv₂] at hMut₂
        injection hMut₂ with hT2
        rcases Prod.mk.inj hT2 with ⟨_, hT2b⟩
        rcases Prod.mk.inj hT2b with ⟨hL2, hT2c⟩
        rcases Prod.mk.inj hT2c with ⟨_, hS2⟩
        subst leaf₂; subst s2
        obtain ⟨hWf, hSt, _, _, _, hDPos, _, _⟩ := params.checkedStatefulValid_facts hValid
        have hBud₁ : reqEp₁ % 2 ^ params.maxSigsLog2 < 2 ^ params.maxSigsLog2 :=
          Nat.mod_lt _ (Nat.two_pow_pos _)
        obtain ⟨_, hLeafLt₁, hRand₁, _, hIdx₁, _, hLs₁⟩ :=
          evalSingleSign_stateful_inv suite params sk m₁ _ _ grind₁ sig₁ hSt hEv₁
        obtain ⟨_, _, hRand₂, _, hIdx₂, _, hLs₂⟩ :=
          evalSingleSign_stateful_inv suite params sk m₂ _ _ grind₂ sig₂ hSt hEv₂
        have hSameSigLeaf : sig₂.leafGlobalIdx = sig₁.leafGlobalIdx := by
          rw [hIdx₁, hIdx₂, hSameLeaf]
        obtain ⟨dRem, hNumLayers⟩ : ∃ dRem, params.numLayers = dRem + 1 :=
          ⟨params.numLayers - 1, (Nat.sub_add_cancel hDPos).symm⟩
        rw [hNumLayers, signHypertreeLayers_succ] at hLs₁ hLs₂
        dsimp only at hLs₁ hLs₂
        cases hG₁ : grindTswCounterAux suite params.w params.ell1 params.targetSum
            (thPrfMsg suite sk.skPrf (buildStatefulDetOptDomain reqEp₁ sk.pkSeed)
              (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot m₁))
            sk.pkSeed (derivePublicKey suite params sk).pkRoot
            (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot m₁)
            (UInt32.ofNat 0)
            (UInt64.ofNat ((reqEp₁ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight))
            (UInt32.ofNat ((reqEp₁ % 2 ^ params.maxSigsLog2) % 2 ^ params.subtreeHeight))
            0 grind₁ with
        | none => rw [hG₁] at hLs₁; cases hLs₁
        | some tr1 =>
          rcases tr1 with ⟨ctr1, dg1, hm1⟩
          rw [hG₁] at hLs₁; dsimp only at hLs₁
          cases hRest₁ : signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot []
              grind₁ 1 ((reqEp₁ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight)
              (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 0)
                (UInt64.ofNat ((reqEp₁ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight))) dRem with
          | none => rw [hRest₁] at hLs₁; cases hLs₁
          | some restSigs₁ =>
            rw [hRest₁] at hLs₁
            injection hLs₁ with hSig1Cons
            cases hG₂ : grindTswCounterAux suite params.w params.ell1 params.targetSum
                (thPrfMsg suite sk.skPrf (buildStatefulDetOptDomain reqEp₂ sk.pkSeed)
                  (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot m₂))
                sk.pkSeed (derivePublicKey suite params sk).pkRoot
                (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot m₂)
                (UInt32.ofNat 0)
                (UInt64.ofNat ((reqEp₂ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight))
                (UInt32.ofNat ((reqEp₂ % 2 ^ params.maxSigsLog2) % 2 ^ params.subtreeHeight))
                0 grind₂ with
            | none => rw [hG₂] at hLs₂; cases hLs₂
            | some tr2 =>
              rcases tr2 with ⟨ctr2, dg2, hm2⟩
              rw [hG₂] at hLs₂; dsimp only at hLs₂
              cases hRest₂ : signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot []
                  grind₂ 1 ((reqEp₂ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight)
                  (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 0)
                    (UInt64.ofNat ((reqEp₂ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight))) dRem with
              | none => rw [hRest₂] at hLs₂; cases hLs₂
              | some restSigs₂ =>
                rw [hRest₂] at hLs₂
                injection hLs₂ with hSig2Cons
                obtain ⟨hmEq1, hdEq1, _⟩ := grindTswCounterAux_sound hG₁
                obtain ⟨hmEq2, hdEq2, _⟩ := grindTswCounterAux_sound hG₂
                have hU0 : UInt32.ofNat 0 = (0 : UInt32) := rfl
                have hPkSeed : (derivePublicKey suite params sk).pkSeed = sk.pkSeed := rfl
                let pk := derivePublicKey suite params sk
                let leaf := sig₁.leafGlobalIdx
                let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
                let kp0 := leaf % 2 ^ params.subtreeHeight
                let digStar := extractBaseWDigits params.w params.ell1
                  (thHashMsg suite rStar pk.pkSeed pk.pkRoot
                    (thPreHash suite pk.pkSeed pk.pkRoot msgStar) 0 tree0 (UInt32.ofNat kp0) ctrStar)
                let sigStar := forgeFromReusedLeafSigs suite params pk m₁ sig₁ m₂ sig₂ msgStar rStar ctrStar
                have hLs1Get0 : sig₁.layerSigs.getD 0 ⟨0, [], []⟩ =
                    { tswCtr := ctr1
                      wotsChains := (List.range params.ell1).map fun r =>
                        wotsChainSteps suite sk.pkSeed 0 tree0 kp0 r 0 (dg1.getD r 0)
                          (wotsSecretBase suite sk 0 tree0 kp0 r)
                      authPath := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .tree
                        (computeWotsPk suite params sk 0 tree0) params.subtreeHeight 0 kp0 } := by
                  rw [← hSig1Cons, List.getD_cons_zero]
                  simp only [hU0, leaf, tree0, kp0, hIdx₁]
                have hLs2Get0 : sig₂.layerSigs.getD 0 ⟨0, [], []⟩ =
                    { tswCtr := ctr2
                      wotsChains := (List.range params.ell1).map fun r =>
                        wotsChainSteps suite sk.pkSeed 0 tree0 kp0 r 0 (dg2.getD r 0)
                          (wotsSecretBase suite sk 0 tree0 kp0 r)
                      authPath := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .tree
                        (computeWotsPk suite params sk 0 tree0) params.subtreeHeight 0 kp0 } := by
                  rw [← hSig2Cons, List.getD_cons_zero]
                  simp only [hU0, leaf, tree0, kp0, hIdx₁, hSameLeaf]
                have hDig1Eq :
                    extractBaseWDigits params.w params.ell1
                      (thHashMsg suite sig₁.rRand pk.pkSeed pk.pkRoot
                        (thPreHash suite pk.pkSeed pk.pkRoot m₁) 0 tree0 (UInt32.ofNat kp0)
                        (sig₁.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr) = dg1 := by
                  rw [hLs1Get0]
                  dsimp only
                  rw [hRand₁, hPkSeed]
                  simp only [leaf, tree0, kp0, hIdx₁]
                  rw [← hU0, ← hmEq1, ← hdEq1]
                have hDig2Eq :
                    extractBaseWDigits params.w params.ell1
                      (thHashMsg suite sig₂.rRand pk.pkSeed pk.pkRoot
                        (thPreHash suite pk.pkSeed pk.pkRoot m₂) 0 tree0 (UInt32.ofNat kp0)
                        (sig₂.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr) = dg2 := by
                  rw [hLs2Get0]
                  dsimp only
                  rw [hRand₂, hPkSeed]
                  simp only [leaf, tree0, kp0, hIdx₁, hSameLeaf]
                  rw [← hU0, ← hmEq2, ← hdEq2]
                have hChainStar : ∀ r, r < params.ell1 →
                    (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains.getD r [] =
                      honestChainNode suite sk 0 tree0 kp0 r (digStar.getD r 0) := by
                  intro r hr
                  have hDomR := hDom r hr
                  rw [hDig1Eq, hDig2Eq] at hDomR
                  dsimp only [sigStar, forgeFromReusedLeafSigs]
                  rw [List.getD_cons_zero]
                  rw [list_getD_map_range params.ell1 _ [] hr]
                  change (if (extractBaseWDigits params.w params.ell1
                            (thHashMsg suite sig₁.rRand pk.pkSeed pk.pkRoot
                              (thPreHash suite pk.pkSeed pk.pkRoot m₁) 0 tree0 (UInt32.ofNat kp0)
                              (sig₁.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)).getD r 0 ≤ digStar.getD r 0 then _ else _) = _
                  rw [hDig1Eq, hDig2Eq]
                  by_cases hLe1 : dg1.getD r 0 ≤ digStar.getD r 0
                  · simp only [hLe1, ↓reduceIte]
                    rw [hLs1Get0]
                    dsimp only
                    rw [list_getD_map_range params.ell1 _ [] hr, hPkSeed]
                    have hStep := wotsChainSteps_add suite sk.pkSeed 0 tree0 kp0 r
                      (dg1.getD r 0) (digStar.getD r 0 - dg1.getD r 0) 0
                      (wotsSecretBase suite sk 0 tree0 kp0 r)
                    rw [Nat.zero_add, Nat.add_sub_of_le hLe1] at hStep
                    exact hStep
                  · simp only [hLe1, ↓reduceIte]
                    have hLe2 : dg2.getD r 0 ≤ digStar.getD r 0 := by
                      rcases hDomR with h1 | h2
                      · exact absurd h1 hLe1
                      · exact h2
                    rw [hLs2Get0]
                    dsimp only
                    rw [list_getD_map_range params.ell1 _ [] hr, hPkSeed]
                    have hStep := wotsChainSteps_add suite sk.pkSeed 0 tree0 kp0 r
                      (dg2.getD r 0) (digStar.getD r 0 - dg2.getD r 0) 0
                      (wotsSecretBase suite sk 0 tree0 kp0 r)
                    rw [Nat.zero_add, Nat.add_sub_of_le hLe2] at hStep
                    exact hStep
                have hChainsListEq :
                    (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains =
                      (List.range params.ell1).map fun r =>
                        honestChainNode suite sk 0 tree0 kp0 r (digStar.getD r 0) := by
                  have hLenL : (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains.length = params.ell1 := by
                    dsimp [sigStar, forgeFromReusedLeafSigs]; simp
                  apply List.ext_getElem
                  · rw [hLenL, List.length_map, List.length_range]
                  · intro r hr1 hr2
                    have hr : r < params.ell1 := by simp at hr2; exact hr2
                    rw [← list_getD_eq_getElem _ [] hr1, ← list_getD_eq_getElem _ [] hr2,
                        list_getD_map_range params.ell1 _ [] hr]
                    exact hChainStar r hr
                refine ⟨?_, hChainStar, ?_⟩
                · -- Prove `verifyCheckedStateful suite params pk msgStar sigStar = true`
                  have hDrop1 : sig₁.layerSigs.drop 1 = restSigs₁ := by
                    rw [← hSig1Cons]; rfl
                  have hSubPos : 0 < 2 ^ params.subtreeHeight := Nat.two_pow_pos _
                  have hTreeLt : (reqEp₁ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight <
                      2 ^ (dRem * params.subtreeHeight) := by
                    rw [hNumLayers, Nat.succ_mul, Nat.pow_add] at hLeafLt₁
                    exact (Nat.div_lt_iff_lt_mul hSubPos).mpr hLeafLt₁
                  have hRestInfo : restSigs₁.length = dRem ∧
                      verifyHypertreeLayers suite params sk.pkSeed pk.pkRoot [] 1
                        ((reqEp₁ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight)
                        (computeXmssSubtreeRoot suite params sk 0 tree0) restSigs₁ =
                      some pk.pkRoot := by
                    cases dRem with
                    | zero =>
                      rw [signHypertreeLayers_zero] at hRest₁
                      injection hRest₁ with hNil
                      subst hNil
                      have hTree0 : (reqEp₁ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight = 0 :=
                        Nat.lt_one_iff.mp (by simpa only [Nat.zero_mul, Nat.pow_zero] using hTreeLt)
                      refine ⟨rfl, ?_⟩
                      rw [verifyHypertreeLayers_nil]
                      simp only [Option.some.injEq, pk, derivePublicKey, hNumLayers, Nat.zero_add,
                                 Nat.sub_self, hU0, tree0, leaf, hIdx₁, hTree0]
                      rfl
                    | succ rRem =>
                      have hSnd := signHypertreeLayers_sound suite params sk pk.pkRoot grind₁
                        (rRem + 1) 1 ((reqEp₁ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight) []
                        (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 0)
                          (UInt64.ofNat ((reqEp₁ % 2 ^ params.maxSigsLog2) / 2 ^ params.subtreeHeight)))
                        restSigs₁ (Nat.succ_pos _) hTreeLt hRest₁
                      refine ⟨hSnd.1, ?_⟩
                      have hTopEq : UInt32.ofNat (1 + (rRem + 1) - 1) = UInt32.ofNat (params.numLayers - 1) := by
                        rw [hNumLayers]; congr 1; omega
                      simpa only [hU0, tree0, leaf, hIdx₁, pk, derivePublicKey, hTopEq] using hSnd.2
                  rw [verifyCheckedStateful_eq]
                  have hSigLeaf : sigStar.leafGlobalIdx = reqEp₁ % 2 ^ params.maxSigsLog2 := hIdx₁
                  rw [hValid, hSigLeaf, decide_eq_true hBud₁]
                  simp only [Bool.true_and]
                  have hSigLen : sigStar.layerSigs.length = params.numLayers := by
                    dsimp only [sigStar, forgeFromReusedLeafSigs, List.length_cons]
                    rw [hDrop1, hRestInfo.1, hNumLayers]
                  have hLeafLtStar : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) := by
                    rw [hSigLeaf]; exact hLeafLt₁
                  have hForsEmpty : sigStar.forsOpenings = [] ∧ sigStar.msgTswCtr = 0 := ⟨rfl, rfl⟩
                  have hVerLayers :
                      verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot sigStar.rRand 0
                        sigStar.leafGlobalIdx (thPreHash suite pk.pkSeed pk.pkRoot msgStar) sigStar.layerSigs =
                      some pk.pkRoot := by
                    have hStarRand : sigStar.rRand = rStar := rfl
                    have hStarIdx : sigStar.leafGlobalIdx = leaf := rfl
                    have hStarLayers : sigStar.layerSigs = (sigStar.layerSigs.getD 0 ⟨0, [], []⟩) :: restSigs₁ := by
                      dsimp only [sigStar, forgeFromReusedLeafSigs]; rw [List.getD_cons_zero, hDrop1]
                    rw [hStarRand, hStarIdx, hStarLayers, verifyHypertreeLayers_cons]
                    have hTsw' : checkTargetSum params.w params.ell1 params.targetSum digStar = true := hTswStar
                    have hChLen' : (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains.length = params.ell1 := by
                      rw [hChainsListEq]; simp
                    have hCtrStar : (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr = ctrStar := rfl
                    have hAuthStar : (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).authPath =
                        buildMerkleAuthPath suite sk.pkSeed 0 tree0 .tree
                          (computeWotsPk suite params sk 0 tree0) params.subtreeHeight 0 kp0 := by
                      dsimp only [sigStar, forgeFromReusedLeafSigs]; rw [List.getD_cons_zero, hLs1Get0]
                    simp only [hU0, tree0, kp0, hCtrStar, digStar, hTsw', Bool.not_true, Bool.false_eq_true,
                               ↓reduceIte, hChLen', ne_eq, not_true_eq_false]
                    rw [hChainsListEq, hAuthStar, hPkSeed]
                    have hWotsEq := recoverWotsPkFromSig_eq_computeWotsPk suite params sk 0 tree0 kp0 digStar hTsw'
                    have hWotsGoal :
                        recoverWotsPkFromSig suite params sk.pkSeed 0
                          (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight)
                          (extractBaseWDigits params.w params.ell1
                            (thHashMsg suite rStar sk.pkSeed pk.pkRoot (thPreHash suite sk.pkSeed pk.pkRoot msgStar) 0
                              (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (UInt32.ofNat (leaf % 2 ^ params.subtreeHeight))
                              ctrStar))
                          (List.map (fun r => honestChainNode suite sk 0 tree0 kp0 r (digStar.getD r 0))
                            (List.range params.ell1)) =
                        computeWotsPk suite params sk 0 tree0 kp0 := hWotsEq
                    rw [hWotsGoal]
                    have hWalk0 := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed 0 tree0 .tree
                      (computeWotsPk suite params sk 0 tree0) params.subtreeHeight 0 kp0 (Nat.mod_lt _ hSubPos)
                    simp only [Nat.zero_mul, Nat.zero_add] at hWalk0
                    have hWalkGoal :
                        walkMerkleAuthPath suite sk.pkSeed 0 (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) .tree
                          params.subtreeHeight 0 (leaf % 2 ^ params.subtreeHeight)
                          (computeWotsPk suite params sk 0 tree0 kp0)
                          (buildMerkleAuthPath suite sk.pkSeed 0 tree0 .tree
                            (computeWotsPk suite params sk 0 tree0) params.subtreeHeight 0 kp0) =
                        some (computeMerkleNode suite sk.pkSeed 0 tree0 .tree
                          (computeWotsPk suite params sk 0 tree0) params.subtreeHeight 0) := hWalk0
                    rw [hWalkGoal]
                    dsimp only
                    rw [← computeXmssSubtreeRoot_eq]
                    simpa only [Nat.zero_add, leaf, hIdx₁] using hRestInfo.2
                  rcases (⟨sigStar, rfl⟩ : ∃ sStar, sStar = sigStar) with ⟨sStar, hSS⟩
                  change verifyPqHashSig suite params pk msgStar sigStar = true
                  rw [← hSS] at hSigLen hLeafLtStar hForsEmpty hVerLayers ⊢
                  unfold verifyPqHashSig
                  simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hSigLen, ne_eq,
                             not_true_eq_false, hLeafLtStar, decide_true, hSt, hForsEmpty.1,
                             List.isEmpty_nil, hForsEmpty.2, decide_false, Bool.or_self]
                  rw [hVerLayers]
                  simp
                · -- Prove `CheckedStatefulWotsTswWitness ... → False` when `params.numLayers = 1`
                  intro hNum1 w
                  have hLay0 : w.layerIdx = 0 := by have := w.layer_lt; omega
                  have hSD := w.layer0_digest hLay0
                  have hFDig := w.forgedDigit_eq
                  rw [hLay0] at hFDig
                  simp only [↓reduceIte, Nat.zero_mul, Nat.pow_zero, Nat.div_one, hU0, hSD] at hFDig
                  have hStarLeafEq : sigStar.leafGlobalIdx = leaf := rfl
                  have hStarCtrEq : (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr = ctrStar := rfl
                  rw [hStarLeafEq, hStarCtrEq] at hFDig
                  have hAddr1 : wotsPosAddr params sig₁.leafGlobalIdx 0 =
                      wotsPosAddr params sigStar.leafGlobalIdx w.layerIdx := by
                    rw [hLay0]; rfl
                  have hAddr2 : wotsPosAddr params sig₂.leafGlobalIdx 0 =
                      wotsPosAddr params sigStar.leafGlobalIdx w.layerIdx := by
                    rw [hLay0, hSameSigLeaf]; rfl
                  have hLt1 := w.unrevealedInLog (reqEp₁ % 2 ^ params.maxSigsLog2, m₁, sig₁)
                    List.mem_cons_self 0 (by omega) hAddr1
                  have hLt2 := w.unrevealedInLog (reqEp₂ % 2 ^ params.maxSigsLog2, m₂, sig₂)
                    (List.mem_cons_of_mem _ List.mem_cons_self) 0 (by omega) hAddr2
                  have hLog1 : statefulLogLayerDigits suite params sk
                      (reqEp₁ % 2 ^ params.maxSigsLog2, m₁, sig₁) 0 = dg1 := by
                    rw [statefulLogLayerDigits_eq]
                    simp only [honestStatefulLayerRand, honestStatefulLayerRoot, ↓reduceIte,
                               Nat.zero_mul, Nat.pow_zero, Nat.div_one, hU0]
                    exact hDig1Eq
                  have hLog2 : statefulLogLayerDigits suite params sk
                      (reqEp₂ % 2 ^ params.maxSigsLog2, m₂, sig₂) 0 = dg2 := by
                    rw [statefulLogLayerDigits_eq]
                    simp only [honestStatefulLayerRand, honestStatefulLayerRoot, ↓reduceIte,
                               Nat.zero_mul, Nat.pow_zero, Nat.div_one, hU0, hSameSigLeaf]
                    exact hDig2Eq
                  rw [hLog1] at hLt1
                  rw [hLog2] at hLt2
                  have hDomR := hDom w.chainIdx w.chain_lt
                  change _ ≤ digStar.getD w.chainIdx 0 ∨ _ ≤ digStar.getD w.chainIdx 0 at hDomR
                  rw [hDig1Eq, hDig2Eq] at hDomR
                  change w.forgedDigit = digStar.getD w.chainIdx 0 at hFDig
                  rw [hFDig] at hLt1 hLt2
                  rcases hDomR with hLe1 | hLe2 <;> omega

/-- Domain-separated concrete hash suite for `#tooth` executable verification:
    - `thPrfMsg` (`6` frames) maps `epoch = 0` (`bytes[88] = 0`) vs `epoch ≠ 0` (`bytes[88] ≠ 0`)
      to distinct `rRand` prefixes `[1, ...]` vs `[2, ...]`;
    - `thHashMsg` (`7` frames) maps `rRand[0] = 1, 2, 3` (`bytes[52]`) to three pairwise distinct
      128-crumb (`w = 4`) codewords `d₁ ≠ d₂`, `dStar ≠ d₁`, `dStar ≠ d₂`, all with target sum `192`
      and satisfying `min(d₁[r], d₂[r]) ≤ dStar[r]` for every `r < 128`! -/
def toothDistinctSuite : TweakableHashSuite where
  suiteId := []
  rawHash := fun bytes =>
    match bytes with
    | b :: _ =>
      if b == 6 then
        if bytes.getD 88 0 == 0 then
          [1] ++ List.replicate 31 0
        else
          [2] ++ List.replicate 31 0
      else if b == 7 then
        match bytes.getD 52 0 with
        | 1 => [0x0F, 0xF0] ++ List.replicate 30 0x1B
        | 2 => [0xF0, 0x0F] ++ List.replicate 30 0x1B
        | 3 => [0x66, 0x99] ++ List.replicate 30 0x1B
        | _ => List.replicate 32 0x1B
      else
        List.replicate 32 0x1B
    | [] => List.replicate 32 0x1B
  rawHash_len := fun bytes => by
    cases bytes with
    | nil => rfl
    | cons b bs =>
      dsimp only
      by_cases hb6 : b == 6
      · simp only [hb6, ↓reduceIte]
        split <;> rfl
      · simp only [hb6, Bool.false_eq_true, ↓reduceIte]
        by_cases hb7 : b == 7
        · simp only [hb7, ↓reduceIte]
          split <;> rfl
        · simp [hb7]

private theorem byteArray_loop_eq (bs : ByteArray) :
    ∀ i acc, ByteArray.toList.loop bs i acc = acc.reverse ++ (bs.data.toList.drop i) := by
  intro i acc
  induction h : bs.size - i generalizing i acc with
  | zero =>
    rw [ByteArray.toList.loop.eq_1]
    have hGe : ¬ (i < bs.size) := by omega
    simp only [hGe, ↓reduceIte]
    have hLen : bs.data.toList.length ≤ i := by
      have : bs.data.toList.length = bs.size := Array.length_toList
      omega
    rw [List.drop_of_length_le hLen, List.append_nil]
  | succ k ih =>
    rw [ByteArray.toList.loop.eq_1]
    have hLt : i < bs.size := by omega
    simp only [hLt, ↓reduceIte]
    rw [ih (i + 1) (bs.get! i :: acc) (by omega)]
    have hLtList : i < bs.data.toList.length := by
      have : bs.data.toList.length = bs.size := Array.length_toList
      omega
    have hGet : bs.get! i = bs.data.toList[i] := by
      simp only [ByteArray.get!, Array.getElem_toList]
      exact getElem!_pos bs.data i hLt
    rw [hGet, List.reverse_cons, List.append_assoc, List.singleton_append,
        ← List.drop_eq_getElem_cons hLtList]

private theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [byteArray_loop_eq bs 0 []]
  simp

private theorem tagPrfMsg_bytes_eq :
    tagPrfMsg = [81, 83, 65, 71, 46, 80, 81, 46, 80, 82, 70, 77, 83, 71, 47, 118, 49] := by
  unfold tagPrfMsg
  rw [byteArray_toList_eq, String.toUTF8_eq_toByteArray]
  have hStr : "QSAG.PQ.PRFMSG/v1" =
      String.ofList ['Q', 'S', 'A', 'G', '.', 'P', 'Q', '.', 'P', 'R', 'F', 'M', 'S', 'G', '/', 'v', '1'] := by
    decide +kernel
  rw [hStr, String.toByteArray_ofList]
  decide +kernel

private theorem thPrfMsg_tooth_eq (skPrf optRand mu : List UInt8) :
    thPrfMsg toothDistinctSuite skPrf optRand mu =
      toothDistinctSuite.rawHash
        (encodeMultiFrame [[81, 83, 65, 71, 46, 80, 81, 46, 80, 82, 70, 77, 83, 71, 47, 118, 49],
          [], encodeAdrs zeroAdrs, skPrf, optRand, mu]) := by
  unfold thPrfMsg thCall thPreimage
  rw [tagPrfMsg_bytes_eq]
  rfl

/-- Concrete 1-layer stateful profile with budget `2 ^ 1 = 2` signatures (`maxSigsLog2 = 1`). -/
def toothStatefulParams : PqHashParams := ⟨4, 128, 1, 1, 0, 0, 1, true⟩

/-- **`#tooth` Concrete Executable Leaf-Reuse Forgery Witness
    (`tooth_mutantUncheckedReuseSign_concrete_forgery`)**:
    1. Real `checkedStatefulSignStep` strictly enforces the epoch budget (`2^1 = 2`) and aborts on
       epoch `2` with `.error (.budgetExhausted 2 2)` (and aborts on epoch-`0` equivocation with
       `.error (.equivocationRefused 0)`);
    2. `mutantUncheckedReuseSign` wraps `reqEpoch = 2` onto leaf `0`, emitting two valid signatures
       `sig₁` (on `m₁ = [1]`) and `sig₂` (on `m₂ = [2]`) with distinct codewords `dig₁ ≠ dig₂`;
    3. `forgeFromReusedLeafSigs` (using ONLY public inputs, zero `sk`) forges `sigStar` on fresh
       `msgStar = [3] ∉ [[1], [2]]` with a third distinct codeword `digStar` (`rStar = [3]`) passing
       `verifyCheckedStateful = true`, with every forged chain value equal to `honestChainNode`
       (`0` hash collisions) and `CheckedStatefulWotsTswWitness ... → False` (`0` backward inversions)! -/
theorem tooth_mutantUncheckedReuseSign_concrete_forgery :
    let suite := toothDistinctSuite
    let params := toothStatefulParams
    let sk : PqSecretKey := ⟨[], [], []⟩
    let pk := derivePublicKey suite params sk
    -- Real checked stateful oracle signs epochs 0 and 1, then aborts on epoch 2 (`budgetExhausted 2 2`)
    (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch
      [.signNext [1] 1, .signNext [9] 1, .signNext [2] 1]).abortError =
      some (.budgetExhausted 2 2) ∧
    -- Real checked stateful oracle also aborts on direct epoch-0 equivocation (`equivocationRefused 0`)
    (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch
      [.signEpoch 0 [1] 1, .signEpoch 0 [2] 1]).abortError =
      some (.equivocationRefused 0) ∧
    -- Mutant signer succeeds on both `(reqEpoch = 0, [1])` and `(reqEpoch = 2, [2])` at leaf 0,
    -- and public `forgeFromReusedLeafSigs` forges fresh `msgStar = [3]` with 0 collisions & 0 inversions:
    ∃ st1 st2 sig₁ sig₂,
      mutantUncheckedReuseSign suite params sk initCheckedStatefulLatch 0 [1] 1 = .ok (st1, 0, [1], sig₁) ∧
      mutantUncheckedReuseSign suite params sk st1 2 [2] 1 = .ok (st2, 0, [2], sig₂) ∧
      [3] ∉ ([[1], [2]] : List (List UInt8)) ∧
      let sigStar := forgeFromReusedLeafSigs suite params pk [1] sig₁ [2] sig₂ [3] [3] 0
      let digStar := extractBaseWDigits params.w params.ell1
        (thHashMsg suite [3] pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot [3]) 0 0 0 0)
      verifyCheckedStateful suite params pk [3] sigStar = true ∧
      (∀ r, r < params.ell1 →
        (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains.getD r [] =
          honestChainNode suite sk 0 0 0 r (digStar.getD r 0)) ∧
      (CheckedStatefulWotsTswWitness suite params sk [(0, [1], sig₁), (0, [2], sig₂)] [3] sigStar → False) := by
  intro suite params sk pk
  refine ⟨?_, ?_, ?_⟩
  · simp only [suite, params, sk, execCheckedStatefulOracle, execCheckedStatefulOracleAux,
               checkedStatefulSignStep, checkedStatefulFreshEpochSign, evalSingleSign, thPrfMsg_tooth_eq]
    decide +kernel
  · simp only [suite, params, sk, execCheckedStatefulOracle, execCheckedStatefulOracleAux,
               checkedStatefulSignStep, checkedStatefulFreshEpochSign, evalSingleSign, thPrfMsg_tooth_eq]
    decide +kernel
  · cases hM1 : mutantUncheckedReuseSign suite params sk
        initCheckedStatefulLatch 0 [1] 1 with
    | error e =>
      exfalso
      have hOk1 : (mutantUncheckedReuseSign suite params sk
          initCheckedStatefulLatch 0 [1] 1).isOk = true := by
        dsimp only [suite, params, sk]
        unfold mutantUncheckedReuseSign evalSingleSign
        simp only [thPrfMsg_tooth_eq]
        decide +kernel
      rw [hM1] at hOk1; cases hOk1
    | ok q1 =>
      rcases q1 with ⟨st1, leaf1, m1Out, sig₁⟩
      cases hM2 : mutantUncheckedReuseSign suite params sk
          st1 2 [2] 1 with
      | error e =>
        exfalso
        have hOk2 : (match mutantUncheckedReuseSign suite params sk
            initCheckedStatefulLatch 0 [1] 1 with
          | .error _ => false
          | .ok (s1, _, _, _) =>
            (mutantUncheckedReuseSign suite params sk s1 2 [2] 1).isOk) = true := by
          dsimp only [suite, params, sk]
          unfold mutantUncheckedReuseSign evalSingleSign
          simp only [thPrfMsg_tooth_eq]
          decide +kernel
        rw [hM1] at hOk2; dsimp only at hOk2; rw [hM2] at hOk2; cases hOk2
      | ok q2 =>
        rcases q2 with ⟨st2, leaf2, m2Out, sig₂⟩
        have hTV : toothStatefulParams.checkedStatefulValid = true := by decide +kernel
        have hL1AndIdx : leaf1 = 0 ∧ m1Out = [1] ∧ sig₁.leafGlobalIdx = 0 := by
          have hM1' := hM1
          dsimp only [suite, params, sk] at hM1'
          unfold mutantUncheckedReuseSign at hM1'
          rw [hTV] at hM1'
          dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hM1'
          cases hE1 : evalSingleSign toothDistinctSuite toothStatefulParams ⟨[], [], []⟩ [1]
              (buildStatefulDetOptDomain 0 []) (0 % 2 ^ toothStatefulParams.maxSigsLog2) 1 with
          | none => rw [hE1] at hM1'; cases hM1'
          | some s =>
            rw [hE1] at hM1'
            injection hM1' with hT
            rcases Prod.mk.inj hT with ⟨_, hTb⟩
            rcases Prod.mk.inj hTb with ⟨hLeaf, hTc⟩
            rcases Prod.mk.inj hTc with ⟨hMsg, hS⟩
            subst s
            have hInv := (evalSingleSign_stateful_inv toothDistinctSuite toothStatefulParams ⟨[], [], []⟩ [1]
              (buildStatefulDetOptDomain 0 []) (0 % 2 ^ toothStatefulParams.maxSigsLog2) 1 sig₁ rfl hE1).2.2.2.2.1
            exact ⟨hLeaf.symm, hMsg.symm, hInv⟩
        have hL2 : leaf2 = 0 ∧ m2Out = [2] := by
          have hM2' := hM2
          dsimp only [suite, params, sk] at hM2'
          unfold mutantUncheckedReuseSign at hM2'
          rw [hTV] at hM2'
          dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hM2'
          cases hE2 : evalSingleSign toothDistinctSuite toothStatefulParams ⟨[], [], []⟩ [2]
              (buildStatefulDetOptDomain 2 []) (2 % 2 ^ toothStatefulParams.maxSigsLog2) 1 with
          | none => rw [hE2] at hM2'; cases hM2'
          | some s =>
            rw [hE2] at hM2'
            injection hM2' with hT
            rcases Prod.mk.inj hT with ⟨_, hTb⟩
            rcases Prod.mk.inj hTb with ⟨hLeaf, hTc⟩
            exact ⟨hLeaf.symm, (Prod.mk.inj hTc).1.symm⟩
        rcases hL1AndIdx with ⟨rfl, rfl, hSig1Idx⟩
        rcases hL2 with ⟨rfl, rfl⟩
        have hTsw3 :
            let pk0 := derivePublicKey suite params sk
            let leaf := sig₁.leafGlobalIdx
            let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
            let kp0 := leaf % 2 ^ params.subtreeHeight
            checkTargetSum params.w params.ell1 params.targetSum
              (extractBaseWDigits params.w params.ell1
                (thHashMsg suite [3] pk0.pkSeed pk0.pkRoot
                  (thPreHash suite pk0.pkSeed pk0.pkRoot [3]) 0 tree0 (UInt32.ofNat kp0) 0)) = true := by
          dsimp only [suite, params, sk]
          rw [hSig1Idx]
          decide +kernel
        have hDom3 :
            let pk0 := derivePublicKey suite params sk
            let leaf := sig₁.leafGlobalIdx
            let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
            let kp0 := leaf % 2 ^ params.subtreeHeight
            let dig₁ := extractBaseWDigits params.w params.ell1
              (thHashMsg suite sig₁.rRand pk0.pkSeed pk0.pkRoot
                (thPreHash suite pk0.pkSeed pk0.pkRoot [1]) 0 tree0 (UInt32.ofNat kp0)
                (sig₁.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
            let dig₂ := extractBaseWDigits params.w params.ell1
              (thHashMsg suite sig₂.rRand pk0.pkSeed pk0.pkRoot
                (thPreHash suite pk0.pkSeed pk0.pkRoot [2]) 0 tree0 (UInt32.ofNat kp0)
                (sig₂.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
            let digStar := extractBaseWDigits params.w params.ell1
              (thHashMsg suite [3] pk0.pkSeed pk0.pkRoot
                (thPreHash suite pk0.pkSeed pk0.pkRoot [3]) 0 tree0 (UInt32.ofNat kp0) 0)
            ∀ r, r < params.ell1 →
              dig₁.getD r 0 ≤ digStar.getD r 0 ∨ dig₂.getD r 0 ≤ digStar.getD r 0 := by
          have hDecDom :
              (match mutantUncheckedReuseSign suite params sk
                       initCheckedStatefulLatch 0 [1] 1,
                     mutantUncheckedReuseSign suite params sk
                       st1 2 [2] 1 with
               | .ok (_, _, _, s1), .ok (_, _, _, s2) =>
                 let pk0 := derivePublicKey suite params sk
                 let leaf := s1.leafGlobalIdx
                 let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
                 let kp0 := leaf % 2 ^ params.subtreeHeight
                 let d1 := extractBaseWDigits params.w params.ell1
                   (thHashMsg suite s1.rRand pk0.pkSeed pk0.pkRoot
                     (thPreHash suite pk0.pkSeed pk0.pkRoot [1]) 0 tree0 (UInt32.ofNat kp0)
                     (s1.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
                 let d2 := extractBaseWDigits params.w params.ell1
                   (thHashMsg suite s2.rRand pk0.pkSeed pk0.pkRoot
                     (thPreHash suite pk0.pkSeed pk0.pkRoot [2]) 0 tree0 (UInt32.ofNat kp0)
                     (s2.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
                 let dS := extractBaseWDigits params.w params.ell1
                   (thHashMsg suite [3] pk0.pkSeed pk0.pkRoot
                     (thPreHash suite pk0.pkSeed pk0.pkRoot [3]) 0 tree0 (UInt32.ofNat kp0) 0)
                 (List.range params.ell1).all (fun r => decide (d1.getD r 0 ≤ dS.getD r 0 ∨ d2.getD r 0 ≤ dS.getD r 0))
               | _, _ => false) = true := by
            have hClosed :
                (match mutantUncheckedReuseSign suite params sk
                         initCheckedStatefulLatch 0 [1] 1 with
                 | .ok (s1State, _, _, s1) =>
                   match mutantUncheckedReuseSign suite params sk
                           s1State 2 [2] 1 with
                   | .ok (_, _, _, s2) =>
                     let pk0 := derivePublicKey suite params sk
                     let leaf := s1.leafGlobalIdx
                     let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
                     let kp0 := leaf % 2 ^ params.subtreeHeight
                     let d1 := extractBaseWDigits params.w params.ell1
                       (thHashMsg suite s1.rRand pk0.pkSeed pk0.pkRoot
                         (thPreHash suite pk0.pkSeed pk0.pkRoot [1]) 0 tree0 (UInt32.ofNat kp0)
                         (s1.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
                     let d2 := extractBaseWDigits params.w params.ell1
                       (thHashMsg suite s2.rRand pk0.pkSeed pk0.pkRoot
                         (thPreHash suite pk0.pkSeed pk0.pkRoot [2]) 0 tree0 (UInt32.ofNat kp0)
                         (s2.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
                     let dS := extractBaseWDigits params.w params.ell1
                       (thHashMsg suite [3] pk0.pkSeed pk0.pkRoot
                         (thPreHash suite pk0.pkSeed pk0.pkRoot [3]) 0 tree0 (UInt32.ofNat kp0) 0)
                     (List.range params.ell1).all (fun r => decide (d1.getD r 0 ≤ dS.getD r 0 ∨ d2.getD r 0 ≤ dS.getD r 0))
                   | .error _ => false
                 | .error _ => false) = true := by
              dsimp only [suite, params, sk]
              unfold mutantUncheckedReuseSign evalSingleSign
              simp only [thPrfMsg_tooth_eq]
              decide +kernel
            rw [hM1] at hClosed ⊢
            dsimp only at hClosed ⊢
            rw [hM2] at hClosed ⊢
            exact hClosed
          rw [hM1, hM2] at hDecDom
          dsimp only at hDecDom ⊢
          intro r hr
          have hAll := List.all_eq_true.mp hDecDom r (List.mem_range.mpr hr)
          exact of_decide_eq_true hAll
        obtain ⟨hVerStar, hChainsStar, hNoWots⟩ :=
          mutantUncheckedReuseSign_collision_free_forgery suite params sk
            [3] [3] 0 hM1 hM2 (by decide) hTsw3 hDom3
        refine ⟨st1, st2, sig₁, sig₂, ?_⟩
        refine ⟨rfl, hM2, by decide, ?_⟩
        intro sigStar digStar
        have hPk : derivePublicKey suite params sk = pk := rfl
        have hSigStar : forgeFromReusedLeafSigs suite params pk [1] sig₁ [2] sig₂ [3] [3] 0 = sigStar := rfl
        have hDigStar :
            extractBaseWDigits params.w params.ell1
              (thHashMsg suite [3] pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot [3]) 0 0 0 0) =
              digStar := rfl
        rw [hPk, hSigStar] at hVerStar
        have hParams1 : params.numLayers = 1 := rfl
        have hNoWots' := hNoWots hParams1
        rw [hPk, hSigStar] at hNoWots'
        refine ⟨hVerStar, ?_, hNoWots'⟩
        intro r hr
        have hC := hChainsStar r hr
        have hZeroDiv : 0 / 2 ^ params.subtreeHeight = 0 := Nat.zero_div _
        have hZeroMod : 0 % 2 ^ params.subtreeHeight = 0 := Nat.zero_mod _
        have hU64 : UInt64.ofNat 0 = (0 : UInt64) := rfl
        have hU32 : UInt32.ofNat 0 = (0 : UInt32) := rfl
        rw [hPk, hSigStar, hSig1Idx, hZeroDiv, hZeroMod, hU64, hU32, hDigStar] at hC
        exact hC

/-- Concrete 2-layer (`d = 2`) stateful profile with budget `2 ^ 2 = 4` signatures (`maxSigsLog2 = 2`). -/
def inhabitedStatefulParams : PqHashParams := ⟨4, 128, 1, 2, 0, 0, 2, true⟩

/-- Multi-turn checked stateful query schedule exercising fresh `.signNext` across subtree
    boundaries (`epoch = 0, 1`), crash-recovery `.retryEpoch 1`, and explicit `.signEpoch 2`. -/
def inhabitedStatefulQueries : List CheckedStatefulQuery :=
  [.signNext [10] 1, .signNext [20] 1, .retryEpoch 1 [20], .signEpoch 2 [30] 1]

/-- Well-shaped 2-layer signature on leaf `0` accepted by `verifyCheckedStateful` under `crumbToySuite`. -/
def inhabitedStatefulForgery : PqHashSig :=
  { rRand := []
    msgTswCtr := 0
    leafGlobalIdx := 0
    forsOpenings := []
    layerSigs := [⟨0, List.replicate 128 [], [[]]⟩, ⟨0, List.replicate 128 [], [[]]⟩] }

/-- **Inhabited Multi-Signature Constructive Extraction Witness (`inhabited_checked_stateful_multi_sign_extract`)**:
    Directly executes `checked_stateful_hypertree_euf_cma_extract` on the 4-entry, 2-layer
    multi-signature transcript produced by `inhabitedStatefulQueries` (`0 Classical.choice`). -/
def inhabited_checked_stateful_multi_sign_extract :
    let log := (execCheckedStatefulOracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
                  initCheckedStatefulLatch inhabitedStatefulQueries).emittedLog
    PSum (CheckedStatefulCollisionWitness crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩ log)
         (CheckedStatefulWotsTswWitness crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩ log
            [99] inhabitedStatefulForgery) :=
  checked_stateful_hypertree_euf_cma_extract
    crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
    inhabitedStatefulQueries [99] inhabitedStatefulForgery
    (.inl ⟨rfl, rfl⟩)
    (by decide +kernel)
    (by decide +kernel)

/-- **Multi-Signature Inhabitedness Theorem (`inhabited_checked_stateful_multi_sign_log`)**:
    Proves that all hypotheses of `checked_stateful_hypertree_euf_cma_extract` and
    `checked_stateful_strict_euf_cma_extract` are jointly inhabited on a genuine 2-layer (`d = 2`),
    multi-signature checked stateful execution:
    1. `execCheckedStatefulStrict` succeeds (`abortError = none`) with `stFinal.nextEpoch = 3` and
       `4` emitted log entries across epochs `[0, 1, 1, 2]` and messages `[[10], [20], [20], [30]]`;
    2. Every emitted signature passes `verifyCheckedStateful = true`;
    3. `msgStar = [99]` is fresh (`∉ log.map (·.2.1)`) and `inhabitedStatefulForgery` passes
       `verifyCheckedStateful = true`; and
    4. `checked_stateful_hypertree_euf_cma_extract` produces an inhabited transcript-indexed break witness! -/
theorem inhabited_checked_stateful_multi_sign_log :
    let suite := crumbToySuite
    let params := inhabitedStatefulParams
    let sk : PqSecretKey := ⟨[], [], []⟩
    let pk := derivePublicKey suite params sk
    let run := execCheckedStatefulOracle suite params sk initCheckedStatefulLatch inhabitedStatefulQueries
    run.abortError = none ∧
    (∃ stFinal, execCheckedStatefulStrict suite params sk initCheckedStatefulLatch inhabitedStatefulQueries =
      .ok (stFinal, run.emittedLog) ∧ stFinal.nextEpoch = 3) ∧
    run.emittedLog.length = 4 ∧
    (run.emittedLog.map Prod.fst) = [0, 1, 1, 2] ∧
    (run.emittedLog.map fun e => e.2.1) = [[10], [20], [20], [30]] ∧
    (∀ e ∈ run.emittedLog, verifyCheckedStateful suite params pk e.2.1 e.2.2 = true) ∧
    ([99] : List UInt8) ∉ (run.emittedLog.map fun e => e.2.1) ∧
    verifyCheckedStateful suite params pk [99] inhabitedStatefulForgery = true ∧
    (Nonempty (CheckedStatefulCollisionWitness suite params sk run.emittedLog) ∨
     Nonempty (CheckedStatefulWotsTswWitness suite params sk run.emittedLog [99] inhabitedStatefulForgery)) := by
  dsimp only
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel, ?_,
          by decide +kernel, by decide +kernel, ?_⟩
  · cases hStr : execCheckedStatefulStrict crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
        initCheckedStatefulLatch inhabitedStatefulQueries with
    | error err =>
      exfalso
      have hOk : (execCheckedStatefulStrict crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
          initCheckedStatefulLatch inhabitedStatefulQueries).isOk = true := by decide +kernel
      rw [hStr] at hOk; cases hOk
    | ok pair =>
      rcases pair with ⟨stFinal, log⟩
      have hOrcEq :=
        ((execCheckedStatefulStrict_eq_oracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
          inhabitedStatefulQueries initCheckedStatefulLatch).1 stFinal log).mp hStr
      have hLogEq : log = (execCheckedStatefulOracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
          initCheckedStatefulLatch inhabitedStatefulQueries).emittedLog :=
        congrArg CheckedStatefulOracleRun.emittedLog hOrcEq.symm
      have hNext : stFinal.nextEpoch = 3 := by
        have hDec : (match execCheckedStatefulStrict crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
                        initCheckedStatefulLatch inhabitedStatefulQueries with
                     | .ok (s, _) => s.nextEpoch == 3
                     | .error _ => false) = true := by decide +kernel
        rw [hStr] at hDec
        exact of_decide_eq_true (by simpa [beq_iff_eq] using hDec)
      exact ⟨stFinal, by rw [← hLogEq], hNext⟩
  · intro e he
    exact checkedStatefulOracle_accepts crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
      inhabitedStatefulQueries he
  · cases inhabited_checked_stateful_multi_sign_extract with
    | inl col => exact .inl ⟨col⟩
    | inr wots => exact .inr ⟨wots⟩

/-- The latch invariant has a concrete occupied state, not just an empty log. -/
theorem witness_occupied_epoch_latch : ∃ st : EpochLatchState, st.WellFormed := by
  refine ⟨⟨1, some (0, [], ⟨[], 0, 0, [], []⟩)⟩, ?_⟩
  intro ep msg sig h
  change some (0, [], (⟨[], 0, 0, [], []⟩ : PqHashSig)) = some (ep, msg, sig) at h
  have he := congrArg (fun x => x.1) (Option.some.inj h)
  change 0 = ep at he
  change ep < 1
  omega

/-- The invariant and an actual successful replay share one assignment. -/
theorem witness_occupied_epoch_latch_step :
    ∃ (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
      (st : EpochLatchState) (sig : PqHashSig),
      st.WellFormed ∧ epochLatchSign suite params sk [] 0 st 0 [] = some (st, sig) := by
  refine ⟨crumbToySuite, inhabitedStatefulParams, ⟨[], [], []⟩,
    ⟨1, some (0, [], ⟨[], 0, 0, [], []⟩)⟩, ⟨[], 0, 0, [], []⟩, ?_, ?_⟩
  · intro ep msg sig h
    have he := congrArg (fun x => x.1) (Option.some.inj h)
    change 0 = ep at he
    change ep < 1
    omega
  · exact stateful_jorts_crash_retry_idempotent _ _ _ _ _ _ _ _

/-- Equivocation rejection with the occupied latch explicit in the theorem statement. -/
theorem tooth_occupied_latch_rejects_equivocation
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind ep : Nat)
    (msg msg' : List UInt8) (sig : PqHashSig) (hDiff : msg' ≠ msg) :
    epochLatchSign suite params sk optRand maxGrind
      ⟨ep + 1, some (ep, msg, sig)⟩ ep msg' = none :=
  stateful_jorts_equivocation_rejected suite params sk optRand maxGrind ep msg msg' sig hDiff

end Qsag
end

#tooth_pair Qsag.stateful_jorts_crash_retry_idempotent vs Qsag.tooth_occupied_latch_rejects_equivocation
#verify_inhabited Qsag.epochLatchSign_preserves_wellFormed Qsag.witness_occupied_epoch_latch_step
