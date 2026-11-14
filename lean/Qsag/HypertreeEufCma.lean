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
* Extracted break events and `hitCount` union bounds are explicit witness and finite-coin reductions,
  not concrete hash-suite probability bounds.
-/

public import Qsag.Goldilocks
public import Qsag.Keccak
public import Qsag.Poseidon2
public import Qsag.UcGames
public import Qsag.HashSigs
import all Qsag.HashSigs

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
                apply Nat.div_lt_of_lt_mul
                rw [← Nat.pow_add]
                have hMulEq : params.subtreeHeight + (r0 :: rs).length * params.subtreeHeight =
                    (lsig :: r0 :: rs).length * params.subtreeHeight := by
                  simp only [List.length_cons]
                  rw [Nat.succ_mul (rs.length + 1), Nat.add_comm]
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
