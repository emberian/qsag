module
public import Qsag.Constructive
public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.UcGames
public import Qsag.ConcreteSecurityBudget
import all Qsag.ConcreteSecurityBudget
public import Qsag.AffineProximityGaps
import all Qsag.AffineProximityGaps
public import Qsag.CodingTheory.Cwyz26AffineGap

public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-!
# Multi-Round QROM Fiat–Shamir & `[CWYZ26]` Affine WHIR IOP Composition

Constructive Lean 4.35 development for the multi-round QROM Fiat–Shamir reduction
(`ASSURANCE.md:30`, `PROJECT.md:43`):

1. **Round-by-Round (`RbrStateFunction`) & Adaptive State-Restoration Soundness
   (`rbr_implies_state_restoration_soundness`)**:
   `k`-round public-coin IOPs (`PublicCoinIop`), round-by-round state functions with a
   proposition-valued liveness predicate and pigeonhole flip bounds (`RbrStateFunction`; the
   Boolean counting form is `RbrStateFunction.ofBoolState`), and `T`-step adaptive rewinding /
   state-restoration attack trees (`SrScheduleTree`): the fraction of challenge schedules reaching
   an accepting full transcript is at most `∑_{t=1..T} (badCard(r_t) / challengeCard(r_t))`.

2. **State functions instantiated from `Qsag.AffineProximityGaps` (§1.1)**:
   `affineMcaRbrOf` (flip bound from any mutual correlated agreement bound `AffineMcaBound`;
   `hem_johnson_fold_state_restoration_of_mca` instantiates it at the deployed Johnson-radius
   rows, where the bound is a hypothesis), `affineMcaRbr` (the same with the bound proved from
   `welch_berlekamp_affine_proximity_gap`) and
   `affineCommittedRbr` (flip bound proved from `committed_polynomial_pair_bad_lines_le_choose2`),
   composed into `affine_mca_state_restoration_soundness` and
   `affine_committed_pair_state_restoration_soundness` for statements without correlated
   agreement, over any constructive field and at `QuarticGoldilocks`.

3. **`Hem` v6 transcript model (`hemAffineWhirStateFunction`, `verifyHemAffineWhir`)**:
   asymmetric cascade, per-stage affine fold with the `affine.rs` five-wire dual bridge
   (`hemBridgeFoldClaim`, verifier-computed `hemKernelFold`, `hem_bridge_fold_claim_eq_dot`),
   dual OOD pinning (`dual_ood_list_collision_bound`), and coset-query survival
   (`far_codeword_coset_queries_survive_bound`). The statement language `HemStatementValid` is
   an existential over polynomial witnesses and does not depend on any candidate list. The
   model carries doomed-init, accept-implies-live and honest completeness; its stage liveness
   is witnessed by decoded polynomials listed in the transcript and it is NOT packaged as an
   `RbrStateFunction`: `tooth_hem_zero_cascade_weights_accept_false_claim` exhibits a flip, and
   a flip bound at the deployed Johnson radius needs `[CWYZ26]` Theorem 4.8, which is checked
   here only through its finite side conditions (`checkWhirAffineWitness`).

4. **Multi-round Fiat–Shamir QROM reduction via unitary Measure-and-Reprogram (§3)**:
   the exact `(2 * Q + 1)`-branch telescoping identity over `QVec` / `GaussInt`, the projected
   step `qrom_unitary_measure_reprogram_rbr_step_projected` (output register ≠ query point), its
   oracle-dependent form `qrom_adaptive_oracle_dependent_rbr_step`, and the `k`-round union
   `qrom_multiRound_measure_reprogram_union` (`(2 Q + 1)^2 ∑_r badCard_r / 2^w`, for a FIXED
   background oracle), with uniform-oracle resampling and the averaged round bound
   `qrom_uniform_oracle_round_bound`. The numerical budget `multiRoundFsQrom_budget_bound`
   instantiates round AND query bounds derived from the deployed
   `whirAffineStageWitnesses 24 true` rows, charges query rounds under Fiat–Shamir search with
   no proof-of-work credit, and charges commitment extraction with a collision term
   (`qromMerkleOnlineExtractBound`; classical binding is `merkle_collision_or_unique_opening`,
   the quantum extraction reduction is not mechanized). The collision term limits the budget
   to `Q + 1 ≤ 2^40`. The budget is arithmetic: it is not yet connected to verifier acceptance
   (item 3).

5. **Fiat–Shamir transcript-ordering `#tooth` (`tooth_unabsorbed_shifted_claim_breaks_rbr`)**:
   squeezing `(α, β)` before absorbing the shifted functional claim admits a forgery on every
   `β ≠ 0`, whereas absorb-before-squeeze caps flips at `≤ 1 / |S|`.
-/


/-! ## §1. Round-by-Round Soundness (`RbrStateFunction`) & Adaptive State-Restoration Game -/

/-- Constructive boolean list-membership test (`0` classical typeclass search). -/
def listHasElem {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => if x = y then true else listHasElem x ys

private theorem listHasElem_eq_true_iff {α : Type} [DecidableEq α] (x : α) :
    ∀ (ys : List α), listHasElem x ys = true ↔ x ∈ ys
  | [] => by simp [listHasElem]
  | y :: ys => by
    simp only [listHasElem, List.mem_cons]
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy, listHasElem_eq_true_iff x ys]

/-- Constructive enumeration of `{i : Fin n | e i = true}` in increasing order. -/
def finFilterList : (n : Nat) → (Fin n → Bool) → List (Fin n)
  | 0, _ => []
  | n + 1, e =>
    (if e ⟨0, Nat.zero_lt_succ n⟩ = true then [(⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))] else []) ++
    (finFilterList n (fun i => e ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)).map
      (fun i => (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)))

theorem finFilterList_sound :
    ∀ (n : Nat) (e : Fin n → Bool) (i : Fin n), i ∈ finFilterList n e → e i = true
  | 0, _, i, _ => Fin.elim0 i
  | n + 1, e, i, hi => by
    have ih := finFilterList_sound n (fun j => e ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
    rw [finFilterList, List.mem_append] at hi
    rcases hi with h | h
    · cases h0 : e ⟨0, Nat.zero_lt_succ n⟩
      · rw [h0] at h
        simp at h
      · rw [h0] at h
        simp only [↓reduceIte, List.mem_singleton] at h
        rw [h]
        exact h0
    · rcases List.mem_map.mp h with ⟨j, hj, rfl⟩
      exact ih j hj

theorem finFilterList_complete :
    ∀ (n : Nat) (e : Fin n → Bool) (i : Fin n), e i = true → i ∈ finFilterList n e
  | 0, _, i, _ => Fin.elim0 i
  | n + 1, e, ⟨0, h0⟩, hi => by
    rw [finFilterList, List.mem_append]
    left
    have hi' : e ⟨0, Nat.zero_lt_succ n⟩ = true := hi
    rw [hi']
    exact .head _
  | n + 1, e, ⟨k + 1, hk⟩, hi => by
    rw [finFilterList, List.mem_append]
    right
    exact List.mem_map.mpr ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩,
      finFilterList_complete n (fun j => e ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        ⟨k, Nat.lt_of_succ_lt_succ hk⟩ hi, rfl⟩

theorem finFilterList_nodup : ∀ (n : Nat) (e : Fin n → Bool), (finFilterList n e).Nodup
  | 0, _ => List.Pairwise.nil
  | n + 1, e => by
    have ih := finFilterList_nodup n (fun j => e ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
    have hTail : ((finFilterList n (fun i => e ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)).map
        (fun i => (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)))).Nodup :=
      List.Pairwise.map _
        (fun a b hab hEq => hab (Fin.ext (Nat.succ.inj (congrArg Fin.val hEq)))) ih
    rw [finFilterList]
    cases e ⟨0, Nat.zero_lt_succ n⟩
    · exact hTail
    · refine List.pairwise_cons.mpr ⟨?_, hTail⟩
      intro a ha hEq
      rcases List.mem_map.mp ha with ⟨j, _, rfl⟩
      exact Nat.succ_ne_zero j.1 (congrArg Fin.val hEq).symm

theorem finFilterList_length : ∀ (n : Nat) (e : Fin n → Bool),
    (finFilterList n e).length = qsum n (fun i => if e i = true then 1 else 0)
  | 0, _ => rfl
  | n + 1, e => by
    have ih := finFilterList_length n (fun j => e ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
    rw [finFilterList, List.length_append, List.length_map, ih]
    show _ = (if e ⟨0, Nat.zero_lt_succ n⟩ = true then 1 else 0) +
      qsum n (fun i => if e ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = true then 1 else 0)
    cases e ⟨0, Nat.zero_lt_succ n⟩ <;> rfl

/-- `k`-round public-coin Interactive Oracle Proof (`PublicCoinIop`) with explicit prover messages
    `m_r : Msg`, round-`r` verifier challenge cardinalities `challengeCard r > 0`, language
    membership specification `inLang`, and deterministic full-transcript verifier `verify`. -/
structure PublicCoinIop (Stmt Msg : Type) (numRounds : Nat) where
  challengeCard : Fin numRounds → Nat
  h_chal_pos : ∀ r : Fin numRounds, 0 < challengeCard r
  inLang : Stmt → Prop
  verify : Stmt → List (Msg × Nat) → Bool

/-- Round-by-Round (`RBR`) soundness state function for a `numRounds`-round `PublicCoinIop`
    (`[CCH+19]`, `[CMS19]`, `[DFM20]`), with a PROPOSITION-valued liveness predicate `Live`
    (`¬ Live` = doomed). Liveness of a prefix is typically an existential over decoded codewords
    (`∃ P` close to the committed oracle), which is not computable over an abstract field, so the
    per-round flip bound is stated as a pigeonhole bound: every duplicate-free list of challenges
    that are not-not live has length at most `badCard r`. No decidability of `Live` is needed
    anywhere (`0` classical choice); a Boolean state function is the special case
    `RbrStateFunction.ofBoolState`. -/
structure RbrStateFunction {Stmt Msg : Type} {numRounds : Nat}
    (iop : PublicCoinIop Stmt Msg numRounds) where
  Live : Stmt → List (Msg × Nat) → Prop
  badCard : Fin numRounds → Nat
  doomed_init : ∀ x : Stmt, ¬ iop.inLang x → ¬ Live x []
  accept_implies_live :
    ∀ (x : Stmt) (tr : List (Msg × Nat)),
      tr.length = numRounds → iop.verify x tr = true → Live x tr
  round_flip_bound :
    ∀ (x : Stmt) (r : Fin numRounds) (pref : List (Msg × Nat)) (m : Msg),
      pref.length = r.1 →
      ¬ Live x pref →
      ∀ (L : List (Fin (iop.challengeCard r))), L.Nodup →
        (∀ ch ∈ L, ¬¬ Live x (pref ++ [(m, ch.1)])) →
        L.length ≤ badCard r

/-- A Boolean state function with the counting flip bound
    `#{ch | state (pref ++ [(m, ch)]) = true} ≤ badCard r` is an `RbrStateFunction`. -/
def RbrStateFunction.ofBoolState {Stmt Msg : Type} {numRounds : Nat}
    (iop : PublicCoinIop Stmt Msg numRounds)
    (state : Stmt → List (Msg × Nat) → Bool)
    (badCard : Fin numRounds → Nat)
    (hInit : ∀ x : Stmt, ¬ iop.inLang x → state x [] = false)
    (hAccept : ∀ (x : Stmt) (tr : List (Msg × Nat)),
      tr.length = numRounds → iop.verify x tr = true → state x tr = true)
    (hFlip : ∀ (x : Stmt) (r : Fin numRounds) (pref : List (Msg × Nat)) (m : Msg),
      pref.length = r.1 →
      state x pref = false →
      qsum (iop.challengeCard r)
        (fun ch => if state x (pref ++ [(m, ch.1)]) = true then 1 else 0) ≤ badCard r) :
    RbrStateFunction iop where
  Live := fun x tr => state x tr = true
  badCard := badCard
  doomed_init := fun x h hLive => by
    rw [hInit x h] at hLive
    exact Bool.noConfusion hLive
  accept_implies_live := hAccept
  round_flip_bound := fun x r pref m hLen hDoomed L hNd hL => by
    have hFalse : state x pref = false := by
      cases h : state x pref
      · rfl
      · exact absurd h hDoomed
    have hSub : ∀ ch ∈ L, ch ∈ finFilterList (iop.challengeCard r)
        (fun ch => state x (pref ++ [(m, ch.1)])) :=
      fun ch hch => finFilterList_complete _ _ ch (Decidable.of_not_not (hL ch hch))
    have h1 := nodup_length_le_of_subset hNd hSub
    rw [finFilterList_length] at h1
    exact Nat.le_trans h1 (hFlip x r pref m hLen hFalse)

/-- Adaptive `T`-step State-Restoration / Rewinding attack tree indexed by the round-rewind
    schedule `sched : List (Fin numRounds)` (`T = sched.length`). At each step for round `r`,
    the adaptive attacker inspects the entire history `hist` of visited transcript prefixes,
    chooses a visited prefix `pref` of length `r.1` and a prover message `m`, receives a uniform
    verifier challenge `ch : Fin (iop.challengeCard r)`, appends `pref ++ [(m, ch.1)]` to `hist`,
    and branches adaptively on `ch`. -/
inductive SrScheduleTree {Stmt Msg : Type} {numRounds : Nat}
    (iop : PublicCoinIop Stmt Msg numRounds) : List (Fin numRounds) → Type where
  | done (extract : List (List (Msg × Nat)) → List (Msg × Nat)) :
      SrScheduleTree iop []
  | rewind {r : Fin numRounds} {rest : List (Fin numRounds)}
      (selectPref : List (List (Msg × Nat)) → List (Msg × Nat))
      (chooseMsg : List (List (Msg × Nat)) → Msg)
      (next : Fin (iop.challengeCard r) → SrScheduleTree iop rest) :
      SrScheduleTree iop (r :: rest)

/-- Total number of challenge-schedule realizations `∏_{t=1..T} challengeCard(r_t)`. -/
@[expose] def srScheduleCard {Stmt Msg : Type} {numRounds : Nat}
    (iop : PublicCoinIop Stmt Msg numRounds) : List (Fin numRounds) → Nat
  | [] => 1
  | r :: rest => iop.challengeCard r * srScheduleCard iop rest

theorem srScheduleCard_pos {Stmt Msg : Type} {numRounds : Nat}
    (iop : PublicCoinIop Stmt Msg numRounds) :
    ∀ (sched : List (Fin numRounds)), 0 < srScheduleCard iop sched
  | [] => Nat.zero_lt_one
  | r :: rest => Nat.mul_pos (iop.h_chal_pos r) (srScheduleCard_pos iop rest)

/-- Exact count of challenge schedules reaching an accepting full transcript in `hist`. -/
def srAcceptCount {Stmt Msg : Type} [DecidableEq Msg] {numRounds : Nat}
    (iop : PublicCoinIop Stmt Msg numRounds) :
    {sched : List (Fin numRounds)} →
    SrScheduleTree iop sched → Stmt → List (List (Msg × Nat)) → Nat
  | [], .done extract, x, hist =>
    let tr := extract hist
    if (listHasElem tr hist && decide (tr.length = numRounds) && iop.verify x tr) = true then 1 else 0
  | r :: _, .rewind selectPref chooseMsg next, x, hist =>
    let pref := selectPref hist
    let m := chooseMsg hist
    let validStep := listHasElem pref hist && decide (pref.length = r.1)
    qsum (iop.challengeCard r) (fun ch =>
      let hist' := if validStep = true then (pref ++ [(m, ch.1)]) :: hist else hist
      srAcceptCount iop (next ch) x hist')

/-- Exact rational acceptance probability of `tree` starting from initial history `[[]]`. -/
@[expose] def srTreeAcceptProb {Stmt Msg : Type} [DecidableEq Msg] {numRounds : Nat}
    {sched : List (Fin numRounds)}
    (iop : PublicCoinIop Stmt Msg numRounds)
    (tree : SrScheduleTree iop sched) (x : Stmt) : RatBound :=
  ⟨srAcceptCount iop tree x [[]], srScheduleCard iop sched, srScheduleCard_pos iop sched⟩

/-- Additive state-restoration error bound `∑_{t=1..T} (badCard(r_t) / challengeCard(r_t))`. -/
@[expose] def srScheduleErrorSum {Stmt Msg : Type} {numRounds : Nat}
    {iop : PublicCoinIop Stmt Msg numRounds}
    (rbr : RbrStateFunction iop) (sched : List (Fin numRounds)) : RatBound :=
  RatBound.sumList (sched.map (fun r => ⟨rbr.badCard r, iop.challengeCard r, iop.h_chal_pos r⟩))

private theorem srAcceptCount_le_card {Stmt Msg : Type} [DecidableEq Msg] {numRounds : Nat}
    (iop : PublicCoinIop Stmt Msg numRounds) :
    ∀ {sched : List (Fin numRounds)} (tree : SrScheduleTree iop sched)
      (x : Stmt) (hist : List (List (Msg × Nat))),
      srAcceptCount iop tree x hist ≤ srScheduleCard iop sched
  | [], .done extract, x, hist => by
    simp only [srAcceptCount, srScheduleCard]
    split <;> omega
  | r :: rest, .rewind selectPref chooseMsg next, x, hist => by
    simp only [srAcceptCount, srScheduleCard]
    have hEach :
        qsum (iop.challengeCard r) (fun ch =>
          srAcceptCount iop (next ch) x
            (if (listHasElem (selectPref hist) hist && decide ((selectPref hist).length = r.1)) = true
             then (selectPref hist ++ [(chooseMsg hist, ch.1)]) :: hist else hist)) ≤
        qsum (iop.challengeCard r) (fun _ => srScheduleCard iop rest) := by
      apply qsum_le_qsum
      intro ch
      exact srAcceptCount_le_card iop (next ch) x _
    rw [qsum_const] at hEach
    exact hEach

private theorem nat_sr_rhs_invalid (C num RestCard : Nat) :
    C * (C * (num * RestCard)) = (num * C) * (C * RestCard) := by
  rw [Nat.mul_left_comm C num RestCard,
      ← Nat.mul_assoc C num (C * RestCard),
      Nat.mul_comm C num]

private theorem nat_sr_rhs_valid (C bad den num RestCard : Nat) :
    C * (bad * (RestCard * den) + C * (num * RestCard)) =
      (bad * den + num * C) * (C * RestCard) := by
  rw [Nat.left_distrib, Nat.right_distrib, nat_sr_rhs_invalid C num RestCard]
  congr 1
  rw [Nat.mul_left_comm C bad (RestCard * den),
      ← Nat.mul_assoc C RestCard den,
      Nat.mul_comm (C * RestCard) den,
      ← Nat.mul_assoc bad den (C * RestCard)]

private theorem srAcceptCount_le_of_doomed_hist {Stmt Msg : Type} [DecidableEq Msg] {numRounds : Nat}
    {iop : PublicCoinIop Stmt Msg numRounds}
    (rbr : RbrStateFunction iop) (x : Stmt) :
    ∀ (sched : List (Fin numRounds)) (tree : SrScheduleTree iop sched)
      (hist : List (List (Msg × Nat))),
      (∀ p ∈ hist, ¬ rbr.Live x p) →
      RatBound.le
        ⟨srAcceptCount iop tree x hist, srScheduleCard iop sched, srScheduleCard_pos iop sched⟩
        (srScheduleErrorSum rbr sched)
  | [], .done extract, hist, hDoomed => by
    unfold RatBound.le srScheduleErrorSum RatBound.sumList RatBound.zero
    dsimp only [List.map, srAcceptCount, srScheduleCard]
    let tr := extract hist
    cases hAcc : (listHasElem tr hist && decide (tr.length = numRounds) && iop.verify x tr)
    · simp
    · exfalso
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hAcc
      rcases hAcc with ⟨⟨hElem, hLen⟩, hVer⟩
      have hMem : tr ∈ hist := (listHasElem_eq_true_iff tr hist).mp hElem
      exact hDoomed tr hMem (rbr.accept_implies_live x tr hLen hVer)
  | r :: rest, .rewind selectPref chooseMsg next, hist, hDoomed => by
    let C := iop.challengeCard r
    let RestCard := srScheduleCard iop rest
    let RestSum := srScheduleErrorSum rbr rest
    let pref := selectPref hist
    let m := chooseMsg hist
    let validStep := listHasElem pref hist && decide (pref.length = r.1)
    unfold srScheduleErrorSum
    simp only [List.map, RatBound.sumList]
    change RatBound.le
      ⟨srAcceptCount iop (.rewind selectPref chooseMsg next) x hist, C * RestCard, _⟩
      (RatBound.add ⟨rbr.badCard r, C, iop.h_chal_pos r⟩ RestSum)
    unfold RatBound.le RatBound.add
    change (qsum C fun ch =>
        srAcceptCount iop (next ch) x
          (if validStep = true then (pref ++ [(m, ch.1)]) :: hist else hist)) *
        (C * RestSum.den) ≤
      (rbr.badCard r * RestSum.den + RestSum.num * C) * (C * RestCard)
    cases hVal : validStep
    · have hEach :
          qsum C (fun ch =>
            srAcceptCount iop (next ch) x (if false = true then (pref ++ [(m, ch.1)]) :: hist else hist) *
              RestSum.den) ≤
          qsum C (fun _ => RestSum.num * RestCard) := by
        apply qsum_le_qsum
        intro ch
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact srAcceptCount_le_of_doomed_hist rbr x rest (next ch) hist hDoomed
      rw [qsum_mul_right, qsum_const] at hEach
      have hMulC := Nat.mul_le_mul_left C hEach
      have hL : C * (qsum C (fun ch =>
          srAcceptCount iop (next ch) x (if false = true then (pref ++ [(m, ch.1)]) :: hist else hist)) *
            RestSum.den) =
          qsum C (fun ch =>
            srAcceptCount iop (next ch) x (if false = true then (pref ++ [(m, ch.1)]) :: hist else hist)) *
            (C * RestSum.den) := by
        rw [← Nat.mul_assoc, Nat.mul_comm C, Nat.mul_assoc]
      have hR : C * (C * (RestSum.num * RestCard)) ≤
          (rbr.badCard r * RestSum.den + RestSum.num * C) * (C * RestCard) := by
        rw [nat_sr_rhs_invalid C RestSum.num RestCard]
        exact Nat.mul_le_mul_right (C * RestCard) (Nat.le_add_left _ _)
      rw [hL] at hMulC
      exact Nat.le_trans hMulC hR
    · have hValProps : listHasElem pref hist = true ∧ pref.length = r.1 := by
        dsimp [validStep] at hVal
        simpa [Bool.and_eq_true, decide_eq_true_eq] using hVal
      have hPrefMem : pref ∈ hist := (listHasElem_eq_true_iff pref hist).mp hValProps.1
      have hPrefDoomed : ¬ rbr.Live x pref := hDoomed pref hPrefMem
      -- Decidable set of challenges on which the inductive bound FAILS; each is not-not live.
      let e : Fin C → Bool := fun ch =>
        decide (RestSum.num * RestCard <
          srAcceptCount iop (next ch) x ((pref ++ [(m, ch.1)]) :: hist) * RestSum.den)
      have hENotNot : ∀ ch : Fin C, e ch = true → ¬¬ rbr.Live x (pref ++ [(m, ch.1)]) := by
        intro ch hch hNotLive
        have hNextDoomed : ∀ p ∈ (pref ++ [(m, ch.1)]) :: hist, ¬ rbr.Live x p := by
          intro p hp
          rcases List.mem_cons.mp hp with hEq | hp'
          · rw [hEq]; exact hNotLive
          · exact hDoomed p hp'
        have ih := srAcceptCount_le_of_doomed_hist rbr x rest (next ch) _ hNextDoomed
        have hlt : RestSum.num * RestCard <
            srAcceptCount iop (next ch) x ((pref ++ [(m, ch.1)]) :: hist) * RestSum.den :=
          of_decide_eq_true hch
        exact Nat.not_le_of_gt hlt ih
      have hFlipBound : qsum C (fun ch => if e ch = true then 1 else 0) ≤ rbr.badCard r := by
        rw [← finFilterList_length C e]
        exact rbr.round_flip_bound x r pref m hValProps.2 hPrefDoomed (finFilterList C e)
          (finFilterList_nodup C e)
          (fun ch hch => hENotNot ch (finFilterList_sound C e ch hch))
      have hPoint :
          qsum C (fun ch =>
            srAcceptCount iop (next ch) x (if true = true then (pref ++ [(m, ch.1)]) :: hist else hist) *
              RestSum.den) ≤
          qsum C (fun ch =>
            (if e ch = true then 1 else 0) * (RestCard * RestSum.den) +
              RestSum.num * RestCard) := by
        apply qsum_le_qsum
        intro ch
        simp only [↓reduceIte]
        cases hE : e ch
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
          have hNot : ¬ (RestSum.num * RestCard <
              srAcceptCount iop (next ch) x ((pref ++ [(m, ch.1)]) :: hist) * RestSum.den) :=
            of_decide_eq_false hE
          exact Nat.le_of_not_lt hNot
        · simp only [↓reduceIte, Nat.one_mul]
          have hCard := srAcceptCount_le_card iop (next ch) x ((pref ++ [(m, ch.1)]) :: hist)
          exact Nat.le_trans (Nat.mul_le_mul_right RestSum.den hCard) (Nat.le_add_right _ _)
      rw [qsum_mul_right, qsum_add, qsum_mul_right, qsum_const] at hPoint
      have hBadMul := Nat.mul_le_mul_right (RestCard * RestSum.den) hFlipBound
      have hCombined :
          qsum C (fun ch =>
            srAcceptCount iop (next ch) x (if true = true then (pref ++ [(m, ch.1)]) :: hist else hist)) *
            RestSum.den ≤
          rbr.badCard r * (RestCard * RestSum.den) + C * (RestSum.num * RestCard) :=
        Nat.le_trans hPoint (Nat.add_le_add_right hBadMul _)
      have hMulC := Nat.mul_le_mul_left C hCombined
      have hL : C * (qsum C (fun ch =>
          srAcceptCount iop (next ch) x (if true = true then (pref ++ [(m, ch.1)]) :: hist else hist)) *
            RestSum.den) =
          qsum C (fun ch =>
            srAcceptCount iop (next ch) x (if true = true then (pref ++ [(m, ch.1)]) :: hist else hist)) *
            (C * RestSum.den) := by
        rw [← Nat.mul_assoc, Nat.mul_comm C, Nat.mul_assoc]
      rw [hL, nat_sr_rhs_valid C (rbr.badCard r) RestSum.den RestSum.num RestCard] at hMulC
      exact hMulC

/-- **State-Restoration Soundness Theorem (`rbr_implies_state_restoration_soundness`)**:
    For ANY `k`-round `PublicCoinIop`, ANY `RbrStateFunction` `rbr` (proposition-valued liveness,
    pigeonhole flip bounds), ANY false statement `x` (`¬ iop.inLang x`), ANY `T`-step rewind
    schedule `sched = [r_1, ..., r_T]`, and ANY adaptive state-restoration / rewinding tree
    `tree : SrScheduleTree iop sched`, the exact rational probability of reaching an accepting
    full transcript is bounded by `∑_{t=1..T} (badCard(r_t) / challengeCard(r_t))`! -/
theorem rbr_implies_state_restoration_soundness
    {Stmt Msg : Type} [DecidableEq Msg] {numRounds : Nat}
    {iop : PublicCoinIop Stmt Msg numRounds}
    (rbr : RbrStateFunction iop)
    (x : Stmt) (hNotInLang : ¬ iop.inLang x)
    (sched : List (Fin numRounds))
    (tree : SrScheduleTree iop sched) :
    RatBound.le (srTreeAcceptProb iop tree x) (srScheduleErrorSum rbr sched) := by
  have hInit : ∀ p ∈ ([[]] : List (List (Msg × Nat))), ¬ rbr.Live x p := by
    intro p hp
    rw [List.mem_singleton.mp hp]
    exact rbr.doomed_init x hNotInLang
  exact srAcceptCount_le_of_doomed_hist rbr x sched tree [[]] hInit


/-! ### §1.1 RBR State Functions Instantiated From `Qsag.AffineProximityGaps`

Two concrete `RbrStateFunction`s for one `[CWYZ26]` affine fold `w_{α,β}(z) = f(z) + (α + β z) g(z)`
over ANY constructive field, whose `round_flip_bound` fields are PROVED from
`welch_berlekamp_affine_proximity_gap` and `committed_polynomial_pair_bad_lines_le_choose2`
(no restated or assumed round bound), then composed with
`rbr_implies_state_restoration_soundness`. -/

private theorem length_filter_split {α : Type} (p : α → Bool) :
    ∀ l : List α, l.length = (l.filter p).length + (l.filter (fun x => !p x)).length
  | [] => rfl
  | a :: l => by
    have ih := length_filter_split p l
    cases hp : p a <;>
      simp only [List.filter_cons, hp, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] <;> omega

private theorem length_filter_filter_le {α : Type} (p q : α → Bool) :
    ∀ l : List α, ((l.filter q).filter p).length ≤ (l.filter p).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := length_filter_filter_le p q l
    cases hq : q a <;> cases hp : p a <;>
      simp only [List.filter_cons, hq, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
      omega

private theorem length_filter_le_add_filter_and_not {α : Type} (p q : α → Bool) :
    ∀ l : List α,
      (l.filter p).length ≤ (l.filter q).length + (l.filter (fun z => p z && !q z)).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := length_filter_le_add_filter_and_not p q l
    cases hq : q a <;> cases hp : p a <;>
      simp only [List.filter_cons, hq, hp, Bool.not_false, Bool.not_true, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

section AffineWeld
variable {F : Type} [LawfulField F] [DecidableEq F]

/-! #### Uncommitted fold: flip bound from `AffineMcaBound` -/

/-- Two-round affine-fold proximity IOP for the received words `x = (f, g)`:
    round 0 draws `(α, β) ∈ S × S` (the prover's round-0 message is ignored: `f, g` are the
    committed statement); in round 1 the prover answers with a polynomial `P` (the round-1
    challenge is unused). The language is correlated agreement `≥ A - 1`. -/
def affineMcaIop (D S : List F) (hSpos : 0 < S.length) (d A : Nat) :
    PublicCoinIop ((F → F) × (F → F)) (List F) 2 where
  challengeCard := fun _ => (prodPool S).length
  h_chal_pos := fun _ => by
    rw [prodPool_length]
    exact Nat.mul_pos hSpos hSpos
  inLang := fun x => HasCorrelatedAgreement d (A - 1) x.1 x.2 D
  verify := fun x tr =>
    match tr with
    | [(_, c), (P, _)] => affineMcaAccepts D S d A x c P
    | _ => false

/-- Liveness: the statement has correlated agreement, or (after the challenge) SOME response is
    accepted, or (after the response) THE response is accepted. -/
def affineMcaLive (D S : List F) (d A : Nat) (x : (F → F) × (F → F))
    (tr : List (List F × Nat)) : Prop :=
  HasCorrelatedAgreement d (A - 1) x.1 x.2 D ∨
  match tr with
  | [(_, c)] => ∃ P : List F, affineMcaAccepts D S d A x c P = true
  | [(_, c), (P, _)] => affineMcaAccepts D S d A x c P = true
  | _ => False

private theorem affineMca_accept_implies_live (D S : List F) (hSpos : 0 < S.length) (d A : Nat)
    (x : (F → F) × (F → F)) (tr : List (List F × Nat))
    (_hLen : tr.length = 2)
    (hVer : (affineMcaIop D S hSpos d A).verify x tr = true) :
    affineMcaLive D S d A x tr := by
  rcases tr with _ | ⟨⟨m0, c⟩, _ | ⟨⟨P, c1⟩, _ | ⟨hd, tl⟩⟩⟩
  · exact Bool.noConfusion hVer
  · exact Bool.noConfusion hVer
  · exact Or.inr hVer
  · exact Bool.noConfusion hVer

private theorem affineMca_round_flip_bound (D S : List F) (d A bad : Nat)
    (hB : AffineMcaBound D S d A bad)
    (x : (F → F) × (F → F)) (r : Fin 2) (pref : List (List F × Nat)) (m : List F)
    (hLen : pref.length = r.1)
    (hDoomed : ¬ affineMcaLive D S d A x pref)
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hL : ∀ ch ∈ L, ¬¬ affineMcaLive D S d A x (pref ++ [(m, ch.1)])) :
    L.length ≤ (match r.1 with
      | 0 => bad
      | _ => 0) := by
  have hNotCA : ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D := fun h => hDoomed (Or.inl h)
  rcases r with ⟨_ | _ | k, hr⟩
  · have hNil : pref = [] := List.eq_nil_of_length_eq_zero hLen
    subst hNil
    show L.length ≤ bad
    exact hB x hNotCA L hNd
      (fun ch hch hNo => hL ch hch (fun hLive => Or.elim hLive hNotCA hNo))
  · rcases pref with _ | ⟨⟨m0, c⟩, _ | ⟨hd, tl⟩⟩
    · exact absurd hLen (Nat.succ_ne_zero 0).symm
    · show L.length ≤ 0
      rcases L with _ | ⟨ch, rest⟩
      · exact Nat.le_refl 0
      · have hNN := hL ch (.head rest)
        refine absurd ?_ hNN
        intro hLive
        have hLive' : HasCorrelatedAgreement d (A - 1) x.1 x.2 D ∨
            affineMcaAccepts D S d A x c m = true := hLive
        rcases hLive' with h | h
        · exact hNotCA h
        · have hEx : ∃ P : List F, affineMcaAccepts D S d A x c P = true := ⟨m, h⟩
          exact hDoomed (Or.inr hEx)
    · exact absurd (Nat.succ.inj hLen) (Nat.succ_ne_zero _)
  · exact absurd hr (by omega)

/-- **`RbrStateFunction` of the affine-fold proximity IOP from a mutual correlated agreement
    bound**: a statement without correlated agreement `≥ A - 1` turns live on at most `bad` of
    the `|S|^2` challenges `(α, β)`, and never on the response round. The radius enters only
    through the hypothesis `hB`. -/
def affineMcaRbrOf (D S : List F) (hSpos : 0 < S.length) (d A bad : Nat)
    (hB : AffineMcaBound D S d A bad) :
    RbrStateFunction (affineMcaIop D S hSpos d A) where
  Live := affineMcaLive D S d A
  badCard := fun r => match r.1 with
    | 0 => bad
    | _ => 0
  doomed_init := fun _ hNot hLive => Or.elim hLive hNot (fun h => h)
  accept_implies_live := affineMca_accept_implies_live D S hSpos d A
  round_flip_bound := affineMca_round_flip_bound D S d A bad hB

/-- **`RbrStateFunction` of the affine-fold proximity IOP, flip bound PROVED from
    `welch_berlekamp_affine_proximity_gap`**: in the regime `2 |D| + d + 1 < 3 A`, a statement
    without correlated agreement `≥ A - 1` turns live on at most `max(|S|, |D|(|D|-1)/2)` of the
    `|S|^2` challenges `(α, β)`, and never on the response round. -/
def affineMcaRbr (D S : List F) (hSpos : 0 < S.length) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup) (hAD : A ≤ D.length) (hWB : 2 * D.length + d + 1 < 3 * A) :
    RbrStateFunction (affineMcaIop D S hSpos d A) :=
  affineMcaRbrOf D S hSpos d A _ (affineMcaBound_welch_berlekamp D S d A hD hS hAD hWB)

/-- **Fold state-restoration soundness at ANY radius, from a mutual correlated agreement
    bound.** For words `(f, g)` without correlated agreement `≥ A - 1`, any rewind schedule and
    any adaptive rewinding prover, the acceptance probability of the affine-fold proximity IOP
    is at most `∑_t badCard(r_t) / |S|^2` with `badCard 0 = bad`, `badCard 1 = 0`. -/
theorem affine_mca_state_restoration_of_bound
    (D S : List F) (hSpos : 0 < S.length) (d A bad : Nat) (hB : AffineMcaBound D S d A bad)
    (f g : F → F) (hFar : ¬ HasCorrelatedAgreement d (A - 1) f g D)
    (sched : List (Fin 2)) (tree : SrScheduleTree (affineMcaIop D S hSpos d A) sched) :
    RatBound.le (srTreeAcceptProb (affineMcaIop D S hSpos d A) tree (f, g))
      (srScheduleErrorSum (affineMcaRbrOf D S hSpos d A bad hB) sched) ∧
    (affineMcaRbrOf D S hSpos d A bad hB).badCard ⟨0, by decide⟩ = bad ∧
    (affineMcaRbrOf D S hSpos d A bad hB).badCard ⟨1, by decide⟩ = 0 :=
  ⟨rbr_implies_state_restoration_soundness (affineMcaRbrOf D S hSpos d A bad hB)
    (f, g) hFar sched tree, rfl, rfl⟩

/-- **Affine-Fold State-Restoration Soundness (`affine_mca_state_restoration_soundness`)**:
    `rbr_implies_state_restoration_soundness` composed with the flip bound proved from
    `welch_berlekamp_affine_proximity_gap`. For ANY received words `(f, g)` WITHOUT correlated
    agreement `≥ A - 1`, ANY rewind schedule and ANY adaptive rewinding prover, the acceptance
    probability is at most `∑_t badCard(r_t) / |S|^2` with
    `badCard 0 = max(|S|, |D|(|D|-1)/2)` and `badCard 1 = 0`. -/
theorem affine_mca_state_restoration_soundness
    (D S : List F) (hSpos : 0 < S.length) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup) (hAD : A ≤ D.length) (hWB : 2 * D.length + d + 1 < 3 * A)
    (f g : F → F) (hFar : ¬ HasCorrelatedAgreement d (A - 1) f g D)
    (sched : List (Fin 2)) (tree : SrScheduleTree (affineMcaIop D S hSpos d A) sched) :
    RatBound.le (srTreeAcceptProb (affineMcaIop D S hSpos d A) tree (f, g))
      (srScheduleErrorSum (affineMcaRbr D S hSpos d A hD hS hAD hWB) sched) ∧
    (affineMcaRbr D S hSpos d A hD hS hAD hWB).badCard ⟨0, by decide⟩ =
      Nat.max S.length (D.length * (D.length - 1) / 2) ∧
    (affineMcaRbr D S hSpos d A hD hS hAD hWB).badCard ⟨1, by decide⟩ = 0 :=
  ⟨rbr_implies_state_restoration_soundness (affineMcaRbr D S hSpos d A hD hS hAD hWB)
    (f, g) hFar sched tree, rfl, rfl⟩

/-! #### Committed pair: flip bound from `committed_polynomial_pair_bad_lines_le_choose2` -/

/-- Verifier predicate of the committed-pair fold IOP: the prover's message `(F_poly, G_poly)`
    (sent BEFORE the challenge) has the right degrees and its fold
    `F_poly + (α + β X) G_poly` agrees with the fold word on at least `A` points of `D`. -/
def affineCommittedAccepts (D S : List F) (d A : Nat) (x : (F → F) × (F → F)) (c : Nat)
    (FG : List F × List F) : Bool :=
  decide (c < (prodPool S).length) &&
  decide (FG.1.length ≤ d + 1) &&
  decide (FG.2.length ≤ d) &&
  decide (A ≤ (D.filter (fun z =>
    decide (CommRingOps.add (RoundPoly.evalCoeffs FG.1 z)
        (CommRingOps.mul
          (CommRingOps.add ((prodPool S).getD c (CommRingOps.zero, CommRingOps.zero)).1
            (CommRingOps.mul ((prodPool S).getD c (CommRingOps.zero, CommRingOps.zero)).2 z))
          (RoundPoly.evalCoeffs FG.2 z)) =
      CommRingOps.add (x.1 z)
        (CommRingOps.mul
          (CommRingOps.add ((prodPool S).getD c (CommRingOps.zero, CommRingOps.zero)).1
            (CommRingOps.mul ((prodPool S).getD c (CommRingOps.zero, CommRingOps.zero)).2 z))
          (x.2 z))))).length)

/-- One-round committed-pair fold IOP: the prover commits `(F_poly, G_poly)`, then the verifier
    draws `(α, β) ∈ S × S`. The language is correlated agreement `≥ A - 1`. -/
def affineCommittedIop (D S : List F) (hSpos : 0 < S.length) (d A : Nat) :
    PublicCoinIop ((F → F) × (F → F)) (List F × List F) 1 where
  challengeCard := fun _ => (prodPool S).length
  h_chal_pos := fun _ => by
    rw [prodPool_length]
    exact Nat.mul_pos hSpos hSpos
  inLang := fun x => HasCorrelatedAgreement d (A - 1) x.1 x.2 D
  verify := fun x tr =>
    match tr with
    | [(FG, c)] => affineCommittedAccepts D S d A x c FG
    | _ => false

def affineCommittedLive (D S : List F) (d A : Nat) (x : (F → F) × (F → F))
    (tr : List ((List F × List F) × Nat)) : Prop :=
  HasCorrelatedAgreement d (A - 1) x.1 x.2 D ∨
  match tr with
  | [(FG, c)] => affineCommittedAccepts D S d A x c FG = true
  | _ => False

private theorem affineCommitted_accept_implies_live (D S : List F) (hSpos : 0 < S.length)
    (d A : Nat) (x : (F → F) × (F → F)) (tr : List ((List F × List F) × Nat))
    (_hLen : tr.length = 1)
    (hVer : (affineCommittedIop D S hSpos d A).verify x tr = true) :
    affineCommittedLive D S d A x tr := by
  rcases tr with _ | ⟨⟨FG, c⟩, _ | ⟨hd, tl⟩⟩
  · exact Bool.noConfusion hVer
  · exact Or.inr hVer
  · exact Bool.noConfusion hVer

private theorem affineCommitted_round_flip_bound (D S : List F)
    (d A : Nat) (hD : D.Nodup) (hS : S.Nodup)
    (x : (F → F) × (F → F)) (r : Fin 1) (pref : List ((List F × List F) × Nat))
    (m : List F × List F)
    (hLen : pref.length = r.1)
    (hDoomed : ¬ affineCommittedLive D S d A x pref)
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hL : ∀ ch ∈ L, ¬¬ affineCommittedLive D S d A x (pref ++ [(m, ch.1)])) :
    L.length ≤ D.length * (D.length - 1) / 2 := by
  have hNotCA : ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D := fun h => hDoomed (Or.inl h)
  have hNil : pref = [] :=
    List.eq_nil_of_length_eq_zero (hLen.trans (Nat.lt_one_iff.mp r.2))
  subst hNil
  have hAcc : ∀ ch ∈ L, affineCommittedAccepts D S d A x ch.1 m = true := by
    intro ch hch
    apply Decidable.of_not_not
    intro hNo
    exact hL ch hch (fun hLive => Or.elim hLive hNotCA hNo)
  have hSub : ∀ p ∈ L.map (fun ch => (prodPool S).get ch),
      p ∈ (prodPool S).filter (fun p =>
        decide (2 ≤ (D.filter (isAccidentalAgreement m.1 m.2 x.1 x.2 p.1 p.2)).length)) := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨ch, hch, rfl⟩
    have h := hAcc ch hch
    unfold affineCommittedAccepts at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [list_getD_eq_get (prodPool S) _ ch] at h
    rcases h with ⟨⟨⟨_, hF⟩, hG⟩, hAgree⟩
    have hJ : ¬ (A - 1 ≤ (D.filter (fun z =>
        decide (RoundPoly.evalCoeffs m.1 z = x.1 z) &&
        decide (RoundPoly.evalCoeffs m.2 z = x.2 z))).length) :=
      fun hJ => hNotCA ⟨m.1, m.2, hF, hG, hJ⟩
    have hSplit :
        (D.filter (fun z =>
          decide (CommRingOps.add (RoundPoly.evalCoeffs m.1 z)
              (CommRingOps.mul
                (CommRingOps.add ((prodPool S).get ch).1
                  (CommRingOps.mul ((prodPool S).get ch).2 z))
                (RoundPoly.evalCoeffs m.2 z)) =
            CommRingOps.add (x.1 z)
              (CommRingOps.mul
                (CommRingOps.add ((prodPool S).get ch).1
                  (CommRingOps.mul ((prodPool S).get ch).2 z))
                (x.2 z))))).length ≤
        (D.filter (fun z =>
          decide (RoundPoly.evalCoeffs m.1 z = x.1 z) &&
          decide (RoundPoly.evalCoeffs m.2 z = x.2 z))).length +
        (D.filter (isAccidentalAgreement m.1 m.2 x.1 x.2
          ((prodPool S).get ch).1 ((prodPool S).get ch).2)).length :=
      length_filter_le_add_filter_and_not _ _ D
    have hAj := Nat.le_trans hAgree hSplit
    have hTwo : 2 ≤ (D.filter (isAccidentalAgreement m.1 m.2 x.1 x.2
        ((prodPool S).get ch).1 ((prodPool S).get ch).2)).length := by
      omega
    exact List.mem_filter.mpr ⟨list_get_mem (prodPool S) ch, decide_eq_true hTwo⟩
  have h1 := nodup_length_le_of_subset
    (List.Pairwise.map _
      (fun a b hab hEq => hab (nodup_get_inj (prodPool_nodup hS) hEq)) hNd) hSub
  rw [List.length_map] at h1
  exact Nat.le_trans h1
    (committed_polynomial_pair_bad_lines_le_choose2 m.1 m.2 x.1 x.2 D S hD hS)

/-- **`RbrStateFunction` of the committed-pair fold IOP, flip bound PROVED from
    `committed_polynomial_pair_bad_lines_le_choose2`**: for ANY agreement threshold `A` (no
    Welch–Berlekamp radius condition), once `(F_poly, G_poly)` is committed, a statement without
    correlated agreement `≥ A - 1` turns live on at most `|D|(|D|-1)/2` of the `|S|^2`
    challenges (each needs `≥ 2` accidental agreements). -/
def affineCommittedRbr (D S : List F) (hSpos : 0 < S.length) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup) :
    RbrStateFunction (affineCommittedIop D S hSpos d A) where
  Live := affineCommittedLive D S d A
  badCard := fun _ => D.length * (D.length - 1) / 2
  doomed_init := fun _ hNot hLive => Or.elim hLive hNot (fun h => h)
  accept_implies_live := affineCommitted_accept_implies_live D S hSpos d A
  round_flip_bound := affineCommitted_round_flip_bound D S d A hD hS

/-- **Committed-Pair Fold State-Restoration Soundness
    (`affine_committed_pair_state_restoration_soundness`)**: for ANY `T`-step adaptive rewinding
    prover against received words without correlated agreement `≥ A - 1`, acceptance probability
    is at most `T * (|D|(|D|-1)/2) / |S|^2` (as `srScheduleErrorSum`). -/
theorem affine_committed_pair_state_restoration_soundness
    (D S : List F) (hSpos : 0 < S.length) (d A : Nat) (hD : D.Nodup) (hS : S.Nodup)
    (f g : F → F) (hFar : ¬ HasCorrelatedAgreement d (A - 1) f g D)
    (sched : List (Fin 1)) (tree : SrScheduleTree (affineCommittedIop D S hSpos d A) sched) :
    RatBound.le (srTreeAcceptProb (affineCommittedIop D S hSpos d A) tree (f, g))
      (srScheduleErrorSum (affineCommittedRbr D S hSpos d A hD hS) sched) :=
  rbr_implies_state_restoration_soundness (affineCommittedRbr D S hSpos d A hD hS)
    (f, g) hFar sched tree

/-- **Committed-pair IOP: perfect completeness / non-vacuity.** For honest received words
    `f = F_poly`, `g = G_poly` (as evaluation functions) the prover's commitment `(F_poly, G_poly)`
    is accepted on EVERY challenge index, the statement is in the language (for `A - 1 ≤ |D|`),
    and the transcript is live. -/
theorem affineCommitted_honest_accepts
    (D S : List F) (hSpos : 0 < S.length) (d A : Nat) (F_poly G_poly : List F)
    (hF : F_poly.length ≤ d + 1) (hG : G_poly.length ≤ d) (hA : A ≤ D.length)
    (c : Nat) (hc : c < (prodPool S).length) :
    (affineCommittedIop D S hSpos d A).verify
      (fun z => RoundPoly.evalCoeffs F_poly z, fun z => RoundPoly.evalCoeffs G_poly z)
      [((F_poly, G_poly), c)] = true ∧
    (affineCommittedIop D S hSpos d A).inLang
      (fun z => RoundPoly.evalCoeffs F_poly z, fun z => RoundPoly.evalCoeffs G_poly z) := by
  constructor
  · show affineCommittedAccepts D S d A
      (fun z => RoundPoly.evalCoeffs F_poly z, fun z => RoundPoly.evalCoeffs G_poly z) c
      (F_poly, G_poly) = true
    unfold affineCommittedAccepts
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hc, hF⟩, hG⟩, ?_⟩
    have hFilt : D.filter (fun _ => decide True) = D :=
      List.filter_eq_self.mpr (fun _ _ => rfl)
    rw [hFilt]
    exact hA
  · refine ⟨F_poly, G_poly, hF, hG, ?_⟩
    rw [List.filter_eq_self.mpr (fun z _ => by
      simp only [decide_true, Bool.and_self])]
    exact Nat.le_trans (Nat.sub_le A 1) hA

end AffineWeld

/-- **`#tooth`: the deployed stages lie OUTSIDE the Welch–Berlekamp radius.** Every deployed
    `nv = 24` `BciksJohnsonQrom128` row has `3 A ≤ 2 n + d + 1`, so `affineMcaRbr` (hypothesis
    `2 |D| + d + 1 < 3 A`) does not apply at the deployed agreement thresholds; there the
    uncommitted-fold flip bound rests on `[CWYZ26]` Theorem 4.8, whose side conditions alone are
    kernel-checked (`hem_johnson_qrom_witnesses_cover_every_canonical_stage`).
    `affineCommittedRbr` has no radius hypothesis and applies at every `A`. -/
theorem tooth_deployed_rows_exceed_welch_berlekamp_radius :
    ∀ w ∈ whirAffineStageWitnesses 24 true, ¬ (2 * w.n + w.d + 1 < 3 * w.A) := by
  decide +kernel

/-- The two composed theorems at the deployed field `QuarticGoldilocks` (`𝔽_{p^4}`). -/
theorem goldilocksExt4_affine_fold_state_restoration_soundness
    (D S : List QuarticGoldilocks) (hSpos : 0 < S.length) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup)
    (f g : QuarticGoldilocks → QuarticGoldilocks)
    (hFar : ¬ HasCorrelatedAgreement d (A - 1) f g D) :
    (∀ (sched : List (Fin 1)) (tree : SrScheduleTree (affineCommittedIop D S hSpos d A) sched),
      RatBound.le (srTreeAcceptProb (affineCommittedIop D S hSpos d A) tree (f, g))
        (srScheduleErrorSum (affineCommittedRbr D S hSpos d A hD hS) sched)) ∧
    (∀ (hAD : A ≤ D.length) (hWB : 2 * D.length + d + 1 < 3 * A)
       (sched : List (Fin 2)) (tree : SrScheduleTree (affineMcaIop D S hSpos d A) sched),
      RatBound.le (srTreeAcceptProb (affineMcaIop D S hSpos d A) tree (f, g))
        (srScheduleErrorSum (affineMcaRbr D S hSpos d A hD hS hAD hWB) sched)) :=
  ⟨fun sched tree =>
     affine_committed_pair_state_restoration_soundness D S hSpos d A hD hS f g hFar sched tree,
   fun hAD hWB sched tree =>
     (affine_mca_state_restoration_soundness D S hSpos d A hD hS hAD hWB f g hFar sched tree).1⟩


/-- **Deployed Johnson-radius fold rounds, reduced to one proximity-gap statement.** Every
    deployed `BciksJohnsonQrom128` row `w` (`whirAffineStageWitnesses 24 true`) lies outside the
    Welch–Berlekamp regime, so `affineMcaBound_welch_berlekamp` does not apply to it. Given the
    mutual correlated agreement bound at the row's own degree and agreement threshold (the
    conclusion of `[CWYZ26]` Theorem 4.8 for that row, with `bad` exceptional challenges), the
    fold round over a domain of the row's size has state-restoration error at most
    `∑_t badCard(r_t) / |S|^2`. The hypothesis `hB` is a proposition about Reed–Solomon codes; it
    is not proved here beyond the Welch–Berlekamp regime. -/
theorem hem_johnson_fold_state_restoration_of_mca
    (w : WhirAffineWitness) (hw : w ∈ whirAffineStageWitnesses 24 true)
    (D S : List QuarticGoldilocks) (hSpos : 0 < S.length) (hDn : D.length = w.n) (bad : Nat)
    (hB : AffineMcaBound D S w.d w.A bad)
    (f g : QuarticGoldilocks → QuarticGoldilocks)
    (hFar : ¬ HasCorrelatedAgreement w.d (w.A - 1) f g D)
    (sched : List (Fin 2)) (tree : SrScheduleTree (affineMcaIop D S hSpos w.d w.A) sched) :
    ¬ (2 * D.length + w.d + 1 < 3 * w.A) ∧
    RatBound.le (srTreeAcceptProb (affineMcaIop D S hSpos w.d w.A) tree (f, g))
      (srScheduleErrorSum (affineMcaRbrOf D S hSpos w.d w.A bad hB) sched) := by
  refine ⟨?_, (affine_mca_state_restoration_of_bound D S hSpos w.d w.A bad hB f g hFar
    sched tree).1⟩
  rw [hDn]
  exact tooth_deployed_rows_exceed_welch_berlekamp_radius w hw

/-- The mutual correlated agreement bound is inhabited with a nontrivial count: in the
    Welch–Berlekamp regime over `QuarticGoldilocks` it holds with
    `max(|S|, |D|(|D|-1)/2)` exceptional challenges out of `|S|^2`. -/
theorem inhabited_affineMcaBound
    (D S : List QuarticGoldilocks) (d A : Nat) (hD : D.Nodup) (hS : S.Nodup)
    (hAD : A ≤ D.length) (hWB : 2 * D.length + d + 1 < 3 * A) :
    ∃ bad : Nat, bad = Nat.max S.length (D.length * (D.length - 1) / 2) ∧
      AffineMcaBound D S d A bad :=
  ⟨_, rfl, affineMcaBound_welch_berlekamp D S d A hD hS hAD hWB⟩


/-! ## §2. Concrete RBR State Function for `[CWYZ26]` Affine WHIR (`hemAffineWhirStateFunction`) -/

/-! ### §2.1 `QuarticGoldilocks` Polynomial Algebra & 5-Scalar Linear-Functional Bridge -/

/-- Variable-length polynomial coefficient addition over any ring `F`. -/
def polyAddVar {F : Type} [CommRingOps F] : List F → List F → List F
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => CommRingOps.add x y :: polyAddVar xs ys

/-- Variable-length polynomial subtraction `P - Q` over any ring `F`. -/
def polySubVar {F : Type} [CommRingOps F] : List F → List F → List F
  | xs, [] => xs
  | [], y :: ys => CommRingOps.sub CommRingOps.zero y :: polySubVar [] ys
  | x :: xs, y :: ys => CommRingOps.sub x y :: polySubVar xs ys

/-- Scalar multiplication `c * P(X)` over any ring `F`. -/
def polyScaleVar {F : Type} [CommRingOps F] (c : F) : List F → List F :=
  List.map (CommRingOps.mul c)

/-- Monomial shift `X * P(X)` (`0` constant term prepended). -/
def shiftPoly {F : Type} [CommRingOps F] (xs : List F) : List F :=
  CommRingOps.zero :: xs

/-- `[CWYZ26]` §5.1 / `affine.rs:fold_step` equal-degree affine combiner:
    `affineCombine θ α β F G(Y) = G(Y) + (α + β Y) (F(Y) + θ G(Y))`. -/
def affineCombine {F : Type} [CommRingOps F] (θ α β : F) (F_poly G_poly : List F) : List F :=
  let H_comb := polyAddVar F_poly (polyScaleVar θ G_poly)
  polyAddVar G_poly (polyAddVar (polyScaleVar α H_comb) (polyScaleVar β (shiftPoly H_comb)))

theorem polyAddVar_length_le {F : Type} [CommRingOps F] :
    ∀ (xs ys : List F) (b : Nat), xs.length ≤ b → ys.length ≤ b → (polyAddVar xs ys).length ≤ b
  | [], _, _, _, hy => hy
  | _ :: _, [], _, hx, _ => hx
  | _ :: _, _ :: _, 0, hx, _ => by simp at hx
  | _ :: xs, _ :: ys, b + 1, hx, hy => by
    simp only [polyAddVar, List.length_cons] at hx hy ⊢
    exact Nat.succ_le_succ (polyAddVar_length_le xs ys b (Nat.le_of_succ_le_succ hx) (Nat.le_of_succ_le_succ hy))

theorem polySubVar_length_le {F : Type} [CommRingOps F] :
    ∀ (xs ys : List F) (b : Nat), xs.length ≤ b → ys.length ≤ b → (polySubVar xs ys).length ≤ b
  | _, [], _, hx, _ => hx
  | [], _ :: _, 0, _, hy => by simp at hy
  | [], _ :: ys, b + 1, _, hy => by
    simp only [polySubVar, List.length_cons] at hy ⊢
    exact Nat.succ_le_succ (polySubVar_length_le [] ys b (Nat.zero_le b) (Nat.le_of_succ_le_succ hy))
  | _ :: _, _ :: _, 0, hx, _ => by simp at hx
  | _ :: xs, _ :: ys, b + 1, hx, hy => by
    simp only [polySubVar, List.length_cons] at hx hy ⊢
    exact Nat.succ_le_succ (polySubVar_length_le xs ys b (Nat.le_of_succ_le_succ hx) (Nat.le_of_succ_le_succ hy))

theorem evalCoeffs_polyAddVar {F : Type} [LawfulCommRing F] :
    ∀ (xs ys : List F) (z : F),
      RoundPoly.evalCoeffs (polyAddVar xs ys) z =
        CommRingOps.add (RoundPoly.evalCoeffs xs z) (RoundPoly.evalCoeffs ys z)
  | [], ys, z => by
    change RoundPoly.evalCoeffs ys z = CommRingOps.add CommRingOps.zero (RoundPoly.evalCoeffs ys z)
    rw [LawfulCommRing.zero_add]
  | x :: xs, [], z => by
    change RoundPoly.evalCoeffs (x :: xs) z =
      CommRingOps.add (RoundPoly.evalCoeffs (x :: xs) z) CommRingOps.zero
    rw [LawfulCommRing.add_zero]
  | x :: xs, y :: ys, z => by
    simp only [polyAddVar, RoundPoly.evalCoeffs_cons, evalCoeffs_polyAddVar xs ys z]
    rw [LawfulCommRing.left_distrib,
        LawfulCommRing.add_assoc x y _,
        ← LawfulCommRing.add_assoc y (CommRingOps.mul z (RoundPoly.evalCoeffs xs z)) _,
        LawfulCommRing.add_comm y (CommRingOps.mul z (RoundPoly.evalCoeffs xs z)),
        LawfulCommRing.add_assoc (CommRingOps.mul z (RoundPoly.evalCoeffs xs z)) y _,
        ← LawfulCommRing.add_assoc x _ _]

private theorem add_neg_distrib {F : Type} [LawfulCommRing F] (a b : F) :
    CommRingOps.add (CommRingOps.neg a) (CommRingOps.neg b) =
      CommRingOps.neg (CommRingOps.add a b) := by
  have hZero :
      CommRingOps.add (CommRingOps.add a b)
        (CommRingOps.add (CommRingOps.neg a) (CommRingOps.neg b)) = CommRingOps.zero := by
    rw [LawfulCommRing.add_assoc a b _,
        ← LawfulCommRing.add_assoc b (CommRingOps.neg a) _,
        LawfulCommRing.add_comm b (CommRingOps.neg a),
        LawfulCommRing.add_assoc (CommRingOps.neg a) b _,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_zero,
        LawfulCommRing.add_right_neg]
  have hAdd := congrArg (CommRingOps.add (CommRingOps.neg (CommRingOps.add a b))) hZero
  rw [LawfulCommRing.add_zero,
      ← LawfulCommRing.add_assoc (CommRingOps.neg (CommRingOps.add a b)),
      LawfulCommRing.add_left_neg,
      LawfulCommRing.zero_add] at hAdd
  exact hAdd

theorem evalCoeffs_polySubVar {F : Type} [LawfulCommRing F] :
    ∀ (xs ys : List F) (z : F),
      RoundPoly.evalCoeffs (polySubVar xs ys) z =
        CommRingOps.sub (RoundPoly.evalCoeffs xs z) (RoundPoly.evalCoeffs ys z)
  | xs, [], z => by
    change RoundPoly.evalCoeffs xs z = CommRingOps.sub (RoundPoly.evalCoeffs xs z) CommRingOps.zero
    have hNeg0 : CommRingOps.neg (CommRingOps.zero : F) = CommRingOps.zero := by
      have h := LawfulCommRing.add_left_neg (CommRingOps.zero : F)
      rw [LawfulCommRing.add_zero] at h
      exact h
    rw [LawfulCommRing.sub_eq_add_neg, hNeg0, LawfulCommRing.add_zero]
  | [], y :: ys, z => by
    simp only [polySubVar, RoundPoly.evalCoeffs_cons, evalCoeffs_polySubVar [] ys z]
    change CommRingOps.add (CommRingOps.sub CommRingOps.zero y)
        (CommRingOps.mul z (CommRingOps.sub CommRingOps.zero (RoundPoly.evalCoeffs ys z))) =
      CommRingOps.sub CommRingOps.zero
        (CommRingOps.add y (CommRingOps.mul z (RoundPoly.evalCoeffs ys z)))
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.zero_add, LawfulCommRing.zero_add, LawfulCommRing.zero_add,
        LawfulCommRing.mul_neg, add_neg_distrib]
  | x :: xs, y :: ys, z => by
    simp only [polySubVar, RoundPoly.evalCoeffs_cons, evalCoeffs_polySubVar xs ys z]
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.left_distrib, LawfulCommRing.mul_neg, ← add_neg_distrib,
        LawfulCommRing.add_assoc x (CommRingOps.neg y) _,
        ← LawfulCommRing.add_assoc (CommRingOps.neg y) (CommRingOps.mul z (RoundPoly.evalCoeffs xs z)) _,
        LawfulCommRing.add_comm (CommRingOps.neg y) (CommRingOps.mul z (RoundPoly.evalCoeffs xs z)),
        LawfulCommRing.add_assoc (CommRingOps.mul z (RoundPoly.evalCoeffs xs z)) (CommRingOps.neg y) _,
        ← LawfulCommRing.add_assoc x _ _]

theorem evalCoeffs_polyScaleVar {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (xs : List F) (z : F),
      RoundPoly.evalCoeffs (polyScaleVar c xs) z = CommRingOps.mul c (RoundPoly.evalCoeffs xs z)
  | [], _ => (LawfulCommRing.mul_zero c).symm
  | x :: xs, z => by
    simp only [polyScaleVar, List.map_cons, RoundPoly.evalCoeffs_cons]
    change CommRingOps.add (CommRingOps.mul c x)
        (CommRingOps.mul z (RoundPoly.evalCoeffs (polyScaleVar c xs) z)) = _
    rw [evalCoeffs_polyScaleVar c xs z,
        ← LawfulCommRing.mul_assoc z c _,
        LawfulCommRing.mul_comm z c,
        LawfulCommRing.mul_assoc c z _,
        ← LawfulCommRing.left_distrib]

theorem evalCoeffs_shiftPoly {F : Type} [LawfulCommRing F] (xs : List F) (z : F) :
    RoundPoly.evalCoeffs (shiftPoly xs) z = CommRingOps.mul z (RoundPoly.evalCoeffs xs z) := by
  simp only [shiftPoly, RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_add]

theorem ringDot_polyAddVar {F : Type} [LawfulCommRing F] :
    ∀ (xs ys v : List F),
      ringDot (polyAddVar xs ys) v = CommRingOps.add (ringDot xs v) (ringDot ys v)
  | [], _, _ => by simp only [polyAddVar, ringDot, LawfulCommRing.zero_add]
  | _ :: _, [], _ => by simp only [polyAddVar, ringDot, LawfulCommRing.add_zero]
  | _ :: _, _ :: _, [] => by simp only [polyAddVar, ringDot, LawfulCommRing.add_zero]
  | x :: xs, y :: ys, k :: ks => by
    simp only [polyAddVar, ringDot, ringDot_polyAddVar xs ys ks]
    rw [LawfulCommRing.right_distrib,
        LawfulCommRing.add_assoc (CommRingOps.mul x k) (CommRingOps.mul y k) _,
        ← LawfulCommRing.add_assoc (CommRingOps.mul y k) (ringDot xs ks) _,
        LawfulCommRing.add_comm (CommRingOps.mul y k) (ringDot xs ks),
        LawfulCommRing.add_assoc (ringDot xs ks) (CommRingOps.mul y k) _,
        ← LawfulCommRing.add_assoc]

theorem ringDot_polyScaleVar {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (xs v : List F),
      ringDot (polyScaleVar c xs) v = CommRingOps.mul c (ringDot xs v)
  | [], _ => by simp only [polyScaleVar, List.map_nil, ringDot, LawfulCommRing.mul_zero]
  | _ :: _, [] => by simp only [polyScaleVar, List.map_cons, ringDot, LawfulCommRing.mul_zero]
  | x :: xs, k :: ks => by
    simp only [polyScaleVar, List.map_cons, ringDot]
    change CommRingOps.add (CommRingOps.mul (CommRingOps.mul c x) k)
        (ringDot (polyScaleVar c xs) ks) = _
    rw [ringDot_polyScaleVar c xs ks, LawfulCommRing.mul_assoc c x k, ← LawfulCommRing.left_distrib]

/-- **5-Scalar Linear-Functional Bridge Identity (`ringDot_affineCombine_eq_bridge`)**:
    Proves constructively over any commutative ring `F` (`QuarticGoldilocks`) that the inner
    product of `affineCombine θ α β F_poly G_poly` against any dual kernel `v` equals
    `γ_G + α * (γ_F + θ * γ_G) + β * (c_F + θ * c_G)`, where `γ_F = ⟨F, v⟩`, `γ_G = ⟨G, v⟩`,
    `c_F = ⟨X · F, v⟩`, and `c_G = ⟨X · G, v⟩` — matching `affine.rs:61`! -/
theorem ringDot_affineCombine_eq_bridge {F : Type} [LawfulCommRing F]
    (θ α β : F) (F_poly G_poly v : List F) :
    ringDot (affineCombine θ α β F_poly G_poly) v =
      CommRingOps.add (ringDot G_poly v)
        (CommRingOps.add
          (CommRingOps.mul α (CommRingOps.add (ringDot F_poly v) (CommRingOps.mul θ (ringDot G_poly v))))
          (CommRingOps.mul β
            (CommRingOps.add (ringDot (shiftPoly F_poly) v)
              (CommRingOps.mul θ (ringDot (shiftPoly G_poly) v))))) := by
  have hShiftAdd : ∀ (a b : List F) (k : List F),
      ringDot (shiftPoly (polyAddVar a b)) k =
        CommRingOps.add (ringDot (shiftPoly a) k) (ringDot (shiftPoly b) k) := by
    intro a b k
    cases k with
    | nil => simp only [shiftPoly, ringDot, LawfulCommRing.add_zero]
    | cons _ ks =>
      simp only [shiftPoly, ringDot, LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
      exact ringDot_polyAddVar a b ks
  have hShiftScale : ∀ (c : F) (a k : List F),
      ringDot (shiftPoly (polyScaleVar c a)) k = CommRingOps.mul c (ringDot (shiftPoly a) k) := by
    intro c a k
    cases k with
    | nil => simp only [shiftPoly, ringDot, LawfulCommRing.mul_zero]
    | cons _ ks =>
      simp only [shiftPoly, ringDot, LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
      exact ringDot_polyScaleVar c a ks
  unfold affineCombine
  dsimp only
  rw [ringDot_polyAddVar, ringDot_polyAddVar,
      ringDot_polyScaleVar, ringDot_polyScaleVar,
      ringDot_polyAddVar, ringDot_polyScaleVar,
      hShiftAdd, hShiftScale]

/-! ### §2.2 Genuine Algebraic Dual OOD List-Collision & Coset Query Survival Bounds -/

/-- Exact unordered pair count `binomial(L, 2) = L * (L - 1) / 2`. -/
def binom2 (L : Nat) : Nat := L * (L - 1) / 2

private theorem binom2_succ (L : Nat) : binom2 (L + 1) = L + binom2 L := by
  unfold binom2
  have hEq : (L + 1) * L = 2 * L + L * (L - 1) := by
    cases L with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_comm (m + 1 + 1) (m + 1)]
      have h1 : (m + 1) * (m + 1 + 1) = (m + 1) * 2 + (m + 1) * m := by
        have hm2 : m + 1 + 1 = 2 + m := by omega
        rw [hm2, Nat.mul_add]
      rw [h1, Nat.mul_comm 2 (m + 1)]
  simp only [Nat.add_sub_cancel, hEq]
  omega

/-- Count of dual OOD challenge pairs `(z₀, z₁) ∈ S × S` on which `P₁` and `P₂` agree at BOTH points. -/
def dualOodPairCollisionCount (S : List QuarticGoldilocks)
    (P₁ P₂ : List QuarticGoldilocks) : Nat :=
  qsum S.length (fun i =>
    qsum S.length (fun j =>
      if decide (RoundPoly.evalCoeffs P₁ (S.get i) = RoundPoly.evalCoeffs P₂ (S.get i)) &&
         decide (RoundPoly.evalCoeffs P₁ (S.get j) = RoundPoly.evalCoeffs P₂ (S.get j))
      then 1 else 0))

private theorem qsum_get_filter_eq {α : Type} (p : α → Bool) :
    ∀ (S : List α),
      qsum S.length (fun i => if p (S.get i) = true then 1 else 0) = (S.filter p).length
  | [] => rfl
  | a :: rest => by
    have hHead : (a :: rest).get ⟨0, Nat.zero_lt_succ rest.length⟩ = a := rfl
    have hTail :
        qsum rest.length (fun i =>
          if p ((a :: rest).get ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = true then 1 else 0) =
        qsum rest.length (fun i => if p (rest.get i) = true then 1 else 0) :=
      qsum_congr (fun _ => rfl)
    change (if p ((a :: rest).get ⟨0, Nat.zero_lt_succ rest.length⟩) = true then 1 else 0) +
        qsum rest.length (fun i =>
          if p ((a :: rest).get ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = true then 1 else 0) =
      ((a :: rest).filter p).length
    rw [hHead, hTail, qsum_get_filter_eq p rest]
    cases hp : p a
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    · simp only [List.filter_cons, hp, ↓reduceIte, List.length_cons, Nat.add_comm 1]

/-- Single-pair algebraic Dual OOD bound: any two distinct degree-`≤ d` polynomials over
    `QuarticGoldilocks` collide on BOTH independent OOD points `(z₀, z₁) ∈ S × S` on at most
    `d ^ 2` pairs! -/
theorem dual_ood_single_pair_le_deg_sq
    (d : Nat) (S : List QuarticGoldilocks) (hNodup : S.Nodup)
    (P₁ P₂ : List QuarticGoldilocks)
    (hDeg₁ : P₁.length ≤ d + 1) (hDeg₂ : P₂.length ≤ d + 1)
    (hDiff : ∃ x₀ : QuarticGoldilocks, RoundPoly.evalCoeffs P₁ x₀ ≠ RoundPoly.evalCoeffs P₂ x₀) :
    dualOodPairCollisionCount S P₁ P₂ ≤ d ^ 2 := by
  let diff := polySubVar P₁ P₂
  have hDiffLen : diff.length ≤ d + 1 :=
    polySubVar_length_le P₁ P₂ (d + 1) hDeg₁ hDeg₂
  rcases hDiff with ⟨x₀, hx₀⟩
  have hDiffNz : ∃ x₀ : QuarticGoldilocks, RoundPoly.evalCoeffs diff x₀ ≠ CommRingOps.zero := by
    refine ⟨x₀, ?_⟩
    rw [evalCoeffs_polySubVar]
    intro hSub0
    have hEq := congrArg (fun u => CommRingOps.add u (RoundPoly.evalCoeffs P₂ x₀)) hSub0
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_left_neg, LawfulCommRing.add_zero, LawfulCommRing.zero_add] at hEq
    exact hx₀ hEq
  have hRootsLe :
      (S.filter (fun r => decide (RoundPoly.evalCoeffs diff r = CommRingOps.zero))).length ≤ d :=
    RoundPoly.roots_nodup_length_le d diff S hNodup hDiffLen hDiffNz
  let pEq : QuarticGoldilocks → Bool :=
    fun r => decide (RoundPoly.evalCoeffs diff r = CommRingOps.zero)
  have hOneCoord :
      qsum S.length (fun i =>
        if decide (RoundPoly.evalCoeffs P₁ (S.get i) = RoundPoly.evalCoeffs P₂ (S.get i)) = true
        then 1 else 0) ≤ d := by
    have hEqFilt :
        qsum S.length (fun i =>
          if decide (RoundPoly.evalCoeffs P₁ (S.get i) = RoundPoly.evalCoeffs P₂ (S.get i)) = true
          then 1 else 0) =
        qsum S.length (fun i => if pEq (S.get i) = true then 1 else 0) := by
      apply qsum_congr; intro i
      have hBoolEq :
          decide (RoundPoly.evalCoeffs P₁ (S.get i) = RoundPoly.evalCoeffs P₂ (S.get i)) =
            pEq (S.get i) := by
        dsimp only [pEq]
        by_cases h : RoundPoly.evalCoeffs P₁ (S.get i) = RoundPoly.evalCoeffs P₂ (S.get i)
        · have hd : RoundPoly.evalCoeffs diff (S.get i) = CommRingOps.zero := by
            rw [evalCoeffs_polySubVar, h, LawfulCommRing.sub_self]
          simp only [h, hd, decide_true]
        · have hd : RoundPoly.evalCoeffs diff (S.get i) ≠ CommRingOps.zero := by
            rw [evalCoeffs_polySubVar]
            intro hSub0
            apply h
            have hA := congrArg (fun u => CommRingOps.add u (RoundPoly.evalCoeffs P₂ (S.get i))) hSub0
            rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
                LawfulCommRing.add_left_neg, LawfulCommRing.add_zero, LawfulCommRing.zero_add] at hA
            exact hA
          simp only [h, hd, decide_false]
      rw [hBoolEq]
    rw [hEqFilt, qsum_get_filter_eq pEq S]
    exact hRootsLe
  unfold dualOodPairCollisionCount
  have hFactor :
      qsum S.length (fun i =>
        qsum S.length (fun j =>
          if (decide (RoundPoly.evalCoeffs P₁ (S.get i) = RoundPoly.evalCoeffs P₂ (S.get i)) &&
              decide (RoundPoly.evalCoeffs P₁ (S.get j) = RoundPoly.evalCoeffs P₂ (S.get j))) = true
          then 1 else 0)) =
      qsum S.length (fun i =>
        (if decide (RoundPoly.evalCoeffs P₁ (S.get i) = RoundPoly.evalCoeffs P₂ (S.get i)) = true
         then 1 else 0) *
        qsum S.length (fun j =>
          if decide (RoundPoly.evalCoeffs P₁ (S.get j) = RoundPoly.evalCoeffs P₂ (S.get j)) = true
          then 1 else 0)) := by
    apply qsum_congr; intro i
    cases hi : decide (RoundPoly.evalCoeffs P₁ (S.get i) = RoundPoly.evalCoeffs P₂ (S.get i))
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, qsum_const, Nat.mul_zero]
    · simp only [Bool.true_and, ↓reduceIte, Nat.one_mul]
  rw [hFactor, qsum_mul_right]
  have hSq : d * d = d ^ 2 := (Nat.pow_two d).symm
  rw [← hSq]
  exact Nat.mul_le_mul hOneCoord hOneCoord

/-- Sum of `dualOodPairCollisionCount` across all unordered pairs `{P_a, P_b}` (`a < b`) in `cands`. -/
def dualOodAllPairsSum (S : List QuarticGoldilocks) :
    List (List QuarticGoldilocks) → Nat
  | [] => 0
  | P :: rest =>
    (rest.foldl (fun acc Q => acc + dualOodPairCollisionCount S P Q) 0) +
      dualOodAllPairsSum S rest

private theorem foldl_pair_collision_le (d : Nat) (S : List QuarticGoldilocks) (hNodup : S.Nodup)
    (P : List QuarticGoldilocks) (hDegP : P.length ≤ d + 1) :
    ∀ (rest : List (List QuarticGoldilocks)) (acc : Nat),
      (∀ Q ∈ rest, Q.length ≤ d + 1 ∧
        ∃ x₀ : QuarticGoldilocks, RoundPoly.evalCoeffs P x₀ ≠ RoundPoly.evalCoeffs Q x₀) →
      rest.foldl (fun a Q => a + dualOodPairCollisionCount S P Q) acc ≤
        acc + rest.length * d ^ 2
  | [], acc, _ => by simp
  | Q :: qs, acc, hAll => by
    simp only [List.foldl_cons, List.length_cons]
    rcases hAll Q (.head qs) with ⟨hDegQ, hDiffPQ⟩
    have hPair := dual_ood_single_pair_le_deg_sq d S hNodup P Q hDegP hDegQ hDiffPQ
    have ih := foldl_pair_collision_le d S hNodup P hDegP qs
      (acc + dualOodPairCollisionCount S P Q)
      (fun R hR => hAll R (.tail Q hR))
    have hDist : (qs.length + 1) * d ^ 2 = d ^ 2 + qs.length * d ^ 2 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [hDist]
    omega

private theorem dualOodAllPairsSum_le_exact
    (d : Nat) (S : List QuarticGoldilocks) (hNodup : S.Nodup) :
    ∀ (cands : List (List QuarticGoldilocks)),
      (∀ P ∈ cands, P.length ≤ d + 1) →
      cands.Pairwise (fun P Q =>
        ∃ x₀ : QuarticGoldilocks, RoundPoly.evalCoeffs P x₀ ≠ RoundPoly.evalCoeffs Q x₀) →
      dualOodAllPairsSum S cands ≤ binom2 cands.length * d ^ 2
  | [], _, _ => by simp [dualOodAllPairsSum, binom2]
  | P :: rest, hDeg, hDistinct => by
    rcases List.pairwise_cons.mp hDistinct with ⟨hHead, hTailPw⟩
    have hDegP := hDeg P (.head rest)
    have hDegRest : ∀ Q ∈ rest, Q.length ≤ d + 1 := fun Q hQ => hDeg Q (.tail P hQ)
    have ihRest := dualOodAllPairsSum_le_exact d S hNodup rest hDegRest hTailPw
    have hFold := foldl_pair_collision_le d S hNodup P hDegP rest 0
      (fun Q hQ => ⟨hDegRest Q hQ, hHead Q hQ⟩)
    simp only [Nat.zero_add] at hFold
    simp only [dualOodAllPairsSum, List.length_cons, binom2_succ, Nat.add_mul]
    exact Nat.add_le_add hFold ihRest

/-- **Algebraic Dual OOD List-Collision Theorem (`dual_ood_list_collision_bound`)**:
    Over `QuarticGoldilocks`, for ANY decoded polynomial list `cands` of size `≤ L` whose entries
    have degree `≤ d` and are pairwise semantically distinct, and ANY duplicate-free challenge pool
    `S` of size `M > 0`, the fraction of dual OOD pairs `(z₀, z₁) ∈ S × S` on which some distinct
    pair in `cands` collides is bounded by `binomial(L, 2) * d^2 / M^2`
    (`= ((d / q)^2) * binomial(L, 2)` when `S = 𝔽_{p^4}`)! -/
theorem dual_ood_list_collision_bound
    (d L : Nat) (S : List QuarticGoldilocks) (hPos : 0 < S.length) (hNodup : S.Nodup)
    (cands : List (List QuarticGoldilocks))
    (hLen : cands.length ≤ L)
    (hDeg : ∀ P ∈ cands, P.length ≤ d + 1)
    (hDistinct : cands.Pairwise (fun P Q =>
      ∃ x₀ : QuarticGoldilocks, RoundPoly.evalCoeffs P x₀ ≠ RoundPoly.evalCoeffs Q x₀)) :
    dualOodAllPairsSum S cands ≤ binom2 L * d ^ 2 ∧
    RatBound.le
      ⟨dualOodAllPairsSum S cands, S.length ^ 2, Nat.pow_pos hPos⟩
      ⟨binom2 L * d ^ 2, S.length ^ 2, Nat.pow_pos hPos⟩ := by
  have hExactCands := dualOodAllPairsSum_le_exact d S hNodup cands hDeg hDistinct
  have hBinomMono : ∀ (b a : Nat), a ≤ b → binom2 a ≤ binom2 b := by
    intro b
    induction b with
    | zero =>
      intro a hab
      have ha0 : a = 0 := by omega
      rw [ha0]
      exact Nat.le_refl _
    | succ m ihm =>
      intro a hab
      if haEq : a = m + 1 then
        rw [haEq]
        exact Nat.le_refl _
      else
        have haLe : a ≤ m := by omega
        rw [binom2_succ]
        exact Nat.le_trans (ihm a haLe) (Nat.le_add_left _ _)
  have hTotal : dualOodAllPairsSum S cands ≤ binom2 L * d ^ 2 :=
    Nat.le_trans hExactCands (Nat.mul_le_mul_right (d ^ 2) (hBinomMono L cands.length hLen))
  refine ⟨hTotal, ?_⟩
  unfold RatBound.le
  dsimp only
  exact Nat.mul_le_mul_right (S.length ^ 2) hTotal

/-- Count of `q`-query coset tuples in `(Fin n)^q` where EVERY queried coset passes `passCoset`. -/
def cosetSurvivalTupleCount (n : Nat) (passCoset : Fin n → Bool) : Nat → Nat
  | 0 => 1
  | q + 1 =>
    qsum n (fun idx =>
      if passCoset idx = true then cosetSurvivalTupleCount n passCoset q else 0)

/-- **`δ_j`-Far Codeword Multi-Query Survival Theorem (`far_codeword_coset_queries_survive_bound`)**:
    If a `δ_j`-far oracle table passes single-coset verification on at most `agreeMax` out of `n`
    cosets (`agreeMax / n = 1 - δ_j`), then across all `n ^ q` independent `q`-coset query
    schedules, at most `agreeMax ^ q` schedules survive all `q` checks (`≤ (1 - δ_j)^q`)! -/
theorem far_codeword_coset_queries_survive_bound
    (n agreeMax : Nat) (hNPos : 0 < n) (passCoset : Fin n → Bool)
    (hFar : qsum n (fun idx => if passCoset idx = true then 1 else 0) ≤ agreeMax) :
    ∀ (q : Nat),
      cosetSurvivalTupleCount n passCoset q ≤ agreeMax ^ q ∧
      RatBound.le
        ⟨cosetSurvivalTupleCount n passCoset q, n ^ q, Nat.pow_pos hNPos⟩
        ⟨agreeMax ^ q, n ^ q, Nat.pow_pos hNPos⟩
  | 0 => ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  | q + 1 => by
    let prev := cosetSurvivalTupleCount n passCoset q
    have ih : prev ≤ agreeMax ^ q :=
      (far_codeword_coset_queries_survive_bound n agreeMax hNPos passCoset hFar q).1
    have hFactor :
        cosetSurvivalTupleCount n passCoset (q + 1) =
          qsum n (fun idx => (if passCoset idx = true then 1 else 0) * prev) := by
      change qsum n (fun idx => if passCoset idx = true then prev else 0) = _
      apply qsum_congr; intro idx
      cases passCoset idx
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]
      · simp only [↓reduceIte, Nat.one_mul]
    have hLe : cosetSurvivalTupleCount n passCoset (q + 1) ≤ agreeMax ^ (q + 1) := by
      rw [hFactor, qsum_mul_right, Nat.pow_succ, Nat.mul_comm (agreeMax ^ q) agreeMax]
      exact Nat.mul_le_mul hFar ih
    refine ⟨hLe, ?_⟩
    unfold RatBound.le
    dsimp only
    exact Nat.mul_le_mul_right (n ^ (q + 1)) hLe

/-! ### §2.3 Explicit `Hem` v6 Multi-Round Protocol, `hemAffineWhirStateFunction` & Verifier -/

/-- Exact coset agreement count between oracle `O : Nat → F` and polynomial `P` over `domPts`. -/
def hemCosetAgreeCount {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (oracleAt : Nat → F) (P : List F) : Nat :=
  qsum domPts.length (fun idx =>
    if oracleAt idx.1 = RoundPoly.evalCoeffs P (domPts.get idx) then 1 else 0)

/-- Checks whether polynomial `P` has degree `≤ degBound`, coset agreement `≥ minAgree` with
    `oracleAt` on `domPts`, and linear-functional evaluation `ringDot P kernel = claim`. -/
def polyWitnessValid {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (minAgree degBound : Nat)
    (oracleAt : Nat → F) (kernel : List F) (claim : F) (P : List F) : Bool :=
  decide (P.length ≤ degBound + 1) &&
  decide (minAgree ≤ hemCosetAgreeCount domPts oracleAt P) &&
  decide (ringDot P kernel = claim)

/-- Asymmetric cascade polynomial combiner `∑_i (α_i + β_i X) W_i` (`deg ≤ d₀ + 1`). -/
def evalCascadePolySum {F : Type} [CommRingOps F] :
    List (List F) → List (F × F) → List F
  | [], _ => []
  | _, [] => []
  | W :: ws, (α, β) :: abs =>
    polyAddVar
      (polyAddVar (polyScaleVar α W) (polyScaleVar β (shiftPoly W)))
      (evalCascadePolySum ws abs)

/-- Asymmetric cascade combined claim `∑_i (α_i * e_i + β_i * s_i)` matching `PCS_BATCH_SHIFT`. -/
def evalCascadeClaim {F : Type} [CommRingOps F] :
    List F → List F → List (F × F) → F
  | [], _, _ => CommRingOps.zero
  | _, [], _ => CommRingOps.zero
  | _, _, [] => CommRingOps.zero
  | e :: es, s :: ss, (α, β) :: abs =>
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul α e) (CommRingOps.mul β s))
      (evalCascadeClaim es ss abs)

/-- Asymmetric cascade combined oracle `O_cascade(idx) = ∑_i (α_i + β_i * dom[idx]) * O_i(idx)`. -/
def evalCascadeOracle {F : Type} [CommRingOps F] (domPts : List F) :
    List (Nat → F) → List (F × F) → Nat → F
  | [], _, _ => CommRingOps.zero
  | _, [], _ => CommRingOps.zero
  | O :: os, (α, β) :: abs, idx =>
    let x := domPts.getD idx CommRingOps.zero
    let w := CommRingOps.add α (CommRingOps.mul β x)
    CommRingOps.add (CommRingOps.mul w (O idx)) (evalCascadeOracle domPts os abs idx)

theorem ringDot_evalCascadePolySum {F : Type} [LawfulCommRing F] (kernel : List F) :
    ∀ (ws : List (List F)) (abs : List (F × F)),
      ws.length = abs.length →
      ringDot (evalCascadePolySum ws abs) kernel =
        evalCascadeClaim
          (ws.map (fun W => ringDot W kernel))
          (ws.map (fun W => ringDot (shiftPoly W) kernel))
          abs
  | [], [], _ => rfl
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)
  | [], _ :: _, h => absurd h.symm (Nat.succ_ne_zero _)
  | W :: ws, (α, β) :: abs, h => by
    have hSub : ws.length = abs.length := Nat.succ.inj h
    dsimp only [evalCascadePolySum, evalCascadeClaim, List.map]
    rw [ringDot_polyAddVar, ringDot_polyAddVar, ringDot_polyScaleVar, ringDot_polyScaleVar,
        ringDot_evalCascadePolySum kernel ws abs hSub]
termination_by structural ws => ws

/-- Stage specification of `Hem` v6 Affine WHIR over field `F` (`QuarticGoldilocks`). -/
structure HemWhirStageSpec (F : Type := QuarticGoldilocks) where
  domainPts : List F
  degBound : Nat
  minAgree : Nat
  listBound : Nat
  queriedCosets : List Nat
  deriving Repr

/-- Complete `Hem` v6 statement & committed codeword instance (`S_poly ≤ 16` batch polynomials
    reduced across `stages.length` WHIR affine-folding + dual-OOD + coset-query stages). -/
structure HemWhirInstance (F : Type := QuarticGoldilocks) where
  batchOracles : List (Nat → F)
  batchClaims : List F
  initDomainPts : List F
  initDegBound : Nat
  initMinAgree : Nat
  initKernel : List F
  stages : List (HemWhirStageSpec F)

/-- Explicit multi-round transcript message & challenge record for `Hem` v6. -/
inductive HemTranscriptRound (F : Type := QuarticGoldilocks) where
  | cascade
      (absorbedShifts : List F)
      (weights : List (F × F))
      (cascadeDecoded : List (List F))
  | stageFold
      (stageOracle : Nat → F)
      (w₀ w₁ w₂ c_F c_G : F)
      (φ θ α β : F)
      (z₀ z₁ ood₀ ood₁ : F)
      (stageDecoded : List (List F))
  | finalQuery
      (finalCoeffs : List F)

/-- Language of a `Hem` batch: every batch oracle has SOME polynomial of degree `≤ degBound`
    that agrees with it on at least `minAgree` domain points and meets its linear-functional
    claim. The polynomial is existentially quantified: it is not supplied with the instance. -/
def HemBatchValid {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (minAgree degBound : Nat) (kernel : List F) :
    List (Nat → F) → List F → Prop
  | [], [] => True
  | O :: os, e :: es =>
    (∃ P : List F, polyWitnessValid domPts minAgree degBound O kernel e P = true) ∧
      HemBatchValid domPts minAgree degBound kernel os es
  | _, _ => False

/-- Language of the `Hem` v6 statement: between 1 and 16 batch oracles, each with a valid
    polynomial witness. Membership depends on the oracles and claims alone. -/
def HemStatementValid {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) : Prop :=
  (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16) ∧
  HemBatchValid inst.initDomainPts inst.initMinAgree inst.initDegBound inst.initKernel
    inst.batchOracles inst.batchClaims

def checkQueriedCosets {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (oracleAt : Nat → F) (P : List F) : List Nat → Bool
  | [] => true
  | idx :: rest =>
    decide (idx < domPts.length) &&
    decide (oracleAt idx = RoundPoly.evalCoeffs P (domPts.getD idx CommRingOps.zero)) &&
    checkQueriedCosets domPts oracleAt P rest

/-- `affine.rs::fold_kernel`: `k'_i = k_{2i} + φ k_{2i+1}` followed by the extra zero overflow slot
    (`chunks_exact(2)` drops an unpaired tail element). The NEXT kernel is computed by the
    verifier from the challenge `φ`; it is never a prover-supplied transcript field. -/
def hemKernelFold {F : Type} [CommRingOps F] (φ : F) : List F → List F
  | a :: b :: rest => CommRingOps.add a (CommRingOps.mul φ b) :: hemKernelFold φ rest
  | _ => [CommRingOps.zero]

/-- `affine.rs::bridge_finish`: from the five bridge wires `(w₀, w₁, w₂, c_F, c_G)`
    (`WHIR_AFFINE_CROSS` ×3, then `WHIR_AFFINE_SHIFT` ×2), the running claim and the challenges
    `(φ, θ, α, β)`, the verifier DERIVES `f = w₀ + φ w₁`, `g = w₂ + φ (claim - w₀)` and the next
    claim `g + α (f + θ g) + β (c_F + θ c_G)`. There is no separate consistency check: the
    fourth cross term is forced to `claim - w₀`. -/
def hemBridgeFoldClaim {F : Type} [CommRingOps F]
    (claim w₀ w₁ w₂ c_F c_G φ θ α β : F) : F :=
  CommRingOps.add
    (CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub claim w₀)))
    (CommRingOps.add
      (CommRingOps.mul α
        (CommRingOps.add (CommRingOps.add w₀ (CommRingOps.mul φ w₁))
          (CommRingOps.mul θ (CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub claim w₀))))))
      (CommRingOps.mul β (CommRingOps.add c_F (CommRingOps.mul θ c_G))))

/-- Interleave even- and odd-indexed halves back into one coefficient / kernel vector. -/
def hemInterleave {F : Type} : List F → List F → List F
  | a :: as, b :: bs => a :: b :: hemInterleave as bs
  | _, _ => []

theorem hemKernelFold_interleave {F : Type} [CommRingOps F] (φ : F) :
    ∀ (kE kO : List F), kE.length = kO.length →
      hemKernelFold φ (hemInterleave kE kO) =
        List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO ++
          [CommRingOps.zero]
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)
  | a :: as, b :: bs, h =>
    congrArg (List.cons (CommRingOps.add a (CommRingOps.mul φ b)))
      (hemKernelFold_interleave φ as bs (Nat.succ.inj h))

theorem ringDot_zipFold {F : Type} [LawfulCommRing F] (φ : F) :
    ∀ (c kE kO : List F), kE.length = kO.length →
      ringDot c (List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO) =
        CommRingOps.add (ringDot c kE) (CommRingOps.mul φ (ringDot c kO))
  | [], _, _, _ => by
    simp only [ringDot, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | _ :: _, [], [], _ => by
    simp only [List.zipWith_nil_left, ringDot, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | _ :: _, [], _ :: _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, _ :: _, [], h => absurd h (Nat.succ_ne_zero _)
  | x :: xs, a :: as, b :: bs, h => by
    have ih := ringDot_zipFold φ xs as bs (Nat.succ.inj h)
    simp only [List.zipWith_cons_cons, ringDot]
    rw [ih, LawfulCommRing.left_distrib x a (CommRingOps.mul φ b),
        ← LawfulCommRing.mul_assoc x φ b, LawfulCommRing.mul_comm x φ,
        LawfulCommRing.mul_assoc φ x b, LawfulCommRing.add_add_add_comm,
        ← LawfulCommRing.left_distrib φ (CommRingOps.mul x b) (ringDot xs bs)]

/-- **Rust-Faithful Dual Bridge (`hem_bridge_fold_claim_eq_dot`, `affine.rs::prove_fold`)**:
    split coefficients and kernel into even / odd halves `(cE, cO)`, `(kE, kO)`. With the honest
    cross wires `w₀ = ⟨cE, kE⟩`, `w₁ = ⟨cE, kO⟩`, `w₂ = ⟨cO, kE⟩`, the running claim
    `⟨cE, kE⟩ + ⟨cO, kO⟩`, and the shift wires against the folded kernel `k' = kE + φ kO`,
    `hemBridgeFoldClaim` IS the inner product of the folded coefficients
    `affineCombine θ α β cE cO = cO + (α + β X)(cE + θ cO)` (`fold_coeffs`) with `k'`: the Lean
    counterpart of `debug_assert_eq!(dot_ext4_fast(c, k), next)`. -/
theorem hem_bridge_fold_claim_eq_dot {F : Type} [LawfulCommRing F]
    (φ θ α β : F) (cE cO kE kO : List F) (h : kE.length = kO.length) :
    hemBridgeFoldClaim
        (CommRingOps.add (ringDot cE kE) (ringDot cO kO))
        (ringDot cE kE) (ringDot cE kO) (ringDot cO kE)
        (ringDot (shiftPoly cE)
          (List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO))
        (ringDot (shiftPoly cO)
          (List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO))
        φ θ α β =
      ringDot (affineCombine θ α β cE cO)
        (List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO) := by
  have hSub : CommRingOps.sub (CommRingOps.add (ringDot cE kE) (ringDot cO kO)) (ringDot cE kE) =
      ringDot cO kO := by
    rw [LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.add_comm (ringDot cE kE) (ringDot cO kO),
        LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  unfold hemBridgeFoldClaim
  rw [ringDot_affineCombine_eq_bridge, ringDot_zipFold φ cE kE kO h,
      ringDot_zipFold φ cO kE kO h, hSub]

def evalHemRbrPrefix {F : Type} [CommRingOps F] [DecidableEq F]
    (curLive : Bool)
    (curOracle : Nat → F)
    (curDom : List F)
    (curDeg curMinAgree : Nat)
    (curKernel : List F)
    (curClaim : F) :
    List (HemWhirStageSpec F) → List (HemTranscriptRound F) → Bool
  | _, [] => curLive
  | remStages, .cascade _ _ cascadeDecoded :: restTr =>
    let nextLive :=
      cascadeDecoded.any (fun P =>
        polyWitnessValid curDom curMinAgree (curDeg + 1) curOracle curKernel curClaim P)
    evalHemRbrPrefix (curLive || nextLive) curOracle curDom (curDeg + 1) curMinAgree
      curKernel curClaim remStages restTr
  | st :: remStages,
    .stageFold stageOracle w₀ w₁ w₂ c_F c_G φ θ α β z₀ z₁ ood₀ ood₁ stageDecoded :: restTr =>
    let expectedFoldClaim := hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β
    let nextKernel := hemKernelFold φ curKernel
    let stageHasWitness :=
      stageDecoded.any (fun P =>
        polyWitnessValid st.domainPts st.minAgree st.degBound stageOracle nextKernel expectedFoldClaim P &&
        decide (RoundPoly.evalCoeffs P z₀ = ood₀) &&
        decide (RoundPoly.evalCoeffs P z₁ = ood₁))
    evalHemRbrPrefix stageHasWitness stageOracle st.domainPts st.degBound st.minAgree
      nextKernel expectedFoldClaim remStages restTr
  | [], [.finalQuery finalCoeffs] =>
    decide (finalCoeffs.length ≤ curDeg + 1) &&
    decide (ringDot finalCoeffs curKernel = curClaim) &&
    checkQueriedCosets curDom curOracle finalCoeffs
      (List.range (Nat.min curMinAgree curDom.length))
  | _, _ => false

/-- Boolean liveness of a nonempty transcript prefix of the `Hem` v6 model: Round 0 asymmetric
    cascade (`S_poly ≤ 16`), `S` stages of monomial-shift affine folding with the `affine.rs`
    five-wire bridge (`hemBridgeFoldClaim`, verifier-computed `hemKernelFold`) + dual OOD
    pinning, and final coefficients + coset checks. Every stage check is algebraic; the decoded
    polynomial witnessing a live stage is read from the transcript's decoded lists. -/
def hemPrefixState {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (tr : List (HemTranscriptRound F)) : Bool :=
  match tr with
  | .cascade absorbedShifts weights cascadeDecoded :: restTr =>
    let okLengths :=
      decide (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16) &&
      decide (absorbedShifts.length = inst.batchClaims.length) &&
      decide (weights.length = inst.batchClaims.length)
    if okLengths = true then
      let combClaim := evalCascadeClaim inst.batchClaims absorbedShifts weights
      let combOracle := evalCascadeOracle inst.initDomainPts inst.batchOracles weights
      let cascadeLive :=
        cascadeDecoded.any (fun P =>
          polyWitnessValid inst.initDomainPts inst.initMinAgree (inst.initDegBound + 1)
            combOracle inst.initKernel combClaim P)
      evalHemRbrPrefix cascadeLive combOracle inst.initDomainPts (inst.initDegBound + 1)
        inst.initMinAgree inst.initKernel combClaim inst.stages restTr
    else false
  | _ => false

/-- **State predicate of the `Hem` v6 transcript model (`hemAffineWhirStateFunction`)** over
    `QuarticGoldilocks` (`F = QuarticGoldilocks` by default). The empty transcript is live
    exactly when the statement is in the language `HemStatementValid` (an existential over
    polynomial witnesses, independent of any prover-supplied candidate list); a nonempty
    prefix is live when `hemPrefixState` holds. -/
@[expose] def hemAffineWhirStateFunction {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (tr : List (HemTranscriptRound F)) : Prop :=
  match tr with
  | [] => HemStatementValid inst
  | _ :: _ => hemPrefixState inst tr = true

def verifyHemStages {F : Type} [CommRingOps F] [DecidableEq F]
    (curOracle : Nat → F)
    (curDom : List F)
    (curDeg curMinAgree : Nat)
    (curKernel : List F)
    (curClaim : F) :
    List (HemWhirStageSpec F) → List (HemTranscriptRound F) → Bool
  | [], [.finalQuery finalCoeffs] =>
    decide (finalCoeffs.length ≤ curDeg + 1) &&
    decide (ringDot finalCoeffs curKernel = curClaim) &&
    checkQueriedCosets curDom curOracle finalCoeffs
      (List.range (Nat.min curMinAgree curDom.length))
  | st :: remStages,
    .stageFold stageOracle w₀ w₁ w₂ c_F c_G φ θ α β z₀ z₁ ood₀ ood₁ stageDecoded :: restTr =>
    let expectedFoldClaim := hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β
    let nextKernel := hemKernelFold φ curKernel
    stageDecoded.any (fun P =>
      polyWitnessValid st.domainPts st.minAgree st.degBound stageOracle nextKernel expectedFoldClaim P &&
      decide (RoundPoly.evalCoeffs P z₀ = ood₀) &&
      decide (RoundPoly.evalCoeffs P z₁ = ood₁) &&
      checkQueriedCosets st.domainPts stageOracle P st.queriedCosets) &&
    verifyHemStages stageOracle st.domainPts st.degBound st.minAgree
      nextKernel expectedFoldClaim remStages restTr
  | _, _ => false

/-- Deterministic `Hem` v6 full-transcript verifier (`verifyHemAffineWhir`). -/
@[expose] def verifyHemAffineWhir {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (tr : List (HemTranscriptRound F)) : Bool :=
  match tr with
  | .cascade absorbedShifts weights cascadeDecoded :: restTr =>
    decide (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16) &&
    decide (absorbedShifts.length = inst.batchClaims.length) &&
    decide (weights.length = inst.batchClaims.length) &&
    let combClaim := evalCascadeClaim inst.batchClaims absorbedShifts weights
    let combOracle := evalCascadeOracle inst.initDomainPts inst.batchOracles weights
    cascadeDecoded.any (fun P =>
      polyWitnessValid inst.initDomainPts inst.initMinAgree (inst.initDegBound + 1)
        combOracle inst.initKernel combClaim P) &&
    verifyHemStages combOracle inst.initDomainPts (inst.initDegBound + 1)
      inst.initMinAgree inst.initKernel combClaim inst.stages restTr
  | _ => false

private theorem verifyHemStages_implies_evalHemRbrPrefix {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (curLive : Bool) (curOracle : Nat → F)
      (curDom : List F) (curDeg curMinAgree : Nat)
      (curKernel : List F) (curClaim : F)
      (remStages : List (HemWhirStageSpec F)) (restTr : List (HemTranscriptRound F)),
      verifyHemStages curOracle curDom curDeg curMinAgree curKernel curClaim remStages restTr = true →
      evalHemRbrPrefix curLive curOracle curDom curDeg curMinAgree curKernel curClaim remStages restTr = true
  | _, _, _, _, _, _, _, [], [.finalQuery _], hVer => hVer
  | _, _, _, _, _, _, _, [], [], hVer => Bool.noConfusion hVer
  | _, _, _, _, _, _, _, [], .cascade _ _ _ :: _, hVer => Bool.noConfusion hVer
  | _, _, _, _, _, _, _, [], .stageFold _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :: _, hVer =>
    Bool.noConfusion hVer
  | _, _, _, _, _, _, _, [], .finalQuery _ :: _ :: _, hVer => Bool.noConfusion hVer
  | _, _, _, _, _, _, _, _ :: _, [], hVer => Bool.noConfusion hVer
  | _, _, _, _, _, _, _, _ :: _, .cascade _ _ _ :: _, hVer => Bool.noConfusion hVer
  | _, _, _, _, _, _, _, _ :: _, .finalQuery _ :: _, hVer => Bool.noConfusion hVer
  | _, _, _, _, _, _, _, st :: remStages,
    .stageFold stageOracle w₀ w₁ w₂ c_F c_G φ θ α β z₀ z₁ ood₀ ood₁ stageDecoded :: restTr,
    hVer => by
    simp only [verifyHemStages, Bool.and_eq_true] at hVer
    simp only [evalHemRbrPrefix]
    exact verifyHemStages_implies_evalHemRbrPrefix _ stageOracle st.domainPts st.degBound
      st.minAgree _ _ remStages restTr hVer.2

private theorem honest_cascade_completeness_poly {F : Type} [LawfulCommRing F] [DecidableEq F]
    (W kernel domPts : List F) (d₀ : Nat) (α β : F) (hWLen : W.length ≤ d₀ + 1) :
    let O : Nat → F := fun idx => RoundPoly.evalCoeffs W (domPts.getD idx CommRingOps.zero)
    let e := ringDot W kernel
    let s := ringDot (shiftPoly W) kernel
    let P_comb := evalCascadePolySum [W] [(α, β)]
    let inst : HemWhirInstance F :=
      { batchOracles := [O]
        batchClaims := [e]
        initDomainPts := domPts
        initDegBound := d₀
        initMinAgree := domPts.length
        initKernel := kernel
        stages := [] }
    let tr : List (HemTranscriptRound F) :=
      [ .cascade [s] [(α, β)] [P_comb],
        .finalQuery P_comb ]
    HemStatementValid inst ∧
    verifyHemAffineWhir inst tr = true := by
  dsimp only
  let O : Nat → F := fun idx => RoundPoly.evalCoeffs W (domPts.getD idx CommRingOps.zero)
  let P_comb := evalCascadePolySum [W] [(α, β)]
  have hAgreeW : hemCosetAgreeCount domPts O W = domPts.length := by
    unfold hemCosetAgreeCount
    have hOnes : qsum domPts.length (fun idx =>
        if O idx.1 = RoundPoly.evalCoeffs W (domPts.get idx) then 1 else 0) =
        qsum domPts.length (fun _ => 1) := by
      apply qsum_congr; intro idx
      have hEq : O idx.1 = RoundPoly.evalCoeffs W (domPts.get idx) := by
        dsimp only [O]
        rw [list_getD_eq_get domPts CommRingOps.zero idx]
      simp only [hEq, ↓reduceIte]
    rw [hOnes, qsum_const, Nat.mul_one]
  have hPCombLen : P_comb.length ≤ (d₀ + 1) + 1 := by
    dsimp only [P_comb, evalCascadePolySum]
    have h1 : (polyScaleVar α W).length ≤ d₀ + 2 := by
      simp only [polyScaleVar, List.length_map]; omega
    have h2 : (polyScaleVar β (shiftPoly W)).length ≤ d₀ + 2 := by
      simp only [polyScaleVar, shiftPoly, List.length_map, List.length_cons]; omega
    have h3 := polyAddVar_length_le _ _ (d₀ + 2) h1 h2
    exact polyAddVar_length_le _ [] (d₀ + 2) h3 (Nat.zero_le _)
  have hPCombEval : ∀ z : F,
      RoundPoly.evalCoeffs P_comb z =
        CommRingOps.add
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (RoundPoly.evalCoeffs W z))
          CommRingOps.zero := by
    intro z
    dsimp only [P_comb, evalCascadePolySum]
    rw [evalCoeffs_polyAddVar, evalCoeffs_polyAddVar, evalCoeffs_polyScaleVar,
        evalCoeffs_polyScaleVar, evalCoeffs_shiftPoly]
    change CommRingOps.add
        (CommRingOps.add (CommRingOps.mul α (RoundPoly.evalCoeffs W z))
          (CommRingOps.mul β (CommRingOps.mul z (RoundPoly.evalCoeffs W z))))
        CommRingOps.zero = _
    rw [← LawfulCommRing.mul_assoc β z (RoundPoly.evalCoeffs W z),
        ← LawfulCommRing.right_distrib]
  have hAgreeComb :
      hemCosetAgreeCount domPts (evalCascadeOracle domPts [O] [(α, β)]) P_comb = domPts.length := by
    unfold hemCosetAgreeCount
    have hOnes : qsum domPts.length (fun idx =>
        if evalCascadeOracle domPts [O] [(α, β)] idx.1 =
            RoundPoly.evalCoeffs P_comb (domPts.get idx) then 1 else 0) =
        qsum domPts.length (fun _ => 1) := by
      apply qsum_congr; intro idx
      have hEq : evalCascadeOracle domPts [O] [(α, β)] idx.1 =
          RoundPoly.evalCoeffs P_comb (domPts.get idx) := by
        dsimp only [evalCascadeOracle, O]
        rw [list_getD_eq_get domPts CommRingOps.zero idx, hPCombEval (domPts.get idx)]
      simp only [hEq, ↓reduceIte]
    rw [hOnes, qsum_const, Nat.mul_one]
  have hDotComb :
      ringDot P_comb kernel =
        evalCascadeClaim [ringDot W kernel] [ringDot (shiftPoly W) kernel] [(α, β)] :=
    ringDot_evalCascadePolySum kernel [W] [(α, β)] rfl
  have hMinSelf : Nat.min domPts.length domPts.length = domPts.length := by simp
  have hQueriedComb :
      checkQueriedCosets domPts (evalCascadeOracle domPts [O] [(α, β)]) P_comb
        (List.range (Nat.min domPts.length domPts.length)) = true := by
    rw [hMinSelf]
    have hRange : ∀ (idxs : List Nat),
        (∀ idx ∈ idxs, idx < domPts.length) →
        checkQueriedCosets domPts (evalCascadeOracle domPts [O] [(α, β)]) P_comb idxs = true := by
      intro idxs hLt
      induction idxs with
      | nil => rfl
      | cons idx rest ih =>
        have hi := hLt idx (.head rest)
        have hEqPt : evalCascadeOracle domPts [O] [(α, β)] idx =
            RoundPoly.evalCoeffs P_comb (domPts.getD idx CommRingOps.zero) := by
          dsimp only [evalCascadeOracle, O]
          rw [hPCombEval (domPts.getD idx CommRingOps.zero)]
        simp only [checkQueriedCosets, hi, hEqPt, decide_true, Bool.true_and,
          ih (fun j hj => hLt j (.tail idx hj))]
    exact hRange (List.range domPts.length) (fun idx hMem => List.mem_range.mp hMem)
  have hValidInst :
      HemStatementValid
        ({ batchOracles := [O]
           batchClaims := [ringDot W kernel]
           initDomainPts := domPts
           initDegBound := d₀
           initMinAgree := domPts.length
           initKernel := kernel
           stages := [] } : HemWhirInstance F) := by
    have hW : polyWitnessValid domPts domPts.length d₀ O kernel (ringDot W kernel) W = true := by
      unfold polyWitnessValid
      rw [hAgreeW]
      simp only [hWLen, Nat.le_refl, decide_true, eq_self, Bool.and_self]
    show (1 ≤ [O].length ∧ [O].length ≤ 16) ∧
      ((∃ P : List F,
        polyWitnessValid domPts domPts.length d₀ O kernel (ringDot W kernel) P = true) ∧ True)
    exact ⟨⟨Nat.le_refl 1, Nat.le_of_ble_eq_true rfl⟩, ⟨W, hW⟩, trivial⟩
  have hVerTr :
      verifyHemAffineWhir
        { batchOracles := [O]
          batchClaims := [ringDot W kernel]
          initDomainPts := domPts
          initDegBound := d₀
          initMinAgree := domPts.length
          initKernel := kernel
          stages := [] }
        [ .cascade [ringDot (shiftPoly W) kernel] [(α, β)] [P_comb],
          .finalQuery P_comb ] = true := by
    unfold verifyHemAffineWhir
    dsimp only [polyWitnessValid, verifyHemStages, List.length_cons, List.length_nil,
      List.any_cons, List.any_nil]
    rw [hAgreeComb, hDotComb, hQueriedComb]
    simp only [hPCombLen, Nat.le_refl, decide_true, Bool.or_false, Bool.and_self]
    decide
  exact ⟨hValidInst, hVerTr⟩

private theorem accept_implies_live_poly {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (fullTr : List (HemTranscriptRound F)) :
    verifyHemAffineWhir inst fullTr = true → hemAffineWhirStateFunction inst fullTr := by
  cases fullTr with
  | nil => intro hVer; exact Bool.noConfusion hVer
  | cons hd restTr =>
    cases hd with
    | stageFold _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => intro hVer; exact Bool.noConfusion hVer
    | finalQuery _ => intro hVer; exact Bool.noConfusion hVer
    | cascade absorbedShifts weights cascadeDecoded =>
      intro hVer
      unfold verifyHemAffineWhir at hVer
      dsimp only at hVer
      rcases (Bool.and_eq_true _ _).mp hVer with ⟨hOk, hRest⟩
      rcases (Bool.and_eq_true _ _).mp hRest with ⟨_, hStages⟩
      show hemPrefixState inst (.cascade absorbedShifts weights cascadeDecoded :: restTr) = true
      unfold hemPrefixState
      dsimp only
      rw [hOk]
      simp only [↓reduceIte]
      exact verifyHemStages_implies_evalHemRbrPrefix _ _ _ _ _ _ _ inst.stages restTr hStages

/-- **`Hem` v6 doomed-init, accept-implies-live and honest completeness
    (`hemAffineWhir_rbr_completeness_and_doomed_init`)**, over `QuarticGoldilocks`:
    1. a statement outside `HemStatementValid` is doomed on the empty transcript;
    2. a doomed full transcript is rejected by the deterministic verifier;
    3. an accepted full transcript is live;
    4. any polynomial `W` of degree `≤ d₀`, with its shifted functional claim absorbed before
       the challenge squeeze, gives a statement in the language and a live, accepted
       transcript.
    These are the first two laws of `RbrStateFunction` together with completeness. The third
    law, a per-round flip bound, is NOT proved for this model:
    `tooth_hem_zero_cascade_weights_accept_false_claim` exhibits a flip, and bounding the
    number of flipping challenges at the deployed radius needs a mutual correlated agreement
    bound for the 16-fold cascade and for each fold (`AffineMcaBound` at the Johnson radius). -/
theorem hemAffineWhir_rbr_completeness_and_doomed_init :
    (∀ inst : HemWhirInstance QuarticGoldilocks,
      ¬ HemStatementValid inst → ¬ hemAffineWhirStateFunction inst []) ∧
    (∀ (inst : HemWhirInstance QuarticGoldilocks) (fullTr : List (HemTranscriptRound QuarticGoldilocks)),
      ¬ hemAffineWhirStateFunction inst fullTr → verifyHemAffineWhir inst fullTr = false) ∧
    (∀ (inst : HemWhirInstance QuarticGoldilocks) (fullTr : List (HemTranscriptRound QuarticGoldilocks)),
      verifyHemAffineWhir inst fullTr = true → hemAffineWhirStateFunction inst fullTr) ∧
    (∀ (W kernel domPts : List QuarticGoldilocks) (d₀ : Nat) (α β : QuarticGoldilocks),
      W.length ≤ d₀ + 1 →
      let O : Nat → QuarticGoldilocks := fun idx =>
        RoundPoly.evalCoeffs W (domPts.getD idx CommRingOps.zero)
      let e := ringDot W kernel
      let s := ringDot (shiftPoly W) kernel
      let P_comb := evalCascadePolySum [W] [(α, β)]
      let inst : HemWhirInstance QuarticGoldilocks :=
        { batchOracles := [O]
          batchClaims := [e]
          initDomainPts := domPts
          initDegBound := d₀
          initMinAgree := domPts.length
          initKernel := kernel
          stages := [] }
      let tr : List (HemTranscriptRound QuarticGoldilocks) :=
        [ .cascade [s] [(α, β)] [P_comb],
          .finalQuery P_comb ]
      HemStatementValid inst ∧
      hemAffineWhirStateFunction inst tr ∧
      verifyHemAffineWhir inst tr = true) := by
  refine ⟨fun _ hInv => hInv, ?_, accept_implies_live_poly, ?_⟩
  · intro inst fullTr hDoomed
    cases hv : verifyHemAffineWhir inst fullTr
    · rfl
    · exact absurd (accept_implies_live_poly inst fullTr hv) hDoomed
  · intro W kernel domPts d₀ α β hWLen
    rcases honest_cascade_completeness_poly W kernel domPts d₀ α β hWLen with ⟨hVal, hVer⟩
    exact ⟨hVal, accept_implies_live_poly _ _ hVer, hVer⟩

/-- A false `Hem` statement: the zero oracle on the domain `{0, 1}` with the claim that its
    degree-0 interpolant evaluates to `1` under the functional `[1]`. -/
def hemFalseClaimInstance : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun _ => CommRingOps.zero]
    batchClaims := [CommRingOps.one]
    initDomainPts := [CommRingOps.zero, CommRingOps.one]
    initDegBound := 0
    initMinAgree := 2
    initKernel := [CommRingOps.one]
    stages := [] }

/-- No polynomial witnesses the false statement: a constant agreeing with the zero oracle on
    both domain points is zero, and the zero polynomial does not meet the claim `1`. -/
theorem hemFalseClaimInstance_invalid : ¬ HemStatementValid hemFalseClaimInstance := by
  intro h
  have h' : (1 ≤ 1 ∧ 1 ≤ 16) ∧
      ((∃ P : List QuarticGoldilocks,
        polyWitnessValid [CommRingOps.zero, CommRingOps.one] 2 0 (fun _ => CommRingOps.zero)
          [CommRingOps.one] CommRingOps.one P = true) ∧ True) := h
  obtain ⟨_, ⟨P, hP⟩, _⟩ := h'
  unfold polyWitnessValid at hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨hLen, hAg⟩, hDot⟩ := hP
  rcases P with _ | ⟨c, _ | ⟨c2, rest⟩⟩
  · exact absurd hDot (by decide)
  · have hc : c = CommRingOps.zero := by
      apply Decidable.byContradiction
      intro hne
      have hne' : ¬ ((CommRingOps.zero : QuarticGoldilocks) =
          RoundPoly.evalCoeffs [c] (CommRingOps.zero : QuarticGoldilocks)) := by
        intro h
        apply hne
        have e : RoundPoly.evalCoeffs [c] (CommRingOps.zero : QuarticGoldilocks) = c := by
          show CommRingOps.add c (CommRingOps.mul CommRingOps.zero CommRingOps.zero) = c
          rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
        rw [e] at h
        exact h.symm
      change 2 ≤ (if (CommRingOps.zero : QuarticGoldilocks) =
            RoundPoly.evalCoeffs [c] (CommRingOps.zero : QuarticGoldilocks) then 1 else 0) +
          ((if (CommRingOps.zero : QuarticGoldilocks) =
            RoundPoly.evalCoeffs [c] (CommRingOps.one : QuarticGoldilocks) then 1 else 0) + 0)
        at hAg
      simp only [hne', ↓reduceIte] at hAg
      by_cases h1 : (CommRingOps.zero : QuarticGoldilocks) =
          RoundPoly.evalCoeffs [c] (CommRingOps.one : QuarticGoldilocks)
      · simp only [h1, ↓reduceIte] at hAg
        exact absurd hAg (by decide)
      · simp only [h1, ↓reduceIte] at hAg
        exact absurd hAg (by decide)
    subst hc
    exact absurd hDot (by decide)
  · simp only [List.length_cons] at hLen
    omega

/-- **A flip of the `Hem` v6 state exists.** The false statement `hemFalseClaimInstance` is
    doomed on the empty transcript, yet the deterministic verifier accepts it when the cascade
    challenge is `(α, β) = (0, 0)`: the combined oracle and the combined claim both vanish.
    Hence every round-by-round flip bound for the cascade round counts at least this
    challenge, and soundness of the model rests on bounding the number of such challenges. -/
theorem tooth_hem_zero_cascade_weights_accept_false_claim :
    ¬ hemAffineWhirStateFunction hemFalseClaimInstance [] ∧
    verifyHemAffineWhir hemFalseClaimInstance
      [.cascade [CommRingOps.zero] [(CommRingOps.zero, CommRingOps.zero)] [[]],
       .finalQuery []] = true :=
  ⟨hemFalseClaimInstance_invalid, by decide⟩


/-! ## §3. Multi-Round Fiat–Shamir QROM Reduction via Measure-and-Reprogram & Online Merkle Extraction -/

/-! ### §3.1 Unitary `(2 * Q + 1)`-Branch Amplitude Decomposition & `(2 * Q + 1)^2` RBR Step -/

/-- Project `QVec` onto a single target query coordinate `xStar : Fin cardX`. -/
def projSingle {cardX w cardAnc : Nat} (xStar : Fin cardX)
    (ψ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => if x = xStar then ψ x y a else GaussInt.zero

/-- Negate all Gaussian-integer amplitudes of a `QVec`. -/
def negQVec {cardX w cardAnc : Nat} (ψ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  (QVec.zero cardX w cardAnc).sub ψ

private theorem projSingle_normSq {cardX w cardAnc : Nat} (xStar : Fin cardX)
    (ψ : QVec cardX w cardAnc) :
    QVec.stateNormSq (projSingle xStar ψ) = QVec.queryWeight ψ xStar := by
  unfold QVec.stateNormSq
  have hPt :
      qsum cardX (fun x => QVec.queryWeight (projSingle xStar ψ) x) =
      qsum cardX (fun x => (if x = xStar then 1 else 0) * QVec.queryWeight ψ xStar) := by
    apply qsum_congr; intro x
    by_cases hx : x = xStar
    · subst hx
      simp only [↓reduceIte, Nat.one_mul, QVec.queryWeight, projSingle]
    · simp only [hx, ↓reduceIte, Nat.zero_mul, QVec.queryWeight, projSingle]
      have h0 : qsum (2 ^ w) (fun _ => qsum cardAnc (fun _ => GaussInt.normSq GaussInt.zero)) =
          qsum (2 ^ w) (fun _ => 0) := by
        apply qsum_congr; intro _
        have ha : GaussInt.normSq GaussInt.zero = 0 := rfl
        rw [qsum_congr (fun _ => ha), qsum_const, Nat.mul_zero]
      rw [h0, qsum_const, Nat.mul_zero]
  rw [hPt, qsum_mul_right, qsum_eq_indicator, Nat.one_mul]

private theorem negQVec_normSq {cardX w cardAnc : Nat} (ψ : QVec cardX w cardAnc) :
    QVec.stateNormSq (negQVec ψ) = QVec.stateNormSq ψ := by
  have hIntAbs : ∀ z : Int, (0 - z).natAbs = z.natAbs := by
    intro z; rw [Int.zero_sub, Int.natAbs_neg]
  unfold QVec.stateNormSq QVec.queryWeight negQVec QVec.sub QVec.zero
  apply qsum_congr; intro x
  apply qsum_congr; intro y
  apply qsum_congr; intro a
  unfold GaussInt.normSq GaussInt.sub GaussInt.zero
  dsimp only
  rw [hIntAbs, hIntAbs]

private theorem oracleXor_reprogram_diff_eq_projSingle {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (xStar : Fin cardX) (ch : BitVec w)
    (ψ : QVec cardX w cardAnc) :
    (oracleXor (reprogramOracle H xStar ch) ψ).sub (oracleXor H ψ) =
      (oracleXor (reprogramOracle H xStar ch) (projSingle xStar ψ)).sub
        (oracleXor H (projSingle xStar ψ)) := by
  funext x y a
  by_cases hx : x = xStar
  · subst hx
    simp only [QVec.sub, oracleXor, projSingle, ↓reduceIte]
  · simp only [QVec.sub, oracleXor, projSingle, reprogramOracle, hx, ↓reduceIte]
    unfold GaussInt.sub GaussInt.zero
    ext <;> dsimp only <;> omega

/-- Structural `2 * q + 1` counter matching `finGaussSum` & `qsum` front-peeling recursion. -/
def twoMulPlusOne : Nat → Nat
  | 0 => 1
  | q + 1 => (twoMulPlusOne q + 1) + 1

private theorem twoMulPlusOne_eq (q : Nat) : twoMulPlusOne q = 2 * q + 1 := by
  induction q with
  | zero => rfl
  | succ m ih => simp only [twoMulPlusOne, ih]; omega

/-- Interleaves `q` positive reprogramming branches, `q` negative pre-reprogramming branches, and
    `1` base execution branch into `twoMulPlusOne q` (`= 2 * q + 1`) vectors. -/
def interleaveDfmBranches {α : Type} :
    (q : Nat) → (Fin q → α) → (Fin q → α) → α → Fin (twoMulPlusOne q) → α
  | 0, _, _, base, _ => base
  | q + 1, posB, _, _, ⟨0, _⟩ => posB ⟨0, Nat.zero_lt_succ q⟩
  | q + 1, _, negB, _, ⟨1, _⟩ => negB ⟨0, Nat.zero_lt_succ q⟩
  | q + 1, posB, negB, base, ⟨k + 2, hk⟩ =>
    interleaveDfmBranches q
      (fun t => posB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)
      (fun t => negB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)
      base
      ⟨k, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk)⟩

private theorem finGaussSum_interleaveDfmBranches :
    ∀ (q : Nat) (posB negB : Fin q → GaussInt) (base : GaussInt),
      finGaussSum (twoMulPlusOne q) (interleaveDfmBranches q posB negB base) =
        GaussInt.add (finGaussSum q (fun t => GaussInt.add (posB t) (negB t))) base
  | 0, _, _, base => by
    simp only [twoMulPlusOne, finGaussSum, interleaveDfmBranches, GaussInt.add, GaussInt.zero]
    ext <;> dsimp only <;> omega
  | q + 1, posB, negB, base => by
    let posTail : Fin q → GaussInt := fun t => posB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    let negTail : Fin q → GaussInt := fun t => negB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    have ih := finGaussSum_interleaveDfmBranches q posTail negTail base
    change GaussInt.add (posB ⟨0, Nat.zero_lt_succ q⟩)
        (GaussInt.add (negB ⟨0, Nat.zero_lt_succ q⟩)
          (finGaussSum (twoMulPlusOne q) (interleaveDfmBranches q posTail negTail base))) =
      GaussInt.add
        (GaussInt.add
          (GaussInt.add (posB ⟨0, Nat.zero_lt_succ q⟩) (negB ⟨0, Nat.zero_lt_succ q⟩))
          (finGaussSum q (fun t => GaussInt.add (posTail t) (negTail t))))
        base
    rw [ih]
    unfold GaussInt.add
    ext <;> dsimp only <;> omega

private theorem qsum_interleaveDfmBranches {α : Type} (wt : α → Nat) :
    ∀ (q : Nat) (posB negB : Fin q → α) (base : α),
      qsum (twoMulPlusOne q) (fun k => wt (interleaveDfmBranches q posB negB base k)) =
        qsum q (fun t => wt (posB t) + wt (negB t)) + wt base
  | 0, _, _, base => by simp [twoMulPlusOne, qsum, interleaveDfmBranches]
  | q + 1, posB, negB, base => by
    let posTail : Fin q → α := fun t => posB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    let negTail : Fin q → α := fun t => negB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    have ih := qsum_interleaveDfmBranches wt q posTail negTail base
    change wt (posB ⟨0, Nat.zero_lt_succ q⟩) +
        (wt (negB ⟨0, Nat.zero_lt_succ q⟩) +
          qsum (twoMulPlusOne q) (fun k => wt (interleaveDfmBranches q posTail negTail base k))) =
      (wt (posB ⟨0, Nat.zero_lt_succ q⟩) + wt (negB ⟨0, Nat.zero_lt_succ q⟩) +
        qsum q (fun t => wt (posTail t) + wt (negTail t))) + wt base
    rw [ih]
    omega

private theorem interleaveDfmBranches_eval {cardX w cardAnc : Nat}
    (x : Fin cardX) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    ∀ (m : Nat) (pV nV : Fin m → QVec cardX w cardAnc) (bV : QVec cardX w cardAnc)
      (k : Fin (twoMulPlusOne m)),
      interleaveDfmBranches m pV nV bV k x y a =
        interleaveDfmBranches m (fun t => pV t x y a) (fun t => nV t x y a) (bV x y a) k
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, _, ⟨0, _⟩ => rfl
  | _ + 1, _, _, _, ⟨1, _⟩ => rfl
  | m' + 1, pV, nV, bV, ⟨k' + 2, hk⟩ =>
    interleaveDfmBranches_eval x y a m'
      (fun t => pV ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)
      (fun t => nV ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)
      bV
      ⟨k', Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk)⟩

private theorem advStateAt_congr_idx {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w)
    {k₁ k₂ : Nat} (hk₁ : k₁ ≤ q) (hk₂ : k₂ ≤ q) (hEq : k₁ = k₂) :
    advStateAt A H k₁ hk₁ = advStateAt A H k₂ hk₂ := by
  subst hEq
  rfl

private theorem telescope_hybridAdv_reprogram {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) (xStar : Fin cardX) (ch : BitVec w)
    (x : Fin cardX) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    let H_ch := reprogramOracle H xStar ch
    let posB : Fin q → QVec cardX w cardAnc := fun t =>
      applySuffixFrom A H_ch t.1 t.2
        (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))
    let negB : Fin q → QVec cardX w cardAnc := fun t =>
      negQVec (applySuffixFrom A H_ch t.1 t.2
        (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2)))))
    finGaussSum (twoMulPlusOne q)
        (fun k => interleaveDfmBranches q posB negB (runQuantumAdv A H) k x y a) =
      runQuantumAdv A H_ch x y a := by
  dsimp only
  let H_ch := reprogramOracle H xStar ch
  let posVal : Fin q → GaussInt := fun t =>
    applySuffixFrom A H_ch t.1 t.2
      (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2)))) x y a
  let negVal : Fin q → GaussInt := fun t =>
    negQVec (applySuffixFrom A H_ch t.1 t.2
      (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))) x y a
  have hInter :
      finGaussSum (twoMulPlusOne q)
        (fun k => interleaveDfmBranches q
          (fun t => applySuffixFrom A H_ch t.1 t.2
            (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2)))))
          (fun t => negQVec (applySuffixFrom A H_ch t.1 t.2
            (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))))
          (runQuantumAdv A H) k x y a) =
      finGaussSum (twoMulPlusOne q)
        (interleaveDfmBranches q posVal negVal (runQuantumAdv A H x y a)) :=
    congrArg (finGaussSum (twoMulPlusOne q))
      (funext (interleaveDfmBranches_eval x y a q _ _ _))
  rw [hInter, finGaussSum_interleaveDfmBranches]
  have hStepEq : ∀ t : Fin q,
      GaussInt.add (posVal t) (negVal t) =
        GaussInt.sub
          (hybridAdv A H_ch H t.1 (Nat.le_of_lt t.2) x y a)
          (hybridAdv A H_ch H (t.1 + 1) t.2 x y a) := by
    intro t
    have hSubVec :
        (hybridAdv A H_ch H t.1 (Nat.le_of_lt t.2)).sub (hybridAdv A H_ch H (t.1 + 1) t.2) =
          (applySuffixFrom A H_ch t.1 t.2
            (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))).sub
          (applySuffixFrom A H_ch t.1 t.2
            (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))) := by
      have hRhs2 :
          applySuffixFrom A H_ch t.1 t.2 (oracleXor H (advStateAt A H t.1 (Nat.le_of_lt t.2))) =
            hybridAdv A H_ch H (t.1 + 1) t.2 := by
        rw [applySuffixFrom.eq_def]
        dsimp only
        have hStep : (A.steps t).apply (oracleXor H (advStateAt A H t.1 (Nat.le_of_lt t.2))) =
            advStateAt A H (t.1 + 1) t.2 := rfl
        rw [hStep]
        unfold hybridAdv
        if hNext : t.1 + 1 < q then
          simp only [hNext, ↓reduceDIte]
        else
          have hEqQ : t.1 + 1 = q := by omega
          simp only [hNext, ↓reduceDIte]
          exact advStateAt_congr_idx A H t.2 (Nat.le_refl q) hEqQ
      have hLhs1 : hybridAdv A H_ch H t.1 (Nat.le_of_lt t.2) =
          applySuffixFrom A H_ch t.1 t.2 (oracleXor H_ch (advStateAt A H t.1 (Nat.le_of_lt t.2))) := by
        unfold hybridAdv
        simp only [t.2, ↓reduceDIte]
      rw [hLhs1, ← hRhs2, ← applySuffixFrom_sub,
          oracleXor_reprogram_diff_eq_projSingle H xStar ch, applySuffixFrom_sub]
    have hAtCoord := congrFun (congrFun (congrFun hSubVec x) y) a
    dsimp only [posVal, negVal, negQVec, QVec.sub, QVec.zero] at hAtCoord ⊢
    rw [hAtCoord]
    unfold GaussInt.add GaussInt.sub GaussInt.zero
    ext <;> dsimp only <;> omega
  have hCongrG : ∀ {m : Nat} (f g : Fin m → GaussInt),
      (∀ i, f i = g i) → finGaussSum m f = finGaussSum m g := by
    intro m f g hfg
    exact congrArg (finGaussSum m) (funext hfg)
  rw [hCongrG _ _ hStepEq]
  have hTele : ∀ (m : Nat) (seq : (k : Nat) → k ≤ m → GaussInt),
      finGaussSum m (fun t => GaussInt.sub (seq t.1 (Nat.le_of_lt t.2)) (seq (t.1 + 1) t.2)) =
        GaussInt.sub (seq 0 (Nat.zero_le m)) (seq m (Nat.le_refl m)) := by
    intro m
    induction m with
    | zero => intro seq; simp [finGaussSum, GaussInt.sub, GaussInt.zero]
    | succ m' ihm =>
      intro seq
      simp only [finGaussSum]
      rw [ihm (fun k hk => seq (k + 1) (Nat.succ_le_succ hk))]
      unfold GaussInt.add GaussInt.sub
      ext <;> dsimp only <;> omega
  rw [hTele q (fun k hk => hybridAdv A H_ch H k hk x y a)]
  have hHyb0 : hybridAdv A H_ch H 0 (Nat.zero_le q) = runQuantumAdv A H_ch := by
    have hSuffEq : ∀ (k : Nat) (hk : k ≤ q),
        (if hlt : k < q then applySuffixFrom A H_ch k hlt (oracleXor H_ch (advStateAt A H_ch k hk))
         else advStateAt A H_ch q (Nat.le_refl q)) = runQuantumAdv A H_ch := by
      intro k hk
      induction hRem : q - k generalizing k with
      | zero =>
        have hEqQ : k = q := by omega
        subst hEqQ
        simp [runQuantumAdv]
      | succ rem ihRem =>
        have hlt : k < q := by omega
        simp only [hlt, ↓reduceDIte]
        rw [applySuffixFrom.eq_def]
        dsimp only
        have hAdvNext : (A.steps ⟨k, hlt⟩).apply (oracleXor H_ch (advStateAt A H_ch k hk)) =
            advStateAt A H_ch (k + 1) hlt := rfl
        rw [hAdvNext]
        if hNext : k + 1 < q then
          simp only [hNext, ↓reduceDIte]
          have ih' := ihRem (k + 1) (Nat.le_of_lt hNext) (by omega)
          simp only [hNext, ↓reduceDIte] at ih'
          exact ih'
        else
          have hEqQ : k + 1 = q := by omega
          simp only [hNext, ↓reduceDIte, runQuantumAdv]
          exact advStateAt_congr_idx A H_ch hlt (Nat.le_refl q) hEqQ
    cases q with
    | zero => rfl
    | succ q' =>
      have hPos : 0 < q' + 1 := Nat.zero_lt_succ q'
      have h0 := hSuffEq 0 (Nat.zero_le (q' + 1))
      simp only [hPos, ↓reduceDIte] at h0
      unfold hybridAdv
      simp only [hPos, ↓reduceDIte]
      exact h0
  have hHybQ : hybridAdv A H_ch H q (Nat.le_refl q) = runQuantumAdv A H := by
    unfold hybridAdv runQuantumAdv
    simp
  rw [hHyb0, hHybQ]
  dsimp only [H_ch]
  unfold GaussInt.add GaussInt.sub
  ext <;> dsimp only <;> omega

/-- `ch`-independent squared-amplitude envelope of `A` reprogrammed at `xStar` under `H`, for an
    arbitrary OUTPUT event `T` on the final query/output register. -/
def dfmEventEnvelope {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w) (xStar : Fin cardX)
    (T : Fin cardX → Bool) : Nat :=
  qsum q (fun t =>
    2 * (suffixScale A t.1 (Nat.le_of_lt t.2) *
      QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) xStar)) +
    QVec.queryMassOn T (runQuantumAdv A H)

private theorem queryMassOn_reprogram_le_dfmEventEnvelope {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w)
    (xStar : Fin cardX) (ch : BitVec w) (T : Fin cardX → Bool) :
    QVec.queryMassOn T (runQuantumAdv A (reprogramOracle H xStar ch)) ≤
      (2 * q + 1) * dfmEventEnvelope A H xStar T := by
  let H_ch := reprogramOracle H xStar ch
  let posB : Fin q → QVec cardX w cardAnc := fun t =>
    applySuffixFrom A H_ch t.1 t.2
      (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))
  let negB : Fin q → QVec cardX w cardAnc := fun t =>
    negQVec (applySuffixFrom A H_ch t.1 t.2
      (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2)))))
  let V := interleaveDfmBranches q posB negB (runQuantumAdv A H)
  have hPtCS : ∀ x : Fin cardX,
      QVec.queryWeight (runQuantumAdv A H_ch) x ≤
        twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k => QVec.queryWeight (V k) x) := by
    intro x
    unfold QVec.queryWeight
    have hStep1 :
        qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
          GaussInt.normSq (runQuantumAdv A H_ch x y a))) ≤
        qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
          twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k => GaussInt.normSq (V k x y a)))) := by
      apply qsum_le_qsum; intro y
      apply qsum_le_qsum; intro a
      rw [← telescope_hybridAdv_reprogram A H xStar ch x y a]
      exact normSq_finGaussSum_le (twoMulPlusOne q) (fun k => V k x y a)
    apply Nat.le_trans hStep1
    have hSwap : ∀ y,
        qsum cardAnc (fun a =>
          twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k => GaussInt.normSq (V k x y a))) =
        twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k =>
          qsum cardAnc (fun a => GaussInt.normSq (V k x y a))) := by
      intro y
      rw [qsum_mul_left, qsum_comm]
    rw [qsum_congr hSwap, qsum_mul_left, qsum_comm]
    exact Nat.le_refl _
  have hMass :
      QVec.queryMassOn T (runQuantumAdv A H_ch) ≤
        twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k => QVec.queryMassOn T (V k)) := by
    have hPt :
        qsum cardX (fun x =>
          if T x = true then QVec.queryWeight (runQuantumAdv A H_ch) x else 0) ≤
        qsum cardX (fun x =>
          twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k =>
            if T x = true then QVec.queryWeight (V k) x else 0)) := by
      apply qsum_le_qsum; intro x
      cases T x
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
      · simp only [↓reduceIte]
        exact hPtCS x
    rw [qsum_mul_left, qsum_comm] at hPt
    exact hPt
  rw [qsum_interleaveDfmBranches (fun φ => QVec.queryMassOn T φ), twoMulPlusOne_eq] at hMass
  apply Nat.le_trans hMass
  apply Nat.mul_le_mul_left (2 * q + 1)
  unfold dfmEventEnvelope
  apply Nat.add_le_add_right
  apply qsum_le_qsum; intro t
  have hPosNorm :
      QVec.queryMassOn T (posB t) ≤
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) xStar := by
    have h1 := QVec.queryMassOn_le_stateNormSq T (posB t)
    dsimp only [posB] at h1
    rw [applySuffixFrom_normSq, oracleXor_isometry, projSingle_normSq] at h1
    exact h1
  have hNegNorm :
      QVec.queryMassOn T (negB t) ≤
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) xStar := by
    have h1 := QVec.queryMassOn_le_stateNormSq T (negB t)
    dsimp only [negB] at h1
    rw [negQVec_normSq, applySuffixFrom_normSq, oracleXor_isometry, projSingle_normSq] at h1
    exact h1
  omega

private theorem qsum_queryMassOn_fiber {cardX w cardAnc : Nat}
    (proj : Fin cardX → Fin cardX) (ψ : QVec cardX w cardAnc) :
    qsum cardX (fun xStar => QVec.queryMassOn (fun x => decide (xStar = proj x)) ψ) =
      QVec.stateNormSq ψ := by
  unfold QVec.queryMassOn QVec.stateNormSq
  rw [qsum_comm]
  apply qsum_congr; intro x
  have h : qsum cardX (fun xs =>
      if decide (xs = proj x) = true then QVec.queryWeight ψ x else 0) =
      qsum cardX (fun xs => if xs = proj x then QVec.queryWeight ψ x else 0) := by
    apply qsum_congr; intro xs
    simp only [decide_eq_true_eq]
  rw [h, qsum_ite_eq]

private theorem queryMassOn_point_eq {cardX w cardAnc : Nat}
    (ψ : QVec cardX w cardAnc) (xStar : Fin cardX) :
    QVec.queryMassOn (fun x => decide (xStar = x)) ψ = QVec.queryWeight ψ xStar := by
  unfold QVec.queryMassOn
  have hEq : qsum cardX (fun x =>
      if decide (xStar = x) = true then QVec.queryWeight ψ x else 0) =
      qsum cardX (fun x => if x = xStar then QVec.queryWeight ψ xStar else 0) := by
    apply qsum_congr; intro x
    by_cases hx : x = xStar
    · subst hx; simp
    · have hx' : ¬ xStar = x := fun h => hx h.symm
      simp [hx, hx']
  rw [hEq, qsum_ite_eq]

private theorem sum_dfmEventEnvelope_fiber_eq {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX) :
    qsum cardX (fun xStar =>
      dfmEventEnvelope A H xStar (fun x => decide (xStar = proj x))) =
      (2 * q + 1) * QVec.stateNormSq (runQuantumAdv A H) := by
  unfold dfmEventEnvelope
  rw [qsum_add, qsum_comm, qsum_queryMassOn_fiber]
  have hEachT :
      qsum q (fun t =>
        qsum cardX (fun xStar =>
          2 * (suffixScale A t.1 (Nat.le_of_lt t.2) *
            QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) xStar))) =
      qsum q (fun _ => 2 * QVec.stateNormSq (runQuantumAdv A H)) := by
    apply qsum_congr; intro t
    rw [qsum_mul_left 2, qsum_mul_left (suffixScale A t.1 (Nat.le_of_lt t.2))]
    change 2 * (suffixScale A t.1 (Nat.le_of_lt t.2) *
        QVec.stateNormSq (advStateAt A H t.1 (Nat.le_of_lt t.2))) = _
    rw [advStateAt_normSq, ← Nat.mul_assoc (suffixScale A t.1 _),
        Nat.mul_comm (suffixScale A t.1 _), prefix_mul_suffix_eq_total,
        ← runQuantumAdv_normSq A H]
  rw [hEachT, qsum_const]
  rw [← Nat.mul_assoc q 2, Nat.mul_comm q 2, Nat.add_mul, Nat.one_mul]

/-- **Projected Unitary Measure-and-Reprogram RBR Step
    (`qrom_unitary_measure_reprogram_rbr_step_projected`)**:
    For ANY `Q`-query unitary quantum adversary `A` (arbitrary scaled unitaries between
    superposition oracle calls, i.e. fully adaptive), ANY background oracle `H`, and ANY
    projection `proj` from the adversary's final OUTPUT register to the Fiat–Shamir query point
    it must be consistent with (in a transcript-chained `k`-round protocol the output is the full
    transcript and `proj` returns its round-`r` prefix), the total Born mass of outputs whose
    projected point `xStar = proj x` is doomed and is reprogrammed to a flipping challenge is at
    most **`(2 * Q + 1)^2 * badCard / 2^w`**. The fibers `{x | proj x = xStar}` are disjoint, so
    the bound does NOT pay for the size of the output register. -/
theorem qrom_unitary_measure_reprogram_rbr_step_projected
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX)
    (isDoomed : Fin cardX → Bool)
    (flipsToLive : Fin cardX → BitVec w → Bool)
    (badCard : Nat)
    (hRbr : ∀ x : Fin cardX, isDoomed x = true →
      qsum (2 ^ w) (fun j => if flipsToLive x (BitVec.ofFin j) = true then 1 else 0) ≤ badCard) :
    RatBound.le
      ⟨qsum cardX (fun xStar =>
         if isDoomed xStar = true then
           qsum (2 ^ w) (fun j =>
             if flipsToLive xStar (BitVec.ofFin j) = true then
               QVec.queryMassOn (fun x => decide (xStar = proj x))
                 (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
             else 0)
         else 0),
       2 ^ w * QVec.stateNormSq (runQuantumAdv A H),
       Nat.mul_pos (Nat.two_pow_pos w) (runQuantumAdv_normSq_pos A H)⟩
      ⟨(2 * Q + 1) ^ 2 * badCard, 2 ^ w, Nat.two_pow_pos w⟩ := by
  dsimp only [RatBound.le]
  let normFinal := QVec.stateNormSq (runQuantumAdv A H)
  have hPerX :
      qsum cardX (fun xStar =>
        if isDoomed xStar = true then
          qsum (2 ^ w) (fun j =>
            if flipsToLive xStar (BitVec.ofFin j) = true then
              QVec.queryMassOn (fun x => decide (xStar = proj x))
                (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
            else 0)
        else 0) ≤
      qsum cardX (fun xStar =>
        badCard * ((2 * Q + 1) *
          dfmEventEnvelope A H xStar (fun x => decide (xStar = proj x)))) := by
    apply qsum_le_qsum; intro xStar
    cases hD : isDoomed xStar
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
    · simp only [↓reduceIte]
      have hIn :
          qsum (2 ^ w) (fun j =>
            if flipsToLive xStar (BitVec.ofFin j) = true then
              QVec.queryMassOn (fun x => decide (xStar = proj x))
                (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
            else 0) ≤
          qsum (2 ^ w) (fun j =>
            (if flipsToLive xStar (BitVec.ofFin j) = true then 1 else 0) *
              ((2 * Q + 1) *
                dfmEventEnvelope A H xStar (fun x => decide (xStar = proj x)))) := by
        apply qsum_le_qsum; intro j
        cases flipsToLive xStar (BitVec.ofFin j)
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.le_refl]
        · simp only [↓reduceIte, Nat.one_mul]
          exact queryMassOn_reprogram_le_dfmEventEnvelope A H xStar (BitVec.ofFin j) _
      rw [qsum_mul_right] at hIn
      exact Nat.le_trans hIn
        (Nat.mul_le_mul_right _ (hRbr xStar hD))
  rw [qsum_mul_left badCard, qsum_mul_left (2 * Q + 1),
      sum_dfmEventEnvelope_fiber_eq] at hPerX
  have hSqEq : badCard * ((2 * Q + 1) * ((2 * Q + 1) * normFinal)) =
      (2 * Q + 1) ^ 2 * badCard * normFinal := by
    rw [Nat.pow_two, ← Nat.mul_assoc (2 * Q + 1) (2 * Q + 1) normFinal,
        Nat.mul_left_comm badCard ((2 * Q + 1) * (2 * Q + 1)) normFinal,
        Nat.mul_assoc ((2 * Q + 1) * (2 * Q + 1)) badCard normFinal]
  rw [hSqEq] at hPerX
  have hMul2w := Nat.mul_le_mul_right (2 ^ w) hPerX
  have hRhsEq : (2 * Q + 1) ^ 2 * badCard * normFinal * 2 ^ w =
      (2 * Q + 1) ^ 2 * badCard * (2 ^ w * normFinal) := by
    rw [Nat.mul_assoc ((2 * Q + 1) ^ 2 * badCard) normFinal (2 ^ w),
        Nat.mul_comm normFinal (2 ^ w)]
  rwa [hRhsEq] at hMul2w

/-- **Unitary Measure-and-Reprogram Single-Round RBR Theorem
    (`qrom_unitary_measure_reprogram_rbr_step`)**: the special case `proj = id` of
    `qrom_unitary_measure_reprogram_rbr_step_projected` (the output register IS the reprogrammed
    query point): the exact Born-rule RBR transition probability is bounded by
    **`(2 * Q + 1)^2 * badCard / 2^w`**. -/
theorem qrom_unitary_measure_reprogram_rbr_step
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (H : Fin cardX → BitVec w)
    (isDoomed : Fin cardX → Bool)
    (flipsToLive : Fin cardX → BitVec w → Bool)
    (badCard : Nat)
    (hRbr : ∀ x : Fin cardX, isDoomed x = true →
      qsum (2 ^ w) (fun j => if flipsToLive x (BitVec.ofFin j) = true then 1 else 0) ≤ badCard) :
    let normFinal := QVec.stateNormSq (runQuantumAdv A H)
    RatBound.le
      ⟨qsum cardX (fun xStar =>
         if isDoomed xStar = true then
           qsum (2 ^ w) (fun j =>
             if flipsToLive xStar (BitVec.ofFin j) = true then
               QVec.queryWeight (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j))) xStar
             else 0)
         else 0),
       2 ^ w * normFinal,
       Nat.mul_pos (Nat.two_pow_pos w) (runQuantumAdv_normSq_pos A H)⟩
      ⟨(2 * Q + 1) ^ 2 * badCard, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have h := qrom_unitary_measure_reprogram_rbr_step_projected A H id isDoomed flipsToLive
    badCard hRbr
  dsimp only [RatBound.le] at h ⊢
  refine Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_eq ?_)) h
  apply qsum_congr; intro xStar
  cases isDoomed xStar
  · rfl
  · simp only [↓reduceIte]
    apply qsum_congr; intro j
    cases flipsToLive xStar (BitVec.ofFin j)
    · rfl
    · simp only [↓reduceIte]
      exact (queryMassOn_point_eq _ xStar).symm

/-- **Oracle-Dependent (Adaptive Across Rounds) Measure-and-Reprogram Step
    (`qrom_adaptive_oracle_dependent_rbr_step`)**:
    In a multi-round Fiat–Shamir transcript, whether the round-`r` point `xStar` is doomed, and
    whether its challenge makes it live, depend on the ORACLE (through the challenges of earlier
    rounds). Both predicates here take the oracle as an argument and are evaluated on the very
    oracle `H[xStar ↦ ch]` the adversary ran against. The only structural requirement is
    acyclicity (`hLocal`): doomedness of `xStar` does not read the oracle AT `xStar`. -/
theorem qrom_adaptive_oracle_dependent_rbr_step
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX)
    (isDoomedAt : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (isLiveAfter : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (badCard : Nat)
    (hLocal : ∀ (x : Fin cardX) (ch : BitVec w),
      isDoomedAt (reprogramOracle H x ch) x = isDoomedAt H x)
    (hRbr : ∀ x : Fin cardX, isDoomedAt H x = true →
      qsum (2 ^ w) (fun j =>
        if isLiveAfter (reprogramOracle H x (BitVec.ofFin j)) x = true then 1 else 0) ≤ badCard) :
    RatBound.le
      ⟨qsum cardX (fun xStar =>
         qsum (2 ^ w) (fun j =>
           if (isDoomedAt (reprogramOracle H xStar (BitVec.ofFin j)) xStar &&
               isLiveAfter (reprogramOracle H xStar (BitVec.ofFin j)) xStar) = true then
             QVec.queryMassOn (fun x => decide (xStar = proj x))
               (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
           else 0)),
       2 ^ w * QVec.stateNormSq (runQuantumAdv A H),
       Nat.mul_pos (Nat.two_pow_pos w) (runQuantumAdv_normSq_pos A H)⟩
      ⟨(2 * Q + 1) ^ 2 * badCard, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have h := qrom_unitary_measure_reprogram_rbr_step_projected A H proj (isDoomedAt H)
    (fun x ch => isLiveAfter (reprogramOracle H x ch) x) badCard hRbr
  dsimp only [RatBound.le] at h ⊢
  refine Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_eq ?_)) h
  apply qsum_congr; intro xStar
  simp only [hLocal]
  cases isDoomedAt H xStar
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]
  · simp only [Bool.true_and, ↓reduceIte]

/-- One Fiat–Shamir round of a transcript-chained multi-round protocol as seen by the QROM
    reduction against the fixed background oracle `H`: the projection from the adversary's output
    to this round's query point, the oracle-dependent doomed / live-after predicates, and the
    round's bad-challenge count with its acyclicity and RBR flip-bound obligations. -/
structure QromRbrRound (cardX w : Nat) (H : Fin cardX → BitVec w) where
  proj : Fin cardX → Fin cardX
  isDoomedAt : (Fin cardX → BitVec w) → Fin cardX → Bool
  isLiveAfter : (Fin cardX → BitVec w) → Fin cardX → Bool
  badCard : Nat
  doomed_local : ∀ (x : Fin cardX) (ch : BitVec w),
    isDoomedAt (reprogramOracle H x ch) x = isDoomedAt H x
  flip_bound : ∀ x : Fin cardX, isDoomedAt H x = true →
    qsum (2 ^ w) (fun j =>
      if isLiveAfter (reprogramOracle H x (BitVec.ofFin j)) x = true then 1 else 0) ≤ badCard

/-- **Inhabited, oracle-dependent `QromRbrRound`**: over `Fin 2 → BitVec 2`, the round whose
    point is always doomed and becomes live exactly when the REPROGRAMMED oracle value at that
    point is zero has `badCard = 1`, attained with equality at every point. -/
def qromZeroChallengeRound (H : Fin 2 → BitVec 2) : QromRbrRound 2 2 H where
  proj := id
  isDoomedAt := fun _ _ => true
  isLiveAfter := fun O x => decide ((O x).toNat = 0)
  badCard := 1
  doomed_local := fun _ _ => rfl
  flip_bound := fun x _ => by
    have hEq : ∀ j : Fin (2 ^ 2),
        decide (((reprogramOracle H x (BitVec.ofFin j)) x).toNat = 0) = decide (j.1 = 0) := by
      intro j
      simp only [reprogramOracle, ↓reduceIte, BitVec.toNat_ofFin]
    rw [qsum_congr (fun j => by rw [hEq j])]
    decide

/-- Total reprogrammed Born mass of the doomed-to-live flip event of round `rd`. -/
def qromRoundFlipMass {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (H : Fin cardX → BitVec w)
    (rd : QromRbrRound cardX w H) : Nat :=
  qsum cardX (fun xStar =>
    qsum (2 ^ w) (fun j =>
      if (rd.isDoomedAt (reprogramOracle H xStar (BitVec.ofFin j)) xStar &&
          rd.isLiveAfter (reprogramOracle H xStar (BitVec.ofFin j)) xStar) = true then
        QVec.queryMassOn (fun x => decide (xStar = rd.proj x))
          (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
      else 0))

/-- **`k`-Round QROM Measure-and-Reprogram Union Theorem
    (`qrom_multiRound_measure_reprogram_union`)**:
    For ANY `Q`-query unitary adversary and ANY list of Fiat–Shamir rounds, the summed
    doomed-to-live flip mass over all rounds is at most
    **`(2 * Q + 1)^2 * (∑_r badCard_r) / 2^w`**: each round pays `(2 * Q + 1)^2` once (no
    `(2 * Q + 1)^{2k}` blow-up), derived from the unitary step theorem rather than assumed. -/
theorem qrom_multiRound_measure_reprogram_union
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (H : Fin cardX → BitVec w) :
    ∀ (rounds : List (QromRbrRound cardX w H)),
      RatBound.le
        ⟨(rounds.map (qromRoundFlipMass A H)).sum,
         2 ^ w * QVec.stateNormSq (runQuantumAdv A H),
         Nat.mul_pos (Nat.two_pow_pos w) (runQuantumAdv_normSq_pos A H)⟩
        ⟨(2 * Q + 1) ^ 2 * (rounds.map (fun rd => rd.badCard)).sum, 2 ^ w, Nat.two_pow_pos w⟩
  | [] => by
    show 0 * 2 ^ w ≤ _
    rw [Nat.zero_mul]
    exact Nat.zero_le _
  | rd :: rest => by
    have ih := qrom_multiRound_measure_reprogram_union A H rest
    have h1 : qromRoundFlipMass A H rd * 2 ^ w ≤
        (2 * Q + 1) ^ 2 * rd.badCard * (2 ^ w * QVec.stateNormSq (runQuantumAdv A H)) :=
      qrom_adaptive_oracle_dependent_rbr_step A H rd.proj rd.isDoomedAt rd.isLiveAfter
        rd.badCard rd.doomed_local rd.flip_bound
    have ih' : (rest.map (qromRoundFlipMass A H)).sum * 2 ^ w ≤
        (2 * Q + 1) ^ 2 * (rest.map (fun rd => rd.badCard)).sum *
          (2 ^ w * QVec.stateNormSq (runQuantumAdv A H)) := ih
    show (qromRoundFlipMass A H rd + (rest.map (qromRoundFlipMass A H)).sum) * 2 ^ w ≤
      (2 * Q + 1) ^ 2 * (rd.badCard + (rest.map (fun rd => rd.badCard)).sum) *
        (2 ^ w * QVec.stateNormSq (runQuantumAdv A H))
    rw [Nat.add_mul, Nat.mul_add, Nat.add_mul]
    exact Nat.add_le_add h1 ih'

/-- Sum over every oracle `Fin n → BitVec w`, with each function occurring once.
    The recursion is the constructive product enumeration of the finite output alphabet. -/
def uniformOracleSum (w : Nat) : (n : Nat) → ((Fin n → BitVec w) → Nat) → Nat
  | 0, f => f Fin.elim0
  | n + 1, f => qsum (2 ^ w) (fun j =>
      uniformOracleSum w n (fun H => f (Fin.cases (BitVec.ofFin j) H)))

theorem uniformOracleSum_congr (w : Nat) : ∀ (n : Nat)
    (f g : (Fin n → BitVec w) → Nat), (∀ H, f H = g H) →
    uniformOracleSum w n f = uniformOracleSum w n g
  | 0, _, _, h => h _
  | n + 1, _, _, h => qsum_congr (fun _ => uniformOracleSum_congr w n _ _ (fun _ => h _))

theorem uniformOracleSum_const (w : Nat) : ∀ (n c : Nat),
    uniformOracleSum w n (fun _ => c) = (2 ^ w) ^ n * c
  | 0, c => (Nat.one_mul c).symm
  | n + 1, c => by
    simp only [uniformOracleSum, uniformOracleSum_const w n c, qsum_const,
      Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

theorem uniformOracleSum_mul (w : Nat) : ∀ (n c : Nat)
    (f : (Fin n → BitVec w) → Nat),
    uniformOracleSum w n (fun H => c * f H) = c * uniformOracleSum w n f
  | 0, _, _ => rfl
  | n + 1, c, f => by
    simp only [uniformOracleSum, uniformOracleSum_mul w n c, qsum_mul_left]

theorem uniformOracleSum_le (w : Nat) : ∀ (n : Nat)
    (f g : (Fin n → BitVec w) → Nat), (∀ H, f H ≤ g H) →
    uniformOracleSum w n f ≤ uniformOracleSum w n g
  | 0, _, _, h => h _
  | n + 1, _, _, h => qsum_le_qsum (fun _ => uniformOracleSum_le w n _ _ (fun _ => h _))

theorem uniformOracleSum_qsum (w : Nat) : ∀ (n k : Nat)
    (f : (Fin n → BitVec w) → Fin k → Nat),
    uniformOracleSum w n (fun H => qsum k (f H)) =
      qsum k (fun j => uniformOracleSum w n (fun H => f H j))
  | 0, _, _ => rfl
  | n + 1, k, f => by
    simp only [uniformOracleSum, uniformOracleSum_qsum w n k]
    exact qsum_comm _ _ _

/-- Replacing one coordinate of a uniformly random oracle by an independent uniform
    challenge preserves its distribution. This identity applies to arbitrary oracle-dependent
    payoffs, including the Born mass of an adaptive adversary. No independence of the payoff
    from the reprogrammed coordinate is required. -/
theorem uniformOracleSum_resample (w : Nat) : ∀ (n : Nat) (x : Fin n)
    (f : (Fin n → BitVec w) → Nat),
    uniformOracleSum w n (fun H => qsum (2 ^ w) (fun j =>
      f (reprogramOracle H x (BitVec.ofFin j)))) =
      2 ^ w * uniformOracleSum w n f
  | 0, x, _ => Fin.elim0 x
  | n + 1, x, f => by
    refine Fin.cases ?_ (fun y => ?_) x
    · have heq : ∀ (a b : BitVec w) (H : Fin n → BitVec w),
          reprogramOracle (Fin.cases a H) 0 b = Fin.cases b H := by
        intro a b H
        funext z
        refine Fin.cases ?_ (fun i => ?_) z
        · simp [reprogramOracle]
        · simp [reprogramOracle, Fin.succ_ne_zero]
      simp only [uniformOracleSum, heq, uniformOracleSum_qsum]
      rw [qsum_const]
    · have heq : ∀ (a b : BitVec w) (H : Fin n → BitVec w),
          reprogramOracle (Fin.cases a H) y.succ b =
            Fin.cases a (reprogramOracle H y b) := by
        intro a b H
        funext z
        refine Fin.cases ?_ (fun i => ?_) z
        · simp [reprogramOracle, Ne.symm (Fin.succ_ne_zero y)]
        · simp [reprogramOracle, Fin.succ_inj]
      simp only [uniformOracleSum, heq]
      rw [← qsum_mul_left]
      apply qsum_congr
      intro j
      exact uniformOracleSum_resample w n y (fun H => f (Fin.cases (BitVec.ofFin j) H))

/-- A round's ordinary (unreprogrammed) success mass, summed over the projected output point. -/
def qromOrdinaryFlipMass {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX)
    (doomed live : (Fin cardX → BitVec w) → Fin cardX → Bool) : Nat :=
  qsum cardX (fun x => if (doomed H x && live H x) = true then
    QVec.queryMassOn (fun z => decide (x = proj z)) (runQuantumAdv A H) else 0)

/-- Exact bridge from the per-oracle reprogrammed mass to uniformly averaged ordinary
    adversary success mass. The factor `2^w` cancels the sampled-challenge denominator. -/
theorem qrom_uniform_oracle_flip_mass {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (round : (H : Fin cardX → BitVec w) → QromRbrRound cardX w H)
    (proj : Fin cardX → Fin cardX)
    (doomed live : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (hp : ∀ H, (round H).proj = proj)
    (hd : ∀ H, (round H).isDoomedAt = doomed)
    (hl : ∀ H, (round H).isLiveAfter = live) :
    uniformOracleSum w cardX (fun H => qromRoundFlipMass A H (round H)) =
      2 ^ w * uniformOracleSum w cardX (fun H =>
        qromOrdinaryFlipMass A H proj doomed live) := by
  simp only [qromRoundFlipMass, hp, hd, hl, qromOrdinaryFlipMass]
  rw [uniformOracleSum_qsum, uniformOracleSum_qsum, ← qsum_mul_left]
  apply qsum_congr
  intro x
  exact uniformOracleSum_resample w cardX x (fun H =>
    if (doomed H x && live H x) = true then
      QVec.queryMassOn (fun z => decide (x = proj z)) (runQuantumAdv A H) else 0)

/-- Averaged QROM round bound with a uniformly random oracle. The denominator is exactly
    the number of oracles times the adversary's oracle-independent squared norm. -/
theorem qrom_uniform_oracle_round_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (round : (H : Fin cardX → BitVec w) → QromRbrRound cardX w H)
    (proj : Fin cardX → Fin cardX)
    (doomed live : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (bad : Nat)
    (hp : ∀ H, (round H).proj = proj)
    (hd : ∀ H, (round H).isDoomedAt = doomed)
    (hl : ∀ H, (round H).isLiveAfter = live)
    (hb : ∀ H, (round H).badCard = bad) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => qromOrdinaryFlipMass A H proj doomed live),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * bad, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have hpoint : ∀ H, qromRoundFlipMass A H (round H) ≤
      (2 * Q + 1) ^ 2 * bad *
        (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init) := by
    intro H
    have h := qrom_multiRound_measure_reprogram_union A H [round H]
    change qromRoundFlipMass A H (round H) * 2 ^ w ≤
      (2 * Q + 1) ^ 2 * (round H).badCard *
        (2 ^ w * QVec.stateNormSq (runQuantumAdv A H)) at h
    rw [hb, runQuantumAdv_normSq] at h
    apply Nat.le_of_mul_le_mul_right (c := 2 ^ w) _ (Nat.two_pow_pos w)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have havg := uniformOracleSum_le w cardX _ _ hpoint
  rw [qrom_uniform_oracle_flip_mass A round proj doomed live hp hd hl,
    uniformOracleSum_const] at havg
  dsimp only [RatBound.le]
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using havg

/-- Uniform-oracle multi-round union bound. Each round may depend on the entire oracle;
    only its projection and predicate definitions are fixed across background-oracle choices.
    The adversary remains fully adaptive, and the reduction pays the quadratic loss once. -/
theorem qrom_uniform_oracle_multiRound_union {cardX w cardAnc Q k : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (round : Fin k → (H : Fin cardX → BitVec w) → QromRbrRound cardX w H)
    (proj : Fin k → Fin cardX → Fin cardX)
    (doomed live : Fin k → (Fin cardX → BitVec w) → Fin cardX → Bool)
    (bad : Fin k → Nat)
    (hp : ∀ r H, (round r H).proj = proj r)
    (hd : ∀ r H, (round r H).isDoomedAt = doomed r)
    (hl : ∀ r H, (round r H).isLiveAfter = live r)
    (hb : ∀ r H, (round r H).badCard = bad r) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => qsum k (fun r =>
          qromOrdinaryFlipMass A H (proj r) (doomed r) (live r))),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * qsum k bad, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have h := qsum_le_qsum (fun r => qrom_uniform_oracle_round_bound A (round r)
    (proj r) (doomed r) (live r) (bad r) (hp r) (hd r) (hl r) (hb r))
  dsimp only [RatBound.le] at h ⊢
  rw [uniformOracleSum_qsum]
  simpa only [qsum_mul_right, qsum_mul_left] using h

/-- Expected adversary success over a uniformly random oracle. A protocol supplies the
    ordinary round-flip covering property; averaging and measure-and-reprogram then give the
    same single quadratic loss as the per-oracle union theorem. -/
theorem qrom_uniform_oracle_success_bound {cardX w cardAnc Q k : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (accept : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (round : Fin k → (H : Fin cardX → BitVec w) → QromRbrRound cardX w H)
    (proj : Fin k → Fin cardX → Fin cardX)
    (doomed live : Fin k → (Fin cardX → BitVec w) → Fin cardX → Bool)
    (bad : Fin k → Nat)
    (hp : ∀ r H, (round r H).proj = proj r)
    (hd : ∀ r H, (round r H).isDoomedAt = doomed r)
    (hl : ∀ r H, (round r H).isLiveAfter = live r)
    (hb : ∀ r H, (round r H).badCard = bad r)
    (hCover : ∀ H, QVec.queryMassOn (accept H) (runQuantumAdv A H) ≤
      qsum k (fun r => qromOrdinaryFlipMass A H (proj r) (doomed r) (live r))) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => QVec.queryMassOn (accept H) (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * qsum k bad, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have h := qrom_uniform_oracle_multiRound_union A round proj doomed live bad hp hd hl hb
  exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ w)
    (uniformOracleSum_le w cardX _ _ hCover)) h

/-! ### §3.2 `k`-Round RBR Induction, Online Merkle Extraction & Concrete `Hem` v6 (`k = 5`) -/

/-- Exact `(2 * Q + 1)^2` Measure-and-Reprogram scaling of an interactive RBR round bound `b`. -/
@[expose] def dfmRoundScale (Q : Nat) (b : RatBound) : RatBound :=
  RatBound.scale ((2 * Q + 1) ^ 2) b

/-- Recompute a position-tweaked Merkle root from a node digest and its authentication path.
    `H lvl node` compresses the two children of node `node` at level `lvl`; `idx` is the index
    of the current node and its parity selects the child slot. -/
def merkleRootFromPath {D : Type} (H : Nat → Nat → D → D → D) : Nat → Nat → D → List D → D
  | _, _, cur, [] => cur
  | lvl, idx, cur, sib :: rest =>
    merkleRootFromPath H (lvl + 1) (idx / 2)
      (if idx % 2 = 0 then H lvl (idx / 2) cur sib else H lvl (idx / 2) sib cur) rest

/-- A collision of the tweaked compression function at ONE tree position: two different child
    pairs with the same digest under the same `(lvl, node)` tweak. -/
def MerkleTweakCollision {D : Type} (H : Nat → Nat → D → D → D) : Prop :=
  ∃ (lvl node : Nat) (a b a' b' : D), (a ≠ a' ∨ b ≠ b') ∧ H lvl node a b = H lvl node a' b'

/-- **Collision-or-unique-opening.** Two openings of the same position to the same root either
    coincide (same leaf digest, same authentication path) or exhibit a same-position collision
    of the tweaked compression function. This is the classical binding reduction behind the
    collision term of `qromMerkleOnlineExtractBound`; it is a statement about fixed openings
    and not the quantum online-extraction game. -/
theorem merkle_collision_or_unique_opening {D : Type} [DecidableEq D]
    (H : Nat → Nat → D → D → D) :
    ∀ (path path' : List D) (lvl idx : Nat) (leaf leaf' : D),
      path.length = path'.length →
      merkleRootFromPath H lvl idx leaf path = merkleRootFromPath H lvl idx leaf' path' →
      (leaf = leaf' ∧ path = path') ∨ MerkleTweakCollision H
  | [], [], _, _, _, _, _, h => .inl ⟨h, rfl⟩
  | [], _ :: _, _, _, _, _, hl, _ => absurd hl.symm (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, _, _, hl, _ => absurd hl (Nat.succ_ne_zero _)
  | sib :: rest, sib' :: rest', lvl, idx, leaf, leaf', hl, h => by
    have h' : merkleRootFromPath H (lvl + 1) (idx / 2)
          (if idx % 2 = 0 then H lvl (idx / 2) leaf sib else H lvl (idx / 2) sib leaf) rest =
        merkleRootFromPath H (lvl + 1) (idx / 2)
          (if idx % 2 = 0 then H lvl (idx / 2) leaf' sib' else H lvl (idx / 2) sib' leaf')
          rest' := h
    cases merkle_collision_or_unique_opening H rest rest' (lvl + 1) (idx / 2) _ _
        (Nat.succ.inj hl) h' with
    | inr hc => exact .inr hc
    | inl hp =>
      obtain ⟨hpar, hrest⟩ := hp
      if hEq : leaf = leaf' ∧ sib = sib' then
        exact .inl ⟨hEq.1, by rw [hEq.2, hrest]⟩
      else
        if hpar0 : idx % 2 = 0 then
          rw [ite_eq_left hpar0, ite_eq_left hpar0] at hpar
          refine .inr ?_
          unfold MerkleTweakCollision
          exact ⟨lvl, idx / 2, leaf, sib, leaf', sib',
            if hl1 : leaf = leaf' then .inr (fun hs => hEq ⟨hl1, hs⟩) else .inl hl1, hpar⟩
        else
          rw [ite_eq_right hpar0, ite_eq_right hpar0] at hpar
          refine .inr ?_
          unfold MerkleTweakCollision
          exact ⟨lvl, idx / 2, sib, leaf, sib', leaf',
            if hl1 : leaf = leaf' then .inl (fun hs => hEq ⟨hl1, hs⟩) else .inr hl1, hpar⟩

/-- `#tooth`: a compression function that forgets its right child is not binding, and the
    theorem's collision branch is the one that fires. -/
theorem tooth_merkle_right_blind_compression_collides :
    merkleRootFromPath (fun _ _ (a : Nat) _ => a) 0 0 7 [1] =
      merkleRootFromPath (fun _ _ (a : Nat) _ => a) 0 0 7 [2] ∧
    MerkleTweakCollision (fun _ _ (a : Nat) _ => a) := by
  refine ⟨rfl, ?_⟩
  unfold MerkleTweakCollision
  exact ⟨0, 0, 7, 1, 7, 2, .inr (by decide), rfl⟩

/-- Commitment-extraction CHARGE per committed Merkle root over `secBits`-bit digests:
    the single-target Grover term `8 (Q + 1)^2 / 2^secBits` plus the generic quantum collision
    term `8 (Q + 1)^3 / 2^secBits` (`quantumBhtCollisionBound`). Position tweaks confine a
    collision to one tree position (`merkle_collision_or_unique_opening`) but the adversary still
    chooses both preimages, so the cubic term cannot be dropped. This is a budget term in the
    shape of `[DFMS21]` / `[CMS19]`; the quantum online-extraction reduction for the deployed
    tree is NOT mechanized here. At `secBits = 256` the cubic term limits `128`-bit budgets to
    `Q + 1 ≤ 2^40`. -/
@[expose] def qromMerkleOnlineExtractBound (numRoots secBits Q : Nat) : RatBound :=
  RatBound.scale numRoots
    (RatBound.add (quantumGroverSingleTargetBound secBits Q) (quantumBhtCollisionBound secBits Q))

/-- Multi-round QROM Fiat–Shamir budget in the shape of `[DFMS19]` / `[CMS19]`:
    1. `k` reprogrammed RBR challenge rounds, `∑_r (2 Q + 1)^2 * rbrBounds[r]`;
    2. commitment extraction, `qromMerkleOnlineExtractBound`;
    3. query rounds under Fiat–Shamir search, `∑_j 8 (Q + 1)^2 * queryBounds[j]`
       (`quantumGroverGrindingBound`): the prover picks the grinding nonce before the queries are
       derived, so query soundness is a search bound in the oracle budget. `queryBounds` are
       PURE per-stage query errors; no proof-of-work density is credited on top of the search
       factor. -/
@[expose] def multiRoundFsQromCompilerBound
    (Q numRoots secBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) : RatBound :=
  RatBound.add
    (RatBound.sumList (rbrChallengeBounds.map (dfmRoundScale Q)))
    (RatBound.add
      (qromMerkleOnlineExtractBound numRoots secBits Q)
      (RatBound.sumList (queryStageBounds.map (quantumGroverGrindingBound Q))))

/-- **Constructive `k`-Round QROM RBR Induction Theorem (`rbr_multiRound_qrom_induction`)**:
    Starting from a doomed initial state (`liveAt 0 ≤ 0`), if each round `idx` satisfies
    `liveAt (idx + 1) ≤ liveAt idx + (2 * Q + 1)^2 * rbrBounds[idx]`, then after `k` rounds
    `liveAt k ≤ ∑_{idx < k} (2 * Q + 1)^2 * rbrBounds[idx]`! -/
theorem rbr_multiRound_qrom_induction
    (Q : Nat) :
    ∀ (rbrBounds : List RatBound) (liveAt : Nat → RatBound),
      RatBound.le (liveAt 0) RatBound.zero →
      (∀ (idx : Nat) (b : RatBound), rbrBounds[idx]? = some b →
        RatBound.le (liveAt (idx + 1)) (RatBound.add (liveAt idx) (dfmRoundScale Q b))) →
      RatBound.le (liveAt rbrBounds.length)
        (RatBound.sumList (rbrBounds.map (dfmRoundScale Q)))
  | [], liveAt, h0, _ => h0
  | b :: rest, liveAt, h0, hStep => by
    simp only [List.length_cons, List.map_cons, RatBound.sumList]
    have hFirst : RatBound.le (liveAt 1) (RatBound.add (liveAt 0) (dfmRoundScale Q b)) :=
      hStep 0 b rfl
    have hFirstSimp : RatBound.le (liveAt 1) (dfmRoundScale Q b) := by
      have hAdd0 := RatBound.add_le_add h0 (RatBound.le_refl (dfmRoundScale Q b))
      have hZeroAdd : RatBound.le (RatBound.add RatBound.zero (dfmRoundScale Q b))
          (dfmRoundScale Q b) := by
        unfold RatBound.le RatBound.add RatBound.zero
        dsimp only
        rw [Nat.zero_mul, Nat.zero_add, Nat.mul_one, Nat.one_mul]
        exact Nat.le_refl _
      exact RatBound.le_trans hFirst (RatBound.le_trans hAdd0 hZeroAdd)
    have hTail : ∀ (bs : List RatBound) (f : Nat → RatBound),
        (∀ (idx : Nat) (item : RatBound), bs[idx]? = some item →
          RatBound.le (f (idx + 1)) (RatBound.add (f idx) (dfmRoundScale Q item))) →
        RatBound.le (f bs.length)
          (RatBound.add (f 0) (RatBound.sumList (bs.map (dfmRoundScale Q)))) := by
      intro bs
      induction bs with
      | nil =>
        intro f _
        unfold RatBound.le RatBound.add RatBound.sumList RatBound.zero
        dsimp only [List.map, List.length_nil]
        rw [Nat.zero_mul, Nat.add_zero, Nat.mul_one, Nat.mul_one]
        exact Nat.le_refl _
      | cons hd tl ih =>
        intro f hf
        have h1 := hf 0 hd rfl
        have ihShift := ih (fun i => f (i + 1)) (fun idx item hGet => hf (idx + 1) item hGet)
        simp only [List.length_cons, List.map_cons, RatBound.sumList]
        have hStepAdd := RatBound.add_le_add h1
          (RatBound.le_refl (RatBound.sumList (tl.map (dfmRoundScale Q))))
        have hAssoc : RatBound.le
            (RatBound.add (RatBound.add (f 0) (dfmRoundScale Q hd))
              (RatBound.sumList (tl.map (dfmRoundScale Q))))
            (RatBound.add (f 0)
              (RatBound.add (dfmRoundScale Q hd)
                (RatBound.sumList (tl.map (dfmRoundScale Q))))) := by
          unfold RatBound.le RatBound.add
          dsimp only
          have hEq :
              ((f 0).num * (dfmRoundScale Q hd).den + (dfmRoundScale Q hd).num * (f 0).den) *
                (RatBound.sumList (tl.map (dfmRoundScale Q))).den +
              (RatBound.sumList (tl.map (dfmRoundScale Q))).num *
                ((f 0).den * (dfmRoundScale Q hd).den) =
              (f 0).num * ((dfmRoundScale Q hd).den *
                (RatBound.sumList (tl.map (dfmRoundScale Q))).den) +
              ((dfmRoundScale Q hd).num * (RatBound.sumList (tl.map (dfmRoundScale Q))).den +
                (RatBound.sumList (tl.map (dfmRoundScale Q))).num * (dfmRoundScale Q hd).den) *
                (f 0).den := by
            rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
            congr 1
            rw [Nat.mul_right_comm ((dfmRoundScale Q hd).num),
                Nat.mul_comm (f 0).den (dfmRoundScale Q hd).den,
                ← Nat.mul_assoc]
          have hDenEq :
              (f 0).den * (dfmRoundScale Q hd).den *
                (RatBound.sumList (tl.map (dfmRoundScale Q))).den =
              (f 0).den * ((dfmRoundScale Q hd).den *
                (RatBound.sumList (tl.map (dfmRoundScale Q))).den) :=
            Nat.mul_assoc _ _ _
          rw [hEq, hDenEq]
          exact Nat.le_refl _
        exact RatBound.le_trans ihShift (RatBound.le_trans hStepAdd hAssoc)
    have hRestBound := hTail rest (fun i => liveAt (i + 1)) (fun idx item hGet => hStep (idx + 1) item hGet)
    exact RatBound.le_trans hRestBound
      (RatBound.add_le_add hFirstSimp (RatBound.le_refl _))

/-- Round-0 batch RBR bound over `QuarticGoldilocks`, DERIVED from the deployed `nv = 24` stage-0
    witness: at most `MAX_BATCH_POLYS - 1 = 15` asymmetric-cascade affine combinations, each at
    the stage-0 per-fold `[CWYZ26]` numerator `ℓ + 2 ℓ₀ + 1`, plus the `72 / p^4` `Ext4`
    point-reduction sumcheck. -/
def hemV6CascadeRbrBound : RatBound :=
  match whirAffineStageWitnesses 24 true with
  | w :: _ =>
    ⟨15 * (whirAffineStageSimpleNum w / w.sFolds) + 72, goldilocksExt4Card, goldilocksExt4Card_pos⟩
  | [] => RatBound.one

/-- RBR challenge-round error bounds for `Hem` v6 (`nv = 24`) over `QuarticGoldilocks`
    (`q = goldilocksExt4Card = p^4`), DERIVED from the deployed witnesses rather than literals:
    the round-0 cascade bound followed by, for each of the `4` WHIR stages, the `[CWYZ26]`
    Theorem 4.8 + 5.1 bound `whirAffineEqualDegreeCommitFoldBound` of the deployed
    `whirAffineStageWitnesses 24 true` row. Each stage entry is the SUM over that stage's `s_i`
    fold rounds (`s_i (ℓ + 2 ℓ₀ + 1) / p^4`); the per-round Measure-and-Reprogram factor
    `(2 Q + 1)^2` is linear, so scaling the aggregate equals summing the scaled rounds. -/
def hemV6FiveRoundRbrBounds : List RatBound :=
  hemV6CascadeRbrBound ::
    (whirAffineStageWitnesses 24 true).map whirAffineEqualDegreeCommitFoldBound

/-- The derived round bounds evaluate to `(4182, 1644, 824, 489, 792) / p^4` (total `7931 / p^4`). -/
theorem hemV6FiveRoundRbrBounds_eq_deployed :
    hemV6FiveRoundRbrBounds.map (fun b => (b.num, b.den)) =
      [4182, 1644, 824, 489, 792].map (fun n => (n, goldilocksExt4Card)) := by
  decide +kernel

/-- Pure 4-stage `Hem` v6 coset-query error bounds under default `BciksJohnsonQrom128`, DERIVED
    from the same deployed `whirAffineStageWitnesses 24 true` rows as the fold bounds: the exact
    distinct-fiber bound `(A + s_i)_{q_i} / (n)_{q_i}` at each row's own agreement threshold
    (`whirAffine_deployed_pure_query_bounds`), with no proof-of-work density. -/
def hemV6BciksJohnsonQueryBounds : List RatBound :=
  (whirAffineStageWitnesses 24 true).map whirAffinePureQueryBoundOrOne

private theorem hemCompiler_budget_up_to (QMax digestBits : Nat)
    (hBciksMax : strictlyMoreThanBits 128
      (multiRoundFsQromCompilerBound QMax 5 digestBits
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds)) :
    ∀ Q : Nat, Q ≤ QMax →
      strictlyMoreThanBits 128 (multiRoundFsQromCompilerBound Q 5 digestBits
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) ∧
      atLeastBits 128 (multiRoundFsQromCompilerBound Q 5 digestBits
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) := by
  have hMonoScale : ∀ {a b : Nat} (hab : a ≤ b) (r : RatBound),
      RatBound.le (RatBound.scale a r) (RatBound.scale b r) := by
    intro a b hab r
    unfold RatBound.le RatBound.scale
    dsimp only
    exact Nat.mul_le_mul_right r.den (Nat.mul_le_mul_right r.num hab)
  have hScaleMono : ∀ (k : Nat) {a b : RatBound},
      RatBound.le a b → RatBound.le (RatBound.scale k a) (RatBound.scale k b) := by
    intro k a b h
    unfold RatBound.le at h
    unfold RatBound.le RatBound.scale
    dsimp only
    rw [Nat.mul_assoc, Nat.mul_assoc]
    exact Nat.mul_le_mul_left k h
  have hMonoSum : ∀ (xs ys : List RatBound) (hLen : xs.length = ys.length),
      (∀ i : Fin xs.length, RatBound.le (xs.get i) (ys.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 hLen⟩)) →
      RatBound.le (RatBound.sumList xs) (RatBound.sumList ys) := by
    intro xs
    induction xs with
    | nil =>
      intro ys hLen _
      cases ys with
      | nil => exact RatBound.le_refl _
      | cons _ _ => exact absurd hLen.symm (Nat.succ_ne_zero _)
    | cons x xs' ih =>
      intro ys hLen hPt
      cases ys with
      | nil => exact absurd hLen (Nat.succ_ne_zero _)
      | cons y ys' =>
        have hLen' : xs'.length = ys'.length := Nat.succ.inj hLen
        simp only [RatBound.sumList]
        exact RatBound.add_le_add
          (hPt ⟨0, Nat.zero_lt_succ _⟩)
          (ih ys' hLen' (fun i => hPt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))
  have hStrictOfLe : ∀ {b₁ b₂ : RatBound},
      RatBound.le b₁ b₂ → strictlyMoreThanBits 128 b₂ → strictlyMoreThanBits 128 b₁ := by
    intro b₁ b₂ hLe hStrict
    unfold RatBound.le at hLe
    unfold strictlyMoreThanBits at hStrict ⊢
    have h1 : b₁.num * 2 ^ 128 * b₂.den ≤ b₂.num * 2 ^ 128 * b₁.den := by
      have hm := Nat.mul_le_mul_right (2 ^ 128) hLe
      have e1 : b₁.num * b₂.den * 2 ^ 128 = b₁.num * 2 ^ 128 * b₂.den := by
        rw [Nat.mul_right_comm]
      have e2 : b₂.num * b₁.den * 2 ^ 128 = b₂.num * 2 ^ 128 * b₁.den := by
        rw [Nat.mul_right_comm]
      rwa [e1, e2] at hm
    have h2 : b₂.num * 2 ^ 128 * b₁.den < b₂.den * b₁.den :=
      Nat.mul_lt_mul_of_pos_right hStrict b₁.h_pos
    have h3 : b₁.num * 2 ^ 128 * b₂.den < b₁.den * b₂.den := by
      rw [Nat.mul_comm b₁.den b₂.den]
      exact Nat.lt_of_le_of_lt h1 h2
    if hLt : b₁.num * 2 ^ 128 < b₁.den then
      exact hLt
    else
      exfalso
      have hGe := Nat.mul_le_mul_right b₂.den (Nat.le_of_not_lt hLt)
      exact Nat.not_le_of_gt h3 hGe
  have hCompilerMono : ∀ {Q : Nat} (hQ : Q ≤ QMax) (qBounds : List RatBound),
      RatBound.le
        (multiRoundFsQromCompilerBound Q 5 digestBits hemV6FiveRoundRbrBounds qBounds)
        (multiRoundFsQromCompilerBound QMax 5 digestBits hemV6FiveRoundRbrBounds qBounds) := by
    intro Q hQ qBounds
    unfold multiRoundFsQromCompilerBound
    have hSqLe : (2 * Q + 1) ^ 2 ≤ (2 * QMax + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hRbrLe :
        RatBound.le
          (RatBound.sumList (hemV6FiveRoundRbrBounds.map (dfmRoundScale Q)))
          (RatBound.sumList (hemV6FiveRoundRbrBounds.map (dfmRoundScale QMax))) := by
      apply hMonoSum _ _ (by simp only [List.length_map])
      intro i
      simp only [List.get_eq_getElem, List.getElem_map]
      exact hMonoScale hSqLe _
    have hGrindLe : 8 * (Q + 1) ^ 2 ≤ 8 * (QMax + 1) ^ 2 :=
      Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (by omega) 2)
    have hQueryLe :
        RatBound.le
          (RatBound.sumList (qBounds.map (quantumGroverGrindingBound Q)))
          (RatBound.sumList (qBounds.map (quantumGroverGrindingBound QMax))) := by
      apply hMonoSum _ _ (by simp only [List.length_map])
      intro i
      simp only [List.get_eq_getElem, List.getElem_map]
      exact hMonoScale hGrindLe _
    have hMerkleLe :
        RatBound.le (qromMerkleOnlineExtractBound 5 digestBits Q)
          (qromMerkleOnlineExtractBound 5 digestBits QMax) := by
      unfold qromMerkleOnlineExtractBound
      apply hScaleMono
      apply RatBound.add_le_add
      · unfold RatBound.le quantumGroverSingleTargetBound quantumZhandryMultiTargetBound
        dsimp only
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
      · unfold RatBound.le quantumBhtCollisionBound
        dsimp only
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
    exact RatBound.add_le_add hRbrLe (RatBound.add_le_add hMerkleLe hQueryLe)
  intro Q hQ
  have hb := hStrictOfLe (hCompilerMono hQ hemV6BciksJohnsonQueryBounds) hBciksMax
  exact ⟨hb, Nat.le_of_lt hb⟩

/-- **Multi-round Fiat–Shamir QROM numerical budget (`multiRoundFsQrom_budget_bound`)**.
    For every oracle budget `Q + 1 ≤ 2^40`, `multiRoundFsQromCompilerBound` at the deployed
    `num_vars = 24` parameters (five aggregated RBR entries derived from the deployed witness
    rows, five committed Merkle roots over `256`-bit digests, four query stages) is strictly
    below `2^-128` for the witness-derived `BciksJohnsonQrom128` query bounds.

    The range is forced by the collision term of commitment extraction: at `Q + 1 = 2^41` the
    same expression exceeds `2^-128` (`tooth_multiRoundFsQrom_budget_fails_at_2pow41`).

    This is arithmetic about the budget expression. It becomes an acceptance-probability bound
    for the deployed verifier only together with (a) an `RbrStateFunction` for the `Hem`
    transcript whose flip bounds are the listed round bounds, which needs `[CWYZ26]`
    Theorem 4.8 at the Johnson radius, and (b) a quantum extraction reduction for the
    commitment charge. Neither is proved in this module. -/
theorem multiRoundFsQrom_budget_bound :
    hemV6FiveRoundRbrBounds.length = 5 ∧
    (∀ Q : Nat, Q + 1 ≤ 2 ^ 40 →
      strictlyMoreThanBits 128
        (multiRoundFsQromCompilerBound Q 5 256
          hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) ∧
      atLeastBits 128
        (multiRoundFsQromCompilerBound Q 5 256
          hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds)) := by
  refine ⟨by decide +kernel, ?_⟩
  intro Q hQ
  exact hemCompiler_budget_up_to (2 ^ 40 - 1) 256 (by decide +kernel) Q (by omega)


/-- `#tooth`: the oracle-budget range of `multiRoundFsQrom_budget_bound` is not slack. One more
    bit of budget (`Q + 1 = 2^41`) pushes the same expression above `2^-128`, through the
    `8 (Q + 1)^3 / 2^256` collision term of commitment extraction. -/
theorem tooth_multiRoundFsQrom_budget_fails_at_2pow41 :
    ¬ atLeastBits 128
      (multiRoundFsQromCompilerBound (2 ^ 41 - 1) 5 256
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) := by
  decide +kernel


/-! ## §4. Fiat–Shamir Ordering `#tooth` Witness (`tooth_unabsorbed_shifted_claim_breaks_rbr`) -/

/-- Expected `[CWYZ26]` §5.1 / `affine.rs:61` folded linear-functional claim
    `σ' = γ_G + α * (γ_F + θ * γ_G) + β * (c_F + θ * c_G)` over any commutative ring `F`. -/
def hemFoldClaimUpdate {F : Type} [CommRingOps F] (γ_F γ_G c_F c_G θ α β : F) : F :=
  CommRingOps.add γ_G
    (CommRingOps.add
      (CommRingOps.mul α (CommRingOps.add γ_F (CommRingOps.mul θ γ_G)))
      (CommRingOps.mul β (CommRingOps.add c_F (CommRingOps.mul θ c_G))))

/-- Explicit cheating shifted-claim calculation when a buggy Fiat–Shamir transcript squeezes
    `(θ, α, β)` BEFORE absorbing `(c_F, c_G)`: on the committed zero polynomial (`F = [], G = []`,
    true folded claim `= 0`), chooses `c_G := 0` and `c_F := - β⁻¹ * (γ_G + α * (γ_F + θ * γ_G))`! -/
def cheatUnabsorbedShiftClaimGen {F : Type} [CommRingOps F] (inv : F → F)
    (γ_F γ_G θ α β : F) : F × F :=
  let baseTerm := CommRingOps.add γ_G
    (CommRingOps.mul α (CommRingOps.add γ_F (CommRingOps.mul θ γ_G)))
  (CommRingOps.mul (inv β) (CommRingOps.neg baseTerm), CommRingOps.zero)

def cheatUnabsorbedShiftClaim (γ_F γ_G θ α β : QuarticGoldilocks) :
    QuarticGoldilocks × QuarticGoldilocks :=
  cheatUnabsorbedShiftClaimGen QuarticGoldilocks.inv γ_F γ_G θ α β

/-- Checks whether an affine fold step from committed zero polynomials `(F = [], G = [])` with
    claimed `(γ_F, γ_G)` lands in a `live` (`true`) post-fold `StateFunction` state on the zero
    oracle (`hemFoldClaimUpdate γ_F γ_G c_F c_G θ α β = 0`). -/
def zeroPolyPostFoldStateLive {F : Type} [CommRingOps F] [DecidableEq F]
    (γ_F γ_G c_F c_G θ α β : F) : Bool :=
  decide (hemFoldClaimUpdate γ_F γ_G c_F c_G θ α β = CommRingOps.zero)

private theorem unabsorbed_shift_forgery_prob_one_poly
    {F : Type} [LawfulCommRing F] [DecidableEq F]
    (inv : F → F)
    (hInv : ∀ x : F, x ≠ CommRingOps.zero → CommRingOps.mul x (inv x) = CommRingOps.one)
    (γ_F γ_G : F) (S_θ S_α S_β : List F)
    (hθ : 0 < S_θ.length) (hα : 0 < S_α.length) (hβ : 0 < S_β.length)
    (hNz : ∀ β ∈ S_β, β ≠ CommRingOps.zero) :
    let totalCard := S_θ.length * (S_α.length * S_β.length)
    let hitCount :=
      qsum S_θ.length (fun i =>
        qsum S_α.length (fun j =>
          qsum S_β.length (fun k =>
            let θ := S_θ.get i
            let α := S_α.get j
            let β := S_β.get k
            let (c_F, c_G) := cheatUnabsorbedShiftClaimGen inv γ_F γ_G θ α β
            if zeroPolyPostFoldStateLive γ_F γ_G c_F c_G θ α β = true then 1 else 0)))
    hitCount = totalCard ∧
    RatBound.le RatBound.one
      ⟨hitCount, totalCard, Nat.mul_pos hθ (Nat.mul_pos hα hβ)⟩ ∧
    RatBound.le
      ⟨hitCount, totalCard, Nat.mul_pos hθ (Nat.mul_pos hα hβ)⟩
      RatBound.one := by
  dsimp only
  have hPointZero : ∀ (θ α β : F), β ≠ CommRingOps.zero →
      let (c_F, c_G) := cheatUnabsorbedShiftClaimGen inv γ_F γ_G θ α β
      hemFoldClaimUpdate γ_F γ_G c_F c_G θ α β = CommRingOps.zero := by
    intro θ α β hβNz
    dsimp only [cheatUnabsorbedShiftClaimGen, hemFoldClaimUpdate]
    let baseTerm := CommRingOps.add γ_G
      (CommRingOps.mul α (CommRingOps.add γ_F (CommRingOps.mul θ γ_G)))
    change CommRingOps.add γ_G
        (CommRingOps.add
          (CommRingOps.mul α (CommRingOps.add γ_F (CommRingOps.mul θ γ_G)))
          (CommRingOps.mul β
            (CommRingOps.add
              (CommRingOps.mul (inv β) (CommRingOps.neg baseTerm))
              (CommRingOps.mul θ CommRingOps.zero)))) = CommRingOps.zero
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
        ← LawfulCommRing.mul_assoc β (inv β) (CommRingOps.neg baseTerm),
        hInv β hβNz,
        LawfulCommRing.one_mul,
        ← LawfulCommRing.add_assoc γ_G _ (CommRingOps.neg baseTerm)]
    exact LawfulCommRing.add_right_neg baseTerm
  have hInnerβ : ∀ (θ α : F),
      qsum S_β.length (fun k =>
        let (c_F, c_G) := cheatUnabsorbedShiftClaimGen inv γ_F γ_G θ α (S_β.get k)
        if zeroPolyPostFoldStateLive γ_F γ_G c_F c_G θ α (S_β.get k) = true then 1 else 0) =
      S_β.length := by
    intro θ α
    have h1 : qsum S_β.length (fun k =>
        let (c_F, c_G) := cheatUnabsorbedShiftClaimGen inv γ_F γ_G θ α (S_β.get k)
        if zeroPolyPostFoldStateLive γ_F γ_G c_F c_G θ α (S_β.get k) = true then 1 else 0) =
        qsum S_β.length (fun _ => 1) := by
      apply qsum_congr; intro k
      have hkNz : S_β.get k ≠ CommRingOps.zero := hNz (S_β.get k) (List.get_mem S_β k)
      have hEq0 := hPointZero θ α (S_β.get k) hkNz
      dsimp only at hEq0
      unfold zeroPolyPostFoldStateLive
      simp only [hEq0, decide_true, ↓reduceIte]
    rw [h1, qsum_const, Nat.mul_one]
  have hInnerα : ∀ (θ : F),
      qsum S_α.length (fun j =>
        qsum S_β.length (fun k =>
          let (c_F, c_G) := cheatUnabsorbedShiftClaimGen inv γ_F γ_G θ (S_α.get j) (S_β.get k)
          if zeroPolyPostFoldStateLive γ_F γ_G c_F c_G θ (S_α.get j) (S_β.get k) = true then 1 else 0)) =
      S_α.length * S_β.length := by
    intro θ
    rw [qsum_congr (fun j => hInnerβ θ (S_α.get j)), qsum_const]
  have hHitEq :
      qsum S_θ.length (fun i =>
        qsum S_α.length (fun j =>
          qsum S_β.length (fun k =>
            let (c_F, c_G) := cheatUnabsorbedShiftClaimGen inv γ_F γ_G (S_θ.get i) (S_α.get j) (S_β.get k)
            if zeroPolyPostFoldStateLive γ_F γ_G c_F c_G (S_θ.get i) (S_α.get j) (S_β.get k) = true
            then 1 else 0))) =
      S_θ.length * (S_α.length * S_β.length) := by
    rw [qsum_congr (fun i => hInnerα (S_θ.get i)), qsum_const]
  refine ⟨hHitEq, ?_, ?_⟩
  · unfold RatBound.le RatBound.one; dsimp only; rw [hHitEq, Nat.one_mul, Nat.mul_one]; exact Nat.le_refl _
  · unfold RatBound.le RatBound.one; dsimp only; rw [hHitEq, Nat.one_mul, Nat.mul_one]; exact Nat.le_refl _

private theorem absorbed_shift_preserves_soundness_poly
    {F : Type} [LawfulCommRing F] [DecidableEq F]
    (c_F c_G θ : F) (S : List F) (hPos : 0 < S.length) (hNodup : S.Nodup) :
    let absorbedHits :=
      qsum S.length (fun i =>
        qsum S.length (fun j =>
          if zeroPolyPostFoldStateLive CommRingOps.one CommRingOps.zero
               c_F c_G θ (S.get i) (S.get j) = true then 1 else 0))
    absorbedHits ≤ S.length ∧
    RatBound.le
      ⟨absorbedHits, S.length ^ 2, Nat.pow_pos hPos⟩
      ⟨1, S.length, hPos⟩ := by
  dsimp only
  rw [qsum_comm]
  have hPerBeta : ∀ j : Fin S.length,
      qsum S.length (fun i =>
        if zeroPolyPostFoldStateLive CommRingOps.one CommRingOps.zero
             c_F c_G θ (S.get i) (S.get j) = true then 1 else 0) ≤ 1 := by
    intro j
    apply qsum_le_one_of_subsingleton
    intro i₁ i₂ h₁ h₂
    have e₁ : hemFoldClaimUpdate CommRingOps.one CommRingOps.zero
        c_F c_G θ (S.get i₁) (S.get j) = CommRingOps.zero := of_decide_eq_true h₁
    have e₂ : hemFoldClaimUpdate CommRingOps.one CommRingOps.zero
        c_F c_G θ (S.get i₂) (S.get j) = CommRingOps.zero := of_decide_eq_true h₂
    let shiftVal := CommRingOps.mul (S.get j) (CommRingOps.add c_F (CommRingOps.mul θ c_G))
    have hSimp : ∀ α : F,
        hemFoldClaimUpdate CommRingOps.one CommRingOps.zero c_F c_G θ α (S.get j) =
          CommRingOps.add α shiftVal := by
      intro α
      unfold hemFoldClaimUpdate
      rw [LawfulCommRing.zero_add, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
          LawfulCommRing.mul_one]
    rw [hSimp (S.get i₁)] at e₁
    rw [hSimp (S.get i₂)] at e₂
    have hEqAlpha : S.get i₁ = S.get i₂ := by
      have c1 := congrArg (fun u => CommRingOps.add u (CommRingOps.neg shiftVal)) e₁
      have c2 := congrArg (fun u => CommRingOps.add u (CommRingOps.neg shiftVal)) e₂
      rw [LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero,
          LawfulCommRing.zero_add] at c1 c2
      exact c1.trans c2.symm
    exact nodup_get_inj hNodup hEqAlpha
  have hHitsLe :
      qsum S.length (fun j =>
        qsum S.length (fun i =>
          if zeroPolyPostFoldStateLive CommRingOps.one CommRingOps.zero
               c_F c_G θ (S.get i) (S.get j) = true then 1 else 0)) ≤
      S.length := by
    have h1 := qsum_le_qsum hPerBeta
    rw [qsum_const, Nat.mul_one] at h1
    exact h1
  refine ⟨hHitsLe, ?_⟩
  unfold RatBound.le
  dsimp only
  rw [Nat.one_mul, Nat.pow_two]
  exact Nat.mul_le_mul_right S.length hHitsLe

/-- **`#tooth` Unabsorbed Shifted Claim Breaks RBR Soundness With Probability `1`
    (`tooth_unabsorbed_shifted_claim_breaks_rbr`)**:
    1. **False Initial Statement is Doomed**: committing the zero oracle over
       `QuarticGoldilocks` while claiming the non-zero evaluation `σ = 1` is outside the language
       for EVERY polynomial witness (`hemFalseClaimInstance_invalid`), so the empty transcript is
       doomed.
    2. **Buggy Squeeze-Before-Absorb Transcript Flips `false → true` With Exact Probability `1`**:
       When `(θ, α, β)` is squeezed BEFORE absorbing `(c_F, c_G)`, for EVERY challenge `(θ, α, β)`
       with `β ≠ 0` (`∀ β ∈ S_β, β ≠ 0`), `cheatUnabsorbedShiftClaim` flips `zeroPolyPostFoldStateLive`
       to `true` on **100% of challenges** (`hitCount = S_θ.length * S_α.length * S_β.length`,
       exact `RatBound` probability = `1 / 1 = RatBound.one`!).
    3. **Deployed `Hem` v6 Absorb-Before-Squeeze Ordering Preserves `≤ 1 / |S|` Soundness**:
       When `(c_F, c_G)` MUST be absorbed BEFORE squeezing `(α, β)` from any duplicate-free pool
       `S`, at `(γ_F = 1, γ_G = 0)`, at most `S.length` out of `S.length ^ 2` pairs (`≤ 1 / S.length`)
       flip `zeroPolyPostFoldStateLive` to `true`! -/
theorem tooth_unabsorbed_shifted_claim_breaks_rbr :
    (¬ hemAffineWhirStateFunction hemFalseClaimInstance []) ∧
    (∀ (γ_F γ_G : QuarticGoldilocks)
       (S_θ S_α S_β : List QuarticGoldilocks)
       (hθ : 0 < S_θ.length) (hα : 0 < S_α.length) (hβ : 0 < S_β.length),
       (∀ β ∈ S_β, β ≠ CommRingOps.zero) →
      let totalCard := S_θ.length * (S_α.length * S_β.length)
      let hitCount :=
        qsum S_θ.length (fun i =>
          qsum S_α.length (fun j =>
            qsum S_β.length (fun k =>
              let θ := S_θ.get i
              let α := S_α.get j
              let β := S_β.get k
              let (c_F, c_G) := cheatUnabsorbedShiftClaim γ_F γ_G θ α β
              if zeroPolyPostFoldStateLive γ_F γ_G c_F c_G θ α β = true then 1 else 0)))
      hitCount = totalCard ∧
      RatBound.le RatBound.one
        ⟨hitCount, totalCard, Nat.mul_pos hθ (Nat.mul_pos hα hβ)⟩ ∧
      RatBound.le
        ⟨hitCount, totalCard, Nat.mul_pos hθ (Nat.mul_pos hα hβ)⟩
        RatBound.one) ∧
    (∀ (c_F c_G θ : QuarticGoldilocks) (S : List QuarticGoldilocks)
       (hPos : 0 < S.length), S.Nodup →
      let absorbedHits :=
        qsum S.length (fun i =>
          qsum S.length (fun j =>
            if zeroPolyPostFoldStateLive CommRingOps.one CommRingOps.zero
                 c_F c_G θ (S.get i) (S.get j) = true then 1 else 0))
      absorbedHits ≤ S.length ∧
      RatBound.le
        ⟨absorbedHits, S.length ^ 2, Nat.pow_pos hPos⟩
        ⟨1, S.length, hPos⟩) := by
  refine ⟨hemFalseClaimInstance_invalid, ?_, ?_⟩
  · intro γ_F γ_G S_θ S_α S_β hθ hα hβ hNz
    exact unabsorbed_shift_forgery_prob_one_poly
      QuarticGoldilocks.inv
      (fun _ hx => QuarticGoldilocks.mul_inv_cancel hx)
      γ_F γ_G S_θ S_α S_β hθ hα hβ hNz
  · intro c_F c_G θ S hPos hNodup
    exact absorbed_shift_preserves_soundness_poly c_F c_G θ S hPos hNodup

/-- **Non-Vacuity & Inhabitedness Certificate (`inhabited_multi_round_fs_qrom`)**:
    Certifies that all concrete schedules, unitary quantum superposition adversaries (`hadamardQuery2`),
    honest `HemWhirInstance` transcripts, and `multiRoundFsQrom_budget_bound` budgets are
    strictly inhabited with positive numerators and non-trivial quantum/field witnesses! -/
theorem inhabited_multi_round_fs_qrom :
    0 < (multiRoundFsQromCompilerBound (2 ^ 39) 5 256
           hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds).num ∧
    (∃ (A : QuantumAdv 2 2 1 1) (H : Fin 2 → BitVec 2),
      0 < QVec.stateNormSq (runQuantumAdv A H) ∧
      RatBound.le
        ⟨qsum 2 (fun xStar =>
           qsum 4 (fun j =>
             if decide (j.1 = 0) = true then
               QVec.queryWeight (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j))) xStar
             else 0)),
         4 * QVec.stateNormSq (runQuantumAdv A H),
         Nat.mul_pos (by decide) (runQuantumAdv_normSq_pos A H)⟩
        ⟨(2 * 1 + 1) ^ 2 * 1, 4, by decide⟩) := by
  refine ⟨by decide +kernel, ?_⟩
  let initVec : QVec 2 2 1 := fun x y _ =>
    if x.1 == 0 && y.1 == 0 then GaussInt.one else GaussInt.zero
  have hInitPos : 0 < QVec.stateNormSq initVec := by
    unfold QVec.stateNormSq QVec.queryWeight initVec GaussInt.normSq GaussInt.one GaussInt.zero
    decide
  let A : QuantumAdv 2 2 1 1 :=
    { init := initVec
      h_init_pos := hInitPos
      steps := fun _ => hadamardQuery2 2 1 }
  let H : Fin 2 → BitVec 2 := fun _ => 0#2
  refine ⟨A, H, runQuantumAdv_normSq_pos A H, ?_⟩
  have hStep := qrom_unitary_measure_reprogram_rbr_step A H (fun _ => true)
    (fun _ bv => decide (bv.toNat = 0)) 1
    (by
      intro _ _
      decide)
  simpa only [↓reduceIte, BitVec.toNat_ofFin] using hStep


/-- Arithmetic repair for a portfolio budget of `2^56` oracle queries: 384-bit commitment
    digests suffice with the same field and query schedule. This changes the commitment
    parameter; it is not a security claim for the deployed 256-bit Merkle implementation. -/
theorem multiRoundFsQrom_budget_384_at_2pow56 (Q : Nat) (hQ : Q ≤ 2 ^ 56) :
    strictlyMoreThanBits 128 (multiRoundFsQromCompilerBound Q 5 384
      hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) ∧
    atLeastBits 128 (multiRoundFsQromCompilerBound Q 5 384
      hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) :=
  hemCompiler_budget_up_to (2 ^ 56) 384 (by decide +kernel) Q hQ

/-- Keeping the deployed 256-bit commitment parameter fails the requested budget. -/
theorem tooth_multiRoundFsQrom_256_at_2pow56 :
    ¬ atLeastBits 128 (multiRoundFsQromCompilerBound (2 ^ 56) 5 256
      hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) := by
  decide +kernel

/-- Nonzero portfolio query budget satisfying the repaired bound. -/
theorem inhabited_multiRoundFsQrom_384 :
    ∃ Q : Nat, Q = 2 ^ 56 ∧ Q ≤ 2 ^ 56 ∧
      atLeastBits 128 (multiRoundFsQromCompilerBound Q 5 384
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) :=
  ⟨2 ^ 56, rfl, Nat.le_refl _,
    (multiRoundFsQrom_budget_384_at_2pow56 (2 ^ 56) (Nat.le_refl _)).2⟩

#tooth_pair multiRoundFsQrom_budget_384_at_2pow56 vs tooth_multiRoundFsQrom_256_at_2pow56
#tooth_pair hemAffineWhir_rbr_completeness_and_doomed_init vs hemFalseClaimInstance_invalid
#tooth_pair hem_johnson_fold_state_restoration_of_mca vs tooth_deployed_rows_exceed_welch_berlekamp_radius
#verify_inhabited multiRoundFsQrom_budget_384_at_2pow56 inhabited_multiRoundFsQrom_384

end Qsag
