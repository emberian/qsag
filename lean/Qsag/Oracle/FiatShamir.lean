module
public import Qsag.Math.Algebra
public import Qsag.Spec.Bounds
public import Qsag.Tactic.Prelude
public section
namespace Qsag
set_option autoImplicit false
/-! ## §1. Round-by-Round Soundness (`RbrStateFunction`) & Adaptive State-Restoration Game -/

/-- Constructive boolean list-membership test (`0` classical typeclass search). -/
def listHasElem {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => if x = y then true else listHasElem x ys

theorem listHasElem_eq_true_iff {α : Type} [DecidableEq α] (x : α) :
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
  | 0, _ => (qsum_zero _).symm
  | n + 1, e => by
    rw [qsum_succ]
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
    unfold RatBound.le srScheduleErrorSum
    simp only [List.map_nil, RatBound.sumList_nil, RatBound.zero_num, RatBound.zero_den]
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
    simp only [List.map, RatBound.sumList_cons]
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



end Qsag

namespace Qsag
@[simp] theorem listHasElem_nil {α : Type} [DecidableEq α] (x : α) : listHasElem x [] = false := by rfl
theorem listHasElem_cons {α : Type} [DecidableEq α] (x y : α) (ys : List α) :
    listHasElem x (y::ys) = if x=y then true else listHasElem x ys := by rfl
end Qsag
