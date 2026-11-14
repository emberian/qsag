module
public import Qsag.Constructive
public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.UcGames
public import Qsag.ConcreteSecurityBudget
import all Qsag.ConcreteSecurityBudget
public import Qsag.AffineProximityGaps
import all Qsag.AffineProximityGaps

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
   `affineMcaRbr` (flip bound proved from `welch_berlekamp_affine_proximity_gap`) and
   `affineCommittedRbr` (flip bound proved from `committed_polynomial_pair_bad_lines_le_choose2`),
   composed into `affine_mca_state_restoration_soundness` and
   `affine_committed_pair_state_restoration_soundness` for statements without correlated
   agreement, over any constructive field and at `QuarticGoldilocks`.

3. **`Hem` v6 transcript model (`hemAffineWhirStateFunction`, `verifyHemAffineWhir`)**:
   asymmetric cascade, per-stage affine fold with the `affine.rs` five-wire dual bridge
   (`hemBridgeFoldClaim`, verifier-computed `hemKernelFold`, `hem_bridge_fold_claim_eq_dot`),
   dual OOD pinning (`dual_ood_list_collision_bound`), and coset-query survival
   (`far_codeword_coset_queries_survive_bound`). This model carries doomed-init,
   accept-implies-live and honest completeness; its stage liveness is witnessed by decoded
   polynomials listed in the transcript and it is NOT packaged as an `RbrStateFunction`: a flip
   bound at the deployed Johnson radius needs `[CWYZ26]` Theorem 4.8, which is checked here only
   through its finite side conditions (`checkWhirAffineWitness`).

4. **Multi-round Fiat–Shamir QROM reduction via unitary Measure-and-Reprogram (§3)**:
   the exact `(2 * Q + 1)`-branch telescoping identity over `QVec` / `GaussInt`, the projected
   step `qrom_unitary_measure_reprogram_rbr_step_projected` (output register ≠ query point), its
   oracle-dependent form `qrom_adaptive_oracle_dependent_rbr_step`, and the `k`-round union
   `qrom_multiRound_measure_reprogram_union` (`(2 Q + 1)^2 ∑_r badCard_r / 2^w`, for a FIXED
   background oracle; averaging over the oracle is not formalized). The concrete budget
   `multiRoundFsQrom_soundness_bound` instantiates round bounds DERIVED from the deployed
   `whirAffineStageWitnesses 24 true` rows (`hemV6FiveRoundRbrBounds_eq_deployed`).

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

private theorem list_getD_eq_get {α : Type} :
    ∀ (xs : List α) (d : α) (idx : Fin xs.length), xs.getD idx.1 d = xs.get idx
  | [], _, idx => absurd idx.2 (Nat.not_lt_zero _)
  | _ :: _, _, ⟨0, _⟩ => rfl
  | _ :: xs, d, ⟨i + 1, hi⟩ => list_getD_eq_get xs d ⟨i, Nat.lt_of_succ_lt_succ hi⟩

private theorem list_get_mem {α : Type} : ∀ (xs : List α) (k : Fin xs.length), xs.get k ∈ xs
  | _ :: _, ⟨0, _⟩ => .head _
  | _ :: xs, ⟨k + 1, hk⟩ => .tail _ (list_get_mem xs ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

private theorem nodup_get_inj {α : Type} :
    ∀ {S : List α} (_ : S.Nodup) {i j : Fin S.length}, S.get i = S.get j → i = j
  | [], _, ⟨_, hi⟩, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | _ :: xs, hNodup, ⟨0, _⟩, ⟨j + 1, hj⟩, hEq =>
    absurd hEq ((List.pairwise_cons.mp hNodup).1 _
      (list_get_mem xs ⟨j, Nat.lt_of_succ_lt_succ hj⟩))
  | _ :: xs, hNodup, ⟨i + 1, hi⟩, ⟨0, _⟩, hEq =>
    absurd hEq.symm ((List.pairwise_cons.mp hNodup).1 _
      (list_get_mem xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩))
  | _ :: xs, hNodup, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hEq => by
    have hSub := nodup_get_inj (List.pairwise_cons.mp hNodup).2
      (i := ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (j := ⟨j, Nat.lt_of_succ_lt_succ hj⟩) hEq
    exact Fin.ext (by simpa using congrArg Fin.val hSub)

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

private theorem not_not_forall_mem {α : Type} (Q : α → Prop) :
    ∀ l : List α, (∀ a ∈ l, ¬¬ Q a) → ¬¬ (∀ a ∈ l, Q a)
  | [], _ => fun h => h (fun _ hm => nomatch hm)
  | a :: l, h => fun hn =>
    h a (.head l) (fun hQa =>
      not_not_forall_mem Q l (fun a' ha' => h a' (.tail a ha')) (fun hRest =>
        hn (fun a' ha' => by
          rcases List.mem_cons.mp ha' with hEq | h1
          · rw [hEq]; exact hQa
          · exact hRest a' h1)))

private theorem list_finite_choice {α β : Type} [DecidableEq α] (Q : α → β → Prop) (dflt : β) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, Q a b) → ∃ f : α → β, ∀ a ∈ l, Q a (f a)
  | [], _ => ⟨fun _ => dflt, fun _ hm => nomatch hm⟩
  | a :: l, h => by
    rcases h a (.head l) with ⟨b, hb⟩
    rcases list_finite_choice Q dflt l (fun a' ha' => h a' (.tail a ha')) with ⟨f, hf⟩
    refine ⟨fun a' => if a' = a then b else f a', ?_⟩
    intro a' ha'
    if hEq : a' = a then
      rw [hEq]
      simp only [↓reduceIte]
      exact hb
    else
      simp only [hEq, ↓reduceIte]
      rcases List.mem_cons.mp ha' with h1 | h1
      · exact absurd h1 hEq
      · exact hf a' h1

section AffineWeld
variable {F : Type} [LawfulField F] [DecidableEq F]

/-- **Correlated agreement**: ONE polynomial pair `(F_poly, G_poly)` (`deg F_poly ≤ d`,
    `deg G_poly ≤ d - 1`) simultaneously agrees with the received words `(f, g)` on at least `A`
    coordinates of the evaluation domain `D`. -/
def HasCorrelatedAgreement (d A : Nat) (f g : F → F) (D : List F) : Prop :=
  ∃ F_poly G_poly : List F,
    F_poly.length ≤ d + 1 ∧
    G_poly.length ≤ d ∧
    A ≤ (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs F_poly z = f z) &&
      decide (RoundPoly.evalCoeffs G_poly z = g z))).length

/-- An `s = 1` affine witness for a fold that is `A`-close forces correlated agreement `≥ A - 1`:
    the decomposition `P = F + (α + β X) G` loses at most one coordinate of the agreement set. -/
theorem hasCorrelatedAgreement_of_affineWitnessS1
    {d A : Nat} {f g : F → F} {D : List F} {α β : F} {P : List F}
    (hW : HasAffineWitnessS1 d f g D α β P)
    (hAgree : A ≤ (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs P z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z))))).length) :
    HasCorrelatedAgreement d (A - 1) f g D := by
  rcases hW with ⟨F_poly, G_poly, hF, hG, _, hLoss⟩
  refine ⟨F_poly, G_poly, hF, hG, ?_⟩
  have hSplit := length_filter_split
    (fun z => decide (RoundPoly.evalCoeffs F_poly z = f z) &&
      decide (RoundPoly.evalCoeffs G_poly z = g z))
    (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs P z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)))))
  have hLe := length_filter_filter_le
    (fun z => decide (RoundPoly.evalCoeffs F_poly z = f z) &&
      decide (RoundPoly.evalCoeffs G_poly z = g z))
    (fun z =>
      decide (RoundPoly.evalCoeffs P z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)))) D
  apply Nat.sub_le_of_le_add
  apply Nat.le_trans hAgree
  rw [hSplit]
  exact Nat.add_le_add hLe hLoss

/-! #### Uncommitted fold: flip bound from `welch_berlekamp_affine_proximity_gap` -/

/-- Verifier predicate of the affine-fold proximity IOP: challenge index `c` selects
    `(α, β) = (prodPool S)[c]`, and the prover's response `P` has degree `≤ d` and agrees with the
    fold word `f + (α + β X) g` on at least `A` points of `D`. -/
def affineMcaAccepts (D S : List F) (d A : Nat) (x : (F → F) × (F → F)) (c : Nat)
    (P : List F) : Bool :=
  decide (c < (prodPool S).length) &&
  decide (P.length ≤ d + 1) &&
  decide (A ≤ (D.filter (fun z =>
    decide (RoundPoly.evalCoeffs P z =
      CommRingOps.add (x.1 z)
        (CommRingOps.mul
          (CommRingOps.add ((prodPool S).getD c (CommRingOps.zero, CommRingOps.zero)).1
            (CommRingOps.mul ((prodPool S).getD c (CommRingOps.zero, CommRingOps.zero)).2 z))
          (x.2 z))))).length)

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

private theorem affineMca_round_flip_bound (D S : List F) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup) (hAD : A ≤ D.length) (hWB : 2 * D.length + d + 1 < 3 * A)
    (x : (F → F) × (F → F)) (r : Fin 2) (pref : List (List F × Nat)) (m : List F)
    (hLen : pref.length = r.1)
    (hDoomed : ¬ affineMcaLive D S d A x pref)
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hL : ∀ ch ∈ L, ¬¬ affineMcaLive D S d A x (pref ++ [(m, ch.1)])) :
    L.length ≤ (match r.1 with
      | 0 => Nat.max S.length (D.length * (D.length - 1) / 2)
      | _ => 0) := by
  have hNotCA : ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D := fun h => hDoomed (Or.inl h)
  rcases r with ⟨_ | _ | k, hr⟩
  · have hNil : pref = [] := List.eq_nil_of_length_eq_zero hLen
    subst hNil
    show L.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2)
    apply Decidable.byContradiction
    intro hGt
    have hEx : ∀ ch ∈ L, ¬¬ ∃ P : List F, affineMcaAccepts D S d A x ch.1 P = true := by
      intro ch hch hNo
      exact hL ch hch (fun hLive => Or.elim hLive hNotCA hNo)
    refine not_not_forall_mem _ L hEx (fun hAll => hGt ?_)
    have hPairs : ∀ p ∈ L.map (fun ch => (prodPool S).get ch), ∃ P : List F,
        P.length ≤ d + 1 ∧
        A ≤ (D.filter (fun z =>
          decide (RoundPoly.evalCoeffs P z =
            CommRingOps.add (x.1 z)
              (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (x.2 z))))).length := by
      intro p hp
      rcases List.mem_map.mp hp with ⟨ch, hch, rfl⟩
      rcases hAll ch hch with ⟨P, hP⟩
      unfold affineMcaAccepts at hP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
      rw [list_getD_eq_get (prodPool S) _ ch] at hP
      exact ⟨P, hP.1.2, hP.2⟩
    rcases list_finite_choice _ ([] : List F) _ hPairs with ⟨P_of, hP_of⟩
    have hBound := welch_berlekamp_affine_proximity_gap x.1 x.2 D S d A
      (L.map (fun ch => (prodPool S).get ch)) P_of hD hS hAD hWB
      (List.Pairwise.map _
        (fun a b hab hEq => hab (nodup_get_inj (prodPool_nodup hS) hEq)) hNd)
      (fun p hp => by
        rcases List.mem_map.mp hp with ⟨ch, _, rfl⟩
        exact list_get_mem (prodPool S) ch)
      (fun p hp => (hP_of p hp).1)
      (fun p hp => (hP_of p hp).2)
      (fun p hp hW => hNotCA (hasCorrelatedAgreement_of_affineWitnessS1 hW (hP_of p hp).2))
    rw [List.length_map] at hBound
    exact hBound
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

/-- **`RbrStateFunction` of the affine-fold proximity IOP, flip bound PROVED from
    `welch_berlekamp_affine_proximity_gap`**: in the regime `2 |D| + d + 1 < 3 A`, a statement
    without correlated agreement `≥ A - 1` turns live on at most `max(|S|, |D|(|D|-1)/2)` of the
    `|S|^2` challenges `(α, β)`, and never on the response round. -/
def affineMcaRbr (D S : List F) (hSpos : 0 < S.length) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup) (hAD : A ≤ D.length) (hWB : 2 * D.length + d + 1 < 3 * A) :
    RbrStateFunction (affineMcaIop D S hSpos d A) where
  Live := affineMcaLive D S d A
  badCard := fun r => match r.1 with
    | 0 => Nat.max S.length (D.length * (D.length - 1) / 2)
    | _ => 0
  doomed_init := fun _ hNot hLive => Or.elim hLive hNot (fun h => h)
  accept_implies_live := affineMca_accept_implies_live D S hSpos d A
  round_flip_bound := affineMca_round_flip_bound D S d A hD hS hAD hWB

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
