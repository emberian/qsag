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
  batchCandidateLists : List (List (List F))
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

def checkBatchValidAux {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (minAgree degBound : Nat) (kernel : List F) :
    List (Nat → F) → List F → List (List (List F)) → Bool
  | [], [], [] => true
  | O :: os, e :: es, cands :: cs =>
    cands.any (polyWitnessValid domPts minAgree degBound O kernel e) &&
      checkBatchValidAux domPts minAgree degBound kernel os es cs
  | _, _, _ => false

def validHemStatement {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) : Bool :=
  decide (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16) &&
  checkBatchValidAux inst.initDomainPts inst.initMinAgree inst.initDegBound inst.initKernel
    inst.batchOracles inst.batchClaims inst.batchCandidateLists

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

/-- **State predicate of the `Hem` v6 transcript model (`hemAffineWhirStateFunction`)** over
    `QuarticGoldilocks` (`F = QuarticGoldilocks` by default): Round 0 asymmetric cascade
    (`S_poly ≤ 16`), `S` stages of monomial-shift affine folding with the `affine.rs` five-wire
    bridge (`hemBridgeFoldClaim`, verifier-computed `hemKernelFold`) + dual OOD pinning, and final
    coefficients + coset checks. Every stage check is algebraic (degree bound, agreement count
    with the stage oracle, linear-functional claim, OOD evaluations); the decoded polynomial
    witnessing a live stage is read from the transcript's `stageDecoded` list. -/
@[expose] def hemAffineWhirStateFunction {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (tr : List (HemTranscriptRound F)) : Bool :=
  match tr with
  | [] => validHemStatement inst
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
        batchCandidateLists := [[W]]
        initDomainPts := domPts
        initDegBound := d₀
        initMinAgree := domPts.length
        initKernel := kernel
        stages := [] }
    let tr : List (HemTranscriptRound F) :=
      [ .cascade [s] [(α, β)] [P_comb],
        .finalQuery P_comb ]
    validHemStatement inst = true ∧
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
      validHemStatement
        { batchOracles := [O]
          batchClaims := [ringDot W kernel]
          batchCandidateLists := [[W]]
          initDomainPts := domPts
          initDegBound := d₀
          initMinAgree := domPts.length
          initKernel := kernel
          stages := [] } = true := by
    unfold validHemStatement
    dsimp only [checkBatchValidAux, polyWitnessValid, List.length_cons, List.length_nil,
      List.any_cons, List.any_nil]
    rw [hAgreeW]
    simp only [hWLen, Nat.le_refl, decide_true, Bool.or_false, Bool.and_true]
    decide
  have hVerTr :
      verifyHemAffineWhir
        { batchOracles := [O]
          batchClaims := [ringDot W kernel]
          batchCandidateLists := [[W]]
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
    verifyHemAffineWhir inst fullTr = true → hemAffineWhirStateFunction inst fullTr = true := by
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
      unfold hemAffineWhirStateFunction
      dsimp only
      rw [hOk]
      simp only [↓reduceIte]
      exact verifyHemStages_implies_evalHemRbrPrefix _ _ _ _ _ _ _ inst.stages restTr hStages

/-- **`Hem` v6 RBR Doomed-Init & Verifier-Rejection Completeness Theorem
    (`hemAffineWhir_rbr_completeness_and_doomed_init`)**:
    Over `QuarticGoldilocks` (`|𝔽| = p^4`):
    1. **Invalid Witness $\implies$ Doomed Init**: if `validHemStatement inst = false`, then
       `hemAffineWhirStateFunction inst [] = false`.
    2. **Doomed Final $\implies$ Deterministic Verifier Rejects**: for ANY full transcript `fullTr`,
       if `hemAffineWhirStateFunction inst fullTr = false`, then
       `verifyHemAffineWhir inst fullTr = false` (and contrapositively
       `verifyHemAffineWhir inst fullTr = true → hemAffineWhirStateFunction inst fullTr = true`).
    3. **Honest Prover Completeness**: any valid `QuarticGoldilocks` polynomial witness `W` of
       degree `≤ d₀` absorbing its shifted functional claim before challenge squeeze satisfies both
       `hemAffineWhirStateFunction = true` and `verifyHemAffineWhir = true`! -/
theorem hemAffineWhir_rbr_completeness_and_doomed_init :
    (∀ inst : HemWhirInstance QuarticGoldilocks,
      validHemStatement inst = false → hemAffineWhirStateFunction inst [] = false) ∧
    (∀ (inst : HemWhirInstance QuarticGoldilocks) (fullTr : List (HemTranscriptRound QuarticGoldilocks)),
      hemAffineWhirStateFunction inst fullTr = false → verifyHemAffineWhir inst fullTr = false) ∧
    (∀ (inst : HemWhirInstance QuarticGoldilocks) (fullTr : List (HemTranscriptRound QuarticGoldilocks)),
      verifyHemAffineWhir inst fullTr = true → hemAffineWhirStateFunction inst fullTr = true) ∧
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
          batchCandidateLists := [[W]]
          initDomainPts := domPts
          initDegBound := d₀
          initMinAgree := domPts.length
          initKernel := kernel
          stages := [] }
      let tr : List (HemTranscriptRound QuarticGoldilocks) :=
        [ .cascade [s] [(α, β)] [P_comb],
          .finalQuery P_comb ]
      validHemStatement inst = true ∧
      hemAffineWhirStateFunction inst tr = true ∧
      verifyHemAffineWhir inst tr = true) := by
  refine ⟨fun _ hInv => hInv, ?_, accept_implies_live_poly, ?_⟩
  · intro inst fullTr hDoomed
    cases hv : verifyHemAffineWhir inst fullTr
    · rfl
    · have hLive := accept_implies_live_poly inst fullTr hv
      rw [hDoomed] at hLive
      exact Bool.noConfusion hLive
  · intro W kernel domPts d₀ α β hWLen
    rcases honest_cascade_completeness_poly W kernel domPts d₀ α β hWLen with ⟨hVal, hVer⟩
    exact ⟨hVal, accept_implies_live_poly _ _ hVer, hVer⟩


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
