module
public import Qsag.Tactic.Prelude
public import Qsag.Oracle.Qrom
public import Qsag.Oracle.FiatShamir
public import Qsag.Math.Goldilocks
import all Qsag.Math.Goldilocks
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import all Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Coding.Cwyz26
import all Qsag.Coding.Cwyz26

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
