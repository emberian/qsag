module
public import Qsag.Tactic.Prelude
public import Qsag.Oracle.Qrom
public import Qsag.Oracle.FiatShamir
public import Qsag.Math.Goldilocks
import Qsag.Math.CoeffPoly
import Qsag.Math.PolyRing
import Qsag.Math.QuarticExt4
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Coding.Cwyz26

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
  rw [whirAffineStageWitnesses_qrom_eq_deployed.2]
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

theorem ringDot_nil_left {F : Type} [CommRingOps F] (v : List F) :
    ringDot [] v = CommRingOps.zero := by rw [ringDot_eq]; exact dotVec_nil_left v

theorem ringDot_nil_right {F : Type} [CommRingOps F] (xs : List F) :
    ringDot xs [] = CommRingOps.zero := by rw [ringDot_eq]; exact dotVec_nil_right xs

theorem ringDot_cons_cons {F : Type} [CommRingOps F] (a b : F) (as bs : List F) :
    ringDot (a :: as) (b :: bs) = CommRingOps.add (CommRingOps.mul a b) (ringDot as bs) := by
  simp only [ringDot_eq]; exact dotVec_cons a b as bs

theorem polyAddVar_nil_left {F : Type} [CommRingOps F] (ys : List F) :
    polyAddVar [] ys = ys := by unfold polyAddVar; cases ys <;> rfl

theorem polyAddVar_nil_right {F : Type} [CommRingOps F] (xs : List F) :
    polyAddVar xs [] = xs := by unfold polyAddVar; cases xs <;> rfl

theorem polyAddVar_cons_cons {F : Type} [CommRingOps F] (x y : F) (xs ys : List F) :
    polyAddVar (x :: xs) (y :: ys) = CommRingOps.add x y :: polyAddVar xs ys := by
  unfold polyAddVar; rfl

theorem ringDot_polyAddVar {F : Type} [LawfulCommRing F] :
    ∀ (xs ys v : List F),
      ringDot (polyAddVar xs ys) v = CommRingOps.add (ringDot xs v) (ringDot ys v)
  | [], _, _ => by simp only [polyAddVar_nil_left, ringDot_nil_left, LawfulCommRing.zero_add]
  | _ :: _, [], _ => by simp only [polyAddVar_nil_right, ringDot_nil_left, LawfulCommRing.add_zero]
  | _ :: _, _ :: _, [] => by simp only [polyAddVar_cons_cons, ringDot_nil_right, LawfulCommRing.add_zero]
  | x :: xs, y :: ys, k :: ks => by
    simp only [polyAddVar_cons_cons, ringDot_cons_cons, ringDot_polyAddVar xs ys ks]
    rw [LawfulCommRing.right_distrib,
        LawfulCommRing.add_assoc (CommRingOps.mul x k) (CommRingOps.mul y k) _,
        ← LawfulCommRing.add_assoc (CommRingOps.mul y k) (ringDot xs ks) _,
        LawfulCommRing.add_comm (CommRingOps.mul y k) (ringDot xs ks),
        LawfulCommRing.add_assoc (ringDot xs ks) (CommRingOps.mul y k) _,
        ← LawfulCommRing.add_assoc]

theorem ringDot_polyScaleVar {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (xs v : List F),
      ringDot (polyScaleVar c xs) v = CommRingOps.mul c (ringDot xs v)
  | [], _ => by simp only [polyScaleVar_def, List.map_nil, ringDot_nil_left, LawfulCommRing.mul_zero]
  | _ :: _, [] => by simp only [polyScaleVar_def, List.map_cons, ringDot_nil_right, LawfulCommRing.mul_zero]
  | x :: xs, k :: ks => by
    simp only [polyScaleVar_def, List.map_cons, ringDot_cons_cons]
    rw [← polyScaleVar_def c, ringDot_polyScaleVar c xs ks, LawfulCommRing.mul_assoc c x k, ← LawfulCommRing.left_distrib]

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
    | nil => simp only [shiftPoly_eq, ringDot_nil_right, LawfulCommRing.add_zero]
    | cons _ ks =>
      simp only [shiftPoly_eq, ringDot_cons_cons, LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
      exact ringDot_polyAddVar a b ks
  have hShiftScale : ∀ (c : F) (a k : List F),
      ringDot (shiftPoly (polyScaleVar c a)) k = CommRingOps.mul c (ringDot (shiftPoly a) k) := by
    intro c a k
    cases k with
    | nil => simp only [shiftPoly_eq, ringDot_nil_right, LawfulCommRing.mul_zero]
    | cons _ ks =>
      simp only [shiftPoly_eq, ringDot_cons_cons, LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
      exact ringDot_polyScaleVar c a ks
  rw [affineCombine_def]
  rw [ringDot_polyAddVar, ringDot_polyAddVar,
      ringDot_polyScaleVar, ringDot_polyScaleVar,
      ringDot_polyAddVar, ringDot_polyScaleVar,
      hShiftAdd, hShiftScale]

/-! ### §2.2 Genuine Algebraic Dual OOD List-Collision & Coset Query Survival Bounds -/

/-- Exact unordered pair count `binomial(L, 2) = L * (L - 1) / 2`. -/
def binom2 (L : Nat) : Nat := L * (L - 1) / 2

theorem binom2_eq (L : Nat) : binom2 L = L * (L - 1) / 2 := by unfold binom2; rfl


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
@[expose] def hemCosetAgreeCount {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (oracleAt : Nat → F) (P : List F) : Nat :=
  qsum domPts.length (fun idx =>
    if oracleAt idx.1 = RoundPoly.evalCoeffs P (domPts.get idx) then 1 else 0)

/-- Checks whether polynomial `P` has degree `≤ degBound`, coset agreement `≥ minAgree` with
    `oracleAt` on `domPts`, and linear-functional evaluation `ringDot P kernel = claim`. -/
@[expose] def polyWitnessValid {F : Type} [CommRingOps F] [DecidableEq F]
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
@[expose] def evalCascadeClaim {F : Type} [CommRingOps F] :
    List F → List F → List (F × F) → F
  | [], _, _ => CommRingOps.zero
  | _, [], _ => CommRingOps.zero
  | _, _, [] => CommRingOps.zero
  | e :: es, s :: ss, (α, β) :: abs =>
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul α e) (CommRingOps.mul β s))
      (evalCascadeClaim es ss abs)

/-- Asymmetric cascade combined oracle `O_cascade(idx) = ∑_i (α_i + β_i * dom[idx]) * O_i(idx)`. -/
@[expose] def evalCascadeOracle {F : Type} [CommRingOps F] (domPts : List F) :
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

@[expose] def checkQueriedCosets {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (oracleAt : Nat → F) (P : List F) : List Nat → Bool
  | [] => true
  | idx :: rest =>
    decide (idx < domPts.length) &&
    decide (oracleAt idx = RoundPoly.evalCoeffs P (domPts.getD idx CommRingOps.zero)) &&
    checkQueriedCosets domPts oracleAt P rest

/-- `affine.rs::fold_kernel`: `k'_i = k_{2i} + φ k_{2i+1}` followed by the extra zero overflow slot
    (`chunks_exact(2)` drops an unpaired tail element). The NEXT kernel is computed by the
    verifier from the challenge `φ`; it is never a prover-supplied transcript field. -/
@[expose] def hemKernelFold {F : Type} [CommRingOps F] (φ : F) : List F → List F
  | a :: b :: rest => CommRingOps.add a (CommRingOps.mul φ b) :: hemKernelFold φ rest
  | _ => [CommRingOps.zero]

theorem hemKernelFold_pair {F : Type} [LawfulCommRing F] (φ k : F) :
    hemKernelFold φ [k, CommRingOps.zero] = [k, CommRingOps.zero] := by
  simp only [hemKernelFold, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-- `affine.rs::bridge_finish`: from the five bridge wires `(w₀, w₁, w₂, c_F, c_G)`
    (`WHIR_AFFINE_CROSS` ×3, then `WHIR_AFFINE_SHIFT` ×2), the running claim and the challenges
    `(φ, θ, α, β)`, the verifier DERIVES `f = w₀ + φ w₁`, `g = w₂ + φ (claim - w₀)` and the next
    claim `g + α (f + θ g) + β (c_F + θ c_G)`. There is no separate consistency check: the
    fourth cross term is forced to `claim - w₀`. -/
@[expose] def hemBridgeFoldClaim {F : Type} [CommRingOps F]
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
    simp only [ringDot_nil_left, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | _ :: _, [], [], _ => by
    simp only [List.zipWith_nil_left, ringDot_nil_right, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | _ :: _, [], _ :: _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, _ :: _, [], h => absurd h (Nat.succ_ne_zero _)
  | x :: xs, a :: as, b :: bs, h => by
    have ih := ringDot_zipFold φ xs as bs (Nat.succ.inj h)
    simp only [List.zipWith_cons_cons, ringDot_cons_cons]
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

/-- A monomial-shift round spends one point of agreement slack. At an exhaustive
    threshold no slack remains to spend; thresholds already above the domain stay invalid. -/
@[expose] def hemNextMinAgree (domainSize curAgree : Nat) : Nat :=
  if curAgree < domainSize then curAgree + 1 else curAgree

@[simp] theorem hemNextMinAgree_exhaustive (n : Nat) : hemNextMinAgree n n = n := by
  simp [hemNextMinAgree]

theorem hemNextMinAgree_mono (n A : Nat) : A ≤ hemNextMinAgree n A := by
  unfold hemNextMinAgree
  split <;> omega

theorem hemNextMinAgree_increments (n A : Nat) (h : A < n) :
    hemNextMinAgree n A = A + 1 := by simp [hemNextMinAgree, h]

/-- `#tooth`: two consecutive non-exhaustive transitions must spend two points,
    whereas the unincremented transition spends none. -/
theorem tooth_hem_agreement_two_rounds :
    ∃ threshold : Nat, threshold = 4 ∧
    hemNextMinAgree 5 (hemNextMinAgree 5 2) = threshold ∧
    hemNextMinAgree 5 (hemNextMinAgree 5 2) ≠ 2 ∧
    hemNextMinAgree 3 3 = 3 ∧ hemNextMinAgree 3 4 = 4 := by
  exact ⟨4, by decide⟩

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
        polyWitnessValid curDom (hemNextMinAgree curDom.length curMinAgree) (curDeg + 1) curOracle curKernel curClaim P)
    evalHemRbrPrefix (curLive || nextLive) curOracle curDom (curDeg + 1) (hemNextMinAgree curDom.length curMinAgree)
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

/-- The recursive prefix transition carries the incremented agreement into its
    continuation, including when the current decoded list is empty. -/
theorem hemRbrPrefix_cascade_step {F : Type} [CommRingOps F] [DecidableEq F]
    (live : Bool) (oracle : Nat → F) (domain : List F) (degree agree : Nat)
    (kernel : List F) (claim : F) (stages : List (HemWhirStageSpec F))
    (shifts : List F) (weights : List (F × F)) (decoded : List (List F))
    (rest : List (HemTranscriptRound F)) :
    evalHemRbrPrefix live oracle domain degree agree kernel claim stages
      (.cascade shifts weights decoded :: rest) =
    evalHemRbrPrefix
      (live || decoded.any (fun P => polyWitnessValid domain
        (hemNextMinAgree domain.length agree) (degree + 1) oracle kernel claim P))
      oracle domain (degree + 1) (hemNextMinAgree domain.length agree) kernel claim stages rest := by
  rfl

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
      decide (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16 ∧
      inst.batchClaims.length = inst.batchOracles.length) &&
      decide (absorbedShifts.length = inst.batchClaims.length) &&
      decide (weights.length = inst.batchClaims.length)
    if okLengths = true then
      let combClaim := evalCascadeClaim inst.batchClaims absorbedShifts weights
      let combOracle := evalCascadeOracle inst.initDomainPts inst.batchOracles weights
      let cascadeLive :=
        cascadeDecoded.any (fun P =>
          polyWitnessValid inst.initDomainPts (hemNextMinAgree inst.initDomainPts.length inst.initMinAgree) (inst.initDegBound + 1)
            combOracle inst.initKernel combClaim P)
      evalHemRbrPrefix cascadeLive combOracle inst.initDomainPts (inst.initDegBound + 1)
        (hemNextMinAgree inst.initDomainPts.length inst.initMinAgree) inst.initKernel combClaim inst.stages restTr
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

@[expose] def verifyHemStages {F : Type} [CommRingOps F] [DecidableEq F]
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
    decide (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16 ∧
      inst.batchClaims.length = inst.batchOracles.length) &&
    decide (absorbedShifts.length = inst.batchClaims.length) &&
    decide (weights.length = inst.batchClaims.length) &&
    let combClaim := evalCascadeClaim inst.batchClaims absorbedShifts weights
    let combOracle := evalCascadeOracle inst.initDomainPts inst.batchOracles weights
    cascadeDecoded.any (fun P =>
      polyWitnessValid inst.initDomainPts (hemNextMinAgree inst.initDomainPts.length inst.initMinAgree) (inst.initDegBound + 1)
        combOracle inst.initKernel combClaim P) &&
    verifyHemStages combOracle inst.initDomainPts (inst.initDegBound + 1)
      (hemNextMinAgree inst.initDomainPts.length inst.initMinAgree) inst.initKernel combClaim inst.stages restTr
  | _ => false

/-- Accepted cascades expose a witness at the incremented agreement threshold. -/
theorem verifyHemAffineWhir_incremented_cascade_witness {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (shifts : List F) (weights : List (F × F))
    (decoded : List (List F)) (rest : List (HemTranscriptRound F))
    (h : verifyHemAffineWhir inst (.cascade shifts weights decoded :: rest) = true) :
    inst.batchClaims.length = inst.batchOracles.length ∧
    shifts.length = inst.batchClaims.length ∧ weights.length = inst.batchClaims.length ∧
    ∃ P ∈ decoded, polyWitnessValid inst.initDomainPts
      (hemNextMinAgree inst.initDomainPts.length inst.initMinAgree)
      (inst.initDegBound + 1) (evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
      inst.initKernel (evalCascadeClaim inst.batchClaims shifts weights) P = true := by
  unfold verifyHemAffineWhir at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2.2, h.1.1.2, h.1.2, List.any_eq_true.mp h.2.1⟩

/-- Deliberately stale cascade transition, retained only as an attack witness. -/
def mutantVerifyHemAffineWhirUnincremented {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (tr : List (HemTranscriptRound F)) : Bool :=
  match tr with
  | .cascade absorbedShifts weights cascadeDecoded :: restTr =>
    decide (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16 ∧
      inst.batchClaims.length = inst.batchOracles.length) &&
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
      simp only [polyScaleVar_def, List.length_map]; omega
    have h2 : (polyScaleVar β (shiftPoly W)).length ≤ d₀ + 2 := by
      simp only [polyScaleVar_def, shiftPoly_eq, List.length_map, List.length_cons]; omega
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
    simp only [hemNextMinAgree_exhaustive]
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

/-- `#tooth`: the actual prefix evaluator carries the updated threshold across two
    cascade rounds. The fourth query exposes the mismatch that a stale threshold misses. -/
theorem tooth_hem_prefix_two_round_agreement :
    ∃ (D : List QuarticGoldilocks) (oracle : Nat → QuarticGoldilocks),
    evalHemRbrPrefix false oracle D 0 2 [] CommRingOps.zero [] [.finalQuery []] = true ∧
    evalHemRbrPrefix false oracle D 0 2 [] CommRingOps.zero []
      [.cascade [] [] [], .cascade [] [] [], .finalQuery []] = false := by
  refine ⟨[CommRingOps.zero, CommRingOps.one, CommRingOps.zero, CommRingOps.one, CommRingOps.zero],
    (fun i => if i = 3 then CommRingOps.one else CommRingOps.zero), ?_⟩
  decide +kernel

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
      unfold hemCosetAgreeCount at hAg
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


/-- Conditional round-0 cascade profile input over `QuarticGoldilocks`, computed from the
    stage-0 paper numerator and the point-reduction term. This definition does not prove
    the arbitrary-batch RBR bound; the stronger incidence and cascade composition are
    required before charging this input to an acceptance event. -/
def hemV6CascadeRbrBound : RatBound :=
  match whirAffineStageWitnesses 24 true with
  | w :: _ =>
    ⟨15 * (whirAffineStageSimpleNum w / w.sFolds) + 72, goldilocksExt4Card, goldilocksExt4Card_pos⟩
  | [] => RatBound.one

/-- Conditional RBR paper/profile inputs for `Hem` v6 (`nv = 24`). Their numbers are computed
    from deployed witness rows, but no RBR event bound is derived by this definition.
    The stronger incidence constant, the equal-degree three-challenge lift, intermediate
    fold geometries and arbitrary-batch/stage composition remain obligations. In particular
    the larger proved sliced binary-fold counts do not justify these inputs. Multiplying
    these rational inputs by `(2Q+1)^2` is arithmetic until the execution-level reduction
    supplies its matching RBR bound. -/
def hemV6FiveRoundRbrBounds : List RatBound :=
  hemV6CascadeRbrBound ::
    (whirAffineStageWitnesses 24 true).map whirAffineEqualDegreeCommitFoldBound

attribute [local irreducible] hemV6FiveRoundRbrBounds

/-- The conditional profile inputs evaluate to `(4182, 1644, 824, 489, 792) / p^4` (total `7931 / p^4`). -/
theorem hemV6FiveRoundRbrBounds_eq_deployed :
    hemV6FiveRoundRbrBounds.map (fun b => (b.num, b.den)) =
      [4182, 1644, 824, 489, 792].map (fun n => (n, goldilocksExt4Card)) := by
  unfold hemV6FiveRoundRbrBounds hemV6CascadeRbrBound
  rw [whirAffineStageWitnesses_qrom_eq_deployed.2]
  simp only [List.map_cons, List.map_nil, whirAffineEqualDegreeCommitFoldBound_def,
    whirAffineStageSimpleNum_def] <;> decide +kernel

/-- Pure 4-stage `Hem` v6 coset-query error bounds under default `BciksJohnsonQrom128`, DERIVED
    from the same deployed `whirAffineStageWitnesses 24 true` rows as the fold bounds: the exact
    distinct-fiber bound `(A + s_i)_{q_i} / (n)_{q_i}` at each row's own agreement threshold
    (`whirAffine_deployed_pure_query_bounds`), with no proof-of-work density. -/
def hemV6BciksJohnsonQueryBounds : List RatBound :=
  (whirAffineStageWitnesses 24 true).map whirAffinePureQueryBoundOrOne

attribute [local irreducible] hemV6BciksJohnsonQueryBounds

private theorem compiler_query_upper (Q roots bits : Nat) (rb qb : List RatBound)
    (upper : RatBound) (h : ∀ q ∈ qb, q.le upper) :
    (multiRoundFsQromCompilerBound Q roots bits rb qb).le
      (multiRoundFsQromCompilerBound Q roots bits rb (List.replicate qb.length upper)) := by
  unfold multiRoundFsQromCompilerBound
  apply RatBound.add_le_add (RatBound.le_refl _)
  apply RatBound.add_le_add (RatBound.le_refl _)
  induction qb with
  | nil => exact RatBound.le_refl _
  | cons q qs ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ, RatBound.sumList_cons]
    apply RatBound.add_le_add
    · simp only [quantumGroverGrindingBound_def]
      exact RatBound.scale_mono _ (h q (.head qs))
    · exact ih (fun x hx => h x (.tail q hx))

private theorem compiler_bht_lower (Q bits : Nat) (rb qb : List RatBound) :
    (RatBound.scale 5 (quantumBhtCollisionBound bits Q)).le
      (multiRoundFsQromCompilerBound Q 5 bits rb qb) := by
  have hm : (RatBound.scale 5 (quantumBhtCollisionBound bits Q)).le
      (qromMerkleOnlineExtractBound 5 bits Q) :=
    RatBound.scale_mono 5 (RatBound.le_add_right _ _)
  exact RatBound.le_trans hm (RatBound.le_trans (RatBound.le_add_left _ _)
    (RatBound.le_add_right _ _))

private theorem hemV6Query_upper :
    ∀ q ∈ hemV6BciksJohnsonQueryBounds, q.le (RatBound.invPow2 256) := by
  intro q hq
  unfold hemV6BciksJohnsonQueryBounds at hq
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
  exact (atLeastBits_iff_le_invPow2 _ _).mp
    (Nat.le_of_lt (whirAffine_deployed_pure_query_bounds 24 (by decide) (by decide) w hw))

private theorem hemV6Query_length : hemV6BciksJohnsonQueryBounds.length = 4 := by
  unfold hemV6BciksJohnsonQueryBounds
  rw [List.length_map, whirAffineStageWitnesses_qrom_eq_deployed.2]
  rfl

private theorem hemV6Rbr_explicit :
    hemV6FiveRoundRbrBounds = [4182, 1644, 824, 489, 792].map
      (fun n => RatBound.mk n goldilocksExt4Card goldilocksExt4Card_pos) := by
  unfold hemV6FiveRoundRbrBounds hemV6CascadeRbrBound
  rw [whirAffineStageWitnesses_qrom_eq_deployed.2]
  simp only [List.map_cons, List.map_nil, whirAffineEqualDegreeCommitFoldBound_def,
    whirAffineStageSimpleNum_def] <;> decide +kernel

private theorem hemV6_budget_of_upper (Q bits : Nat)
    (hUpper : strictlyMoreThanBits 128 (multiRoundFsQromCompilerBound Q 5 bits
      ([4182, 1644, 824, 489, 792].map
        (fun n => RatBound.mk n goldilocksExt4Card goldilocksExt4Card_pos))
      (List.replicate 4 (RatBound.invPow2 256)))) :
    strictlyMoreThanBits 128 (multiRoundFsQromCompilerBound Q 5 bits
      hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) := by
  have h := compiler_query_upper Q 5 bits hemV6FiveRoundRbrBounds
    hemV6BciksJohnsonQueryBounds (RatBound.invPow2 256) hemV6Query_upper
  apply RatBound.strictlyMoreThanBits_of_le h
  rw [hemV6Query_length, hemV6Rbr_explicit]
  exact hUpper

private theorem compiler_upper_40_256 :
    strictlyMoreThanBits 128 (multiRoundFsQromCompilerBound (2 ^ 40 - 1) 5 256
      ([4182, 1644, 824, 489, 792].map
        (fun n => RatBound.mk n goldilocksExt4Card goldilocksExt4Card_pos))
      (List.replicate 4 (RatBound.invPow2 256))) := by
  simp only [multiRoundFsQromCompilerBound, quantumGroverGrindingBound_def,
    quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def,
    qromMerkleOnlineExtractBound, dfmRoundScale, goldilocksExt4Card, goldilocksPrime,
    strictlyMoreThanBits, RatBound.sumList, RatBound.zero, RatBound.add, RatBound.scale,
    RatBound.invPow2, List.map_cons, List.map_nil, List.replicate_succ, List.replicate_zero]
  decide +kernel

private theorem compiler_upper_56_384 :
    strictlyMoreThanBits 128 (multiRoundFsQromCompilerBound (2 ^ 56) 5 384
      ([4182, 1644, 824, 489, 792].map
        (fun n => RatBound.mk n goldilocksExt4Card goldilocksExt4Card_pos))
      (List.replicate 4 (RatBound.invPow2 256))) := by
  simp only [multiRoundFsQromCompilerBound, quantumGroverGrindingBound_def,
    quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def,
    qromMerkleOnlineExtractBound, dfmRoundScale, goldilocksExt4Card, goldilocksPrime,
    strictlyMoreThanBits, RatBound.sumList, RatBound.zero, RatBound.add, RatBound.scale,
    RatBound.invPow2, List.map_cons, List.map_nil, List.replicate_succ, List.replicate_zero]
  decide +kernel

private theorem compiler_budget_up_to (rbrBounds queryBounds : List RatBound)
    (QMax digestBits : Nat)
    (hBciksMax : strictlyMoreThanBits 128
      (multiRoundFsQromCompilerBound QMax 5 digestBits
        rbrBounds queryBounds)) :
    ∀ Q : Nat, Q ≤ QMax →
      strictlyMoreThanBits 128 (multiRoundFsQromCompilerBound Q 5 digestBits
        rbrBounds queryBounds) ∧
      atLeastBits 128 (multiRoundFsQromCompilerBound Q 5 digestBits
        rbrBounds queryBounds) := by
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
        (multiRoundFsQromCompilerBound Q 5 digestBits rbrBounds qBounds)
        (multiRoundFsQromCompilerBound QMax 5 digestBits rbrBounds qBounds) := by
    intro Q hQ qBounds
    unfold multiRoundFsQromCompilerBound
    have hSqLe : (2 * Q + 1) ^ 2 ≤ (2 * QMax + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hRbrLe :
        RatBound.le
          (RatBound.sumList (rbrBounds.map (dfmRoundScale Q)))
          (RatBound.sumList (rbrBounds.map (dfmRoundScale QMax))) := by
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
      simp only [quantumGroverGrindingBound_def]
      exact hMonoScale hGrindLe _
    have hMerkleLe :
        RatBound.le (qromMerkleOnlineExtractBound 5 digestBits Q)
          (qromMerkleOnlineExtractBound 5 digestBits QMax) := by
      unfold qromMerkleOnlineExtractBound
      apply hScaleMono
      apply RatBound.add_le_add
      · simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def]
        unfold RatBound.le
        dsimp only
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
      · simp only [quantumBhtCollisionBound_def]
        unfold RatBound.le
        dsimp only
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
    exact RatBound.add_le_add hRbrLe (RatBound.add_le_add hMerkleLe hQueryLe)
  intro Q hQ
  have hb := hStrictOfLe (hCompilerMono hQ queryBounds) hBciksMax
  exact ⟨hb, Nat.le_of_lt hb⟩

private theorem hemCompiler_budget_up_to (QMax digestBits : Nat)
    (hMax : strictlyMoreThanBits 128
      (multiRoundFsQromCompilerBound QMax 5 digestBits
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds)) :
    ∀ Q : Nat, Q ≤ QMax →
      strictlyMoreThanBits 128 (multiRoundFsQromCompilerBound Q 5 digestBits
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) ∧
      atLeastBits 128 (multiRoundFsQromCompilerBound Q 5 digestBits
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) :=
  compiler_budget_up_to hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds
    QMax digestBits hMax

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
  refine ⟨?_, ?_⟩
  · rw [hemV6Rbr_explicit, List.length_map]
    rfl
  · intro Q hQ
    exact hemCompiler_budget_up_to (2 ^ 40 - 1) 256
      (hemV6_budget_of_upper _ _ compiler_upper_40_256) Q (by omega)


/-- `#tooth`: the oracle-budget range of `multiRoundFsQrom_budget_bound` is not slack. One more
    bit of budget (`Q + 1 = 2^41`) pushes the same expression above `2^-128`, through the
    `8 (Q + 1)^3 / 2^256` collision term of commitment extraction. -/
theorem tooth_multiRoundFsQrom_budget_fails_at_2pow41 :
    ¬ atLeastBits 128
      (multiRoundFsQromCompilerBound (2 ^ 41 - 1) 5 256
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) := by
  intro hBits
  have h := atLeastBits_of_le (compiler_bht_lower (2 ^ 41 - 1) 256
    hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) hBits
  have hNot : ¬ atLeastBits 128 (RatBound.scale 5 (quantumBhtCollisionBound 256 (2 ^ 41 - 1))) := by
    simp only [quantumBhtCollisionBound_def]
    decide +kernel
  exact hNot h


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
  · unfold RatBound.le; rw [RatBound.one_num, RatBound.one_den]; dsimp only; rw [hHitEq, Nat.one_mul, Nat.mul_one]; exact Nat.le_refl _
  · unfold RatBound.le; rw [RatBound.one_num, RatBound.one_den]; dsimp only; rw [hHitEq, Nat.one_mul, Nat.mul_one]; exact Nat.le_refl _

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
  refine ⟨?_, ?_⟩
  · apply RatBound.num_pos_of_le (a := RatBound.scale 5 (quantumBhtCollisionBound 256 (2 ^ 39)))
      (b := multiRoundFsQromCompilerBound (2 ^ 39) 5 256
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds)
    · simp only [quantumBhtCollisionBound_def, RatBound.scale]
      decide +kernel
    · exact compiler_bht_lower _ _ _ _
  let initVec : QVec 2 2 1 := fun x y _ =>
    if x.1 == 0 && y.1 == 0 then ⟨1, 0⟩ else ⟨0, 0⟩
  have hInitPos : 0 < QVec.stateNormSq initVec := by
    rw [QVec.stateNormSq_def]
    simp only [QVec.queryWeight_def, GaussInt.normSq_def]
    unfold initVec
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


/-- Arithmetic repair of the conditional paper/profile expression at `2^56` queries: changing
    only its digest parameter to 384 makes that expression small enough. This neither
    discharges the RBR input nor upgrades the larger proved sliced counts. It is not a
    security claim for either a 256-bit or a 384-bit deployed verifier. -/
theorem multiRoundFsQrom_budget_384_at_2pow56 (Q : Nat) (hQ : Q ≤ 2 ^ 56) :
    strictlyMoreThanBits 128 (multiRoundFsQromCompilerBound Q 5 384
      hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) ∧
    atLeastBits 128 (multiRoundFsQromCompilerBound Q 5 384
      hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) :=
  hemCompiler_budget_up_to (2 ^ 56) 384
    (hemV6_budget_of_upper _ _ compiler_upper_56_384) Q hQ

/-- Keeping the deployed 256-bit commitment parameter fails the requested budget. -/
theorem tooth_multiRoundFsQrom_256_at_2pow56 :
    ¬ atLeastBits 128 (multiRoundFsQromCompilerBound (2 ^ 56) 5 256
      hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) := by
  intro hBits
  have h := atLeastBits_of_le (compiler_bht_lower (2 ^ 56) 256
    hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) hBits
  have hNot : ¬ atLeastBits 128 (RatBound.scale 5 (quantumBhtCollisionBound 256 (2 ^ 56))) := by
    simp only [quantumBhtCollisionBound_def]
    decide +kernel
  exact hNot h

/-- Nonzero portfolio query budget satisfying the repaired bound. -/
theorem inhabited_multiRoundFsQrom_384 :
    ∃ Q : Nat, Q = 2 ^ 56 ∧ Q ≤ 2 ^ 56 ∧
      atLeastBits 128 (multiRoundFsQromCompilerBound Q 5 384
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) :=
  ⟨2 ^ 56, rfl, Nat.le_refl _,
    (multiRoundFsQrom_budget_384_at_2pow56 (2 ^ 56) (Nat.le_refl _)).2⟩

#tooth_pair hemNextMinAgree_increments vs tooth_hem_agreement_two_rounds
#tooth_pair hemRbrPrefix_cascade_step vs tooth_hem_prefix_two_round_agreement
#tooth_pair multiRoundFsQrom_budget_384_at_2pow56 vs tooth_multiRoundFsQrom_256_at_2pow56
#tooth_pair hemAffineWhir_rbr_completeness_and_doomed_init vs hemFalseClaimInstance_invalid
#tooth_pair hem_johnson_fold_state_restoration_of_mca vs tooth_deployed_rows_exceed_welch_berlekamp_radius
#verify_inhabited multiRoundFsQrom_budget_384_at_2pow56 inhabited_multiRoundFsQrom_384

/-! ### Exports for lane agg-whir-cert -/

theorem qsum_get_filter_length {α : Type} (p : α → Bool) (S : List α) :
    qsum S.length (fun i => if p (S.get i) = true then 1 else 0) = (S.filter p).length :=
  qsum_get_filter_eq p S

theorem hemCosetAgreeCount_def {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (oracleAt : Nat → F) (P : List F) :
    hemCosetAgreeCount domPts oracleAt P =
      qsum domPts.length (fun idx =>
        if oracleAt idx.1 = RoundPoly.evalCoeffs P (domPts.get idx) then 1 else 0) := by rfl

theorem polyWitnessValid_def {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (minAgree degBound : Nat)
    (oracleAt : Nat → F) (kernel : List F) (claim : F) (P : List F) :
    polyWitnessValid domPts minAgree degBound oracleAt kernel claim P =
      (decide (P.length ≤ degBound + 1) &&
        decide (minAgree ≤ hemCosetAgreeCount domPts oracleAt P) &&
        decide (ringDot P kernel = claim)) := by rfl

theorem HemBatchValid_nil_nil {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (minAgree degBound : Nat) (kernel : List F) :
    HemBatchValid domPts minAgree degBound kernel [] [] := by
  unfold HemBatchValid; trivial

theorem HemBatchValid_cons_cons_iff {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (minAgree degBound : Nat) (kernel : List F)
    (O : Nat → F) (os : List (Nat → F)) (e : F) (es : List F) :
    HemBatchValid domPts minAgree degBound kernel (O :: os) (e :: es) ↔
      (∃ P : List F, polyWitnessValid domPts minAgree degBound O kernel e P = true) ∧
        HemBatchValid domPts minAgree degBound kernel os es := by
  exact Iff.rfl

theorem HemStatementValid_iff {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) :
    HemStatementValid inst ↔
      (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16) ∧
      HemBatchValid inst.initDomainPts inst.initMinAgree inst.initDegBound inst.initKernel
        inst.batchOracles inst.batchClaims := by
  exact Iff.rfl

theorem checkQueriedCosets_nil {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (oracleAt : Nat → F) (P : List F) :
    checkQueriedCosets domPts oracleAt P [] = true := by rfl

theorem checkQueriedCosets_cons {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (oracleAt : Nat → F) (P : List F) (idx : Nat) (rest : List Nat) :
    checkQueriedCosets domPts oracleAt P (idx :: rest) =
      (decide (idx < domPts.length) &&
        decide (oracleAt idx = RoundPoly.evalCoeffs P (domPts.getD idx CommRingOps.zero)) &&
        checkQueriedCosets domPts oracleAt P rest) := by rfl

theorem hemKernelFold_cons_cons {F : Type} [CommRingOps F] (φ a b : F) (rest : List F) :
    hemKernelFold φ (a :: b :: rest) =
      CommRingOps.add a (CommRingOps.mul φ b) :: hemKernelFold φ rest := by rfl

theorem hemKernelFold_nil {F : Type} [CommRingOps F] (φ : F) :
    hemKernelFold φ ([] : List F) = [CommRingOps.zero] := by rfl

theorem hemKernelFold_singleton {F : Type} [CommRingOps F] (φ a : F) :
    hemKernelFold φ [a] = [CommRingOps.zero] := by rfl

theorem hemBridgeFoldClaim_def {F : Type} [CommRingOps F]
    (claim w₀ w₁ w₂ c_F c_G φ θ α β : F) :
    hemBridgeFoldClaim claim w₀ w₁ w₂ c_F c_G φ θ α β =
      CommRingOps.add
        (CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub claim w₀)))
        (CommRingOps.add
          (CommRingOps.mul α
            (CommRingOps.add (CommRingOps.add w₀ (CommRingOps.mul φ w₁))
              (CommRingOps.mul θ
                (CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub claim w₀))))))
          (CommRingOps.mul β (CommRingOps.add c_F (CommRingOps.mul θ c_G)))) := by rfl

theorem verifyHemStages_nil_finalQuery {F : Type} [CommRingOps F] [DecidableEq F]
    (curOracle : Nat → F) (curDom : List F) (curDeg curMinAgree : Nat)
    (curKernel : List F) (curClaim : F) (finalCoeffs : List F) :
    verifyHemStages curOracle curDom curDeg curMinAgree curKernel curClaim []
        [.finalQuery finalCoeffs] =
      (decide (finalCoeffs.length ≤ curDeg + 1) &&
        decide (ringDot finalCoeffs curKernel = curClaim) &&
        checkQueriedCosets curDom curOracle finalCoeffs
          (List.range (Nat.min curMinAgree curDom.length))) := by rfl

theorem verifyHemStages_cons_stageFold {F : Type} [CommRingOps F] [DecidableEq F]
    (curOracle : Nat → F) (curDom : List F) (curDeg curMinAgree : Nat)
    (curKernel : List F) (curClaim : F)
    (st : HemWhirStageSpec F) (remStages : List (HemWhirStageSpec F))
    (stageOracle : Nat → F) (w₀ w₁ w₂ c_F c_G φ θ α β z₀ z₁ ood₀ ood₁ : F)
    (stageDecoded : List (List F)) (restTr : List (HemTranscriptRound F)) :
    verifyHemStages curOracle curDom curDeg curMinAgree curKernel curClaim (st :: remStages)
        (.stageFold stageOracle w₀ w₁ w₂ c_F c_G φ θ α β z₀ z₁ ood₀ ood₁ stageDecoded ::
          restTr) =
      (stageDecoded.any (fun P =>
          polyWitnessValid st.domainPts st.minAgree st.degBound stageOracle
            (hemKernelFold φ curKernel)
            (hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β) P &&
          decide (RoundPoly.evalCoeffs P z₀ = ood₀) &&
          decide (RoundPoly.evalCoeffs P z₁ = ood₁) &&
          checkQueriedCosets st.domainPts stageOracle P st.queriedCosets) &&
        verifyHemStages stageOracle st.domainPts st.degBound st.minAgree
          (hemKernelFold φ curKernel)
          (hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β) remStages restTr) := by rfl

theorem evalCascadeClaim_nil {F : Type} [CommRingOps F] (ss : List F) (abs : List (F × F)) :
    evalCascadeClaim ([] : List F) ss abs = CommRingOps.zero := by rfl

theorem evalCascadeClaim_cons {F : Type} [CommRingOps F]
    (e : F) (es : List F) (s : F) (ss : List F) (ab : F × F) (abs : List (F × F)) :
    evalCascadeClaim (e :: es) (s :: ss) (ab :: abs) =
      CommRingOps.add
        (CommRingOps.add (CommRingOps.mul ab.1 e) (CommRingOps.mul ab.2 s))
        (evalCascadeClaim es ss abs) := by
  cases ab; rfl

theorem evalCascadeOracle_nil {F : Type} [CommRingOps F] (domPts : List F)
    (abs : List (F × F)) (idx : Nat) :
    evalCascadeOracle domPts [] abs idx = CommRingOps.zero := by rfl

theorem evalCascadeOracle_cons {F : Type} [CommRingOps F] (domPts : List F)
    (O : Nat → F) (os : List (Nat → F)) (ab : F × F) (abs : List (F × F)) (idx : Nat) :
    evalCascadeOracle domPts (O :: os) (ab :: abs) idx =
      CommRingOps.add
        (CommRingOps.mul
          (CommRingOps.add ab.1 (CommRingOps.mul ab.2 (domPts.getD idx CommRingOps.zero)))
          (O idx))
        (evalCascadeOracle domPts os abs idx) := by
  cases ab; rfl

theorem hemFalseClaimInstance_def :
    hemFalseClaimInstance =
      { batchOracles := [fun _ => CommRingOps.zero]
        batchClaims := [CommRingOps.one]
        initDomainPts := [CommRingOps.zero, CommRingOps.one]
        initDegBound := 0
        initMinAgree := 2
        initKernel := [CommRingOps.one]
        stages := [] } := by rfl

end Qsag

public section
namespace Qsag

theorem hemFoldClaimUpdate_def {F : Type} [CommRingOps F] (gF gG cF cG theta alpha beta : F) :
    hemFoldClaimUpdate gF gG cF cG theta alpha beta =
      CommRingOps.add gG (CommRingOps.add
        (CommRingOps.mul alpha (CommRingOps.add gF (CommRingOps.mul theta gG)))
        (CommRingOps.mul beta (CommRingOps.add cF (CommRingOps.mul theta cG)))) := by
  unfold hemFoldClaimUpdate
  rfl

end Qsag
end

public section
namespace Qsag
 theorem hemInterleave_nil_left {F : Type} (ys : List F) : hemInterleave [] ys = [] := by
  cases ys <;> rfl
 theorem hemInterleave_cons_cons {F : Type} (a b : F) (xs ys : List F) :
    hemInterleave (a :: xs) (b :: ys) = a :: b :: hemInterleave xs ys := by rfl

-- Equations for `Tests/HemMultistageCascadeTeeth` (no body exposed).
/-! ## Executed Hem checker fixtures and teeth

These evaluate `polyWitnessValid`, `HemStatementValid`, `verifyHemAffineWhir` and
`mutantVerifyHemAffineWhirUnincremented` over `QuarticGoldilocks`, whose bodies are visible only in this
module. They are audited and paired in `Tests/HemExtractedOpeningBridgeTests`; the facts stated over a
literal instance are cited by `Protocol/Aggregation/HemOpening`, which owns `hemZeroOracleClaimInstance`. -/
section HemExecutedTeeth
set_option exponentiation.threshold 2048
set_option maxRecDepth 65536

/-- The former checker, retained only as the mutation under test: it forgets to compare
    the number of batch claims to the number of batch oracles. -/
def verifyHemMissingBatchArity {F : Type} [CommRingOps F] [DecidableEq F]
    (inst : HemWhirInstance F) (tr : List (HemTranscriptRound F)) : Bool :=
  match tr with
  | .cascade shifts weights decoded :: rest =>
    decide (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16) &&
    decide (shifts.length = inst.batchClaims.length) &&
    decide (weights.length = inst.batchClaims.length) &&
    decoded.any (fun P => polyWitnessValid inst.initDomainPts inst.initMinAgree
      (inst.initDegBound + 1) (evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
      inst.initKernel (evalCascadeClaim inst.batchClaims shifts weights) P) &&
    verifyHemStages (evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
      inst.initDomainPts (inst.initDegBound + 1) inst.initMinAgree inst.initKernel
      (evalCascadeClaim inst.batchClaims shifts weights) inst.stages rest
  | _ => false

def hemMissingClaimInstance : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun _ => CommRingOps.one]
    batchClaims := []
    initDomainPts := [CommRingOps.zero, CommRingOps.one]
    initDegBound := 0
    initMinAgree := 2
    initKernel := [CommRingOps.one]
    stages := [] }

/-- The old checker accepted an invalid statement by dropping its only oracle. The repaired
    checker rejects exactly the same transcript, even though its polynomial checks succeed. -/
theorem tooth_missing_batch_claim_erases_oracle :
    ¬ HemStatementValid hemMissingClaimInstance ∧
    verifyHemMissingBatchArity hemMissingClaimInstance
      [.cascade [] [] [[]], .finalQuery []] = true ∧
    verifyHemAffineWhir hemMissingClaimInstance
      [.cascade [] [] [[]], .finalQuery []] = false := by
  exact ⟨fun h => h.2, by decide, by decide⟩

def qgNat : Nat → QuarticGoldilocks
  | 0 => CommRingOps.zero
  | n + 1 => CommRingOps.add (qgNat n) CommRingOps.one

def toothDeg1Dom : List QuarticGoldilocks :=
  [qgNat 0, qgNat 1, qgNat 2, qgNat 3]

def toothDeg1Pool : List QuarticGoldilocks :=
  [qgNat 0, qgNat 1, CommRingOps.sub CommRingOps.zero CommRingOps.one]

/-- **Unincremented Cascade Agreement Counterexample
    (`tooth_verifyHemAffineWhir_unincremented_agree_accepts_all`)**:
    In `mutantVerifyHemAffineWhirUnincremented`, `.cascade` checks `polyWitnessValid` at
    `inst.initMinAgree` (`A₀`) rather than `A₀ + 1`. At `domPts = [0, 1, 2]`, `d₀ = 0`, `A₀ = 2`,
    the oracle `0 ↦ 1, _ ↦ 0` with claim `1` violates `HemStatementValid inst` at `A₀ = 2`, yet
    has an `(A₀ - 1) = 1`-agreeing witness `G = [1]` and therefore passes the deliberately stale verifier
    via `P(z) = α - α z` on **every** `(α, β) ∈ prodPool S` (`100%` acceptance)!
    This proves that the `initMinAgree - 1` premise in `arbitrary_batch_cascade_fiber_bound`
    cannot be weakened to `¬ HemStatementValid inst` without the agreement increment now enforced by `verifyHemAffineWhir`. -/
def toothUnincCascadeInst : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun idx => if idx = 0 then qgNat 1 else qgNat 0]
    batchClaims := [qgNat 1]
    initDomainPts := [qgNat 0, qgNat 1, qgNat 2]
    initDegBound := 0
    initMinAgree := 2
    initKernel := [qgNat 1]
    stages := [] }

theorem tooth_verifyHemAffineWhir_unincremented_agree_accepts_all :
    ∃ inst : HemWhirInstance QuarticGoldilocks,
      ¬ HemStatementValid inst ∧
      HemStatementValid { inst with initMinAgree := 1 } ∧
      ∀ ch : Fin (prodPool toothDeg1Pool).length,
        let p := (prodPool toothDeg1Pool).get ch
        let P : List QuarticGoldilocks := [p.1, CommRingOps.sub CommRingOps.zero p.1]
        mutantVerifyHemAffineWhirUnincremented inst
          [.cascade [qgNat 0] [p] [P], .finalQuery P] = true := by
  refine ⟨toothUnincCascadeInst, ?_, ⟨by decide, ⟨[qgNat 1], by decide +kernel⟩, trivial⟩, by
    rw [prodPool_eq]
    decide +kernel⟩
  rintro ⟨_, ⟨G, hG⟩, _⟩
  unfold polyWitnessValid toothUnincCascadeInst at hG
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
  rcases hG with ⟨⟨hGLen, hGAg⟩, hGDot⟩
  rcases G with _ | ⟨c, _ | _⟩
  · change CommRingOps.zero = qgNat 1 at hGDot
    exact (by decide : CommRingOps.zero ≠ qgNat 1) hGDot
  · have hOne : qgNat 1 = CommRingOps.one := by decide
    have hc1 : c = CommRingOps.one := by
      rw [hOne] at hGDot
      simpa only [ringDot_cons_cons, ringDot_nil_left, ringDot_nil_right, LawfulCommRing.mul_one, LawfulCommRing.add_zero] using hGDot
    subst hc1
    exact absurd hGAg (by decide +kernel)
  · simp only [List.length_cons] at hGLen
    omega

/-- The repaired verifier rejects the old attack at a nonzero challenge; the zero
    challenge still legitimately belongs to the bad-challenge set. -/
theorem tooth_incremented_cascade_rejects_old_attack :
    ∃ P : List QuarticGoldilocks,
    mutantVerifyHemAffineWhirUnincremented toothUnincCascadeInst
      [.cascade [qgNat 0] [(qgNat 1, qgNat 0)] [P], .finalQuery P] = true ∧
    verifyHemAffineWhir toothUnincCascadeInst
      [.cascade [qgNat 0] [(qgNat 1, qgNat 0)] [P], .finalQuery P] = false := by
  refine ⟨[qgNat 1, CommRingOps.sub (qgNat 0) (qgNat 1)], ?_⟩
  decide +kernel

/-- The zero-oracle / claim-one instance on the domain `[0, 1]` (the body of
    `hemZeroOracleClaimInstance [0, 1] 0 2 []`): the cascade transcript with shift `0`, weight `(0, 1)` and
    the empty polynomial is accepted, and exactly two of the four weight pairs are. -/
theorem verifyHemAffineWhir_zeroOracleClaim_dom01_kat :
    verifyHemAffineWhir
      ({ batchOracles := [fun _ => CommRingOps.zero]
         batchClaims := [CommRingOps.one]
         initDomainPts := [CommRingOps.zero, CommRingOps.one]
         initDegBound := 0
         initMinAgree := 2
         initKernel := [CommRingOps.one]
         stages := [] } : HemWhirInstance QuarticGoldilocks)
      [.cascade [CommRingOps.zero] [(CommRingOps.zero, CommRingOps.one)] [[]], .finalQuery []] = true ∧
    ((prodPool ([CommRingOps.zero, CommRingOps.one] : List QuarticGoldilocks)).filter (fun p =>
      verifyHemAffineWhir
        ({ batchOracles := [fun _ => CommRingOps.zero]
           batchClaims := [CommRingOps.one]
           initDomainPts := [CommRingOps.zero, CommRingOps.one]
           initDegBound := 0
           initMinAgree := 2
           initKernel := [CommRingOps.one]
           stages := [] } : HemWhirInstance QuarticGoldilocks)
        [.cascade [CommRingOps.zero] [p] [[]], .finalQuery []])).length = 2 := by
  rw [prodPool_eq]
  decide

/-- Constant-`1` oracle and claim `1` on `[0, 1]` (`compactHemInst` in `Tests/CompositionInstances`):
    valid statement, and accepted by `verifyHemAffineWhir` on the canonical weight-`(1, 0)` transcript. -/
theorem verifyHemAffineWhir_oneOracleClaim_dom01_kat :
    HemStatementValid
      ({ batchOracles := [fun _ => CommRingOps.one]
         batchClaims := [CommRingOps.one]
         initDomainPts := [CommRingOps.zero, CommRingOps.one]
         initDegBound := 0
         initMinAgree := 2
         initKernel := [CommRingOps.one]
         stages := [] } : HemWhirInstance QuarticGoldilocks) ∧
    verifyHemAffineWhir
      ({ batchOracles := [fun _ => CommRingOps.one]
         batchClaims := [CommRingOps.one]
         initDomainPts := [CommRingOps.zero, CommRingOps.one]
         initDegBound := 0
         initMinAgree := 2
         initKernel := [CommRingOps.one]
         stages := [] } : HemWhirInstance QuarticGoldilocks)
      [.cascade [CommRingOps.zero] [(CommRingOps.one, CommRingOps.zero)] [[CommRingOps.one]],
       .finalQuery [CommRingOps.one]] = true := by
  exact ⟨⟨by decide, ⟨[CommRingOps.one], by decide +kernel⟩, trivial⟩, by decide +kernel⟩

/-- Executed half of `tooth_equal_degree_invalid_mixture`: after `θ = -1` mixing the two zero words
    carry the valid claim zero. -/
theorem polyWitnessValid_theta_neg_one_mixture_kat :
    polyWitnessValid ([CommRingOps.zero, CommRingOps.one] : List QuarticGoldilocks) 2 0
      (fun _ => CommRingOps.add CommRingOps.zero
        (CommRingOps.mul (CommRingOps.sub CommRingOps.zero CommRingOps.one) CommRingOps.zero))
      [CommRingOps.one]
      (CommRingOps.add CommRingOps.one
        (CommRingOps.mul (CommRingOps.sub CommRingOps.zero CommRingOps.one) CommRingOps.one)) [] = true := by
  decide

/-- Regression for the old unincremented checker: the restricted cascade IOP
    already required the stronger agreement threshold now enforced by the full checker. -/
def hemCoreAgreementBoundaryInstance : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun i => if i = 1 then CommRingOps.one else CommRingOps.zero]
    batchClaims := [CommRingOps.one]
    initDomainPts := [CommRingOps.zero, CommRingOps.one,
      CommRingOps.add CommRingOps.one CommRingOps.one]
    initDegBound := 0
    initMinAgree := 2
    initKernel := [CommRingOps.zero, CommRingOps.one]
    stages := [] }

private theorem nodup_filter_eq_const_length_le_one {α : Type} [DecidableEq α] (v : α) (l : List α)
    (h : l.Nodup) : (l.filter (fun z => decide (v = z))).length ≤ 1 := by
  have hNd : (l.filter (fun z => decide (v = z))).Nodup := List.Pairwise.filter _ h
  have hAll : ∀ z ∈ l.filter (fun z => decide (v = z)), v = z :=
    fun z hz => of_decide_eq_true (List.mem_filter.mp hz).2
  generalize l.filter (fun z => decide (v = z)) = f at hNd hAll
  match f, hNd, hAll with
  | [], _, _ => exact Nat.zero_le 1
  | [_], _, _ => exact Nat.le_refl 1
  | a :: b :: _, hNd, hAll =>
    exfalso
    have hab : a = b := (hAll a List.mem_cons_self).symm.trans
      (hAll b (List.mem_cons_of_mem _ List.mem_cons_self))
    exact (List.nodup_cons.mp hNd).1 (hab ▸ List.mem_cons_self)

/-- **Equal-Degree `θ`-Exception Necessity Counterexample (`tooth_equal_degree_drop_theta_exception_unsound`)**:
    Let `D = [0, 1, 2, 3]`, `S = [0, 1, -1]`, `d = 0, A = 3`, `f(z) = z`, `g(z) = z`, and all claims `0`.
    Neither `(f, 0)` nor `(g, 0)` admits any degree-`≤ 0` witness at agreement `≥ A - 1 = 2`
    (`gsDecodeList 0 2 D id = []`). Yet at `θ = -1` (`iθ = 2`), `f + θ g = 0` and **all**
    `|prodPool S| = 9 = |S|^2` pairs `(α, β)` accept `P(X) = X` (`deg 1 ≤ d + 1`), proving that
    the `(badTheta + ...) · |prodPool S|` term in `equal_degree_three_challenge_bound` cannot be omitted. -/
theorem tooth_equal_degree_drop_theta_exception_unsound :
    ∃ iθ : Fin toothDeg1Pool.length,
      (gsDecodeList 0 2 toothDeg1Dom (fun z => z)).length = 0 ∧
      (∀ Fp : List QuarticGoldilocks, Fp.length ≤ 1 →
        2 ≤ (toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = z))).length → False) ∧
      (prodPool toothDeg1Pool).length = 9 ∧
      ∀ ch : Fin (prodPool toothDeg1Pool).length,
        affineMcaAccepts toothDeg1Dom toothDeg1Pool 1 4
          ((fun z => z),
           fun z => CommRingOps.add z (CommRingOps.mul (toothDeg1Pool.get iθ) z))
          ch.1 [qgNat 0, qgNat 1] = true ∧
        ringDot [qgNat 0, qgNat 1] [qgNat 1] =
          hemFoldClaimUpdate (qgNat 0) (qgNat 0) (qgNat 0) (qgNat 0)
            (toothDeg1Pool.get iθ)
            ((prodPool toothDeg1Pool).get ch).1 ((prodPool toothDeg1Pool).get ch).2 := by
  -- `gsDecodeList` is sealed in `Coding/ReedSolomon` and cannot be executed here: the empty decoding
  -- list is derived from `mem_gsDecodeList_iff` and the direct agreement count below.
  have hD : toothDeg1Dom.Nodup := by decide +kernel
  have hNo : ∀ Fp : List QuarticGoldilocks, Fp.length ≤ 1 →
      2 ≤ (toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = z))).length → False := by
    intro Fp hLen hAg
    have hConst : ∃ v : QuarticGoldilocks, ∀ z, RoundPoly.evalCoeffs Fp z = v := by
      match Fp, hLen with
      | [], _ => exact ⟨CommRingOps.zero, fun _ => rfl⟩
      | [c], _ =>
        exact ⟨c, fun z => by
          simp only [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil, LawfulCommRing.mul_zero,
            LawfulCommRing.add_zero]⟩
      | _ :: _ :: _, h => exact absurd h (by simp only [List.length_cons]; omega)
    obtain ⟨v, hv⟩ := hConst
    have hLe := nodup_filter_eq_const_length_le_one v toothDeg1Dom hD
    simp only [hv] at hAg
    omega
  have hEmpty : gsDecodeList 0 2 toothDeg1Dom (fun z => z) = [] := by
    generalize hC : gsDecodeList 0 2 toothDeg1Dom (fun z => z) = cands
    match cands, hC with
    | [], _ => rfl
    | p :: _, hC =>
      exfalso
      have hMem : p ∈ gsDecodeList 0 2 toothDeg1Dom (fun z => z) := hC ▸ List.mem_cons_self
      have h := (mem_gsDecodeList_iff (fun z => z) hD (by decide) p).mp hMem
      exact hNo p.coeffs h.1 h.2
  refine ⟨⟨2, by decide⟩, by rw [hEmpty]; rfl, hNo, by rw [prodPool_length]; decide, by
    unfold affineMcaAccepts
    rw [prodPool_eq]
    decide +kernel⟩

/-- Executed checker values behind `tooth_core_agreement_is_stronger_than_checker`
    (`Protocol/Aggregation/HemRbrSoundness`), on the transcript that `assembleHemCoreTranscript` builds
    for challenge index `2` (pair `(1, 0)`): the stale checker accepts, the incremented one rejects. -/
theorem hemCoreAgreementBoundary_transcript_kat :
    mutantVerifyHemAffineWhirUnincremented hemCoreAgreementBoundaryInstance
      [.cascade [CommRingOps.zero] [(CommRingOps.one, CommRingOps.zero)]
        [[CommRingOps.zero, CommRingOps.one]], .finalQuery [CommRingOps.zero, CommRingOps.one]] = true ∧
    verifyHemAffineWhir hemCoreAgreementBoundaryInstance
      [.cascade [CommRingOps.zero] [(CommRingOps.one, CommRingOps.zero)]
        [[CommRingOps.zero, CommRingOps.one]], .finalQuery [CommRingOps.zero, CommRingOps.one]] = false := by
  decide

/-! Facts about the fixtures `qgNat` / `toothDeg1Dom` for the witnesses of
`Protocol/Aggregation/HemOpening` (the fixture bodies are not exported). -/
theorem toothDeg1Dom_eq : toothDeg1Dom = [qgNat 0, qgNat 1, qgNat 2, qgNat 3] := by rfl
theorem qgNat_zero : qgNat 0 = CommRingOps.zero := by rfl
theorem qgNat_one : qgNat 1 = CommRingOps.one := by decide
theorem toothDeg1Dom_fixture_facts :
    toothDeg1Dom.Nodup ∧ (CommRingOps.zero : QuarticGoldilocks) ∈ toothDeg1Dom ∧
    ¬ 2 ≤ (toothDeg1Dom.filter
      (fun z => decide (RoundPoly.evalCoeffs [CommRingOps.one] z = qgNat 0))).length := by
  decide +kernel

#verify_constructive
  Qsag.tooth_missing_batch_claim_erases_oracle
  Qsag.qgNat_one
  Qsag.toothDeg1Dom_fixture_facts
  Qsag.tooth_equal_degree_drop_theta_exception_unsound
  Qsag.hemCoreAgreementBoundary_transcript_kat
  Qsag.tooth_verifyHemAffineWhir_unincremented_agree_accepts_all
  Qsag.tooth_incremented_cascade_rejects_old_attack
  Qsag.verifyHemAffineWhir_zeroOracleClaim_dom01_kat
  Qsag.verifyHemAffineWhir_oneOracleClaim_dom01_kat
  Qsag.polyWitnessValid_theta_neg_one_mixture_kat
end HemExecutedTeeth

#export_eqns evalCascadePolySum
-- Equations for the executed fold witnesses of `Cwyz26EqualDegreeAndMultiFold` (no body exposed).
#export_eqns hemInterleave hemKernelFold hemBridgeFoldClaim hemFoldClaimUpdate hemCosetAgreeCount
  polyWitnessValid
end Qsag
end
