module
public import Qsag.Coding.ReedSolomon
public import Qsag.Coding.GuruswamiSudan
public import Qsag.Tactic.Prelude

public section

section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

/-! ## List lemmas & Mutual Correlated Agreement Bound -/

theorem list_getD_eq_get {α : Type} :
    ∀ (xs : List α) (d : α) (idx : Fin xs.length), xs.getD idx.1 d = xs.get idx
  | [], _, idx => absurd idx.2 (Nat.not_lt_zero _)
  | _ :: _, _, ⟨0, _⟩ => rfl
  | _ :: xs, d, ⟨i + 1, hi⟩ => list_getD_eq_get xs d ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem list_get_mem {α : Type} : ∀ (xs : List α) (k : Fin xs.length), xs.get k ∈ xs
  | _ :: _, ⟨0, _⟩ => .head _
  | _ :: xs, ⟨k + 1, hk⟩ => .tail _ (list_get_mem xs ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

theorem nodup_get_inj {α : Type} :
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

theorem not_not_forall_mem {α : Type} (Q : α → Prop) :
    ∀ l : List α, (∀ a ∈ l, ¬¬ Q a) → ¬¬ (∀ a ∈ l, Q a)
  | [], _ => fun h => h (fun _ hm => nomatch hm)
  | a :: l, h => fun hn =>
    h a (.head l) (fun hQa =>
      not_not_forall_mem Q l (fun a' ha' => h a' (.tail a ha')) (fun hRest =>
        hn (fun a' ha' => by
          rcases List.mem_cons.mp ha' with hEq | h1
          · rw [hEq]; exact hQa
          · exact hRest a' h1)))

theorem list_finite_choice {α β : Type} [DecidableEq α] (Q : α → β → Prop) (dflt : β) :
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

private theorem length_filter_split_bool {α : Type} (p : α → Bool) :
    ∀ l : List α, l.length = (l.filter p).length + (l.filter (fun x => !p x)).length
  | [] => rfl
  | a :: l => by
    have ih := length_filter_split_bool p l
    cases hp : p a <;>
      simp only [List.filter_cons, hp, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] <;> omega

private theorem length_filter_filter_le_bool {α : Type} (p q : α → Bool) :
    ∀ l : List α, ((l.filter q).filter p).length ≤ (l.filter p).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := length_filter_filter_le_bool p q l
    cases hq : q a <;> cases hp : p a <;>
      simp only [List.filter_cons, hq, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
      omega

section McaDefs
variable {F : Type} [LawfulField F] [DecidableEq F]

/-- **Correlated agreement**: ONE polynomial pair `(F_poly, G_poly)` (`deg F_poly ≤ d`,
    `deg G_poly ≤ d - 1`) simultaneously agrees with the received words `(f, g)` on at least `A`
    coordinates of the evaluation domain `D`. -/
@[expose] def HasCorrelatedAgreement (d A : Nat) (f g : F → F) (D : List F) : Prop :=
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
  have hSplit := length_filter_split_bool
    (fun z => decide (RoundPoly.evalCoeffs F_poly z = f z) &&
      decide (RoundPoly.evalCoeffs G_poly z = g z))
    (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs P z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)))))
  have hLe := length_filter_filter_le_bool
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

/-- Verifier predicate of the affine-fold proximity IOP: challenge index `c` selects
    `(α, β) = (prodPool S)[c]`, and the prover's response `P` has degree `≤ d` and agrees with the
    fold word `f + (α + β X) g` on at least `A` points of `D`. -/
@[expose] def affineMcaAccepts (D S : List F) (d A : Nat) (x : (F → F) × (F → F)) (c : Nat)
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

/-- **Mutual correlated agreement bound** for the affine fold of words on `D` with challenges
    `(α, β) ∈ S × S`, degree bound `d` and agreement threshold `A`: for every pair of words
    WITHOUT correlated agreement `≥ A - 1`, at most `bad` challenges admit a degree-`≤ d`
    polynomial `A`-close to the fold word. -/
@[expose] def AffineMcaBound (D S : List F) (d A bad : Nat) : Prop :=
  ∀ x : (F → F) × (F → F), ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D →
    ∀ L : List (Fin (prodPool S).length), L.Nodup →
      (∀ ch ∈ L, ¬¬ ∃ P : List F, affineMcaAccepts D S d A x ch.1 P = true) →
      L.length ≤ bad

/-- The bound is monotone in the number of exceptional challenges. -/
theorem AffineMcaBound.mono {D S : List F} {d A bad bad' : Nat}
    (h : AffineMcaBound D S d A bad) (hLe : bad ≤ bad') : AffineMcaBound D S d A bad' :=
  fun x hFar L hNd hEx => Nat.le_trans (h x hFar L hNd hEx) hLe

/-- **Welch–Berlekamp instance of the mutual correlated agreement bound**, proved from
    `welch_berlekamp_affine_proximity_gap` in the regime `2 |D| + d + 1 < 3 A`. -/
theorem affineMcaBound_welch_berlekamp (D S : List F) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup) (hAD : A ≤ D.length) (hWB : 2 * D.length + d + 1 < 3 * A) :
    AffineMcaBound D S d A (Nat.max S.length (D.length * (D.length - 1) / 2)) := by
  intro x hFar L hNd hEx
  apply Decidable.byContradiction
  intro hGt
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
    (fun p hp hW => hFar (hasCorrelatedAgreement_of_affineWitnessS1 hW (hP_of p hp).2))
  rw [List.length_map] at hBound
  exact hBound

end McaDefs

theorem exists_fin_of_mem {α : Type} : ∀ (l : List α) (a : α), a ∈ l →
    ∃ i : Fin l.length, l.get i = a
  | _ :: _, _, .head _ => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
  | _ :: l, a, .tail _ h => by
    obtain ⟨i, hi⟩ := exists_fin_of_mem l a h
    exact ⟨⟨i.1 + 1, Nat.succ_lt_succ i.2⟩, hi⟩

theorem filter_eq_self_of_all {α : Type} (p : α → Bool) : ∀ l : List α,
    (∀ a ∈ l, p a = true) → l.filter p = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons_of_pos (h a (.head _)),
      filter_eq_self_of_all p l (fun b hb => h b (.tail _ hb))]

theorem nodup_filter {α : Type} (p : α → Bool) : ∀ l : List α, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | a :: l, h => by
    have hp := List.pairwise_cons.mp h
    have ih := nodup_filter p l hp.2
    cases hpa : p a with
    | true =>
      rw [List.filter_cons_of_pos hpa]
      exact List.pairwise_cons.mpr ⟨fun b hb => hp.1 b (List.mem_filter.mp hb).1, ih⟩
    | false =>
      rw [List.filter_cons_of_neg (by rw [hpa]; exact Bool.false_ne_true)]
      exact ih

/-! ## Roots on a fixed line -/

namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

/-- **Candidates per challenge.** If `Q(X, α + βX, Z) ≠ 0`, at most `deg_Z Q` polynomials `P`
    satisfy `Q(X, α + βX, P(X)) = 0`. -/
theorem roots_on_line_card_le (Q : Poly3 F) (α β : F) (hnv : lineSpec Q α β ≠ zero)
    (Ps : List (UPoly F)) (hnd : Ps.Nodup) (hroot : ∀ P ∈ Ps, evalAffineLine Q α β P = zero) :
    Ps.length ≤ Q.degZ := by
  have h := gs_formal_root_bound (lineSpec Q α β).natDeg (lineSpec Q α β).coeffs Ps
    (by show _ ≤ (lineSpec Q α β).coeffs.length - 1 + 1; omega)
    (exists_mem_ne_zero_of_coeffAt _ _ (coeffAt_natDeg_ne_zero hnv)) hnd (fun P hP => by
      rw [← eval_eq]
      rw [lineSpec_apply]
      show eval₂ (RingHom.id _) P ((mapHom (evalHom (line α β))).toFun Q) = zero
      rw [eval₂_mapHom]
      simpa only [evalAffineLine_eq_eval₂, RingHom.id_comp] using hroot P hP)
  exact Nat.le_trans h (by simpa only [lineSpec_apply, degZ_eq] using natDeg_mapHom_le (evalHom (line α β)) Q)

end Poly3

/-! ## Every bound is at least the size of the challenge set -/

section LowerBound
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

local instance : NoZeroDivisors F := LawfulField.toNoZeroDivisors F

/-- The received words `f = 0`, `g(z) = 1/(z + 1)`. -/
def poleWords : (F → F) × (F → F) := (fun _ => zero, fun z => LawfulField.inv (add z one))

omit [DecidableEq F] in
theorem add_one_ne_zero {D : List F} (hneg : neg one ∉ D) {z : F} (hz : z ∈ D) :
    add z one ≠ zero := fun e => hneg (by
  have h1 : z = add (add z one) (neg one) := by constructive_ring
  rw [e, LawfulCommRing.zero_add] at h1
  rw [← h1]; exact hz)

/-- `g(z) = 1/(z + 1)` agrees with a polynomial of degree below `d` on at most `d` points
    of a domain avoiding `-1`, so the pole words have no correlated agreement `≥ A - 1`. -/
theorem poleWords_far (D : List F) (d A : Nat) (hD : D.Nodup) (hneg : neg one ∉ D)
    (hd : 1 ≤ d) (hA : d + 2 ≤ A) :
    ¬ HasCorrelatedAgreement d (A - 1) (poleWords (F := F)).1 poleWords.2 D := by
  rintro ⟨Fp, Gp, _, hG, hlen⟩
  generalize hH : sub (mul (ofList [(one : F), one]) (ofList Gp)) one = H
  have hHeval : ∀ z, H.eval z = sub (mul (add one z) (evalCoeffs Gp z)) one := by
    intro z
    rw [← hH]
    rw [← evalHom_apply]
    show (evalHom z).toFun (sub (mul (ofList [(one : F), one]) (ofList Gp)) one) = _
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_one, evalHom_apply, evalHom_apply,
      eval_ofList, eval_ofList]
    show sub (mul (add one (mul z (add one (mul z zero)))) (evalCoeffs Gp z)) one = _
    constructive_ring
  have hHne : H ≠ zero := fun e => by
    have h1 := hHeval (neg one)
    rw [e] at h1
    have h2 : (zero : UPoly F).eval (neg one) = zero := eval₂_zero _ _
    rw [h2, LawfulCommRing.add_right_neg, LawfulCommRing.zero_mul] at h1
    have h3 : (one : F) = sub zero (sub zero one) := by constructive_ring
    rw [← h1, LawfulCommRing.sub_self] at h3
    exact LawfulField.one_ne_zero h3
  have hdeg : H.natDeg ≤ d := by
    have h1 := natDeg_mul_le (ofList [(one : F), one]) (ofList Gp)
    have h2 := natDeg_ofList_le [(one : F), one]
    have h3 := natDeg_ofList_le Gp
    have h4 := (degFn_natDeg (R := F)).add_le (mul (ofList [(one : F), one]) (ofList Gp)) (neg one)
    have h5 := (degFn_natDeg (R := F)).neg_le one
    have h6 := natDeg_one (R := F)
    have h7 : H = add (mul (ofList [(one : F), one]) (ofList Gp)) (neg one) := by
      rw [← hH]; exact LawfulCommRing.sub_eq_add_neg _ _
    have h2' : (ofList [(one : F), one]).natDeg ≤ 1 := h2
    rw [h7]
    omega
  have hroot : ∀ z ∈ D.filter (fun z => decide (evalCoeffs Fp z = (poleWords (F := F)).1 z) &&
      decide (evalCoeffs Gp z = (poleWords (F := F)).2 z)), evalCoeffs H.coeffs z = zero := by
    intro z hz
    obtain ⟨hzD, hp⟩ := List.mem_filter.mp hz
    have hg : evalCoeffs Gp z = LawfulField.inv (add z one) :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hp).2
    rw [← eval_eq, hHeval, hg, LawfulCommRing.add_comm one z,
      LawfulField.mul_inv_cancel (add_one_ne_zero hneg hzD), LawfulCommRing.sub_self]
  have hcount := gs_formal_root_bound H.natDeg H.coeffs _
    (by show _ ≤ H.coeffs.length - 1 + 1; omega)
    (exists_mem_ne_zero_of_coeffAt _ _ (coeffAt_natDeg_ne_zero hHne)) (nodup_filter _ D hD) hroot
  omega

/-- On a diagonal challenge `(β, β)` the constant `β` is accepted with full agreement. -/
theorem poleWords_accept (D S : List F) (d A : Nat) (hneg : neg one ∉ D) (hAD : A ≤ D.length)
    (ch : Fin (prodPool S).length) (β : F) (hch : (prodPool S).get ch = (β, β)) :
    affineMcaAccepts D S d A poleWords ch.1 [β] = true := by
  unfold affineMcaAccepts
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [list_getD_eq_get (prodPool S) _ ch, hch]
  refine ⟨⟨ch.2, Nat.succ_le_succ (Nat.zero_le d)⟩, ?_⟩
  rw [filter_eq_self_of_all _ D (fun z hz => decide_eq_true (by
    show add β (mul z zero) = add zero (mul (add β (mul β z)) (LawfulField.inv (add z one)))
    have e : mul (add β (mul β z)) (LawfulField.inv (add z one)) =
        mul β (mul (add z one) (LawfulField.inv (add z one))) := by constructive_ring
    rw [e, LawfulField.mul_inv_cancel (add_one_ne_zero hneg hz)]
    constructive_ring))]
  exact hAD

/-- **Necessity of the field-size term.** Any mutual correlated agreement bound for the
    affine fold on a domain avoiding `-1` has at least `|S|` exceptional challenges: the
    diagonal `(β, β)`, `β ∈ S`. -/
theorem affineMcaBound_ge_card (D S : List F) (d A bad : Nat) (h : AffineMcaBound D S d A bad)
    (hD : D.Nodup) (hS : S.Nodup) (hneg : neg one ∉ D) (hd : 1 ≤ d) (hA : d + 2 ≤ A)
    (hAD : A ≤ D.length) : S.length ≤ bad := by
  if h0 : (prodPool S).length = 0 then
    rw [prodPool_length] at h0
    have : S.length = 0 := by
      rcases Nat.eq_zero_or_pos S.length with h1 | h1
      · exact h1
      · exact absurd h0 (Nat.ne_of_gt (Nat.mul_pos h1 h1))
    rw [this]; exact Nat.zero_le _
  else
    have hidx : ∀ β ∈ S, ∃ ch : Fin (prodPool S).length, (prodPool S).get ch = (β, β) :=
      fun β hβ => exists_fin_of_mem _ _ (mem_prodPool_iff.mpr ⟨hβ, hβ⟩)
    obtain ⟨f, hf⟩ := list_finite_choice (fun β ch => (prodPool S).get ch = (β, β))
      ⟨0, Nat.pos_of_ne_zero h0⟩ S hidx
    have hNd : (S.map f).Nodup := List.pairwise_map.mpr (List.Pairwise.imp_of_mem
      (fun {a b} ha hb hne e => hne (by
        have h1 := (hf a ha).symm.trans ((congrArg (prodPool S).get e).trans (hf b hb))
        exact (Prod.mk.inj h1).1)) hS)
    have key := h poleWords (poleWords_far D d A hD hneg hd hA) (S.map f) hNd (fun ch hch hno => by
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hch
      exact hno ⟨[β], poleWords_accept D S d A hneg hAD (f β) β (hf β hβ)⟩)
    rwa [List.length_map] at key

/-- A bound `Dg² + 2·d·Dg` with no term in the size of the challenge set is not a mutual
    correlated agreement bound once `|S|` exceeds it. -/
theorem affineMcaBound_without_field_term_fails (D S : List F) (d A Dg : Nat) (hD : D.Nodup)
    (hS : S.Nodup) (hneg : neg one ∉ D) (hd : 1 ≤ d) (hA : d + 2 ≤ A) (hAD : A ≤ D.length)
    (hbig : Dg ^ 2 + 2 * d * Dg < S.length) : ¬ AffineMcaBound D S d A (Dg ^ 2 + 2 * d * Dg) :=
  fun h => Nat.not_le_of_lt hbig (affineMcaBound_ge_card D S d A _ h hD hS hneg hd hA hAD)

end LowerBound

/-! ## Witnesses -/

end Qsag

end

section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

section Persistent
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly Poly3

local instance : NoZeroDivisors F := LawfulField.toNoZeroDivisors F

/-- `P` agrees at `z` with the affine fold `f(z) + (α + β z)·g(z)` of `x = (f, g)`. -/
@[expose] def foldAgreePt (x : (F → F) × (F → F)) (α β : F) (P : UPoly F) (z : F) : Bool :=
  decide (P.eval z = add (x.1 z) (mul (add α (mul β z)) (x.2 z)))

/-- **`[CWYZ26]` `B`-Persistence**: `(α, β, P)` has a rational explanation `G = H / L`,
    `F = P - (α + β X) G` (`L ≠ 0`, `deg L ≤ 1`, `deg H ≤ d`) agreeing with `(f, g)` on at
    least `B` coordinates of `D` where `L(z) ≠ 0`. -/
@[expose] def IsPersistent (x : (F → F) × (F → F)) (D : List F) (d B : Nat)
    (α β : F) (P : UPoly F) : Prop :=
  ∃ H L : UPoly F, L ≠ zero ∧ L.natDeg ≤ 1 ∧ H.natDeg ≤ d ∧
    B ≤ (D.filter (fun z =>
      decide (L.eval z ≠ zero) &&
      foldAgreePt x α β P z &&
      decide (H.eval z = mul (x.2 z) (L.eval z)))).length

private theorem eval_line_eq (a b z : F) :
    (line a b).eval z = add a (mul b z) := by
  show (ofList [a, b]).eval z = _
  rw [eval_ofList]
  show add a (mul z (add b (mul z zero))) = add a (mul b z)
  constructive_ring

private theorem natDeg_line_le (a b : F) : (line a b).natDeg ≤ 1 :=
  natDeg_ofList_le [a, b]

private theorem line_ne_zero_of_ne {a b : F} (h : ¬ (a = zero ∧ b = zero)) :
    line a b ≠ zero := fun e => h (by
  have h0 : line (zero : F) zero = zero := line_zero
  exact line_inj (e.trans h0.symm))

private theorem natDeg_sub_le_max {R : Type} [LawfulCommRing R] [DecidableEq R]
    (p q : UPoly R) (B : Nat) (hp : p.natDeg ≤ B) (hq : q.natDeg ≤ B) :
    (sub p q).natDeg ≤ B := by
  rw [LawfulCommRing.sub_eq_add_neg]
  have h1 := (degFn_natDeg (R := R)).add_le p (neg q)
  have h2 := (degFn_natDeg (R := R)).neg_le q
  omega

private theorem eval_sub_eq {R : Type} [LawfulCommRing R] [DecidableEq R]
    (p q : UPoly R) (z : R) : (sub p q).eval z = sub (p.eval z) (q.eval z) := by
  simpa only [evalHom_apply] using RingHom.map_sub (evalHom z) p q

private theorem eval_mul_eq {R : Type} [LawfulCommRing R] [DecidableEq R]
    (p q : UPoly R) (z : R) : (mul p q).eval z = mul (p.eval z) (q.eval z) := by
  simpa only [evalHom_apply] using RingHom.map_mul (evalHom z) p q

private theorem uPoly_roots_le_natDeg (P : UPoly F) (hP : P ≠ zero) (zs : List F)
    (hNd : zs.Nodup) (hRoot : ∀ z ∈ zs, P.eval z = zero) :
    zs.length ≤ P.natDeg := by
  refine gs_formal_root_bound P.natDeg P.coeffs zs
    (by show _ ≤ P.coeffs.length - 1 + 1; omega)
    (exists_mem_ne_zero_of_coeffAt _ _ (coeffAt_natDeg_ne_zero hP)) hNd ?_
  intro z hz
  rw [← eval_eq]
  exact hRoot z hz

private theorem filter_length_add_not {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter (fun a => !p a)).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := filter_length_add_not p l
    cases hpa : p a with
    | true =>
      rw [List.filter_cons_of_pos hpa,
        List.filter_cons_of_neg (by show ¬ (!p a) = true; rw [hpa]; decide)]
      show (l.filter p).length + 1 + _ = l.length + 1
      omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hpa]; decide),
        List.filter_cons_of_pos (by show (!p a) = true; rw [hpa]; rfl)]
      show _ + ((l.filter _).length + 1) = l.length + 1
      omega

/-- **`F`-Linear Persistence Contradiction (`[CWYZ26]` Claim 4.8, `c > B` case)**:
    If `(α₁, β₁, P₁) ≠ (α₂, β₂, P₂)` are degree-`≤ d` candidates and `(α₁, β₁, P₁)` is NOT
    `B`-persistent (`d + 1 ≤ B`), then they simultaneously agree with the fold on at most `B`
    distinct points of `D` (`0` Nullstellensatz, `0` algebraic closure). -/
theorem nonpersistent_common_agree_le
    (x : (F → F) × (F → F)) (D : List F) (d B : Nat) (hB : d + 1 ≤ B)
    (α₁ β₁ : F) (P₁ : UPoly F) (hP₁ : P₁.natDeg ≤ d)
    (α₂ β₂ : F) (P₂ : UPoly F) (hP₂ : P₂.natDeg ≤ d)
    (hne : (α₁, β₁, P₁) ≠ (α₂, β₂, P₂))
    (hNonpers : ¬ IsPersistent x D d B α₁ β₁ P₁)
    (zs : List F) (hzsNd : zs.Nodup) (hzsSub : ∀ z ∈ zs, z ∈ D)
    (hAg₁ : ∀ z ∈ zs, foldAgreePt x α₁ β₁ P₁ z = true)
    (hAg₂ : ∀ z ∈ zs, foldAgreePt x α₂ β₂ P₂ z = true) :
    zs.length ≤ B := by
  refine Decidable.byContradiction (fun hGt => ?_)
  have hLen : B + 1 ≤ zs.length := by omega
  let H := sub P₂ P₁
  have hHdeg : H.natDeg ≤ d := natDeg_sub_le_max P₂ P₁ d hP₂ hP₁
  have hPairNe : ¬ (α₁ = α₂ ∧ β₁ = β₂) := by
    rintro ⟨rfl, rfl⟩
    have hHne : H ≠ zero := fun h0 => hne (by
      have hEq : P₂ = P₁ := LawfulCommRing.sub_eq_zero_iff.mp h0
      rw [hEq])
    have hRoots : zs.length ≤ H.natDeg := uPoly_roots_le_natDeg H hHne zs hzsNd (fun z hz => by
      have e1 := of_decide_eq_true (hAg₁ z hz)
      have e2 := of_decide_eq_true (hAg₂ z hz)
      show (sub P₂ P₁).eval z = zero
      rw [eval_sub_eq, e1, e2, LawfulCommRing.sub_self])
    omega
  let L := line (sub α₂ α₁) (sub β₂ β₁)
  have hLne : L ≠ zero := line_ne_zero_of_ne (fun ⟨h1, h2⟩ => hPairNe
    ⟨(LawfulCommRing.sub_eq_zero_iff.mp h1).symm, (LawfulCommRing.sub_eq_zero_iff.mp h2).symm⟩)
  have hLdeg : L.natDeg ≤ 1 := natDeg_line_le _ _
  have hZeroL : (zs.filter (fun z => decide (L.eval z = zero))).length ≤ 1 := by
    have hle := uPoly_roots_le_natDeg L hLne _ (nodup_filter _ zs hzsNd)
      (fun z hz => of_decide_eq_true (List.mem_filter.mp hz).2)
    omega
  have hSplit := filter_length_add_not (fun z : F => decide (L.eval z = zero)) zs
  let zsGood := zs.filter (fun z => !decide (L.eval z = zero))
  have hGoodLen : B ≤ zsGood.length := by
    show B ≤ (zs.filter (fun z => !decide (L.eval z = zero))).length
    omega
  have hGoodNd : zsGood.Nodup := nodup_filter _ zs hzsNd
  let target := D.filter (fun z =>
    decide (L.eval z ≠ zero) && foldAgreePt x α₁ β₁ P₁ z &&
    decide (H.eval z = mul (x.2 z) (L.eval z)))
  have hSubTarget : ∀ z ∈ zsGood, z ∈ target := by
    intro z hz
    obtain ⟨hzZs, hLnzB⟩ := List.mem_filter.mp hz
    have hLnz : L.eval z ≠ zero := fun e => by
      rw [decide_eq_true e] at hLnzB; exact Bool.noConfusion hLnzB
    have e1 := of_decide_eq_true (hAg₁ z hzZs)
    have e2 := of_decide_eq_true (hAg₂ z hzZs)
    have hHL : H.eval z = mul (x.2 z) (L.eval z) := by
      show (sub P₂ P₁).eval z = mul (x.2 z) ((line (sub α₂ α₁) (sub β₂ β₁)).eval z)
      rw [eval_sub_eq, eval_line_eq, e1, e2]
      constructive_ring
    exact List.mem_filter.mpr ⟨hzsSub z hzZs, by
      simp only [Bool.and_eq_true]
      exact ⟨⟨decide_eq_true hLnz, hAg₁ z hzZs⟩, decide_eq_true hHL⟩⟩
  have hTargetLen : zsGood.length ≤ target.length :=
    nodup_length_le_of_subset hGoodNd hSubTarget
  exact hNonpers ⟨H, L, hLne, hLdeg, hHdeg, Nat.le_trans hGoodLen hTargetLen⟩

/-! ### `[CWYZ26]` Lemma 4.4: Challenges per Rational Explanation -/

/-- Rational fold `F_rat + (α + β X)·G_rat` in `RatFunc F = Frac (UPoly F)`. -/
def ratFold (F_rat G_rat : RatFunc F) (α β : F) : RatFunc F :=
  add F_rat (mul ((Frac.of (D := UPoly F)).toFun (line α β)) G_rat)

/-- `W ∈ RatFunc F` is a polynomial in `F[X]` of degree at most `d`. -/
def IsPolyDegLe (d : Nat) (W : RatFunc F) : Prop :=
  ∃ P : UPoly F, P.natDeg ≤ d ∧ W = (Frac.of (D := UPoly F)).toFun P

private theorem isPolyDegLe_sub {d : Nat} {W₁ W₂ : RatFunc F}
    (h₁ : IsPolyDegLe d W₁) (h₂ : IsPolyDegLe d W₂) : IsPolyDegLe d (sub W₁ W₂) := by
  obtain ⟨P₁, hd₁, rfl⟩ := h₁
  obtain ⟨P₂, hd₂, rfl⟩ := h₂
  exact ⟨sub P₁ P₂, natDeg_sub_le_max P₁ P₂ d hd₁ hd₂, (RingHom.map_sub _ P₁ P₂).symm⟩

private theorem natDeg_C_eq_zero (c : F) : (C c).natDeg = 0 :=
  Nat.le_zero.mp (natDeg_ofList_le [c])

private theorem isPolyDegLe_smul {d : Nat} (c : F) {W : RatFunc F}
    (h : IsPolyDegLe d W) :
    IsPolyDegLe d (mul ((Frac.of (D := UPoly F)).toFun (C c)) W) := by
  obtain ⟨P, hd, rfl⟩ := h
  refine ⟨mul (C c) P, ?_, (RingHom.map_mul _ (C c) P).symm⟩
  have h1 := (degFn_natDeg (R := F)).mul_le (C c) P
  rw [natDeg_C_eq_zero] at h1
  omega

private theorem frac_of_line_sub (F_rat G_rat : RatFunc F) (α₁ β₁ α₂ β₂ : F) :
    sub (ratFold F_rat G_rat α₁ β₁) (ratFold F_rat G_rat α₂ β₂) =
      mul ((Frac.of (D := UPoly F)).toFun (line (sub α₁ α₂) (sub β₁ β₂))) G_rat := by
  unfold ratFold
  have hL : sub (line α₁ β₁) (line α₂ β₂) = line (sub α₁ α₂) (sub β₁ β₂) := by
    apply UPoly.ext_coeffAt; intro k
    show coeffAt (sub (ofList [α₁, β₁]) (ofList [α₂, β₂])).coeffs k =
      coeffAt (ofList [sub α₁ α₂, sub β₁ β₂]).coeffs k
    rw [coeffAt_sub, coeffAt_ofList, coeffAt_ofList, coeffAt_ofList]
    cases k with
    | zero => simp only [coeffAt_cons_zero]
    | succ k => cases k with
      | zero => simp only [coeffAt_cons_zero, coeffAt_cons_succ]
      | succ k => simp only [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.sub_self]
  rw [← hL, RingHom.map_sub]
  constructive_ring

private theorem line_comb_basis (u₁ v₁ u₂ v₂ : F) (c₁ c₂ : F) :
    add (mul (C c₁) (line u₁ v₁)) (mul (C c₂) (line u₂ v₂)) =
      line (add (mul c₁ u₁) (mul c₂ u₂)) (add (mul c₁ v₁) (mul c₂ v₂)) := by
  apply UPoly.ext_coeffAt; intro k
  rw [coeffAt_add, coeffAt_C_mul, coeffAt_C_mul]
  show add (mul c₁ (coeffAt (ofList [u₁, v₁]).coeffs k))
      (mul c₂ (coeffAt (ofList [u₂, v₂]).coeffs k)) =
    coeffAt (ofList [add (mul c₁ u₁) (mul c₂ u₂), add (mul c₁ v₁) (mul c₂ v₂)]).coeffs k
  rw [coeffAt_ofList, coeffAt_ofList, coeffAt_ofList]
  cases k with
  | zero => simp only [coeffAt_cons_zero]
  | succ k => cases k with
    | zero => simp only [coeffAt_cons_zero, coeffAt_cons_succ]
    | succ k => simp only [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem coeffs_length_of_mul_X_deg_le (d : Nat) (G_u H_u : UPoly F)
    (hH : H_u.natDeg ≤ d) (hEq : mul X G_u = H_u) : G_u.coeffs.length ≤ d := by
  if hG0 : G_u = zero then
    rw [hG0, coeffs_zero]; exact Nat.zero_le d
  else
    have hPos : 1 ≤ G_u.coeffs.length := by
      cases hc : G_u.coeffs with
      | nil => exact absurd (UPoly.ext (hc.trans coeffs_zero.symm)) hG0
      | cons _ _ => exact Nat.succ_pos _
    have hLeadNe : coeffAt G_u.coeffs G_u.natDeg ≠ zero := coeffAt_natDeg_ne_zero hG0
    have hShift : coeffAt (mul X G_u).coeffs (G_u.natDeg + 1) = coeffAt G_u.coeffs G_u.natDeg :=
      coeffAt_X_mul_succ G_u G_u.natDeg
    rw [hEq] at hShift
    have hDegLt : ¬ H_u.natDeg < G_u.natDeg + 1 := fun hlt =>
      hLeadNe (hShift.symm.trans (coeffAt_eq_zero_of_natDeg_lt H_u hlt))
    have hNatDeg : G_u.natDeg = G_u.coeffs.length - 1 := rfl
    omega

private theorem find_some_mem_and_pred {α : Type} (p : α → Bool) :
    ∀ {l : List α} {x : α}, l.find? p = some x → x ∈ l ∧ p x = true
  | [], _, h => nomatch h
  | a :: tl, x, h => by
    unfold List.find? at h
    cases hpa : p a with
    | true =>
      rw [hpa] at h
      injection h with hEq
      subst hEq
      exact ⟨.head _, hpa⟩
    | false =>
      rw [hpa] at h
      obtain ⟨hm, hp⟩ := find_some_mem_and_pred p h
      exact ⟨.tail _ hm, hp⟩

/-- Constructive affine-subspace dichotomy for `[CWYZ26]` Lemma 4.4: either `(F_rat, G_rat)` comes
    from polynomials `(F_poly, G_poly)` with `deg F_poly ≤ d` and `deg G_poly ≤ d - 1`, or all
    challenges in `pairs` lie on a single affine line `a·α + b·β = c` in `F²`. -/
theorem rat_pair_collinear_or_polys (d : Nat) (F_rat G_rat : RatFunc F)
    (pairs : List (F × F))
    (hPoly : ∀ p ∈ pairs, IsPolyDegLe d (ratFold F_rat G_rat p.1 p.2)) :
    (∃ F_poly G_poly : List F, F_poly.length ≤ d + 1 ∧ G_poly.length ≤ d ∧
      F_rat = (Frac.of (D := UPoly F)).toFun (ofList F_poly) ∧
      G_rat = (Frac.of (D := UPoly F)).toFun (ofList G_poly)) ∨
    (∃ a b c : F, ¬ (a = zero ∧ b = zero) ∧
      ∀ p ∈ pairs, add (mul a p.1) (mul b p.2) = c) := by
  cases pairs with
  | nil =>
    exact .inr ⟨one, zero, zero, fun h => LawfulField.one_ne_zero h.1, fun _ hm => nomatch hm⟩
  | cons p₀ rest =>
    cases hFind1 : rest.find? (fun p => decide (p ≠ p₀)) with
    | none =>
      refine .inr ⟨one, zero, p₀.1, fun h => LawfulField.one_ne_zero h.1, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hrest
      · constructive_ring
      · have hall := List.find?_eq_none.mp hFind1 p hrest
        have hpEq : p = p₀ := Decidable.byContradiction (fun hne => hall (decide_eq_true hne))
        rw [hpEq]; constructive_ring
    | some p₁ =>
      obtain ⟨hp₁Rest, hp₁Pred⟩ := find_some_mem_and_pred _ hFind1
      have hp₁Mem : p₁ ∈ p₀ :: rest := .tail _ hp₁Rest
      have hp₁Ne : p₁ ≠ p₀ := of_decide_eq_true hp₁Pred
      let u₁ := sub p₁.1 p₀.1
      let v₁ := sub p₁.2 p₀.2
      have huv₁Ne : ¬ (u₁ = zero ∧ v₁ = zero) := fun ⟨h1, h2⟩ => hp₁Ne (Prod.ext
        (LawfulCommRing.sub_eq_zero_iff.mp h1) (LawfulCommRing.sub_eq_zero_iff.mp h2))
      cases hFind2 : (p₀ :: rest).find? (fun p =>
          decide (sub (mul u₁ (sub p.2 p₀.2)) (mul v₁ (sub p.1 p₀.1)) ≠ zero)) with
      | none =>
        refine .inr ⟨v₁, neg u₁, sub (mul v₁ p₀.1) (mul u₁ p₀.2), ?_, ?_⟩
        · rintro ⟨hv0, hnu0⟩
          have hu0 : u₁ = zero := by
            have h := congrArg neg hnu0
            have hn : neg (neg u₁) = u₁ := by constructive_ring
            have hz : neg (zero : F) = zero := by constructive_ring
            rw [hn, hz] at h; exact h
          exact huv₁Ne ⟨hu0, hv0⟩
        · intro p hp
          have hall := List.find?_eq_none.mp hFind2 p hp
          have hdet0 : sub (mul u₁ (sub p.2 p₀.2)) (mul v₁ (sub p.1 p₀.1)) = zero :=
            Decidable.byContradiction (fun hne => hall (decide_eq_true hne))
          have hrel := LawfulCommRing.sub_eq_zero_iff.mp hdet0
          calc add (mul v₁ p.1) (mul (neg u₁) p.2)
              = add (sub (mul v₁ p₀.1) (mul u₁ p₀.2))
                  (sub (mul v₁ (sub p.1 p₀.1)) (mul u₁ (sub p.2 p₀.2))) := by constructive_ring
            _ = add (sub (mul v₁ p₀.1) (mul u₁ p₀.2)) zero := by
                  rw [hrel, LawfulCommRing.sub_self]
            _ = sub (mul v₁ p₀.1) (mul u₁ p₀.2) := LawfulCommRing.add_zero _
      | some p₂ =>
        left
        obtain ⟨hp₂Mem, hp₂Pred⟩ := find_some_mem_and_pred _ hFind2
        let u₂ := sub p₂.1 p₀.1
        let v₂ := sub p₂.2 p₀.2
        let det := sub (mul u₁ v₂) (mul v₁ u₂)
        have hdetNe : det ≠ zero := of_decide_eq_true hp₂Pred
        let invD := LawfulField.inv det
        have hW₀ := hPoly p₀ (.head _)
        have hD₁ : IsPolyDegLe d (mul ((Frac.of (D := UPoly F)).toFun (line u₁ v₁)) G_rat) := by
          rw [← frac_of_line_sub F_rat G_rat p₁.1 p₁.2 p₀.1 p₀.2]
          exact isPolyDegLe_sub (hPoly p₁ hp₁Mem) hW₀
        have hD₂ : IsPolyDegLe d (mul ((Frac.of (D := UPoly F)).toFun (line u₂ v₂)) G_rat) := by
          rw [← frac_of_line_sub F_rat G_rat p₂.1 p₂.2 p₀.1 p₀.2]
          exact isPolyDegLe_sub (hPoly p₂ hp₂Mem) hW₀
        have hSpan : ∀ c₁ c₂ : F, IsPolyDegLe d
            (mul ((Frac.of (D := UPoly F)).toFun
              (line (add (mul c₁ u₁) (mul c₂ u₂)) (add (mul c₁ v₁) (mul c₂ v₂)))) G_rat) := by
          intro c₁ c₂
          rw [← line_comb_basis, RingHom.map_add, RingHom.map_mul, RingHom.map_mul]
          have heq : mul (add (mul ((Frac.of (D := UPoly F)).toFun (C c₁))
                ((Frac.of (D := UPoly F)).toFun (line u₁ v₁)))
              (mul ((Frac.of (D := UPoly F)).toFun (C c₂))
                ((Frac.of (D := UPoly F)).toFun (line u₂ v₂)))) G_rat =
              sub (mul ((Frac.of (D := UPoly F)).toFun (C c₁))
                (mul ((Frac.of (D := UPoly F)).toFun (line u₁ v₁)) G_rat))
              (mul ((Frac.of (D := UPoly F)).toFun (C (neg c₂)))
                (mul ((Frac.of (D := UPoly F)).toFun (line u₂ v₂)) G_rat)) := by
            have hnegC : (Frac.of (D := UPoly F)).toFun (C (neg c₂)) =
                neg ((Frac.of (D := UPoly F)).toFun (C c₂)) := by
              have hc : (C (neg c₂) : UPoly F) = neg (C c₂) := by simpa only [CHom_apply] using (CHom (R := F)).map_neg c₂
              rw [hc, RingHom.map_neg]
            rw [hnegC]; constructive_ring
          rw [heq]
          exact isPolyDegLe_sub (isPolyDegLe_smul c₁ hD₁) (isPolyDegLe_smul (neg c₂) hD₂)
        have h10 := hSpan (mul v₂ invD) (neg (mul v₁ invD))
        have e10a : add (mul (mul v₂ invD) u₁) (mul (neg (mul v₁ invD)) u₂) = one := by
          have : add (mul (mul v₂ invD) u₁) (mul (neg (mul v₁ invD)) u₂) = mul det invD := by
            dsimp [det]; constructive_ring
          rw [this, LawfulField.mul_inv_cancel hdetNe]
        have e10b : add (mul (mul v₂ invD) v₁) (mul (neg (mul v₁ invD)) v₂) = zero := by
          constructive_ring
        rw [e10a, e10b] at h10
        have hLine10 : line (one : F) zero = one := line_one_zero
        rw [hLine10, RingHom.map_one, LawfulCommRing.one_mul] at h10
        have h01 := hSpan (neg (mul u₂ invD)) (mul u₁ invD)
        have e01a : add (mul (neg (mul u₂ invD)) u₁) (mul (mul u₁ invD) u₂) = zero := by
          constructive_ring
        have e01b : add (mul (neg (mul u₂ invD)) v₁) (mul (mul u₁ invD) v₂) = one := by
          have : add (mul (neg (mul u₂ invD)) v₁) (mul (mul u₁ invD) v₂) = mul det invD := by
            dsimp [det]; constructive_ring
          rw [this, LawfulField.mul_inv_cancel hdetNe]
        rw [e01a, e01b] at h01
        have hLine01 : line (zero : F) one = X := rfl
        rw [hLine01] at h01
        obtain ⟨G_u, hGuDeg, hGuEq⟩ := h10
        obtain ⟨H_u, hHuDeg, hHuEq⟩ := h01
        have hXG : mul X G_u = H_u := Frac.of_injective (by
          rw [RingHom.map_mul, ← hGuEq, ← hHuEq])
        have hGuLen : G_u.coeffs.length ≤ d := coeffs_length_of_mul_X_deg_le d G_u H_u hHuDeg hXG
        have hBase : IsPolyDegLe d F_rat := by
          obtain ⟨P₀, hP₀Deg, hP₀Eq⟩ := hW₀
          refine ⟨sub P₀ (mul (line p₀.1 p₀.2) G_u), ?_, ?_⟩
          · refine natDeg_sub_le_max P₀ _ d hP₀Deg ?_
            have hlin : mul (line p₀.1 p₀.2) G_u =
                add (mul (C p₀.1) G_u) (mul (C p₀.2) H_u) := by
              rw [← hXG]
              have hl : line p₀.1 p₀.2 = add (C p₀.1) (mul X (C p₀.2)) := ofList_cons p₀.1 [p₀.2]
              rw [hl]; constructive_ring
            rw [hlin]
            have ha := (degFn_natDeg (R := F)).add_le (mul (C p₀.1) G_u) (mul (C p₀.2) H_u)
            have hm1 := (degFn_natDeg (R := F)).mul_le (C p₀.1) G_u
            have hm2 := (degFn_natDeg (R := F)).mul_le (C p₀.2) H_u
            rw [natDeg_C_eq_zero] at hm1 hm2
            omega
          · rw [RingHom.map_sub, RingHom.map_mul, ← hGuEq, ← hP₀Eq]
            unfold ratFold; constructive_ring
        obtain ⟨F_u, hFuDeg, hFuEq⟩ := hBase
        have hFuLen : F_u.coeffs.length ≤ d + 1 := by
          cases hc : F_u.coeffs with
          | nil => exact Nat.zero_le _
          | cons _ tl =>
            have : F_u.natDeg = (tl.length + 1) - 1 := by show F_u.coeffs.length - 1 = _; rw [hc]; rfl
            show tl.length + 1 ≤ d + 1; omega
        have hOfList : ∀ U : UPoly F, ofList U.coeffs = U := fun U => UPoly.ofList_coeffs U
        exact ⟨F_u.coeffs, G_u.coeffs, hFuLen, hGuLen,
          by rw [hOfList]; exact hFuEq, by rw [hOfList]; exact hGuEq⟩

private theorem collinear_pairs_le_pool (S : List F) (_hS : S.Nodup)
    (pairs : List (F × F)) (hNd : pairs.Nodup) (hPool : ∀ p ∈ pairs, p ∈ prodPool S)
    (a b c : F) (hab : ¬ (a = zero ∧ b = zero))
    (hLine : ∀ p ∈ pairs, add (mul a p.1) (mul b p.2) = c) :
    pairs.length ≤ S.length := by
  if ha : a = zero then
    have hb : b ≠ zero := fun hb0 => hab ⟨ha, hb0⟩
    have hMapNd : (pairs.map Prod.fst).Nodup := List.pairwise_map.mpr
      (List.Pairwise.imp_of_mem (fun {p q} hp hq hne hfst => hne (Prod.ext hfst (by
        have e1 := hLine p hp
        have e2 := hLine q hq
        rw [ha, LawfulCommRing.zero_mul, LawfulCommRing.zero_add] at e1 e2
        have hmul := congrArg (mul (LawfulField.inv b)) (e1.trans e2.symm)
        rw [← LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel hb, LawfulCommRing.one_mul,
          ← LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel hb, LawfulCommRing.one_mul] at hmul
        exact hmul))) hNd)
    have hSub : ∀ u ∈ pairs.map Prod.fst, u ∈ S := by
      intro u hu
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      exact (mem_prodPool_iff.mp (hPool p hp)).1
    have hle := nodup_length_le_of_subset hMapNd hSub
    rwa [List.length_map] at hle
  else
    have hMapNd : (pairs.map Prod.snd).Nodup := List.pairwise_map.mpr
      (List.Pairwise.imp_of_mem (fun {p q} hp hq hne hsnd => hne (Prod.ext (by
        have e1 := hLine p hp
        have e2 := hLine q hq
        rw [hsnd] at e1
        have hsub : mul a p.1 = mul a q.1 := by
          have h3 : add (mul b q.2) (mul a p.1) = add (mul b q.2) (mul a q.1) := by
            rw [LawfulCommRing.add_comm (mul b q.2), e1, LawfulCommRing.add_comm (mul b q.2), e2]
          exact LawfulCommRing.add_left_cancel h3
        have hmul := congrArg (mul (LawfulField.inv a)) hsub
        rw [← LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel ha, LawfulCommRing.one_mul,
          ← LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel ha, LawfulCommRing.one_mul] at hmul
        exact hmul) hsnd)) hNd)
    have hSub : ∀ v ∈ pairs.map Prod.snd, v ∈ S := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      exact (mem_prodPool_iff.mp (hPool p hp)).2
    have hle := nodup_length_le_of_subset hMapNd hSub
    rwa [List.length_map] at hle

/-- A polynomial explanation of this particular candidate, with correlated agreement.
Unlike a global correlated-agreement premise this retains the accepted polynomial. -/
@[expose] def HasPolynomialExplanation (x : (F → F) × (F → F)) (D : List F)
    (d B : Nat) (α β : F) (P : UPoly F) : Prop :=
  ∃ F_poly G_poly : List F,
    F_poly.length ≤ d + 1 ∧ G_poly.length ≤ d ∧
    B ≤ (D.filter (fun z => decide (evalCoeffs F_poly z = x.1 z) &&
      decide (evalCoeffs G_poly z = x.2 z))).length ∧
    add (ofList F_poly) (mul (line α β) (ofList G_poly)) = P

/-- **`[CWYZ26]` Lemma 4.4 (`persistent_challenges_per_witness_le`)**:
    For any fixed rational pair `(F_rat, G_rat) ∈ F(X)²`, at most `max(|S|, |D|(|D| - 1)/2)` challenges `(α, β) ∈ S × S` yield a degree-`≤ d`
    polynomial `P = F_rat + (α + β X) G_rat` agreeing with the fold on `≥ A` points of `D`
    and lacking a polynomial explanation with correlated agreement `≥ A - 1`. -/
theorem exceptional_persistent_challenges_per_witness_le
    (x : (F → F) × (F → F)) (D S : List F) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup)
    (F_rat G_rat : RatFunc F)
    (pairs : List (F × F)) (hNd : pairs.Nodup) (hPool : ∀ p ∈ pairs, p ∈ prodPool S)
    (hEx : ∀ p ∈ pairs, ∃ P : UPoly F, P.natDeg ≤ d ∧
      A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
      ratFold F_rat G_rat p.1 p.2 = (Frac.of (D := UPoly F)).toFun P ∧
      ¬ HasPolynomialExplanation x D d (A - 1) p.1 p.2 P) :
    pairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2) := by
  have hPoly : ∀ p ∈ pairs, IsPolyDegLe d (ratFold F_rat G_rat p.1 p.2) := by
    intro p hp
    obtain ⟨P, hdeg, _, heq, _⟩ := hEx p hp
    exact ⟨P, hdeg, heq⟩
  rcases rat_pair_collinear_or_polys d F_rat G_rat pairs hPoly with
    ⟨F_poly, G_poly, hFlen, hGlen, hFeq, hGeq⟩ | ⟨a, b, c, hab, hLine⟩
  · refine Nat.le_trans ?_ (Nat.le_max_right S.length _)
    have hSub : ∀ p ∈ pairs, p ∈ (prodPool S).filter (fun p =>
        decide (2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly x.1 x.2 p.1 p.2)).length)) := by
      intro p hp
      refine List.mem_filter.mpr ⟨hPool p hp, decide_eq_true ?_⟩
      obtain ⟨P, _, hAgLen, hPeq, hNoExplanation⟩ := hEx p hp
      rw [hFeq, hGeq] at hPeq
      unfold ratFold at hPeq
      rw [← RingHom.map_mul, ← RingHom.map_add] at hPeq
      have hPolyEq : add (ofList F_poly) (mul (line p.1 p.2) (ofList G_poly)) = P :=
        Frac.of_injective hPeq
      have hCAle : (D.filter (fun z =>
          decide (evalCoeffs F_poly z = x.1 z) &&
          decide (evalCoeffs G_poly z = x.2 z))).length < A - 1 :=
        Decidable.byContradiction (fun hge =>
          hNoExplanation ⟨F_poly, G_poly, hFlen, hGlen, by omega, hPolyEq⟩)
      have hTot := JohnsonBound.filter_length_le_add
        (foldAgreePt x p.1 p.2 P)
        (fun z => decide (evalCoeffs F_poly z = x.1 z) && decide (evalCoeffs G_poly z = x.2 z))
        (isAccidentalAgreement F_poly G_poly x.1 x.2 p.1 p.2) D
        (fun z _ hf => by
          cases hc1 : (decide (evalCoeffs F_poly z = x.1 z) &&
              decide (evalCoeffs G_poly z = x.2 z)) with
          | true => exact .inl rfl
          | false =>
            have hPval : P.eval z = add (evalCoeffs F_poly z)
                (mul (add p.1 (mul p.2 z)) (evalCoeffs G_poly z)) := by
              rw [← hPolyEq]
              rw [← evalHom_apply]
              show (evalHom z).toFun (add (ofList F_poly) (mul (line p.1 p.2) (ofList G_poly))) = _
              rw [RingHom.map_add, RingHom.map_mul, evalHom_apply, evalHom_apply, evalHom_apply,
                eval_ofList, eval_ofList, eval_line_eq]
            have hag := of_decide_eq_true hf
            rw [hPval] at hag
            refine .inr ?_
            unfold isAccidentalAgreement
            simp only [Bool.and_eq_true]
            exact ⟨decide_eq_true hag, by rw [hc1]; rfl⟩)
      have hApos : 2 ≤ A := Decidable.byContradiction (fun hlt => by
        have hA1 : A - 1 = 0 := by omega
        rw [hA1] at hCAle; omega)
      omega
    exact Nat.le_trans (nodup_length_le_of_subset hNd hSub)
      (committed_polynomial_pair_bad_lines_le_choose2 F_poly G_poly x.1 x.2 D S hD hS)
  · exact Nat.le_trans (collinear_pairs_le_pool S hS pairs hNd hPool a b c hab hLine)
      (Nat.le_max_left S.length _)

/-- Global lack of correlated agreement implies the candidate-specific exceptional bound. -/
theorem persistent_challenges_per_witness_le
    (x : (F → F) × (F → F)) (D S : List F) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup)
    (hFar : ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D)
    (F_rat G_rat : RatFunc F)
    (pairs : List (F × F)) (hNd : pairs.Nodup) (hPool : ∀ p ∈ pairs, p ∈ prodPool S)
    (hEx : ∀ p ∈ pairs, ∃ P : UPoly F, P.natDeg ≤ d ∧
      A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
      ratFold F_rat G_rat p.1 p.2 = (Frac.of (D := UPoly F)).toFun P) :
    pairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2) := by
  apply exceptional_persistent_challenges_per_witness_le x D S d A hD hS
    F_rat G_rat pairs hNd hPool
  intro p hp
  obtain ⟨P, hd, ha, hr⟩ := hEx p hp
  refine ⟨P, hd, ha, hr, ?_⟩
  rintro ⟨Fp, Gp, hF, hG, hAgree, _⟩
  exact hFar ⟨Fp, Gp, hF, hG, hAgree⟩

/-! ### `[CWYZ26]` Lemma 4.5: Total Persistent Challenge Bound via Johnson Set System -/

private def persValid (x : (F → F) × (F → F)) (D : List F) (d A B : Nat)
    (p : F × F) (P H L : UPoly F) : Prop :=
  P.natDeg ≤ d ∧
  A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
  L ≠ zero ∧ L.natDeg ≤ 1 ∧ H.natDeg ≤ d ∧
  B ≤ (D.filter (fun z =>
    decide (L.eval z ≠ zero) &&
    foldAgreePt x p.1 p.2 P z &&
    decide (H.eval z = mul (x.2 z) (L.eval z)))).length

private def persRatPair (α β : F) (P H L : UPoly F) : RatFunc F × RatFunc F :=
  let G_rat := mul ((Frac.of (D := UPoly F)).toFun H)
    (LawfulField.inv ((Frac.of (D := UPoly F)).toFun L))
  (sub ((Frac.of (D := UPoly F)).toFun P)
    (mul ((Frac.of (D := UPoly F)).toFun (line α β)) G_rat), G_rat)

/-- Retain an explicit rational explanation, including its denominator, agreement set,
and identity for the selected polynomial. This witness does not identify other accepted
polynomials at the same challenge. -/
theorem IsPersistent.rational_explanation (x : (F → F) × (F → F)) (D : List F)
    (d B : Nat) (α β : F) (P : UPoly F) (h : IsPersistent x D d B α β P) :
    ∃ (H L : UPoly F) (F_rat G_rat : RatFunc F),
      L ≠ zero ∧ L.natDeg ≤ 1 ∧ H.natDeg ≤ d ∧
      B ≤ (D.filter (fun z => decide (L.eval z ≠ zero) && foldAgreePt x α β P z &&
        decide (H.eval z = mul (x.2 z) (L.eval z)))).length ∧
      G_rat = mul ((Frac.of (D := UPoly F)).toFun H)
        (LawfulField.inv ((Frac.of (D := UPoly F)).toFun L)) ∧
      F_rat = sub ((Frac.of (D := UPoly F)).toFun P)
        (mul ((Frac.of (D := UPoly F)).toFun (line α β)) G_rat) ∧
      ratFold F_rat G_rat α β = (Frac.of (D := UPoly F)).toFun P := by
  obtain ⟨H, L, hL, hLd, hHd, hAgree⟩ := h
  refine ⟨H, L, (persRatPair α β P H L).1, (persRatPair α β P H L).2,
    hL, hLd, hHd, hAgree, rfl, rfl, ?_⟩
  dsimp [persRatPair, ratFold]
  constructive_ring

/-- **`[CWYZ26]` Lemma 4.5 (`persistent_pairs_card_le`)**:
    For selected candidates without polynomial explanations, under the Johnson condition
    `D.length * (d + 1) < B * B`, at most
    `((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) * max(|S|, |D|(|D| - 1)/2)`
    challenges `(α, β) ∈ S × S` admit a `B`-persistent degree-`≤ d` candidate with `≥ A`
    agreements on `D`. -/
theorem exceptional_persistent_pairs_card_le
    (x : (F → F) × (F → F)) (D S : List F) (d A B : Nat)
    (hD : D.Nodup) (hS : S.Nodup)
    (hDen : D.length * (d + 1) < B * B)
    (L : List (F × F)) (hNd : L.Nodup) (hPool : ∀ p ∈ L, p ∈ prodPool S)
    (hPers : ∀ p ∈ L, ∃ P : UPoly F, P.natDeg ≤ d ∧
      A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
      IsPersistent x D d B p.1 p.2 P ∧
      ¬ HasPolynomialExplanation x D d (A - 1) p.1 p.2 P) :
    L.length ≤ ((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
      Nat.max S.length (D.length * (D.length - 1) / 2) := by
  have hEx : ∀ p ∈ L, ∃ w : UPoly F × UPoly F × UPoly F,
      persValid x D d A B p w.1 w.2.1 w.2.2 ∧
        ¬ HasPolynomialExplanation x D d (A - 1) p.1 p.2 w.1 := by
    intro p hp
    obtain ⟨P, hPdeg, hPAg, ⟨H, Ld, hLne, hLdeg, hHdeg, hBLen⟩, hNoExplanation⟩ := hPers p hp
    exact ⟨(P, H, Ld), ⟨hPdeg, hPAg, hLne, hLdeg, hHdeg, hBLen⟩, hNoExplanation⟩
  obtain ⟨wf, hwf⟩ := list_finite_choice _ (zero, zero, zero) L hEx
  let rpOf : F × F → RatFunc F × RatFunc F := fun p =>
    persRatPair p.1 p.2 (wf p).1 (wf p).2.1 (wf p).2.2
  let fam := JohnsonBound.dedupFirst (L.map rpOf)
  have hFamNd : fam.Nodup := JohnsonBound.dedupFirst_nodup _
  have hRepEx : ∀ rp ∈ fam, ∃ p : F × F, p ∈ L ∧ rpOf p = rp := by
    intro rp hrp
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((JohnsonBound.mem_dedupFirst_iff rp _).mp hrp)
    exact ⟨p, hp, rfl⟩
  obtain ⟨rep, hrep⟩ := list_finite_choice _ (zero, zero) fam hRepEx
  let memSet : (RatFunc F × RatFunc F) → F → Bool := fun rp z =>
    let p := rep rp; let w := wf p
    decide (w.2.2.eval z ≠ zero) && foldAgreePt x p.1 p.2 w.1 z &&
    decide (w.2.1.eval z = mul (x.2 z) (w.2.2.eval z))
  have hSize : ∀ rp ∈ fam, B ≤ (D.filter (fun z => memSet rp z)).length :=
    fun rp hrp => (hwf (rep rp) (hrep rp hrp).1).1.2.2.2.2.2
  have hInter : fam.Pairwise (fun rp₀ rp₁ =>
      (D.filter (fun z => memSet rp₀ z && memSet rp₁ z)).length ≤ d + 1) := by
    refine JohnsonBound.pairwise_of_nodup hFamNd (fun rp₀ hrp₀ rp₁ hrp₁ hne => ?_)
    let p₀ := rep rp₀; let p₁ := rep rp₁
    obtain ⟨hP₀d, _, hL₀ne, hL₀d, hH₀d, _⟩ := (hwf p₀ (hrep rp₀ hrp₀).1).1
    obtain ⟨hP₁d, _, hL₁ne, hL₁d, hH₁d, _⟩ := (hwf p₁ (hrep rp₁ hrp₁).1).1
    let P₀ := (wf p₀).1; let H₀ := (wf p₀).2.1; let L₀ := (wf p₀).2.2
    let P₁ := (wf p₁).1; let H₁ := (wf p₁).2.1; let L₁ := (wf p₁).2.2
    have hL₀F : (Frac.of (D := UPoly F)).toFun L₀ ≠ zero := fun e =>
      hL₀ne (Frac.of_injective (e.trans (RingHom.map_zero _).symm))
    have hL₁F : (Frac.of (D := UPoly F)).toFun L₁ ≠ zero := fun e =>
      hL₁ne (Frac.of_injective (e.trans (RingHom.map_zero _).symm))
    if hGeq : (rpOf p₀).2 = (rpOf p₁).2 then
      have hFeqNe : (rpOf p₀).1 ≠ (rpOf p₁).1 := fun hFeq =>
        hne ((hrep rp₀ hrp₀).2.symm.trans ((Prod.ext hFeq hGeq).trans (hrep rp₁ hrp₁).2))
      let CrossF := sub (mul (sub P₀ P₁) L₀) (mul (sub (line p₀.1 p₀.2) (line p₁.1 p₁.2)) H₀)
      have hCFne : CrossF ≠ zero := fun h0 => hFeqNe (by
        have hm := congrArg (Frac.of (D := UPoly F)).toFun h0
        rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_mul,
          RingHom.map_sub, RingHom.map_zero] at hm
        have hsub0 := LawfulCommRing.sub_eq_zero_iff.mp hm
        have hinv := LawfulField.mul_inv_cancel hL₀F
        dsimp [rpOf, persRatPair] at hGeq ⊢
        rw [← hGeq]
        apply LawfulCommRing.sub_eq_zero_iff.mp
        apply mul_right_cancel' hL₀F
        rw [LawfulCommRing.zero_mul]
        have hId : mul (sub
            (sub ((Frac.of (D := UPoly F)).toFun P₀)
              (mul ((Frac.of (D := UPoly F)).toFun (line p₀.1 p₀.2))
                (mul ((Frac.of (D := UPoly F)).toFun H₀)
                  (LawfulField.inv ((Frac.of (D := UPoly F)).toFun L₀)))))
            (sub ((Frac.of (D := UPoly F)).toFun P₁)
              (mul ((Frac.of (D := UPoly F)).toFun (line p₁.1 p₁.2))
                (mul ((Frac.of (D := UPoly F)).toFun H₀)
                  (LawfulField.inv ((Frac.of (D := UPoly F)).toFun L₀))))))
            ((Frac.of (D := UPoly F)).toFun L₀) =
          sub (mul (sub ((Frac.of (D := UPoly F)).toFun P₀) ((Frac.of (D := UPoly F)).toFun P₁))
              ((Frac.of (D := UPoly F)).toFun L₀))
            (mul (mul (sub ((Frac.of (D := UPoly F)).toFun (line p₀.1 p₀.2))
                ((Frac.of (D := UPoly F)).toFun (line p₁.1 p₁.2)))
              ((Frac.of (D := UPoly F)).toFun H₀))
              (mul ((Frac.of (D := UPoly F)).toFun L₀)
                (LawfulField.inv ((Frac.of (D := UPoly F)).toFun L₀)))) := by constructive_ring
        rw [hId, hinv, LawfulCommRing.mul_one, hsub0, LawfulCommRing.sub_self])
      have hCFdeg : CrossF.natDeg ≤ d + 1 := by
        refine natDeg_sub_le_max _ _ (d + 1) ?_ ?_
        · have hm := (degFn_natDeg (R := F)).mul_le (sub P₀ P₁) L₀
          have hs := natDeg_sub_le_max P₀ P₁ d hP₀d hP₁d
          dsimp only [P₀, P₁, L₀] at hm hs ⊢; omega
        · have hm := (degFn_natDeg (R := F)).mul_le (sub (line p₀.1 p₀.2) (line p₁.1 p₁.2)) H₀
          have hs := natDeg_sub_le_max _ _ 1 (natDeg_line_le p₀.1 p₀.2) (natDeg_line_le p₁.1 p₁.2)
          dsimp only [H₀] at hm ⊢; omega
      refine Nat.le_trans (uPoly_roots_le_natDeg CrossF hCFne _ (nodup_filter _ D hD) ?_) hCFdeg
      intro z hz
      obtain ⟨hm₀, hm₁⟩ := Bool.and_eq_true_iff.mp (List.mem_filter.mp hz).2
      obtain ⟨hm₀a, hHL₀⟩ := Bool.and_eq_true_iff.mp hm₀
      obtain ⟨_, hag₀⟩ := Bool.and_eq_true_iff.mp hm₀a
      obtain ⟨hm₁a, _⟩ := Bool.and_eq_true_iff.mp hm₁
      obtain ⟨_, hag₁⟩ := Bool.and_eq_true_iff.mp hm₁a
      show (sub (mul (sub P₀ P₁) L₀) (mul (sub (line p₀.1 p₀.2) (line p₁.1 p₁.2)) H₀)).eval z = zero
      rw [eval_sub_eq, eval_mul_eq, eval_sub_eq, eval_mul_eq, eval_sub_eq,
        eval_line_eq, eval_line_eq, of_decide_eq_true hag₀, of_decide_eq_true hag₁,
        of_decide_eq_true hHL₀]
      constructive_ring
    else
      let CrossG := sub (mul H₀ L₁) (mul H₁ L₀)
      have hCGne : CrossG ≠ zero := fun h0 => hGeq (by
        have hm := congrArg (Frac.of (D := UPoly F)).toFun h0
        rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_zero] at hm
        have hsub0 := LawfulCommRing.sub_eq_zero_iff.mp hm
        have hinv₀ := LawfulField.mul_inv_cancel hL₀F
        have hinv₁ := LawfulField.mul_inv_cancel hL₁F
        dsimp [rpOf, persRatPair]
        apply LawfulCommRing.sub_eq_zero_iff.mp
        apply mul_right_cancel' (mul_ne_zero' hL₀F hL₁F)
        rw [LawfulCommRing.zero_mul]
        have hId : mul (sub
            (mul ((Frac.of (D := UPoly F)).toFun H₀)
              (LawfulField.inv ((Frac.of (D := UPoly F)).toFun L₀)))
            (mul ((Frac.of (D := UPoly F)).toFun H₁)
              (LawfulField.inv ((Frac.of (D := UPoly F)).toFun L₁))))
            (mul ((Frac.of (D := UPoly F)).toFun L₀) ((Frac.of (D := UPoly F)).toFun L₁)) =
          sub (mul (mul ((Frac.of (D := UPoly F)).toFun H₀) ((Frac.of (D := UPoly F)).toFun L₁))
              (mul ((Frac.of (D := UPoly F)).toFun L₀)
                (LawfulField.inv ((Frac.of (D := UPoly F)).toFun L₀))))
            (mul (mul ((Frac.of (D := UPoly F)).toFun H₁) ((Frac.of (D := UPoly F)).toFun L₀))
              (mul ((Frac.of (D := UPoly F)).toFun L₁)
                (LawfulField.inv ((Frac.of (D := UPoly F)).toFun L₁)))) := by constructive_ring
        rw [hId, hinv₀, hinv₁, LawfulCommRing.mul_one, LawfulCommRing.mul_one,
          hsub0, LawfulCommRing.sub_self])
      have hCGdeg : CrossG.natDeg ≤ d + 1 := by
        refine natDeg_sub_le_max _ _ (d + 1) ?_ ?_
        · have hm := (degFn_natDeg (R := F)).mul_le H₀ L₁
          dsimp only [H₀, L₁] at hm ⊢; omega
        · have hm := (degFn_natDeg (R := F)).mul_le H₁ L₀
          dsimp only [H₁, L₀] at hm ⊢; omega
      refine Nat.le_trans (uPoly_roots_le_natDeg CrossG hCGne _ (nodup_filter _ D hD) ?_) hCGdeg
      intro z hz
      obtain ⟨hm₀, hm₁⟩ := Bool.and_eq_true_iff.mp (List.mem_filter.mp hz).2
      obtain ⟨_, hHL₀⟩ := Bool.and_eq_true_iff.mp hm₀
      obtain ⟨_, hHL₁⟩ := Bool.and_eq_true_iff.mp hm₁
      show (sub (mul H₀ L₁) (mul H₁ L₀)).eval z = zero
      rw [eval_sub_eq, eval_mul_eq, eval_mul_eq, of_decide_eq_true hHL₀, of_decide_eq_true hHL₁]
      constructive_ring
  have hFamLen : fam.length ≤ (D.length * (B - (d + 1))) / (B * B - D.length * (d + 1)) :=
    by simpa only [JohnsonBound.johnsonBound_eq] using JohnsonBound.johnson_set_system_card_le D fam memSet B (d + 1) hD hSize hInter hDen
  have hFib : ∀ rp ∈ fam,
      (L.filter (fun p => decide (rpOf p = rp))).length ≤
        Nat.max S.length (D.length * (D.length - 1) / 2) := by
    intro rp _
    refine exceptional_persistent_challenges_per_witness_le x D S d A hD hS rp.1 rp.2
      (L.filter (fun p => decide (rpOf p = rp))) (nodup_filter _ L hNd)
      (fun p hp => hPool p (List.mem_filter.mp hp).1) (fun p hp => ?_)
    obtain ⟨hpL, hrpEqB⟩ := List.mem_filter.mp hp
    have hval := hwf p hpL
    refine ⟨(wf p).1, hval.1.1, hval.1.2.1, ?_, hval.2⟩
    rw [← of_decide_eq_true hrpEqB]
    dsimp [rpOf, persRatPair, ratFold]
    constructive_ring
  have hCov : ∀ p ∈ L, rpOf p ∈ fam := fun p hp =>
    (JohnsonBound.mem_dedupFirst_iff (rpOf p) _).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact Nat.le_trans (JohnsonBound.count_partition_le rpOf _ L fam hCov hFib)
    (Nat.mul_le_mul_right _ hFamLen)

/-- The original far-word bound is a corollary of the candidate-specific result. -/
theorem persistent_pairs_card_le
    (x : (F → F) × (F → F)) (D S : List F) (d A B : Nat)
    (hD : D.Nodup) (hS : S.Nodup)
    (hDen : D.length * (d + 1) < B * B)
    (hFar : ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D)
    (L : List (F × F)) (hNd : L.Nodup) (hPool : ∀ p ∈ L, p ∈ prodPool S)
    (hPers : ∀ p ∈ L, ∃ P : UPoly F, P.natDeg ≤ d ∧
      A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
      IsPersistent x D d B p.1 p.2 P) :
    L.length ≤ ((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
      Nat.max S.length (D.length * (D.length - 1) / 2) := by
  apply exceptional_persistent_pairs_card_le x D S d A B hD hS hDen L hNd hPool
  intro p hp
  obtain ⟨P, hd, ha, hpers⟩ := hPers p hp
  refine ⟨P, hd, ha, hpers, ?_⟩
  rintro ⟨Fp, Gp, hF, hG, hAgree, _⟩
  exact hFar ⟨Fp, Gp, hF, hG, hAgree⟩

end Persistent

#verify_constructive nonpersistent_common_agree_le rat_pair_collinear_or_polys IsPersistent.rational_explanation
#verify_constructive exceptional_persistent_challenges_per_witness_le exceptional_persistent_pairs_card_le
#verify_constructive persistent_challenges_per_witness_le persistent_pairs_card_le

end Qsag

end

section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace NonpersistentIncidence

/-- Incidence double counting with the coordinates common to every candidate removed.
The pairwise hypothesis is used only to bound those common coordinates. -/
theorem incidence_mul_le {Point Coord : Type} [DecidableEq Coord]
    (pts : List Point) (D : List Coord) (agree : Point → Coord → Bool)
    (A B K : Nat) (hD : D.Nodup) (hnd : pts.Nodup) (htwo : 2 ≤ pts.length)
    (hsize : ∀ p ∈ pts, A ≤ (D.filter (agree p)).length)
    (hshared : ∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
      (D.filter (fun z => agree p z && agree q z)).length ≤ B)
    (hfiber : ∀ z ∈ D, ¬ (∀ p ∈ pts, agree p z = true) →
      (pts.filter (fun p => agree p z)).length ≤ K) :
    pts.length * (A - B) ≤ D.length * K := by
  let inside : Coord → Bool := fun z => pts.all (fun p => agree p z)
  have hins : ∀ z, inside z = true ↔ ∀ p ∈ pts, agree p z = true := by
    intro z
    exact List.all_eq_true
  have hcommon : (D.filter inside).length ≤ B := by
    cases pts with
    | nil => simp at htwo
    | cons p tail =>
      cases tail with
      | nil => simp at htwo
      | cons q rest =>
        have hpq : p ≠ q := (List.pairwise_cons.mp hnd).1 q (.head _)
        have hb := hshared p (.head _) q (.tail _ (.head _)) hpq
        apply Nat.le_trans (nodup_length_le_of_subset (nodup_filter _ D hD) ?_) hb
        intro z hz
        obtain ⟨hzD, hzall⟩ := List.mem_filter.mp hz
        exact List.mem_filter.mpr ⟨hzD, Bool.and_eq_true_iff.mpr
          ⟨(hins z).mp hzall p (.head _), (hins z).mp hzall q (.tail _ (.head _))⟩⟩
  let remaining : Point → Coord → Bool := fun p z => !inside z && agree p z
  have hremain : ∀ p ∈ pts, A - B ≤ (D.filter (remaining p)).length := by
    intro p hp
    have hc := JohnsonBound.filter_length_le_add (agree p) inside (remaining p) D
      (fun z _ hz => by
        cases hi : inside z with
        | true => exact .inl rfl
        | false => exact .inr (by simp only [remaining, hi]; exact hz))
    have ha := hsize p hp
    omega
  have hfib : ∀ z ∈ D, JohnsonBound.ptDeg remaining pts z ≤ K := by
    intro z hz
    cases hi : inside z with
    | true =>
      have he : pts.filter (fun p => remaining p z) = [] := by
        have hf : ∀ xs : List Point, xs.filter (fun _ => false) = [] := by
          intro xs
          induction xs with
          | nil => rfl
          | cons _ _ ih => exact ih
        simpa only [remaining, hi, Bool.not_true, Bool.false_and] using hf pts
      rw [JohnsonBound.ptDeg_eq]
      change (pts.filter (fun p => remaining p z)).length ≤ K
      rw [he]; exact Nat.zero_le _
    | false =>
      have hn : ¬ (∀ p ∈ pts, agree p z = true) := fun h =>
        Bool.false_ne_true (hi.symm.trans ((hins z).mpr h))
      have he : (fun p => remaining p z) = (fun p => agree p z) := by
        funext p; simp only [remaining, hi, Bool.not_false, Bool.true_and]
      rw [JohnsonBound.ptDeg_eq]
      change (pts.filter (fun p => remaining p z)).length ≤ K
      rw [he]; exact hfiber z hz hn
  have hlo := JohnsonBound.sumNat_map_le (fun _ => A - B)
    (fun p => (D.filter (remaining p)).length) pts hremain
  rw [JohnsonBound.sumNat_map_const] at hlo
  have hhi := JohnsonBound.sumNat_map_le (JohnsonBound.ptDeg remaining pts)
    (fun _ => K) D hfib
  rw [JohnsonBound.sumNat_map_const, JohnsonBound.sum_ptDeg_eq] at hhi
  exact Nat.le_trans hlo hhi

variable {F : Type} [LawfulField F] [DecidableEq F]
local instance : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
open Poly2

/-- Dimension-one incidence count on a primitive component refined against each coordinate
polynomial. The denominator is `A-B`, not a unique-decoding overlap requirement. -/
theorem curve_incidence_card_le {Coord : Type} [DecidableEq Coord] (C : Poly2 F) (hprim : IsPrimY C) (hC : 1 ≤ C.natDeg)
    (D : List Coord) (hD : D.Nodup) (equation : Coord → Poly2 F) (M A B : Nat)
    (hAB : B < A) (hdegree : ∀ z ∈ D, tdeg (equation z) ≤ M)
    (hrefined : ∀ z ∈ D, (∃ Q, equation z = mul C Q) ∨ CoprimeZ C (equation z))
    (pts : List (F × F)) (hnd : pts.Nodup)
    (hcurve : ∀ p ∈ pts, C.eval2 p.1 p.2 = zero)
    (hsize : ∀ p ∈ pts,
      A ≤ (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero))).length)
    (hshared : ∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
      (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero) &&
        decide ((equation z).eval2 q.1 q.2 = zero))).length ≤ B) :
    pts.length ≤ Nat.max 1 ((D.length * (tdeg C * M * C.natDeg)) / (A - B)) := by
  if hsmall : pts.length ≤ 1 then exact Nat.le_trans hsmall (Nat.le_max_left _ _)
  else
    have htwo : 2 ≤ pts.length := by omega
    have hm := incidence_mul_le pts D (fun p z => decide ((equation z).eval2 p.1 p.2 = zero))
      A B (tdeg C * M * C.natDeg) hD hnd htwo hsize hshared (fun z hz hnonfull => by
        rcases hrefined z hz with ⟨Q, hQ⟩ | hcop
        · exact False.elim (hnonfull (fun p hp => decide_eq_true (by
            rw [hQ]
            rw [Poly2.eval2_mul]
            rw [hcurve p hp, LawfulCommRing.zero_mul])))
        · have hne : equation z ≠ zero := fun hzero =>
            hnonfull (fun p _ => decide_eq_true (by rw [hzero, Poly2.eval2_zero]))
          have hb := primitive_common_roots_card_le C (equation z) hprim hC hne hcop
            (pts.filter (fun p => decide ((equation z).eval2 p.1 p.2 = zero)))
            (nodup_filter _ pts hnd) (fun p hp =>
              ⟨hcurve p (List.mem_filter.mp hp).1, of_decide_eq_true (List.mem_filter.mp hp).2⟩)
          exact Nat.le_trans hb (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hdegree z hz))))
    exact Nat.le_trans ((Nat.le_div_iff_mul_le (by omega)).mpr hm) (Nat.le_max_right _ _)

/-- Nonpersistent accepted polynomials on a refined primitive curve satisfy the curve
incidence bound. The geometry may live over an extension field; the words and challenges
remain over their original field. The labels retain the specific accepted polynomial. -/
theorem nonpersistent_curve_card_le {E : Type} [LawfulField E] [DecidableEq E]
    (x : (E → E) × (E → E)) (D : List E) (hD : D.Nodup) (d A B M : Nat)
    (hAB : B < A) (hB : d + 1 ≤ B)
    (C : Poly2 F) (hprim : IsPrimY C) (hC : 1 ≤ C.natDeg)
    (equation : E → Poly2 F) (hdegree : ∀ z ∈ D, tdeg (equation z) ≤ M)
    (hrefined : ∀ z ∈ D, (∃ Q, equation z = mul C Q) ∨ CoprimeZ C (equation z))
    (pts : List (F × F)) (hnd : pts.Nodup)
    (α β : (F × F) → E) (P : (F × F) → UPoly E)
    (hinj : ∀ p ∈ pts, ∀ q ∈ pts, (α p, β p, P p) = (α q, β q, P q) → p = q)
    (hcurve : ∀ p ∈ pts, C.eval2 p.1 p.2 = zero)
    (hdeg : ∀ p ∈ pts, (P p).natDeg ≤ d)
    (haccept : ∀ p ∈ pts, A ≤ (D.filter (foldAgreePt x (α p) (β p) (P p))).length)
    (hnonpers : ∀ p ∈ pts, ¬ IsPersistent x D d B (α p) (β p) (P p))
    (hmatch : ∀ p ∈ pts, ∀ z ∈ D,
      decide ((equation z).eval2 p.1 p.2 = zero) = foldAgreePt x (α p) (β p) (P p) z) :
    pts.length ≤ Nat.max 1 ((D.length * (tdeg C * M * C.natDeg)) / (A - B)) := by
  apply curve_incidence_card_le C hprim hC D hD equation M A B hAB hdegree hrefined
    pts hnd hcurve
  · intro p hp
    have he : D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero)) =
        D.filter (foldAgreePt x (α p) (β p) (P p)) :=
      List.filter_congr (hmatch p hp)
    rw [he]; exact haccept p hp
  · intro p hp q hq hne
    apply nonpersistent_common_agree_le x D d B hB (α p) (β p) (P p) (hdeg p hp)
      (α q) (β q) (P q) (hdeg q hq) (fun he => hne (hinj p hp q hq he)) (hnonpers p hp)
      (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero) &&
        decide ((equation z).eval2 q.1 q.2 = zero))) (nodup_filter _ D hD)
      (fun _ hz => (List.mem_filter.mp hz).1)
    · intro z hz
      obtain ⟨hzD, hpair⟩ := List.mem_filter.mp hz
      rw [hmatch p hp z hzD] at hpair
      exact (Bool.and_eq_true_iff.mp hpair).1
    · intro z hz
      obtain ⟨hzD, hpair⟩ := List.mem_filter.mp hz
      rw [hmatch q hq z hzD] at hpair
      exact (Bool.and_eq_true_iff.mp hpair).2

private theorem root_of_prodList (Cs : List (Poly2 F)) (y z : F)
    (hzero : Poly2.eval2 (UPoly.prodList Cs) y z = zero) :
    ∃ C ∈ Cs, C.eval2 y z = zero := by
  induction Cs with
  | nil =>
    have hone : Poly2.eval2 (UPoly.prodList ([] : List (Poly2 F))) y z = one := by
      rw [UPoly.prodList_nil, Poly2.eval2_eq]
      exact RingHom.map_one _
    rw [hone] at hzero
    exact False.elim (LawfulField.one_ne_zero hzero)
  | cons C Cs ih =>
    have he : Poly2.eval2 (UPoly.prodList (C :: Cs)) y z =
        mul (C.eval2 y z) (Poly2.eval2 (UPoly.prodList Cs) y z) :=
      by rw [UPoly.prodList_cons, Poly2.eval2_mul]
    rw [he] at hzero
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hzero with hC | hCs
    · exact ⟨C, .head _, hC⟩
    · obtain ⟨Q, hQ, hroot⟩ := ih hCs
      exact ⟨Q, .tail _ hQ, hroot⟩

/-- Construct the coordinate-refined curve cover, preserving total degree, and prove
its nonpersistent incidence bounds. No refinement certificate is required from callers. -/
theorem nonpersistent_curve_cover {E : Type} [LawfulField E] [DecidableEq E]
    (x : (E → E) × (E → E)) (D : List E) (hD : D.Nodup) (d A B M : Nat)
    (hAB : B < A) (hB : d + 1 ≤ B)
    (C : Poly2 F) (hprim : IsPrimY C) (hC : 1 ≤ C.natDeg)
    (equation : E → Poly2 F) (hdegree : ∀ z ∈ D, tdeg (equation z) ≤ M)
    (pts : List (F × F)) (hnd : pts.Nodup)
    (α β : (F × F) → E) (P : (F × F) → UPoly E)
    (hinj : ∀ p ∈ pts, ∀ q ∈ pts, (α p, β p, P p) = (α q, β q, P q) → p = q)
    (hcurve : ∀ p ∈ pts, C.eval2 p.1 p.2 = zero)
    (hdeg : ∀ p ∈ pts, (P p).natDeg ≤ d)
    (haccept : ∀ p ∈ pts, A ≤ (D.filter (foldAgreePt x (α p) (β p) (P p))).length)
    (hnonpers : ∀ p ∈ pts, ¬ IsPersistent x D d B (α p) (β p) (P p))
    (hmatch : ∀ p ∈ pts, ∀ z ∈ D,
      decide ((equation z).eval2 p.1 p.2 = zero) = foldAgreePt x (α p) (β p) (P p) z) :
    ∃ Cs : List (Poly2 F), C = UPoly.prodList Cs ∧ (Cs.map tdeg).sum = tdeg C ∧
      (∀ p ∈ pts, ∃ Ci ∈ Cs, Ci.eval2 p.1 p.2 = zero) ∧
      ∀ Ci ∈ Cs, IsPrimY Ci ∧ 1 ≤ Ci.natDeg ∧
        (pts.filter (fun p => decide (Ci.eval2 p.1 p.2 = zero))).length ≤
          Nat.max 1 ((D.length * (tdeg Ci * M * Ci.natDeg)) / (A - B)) := by
  obtain ⟨Cs, hprod, hsum, hvalid, hrefined⟩ := splitAgainstList C (D.map equation) hprim hC
  refine ⟨Cs, hprod, hsum, ?_, ?_⟩
  · intro p hp
    apply root_of_prodList Cs p.1 p.2
    rw [← hprod]
    exact hcurve p hp
  · intro Ci hCi
    obtain ⟨hpri, hpos⟩ := hvalid Ci hCi
    refine ⟨hpri, hpos, ?_⟩
    apply nonpersistent_curve_card_le x D hD d A B M hAB hB Ci hpri hpos equation hdegree
      (fun z hz => hrefined Ci hCi (equation z) (List.mem_map.mpr ⟨z, hz, rfl⟩))
      (pts.filter (fun p => decide (Ci.eval2 p.1 p.2 = zero))) (nodup_filter _ pts hnd)
      α β P
      (fun p hp q hq => hinj p (List.mem_filter.mp hp).1 q (List.mem_filter.mp hq).1)
      (fun _ hp => of_decide_eq_true (List.mem_filter.mp hp).2)
      (fun p hp => hdeg p (List.mem_filter.mp hp).1)
      (fun p hp => haccept p (List.mem_filter.mp hp).1)
      (fun p hp => hnonpers p (List.mem_filter.mp hp).1)
      (fun p hp => hmatch p (List.mem_filter.mp hp).1)

#verify_constructive incidence_mul_le curve_incidence_card_le nonpersistent_curve_card_le nonpersistent_curve_cover
end NonpersistentIncidence
end Qsag

end

section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

/-! ## Lists, covers and arithmetic -/

namespace SlicedJet

section Tab
variable {R : Type} [LawfulCommRing R]

/-- `[f 0, …, f (n-1)]`. -/
def tab (f : Nat → R) : Nat → List R
  | 0 => []
  | n + 1 => f 0 :: tab (fun k => f (k + 1)) n

omit [LawfulCommRing R] in
theorem tab_congr : ∀ (n : Nat) (f g : Nat → R), (∀ j, j < n → f j = g j) → tab f n = tab g n
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    show f 0 :: tab (fun k => f (k + 1)) n = g 0 :: tab (fun k => g (k + 1)) n
    rw [h 0 (Nat.succ_pos n), tab_congr n (fun k => f (k + 1)) (fun k => g (k + 1))
      (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))]

omit [LawfulCommRing R] in
theorem tab_map {S : Type} (φ : R → S) : ∀ (n : Nat) (f : Nat → R),
    (tab f n).map φ = tab (fun k => φ (f k)) n
  | 0, _ => rfl
  | n + 1, f => by
    show φ (f 0) :: (tab (fun k => f (k + 1)) n).map φ =
      φ (f 0) :: tab (fun k => φ (f (k + 1))) n
    rw [tab_map φ n (fun k => f (k + 1))]

theorem evalCoeffs_tab_smul (c w : R) : ∀ (n : Nat) (f : Nat → R),
    evalCoeffs (tab (fun k => mul c (f k)) n) w = mul c (evalCoeffs (tab f n) w)
  | 0, _ => (LawfulCommRing.mul_zero c).symm
  | n + 1, f => by
    show add (mul c (f 0)) (mul w (evalCoeffs (tab (fun k => mul c (f (k + 1))) n) w)) =
      mul c (add (f 0) (mul w (evalCoeffs (tab (fun k => f (k + 1)) n) w)))
    rw [evalCoeffs_tab_smul c w n (fun k => f (k + 1))]
    generalize evalCoeffs (tab (fun k => f (k + 1)) n) w = e
    constructive_ring

theorem evalCoeffs_tab_coeffAt (w : R) : ∀ (n : Nat) (l : List R), l.length ≤ n →
    evalCoeffs (tab (coeffAt l) n) w = evalCoeffs l w
  | 0, l, h => by
    have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
    rw [hl]; rfl
  | n + 1, [], _ => by
    have hf : (fun k => coeffAt ([] : List R) (k + 1)) = coeffAt ([] : List R) :=
      funext fun k => (coeffAt_nil (k + 1)).trans (coeffAt_nil k).symm
    show add (coeffAt ([] : List R) 0)
      (mul w (evalCoeffs (tab (fun k => coeffAt ([] : List R) (k + 1)) n) w)) = zero
    rw [hf, evalCoeffs_tab_coeffAt w n [] (Nat.zero_le n), coeffAt_nil]
    show add zero (mul w zero) = zero
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | n + 1, c :: cs, h => by
    have hf : (fun k => coeffAt (c :: cs) (k + 1)) = coeffAt cs :=
      funext fun k => coeffAt_cons_succ c cs k
    show add (coeffAt (c :: cs) 0)
      (mul w (evalCoeffs (tab (fun k => coeffAt (c :: cs) (k + 1)) n) w)) =
      add c (mul w (evalCoeffs cs w))
    rw [hf, evalCoeffs_tab_coeffAt w n cs (Nat.le_of_succ_le_succ h), coeffAt_cons_zero]

theorem coeffAt_tab : ∀ (n : Nat) (f : Nat → R) (k : Nat),
    coeffAt (tab f n) k = zero ∨ (k < n ∧ coeffAt (tab f n) k = f k)
  | 0, _, k => .inl (coeffAt_nil k)
  | n + 1, f, 0 => .inr ⟨Nat.succ_pos n, coeffAt_cons_zero _ _⟩
  | n + 1, f, k + 1 => by
    have e : coeffAt (tab f (n + 1)) (k + 1) = coeffAt (tab (fun j => f (j + 1)) n) k :=
      coeffAt_cons_succ _ _ k
    rcases coeffAt_tab n (fun j => f (j + 1)) k with h | ⟨hk, h⟩
    · exact .inl (e.trans h)
    · exact .inr ⟨Nat.succ_lt_succ hk, e.trans h⟩

theorem degFn_add_bnd {δ : R → Nat} (hδ : DegFn δ) {a b : R} {B : Nat} (ha : δ a ≤ B)
    (hb : δ b ≤ B) : δ (add a b) ≤ B :=
  Nat.le_trans (hδ.add_le a b) (Nat.max_le.mpr ⟨ha, hb⟩)

theorem degFn_sub_bnd {δ : R → Nat} (hδ : DegFn δ) {a b : R} {B : Nat} (ha : δ a ≤ B)
    (hb : δ b ≤ B) : δ (sub a b) ≤ B := by
  rw [LawfulCommRing.sub_eq_add_neg]
  exact degFn_add_bnd hδ ha (Nat.le_trans (hδ.neg_le b) hb)

theorem degFn_mul_bnd {δ : R → Nat} (hδ : DegFn δ) {a b : R} {A B : Nat} (ha : δ a ≤ A)
    (hb : δ b ≤ B) : δ (mul a b) ≤ A + B :=
  Nat.le_trans (hδ.mul_le a b) (Nat.add_le_add ha hb)

end Tab

theorem filter_split_length {α : Type} (p : α → Bool) : ∀ l : List α,
    (l.filter p).length + (l.filter (fun a => !p a)).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := filter_split_length p l
    cases hpa : p a with
    | true =>
      rw [List.filter_cons_of_pos hpa, List.filter_cons_of_neg (by
        show ¬ (!p a) = true
        rw [hpa]; decide)]
      show (l.filter p).length + 1 + _ = l.length + 1
      omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hpa]; exact Bool.false_ne_true),
        List.filter_cons_of_pos (by show (!p a) = true; rw [hpa]; rfl)]
      show _ + ((l.filter _).length + 1) = l.length + 1
      omega

/-- Counting through a cover: if every point lies on some member and member `Cᵢ` carries at
    most `w(Cᵢ)·K` points, there are at most `(Σ w(Cᵢ))·K` points. -/
theorem cover_count {P C : Type} [DecidableEq P] (pred : C → P → Bool) (w : C → Nat) (K : Nat) :
    ∀ (Cs : List C) (pts : List P), pts.Nodup →
      (∀ Ci ∈ Cs, (pts.filter (pred Ci)).length ≤ w Ci * K) →
      (∀ p ∈ pts, ∃ Ci ∈ Cs, pred Ci p = true) →
      pts.length ≤ (Cs.map w).sum * K
  | [], pts, _, _, hcov => by
    cases pts with
    | nil => exact Nat.zero_le _
    | cons p _ =>
      obtain ⟨_, hm, _⟩ := hcov p (.head _)
      cases hm
  | Ci :: Cs, pts, hnd, hleaf, hcov => by
    have hsplit := filter_split_length (pred Ci) pts
    have ih := cover_count pred w K Cs (pts.filter (fun p => !pred Ci p))
      (nodup_filter _ pts hnd)
      (fun Cj hCj => Nat.le_trans
        (nodup_length_le_of_subset (nodup_filter _ _ (nodup_filter _ pts hnd))
          (fun p hp => by
            obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
            exact List.mem_filter.mpr ⟨(List.mem_filter.mp hp1).1, hp2⟩))
        (hleaf Cj (.tail _ hCj)))
      (fun p hp => by
        obtain ⟨hpm, hpn⟩ := List.mem_filter.mp hp
        obtain ⟨Cj, hCj, hpred⟩ := hcov p hpm
        rcases List.mem_cons.mp hCj with hEq | hCj'
        · rw [hEq] at hpred
          rw [hpred] at hpn
          exact absurd hpn (by decide)
        · exact ⟨Cj, hCj', hpred⟩)
    have hhead := hleaf Ci (.head _)
    show pts.length ≤ (w Ci + (Cs.map w).sum) * K
    rw [Nat.add_mul]
    omega

theorem le_sum_of_mem : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.sum
  | [], _, h => nomatch h
  | a :: l, x, h => by
    show x ≤ a + l.sum
    rcases List.mem_cons.mp h with hEq | h'
    · rw [hEq]; exact Nat.le_add_right _ _
    · exact Nat.le_trans (le_sum_of_mem l x h') (Nat.le_add_left _ _)

/-- The per-leaf bound of `nonpersistent_curve_cover`, made linear in the leaf degree `t`. -/
theorem leaf_bound_arith (n t m M T q : Nat) (ht : 1 ≤ t) (hm : m ≤ T) (hq : 0 < q) :
    Nat.max 1 (n * (t * M * m) / q) ≤ t * (n * (T * M) / q + 1) := by
  have hK : 1 ≤ n * (T * M) / q + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have h1 : 1 ≤ t * (n * (T * M) / q + 1) := Nat.mul_le_mul ht hK
  have hX : n * (T * M) ≤ q * (n * (T * M) / q + 1) := by
    have hd := Nat.div_add_mod (n * (T * M)) q
    have hmod := Nat.mod_lt (n * (T * M)) hq
    rw [Nat.mul_succ]
    omega
  have hnum : n * (t * M * m) ≤ q * (t * (n * (T * M) / q + 1)) := by
    have e1 : n * (t * M * m) ≤ n * (t * M * T) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    have e2 : n * (t * M * T) = t * (n * (T * M)) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have e3 : t * (n * (T * M)) ≤ t * (q * (n * (T * M) / q + 1)) := Nat.mul_le_mul_left _ hX
    have e4 : t * (q * (n * (T * M) / q + 1)) = q * (t * (n * (T * M) / q + 1)) :=
      Nat.mul_left_comm _ _ _
    exact Nat.le_trans e1 (Nat.le_trans (Nat.le_of_eq e2) (Nat.le_trans e3 (Nat.le_of_eq e4)))
  exact Nat.max_le.mpr ⟨h1, Nat.div_le_of_le_mul hnum⟩

/-- `[n-1, …, 0]`. -/
def upTo : Nat → List Nat
  | 0 => []
  | n + 1 => n :: upTo n

theorem mem_upTo : ∀ {n k : Nat}, k < n → k ∈ upTo n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    if hk : k = n then rw [hk]; exact .head _
    else exact .tail _ (mem_upTo (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hk))

theorem length_upTo : ∀ n, (upTo n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (length_upTo n)

theorem pred_lt_of_le {μ n : Nat} (h1 : 1 ≤ μ) (h2 : μ ≤ n) : μ - 1 < n := by omega

theorem npow_ne_zero_field {K : Type} [LawfulField K] [DecidableEq K] {s : K} (hs : s ≠ zero) :
    ∀ n, CRing.npow s n ≠ zero
  | 0 => LawfulField.one_ne_zero
  | n + 1 => fun e => by
    letI : NoZeroDivisors K := LawfulField.toNoZeroDivisors K
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
      (show mul (CRing.npow s n) s = zero from e) with h | h
    · exact npow_ne_zero_field hs n h
    · exact hs h

/-- A factor of a product of nonzero polynomials over a domain has at most its degree. -/
theorem natDeg_le_prodList {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R]
    [NontrivialRing R] : ∀ (ps : List (UPoly R)), (∀ p ∈ ps, p ≠ zero) → ∀ c ∈ ps,
      c.natDeg ≤ (UPoly.prodList ps).natDeg
  | [], _, _, hc => nomatch hc
  | p :: ps, hne, c, hc => by
    have hp : p ≠ zero := hne p (.head _)
    have hps : UPoly.prodList ps ≠ zero :=
      UPoly.prodList_ne_zero ps (fun q hq => hne q (.tail _ hq))
    have hmul : (UPoly.prodList (p :: ps)).natDeg = p.natDeg + (UPoly.prodList ps).natDeg :=
      by rw [UPoly.prodList_cons]; exact UPoly.natDeg_mul hp hps
    rcases List.mem_cons.mp hc with hEq | hc'
    · rw [hEq, hmul]; exact Nat.le_add_right _ _
    · have ih := natDeg_le_prodList ps (fun q hq => hne q (.tail _ hq)) c hc'
      rw [hmul]; exact Nat.le_trans ih (Nat.le_add_left _ _)

end SlicedJet

/-! ## The agreement equation in the jet ring -/

namespace Poly3
section Slice
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly SlicedJet

local instance sliceNoZeroDivisors : NoZeroDivisors (RatFunc F) :=
  LawfulField.toNoZeroDivisors (RatFunc F)

/-- `ζ - T₀ ∈ F(T₀)`. -/
def offK (ζ : F) : RatFunc F := sub (scalK.toFun ζ) genPt

/-- The agreement equation at the coordinate `ζ`, cleared of the denominator `S^(2d-1)`:
    `Σ_{j ≤ d} reconCoeff_j·(ζ - T₀)^j - S^(2d-1)·(f(ζ) + (Y + V·(ζ - T₀))·g(ζ))`
    in the jet ring `F(T₀)[Y][V][Z]`. -/
def jetEq (R : Poly3 F) (d : Nat) (fz gz ζ : F) : Poly3 (RatFunc F) :=
  sub (evalCoeffs (tab (reconCoeff (baseK.toFun R) genPt d) (d + 1)) (C3 (offK ζ)))
    (mul (CRing.npow (henselSep (baseK.toFun R) genPt) (2 * d - 1))
      (add (C3 (scalK.toFun fz))
        (mul (add jetY (mul jetV (C3 (offK ζ)))) (C3 (scalK.toFun gz)))))

theorem deg_jetEq_le (R : Poly3 F) (d h : Nat) (fz gz ζ : F) (hR : R.degYZ ≤ h) (hh : 1 ≤ h)
    (hd : 1 ≤ d) : deg11d 1 (jetEq R d fz gz ζ) ≤ 2 * d * h := by
  have hδ := degFn_deg11d (K := RatFunc F) 1
  have hRK : (baseK.toFun R).degYZ ≤ h :=
    Nat.le_trans (by simpa only [baseK_apply, degYZ] using wdeg_mapHom_mapHom_le (mapHom (scalK (F := F))) R) hR
  have hfirst : deg11d 1 (evalCoeffs (tab (reconCoeff (baseK.toFun R) genPt d) (d + 1))
      (C3 (offK ζ))) ≤ 2 * d * h := by
    apply degFn_evalCoeffs_le hδ (C3 (offK ζ)) 0 (Nat.le_of_eq (deg11d_C3 1 _))
    intro k hk
    rcases coeffAt_tab (d + 1) (reconCoeff (baseK.toFun R) genPt d) k with h0 | ⟨hlt, he⟩
    · exact absurd h0 hk
    · rw [he, Nat.zero_mul, Nat.add_zero]
      exact deg_reconCoeff_le (baseK.toFun R) genPt d h k hRK hh hd (Nat.le_of_lt_succ hlt)
  have hS := deg_henselSep_le (baseK.toFun R) genPt h hRK
  have hpow := degFn_npow_le hδ (deg11d_one 1) _ _ hS (2 * d - 1)
  have hc : ∀ a : RatFunc F, deg11d 1 (C3 a) ≤ 0 := fun a => Nat.le_of_eq (deg11d_C3 1 a)
  have hc1 : ∀ a : RatFunc F, deg11d 1 (C3 a) ≤ 1 := fun a => Nat.le_trans (hc a) (Nat.zero_le 1)
  have hlin : deg11d 1 (add (C3 (scalK.toFun fz))
      (mul (add jetY (mul jetV (C3 (offK ζ)))) (C3 (scalK.toFun gz)))) ≤ 1 :=
    degFn_add_bnd hδ (hc1 _)
      (degFn_mul_bnd hδ (degFn_add_bnd hδ deg11d_jetY_le (degFn_mul_bnd hδ deg11d_jetV_le (hc _)))
        (hc _))
  have harith := recon_arith d h (2 * d - 1) 0 hd hh (Nat.le_refl _)
  rw [Nat.zero_mul] at harith
  exact degFn_sub_bnd hδ hfirst (Nat.le_trans (degFn_mul_bnd hδ hpow hlin) harith)

theorem scalK_inj (c : F) (h : (scalK (F := F)).toFun c = zero) : c = zero := by
  rw [scalK_apply] at h
  have h1 : (C c : UPoly F) = zero :=
    Frac.of_injective (h.trans (Frac.of (D := UPoly F)).map_zero.symm)
  have h2 := congrArg (fun p : UPoly F => coeffAt p.coeffs 0) h1
  rwa [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at h2

/-- The reconstruction sum at the jet of a simple root is `s^(2d-1)·P(T₀ + w)`. -/
theorem recon_sum_pt (R : Poly3 F) (α β : F) (P : UPoly F) (d : Nat) (hd : 1 ≤ d)
    (hP : P.natDeg ≤ d) (hroot : evalAffineLine R α β P = zero)
    (hsep : evalAffineLine (hasseZ 1 R) α β P ≠ zero) (w : RatFunc F) :
    evalCoeffs ((tab (reconCoeff (baseK.toFun R) genPt d) (d + 1)).map
      (ptHom ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)
        ((Frac.of (D := UPoly F)).toFun P)).toFun) w =
      mul (CRing.npow ((Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P))
        (2 * d - 1))
        (((mapHom scalK).toFun P).eval (add genPt w)) := by
  have hqlen : ((taylorShift genPt).toFun ((mapHom (scalK (F := F))).toFun P)).coeffs.length ≤
      d + 1 := by
    have hq : ((taylorShift genPt).toFun ((mapHom (scalK (F := F))).toFun P)).natDeg ≤ d :=
      natDeg_le_of_coeffAt _ d (fun k hk => by
        rw [coeffAt_taylorShift, eval_hasse]
        apply gsUniHasse_eq_zero_of_length_le
        have h1 : ((mapHom (scalK (F := F))).toFun P).coeffs.length - 1 ≤ P.natDeg :=
          natDeg_mapHom_le (scalK (F := F)) P
        omega)
    have hq' : ((taylorShift genPt).toFun ((mapHom (scalK (F := F))).toFun P)).coeffs.length - 1
        ≤ d := hq
    omega
  have e1 := tab_map (ptHom ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)
    ((Frac.of (D := UPoly F)).toFun P)).toFun (d + 1) (reconCoeff (baseK.toFun R) genPt d)
  have e2 := tab_congr (d + 1)
    (fun k => (ptHom ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)
      ((Frac.of (D := UPoly F)).toFun P)).toFun (reconCoeff (baseK.toFun R) genPt d k))
    (fun k => mul (CRing.npow ((Frac.of (D := UPoly F)).toFun
        (evalAffineLine (hasseZ 1 R) α β P)) (2 * d - 1))
      (coeffAt ((taylorShift genPt).toFun ((mapHom scalK).toFun P)).coeffs k))
    (fun j hj => jet_cover R α β P d hd hroot hsep j (Nat.le_of_lt_succ hj))
  rw [e1, e2, evalCoeffs_tab_smul _ w (d + 1)
    (coeffAt ((taylorShift genPt).toFun ((mapHom scalK).toFun P)).coeffs),
    evalCoeffs_tab_coeffAt w (d + 1) _ hqlen, ← eval_eq, eval_taylorShift]

/-- **Value of the agreement equation at a jet.** At the jet of a simple root `(α, β, P)` of
    `R`, `jetEq` evaluates to `s^(2d-1)·(P(ζ) - f(ζ) - (α + βζ)·g(ζ))` with `s ≠ 0`. -/
theorem jetEq_pt (R : Poly3 F) (x : (F → F) × (F → F)) (α β ζ : F) (P : UPoly F) (d : Nat)
    (hd : 1 ≤ d) (hP : P.natDeg ≤ d) (hroot : evalAffineLine R α β P = zero)
    (hsep : evalAffineLine (hasseZ 1 R) α β P ≠ zero) :
    (ptHom ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)
      ((Frac.of (D := UPoly F)).toFun P)).toFun (jetEq R d (x.1 ζ) (x.2 ζ) ζ) =
    mul (CRing.npow ((Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P))
        (2 * d - 1))
      (scalK.toFun (sub (P.eval ζ) (add (x.1 ζ) (mul (add α (mul β ζ)) (x.2 ζ))))) := by
  obtain ⟨_, _, h3, _, _⟩ := jet_hyps R α β P hroot hsep
  have hSep : (ptHom ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)
      ((Frac.of (D := UPoly F)).toFun P)).toFun (henselSep (baseK.toFun R) genPt) =
      (Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P) :=
    (ptHom_henselSep _ _ _ _ _).trans h3
  have hoff : add genPt (offK ζ) = (scalK (F := F)).toFun ζ := by
    show add genPt (sub (scalK.toFun ζ) genPt) = scalK.toFun ζ
    constructive_ring
  have hPK : ((mapHom (scalK (F := F))).toFun P).eval (scalK.toFun ζ) = scalK.toFun (P.eval ζ) :=
    eval_mapHom scalK P ζ
  have e1 : line α β = add (C α) (mul X (C β)) := ofList_cons α [β]
  have hy : (Frac.of (D := UPoly F)).toFun (line α β) =
      add (scalK.toFun α) (mul genPt (scalK.toFun β)) := by
    rw [e1, RingHom.map_add, RingHom.map_mul, scalK_apply, scalK_apply, genPt_eq]
  show (ptHom ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)
      ((Frac.of (D := UPoly F)).toFun P)).toFun
    (sub (evalCoeffs (tab (reconCoeff (baseK.toFun R) genPt d) (d + 1)) (C3 (offK ζ)))
      (mul (CRing.npow (henselSep (baseK.toFun R) genPt) (2 * d - 1))
        (add (C3 (scalK.toFun (x.1 ζ)))
          (mul (add jetY (mul jetV (C3 (offK ζ)))) (C3 (scalK.toFun (x.2 ζ))))))) = _
  rw [RingHom.map_sub, RingHom.map_evalCoeffs, RingHom.map_mul, RingHom.map_npow, hSep,
    RingHom.map_add, RingHom.map_mul, RingHom.map_add, RingHom.map_mul, ptHom_C3, ptHom_C3,
    ptHom_C3, ptHom_jetY, ptHom_jetV, recon_sum_pt R α β P d hd hP hroot hsep, hoff, hPK,
    RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_add, RingHom.map_mul]
  show sub _ (mul _ (add _ (mul (add ((Frac.of (D := UPoly F)).toFun (line α β))
    (mul (scalK.toFun β) (sub (scalK.toFun ζ) genPt))) _))) = _
  rw [hy]
  constructive_ring

/-! ## Fixing the slope: from the jet ring to the plane -/

/-- Substitute `V = v`: `K[Y][V][Z] → K[Y][Z]`. -/
def specV {K : Type} [LawfulField K] [DecidableEq K] (v : K) : RingHom (Poly3 K) (Poly2 K) :=
  mapHom (evalHom (C v))

theorem eval2_specV {K : Type} [LawfulField K] [DecidableEq K] (v y z : K) (q : Poly3 K) :
    Poly2.eval2 ((specV v).toFun q) y z = (ptHom y v z).toFun q := by
  rw [Poly2.eval2_eq, eval₂Hom_apply, ptHom_apply]
  show eval₂ (evalHom y) z ((mapHom (evalHom (C v))).toFun q) =
    eval₂ (eval₂Hom (evalHom y) v) z q
  rw [eval₂_mapHom]
  refine eval₂_congr _ _ (fun c => ?_) z q
  simp only [RingHom.comp_toFun, eval₂Hom_apply, evalHom_apply]
  rw [← eval₂_id (C v) c, ← evalHom_apply]
  show (evalHom y).toFun (eval₂ (RingHom.id _) (C v) c) = eval₂ (evalHom y) v c
  rw [hom_eval₂, evalHom_apply, eval_C]
  rw [RingHom.comp_id]

theorem tdeg_specV_le {K : Type} [LawfulField K] [DecidableEq K] (v : K) (q : Poly3 K) :
    Poly2.tdeg ((specV v).toFun q) ≤ deg11d 1 q := by
  apply wdeg_le
  intro k hk
  rw [show coeffAt ((specV v).toFun q).coeffs k = (evalHom (C v)).toFun (coeffAt q.coeffs k)
    from coeffAt_mapHom _ q k] at hk ⊢
  have hne : coeffAt q.coeffs k ≠ zero := fun e => hk (by rw [e, RingHom.map_zero])
  have h1 := le_wdeg (fun c : UPoly (UPoly K) => c.wdeg natDeg 1) 1 q k hne
  have h2 : natDeg (eval₂ (RingHom.id _) (C v) (coeffAt q.coeffs k)) ≤
      (coeffAt q.coeffs k).wdeg natDeg 1 :=
    degFn_eval₂_le degFn_natDeg (RingHom.id _) natDeg (fun _ => by rw [RingHom.id_toFun]; exact Nat.le_refl _) (C v) 1
      (Nat.le_trans (Nat.le_of_eq (natDeg_C_eq v)) (Nat.zero_le 1)) (coeffAt q.coeffs k)
  have h2' : natDeg ((evalHom (C v)).toFun (coeffAt q.coeffs k)) ≤
      (coeffAt q.coeffs k).wdeg natDeg 1 := by simpa only [evalHom_apply, eval₂_id] using h2
  have h1' : (coeffAt q.coeffs k).wdeg natDeg 1 + 1 * k ≤ deg11d 1 q := h1
  omega

/-! ## The plane curve -/

theorem liftK_facts_of_sep (R : Poly3 F) (α β : F) (P : UPoly F)
    (hsep : evalAffineLine (hasseZ 1 R) α β P ≠ zero) :
    liftK.toFun R ≠ zero ∧ 1 ≤ (liftK.toFun R).natDeg := by
  have hRdeg : 1 ≤ R.natDeg := by
    apply Decidable.byContradiction
    intro hn
    have h0 : R.natDeg = 0 := by omega
    have hRC : R = C (coeffAt R.coeffs 0) := ext_coeffAt (fun k => by
      cases k with
      | zero => rw [coeffAt_C_zero]
      | succ k => rw [coeffAt_C_succ]; exact R.coeffAt_eq_zero_of_natDeg_lt (by omega))
    apply hsep
    have hz : hasseZ 1 R = zero := by
      rw [hasseZ_eq]
      rw [hRC]; exact hasse_one_C _
    rw [hz, evalAffineLine_zero]
  have hnat : (liftK.toFun R).natDeg = R.natDeg := by simpa only [liftK_apply] using natDeg_mapHom _ map_of_inj R
  refine ⟨fun e => ?_, by omega⟩
  have h0 : (liftK.toFun R).natDeg = 0 := by rw [e]; exact natDeg_zero
  omega

/-- The jet of a simple root lies on the `Y`-primitive part of the plane curve
    `R(T₀, Y, Z) = 0`: the content cannot vanish there, since the separant does not. -/
theorem primY_liftK_eval (R : Poly3 F) (α β : F) (P : UPoly F)
    (hroot : evalAffineLine R α β P = zero)
    (hsep : evalAffineLine (hasseZ 1 R) α β P ≠ zero) :
    (Poly2.primY (liftK.toFun R)).eval2 ((Frac.of (D := UPoly F)).toFun (line α β))
      ((Frac.of (D := UPoly F)).toFun P) = zero := by
  obtain ⟨hne, _⟩ := liftK_facts_of_sep R α β P hsep
  obtain ⟨_, _, hfac, _, _⟩ := Poly2.contY_mul_primY hne
  have hC0 : eval₂ (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))
      ((Frac.of (D := UPoly F)).toFun P) (liftK.toFun R) = zero := by
    rw [liftK_apply]
    rw [eval₂_mapHom_mapHom]
    rw [← evalAffineLine_eq_eval₂]
    rw [hroot, RingHom.map_zero]
  have hmul : eval₂ (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))
      ((Frac.of (D := UPoly F)).toFun P) (liftK.toFun R) =
      mul ((Poly2.contY (liftK.toFun R)).eval ((Frac.of (D := UPoly F)).toFun (line α β)))
        (eval₂ (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))
          ((Frac.of (D := UPoly F)).toFun P) (Poly2.primY (liftK.toFun R))) := by
    conv => lhs; rw [hfac]
    rw [eval₂_mul, eval₂_C, evalHom_apply]
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (hmul.symm.trans hC0) with hc | hp
  · exfalso
    apply hsep
    apply Frac.of_injective
    rw [RingHom.map_zero]
    have e1 : (Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P) =
        eval₂ (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))
          ((Frac.of (D := UPoly F)).toFun P) (liftK.toFun (hasseZ 1 R)) :=
      by simpa only [evalAffineLine_eq_eval₂, liftK_apply] using (eval₂_mapHom_mapHom (Frac.of (D := UPoly F)) (hasseZ 1 R) (line α β) P).symm
    have e2 : liftK.toFun (hasseZ 1 R) = hasse 1 (liftK.toFun R) :=
      by simpa only [liftK_apply, hasseZ_eq] using mapHom_hasse (mapHom (Frac.of (D := UPoly F))) 1 R
    have e3 : ∀ q : Poly2 (RatFunc F),
        eval₂ (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))
          ((Frac.of (D := UPoly F)).toFun P) q =
        ((mapHom (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))).toFun q).eval
          ((Frac.of (D := UPoly F)).toFun P) := fun q => by
      show _ = eval₂ (RingHom.id _) _ ((mapHom _).toFun q)
      rw [eval₂_mapHom]
      rw [RingHom.id_comp]
    have e4 : (mapHom (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))).toFun
        (liftK.toFun R) = zero := ext_coeffAt (fun k => by
      have hk : coeffAt (liftK.toFun R).coeffs k =
          mul (Poly2.contY (liftK.toFun R)) (coeffAt (Poly2.primY (liftK.toFun R)).coeffs k) := by
        conv => lhs; rw [hfac]
        exact coeffAt_C_mul _ _ k
      rw [coeffAt_mapHom, coeffs_zero, coeffAt_nil, hk, RingHom.map_mul, evalHom_apply, hc,
        LawfulCommRing.zero_mul])
    rw [e1, e2, e3, mapHom_hasse, e4, hasse_one_zero, eval_zero_poly]
  · exact hp

/-! ## One slope, one stratum -/

/-- The jet of the selected root at the challenge `(a, β)`, without its fixed `V`-coordinate. -/
def jetPt (β : F) (Pf : F → UPoly F) (a : F) : RatFunc F × RatFunc F :=
  ((Frac.of (D := UPoly F)).toFun (line a β), (Frac.of (D := UPoly F)).toFun (Pf a))

theorem jetPt_inj (β : F) (Pf : F → UPoly F) (a a' : F) (e : jetPt β Pf a = jetPt β Pf a') :
    a = a' :=
  (line_inj (Frac.of_injective (congrArg Prod.fst e))).1

private theorem slice_card_le_of_mem (x : (F → F) × (F → F)) (D : List F) (hD : D.Nodup)
    (d A B h : Nat) (hd : 1 ≤ d) (hh : 1 ≤ h) (hAB : B < A) (hB : d + 1 ≤ B)
    (R : Poly3 F) (hR : R.degYZ ≤ h) (zb : Nat) (hz : R.degZ ≤ zb) (β : F) (as : List F)
    (hgood : ∀ a ∈ as, ∃ P : UPoly F, P.natDeg ≤ d ∧
      A ≤ (D.filter (foldAgreePt x a β P)).length ∧ evalAffineLine R a β P = zero ∧
      evalAffineLine (hasseZ 1 R) a β P ≠ zero ∧ ¬ IsPersistent x D d B a β P)
    (hnd : as.Nodup)
    (a₀ : F) (ha₀ : a₀ ∈ as) :
    as.length ≤ h * (D.length * (zb * (2 * d * h)) / (A - B) + 1) := by
  obtain ⟨Pf, hPf⟩ := list_finite_choice (fun (a : F) (P : UPoly F) => P.natDeg ≤ d ∧
      A ≤ (D.filter (foldAgreePt x a β P)).length ∧ evalAffineLine R a β P = zero ∧
      evalAffineLine (hasseZ 1 R) a β P ≠ zero ∧ ¬ IsPersistent x D d B a β P) zero as hgood
  have hptsNd : (as.map (jetPt β Pf)).Nodup :=
    List.pairwise_map.mpr (List.Pairwise.imp (fun {a a'} hne e => hne (jetPt_inj β Pf a a' e)) hnd)
  obtain ⟨inv, hinv⟩ := list_finite_choice
    (fun (pt : RatFunc F × RatFunc F) (a : F) => a ∈ as ∧ pt = jetPt β Pf a) zero
    (as.map (jetPt β Pf)) (fun pt hpt => by
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hpt
      exact ⟨a, ha, he.symm⟩)
  obtain ⟨_, _, _, hsep₀, _⟩ := hPf a₀ ha₀
  obtain ⟨hC0, hC0deg⟩ := liftK_facts_of_sep R a₀ β (Pf a₀) hsep₀
  obtain ⟨_, hprim, _, hpdeg, htd⟩ := Poly2.contY_mul_primY hC0
  have hT : Poly2.tdeg (Poly2.primY (liftK.toFun R)) ≤ h := by
    have h2 : Poly2.tdeg (liftK.toFun R) ≤ R.degYZ := by simpa only [liftK_apply, Poly2.tdeg, degYZ] using wdeg_mapHom_mapHom_le (Frac.of (D := UPoly F)) R
    omega
  have hfst : ∀ pt ∈ as.map (jetPt β Pf),
      pt.1 = (Frac.of (D := UPoly F)).toFun (line (inv pt) β) :=
    fun pt hpt => congrArg Prod.fst (hinv pt hpt).2
  have hsnd : ∀ pt ∈ as.map (jetPt β Pf),
      pt.2 = (Frac.of (D := UPoly F)).toFun (Pf (inv pt)) :=
    fun pt hpt => congrArg Prod.snd (hinv pt hpt).2
  have key : ∀ pt ∈ as.map (jetPt β Pf), ∀ ζ : F,
      decide (((specV (scalK.toFun β)).toFun (jetEq R d (x.1 ζ) (x.2 ζ) ζ)).eval2 pt.1 pt.2 =
        zero) = foldAgreePt x (inv pt) β (Pf (inv pt)) ζ := by
    intro pt hpt ζ
    obtain ⟨hPd, _, hroot, hsep, _⟩ := hPf (inv pt) (hinv pt hpt).1
    have hs : (Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) (inv pt) β
        (Pf (inv pt))) ≠ zero := fun e =>
      hsep (Frac.of_injective (e.trans (Frac.of (D := UPoly F)).map_zero.symm))
    have hval := (eval2_specV (scalK.toFun β) _ _ _).trans
      (jetEq_pt R x (inv pt) β ζ (Pf (inv pt)) d hd hPd hroot hsep)
    rw [hfst pt hpt, hsnd pt hpt, hval]
    show _ = decide ((Pf (inv pt)).eval ζ =
      add (x.1 ζ) (mul (add (inv pt) (mul β ζ)) (x.2 ζ)))
    if hag : (Pf (inv pt)).eval ζ = add (x.1 ζ) (mul (add (inv pt) (mul β ζ)) (x.2 ζ)) then
      exact (decide_eq_true (by
        rw [hag, LawfulCommRing.sub_self, RingHom.map_zero, LawfulCommRing.mul_zero])).trans
        (decide_eq_true hag).symm
    else
      exact (decide_eq_false (fun hz => by
        rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with h1 | h1
        · exact npow_ne_zero_field hs _ h1
        · exact hag (LawfulCommRing.sub_eq_zero_iff.mp (scalK_inj _ h1)))).trans
        (decide_eq_false hag).symm
  obtain ⟨Cs, hprod, hsum, hcov, hleaf⟩ := NonpersistentIncidence.nonpersistent_curve_cover
    (F := RatFunc F) x D hD d A B (2 * d * h) hAB hB
    (Poly2.primY (liftK.toFun R)) hprim (by rw [hpdeg]; exact hC0deg)
    (fun ζ => (specV (scalK.toFun β)).toFun (jetEq R d (x.1 ζ) (x.2 ζ) ζ))
    (fun ζ _ => Nat.le_trans (tdeg_specV_le _ _) (deg_jetEq_le R d h _ _ ζ hR hh hd))
    (as.map (jetPt β Pf)) hptsNd inv (fun _ => β) (fun pt => Pf (inv pt))
    (fun p hp q hq e => (hinv p hp).2.trans
      ((congrArg (jetPt β Pf) (congrArg Prod.fst e)).trans (hinv q hq).2.symm))
    (fun pt hpt => by
      obtain ⟨_, _, hroot, hsep, _⟩ := hPf (inv pt) (hinv pt hpt).1
      rw [hfst pt hpt, hsnd pt hpt]
      exact primY_liftK_eval R (inv pt) β (Pf (inv pt)) hroot hsep)
    (fun pt hpt => (hPf (inv pt) (hinv pt hpt).1).1)
    (fun pt hpt => (hPf (inv pt) (hinv pt hpt).1).2.1)
    (fun pt hpt => (hPf (inv pt) (hinv pt hpt).1).2.2.2.2)
    (fun pt hpt ζ _ => key pt hpt ζ)
  have hcount := cover_count
    (fun (Ci : Poly2 (RatFunc F)) (pt : RatFunc F × RatFunc F) =>
      decide (Ci.eval2 pt.1 pt.2 = zero)) Poly2.tdeg
    (D.length * (zb * (2 * d * h)) / (A - B) + 1) Cs (as.map (jetPt β Pf)) hptsNd
    (fun Ci hCi => by
      obtain ⟨_, hpos, hb⟩ := hleaf Ci hCi
      have hleafZ : Ci.natDeg ≤ zb := by
        have h1 := natDeg_le_prodList Cs (fun c hc => (hleaf c hc).1.1) Ci hCi
        rw [← hprod, hpdeg] at h1
        have hnat : (liftK.toFun R).natDeg = R.natDeg := by simpa only [liftK_apply] using natDeg_mapHom _ map_of_inj R
        rw [hnat] at h1
        exact Nat.le_trans h1 (by simpa only [degZ_eq] using hz)
      exact Nat.le_trans hb (leaf_bound_arith D.length (Poly2.tdeg Ci) Ci.natDeg (2 * d * h) zb
        (A - B) (Nat.le_trans hpos (Poly2.natDeg_le_tdeg Ci)) hleafZ (Nat.sub_pos_of_lt hAB)))
    (fun pt hpt => by
      obtain ⟨Ci, hCi, hz⟩ := hcov pt hpt
      exact ⟨Ci, hCi, decide_eq_true hz⟩)
  rw [hsum, List.length_map] at hcount
  exact Nat.le_trans hcount (Nat.mul_le_mul_right _ hT)

/-- **Nonpersistent count on one slice.** Fix `R` with `deg_{Y,Z} R ≤ h`, `deg_Z R ≤ zb` and a
    slope `β`. At most `h·(|D|·zb·2dh/(A-B) + 1)` intercepts `α` admit a simple root `P` of `R` on the
    line `Y = α + βX` of degree at most `d` that agrees with the fold on at least `A`
    coordinates and is not `B`-persistent. -/
theorem slice_card_le (x : (F → F) × (F → F)) (D : List F) (hD : D.Nodup)
    (d A B h : Nat) (hd : 1 ≤ d) (hh : 1 ≤ h) (hAB : B < A) (hB : d + 1 ≤ B)
    (R : Poly3 F) (hR : R.degYZ ≤ h) (zb : Nat) (hz : R.degZ ≤ zb) (β : F) (as : List F)
    (hgood : ∀ a ∈ as, ∃ P : UPoly F, P.natDeg ≤ d ∧
      A ≤ (D.filter (foldAgreePt x a β P)).length ∧ evalAffineLine R a β P = zero ∧
      evalAffineLine (hasseZ 1 R) a β P ≠ zero ∧ ¬ IsPersistent x D d B a β P)
    (hnd : as.Nodup) :
    as.length ≤ h * (D.length * (zb * (2 * d * h)) / (A - B) + 1) := by
  cases as with
  | nil => exact Nat.zero_le _
  | cons a₀ rest =>
    exact slice_card_le_of_mem x D hD d A B h hd hh hAB hB R hR zb hz β (a₀ :: rest) hgood hnd a₀
      (.head _)

/-! ## All slopes and strata, with the persistent pairs -/

/-- The `Z`-degree is at most the `(1, 1, d)`-weighted degree divided by `d`. -/
theorem degZ_le_div (R : Poly3 F) (d W : Nat) (hd : 1 ≤ d) (hW : R.deg11d d ≤ W) :
    R.degZ ≤ W / d := by
  if h0 : R = zero then
    have hz : R.degZ = 0 := by rw [degZ_eq, h0]; exact UPoly.natDeg_zero
    rw [hz]; exact Nat.zero_le _
  else
    have hl := le_wdeg (fun q : UPoly (UPoly F) => q.wdeg natDeg 1) d R R.natDeg (coeffAt_natDeg_ne_zero h0)
    have hl' : d * R.natDeg ≤ W :=
      Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _) hl) hW
    rw [Nat.mul_comm] at hl'
    rw [degZ_eq]
    exact (Nat.le_div_iff_mul_le hd).mpr hl'

theorem degZ_le_degYZ (Q : Poly3 F) : Q.degZ ≤ Q.degYZ := by
  rw [degZ_eq]
  if h : Q = zero then
    show Q.coeffs.length - 1 ≤ _
    rw [h, coeffs_zero]; exact Nat.zero_le _
  else
    have hl := le_wdeg UPoly.natDeg 1 Q Q.natDeg (coeffAt_natDeg_ne_zero h)
    show Q.natDeg ≤ Q.wdeg UPoly.natDeg 1
    omega

theorem deg11d_hasseZ_le (d k : Nat) (Q : Poly3 F) : (hasseZ k Q).deg11d d ≤ Q.deg11d d :=
  by rw [hasseZ_eq]; exact Nat.le_trans (wdeg_hasse_le (fun q : UPoly (UPoly F) => q.wdeg natDeg 1)
    (degFn_wdeg degFn_natDeg 1) d k Q) (Nat.sub_le _ _)

/-- **The non-excluded count, candidate by candidate.** Let `deg_{Y,Z} Q ≤ h`, let
    `1, …, deg_Z Q` be invertible, `d + 1 ≤ B < A` and `|D|·(d + 1) < B²`. The challenges
    `(α, β) ∈ S × S` on which `Q` does not vanish identically and which carry a root `P` of
    `Q` of degree at most `d` with agreement at least `A` and no polynomial explanation with
    correlated agreement `A - 1` number at most
    `ℓ·max{|S|, n(n-1)/2} + |S|·z·h·(n·z·2dh/(A-B) + 1)`, where `z = min{h, W/d}` and
    `deg_{1,1,d} Q ≤ W`. -/
theorem nonExcluded_pairs_card_le (x : (F → F) × (F → F)) (D S : List F) (hD : D.Nodup)
    (hS : S.Nodup) (d A B h : Nat) (hd : 1 ≤ d) (hh : 1 ≤ h) (hAB : B < A) (hB : d + 1 ≤ B)
    (hDen : D.length * (d + 1) < B * B) (Q : Poly3 F) (hQ : Q.degYZ ≤ h)
    (W : Nat) (hW : Q.deg11d d ≤ W)
    (hchar : ∀ k, 1 ≤ k → k ≤ Q.degZ → (CRing.natCast k : F) ≠ zero)
    (L : List (F × F)) (hNd : L.Nodup)
    (hL : ∀ p ∈ L, p ∈ prodPool S ∧ lineSpec Q p.1 p.2 ≠ zero ∧
      ∃ P : UPoly F, P.natDeg ≤ d ∧ A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
        evalAffineLine Q p.1 p.2 P = zero ∧
        ¬ HasPolynomialExplanation x D d (A - 1) p.1 p.2 P) :
    L.length ≤ ((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
        Nat.max S.length (D.length * (D.length - 1) / 2) +
      S.length * ((Nat.min h (W / d)) * (h * (D.length * ((Nat.min h (W / d)) * (2 * d * h)) / (A - B) + 1))) := by
  apply Decidable.byContradiction
  intro hGt
  let Sel : F × F → Bool × UPoly F × Nat → Prop := fun p w =>
    w.2.1.natDeg ≤ d ∧ A ≤ (D.filter (foldAgreePt x p.1 p.2 w.2.1)).length ∧
    ¬ HasPolynomialExplanation x D d (A - 1) p.1 p.2 w.2.1 ∧ w.2.2 < Q.degZ ∧
    evalAffineLine (hasseZ w.2.2 Q) p.1 p.2 w.2.1 = zero ∧
    evalAffineLine (hasseZ 1 (hasseZ w.2.2 Q)) p.1 p.2 w.2.1 ≠ zero ∧
    (w.1 = true → IsPersistent x D d B p.1 p.2 w.2.1) ∧
    (w.1 = false → ¬ IsPersistent x D d B p.1 p.2 w.2.1)
  have hnn : ∀ p ∈ L, ¬¬ ∃ w, Sel p w := by
    intro p hp hn
    obtain ⟨_, hnv, P, hPd, hPa, hroot, hNoEx⟩ := hL p hp
    obtain ⟨μ, h1, h2, h3, h4⟩ := simple_root_of_hasse Q hchar p.1 p.2 P hnv hroot
    exact hn ⟨(false, P, μ - 1), hPd, hPa, hNoEx, pred_lt_of_le h1 h2, h3, h4,
      (fun e => Bool.noConfusion (show false = true from e)),
      (fun _ hpers => hn ⟨(true, P, μ - 1), hPd, hPa, hNoEx,
        pred_lt_of_le h1 h2, h3, h4, (fun _ => hpers),
        (fun e => Bool.noConfusion (show true = false from e))⟩)⟩
  refine not_not_forall_mem _ L hnn (fun hAll => hGt ?_)
  obtain ⟨wf, hwf⟩ := list_finite_choice Sel (false, zero, 0) L hAll
  have hsplit := filter_split_length (fun p : F × F => (wf p).1) L
  have hP : (L.filter (fun p => (wf p).1)).length ≤
      ((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
        Nat.max S.length (D.length * (D.length - 1) / 2) :=
    exceptional_persistent_pairs_card_le x D S d A B hD hS hDen _ (nodup_filter _ L hNd)
      (fun p hp => (hL p (List.mem_filter.mp hp).1).1) (fun p hp => by
        obtain ⟨hpL, hlab⟩ := List.mem_filter.mp hp
        obtain ⟨hPd, hPa, hNoEx, _, _, _, hpers, _⟩ := hwf p hpL
        exact ⟨(wf p).2.1, hPd, hPa, hpers hlab, hNoEx⟩)
  have hclass : ∀ (b : F) (k : Nat),
      (((L.filter (fun p => !(wf p).1)).filter (fun p => decide (p.2 = b))).filter
        (fun p => decide ((wf p).2.2 = k))).length ≤
        h * (D.length * ((Nat.min h (W / d)) * (2 * d * h)) / (A - B) + 1) := by
    intro b k
    have hmemL : ∀ p ∈ ((L.filter (fun p => !(wf p).1)).filter
        (fun p => decide (p.2 = b))).filter (fun p => decide ((wf p).2.2 = k)),
        p ∈ L ∧ (wf p).1 = false ∧ p.2 = b ∧ (wf p).2.2 = k := by
      intro p hp
      obtain ⟨hp1, hk⟩ := List.mem_filter.mp hp
      obtain ⟨hp2, hb⟩ := List.mem_filter.mp hp1
      obtain ⟨hpL, hlab⟩ := List.mem_filter.mp hp2
      refine ⟨hpL, ?_, of_decide_eq_true hb, of_decide_eq_true hk⟩
      cases hw : (wf p).1 with
      | false => rfl
      | true => rw [hw] at hlab; exact absurd hlab (by decide)
    have hLNd := nodup_filter (fun p : F × F => decide ((wf p).2.2 = k)) _
      (nodup_filter (fun p : F × F => decide (p.2 = b)) _
        (nodup_filter (fun p : F × F => !(wf p).1) L hNd))
    rw [← List.length_map (f := Prod.fst)]
    apply slice_card_le x D hD d A B h hd hh hAB hB (hasseZ k Q)
      (Nat.le_trans (Nat.le_trans (degYZ_hasseZ_le k Q) (Nat.sub_le _ _)) hQ) (Nat.min h (W / d))
      (Nat.le_min.mpr ⟨Nat.le_trans (degZ_le_degYZ _)
          (Nat.le_trans (Nat.le_trans (degYZ_hasseZ_le k Q) (Nat.sub_le _ _)) hQ),
        degZ_le_div (hasseZ k Q) d W hd (Nat.le_trans (deg11d_hasseZ_le d k Q) hW)⟩) b
    · intro a ha
      obtain ⟨p, hp, hpa⟩ := List.mem_map.mp ha
      obtain ⟨hpL, hlab, hpb, hpk⟩ := hmemL p hp
      obtain ⟨hPd, hPa, _, _, hroot, hsep, _, hnp⟩ := hwf p hpL
      rw [← hpa, ← hpb, ← hpk]
      exact ⟨(wf p).2.1, hPd, hPa, hroot, hsep, hnp hlab⟩
    · exact List.pairwise_map.mpr (List.Pairwise.imp_of_mem (fun {p q} hp hq hne hfst =>
        hne (Prod.ext hfst ((hmemL p hp).2.2.1.trans (hmemL q hq).2.2.1.symm))) hLNd)
  have hN : (L.filter (fun p => !(wf p).1)).length ≤
      S.length * (Q.degZ * (h * (D.length * ((Nat.min h (W / d)) * (2 * d * h)) / (A - B) + 1))) :=
    JohnsonBound.count_partition_le Prod.snd _ _ S
      (fun p hp => (mem_prodPool_iff.mp (hL p (List.mem_filter.mp hp).1).1).2)
      (fun b _ => by
        have hk := JohnsonBound.count_partition_le (fun p : F × F => (wf p).2.2)
          (h * (D.length * ((Nat.min h (W / d)) * (2 * d * h)) / (A - B) + 1))
          ((L.filter (fun p => !(wf p).1)).filter (fun p => decide (p.2 = b))) (upTo Q.degZ)
          (fun p hp => mem_upTo
            (hwf p (List.mem_filter.mp (List.mem_filter.mp hp).1).1).2.2.2.1)
          (fun k _ => hclass b k)
        rw [length_upTo] at hk
        exact hk)
  have hsum := Nat.add_le_add hP (Nat.le_trans hN (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_right _ (Nat.le_min.mpr
      ⟨Nat.le_trans (degZ_le_degYZ Q) hQ, degZ_le_div Q d W hd hW⟩))))
  rw [hsplit] at hsum
  exact hsum

end Slice
end Poly3

end Qsag

end
