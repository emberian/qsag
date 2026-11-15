module
/-
# Qsag.Coding.PersistentPairsBound — `[CWYZ26]` Lemmas 4.4 & 4.5 + Linear Persistence Lemma

Proves `IsPersistent`, `nonpersistent_common_agree_le` (`c ≤ B` for Claim 4.8),
`persistent_challenges_per_witness_le` (Lemma 4.4), and `persistent_pairs_card_le` (Lemma 4.5).
The `exceptional_` versions retain the selected candidate and exclude its polynomial
explanations; they do not require the whole received word to lack correlated agreement.
Nonempty instances and countermodels are in `PersistentPairsBoundTests`.
-/

public import Qsag.Coding.JohnsonSetSystem
public import Qsag.Coding.AffineIncidenceBound
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.SimpleRootStratification
import all Qsag.Coding.AffineIncidenceBound
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Math.Goldilocks

public section
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
  have h0 : line (zero : F) zero = zero := by
    apply UPoly.ext; show trimPoly [zero, zero] = []
    simp [trimPoly]
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
  show (evalHom z).toFun (sub p q) = _
  exact RingHom.map_sub _ p q

private theorem eval_mul_eq {R : Type} [LawfulCommRing R] [DecidableEq R]
    (p q : UPoly R) (z : R) : (mul p q).eval z = mul (p.eval z) (q.eval z) := by
  show (evalHom z).toFun (mul p q) = _
  exact RingHom.map_mul _ p q

private theorem uPoly_roots_le_natDeg (P : UPoly F) (hP : P ≠ zero) (zs : List F)
    (hNd : zs.Nodup) (hRoot : ∀ z ∈ zs, P.eval z = zero) :
    zs.length ≤ P.natDeg := by
  refine gs_formal_root_bound P.natDeg P.coeffs zs
    (by show _ ≤ P.coeffs.length - 1 + 1; omega)
    (exists_mem_ne_zero_of_coeffAt _ _ (lead_ne_zero hP)) hNd ?_
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
    | zero => rfl
    | succ k => cases k with
      | zero => rfl
      | succ k => show sub zero zero = zero; exact LawfulCommRing.sub_self zero
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
  | zero => rfl
  | succ k => cases k with
    | zero => rfl
    | succ k => show add (mul c₁ zero) (mul c₂ zero) = zero; constructive_ring

private theorem coeffs_length_of_mul_X_deg_le (d : Nat) (G_u H_u : UPoly F)
    (hH : H_u.natDeg ≤ d) (hEq : mul X G_u = H_u) : G_u.coeffs.length ≤ d := by
  if hG0 : G_u = zero then
    rw [hG0, coeffs_zero]; exact Nat.zero_le d
  else
    have hPos : 1 ≤ G_u.coeffs.length := by
      cases hc : G_u.coeffs with
      | nil => exact absurd (UPoly.ext hc) hG0
      | cons _ _ => exact Nat.succ_pos _
    have hLeadNe : coeffAt G_u.coeffs G_u.natDeg ≠ zero := lead_ne_zero hG0
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
              have hc : (C (neg c₂) : UPoly F) = neg (C c₂) := CHom.map_neg c₂
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
        have hLine10 : line (one : F) zero = one := by
          apply UPoly.ext; show trimPoly [one, zero] = trimPoly [one]
          simp [trimPoly, LawfulField.one_ne_zero]
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
        have hOfList : ∀ U : UPoly F, ofList U.coeffs = U := fun U => UPoly.ext U.trimmed
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
    JohnsonBound.johnson_set_system_card_le D fam memSet B (d + 1) hD hSize hInter hDen
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
