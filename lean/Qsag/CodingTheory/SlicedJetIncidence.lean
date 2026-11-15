module
/-
# Qsag.CodingTheory.SlicedJetIncidence — the non-excluded count, one challenge slope at a time

`[CWYZ26]` Claim 4.9 sends a simple root `(α, β, P)` of `R` to its jet
`(y, v, z) = (α + βT₀, β, P(T₀))` on the surface `R(T₀, Y, Z) = 0` in `F(T₀)³`, and Claim 4.8
counts nonpersistent triples on that surface by two rounds of incidence counting. The surface
is a cylinder over the plane curve `R(T₀, Y, Z) = 0`, and the coordinate `v = β` is a
challenge. Fixing `β` therefore leaves a plane curve and, for every `ζ ∈ D`, a plane equation
`A_ζ(Y, β, Z) = 0` of degree at most `2·d·h` that holds at a jet exactly when the triple
agrees with the fold at `ζ`. That is the input of `nonpersistent_curve_cover`, so one round of
incidence counting suffices and no space curve appears.

* `Poly3.jetEq`, `Poly3.jetEq_pt`, `Poly3.deg_jetEq_le`: the agreement equation in the jet
  ring, its value `s^(2d-1)·(P(ζ) - f(ζ) - (α + βζ)·g(ζ))` at the jet of a simple root, and
  its degree.
* `Poly3.slice_card_le`: for one `R` with `deg_Z R ≤ zb` and one `β`, at most
  `h·(|D|·zb·2dh/(A-B) + 1)` values of `α` carry a nonpersistent simple root with agreement
  at least `A`.
* `Poly3.nonExcluded_pairs_card_le`: for any `Q` with `deg_{Y,Z} Q ≤ h` and
  `deg_{1,1,d} Q ≤ W`, the non-excluded challenges that carry an accepted root of `Q` without
  a polynomial explanation number at most
  `ℓ·max{|S|, n(n-1)/2} + |S|·z·h·(|D|·z·2dh/(A-B) + 1)` with `z = min{h, W/d}`, which bounds
  both the number of multiplicity strata and the `Z`-degree of every curve leaf.

The second summand is linear in `|S|` where `[CWYZ26]` Lemma 4.7 has `4d²M²D³(n/(A-B))²`,
independent of `|S|`: the slope is enumerated instead of being eliminated by the second
incidence round. The characteristic hypothesis is that of `simple_root_of_hasse`.
-/

public import Qsag.CodingTheory.NonpersistentIncidenceBound
public import Qsag.CodingTheory.AffineIncidenceBound
import all Qsag.CodingTheory.NonpersistentIncidenceBound
import all Qsag.CodingTheory.PersistentPairsBound
import all Qsag.CodingTheory.JohnsonSetSystem
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.SylvesterResultant
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.HenselNumerators
import all Qsag.CodingTheory.UniversalHenselLift
import all Qsag.CodingTheory.SimpleRootStratification
import all Qsag.CodingTheory.AffineIncidenceBound
import all Qsag.CodingTheory.BivariateGauss
import all Qsag.CodingTheory.BivariateFactorSplit
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
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
      UPoly.natDeg_mul hp hps
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
    Nat.le_trans (wdeg_mapHom_mapHom_le (mapHom (scalK (F := F))) R) hR
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
    rw [e1, RingHom.map_add, RingHom.map_mul]; rfl
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
  show eval₂ (evalHom y) z ((mapHom (evalHom (C v))).toFun q) =
    eval₂ (eval₂Hom (evalHom y) v) z q
  rw [eval₂_mapHom]
  refine eval₂_congr _ _ (fun c => ?_) z q
  show (evalHom y).toFun (eval₂ (RingHom.id _) (C v) c) = eval₂ (evalHom y) v c
  rw [hom_eval₂, evalHom_apply, eval_C]
  exact eval₂_congr _ _ (fun _ => rfl) v c

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
    degFn_eval₂_le degFn_natDeg (RingHom.id _) natDeg (fun _ => Nat.le_refl _) (C v) 1
      (Nat.le_trans (Nat.le_of_eq (natDeg_C_eq v)) (Nat.zero_le 1)) (coeffAt q.coeffs k)
  have h2' : natDeg ((evalHom (C v)).toFun (coeffAt q.coeffs k)) ≤
      (coeffAt q.coeffs k).wdeg natDeg 1 := h2
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
      show hasse 1 R = zero
      rw [hRC]; exact hasse_one_C _
    rw [hz]; exact (affineLineHom α β P).map_zero
  have hnat : (liftK.toFun R).natDeg = R.natDeg := natDeg_mapHom _ map_of_inj R
  refine ⟨fun e => ?_, by omega⟩
  have h0 : (liftK.toFun R).natDeg = 0 := by rw [e]; rfl
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
    show eval₂ _ _ ((mapHom (mapHom (Frac.of (D := UPoly F)))).toFun R) = zero
    rw [eval₂_mapHom_mapHom]
    show (Frac.of (D := UPoly F)).toFun (evalAffineLine R α β P) = zero
    rw [hroot, RingHom.map_zero]
  have hmul : eval₂ (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))
      ((Frac.of (D := UPoly F)).toFun P) (liftK.toFun R) =
      mul ((Poly2.contY (liftK.toFun R)).eval ((Frac.of (D := UPoly F)).toFun (line α β)))
        (eval₂ (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))
          ((Frac.of (D := UPoly F)).toFun P) (Poly2.primY (liftK.toFun R))) := by
    conv => lhs; rw [hfac]
    rw [eval₂_mul, eval₂_C]; rfl
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (hmul.symm.trans hC0) with hc | hp
  · exfalso
    apply hsep
    apply Frac.of_injective
    rw [RingHom.map_zero]
    have e1 : (Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P) =
        eval₂ (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))
          ((Frac.of (D := UPoly F)).toFun P) (liftK.toFun (hasseZ 1 R)) :=
      (eval₂_mapHom_mapHom (Frac.of (D := UPoly F)) (hasseZ 1 R) (line α β) P).symm
    have e2 : liftK.toFun (hasseZ 1 R) = hasse 1 (liftK.toFun R) :=
      mapHom_hasse (mapHom (Frac.of (D := UPoly F))) 1 R
    have e3 : ∀ q : Poly2 (RatFunc F),
        eval₂ (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))
          ((Frac.of (D := UPoly F)).toFun P) q =
        ((mapHom (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))).toFun q).eval
          ((Frac.of (D := UPoly F)).toFun P) := fun q => by
      show _ = eval₂ (RingHom.id _) _ ((mapHom _).toFun q)
      rw [eval₂_mapHom]
      exact eval₂_congr _ _ (fun _ => rfl) _ q
    have e4 : (mapHom (evalHom ((Frac.of (D := UPoly F)).toFun (line α β)))).toFun
        (liftK.toFun R) = zero := ext_coeffAt (fun k => by
      have hk : coeffAt (liftK.toFun R).coeffs k =
          mul (Poly2.contY (liftK.toFun R)) (coeffAt (Poly2.primY (liftK.toFun R)).coeffs k) := by
        conv => lhs; rw [hfac]
        exact coeffAt_C_mul _ _ k
      rw [coeffAt_mapHom, coeffs_zero, coeffAt_nil, hk, RingHom.map_mul, evalHom_apply, hc,
        LawfulCommRing.zero_mul])
    rw [e1, e2, e3, mapHom_hasse, e4, hasse_one_zero]
    rfl
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
    have h2 : Poly2.tdeg (liftK.toFun R) ≤ R.degYZ := wdeg_mapHom_mapHom_le _ R
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
        have hnat : (liftK.toFun R).natDeg = R.natDeg := natDeg_mapHom _ map_of_inj R
        rw [hnat] at h1
        exact Nat.le_trans h1 hz
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
    have hz : R.degZ = 0 := by rw [h0]; rfl
    rw [hz]; exact Nat.zero_le _
  else
    have hl := le_wdeg (fun q : UPoly (UPoly F) => q.wdeg natDeg 1) d R R.natDeg (lead_ne_zero h0)
    have hl' : d * R.natDeg ≤ W :=
      Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _) hl) hW
    rw [Nat.mul_comm] at hl'
    exact (Nat.le_div_iff_mul_le hd).mpr hl'

theorem degZ_le_degYZ (Q : Poly3 F) : Q.degZ ≤ Q.degYZ := by
  if h : Q = zero then
    show Q.coeffs.length - 1 ≤ _
    rw [h, coeffs_zero]; exact Nat.zero_le _
  else
    have hl := le_wdeg UPoly.natDeg 1 Q Q.natDeg (lead_ne_zero h)
    show Q.natDeg ≤ Q.wdeg UPoly.natDeg 1
    omega

theorem deg11d_hasseZ_le (d k : Nat) (Q : Poly3 F) : (hasseZ k Q).deg11d d ≤ Q.deg11d d :=
  Nat.le_trans (wdeg_hasse_le (fun q : UPoly (UPoly F) => q.wdeg natDeg 1)
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
