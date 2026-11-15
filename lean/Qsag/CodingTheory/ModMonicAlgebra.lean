module
/-
# Qsag.CodingTheory.ModMonicAlgebra — Monic Quotient Algebras & Double-Root Derivative Vanishing

Constructive quotient ring `ModMonic M` (`R[W]/(M(W))` for monic `M` of degree `≥ 1`,
`0 Classical.choice`):
* `SylElim.wdeg_divModLead_rem_le`: unit-leading division `divModLead` preserves weighted degrees.
* `ModMonic M`: free `R`-algebra `R[W]/(M)` with injective `modInl : R → ModMonic M` and canonical
  root `modGen M` of `M`.
* `sylResDeriv_eq_zero_of_common_factor_ge_two`: if a monic `G` of degree `≥ 2` divides both `C1`
  and `P0` in `R[Z]`, then `sylResDeriv m N C1 P0 1 = 0` in `R` (proved via the 2-step free tower
  `R ↪ R[T₁]/(G) ↪ R₁[T₂]/(G₁)`).
-/

public import Qsag.CodingTheory.SylvesterDeriv
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.MatrixDet
import all Qsag.CodingTheory.SylvesterElimination
import all Qsag.CodingTheory.SylvesterDeriv
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false
open CommRingOps RoundPoly

namespace SylElim

private theorem ite_pos {α : Type} {p : Prop} [Decidable p] (hp : p) {a b : α} :
    (if p then a else b) = a := by
  split
  · rfl
  · next hn => exact absurd hp hn

private theorem ite_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) {a b : α} :
    (if p then a else b) = b := by
  split
  · next hp => exact absurd hp hnp
  · rfl

/-! ## Weighted-degree preservation of `divModLead` -/

section WdegDiv
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
open UPoly

theorem wdeg_divModLead_rem_le {w : R → Nat} (hw : DegFn w)
    (A : UPoly R) (m T : Nat) (c_inv : R)
    (hm : 1 ≤ m) (hAdeg : A.natDeg ≤ m) (hInv : mul c_inv (coeffAt A.coeffs m) = one)
    (hcinv : w c_inv = 0) (hAw : A.wdeg w 1 ≤ m)
    (P : UPoly R) (hPw : P.wdeg w 1 ≤ T) :
    (divModLead A m c_inv P).2.wdeg w 1 ≤ T := by
  have hwSub : ∀ X Y : UPoly R, X.wdeg w 1 ≤ T → Y.wdeg w 1 ≤ T → (sub X Y).wdeg w 1 ≤ T := by
    intro X Y hX hY
    have hD := UPoly.degFn_wdeg hw 1
    rw [LawfulCommRing.sub_eq_add_neg]
    have h1 := hD.add_le X (neg Y)
    have h2 := Nat.le_trans (hD.neg_le Y) hY
    if hmxy : X.wdeg w 1 ≤ (neg Y).wdeg w 1 then
      rw [Nat.max_eq_right hmxy] at h1; exact Nat.le_trans h1 h2
    else
      rw [Nat.max_eq_left (by omega)] at h1; exact Nat.le_trans h1 hX
  have aux : ∀ (fuel : Nat) (P : UPoly R), P.natDeg < fuel → P.wdeg w 1 ≤ T →
      (divModLeadAux A m c_inv fuel P).2.wdeg w 1 ≤ T := by
    intro fuel; induction fuel with
    | zero => intros _ h _; exfalso; omega
    | succ fuel ih =>
      intro P hFuel hPT
      unfold divModLeadAux
      if hlt : P.natDeg < m then
        rw [ite_pos hlt]; exact hPT
      else
        rw [ite_neg hlt]
        have hP0 : P ≠ zero := fun e => by
          rw [e] at hlt; have : (zero : UPoly R).natDeg = 0 := by show [].length - 1 = 0; rfl
          omega
        have hLeadW : w P.lead + 1 * P.natDeg ≤ T :=
          Nat.le_trans (le_wdeg w 1 P P.natDeg (lead_ne_zero hP0)) hPT
        let qTop := mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))
        let P' := sub P (mul qTop A)
        have hqTopW : qTop.wdeg w 1 ≤ T - m := by
          apply wdeg_le; intro k hk
          dsimp only [qTop] at hk ⊢
          rw [coeffAt_C_mul, coeffAt_monom] at hk ⊢
          if hEq : k = P.natDeg - m then
            subst hEq; rw [ite_pos rfl, LawfulCommRing.mul_one] at hk ⊢
            have hwMul := hw.mul_le P.lead c_inv
            unfold lead at hwMul hLeadW
            rw [hcinv] at hwMul; omega
          else
            rw [ite_neg hEq, LawfulCommRing.mul_zero] at hk; exact absurd rfl hk
        have hMulW : (mul qTop A).wdeg w 1 ≤ T := by
          have h1 := (UPoly.degFn_wdeg hw 1).mul_le qTop A
          omega
        have hCancel : ∀ k, P.natDeg ≤ k → coeffAt P'.coeffs k = zero := by
          intro k hk
          dsimp only [P', qTop]
          have hqA : mul (mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))) A =
              mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (mul (monom (P.natDeg - m)) A) := by
            constructive_ring
          rw [coeffAt_sub, hqA, coeffAt_C_mul, coeffAt_monom_mul, ite_pos (by omega)]
          if hEq : k = P.natDeg then
            subst hEq; rw [show P.natDeg - (P.natDeg - m) = m by omega]
            have h1 : mul (mul (coeffAt P.coeffs P.natDeg) c_inv) (coeffAt A.coeffs m) =
                mul (coeffAt P.coeffs P.natDeg) (mul c_inv (coeffAt A.coeffs m)) := by constructive_ring
            rw [h1, hInv, LawfulCommRing.mul_one, LawfulCommRing.sub_self]
          else
            rw [P.coeffAt_eq_zero_of_natDeg_lt (by omega),
              A.coeffAt_eq_zero_of_natDeg_lt (by omega), LawfulCommRing.mul_zero, LawfulCommRing.sub_self]
        have hDegP' : P'.natDeg < fuel := by
          have hle := natDeg_le_of_coeffAt P' (P.natDeg - 1) fun k hk => hCancel k (by omega)
          omega
        exact ih P' hDegP' (hwSub P (mul qTop A) hPT hMulW)
  exact aux (P.natDeg + 1) P (Nat.lt_succ_self _) hPw

end WdegDiv

/-! ## Monic Quotient Algebra `ModMonic M = R[W]/(M)` -/

structure MonicPoly (R : Type) [LawfulCommRing R] [DecidableEq R] where
  poly : UPoly R
  deg : Nat
  deg_pos : 1 ≤ deg
  natDeg_le : poly.natDeg ≤ deg
  coeff_deg : coeffAt poly.coeffs deg = one

section ModMonicRing
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
open UPoly

def remM (M : MonicPoly R) (P : UPoly R) : UPoly R :=
  (divModLead M.poly M.deg one P).2

def quotM (M : MonicPoly R) (P : UPoly R) : UPoly R :=
  (divModLead M.poly M.deg one P).1

theorem quotM_remM_spec (M : MonicPoly R) (P : UPoly R) :
    P = add (mul (quotM M P) M.poly) (remM M P) ∧ (remM M P).natDeg < M.deg := by
  have hInv : mul (one : R) (coeffAt M.poly.coeffs M.deg) = one := by
    rw [M.coeff_deg, LawfulCommRing.one_mul]
  exact divModLead_spec M.poly M.deg one M.deg_pos M.natDeg_le hInv P

theorem eq_zero_of_mul_monic_lt (M : MonicPoly R) {Q : UPoly R}
    (hLt : (mul Q M.poly).natDeg < M.deg) : Q = zero := by
  apply Decidable.byContradiction; intro hQ0
  let u := Q.natDeg
  have hZero : coeffAt (mul Q M.poly).coeffs (u + M.deg) = zero :=
    (mul Q M.poly).coeffAt_eq_zero_of_natDeg_lt (by omega)
  if hM0 : M.poly = zero then
    have h10 : (one : R) = zero := by
      rw [← M.coeff_deg, hM0, coeffs_zero, coeffAt_nil]
    have hQl : Q.lead = zero := by
      rw [← LawfulCommRing.mul_one Q.lead, h10, LawfulCommRing.mul_zero]
    exact lead_ne_zero hQ0 hQl
  else
    have hMdeg : M.poly.natDeg = M.deg := by
      apply Nat.le_antisymm M.natDeg_le
      apply Decidable.byContradiction; intro hNot
      have hz := M.poly.coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hNot)
      rw [M.coeff_deg] at hz
      exact lead_ne_zero hQ0 (by
        rw [← LawfulCommRing.mul_one Q.lead, hz, LawfulCommRing.mul_zero])
    have hTop := (coeffAt_mul_top Q M.poly).2
    unfold lead at hTop
    rw [hMdeg, M.coeff_deg, LawfulCommRing.mul_one] at hTop
    rw [hTop] at hZero
    exact lead_ne_zero hQ0 hZero

theorem remM_eq_of_sub_mul (M : MonicPoly R) {P R0 Q : UPoly R}
    (hSub : sub P R0 = mul Q M.poly) (hDeg : R0.natDeg < M.deg) :
    remM M P = R0 := by
  obtain ⟨hDiv, hRemDeg⟩ := quotM_remM_spec M P
  have hDiff : sub (remM M P) R0 = mul (sub Q (quotM M P)) M.poly := by
    have h1 : remM M P = sub P (mul (quotM M P) M.poly) := by
      conv => rhs; lhs; rw [hDiv]
      constructive_ring
    rw [h1]
    have h2 : sub (sub P (mul (quotM M P) M.poly)) R0 =
        sub (sub P R0) (mul (quotM M P) M.poly) := by constructive_ring
    rw [h2, hSub]; constructive_ring
  have hDiffDeg : (mul (sub Q (quotM M P)) M.poly).natDeg < M.deg := by
    rw [← hDiff, LawfulCommRing.sub_eq_add_neg]
    have h1 := natDeg_add_le (remM M P) (neg R0)
    have hNeg : (neg R0).natDeg ≤ R0.natDeg :=
      natDeg_le_of_coeffAt _ _ fun k hk => by
        rw [coeffAt_neg, R0.coeffAt_eq_zero_of_natDeg_lt hk, LawfulCommRing.neg_zero]
    omega
  have hQeq := eq_zero_of_mul_monic_lt M hDiffDeg
  rw [hQeq, LawfulCommRing.zero_mul] at hDiff
  exact LawfulCommRing.sub_eq_zero_iff.mp hDiff

theorem remM_of_lt (M : MonicPoly R) {P : UPoly R} (hP : P.natDeg < M.deg) :
    remM M P = P :=
  remM_eq_of_sub_mul M (Q := zero)
    (by rw [LawfulCommRing.sub_self, LawfulCommRing.zero_mul]) hP

@[ext]
structure ModMonic (M : MonicPoly R) where
  rep : UPoly R
  reduced : rep.natDeg < M.deg
  deriving DecidableEq

namespace ModMonic

theorem natDeg_zero_lt (M : MonicPoly R) : (zero : UPoly R).natDeg < M.deg := by
  have : (zero : UPoly R).natDeg = 0 := by show [].length - 1 = 0; rfl
  have := M.deg_pos; omega

theorem natDeg_C_lt (M : MonicPoly R) (c : R) : (C c : UPoly R).natDeg < M.deg := by
  have hc0 : (C c : UPoly R).natDeg = 0 :=
    Nat.le_zero.mp (natDeg_le_of_coeffAt _ 0 fun k hk => by
      cases k with
      | zero => omega
      | succ k => exact coeffAt_C_succ c k)
  have := M.deg_pos; omega

theorem natDeg_add_lt (M : MonicPoly R) {a b : UPoly R}
    (ha : a.natDeg < M.deg) (hb : b.natDeg < M.deg) : (add a b).natDeg < M.deg := by
  have h := natDeg_add_le a b; omega

theorem natDeg_neg_lt (M : MonicPoly R) {a : UPoly R}
    (ha : a.natDeg < M.deg) : (neg a).natDeg < M.deg := by
  have h : (neg a).natDeg ≤ a.natDeg :=
    natDeg_le_of_coeffAt _ _ fun k hk => by
      rw [coeffAt_neg, a.coeffAt_eq_zero_of_natDeg_lt hk, LawfulCommRing.neg_zero]
  omega

instance (M : MonicPoly R) : LawfulCommRing (ModMonic M) where
  zero := ⟨zero, natDeg_zero_lt M⟩
  one := ⟨one, by rw [one_eq_C]; exact natDeg_C_lt M one⟩
  add a b := ⟨add a.rep b.rep, natDeg_add_lt M a.reduced b.reduced⟩
  mul a b := ⟨remM M (mul a.rep b.rep), (quotM_remM_spec M _).2⟩
  neg a := ⟨neg a.rep, natDeg_neg_lt M a.reduced⟩
  sub a b := ⟨sub a.rep b.rep, by
    rw [LawfulCommRing.sub_eq_add_neg]
    exact natDeg_add_lt M a.reduced (natDeg_neg_lt M b.reduced)⟩
  add_assoc a b c := by apply ModMonic.ext; exact LawfulCommRing.add_assoc _ _ _
  add_comm a b := by apply ModMonic.ext; exact LawfulCommRing.add_comm _ _
  zero_add a := by apply ModMonic.ext; exact LawfulCommRing.zero_add _
  add_zero a := by apply ModMonic.ext; exact LawfulCommRing.add_zero _
  add_left_neg a := by apply ModMonic.ext; exact LawfulCommRing.add_left_neg _
  sub_eq_add_neg a b := by apply ModMonic.ext; exact LawfulCommRing.sub_eq_add_neg _ _
  mul_comm a b := by apply ModMonic.ext; dsimp; rw [LawfulCommRing.mul_comm]
  one_mul a := by
    apply ModMonic.ext; dsimp
    rw [LawfulCommRing.one_mul, remM_of_lt M a.reduced]
  mul_one a := by
    apply ModMonic.ext; dsimp
    rw [LawfulCommRing.mul_one, remM_of_lt M a.reduced]
  left_distrib a b c := by
    apply ModMonic.ext; dsimp
    rw [LawfulCommRing.left_distrib]
    obtain ⟨hB, hBd⟩ := quotM_remM_spec M (mul a.rep b.rep)
    obtain ⟨hC, hCd⟩ := quotM_remM_spec M (mul a.rep c.rep)
    refine remM_eq_of_sub_mul M (Q := add (quotM M (mul a.rep b.rep)) (quotM M (mul a.rep c.rep)))
      ?_ (natDeg_add_lt M hBd hCd)
    conv => lhs; lhs; rw [hB, hC]
    constructive_ring
  right_distrib a b c := by
    apply ModMonic.ext; dsimp
    rw [LawfulCommRing.right_distrib]
    obtain ⟨hA, hAd⟩ := quotM_remM_spec M (mul a.rep c.rep)
    obtain ⟨hB, hBd⟩ := quotM_remM_spec M (mul b.rep c.rep)
    refine remM_eq_of_sub_mul M (Q := add (quotM M (mul a.rep c.rep)) (quotM M (mul b.rep c.rep)))
      ?_ (natDeg_add_lt M hAd hBd)
    conv => lhs; lhs; rw [hA, hB]
    constructive_ring
  mul_assoc a b c := by
    apply ModMonic.ext; dsimp
    obtain ⟨hAB, _⟩ := quotM_remM_spec M (mul a.rep b.rep)
    obtain ⟨hBC, _⟩ := quotM_remM_spec M (mul b.rep c.rep)
    obtain ⟨hR, hRd⟩ := quotM_remM_spec M (mul a.rep (remM M (mul b.rep c.rep)))
    refine remM_eq_of_sub_mul M
      (Q := sub (add (quotM M (mul a.rep (remM M (mul b.rep c.rep)))) (mul a.rep (quotM M (mul b.rep c.rep))))
        (mul (quotM M (mul a.rep b.rep)) c.rep)) ?_ hRd
    have hEqABC : mul (add (mul (quotM M (mul a.rep b.rep)) M.poly) (remM M (mul a.rep b.rep))) c.rep =
        mul a.rep (add (mul (quotM M (mul b.rep c.rep)) M.poly) (remM M (mul b.rep c.rep))) := by
      rw [← hAB, ← hBC, LawfulCommRing.mul_assoc]
    have hRemEq : mul (remM M (mul a.rep b.rep)) c.rep =
        sub (mul a.rep (add (mul (quotM M (mul b.rep c.rep)) M.poly) (remM M (mul b.rep c.rep))))
          (mul (mul (quotM M (mul a.rep b.rep)) M.poly) c.rep) := by
      rw [← hEqABC]; constructive_ring
    rw [hRemEq]
    conv => lhs; lhs; lhs; rhs; rhs; rw [hR]
    constructive_ring

instance [NontrivialRing R] (M : MonicPoly R) : NontrivialRing (ModMonic M) where
  one_ne_zero h := by
    have hRep : (one : UPoly R) = zero := congrArg ModMonic.rep h
    have hc := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) hRep
    rw [one_eq_C, coeffAt_C_zero, coeffs_zero, coeffAt_nil] at hc
    exact NontrivialRing.one_ne_zero hc

def modQuotHom (M : MonicPoly R) : RingHom (UPoly R) (ModMonic M) where
  toFun P := ⟨remM M P, (quotM_remM_spec M P).2⟩
  map_zero := by apply ModMonic.ext; exact remM_of_lt M (natDeg_zero_lt M)
  map_one := by
    apply ModMonic.ext
    exact remM_of_lt M (by rw [one_eq_C]; exact natDeg_C_lt M one)
  map_add A B := by
    apply ModMonic.ext; dsimp
    obtain ⟨hA, hAd⟩ := quotM_remM_spec M A
    obtain ⟨hB, hBd⟩ := quotM_remM_spec M B
    refine remM_eq_of_sub_mul M (Q := add (quotM M A) (quotM M B)) ?_ (natDeg_add_lt M hAd hBd)
    conv => lhs; lhs; rw [hA, hB]
    constructive_ring
  map_mul A B := by
    apply ModMonic.ext; dsimp
    obtain ⟨hA, _⟩ := quotM_remM_spec M A
    obtain ⟨hB, _⟩ := quotM_remM_spec M B
    obtain ⟨hR, hRd⟩ := quotM_remM_spec M (mul (remM M A) (remM M B))
    refine remM_eq_of_sub_mul M
      (Q := add (add (mul (quotM M A) (mul (quotM M B) M.poly))
          (add (mul (quotM M A) (remM M B)) (mul (remM M A) (quotM M B))))
        (quotM M (mul (remM M A) (remM M B)))) ?_ hRd
    conv => lhs; lhs; rw [hA, hB]
    conv => lhs; lhs; rhs; rhs; rw [hR]
    constructive_ring

def modInl (M : MonicPoly R) : RingHom R (ModMonic M) :=
  (modQuotHom M).comp CHom

theorem modInl_inj (M : MonicPoly R) {r : R} (h : (modInl M).toFun r = zero) : r = zero := by
  have hRep : remM M (C r) = zero := congrArg ModMonic.rep h
  rw [remM_of_lt M (natDeg_C_lt M r)] at hRep
  have hc := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) hRep
  rwa [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at hc

def modGen (M : MonicPoly R) : ModMonic M :=
  (modQuotHom M).toFun X

theorem eval_mapHom_modInl (M : MonicPoly R) (P : UPoly R) :
    ((mapHom (modInl M)).toFun P).eval (modGen M) = (modQuotHom M).toFun P := by
  show eval₂ (RingHom.id _) (modGen M) ((mapHom (modInl M)).toFun P) = _
  rw [eval₂_mapHom]
  have hEqFun : ∀ c : R, ((RingHom.id (ModMonic M)).comp (modInl M)).toFun c =
      ((modQuotHom M).comp CHom).toFun c := fun _ => rfl
  show evalCoeffs (P.coeffs.map ((RingHom.id (ModMonic M)).comp (modInl M)).toFun) (modGen M) = _
  have hMap : P.coeffs.map ((RingHom.id (ModMonic M)).comp (modInl M)).toFun =
      P.coeffs.map ((modQuotHom M).comp CHom).toFun := List.map_congr_left fun c _ => hEqFun c
  rw [hMap]
  change eval₂ ((modQuotHom M).comp CHom) ((modQuotHom M).toFun X) P = (modQuotHom M).toFun P
  have hIdP : P = eval₂ CHom X P := by
    conv => lhs; rw [← ofList_coeffs P]
    generalize P.coeffs = l
    induction l with
    | nil => rfl
    | cons c cs ih =>
      show ofList (c :: cs) = add (C c) (mul X _)
      rw [ofList_cons, ← ih]; rfl
  conv => rhs; rw [hIdP]
  exact (hom_eval₂ (modQuotHom M) CHom X P).symm

theorem modQuotHom_self_eq_zero (M : MonicPoly R) : (modQuotHom M).toFun M.poly = zero := by
  apply ModMonic.ext; dsimp [modQuotHom]
  exact remM_eq_of_sub_mul M (Q := one)
    (by rw [LawfulCommRing.sub_zero, LawfulCommRing.one_mul]) (natDeg_zero_lt M)

theorem eval_modGen_eq_zero (M : MonicPoly R) :
    ((mapHom (modInl M)).toFun M.poly).eval (modGen M) = zero := by
  rw [eval_mapHom_modInl, modQuotHom_self_eq_zero]

end ModMonic

/-! ## `d_G ≥ 2` Common-Factor Vanishing of `sylResDeriv` -/

theorem sylResDeriv_eq_zero_of_common_factor_ge_two {m N d_G : Nat}
    {C1 P0 G Q_C Q_P : UPoly R}
    (hdG : 2 ≤ d_G) (hdGm : d_G ≤ m) (hC1 : C1.natDeg ≤ m) (hP0 : P0.natDeg ≤ N)
    (hGdeg : G.natDeg ≤ d_G) (hGmon : coeffAt G.coeffs d_G = one)
    (hC1fac : C1 = mul G Q_C) (hQCdeg : Q_C.natDeg ≤ m - d_G)
    (hP0fac : P0 = mul G Q_P) :
    sylResDeriv m N C1 P0 one = zero := by
  let M1 : MonicPoly R := ⟨G, d_G, by omega, hGdeg, hGmon⟩
  let φ1 := ModMonic.modInl M1
  let T1 := ModMonic.modGen M1
  let G_1 := (mapHom φ1).toFun G
  have hG1root : G_1.eval T1 = zero := ModMonic.eval_modGen_eq_zero M1
  obtain ⟨hG1div, hG1deg_raw⟩ := divXSub_spec G_1 T1
  have hC0_1 : (C (zero : ModMonic M1) : UPoly (ModMonic M1)) = zero := by
    rw [← CHom_apply]; exact CHom.map_zero
  rw [hG1root, hC0_1, LawfulCommRing.zero_add] at hG1div
  let G1 := divXSub G_1 T1
  have hG1_le : G1.natDeg ≤ d_G - 1 := by
    have := natDeg_mapHom_le φ1 G; omega
  have hG1_mon : coeffAt G1.coeffs (d_G - 1) = one := by
    have hTop : coeffAt G_1.coeffs d_G = one := by
      dsimp only [G_1]; rw [coeffAt_mapHom, hGmon, φ1.map_one]
    have hExpand : mul (sub X (C T1)) G1 = sub (mul X G1) (mul (C T1) G1) := by constructive_ring
    obtain ⟨d', hd'⟩ : ∃ d', d_G = d' + 1 := ⟨d_G - 1, by omega⟩
    rw [hG1div, hExpand, hd', coeffAt_sub, coeffAt_X_mul_succ, coeffAt_C_mul,
      G1.coeffAt_eq_zero_of_natDeg_lt (by omega), LawfulCommRing.mul_zero,
      LawfulCommRing.sub_zero] at hTop
    rwa [show d_G - 1 = d' by omega]
  let C1_1 := (mapHom φ1).toFun C1
  let P0_1 := (mapHom φ1).toFun P0
  let QC_1 := (mapHom φ1).toFun Q_C
  let QP_1 := (mapHom φ1).toFun Q_P
  have hC1_1_eq : C1_1 = mul (sub X (C T1)) (mul G1 QC_1) := by
    dsimp only [C1_1, QC_1]
    rw [hC1fac, RingHom.map_mul]; change mul G_1 QC_1 = _
    rw [hG1div, LawfulCommRing.mul_assoc]
  have hP0_1_root : P0_1.eval T1 = zero := by
    dsimp only [P0_1]
    rw [hP0fac, RingHom.map_mul]; change ((evalHom T1).toFun (mul G_1 QP_1)) = zero
    rw [RingHom.map_mul, evalHom_apply, hG1root, LawfulCommRing.zero_mul]
  have hG1QC_deg : (mul G1 QC_1).natDeg ≤ m - 1 := by
    have h1 := natDeg_mul_le G1 QC_1
    have h2 := natDeg_mapHom_le φ1 Q_C
    omega
  have hP0_1_deg : P0_1.natDeg ≤ N := Nat.le_trans (natDeg_mapHom_le φ1 P0) hP0
  have hOne_deg : (one : UPoly (ModMonic M1)).natDeg ≤ N := by
    rw [natDeg_one]; exact Nat.zero_le N
  have hStep1 : φ1.toFun (sylResDeriv m N C1 P0 one) = sylRes (m - 1) N (mul G1 QC_1) P0_1 := by
    rw [map_sylResDeriv φ1, RingHom.map_one]
    change sylResDeriv m N C1_1 P0_1 one = _
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm', show m' + 1 - 1 = m' by omega] at hG1QC_deg ⊢
    rw [hC1_1_eq, sylResDeriv_of_factor m' N T1 (mul G1 QC_1) P0_1 one hG1QC_deg hP0_1_deg hOne_deg hP0_1_root,
      one_eq_C, eval_C, LawfulCommRing.one_mul]
  let M2 : MonicPoly (ModMonic M1) := ⟨G1, d_G - 1, by omega, hG1_le, hG1_mon⟩
  let φ2 := ModMonic.modInl M2
  let T2 := ModMonic.modGen M2
  have hG1_2_root : ((mapHom φ2).toFun G1).eval T2 = zero := ModMonic.eval_modGen_eq_zero M2
  have hStep2 : φ2.toFun (sylRes (m - 1) N (mul G1 QC_1) P0_1) = zero := by
    rw [map_sylRes φ2]
    refine sylRes_eq_zero_of_common_root (ζ := T2) (by omega)
      (Nat.le_trans (natDeg_mapHom_le φ2 _) hG1QC_deg)
      (Nat.le_trans (natDeg_mapHom_le φ2 _) hP0_1_deg) ?_ ?_
    · rw [RingHom.map_mul]; change (evalHom T2).toFun _ = zero
      rw [RingHom.map_mul, evalHom_apply, hG1_2_root, LawfulCommRing.zero_mul]
    · dsimp only [P0_1]
      rw [hP0fac, RingHom.map_mul]; change ((mapHom φ2).toFun (mul G_1 QP_1)).eval T2 = zero
      rw [hG1div, RingHom.map_mul, RingHom.map_mul]
      change (evalHom T2).toFun _ = zero
      rw [RingHom.map_mul, RingHom.map_mul, evalHom_apply ((mapHom φ2).toFun G1), hG1_2_root,
        LawfulCommRing.mul_zero, LawfulCommRing.zero_mul]
  apply ModMonic.modInl_inj M1
  apply ModMonic.modInl_inj M2
  rw [hStep1, hStep2]

end ModMonicRing
end SylElim

namespace ModMonicAlgebraTests
open UPoly SylElim

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- Double common factor `G = X² - 1` (`d_G = 2`) dividing `C1 = G` and `P0 = G`:
    `sylResDeriv 2 2 G G 1 = 0`. -/
theorem inhabited_sylResDeriv_eq_zero_of_common_factor_ge_two :
    ∃ (m N d_G : Nat) (C1 P0 G Q_C Q_P : UPoly Goldilocks),
      2 ≤ d_G ∧ d_G ≤ m ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧
      G.natDeg ≤ d_G ∧ coeffAt G.coeffs d_G = one ∧
      C1 = mul G Q_C ∧ Q_C.natDeg ≤ m - d_G ∧ P0 = mul G Q_P ∧
      sylResDeriv m N C1 P0 one = zero :=
  let G : UPoly Goldilocks := ofList [neg (g 1), g 0, g 1]
  ⟨2, 2, 2, mul G one, mul G one, G, one, one,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, by decide +kernel⟩

/-- `#tooth`: dropping `2 ≤ d_G` (`d_G = 1`, simple common factor `G = X - 3` of `C1 = (X - 3)(X - 5)`
    and `P0 = X - 3`) makes `sylResDeriv 2 1 C1 P0 1 = -2 ≠ 0`! -/
theorem tooth_sylResDeriv_nonzero_for_deg_one_gcd :
    ∃ (m N d_G : Nat) (C1 P0 G Q_C Q_P : UPoly Goldilocks),
      1 ≤ d_G ∧ d_G ≤ m ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧
      G.natDeg ≤ d_G ∧ coeffAt G.coeffs d_G = one ∧
      C1 = mul G Q_C ∧ Q_C.natDeg ≤ m - d_G ∧ P0 = mul G Q_P ∧
      sylResDeriv m N C1 P0 one ≠ zero :=
  let G : UPoly Goldilocks := ofList [neg (g 3), g 1]
  let QC : UPoly Goldilocks := ofList [neg (g 5), g 1]
  ⟨2, 1, 1, mul G QC, mul G one, G, QC, one,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, by decide +kernel⟩

#verify_constructive SylElim.wdeg_divModLead_rem_le SylElim.ModMonic.eval_modGen_eq_zero
#verify_constructive SylElim.sylResDeriv_eq_zero_of_common_factor_ge_two
#verify_constructive inhabited_sylResDeriv_eq_zero_of_common_factor_ge_two tooth_sylResDeriv_nonzero_for_deg_one_gcd
#tooth_pair SylElim.sylResDeriv_eq_zero_of_common_factor_ge_two vs tooth_sylResDeriv_nonzero_for_deg_one_gcd
#verify_inhabited SylElim.sylResDeriv_eq_zero_of_common_factor_ge_two inhabited_sylResDeriv_eq_zero_of_common_factor_ge_two

end ModMonicAlgebraTests
end Qsag
end
