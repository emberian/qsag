module
/-
# Qsag.CodingTheory.ShearedCurveGcd — Dynamic Euclidean Curve Root Decomposition

Dynamic Euclidean `xgcd` and root extraction over bivariate curve factors (`0 Classical.choice`,
`0` irreducible factorization):
* `modUnitOrSplit`: every element of `ModMonic (monicFY E ...)` is `0`, a unit, or yields a proper
  `Y`-primitive split `E = mul E₁ E₂` in `Poly2 E_fld` with `tdeg E₁ + tdeg E₂ = tdeg E`.
* `d5_xgcd_mod`: dynamic Euclidean `xgcd` in `(ModMonic (monicFY E ...))[Z]`.
* `curve_leaf_root_decomp`: dynamically splits any `Y`-primitive factor `E ∈ E_fld[U][W]` of
  `sylRes h_C H₀ (embedUZ C₁) P₀` into `Y`-primitive leaves `E_j` (`∑ tdeg E_j = tdeg E`) on each
  of which either `E_j ∣ g₁` or `(CoprimeZ E_j g₁ ∧ ∃ ζ ∈ R_{E_j}, C₁(ζ) = 0 ∧ P₀(ζ) = 0)`.
-/

public import Qsag.CodingTheory.BivariateFactorSplit
public import Qsag.CodingTheory.ModMonicAlgebra
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.SylvesterResultant
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.BivariateGauss
import all Qsag.CodingTheory.BivariateFactorSplit
import all Qsag.CodingTheory.MatrixDet
import all Qsag.CodingTheory.SylvesterElimination
import all Qsag.CodingTheory.SylvesterDeriv
import all Qsag.CodingTheory.ModMonicAlgebra
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false
open CommRingOps RoundPoly

namespace SylElim
section CurveDecomp
variable {E_fld : Type} [LawfulField E_fld] [DecidableEq E_fld]
open UPoly Poly2

local instance : NoZeroDivisors E_fld := LawfulField.toNoZeroDivisors E_fld

/-- Nonzero `Y`-primitive polynomial of total degree `≥ 1` has `Z`-degree `≥ 1`. -/
theorem primY_natDeg_pos {E : Poly2 E_fld} (hPrim : IsPrimY E) (hTdeg : 1 ≤ tdeg E) :
    1 ≤ E.natDeg := by
  if h0 : E.natDeg = 0 then
    exfalso
    have hEC : E = C (coeffAt E.coeffs 0) := by
      apply ext_coeffAt; intro k
      cases k with
      | zero => rw [coeffAt_C_zero]
      | succ k => rw [coeffAt_C_succ]; exact E.coeffAt_eq_zero_of_natDeg_lt (by omega)
    have hDivAll : ∀ k, ∃ q, coeffAt E.coeffs k = mul (coeffAt E.coeffs 0) q := fun k => by
      cases k with
      | zero => exact ⟨one, (LawfulCommRing.mul_one _).symm⟩
      | succ k =>
        rw [E.coeffAt_eq_zero_of_natDeg_lt (by omega)]
        exact ⟨zero, (LawfulCommRing.mul_zero _).symm⟩
    have hcDeg0 := hPrim.2 (coeffAt E.coeffs 0) hDivAll
    have ht0 : tdeg E = 0 := by rw [hEC, tdeg_C, hcDeg0]
    omega
  else omega

/-- Monic normalization of `liftFY.toFun E ∈ E_fld(Y)[Z]` for `E : Poly2 E_fld` with `1 ≤ E.natDeg`. -/
def monicFY (E : Poly2 E_fld) (hPrim : IsPrimY E) (hDeg : 1 ≤ E.natDeg) :
    MonicPoly (RatFunc E_fld) :=
  let E_L := liftFY.toFun E
  have hENe : E_L ≠ zero := fun e => hPrim.1 (liftFY_inj E e)
  have hDegEq : E_L.natDeg = E.natDeg :=
    UPoly.natDeg_mapHom _ (fun x hx => Frac.of_injective (hx.trans (Frac.of (D := UPoly E_fld)).map_zero.symm)) E
  { poly := mul (C (LawfulField.inv E_L.lead)) E_L
    deg := E.natDeg
    deg_pos := hDeg
    natDeg_le := by
      have h := natDeg_mul_le (C (LawfulField.inv E_L.lead)) E_L
      have hC0 : (C (LawfulField.inv E_L.lead)).natDeg = 0 := by
        apply Nat.le_zero.mp; apply natDeg_le_of_coeffAt; intro k hk
        cases k with | zero => omega | succ k => exact coeffAt_C_succ _ k
      omega
    coeff_deg := by
      rw [coeffAt_C_mul, ← hDegEq]
      show mul (LawfulField.inv E_L.lead) E_L.lead = one
      rw [LawfulCommRing.mul_comm]
      exact LawfulField.mul_inv_cancel (lead_ne_zero hENe) }

/-- Canonical projection `Poly2 E_fld = E_fld[U][W] → ModMonic (monicFY E ...)`. -/
def modPoly2Hom (E : Poly2 E_fld) (hPrim : IsPrimY E) (hDeg : 1 ≤ E.natDeg) :
    RingHom (Poly2 E_fld) (ModMonic (monicFY E hPrim hDeg)) :=
  (ModMonic.modQuotHom (monicFY E hPrim hDeg)).comp liftFY

theorem modPoly2Hom_self (E : Poly2 E_fld) (hPrim : IsPrimY E) (hDeg : 1 ≤ E.natDeg) :
    (modPoly2Hom E hPrim hDeg).toFun E = zero := by
  let M := monicFY E hPrim hDeg
  have hENe : (liftFY.toFun E) ≠ zero := fun e => hPrim.1 (liftFY_inj E e)
  have hLeadNe : (liftFY.toFun E).lead ≠ zero := lead_ne_zero hENe
  have hEq : liftFY.toFun E = mul (C (liftFY.toFun E).lead) M.poly := by
    dsimp only [M, monicFY]
    rw [← LawfulCommRing.mul_assoc]
    have hC : mul (C (liftFY.toFun E).lead) (C (LawfulField.inv (liftFY.toFun E).lead)) = one := by
      rw [← CHom_apply, ← CHom_apply, ← CHom.map_mul, LawfulField.mul_inv_cancel hLeadNe, CHom.map_one]
    rw [hC, LawfulCommRing.one_mul]
  change (ModMonic.modQuotHom M).toFun (liftFY.toFun E) = zero
  rw [hEq, RingHom.map_mul, ModMonic.modQuotHom_self_eq_zero M, LawfulCommRing.mul_zero]

theorem modPoly2Hom_C_ne_zero (E : Poly2 E_fld) (hPrim : IsPrimY E) (hDeg : 1 ≤ E.natDeg)
    {c : UPoly E_fld} (hc : c ≠ zero) :
    (modPoly2Hom E hPrim hDeg).toFun (C c) ≠ zero := by
  intro h0
  change (ModMonic.modQuotHom (monicFY E hPrim hDeg)).toFun (liftFY.toFun (C c)) = zero at h0
  rw [mapHom_C] at h0
  have h1 : (Frac.of (D := UPoly E_fld)).toFun c = zero :=
    ModMonic.modInl_inj (monicFY E hPrim hDeg) h0
  exact hc (Frac.of_injective (h1.trans (Frac.of (D := UPoly E_fld)).map_zero.symm))

/-- The kernel of the curve projection is exactly the primitive principal ideal. -/
theorem modPoly2Hom_eq_zero_iff (E : Poly2 E_fld) (hPrim : IsPrimY E)
    (hDeg : 1 ≤ E.natDeg) (P : Poly2 E_fld) :
    (modPoly2Hom E hPrim hDeg).toFun P = zero ↔ ∃ Q, P = mul E Q := by
  constructor
  · intro h
    let M := monicFY E hPrim hDeg
    have hrem : remM M (liftFY.toFun P) = zero := congrArg ModMonic.rep h
    have hspec := (quotM_remM_spec M (liftFY.toFun P)).1
    rw [hrem, LawfulCommRing.add_zero] at hspec
    apply primY_dvd_of_dvd_FY hPrim
    refine ⟨mul (quotM M (liftFY.toFun P)) (C (LawfulField.inv (liftFY.toFun E).lead)), ?_⟩
    conv => lhs; rw [hspec]
    change mul (quotM M (liftFY.toFun P))
        (mul (C (LawfulField.inv (liftFY.toFun E).lead)) (liftFY.toFun E)) = _
    constructive_ring
  · rintro ⟨Q, hQ⟩
    rw [hQ, RingHom.map_mul, modPoly2Hom_self, LawfulCommRing.zero_mul]

/-- A cleared Bezout identity supplies an actual inverse in the curve quotient. -/
theorem modPoly2Hom_unit_of_coprimeZ (E : Poly2 E_fld) (hPrim : IsPrimY E)
    (hDeg : 1 ≤ E.natDeg) {P : Poly2 E_fld} (hCop : CoprimeZ E P) :
    ∃ x_inv, mul x_inv ((modPoly2Hom E hPrim hDeg).toFun P) = one := by
  obtain ⟨u, v, c, hc, hBez⟩ := hCop
  let M := monicFY E hPrim hDeg
  let φ := modPoly2Hom E hPrim hDeg
  let cF := (Frac.of (D := UPoly E_fld)).toFun c
  have hcF : cF ≠ zero := fun e =>
    hc (Frac.of_injective (e.trans (Frac.of (D := UPoly E_fld)).map_zero.symm))
  have hApp := congrArg φ.toFun hBez
  rw [RingHom.map_add, RingHom.map_mul, RingHom.map_mul, modPoly2Hom_self,
    LawfulCommRing.mul_zero, LawfulCommRing.zero_add] at hApp
  have hcInl : φ.toFun (C c) = (ModMonic.modInl M).toFun cF := by
    show (ModMonic.modQuotHom M).toFun (liftFY.toFun (C c)) = _
    rw [mapHom_C]
    rfl
  refine ⟨mul ((ModMonic.modInl M).toFun (LawfulField.inv cF)) (φ.toFun v), ?_⟩
  rw [LawfulCommRing.mul_assoc, hApp, hcInl, ← RingHom.map_mul,
    LawfulCommRing.mul_comm (LawfulField.inv cF) cF,
    LawfulField.mul_inv_cancel hcF, RingHom.map_one]

/-- A polynomial constraint at a quotient root is equivalent to divisibility of its
cleared polynomial pullback, whenever its denominator is coprime to the curve. -/
theorem curve_pullback_dvd_iff (E : Poly2 E_fld) (hPrim : IsPrimY E)
    (hDeg : 1 ≤ E.natDeg) (a b : Poly2 E_fld)
    (z : ModMonic (monicFY E hPrim hDeg))
    (hcoord : (modPoly2Hom E hPrim hDeg).toFun a =
      mul z ((modPoly2Hom E hPrim hDeg).toFun b))
    (hCop : CoprimeZ E b) (P : UPoly (Poly2 E_fld)) :
    (∃ Q, homEvalCoeffs a b P.coeffs = mul E Q) ↔
      eval₂ (modPoly2Hom E hPrim hDeg) z P = zero := by
  obtain ⟨b_inv, hunit⟩ := modPoly2Hom_unit_of_coprimeZ E hPrim hDeg hCop
  rw [← modPoly2Hom_eq_zero_iff E hPrim hDeg]
  exact homEvalCoeffs_map_zero_iff (modPoly2Hom E hPrim hDeg) a b z b_inv hcoord hunit P

/-- Dynamic unit-or-split oracle on `ModMonic (monicFY E ...)`: every element `x` is `0`, a unit,
    or yields a proper `Y`-primitive factorization `E = mul E₁ E₂`. -/
theorem modUnitOrSplit (E : Poly2 E_fld) (hPrim : IsPrimY E) (hDeg : 1 ≤ E.natDeg)
    (x : ModMonic (monicFY E hPrim hDeg)) :
    x = zero ∨ (∃ x_inv, mul x_inv x = one) ∨
      ∃ E₁ E₂ : Poly2 E_fld, IsPrimY E₁ ∧ IsPrimY E₂ ∧ 1 ≤ E₁.natDeg ∧ 1 ≤ E₂.natDeg ∧
        E = mul E₁ E₂ ∧ tdeg E₁ + tdeg E₂ = tdeg E := by
  let M := monicFY E hPrim hDeg
  obtain ⟨dx, X0, hdx, hX0⟩ := clear_uPoly_ratFunc x.rep
  have hCdxNe : (C ((Frac.of (D := UPoly E_fld)).toFun dx) : UPoly (RatFunc E_fld)) ≠ zero := fun e => by
    have hc := congrArg (fun p : UPoly (RatFunc E_fld) => coeffAt p.coeffs 0) e
    rw [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at hc
    exact hdx (Frac.of_injective (hc.trans (Frac.of (D := UPoly E_fld)).map_zero.symm))
  have hxRel : mul ((modPoly2Hom E hPrim hDeg).toFun (C dx)) x =
      (modPoly2Hom E hPrim hDeg).toFun X0 := by
    have hxId : (ModMonic.modQuotHom M).toFun x.rep = x := by
      apply ModMonic.ext; exact remM_of_lt M x.reduced
    conv => lhs; rhs; rw [← hxId]
    change mul ((ModMonic.modQuotHom M).toFun (liftFY.toFun (C dx)))
        ((ModMonic.modQuotHom M).toFun x.rep) = (ModMonic.modQuotHom M).toFun (liftFY.toFun X0)
    rw [← RingHom.map_mul, mapHom_C, hX0]
  rcases d5_split_prim E X0 hPrim with ⟨Q, hQ⟩ | ⟨u0, v0, c, hc, hBez⟩ |
    ⟨E₁, E₂, h1, h2, hd1, hd2, hEq, hTdeg, _⟩
  · left
    have hX0_zero : X0 = zero := by
      apply Decidable.byContradiction; intro hX0Ne
      have hQNe : Q ≠ zero := fun e => hX0Ne (by rw [hQ, e, LawfulCommRing.mul_zero])
      have hDegX0 : X0.natDeg = E.natDeg + Q.natDeg := by
        rw [hQ]; exact UPoly.natDeg_mul hPrim.1 hQNe
      have hDegLift : (liftFY.toFun X0).natDeg = X0.natDeg :=
        UPoly.natDeg_mapHom _ (fun a ha => Frac.of_injective (ha.trans (Frac.of (D := UPoly E_fld)).map_zero.symm)) X0
      have hDegMul : (mul (C ((Frac.of (D := UPoly E_fld)).toFun dx)) x.rep).natDeg ≤ x.rep.natDeg := by
        have h1 := natDeg_mul_le (C ((Frac.of (D := UPoly E_fld)).toFun dx)) x.rep
        have hC0 : (C ((Frac.of (D := UPoly E_fld)).toFun dx)).natDeg = 0 := by
          apply Nat.le_zero.mp; apply natDeg_le_of_coeffAt; intro k hk
          cases k with | zero => omega | succ k => exact coeffAt_C_succ _ k
        omega
      rw [hX0] at hDegMul
      have hReduced : x.rep.natDeg < E.natDeg := x.reduced
      omega
    have hRep0 : x.rep = zero := by
      rw [hX0_zero, RingHom.map_zero] at hX0
      exact mul_right_cancel' hCdxNe (by rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_comm]; exact hX0)
    exact ModMonic.ext hRep0
  · right; left
    let φ := modPoly2Hom E hPrim hDeg
    have hApp := congrArg φ.toFun hBez
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_mul, modPoly2Hom_self E hPrim hDeg,
      LawfulCommRing.mul_zero, LawfulCommRing.zero_add, ← hxRel] at hApp
    let sc : RatFunc E_fld := mul (LawfulField.inv ((Frac.of (D := UPoly E_fld)).toFun c))
      ((Frac.of (D := UPoly E_fld)).toFun dx)
    have hcNeF : (Frac.of (D := UPoly E_fld)).toFun c ≠ zero := fun e =>
      hc (Frac.of_injective (e.trans (Frac.of (D := UPoly E_fld)).map_zero.symm))
    refine ⟨mul ((ModMonic.modInl M).toFun sc) (φ.toFun v0), ?_⟩
    have hAssoc : mul (mul ((ModMonic.modInl M).toFun sc) (φ.toFun v0)) x =
        mul ((ModMonic.modInl M).toFun (LawfulField.inv ((Frac.of (D := UPoly E_fld)).toFun c)))
          (mul (φ.toFun v0) (mul (φ.toFun (C dx)) x)) := by
      dsimp only [sc]
      have hdxInl : φ.toFun (C dx) = (ModMonic.modInl M).toFun ((Frac.of (D := UPoly E_fld)).toFun dx) := by
        show (ModMonic.modQuotHom M).toFun (liftFY.toFun (C dx)) = _
        rw [mapHom_C]; rfl
      rw [hdxInl, RingHom.map_mul]; constructive_ring
    have hcInl : φ.toFun (C c) = (ModMonic.modInl M).toFun ((Frac.of (D := UPoly E_fld)).toFun c) := by
      show (ModMonic.modQuotHom M).toFun (liftFY.toFun (C c)) = _
      rw [mapHom_C]; rfl
    rw [hAssoc, hApp, hcInl, ← RingHom.map_mul, LawfulCommRing.mul_comm,
      LawfulField.mul_inv_cancel hcNeF, RingHom.map_one]
  · exact .inr (.inr ⟨E₁, E₂, h1, h2, hd1, hd2, hEq, hTdeg⟩)

/-- Dynamic Euclidean `xgcd` in `(ModMonic (monicFY E ...))[Z]` when `A ≠ 0`. -/
theorem d5_xgcd_mod (E : Poly2 E_fld) (hPrim : IsPrimY E) (hDeg : 1 ≤ E.natDeg)
    (A B : UPoly (ModMonic (monicFY E hPrim hDeg))) (hANe : A ≠ zero) :
    (∃ E₁ E₂ : Poly2 E_fld, IsPrimY E₁ ∧ IsPrimY E₂ ∧ 1 ≤ E₁.natDeg ∧ 1 ≤ E₂.natDeg ∧
      E = mul E₁ E₂ ∧ tdeg E₁ + tdeg E₂ = tdeg E) ∨
    ∃ (G U0 V0 : UPoly (ModMonic (monicFY E hPrim hDeg))),
      G ≠ zero ∧ coeffAt G.coeffs G.natDeg = one ∧
      add (mul U0 A) (mul V0 B) = G ∧
      (∃ Q_A, A = mul G Q_A) ∧ (∃ Q_B, B = mul G Q_B) := by
  let R_E := ModMonic (monicFY E hPrim hDeg)
  have aux : ∀ (fuel : Nat) (A B : UPoly R_E), B.coeffs.length ≤ fuel → A ≠ zero →
      (∃ E₁ E₂ : Poly2 E_fld, IsPrimY E₁ ∧ IsPrimY E₂ ∧ 1 ≤ E₁.natDeg ∧ 1 ≤ E₂.natDeg ∧
        E = mul E₁ E₂ ∧ tdeg E₁ + tdeg E₂ = tdeg E) ∨
      ∃ (G U0 V0 : UPoly R_E),
        G ≠ zero ∧ coeffAt G.coeffs G.natDeg = one ∧
        add (mul U0 A) (mul V0 B) = G ∧
        (∃ Q_A, A = mul G Q_A) ∧ (∃ Q_B, B = mul G Q_B) := by
    intro fuel; induction fuel with
    | zero =>
      intro A B hLen hA0
      have hBnil : B.coeffs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hLen)
      have hB0 : B = zero := (eq_zero_iff B).mpr hBnil
      subst hB0
      rcases modUnitOrSplit E hPrim hDeg A.lead with hLead0 | ⟨c_inv, hInv⟩ | hSplit
      · exact absurd hLead0 (lead_ne_zero hA0)
      · right
        let G := mul (C c_inv) A
        have hAG : A = mul G (C A.lead) := by
          dsimp only [G]
          have h1 : mul (mul (C c_inv) A) (C A.lead) = mul (mul (C A.lead) (C c_inv)) A := by
            constructive_ring
          rw [h1, ← CHom_apply, ← CHom_apply, ← CHom.map_mul, LawfulCommRing.mul_comm A.lead c_inv, hInv, CHom.map_one, LawfulCommRing.one_mul]
        have hGNe : G ≠ zero := fun e => hA0 (by rw [hAG, e, LawfulCommRing.zero_mul])
        have hGdeg : G.natDeg = A.natDeg := by
          apply Nat.le_antisymm
          · have h1 := natDeg_mul_le (C c_inv) A
            have hC0 : (C c_inv).natDeg = 0 := by
              apply Nat.le_zero.mp; apply natDeg_le_of_coeffAt; intro k hk
              cases k with | zero => omega | succ k => exact coeffAt_C_succ _ k
            change G.natDeg ≤ (C c_inv).natDeg + A.natDeg at h1
            omega
          · have h1 := natDeg_mul_le G (C A.lead)
            rw [← hAG] at h1
            have hC0 : (C A.lead).natDeg = 0 := by
              apply Nat.le_zero.mp; apply natDeg_le_of_coeffAt; intro k hk
              cases k with | zero => omega | succ k => exact coeffAt_C_succ _ k
            omega
        have hGmon : coeffAt G.coeffs G.natDeg = one := by
          rw [hGdeg]; dsimp only [G]; rw [coeffAt_C_mul]; exact hInv
        refine ⟨G, C c_inv, zero, hGNe, hGmon, ?_, ⟨C A.lead, hAG⟩, ⟨zero, (LawfulCommRing.mul_zero G).symm⟩⟩
        rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
      · exact .inl hSplit
    | succ fuel ih =>
      intro A B hLen hA0
      if hB0 : B = zero then
        subst B
        exact ih A zero (by rw [coeffs_zero]; exact Nat.zero_le _) hA0
      else
        rcases modUnitOrSplit E hPrim hDeg B.lead with hLead0 | ⟨c_inv, hInv⟩ | hSplit
        · exact absurd hLead0 (lead_ne_zero hB0)
        · if hBdeg0 : B.natDeg = 0 then
            right
            have hBC : B = C B.lead := by
              apply ext_coeffAt; intro k
              cases k with
              | zero => rw [coeffAt_C_zero]; unfold lead; rw [hBdeg0]
              | succ k => rw [coeffAt_C_succ]; exact B.coeffAt_eq_zero_of_natDeg_lt (by omega)
            have hBez1 : add (mul zero A) (mul (C c_inv) B) = one := by
              rw [LawfulCommRing.zero_mul, LawfulCommRing.zero_add, hBC, ← CHom_apply, ← CHom_apply, ← CHom.map_mul, hInv, CHom.map_one]
            exact ⟨one, zero, C c_inv, NontrivialRing.one_ne_zero,
              by rw [natDeg_one, one_eq_C, coeffAt_C_zero], hBez1,
              ⟨A, (LawfulCommRing.one_mul A).symm⟩, ⟨B, (LawfulCommRing.one_mul B).symm⟩⟩
          else
            have hBpos : 1 ≤ B.natDeg := by omega
            have hInvCoeff : mul c_inv (coeffAt B.coeffs B.natDeg) = one := hInv
            obtain ⟨hDiv, hRemLt⟩ := divModLead_spec B B.natDeg c_inv hBpos (Nat.le_refl _) hInvCoeff A
            let Q := (divModLead B B.natDeg c_inv A).1
            let R_rem := (divModLead B B.natDeg c_inv A).2
            change A = add (mul Q B) R_rem at hDiv
            change R_rem.natDeg < B.natDeg at hRemLt
            have hRemLen : R_rem.coeffs.length ≤ fuel := by
              if hR0 : R_rem = zero then
                rw [hR0, coeffs_zero]; exact Nat.zero_le _
              else
                have hRne : R_rem.coeffs ≠ [] := fun e => hR0 ((eq_zero_iff R_rem).mpr e)
                have hPos := List.length_pos_iff.mpr hRne
                unfold natDeg at hRemLt hBpos
                omega
            rcases ih B R_rem hRemLen hB0 with hSplit | ⟨G, U', V', hGNe, hGmon, hBez', ⟨QB, hQB⟩, ⟨QR, hQR⟩⟩
            · exact .inl hSplit
            · right
              refine ⟨G, V', sub U' (mul V' Q), hGNe, hGmon, ?_,
                ⟨add (mul QB Q) QR, ?_⟩, ⟨QB, hQB⟩⟩
              · have hSubR : R_rem = sub A (mul Q B) := by
                  conv => rhs; lhs; rw [hDiv]
                  constructive_ring
                rw [← hBez', hSubR]; constructive_ring
              · conv => lhs; rw [hDiv]
                conv => lhs; lhs; rhs; rw [hQB]
                rw [hQR]; constructive_ring
        · exact .inl hSplit
  exact aux B.coeffs.length A B (Nat.le_refl _) hANe

/-- Embed `E_fld[U][Z]` (`Poly2 E_fld`) into `(E_fld[U][W])[Z]` (`UPoly (Poly2 E_fld)`), constant in `W`. -/
def embedUZ : RingHom (Poly2 E_fld) (UPoly (Poly2 E_fld)) :=
  UPoly.mapHom UPoly.CHom

/-- **Dynamic Curve Leaf Root Decomposition (`curve_leaf_root_decomp`)**:
    Given `C₁ : Poly2 E_fld` monic in `Z` of degree `h_C ≥ 1`, `P₀ : UPoly (Poly2 E_fld)` with
    `P₀.natDeg ≤ H₀`, and any `Y`-primitive factor `E : Poly2 E_fld` (`1 ≤ tdeg E`) dividing
    `sylRes h_C H₀ (embedUZ C₁) P₀`, dynamically decomposes `E` into a list `Es` of `Y`-primitive
    factors (`1 ≤ E_j.natDeg`, `(Es.map tdeg).sum = tdeg E`, every root `(u, w)` of `E` is a root
    of some `E_j ∈ Es`) such that on EVERY leaf `E_j ∈ Es`, EITHER `E_j` divides
    `g₁ := sylResDeriv h_C H₀ (embedUZ C₁) P₀ 1`, OR `CoprimeZ E_j g₁` AND `(C₁, P₀)` has an
    explicit common root `ζ : ModMonic (monicFY E_j ...)`! -/
theorem curve_leaf_root_decomp {h_C H₀ : Nat} {C₁ : Poly2 E_fld} {P₀ : UPoly (Poly2 E_fld)}
    (hC₁deg : C₁.natDeg ≤ h_C) (hC₁mon : coeffAt C₁.coeffs h_C = one)
    (hP₀deg : P₀.natDeg ≤ H₀) :
    let R_res := sylRes h_C H₀ (embedUZ.toFun C₁) P₀
    let g₁ := sylResDeriv h_C H₀ (embedUZ.toFun C₁) P₀ one
    ∀ (E : Poly2 E_fld), IsPrimY E → 1 ≤ tdeg E → (∃ Q_res, R_res = mul E Q_res) →
      ∃ Es : List (Poly2 E_fld),
        (Es.map tdeg).sum = tdeg E ∧
        (∀ u w, E.eval2 u w = zero → ∃ Ej ∈ Es, Ej.eval2 u w = zero) ∧
        ∀ Ej ∈ Es, ∃ (hPj : IsPrimY Ej) (hDj : 1 ≤ Ej.natDeg),
          (∃ Qg, g₁ = mul Ej Qg) ∨
          (CoprimeZ Ej g₁ ∧
            ∃ ζ : ModMonic (monicFY Ej hPj hDj),
              ((mapHom (modPoly2Hom Ej hPj hDj)).toFun (embedUZ.toFun C₁)).eval ζ = zero ∧
              ((mapHom (modPoly2Hom Ej hPj hDj)).toFun P₀).eval ζ = zero) := by
  dsimp only
  let R_res := sylRes h_C H₀ (embedUZ.toFun C₁) P₀
  let g₁ := sylResDeriv h_C H₀ (embedUZ.toFun C₁) P₀ one
  have sum_append : ∀ xs ys : List Nat, (xs ++ ys).sum = xs.sum + ys.sum := by
    intro xs ys; induction xs with
    | nil => show ys.sum = 0 + ys.sum; omega
    | cons x tl ih => show x + (tl ++ ys).sum = x + tl.sum + ys.sum; rw [ih]; omega
  have eval2_mul_eq : ∀ (A B : Poly2 E_fld) (u w : E_fld),
      (mul A B).eval2 u w = mul (A.eval2 u w) (B.eval2 u w) :=
    fun A B u w => UPoly.eval₂_mul (UPoly.evalHom u) w A B
  have aux : ∀ (fuel : Nat) (E : Poly2 E_fld), tdeg E ≤ fuel →
      IsPrimY E → 1 ≤ tdeg E → (∃ Q_res, R_res = mul E Q_res) →
      ∃ Es : List (Poly2 E_fld),
        (Es.map tdeg).sum = tdeg E ∧
        (∀ u w, E.eval2 u w = zero → ∃ Ej ∈ Es, Ej.eval2 u w = zero) ∧
        ∀ Ej ∈ Es, ∃ (hPj : IsPrimY Ej) (hDj : 1 ≤ Ej.natDeg),
          (∃ Qg, g₁ = mul Ej Qg) ∨
          (CoprimeZ Ej g₁ ∧
            ∃ ζ : ModMonic (monicFY Ej hPj hDj),
              ((mapHom (modPoly2Hom Ej hPj hDj)).toFun (embedUZ.toFun C₁)).eval ζ = zero ∧
              ((mapHom (modPoly2Hom Ej hPj hDj)).toFun P₀).eval ζ = zero) := by
    intro fuel; induction fuel with
    | zero => intros E hFuel _ hPos _; exfalso; omega
    | succ fuel ih =>
      intro E hFuel hPrim hPos ⟨Q_res, hQres⟩
      have hEDeg : 1 ≤ E.natDeg := primY_natDeg_pos hPrim hPos
      have mergeSplit : ∀ (E₁ E₂ : Poly2 E_fld),
          IsPrimY E₁ → IsPrimY E₂ → 1 ≤ E₁.natDeg → 1 ≤ E₂.natDeg →
          E = mul E₁ E₂ → tdeg E₁ + tdeg E₂ = tdeg E →
          ∃ Es : List (Poly2 E_fld),
            (Es.map tdeg).sum = tdeg E ∧
            (∀ u w, E.eval2 u w = zero → ∃ Ej ∈ Es, Ej.eval2 u w = zero) ∧
            ∀ Ej ∈ Es, ∃ (hPj : IsPrimY Ej) (hDj : 1 ≤ Ej.natDeg),
              (∃ Qg, g₁ = mul Ej Qg) ∨
              (CoprimeZ Ej g₁ ∧
                ∃ ζ : ModMonic (monicFY Ej hPj hDj),
                  ((mapHom (modPoly2Hom Ej hPj hDj)).toFun (embedUZ.toFun C₁)).eval ζ = zero ∧
                  ((mapHom (modPoly2Hom Ej hPj hDj)).toFun P₀).eval ζ = zero) := by
        intro E₁ E₂ hP1 hP2 hD1 hD2 hMul hSum
        have hT1 : 1 ≤ tdeg E₁ := Nat.le_trans hD1 (natDeg_le_tdeg E₁)
        have hT2 : 1 ≤ tdeg E₂ := Nat.le_trans hD2 (natDeg_le_tdeg E₂)
        obtain ⟨Es1, hS1, hR1, hL1⟩ := ih E₁ (by omega) hP1 hT1
          ⟨mul E₂ Q_res, by rw [hQres, hMul, LawfulCommRing.mul_assoc]⟩
        obtain ⟨Es2, hS2, hR2, hL2⟩ := ih E₂ (by omega) hP2 hT2
          ⟨mul E₁ Q_res, by rw [hQres, hMul]; constructive_ring⟩
        refine ⟨Es1 ++ Es2, by rw [List.map_append, sum_append, hS1, hS2, hSum], ?_, ?_⟩
        · intro u w huw
          rw [hMul, eval2_mul_eq] at huw
          rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero huw with h0 | h0
          · obtain ⟨Ej, hMem, hZ⟩ := hR1 u w h0
            exact ⟨Ej, List.mem_append_left _ hMem, hZ⟩
          · obtain ⟨Ej, hMem, hZ⟩ := hR2 u w h0
            exact ⟨Ej, List.mem_append_right _ hMem, hZ⟩
        · intro Ej hMem
          rcases List.mem_append.mp hMem with hM | hM
          · exact hL1 Ej hM
          · exact hL2 Ej hM
      rcases d5_split_prim E g₁ hPrim with ⟨Qg, hQg⟩ | hCopG1 | ⟨E₁, E₂, hP1, hP2, hD1, hD2, hMul, hSum, _⟩
      · refine ⟨[E], by show tdeg E + 0 = tdeg E; omega, fun u w h => ⟨E, .head _, h⟩, ?_⟩
        intro Ej hMem; cases hMem with
        | head => exact ⟨hPrim, hEDeg, .inl ⟨Qg, hQg⟩⟩
        | tail _ hNil => cases hNil
      · let φ := modPoly2Hom E hPrim hEDeg
        let C1_mod := (mapHom φ).toFun (embedUZ.toFun C₁)
        let P0_mod := (mapHom φ).toFun P₀
        have hC1_mod_mon : coeffAt C1_mod.coeffs h_C = one := by
          dsimp only [C1_mod, embedUZ]
          rw [coeffAt_mapHom, coeffAt_mapHom, hC₁mon, CHom.map_one, φ.map_one]
        have hC1_mod_deg : C1_mod.natDeg ≤ h_C :=
          Nat.le_trans (natDeg_mapHom_le φ _) (Nat.le_trans (natDeg_mapHom_le CHom C₁) hC₁deg)
        have hP0_mod_deg : P0_mod.natDeg ≤ H₀ := Nat.le_trans (natDeg_mapHom_le φ P₀) hP₀deg
        have hC1_mod_ne : C1_mod ≠ zero := fun e => by
          rw [e, coeffs_zero, coeffAt_nil] at hC1_mod_mon
          exact NontrivialRing.one_ne_zero hC1_mod_mon.symm
        rcases d5_xgcd_mod E hPrim hEDeg C1_mod P0_mod hC1_mod_ne with
          ⟨E₁, E₂, hP1, hP2, hD1, hD2, hMul, hSum⟩ |
          ⟨G, U0, V0, hGNe, hGmon, hBez, ⟨Q_C, hQC⟩, ⟨Q_P, hQP⟩⟩
        · exact mergeSplit E₁ E₂ hP1 hP2 hD1 hD2 hMul hSum
        · let d_G := G.natDeg
          have hQCNe : Q_C ≠ zero := fun e => hC1_mod_ne (by rw [hQC, e, LawfulCommRing.mul_zero])
          have hdG_QC_le : d_G + Q_C.natDeg ≤ h_C := by
            apply Decidable.byContradiction; intro hNot
            have hz := C1_mod.coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_le_of_lt hC1_mod_deg (Nat.lt_of_not_le hNot))
            rw [hQC, (coeffAt_mul_top G Q_C).2] at hz
            unfold lead at hz; rw [hGmon, LawfulCommRing.one_mul] at hz
            exact lead_ne_zero hQCNe hz
          if hdG0 : d_G = 0 then
            exfalso
            have hG1 : G = one := by
              apply ext_coeffAt; intro k
              cases k with
              | zero =>
                have : coeffAt G.coeffs 0 = one := by rw [← hdG0]; exact hGmon
                rw [this, one_eq_C, coeffAt_C_zero]
              | succ k =>
                rw [one_eq_C, coeffAt_C_succ]
                exact G.coeffAt_eq_zero_of_natDeg_lt (by omega)
            rw [hG1] at hBez
            obtain ⟨r_inv, hUnit⟩ := isUnit_sylRes_of_bezout hC1_mod_deg
              (by rw [hC1_mod_mon, LawfulCommRing.one_mul]) hP0_mod_deg hBez
            have hRes0 : sylRes h_C H₀ C1_mod P0_mod = zero := by
              rw [← map_sylRes φ]; change φ.toFun R_res = zero
              rw [hQres, RingHom.map_mul, modPoly2Hom_self E hPrim hEDeg, LawfulCommRing.zero_mul]
            rw [hRes0, LawfulCommRing.mul_zero] at hUnit
            exact NontrivialRing.one_ne_zero hUnit.symm
          else if hdG2 : 2 ≤ d_G then
            exfalso
            have hg1_zero : φ.toFun g₁ = zero := by
              dsimp only [g₁]
              rw [map_sylResDeriv φ, RingHom.map_one]
              exact sylResDeriv_eq_zero_of_common_factor_ge_two hdG2 (by omega)
                hP0_mod_deg (Nat.le_refl d_G) hGmon hQC (by omega) hQP
            obtain ⟨u0, v0, c, hc, hCopEq⟩ := hCopG1
            have hApp := congrArg φ.toFun hCopEq
            rw [RingHom.map_add, RingHom.map_mul, RingHom.map_mul,
              modPoly2Hom_self E hPrim hEDeg, hg1_zero, LawfulCommRing.mul_zero,
              LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hApp
            exact modPoly2Hom_C_ne_zero E hPrim hEDeg hc hApp.symm
          else
            have hdG1 : d_G = 1 := by omega
            let ζ := neg (coeffAt G.coeffs 0)
            have hGlin : G = sub X (C ζ) := by
              apply ext_coeffAt; intro k
              have hSubEq : sub X (C ζ) = add X (C (coeffAt G.coeffs 0)) := by
                dsimp only [ζ]; rw [LawfulCommRing.sub_eq_add_neg, ← CHom_apply, ← RingHom.map_neg CHom,
                  CHom_apply, LawfulCommRing.neg_neg]
              rw [hSubEq, coeffAt_add]
              cases k with
              | zero =>
                show coeffAt G.coeffs 0 = add (coeffAt (ofList [zero, one]).coeffs 0) (coeffAt (C _).coeffs 0)
                rw [coeffAt_ofList, coeffAt_cons_zero, coeffAt_C_zero, LawfulCommRing.zero_add]
              | succ k =>
                cases k with
                | zero =>
                  have h1 : coeffAt G.coeffs 1 = one := by rw [← hdG1]; exact hGmon
                  show coeffAt G.coeffs 1 = add (coeffAt (ofList [zero, one]).coeffs 1) (coeffAt (C _).coeffs 1)
                  rw [h1, coeffAt_ofList, coeffAt_cons_succ, coeffAt_cons_zero, coeffAt_C_succ, LawfulCommRing.add_zero]
                | succ k =>
                  rw [G.coeffAt_eq_zero_of_natDeg_lt (by omega), coeffAt_C_succ]
                  show zero = add (coeffAt (ofList [zero, one]).coeffs (k + 2)) zero
                  rw [coeffAt_ofList, coeffAt_cons_succ, coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.add_zero]
            have hLinZ : (sub X (C ζ)).eval ζ = zero := by
              show (evalHom ζ).toFun (sub X (C ζ)) = zero
              rw [RingHom.map_sub, evalHom_apply, evalHom_apply, eval_X, eval_C, LawfulCommRing.sub_self]
            have hC1_root : C1_mod.eval ζ = zero := by
              rw [hQC, hGlin]; show (evalHom ζ).toFun _ = zero
              rw [RingHom.map_mul, evalHom_apply, hLinZ, LawfulCommRing.zero_mul]
            have hP0_root : P0_mod.eval ζ = zero := by
              rw [hQP, hGlin]; show (evalHom ζ).toFun _ = zero
              rw [RingHom.map_mul, evalHom_apply, hLinZ, LawfulCommRing.zero_mul]
            refine ⟨[E], by show tdeg E + 0 = tdeg E; omega, fun u w h => ⟨E, .head _, h⟩, ?_⟩
            intro Ej hMem; cases hMem with
            | head => exact ⟨hPrim, hEDeg, .inr ⟨hCopG1, ζ, hC1_root, hP0_root⟩⟩
            | tail _ hNil => cases hNil
      · exact mergeSplit E₁ E₂ hP1 hP2 hD1 hD2 hMul hSum
  intro E hPrim hPos hDiv
  exact aux (tdeg E) E (Nat.le_refl _) hPrim hPos hDiv

end CurveDecomp
end SylElim

namespace ShearedCurveGcdTests
open UPoly Poly2 SylElim

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

private theorem isPrimY_monic_deg1_loc (p : UPoly Goldilocks) :
    IsPrimY (ofList [p, one] : Poly2 Goldilocks) := by
  refine ⟨by
    intro h0
    have hc := congrArg (fun q : Poly2 Goldilocks => coeffAt q.coeffs 1) h0
    rw [coeffAt_ofList, coeffAt_cons_succ, coeffAt_cons_zero, coeffs_zero, coeffAt_nil] at hc
    exact NontrivialRing.one_ne_zero hc, fun f hf => ?_⟩
  obtain ⟨q, hq⟩ := hf 1
  rw [coeffAt_ofList, coeffAt_cons_succ, coeffAt_cons_zero] at hq
  have hf0 : f ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.zero_mul])
  have hq0 : q ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.mul_zero])
  have hd := UPoly.natDeg_mul hf0 hq0
  rw [← hq, natDeg_one] at hd; omega

/-- `E = W - U` (`ofList [neg X, one]`) is `U`-primitive with `tdeg E = 1` and `1 ≤ E.natDeg`. -/
theorem inhabited_primY_natDeg_pos :
    ∃ E : Poly2 Goldilocks, IsPrimY E ∧ 1 ≤ tdeg E ∧ 1 ≤ E.natDeg :=
  let E : Poly2 Goldilocks := ofList [neg X, one]
  ⟨E, isPrimY_monic_deg1_loc (neg X), by decide +kernel,
    primY_natDeg_pos (isPrimY_monic_deg1_loc (neg X)) (by decide +kernel)⟩

/-- `#tooth`: dropping `IsPrimY E` invalidates `primY_natDeg_pos`: `E = C X` (`U · 1`) has
    `tdeg E = 1 ≥ 1` yet `E.natDeg = 0`! -/
theorem tooth_natDeg_pos_needs_primY :
    ∃ E : Poly2 Goldilocks, E ≠ zero ∧ 1 ≤ tdeg E ∧ ¬ (1 ≤ E.natDeg) :=
  ⟨C X, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The curve `W = 0` divides `Res_Z(Z, W) = W`, while its derivative resultant is `1`.
This exercises the common-root branch with a nonzero resultant and a nonempty curve. -/
theorem inhabited_curve_leaf_root_decomp :
    ∃ (C₁ E : Poly2 Goldilocks) (P₀ : UPoly (Poly2 Goldilocks)),
      C₁.natDeg ≤ 1 ∧ coeffAt C₁.coeffs 1 = one ∧ P₀.natDeg ≤ 0 ∧
      IsPrimY E ∧ 1 ≤ tdeg E ∧
      (∃ Q_res, sylRes 1 0 (embedUZ.toFun C₁) P₀ = mul E Q_res) ∧
      sylRes 1 0 (embedUZ.toFun C₁) P₀ ≠ zero ∧
      sylResDeriv 1 0 (embedUZ.toFun C₁) P₀ one = one := by
  refine ⟨X, X, C X, by decide +kernel, by decide +kernel, by decide +kernel,
    isPrimY_monic_deg1_loc zero, by decide +kernel, ⟨one, by decide +kernel⟩,
    by decide +kernel, by decide +kernel⟩

/-- Applying the decomposition to `Res_Z(Z,W)` produces an actual common-root leaf. -/
theorem inhabited_curve_common_root :
    ∃ (E : Poly2 Goldilocks) (hP : IsPrimY E) (hD : 1 ≤ E.natDeg)
      (ζ : ModMonic (monicFY E hP hD)),
      ((mapHom (modPoly2Hom E hP hD)).toFun (embedUZ.toFun (X : Poly2 Goldilocks))).eval ζ = zero ∧
      ((mapHom (modPoly2Hom E hP hD)).toFun (C (X : Poly2 Goldilocks))).eval ζ = zero := by
  obtain ⟨Es, _, hCover, hLeaves⟩ :=
    curve_leaf_root_decomp (h_C := 1) (H₀ := 0) (C₁ := (X : Poly2 Goldilocks))
      (P₀ := C X) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      X (isPrimY_monic_deg1_loc zero) (by decide +kernel) ⟨one, by decide +kernel⟩
  obtain ⟨E, hMem, _⟩ := hCover zero zero (by decide +kernel)
  obtain ⟨hP, hD, hDiv | hRoot⟩ := hLeaves E hMem
  · obtain ⟨Q, hQ⟩ := hDiv
    have hDeriv : sylResDeriv 1 0 (embedUZ.toFun (X : Poly2 Goldilocks)) (C X) one = one :=
      by decide +kernel
    rw [hDeriv] at hQ
    have hQne : Q ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hQ, e, LawfulCommRing.mul_zero])
    have hDegree := UPoly.natDeg_mul hP.1 hQne
    rw [← hQ, natDeg_one] at hDegree
    exfalso
    omega
  · obtain ⟨ζ, hC, hP₀⟩ := hRoot.2
    exact ⟨E, hP, hD, ζ, hC, hP₀⟩

/-- Without resultant divisibility, `C₁=Z`, `P₀=1`, and the curve `W=0` cannot
have the asserted decomposition: neither a derivative-divisor leaf nor a common root exists. -/
theorem tooth_curve_leaf_root_decomp_needs_divisibility :
    ∃ (C₁ E : Poly2 Goldilocks) (P₀ : UPoly (Poly2 Goldilocks)),
      C₁.natDeg ≤ 1 ∧ coeffAt C₁.coeffs 1 = one ∧ P₀.natDeg ≤ 0 ∧
      IsPrimY E ∧ 1 ≤ tdeg E ∧
      ¬ ∃ Es : List (Poly2 Goldilocks),
        (Es.map tdeg).sum = tdeg E ∧
        (∀ u w, E.eval2 u w = zero → ∃ Ej ∈ Es, Ej.eval2 u w = zero) ∧
        ∀ Ej ∈ Es, ∃ (hPj : IsPrimY Ej) (hDj : 1 ≤ Ej.natDeg),
          (∃ Qg, sylResDeriv 1 0 (embedUZ.toFun C₁) P₀ one = mul Ej Qg) ∨
          (CoprimeZ Ej (sylResDeriv 1 0 (embedUZ.toFun C₁) P₀ one) ∧
            ∃ ζ : ModMonic (monicFY Ej hPj hDj),
              ((mapHom (modPoly2Hom Ej hPj hDj)).toFun (embedUZ.toFun C₁)).eval ζ = zero ∧
              ((mapHom (modPoly2Hom Ej hPj hDj)).toFun P₀).eval ζ = zero) := by
  refine ⟨X, X, one, by decide +kernel, by decide +kernel, by decide +kernel,
    isPrimY_monic_deg1_loc zero, by decide +kernel, ?_⟩
  rintro ⟨Es, _, hCover, hLeaves⟩
  obtain ⟨E, hMem, _⟩ := hCover zero zero (by decide +kernel)
  obtain ⟨hP, hD, hDiv | hRoot⟩ := hLeaves E hMem
  · obtain ⟨Q, hQ⟩ := hDiv
    have hDeriv : sylResDeriv 1 0 (embedUZ.toFun (X : Poly2 Goldilocks)) one one = one :=
      by decide +kernel
    rw [hDeriv] at hQ
    have hQne : Q ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hQ, e, LawfulCommRing.mul_zero])
    have hDegree := UPoly.natDeg_mul hP.1 hQne
    rw [← hQ, natDeg_one] at hDegree
    omega
  · obtain ⟨ζ, _, hP₀⟩ := hRoot.2
    rw [RingHom.map_one, one_eq_C, eval_C] at hP₀
    exact NontrivialRing.one_ne_zero hP₀

#verify_constructive SylElim.modPoly2Hom_eq_zero_iff SylElim.modPoly2Hom_unit_of_coprimeZ SylElim.curve_pullback_dvd_iff
#verify_constructive SylElim.primY_natDeg_pos SylElim.modUnitOrSplit SylElim.d5_xgcd_mod SylElim.curve_leaf_root_decomp
#verify_constructive inhabited_primY_natDeg_pos tooth_natDeg_pos_needs_primY
#tooth_pair SylElim.primY_natDeg_pos vs tooth_natDeg_pos_needs_primY
#verify_inhabited SylElim.primY_natDeg_pos inhabited_primY_natDeg_pos
#verify_constructive inhabited_curve_leaf_root_decomp inhabited_curve_common_root
#verify_inhabited SylElim.curve_leaf_root_decomp inhabited_curve_leaf_root_decomp
#verify_constructive tooth_curve_leaf_root_decomp_needs_divisibility
#tooth_pair SylElim.curve_leaf_root_decomp vs tooth_curve_leaf_root_decomp_needs_divisibility

end ShearedCurveGcdTests
end Qsag
end
