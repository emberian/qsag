module
/-
# Qsag.CodingTheory.SylvesterDeriv — Dual Numbers & Formal Resultant Derivative Identity

Constructive dual numbers `Dual R` (`R[ε]/(ε²)`) and directional resultant derivative `sylResDeriv`:
* `sylResDeriv_of_factor`: if `C1 = (X - C ζ) * Q` and `P0.eval ζ = 0`, then
  `sylResDeriv (m' + 1) N C1 P0 B = B.eval ζ * sylRes m' N Q P0` over every `[LawfulCommRing R]`.
* `sylResDeriv_common_root`: at ANY common root `ζ` of `(C1, P0)` (`1 ≤ m`),
  `sylResDeriv m N C1 P0 B = B.eval ζ * sylResDeriv m N C1 P0 1`!
* `degFn_sylResDeriv_le`: weighted `DegFn` bound `w (sylResDeriv m N C1 P0 B) ≤ h_A * h_B`.
-/

public import Qsag.CodingTheory.SylvesterElimination
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.MatrixDet
import all Qsag.CodingTheory.SylvesterElimination
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false
open CommRingOps RoundPoly

namespace SylElim

@[ext]
structure Dual (R : Type) where
  fst : R
  snd : R
  deriving DecidableEq

namespace Dual
section Ring
variable {R S : Type} [LawfulCommRing R] [LawfulCommRing S]

instance : LawfulCommRing (Dual R) where
  zero := ⟨zero, zero⟩
  one := ⟨one, zero⟩
  add x y := ⟨add x.fst y.fst, add x.snd y.snd⟩
  mul x y := ⟨mul x.fst y.fst, add (mul x.fst y.snd) (mul x.snd y.fst)⟩
  neg x := ⟨neg x.fst, neg x.snd⟩
  sub x y := ⟨sub x.fst y.fst, sub x.snd y.snd⟩
  add_assoc a b c := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.add_assoc _ _ _
  add_comm a b := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.add_comm _ _
  zero_add a := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.zero_add _
  add_zero a := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.add_zero _
  add_left_neg a := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.add_left_neg _
  sub_eq_add_neg a b := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.sub_eq_add_neg _ _
  mul_assoc a b c := by apply Dual.ext <;> dsimp <;> constructive_ring
  mul_comm a b := by apply Dual.ext <;> dsimp <;> constructive_ring
  one_mul a := by apply Dual.ext <;> dsimp <;> constructive_ring
  mul_one a := by apply Dual.ext <;> dsimp <;> constructive_ring
  left_distrib a b c := by apply Dual.ext <;> dsimp <;> constructive_ring
  right_distrib a b c := by apply Dual.ext <;> dsimp <;> constructive_ring

def inl : RingHom R (Dual R) where
  toFun a := ⟨a, zero⟩
  map_zero := rfl
  map_one := rfl
  map_add a b := by
    apply Dual.ext
    · rfl
    · show zero = add zero zero; rw [LawfulCommRing.add_zero]
  map_mul a b := by
    apply Dual.ext
    · rfl
    · show zero = add (mul a zero) (mul zero b); constructive_ring

def fstHom : RingHom (Dual R) R where
  toFun x := x.fst
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

def map (φ : RingHom R S) : RingHom (Dual R) (Dual S) where
  toFun x := ⟨φ.toFun x.fst, φ.toFun x.snd⟩
  map_zero := by apply Dual.ext <;> exact φ.map_zero
  map_one := by
    apply Dual.ext
    · exact φ.map_one
    · exact φ.map_zero
  map_add a b := by apply Dual.ext <;> exact φ.map_add _ _
  map_mul a b := by
    apply Dual.ext
    · exact φ.map_mul _ _
    · show φ.toFun (add (mul a.fst b.snd) (mul a.snd b.fst)) =
        add (mul (φ.toFun a.fst) (φ.toFun b.snd)) (mul (φ.toFun a.snd) (φ.toFun b.fst))
      rw [φ.map_add, φ.map_mul, φ.map_mul]

@[expose] def eps : Dual R := ⟨zero, one⟩

end Ring
end Dual

section Deriv
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
open UPoly

private theorem C_zero_deriv : (C zero : UPoly R) = zero := by
  rw [← CHom_apply]; exact CHom.map_zero

def dualPerturb (P0 B : UPoly R) : UPoly (Dual R) :=
  add ((mapHom Dual.inl).toFun P0) (mul (C Dual.eps) ((mapHom Dual.inl).toFun B))

/-- Formal directional resultant derivative `[ε¹] sylRes m N C1 (P0 + ε · B)`. -/
@[expose] def sylResDeriv (m N : Nat) (C1 P0 B : UPoly R) : R :=
  (sylRes m N ((mapHom Dual.inl).toFun C1) (dualPerturb P0 B)).snd

private theorem mapHom_comp {A B C' : Type}
    [LawfulCommRing A] [DecidableEq A] [LawfulCommRing B] [DecidableEq B] [LawfulCommRing C'] [DecidableEq C']
    (ψ : RingHom B C') (φ : RingHom A B) (p : UPoly A) :
    (mapHom ψ).toFun ((mapHom φ).toFun p) = (mapHom (ψ.comp φ)).toFun p := by
  apply ext_coeffAt; intro k
  rw [coeffAt_mapHom, coeffAt_mapHom, coeffAt_mapHom]; rfl

private theorem mapHom_eq_of_toFun {A B : Type}
    [LawfulCommRing A] [DecidableEq A] [LawfulCommRing B] [DecidableEq B]
    (φ ψ : RingHom A B) (h : ∀ a, φ.toFun a = ψ.toFun a) (p : UPoly A) :
    (mapHom φ).toFun p = (mapHom ψ).toFun p := by
  apply ext_coeffAt; intro k
  rw [coeffAt_mapHom, coeffAt_mapHom, h]

private theorem mapHom_id (p : UPoly R) : (mapHom (RingHom.id R)).toFun p = p := by
  apply ext_coeffAt; intro k
  rw [coeffAt_mapHom]; rfl

theorem map_sylResDeriv {S : Type} [LawfulCommRing S] [DecidableEq S]
    (φ : RingHom R S) (m N : Nat) (C1 P0 B : UPoly R) :
    φ.toFun (sylResDeriv m N C1 P0 B) =
      sylResDeriv m N ((mapHom φ).toFun C1) ((mapHom φ).toFun P0) ((mapHom φ).toFun B) := by
  unfold sylResDeriv
  have h1 : (Dual.map φ).toFun (sylRes m N ((mapHom Dual.inl).toFun C1) (dualPerturb P0 B)) =
      sylRes m N ((mapHom (Dual.map φ)).toFun ((mapHom Dual.inl).toFun C1))
        ((mapHom (Dual.map φ)).toFun (dualPerturb P0 B)) :=
    map_sylRes (Dual.map φ) m N _ _
  have hComm : ∀ q : UPoly R,
      (mapHom (Dual.map φ)).toFun ((mapHom Dual.inl).toFun q) =
        (mapHom Dual.inl).toFun ((mapHom φ).toFun q) := fun q => by
    rw [mapHom_comp, mapHom_comp]
    refine mapHom_eq_of_toFun _ _ (fun a => ?_) q
    show (⟨φ.toFun a, φ.toFun zero⟩ : Dual S) = ⟨φ.toFun a, zero⟩
    rw [φ.map_zero]
  have hP : (mapHom (Dual.map φ)).toFun (dualPerturb P0 B) =
      dualPerturb ((mapHom φ).toFun P0) ((mapHom φ).toFun B) := by
    unfold dualPerturb
    rw [RingHom.map_add, RingHom.map_mul, mapHom_C, hComm P0, hComm B]
    have hEps : (Dual.map φ).toFun Dual.eps = Dual.eps := by
      show (⟨φ.toFun zero, φ.toFun one⟩ : Dual S) = ⟨zero, one⟩
      rw [φ.map_zero, φ.map_one]
    rw [hEps]
  rw [hComm C1, hP] at h1
  exact congrArg Dual.snd h1

/-- **Key Derivative-Factor Identity**: if `C1 = (X - C ζ) * Q`, `Q.natDeg ≤ m'`, `P0.natDeg ≤ N`,
    `B.natDeg ≤ N`, and `P0.eval ζ = 0`, then
    `sylResDeriv (m' + 1) N C1 P0 B = B.eval ζ * sylRes m' N Q P0`! -/
theorem sylResDeriv_of_factor (m' N : Nat) (ζ : R) (Q P0 B : UPoly R)
    (hQ : Q.natDeg ≤ m') (hP0 : P0.natDeg ≤ N) (hB : B.natDeg ≤ N) (hP0z : P0.eval ζ = zero) :
    sylResDeriv (m' + 1) N (mul (sub X (C ζ)) Q) P0 B = mul (B.eval ζ) (sylRes m' N Q P0) := by
  unfold sylResDeriv
  have hMapC1 : (mapHom (Dual.inl (R := R))).toFun (mul (sub X (C ζ)) Q) =
      mul (sub X (C (Dual.inl.toFun ζ))) ((mapHom Dual.inl).toFun Q) := by
    rw [RingHom.map_mul, RingHom.map_sub, mapHom_C]
    have hX : (mapHom (Dual.inl (R := R))).toFun X = X := eval₂_X _ _
    rw [hX]
  have hDegQ : ((mapHom (Dual.inl (R := R))).toFun Q).natDeg ≤ m' :=
    Nat.le_trans (natDeg_mapHom_le _ Q) hQ
  have hDegPert : (dualPerturb P0 B).natDeg ≤ N := by
    unfold dualPerturb
    apply natDeg_le_of_coeffAt; intro k hk
    rw [coeffAt_add, coeffAt_C_mul, coeffAt_mapHom, coeffAt_mapHom,
      P0.coeffAt_eq_zero_of_natDeg_lt (by omega), B.coeffAt_eq_zero_of_natDeg_lt (by omega),
      Dual.inl.map_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [hMapC1, sylRes_mul_X_sub m' N (Dual.inl.toFun ζ) _ _ hDegQ hDegPert]
  have hEvalPert : (dualPerturb P0 B).eval (Dual.inl.toFun ζ) = (⟨zero, B.eval ζ⟩ : Dual R) := by
    unfold dualPerturb
    show (evalHom (Dual.inl.toFun ζ)).toFun _ = _
    rw [RingHom.map_add, RingHom.map_mul, evalHom_apply, evalHom_apply, evalHom_apply,
      eval_C, eval_mapHom, eval_mapHom, hP0z]
    apply Dual.ext
    · show add zero (mul zero (B.eval ζ)) = zero; constructive_ring
    · show add zero (add (mul zero zero) (mul one (B.eval ζ))) = B.eval ζ; constructive_ring
  have hFstInl : ∀ q : UPoly R, (mapHom Dual.fstHom).toFun ((mapHom Dual.inl).toFun q) = q := fun q => by
    rw [mapHom_comp, mapHom_eq_of_toFun (Dual.fstHom.comp Dual.inl) (RingHom.id R) (fun _ => rfl) q, mapHom_id]
  have hFstRes : (sylRes m' N ((mapHom Dual.inl).toFun Q) (dualPerturb P0 B)).fst =
      sylRes m' N Q P0 := by
    change Dual.fstHom.toFun (sylRes m' N ((mapHom Dual.inl).toFun Q) (dualPerturb P0 B)) = _
    rw [map_sylRes Dual.fstHom, hFstInl Q]
    have hP1 : (mapHom Dual.fstHom).toFun (dualPerturb P0 B) = P0 := by
      unfold dualPerturb
      rw [RingHom.map_add, RingHom.map_mul, mapHom_C, hFstInl P0, hFstInl B]
      have hEps0 : Dual.fstHom.toFun (Dual.eps (R := R)) = zero := rfl
      have hC0 : (C zero : UPoly R) = zero := C_zero_deriv
      rw [hEps0, hC0, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [hP1]
  rw [hEvalPert]
  generalize sylRes m' N ((mapHom Dual.inl).toFun Q) (dualPerturb P0 B) = R_dual at hFstRes ⊢
  obtain ⟨r0, r1⟩ := R_dual
  dsimp at hFstRes
  subst hFstRes
  show add (mul zero r1) (mul (B.eval ζ) (sylRes m' N Q P0)) = _
  rw [LawfulCommRing.zero_mul, LawfulCommRing.zero_add]

/-- At ANY common root `ζ` of `(C1, P0)` (`1 ≤ m`), `sylResDeriv m N C1 P0 B = B.eval ζ * sylResDeriv m N C1 P0 1`! -/
theorem sylResDeriv_common_root {m N : Nat} {C1 P0 B : UPoly R} {ζ : R}
    (hm : 1 ≤ m) (hC1 : C1.natDeg ≤ m) (hP0 : P0.natDeg ≤ N) (hB : B.natDeg ≤ N)
    (hC1z : C1.eval ζ = zero) (hP0z : P0.eval ζ = zero) :
    sylResDeriv m N C1 P0 B = mul (B.eval ζ) (sylResDeriv m N C1 P0 one) := by
  obtain ⟨hDiv, hDeg⟩ := divXSub_spec C1 ζ
  rw [hC1z, C_zero_deriv, LawfulCommRing.zero_add] at hDiv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h1 : (one : UPoly R).natDeg ≤ N := by rw [natDeg_one]; exact Nat.zero_le N
  have hEval1 : (one : UPoly R).eval ζ = one := by rw [one_eq_C, eval_C]
  rw [hDiv,
    sylResDeriv_of_factor m' N ζ (divXSub C1 ζ) P0 B (by omega) hP0 hB hP0z,
    sylResDeriv_of_factor m' N ζ (divXSub C1 ζ) P0 one (by omega) hP0 h1 hP0z,
    hEval1, LawfulCommRing.one_mul]

private theorem max_le_of_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  if h : a ≤ b then rw [Nat.max_eq_right h]; exact hb
  else rw [Nat.max_eq_left (by omega)]; exact ha

/-- Weighted `DegFn` bound on `sylResDeriv m N C1 P0 B`. -/
theorem degFn_sylResDeriv_le {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0)
    (m N h_A h_B : Nat) (C1 P0 B : UPoly R)
    (hC1 : C1.wdeg w 1 ≤ h_A) (hP0 : P0.wdeg w 1 ≤ h_B) (hB : B.wdeg w 1 ≤ h_B)
    (hm : m ≤ h_A) (hN : N ≤ h_B) :
    w (sylResDeriv m N C1 P0 B) ≤ h_A * h_B := by
  let wD (x : Dual R) : Nat := max (w x.fst) (w x.snd)
  have hwD : DegFn wD := {
    zero := by
      show max (w zero) (w zero) = 0
      rw [hw.zero, Nat.max_self]
    add_le := fun x y =>
      max_le_of_le
        (Nat.le_trans (hw.add_le x.fst y.fst)
          (max_le_of_le
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))))
        (Nat.le_trans (hw.add_le x.snd y.snd)
          (max_le_of_le
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))
    mul_le := fun x y => by
      have h1 : w (mul x.fst y.fst) ≤ wD x + wD y :=
        Nat.le_trans (hw.mul_le x.fst y.fst)
          (Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      have h2a : w (mul x.fst y.snd) ≤ wD x + wD y :=
        Nat.le_trans (hw.mul_le x.fst y.snd)
          (Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      have h2b : w (mul x.snd y.fst) ≤ wD x + wD y :=
        Nat.le_trans (hw.mul_le x.snd y.fst)
          (Nat.add_le_add (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      exact max_le_of_le h1
        (Nat.le_trans (hw.add_le _ _) (max_le_of_le h2a h2b))
    neg_le := fun x =>
      max_le_of_le
        (Nat.le_trans (hw.neg_le x.fst) (Nat.le_max_left _ _))
        (Nat.le_trans (hw.neg_le x.snd) (Nat.le_max_right _ _))
  }
  have hwD1 : wD (one : Dual R) = 0 := by
    show max (w one) (w zero) = 0
    rw [hw1, hw.zero]; rfl
  have hC1D : ((mapHom Dual.inl).toFun C1).wdeg wD 1 ≤ h_A := by
    apply wdeg_le; intro k hk
    rw [coeffAt_mapHom] at hk ⊢
    have hcNe : coeffAt C1.coeffs k ≠ zero := fun e => hk (by rw [e]; rfl)
    have hle := Nat.le_trans (le_wdeg w 1 C1 k hcNe) hC1
    show max (w (coeffAt C1.coeffs k)) (w zero) + 1 * k ≤ h_A
    rw [hw.zero, Nat.max_zero]; exact hle
  have hPD : (dualPerturb P0 B).wdeg wD 1 ≤ h_B := by
    apply wdeg_le; intro k hk
    unfold dualPerturb at hk ⊢
    rw [coeffAt_add, coeffAt_C_mul, coeffAt_mapHom, coeffAt_mapHom] at hk ⊢
    have hCoeff : add (Dual.inl.toFun (coeffAt P0.coeffs k))
        (mul Dual.eps (Dual.inl.toFun (coeffAt B.coeffs k))) =
        (⟨coeffAt P0.coeffs k, coeffAt B.coeffs k⟩ : Dual R) := by
      apply Dual.ext
      · show add (coeffAt P0.coeffs k) (mul zero (coeffAt B.coeffs k)) = coeffAt P0.coeffs k
        constructive_ring
      · show add zero (add (mul zero zero) (mul one (coeffAt B.coeffs k))) = coeffAt B.coeffs k
        constructive_ring
    rw [hCoeff] at hk ⊢
    if hkB : k ≤ h_B then
      have hP0k : w (coeffAt P0.coeffs k) ≤ h_B - k := by
        if hz : coeffAt P0.coeffs k = zero then rw [hz, hw.zero]; omega
        else have := Nat.le_trans (le_wdeg w 1 P0 k hz) hP0; omega
      have hBk : w (coeffAt B.coeffs k) ≤ h_B - k := by
        if hz : coeffAt B.coeffs k = zero then rw [hz, hw.zero]; omega
        else have := Nat.le_trans (le_wdeg w 1 B k hz) hB; omega
      have hMax : max (w (coeffAt P0.coeffs k)) (w (coeffAt B.coeffs k)) ≤ h_B - k :=
        max_le_of_le hP0k hBk
      show max (w (coeffAt P0.coeffs k)) (w (coeffAt B.coeffs k)) + 1 * k ≤ h_B
      omega
    else
      exfalso
      have hzP : coeffAt P0.coeffs k = zero := by
        apply Decidable.byContradiction; intro hz
        have := Nat.le_trans (le_wdeg w 1 P0 k hz) hP0; omega
      have hzB : coeffAt B.coeffs k = zero := by
        apply Decidable.byContradiction; intro hz
        have := Nat.le_trans (le_wdeg w 1 B k hz) hB; omega
      rw [hzP, hzB] at hk; exact hk rfl
  have hMain := degFn_sylRes_le hwD hwD1 m N h_A h_B _ _ hC1D hPD hm hN
  exact Nat.le_trans (Nat.le_max_right _ _) hMain

end Deriv
end SylElim

namespace SylvesterDerivTests
open UPoly SylElim

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- Common root `ζ = 3` of `C1 = (X - 3)(X - 5)` (`ofList [15, -8, 1]`) and `P0 = X - 3`, `B = X + 2`:
    `sylResDeriv 2 1 C1 P0 B = B(3) * sylResDeriv 2 1 C1 P0 1 = 5 * (-2)`. -/
theorem inhabited_sylResDeriv_common_root :
    ∃ (m N : Nat) (C1 P0 B : UPoly Goldilocks) (ζ : Goldilocks),
      1 ≤ m ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧ B.natDeg ≤ N ∧
      C1.eval ζ = zero ∧ P0.eval ζ = zero ∧
      sylResDeriv m N C1 P0 B ≠ zero :=
  ⟨2, 1, ofList [g 15, neg (g 8), g 1], ofList [neg (g 3), g 1], ofList [g 2, g 1], g 3,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `#tooth`: dropping `P0.eval ζ = 0` invalidates `sylResDeriv_common_root`
    (`C1 = (X - 3)(X - 5)`, `P0 = X - 7`, `B = X`, `ζ = 3`). -/
theorem tooth_sylResDeriv_needs_P0_root :
    ∃ (m N : Nat) (C1 P0 B : UPoly Goldilocks) (ζ : Goldilocks),
      1 ≤ m ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧ B.natDeg ≤ N ∧ C1.eval ζ = zero ∧
      sylResDeriv m N C1 P0 B ≠ mul (B.eval ζ) (sylResDeriv m N C1 P0 one) :=
  ⟨2, 1, ofList [g 15, neg (g 8), g 1], ofList [neg (g 7), g 1], X, g 3,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

#verify_constructive SylElim.sylResDeriv_of_factor SylElim.sylResDeriv_common_root SylElim.degFn_sylResDeriv_le
#verify_constructive inhabited_sylResDeriv_common_root tooth_sylResDeriv_needs_P0_root
#tooth_pair SylElim.sylResDeriv_common_root vs tooth_sylResDeriv_needs_P0_root
#verify_inhabited SylElim.sylResDeriv_common_root inhabited_sylResDeriv_common_root

end SylvesterDerivTests
end Qsag
end
