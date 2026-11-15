module
/-
# Qsag.Coding.SimpleRootStratification — simple roots without factoring

`[CWYZ26]` §4.2 factors the explainer `Q = C·Π Qᵢ^{aᵢ}` and excludes the challenges at which
a factor has a repeated root. This file reaches the same conclusion — every root of `Q` on a
non-excluded line is a *simple* root of a polynomial of `(Y, Z)`-degree at most `deg_{Y,Z} Q` —
without factoring, by stratifying roots by multiplicity:

* `Poly3.lineSpec Q α β = Q(X, α + βX, Z) ∈ F[X][Z]`; a line is excluded when this vanishes.
  `lineSpec_zero_card_le`: at most `deg_{Y,Z} Q` lines are excluded (the paper's bound for its
  larger excluded set is `D²`).
* `UPoly.hasse_one_hasse`: `∂^{(1)} ∂^{(k)} = (k + 1)·∂^{(k+1)}` for Hasse derivatives.
* `Poly3.exists_multiplicity`: a root `P` of `Q` on a non-excluded line has a multiplicity
  `1 ≤ μ ≤ deg_Z Q`: `∂_Z^{(k)} Q` vanishes at `P` for `k < μ` and `∂_Z^{(μ)} Q` does not.
* `Poly3.simple_root_of_hasse`: if `1, …, deg_Z Q` are invertible in `F`, then `P` is a simple
  root of `R = ∂_Z^{(μ-1)} Q`, and `deg_{Y,Z} R ≤ deg_{Y,Z} Q` by `degYZ_hasseZ_le`.

So the family `{∂_Z^{(k)} Q : k < deg_Z Q}` plays the role of the factor system `{Rᵢ}`; it has
`deg_Z Q` members of degree at most `D` each, where the paper has `Σ hᵢ ≤ D`. A Yun squarefree
decomposition, Gauss contents and D5 refinement are not needed for this and are not here; they
would be needed to recover the paper's sharper `Σ hᵢ ≤ D` and to treat characteristic
`p ≤ deg_Z Q`.
-/

public import Qsag.Coding.UniversalHenselLift
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.SylvesterResultant
import all Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.HenselNumerators
import all Qsag.Coding.UniversalHenselLift
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Math.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

/-- A decidable predicate fails throughout `0..n`, or has a first point where it holds. -/
theorem first_or_none (p : Nat → Prop) [DecidablePred p] : ∀ n,
    (∀ k, k ≤ n → ¬ p k) ∨ ∃ μ, μ ≤ n ∧ p μ ∧ ∀ k, k < μ → ¬ p k
  | 0 =>
    if h : p 0 then .inr ⟨0, Nat.le_refl 0, h, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    else .inl (fun k hk => by
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact h)
  | n + 1 => by
    rcases first_or_none p n with hall | ⟨μ, hμ, hp, hlt⟩
    · if h : p (n + 1) then
        exact .inr ⟨n + 1, Nat.le_refl _, h, fun k hk => hall k (Nat.le_of_lt_succ hk)⟩
      else
        refine .inl (fun k hk => ?_)
        if hk' : k ≤ n then exact hall k hk'
        else
          obtain rfl : k = n + 1 := by omega
          exact h
    · exact .inr ⟨μ, Nat.le_succ_of_le hμ, hp, hlt⟩

namespace RingHom

theorem map_natCast {R S : Type} [LawfulCommRing R] [LawfulCommRing S] (φ : RingHom R S) :
    ∀ n : Nat, φ.toFun (CRing.natCast n) = CRing.natCast n
  | 0 => φ.map_zero
  | n + 1 => by
    rw [CRing.natCast_succ, CRing.natCast_succ, φ.map_add, map_natCast φ n, φ.map_one]

end RingHom

/-! ## Composition of Hasse derivatives -/

namespace UPoly

theorem gsUniHasse_eq_zero_of_length_le {S : Type} [LawfulCommRing S] (s : S) :
    ∀ (l : List S) (k : Nat), l.length ≤ k → gsUniHasse l k s = zero
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: cs, k + 1, h => by
    show add (gsUniHasse cs k s) (mul s (gsUniHasse cs (k + 1) s)) = zero
    rw [gsUniHasse_eq_zero_of_length_le s cs k (Nat.le_of_succ_le_succ h),
      gsUniHasse_eq_zero_of_length_le s cs (k + 1)
        (Nat.le_succ_of_le (Nat.le_of_succ_le_succ h)),
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

section
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- A coefficient list all of whose Hasse derivatives vanish at one point is zero. -/
theorem coeffs_zero_of_hasse_zero (l : List R) (s : R) (h : ∀ k, gsUniHasse l k s = zero) :
    ∀ j, coeffAt l j = zero := by
  have hT : (taylorShift s).toFun (ofList l) = zero := ext_coeffAt fun k => by
    show coeffAt (eval₂ CHom (add (C s) X) (ofList l)).coeffs k = _
    rw [eval₂_ofList, coeffs_zero, coeffAt_nil]
    exact (coeffAt_shift_list s l k).trans (h k)
  have h2 := congrArg (taylorShift (neg s)).toFun hT
  rw [taylorShift_neg_cancel, RingHom.map_zero] at h2
  intro j
  rw [← coeffAt_ofList, h2, coeffs_zero, coeffAt_nil]

/-- `p(X) ↦ p(X + T) ∈ R[X][T]`. -/
def shift2 : RingHom (UPoly R) (UPoly (UPoly R)) := eval₂Hom (CHom.comp CHom) (add (C X) X)

/-- The `k`-th Hasse derivative is the coefficient of `T^k` in `p(X + T)`. -/
theorem hasse_eq_coeff (k : Nat) (p : UPoly R) :
    hasse k p = coeffAt ((shift2 (R := R)).toFun p).coeffs k := by
  have h := coeffAt_shift_list (X : UPoly R) (p.coeffs.map C) k
  rw [List.map_map] at h
  exact h.symm

theorem hasse_add (k : Nat) (p q : UPoly R) :
    hasse k (add p q) = add (hasse k p) (hasse k q) := by
  rw [hasse_eq_coeff, hasse_eq_coeff, hasse_eq_coeff, RingHom.map_add, coeffAt_add]

theorem hasse_one_zero : hasse 1 (zero : UPoly R) = zero := by
  rw [hasse_eq_coeff, RingHom.map_zero, coeffs_zero, coeffAt_nil]

theorem hasse_one_C (c : R) : hasse 1 (C c) = zero := by
  rw [hasse_eq_coeff]
  show coeffAt (eval₂ (CHom.comp CHom) (add (C X) X) (C c)).coeffs 1 = zero
  rw [eval₂_C]
  exact coeffAt_C_succ (C c) 0

/-- The product rule against the variable. -/
theorem hasse_one_X_mul (p : UPoly R) : hasse 1 (mul X p) = add p (mul X (hasse 1 p)) := by
  have hX : (shift2 (R := R)).toFun X = add (C X) X := eval₂_X _ _
  have h0 : coeffAt ((shift2 (R := R)).toFun p).coeffs 0 = p :=
    (hasse_eq_coeff 0 p).symm.trans (Poly3.hasse_zero p)
  rw [hasse_eq_coeff, hasse_eq_coeff 1 p, RingHom.map_mul, hX, LawfulCommRing.right_distrib,
    coeffAt_add, coeffAt_C_mul, coeffAt_X_mul_succ, h0]
  exact LawfulCommRing.add_comm _ _

theorem hasse_one_hasse_list : ∀ (l : List R) (k : Nat),
    hasse 1 (gsUniHasse (l.map C) k (X : UPoly R)) =
      mul (CRing.natCast (k + 1)) (gsUniHasse (l.map C) (k + 1) X)
  | [], k => by
    show hasse 1 (zero : UPoly R) = mul _ zero
    rw [hasse_one_zero, LawfulCommRing.mul_zero]
  | c :: cs, 0 => by
    show hasse 1 (add (C c) (mul X (gsUniHasse (cs.map C) 0 X))) =
      mul one (add (gsUniHasse (cs.map C) 0 X) (mul X (gsUniHasse (cs.map C) 1 X)))
    rw [hasse_add, hasse_one_C, hasse_one_X_mul, hasse_one_hasse_list cs 0]
    show add zero (add _ (mul X (mul one _))) = _
    constructive_ring
  | c :: cs, k + 1 => by
    show hasse 1 (add (gsUniHasse (cs.map C) k X) (mul X (gsUniHasse (cs.map C) (k + 1) X))) =
      mul (CRing.natCast (k + 1 + 1)) (add (gsUniHasse (cs.map C) (k + 1) X)
        (mul X (gsUniHasse (cs.map C) (k + 1 + 1) X)))
    rw [hasse_add, hasse_one_X_mul, hasse_one_hasse_list cs k, hasse_one_hasse_list cs (k + 1),
      CRing.natCast_succ (k + 1)]
    generalize (CRing.natCast (k + 1) : UPoly R) = n
    constructive_ring

/-- **Composition of Hasse derivatives**: `∂^{(1)} ∂^{(k)} = (k + 1)·∂^{(k+1)}`. -/
theorem hasse_one_hasse (k : Nat) (p : UPoly R) :
    hasse 1 (hasse k p) = mul (CRing.natCast (k + 1)) (hasse (k + 1) p) :=
  hasse_one_hasse_list p.coeffs k

theorem natCast_ne_zero (n : Nat) (h : (CRing.natCast n : R) ≠ zero) :
    (CRing.natCast n : UPoly R) ≠ zero := fun e => h (by
  have h1 : (CRing.natCast n : UPoly R) = C (CRing.natCast n) :=
    ((CHom (R := R)).map_natCast n).symm
  have h2 := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) (h1.symm.trans e)
  simp only [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at h2
  exact h2)

end
end UPoly

/-! ## Excluded lines and multiplicities -/

namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

local instance : NoZeroDivisors (RatFunc F) := LawfulField.toNoZeroDivisors (RatFunc F)

/-- `Q(X, α + βX, Z) ∈ F[X][Z]`: the specialization of `Q` to the line `Y = α + βX`. -/
def lineSpec (Q : Poly3 F) (α β : F) : UPoly (UPoly F) := (mapHom (evalHom (line α β))).toFun Q

theorem coeffAt_lineSpec (Q : Poly3 F) (α β : F) (j : Nat) :
    coeffAt (lineSpec Q α β).coeffs j = (coeffAt Q.coeffs j).eval (line α β) :=
  coeffAt_mapHom _ _ _

/-- **Excluded lines.** A nonzero `Q` vanishes identically on at most `deg_{Y,Z} Q` lines
    `Y = α + βX`. -/
theorem lineSpec_zero_card_le (Q : Poly3 F) (hQ : Q ≠ zero) (E : List (F × F)) (hnd : E.Nodup)
    (hE : ∀ p ∈ E, lineSpec Q p.1 p.2 = zero) : E.length ≤ Q.degYZ := by
  let lineK : F × F → RatFunc F := fun p => (Frac.of (D := UPoly F)).toFun (line p.1 p.2)
  have hc : Q.lead ≠ zero := lead_ne_zero hQ
  have hcK : (mapHom (Frac.of (D := UPoly F))).toFun Q.lead ≠ zero := fun e => hc (map_of_inj _ e)
  have hroot : ∀ y ∈ E.map lineK,
      evalCoeffs ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).coeffs y = zero := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    rw [← eval_eq]
    show ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).eval
      ((Frac.of (D := UPoly F)).toFun (line p.1 p.2)) = zero
    have h1 : Q.lead.eval (line p.1 p.2) = zero := by
      have := congrArg (fun q : UPoly (UPoly F) => coeffAt q.coeffs Q.natDeg) (hE p hp)
      simp only [coeffAt_lineSpec, coeffs_zero, coeffAt_nil] at this
      exact this
    rw [eval_mapHom, h1, RingHom.map_zero]
  have hndK : (E.map lineK).Nodup :=
    List.pairwise_map.mpr (List.Pairwise.imp (fun {p q} hne e => hne (by
      have := line_inj (Frac.of_injective e)
      exact Prod.ext this.1 this.2)) hnd)
  have hcount := gs_formal_root_bound ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).natDeg
    ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).coeffs (E.map lineK)
    (by show _ ≤ ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).coeffs.length - 1 + 1; omega)
    (Poly2.exists_ne_zero_of_ne_zero hcK) hndK hroot
  rw [List.length_map] at hcount
  have h2 := natDeg_mapHom_le (Frac.of (D := UPoly F)) Q.lead
  have h3 := le_wdeg natDeg 1 Q Q.natDeg hc
  have h3' : Q.lead.natDeg + 1 * Q.natDeg ≤ Q.degYZ := h3
  omega

theorem evalAffineLine_hasseZ (k : Nat) (Q : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine (hasseZ k Q) α β P =
      gsUniHasse (Q.coeffs.map (evalHom (line α β)).toFun) k P := eval₂_hasse _ _ _ _

/-- **Multiplicity of a root on a non-excluded line.** If `Q(X, α + βX, Z) ≠ 0` and
    `Q(X, α + βX, P(X)) = 0`, there is `1 ≤ μ ≤ deg_Z Q` with `∂_Z^{(k)} Q` vanishing at `P`
    for all `k < μ` and `∂_Z^{(μ)} Q` not vanishing there. No assumption on the
    characteristic. -/
theorem exists_multiplicity (Q : Poly3 F) (α β : F) (P : UPoly F)
    (hnv : lineSpec Q α β ≠ zero) (hroot : evalAffineLine Q α β P = zero) :
    ∃ μ, 1 ≤ μ ∧ μ ≤ Q.degZ ∧ (∀ k, k < μ → evalAffineLine (hasseZ k Q) α β P = zero) ∧
      evalAffineLine (hasseZ μ Q) α β P ≠ zero := by
  have hhigh : ∀ k, Q.coeffs.length ≤ k → evalAffineLine (hasseZ k Q) α β P = zero :=
    fun k hk => by
      rw [evalAffineLine_hasseZ]
      exact gsUniHasse_eq_zero_of_length_le P _ k (by rw [List.length_map]; exact hk)
  rcases first_or_none (fun k => evalAffineLine (hasseZ k Q) α β P ≠ zero) Q.coeffs.length
    with hall | ⟨μ, hμ, hp, hlt⟩
  · exfalso
    apply hnv
    have hz : ∀ k, gsUniHasse (Q.coeffs.map (evalHom (line α β)).toFun) k P = zero := fun k => by
      rw [← evalAffineLine_hasseZ]
      if hk : k ≤ Q.coeffs.length then exact Decidable.not_not.mp (hall k hk)
      else exact hhigh k (by omega)
    have hc := coeffs_zero_of_hasse_zero _ P hz
    exact ext_coeffAt fun j => by
      rw [coeffAt_lineSpec, coeffs_zero, coeffAt_nil]
      have := hc j
      rwa [RingHom.coeffAt_map] at this
  · refine ⟨μ, Nat.pos_of_ne_zero (fun e => ?_), ?_, fun k hk => Decidable.not_not.mp (hlt k hk),
      hp⟩
    · subst e
      apply hp
      show evalAffineLine (hasse 0 Q) α β P = zero
      rw [hasse_zero]; exact hroot
    · have : μ < Q.coeffs.length := Nat.lt_of_not_le (fun hle => hp (hhigh μ hle))
      show μ ≤ Q.coeffs.length - 1
      omega

/-- **Simple roots without factoring** (the role of `[CWYZ26]` Lemma 4.3 when
    `1, …, deg_Z Q` are invertible). On a non-excluded line every root `P` of `Q` is a simple
    root of the Hasse derivative `R = ∂_Z^{(μ-1)} Q` for its multiplicity `μ`:
    `R(X, α + βX, P) = 0` and `∂_Z R(X, α + βX, P) ≠ 0`. -/
theorem simple_root_of_hasse (Q : Poly3 F)
    (hchar : ∀ k, 1 ≤ k → k ≤ Q.degZ → (CRing.natCast k : F) ≠ zero) (α β : F) (P : UPoly F)
    (hnv : lineSpec Q α β ≠ zero) (hroot : evalAffineLine Q α β P = zero) :
    ∃ μ, 1 ≤ μ ∧ μ ≤ Q.degZ ∧ evalAffineLine (hasseZ (μ - 1) Q) α β P = zero ∧
      evalAffineLine (hasseZ 1 (hasseZ (μ - 1) Q)) α β P ≠ zero := by
  obtain ⟨μ, h1, h2, h3, h4⟩ := exists_multiplicity Q α β P hnv hroot
  refine ⟨μ, h1, h2, h3 (μ - 1) (by omega), ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, μ = m + 1 := ⟨μ - 1, by omega⟩
  show (affineLineHom α β P).toFun (hasse 1 (hasse m Q)) ≠ zero
  rw [hasse_one_hasse, RingHom.map_mul, RingHom.map_natCast]
  exact mul_ne_zero' (natCast_ne_zero (m + 1) (hchar (m + 1) h1 h2)) h4

end Poly3

/-! ## Witnesses -/

namespace Poly3.StratTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `Q = (Z - X)²`, with the double root `P = X` on every line. -/
def qDouble : Poly3 Goldilocks :=
  ofList [ofList [ofList [g 0, g 0, g 1]], ofList [ofList [g 0, neg (g 2)]], one]

/-- `Q = Z·(Y - X)`, which vanishes identically on the line `Y = X`. -/
def qLine : Poly3 Goldilocks := ofList [zero, ofList [ofList [g 0, neg (g 1)], one]]

/-- The hypotheses of `simple_root_of_hasse` hold together for the double root of `(Z - X)²`. -/
theorem inhabited_simple_root_of_hasse :
    ∃ (Q : Poly3 Goldilocks) (α β : Goldilocks) (P : UPoly Goldilocks),
      (∀ k, 1 ≤ k → k ≤ Q.degZ → (CRing.natCast k : Goldilocks) ≠ zero) ∧
      lineSpec Q α β ≠ zero ∧ evalAffineLine Q α β P = zero :=
  ⟨qDouble, g 3, g 5, X, fun k h1 h2 => by
      have hk : k = 1 ∨ k = 2 := by
        have : qDouble.degZ = 2 := by decide +kernel
        omega
      rcases hk with rfl | rfl <;> decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- The double root is found at multiplicity two: `∂_Z Q = 2(Z - X)` vanishes at `P = X` and
    its derivative `2` does not. -/
theorem double_root_stratum :
    evalAffineLine (hasseZ 1 qDouble) (g 3) (g 5) X = zero ∧
      evalAffineLine (hasseZ 1 (hasseZ 1 qDouble)) (g 3) (g 5) X ≠ zero := by
  decide +kernel

/-- The non-vanishing hypothesis is needed: `Q = Z·(Y - X)` has every `P` as a root on the
    line `Y = X`, and none of them is a simple root of a Hasse derivative of `Q`. -/
theorem tooth_simple_root_needs_nonvanishing :
    ∃ (Q : Poly3 Goldilocks) (α β : Goldilocks) (P : UPoly Goldilocks),
      evalAffineLine Q α β P = zero ∧
      ¬ ∃ μ, 1 ≤ μ ∧ μ ≤ Q.degZ ∧ evalAffineLine (hasseZ (μ - 1) Q) α β P = zero ∧
        evalAffineLine (hasseZ 1 (hasseZ (μ - 1) Q)) α β P ≠ zero :=
  ⟨qLine, g 0, g 1, X, by decide +kernel, fun ⟨μ, h1, h2, _, h4⟩ => by
    have hd : qLine.degZ = 1 := by decide +kernel
    rw [hd] at h2
    have hμ : μ = 1 := Nat.le_antisymm h2 h1
    subst hμ
    exact h4 (by decide +kernel)⟩

#verify_constructive simple_root_of_hasse exists_multiplicity lineSpec_zero_card_le
#verify_constructive UPoly.hasse_one_hasse double_root_stratum
#verify_constructive tooth_simple_root_needs_nonvanishing
#tooth_pair simple_root_of_hasse vs tooth_simple_root_needs_nonvanishing
#verify_inhabited simple_root_of_hasse inhabited_simple_root_of_hasse

end Poly3.StratTests

end Qsag
end
