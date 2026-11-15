module
/-
# Qsag.Coding.TrivariateGsExplainer — `[CWYZ26]` Lemma 4.2

For received words `f, g` on a domain `Dm`, a nonzero `Q ∈ F[X][Y][Z]` is found by Gaussian
elimination over `F` with the following property: for every challenge `(α, β)` and every `P`
of degree at most `d` agreeing with the fold `f + (α + βX)·g` on enough points of `Dm`,
`Q(X, α + βX, P(X)) = 0`.

* `shiftHom z b₀ b₁ : Q ↦ Q(z + X, Y, b₀ + b₁Y + Z)` and the constraint functionals `cons`:
  `Q` has multiplicity `m` along `(z, f z + Y·g z)` when every coefficient of `X^r Z^s`,
  `r + s < m`, of the shifted polynomial vanishes (equation (4.3)).
* `inPow_affine_of_cons`: the constraints at `z` give `(X - z)^m ∣ Q(X, α + βX, P(X))`
  whenever `P` agrees with the fold at `z`.
* `evalAffineLine_eq_zero_of_agree`: with more than `deg_{1,1,d} Q / m` agreement points the
  specialization vanishes identically.
* `explainer`, `explainer_spec`, `exists_trivariate_affine_explainer`: the solver output and
  its degree bounds, under the count hypothesis (4.5) `n · Σ_s (m-s)(D-s+1) < Σ_j (W-dj)(D-j+1)`.

Not proved here: `deg_Z Q ≥ 1`. It is not needed downstream, since a `Z`-free `Q` vanishes on
the line `Y = α + βX` only for excluded pairs.
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

/-! ## Coefficient functionals and linear combinations in `F[X][Y][Z]` -/

namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

/-- Coefficient of `X^i Y^t Z^j`. -/
def coeff3 (Q : Poly3 F) (i t j : Nat) : F :=
  coeffAt (coeffAt (coeffAt Q.coeffs j).coeffs t).coeffs i

/-- `F`-linear functionals on `F[X][Y][Z]`. -/
structure IsLin (ℓ : Poly3 F → F) : Prop where
  map_add : ∀ a b, ℓ (add a b) = add (ℓ a) (ℓ b)
  map_zero : ℓ zero = zero
  map_smul : ∀ x a, ℓ (mul (C3 x) a) = mul x (ℓ a)

theorem isLin_coeff3 (i t j : Nat) : IsLin (fun Q : Poly3 F => coeff3 Q i t j) where
  map_add a b := by
    show coeffAt (coeffAt (coeffAt (add a b).coeffs j).coeffs t).coeffs i = _
    rw [coeffAt_add, coeffAt_add, coeffAt_add]; rfl
  map_zero := by
    show coeffAt (coeffAt (coeffAt (zero : Poly3 F).coeffs j).coeffs t).coeffs i = zero
    rw [coeffs_zero, coeffAt_nil, coeffs_zero, coeffAt_nil, coeffs_zero, coeffAt_nil]
  map_smul x a := by
    show coeffAt (coeffAt (coeffAt (mul (C (C (C x))) a).coeffs j).coeffs t).coeffs i = _
    rw [coeffAt_C_mul, coeffAt_C_mul, coeffAt_C_mul]; rfl

/-- `Σ_k x_k · g_k`. -/
def comb : List F → List (Poly3 F) → Poly3 F
  | x :: xs, g :: gs => add (mul (C3 x) g) (comb xs gs)
  | [], _ => zero
  | _ :: _, [] => zero

theorem lin_comb {ℓ : Poly3 F → F} (h : IsLin ℓ) : ∀ (xs : List F) (gs : List (Poly3 F)),
    ℓ (comb xs gs) = dotVec (gs.map ℓ) xs
  | [], gs => by
    show ℓ zero = _
    rw [h.map_zero]; cases gs <;> rfl
  | _ :: _, [] => h.map_zero
  | x :: xs, g :: gs => by
    show ℓ (add (mul (C3 x) g) (comb xs gs)) = add (mul (ℓ g) x) (dotVec (gs.map ℓ) xs)
    rw [h.map_add, h.map_smul, lin_comb h xs gs, LawfulCommRing.mul_comm]

theorem degFn_comb_le {δ : Poly3 F → Nat} (hδ : DegFn δ) (hC : ∀ x : F, δ (C3 x) = 0)
    (B : Nat) : ∀ (xs : List F) (gs : List (Poly3 F)), (∀ g ∈ gs, δ g ≤ B) →
      δ (comb xs gs) ≤ B
  | [], _, _ => by show δ zero ≤ B; rw [hδ.zero]; exact Nat.zero_le _
  | _ :: _, [], _ => by show δ zero ≤ B; rw [hδ.zero]; exact Nat.zero_le _
  | x :: xs, g :: gs, h => by
    show δ (add (mul (C3 x) g) (comb xs gs)) ≤ B
    have h1 := hδ.add_le (mul (C3 x) g) (comb xs gs)
    have h2 := hδ.mul_le (C3 x) g
    have h3 := h g (.head _)
    have h4 := degFn_comb_le hδ hC B xs gs (fun g' hg' => h g' (.tail _ hg'))
    rw [hC x] at h2
    omega

/-- `X^i Y^t Z^j`. -/
def mono3 (i t j : Nat) : Poly3 F := ofList (monomial j (Poly2.mono (K := F) i t))

theorem coeffAt_mono3 (i t j k : Nat) :
    coeffAt (mono3 (F := F) i t j).coeffs k = if k = j then Poly2.mono i t else zero := by
  show coeffAt (ofList _).coeffs k = _
  rw [coeffAt_ofList, coeffAt_monomial]

theorem coeff3_mono3_self (i t j : Nat) : coeff3 (mono3 (F := F) i t j) i t j = one := by
  show coeffAt (coeffAt (coeffAt (mono3 (F := F) i t j).coeffs j).coeffs t).coeffs i = one
  rw [coeffAt_mono3]; simp only [↓reduceIte]
  exact Poly2.coeff2_mono_self i t

theorem coeff3_mono3_ne (p q : Nat × Nat × Nat) (h : q ≠ p) :
    coeff3 (mono3 (F := F) p.1 p.2.1 p.2.2) q.1 q.2.1 q.2.2 = zero := by
  show coeffAt (coeffAt (coeffAt (mono3 (F := F) p.1 p.2.1 p.2.2).coeffs q.2.2).coeffs
    q.2.1).coeffs q.1 = zero
  rw [coeffAt_mono3]
  if hj : q.2.2 = p.2.2 then
    simp only [hj, ↓reduceIte]
    refine Poly2.coeff2_mono_ne p.1 p.2.1 q.1 q.2.1 (fun e => h ?_)
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    exact Prod.ext e1 (Prod.ext e2 hj)
  else
    simp only [hj, ↓reduceIte]
    rw [coeffs_zero, coeffAt_nil, coeffs_zero, coeffAt_nil]

/-- Distinct monomials are linearly independent over `F`. -/
theorem eq_zero_of_comb_mono3 : ∀ (ps : List (Nat × Nat × Nat)) (xs : List F), ps.Nodup →
    xs.length = ps.length →
    (∀ q : Nat × Nat × Nat, dotVec ((ps.map (fun p => mono3 (F := F) p.1 p.2.1 p.2.2)).map
      (fun g => coeff3 g q.1 q.2.1 q.2.2)) xs = zero) → ∀ c ∈ xs, c = zero
  | [], [], _, _, _, c, hc => by cases hc
  | [], _ :: _, _, hl, _, _, _ => by cases hl
  | _ :: _, [], _, hl, _, _, _ => by cases hl
  | p :: ps, x :: xs, hnd, hl, h, c, hc => by
    have hp := List.pairwise_cons.mp hnd
    have hx : x = zero := by
      have hz : dotVec ((ps.map (fun q => mono3 (F := F) q.1 q.2.1 q.2.2)).map
          (fun g => coeff3 g p.1 p.2.1 p.2.2)) xs = zero := by
        apply Poly2.dotVec_zero_left
        intro r hr
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
        exact coeff3_mono3_ne q p (fun e => hp.1 q hq e)
      have h1 : add (mul (coeff3 (mono3 (F := F) p.1 p.2.1 p.2.2) p.1 p.2.1 p.2.2) x)
          (dotVec ((ps.map (fun q => mono3 (F := F) q.1 q.2.1 q.2.2)).map
            (fun g => coeff3 g p.1 p.2.1 p.2.2)) xs) = zero := h p
      rw [hz, coeff3_mono3_self, LawfulCommRing.one_mul, LawfulCommRing.add_zero] at h1
      exact h1
    cases hc with
    | head => exact hx
    | tail _ hc' =>
      refine eq_zero_of_comb_mono3 ps xs hp.2 (Nat.succ.inj hl) (fun q => ?_) c hc'
      have h1 : add (mul (coeff3 (mono3 (F := F) p.1 p.2.1 p.2.2) q.1 q.2.1 q.2.2) x)
          (dotVec ((ps.map (fun q => mono3 (F := F) q.1 q.2.1 q.2.2)).map
            (fun g => coeff3 g q.1 q.2.1 q.2.2)) xs) = zero := h q
      rwa [hx, LawfulCommRing.mul_zero, LawfulCommRing.zero_add] at h1

theorem degYZ_mono3_le (i t j : Nat) : degYZ (mono3 (F := F) i t j) ≤ t + j := by
  apply wdeg_le
  intro k hk
  rw [coeffAt_mono3] at hk ⊢
  if hkj : k = j then
    subst hkj
    simp only [↓reduceIte] at hk ⊢
    have := Poly2.natDeg_mono_le (K := F) i t
    omega
  else
    simp only [hkj, ↓reduceIte] at hk
    exact absurd rfl hk

theorem deg11d_mono3_le (d i t j : Nat) : deg11d d (mono3 (F := F) i t j) ≤ i + t + d * j := by
  apply wdeg_le
  intro k hk
  rw [coeffAt_mono3] at hk ⊢
  if hkj : k = j then
    subst hkj
    simp only [↓reduceIte] at hk ⊢
    have : (Poly2.mono (K := F) i t).wdeg natDeg 1 ≤ i + t := Poly2.tdeg_mono_le i t
    omega
  else
    simp only [hkj, ↓reduceIte] at hk
    exact absurd rfl hk

/-! ## The shift and the multiplicity constraints -/

/-- `b₀ + b₁ Y ∈ F[X][Y]`. -/
def yLine (b₀ b₁ : F) : UPoly (UPoly F) := ofList [C b₀, C b₁]

theorem natDeg_yLine_le (b₀ b₁ : F) : (yLine b₀ b₁).natDeg ≤ 1 := by
  have := trimPoly_length_le [C b₀, C b₁]
  show (trimPoly [C b₀, C b₁]).length - 1 ≤ 1
  simp only [List.length_cons, List.length_nil] at this; omega

/-- `Q(X, Y, Z) ↦ Q(z + X, Y, b₀ + b₁Y + Z)`. -/
def shiftHom (z b₀ b₁ : F) : RingHom (Poly3 F) (Poly3 F) :=
  (taylorShift (yLine b₀ b₁)).comp (mapHom (mapHom (taylorShift z)))

theorem shiftHom_C3 (z b₀ b₁ x : F) : (shiftHom z b₀ b₁).toFun (C3 x) = C3 x := by
  show (taylorShift (yLine b₀ b₁)).toFun
    ((mapHom (mapHom (taylorShift z))).toFun (C (C (C x)))) = C (C (C x))
  rw [mapHom_C, mapHom_C, taylorShift_C, taylorShift_C]

theorem degYZ_shiftHom_le (z b₀ b₁ : F) (Q : Poly3 F) :
    ((shiftHom z b₀ b₁).toFun Q).degYZ ≤ Q.degYZ := by
  have hX : (X : Poly3 F).wdeg natDeg 1 ≤ 1 := by
    have := wdeg_X_le (R := UPoly (UPoly F)) natDeg 1
    rw [natDeg_one] at this; omega
  have hs : (add (C (yLine b₀ b₁)) (X : Poly3 F)).wdeg natDeg 1 ≤ 1 := by
    have h1 := (degFn_degYZ (K := F)).add_le (C (yLine b₀ b₁)) X
    have h2 : (C (yLine b₀ b₁) : Poly3 F).wdeg natDeg 1 ≤ (yLine b₀ b₁).natDeg :=
      wdeg_C_le natDeg 1 _
    have h3 := natDeg_yLine_le b₀ b₁
    have h1' : (add (C (yLine b₀ b₁)) (X : Poly3 F)).wdeg natDeg 1 ≤
        max ((C (yLine b₀ b₁) : Poly3 F).wdeg natDeg 1) ((X : Poly3 F).wdeg natDeg 1) := h1
    omega
  have hb := degFn_eval₂_le (degFn_degYZ (K := F)) CHom natDeg (fun c => wdeg_C_le natDeg 1 c)
    (add (C (yLine b₀ b₁)) X) 1 hs ((mapHom (mapHom (taylorShift z))).toFun Q)
  exact Nat.le_trans hb (wdeg_mapHom_mapHom_le (taylorShift z) Q)

/-- The constraint functional: the coefficient of `X^r Y^t Z^s` in the shifted polynomial. -/
def cons (z b₀ b₁ : F) (r t s : Nat) (Q : Poly3 F) : F :=
  coeff3 ((shiftHom z b₀ b₁).toFun Q) r t s

theorem isLin_cons (z b₀ b₁ : F) (r t s : Nat) : IsLin (cons z b₀ b₁ r t s) where
  map_add a b := by
    show coeff3 ((shiftHom z b₀ b₁).toFun (add a b)) r t s = _
    rw [RingHom.map_add]; exact (isLin_coeff3 r t s).map_add _ _
  map_zero := by
    show coeff3 ((shiftHom z b₀ b₁).toFun zero) r t s = _
    rw [RingHom.map_zero]; exact (isLin_coeff3 r t s).map_zero
  map_smul x a := by
    show coeff3 ((shiftHom z b₀ b₁).toFun (mul (C3 x) a)) r t s = _
    rw [RingHom.map_mul, shiftHom_C3]; exact (isLin_coeff3 r t s).map_smul _ _

/-- `Q(X, Y, Z) ↦ Q(X - z, α + βX, Zv)`. -/
def unshiftHom (z α β : F) (Zv : UPoly F) : RingHom (Poly3 F) (UPoly F) :=
  eval₂Hom (eval₂Hom (taylorShift (neg z)) (line α β)) Zv

/-- Undoing the shift along the line: `Q(z + (X - z), α + βX, b₀ + b₁(α + βX) + Zv)` with
    `Zv = P - b₀ - b₁(α + βX)` is `Q(X, α + βX, P)`. -/
theorem unshift_shift (z b₀ b₁ α β : F) (P : UPoly F) (Q : Poly3 F) :
    (unshiftHom z α β (sub P (add (C b₀) (mul (line α β) (C b₁))))).toFun
      ((shiftHom z b₀ b₁).toFun Q) = evalAffineLine Q α β P := by
  let Zv : UPoly F := sub P (add (C b₀) (mul (line α β) (C b₁)))
  let mid : RingHom (UPoly (UPoly F)) (UPoly F) := eval₂Hom (taylorShift (neg z)) (line α β)
  have hmid : ∀ c : UPoly (UPoly F),
      mid.toFun ((mapHom (taylorShift z)).toFun c) = (evalHom (line α β)).toFun c := by
    intro c
    refine hom_ext (mid.comp (mapHom (taylorShift z))) (evalHom (line α β)) (fun a => ?_) ?_ c
    · show mid.toFun ((mapHom (taylorShift z)).toFun (C a)) = (C a).eval (line α β)
      rw [mapHom_C, eval_C]
      show eval₂ (taylorShift (neg z)) (line α β) (C ((taylorShift z).toFun a)) = a
      rw [eval₂_C, taylorShift_neg_cancel]
    · show mid.toFun ((mapHom (taylorShift z)).toFun X) = (X : UPoly (UPoly F)).eval (line α β)
      rw [mapHom_X, eval_X]
      exact eval₂_X _ _
  refine hom_ext ((unshiftHom z α β Zv).comp (shiftHom z b₀ b₁)) (affineLineHom α β P)
    (fun c => ?_) ?_ Q
  · show eval₂ mid Zv ((taylorShift (yLine b₀ b₁)).toFun
      ((mapHom (mapHom (taylorShift z))).toFun (C c))) = eval₂ (evalHom (line α β)) P (C c)
    rw [mapHom_C, taylorShift_C, eval₂_C, eval₂_C]
    exact hmid c
  · show eval₂ mid Zv ((taylorShift (yLine b₀ b₁)).toFun
      ((mapHom (mapHom (taylorShift z))).toFun X)) = eval₂ (evalHom (line α β)) P X
    rw [mapHom_X, taylorShift_X, eval₂_X]
    show (eval₂Hom mid Zv).toFun (add (C (yLine b₀ b₁)) X) = P
    rw [RingHom.map_add]
    show add (eval₂ mid Zv (C (yLine b₀ b₁))) (eval₂ mid Zv X) = P
    rw [eval₂_C, eval₂_X]
    have hy : mid.toFun (yLine b₀ b₁) =
        add (C b₀) (mul (line α β) (add (C b₁) (mul (line α β) zero))) := by
      show eval₂ (taylorShift (neg z)) (line α β) (ofList [C b₀, C b₁]) = _
      rw [eval₂_ofList]
      show add ((taylorShift (neg z)).toFun (C b₀)) (mul (line α β)
        (add ((taylorShift (neg z)).toFun (C b₁)) (mul (line α β) zero))) = _
      rw [taylorShift_C, taylorShift_C]
    rw [hy]
    show add _ (sub P (add (C b₀) (mul (line α β) (C b₁)))) = P
    constructive_ring

theorem eval_line (α β z : F) : (line α β).eval z = add α (mul β z) := by
  rw [eval_eq]
  show evalCoeffs (trimPoly [α, β]) z = _
  rw [evalCoeffs_trimPoly]
  show add α (mul z (add β (mul z zero))) = _
  constructive_ring

/-- A polynomial vanishing at `z` is a multiple of `X - z`. -/
theorem exists_mul_of_eval_eq_zero (p : UPoly F) (z : F) (h : p.eval z = zero) :
    ∃ w, p = mul (add (C (neg z)) X) w := by
  have h0 : coeffAt ((taylorShift z).toFun p).coeffs 0 = zero := by
    rw [← eval_zero_eq, eval_taylorShift, LawfulCommRing.add_zero, h]
  have hsplit := eq_C_add_X_mul ((taylorShift z).toFun p)
  rw [h0] at hsplit
  refine ⟨(taylorShift (neg z)).toFun (shiftDown ((taylorShift z).toFun p)), ?_⟩
  have := congrArg (taylorShift (neg z)).toFun hsplit
  rw [taylorShift_neg_cancel, RingHom.map_add, RingHom.map_mul, taylorShift_C, taylorShift_X,
    ← CHom_apply, CHom.map_zero, LawfulCommRing.zero_add] at this
  exact this

/-- **Multiplicity gives divisibility** (the substitution step of `[CWYZ26]` Lemma 4.2).
    If `Q` satisfies the order-`m` constraints at `z` for the values `b₀ = f z`, `b₁ = g z`,
    and `P(z) = b₀ + (α + βz)·b₁`, then `(X - z)^m` divides `Q(X, α + βX, P(X))`. -/
theorem inPow_affine_of_cons (Q : Poly3 F) (z b₀ b₁ α β : F) (P : UPoly F) (m : Nat)
    (hcons : ∀ r t s, r + s < m → cons z b₀ b₁ r t s Q = zero)
    (hagree : P.eval z = add b₀ (mul (add α (mul β z)) b₁)) :
    InPow (add (C (neg z)) X) m (evalAffineLine Q α β P) := by
  have hZ : (sub P (add (C b₀) (mul (line α β) (C b₁)))).eval z = zero := by
    show (evalHom z).toFun (sub P (add (C b₀) (mul (line α β) (C b₁)))) = zero
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, evalHom_apply, evalHom_apply,
      evalHom_apply, evalHom_apply, eval_C, eval_C, eval_line, hagree]
    constructive_ring
  obtain ⟨w, hw⟩ := exists_mul_of_eval_eq_zero _ z hZ
  rw [← unshift_shift z b₀ b₁ α β P Q, hw]
  show InPow _ m (evalCoeffs (((shiftHom z b₀ b₁).toFun Q).coeffs.map
    (eval₂Hom (taylorShift (neg z)) (line α β)).toFun) (mul (add (C (neg z)) X) w))
  apply InPow.evalCoeffs_graded
  intro s
  rw [RingHom.coeffAt_map]
  show InPow _ (m - s) (evalCoeffs ((coeffAt ((shiftHom z b₀ b₁).toFun Q).coeffs s).coeffs.map
    (taylorShift (neg z)).toFun) (line α β))
  apply InPow.evalCoeffs_all
  intro t
  rw [RingHom.coeffAt_map]
  show InPow _ (m - s) (evalCoeffs
    ((coeffAt (coeffAt ((shiftHom z b₀ b₁).toFun Q).coeffs s).coeffs t).coeffs.map
      (CHom (R := F)).toFun) (add (C (neg z)) X))
  apply InPow.evalCoeffs_low
  intro r hr
  exact hcons r t s (by omega)

/-! ## Enough agreement forces the specialization to vanish -/

/-- The same polynomial in the subtype presentation used by the bivariate decoder. -/
def toGs (p : UPoly F) : GsUniPoly F := ⟨p.coeffs, p.trimmed⟩

theorem toGs_mul (a b : UPoly F) : toGs (mul a b) = mul (toGs a) (toGs b) := by rfl

theorem toGs_npow (u : UPoly F) : ∀ k : Nat, toGs (CRing.npow u k) = gsPow (toGs u) k
  | 0 => Subtype.ext (by
    show trimPoly [(one : F)] = [one]
    simp [trimPoly, LawfulField.one_ne_zero])
  | k + 1 => by
    show toGs (mul (CRing.npow u k) u) = mul (toGs u) (gsPow (toGs u) k)
    rw [toGs_mul, toGs_npow u k, LawfulCommRing.mul_comm]

theorem toGs_linear (z : F) : toGs (add (C (neg z)) X) = gsLinear z := by
  have e : add (C (neg z)) X = (⟨[neg z, one], gsLinear_trimmed z⟩ : UPoly F) := by
    apply ext_coeffAt
    intro k
    rw [coeffAt_add]
    have eX : coeffAt (X : UPoly F).coeffs k = coeffAt [zero, one] k := coeffAt_ofList _ k
    rw [eX]
    cases k with
    | zero => rw [coeffAt_C_zero]; exact LawfulCommRing.add_zero _
    | succ k =>
      rw [coeffAt_C_succ, LawfulCommRing.zero_add]
      cases k <;> rfl
  rw [e]; rfl

/-- **Agreement forces vanishing** (`[CWYZ26]` Lemma 4.2, third item). If `Q` satisfies the
    order-`m` constraints at the distinct points `zs`, `P` has degree at most `d` and agrees
    with the fold `f + (α + βX)·g` on `zs`, and `deg_{1,1,d} Q < m·|zs|`, then
    `Q(X, α + βX, P(X)) = 0`. -/
theorem evalAffineLine_eq_zero_of_agree (Q : Poly3 F) (m d : Nat) (f g : F → F) (α β : F)
    (P : UPoly F) (zs : List F) (hnd : zs.Nodup)
    (hcons : ∀ z ∈ zs, ∀ r t s, r + s < m → cons z (f z) (g z) r t s Q = zero)
    (hagree : ∀ z ∈ zs, P.eval z = add (f z) (mul (add α (mul β z)) (g z)))
    (hP : P.natDeg ≤ d) (hdeg : Q.deg11d d < m * zs.length) :
    evalAffineLine Q α β P = zero := by
  if hz : evalAffineLine Q α β P = zero then exact hz
  else
    exfalso
    have hne : (toGs (evalAffineLine Q α β P)).val ≠ [] := fun e =>
      hz ((eq_zero_iff _).mpr e)
    have hdiv : ∀ x ∈ zs, ∃ k : GsUniPoly F,
        toGs (evalAffineLine Q α β P) = mul (gsPow (gsLinear x) m) k := by
      intro x hx
      obtain ⟨q, hq⟩ := inPow_affine_of_cons Q x (f x) (g x) α β P m (hcons x hx) (hagree x hx)
      exact ⟨toGs q, by rw [hq, toGs_mul, toGs_npow, toGs_linear]⟩
    have hlen := gs_multiplicity_length m zs _ hnd hne hdiv
    have hd := deg_evalAffineLine_le Q α β P d hP
    have hl : (evalAffineLine Q α β P).natDeg = (evalAffineLine Q α β P).coeffs.length - 1 := rfl
    have hv : (toGs (evalAffineLine Q α β P)).val = (evalAffineLine Q α β P).coeffs := rfl
    rw [hv] at hlen
    omega

/-! ## Index sets and the interpolation count -/

/-- Triples `(i, t, j)` with `j < n`, `t + j ≤ Dy` and `i + d·j < Wx`. -/
def triples (d Wx Dy : Nat) : Nat → List (Nat × Nat × Nat)
  | 0 => []
  | n + 1 => triples d Wx Dy n ++
      (rows (fun _ => Wx - d * n) (Dy + 1 - n)).map (fun p => (p.1, p.2, n))

/-- `Σ_{j<n} (Dy + 1 - j)·(Wx - d·j)`, as an iterated sum. -/
def triCount (d Wx Dy n : Nat) : Nat :=
  sumTo (fun j => sumTo (fun _ => Wx - d * j) (Dy + 1 - j)) n

theorem sumTo_const (c : Nat) : ∀ n, sumTo (fun _ => c) n = n * c
  | 0 => (Nat.zero_mul c).symm
  | n + 1 => by
    show sumTo (fun _ => c) n + c = (n + 1) * c
    rw [sumTo_const c n, Nat.succ_mul]

theorem sumTo_congr (f g : Nat → Nat) : ∀ n, (∀ j, j < n → f j = g j) → sumTo f n = sumTo g n
  | 0, _ => rfl
  | n + 1, h => by
    show sumTo f n + f n = sumTo g n + g n
    rw [sumTo_congr f g n (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

/-- The count in closed form: `Σ_{j<n} (Dy + 1 - j)·(Wx - d·j)`. -/
theorem triCount_eq (d Wx Dy n : Nat) :
    triCount d Wx Dy n = sumTo (fun j => (Dy + 1 - j) * (Wx - d * j)) n :=
  sumTo_congr _ _ n (fun _ _ => sumTo_const _ _)

theorem triCount_zero_width (d Dy : Nat) : ∀ n, triCount d 0 Dy n = 0
  | 0 => rfl
  | n + 1 => by
    show triCount d 0 Dy n + sumTo (fun _ => 0 - d * n) (Dy + 1 - n) = 0
    rw [triCount_zero_width d Dy n, sumTo_const, Nat.zero_sub, Nat.mul_zero]

theorem length_triples (d Wx Dy : Nat) : ∀ n, (triples d Wx Dy n).length = triCount d Wx Dy n
  | 0 => rfl
  | n + 1 => by
    show (triples d Wx Dy n ++ _).length =
      triCount d Wx Dy n + sumTo (fun _ => Wx - d * n) (Dy + 1 - n)
    rw [List.length_append, List.length_map, length_rows, length_triples d Wx Dy n]

theorem mem_triples (d Wx Dy i t j : Nat) : ∀ n,
    (i, t, j) ∈ triples d Wx Dy n ↔ j < n ∧ t < Dy + 1 - j ∧ i < Wx - d * j
  | 0 => by
    constructor
    · intro h; cases h
    · intro h; exact absurd h.1 (Nat.not_lt_zero j)
  | n + 1 => by
    show (i, t, j) ∈ triples d Wx Dy n ++ _ ↔ _
    rw [List.mem_append, mem_triples d Wx Dy i t j n, List.mem_map]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨p, hp, he⟩)
      · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
      · obtain ⟨i', t'⟩ := p
        cases he
        exact ⟨Nat.lt_succ_self _, (mem_rows _ _ _ _).mp hp⟩
    · rintro ⟨h1, h2⟩
      if h : j < n then exact .inl ⟨h, h2⟩
      else
        have hj : j = n := by omega
        subst hj
        exact .inr ⟨(i, t), (mem_rows _ _ _ _).mpr h2, rfl⟩

theorem nodup_triples (d Wx Dy : Nat) : ∀ n, (triples d Wx Dy n).Nodup
  | 0 => .nil
  | n + 1 => by
    show (triples d Wx Dy n ++ _).Nodup
    rw [List.nodup_append]
    refine ⟨nodup_triples d Wx Dy n, ?_, ?_⟩
    · exact List.pairwise_map.mpr (List.Pairwise.imp (fun h e => h (by
        obtain ⟨e1, e2⟩ := Prod.mk.inj e
        exact Prod.ext e1 (Prod.mk.inj e2).1)) (nodup_rows _ _))
    · intro p hp q hq e
      subst e
      obtain ⟨i, t, j⟩ := p
      have h1 := ((mem_triples d Wx Dy i t j n).mp hp).1
      obtain ⟨p', _, he⟩ := List.mem_map.mp hq
      cases he
      omega

/-! ## The explainer -/

/-- The monomial basis `X^i Y^t Z^j`, `t + j ≤ Dy`, `i + d·j < Wx`. -/
def gens (d Wx Dy : Nat) : List (Poly3 F) :=
  (triples d Wx Dy (Dy + 1)).map fun p => mono3 p.1 p.2.1 p.2.2

/-- The constraint matrix of equation (4.3): one row per point `z` and per `(r, t, s)` with
    `s < m`, `r < m - s`, `t ≤ Dy - s`. -/
def consRows (f g : F → F) (Dm : List F) (m Dy : Nat) (gs : List (Poly3 F)) : List (List F) :=
  Dm.flatMap fun z => (triples 1 m Dy m).map fun c => gs.map (cons z (f z) (g z) c.1 c.2.1 c.2.2)

/-- **The trivariate explainer** of `[CWYZ26]` Lemma 4.2, computed by the homogeneous solver. -/
def explainer (f g : F → F) (Dm : List F) (m d Wx Dy : Nat) : Poly3 F :=
  comb (solveHomogeneous (gens (F := F) d Wx Dy).length
    (consRows f g Dm m Dy (gens d Wx Dy))) (gens d Wx Dy)

theorem explainer_spec (f g : F → F) (Dm : List F) (m d Wx Dy : Nat)
    (hcount : Dm.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1)) :
    explainer f g Dm m d Wx Dy ≠ zero ∧ (explainer f g Dm m d Wx Dy).degYZ ≤ Dy ∧
      (explainer f g Dm m d Wx Dy).deg11d d ≤ Wx + Dy - 1 ∧
      ∀ z ∈ Dm, ∀ r t s, r + s < m → cons z (f z) (g z) r t s (explainer f g Dm m d Wx Dy) = zero := by
  have hglen : (gens (F := F) d Wx Dy).length = triCount d Wx Dy (Dy + 1) := by
    show (List.map _ _).length = _
    rw [List.length_map, length_triples]
  have hrlen : (consRows f g Dm m Dy (gens d Wx Dy)).length = Dm.length * triCount 1 m Dy m :=
    flatMap_const_length _ _ Dm (fun z _ => by rw [List.length_map, length_triples])
  obtain ⟨h1, h2, h3⟩ := gauss_nullspace_witness (gens (F := F) d Wx Dy).length
    (consRows f g Dm m Dy (gens d Wx Dy)) (by rw [hrlen, hglen]; exact hcount)
    (fun row hrow => by
      obtain ⟨z, _, hz⟩ := List.mem_flatMap.mp hrow
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hz
      exact List.length_map _)
  have hdegYZ : (explainer f g Dm m d Wx Dy).degYZ ≤ Dy :=
    degFn_comb_le degFn_degYZ degYZ_C3 Dy _ _ (fun q hq => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      obtain ⟨i, t, j⟩ := p
      have hm := (mem_triples d Wx Dy i t j (Dy + 1)).mp hp
      have := degYZ_mono3_le (F := F) i t j
      show degYZ (mono3 (F := F) i t j) ≤ Dy
      omega)
  refine ⟨fun e => ?_, hdegYZ, ?_, ?_⟩
  · obtain ⟨c, hc, hne⟩ := List.any_eq_true.mp h2
    have hall := eq_zero_of_comb_mono3 (F := F) (triples d Wx Dy (Dy + 1)) _
      (nodup_triples d Wx Dy (Dy + 1)) (by rw [h1]; exact List.length_map _)
      (fun q => by
        rw [← lin_comb (isLin_coeff3 q.1 q.2.1 q.2.2)]
        show coeff3 (explainer f g Dm m d Wx Dy) q.1 q.2.1 q.2.2 = zero
        rw [e]; exact (isLin_coeff3 q.1 q.2.1 q.2.2).map_zero) c hc
    simp [hall] at hne
  · exact degFn_comb_le (degFn_deg11d d) (deg11d_C3 d) _ _ _ (fun q hq => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      obtain ⟨i, t, j⟩ := p
      have hm := (mem_triples d Wx Dy i t j (Dy + 1)).mp hp
      have := deg11d_mono3_le (F := F) d i t j
      show deg11d d (mono3 (F := F) i t j) ≤ Wx + Dy - 1
      omega)
  · intro z hz r t s hrs
    if ht : t < Dy + 1 - s then
      have hmem : (r, t, s) ∈ triples 1 m Dy m :=
        (mem_triples 1 m Dy r t s m).mpr ⟨by omega, ht, by omega⟩
      have := h3 _ (List.mem_flatMap.mpr ⟨z, hz, List.mem_map.mpr ⟨(r, t, s), hmem, rfl⟩⟩)
      rw [← lin_comb (isLin_cons z (f z) (g z) r t s)] at this
      exact this
    else
      have hsh : ((shiftHom z (f z) (g z)).toFun (explainer f g Dm m d Wx Dy)).wdeg natDeg 1
          ≤ (explainer f g Dm m d Wx Dy).wdeg natDeg 1 :=
        degYZ_shiftHom_le z (f z) (g z) (explainer f g Dm m d Wx Dy)
      have hdy : (explainer f g Dm m d Wx Dy).wdeg natDeg 1 ≤ Dy := hdegYZ
      show coeffAt (coeffAt (coeffAt
        ((shiftHom z (f z) (g z)).toFun (explainer f g Dm m d Wx Dy)).coeffs s).coeffs
          t).coeffs r = zero
      generalize (shiftHom z (f z) (g z)).toFun (explainer f g Dm m d Wx Dy) = T at hsh ⊢
      have hzero : coeffAt (coeffAt T.coeffs s).coeffs t = zero := by
        if hq : coeffAt T.coeffs s = zero then
          rw [hq, coeffs_zero, coeffAt_nil]
        else
          have hle := le_wdeg natDeg 1 T s hq
          exact coeffAt_eq_zero_of_natDeg_lt (coeffAt T.coeffs s) (by omega)
      rw [hzero, coeffs_zero, coeffAt_nil]

/-- The explainer vanishes on every sufficiently agreeing candidate: for `P` of degree at most
    `d` agreeing with `f + (α + βX)·g` on distinct points `zs` of `Dm` with
    `Wx + Dy ≤ m·|zs|`, `Q(X, α + βX, P(X)) = 0`. -/
theorem explainer_vanishes (f g : F → F) (Dm : List F) (m d Wx Dy : Nat)
    (hcount : Dm.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1)) (α β : F)
    (P : UPoly F) (zs : List F) (hP : P.natDeg ≤ d) (hnd : zs.Nodup) (hsub : ∀ z ∈ zs, z ∈ Dm)
    (hag : ∀ z ∈ zs, P.eval z = add (f z) (mul (add α (mul β z)) (g z)))
    (hlen : Wx + Dy ≤ m * zs.length) :
    evalAffineLine (explainer f g Dm m d Wx Dy) α β P = zero := by
  obtain ⟨_, _, h11, hc⟩ := explainer_spec f g Dm m d Wx Dy hcount
  have hW : 1 ≤ Wx := Nat.pos_of_ne_zero (fun e => by
    rw [e, triCount_zero_width] at hcount
    exact Nat.not_lt_zero _ hcount)
  exact evalAffineLine_eq_zero_of_agree _ m d f g α β P zs hnd
    (fun z hz => hc z (hsub z hz)) hag hP (by omega)

/-- **`[CWYZ26]` Lemma 4.2.** Under the count hypothesis (4.5) there is a nonzero
    `Q ∈ F[X][Y][Z]` with `deg_{Y,Z} Q ≤ Dy` and `deg_{1,1,d} Q < Wx + Dy` such that, for all
    `α, β` and every `P` of degree at most `d` agreeing with `f + (α + βX)·g` on a set `zs` of
    points of `Dm` with `Wx + Dy ≤ m·|zs|`, the specialization `Q(X, α + βX, P(X))` is zero. -/
theorem exists_trivariate_affine_explainer (f g : F → F) (Dm : List F) (m d Wx Dy : Nat)
    (hcount : Dm.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1)) :
    ∃ Q : Poly3 F, Q ≠ zero ∧ Q.degYZ ≤ Dy ∧ Q.deg11d d ≤ Wx + Dy - 1 ∧
      ∀ (α β : F) (P : UPoly F) (zs : List F), P.natDeg ≤ d → zs.Nodup → (∀ z ∈ zs, z ∈ Dm) →
        (∀ z ∈ zs, P.eval z = add (f z) (mul (add α (mul β z)) (g z))) →
        Wx + Dy ≤ m * zs.length → evalAffineLine Q α β P = zero := by
  obtain ⟨hne, hYZ, h11, _⟩ := explainer_spec f g Dm m d Wx Dy hcount
  exact ⟨_, hne, hYZ, h11, fun α β P zs hP hnd hsub hag hlen =>
    explainer_vanishes f g Dm m d Wx Dy hcount α β P zs hP hnd hsub hag hlen⟩

end Poly3

/-! ## Witnesses -/

namespace Poly3.ExplainerTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- The count hypothesis is satisfiable: two points, multiplicity one, `Dy = 1`, `Wx = 2`
    give `5` unknowns against `4` equations. -/
theorem inhabited_explainer :
    ∃ (f g' : Goldilocks → Goldilocks) (Dm : List Goldilocks) (m d Wx Dy : Nat),
      Dm.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1) ∧
      explainer f g' Dm m d Wx Dy ≠ zero :=
  ⟨fun _ => g 0, fun _ => g 1, [g 0, g 1], 1, 1, 2, 1, by decide,
    (explainer_spec _ _ _ 1 1 2 1 (by decide)).1⟩

/-- `Q = Z - Y` meets the order-one constraint at `z = 0` for `f(0) = 0`, `g(0) = 1`. -/
def qTooth : Poly3 Goldilocks := ofList [ofList [zero, neg one], one]

/-- The degree hypothesis of `evalAffineLine_eq_zero_of_agree` is needed: `Q = Z - Y`
    satisfies the constraint at the single point `0` and `P = X` agrees with the fold there
    (`α = β = 0`), yet `Q(X, 0, X) = X ≠ 0`; here `deg_{1,1,1} Q = 1 = m·|zs|`. -/
theorem tooth_agree_needs_degree :
    ∃ (Q : Poly3 Goldilocks) (f g' : Goldilocks → Goldilocks) (α β : Goldilocks)
      (P : UPoly Goldilocks) (zs : List Goldilocks), zs.Nodup ∧
      (∀ z ∈ zs, ∀ r t s, r + s < 1 → cons z (f z) (g' z) r t s Q = zero) ∧
      (∀ z ∈ zs, P.eval z = add (f z) (mul (add α (mul β z)) (g' z))) ∧ P.natDeg ≤ 1 ∧
      evalAffineLine Q α β P ≠ zero := by
  refine ⟨qTooth, fun _ => g 0, fun _ => g 1, g 0, g 0, X, [g 0], by decide, ?_, ?_,
    by decide, by decide +kernel⟩
  · intro z hz r t s hrs
    rw [List.mem_singleton.mp hz]
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := ⟨by omega, by omega⟩
    have e : (shiftHom (g 0) (g 0) (g 1)).toFun qTooth = X := by decide +kernel
    show coeffAt (coeffAt (coeffAt ((shiftHom (g 0) (g 0) (g 1)).toFun qTooth).coeffs 0).coeffs
      t).coeffs 0 = zero
    rw [e]
    show coeffAt (coeffAt (zero : UPoly (UPoly Goldilocks)).coeffs t).coeffs 0 = zero
    rw [coeffs_zero, coeffAt_nil, coeffs_zero, coeffAt_nil]
  · intro z hz
    rw [List.mem_singleton.mp hz]
    decide +kernel

#verify_constructive exists_trivariate_affine_explainer explainer_spec explainer_vanishes
#verify_constructive evalAffineLine_eq_zero_of_agree inPow_affine_of_cons unshift_shift
#verify_constructive tooth_agree_needs_degree inhabited_explainer
#tooth_pair evalAffineLine_eq_zero_of_agree vs tooth_agree_needs_degree
#verify_inhabited exists_trivariate_affine_explainer inhabited_explainer

end Poly3.ExplainerTests

end Qsag
end
