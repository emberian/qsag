module
/-
# Qsag.Coding.DynamicGcdSplit — fraction fields, squarefree factors, and `[CWYZ26]` Lemma 4.3

* `Frac D`: the fraction field of a decidable integral domain, as a quotient of pairs by
  cross-multiplication, with `DecidableEq` and `LawfulField`. `RatFunc F := Frac F[X]`.
* `UPoly.mapHom` (base change into `F(X)[Y][Z]`) and `UPoly.d5_split` (the splitting step).
* `SqFactor R`: a factor of positive `Z`-degree that is coprime to its `Z`-derivative over
  `F(X)(Y)`; its separant eliminant `sepElim R ∈ F(X)[Y]` is nonzero of degree at most
  `(deg_{Y,Z} R)²`.
* `excluded_pairs_card_le`: at most `D²` pairs `(α, β)` are excluded (`[CWYZ26]` Lemma 4.3),
  and `simple_root_of_not_excluded`: outside them every root `P` of the factored `Q` on the
  line `Y = α + βX` is a simple root of some factor.
-/

public import Qsag.Coding.SylvesterResultant
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.SylvesterResultant
import all Qsag.Coding.AffineProximityGaps

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

/-! ## The fraction field of an integral domain -/

/-- A ring in which `1 ≠ 0`. -/
class NontrivialRing (D : Type) [CommRingOps D] : Prop where
  one_ne_zero : (one : D) ≠ zero

instance (F : Type) [LawfulField F] : NontrivialRing F := ⟨LawfulField.one_ne_zero⟩

/-- A numerator and a nonzero denominator. -/
structure PreFrac (D : Type) [CommRingOps D] where
  num : D
  den : D
  den_ne : den ≠ zero

section Domain
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D]

theorem mul_ne_zero' {a b : D} (ha : a ≠ zero) (hb : b ≠ zero) : mul a b ≠ zero := fun h =>
  (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).elim ha hb

theorem mul_right_cancel' {x y d : D} (hd : d ≠ zero) (h : mul x d = mul y d) : x = y := by
  have h0 : mul (sub x y) d = zero := by
    rw [LawfulCommRing.sub_mul, h, LawfulCommRing.sub_self]
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0 with h1 | h1
  · exact LawfulCommRing.sub_eq_zero_iff.mp h1
  · exact absurd h1 hd

end Domain

namespace PreFrac
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D]

/-- Equality of fractions by cross-multiplication. -/
@[expose] def Rel (a b : PreFrac D) : Prop := mul a.num b.den = mul b.num a.den

theorem Rel.trans' {a b c : PreFrac D} (hab : Rel a b) (hbc : Rel b c) : Rel a c := by
  unfold Rel at *
  apply mul_right_cancel' b.den_ne
  have e1 : mul (mul a.num c.den) b.den = mul (mul a.num b.den) c.den := by constructive_ring
  have e2 : mul (mul b.num a.den) c.den = mul (mul b.num c.den) a.den := by constructive_ring
  have e3 : mul (mul c.num b.den) a.den = mul (mul c.num a.den) b.den := by constructive_ring
  rw [e1, hab, e2, hbc, e3]

instance setoid : Setoid (PreFrac D) where
  r := Rel
  iseqv := ⟨fun _ => rfl, fun h => h.symm, Rel.trans'⟩

def padd (a b : PreFrac D) : PreFrac D :=
  ⟨add (mul a.num b.den) (mul b.num a.den), mul a.den b.den, mul_ne_zero' a.den_ne b.den_ne⟩

def pmul (a b : PreFrac D) : PreFrac D :=
  ⟨mul a.num b.num, mul a.den b.den, mul_ne_zero' a.den_ne b.den_ne⟩

def pneg (a : PreFrac D) : PreFrac D := ⟨neg a.num, a.den, a.den_ne⟩

def pinv [DecidableEq D] [NontrivialRing D] (a : PreFrac D) : PreFrac D :=
  if h : a.num = zero then ⟨zero, one, NontrivialRing.one_ne_zero⟩ else ⟨a.den, a.num, h⟩

theorem padd_rel {a a' b b' : PreFrac D} (ha : Rel a a') (hb : Rel b b') :
    Rel (padd a b) (padd a' b') := by
  unfold Rel at *
  show mul (add (mul a.num b.den) (mul b.num a.den)) (mul a'.den b'.den) =
    mul (add (mul a'.num b'.den) (mul b'.num a'.den)) (mul a.den b.den)
  have e1 : mul (add (mul a.num b.den) (mul b.num a.den)) (mul a'.den b'.den) =
      add (mul (mul a.num a'.den) (mul b.den b'.den))
        (mul (mul b.num b'.den) (mul a.den a'.den)) := by constructive_ring
  rw [e1, ha, hb]; constructive_ring

theorem pmul_rel {a a' b b' : PreFrac D} (ha : Rel a a') (hb : Rel b b') :
    Rel (pmul a b) (pmul a' b') := by
  unfold Rel at *
  show mul (mul a.num b.num) (mul a'.den b'.den) = mul (mul a'.num b'.num) (mul a.den b.den)
  have e1 : mul (mul a.num b.num) (mul a'.den b'.den) =
      mul (mul a.num a'.den) (mul b.num b'.den) := by constructive_ring
  rw [e1, ha, hb]; constructive_ring

omit [NoZeroDivisors D] in
theorem pneg_rel {a a' : PreFrac D} (ha : Rel a a') : Rel (pneg a) (pneg a') := by
  unfold Rel at *
  show mul (neg a.num) a'.den = mul (neg a'.num) a.den
  rw [LawfulCommRing.neg_mul, ha, LawfulCommRing.neg_mul]

theorem pinv_rel [DecidableEq D] [NontrivialRing D] {a a' : PreFrac D} (ha : Rel a a') :
    Rel (pinv a) (pinv a') := by
  unfold Rel at ha
  have hiff : a.num = zero ↔ a'.num = zero := by
    constructor
    · intro h
      rw [h, LawfulCommRing.zero_mul] at ha
      exact (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero ha.symm).elim id
        (fun e => absurd e a.den_ne)
    · intro h
      rw [h, LawfulCommRing.zero_mul] at ha
      exact (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero ha).elim id
        (fun e => absurd e a'.den_ne)
  unfold pinv
  split
  · next h =>
    split
    · rfl
    · next h' => exact absurd (hiff.mp h) h'
  · next h =>
    split
    · next h' => exact absurd (hiff.mpr h') h
    · show mul a.den a'.num = mul a'.den a.num
      rw [LawfulCommRing.mul_comm, ← ha, LawfulCommRing.mul_comm]

end PreFrac

/-- The fraction field of the integral domain `D`. -/
@[expose] def Frac (D : Type) [LawfulCommRing D] [NoZeroDivisors D] : Type :=
  Quotient (PreFrac.setoid (D := D))

namespace Frac
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D] [DecidableEq D] [NontrivialRing D]
open PreFrac

/-- The class of `n/d`. -/
def mk (a : PreFrac D) : Frac D := Quotient.mk _ a

omit [DecidableEq D] [NontrivialRing D] in
theorem sound {a b : PreFrac D} (h : Rel a b) : mk a = mk b := Quotient.sound h

omit [DecidableEq D] [NontrivialRing D] in
theorem exact {a b : PreFrac D} (h : mk a = mk b) : Rel a b := Quotient.exact h

instance : DecidableEq (Frac D) := fun x y =>
  Quotient.recOnSubsingleton₂ x y fun a b =>
    if h : mul a.num b.den = mul b.num a.den then .isTrue (Quotient.sound h)
    else .isFalse (fun e => h (Quotient.exact e))

def fadd (x y : Frac D) : Frac D :=
  Quotient.liftOn₂ x y (fun a b => mk (padd a b)) (fun _ _ _ _ ha hb => sound (padd_rel ha hb))

def fmul (x y : Frac D) : Frac D :=
  Quotient.liftOn₂ x y (fun a b => mk (pmul a b)) (fun _ _ _ _ ha hb => sound (pmul_rel ha hb))

def fneg (x : Frac D) : Frac D :=
  Quotient.liftOn x (fun a => mk (pneg a)) (fun _ _ ha => sound (pneg_rel ha))

def finv (x : Frac D) : Frac D :=
  Quotient.liftOn x (fun a => mk (pinv a)) (fun _ _ ha => sound (pinv_rel ha))

/-- The class of `c/1`. -/
def ofD (c : D) : Frac D := mk ⟨c, one, NontrivialRing.one_ne_zero⟩

omit [DecidableEq D] [NontrivialRing D] in
theorem ind₁ {p : Frac D → Prop} (h : ∀ a, p (mk a)) : ∀ x, p x := Quotient.ind h

omit [DecidableEq D] [NontrivialRing D] in
theorem ind₂ {p : Frac D → Frac D → Prop} (h : ∀ a b, p (mk a) (mk b)) : ∀ x y, p x y :=
  fun x y => Quotient.inductionOn₂ x y h

omit [DecidableEq D] [NontrivialRing D] in
theorem ind₃ {p : Frac D → Frac D → Frac D → Prop}
    (h : ∀ a b c, p (mk a) (mk b) (mk c)) : ∀ x y z, p x y z :=
  fun x y z => Quotient.inductionOn₃ x y z h

instance instLawfulField : LawfulField (Frac D) where
  zero := ofD zero
  one := ofD one
  add := fadd
  mul := fmul
  neg := fneg
  sub x y := fadd x (fneg y)
  inv := finv
  add_assoc := ind₃ fun a b c => by
    exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  add_comm := ind₂ fun a b => by exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  zero_add := ind₁ fun a => by exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  add_zero := ind₁ fun a => by exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  add_left_neg := ind₁ fun a => by
    exact sound (by unfold Rel padd pneg; dsimp only; constructive_ring)
  sub_eq_add_neg _ _ := by rfl
  mul_assoc := ind₃ fun a b c => by
    exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  mul_comm := ind₂ fun a b => by exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  one_mul := ind₁ fun a => by exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  mul_one := ind₁ fun a => by exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  left_distrib := ind₃ fun a b c => by
    exact sound (by unfold Rel pmul padd; dsimp only; constructive_ring)
  right_distrib := ind₃ fun a b c => by
    exact sound (by unfold Rel pmul padd; dsimp only; constructive_ring)
  zero_ne_one := by
    intro h
    have h' : mul (zero : D) one = mul one one := exact h
    rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_one] at h'
    exact NontrivialRing.one_ne_zero h'.symm
  mul_inv_cancel := by
    intro x
    induction x using ind₁ with | h a =>
    intro hx
    have hn : a.num ≠ zero := fun e => hx (sound (by
      show mul a.num one = mul zero a.den
      rw [e, LawfulCommRing.zero_mul, LawfulCommRing.zero_mul]))
    exact sound (by
      unfold pinv; split
      · next h => exact absurd h hn
      · show mul (mul a.num a.den) one = mul one (mul a.den a.num)
        constructive_ring)

/-- The embedding `D → Frac D`. -/
def of : RingHom D (Frac D) where
  toFun := ofD
  map_zero := by rfl
  map_one := by rfl
  map_add a b := sound (by
    show mul (add a b) (mul one one) = mul (add (mul a one) (mul b one)) one
    constructive_ring)
  map_mul a b := sound (by
    show mul (mul a b) (mul one one) = mul (mul a b) one
    constructive_ring)

theorem of_injective {a b : D} (h : (of (D := D)).toFun a = (of (D := D)).toFun b) : a = b := by
  have h' : mul a one = mul b one := exact h
  rwa [LawfulCommRing.mul_one, LawfulCommRing.mul_one] at h'

end Frac

/-! ## Base change of coefficients -/

namespace UPoly

section Map
variable {R S T : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S] [DecidableEq S]
  [LawfulCommRing T]

/-- Coefficientwise base change `R[X] → S[X]`. -/
def mapHom (φ : RingHom R S) : RingHom (UPoly R) (UPoly S) := eval₂Hom (CHom.comp φ) X

theorem mapHom_apply (φ : RingHom R S) (p : UPoly R) :
    (mapHom φ).toFun p = ofList (p.coeffs.map φ.toFun) := by
  show evalCoeffs (p.coeffs.map (CHom.comp φ).toFun) X = _
  generalize p.coeffs = l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    show add (C (φ.toFun c)) (mul X (evalCoeffs (cs.map (CHom.comp φ).toFun) X)) =
      ofList (φ.toFun c :: cs.map φ.toFun)
    rw [ih, ofList_cons]

theorem coeffAt_mapHom (φ : RingHom R S) (p : UPoly R) (k : Nat) :
    coeffAt ((mapHom φ).toFun p).coeffs k = φ.toFun (coeffAt p.coeffs k) := by
  rw [mapHom_apply, coeffAt_ofList, RingHom.coeffAt_map]

theorem mapHom_C (φ : RingHom R S) (c : R) : (mapHom φ).toFun (C c) = C (φ.toFun c) :=
  eval₂_C _ _ _

theorem mapHom_inj (φ : RingHom R S) (hinj : ∀ x, φ.toFun x = zero → x = zero)
    (p : UPoly R) (h : (mapHom φ).toFun p = zero) : p = zero :=
  ext_coeffAt fun k => by
    have := congrArg (fun q : UPoly S => coeffAt q.coeffs k) h
    simp only [coeffAt_mapHom, coeffs_zero, coeffAt_nil] at this
    rw [coeffs_zero, coeffAt_nil]; exact hinj _ this

theorem natDeg_mapHom_le (φ : RingHom R S) (p : UPoly R) :
    ((mapHom φ).toFun p).natDeg ≤ p.natDeg :=
  natDeg_le_of_coeffAt _ _ (fun k hk => by
    rw [coeffAt_mapHom, p.coeffAt_eq_zero_of_natDeg_lt hk, φ.map_zero])

theorem natDeg_mapHom (φ : RingHom R S) (hinj : ∀ x, φ.toFun x = zero → x = zero)
    (p : UPoly R) : ((mapHom φ).toFun p).natDeg = p.natDeg := by
  apply Nat.le_antisymm (natDeg_mapHom_le φ p)
  apply Decidable.byContradiction
  intro hlt
  have hz := ((mapHom φ).toFun p).coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hlt)
  rw [coeffAt_mapHom] at hz
  have hp : p ≠ zero := fun e => by
    rw [e] at hlt; exact hlt (Nat.zero_le _)
  exact lead_ne_zero hp (hinj _ hz)

theorem eval₂_mapHom (ψ : RingHom S T) (s : T) (φ : RingHom R S) (p : UPoly R) :
    eval₂ ψ s ((mapHom φ).toFun p) = eval₂ (ψ.comp φ) s p := by
  rw [mapHom_apply, eval₂_ofList, List.map_map]; rfl

theorem eval_mapHom (φ : RingHom R S) (p : UPoly R) (y : R) :
    ((mapHom φ).toFun p).eval (φ.toFun y) = φ.toFun (p.eval y) := by
  show eval₂ (RingHom.id S) (φ.toFun y) ((mapHom φ).toFun p) = φ.toFun (eval₂ (RingHom.id R) y p)
  rw [eval₂_mapHom, hom_eval₂]; rfl

/-- Evaluating a doubly base-changed polynomial at the image of a point. -/
theorem eval₂_mapHom_mapHom (φ : RingHom R S) (Q : UPoly (UPoly R)) (y z : R) :
    eval₂ (evalHom (φ.toFun y)) (φ.toFun z) ((mapHom (mapHom φ)).toFun Q) =
      φ.toFun (eval₂ (evalHom y) z Q) := by
  rw [eval₂_mapHom, hom_eval₂]
  show evalCoeffs (Q.coeffs.map _) _ = evalCoeffs (Q.coeffs.map _) _
  congr 1
  apply List.map_congr_left
  intro q _
  exact eval_mapHom φ q y

/-- Base change does not raise the total degree. -/
theorem wdeg_mapHom_mapHom_le (φ : RingHom R S) (Q : UPoly (UPoly R)) :
    ((mapHom (mapHom φ)).toFun Q).wdeg natDeg 1 ≤ Q.wdeg natDeg 1 := by
  apply wdeg_le
  intro k hk
  rw [coeffAt_mapHom] at hk ⊢
  have hne : coeffAt Q.coeffs k ≠ zero := fun e => hk (by rw [e, (mapHom φ).map_zero])
  have := le_wdeg natDeg 1 Q k hne
  have := natDeg_mapHom_le φ (coeffAt Q.coeffs k)
  omega

end Map

section Hasse
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- Hasse derivatives respect coefficient filtrations: the `i`-th coefficient of the `k`-th
    derivative is an integer combination of the coefficient of index `i + k`. -/
theorem coeffAt_hasse_graded : ∀ (l : List R) (L : Nat → R → Prop), (∀ j, L j zero) →
    (∀ j x y, L j x → L j y → L j (add x y)) → (∀ j, L j (coeffAt l j)) →
    ∀ k i, L (i + k) (coeffAt (gsUniHasse (l.map C) k (X : UPoly R)).coeffs i)
  | [], L, hz, _, _, k, i => by
    show L (i + k) (coeffAt (zero : UPoly R).coeffs i); rw [coeffs_zero, coeffAt_nil]; exact hz _
  | c :: cs, L, hz, hadd, hl, k, i => by
    have ih := coeffAt_hasse_graded cs (fun j => L (j + 1)) (fun _ => hz _) (fun _ => hadd _)
      (fun j => hl (j + 1))
    cases k with
    | zero =>
      show L (i + 0) (coeffAt (add (C c) (mul X (gsUniHasse (cs.map C) 0 X))).coeffs i)
      rw [coeffAt_add]
      cases i with
      | zero => rw [coeffAt_X_mul_zero, coeffAt_C_zero, LawfulCommRing.add_zero]; exact hl 0
      | succ i => rw [coeffAt_X_mul_succ, coeffAt_C_succ, LawfulCommRing.zero_add]; exact ih 0 i
    | succ k =>
      show L (i + (k + 1)) (coeffAt (add (gsUniHasse (cs.map C) k X)
        (mul X (gsUniHasse (cs.map C) (k + 1) X))).coeffs i)
      rw [coeffAt_add]
      apply hadd
      · exact ih k i
      · cases i with
        | zero => rw [coeffAt_X_mul_zero]; exact hz _
        | succ i =>
          rw [coeffAt_X_mul_succ]
          have := ih (k + 1) i
          rwa [show i + (k + 1) + 1 = i + 1 + (k + 1) by omega] at this

/-- Differentiating `k` times lowers the weighted degree by `k` times the variable weight. -/
theorem wdeg_hasse_le (w : R → Nat) (hw : DegFn w) (s k : Nat) (p : UPoly R) :
    (hasse k p).wdeg w s ≤ p.wdeg w s - s * k := by
  apply wdeg_le
  intro i h
  have key : coeffAt (hasse k p).coeffs i ≠ zero →
      w (coeffAt (hasse k p).coeffs i) + s * (i + k) ≤ p.wdeg w s :=
    coeffAt_hasse_graded p.coeffs (fun j x => x ≠ zero → w x + s * j ≤ p.wdeg w s)
      (fun _ h => absurd rfl h) (fun _ _ _ hx hy h => bnd_add hw hx hy h) (le_wdeg w s p) k i
  have := key h
  rw [Nat.mul_add] at this; omega
end Hasse

/-- The product of a list of polynomials. -/
def prodList {R : Type} [LawfulCommRing R] [DecidableEq R] : List (UPoly R) → UPoly R
  | [] => one
  | p :: ps => mul p (prodList ps)

end UPoly

instance (F : Type) [LawfulField F] [DecidableEq F] : NoZeroDivisors (UPoly F) :=
  letI : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
  inferInstance

instance (R : Type) [LawfulCommRing R] [DecidableEq R] [NontrivialRing R] :
    NontrivialRing (UPoly R) where
  one_ne_zero := fun e => NontrivialRing.one_ne_zero (D := R) (by
    have := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) e
    simp only [UPoly.one_eq_C, UPoly.coeffAt_C_zero, UPoly.coeffs_zero, coeffAt_nil] at this
    exact this)

/-- Rational functions `F(X)`. -/
abbrev RatFunc (F : Type) [LawfulField F] [DecidableEq F] := Frac (UPoly F)

namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

theorem natDeg_one : (one : UPoly R).natDeg = 0 := by
  have := trimPoly_length_le [(one : R)]
  show (ofList [one]).coeffs.length - 1 = 0
  rw [coeffs_ofList]
  simp only [List.length_cons, List.length_nil] at this; omega

theorem prodList_ne_zero [NoZeroDivisors R] [NontrivialRing R] :
    ∀ ps : List (UPoly R), (∀ p ∈ ps, p ≠ zero) → prodList ps ≠ zero
  | [], _ => NontrivialRing.one_ne_zero
  | p :: ps, h => mul_ne_zero' (h p (.head _))
      (prodList_ne_zero ps (fun q hq => h q (.tail _ hq)))

theorem eval_prodList_eq_zero (y : R) : ∀ ps : List (UPoly R),
    (∃ p ∈ ps, p.eval y = zero) → (prodList ps).eval y = zero
  | [], h => by obtain ⟨_, hp, _⟩ := h; cases hp
  | p :: ps, h => by
    show (evalHom y).toFun (mul p (prodList ps)) = zero
    rw [(evalHom y).map_mul]
    obtain ⟨q, hq, hz⟩ := h
    cases hq with
    | head => rw [evalHom_apply, hz, LawfulCommRing.zero_mul]
    | tail _ hq' =>
      rw [evalHom_apply, evalHom_apply, eval_prodList_eq_zero y ps ⟨q, hq', hz⟩,
        LawfulCommRing.mul_zero]

end UPoly

/-! ## Squarefree factors and `[CWYZ26]` Lemma 4.3 -/

namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]

local instance : NoZeroDivisors (RatFunc F) := LawfulField.toNoZeroDivisors (RatFunc F)

/-- `∂_Z` lowers the `(Y, Z)`-degree. -/
theorem degYZ_hasseZ_le (s : Nat) (Q : Poly3 F) : (hasseZ s Q).degYZ ≤ Q.degYZ - s := by
  have := UPoly.wdeg_hasse_le UPoly.natDeg UPoly.degFn_natDeg 1 s Q
  rwa [Nat.one_mul] at this

/-- Base change `F[X][Y][Z] → F(X)[Y][Z]`. -/
def liftK : RingHom (Poly3 F) (Poly2 (RatFunc F)) := UPoly.mapHom (UPoly.mapHom Frac.of)

private theorem of_inj (x : UPoly F) (h : (Frac.of (D := UPoly F)).toFun x = zero) : x = zero :=
  Frac.of_injective (h.trans (Frac.of (D := UPoly F)).map_zero.symm)

private theorem map_of_inj (q : UPoly (UPoly F))
    (h : (UPoly.mapHom (Frac.of (D := UPoly F))).toFun q = zero) : q = zero :=
  UPoly.mapHom_inj _ of_inj q h

/-- The separant eliminant `Δ_R ∈ F(X)[Y]`, a member of the ideal `(R, ∂_Z R)`. -/
def sepElim (R : Poly3 F) : UPoly (RatFunc F) :=
  Poly2.resZ (liftK.toFun R) (liftK.toFun (hasseZ 1 R))

/-- A squarefree factor: positive `Z`-degree, and coprime to its `Z`-derivative over
    `F(X)(Y)`. -/
structure SqFactor (R : Poly3 F) : Prop where
  degZ_pos : 1 ≤ R.degZ
  coprime : Poly2.CoprimeZ (liftK.toFun R) (liftK.toFun (hasseZ 1 R))

/-- An integral Bézout certificate `u·R + v·∂_Z R = c ∈ F[X][Y]`, `c ≠ 0`, proves
    squarefreeness. Such certificates are what a computer-algebra system returns. -/
theorem SqFactor.of_cert {R : Poly3 F} (hdeg : 1 ≤ R.degZ) (u v : Poly3 F)
    (c : UPoly (UPoly F)) (hc : c ≠ zero)
    (h : add (mul u R) (mul v (hasseZ 1 R)) = UPoly.C c) : SqFactor R :=
  ⟨hdeg, liftK.toFun u, liftK.toFun v, (UPoly.mapHom Frac.of).toFun c,
    fun e => hc (map_of_inj c e), by
      rw [← liftK.map_mul, ← liftK.map_mul, ← liftK.map_add, h]
      exact UPoly.mapHom_C _ c⟩

theorem SqFactor.natDeg_liftK {R : Poly3 F} (h : SqFactor R) : 1 ≤ (liftK.toFun R).natDeg := by
  have : (liftK.toFun R).natDeg = R.natDeg := UPoly.natDeg_mapHom _ map_of_inj R
  rw [this]; exact h.degZ_pos

theorem SqFactor.liftK_hasse_ne_zero {R : Poly3 F} (h : SqFactor R) :
    liftK.toFun (hasseZ 1 R) ≠ zero := by
  intro e
  obtain ⟨u, v, c, hc, hcert⟩ := h.coprime
  rw [e, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hcert
  have hu : u ≠ zero := fun e' => Poly2.C_ne_zero hc (by
    rw [← hcert, e', LawfulCommRing.zero_mul])
  have hA : liftK.toFun R ≠ zero := fun e' => Poly2.C_ne_zero hc (by
    rw [← hcert, e', LawfulCommRing.mul_zero])
  have h1 := UPoly.natDeg_mul hu hA
  rw [hcert, Poly2.natDeg_C] at h1
  have := h.natDeg_liftK
  omega

theorem sepElim_ne_zero {R : Poly3 F} (h : SqFactor R) : sepElim R ≠ zero :=
  (Poly2.resZ_ne_zero_iff _ _ h.natDeg_liftK h.liftK_hasse_ne_zero).mpr h.coprime

theorem natDeg_sepElim_le {R : Poly3 F} (h : SqFactor R) :
    (sepElim R).natDeg ≤ R.degYZ * R.degYZ := by
  have h1 := Poly2.natDeg_resZ_le (liftK.toFun R) (liftK.toFun (hasseZ 1 R)) h.natDeg_liftK
  have h2 : Poly2.tdeg (liftK.toFun R) ≤ R.degYZ := UPoly.wdeg_mapHom_mapHom_le _ R
  have h3 : Poly2.tdeg (liftK.toFun (hasseZ 1 R)) ≤ (hasseZ 1 R).degYZ :=
    UPoly.wdeg_mapHom_mapHom_le _ _
  have h4 := degYZ_hasseZ_le 1 R
  exact Nat.le_trans h1 (Nat.mul_le_mul h2 (by omega))

/-- `(α, β)` is excluded when the `Z`-free content `Cc` vanishes on the line `Y = α + βX`,
    or the separant eliminant of some factor does. Outside this set every factor
    specializes to a polynomial without repeated roots along the line. -/
def Excluded (Cc : UPoly (UPoly F)) (Rs : List (Poly3 F)) (α β : F) : Prop :=
  Cc.eval (line α β) = zero ∨
    ∃ R ∈ Rs, (sepElim R).eval ((Frac.of (D := UPoly F)).toFun (line α β)) = zero

private theorem natDeg_prod_sepElim_le : ∀ Rs : List (Poly3 F), (∀ R ∈ Rs, SqFactor R) →
    (UPoly.prodList (Rs.map sepElim)).natDeg ≤ (Rs.map degYZ).sum * (Rs.map degYZ).sum
  | [], _ => by show (one : UPoly (RatFunc F)).natDeg ≤ _; rw [UPoly.natDeg_one]; exact Nat.zero_le _
  | R :: Rs, h => by
    have ih := natDeg_prod_sepElim_le Rs (fun R' hR' => h R' (.tail _ hR'))
    have h1 := natDeg_sepElim_le (h R (.head _))
    have h2 := UPoly.natDeg_mul_le (sepElim R) (UPoly.prodList (Rs.map sepElim))
    show (mul (sepElim R) (UPoly.prodList (Rs.map sepElim))).natDeg ≤
      (R.degYZ + (Rs.map degYZ).sum) * (R.degYZ + (Rs.map degYZ).sum)
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega

private theorem line_inj {α β α' β' : F} (h : line α β = line α' β') : α = α' ∧ β = β' := by
  have h0 := congrArg (fun p : UPoly F => coeffAt p.coeffs 0) h
  have h1 := congrArg (fun p : UPoly F => coeffAt p.coeffs 1) h
  simp only [line, UPoly.coeffAt_ofList] at h0 h1
  exact ⟨h0, h1⟩

/-- **`[CWYZ26]` Lemma 4.3, counting part.** If `deg_Y Cc + Σ deg_{Y,Z} Rᵢ ≤ D` for squarefree
    factors `Rᵢ`, at most `D²` coefficient pairs `(α, β)` are excluded. -/
theorem excluded_pairs_card_le (Cc : UPoly (UPoly F)) (Rs : List (Poly3 F)) (hC : Cc ≠ zero)
    (hRs : ∀ R ∈ Rs, SqFactor R) (D : Nat) (hD : Cc.natDeg + (Rs.map degYZ).sum ≤ D)
    (E : List (F × F)) (hnd : E.Nodup) (hE : ∀ p ∈ E, Excluded Cc Rs p.1 p.2) :
    E.length ≤ D ^ 2 := by
  let lineK : F × F → RatFunc F := fun p => (Frac.of (D := UPoly F)).toFun (line p.1 p.2)
  let Pr : UPoly (RatFunc F) :=
    mul ((UPoly.mapHom Frac.of).toFun Cc) (UPoly.prodList (Rs.map sepElim))
  have hPrne : Pr ≠ zero := mul_ne_zero' (fun e => hC (map_of_inj Cc e))
    (UPoly.prodList_ne_zero _ (fun q hq => by
      obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hq
      exact sepElim_ne_zero (hRs R hR)))
  have hPrdeg : Pr.natDeg ≤ Cc.natDeg + (Rs.map degYZ).sum * (Rs.map degYZ).sum := by
    have h1 := UPoly.natDeg_mul_le ((UPoly.mapHom Frac.of).toFun Cc)
      (UPoly.prodList (Rs.map sepElim))
    have h2 := UPoly.natDeg_mapHom_le (Frac.of (D := UPoly F)) Cc
    have h3 := natDeg_prod_sepElim_le Rs hRs
    show UPoly.natDeg (mul ((UPoly.mapHom Frac.of).toFun Cc)
      (UPoly.prodList (Rs.map sepElim))) ≤ _
    omega
  have hroot : ∀ y ∈ E.map lineK, evalCoeffs Pr.coeffs y = zero := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    rw [← UPoly.eval_eq]
    show (UPoly.evalHom (lineK p)).toFun (mul _ _) = zero
    rw [RingHom.map_mul, UPoly.evalHom_apply, UPoly.evalHom_apply]
    rcases hE p hp with h | ⟨R, hR, h⟩
    · rw [UPoly.eval_mapHom, h, RingHom.map_zero, LawfulCommRing.zero_mul]
    · rw [UPoly.eval_prodList_eq_zero _ _ ⟨sepElim R, List.mem_map.mpr ⟨R, hR, rfl⟩, h⟩,
        LawfulCommRing.mul_zero]
  have hndK : (E.map lineK).Nodup :=
    List.pairwise_map.mpr (List.Pairwise.imp (fun {p q} hne e => hne (by
      have := line_inj (Frac.of_injective e)
      exact Prod.ext this.1 this.2)) hnd)
  have hcount := gs_formal_root_bound Pr.natDeg Pr.coeffs (E.map lineK)
    (by show _ ≤ Pr.coeffs.length - 1 + 1; omega)
    (Poly2.exists_ne_zero_of_ne_zero hPrne) hndK hroot
  rw [List.length_map] at hcount
  have hsq : Cc.natDeg + (Rs.map degYZ).sum * (Rs.map degYZ).sum ≤
      (Cc.natDeg + (Rs.map degYZ).sum) * (Cc.natDeg + (Rs.map degYZ).sum) := by
    have := Nat.le_mul_self Cc.natDeg
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hDD := Nat.mul_le_mul hD hD
  rw [Nat.pow_two]
  omega

/-- `C · Π Rᵢ^{eᵢ}`. -/
def factored (Cc : UPoly (UPoly F)) (Rs : List (Poly3 F)) (e : Poly3 F → Nat) : Poly3 F :=
  mul (UPoly.C Cc) (UPoly.prodList (Rs.map fun R => CRing.npow R (e R)))

private theorem affine_npow_eq_zero (α β : F) (P : UPoly F) (R : Poly3 F) : ∀ k : Nat,
    evalAffineLine (CRing.npow R k) α β P = zero → evalAffineLine R α β P = zero
  | 0, h => by
    have h1 : evalAffineLine (one : Poly3 F) α β P = one := (affineLineHom α β P).map_one
    exact absurd (h1.symm.trans h) NontrivialRing.one_ne_zero
  | k + 1, h => by
    have h1 : evalAffineLine (mul (CRing.npow R k) R) α β P = zero := h
    rw [evalAffineLine_mul] at h1
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2
    · exact affine_npow_eq_zero α β P R k h2
    · exact h2

private theorem affine_prod_eq_zero (α β : F) (P : UPoly F) (e : Poly3 F → Nat) :
    ∀ Rs : List (Poly3 F),
      evalAffineLine (UPoly.prodList (Rs.map fun R => CRing.npow R (e R))) α β P = zero →
      ∃ R ∈ Rs, evalAffineLine R α β P = zero
  | [], h => by
    have h1 : evalAffineLine (one : Poly3 F) α β P = one := (affineLineHom α β P).map_one
    exact absurd (h1.symm.trans h) NontrivialRing.one_ne_zero
  | R :: Rs, h => by
    have h1 : evalAffineLine (mul (CRing.npow R (e R))
        (UPoly.prodList (Rs.map fun R => CRing.npow R (e R)))) α β P = zero := h
    rw [evalAffineLine_mul] at h1
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2
    · exact ⟨R, .head _, affine_npow_eq_zero α β P R _ h2⟩
    · obtain ⟨R', hR', hz⟩ := affine_prod_eq_zero α β P e Rs h2
      exact ⟨R', .tail _ hR', hz⟩

/-- **`[CWYZ26]` Lemma 4.3, simple-root part.** Outside the excluded set, a root `P` of
    `Q = C · Π Rᵢ^{eᵢ}` along the line `Y = α + βX` is a root of some factor `Rᵢ` at which the
    separant `∂_Z Rᵢ` does not vanish. -/
theorem simple_root_of_not_excluded (Cc : UPoly (UPoly F)) (Rs : List (Poly3 F))
    (e : Poly3 F → Nat) (hRs : ∀ R ∈ Rs, SqFactor R) (α β : F)
    (hnot : ¬ Excluded Cc Rs α β) (P : UPoly F)
    (hroot : evalAffineLine (factored Cc Rs e) α β P = zero) :
    ∃ R ∈ Rs, evalAffineLine R α β P = zero ∧ evalAffineLine (hasseZ 1 R) α β P ≠ zero := by
  have h1 : evalAffineLine (mul (UPoly.C Cc)
      (UPoly.prodList (Rs.map fun R => CRing.npow R (e R)))) α β P = zero := hroot
  rw [evalAffineLine_mul, evalAffineLine_C] at h1
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2
  · exact absurd (.inl h2) hnot
  · obtain ⟨R, hR, hz⟩ := affine_prod_eq_zero α β P e Rs h2
    refine ⟨R, hR, hz, fun hsep => hnot (.inr ⟨R, hR, ?_⟩)⟩
    have key : ∀ Q : Poly3 F, evalAffineLine Q α β P = zero →
        (liftK.toFun Q).eval2 ((Frac.of (D := UPoly F)).toFun (line α β))
          ((Frac.of (D := UPoly F)).toFun P) = zero := by
      intro Q hQ
      have := UPoly.eval₂_mapHom_mapHom (Frac.of (D := UPoly F)) Q (line α β) P
      show UPoly.eval₂ _ _ ((UPoly.mapHom (UPoly.mapHom Frac.of)).toFun Q) = zero
      rw [this]
      show (Frac.of (D := UPoly F)).toFun (evalAffineLine Q α β P) = zero
      rw [hQ, RingHom.map_zero]
    exact Poly2.eval_resZ_eq_zero _ _ (hRs R hR).natDeg_liftK _ _ (key R hz) (key _ hsep)

end Poly3

/-! ## Dynamic GCD splitting over a field -/

namespace UPoly
variable {K : Type} [LawfulField K] [DecidableEq K]

local instance : NoZeroDivisors K := LawfulField.toNoZeroDivisors K

/-- Euclidean division in `K[Z]`. -/
def divMod (a b : UPoly K) : UPoly K × UPoly K :=
  (ofList (polyDivMod a.coeffs b.coeffs).1, ofList (polyDivMod a.coeffs b.coeffs).2)

theorem divMod_spec (a b : UPoly K) (hb : b ≠ zero) :
    a = add (mul (divMod a b).1 b) (divMod a b).2 ∧
      (divMod a b).2.coeffs.length < b.coeffs.length := by
  have hb' : trimPoly b.coeffs ≠ [] := by
    rw [b.trimmed]; exact fun e => hb ((eq_zero_iff b).mpr e)
  have h := polyDivMod_spec a.coeffs b.coeffs hb'
  unfold divMod
  generalize polyDivMod a.coeffs b.coeffs = qr at h
  obtain ⟨q, r⟩ := qr
  obtain ⟨hq, hr, heq, hlen⟩ := h
  have hq' : trimPoly q = q := hq
  have hr' : trimPoly r = r := hr
  refine ⟨ext ?_, ?_⟩
  · show a.coeffs = pAdd (pMul (trimPoly q) b.coeffs) (trimPoly r)
    rw [hq', hr', ← heq, a.trimmed]
  · show (trimPoly r).length < b.coeffs.length
    rw [hr']; rwa [b.trimmed] at hlen

/-- Extended Euclid: `(g, u, v)` with `u·a + v·b = g` and `g` dividing both. -/
def xgcdAux : Nat → UPoly K → UPoly K → UPoly K × UPoly K × UPoly K
  | 0, a, _ => (a, one, zero)
  | fuel + 1, a, b =>
    if b = zero then (a, one, zero)
    else
      let r := xgcdAux fuel b (divMod a b).2
      (r.1, r.2.2, sub r.2.1 (mul r.2.2 (divMod a b).1))

theorem xgcdAux_spec : ∀ (fuel : Nat) (a b : UPoly K), b.coeffs.length ≤ fuel →
    add (mul (xgcdAux fuel a b).2.1 a) (mul (xgcdAux fuel a b).2.2 b) = (xgcdAux fuel a b).1 ∧
      (∃ s, a = mul (xgcdAux fuel a b).1 s) ∧ (∃ t, b = mul (xgcdAux fuel a b).1 t)
  | 0, a, b, h => by
    have hb : b = zero := (eq_zero_iff b).mpr (List.eq_nil_of_length_eq_zero (by omega))
    subst hb
    exact ⟨by show add (mul one a) (mul zero zero) = a; constructive_ring,
      ⟨one, (LawfulCommRing.mul_one a).symm⟩, ⟨zero, (LawfulCommRing.mul_zero a).symm⟩⟩
  | fuel + 1, a, b, h => by
    unfold xgcdAux
    split
    · next hb =>
      subst hb
      exact ⟨by show add (mul one a) (mul zero zero) = a; constructive_ring,
        ⟨one, (LawfulCommRing.mul_one a).symm⟩, ⟨zero, (LawfulCommRing.mul_zero a).symm⟩⟩
    · next hb =>
      obtain ⟨hdiv, hlen⟩ := divMod_spec a b hb
      obtain ⟨hbez, ⟨s, hs⟩, ⟨t, ht⟩⟩ := xgcdAux_spec fuel b (divMod a b).2 (by omega)
      generalize xgcdAux fuel b (divMod a b).2 = res at hbez hs ht
      generalize (divMod a b).1 = q at hdiv
      generalize (divMod a b).2 = r at hdiv hbez ht
      refine ⟨?_, ⟨add (mul q s) t, ?_⟩, ⟨s, hs⟩⟩
      · show add (mul res.2.2 a) (mul (sub res.2.1 (mul res.2.2 q)) b) = res.1
        rw [← hbez, hdiv]; constructive_ring
      · rw [hdiv, hs, ht]; constructive_ring

/-- A gcd of `R` and `G` with its Bézout cofactors. -/
def xgcd (R G : UPoly K) : UPoly K × UPoly K × UPoly K := xgcdAux G.coeffs.length R G

/-- **D5 splitting step.** Testing `G` against a modulus `R ≠ 0` has three outcomes: `G` is
    invertible modulo `R`; or `R` divides `G`; or `R = g·q` splits into two factors of
    positive degree, with `deg g + deg q = deg R`, so the degree sum of a factor list is
    preserved and its length strictly grows. -/
theorem d5_split (R G : UPoly K) (hR : R ≠ zero) :
    (∃ u v, add (mul u R) (mul v G) = one) ∨ (∃ t, G = mul R t) ∨
      (∃ g q, R = mul g q ∧ 0 < g.natDeg ∧ 0 < q.natDeg ∧ g.natDeg + q.natDeg = R.natDeg ∧
        ∃ t, G = mul g t) := by
  obtain ⟨hbez, ⟨s, hs⟩, ⟨t, ht⟩⟩ := xgcdAux_spec G.coeffs.length R G (Nat.le_refl _)
  generalize (xgcdAux G.coeffs.length R G).1 = g at hbez hs ht
  generalize (xgcdAux G.coeffs.length R G).2.1 = u at hbez
  generalize (xgcdAux G.coeffs.length R G).2.2 = v at hbez
  have hg : g ≠ zero := fun e => hR (by rw [hs, e, LawfulCommRing.zero_mul])
  have hs0 : s ≠ zero := fun e => hR (by rw [hs, e, LawfulCommRing.mul_zero])
  have hdeg : R.natDeg = g.natDeg + s.natDeg := by rw [hs]; exact natDeg_mul hg hs0
  have unit : ∀ p : UPoly K, p ≠ zero → p.natDeg = 0 → mul p (C (LawfulField.inv p.lead)) = one := by
    intro p hp hd
    have hpC : p = C p.lead := ext_coeffAt fun k => by
      cases k with
      | zero => rw [coeffAt_C_zero]; show _ = coeffAt p.coeffs p.natDeg; rw [hd]
      | succ k => rw [coeffAt_C_succ]; exact p.coeffAt_eq_zero_of_natDeg_lt (by omega)
    have h1 : mul (C p.lead) (C (LawfulField.inv p.lead)) = C (mul p.lead (LawfulField.inv p.lead)) :=
      (CHom.map_mul _ _).symm
    rw [LawfulField.mul_inv_cancel (lead_ne_zero hp)] at h1
    exact (congrArg (fun x => mul x (C (LawfulField.inv p.lead))) hpC).trans h1
  if h0 : g.natDeg = 0 then
    refine .inl ⟨mul (C (LawfulField.inv g.lead)) u, mul (C (LawfulField.inv g.lead)) v, ?_⟩
    rw [← unit g hg h0, ← hbez]; constructive_ring
  else if h1 : s.natDeg = 0 then
    refine .inr (.inl ⟨mul (C (LawfulField.inv s.lead)) t, ?_⟩)
    have hu := unit s hs0 h1
    have : mul R (mul (C (LawfulField.inv s.lead)) t) =
        mul g (mul (mul s (C (LawfulField.inv s.lead))) t) := by rw [hs]; constructive_ring
    rw [this, hu, ht]; constructive_ring
  else
    exact .inr (.inr ⟨g, s, hs, by omega, by omega, hdeg.symm, t, ht⟩)

end UPoly

/-! ## Witnesses -/

namespace Poly3.SplitTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `R = Z² - Y`. -/
def rPar : Poly3 Goldilocks := ofList [ofList [zero, neg one], zero, one]

/-- `C = Y - (3 + 5X)`, vanishing exactly on the line `(α, β) = (3, 5)`. -/
def cLine : UPoly (UPoly Goldilocks) := ofList [neg (line (g 3) (g 5)), one]

/-- `2·R - Z·∂_Z R = -2Y` certifies that `Z² - Y` is squarefree in `Z`. -/
theorem sqFactor_rPar : SqFactor rPar :=
  SqFactor.of_cert (by decide) (ofList [ofList [ofList [g 2]]]) (ofList [zero, neg one])
    (ofList [zero, ofList [neg (g 2)]]) (by decide) (by decide +kernel)

/-- The hypotheses of `excluded_pairs_card_le` hold together, with a genuinely excluded pair. -/
theorem inhabited_excluded_pairs :
    ∃ (Cc : UPoly (UPoly Goldilocks)) (Rs : List (Poly3 Goldilocks)) (D : Nat)
      (E : List (Goldilocks × Goldilocks)), Cc ≠ zero ∧ (∀ R ∈ Rs, SqFactor R) ∧
      Cc.natDeg + (Rs.map degYZ).sum ≤ D ∧ E.Nodup ∧
      (∀ p ∈ E, Excluded Cc Rs p.1 p.2) ∧ E.length = 1 :=
  ⟨cLine, [rPar], 3, [(g 3, g 5)], (by decide),
    (fun R hR => by rw [List.mem_singleton.mp hR]; exact sqFactor_rPar), (by decide),
    (by decide),
    (fun p hp => by rw [List.mem_singleton.mp hp]; exact Or.inl (by decide +kernel)), rfl⟩

/-- The content must be nonzero: with `C = 0` every pair is excluded, so no bound holds. -/
theorem tooth_excluded_needs_content :
    ∃ (Rs : List (Poly3 Goldilocks)) (D : Nat) (E : List (Goldilocks × Goldilocks)),
      (∀ R ∈ Rs, SqFactor R) ∧
      (zero : UPoly (UPoly Goldilocks)).natDeg + (Rs.map degYZ).sum ≤ D ∧ E.Nodup ∧
      (∀ p ∈ E, Excluded zero Rs p.1 p.2) ∧ ¬ E.length ≤ D ^ 2 :=
  ⟨[], 0, [(g 0, g 0), (g 1, g 1)], (fun _ h => by cases h), (by decide), (by decide),
    (fun _ _ => Or.inl (UPoly.eval₂_zero _ _)), (by decide)⟩

/-- A root on a non-excluded line: on `Y = 1` the factor `Z² - 1` has the simple root
    `P = 1`. The separant eliminant is computed over `F(X)` by the kernel. -/
theorem inhabited_simple_root :
    ∃ (Cc : UPoly (UPoly Goldilocks)) (Rs : List (Poly3 Goldilocks))
      (e : Poly3 Goldilocks → Nat) (α β : Goldilocks) (P : UPoly Goldilocks),
      (∀ R ∈ Rs, SqFactor R) ∧ ¬ Excluded Cc Rs α β ∧
      evalAffineLine (factored Cc Rs e) α β P = zero :=
  ⟨one, [rPar], fun _ => 1, g 1, g 0, ofList [g 1],
    (fun R hR => by rw [List.mem_singleton.mp hR]; exact sqFactor_rPar),
    (by show ¬ (_ ∨ ∃ R ∈ [rPar], _); decide +kernel), (by decide +kernel)⟩

#verify_constructive excluded_pairs_card_le simple_root_of_not_excluded sepElim_ne_zero
#verify_constructive natDeg_sepElim_le sqFactor_rPar Frac.of_injective UPoly.d5_split
#tooth_pair excluded_pairs_card_le vs tooth_excluded_needs_content
#verify_inhabited excluded_pairs_card_le inhabited_excluded_pairs
#verify_inhabited simple_root_of_not_excluded inhabited_simple_root

end Poly3.SplitTests

end Qsag
end
