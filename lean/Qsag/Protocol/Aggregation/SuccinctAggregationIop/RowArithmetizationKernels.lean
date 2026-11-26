module


public import Qsag.Protocol.Aggregation.SuccinctAggregationIop.NativeSigEngine

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv
set_option autoImplicit false
set_option exponentiation.threshold 2048
attribute [local irreducible] verifyUpperLayers
attribute [local irreducible] computeMessageMu
attribute [local irreducible] verifyAggNativeSigStateful verifyAggNativeSigStateless


/-! ### Quadratic-extension identities over an arbitrary `LawfulCommRing` -/

private theorem ringMulMulMulComm {R : Type} [LawfulCommRing R] (a b c d : R) :
    CommRingOps.mul (CommRingOps.mul a b) (CommRingOps.mul c d) =
      CommRingOps.mul (CommRingOps.mul a c) (CommRingOps.mul b d) := by
  rw [LawfulCommRing.mul_assoc, ← LawfulCommRing.mul_assoc b c d, LawfulCommRing.mul_comm b c,
    LawfulCommRing.mul_assoc c b d, ← LawfulCommRing.mul_assoc]

private theorem ringEqNegOfAddEqZero {R : Type} [LawfulCommRing R] {a b : R}
    (h : CommRingOps.add a b = CommRingOps.zero) : a = CommRingOps.neg b := by
  have h1 : CommRingOps.add (CommRingOps.add a b) (CommRingOps.neg b) =
      CommRingOps.add CommRingOps.zero (CommRingOps.neg b) :=
    congrArg (fun z => CommRingOps.add z (CommRingOps.neg b)) h
  rw [LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero,
    LawfulCommRing.zero_add] at h1
  exact h1

private theorem quadExtMulComm0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 : R) :
    CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1)) =
      CommRingOps.add (CommRingOps.mul y0 x0) (CommRingOps.mul n (CommRingOps.mul y1 x1)) := by
  rw [LawfulCommRing.mul_comm x0 y0, LawfulCommRing.mul_comm x1 y1]

private theorem quadExtMulComm1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 : R) :
    CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0) =
      CommRingOps.add (CommRingOps.mul y0 x1) (CommRingOps.mul y1 x0) := by
  rw [LawfulCommRing.mul_comm x0 y1, LawfulCommRing.mul_comm x1 y0]
  exact LawfulCommRing.add_comm _ _

private theorem quadExtOneMul0 {R : Type} [LawfulCommRing R] (n x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul CommRingOps.one x0)
      (CommRingOps.mul n (CommRingOps.mul CommRingOps.zero x1)) = x0 := by
  rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero,
    LawfulCommRing.add_zero]

private theorem quadExtOneMul1 {R : Type} [LawfulCommRing R] (x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul CommRingOps.one x1)
      (CommRingOps.mul CommRingOps.zero x0) = x1 := by
  rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

private theorem quadExtMulOne0 {R : Type} [LawfulCommRing R] (n x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul x0 CommRingOps.one)
      (CommRingOps.mul n (CommRingOps.mul x1 CommRingOps.zero)) = x0 := by
  rw [LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
    LawfulCommRing.add_zero]

private theorem quadExtMulOne1 {R : Type} [LawfulCommRing R] (x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul x0 CommRingOps.zero)
      (CommRingOps.mul x1 CommRingOps.one) = x1 := by
  rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.zero_add]

private theorem quadExtLeftDistrib0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul x0 (CommRingOps.add y0 z0))
      (CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.add y1 z1))) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1)))
      (CommRingOps.add (CommRingOps.mul x0 z0) (CommRingOps.mul n (CommRingOps.mul x1 z1))) := by
  rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtLeftDistrib1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul x0 (CommRingOps.add y1 z1))
      (CommRingOps.mul x1 (CommRingOps.add y0 z0)) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0))
      (CommRingOps.add (CommRingOps.mul x0 z1) (CommRingOps.mul x1 z0)) := by
  rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtRightDistrib0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul (CommRingOps.add x0 y0) z0)
      (CommRingOps.mul n (CommRingOps.mul (CommRingOps.add x1 y1) z1)) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 z0) (CommRingOps.mul n (CommRingOps.mul x1 z1)))
      (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtRightDistrib1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul (CommRingOps.add x0 y0) z1)
      (CommRingOps.mul (CommRingOps.add x1 y1) z0) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 z1) (CommRingOps.mul x1 z0))
      (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtMulAssoc0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1))) z0)
      (CommRingOps.mul n
        (CommRingOps.mul (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0)) z1)) =
    CommRingOps.add
      (CommRingOps.mul x0
        (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1))))
      (CommRingOps.mul n
        (CommRingOps.mul x1 (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  have t1 : CommRingOps.mul (CommRingOps.mul x0 y0) z0 =
      CommRingOps.mul x0 (CommRingOps.mul y0 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  have t2 : CommRingOps.mul (CommRingOps.mul n (CommRingOps.mul x1 y1)) z0 =
      CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.mul y1 z0)) := by
    rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc]
  have t3 : CommRingOps.mul n (CommRingOps.mul (CommRingOps.mul x0 y1) z1) =
      CommRingOps.mul x0 (CommRingOps.mul n (CommRingOps.mul y1 z1)) := by
    rw [LawfulCommRing.mul_assoc x0 y1 z1,
        ← LawfulCommRing.mul_assoc n x0 _,
        LawfulCommRing.mul_comm n x0,
        LawfulCommRing.mul_assoc]
  have t4 : CommRingOps.mul n (CommRingOps.mul (CommRingOps.mul x1 y0) z1) =
      CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.mul y0 z1)) := by
    rw [LawfulCommRing.mul_assoc]
  rw [t1, t2, t3, t4, LawfulCommRing.add_add_add_comm]
  congr 1
  exact LawfulCommRing.add_comm _ _

private theorem quadExtMulAssoc1 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1))) z1)
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0)) z0) =
    CommRingOps.add
      (CommRingOps.mul x0
        (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)))
      (CommRingOps.mul x1
        (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1)))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  have s1 : CommRingOps.mul (CommRingOps.mul x0 y0) z1 =
      CommRingOps.mul x0 (CommRingOps.mul y0 z1) :=
    LawfulCommRing.mul_assoc _ _ _
  have s2 : CommRingOps.mul (CommRingOps.mul n (CommRingOps.mul x1 y1)) z1 =
      CommRingOps.mul x1 (CommRingOps.mul n (CommRingOps.mul y1 z1)) := by
    rw [LawfulCommRing.mul_assoc n _ z1,
        LawfulCommRing.mul_assoc x1 y1 z1,
        ← LawfulCommRing.mul_assoc n x1 _,
        LawfulCommRing.mul_comm n x1,
        LawfulCommRing.mul_assoc]
  have s3 : CommRingOps.mul (CommRingOps.mul x0 y1) z0 =
      CommRingOps.mul x0 (CommRingOps.mul y1 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  have s4 : CommRingOps.mul (CommRingOps.mul x1 y0) z0 =
      CommRingOps.mul x1 (CommRingOps.mul y0 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  rw [s1, s2, s3, s4, LawfulCommRing.add_add_add_comm]
  congr 1
  exact LawfulCommRing.add_comm _ _

/-- Karatsuba middle term: `(x0 + x1)(y0 + y1) - x0 y0 - x1 y1 = x0 y1 + x1 y0`. -/
private theorem quadExtKaratsubaMid {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 : R) :
    CommRingOps.sub
      (CommRingOps.sub (CommRingOps.mul (CommRingOps.add x0 x1) (CommRingOps.add y0 y1))
        (CommRingOps.mul x0 y0))
      (CommRingOps.mul x1 y1) =
    CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0) := by
  have hsub : ∀ p q : R, CommRingOps.sub (CommRingOps.add p q) q = p := by
    intro p q
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg,
      LawfulCommRing.add_zero]
  have hexp : CommRingOps.mul (CommRingOps.add x0 x1) (CommRingOps.add y0 y1) =
      CommRingOps.add
        (CommRingOps.add (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0))
          (CommRingOps.mul x1 y1))
        (CommRingOps.mul x0 y0) := by
    rw [LawfulCommRing.right_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
      LawfulCommRing.add_comm (CommRingOps.mul x0 y0) (CommRingOps.mul x0 y1),
      LawfulCommRing.add_add_add_comm,
      LawfulCommRing.add_comm (CommRingOps.mul x0 y0) (CommRingOps.mul x1 y1),
      ← LawfulCommRing.add_assoc]
  rw [hexp, hsub, hsub]


/-! ## §2. Exact Degree-8 Row Sumcheck Arithmetization (`arithmetize.rs`, `trace.rs`, `ROW_SUMCHECK_DEGREE = 8`) -/

/-- Exact degree of each row-sumcheck univariate round polynomial (`1` from `eq(tau, x)` + `7` from `x^7`). -/
def rowSumcheckDegree : Nat := 8


def rowSumcheckCoeffs : Nat := 9

/-! ### Univariate Polynomial Ring Algebra & Exact Degree-8 Bound -/

private theorem gold_one_eq : Goldilocks.one = (CommRingOps.one : Goldilocks) := by rfl
private theorem gold_zero_eq : Goldilocks.zero = (CommRingOps.zero : Goldilocks) := by rfl

/-- Ring identity behind the affine form of the equality factor:
    `(1 - τ) + x · (τ - (1 - τ)) = (1 - τ) · (1 - x) + τ · x`. -/
private theorem eqFactor_affine_identity {R : Type} [LawfulCommRing R] (tau x : R) :
    CommRingOps.add (CommRingOps.sub CommRingOps.one tau)
        (CommRingOps.mul x (CommRingOps.sub tau (CommRingOps.sub CommRingOps.one tau))) =
      CommRingOps.add
        (CommRingOps.mul (CommRingOps.sub CommRingOps.one tau) (CommRingOps.sub CommRingOps.one x))
        (CommRingOps.mul tau x) := by
  rw [LawfulCommRing.sub_eq_add_neg CommRingOps.one x,
      LawfulCommRing.left_distrib (CommRingOps.sub CommRingOps.one tau) CommRingOps.one (CommRingOps.neg x),
      LawfulCommRing.mul_one,
      LawfulCommRing.mul_neg,
      LawfulCommRing.add_assoc (CommRingOps.sub CommRingOps.one tau)]
  congr 1
  rw [LawfulCommRing.mul_comm (CommRingOps.sub CommRingOps.one tau) x,
      LawfulCommRing.mul_comm tau x,
      ← LawfulCommRing.mul_neg x (CommRingOps.sub CommRingOps.one tau),
      ← LawfulCommRing.left_distrib x,
      LawfulCommRing.add_comm (CommRingOps.neg (CommRingOps.sub CommRingOps.one tau)) tau,
      ← LawfulCommRing.sub_eq_add_neg]

def polyAddCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], ds => ds
  | cs, [] => cs
  | c :: cs, d :: ds => CommRingOps.add c d :: polyAddCoeffs cs ds

theorem polyAddCoeffs_length {R : Type} [CommRingOps R] :
    ∀ (cs ds : List R), (polyAddCoeffs cs ds).length = Nat.max cs.length ds.length
  | [], ds => by simp [polyAddCoeffs]
  | c :: cs, [] => by simp [polyAddCoeffs]
  | c :: cs, d :: ds => by
    simp [polyAddCoeffs, polyAddCoeffs_length cs ds, Nat.succ_max_succ]

theorem evalCoeffs_polyAddCoeffs {R : Type} [LawfulCommRing R] :
    ∀ (cs ds : List R) (x : R),
      RoundPoly.evalCoeffs (polyAddCoeffs cs ds) x =
        CommRingOps.add (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x)
  | [], ds, x => by
    simp [polyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | c :: cs, [], x => by
    simp [polyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | c :: cs, d :: ds, x => by
    simp only [polyAddCoeffs, RoundPoly.evalCoeffs, evalCoeffs_polyAddCoeffs cs ds x]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

def polyScaleCoeffs {R : Type} [CommRingOps R] (s : R) : List R → List R
  | [] => []
  | c :: cs => CommRingOps.mul s c :: polyScaleCoeffs s cs

theorem polyScaleCoeffs_length {R : Type} [CommRingOps R] (s : R) :
    ∀ (cs : List R), (polyScaleCoeffs s cs).length = cs.length
  | [] => rfl
  | _ :: cs => by simp [polyScaleCoeffs, polyScaleCoeffs_length s cs]

theorem evalCoeffs_polyScaleCoeffs {R : Type} [LawfulCommRing R] (s : R) :
    ∀ (cs : List R) (x : R),
      RoundPoly.evalCoeffs (polyScaleCoeffs s cs) x =
        CommRingOps.mul s (RoundPoly.evalCoeffs cs x)
  | [], _ => by
    simp [polyScaleCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    simp only [polyScaleCoeffs, RoundPoly.evalCoeffs, evalCoeffs_polyScaleCoeffs s cs x]
    rw [LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc s x _,
        LawfulCommRing.mul_comm s x,
        LawfulCommRing.mul_assoc x s _]

def polyMulCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], _ => []
  | c :: rest, ds =>
    match rest with
    | [] => polyScaleCoeffs c ds
    | c1 :: cs =>
      polyAddCoeffs (polyScaleCoeffs c ds) (CommRingOps.zero :: polyMulCoeffs (c1 :: cs) ds)
  termination_by structural cs _ => cs

theorem polyMulCoeffs_length_le {R : Type} [CommRingOps R] :
    ∀ (cs ds : List R) (d1 d2 : Nat),
      cs.length ≤ d1 + 1 →
      ds.length ≤ d2 + 1 →
      (polyMulCoeffs cs ds).length ≤ d1 + d2 + 1
  | [], _, _, _, _, _ => by simp [polyMulCoeffs]
  | c :: rest, ds, d1, d2, h1, h2 =>
    match rest, h1 with
    | [], _ => by
      simp only [polyMulCoeffs, polyScaleCoeffs_length]
      omega
    | c1 :: cs, h1 => by
      cases d1 with
      | zero =>
        simp only [List.length_cons] at h1
        omega
      | succ d1' =>
        have hTail : (c1 :: cs).length ≤ d1' + 1 := by
          simp only [List.length_cons] at h1 ⊢
          omega
        have ih := polyMulCoeffs_length_le (c1 :: cs) ds d1' d2 hTail h2
        simp only [polyMulCoeffs, polyAddCoeffs_length, polyScaleCoeffs_length, List.length_cons]
        exact Nat.max_le.mpr ⟨by omega, by omega⟩
  termination_by structural cs _ _ _ _ _ => cs

theorem evalCoeffs_polyMulCoeffs {R : Type} [LawfulCommRing R] :
    ∀ (cs ds : List R) (x : R),
      RoundPoly.evalCoeffs (polyMulCoeffs cs ds) x =
        CommRingOps.mul (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x)
  | [], _, _ => by
    simp [polyMulCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | c :: rest, ds, x =>
    match rest with
    | [] => by
      simp only [polyMulCoeffs, RoundPoly.evalCoeffs, evalCoeffs_polyScaleCoeffs,
        LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | c1 :: cs => by
      let tl := c1 :: cs
      have ih := evalCoeffs_polyMulCoeffs tl ds x
      simp only [polyMulCoeffs, evalCoeffs_polyAddCoeffs, evalCoeffs_polyScaleCoeffs,
        RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
      rw [ih, ← LawfulCommRing.mul_assoc x (RoundPoly.evalCoeffs tl x) _,
          ← LawfulCommRing.right_distrib]
      rfl
  termination_by structural cs _ _ => cs


/-! ### Multilinear Equality & Inter-Row Shift Kernel (`arithmetize.rs:66-106`) -/


/-- Polymorphic zip-product over `{R : Type}` (compiles to pure `List.rec` in `< 1ms`). -/
@[expose] def evalZipProdPoly {R : Type} (oneVal zeroVal : R) (mulFn factorFn : R → R → R) :
    List R → List R → R
  | [], [] => oneVal
  | t :: ts, x :: xs => mulFn (factorFn t x) (evalZipProdPoly oneVal zeroVal mulFn factorFn ts xs)
  | [], _ :: _ => zeroVal
  | _ :: _, [] => zeroVal


private theorem lt_two_eq_of_beq_zero_eq :
    ∀ {a b : Nat}, a < 2 → b < 2 → (a == 0) = (b == 0) → a = b
  | 0, 0, _, _, _ => rfl
  | 1, 1, _, _, _ => rfl
  | 0, 1, _, _, h => absurd h (by decide)
  | 1, 0, _, _, h => absurd h (by decide)
  | _ + 2, _, ha, _, _ => absurd ha (Nat.not_lt_of_le (Nat.le_add_left 2 _))
  | _, _ + 2, _, hb, _ => absurd hb (Nat.not_lt_of_le (Nat.le_add_left 2 _))


/-! ### Multilinear Inter-Row Shift Kernel Identities (`arithmetize.rs:63-106`) -/


@[expose] def evalShiftPoly {R : Type} (zeroVal : R) (addFn mulFn eqTermFn carryTermFn : R → R → R)
    (eqTailFn : List R → List R → R) : List R → List R → R
  | [], [] => zeroVal
  | t :: ts, x :: xs =>
    addFn
      (mulFn (eqTermFn t x) (eqTailFn ts xs))
      (mulFn (carryTermFn t x) (evalShiftPoly zeroVal addFn mulFn eqTermFn carryTermFn eqTailFn ts xs))
  | [], _ :: _ => zeroVal
  | _ :: _, [] => zeroVal


end Qsag
end
