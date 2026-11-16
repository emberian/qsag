module
/- Exact FIPS 204 polynomial trees, negacyclic multiplication and NTT correctness. -/
public import Qsag.Math.MlDsaField
public section
namespace Qsag
set_option autoImplicit false
/-- Inductive binary tree of $2^d$ field elements (`0` `module` opacity mismatch). -/
inductive PolyTree : Nat → Type where
  | leaf (x : Fq204) : PolyTree 0
  | branch {d : Nat} (lo hi : PolyTree d) : PolyTree (d + 1)
  deriving Repr

@[expose, instance_reducible] def instDecidableEqPolyTree : {d : Nat} → DecidableEq (PolyTree d)
  | 0, .leaf a, .leaf b =>
    if h : a = b then isTrue (by cases h; rfl)
    else isFalse (fun hEq => h (PolyTree.leaf.inj hEq))
  | _ + 1, .branch a b, .branch c d =>
    match instDecidableEqPolyTree a c with
    | isFalse h => isFalse (fun hEq => h (PolyTree.branch.inj hEq).1)
    | isTrue h =>
      match instDecidableEqPolyTree b d with
      | isFalse h' => isFalse (fun hEq => h' (PolyTree.branch.inj hEq).2)
      | isTrue h' => isTrue (by cases h; cases h'; rfl)
attribute [instance] instDecidableEqPolyTree

/-- Exact 256-coefficient polynomial / NTT vector over $\mathbb{Z}_{8380417}$ ($2^8 = 256$). -/
abbrev Poly256 := PolyTree 8

namespace PolyTree

@[expose] def zero : (d : Nat) → PolyTree d
  | 0 => .leaf Fq204.zero
  | d + 1 => .branch (zero d) (zero d)

@[expose] def constUnit : (d : Nat) → PolyTree d
  | 0 => .leaf Fq204.one
  | d + 1 => .branch (constUnit d) (zero d)

def ones : (d : Nat) → PolyTree d
  | 0 => .leaf Fq204.one
  | d + 1 => .branch (ones d) (ones d)

instance (d : Nat) : Inhabited (PolyTree d) := ⟨zero d⟩

@[expose] def add : {d : Nat} → PolyTree d → PolyTree d → PolyTree d
  | 0, .leaf a, .leaf b => .leaf (Fq204.add a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => .branch (add a0 b0) (add a1 b1)

@[expose] def sub : {d : Nat} → PolyTree d → PolyTree d → PolyTree d
  | 0, .leaf a, .leaf b => .leaf (Fq204.sub a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => .branch (sub a0 b0) (sub a1 b1)

@[expose] def neg : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf a => .leaf (Fq204.neg a)
  | _ + 1, .branch a0 a1 => .branch (neg a0) (neg a1)

@[expose] def scale (k : Fq204) : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf a => .leaf (Fq204.mul k a)
  | _ + 1, .branch a0 a1 => .branch (scale k a0) (scale k a1)

@[expose] def pointwiseMul : {d : Nat} → PolyTree d → PolyTree d → PolyTree d
  | 0, .leaf a, .leaf b => .leaf (Fq204.mul a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => .branch (pointwiseMul a0 b0) (pointwiseMul a1 b1)

@[expose] def toList : {d : Nat} → PolyTree d → List Fq204
  | 0, .leaf x => [x]
  | _ + 1, .branch lo hi => toList lo ++ toList hi

@[simp] theorem length_toList : ∀ {d : Nat} (p : PolyTree d), (toList p).length = 2 ^ d
  | 0, .leaf _ => by rfl
  | d + 1, .branch lo hi => by
    simp only [toList, List.length_append, length_toList, Nat.pow_succ]
    omega

@[expose] def ofList : (d : Nat) → List Fq204 → PolyTree d
  | 0, xs => .leaf (xs.headD Fq204.zero)
  | d + 1, xs =>
    let half := 2 ^ d
    .branch (ofList d (xs.take half)) (ofList d (xs.drop half))

theorem ofList_toList : ∀ {d : Nat} (p : PolyTree d), ofList d (toList p) = p
  | 0, .leaf _ => by rfl
  | d + 1, .branch lo hi => by
    simp only [toList, ofList]
    have hlen : (toList lo).length = 2 ^ d := length_toList lo
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append, ofList_toList lo, ofList_toList hi]

theorem toList_ofList : ∀ {d : Nat} {xs : List Fq204}, xs.length = 2 ^ d → toList (ofList d xs) = xs
  | 0, xs, hlen => by
    cases xs with
    | nil => exact absurd hlen (by decide)
    | cons x rest =>
      cases rest with
      | nil => rfl
      | cons _ _ => simp only [List.length_cons] at hlen; omega
  | d + 1, xs, hlen => by
    simp only [ofList, toList]
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    have htake : (xs.take (2 ^ d)).length = 2 ^ d := by
      rw [List.length_take, hlen, hpow]; omega
    have hdrop : (xs.drop (2 ^ d)).length = 2 ^ d := by
      rw [List.length_drop, hlen, hpow]; omega
    rw [toList_ofList htake, toList_ofList hdrop, List.take_append_drop]

/-- Infinity norm $\max_{j} |p_j \bmod^\pm q|$ across all $2^d$ coefficients. -/
@[expose] def infNorm : {d : Nat} → PolyTree d → Nat
  | 0, .leaf x => Fq204.centeredAbs x
  | _ + 1, .branch lo hi => max (infNorm lo) (infNorm hi)

/-- Taxicab ($\ell_1$) norm $\sum_j |p_j \bmod^\pm q|$. -/
def l1Norm : {d : Nat} → PolyTree d → Nat
  | 0, .leaf x => Fq204.centeredAbs x
  | _ + 1, .branch lo hi => l1Norm lo + l1Norm hi

/-- Leafwise predicate over a single `PolyTree d`. -/
def AllLeaves : {d : Nat} → (Fq204 → Prop) → PolyTree d → Prop
  | 0, P, .leaf a => P a
  | _ + 1, P, .branch a0 a1 => AllLeaves P a0 ∧ AllLeaves P a1

end PolyTree

/-- Exact 8-stage Cooley–Tukey radix-2 butterfly recursion (`fips204_ntt.rs:Poly256::ntt`). -/
def nttStage : (d : Nat) → Nat → PolyTree d → PolyTree d
  | 0, _, .leaf x => .leaf x
  | d + 1, e, .branch lo hi =>
    let z := Fq204.pow mldsaZeta (e / 2)
    let zh := PolyTree.scale z hi
    .branch (nttStage d (e / 2) (PolyTree.add lo zh))
            (nttStage d (e / 2 + 256) (PolyTree.sub lo zh))

/-- Exact 8-stage Gentleman–Sande inverse butterfly recursion (`fips204_ntt.rs:Poly256::inv_ntt`). -/
def invNttStage : (d : Nat) → Nat → PolyTree d → PolyTree d
  | 0, _, .leaf x => .leaf x
  | d + 1, e, .branch u v =>
    let u' := invNttStage d (e / 2) u
    let v' := invNttStage d (e / 2 + 256) v
    let zInv := Fq204.inv (Fq204.pow mldsaZeta (e / 2))
    .branch (PolyTree.scale mldsaInv2 (PolyTree.add u' v'))
            (PolyTree.scale (Fq204.mul mldsaInv2 zInv) (PolyTree.sub u' v'))

/-- Forward 256-point NIST FIPS 204 NTT (`Algorithm 41`). -/
def fips204Ntt (p : Poly256) : Poly256 := nttStage 8 256 p

/-- Inverse 256-point NIST FIPS 204 NTT (`Algorithm 42`). -/
def fips204InvNtt (u : Poly256) : Poly256 := invNttStage 8 256 u

private theorem mldsaZeta_pow_ne_zero (k : Nat) : Fq204.pow mldsaZeta k ≠ Fq204.zero := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro h0
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0 with h1 | h2
    · exact ih h1
    · exact absurd h2 (by decide)

private theorem polyTree_butterfly_left_inv {d : Nat} (z : Fq204) (hz : z ≠ Fq204.zero)
    (lo hi : PolyTree d) :
    let zh := PolyTree.scale z hi
    let u := PolyTree.add lo zh
    let v := PolyTree.sub lo zh
    PolyTree.branch (PolyTree.scale mldsaInv2 (PolyTree.add u v))
      (PolyTree.scale (Fq204.mul mldsaInv2 (Fq204.inv z)) (PolyTree.sub u v)) =
      PolyTree.branch lo hi := by
  induction d with
  | zero =>
    cases lo with | leaf a =>
    cases hi with | leaf b =>
    dsimp only [PolyTree.scale, PolyTree.add, PolyTree.sub]
    have hTwo : Fq204.add Fq204.one Fq204.one = Fq204.ofNat 2 := by decide
    have h1 : Fq204.mul mldsaInv2 (Fq204.add (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b))) = a := by
      have hsum : Fq204.add (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b)) =
          Fq204.mul (Fq204.ofNat 2) a := by
        rw [Fq204.sub_eq_add_neg, Fq204.add_assoc a (Fq204.mul z b),
            ← Fq204.add_assoc (Fq204.mul z b) a, Fq204.add_comm (Fq204.mul z b) a,
            Fq204.add_assoc a (Fq204.mul z b), Fq204.add_right_neg, Fq204.add_zero]
        calc Fq204.add a a = Fq204.add (Fq204.mul Fq204.one a) (Fq204.mul Fq204.one a) := by
              rw [Fq204.one_mul]
        _ = Fq204.mul (Fq204.ofNat 2) a := by rw [← Fq204.right_distrib, hTwo]
      rw [hsum, ← Fq204.mul_assoc, Fq204.mul_comm mldsaInv2, mldsa_two_mul_inv2, Fq204.one_mul]
    have h2 : Fq204.mul (Fq204.mul mldsaInv2 (Fq204.inv z))
        (Fq204.sub (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b))) = b := by
      have hdiff : Fq204.sub (Fq204.add a (Fq204.mul z b)) (Fq204.sub a (Fq204.mul z b)) =
          Fq204.mul (Fq204.ofNat 2) (Fq204.mul z b) := by
        apply Fq204.add_left_cancel (a := Fq204.sub a (Fq204.mul z b))
        rw [Fq204.sub_eq_add_neg (Fq204.add a _), Fq204.add_comm (Fq204.sub a _),
            Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
        calc Fq204.add a (Fq204.mul z b)
          _ = Fq204.add (Fq204.sub a (Fq204.mul z b)) (Fq204.add (Fq204.mul z b) (Fq204.mul z b)) := by
            rw [Fq204.sub_eq_add_neg, Fq204.add_assoc, ← Fq204.add_assoc (Fq204.neg _),
                Fq204.add_left_neg, Fq204.zero_add]
          _ = Fq204.add (Fq204.sub a (Fq204.mul z b)) (Fq204.mul (Fq204.ofNat 2) (Fq204.mul z b)) := by
            congr 1
            calc Fq204.add (Fq204.mul z b) (Fq204.mul z b)
              _ = Fq204.add (Fq204.mul Fq204.one (Fq204.mul z b)) (Fq204.mul Fq204.one (Fq204.mul z b)) := by
                rw [Fq204.one_mul]
              _ = Fq204.mul (Fq204.ofNat 2) (Fq204.mul z b) := by rw [← Fq204.right_distrib, hTwo]
      rw [hdiff, Fq204.mul_comm mldsaInv2 (Fq204.inv z), Fq204.mul_assoc (Fq204.inv z) mldsaInv2,
          ← Fq204.mul_assoc mldsaInv2 (Fq204.ofNat 2), Fq204.mul_comm mldsaInv2 (Fq204.ofNat 2),
          mldsa_two_mul_inv2, Fq204.one_mul, ← Fq204.mul_assoc, Fq204.inv_mul_cancel hz, Fq204.one_mul]
    rw [h1, h2]
  | succ d ih =>
    cases lo with | branch lo0 lo1 =>
    cases hi with | branch hi0 hi1 =>
    have ih0 := PolyTree.branch.inj (ih lo0 hi0)
    have ih1 := PolyTree.branch.inj (ih lo1 hi1)
    simp only [PolyTree.scale, PolyTree.add, PolyTree.sub, ih0.1, ih1.1, ih0.2, ih1.2]

private theorem polyTree_butterfly_right_inv {d : Nat} (z : Fq204) (hz : z ≠ Fq204.zero)
    (u v : PolyTree d) :
    let lo := PolyTree.scale mldsaInv2 (PolyTree.add u v)
    let hi := PolyTree.scale (Fq204.mul mldsaInv2 (Fq204.inv z)) (PolyTree.sub u v)
    let zh := PolyTree.scale z hi
    PolyTree.branch (PolyTree.add lo zh) (PolyTree.sub lo zh) = PolyTree.branch u v := by
  induction d with
  | zero =>
    cases u with | leaf a =>
    cases v with | leaf b =>
    dsimp only [PolyTree.scale, PolyTree.add, PolyTree.sub]
    have hTwo : Fq204.add Fq204.one Fq204.one = Fq204.ofNat 2 := by decide
    have hzh : Fq204.mul z (Fq204.mul (Fq204.mul mldsaInv2 (Fq204.inv z)) (Fq204.sub a b)) =
        Fq204.mul mldsaInv2 (Fq204.sub a b) := by
      rw [Fq204.mul_comm mldsaInv2 (Fq204.inv z), ← Fq204.mul_assoc z,
          ← Fq204.mul_assoc z (Fq204.inv z), Fq204.mul_inv_cancel hz, Fq204.one_mul]
    rw [hzh, ← Fq204.left_distrib]
    have hsum : Fq204.add (Fq204.add a b) (Fq204.sub a b) = Fq204.mul (Fq204.ofNat 2) a := by
      rw [Fq204.sub_eq_add_neg, Fq204.add_assoc a b, ← Fq204.add_assoc b a,
          Fq204.add_comm b a, Fq204.add_assoc a b, Fq204.add_right_neg, Fq204.add_zero]
      calc Fq204.add a a = Fq204.add (Fq204.mul Fq204.one a) (Fq204.mul Fq204.one a) := by
            rw [Fq204.one_mul]
      _ = Fq204.mul (Fq204.ofNat 2) a := by rw [← Fq204.right_distrib, hTwo]
    have h1 : Fq204.mul mldsaInv2 (Fq204.add (Fq204.add a b) (Fq204.sub a b)) = a := by
      rw [hsum, ← Fq204.mul_assoc, Fq204.mul_comm mldsaInv2, mldsa_two_mul_inv2, Fq204.one_mul]
    have h2 : Fq204.sub (Fq204.mul mldsaInv2 (Fq204.add a b)) (Fq204.mul mldsaInv2 (Fq204.sub a b)) = b := by
      apply Fq204.add_left_cancel (a := Fq204.mul mldsaInv2 (Fq204.sub a b))
      rw [Fq204.sub_eq_add_neg (Fq204.mul mldsaInv2 (Fq204.add a b)),
          Fq204.add_comm (Fq204.mul mldsaInv2 (Fq204.sub a b)),
          Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
      calc Fq204.mul mldsaInv2 (Fq204.add a b)
        _ = Fq204.add (Fq204.mul mldsaInv2 (Fq204.sub a b)) (Fq204.mul mldsaInv2 (Fq204.add b b)) := by
          rw [← Fq204.left_distrib]
          congr 1
          rw [Fq204.sub_eq_add_neg, Fq204.add_assoc, ← Fq204.add_assoc (Fq204.neg b),
              Fq204.add_left_neg, Fq204.zero_add]
        _ = Fq204.add (Fq204.mul mldsaInv2 (Fq204.sub a b)) b := by
          congr 1
          have hbb : Fq204.add b b = Fq204.mul (Fq204.ofNat 2) b := by
            calc Fq204.add b b = Fq204.add (Fq204.mul Fq204.one b) (Fq204.mul Fq204.one b) := by
                  rw [Fq204.one_mul]
            _ = Fq204.mul (Fq204.ofNat 2) b := by rw [← Fq204.right_distrib, hTwo]
          rw [hbb, ← Fq204.mul_assoc, Fq204.mul_comm mldsaInv2, mldsa_two_mul_inv2, Fq204.one_mul]
    rw [h1, h2]
  | succ d ih =>
    cases u with | branch u0 u1 =>
    cases v with | branch v0 v1 =>
    have ih0 := PolyTree.branch.inj (ih u0 v0)
    have ih1 := PolyTree.branch.inj (ih u1 v1)
    simp only [PolyTree.scale, PolyTree.add, PolyTree.sub, ih0.1, ih1.1, ih0.2, ih1.2]

private theorem invNttStage_nttStage : ∀ (d e : Nat) (p : PolyTree d),
    invNttStage d e (nttStage d e p) = p
  | 0, _, .leaf _ => rfl
  | d + 1, e, .branch lo hi => by
    simp only [nttStage, invNttStage, invNttStage_nttStage d]
    exact polyTree_butterfly_left_inv (Fq204.pow mldsaZeta (e / 2)) (mldsaZeta_pow_ne_zero _) lo hi

private theorem nttStage_invNttStage : ∀ (d e : Nat) (u : PolyTree d),
    nttStage d e (invNttStage d e u) = u
  | 0, _, .leaf _ => rfl
  | d + 1, e, .branch u v => by
    simp only [invNttStage]
    have h := PolyTree.branch.inj <|
      polyTree_butterfly_right_inv (Fq204.pow mldsaZeta (e / 2)) (mldsaZeta_pow_ne_zero _)
        (invNttStage d (e / 2) u) (invNttStage d (e / 2 + 256) v)
    simp only [nttStage, h.1, h.2, nttStage_invNttStage d]

/-- **`fips204InvNtt_ntt`**: 256-point FIPS 204 inverse NTT left-inverts forward NTT. -/
theorem fips204InvNtt_ntt (p : Poly256) : fips204InvNtt (fips204Ntt p) = p :=
  invNttStage_nttStage 8 256 p

/-- **`fips204Ntt_invNtt`**: 256-point FIPS 204 forward NTT right-inverts inverse NTT. -/
theorem fips204Ntt_invNtt (u : Poly256) : fips204Ntt (fips204InvNtt u) = u :=
  nttStage_invNttStage 8 256 u

/-! #### Coefficient-Domain Polynomial Evaluation & Negacyclic Convolution -/

/-- Horner polynomial evaluation $\sum_{j=0}^{m-1} p_j \omega^j$ over $\mathbb{Z}_q$. -/
def evalPoly204 : List Fq204 → Fq204 → Fq204
  | [], _ => Fq204.zero
  | c :: cs, w => Fq204.add c (Fq204.mul w (evalPoly204 cs w))

theorem evalPoly204_append : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (xs ++ ys) w =
      Fq204.add (evalPoly204 xs w) (Fq204.mul (Fq204.pow w xs.length) (evalPoly204 ys w))
  | [], ys, w => by
    dsimp only [List.nil_append, evalPoly204, List.length_nil, Fq204.pow]
    rw [Fq204.zero_add, Fq204.one_mul]
  | c :: cs, ys, w => by
    simp only [List.cons_append, evalPoly204, evalPoly204_append cs ys w, List.length_cons,
      Fq204.pow, Fq204.left_distrib, Fq204.add_assoc]
    congr 2
    rw [← Fq204.mul_assoc, Fq204.mul_comm w (Fq204.pow w cs.length)]

def addPolyList : List Fq204 → List Fq204 → List Fq204
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => Fq204.add x y :: addPolyList xs ys

def subPolyList : List Fq204 → List Fq204 → List Fq204
  | [], [] => []
  | [], y :: ys => Fq204.neg y :: subPolyList [] ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => Fq204.sub x y :: subPolyList xs ys

def scalePolyList (k : Fq204) : List Fq204 → List Fq204
  | [] => []
  | x :: xs => Fq204.mul k x :: scalePolyList k xs

/-- Unreduced Cauchy product of two polynomials in $\mathbb{Z}_q[X]$. -/
def cauchyMulList : List Fq204 → List Fq204 → List Fq204
  | [], _ => []
  | a :: as, bs => addPolyList (scalePolyList a bs) (Fq204.zero :: cauchyMulList as bs)

theorem evalPoly204_addPolyList : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (addPolyList xs ys) w = Fq204.add (evalPoly204 xs w) (evalPoly204 ys w)
  | [], ys, w => by dsimp only [addPolyList, evalPoly204]; rw [Fq204.zero_add]
  | x :: xs, [], w => by dsimp only [addPolyList, evalPoly204]; rw [Fq204.add_zero]
  | x :: xs, y :: ys, w => by
    simp only [addPolyList, evalPoly204, evalPoly204_addPolyList xs ys w, Fq204.left_distrib]
    rw [Fq204.add_assoc x y,
        ← Fq204.add_assoc y (Fq204.mul w (evalPoly204 xs w)),
        Fq204.add_comm y (Fq204.mul w (evalPoly204 xs w)),
        Fq204.add_assoc (Fq204.mul w (evalPoly204 xs w)) y,
        ← Fq204.add_assoc x (Fq204.mul w (evalPoly204 xs w))]

theorem evalPoly204_subPolyList : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (subPolyList xs ys) w = Fq204.sub (evalPoly204 xs w) (evalPoly204 ys w)
  | [], [], _ => by dsimp only [subPolyList, evalPoly204]; rw [Fq204.sub_zero]
  | [], y :: ys, w => by
    simp only [subPolyList, evalPoly204, evalPoly204_subPolyList [] ys w]
    rw [Fq204.sub_eq_add_neg, Fq204.zero_add, Fq204.sub_eq_add_neg Fq204.zero,
        Fq204.zero_add, Fq204.mul_neg, Fq204.neg_add]
  | x :: xs, [], w => by dsimp only [subPolyList, evalPoly204]; rw [Fq204.sub_zero]
  | x :: xs, y :: ys, w => by
    simp only [subPolyList, evalPoly204, evalPoly204_subPolyList xs ys w,
      Fq204.sub_eq_add_neg, Fq204.left_distrib, Fq204.mul_neg, Fq204.neg_add]
    rw [Fq204.add_assoc x, ← Fq204.add_assoc (Fq204.neg y),
        Fq204.add_comm (Fq204.neg y) (Fq204.mul w _),
        Fq204.add_assoc (Fq204.mul w _), ← Fq204.add_assoc x]

theorem evalPoly204_scalePolyList (k : Fq204) : ∀ (xs : List Fq204) (w : Fq204),
    evalPoly204 (scalePolyList k xs) w = Fq204.mul k (evalPoly204 xs w)
  | [], _ => by dsimp only [scalePolyList, evalPoly204]; rw [Fq204.mul_zero]
  | x :: xs, w => by
    simp only [scalePolyList, evalPoly204, evalPoly204_scalePolyList k xs w, Fq204.left_distrib]
    congr 1
    rw [← Fq204.mul_assoc, Fq204.mul_comm w k, Fq204.mul_assoc]

theorem evalPoly204_cauchyMulList : ∀ (xs ys : List Fq204) (w : Fq204),
    evalPoly204 (cauchyMulList xs ys) w = Fq204.mul (evalPoly204 xs w) (evalPoly204 ys w)
  | [], ys, _ => by dsimp only [cauchyMulList, evalPoly204]; rw [Fq204.zero_mul]
  | a :: as, ys, w => by
    simp only [cauchyMulList, evalPoly204, evalPoly204_addPolyList, evalPoly204_scalePolyList,
      Fq204.zero_add, evalPoly204_cauchyMulList as ys w, Fq204.right_distrib, Fq204.mul_assoc]

private theorem length_addPolyList : ∀ (xs ys : List Fq204),
    (addPolyList xs ys).length = max xs.length ys.length
  | [], ys => by simp [addPolyList]
  | x :: xs, [] => by simp [addPolyList]
  | _ :: xs, _ :: ys => by simp [addPolyList, length_addPolyList xs ys, Nat.succ_max_succ]

private theorem length_subPolyList_left : ∀ (xs ys : List Fq204),
    ys.length ≤ xs.length → (subPolyList xs ys).length = xs.length
  | xs, [], _ => by cases xs <;> rfl
  | [], _ :: _, h => by simp at h
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons] at h
    simp [subPolyList, length_subPolyList_left xs ys (by omega)]

private theorem length_scalePolyList (k : Fq204) : ∀ (xs : List Fq204),
    (scalePolyList k xs).length = xs.length
  | [] => rfl
  | _ :: xs => by simp [scalePolyList, length_scalePolyList k xs]

private theorem length_cauchyMulList : ∀ (xs ys : List Fq204),
    xs ≠ [] → ys ≠ [] → (cauchyMulList xs ys).length = xs.length + ys.length - 1
  | [], _, h, _ => False.elim (h rfl)
  | [a], ys, _, hys => by
    have hpos : 1 ≤ ys.length := by
      cases ys with
      | nil => exact False.elim (hys rfl)
      | cons _ _ => simp
    dsimp only [cauchyMulList]
    rw [length_addPolyList, length_scalePolyList]
    simp only [List.length_cons, List.length_nil]
    omega
  | a :: b :: as, ys, _, hys => by
    have hpos : 1 ≤ ys.length := by
      cases ys with
      | nil => exact False.elim (hys rfl)
      | cons _ _ => simp
    have ih := length_cauchyMulList (b :: as) ys (by simp) hys
    change (addPolyList (scalePolyList a ys) (Fq204.zero :: cauchyMulList (b :: as) ys)).length =
      (a :: b :: as).length + ys.length - 1
    rw [length_addPolyList, length_scalePolyList, List.length_cons, ih]
    simp only [List.length_cons]
    omega

/-- Coefficient-domain negacyclic multiplication in $\mathbb{Z}_q[X]/(X^{256} + 1)$ (`X^256 ≡ -1`). -/
def negacyclicMulList (xs ys : List Fq204) : List Fq204 :=
  let prod := cauchyMulList xs ys
  subPolyList (prod.take 256) (prod.drop 256)

/-- Coefficient-domain negacyclic multiplication on `Poly256`. -/
def negacyclicMul (a b : Poly256) : Poly256 :=
  PolyTree.ofList 8 (negacyclicMulList (PolyTree.toList a) (PolyTree.toList b))

theorem length_negacyclicMulList {xs ys : List Fq204}
    (hx : xs.length = 256) (hy : ys.length = 256) :
    (negacyclicMulList xs ys).length = 256 := by
  unfold negacyclicMulList
  have hxNe : xs ≠ [] := by intro h; rw [h] at hx; simp at hx
  have hyNe : ys ≠ [] := by intro h; rw [h] at hy; simp at hy
  have hlen : (cauchyMulList xs ys).length = 511 := by
    rw [length_cauchyMulList xs ys hxNe hyNe, hx, hy]
  have htake : ((cauchyMulList xs ys).take 256).length = 256 := by simp [hlen]
  have hdrop : ((cauchyMulList xs ys).drop 256).length = 255 := by simp [hlen]
  rw [length_subPolyList_left _ _ (by omega), htake]

/-- Evaluation at any root $\omega$ of $X^{256} + 1 = 0$ ($\omega^{256} = -1$) is a ring homomorphism. -/
theorem evalPoly204_negacyclicMulList {xs ys : List Fq204}
    (hx : xs.length = 256) (hy : ys.length = 256)
    {w : Fq204} (hw : Fq204.pow w 256 = Fq204.neg Fq204.one) :
    evalPoly204 (negacyclicMulList xs ys) w =
      Fq204.mul (evalPoly204 xs w) (evalPoly204 ys w) := by
  unfold negacyclicMulList
  have hxNe : xs ≠ [] := by intro h; rw [h] at hx; simp at hx
  have hyNe : ys ≠ [] := by intro h; rw [h] at hy; simp at hy
  have hlen : (cauchyMulList xs ys).length = 511 := by
    rw [length_cauchyMulList xs ys hxNe hyNe, hx, hy]
  let prod := cauchyMulList xs ys
  have hsplit : prod = prod.take 256 ++ prod.drop 256 := (List.take_append_drop 256 prod).symm
  have htakeLen : (prod.take 256).length = 256 := by dsimp [prod]; simp [hlen]
  have hevalProd : evalPoly204 prod w = Fq204.mul (evalPoly204 xs w) (evalPoly204 ys w) :=
    evalPoly204_cauchyMulList xs ys w
  rw [← hevalProd, hsplit, evalPoly204_append, htakeLen, hw, evalPoly204_subPolyList,
      Fq204.sub_eq_add_neg]
  congr 1
  rw [Fq204.mul_comm (Fq204.neg Fq204.one), Fq204.mul_neg, Fq204.mul_one]

/-! #### Connecting 8-Stage `nttStage` Leaves to `evalPoly204` at Roots of $X^{256} + 1$ -/

/-- Tree of evaluation roots generated by the FIPS 204 radix-2 twist `e ↦ (e/2, e/2 + 256)`. -/
def rootTree : (d : Nat) → Nat → PolyTree d
  | 0, e => .leaf (Fq204.pow mldsaZeta e)
  | d + 1, e => .branch (rootTree d (e / 2)) (rootTree d (e / 2 + 256))

/-- Map polynomial evaluation `evalPoly204 coeffs` across every root in a `PolyTree d`. -/
def evalAtTree (coeffs : List Fq204) : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf w => .leaf (evalPoly204 coeffs w)
  | _ + 1, .branch rL rR => .branch (evalAtTree coeffs rL) (evalAtTree coeffs rR)

private theorem addPolyList_append : ∀ {xs1 xs2 ys1 ys2 : List Fq204},
    xs1.length = ys1.length →
    addPolyList (xs1 ++ xs2) (ys1 ++ ys2) = addPolyList xs1 ys1 ++ addPolyList xs2 ys2
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => (Nat.succ_ne_zero _ h.symm).elim
  | _ :: _, _, [], _, h => (Nat.succ_ne_zero _ h).elim
  | _ :: xs1, xs2, _ :: ys1, ys2, h => by
    simp only [List.length_cons] at h
    simp [addPolyList, addPolyList_append (Nat.succ.inj h)]

private theorem subPolyList_append : ∀ {xs1 xs2 ys1 ys2 : List Fq204},
    xs1.length = ys1.length →
    subPolyList (xs1 ++ xs2) (ys1 ++ ys2) = subPolyList xs1 ys1 ++ subPolyList xs2 ys2
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => (Nat.succ_ne_zero _ h.symm).elim
  | _ :: _, _, [], _, h => (Nat.succ_ne_zero _ h).elim
  | _ :: xs1, xs2, _ :: ys1, ys2, h => by
    simp only [List.length_cons] at h
    simp [subPolyList, subPolyList_append (Nat.succ.inj h)]

private theorem scalePolyList_append (k : Fq204) : ∀ (xs1 xs2 : List Fq204),
    scalePolyList k (xs1 ++ xs2) = scalePolyList k xs1 ++ scalePolyList k xs2
  | [], _ => rfl
  | _ :: xs1, xs2 => by simp [scalePolyList, scalePolyList_append k xs1 xs2]

private theorem toList_addTree : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.toList (PolyTree.add a b) = addPolyList (PolyTree.toList a) (PolyTree.toList b)
  | 0, .leaf _, .leaf _ => rfl
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.add, PolyTree.toList, toList_addTree]
    exact (addPolyList_append (by rw [PolyTree.length_toList, PolyTree.length_toList])).symm

private theorem toList_subTree : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.toList (PolyTree.sub a b) = subPolyList (PolyTree.toList a) (PolyTree.toList b)
  | 0, .leaf _, .leaf _ => rfl
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.sub, PolyTree.toList, toList_subTree]
    exact (subPolyList_append (by rw [PolyTree.length_toList, PolyTree.length_toList])).symm

private theorem toList_scaleTree (k : Fq204) : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.toList (PolyTree.scale k a) = scalePolyList k (PolyTree.toList a)
  | 0, .leaf _ => rfl
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.scale, PolyTree.toList, toList_scaleTree k, scalePolyList_append]

private theorem allLeaves_imp {P Q : Fq204 → Prop} (hImp : ∀ x, P x → Q x) :
    ∀ {d : Nat} {r : PolyTree d}, PolyTree.AllLeaves P r → PolyTree.AllLeaves Q r
  | 0, .leaf _, h => hImp _ h
  | _ + 1, .branch _ _, h => ⟨allLeaves_imp hImp h.1, allLeaves_imp hImp h.2⟩

private theorem evalAtTree_congr {c1 c2 : List Fq204} {P : Fq204 → Prop}
    (hEq : ∀ w, P w → evalPoly204 c1 w = evalPoly204 c2 w) :
    ∀ {d : Nat} {r : PolyTree d}, PolyTree.AllLeaves P r → evalAtTree c1 r = evalAtTree c2 r
  | 0, .leaf w, hw => congrArg PolyTree.leaf (hEq w hw)
  | _ + 1, .branch _ _, h => by
    simp only [evalAtTree, evalAtTree_congr hEq h.1, evalAtTree_congr hEq h.2]

private theorem rootTree_allLeavesPow :
    ∀ (d e : Nat), 2 ^ d ∣ e → d ≤ 8 →
      PolyTree.AllLeaves (fun w => Fq204.pow w (2 ^ d) = Fq204.pow mldsaZeta e) (rootTree d e)
  | 0, e, _, _ => by
    dsimp only [rootTree, PolyTree.AllLeaves, Nat.pow_zero, Fq204.pow]
    rw [Fq204.one_mul]
  | d + 1, e, hdvd, hdle => by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : e = (2 ^ d * k) * 2 := by rw [hk, Nat.pow_succ, Nat.mul_right_comm]
    have heDiv : e / 2 = 2 ^ d * k := by rw [hk2]; exact Nat.mul_div_cancel _ (by decide)
    have hdvdL : 2 ^ d ∣ (e / 2) := ⟨k, heDiv⟩
    have hdvd256 : 2 ^ d ∣ 256 := by
      obtain ⟨t, ht⟩ : ∃ t, 8 = d + t := ⟨8 - d, by omega⟩
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ht, Nat.pow_add]
      exact Nat.dvd_mul_right (2 ^ d) (2 ^ t)
    have hdvdR : 2 ^ d ∣ (e / 2 + 256) := Nat.dvd_add hdvdL hdvd256
    have he2 : 2 * (e / 2) = e := by rw [heDiv, hk2, Nat.mul_comm]
    simp only [rootTree, PolyTree.AllLeaves]
    refine ⟨allLeaves_imp ?_ (rootTree_allLeavesPow d (e / 2) hdvdL (by omega)),
            allLeaves_imp ?_ (rootTree_allLeavesPow d (e / 2 + 256) hdvdR (by omega))⟩
    · intro w hw
      rw [Nat.pow_succ, Fq204.pow_mul, hw, ← Fq204.pow_mul, Nat.mul_comm _ 2, he2]
    · intro w hw
      rw [Nat.pow_succ, Fq204.pow_mul, hw, ← Fq204.pow_mul]
      have hmul : (e / 2 + 256) * 2 = e + 512 := by omega
      rw [hmul, Fq204.pow_add, mldsaZeta_pow512_eq_one, Fq204.mul_one]

private theorem nttStage_eq_evalAtTree :
    ∀ (d e : Nat), 2 ^ d ∣ e → d ≤ 8 →
      ∀ (p : PolyTree d), nttStage d e p = evalAtTree (PolyTree.toList p) (rootTree d e)
  | 0, _, _, _, .leaf x => by
    dsimp only [nttStage, rootTree, evalAtTree, PolyTree.toList, evalPoly204]
    rw [Fq204.mul_zero, Fq204.add_zero]
  | d + 1, e, hdvd, hdle, .branch lo hi => by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : e = (2 ^ d * k) * 2 := by rw [hk, Nat.pow_succ, Nat.mul_right_comm]
    have heDiv : e / 2 = 2 ^ d * k := by rw [hk2]; exact Nat.mul_div_cancel _ (by decide)
    have hdvdL : 2 ^ d ∣ (e / 2) := ⟨k, heDiv⟩
    have hdvd256 : 2 ^ d ∣ 256 := by
      obtain ⟨t, ht⟩ : ∃ t, 8 = d + t := ⟨8 - d, by omega⟩
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ht, Nat.pow_add]
      exact Nat.dvd_mul_right (2 ^ d) (2 ^ t)
    have hdvdR : 2 ^ d ∣ (e / 2 + 256) := Nat.dvd_add hdvdL hdvd256
    simp only [nttStage, rootTree, evalAtTree, PolyTree.toList,
      nttStage_eq_evalAtTree d (e / 2) hdvdL (by omega),
      nttStage_eq_evalAtTree d (e / 2 + 256) hdvdR (by omega)]
    congr 1
    · apply evalAtTree_congr _ (rootTree_allLeavesPow d (e / 2) hdvdL (by omega))
      intro w hw
      rw [toList_addTree, toList_scaleTree, evalPoly204_addPolyList, evalPoly204_scalePolyList,
          evalPoly204_append, PolyTree.length_toList, hw]
    · apply evalAtTree_congr _ (rootTree_allLeavesPow d (e / 2 + 256) hdvdR (by omega))
      intro w hw
      rw [toList_subTree, toList_scaleTree, evalPoly204_subPolyList, evalPoly204_scalePolyList,
          evalPoly204_append, PolyTree.length_toList, hw,
          Fq204.pow_add mldsaZeta (e / 2) 256, mldsaZeta_pow256_eq_neg_one,
          Fq204.sub_eq_add_neg]
      congr 1
      rw [Fq204.mul_neg (Fq204.pow mldsaZeta (e / 2)) Fq204.one, Fq204.mul_one,
          Fq204.mul_comm (Fq204.neg _) (evalPoly204 hi.toList w),
          Fq204.mul_neg (evalPoly204 hi.toList w), Fq204.mul_comm (evalPoly204 hi.toList w)]

private theorem evalAtTree_pointwiseMul {xs ys : List Fq204}
    (hx : xs.length = 256) (hy : ys.length = 256) :
    ∀ {d : Nat} {r : PolyTree d},
      PolyTree.AllLeaves (fun w => Fq204.pow w 256 = Fq204.neg Fq204.one) r →
      evalAtTree (negacyclicMulList xs ys) r =
        PolyTree.pointwiseMul (evalAtTree xs r) (evalAtTree ys r)
  | 0, .leaf _, hw => congrArg PolyTree.leaf (evalPoly204_negacyclicMulList hx hy hw)
  | _ + 1, .branch _ _, h => by
    simp only [evalAtTree, PolyTree.pointwiseMul,
      evalAtTree_pointwiseMul hx hy h.1, evalAtTree_pointwiseMul hx hy h.2]

/-- **`fips204Ntt_negacyclicMul` (NTT Convolution Homomorphism)**:
    Forward 256-point FIPS 204 NTT maps negacyclic polynomial multiplication in
    $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$ to coordinatewise multiplication in $\mathbb{Z}_q^{256}$. -/
theorem fips204Ntt_negacyclicMul (a b : Poly256) :
    fips204Ntt (negacyclicMul a b) =
      PolyTree.pointwiseMul (fips204Ntt a) (fips204Ntt b) := by
  unfold fips204Ntt negacyclicMul
  have hlenA : (PolyTree.toList a).length = 256 := PolyTree.length_toList a
  have hlenB : (PolyTree.toList b).length = 256 := PolyTree.length_toList b
  have hlenM : (negacyclicMulList (PolyTree.toList a) (PolyTree.toList b)).length = 256 :=
    length_negacyclicMulList hlenA hlenB
  rw [nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8),
      nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8),
      nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8),
      PolyTree.toList_ofList hlenM]
  have hRoots := rootTree_allLeavesPow 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8)
  rw [show (2 : Nat) ^ 8 = 256 from rfl, mldsaZeta_pow256_eq_neg_one] at hRoots
  exact evalAtTree_pointwiseMul hlenA hlenB hRoots

/-- **`fips204InvNtt_pointwiseMul`**: inverse NTT of coordinatewise product equals exact
    negacyclic polynomial multiplication in $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$. -/
theorem fips204InvNtt_pointwiseMul (a b : Poly256) :
    fips204InvNtt (PolyTree.pointwiseMul (fips204Ntt a) (fips204Ntt b)) = negacyclicMul a b := by
  rw [← fips204Ntt_negacyclicMul, fips204InvNtt_ntt]

/-! #### `LawfulCommRing Poly256` via Linearity & NTT Homomorphism -/

private theorem polyTree_scale_add (z : Fq204) : ∀ {d : Nat} (x y : PolyTree d),
    PolyTree.scale z (PolyTree.add x y) = PolyTree.add (PolyTree.scale z x) (PolyTree.scale z y)
  | 0, .leaf x, .leaf y => congrArg PolyTree.leaf (Fq204.left_distrib z x y)
  | _ + 1, .branch x0 x1, .branch y0 y1 => by
    simp only [PolyTree.add, PolyTree.scale, polyTree_scale_add z]

theorem polyTree_add_add_comm : ∀ {d : Nat} (x0 y0 x1 y1 : PolyTree d),
    PolyTree.add (PolyTree.add x0 y0) (PolyTree.add x1 y1) =
      PolyTree.add (PolyTree.add x0 x1) (PolyTree.add y0 y1)
  | 0, .leaf x0, .leaf y0, .leaf x1, .leaf y1 => congrArg PolyTree.leaf <| by
    rw [Fq204.add_assoc x0, ← Fq204.add_assoc y0, Fq204.add_comm y0 x1,
        Fq204.add_assoc x1, ← Fq204.add_assoc x0]
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1, .branch d0 d1 => by
    simp only [PolyTree.add, polyTree_add_add_comm]

private theorem polyTree_sub_add_comm : ∀ {d : Nat} (x0 y0 x1 y1 : PolyTree d),
    PolyTree.sub (PolyTree.add x0 y0) (PolyTree.add x1 y1) =
      PolyTree.add (PolyTree.sub x0 x1) (PolyTree.sub y0 y1)
  | 0, .leaf x0, .leaf y0, .leaf x1, .leaf y1 => congrArg PolyTree.leaf <| by
    rw [Fq204.sub_eq_add_neg, Fq204.sub_eq_add_neg, Fq204.sub_eq_add_neg, Fq204.neg_add,
        Fq204.add_assoc x0, ← Fq204.add_assoc y0, Fq204.add_comm y0 (Fq204.neg x1),
        Fq204.add_assoc (Fq204.neg x1), ← Fq204.add_assoc x0]
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1, .branch d0 d1 => by
    simp only [PolyTree.add, PolyTree.sub, polyTree_sub_add_comm]

private theorem nttStage_add : ∀ (d e : Nat) (a b : PolyTree d),
    nttStage d e (PolyTree.add a b) = PolyTree.add (nttStage d e a) (nttStage d e b)
  | 0, _, .leaf _, .leaf _ => rfl
  | d + 1, e, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.add, nttStage, polyTree_scale_add, polyTree_add_add_comm,
      polyTree_sub_add_comm, nttStage_add d]

theorem fips204Ntt_add (a b : Poly256) :
    fips204Ntt (PolyTree.add a b) = PolyTree.add (fips204Ntt a) (fips204Ntt b) :=
  nttStage_add 8 256 a b

private theorem evalPoly204_toList_zero :
    ∀ (d : Nat) (w : Fq204), evalPoly204 (PolyTree.toList (PolyTree.zero d)) w = Fq204.zero
  | 0, _ => by dsimp only [PolyTree.zero, PolyTree.toList, evalPoly204]; rw [Fq204.mul_zero, Fq204.add_zero]
  | d + 1, w => by
    simp only [PolyTree.zero, PolyTree.toList, evalPoly204_append, evalPoly204_toList_zero d w,
      Fq204.mul_zero, Fq204.add_zero]

private theorem evalPoly204_toList_constUnit :
    ∀ (d : Nat) (w : Fq204), evalPoly204 (PolyTree.toList (PolyTree.constUnit d)) w = Fq204.one
  | 0, _ => by dsimp only [PolyTree.constUnit, PolyTree.toList, evalPoly204]; rw [Fq204.mul_zero, Fq204.add_zero]
  | d + 1, w => by
    simp only [PolyTree.constUnit, PolyTree.toList, evalPoly204_append,
      evalPoly204_toList_constUnit d w, evalPoly204_toList_zero d w,
      Fq204.mul_zero, Fq204.add_zero]

private theorem evalAtTree_eq_ones {coeffs : List Fq204}
    (h1 : ∀ w, evalPoly204 coeffs w = Fq204.one) :
    ∀ {d : Nat} (r : PolyTree d), evalAtTree coeffs r = PolyTree.ones d
  | 0, .leaf w => congrArg PolyTree.leaf (h1 w)
  | _ + 1, .branch r0 r1 => by
    simp only [evalAtTree, PolyTree.ones, evalAtTree_eq_ones h1 r0, evalAtTree_eq_ones h1 r1]

private theorem evalAtTree_eq_zero {coeffs : List Fq204}
    (h0 : ∀ w, evalPoly204 coeffs w = Fq204.zero) :
    ∀ {d : Nat} (r : PolyTree d), evalAtTree coeffs r = PolyTree.zero d
  | 0, .leaf w => congrArg PolyTree.leaf (h0 w)
  | _ + 1, .branch r0 r1 => by
    simp only [evalAtTree, PolyTree.zero, evalAtTree_eq_zero h0 r0, evalAtTree_eq_zero h0 r1]

theorem fips204Ntt_constUnit :
    fips204Ntt (PolyTree.constUnit 8) = PolyTree.ones 8 := by
  unfold fips204Ntt
  rw [nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8)]
  exact evalAtTree_eq_ones (evalPoly204_toList_constUnit 8) _

theorem fips204Ntt_zero :
    fips204Ntt (PolyTree.zero 8) = PolyTree.zero 8 := by
  unfold fips204Ntt
  rw [nttStage_eq_evalAtTree 8 256 (Nat.dvd_refl 256) (Nat.le_refl 8)]
  exact evalAtTree_eq_zero (evalPoly204_toList_zero 8) _

theorem polyTree_add_assoc : ∀ {d : Nat} (a b c : PolyTree d),
    PolyTree.add (PolyTree.add a b) c = PolyTree.add a (PolyTree.add b c)
  | 0, .leaf a, .leaf b, .leaf c => congrArg PolyTree.leaf (Fq204.add_assoc a b c)
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1 => by
    simp only [PolyTree.add, polyTree_add_assoc a0 b0 c0, polyTree_add_assoc a1 b1 c1]

theorem polyTree_add_comm : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.add a b = PolyTree.add b a
  | 0, .leaf a, .leaf b => congrArg PolyTree.leaf (Fq204.add_comm a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.add, polyTree_add_comm a0 b0, polyTree_add_comm a1 b1]

theorem polyTree_zero_add : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.add (PolyTree.zero d) a = a
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.zero_add a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.zero, PolyTree.add, polyTree_zero_add a0, polyTree_zero_add a1]

theorem polyTree_add_zero : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.add a (PolyTree.zero d) = a
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.add_zero a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.zero, PolyTree.add, polyTree_add_zero a0, polyTree_add_zero a1]

theorem polyTree_add_left_neg : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.add (PolyTree.neg a) a = PolyTree.zero d
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.add_left_neg a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.neg, PolyTree.add, PolyTree.zero, polyTree_add_left_neg a0, polyTree_add_left_neg a1]

theorem polyTree_sub_eq_add_neg : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.sub a b = PolyTree.add a (PolyTree.neg b)
  | 0, .leaf a, .leaf b => congrArg PolyTree.leaf (Fq204.sub_eq_add_neg a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => by
    simp only [PolyTree.sub, PolyTree.add, PolyTree.neg, polyTree_sub_eq_add_neg a0 b0, polyTree_sub_eq_add_neg a1 b1]

private theorem polyTree_zero_pmul : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.pointwiseMul (PolyTree.zero d) a = PolyTree.zero d
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.zero_mul a)
  | _ + 1, .branch a0 a1 => by
    simp only [PolyTree.zero, PolyTree.pointwiseMul, polyTree_zero_pmul a0, polyTree_zero_pmul a1]

private theorem polyTree_pmul_assoc : ∀ {d : Nat} (a b c : PolyTree d),
    PolyTree.pointwiseMul (PolyTree.pointwiseMul a b) c = PolyTree.pointwiseMul a (PolyTree.pointwiseMul b c)
  | 0, .leaf a, .leaf b, .leaf c => congrArg PolyTree.leaf (Fq204.mul_assoc a b c)
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1 => by simp only [PolyTree.pointwiseMul, polyTree_pmul_assoc]

private theorem polyTree_pmul_comm : ∀ {d : Nat} (a b : PolyTree d),
    PolyTree.pointwiseMul a b = PolyTree.pointwiseMul b a
  | 0, .leaf a, .leaf b => congrArg PolyTree.leaf (Fq204.mul_comm a b)
  | _ + 1, .branch a0 a1, .branch b0 b1 => by simp only [PolyTree.pointwiseMul, polyTree_pmul_comm a0, polyTree_pmul_comm a1]

private theorem polyTree_ones_pmul : ∀ {d : Nat} (a : PolyTree d),
    PolyTree.pointwiseMul (PolyTree.ones d) a = a
  | 0, .leaf a => congrArg PolyTree.leaf (Fq204.one_mul a)
  | _ + 1, .branch a0 a1 => by simp only [PolyTree.ones, PolyTree.pointwiseMul, polyTree_ones_pmul]

private theorem polyTree_pmul_left_distrib : ∀ {d : Nat} (a b c : PolyTree d),
    PolyTree.pointwiseMul a (PolyTree.add b c) =
      PolyTree.add (PolyTree.pointwiseMul a b) (PolyTree.pointwiseMul a c)
  | 0, .leaf a, .leaf b, .leaf c => congrArg PolyTree.leaf (Fq204.left_distrib a b c)
  | _ + 1, .branch a0 a1, .branch b0 b1, .branch c0 c1 => by
    simp only [PolyTree.pointwiseMul, PolyTree.add, polyTree_pmul_left_distrib]

theorem fips204Ntt_injective {a b : Poly256} (h : fips204Ntt a = fips204Ntt b) : a = b := by
  have := congrArg fips204InvNtt h
  rwa [fips204InvNtt_ntt, fips204InvNtt_ntt] at this

theorem negacyclicMul_assoc (a b c : Poly256) :
    negacyclicMul (negacyclicMul a b) c = negacyclicMul a (negacyclicMul b c) :=
  fips204Ntt_injective <| by simp only [fips204Ntt_negacyclicMul, polyTree_pmul_assoc]

theorem negacyclicMul_comm (a b : Poly256) :
    negacyclicMul a b = negacyclicMul b a :=
  fips204Ntt_injective <| by rw [fips204Ntt_negacyclicMul, fips204Ntt_negacyclicMul, polyTree_pmul_comm]

theorem negacyclicMul_zero_left (a : Poly256) :
    negacyclicMul (PolyTree.zero 8) a = PolyTree.zero 8 :=
  fips204Ntt_injective <| by rw [fips204Ntt_negacyclicMul, fips204Ntt_zero, polyTree_zero_pmul]

theorem negacyclicMul_one_left (a : Poly256) :
    negacyclicMul (PolyTree.constUnit 8) a = a :=
  fips204Ntt_injective <| by rw [fips204Ntt_negacyclicMul, fips204Ntt_constUnit, polyTree_ones_pmul]

theorem negacyclicMul_one_right (a : Poly256) :
    negacyclicMul a (PolyTree.constUnit 8) = a := by
  rw [negacyclicMul_comm, negacyclicMul_one_left]

theorem negacyclicMul_left_distrib (a b c : Poly256) :
    negacyclicMul a (PolyTree.add b c) = PolyTree.add (negacyclicMul a b) (negacyclicMul a c) :=
  fips204Ntt_injective <| by
    rw [fips204Ntt_negacyclicMul, fips204Ntt_add, fips204Ntt_add,
        fips204Ntt_negacyclicMul, fips204Ntt_negacyclicMul, polyTree_pmul_left_distrib]

theorem negacyclicMul_right_distrib (a b c : Poly256) :
    negacyclicMul (PolyTree.add a b) c = PolyTree.add (negacyclicMul a c) (negacyclicMul b c) := by
  rw [negacyclicMul_comm, negacyclicMul_left_distrib, negacyclicMul_comm c a, negacyclicMul_comm c b]

theorem poly256_add_left_cancel {a b c : Poly256} (h : PolyTree.add a b = PolyTree.add a c) : b = c := by
  have h1 := congrArg (PolyTree.add (PolyTree.neg a)) h
  rwa [← polyTree_add_assoc, ← polyTree_add_assoc, polyTree_add_left_neg,
       polyTree_zero_add, polyTree_zero_add] at h1

instance : CommRingOps Poly256 where
  zero := PolyTree.zero 8
  one := PolyTree.constUnit 8
  add := PolyTree.add
  mul := negacyclicMul
  neg := PolyTree.neg
  sub := PolyTree.sub

instance : LawfulCommRing Poly256 where
  add_assoc := polyTree_add_assoc
  add_comm := polyTree_add_comm
  zero_add := polyTree_zero_add
  add_zero := polyTree_add_zero
  add_left_neg := polyTree_add_left_neg
  sub_eq_add_neg := polyTree_sub_eq_add_neg
  mul_assoc := negacyclicMul_assoc
  mul_comm := negacyclicMul_comm
  one_mul := negacyclicMul_one_left
  mul_one := negacyclicMul_one_right
  left_distrib := negacyclicMul_left_distrib
  right_distrib := negacyclicMul_right_distrib

namespace Fq204
abbrev val (a : Fq204) := ModZq.val a
theorem isLt (a : Fq204) : a.val < mldsaQ := ModZq.isLt a
end Fq204
end Qsag
