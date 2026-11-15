module
/-
# Qsag.CodingTheory.SylvesterElimination — Constructive Sylvester Determinant & Linear-Factor Identity

Constructive Sylvester matrix determinant `sylRes m N A B` over any `[LawfulCommRing R] [DecidableEq R]`
(`0 Classical.choice`, `0` subresultant sequences):
* `sylRes_mul_X_sub`: Master Linear-Factor Identity
  `sylRes (m' + 1) N ((X - C ζ) * Q) F = F.eval ζ * sylRes m' N Q F` over every commutative ring.
* `sylRes_eq_zero_of_common_root` & `isUnit_sylRes_of_bezout`: root vanishing and Bézout invertibility.
* `degFn_sylRes_le`: weighted `DegFn` bound `w (sylRes m N A B) ≤ m * h_B + N * h_A - m * N ≤ h_A * h_B`.
-/

public import Qsag.CodingTheory.DynamicGcdSplit
public import Qsag.CodingTheory.MatrixDet
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.MatrixDet
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

/-! ## `natRangeSum` & `rangeSum` splitting helpers -/

theorem natRangeSum_const_add :
    ∀ (n c : Nat), Mat.natRangeSum n (fun i => c + i) = n * c + Mat.natRangeSum n (fun i => i)
  | 0, c => by show 0 = 0 * c + 0; omega
  | n + 1, c => by
    show Mat.natRangeSum n (fun i => c + i) + (c + n) = (n + 1) * c + (Mat.natRangeSum n (fun i => i) + n)
    rw [natRangeSum_const_add n c, Nat.succ_mul]; omega

theorem natRangeSum_split :
    ∀ (m N : Nat) (f : Nat → Nat),
      Mat.natRangeSum (m + N) f = Mat.natRangeSum m f + Mat.natRangeSum N (fun r => f (m + r))
  | m, 0, _ => by show Mat.natRangeSum m _ = Mat.natRangeSum m _ + 0; omega
  | m, N + 1, f => by
    show Mat.natRangeSum (m + N) f + f (m + N) =
      Mat.natRangeSum m f + (Mat.natRangeSum N (fun r => f (m + r)) + f (m + N))
    rw [natRangeSum_split m N f]; omega

theorem natRangeSum_split_id (m N : Nat) :
    Mat.natRangeSum (m + N) (fun i => i) =
      Mat.natRangeSum m (fun i => i) + Mat.natRangeSum N (fun i => i) + m * N := by
  rw [natRangeSum_split m N (fun i => i), natRangeSum_const_add N m, Nat.mul_comm N m]; omega

theorem rangeSum_split {R : Type} [LawfulCommRing R] (m : Nat) :
    ∀ (N : Nat) (f : Nat → R),
      Mat.rangeSum (m + N) f = add (Mat.rangeSum m f) (Mat.rangeSum N (fun r => f (m + r)))
  | 0, f => by show Mat.rangeSum m f = add (Mat.rangeSum m f) zero; rw [LawfulCommRing.add_zero]
  | N + 1, f => by
    show add (Mat.rangeSum (m + N) f) (f (m + N)) =
      add (Mat.rangeSum m f) (add (Mat.rangeSum N (fun r => f (m + r))) (f (m + N)))
    rw [rangeSum_split m N f, LawfulCommRing.add_assoc]

/-! ## Sylvester Matrix and Resultant -/

section SylRes
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
open UPoly

private theorem C_zero : (C zero : UPoly R) = zero := by
  rw [← CHom_apply]; exact CHom.map_zero

private theorem C_add (a b : R) : C (add a b) = add (C a) (C b) := CHom.map_add a b
private theorem C_mul (a b : R) : C (mul a b) = mul (C a) (C b) := CHom.map_mul a b

/-- `(m + N) × (m + N)` Sylvester matrix of `(A, B)` with `m` shifted `B`-rows followed by
    `N` shifted `A`-rows. -/
@[expose] def sylMat (m : Nat) (_N : Nat) (A B : UPoly R) (i j : Nat) : R :=
  if i < m then
    if i ≤ j then coeffAt B.coeffs (j - i) else zero
  else
    if i - m ≤ j then coeffAt A.coeffs (j - (i - m)) else zero

/-- Constructive `(m, N)`-Sylvester resultant `det (m + N) (sylMat m N A B)`. -/
@[expose] def sylRes (m N : Nat) (A B : UPoly R) : R :=
  Mat.det (m + N) (sylMat m N A B)

theorem map_sylRes {S : Type} [LawfulCommRing S] [DecidableEq S]
    (φ : RingHom R S) (m N : Nat) (A B : UPoly R) :
    φ.toFun (sylRes m N A B) = sylRes m N ((mapHom φ).toFun A) ((mapHom φ).toFun B) := by
  unfold sylRes
  rw [Mat.map_det]
  refine Mat.det_congr (m + N) fun i _ j _ => ?_
  unfold sylMat
  if hi : i < m then
    rw [ite_pos hi, ite_pos hi]
    if hij : i ≤ j then rw [ite_pos hij, ite_pos hij, coeffAt_mapHom]
    else rw [ite_neg hij, ite_neg hij, φ.map_zero]
  else
    rw [ite_neg hi, ite_neg hi]
    if hij : i - m ≤ j then rw [ite_pos hij, ite_pos hij, coeffAt_mapHom]
    else rw [ite_neg hij, ite_neg hij, φ.map_zero]

/-- Tight row/column-weighted degree bound on `sylRes m N A B`:
    `w (sylRes m N A B) ≤ m * h_B + N * h_A - m * N`. -/
theorem degFn_sylRes_tight {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0)
    (m N h_A h_B : Nat) (A B : UPoly R)
    (hA : A.wdeg w 1 ≤ h_A) (hB : B.wdeg w 1 ≤ h_B) :
    w (sylRes m N A B) ≤ m * h_B + N * h_A - m * N := by
  if hNe : sylRes m N A B = zero then
    rw [hNe, hw.zero]; exact Nat.zero_le _
  else
    let rowWt (i : Nat) : Nat := if i < m then h_B + i else h_A + (i - m)
    let colWt (j : Nat) : Nat := j
    have hEntry : ∀ i, i < m + N → ∀ j, j < m + N → sylMat m N A B i j ≠ zero →
        w (sylMat m N A B i j) + colWt j ≤ rowWt i := by
      intro i _ j _ hnij
      dsimp only [colWt, rowWt]
      if hi : i < m then
        rw [ite_pos hi]
        unfold sylMat at hnij ⊢
        rw [ite_pos hi] at hnij ⊢
        if hij : i ≤ j then
          rw [ite_pos hij] at hnij ⊢
          have hle := le_wdeg w 1 B (j - i) hnij
          have := hB; omega
        else rw [ite_neg hij] at hnij; exact absurd rfl hnij
      else
        rw [ite_neg hi]
        unfold sylMat at hnij ⊢
        rw [ite_neg hi] at hnij ⊢
        if hij : i - m ≤ j then
          rw [ite_pos hij] at hnij ⊢
          have hle := le_wdeg w 1 A (j - (i - m)) hnij
          have := hA; omega
        else rw [ite_neg hij] at hnij; exact absurd rfl hnij
    have hDet := Mat.degFn_det_weighted_le hw hw1 (m + N) (sylMat m N A B) rowWt colWt hEntry hNe
    have hCol : Mat.natRangeSum (m + N) colWt =
        Mat.natRangeSum m (fun i => i) + Mat.natRangeSum N (fun i => i) + m * N :=
      natRangeSum_split_id m N
    have hRow1 : Mat.natRangeSum m rowWt = m * h_B + Mat.natRangeSum m (fun i => i) := by
      have hEq : ∀ k, k ≤ m → Mat.natRangeSum k rowWt = Mat.natRangeSum k (fun i => h_B + i) := by
        intro k; induction k with
        | zero => intro _; rfl
        | succ k ihk =>
          intro hk; show Mat.natRangeSum k rowWt + rowWt k = Mat.natRangeSum k _ + (h_B + k)
          rw [ihk (by omega)]; dsimp only [rowWt]; rw [ite_pos (show k < m by omega)]
      rw [hEq m (Nat.le_refl m), natRangeSum_const_add]
    have hRow2 : Mat.natRangeSum N (fun r => rowWt (m + r)) = N * h_A + Mat.natRangeSum N (fun i => i) := by
      have hEq : ∀ k, Mat.natRangeSum k (fun r => rowWt (m + r)) = Mat.natRangeSum k (fun r => h_A + r) := by
        intro k; induction k with
        | zero => rfl
        | succ k ihk =>
          show Mat.natRangeSum k _ + rowWt (m + k) = Mat.natRangeSum k _ + (h_A + k)
          rw [ihk]; dsimp only [rowWt]; rw [ite_neg (by omega), show m + k - m = k by omega]
      rw [hEq N, natRangeSum_const_add]
    have hRow := natRangeSum_split m N rowWt
    rw [hRow1, hRow2] at hRow
    show w (Mat.det (m + N) (sylMat m N A B)) ≤ _
    omega

theorem degFn_sylRes_le {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0)
    (m N h_A h_B : Nat) (A B : UPoly R)
    (hA : A.wdeg w 1 ≤ h_A) (hB : B.wdeg w 1 ≤ h_B)
    (hm : m ≤ h_A) (hN : N ≤ h_B) :
    w (sylRes m N A B) ≤ h_A * h_B := by
  have h1 := degFn_sylRes_tight hw hw1 m N h_A h_B A B hA hB
  obtain ⟨dA, rfl⟩ : ∃ dA, h_A = m + dA := ⟨h_A - m, by omega⟩
  obtain ⟨dB, rfl⟩ : ∃ dB, h_B = N + dB := ⟨h_B - N, by omega⟩
  have hExp : (m + dA) * (N + dB) = m * N + m * dB + dA * N + dA * dB := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hSub : m * (N + dB) + N * (m + dA) - m * N = m * N + m * dB + dA * N := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm N m, Nat.mul_comm N dA]; omega
  omega

/-! ## Constructive division by `X - C ζ` -/

def divXSubList (ζ : R) : List R → List R
  | [] => []
  | [_] => []
  | _ :: c₁ :: cs => evalCoeffs (c₁ :: cs) ζ :: divXSubList ζ (c₁ :: cs)

def divXSub (p : UPoly R) (ζ : R) : UPoly R :=
  ofList (divXSubList ζ p.coeffs)

omit [DecidableEq R] in
private theorem length_divXSubList (ζ : R) :
    ∀ l : List R, (divXSubList ζ l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: c₁ :: cs => by
    show (divXSubList ζ (c₁ :: cs)).length + 1 = (c₁ :: cs).length
    rw [length_divXSubList ζ (c₁ :: cs)]; rfl

private theorem divXSubList_spec (ζ : R) :
    ∀ l : List R, ofList l = add (C (evalCoeffs l ζ)) (mul (sub X (C ζ)) (ofList (divXSubList ζ l)))
  | [] => by
    show zero = add (C zero) (mul (sub X (C ζ)) zero)
    rw [C_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | [c] => by
    show ofList [c] = add (C (add c (mul ζ zero))) (mul (sub X (C ζ)) zero)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rfl
  | c₀ :: c₁ :: cs => by
    rw [ofList_cons c₀ (c₁ :: cs), divXSubList_spec ζ (c₁ :: cs)]
    show add (C c₀) (mul X (add (C (evalCoeffs (c₁ :: cs) ζ))
        (mul (sub X (C ζ)) (ofList (divXSubList ζ (c₁ :: cs)))))) =
      add (C (add c₀ (mul ζ (evalCoeffs (c₁ :: cs) ζ))))
        (mul (sub X (C ζ)) (ofList (evalCoeffs (c₁ :: cs) ζ :: divXSubList ζ (c₁ :: cs))))
    rw [ofList_cons, C_add, C_mul]; constructive_ring

theorem divXSub_spec (p : UPoly R) (ζ : R) :
    p = add (C (p.eval ζ)) (mul (sub X (C ζ)) (divXSub p ζ)) ∧
      (divXSub p ζ).natDeg ≤ p.natDeg - 1 := by
  refine ⟨?_, ?_⟩
  · have h := divXSubList_spec ζ p.coeffs
    rwa [ofList_coeffs, ← eval_eq] at h
  · unfold divXSub natDeg
    have htr := trimPoly_length_le (divXSubList ζ p.coeffs)
    have hlen := length_divXSubList ζ p.coeffs
    rw [coeffs_ofList]; omega

/-! ## Monomials & Coefficient Extraction -/

def monom : Nat → UPoly R
  | 0 => one
  | k + 1 => mul X (monom k)

theorem coeffAt_monom :
    ∀ (k j : Nat), coeffAt (monom (R := R) k).coeffs j = if j = k then one else zero
  | 0, 0 => coeffAt_C_zero one
  | 0, j + 1 => coeffAt_C_succ one j
  | k + 1, 0 => coeffAt_X_mul_zero (monom k)
  | k + 1, j + 1 => by
    rw [monom, coeffAt_X_mul_succ, coeffAt_monom k j]
    if h : j = k then rw [h, ite_pos rfl, ite_pos rfl]
    else rw [ite_neg (fun e => h (Nat.succ.inj e)), ite_neg h]

theorem coeffAt_monom_mul :
    ∀ (d : Nat) (G : UPoly R) (j : Nat),
      coeffAt (mul (monom d) G).coeffs j = if d ≤ j then coeffAt G.coeffs (j - d) else zero
  | 0, G, j => by
    show coeffAt (mul one G).coeffs j = _
    rw [LawfulCommRing.one_mul, ite_pos (Nat.zero_le j), Nat.sub_zero]
  | d + 1, G, 0 => by
    show coeffAt (mul (mul X (monom d)) G).coeffs 0 = _
    rw [LawfulCommRing.mul_assoc, coeffAt_X_mul_zero, ite_neg (Nat.not_succ_le_zero d)]
  | d + 1, G, j + 1 => by
    show coeffAt (mul (mul X (monom d)) G).coeffs (j + 1) = _
    rw [LawfulCommRing.mul_assoc, coeffAt_X_mul_succ, coeffAt_monom_mul d G j]
    if h : d ≤ j then rw [ite_pos h, ite_pos (Nat.succ_le_succ h), Nat.succ_sub_succ]
    else rw [ite_neg h, ite_neg (fun hs => h (Nat.le_of_succ_le_succ hs))]

/-! ## Master Linear-Factor Identity `sylRes_mul_X_sub` -/

private theorem coeffAt_sub_X_C_mul (ζ : R) (G : UPoly R) :
    (coeffAt (mul (sub X (C ζ)) G).coeffs 0 = neg (mul ζ (coeffAt G.coeffs 0))) ∧
      ∀ s : Nat, coeffAt (mul (sub X (C ζ)) G).coeffs (s + 1) =
        sub (coeffAt G.coeffs s) (mul ζ (coeffAt G.coeffs (s + 1))) := by
  have hExpand : mul (sub X (C ζ)) G = sub (mul X G) (mul (C ζ) G) := by constructive_ring
  refine ⟨?_, fun s => ?_⟩
  · rw [hExpand, coeffAt_sub, coeffAt_X_mul_zero, coeffAt_C_mul]; constructive_ring
  · rw [hExpand, coeffAt_sub, coeffAt_X_mul_succ, coeffAt_C_mul]

omit [DecidableEq R] in
private theorem rangeSum_eval_eq (ζ : R) :
    ∀ (l : List R) (K : Nat),
      l.length ≤ K → Mat.rangeSum K (fun j => mul (coeffAt l j) (CRing.npow ζ j)) = evalCoeffs l ζ
  | [], K, _ => Mat.rangeSum_eq_zero fun j _ => by rw [coeffAt_nil, LawfulCommRing.zero_mul]
  | _ :: _, 0, h => by simp only [List.length_cons] at h; exfalso; omega
  | c :: cs, K + 1, h => by
    have hShift : ∀ m, Mat.rangeSum (m + 1) (fun j => mul (coeffAt (c :: cs) j) (CRing.npow ζ j)) =
        add c (mul ζ (Mat.rangeSum m (fun j => mul (coeffAt cs j) (CRing.npow ζ j)))) := by
      intro m; induction m with
      | zero =>
        show add zero (mul c one) = add c (mul ζ zero)
        rw [LawfulCommRing.zero_add, LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      | succ m ihm =>
        show add (Mat.rangeSum (m + 1) _) (mul (coeffAt cs m) (mul (CRing.npow ζ m) ζ)) =
          add c (mul ζ (add (Mat.rangeSum m _) (mul (coeffAt cs m) (CRing.npow ζ m))))
        rw [ihm]; constructive_ring
    rw [hShift K, rangeSum_eval_eq ζ cs K (by simp only [List.length_cons] at h; omega)]; rfl

private theorem telescope_col0 (ζ : R) (G : UPoly R) :
    ∀ s : Nat,
      Mat.rangeSum (s + 1) (fun j => mul (coeffAt (mul (sub X (C ζ)) G).coeffs j) (CRing.npow ζ j)) =
        neg (mul (coeffAt G.coeffs s) (CRing.npow ζ (s + 1)))
  | 0 => by
    show add zero (mul (coeffAt (mul (sub X (C ζ)) G).coeffs 0) one) = neg (mul (coeffAt G.coeffs 0) (mul one ζ))
    rw [(coeffAt_sub_X_C_mul ζ G).1]; constructive_ring
  | s + 1 => by
    show add (Mat.rangeSum (s + 1) _)
        (mul (coeffAt (mul (sub X (C ζ)) G).coeffs (s + 1)) (CRing.npow ζ (s + 1))) =
      neg (mul (coeffAt G.coeffs (s + 1)) (mul (CRing.npow ζ (s + 1)) ζ))
    rw [telescope_col0 ζ G s, (coeffAt_sub_X_C_mul ζ G).2 s]; constructive_ring

private theorem telescope_col_succ (ζ : R) (G : UPoly R) (c : Nat) :
    ∀ d : Nat,
      Mat.rangeSum (c + 1 + (d + 1))
        (fun j => mul (coeffAt (mul (sub X (C ζ)) G).coeffs j)
          (if c + 1 ≤ j then CRing.npow ζ (j - (c + 1)) else zero)) =
        sub (coeffAt G.coeffs c) (mul (coeffAt G.coeffs (c + 1 + d)) (CRing.npow ζ (d + 1)))
  | 0 => by
    have hz : Mat.rangeSum (c + 1)
        (fun j => mul (coeffAt (mul (sub X (C ζ)) G).coeffs j)
          (if c + 1 ≤ j then CRing.npow ζ (j - (c + 1)) else zero)) = zero :=
      Mat.rangeSum_eq_zero fun j hj => by rw [ite_neg (by omega), LawfulCommRing.mul_zero]
    show add (Mat.rangeSum (c + 1) _) _ = sub (coeffAt G.coeffs c) (mul (coeffAt G.coeffs (c + 1 + 0)) (mul one ζ))
    rw [hz, LawfulCommRing.zero_add]
    dsimp only
    rw [ite_pos (Nat.le_refl (c + 1)), Nat.sub_self, (coeffAt_sub_X_C_mul ζ G).2 c]
    show mul _ one = _; constructive_ring
  | d + 1 => by
    show add (Mat.rangeSum (c + 1 + (d + 1)) _)
        (mul (coeffAt (mul (sub X (C ζ)) G).coeffs (c + 1 + (d + 1)))
          (if c + 1 ≤ c + 1 + (d + 1) then CRing.npow ζ (c + 1 + (d + 1) - (c + 1)) else zero)) =
      sub (coeffAt G.coeffs c) (mul (coeffAt G.coeffs (c + 1 + (d + 1))) (mul (CRing.npow ζ (d + 1)) ζ))
    rw [telescope_col_succ ζ G c d, ite_pos (by omega), show c + 1 + (d + 1) - (c + 1) = d + 1 by omega,
      show c + 1 + (d + 1) = (c + 1 + d) + 1 by omega, (coeffAt_sub_X_C_mul ζ G).2 (c + 1 + d)]
    constructive_ring

/-- **Master Linear-Factor Identity**: over any `[LawfulCommRing R] [DecidableEq R]`, if
    `Q.natDeg ≤ m'` and `F.natDeg ≤ N`, then
    `sylRes (m' + 1) N ((X - C ζ) * Q) F = F.eval ζ * sylRes m' N Q F`. -/
theorem sylRes_mul_X_sub (m' N : Nat) (ζ : R) (Q F : UPoly R)
    (hQ : Q.natDeg ≤ m') (hF : F.natDeg ≤ N) :
    sylRes (m' + 1) N (mul (sub X (C ζ)) Q) F = mul (F.eval ζ) (sylRes m' N Q F) := by
  let K := m' + 1 + N
  let A := mul (sub X (C ζ)) Q
  let Lmat (i l : Nat) : R :=
    if i = l then one
    else if 1 ≤ i ∧ i ≤ m' ∧ l + 1 = i then neg ζ
    else zero
  let Pmat (j c : Nat) : R := if c ≤ j then CRing.npow ζ (j - c) else zero
  have hDetL : Mat.det K Lmat = one :=
    Mat.det_lower_tri_one K Lmat
      (fun i l hil _ => by
        dsimp only [Lmat]; rw [ite_neg (Nat.ne_of_lt hil), ite_neg (by omega)])
      (fun i _ => by dsimp only [Lmat]; rw [ite_pos rfl])
  have hDetP : Mat.det K Pmat = one :=
    Mat.det_lower_tri_one K Pmat
      (fun j c hjc _ => by dsimp only [Pmat]; rw [ite_neg (by omega)])
      (fun j _ => by dsimp only [Pmat]; rw [ite_pos (Nat.le_refl j), Nat.sub_self]; rfl)
  let M1 := Mat.matMul K Lmat (sylMat (m' + 1) N A F)
  let M2 := Mat.matMul K M1 Pmat
  have hM1_row0 : ∀ j, j < K → M1 0 j = coeffAt F.coeffs j := by
    intro j hj
    dsimp only [M1]; unfold Mat.matMul
    rw [Mat.rangeSum_single (Nat.zero_lt_of_lt hj) _ fun l _ hne => by
      dsimp only [Lmat]; rw [ite_neg (Ne.symm hne), ite_neg (by omega), LawfulCommRing.zero_mul]]
    dsimp only [Lmat]; rw [ite_pos rfl, LawfulCommRing.one_mul]
    unfold sylMat; rw [ite_pos (Nat.zero_lt_succ m'), ite_pos (Nat.zero_le j), Nat.sub_zero]
  let rowPoly (i' : Nat) : UPoly R :=
    if i' < m' then mul (monom i') F else mul (monom (i' - m')) Q
  have hRowPoly_top : ∀ i', i' < m' + N → coeffAt (rowPoly i').coeffs (m' + N) = zero := by
    intro i' hi'
    dsimp only [rowPoly]
    if hlt : i' < m' then
      rw [ite_pos hlt, coeffAt_monom_mul, ite_pos (by omega)]
      exact F.coeffAt_eq_zero_of_natDeg_lt (by omega)
    else
      rw [ite_neg hlt, coeffAt_monom_mul, ite_pos (by omega)]
      exact Q.coeffAt_eq_zero_of_natDeg_lt (by omega)
  have hM1_succ : ∀ i', i' < m' + N → ∀ j, j < K →
      M1 (i' + 1) j = coeffAt (mul (sub X (C ζ)) (rowPoly i')).coeffs j := by
    intro i' hi' j hj
    dsimp only [M1]; unfold Mat.matMul
    if hlt : i' < m' then
      have hTwo : Mat.rangeSum K (fun l => mul (Lmat (i' + 1) l) (sylMat (m' + 1) N A F l j)) =
          add (mul (neg ζ) (sylMat (m' + 1) N A F i' j)) (sylMat (m' + 1) N A F (i' + 1) j) := by
        let f0 (l : Nat) : R := if l = i' then mul (neg ζ) (sylMat (m' + 1) N A F i' j) else zero
        let f1 (l : Nat) : R := if l = i' + 1 then sylMat (m' + 1) N A F (i' + 1) j else zero
        have hSplit : Mat.rangeSum K (fun l => mul (Lmat (i' + 1) l) (sylMat (m' + 1) N A F l j)) =
            Mat.rangeSum K (fun l => add (f0 l) (f1 l)) :=
          Mat.rangeSum_congr fun l _ => by
            dsimp only [Lmat, f0, f1]
            if h1 : l = i' + 1 then
              subst h1; rw [ite_pos rfl, ite_neg (by omega), ite_pos rfl, LawfulCommRing.zero_add, LawfulCommRing.one_mul]
            else if h0 : l = i' then
              subst h0; rw [ite_neg (by omega), ite_pos ⟨by omega, by omega, rfl⟩, ite_pos rfl, ite_neg (by omega), LawfulCommRing.add_zero]
            else
              rw [ite_neg (Ne.symm h1), ite_neg (by omega), ite_neg h0, ite_neg h1, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
        rw [hSplit, Mat.rangeSum_add,
          Mat.rangeSum_single (j₀ := i') (by omega) f0 (fun l _ hne => by dsimp only [f0]; rw [ite_neg hne]),
          Mat.rangeSum_single (j₀ := i' + 1) (by omega) f1 (fun l _ hne => by dsimp only [f1]; rw [ite_neg hne])]
        dsimp only [f0, f1]; rw [ite_pos rfl, ite_pos rfl]
      rw [hTwo]; dsimp only [rowPoly]; rw [ite_pos hlt]
      unfold sylMat
      rw [ite_pos (Nat.lt_succ_of_lt hlt), ite_pos (Nat.succ_lt_succ hlt)]
      cases j with
      | zero =>
        rw [(coeffAt_sub_X_C_mul ζ _).1, coeffAt_monom_mul]
        if hi0 : i' = 0 then
          subst hi0
          rw [ite_pos (Nat.le_refl 0), ite_neg (Nat.not_succ_le_zero 0)]
          constructive_ring
        else
          rw [ite_neg (show ¬ (i' ≤ 0) by omega), ite_neg (show ¬ (i' + 1 ≤ 0) by omega)]
          constructive_ring
      | succ s =>
        rw [(coeffAt_sub_X_C_mul ζ _).2 s, coeffAt_monom_mul, coeffAt_monom_mul]
        if h1 : i' ≤ s then
          rw [ite_pos (show i' ≤ s + 1 by omega), ite_pos (Nat.succ_le_succ h1), ite_pos h1,
            Nat.succ_sub_succ]; constructive_ring
        else if h2 : i' = s + 1 then
          subst h2
          rw [ite_pos (Nat.le_refl (s + 1)), ite_neg (show ¬ (s + 1 + 1 ≤ s + 1) by omega),
            ite_neg (show ¬ (s + 1 ≤ s) by omega)]; constructive_ring
        else
          rw [ite_neg (show ¬ (i' ≤ s + 1) by omega), ite_neg (show ¬ (i' + 1 ≤ s + 1) by omega),
            ite_neg h1]; constructive_ring
    else
      rw [Mat.rangeSum_single (j₀ := i' + 1) (by omega) _ fun l _ hne => by
        dsimp only [Lmat]; rw [ite_neg (Ne.symm hne), ite_neg (by omega), LawfulCommRing.zero_mul]]
      dsimp only [Lmat, rowPoly]; rw [ite_pos rfl, LawfulCommRing.one_mul, ite_neg hlt]
      unfold sylMat
      rw [ite_neg (by omega), show i' + 1 - (m' + 1) = i' - m' by omega]
      have hComm : mul (sub X (C ζ)) (mul (monom (i' - m')) Q) = mul (monom (i' - m')) A := by
        dsimp only [A]; constructive_ring
      rw [hComm, coeffAt_monom_mul]
  have hM2_00 : M2 0 0 = F.eval ζ := by
    dsimp only [M2]; unfold Mat.matMul
    have hCongr : Mat.rangeSum K (fun j => mul (M1 0 j) (Pmat j 0)) =
        Mat.rangeSum K (fun j => mul (coeffAt F.coeffs j) (CRing.npow ζ j)) :=
      Mat.rangeSum_congr fun j hj => by
        rw [hM1_row0 j hj]; dsimp only [Pmat]; rw [ite_pos (Nat.zero_le j), Nat.sub_zero]
    have hLen : F.coeffs.length ≤ K := by unfold natDeg at hF; dsimp only [K]; omega
    rw [hCongr, rangeSum_eval_eq ζ F.coeffs K hLen, eval_eq]
  have hM2_col0 : ∀ i', i' < m' + N → M2 (i' + 1) 0 = zero := by
    intro i' hi'
    dsimp only [M2]; unfold Mat.matMul
    have hCongr : Mat.rangeSum K (fun j => mul (M1 (i' + 1) j) (Pmat j 0)) =
        Mat.rangeSum ((m' + N) + 1)
          (fun j => mul (coeffAt (mul (sub X (C ζ)) (rowPoly i')).coeffs j) (CRing.npow ζ j)) := by
      have hKEq : K = (m' + N) + 1 := by dsimp only [K]; omega
      rw [hKEq]
      refine Mat.rangeSum_congr fun j hj => ?_
      rw [hM1_succ i' hi' j (by dsimp only [K]; omega)]
      dsimp only [Pmat]; rw [ite_pos (Nat.zero_le j), Nat.sub_zero]
    rw [hCongr, telescope_col0, hRowPoly_top i' hi', LawfulCommRing.zero_mul, LawfulCommRing.neg_zero]
  have hM2_minor : ∀ i', i' < m' + N → ∀ c, c < m' + N →
      Mat.minor M2 0 0 i' c = sylMat m' N Q F i' c := by
    intro i' hi' c hc
    show M2 (i' + 1) (c + 1) = _
    dsimp only [M2]; unfold Mat.matMul
    have hKEq : K = c + 1 + ((m' + N - c - 1) + 1) := by dsimp only [K]; omega
    have hCongr : Mat.rangeSum K (fun j => mul (M1 (i' + 1) j) (Pmat j (c + 1))) =
        Mat.rangeSum (c + 1 + ((m' + N - c - 1) + 1))
          (fun j => mul (coeffAt (mul (sub X (C ζ)) (rowPoly i')).coeffs j)
            (if c + 1 ≤ j then CRing.npow ζ (j - (c + 1)) else zero)) := by
      rw [hKEq]
      refine Mat.rangeSum_congr fun j hj => ?_
      rw [hM1_succ i' hi' j (by dsimp only [K]; omega)]
    rw [hCongr, telescope_col_succ, show c + 1 + (m' + N - c - 1) = m' + N by omega,
      hRowPoly_top i' hi', LawfulCommRing.zero_mul, LawfulCommRing.sub_zero]
    dsimp only [rowPoly]; unfold sylMat
    if hlt : i' < m' then rw [ite_pos hlt, ite_pos hlt, coeffAt_monom_mul]
    else rw [ite_neg hlt, ite_neg hlt, coeffAt_monom_mul]
  have hDetM2 : Mat.det K M2 = sylRes (m' + 1) N A F := by
    dsimp only [M2, M1]
    rw [Mat.det_matMul, Mat.det_matMul, hDetL, hDetP, LawfulCommRing.one_mul, LawfulCommRing.mul_one]
    rfl
  have hKEq : K = (m' + N) + 1 := by dsimp only [K]; omega
  rw [← hDetM2, hKEq, Mat.det_col0_unit (m' + N) M2 hM2_col0, hM2_00,
    Mat.det_congr (m' + N) hM2_minor]
  rfl

/-- Common root `ζ` of `(A, B)` forces `sylRes m N A B = 0` (`1 ≤ m`). -/
theorem sylRes_eq_zero_of_common_root {m N : Nat} {A B : UPoly R} {ζ : R}
    (hm : 1 ≤ m) (hA : A.natDeg ≤ m) (hB : B.natDeg ≤ N)
    (hAz : A.eval ζ = zero) (hBz : B.eval ζ = zero) :
    sylRes m N A B = zero := by
  obtain ⟨hDiv, hDeg⟩ := divXSub_spec A ζ
  rw [hAz, C_zero, LawfulCommRing.zero_add] at hDiv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [hDiv, sylRes_mul_X_sub m' N ζ (divXSub A ζ) B (by omega) hB, hBz, LawfulCommRing.zero_mul]

/-! ## Unit-Leading Division `divModLead` & Bézout Invertibility `isUnit_sylRes_of_bezout` -/

def divModLeadAux (A : UPoly R) (m : Nat) (c_inv : R) : Nat → UPoly R → UPoly R × UPoly R
  | 0, P => (zero, P)
  | fuel + 1, P =>
    if P.natDeg < m then (zero, P)
    else
      let qTop := mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))
      let P' := sub P (mul qTop A)
      let qr := divModLeadAux A m c_inv fuel P'
      (add qTop qr.1, qr.2)

/-- Polynomial division by `A` (`1 ≤ m`, `A.natDeg ≤ m`) with invertible `m`-th coefficient. -/
def divModLead (A : UPoly R) (m : Nat) (c_inv : R) (P : UPoly R) : UPoly R × UPoly R :=
  divModLeadAux A m c_inv (P.natDeg + 1) P

theorem divModLead_spec (A : UPoly R) (m : Nat) (c_inv : R)
    (hm : 1 ≤ m) (hA : A.natDeg ≤ m) (hInv : mul c_inv (coeffAt A.coeffs m) = one) (P : UPoly R) :
    P = add (mul (divModLead A m c_inv P).1 A) (divModLead A m c_inv P).2 ∧
      (divModLead A m c_inv P).2.natDeg < m := by
  have aux : ∀ (fuel : Nat) (P : UPoly R), P.natDeg < fuel →
      P = add (mul (divModLeadAux A m c_inv fuel P).1 A) (divModLeadAux A m c_inv fuel P).2 ∧
        (divModLeadAux A m c_inv fuel P).2.natDeg < m := by
    intro fuel; induction fuel with
    | zero => intros _ h; exfalso; omega
    | succ fuel ih =>
      intro P hFuel
      unfold divModLeadAux
      if hlt : P.natDeg < m then
        rw [ite_pos hlt]
        exact ⟨by show P = add (mul zero A) P; constructive_ring, hlt⟩
      else
        rw [ite_neg hlt]
        let qTop := mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))
        let P' := sub P (mul qTop A)
        have hCancel : ∀ k, P.natDeg ≤ k → coeffAt P'.coeffs k = zero := by
          intro k hk
          dsimp only [P', qTop]
          have hqA : mul (mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))) A =
              mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (mul (monom (P.natDeg - m)) A) := by
            constructive_ring
          rw [coeffAt_sub, hqA, coeffAt_C_mul, coeffAt_monom_mul, ite_pos (by omega)]
          if hEq : k = P.natDeg then
            subst hEq
            rw [show P.natDeg - (P.natDeg - m) = m by omega]
            have h1 : mul (mul (coeffAt P.coeffs P.natDeg) c_inv) (coeffAt A.coeffs m) =
                mul (coeffAt P.coeffs P.natDeg) (mul c_inv (coeffAt A.coeffs m)) := by constructive_ring
            rw [h1, hInv, LawfulCommRing.mul_one, LawfulCommRing.sub_self]
          else
            rw [P.coeffAt_eq_zero_of_natDeg_lt (by omega),
              A.coeffAt_eq_zero_of_natDeg_lt (by omega), LawfulCommRing.mul_zero, LawfulCommRing.sub_self]
        have hDegP' : P'.natDeg < fuel := by
          have hle : P'.natDeg ≤ P.natDeg - 1 :=
            natDeg_le_of_coeffAt P' (P.natDeg - 1) fun k hk => hCancel k (by omega)
          omega
        obtain ⟨hEq', hRem⟩ := ih P' hDegP'
        refine ⟨?_, hRem⟩
        show P = add (mul (add qTop (divModLeadAux A m c_inv fuel P').1) A)
          (divModLeadAux A m c_inv fuel P').2
        have hP : P = add (mul qTop A) P' := by dsimp only [P']; constructive_ring
        conv => lhs; rw [hP, hEq']
        constructive_ring
  exact aux (P.natDeg + 1) P (Nat.lt_succ_self _)

private def polyOfRange : Nat → (Nat → R) → UPoly R
  | 0, _ => zero
  | n + 1, f => add (polyOfRange n f) (mul (C (f n)) (monom n))

private theorem coeffAt_polyOfRange :
    ∀ (n : Nat) (f : Nat → R) (i : Nat),
      coeffAt (polyOfRange n f).coeffs i = if i < n then f i else zero
  | 0, _, i => by show coeffAt (zero : UPoly R).coeffs i = zero; rw [coeffs_zero, coeffAt_nil]
  | n + 1, f, i => by
    show coeffAt (add (polyOfRange n f) (mul (C (f n)) (monom n))).coeffs i = _
    rw [coeffAt_add, coeffAt_polyOfRange n f i, coeffAt_C_mul, coeffAt_monom]
    if hEq : i = n then
      subst hEq; rw [ite_neg (Nat.lt_irrefl i), ite_pos rfl, ite_pos (Nat.lt_succ_self i)]; constructive_ring
    else if hLt : i < n then
      rw [ite_pos hLt, ite_neg hEq, ite_pos (Nat.lt_succ_of_lt hLt)]; constructive_ring
    else
      rw [ite_neg hLt, ite_neg hEq, ite_neg (by omega)]; constructive_ring

private theorem coeffAt_mul_polyOfRange (B : UPoly R) :
    ∀ (n : Nat) (f : Nat → R) (j : Nat),
      coeffAt (mul (polyOfRange n f) B).coeffs j =
        Mat.rangeSum n (fun i => mul (f i) (if i ≤ j then coeffAt B.coeffs (j - i) else zero))
  | 0, _, _ => by show coeffAt (mul zero B).coeffs _ = zero; rw [LawfulCommRing.zero_mul, coeffs_zero, coeffAt_nil]
  | n + 1, f, j => by
    show coeffAt (mul (add (polyOfRange n f) (mul (C (f n)) (monom n))) B).coeffs j = add _ _
    have hDist : mul (add (polyOfRange n f) (mul (C (f n)) (monom n))) B =
        add (mul (polyOfRange n f) B) (mul (C (f n)) (mul (monom n) B)) := by constructive_ring
    rw [hDist, coeffAt_add, coeffAt_mul_polyOfRange B n f j, coeffAt_C_mul, coeffAt_monom_mul]

private theorem bezout_step (mK U0 A V0 B q r : UPoly R)
    (h1 : mul mK (add (mul U0 A) (mul V0 B)) = mK)
    (h2 : mul mK V0 = add (mul q A) r) :
    add (mul (add (mul mK U0) (mul q B)) A) (mul r B) = mK := by
  have hRhs : mK = add (mul (mul mK U0) A) (mul (add (mul q A) r) B) := by
    conv => lhs; rw [← h1]
    rw [LawfulCommRing.left_distrib, ← LawfulCommRing.mul_assoc mK V0 B, h2]
    constructive_ring
  conv => rhs; rw [hRhs]
  constructive_ring

/-- **Bézout Invertibility**: if `A.natDeg ≤ m`, `coeffAt A.coeffs m` is a unit, `B.natDeg ≤ N`,
    and `U0 * A + V0 * B = 1`, then `sylRes m N A B` is a unit in `R`! -/
theorem isUnit_sylRes_of_bezout {m N : Nat} {A B U0 V0 : UPoly R} {c_inv : R}
    (hA : A.natDeg ≤ m) (hInv : mul c_inv (coeffAt A.coeffs m) = one)
    (hB : B.natDeg ≤ N) (hBez : add (mul U0 A) (mul V0 B) = one) :
    ∃ r_inv : R, mul r_inv (sylRes m N A B) = one := by
  if hm0 : m = 0 then
    subst hm0
    have hDiag : sylRes 0 N A B = CRing.npow (coeffAt A.coeffs 0) N := by
      unfold sylRes; rw [Nat.zero_add]
      refine Mat.det_lower_tri_const (coeffAt A.coeffs 0) N (sylMat 0 N A B) (fun i j hij _ => ?_) (fun i _ => ?_)
      · unfold sylMat; rw [ite_neg (Nat.not_lt_zero i), Nat.sub_zero, ite_pos (Nat.le_of_lt hij)]
        exact A.coeffAt_eq_zero_of_natDeg_lt (by omega)
      · unfold sylMat; rw [ite_neg (Nat.not_lt_zero i), Nat.sub_zero, ite_pos (Nat.le_refl i), Nat.sub_self]
    have hPowInv : ∀ n : Nat, mul (CRing.npow c_inv n) (CRing.npow (coeffAt A.coeffs 0) n) = one := by
      intro n; induction n with
      | zero => exact LawfulCommRing.one_mul one
      | succ n ihn =>
        show mul (mul (CRing.npow c_inv n) c_inv) (mul (CRing.npow (coeffAt A.coeffs 0) n) (coeffAt A.coeffs 0)) = one
        have hAssoc : mul (mul (CRing.npow c_inv n) c_inv) (mul (CRing.npow (coeffAt A.coeffs 0) n) (coeffAt A.coeffs 0)) =
            mul (mul (CRing.npow c_inv n) (CRing.npow (coeffAt A.coeffs 0) n)) (mul c_inv (coeffAt A.coeffs 0)) := by
          constructive_ring
        rw [hAssoc, ihn, hInv, LawfulCommRing.mul_one]
    exact ⟨CRing.npow c_inv N, by rw [hDiag]; exact hPowInv N⟩
  else
    have hm : 1 ≤ m := by omega
    let qr (k : Nat) := divModLead A m c_inv (mul (monom k) V0)
    let Vk (k : Nat) : UPoly R := (qr k).2
    let Uk (k : Nat) : UPoly R := add (mul (monom k) U0) (mul (qr k).1 B)
    have hUkVk : ∀ k, add (mul (Uk k) A) (mul (Vk k) B) = monom k := fun k =>
      bezout_step (monom k) U0 A V0 B (qr k).1 (qr k).2
        (by rw [hBez, LawfulCommRing.mul_one])
        (divModLead_spec A m c_inv hm hA hInv (mul (monom k) V0)).1
    have hVk_high : ∀ k i, m ≤ i → coeffAt (Vk k).coeffs i = zero := fun k i hi =>
      (Vk k).coeffAt_eq_zero_of_natDeg_lt
        (Nat.lt_of_lt_of_le (divModLead_spec A m c_inv hm hA hInv _).2 hi)
    have hUk_high : ∀ k, k < m + N → ∀ r, N ≤ r → coeffAt (Uk k).coeffs r = zero := by
      intro k hk r hr
      have hProdHigh : ∀ t, m + N ≤ t → coeffAt (mul (Uk k) A).coeffs t = zero := by
        intro t ht
        have hEq : mul (Uk k) A = sub (monom k) (mul (Vk k) B) := by
          rw [← hUkVk k]; constructive_ring
        have hVB_deg : (mul (Vk k) B).natDeg < m + N := by
          have h1 := natDeg_mul_le (Vk k) B
          have h2 : (Vk k).natDeg < m := (divModLead_spec A m c_inv hm hA hInv (mul (monom k) V0)).2
          have := hB; omega
        rw [hEq, coeffAt_sub, coeffAt_monom, ite_neg (by omega),
          (mul (Vk k) B).coeffAt_eq_zero_of_natDeg_lt (by omega), LawfulCommRing.sub_self]
      if hU0 : Uk k = zero then
        rw [hU0, coeffs_zero, coeffAt_nil]
      else
        if hLt : (Uk k).natDeg < N then
          exact (Uk k).coeffAt_eq_zero_of_natDeg_lt (by omega)
        else
          exfalso
          let u := (Uk k).natDeg
          have hTop0 : coeffAt (mul (Uk k) A).coeffs (u + m) = zero := hProdHigh (u + m) (by omega)
          have hAm : A.natDeg = m := by
            apply Nat.le_antisymm hA
            apply Decidable.byContradiction; intro hNot
            have hz := A.coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hNot)
            rw [hz, LawfulCommRing.mul_zero] at hInv
            have hLeadZero : (Uk k).lead = zero := by
              have hMul := congrArg (mul (Uk k).lead) hInv
              rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one] at hMul
              exact hMul.symm
            exact lead_ne_zero hU0 hLeadZero
          have hTopEq := (coeffAt_mul_top (Uk k) A).2
          unfold lead at hTopEq
          rw [hAm] at hTopEq
          rw [hTopEq] at hTop0
          have hLead0 : coeffAt (Uk k).coeffs u = zero := by
            have h1 : coeffAt (Uk k).coeffs u = mul (coeffAt (Uk k).coeffs u) (mul c_inv (coeffAt A.coeffs m)) := by
              rw [hInv, LawfulCommRing.mul_one]
            have h2 : mul (coeffAt (Uk k).coeffs u) (mul c_inv (coeffAt A.coeffs m)) =
                mul c_inv (mul (coeffAt (Uk k).coeffs u) (coeffAt A.coeffs m)) := by constructive_ring
            rw [h1, h2, hTop0, LawfulCommRing.mul_zero]
          exact lead_ne_zero hU0 hLead0
    let W (k l : Nat) : R :=
      if l < m then coeffAt (Vk k).coeffs l else coeffAt (Uk k).coeffs (l - m)
    have hMulId : Mat.det (m + N) (Mat.matMul (m + N) W (sylMat m N A B)) = one := by
      rw [Mat.det_congr (m + N) (N := Mat.idMat) fun k hk j _ => ?_, Mat.det_idMat]
      unfold Mat.matMul
      rw [rangeSum_split m N]
      have hLeft : Mat.rangeSum m (fun l => mul (W k l) (sylMat m N A B l j)) =
          coeffAt (mul (Vk k) B).coeffs j := by
        have hVpoly : Vk k = polyOfRange m (fun l => coeffAt (Vk k).coeffs l) := by
          apply ext_coeffAt; intro i
          rw [coeffAt_polyOfRange]
          if hi : i < m then rw [ite_pos hi] else rw [ite_neg hi, hVk_high k i (by omega)]
        conv => rhs; rw [hVpoly, coeffAt_mul_polyOfRange]
        refine Mat.rangeSum_congr fun l hl => ?_
        dsimp only [W]; unfold sylMat; rw [ite_pos hl, ite_pos hl]
      have hRight : Mat.rangeSum N (fun r => mul (W k (m + r)) (sylMat m N A B (m + r) j)) =
          coeffAt (mul (Uk k) A).coeffs j := by
        have hUpoly : Uk k = polyOfRange N (fun r => coeffAt (Uk k).coeffs r) := by
          apply ext_coeffAt; intro r
          rw [coeffAt_polyOfRange]
          if hr : r < N then rw [ite_pos hr] else rw [ite_neg hr, hUk_high k hk r (by omega)]
        conv => rhs; rw [hUpoly, coeffAt_mul_polyOfRange]
        refine Mat.rangeSum_congr fun r _ => ?_
        dsimp only [W]; unfold sylMat
        rw [ite_neg (by omega), ite_neg (by omega), show m + r - m = r by omega]
      rw [hLeft, hRight, LawfulCommRing.add_comm, ← coeffAt_add, hUkVk k, coeffAt_monom]
      unfold Mat.idMat
      if hkj : k = j then subst hkj; rw [ite_pos rfl]
      else rw [ite_neg (Ne.symm hkj), ite_neg hkj]
    rw [Mat.det_matMul] at hMulId
    exact ⟨Mat.det (m + N) W, hMulId⟩

end SylRes
end SylElim

namespace SylvesterEliminationTests
open UPoly SylElim

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `(X - 3)(X - 5)` and `F = X + 2`, `ζ = 3`:
    `sylRes 2 1 ((X - 3)(X - 5)) (X + 2) = F(3) * sylRes 1 1 (X - 5) (X + 2) = 5 * 7 = 35`. -/
theorem inhabited_sylRes_mul_X_sub :
    ∃ (m' N : Nat) (ζ : Goldilocks) (Q F : UPoly Goldilocks),
      Q.natDeg ≤ m' ∧ F.natDeg ≤ N ∧
      sylRes (m' + 1) N (mul (sub X (C ζ)) Q) F = g 35 :=
  ⟨1, 1, g 3, ofList [neg (g 5), g 1], ofList [g 2, g 1],
    by decide +kernel, by decide +kernel, by
      rw [sylRes_mul_X_sub 1 1 (g 3) _ _ (by decide +kernel) (by decide +kernel)]
      decide +kernel⟩

/-- `#tooth`: dropping `B.eval ζ = 0` invalidates `sylRes_eq_zero_of_common_root`
    (`A = X - 3`, `B = X - 5`, `ζ = 3` gives `sylRes 1 1 A B = -2 ≠ 0`). -/
theorem tooth_sylRes_needs_both_roots :
    ∃ (m N : Nat) (A B : UPoly Goldilocks) (ζ : Goldilocks),
      1 ≤ m ∧ A.natDeg ≤ m ∧ B.natDeg ≤ N ∧ A.eval ζ = zero ∧
      sylRes m N A B ≠ zero :=
  ⟨1, 1, ofList [neg (g 3), g 1], ofList [neg (g 5), g 1], g 3,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

#verify_constructive SylElim.sylRes_mul_X_sub SylElim.sylRes_eq_zero_of_common_root
#verify_constructive SylElim.divModLead_spec SylElim.isUnit_sylRes_of_bezout SylElim.degFn_sylRes_le
#verify_constructive inhabited_sylRes_mul_X_sub tooth_sylRes_needs_both_roots
#tooth_pair SylElim.sylRes_eq_zero_of_common_root vs tooth_sylRes_needs_both_roots
#verify_inhabited SylElim.sylRes_mul_X_sub inhabited_sylRes_mul_X_sub

end SylvesterEliminationTests
end Qsag
end
