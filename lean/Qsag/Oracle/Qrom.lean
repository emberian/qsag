module
public import Qsag.Math.Algebra
public import Qsag.Math.Primality
public import Qsag.Spec.Bounds
public import Qsag.Oracle.FiatShamir
public import Qsag.Oracle.Spn
public import Qsag.Tactic.Prelude
public section
-- Avoid the choice-based LawfulBEq derived from the Fin order package.
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048
/-! ## 1. Rational Probability Bounds, `OracleComp` & `KeyedLazyRO` Floors -/

/-- Exact cross-multiplied rational inequality `a.1 / a.2 ≤ b.1 / b.2` with mandatory positive denominators (`0 < a.2 ∧ 0 < b.2`). -/
@[expose] def ratLe (a b : Nat × Nat) : Prop :=
  0 < a.2 ∧ 0 < b.2 ∧ a.1 * b.2 ≤ b.1 * a.2

theorem ratLe_zero_den_false (a b c : Nat) : ¬ ratLe (a, 0) (b, c) ∧ ¬ ratLe (a, c) (b, 0) := by
  constructor
  · intro h; exact Nat.not_lt_zero _ h.1
  · intro h; exact Nat.not_lt_zero _ h.2.1

@[expose] def deployedCardBitVec256 : Nat := 2 ^ 256
@[expose] def deployedCardGoldilocks4 : Nat := goldilocksPrime ^ 4

theorem deployedCardGoldilocks4_ne_bitVec256 :
    deployedCardGoldilocks4 ≠ deployedCardBitVec256 ∧
    2 ^ 255 < deployedCardGoldilocks4 ∧
    deployedCardGoldilocks4 < deployedCardBitVec256 := by
  unfold deployedCardGoldilocks4 deployedCardBitVec256
  decide

inductive OracleComp (Dom Cod α : Type) where
  | pure (ret : α)
  | query (q : Dom) (next : Cod → OracleComp Dom Cod α)

@[expose] def evalOracleComp {Dom Cod α : Type} (O : Dom → Cod) : OracleComp Dom Cod α → α
  | .pure ret => ret
  | .query q next => evalOracleComp O (next (O q))

def queryLog {Dom Cod α : Type} (O : Dom → Cod) : OracleComp Dom Cod α → List Dom
  | .pure _ => []
  | .query q next => q :: queryLog O (next (O q))

def QueryBounded {Dom Cod α : Type} : Nat → OracleComp Dom Cod α → Prop
  | _, .pure _ => True
  | 0, .query _ _ => False
  | Q + 1, .query _ next => ∀ y : Cod, QueryBounded Q (next y)

theorem queryLog_length_le {Dom Cod α : Type} (O : Dom → Cod) :
    ∀ {Q : Nat} {prog : OracleComp Dom Cod α}, QueryBounded Q prog → (queryLog O prog).length ≤ Q
  | _, .pure _, _ => Nat.zero_le _
  | 0, .query _ _, h => False.elim h
  | Q + 1, .query q next, h => by
    simp only [queryLog, List.length_cons]
    have ih := queryLog_length_le O (h (O q))
    omega

def pinOracle {Dom Cod : Type} [DecidableEq Dom] (O : Dom → Cod) (x₀ : Dom) (v : Cod) : Dom → Cod :=
  fun x => if x = x₀ then v else O x

theorem evalOracleComp_pin_untouched {Dom Cod α : Type} [DecidableEq Dom]
    (O : Dom → Cod) (x₀ : Dom) (v : Cod) :
    ∀ (prog : OracleComp Dom Cod α), x₀ ∉ queryLog O prog →
      evalOracleComp (pinOracle O x₀ v) prog = evalOracleComp O prog ∧
      queryLog (pinOracle O x₀ v) prog = queryLog O prog
  | .pure _, _ => ⟨rfl, rfl⟩
  | .query q next, hNotMem => by
    simp only [queryLog, List.mem_cons, not_or] at hNotMem
    have hqNe : q ≠ x₀ := fun hEq => hNotMem.1 hEq.symm
    have hPinQ : pinOracle O x₀ v q = O q := by simp [pinOracle, hqNe]
    simp only [evalOracleComp, queryLog, hPinQ]
    obtain ⟨hEval, hLog⟩ := evalOracleComp_pin_untouched O x₀ v (next (O q)) hNotMem.2
    exact ⟨hEval, congrArg (q :: ·) hLog⟩

/-- **Slice Reprogramming Lemma (`condProb_pin_untouched`)**. -/
theorem condProb_pin_untouched {Dom Cod α : Type} [DecidableEq Dom]
    (C : Nat) (decodeCod : Fin C → Cod)
    (O : Dom → Cod) (x₀ : Dom) (prog : OracleComp Dom Cod α) (accept : α → Bool)
    (guessProg : OracleComp Dom Cod (Fin C))
    (hUntouched : x₀ ∉ queryLog O prog)
    (hUntouchedGuess : x₀ ∉ queryLog O guessProg) :
    qsum C (fun c => if accept (evalOracleComp (pinOracle O x₀ (decodeCod c)) prog) then 1 else 0) =
      C * (if accept (evalOracleComp O prog) then 1 else 0) ∧
    qsum C (fun c => if evalOracleComp (pinOracle O x₀ (decodeCod c)) guessProg = c then 1 else 0) ≤
      (if 0 < C then 1 else 0) := by
  refine ⟨?_, ?_⟩
  · have hCongr :
        qsum C (fun c => if accept (evalOracleComp (pinOracle O x₀ (decodeCod c)) prog) then 1 else 0) =
        qsum C (fun _ => if accept (evalOracleComp O prog) then 1 else 0) := by
      apply qsum_congr
      intro c
      rw [(evalOracleComp_pin_untouched O x₀ (decodeCod c) prog hUntouched).1]
    rw [hCongr, qsum_const]
  · cases C with
    | zero => simp [qsum_zero]
    | succ n =>
      have hCongr :
          qsum (n + 1) (fun c => if evalOracleComp (pinOracle O x₀ (decodeCod c)) guessProg = c then 1 else 0) =
          qsum (n + 1) (fun c => if c = evalOracleComp O guessProg then 1 else 0) := by
        apply qsum_congr
        intro c
        rw [(evalOracleComp_pin_untouched O x₀ (decodeCod c) guessProg hUntouchedGuess).1]
        by_cases hcg : evalOracleComp O guessProg = c
        · rw [hcg]
        · have hgc : c ≠ evalOracleComp O guessProg := fun h => hcg h.symm
          rw [ite_eq_right_iff.mpr (fun h => False.elim (hcg h)),
              ite_eq_right_iff.mpr (fun h => False.elim (hgc h))]
      rw [hCongr, qsum_eq_indicator]
      simp

abbrev UnifiedTreeDom (LeafBlock Digest32 : Type) := Sum LeafBlock (Digest32 × Digest32)

def merkleWalkQueries (depth : Nat) : Nat := 2 + 2 * depth

def stepCollisionHits (C : Nat) (prevDigests : List (Fin C)) : Nat :=
  qsum C (fun y => if y ∈ prevDigests then 1 else 0)

def cumulativeBirthdayBound : Nat → Nat
  | 0 => 1
  | q + 1 => cumulativeBirthdayBound q + q

theorem cumulativeBirthdayBound_le_sq_succ : ∀ (Q : Nat),
    cumulativeBirthdayBound Q ≤ Q * Q + 1
  | 0 => by simp [cumulativeBirthdayBound]
  | q + 1 => by
    simp only [cumulativeBirthdayBound]
    have ih := cumulativeBirthdayBound_le_sq_succ q
    have hExpand : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    omega

private theorem qsum_stepHits_le_sq_succ (C : Nat) :
    ∀ (Q : Nat) (stepHistory : (i : Nat) → i < Q → List (Fin C)),
      (∀ i (hi : i < Q), (stepHistory i hi).length ≤ i) →
      1 + qsum Q (fun idx => stepCollisionHits C (stepHistory idx.val idx.isLt)) ≤ Q * Q + 1
  | 0, _, _ => by simp [qsum_zero]
  | q + 1, stepHistory, hHistLen => by
    have hPt : ∀ idx : Fin (q + 1),
        stepCollisionHits C (stepHistory idx.val idx.isLt) ≤ q := fun idx =>
      Nat.le_trans (Nat.le_trans (qsum_mem_list_le C _) (hHistLen idx.val idx.isLt))
        (Nat.le_of_lt_succ idx.isLt)
    have hSumLe : qsum (q + 1) (fun idx => stepCollisionHits C (stepHistory idx.val idx.isLt)) ≤
        (q + 1) * q := by
      rw [← qsum_const (q + 1) q]
      exact qsum_le_qsum hPt
    have hMulLe : (q + 1) * q ≤ (q + 1) * (q + 1) := Nat.mul_le_mul_left (q + 1) (Nat.le_succ q)
    omega

/-- **Unified `LeafBlock ⊕ (Digest32 × Digest32)` Tree Birthday Floor (`unifiedTreeGame_birthday_le`)**. -/
theorem unifiedTreeGame_birthday_le {LeafBlock Digest32 : Type}
    (C Q depth : Nat) (hCPos : 0 < C) (hWalk : merkleWalkQueries depth ≤ Q)
    (stepHistory : (i : Nat) → i < Q → List (Fin C))
    (hHistLen : ∀ i (hi : i < Q), (stepHistory i hi).length ≤ i)
    (leafA : LeafBlock) (nodeB : Digest32 × Digest32) :
    (Sum.inl leafA : UnifiedTreeDom LeafBlock Digest32) ≠ Sum.inr nodeB ∧
    ratLe (1 + qsum Q (fun idx => stepCollisionHits C (stepHistory idx.val idx.isLt)), C)
          (Q * Q + 1, C) ∧
    cumulativeBirthdayBound (merkleWalkQueries depth) ≤ Q * Q + 1 := by
  have hCumMono : ∀ a b, a ≤ b → cumulativeBirthdayBound a ≤ cumulativeBirthdayBound b := by
    intro a b hab
    induction hab with
    | refl => exact Nat.le_refl _
    | step _ ih => simp only [cumulativeBirthdayBound]; omega
  refine ⟨?_, ?_, Nat.le_trans (hCumMono _ _ hWalk) (cumulativeBirthdayBound_le_sq_succ Q)⟩
  · intro h; cases h
  · unfold ratLe
    exact ⟨hCPos, hCPos, Nat.mul_le_mul_right C (qsum_stepHits_le_sq_succ C Q stepHistory hHistLen)⟩

def keyedPrfRealAccept {TagDom Cod : Type} (cardB : Nat)
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool) : Nat :=
  qsum cardB (fun kStar =>
    let world0 : Fin cardB × TagDom → Cod :=
      fun q => if q.1 = kStar then secretFn q.2 else baseO q
    if evalOracleComp world0 A then 1 else 0)

def keyedPrfIdealAccept {TagDom Cod : Type} (cardB : Nat)
    (baseO : Fin cardB × TagDom → Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool) : Nat :=
  qsum cardB (fun _ => if evalOracleComp baseO A then 1 else 0)

theorem evalOracleComp_agree_if_key_unqueried {TagDom Cod α : Type} {cardB : Nat}
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod) (kStar : Fin cardB) :
    ∀ (prog : OracleComp (Fin cardB × TagDom) Cod α),
      kStar ∉ (queryLog baseO prog).map Prod.fst →
      evalOracleComp (fun q => if q.1 = kStar then secretFn q.2 else baseO q) prog =
        evalOracleComp baseO prog
  | .pure _, _ => rfl
  | .query q next, hNotMem => by
    simp only [queryLog, List.map_cons, List.mem_cons, not_or] at hNotMem
    have hNe : q.1 ≠ kStar := fun h => hNotMem.1 h.symm
    simp only [evalOracleComp, hNe, ↓reduceIte]
    exact evalOracleComp_agree_if_key_unqueried baseO secretFn kStar (next (baseO q)) hNotMem.2

/-- **Keyed-ROM Blinding / PRF Hiding Floor (`hidingAdv_le`)**. -/
theorem hidingAdv_le {TagDom Cod : Type}
    (cardB Q : Nat) (hCardPos : 0 < cardB)
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool)
    (hBounded : QueryBounded Q A) :
    let advNum := natAbsDiff (keyedPrfRealAccept cardB baseO secretFn A)
                             (keyedPrfIdealAccept cardB baseO A)
    advNum ≤ Q ∧
    ratLe (advNum, cardB) (2 * Q, cardB) := by
  intro advNum
  let touchedKeys : List (Fin cardB) := (queryLog baseO A).map Prod.fst
  have hLen : touchedKeys.length ≤ Q := by
    simp only [touchedKeys, List.length_map]
    exact queryLog_length_le baseO hBounded
  have hDiff : advNum ≤ qsum cardB (fun k => if k ∈ touchedKeys then 1 else 0) := by
    have hBadEq :
        qsum cardB (fun k => if decide (k ∈ touchedKeys) = true then 1 else 0) =
        qsum cardB (fun k => if k ∈ touchedKeys then 1 else 0) := by
      apply qsum_congr
      intro k
      by_cases hk : k ∈ touchedKeys <;> simp [hk]
    rw [← hBadEq]
    exact qsum_indicator_diff_le
      (fun kStar => evalOracleComp (fun q => if q.1 = kStar then secretFn q.2 else baseO q) A)
      (fun _ => evalOracleComp baseO A)
      (fun k => decide (k ∈ touchedKeys))
      (fun k hkFalse => by
        have hkNotMem : k ∉ touchedKeys := fun hm => by simp [hm] at hkFalse
        exact evalOracleComp_agree_if_key_unqueried baseO secretFn k A hkNotMem)
  have hAdvLeQ : advNum ≤ Q :=
    Nat.le_trans hDiff (Nat.le_trans (qsum_mem_list_le cardB touchedKeys) hLen)
  refine ⟨hAdvLeQ, ?_⟩
  unfold ratLe
  have h2Q : advNum ≤ 2 * Q := by omega
  exact ⟨hCardPos, hCardPos, Nat.mul_le_mul_right cardB h2Q⟩

theorem hidingAdv_le_deployed {TagDom Cod : Type} (Q : Nat)
    (baseBv : Fin deployedCardBitVec256 × TagDom → Cod)
    (baseGl : Fin deployedCardGoldilocks4 × TagDom → Cod)
    (secFn : TagDom → Cod)
    (Abv : OracleComp (Fin deployedCardBitVec256 × TagDom) Cod Bool)
    (Agl : OracleComp (Fin deployedCardGoldilocks4 × TagDom) Cod Bool)
    (hBv : QueryBounded Q Abv) (hGl : QueryBounded Q Agl) :
    ratLe (natAbsDiff (keyedPrfRealAccept deployedCardBitVec256 baseBv secFn Abv)
                      (keyedPrfIdealAccept deployedCardBitVec256 baseBv Abv),
           deployedCardBitVec256)
          (2 * Q, deployedCardBitVec256) ∧
    ratLe (natAbsDiff (keyedPrfRealAccept deployedCardGoldilocks4 baseGl secFn Agl)
                      (keyedPrfIdealAccept deployedCardGoldilocks4 baseGl Agl),
           deployedCardGoldilocks4)
          (2 * Q, deployedCardGoldilocks4) :=
  ⟨(hidingAdv_le deployedCardBitVec256 Q (by unfold deployedCardBitVec256; decide) baseBv secFn Abv hBv).2,
   (hidingAdv_le deployedCardGoldilocks4 Q (by unfold deployedCardGoldilocks4; decide) baseGl secFn Agl hGl).2⟩

theorem RatBound.to_ratLe_iff (a b : RatBound) :
    RatBound.le a b ↔ ratLe (a.num, a.den) (b.num, b.den) := by
  unfold RatBound.le ratLe
  exact ⟨fun h => ⟨a.h_pos, b.h_pos, h⟩, fun h => h.2.2⟩

/-! ## §2. Unitary Quantum Query Mechanics (`GaussInt`), `[BBBV97]` / `[AHU19]` One-Way-to-Hiding,
           Born Rule & Adaptive Query Trees -/

private theorem ofNat_add_eq (a b : Nat) : Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b := rfl
private theorem ofNat_mul_eq (a b : Nat) : Int.ofNat (a * b) = Int.ofNat a * Int.ofNat b := rfl

private theorem int_sq_eq_natAbs_sq (a : Int) : a * a = Int.ofNat (a.natAbs * a.natAbs) := by
  cases a with
  | ofNat _ => rfl
  | negSucc _ => rfl

private theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  rw [int_sq_eq_natAbs_sq]
  exact Int.ofNat_le.mpr (Nat.zero_le _)

/-! ### §2.1 Constructive Finite Sum Combinatorics & Bijection Invariance -/

private def finIntSum : (q : Nat) → (Fin q → Int) → Int
  | 0, _ => 0
  | q + 1, f => f ⟨0, Nat.zero_lt_succ q⟩ +
      finIntSum q (fun t => f ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)

/-- Exact Gaussian integer `re + i * im` (`ℤ[i]`), enabling constructive unitary quantum mechanics
    with zero `ℝ`/`ℂ` axioms, zero square roots, and syntactic equality. -/
structure GaussInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

@[ext] theorem GaussInt.ext {z w : GaussInt} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; cases hre; cases him; rfl

namespace GaussInt

def zero : GaussInt := ⟨0, 0⟩
def one : GaussInt := ⟨1, 0⟩
def neg (z : GaussInt) : GaussInt := ⟨-z.re, -z.im⟩
def conj (z : GaussInt) : GaussInt := ⟨z.re, -z.im⟩
def add (z w : GaussInt) : GaussInt := ⟨z.re + w.re, z.im + w.im⟩
def sub (z w : GaussInt) : GaussInt := ⟨z.re - w.re, z.im - w.im⟩
def scaleInt (c : Int) (z : GaussInt) : GaussInt := ⟨c * z.re, c * z.im⟩
def mul (z w : GaussInt) : GaussInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- Exact squared modulus `|z|² = re² + im²` as an `Int` (`≥ 0`) and as a `Nat`. -/
def normSqInt (z : GaussInt) : Int := z.re * z.re + z.im * z.im
def normSq (z : GaussInt) : Nat := z.re.natAbs * z.re.natAbs + z.im.natAbs * z.im.natAbs

/-- Real inner product `Re(z · conj w) = z.re * w.re + z.im * w.im`. -/
def reInner (z w : GaussInt) : Int := z.re * w.re + z.im * w.im

theorem normSqInt_eq_ofNat_normSq (z : GaussInt) :
    normSqInt z = Int.ofNat (normSq z) := by
  unfold normSqInt normSq
  rw [int_sq_eq_natAbs_sq z.re, int_sq_eq_natAbs_sq z.im, ← ofNat_add_eq]

theorem normSq_zero : normSq zero = 0 := by rfl

theorem normSq_neg (z : GaussInt) : normSq (neg z) = normSq z := by
  unfold normSq neg
  rw [Int.natAbs_neg, Int.natAbs_neg]

theorem normSq_add_int (z w : GaussInt) :
    normSqInt (add z w) = normSqInt z + normSqInt w + 2 * reInner z w := by
  unfold normSqInt add reInner
  have hRe : (z.re + w.re) * (z.re + w.re) = z.re * z.re + w.re * w.re + 2 * (z.re * w.re) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm w.re z.re]
    omega
  have hIm : (z.im + w.im) * (z.im + w.im) = z.im * z.im + w.im * w.im + 2 * (z.im * w.im) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm w.im z.im]
    omega
  rw [hRe, hIm]
  omega

theorem normSq_sub_int (z w : GaussInt) :
    normSqInt (sub z w) = normSqInt z + normSqInt w - 2 * reInner z w := by
  unfold normSqInt sub reInner
  have hNegSq : ∀ x : Int, (-x) * (-x) = x * x := fun x => by
    rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  have hRe : (z.re - w.re) * (z.re - w.re) = z.re * z.re + w.re * w.re - 2 * (z.re * w.re) := by
    rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
        Int.mul_neg, Int.neg_mul, hNegSq, Int.mul_comm w.re z.re]
    omega
  have hIm : (z.im - w.im) * (z.im - w.im) = z.im * z.im + w.im * w.im - 2 * (z.im * w.im) := by
    rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
        Int.mul_neg, Int.neg_mul, hNegSq, Int.mul_comm w.im z.im]
    omega
  rw [hRe, hIm]
  omega

/-- **Parallelogram Identity**: `|z - w|² + |z + w|² = 2 |z|² + 2 |w|²`. -/
theorem normSq_parallelogram (z w : GaussInt) :
    normSq (sub z w) + normSq (add z w) = 2 * normSq z + 2 * normSq w := by
  have hInt : Int.ofNat (normSq (sub z w) + normSq (add z w)) =
      Int.ofNat (2 * normSq z + 2 * normSq w) := by
    rw [ofNat_add_eq, ofNat_add_eq, ofNat_mul_eq, ofNat_mul_eq,
        ← normSqInt_eq_ofNat_normSq, ← normSqInt_eq_ofNat_normSq,
        ← normSqInt_eq_ofNat_normSq, ← normSqInt_eq_ofNat_normSq,
        normSq_sub_int, normSq_add_int]
    change normSqInt z + normSqInt w - 2 * reInner z w +
           (normSqInt z + normSqInt w + 2 * reInner z w) =
           2 * normSqInt z + 2 * normSqInt w
    omega
  exact Int.ofNat.inj hInt

theorem normSq_sub_le (z w : GaussInt) :
    normSq (sub z w) ≤ 2 * normSq z + 2 * normSq w := by
  have h := normSq_parallelogram z w
  omega

theorem normSq_add_le (z w : GaussInt) :
    normSq (add z w) ≤ 2 * normSq z + 2 * normSq w := by
  have h := normSq_parallelogram z w
  omega

end GaussInt

/-- Finite sum of Gaussian-integer amplitudes over `Fin q`. -/
def finGaussSum : (q : Nat) → (Fin q → GaussInt) → GaussInt
  | 0, _ => GaussInt.zero
  | q + 1, v =>
    GaussInt.add (v ⟨0, Nat.zero_lt_succ q⟩)
      (finGaussSum q (fun t => v ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩))

/-- Sum of pairwise squared differences `∑_{0 ≤ s < t < q} |v_s - v_t|²`. -/
def pairDiffNormSq : (q : Nat) → (Fin q → GaussInt) → Nat
  | 0, _ => 0
  | q + 1, v =>
    let v0 := v ⟨0, Nat.zero_lt_succ q⟩
    let tail : Fin q → GaussInt := fun t => v ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (tail t))) + pairDiffNormSq q tail

private theorem qsum_sub_with_head :
    ∀ (q : Nat) (v0 : GaussInt) (tail : Fin q → GaussInt),
      Int.ofNat (qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (tail t)))) =
        Int.ofNat q * GaussInt.normSqInt v0 +
        Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) -
        2 * GaussInt.reInner v0 (finGaussSum q tail)
  | 0, v0, _ => by
    simp [qsum_zero, finGaussSum, GaussInt.zero, GaussInt.reInner]
  | q + 1, v0, tail => by
    let t0 := tail ⟨0, Nat.zero_lt_succ q⟩
    let rest : Fin q → GaussInt := fun i => tail ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have ih := qsum_sub_with_head q v0 rest
    simp only [qsum_succ]
    change Int.ofNat (GaussInt.normSq (GaussInt.sub v0 t0) +
             qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (rest t)))) =
           Int.ofNat (q + 1) * GaussInt.normSqInt v0 +
             Int.ofNat (GaussInt.normSq t0 + qsum q (fun t => GaussInt.normSq (rest t))) -
             2 * GaussInt.reInner v0 (GaussInt.add t0 (finGaussSum q rest))
    rw [ofNat_add_eq (GaussInt.normSq (GaussInt.sub v0 t0)),
        ofNat_add_eq (GaussInt.normSq t0),
        ← GaussInt.normSqInt_eq_ofNat_normSq (GaussInt.sub v0 t0),
        ← GaussInt.normSqInt_eq_ofNat_normSq t0,
        GaussInt.normSq_sub_int v0 t0, ih]
    have hRe : GaussInt.reInner v0 (GaussInt.add t0 (finGaussSum q rest)) =
        GaussInt.reInner v0 t0 + GaussInt.reInner v0 (finGaussSum q rest) := by
      unfold GaussInt.reInner GaussInt.add
      rw [Int.mul_add, Int.mul_add]
      omega
    have hQ : Int.ofNat (q + 1) * GaussInt.normSqInt v0 =
        GaussInt.normSqInt v0 + Int.ofNat q * GaussInt.normSqInt v0 := by
      rw [ofNat_add_eq q 1, Int.add_mul]
      change Int.ofNat q * GaussInt.normSqInt v0 + 1 * GaussInt.normSqInt v0 = _
      rw [Int.one_mul, Int.add_comm]
    rw [hRe, hQ]
    omega

/-- **Square-Root-Free `q`-Way Cauchy–Schwarz Identity (`gauss_sum_of_squares_identity`)**:
    `q * (∑_{t < q} |v_t|²) = |∑_{t < q} v_t|² + ∑_{s < t} |v_s - v_t|²`. -/
theorem gauss_sum_of_squares_identity :
    ∀ (q : Nat) (v : Fin q → GaussInt),
      q * qsum q (fun t => GaussInt.normSq (v t)) =
        GaussInt.normSq (finGaussSum q v) + pairDiffNormSq q v
  | 0, _ => by rw [qsum_zero]; rfl
  | q + 1, v => by
    let v0 := v ⟨0, Nat.zero_lt_succ q⟩
    let tail : Fin q → GaussInt := fun t => v ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    have ih := gauss_sum_of_squares_identity q tail
    apply Int.ofNat.inj
    simp only [qsum_succ]
    change Int.ofNat ((q + 1) * (GaussInt.normSq v0 + qsum q (fun t => GaussInt.normSq (tail t)))) =
      Int.ofNat (GaussInt.normSq (GaussInt.add v0 (finGaussSum q tail)) +
        (qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (tail t))) + pairDiffNormSq q tail))
    have ihInt : Int.ofNat q * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) =
        GaussInt.normSqInt (finGaussSum q tail) + Int.ofNat (pairDiffNormSq q tail) := by
      rw [GaussInt.normSqInt_eq_ofNat_normSq, ← ofNat_add_eq, ← ofNat_mul_eq, ih]
    rw [ofNat_mul_eq (q + 1),
        ofNat_add_eq (GaussInt.normSq v0),
        ofNat_add_eq (GaussInt.normSq (GaussInt.add v0 (finGaussSum q tail))),
        ofNat_add_eq (qsum q (fun t => GaussInt.normSq (GaussInt.sub v0 (tail t)))),
        ← GaussInt.normSqInt_eq_ofNat_normSq (GaussInt.add v0 (finGaussSum q tail)),
        GaussInt.normSq_add_int v0 (finGaussSum q tail),
        qsum_sub_with_head q v0 tail,
        ← GaussInt.normSqInt_eq_ofNat_normSq v0]
    have hQ1 : Int.ofNat (q + 1) * GaussInt.normSqInt v0 =
        GaussInt.normSqInt v0 + Int.ofNat q * GaussInt.normSqInt v0 := by
      rw [ofNat_add_eq q 1, Int.add_mul]
      change Int.ofNat q * GaussInt.normSqInt v0 + 1 * GaussInt.normSqInt v0 = _
      rw [Int.one_mul, Int.add_comm]
    have hS1 : Int.ofNat (q + 1) * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) =
        Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) +
        Int.ofNat q * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) := by
      rw [ofNat_add_eq q 1, Int.add_mul]
      change Int.ofNat q * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) +
        1 * Int.ofNat (qsum q (fun t => GaussInt.normSq (tail t))) = _
      rw [Int.one_mul, Int.add_comm]
    rw [Int.mul_add, hQ1, hS1, ihInt]
    omega

/-- Immediate Cauchy–Schwarz norm inequality `|∑_{t < q} v_t|² ≤ q * ∑_{t < q} |v_t|²`. -/
theorem normSq_finGaussSum_le (q : Nat) (v : Fin q → GaussInt) :
    GaussInt.normSq (finGaussSum q v) ≤ q * qsum q (fun t => GaussInt.normSq (v t)) := by
  have h := gauss_sum_of_squares_identity q v
  omega

/-! ### §2.2 Quantum State Vectors `QVec`, `oracleXor` Isometry, Scaled Unitaries & `QuantumAdv` -/

/-- Tripartite quantum state vector over query register `Fin cardX`, `w`-bit response register
    `Fin (2 ^ w)`, and `cardAnc`-dimensional ancilla workspace. -/
abbrev QVec (cardX w cardAnc : Nat) : Type :=
  Fin cardX → Fin (2 ^ w) → Fin cardAnc → GaussInt

namespace QVec

def zero (cardX w cardAnc : Nat) : QVec cardX w cardAnc :=
  fun _ _ _ => GaussInt.zero

def add {cardX w cardAnc : Nat} (ψ φ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => GaussInt.add (ψ x y a) (φ x y a)

def sub {cardX w cardAnc : Nat} (ψ φ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => GaussInt.sub (ψ x y a) (φ x y a)

/-- Squared amplitude mass on a single query coordinate `x : Fin cardX`. -/
def queryWeight {cardX w cardAnc : Nat} (ψ : QVec cardX w cardAnc) (x : Fin cardX) : Nat :=
  qsum (2 ^ w) (fun y => qsum cardAnc (fun a => GaussInt.normSq (ψ x y a)))

/-- Squared amplitude mass on a marked subset `S : Fin cardX → Bool` of queries. -/
def queryMassOn {cardX w cardAnc : Nat} (S : Fin cardX → Bool) (ψ : QVec cardX w cardAnc) : Nat :=
  qsum cardX (fun x => if S x = true then queryWeight ψ x else 0)

/-- Total squared Hilbert-space norm `‖ψ‖² = ∑_{x, y, a} |ψ(x, y, a)|²`. -/
def stateNormSq {cardX w cardAnc : Nat} (ψ : QVec cardX w cardAnc) : Nat :=
  qsum cardX (fun x => queryWeight ψ x)

/-- Unnormalized Born numerator `∑_{x : E x = true} queryWeight ψ x` for projective measurement `E`
    on the query/output register `Fin cardX`. -/
def measureNormSq {cardX w cardAnc : Nat} (E : Fin cardX → Bool) (ψ : QVec cardX w cardAnc) : Nat :=
  queryMassOn E ψ

/-- Exact Born-rule measurement probability `measureNormSq E ψ / stateNormSq ψ` as a `RatBound`. -/
def bornProb {cardX w cardAnc : Nat} (E : Fin cardX → Bool)
    (ψ : QVec cardX w cardAnc) (hPos : 0 < stateNormSq ψ) : RatBound :=
  ⟨measureNormSq E ψ, stateNormSq ψ, hPos⟩

theorem queryMassOn_le_stateNormSq {cardX w cardAnc : Nat}
    (S : Fin cardX → Bool) (ψ : QVec cardX w cardAnc) :
    queryMassOn S ψ ≤ stateNormSq ψ := by
  unfold queryMassOn stateNormSq
  apply qsum_le_qsum
  intro x
  cases S x <;> simp

theorem sumQVec_normSq_le {cardX w cardAnc : Nat} (q : Nat)
    (V : Fin q → QVec cardX w cardAnc) :
    stateNormSq (fun x y a => finGaussSum q (fun t => V t x y a)) ≤
      q * qsum q (fun t => stateNormSq (V t)) := by
  unfold stateNormSq queryWeight
  have hPoint :
      qsum cardX (fun x => qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
        GaussInt.normSq (finGaussSum q (fun t => V t x y a))))) ≤
      qsum cardX (fun x => qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
        q * qsum q (fun t => GaussInt.normSq (V t x y a))))) := by
    apply qsum_le_qsum; intro x
    apply qsum_le_qsum; intro y
    apply qsum_le_qsum; intro a
    exact normSq_finGaussSum_le q (fun t => V t x y a)
  apply Nat.le_trans hPoint
  have hSwap :
      qsum cardX (fun x => qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
        q * qsum q (fun t => GaussInt.normSq (V t x y a))))) =
      q * qsum q (fun t => qsum cardX (fun x => qsum (2 ^ w) (fun y =>
        qsum cardAnc (fun a => GaussInt.normSq (V t x y a))))) := by
    have p1 : ∀ x y, qsum cardAnc (fun a => q * qsum q (fun t => GaussInt.normSq (V t x y a))) =
        q * qsum q (fun t => qsum cardAnc (fun a => GaussInt.normSq (V t x y a))) := by
      intro x y
      rw [qsum_mul_left, qsum_comm]
    have p2 : ∀ x, qsum (2 ^ w) (fun y =>
        qsum cardAnc (fun a => q * qsum q (fun t => GaussInt.normSq (V t x y a)))) =
        q * qsum q (fun t => qsum (2 ^ w) (fun y =>
          qsum cardAnc (fun a => GaussInt.normSq (V t x y a)))) := by
      intro x
      rw [qsum_congr (fun y => p1 x y), qsum_mul_left, qsum_comm]
    rw [qsum_congr p2, qsum_mul_left, qsum_comm]
  exact Nat.le_of_eq hSwap

end QVec

/-- Bitwise XOR permutation on `Fin (2 ^ w)` induced by `v : BitVec w`. -/
def xorFin {w : Nat} (y : Fin (2 ^ w)) (v : BitVec w) : Fin (2 ^ w) :=
  (BitVec.ofFin y ^^^ v).toFin

theorem xorFin_involutive {w : Nat} (v : BitVec w) (y : Fin (2 ^ w)) :
    xorFin (xorFin y v) v = y := by
  unfold xorFin
  have hXor : (BitVec.ofFin y ^^^ v) ^^^ v = BitVec.ofFin y := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor]
    cases (BitVec.ofFin y).getLsbD i <;> cases v.getLsbD i <;> rfl
  rw [BitVec.ofFin_toFin, hXor, BitVec.toFin_ofFin]

/-- Reversible QROM bit-XOR oracle `O_H : |x, y, a⟩ ↦ |x, y ⊕ H(x), a⟩`. -/
def oracleXor {cardX w cardAnc : Nat} (H : Fin cardX → BitVec w)
    (ψ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => ψ x (xorFin y (H x)) a

theorem oracleXor_involutive {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) :
    oracleXor H (oracleXor H ψ) = ψ := by
  funext x y a
  simp [oracleXor, xorFin_involutive]

theorem oracleXor_sub {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ φ : QVec cardX w cardAnc) :
    oracleXor H (ψ.sub φ) = (oracleXor H ψ).sub (oracleXor H φ) := by rfl

theorem oracleXor_queryWeight {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) (x : Fin cardX) :
    QVec.queryWeight (oracleXor H ψ) x = QVec.queryWeight ψ x := by
  unfold QVec.queryWeight oracleXor
  exact qsum_involutive (fun y => xorFin y (H x)) (xorFin_involutive (H x))
    (fun y => qsum cardAnc (fun a => GaussInt.normSq (ψ x y a)))

/-- **`oracleXor` Isometry Theorem**: `O_H` preserves squared Hilbert-space norm with exact scale `1`. -/
theorem oracleXor_isometry {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) :
    QVec.stateNormSq (oracleXor H ψ) = QVec.stateNormSq ψ := by
  unfold QVec.stateNormSq
  exact qsum_congr (oracleXor_queryWeight H ψ)

/-- Pointwise oracle-difference bound: if `H` and `H'` agree outside `S`, then
    `‖(O_H - O_{H'}) ψ‖² ≤ 4 * queryMassOn S ψ`. -/
theorem oracleXor_diff_normSq_le {cardX w cardAnc : Nat}
    (H H' : Fin cardX → BitVec w) (S : Fin cardX → Bool)
    (hAgree : ∀ x : Fin cardX, S x = false → H x = H' x)
    (ψ : QVec cardX w cardAnc) :
    QVec.stateNormSq ((oracleXor H ψ).sub (oracleXor H' ψ)) ≤
      4 * QVec.queryMassOn S ψ := by
  unfold QVec.stateNormSq QVec.queryMassOn
  rw [← qsum_mul_left 4]
  apply qsum_le_qsum
  intro x
  cases hSx : S x
  · have hEq := hAgree x hSx
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, QVec.queryWeight,
      QVec.sub, oracleXor, hEq]
    have h0 : qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
        GaussInt.normSq (GaussInt.sub (ψ x (xorFin y (H' x)) a) (ψ x (xorFin y (H' x)) a)))) =
        qsum (2 ^ w) (fun _ => 0) := by
      apply qsum_congr; intro y
      have ha0 : qsum cardAnc (fun a =>
          GaussInt.normSq (GaussInt.sub (ψ x (xorFin y (H' x)) a) (ψ x (xorFin y (H' x)) a))) =
          qsum cardAnc (fun _ => 0) := by
        apply qsum_congr; intro a
        unfold GaussInt.sub GaussInt.normSq
        simp
      rw [ha0, qsum_const]; omega
    rw [h0, qsum_const]; omega
  · simp only [↓reduceIte]
    have hPt : QVec.queryWeight ((oracleXor H ψ).sub (oracleXor H' ψ)) x ≤
        2 * QVec.queryWeight (oracleXor H ψ) x + 2 * QVec.queryWeight (oracleXor H' ψ) x := by
      unfold QVec.queryWeight QVec.sub
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro y
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro a
      exact GaussInt.normSq_sub_le _ _
    rw [oracleXor_queryWeight H ψ x, oracleXor_queryWeight H' ψ x] at hPt
    omega

/-- Linear scaled unitary operator `U` on `QVec cardX w cardAnc` with positive integer squared-norm
    factor `scaleSq > 0` (`‖U ψ‖² = scaleSq * ‖ψ‖²`). Supports strict norm-`1` unitaries, exact
    Hadamards (`scaleSq = 2`), and exact `M`-item Grover reflections (`scaleSq = M^2`) without `√2`. -/
structure ScaledUnitary (cardX w cardAnc : Nat) where
  apply : QVec cardX w cardAnc → QVec cardX w cardAnc
  scaleSq : Nat
  h_scale_pos : 0 < scaleSq
  map_sub : ∀ ψ φ, apply (ψ.sub φ) = (apply ψ).sub (apply φ)
  normSq_eq : ∀ ψ, QVec.stateNormSq (apply ψ) = scaleSq * QVec.stateNormSq ψ

/-- Identity unitary (`scaleSq = 1`). -/
def ScaledUnitary.id (cardX w cardAnc : Nat) : ScaledUnitary cardX w cardAnc where
  apply ψ := ψ
  scaleSq := 1
  h_scale_pos := Nat.zero_lt_one
  map_sub _ _ := rfl
  normSq_eq _ := (Nat.one_mul _).symm

private theorem qsum_two (f : Fin 2 → Nat) :
    qsum 2 f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ := by
  simp [qsum_zero, qsum_succ]

/-- Concrete 1-qubit Hadamard gate `[[1, 1], [1, -1]]` on query register `Fin 2` (`scaleSq = 2`),
    certifying that `ScaledUnitary` natively encompasses Clifford superposition creation. -/
def hadamardQuery2 (w cardAnc : Nat) : ScaledUnitary 2 w cardAnc where
  apply ψ x y a :=
    if x.val == 0 then
      GaussInt.add (ψ ⟨0, by decide⟩ y a) (ψ ⟨1, by decide⟩ y a)
    else
      GaussInt.sub (ψ ⟨0, by decide⟩ y a) (ψ ⟨1, by decide⟩ y a)
  scaleSq := 2
  h_scale_pos := by decide
  map_sub ψ φ := by
    funext x y a
    cases h0 : (x.val == 0)
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, QVec.sub, GaussInt.sub]
      ext <;> dsimp only <;> omega
    · simp only [h0, ↓reduceIte, QVec.sub, GaussInt.add, GaussInt.sub]
      ext <;> dsimp only <;> omega
  normSq_eq ψ := by
    unfold QVec.stateNormSq QVec.queryWeight
    rw [qsum_two, qsum_two]
    dsimp only
    have h00 : ((0 : Nat) == 0) = true := rfl
    have h10 : ((1 : Nat) == 0) = false := rfl
    simp only [h00, h10, Bool.false_eq_true, ↓reduceIte]
    rw [← qsum_add, Nat.left_distrib, ← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
    apply qsum_congr; intro y
    rw [← qsum_add, ← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
    apply qsum_congr; intro a
    have hp := GaussInt.normSq_parallelogram (ψ ⟨0, by decide⟩ y a) (ψ ⟨1, by decide⟩ y a)
    omega

/-- Arbitrary `q`-query unitary quantum adversary interleaving `q` oracle calls `O_H` with
    arbitrary scaled unitary circuits `U_0, ..., U_{q-1}`. -/
structure QuantumAdv (cardX w cardAnc q : Nat) where
  init : QVec cardX w cardAnc
  h_init_pos : 0 < QVec.stateNormSq init
  steps : Fin q → ScaledUnitary cardX w cardAnc

/-- State of `A` immediately before query `t` (`0 ≤ t ≤ q`) when interacting with oracle `H`. -/
def advStateAt {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) : (t : Nat) → t ≤ q → QVec cardX w cardAnc
  | 0, _ => A.init
  | t + 1, ht =>
    let prev := advStateAt A H t (Nat.le_of_succ_le ht)
    (A.steps ⟨t, ht⟩).apply (oracleXor H prev)

/-- Final `q`-query quantum state `ψ_q^H` of adversary `A` under oracle `H`. -/
def runQuantumAdv {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) : QVec cardX w cardAnc :=
  advStateAt A H q (Nat.le_refl q)

/-- Cumulative squared-norm scale of the first `t` unitary layers. -/
def prefixScale {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    (t : Nat) → t ≤ q → Nat
  | 0, _ => 1
  | t + 1, ht => (A.steps ⟨t, ht⟩).scaleSq * prefixScale A t (Nat.le_of_succ_le ht)

/-- Cumulative squared-norm scale of the remaining unitary layers `t .. q - 1`. -/
def suffixScale {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    (t : Nat) → t ≤ q → Nat
  | t, _ =>
    if hlt : t < q then
      (A.steps ⟨t, hlt⟩).scaleSq * suffixScale A (t + 1) hlt
    else
      1
termination_by t => q - t

/-- Apply layers `t .. q - 1` using oracle `H` after query `t` has already been applied. -/
def applySuffixFrom {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) : (t : Nat) → t < q → QVec cardX w cardAnc → QVec cardX w cardAnc
  | t, hlt, ψ =>
    let ψ1 := (A.steps ⟨t, hlt⟩).apply ψ
    if hNext : t + 1 < q then
      applySuffixFrom A H (t + 1) hNext (oracleXor H ψ1)
    else
      ψ1
termination_by t => q - t

theorem prefixScale_pos {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    ∀ (t : Nat) (ht : t ≤ q), 0 < prefixScale A t ht
  | 0, _ => Nat.zero_lt_one
  | t + 1, ht => Nat.mul_pos (A.steps ⟨t, ht⟩).h_scale_pos (prefixScale_pos A t (Nat.le_of_succ_le ht))

theorem advStateAt_normSq {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    ∀ (t : Nat) (ht : t ≤ q),
      QVec.stateNormSq (advStateAt A H t ht) = prefixScale A t ht * QVec.stateNormSq A.init
  | 0, _ => (Nat.one_mul _).symm
  | t + 1, ht => by
    simp only [advStateAt, prefixScale]
    rw [(A.steps ⟨t, ht⟩).normSq_eq, oracleXor_isometry,
        advStateAt_normSq A H t (Nat.le_of_succ_le ht), Nat.mul_assoc]

theorem runQuantumAdv_normSq {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    QVec.stateNormSq (runQuantumAdv A H) = prefixScale A q (Nat.le_refl q) * QVec.stateNormSq A.init :=
  advStateAt_normSq A H q (Nat.le_refl q)

theorem runQuantumAdv_normSq_pos {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    0 < QVec.stateNormSq (runQuantumAdv A H) := by
  rw [runQuantumAdv_normSq]
  exact Nat.mul_pos (prefixScale_pos A q (Nat.le_refl q)) A.h_init_pos

theorem applySuffixFrom_sub {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    ∀ (t : Nat) (hlt : t < q) (ψ φ : QVec cardX w cardAnc),
      applySuffixFrom A H t hlt (ψ.sub φ) =
        (applySuffixFrom A H t hlt ψ).sub (applySuffixFrom A H t hlt φ)
  | t, hlt, ψ, φ => by
    unfold applySuffixFrom
    dsimp only
    rw [(A.steps ⟨t, hlt⟩).map_sub]
    split
    · rename_i hNext
      rw [oracleXor_sub, applySuffixFrom_sub A H (t + 1) hNext]
    · rfl
termination_by t => q - t

theorem applySuffixFrom_normSq {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) :
    ∀ (t : Nat) (hlt : t < q) (ψ : QVec cardX w cardAnc),
      QVec.stateNormSq (applySuffixFrom A H t hlt ψ) =
        suffixScale A t (Nat.le_of_lt hlt) * QVec.stateNormSq ψ
  | t, hlt, ψ => by
    unfold applySuffixFrom
    rw [suffixScale]
    simp only [hlt, ↓reduceDIte]
    split
    · rename_i hNext
      rw [applySuffixFrom_normSq A H (t + 1) hNext, oracleXor_isometry,
          (A.steps ⟨t, hlt⟩).normSq_eq, ← Nat.mul_assoc, Nat.mul_comm _ ((A.steps ⟨t, hlt⟩).scaleSq),
          Nat.mul_assoc]
    · rename_i hNotNext
      rw [suffixScale]
      simp only [hNotNext, ↓reduceDIte, Nat.mul_one, (A.steps ⟨t, hlt⟩).normSq_eq]
termination_by t => q - t

theorem prefix_mul_suffix_eq_total {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    ∀ (t : Nat) (ht : t ≤ q),
      prefixScale A t ht * suffixScale A t ht = prefixScale A q (Nat.le_refl q)
  | t, ht => by
    if hlt : t < q then
      have ih := prefix_mul_suffix_eq_total A (t + 1) hlt
      rw [suffixScale]
      simp only [hlt, ↓reduceDIte]
      have hPref : prefixScale A (t + 1) hlt = (A.steps ⟨t, hlt⟩).scaleSq * prefixScale A t ht := rfl
      rw [← ih, hPref, ← Nat.mul_assoc, Nat.mul_comm (prefixScale A t ht), Nat.mul_assoc]
    else
      have hEq : t = q := by omega
      subst hEq
      rw [suffixScale]
      simp
termination_by t => q - t

/-! ### §2.3 Mechanized `[BBBV97]` / `[AHU19]` One-Way-to-Hiding (`O2H`) & Born-Rule Theorems -/

/-- Hybrid quantum state executing `H'` for the first `k` oracle calls and `H` for the remaining
    `q - k` oracle calls (`hybridAdv A H H' 0 = runQuantumAdv A H` and
    `hybridAdv A H H' q = runQuantumAdv A H'`). -/
def hybridAdv {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H H' : Fin cardX → BitVec w) (k : Nat) (hk : k ≤ q) : QVec cardX w cardAnc :=
  if hlt : k < q then
    applySuffixFrom A H k hlt (oracleXor H (advStateAt A H' k hk))
  else
    advStateAt A H' q (Nat.le_refl q)

private theorem applySuffixFrom_step_eq {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w) :
    ∀ (k : Nat) (hk : k ≤ q),
      (if hlt : k < q then applySuffixFrom A H k hlt (oracleXor H (advStateAt A H k hk))
       else advStateAt A H q (Nat.le_refl q)) = runQuantumAdv A H
  | k, hk => by
    if hlt : k < q then
      simp only [hlt, ↓reduceDIte]
      unfold applySuffixFrom
      dsimp only
      have hAdvNext : (A.steps ⟨k, hlt⟩).apply (oracleXor H (advStateAt A H k hk)) =
          advStateAt A H (k + 1) hlt := rfl
      rw [hAdvNext]
      split
      · rename_i hNext
        have ih := applySuffixFrom_step_eq A H (k + 1) (Nat.le_of_lt hNext)
        simp only [hNext, ↓reduceDIte] at ih
        exact ih
      · rename_i hNotNext
        have hEqQ : k + 1 = q := by omega
        unfold runQuantumAdv
        cases hEqQ
        rfl
    else
      have hEqQ : k = q := by omega
      subst hEqQ
      simp [runQuantumAdv]
termination_by k => q - k

private theorem hybridAdv_zero {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H H' : Fin cardX → BitVec w) :
    hybridAdv A H H' 0 (Nat.zero_le q) = runQuantumAdv A H := by
  cases q with
  | zero => rfl
  | succ q' =>
    have hPos : 0 < q' + 1 := Nat.zero_lt_succ q'
    have h0 := applySuffixFrom_step_eq A H 0 (Nat.zero_le (q' + 1))
    simp only [hPos, ↓reduceDIte] at h0
    unfold hybridAdv
    simp only [hPos, ↓reduceDIte]
    exact h0

private theorem hybridAdv_full {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H H' : Fin cardX → BitVec w) :
    hybridAdv A H H' q (Nat.le_refl q) = runQuantumAdv A H' := by
  unfold hybridAdv runQuantumAdv
  simp

private theorem hybridAdv_step_diff {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H H' : Fin cardX → BitVec w)
    (t : Nat) (ht : t < q) :
    (hybridAdv A H H' t (Nat.le_of_lt ht)).sub (hybridAdv A H H' (t + 1) ht) =
      applySuffixFrom A H t ht
        ((oracleXor H (advStateAt A H' t (Nat.le_of_lt ht))).sub
         (oracleXor H' (advStateAt A H' t (Nat.le_of_lt ht)))) := by
  rw [applySuffixFrom_sub]
  have hRhs2 : applySuffixFrom A H t ht (oracleXor H' (advStateAt A H' t (Nat.le_of_lt ht))) =
      hybridAdv A H H' (t + 1) ht := by
    rw [applySuffixFrom.eq_def]
    dsimp only
    have hStep : (A.steps ⟨t, ht⟩).apply (oracleXor H' (advStateAt A H' t (Nat.le_of_lt ht))) =
        advStateAt A H' (t + 1) ht := rfl
    rw [hStep]
    unfold hybridAdv
    if hNext : t + 1 < q then
      simp [hNext]
    else
      have hEqQ : t + 1 = q := by omega
      simp only [hNext, ↓reduceDIte]
      cases hEqQ
      rfl
  rw [hRhs2]
  unfold hybridAdv
  simp only [ht, ↓reduceDIte]

private theorem telescope_gauss_sum :
    ∀ (q : Nat) (seq : (k : Nat) → k ≤ q → GaussInt),
      finGaussSum q (fun t => GaussInt.sub (seq t.1 (Nat.le_of_lt t.2)) (seq (t.1 + 1) t.2)) =
        GaussInt.sub (seq 0 (Nat.zero_le q)) (seq q (Nat.le_refl q))
  | 0, seq => by
    simp [finGaussSum, GaussInt.sub, GaussInt.zero]
  | q + 1, seq => by
    simp only [finGaussSum]
    have ih := telescope_gauss_sum q (fun k hk => seq (k + 1) (Nat.succ_le_succ hk))
    rw [ih]
    unfold GaussInt.add GaussInt.sub
    ext <;> dsimp only <;> omega

/-- **Real `[BBBV97]` / `[AHU19]` One-Way-to-Hiding (`O2H`) Telescoping Theorem**:
    For ANY `q`-query unitary circuit `A` and ANY two oracles `H, H'` agreeing outside `S`,
    `‖ψ_q^H - ψ_q^{H'}‖² ≤ 4 * q * ∑_{t < q} suffixScale(t) * queryMassOn S (ψ_t^{H'})`,
    where `ψ_t^{H'}` depends ONLY on the reference oracle `H'`! -/
theorem qrom_o2h_telescoping_disturbance_le {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q)
    (H H' : Fin cardX → BitVec w) (S : Fin cardX → Bool)
    (hAgree : ∀ x : Fin cardX, S x = false → H x = H' x) :
    QVec.stateNormSq ((runQuantumAdv A H).sub (runQuantumAdv A H')) ≤
      4 * q * qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn S (advStateAt A H' t.1 (Nat.le_of_lt t.2))) := by
  let V : Fin q → QVec cardX w cardAnc := fun t =>
    (hybridAdv A H H' t.1 (Nat.le_of_lt t.2)).sub (hybridAdv A H H' (t.1 + 1) t.2)
  have hTele : (runQuantumAdv A H).sub (runQuantumAdv A H') =
      (fun x y a => finGaussSum q (fun t => V t x y a)) := by
    rw [← hybridAdv_zero A H H', ← hybridAdv_full A H H']
    funext x y a
    exact (telescope_gauss_sum q (fun k hk => hybridAdv A H H' k hk x y a)).symm
  rw [hTele]
  have hCS := QVec.sumQVec_normSq_le q V
  apply Nat.le_trans hCS
  have hEach : qsum q (fun t => QVec.stateNormSq (V t)) ≤
      qsum q (fun t => 4 * (suffixScale A t.1 (Nat.le_of_lt t.2) *
        QVec.queryMassOn S (advStateAt A H' t.1 (Nat.le_of_lt t.2)))) := by
    apply qsum_le_qsum
    intro t
    dsimp only [V]
    rw [hybridAdv_step_diff, applySuffixFrom_normSq]
    have hDiff := oracleXor_diff_normSq_le H H' S hAgree (advStateAt A H' t.1 (Nat.le_of_lt t.2))
    have hMul := Nat.mul_le_mul_left (suffixScale A t.1 (Nat.le_of_lt t.2)) hDiff
    rw [Nat.mul_left_comm _ 4] at hMul
    exact hMul
  rw [qsum_mul_left 4] at hEach
  have hMulQ := Nat.mul_le_mul_left q hEach
  rw [Nat.mul_left_comm q 4, ← Nat.mul_assoc 4 q] at hMulQ
  exact hMulQ

/-- Reprogram oracle `H` at a single coordinate `xStar` to output `yStar`. -/
def reprogramOracle {cardX w : Nat} (H : Fin cardX → BitVec w)
    (xStar : Fin cardX) (yStar : BitVec w) : Fin cardX → BitVec w :=
  fun x => if x = xStar then yStar else H x

/-- **Uniform Point-Reprogramming O2H Average Disturbance (`≤ 4 q² / M`)**:
    Averaging squared state disturbance over any duplicate-free `M`-element candidate list
    `candidates : List (Fin cardX)` (`M > 0`) bounds the average normalized squared state
    disturbance by `(4 * q ^ 2) / M`. -/
theorem qrom_o2h_average_point_disturbance {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) (yStar : Fin cardX → BitVec w)
    (M : Nat) (hMPos : 0 < M) (cand : Fin M → Fin cardX)
    (hInj : ∀ i j : Fin M, cand i = cand j → i = j) :
    let normFinal := QVec.stateNormSq (runQuantumAdv A H)
    RatBound.le
      ⟨qsum M (fun i =>
        QVec.stateNormSq ((runQuantumAdv A (reprogramOracle H (cand i) (yStar (cand i)))).sub
          (runQuantumAdv A H))),
       M * normFinal,
       Nat.mul_pos hMPos (runQuantumAdv_normSq_pos A H)⟩
      ⟨4 * q ^ 2, M, hMPos⟩ := by
  dsimp only [RatBound.le]
  let normFinal := QVec.stateNormSq (runQuantumAdv A H)
  have hPerI : ∀ i : Fin M,
      QVec.stateNormSq ((runQuantumAdv A (reprogramOracle H (cand i) (yStar (cand i)))).sub
        (runQuantumAdv A H)) ≤
      4 * q * qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) := by
    intro i
    let Si : Fin cardX → Bool := fun x => decide (x = cand i)
    have hAgree : ∀ x : Fin cardX, Si x = false →
        reprogramOracle H (cand i) (yStar (cand i)) x = H x := by
      intro x hx
      unfold reprogramOracle
      have hne : x ≠ cand i := by
        intro heq; simp [Si, heq] at hx
      simp [hne]
    have hO2h := qrom_o2h_telescoping_disturbance_le A
      (reprogramOracle H (cand i) (yStar (cand i))) H Si hAgree
    have hMassEq : ∀ t : Fin q,
        QVec.queryMassOn Si (advStateAt A H t.1 (Nat.le_of_lt t.2)) =
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i) := by
      intro t
      unfold QVec.queryMassOn
      have hCongr : qsum cardX (fun x =>
          if Si x = true then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x else 0) =
          qsum cardX (fun x =>
            if x = cand i then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i) else 0) := by
        apply qsum_congr; intro x
        by_cases hx : x = cand i <;> simp [Si, hx]
      rw [hCongr, qsum_ite_eq]
    have hSumEq : qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn Si (advStateAt A H t.1 (Nat.le_of_lt t.2))) =
        qsum q (fun t =>
          suffixScale A t.1 (Nat.le_of_lt t.2) *
            QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) :=
      qsum_congr (fun t => by rw [hMassEq t])
    rw [hSumEq] at hO2h
    exact hO2h
  have hSumM := qsum_le_qsum hPerI
  rw [qsum_mul_left (4 * q), qsum_comm M q] at hSumM
  have hStepBound : ∀ t : Fin q,
      qsum M (fun i =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) ≤ normFinal := by
    intro t
    rw [qsum_mul_left]
    have hSub : qsum M (fun i => QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) ≤
        QVec.stateNormSq (advStateAt A H t.1 (Nat.le_of_lt t.2)) := by
      unfold QVec.stateNormSq
      have hExpand : qsum M (fun i => QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) =
          qsum cardX (fun x =>
            QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x *
              qsum M (fun i => if x = cand i then 1 else 0)) := by
        have h1 : qsum M (fun i => QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i)) =
            qsum M (fun i => qsum cardX (fun x =>
              if x = cand i then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x else 0)) := by
          apply qsum_congr; intro i
          have hCongrX : qsum cardX (fun x =>
              if x = cand i then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x else 0) =
              qsum cardX (fun x =>
                if x = cand i then QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) (cand i) else 0) := by
            apply qsum_congr; intro x
            by_cases hx : x = cand i
            · rw [hx]
            · simp only [hx, ↓reduceIte]
          rw [hCongrX, qsum_ite_eq]
        rw [h1, qsum_comm]
        apply qsum_congr; intro x
        rw [← qsum_mul_left]
        apply qsum_congr; intro i
        by_cases hx : x = cand i <;> simp [hx]
      rw [hExpand]
      apply qsum_le_qsum; intro x
      have hLe1 : qsum M (fun i => if x = cand i then 1 else 0) ≤ 1 := by
        have hBool : qsum M (fun i => if x = cand i then 1 else 0) =
            qsum M (fun i => if decide (x = cand i) = true then 1 else 0) := by
          apply qsum_congr; intro i; by_cases hx : x = cand i <;> simp [hx]
        rw [hBool]
        exact qsum_le_one_of_subsingleton (fun i => decide (x = cand i)) (fun i j hi hj => by
          have hi' : x = cand i := of_decide_eq_true hi
          have hj' : x = cand j := of_decide_eq_true hj
          exact hInj i j (hi'.symm.trans hj'))
      have hm := Nat.mul_le_mul_left (QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) x) hLe1
      rw [Nat.mul_one] at hm
      exact hm
    have hMulS := Nat.mul_le_mul_left (suffixScale A t.1 (Nat.le_of_lt t.2)) hSub
    apply Nat.le_trans hMulS
    dsimp only [normFinal]
    rw [advStateAt_normSq, runQuantumAdv_normSq, ← Nat.mul_assoc,
        Nat.mul_comm (suffixScale A t.1 (Nat.le_of_lt t.2)),
        prefix_mul_suffix_eq_total A t.1 (Nat.le_of_lt t.2)]
    exact Nat.le_refl _
  have hAllQ := qsum_le_qsum hStepBound
  rw [qsum_const] at hAllQ
  have hBoundTotal : qsum M (fun i =>
      QVec.stateNormSq ((runQuantumAdv A (reprogramOracle H (cand i) (yStar (cand i)))).sub
        (runQuantumAdv A H))) ≤ 4 * q ^ 2 * normFinal := by
    have hMul4 := Nat.mul_le_mul_left (4 * q) hAllQ
    have hPow2 : 4 * q * (q * normFinal) = 4 * q ^ 2 * normFinal := by
      rw [Nat.pow_two]; simp only [Nat.mul_assoc]
    rw [hPow2] at hMul4
    exact Nat.le_trans hSumM hMul4
  have hMulM := Nat.mul_le_mul_right M hBoundTotal
  have hRearr : 4 * q ^ 2 * normFinal * M = 4 * q ^ 2 * (M * normFinal) := by
    rw [Nat.mul_assoc (4 * q ^ 2) normFinal M, Nat.mul_comm normFinal M]
  rw [hRearr] at hMulM
  exact hMulM

/-- **One-Sided Born Probability Disturbance Lemma**:
    For ANY event `E` and ANY two state vectors `ψ, φ`,
    `measureNormSq E ψ ≤ 2 * measureNormSq E φ + 2 * stateNormSq (ψ - φ)`. -/
theorem born_measure_le_two_add_two_dist_sq {cardX w cardAnc : Nat}
    (E : Fin cardX → Bool) (ψ φ : QVec cardX w cardAnc) :
    QVec.measureNormSq E ψ ≤ 2 * QVec.measureNormSq E φ + 2 * QVec.stateNormSq (ψ.sub φ) := by
  have hSubE : QVec.measureNormSq E (ψ.sub φ) ≤ QVec.stateNormSq (ψ.sub φ) :=
    QVec.queryMassOn_le_stateNormSq E (ψ.sub φ)
  have hPoint : QVec.measureNormSq E ψ ≤
      2 * QVec.measureNormSq E φ + 2 * QVec.measureNormSq E (ψ.sub φ) := by
    unfold QVec.measureNormSq QVec.queryMassOn
    rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
    apply qsum_le_qsum; intro x
    cases E x
    · simp
    · simp only [↓reduceIte, QVec.queryWeight, QVec.sub]
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro y
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro a
      have hEq : ψ x y a = GaussInt.add (φ x y a) (GaussInt.sub (ψ x y a) (φ x y a)) := by
        unfold GaussInt.add GaussInt.sub; ext <;> dsimp only <;> omega
      have hLe := GaussInt.normSq_add_le (φ x y a) (GaussInt.sub (ψ x y a) (φ x y a))
      rw [← hEq] at hLe
      exact hLe
  omega

private theorem int_lagrange_identity :
    ∀ (n : Nat) (u0 v0 : Int) (ut vt : Fin n → Int),
      finIntSum n (fun i => (u0 * vt i - v0 * ut i) * (u0 * vt i - v0 * ut i)) =
        u0 * u0 * finIntSum n (fun i => vt i * vt i) +
        v0 * v0 * finIntSum n (fun i => ut i * ut i) -
        2 * u0 * v0 * finIntSum n (fun i => ut i * vt i)
  | 0, u0, v0, _, _ => by
    simp only [finIntSum, Int.mul_zero, Int.add_zero, Int.sub_zero]
  | m + 1, u0, v0, ut, vt => by
    let a1 := ut ⟨0, Nat.zero_lt_succ m⟩
    let b1 := vt ⟨0, Nat.zero_lt_succ m⟩
    let ur : Fin m → Int := fun i => ut ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let vr : Fin m → Int := fun i => vt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have ihm := int_lagrange_identity m u0 v0 ur vr
    have hSq : (u0 * b1 - v0 * a1) * (u0 * b1 - v0 * a1) =
        u0 * u0 * (b1 * b1) + v0 * v0 * (a1 * a1) - 2 * u0 * v0 * (a1 * b1) := by
      have hNegSq : ∀ x : Int, (-x) * (-x) = x * x := fun x => by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      have e1 : (u0 * b1 - v0 * a1) * (u0 * b1 - v0 * a1) =
          (u0 * b1) * (u0 * b1) - 2 * ((u0 * b1) * (v0 * a1)) + (v0 * a1) * (v0 * a1) := by
        rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
            Int.mul_neg, Int.neg_mul, hNegSq, Int.mul_comm (v0 * a1) (u0 * b1)]
        omega
      have p1 : (u0 * b1) * (u0 * b1) = u0 * u0 * (b1 * b1) := by
        rw [Int.mul_assoc u0 b1, Int.mul_left_comm b1 u0 b1, ← Int.mul_assoc u0 u0]
      have p2 : (v0 * a1) * (v0 * a1) = v0 * v0 * (a1 * a1) := by
        rw [Int.mul_assoc v0 a1, Int.mul_left_comm a1 v0 a1, ← Int.mul_assoc v0 v0]
      have p3 : (u0 * b1) * (v0 * a1) = u0 * v0 * (a1 * b1) := by
        rw [Int.mul_assoc u0 b1, Int.mul_left_comm b1 v0 a1,
            ← Int.mul_assoc u0 v0, Int.mul_comm b1 a1]
      have p4 : 2 * (u0 * v0 * (a1 * b1)) = 2 * u0 * v0 * (a1 * b1) := by
        simp only [Int.mul_assoc]
      rw [e1, p1, p2, p3, p4]
      omega
    change (u0 * b1 - v0 * a1) * (u0 * b1 - v0 * a1) +
        finIntSum m (fun i => (u0 * vr i - v0 * ur i) * (u0 * vr i - v0 * ur i)) =
      u0 * u0 * (b1 * b1 + finIntSum m (fun i => vr i * vr i)) +
      v0 * v0 * (a1 * a1 + finIntSum m (fun i => ur i * ur i)) -
      2 * u0 * v0 * (a1 * b1 + finIntSum m (fun i => ur i * vr i))
    rw [hSq, ihm, Int.mul_add, Int.mul_add, Int.mul_add]
    omega

private theorem finIntSum_sq_nonneg :
    ∀ (n : Nat) (f : Fin n → Int), 0 ≤ finIntSum n (fun i => f i * f i)
  | 0, _ => Int.le_refl 0
  | m + 1, f => by
    simp only [finIntSum]
    have h0 := int_sq_nonneg (f ⟨0, Nat.zero_lt_succ m⟩)
    have ht := finIntSum_sq_nonneg m (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

private theorem int_cauchy_schwarz_qsum :
    ∀ (n : Nat) (u v : Fin n → Int),
      (finIntSum n (fun i => u i * v i)) ^ 2 ≤
        finIntSum n (fun i => u i * u i) * finIntSum n (fun i => v i * v i)
  | 0, _, _ => by unfold finIntSum; decide
  | n + 1, u, v => by
    let u0 := u ⟨0, Nat.zero_lt_succ n⟩
    let v0 := v ⟨0, Nat.zero_lt_succ n⟩
    let ut : Fin n → Int := fun i => u ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let vt : Fin n → Int := fun i => v ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have ih := int_cauchy_schwarz_qsum n ut vt
    let A := finIntSum n (fun i => ut i * ut i)
    let B := finIntSum n (fun i => vt i * vt i)
    let C := finIntSum n (fun i => ut i * vt i)
    change (u0 * v0 + C) ^ 2 ≤ (u0 * u0 + A) * (v0 * v0 + B)
    change C ^ 2 ≤ A * B at ih
    have hLagrange :
        finIntSum n (fun i => (u0 * vt i - v0 * ut i) * (u0 * vt i - v0 * ut i)) =
          u0 * u0 * B + v0 * v0 * A - 2 * u0 * v0 * C :=
      int_lagrange_identity n u0 v0 ut vt
    have hNonneg : 0 ≤ finIntSum n
        (fun i => (u0 * vt i - v0 * ut i) * (u0 * vt i - v0 * ut i)) :=
      finIntSum_sq_nonneg n (fun i => u0 * vt i - v0 * ut i)
    have p2 : ∀ x : Int, x ^ 2 = x * x := fun x => by
      change x ^ (1 + 1) = x * x
      rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
    have hSqL : (u0 * v0 + C) ^ 2 = (u0 * v0) * (u0 * v0) + 2 * u0 * v0 * C + C ^ 2 := by
      rw [p2 (u0 * v0 + C), Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm C (u0 * v0), ← p2 C]
      have assoc2 : 2 * (u0 * v0 * C) = 2 * u0 * v0 * C := by simp only [Int.mul_assoc]
      omega
    have hSqR : (u0 * u0 + A) * (v0 * v0 + B) =
        (u0 * v0) * (u0 * v0) + u0 * u0 * B + v0 * v0 * A + A * B := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm A (v0 * v0)]
      have uvEq : (u0 * u0) * (v0 * v0) = (u0 * v0) * (u0 * v0) := by
        rw [Int.mul_assoc u0 u0, Int.mul_left_comm u0 v0 v0, ← Int.mul_assoc u0 v0]
      rw [uvEq]
      omega
    rw [hSqL, hSqR]
    omega

private theorem int_mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact Int.ofNat_le.mpr (Nat.zero_le (m * n))
    | negSucc n => cases hb
  | negSucc m => cases ha

private theorem int_mul_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      exact Int.ofNat_lt.mpr (Nat.mul_pos (Int.ofNat_lt.mp ha) (Int.ofNat_lt.mp hb))
    | negSucc n => cases hb
  | negSucc m => cases ha

private theorem cs_combine_two {a1 b1 c1 a2 b2 c2 : Int}
    (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1) (ha2 : 0 ≤ a2) (hb2 : 0 ≤ b2)
    (h1 : c1 ^ 2 ≤ a1 * b1) (h2 : c2 ^ 2 ≤ a2 * b2) :
    (c1 + c2) ^ 2 ≤ (a1 + a2) * (b1 + b2) := by
  have p2 : ∀ x : Int, x ^ 2 = x * x := fun x => by
    change x ^ (1 + 1) = x * x
    rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  have hProd : c1 ^ 2 * c2 ^ 2 ≤ (a1 * b1) * (a2 * b2) := by
    have hs1 : 0 ≤ (a1 * b1 - c1 ^ 2) * c2 ^ 2 :=
      int_mul_nonneg (by omega) (by rw [p2]; exact int_sq_nonneg c2)
    rw [Int.sub_eq_add_neg, Int.add_mul, Int.neg_mul] at hs1
    have hs2 : 0 ≤ (a1 * b1) * (a2 * b2 - c2 ^ 2) :=
      int_mul_nonneg (int_mul_nonneg ha1 hb1) (by omega)
    rw [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg] at hs2
    omega
  have hAmGm : 4 * ((a1 * b1) * (a2 * b2)) ≤ (a1 * b2 + a2 * b1) ^ 2 := by
    have hDiffSq := int_sq_nonneg (a1 * b2 - a2 * b1)
    rw [p2]
    have idPlus : ∀ u v : Int, (u + v) * (u + v) = u * u + u * v + (v * u + v * v) := fun u v => by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have idMinus : ∀ u v : Int, (u - v) * (u - v) = u * u - u * v - v * u + v * v := fun u v => by
      have hNegSq : (-v) * (-v) = v * v := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
          Int.mul_neg, Int.neg_mul, hNegSq]
      omega
    have id1 : (a1 * b2 + a2 * b1) * (a1 * b2 + a2 * b1) -
        (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1) = 4 * ((a1 * b1) * (a2 * b2)) := by
      rw [idPlus (a1 * b2) (a2 * b1), idMinus (a1 * b2) (a2 * b1)]
      have mEq : (a1 * b2) * (a2 * b1) = (a1 * b1) * (a2 * b2) := by
        rw [Int.mul_assoc a1 b2 (a2 * b1), Int.mul_comm b2 (a2 * b1),
            Int.mul_assoc a2 b1 b2, Int.mul_left_comm a2 b1 b2,
            ← Int.mul_assoc a1 b1 (a2 * b2)]
      have mEq2 : (a2 * b1) * (a1 * b2) = (a1 * b1) * (a2 * b2) := by rw [Int.mul_comm, mEq]
      rw [mEq, mEq2]
      omega
    omega
  have h4L : (2 * c1 * c2) ^ 2 = 4 * (c1 ^ 2 * c2 ^ 2) := by
    rw [p2, p2 c1, p2 c2]
    rw [Int.mul_assoc (2 * c1) c2 (2 * c1 * c2),
        ← Int.mul_assoc c2 (2 * c1) c2,
        Int.mul_comm c2 (2 * c1),
        Int.mul_assoc (2 * c1) c2 c2,
        ← Int.mul_assoc (2 * c1) (2 * c1) (c2 * c2)]
    have h2c : (2 * c1) * (2 * c1) = 4 * (c1 * c1) := by
      rw [Int.mul_assoc 2 c1 (2 * c1), Int.mul_left_comm c1 2 c1,
          ← Int.mul_assoc (2 : Int) 2 (c1 * c1)]
      rfl
    rw [h2c, Int.mul_assoc 4 (c1 * c1) (c2 * c2)]
  have hCrossSq : (2 * c1 * c2) ^ 2 ≤ (a1 * b2 + a2 * b1) ^ 2 := by
    omega
  have hCross : 2 * c1 * c2 ≤ a1 * b2 + a2 * b1 := by
    let u := 2 * c1 * c2
    let v := a1 * b2 + a2 * b1
    have hSN : 0 ≤ v := by
      have pA := int_mul_nonneg ha1 hb2
      have pB := int_mul_nonneg ha2 hb1
      dsimp only [v]; omega
    if hc : u ≤ v then
      exact hc
    else
      exfalso
      have hSqUV : u * u ≤ v * v := by
        change (2 * c1 * c2) * (2 * c1 * c2) ≤ (a1 * b2 + a2 * b1) * (a1 * b2 + a2 * b1)
        rwa [p2, p2] at hCrossSq
      have hPosDiff : 0 < u - v := by omega
      have hPosSum : 0 < u + v := by omega
      have hPosProd : 0 < (u - v) * (u + v) := int_mul_pos hPosDiff hPosSum
      have hDiffSq : (u - v) * (u + v) = u * u - v * v := by
        calc (u - v) * (u + v)
          _ = u * (u + v) - v * (u + v) := Int.sub_mul u v (u + v)
          _ = (u * u + u * v) - (v * u + v * v) := by rw [Int.mul_add u u v, Int.mul_add v u v]
          _ = (u * u + u * v) - (u * v + v * v) := by rw [Int.mul_comm v u]
          _ = u * u - v * v := by omega
      omega
  have expL : (c1 + c2) ^ 2 = c1 ^ 2 + c2 ^ 2 + 2 * c1 * c2 := by
    rw [p2 (c1 + c2), Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm c2 c1, ← p2 c1, ← p2 c2]
    have a2c : 2 * (c1 * c2) = 2 * c1 * c2 := by simp only [Int.mul_assoc]
    omega
  have expR : (a1 + a2) * (b1 + b2) = a1 * b1 + a2 * b2 + (a1 * b2 + a2 * b1) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    omega
  rw [expL, expR]
  omega

/-- **Born-Rule Probability Difference Bound (`(P(ψ) - P(φ))² ≤ 4 ‖ψ‖² ‖ψ - φ‖²`)**:
    For ANY two states `ψ, φ` of equal squared norm `N = stateNormSq ψ = stateNormSq φ` and ANY
    projective measurement event `E`, `(P_E(ψ) - P_E(φ))² ≤ 4 * N * stateNormSq (ψ - φ)`. -/
theorem born_prob_diff_sq_le_four_state_dist_sq {cardX w cardAnc : Nat}
    (E : Fin cardX → Bool) (ψ φ : QVec cardX w cardAnc)
    (hNormEq : QVec.stateNormSq ψ = QVec.stateNormSq φ) :
    ((Int.ofNat (QVec.measureNormSq E ψ) - Int.ofNat (QVec.measureNormSq E φ)) ^ 2) ≤
      Int.ofNat (4 * QVec.stateNormSq ψ * QVec.stateNormSq (ψ.sub φ)) := by
  have hCoordCS :
      ∀ {M : Nat} (z g : Fin M → GaussInt),
        (finIntSum M (fun i => GaussInt.normSqInt (z i) - GaussInt.normSqInt (g i))) ^ 2 ≤
        Int.ofNat (qsum M (fun i => GaussInt.normSq (GaussInt.sub (z i) (g i)))) *
        Int.ofNat (qsum M (fun i => GaussInt.normSq (GaussInt.add (z i) (g i)))) := by
    intro M z g
    induction M with
    | zero => unfold finIntSum; rw [qsum_zero, qsum_zero]; decide
    | succ m ihm =>
      let z0 := z ⟨0, Nat.zero_lt_succ m⟩
      let g0 := g ⟨0, Nat.zero_lt_succ m⟩
      let zt : Fin m → GaussInt := fun i => z ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
      let gt : Fin m → GaussInt := fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
      have ih' := ihm zt gt
      have hBase : (GaussInt.normSqInt z0 - GaussInt.normSqInt g0) ^ 2 ≤
          Int.ofNat (GaussInt.normSq (GaussInt.sub z0 g0)) *
          Int.ofNat (GaussInt.normSq (GaussInt.add z0 g0)) := by
        rw [← GaussInt.normSqInt_eq_ofNat_normSq, ← GaussInt.normSqInt_eq_ofNat_normSq]
        let u2 : Fin 2 → Int := fun i => if i.1 == 0 then z0.re - g0.re else z0.im - g0.im
        let v2 : Fin 2 → Int := fun i => if i.1 == 0 then z0.re + g0.re else z0.im + g0.im
        have cs2 := int_cauchy_schwarz_qsum 2 u2 v2
        have h00 : ((0 : Nat) == 0) = true := rfl
        have h10 : ((0 + 1 : Nat) == 0) = false := rfl
        simp only [finIntSum, u2, v2, h00, h10, Bool.false_eq_true, ↓reduceIte] at cs2
        have hDiff : (z0.re - g0.re) * (z0.re + g0.re) + ((z0.im - g0.im) * (z0.im + g0.im) + 0) =
            GaussInt.normSqInt z0 - GaussInt.normSqInt g0 := by
          unfold GaussInt.normSqInt
          have r1 : (z0.re - g0.re) * (z0.re + g0.re) = z0.re * z0.re - g0.re * g0.re := by
            rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
                Int.neg_mul, Int.neg_mul, Int.mul_comm g0.re z0.re]
            omega
          have r2 : (z0.im - g0.im) * (z0.im + g0.im) = z0.im * z0.im - g0.im * g0.im := by
            rw [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add, Int.mul_add,
                Int.neg_mul, Int.neg_mul, Int.mul_comm g0.im z0.im]
            omega
          rw [r1, r2]
          omega
        rw [hDiff, Int.add_zero, Int.add_zero] at cs2
        exact cs2
      simp only [finIntSum, qsum_succ, ofNat_add_eq]
      exact cs_combine_two (Int.ofNat_le.mpr (Nat.zero_le _)) (Int.ofNat_le.mpr (Nat.zero_le _))
        (Int.ofNat_le.mpr (Nat.zero_le _)) (Int.ofNat_le.mpr (Nat.zero_le _)) hBase ih'
  have liftQsum : ∀ {N : Nat} (A B P Q : Fin N → Nat),
      (∀ i, ((Int.ofNat (P i) - Int.ofNat (Q i)) ^ 2) ≤ Int.ofNat (A i) * Int.ofNat (B i)) →
      ((Int.ofNat (qsum N P) - Int.ofNat (qsum N Q)) ^ 2) ≤
        Int.ofNat (qsum N A) * Int.ofNat (qsum N B) := by
    intro N A B P Q hI
    induction N with
    | zero => simp only [qsum_zero]; decide
    | succ m ihm =>
      simp only [qsum_succ, ofNat_add_eq]
      have hEqDiff : Int.ofNat (P ⟨0, Nat.zero_lt_succ m⟩) +
          Int.ofNat (qsum m (fun i => P ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) -
          (Int.ofNat (Q ⟨0, Nat.zero_lt_succ m⟩) +
           Int.ofNat (qsum m (fun i => Q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))) =
          (Int.ofNat (P ⟨0, Nat.zero_lt_succ m⟩) - Int.ofNat (Q ⟨0, Nat.zero_lt_succ m⟩)) +
          (Int.ofNat (qsum m (fun i => P ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) -
           Int.ofNat (qsum m (fun i => Q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))) := by omega
      rw [hEqDiff]
      exact cs_combine_two (Int.ofNat_le.mpr (Nat.zero_le _)) (Int.ofNat_le.mpr (Nat.zero_le _))
        (Int.ofNat_le.mpr (Nat.zero_le _)) (Int.ofNat_le.mpr (Nat.zero_le _))
        (hI ⟨0, Nat.zero_lt_succ m⟩)
        (ihm _ _ _ _ (fun i => hI ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))
  have hAnc : ∀ x y,
      ((Int.ofNat (qsum cardAnc (fun a => GaussInt.normSq (ψ x y a))) -
        Int.ofNat (qsum cardAnc (fun a => GaussInt.normSq (φ x y a)))) ^ 2) ≤
      Int.ofNat (qsum cardAnc (fun a => GaussInt.normSq (GaussInt.sub (ψ x y a) (φ x y a)))) *
      Int.ofNat (qsum cardAnc (fun a => GaussInt.normSq (GaussInt.add (ψ x y a) (φ x y a)))) := by
    intro x y
    have hDiffEq : ∀ (n : Nat) (z g : Fin n → GaussInt),
        Int.ofNat (qsum n (fun a => GaussInt.normSq (z a))) -
        Int.ofNat (qsum n (fun a => GaussInt.normSq (g a))) =
        finIntSum n (fun a => GaussInt.normSqInt (z a) - GaussInt.normSqInt (g a)) := by
      intro n z g
      induction n with
      | zero => simp [qsum_zero, finIntSum]
      | succ k ihk =>
        simp only [qsum_succ, finIntSum]
        rw [ofNat_add_eq (GaussInt.normSq (z ⟨0, Nat.zero_lt_succ k⟩)),
            ofNat_add_eq (GaussInt.normSq (g ⟨0, Nat.zero_lt_succ k⟩)),
            ← GaussInt.normSqInt_eq_ofNat_normSq (z ⟨0, Nat.zero_lt_succ k⟩),
            ← GaussInt.normSqInt_eq_ofNat_normSq (g ⟨0, Nat.zero_lt_succ k⟩)]
        have ihk' := ihk (fun a => z ⟨a.1 + 1, Nat.succ_lt_succ a.2⟩)
                         (fun a => g ⟨a.1 + 1, Nat.succ_lt_succ a.2⟩)
        omega
    rw [hDiffEq]
    exact hCoordCS (ψ x y) (φ x y)
  have hY : ∀ x,
      ((Int.ofNat (QVec.queryWeight ψ x) - Int.ofNat (QVec.queryWeight φ x)) ^ 2) ≤
      Int.ofNat (QVec.queryWeight (ψ.sub φ) x) * Int.ofNat (QVec.queryWeight (ψ.add φ) x) := by
    intro x
    exact liftQsum _ _ _ _ (hAnc x)
  have hMeas :
      ((Int.ofNat (QVec.measureNormSq E ψ) - Int.ofNat (QVec.measureNormSq E φ)) ^ 2) ≤
      Int.ofNat (QVec.measureNormSq E (ψ.sub φ)) * Int.ofNat (QVec.measureNormSq E (ψ.add φ)) := by
    apply liftQsum
    intro x
    cases E x
    · simp only [Bool.false_eq_true, ↓reduceIte]; decide
    · simp only [↓reduceIte]; exact hY x
  have hSubLe : QVec.measureNormSq E (ψ.sub φ) ≤ QVec.stateNormSq (ψ.sub φ) :=
    QVec.queryMassOn_le_stateNormSq E (ψ.sub φ)
  have hAddLe : QVec.measureNormSq E (ψ.add φ) ≤ 4 * QVec.stateNormSq ψ := by
    have h1 : QVec.measureNormSq E (ψ.add φ) ≤ QVec.stateNormSq (ψ.add φ) :=
      QVec.queryMassOn_le_stateNormSq E (ψ.add φ)
    have h2 : QVec.stateNormSq (ψ.add φ) ≤ 2 * QVec.stateNormSq ψ + 2 * QVec.stateNormSq φ := by
      unfold QVec.stateNormSq QVec.queryWeight QVec.add
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro x
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro y
      rw [← qsum_mul_left 2, ← qsum_mul_left 2, ← qsum_add]
      apply qsum_le_qsum; intro a
      exact GaussInt.normSq_add_le _ _
    omega
  have hProdNat : QVec.measureNormSq E (ψ.sub φ) * QVec.measureNormSq E (ψ.add φ) ≤
      4 * QVec.stateNormSq ψ * QVec.stateNormSq (ψ.sub φ) := by
    have hp := Nat.mul_le_mul hSubLe hAddLe
    exact Nat.le_trans hp (Nat.le_of_eq (Nat.mul_comm _ _))
  rw [← ofNat_mul_eq] at hMeas
  exact Int.le_trans hMeas (Int.ofNat_le.mpr hProdNat)

/-! ### §2.4 Protocol-Coupled QROM & Classical Adaptive Fiber-Search Theorems -/

/-- Exact preimage fiber cardinality `|{ d ∈ BitVec n | encode d = target }|`. -/
def fiberCard {Code : Type} [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) : Nat :=
  qsum (2 ^ n) (fun j => if encode (BitVec.ofFin j) = target then 1 else 0)

/-- Any injective protocol digest encoding `encode : BitVec n → Code` has fiber cardinality `≤ 1`
    at every target codeword. -/
theorem fiberCard_le_one_of_injective {Code : Type} [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (hInj : Function.Injective encode) (target : Code) :
    fiberCard n encode target ≤ 1 := by
  unfold fiberCard
  have hBool : qsum (2 ^ n) (fun j => if encode (BitVec.ofFin j) = target then 1 else 0) =
      qsum (2 ^ n) (fun j => if decide (encode (BitVec.ofFin j) = target) = true then 1 else 0) := by
    apply qsum_congr; intro j
    by_cases h : encode (BitVec.ofFin j) = target <;> simp [h]
  rw [hBool]
  apply qsum_le_one_of_subsingleton
  intro i j hi hj
  have hi' : encode (BitVec.ofFin i) = target := of_decide_eq_true hi
  have hj' : encode (BitVec.ofFin j) = target := of_decide_eq_true hj
  have hEqBv : BitVec.ofFin i = BitVec.ofFin j := hInj (hi'.trans hj'.symm)
  exact congrArg BitVec.toFin hEqBv

/-- XOR-shifted indicator oracle `O_Δ` marking `x : Fin (2 ^ n)` with `1#(w + 1)` iff
    `encode (x ⊕ Δ) = target`. -/
def shiftedFiberOracle {Code : Type} [DecidableEq Code]
    (n w : Nat) (encode : BitVec n → Code) (target : Code) (mask : BitVec n) :
    Fin (2 ^ n) → BitVec (w + 1) :=
  fun x => if encode (BitVec.ofFin x ^^^ mask) = target then 1#(w + 1) else 0#(w + 1)

/-- Blank reference oracle returning `0#(w + 1)` on every query. -/
def blankFiberOracle (n w : Nat) : Fin (2 ^ n) → BitVec (w + 1) :=
  fun _ => 0#(w + 1)

private theorem sum_masks_shifted_fiber {Code : Type} [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) (weight : Fin (2 ^ n) → Nat) :
    qsum (2 ^ n) (fun m =>
      qsum (2 ^ n) (fun x =>
        if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target then weight x else 0)) =
      fiberCard n encode target * qsum (2 ^ n) weight := by
  rw [qsum_comm]
  have hInner : ∀ x : Fin (2 ^ n),
      qsum (2 ^ n) (fun m =>
        if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target then weight x else 0) =
      weight x * fiberCard n encode target := by
    intro x
    have hFactor : qsum (2 ^ n) (fun m =>
        if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target then weight x else 0) =
        weight x * qsum (2 ^ n) (fun m =>
          if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target then 1 else 0) := by
      rw [← qsum_mul_left]
      apply qsum_congr; intro m
      by_cases h : encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target <;> simp [h]
    rw [hFactor]
    congr 1
    let π : Fin (2 ^ n) → Fin (2 ^ n) := fun m => (BitVec.ofFin x ^^^ BitVec.ofFin m).toFin
    have hInv : ∀ m : Fin (2 ^ n), π (π m) = m := by
      intro m
      dsimp only [π]
      rw [BitVec.ofFin_toFin]
      have hX : BitVec.ofFin x ^^^ (BitVec.ofFin x ^^^ BitVec.ofFin m) = BitVec.ofFin m := by
        apply BitVec.eq_of_getLsbD_eq; intro i _
        simp only [BitVec.getLsbD_xor]
        cases (BitVec.ofFin x).getLsbD i <;> cases (BitVec.ofFin m).getLsbD i <;> rfl
      rw [hX, BitVec.toFin_ofFin]
    have hPerm := qsum_involutive π hInv
      (fun z => if encode (BitVec.ofFin z) = target then 1 else 0)
    unfold fiberCard
    rw [← hPerm]
  rw [qsum_congr hInner, qsum_mul_right, Nat.mul_comm]

/-- **Protocol-Coupled Unitary QROM Fiber-Search Theorem (`qrom_fiber_search_bound`)**:
    For ANY `q`-query unitary quantum adversary `A` (`QuantumAdv (2 ^ n) (w + 1) cardAnc q`) and
    ANY protocol digest map `encode : BitVec n → Code`, the Born-rule success probability of
    finding `x` in `target`'s preimage fiber (averaged over `2 ^ n` keyed/tweaked masks `Δ`) is
    bounded by `((8 * q ^ 2 + 2) * fiberCard n encode target) / 2 ^ n`, and hence by
    `8 * (q + 1) ^ 2 * fiberCard n encode target / 2 ^ n`! -/
theorem qrom_fiber_search_bound {Code : Type} [DecidableEq Code]
    {n w cardAnc q : Nat}
    (A : QuantumAdv (2 ^ n) (w + 1) cardAnc q)
    (encode : BitVec n → Code) (target : Code) :
    let normFinal := QVec.stateNormSq (runQuantumAdv A (blankFiberOracle n w))
    let avgBornSuccess : RatBound :=
      ⟨qsum (2 ^ n) (fun m =>
         QVec.measureNormSq
           (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
           (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m)))),
       2 ^ n * normFinal,
       Nat.mul_pos (Nat.two_pow_pos n) (runQuantumAdv_normSq_pos A (blankFiberOracle n w))⟩
    RatBound.le avgBornSuccess
      ⟨(8 * q ^ 2 + 2) * fiberCard n encode target, 2 ^ n, Nat.two_pow_pos n⟩ ∧
    RatBound.le avgBornSuccess
      ⟨8 * (q + 1) ^ 2 * fiberCard n encode target, 2 ^ n, Nat.two_pow_pos n⟩ := by
  let normFinal := QVec.stateNormSq (runQuantumAdv A (blankFiberOracle n w))
  let ψBlank := runQuantumAdv A (blankFiberOracle n w)
  let K := fiberCard n encode target
  have hPerMask : ∀ m : Fin (2 ^ n),
      let Sm : Fin (2 ^ n) → Bool :=
        fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target)
      QVec.measureNormSq Sm
        (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m))) ≤
      2 * QVec.measureNormSq Sm ψBlank +
      8 * q * qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn Sm (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2))) := by
    intro m
    let Sm : Fin (2 ^ n) → Bool :=
      fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target)
    have hBorn := born_measure_le_two_add_two_dist_sq Sm
      (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m))) ψBlank
    have hAgree : ∀ x : Fin (2 ^ n), Sm x = false →
        shiftedFiberOracle n w encode target (BitVec.ofFin m) x = blankFiberOracle n w x := by
      intro x hx
      unfold shiftedFiberOracle blankFiberOracle
      have hne : encode (BitVec.ofFin x ^^^ BitVec.ofFin m) ≠ target := by
        intro heq; simp [Sm, heq] at hx
      simp [hne]
    have hO2h := qrom_o2h_telescoping_disturbance_le A
      (shiftedFiberOracle n w encode target (BitVec.ofFin m)) (blankFiberOracle n w) Sm hAgree
    have h2 := Nat.mul_le_mul_left 2 hO2h
    rw [← Nat.mul_assoc 2 (4 * q), show 2 * (4 * q) = 8 * q by omega] at h2
    exact Nat.le_trans hBorn (Nat.add_le_add_left h2 _)
  have hSumMasks := qsum_le_qsum hPerMask
  rw [qsum_add, qsum_mul_left 2, qsum_mul_left (8 * q), qsum_comm (2 ^ n) q] at hSumMasks
  have hBlankTerm :
      qsum (2 ^ n) (fun m =>
        QVec.measureNormSq (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target)) ψBlank) =
      K * normFinal := by
    unfold QVec.measureNormSq QVec.queryMassOn
    have hRewrite : qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
        if decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target) = true
        then QVec.queryWeight ψBlank x else 0)) =
        qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
          if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target
          then QVec.queryWeight ψBlank x else 0)) := by
      apply qsum_congr; intro m; apply qsum_congr; intro x
      by_cases h : encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target <;> simp [h]
    rw [hRewrite, sum_masks_shifted_fiber]
    rfl
  have hQueryTerms :
      qsum q (fun t => qsum (2 ^ n) (fun m =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
            (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)))) =
      q * (K * normFinal) := by
    have hEachT : ∀ t : Fin q,
        qsum (2 ^ n) (fun m =>
          suffixScale A t.1 (Nat.le_of_lt t.2) *
            QVec.queryMassOn (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
              (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2))) =
        K * normFinal := by
      intro t
      rw [qsum_mul_left]
      unfold QVec.queryMassOn
      have hRew : qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
          if decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target) = true
          then QVec.queryWeight (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)) x else 0)) =
          K * QVec.stateNormSq (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)) := by
        have h1 : qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
            if decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target) = true
            then QVec.queryWeight (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)) x else 0)) =
            qsum (2 ^ n) (fun m => qsum (2 ^ n) (fun x =>
              if encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target
              then QVec.queryWeight (advStateAt A (blankFiberOracle n w) t.1 (Nat.le_of_lt t.2)) x else 0)) := by
          apply qsum_congr; intro m; apply qsum_congr; intro x
          by_cases h : encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target <;> simp [h]
        rw [h1, sum_masks_shifted_fiber]
        rfl
      rw [hRew, advStateAt_normSq]
      dsimp only [normFinal]
      rw [runQuantumAdv_normSq]
      have hScale := prefix_mul_suffix_eq_total A t.1 (Nat.le_of_lt t.2)
      calc suffixScale A t.1 (Nat.le_of_lt t.2) *
             (K * (prefixScale A t.1 (Nat.le_of_lt t.2) * QVec.stateNormSq A.init))
        _ = K * ((prefixScale A t.1 (Nat.le_of_lt t.2) * suffixScale A t.1 (Nat.le_of_lt t.2)) *
                 QVec.stateNormSq A.init) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (suffixScale A t.1 (Nat.le_of_lt t.2)) K,
              Nat.mul_assoc K, ← Nat.mul_assoc (suffixScale A t.1 (Nat.le_of_lt t.2)),
              Nat.mul_comm (suffixScale A t.1 (Nat.le_of_lt t.2))]
        _ = K * (prefixScale A q (Nat.le_refl q) * QVec.stateNormSq A.init) := by rw [hScale]
    rw [qsum_congr hEachT, qsum_const]
  rw [hBlankTerm, hQueryTerms] at hSumMasks
  have hTight : qsum (2 ^ n) (fun m =>
      QVec.measureNormSq
        (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
        (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m)))) ≤
      (8 * q ^ 2 + 2) * K * normFinal := by
    have hAlg : 2 * (K * normFinal) + 8 * q * (q * (K * normFinal)) =
        (8 * q ^ 2 + 2) * K * normFinal := by
      rw [Nat.pow_two, Nat.add_mul, Nat.add_mul, Nat.add_comm]
      simp only [Nat.mul_assoc]
    rw [hAlg] at hSumMasks
    exact hSumMasks
  have hFirst : RatBound.le
      ⟨qsum (2 ^ n) (fun m =>
         QVec.measureNormSq
           (fun x => decide (encode (BitVec.ofFin x ^^^ BitVec.ofFin m) = target))
           (runQuantumAdv A (shiftedFiberOracle n w encode target (BitVec.ofFin m)))),
       2 ^ n * normFinal,
       Nat.mul_pos (Nat.two_pow_pos n) (runQuantumAdv_normSq_pos A (blankFiberOracle n w))⟩
      ⟨(8 * q ^ 2 + 2) * K, 2 ^ n, Nat.two_pow_pos n⟩ := by
    unfold RatBound.le
    dsimp only
    have hm := Nat.mul_le_mul_right (2 ^ n) hTight
    have hR : (8 * q ^ 2 + 2) * K * normFinal * 2 ^ n =
        (8 * q ^ 2 + 2) * K * (2 ^ n * normFinal) := by
      rw [Nat.mul_assoc ((8 * q ^ 2 + 2) * K) normFinal (2 ^ n), Nat.mul_comm normFinal (2 ^ n)]
    rw [hR] at hm
    exact hm
  refine ⟨hFirst, RatBound.le_trans hFirst ?_⟩
  unfold RatBound.le
  dsimp only
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_right
  have hSq : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  rw [hSq, Nat.mul_add, Nat.mul_add]
  omega

/-! ### §2.5 Classical Adaptive `OracleComp` Lazy-RO Fiber-Search Theorem -/

/-- Lookup a previously queried input `x` inside a lazy random-oracle transcript. -/
def lookupLazyRo {Dom Val : Type} [DecidableEq Dom] : List (Dom × Val) → Dom → Option Val
  | [], _ => none
  | (k, v) :: rest, x => if x = k then some v else lookupLazyRo rest x

/-- Exact integer-scaled hitting count (denominator `(2 ^ n) ^ (q + 1)`) of an adaptive height-`q`
    `OracleComp Dom (BitVec n) Dom` adversary over a uniform lazy random oracle trying to output
    `m' ≠ mSigned` with `encode (H m') = target`. -/
def lazyRoScaledHits {Dom Code : Type} [DecidableEq Dom] [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) (mSigned : Dom) :
    Nat → List (Dom × BitVec n) → OracleComp Dom (BitVec n) Dom → Nat
  | 0, hist, .pure mOut =>
    if mOut = mSigned then 0
    else match lookupLazyRo hist mOut with
      | some d => if encode d = target then 2 ^ n else 0
      | none => fiberCard n encode target
  | 0, _, .query _ _ => 0
  | q + 1, hist, .pure mOut =>
    2 ^ n * lazyRoScaledHits n encode target mSigned q hist (.pure mOut)
  | q + 1, hist, .query x next =>
    match lookupLazyRo hist x with
    | some d => 2 ^ n * lazyRoScaledHits n encode target mSigned q hist (next d)
    | none =>
      qsum (2 ^ n) (fun j =>
        lazyRoScaledHits n encode target mSigned q
          ((x, BitVec.ofFin j) :: hist) (next (BitVec.ofFin j)))

private theorem fiberCard_le_two_pow {Code : Type} [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) :
    fiberCard n encode target ≤ 2 ^ n := by
  unfold fiberCard
  have h1 : qsum (2 ^ n) (fun j => if encode (BitVec.ofFin j) = target then 1 else 0) ≤
      qsum (2 ^ n) (fun _ => 1) := by
    apply qsum_le_qsum; intro j
    by_cases h : encode (BitVec.ofFin j) = target <;> simp [h]
  rw [qsum_const, Nat.mul_one] at h1
  exact h1

private theorem lazyRoScaledHits_le_full {Dom Code : Type} [DecidableEq Dom] [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) (mSigned : Dom) :
    ∀ (q : Nat) (hist : List (Dom × BitVec n)) (prog : OracleComp Dom (BitVec n) Dom),
      lazyRoScaledHits n encode target mSigned q hist prog ≤ (2 ^ n) ^ (q + 1)
  | 0, hist, .pure mOut => by
    simp only [lazyRoScaledHits]
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    split
    · exact Nat.zero_le _
    · split
      · split
        · exact Nat.le_refl _
        · exact Nat.zero_le _
      · exact fiberCard_le_two_pow n encode target
  | 0, _, .query _ _ => Nat.zero_le _
  | q + 1, hist, .pure mOut => by
    simp only [lazyRoScaledHits]
    have ih := lazyRoScaledHits_le_full n encode target mSigned q hist (.pure mOut)
    rw [Nat.pow_succ _ (q + 1), Nat.mul_comm ((2 ^ n) ^ (q + 1)) (2 ^ n)]
    exact Nat.mul_le_mul_left (2 ^ n) ih
  | q + 1, hist, .query x next => by
    simp only [lazyRoScaledHits]
    split
    · rename_i d _
      have ih := lazyRoScaledHits_le_full n encode target mSigned q hist (next d)
      rw [Nat.pow_succ _ (q + 1), Nat.mul_comm ((2 ^ n) ^ (q + 1)) (2 ^ n)]
      exact Nat.mul_le_mul_left (2 ^ n) ih
    · have hEach : ∀ j : Fin (2 ^ n),
          lazyRoScaledHits n encode target mSigned q
            ((x, BitVec.ofFin j) :: hist) (next (BitVec.ofFin j)) ≤ (2 ^ n) ^ (q + 1) :=
        fun j => lazyRoScaledHits_le_full n encode target mSigned q _ _
      have hSum := qsum_le_qsum hEach
      rw [qsum_const, Nat.pow_succ _ (q + 1), Nat.mul_comm ((2 ^ n) ^ (q + 1)) (2 ^ n)] at *
      exact hSum

private theorem lazyRo_step_prod (N q K : Nat) :
    N * ((q + 1) * K * N ^ q) = (q + 1) * (K * N ^ (q + 1)) := by
  calc N * ((q + 1) * K * N ^ q)
    _ = (N * ((q + 1) * K)) * N ^ q := (Nat.mul_assoc _ _ _).symm
    _ = (((q + 1) * K) * N) * N ^ q := by rw [Nat.mul_comm N ((q + 1) * K)]
    _ = ((q + 1) * K) * (N * N ^ q) := Nat.mul_assoc _ _ _
    _ = (q + 1) * (K * (N ^ q * N)) := by rw [Nat.mul_comm N (N ^ q), Nat.mul_assoc (q + 1)]
    _ = (q + 1) * (K * N ^ (q + 1)) := by rw [← Nat.pow_succ N q]

private theorem lazyRo_step_le (N q K : Nat) :
    N * ((q + 1) * K * N ^ q) ≤ (q + 2) * K * N ^ (q + 1) := by
  rw [lazyRo_step_prod, Nat.mul_assoc (q + 2) K (N ^ (q + 1))]
  exact Nat.mul_le_mul_right (K * N ^ (q + 1)) (by omega)

private theorem lazyRo_step_eq (N q K : Nat) :
    K * N ^ (q + 1) + N * ((q + 1) * K * N ^ q) = (q + 2) * K * N ^ (q + 1) := by
  rw [lazyRo_step_prod, Nat.mul_assoc (q + 2) K (N ^ (q + 1))]
  have h1 : q + 2 = 1 + (q + 1) := by omega
  rw [h1, Nat.add_mul 1 (q + 1) (K * N ^ (q + 1)), Nat.one_mul]

private theorem lazyRoScaledHits_bound_aux {Dom Code : Type} [DecidableEq Dom] [DecidableEq Code]
    (n : Nat) (encode : BitVec n → Code) (target : Code) (mSigned : Dom) :
    ∀ (q : Nat) (hist : List (Dom × BitVec n)) (prog : OracleComp Dom (BitVec n) Dom),
      QueryBounded q prog →
      (∀ x d, lookupLazyRo hist x = some d → x ≠ mSigned → encode d ≠ target) →
      lazyRoScaledHits n encode target mSigned q hist prog ≤
        (q + 1) * fiberCard n encode target * (2 ^ n) ^ q
  | 0, hist, .pure mOut, _, hClean => by
    simp only [lazyRoScaledHits, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.one_mul]
    split
    · exact Nat.zero_le _
    · rename_i hNe
      split
      · rename_i d hLk
        have hNot := hClean mOut d hLk hNe
        simp [hNot]
      · exact Nat.le_refl _
  | 0, _, .query _ _, hQB, _ => False.elim hQB
  | q + 1, hist, .pure mOut, _, hClean => by
    simp only [lazyRoScaledHits]
    have hQBPure : QueryBounded q (OracleComp.pure mOut : OracleComp Dom (BitVec n) Dom) := by
      cases q <;> exact trivial
    have ih := lazyRoScaledHits_bound_aux n encode target mSigned q hist (.pure mOut) hQBPure hClean
    exact Nat.le_trans (Nat.mul_le_mul_left (2 ^ n) ih)
      (lazyRo_step_le (2 ^ n) q (fiberCard n encode target))
  | q + 1, hist, .query x next, hQB, hClean => by
    simp only [lazyRoScaledHits]
    split
    · rename_i d _
      have ih := lazyRoScaledHits_bound_aux n encode target mSigned q hist (next d) (hQB d) hClean
      exact Nat.le_trans (Nat.mul_le_mul_left (2 ^ n) ih)
        (lazyRo_step_le (2 ^ n) q (fiberCard n encode target))
    · by_cases hxSigned : x = mSigned
      · have hEach : ∀ j : Fin (2 ^ n),
            lazyRoScaledHits n encode target mSigned q
              ((x, BitVec.ofFin j) :: hist) (next (BitVec.ofFin j)) ≤
            (q + 1) * fiberCard n encode target * (2 ^ n) ^ q := by
          intro j
          apply lazyRoScaledHits_bound_aux n encode target mSigned q _ _ (hQB _)
          intro y dy hyLk hyNe
          simp only [lookupLazyRo] at hyLk
          split at hyLk
          · rename_i hyx
            exact False.elim (hyNe (hyx.trans hxSigned))
          · exact hClean y dy hyLk hyNe
        have hSum := qsum_le_qsum hEach
        rw [qsum_const] at hSum
        exact Nat.le_trans hSum (lazyRo_step_le (2 ^ n) q (fiberCard n encode target))
      · have hPoint : ∀ j : Fin (2 ^ n),
            lazyRoScaledHits n encode target mSigned q
              ((x, BitVec.ofFin j) :: hist) (next (BitVec.ofFin j)) ≤
            (if encode (BitVec.ofFin j) = target then (2 ^ n) ^ (q + 1) else 0) +
            (q + 1) * fiberCard n encode target * (2 ^ n) ^ q := by
          intro j
          by_cases hHit : encode (BitVec.ofFin j) = target
          · simp only [hHit, ↓reduceIte]
            exact Nat.le_trans (lazyRoScaledHits_le_full n encode target mSigned q _ _)
              (Nat.le_add_right _ _)
          · simp only [hHit, ↓reduceIte, Nat.zero_add]
            apply lazyRoScaledHits_bound_aux n encode target mSigned q _ _ (hQB _)
            intro y dy hyLk hyNe
            simp only [lookupLazyRo] at hyLk
            split at hyLk
            · injection hyLk with hEqD
              subst hEqD
              exact hHit
            · exact hClean y dy hyLk hyNe
        have hSum := qsum_le_qsum hPoint
        rw [qsum_add, qsum_const] at hSum
        have hFirst : qsum (2 ^ n) (fun j =>
            if encode (BitVec.ofFin j) = target then (2 ^ n) ^ (q + 1) else 0) =
            fiberCard n encode target * (2 ^ n) ^ (q + 1) := by
          have hRew : qsum (2 ^ n) (fun j =>
              if encode (BitVec.ofFin j) = target then (2 ^ n) ^ (q + 1) else 0) =
              qsum (2 ^ n) (fun j =>
                (if encode (BitVec.ofFin j) = target then 1 else 0) * (2 ^ n) ^ (q + 1)) := by
            apply qsum_congr; intro j
            by_cases h : encode (BitVec.ofFin j) = target <;> simp [h]
          rw [hRew, qsum_mul_right]
          rfl
        rw [hFirst, lazyRo_step_eq (2 ^ n) q (fiberCard n encode target)] at hSum
        exact hSum

/-- **Protocol-Coupled Classical Lazy-RO Adaptive Query Theorem (`classical_lazy_ro_fiber_search_bound`)**:
    For ANY adaptive `OracleComp Dom (BitVec n) Dom` adversary `prog` making at most `q` random-oracle
    queries (given `(mSigned, dSigned)` with `encode dSigned = target`), its exact lazy-RO probability
    of outputting `m' ≠ mSigned` with `encode (H m') = target` is bounded by
    `((q + 1) * fiberCard n encode target) / 2 ^ n`. -/
theorem classical_lazy_ro_fiber_search_bound {Dom Code : Type} [DecidableEq Dom] [DecidableEq Code]
    (n q : Nat) (encode : BitVec n → Code) (mSigned : Dom) (dSigned : BitVec n)
    (prog : OracleComp Dom (BitVec n) Dom) (hQB : QueryBounded q prog) :
    let target := encode dSigned
    let lazyProb : RatBound :=
      ⟨lazyRoScaledHits n encode target mSigned q [(mSigned, dSigned)] prog,
       (2 ^ n) ^ (q + 1),
       Nat.pow_pos (Nat.two_pow_pos n)⟩
    RatBound.le lazyProb
      ⟨(q + 1) * fiberCard n encode target, 2 ^ n, Nat.two_pow_pos n⟩ := by
  dsimp only [RatBound.le]
  have hClean : ∀ x d, lookupLazyRo [(mSigned, dSigned)] x = some d →
      x ≠ mSigned → encode d ≠ encode dSigned := by
    intro x d hLk hNe
    simp only [lookupLazyRo] at hLk
    split at hLk
    · rename_i hx; exact False.elim (hNe hx)
    · cases hLk
  have hAux := lazyRoScaledHits_bound_aux n encode (encode dSigned) mSigned q
    [(mSigned, dSigned)] prog hQB hClean
  have hMul := Nat.mul_le_mul_right (2 ^ n) hAux
  rw [Nat.mul_assoc ((q + 1) * fiberCard n encode (encode dSigned)) ((2 ^ n) ^ q) (2 ^ n),
      ← Nat.pow_succ] at hMul
  exact hMul

/-! ### §2.6 Multi-Target `ADRS` Domain Separation, Quantum BHT Collisions & Fiat–Shamir Bounds -/

/-- Exact QROM single-target (`M = 1`) vs `M`-target Zhandry/Grover preimage bound over `n` bits. -/
def quantumZhandryMultiTargetBound (n M qHash : Nat) : RatBound :=
  ⟨8 * M * (qHash + 1) ^ 2, 2 ^ n, Nat.two_pow_pos n⟩

def quantumGroverSingleTargetBound (n qHash : Nat) : RatBound :=
  quantumZhandryMultiTargetBound n 1 qHash

/-- Pure Grover query-scale bound `qHash ^ 2 / 2 ^ n` (without constant reduction overhead). -/
def groverPureSearchBound (n qHash : Nat) : RatBound :=
  ⟨qHash ^ 2, 2 ^ n, Nat.two_pow_pos n⟩

/-- Classical birthday collision bound `(qHash + 1) ^ 2 / 2 ^ n`. -/
def classicalBirthdayCollisionBound (n qHash : Nat) : RatBound :=
  ⟨(qHash + 1) ^ 2, 2 ^ n, Nat.two_pow_pos n⟩

/-- Quantum Brassard–Høyer–Tapp (`BHT`) / Chailloux–Naya-Plasencia–Schrottenloher (`CNS`) QROM
    unrestricted collision bound `8 * (qHash + 1) ^ 3 / 2 ^ n` (and pure cubic `qHash ^ 3 / 2 ^ n`). -/
def quantumBhtCollisionBound (n qHash : Nat) : RatBound :=
  ⟨8 * (qHash + 1) ^ 3, 2 ^ n, Nat.two_pow_pos n⟩

def quantumBhtPureCubicBound (n qHash : Nat) : RatBound :=
  ⟨qHash ^ 3, 2 ^ n, Nat.two_pow_pos n⟩

/-- Classical Fiat–Shamir single-challenge grinding bound `(qHash + 1) * pErr`. -/
def classicalFiatShamirBound (qHash : Nat) (pErr : RatBound) : RatBound :=
  RatBound.scale (qHash + 1) pErr

/-- Quantum Fiat–Shamir offline Grover grinding bound `8 * (qHash + 1) ^ 2 * pErr` (matching
    `qrom_fiber_search_bound` on bad-challenge fibers!). -/
def quantumGroverGrindingBound (qHash : Nat) (pErr : RatBound) : RatBound :=
  RatBound.scale (8 * (qHash + 1) ^ 2) pErr

/-- Don–Fehr–Majenz (`[DFM20]`) QROM Measure-and-Reprogram bound `(2 * qHash + 1) ^ (2 * mu) * pErr`
    for a `(2 * mu + 1)`-move public-coin interactive argument with `mu` challenge rounds. -/
def quantumDfmMeasureReprogramBound (mu qHash : Nat) (pErr : RatBound) : RatBound :=
  RatBound.scale ((2 * qHash + 1) ^ (2 * mu)) pErr

/-- **Unitary O2H Justification of Quantum Fiat–Shamir Grinding**:
    Offline quantum grinding by ANY `qHash`-query unitary circuit `A` over an `n`-bit transcript
    challenge space where bad challenges satisfy `acceptBad : BitVec n → Bool` (`pErr = K / 2^n`)
    is bounded directly by `quantumGroverGrindingBound qHash pErr` via `qrom_fiber_search_bound`! -/
theorem quantum_fs_grover_grinding_from_o2h {n w cardAnc qHash : Nat}
    (A : QuantumAdv (2 ^ n) (w + 1) cardAnc qHash) (acceptBad : BitVec n → Bool) :
    let normFinal := QVec.stateNormSq (runQuantumAdv A (blankFiberOracle n w))
    let pErr : RatBound := ⟨fiberCard n acceptBad true, 2 ^ n, Nat.two_pow_pos n⟩
    RatBound.le
      ⟨qsum (2 ^ n) (fun m =>
         QVec.measureNormSq
           (fun x => decide (acceptBad (BitVec.ofFin x ^^^ BitVec.ofFin m) = true))
           (runQuantumAdv A (shiftedFiberOracle n w acceptBad true (BitVec.ofFin m)))),
       2 ^ n * normFinal,
       Nat.mul_pos (Nat.two_pow_pos n) (runQuantumAdv_normSq_pos A (blankFiberOracle n w))⟩
      (quantumGroverGrindingBound qHash pErr) :=
  (qrom_fiber_search_bound A acceptBad true).2

/-- **`ADRS` Domain-Separation Multi-Target Reduction (`M = 1`)**:
    Binding distinct `(pkSeed, layer, tree, kind, keyPair, chainIdx, hashStep)` 32-byte `HashAdrs`
    tweaks per one-time chain step isolates each target preimage (`M = 1`), whereas sharing an
    untweaked oracle across `M ≥ 2` signatures incurs a strict `M`-fold multi-target loss. -/
theorem adrs_tweak_reduces_multitarget_to_single_target (n qHash : Nat) :
    quantumZhandryMultiTargetBound n 1 qHash = quantumGroverSingleTargetBound n qHash ∧
    (∀ M : Nat, 2 ≤ M →
      RatBound.lt (quantumGroverSingleTargetBound n qHash)
                  (quantumZhandryMultiTargetBound n M qHash)) := by
  refine ⟨rfl, ?_⟩
  intro M hM
  unfold RatBound.lt quantumGroverSingleTargetBound quantumZhandryMultiTargetBound
  dsimp only
  have hPosSq : 0 < (qHash + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos qHash)
  have hPosPow : 0 < 2 ^ n := Nat.two_pow_pos n
  have hLt8 : 8 * 1 < 8 * M := by omega
  have hLtNum : 8 * 1 * (qHash + 1) ^ 2 < 8 * M * (qHash + 1) ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hLt8 hPosSq
  exact Nat.mul_lt_mul_of_pos_right hLtNum hPosPow

/-- Parametric QROM bit-margin theorem: for `qHash + 1 ≤ 2 ^ k` and `2 * k + 3 + b ≤ n`,
    `quantumGroverSingleTargetBound n qHash` achieves `atLeastBits b`. -/
theorem qrom_single_target_parametric_bits {n k b qHash : Nat}
    (hq : qHash + 1 ≤ 2 ^ k) (hWidth : 2 * k + 3 + b ≤ n) :
    atLeastBits b (quantumGroverSingleTargetBound n qHash) := by
  unfold atLeastBits quantumGroverSingleTargetBound quantumZhandryMultiTargetBound
  dsimp only
  have hSq : (qHash + 1) ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hq 2
  rw [← Nat.pow_mul, Nat.mul_comm k 2] at hSq
  have h8 : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 3 * 2 ^ (2 * k) := Nat.mul_le_mul_left 8 hSq
  rw [← Nat.pow_add, Nat.add_comm 3 (2 * k)] at h8
  have hMulB := Nat.mul_le_mul_right (2 ^ b) h8
  rw [← Nat.pow_add] at hMulB
  exact Nat.le_trans hMulB (Nat.pow_le_pow_right (by decide) hWidth)

/-! ## §3. Multi-Round Fiat–Shamir QROM Reduction via Measure-and-Reprogram & Online Merkle Extraction -/

/-! ### §3.1 Unitary `(2 * Q + 1)`-Branch Amplitude Decomposition & `(2 * Q + 1)^2` RBR Step -/

/-- Project `QVec` onto a single target query coordinate `xStar : Fin cardX`. -/
def projSingle {cardX w cardAnc : Nat} (xStar : Fin cardX)
    (ψ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => if x = xStar then ψ x y a else GaussInt.zero

/-- Negate all Gaussian-integer amplitudes of a `QVec`. -/
def negQVec {cardX w cardAnc : Nat} (ψ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  (QVec.zero cardX w cardAnc).sub ψ

private theorem projSingle_normSq {cardX w cardAnc : Nat} (xStar : Fin cardX)
    (ψ : QVec cardX w cardAnc) :
    QVec.stateNormSq (projSingle xStar ψ) = QVec.queryWeight ψ xStar := by
  unfold QVec.stateNormSq
  have hPt :
      qsum cardX (fun x => QVec.queryWeight (projSingle xStar ψ) x) =
      qsum cardX (fun x => (if x = xStar then 1 else 0) * QVec.queryWeight ψ xStar) := by
    apply qsum_congr; intro x
    by_cases hx : x = xStar
    · subst hx
      simp only [↓reduceIte, Nat.one_mul, QVec.queryWeight, projSingle]
    · simp only [hx, ↓reduceIte, Nat.zero_mul, QVec.queryWeight, projSingle]
      have h0 : qsum (2 ^ w) (fun _ => qsum cardAnc (fun _ => GaussInt.normSq GaussInt.zero)) =
          qsum (2 ^ w) (fun _ => 0) := by
        apply qsum_congr; intro _
        have ha : GaussInt.normSq GaussInt.zero = 0 := rfl
        rw [qsum_congr (fun _ => ha), qsum_const, Nat.mul_zero]
      rw [h0, qsum_const, Nat.mul_zero]
  rw [hPt, qsum_mul_right, qsum_eq_indicator, Nat.one_mul]

private theorem negQVec_normSq {cardX w cardAnc : Nat} (ψ : QVec cardX w cardAnc) :
    QVec.stateNormSq (negQVec ψ) = QVec.stateNormSq ψ := by
  have hIntAbs : ∀ z : Int, (0 - z).natAbs = z.natAbs := by
    intro z; rw [Int.zero_sub, Int.natAbs_neg]
  unfold QVec.stateNormSq QVec.queryWeight negQVec QVec.sub QVec.zero
  apply qsum_congr; intro x
  apply qsum_congr; intro y
  apply qsum_congr; intro a
  unfold GaussInt.normSq GaussInt.sub GaussInt.zero
  dsimp only
  rw [hIntAbs, hIntAbs]

private theorem oracleXor_reprogram_diff_eq_projSingle {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (xStar : Fin cardX) (ch : BitVec w)
    (ψ : QVec cardX w cardAnc) :
    (oracleXor (reprogramOracle H xStar ch) ψ).sub (oracleXor H ψ) =
      (oracleXor (reprogramOracle H xStar ch) (projSingle xStar ψ)).sub
        (oracleXor H (projSingle xStar ψ)) := by
  funext x y a
  by_cases hx : x = xStar
  · subst hx
    simp only [QVec.sub, oracleXor, projSingle, ↓reduceIte]
  · simp only [QVec.sub, oracleXor, projSingle, reprogramOracle, hx, ↓reduceIte]
    unfold GaussInt.sub GaussInt.zero
    ext <;> dsimp only <;> omega

/-- Structural `2 * q + 1` counter matching `finGaussSum` & `qsum` front-peeling recursion. -/
def twoMulPlusOne : Nat → Nat
  | 0 => 1
  | q + 1 => (twoMulPlusOne q + 1) + 1

private theorem twoMulPlusOne_eq (q : Nat) : twoMulPlusOne q = 2 * q + 1 := by
  induction q with
  | zero => rfl
  | succ m ih => simp only [twoMulPlusOne, ih]; omega

/-- Interleaves `q` positive reprogramming branches, `q` negative pre-reprogramming branches, and
    `1` base execution branch into `twoMulPlusOne q` (`= 2 * q + 1`) vectors. -/
def interleaveDfmBranches {α : Type} :
    (q : Nat) → (Fin q → α) → (Fin q → α) → α → Fin (twoMulPlusOne q) → α
  | 0, _, _, base, _ => base
  | q + 1, posB, _, _, ⟨0, _⟩ => posB ⟨0, Nat.zero_lt_succ q⟩
  | q + 1, _, negB, _, ⟨1, _⟩ => negB ⟨0, Nat.zero_lt_succ q⟩
  | q + 1, posB, negB, base, ⟨k + 2, hk⟩ =>
    interleaveDfmBranches q
      (fun t => posB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)
      (fun t => negB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)
      base
      ⟨k, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk)⟩

private theorem finGaussSum_interleaveDfmBranches :
    ∀ (q : Nat) (posB negB : Fin q → GaussInt) (base : GaussInt),
      finGaussSum (twoMulPlusOne q) (interleaveDfmBranches q posB negB base) =
        GaussInt.add (finGaussSum q (fun t => GaussInt.add (posB t) (negB t))) base
  | 0, _, _, base => by
    simp only [twoMulPlusOne, finGaussSum, interleaveDfmBranches, GaussInt.add, GaussInt.zero]
    ext <;> dsimp only <;> omega
  | q + 1, posB, negB, base => by
    let posTail : Fin q → GaussInt := fun t => posB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    let negTail : Fin q → GaussInt := fun t => negB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    have ih := finGaussSum_interleaveDfmBranches q posTail negTail base
    change GaussInt.add (posB ⟨0, Nat.zero_lt_succ q⟩)
        (GaussInt.add (negB ⟨0, Nat.zero_lt_succ q⟩)
          (finGaussSum (twoMulPlusOne q) (interleaveDfmBranches q posTail negTail base))) =
      GaussInt.add
        (GaussInt.add
          (GaussInt.add (posB ⟨0, Nat.zero_lt_succ q⟩) (negB ⟨0, Nat.zero_lt_succ q⟩))
          (finGaussSum q (fun t => GaussInt.add (posTail t) (negTail t))))
        base
    rw [ih]
    unfold GaussInt.add
    ext <;> dsimp only <;> omega

private theorem qsum_interleaveDfmBranches {α : Type} (wt : α → Nat) :
    ∀ (q : Nat) (posB negB : Fin q → α) (base : α),
      qsum (twoMulPlusOne q) (fun k => wt (interleaveDfmBranches q posB negB base k)) =
        qsum q (fun t => wt (posB t) + wt (negB t)) + wt base
  | 0, _, _, base => by simp [twoMulPlusOne, qsum_zero, qsum_succ, interleaveDfmBranches]
  | q + 1, posB, negB, base => by
    let posTail : Fin q → α := fun t => posB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    let negTail : Fin q → α := fun t => negB ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩
    have ih := qsum_interleaveDfmBranches wt q posTail negTail base
    simp only [twoMulPlusOne, qsum_succ]
    change wt (posB ⟨0, Nat.zero_lt_succ q⟩) +
        (wt (negB ⟨0, Nat.zero_lt_succ q⟩) +
          qsum (twoMulPlusOne q) (fun k => wt (interleaveDfmBranches q posTail negTail base k))) =
      (wt (posB ⟨0, Nat.zero_lt_succ q⟩) + wt (negB ⟨0, Nat.zero_lt_succ q⟩) +
        qsum q (fun t => wt (posTail t) + wt (negTail t))) + wt base
    rw [ih]
    omega

private theorem interleaveDfmBranches_eval {cardX w cardAnc : Nat}
    (x : Fin cardX) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    ∀ (m : Nat) (pV nV : Fin m → QVec cardX w cardAnc) (bV : QVec cardX w cardAnc)
      (k : Fin (twoMulPlusOne m)),
      interleaveDfmBranches m pV nV bV k x y a =
        interleaveDfmBranches m (fun t => pV t x y a) (fun t => nV t x y a) (bV x y a) k
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, _, ⟨0, _⟩ => rfl
  | _ + 1, _, _, _, ⟨1, _⟩ => rfl
  | m' + 1, pV, nV, bV, ⟨k' + 2, hk⟩ =>
    interleaveDfmBranches_eval x y a m'
      (fun t => pV ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)
      (fun t => nV ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩)
      bV
      ⟨k', Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk)⟩

private theorem advStateAt_congr_idx {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w)
    {k₁ k₂ : Nat} (hk₁ : k₁ ≤ q) (hk₂ : k₂ ≤ q) (hEq : k₁ = k₂) :
    advStateAt A H k₁ hk₁ = advStateAt A H k₂ hk₂ := by
  subst hEq
  rfl

private theorem telescope_hybridAdv_reprogram {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) (xStar : Fin cardX) (ch : BitVec w)
    (x : Fin cardX) (y : Fin (2 ^ w)) (a : Fin cardAnc) :
    let H_ch := reprogramOracle H xStar ch
    let posB : Fin q → QVec cardX w cardAnc := fun t =>
      applySuffixFrom A H_ch t.1 t.2
        (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))
    let negB : Fin q → QVec cardX w cardAnc := fun t =>
      negQVec (applySuffixFrom A H_ch t.1 t.2
        (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2)))))
    finGaussSum (twoMulPlusOne q)
        (fun k => interleaveDfmBranches q posB negB (runQuantumAdv A H) k x y a) =
      runQuantumAdv A H_ch x y a := by
  dsimp only
  let H_ch := reprogramOracle H xStar ch
  let posVal : Fin q → GaussInt := fun t =>
    applySuffixFrom A H_ch t.1 t.2
      (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2)))) x y a
  let negVal : Fin q → GaussInt := fun t =>
    negQVec (applySuffixFrom A H_ch t.1 t.2
      (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))) x y a
  have hInter :
      finGaussSum (twoMulPlusOne q)
        (fun k => interleaveDfmBranches q
          (fun t => applySuffixFrom A H_ch t.1 t.2
            (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2)))))
          (fun t => negQVec (applySuffixFrom A H_ch t.1 t.2
            (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))))
          (runQuantumAdv A H) k x y a) =
      finGaussSum (twoMulPlusOne q)
        (interleaveDfmBranches q posVal negVal (runQuantumAdv A H x y a)) :=
    congrArg (finGaussSum (twoMulPlusOne q))
      (funext (interleaveDfmBranches_eval x y a q _ _ _))
  rw [hInter, finGaussSum_interleaveDfmBranches]
  have hStepEq : ∀ t : Fin q,
      GaussInt.add (posVal t) (negVal t) =
        GaussInt.sub
          (hybridAdv A H_ch H t.1 (Nat.le_of_lt t.2) x y a)
          (hybridAdv A H_ch H (t.1 + 1) t.2 x y a) := by
    intro t
    have hSubVec :
        (hybridAdv A H_ch H t.1 (Nat.le_of_lt t.2)).sub (hybridAdv A H_ch H (t.1 + 1) t.2) =
          (applySuffixFrom A H_ch t.1 t.2
            (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))).sub
          (applySuffixFrom A H_ch t.1 t.2
            (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))) := by
      have hRhs2 :
          applySuffixFrom A H_ch t.1 t.2 (oracleXor H (advStateAt A H t.1 (Nat.le_of_lt t.2))) =
            hybridAdv A H_ch H (t.1 + 1) t.2 := by
        rw [applySuffixFrom.eq_def]
        dsimp only
        have hStep : (A.steps t).apply (oracleXor H (advStateAt A H t.1 (Nat.le_of_lt t.2))) =
            advStateAt A H (t.1 + 1) t.2 := rfl
        rw [hStep]
        unfold hybridAdv
        if hNext : t.1 + 1 < q then
          simp only [hNext, ↓reduceDIte]
        else
          have hEqQ : t.1 + 1 = q := by omega
          simp only [hNext, ↓reduceDIte]
          exact advStateAt_congr_idx A H t.2 (Nat.le_refl q) hEqQ
      have hLhs1 : hybridAdv A H_ch H t.1 (Nat.le_of_lt t.2) =
          applySuffixFrom A H_ch t.1 t.2 (oracleXor H_ch (advStateAt A H t.1 (Nat.le_of_lt t.2))) := by
        unfold hybridAdv
        simp only [t.2, ↓reduceDIte]
      rw [hLhs1, ← hRhs2, ← applySuffixFrom_sub,
          oracleXor_reprogram_diff_eq_projSingle H xStar ch, applySuffixFrom_sub]
    have hAtCoord := congrFun (congrFun (congrFun hSubVec x) y) a
    dsimp only [posVal, negVal, negQVec, QVec.sub, QVec.zero] at hAtCoord ⊢
    rw [hAtCoord]
    unfold GaussInt.add GaussInt.sub GaussInt.zero
    ext <;> dsimp only <;> omega
  have hCongrG : ∀ {m : Nat} (f g : Fin m → GaussInt),
      (∀ i, f i = g i) → finGaussSum m f = finGaussSum m g := by
    intro m f g hfg
    exact congrArg (finGaussSum m) (funext hfg)
  rw [hCongrG _ _ hStepEq]
  have hTele : ∀ (m : Nat) (seq : (k : Nat) → k ≤ m → GaussInt),
      finGaussSum m (fun t => GaussInt.sub (seq t.1 (Nat.le_of_lt t.2)) (seq (t.1 + 1) t.2)) =
        GaussInt.sub (seq 0 (Nat.zero_le m)) (seq m (Nat.le_refl m)) := by
    intro m
    induction m with
    | zero => intro seq; simp [finGaussSum, GaussInt.sub, GaussInt.zero]
    | succ m' ihm =>
      intro seq
      simp only [finGaussSum]
      rw [ihm (fun k hk => seq (k + 1) (Nat.succ_le_succ hk))]
      unfold GaussInt.add GaussInt.sub
      ext <;> dsimp only <;> omega
  rw [hTele q (fun k hk => hybridAdv A H_ch H k hk x y a)]
  have hHyb0 : hybridAdv A H_ch H 0 (Nat.zero_le q) = runQuantumAdv A H_ch := by
    have hSuffEq : ∀ (k : Nat) (hk : k ≤ q),
        (if hlt : k < q then applySuffixFrom A H_ch k hlt (oracleXor H_ch (advStateAt A H_ch k hk))
         else advStateAt A H_ch q (Nat.le_refl q)) = runQuantumAdv A H_ch := by
      intro k hk
      induction hRem : q - k generalizing k with
      | zero =>
        have hEqQ : k = q := by omega
        subst hEqQ
        simp [runQuantumAdv]
      | succ rem ihRem =>
        have hlt : k < q := by omega
        simp only [hlt, ↓reduceDIte]
        rw [applySuffixFrom.eq_def]
        dsimp only
        have hAdvNext : (A.steps ⟨k, hlt⟩).apply (oracleXor H_ch (advStateAt A H_ch k hk)) =
            advStateAt A H_ch (k + 1) hlt := rfl
        rw [hAdvNext]
        if hNext : k + 1 < q then
          simp only [hNext, ↓reduceDIte]
          have ih' := ihRem (k + 1) (Nat.le_of_lt hNext) (by omega)
          simp only [hNext, ↓reduceDIte] at ih'
          exact ih'
        else
          have hEqQ : k + 1 = q := by omega
          simp only [hNext, ↓reduceDIte, runQuantumAdv]
          exact advStateAt_congr_idx A H_ch hlt (Nat.le_refl q) hEqQ
    cases q with
    | zero => rfl
    | succ q' =>
      have hPos : 0 < q' + 1 := Nat.zero_lt_succ q'
      have h0 := hSuffEq 0 (Nat.zero_le (q' + 1))
      simp only [hPos, ↓reduceDIte] at h0
      unfold hybridAdv
      simp only [hPos, ↓reduceDIte]
      exact h0
  have hHybQ : hybridAdv A H_ch H q (Nat.le_refl q) = runQuantumAdv A H := by
    unfold hybridAdv runQuantumAdv
    simp
  rw [hHyb0, hHybQ]
  dsimp only [H_ch]
  unfold GaussInt.add GaussInt.sub
  ext <;> dsimp only <;> omega

/-- `ch`-independent squared-amplitude envelope of `A` reprogrammed at `xStar` under `H`, for an
    arbitrary OUTPUT event `T` on the final query/output register. -/
def dfmEventEnvelope {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w) (xStar : Fin cardX)
    (T : Fin cardX → Bool) : Nat :=
  qsum q (fun t =>
    2 * (suffixScale A t.1 (Nat.le_of_lt t.2) *
      QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) xStar)) +
    QVec.queryMassOn T (runQuantumAdv A H)

private theorem queryMassOn_reprogram_le_dfmEventEnvelope {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w)
    (xStar : Fin cardX) (ch : BitVec w) (T : Fin cardX → Bool) :
    QVec.queryMassOn T (runQuantumAdv A (reprogramOracle H xStar ch)) ≤
      (2 * q + 1) * dfmEventEnvelope A H xStar T := by
  let H_ch := reprogramOracle H xStar ch
  let posB : Fin q → QVec cardX w cardAnc := fun t =>
    applySuffixFrom A H_ch t.1 t.2
      (oracleXor H_ch (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2))))
  let negB : Fin q → QVec cardX w cardAnc := fun t =>
    negQVec (applySuffixFrom A H_ch t.1 t.2
      (oracleXor H (projSingle xStar (advStateAt A H t.1 (Nat.le_of_lt t.2)))))
  let V := interleaveDfmBranches q posB negB (runQuantumAdv A H)
  have hPtCS : ∀ x : Fin cardX,
      QVec.queryWeight (runQuantumAdv A H_ch) x ≤
        twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k => QVec.queryWeight (V k) x) := by
    intro x
    unfold QVec.queryWeight
    have hStep1 :
        qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
          GaussInt.normSq (runQuantumAdv A H_ch x y a))) ≤
        qsum (2 ^ w) (fun y => qsum cardAnc (fun a =>
          twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k => GaussInt.normSq (V k x y a)))) := by
      apply qsum_le_qsum; intro y
      apply qsum_le_qsum; intro a
      rw [← telescope_hybridAdv_reprogram A H xStar ch x y a]
      exact normSq_finGaussSum_le (twoMulPlusOne q) (fun k => V k x y a)
    apply Nat.le_trans hStep1
    have hSwap : ∀ y,
        qsum cardAnc (fun a =>
          twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k => GaussInt.normSq (V k x y a))) =
        twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k =>
          qsum cardAnc (fun a => GaussInt.normSq (V k x y a))) := by
      intro y
      rw [qsum_mul_left, qsum_comm]
    rw [qsum_congr hSwap, qsum_mul_left, qsum_comm]
    exact Nat.le_refl _
  have hMass :
      QVec.queryMassOn T (runQuantumAdv A H_ch) ≤
        twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k => QVec.queryMassOn T (V k)) := by
    have hPt :
        qsum cardX (fun x =>
          if T x = true then QVec.queryWeight (runQuantumAdv A H_ch) x else 0) ≤
        qsum cardX (fun x =>
          twoMulPlusOne q * qsum (twoMulPlusOne q) (fun k =>
            if T x = true then QVec.queryWeight (V k) x else 0)) := by
      apply qsum_le_qsum; intro x
      cases T x
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
      · simp only [↓reduceIte]
        exact hPtCS x
    rw [qsum_mul_left, qsum_comm] at hPt
    exact hPt
  rw [qsum_interleaveDfmBranches (fun φ => QVec.queryMassOn T φ), twoMulPlusOne_eq] at hMass
  apply Nat.le_trans hMass
  apply Nat.mul_le_mul_left (2 * q + 1)
  unfold dfmEventEnvelope
  apply Nat.add_le_add_right
  apply qsum_le_qsum; intro t
  have hPosNorm :
      QVec.queryMassOn T (posB t) ≤
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) xStar := by
    have h1 := QVec.queryMassOn_le_stateNormSq T (posB t)
    dsimp only [posB] at h1
    rw [applySuffixFrom_normSq, oracleXor_isometry, projSingle_normSq] at h1
    exact h1
  have hNegNorm :
      QVec.queryMassOn T (negB t) ≤
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) xStar := by
    have h1 := QVec.queryMassOn_le_stateNormSq T (negB t)
    dsimp only [negB] at h1
    rw [negQVec_normSq, applySuffixFrom_normSq, oracleXor_isometry, projSingle_normSq] at h1
    exact h1
  omega

private theorem qsum_queryMassOn_fiber {cardX w cardAnc : Nat}
    (proj : Fin cardX → Fin cardX) (ψ : QVec cardX w cardAnc) :
    qsum cardX (fun xStar => QVec.queryMassOn (fun x => decide (xStar = proj x)) ψ) =
      QVec.stateNormSq ψ := by
  unfold QVec.queryMassOn QVec.stateNormSq
  rw [qsum_comm]
  apply qsum_congr; intro x
  have h : qsum cardX (fun xs =>
      if decide (xs = proj x) = true then QVec.queryWeight ψ x else 0) =
      qsum cardX (fun xs => if xs = proj x then QVec.queryWeight ψ x else 0) := by
    apply qsum_congr; intro xs
    simp only [decide_eq_true_eq]
  rw [h, qsum_ite_eq]

private theorem queryMassOn_point_eq {cardX w cardAnc : Nat}
    (ψ : QVec cardX w cardAnc) (xStar : Fin cardX) :
    QVec.queryMassOn (fun x => decide (xStar = x)) ψ = QVec.queryWeight ψ xStar := by
  unfold QVec.queryMassOn
  have hEq : qsum cardX (fun x =>
      if decide (xStar = x) = true then QVec.queryWeight ψ x else 0) =
      qsum cardX (fun x => if x = xStar then QVec.queryWeight ψ xStar else 0) := by
    apply qsum_congr; intro x
    by_cases hx : x = xStar
    · subst hx; simp
    · have hx' : ¬ xStar = x := fun h => hx h.symm
      simp [hx, hx']
  rw [hEq, qsum_ite_eq]

private theorem sum_dfmEventEnvelope_fiber_eq {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX) :
    qsum cardX (fun xStar =>
      dfmEventEnvelope A H xStar (fun x => decide (xStar = proj x))) =
      (2 * q + 1) * QVec.stateNormSq (runQuantumAdv A H) := by
  unfold dfmEventEnvelope
  rw [qsum_add, qsum_comm, qsum_queryMassOn_fiber]
  have hEachT :
      qsum q (fun t =>
        qsum cardX (fun xStar =>
          2 * (suffixScale A t.1 (Nat.le_of_lt t.2) *
            QVec.queryWeight (advStateAt A H t.1 (Nat.le_of_lt t.2)) xStar))) =
      qsum q (fun _ => 2 * QVec.stateNormSq (runQuantumAdv A H)) := by
    apply qsum_congr; intro t
    rw [qsum_mul_left 2, qsum_mul_left (suffixScale A t.1 (Nat.le_of_lt t.2))]
    change 2 * (suffixScale A t.1 (Nat.le_of_lt t.2) *
        QVec.stateNormSq (advStateAt A H t.1 (Nat.le_of_lt t.2))) = _
    rw [advStateAt_normSq, ← Nat.mul_assoc (suffixScale A t.1 _),
        Nat.mul_comm (suffixScale A t.1 _), prefix_mul_suffix_eq_total,
        ← runQuantumAdv_normSq A H]
  rw [hEachT, qsum_const]
  rw [← Nat.mul_assoc q 2, Nat.mul_comm q 2, Nat.add_mul, Nat.one_mul]

/-- **Projected Unitary Measure-and-Reprogram RBR Step
    (`qrom_unitary_measure_reprogram_rbr_step_projected`)**:
    For ANY `Q`-query unitary quantum adversary `A` (arbitrary scaled unitaries between
    superposition oracle calls, i.e. fully adaptive), ANY background oracle `H`, and ANY
    projection `proj` from the adversary's final OUTPUT register to the Fiat–Shamir query point
    it must be consistent with (in a transcript-chained `k`-round protocol the output is the full
    transcript and `proj` returns its round-`r` prefix), the total Born mass of outputs whose
    projected point `xStar = proj x` is doomed and is reprogrammed to a flipping challenge is at
    most **`(2 * Q + 1)^2 * badCard / 2^w`**. The fibers `{x | proj x = xStar}` are disjoint, so
    the bound does NOT pay for the size of the output register. -/
theorem qrom_unitary_measure_reprogram_rbr_step_projected
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX)
    (isDoomed : Fin cardX → Bool)
    (flipsToLive : Fin cardX → BitVec w → Bool)
    (badCard : Nat)
    (hRbr : ∀ x : Fin cardX, isDoomed x = true →
      qsum (2 ^ w) (fun j => if flipsToLive x (BitVec.ofFin j) = true then 1 else 0) ≤ badCard) :
    RatBound.le
      ⟨qsum cardX (fun xStar =>
         if isDoomed xStar = true then
           qsum (2 ^ w) (fun j =>
             if flipsToLive xStar (BitVec.ofFin j) = true then
               QVec.queryMassOn (fun x => decide (xStar = proj x))
                 (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
             else 0)
         else 0),
       2 ^ w * QVec.stateNormSq (runQuantumAdv A H),
       Nat.mul_pos (Nat.two_pow_pos w) (runQuantumAdv_normSq_pos A H)⟩
      ⟨(2 * Q + 1) ^ 2 * badCard, 2 ^ w, Nat.two_pow_pos w⟩ := by
  dsimp only [RatBound.le]
  let normFinal := QVec.stateNormSq (runQuantumAdv A H)
  have hPerX :
      qsum cardX (fun xStar =>
        if isDoomed xStar = true then
          qsum (2 ^ w) (fun j =>
            if flipsToLive xStar (BitVec.ofFin j) = true then
              QVec.queryMassOn (fun x => decide (xStar = proj x))
                (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
            else 0)
        else 0) ≤
      qsum cardX (fun xStar =>
        badCard * ((2 * Q + 1) *
          dfmEventEnvelope A H xStar (fun x => decide (xStar = proj x)))) := by
    apply qsum_le_qsum; intro xStar
    cases hD : isDoomed xStar
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
    · simp only [↓reduceIte]
      have hIn :
          qsum (2 ^ w) (fun j =>
            if flipsToLive xStar (BitVec.ofFin j) = true then
              QVec.queryMassOn (fun x => decide (xStar = proj x))
                (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
            else 0) ≤
          qsum (2 ^ w) (fun j =>
            (if flipsToLive xStar (BitVec.ofFin j) = true then 1 else 0) *
              ((2 * Q + 1) *
                dfmEventEnvelope A H xStar (fun x => decide (xStar = proj x)))) := by
        apply qsum_le_qsum; intro j
        cases flipsToLive xStar (BitVec.ofFin j)
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.le_refl]
        · simp only [↓reduceIte, Nat.one_mul]
          exact queryMassOn_reprogram_le_dfmEventEnvelope A H xStar (BitVec.ofFin j) _
      rw [qsum_mul_right] at hIn
      exact Nat.le_trans hIn
        (Nat.mul_le_mul_right _ (hRbr xStar hD))
  rw [qsum_mul_left badCard, qsum_mul_left (2 * Q + 1),
      sum_dfmEventEnvelope_fiber_eq] at hPerX
  have hSqEq : badCard * ((2 * Q + 1) * ((2 * Q + 1) * normFinal)) =
      (2 * Q + 1) ^ 2 * badCard * normFinal := by
    rw [Nat.pow_two, ← Nat.mul_assoc (2 * Q + 1) (2 * Q + 1) normFinal,
        Nat.mul_left_comm badCard ((2 * Q + 1) * (2 * Q + 1)) normFinal,
        Nat.mul_assoc ((2 * Q + 1) * (2 * Q + 1)) badCard normFinal]
  rw [hSqEq] at hPerX
  have hMul2w := Nat.mul_le_mul_right (2 ^ w) hPerX
  have hRhsEq : (2 * Q + 1) ^ 2 * badCard * normFinal * 2 ^ w =
      (2 * Q + 1) ^ 2 * badCard * (2 ^ w * normFinal) := by
    rw [Nat.mul_assoc ((2 * Q + 1) ^ 2 * badCard) normFinal (2 ^ w),
        Nat.mul_comm normFinal (2 ^ w)]
  rwa [hRhsEq] at hMul2w

/-- **Unitary Measure-and-Reprogram Single-Round RBR Theorem
    (`qrom_unitary_measure_reprogram_rbr_step`)**: the special case `proj = id` of
    `qrom_unitary_measure_reprogram_rbr_step_projected` (the output register IS the reprogrammed
    query point): the exact Born-rule RBR transition probability is bounded by
    **`(2 * Q + 1)^2 * badCard / 2^w`**. -/
theorem qrom_unitary_measure_reprogram_rbr_step
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (H : Fin cardX → BitVec w)
    (isDoomed : Fin cardX → Bool)
    (flipsToLive : Fin cardX → BitVec w → Bool)
    (badCard : Nat)
    (hRbr : ∀ x : Fin cardX, isDoomed x = true →
      qsum (2 ^ w) (fun j => if flipsToLive x (BitVec.ofFin j) = true then 1 else 0) ≤ badCard) :
    let normFinal := QVec.stateNormSq (runQuantumAdv A H)
    RatBound.le
      ⟨qsum cardX (fun xStar =>
         if isDoomed xStar = true then
           qsum (2 ^ w) (fun j =>
             if flipsToLive xStar (BitVec.ofFin j) = true then
               QVec.queryWeight (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j))) xStar
             else 0)
         else 0),
       2 ^ w * normFinal,
       Nat.mul_pos (Nat.two_pow_pos w) (runQuantumAdv_normSq_pos A H)⟩
      ⟨(2 * Q + 1) ^ 2 * badCard, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have h := qrom_unitary_measure_reprogram_rbr_step_projected A H id isDoomed flipsToLive
    badCard hRbr
  dsimp only [RatBound.le] at h ⊢
  refine Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_eq ?_)) h
  apply qsum_congr; intro xStar
  cases isDoomed xStar
  · rfl
  · simp only [↓reduceIte]
    apply qsum_congr; intro j
    cases flipsToLive xStar (BitVec.ofFin j)
    · rfl
    · simp only [↓reduceIte]
      exact (queryMassOn_point_eq _ xStar).symm

/-- **Oracle-Dependent (Adaptive Across Rounds) Measure-and-Reprogram Step
    (`qrom_adaptive_oracle_dependent_rbr_step`)**:
    In a multi-round Fiat–Shamir transcript, whether the round-`r` point `xStar` is doomed, and
    whether its challenge makes it live, depend on the ORACLE (through the challenges of earlier
    rounds). Both predicates here take the oracle as an argument and are evaluated on the very
    oracle `H[xStar ↦ ch]` the adversary ran against. The only structural requirement is
    acyclicity (`hLocal`): doomedness of `xStar` does not read the oracle AT `xStar`. -/
theorem qrom_adaptive_oracle_dependent_rbr_step
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX)
    (isDoomedAt : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (isLiveAfter : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (badCard : Nat)
    (hLocal : ∀ (x : Fin cardX) (ch : BitVec w),
      isDoomedAt (reprogramOracle H x ch) x = isDoomedAt H x)
    (hRbr : ∀ x : Fin cardX, isDoomedAt H x = true →
      qsum (2 ^ w) (fun j =>
        if isLiveAfter (reprogramOracle H x (BitVec.ofFin j)) x = true then 1 else 0) ≤ badCard) :
    RatBound.le
      ⟨qsum cardX (fun xStar =>
         qsum (2 ^ w) (fun j =>
           if (isDoomedAt (reprogramOracle H xStar (BitVec.ofFin j)) xStar &&
               isLiveAfter (reprogramOracle H xStar (BitVec.ofFin j)) xStar) = true then
             QVec.queryMassOn (fun x => decide (xStar = proj x))
               (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
           else 0)),
       2 ^ w * QVec.stateNormSq (runQuantumAdv A H),
       Nat.mul_pos (Nat.two_pow_pos w) (runQuantumAdv_normSq_pos A H)⟩
      ⟨(2 * Q + 1) ^ 2 * badCard, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have h := qrom_unitary_measure_reprogram_rbr_step_projected A H proj (isDoomedAt H)
    (fun x ch => isLiveAfter (reprogramOracle H x ch) x) badCard hRbr
  dsimp only [RatBound.le] at h ⊢
  refine Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_eq ?_)) h
  apply qsum_congr; intro xStar
  simp only [hLocal]
  cases isDoomedAt H xStar
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]
  · simp only [Bool.true_and, ↓reduceIte]

/-- One Fiat–Shamir round of a transcript-chained multi-round protocol as seen by the QROM
    reduction against the fixed background oracle `H`: the projection from the adversary's output
    to this round's query point, the oracle-dependent doomed / live-after predicates, and the
    round's bad-challenge count with its acyclicity and RBR flip-bound obligations. -/
structure QromRbrRound (cardX w : Nat) (H : Fin cardX → BitVec w) where
  proj : Fin cardX → Fin cardX
  isDoomedAt : (Fin cardX → BitVec w) → Fin cardX → Bool
  isLiveAfter : (Fin cardX → BitVec w) → Fin cardX → Bool
  badCard : Nat
  doomed_local : ∀ (x : Fin cardX) (ch : BitVec w),
    isDoomedAt (reprogramOracle H x ch) x = isDoomedAt H x
  flip_bound : ∀ x : Fin cardX, isDoomedAt H x = true →
    qsum (2 ^ w) (fun j =>
      if isLiveAfter (reprogramOracle H x (BitVec.ofFin j)) x = true then 1 else 0) ≤ badCard

/-- **Inhabited, oracle-dependent `QromRbrRound`**: over `Fin 2 → BitVec 2`, the round whose
    point is always doomed and becomes live exactly when the REPROGRAMMED oracle value at that
    point is zero has `badCard = 1`, attained with equality at every point. -/
def qromZeroChallengeRound (H : Fin 2 → BitVec 2) : QromRbrRound 2 2 H where
  proj := id
  isDoomedAt := fun _ _ => true
  isLiveAfter := fun O x => decide ((O x).toNat = 0)
  badCard := 1
  doomed_local := fun _ _ => rfl
  flip_bound := fun x _ => by
    have hEq : ∀ j : Fin (2 ^ 2),
        decide (((reprogramOracle H x (BitVec.ofFin j)) x).toNat = 0) = decide (j.1 = 0) := by
      intro j
      simp only [reprogramOracle, ↓reduceIte, BitVec.toNat_ofFin]
    rw [qsum_congr (fun j => by rw [hEq j])]
    simp [qsum_succ, qsum_zero]

/-- Total reprogrammed Born mass of the doomed-to-live flip event of round `rd`. -/
def qromRoundFlipMass {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (H : Fin cardX → BitVec w)
    (rd : QromRbrRound cardX w H) : Nat :=
  qsum cardX (fun xStar =>
    qsum (2 ^ w) (fun j =>
      if (rd.isDoomedAt (reprogramOracle H xStar (BitVec.ofFin j)) xStar &&
          rd.isLiveAfter (reprogramOracle H xStar (BitVec.ofFin j)) xStar) = true then
        QVec.queryMassOn (fun x => decide (xStar = rd.proj x))
          (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
      else 0))

/-- **`k`-Round QROM Measure-and-Reprogram Union Theorem
    (`qrom_multiRound_measure_reprogram_union`)**:
    For ANY `Q`-query unitary adversary and ANY list of Fiat–Shamir rounds, the summed
    doomed-to-live flip mass over all rounds is at most
    **`(2 * Q + 1)^2 * (∑_r badCard_r) / 2^w`**: each round pays `(2 * Q + 1)^2` once (no
    `(2 * Q + 1)^{2k}` blow-up), derived from the unitary step theorem rather than assumed. -/
theorem qrom_multiRound_measure_reprogram_union
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (H : Fin cardX → BitVec w) :
    ∀ (rounds : List (QromRbrRound cardX w H)),
      RatBound.le
        ⟨(rounds.map (qromRoundFlipMass A H)).sum,
         2 ^ w * QVec.stateNormSq (runQuantumAdv A H),
         Nat.mul_pos (Nat.two_pow_pos w) (runQuantumAdv_normSq_pos A H)⟩
        ⟨(2 * Q + 1) ^ 2 * (rounds.map (fun rd => rd.badCard)).sum, 2 ^ w, Nat.two_pow_pos w⟩
  | [] => by
    show 0 * 2 ^ w ≤ _
    rw [Nat.zero_mul]
    exact Nat.zero_le _
  | rd :: rest => by
    have ih := qrom_multiRound_measure_reprogram_union A H rest
    have h1 : qromRoundFlipMass A H rd * 2 ^ w ≤
        (2 * Q + 1) ^ 2 * rd.badCard * (2 ^ w * QVec.stateNormSq (runQuantumAdv A H)) :=
      qrom_adaptive_oracle_dependent_rbr_step A H rd.proj rd.isDoomedAt rd.isLiveAfter
        rd.badCard rd.doomed_local rd.flip_bound
    have ih' : (rest.map (qromRoundFlipMass A H)).sum * 2 ^ w ≤
        (2 * Q + 1) ^ 2 * (rest.map (fun rd => rd.badCard)).sum *
          (2 ^ w * QVec.stateNormSq (runQuantumAdv A H)) := ih
    show (qromRoundFlipMass A H rd + (rest.map (qromRoundFlipMass A H)).sum) * 2 ^ w ≤
      (2 * Q + 1) ^ 2 * (rd.badCard + (rest.map (fun rd => rd.badCard)).sum) *
        (2 ^ w * QVec.stateNormSq (runQuantumAdv A H))
    rw [Nat.add_mul, Nat.mul_add, Nat.add_mul]
    exact Nat.add_le_add h1 ih'

/-- Sum over every oracle `Fin n → BitVec w`, with each function occurring once.
    The recursion is the constructive product enumeration of the finite output alphabet. -/
def uniformOracleSum (w : Nat) : (n : Nat) → ((Fin n → BitVec w) → Nat) → Nat
  | 0, f => f Fin.elim0
  | n + 1, f => qsum (2 ^ w) (fun j =>
      uniformOracleSum w n (fun H => f (Fin.cases (BitVec.ofFin j) H)))

theorem uniformOracleSum_congr (w : Nat) : ∀ (n : Nat)
    (f g : (Fin n → BitVec w) → Nat), (∀ H, f H = g H) →
    uniformOracleSum w n f = uniformOracleSum w n g
  | 0, _, _, h => h _
  | n + 1, _, _, h => qsum_congr (fun _ => uniformOracleSum_congr w n _ _ (fun _ => h _))

theorem uniformOracleSum_const (w : Nat) : ∀ (n c : Nat),
    uniformOracleSum w n (fun _ => c) = (2 ^ w) ^ n * c
  | 0, c => (Nat.one_mul c).symm
  | n + 1, c => by
    simp only [uniformOracleSum, uniformOracleSum_const w n c, qsum_const,
      Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

theorem uniformOracleSum_mul (w : Nat) : ∀ (n c : Nat)
    (f : (Fin n → BitVec w) → Nat),
    uniformOracleSum w n (fun H => c * f H) = c * uniformOracleSum w n f
  | 0, _, _ => rfl
  | n + 1, c, f => by
    simp only [uniformOracleSum, uniformOracleSum_mul w n c, qsum_mul_left]

theorem uniformOracleSum_le (w : Nat) : ∀ (n : Nat)
    (f g : (Fin n → BitVec w) → Nat), (∀ H, f H ≤ g H) →
    uniformOracleSum w n f ≤ uniformOracleSum w n g
  | 0, _, _, h => h _
  | n + 1, _, _, h => qsum_le_qsum (fun _ => uniformOracleSum_le w n _ _ (fun _ => h _))

theorem uniformOracleSum_qsum (w : Nat) : ∀ (n k : Nat)
    (f : (Fin n → BitVec w) → Fin k → Nat),
    uniformOracleSum w n (fun H => qsum k (f H)) =
      qsum k (fun j => uniformOracleSum w n (fun H => f H j))
  | 0, _, _ => rfl
  | n + 1, k, f => by
    simp only [uniformOracleSum, uniformOracleSum_qsum w n k]
    exact qsum_comm _ _ _

/-- Replacing one coordinate of a uniformly random oracle by an independent uniform
    challenge preserves its distribution. This identity applies to arbitrary oracle-dependent
    payoffs, including the Born mass of an adaptive adversary. No independence of the payoff
    from the reprogrammed coordinate is required. -/
theorem uniformOracleSum_resample (w : Nat) : ∀ (n : Nat) (x : Fin n)
    (f : (Fin n → BitVec w) → Nat),
    uniformOracleSum w n (fun H => qsum (2 ^ w) (fun j =>
      f (reprogramOracle H x (BitVec.ofFin j)))) =
      2 ^ w * uniformOracleSum w n f
  | 0, x, _ => Fin.elim0 x
  | n + 1, x, f => by
    refine Fin.cases ?_ (fun y => ?_) x
    · have heq : ∀ (a b : BitVec w) (H : Fin n → BitVec w),
          reprogramOracle (Fin.cases a H) 0 b = Fin.cases b H := by
        intro a b H
        funext z
        refine Fin.cases ?_ (fun i => ?_) z
        · simp [reprogramOracle]
        · simp [reprogramOracle, Fin.succ_ne_zero]
      simp only [uniformOracleSum, heq, uniformOracleSum_qsum]
      rw [qsum_const]
    · have heq : ∀ (a b : BitVec w) (H : Fin n → BitVec w),
          reprogramOracle (Fin.cases a H) y.succ b =
            Fin.cases a (reprogramOracle H y b) := by
        intro a b H
        funext z
        refine Fin.cases ?_ (fun i => ?_) z
        · simp [reprogramOracle, Ne.symm (Fin.succ_ne_zero y)]
        · simp [reprogramOracle, Fin.succ_inj]
      simp only [uniformOracleSum, heq]
      rw [← qsum_mul_left]
      apply qsum_congr
      intro j
      exact uniformOracleSum_resample w n y (fun H => f (Fin.cases (BitVec.ofFin j) H))

/-- A round's ordinary (unreprogrammed) success mass, summed over the projected output point. -/
def qromOrdinaryFlipMass {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX)
    (doomed live : (Fin cardX → BitVec w) → Fin cardX → Bool) : Nat :=
  qsum cardX (fun x => if (doomed H x && live H x) = true then
    QVec.queryMassOn (fun z => decide (x = proj z)) (runQuantumAdv A H) else 0)

/-- Exact bridge from the per-oracle reprogrammed mass to uniformly averaged ordinary
    adversary success mass. The factor `2^w` cancels the sampled-challenge denominator. -/
theorem qrom_uniform_oracle_flip_mass {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (round : (H : Fin cardX → BitVec w) → QromRbrRound cardX w H)
    (proj : Fin cardX → Fin cardX)
    (doomed live : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (hp : ∀ H, (round H).proj = proj)
    (hd : ∀ H, (round H).isDoomedAt = doomed)
    (hl : ∀ H, (round H).isLiveAfter = live) :
    uniformOracleSum w cardX (fun H => qromRoundFlipMass A H (round H)) =
      2 ^ w * uniformOracleSum w cardX (fun H =>
        qromOrdinaryFlipMass A H proj doomed live) := by
  simp only [qromRoundFlipMass, hp, hd, hl, qromOrdinaryFlipMass]
  rw [uniformOracleSum_qsum, uniformOracleSum_qsum, ← qsum_mul_left]
  apply qsum_congr
  intro x
  exact uniformOracleSum_resample w cardX x (fun H =>
    if (doomed H x && live H x) = true then
      QVec.queryMassOn (fun z => decide (x = proj z)) (runQuantumAdv A H) else 0)

/-- Averaged QROM round bound with a uniformly random oracle. The denominator is exactly
    the number of oracles times the adversary's oracle-independent squared norm. -/
theorem qrom_uniform_oracle_round_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (round : (H : Fin cardX → BitVec w) → QromRbrRound cardX w H)
    (proj : Fin cardX → Fin cardX)
    (doomed live : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (bad : Nat)
    (hp : ∀ H, (round H).proj = proj)
    (hd : ∀ H, (round H).isDoomedAt = doomed)
    (hl : ∀ H, (round H).isLiveAfter = live)
    (hb : ∀ H, (round H).badCard = bad) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => qromOrdinaryFlipMass A H proj doomed live),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * bad, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have hpoint : ∀ H, qromRoundFlipMass A H (round H) ≤
      (2 * Q + 1) ^ 2 * bad *
        (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init) := by
    intro H
    have h := qrom_multiRound_measure_reprogram_union A H [round H]
    change qromRoundFlipMass A H (round H) * 2 ^ w ≤
      (2 * Q + 1) ^ 2 * (round H).badCard *
        (2 ^ w * QVec.stateNormSq (runQuantumAdv A H)) at h
    rw [hb, runQuantumAdv_normSq] at h
    apply Nat.le_of_mul_le_mul_right (c := 2 ^ w) _ (Nat.two_pow_pos w)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have havg := uniformOracleSum_le w cardX _ _ hpoint
  rw [qrom_uniform_oracle_flip_mass A round proj doomed live hp hd hl,
    uniformOracleSum_const] at havg
  dsimp only [RatBound.le]
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using havg

/-- Uniform-oracle multi-round union bound. Each round may depend on the entire oracle;
    only its projection and predicate definitions are fixed across background-oracle choices.
    The adversary remains fully adaptive, and the reduction pays the quadratic loss once. -/
theorem qrom_uniform_oracle_multiRound_union {cardX w cardAnc Q k : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (round : Fin k → (H : Fin cardX → BitVec w) → QromRbrRound cardX w H)
    (proj : Fin k → Fin cardX → Fin cardX)
    (doomed live : Fin k → (Fin cardX → BitVec w) → Fin cardX → Bool)
    (bad : Fin k → Nat)
    (hp : ∀ r H, (round r H).proj = proj r)
    (hd : ∀ r H, (round r H).isDoomedAt = doomed r)
    (hl : ∀ r H, (round r H).isLiveAfter = live r)
    (hb : ∀ r H, (round r H).badCard = bad r) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => qsum k (fun r =>
          qromOrdinaryFlipMass A H (proj r) (doomed r) (live r))),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * qsum k bad, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have h := qsum_le_qsum (fun r => qrom_uniform_oracle_round_bound A (round r)
    (proj r) (doomed r) (live r) (bad r) (hp r) (hd r) (hl r) (hb r))
  dsimp only [RatBound.le] at h ⊢
  rw [uniformOracleSum_qsum]
  simpa only [qsum_mul_right, qsum_mul_left] using h

/-- Expected adversary success over a uniformly random oracle. A protocol supplies the
    ordinary round-flip covering property; averaging and measure-and-reprogram then give the
    same single quadratic loss as the per-oracle union theorem. -/
theorem qrom_uniform_oracle_success_bound {cardX w cardAnc Q k : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (accept : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (round : Fin k → (H : Fin cardX → BitVec w) → QromRbrRound cardX w H)
    (proj : Fin k → Fin cardX → Fin cardX)
    (doomed live : Fin k → (Fin cardX → BitVec w) → Fin cardX → Bool)
    (bad : Fin k → Nat)
    (hp : ∀ r H, (round r H).proj = proj r)
    (hd : ∀ r H, (round r H).isDoomedAt = doomed r)
    (hl : ∀ r H, (round r H).isLiveAfter = live r)
    (hb : ∀ r H, (round r H).badCard = bad r)
    (hCover : ∀ H, QVec.queryMassOn (accept H) (runQuantumAdv A H) ≤
      qsum k (fun r => qromOrdinaryFlipMass A H (proj r) (doomed r) (live r))) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => QVec.queryMassOn (accept H) (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * qsum k bad, 2 ^ w, Nat.two_pow_pos w⟩ := by
  have h := qrom_uniform_oracle_multiRound_union A round proj doomed live bad hp hd hl hb
  exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ w)
    (uniformOracleSum_le w cardX _ _ hCover)) h

/-! ### §3.2 `k`-Round RBR Induction, Online Merkle Extraction & Concrete `Hem` v6 (`k = 5`) -/

/-- Exact `(2 * Q + 1)^2` Measure-and-Reprogram scaling of an interactive RBR round bound `b`. -/
@[expose] def dfmRoundScale (Q : Nat) (b : RatBound) : RatBound :=
  RatBound.scale ((2 * Q + 1) ^ 2) b

/-- Recompute a position-tweaked Merkle root from a node digest and its authentication path.
    `H lvl node` compresses the two children of node `node` at level `lvl`; `idx` is the index
    of the current node and its parity selects the child slot. -/
def merkleRootFromPath {D : Type} (H : Nat → Nat → D → D → D) : Nat → Nat → D → List D → D
  | _, _, cur, [] => cur
  | lvl, idx, cur, sib :: rest =>
    merkleRootFromPath H (lvl + 1) (idx / 2)
      (if idx % 2 = 0 then H lvl (idx / 2) cur sib else H lvl (idx / 2) sib cur) rest

/-- A collision of the tweaked compression function at ONE tree position: two different child
    pairs with the same digest under the same `(lvl, node)` tweak. -/
def MerkleTweakCollision {D : Type} (H : Nat → Nat → D → D → D) : Prop :=
  ∃ (lvl node : Nat) (a b a' b' : D), (a ≠ a' ∨ b ≠ b') ∧ H lvl node a b = H lvl node a' b'

/-- **Collision-or-unique-opening.** Two openings of the same position to the same root either
    coincide (same leaf digest, same authentication path) or exhibit a same-position collision
    of the tweaked compression function. This is the classical binding reduction behind the
    collision term of `qromMerkleOnlineExtractBound`; it is a statement about fixed openings
    and not the quantum online-extraction game. -/
theorem merkle_collision_or_unique_opening {D : Type} [DecidableEq D]
    (H : Nat → Nat → D → D → D) :
    ∀ (path path' : List D) (lvl idx : Nat) (leaf leaf' : D),
      path.length = path'.length →
      merkleRootFromPath H lvl idx leaf path = merkleRootFromPath H lvl idx leaf' path' →
      (leaf = leaf' ∧ path = path') ∨ MerkleTweakCollision H
  | [], [], _, _, _, _, _, h => .inl ⟨h, rfl⟩
  | [], _ :: _, _, _, _, _, hl, _ => absurd hl.symm (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, _, _, hl, _ => absurd hl (Nat.succ_ne_zero _)
  | sib :: rest, sib' :: rest', lvl, idx, leaf, leaf', hl, h => by
    have h' : merkleRootFromPath H (lvl + 1) (idx / 2)
          (if idx % 2 = 0 then H lvl (idx / 2) leaf sib else H lvl (idx / 2) sib leaf) rest =
        merkleRootFromPath H (lvl + 1) (idx / 2)
          (if idx % 2 = 0 then H lvl (idx / 2) leaf' sib' else H lvl (idx / 2) sib' leaf')
          rest' := h
    cases merkle_collision_or_unique_opening H rest rest' (lvl + 1) (idx / 2) _ _
        (Nat.succ.inj hl) h' with
    | inr hc => exact .inr hc
    | inl hp =>
      obtain ⟨hpar, hrest⟩ := hp
      if hEq : leaf = leaf' ∧ sib = sib' then
        exact .inl ⟨hEq.1, by rw [hEq.2, hrest]⟩
      else
        if hpar0 : idx % 2 = 0 then
          rw [ite_eq_left hpar0, ite_eq_left hpar0] at hpar
          refine .inr ?_
          unfold MerkleTweakCollision
          exact ⟨lvl, idx / 2, leaf, sib, leaf', sib',
            if hl1 : leaf = leaf' then .inr (fun hs => hEq ⟨hl1, hs⟩) else .inl hl1, hpar⟩
        else
          rw [ite_eq_right hpar0, ite_eq_right hpar0] at hpar
          refine .inr ?_
          unfold MerkleTweakCollision
          exact ⟨lvl, idx / 2, sib, leaf, sib', leaf',
            if hl1 : leaf = leaf' then .inl (fun hs => hEq ⟨hl1, hs⟩) else .inr hl1, hpar⟩

/-- Commitment-extraction CHARGE per committed Merkle root over `secBits`-bit digests:
    the single-target Grover term `8 (Q + 1)^2 / 2^secBits` plus the generic quantum collision
    term `8 (Q + 1)^3 / 2^secBits` (`quantumBhtCollisionBound`). Position tweaks confine a
    collision to one tree position (`merkle_collision_or_unique_opening`) but the adversary still
    chooses both preimages, so the cubic term cannot be dropped. This is a budget term in the
    shape of `[DFMS21]` / `[CMS19]`; the quantum online-extraction reduction for the deployed
    tree is NOT mechanized here. At `secBits = 256` the cubic term limits `128`-bit budgets to
    `Q + 1 ≤ 2^40`. -/
@[expose] def qromMerkleOnlineExtractBound (numRoots secBits Q : Nat) : RatBound :=
  RatBound.scale numRoots
    (RatBound.add (quantumGroverSingleTargetBound secBits Q) (quantumBhtCollisionBound secBits Q))

/-- Multi-round QROM Fiat–Shamir budget in the shape of `[DFMS19]` / `[CMS19]`:
    1. `k` reprogrammed RBR challenge rounds, `∑_r (2 Q + 1)^2 * rbrBounds[r]`;
    2. commitment extraction, `qromMerkleOnlineExtractBound`;
    3. query rounds under Fiat–Shamir search, `∑_j 8 (Q + 1)^2 * queryBounds[j]`
       (`quantumGroverGrindingBound`): the prover picks the grinding nonce before the queries are
       derived, so query soundness is a search bound in the oracle budget. `queryBounds` are
       PURE per-stage query errors; no proof-of-work density is credited on top of the search
       factor. -/
@[expose] def multiRoundFsQromCompilerBound
    (Q numRoots secBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) : RatBound :=
  RatBound.add
    (RatBound.sumList (rbrChallengeBounds.map (dfmRoundScale Q)))
    (RatBound.add
      (qromMerkleOnlineExtractBound numRoots secBits Q)
      (RatBound.sumList (queryStageBounds.map (quantumGroverGrindingBound Q))))

/-- **Constructive `k`-Round QROM RBR Induction Theorem (`rbr_multiRound_qrom_induction`)**:
    Starting from a doomed initial state (`liveAt 0 ≤ 0`), if each round `idx` satisfies
    `liveAt (idx + 1) ≤ liveAt idx + (2 * Q + 1)^2 * rbrBounds[idx]`, then after `k` rounds
    `liveAt k ≤ ∑_{idx < k} (2 * Q + 1)^2 * rbrBounds[idx]`! -/
theorem rbr_multiRound_qrom_induction
    (Q : Nat) :
    ∀ (rbrBounds : List RatBound) (liveAt : Nat → RatBound),
      RatBound.le (liveAt 0) RatBound.zero →
      (∀ (idx : Nat) (b : RatBound), rbrBounds[idx]? = some b →
        RatBound.le (liveAt (idx + 1)) (RatBound.add (liveAt idx) (dfmRoundScale Q b))) →
      RatBound.le (liveAt rbrBounds.length)
        (RatBound.sumList (rbrBounds.map (dfmRoundScale Q)))
  | [], liveAt, h0, _ => h0
  | b :: rest, liveAt, h0, hStep => by
    simp only [List.length_cons, List.map_cons, RatBound.sumList]
    have hFirst : RatBound.le (liveAt 1) (RatBound.add (liveAt 0) (dfmRoundScale Q b)) :=
      hStep 0 b rfl
    have hFirstSimp : RatBound.le (liveAt 1) (dfmRoundScale Q b) := by
      have hAdd0 := RatBound.add_le_add h0 (RatBound.le_refl (dfmRoundScale Q b))
      have hZeroAdd : RatBound.le (RatBound.add RatBound.zero (dfmRoundScale Q b))
          (dfmRoundScale Q b) := by
        unfold RatBound.le RatBound.add RatBound.zero
        dsimp only
        rw [Nat.zero_mul, Nat.zero_add, Nat.mul_one, Nat.one_mul]
        exact Nat.le_refl _
      exact RatBound.le_trans hFirst (RatBound.le_trans hAdd0 hZeroAdd)
    have hTail : ∀ (bs : List RatBound) (f : Nat → RatBound),
        (∀ (idx : Nat) (item : RatBound), bs[idx]? = some item →
          RatBound.le (f (idx + 1)) (RatBound.add (f idx) (dfmRoundScale Q item))) →
        RatBound.le (f bs.length)
          (RatBound.add (f 0) (RatBound.sumList (bs.map (dfmRoundScale Q)))) := by
      intro bs
      induction bs with
      | nil =>
        intro f _
        unfold RatBound.le RatBound.add RatBound.sumList RatBound.zero
        dsimp only [List.map, List.length_nil]
        rw [Nat.zero_mul, Nat.add_zero, Nat.mul_one, Nat.mul_one]
        exact Nat.le_refl _
      | cons hd tl ih =>
        intro f hf
        have h1 := hf 0 hd rfl
        have ihShift := ih (fun i => f (i + 1)) (fun idx item hGet => hf (idx + 1) item hGet)
        simp only [List.length_cons, List.map_cons, RatBound.sumList]
        have hStepAdd := RatBound.add_le_add h1
          (RatBound.le_refl (RatBound.sumList (tl.map (dfmRoundScale Q))))
        have hAssoc : RatBound.le
            (RatBound.add (RatBound.add (f 0) (dfmRoundScale Q hd))
              (RatBound.sumList (tl.map (dfmRoundScale Q))))
            (RatBound.add (f 0)
              (RatBound.add (dfmRoundScale Q hd)
                (RatBound.sumList (tl.map (dfmRoundScale Q))))) := by
          unfold RatBound.le RatBound.add
          dsimp only
          have hEq :
              ((f 0).num * (dfmRoundScale Q hd).den + (dfmRoundScale Q hd).num * (f 0).den) *
                (RatBound.sumList (tl.map (dfmRoundScale Q))).den +
              (RatBound.sumList (tl.map (dfmRoundScale Q))).num *
                ((f 0).den * (dfmRoundScale Q hd).den) =
              (f 0).num * ((dfmRoundScale Q hd).den *
                (RatBound.sumList (tl.map (dfmRoundScale Q))).den) +
              ((dfmRoundScale Q hd).num * (RatBound.sumList (tl.map (dfmRoundScale Q))).den +
                (RatBound.sumList (tl.map (dfmRoundScale Q))).num * (dfmRoundScale Q hd).den) *
                (f 0).den := by
            rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
            congr 1
            rw [Nat.mul_right_comm ((dfmRoundScale Q hd).num),
                Nat.mul_comm (f 0).den (dfmRoundScale Q hd).den,
                ← Nat.mul_assoc]
          have hDenEq :
              (f 0).den * (dfmRoundScale Q hd).den *
                (RatBound.sumList (tl.map (dfmRoundScale Q))).den =
              (f 0).den * ((dfmRoundScale Q hd).den *
                (RatBound.sumList (tl.map (dfmRoundScale Q))).den) :=
            Nat.mul_assoc _ _ _
          rw [hEq, hDenEq]
          exact Nat.le_refl _
        exact RatBound.le_trans ihShift (RatBound.le_trans hStepAdd hAssoc)
    have hRestBound := hTail rest (fun i => liveAt (i + 1)) (fun idx item hGet => hStep (idx + 1) item hGet)
    exact RatBound.le_trans hRestBound
      (RatBound.add_le_add hFirstSimp (RatBound.le_refl _))


end Qsag

namespace Qsag
/-! ## §3. Steiner-Deduplicated Merkle-Canopy Multi-Proofs (`pcs.rs`, `CanopyMultiProof`) -/

/-- Parent digest of the active node `(u, hu)` combined with an authentication sibling `s`
    consumed from the proof (`pcs.rs:verify_canopy_multiproof`, the `else` arm):
    `(u & 1) == 0` puts `hu` on the left, otherwise on the right; the node index fed to the hash is
    the parent `u >> 1`. -/
def canopyParentHash {D : Type} (nodeHash : Nat → D → D → D) (u : Nat) (hu s : D) : D :=
  if u &&& 1 = 0 then nodeHash (u >>> 1) hu s else nodeHash (u >>> 1) s hu

/-- One tree level of `verify_canopy_multiproof` (the inner `while k < active.len()` loop).
    Walks the active list of heap-indexed `(node, digest)` pairs left to right. If the next active
    entry is the sibling `u ^ 1`, the two are merged as `nodeHash (u >> 1) hu hv` (`k += 2`) and no
    proof digest is consumed. Otherwise exactly one digest is consumed from the sibling list
    (`k += 1`), and the walk fails (`none`) when the list is exhausted. Returns the next level's
    active list together with the unconsumed siblings. -/
def canopyLevelStep {D : Type} (nodeHash : Nat → D → D → D) :
    List (Nat × D) → List D → Option (List (Nat × D) × List D)
  | [], sibs => some ([], sibs)
  | [(u, hu)], sibs =>
    match sibs with
    | [] => none
    | s :: rest => some ([(u >>> 1, canopyParentHash nodeHash u hu s)], rest)
  | (u, hu) :: (v, hv) :: tl, sibs =>
    if v = u ^^^ 1 then
      (canopyLevelStep nodeHash tl sibs).map
        (fun r => ((u >>> 1, nodeHash (u >>> 1) hu hv) :: r.1, r.2))
    else
      match sibs with
      | [] => none
      | s :: rest =>
        (canopyLevelStep nodeHash ((v, hv) :: tl) rest).map
          (fun r => ((u >>> 1, canopyParentHash nodeHash u hu s) :: r.1, r.2))

/-- `depth` iterations of `canopyLevelStep` (the outer `while cur_depth > 0` loop), threading
    the sibling cursor as the list of unconsumed digests. -/
def canopyLevels {D : Type} (nodeHash : Nat → D → D → D) :
    Nat → List (Nat × D) → List D → Option (List (Nat × D) × List D)
  | 0, active, sibs => some (active, sibs)
  | depth + 1, active, sibs =>
    match canopyLevelStep nodeHash active sibs with
    | none => none
    | some r => canopyLevels nodeHash depth r.1 r.2

/-- Index pre-checks of `verify_canopy_multiproof`: the list is nonempty, strictly ascending on
    every adjacent window, and its last index is `< n`. -/
def canopyIndicesOk (n : Nat) : List Nat → Bool
  | [] => false
  | [i] => decide (i < n)
  | i :: j :: tl => decide (i < j) && canopyIndicesOk n (j :: tl)

/-- `pcs.rs:verify_canopy_multiproof`. Leaf `i` sits at heap index `2^logLeaves + i`; after
    `logLeaves` levels the walk must have consumed every proof digest (`sib_cursor == len`), the
    active list must be exactly `[(1, top)]`, and `rootHash logLeaves top` must equal the
    commitment. `nodeHash` models `hash_merkle_internal(node_idx, left, right)` and `rootHash`
    models `hash_tree_root(log_leaves, top)`. -/
def verifyCanopyMultiproof {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D) : Bool :=
  decide (logLeaves ≤ 28) &&
  canopyIndicesOk (2 ^ logLeaves) (leaves.map Prod.fst) &&
  match canopyLevels nodeHash logLeaves
      (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof with
  | some ([(u, top)], []) => decide (u = 1) && decide (rootHash logLeaves top = commitment)
  | _ => false

/-- `verifyCanopyMultiproof` with the exact-consumption check (`sib_cursor == len`) removed:
    unconsumed trailing digests are ignored. Defined only to show that the check is load-bearing
    (`canopyToy_relaxed_accepts_extra_sibling`). -/
def verifyCanopyMultiproofRelaxed {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D) : Bool :=
  decide (logLeaves ≤ 28) &&
  canopyIndicesOk (2 ^ logLeaves) (leaves.map Prod.fst) &&
  match canopyLevels nodeHash logLeaves
      (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof with
  | some ([(u, top)], _) => decide (u = 1) && decide (rootHash logLeaves top = commitment)
  | _ => false

/-- The level walk of `canopyLevelStep` on node indices alone: the next level's indices and the
    number of sibling digests the level consumes. -/
def steinerLevelStep : List Nat → List Nat × Nat
  | [] => ([], 0)
  | [u] => ([u >>> 1], 1)
  | u :: v :: tl =>
    if v = u ^^^ 1 then
      ((u >>> 1) :: (steinerLevelStep tl).1, (steinerLevelStep tl).2)
    else
      ((u >>> 1) :: (steinerLevelStep (v :: tl)).1, (steinerLevelStep (v :: tl)).2 + 1)

/-- Total number of sibling digests consumed over `depth` levels starting from `nodes`. -/
def steinerCountLevels : Nat → List Nat → Nat
  | 0, _ => 0
  | depth + 1, nodes =>
    (steinerLevelStep nodes).2 + steinerCountLevels depth (steinerLevelStep nodes).1

/-- Number of authentication siblings in the Steiner-deduplicated multiproof for the leaf index
    list `indices` in a tree with `2^logLeaves` leaves. A function of the indices only. -/
def steinerSiblingCount (logLeaves : Nat) (indices : List Nat) : Nat :=
  steinerCountLevels logLeaves (indices.map (fun i => 2 ^ logLeaves + i))

private theorem canopyLevelStep_nil {D : Type} (nodeHash : Nat → D → D → D)
    {s : List D} {b : List (Nat × D)} {t : List D}
    (h : canopyLevelStep nodeHash [] s = some (b, t)) : b = [] ∧ t = s := by
  simp only [canopyLevelStep] at h
  obtain ⟨hb, ht⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hb.symm, ht.symm⟩

private theorem canopyLevelStep_single {D : Type} (nodeHash : Nat → D → D → D)
    {u : Nat} {hu : D} {s : List D} {b : List (Nat × D)} {t : List D}
    (h : canopyLevelStep nodeHash [(u, hu)] s = some (b, t)) :
    ∃ c, s = c :: t ∧ b = [(u >>> 1, canopyParentHash nodeHash u hu c)] := by
  simp only [canopyLevelStep] at h
  match s, h with
  | [], h => cases h
  | c :: rest, h =>
    obtain ⟨hb, ht⟩ := Prod.mk.inj (Option.some.inj h)
    subst ht
    exact ⟨c, rfl, hb.symm⟩

private theorem canopyLevelStep_pair {D : Type} (nodeHash : Nat → D → D → D)
    {u v : Nat} {hu hv : D} {tl : List (Nat × D)} {s : List D} {b : List (Nat × D)} {t : List D}
    (hv' : v = u ^^^ 1)
    (h : canopyLevelStep nodeHash ((u, hu) :: (v, hv) :: tl) s = some (b, t)) :
    ∃ act, canopyLevelStep nodeHash tl s = some (act, t) ∧
      b = (u >>> 1, nodeHash (u >>> 1) hu hv) :: act := by
  have hc : (v = u ^^^ 1) = True := eq_true hv'
  simp only [canopyLevelStep, hc, ↓reduceIte] at h
  cases hs : canopyLevelStep nodeHash tl s with
  | none => rw [hs] at h; cases h
  | some r =>
    obtain ⟨act, rest⟩ := r
    rw [hs] at h
    obtain ⟨hb, ht⟩ := Prod.mk.inj (Option.some.inj h)
    subst ht
    exact ⟨act, rfl, hb.symm⟩

private theorem canopyLevelStep_solo {D : Type} (nodeHash : Nat → D → D → D)
    {u v : Nat} {hu hv : D} {tl : List (Nat × D)} {s : List D} {b : List (Nat × D)} {t : List D}
    (hv' : ¬ v = u ^^^ 1)
    (h : canopyLevelStep nodeHash ((u, hu) :: (v, hv) :: tl) s = some (b, t)) :
    ∃ c rest act, s = c :: rest ∧
      canopyLevelStep nodeHash ((v, hv) :: tl) rest = some (act, t) ∧
      b = (u >>> 1, canopyParentHash nodeHash u hu c) :: act := by
  simp only [canopyLevelStep, hv', ↓reduceIte] at h
  match s, h with
  | [], h => cases h
  | c :: rest, h =>
    dsimp only at h
    cases hs : canopyLevelStep nodeHash ((v, hv) :: tl) rest with
    | none => rw [hs] at h; cases h
    | some r =>
      obtain ⟨act, rest'⟩ := r
      rw [hs] at h
      obtain ⟨hb, ht⟩ := Prod.mk.inj (Option.some.inj h)
      subst ht
      exact ⟨c, rest, act, rfl, hs, hb.symm⟩

private theorem canopyLevels_succ {D : Type} (nodeHash : Nat → D → D → D)
    {d : Nat} {a : List (Nat × D)} {s : List D} {b : List (Nat × D)} {t : List D}
    (h : canopyLevels nodeHash (d + 1) a s = some (b, t)) :
    ∃ m r, canopyLevelStep nodeHash a s = some (m, r) ∧ canopyLevels nodeHash d m r = some (b, t) := by
  rw [canopyLevels] at h
  cases hs : canopyLevelStep nodeHash a s with
  | none => rw [hs] at h; cases h
  | some p =>
    obtain ⟨m, r⟩ := p
    rw [hs] at h
    exact ⟨m, r, rfl, h⟩

/-- A successful level step maps the index list by `steinerLevelStep` and consumes exactly the
    number of digests `steinerLevelStep` predicts. -/
private theorem canopyLevelStep_shape {D : Type} (nodeHash : Nat → D → D → D) :
    ∀ (n : Nat) (a : List (Nat × D)) (s : List D) (b : List (Nat × D)) (t : List D),
      a.length < n →
      canopyLevelStep nodeHash a s = some (b, t) →
      b.map Prod.fst = (steinerLevelStep (a.map Prod.fst)).1 ∧
      s.length = (steinerLevelStep (a.map Prod.fst)).2 + t.length := by
  intro n
  induction n with
  | zero => intro a s b t hLen _; exact absurd hLen (Nat.not_lt_zero _)
  | succ n ih =>
    intro a s b t hLen h
    match a, hLen, h with
    | [], _, h =>
      obtain ⟨hb, ht⟩ := canopyLevelStep_nil nodeHash h
      subst hb; subst ht
      exact ⟨rfl, (Nat.zero_add _).symm⟩
    | [(u, hu)], _, h =>
      obtain ⟨c, hs, hb⟩ := canopyLevelStep_single nodeHash h
      subst hs; subst hb
      exact ⟨rfl, Nat.add_comm _ _⟩
    | (u, hu) :: (v, hv) :: tl, hLen, h =>
      have hLen1 : ((v, hv) :: tl).length < n := Nat.lt_of_succ_lt_succ hLen
      have hLen2 : tl.length < n := Nat.lt_of_succ_lt hLen1
      by_cases hv' : v = u ^^^ 1
      · obtain ⟨act, hr, hb⟩ := canopyLevelStep_pair nodeHash hv' h
        obtain ⟨h1, h2⟩ := ih tl s act t hLen2 hr
        subst hb
        have hc : (v = u ^^^ 1) = True := eq_true hv'
        simp only [List.map_cons, steinerLevelStep, hc, ↓reduceIte]
        exact ⟨congrArg (List.cons (u >>> 1)) h1, h2⟩
      · obtain ⟨c, rest, act, hs, hr, hb⟩ := canopyLevelStep_solo nodeHash hv' h
        obtain ⟨h1, h2⟩ := ih ((v, hv) :: tl) rest act t hLen1 hr
        subst hs; subst hb
        simp only [List.map_cons] at h1 h2
        simp only [List.map_cons, steinerLevelStep, hv', ↓reduceIte, List.length_cons]
        refine ⟨congrArg (List.cons (u >>> 1)) h1, ?_⟩
        rw [h2]
        exact Nat.add_right_comm _ _ _

private theorem canopyLevels_count {D : Type} (nodeHash : Nat → D → D → D) :
    ∀ (d : Nat) (a : List (Nat × D)) (s : List D) (b : List (Nat × D)) (t : List D),
      canopyLevels nodeHash d a s = some (b, t) →
      s.length = steinerCountLevels d (a.map Prod.fst) + t.length
  | 0, a, s, b, t, h => by
    rw [canopyLevels] at h
    obtain ⟨_, ht⟩ := Prod.mk.inj (Option.some.inj h)
    subst ht
    exact (Nat.zero_add _).symm
  | d + 1, a, s, b, t, h => by
    obtain ⟨m, r, hStep, hRest⟩ := canopyLevels_succ nodeHash h
    obtain ⟨hm, hLen⟩ := canopyLevelStep_shape nodeHash _ a s m r (Nat.lt_succ_self _) hStep
    have ih := canopyLevels_count nodeHash d m r b t hRest
    rw [hm] at ih
    rw [steinerCountLevels, hLen, ih]
    exact (Nat.add_assoc _ _ _).symm

private theorem canopy_map_fst {D : Type} (n : Nat) :
    ∀ (leaves : List (Nat × D)),
      (leaves.map (fun p => (n + p.1, p.2))).map Prod.fst =
        (leaves.map Prod.fst).map (fun i => n + i)
  | [] => rfl
  | p :: tl => congrArg (List.cons (n + p.1)) (canopy_map_fst n tl)

private theorem canopy_lift_inj {D : Type} (n : Nat) :
    ∀ (l1 l2 : List (Nat × D)),
      l1.map (fun p => (n + p.1, p.2)) = l2.map (fun p => (n + p.1, p.2)) → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | p :: t1, q :: t2, h => by
    have h' : (n + p.1, p.2) :: t1.map (fun p => (n + p.1, p.2)) =
        (n + q.1, q.2) :: t2.map (fun p => (n + p.1, p.2)) := h
    obtain ⟨hh, ht⟩ := List.cons.inj h'
    obtain ⟨h1, h2⟩ := Prod.mk.inj hh
    rw [canopy_lift_inj n t1 t2 ht]
    exact congrArg (fun x => x :: t2) (Prod.ext (Nat.add_left_cancel h1) h2)

private theorem canopy_accept_unpack {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D)
    (h : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    ∃ top, canopyLevels nodeHash logLeaves
        (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof = some ([(1, top)], []) ∧
      rootHash logLeaves top = commitment := by
  unfold verifyCanopyMultiproof at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hM⟩ := h
  split at hM
  next u top hEq =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hM
    obtain ⟨hu, hR⟩ := hM
    subst hu
    exact ⟨top, hEq, hR⟩
  next => cases hM

/-- **Exact sibling consumption is determined by the index set alone.** Whatever the hash
    functions, leaf digests and commitment, an accepted multiproof carries exactly
    `steinerSiblingCount logLeaves indices` authentication siblings. -/
theorem verifyCanopyMultiproof_exact_sibling_count {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    proof.length = steinerSiblingCount logLeaves (leaves.map Prod.fst) := by
  obtain ⟨top, hL, _⟩ := canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
  have hCount := canopyLevels_count nodeHash logLeaves _ proof _ _ hL
  rw [canopy_map_fst] at hCount
  exact hCount

/-- Two proofs of different lengths for the same index list are never both accepted, for any
    hash functions, commitments and leaf digests. -/
theorem verifyCanopyMultiproof_length_mismatch_rejected {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment commitment' : D)
    (leaves leaves' : List (Nat × D)) (proof proof' : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true)
    (hIdx : leaves'.map Prod.fst = leaves.map Prod.fst)
    (hLen : proof'.length ≠ proof.length) :
    verifyCanopyMultiproof nodeHash rootHash logLeaves commitment' leaves' proof' = false := by
  apply Bool.eq_false_iff.mpr
  intro hAcc'
  apply hLen
  rw [verifyCanopyMultiproof_exact_sibling_count nodeHash rootHash logLeaves commitment' leaves' proof' hAcc',
    verifyCanopyMultiproof_exact_sibling_count nodeHash rootHash logLeaves commitment leaves proof hAcc, hIdx]

/-- **Extra-sibling tooth.** Appending one or more digests to an accepted proof yields a
    rejected proof, for any hash functions. -/
theorem verifyCanopyMultiproof_extra_sibling_rejected {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D)
    (extra : D) (more : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves
      (proof ++ extra :: more) = false := by
  refine verifyCanopyMultiproof_length_mismatch_rejected nodeHash rootHash logLeaves commitment
    commitment leaves leaves proof _ hAcc rfl ?_
  rw [List.length_append, List.length_cons]
  exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (Nat.succ_pos _))

/-- **Missing-sibling tooth.** Dropping the last digest of an accepted nonempty proof yields a
    rejected proof, for any hash functions. -/
theorem verifyCanopyMultiproof_missing_sibling_rejected {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D)
    (hNonempty : proof ≠ [])
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof.dropLast = false := by
  refine verifyCanopyMultiproof_length_mismatch_rejected nodeHash rootHash logLeaves commitment
    commitment leaves leaves proof _ hAcc rfl ?_
  rw [List.length_dropLast]
  exact Nat.ne_of_lt (Nat.sub_lt (List.length_pos_iff.mpr hNonempty) Nat.one_pos)

private theorem canopyNode_binding {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D)
    {i : Nat} {l r l' r' : D} (h : nodeHash i l r = nodeHash i l' r') :
    (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') ∨
    (l = l' ∧ r = r') := by
  by_cases he : (l, r) = (l', r')
  · exact Or.inr (Prod.mk.inj he)
  · exact Or.inl ⟨i, l, r, l', r', he, h⟩

private theorem canopyParentHash_binding {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D)
    {u : Nat} {hu s hu' s' : D}
    (h : canopyParentHash nodeHash u hu s = canopyParentHash nodeHash u hu' s') :
    (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') ∨
    (hu = hu' ∧ s = s') := by
  unfold canopyParentHash at h
  by_cases hp : u &&& 1 = 0
  · simp only [hp, ↓reduceIte] at h
    exact canopyNode_binding nodeHash h
  · simp only [hp, ↓reduceIte] at h
    rcases canopyNode_binding nodeHash h with hc | ⟨e1, e2⟩
    · exact Or.inl hc
    · exact Or.inr ⟨e2, e1⟩

/-- Per-level binding: two successful level steps over the same index list that produce the
    same next level and the same unconsumed siblings either started from identical inputs or
    exhibit a `nodeHash` collision. -/
private theorem canopyLevelStep_binding {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D) :
    ∀ (n : Nat) (a1 a2 : List (Nat × D)) (s1 s2 : List D) (b : List (Nat × D)) (t : List D),
      a1.length < n →
      a1.map Prod.fst = a2.map Prod.fst →
      canopyLevelStep nodeHash a1 s1 = some (b, t) →
      canopyLevelStep nodeHash a2 s2 = some (b, t) →
      (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') ∨
      (a1 = a2 ∧ s1 = s2) := by
  intro n
  induction n with
  | zero => intro a1 a2 s1 s2 b t hLen _ _ _; exact absurd hLen (Nat.not_lt_zero _)
  | succ n ih =>
    intro a1 a2 s1 s2 b t hLen hIdx h1 h2
    match a1, a2, hLen, hIdx, h1, h2 with
    | [], [], _, _, h1, h2 =>
      obtain ⟨_, ht1⟩ := canopyLevelStep_nil nodeHash h1
      obtain ⟨_, ht2⟩ := canopyLevelStep_nil nodeHash h2
      exact Or.inr ⟨rfl, ht1.symm.trans ht2⟩
    | [], _ :: _, _, hIdx, _, _ => cases hIdx
    | _ :: _, [], _, hIdx, _, _ => cases hIdx
    | [(u, hu)], [(u2, hu2)], _, hIdx, h1, h2 =>
      have hu_eq : u = u2 := (List.cons.inj hIdx).1
      subst hu_eq
      obtain ⟨c1, hs1, hb1⟩ := canopyLevelStep_single nodeHash h1
      obtain ⟨c2, hs2, hb2⟩ := canopyLevelStep_single nodeHash h2
      have hH := (Prod.mk.inj (List.cons.inj (hb1.symm.trans hb2)).1).2
      rcases canopyParentHash_binding nodeHash hH with hc | ⟨e1, e2⟩
      · exact Or.inl hc
      · subst e1; subst e2; subst hs1; subst hs2
        exact Or.inr ⟨rfl, rfl⟩
    | [_], _ :: _ :: _, _, hIdx, _, _ => cases (List.cons.inj hIdx).2
    | _ :: _ :: _, [_], _, hIdx, _, _ => cases (List.cons.inj hIdx).2
    | (u, hu) :: (v, hv) :: tl1, (u2, hu2) :: (v2, hv2) :: tl2, hLen, hIdx, h1, h2 =>
      have hu_eq : u = u2 := (List.cons.inj hIdx).1
      have hv_eq : v = v2 := (List.cons.inj (List.cons.inj hIdx).2).1
      have hTl : tl1.map Prod.fst = tl2.map Prod.fst := (List.cons.inj (List.cons.inj hIdx).2).2
      subst hu_eq; subst hv_eq
      have hLen1 : ((v, hv) :: tl1).length < n := Nat.lt_of_succ_lt_succ hLen
      have hLen2 : tl1.length < n := Nat.lt_of_succ_lt hLen1
      by_cases hv' : v = u ^^^ 1
      · obtain ⟨act1, hr1, hb1⟩ := canopyLevelStep_pair nodeHash hv' h1
        obtain ⟨act2, hr2, hb2⟩ := canopyLevelStep_pair nodeHash hv' h2
        obtain ⟨hHead, hAct⟩ := List.cons.inj (hb1.symm.trans hb2)
        subst hAct
        rcases canopyNode_binding nodeHash (Prod.mk.inj hHead).2 with hc | ⟨e1, e2⟩
        · exact Or.inl hc
        · rcases ih tl1 tl2 s1 s2 act1 t hLen2 hTl hr1 hr2 with hc | ⟨eT, eS⟩
          · exact Or.inl hc
          · subst e1; subst e2; subst eT; subst eS
            exact Or.inr ⟨rfl, rfl⟩
      · obtain ⟨c1, r1, act1, hs1, hr1, hb1⟩ := canopyLevelStep_solo nodeHash hv' h1
        obtain ⟨c2, r2, act2, hs2, hr2, hb2⟩ := canopyLevelStep_solo nodeHash hv' h2
        obtain ⟨hHead, hAct⟩ := List.cons.inj (hb1.symm.trans hb2)
        subst hAct
        rcases canopyParentHash_binding nodeHash (Prod.mk.inj hHead).2 with hc | ⟨e1, e2⟩
        · exact Or.inl hc
        · rcases ih ((v, hv) :: tl1) ((v, hv2) :: tl2) r1 r2 act1 t hLen1
              (congrArg (List.cons v) hTl) hr1 hr2 with hc | ⟨eT, eS⟩
          · exact Or.inl hc
          · subst e1; subst e2; subst eS; subst hs1; subst hs2
            exact Or.inr ⟨congrArg (List.cons (u, hu)) eT, rfl⟩

/-- Binding of the whole level iteration: equal final state and equal starting index list force
    equal starting digests and equal sibling lists, or a `nodeHash` collision. -/
private theorem canopyLevels_binding {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D) :
    ∀ (d : Nat) (a1 a2 : List (Nat × D)) (s1 s2 : List D) (b : List (Nat × D)) (t : List D),
      a1.map Prod.fst = a2.map Prod.fst →
      canopyLevels nodeHash d a1 s1 = some (b, t) →
      canopyLevels nodeHash d a2 s2 = some (b, t) →
      (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') ∨
      (a1 = a2 ∧ s1 = s2)
  | 0, a1, a2, s1, s2, b, t, _, h1, h2 => by
    rw [canopyLevels] at h1 h2
    obtain ⟨ha, hs⟩ := Prod.mk.inj (Option.some.inj (h1.trans h2.symm))
    exact Or.inr ⟨ha, hs⟩
  | d + 1, a1, a2, s1, s2, b, t, hIdx, h1, h2 => by
    obtain ⟨m1, r1, hStep1, hRest1⟩ := canopyLevels_succ nodeHash h1
    obtain ⟨m2, r2, hStep2, hRest2⟩ := canopyLevels_succ nodeHash h2
    have hm1 := (canopyLevelStep_shape nodeHash _ a1 s1 m1 r1 (Nat.lt_succ_self _) hStep1).1
    have hm2 := (canopyLevelStep_shape nodeHash _ a2 s2 m2 r2 (Nat.lt_succ_self _) hStep2).1
    rw [hIdx] at hm1
    rcases canopyLevels_binding nodeHash d m1 m2 r1 r2 b t (hm1.trans hm2.symm) hRest1 hRest2
      with hc | ⟨eM, eR⟩
    · exact Or.inl hc
    · subst eM; subst eR
      exact canopyLevelStep_binding nodeHash _ a1 a2 s1 s2 m1 r1 (Nat.lt_succ_self _) hIdx
        hStep1 hStep2

/-- **Binding of the Steiner multiproof verifier (collision extraction).** If two distinct
    openings `(leaves₁, proof₁) ≠ (leaves₂, proof₂)` of the same index list are both accepted
    against the same commitment, then either `rootHash` collides on two distinct top nodes, or
    `nodeHash` collides at one node index on two distinct `(left, right)` pairs. -/
theorem verifyCanopyMultiproof_binding {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (leaves₁ leaves₂ : List (Nat × D)) (proof₁ proof₂ : List D)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (hAcc₁ : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves₁ proof₁ = true)
    (hAcc₂ : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves₂ proof₂ = true)
    (hNe : (leaves₁, proof₁) ≠ (leaves₂, proof₂)) :
    (∃ top₁ top₂ : D, top₁ ≠ top₂ ∧ rootHash logLeaves top₁ = rootHash logLeaves top₂) ∨
    (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') := by
  obtain ⟨top1, hL1, hR1⟩ :=
    canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₁ proof₁ hAcc₁
  obtain ⟨top2, hL2, hR2⟩ :=
    canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₂ proof₂ hAcc₂
  by_cases hTop : top1 = top2
  · subst hTop
    have hIdx' : (leaves₁.map (fun p => (2 ^ logLeaves + p.1, p.2))).map Prod.fst =
        (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))).map Prod.fst := by
      rw [canopy_map_fst, canopy_map_fst, hIdx]
    rcases canopyLevels_binding nodeHash logLeaves _ _ proof₁ proof₂ _ _ hIdx' hL1 hL2
      with hc | ⟨eA, eP⟩
    · exact Or.inr hc
    · have eL := canopy_lift_inj (2 ^ logLeaves) leaves₁ leaves₂ eA
      subst eL; subst eP
      exact absurd rfl hNe
  · exact Or.inl ⟨top1, top2, hTop, hR1.trans hR2.symm⟩

/-- **Tampered Steiner multiproof.** Starting from an accepted opening, any change to a leaf
    digest or to the sibling list (same index list, different data) is rejected, unless it
    exhibits a `rootHash` or `nodeHash` collision. -/
theorem verifyCanopyMultiproof_tamper_rejected_or_collision {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (leaves leaves' : List (Nat × D)) (proof proof' : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true)
    (hIdx : leaves'.map Prod.fst = leaves.map Prod.fst)
    (hNe : (leaves', proof') ≠ (leaves, proof)) :
    verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves' proof' = false ∨
    (∃ top₁ top₂ : D, top₁ ≠ top₂ ∧ rootHash logLeaves top₁ = rootHash logLeaves top₂) ∨
    (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') := by
  cases hV : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves' proof' with
  | false => exact Or.inl rfl
  | true =>
    exact Or.inr (verifyCanopyMultiproof_binding nodeHash rootHash logLeaves commitment
      leaves' leaves proof' proof hIdx hV hAcc hNe)


end Qsag


namespace Qsag
/-! ### Constructive collision extraction from two `CanopyMultiProof` transcripts -/

/-- An explicit `nodeHash` collision: one node index, two distinct `(left, right)` pairs, equal
    digests. -/
structure CanopyNodeCollision {D : Type} (nodeHash : Nat → D → D → D) where
  idx : Nat
  l : D
  r : D
  l' : D
  r' : D
  ne : (l, r) ≠ (l', r')
  eq : nodeHash idx l r = nodeHash idx l' r'

/-- An explicit `rootHash` collision on two distinct top nodes. -/
