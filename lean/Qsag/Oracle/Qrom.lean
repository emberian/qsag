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
