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
structure CanopyRootCollision {D : Type} (rootHash : Nat → D → D) (logLeaves : Nat) where
  top₁ : D
  top₂ : D
  ne : top₁ ≠ top₂
  eq : rootHash logLeaves top₁ = rootHash logLeaves top₂

private def canopyNodeExtract {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D)
    {i : Nat} {l r l' r' : D} (h : nodeHash i l r = nodeHash i l' r') :
    PSum (CanopyNodeCollision nodeHash) (l = l' ∧ r = r') :=
  if he : (l, r) = (l', r') then .inr (Prod.mk.inj he) else .inl ⟨i, l, r, l', r', he, h⟩

private def canopyParentExtract {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D)
    {u : Nat} {hu s hu' s' : D}
    (h : canopyParentHash nodeHash u hu s = canopyParentHash nodeHash u hu' s') :
    PSum (CanopyNodeCollision nodeHash) (hu = hu' ∧ s = s') :=
  if hp : u &&& 1 = 0 then
    canopyNodeExtract nodeHash (i := u >>> 1) (l := hu) (r := s) (l' := hu') (r' := s')
      (by unfold canopyParentHash at h; simp only [hp, ↓reduceIte] at h; exact h)
  else
    match canopyNodeExtract nodeHash (i := u >>> 1) (l := s) (r := hu) (l' := s') (r' := hu')
        (by unfold canopyParentHash at h; simp only [hp, ↓reduceIte] at h; exact h) with
    | .inl c => .inl c
    | .inr e => .inr ⟨e.2, e.1⟩

/-- One level of the lockstep walk over two transcripts: either both level inputs agree, or the
    first differing position is returned as a `nodeHash` collision. -/
private def canopyLevelStepExtract {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D) :
    (n : Nat) → (a1 a2 : List (Nat × D)) → (s1 s2 : List D) → (b : List (Nat × D)) →
      (t : List D) → a1.length < n → a1.map Prod.fst = a2.map Prod.fst →
      canopyLevelStep nodeHash a1 s1 = some (b, t) →
      canopyLevelStep nodeHash a2 s2 = some (b, t) →
      PSum (CanopyNodeCollision nodeHash) (a1 = a2 ∧ s1 = s2)
  | 0, _, _, _, _, _, _, hLen, _, _, _ => absurd hLen (Nat.not_lt_zero _)
  | _ + 1, [], [], _, _, _, _, _, _, h1, h2 =>
    .inr ⟨rfl, (canopyLevelStep_nil nodeHash h1).2.symm.trans (canopyLevelStep_nil nodeHash h2).2⟩
  | _ + 1, [], _ :: _, _, _, _, _, _, hIdx, _, _ => by cases hIdx
  | _ + 1, _ :: _, [], _, _, _, _, _, hIdx, _, _ => by cases hIdx
  | _ + 1, [_], _ :: _ :: _, _, _, _, _, _, hIdx, _, _ => by cases (List.cons.inj hIdx).2
  | _ + 1, _ :: _ :: _, [_], _, _, _, _, _, hIdx, _, _ => by cases (List.cons.inj hIdx).2
  | _ + 1, [(u, hu)], [(u2, hu2)], s1, s2, b, t, _, hIdx, h1, h2 => by
    have hu_eq : u = u2 := (List.cons.inj hIdx).1
    subst hu_eq
    match s1, s2, h1, h2 with
    | [], _, h1, _ => exact False.elim (by cases h1)
    | _ :: _, [], _, h2 => exact False.elim (by cases h2)
    | c1 :: r1, c2 :: r2, h1, h2 =>
      have f1 : r1 = t ∧ b = [(u >>> 1, canopyParentHash nodeHash u hu c1)] := by
        obtain ⟨c, hs, hb⟩ := canopyLevelStep_single nodeHash h1
        obtain ⟨hc, hr⟩ := List.cons.inj hs
        rw [hc]
        exact ⟨hr, hb⟩
      have f2 : r2 = t ∧ b = [(u >>> 1, canopyParentHash nodeHash u hu2 c2)] := by
        obtain ⟨c, hs, hb⟩ := canopyLevelStep_single nodeHash h2
        obtain ⟨hc, hr⟩ := List.cons.inj hs
        rw [hc]
        exact ⟨hr, hb⟩
      have hH : canopyParentHash nodeHash u hu c1 = canopyParentHash nodeHash u hu2 c2 :=
        (Prod.mk.inj (List.cons.inj (f1.2.symm.trans f2.2)).1).2
      match canopyParentExtract nodeHash hH with
      | .inl c => exact .inl c
      | .inr e => exact .inr ⟨by rw [e.1], by rw [e.2, f1.1, f2.1]⟩
  | n + 1, (u, hu) :: (v, hv) :: tl1, (u2, hu2) :: (v2, hv2) :: tl2, s1, s2, b, t,
      hLen, hIdx, h1, h2 => by
    have hu_eq : u = u2 := (List.cons.inj hIdx).1
    have hv_eq : v = v2 := (List.cons.inj (List.cons.inj hIdx).2).1
    have hTl : tl1.map Prod.fst = tl2.map Prod.fst := (List.cons.inj (List.cons.inj hIdx).2).2
    subst hu_eq; subst hv_eq
    have hLen1 : ((v, hv) :: tl1).length < n := Nat.lt_of_succ_lt_succ hLen
    have hLen2 : tl1.length < n := Nat.lt_of_succ_lt hLen1
    refine if hv' : v = u ^^^ 1 then ?_ else ?_
    · have f1 : canopyLevelStep nodeHash tl1 s1 = some (b.tail, t) ∧
          b = (u >>> 1, nodeHash (u >>> 1) hu hv) :: b.tail := by
        obtain ⟨act, hr, hb⟩ := canopyLevelStep_pair nodeHash hv' h1
        rw [hb]
        exact ⟨hr, rfl⟩
      have f2 : canopyLevelStep nodeHash tl2 s2 = some (b.tail, t) ∧
          b = (u >>> 1, nodeHash (u >>> 1) hu2 hv2) :: b.tail := by
        obtain ⟨act, hr, hb⟩ := canopyLevelStep_pair nodeHash hv' h2
        rw [hb]
        exact ⟨hr, rfl⟩
      have hHead : nodeHash (u >>> 1) hu hv = nodeHash (u >>> 1) hu2 hv2 :=
        (Prod.mk.inj (List.cons.inj (f1.2.symm.trans f2.2)).1).2
      match canopyNodeExtract nodeHash hHead with
      | .inl c => exact .inl c
      | .inr e =>
        match canopyLevelStepExtract nodeHash n tl1 tl2 s1 s2 b.tail t hLen2 hTl f1.1 f2.1 with
        | .inl c => exact .inl c
        | .inr e' => exact .inr ⟨by rw [e.1, e.2, e'.1], e'.2⟩
    · match s1, s2, h1, h2 with
      | [], _, h1, _ =>
        exact False.elim (by
          obtain ⟨_, _, _, hs, _, _⟩ := canopyLevelStep_solo nodeHash hv' h1
          cases hs)
      | _ :: _, [], _, h2 =>
        exact False.elim (by
          obtain ⟨_, _, _, hs, _, _⟩ := canopyLevelStep_solo nodeHash hv' h2
          cases hs)
      | c1 :: r1, c2 :: r2, h1, h2 =>
        have f1 : canopyLevelStep nodeHash ((v, hv) :: tl1) r1 = some (b.tail, t) ∧
            b = (u >>> 1, canopyParentHash nodeHash u hu c1) :: b.tail := by
          obtain ⟨c, rest, act, hs, hr, hb⟩ := canopyLevelStep_solo nodeHash hv' h1
          obtain ⟨hc, hrest⟩ := List.cons.inj hs
          rw [hb, hc, hrest]
          exact ⟨hr, rfl⟩
        have f2 : canopyLevelStep nodeHash ((v, hv2) :: tl2) r2 = some (b.tail, t) ∧
            b = (u >>> 1, canopyParentHash nodeHash u hu2 c2) :: b.tail := by
          obtain ⟨c, rest, act, hs, hr, hb⟩ := canopyLevelStep_solo nodeHash hv' h2
          obtain ⟨hc, hrest⟩ := List.cons.inj hs
          rw [hb, hc, hrest]
          exact ⟨hr, rfl⟩
        have hHead : canopyParentHash nodeHash u hu c1 = canopyParentHash nodeHash u hu2 c2 :=
          (Prod.mk.inj (List.cons.inj (f1.2.symm.trans f2.2)).1).2
        match canopyParentExtract nodeHash hHead with
        | .inl c => exact .inl c
        | .inr e =>
          match canopyLevelStepExtract nodeHash n ((v, hv) :: tl1) ((v, hv2) :: tl2) r1 r2
              b.tail t hLen1 (congrArg (List.cons v) hTl) f1.1 f2.1 with
          | .inl c => exact .inl c
          | .inr e' => exact .inr ⟨by rw [e.1, e'.1], by rw [e.2, e'.2]⟩

/-- The lockstep walk over all `d` levels, from the common final state back to the leaves. -/
private def canopyLevelsExtract {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D) :
    (d : Nat) → (a1 a2 : List (Nat × D)) → (s1 s2 : List D) → (b : List (Nat × D)) →
      (t : List D) → a1.map Prod.fst = a2.map Prod.fst →
      canopyLevels nodeHash d a1 s1 = some (b, t) →
      canopyLevels nodeHash d a2 s2 = some (b, t) →
      PSum (CanopyNodeCollision nodeHash) (a1 = a2 ∧ s1 = s2)
  | 0, _, _, _, _, _, _, _, h1, h2 => .inr (by
      rw [canopyLevels] at h1 h2
      exact Prod.mk.inj (Option.some.inj (h1.trans h2.symm)))
  | d + 1, a1, a2, s1, s2, b, t, hIdx, h1, h2 => by
    match hs1 : canopyLevelStep nodeHash a1 s1, hs2 : canopyLevelStep nodeHash a2 s2 with
    | none, _ =>
      exact False.elim (by
        obtain ⟨_, _, hStep, _⟩ := canopyLevels_succ nodeHash h1
        rw [hs1] at hStep
        cases hStep)
    | some _, none =>
      exact False.elim (by
        obtain ⟨_, _, hStep, _⟩ := canopyLevels_succ nodeHash h2
        rw [hs2] at hStep
        cases hStep)
    | some (m1, r1), some (m2, r2) =>
      have hRest1 : canopyLevels nodeHash d m1 r1 = some (b, t) := by
        obtain ⟨m, r, hStep, hRest⟩ := canopyLevels_succ nodeHash h1
        rw [hs1] at hStep
        obtain ⟨hm, hr⟩ := Prod.mk.inj (Option.some.inj hStep)
        rw [hm, hr]
        exact hRest
      have hRest2 : canopyLevels nodeHash d m2 r2 = some (b, t) := by
        obtain ⟨m, r, hStep, hRest⟩ := canopyLevels_succ nodeHash h2
        rw [hs2] at hStep
        obtain ⟨hm, hr⟩ := Prod.mk.inj (Option.some.inj hStep)
        rw [hm, hr]
        exact hRest
      have hm1 := (canopyLevelStep_shape nodeHash _ a1 s1 m1 r1 (Nat.lt_succ_self _) hs1).1
      have hm2 := (canopyLevelStep_shape nodeHash _ a2 s2 m2 r2 (Nat.lt_succ_self _) hs2).1
      rw [hIdx] at hm1
      match canopyLevelsExtract nodeHash d m1 m2 r1 r2 b t (hm1.trans hm2.symm) hRest1 hRest2 with
      | .inl c => exact .inl c
      | .inr e =>
        have hs2' : canopyLevelStep nodeHash a2 s2 = some (m1, r1) := by
          rw [hs2, e.1, e.2]
        exact canopyLevelStepExtract nodeHash _ a1 a2 s1 s2 m1 r1 (Nat.lt_succ_self _) hIdx
          hs1 hs2'

private def canopyTopOf {D : Type} (r : Option (List (Nat × D) × List D)) : Option D :=
  match r with
  | some ([(_, top)], []) => some top
  | _ => none

/-- **Constructive collision extractor over `CanopyMultiProof` transcripts.** Given two accepted
    openings of one index set against one commitment that differ in a leaf digest or a sibling,
    the function walks both transcripts level by level and returns an explicit collision: of
    `rootHash` on the two top nodes, or of `nodeHash` at the first node where the two
    transcripts hash different children to the same parent. The result is data in `Type`, built
    with `DecidableEq D` only. -/
def extractCanopyCollision {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (leaves₁ leaves₂ : List (Nat × D)) (proof₁ proof₂ : List D)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (hAcc₁ : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves₁ proof₁ = true)
    (hAcc₂ : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves₂ proof₂ = true)
    (hNe : (leaves₁, proof₁) ≠ (leaves₂, proof₂)) :
    PSum (CanopyRootCollision rootHash logLeaves) (CanopyNodeCollision nodeHash) := by
  match hT1 : canopyTopOf (canopyLevels nodeHash logLeaves
        (leaves₁.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₁),
      hT2 : canopyTopOf (canopyLevels nodeHash logLeaves
        (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₂) with
  | none, _ =>
    exact False.elim (by
      obtain ⟨top, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₁ proof₁ hAcc₁
      rw [hL] at hT1
      cases hT1)
  | some _, none =>
    exact False.elim (by
      obtain ⟨top, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₂ proof₂ hAcc₂
      rw [hL] at hT2
      cases hT2)
  | some top1, some top2 =>
    have hL1 : canopyLevels nodeHash logLeaves
          (leaves₁.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₁ = some ([(1, top1)], []) ∧
        rootHash logLeaves top1 = commitment := by
      obtain ⟨top, hL, hR⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₁ proof₁ hAcc₁
      rw [hL] at hT1
      have hEq : some top = some top1 := hT1
      rw [← Option.some.inj hEq]
      exact ⟨hL, hR⟩
    have hL2 : canopyLevels nodeHash logLeaves
          (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₂ = some ([(1, top2)], []) ∧
        rootHash logLeaves top2 = commitment := by
      obtain ⟨top, hL, hR⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₂ proof₂ hAcc₂
      rw [hL] at hT2
      have hEq : some top = some top2 := hT2
      rw [← Option.some.inj hEq]
      exact ⟨hL, hR⟩
    refine if hTop : top1 = top2 then ?_ else .inl ⟨top1, top2, hTop, hL1.2.trans hL2.2.symm⟩
    have hL2' : canopyLevels nodeHash logLeaves
        (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₂ = some ([(1, top1)], []) := by
      rw [hTop]; exact hL2.1
    have hIdx' : (leaves₁.map (fun p => (2 ^ logLeaves + p.1, p.2))).map Prod.fst =
        (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))).map Prod.fst := by
      rw [canopy_map_fst, canopy_map_fst, hIdx]
    match canopyLevelsExtract nodeHash logLeaves _ _ proof₁ proof₂ _ _ hIdx' hL1.1 hL2' with
    | .inl c => exact .inr c
    | .inr e =>
      exact False.elim (hNe (by
        rw [canopy_lift_inj (2 ^ logLeaves) leaves₁ leaves₂ e.1, e.2]))


end Qsag


namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Pre-Challenge Online Extraction for Position-Tweaked `merkleRootFromPath` -/

/-- Constructive first-match lookup avoiding opaque library lemma dependencies. -/
def findFirst {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x = true then some x else findFirst p xs

theorem findFirst_some_spec {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {x : α}, findFirst p xs = some x → x ∈ xs ∧ p x = true
  | [], _, h => by cases h
  | y :: ys, x, h => by
    unfold findFirst at h
    cases hp : p y
    · rw [hp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases findFirst_some_spec p h with ⟨hm, hpx⟩
      exact ⟨.tail y hm, hpx⟩
    · rw [hp] at h; simp only [↓reduceIte, Option.some.injEq] at h
      subst h; exact ⟨.head ys, hp⟩

theorem findFirst_none_spec {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, findFirst p xs = none → ∀ x ∈ xs, p x = false
  | [], _, _, hx => nomatch hx
  | y :: ys, h, x, hx => by
    unfold findFirst at h
    cases hp : p y
    · rw [hp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases List.mem_cons.mp hx with rfl | htl
      · exact hp
      · exact findFirst_none_spec p h x htl
    · rw [hp] at h; simp only [↓reduceIte] at h; cases h

/-- One recorded compression query `(lvl, node, left, right) ↦ out` in a classical
    pre-challenge query table. Coherent QROM access does not itself provide such a record. -/
structure RecordedMerkleQuery (D : Type) where
  lvl : Nat
  node : Nat
  left : D
  right : D
  out : D
  deriving DecidableEq, Repr

/-- Consistency of a recorded query entry with compression oracle `H`. -/
@[expose] def merkleQueryConsistent {D : Type} (H : Nat → Nat → D → D → D)
    (q : RecordedMerkleQuery D) : Prop :=
  H q.lvl q.node q.left q.right = q.out

/-- Child digests `{q.left, q.right | q ∈ queries}` appearing in a recorded `Q`-query table. -/
def merkleChildTargets {D : Type} : List (RecordedMerkleQuery D) → List D
  | [] => []
  | q :: qs => q.left :: q.right :: merkleChildTargets qs

/-- Full pre-challenge target set `rt :: merkleChildTargets queries` (length `2 * Q + 1`). -/
def merklePreChallengeTargets {D : Type} (rt : D) (queries : List (RecordedMerkleQuery D)) :
    List D :=
  rt :: merkleChildTargets queries

theorem merkleChildTargets_length {D : Type} :
    ∀ (qs : List (RecordedMerkleQuery D)), (merkleChildTargets qs).length = 2 * qs.length
  | [] => rfl
  | _ :: qs => by
    simp only [merkleChildTargets, List.length_cons, merkleChildTargets_length qs]; omega

theorem merklePreChallengeTargets_length {D : Type} (rt : D)
    (qs : List (RecordedMerkleQuery D)) :
    (merklePreChallengeTargets rt qs).length = 2 * qs.length + 1 := by
  simp only [merklePreChallengeTargets, List.length_cons, merkleChildTargets_length]

private theorem mem_merkleChildTargets_of_mem {D : Type}
    {q : RecordedMerkleQuery D} {qs : List (RecordedMerkleQuery D)} (hq : q ∈ qs) :
    q.left ∈ merkleChildTargets qs ∧ q.right ∈ merkleChildTargets qs := by
  induction qs with
  | nil => nomatch hq
  | cons hd tl ih =>
    rcases List.mem_cons.mp hq with rfl | htl
    · exact ⟨.head _, .tail _ (.head _)⟩
    · rcases ih htl with ⟨hl, hr⟩
      exact ⟨.tail _ (.tail _ hl), .tail _ (.tail _ hr)⟩

/-- **Pre-challenge online opening extractor** for `merkleRootFromPath`: reconstructs `(leaf, path)`
    solely from `(rt, queries)` and `(lvl, depth, idx)` BEFORE any challenge is squeezed. -/
@[expose] def extractOnlineMerkleOpening {D : Type} [DecidableEq D]
    (rt : D) (queries : List (RecordedMerkleQuery D)) :
    Nat → Nat → Nat → Option (D × List D)
  | _, 0, _ => some (rt, [])
  | lvl, depth + 1, idx =>
    match extractOnlineMerkleOpening rt queries (lvl + 1) depth (idx / 2) with
    | none => none
    | some (parent, restPath) =>
      match findFirst (fun q =>
          decide (q.lvl = lvl) && decide (q.node = idx / 2) && decide (q.out = parent)) queries with
      | none => none
      | some q =>
        if idx % 2 = 0 then some (q.left, q.right :: restPath)
        else some (q.right, q.left :: restPath)

private theorem extractOnlineMerkleOpening_succ_child {D : Type} [DecidableEq D]
    (rt : D) (queries : List (RecordedMerkleQuery D))
    (lvl depth idx : Nat) (val : D) (pth : List D)
    (h : extractOnlineMerkleOpening rt queries lvl (depth + 1) idx = some (val, pth)) :
    val ∈ merkleChildTargets queries := by
  unfold extractOnlineMerkleOpening at h
  cases hUp : extractOnlineMerkleOpening rt queries (lvl + 1) depth (idx / 2) with
  | none => rw [hUp] at h; cases h
  | some pr =>
    rw [hUp] at h; dsimp only at h
    cases hFind : findFirst (fun q =>
        decide (q.lvl = lvl) && decide (q.node = idx / 2) && decide (q.out = pr.1)) queries with
    | none => rw [hFind] at h; cases h
    | some q =>
      rw [hFind] at h; dsimp only at h
      rcases mem_merkleChildTargets_of_mem (findFirst_some_spec _ hFind).1 with ⟨hL, hR⟩
      by_cases hPar : idx % 2 = 0
      · simp only [hPar, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact hL
      · simp only [hPar, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact hR

/-- `Type`-valued 4-way constructive online-extraction outcome for `merkleRootFromPath`. -/
inductive OnlineMerkleOutcome {D : Type} [DecidableEq D]
    (H : Nat → Nat → D → D → D) (rt : D) (queries : List (RecordedMerkleQuery D))
    (lvl depth idx : Nat) (leaf : D) (path : List D) : Type where
  | extractedEq
      (hExt : extractOnlineMerkleOpening rt queries lvl depth idx = some (leaf, path))
  | queryCollision
      (lvlC nodeC : Nat) (a b a' b' : D)
      (hNe : (a, b) ≠ (a', b'))
      (hEq : H lvlC nodeC a b = H lvlC nodeC a' b')
  | unqueriedRootPreimage
      (lvlU nodeU : Nat) (lU rU : D)
      (hOut : H lvlU nodeU lU rU = rt)
      (hUnq : ∀ q ∈ queries, ¬(q.lvl = lvlU ∧ q.node = nodeU ∧ q.left = lU ∧ q.right = rU))
  | unqueriedChildPreimage
      (lvlU nodeU : Nat) (lU rU outU : D)
      (hOut : H lvlU nodeU lU rU = outU)
      (hMem : outU ∈ merkleChildTargets queries)
      (hUnq : ∀ q ∈ queries, ¬(q.lvl = lvlU ∧ q.node = nodeU ∧ q.left = lU ∧ q.right = rU))

/-- Every `.queryCollision` branch immediately witnesses `MerkleTweakCollision H`. -/
theorem onlineMerkleOutcome_collision_sound {D : Type} [DecidableEq D]
    {H : Nat → Nat → D → D → D} {lvlC nodeC : Nat} {a b a' b' : D}
    (hNe : (a, b) ≠ (a', b')) (hEq : H lvlC nodeC a b = H lvlC nodeC a' b') :
    MerkleTweakCollision H :=
  ⟨lvlC, nodeC, a, b, a', b',
    if ha : a = a' then .inr (fun hb => hNe (Prod.ext ha hb)) else .inl ha, hEq⟩

/-- **Constructive `Type`-valued online Merkle query-table classifier** (`0 Classical.choice`). -/
def classifyOnlineMerkleOpening {D : Type} [DecidableEq D]
    (H : Nat → Nat → D → D → D) (rt : D) (queries : List (RecordedMerkleQuery D))
    (hCons : ∀ q ∈ queries, merkleQueryConsistent H q) :
    (lvl idx : Nat) → (leaf : D) → (path : List D) →
      merkleRootFromPath H lvl idx leaf path = rt →
      OnlineMerkleOutcome H rt queries lvl path.length idx leaf path
  | lvl, idx, leaf, [], hRoot =>
    .extractedEq (by have hEq : leaf = rt := hRoot; subst hEq; rfl)
  | lvl, idx, leaf, sib :: rest, hRoot => by
    let lCh := if idx % 2 = 0 then leaf else sib
    let rCh := if idx % 2 = 0 then sib else leaf
    let parent := H lvl (idx / 2) lCh rCh
    have hStepEq : (if idx % 2 = 0 then H lvl (idx / 2) leaf sib else H lvl (idx / 2) sib leaf) =
        parent := by
      dsimp only [parent, lCh, rCh]; by_cases hp : idx % 2 = 0 <;> simp [hp]
    have hRestRoot : merkleRootFromPath H (lvl + 1) (idx / 2) parent rest = rt := by
      unfold merkleRootFromPath at hRoot; rwa [hStepEq] at hRoot
    match classifyOnlineMerkleOpening H rt queries hCons (lvl + 1) (idx / 2) parent rest hRestRoot with
    | .queryCollision lc nc a b a' b' hNe hEq =>
      exact .queryCollision lc nc a b a' b' hNe hEq
    | .unqueriedRootPreimage lu nu lU rU hOut hUnq =>
      exact .unqueriedRootPreimage lu nu lU rU hOut hUnq
    | .unqueriedChildPreimage lu nu lU rU outU hOut hMem hUnq =>
      exact .unqueriedChildPreimage lu nu lU rU outU hOut hMem hUnq
    | .extractedEq hExtUp =>
      let pred := fun q : RecordedMerkleQuery D =>
        decide (q.lvl = lvl) && decide (q.node = idx / 2) && decide (q.out = parent)
      match hFind : findFirst pred queries with
      | none =>
        have hUnq : ∀ q ∈ queries, ¬(q.lvl = lvl ∧ q.node = idx / 2 ∧ q.left = lCh ∧ q.right = rCh) := by
          intro q hq ⟨hL, hN, hLc, hRc⟩
          have hFalse := findFirst_none_spec pred hFind q hq
          have hOutEq : q.out = parent := by
            have hc := hCons q hq; unfold merkleQueryConsistent at hc
            rw [← hc, hL, hN, hLc, hRc]
          dsimp only [pred] at hFalse
          simp only [hL, hN, hOutEq, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
        match rest, hExtUp with
        | [], hUp0 =>
          have hParRt : parent = rt := by
            simp only [List.length_nil, extractOnlineMerkleOpening,
              Option.some.injEq, Prod.mk.injEq] at hUp0
            exact hUp0.1.symm
          exact .unqueriedRootPreimage lvl (idx / 2) lCh rCh hParRt hUnq
        | _ :: tlRest, hUpS =>
          exact .unqueriedChildPreimage lvl (idx / 2) lCh rCh parent rfl
            (extractOnlineMerkleOpening_succ_child rt queries (lvl + 1) tlRest.length
              (idx / 2) parent _ hUpS) hUnq
      | some q =>
        rcases findFirst_some_spec pred hFind with ⟨hqMem, hqPred⟩
        dsimp only [pred] at hqPred
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hqPred
        rcases hqPred with ⟨⟨hqLvl, hqNode⟩, hqOut⟩
        if hPairEq : (q.left, q.right) = (lCh, rCh) then
          exact .extractedEq (by
            have hqL : q.left = lCh := (Prod.mk.inj hPairEq).1
            have hqR : q.right = rCh := (Prod.mk.inj hPairEq).2
            show extractOnlineMerkleOpening rt queries lvl (rest.length + 1) idx =
              some (leaf, sib :: rest)
            unfold extractOnlineMerkleOpening
            rw [hExtUp]; dsimp only; rw [hFind]; dsimp only
            by_cases hp : idx % 2 = 0 <;>
              (dsimp only [lCh, rCh] at hqL hqR; simp only [hp, ↓reduceIte] at hqL hqR ⊢; rw [hqL, hqR]))
        else
          have hColl : H lvl (idx / 2) q.left q.right = H lvl (idx / 2) lCh rCh := by
            have hc := hCons q hqMem; unfold merkleQueryConsistent at hc
            rw [← hqLvl, ← hqNode, hc, hqOut]; dsimp only [parent]; rw [hqLvl, hqNode]
          exact .queryCollision lvl (idx / 2) q.left q.right lCh rCh hPairEq hColl

/-- **Pre-challenge binding of online extraction**: any two openings `(leaf₁, path₁)` and
    `(leaf₂, path₂)` at `(lvl, depth, idx)` landing in `.extractedEq` coincide identically. -/
theorem onlineMerkle_preChallenge_unique {D : Type} [DecidableEq D]
    (rt : D) (queries : List (RecordedMerkleQuery D))
    (lvl depth idx : Nat) (leaf₁ leaf₂ : D) (path₁ path₂ : List D)
    (h₁ : extractOnlineMerkleOpening rt queries lvl depth idx = some (leaf₁, path₁))
    (h₂ : extractOnlineMerkleOpening rt queries lvl depth idx = some (leaf₂, path₂)) :
    leaf₁ = leaf₂ ∧ path₁ = path₂ :=
  Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))

/-! ## §2. Pre-Challenge Online Extraction for `verifyCanopyMultiproof` (`pcs.rs`) -/

/-- Recorded `rootHash(logLeaves, top) ↦ out` query for `CanopyMultiProof`. -/
structure RecordedCanopyRootQuery (D : Type) where
  logLeaves : Nat
  top : D
  out : D
  deriving DecidableEq, Repr

/-- Recorded `nodeHash(idx, left, right) ↦ out` query for `CanopyMultiProof`. -/
structure RecordedCanopyNodeQuery (D : Type) where
  idx : Nat
  left : D
  right : D
  out : D
  deriving DecidableEq, Repr

def canopyNodeChildTargets {D : Type} : List (RecordedCanopyNodeQuery D) → List D
  | [] => []
  | q :: qs => q.left :: q.right :: canopyNodeChildTargets qs

theorem canopyNodeChildTargets_length {D : Type} :
    ∀ (qs : List (RecordedCanopyNodeQuery D)), (canopyNodeChildTargets qs).length = 2 * qs.length
  | [] => rfl
  | _ :: qs => by
    simp only [canopyNodeChildTargets, List.length_cons, canopyNodeChildTargets_length qs]; omega

private theorem mem_canopyNodeChildTargets_of_mem {D : Type}
    {q : RecordedCanopyNodeQuery D} {qs : List (RecordedCanopyNodeQuery D)} (hq : q ∈ qs) :
    q.left ∈ canopyNodeChildTargets qs ∧ q.right ∈ canopyNodeChildTargets qs := by
  induction qs with
  | nil => nomatch hq
  | cons hd tl ih =>
    rcases List.mem_cons.mp hq with rfl | htl
    · exact ⟨.head _, .tail _ (.head _)⟩
    · rcases ih htl with ⟨hl, hr⟩
      exact ⟨.tail _ (.tail _ hl), .tail _ (.tail _ hr)⟩

/-- Structural single-level top-down online extractor inverting `canopyLevelStep` using ONLY
    `(nodeQueries, activeIdxs, parents, remSibs)` (fuel = `activeIdxs.length`). -/
def extractOnlineCanopyStep {D : Type} [DecidableEq D]
    (nodeQueries : List (RecordedCanopyNodeQuery D)) :
    Nat → List Nat → List (Nat × D) → List D → Option (List (Nat × D) × List D)
  | 0, [], [], remSibs => some ([], remSibs)
  | _ + 1, [], [], remSibs => some ([], remSibs)
  | _ + 1, [u], [(pIdx, pDig)], remSibs =>
    if pIdx = u >>> 1 then
      match findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries with
      | none => none
      | some q =>
        if u &&& 1 = 0 then some ([(u, q.left)], q.right :: remSibs)
        else some ([(u, q.right)], q.left :: remSibs)
    else none
  | fuel + 1, u :: v :: tl, (pIdx, pDig) :: restParents, remSibs =>
    if pIdx = u >>> 1 then
      if v = u ^^^ 1 then
        match findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries,
              extractOnlineCanopyStep nodeQueries fuel tl restParents remSibs with
        | some q, some (tlAct, fullSibs) =>
          some ((u, q.left) :: (v, q.right) :: tlAct, fullSibs)
        | _, _ => none
      else
        match findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries,
              extractOnlineCanopyStep nodeQueries fuel (v :: tl) restParents remSibs with
        | some q, some (vTlAct, afterUSibs) =>
          if u &&& 1 = 0 then some ((u, q.left) :: vTlAct, q.right :: afterUSibs)
          else some ((u, q.right) :: vTlAct, q.left :: afterUSibs)
        | _, _ => none
    else none
  | _, _, _, _ => none

/-- Multi-level top-down online extractor inverting `canopyLevels` from `[(1, top₀)]`. -/
def extractOnlineCanopyLevels {D : Type} [DecidableEq D]
    (nodeQueries : List (RecordedCanopyNodeQuery D)) :
    Nat → List Nat → List (Nat × D) → List D → Option (List (Nat × D) × List D)
  | 0, activeIdxs, topParents, topSibs =>
    if activeIdxs = topParents.map Prod.fst then some (topParents, topSibs) else none
  | d + 1, activeIdxs, topParents, topSibs =>
    let nextIdxs := (steinerLevelStep activeIdxs).1
    match extractOnlineCanopyLevels nodeQueries d nextIdxs topParents topSibs with
    | none => none
    | some (parents, remSibs) =>
      extractOnlineCanopyStep nodeQueries activeIdxs.length activeIdxs parents remSibs

/-- **Pre-challenge online `CanopyMultiProof` extractor**: given `(commitment, rootQueries,
    nodeQueries, logLeaves, indices)`, reconstructs `(leaves, proof)` without seeing the prover's
    post-challenge leaf digests or sibling list. -/
@[expose] def extractOnlineCanopyOpening {D : Type} [DecidableEq D]
    (commitment : D)
    (rootQueries : List (RecordedCanopyRootQuery D))
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (logLeaves : Nat) (indices : List Nat) : Option (List (Nat × D) × List D) :=
  match findFirst (fun q => decide (q.logLeaves = logLeaves) && decide (q.out = commitment))
      rootQueries with
  | none => none
  | some rq =>
    match extractOnlineCanopyLevels nodeQueries logLeaves
        (indices.map (fun i => 2 ^ logLeaves + i)) [(1, rq.top)] [] with
    | none => none
    | some (shiftedLeaves, proof) =>
      some (List.zip indices (shiftedLeaves.map Prod.snd), proof)

private theorem zip_fst_snd_eq {α β : Type} :
    ∀ (xs : List (α × β)), List.zip (xs.map Prod.fst) (xs.map Prod.snd) = xs
  | [] => rfl
  | (_, _) :: tl => congrArg (List.cons _) (zip_fst_snd_eq tl)

private theorem map_snd_shift_eq {D : Type} (off : Nat) :
    ∀ (xs : List (Nat × D)), (xs.map (fun p => (off + p.1, p.2))).map Prod.snd = xs.map Prod.snd
  | [] => rfl
  | (_, _) :: tl => congrArg (List.cons _) (map_snd_shift_eq off tl)

private theorem map_fst_shift_eq {D : Type} (off : Nat) :
    ∀ (xs : List (Nat × D)),
      (xs.map (fun p => (off + p.1, p.2))).map Prod.fst = (xs.map Prod.fst).map (fun i => off + i)
  | [] => rfl
  | (_, _) :: tl => congrArg (List.cons _) (map_fst_shift_eq off tl)

private theorem extractOnlineCanopyStep_targets {D : Type} [DecidableEq D]
    (nodeQueries : List (RecordedCanopyNodeQuery D)) (top₀ : D) :
    ∀ (fuel : Nat) (idxs : List Nat) (parents : List (Nat × D)) (remSibs : List D)
      (act : List (Nat × D)) (sibs : List D),
      extractOnlineCanopyStep nodeQueries fuel idxs parents remSibs = some (act, sibs) →
      ∀ p ∈ act, p.2 ∈ top₀ :: canopyNodeChildTargets nodeQueries
  | 0, [], [], _, act, _, h, p, hp => by
    simp only [extractOnlineCanopyStep, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; nomatch hp
  | 0, _ :: _, _, _, _, _, h, _, _ => by cases h
  | 0, [], _ :: _, _, _, _, h, _, _ => by cases h
  | _ + 1, [], [], _, act, _, h, p, hp => by
    simp only [extractOnlineCanopyStep, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; nomatch hp
  | _ + 1, [], _ :: _, _, _, _, h, _, _ => by cases h
  | _ + 1, [_], [], _, _, _, h, _, _ => by cases h
  | _ + 1, [_], _ :: _ :: _, _, _, _, h, _, _ => by cases h
  | _ + 1, [u], [(pIdx, pDig)], remSibs, act, sibs, h, p, hp => by
    unfold extractOnlineCanopyStep at h
    by_cases hIdx : pIdx = u >>> 1
    · simp only [hIdx, ↓reduceIte] at h
      cases hF : findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries with
      | none => rw [hF] at h; cases h
      | some q =>
        rw [hF] at h; dsimp only at h
        rcases mem_canopyNodeChildTargets_of_mem (findFirst_some_spec _ hF).1 with ⟨hL, hR⟩
        by_cases hp0 : u &&& 1 = 0
        · simp only [hp0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1] at hp; rcases List.mem_singleton.mp hp with rfl; exact .tail _ hL
        · simp only [hp0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1] at hp; rcases List.mem_singleton.mp hp with rfl; exact .tail _ hR
    · simp only [hIdx, ↓reduceIte] at h; cases h
  | _ + 1, _ :: _ :: _, [], _, _, _, h, _, _ => by cases h
  | fuel + 1, u :: v :: tl, (pIdx, pDig) :: restP, remSibs, act, sibs, h, p, hp => by
    unfold extractOnlineCanopyStep at h
    by_cases hIdx : pIdx = u >>> 1
    · simp only [hIdx, ↓reduceIte] at h
      by_cases hv : v = u ^^^ 1
      · simp only [hv, ↓reduceIte] at h
        cases hF : findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries with
        | none => rw [hF] at h; cases h
        | some q =>
          rw [hF] at h
          cases hSub : extractOnlineCanopyStep nodeQueries fuel tl restP remSibs with
          | none => rw [hSub] at h; cases h
          | some sub =>
            rw [hSub] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases mem_canopyNodeChildTargets_of_mem (findFirst_some_spec _ hF).1 with ⟨hL, hR⟩
            rw [← h.1] at hp
            rcases List.mem_cons.mp hp with rfl | hp1
            · exact .tail _ hL
            · rcases List.mem_cons.mp hp1 with rfl | hp2
              · exact .tail _ hR
              · exact extractOnlineCanopyStep_targets nodeQueries top₀ fuel tl restP remSibs
                  sub.1 sub.2 hSub p hp2
      · simp only [hv, ↓reduceIte] at h
        cases hF : findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries with
        | none => rw [hF] at h; cases h
        | some q =>
          rw [hF] at h
          cases hSub : extractOnlineCanopyStep nodeQueries fuel (v :: tl) restP remSibs with
          | none => rw [hSub] at h; cases h
          | some sub =>
            rw [hSub] at h; dsimp only at h
            rcases mem_canopyNodeChildTargets_of_mem (findFirst_some_spec _ hF).1 with ⟨hL, hR⟩
            by_cases hp0 : u &&& 1 = 0
            · simp only [hp0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1] at hp
              rcases List.mem_cons.mp hp with rfl | hp1
              · exact .tail _ hL
              · exact extractOnlineCanopyStep_targets nodeQueries top₀ fuel (v :: tl) restP
                  remSibs sub.1 sub.2 hSub p hp1
            · simp only [hp0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1] at hp
              rcases List.mem_cons.mp hp with rfl | hp1
              · exact .tail _ hR
              · exact extractOnlineCanopyStep_targets nodeQueries top₀ fuel (v :: tl) restP
                  remSibs sub.1 sub.2 hSub p hp1
    · simp only [hIdx, ↓reduceIte] at h; cases h

private theorem extractOnlineCanopyLevels_targets {D : Type} [DecidableEq D]
    (nodeQueries : List (RecordedCanopyNodeQuery D)) (top₀ : D) :
    ∀ (d : Nat) (idxs : List Nat) (act : List (Nat × D)) (sibs : List D),
      extractOnlineCanopyLevels nodeQueries d idxs [(1, top₀)] [] = some (act, sibs) →
      ∀ p ∈ act, p.2 ∈ top₀ :: canopyNodeChildTargets nodeQueries
  | 0, idxs, act, sibs, h, p, hp => by
    unfold extractOnlineCanopyLevels at h
    by_cases hEq : idxs = [(1, top₀)].map Prod.fst
    · simp only [hEq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1] at hp; rcases List.mem_singleton.mp hp with rfl; exact .head _
    · simp only [hEq, ↓reduceIte] at h; cases h
  | d + 1, idxs, act, sibs, h, p, hp => by
    unfold extractOnlineCanopyLevels at h; dsimp only at h
    cases hUp : extractOnlineCanopyLevels nodeQueries d (steinerLevelStep idxs).1 [(1, top₀)] [] with
    | none => rw [hUp] at h; cases h
    | some up =>
      rw [hUp] at h; dsimp only at h
      exact extractOnlineCanopyStep_targets nodeQueries top₀ idxs.length idxs up.1 up.2 act sibs h p hp

/-- `Type`-valued 5-way constructive online extraction outcome for `verifyCanopyMultiproof`. -/
inductive OnlineCanopyOutcome {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (rootQueries : List (RecordedCanopyRootQuery D))
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (leaves : List (Nat × D)) (proof : List D) : Type where
  | extractedEq
      (hExt : extractOnlineCanopyOpening commitment rootQueries nodeQueries logLeaves
        (leaves.map Prod.fst) = some (leaves, proof))
  | rootCollision (c : CanopyRootCollision rootHash logLeaves)
  | nodeCollision (c : CanopyNodeCollision nodeHash)
  | unqueriedRootPreimage
      (topU : D)
      (hOut : rootHash logLeaves topU = commitment)
      (hUnq : ∀ q ∈ rootQueries, ¬(q.logLeaves = logLeaves ∧ q.top = topU))
  | unqueriedNodePreimage
      (top₀ : D) (idxU : Nat) (lU rU outU : D)
      (hRootMem : ∃ rq ∈ rootQueries, rq.logLeaves = logLeaves ∧ rq.top = top₀ ∧ rq.out = commitment)
      (hOut : nodeHash idxU lU rU = outU)
      (hMem : outU ∈ top₀ :: canopyNodeChildTargets nodeQueries)
      (hUnq : ∀ q ∈ nodeQueries, ¬(q.idx = idxU ∧ q.left = lU ∧ q.right = rU))

private inductive StepClassify {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (top₀ : D)
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (fuel : Nat) (active : List (Nat × D)) (sibs : List D)
    (parents : List (Nat × D)) (remSibs : List D) : Type where
  | ok (hExt : extractOnlineCanopyStep nodeQueries fuel (active.map Prod.fst) parents remSibs =
      some (active, sibs))
  | coll (c : CanopyNodeCollision nodeHash)
  | unq (idxU : Nat) (lU rU outU : D)
      (hOut : nodeHash idxU lU rU = outU)
      (hMem : outU ∈ top₀ :: canopyNodeChildTargets nodeQueries)
      (hUnq : ∀ q ∈ nodeQueries, ¬(q.idx = idxU ∧ q.left = lU ∧ q.right = rU))

private def classifyCanopyStep {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (top₀ : D)
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (hNodeCons : ∀ q ∈ nodeQueries, nodeHash q.idx q.left q.right = q.out) :
    (fuel : Nat) → (active : List (Nat × D)) → (sibs : List D) →
    (parents : List (Nat × D)) → (remSibs : List D) →
    active.length ≤ fuel →
    canopyLevelStep nodeHash active sibs = some (parents, remSibs) →
    (∀ p ∈ parents, p.2 ∈ top₀ :: canopyNodeChildTargets nodeQueries) →
    StepClassify nodeHash top₀ nodeQueries fuel active sibs parents remSibs
  | 0, active, sibs, parents, remSibs, hFuel, hStep, _ => by
    cases active with
    | nil =>
      exact .ok (by
        obtain ⟨hb, ht⟩ := canopyLevelStep_nil nodeHash hStep
        subst hb; subst ht; rfl)
    | cons _ _ => exact absurd hFuel (by simp)
  | fuel + 1, [], sibs, parents, remSibs, _, hStep, _ =>
    .ok (by
      obtain ⟨hb, ht⟩ := canopyLevelStep_nil nodeHash hStep
      subst hb; subst ht; rfl)
  | fuel + 1, [(u, hu)], [], _, _, _, hStep, _ => False.elim (by cases hStep)
  | fuel + 1, [(u, hu)], s :: afterS, parents, remSibs, _, hStep, hParTargets => by
    have hEqStep : parents = [(u >>> 1, canopyParentHash nodeHash u hu s)] ∧ afterS = remSibs := by
      simp only [canopyLevelStep, Option.some.injEq, Prod.mk.injEq] at hStep
      exact ⟨hStep.1.symm, hStep.2⟩
    let pDig := canopyParentHash nodeHash u hu s
    let lCh := if u &&& 1 = 0 then hu else s
    let rCh := if u &&& 1 = 0 then s else hu
    have hHashEq : nodeHash (u >>> 1) lCh rCh = pDig := by
      dsimp only [pDig, canopyParentHash, lCh, rCh]
      by_cases hp : u &&& 1 = 0 <;> simp only [hp, ↓reduceIte]
    have hMemT : pDig ∈ top₀ :: canopyNodeChildTargets nodeQueries :=
      hParTargets (u >>> 1, pDig) (by rw [hEqStep.1]; exact .head _)
    let pred := fun q : RecordedCanopyNodeQuery D =>
      decide (q.idx = u >>> 1) && decide (q.out = pDig)
    match hF : findFirst pred nodeQueries with
    | none =>
      refine .unq (u >>> 1) lCh rCh pDig hHashEq hMemT (fun q hq ⟨hI, hL, hR⟩ => ?_)
      have hFalse := findFirst_none_spec pred hF q hq
      have hOut : q.out = pDig := by rw [← hNodeCons q hq, hI, hL, hR, hHashEq]
      dsimp only [pred] at hFalse
      simp only [hI, hOut, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
    | some q =>
      rcases findFirst_some_spec pred hF with ⟨hqMem, hqP⟩
      dsimp only [pred] at hqP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hqP
      if hEq : (q.left, q.right) = (lCh, rCh) then
        exact .ok (by
          have hL : q.left = lCh := (Prod.mk.inj hEq).1
          have hR : q.right = rCh := (Prod.mk.inj hEq).2
          rw [hEqStep.1, hEqStep.2]
          show extractOnlineCanopyStep nodeQueries (fuel + 1) [u] [(u >>> 1, pDig)] remSibs =
            some ([(u, hu)], s :: remSibs)
          unfold extractOnlineCanopyStep
          dsimp only [pred] at hF
          simp only [↓reduceIte, hF]
          by_cases hp : u &&& 1 = 0 <;>
            (dsimp only [lCh, rCh] at hL hR; simp only [hp, ↓reduceIte] at hL hR ⊢; rw [hL, hR]))
      else
        exact .coll ⟨u >>> 1, q.left, q.right, lCh, rCh, hEq, by
          rw [← hqP.1, hNodeCons q hqMem, hqP.2, ← hHashEq, hqP.1]⟩
  | fuel + 1, (u, hu) :: (v, hv) :: tl, sibs, parents, remSibs, hFuel, hStep, hParTargets => by
    by_cases hv' : v = u ^^^ 1
    · match hSubOpt : canopyLevelStep nodeHash tl sibs with
      | none =>
        exact False.elim (by
          obtain ⟨_, hSub, _⟩ := canopyLevelStep_pair nodeHash hv' hStep
          rw [hSubOpt] at hSub; cases hSub)
      | some (subAct, subRem) =>
        have hShapePair : subRem = remSibs ∧
            parents = (u >>> 1, nodeHash (u >>> 1) hu hv) :: subAct := by
          obtain ⟨act', hSub, hb⟩ := canopyLevelStep_pair nodeHash hv' hStep
          rw [hSubOpt] at hSub
          injection hSub with hPr; injection hPr with hA hR
          subst hA; exact ⟨hR, hb⟩
        let pDig := nodeHash (u >>> 1) hu hv
        have hMemT : pDig ∈ top₀ :: canopyNodeChildTargets nodeQueries :=
          hParTargets (u >>> 1, pDig) (by rw [hShapePair.2]; exact .head _)
        have hTlFuel : tl.length ≤ fuel := by simp only [List.length_cons] at hFuel; omega
        let pred := fun q : RecordedCanopyNodeQuery D =>
          decide (q.idx = u >>> 1) && decide (q.out = pDig)
        match hF : findFirst pred nodeQueries with
        | none =>
          refine .unq (u >>> 1) hu hv pDig rfl hMemT (fun q hq ⟨hI, hL, hR⟩ => ?_)
          have hFalse := findFirst_none_spec pred hF q hq
          have hOut : q.out = pDig := by rw [← hNodeCons q hq, hI, hL, hR]
          dsimp only [pred] at hFalse
          simp only [hI, hOut, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
        | some q =>
          rcases findFirst_some_spec pred hF with ⟨hqMem, hqP⟩
          dsimp only [pred] at hqP
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hqP
          if hEq : (q.left, q.right) = (hu, hv) then
            have hSubStep : canopyLevelStep nodeHash tl sibs = some (subAct, remSibs) := by
              rw [← hShapePair.1]; exact hSubOpt
            match classifyCanopyStep nodeHash top₀ nodeQueries hNodeCons fuel tl sibs subAct remSibs
                hTlFuel hSubStep (fun p hp => hParTargets p (by rw [hShapePair.2]; exact .tail _ hp)) with
            | .coll c => exact .coll c
            | .unq idxU lU rU outU hO hM hU => exact .unq idxU lU rU outU hO hM hU
            | .ok hSubExt =>
              exact .ok (by
                have hL : q.left = hu := (Prod.mk.inj hEq).1
                have hR : q.right = hv := (Prod.mk.inj hEq).2
                rw [hShapePair.2]
                show extractOnlineCanopyStep nodeQueries (fuel + 1) (u :: v :: tl.map Prod.fst)
                    ((u >>> 1, pDig) :: subAct) remSibs =
                  some ((u, hu) :: (v, hv) :: tl, sibs)
                unfold extractOnlineCanopyStep
                dsimp only [pred] at hF
                simp only [↓reduceIte, hv', hF, hSubExt]
                rw [hL, hR])
          else
            exact .coll ⟨u >>> 1, q.left, q.right, hu, hv, hEq, by
              rw [← hqP.1, hNodeCons q hqMem, hqP.2]; dsimp only [pDig]; rw [hqP.1]⟩
    · match sibs, hStep with
      | [], hStepNil =>
        exact False.elim (by
          obtain ⟨_, _, _, hs, _, _⟩ := canopyLevelStep_solo nodeHash hv' hStepNil; cases hs)
      | s :: afterSibs, hStepCons =>
        match hSubOpt : canopyLevelStep nodeHash ((v, hv) :: tl) afterSibs with
        | none =>
          exact False.elim (by
            obtain ⟨_, _, _, hs, hSub, _⟩ := canopyLevelStep_solo nodeHash hv' hStepCons
            injection hs with _ hRestEq; subst hRestEq
            rw [hSubOpt] at hSub; cases hSub)
        | some (subAct, subRem) =>
          have hShapeSolo : subRem = remSibs ∧
              parents = (u >>> 1, canopyParentHash nodeHash u hu s) :: subAct := by
            obtain ⟨c, rest, act', hs, hSub, hb⟩ := canopyLevelStep_solo nodeHash hv' hStepCons
            injection hs with hcEq hRestEq; subst hcEq; subst hRestEq
            rw [hSubOpt] at hSub
            injection hSub with hPr; injection hPr with hA hR
            subst hA; exact ⟨hR, hb⟩
          let pDig := canopyParentHash nodeHash u hu s
          let lCh := if u &&& 1 = 0 then hu else s
          let rCh := if u &&& 1 = 0 then s else hu
          have hHashEq : nodeHash (u >>> 1) lCh rCh = pDig := by
            dsimp only [pDig, canopyParentHash, lCh, rCh]
            by_cases hp : u &&& 1 = 0 <;> simp only [hp, ↓reduceIte]
          have hMemT : pDig ∈ top₀ :: canopyNodeChildTargets nodeQueries :=
            hParTargets (u >>> 1, pDig) (by rw [hShapeSolo.2]; exact .head _)
          have hVTlFuel : ((v, hv) :: tl).length ≤ fuel := Nat.le_of_succ_le_succ hFuel
          let pred := fun q : RecordedCanopyNodeQuery D =>
            decide (q.idx = u >>> 1) && decide (q.out = pDig)
          match hF : findFirst pred nodeQueries with
          | none =>
            refine .unq (u >>> 1) lCh rCh pDig hHashEq hMemT (fun q hq ⟨hI, hL, hR⟩ => ?_)
            have hFalse := findFirst_none_spec pred hF q hq
            have hOut : q.out = pDig := by rw [← hNodeCons q hq, hI, hL, hR, hHashEq]
            dsimp only [pred] at hFalse
            simp only [hI, hOut, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
          | some q =>
            rcases findFirst_some_spec pred hF with ⟨hqMem, hqP⟩
            dsimp only [pred] at hqP
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hqP
            if hEq : (q.left, q.right) = (lCh, rCh) then
              have hSubStep : canopyLevelStep nodeHash ((v, hv) :: tl) afterSibs =
                  some (subAct, remSibs) := by rw [← hShapeSolo.1]; exact hSubOpt
              match classifyCanopyStep nodeHash top₀ nodeQueries hNodeCons fuel ((v, hv) :: tl)
                  afterSibs subAct remSibs hVTlFuel hSubStep
                  (fun p hp => hParTargets p (by rw [hShapeSolo.2]; exact .tail _ hp)) with
              | .coll c => exact .coll c
              | .unq idxU lU rU outU hO hM hU => exact .unq idxU lU rU outU hO hM hU
              | .ok hSubExt =>
                exact .ok (by
                  have hL : q.left = lCh := (Prod.mk.inj hEq).1
                  have hR : q.right = rCh := (Prod.mk.inj hEq).2
                  rw [hShapeSolo.2]
                  show extractOnlineCanopyStep nodeQueries (fuel + 1) (u :: v :: tl.map Prod.fst)
                      ((u >>> 1, pDig) :: subAct) remSibs =
                    some ((u, hu) :: (v, hv) :: tl, s :: afterSibs)
                  unfold extractOnlineCanopyStep
                  dsimp only [pred] at hF
                  dsimp only [List.map] at hSubExt
                  simp only [↓reduceIte, hv', hF, hSubExt]
                  by_cases hp : u &&& 1 = 0 <;>
                    (dsimp only [lCh, rCh] at hL hR; simp only [hp, ↓reduceIte] at hL hR ⊢; rw [hL, hR]))
            else
              exact .coll ⟨u >>> 1, q.left, q.right, lCh, rCh, hEq, by
                rw [← hqP.1, hNodeCons q hqMem, hqP.2, ← hHashEq, hqP.1]⟩

private inductive LevelsClassify {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (top₀ : D)
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (d : Nat) (active : List (Nat × D)) (sibs : List D) : Type where
  | ok (hExt : extractOnlineCanopyLevels nodeQueries d (active.map Prod.fst) [(1, top₀)] [] =
      some (active, sibs))
  | coll (c : CanopyNodeCollision nodeHash)
  | unq (idxU : Nat) (lU rU outU : D)
      (hOut : nodeHash idxU lU rU = outU)
      (hMem : outU ∈ top₀ :: canopyNodeChildTargets nodeQueries)
      (hUnq : ∀ q ∈ nodeQueries, ¬(q.idx = idxU ∧ q.left = lU ∧ q.right = rU))

private def classifyCanopyLevels {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (top₀ : D)
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (hNodeCons : ∀ q ∈ nodeQueries, nodeHash q.idx q.left q.right = q.out) :
    (d : Nat) → (active : List (Nat × D)) → (sibs : List D) →
    canopyLevels nodeHash d active sibs = some ([(1, top₀)], []) →
    LevelsClassify nodeHash top₀ nodeQueries d active sibs
  | 0, active, sibs, hLvls =>
    .ok (by
      simp only [canopyLevels, Option.some.injEq, Prod.mk.injEq] at hLvls
      rcases hLvls with ⟨rfl, rfl⟩; rfl)
  | d + 1, active, sibs, hLvls => by
    match hStep : canopyLevelStep nodeHash active sibs with
    | none =>
      exact False.elim (by
        obtain ⟨_, _, hs, _⟩ := canopyLevels_succ nodeHash hLvls
        rw [hStep] at hs; cases hs)
    | some (midAct, midSibs) =>
      have hRest : canopyLevels nodeHash d midAct midSibs = some ([(1, top₀)], []) := by
        obtain ⟨m, r, hs, hr⟩ := canopyLevels_succ nodeHash hLvls
        rw [hStep] at hs; injection hs with hPr; injection hPr with hm hr'
        subst hm; subst hr'; exact hr
      have hShape := (canopyLevelStep_shape nodeHash _ active sibs midAct midSibs
        (Nat.lt_succ_self _) hStep).1
      match classifyCanopyLevels nodeHash top₀ nodeQueries hNodeCons d midAct midSibs hRest with
      | .coll c => exact .coll c
      | .unq idxU lU rU outU hO hM hU => exact .unq idxU lU rU outU hO hM hU
      | .ok hUpExt =>
        have hUpTargets := extractOnlineCanopyLevels_targets nodeQueries top₀ d
          (midAct.map Prod.fst) midAct midSibs hUpExt
        match classifyCanopyStep nodeHash top₀ nodeQueries hNodeCons active.length active sibs
            midAct midSibs (Nat.le_refl _) hStep hUpTargets with
        | .coll c => exact .coll c
        | .unq idxU lU rU outU hO hM hU => exact .unq idxU lU rU outU hO hM hU
        | .ok hStepExt =>
          exact .ok (by
            show extractOnlineCanopyLevels nodeQueries (d + 1) (active.map Prod.fst) [(1, top₀)] [] =
              some (active, sibs)
            unfold extractOnlineCanopyLevels; dsimp only
            rw [← hShape, hUpExt]; dsimp only
            rw [List.length_map]; exact hStepExt)

/-- **Constructive `Type`-valued online `CanopyMultiProof` query-table classifier**
    (`0 Classical.choice`). -/
def classifyOnlineCanopyOpening {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (rootQueries : List (RecordedCanopyRootQuery D))
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (hRootCons : ∀ q ∈ rootQueries, rootHash q.logLeaves q.top = q.out)
    (hNodeCons : ∀ q ∈ nodeQueries, nodeHash q.idx q.left q.right = q.out)
    (leaves : List (Nat × D)) (proof : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    OnlineCanopyOutcome nodeHash rootHash logLeaves commitment rootQueries nodeQueries
      leaves proof := by
  match hLvlsOpt : canopyLevels nodeHash logLeaves
      (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof with
  | some ([(uTop, top)], []) =>
    have hTopSpec : uTop = 1 ∧ rootHash logLeaves top = commitment := by
      obtain ⟨top', hL, hR⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hLvlsOpt] at hL
      injection hL with hPr; injection hPr with hList _
      injection hList with hHead _; injection hHead with hu ht
      subst ht; exact ⟨hu, hR⟩
    let rPred := fun q : RecordedCanopyRootQuery D =>
      decide (q.logLeaves = logLeaves) && decide (q.out = commitment)
    match hRF : findFirst rPred rootQueries with
    | none =>
      refine .unqueriedRootPreimage top hTopSpec.2 (fun q hq ⟨hLL, hTop⟩ => ?_)
      have hFalse := findFirst_none_spec rPred hRF q hq
      have hOut : q.out = commitment := by rw [← hRootCons q hq, hLL, hTop, hTopSpec.2]
      dsimp only [rPred] at hFalse
      simp only [hLL, hOut, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
    | some rq =>
      rcases findFirst_some_spec rPred hRF with ⟨hrqMem, hrqP⟩
      dsimp only [rPred] at hrqP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrqP
      if hTopEq : rq.top = top then
        have hLvlsRq : canopyLevels nodeHash logLeaves
            (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof = some ([(1, rq.top)], []) := by
          rw [hTopEq, ← hTopSpec.1]; exact hLvlsOpt
        match classifyCanopyLevels nodeHash rq.top nodeQueries hNodeCons logLeaves
            (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof hLvlsRq with
        | .coll c => exact .nodeCollision c
        | .unq idxU lU rU outU hO hM hU =>
          exact .unqueriedNodePreimage rq.top idxU lU rU outU
            ⟨rq, hrqMem, hrqP.1, rfl, hrqP.2⟩ hO hM hU
        | .ok hExtLvls =>
          exact .extractedEq (by
            unfold extractOnlineCanopyOpening
            rw [hRF]; dsimp only
            rw [map_fst_shift_eq (2 ^ logLeaves) leaves] at hExtLvls
            rw [hExtLvls]; dsimp only
            rw [map_snd_shift_eq (2 ^ logLeaves) leaves, zip_fst_snd_eq leaves])
      else
        exact .rootCollision ⟨rq.top, top, hTopEq, by
          have h1 := hRootCons rq hrqMem
          rw [hrqP.1, hrqP.2] at h1
          exact h1.trans hTopSpec.2.symm⟩
  | none =>
    exact False.elim (by
      obtain ⟨_, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hL] at hLvlsOpt; cases hLvlsOpt)
  | some ([], _) =>
    exact False.elim (by
      obtain ⟨_, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hL] at hLvlsOpt; injection hLvlsOpt with hp; injection hp with hl _; cases hl)
  | some (_ :: _ :: _, _) =>
    exact False.elim (by
      obtain ⟨_, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hL] at hLvlsOpt; injection hLvlsOpt with hp; injection hp with hl _
      injection hl with _ htl; cases htl)
  | some ([_], _ :: _) =>
    exact False.elim (by
      obtain ⟨_, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hL] at hLvlsOpt; injection hLvlsOpt with hp; injection hp with _ hr; cases hr)

/-- **Pre-challenge binding of `CanopyMultiProof` online extraction**. -/
theorem onlineCanopy_preChallenge_unique {D : Type} [DecidableEq D]
    (commitment : D)
    (rootQueries : List (RecordedCanopyRootQuery D))
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (logLeaves : Nat) (leaves₁ leaves₂ : List (Nat × D)) (proof₁ proof₂ : List D)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (h₁ : extractOnlineCanopyOpening commitment rootQueries nodeQueries logLeaves
      (leaves₁.map Prod.fst) = some (leaves₁, proof₁))
    (h₂ : extractOnlineCanopyOpening commitment rootQueries nodeQueries logLeaves
      (leaves₂.map Prod.fst) = some (leaves₂, proof₂)) :
    leaves₁ = leaves₂ ∧ proof₁ = proof₂ := by
  rw [hIdx] at h₁
  exact Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))


/-! ## §3. Unitary `QVec` / `GaussInt` Quantum Online-Extraction Reduction (`qromMerkleOnlineExtractBound`) -/

private theorem qsum_ofFin_eq_single (w : Nat) (y : BitVec w) :
    qsum (2 ^ w) (fun j => if BitVec.ofFin j = y then 1 else 0) = 1 := by
  have hCongr : qsum (2 ^ w) (fun j => if BitVec.ofFin j = y then 1 else 0) =
      qsum (2 ^ w) (fun j => if j = y.toFin then 1 else 0) := by
    apply qsum_congr; intro j
    by_cases hj : j = y.toFin
    · subst hj; simp
    · have hne : BitVec.ofFin j ≠ y := fun he => hj (by rw [← he])
      simp [hj, hne]
  rw [hCongr, qsum_eq_indicator]

/-- At most `ts.length` values `j : Fin (2 ^ w)` land inside any target list `ts : List (BitVec w)`. -/
theorem qsum_ofFin_listHasElem_le_length (w : Nat) :
    ∀ (ts : List (BitVec w)),
      qsum (2 ^ w) (fun j => if listHasElem (BitVec.ofFin j) ts = true then 1 else 0) ≤ ts.length
  | [] => by simp only [listHasElem_nil, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]; omega
  | t :: rest => by
    have ih := qsum_ofFin_listHasElem_le_length w rest
    have hSplit :
        qsum (2 ^ w) (fun j => if listHasElem (BitVec.ofFin j) (t :: rest) = true then 1 else 0) ≤
        qsum (2 ^ w) (fun j =>
          (if BitVec.ofFin j = t then 1 else 0) +
          (if listHasElem (BitVec.ofFin j) rest = true then 1 else 0)) := by
      apply qsum_le_qsum; intro j
      rw [listHasElem_cons]
      by_cases hjt : BitVec.ofFin j = t
      · simp [hjt]
      · simp [hjt]
    rw [qsum_add, qsum_ofFin_eq_single w t] at hSplit
    simp only [List.length_cons]
    omega

/-- `QromRbrRound` for a coordinate `x = proj z` hashing into a target list of size `≤ T`
    that is invariant under reprogramming `x`. The definition does not assert that `x` was
    unqueried, or that the targets were extracted before a protocol challenge. -/
def qromTargetSetRound {cardX w : Nat} (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX)
    (targetSet : (Fin cardX → BitVec w) → Fin cardX → List (BitVec w))
    (T : Nat)
    (hLocal : ∀ (O : Fin cardX → BitVec w) (x : Fin cardX) (ch : BitVec w),
      targetSet (reprogramOracle O x ch) x = targetSet O x)
    (hCard : ∀ (O : Fin cardX → BitVec w) (x : Fin cardX), (targetSet O x).length ≤ T) :
    QromRbrRound cardX w H where
  proj := proj
  isDoomedAt := fun _ _ => true
  isLiveAfter := fun O x => listHasElem (O x) (targetSet O x)
  badCard := T
  doomed_local := fun _ _ => rfl
  flip_bound := fun x _ => by
    have hEq : ∀ j : Fin (2 ^ w),
        listHasElem ((reprogramOracle H x (BitVec.ofFin j)) x)
          (targetSet (reprogramOracle H x (BitVec.ofFin j)) x) =
        listHasElem (BitVec.ofFin j) (targetSet H x) := by
      intro j
      rw [hLocal H x (BitVec.ofFin j)]
      simp [reprogramOracle]
    rw [qsum_congr (fun j => by rw [hEq j])]
    exact Nat.le_trans (qsum_ofFin_listHasElem_le_length w (targetSet H x)) (hCard H x)

/-- **Unitary `QVec` / `GaussInt` Target-Set Preimage Bound (`qrom_unitary_target_hit_bound`)**. -/
theorem qrom_unitary_target_hit_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (proj : Fin cardX → Fin cardX)
    (targetSet : (Fin cardX → BitVec w) → Fin cardX → List (BitVec w))
    (T : Nat)
    (hLocal : ∀ (O : Fin cardX → BitVec w) (x : Fin cardX) (ch : BitVec w),
      targetSet (reprogramOracle O x ch) x = targetSet O x)
    (hCard : ∀ (O : Fin cardX → BitVec w) (x : Fin cardX), (targetSet O x).length ≤ T) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    let live := fun (O : Fin cardX → BitVec w) (x : Fin cardX) => listHasElem (O x) (targetSet O x)
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H =>
          qromOrdinaryFlipMass A H proj (fun _ _ => true) live),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * T, 2 ^ w, Nat.two_pow_pos w⟩ :=
  qrom_uniform_oracle_round_bound A
    (fun H => qromTargetSetRound H proj targetSet T hLocal hCard)
    proj (fun _ _ => true) (fun O x => listHasElem (O x) (targetSet O x)) T
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem twoQ_plus_one_sq_le_eight_Q_succ_sq (Q : Nat) :
    (2 * Q + 1) ^ 2 ≤ 8 * (Q + 1) ^ 2 := by
  have h1 : 2 * Q + 1 ≤ 2 * (Q + 1) := by omega
  have h2 : (2 * Q + 1) ^ 2 ≤ (2 * (Q + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : (2 * (Q + 1)) ^ 2 = 4 * (Q + 1) ^ 2 := by rw [Nat.mul_pow]
  rw [h3] at h2
  exact Nat.le_trans h2 (Nat.mul_le_mul_right ((Q + 1) ^ 2) (by decide : 4 ≤ 8))

private theorem twoQ_plus_one_cube_le_eight_Q_succ_cube (Q : Nat) :
    (2 * Q + 1) ^ 2 * (2 * Q + 1) ≤ 8 * (Q + 1) ^ 3 := by
  have hPow : (2 * Q + 1) ^ 2 * (2 * Q + 1) = (2 * Q + 1) ^ 3 := (Nat.pow_succ (2 * Q + 1) 2).symm
  have h1 : 2 * Q + 1 ≤ 2 * (Q + 1) := by omega
  have h2 : (2 * Q + 1) ^ 3 ≤ (2 * (Q + 1)) ^ 3 := Nat.pow_le_pow_left h1 3
  have h3 : (2 * (Q + 1)) ^ 3 = 8 * (Q + 1) ^ 3 := by rw [Nat.mul_pow]
  rw [hPow, ← h3]; exact h2

/-- Exact algebraic dominance of `qromMerkleOnlineExtractBound numRoots w Q` over the unitary
    Measure-and-Reprogram bound `(2Q + 1)^2 * (numRoots * (1 + (2Q + 1))) / 2^w`. -/
theorem unitary_merkle_raw_le_qromMerkleOnlineExtractBound (numRoots w Q : Nat) :
    RatBound.le
      ⟨(2 * Q + 1) ^ 2 * (numRoots * (1 + (2 * Q + 1))), 2 ^ w, Nat.two_pow_pos w⟩
      (qromMerkleOnlineExtractBound numRoots w Q) := by
  unfold qromMerkleOnlineExtractBound RatBound.scale RatBound.add
    quantumGroverSingleTargetBound quantumZhandryMultiTargetBound quantumBhtCollisionBound
    RatBound.le
  dsimp only
  have hPerRoot :
      (2 * Q + 1) ^ 2 * (1 + (2 * Q + 1)) ≤
        8 * 1 * (Q + 1) ^ 2 + 8 * (Q + 1) ^ 3 := by
    rw [Nat.mul_add, Nat.mul_one, show 8 * 1 = 8 from rfl]
    exact Nat.add_le_add (twoQ_plus_one_sq_le_eight_Q_succ_sq Q)
      (twoQ_plus_one_cube_le_eight_Q_succ_cube Q)
  have hScaled :
      (2 * Q + 1) ^ 2 * (numRoots * (1 + (2 * Q + 1))) ≤
        numRoots * (8 * 1 * (Q + 1) ^ 2 + 8 * (Q + 1) ^ 3) := by
    rw [← Nat.mul_assoc, Nat.mul_comm ((2 * Q + 1) ^ 2) numRoots, Nat.mul_assoc]
    exact Nat.mul_le_mul_left numRoots hPerRoot
  let S := 8 * 1 * (Q + 1) ^ 2 + 8 * (Q + 1) ^ 3
  let W := 2 ^ w
  have hRhsEq :
      numRoots * (8 * 1 * (Q + 1) ^ 2 * W + 8 * (Q + 1) ^ 3 * W) * W =
      numRoots * S * (W * W) := by
    dsimp only [S]
    rw [← Nat.add_mul (8 * 1 * (Q + 1) ^ 2) (8 * (Q + 1) ^ 3) W,
        ← Nat.mul_assoc numRoots _ W,
        Nat.mul_assoc (numRoots * _) W W]
  change (2 * Q + 1) ^ 2 * (numRoots * (1 + (2 * Q + 1))) * (W * W) ≤
    numRoots * (8 * 1 * (Q + 1) ^ 2 * W + 8 * (Q + 1) ^ 3 * W) * W
  rw [hRhsEq]
  exact Nat.mul_le_mul_right (W * W) hScaled

/-- Conditional target-hit union bound with the arithmetic Merkle extraction budget.
    `failExtract` is an arbitrary event. A protocol reduction must supply `hCover`, `hLocal`,
    and `hCard`; this theorem neither constructs a query table nor relates that event to
    `classifyOnlineMerkleOpening` or `classifyOnlineCanopyOpening`. -/
theorem qrom_unitary_multiRoot_merkle_extract_bound {cardX w cardAnc Q : Nat}
    (numRoots : Nat)
    (A : QuantumAdv cardX w cardAnc Q)
    (failExtract : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (proj : Fin (2 * numRoots) → Fin cardX → Fin cardX)
    (targetSet : Fin (2 * numRoots) → (Fin cardX → BitVec w) → Fin cardX → List (BitVec w))
    (hLocal : ∀ r O x ch, targetSet r (reprogramOracle O x ch) x = targetSet r O x)
    (hCard : ∀ r O x,
      (targetSet r O x).length ≤ (if r.1 % 2 = 0 then 1 else 2 * Q + 1))
    (hCover : ∀ H, QVec.queryMassOn (failExtract H) (runQuantumAdv A H) ≤
      qsum (2 * numRoots) (fun r =>
        qromOrdinaryFlipMass A H (proj r) (fun _ _ => true)
          (fun O x => listHasElem (O x) (targetSet r O x)))) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => QVec.queryMassOn (failExtract H) (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (qromMerkleOnlineExtractBound numRoots w Q) := by
  let bad : Fin (2 * numRoots) → Nat := fun r => if r.1 % 2 = 0 then 1 else 2 * Q + 1
  have hUnion := qrom_uniform_oracle_success_bound A failExtract
    (fun r H => qromTargetSetRound H (proj r) (targetSet r) (bad r) (hLocal r) (hCard r))
    proj (fun _ _ _ => true) (fun r O x => listHasElem (O x) (targetSet r O x)) bad
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) hCover
  have hSumBad : ∀ m : Nat,
      qsum (2 * m) (fun r : Fin (2 * m) => if r.1 % 2 = 0 then 1 else 2 * Q + 1) =
        m * (1 + (2 * Q + 1)) := by
    intro m
    induction m with
    | zero => simp [qsum_zero]
    | succ k ih =>
      let C := 1 + (2 * Q + 1)
      have hStep2 : ∀ (n : Nat), n = 2 * k →
          qsum (n + 2) (fun r : Fin (n + 2) => if r.1 % 2 = 0 then 1 else 2 * Q + 1) =
            C + qsum n (fun r : Fin n => if r.1 % 2 = 0 then 1 else 2 * Q + 1) := by
        intro n _
        change qsum ((n + 1) + 1) _ = _
        simp only [qsum_succ]
        have h1 : (0 + 1 : Nat) % 2 = 1 := rfl
        have hMod : ∀ (i : Fin n), (i.1 + 1 + 1) % 2 = i.1 % 2 := fun _ => by omega
        rw [qsum_congr (fun i => by rw [hMod i])]
        simp only [h1, Nat.one_ne_zero, ↓reduceIte]
        dsimp only [C]
        omega
      have hEq2 : 2 * (k + 1) = 2 * k + 2 := by omega
      have hGen : ∀ (N : Nat), N = 2 * k + 2 →
          qsum N (fun r : Fin N => if r.1 % 2 = 0 then 1 else 2 * Q + 1) =
            (k + 1) * C := by
        intro N hN; subst hN
        rw [hStep2 (2 * k) rfl, Nat.succ_mul k C]
        change C + qsum (2 * k) (fun r : Fin (2 * k) => if r.1 % 2 = 0 then 1 else 2 * Q + 1) =
          k * C + C
        rw [ih]
        exact Nat.add_comm C (k * C)
      exact hGen (2 * (k + 1)) hEq2
  have hBadEq : qsum (2 * numRoots) bad = numRoots * (1 + (2 * Q + 1)) := hSumBad numRoots
  rw [hBadEq] at hUnion
  exact RatBound.le_trans hUnion (unitary_merkle_raw_le_qromMerkleOnlineExtractBound numRoots w Q)

/-- Single-root specialization (`numRoots = 1`) of `qrom_unitary_multiRoot_merkle_extract_bound`. -/
theorem qrom_unitary_single_root_merkle_extract_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (failExtract : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (proj : Fin 2 → Fin cardX → Fin cardX)
    (targetSet : Fin 2 → (Fin cardX → BitVec w) → Fin cardX → List (BitVec w))
    (hLocal : ∀ r O x ch, targetSet r (reprogramOracle O x ch) x = targetSet r O x)
    (hCard : ∀ r O x, (targetSet r O x).length ≤ (if r.1 % 2 = 0 then 1 else 2 * Q + 1))
    (hCover : ∀ H, QVec.queryMassOn (failExtract H) (runQuantumAdv A H) ≤
      qsum 2 (fun r =>
        qromOrdinaryFlipMass A H (proj r) (fun _ _ => true)
          (fun O x => listHasElem (O x) (targetSet r O x)))) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => QVec.queryMassOn (failExtract H) (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (qromMerkleOnlineExtractBound 1 w Q) :=
  qrom_unitary_multiRoot_merkle_extract_bound 1 A failExtract proj targetSet hLocal hCard hCover

end Qsag


namespace Qsag

set_option autoImplicit false

/-- A genuine measured-query interface: branch `x` is obtained by projecting the actual
    post-oracle state onto the observed query address. It is not an unobserved query log. -/
def measuredOracleQueryBranch {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) (x : Fin cardX) :
    QVec cardX w cardAnc := projSingle x (oracleXor H ψ)

/-- The measured branches have exactly the input query weights and conserve total mass.
    This supplies probabilities for an explicit measurement instrument; it does not identify
    the instrument with the original coherent execution. -/
theorem measuredOracleQueryBranch_mass {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) :
    (∀ x, QVec.stateNormSq (measuredOracleQueryBranch H ψ x) = QVec.queryWeight ψ x) ∧
    qsum cardX (fun x => QVec.stateNormSq (measuredOracleQueryBranch H ψ x)) =
      QVec.stateNormSq ψ := by
  have h : ∀ x, QVec.stateNormSq (measuredOracleQueryBranch H ψ x) =
      QVec.queryWeight ψ x := fun x => by
    rw [measuredOracleQueryBranch, projSingle_normSq, oracleXor_queryWeight]
  exact ⟨h, qsum_congr h⟩

/-- When a query's response register starts at zero, measuring its address and answer
    produces an oracle-consistent classical record. This is a positive bridge to classical
    query-table consistency for explicitly measured executions, not for arbitrary QROM runs. -/
theorem measuredOracleQueryBranch_consistent {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc)
    (hZero : ∀ x y a, y.val ≠ 0 → ψ x y a = GaussInt.zero)
    (recorded x : Fin cardX) (y : Fin (2 ^ w)) (a : Fin cardAnc)
    (hMass : measuredOracleQueryBranch H ψ recorded x y a ≠ GaussInt.zero) :
    x = recorded ∧ BitVec.ofFin y = H recorded := by
  have hx : x = recorded := by
    by_cases heq : x = recorded
    · exact heq
    · exact False.elim (hMass (by simp [measuredOracleQueryBranch, projSingle, heq]))
  subst hx
  have hAnsZero : (xorFin y (H x)).val = 0 := by
    by_cases heq : (xorFin y (H x)).val = 0
    · exact heq
    · exact False.elim (hMass (by
        simp only [measuredOracleQueryBranch, projSingle, ↓reduceIte, oracleXor]
        exact hZero x (xorFin y (H x)) a heq))
  have hFinZero : xorFin y (H x) = (0 : Fin (2 ^ w)) := Fin.ext hAnsZero
  have hInv := congrArg (fun z => xorFin z (H x)) hFinZero
  rw [xorFin_involutive] at hInv
  have hZeroXor : (0#w ^^^ H x) = H x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_zero, Bool.false_xor]
  have hOutput : y = (H x).toFin := by
    change y = (0#w ^^^ H x).toFin at hInv
    rw [hZeroXor] at hInv
    exact hInv
  exact ⟨rfl, by rw [hOutput, BitVec.ofFin_toFin]⟩

/-- An observed zero-response oracle query supplies the classical classifier's actual
    `merkleQueryConsistent` premise for a chosen compression-input encoding. This lemma
    only establishes record consistency: injective domain encoding, sequential recording,
    pre-challenge timing, and disturbance bounds remain separate obligations. -/
theorem measuredOracleQuery_merkle_record_consistent {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w)
    (encode : Nat → Nat → BitVec w → BitVec w → Fin cardX)
    (ψ : QVec cardX w cardAnc)
    (hZero : ∀ x y a, y.val ≠ 0 → ψ x y a = GaussInt.zero)
    (lvl node : Nat) (left right : BitVec w)
    (y : Fin (2 ^ w)) (a : Fin cardAnc)
    (hMass : measuredOracleQueryBranch H ψ (encode lvl node left right)
      (encode lvl node left right) y a ≠ GaussInt.zero) :
    merkleQueryConsistent (fun l n u v => H (encode l n u v))
      ⟨lvl, node, left, right, BitVec.ofFin y⟩ :=
  (measuredOracleQueryBranch_consistent H ψ hZero
    (encode lvl node left right) (encode lvl node left right) y a hMass).2.symm


end Qsag


namespace Qsag

set_option autoImplicit false

/-! ## Sums over query logs -/

/-- Sum over every query log of length `t`, each occurring once; the head is the most
    recent address. -/
def sumLogs (cardX : Nat) : (t : Nat) → (List (Fin cardX) → Nat) → Nat
  | 0, f => f []
  | t + 1, f => qsum cardX (fun x => sumLogs cardX t (fun xs => f (x :: xs)))

theorem sumLogs_le_of_length (cardX : Nat) : ∀ (t : Nat) (f g : List (Fin cardX) → Nat),
    (∀ xs, xs.length = t → f xs ≤ g xs) → sumLogs cardX t f ≤ sumLogs cardX t g
  | 0, _, _, h => h [] rfl
  | t + 1, _, _, h => qsum_le_qsum (fun x => sumLogs_le_of_length cardX t _ _
      (fun xs hx => h (x :: xs) (congrArg Nat.succ hx)))

theorem sumLogs_congr (cardX : Nat) : ∀ (t : Nat) (f g : List (Fin cardX) → Nat),
    (∀ xs, f xs = g xs) → sumLogs cardX t f = sumLogs cardX t g
  | 0, _, _, h => h []
  | t + 1, _, _, h => qsum_congr (fun x => sumLogs_congr cardX t _ _ (fun xs => h (x :: xs)))

theorem sumLogs_add (cardX : Nat) : ∀ (t : Nat) (f g : List (Fin cardX) → Nat),
    sumLogs cardX t (fun xs => f xs + g xs) = sumLogs cardX t f + sumLogs cardX t g
  | 0, _, _ => rfl
  | t + 1, f, g =>
    (qsum_congr (fun x => sumLogs_add cardX t (fun xs => f (x :: xs))
      (fun xs => g (x :: xs)))).trans (qsum_add _ _)

theorem sumLogs_mul (cardX : Nat) : ∀ (t c : Nat) (f : List (Fin cardX) → Nat),
    sumLogs cardX t (fun xs => c * f xs) = c * sumLogs cardX t f
  | 0, _, _ => rfl
  | t + 1, c, f =>
    (qsum_congr (fun x => sumLogs_mul cardX t c (fun xs => f (x :: xs)))).trans
      (qsum_mul_left c _)

theorem sumLogs_qsum (cardX : Nat) : ∀ (t k : Nat) (f : List (Fin cardX) → Fin k → Nat),
    sumLogs cardX t (fun xs => qsum k (fun j => f xs j)) =
      qsum k (fun j => sumLogs cardX t (fun xs => f xs j))
  | 0, _, _ => rfl
  | t + 1, k, f =>
    (qsum_congr (fun x => sumLogs_qsum cardX t k (fun xs j => f (x :: xs) j))).trans
      (qsum_comm cardX k (fun x j => sumLogs cardX t (fun xs => f (x :: xs) j)))

theorem uniformOracleSum_sumLogs (w n cardX : Nat) : ∀ (t : Nat)
    (f : (Fin n → BitVec w) → List (Fin cardX) → Nat),
    uniformOracleSum w n (fun H => sumLogs cardX t (f H)) =
      sumLogs cardX t (fun xs => uniformOracleSum w n (fun H => f H xs))
  | 0, _ => rfl
  | t + 1, f =>
    (uniformOracleSum_qsum w n cardX
      (fun H x => sumLogs cardX t (fun xs => f H (x :: xs)))).trans
      (qsum_congr (fun x => uniformOracleSum_sumLogs w n cardX t (fun H xs => f H (x :: xs))))

theorem uniformOracleSum_add (w : Nat) : ∀ (n : Nat) (f g : (Fin n → BitVec w) → Nat),
    uniformOracleSum w n (fun H => f H + g H) =
      uniformOracleSum w n f + uniformOracleSum w n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show qsum (2 ^ w) (fun j => uniformOracleSum w n (fun H =>
        f (Fin.cases (BitVec.ofFin j) H) + g (Fin.cases (BitVec.ofFin j) H))) =
      qsum (2 ^ w) (fun j => uniformOracleSum w n (fun H => f (Fin.cases (BitVec.ofFin j) H))) +
      qsum (2 ^ w) (fun j => uniformOracleSum w n (fun H => g (Fin.cases (BitVec.ofFin j) H)))
    rw [← qsum_add]
    exact qsum_congr (fun j => uniformOracleSum_add w n _ _)

/-! ## Point reprogramming -/

theorem reprogramOracle_self {n w : Nat} (H : Fin n → BitVec w) (x : Fin n) (ch : BitVec w) :
    reprogramOracle H x ch x = ch := ite_eq_left rfl

theorem reprogramOracle_of_ne {n w : Nat} (H : Fin n → BitVec w) (x : Fin n) (ch : BitVec w)
    (y : Fin n) (h : y ≠ x) : reprogramOracle H x ch y = H y := ite_eq_right h

theorem reprogramOracle_undo {n w : Nat} (H : Fin n → BitVec w) (x : Fin n) (ch : BitVec w) :
    reprogramOracle (reprogramOracle H x ch) x (H x) = H := by
  funext y
  by_cases hy : y = x
  · rw [hy]; exact reprogramOracle_self _ _ _
  · rw [reprogramOracle_of_ne _ _ _ _ hy, reprogramOracle_of_ne _ _ _ _ hy]

theorem bool_not_eq_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b
  · rfl
  · cases h

theorem map_reprogram_of_fresh {n w : Nat} (H : Fin n → BitVec w) (x : Fin n)
    (ch : BitVec w) : ∀ (xs : List (Fin n)), listHasElem x xs = false →
      xs.map (reprogramOracle H x ch) = xs.map H
  | [], _ => rfl
  | y :: ys, h => by
    have hyx : y ≠ x := fun he =>
      Bool.noConfusion (h.symm.trans ((listHasElem_eq_true_iff x (y :: ys)).mpr (he ▸ .head ys)))
    have hTail : listHasElem x ys = false := by
      cases hc : listHasElem x ys
      · rfl
      · exact Bool.noConfusion (h.symm.trans ((listHasElem_eq_true_iff x (y :: ys)).mpr
          (.tail y ((listHasElem_eq_true_iff x ys).mp hc))))
    show reprogramOracle H x ch y :: ys.map (reprogramOracle H x ch) = H y :: ys.map H
    rw [reprogramOracle_of_ne _ _ _ _ hyx, map_reprogram_of_fresh H x ch ys hTail]

/-- Lazy sampling at a single oracle-dependent address. The address `p H`, the flag `ok H`,
    the target list `T H` and the weight `W H` must not read the oracle at `p H`. Then the
    answer at `p H` lands in `T H` with weight at most `K / 2^w` of the total weight. -/
theorem uniform_fresh_point_bound (w n : Nat)
    (p : (Fin n → BitVec w) → Fin n) (ok : (Fin n → BitVec w) → Bool)
    (T : (Fin n → BitVec w) → List (BitVec w)) (W : (Fin n → BitVec w) → Nat) (K : Nat)
    (hp : ∀ H ch, p (reprogramOracle H (p H) ch) = p H)
    (hok : ∀ H ch, ok (reprogramOracle H (p H) ch) = ok H)
    (hT : ∀ H ch, ok H = true → T (reprogramOracle H (p H) ch) = T H)
    (hW : ∀ H ch, ok H = true → W (reprogramOracle H (p H) ch) = W H)
    (hK : ∀ H, ok H = true → (T H).length ≤ K) :
    2 ^ w * uniformOracleSum w n (fun H =>
      if (ok H && listHasElem (H (p H)) (T H)) = true then W H else 0) ≤
      K * uniformOracleSum w n W := by
  let g : (Fin n → BitVec w) → Nat := fun H =>
    if (ok H && listHasElem (H (p H)) (T H)) = true then W H else 0
  let f : Fin n → (Fin n → BitVec w) → Nat := fun x H => if x = p H then g H else 0
  have hDecomp : ∀ H, g H = qsum n (fun x => f x H) :=
    fun H => (qsum_ite_eq n (p H) (g H)).symm
  have hIff : ∀ H x ch, x = p (reprogramOracle H x ch) → x = p H := by
    intro H x ch hx
    have h := hp (reprogramOracle H x ch) (H x)
    rw [← hx, reprogramOracle_undo] at h
    exact h.symm
  have hPt : ∀ x H, qsum (2 ^ w) (fun j => f x (reprogramOracle H x (BitVec.ofFin j))) ≤
      (if x = p H then K * W H else 0) := by
    intro x H
    by_cases hx : x = p H
    · subst hx
      rw [ite_eq_left rfl]
      cases hOk : ok H with
      | false =>
        have hz : ∀ j : Fin (2 ^ w),
            f (p H) (reprogramOracle H (p H) (BitVec.ofFin j)) = 0 := by
          intro j
          simp only [f, g, hp H _, hok H _, hOk, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte]
        rw [qsum_congr hz, qsum_const, Nat.mul_zero]
        exact Nat.zero_le _
      | true =>
        have hEq : ∀ j : Fin (2 ^ w),
            f (p H) (reprogramOracle H (p H) (BitVec.ofFin j)) =
              (if listHasElem (BitVec.ofFin j) (T H) = true then 1 else 0) * W H := by
          intro j
          simp only [f, g, hp H _, hok H _, hOk, hT H _ hOk, hW H _ hOk,
            reprogramOracle_self, Bool.true_and, ↓reduceIte]
          cases listHasElem (BitVec.ofFin j) (T H)
          · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]
          · simp only [↓reduceIte, Nat.one_mul]
        rw [qsum_congr hEq, qsum_mul_right]
        exact Nat.mul_le_mul_right _
          (Nat.le_trans (qsum_ofFin_listHasElem_le_length w (T H)) (hK H hOk))
    · rw [ite_eq_right hx]
      have hz : ∀ j : Fin (2 ^ w), f x (reprogramOracle H x (BitVec.ofFin j)) = 0 :=
        fun j => ite_eq_right (fun h => hx (hIff H x _ h))
      rw [qsum_congr hz, qsum_const, Nat.mul_zero]
      exact Nat.le_refl 0
  have h1 : 2 ^ w * uniformOracleSum w n g =
      qsum n (fun x => uniformOracleSum w n (fun H =>
        qsum (2 ^ w) (fun j => f x (reprogramOracle H x (BitVec.ofFin j))))) := by
    rw [uniformOracleSum_congr w n g _ hDecomp, uniformOracleSum_qsum w n n (fun H x => f x H),
      ← qsum_mul_left]
    exact qsum_congr (fun x => (uniformOracleSum_resample w n x (f x)).symm)
  have h2 : qsum n (fun x => uniformOracleSum w n (fun H =>
        qsum (2 ^ w) (fun j => f x (reprogramOracle H x (BitVec.ofFin j))))) ≤
      qsum n (fun x => uniformOracleSum w n (fun H => if x = p H then K * W H else 0)) :=
    qsum_le_qsum (fun x => uniformOracleSum_le w n _ _ (hPt x))
  have h3 : qsum n (fun x => uniformOracleSum w n (fun H =>
        if x = p H then K * W H else 0)) = K * uniformOracleSum w n W := by
    rw [← uniformOracleSum_qsum w n n (fun H x => if x = p H then K * W H else 0),
      uniformOracleSum_congr w n _ _ (fun H => qsum_ite_eq n (p H) (K * W H)),
      uniformOracleSum_mul]
  show 2 ^ w * uniformOracleSum w n g ≤ K * uniformOracleSum w n W
  rw [h1, ← h3]
  exact h2

/-! ## The measured-query experiment -/

/-- Unnormalized branch state after `t` oracle calls whose query addresses were measured
    right after the oracle acted, with outcomes `xs` (most recent first). A log of the wrong
    length is the zero branch (length 0 ignores the log). -/
def measuredStateAt {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H : Fin cardX → BitVec w) : (t : Nat) → t ≤ q → List (Fin cardX) → QVec cardX w cardAnc
  | 0, _, _ => A.init
  | _ + 1, _, [] => QVec.zero cardX w cardAnc
  | t + 1, ht, x :: xs =>
    (A.steps ⟨t, ht⟩).apply
      (measuredOracleQueryBranch H (measuredStateAt A H t (Nat.le_of_succ_le ht) xs) x)

/-- A measured branch reads the oracle only at its measured addresses. -/
theorem measuredStateAt_congr {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (H H' : Fin cardX → BitVec w) : ∀ (t : Nat) (ht : t ≤ q) (xs : List (Fin cardX)),
    (∀ x ∈ xs, H x = H' x) → measuredStateAt A H t ht xs = measuredStateAt A H' t ht xs
  | 0, _, _, _ => rfl
  | _ + 1, _, [], _ => rfl
  | t + 1, ht, x :: xs, h => by
    have ih := measuredStateAt_congr A H H' t (Nat.le_of_succ_le ht) xs
      (fun y hy => h y (.tail x hy))
    have hx : H x = H' x := h x (.head xs)
    show (A.steps ⟨t, ht⟩).apply (measuredOracleQueryBranch H
        (measuredStateAt A H t (Nat.le_of_succ_le ht) xs) x) =
      (A.steps ⟨t, ht⟩).apply (measuredOracleQueryBranch H'
        (measuredStateAt A H' t (Nat.le_of_succ_le ht) xs) x)
    rw [ih]
    refine congrArg (A.steps ⟨t, ht⟩).apply ?_
    funext x' y a
    simp only [measuredOracleQueryBranch, projSingle, oracleXor]
    by_cases hxx : x' = x
    · rw [ite_eq_left hxx, ite_eq_left hxx, hxx, hx]
    · rw [ite_eq_right hxx, ite_eq_right hxx]

/-- Born mass of one further measured query: the branch for outcome `x` carries the step
    scale times the pre-query weight of `x`. The oracle answer does not enter. -/
theorem measuredStateAt_succ_normSq {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w)
    (t : Nat) (ht : t + 1 ≤ q) (x : Fin cardX) (xs : List (Fin cardX)) :
    QVec.stateNormSq (measuredStateAt A H (t + 1) ht (x :: xs)) =
      (A.steps ⟨t, ht⟩).scaleSq *
        QVec.queryWeight (measuredStateAt A H t (Nat.le_of_succ_le ht) xs) x := by
  show QVec.stateNormSq ((A.steps ⟨t, ht⟩).apply (measuredOracleQueryBranch H
    (measuredStateAt A H t (Nat.le_of_succ_le ht) xs) x)) = _
  rw [(A.steps ⟨t, ht⟩).normSq_eq, (measuredOracleQueryBranch_mass H _).1 x]

theorem measuredStateAt_step_mass {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w)
    (t : Nat) (ht : t + 1 ≤ q) (xs : List (Fin cardX)) :
    qsum cardX (fun x => QVec.stateNormSq (measuredStateAt A H (t + 1) ht (x :: xs))) =
      (A.steps ⟨t, ht⟩).scaleSq *
        QVec.stateNormSq (measuredStateAt A H t (Nat.le_of_succ_le ht) xs) := by
  rw [qsum_congr (fun x => measuredStateAt_succ_normSq A H t ht x xs), qsum_mul_left]
  rfl

/-- The measured branches conserve the adversary's oracle-independent total mass, the same
    value as `runQuantumAdv_normSq` gives for the coherent execution. -/
theorem measuredStateAt_total_mass {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w) :
    ∀ (t : Nat) (ht : t ≤ q),
      sumLogs cardX t (fun xs => QVec.stateNormSq (measuredStateAt A H t ht xs)) =
        prefixScale A t ht * QVec.stateNormSq A.init
  | 0, _ => (Nat.one_mul _).symm
  | t + 1, ht => by
    have hSwap := sumLogs_qsum cardX t cardX
      (fun xs x => QVec.stateNormSq (measuredStateAt A H (t + 1) ht (x :: xs)))
    show qsum cardX (fun x => sumLogs cardX t (fun xs =>
      QVec.stateNormSq (measuredStateAt A H (t + 1) ht (x :: xs)))) = _
    rw [← hSwap, sumLogs_congr cardX t _ _ (fun xs => measuredStateAt_step_mass A H t ht xs),
      sumLogs_mul, measuredStateAt_total_mass A H t (Nat.le_of_succ_le ht)]
    exact (Nat.mul_assoc _ _ _).symm

/-- Output-register mass summed over all outputs of one branch is the branch mass. -/
private theorem qsum_queryWeight_eq {cardX w cardAnc : Nat} (ψ : QVec cardX w cardAnc) :
    qsum cardX (fun o => QVec.queryWeight ψ o) = QVec.stateNormSq ψ := rfl

/-- **Fresh-address target bound for the measured experiment.** The tested address
    `point H xs o` is computed from the query log `xs` and the final measured output `o`,
    possibly reading the oracle elsewhere. If that address is not in the log, its answer
    lies in the reprogramming-local list `targets H xs o` (at most `K` entries) with total
    mass at most `K / 2^w` of the oracle-averaged total mass. -/
theorem measured_fresh_target_hit_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (point : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Fin cardX)
    (targets : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → List (BitVec w))
    (K : Nat)
    (hPoint : ∀ H xs o ch,
      point (reprogramOracle H (point H xs o) ch) xs o = point H xs o)
    (hTargets : ∀ H xs o ch, listHasElem (point H xs o) xs = false →
      targets (reprogramOracle H (point H xs o) ch) xs o = targets H xs o)
    (hCard : ∀ H xs o, xs.length = Q → (targets H xs o).length ≤ K) :
    2 ^ w * uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (fun o => !listHasElem (point H xs o) xs &&
            listHasElem (H (point H xs o)) (targets H xs o))
          (measuredStateAt A H Q (Nat.le_refl Q) xs))) ≤
      K * ((2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)) := by
  let Wt : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Nat := fun H xs o =>
    QVec.queryWeight (measuredStateAt A H Q (Nat.le_refl Q) xs) o
  let G : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Nat := fun H xs o =>
    if (!listHasElem (point H xs o) xs &&
      listHasElem (H (point H xs o)) (targets H xs o)) = true then Wt H xs o else 0
  have hCell : ∀ xs o, xs.length = Q →
      2 ^ w * uniformOracleSum w cardX (fun H => G H xs o) ≤
        K * uniformOracleSum w cardX (fun H => Wt H xs o) := by
    intro xs o hLen
    refine uniform_fresh_point_bound w cardX (fun H => point H xs o)
      (fun H => !listHasElem (point H xs o) xs) (fun H => targets H xs o)
      (fun H => Wt H xs o) K (fun H ch => hPoint H xs o ch) ?_ ?_ ?_ ?_
    · intro H ch
      show (!listHasElem (point (reprogramOracle H (point H xs o) ch) xs o) xs) = _
      rw [hPoint]
    · intro H ch hOk
      exact hTargets H xs o ch (bool_not_eq_true hOk)
    · intro H ch hOk
      have hFresh := bool_not_eq_true hOk
      refine congrArg (fun ψ => QVec.queryWeight ψ o)
        (measuredStateAt_congr A _ H Q (Nat.le_refl Q) xs (fun y hy => ?_))
      refine reprogramOracle_of_ne _ _ _ _ (fun he => ?_)
      exact Bool.noConfusion (hFresh.symm.trans
        ((listHasElem_eq_true_iff (point H xs o) xs).mpr (he ▸ hy)))
    · intro H _
      exact hCard H xs o hLen
  have hL : uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        qsum cardX (fun o => G H xs o))) =
      sumLogs cardX Q (fun xs => qsum cardX (fun o =>
        uniformOracleSum w cardX (fun H => G H xs o))) :=
    (uniformOracleSum_sumLogs w cardX cardX Q (fun H xs => qsum cardX (fun o => G H xs o))).trans
      (sumLogs_congr cardX Q _ _ (fun xs =>
        uniformOracleSum_qsum w cardX cardX (fun H o => G H xs o)))
  have hTot : ∀ H, sumLogs cardX Q (fun xs => qsum cardX (fun o => Wt H xs o)) =
      prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init :=
    fun H => measuredStateAt_total_mass A H Q (Nat.le_refl Q)
  have hR : sumLogs cardX Q (fun xs => qsum cardX (fun o =>
        uniformOracleSum w cardX (fun H => Wt H xs o))) =
      (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init) := by
    rw [← sumLogs_congr cardX Q _ _ (fun xs =>
        uniformOracleSum_qsum w cardX cardX (fun H o => Wt H xs o)),
      ← uniformOracleSum_sumLogs w cardX cardX Q (fun H xs => qsum cardX (fun o => Wt H xs o)),
      uniformOracleSum_congr w cardX _ _ hTot, uniformOracleSum_const]
  show 2 ^ w * uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
    qsum cardX (fun o => G H xs o))) ≤ _
  rw [hL, ← hR, ← sumLogs_mul, ← sumLogs_mul]
  refine sumLogs_le_of_length cardX Q _ _ (fun xs hLen => ?_)
  rw [← qsum_mul_left, ← qsum_mul_left]
  exact qsum_le_qsum (fun o => hCell xs o hLen)

/-! ## Collisions among measured queries -/

/-- Some measured address was new when asked and received an answer already given to an
    earlier measured address. -/
def freshCollision {cardX w : Nat} (H : Fin cardX → BitVec w) : List (Fin cardX) → Bool
  | [] => false
  | x :: xs => (!listHasElem x xs && listHasElem (H x) (xs.map H)) || freshCollision H xs

/-- Two distinct logged addresses with equal answers force a `freshCollision`. -/
theorem freshCollision_of_distinct_equal {cardX w : Nat} (H : Fin cardX → BitVec w) :
    ∀ (xs : List (Fin cardX)) (a b : Fin cardX), a ∈ xs → b ∈ xs → a ≠ b → H a = H b →
      freshCollision H xs = true
  | [], _, _, ha, _, _, _ => nomatch ha
  | x :: xs, a, b, ha, hb, hne, hEq => by
    show ((!listHasElem x xs && listHasElem (H x) (xs.map H)) || freshCollision H xs) = true
    cases hIn : listHasElem x xs with
    | true =>
      have hxMem : x ∈ xs := (listHasElem_eq_true_iff x xs).mp hIn
      have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with rfl | h
        · exact hxMem
        · exact h
      have hb' : b ∈ xs := by
        rcases List.mem_cons.mp hb with rfl | h
        · exact hxMem
        · exact h
      rw [freshCollision_of_distinct_equal H xs a b ha' hb' hne hEq, Bool.or_true]
    | false =>
      have hxNot : ∀ y, y ∈ xs → y ≠ x := fun y hy he =>
        Bool.noConfusion (hIn.symm.trans ((listHasElem_eq_true_iff x xs).mpr (he ▸ hy)))
      have hHit : ∀ y, y ∈ xs → H x = H y → listHasElem (H x) (xs.map H) = true :=
        fun y hy he => (listHasElem_eq_true_iff (H x) (xs.map H)).mpr
          (he ▸ List.mem_map_of_mem hy)
      rcases List.mem_cons.mp ha with rfl | haT
      · rcases List.mem_cons.mp hb with rfl | hbT
        · exact absurd rfl hne
        · rw [hHit b hbT hEq]; rfl
      · rcases List.mem_cons.mp hb with rfl | hbT
        · rw [hHit a haT hEq.symm]; rfl
        · rw [freshCollision_of_distinct_equal H xs a b haT hbT hne hEq, Bool.or_true]

/-- `0 + 1 + ... + (t - 1)`. -/
def triangleSum : Nat → Nat
  | 0 => 0
  | t + 1 => triangleSum t + t

private theorem collision_step_arith (s tri t P M : Nat) :
    s * (tri * (P * M)) + t * (P * (s * M)) = (tri + t) * (P * (s * M)) := by
  rw [Nat.add_mul, Nat.mul_left_comm s tri (P * M), Nat.mul_left_comm s P M]

/-- **Birthday bound for the measured experiment.** Over a uniformly random oracle, the
    total mass of logs containing two distinct measured addresses with equal answers is at
    most `triangleSum t / 2^w` of the total mass. Adaptivity is handled by resampling the
    answer at the later address, whose branch weight was fixed before that answer existed. -/
theorem measured_record_collision_bound {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) : ∀ (t : Nat) (ht : t ≤ q),
    2 ^ w * uniformOracleSum w cardX (fun H => sumLogs cardX t (fun xs =>
        if freshCollision H xs = true then
          QVec.stateNormSq (measuredStateAt A H t ht xs) else 0)) ≤
      triangleSum t * ((2 ^ w) ^ cardX * (prefixScale A t ht * QVec.stateNormSq A.init))
  | 0, _ => by
    have hz : ∀ H : Fin cardX → BitVec w, sumLogs cardX 0 (fun xs =>
        if freshCollision H xs = true then
          QVec.stateNormSq (measuredStateAt A H 0 (Nat.zero_le q) xs) else 0) = 0 :=
      fun _ => rfl
    rw [uniformOracleSum_congr w cardX _ _ hz, uniformOracleSum_const]
    simp only [Nat.mul_zero, triangleSum, Nat.zero_mul, Nat.le_refl]
  | t + 1, ht => by
    have ht' : t ≤ q := Nat.le_of_succ_le ht
    let s := (A.steps ⟨t, ht⟩).scaleSq
    let Wq : (Fin cardX → BitVec w) → Fin cardX → List (Fin cardX) → Nat := fun H x xs =>
      s * QVec.queryWeight (measuredStateAt A H t ht' xs) x
    let a : (Fin cardX → BitVec w) → Fin cardX → List (Fin cardX) → Nat := fun H x xs =>
      if (!listHasElem x xs && listHasElem (H x) (xs.map H)) = true then Wq H x xs else 0
    let b : (Fin cardX → BitVec w) → Fin cardX → List (Fin cardX) → Nat := fun H x xs =>
      if freshCollision H xs = true then Wq H x xs else 0
    let Gt : (Fin cardX → BitVec w) → List (Fin cardX) → Nat := fun H xs =>
      if freshCollision H xs = true then
        QVec.stateNormSq (measuredStateAt A H t ht' xs) else 0
    let Tot := (2 ^ w) ^ cardX * (prefixScale A t ht' * QVec.stateNormSq A.init)
    -- pointwise split of the event at the most recent query
    have hSplit : ∀ H x xs,
        (if freshCollision H (x :: xs) = true then
          QVec.stateNormSq (measuredStateAt A H (t + 1) ht (x :: xs)) else 0) ≤
          a H x xs + b H x xs := by
      intro H x xs
      rw [measuredStateAt_succ_normSq A H t ht x xs]
      show (if ((!listHasElem x xs && listHasElem (H x) (xs.map H)) ||
          freshCollision H xs) = true then Wq H x xs else 0) ≤
        (if (!listHasElem x xs && listHasElem (H x) (xs.map H)) = true then Wq H x xs else 0) +
        (if freshCollision H xs = true then Wq H x xs else 0)
      cases (!listHasElem x xs && listHasElem (H x) (xs.map H)) <;>
        cases freshCollision H xs <;>
        simp only [Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte,
          Nat.zero_add, Nat.add_zero, Nat.le_refl, Nat.le_add_right]
    have hUpper : uniformOracleSum w cardX (fun H => sumLogs cardX (t + 1) (fun xs =>
          if freshCollision H xs = true then
            QVec.stateNormSq (measuredStateAt A H (t + 1) ht xs) else 0)) ≤
        uniformOracleSum w cardX (fun H => qsum cardX (fun x => sumLogs cardX t (a H x))) +
        uniformOracleSum w cardX (fun H => qsum cardX (fun x => sumLogs cardX t (b H x))) := by
      rw [← uniformOracleSum_add]
      refine uniformOracleSum_le w cardX _ _ (fun H => ?_)
      rw [← qsum_add]
      refine qsum_le_qsum (fun x => ?_)
      rw [← sumLogs_add]
      exact sumLogs_le_of_length cardX t _ _ (fun xs _ => hSplit H x xs)
    -- part B: marginalize the most recent query, then the induction hypothesis
    have hBeq : ∀ H, qsum cardX (fun x => sumLogs cardX t (b H x)) =
        s * sumLogs cardX t (Gt H) := by
      intro H
      rw [← sumLogs_qsum cardX t cardX (fun xs x => b H x xs), ← sumLogs_mul]
      refine sumLogs_congr cardX t _ _ (fun xs => ?_)
      show qsum cardX (fun x => if freshCollision H xs = true then
          s * QVec.queryWeight (measuredStateAt A H t ht' xs) x else 0) =
        s * (if freshCollision H xs = true then
          QVec.stateNormSq (measuredStateAt A H t ht' xs) else 0)
      cases freshCollision H xs
      · simp only [Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]
      · simp only [↓reduceIte, qsum_mul_left]
        rfl
    have hB : 2 ^ w * uniformOracleSum w cardX (fun H =>
          qsum cardX (fun x => sumLogs cardX t (b H x))) ≤ s * (triangleSum t * Tot) := by
      rw [uniformOracleSum_congr w cardX _ _ hBeq, uniformOracleSum_mul, Nat.mul_left_comm]
      exact Nat.mul_le_mul_left s (measured_record_collision_bound A t ht')
    -- part A: lazy sampling of the answer at a new address
    have hCell : ∀ x xs, xs.length = t →
        2 ^ w * uniformOracleSum w cardX (fun H => a H x xs) ≤
          t * uniformOracleSum w cardX (fun H => Wq H x xs) := by
      intro x xs hLen
      refine uniform_fresh_point_bound w cardX (fun _ => x) (fun _ => !listHasElem x xs)
        (fun H => xs.map H) (fun H => Wq H x xs) t (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_ ?_
      · intro H ch hOk
        exact map_reprogram_of_fresh H x ch xs (bool_not_eq_true hOk)
      · intro H ch hOk
        have hFresh := bool_not_eq_true hOk
        refine congrArg (fun ψ => s * QVec.queryWeight ψ x)
          (measuredStateAt_congr A _ H t ht' xs (fun y hy => ?_))
        refine reprogramOracle_of_ne _ _ _ _ (fun he => ?_)
        exact Bool.noConfusion (hFresh.symm.trans
          ((listHasElem_eq_true_iff x xs).mpr (he ▸ hy)))
      · intro H _
        rw [List.length_map, hLen]
        exact Nat.le_refl t
    have hWsum : ∀ H, qsum cardX (fun x => sumLogs cardX t (Wq H x)) =
        s * (prefixScale A t ht' * QVec.stateNormSq A.init) := by
      intro H
      rw [← sumLogs_qsum cardX t cardX (fun xs x => Wq H x xs),
        ← measuredStateAt_total_mass A H t ht', ← sumLogs_mul]
      refine sumLogs_congr cardX t _ _ (fun xs => ?_)
      show qsum cardX (fun x => s * QVec.queryWeight (measuredStateAt A H t ht' xs) x) = _
      rw [qsum_mul_left]
      rfl
    have hA : 2 ^ w * uniformOracleSum w cardX (fun H =>
          qsum cardX (fun x => sumLogs cardX t (a H x))) ≤
        t * ((2 ^ w) ^ cardX * (s * (prefixScale A t ht' * QVec.stateNormSq A.init))) := by
      have hAL : uniformOracleSum w cardX (fun H =>
            qsum cardX (fun x => sumLogs cardX t (a H x))) =
          qsum cardX (fun x => sumLogs cardX t (fun xs =>
            uniformOracleSum w cardX (fun H => a H x xs))) :=
        (uniformOracleSum_qsum w cardX cardX (fun H x => sumLogs cardX t (a H x))).trans
          (qsum_congr (fun x => uniformOracleSum_sumLogs w cardX cardX t (fun H => a H x)))
      have hAR : qsum cardX (fun x => sumLogs cardX t (fun xs =>
            uniformOracleSum w cardX (fun H => Wq H x xs))) =
          (2 ^ w) ^ cardX * (s * (prefixScale A t ht' * QVec.stateNormSq A.init)) := by
        rw [← qsum_congr (fun x => uniformOracleSum_sumLogs w cardX cardX t (fun H => Wq H x)),
          ← uniformOracleSum_qsum w cardX cardX (fun H x => sumLogs cardX t (Wq H x)),
          uniformOracleSum_congr w cardX _ _ hWsum, uniformOracleSum_const]
      rw [hAL, ← hAR, ← qsum_mul_left, ← qsum_mul_left]
      refine qsum_le_qsum (fun x => ?_)
      rw [← sumLogs_mul, ← sumLogs_mul]
      exact sumLogs_le_of_length cardX t _ _ (fun xs hLen => hCell x xs hLen)
    have hTotal := Nat.le_trans (Nat.mul_le_mul_left (2 ^ w) hUpper)
      (by rw [Nat.mul_add]; exact Nat.add_le_add hA hB)
    refine Nat.le_trans hTotal (Nat.le_of_eq ?_)
    show t * ((2 ^ w) ^ cardX * (s * (prefixScale A t ht' * QVec.stateNormSq A.init))) +
        s * (triangleSum t * ((2 ^ w) ^ cardX *
          (prefixScale A t ht' * QVec.stateNormSq A.init))) =
      (triangleSum t + t) * ((2 ^ w) ^ cardX *
        (s * prefixScale A t ht' * QVec.stateNormSq A.init))
    rw [Nat.mul_assoc s, Nat.add_comm]
    exact collision_step_arith s (triangleSum t) t _ _

end Qsag


namespace Qsag

set_option autoImplicit false

/-! ## Address layout and records -/

/-- How Merkle compression inputs `(lvl, node, left, right)` occupy oracle addresses.
    Addresses that are not compression inputs decode to `none`. -/
structure MerkleAddressLayout (cardX w : Nat) where
  encode : Nat → Nat → BitVec w → BitVec w → Fin cardX
  decode : Fin cardX → Option (Nat × Nat × BitVec w × BitVec w)
  levels : Nat
  nodes : Nat
  decode_sound : ∀ x l n u v, decode x = some (l, n, u, v) → encode l n u v = x
  decode_encode : ∀ l n u v, l < levels → n < nodes →
    decode (encode l n u v) = some (l, n, u, v)

/-- The tweaked compression function read through the layout. -/
def MerkleAddressLayout.hash {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) : Nat → Nat → BitVec w → BitVec w → BitVec w :=
  fun l n u v => H (L.encode l n u v)

/-- The classical record of one measured query, if its address is a compression input. -/
def merkleRecordOf {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (x : Fin cardX) : Option (RecordedMerkleQuery (BitVec w)) :=
  match L.decode x with
  | none => none
  | some (l, n, u, v) => some ⟨l, n, u, v, H x⟩

/-- Records of a measured query log. -/
def merkleRecords {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) :
    List (RecordedMerkleQuery (BitVec w)) :=
  xs.filterMap (merkleRecordOf L H)

theorem merkleRecordOf_some {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (x : Fin cardX) (q : RecordedMerkleQuery (BitVec w))
    (h : merkleRecordOf L H x = some q) :
    L.decode x = some (q.lvl, q.node, q.left, q.right) ∧ q.out = H x := by
  unfold merkleRecordOf at h
  cases hd : L.decode x with
  | none => rw [hd] at h; cases h
  | some τ =>
    obtain ⟨l, n, u, v⟩ := τ
    rw [hd] at h
    have h' : some (⟨l, n, u, v, H x⟩ : RecordedMerkleQuery (BitVec w)) = some q := h
    cases h'
    exact ⟨rfl, rfl⟩

/-- The records satisfy the classical classifier's consistency premise. It is derived from
    the measured log and the layout, not assumed. -/
theorem merkleRecords_consistent {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) :
    ∀ q ∈ merkleRecords L H xs, merkleQueryConsistent (L.hash H) q := by
  intro q hq
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.mp hq
  obtain ⟨hDec, hOut⟩ := merkleRecordOf_some L H x q hx
  show H (L.encode q.lvl q.node q.left q.right) = q.out
  rw [L.decode_sound x _ _ _ _ hDec, hOut]

private theorem listHasElem_false_cons {α : Type} [DecidableEq α] {x y : α} {ys : List α}
    (h : listHasElem x (y :: ys) = false) : y ≠ x ∧ listHasElem x ys = false := by
  refine ⟨fun he => Bool.noConfusion (h.symm.trans
    ((listHasElem_eq_true_iff x (y :: ys)).mpr (he ▸ .head ys))), ?_⟩
  cases hc : listHasElem x ys
  · rfl
  · exact Bool.noConfusion (h.symm.trans ((listHasElem_eq_true_iff x (y :: ys)).mpr
      (.tail y ((listHasElem_eq_true_iff x ys).mp hc))))

private theorem not_mem_of_listHasElem_false {α : Type} [DecidableEq α] {x : α} {ys : List α}
    (h : listHasElem x ys = false) : x ∉ ys :=
  fun hm => Bool.noConfusion (h.symm.trans ((listHasElem_eq_true_iff x ys).mpr hm))

/-- Records do not change when the oracle is reprogrammed at an unmeasured address. -/
theorem merkleRecords_reprogram_of_fresh {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (a : Fin cardX) (ch : BitVec w) :
    ∀ (xs : List (Fin cardX)), listHasElem a xs = false →
      merkleRecords L (reprogramOracle H a ch) xs = merkleRecords L H xs
  | [], _ => rfl
  | y :: ys, h => by
    obtain ⟨hya, hTail⟩ := listHasElem_false_cons h
    have hRec : merkleRecordOf L (reprogramOracle H a ch) y = merkleRecordOf L H y := by
      unfold merkleRecordOf
      rw [reprogramOracle_of_ne H a ch y hya]
    have ih := merkleRecords_reprogram_of_fresh L H a ch ys hTail
    unfold merkleRecords at ih ⊢
    rw [List.filterMap_cons, List.filterMap_cons, hRec, ih]

/-! ## The verifier's evaluation addresses -/

/-- Oracle addresses evaluated by `merkleRootFromPath` through the layout, leaf side first. -/
def merklePathPoints {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) : Nat → Nat → BitVec w → List (BitVec w) → List (Fin cardX)
  | _, _, _, [] => []
  | lvl, idx, cur, sib :: rest =>
    L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib) (if idx % 2 = 0 then sib else cur) ::
      merklePathPoints L H (lvl + 1) (idx / 2)
        (H (L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
          (if idx % 2 = 0 then sib else cur))) rest

theorem merklePathPoints_length {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) : ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w),
    (merklePathPoints L H lvl idx cur path).length = path.length
  | [], _, _, _ => rfl
  | _ :: rest, lvl, idx, _ =>
    congrArg Nat.succ (merklePathPoints_length L H rest (lvl + 1) (idx / 2) _)

/-- The root recomputation reads the oracle exactly along `merklePathPoints`. -/
theorem merkleRootFromPath_step {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (lvl idx : Nat) (cur sib : BitVec w) (rest : List (BitVec w)) :
    merkleRootFromPath (L.hash H) lvl idx cur (sib :: rest) =
      merkleRootFromPath (L.hash H) (lvl + 1) (idx / 2)
        (H (L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
          (if idx % 2 = 0 then sib else cur))) rest := by
  show merkleRootFromPath (L.hash H) (lvl + 1) (idx / 2)
    (if idx % 2 = 0 then L.hash H lvl (idx / 2) cur sib else L.hash H lvl (idx / 2) sib cur)
    rest = _
  by_cases hp : idx % 2 = 0
  · simp only [hp, ↓reduceIte, MerkleAddressLayout.hash]
  · simp only [hp, ↓reduceIte, MerkleAddressLayout.hash]

/-- Inside the tweak range, every evaluation address decodes to a level at or above the
    starting level. -/
theorem merklePathPoints_level {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) : ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w)
    (a : Fin cardX), lvl + path.length ≤ L.levels → idx < L.nodes →
    a ∈ merklePathPoints L H lvl idx cur path →
    ∃ τ, L.decode a = some τ ∧ lvl ≤ τ.1
  | [], _, _, _, _, _, _, ha => nomatch ha
  | sib :: rest, lvl, idx, cur, a, hLvl, hIdx, ha => by
    have hLen : (sib :: rest).length = rest.length + 1 := rfl
    have hl : lvl < L.levels := by omega
    have hn : idx / 2 < L.nodes := Nat.lt_of_le_of_lt (Nat.div_le_self idx 2) hIdx
    rcases List.mem_cons.mp ha with rfl | hTail
    · exact ⟨_, L.decode_encode lvl (idx / 2) _ _ hl hn, Nat.le_refl lvl⟩
    · obtain ⟨τ, hτ, hle⟩ := merklePathPoints_level L H rest (lvl + 1) (idx / 2) _ a
        (by omega) hn hTail
      exact ⟨τ, hτ, Nat.le_of_succ_le hle⟩

/-- Inside the tweak range, the `k`-th evaluation address is not changed by reprogramming
    the oracle at that address: it is computed from answers at strictly lower levels. -/
theorem merklePathPoints_reprogram {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (ch : BitVec w) :
    ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w) (k : Nat) (a : Fin cardX),
    lvl + path.length ≤ L.levels → idx < L.nodes →
    (merklePathPoints L H lvl idx cur path)[k]? = some a →
    (merklePathPoints L (reprogramOracle H a ch) lvl idx cur path)[k]? = some a
  | [], _, _, _, _, _, _, _, h => nomatch h
  | _ :: _, _, _, _, 0, _, _, _, h => h
  | sib :: rest, lvl, idx, cur, k + 1, a, hLvl, hIdx, h => by
    have hLen : (sib :: rest).length = rest.length + 1 := rfl
    have hl : lvl < L.levels := by omega
    have hn : idx / 2 < L.nodes := Nat.lt_of_le_of_lt (Nat.div_le_self idx 2) hIdx
    have hTail : (merklePathPoints L H (lvl + 1) (idx / 2)
        (H (L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
          (if idx % 2 = 0 then sib else cur))) rest)[k]? = some a := h
    have hMem := List.mem_of_getElem? hTail
    obtain ⟨τ, hτ, hle⟩ := merklePathPoints_level L H rest (lvl + 1) (idx / 2) _ a
      (by omega) hn hMem
    have hNe : L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
        (if idx % 2 = 0 then sib else cur) ≠ a := by
      intro he
      have hd := L.decode_encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
        (if idx % 2 = 0 then sib else cur) hl hn
      rw [he, hτ] at hd
      have hEq : τ.1 = lvl := congrArg Prod.fst (Option.some.inj hd)
      omega
    show (merklePathPoints L (reprogramOracle H a ch) (lvl + 1) (idx / 2)
        (reprogramOracle H a ch (L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib)
          (if idx % 2 = 0 then sib else cur))) rest)[k]? = some a
    rw [reprogramOracle_of_ne H a ch _ hNe]
    exact merklePathPoints_reprogram L H ch rest (lvl + 1) (idx / 2) _ k a (by omega) hn hTail

/-! ## Deterministic classification of an accepted opening -/

/-- Targets fixed by the measured log: the root, the children named in recorded inputs,
    and the recorded answers. -/
def merkleMeasuredTargets {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (rt : BitVec w) : List (BitVec w) :=
  rt :: (merkleChildTargets (merkleRecords L H xs) ++ xs.map H)

theorem merkleMeasuredTargets_length {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (rt : BitVec w) :
    (merkleMeasuredTargets L H xs rt).length ≤ 3 * xs.length + 1 := by
  have hRec : (merkleRecords L H xs).length ≤ xs.length := List.length_filterMap_le _ _
  simp only [merkleMeasuredTargets, List.length_cons, List.length_append,
    merkleChildTargets_length, List.length_map]
  omega

/-- An opening that verifies against the oracle either equals the opening extracted from
    the measured records, or the verifier evaluated an unmeasured address whose answer lies
    in the log-determined target list, or two distinct measured addresses share an answer.
    This uses only the layout laws; the records come from the log itself. -/
theorem merkle_measured_opening_classification {cardX w : Nat}
    (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) (xs : List (Fin cardX))
    (rt : BitVec w) :
    ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w),
    lvl + path.length ≤ L.levels → idx < L.nodes →
    merkleRootFromPath (L.hash H) lvl idx cur path = rt →
    extractOnlineMerkleOpening rt (merkleRecords L H xs) lvl path.length idx =
        some (cur, path) ∨
    (∃ a ∈ merklePathPoints L H lvl idx cur path, listHasElem a xs = false ∧
      listHasElem (H a) (merkleMeasuredTargets L H xs rt) = true) ∨
    freshCollision H xs = true
  | [], lvl, idx, cur, _, _, hRoot => by
    have hEq : cur = rt := hRoot
    subst hEq
    exact Or.inl rfl
  | sib :: rest, lvl, idx, cur, hLvl, hIdx, hRoot => by
    have hLen : (sib :: rest).length = rest.length + 1 := rfl
    have hl : lvl < L.levels := by omega
    have hn : idx / 2 < L.nodes := Nat.lt_of_le_of_lt (Nat.div_le_self idx 2) hIdx
    let lCh := if idx % 2 = 0 then cur else sib
    let rCh := if idx % 2 = 0 then sib else cur
    let a := L.encode lvl (idx / 2) lCh rCh
    let parent := H a
    have hRoot' : merkleRootFromPath (L.hash H) (lvl + 1) (idx / 2) parent rest = rt :=
      (merkleRootFromPath_step L H lvl idx cur sib rest).symm.trans hRoot
    have hDecA : L.decode a = some (lvl, idx / 2, lCh, rCh) :=
      L.decode_encode lvl (idx / 2) lCh rCh hl hn
    have hParentTarget : extractOnlineMerkleOpening rt (merkleRecords L H xs) (lvl + 1)
        rest.length (idx / 2) = some (parent, rest) →
        listHasElem parent (merkleMeasuredTargets L H xs rt) = true := by
      intro hExtUp
      refine (listHasElem_eq_true_iff _ _).mpr ?_
      cases rest with
      | nil =>
        have hPar : parent = rt := by
          simp only [List.length_nil, extractOnlineMerkleOpening, Option.some.injEq,
            Prod.mk.injEq] at hExtUp
          exact hExtUp.1.symm
        rw [hPar]
        exact .head _
      | cons s tl =>
        exact .tail _ (List.mem_append.mpr (Or.inl
          (extractOnlineMerkleOpening_succ_child rt (merkleRecords L H xs) (lvl + 1)
            tl.length (idx / 2) parent _ hExtUp)))
    rcases merkle_measured_opening_classification L H xs rt rest (lvl + 1) (idx / 2) parent
        (by omega) hn hRoot' with hExtUp | ⟨a', ha', hFresh, hHit⟩ | hColl
    · let pred := fun q : RecordedMerkleQuery (BitVec w) =>
        decide (q.lvl = lvl) && decide (q.node = idx / 2) && decide (q.out = parent)
      cases hFind : findFirst pred (merkleRecords L H xs) with
      | none =>
        -- the verifier's address was never measured, and its answer is a logged target
        have hFreshA : listHasElem a xs = false := by
          cases hc : listHasElem a xs
          · rfl
          · have haMem : a ∈ xs := (listHasElem_eq_true_iff a xs).mp hc
            have hRec : merkleRecordOf L H a = some ⟨lvl, idx / 2, lCh, rCh, parent⟩ := by
              unfold merkleRecordOf
              rw [hDecA]
            have hMemRec : (⟨lvl, idx / 2, lCh, rCh, parent⟩ : RecordedMerkleQuery (BitVec w)) ∈
                merkleRecords L H xs := List.mem_filterMap.mpr ⟨a, haMem, hRec⟩
            have hFalse := findFirst_none_spec pred hFind _ hMemRec
            simp only [pred, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
        exact Or.inr (Or.inl ⟨a, .head _, hFreshA, hParentTarget hExtUp⟩)
      | some q =>
        obtain ⟨hqMem, hqPred⟩ := findFirst_some_spec pred hFind
        simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hqPred
        obtain ⟨⟨hqLvl, hqNode⟩, hqOut⟩ := hqPred
        obtain ⟨x, hxMem, hxRec⟩ := List.mem_filterMap.mp hqMem
        obtain ⟨hDecX, hOutX⟩ := merkleRecordOf_some L H x q hxRec
        have hAns : H x = H a := hOutX.symm.trans hqOut
        by_cases hxa : x = a
        · -- the recorded query is the verifier's own evaluation: the opening is extracted
          rw [hxa, hDecA] at hDecX
          have hTup := Option.some.inj hDecX
          have hqL : q.left = lCh := (congrArg (fun τ => τ.2.2.1) hTup).symm
          have hqR : q.right = rCh := (congrArg (fun τ => τ.2.2.2) hTup).symm
          refine Or.inl ?_
          show extractOnlineMerkleOpening rt (merkleRecords L H xs) lvl (rest.length + 1) idx =
            some (cur, sib :: rest)
          unfold extractOnlineMerkleOpening
          rw [hExtUp]
          dsimp only
          rw [hFind]
          dsimp only
          by_cases hp : idx % 2 = 0
          · dsimp only [lCh, rCh] at hqL hqR
            simp only [hp, ↓reduceIte] at hqL hqR ⊢
            rw [hqL, hqR]
          · dsimp only [lCh, rCh] at hqL hqR
            simp only [hp, ↓reduceIte] at hqL hqR ⊢
            rw [hqL, hqR]
        · cases hc : listHasElem a xs with
          | true =>
            exact Or.inr (Or.inr (freshCollision_of_distinct_equal H xs x a hxMem
              ((listHasElem_eq_true_iff a xs).mp hc) hxa hAns))
          | false =>
            refine Or.inr (Or.inl ⟨a, .head _, hc, (listHasElem_eq_true_iff _ _).mpr ?_⟩)
            refine .tail _ (List.mem_append.mpr (Or.inr ?_))
            show H a ∈ xs.map H
            rw [← hAns]
            exact List.mem_map_of_mem hxMem
    · exact Or.inr (Or.inl ⟨a', .tail _ ha', hFresh, hHit⟩)
    · exact Or.inr (Or.inr hColl)

/-! ## The extraction-failure bound -/

/-- Opening read from the final measured output register. -/
structure MerkleOpeningReadout (w : Nat) where
  rt : BitVec w
  idx : Nat
  leaf : BitVec w
  path : List (BitVec w)

/-- The opening has the verifier's shape: path length at most `d`, index in range. -/
def merkleOpeningShape {cardX w : Nat} (L : MerkleAddressLayout cardX w) (d : Nat)
    (op : MerkleOpeningReadout w) : Bool :=
  decide (op.path.length ≤ d) && decide (op.idx < L.nodes)

/-- Extraction failure: the output opening has the verifier's shape and recomputes its
    root under the oracle, yet is not the opening extracted from the measured records. -/
def measuredMerkleFailure {cardX w : Nat} (L : MerkleAddressLayout cardX w) (lvl d : Nat)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (o : Fin cardX) : Bool :=
  merkleOpeningShape L d (opening o) &&
  decide (merkleRootFromPath (L.hash H) lvl (opening o).idx (opening o).leaf (opening o).path =
    (opening o).rt) &&
  !decide (extractOnlineMerkleOpening (opening o).rt (merkleRecords L H xs) lvl
    (opening o).path.length (opening o).idx = some ((opening o).leaf, (opening o).path))

/-- The `k`-th verifier evaluation address of the output opening (the output address itself
    when the opening is misshapen or shorter than `k + 1`). -/
def merkleFailurePoint {cardX w : Nat} (L : MerkleAddressLayout cardX w) (lvl d k : Nat)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (o : Fin cardX) : Fin cardX :=
  if merkleOpeningShape L d (opening o) = true then
    ((merklePathPoints L H lvl (opening o).idx (opening o).leaf (opening o).path)[k]?).getD o
  else o

/-- Targets for the `k`-th evaluation address (empty for a misshapen opening). -/
def merkleFailureTargets {cardX w : Nat} (L : MerkleAddressLayout cardX w) (d : Nat)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (o : Fin cardX) : List (BitVec w) :=
  if merkleOpeningShape L d (opening o) = true then
    merkleMeasuredTargets L H xs (opening o).rt
  else []

theorem merkleFailurePoint_local {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (lvl d k : Nat) (hLvl : lvl + d ≤ L.levels)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (o : Fin cardX) (ch : BitVec w) :
    merkleFailurePoint L lvl d k opening
      (reprogramOracle H (merkleFailurePoint L lvl d k opening H o) ch) o =
      merkleFailurePoint L lvl d k opening H o := by
  unfold merkleFailurePoint
  cases hShape : merkleOpeningShape L d (opening o) with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    simp only [merkleOpeningShape, Bool.and_eq_true, decide_eq_true_eq] at hShape
    have hRange : lvl + (opening o).path.length ≤ L.levels := by omega
    cases hk : (merklePathPoints L H lvl (opening o).idx (opening o).leaf (opening o).path)[k]? with
    | none =>
      have hLe := List.getElem?_eq_none_iff.mp hk
      rw [merklePathPoints_length] at hLe
      have hk' : (merklePathPoints L (reprogramOracle H o ch) lvl (opening o).idx
          (opening o).leaf (opening o).path)[k]? = none :=
        List.getElem?_eq_none_iff.mpr (by rw [merklePathPoints_length]; exact hLe)
      simp only [Option.getD_none, hk']
    | some a =>
      simp only [Option.getD_some]
      rw [merklePathPoints_reprogram L H ch _ lvl _ _ k a hRange hShape.2 hk]
      rfl

private theorem le_qsum_term {n : Nat} (f : Fin n → Nat) (k : Fin n) : f k ≤ qsum n f := by
  rw [← qsum_ite_eq n k (f k)]
  refine qsum_le_qsum (fun i => ?_)
  by_cases h : i = k
  · rw [ite_eq_left h, h]
    exact Nat.le_refl _
  · rw [ite_eq_right h]
    exact Nat.zero_le _

/-- Failure implies a fresh-address hit at one of the first `d` evaluation addresses, or a
    collision among measured answers. -/
theorem measuredMerkleFailure_cover {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (hLvl : lvl + d ≤ L.levels)
    (opening : Fin cardX → MerkleOpeningReadout w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (o : Fin cardX)
    (hFail : measuredMerkleFailure L lvl d opening H xs o = true) :
    (∃ k : Fin d,
      (!listHasElem (merkleFailurePoint L lvl d k.1 opening H o) xs &&
        listHasElem (H (merkleFailurePoint L lvl d k.1 opening H o))
          (merkleFailureTargets L d opening H xs o)) = true) ∨
    freshCollision H xs = true := by
  simp only [measuredMerkleFailure, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hFail
  obtain ⟨⟨hShape, hRoot⟩, hNot⟩ := hFail
  have hShape' := hShape
  simp only [merkleOpeningShape, Bool.and_eq_true, decide_eq_true_eq] at hShape'
  have hRange : lvl + (opening o).path.length ≤ L.levels := by omega
  rcases merkle_measured_opening_classification L H xs (opening o).rt (opening o).path lvl
      (opening o).idx (opening o).leaf hRange hShape'.2 hRoot with hExt | ⟨a, ha, hFresh, hHit⟩ | hC
  · exact absurd hExt hNot
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ha
    have hkLt : k < d := by
      have h1 := (List.getElem?_eq_some_iff.mp hk).1
      rw [merklePathPoints_length] at h1
      omega
    refine Or.inl ⟨⟨k, hkLt⟩, ?_⟩
    have hPt : merkleFailurePoint L lvl d k opening H o = a := by
      unfold merkleFailurePoint
      rw [ite_eq_left hShape, hk]
      rfl
    have hTg : merkleFailureTargets L d opening H xs o =
        merkleMeasuredTargets L H xs (opening o).rt := by
      unfold merkleFailureTargets
      rw [ite_eq_left hShape]
    show (!listHasElem (merkleFailurePoint L lvl d k opening H o) xs &&
      listHasElem (H (merkleFailurePoint L lvl d k opening H o))
        (merkleFailureTargets L d opening H xs o)) = true
    rw [hPt, hTg, hFresh, hHit]
    rfl
  · exact Or.inr hC

/-- **Merkle extraction-failure bound for the measured-query experiment.** For every
    `Q`-query adversary, layout and output readout, with the oracle uniform: the mass of
    outputs whose opening (path length at most `d`) verifies but is not the opening
    extracted from the measured query log is at most
    `(d * (3 * Q + 1) + triangleSum Q) / 2^w` of the total mass. In `RatBound.le` form this
    is `⟨failure mass, total⟩ ≤ ⟨d * (3 * Q + 1) + triangleSum Q, 2^w⟩`. -/
theorem measured_merkle_extraction_failure_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (hLvl : lvl + d ≤ L.levels)
    (opening : Fin cardX → MerkleOpeningReadout w) :
    2 ^ w * uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs)
          (measuredStateAt A H Q (Nat.le_refl Q) xs))) ≤
      (d * (3 * Q + 1) + triangleSum Q) *
        ((2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)) := by
  let Tot := (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)
  let ψ : (Fin cardX → BitVec w) → List (Fin cardX) → QVec cardX w cardAnc := fun H xs =>
    measuredStateAt A H Q (Nat.le_refl Q) xs
  let ev : Fin d → (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool :=
    fun k H xs o =>
      !listHasElem (merkleFailurePoint L lvl d k.1 opening H o) xs &&
        listHasElem (H (merkleFailurePoint L lvl d k.1 opening H o))
          (merkleFailureTargets L d opening H xs o)
  -- per-level fresh-address bound
  have hLevel : ∀ k : Fin d,
      2 ^ w * uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (ev k H xs) (ψ H xs))) ≤ (3 * Q + 1) * Tot := by
    intro k
    refine measured_fresh_target_hit_bound A
      (fun H _ o => merkleFailurePoint L lvl d k.1 opening H o)
      (fun H xs o => merkleFailureTargets L d opening H xs o) (3 * Q + 1)
      (fun H _ o ch => merkleFailurePoint_local L lvl d k.1 hLvl opening H o ch) ?_ ?_
    · intro H xs o ch hFresh
      unfold merkleFailureTargets
      cases merkleOpeningShape L d (opening o)
      · rfl
      · simp only [↓reduceIte, merkleMeasuredTargets]
        rw [merkleRecords_reprogram_of_fresh L H _ ch xs hFresh,
          map_reprogram_of_fresh H _ ch xs hFresh]
    · intro H xs o hLen
      unfold merkleFailureTargets
      cases merkleOpeningShape L d (opening o)
      · exact Nat.zero_le _
      · simp only [↓reduceIte]
        rw [← hLen]
        exact merkleMeasuredTargets_length L H xs _
  -- pointwise cover of the failure mass
  have hCover : ∀ H xs,
      QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs) (ψ H xs) ≤
        qsum d (fun k => QVec.queryMassOn (ev k H xs) (ψ H xs)) +
        (if freshCollision H xs = true then QVec.stateNormSq (ψ H xs) else 0) := by
    intro H xs
    have hColl : (if freshCollision H xs = true then QVec.stateNormSq (ψ H xs) else 0) =
        qsum cardX (fun o => if freshCollision H xs = true then
          QVec.queryWeight (ψ H xs) o else 0) := by
      cases freshCollision H xs
      · simp only [Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]
      · rfl
    have hSwap : qsum d (fun k => QVec.queryMassOn (ev k H xs) (ψ H xs)) =
        qsum cardX (fun o => qsum d (fun k =>
          if ev k H xs o = true then QVec.queryWeight (ψ H xs) o else 0)) :=
      qsum_comm d cardX (fun k o => if ev k H xs o = true then QVec.queryWeight (ψ H xs) o else 0)
    rw [hColl, hSwap, ← qsum_add]
    refine qsum_le_qsum (fun o => ?_)
    cases hF : measuredMerkleFailure L lvl d opening H xs o with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact Nat.zero_le _
    | true =>
      simp only [↓reduceIte]
      rcases measuredMerkleFailure_cover L lvl d hLvl opening H xs o hF with ⟨k, hk⟩ | hC
      · have hTerm := le_qsum_term
          (fun k => if ev k H xs o = true then QVec.queryWeight (ψ H xs) o else 0) k
        have hk' : ev k H xs o = true := hk
        simp only [hk', ↓reduceIte] at hTerm
        exact Nat.le_trans hTerm (Nat.le_add_right _ _)
      · rw [hC]
        exact Nat.le_add_left _ _
  have hSum : uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs) (ψ H xs))) ≤
      qsum d (fun k => uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (ev k H xs) (ψ H xs)))) +
      uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        if freshCollision H xs = true then QVec.stateNormSq (ψ H xs) else 0)) := by
    rw [← uniformOracleSum_qsum w cardX d (fun H k => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (ev k H xs) (ψ H xs))), ← uniformOracleSum_add]
    refine uniformOracleSum_le w cardX _ _ (fun H => ?_)
    rw [← sumLogs_qsum cardX Q d (fun xs k => QVec.queryMassOn (ev k H xs) (ψ H xs)),
      ← sumLogs_add]
    exact sumLogs_le_of_length cardX Q _ _ (fun xs _ => hCover H xs)
  have hLevels : 2 ^ w * qsum d (fun k => uniformOracleSum w cardX (fun H =>
        sumLogs cardX Q (fun xs => QVec.queryMassOn (ev k H xs) (ψ H xs)))) ≤
      d * ((3 * Q + 1) * Tot) := by
    rw [← qsum_mul_left, ← qsum_const d ((3 * Q + 1) * Tot)]
    exact qsum_le_qsum hLevel
  have hCollision := measured_record_collision_bound A Q (Nat.le_refl Q)
  have hAll := Nat.le_trans (Nat.mul_le_mul_left (2 ^ w) hSum)
    (by rw [Nat.mul_add]; exact Nat.add_le_add hLevels hCollision)
  refine Nat.le_trans hAll (Nat.le_of_eq ?_)
  show d * ((3 * Q + 1) * Tot) + triangleSum Q * Tot = (d * (3 * Q + 1) + triangleSum Q) * Tot
  rw [Nat.add_mul (d * (3 * Q + 1)) (triangleSum Q) Tot, Nat.mul_assoc d (3 * Q + 1) Tot]

/-! ## Size of the bound at deployment-scale parameters -/

theorem triangleSum_le_sq : ∀ t : Nat, triangleSum t ≤ t * t
  | 0 => Nat.le_refl 0
  | t + 1 => by
    have ih := triangleSum_le_sq t
    show triangleSum t + t ≤ (t + 1) * (t + 1)
    rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

/-- With 256-bit answers, up to `2^60` measured queries and paths of length up to 64, the
    failure fraction is below `2^-128`. -/
theorem measured_merkle_bound_below_128_bits (Q d : Nat) (hQ : Q ≤ 2 ^ 60) (hd : d ≤ 64) :
    (d * (3 * Q + 1) + triangleSum Q) * 2 ^ 128 < 2 ^ 256 := by
  have h1 : d * (3 * Q + 1) ≤ 64 * (3 * 2 ^ 60 + 1) :=
    Nat.mul_le_mul hd (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hQ) 1)
  have h2 : triangleSum Q ≤ 2 ^ 60 * 2 ^ 60 :=
    Nat.le_trans (triangleSum_le_sq Q) (Nat.mul_le_mul hQ hQ)
  have h3 : (d * (3 * Q + 1) + triangleSum Q) * 2 ^ 128 ≤
      (64 * (3 * 2 ^ 60 + 1) + 2 ^ 60 * 2 ^ 60) * 2 ^ 128 :=
    Nat.mul_le_mul_right _ (Nat.add_le_add h1 h2)
  exact Nat.lt_of_le_of_lt h3 (by decide)


end Qsag


namespace Qsag

set_option autoImplicit false

/-- The state before query `t` is supported on the single query address `addr H t`. -/
def ClassicalQueryAddresses {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) : Prop :=
  ∀ (H : Fin cardX → BitVec w) (t : Nat) (ht : t < q) (x : Fin cardX) (y : Fin (2 ^ w))
    (a : Fin cardAnc), x ≠ addr H t → advStateAt A H t (Nat.le_of_lt ht) x y a = GaussInt.zero

/-- The address log of the first `t` queries, most recent first. -/
def classicalQueryLog {cardX w : Nat} (addr : (Fin cardX → BitVec w) → Nat → Fin cardX)
    (H : Fin cardX → BitVec w) : Nat → List (Fin cardX)
  | 0 => []
  | t + 1 => addr H t :: classicalQueryLog addr H t

theorem classicalQueryLog_length {cardX w : Nat}
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (H : Fin cardX → BitVec w) :
    ∀ t, (classicalQueryLog addr H t).length = t
  | 0 => rfl
  | t + 1 => congrArg Nat.succ (classicalQueryLog_length addr H t)

theorem ScaledUnitary.apply_zero {cardX w cardAnc : Nat} (U : ScaledUnitary cardX w cardAnc) :
    U.apply (QVec.zero cardX w cardAnc) = QVec.zero cardX w cardAnc := by
  have hz : (QVec.zero cardX w cardAnc).sub (QVec.zero cardX w cardAnc) =
      QVec.zero cardX w cardAnc := rfl
  have h := U.map_sub (QVec.zero cardX w cardAnc) (QVec.zero cardX w cardAnc)
  rw [hz] at h
  rw [h]
  funext x y a
  exact GaussInt.ext (Int.sub_self _) (Int.sub_self _)

theorem queryMassOn_zero {cardX w cardAnc : Nat} (S : Fin cardX → Bool) :
    QVec.queryMassOn S (QVec.zero cardX w cardAnc) = 0 := by
  have hw : ∀ x, QVec.queryWeight (QVec.zero cardX w cardAnc) x = 0 := by
    intro x
    show qsum (2 ^ w) (fun _ => qsum cardAnc (fun _ => 0)) = 0
    simp only [qsum_const, Nat.mul_zero]
  have h0 : ∀ x, (if S x = true then QVec.queryWeight (QVec.zero cardX w cardAnc) x else 0) = 0 :=
    fun x => by rw [hw x]; exact ite_self 0
  show qsum cardX (fun x => if S x = true then
    QVec.queryWeight (QVec.zero cardX w cardAnc) x else 0) = 0
  rw [qsum_congr h0, qsum_const, Nat.mul_zero]

/-- Only the branch of the adversary's own address log is nonzero, and it is the coherent
    state. -/
theorem measuredStateAt_classical {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (H : Fin cardX → BitVec w) :
    ∀ (t : Nat) (ht : t ≤ q) (xs : List (Fin cardX)), xs.length = t →
      measuredStateAt A H t ht xs =
        if xs = classicalQueryLog addr H t then advStateAt A H t ht
        else QVec.zero cardX w cardAnc
  | 0, _, [], _ => (ite_eq_left rfl).symm
  | 0, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | _ + 1, _, [], h => absurd h.symm (Nat.succ_ne_zero _)
  | t + 1, ht, x :: xs, h => by
    have hLen : xs.length = t := Nat.succ.inj h
    have ih := measuredStateAt_classical A addr hC H t (Nat.le_of_succ_le ht) xs hLen
    show (A.steps ⟨t, ht⟩).apply (measuredOracleQueryBranch H
        (measuredStateAt A H t (Nat.le_of_succ_le ht) xs) x) =
      if x :: xs = addr H t :: classicalQueryLog addr H t then
        (A.steps ⟨t, ht⟩).apply (oracleXor H (advStateAt A H t (Nat.le_of_succ_le ht)))
      else QVec.zero cardX w cardAnc
    rw [ih]
    by_cases hxs : xs = classicalQueryLog addr H t
    · rw [ite_eq_left hxs]
      by_cases hx : x = addr H t
      · rw [ite_eq_left (by rw [hx, hxs])]
        refine congrArg (A.steps ⟨t, ht⟩).apply ?_
        funext x' y a
        show (if x' = x then oracleXor H (advStateAt A H t (Nat.le_of_succ_le ht)) x' y a
          else GaussInt.zero) = oracleXor H (advStateAt A H t (Nat.le_of_succ_le ht)) x' y a
        by_cases hx' : x' = x
        · rw [ite_eq_left hx']
        · rw [ite_eq_right hx']
          exact (hC H t ht x' _ a (fun he => hx' (he.trans hx.symm))).symm
      · rw [ite_eq_right (fun he => hx (List.cons.inj he).1)]
        have hz : measuredOracleQueryBranch H (advStateAt A H t (Nat.le_of_succ_le ht)) x =
            QVec.zero cardX w cardAnc := by
          funext x' y a
          show (if x' = x then oracleXor H (advStateAt A H t (Nat.le_of_succ_le ht)) x' y a
            else GaussInt.zero) = GaussInt.zero
          by_cases hx' : x' = x
          · rw [ite_eq_left hx']
            exact hC H t ht x' _ a (fun he => hx (hx'.symm.trans he))
          · rw [ite_eq_right hx']
        rw [hz, ScaledUnitary.apply_zero]
    · rw [ite_eq_right hxs, ite_eq_right (fun he => hxs (List.cons.inj he).2)]
      have hz : measuredOracleQueryBranch H (QVec.zero cardX w cardAnc) x =
          QVec.zero cardX w cardAnc := by
        funext x' y a
        show (if x' = x then GaussInt.zero else GaussInt.zero) = GaussInt.zero
        exact ite_self _
      rw [hz, ScaledUnitary.apply_zero]

/-- A log sum whose summand vanishes off one log is the summand at that log. -/
theorem sumLogs_single (cardX : Nat) : ∀ (t : Nat) (l : List (Fin cardX)), l.length = t →
    ∀ (f : List (Fin cardX) → Nat), (∀ xs, xs.length = t → xs ≠ l → f xs = 0) →
      sumLogs cardX t f = f l
  | 0, [], _, _, _ => rfl
  | 0, _ :: _, h, _, _ => absurd h (Nat.succ_ne_zero _)
  | _ + 1, [], h, _, _ => absurd h.symm (Nat.succ_ne_zero _)
  | t + 1, a :: l, h, f, hf => by
    have hInner : ∀ x, sumLogs cardX t (fun xs => f (x :: xs)) =
        if x = a then f (a :: l) else 0 := by
      intro x
      by_cases hx : x = a
      · rw [ite_eq_left hx, hx]
        exact sumLogs_single cardX t l (Nat.succ.inj h) (fun xs => f (a :: xs))
          (fun xs hLen hne => hf _ (congrArg Nat.succ hLen) (fun he => hne (List.cons.inj he).2))
      · rw [ite_eq_right hx]
        have hz : ∀ xs, xs.length = t → f (x :: xs) = 0 :=
          fun xs hLen => hf _ (congrArg Nat.succ hLen) (fun he => hx (List.cons.inj he).1)
        have hLe : sumLogs cardX t (fun xs => f (x :: xs)) ≤ sumLogs cardX t (fun _ => 0 * 0) :=
          sumLogs_le_of_length cardX t _ _ (fun xs hLen => Nat.le_of_eq (hz xs hLen))
        have hZero : sumLogs cardX t (fun _ => 0 * 0) = 0 :=
          (sumLogs_mul cardX t 0 (fun _ => 0)).trans (Nat.zero_mul _)
        exact Nat.le_antisymm (hZero ▸ hLe) (Nat.zero_le _)
    show qsum cardX (fun x => sumLogs cardX t (fun xs => f (x :: xs))) = f (a :: l)
    rw [qsum_congr hInner, qsum_ite_eq]

/-- **Transfer.** For a classical-address adversary, any log-indexed payoff that vanishes on
    the zero state has the same value in the measured experiment and in the coherent run
    with the adversary's own address log. -/
theorem classical_query_measured_eq {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (H : Fin cardX → BitVec w) (F : List (Fin cardX) → QVec cardX w cardAnc → Nat)
    (hF : ∀ xs, F xs (QVec.zero cardX w cardAnc) = 0) :
    sumLogs cardX q (fun xs => F xs (measuredStateAt A H q (Nat.le_refl q) xs)) =
      F (classicalQueryLog addr H q) (runQuantumAdv A H) := by
  have hAt := measuredStateAt_classical A addr hC H q (Nat.le_refl q)
  rw [sumLogs_single cardX q (classicalQueryLog addr H q) (classicalQueryLog_length addr H q)
    (fun xs => F xs (measuredStateAt A H q (Nat.le_refl q) xs))
    (fun xs hLen hne => by rw [hAt xs hLen, ite_eq_right hne]; exact hF xs)]
  rw [hAt _ (classicalQueryLog_length addr H q), ite_eq_left rfl]
  rfl

/-- **Merkle extraction-failure bound for classical-address adversaries, on the coherent
    run.** The extractor reads the adversary's own address log and the oracle answers at
    those addresses; the failure mass of `runQuantumAdv` is at most
    `(d * (3 * Q + 1) + triangleSum Q) / 2^w` of the total. -/
theorem classical_query_merkle_extraction_failure_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (hLvl : lvl + d ≤ L.levels)
    (opening : Fin cardX → MerkleOpeningReadout w) :
    2 ^ w * uniformOracleSum w cardX (fun H =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H (classicalQueryLog addr H Q))
          (runQuantumAdv A H)) ≤
      (d * (3 * Q + 1) + triangleSum Q) *
        ((2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)) := by
  have hEq : uniformOracleSum w cardX (fun H =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H (classicalQueryLog addr H Q))
          (runQuantumAdv A H)) =
      uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs)
          (measuredStateAt A H Q (Nat.le_refl Q) xs))) :=
    uniformOracleSum_congr w cardX _ _ (fun H =>
      (classical_query_measured_eq A addr hC H
        (fun xs ψ => QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs) ψ)
        (fun _ => queryMassOn_zero _)).symm)
  rw [hEq]
  exact measured_merkle_extraction_failure_bound A L lvl d hLvl opening


end Qsag


namespace Qsag
set_option autoImplicit false

/-- Unnormalized event mass, including the measured query log and uniform oracle. -/
def measuredEventMass {cardX w cardAnc Q : Nat} (A : QuantumAdv cardX w cardAnc Q)
    (event : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool) : Nat :=
  uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
    QVec.queryMassOn (event H xs) (measuredStateAt A H Q (Nat.le_refl Q) xs)))

def quantumExperimentTotal {cardX w cardAnc Q : Nat} (A : QuantumAdv cardX w cardAnc Q) : Nat :=
  (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)

theorem queryMassOn_union_le {cardX w cardAnc : Nat}
    (p r : Fin cardX → Bool) (ψ : QVec cardX w cardAnc) :
    QVec.queryMassOn (fun x => p x || r x) ψ ≤
      QVec.queryMassOn p ψ + QVec.queryMassOn r ψ := by
  unfold QVec.queryMassOn
  rw [← qsum_add]
  apply qsum_le_qsum
  intro x
  cases hp : p x <;> cases hr : r x <;> simp [hp, hr]

theorem measuredEventMass_union_le {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (p r : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool) :
    measuredEventMass A (fun H xs x => p H xs x || r H xs x) ≤
      measuredEventMass A p + measuredEventMass A r := by
  unfold measuredEventMass
  rw [← uniformOracleSum_add]
  apply uniformOracleSum_le
  intro H
  rw [← sumLogs_add]
  exact sumLogs_le_of_length cardX Q _ _ (fun xs _ => queryMassOn_union_le _ _ _)

theorem measuredEventMass_mono {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (p r : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool)
    (h : ∀ H xs x, p H xs x = true → r H xs x = true) :
    measuredEventMass A p ≤ measuredEventMass A r := by
  apply uniformOracleSum_le
  intro H
  apply sumLogs_le_of_length
  intro xs _
  apply qsum_le_qsum
  intro x
  change (if p H xs x = true then _ else 0) ≤ (if r H xs x = true then _ else 0)
  cases hp : p H xs x with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact Nat.zero_le _
  | true => simp [h H xs x hp]

structure MerkleOpeningSlot (cardX w : Nat) where
  level : Nat
  depth : Nat
  readout : Fin cardX → MerkleOpeningReadout w

def batchMerkleFailure {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (x : Fin cardX) : Bool :=
  slots.any (fun s => measuredMerkleFailure L s.level s.depth s.readout H xs x)

/-- This conservative budget counts the shared collision term once per opening. -/
def batchMerkleCost {cardX w : Nat} (Q : Nat) (slots : List (MerkleOpeningSlot cardX w)) : Nat :=
  (slots.map (fun s => s.depth * (3 * Q + 1) + triangleSum Q)).sum

/-- No locality or extraction-failure cover premise is required. -/
theorem measured_batch_merkle_extraction_failure_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L.levels) :
    2 ^ w * measuredEventMass A (batchMerkleFailure L slots) ≤
      batchMerkleCost Q slots * quantumExperimentTotal A := by
  induction slots with
  | nil =>
    unfold measuredEventMass
    change 2 ^ w * uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
      QVec.queryMassOn (fun _ => false) (measuredStateAt A H Q (Nat.le_refl Q) xs))) ≤ _
    have hz : ∀ H : Fin cardX → BitVec w,
        sumLogs cardX Q (fun xs => QVec.queryMassOn (fun _ => false)
          (measuredStateAt A H Q (Nat.le_refl Q) xs)) = 0 := by
      intro H
      have hp : ∀ xs, QVec.queryMassOn (fun _ => false)
          (measuredStateAt A H Q (Nat.le_refl Q) xs) = 0 := by
        intro xs; simp [QVec.queryMassOn, qsum_const]
      rw [show (fun xs => QVec.queryMassOn (fun _ => false)
        (measuredStateAt A H Q (Nat.le_refl Q) xs)) = fun _ => 0 * 0 from funext hp]
      rw [sumLogs_mul, Nat.zero_mul]
    rw [uniformOracleSum_congr w cardX _ _ hz, uniformOracleSum_const]
    simp
  | cons s rest ih =>
    have hOne := measured_merkle_extraction_failure_bound A L s.level s.depth
      (hLevels s (.head rest)) s.readout
    have hRest := ih (fun t ht => hLevels t (.tail s ht))
    have hUnion := measuredEventMass_union_le A
      (measuredMerkleFailure L s.level s.depth s.readout) (batchMerkleFailure L rest)
    have h := Nat.le_trans (Nat.mul_le_mul_left (2 ^ w) hUnion)
      (by rw [Nat.mul_add]; exact Nat.add_le_add hOne hRest)
    change 2 ^ w * measuredEventMass A (fun H xs x =>
      measuredMerkleFailure L s.level s.depth s.readout H xs x || batchMerkleFailure L rest H xs x) ≤ _
    simpa only [batchMerkleFailure, List.any_cons, batchMerkleCost, List.map_cons,
      List.sum_cons, Nat.add_mul, quantumExperimentTotal, measuredEventMass] using h

/-- General event transfer; no identification is made for superposition queries. -/
theorem measuredEventMass_classical {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (event : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool) :
    measuredEventMass A event = uniformOracleSum w cardX (fun H =>
      QVec.queryMassOn (event H (classicalQueryLog addr H Q)) (runQuantumAdv A H)) := by
  apply uniformOracleSum_congr
  intro H
  exact classical_query_measured_eq A addr hC H
    (fun xs ψ => QVec.queryMassOn (event H xs) ψ) (fun _ => queryMassOn_zero _)

/-- The batch bound transferred to the coherent run only for classical-address queries. -/
theorem classical_query_batch_merkle_extraction_failure_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (L : MerkleAddressLayout cardX w) (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L.levels) :
    2 ^ w * uniformOracleSum w cardX (fun H =>
      QVec.queryMassOn (batchMerkleFailure L slots H (classicalQueryLog addr H Q))
        (runQuantumAdv A H)) ≤ batchMerkleCost Q slots * quantumExperimentTotal A := by
  rw [← measuredEventMass_classical A addr hC (batchMerkleFailure L slots)]
  exact measured_batch_merkle_extraction_failure_bound A L slots hLevels

end Qsag


namespace Qsag
set_option autoImplicit false

/-- One bit for each of n oracle addresses. -/
@[reducible, expose] def OracleBitTable : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × OracleBitTable n

def oracleTableSum : (n : Nat) → (OracleBitTable n → Nat) → Nat
  | 0, f => f ()
  | n + 1, f => oracleTableSum n (fun h => f (false, h)) +
    oracleTableSum n (fun h => f (true, h))

theorem oracleTableSum_congr : ∀ n (f g : OracleBitTable n → Nat),
    (∀ h, f h = g h) → oracleTableSum n f = oracleTableSum n g
  | 0, _, _, h => h ()
  | n + 1, _, _, h => by
    simp only [oracleTableSum]
    rw [oracleTableSum_congr n _ _ (fun x => h (false, x)),
      oracleTableSum_congr n _ _ (fun x => h (true, x))]

theorem oracleTableSum_add : ∀ n (f g : OracleBitTable n → Nat),
    oracleTableSum n (fun h => f h + g h) = oracleTableSum n f + oracleTableSum n g
  | 0, _, _ => rfl
  | n + 1, _, _ => by
    simp only [oracleTableSum, oracleTableSum_add]; omega

theorem oracleTableSum_mul : ∀ n (c : Nat) (f : OracleBitTable n → Nat),
    oracleTableSum n (fun h => c * f h) = c * oracleTableSum n f
  | 0, _, _ => rfl
  | n + 1, _, _ => by simp only [oracleTableSum, oracleTableSum_mul, Nat.mul_add]

/-- Multiplication by 2^k, implemented additively for the existing linearity interface. -/
def gaussDoublePow : Nat → GaussInt → GaussInt
  | 0, z => z
  | k + 1, z => (gaussDoublePow k z).add (gaussDoublePow k z)

def oracleWalsh : (n : Nat) → (OracleBitTable n → GaussInt) → OracleBitTable n → GaussInt
  | 0, f, _ => f ()
  | n + 1, f, (b, d) =>
    let u := oracleWalsh n (fun h => f (false, h)) d
    let v := oracleWalsh n (fun h => f (true, h)) d
    if b then u.sub v else u.add v

theorem oracleWalsh_congr : ∀ n (f g : OracleBitTable n → GaussInt),
    (∀ h, f h = g h) → oracleWalsh n f = oracleWalsh n g := by
  intro n f g h
  exact congrArg (oracleWalsh n) (funext h)

theorem oracleWalsh_add : ∀ n (f g : OracleBitTable n → GaussInt) (d : OracleBitTable n),
    oracleWalsh n (fun h => (f h).add (g h)) d =
      (oracleWalsh n f d).add (oracleWalsh n g d)
  | 0, _, _, _ => rfl
  | n + 1, f, g, (b, d) => by
    simp only [oracleWalsh, oracleWalsh_add]
    cases b <;> apply GaussInt.ext <;> simp [GaussInt.add, GaussInt.sub] <;> omega

theorem oracleWalsh_sub : ∀ n (f g : OracleBitTable n → GaussInt) (d : OracleBitTable n),
    oracleWalsh n (fun h => (f h).sub (g h)) d =
      (oracleWalsh n f d).sub (oracleWalsh n g d)
  | 0, _, _, _ => rfl
  | n + 1, f, g, (b, d) => by
    simp only [oracleWalsh, oracleWalsh_sub]
    cases b <;> apply GaussInt.ext <;> simp [GaussInt.add, GaussInt.sub] <;> omega

theorem oracleWalsh_doublePow (n k : Nat) (f : OracleBitTable n → GaussInt) (d : OracleBitTable n) :
    oracleWalsh n (fun h => gaussDoublePow k (f h)) d = gaussDoublePow k (oracleWalsh n f d) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [gaussDoublePow, oracleWalsh_add, ih]

/-- Exact inverse up to the known integer normalization. -/
theorem oracleWalsh_square : ∀ n (f : OracleBitTable n → GaussInt) (d : OracleBitTable n),
    oracleWalsh n (oracleWalsh n f) d = gaussDoublePow n (f d)
  | 0, _, () => rfl
  | n + 1, f, (b, d) => by
    change (if b then
      (oracleWalsh n (fun h => (oracleWalsh n (fun z => f (false, z)) h).add
        (oracleWalsh n (fun z => f (true, z)) h)) d).sub
      (oracleWalsh n (fun h => (oracleWalsh n (fun z => f (false, z)) h).sub
        (oracleWalsh n (fun z => f (true, z)) h)) d)
      else (oracleWalsh n (fun h => (oracleWalsh n (fun z => f (false, z)) h).add
        (oracleWalsh n (fun z => f (true, z)) h)) d).add
      (oracleWalsh n (fun h => (oracleWalsh n (fun z => f (false, z)) h).sub
        (oracleWalsh n (fun z => f (true, z)) h)) d)) = _
    rw [oracleWalsh_add, oracleWalsh_sub, oracleWalsh_square, oracleWalsh_square]
    cases b <;> apply GaussInt.ext <;> simp [gaussDoublePow, GaussInt.add, GaussInt.sub] <;> omega

/-- Scaled isometry on the entire oracle register, for arbitrary coherent amplitudes. -/
theorem oracleWalsh_norm : ∀ n (f : OracleBitTable n → GaussInt),
    oracleTableSum n (fun d => GaussInt.normSq (oracleWalsh n f d)) =
      2 ^ n * oracleTableSum n (fun h => GaussInt.normSq (f h))
  | 0, _ => by simp [oracleTableSum, oracleWalsh]
  | n + 1, f => by
    change oracleTableSum n (fun d => GaussInt.normSq
      ((oracleWalsh n (fun h => f (false, h)) d).add (oracleWalsh n (fun h => f (true, h)) d))) +
      oracleTableSum n (fun d => GaussInt.normSq
      ((oracleWalsh n (fun h => f (false, h)) d).sub (oracleWalsh n (fun h => f (true, h)) d))) = _
    rw [← oracleTableSum_add]
    rw [oracleTableSum_congr n _ _ (fun d => (Nat.add_comm _ _).trans (GaussInt.normSq_parallelogram _ _))]
    rw [oracleTableSum_add, oracleTableSum_mul, oracleTableSum_mul,
      oracleWalsh_norm, oracleWalsh_norm]
    simp only [oracleTableSum, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]

theorem gaussDoublePow_norm (k : Nat) (z : GaussInt) :
    GaussInt.normSq (gaussDoublePow k z) = 4 ^ k * GaussInt.normSq z := by
  induction k with
  | zero => simp [gaussDoublePow]
  | succ k ih =>
    have h := GaussInt.normSq_parallelogram (gaussDoublePow k z) (gaussDoublePow k z)
    have hz : (gaussDoublePow k z).sub (gaussDoublePow k z) = GaussInt.zero := by
      apply GaussInt.ext <;> simp [GaussInt.sub, GaussInt.zero]
    rw [hz, GaussInt.normSq_zero, Nat.zero_add, ih] at h
    change GaussInt.normSq ((gaussDoublePow k z).add (gaussDoublePow k z)) = _
    rw [h, Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm]
    omega

end Qsag


namespace Qsag
set_option autoImplicit false

def tableBitOracle : (n : Nat) → OracleBitTable n → Fin n → BitVec 1
  | 0, _, x => Fin.elim0 x
  | n + 1, (b, h), x => Fin.cases (if b then 1#1 else 0#1) (tableBitOracle n h) x

/-- This table enumeration is precisely the existing uniform random-function experiment. -/
theorem oracleTableSum_eq_uniform : ∀ n (f : (Fin n → BitVec 1) → Nat),
    oracleTableSum n (fun h => f (tableBitOracle n h)) = uniformOracleSum 1 n f
  | 0, _ => rfl
  | n + 1, f => by
    change oracleTableSum n (fun h => f (Fin.cases 0#1 (tableBitOracle n h))) +
      oracleTableSum n (fun h => f (Fin.cases 1#1 (tableBitOracle n h))) = _
    rw [oracleTableSum_eq_uniform n (fun H => f (Fin.cases 0#1 H)),
      oracleTableSum_eq_uniform n (fun H => f (Fin.cases 1#1 H))]
    simp only [uniformOracleSum, qsum_zero, qsum_succ]
    rfl

/-- Finite sum exchange between the oracle register and a computational register. -/
theorem oracleTableSum_qsum (n k : Nat) (f : OracleBitTable n → Fin k → Nat) :
    oracleTableSum n (fun h => qsum k (f h)) = qsum k (fun i => oracleTableSum n (fun h => f h i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [oracleTableSum, ih, qsum_add]

theorem ScaledUnitary.map_add {cardX w cardAnc : Nat} (U : ScaledUnitary cardX w cardAnc)
    (ψ φ : QVec cardX w cardAnc) : U.apply (ψ.add φ) = (U.apply ψ).add (U.apply φ) := by
  have he : (ψ.add φ).sub φ = ψ := by
    funext x y a
    apply GaussInt.ext <;> simp [QVec.add, QVec.sub, GaussInt.add, GaussInt.sub]
  have h := U.map_sub (ψ.add φ) φ
  rw [he] at h
  funext x y a
  have hp := congrArg (fun v => v x y a) h
  have hr := congrArg GaussInt.re hp
  have hi := congrArg GaussInt.im hp
  apply GaussInt.ext <;> simp only [QVec.add, QVec.sub, GaussInt.add, GaussInt.sub] at * <;> omega

def qvecDoublePow {cardX w cardAnc : Nat} (k : Nat) (ψ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => gaussDoublePow k (ψ x y a)

theorem ScaledUnitary.map_doublePow {cardX w cardAnc : Nat} (U : ScaledUnitary cardX w cardAnc)
    (k : Nat) (ψ : QVec cardX w cardAnc) : U.apply (qvecDoublePow k ψ) = qvecDoublePow k (U.apply ψ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change U.apply ((qvecDoublePow k ψ).add (qvecDoublePow k ψ)) =
      (qvecDoublePow k (U.apply ψ)).add (qvecDoublePow k (U.apply ψ))
    rw [U.map_add, ih]

theorem gaussDoublePow_add (k l : Nat) (z : GaussInt) :
    gaussDoublePow k (gaussDoublePow l z) = gaussDoublePow (k + l) z := by
  induction k with
  | zero => simp only [gaussDoublePow, Nat.zero_add]
  | succ k ih => simp only [gaussDoublePow, ih, Nat.succ_add]

abbrev CoherentBitState (n cardAnc : Nat) := OracleBitTable n → QVec n 1 cardAnc

def fourierOracleState {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fun d x y a => oracleWalsh n (fun h => ψ h x y a) d

def doubleOracleState {n cardAnc : Nat} (k : Nat) (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fun h => qvecDoublePow k (ψ h)

theorem fourierOracleState_square {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc) :
    fourierOracleState (fourierOracleState ψ) = doubleOracleState n ψ := by
  funext h x y a
  exact oracleWalsh_square n _ h

theorem fourierOracleState_double {n cardAnc : Nat} (k : Nat) (ψ : CoherentBitState n cardAnc) :
    fourierOracleState (doubleOracleState k ψ) = doubleOracleState k (fourierOracleState ψ) := by
  funext h x y a
  exact oracleWalsh_doublePow n k _ h

theorem doubleOracleState_add {n cardAnc : Nat} (k l : Nat) (ψ : CoherentBitState n cardAnc) :
    doubleOracleState k (doubleOracleState l ψ) = doubleOracleState (k + l) ψ := by
  funext h x y a
  exact gaussDoublePow_add k l _

/-- Scaled isometry on the joint oracle and adversary state. -/
theorem fourierOracleState_norm {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc) :
    oracleTableSum n (fun d => QVec.stateNormSq (fourierOracleState ψ d)) =
      2 ^ n * oracleTableSum n (fun h => QVec.stateNormSq (ψ h)) := by
  unfold QVec.stateNormSq QVec.queryWeight fourierOracleState
  simp only [oracleTableSum_qsum, oracleWalsh_norm, qsum_mul_left]

/-- One ordinary coherent query to the table, followed by the oracle-independent local gate. -/
def coherentOracleStep {n cardAnc : Nat} (U : ScaledUnitary n 1 cardAnc)
    (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fun h => U.apply (oracleXor (tableBitOracle n h) (ψ h))

/-- Operational conjugated step. Both transforms are known gates; exactly one oracle query
    occurs. Unnormalized Walsh multiplies amplitude by 2^n per completed step. -/
def fourierOracleStep {n cardAnc : Nat} (U : ScaledUnitary n 1 cardAnc)
    (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fourierOracleState (coherentOracleStep U (fourierOracleState ψ))

theorem coherentOracleStep_double {n cardAnc : Nat} (U : ScaledUnitary n 1 cardAnc)
    (k : Nat) (ψ : CoherentBitState n cardAnc) :
    coherentOracleStep U (doubleOracleState k ψ) = doubleOracleState k (coherentOracleStep U ψ) := by
  funext h
  exact U.map_doublePow k (oracleXor (tableBitOracle n h) (ψ h))

/-- Independently stepped runtime, starting with the Fourier encoding of the uniform table. -/
def fourierAdvStateAt {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    (t : Nat) → t ≤ Q → CoherentBitState n cardAnc
  | 0, _ => fourierOracleState (fun _ => A.init)
  | t + 1, ht => fourierOracleStep (A.steps ⟨t, ht⟩)
      (fourierAdvStateAt A t (Nat.le_of_succ_le ht))

/-- Exact state equivalence for arbitrary superposition-query adversaries. No classical
    address restriction and no event cover occurs in this theorem. -/
theorem fourierAdvStateAt_eq {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    ∀ t (ht : t ≤ Q), fourierAdvStateAt A t ht =
      doubleOracleState (n * t) (fourierOracleState (fun h => advStateAt A (tableBitOracle n h) t ht))
  | 0, _ => rfl
  | t + 1, ht => by
    simp only [fourierAdvStateAt, fourierOracleStep, fourierAdvStateAt_eq,
      fourierOracleState_double, fourierOracleState_square, doubleOracleState_add,
      coherentOracleStep_double, Nat.mul_succ]
    rfl

/-- Decoding the final Fourier register recovers the actual coherent execution, including
    all oracle/output correlations; the normalization is known and oracle-independent. -/
theorem fourierAdvStateAt_decode {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q)) =
      doubleOracleState (n * Q + n) (fun h => runQuantumAdv A (tableBitOracle n h)) := by
  rw [fourierAdvStateAt_eq, fourierOracleState_double, fourierOracleState_square, doubleOracleState_add]
  rfl

/-- Observable event after decoding the oracle register. It may depend on both H and the
    final output x (e.g. root verification). No query-address measurement is inserted. -/
def coherentTableEventMass {n cardAnc : Nat}
    (event : (Fin n → BitVec 1) → Fin n → Bool) (ψ : CoherentBitState n cardAnc) : Nat :=
  oracleTableSum n (fun h => QVec.queryMassOn (event (tableBitOracle n h)) (ψ h))

theorem queryMassOn_doublePow {n w cardAnc : Nat} (k : Nat) (E : Fin n → Bool)
    (ψ : QVec n w cardAnc) : QVec.queryMassOn E (qvecDoublePow k ψ) = 4 ^ k * QVec.queryMassOn E ψ := by
  unfold QVec.queryMassOn QVec.queryWeight qvecDoublePow
  simp only [gaussDoublePow_norm, qsum_mul_left]
  rw [← qsum_mul_left]
  apply qsum_congr
  intro x
  cases E x <;> simp

/-- Exact unnormalized observable equivalence for every event, with explicit scale. -/
theorem fourierAdv_event_eq {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q)
    (event : (Fin n → BitVec 1) → Fin n → Bool) :
    coherentTableEventMass event (fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * Q + n) * uniformOracleSum 1 n
        (fun H => QVec.queryMassOn (event H) (runQuantumAdv A H)) := by
  rw [fourierAdvStateAt_decode]
  unfold coherentTableEventMass doubleOracleState
  simp only [queryMassOn_doublePow]
  rw [oracleTableSum_mul, oracleTableSum_eq_uniform n
    (fun H => QVec.queryMassOn (event H) (runQuantumAdv A H))]

end Qsag


namespace Qsag
set_option autoImplicit false

@[reducible] def tableBit : (n : Nat) → OracleBitTable n → Fin n → Bool
  | 0, _, x => Fin.elim0 x
  | _ + 1, (b, _), ⟨0, _⟩ => b
  | n + 1, (_, h), ⟨i + 1, hi⟩ => tableBit n h ⟨i, Nat.lt_of_succ_lt_succ hi⟩

@[reducible] def toggleTableBit : (n : Nat) → OracleBitTable n → Fin n → OracleBitTable n
  | 0, _, x => Fin.elim0 x
  | _ + 1, (b, d), ⟨0, _⟩ => (!b, d)
  | n + 1, (b, d), ⟨i + 1, hi⟩ => (b, toggleTableBit n d ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

@[reducible] def tableWeight : (n : Nat) → OracleBitTable n → Nat
  | 0, _ => 0
  | n + 1, (b, d) => (if b then 1 else 0) + tableWeight n d

/-- A single queried coordinate can change the Fourier database size by at most one. -/
theorem tableWeight_toggle_le : ∀ n (d : OracleBitTable n) (x : Fin n),
    tableWeight n d ≤ tableWeight n (toggleTableBit n d x) + 1
  | 0, _, x => Fin.elim0 x
  | n + 1, (b, d), x => by
    refine Fin.cases ?_ (fun j => ?_) x
    · change (if b then 1 else 0) + tableWeight n d ≤
        (if !b then 1 else 0) + tableWeight n d + 1
      cases b <;> simp <;> omega
    · have ih := tableWeight_toggle_le n d j
      change (if b then 1 else 0) + tableWeight n d ≤
        (if b then 1 else 0) + tableWeight n (toggleTableBit n d j) + 1
      omega

theorem oracleWalsh_neg : ∀ n (f : OracleBitTable n → GaussInt) (d : OracleBitTable n),
    oracleWalsh n (fun h => (f h).neg) d = (oracleWalsh n f d).neg
  | 0, _, _ => rfl
  | n + 1, f, (b, d) => by
    simp only [oracleWalsh, oracleWalsh_neg]
    cases b <;> apply GaussInt.ext <;> simp [GaussInt.neg, GaussInt.add, GaussInt.sub] <;> omega

/-- Operational Fourier query law for phase kickback, valid at superposed input addresses.
    Multiplication by (-1)^H(x) toggles database coordinate x coherently. -/
theorem oracleWalsh_phase_query : ∀ n (f : OracleBitTable n → GaussInt)
    (d : OracleBitTable n) (x : Fin n),
    oracleWalsh n (fun h => if tableBit n h x then (f h).neg else f h) d =
      oracleWalsh n f (toggleTableBit n d x)
  | 0, _, _, x => Fin.elim0 x
  | n + 1, f, (b, d), x => by
    refine Fin.cases ?_ (fun j => ?_) x
    · change (if b then
        (oracleWalsh n (fun h => f (false, h)) d).sub
          (oracleWalsh n (fun h => (f (true, h)).neg) d)
        else (oracleWalsh n (fun h => f (false, h)) d).add
          (oracleWalsh n (fun h => (f (true, h)).neg) d)) =
        (if !b then (oracleWalsh n (fun h => f (false, h)) d).sub
          (oracleWalsh n (fun h => f (true, h)) d)
        else (oracleWalsh n (fun h => f (false, h)) d).add
          (oracleWalsh n (fun h => f (true, h)) d))
      rw [oracleWalsh_neg]
      cases b <;> apply GaussInt.ext <;> simp [GaussInt.neg, GaussInt.add, GaussInt.sub] <;> omega
    · change (if b then
        (oracleWalsh n (fun h => if tableBit n h j then (f (false, h)).neg else f (false, h)) d).sub
          (oracleWalsh n (fun h => if tableBit n h j then (f (true, h)).neg else f (true, h)) d)
        else (oracleWalsh n (fun h => if tableBit n h j then (f (false, h)).neg else f (false, h)) d).add
          (oracleWalsh n (fun h => if tableBit n h j then (f (true, h)).neg else f (true, h)) d)) =
        (if b then (oracleWalsh n (fun h => f (false, h)) (toggleTableBit n d j)).sub
          (oracleWalsh n (fun h => f (true, h)) (toggleTableBit n d j))
        else (oracleWalsh n (fun h => f (false, h)) (toggleTableBit n d j)).add
          (oracleWalsh n (fun h => f (true, h)) (toggleTableBit n d j)))
      rw [oracleWalsh_phase_query n (fun h => f (false, h)) d j,
        oracleWalsh_phase_query n (fun h => f (true, h)) d j]

theorem oracleWalsh_const : ∀ n (z : GaussInt) (d : OracleBitTable n),
    oracleWalsh n (fun _ => z) d = if tableWeight n d = 0 then gaussDoublePow n z else GaussInt.zero
  | 0, _, _ => rfl
  | n + 1, z, (b, d) => by
    simp only [oracleWalsh, oracleWalsh_const, tableWeight]
    by_cases hd : tableWeight n d = 0
    · rw [ite_eq_left hd]
      cases b <;> apply GaussInt.ext <;>
        simp [hd, gaussDoublePow, GaussInt.add, GaussInt.sub, GaussInt.zero]
    · rw [ite_eq_right hd]
      have hn : 0 < tableWeight n d := Nat.pos_of_ne_zero hd
      cases b <;> apply GaussInt.ext <;>
        simp [hd, GaussInt.add, GaussInt.sub, GaussInt.zero]

/-- Uniform oracle purification starts at the empty Fourier label, without measuring H. -/
theorem fourier_initial_empty {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q)
    (d : OracleBitTable n) (h : tableWeight n d ≠ 0) :
    fourierAdvStateAt A 0 (Nat.zero_le Q) d = QVec.zero n 1 cardAnc := by
  funext x y a
  exact (oracleWalsh_const n (A.init x y a) d).trans (ite_eq_right h)

/-- The finite bit-table decoder agrees pointwise with its Boolean coordinate. -/
theorem tableBitOracle_eq : ∀ n (h : OracleBitTable n) (x : Fin n),
    tableBitOracle n h x = if tableBit n h x then 1#1 else 0#1
  | 0, _, x => Fin.elim0 x
  | n + 1, (b, h), x => by
    refine Fin.cases ?_ (fun j => ?_) x
    · rfl
    · exact tableBitOracle_eq n h j

/-- Multiplexer law: the computational-response query is a coherent sum of an unchanged
    database label and a one-coordinate toggle, with exact factor two normalization. -/
theorem oracleWalsh_mux (n : Nat) (f g : OracleBitTable n → GaussInt)
    (d : OracleBitTable n) (x : Fin n) :
    gaussDoublePow 1 (oracleWalsh n (fun h => if tableBit n h x then g h else f h) d) =
      ((oracleWalsh n f d).add (oracleWalsh n g d)).add
        ((oracleWalsh n f (toggleTableBit n d x)).sub (oracleWalsh n g (toggleTableBit n d x))) := by
  rw [← oracleWalsh_doublePow]
  have hp : ∀ h, gaussDoublePow 1 (if tableBit n h x then g h else f h) =
      ((f h).add (g h)).add (if tableBit n h x then ((f h).sub (g h)).neg else (f h).sub (g h)) := by
    intro h
    cases tableBit n h x <;> apply GaussInt.ext <;>
      simp [gaussDoublePow, GaussInt.add, GaussInt.sub, GaussInt.neg] <;> omega
  rw [oracleWalsh_congr n _ _ hp, oracleWalsh_add, oracleWalsh_add,
    oracleWalsh_phase_query, oracleWalsh_sub]

/-- Fourier transform commutes with every existing adversary local gate: no operation
    on the oracle register is smuggled into the adversary interface. -/
theorem oracleWalsh_local {cardX w cardAnc : Nat} (U : ScaledUnitary cardX w cardAnc) :
    ∀ k (ψ : OracleBitTable k → QVec cardX w cardAnc) (d : OracleBitTable k),
    U.apply (fun x y a => oracleWalsh k (fun h => ψ h x y a) d) =
      fun x y a => oracleWalsh k (fun h => U.apply (ψ h) x y a) d
  | 0, _, () => rfl
  | k + 1, ψ, (b, d) => by
    cases b
    · change U.apply (QVec.add (fun x y a => oracleWalsh k (fun h => ψ (false, h) x y a) d)
        (fun x y a => oracleWalsh k (fun h => ψ (true, h) x y a) d)) = _
      rw [U.map_add, oracleWalsh_local, oracleWalsh_local]
      rfl
    · change U.apply (QVec.sub (fun x y a => oracleWalsh k (fun h => ψ (false, h) x y a) d)
        (fun x y a => oracleWalsh k (fun h => ψ (true, h) x y a) d)) = _
      rw [U.map_sub, oracleWalsh_local, oracleWalsh_local]
      rfl

/-- A full XOR-response query can only use the old label and a one-coordinate toggle. -/
theorem fourier_query_zero_of_neighbors {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc)
    (d : OracleBitTable n)
    (hd : fourierOracleState ψ d = QVec.zero n 1 cardAnc)
    (ht : ∀ x, fourierOracleState ψ (toggleTableBit n d x) = QVec.zero n 1 cardAnc) :
    fourierOracleState (fun h => oracleXor (tableBitOracle n h) (ψ h)) d = QVec.zero n 1 cardAnc := by
  funext x y a
  have hq : (fun h => oracleXor (tableBitOracle n h) (ψ h) x y a) =
      (fun h => if tableBit n h x then ψ h x (xorFin y 1#1) a else ψ h x y a) := by
    funext h
    unfold oracleXor
    rw [tableBitOracle_eq]
    cases tableBit n h x
    · have hz : xorFin y 0#1 = y := by revert y; decide
      simp only [Bool.false_eq_true, ↓reduceIte, hz]
    · rfl
  have hm := oracleWalsh_mux n (fun h => ψ h x y a) (fun h => ψ h x (xorFin y 1#1) a) d x
  have hd0 := congrArg (fun v => v x y a) hd
  have hd1 := congrArg (fun v => v x (xorFin y 1#1) a) hd
  have ht0 := congrArg (fun v => v x y a) (ht x)
  have ht1 := congrArg (fun v => v x (xorFin y 1#1) a) (ht x)
  change oracleWalsh n (fun h => ψ h x y a) d = GaussInt.zero at hd0
  change oracleWalsh n (fun h => ψ h x (xorFin y 1#1) a) d = GaussInt.zero at hd1
  change oracleWalsh n (fun h => ψ h x y a) (toggleTableBit n d x) = GaussInt.zero at ht0
  change oracleWalsh n (fun h => ψ h x (xorFin y 1#1) a) (toggleTableBit n d x) = GaussInt.zero at ht1
  rw [hd0, hd1, ht0, ht1] at hm
  change oracleWalsh n (fun h => oracleXor (tableBitOracle n h) (ψ h) x y a) d = GaussInt.zero
  rw [hq]
  have hr := congrArg GaussInt.re hm
  have hi := congrArg GaussInt.im hm
  apply GaussInt.ext <;> simp only [gaussDoublePow, GaussInt.add, GaussInt.sub, GaussInt.zero] at * <;> omega

/-- Genuine coherent sparsity invariant: after t queries the Fourier truth-table register
    has zero amplitude on labels with more than t nonzero coordinates. This is not a list
    of queried addresses or a table of measured oracle answers. -/
theorem fourier_coherent_support {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    ∀ t (ht : t ≤ Q) (d : OracleBitTable n), t < tableWeight n d →
      fourierOracleState (fun h => advStateAt A (tableBitOracle n h) t ht) d = QVec.zero n 1 cardAnc
  | 0, _, d, hd => by
    funext x y a
    exact (oracleWalsh_const n (A.init x y a) d).trans (ite_eq_right (by omega))
  | t + 1, ht, d, hd => by
    let ψ := fun h => advStateAt A (tableBitOracle n h) t (Nat.le_of_succ_le ht)
    have hD : fourierOracleState ψ d = QVec.zero n 1 cardAnc :=
      fourier_coherent_support A t (Nat.le_of_succ_le ht) d (by omega)
    have hT : ∀ x, fourierOracleState ψ (toggleTableBit n d x) = QVec.zero n 1 cardAnc := by
      intro x
      have hw := tableWeight_toggle_le n d x
      exact fourier_coherent_support A t (Nat.le_of_succ_le ht) _ (by omega)
    have hz := fourier_query_zero_of_neighbors ψ d hD hT
    have hl := oracleWalsh_local (A.steps ⟨t, ht⟩) n
      (fun h => oracleXor (tableBitOracle n h) (ψ h)) d
    change (fun x y a => oracleWalsh n
      (fun h => (A.steps ⟨t, ht⟩).apply (oracleXor (tableBitOracle n h) (ψ h)) x y a) d) = _
    rw [← hl]
    change (A.steps ⟨t, ht⟩).apply (fourierOracleState
      (fun h => oracleXor (tableBitOracle n h) (ψ h)) d) = _
    rw [hz, ScaledUnitary.apply_zero]

/-- The independently executed Fourier runtime obeys the same Q-entry support cap. -/
theorem fourier_runtime_support {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q)
    (t : Nat) (ht : t ≤ Q) (d : OracleBitTable n) (hd : t < tableWeight n d) :
    fourierAdvStateAt A t ht d = QVec.zero n 1 cardAnc := by
  rw [fourierAdvStateAt_eq]
  have hz := fourier_coherent_support A t ht d hd
  change qvecDoublePow (n * t) (fourierOracleState
    (fun h => advStateAt A (tableBitOracle n h) t ht) d) = _
  rw [hz]
  funext x y a
  change gaussDoublePow (n * t) GaussInt.zero = GaussInt.zero
  generalize n * t = k
  induction k with
  | zero => rfl
  | succ k ih => simp only [gaussDoublePow, ih]; rfl

/-- Terminal measurement of the Fourier label never reports more than Q nonzero entries.
    Reading such a label is not reading the original oracle answers. -/
theorem fourier_database_overflow_mass_zero {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    oracleTableSum n (fun d => if Q < tableWeight n d then
      QVec.stateNormSq (fourierAdvStateAt A Q (Nat.le_refl Q) d) else 0) = 0 := by
  have h : ∀ d : OracleBitTable n, (if Q < tableWeight n d then
      QVec.stateNormSq (fourierAdvStateAt A Q (Nat.le_refl Q) d) else 0) = 0 := by
    intro d
    by_cases hd : Q < tableWeight n d
    · rw [ite_eq_left hd, fourier_runtime_support A Q (Nat.le_refl Q) d hd]
      simp [QVec.stateNormSq, QVec.queryWeight, QVec.zero, GaussInt.normSq_zero, qsum_const]
    · exact ite_eq_right hd
  rw [oracleTableSum_congr n _ _ h]
  have hz : ∀ k, oracleTableSum k (fun _ => 0) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [oracleTableSum, ih, Nat.zero_add]
  exact hz n

def tableSame : (n : Nat) → OracleBitTable n → OracleBitTable n → Bool
  | 0, _, _ => true
  | n + 1, (a, d), (b, e) => (a == b) && tableSame n d e

/-- Actual projective measurement branch on the Fourier database. -/
def projectFourierLabel {n cardAnc : Nat} (d : OracleBitTable n)
    (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fun e x y a => if tableSame n d e then ψ e x y a else GaussInt.zero

theorem oracleTableSum_zero : ∀ n, oracleTableSum n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by simp only [oracleTableSum, oracleTableSum_zero, Nat.zero_add]

/-- A complete computational-basis label projector picks exactly one summand. -/
theorem oracleTableSum_single : ∀ n (d : OracleBitTable n) (f : OracleBitTable n → Nat),
    oracleTableSum n (fun e => if tableSame n d e then f e else 0) = f d
  | 0, (), _ => rfl
  | n + 1, (b, d), f => by
    cases b <;> simp only [oracleTableSum, tableSame, Bool.false_beq, Bool.true_beq,
      Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · rw [oracleTableSum_single, oracleTableSum_zero, Nat.add_zero]
    · rw [oracleTableSum_zero, oracleTableSum_single, Nat.zero_add]

/-- Mass of one explicit Fourier-label measurement branch. -/
theorem projectFourierLabel_norm {n cardAnc : Nat} (d : OracleBitTable n)
    (ψ : CoherentBitState n cardAnc) :
    oracleTableSum n (fun e => QVec.stateNormSq (projectFourierLabel d ψ e)) = QVec.stateNormSq (ψ d) := by
  have h : ∀ e : OracleBitTable n, QVec.stateNormSq (projectFourierLabel d ψ e) =
      if tableSame n d e then QVec.stateNormSq (ψ e) else 0 := by
    intro e
    cases he : tableSame n d e
    · simp only [projectFourierLabel, he, Bool.false_eq_true, ↓reduceIte,
        QVec.stateNormSq, QVec.queryWeight, GaussInt.normSq_zero, qsum_const, Nat.mul_zero]
    · have hp : projectFourierLabel d ψ e = ψ e := by
        funext x y a
        exact ite_eq_left he
      rw [hp]
      rfl
  rw [oracleTableSum_congr n _ _ h, oracleTableSum_single]

/-- Measuring the database preserves total probability, even though the correlations
    tested by an oracle-dependent verifier can change after decoding. -/
theorem fourier_label_measurement_total {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc) :
    oracleTableSum n (fun d => oracleTableSum n (fun e =>
      QVec.stateNormSq (fourierOracleState (projectFourierLabel d ψ) e))) =
      oracleTableSum n (fun e => QVec.stateNormSq (fourierOracleState ψ e)) := by
  simp only [fourierOracleState_norm, projectFourierLabel_norm, oracleTableSum_mul]

end Qsag

namespace Qsag.PreprocessingGame
set_option autoImplicit false

/-- A classical adaptive online algorithm with an upper bound on queries on every branch.
There is no restriction on the size of its code or its local workspace. -/
inductive Program (X Y Out : Type) : Nat → Type where
  | done {q : Nat} : Out → Program X Y Out q
  | query {q : Nat} : X → (Y → Program X Y Out q) → Program X Y Out (q + 1)

def Program.run {X Y Out : Type} {q : Nat} (H : X → Y) :
    Program X Y Out q → Out × Nat
  | .done out => (out, 0)
  | .query x next => let result := (next (H x)).run H; (result.1, result.2 + 1)

theorem Program.queries_le {X Y Out : Type} {q : Nat} (H : X → Y)
    (A : Program X Y Out q) : (A.run H).2 ≤ q := by
  induction A with
  | done out => exact Nat.zero_le _
  | query x next ih => exact Nat.succ_le_succ (ih (H x))

/-- Unbounded offline computation with oracle-dependent classical advice. Challenge
randomness is unavailable to preprocessing; oracle dependence is deliberately allowed. -/
structure ClassicalAdvice (n w k bits q : Nat) (Out : Type) where
  preprocess : (Fin n → BitVec w) → BitVec bits
  online : BitVec bits → Fin k → Program (Fin n) (BitVec w) Out q

def ClassicalAdvice.run {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out) (H : Fin n → BitVec w) (salt : Fin k) : Out × Nat :=
  (A.online (A.preprocess H) salt).run H

theorem ClassicalAdvice.online_queries_le {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out) (H : Fin n → BitVec w) (salt : Fin k) :
    (A.run H salt).2 ≤ q := Program.queries_le H _

/-- Counts oracle/challenge pairs. The denominator for positive k is `(2^w)^n * k`.
The win predicate can include verification calls; those calls are NOT in the online count. -/
def adviceWinCount {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out)
    (win : (Fin n → BitVec w) → Fin k → Out → Bool) : Nat :=
  uniformOracleSum w n fun H => qsum k fun salt =>
    if win H salt (A.run H salt).1 then 1 else 0

def fixedAdviceWinCount {n w k bits q : Nat} {Out : Type}
    (online : BitVec bits → Fin k → Program (Fin n) (BitVec w) Out q)
    (win : (Fin n → BitVec w) → Fin k → Out → Bool) (advice : BitVec bits) : Nat :=
  uniformOracleSum w n fun H => qsum k fun salt =>
    if win H salt ((online advice salt).run H).1 then 1 else 0

/-- A selected term is at most the sum, constructively and without a finite-set library. -/
theorem selected_le_sum {m : Nat} (a : Fin m) (f : Fin m → Nat) : f a ≤ qsum m f := by
  rw [← qsum_ite_eq m a (f a)]
  exact qsum_le_qsum fun i => by
    by_cases h : i = a
    · subst i; simp
    · simp [h]

/-- Exact reduction to the sum of fixed-advice experiments. No hardness premise, no
oracle-independent assumption on preprocessing, and no assumption of successful extraction. -/
theorem adviceWinCount_le_sum_fixed {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out)
    (win : (Fin n → BitVec w) → Fin k → Out → Bool) :
    adviceWinCount A win ≤ qsum (2 ^ bits) fun a =>
      fixedAdviceWinCount A.online win (BitVec.ofFin a) := by
  unfold adviceWinCount fixedAdviceWinCount
  rw [← uniformOracleSum_qsum]
  apply uniformOracleSum_le
  intro H
  rw [qsum_comm]
  apply qsum_le_qsum
  intro salt
  have h := selected_le_sum (A.preprocess H).toFin (fun a =>
    if win H salt ((A.online (BitVec.ofFin a) salt).run H).1 then 1 else 0)
  exact h

/-- If each oracle-independent fixed-advice experiment has count at most B, the
oracle-dependent experiment has count at most `2^bits * B`. This deliberately loose
classical advice union bound does not claim the literature's stronger QAI estimates. -/
theorem adviceWinCount_le_capacity_mul {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out)
    (win : (Fin n → BitVec w) → Fin k → Out → Bool) (B : Nat)
    (hB : ∀ a, fixedAdviceWinCount A.online win a ≤ B) :
    adviceWinCount A win ≤ 2 ^ bits * B := by
  apply Nat.le_trans (adviceWinCount_le_sum_fixed A win)
  have h := qsum_le_qsum (fun a : Fin (2 ^ bits) => hB (BitVec.ofFin a))
  simpa only [qsum_const] using h

/-- The actual output pair must be distinct and collide; existence of some other pair
is irrelevant to this verifier. -/
def collisionWin {n w : Nat} (H : Fin n → BitVec w) (pair : Fin n × Fin n) : Bool :=
  decide (pair.1 ≠ pair.2 ∧ H pair.1 = H pair.2)

/-! ## A fresh-salt table attack with a sharp table-entry bound

This strategy is a special case, not a bound on arbitrary S-bit advice. An entry
contains one salt and one candidate. After seeing the fresh uniform salt, the online
algorithm returns the first matching candidate or fails. It does not inspect H.
Table capacity is number of entries, and is not mislabeled as number of advice bits.
-/

def lookup {k : Nat} {Out : Type} (salt : Fin k) : List (Fin k × Out) → Option Out
  | [] => none
  | (s, out) :: rest => if salt = s then some out else lookup salt rest

/-- The stored-table online algorithm explicitly has budget zero. -/
def tableOnline {k : Nat} {Out X Y : Type} (table : List (Fin k × Out)) (salt : Fin k) :
    Program X Y (Option Out) 0 := .done (lookup salt table)

theorem tableOnline_run {k : Nat} {Out X Y : Type} (H : X → Y)
    (table : List (Fin k × Out)) (salt : Fin k) :
    (tableOnline table salt).run H = (lookup salt table, 0) := by
  unfold tableOnline Program.run
  rfl

def tableWin {k : Nat} {Out : Type} (check : Fin k → Out → Bool)
    (table : List (Fin k × Out)) (salt : Fin k) : Nat :=
  match lookup salt table with
  | none => 0
  | some out => if check salt out then 1 else 0

theorem tableWin_cons_le {k : Nat} {Out : Type} (check : Fin k → Out → Bool)
    (s : Fin k) (out : Out) (rest : List (Fin k × Out)) (salt : Fin k) :
    tableWin check ((s, out) :: rest) salt ≤
      (if salt = s then 1 else 0) + tableWin check rest salt := by
  by_cases h : salt = s
  · simp only [tableWin, lookup, h, ↓reduceIte]
    split <;> omega
  · simp [tableWin, lookup, h]

/-- For every fixed oracle-dependent table, at most its length of the fresh salts win.
No independence of table contents from the oracle is required. -/
theorem freshSalt_table_bound {k : Nat} {Out : Type} (check : Fin k → Out → Bool)
    (table : List (Fin k × Out)) : qsum k (tableWin check table) ≤ table.length := by
  induction table with
  | nil =>
    change qsum k (fun _ => 0) ≤ 0
    rw [qsum_const, Nat.mul_zero]
    exact Nat.le_refl 0
  | cons entry rest ih =>
    have h := qsum_le_qsum (tableWin_cons_le check entry.1 entry.2 rest)
    rw [qsum_add, qsum_ite_eq] at h
    exact Nat.le_trans h (by simp only [List.length_cons]; omega)

/-- Averaging the pointwise salt bound over the actual uniform oracle enumeration.
For positive k this is probability ≤ entries/k, even with unbounded preprocessing. -/
theorem freshSalt_preprocessed_table_bound {n w k : Nat} {Out : Type}
    (preprocess : (Fin n → BitVec w) → List (Fin k × Out))
    (check : (Fin n → BitVec w) → Fin k → Out → Bool) (entries : Nat)
    (capacity : ∀ H, (preprocess H).length ≤ entries) :
    uniformOracleSum w n (fun H => qsum k (tableWin (check H) (preprocess H))) ≤
      (2 ^ w) ^ n * entries := by
  rw [← uniformOracleSum_const w n entries]
  exact uniformOracleSum_le w n _ _ fun H =>
    Nat.le_trans (freshSalt_table_bound (check H) (preprocess H)) (capacity H)


end Qsag.PreprocessingGame


namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 512

def publicSpnPack (x : PublicSpnState) : BitVec 256 := x.2 ++ x.1

def publicSpnUnpack (x : BitVec 256) : PublicSpnState :=
  (x.extractLsb' 0 128, x.extractLsb' 128 128)

theorem publicSpnUnpack_pack (x : PublicSpnState) :
    publicSpnUnpack (publicSpnPack x) = x := by
  simp only [publicSpnUnpack, publicSpnPack, BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_append_eq_left]

theorem publicSpnPack_unpack (x : BitVec 256) :
    publicSpnPack (publicSpnUnpack x) = x := by
  exact BitVec.extractLsb'_append_extractLsb'

def publicSpnQueryCode (direction : PublicPermutationDirection) (x : PublicSpnState) :
    Fin (2 ^ 257) :=
  ((match direction with | .forward => 0#1 | .inverse => 1#1) ++ publicSpnPack x).toFin

def publicSpnQueryDecode (code : Fin (2 ^ 257)) : PublicPermutationDirection × PublicSpnState :=
  let word := BitVec.ofFin code
  (if word.extractLsb' 256 1 = 0#1 then .forward else .inverse,
    publicSpnUnpack (word.extractLsb' 0 256))

theorem publicSpnQueryDecode_code (direction : PublicPermutationDirection) (x : PublicSpnState) :
    publicSpnQueryDecode (publicSpnQueryCode direction x) = (direction, x) := by
  have h : (1#1 : BitVec 1) ≠ 0#1 := by decide
  cases direction <;>
    simp only [publicSpnQueryDecode, publicSpnQueryCode, BitVec.ofFin_toFin,
      BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
      publicSpnUnpack_pack, h, ↓reduceIte]

/-- Both operations exposed as one bitstring oracle table. -/
def publicSpnOracleTable (p : PublicPermutation PublicSpnState)
    (code : Fin (2 ^ 257)) : BitVec 256 :=
  let query := publicSpnQueryDecode code
  publicSpnPack (publicPermutationQuery p query.1 query.2)

theorem publicSpnOracleTable_code (p : PublicPermutation PublicSpnState)
    (direction : PublicPermutationDirection) (x : PublicSpnState) :
    publicSpnOracleTable p (publicSpnQueryCode direction x) =
      publicSpnPack (publicPermutationQuery p direction x) := by
  unfold publicSpnOracleTable
  rw [publicSpnQueryDecode_code]

/-- Coherent XOR query, including a coherent direction register. -/
def publicSpnCoherentQuery {anc : Nat} (p : PublicPermutation PublicSpnState)
    (state : QVec (2 ^ 257) 256 anc) : QVec (2 ^ 257) 256 anc :=
  oracleXor (publicSpnOracleTable p) state

theorem publicSpnCoherentQuery_involutive {anc : Nat} (p : PublicPermutation PublicSpnState)
    (state : QVec (2 ^ 257) 256 anc) :
    publicSpnCoherentQuery p (publicSpnCoherentQuery p state) = state :=
  oracleXor_involutive (publicSpnOracleTable p) state

theorem publicSpnCoherentQuery_isometry {anc : Nat} (p : PublicPermutation PublicSpnState)
    (state : QVec (2 ^ 257) 256 anc) :
    QVec.stateNormSq (publicSpnCoherentQuery p state) = QVec.stateNormSq state :=
  oracleXor_isometry (publicSpnOracleTable p) state

/-- The target is given before the online run. This family is fixed before sampling p;
there is no extra oracle-correlated advice parameter. `q` counts forward/inverse
primitive calls together; a superposition of directions costs one call. -/
abbrev PublicSpnPreimageAdversary (anc q : Nat) :=
  PublicSpnState → QuantumAdv (2 ^ 257) 256 anc q

/-- Fresh-image challenge: sample x, compute target=P(x) XOR x, then run the adversary
on target with BOTH primitive directions. One sampler forward call is additional to q.
The final target register is measured as the proposed preimage; the input and ancilla
registers are ignored. The verifier makes one further forward call. -/
def publicSpnPreimageFinalState {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) :
    QVec (2 ^ 257) 256 anc :=
  runQuantumAdv (adversary (publicSpnFeedForward p challenge)) (publicSpnOracleTable p)

/-- Unnormalized Born mass of the actual feed-forward preimage relation. -/
def publicSpnPreimageMass {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) : Nat :=
  let state := publicSpnPreimageFinalState p adversary challenge
  qsum (2 ^ 257) (fun input => qsum (2 ^ 256) (fun output => qsum anc (fun auxiliary =>
    if publicSpnFeedForward p (publicSpnUnpack (BitVec.ofFin output)) =
        publicSpnFeedForward p challenge
    then GaussInt.normSq (state input output auxiliary) else 0)))

def publicSpnPreimageProbability {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) : RatBound where
  num := publicSpnPreimageMass p adversary challenge
  den := QVec.stateNormSq (publicSpnPreimageFinalState p adversary challenge)
  h_pos := runQuantumAdv_normSq_pos _ _

/-- Uniform fresh 256-bit input challenge, sampled after the public primitive.
Normalization is performed per challenge before averaging, since target-dependent
scaled circuits may have different squared norms. -/
def publicSpnFreshPreimageProbability {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) : RatBound :=
  RatBound.mul (RatBound.invPow2 256) (RatBound.sumList (List.ofFn
    (fun challenge : Fin (2 ^ 256) => publicSpnPreimageProbability p adversary
      (publicSpnUnpack (BitVec.ofFin challenge)))))

/-- Exact experiment for a finite primitive ensemble: select an entry uniformly,
then a fresh uniform input, then run the fixed adversary family. The same adversary
is used for every primitive. Repeated entries carry repeated probability weight.
This does NOT assert the supplied ensemble is uniform over all permutations; such
an ideal sampler and its uniformity certificate remain separate work. -/
def publicSpnEnsemblePreimageProbability {anc q : Nat}
    (primitives : List (PublicPermutation PublicSpnState)) (nonempty : 0 < primitives.length)
    (adversary : PublicSpnPreimageAdversary anc q) : RatBound :=
  RatBound.mul ⟨1, primitives.length, nonempty⟩
    (RatBound.sumList (primitives.map (fun p => publicSpnFreshPreimageProbability p adversary)))

/-- The game probability is normalized even when the adversary uses scaled unitaries. -/
theorem publicSpnPreimageMass_le_norm {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) :
    publicSpnPreimageMass p adversary challenge ≤
      QVec.stateNormSq (publicSpnPreimageFinalState p adversary challenge) := by
  unfold publicSpnPreimageMass QVec.stateNormSq QVec.queryWeight
  apply qsum_le_qsum
  intro input
  apply qsum_le_qsum
  intro output
  apply qsum_le_qsum
  intro auxiliary
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

theorem publicSpnPreimageProbability_le_one {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) :
    RatBound.le (publicSpnPreimageProbability p adversary challenge) RatBound.one := by
  simpa only [RatBound.le, publicSpnPreimageProbability, RatBound.one_num, RatBound.one_den,
    Nat.mul_one, Nat.one_mul] using publicSpnPreimageMass_le_norm p adversary challenge

/-- Concrete single-address experiment. Public address parameters are given to the
adversary before its online run; the function family and code may depend on them.
This does not model extra queries to OTHER chain addresses or a full signature game. -/
def publicChainPreimageProbability {anc q : Nat}
    (hash32 : List UInt8 → List (List UInt8) → List UInt8) (address : PublicChainAddress)
    (adversary : PublicChainAddress → PublicSpnPreimageAdversary anc q) : RatBound :=
  publicSpnFreshPreimageProbability (publicChainPermutation hash32 address) (adversary address)

end Qsag
