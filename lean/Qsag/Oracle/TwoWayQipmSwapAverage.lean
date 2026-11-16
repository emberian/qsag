module
/-
# Qsag.Oracle.TwoWayQipmSwapAverage — averaged two-way transposition O2H bound `8 q² / n`

For a `q`-query quantum adversary with superposition access to `π` and `π⁻¹` on `n` points,
the squared state disturbance caused by composing `π` with a transposition `(a b)`, averaged over
all `n²` pairs `(a, b)`, is at most `8 q² / n` of the squared norm. A uniformly random
transposition of a two-way permutation oracle is therefore undetectable below `√n` queries.
This is a hybrid lemma, not a CICO or collision bound.

-/
public import Qsag.Oracle.TwoWayQipmCompression

public section
namespace Qsag
set_option autoImplicit false

/-- A sum over `Fin (n + m)` splits into the first `m` and the last `n` indices. -/
theorem qipm_qsum_split (n : Nat) : ∀ (m : Nat) (f : Fin (n + m) → Nat),
    qsum (n + m) f =
      qsum m (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_left m n)⟩) +
        qsum n (fun j => f ⟨m + j.val, by have := j.isLt; omega⟩)
  | 0, f => by
    rw [qsum_zero, Nat.zero_add]
    apply qsum_congr
    intro j
    exact congrArg f (Fin.ext (Nat.zero_add j.val).symm)
  | m + 1, f => by
    have ih := qipm_qsum_split n m (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    have hB : qsum n (fun j => f ⟨m + 1 + j.val, by have := j.isLt; omega⟩) =
        qsum n (fun j => f ⟨m + j.val + 1, by have := j.isLt; omega⟩) := by
      apply qsum_congr
      intro j
      exact congrArg f (Fin.ext (by show m + 1 + j.val = m + j.val + 1; omega))
    refine Eq.trans (qsum_succ (n + m) f) (Eq.trans ?_
      (congrArg (· + qsum n (fun j => f ⟨m + 1 + j.val, by have := j.isLt; omega⟩))
        (qsum_succ m _).symm))
    show f ⟨0, _⟩ + qsum (n + m) (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
      (f ⟨0, _⟩ + qsum m (fun i => f ⟨i.1 + 1, _⟩)) +
        qsum n (fun j => f ⟨m + 1 + j.val, _⟩)
    rw [ih, hB, Nat.add_assoc]

private theorem qipm_one_of_four_le (w A B C D : Nat) (h : A = w ∨ B = w ∨ C = w ∨ D = w) :
    w ≤ A + B + C + D := by
  rcases h with h | h | h | h <;> omega

/-- The marked query mass is at most the weight on the four touched points. -/
theorem qipm_swap_mark_mass_le {n w cardAnc : Nat} (π : Fin n → Fin n) (a b : Fin n)
    (ψ : QVec (n + n) w cardAnc) :
    QVec.queryMassOn (qipmSwapMark π a b) ψ ≤
      QVec.queryWeight ψ (qipmFwdIdx a) + QVec.queryWeight ψ (qipmFwdIdx b) +
        QVec.queryWeight ψ (qipmInvIdx (π a)) + QVec.queryWeight ψ (qipmInvIdx (π b)) := by
  rw [QVec.queryMassOn_def]
  have hpt : ∀ i : Fin (n + n),
      (if qipmSwapMark π a b i = true then QVec.queryWeight ψ i else 0) ≤
        (if i = qipmFwdIdx a then QVec.queryWeight ψ (qipmFwdIdx a) else 0) +
        (if i = qipmFwdIdx b then QVec.queryWeight ψ (qipmFwdIdx b) else 0) +
        (if i = qipmInvIdx (π a) then QVec.queryWeight ψ (qipmInvIdx (π a)) else 0) +
        (if i = qipmInvIdx (π b) then QVec.queryWeight ψ (qipmInvIdx (π b)) else 0) := by
    intro i
    cases hm : qipmSwapMark π a b i
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
    · simp only [↓reduceIte]
      apply qipm_one_of_four_le
      rcases qipmSwapMark_cases π a b i hm with e | e | e | e
      · exact Or.inl (by rw [e]; simp only [↓reduceIte])
      · exact Or.inr (Or.inl (by rw [e]; simp only [↓reduceIte]))
      · exact Or.inr (Or.inr (Or.inl (by rw [e]; simp only [↓reduceIte])))
      · exact Or.inr (Or.inr (Or.inr (by rw [e]; simp only [↓reduceIte])))
  refine Nat.le_trans (qsum_le_qsum hpt) ?_
  rw [qsum_add, qsum_add, qsum_add, qsum_ite_eq, qsum_ite_eq, qsum_ite_eq, qsum_ite_eq]
  exact Nat.le_refl _

/-- Summed over all transpositions, the marked mass is at most `2 n` times the squared norm. -/
theorem qipm_swap_mark_mass_sum {n w cardAnc : Nat} (π ρ : Fin n → Fin n)
    (hL : ∀ x, ρ (π x) = x) (hR : ∀ y, π (ρ y) = y) (ψ : QVec (n + n) w cardAnc) :
    qsum n (fun a => qsum n (fun b => QVec.queryMassOn (qipmSwapMark π a b) ψ)) ≤
      2 * n * QVec.stateNormSq ψ := by
  have hbij : qsum n (fun b => QVec.queryWeight ψ (qipmInvIdx (π b))) =
      qsum n (fun y => QVec.queryWeight ψ (qipmInvIdx y)) :=
    qsum_bijection π ρ hL hR (fun y => QVec.queryWeight ψ (qipmInvIdx y))
  have hsplit : QVec.stateNormSq ψ =
      qsum n (fun a => QVec.queryWeight ψ (qipmFwdIdx a)) +
        qsum n (fun y => QVec.queryWeight ψ (qipmInvIdx y)) := by
    rw [QVec.stateNormSq_def]
    exact qipm_qsum_split n n (fun i => QVec.queryWeight ψ i)
  have hin : ∀ a : Fin n, qsum n (fun b => QVec.queryMassOn (qipmSwapMark π a b) ψ) ≤
      n * QVec.queryWeight ψ (qipmFwdIdx a) +
        qsum n (fun b => QVec.queryWeight ψ (qipmFwdIdx b)) +
        n * QVec.queryWeight ψ (qipmInvIdx (π a)) +
        qsum n (fun y => QVec.queryWeight ψ (qipmInvIdx y)) := by
    intro a
    refine Nat.le_trans (qsum_le_qsum (fun b => qipm_swap_mark_mass_le π a b ψ)) ?_
    rw [qsum_add, qsum_add, qsum_add, qsum_const, qsum_const, hbij]
    exact Nat.le_refl _
  refine Nat.le_trans (qsum_le_qsum hin) ?_
  rw [qsum_add, qsum_add, qsum_add, qsum_mul_left, qsum_const, qsum_mul_left, qsum_const, hbij,
    hsplit, Nat.mul_assoc, Nat.mul_add]
  omega

private theorem qipm_qsum_triple (n q : Nat) (s : Fin q → Nat)
    (m : Fin q → Fin n → Fin n → Nat) :
    qsum n (fun a => qsum n (fun b => qsum q (fun t => s t * m t a b))) =
      qsum q (fun t => s t * qsum n (fun a => qsum n (fun b => m t a b))) := by
  have e1 : ∀ a : Fin n, qsum n (fun b => qsum q (fun t => s t * m t a b)) =
      qsum q (fun t => s t * qsum n (fun b => m t a b)) := by
    intro a
    rw [qsum_comm]
    apply qsum_congr
    intro t
    rw [qsum_mul_left]
  rw [qsum_congr e1, qsum_comm]
  apply qsum_congr
  intro t
  rw [qsum_mul_left]

private theorem qipm_suffix_mul_state_norm {cardX w cardAnc q : Nat}
    (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w) (t : Nat) (ht : t ≤ q) :
    suffixScale A t ht * QVec.stateNormSq (advStateAt A H t ht) =
      QVec.stateNormSq (runQuantumAdv A H) := by
  rw [advStateAt_normSq, runQuantumAdv_normSq, ← Nat.mul_assoc,
    Nat.mul_comm (suffixScale A t ht), prefix_mul_suffix_eq_total]

/-- **Averaged two-way transposition O2H.** Summed over all `n²` pairs `(a, b)`, the squared
    disturbance of replacing `π` by `π ∘ (a b)` is at most `8 q² n ‖ψ_final‖²`; the average over
    the pairs is at most `8 q² / n` of the squared norm. -/
theorem qipm_two_way_swap_average_o2h {n w cardAnc q : Nat}
    (A : QuantumAdv (n + n) w cardAnc q) (π ρ : Fin n → Fin n)
    (hL : ∀ x, ρ (π x) = x) (hR : ∀ y, π (ρ y) = y) (enc : Fin n → BitVec w) :
    qsum n (fun a => qsum n (fun b =>
        QVec.stateNormSq
          ((runQuantumAdv A (qipmPermOracle (fun x => π (qipmFinSwap a b x))
            (fun y => qipmFinSwap a b (ρ y)) enc)).sub
            (runQuantumAdv A (qipmPermOracle π ρ enc))))) ≤
      8 * q ^ 2 * n * QVec.stateNormSq (runQuantumAdv A (qipmPermOracle π ρ enc)) := by
  have h1 : ∀ a b : Fin n,
      QVec.stateNormSq
          ((runQuantumAdv A (qipmPermOracle (fun x => π (qipmFinSwap a b x))
            (fun y => qipmFinSwap a b (ρ y)) enc)).sub
            (runQuantumAdv A (qipmPermOracle π ρ enc))) ≤
        4 * q * qsum q (fun t =>
          suffixScale A t.1 (Nat.le_of_lt t.2) *
            QVec.queryMassOn (qipmSwapMark π a b)
              (advStateAt A (qipmPermOracle π ρ enc) t.1 (Nat.le_of_lt t.2))) :=
    fun a b => qipm_two_way_swap_o2h A π ρ hR enc a b
  refine Nat.le_trans (qsum_le_qsum (fun a => qsum_le_qsum (fun b => h1 a b))) ?_
  have e2 : ∀ a : Fin n, qsum n (fun b => 4 * q * qsum q (fun t =>
      suffixScale A t.1 (Nat.le_of_lt t.2) *
        QVec.queryMassOn (qipmSwapMark π a b)
          (advStateAt A (qipmPermOracle π ρ enc) t.1 (Nat.le_of_lt t.2)))) =
      4 * q * qsum n (fun b => qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn (qipmSwapMark π a b)
            (advStateAt A (qipmPermOracle π ρ enc) t.1 (Nat.le_of_lt t.2)))) :=
    fun a => qsum_mul_left (4 * q) _
  rw [qsum_congr e2, qsum_mul_left,
    qipm_qsum_triple n q (fun t => suffixScale A t.1 (Nat.le_of_lt t.2))
      (fun t a b => QVec.queryMassOn (qipmSwapMark π a b)
        (advStateAt A (qipmPermOracle π ρ enc) t.1 (Nat.le_of_lt t.2)))]
  have h3 : ∀ t : Fin q, suffixScale A t.1 (Nat.le_of_lt t.2) *
      qsum n (fun a => qsum n (fun b => QVec.queryMassOn (qipmSwapMark π a b)
        (advStateAt A (qipmPermOracle π ρ enc) t.1 (Nat.le_of_lt t.2)))) ≤
      2 * n * QVec.stateNormSq (runQuantumAdv A (qipmPermOracle π ρ enc)) := by
    intro t
    refine Nat.le_trans (Nat.mul_le_mul_left _ (qipm_swap_mark_mass_sum π ρ hL hR _)) ?_
    rw [Nat.mul_left_comm, qipm_suffix_mul_state_norm]
    exact Nat.le_refl _
  refine Nat.le_trans (Nat.mul_le_mul_left _ (qsum_le_qsum h3)) ?_
  rw [qsum_const, Nat.pow_two]
  generalize QVec.stateNormSq (runQuantumAdv A (qipmPermOracle π ρ enc)) = N
  have e : 4 * q * (q * (2 * n * N)) = 8 * (q * q) * n * N := by
    rw [Nat.mul_assoc 2 n N, Nat.mul_left_comm q 2 (n * N), Nat.mul_assoc 4 q,
      Nat.mul_left_comm q 2, Nat.mul_assoc (8 * (q * q)) n N, Nat.mul_assoc 8 (q * q),
      Nat.mul_assoc q q, ← Nat.mul_assoc 4 2]
  exact Nat.le_of_eq e

#verify_constructive
  Qsag.qipm_qsum_split
  Qsag.qipm_swap_mark_mass_le
  Qsag.qipm_swap_mark_mass_sum
  Qsag.qipm_two_way_swap_average_o2h
end Qsag
end
