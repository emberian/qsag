module
/-
# The measured-query experiment: explicit observation semantics and lazy sampling

`measuredStateAt A H t xs` is the unnormalized state of adversary `A` after `t` oracle calls
in which every query address was projectively measured immediately after the oracle acted,
with outcomes `xs` (most recent first). The branch weights are Born masses of that
instrument. Nothing here is assumed about an event cover.

Results, all for this measured experiment and a uniformly random oracle:

* the branch state depends on the oracle only at the measured addresses;
* the branches conserve the adversary's oracle-independent total mass;
* an oracle answer at an unmeasured address lands in a list of `K` reprogramming-local
  targets with mass at most `K / 2^w` of the total (no query-count loss);
* two distinct measured addresses share an answer with mass at most
  `(0 + 1 + ... + (t-1)) / 2^w` of the total.

Scope. A coherent adversary is not this experiment: `measured_parity_execution` evaluates
both on the same one-query circuit and obtains different output masses. The bounds below
therefore cover adversaries whose queries are observed (classical-query adversaries with
quantum local computation), and do not bound arbitrary coherent-query adversaries.
-/

public import Qsag.QromMerkleOnlineExtraction
public import Qsag.QromExtractionBoundary
import all Qsag.QromMerkleOnlineExtraction
import all Qsag.QromExtractionBoundary
import all Qsag.MultiRoundFsQrom
import all Qsag.ConcreteSecurityBudget

public section
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

/-! ## Executed example: the experiment is not the coherent run -/

/-- On the one-query parity circuit of `QromExtractionBoundary`, the coherent run puts mass
    8 of 8 on output one, while the measured experiment puts 4 of 8 there (two branches of
    mass 4 each). The bounds in this module are statements about the second number. -/
theorem measured_parity_execution :
    QVec.queryMassOn (fun x : Fin 2 => decide (x.val = 1))
      (runQuantumAdv qromParityAdv qromParityOracle) = 8 ∧
    sumLogs 2 1 (fun xs => QVec.queryMassOn (fun x : Fin 2 => decide (x.val = 1))
      (measuredStateAt qromParityAdv qromParityOracle 1 (Nat.le_refl 1) xs)) = 4 ∧
    sumLogs 2 1 (fun xs => QVec.stateNormSq
      (measuredStateAt qromParityAdv qromParityOracle 1 (Nat.le_refl 1) xs)) = 8 := by
  decide

#verify_constructive
  Qsag.uniform_fresh_point_bound
  Qsag.measuredStateAt_congr
  Qsag.measuredStateAt_total_mass
  Qsag.measured_fresh_target_hit_bound
  Qsag.freshCollision_of_distinct_equal
  Qsag.measured_record_collision_bound
  Qsag.measured_parity_execution

end Qsag
end
