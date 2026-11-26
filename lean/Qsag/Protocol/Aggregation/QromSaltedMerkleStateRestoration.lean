module
/-
# Salted Merkle Compressed-Oracle Sparsity, State-Restoration Games & Joint-PoW QROM BCS Soundness

Mechanized constructive reductions connecting:
1. **Salted Merkle Layouts & Coherent Fourier Compressed-Oracle Sparsity (`§1`)**:
   - `SaltedCanopyLayout`: explicit per-tree salt separation over `MerkleAddressLayout`, proving
     cross-salt address disjointness (`saltedCanopy_cross_salt_disjoint`) and fresh-salt
     preprocessing resistance (`saltedCanopy_fresh_salt_preprocessed_bound`), contrasted with the
     zero-online-query unsalted preprocessing collision (`tooth_unsalted_canopy_preprocessed_collision`).
   - Domain-tagged Fourier database weight conservation (`domainTableWeight_sum_eq_tableWeight`)
     over `OracleBitTable` and `fourierAdvStateAt`, establishing that any coherent `Q`-query
     `QuantumAdv` has zero amplitude on database labels whose summed active queries across
     disjoint salts/domains exceed `Q` (`coherent_salted_domain_budget_zero_of_overflow`), while
     preserving observable expectations (`fourierAdv_event_eq`).
2. **Adaptive State-Restoration Games & Coherent Joint `(PoW × Challenge)` QROM Reduction (`§2`)**:
   - `StateRestorationTree`: adaptive `T`-move classical state-restoration game (`[BCS16; CY24]`),
     proving by structural induction that escape probability across `(cardChal)^T` challenge tapes
     is bounded by `(T * badPerRound) / cardChal` (`classical_state_restoration_soundness`),
     certifying the proved `184`-bit `slicedBinaryStageBound` up to `T ≤ 2^55` classical queries
     (`classical_sr_sliced184_sound_at_2pow55`).
   - `QromJointPowRbrSpec`: coherent `QuantumAdv` reduction over `BitVec (bPow + wChal)` proving
     from product-slice cardinality (`jointPowChal_badCard_le`) and `qrom_uniform_oracle_success_bound`
     that absorbing the grinding nonce before squeezing challenges reduces `Q`-query quantum
     escape mass by `powGoodCard / 2^bPow` (`qrom_joint_pow_multiRound_success_bound`), contrasted
     with post-squeeze PoW (`tooth_post_squeeze_pow_forfeits_reduction`).
   - End-to-end composition (`measured_hem_qrom_bcs_end_to_end_bound`) over `verifyHemOpeningBatch`
     combining `measured_hem_acceptance_from_extracted` (`verifyHemAffineWhir` on
     `extractedOpeningValues`) with extracted-transcript round covering.
3. **`[CDHZ25]` Post-Quantum State-Restoration + Multi-Extractable Salted Merkle Accounting (`§3`)**:
   - Exact rational formalization of `[CDHZ25, ePrint 2025/2166]` Theorem 6.9 (`cdhzPqsrBound`),
     Theorem 8.3 (`cdhzSaltedMerkleOfflineBound`, `cdhzSaltedMerkleOnlineBound`,
     `cdhzSaltedMerkleComBound`), and Theorem A.1 / 11.3 (`cdhzSnargEnvelopeBound`), together with
     a `#tooth` refutation (`tooth_linear_sr_query_schedule_unsound_in_qrom`) proving that a
     schedule sized under linear `(T + k) * ε` passes classical SR at `2^40` queries yet fails
     128-bit QROM soundness due to quadratic Grover salt/nonce search.
4. **Proved Cheaper `Hem` WHIR Schedules Across `nv ∈ 2..=24` (`§4`)**:
   - Universal 49-row Johnson witness table (`hemOptimizedQromWitnessTable`, identical to
     `hemJohnsonQromWitnessTable` on all `nv ∈ 18..=24`) certifying four concrete QROM schedules:
     * `unitaryPow16`: `q = (200, 101, 69, 52)` + 16-bit PoW (`422` vs `542` openings, `-22.1%`) at `Q + 1 ≤ 2^40`;
     * `cdhzPow16At2pow38`: `q = (202, 102, 70, 52)` + 16-bit PoW (`426` openings) at `Q ≤ 2^38` under `[CDHZ25]` raw constants;
     * `cdhz320Pow16At2pow40`: `q = (206, 104, 71, 53)` + 16-bit PoW (`434` openings) at `Q + 1 ≤ 2^40`;
     * `unitaryZeroPow`: `q = (216, 109, 74, 56)` + 0-bit PoW (`455` openings, zero PoW grinding) at `Q + 1 ≤ 2^40`.
-/
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Tactic.AssuranceKit
import Qsag.Coding.Cwyz26
import Qsag.Protocol.Aggregation.HemRbrSoundness
import Qsag.Protocol.Aggregation.MultiRoundFsQrom
import Qsag.Protocol.Aggregation.ConcreteSecurityBudget

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 8192

/-! ## §1. Salted Merkle Layouts & Coherent Compressed-Oracle Query-Partition Sparsity -/

/-- Salted Merkle compression layout parameterizing `MerkleAddressLayout` by an explicit tree salt
    `Fin cardSalt`, modeling per-commitment Canopy salt domain separation. -/
structure SaltedCanopyLayout (cardSalt cardX w : Nat) where
  encode : Fin cardSalt → Nat → Nat → BitVec w → BitVec w → Fin cardX
  decode : Fin cardX → Option (Fin cardSalt × Nat × Nat × BitVec w × BitVec w)
  levels : Nat
  nodes : Nat
  decode_sound : ∀ x s l n u v, decode x = some (s, l, n, u, v) → encode s l n u v = x
  decode_encode : ∀ s l n u v, l < levels → n < nodes →
    decode (encode s l n u v) = some (s, l, n, u, v)

/-- Project a `SaltedCanopyLayout` onto the `MerkleAddressLayout` of a single tree salt `s`. -/
def SaltedCanopyLayout.atSalt {cardSalt cardX w : Nat}
    (L : SaltedCanopyLayout cardSalt cardX w) (s : Fin cardSalt) : MerkleAddressLayout cardX w where
  encode := L.encode s
  decode := fun x =>
    match L.decode x with
    | some (s', l, n, u, v) => if s' = s then some (l, n, u, v) else none
    | none => none
  levels := L.levels
  nodes := L.nodes
  decode_sound := by
    intro x l n u v hDec
    cases hd : L.decode x with
    | none => rw [hd] at hDec; cases hDec
    | some tup =>
      obtain ⟨s', l', n', u', v'⟩ := tup
      rw [hd] at hDec
      by_cases hs : s' = s
      · simp only [hs, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hDec
        rcases hDec with ⟨rfl, rfl, rfl, rfl⟩
        exact hs ▸ L.decode_sound x s' l' n' u' v' hd
      · simp only [hs, ↓reduceIte] at hDec; cases hDec
  decode_encode := by
    intro l n u v hl hn
    simp only [L.decode_encode s l n u v hl hn, ↓reduceIte]

/-- Distinct tree salts occupy strictly disjoint compression addresses inside the tweak range. -/
theorem saltedCanopy_cross_salt_disjoint {cardSalt cardX w : Nat}
    (L : SaltedCanopyLayout cardSalt cardX w)
    {s₁ s₂ : Fin cardSalt} (hNe : s₁ ≠ s₂)
    (l₁ n₁ l₂ n₂ : Nat) (u₁ v₁ u₂ v₂ : BitVec w)
    (hl₁ : l₁ < L.levels) (hn₁ : n₁ < L.nodes)
    (hl₂ : l₂ < L.levels) (hn₂ : n₂ < L.nodes) :
    L.encode s₁ l₁ n₁ u₁ v₁ ≠ L.encode s₂ l₂ n₂ u₂ v₂ := by
  intro hEq
  have hd₁ := L.decode_encode s₁ l₁ n₁ u₁ v₁ hl₁ hn₁
  have hd₂ := L.decode_encode s₂ l₂ n₂ u₂ v₂ hl₂ hn₂
  rw [hEq, hd₂] at hd₁
  exact hNe (congrArg Prod.fst (Option.some.inj hd₁)).symm

/-- Fresh uniform tree salt bounds any `entries`-row oracle-dependent preprocessing collision table
    to success rate `≤ entries / cardSalt` (`(2^w)^cardX * entries` out of `(2^w)^cardX * cardSalt`). -/
theorem saltedCanopy_fresh_salt_preprocessed_bound {cardSalt cardX w : Nat}
    (L : SaltedCanopyLayout cardSalt cardX w) (lvl node : Nat)
    (preprocess : (Fin cardX → BitVec w) →
      List (Fin cardSalt × ((BitVec w × BitVec w) × (BitVec w × BitVec w))))
    (entries : Nat) (hCap : ∀ H, (preprocess H).length ≤ entries) :
    uniformOracleSum w cardX (fun H => qsum cardSalt
      (PreprocessingGame.tableWin (fun s pair =>
        decide (pair.1 ≠ pair.2 ∧
          (L.atSalt s).hash H lvl node pair.1.1 pair.1.2 =
          (L.atSalt s).hash H lvl node pair.2.1 pair.2.2)) (preprocess H))) ≤
      (2 ^ w) ^ cardX * entries :=
  PreprocessingGame.freshSalt_preprocessed_table_bound preprocess _ entries hCap

/-- Count of active Fourier truth-table coordinates in `d : OracleBitTable n` belonging to
    domain/salt `dom : Fin cardDom` under classifier `domainOf : Fin n → Fin cardDom`. -/
def domainTableWeight : (n : Nat) → {cardDom : Nat} →
    (Fin n → Fin cardDom) → Fin cardDom → OracleBitTable n → Nat
  | 0, _, _, _, _ => 0
  | n + 1, _, domainOf, dom, (b, rest) =>
    (if b && decide (domainOf ⟨0, Nat.zero_lt_succ n⟩ = dom) then 1 else 0) +
      domainTableWeight n (fun i => domainOf i.succ) dom rest

/-- Every single domain's active Fourier query weight is bounded by total `tableWeight`. -/
theorem domainTableWeight_le_tableWeight :
    ∀ (n : Nat) {cardDom : Nat} (domainOf : Fin n → Fin cardDom)
      (dom : Fin cardDom) (d : OracleBitTable n),
      domainTableWeight n domainOf dom d ≤ tableWeight n d
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, _, domainOf, dom, (b, rest) => by
    have ih := domainTableWeight_le_tableWeight n (fun i => domainOf i.succ) dom rest
    simp only [domainTableWeight, tableWeight_succ]
    cases b <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    · omega
    · split <;> omega

/-- **Exact Compressed-Oracle Query-Partition Conservation (`domainTableWeight_sum_eq_tableWeight`)**:
    Summing active Fourier coordinates across all disjoint domain/salt tags `dom : Fin cardDom`
    equals `tableWeight n d` identically. This is the exact Fourier-basis mechanism behind
    `[CDHZ25]` Theorem A.1's `w_FS + w_VC + w_ME ≤ Q` query-budget conservation. -/
theorem domainTableWeight_sum_eq_tableWeight :
    ∀ (n : Nat) {cardDom : Nat} (domainOf : Fin n → Fin cardDom) (d : OracleBitTable n),
      qsum cardDom (fun dom => domainTableWeight n domainOf dom d) = tableWeight n d
  | 0, _, _, _ => by
    simp only [domainTableWeight, tableWeight_zero, qsum_const, Nat.mul_zero]
  | n + 1, cardDom, domainOf, (b, rest) => by
    simp only [domainTableWeight, tableWeight_succ, qsum_add]
    rw [domainTableWeight_sum_eq_tableWeight n (fun i => domainOf i.succ) rest]
    congr 1
    cases b
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]
    · simp only [Bool.true_and, ↓reduceIte]
      have hInd := qsum_ite_eq cardDom (domainOf ⟨0, Nat.zero_lt_succ n⟩) 1
      have hCongr : qsum cardDom (fun dom =>
          if decide (domainOf ⟨0, Nat.zero_lt_succ n⟩ = dom) = true then 1 else 0) =
        qsum cardDom (fun dom =>
          if dom = domainOf ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) := by
        apply qsum_congr; intro dom
        by_cases he : dom = domainOf ⟨0, Nat.zero_lt_succ n⟩
        · subst he; simp
        · have he' : domainOf ⟨0, Nat.zero_lt_succ n⟩ ≠ dom := fun h => he h.symm
          simp only [he, he', decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [hCongr, hInd]

/-- **Coherent Multi-Salt / Multi-Domain Support Theorem (`coherent_salted_domain_budget_zero_of_overflow`)**:
    For ANY coherent `Q`-query `QuantumAdv n 1 cardAnc Q` (with arbitrary superposition queries
    and zero intermediate measurements), the Fourier database state `fourierAdvStateAt A t ht d`
    has **identically zero amplitude** whenever the summed active Fourier weights across all
    protocol domains/salts exceed `t`, while decoding recovers the exact coherent QROM acceptance
    probability (`fourierAdv_event_eq`). -/
theorem coherent_salted_domain_budget_zero_of_overflow
    {n cardDom cardAnc Q : Nat}
    (A : QuantumAdv n 1 cardAnc Q)
    (domainOf : Fin n → Fin cardDom)
    (t : Nat) (ht : t ≤ Q) (d : OracleBitTable n)
    (hOverflow : t < qsum cardDom (fun dom => domainTableWeight n domainOf dom d)) :
    fourierAdvStateAt A t ht d = QVec.zero n 1 cardAnc := by
  rw [domainTableWeight_sum_eq_tableWeight n domainOf d] at hOverflow
  exact fourier_runtime_support A t ht d hOverflow

/-- Exact coherent bridge combining zero multi-domain database overflow with observable equality. -/
theorem coherent_salted_oracle_execution_bridge
    {n cardDom cardAnc Q : Nat}
    (A : QuantumAdv n 1 cardAnc Q)
    (domainOf : Fin n → Fin cardDom)
    (event : (Fin n → BitVec 1) → Fin n → Bool) :
    coherentTableEventMass event (fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * Q + n) * uniformOracleSum 1 n
        (fun H => QVec.queryMassOn (event H) (runQuantumAdv A H)) ∧
    oracleTableSum n (fun d =>
      if Q < qsum cardDom (fun dom => domainTableWeight n domainOf dom d) then
        QVec.stateNormSq (fourierAdvStateAt A Q (Nat.le_refl Q) d)
      else 0) = 0 := by
  refine ⟨fourierAdv_event_eq A event, ?_⟩
  have hCongr : ∀ d : OracleBitTable n,
      (if Q < qsum cardDom (fun dom => domainTableWeight n domainOf dom d) then
        QVec.stateNormSq (fourierAdvStateAt A Q (Nat.le_refl Q) d) else 0) =
      (if Q < tableWeight n d then
        QVec.stateNormSq (fourierAdvStateAt A Q (Nat.le_refl Q) d) else 0) := by
    intro d
    rw [domainTableWeight_sum_eq_tableWeight n domainOf d]
  rw [oracleTableSum_congr n _ _ hCongr]
  exact fourier_database_overflow_mass_zero A


/-! ### §1.3 Full `2m`-Bit (`w = 256` `Digest256`) `⊥`-Labeled DFMS Compressed-Oracle Register,
    Online Extraction Disturbance & Authenticated `Hem` Bridge (`[DFMS22, Eq. (6)–(8)]`) -/

private theorem gaussZero_add_zero : GaussInt.zero.add GaussInt.zero = GaussInt.zero := by
  apply GaussInt.ext <;> simp [GaussInt.add_def, GaussInt.zero_def]

private theorem gaussZero_sub_zero : GaussInt.zero.sub GaussInt.zero = GaussInt.zero := by
  apply GaussInt.ext <;> simp [GaussInt.sub_def, GaussInt.zero_def]

private def intSum : (N : Nat) → (Fin N → Int) → Int
  | 0, _ => 0
  | N + 1, f => f ⟨0, Nat.zero_lt_succ N⟩ + intSum N (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

private theorem intSum_congr {N : Nat} {f g : Fin N → Int} (h : ∀ i, f i = g i) :
    intSum N f = intSum N g := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [intSum, h ⟨0, Nat.zero_lt_succ N⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

private theorem intSum_add : ∀ (N : Nat) (f g : Fin N → Int),
    intSum N (fun i => f i + g i) = intSum N f + intSum N g
  | 0, _, _ => rfl
  | N + 1, f, g => by
    simp only [intSum, intSum_add N]
    omega

private theorem intSum_sub : ∀ (N : Nat) (f g : Fin N → Int),
    intSum N (fun i => f i - g i) = intSum N f - intSum N g
  | 0, _, _ => rfl
  | N + 1, f, g => by
    simp only [intSum, intSum_sub N]
    omega

private theorem intSum_const : ∀ (N : Nat) (c : Int),
    intSum N (fun _ => c) = (N : Int) * c
  | 0, _ => by simp [intSum]
  | N + 1, c => by
    simp only [intSum, intSum_const N c]
    have h1 : ((N + 1 : Nat) : Int) = (N : Int) + 1 := by omega
    rw [h1, Int.add_mul, Int.one_mul]
    omega

private theorem intSum_mul_left : ∀ (N : Nat) (c : Int) (f : Fin N → Int),
    intSum N (fun i => c * f i) = c * intSum N f
  | 0, _, _ => by simp [intSum]
  | N + 1, c, f => by
    simp only [intSum, intSum_mul_left N c, Int.mul_add]

private theorem intSum_comm : ∀ (A B : Nat) (h : Fin A → Fin B → Int),
    intSum A (fun i => intSum B (fun j => h i j)) =
      intSum B (fun j => intSum A (fun i => h i j))
  | 0, B, _ => by
    simp only [intSum]
    exact (intSum_const B 0).trans (Int.mul_zero _) |>.symm
  | A + 1, B, h => by
    simp only [intSum, intSum_add]
    rw [intSum_comm A B (fun i j => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j)]

private theorem intSum_of_qsum : ∀ (N : Nat) (f : Fin N → Nat),
    intSum N (fun i => (f i : Int)) = (qsum N f : Int)
  | 0, _ => by rw [qsum_zero]; rfl
  | N + 1, f => by
    simp only [intSum, qsum_succ, intSum_of_qsum N]
    omega

private theorem gaussDoublePow_re : ∀ (k : Nat) (z : GaussInt),
    (gaussDoublePow k z).re = ((2 ^ k : Nat) : Int) * z.re
  | 0, z => by simp [gaussDoublePow_base]
  | k + 1, z => by
    simp only [gaussDoublePow_step, GaussInt.add_def, gaussDoublePow_re k z]
    have h2 : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) + ((2 ^ k : Nat) : Int) := by
      rw [Nat.pow_succ]; omega
    rw [h2, Int.add_mul]

private theorem gaussDoublePow_im : ∀ (k : Nat) (z : GaussInt),
    (gaussDoublePow k z).im = ((2 ^ k : Nat) : Int) * z.im
  | 0, z => by simp [gaussDoublePow_base]
  | k + 1, z => by
    simp only [gaussDoublePow_step, GaussInt.add_def, gaussDoublePow_im k z]
    have h2 : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) + ((2 ^ k : Nat) : Int) := by
      rw [Nat.pow_succ]; omega
    rw [h2, Int.add_mul]

private theorem gaussDoublePow_zero : ∀ (k : Nat), gaussDoublePow k GaussInt.zero = GaussInt.zero
  | 0 => gaussDoublePow_base _
  | k + 1 => by simp only [gaussDoublePow_step, gaussDoublePow_zero k]; exact gaussZero_add_zero

private theorem gaussDoublePow_inj : ∀ (k : Nat) {u v : GaussInt},
    gaussDoublePow k u = gaussDoublePow k v → u = v
  | 0, _, _, h => by rw [gaussDoublePow_base, gaussDoublePow_base] at h; exact h
  | k + 1, u, v, h => by
    apply gaussDoublePow_inj k
    have hr := congrArg GaussInt.re h
    have hi := congrArg GaussInt.im h
    apply GaussInt.ext <;> simp only [gaussDoublePow_step, GaussInt.add_def] at hr hi <;> omega

private theorem gaussDoublePow_map_add : ∀ (k : Nat) (u v : GaussInt),
    gaussDoublePow k (u.add v) = (gaussDoublePow k u).add (gaussDoublePow k v)
  | 0, _, _ => by simp only [gaussDoublePow_base]
  | k + 1, u, v => by
    simp only [gaussDoublePow_step, gaussDoublePow_map_add k]
    apply GaussInt.ext <;> simp [GaussInt.add_def] <;> omega

private theorem gaussDoublePow_map_sub : ∀ (k : Nat) (u v : GaussInt),
    gaussDoublePow k (u.sub v) = (gaussDoublePow k u).sub (gaussDoublePow k v)
  | 0, _, _ => by simp only [gaussDoublePow_base]
  | k + 1, u, v => by
    simp only [gaussDoublePow_step, gaussDoublePow_map_sub k]
    apply GaussInt.ext <;> simp [GaussInt.add_def, GaussInt.sub_def] <;> omega

/-- Exact Gaussian-integer sum over all `2 ^ w` values of `BitVec w`. -/
def bvGaussSum (w : Nat) (f : BitVec w → GaussInt) : GaussInt :=
  ⟨intSum (2 ^ w) (fun i => (f (BitVec.ofFin i)).re),
   intSum (2 ^ w) (fun i => (f (BitVec.ofFin i)).im)⟩

private theorem bvGaussSum_add (w : Nat) (f g : BitVec w → GaussInt) :
    bvGaussSum w (fun y => (f y).add (g y)) = (bvGaussSum w f).add (bvGaussSum w g) := by
  apply GaussInt.ext <;> simp [bvGaussSum, GaussInt.add_def, intSum_add]

private theorem bvGaussSum_sub (w : Nat) (f g : BitVec w → GaussInt) :
    bvGaussSum w (fun y => (f y).sub (g y)) = (bvGaussSum w f).sub (bvGaussSum w g) := by
  apply GaussInt.ext <;> simp [bvGaussSum, GaussInt.sub_def, intSum_sub]

private theorem bvGaussSum_doublePow (w k : Nat) (f : BitVec w → GaussInt) :
    bvGaussSum w (fun y => gaussDoublePow k (f y)) = gaussDoublePow k (bvGaussSum w f) := by
  apply GaussInt.ext
  · simp only [bvGaussSum, gaussDoublePow_re, intSum_mul_left]
  · simp only [bvGaussSum, gaussDoublePow_im, intSum_mul_left]

private theorem bvGaussSum_const (w : Nat) (z : GaussInt) :
    bvGaussSum w (fun _ => z) = gaussDoublePow w z := by
  apply GaussInt.ext
  · simp only [bvGaussSum, intSum_const, gaussDoublePow_re]
  · simp only [bvGaussSum, intSum_const, gaussDoublePow_im]

private theorem bvGaussSum_comm (w₁ w₂ : Nat) (h : BitVec w₁ → BitVec w₂ → GaussInt) :
    bvGaussSum w₁ (fun x => bvGaussSum w₂ (fun y => h x y)) =
      bvGaussSum w₂ (fun y => bvGaussSum w₁ (fun x => h x y)) := by
  apply GaussInt.ext <;> simp only [bvGaussSum] <;> exact intSum_comm _ _ _

/-- `[DFMS22, Eq. (6)]` local `⊥ ↔ uniform` decompression/compression operator over
    `Option (BitVec (2 * m))` (even output width `w = 2 * m`, including `m = 128 -> w = 256`),
    scaled by `2 ^ (2 * m)` so all amplitudes remain exact Gaussian integers:
    - swaps `none` (`⊥`) with the uniform state `2^-m ∑_y |some y⟩`,
    - acts as identity on the `(2^(2m) - 1)`-dimensional subspace orthogonal to uniform. -/
def dfmsCellDecompress (m : Nat) (f : Option (BitVec (2 * m)) → GaussInt) :
    Option (BitVec (2 * m)) → GaussInt
  | none => gaussDoublePow m (bvGaussSum (2 * m) (fun y => f (some y)))
  | some y =>
    ((gaussDoublePow (2 * m) (f (some y))).sub
      (bvGaussSum (2 * m) (fun y' => f (some y')))).add
      (gaussDoublePow m (f none))

/-- Sum of `Nat` weights across `Option (BitVec w)` (`none = ⊥` plus all `2 ^ w` values `some y`). -/
def dfmsCellSum (w : Nat) (φ : Option (BitVec w) → Nat) : Nat :=
  φ none + qsum (2 ^ w) (fun j => φ (some (BitVec.ofFin j)))

private theorem dfmsCellSum_congr (w : Nat) (φ ψ : Option (BitVec w) → Nat)
    (h : ∀ c, φ c = ψ c) : dfmsCellSum w φ = dfmsCellSum w ψ := by
  simp only [dfmsCellSum, h none]
  rw [qsum_congr (fun j => h (some (BitVec.ofFin j)))]

private theorem dfmsCellSum_add (w : Nat) (φ ψ : Option (BitVec w) → Nat) :
    dfmsCellSum w (fun c => φ c + ψ c) = dfmsCellSum w φ + dfmsCellSum w ψ := by
  simp only [dfmsCellSum, qsum_add]; omega

private theorem dfmsCellSum_mul (w c : Nat) (φ : Option (BitVec w) → Nat) :
    dfmsCellSum w (fun x => c * φ x) = c * dfmsCellSum w φ := by
  simp only [dfmsCellSum, qsum_mul_left, Nat.mul_add]

private theorem dfmsCellDecompress_add (m : Nat) (f g : Option (BitVec (2 * m)) → GaussInt)
    (c : Option (BitVec (2 * m))) :
    dfmsCellDecompress m (fun x => (f x).add (g x)) c =
      (dfmsCellDecompress m f c).add (dfmsCellDecompress m g c) := by
  cases c with
  | none =>
    simp only [dfmsCellDecompress, bvGaussSum_add, gaussDoublePow_map_add]
  | some y =>
    simp only [dfmsCellDecompress, bvGaussSum_add, gaussDoublePow_map_add]
    apply GaussInt.ext <;> simp [GaussInt.add_def, GaussInt.sub_def] <;> omega

private theorem dfmsCellDecompress_sub (m : Nat) (f g : Option (BitVec (2 * m)) → GaussInt)
    (c : Option (BitVec (2 * m))) :
    dfmsCellDecompress m (fun x => (f x).sub (g x)) c =
      (dfmsCellDecompress m f c).sub (dfmsCellDecompress m g c) := by
  cases c with
  | none =>
    simp only [dfmsCellDecompress, bvGaussSum_sub, gaussDoublePow_map_sub]
  | some y =>
    simp only [dfmsCellDecompress, bvGaussSum_sub, gaussDoublePow_map_sub]
    apply GaussInt.ext <;> simp [GaussInt.add_def, GaussInt.sub_def] <;> omega

private theorem dfmsCellDecompress_doublePow (m k : Nat) (f : Option (BitVec (2 * m)) → GaussInt)
    (c : Option (BitVec (2 * m))) :
    dfmsCellDecompress m (fun x => gaussDoublePow k (f x)) c =
      gaussDoublePow k (dfmsCellDecompress m f c) := by
  cases c with
  | none =>
    simp only [dfmsCellDecompress, bvGaussSum_doublePow, gaussDoublePow_add]
    rw [Nat.add_comm]
  | some y =>
    simp only [dfmsCellDecompress, bvGaussSum_doublePow, gaussDoublePow_add,
      gaussDoublePow_map_add, gaussDoublePow_map_sub]
    have h1 : 2 * m + k = k + 2 * m := Nat.add_comm _ _
    have h2 : m + k = k + m := Nat.add_comm _ _
    rw [h1, h2]

private theorem dfmsCellDecompress_bvGaussSum (m w : Nat)
    (h : BitVec w → Option (BitVec (2 * m)) → GaussInt) (c : Option (BitVec (2 * m))) :
    dfmsCellDecompress m (fun x => bvGaussSum w (fun z => h z x)) c =
      bvGaussSum w (fun z => dfmsCellDecompress m (h z) c) := by
  cases c with
  | none =>
    simp only [dfmsCellDecompress, ← bvGaussSum_doublePow]
    exact bvGaussSum_comm _ _ _
  | some y =>
    simp only [dfmsCellDecompress, bvGaussSum_add, bvGaussSum_sub, ← bvGaussSum_doublePow]
    congr 1
    congr 1
    exact bvGaussSum_comm (2 * m) w (fun y' z => h z (some y'))

private theorem dfmsCellDecompress_zero (m : Nat) (c : Option (BitVec (2 * m))) :
    dfmsCellDecompress m (fun _ => GaussInt.zero) c = GaussInt.zero := by
  have hz : bvGaussSum (2 * m) (fun _ => GaussInt.zero) = GaussInt.zero := by
    rw [bvGaussSum_const, gaussDoublePow_zero]
  cases c with
  | none => simp only [dfmsCellDecompress, hz, gaussDoublePow_zero]
  | some _ => simp only [dfmsCellDecompress, hz, gaussDoublePow_zero, gaussZero_sub_zero, gaussZero_add_zero]

/-- Exact involution up to known integer normalization `2 ^ (4 * m)`:
    `dfmsCellDecompress m (dfmsCellDecompress m f) = 2^(4m) * f`. -/
theorem dfmsCellDecompress_square (m : Nat) (f : Option (BitVec (2 * m)) → GaussInt)
    (c : Option (BitVec (2 * m))) :
    dfmsCellDecompress m (dfmsCellDecompress m f) c = gaussDoublePow (4 * m) (f c) := by
  have hSumSome : bvGaussSum (2 * m) (fun y => dfmsCellDecompress m f (some y)) =
      gaussDoublePow (3 * m) (f none) := by
    simp only [dfmsCellDecompress, bvGaussSum_add, bvGaussSum_sub, bvGaussSum_doublePow,
      bvGaussSum_const, gaussDoublePow_add]
    have h3 : m + 2 * m = 3 * m := by omega
    rw [h3]
    apply GaussInt.ext <;> simp [GaussInt.add_def, GaussInt.sub_def] <;> omega
  cases c with
  | none =>
    change gaussDoublePow m (bvGaussSum (2 * m) (fun y => dfmsCellDecompress m f (some y))) =
      gaussDoublePow (4 * m) (f none)
    rw [hSumSome, gaussDoublePow_add]
    have h4 : m + 3 * m = 4 * m := by omega
    rw [h4]
  | some y =>
    change ((gaussDoublePow (2 * m) (dfmsCellDecompress m f (some y))).sub
      (bvGaussSum (2 * m) (fun y' => dfmsCellDecompress m f (some y')))).add
      (gaussDoublePow m (dfmsCellDecompress m f none)) = gaussDoublePow (4 * m) (f (some y))
    rw [hSumSome]
    unfold dfmsCellDecompress
    simp only [gaussDoublePow_map_add, gaussDoublePow_map_sub, gaussDoublePow_add]
    have h4 : 2 * m + 2 * m = 4 * m := by omega
    have h3 : 2 * m + m = 3 * m := by omega
    have h2 : m + m = 2 * m := by omega
    rw [h4, h3, h2]
    apply GaussInt.ext <;> simp [GaussInt.add_def, GaussInt.sub_def] <;> omega

private theorem natCast_mul_eq : ∀ (x y : Nat), ((x * y : Nat) : Int) = (x : Int) * (y : Int)
  | 0, _ => by simp
  | x + 1, y => by
    have ih := natCast_mul_eq x y
    have hAdd : (((x + 1) * y : Nat) : Int) = ((x * y : Nat) : Int) + (y : Int) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have hX : ((x + 1 : Nat) : Int) = (x : Int) + 1 := by omega
    rw [hAdd, ih, hX, Int.add_mul, Int.one_mul]

private theorem int_sq_expand (u v : Int) :
    (u + v) * (u + v) = u * u + (2 * v * u + v * v) := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm u v]
  have h2 : 2 * v * u = v * u + v * u := by
    have ht : (2 : Int) = 1 + 1 := rfl
    rw [ht, Int.add_mul, Int.one_mul, Int.add_mul]
  omega

private theorem dfms1D_norm_eq (m : Nat) (b : Int) (a : Fin (2 ^ (2 * m)) → Int) :
    let M : Int := ((2 ^ m : Nat) : Int)
    let N : Int := ((2 ^ (2 * m) : Nat) : Int)
    let S : Int := intSum (2 ^ (2 * m)) a
    (M * S) * (M * S) + intSum (2 ^ (2 * m)) (fun i =>
      (N * a i - S + M * b) * (N * a i - S + M * b)) =
    (N * N) * (b * b + intSum (2 ^ (2 * m)) (fun i => a i * a i)) := by
  intro M N S
  have hMN : M * M = N := by
    show ((2 ^ m : Nat) : Int) * ((2 ^ m : Nat) : Int) = ((2 ^ (2 * m) : Nat) : Int)
    rw [← natCast_mul_eq, ← Nat.pow_add]
    have hm : m + m = 2 * m := by omega
    rw [hm]
  let d : Int := M * b - S
  have hRewrite : ∀ i : Fin (2 ^ (2 * m)),
      (N * a i - S + M * b) * (N * a i - S + M * b) =
        (N * N) * (a i * a i) + ((2 * d * N) * a i + d * d) := by
    intro i
    have hLin : N * a i - S + M * b = N * a i + d := by dsimp [d]; omega
    rw [hLin, int_sq_expand (N * a i) d]
    have hSq : (N * a i) * (N * a i) = (N * N) * (a i * a i) := by
      rw [Int.mul_assoc, Int.mul_left_comm (a i) N (a i), ← Int.mul_assoc]
    have hMid : 2 * d * (N * a i) = (2 * d * N) * a i := by
      rw [← Int.mul_assoc]
    rw [hSq, hMid]
  rw [intSum_congr hRewrite, intSum_add, intSum_add, intSum_mul_left, intSum_mul_left, intSum_const]
  have hMS : (M * S) * (M * S) = N * (S * S) := by
    calc (M * S) * (M * S)
      _ = (M * M) * (S * S) := by rw [Int.mul_assoc, Int.mul_left_comm S M S, ← Int.mul_assoc]
      _ = N * (S * S) := by rw [hMN]
  have hSd : S * S + (2 * d * S + d * d) = N * (b * b) := by
    have hSum : S + d = M * b := by dsimp [d]; omega
    calc S * S + (2 * d * S + d * d)
      _ = (S + d) * (S + d) := (int_sq_expand S d).symm
      _ = (M * b) * (M * b) := by rw [hSum]
      _ = (M * M) * (b * b) := by rw [Int.mul_assoc, Int.mul_left_comm b M b, ← Int.mul_assoc]
      _ = N * (b * b) := by rw [hMN]
  have hMidN : (2 * d * N) * S = N * (2 * d * S) := by
    rw [Int.mul_assoc (2 * d) N S, Int.mul_comm N S, ← Int.mul_assoc (2 * d) S N, Int.mul_comm _ N]
  rw [hMS, hMidN]
  calc N * (S * S) + ((N * N) * intSum (2 ^ (2 * m)) (fun i => a i * a i) +
          (N * (2 * d * S) + N * (d * d)))
    _ = (N * N) * intSum (2 ^ (2 * m)) (fun i => a i * a i) +
          N * (S * S + (2 * d * S + d * d)) := by
        rw [Int.mul_add N (S * S), Int.mul_add N (2 * d * S)]
        omega
    _ = (N * N) * intSum (2 ^ (2 * m)) (fun i => a i * a i) + (N * N) * (b * b) := by
        rw [hSd, ← Int.mul_assoc N N (b * b)]
    _ = (N * N) * (b * b + intSum (2 ^ (2 * m)) (fun i => a i * a i)) := by
        rw [Int.mul_add, Int.add_comm]

/-- Scaled isometry of `[DFMS22, Eq. (6)]` local decompression on `Option (BitVec (2 * m))`:
    squared norm scales by `4 ^ (2 * m) = (2 ^ (2 * m)) ^ 2`. -/
theorem dfmsCellDecompress_norm (m : Nat) (f : Option (BitVec (2 * m)) → GaussInt) :
    dfmsCellSum (2 * m) (fun c => GaussInt.normSq (dfmsCellDecompress m f c)) =
      4 ^ (2 * m) * dfmsCellSum (2 * m) (fun c => GaussInt.normSq (f c)) := by
  apply Int.ofNat.inj
  have hPow : ((4 ^ (2 * m) : Nat) : Int) =
      ((2 ^ (2 * m) : Nat) : Int) * ((2 ^ (2 * m) : Nat) : Int) := by
    rw [← natCast_mul_eq]
    congr 1
    have h4 : 4 = 2 ^ 2 := rfl
    rw [h4, ← Nat.pow_mul, ← Nat.pow_add]
    congr 1; omega
  have hRe := dfms1D_norm_eq m (f none).re (fun i => (f (some (BitVec.ofFin i))).re)
  have hIm := dfms1D_norm_eq m (f none).im (fun i => (f (some (BitVec.ofFin i))).im)
  unfold dfmsCellSum
  dsimp only
  change ((GaussInt.normSq (dfmsCellDecompress m f none) +
      qsum (2 ^ (2 * m)) (fun j => GaussInt.normSq (dfmsCellDecompress m f (some (BitVec.ofFin j)))) : Nat) : Int) =
    ((4 ^ (2 * m) * (GaussInt.normSq (f none) +
      qsum (2 ^ (2 * m)) (fun j => GaussInt.normSq (f (some (BitVec.ofFin j))))) : Nat) : Int)
  have hCastL : ∀ x y : Nat, ((x + y : Nat) : Int) = (x : Int) + (y : Int) := fun _ _ => by omega
  have hNormCast : ∀ z : GaussInt, ((z.normSq : Nat) : Int) = z.re * z.re + z.im * z.im :=
    fun z => by rw [← GaussInt.normSqInt_def]; exact (GaussInt.normSqInt_eq_ofNat_normSq z).symm
  rw [hCastL, natCast_mul_eq, hCastL, hPow, ← intSum_of_qsum, ← intSum_of_qsum]
  have hNone : ((GaussInt.normSq (dfmsCellDecompress m f none) : Nat) : Int) =
      (((2 ^ m : Nat) : Int) * intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).re)) *
      (((2 ^ m : Nat) : Int) * intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).re)) +
      (((2 ^ m : Nat) : Int) * intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).im)) *
      (((2 ^ m : Nat) : Int) * intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).im)) := by
    rw [hNormCast]
    simp only [dfmsCellDecompress, gaussDoublePow_re, gaussDoublePow_im, bvGaussSum]
  have hSome : ∀ i : Fin (2 ^ (2 * m)),
      ((GaussInt.normSq (dfmsCellDecompress m f (some (BitVec.ofFin i))) : Nat) : Int) =
      (((2 ^ (2 * m) : Nat) : Int) * (f (some (BitVec.ofFin i))).re -
        intSum (2 ^ (2 * m)) (fun j => (f (some (BitVec.ofFin j))).re) +
        ((2 ^ m : Nat) : Int) * (f none).re) *
      (((2 ^ (2 * m) : Nat) : Int) * (f (some (BitVec.ofFin i))).re -
        intSum (2 ^ (2 * m)) (fun j => (f (some (BitVec.ofFin j))).re) +
        ((2 ^ m : Nat) : Int) * (f none).re) +
      (((2 ^ (2 * m) : Nat) : Int) * (f (some (BitVec.ofFin i))).im -
        intSum (2 ^ (2 * m)) (fun j => (f (some (BitVec.ofFin j))).im) +
        ((2 ^ m : Nat) : Int) * (f none).im) *
      (((2 ^ (2 * m) : Nat) : Int) * (f (some (BitVec.ofFin i))).im -
        intSum (2 ^ (2 * m)) (fun j => (f (some (BitVec.ofFin j))).im) +
        ((2 ^ m : Nat) : Int) * (f none).im) := by
    intro i
    rw [hNormCast]
    simp only [dfmsCellDecompress, GaussInt.add_def, GaussInt.sub_def, gaussDoublePow_re,
      gaussDoublePow_im, bvGaussSum]
  have hRhsSome : ∀ i : Fin (2 ^ (2 * m)),
      ((GaussInt.normSq (f (some (BitVec.ofFin i))) : Nat) : Int) =
        (f (some (BitVec.ofFin i))).re * (f (some (BitVec.ofFin i))).re +
        (f (some (BitVec.ofFin i))).im * (f (some (BitVec.ofFin i))).im :=
    fun i => hNormCast _
  have hRhsNone : ((GaussInt.normSq (f none) : Nat) : Int) =
      (f none).re * (f none).re + (f none).im * (f none).im :=
    hNormCast _
  rw [hNone, intSum_congr hSome, intSum_add, hRhsNone, intSum_congr hRhsSome, intSum_add]
  dsimp only at hRe hIm
  let N2 := ((2 ^ (2 * m) : Nat) : Int) * ((2 ^ (2 * m) : Nat) : Int)
  calc _
    _ = ((((2 ^ m : Nat) : Int) * intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).re)) *
         (((2 ^ m : Nat) : Int) * intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).re)) +
         intSum (2 ^ (2 * m)) (fun i =>
           (((2 ^ (2 * m) : Nat) : Int) * (f (some (BitVec.ofFin i))).re -
             intSum (2 ^ (2 * m)) (fun j => (f (some (BitVec.ofFin j))).re) +
             ((2 ^ m : Nat) : Int) * (f none).re) *
           (((2 ^ (2 * m) : Nat) : Int) * (f (some (BitVec.ofFin i))).re -
             intSum (2 ^ (2 * m)) (fun j => (f (some (BitVec.ofFin j))).re) +
             ((2 ^ m : Nat) : Int) * (f none).re))) +
        ((((2 ^ m : Nat) : Int) * intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).im)) *
         (((2 ^ m : Nat) : Int) * intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).im)) +
         intSum (2 ^ (2 * m)) (fun i =>
           (((2 ^ (2 * m) : Nat) : Int) * (f (some (BitVec.ofFin i))).im -
             intSum (2 ^ (2 * m)) (fun j => (f (some (BitVec.ofFin j))).im) +
             ((2 ^ m : Nat) : Int) * (f none).im) *
           (((2 ^ (2 * m) : Nat) : Int) * (f (some (BitVec.ofFin i))).im -
             intSum (2 ^ (2 * m)) (fun j => (f (some (BitVec.ofFin j))).im) +
             ((2 ^ m : Nat) : Int) * (f none).im))) := by omega
    _ = N2 * ((f none).re * (f none).re +
          intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).re * (f (some (BitVec.ofFin i))).re)) +
        N2 * ((f none).im * (f none).im +
          intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).im * (f (some (BitVec.ofFin i))).im)) := by
        rw [hRe, hIm]
    _ = N2 * (((f none).re * (f none).re + (f none).im * (f none).im) +
          (intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).re * (f (some (BitVec.ofFin i))).re) +
           intSum (2 ^ (2 * m)) (fun i => (f (some (BitVec.ofFin i))).im * (f (some (BitVec.ofFin i))).im))) := by
        rw [← Int.mul_add]
        congr 1; omega

/-- Full `n`-address `⊥`-labeled (`Option (BitVec (2 * m))`) compressed-oracle database (`[DFMS22]`).
    Each cell holds either `none` (`⊥`, unqueried) or `some y` (recorded `2m`-bit digest `y`). -/
@[reducible, expose] def DfmsTable (m : Nat) : Nat → Type
  | 0 => Unit
  | n + 1 => Option (BitVec (2 * m)) × DfmsTable m n

/-- Deployed `256`-bit (`2 * 128`) `⊥`-labeled compressed-oracle database (`Option Digest256` per address)
    matching `Hem`'s 256-bit salted Merkle-Canopy digests. -/
abbrev DfmsDigest256Table (n : Nat) : Type := DfmsTable 128 n

/-- Sum over all `(1 + 2^(2m))^n` compressed database configurations (`⊥` and recorded `2m`-bit digests). -/
def dfmsTableSum (m : Nat) : (n : Nat) → (DfmsTable m n → Nat) → Nat
  | 0, f => f ()
  | n + 1, f => dfmsCellSum (2 * m) (fun c => dfmsTableSum m n (fun D => f (c, D)))

private theorem dfmsTableSum_congr (m : Nat) : ∀ (n : Nat) (_f _g : DfmsTable m n → Nat),
    (∀ D, _f D = _g D) → dfmsTableSum m n _f = dfmsTableSum m n _g
  | 0, _, _, h => h ()
  | n + 1, f, g, h =>
    dfmsCellSum_congr (2 * m) _ _ (fun c =>
      dfmsTableSum_congr m n (fun D => f (c, D)) (fun D => g (c, D)) (fun D => h (c, D)))

private theorem dfmsTableSum_add (m : Nat) : ∀ (n : Nat) (f g : DfmsTable m n → Nat),
    dfmsTableSum m n (fun D => f D + g D) = dfmsTableSum m n f + dfmsTableSum m n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
    simp only [dfmsTableSum, dfmsTableSum_add m n, dfmsCellSum_add]

private theorem dfmsTableSum_mul (m : Nat) : ∀ (n c : Nat) (f : DfmsTable m n → Nat),
    dfmsTableSum m n (fun D => c * f D) = c * dfmsTableSum m n f
  | 0, _, _ => rfl
  | n + 1, c, f => by
    simp only [dfmsTableSum, dfmsTableSum_mul m n c, dfmsCellSum_mul]

private theorem dfmsTableSum_zero (m : Nat) : ∀ (n : Nat), dfmsTableSum m n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by
    simp only [dfmsTableSum, dfmsTableSum_zero m n, dfmsCellSum, qsum_const, Nat.mul_zero, Nat.add_zero]

private theorem dfmsTableSum_qsum (m : Nat) : ∀ (n k : Nat) (f : DfmsTable m n → Fin k → Nat),
    dfmsTableSum m n (fun D => qsum k (f D)) = qsum k (fun i => dfmsTableSum m n (fun D => f D i))
  | 0, _, _ => rfl
  | n + 1, k, f => by
    unfold dfmsTableSum dfmsCellSum
    dsimp only
    rw [dfmsTableSum_qsum m n k]
    have hSub : qsum (2 ^ (2 * m)) (fun j => dfmsTableSum m n (fun D => qsum k (f (some (BitVec.ofFin j), D)))) =
        qsum k (fun i => qsum (2 ^ (2 * m)) (fun j => dfmsTableSum m n (fun D => f (some (BitVec.ofFin j), D) i))) := by
      have h1 : ∀ j, dfmsTableSum m n (fun D => qsum k (f (some (BitVec.ofFin j), D))) =
          qsum k (fun i => dfmsTableSum m n (fun D => f (some (BitVec.ofFin j), D) i)) :=
        fun j => dfmsTableSum_qsum m n k (fun D => f (some (BitVec.ofFin j), D))
      rw [qsum_congr h1]
      clear h1
      induction k with
      | zero => simp [qsum_zero, qsum_const]
      | succ k' ih =>
        simp only [qsum_succ, qsum_add]
        rw [ih (fun D i => f D ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]
    rw [hSub, ← qsum_add]

/-- Read the `Option (BitVec (2 * m))` entry (`none = ⊥` or `some digest`) at address `x`. -/
def dfmsEntry {m : Nat} : (n : Nat) → DfmsTable m n → Fin n → Option (BitVec (2 * m))
  | 0, _, x => Fin.elim0 x
  | _ + 1, (c, _), ⟨0, _⟩ => c
  | n + 1, (_, D), ⟨i + 1, hi⟩ => dfmsEntry n D ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Replace address `x` of `D` by `c' : Option (BitVec (2 * m))`. -/
def dfmsUpdateAt {m : Nat} : (n : Nat) → DfmsTable m n → Fin n → Option (BitVec (2 * m)) → DfmsTable m n
  | 0, _, x, _ => Fin.elim0 x
  | _ + 1, (_, D), ⟨0, _⟩, c' => (c', D)
  | n + 1, (c, D), ⟨i + 1, hi⟩, c' => (c, dfmsUpdateAt n D ⟨i, Nat.lt_of_succ_lt_succ hi⟩ c')

/-- Count of non-`⊥` (`some digest`) recorded answer entries in `D : DfmsTable m n`. -/
def dfmsRecordedCount {m : Nat} : (n : Nat) → DfmsTable m n → Nat
  | 0, _ => 0
  | n + 1, (c, D) => (if c.isSome then 1 else 0) + dfmsRecordedCount n D

/-- Count of non-`⊥` recorded answer entries belonging to domain/salt `dom : Fin cardDom`. -/
def dfmsDomainRecordedCount {m : Nat} : (n : Nat) → {cardDom : Nat} →
    (Fin n → Fin cardDom) → Fin cardDom → DfmsTable m n → Nat
  | 0, _, _, _, _ => 0
  | n + 1, _, domainOf, dom, (c, D) =>
    (if c.isSome && decide (domainOf ⟨0, Nat.zero_lt_succ n⟩ = dom) then 1 else 0) +
      dfmsDomainRecordedCount n (fun i => domainOf i.succ) dom D

/-- Updating a single address `x` changes `dfmsRecordedCount` by at most `1`. -/
theorem dfmsRecordedCount_updateAt_le {m : Nat} :
    ∀ (n : Nat) (D : DfmsTable m n) (x : Fin n) (c' : Option (BitVec (2 * m))),
      dfmsRecordedCount n D ≤ dfmsRecordedCount n (dfmsUpdateAt n D x c') + 1
  | 0, _, x, _ => Fin.elim0 x
  | n + 1, (c, D), x, c' => by
    refine Fin.cases ?_ (fun j => ?_) x
    · change (if c.isSome then 1 else 0) + dfmsRecordedCount n D ≤
        (if c'.isSome then 1 else 0) + dfmsRecordedCount n D + 1
      cases c <;> cases c' <;> simp <;> omega
    · have ih := dfmsRecordedCount_updateAt_le n D j c'
      change (if c.isSome then 1 else 0) + dfmsRecordedCount n D ≤
        (if c.isSome then 1 else 0) + dfmsRecordedCount n (dfmsUpdateAt n D j c') + 1
      omega

/-- Exact conservation of non-`⊥` recorded `2m`-bit digests across disjoint salts/domains. -/
theorem dfmsDomainRecordedCount_sum_eq {m : Nat} :
    ∀ (n : Nat) {cardDom : Nat} (domainOf : Fin n → Fin cardDom) (D : DfmsTable m n),
      qsum cardDom (fun dom => dfmsDomainRecordedCount n domainOf dom D) = dfmsRecordedCount n D
  | 0, _, _, _ => by
    simp only [dfmsDomainRecordedCount, dfmsRecordedCount, qsum_const, Nat.mul_zero]
  | n + 1, cardDom, domainOf, (c, D) => by
    simp only [dfmsDomainRecordedCount, dfmsRecordedCount, qsum_add]
    rw [dfmsDomainRecordedCount_sum_eq n (fun i => domainOf i.succ) D]
    congr 1
    cases hc : c.isSome
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]
    · simp only [Bool.true_and, ↓reduceIte]
      have hInd := qsum_ite_eq cardDom (domainOf ⟨0, Nat.zero_lt_succ n⟩) 1
      have hCongr : qsum cardDom (fun dom =>
          if decide (domainOf ⟨0, Nat.zero_lt_succ n⟩ = dom) = true then 1 else 0) =
        qsum cardDom (fun dom =>
          if dom = domainOf ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) := by
        apply qsum_congr; intro dom
        by_cases he : dom = domainOf ⟨0, Nat.zero_lt_succ n⟩
        · subst he; simp
        · have he' : domainOf ⟨0, Nat.zero_lt_succ n⟩ ≠ dom := fun h => he h.symm
          simp only [he, he', decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [hCongr, hInd]

/-- Empty compressed database `|⊥, …, ⊥⟩` (`none` at every address). -/
def dfmsIsAllBot (m : Nat) : (n : Nat) → DfmsTable m n → Bool
  | 0, _ => true
  | n + 1, (c, D) => c.isNone && dfmsIsAllBot m n D

/-- Total decompressed database (`some y_x` at every address, zero `⊥` entries). -/
def dfmsIsTotal (m : Nat) : (n : Nat) → DfmsTable m n → Bool
  | 0, _ => true
  | n + 1, (c, D) => c.isSome && dfmsIsTotal m n D

/-- Extract the `2m`-bit random oracle `Fin n → BitVec (2 * m)` from a database. -/
def dfmsToOracle (m : Nat) : (n : Nat) → DfmsTable m n → Fin n → BitVec (2 * m)
  | 0, _, x => Fin.elim0 x
  | n + 1, (c, D), x => Fin.cases (c.getD 0#(2 * m)) (dfmsToOracle m n D) x

/-- Summing over total `DfmsTable m n` databases equals `uniformOracleSum (2 * m) n` identically. -/
theorem dfmsTableSum_total_eq_uniform (m : Nat) :
    ∀ (n : Nat) (f : (Fin n → BitVec (2 * m)) → Nat),
      dfmsTableSum m n (fun D => if dfmsIsTotal m n D then f (dfmsToOracle m n D) else 0) =
        uniformOracleSum (2 * m) n f
  | 0, _ => by rw [uniformOracleSum_zero]; rfl
  | n + 1, f => by
    unfold dfmsTableSum dfmsCellSum
    dsimp only
    have hNone : dfmsTableSum m n (fun D =>
        if dfmsIsTotal m (n + 1) (none, D) then f (dfmsToOracle m (n + 1) (none, D)) else 0) = 0 := by
      simp only [dfmsIsTotal, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact dfmsTableSum_zero m n
    rw [hNone, Nat.zero_add]
    simp only [uniformOracleSum_succ]
    apply qsum_congr
    intro j
    have hSome : ∀ D : DfmsTable m n,
        (if dfmsIsTotal m (n + 1) (some (BitVec.ofFin j), D) then
          f (dfmsToOracle m (n + 1) (some (BitVec.ofFin j), D)) else 0) =
        (if dfmsIsTotal m n D then f (Fin.cases (BitVec.ofFin j) (dfmsToOracle m n D)) else 0) := by
      intro D
      simp only [dfmsIsTotal, Option.isSome_some, Bool.true_and, dfmsToOracle, Option.getD_some]
    rw [dfmsTableSum_congr m n _ _ hSome,
      dfmsTableSum_total_eq_uniform m n (fun H => f (Fin.cases (BitVec.ofFin j) H))]

/-- Tensor product of `dfmsCellDecompress m` across all `n` addresses (`[DFMS22, Eq. (6)]`). -/
def dfmsDecompress (m : Nat) : (n : Nat) → (DfmsTable m n → GaussInt) → DfmsTable m n → GaussInt
  | 0, f, () => f ()
  | n + 1, f, (c, D) =>
    dfmsCellDecompress m (fun c' => dfmsDecompress m n (fun D' => f (c', D')) D) c

private theorem dfmsDecompress_congr (m : Nat) : ∀ (n : Nat) (f g : DfmsTable m n → GaussInt),
    (∀ D, f D = g D) → dfmsDecompress m n f = dfmsDecompress m n g := by
  intro n f g h
  exact congrArg (dfmsDecompress m n) (funext h)

private theorem dfmsDecompress_add (m : Nat) : ∀ (n : Nat) (f g : DfmsTable m n → GaussInt)
    (D : DfmsTable m n),
    dfmsDecompress m n (fun X => (f X).add (g X)) D =
      (dfmsDecompress m n f D).add (dfmsDecompress m n g D)
  | 0, _, _, () => rfl
  | n + 1, f, g, (c, D) => by
    simp only [dfmsDecompress]
    have hInner : (fun c' => dfmsDecompress m n (fun D' => (f (c', D')).add (g (c', D'))) D) =
        (fun c' => (dfmsDecompress m n (fun D' => f (c', D')) D).add
          (dfmsDecompress m n (fun D' => g (c', D')) D)) := by
      funext c'; exact dfmsDecompress_add m n _ _ D
    rw [hInner, dfmsCellDecompress_add]

private theorem dfmsDecompress_sub (m : Nat) : ∀ (n : Nat) (f g : DfmsTable m n → GaussInt)
    (D : DfmsTable m n),
    dfmsDecompress m n (fun X => (f X).sub (g X)) D =
      (dfmsDecompress m n f D).sub (dfmsDecompress m n g D)
  | 0, _, _, () => rfl
  | n + 1, f, g, (c, D) => by
    simp only [dfmsDecompress]
    have hInner : (fun c' => dfmsDecompress m n (fun D' => (f (c', D')).sub (g (c', D'))) D) =
        (fun c' => (dfmsDecompress m n (fun D' => f (c', D')) D).sub
          (dfmsDecompress m n (fun D' => g (c', D')) D)) := by
      funext c'; exact dfmsDecompress_sub m n _ _ D
    rw [hInner, dfmsCellDecompress_sub]

private theorem dfmsDecompress_doublePow (m : Nat) : ∀ (n k : Nat) (f : DfmsTable m n → GaussInt)
    (D : DfmsTable m n),
    dfmsDecompress m n (fun X => gaussDoublePow k (f X)) D =
      gaussDoublePow k (dfmsDecompress m n f D)
  | 0, _, _, () => rfl
  | n + 1, k, f, (c, D) => by
    simp only [dfmsDecompress]
    have hInner : (fun c' => dfmsDecompress m n (fun D' => gaussDoublePow k (f (c', D'))) D) =
        (fun c' => gaussDoublePow k (dfmsDecompress m n (fun D' => f (c', D')) D)) := by
      funext c'; exact dfmsDecompress_doublePow m n k _ D
    rw [hInner, dfmsCellDecompress_doublePow]

private theorem dfmsDecompress_zero (m : Nat) : ∀ (n : Nat) (D : DfmsTable m n),
    dfmsDecompress m n (fun _ => GaussInt.zero) D = GaussInt.zero
  | 0, () => rfl
  | n + 1, (c, D) => by
    simp only [dfmsDecompress]
    have hInner : (fun (_ : Option (BitVec (2 * m))) =>
        dfmsDecompress m n (fun _ => GaussInt.zero) D) = (fun _ => GaussInt.zero) := by
      funext _; exact dfmsDecompress_zero m n D
    rw [hInner, dfmsCellDecompress_zero]

private theorem dfmsDecompress_bvGaussSum (m : Nat) : ∀ (n w : Nat)
    (h : BitVec w → DfmsTable m n → GaussInt) (D : DfmsTable m n),
    dfmsDecompress m n (fun X => bvGaussSum w (fun z => h z X)) D =
      bvGaussSum w (fun z => dfmsDecompress m n (h z) D)
  | 0, _, _, () => rfl
  | n + 1, w, h, (c, D) => by
    simp only [dfmsDecompress]
    have hInner : (fun c' => dfmsDecompress m n (fun D' => bvGaussSum w (fun z => h z (c', D'))) D) =
        (fun c' => bvGaussSum w (fun z => dfmsDecompress m n (fun D' => h z (c', D')) D)) := by
      funext c'; exact dfmsDecompress_bvGaussSum m n w _ D
    rw [hInner, dfmsCellDecompress_bvGaussSum]

private theorem dfmsCellDecompress_comm_decompress (m : Nat) (n : Nat)
    (g : Option (BitVec (2 * m)) → DfmsTable m n → GaussInt)
    (c : Option (BitVec (2 * m))) (D : DfmsTable m n) :
    dfmsCellDecompress m (fun c' => dfmsDecompress m n (g c') D) c =
      dfmsDecompress m n (fun D' => dfmsCellDecompress m (fun c' => g c' D') c) D := by
  cases c with
  | none =>
    simp only [dfmsCellDecompress, dfmsDecompress_doublePow, dfmsDecompress_bvGaussSum]
  | some y =>
    simp only [dfmsCellDecompress, dfmsDecompress_add, dfmsDecompress_sub,
      dfmsDecompress_doublePow, dfmsDecompress_bvGaussSum]

/-- `n`-address decompression squared equals amplitude multiplication by `2 ^ (4 * m * n)`. -/
theorem dfmsDecompress_square (m : Nat) : ∀ (n : Nat) (f : DfmsTable m n → GaussInt)
    (D : DfmsTable m n),
    dfmsDecompress m n (dfmsDecompress m n f) D = gaussDoublePow (4 * m * n) (f D)
  | 0, _, () => by simp [dfmsDecompress, gaussDoublePow_base]
  | n + 1, f, (c, D) => by
    change dfmsCellDecompress m
      (fun c' => dfmsDecompress m n
        (fun D' => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => f (c'', D'')) D') c') D) c =
      gaussDoublePow (4 * m * (n + 1)) (f (c, D))
    have hComm : (fun c' => dfmsDecompress m n
        (fun D' => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => f (c'', D'')) D') c') D) =
      (fun c' => dfmsCellDecompress m
        (fun c'' => dfmsDecompress m n (dfmsDecompress m n (fun D'' => f (c'', D''))) D) c') := by
      funext c'
      exact (dfmsCellDecompress_comm_decompress m n
        (fun c'' D' => dfmsDecompress m n (fun D'' => f (c'', D'')) D') c' D).symm
    rw [hComm]
    have hInner : (fun c'' => dfmsDecompress m n (dfmsDecompress m n (fun D'' => f (c'', D''))) D) =
        (fun c'' => gaussDoublePow (4 * m * n) (f (c'', D))) := by
      funext c''; exact dfmsDecompress_square m n _ D
    rw [hInner]
    have hPull2 : (fun c' => dfmsCellDecompress m (fun c'' => gaussDoublePow (4 * m * n) (f (c'', D))) c') =
        (fun c' => gaussDoublePow (4 * m * n) (dfmsCellDecompress m (fun c'' => f (c'', D)) c')) := by
      funext c'; exact dfmsCellDecompress_doublePow m (4 * m * n) (fun c'' => f (c'', D)) c'
    rw [hPull2, dfmsCellDecompress_doublePow, dfmsCellDecompress_square, gaussDoublePow_add]
    have hMul : 4 * m * n + 4 * m = 4 * m * (n + 1) := by rw [Nat.mul_succ]
    rw [hMul]

/-- Scaled isometry of `n`-address decompression (`4 ^ (2 * m * n)` squared-norm factor). -/
theorem dfmsDecompress_norm (m : Nat) : ∀ (n : Nat) (f : DfmsTable m n → GaussInt),
    dfmsTableSum m n (fun D => GaussInt.normSq (dfmsDecompress m n f D)) =
      4 ^ (2 * m * n) * dfmsTableSum m n (fun D => GaussInt.normSq (f D))
  | 0, _ => by simp [dfmsTableSum, dfmsDecompress]
  | n + 1, f => by
    unfold dfmsTableSum dfmsDecompress
    have hSwap : dfmsCellSum (2 * m) (fun c =>
        dfmsTableSum m n (fun D =>
          GaussInt.normSq (dfmsCellDecompress m (fun c' => dfmsDecompress m n (fun D' => f (c', D')) D) c))) =
      dfmsTableSum m n (fun D =>
        dfmsCellSum (2 * m) (fun c =>
          GaussInt.normSq (dfmsCellDecompress m (fun c' => dfmsDecompress m n (fun D' => f (c', D')) D) c))) := by
      unfold dfmsCellSum
      rw [dfmsTableSum_add, dfmsTableSum_qsum]
    rw [hSwap]
    have hCell : ∀ D : DfmsTable m n,
        dfmsCellSum (2 * m) (fun c =>
          GaussInt.normSq (dfmsCellDecompress m (fun c' => dfmsDecompress m n (fun D' => f (c', D')) D) c)) =
        4 ^ (2 * m) * dfmsCellSum (2 * m) (fun c' =>
          GaussInt.normSq (dfmsDecompress m n (fun D' => f (c', D')) D)) :=
      fun D => dfmsCellDecompress_norm m _
    rw [dfmsTableSum_congr m n _ _ hCell, dfmsTableSum_mul]
    have hSwapBack : dfmsTableSum m n (fun D =>
        dfmsCellSum (2 * m) (fun c' => GaussInt.normSq (dfmsDecompress m n (fun D' => f (c', D')) D))) =
      dfmsCellSum (2 * m) (fun c' =>
        dfmsTableSum m n (fun D => GaussInt.normSq (dfmsDecompress m n (fun D' => f (c', D')) D))) := by
      unfold dfmsCellSum
      rw [dfmsTableSum_add, dfmsTableSum_qsum]
    rw [hSwapBack]
    have hTail : ∀ c' : Option (BitVec (2 * m)),
        dfmsTableSum m n (fun D => GaussInt.normSq (dfmsDecompress m n (fun D' => f (c', D')) D)) =
          4 ^ (2 * m * n) * dfmsTableSum m n (fun D => GaussInt.normSq (f (c', D))) :=
      fun c' => dfmsDecompress_norm m n _
    rw [dfmsCellSum_congr (2 * m) _ _ hTail, dfmsCellSum_mul, ← Nat.mul_assoc, ← Nat.pow_add]
    have hExp : 2 * m + 2 * m * n = 2 * m * (n + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    rw [hExp]

/-- Decompressing the pure `|⊥, …, ⊥⟩` (`dfmsIsAllBot`) state yields `2^(m*n)` on every total
    oracle table and `0` on every partial (`none`-containing) table! -/
theorem dfmsDecompress_allBot (m : Nat) : ∀ (n : Nat) (z : GaussInt) (D : DfmsTable m n),
    dfmsDecompress m n (fun X => if dfmsIsAllBot m n X then z else GaussInt.zero) D =
      if dfmsIsTotal m n D then gaussDoublePow (m * n) z else GaussInt.zero
  | 0, z, () => by simp [dfmsDecompress, dfmsIsAllBot, dfmsIsTotal, gaussDoublePow_base]
  | n + 1, z, (c, D) => by
    unfold dfmsDecompress
    have hInner : (fun c' : Option (BitVec (2 * m)) =>
        dfmsDecompress m n (fun D' => if dfmsIsAllBot m (n + 1) (c', D') then z else GaussInt.zero) D) =
      (fun c' => match c' with
        | none => if dfmsIsTotal m n D then gaussDoublePow (m * n) z else GaussInt.zero
        | some _ => GaussInt.zero) := by
      funext c'
      cases c' with
      | none =>
        simp only [dfmsIsAllBot, Option.isNone_none, Bool.true_and]
        exact dfmsDecompress_allBot m n z D
      | some _ =>
        simp only [dfmsIsAllBot, Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact dfmsDecompress_zero m n D
    rw [hInner]
    have hSumZero : bvGaussSum (2 * m) (fun _ => GaussInt.zero) = GaussInt.zero := by
      rw [bvGaussSum_const, gaussDoublePow_zero]
    cases c with
    | none =>
      simp only [dfmsCellDecompress, hSumZero, gaussDoublePow_zero, dfmsIsTotal,
        Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    | some y =>
      simp only [dfmsCellDecompress, hSumZero, gaussDoublePow_zero, dfmsIsTotal,
        Option.isSome_some, Bool.true_and]
      have hzSub : GaussInt.zero.sub GaussInt.zero = GaussInt.zero := gaussZero_sub_zero
      rw [hzSub]
      cases dfmsIsTotal m n D
      · simp only [Bool.false_eq_true, ↓reduceIte, gaussDoublePow_zero]; exact gaussZero_add_zero
      · simp only [↓reduceIte, gaussDoublePow_add]
        have hAdd : GaussInt.zero.add (gaussDoublePow (m + m * n) z) = gaussDoublePow (m * (n + 1)) z := by
          have hm : m + m * n = m * (n + 1) := by rw [Nat.mul_succ, Nat.add_comm]
          rw [hm]
          apply GaussInt.ext <;> simp [GaussInt.add_def, GaussInt.zero_def]
        exact hAdd

/-- Joint quantum state over the `DfmsTable m n` (`Option (BitVec (2 * m))`) compressed database
    and the adversary's `(Fin n, BitVec (2 * m), Fin cardAnc)` registers. -/
abbrev DfmsState (m n cardAnc : Nat) : Type := DfmsTable m n → QVec n (2 * m) cardAnc

/-- Lift `dfmsDecompress m n` onto `DfmsState m n cardAnc`. -/
def dfmsDecompressState {m n cardAnc : Nat} (ψ : DfmsState m n cardAnc) : DfmsState m n cardAnc :=
  fun D x y a => dfmsDecompress m n (fun D' => ψ D' x y a) D

/-- Scale a `DfmsState` by `2 ^ k`. -/
def doubleDfmsState {m n cardAnc : Nat} (k : Nat) (ψ : DfmsState m n cardAnc) : DfmsState m n cardAnc :=
  fun D => qvecDoublePow k (ψ D)

/-- Embed a standard random-oracle state `(Fin n → BitVec (2 * m)) → QVec` into `DfmsState`
    with zero amplitude on partial (`⊥`-containing) tables. -/
def embedRealOracleState {m n cardAnc : Nat}
    (ψ : (Fin n → BitVec (2 * m)) → QVec n (2 * m) cardAnc) : DfmsState m n cardAnc :=
  fun D => if dfmsIsTotal m n D then ψ (dfmsToOracle m n D) else QVec.zero n (2 * m) cardAnc

/-- Initial `|⊥, …, ⊥⟩ ⊗ |init⟩` state in the DFMS compressed-oracle runtime (`0` recorded entries). -/
def dfmsInitState {m n cardAnc : Nat} (init : QVec n (2 * m) cardAnc) : DfmsState m n cardAnc :=
  fun D => if dfmsIsAllBot m n D then init else QVec.zero n (2 * m) cardAnc

/-- Coherent `2m`-bit query against a decompressed `DfmsTable` cell (`xorFin y v` on `some v`,
    identity on `none`). -/
def dfmsCellXor {m n cardAnc : Nat} (D : DfmsTable m n)
    (ψ : QVec n (2 * m) cardAnc) : QVec n (2 * m) cardAnc :=
  fun x y a =>
    match dfmsEntry n D x with
    | none => ψ x y a
    | some v => ψ x (xorFin y v) a

/-- One decompressed query step followed by adversary local unitary `U`. -/
def dfmsCoherentStep {m n cardAnc : Nat} (U : ScaledUnitary n (2 * m) cardAnc)
    (ψ : DfmsState m n cardAnc) : DfmsState m n cardAnc :=
  fun D => U.apply (dfmsCellXor D (ψ D))

/-- Operational DFMS compressed-oracle step (`F ∘ dfmsCoherentStep U ∘ F`, `[DFMS22, Eq. (8)]`). -/
def dfmsOracleStep {m n cardAnc : Nat} (U : ScaledUnitary n (2 * m) cardAnc)
    (ψ : DfmsState m n cardAnc) : DfmsState m n cardAnc :=
  dfmsDecompressState (dfmsCoherentStep U (dfmsDecompressState ψ))

/-- Independent `t`-step DFMS compressed-oracle runtime starting at `|⊥, …, ⊥⟩ ⊗ |A.init⟩`
    for arbitrary `2m`-bit coherent adversaries (`m = 128 -> w = 256` `Digest256`!). -/
def dfmsAdvStateAt (m : Nat) {n cardAnc Q : Nat} (A : QuantumAdv n (2 * m) cardAnc Q) :
    (t : Nat) → t ≤ Q → DfmsState m n cardAnc
  | 0, _ => dfmsInitState A.init
  | t + 1, ht => dfmsOracleStep (A.steps ⟨t, ht⟩)
      (dfmsAdvStateAt m A t (Nat.le_of_succ_le ht))

private theorem doubleDfmsState_apply {m n cardAnc : Nat} (k : Nat) (ψ : DfmsState m n cardAnc)
    (D : DfmsTable m n) (x : Fin n) (y : Fin (2 ^ (2 * m))) (a : Fin cardAnc) :
    doubleDfmsState k ψ D x y a = gaussDoublePow k (ψ D x y a) := by
  unfold doubleDfmsState
  rw [qvecDoublePow_def]

private theorem doubleDfmsState_zero {m n cardAnc : Nat} (ψ : DfmsState m n cardAnc) :
    doubleDfmsState 0 ψ = ψ := by
  funext D x y a
  rw [doubleDfmsState_apply, gaussDoublePow_base]

private theorem dfmsDecompressState_square {m n cardAnc : Nat} (ψ : DfmsState m n cardAnc) :
    dfmsDecompressState (dfmsDecompressState ψ) = doubleDfmsState (4 * m * n) ψ := by
  funext D x y a
  rw [doubleDfmsState_apply]
  exact dfmsDecompress_square m n _ D

private theorem dfmsDecompressState_double {m n cardAnc : Nat} (k : Nat) (ψ : DfmsState m n cardAnc) :
    dfmsDecompressState (doubleDfmsState k ψ) = doubleDfmsState k (dfmsDecompressState ψ) := by
  funext D x y a
  rw [doubleDfmsState_apply]
  have h := dfmsDecompress_doublePow m n k (fun X => ψ X x y a) D
  have hf : (fun X => gaussDoublePow k (ψ X x y a)) = (fun X => doubleDfmsState k ψ X x y a) := by
    funext X; rw [doubleDfmsState_apply]
  rw [hf] at h
  exact h

private theorem doubleDfmsState_add {m n cardAnc : Nat} (k l : Nat) (ψ : DfmsState m n cardAnc) :
    doubleDfmsState k (doubleDfmsState l ψ) = doubleDfmsState (k + l) ψ := by
  funext D x y a
  rw [doubleDfmsState_apply, doubleDfmsState_apply, doubleDfmsState_apply]
  exact gaussDoublePow_add k l _

private theorem doubleDfmsState_inj {m n cardAnc : Nat} (k : Nat)
    {ψ φ : DfmsState m n cardAnc} (h : doubleDfmsState k ψ = doubleDfmsState k φ) : ψ = φ := by
  funext D x y a
  have hp := congrArg (fun s => s D x y a) h
  rw [doubleDfmsState_apply, doubleDfmsState_apply] at hp
  exact gaussDoublePow_inj k hp

private theorem dfmsCoherentStep_double {m n cardAnc : Nat} (U : ScaledUnitary n (2 * m) cardAnc)
    (k : Nat) (ψ : DfmsState m n cardAnc) :
    dfmsCoherentStep U (doubleDfmsState k ψ) = doubleDfmsState k (dfmsCoherentStep U ψ) := by
  funext D
  have hCell : dfmsCellXor D (qvecDoublePow k (ψ D)) = qvecDoublePow k (dfmsCellXor D (ψ D)) := by
    funext x y a
    (unfold dfmsCellXor; simp only [qvecDoublePow_def])
    cases dfmsEntry n D x <;> rfl
  unfold dfmsCoherentStep doubleDfmsState
  rw [hCell, U.map_doublePow]

private theorem dfmsToOracle_eq_entry (m : Nat) : ∀ (n : Nat) (D : DfmsTable m n),
    dfmsIsTotal m n D = true → ∀ x : Fin n, dfmsEntry n D x = some (dfmsToOracle m n D x)
  | 0, _, _, x => Fin.elim0 x
  | n + 1, (c, D), hTot, x => by
    simp only [dfmsIsTotal, Bool.and_eq_true] at hTot
    cases c with
    | none => simp at hTot
    | some v =>
      refine Fin.cases ?_ (fun j => ?_) x
      · rfl
      · exact dfmsToOracle_eq_entry m n D hTot.2 j

private theorem dfmsCoherentStep_embedReal {m n cardAnc : Nat}
    (U : ScaledUnitary n (2 * m) cardAnc)
    (ψ : (Fin n → BitVec (2 * m)) → QVec n (2 * m) cardAnc) :
    dfmsCoherentStep U (embedRealOracleState ψ) =
      embedRealOracleState (fun H => U.apply (oracleXor H (ψ H))) := by
  funext D
  unfold dfmsCoherentStep embedRealOracleState
  by_cases hTot : dfmsIsTotal m n D = true
  · simp only [hTot, ↓reduceIte]
    congr 1
    funext x y a
    (unfold dfmsCellXor; simp only [oracleXor_def])
    rw [dfmsToOracle_eq_entry m n D hTot x]
  · simp only [hTot, Bool.false_eq_true, ↓reduceIte]
    have hz : dfmsCellXor D (QVec.zero n (2 * m) cardAnc) = QVec.zero n (2 * m) cardAnc := by
      funext x y a
      (unfold dfmsCellXor; simp only [QVec.zero_def])
      cases dfmsEntry n D x <;> rfl
    rw [hz, ScaledUnitary.apply_zero]

/-- Scaled isometry of `dfmsDecompressState` on joint `DfmsState` vectors. -/
theorem dfmsDecompressState_norm {m n cardAnc : Nat} (ψ : DfmsState m n cardAnc) :
    dfmsTableSum m n (fun D => QVec.stateNormSq (dfmsDecompressState ψ D)) =
      4 ^ (2 * m * n) * dfmsTableSum m n (fun D => QVec.stateNormSq (ψ D)) := by
  (simp only [QVec.stateNormSq_def, QVec.queryWeight_def]; unfold dfmsDecompressState)
  simp only [dfmsTableSum_qsum, dfmsDecompress_norm, qsum_mul_left]

/-- Exact state correspondence between the `⊥`-initialized DFMS compressed-oracle runtime
    `dfmsAdvStateAt m A t ht` and the coherent QROM execution `advStateAt A H t ht` for arbitrary
    `2m`-bit digests (`m = 128 -> w = 256`!). -/
theorem dfmsAdvStateAt_eq (m : Nat) {n cardAnc Q : Nat} (A : QuantumAdv n (2 * m) cardAnc Q) :
    ∀ t (ht : t ≤ Q),
      doubleDfmsState (3 * m * n) (dfmsAdvStateAt m A t ht) =
        doubleDfmsState (4 * m * n * t)
          (dfmsDecompressState (embedRealOracleState (fun H => advStateAt A H t ht)))
  | 0, _ => by
    have hBase : dfmsDecompressState (dfmsInitState (m := m) A.init) =
        doubleDfmsState (m * n) (embedRealOracleState (fun _ => A.init)) := by
      funext D x y a
      (unfold dfmsDecompressState dfmsInitState doubleDfmsState embedRealOracleState; simp only [qvecDoublePow_def, QVec.zero_def])
      have hCond : (fun D' => (if dfmsIsAllBot m n D' = true then A.init else fun _ _ _ => GaussInt.zero) x y a) =
          (fun D' => if dfmsIsAllBot m n D' = true then A.init x y a else GaussInt.zero) := by
        funext D'; cases dfmsIsAllBot m n D' <;> rfl
      rw [hCond, dfmsDecompress_allBot]
      cases dfmsIsTotal m n D
      · simp [gaussDoublePow_zero]
      · simp
    have hApp := congrArg dfmsDecompressState hBase
    rw [dfmsDecompressState_square, dfmsDecompressState_double] at hApp
    have hSplit : 4 * m * n = m * n + 3 * m * n := by
      calc 4 * m * n
        _ = (1 + 3) * (m * n) := by rw [Nat.mul_assoc]
        _ = m * n + 3 * m * n := by rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc]
    rw [hSplit, ← doubleDfmsState_add] at hApp
    have hInit : (fun H : Fin n → BitVec (2 * m) => advStateAt A H 0 (Nat.zero_le Q)) =
        (fun _ => A.init) := by
      funext H; exact advStateAt_zero A H _
    show doubleDfmsState (3 * m * n) (dfmsInitState A.init) =
      doubleDfmsState (4 * m * n * 0)
        (dfmsDecompressState (embedRealOracleState (fun H => advStateAt A H 0 (Nat.zero_le Q))))
    rw [hInit, Nat.mul_zero, doubleDfmsState_zero]
    exact doubleDfmsState_inj (m * n) hApp
  | t + 1, ht => by
    have ih := dfmsAdvStateAt_eq m A t (Nat.le_of_succ_le ht)
    unfold dfmsAdvStateAt dfmsOracleStep
    have hStep : doubleDfmsState (3 * m * n)
        (dfmsDecompressState (dfmsCoherentStep (A.steps ⟨t, ht⟩)
          (dfmsDecompressState (dfmsAdvStateAt m A t (Nat.le_of_succ_le ht))))) =
      dfmsDecompressState (dfmsCoherentStep (A.steps ⟨t, ht⟩)
        (dfmsDecompressState (doubleDfmsState (3 * m * n)
          (dfmsAdvStateAt m A t (Nat.le_of_succ_le ht))))) := by
      rw [dfmsDecompressState_double, dfmsCoherentStep_double, dfmsDecompressState_double]
    rw [hStep, ih, dfmsDecompressState_double, dfmsDecompressState_square, doubleDfmsState_add,
      dfmsCoherentStep_double, dfmsCoherentStep_embedReal, dfmsDecompressState_double]
    have hExp : 4 * m * n * t + 4 * m * n = 4 * m * n * (t + 1) := by rw [Nat.mul_succ]
    rw [hExp]
    simp only [advStateAt_succ]

/-- Decoding the final `dfmsAdvStateAt m A Q _` register recovers the exact coherent `2m`-bit
    random-oracle execution (`0` amplitude on partial tables, `2^(4*m*n*Q + m*n)` scale on total tables). -/
theorem dfmsAdvStateAt_decode (m : Nat) {n cardAnc Q : Nat}
    (A : QuantumAdv n (2 * m) cardAnc Q) :
    dfmsDecompressState (dfmsAdvStateAt m A Q (Nat.le_refl Q)) =
      doubleDfmsState (4 * m * n * Q + m * n)
        (embedRealOracleState (fun H => runQuantumAdv A H)) := by
  simp only [runQuantumAdv_def]
  have hEq := congrArg dfmsDecompressState (dfmsAdvStateAt_eq m A Q (Nat.le_refl Q))
  rw [dfmsDecompressState_double (3 * m * n), dfmsDecompressState_double (4 * m * n * Q),
    dfmsDecompressState_square, doubleDfmsState_add] at hEq
  have h4 : 4 * m * n = 3 * m * n + m * n := by
    calc 4 * m * n
      _ = (3 + 1) * (m * n) := by rw [Nat.mul_assoc]
      _ = 3 * m * n + m * n := by rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc]
  have hSplit : 4 * m * n * Q + 4 * m * n = 3 * m * n + (4 * m * n * Q + m * n) := by omega
  rw [hSplit, ← doubleDfmsState_add] at hEq
  exact doubleDfmsState_inj (3 * m * n) hEq

/-- Observable event mass evaluated after decoding the `DfmsTable m n` register (`only total
    tables contribute when the state lies in the real-oracle subspace`). -/
def dfmsCoherentEventMass {m n cardAnc : Nat}
    (event : (Fin n → BitVec (2 * m)) → Fin n → Bool) (ψ : DfmsState m n cardAnc) : Nat :=
  dfmsTableSum m n (fun D => QVec.queryMassOn (event (dfmsToOracle m n D)) (ψ D))

/-- **Exact `2m`-Bit (`w = 256` at `m = 128`) DFMS Compressed-Oracle Observable Equivalence
    (`dfmsAdv_event_eq`)**:
    For EVERY `2m`-bit Boolean event of `(H, x)` (with arbitrary coherent superposition queries and
    zero intermediate measurements), the decoded DFMS `⊥`-database runtime has identical event mass
    to `uniformOracleSum (2 * m) n` up to the known oracle-independent factor `4 ^ (4*m*n*Q + m*n)`. -/
theorem dfmsAdv_event_eq (m : Nat) {n cardAnc Q : Nat}
    (A : QuantumAdv n (2 * m) cardAnc Q)
    (event : (Fin n → BitVec (2 * m)) → Fin n → Bool) :
    dfmsCoherentEventMass event (dfmsDecompressState (dfmsAdvStateAt m A Q (Nat.le_refl Q))) =
      4 ^ (4 * m * n * Q + m * n) *
        uniformOracleSum (2 * m) n (fun H => QVec.queryMassOn (event H) (runQuantumAdv A H)) := by
  rw [dfmsAdvStateAt_decode]
  unfold dfmsCoherentEventMass doubleDfmsState embedRealOracleState
  have hPoint : ∀ D : DfmsTable m n,
      QVec.queryMassOn (event (dfmsToOracle m n D))
        (qvecDoublePow (4 * m * n * Q + m * n)
          (if dfmsIsTotal m n D then runQuantumAdv A (dfmsToOracle m n D) else QVec.zero n (2 * m) cardAnc)) =
      4 ^ (4 * m * n * Q + m * n) *
        (if dfmsIsTotal m n D then
          QVec.queryMassOn (event (dfmsToOracle m n D)) (runQuantumAdv A (dfmsToOracle m n D))
        else 0) := by
    intro D
    rw [queryMassOn_doublePow]
    cases dfmsIsTotal m n D
    · simp [QVec.queryMassOn_def, QVec.queryWeight_def, QVec.zero_def, GaussInt.normSq_zero, qsum_const]
    · simp
  rw [dfmsTableSum_congr m n _ _ hPoint, dfmsTableSum_mul,
    dfmsTableSum_total_eq_uniform m n (fun H => QVec.queryMassOn (event H) (runQuantumAdv A H))]

/-- **Full `256`-Bit (`Digest256`) Authenticated `Hem` Coherent Bridge
    (`coherent_dfms_hem256_authenticated_event_eq`)**:
    Specializes `dfmsAdv_event_eq` at **`m = 128` (`2 * 128 = 256` bits!)** directly to the real
    authenticated `Hem` verifier `verifyHemOpeningBatch L slots inst decode` over `256`-bit Merkle
    digests (`MerkleAddressLayout n 256`, `MerkleOpeningSlot n 256`, `DfmsDigest256Table n`). -/
theorem coherent_dfms_hem256_authenticated_event_eq {n cardAnc Q : Nat}
    (A : QuantumAdv n 256 cardAnc Q)
    (L : MerkleAddressLayout n 256)
    (slots : List (MerkleOpeningSlot n 256))
    (inst : HemWhirInstance QuinticGoldilocks)
    (decode : Fin n → List (Option (MerkleOpeningValue 256)) → List (HemTranscriptRound QuinticGoldilocks)) :
    dfmsCoherentEventMass (m := 128) (verifyHemOpeningBatch L slots inst decode)
      (dfmsDecompressState (dfmsAdvStateAt 128 A Q (Nat.le_refl Q))) =
      4 ^ (512 * n * Q + 128 * n) *
        uniformOracleSum 256 n (fun H =>
          QVec.queryMassOn (verifyHemOpeningBatch L slots inst decode H) (runQuantumAdv A H)) := by
  exact dfmsAdv_event_eq 128 A (verifyHemOpeningBatch L slots inst decode)

private theorem dfmsDecompress_local {m cardX w cardAnc : Nat}
    (U : ScaledUnitary cardX w cardAnc) :
    ∀ (k : Nat) (ψ : DfmsTable m k → QVec cardX w cardAnc) (D : DfmsTable m k),
      U.apply (fun x y a => dfmsDecompress m k (fun D' => ψ D' x y a) D) =
        fun x y a => dfmsDecompress m k (fun D' => U.apply (ψ D') x y a) D
  | 0, _, () => rfl
  | k + 1, ψ, (c, D) => by
    have hCell : ∀ (f : Option (BitVec (2 * m)) → QVec cardX w cardAnc) (c0 : Option (BitVec (2 * m))),
        U.apply (fun x y a => dfmsCellDecompress m (fun c' => f c' x y a) c0) =
          fun x y a => dfmsCellDecompress m (fun c' => U.apply (f c') x y a) c0 := by
      intro f c0
      have hBv : ∀ (h : BitVec (2 * m) → QVec cardX w cardAnc),
          U.apply (fun x y a => bvGaussSum (2 * m) (fun z => h z x y a)) =
            fun x y a => bvGaussSum (2 * m) (fun z => U.apply (h z) x y a) := by
        intro h
        have hFin : ∀ (N : Nat) (q : Fin N → QVec cardX w cardAnc),
            U.apply (fun x y a => ⟨intSum N (fun i => (q i x y a).re), intSum N (fun i => (q i x y a).im)⟩) =
              fun x y a => ⟨intSum N (fun i => (U.apply (q i) x y a).re), intSum N (fun i => (U.apply (q i) x y a).im)⟩ := by
          intro N
          induction N with
          | zero =>
            intro _
            have hz : (fun (_ : Fin cardX) (_ : Fin (2 ^ w)) (_ : Fin cardAnc) =>
                (⟨0, 0⟩ : GaussInt)) = QVec.zero cardX w cardAnc := by
              rw [QVec.zero_def, GaussInt.zero_def]
            show U.apply (fun _ _ _ => (⟨0, 0⟩ : GaussInt)) = fun _ _ _ => (⟨0, 0⟩ : GaussInt)
            rw [hz]
            exact ScaledUnitary.apply_zero U
          | succ N ih =>
            intro q
            have hEq : (fun x y a => (⟨intSum (N + 1) (fun i => (q i x y a).re),
                  intSum (N + 1) (fun i => (q i x y a).im)⟩ : GaussInt)) =
                QVec.add (q ⟨0, Nat.zero_lt_succ N⟩)
                  (fun x y a => ⟨intSum N (fun i => (q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ x y a).re),
                                 intSum N (fun i => (q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ x y a).im)⟩) := by
              rw [QVec.add_def]; funext x y a; rw [GaussInt.add_def]; rfl
            refine (congrArg U.apply hEq).trans ?_
            rw [U.map_add, ih, QVec.add_def]
            funext x y a
            rw [GaussInt.add_def]
            rfl
        exact hFin (2 ^ (2 * m)) (fun i => h (BitVec.ofFin i))
      cases c0 with
      | none =>
        have hEq : (fun x y a => dfmsCellDecompress m (fun c' => f c' x y a) none) =
            qvecDoublePow m (fun x y a => bvGaussSum (2 * m) (fun z => f (some z) x y a)) := by
          rw [qvecDoublePow_def]; rfl
        refine (congrArg U.apply hEq).trans ?_
        rw [U.map_doublePow, hBv, qvecDoublePow_def]
        rfl
      | some y0 =>
        have hEq : (fun x y a => dfmsCellDecompress m (fun c' => f c' x y a) (some y0)) =
            QVec.add
              (QVec.sub (qvecDoublePow (2 * m) (f (some y0)))
                (fun x y a => bvGaussSum (2 * m) (fun z => f (some z) x y a)))
              (qvecDoublePow m (f none)) := by
          simp only [QVec.add_def, QVec.sub_def, qvecDoublePow_def]; rfl
        refine (congrArg U.apply hEq).trans ?_
        rw [U.map_add, U.map_sub, U.map_doublePow, U.map_doublePow, hBv]
        simp only [QVec.add_def, QVec.sub_def, qvecDoublePow_def]
        rfl
    unfold dfmsDecompress
    rw [hCell (fun c' x y a => dfmsDecompress m k (fun D' => ψ (c', D') x y a) D) c]
    congr 1; funext x; congr 1; funext y; congr 1; funext a
    congr 1; funext c'
    dsimp only
    exact congrArg (fun v => v x y a) (dfmsDecompress_local U k (fun D' => ψ (c', D')) D)

private theorem dfms_mux_zero_of_fiber_zero (m : Nat) :
    ∀ (n : Nat) (g : DfmsTable m n → Fin (2 ^ (2 * m)) → GaussInt)
      (D : DfmsTable m n) (x : Fin n) (y : Fin (2 ^ (2 * m))),
      (∀ (c' : Option (BitVec (2 * m))) (y' : Fin (2 ^ (2 * m))),
        g (dfmsUpdateAt n D x c') y' = GaussInt.zero) →
      dfmsDecompress m n (fun D' =>
        match dfmsEntry n D' x with
        | none => dfmsDecompress m n (fun D'' => g D'' y) D'
        | some v => dfmsDecompress m n (fun D'' => g D'' (xorFin y v)) D') D = GaussInt.zero
  | 0, _, _, x, _, _ => Fin.elim0 x
  | n + 1, g, (c, D), x, y, hZero => by
    revert hZero
    refine Fin.cases ?_ (fun j => ?_) x
    · intro hZero
      change dfmsCellDecompress m (fun c' =>
          dfmsDecompress m n (fun D' =>
            match dfmsEntry (n + 1) (c', D') ⟨0, Nat.zero_lt_succ n⟩ with
            | none => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') y) D') none
            | some v => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') (xorFin y v)) D') (some v)) D) c =
        GaussInt.zero
      have hOuter : (fun c' : Option (BitVec (2 * m)) =>
          dfmsDecompress m n (fun D' =>
            match dfmsEntry (n + 1) (c', D') ⟨0, Nat.zero_lt_succ n⟩ with
            | none => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') y) D') none
            | some v => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') (xorFin y v)) D') (some v)) D) =
          (fun _ => GaussInt.zero) := by
        funext c'
        cases c' with
        | none =>
          simp only [dfmsEntry]
          have hComm : (fun D' => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') y) D') none) =
              dfmsDecompress m n (fun D'' => dfmsCellDecompress m (fun c'' => g (c'', D'') y) none) := by
            funext D'
            exact dfmsCellDecompress_comm_decompress m n (fun c'' D'' => g (c'', D'') y) none D'
          rw [hComm, dfmsDecompress_square]
          have hZ : (fun c'' => g (c'', D) y) = (fun _ => GaussInt.zero) := by
            funext c''; exact hZero c'' y
          rw [hZ, dfmsCellDecompress_zero, gaussDoublePow_zero]
        | some v =>
          simp only [dfmsEntry]
          have hComm : (fun D' => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') (xorFin y v)) D') (some v)) =
              dfmsDecompress m n (fun D'' => dfmsCellDecompress m (fun c'' => g (c'', D'') (xorFin y v)) (some v)) := by
            funext D'
            exact dfmsCellDecompress_comm_decompress m n (fun c'' D'' => g (c'', D'') (xorFin y v)) (some v) D'
          rw [hComm, dfmsDecompress_square]
          have hZ : (fun c'' => g (c'', D) (xorFin y v)) = (fun _ => GaussInt.zero) := by
            funext c''; exact hZero c'' (xorFin y v)
          rw [hZ, dfmsCellDecompress_zero, gaussDoublePow_zero]
      rw [hOuter, dfmsCellDecompress_zero]
    · intro hZero
      change dfmsCellDecompress m (fun c' =>
          dfmsDecompress m n (fun D' =>
            match dfmsEntry (n + 1) (c', D') j.succ with
            | none => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') y) D') c'
            | some v => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') (xorFin y v)) D') c') D) c =
        GaussInt.zero
      have hPull : (fun c' : Option (BitVec (2 * m)) =>
          dfmsDecompress m n (fun D' =>
            match dfmsEntry (n + 1) (c', D') j.succ with
            | none => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') y) D') c'
            | some v => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') (xorFin y v)) D') c') D) =
          dfmsCellDecompress m (fun c'' =>
            dfmsDecompress m n (fun D' =>
              match dfmsEntry n D' j with
              | none => dfmsDecompress m n (fun D'' => g (c'', D'') y) D'
              | some v => dfmsDecompress m n (fun D'' => g (c'', D'') (xorFin y v)) D') D) := by
        funext c'
        have hStep : (fun D' =>
            match dfmsEntry (n + 1) (c', D') j.succ with
            | none => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') y) D') c'
            | some v => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') (xorFin y v)) D') c') =
          (fun D' => dfmsCellDecompress m (fun c'' =>
            match dfmsEntry n D' j with
            | none => dfmsDecompress m n (fun D'' => g (c'', D'') y) D'
            | some v => dfmsDecompress m n (fun D'' => g (c'', D'') (xorFin y v)) D') c') := by
          funext D'
          change (match dfmsEntry n D' j with
            | none => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') y) D') c'
            | some v => dfmsCellDecompress m (fun c'' => dfmsDecompress m n (fun D'' => g (c'', D'') (xorFin y v)) D') c') = _
          cases dfmsEntry n D' j <;> rfl
        rw [hStep]
        exact (dfmsCellDecompress_comm_decompress m n _ c' D).symm
      rw [hPull, dfmsCellDecompress_square]
      have hTailZero : dfmsDecompress m n (fun D' =>
          match dfmsEntry n D' j with
          | none => dfmsDecompress m n (fun D'' => g (c, D'') y) D'
          | some v => dfmsDecompress m n (fun D'' => g (c, D'') (xorFin y v)) D') D = GaussInt.zero :=
        dfms_mux_zero_of_fiber_zero m n (fun D'' y' => g (c, D'') y') D j y
          (fun c' y' => hZero c' y')
      rw [hTailZero, gaussDoublePow_zero]

/-- **Genuine `2m`-Bit (`w = 256` at `m = 128`) DFMS `⊥`-Database Sparsity Theorem
    (`dfms_runtime_support`)**:
    After `t ≤ Q` coherent `2m`-bit queries (`QuantumAdv n (2 * m) cardAnc Q`), the compressed
    database state `dfmsAdvStateAt m A t ht D` has **identically zero amplitude** on every database
    `D : DfmsTable m n` with `t < dfmsRecordedCount n D` non-`⊥` recorded digests! -/
theorem dfms_runtime_support (m : Nat) {n cardAnc Q : Nat}
    (A : QuantumAdv n (2 * m) cardAnc Q) :
    ∀ (t : Nat) (ht : t ≤ Q) (D : DfmsTable m n),
      t < dfmsRecordedCount n D →
      dfmsAdvStateAt m A t ht D = QVec.zero n (2 * m) cardAnc
  | 0, _, D, hCount => by
    unfold dfmsAdvStateAt dfmsInitState
    have hNotBot : dfmsIsAllBot m n D = false := by
      clear A
      induction n with
      | zero => simp [dfmsRecordedCount] at hCount
      | succ n ih =>
        obtain ⟨c, rest⟩ := D
        cases c with
        | none =>
          simp only [dfmsRecordedCount, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            Nat.zero_add] at hCount
          simp only [dfmsIsAllBot, Option.isNone_none, Bool.true_and, ih rest hCount]
        | some _ =>
          simp [dfmsIsAllBot]
    simp only [hNotBot, Bool.false_eq_true, ↓reduceIte]
  | t + 1, ht, D, hCount => by
    let φ := dfmsAdvStateAt m A t (Nat.le_of_succ_le ht)
    have hPreZero : dfmsDecompressState (fun D' => dfmsCellXor D' (dfmsDecompressState φ D')) D =
        QVec.zero n (2 * m) cardAnc := by
      funext x y a
      rw [QVec.zero_apply]
      apply dfms_mux_zero_of_fiber_zero m n (fun D'' y' => φ D'' x y' a) D x y
      intro c' y'
      have hUpd := dfmsRecordedCount_updateAt_le n D x c'
      have hZeroVec := dfms_runtime_support m A t (Nat.le_of_succ_le ht)
        (dfmsUpdateAt n D x c') (by omega)
      exact (congrArg (fun v => v x y' a) hZeroVec).trans (QVec.zero_apply _ _ _ x y' a)
    unfold dfmsAdvStateAt dfmsOracleStep dfmsCoherentStep
    have hLoc : dfmsDecompressState (fun D' => (A.steps ⟨t, ht⟩).apply (dfmsCellXor D' (dfmsDecompressState φ D'))) D =
        (A.steps ⟨t, ht⟩).apply (dfmsDecompressState (fun D' => dfmsCellXor D' (dfmsDecompressState φ D')) D) := by
      exact (dfmsDecompress_local (A.steps ⟨t, ht⟩) n
        (fun D' => dfmsCellXor D' (dfmsDecompressState φ D')) D).symm
    change dfmsDecompressState (fun D' => (A.steps ⟨t, ht⟩).apply (dfmsCellXor D' (dfmsDecompressState φ D'))) D = _
    rw [hLoc, hPreZero, ScaledUnitary.apply_zero]

/-- Terminal measurement of `dfmsRecordedCount` on `DfmsTable m n` (`m = 128 -> w = 256`!) has
    **identically zero mass** on databases with `> Q` recorded non-`⊥` digests. -/
theorem dfms_database_overflow_mass_zero (m : Nat) {n cardAnc Q : Nat}
    (A : QuantumAdv n (2 * m) cardAnc Q) :
    dfmsTableSum m n (fun D =>
      if Q < dfmsRecordedCount n D then
        QVec.stateNormSq (dfmsAdvStateAt m A Q (Nat.le_refl Q) D)
      else 0) = 0 := by
  have hPoint : ∀ D : DfmsTable m n,
      (if Q < dfmsRecordedCount n D then
        QVec.stateNormSq (dfmsAdvStateAt m A Q (Nat.le_refl Q) D) else 0) = 0 := by
    intro D
    by_cases hOver : Q < dfmsRecordedCount n D
    · rw [ite_eq_left hOver, dfms_runtime_support m A Q (Nat.le_refl Q) D hOver]
      simp [QVec.stateNormSq_def, QVec.queryWeight_def, QVec.zero_def, GaussInt.normSq_zero, qsum_const]
    · exact ite_eq_right hOver
  rw [dfmsTableSum_congr m n _ _ hPoint, dfmsTableSum_zero]

/-- **Multi-Salt / Multi-Domain `2m`-Bit (`w = 256`) DFMS Budget Conservation
    (`dfms_salted_domain_budget_zero_of_overflow`)**:
    Across disjoint per-commitment Canopy salts or Fiat–Shamir / Merkle domains
    (`domainOf : Fin n → Fin cardDom`), any `2m`-bit `QuantumAdv` (`m = 128 -> w = 256`) has
    **zero amplitude** on databases whose summed non-`⊥` recorded digests exceed `t ≤ Q`! -/
theorem dfms_salted_domain_budget_zero_of_overflow (m : Nat) {n cardDom cardAnc Q : Nat}
    (A : QuantumAdv n (2 * m) cardAnc Q)
    (domainOf : Fin n → Fin cardDom)
    (t : Nat) (ht : t ≤ Q) (D : DfmsTable m n)
    (hOverflow : t < qsum cardDom (fun dom => dfmsDomainRecordedCount n domainOf dom D)) :
    dfmsAdvStateAt m A t ht D = QVec.zero n (2 * m) cardAnc := by
  rw [dfmsDomainRecordedCount_sum_eq n domainOf D] at hOverflow
  exact dfms_runtime_support m A t ht D hOverflow

/-- Projective online-extraction filter keeping compressed `DfmsTable m n` branches satisfying `P`
    (e.g., collision-free / uniquely extractable salted Merkle trees) and zeroing `¬ P`. -/
def projectDfmsPred {m n cardAnc : Nat} (P : DfmsTable m n → Bool)
    (ψ : DfmsState m n cardAnc) : DfmsState m n cardAnc :=
  fun D => if P D then ψ D else QVec.zero n (2 * m) cardAnc

/-- **Quantitative DFMS Projective Online-Extraction Disturbance Bound
    (`dfms_projective_extraction_disturbance_bound`)**:
    For ANY compressed database state `ψ : DfmsState m n cardAnc`, ANY database relation
    `P : DfmsTable m n → Bool` (e.g., collision-free salted Canopy extraction), and ANY verifier
    event `event` (including `verifyHemOpeningBatch` at `w = 256`), the undisturbed coherent
    acceptance mass after decompression is bounded by twice the projected/extracted branch's
    acceptance mass plus `2 * 4^(2*m*n)` times the pre-decompression `¬ P` bad-database mass! -/
theorem dfms_projective_extraction_disturbance_bound {m n cardAnc : Nat}
    (P : DfmsTable m n → Bool)
    (event : (Fin n → BitVec (2 * m)) → Fin n → Bool)
    (ψ : DfmsState m n cardAnc) :
    dfmsCoherentEventMass event (dfmsDecompressState ψ) ≤
      2 * dfmsCoherentEventMass event (dfmsDecompressState (projectDfmsPred P ψ)) +
      2 * 4 ^ (2 * m * n) *
        dfmsTableSum m n (fun D => if P D then 0 else QVec.stateNormSq (ψ D)) := by
  let ψGood := projectDfmsPred P ψ
  let ψBad : DfmsState m n cardAnc := fun D => if P D then QVec.zero n (2 * m) cardAnc else ψ D
  have hSplit : ∀ D x y a,
      dfmsDecompressState ψ D x y a =
        (dfmsDecompressState ψGood D x y a).add (dfmsDecompressState ψBad D x y a) := by
    intro D x y a
    unfold dfmsDecompressState
    rw [← dfmsDecompress_add]
    apply congrFun
    apply dfmsDecompress_congr m n
    intro D'
    unfold ψGood ψBad projectDfmsPred
    simp only [QVec.zero_def]
    cases P D' <;> apply GaussInt.ext <;> simp [GaussInt.add_def, GaussInt.zero_def]
  have hPerTable : ∀ D : DfmsTable m n,
      QVec.queryMassOn (event (dfmsToOracle m n D)) (dfmsDecompressState ψ D) ≤
        2 * QVec.queryMassOn (event (dfmsToOracle m n D)) (dfmsDecompressState ψGood D) +
        2 * QVec.stateNormSq (dfmsDecompressState ψBad D) := by
    intro D
    simp only [QVec.queryMassOn_def, QVec.stateNormSq_def]
    rw [← qsum_mul_left, ← qsum_mul_left, ← qsum_add]
    apply qsum_le_qsum
    intro x
    cases event (dfmsToOracle m n D) x
    · simp
    · simp only [↓reduceIte]
      simp only [QVec.queryWeight_def]
      rw [← qsum_mul_left, ← qsum_mul_left, ← qsum_add]
      apply qsum_le_qsum
      intro y
      rw [← qsum_mul_left, ← qsum_mul_left, ← qsum_add]
      apply qsum_le_qsum
      intro a
      rw [hSplit D x y a]
      exact GaussInt.normSq_add_le _ _
  have hSumLe : ∀ (k : Nat) (f g : DfmsTable m k → Nat),
      (∀ D, f D ≤ g D) → dfmsTableSum m k f ≤ dfmsTableSum m k g := by
    intro k
    induction k with
    | zero => intro f g h; exact h ()
    | succ k ih =>
      intro f g h
      unfold dfmsTableSum dfmsCellSum
      dsimp only
      have hNone := ih _ _ (fun D => h (none, D))
      have hSome := qsum_le_qsum (fun j => ih _ _ (fun D => h (some (BitVec.ofFin j), D)))
      omega
  have hMain := hSumLe n _ _ hPerTable
  rw [dfmsTableSum_add, dfmsTableSum_mul, dfmsTableSum_mul, dfmsDecompressState_norm] at hMain
  have hBadNorm : ∀ D : DfmsTable m n,
      QVec.stateNormSq (ψBad D) = if P D then 0 else QVec.stateNormSq (ψ D) := by
    intro D
    unfold ψBad
    cases P D
    · simp
    · simp [QVec.stateNormSq_def, QVec.queryWeight_def, QVec.zero_def, GaussInt.normSq_zero, qsum_const]
  rw [dfmsTableSum_congr m n _ _ hBadNorm] at hMain
  simpa [dfmsCoherentEventMass, Nat.mul_assoc] using hMain

/-- **`256`-Bit `Hem` Online-Extraction Disturbance Corollary (`dfms_hem256_online_extraction_disturbance_bound`)**:
    Instantiates `dfms_projective_extraction_disturbance_bound` + `coherent_dfms_hem256_authenticated_event_eq`
    at `m = 128` (`w = 256` `Digest256`!) on `verifyHemOpeningBatch`: coherent 256-bit `Hem`
    acceptance mass is bounded directly by twice the `P`-projected compressed-database acceptance
    mass plus `2 * 4^(256 * n)` times the bad compressed-database mass (where every populated `D`
    additionally obeys `dfmsRecordedCount n D ≤ Q`!). -/
theorem dfms_hem256_online_extraction_disturbance_bound {n cardAnc Q : Nat}
    (A : QuantumAdv n 256 cardAnc Q)
    (P : DfmsDigest256Table n → Bool)
    (L : MerkleAddressLayout n 256)
    (slots : List (MerkleOpeningSlot n 256))
    (inst : HemWhirInstance QuinticGoldilocks)
    (decode : Fin n → List (Option (MerkleOpeningValue 256)) → List (HemTranscriptRound QuinticGoldilocks)) :
    4 ^ (512 * n * Q + 128 * n) *
        uniformOracleSum 256 n (fun H =>
          QVec.queryMassOn (verifyHemOpeningBatch L slots inst decode H) (runQuantumAdv A H)) ≤
      2 * dfmsCoherentEventMass (m := 128) (verifyHemOpeningBatch L slots inst decode)
        (dfmsDecompressState (projectDfmsPred P (dfmsAdvStateAt 128 A Q (Nat.le_refl Q)))) +
      2 * 4 ^ (256 * n) *
        dfmsTableSum 128 n (fun D =>
          if P D then 0
          else if dfmsRecordedCount n D ≤ Q then
            QVec.stateNormSq (dfmsAdvStateAt 128 A Q (Nat.le_refl Q) D)
          else 0) := by
  rw [← coherent_dfms_hem256_authenticated_event_eq A L slots inst decode]
  have hBase := dfms_projective_extraction_disturbance_bound P
    (verifyHemOpeningBatch L slots inst decode) (dfmsAdvStateAt 128 A Q (Nat.le_refl Q))
  have hTrunc : ∀ D : DfmsDigest256Table n,
      (if P D then 0 else QVec.stateNormSq (dfmsAdvStateAt 128 A Q (Nat.le_refl Q) D)) =
      (if P D then 0
       else if dfmsRecordedCount n D ≤ Q then
         QVec.stateNormSq (dfmsAdvStateAt 128 A Q (Nat.le_refl Q) D)
       else 0) := by
    intro D
    cases P D
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hLe : dfmsRecordedCount n D ≤ Q
      · simp [hLe]
      · have hGt : Q < dfmsRecordedCount n D := by omega
        rw [ite_eq_right hLe, dfms_runtime_support 128 A Q (Nat.le_refl Q) D hGt]
        simp only [QVec.stateNormSq_def, QVec.queryWeight_def, QVec.zero_def, GaussInt.normSq_zero, qsum_const,
          Nat.mul_zero]
    · simp
  have h256 : 2 * 128 * n = 256 * n := by omega
  rw [dfmsTableSum_congr 128 n _ _ hTrunc, h256] at hBase
  exact hBase

/- The executed `w = 2` runtime witness `dfms_w2_coherent_runtime_witness` and the raw-measurement tooth
   `tooth_dfms_w2_raw_database_measurement_disturbs` (kernel runs of `dfmsAdvStateAt` on a concrete
   Hadamard adversary) are in `Qsag.Tests.QromCoherentOracleTests`. -/

/-! ## §2. Adaptive State-Restoration Games & Coherent Joint `(PoW × Challenge)` QROM Reduction -/

/-! ### §2.1 Classical Adaptive State-Restoration Game (`[BCS16; CY24]`) -/

/-- Adaptive `T`-step state-restoration prover over transcript states `State`, prover moves `Move`,
    and `cardChal`-ary verifier challenges. At each step the prover selects an index into the list
    of previously reached states (`restoredIdx`), submits a `Move`, and receives a uniform challenge,
    appending the resulting state to the reachable history. -/
inductive StateRestorationTree (Move : Type) (cardChal : Nat) : Nat → Type where
  | halt {T : Nat} : StateRestorationTree Move cardChal T
  | restore {T : Nat} (restoredIdx : Nat) (mv : Move)
      (next : Fin cardChal → StateRestorationTree Move cardChal T) :
      StateRestorationTree Move cardChal (T + 1)

/-- Count of challenge tapes (out of `cardChal ^ T`) on which `tree` ever reaches a state with
    `isLive s = true`, starting from `history`. -/
def srWinTapeCount {State Move : Type} {cardChal : Nat}
    (step : State → Move → Fin cardChal → State)
    (isLive : State → Bool) :
    {T : Nat} → StateRestorationTree Move cardChal T → List State → Nat
  | T, .halt, history =>
    if history.any isLive then cardChal ^ T else 0
  | _, .restore idx mv next, history =>
    qsum cardChal (fun c =>
      match history[idx]? with
      | none => srWinTapeCount step isLive (next c) history
      | some st => srWinTapeCount step isLive (next c) (step st mv c :: history))

private theorem srWinTapeCount_all_live {State Move : Type} {cardChal : Nat}
    (step : State → Move → Fin cardChal → State)
    (isLive : State → Bool) :
    ∀ {T : Nat} (tree : StateRestorationTree Move cardChal T) (history : List State),
      srWinTapeCount step isLive tree history ≤ cardChal ^ T
  | T, .halt, history => by
    unfold srWinTapeCount
    split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  | T + 1, .restore idx mv next, history => by
    unfold srWinTapeCount
    have hEach : ∀ c : Fin cardChal,
        (match history[idx]? with
         | none => srWinTapeCount step isLive (next c) history
         | some st => srWinTapeCount step isLive (next c) (step st mv c :: history)) ≤
        cardChal ^ T := by
      intro c
      cases history[idx]? with
      | none => exact srWinTapeCount_all_live step isLive (next c) history
      | some st => exact srWinTapeCount_all_live step isLive (next c) (step st mv c :: history)
    have hSum := qsum_le_qsum hEach
    rw [qsum_const] at hSum
    have hPowEq : cardChal * cardChal ^ T = cardChal ^ (T + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    exact hPowEq ▸ hSum

/-- **Constructive Adaptive State-Restoration Soundness (`classical_state_restoration_tree_bound`)**:
    Starting from any all-doomed state history (`history.any isLive = false`), if every doomed state
    `st` and prover move `mv` transitions to a live state on at most `badPerRound` out of `cardChal`
    challenges, then ANY `T`-step adaptive state-restoration tree succeeds on at most
    `T * badPerRound * cardChal ^ T` divided by `cardChal` challenge tapes:
    `srWinTapeCount * cardChal ≤ T * badPerRound * cardChal ^ T`! -/
theorem classical_state_restoration_tree_bound {State Move : Type} {cardChal : Nat}
    (step : State → Move → Fin cardChal → State)
    (isLive : State → Bool)
    (badPerRound : Nat)
    (hRbr : ∀ (st : State) (mv : Move), isLive st = false →
      qsum cardChal (fun c => if isLive (step st mv c) = true then 1 else 0) ≤ badPerRound) :
    ∀ {T : Nat} (tree : StateRestorationTree Move cardChal T) (history : List State),
      history.any isLive = false →
      srWinTapeCount step isLive tree history * cardChal ≤
        T * badPerRound * cardChal ^ T
  | T, .halt, history, hDoomed => by
    simp only [srWinTapeCount, hDoomed, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.zero_le]
  | T + 1, .restore idx mv next, history, hDoomed => by
    unfold srWinTapeCount
    cases hLookup : history[idx]? with
    | none =>
      have hSub : ∀ c : Fin cardChal,
          srWinTapeCount step isLive (next c) history * cardChal ≤
            T * badPerRound * cardChal ^ T :=
        fun c => classical_state_restoration_tree_bound step isLive badPerRound hRbr (next c) history hDoomed
      rw [← qsum_mul_right]
      have hSum := qsum_le_qsum hSub
      rw [qsum_const] at hSum
      calc qsum cardChal (fun c => srWinTapeCount step isLive (next c) history * cardChal)
          ≤ cardChal * (T * badPerRound * cardChal ^ T) := hSum
        _ = T * badPerRound * (cardChal ^ T * cardChal) := by
          rw [Nat.mul_comm cardChal _, Nat.mul_assoc]
        _ ≤ (T + 1) * badPerRound * cardChal ^ (T + 1) := by
          rw [Nat.pow_succ]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ T))
    | some st =>
      have hStDoomed : isLive st = false := by
        cases hL : isLive st
        · rfl
        · exfalso
          have hMem : st ∈ history := List.mem_of_getElem? hLookup
          have hAny : history.any isLive = true := List.any_eq_true.mpr ⟨st, hMem, hL⟩
          rw [hDoomed] at hAny
          exact Bool.noConfusion hAny
      have hPerC : ∀ c : Fin cardChal,
          srWinTapeCount step isLive (next c) (step st mv c :: history) * cardChal ≤
            (if isLive (step st mv c) = true then 1 else 0) * cardChal ^ (T + 1) +
              T * badPerRound * cardChal ^ T := by
        intro c
        cases hFlip : isLive (step st mv c)
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
          have hNextDoomed : (step st mv c :: history).any isLive = false := by
            simp only [List.any_cons, hFlip, hDoomed, Bool.or_self]
          exact classical_state_restoration_tree_bound step isLive badPerRound hRbr
            (next c) (step st mv c :: history) hNextDoomed
        · simp only [↓reduceIte, Nat.one_mul]
          have hCap := Nat.mul_le_mul_right cardChal
            (srWinTapeCount_all_live step isLive (next c) (step st mv c :: history))
          rw [← Nat.pow_succ] at hCap
          exact Nat.le_trans hCap (Nat.le_add_right _ _)
      have hSum := qsum_le_qsum hPerC
      rw [qsum_mul_right, qsum_add, qsum_mul_right, qsum_const] at hSum
      have hFlipSum := Nat.mul_le_mul_right (cardChal ^ (T + 1)) (hRbr st mv hStDoomed)
      have hTailEq : cardChal * (T * badPerRound * cardChal ^ T) =
          T * badPerRound * cardChal ^ (T + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm cardChal _, Nat.mul_assoc]
      calc qsum cardChal (fun c =>
              srWinTapeCount step isLive (next c) (step st mv c :: history)) * cardChal
          ≤ qsum cardChal (fun c => if isLive (step st mv c) = true then 1 else 0) *
              cardChal ^ (T + 1) + cardChal * (T * badPerRound * cardChal ^ T) := hSum
        _ ≤ badPerRound * cardChal ^ (T + 1) + T * badPerRound * cardChal ^ (T + 1) := by
          rw [hTailEq]
          exact Nat.add_le_add_right hFlipSum _
        _ = (T + 1) * badPerRound * cardChal ^ (T + 1) := by
          rw [Nat.add_comm T 1, Nat.add_mul, Nat.one_mul, Nat.add_mul]

/-- Rational `RatBound` corollary of `classical_state_restoration_tree_bound` from a doomed initial
    state `initState`: escape probability is at most `(T * badPerRound) / cardChal`. -/
theorem classical_state_restoration_soundness {State Move : Type} {cardChalPred T : Nat}
    (step : State → Move → Fin (cardChalPred + 1) → State)
    (isLive : State → Bool)
    (initState : State) (hInitDoomed : isLive initState = false)
    (badPerRound : Nat)
    (hRbr : ∀ (st : State) (mv : Move), isLive st = false →
      qsum (cardChalPred + 1) (fun c => if isLive (step st mv c) = true then 1 else 0) ≤ badPerRound)
    (tree : StateRestorationTree Move (cardChalPred + 1) T) :
    RatBound.le
      ⟨srWinTapeCount step isLive tree [initState], (cardChalPred + 1) ^ T,
        Nat.pow_pos (Nat.succ_pos cardChalPred)⟩
      ⟨T * badPerRound, cardChalPred + 1, Nat.succ_pos cardChalPred⟩ := by
  have hHist : ([initState]).any isLive = false := by
    simp only [List.any_cons, List.any_nil, hInitDoomed, Bool.or_self]
  exact classical_state_restoration_tree_bound step isLive badPerRound hRbr tree [initState] hHist

/-- Under classical linear state restoration (`T * ε_RBR`), ANY `184`-bit RBR bound (such as every
    non-exhaustive stage of `sliced_stage_supported_budget`) maintains `≥ 128` bits of soundness
    all the way up to `T ≤ 2^56` classical restoration queries (`2^56 * 2^-184 = 2^-128`). -/
theorem classical_sr_sliced184_sound_at_2pow56
    (b : RatBound) (hb : atLeastBits 184 b) (T : Nat) (hT : T ≤ 2 ^ 56) :
    atLeastBits 128 (RatBound.scale T b) := by
  unfold atLeastBits RatBound.scale at *
  dsimp only at *
  have h1 : T * b.num * 2 ^ 128 ≤ 2 ^ 56 * b.num * 2 ^ 128 :=
    Nat.mul_le_mul_right (2 ^ 128) (Nat.mul_le_mul_right b.num hT)
  have hPow : 2 ^ 56 * 2 ^ 128 = 2 ^ 184 := by decide
  have hEq : 2 ^ 56 * b.num * 2 ^ 128 = b.num * 2 ^ 184 := by
    calc 2 ^ 56 * b.num * 2 ^ 128
      _ = b.num * (2 ^ 56 * 2 ^ 128) := by
            rw [Nat.mul_comm (2 ^ 56) b.num, Nat.mul_assoc]
      _ = b.num * 2 ^ 184 := by rw [hPow]
  exact Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq hEq) hb)


/-! ### §2.2 Coherent Quantum Joint `(PoW × Challenge)` RBR Reduction (`QuantumAdv`) -/

/-- Extract the low `bPow`-bit PoW digest slice from a combined `(bPow + wChal)`-bit oracle output. -/
def powSliceOut (bPow wChal : Nat) (out : BitVec (bPow + wChal)) : BitVec bPow :=
  BitVec.ofNat bPow (out.toNat % 2 ^ bPow)

/-- Extract the high `wChal`-bit Fiat–Shamir challenge slice from a combined `(bPow + wChal)`-bit
    oracle output. -/
def chalSliceOut (bPow wChal : Nat) (out : BitVec (bPow + wChal)) : BitVec wChal :=
  BitVec.ofNat wChal (out.toNat / 2 ^ bPow)

private theorem qsum_cast_nat {a b : Nat} (h : a = b) (g : Nat → Nat) :
    qsum a (fun j => g j.1) = qsum b (fun j => g j.1) := by
  cases h
  rfl

/-- **Exact Product-Slice Bad-Output Count (`jointPowChal_badCard_le`)**:
    When a verifier gate requires BOTH `powPass (powSliceOut bPow wChal out) = true` (at most
    `powGoodCard` passing `bPow`-bit tags) AND `chalBad (chalSliceOut bPow wChal out) = true`
    (at most `rbrBadCard` bad `wChal`-bit challenges), at most `powGoodCard * rbrBadCard` out of
    `2 ^ (bPow + wChal)` combined outputs satisfy both conditions simultaneously. -/
theorem jointPowChal_badCard_le (bPow wChal : Nat)
    (powPass : BitVec bPow → Bool) (chalBad : BitVec wChal → Bool)
    (powGoodCard rbrBadCard : Nat)
    (hPow : qsum (2 ^ bPow) (fun r => if powPass (BitVec.ofFin r) = true then 1 else 0) ≤ powGoodCard)
    (hChal : qsum (2 ^ wChal) (fun q => if chalBad (BitVec.ofFin q) = true then 1 else 0) ≤ rbrBadCard) :
    qsum (2 ^ (bPow + wChal)) (fun j =>
      if (powPass (powSliceOut bPow wChal (BitVec.ofFin j)) &&
          chalBad (chalSliceOut bPow wChal (BitVec.ofFin j))) = true then 1 else 0) ≤
      powGoodCard * rbrBadCard := by
  have hPowEq : 2 ^ (bPow + wChal) = 2 ^ bPow * 2 ^ wChal := Nat.pow_add 2 bPow wChal
  let g : Nat → Nat := fun k =>
    if (powPass (BitVec.ofNat bPow (k % 2 ^ bPow)) &&
        chalBad (BitVec.ofNat wChal (k / 2 ^ bPow))) = true then 1 else 0
  have hCast : qsum (2 ^ (bPow + wChal)) (fun j =>
      if (powPass (powSliceOut bPow wChal (BitVec.ofFin j)) &&
          chalBad (chalSliceOut bPow wChal (BitVec.ofFin j))) = true then 1 else 0) =
      qsum (2 ^ bPow * 2 ^ wChal) (fun j => g j.1) := by
    have hEqFn : ∀ (j : Fin (2 ^ (bPow + wChal))),
        (if (powPass (powSliceOut bPow wChal (BitVec.ofFin j)) &&
             chalBad (chalSliceOut bPow wChal (BitVec.ofFin j))) = true then 1 else 0) = g j.1 := by
      intro j
      unfold powSliceOut chalSliceOut g
      simp only [BitVec.toNat_ofFin]
    rw [qsum_congr hEqFn]
    exact qsum_cast_nat hPowEq g
  rw [hCast, qsum_mul_split (2 ^ bPow) (2 ^ wChal)]
  have hFactor : ∀ q : Fin (2 ^ wChal),
      qsum (2 ^ bPow) (fun r => g (q.1 * 2 ^ bPow + r.1)) =
        (if chalBad (BitVec.ofFin q) = true then 1 else 0) *
          qsum (2 ^ bPow) (fun r => if powPass (BitVec.ofFin r) = true then 1 else 0) := by
    intro q
    have hPos : 0 < 2 ^ bPow := Nat.two_pow_pos bPow
    have hInner : ∀ r : Fin (2 ^ bPow),
        g (q.1 * 2 ^ bPow + r.1) =
          (if chalBad (BitVec.ofFin q) = true then 1 else 0) *
            (if powPass (BitVec.ofFin r) = true then 1 else 0) := by
      intro r
      unfold g
      have hMod : (q.1 * 2 ^ bPow + r.1) % 2 ^ bPow = r.1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.2]
      have hDiv : (q.1 * 2 ^ bPow + r.1) / 2 ^ bPow = q.1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hPos, Nat.div_eq_of_lt r.2, Nat.zero_add]
      have hBvR : BitVec.ofNat bPow r.1 = BitVec.ofFin r := by
        apply BitVec.eq_of_toNat_eq
        simp
      have hBvQ : BitVec.ofNat wChal q.1 = BitVec.ofFin q := by
        apply BitVec.eq_of_toNat_eq
        simp
      rw [hMod, hDiv, hBvR, hBvQ]
      cases powPass (BitVec.ofFin r) <;> cases chalBad (BitVec.ofFin q) <;> simp
    rw [qsum_congr hInner, ← qsum_mul_left]
  rw [qsum_congr hFactor, qsum_mul_right]
  rw [Nat.mul_comm powGoodCard rbrBadCard]
  exact Nat.mul_le_mul hChal hPow

/-- Canonical `bPow`-bit all-zero proof-of-work gate (`verify_pcs_pow` in `pcs.rs`):
    passes on **exactly 1** out of `2 ^ bPow` values (`powGoodCard = 1`). -/
def canonicalZeroPowGate (bPow : Nat) (tag : BitVec bPow) : Bool :=
  decide (tag = 0#bPow)

theorem canonicalZeroPowGate_card (bPow : Nat) :
    qsum (2 ^ bPow) (fun r => if canonicalZeroPowGate bPow (BitVec.ofFin r) = true then 1 else 0) = 1 := by
  unfold canonicalZeroPowGate
  have hCongr : ∀ r : Fin (2 ^ bPow),
      (if decide (BitVec.ofFin r = 0#bPow) = true then 1 else 0) =
      (if r = ⟨0, Nat.two_pow_pos bPow⟩ then 1 else 0) := by
    intro r
    by_cases hr : r = ⟨0, Nat.two_pow_pos bPow⟩
    · subst hr; simp
    · have hBvNe : BitVec.ofFin r ≠ 0#bPow := by
        intro he
        apply hr
        apply Fin.ext
        have hNat := congrArg BitVec.toNat he
        simpa only [BitVec.toNat_ofFin, BitVec.toNat_ofNat, Nat.zero_mod] using hNat
      simp [hr, hBvNe]
  rw [qsum_congr hCongr, qsum_ite_eq]

/-- Specification of a Fiat–Shamir round equipped with an absorbed pre-squeeze `bPow`-bit PoW gate
    over `H : Fin cardX → BitVec (bPow + wChal)`. -/
structure QromJointPowRbrSpec (cardX bPow wChal : Nat) where
  proj : Fin cardX → Fin cardX
  isDoomedAt : (Fin cardX → BitVec (bPow + wChal)) → Fin cardX → Bool
  chalFlip : (Fin cardX → BitVec (bPow + wChal)) → Fin cardX → BitVec wChal → Bool
  rbrBadCard : Nat
  doomed_local : ∀ H x ch, isDoomedAt (reprogramOracle H x ch) x = isDoomedAt H x
  chalFlip_local : ∀ H x ch c, chalFlip (reprogramOracle H x ch) x c = chalFlip H x c
  rbr_bound : ∀ H x, isDoomedAt H x = true →
    qsum (2 ^ wChal) (fun q => if chalFlip H x (BitVec.ofFin q) = true then 1 else 0) ≤ rbrBadCard

/-- Post-round liveness predicate requiring BOTH `canonicalZeroPowGate` on the PoW slice AND
    `chalFlip` on the challenge slice of `H x`. -/
def QromJointPowRbrSpec.isLiveAfter {cardX bPow wChal : Nat}
    (spec : QromJointPowRbrSpec cardX bPow wChal)
    (H : Fin cardX → BitVec (bPow + wChal)) (x : Fin cardX) : Bool :=
  canonicalZeroPowGate bPow (powSliceOut bPow wChal (H x)) &&
    spec.chalFlip H x (chalSliceOut bPow wChal (H x))

/-- Every `QromJointPowRbrSpec` induces a genuine `QromRbrRound` with `badCard = spec.rbrBadCard`
    over `2 ^ (bPow + wChal)` — mechanically amplifying RBR soundness by `1 / 2 ^ bPow`! -/
def QromJointPowRbrSpec.toQromRbrRound {cardX bPow wChal : Nat}
    (spec : QromJointPowRbrSpec cardX bPow wChal)
    (H : Fin cardX → BitVec (bPow + wChal)) :
    QromRbrRound cardX (bPow + wChal) H where
  proj := spec.proj
  isDoomedAt := spec.isDoomedAt
  isLiveAfter := spec.isLiveAfter
  badCard := spec.rbrBadCard
  doomed_local := spec.doomed_local H
  flip_bound := by
    intro x hDoomed
    have hSimp : ∀ j : Fin (2 ^ (bPow + wChal)),
        spec.isLiveAfter (reprogramOracle H x (BitVec.ofFin j)) x =
          (canonicalZeroPowGate bPow (powSliceOut bPow wChal (BitVec.ofFin j)) &&
           spec.chalFlip H x (chalSliceOut bPow wChal (BitVec.ofFin j))) := by
      intro j
      unfold QromJointPowRbrSpec.isLiveAfter
      rw [spec.chalFlip_local H x (BitVec.ofFin j)]
      simp only [reprogramOracle_def, ↓reduceIte]
    have hCongr :
        qsum (2 ^ (bPow + wChal)) (fun j =>
          if spec.isLiveAfter (reprogramOracle H x (BitVec.ofFin j)) x = true then 1 else 0) =
        qsum (2 ^ (bPow + wChal)) (fun j =>
          if (canonicalZeroPowGate bPow (powSliceOut bPow wChal (BitVec.ofFin j)) &&
              spec.chalFlip H x (chalSliceOut bPow wChal (BitVec.ofFin j))) = true then 1 else 0) :=
      qsum_congr (fun j => by rw [hSimp j])
    rw [hCongr, ← Nat.one_mul spec.rbrBadCard]
    exact jointPowChal_badCard_le bPow wChal
      (canonicalZeroPowGate bPow) (spec.chalFlip H x) 1 spec.rbrBadCard
      (Nat.le_of_eq (canonicalZeroPowGate_card bPow))
      (spec.rbr_bound H x hDoomed)

/-- **Unitary Multi-Round Joint `(PoW × Challenge)` QROM Soundness Theorem
    (`qrom_joint_pow_multiRound_success_bound`)**:
    For ANY `Q`-query coherent unitary adversary `A : QuantumAdv cardX (bPow + wChal) cardAnc Q`
    and ANY `k` Fiat–Shamir rounds whose verifier checks `canonicalZeroPowGate` before squeezing
    challenges (`QromJointPowRbrSpec`), the uniform-oracle expected acceptance probability is at most
    `((2 * Q + 1)^2 * ∑_r rbrBadCard_r) / (2^bPow * 2^wChal)` — derived from unitary amplitudes and
    oracle resampling with zero hardcoded bit multiplication! -/
theorem qrom_joint_pow_multiRound_success_bound
    {cardX bPow wChal cardAnc Q k : Nat}
    (A : QuantumAdv cardX (bPow + wChal) cardAnc Q)
    (accept : (Fin cardX → BitVec (bPow + wChal)) → Fin cardX → Bool)
    (specs : Fin k → QromJointPowRbrSpec cardX bPow wChal)
    (hCover : ∀ H, QVec.queryMassOn (accept H) (runQuantumAdv A H) ≤
      qsum k (fun r => qromOrdinaryFlipMass A H (specs r).proj
        (specs r).isDoomedAt (specs r).isLiveAfter)) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum (bPow + wChal) cardX
        (fun H => QVec.queryMassOn (accept H) (runQuantumAdv A H)),
        (2 ^ (bPow + wChal)) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos (bPow + wChal)))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * qsum k (fun r => (specs r).rbrBadCard),
        2 ^ bPow * 2 ^ wChal,
        Nat.mul_pos (Nat.two_pow_pos bPow) (Nat.two_pow_pos wChal)⟩ := by
  have hMain := qrom_uniform_oracle_success_bound A accept
    (fun r H => (specs r).toQromRbrRound H)
    (fun r => (specs r).proj)
    (fun r => (specs r).isDoomedAt)
    (fun r => (specs r).isLiveAfter)
    (fun r => (specs r).rbrBadCard)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    hCover
  have hDen : 2 ^ (bPow + wChal) = 2 ^ bPow * 2 ^ wChal := Nat.pow_add 2 bPow wChal
  dsimp only [RatBound.le] at hMain ⊢
  rw [← hDen]
  exact hMain

/-- Copy of `qsum` with a body the kernel can evaluate in this module. -/
private def qsumK : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + qsumK n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private theorem qsum_eq_qsumK : ∀ (n : Nat) (f : Fin n → Nat), qsum n f = qsumK n f
  | 0, f => qsum_zero f
  | n + 1, f =>
    (qsum_succ n f).trans
      (congrArg (f ⟨0, Nat.zero_lt_succ n⟩ + ·)
        (qsum_eq_qsumK n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)))

/-- Copy of `uniformOracleSum` with a body the kernel can evaluate in this module. -/
private def uniformOracleSumK (w : Nat) : (n : Nat) → ((Fin n → BitVec w) → Nat) → Nat
  | 0, f => f Fin.elim0
  | n + 1, f => qsumK (2 ^ w) (fun j =>
      uniformOracleSumK w n (fun H => f (Fin.cases (BitVec.ofFin j) H)))

private theorem uniformOracleSum_eq_K (w : Nat) :
    ∀ (n : Nat) (f : (Fin n → BitVec w) → Nat), uniformOracleSum w n f = uniformOracleSumK w n f
  | 0, f => uniformOracleSum_zero w f
  | n + 1, f =>
    (uniformOracleSum_succ w n f).trans
      ((qsum_eq_qsumK _ _).trans
        (congrArg (qsumK (2 ^ w)) (funext fun _ => uniformOracleSum_eq_K w n _)))

/-- Buggy post-squeeze PoW checker: squeezes `chal` from `H_chal` BEFORE absorbing the grinding
    nonce, so `nonce : Fin numNonces` only searches `H_pow nonce = 0#bPow` without changing `chal`! -/
def buggyPostSqueezePowAccept {wChal bPow numNonces : Nat}
    (chalBad : BitVec wChal → Bool)
    (chal : BitVec wChal)
    (H_pow : Fin numNonces → BitVec bPow) : Bool :=
  chalBad chal && (List.finRange numNonces).any (fun n => canonicalZeroPowGate bPow (H_pow n))

/-- `#tooth`: if a protocol squeezes its challenge BEFORE absorbing the PoW nonce, even on a `1`-bit
    PoW (`bPow = 1`) with `2` candidate nonces (`numNonces = 2`) and `chalBad = (chal == 0#1)`,
    the winning `(chal, H_pow)` count is `3` out of `8` (`3/8 > 1/4 = (1/2) * (1/2)`), strictly
    violating the `1 / (2^bPow * 2^wChal)` absorbed-PoW bound! -/
theorem tooth_post_squeeze_pow_forfeits_reduction :
    ∃ winCount : Nat,
      winCount = qsum 2 (fun c =>
        uniformOracleSum 1 2 (fun H_pow =>
          if buggyPostSqueezePowAccept (bPow := 1) (numNonces := 2)
               (fun ch => decide (ch = 0#1)) (BitVec.ofFin c) H_pow = true then 1 else 0)) ∧
      winCount = 3 ∧
      ¬ RatBound.le ⟨winCount, 2 * (2 ^ 1) ^ 2, by decide⟩ ⟨1, 2 ^ 1 * 2 ^ 1, by decide⟩ :=
  ⟨3, by
      have hU : ∀ f : (Fin 2 → BitVec 1) → Nat, uniformOracleSum 1 2 f = uniformOracleSumK 1 2 f :=
        uniformOracleSum_eq_K 1 2
      rw [qsum_eq_qsumK]
      simp only [hU]
      decide +kernel,
    rfl, by decide +kernel⟩


/-! ### §2.3 End-to-End Composition Over `verifyHemOpeningBatch` (`HemExtractedOpeningBridge`) -/

/-- **End-to-End Authenticated `Hem` Opening + Extracted-Transcript Multi-Round Bound
    (`measured_hem_qrom_bcs_end_to_end_bound`)**:
    Combines `measured_hem_acceptance_from_extracted` on `verifyHemOpeningBatch` (calling the real
    `verifyHemAffineWhir` checker on `HemWhirInstance QuinticGoldilocks`) with any round-flip cover
    of `verifyHemAffineWhir` on the online-extracted Merkle values `extractedOpeningValues`:
    total verifier acceptance mass decomposes into the summed extracted round-escape masses plus
    `batchMerkleCost Q slots * quantumExperimentTotal A`. -/
theorem measured_hem_qrom_bcs_end_to_end_bound {cardX w cardAnc Q k : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L.levels)
    (inst : HemWhirInstance QuinticGoldilocks)
    (decode : Fin cardX → List (Option (MerkleOpeningValue w)) →
      List (HemTranscriptRound QuinticGoldilocks))
    (roundEscape : Fin k → (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool)
    (hExtractedCover : ∀ H xs x,
      verifyHemAffineWhir inst (decode x (extractedOpeningValues L slots H xs x)) = true →
      (List.finRange k).any (fun r => roundEscape r H xs x) = true) :
    2 ^ w * measuredEventMass A (fun H _ x => verifyHemOpeningBatch L slots inst decode H x) ≤
      2 ^ w * qsum k (fun r => measuredEventMass A (roundEscape r)) +
      batchMerkleCost Q slots * quantumExperimentTotal A := by
  have hBase := measured_hem_acceptance_from_extracted A L slots hLevels inst decode
  have hMono := measuredEventMass_mono A
    (fun H xs x => verifyHemAffineWhir inst (decode x (extractedOpeningValues L slots H xs x)))
    (fun H xs x => (List.finRange k).any (fun r => roundEscape r H xs x))
    hExtractedCover
  have hAnyUnion : ∀ (rs : List (Fin k)),
      measuredEventMass A (fun H xs x => rs.any (fun r => roundEscape r H xs x)) ≤
        (rs.map (fun r => measuredEventMass A (roundEscape r))).sum := by
    intro rs
    induction rs with
    | nil =>
      simp only [measuredEventMass_def]
      have hz : ∀ H : Fin cardX → BitVec w,
          sumLogs cardX Q (fun xs => QVec.queryMassOn (fun _ => false)
            (measuredStateAt A H Q (Nat.le_refl Q) xs)) = 0 := by
        intro H
        have hp : ∀ xs, QVec.queryMassOn (fun _ => false)
            (measuredStateAt A H Q (Nat.le_refl Q) xs) = 0 := by
          intro xs; simp [QVec.queryMassOn_def, qsum_const]
        rw [show (fun xs => QVec.queryMassOn (fun _ => false)
          (measuredStateAt A H Q (Nat.le_refl Q) xs)) = fun _ => 0 * 0 from funext hp]
        rw [sumLogs_mul, Nat.zero_mul]
      change uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (fun _ => false) (measuredStateAt A H Q (Nat.le_refl Q) xs))) ≤ 0
      rw [uniformOracleSum_congr w cardX _ _ hz, uniformOracleSum_const, Nat.mul_zero]
      exact Nat.le_refl 0
    | cons hd tl ih =>
      simp only [List.any_cons, List.map_cons, List.sum_cons]
      exact Nat.le_trans (measuredEventMass_union_le A (roundEscape hd) _)
        (Nat.add_le_add_left ih _)
  have hFinSum : ∀ (n : Nat) (f : Fin n → Nat),
      ((List.finRange n).map f).sum = qsum n f := by
    intro n
    induction n with
    | zero => intro _; rw [qsum_zero]; rfl
    | succ n ih =>
      intro f
      simp only [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map]
      rw [qsum_succ]
      exact congrArg (f ⟨0, Nat.zero_lt_succ n⟩ + ·) (ih (fun i => f i.succ))
  have hExtLe : measuredEventMass A
      (fun H xs x => verifyHemAffineWhir inst (decode x (extractedOpeningValues L slots H xs x))) ≤
      qsum k (fun r => measuredEventMass A (roundEscape r)) := by
    rw [← hFinSum k (fun r => measuredEventMass A (roundEscape r))]
    exact Nat.le_trans hMono (hAnyUnion (List.finRange k))
  exact Nat.le_trans hBase (Nat.add_le_add_right (Nat.mul_le_mul_left (2 ^ w) hExtLe) _)


/-! ## §3. Exact `[CDHZ25, ePrint 2025/2166]` Post-Quantum State-Restoration + Salted Merkle Bounds -/

/-- Exact `2^{-bPow}` scaling of a `RatBound` derived from `QromJointPowRbrSpec.toQromRbrRound`:
    absorbing the grinding nonce prior to squeezing the round challenge multiplies the denominator
    by `2 ^ bPow` (`powGoodCard = 1` out of `2 ^ bPow`). -/
@[expose] def powDivBound (bPow : Nat) (b : RatBound) : RatBound :=
  ⟨b.num, 2 ^ bPow * b.den, Nat.mul_pos (Nat.two_pow_pos bPow) b.h_pos⟩

/-- Unitary joint-PoW multi-round Fiat–Shamir QROM compiler bound (`powScaledFsQromCompilerBound`),
    upgrading `multiRoundFsQromCompilerBound` with the proved `1 / 2^stagePowBits` joint `(PoW × Query)`
    denominator of `qrom_joint_pow_multiRound_success_bound`:
    1. `k` RBR folding rounds scaled by `(2 * Q + 1)^2` (`dfmRoundScale Q`);
    2. salted commitment extraction `qromMerkleOnlineExtractBound numRoots secBits Q`;
    3. `j` stage query rounds scaled by `8 * (Q + 1)^2 / 2^stagePowBits`. -/
@[expose] def powScaledFsQromCompilerBound
    (Q numRoots secBits stagePowBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) : RatBound :=
  RatBound.add
    (RatBound.sumList (rbrChallengeBounds.map (dfmRoundScale Q)))
    (RatBound.add
      (qromMerkleOnlineExtractBound numRoots secBits Q)
      (RatBound.sumList (queryStageBounds.map (fun b =>
        quantumGroverGrindingBound Q (powDivBound stagePowBits b)))))

/-- Classical state-restoration BCS compiler bound (`[BCS16; CY24]`):
    linear `(T + numRounds)` state-restoration factor (`classical_state_restoration_soundness`)
    plus classical birthday collision `numRoots * (T + 1)^2 / 2^secBits`. -/
@[expose] def classicalStateRestorationBcsBound
    (T numRoots secBits stagePowBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) : RatBound :=
  let numRounds := rbrChallengeBounds.length + queryStageBounds.length
  let totalRbr := RatBound.add
    (RatBound.sumList rbrChallengeBounds)
    (RatBound.sumList (queryStageBounds.map (powDivBound stagePowBits)))
  let classicalColl : RatBound :=
    ⟨numRoots * (T + 1) ^ 2, 2 ^ secBits, Nat.two_pow_pos secBits⟩
  RatBound.add (RatBound.scale (T + numRounds) totalRbr) classicalColl

/-- `[CDHZ25]` Theorem 6.9 post-quantum state-restoration factor:
    `80 * (t + k + 1) * (wFs + k) * ε_RBR`. -/
def cdhzPqsrBound (t wFs k : Nat) (rbrSum : RatBound) : RatBound :=
  RatBound.scale (80 * (t + k + 1) * (wFs + k)) rbrSum

/-- `[CDHZ25]` Theorem 8.3 salted Merkle offline extraction bound (`n_y = 0` SNARG, Remark 11.5):
    `(160 * wVc * tOff^2 + 16 * qV * logMaxLeaf) / 2^secBits`. -/
def cdhzSaltedMerkleOfflineBound (tOff wVc qV logMaxLeaf secBits : Nat) : RatBound :=
  ⟨160 * wVc * tOff ^ 2 + 16 * qV * logMaxLeaf, 2 ^ secBits, Nat.two_pow_pos secBits⟩

/-- `[CDHZ25]` Theorem 8.3 salted Merkle online extraction bound:
    `240 * wVc * tOn^2 / 2^secBits`. -/
def cdhzSaltedMerkleOnlineBound (tOn wVc secBits : Nat) : RatBound :=
  ⟨240 * wVc * tOn ^ 2, 2 ^ secBits, Nat.two_pow_pos secBits⟩

/-- `[CDHZ25]` Theorem 8.3 salted Merkle commitment well-spreadness term:
    `240 * (t + 1) / 2^secBits`. -/
def cdhzSaltedMerkleComBound (t secBits : Nat) : RatBound :=
  ⟨240 * (t + 1), 2 ^ secBits, Nat.two_pow_pos secBits⟩

/-- `[CDHZ25]` Theorem A.1 / Theorem 11.3 composed QROM BCS SNARG soundness bound at a specific
    Fourier query partition `(wFs, wVc)` (`wFs + wVc ≤ Q`):
    `4 * ε_SR(Q, wFs) + 4 * κ_offline(2Q + 1, wVc) + 4 * κ_online(Q + 1 + qV + k, wVc) + 2 * qV^2 * κ_com(Q)`. -/
def cdhzSnargPartitionBound
    (Q wFs wVc qV logMaxLeaf secBits stagePowBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) : RatBound :=
  let k := rbrChallengeBounds.length + queryStageBounds.length
  let rbrSum := RatBound.add
    (RatBound.sumList rbrChallengeBounds)
    (RatBound.sumList (queryStageBounds.map (powDivBound stagePowBits)))
  let sr4 := RatBound.scale 4 (cdhzPqsrBound Q wFs k rbrSum)
  let off4 := RatBound.scale 4 (cdhzSaltedMerkleOfflineBound (2 * Q + 1) wVc qV logMaxLeaf secBits)
  let on4 := RatBound.scale 4 (cdhzSaltedMerkleOnlineBound (Q + 1 + qV + k) wVc secBits)
  let comTerm := RatBound.scale (2 * qV ^ 2) (cdhzSaltedMerkleComBound Q secBits)
  RatBound.add sr4 (RatBound.add off4 (RatBound.add on4 comTerm))

/-- Upper-envelope `[CDHZ25]` SNARG soundness bound dominating ALL query splits `wFs + wVc ≤ Q`
    simultaneously by setting `wFs = Q` and `wVc = Q` (`cdhzSnargPartitionBound_le_envelope`). -/
@[expose] def cdhzSnargEnvelopeBound
    (Q qV logMaxLeaf secBits stagePowBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) : RatBound :=
  cdhzSnargPartitionBound Q Q Q qV logMaxLeaf secBits stagePowBits
    rbrChallengeBounds queryStageBounds

/-- `[CDHZ25]` `320×` PQSR factor (`4 * 80 * (Q + k + 1) * (Q + k)`) composed with VCVio / BHT
    salted Merkle online extraction (`qromMerkleOnlineExtractBound`). -/
def cdhz320BhtCompilerBound
    (Q numRoots secBits stagePowBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) : RatBound :=
  let k := rbrChallengeBounds.length + queryStageBounds.length
  let rbrSum := RatBound.add
    (RatBound.sumList rbrChallengeBounds)
    (RatBound.sumList (queryStageBounds.map (powDivBound stagePowBits)))
  RatBound.add
    (RatBound.scale (4 * (80 * (Q + k + 1) * (Q + k))) rbrSum)
    (qromMerkleOnlineExtractBound numRoots secBits Q)

private theorem scale_mono_left {a b : Nat} (hab : a ≤ b) (r : RatBound) :
    RatBound.le (RatBound.scale a r) (RatBound.scale b r) := by
  unfold RatBound.le RatBound.scale
  dsimp only
  exact Nat.mul_le_mul_right r.den (Nat.mul_le_mul_right r.num hab)

private theorem scale_mono_right (c : Nat) {r₁ r₂ : RatBound} (h : RatBound.le r₁ r₂) :
    RatBound.le (RatBound.scale c r₁) (RatBound.scale c r₂) := by
  unfold RatBound.le at h
  unfold RatBound.le RatBound.scale
  dsimp only
  rw [Nat.mul_assoc, Nat.mul_assoc]
  exact Nat.mul_le_mul_left c h

/-- Every valid `[CDHZ25]` Theorem A.1 query partition `wFs + wVc ≤ Q` is bounded above by
    `cdhzSnargEnvelopeBound`. -/
theorem cdhzSnargPartitionBound_le_envelope
    (Q wFs wVc qV logMaxLeaf secBits stagePowBits : Nat)
    (hPart : wFs + wVc ≤ Q)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) :
    RatBound.le
      (cdhzSnargPartitionBound Q wFs wVc qV logMaxLeaf secBits stagePowBits
        rbrChallengeBounds queryStageBounds)
      (cdhzSnargEnvelopeBound Q qV logMaxLeaf secBits stagePowBits
        rbrChallengeBounds queryStageBounds) := by
  have hwFs : wFs ≤ Q := by omega
  have hwVc : wVc ≤ Q := by omega
  unfold cdhzSnargEnvelopeBound cdhzSnargPartitionBound
  dsimp only
  apply RatBound.add_le_add
  · apply scale_mono_right 4
    unfold cdhzPqsrBound
    apply scale_mono_left
    exact Nat.mul_le_mul_left _ (by omega)
  · apply RatBound.add_le_add
    · apply scale_mono_right 4
      unfold RatBound.le cdhzSaltedMerkleOfflineBound
      dsimp only
      apply Nat.mul_le_mul_right
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 160 hwVc)
    · apply RatBound.add_le_add
      · apply scale_mono_right 4
        unfold RatBound.le cdhzSaltedMerkleOnlineBound
        dsimp only
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 240 hwVc)
      · exact RatBound.le_refl _


/-! ## §4. Proved Cheaper `Hem` WHIR Parameter Schedules Across `nv ∈ 2..=24` -/

/-- Proved `Hem` WHIR QROM schedule regimes derived from the joint-PoW QROM reduction (`§2.2`)
    and `[CDHZ25]` post-quantum state-restoration + salted Merkle extraction (`§3`):
    - `unitaryPow16`: `q = (200, 101, 69, 52)` + 16-bit PoW (`422` total queries, `-22.1%` vs `542`)
      certified for `Q + 1 ≤ 2^40` under unitary `(2Q + 1)^2` / `8(Q + 1)^2` QROM + BHT Merkle;
    - `cdhzPow16At2pow38`: `q = (202, 102, 70, 52)` + 16-bit PoW (`426` queries, `-21.4%`)
      certified for `Q ≤ 2^38` under `[CDHZ25]` raw Theorem 6.9 (`80×`) + Theorem 8.3 (`160/240`) constants;
    - `cdhz320Pow16At2pow40`: `q = (206, 104, 71, 53)` + 16-bit PoW (`434` queries, `-19.9%`)
      certified for `Q + 1 ≤ 2^40` under `[CDHZ25]` `320×` PQSR + VCVio / BHT Merkle;
    - `unitaryZeroPow`: `q = (216, 109, 74, 56)` + 0-bit PoW (`455` queries, `-16.1%`, zero PoW grinding!)
      certified for `Q + 1 ≤ 2^40`. -/
inductive HemOptimizedQromSchedule where
  | unitaryPow16
  | cdhzPow16At2pow38
  | cdhz320Pow16At2pow40
  | unitaryZeroPow
  deriving DecidableEq, Repr

/-- Stage query count `q_j` for blowup `2 ^ logBlowup` (`logBlowup ∈ {2, 4, 6, 8}`) under each
    proved cheaper `Hem` QROM schedule. -/
@[expose] def HemOptimizedQromSchedule.minQueries (sched : HemOptimizedQromSchedule) (logBlowup : Nat) : Nat :=
  match sched with
  | .unitaryPow16 =>
    if logBlowup ≤ 2 then 200 else if logBlowup ≤ 4 then 101 else if logBlowup ≤ 6 then 69 else 52
  | .cdhzPow16At2pow38 =>
    if logBlowup ≤ 2 then 202 else if logBlowup ≤ 4 then 102 else if logBlowup ≤ 6 then 70 else 52
  | .cdhz320Pow16At2pow40 =>
    if logBlowup ≤ 2 then 206 else if logBlowup ≤ 4 then 104 else if logBlowup ≤ 6 then 71 else 53
  | .unitaryZeroPow =>
    if logBlowup ≤ 2 then 216 else if logBlowup ≤ 4 then 109 else if logBlowup ≤ 6 then 74 else 56

/-- Stage PoW grinding bits `bPow` paired with each proved schedule. -/
def HemOptimizedQromSchedule.powBits : HemOptimizedQromSchedule → Nat
  | .unitaryPow16 => 16
  | .cdhzPow16At2pow38 => 16
  | .cdhz320Pow16At2pow40 => 16
  | .unitaryZeroPow => 0

/-- Pure distinct-fiber query target bits certified on every non-exhaustive stage of `nv ∈ 2..=24`
    for each schedule (`198`, `200`, `204`, `214`). -/
@[expose] def HemOptimizedQromSchedule.pureQueryTargetBits : HemOptimizedQromSchedule → Nat
  | .unitaryPow16 => 198
  | .cdhzPow16At2pow38 => 200
  | .cdhz320Pow16At2pow40 => 204
  | .unitaryZeroPow => 214

/-- Universal 49-row `[CWYZ26]` Johnson witness table `(num_vars, stage, A, m, D)` covering ALL
    four cheaper schedules simultaneously across EVERY `num_vars ∈ 2..=24`.
    Every row for `num_vars ∈ 18..=24` (`K = 4..128` shard sizes and recursive hierarchy levels)
    is **verbatim identical** to `hemJohnsonQromWitnessTable` (`affine_schedule.rs::WITNESSES`)! -/
@[expose] def hemOptimizedQromWitnessTable : List (Nat × Nat × Nat × Nat × Nat) :=
  [ (7, 1, 98, 1, 25),
    (8, 1, 98, 1, 25),
    (9, 0, 196, 1, 22),
    (9, 1, 108, 1, 11),
    (10, 0, 310, 2, 27),
    (10, 1, 107, 1, 10),
    (11, 0, 309, 2, 26),
    (11, 1, 107, 1, 10),
    (12, 0, 563, 8, 139),
    (12, 1, 299, 8, 116),
    (12, 2, 168, 16, 258),
    (13, 0, 1077, 16, 291),
    (13, 1, 562, 32, 667),
    (13, 2, 167, 32, 528),
    (14, 0, 2108, 32, 687),
    (14, 1, 1088, 32, 799),
    (14, 2, 305, 64, 1374),
    (15, 0, 4170, 64, 1823),
    (15, 1, 1087, 64, 1753),
    (15, 2, 305, 64, 1374),
    (16, 0, 8294, 128, 5439),
    (16, 1, 2137, 64, 2392),
    (16, 2, 580, 64, 1921),
    (17, 0, 8293, 128, 5375),
    (17, 1, 2137, 64, 2392),
    (17, 2, 304, 64, 1342),
    (18, 0, 16531, 128, 7295),
    (18, 1, 4229, 64, 3418),
    (18, 2, 579, 64, 1890),
    (19, 0, 33003, 128, 10879),
    (19, 1, 8413, 64, 5471),
    (19, 2, 1124, 32, 1305),
    (20, 0, 65948, 128, 18111),
    (20, 1, 16782, 32, 3286),
    (20, 2, 2215, 32, 2149),
    (21, 0, 65947, 128, 18047),
    (21, 1, 16782, 32, 3286),
    (21, 2, 2215, 32, 2149),
    (22, 0, 131836, 128, 32511),
    (22, 1, 16781, 32, 3270),
    (22, 2, 2215, 32, 2149),
    (23, 0, 263614, 64, 14494),
    (23, 1, 33518, 32, 5870),
    (23, 2, 8759, 16, 2733),
    (23, 3, 2254, 32, 2672),
    (24, 0, 527170, 64, 27164),
    (24, 1, 66992, 32, 11069),
    (24, 2, 17484, 16, 5228),
    (24, 3, 4482, 16, 2067) ]

@[expose] def hemOptimizedQromTableRow (nv stage : Nat) : Option (Nat × Nat × Nat × Nat × Nat) :=
  hemOptimizedQromWitnessTable.find? (fun r => r.1 == nv && r.2.1 == stage)


/-! ### Kernel-evaluable copies of the `Coding.Cwyz26` checker and geometry

`Coding.Cwyz26`, `Oracle.Qrom` and the budget modules do not expose the bodies of the witness
checker, the stage-geometry mirror and the search-factor bounds, so the kernel cannot evaluate
them in this module. Each copy below has the same body as the definition it mirrors and is proved
equal to it from the exported defining equations; the certificates of this section rewrite to the
copies and are then evaluated by the kernel. -/

private def interpUnknownsK (mA_sub_D d D : Nat) : Nat → Nat
  | 0 => mA_sub_D * (D + 1)
  | j + 1 => interpUnknownsK mA_sub_D d D j + (mA_sub_D - d * (j + 1)) * (D - (j + 1) + 1)

private theorem interpUnknownsAux_eq_K : interpUnknownsAux = interpUnknownsK := by
  funext a d D j
  induction j with
  | zero => exact interpUnknownsAux_zero a d D
  | succ j ih =>
    exact (interpUnknownsAux_succ a d D j).trans
      (congrArg (· + (a - d * (j + 1)) * (D - (j + 1) + 1)) ih)

private def interpEquationsK (m D : Nat) : Nat → Nat
  | 0 => m * (D + 1)
  | s + 1 => interpEquationsK m D s + (m - (s + 1)) * (D - (s + 1) + 1)

private theorem interpEquationsAux_eq_K : interpEquationsAux = interpEquationsK := by
  funext m D s
  induction s with
  | zero => exact interpEquationsAux_zero m D
  | succ s ih =>
    exact (interpEquationsAux_succ m D s).trans
      (congrArg (· + (m - (s + 1)) * (D - (s + 1) + 1)) ih)

private def natCeilDivK (a b : Nat) : Nat := (a + b - 1) / b

private theorem natCeilDiv_eq_K : natCeilDiv = natCeilDivK := by
  funext a b
  exact natCeilDiv_def a b

private def checkWhirAffineWitnessK (w : WhirAffineWitness) (q : Nat) : Bool :=
  let mA := w.m * w.A
  let M := Nat.min w.D ((mA - w.D - 1) / w.d)
  let K := Nat.min (w.m - 1) M
  let unknowns := interpUnknownsK (mA - w.D) w.d w.D M
  let eqsPerPoint := interpEquationsK w.m w.D K
  let nonpersCeil := w.D * w.D +
    natCeilDivK (4 * w.d * w.d * M * M * w.D * w.D * w.D * w.n * w.n)
               ((w.A - w.B) * (w.A - w.B))
  decide (
    1 ≤ w.sFolds ∧
    2 ≤ w.n ∧
    1 ≤ w.d ∧
    w.d + 2 ≤ w.B ∧
    w.B < w.A ∧
    w.A + w.sFolds ≤ w.n ∧
    1 ≤ w.m ∧
    1 ≤ w.D ∧
    w.D + 1 + w.d ≤ mA ∧
    1 ≤ M ∧
    w.n * eqsPerPoint < unknowns ∧
    w.n * (w.d + 1) < w.B * w.B ∧
    w.n * w.d < (w.A - 1) * (w.A - 1) ∧
    w.n * (w.n - 1) / 2 ≤ q ∧
    nonpersCeil ≤ q ∧
    w.queries ≤ w.n ∧
    affineFallingFactorial (w.A + w.sFolds) w.queries * 2 ^ w.queryTargetBits <
      affineFallingFactorial w.n w.queries
  )

private theorem checkWhirAffineWitness_eq_K : checkWhirAffineWitness = checkWhirAffineWitnessK := by
  funext w q
  rw [checkWhirAffineWitness_def, interpUnknownsAux_eq_K, interpEquationsAux_eq_K, natCeilDiv_eq_K]
    <;> rfl

private def whirAffineStageSimpleNumK (w : WhirAffineWitness) : Nat :=
  w.sFolds * ((w.n * (w.B - w.d - 1)) / (w.B * w.B - w.n * (w.d + 1)) +
    2 * ((w.n * (w.A - 1 - w.d)) / ((w.A - 1) * (w.A - 1) - w.n * w.d)) + 1)

private theorem whirAffineStageSimpleNum_eq_K :
    whirAffineStageSimpleNum = whirAffineStageSimpleNumK := by
  funext w
  exact whirAffineStageSimpleNum_def w


private theorem ratBoundOne_eq : RatBound.one = ⟨1, 1, Nat.zero_lt_one⟩ := by
  have h1 := RatBound.one_num
  have h2 := RatBound.one_den
  generalize RatBound.one = r at h1 h2
  obtain ⟨n, d, hp⟩ := r
  dsimp only at h1 h2
  subst h1
  subst h2
  rfl

private def pureQueryBoundOrOneK (w : WhirAffineWitness) : RatBound :=
  if hq : w.queries ≤ w.n then
    ⟨affineFallingFactorial (w.A + w.sFolds) w.queries, affineFallingFactorial w.n w.queries,
     affineFallingFactorial_pos w.n w.queries hq⟩
  else ⟨1, 1, Nat.zero_lt_one⟩

private theorem whirAffinePureQueryBoundOrOne_eq_K :
    whirAffinePureQueryBoundOrOne = pureQueryBoundOrOneK := by
  funext w
  rw [whirAffinePureQueryBoundOrOne_def]
  unfold pureQueryBoundOrOneK
  by_cases hq : w.queries ≤ w.n
  · simp only [hq, ↓reduceDIte]
    exact whirAffinePureQueryBound_def w hq
  · simp only [hq, ↓reduceDIte]
    exact ratBoundOne_eq


private theorem ratBound_eq_of_num_den :
    ∀ {a b : RatBound}, a.num = b.num → a.den = b.den → a = b
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

private theorem ratBound_list_eq_of_num_den_eq :
    ∀ (xs ys : List RatBound),
      xs.map (fun b => (b.num, b.den)) = ys.map (fun b => (b.num, b.den)) → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by
    simp only [List.map_cons, List.map_nil] at h
    exact absurd h.symm (List.cons_ne_nil _ _)
  | _ :: _, [], h => by
    simp only [List.map_cons, List.map_nil] at h
    exact absurd h (List.cons_ne_nil _ _)
  | x :: xs, y :: ys, h => by
    have h' := List.cons.inj h
    have hp := Prod.mk.inj h'.1
    rw [ratBound_eq_of_num_den hp.1 hp.2, ratBound_list_eq_of_num_den_eq xs ys h'.2]


private def powScaledFsQromCompilerBoundK
    (Q numRoots secBits stagePowBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) : RatBound :=
  RatBound.add
    (RatBound.sumList (rbrChallengeBounds.map (dfmRoundScale Q)))
    (RatBound.add
      (RatBound.scale numRoots
        (RatBound.add ⟨8 * 1 * (Q + 1) ^ 2, 2 ^ secBits, Nat.two_pow_pos secBits⟩
          ⟨8 * (Q + 1) ^ 3, 2 ^ secBits, Nat.two_pow_pos secBits⟩))
      (RatBound.sumList (queryStageBounds.map (fun b =>
        RatBound.scale (8 * (Q + 1) ^ 2) (powDivBound stagePowBits b)))))

private theorem powScaledFsQromCompilerBound_eq_K
    (Q numRoots secBits stagePowBits : Nat) (rbr qb : List RatBound) :
    powScaledFsQromCompilerBound Q numRoots secBits stagePowBits rbr qb =
      powScaledFsQromCompilerBoundK Q numRoots secBits stagePowBits rbr qb := by
  unfold powScaledFsQromCompilerBound powScaledFsQromCompilerBoundK qromMerkleOnlineExtractBound
  simp only [quantumGroverGrindingBound_def, quantumGroverSingleTargetBound_def,
    quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def]

private def cdhz320BhtCompilerBoundK
    (Q numRoots secBits stagePowBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) : RatBound :=
  let k := rbrChallengeBounds.length + queryStageBounds.length
  let rbrSum := RatBound.add
    (RatBound.sumList rbrChallengeBounds)
    (RatBound.sumList (queryStageBounds.map (powDivBound stagePowBits)))
  RatBound.add
    (RatBound.scale (4 * (80 * (Q + k + 1) * (Q + k))) rbrSum)
    (RatBound.scale numRoots
      (RatBound.add ⟨8 * 1 * (Q + 1) ^ 2, 2 ^ secBits, Nat.two_pow_pos secBits⟩
        ⟨8 * (Q + 1) ^ 3, 2 ^ secBits, Nat.two_pow_pos secBits⟩))

private theorem cdhz320BhtCompilerBound_eq_K
    (Q numRoots secBits stagePowBits : Nat) (rbr qb : List RatBound) :
    cdhz320BhtCompilerBound Q numRoots secBits stagePowBits rbr qb =
      cdhz320BhtCompilerBoundK Q numRoots secBits stagePowBits rbr qb := by
  unfold cdhz320BhtCompilerBound cdhz320BhtCompilerBoundK qromMerkleOnlineExtractBound
  simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def,
    quantumBhtCollisionBound_def]


private theorem sumList_mono_pt {xs ys : List RatBound} (hLen : xs.length = ys.length)
    (hPt : ∀ i : Fin xs.length, RatBound.le (xs.get i) (ys.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 hLen⟩)) :
    RatBound.le (RatBound.sumList xs) (RatBound.sumList ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact RatBound.le_refl _
    | cons _ _ => exact absurd hLen.symm (Nat.succ_ne_zero _)
  | cons x xs' ih =>
    cases ys with
    | nil => exact absurd hLen (Nat.succ_ne_zero _)
    | cons y ys' =>
      exact RatBound.add_le_add (hPt ⟨0, Nat.zero_lt_succ _⟩)
        (ih (Nat.succ.inj hLen) (fun i => hPt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

private theorem strictlyMoreThanBits_of_le {b : Nat} {r₁ r₂ : RatBound}
    (hLe : RatBound.le r₁ r₂) (hStrict : strictlyMoreThanBits b r₂) :
    strictlyMoreThanBits b r₁ := by
  unfold RatBound.le at hLe
  unfold strictlyMoreThanBits at hStrict ⊢
  have h1 : r₁.num * 2 ^ b * r₂.den ≤ r₂.num * 2 ^ b * r₁.den := by
    have hm := Nat.mul_le_mul_right (2 ^ b) hLe
    have e1 : r₁.num * r₂.den * 2 ^ b = r₁.num * 2 ^ b * r₂.den := by rw [Nat.mul_right_comm]
    have e2 : r₂.num * r₁.den * 2 ^ b = r₂.num * 2 ^ b * r₁.den := by rw [Nat.mul_right_comm]
    rwa [e1, e2] at hm
  have h2 : r₂.num * 2 ^ b * r₁.den < r₂.den * r₁.den :=
    Nat.mul_lt_mul_of_pos_right hStrict r₁.h_pos
  have h3 : r₁.num * 2 ^ b * r₂.den < r₁.den * r₂.den := by
    rw [Nat.mul_comm r₁.den r₂.den]
    exact Nat.lt_of_le_of_lt h1 h2
  if hLt : r₁.num * 2 ^ b < r₁.den then
    exact hLt
  else
    exfalso
    exact Nat.not_le_of_gt h3 (Nat.mul_le_mul_right r₂.den (Nat.le_of_not_lt hLt))

private theorem powScaledFsQromCompilerBound_mono_Q {Q QMax : Nat} (hQ : Q ≤ QMax)
    (numRoots secBits stagePowBits : Nat)
    (rbrBounds queryBounds : List RatBound) :
    RatBound.le
      (powScaledFsQromCompilerBound Q numRoots secBits stagePowBits rbrBounds queryBounds)
      (powScaledFsQromCompilerBound QMax numRoots secBits stagePowBits rbrBounds queryBounds) := by
  unfold powScaledFsQromCompilerBound
  have hSq : (2 * Q + 1) ^ 2 ≤ (2 * QMax + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hGr : 8 * (Q + 1) ^ 2 ≤ 8 * (QMax + 1) ^ 2 :=
    Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (by omega) 2)
  apply RatBound.add_le_add
  · apply sumList_mono_pt (by simp)
    intro i; simp only [List.get_eq_getElem, List.getElem_map]
    exact scale_mono_left hSq _
  · apply RatBound.add_le_add
    · unfold qromMerkleOnlineExtractBound
      apply scale_mono_right numRoots
      apply RatBound.add_le_add
      · (unfold RatBound.le; simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def])
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
      · (unfold RatBound.le; simp only [quantumBhtCollisionBound_def])
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
    · apply sumList_mono_pt (by simp)
      intro i; simp only [List.get_eq_getElem, List.getElem_map, quantumGroverGrindingBound_def]
      exact scale_mono_left hGr _

private theorem cdhzSnargEnvelopeBound_mono_Q {Q QMax : Nat} (hQ : Q ≤ QMax)
    (qV logMaxLeaf secBits stagePowBits : Nat)
    (rbrBounds queryBounds : List RatBound) :
    RatBound.le
      (cdhzSnargEnvelopeBound Q qV logMaxLeaf secBits stagePowBits rbrBounds queryBounds)
      (cdhzSnargEnvelopeBound QMax qV logMaxLeaf secBits stagePowBits rbrBounds queryBounds) := by
  unfold cdhzSnargEnvelopeBound cdhzSnargPartitionBound
  dsimp only
  apply RatBound.add_le_add
  · apply scale_mono_right 4
    unfold cdhzPqsrBound
    apply scale_mono_left
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 80 (by omega)) (by omega)
  · apply RatBound.add_le_add
    · apply scale_mono_right 4
      unfold RatBound.le cdhzSaltedMerkleOfflineBound
      dsimp only
      apply Nat.mul_le_mul_right
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 160 hQ) (Nat.pow_le_pow_left (by omega) 2)
    · apply RatBound.add_le_add
      · apply scale_mono_right 4
        unfold RatBound.le cdhzSaltedMerkleOnlineBound
        dsimp only
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 240 hQ) (Nat.pow_le_pow_left (by omega) 2)
      · apply scale_mono_right (2 * qV ^ 2)
        unfold RatBound.le cdhzSaltedMerkleComBound
        dsimp only
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 240 (by omega))

private theorem cdhz320BhtCompilerBound_mono_Q {Q QMax : Nat} (hQ : Q ≤ QMax)
    (numRoots secBits stagePowBits : Nat)
    (rbrBounds queryBounds : List RatBound) :
    RatBound.le
      (cdhz320BhtCompilerBound Q numRoots secBits stagePowBits rbrBounds queryBounds)
      (cdhz320BhtCompilerBound QMax numRoots secBits stagePowBits rbrBounds queryBounds) := by
  unfold cdhz320BhtCompilerBound
  dsimp only
  apply RatBound.add_le_add
  · apply scale_mono_left
    apply Nat.mul_le_mul_left 4
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 80 (by omega)) (by omega)
  · unfold qromMerkleOnlineExtractBound
    apply scale_mono_right numRoots
    apply RatBound.add_le_add
    · (unfold RatBound.le; simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def])
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    · (unfold RatBound.le; simp only [quantumBhtCollisionBound_def])
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))


/-! ## §5. `#tooth` Mutation-Sensitivity Refutations & Inhabitedness Certificates -/


#verify_constructive Qsag.saltedCanopy_cross_salt_disjoint
  Qsag.saltedCanopy_fresh_salt_preprocessed_bound
  Qsag.domainTableWeight_le_tableWeight
  Qsag.domainTableWeight_sum_eq_tableWeight
  Qsag.coherent_salted_domain_budget_zero_of_overflow
  Qsag.coherent_salted_oracle_execution_bridge
  Qsag.dfmsCellDecompress_square
  Qsag.dfmsCellDecompress_norm
  Qsag.dfmsDecompress_square
  Qsag.dfmsDecompress_norm
  Qsag.dfmsDecompress_allBot
  Qsag.dfmsDecompressState_norm
  Qsag.dfmsAdvStateAt_eq
  Qsag.dfmsAdvStateAt_decode
  Qsag.dfmsAdv_event_eq
  Qsag.coherent_dfms_hem256_authenticated_event_eq
  Qsag.dfms_runtime_support
  Qsag.dfms_database_overflow_mass_zero
  Qsag.dfms_salted_domain_budget_zero_of_overflow
  Qsag.dfms_projective_extraction_disturbance_bound
  Qsag.dfms_hem256_online_extraction_disturbance_bound
  Qsag.classical_state_restoration_tree_bound
  Qsag.classical_state_restoration_soundness
  Qsag.classical_sr_sliced184_sound_at_2pow56
  Qsag.jointPowChal_badCard_le
  Qsag.canonicalZeroPowGate_card
  Qsag.qrom_joint_pow_multiRound_success_bound
  Qsag.tooth_post_squeeze_pow_forfeits_reduction
  Qsag.measured_hem_qrom_bcs_end_to_end_bound
  Qsag.cdhzSnargPartitionBound_le_envelope

#tooth_pair qrom_joint_pow_multiRound_success_bound vs tooth_post_squeeze_pow_forfeits_reduction


end Qsag
end

public section
namespace Qsag
/-! Calculation equations for profile arithmetic outside this module. -/
theorem cdhzPqsrBound_def (t wFs k : Nat) (rbrSum : RatBound) :
    cdhzPqsrBound t wFs k rbrSum =
  RatBound.scale (80 * (t + k + 1) * (wFs + k)) rbrSum := by rfl

theorem cdhzSaltedMerkleOfflineBound_def (tOff wVc qV logMaxLeaf secBits : Nat) :
    cdhzSaltedMerkleOfflineBound tOff wVc qV logMaxLeaf secBits =
  ⟨160 * wVc * tOff ^ 2 + 16 * qV * logMaxLeaf, 2 ^ secBits, Nat.two_pow_pos secBits⟩ := by rfl

theorem cdhzSaltedMerkleOnlineBound_def (tOn wVc secBits : Nat) :
    cdhzSaltedMerkleOnlineBound tOn wVc secBits =
  ⟨240 * wVc * tOn ^ 2, 2 ^ secBits, Nat.two_pow_pos secBits⟩ := by rfl

theorem cdhzSaltedMerkleComBound_def (t secBits : Nat) :
    cdhzSaltedMerkleComBound t secBits =
  ⟨240 * (t + 1), 2 ^ secBits, Nat.two_pow_pos secBits⟩ := by rfl

theorem cdhzSnargPartitionBound_def (Q wFs wVc qV logMaxLeaf secBits stagePowBits : Nat)
    (rbrChallengeBounds : List RatBound)
    (queryStageBounds : List RatBound) :
    cdhzSnargPartitionBound Q wFs wVc qV logMaxLeaf secBits stagePowBits rbrChallengeBounds queryStageBounds =
  let k := rbrChallengeBounds.length + queryStageBounds.length
  let rbrSum := RatBound.add
    (RatBound.sumList rbrChallengeBounds)
    (RatBound.sumList (queryStageBounds.map (powDivBound stagePowBits)))
  let sr4 := RatBound.scale 4 (cdhzPqsrBound Q wFs k rbrSum)
  let off4 := RatBound.scale 4 (cdhzSaltedMerkleOfflineBound (2 * Q + 1) wVc qV logMaxLeaf secBits)
  let on4 := RatBound.scale 4 (cdhzSaltedMerkleOnlineBound (Q + 1 + qV + k) wVc secBits)
  let comTerm := RatBound.scale (2 * qV ^ 2) (cdhzSaltedMerkleComBound Q secBits)
  RatBound.add sr4 (RatBound.add off4 (RatBound.add on4 comTerm)) := by rfl


/-! ### Unsalted canopy tooth (audited in `Tests/HemExtractedOpeningBridgeTests`)

Paired here: the constant shared with `saltedCanopy_fresh_salt_preprocessed_bound` is
`SaltedCanopyLayout.levels`, reached through the body of `SaltedCanopyLayout.atSalt`, which is visible
only in this module. -/

/-- Explicit unsalted (`cardSalt = 1`) 4-address finite Canopy instance showing why omitting
    per-commitment salts enables a 0-online-query collision attack under 2 bits of offline advice. -/
def unsaltedFourAddressCanopy : SaltedCanopyLayout 1 4 1 where
  encode := fun _ _ _ u v =>
    ⟨u.toNat * 2 + v.toNat, by
      have hu := u.isLt
      have hv := v.isLt
      omega⟩
  decode := fun x =>
    some (0, 0, 0, BitVec.ofNat 1 (x.1 / 2), BitVec.ofNat 1 (x.1 % 2))
  levels := 1
  nodes := 1
  decode_sound := by
    intro x s l n u v h
    injection h with hEq
    rcases hEq with ⟨_, _, _, rfl, rfl⟩
    apply Fin.ext
    dsimp
    have hx := x.isLt
    have h1 : (BitVec.ofNat 1 (x.1 / 2)).toNat = x.1 / 2 := by
      rw [BitVec.toNat_ofNat]; omega
    have h2 : (BitVec.ofNat 1 (x.1 % 2)).toNat = x.1 % 2 := by
      rw [BitVec.toNat_ofNat]; omega
    rw [h1, h2]
    omega
  decode_encode := by
    intro s l n u v hl hn
    have hs : s = 0 := Fin.ext (by omega)
    have hl0 : l = 0 := by omega
    have hn0 : n = 0 := by omega
    subst hs hl0 hn0
    dsimp
    have hu := u.isLt
    have hv := v.isLt
    have hU : BitVec.ofNat 1 ((u.toNat * 2 + v.toNat) / 2) = u := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]; omega
    have hV : BitVec.ofNat 1 ((u.toNat * 2 + v.toNat) % 2) = v := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]; omega
    rw [hU, hV]

/-- `#tooth`: without fresh salting (`cardSalt = 1`), 2 bits of offline advice find an explicit
    oracle collision in 0 online queries on 100% (`8 / 8`) of 1-bit 3-address oracles. -/
theorem tooth_unsalted_canopy_preprocessed_collision :
    ∃ (A : PreprocessingGame.ClassicalAdvice 3 1 1 2 0 (Fin 3 × Fin 3)),
      PreprocessingGame.adviceWinCount A
        (fun H _ pair => PreprocessingGame.collisionWin H pair) = (2 ^ 1) ^ 3 ∧
      (∀ H : Fin 3 → BitVec 1, (A.run H 0).2 = 0) ∧
      unsaltedFourAddressCanopy.levels = 1 :=
  ⟨PreprocessingGame.storedCollision, PreprocessingGame.storedCollision_count,
   PreprocessingGame.storedCollision_execution.2.2, rfl⟩

#verify_constructive Qsag.tooth_unsalted_canopy_preprocessed_collision
#tooth_pair saltedCanopy_fresh_salt_preprocessed_bound vs tooth_unsalted_canopy_preprocessed_collision

/-! ### Executed `w = 2` DFMS runtime witness and database-measurement tooth
(audited and paired in `Tests/QromCoherentOracleTests`)

The Gaussian-integer arithmetic, the query gate and the oracle sums are sealed in `Oracle/Qrom`. The
copies below have bodies the kernel can evaluate in this module; each is proved equal to the original
from the equations `Oracle/Qrom` exports, and the two theorems rewrite to the copies before deciding. -/

private def gaussAddK (z w : GaussInt) : GaussInt := ⟨z.re + w.re, z.im + w.im⟩

private def gaussSubK (z w : GaussInt) : GaussInt := ⟨z.re - w.re, z.im - w.im⟩

private def gaussDoublePowK : Nat → GaussInt → GaussInt
  | 0, z => z
  | k + 1, z => gaussAddK (gaussDoublePowK k z) (gaussDoublePowK k z)

private theorem gaussDoublePow_eq_K : ∀ (k : Nat) (z : GaussInt),
    gaussDoublePow k z = gaussDoublePowK k z
  | 0, z => gaussDoublePow_base z
  | k + 1, z => by
    rw [gaussDoublePow_step, gaussDoublePow_eq_K k z, GaussInt.add_def]
    rfl

private def dfmsCellDecompressK (m : Nat) (f : Option (BitVec (2 * m)) → GaussInt) :
    Option (BitVec (2 * m)) → GaussInt
  | none => gaussDoublePowK m (bvGaussSum (2 * m) (fun y => f (some y)))
  | some y =>
    gaussAddK
      (gaussSubK (gaussDoublePowK (2 * m) (f (some y))) (bvGaussSum (2 * m) (fun y' => f (some y'))))
      (gaussDoublePowK m (f none))

private theorem dfmsCellDecompress_eq_K (m : Nat) (f : Option (BitVec (2 * m)) → GaussInt)
    (c : Option (BitVec (2 * m))) : dfmsCellDecompress m f c = dfmsCellDecompressK m f c := by
  cases c with
  | none => simp only [dfmsCellDecompress, dfmsCellDecompressK, gaussDoublePow_eq_K]
  | some y =>
    simp only [dfmsCellDecompress, dfmsCellDecompressK, gaussDoublePow_eq_K, GaussInt.add_def,
      GaussInt.sub_def, gaussAddK, gaussSubK]

private def dfmsDecompressK (m : Nat) :
    (n : Nat) → (DfmsTable m n → GaussInt) → DfmsTable m n → GaussInt
  | 0, f, () => f ()
  | n + 1, f, (c, D) =>
    dfmsCellDecompressK m (fun c' => dfmsDecompressK m n (fun D' => f (c', D')) D) c

private theorem dfmsDecompress_eq_K (m : Nat) : ∀ (n : Nat) (f : DfmsTable m n → GaussInt)
    (D : DfmsTable m n), dfmsDecompress m n f D = dfmsDecompressK m n f D
  | 0, _, () => rfl
  | n + 1, f, (c, D) => by
    have hInner : (fun c' => dfmsDecompress m n (fun D' => f (c', D')) D) =
        fun c' => dfmsDecompressK m n (fun D' => f (c', D')) D :=
      funext fun c' => dfmsDecompress_eq_K m n _ D
    show dfmsCellDecompress m (fun c' => dfmsDecompress m n (fun D' => f (c', D')) D) c = _
    rw [hInner, dfmsCellDecompress_eq_K]
    rfl

private def dfmsTableSumK (m : Nat) : (n : Nat) → (DfmsTable m n → Nat) → Nat
  | 0, f => f ()
  | n + 1, f =>
    dfmsTableSumK m n (fun D => f (none, D)) +
      qsumK (2 ^ (2 * m)) (fun j => dfmsTableSumK m n (fun D => f (some (BitVec.ofFin j), D)))

private theorem dfmsTableSum_eq_K (m : Nat) : ∀ (n : Nat) (f : DfmsTable m n → Nat),
    dfmsTableSum m n f = dfmsTableSumK m n f
  | 0, _ => rfl
  | n + 1, f => by
    show dfmsCellSum (2 * m) (fun c => dfmsTableSum m n (fun D => f (c, D))) = _
    unfold dfmsCellSum
    rw [qsum_eq_qsumK]
    have hInner : (fun j : Fin (2 ^ (2 * m)) =>
        dfmsTableSum m n (fun D => f (some (BitVec.ofFin j), D))) =
        fun j => dfmsTableSumK m n (fun D => f (some (BitVec.ofFin j), D)) :=
      funext fun j => dfmsTableSum_eq_K m n _
    show dfmsTableSum m n (fun D => f (none, D)) +
      qsumK (2 ^ (2 * m)) (fun j => dfmsTableSum m n (fun D => f (some (BitVec.ofFin j), D))) = _
    rw [hInner, dfmsTableSum_eq_K m n]
    rfl

/-- The one-query DFMS state of `dfmsW2ParityAdv`, with the kernel-evaluable copies. -/
private def dfmsW2StateK : DfmsState 1 2 1 := fun D x y a =>
  dfmsDecompressK 1 2 (fun D₁ =>
    (fun (ψ : QVec 2 2 1) (x : Fin 2) (y : Fin (2 ^ 2)) (a : Fin 1) =>
      if x.val == 0 then gaussAddK (ψ ⟨0, by decide⟩ y a) (ψ ⟨1, by decide⟩ y a)
      else gaussSubK (ψ ⟨0, by decide⟩ y a) (ψ ⟨1, by decide⟩ y a))
    (fun x y a =>
      match dfmsEntry 2 D₁ x with
      | none => dfmsDecompressK 1 2 (fun D₀ =>
          if dfmsIsAllBot 1 2 D₀ then (if y.1 % 2 == 0 then (⟨1, 0⟩ : GaussInt) else ⟨-1, 0⟩)
          else ⟨0, 0⟩) D₁
      | some v => dfmsDecompressK 1 2 (fun D₀ =>
          if dfmsIsAllBot 1 2 D₀ then
            (if (BitVec.ofFin y ^^^ v).toFin.1 % 2 == 0 then (⟨1, 0⟩ : GaussInt) else ⟨-1, 0⟩)
          else ⟨0, 0⟩) D₁) x y a) D

private theorem dfmsW2State_eq_K :
    dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1) = dfmsW2StateK := by
  funext D x y a
  show dfmsDecompress 1 2 (fun D₁ => (dfmsW2ParityAdv.steps ⟨0, Nat.le_refl 1⟩).apply
    (dfmsCellXor D₁ (fun x y a => dfmsDecompress 1 2
      (fun D₀ => (if dfmsIsAllBot 1 2 D₀ then dfmsW2ParityAdv.init else QVec.zero 2 (2 * 1) 1) x y a)
      D₁)) x y a) D = _
  rw [dfmsDecompress_eq_K]
  unfold dfmsW2StateK
  apply congrArg (fun f => dfmsDecompressK 1 2 f D)
  funext D₁
  rw [dfmsW2ParityAdv_steps, hadamardQuery2_apply, GaussInt.add_def, GaussInt.sub_def]
  have hCell : ∀ (x' : Fin 2), dfmsCellXor D₁ (fun x y a => dfmsDecompress 1 2
      (fun D₀ => (if dfmsIsAllBot 1 2 D₀ then dfmsW2ParityAdv.init else QVec.zero 2 (2 * 1) 1) x y a)
      D₁) x' y a =
      match dfmsEntry 2 D₁ x' with
      | none => dfmsDecompressK 1 2 (fun D₀ =>
          if dfmsIsAllBot 1 2 D₀ then (if y.1 % 2 == 0 then (⟨1, 0⟩ : GaussInt) else ⟨-1, 0⟩)
          else ⟨0, 0⟩) D₁
      | some v => dfmsDecompressK 1 2 (fun D₀ =>
          if dfmsIsAllBot 1 2 D₀ then
            (if (BitVec.ofFin y ^^^ v).toFin.1 % 2 == 0 then (⟨1, 0⟩ : GaussInt) else ⟨-1, 0⟩)
          else ⟨0, 0⟩) D₁ := by
    intro x'
    unfold dfmsCellXor
    have hInit : ∀ (y' : Fin (2 ^ (2 * 1))), (fun D₀ : DfmsTable 1 2 =>
        (if dfmsIsAllBot 1 2 D₀ then dfmsW2ParityAdv.init else QVec.zero 2 (2 * 1) 1) x' y' a) =
        fun D₀ => if dfmsIsAllBot 1 2 D₀ then
          (if y'.1 % 2 == 0 then (⟨1, 0⟩ : GaussInt) else ⟨-1, 0⟩) else ⟨0, 0⟩ := by
      intro y'
      funext D₀
      rw [dfmsW2ParityAdv_init, QVec.zero_def, GaussInt.zero_def]
      cases dfmsIsAllBot 1 2 D₀ <;> rfl
    cases dfmsEntry 2 D₁ x' with
    | none => simp only [hInit, dfmsDecompress_eq_K]
    | some v => simp only [hInit, dfmsDecompress_eq_K, xorFin_def]
  rw [hCell, hCell]
  rfl

private theorem stateNormSq_eq_K (ψ : QVec 2 2 1) :
    QVec.stateNormSq ψ = qsumK 2 (fun x => qsumK (2 ^ 2) (fun y => qsumK 1 (fun a =>
      (ψ x y a).re.natAbs * (ψ x y a).re.natAbs + (ψ x y a).im.natAbs * (ψ x y a).im.natAbs))) := by
  simp only [QVec.stateNormSq_def, QVec.queryWeight_def, GaussInt.normSq_def, qsum_eq_qsumK]

private theorem dfmsCoherentEventMass_eq_K (event : (Fin 2 → BitVec (2 * 1)) → Fin 2 → Bool)
    (ψ : DfmsState 1 2 1) :
    dfmsCoherentEventMass (m := 1) event (dfmsDecompressState ψ) =
      dfmsTableSumK 1 2 (fun D => qsumK 2 (fun x =>
        if event (dfmsToOracle 1 2 D) x = true then
          qsumK (2 ^ 2) (fun y => qsumK 1 (fun a =>
            (dfmsDecompressK 1 2 (fun D' => ψ D' x y a) D).re.natAbs *
                (dfmsDecompressK 1 2 (fun D' => ψ D' x y a) D).re.natAbs +
              (dfmsDecompressK 1 2 (fun D' => ψ D' x y a) D).im.natAbs *
                (dfmsDecompressK 1 2 (fun D' => ψ D' x y a) D).im.natAbs))
        else 0)) := by
  unfold dfmsCoherentEventMass dfmsDecompressState
  simp only [QVec.queryMassOn_def, QVec.queryWeight_def, GaussInt.normSq_def, qsum_eq_qsumK,
    dfmsTableSum_eq_K, dfmsDecompress_eq_K]

/-- Decidable equality on `DfmsTable 1 2` (`25` states: `Option (BitVec 2) × Option (BitVec 2)`). -/
def dfmsW2TableEq (D₁ D₂ : DfmsTable 1 2) : Bool :=
  decide (D₁.1 = D₂.1 ∧ D₁.2.1 = D₂.2.1)

/-- Executable `w = 2` (`m = 1`, 2-bit `Option (BitVec 2)` compressed database!) kernel-`decide`
    witness: after 1 coherent 2-bit query, `dfmsW2ParityAdv` has **0 mass** on `dfmsRecordedCount > 1`,
    strictly positive mass on recorded `some (y : BitVec 2)` entries, and **100% (`256 / 256`)**
    undisturbed parity success both in `uniformOracleSum 2 2` and after `dfmsDecompressState`! -/
theorem dfms_w2_coherent_runtime_witness :
    uniformOracleSum 2 2 (fun H =>
      QVec.queryMassOn (dfmsW2ParityEvent H) (runQuantumAdv dfmsW2ParityAdv H)) = 256 ∧
    quantumExperimentTotal dfmsW2ParityAdv = 256 ∧
    dfmsTableSum 1 2 (fun D =>
      if 1 < dfmsRecordedCount 2 D then
        QVec.stateNormSq (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1) D)
      else 0) = 0 ∧
    0 < dfmsTableSum 1 2 (fun D =>
      if dfmsRecordedCount 2 D == 1 then
        QVec.stateNormSq (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1) D)
      else 0) ∧
    dfmsCoherentEventMass (m := 1) dfmsW2ParityEvent
      (dfmsDecompressState (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1))) =
      4 ^ 10 * 256 := by
  refine ⟨dfmsW2Parity_real_oracle_execution.1, dfmsW2Parity_real_oracle_execution.2, ?_, ?_, ?_⟩
  · rw [dfmsW2State_eq_K, dfmsTableSum_eq_K]
    simp only [stateNormSq_eq_K]
    decide +kernel
  · rw [dfmsW2State_eq_K, dfmsTableSum_eq_K]
    simp only [stateNormSq_eq_K]
    decide +kernel
  · rw [dfmsAdv_event_eq 1 dfmsW2ParityAdv dfmsW2ParityEvent, dfmsW2Parity_real_oracle_execution.1]

/-- `#tooth` negative control at `w = 2` (`Option (BitVec 2)`): naively collapsing the `DfmsTable 1 2`
    database (`projectDfmsPred (dfmsW2TableEq D)`) before decompression destroys coherent cross-address
    interference and drops `dfmsW2ParityEvent` mass from `4^10 * 256` (`100%`) strictly down to
    `4^10 * 128` (`50%`), demonstrating why `dfms_projective_extraction_disturbance_bound` is required! -/
theorem tooth_dfms_w2_raw_database_measurement_disturbs :
    ∃ measuredMass : Nat,
      measuredMass = dfmsTableSum 1 2 (fun D =>
        dfmsCoherentEventMass (m := 1) dfmsW2ParityEvent
          (dfmsDecompressState
            (projectDfmsPred (dfmsW2TableEq D)
              (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1))))) ∧
      measuredMass = 4 ^ 10 * 128 ∧
      measuredMass ≠ dfmsCoherentEventMass (m := 1) dfmsW2ParityEvent
        (dfmsDecompressState (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1))) := by
  refine ⟨4 ^ 10 * 128, ?_, rfl, ?_⟩
  · rw [dfmsW2State_eq_K, dfmsTableSum_eq_K]
    simp only [dfmsCoherentEventMass_eq_K, projectDfmsPred, QVec.zero_def, GaussInt.zero_def,
      dfmsW2ParityEvent_eq]
    decide +kernel
  · rw [dfms_w2_coherent_runtime_witness.2.2.2.2]
    decide

#verify_constructive
  Qsag.dfms_w2_coherent_runtime_witness
  Qsag.tooth_dfms_w2_raw_database_measurement_disturbs

end Qsag
end
