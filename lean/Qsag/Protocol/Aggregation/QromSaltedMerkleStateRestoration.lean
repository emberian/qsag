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
public import Qsag.Oracle.QromFourierSupport
public import Qsag.Oracle.QromPreprocessingChecks
public import Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
public import Qsag.Protocol.Aggregation.HemSlicedFoldBudget
public import Qsag.Tactic.AssuranceKit
import all Qsag.Oracle.QromFourierSupport
import all Qsag.Oracle.QromCoherentOracleRegister
import all Qsag.Oracle.QromFourierTable
import all Qsag.Oracle.QromPreprocessingChecks
import all Qsag.Oracle.QromPreprocessingGame
import all Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
import all Qsag.Oracle.QromBatchMerkleExtraction
import all Qsag.Oracle.QromMeasuredMerkleExtraction
import all Qsag.Oracle.QromMeasuredQueryExperiment
import all Qsag.Protocol.Aggregation.HemSlicedFoldBudget
import all Qsag.Coding.Cwyz26DeployedStages
import all Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Protocol.Aggregation.HemWhirRbrSoundness
import all Qsag.Oracle.MultiRoundFsQrom
import all Qsag.Oracle.ConcreteSecurityBudget
import all Qsag.Coding.AffineProximityGaps

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
   fun _ => rfl, rfl⟩

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
  | 0, _, _, _, _ => Nat.le_refl 0
  | n + 1, _, domainOf, dom, (b, rest) => by
    have ih := domainTableWeight_le_tableWeight n (fun i => domainOf i.succ) dom rest
    simp only [domainTableWeight, tableWeight]
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
    simp only [domainTableWeight, tableWeight, qsum_const, Nat.mul_zero]
  | n + 1, cardDom, domainOf, (b, rest) => by
    simp only [domainTableWeight, tableWeight, qsum_add]
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
  | 0, _ => rfl
  | N + 1, f => by
    simp only [intSum, qsum, intSum_of_qsum N]
    omega

private theorem gaussDoublePow_re : ∀ (k : Nat) (z : GaussInt),
    (gaussDoublePow k z).re = ((2 ^ k : Nat) : Int) * z.re
  | 0, z => by simp [gaussDoublePow]
  | k + 1, z => by
    simp only [gaussDoublePow, GaussInt.add, gaussDoublePow_re k z]
    have h2 : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) + ((2 ^ k : Nat) : Int) := by
      rw [Nat.pow_succ]; omega
    rw [h2, Int.add_mul]

private theorem gaussDoublePow_im : ∀ (k : Nat) (z : GaussInt),
    (gaussDoublePow k z).im = ((2 ^ k : Nat) : Int) * z.im
  | 0, z => by simp [gaussDoublePow]
  | k + 1, z => by
    simp only [gaussDoublePow, GaussInt.add, gaussDoublePow_im k z]
    have h2 : ((2 ^ (k + 1) : Nat) : Int) = ((2 ^ k : Nat) : Int) + ((2 ^ k : Nat) : Int) := by
      rw [Nat.pow_succ]; omega
    rw [h2, Int.add_mul]

private theorem gaussDoublePow_zero : ∀ (k : Nat), gaussDoublePow k GaussInt.zero = GaussInt.zero
  | 0 => rfl
  | k + 1 => by simp only [gaussDoublePow, gaussDoublePow_zero k]; rfl

private theorem gaussDoublePow_inj : ∀ (k : Nat) {u v : GaussInt},
    gaussDoublePow k u = gaussDoublePow k v → u = v
  | 0, _, _, h => h
  | k + 1, u, v, h => by
    apply gaussDoublePow_inj k
    have hr := congrArg GaussInt.re h
    have hi := congrArg GaussInt.im h
    apply GaussInt.ext <;> simp only [gaussDoublePow, GaussInt.add] at hr hi <;> omega

private theorem gaussDoublePow_map_add : ∀ (k : Nat) (u v : GaussInt),
    gaussDoublePow k (u.add v) = (gaussDoublePow k u).add (gaussDoublePow k v)
  | 0, _, _ => rfl
  | k + 1, u, v => by
    simp only [gaussDoublePow, gaussDoublePow_map_add k]
    apply GaussInt.ext <;> simp [GaussInt.add] <;> omega

private theorem gaussDoublePow_map_sub : ∀ (k : Nat) (u v : GaussInt),
    gaussDoublePow k (u.sub v) = (gaussDoublePow k u).sub (gaussDoublePow k v)
  | 0, _, _ => rfl
  | k + 1, u, v => by
    simp only [gaussDoublePow, gaussDoublePow_map_sub k]
    apply GaussInt.ext <;> simp [GaussInt.add, GaussInt.sub] <;> omega

/-- Exact Gaussian-integer sum over all `2 ^ w` values of `BitVec w`. -/
def bvGaussSum (w : Nat) (f : BitVec w → GaussInt) : GaussInt :=
  ⟨intSum (2 ^ w) (fun i => (f (BitVec.ofFin i)).re),
   intSum (2 ^ w) (fun i => (f (BitVec.ofFin i)).im)⟩

private theorem bvGaussSum_add (w : Nat) (f g : BitVec w → GaussInt) :
    bvGaussSum w (fun y => (f y).add (g y)) = (bvGaussSum w f).add (bvGaussSum w g) := by
  apply GaussInt.ext <;> simp [bvGaussSum, GaussInt.add, intSum_add]

private theorem bvGaussSum_sub (w : Nat) (f g : BitVec w → GaussInt) :
    bvGaussSum w (fun y => (f y).sub (g y)) = (bvGaussSum w f).sub (bvGaussSum w g) := by
  apply GaussInt.ext <;> simp [bvGaussSum, GaussInt.sub, intSum_sub]

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
    apply GaussInt.ext <;> simp [GaussInt.add, GaussInt.sub] <;> omega

private theorem dfmsCellDecompress_sub (m : Nat) (f g : Option (BitVec (2 * m)) → GaussInt)
    (c : Option (BitVec (2 * m))) :
    dfmsCellDecompress m (fun x => (f x).sub (g x)) c =
      (dfmsCellDecompress m f c).sub (dfmsCellDecompress m g c) := by
  cases c with
  | none =>
    simp only [dfmsCellDecompress, bvGaussSum_sub, gaussDoublePow_map_sub]
  | some y =>
    simp only [dfmsCellDecompress, bvGaussSum_sub, gaussDoublePow_map_sub]
    apply GaussInt.ext <;> simp [GaussInt.add, GaussInt.sub] <;> omega

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
  | some _ => simp only [dfmsCellDecompress, hz, gaussDoublePow_zero]; rfl

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
    apply GaussInt.ext <;> simp [GaussInt.add, GaussInt.sub] <;> omega
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
    apply GaussInt.ext <;> simp [GaussInt.add, GaussInt.sub] <;> omega

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
    fun z => (GaussInt.normSqInt_eq_ofNat_normSq z).symm
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
    simp only [dfmsCellDecompress, GaussInt.add, GaussInt.sub, gaussDoublePow_re,
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
      | zero => simp [qsum, qsum_const]
      | succ k' ih =>
        simp only [qsum, qsum_add]
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
  | 0, _ => rfl
  | n + 1, f => by
    unfold dfmsTableSum dfmsCellSum
    dsimp only
    have hNone : dfmsTableSum m n (fun D =>
        if dfmsIsTotal m (n + 1) (none, D) then f (dfmsToOracle m (n + 1) (none, D)) else 0) = 0 := by
      simp only [dfmsIsTotal, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact dfmsTableSum_zero m n
    rw [hNone, Nat.zero_add]
    unfold uniformOracleSum
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
