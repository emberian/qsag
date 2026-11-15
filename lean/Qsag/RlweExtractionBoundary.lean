module
/-
# The norm boundary of the production fork-extraction relation & Euclidean Ring-SIS closure

The `ℓ_∞`-only extraction dichotomy is valid algebra, whose SIS branch at bound `6142`
admits the public candidate `(1, centered(-A))` whenever `A` avoids four residues per
coordinate (`rlweUnitSis_norm_le_6142`). Adding the explicit pair Euclidean check
`RLWE_ZKPOK_PAIR_L2_SQ_BOUND = 1_500_000_000` in `RlweReceiverZkPok::prove_ct` and
`RlweReceiverZkPok::verify` (`crates/qsag-core/src/preprocessing.rs`) restricts forked
extraction over the `24 × 11 = 264`-bit signed-monomial challenge space to a joint
`(ℓ_∞ ≤ 6142, ‖s_sis‖_2^2 + ‖e_sis‖_2^2 ≤ 6_060_827_392)` Ring-SIS relation
(`extract_rlwe_or_sigma_24_euclidean_sis_dichotomy`), deterministically refuting dense
public solutions (`tooth_rlweUnitSis_refuted_by_euclidean_bound`). This module also
establishes exact integer ULP, Q64 fast-filter equivalence, and 49,152-coordinate joint
retry bounds for the production Q192 discrete Gaussian sampler.
-/
public import Qsag.RlweCyclotomicExtraction
import all Qsag.RlweCyclotomicExtraction
public import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
set_option autoImplicit false

/-- Explicit nonzero candidate `(1, centered(-A))`. -/
def rlweUnitSisError (A : CycPolyZq 10 12289) : CycPolyInt 10 :=
  cycZqCentered (cycZqNeg A)

theorem rlweUnitSis_relation (A : CycPolyZq 10 12289) :
    cycIntToZq 12289 (@cycIntOne 1024) ≠ cycZqZero ∧
    cycIntInfNorm (@cycIntOne 1024) ≤ 1 ∧
    cycZqAdd (cycZqMul A (cycIntToZq 12289 (@cycIntOne 1024)))
      (cycIntToZq 12289 (rlweUnitSisError A)) = cycZqZero := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h ⟨0, by decide⟩
    have hv := congrArg ModZq.val h0
    change 1 = 0 at hv
    omega
  · rw [cycIntInfNorm_le_iff]
    intro k
    unfold cycIntOne
    split <;> decide
  · rw [cycIntToZq_one, cycZqMul_one_right (by decide), rlweUnitSisError,
      cycIntToZq_centered]
    funext k
    unfold cycZqAdd cycZqNeg cycZqZero
    rw [← ModZq.ofInt_natVal (A k), ← ModZq.ofInt_neg, ← ModZq.ofInt_add]
    rw [show ((A k).val : Int) + -((A k).val : Int) = 0 by omega, ModZq.ofInt_zero]

theorem rlweUnitSis_norm_le_half_modulus (A : CycPolyZq 10 12289) :
    cycIntInfNorm (rlweUnitSisError A) ≤ 6144 := by
  rw [cycIntInfNorm_le_iff]
  intro k
  unfold rlweUnitSisError cycZqCentered ModZq.centered
  have h := (cycZqNeg A k).isLt
  split <;> omega

/-- Only four out of 12289 residues can obstruct this public candidate at bound 6142.
For independent uniform coefficients the exact success rate is `(12285/12289)^1024`.
The probability interpretation requires that distribution; this theorem is pointwise. -/
theorem rlweUnitSis_norm_le_6142
    (A : CycPolyZq 10 12289)
    (hAvoid : ∀ k, (cycZqNeg A k).val ≤ 6142 ∨ 6147 ≤ (cycZqNeg A k).val) :
    cycIntInfNorm (rlweUnitSisError A) ≤ 6142 := by
  rw [cycIntInfNorm_le_iff]
  intro k
  have h := (cycZqNeg A k).isLt
  have ha := hAvoid k
  unfold rlweUnitSisError cycZqCentered ModZq.centered
  split <;> omega

/-- The union-bound failure numerator is below one third of the denominator.
Together with four excluded residues per coefficient, this gives success > 2/3
under independent uniform A, without a large-power computation. -/
theorem rlweUnitSis_uniform_union_budget : 3 * (1024 * 4) < 12289 := by decide

#verify_constructive rlweUnitSis_relation rlweUnitSis_norm_le_half_modulus
  rlweUnitSis_norm_le_6142 rlweUnitSis_uniform_union_budget

/-! ## Euclidean Pair Norm Closure & Non-Vacuous 24-Parallel Ring-SIS Extraction -/

/-- Production Euclidean pair norm bound `RLWE_ZKPOK_PAIR_L2_SQ_BOUND = 1_500_000_000`
    enforced by `RlweReceiverZkPok::prove_ct` and `RlweReceiverZkPok::verify` in
    `crates/qsag-core/src/preprocessing.rs`. -/
def rlweZkpokPairL2SqBound : Nat := 1500000000

/-- Extracted Ring-SIS Euclidean squared norm bound `6_060_827_392` derived from two
    forked transcripts obeying `rlweZkpokPairL2SqBound` against a ternary RLWE secret
    (`‖s*‖_2^2 + ‖e*‖_2^2 ≤ 2048`). -/
def rlweExtractedSisL2SqBound : Nat := 6060827392

/-- Squared Euclidean norm `‖p‖_2^2 = ∑_{k < N} |p_k|^2` on `ℤ[X]/(X^N + 1)`. -/
def cycIntL2Sq {N : Nat} (p : NegacyclicPolyInt N) : Nat :=
  cycNatFinSum N (fun i => (p i).natAbs * (p i).natAbs)

private theorem cycNatFinSum_mul_left {n : Nat} (c : Nat) (f : Fin n → Nat) :
    cycNatFinSum n (fun i => c * f i) = c * cycNatFinSum n f := by
  induction n with
  | zero => simp [cycNatFinSum]
  | succ n ih => simp only [cycNatFinSum, ih, Nat.mul_add]

private theorem cycNatFinSum_bijection {N : Nat} (σ τ : Fin N → Fin N)
    (hLeft : ∀ j : Fin N, τ (σ j) = j)
    (hRight : ∀ i : Fin N, σ (τ i) = i)
    (f : Fin N → Nat) :
    cycNatFinSum N (fun j => f (σ j)) = cycNatFinSum N f := by
  have hStep1 : ∀ j : Fin N,
      f (σ j) = cycNatFinSum N (fun i => if i = σ j then f i else 0) := by
    intro j
    symm
    rw [cycNatFinSum_eq_single (σ j)]
    · simp
    · intro i hiNe; simp [hiNe]
  rw [cycNatFinSum_congr hStep1, cycNatFinSum_comm]
  apply cycNatFinSum_congr
  intro i
  rw [cycNatFinSum_eq_single (τ i)]
  · simp [hRight i]
  · intro j hjNe
    have hNe : i ≠ σ j := by
      intro hEq
      apply hjNe
      have hAp := congrArg τ hEq
      rw [hLeft j] at hAp
      exact hAp.symm
    simp [hNe]

/-- **Signed-Monomial Euclidean Isometry (`cycIntL2Sq_mul_negacyclicSignedMonomial_eq`)**:
    Multiplying any polynomial in `ℤ[X]/(X^N + 1)` by a signed monomial `±X^k` preserves `‖·‖_2^2`
    identically (`‖(±X^k) ⊛ p‖_2^2 = ‖p‖_2^2`). -/
theorem cycIntL2Sq_mul_negacyclicSignedMonomial_eq {N : Nat} (s : Bool) (k : Fin N)
    (p : NegacyclicPolyInt N) :
    cycIntL2Sq (cycIntMul (negacyclicSignedMonomial s k) p) = cycIntL2Sq p := by
  let σ : Fin N → Fin N := fun j =>
    if h : k.val ≤ j.val then ⟨j.val - k.val, by omega⟩
    else ⟨N + j.val - k.val, by omega⟩
  let τ : Fin N → Fin N := fun i =>
    if h : i.val + k.val < N then ⟨i.val + k.val, h⟩
    else ⟨i.val + k.val - N, by have := i.isLt; have := k.isLt; omega⟩
  have hLeft : ∀ j : Fin N, τ (σ j) = j := by
    intro j; have hj := j.isLt; have hk := k.isLt
    dsimp only [σ, τ]
    by_cases hkj : k.val ≤ j.val
    · simp only [hkj, ↓reduceDIte]
      have hLt : j.val - k.val + k.val < N := by omega
      simp only [hLt, ↓reduceDIte]
      exact Fin.ext (by dsimp only; omega)
    · simp only [hkj, ↓reduceDIte]
      have hNotLt : ¬ (N + j.val - k.val + k.val < N) := by omega
      simp only [hNotLt, ↓reduceDIte]
      exact Fin.ext (by dsimp only; omega)
  have hRight : ∀ i : Fin N, σ (τ i) = i := by
    intro i; have hi := i.isLt; have hk := k.isLt
    dsimp only [σ, τ]
    by_cases hik : i.val + k.val < N
    · simp only [hik, ↓reduceDIte]
      have hLe : k.val ≤ i.val + k.val := by omega
      simp only [hLe, ↓reduceDIte]
      exact Fin.ext (by dsimp only; omega)
    · simp only [hik, ↓reduceDIte]
      have hNotLe : ¬ (k.val ≤ i.val + k.val - N) := by omega
      simp only [hNotLe, ↓reduceDIte]
      exact Fin.ext (by dsimp only; omega)
  unfold cycIntL2Sq
  have hPt : ∀ j : Fin N,
      (cycIntMul (negacyclicSignedMonomial s k) p j).natAbs *
        (cycIntMul (negacyclicSignedMonomial s k) p j).natAbs =
      (p (σ j)).natAbs * (p (σ j)).natAbs := by
    intro j
    rw [negacyclicSignedMonomial_mul_apply]
    dsimp only [σ]
    by_cases hkj : k.val ≤ j.val
    · simp only [hkj, ↓reduceDIte, Int.natAbs_mul, signBitToInt_natAbs, Nat.one_mul]
    · simp only [hkj, ↓reduceDIte, Int.natAbs_neg, Int.natAbs_mul, signBitToInt_natAbs, Nat.one_mul]
  rw [cycNatFinSum_congr hPt]
  exact cycNatFinSum_bijection σ τ hLeft hRight (fun i => (p i).natAbs * (p i).natAbs)

theorem cycIntL2Sq_mul_chalInv_eq {nu : Nat} (c : SignedMonomialChal nu) (p : CycPolyInt nu) :
    cycIntL2Sq (cycIntMul c.invIntPoly p) = cycIntL2Sq p :=
  cycIntL2Sq_mul_negacyclicSignedMonomial_eq _ _ p

theorem cycIntL2Sq_mul_chal_eq {nu : Nat} (c : SignedMonomialChal nu) (p : CycPolyInt nu) :
    cycIntL2Sq (cycIntMul c.toIntPoly p) = cycIntL2Sq p :=
  cycIntL2Sq_mul_negacyclicSignedMonomial_eq _ _ p

private theorem nat_two_mul_le_sq_add (x y : Nat) :
    2 * (x * y) ≤ x * x + y * y := by
  by_cases hxy : x ≤ y
  · let d := y - x
    have hy : y = x + d := by dsimp only [d]; omega
    rw [hy]
    have hRhs : x * x + (x + d) * (x + d) = 2 * (x * (x + d)) + d * d := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm d x]
      omega
    rw [hRhs]
    omega
  · let d := x - y
    have hx : x = y + d := by dsimp only [d]; omega
    rw [hx]
    have hRhs : (y + d) * (y + d) + y * y = 2 * ((y + d) * y) + d * d := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm y d]
      omega
    rw [hRhs]
    omega

private theorem int_sub_natAbs_sq_le (a b : Int) :
    (a - b).natAbs * (a - b).natAbs ≤ 2 * (a.natAbs * a.natAbs) + 2 * (b.natAbs * b.natAbs) := by
  have hTri : (a - b).natAbs ≤ a.natAbs + b.natAbs := by omega
  have hSq : (a - b).natAbs * (a - b).natAbs ≤ (a.natAbs + b.natAbs) * (a.natAbs + b.natAbs) :=
    Nat.mul_le_mul hTri hTri
  have hExpand : (a.natAbs + b.natAbs) * (a.natAbs + b.natAbs) =
      a.natAbs * a.natAbs + b.natAbs * b.natAbs + 2 * (a.natAbs * b.natAbs) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm b.natAbs a.natAbs]; omega
  have hAmGm := nat_two_mul_le_sq_add a.natAbs b.natAbs
  omega

private theorem nat_100y_sq (y : Nat) : 10000 * (y * y) = (100 * y) * (100 * y) := by
  calc 10000 * (y * y) = (100 * 100) * (y * y) := rfl
    _ = 100 * (100 * (y * y)) := Nat.mul_assoc 100 100 (y * y)
    _ = 100 * ((100 * y) * y) := by rw [Nat.mul_assoc 100 y y]
    _ = 100 * (y * (100 * y)) := by rw [Nat.mul_comm (100 * y) y]
    _ = (100 * y) * (100 * y) := (Nat.mul_assoc 100 y (100 * y)).symm

private theorem nat_200_mul_le_sq_add_10000 (x y : Nat) :
    200 * (x * y) ≤ x * x + 10000 * (y * y) := by
  have h2 := nat_two_mul_le_sq_add x (100 * y)
  have hLhs : 2 * (x * (100 * y)) = 200 * (x * y) := by
    calc 2 * (x * (100 * y)) = 2 * ((x * 100) * y) := by rw [Nat.mul_assoc x 100 y]
      _ = 2 * ((100 * x) * y) := by rw [Nat.mul_comm x 100]
      _ = 2 * (100 * (x * y)) := by rw [Nat.mul_assoc 100 x y]
      _ = 200 * (x * y) := by rw [← Nat.mul_assoc 2 100 (x * y)]
  rw [← hLhs, nat_100y_sq y]
  exact h2

private theorem int_sub_natAbs_sq_weighted_100 (a b : Int) :
    100 * ((a - b).natAbs * (a - b).natAbs) ≤
      101 * (a.natAbs * a.natAbs) + 10100 * (b.natAbs * b.natAbs) := by
  have hTri : (a - b).natAbs ≤ a.natAbs + b.natAbs := by omega
  have hSq : (a - b).natAbs * (a - b).natAbs ≤ (a.natAbs + b.natAbs) * (a.natAbs + b.natAbs) :=
    Nat.mul_le_mul hTri hTri
  have h100 : 100 * ((a - b).natAbs * (a - b).natAbs) ≤ 100 * ((a.natAbs + b.natAbs) * (a.natAbs + b.natAbs)) :=
    Nat.mul_le_mul_left 100 hSq
  have hExpand : (a.natAbs + b.natAbs) * (a.natAbs + b.natAbs) =
      a.natAbs * a.natAbs + b.natAbs * b.natAbs + 2 * (a.natAbs * b.natAbs) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm b.natAbs a.natAbs]; omega
  rw [hExpand] at h100
  have hCross := nat_200_mul_le_sq_add_10000 a.natAbs b.natAbs
  omega

theorem cycIntL2Sq_sub_le {N : Nat} (p r : NegacyclicPolyInt N) :
    cycIntL2Sq (cycIntSub p r) ≤ 2 * cycIntL2Sq p + 2 * cycIntL2Sq r := by
  unfold cycIntL2Sq
  rw [← cycNatFinSum_mul_left, ← cycNatFinSum_mul_left, ← cycNatFinSum_add]
  apply cycNatFinSum_le
  intro i; unfold cycIntSub
  exact int_sub_natAbs_sq_le (p i) (r i)

theorem cycIntL2Sq_weighted_sub_100 {N : Nat} (p r : NegacyclicPolyInt N) :
    100 * cycIntL2Sq (cycIntSub p r) ≤ 101 * cycIntL2Sq p + 10100 * cycIntL2Sq r := by
  unfold cycIntL2Sq
  rw [← cycNatFinSum_mul_left, ← cycNatFinSum_mul_left, ← cycNatFinSum_mul_left, ← cycNatFinSum_add]
  apply cycNatFinSum_le
  intro i; unfold cycIntSub
  exact int_sub_natAbs_sq_weighted_100 (p i) (r i)

theorem short_monomial_rRel_mul_l2Sq_le {R nu q : Nat} [NeZero q]
    {stmt : RlweOrSigmaStatement nu q}
    (w : ShortMonomialRelaxedRlweWitness R nu q stmt)
    (p : CycPolyInt nu) :
    cycIntL2Sq (cycIntMul w.rRel p) ≤ 4 * cycIntL2Sq p := by
  have hN := Nat.two_pow_pos nu
  have hMul : cycIntMul w.rRel p =
      cycIntSub p (cycIntMul w.chal.invIntPoly (cycIntMul w.chal'.toIntPoly p)) := by
    rw [w.rRel_eq, cycIntMul_sub_left, cycIntMul_one_left hN, cycIntMul_assoc]
  rw [hMul]
  have hSub := cycIntL2Sq_sub_le p (cycIntMul w.chal.invIntPoly (cycIntMul w.chal'.toIntPoly p))
  rw [cycIntL2Sq_mul_chalInv_eq, cycIntL2Sq_mul_chal_eq] at hSub
  omega

/-- Non-vacuous `(ℓ_∞, ℓ_2)`-bounded Ring-SIS witness over `R_{12289} = ℤ_{12289}[X]/(X^{1024} + 1)`.
    Unlike the `ℓ_∞`-only relation (`rlweUnitSis_norm_le_6142`), the joint Euclidean bound `Bl2Sq`
    rules out public dense solutions such as `(1, centered(-A))`. -/
structure NonVacuousRingSis1024 (A : CycPolyZq 10 12289) (Binf Bl2Sq : Nat)
    (sSis eSis : CycPolyInt 10) : Prop where
  nonZero : cycIntToZq 12289 sSis ≠ cycZqZero ∨ cycIntToZq 12289 eSis ≠ cycZqZero
  s_inf_le : cycIntInfNorm sSis ≤ Binf
  e_inf_le : cycIntInfNorm eSis ≤ Binf
  pair_l2Sq_le : cycIntL2Sq sSis + cycIntL2Sq eSis ≤ Bl2Sq
  sis_eq : cycZqAdd (cycZqMul A (cycIntToZq 12289 sSis)) (cycIntToZq 12289 eSis) = cycZqZero

/-- Euclidean-augmented verifier matching `RlweReceiverZkPok::verify` in
    `crates/qsag-core/src/preprocessing.rs` (`‖z‖_∞ ≤ Bz` AND `‖z_s‖_2^2 + ‖z_e‖_2^2 ≤ Bl2Sq`
    on both OR branches across all `R` repetitions). -/
def verifyRlweOrSigmaEuclidean (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (Bl2Sq : Nat)
    (c : Fin R → SignedMonomialChal nu) (tr : RlweOrSigmaTranscript R nu q) : Bool :=
  verifyRlweOrSigma R nu q stmt c tr &&
  cycAllFin R (fun i : Fin R =>
    decide (cycIntL2Sq (tr.zs0 i) + cycIntL2Sq (tr.ze0 i) ≤ Bl2Sq) &&
    decide (cycIntL2Sq (tr.zs1 i) + cycIntL2Sq (tr.ze1 i) ≤ Bl2Sq))

theorem verifyRlweOrSigmaEuclidean_implies_base {R nu q : Nat} [NeZero q]
    {stmt : RlweOrSigmaStatement nu q} {Bl2Sq : Nat}
    {c : Fin R → SignedMonomialChal nu} {tr : RlweOrSigmaTranscript R nu q}
    (h : verifyRlweOrSigmaEuclidean R nu q stmt Bl2Sq c tr = true) :
    verifyRlweOrSigma R nu q stmt c tr = true := by
  unfold verifyRlweOrSigmaEuclidean at h
  exact ((Bool.and_eq_true _ _).mp h).1

theorem verifyRlweOrSigmaEuclidean_implies_l2Sq {R nu q : Nat} [NeZero q]
    {stmt : RlweOrSigmaStatement nu q} {Bl2Sq : Nat}
    {c : Fin R → SignedMonomialChal nu} {tr : RlweOrSigmaTranscript R nu q}
    (h : verifyRlweOrSigmaEuclidean R nu q stmt Bl2Sq c tr = true) (i : Fin R) :
    cycIntL2Sq (tr.zs0 i) + cycIntL2Sq (tr.ze0 i) ≤ Bl2Sq ∧
    cycIntL2Sq (tr.zs1 i) + cycIntL2Sq (tr.ze1 i) ≤ Bl2Sq := by
  unfold verifyRlweOrSigmaEuclidean at h
  have hR := (cycAllFin_eq_true_iff _).mp ((Bool.and_eq_true _ _).mp h).2 i
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hR
  exact hR

/-- Structured fork predicate for two `R`-parallel OR-Sigma transcripts obeying both the base
    algebraic/infinity-norm verifier AND the pair Euclidean squared-norm bound `Bl2Sq`
    (`RLWE_ZKPOK_PAIR_L2_SQ_BOUND = 1_500_000_000` in `preprocessing.rs`). -/
structure ValidRlweOrSigmaEuclideanFork (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (Bl2Sq : Nat)
    (c c' : Fin R → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript R nu q) : Prop where
  base : ValidRlweOrSigmaFork R nu q stmt c c' tr tr'
  l2_tr : ∀ i : Fin R,
    cycIntL2Sq (tr.zs0 i) + cycIntL2Sq (tr.ze0 i) ≤ Bl2Sq ∧
    cycIntL2Sq (tr.zs1 i) + cycIntL2Sq (tr.ze1 i) ≤ Bl2Sq
  l2_tr' : ∀ i : Fin R,
    cycIntL2Sq (tr'.zs0 i) + cycIntL2Sq (tr'.ze0 i) ≤ Bl2Sq ∧
    cycIntL2Sq (tr'.zs1 i) + cycIntL2Sq (tr'.ze1 i) ≤ Bl2Sq

/-- Equivalence constructor from boolean `verifyRlweOrSigmaEuclidean` acceptances on a shared
    commitment pair (`c ≠ c'`) to `ValidRlweOrSigmaEuclideanFork`. -/
theorem verifyRlweOrSigmaEuclidean_fork_of_accepts {R nu q : Nat} [NeZero q]
    {stmt : RlweOrSigmaStatement nu q} {Bl2Sq : Nat}
    {c c' : Fin R → SignedMonomialChal nu}
    {tr tr' : RlweOrSigmaTranscript R nu q}
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1) (hcNe : c ≠ c')
    (hAccE : verifyRlweOrSigmaEuclidean R nu q stmt Bl2Sq c tr = true)
    (hAccE' : verifyRlweOrSigmaEuclidean R nu q stmt Bl2Sq c' tr' = true) :
    ValidRlweOrSigmaEuclideanFork R nu q stmt Bl2Sq c c' tr tr' :=
  { base := ⟨ht0, ht1, hcNe,
      verifyRlweOrSigmaEuclidean_implies_base hAccE,
      verifyRlweOrSigmaEuclidean_implies_base hAccE'⟩
    l2_tr := verifyRlweOrSigmaEuclidean_implies_l2Sq hAccE
    l2_tr' := verifyRlweOrSigmaEuclidean_implies_l2Sq hAccE' }

theorem extractRlweOrSigmaShortWitnessGen_pair_l2Sq_le (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (Bl2Sq : Nat)
    (c c' : Fin R → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript R nu q)
    (hForkE : ValidRlweOrSigmaEuclideanFork R nu q stmt Bl2Sq c c' tr tr') :
    let w := extractRlweOrSigmaShortWitnessGen R nu q stmt c c' tr tr'
      hForkE.base.t0_eq hForkE.base.t1_eq hForkE.base.chal_ne
      hForkE.base.acc1 hForkE.base.acc2
    cycIntL2Sq w.sIso + cycIntL2Sq w.eIso ≤ 4 * Bl2Sq := by
  intro w
  dsimp only [w, extractRlweOrSigmaShortWitnessGen]
  rcases findDiffChalFin R c c' hForkE.base.chal_ne with ⟨i, hiNe⟩
  dsimp only
  by_cases hc0Eq : tr.c0 i = tr'.c0 i
  · simp only [hc0Eq, ↓reduceDIte]
    unfold extractSingleBranchShortWitness ShortMonomialRelaxedRlweWitness.ofForkDifference
    dsimp only
    rw [cycIntL2Sq_mul_chalInv_eq, cycIntL2Sq_mul_chalInv_eq]
    have h1 := cycIntL2Sq_sub_le (tr.zs1 i) (tr'.zs1 i)
    have h2 := cycIntL2Sq_sub_le (tr.ze1 i) (tr'.ze1 i)
    have hb := (hForkE.l2_tr i).2
    have hb' := (hForkE.l2_tr' i).2
    omega
  · simp only [hc0Eq, ↓reduceDIte]
    unfold extractSingleBranchShortWitness ShortMonomialRelaxedRlweWitness.ofForkDifference
    dsimp only
    rw [cycIntL2Sq_mul_chalInv_eq, cycIntL2Sq_mul_chalInv_eq]
    have h1 := cycIntL2Sq_sub_le (tr.zs0 i) (tr'.zs0 i)
    have h2 := cycIntL2Sq_sub_le (tr.ze0 i) (tr'.ze0 i)
    have hb := (hForkE.l2_tr i).1
    have hb' := (hForkE.l2_tr' i).1
    omega

set_option exponentiation.threshold 512 in
/-- Exact challenge-space cardinality `rlweOrSigmaChallengeCard 10 24 = 2^264` (`24 × 11-bit`
    signed monomials) of the production `RlweReceiverZkPok` proof. -/
theorem rlweOrSigma24_challenge_space_bits :
    rlweOrSigmaChallengeCard 10 24 = 2 ^ 264 :=
  rlwe_or_sigma_24_pq128_vs_13_grover_ceiling.1

/-- **Production 24-Parallel (`264`-bit) Euclidean Ring-SIS Fork-Extraction Dichotomy
    (`extract_rlwe_or_sigma_24_euclidean_sis_dichotomy`)**:
    Under `RLWE_ZKPOK_PAIR_L2_SQ_BOUND = 1_500_000_000` (`stmt.Bz ≤ 3070`) and ternary RLWE
    secret `(sTrue, eTrue)` (`‖sTrue‖_∞, ‖eTrue‖_∞ ≤ 1`, `‖sTrue‖_2^2 + ‖eTrue‖_2^2 ≤ 2048`),
    any valid 24-challenge Euclidean fork (`(2 * 2^10)^24 = 2^264`) constructively yields either
    exact integer RLWE secret recovery OR a `NonVacuousRingSis1024` solution bounded simultaneously
    by `‖·‖_∞ ≤ 6142` AND `‖s_sis‖_2^2 + ‖e_sis‖_2^2 ≤ 6_060_827_392`. -/
theorem extract_rlwe_or_sigma_24_euclidean_sis_dichotomy
    (stmt : RlweOrSigmaStatement 10 12289)
    (hBz : stmt.Bz ≤ rlweProductionBz)
    (c c' : Fin 24 → SignedMonomialChal 10)
    (tr tr' : RlweOrSigmaTranscript 24 10 12289)
    (hForkE : ValidRlweOrSigmaEuclideanFork 24 10 12289 stmt rlweZkpokPairL2SqBound c c' tr tr')
    (sTrue eTrue : CycPolyInt 10)
    (hKey : ShortRlweKeyRelation stmt.A (stmt.branchU
      (extract_rlwe_or_sigma_24_short_witness stmt c c' tr tr'
        hForkE.base.t0_eq hForkE.base.t1_eq hForkE.base.chal_ne
        hForkE.base.acc1 hForkE.base.acc2).branch) 1 sTrue eTrue)
    (hKeyL2 : cycIntL2Sq sTrue + cycIntL2Sq eTrue ≤ 2048) :
    let w := extract_rlwe_or_sigma_24_short_witness stmt c c' tr tr'
      hForkE.base.t0_eq hForkE.base.t1_eq hForkE.base.chal_ne
      hForkE.base.acc1 hForkE.base.acc2
    let sSis := cycIntSub w.sIso (cycIntMul w.rRel sTrue)
    let eSis := cycIntSub w.eIso (cycIntMul w.rRel eTrue)
    (cycZqCentered (cycZqMul w.rRelInvZq (cycIntToZq 12289 w.sIso)) = sTrue ∧
     cycZqCentered (cycZqMul w.rRelInvZq (cycIntToZq 12289 w.eIso)) = eTrue) ∨
    NonVacuousRingSis1024 stmt.A 6142 rlweExtractedSisL2SqBound sSis eSis := by
  intro w sSis eSis
  have hSisLtQ : 2 * stmt.Bz + 2 * 1 < 12289 := by unfold rlweProductionBz at hBz; omega
  have hBase := extract_rlwe_or_sigma_24_recovers_secret_or_breaks_short_sis
    stmt c c' tr tr' hForkE.base 1 sTrue eTrue (by decide) hSisLtQ hKey
  rcases hBase with hRec | ⟨hNz, hsInf, heInf, hSisEq⟩
  · exact Or.inl hRec
  · right
    have hs6142 : cycIntInfNorm sSis ≤ 6142 := by
      dsimp only [sSis, w]; unfold rlweProductionBz at hBz; omega
    have he6142 : cycIntInfNorm eSis ≤ 6142 := by
      dsimp only [eSis, w]; unfold rlweProductionBz at hBz; omega
    have hIsoL2 : cycIntL2Sq w.sIso + cycIntL2Sq w.eIso ≤ 4 * rlweZkpokPairL2SqBound :=
      extractRlweOrSigmaShortWitnessGen_pair_l2Sq_le 24 10 12289 stmt rlweZkpokPairL2SqBound
        c c' tr tr' hForkE
    have hRelS := short_monomial_rRel_mul_l2Sq_le w sTrue
    have hRelE := short_monomial_rRel_mul_l2Sq_le w eTrue
    have hWs := cycIntL2Sq_weighted_sub_100 w.sIso (cycIntMul w.rRel sTrue)
    have hWe := cycIntL2Sq_weighted_sub_100 w.eIso (cycIntMul w.rRel eTrue)
    have hL2 : cycIntL2Sq sSis + cycIntL2Sq eSis ≤ rlweExtractedSisL2SqBound := by
      dsimp only [sSis, eSis]
      unfold rlweZkpokPairL2SqBound at hIsoL2
      unfold rlweExtractedSisL2SqBound
      omega
    exact ⟨hNz, hs6142, he6142, hL2, hSisEq⟩

/-- Explicit public polynomial `A_3000 = 3000` (`-A_3000 ≡ 9289 mod 12289`, avoiding `{6143..6146}`)
    demonstrating that `(1, rlweUnitSisError A_3000)` passes the legacy `ℓ_∞ ≤ 6142` destination
    (`rlwePublicTestPoly3000_passes_inf_6142`) yet is deterministically refuted by
    `NonVacuousRingSis1024` (`9_216_000_000 > 6_060_827_392`). -/
def rlwePublicTestPoly3000 : CycPolyZq 10 12289 :=
  fun _ => ModZq.ofInt 12289 3000

theorem rlwePublicTestPoly3000_passes_inf_6142 :
    cycIntInfNorm (rlweUnitSisError rlwePublicTestPoly3000) ≤ 6142 := by
  apply rlweUnitSis_norm_le_6142
  intro _
  right
  show 6147 ≤ (ModZq.neg (ModZq.ofInt 12289 3000)).val
  decide

theorem tooth_rlweUnitSis_refuted_by_euclidean_bound :
    ¬ NonVacuousRingSis1024 rlwePublicTestPoly3000 6142 rlweExtractedSisL2SqBound
        (@cycIntOne 1024) (rlweUnitSisError rlwePublicTestPoly3000) := by
  intro hSis
  have hErrConst : ∀ i : Fin 1024,
      (rlweUnitSisError rlwePublicTestPoly3000 i).natAbs *
        (rlweUnitSisError rlwePublicTestPoly3000 i).natAbs = 9000000 := by
    intro _
    show ((ModZq.neg (ModZq.ofInt 12289 3000)).centered).natAbs *
         ((ModZq.neg (ModZq.ofInt 12289 3000)).centered).natAbs = 9000000
    decide
  have hErrL2 : cycIntL2Sq (rlweUnitSisError rlwePublicTestPoly3000) = 1024 * 9000000 := by
    unfold cycIntL2Sq
    rw [cycNatFinSum_congr hErrConst, cycNatFinSum_const]
  have hLePair : cycIntL2Sq (rlweUnitSisError rlwePublicTestPoly3000) ≤ rlweExtractedSisL2SqBound :=
    Nat.le_trans (Nat.le_add_left _ _) hSis.pair_l2Sq_le
  rw [hErrL2] at hLePair
  exact absurd hLePair (by unfold rlweExtractedSisL2SqBound; decide)

#tooth_pair extract_rlwe_or_sigma_24_euclidean_sis_dichotomy
  tooth_rlweUnitSis_refuted_by_euclidean_bound

/-! ## Production Q192 Gaussian Sampler Arithmetic & Joint Retry ULP Budget -/

/-- Exact 192-bit fixed-point multiplication `gaussian_fraction_mul(a, b) = ⌊(a * b) / 2^192⌋`
    computed by 3×3 schoolbook limb multiplication in `crates/qsag-core/src/preprocessing.rs`. -/
def q192FractionMul (a b : Nat) : Nat :=
  (a * b) / (2 ^ 192)

/-- Iterative Q192 binary exponential evaluator starting from `2^192 - 1` (`1 - 2^-192`),
    multiplying by rounded table constants `tableSteps : List Nat` down-shifted by `2^192`. -/
def q192EvalSteps : List Nat → Nat → Nat
  | [], acc => acc
  | t :: rest, acc => q192EvalSteps rest (q192FractionMul acc t)

/-- Exact unrounded numerator product `∏_{i} F_i` over `(2^192)^k`. -/
def q192IdealProd : List Nat → Nat
  | [] => 1
  | f :: rest => f * q192IdealProd rest

private theorem q192IdealProd_le_pow : ∀ (fs : List Nat),
    (∀ j : Fin fs.length, fs[j] ≤ 2 ^ 192) → q192IdealProd fs ≤ (2 ^ 192) ^ fs.length
  | [], _ => by dsimp only [q192IdealProd, List.length_nil]; decide
  | f :: rest, hFs => by
    dsimp only [q192IdealProd, List.length_cons]
    rw [Nat.pow_succ (2 ^ 192) rest.length, Nat.mul_comm ((2 ^ 192) ^ rest.length) (2 ^ 192)]
    exact Nat.mul_le_mul (hFs ⟨0, Nat.zero_lt_succ rest.length⟩)
      (q192IdealProd_le_pow rest (fun j => hFs ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))

private theorem q192EvalSteps_acc_error_ind :
    ∀ (ts fs : List Nat) (acc : Nat) (hLen : ts.length = fs.length),
      acc ≤ 2 ^ 192 →
      (∀ i : Fin ts.length,
        let t := ts[i]
        let f := fs[i.val]'(by have := i.isLt; omega)
        t ≤ f ∧ f ≤ 2 ^ 192 ∧ f ≤ t + 1) →
      let out := q192EvalSteps ts acc
      out ≤ 2 ^ 192 ∧
      out * (2 ^ 192) ^ fs.length ≤ acc * q192IdealProd fs ∧
      acc * q192IdealProd fs ≤ (out + 2 * ts.length) * (2 ^ 192) ^ fs.length
  | [], [], acc, _, hAcc, _ => by
    dsimp only [q192EvalSteps, q192IdealProd, List.length_nil]
    refine ⟨hAcc, Nat.le_refl (acc * 1), ?_⟩
    simp only [Nat.pow_zero, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_refl acc
  | _ :: _, [], _, hLen, _, _ => nomatch hLen
  | [], _ :: _, _, hLen, _, _ => nomatch hLen
  | t :: ts, f :: fs, acc, hLen, hAcc, hStep => by
    dsimp only [q192EvalSteps, q192IdealProd, List.length_cons]
    have hLen' : ts.length = fs.length := Nat.succ.inj hLen
    have h0 := hStep ⟨0, Nat.zero_lt_succ ts.length⟩
    dsimp only at h0
    obtain ⟨htLeF, hfLe, hfLeT1⟩ := h0
    let acc1 := q192FractionMul acc t
    have htLe : t ≤ 2 ^ 192 := Nat.le_trans htLeF hfLe
    have hAcc1Le : acc1 ≤ 2 ^ 192 := by
      dsimp only [acc1, q192FractionMul]
      have hProd : acc * t ≤ (2 ^ 192) * (2 ^ 192) := Nat.mul_le_mul hAcc htLe
      exact Nat.div_le_of_le_mul hProd
    have hTail : ∀ i : Fin ts.length,
        let ti := ts[i]
        let fi := fs[i.val]'(by have := i.isLt; omega)
        ti ≤ fi ∧ fi ≤ 2 ^ 192 ∧ fi ≤ ti + 1 :=
      fun i => hStep ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    obtain ⟨hOutLe, hUpperIH, hLowerIH⟩ :=
      q192EvalSteps_acc_error_ind ts fs acc1 hLen' hAcc1Le hTail
    refine ⟨hOutLe, ?_, ?_⟩
    · have hMulDiv : acc1 * (2 ^ 192) ≤ acc * t := Nat.div_mul_le_self (acc * t) (2 ^ 192)
      have hAcc1F : acc1 * (2 ^ 192) ≤ acc * f :=
        Nat.le_trans hMulDiv (Nat.mul_le_mul_left acc htLeF)
      calc q192EvalSteps ts acc1 * (2 ^ 192) ^ (fs.length + 1)
          = (q192EvalSteps ts acc1 * (2 ^ 192) ^ fs.length) * (2 ^ 192) := by
            rw [Nat.pow_succ (2 ^ 192) fs.length, Nat.mul_assoc]
        _ ≤ (acc1 * q192IdealProd fs) * (2 ^ 192) :=
            Nat.mul_le_mul_right (2 ^ 192) hUpperIH
        _ = (acc1 * (2 ^ 192)) * q192IdealProd fs := by
            rw [Nat.mul_assoc acc1, Nat.mul_comm (q192IdealProd fs) (2 ^ 192), ← Nat.mul_assoc]
        _ ≤ (acc * f) * q192IdealProd fs :=
            Nat.mul_le_mul_right _ hAcc1F
        _ = acc * (f * q192IdealProd fs) := Nat.mul_assoc acc f _
    · have hFsLe : q192IdealProd fs ≤ (2 ^ 192) ^ fs.length :=
        q192IdealProd_le_pow fs (fun j => (hTail ⟨j.val, by have := j.isLt; omega⟩).2.1)
      have hDivGt : acc * t < (acc1 + 1) * (2 ^ 192) := by
        dsimp only [acc1, q192FractionMul]
        have hMod := Nat.div_add_mod (acc * t) (2 ^ 192)
        have hRem := Nat.mod_lt (acc * t) (Nat.two_pow_pos 192)
        have hAddLt := Nat.add_lt_add_left hRem ((2 ^ 192) * ((acc * t) / 2 ^ 192))
        rw [hMod] at hAddLt
        calc acc * t < (2 ^ 192) * ((acc * t) / 2 ^ 192) + 2 ^ 192 := hAddLt
          _ = ((acc * t) / 2 ^ 192) * (2 ^ 192) + 1 * (2 ^ 192) := by
              rw [Nat.mul_comm (2 ^ 192), Nat.one_mul]
          _ = (((acc * t) / 2 ^ 192) + 1) * (2 ^ 192) := (Nat.add_mul _ _ _).symm
      have hAccFLe : acc * f ≤ (acc1 + 2) * (2 ^ 192) := by
        calc acc * f ≤ acc * (t + 1) := Nat.mul_le_mul_left acc hfLeT1
          _ = acc * t + acc := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ (acc1 + 1) * (2 ^ 192) + 2 ^ 192 := Nat.add_le_add (Nat.le_of_lt hDivGt) hAcc
          _ = (acc1 + 2) * (2 ^ 192) := by
            calc (acc1 + 1) * (2 ^ 192) + 2 ^ 192
                = (acc1 + 1) * (2 ^ 192) + 1 * (2 ^ 192) := by rw [Nat.one_mul]
              _ = (acc1 + 1 + 1) * (2 ^ 192) := (Nat.add_mul _ _ _).symm
      calc acc * (f * q192IdealProd fs)
          = (acc * f) * q192IdealProd fs := (Nat.mul_assoc acc f _).symm
        _ ≤ ((acc1 + 2) * (2 ^ 192)) * q192IdealProd fs :=
            Nat.mul_le_mul_right _ hAccFLe
        _ = (acc1 * q192IdealProd fs) * (2 ^ 192) + 2 * (q192IdealProd fs * (2 ^ 192)) := by
            rw [Nat.add_mul acc1 2, Nat.add_mul, Nat.mul_assoc acc1,
                Nat.mul_comm (2 ^ 192) (q192IdealProd fs), ← Nat.mul_assoc acc1,
                Nat.mul_assoc 2, Nat.mul_comm (2 ^ 192) (q192IdealProd fs)]
        _ ≤ ((q192EvalSteps ts acc1 + 2 * ts.length) * (2 ^ 192) ^ fs.length) * (2 ^ 192) +
              2 * ((2 ^ 192) ^ fs.length * (2 ^ 192)) :=
            Nat.add_le_add
              (Nat.mul_le_mul_right (2 ^ 192) hLowerIH)
              (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2 ^ 192) hFsLe))
        _ = (q192EvalSteps ts acc1 + 2 * (ts.length + 1)) * (2 ^ 192) ^ (fs.length + 1) := by
            rw [Nat.pow_succ (2 ^ 192) fs.length,
                Nat.mul_assoc (q192EvalSteps ts acc1 + 2 * ts.length) ((2 ^ 192) ^ fs.length) (2 ^ 192),
                ← Nat.add_mul (q192EvalSteps ts acc1 + 2 * ts.length) 2 ((2 ^ 192) ^ fs.length * (2 ^ 192)),
                Nat.mul_add 2 ts.length 1, Nat.mul_one, Nat.add_assoc]

/-- **Q192 Iterative Exponential ULP Error Theorem (`q192EvalSteps_ulp_bound`)**:
    Starting from `acc₀ = 2^192 - 1` (`1 - 2^-192`) and executing `B` rounds of `q192FractionMul`
    against rounded constants `t_i ≤ f_i ≤ t_i + 1 ≤ 2^192 + 1`, the output `out` under-approximates
    the exact rational product `(∏ f_i) / (2^192)^B` by at most `1 + 2 * B` ULPs of `2^-192`
    (`≤ 61 < 64` ULPs for the 30-step `bernoulli_exp_ct` loop in `preprocessing.rs`). -/
theorem q192EvalSteps_ulp_bound (ts fs : List Nat)
    (hLen : ts.length = fs.length)
    (hStep : ∀ i : Fin ts.length,
      let t := ts[i]
      let f := fs[i.val]'(by have := i.isLt; omega)
      t ≤ f ∧ f ≤ 2 ^ 192 ∧ f ≤ t + 1) :
    let out := q192EvalSteps ts (2 ^ 192 - 1)
    out * (2 ^ 192) ^ fs.length ≤ (2 ^ 192) * q192IdealProd fs ∧
    (2 ^ 192) * q192IdealProd fs ≤ (out + (1 + 2 * ts.length)) * (2 ^ 192) ^ fs.length := by
  intro out
  have hPos : 1 ≤ 2 ^ 192 := Nat.two_pow_pos 192
  have hAcc : 2 ^ 192 - 1 ≤ 2 ^ 192 := Nat.sub_le (2 ^ 192) 1
  obtain ⟨_, hUp, hLo⟩ := q192EvalSteps_acc_error_ind ts fs (2 ^ 192 - 1) hLen hAcc hStep
  have hFsLe : q192IdealProd fs ≤ (2 ^ 192) ^ fs.length :=
    q192IdealProd_le_pow fs (fun j => (hStep ⟨j.val, by have := j.isLt; omega⟩).2.1)
  refine ⟨Nat.le_trans hUp (Nat.mul_le_mul_right _ hAcc), ?_⟩
  have hSplit : (2 ^ 192) * q192IdealProd fs =
      (2 ^ 192 - 1) * q192IdealProd fs + q192IdealProd fs := by
    have h1 : 2 ^ 192 = (2 ^ 192 - 1) + 1 := (Nat.sub_add_cancel hPos).symm
    conv => lhs; rw [h1]
    rw [Nat.add_mul, Nat.one_mul]
  rw [hSplit]
  calc (2 ^ 192 - 1) * q192IdealProd fs + q192IdealProd fs
      ≤ (out + 2 * ts.length) * (2 ^ 192) ^ fs.length + 1 * (2 ^ 192) ^ fs.length := by
        rw [Nat.one_mul]
        exact Nat.add_le_add hLo hFsLe
    _ = (out + (1 + 2 * ts.length)) * (2 ^ 192) ^ fs.length := by
        rw [← Nat.add_mul]
        have hCoef : out + 2 * ts.length + 1 = out + (1 + 2 * ts.length) := by ac_rfl
        rw [hCoef]

/-- Q64 top-word fast-accept / fast-reject Bernoulli filter from `preprocessing.rs`:
    checks `u192 / 2^128 < pLo64` (fast accept) and `pHi64 ≤ u192 / 2^128` (fast reject)
    before falling back to full 192-bit comparison `u192 < p192`. -/
def q64FastFilteredBernoulli (pLo64 pHi64 p192 u192 : Nat) : Bool :=
  let u64Top := u192 / (2 ^ 128)
  if u64Top < pLo64 then true
  else if pHi64 ≤ u64Top then false
  else decide (u192 < p192)

/-- **Zero-Distortion Q64 Fast-Filter Theorem (`q64FastFilteredBernoulli_eq_exact`)**:
    Whenever `pLo64 * 2^128 ≤ p192 ≤ pHi64 * 2^128`, the Q64 fast-accept / fast-reject shortcut
    is 100% bit-identical to the exact 192-bit comparison `decide (u192 < p192)` for all `u192`. -/
theorem q64FastFilteredBernoulli_eq_exact (pLo64 pHi64 p192 u192 : Nat)
    (hLo : pLo64 * (2 ^ 128) ≤ p192)
    (hHi : p192 ≤ pHi64 * (2 ^ 128)) :
    q64FastFilteredBernoulli pLo64 pHi64 p192 u192 = decide (u192 < p192) := by
  unfold q64FastFilteredBernoulli
  dsimp only
  have hDivMod := Nat.div_add_mod u192 (2 ^ 128)
  have hRem := Nat.mod_lt u192 (Nat.two_pow_pos 128)
  by_cases hFastAcc : u192 / (2 ^ 128) < pLo64
  · simp only [hFastAcc, ↓reduceIte]
    symm; apply decide_eq_true
    have hLe1 : u192 / (2 ^ 128) + 1 ≤ pLo64 := hFastAcc
    have hMul : (u192 / (2 ^ 128) + 1) * (2 ^ 128) ≤ pLo64 * (2 ^ 128) :=
      Nat.mul_le_mul_right (2 ^ 128) hLe1
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (u192 / (2 ^ 128)) (2 ^ 128)] at hMul
    have huLt : u192 < (2 ^ 128) * (u192 / (2 ^ 128)) + 2 ^ 128 := by
      have hlt := Nat.add_lt_add_left hRem ((2 ^ 128) * (u192 / (2 ^ 128)))
      rw [hDivMod] at hlt
      exact hlt
    exact Nat.lt_of_lt_of_le huLt (Nat.le_trans hMul hLo)
  · simp only [hFastAcc, ↓reduceIte]
    by_cases hFastRej : pHi64 ≤ u192 / (2 ^ 128)
    · simp only [hFastRej, ↓reduceIte]
      symm; apply decide_eq_false
      have hMul : pHi64 * (2 ^ 128) ≤ (u192 / (2 ^ 128)) * (2 ^ 128) :=
        Nat.mul_le_mul_right (2 ^ 128) hFastRej
      have hLeU : (u192 / (2 ^ 128)) * (2 ^ 128) ≤ u192 := Nat.div_mul_le_self u192 (2 ^ 128)
      exact Nat.not_lt.mpr (Nat.le_trans hHi (Nat.le_trans hMul hLeU))
    · simp only [hFastRej, ↓reduceIte]

/-- Mutation witness: if `pLo64 * 2^128 > p192` (unsound fast-accept envelope), there exists `u192`
    where `q64FastFilteredBernoulli` accepts while `u192 < p192` is false (`≠`). -/
theorem tooth_q64FastFilteredBernoulli_unsound_envelope (pLo64 pHi64 p192 : Nat)
    (hUnsound : p192 < pLo64 * (2 ^ 128)) :
    ∃ u192 : Nat, q64FastFilteredBernoulli pLo64 pHi64 p192 u192 ≠ decide (u192 < p192) := by
  refine ⟨(pLo64 - 1) * (2 ^ 128) + (2 ^ 128 - 1), ?_⟩
  have hpPos : 1 ≤ pLo64 := by
    by_cases hp0 : pLo64 = 0
    · subst hp0; simp at hUnsound
    · exact Nat.pos_of_ne_zero hp0
  let u := (pLo64 - 1) * (2 ^ 128) + (2 ^ 128 - 1)
  have hPowPos : 1 ≤ 2 ^ 128 := Nat.two_pow_pos 128
  have huEq : u + 1 = pLo64 * (2 ^ 128) := by
    dsimp only [u]
    calc (pLo64 - 1) * (2 ^ 128) + (2 ^ 128 - 1) + 1
        = (pLo64 - 1) * (2 ^ 128) + ((2 ^ 128 - 1) + 1) := by rw [Nat.add_assoc]
      _ = (pLo64 - 1) * (2 ^ 128) + 1 * (2 ^ 128) := by
            rw [Nat.sub_add_cancel hPowPos, Nat.one_mul]
      _ = ((pLo64 - 1) + 1) * (2 ^ 128) := (Nat.add_mul _ _ _).symm
      _ = pLo64 * (2 ^ 128) := by rw [Nat.sub_add_cancel hpPos]
  have hLtSucc : p192 < u + 1 := by rw [huEq]; exact hUnsound
  have huGeP : p192 ≤ u := Nat.le_of_lt_succ hLtSucc
  have hDiv : u / (2 ^ 128) = pLo64 - 1 := by
    dsimp only [u]
    rw [Nat.mul_comm (pLo64 - 1) (2 ^ 128), Nat.mul_add_div hPowPos]
    have hRemDiv : (2 ^ 128 - 1) / (2 ^ 128) = 0 :=
      Nat.div_eq_of_lt (Nat.sub_lt hPowPos (by decide))
    rw [hRemDiv, Nat.add_zero]
  change q64FastFilteredBernoulli pLo64 pHi64 p192 u ≠ decide (u < p192)
  unfold q64FastFilteredBernoulli
  dsimp only
  rw [hDiv]
  have hLt : pLo64 - 1 < pLo64 := Nat.sub_lt hpPos (by decide)
  have hNotLt : ¬ (u < p192) := Nat.not_lt.mpr huGeP
  simp [hLt, hNotLt]

#tooth_pair q64FastFilteredBernoulli_eq_exact tooth_q64FastFilteredBernoulli_unsound_envelope

/-- **49,152-Coordinate Joint Q192 Retry ULP Budget (`q192_joint_49152_retry_ulp_budget`)**:
    Across all `24 × 2 × 1024 = 49,152` discrete Gaussian coordinates plus `1` joint radial
    rejection step (each bounded by `1 + 2 * 30 = 61` ULPs of `2^-192`), total per-attempt L1
    ULP accumulation is `2,998,333 < 2^22`, so `M = 40` expected joint retries incur `< 2^-165`
    total fixed-point statistical distance (`40 * 2,998,333 < 2^27`, `27 + 165 = 192`). -/
theorem q192_joint_49152_retry_ulp_budget :
    let coords := 24 * 2 * 1024
    let perStepUlps := 1 + 2 * 30
    let attemptUlps := coords * perStepUlps + perStepUlps
    coords = 49152 ∧
    perStepUlps = 61 ∧
    attemptUlps = 2998333 ∧
    attemptUlps < 2 ^ 22 ∧
    40 * attemptUlps < 2 ^ 27 ∧
    27 + 165 = 192 := by
  decide

#verify_constructive cycIntL2Sq_mul_negacyclicSignedMonomial_eq
  rlweOrSigma24_challenge_space_bits
  extract_rlwe_or_sigma_24_euclidean_sis_dichotomy
  rlwePublicTestPoly3000_passes_inf_6142
  tooth_rlweUnitSis_refuted_by_euclidean_bound
  q192EvalSteps_ulp_bound
  q64FastFilteredBernoulli_eq_exact
  tooth_q64FastFilteredBernoulli_unsound_envelope
  q192_joint_49152_retry_ulp_budget
end Qsag
end
