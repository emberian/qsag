module
/-
# Threshold ML-DSA arithmetic, checked signing, TOPRF execution, and credential relations

Proved here, constructively:

* The 256-point negacyclic NTT with its inverse (`fips204InvNtt_ntt`, `fips204Ntt_invNtt`),
  field arithmetic, rounding identities, and a coset LDE that interpolates through the
  inverse NTT (`cosetLde204_ntt`) on a validated domain (`cosetDomain204_inhabited`).
* `mldsaVerify` is the parameterized algebraic core kept for the MIR bridge.
  `mldsaVerifyBytes204` is the standalone ML-DSA-44 verifier on wire bytes (SHAKE, ExpandA,
  SampleInBall, packing, strict signature and hint decoding); it fails closed when a
  rejection sampler exhausts its byte budget. Agreement with other implementations is an
  executed check, not a theorem.
* Signing consumes multiplication results through a transcript-computed sacrifice check
  (`rssSacrificedSignStep`): an accepted attempt equals the exact-product reference
  transition unless the challenge lies in a list of bad values fixed by the transcript
  (`rssSacrificedSignStep_refines`). `rssDurableSign204` reserves the aggregate nonce in a
  persistent ledger before anything is released and releases only a final signature;
  nonces of released signatures are pairwise distinct across signs, failed writes and
  crashes (`rssDurable204_released_nonces_distinct`).
* The DKG is a commit, freeze, reveal machine; after freezing, the share accepted at each
  position is fixed up to a hash collision (`dkg204_reveal_determined_at_freeze`).
* The TOPRF client output is derived through decoded holder messages at every
  multiplication of all 30 rounds, for the full-value transport unconditionally
  (`toprfActiveClient204_correct`) and for the digest transport up to a collision.
  `toprf_joint_view_simulation` gives one coin bijection for the input sharing and all
  gates together.

* The verification extension `F_q[X]/(X^6 - 7)` is a field: Frobenius acts on coordinates
  (`ext6Pow_frobenius`), every nonzero element has the executable inverse `ext6Inv`
  (`ext6Mul_inv_cancel`), products vanish only at zero (`ext6Mul_eq_zero`), and the modulus
  has no proper factorization (`ext6Modulus_irreducible`).

* Batching and folding coins of the multiplication check are extension elements; a
  discrepancy polynomial over the extension has at most degree-many roots among them
  (`rss_ext6_discrepancy_roots_le`).
* Replacing every key-expanded mask tape by an independent tape costs the number of keys
  times the single-key distinguishing bound (`prss_multi_key_hybrid`).

Companion security modules: `Qsag.ThresholdMlDsaSecurity` proves 3-party `(2, 3)` RSS
multiplication and repeated-sacrifice refinement (`rss3MulStep_recon`,
`rss3_repeated_sacrifice_pq256`, `rss_distributed_trace_refines_sacrificedSignStep`),
multi-attempt sealed-`w₁` abort-transcript zero-knowledge (`threshold_mldsa_abort_transcript_zk`),
and `ML-DSA-65`/`87` (`PQ128`) parameter bounds (`mlDsa_challenge_entropy_bounds`), while
`Qsag.BlindVcQromSecurity` proves `438`-repetition `BlindVC` QROM Fiat-Shamir soundness
(`blindVc_quantum128_qrom_fs_soundness`) and issuer `ML-DSA` root-attestation unforgeability
(`blindVc_presentation_reduces_to_issuer_mldsa`). The single-key PRF assumption on PRSS tape
expansion and Rust wire-bytes transcript equivalence remain external to the algebraic model.
-/

public import Qsag.Protocol.Threshold.MlDsa44Parameters
public import Qsag.Tactic.Prelude
public import Qsag.Spec.Refines
public import Qsag.Math.Goldilocks
public import Qsag.Math.Lattices
public import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
public import Qsag.Coding.Cwyz26
public import Qsag.Tactic.AssuranceKit
import Qsag.Math.Primality

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

/-! ### §1.4 Exact FIPS 204 `Power2Round`, `Decompose`, `MakeHint`, `UseHint` & `HighBits` Shift Lemma -/

/-- Exact NIST FIPS 204 `Power2Round(r)` (`Algorithm 35`, $d = 13$, $2^d = 8192$):
    returns `(r1, r0)` with `r0 ∈ (-4096, 4096]`. -/
@[expose] def power2Round (r : Fq204) : Nat × Int :=
  let low : Nat := r.val % 8192
  let r0 : Int := if 4096 < low then (low : Int) - 8192 else (low : Int)
  let r1 : Nat := ((r.val : Int) - r0).toNat / 8192
  (r1, r0)

/-- **`power2Round_reconstruct`**: for every $r \in \mathbb{Z}_q$, `power2Round r = (r1, r0)` satisfies
    $-2^{12} < r_0 \le 2^{12}$, $r_1 < 1024$, and exact integer reconstruction $r_1 \cdot 2^{13} + r_0 = r$. -/
theorem power2Round_reconstruct (r : Fq204) :
    -4096 < (power2Round r).2 ∧ (power2Round r).2 ≤ 4096 ∧ (power2Round r).1 < 1024 ∧
    (((power2Round r).1 : Int) * 8192 + (power2Round r).2 = (r.val : Int)) ∧
    Fq204.add (Fq204.mul (Fq204.ofNat (power2Round r).1) (Fq204.ofNat 8192))
              (Fq204.ofInt (power2Round r).2) = r := by
  have hr := r.isLt
  have hEqInt :
      -4096 < (power2Round r).2 ∧ (power2Round r).2 ≤ 4096 ∧
      (power2Round r).1 < 1024 ∧ (((power2Round r).1 : Int) * 8192 + (power2Round r).2 = (r.val : Int)) := by
    unfold power2Round
    unfold mldsaQ at hr
    dsimp only
    split <;> (refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
  refine ⟨hEqInt.1, hEqInt.2.1, hEqInt.2.2.1, hEqInt.2.2.2, ?_⟩
  let r1 := (power2Round r).1
  let r0 := (power2Round r).2
  have hRec : (r1 : Int) * 8192 + r0 = (r.val : Int) := hEqInt.2.2.2
  have hmul : Fq204.mul (Fq204.ofNat r1) (Fq204.ofNat 8192) = Fq204.ofInt ((r1 : Int) * 8192) := by
    have hmulNat : Fq204.mul (Fq204.ofNat r1) (Fq204.ofNat 8192) = Fq204.ofNat (r1 * 8192) := by
      apply Fq204.ext
      simp only [Fq204.mul_val, Fq204.ofNat_val, Nat.mod_mul_mod, Nat.mul_mod_mod]
    rw [hmulNat]
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val, Fq204.ofNat_val, Int.natCast_emod, Int.natCast_mul]
    rfl
  change Fq204.add (Fq204.mul (Fq204.ofNat r1) (Fq204.ofNat 8192)) (Fq204.ofInt r0) = r
  rw [hmul, Fq204.ofInt_add, hRec, Fq204.ofInt_nat]

/-- Exact NIST FIPS 204 `Decompose(r)` (`Algorithm 36`) for `ML-DSA-44`
    ($\gamma_2 = 95232, \alpha = 2\gamma_2 = 190464, m = 44$). -/
@[expose] def decompose (r : Fq204) : Nat × Int :=
  let rem : Nat := r.val % 190464
  let r0p : Int := if 95232 < rem then (rem : Int) - 190464 else (rem : Int)
  if (r.val : Int) - r0p = 8380416 then
    (0, r0p - 1)
  else
    (((r.val : Int) - r0p).toNat / 190464, r0p)

/-- Division-free 48-bit shift/multiply `decompose_ct` from `fips204_ntt.rs`
    (`M48_88 = (1 << 48) / 190464 + 1 = 1477838210`). -/
def decomposeCtSpec (r : Nat) : Nat × Int :=
  let m48 : Nat := 1477838210
  let qQuot : Nat := (r * m48) / 281474976710656
  let rem : Nat := r - qQuot * 190464
  let gtG2 : Bool := decide (95232 < rem)
  let r0Base : Int := if gtG2 then (rem : Int) - 190464 else (rem : Int)
  if (r : Int) - r0Base = 8380416 then
    (0, r0Base - 1)
  else
    (qQuot + (if gtG2 then 1 else 0), r0Base)

/-- **`decomposeCt_eq_decompose`**: division-free `decompose_ct` equals exact FIPS 204 `decompose`
    over all $8{,}380{,}417$ field elements. -/
theorem decomposeCt_eq_decompose (r : Fq204) :
    decomposeCtSpec r.val = decompose r := by
  have hr := r.isLt
  unfold decomposeCtSpec decompose mldsaQ at *
  dsimp only
  have hq : (r.val * 1477838210) / 281474976710656 = r.val / 190464 := by omega
  have hrem : r.val - (r.val / 190464) * 190464 = r.val % 190464 := by omega
  rw [hq, hrem]
  if hgt : 95232 < r.val % 190464 then
    simp only [hgt, decide_true, ↓reduceIte]
    split
    · rfl
    · congr 1; omega
  else
    simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · congr 1; omega

/-- FIPS 204 `HighBits(r)` (`Algorithm 37`, returning `r1 ∈ [0, 44)`). -/
def mldsaHighBits (r : Fq204) : Nat := (decompose r).1

/-- FIPS 204 `LowBits(r)` (`Algorithm 38`, returning `r0 ∈ [-95232, 95232]`). -/
def mldsaLowBits (r : Fq204) : Int := (decompose r).2

/-- **`decompose_reconstruct`**: exact reconstruction $r \equiv r_1 \cdot 2\gamma_2 + r_0 \pmod q$
    and norm bounds $r_1 < 44$, $-\gamma_2 \le r_0 \le \gamma_2$. -/
theorem decompose_reconstruct (r : Fq204) :
    mldsaHighBits r < 44 ∧
    -95232 ≤ mldsaLowBits r ∧ mldsaLowBits r ≤ 95232 ∧
    (mldsaHighBits r ≠ 0 → -95232 < mldsaLowBits r) ∧
    Fq204.ofInt ((mldsaHighBits r : Int) * 190464 + mldsaLowBits r) = r := by
  have hr := r.isLt
  have hCore :
      mldsaHighBits r < 44 ∧
      -95232 ≤ mldsaLowBits r ∧ mldsaLowBits r ≤ 95232 ∧
      (mldsaHighBits r ≠ 0 → -95232 < mldsaLowBits r) ∧
      (((mldsaHighBits r : Int) * 190464 + mldsaLowBits r = (r.val : Int)) ∨
       ((mldsaHighBits r : Int) * 190464 + mldsaLowBits r = (r.val : Int) - 8380417)) := by
    unfold mldsaHighBits mldsaLowBits decompose
    unfold mldsaQ at hr
    dsimp only
    split <;> split <;> dsimp only <;> (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  refine ⟨hCore.1, hCore.2.1, hCore.2.2.1, hCore.2.2.2.1, ?_⟩
  rcases hCore.2.2.2.2 with hExact | hWrap
  · rw [hExact, Fq204.ofInt_nat]
  · rw [hWrap]
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val]; unfold mldsaQ at hr ⊢
    rw [← Int.add_emod_right _ ((8380417 : Nat) : Int)]
    have hCancel : (r.val : Int) - 8380417 + ((8380417 : Nat) : Int) = (r.val : Int) := by omega
    rw [hCancel]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Interior uniqueness of `decompose`: any representation $u_1 \cdot 2\gamma_2 + u_0 \pmod q$
    with $u_1 < 44$ and $-95232 < u_0 \le 95232$ (or $u_1 = 0, u_0 = -95232$) uniquely determines
    `decompose = (u1, u0)`. -/
theorem decompose_ofInt_interior {u1 : Nat} {u0 : Int}
    (hu1 : u1 < 44) (hu0Lo : -95232 < u0 ∨ (u1 = 0 ∧ u0 = -95232)) (hu0Hi : u0 ≤ 95232) :
    decompose (Fq204.ofInt ((u1 : Int) * 190464 + u0)) = (u1, u0) := by
  if hCorner : (u1 = 0 ∧ u0 = -95232) ∨ (u1 = 0 ∧ u0 = -1) then
    rcases hCorner with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  else
    have hu0Strict : -95232 < u0 := by
      rcases hu0Lo with h | h
      · exact h
      · exact absurd (Or.inl h) hCorner
    clear hu0Lo
    have hv : ((Fq204.ofInt ((u1 : Int) * 190464 + u0)).val : Int) =
        ((u1 : Int) * 190464 + u0) % (8380417 : Int) := Fq204.ofInt_val _
    unfold decompose
    if hWrap : u1 = 0 ∧ u0 < 0 then
      rcases hWrap with ⟨hu1Zero, hu0Neg⟩
      subst hu1Zero
      have hu0NeM1 : u0 ≠ -1 := fun h => hCorner (Or.inr ⟨rfl, h⟩)
      clear hCorner
      have hu0LeMinus2 : u0 ≤ -2 := by omega
      simp only [Int.ofNat_zero, Int.zero_mul, Int.zero_add] at hv ⊢
      have hMod : u0 % (8380417 : Int) = 8380417 + u0 := by
        rw [← Int.add_emod_right u0 (8380417 : Int)]
        have hEq : u0 + (8380417 : Int) = 8380417 + u0 := by omega
        rw [hEq]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [hMod] at hv
      generalize (Fq204.ofInt u0).val = n at hv ⊢
      have hnDiv : n / 190464 = 43 := by omega
      have hgt : 95232 < n % 190464 := by omega
      have htop : (n : Int) - (((n % 190464 : Nat) : Int) - 190464) = 8380416 := by omega
      simp only [hgt, ↓reduceIte, htop]
      exact Prod.ext rfl (by omega)
    else
      have hNonneg : 0 ≤ (u1 : Int) * 190464 + u0 := by
        rcases Nat.eq_zero_or_pos u1 with h0 | hpos
        · have hu0nn : ¬ (u0 < 0) := fun h => hWrap ⟨h0, h⟩
          clear hWrap hCorner
          omega
        · clear hWrap hCorner
          omega
      clear hWrap hCorner
      have hMod : ((u1 : Int) * 190464 + u0) % (8380417 : Int) = (u1 : Int) * 190464 + u0 :=
        Int.emod_eq_of_lt hNonneg (by omega)
      rw [hMod] at hv
      generalize (Fq204.ofInt ((u1 : Int) * 190464 + u0)).val = n at hv ⊢
      dsimp only
      if hu0Pos : 0 ≤ u0 then
        have hngt : ¬ (95232 < n % 190464) := by omega
        have hntop : (n : Int) - ((n % 190464 : Nat) : Int) ≠ 8380416 := by omega
        simp only [hngt, ↓reduceIte, hntop]
        exact Prod.ext (by omega) (by omega)
      else
        have hgt : 95232 < n % 190464 := by omega
        have hntop : (n : Int) - (((n % 190464 : Nat) : Int) - 190464) ≠ 8380416 := by omega
        simp only [hgt, ↓reduceIte, hntop]
        exact Prod.ext (by omega) (by omega)

/-- **`centered_diff_lt_iff_lowBits_and_highBits`** (certifying `threshold_mldsa.rs` Phase 3):
    For any $r \in \mathbb{Z}_q$, $w_1 < 44$, and $B \le \gamma_2 = 95232$,
    $|(r - w_1 \cdot 2\gamma_2) \bmod^\pm q| < B$ holds if and only if
    $|\text{LowBits}(r)| < B \land \text{HighBits}(r) = w_1$. -/
theorem centered_diff_lt_iff_lowBits_and_highBits (r : Fq204) {w1 B : Nat}
    (hw1 : w1 < 44) (hB : B ≤ 95232) :
    Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat (w1 * 190464))) < B ↔
      (mldsaLowBits r).natAbs < B ∧ mldsaHighBits r = w1 := by
  have hw1Int : Fq204.ofNat (w1 * 190464) = Fq204.ofInt ((w1 : Int) * 190464) := by
    apply Fq204.ext; apply Int.ofNat_inj.mp
    rw [Fq204.ofInt_val, Fq204.ofNat_val, Int.natCast_emod, Int.natCast_mul]
    rfl
  constructor
  · intro hAbs
    let diff := Fq204.sub r (Fq204.ofNat (w1 * 190464))
    let d := Fq204.toCenteredInt diff
    have hdAbs : d.natAbs < B := by dsimp [d]; rwa [Fq204.toCenteredInt_natAbs]
    have hrEq : r = Fq204.ofInt ((w1 : Int) * 190464 + d) := by
      calc r = Fq204.add (Fq204.ofNat (w1 * 190464)) diff := by
            dsimp [diff]
            rw [Fq204.sub_eq_add_neg, Fq204.add_comm _ (Fq204.add r _),
                Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
      _ = Fq204.add (Fq204.ofInt ((w1 : Int) * 190464)) (Fq204.ofInt d) := by
            rw [hw1Int, Fq204.ofInt_toCenteredInt]
      _ = Fq204.ofInt ((w1 : Int) * 190464 + d) := Fq204.ofInt_add _ _
    have hdec := decompose_ofInt_interior hw1 (u0 := d) (Or.inl (by omega)) (by omega)
    rw [← hrEq] at hdec
    have h1 : mldsaHighBits r = w1 := congrArg Prod.fst hdec
    have h2 : mldsaLowBits r = d := congrArg Prod.snd hdec
    rw [h2]; exact ⟨hdAbs, h1⟩
  · rintro ⟨hLow, hHigh⟩
    obtain ⟨_, _, _, _, hRec⟩ := decompose_reconstruct r
    have hSub : Fq204.sub r (Fq204.ofNat (w1 * 190464)) = Fq204.ofInt (mldsaLowBits r) := by
      conv => lhs; rw [← hRec, hHigh, hw1Int, Fq204.ofInt_sub]
      congr 1; omega
    rw [hSub, ← Fq204.toCenteredInt_natAbs,
        Fq204.toCenteredInt_ofInt_eq (by omega) (by omega)]
    exact hLow

/-- FIPS 204 Lemma 1 corollary: whenever $|\text{LowBits}(w - cs_2)| < \gamma_2 - \beta$ and
    $|cs_2 \bmod^\pm q| \le \beta$, $\text{HighBits}(w - cs_2) = \text{HighBits}(w)$. -/
theorem highBits_sub_eq_of_lowBits_lt (w cs2 : Fq204) {beta : Nat}
    (hBeta : beta ≤ 95232)
    (hLow : (mldsaLowBits (Fq204.sub w cs2)).natAbs < 95232 - beta)
    (hCs2 : Fq204.centeredAbs cs2 ≤ beta) :
    mldsaHighBits (Fq204.sub w cs2) = mldsaHighBits w := by
  let u := Fq204.sub w cs2
  change (mldsaLowBits u).natAbs < 95232 - beta at hLow
  obtain ⟨hu1Lt, _, _, -, huRec⟩ := decompose_reconstruct u
  let e := Fq204.toCenteredInt cs2
  have heAbs : e.natAbs ≤ beta := by dsimp [e]; rwa [Fq204.toCenteredInt_natAbs]
  have hu0Bounds : -((95232 - beta : Nat) : Int) < mldsaLowBits u ∧
      mldsaLowBits u < ((95232 - beta : Nat) : Int) := by constructor <;> omega
  have heBounds : -(beta : Int) ≤ e ∧ e ≤ (beta : Int) := by constructor <;> omega
  have hwEq : w = Fq204.ofInt ((mldsaHighBits u : Int) * 190464 + (mldsaLowBits u + e)) := by
    calc w = Fq204.add u cs2 := by
          dsimp [u]
          rw [Fq204.sub_eq_add_neg, Fq204.add_assoc, Fq204.add_left_neg, Fq204.add_zero]
    _ = Fq204.add (Fq204.ofInt ((mldsaHighBits u : Int) * 190464 + mldsaLowBits u)) (Fq204.ofInt e) := by
          rw [huRec, Fq204.ofInt_toCenteredInt]
    _ = Fq204.ofInt ((mldsaHighBits u : Int) * 190464 + (mldsaLowBits u + e)) := by
          rw [Fq204.ofInt_add, Int.add_assoc]
  have hdecW := decompose_ofInt_interior hu1Lt (u0 := mldsaLowBits u + e) (Or.inl (by omega)) (by omega)
  rw [← hwEq] at hdecW
  exact (congrArg Prod.fst hdecW).symm

/-- Exact NIST FIPS 204 `MakeHint(z, r)` (`Algorithm 39`). -/
@[expose] def makeHint (z r : Fq204) : Bool :=
  decide (mldsaHighBits r ≠ mldsaHighBits (Fq204.add r z))

/-- Exact NIST FIPS 204 `UseHint(h, r)` (`Algorithm 40`, `ML-DSA-44` $m = 44$). -/
@[expose] def useHint (h : Bool) (r : Fq204) : Nat :=
  let (r1, r0) := decompose r
  if !h then r1
  else if 0 < r0 then
    if r1 + 1 = 44 then 0 else r1 + 1
  else
    if r1 = 0 then 43 else r1 - 1

/-- **Scalar FIPS 204 Supporting Hint Lemma (`useHint_makeHint_eq_highBits`)**:
    For every $u \in \mathbb{Z}_q$ with $|\text{LowBits}(u)| < \gamma_2$ and every $ct_0 \in \mathbb{Z}_q$
    with $|ct_0 \bmod^\pm q| < \gamma_2$,
    `useHint (makeHint (-ct0) (u + ct0)) (u + ct0) = mldsaHighBits u`. -/
theorem useHint_makeHint_eq_highBits (u ct0 : Fq204)
    (hLow : (mldsaLowBits u).natAbs < 95232)
    (hCt0 : Fq204.centeredAbs ct0 < 95232) :
    useHint (makeHint (Fq204.neg ct0) (Fq204.add u ct0)) (Fq204.add u ct0) = mldsaHighBits u := by
  have hCancel : Fq204.add (Fq204.add u ct0) (Fq204.neg ct0) = u := by
    rw [Fq204.add_assoc, Fq204.add_right_neg, Fq204.add_zero]
  unfold makeHint useHint
  rw [hCancel]
  obtain ⟨hu1Lt, _, _, -, huRec⟩ := decompose_reconstruct u
  let u1 := mldsaHighBits u
  let u0 := mldsaLowBits u
  let e := Fq204.toCenteredInt ct0
  have hu0Bounds : -95232 < u0 ∧ u0 < 95232 := by dsimp [u0]; constructor <;> omega
  have heAbs : e.natAbs < 95232 := by dsimp [e]; rwa [Fq204.toCenteredInt_natAbs]
  have heBounds : -95232 < e ∧ e < 95232 := by constructor <;> omega
  have hrEq : Fq204.add u ct0 = Fq204.ofInt ((u1 : Int) * 190464 + (u0 + e)) := by
    conv => lhs; rw [← huRec, ← Fq204.ofInt_toCenteredInt ct0]
    rw [Fq204.ofInt_add]; dsimp [u1, u0, e]; rw [Int.add_assoc]
  let s := u0 + e
  if hsMid : -95232 < s ∧ s ≤ 95232 then
    have hdecR : decompose (Fq204.add u ct0) = (u1, s) := by
      rw [hrEq]; exact decompose_ofInt_interior hu1Lt (Or.inl hsMid.1) hsMid.2
    have hr1 : mldsaHighBits (Fq204.add u ct0) = u1 := by unfold mldsaHighBits; rw [hdecR]
    change (let (r1, r0) := decompose (Fq204.add u ct0)
            if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
            else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
            else if r1 = 0 then 43 else r1 - 1) = u1
    rw [hdecR, hr1]
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte]
  else if hsHi : 95232 < s then
    clear hsMid
    let w0 := s - 190464
    have hw0Bounds : -95232 < w0 ∧ w0 < 0 := by dsimp [w0, s] at *; constructor <;> omega
    if hu1Top : u1 + 1 = 44 then
      have hu1Val : u1 = 43 := by omega
      have hrEqWrap : Fq204.add u ct0 = Fq204.ofInt (((0 : Nat) : Int) * 190464 + (w0 - 1)) := by
        rw [hrEq]; apply Fq204.ext; apply Int.ofNat_inj.mp
        rw [Fq204.ofInt_val, Fq204.ofInt_val]; unfold mldsaQ
        have hDiff : (u1 : Int) * 190464 + (u0 + e) =
            (((0 : Nat) : Int) * 190464 + (w0 - 1)) + ((8380417 : Nat) : Int) := by
          dsimp [w0, s] at *; omega
        rw [hDiff, Int.add_emod_right]
      have hdecR : decompose (Fq204.add u ct0) = (0, w0 - 1) := by
        rw [hrEqWrap]
        exact decompose_ofInt_interior (u1 := 0) (u0 := w0 - 1) (by omega)
          (by
            if hInt : -95232 < w0 - 1 then exact Or.inl hInt
            else exact Or.inr ⟨rfl, by omega⟩)
          (by omega)
      have hr1 : mldsaHighBits (Fq204.add u ct0) = 0 := by unfold mldsaHighBits; rw [hdecR]
      have hne : (0 : Nat) ≠ u1 := by omega
      have hnPos : ¬ (0 < w0 - 1) := by omega
      change (let (r1, r0) := decompose (Fq204.add u ct0)
              if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
              else if r1 = 0 then 43 else r1 - 1) = u1
      rw [hdecR, hr1, decide_eq_true hne]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnPos]
      omega
    else
      have hrEqCarry : Fq204.add u ct0 = Fq204.ofInt (((u1 + 1 : Nat) : Int) * 190464 + w0) := by
        rw [hrEq]; apply congrArg Fq204.ofInt; dsimp [w0, s]; omega
      have hdecR : decompose (Fq204.add u ct0) = (u1 + 1, w0) := by
        rw [hrEqCarry]
        exact decompose_ofInt_interior (u1 := u1 + 1) (u0 := w0) (by omega) (Or.inl hw0Bounds.1) (by omega)
      have hr1 : mldsaHighBits (Fq204.add u ct0) = u1 + 1 := by unfold mldsaHighBits; rw [hdecR]
      have hne : u1 + 1 ≠ u1 := by omega
      have hnPos : ¬ (0 < w0) := by omega
      have hnz : u1 + 1 ≠ 0 := by omega
      change (let (r1, r0) := decompose (Fq204.add u ct0)
              if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
              else if r1 = 0 then 43 else r1 - 1) = u1
      rw [hdecR, hr1, decide_eq_true hne]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnPos, hnz]
      omega
  else
    have hsLe : s ≤ -95232 :=
      Int.not_lt.mp (fun h => hsMid ⟨h, Int.not_lt.mp hsHi⟩)
    clear hsMid
    if hsExactZero : u1 = 0 ∧ s = -95232 then
      rcases hsExactZero with ⟨hu1Zero, hsEq⟩
      have hSumEq : u0 + e = -95232 := hsEq
      have hdecR : decompose (Fq204.add u ct0) = (0, -95232) := by
        rw [hrEq, hu1Zero, hSumEq]; decide
      have hr1 : mldsaHighBits (Fq204.add u ct0) = 0 := by unfold mldsaHighBits; rw [hdecR]
      change (let (r1, r0) := decompose (Fq204.add u ct0)
              if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
              else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
              else if r1 = 0 then 43 else r1 - 1) = u1
      rw [hdecR, hr1, hu1Zero]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.not_false, ↓reduceIte]
    else
      let w0 := s + 190464
      if hu1Zero : u1 = 0 then
        have hsNe : s ≠ -95232 := fun h => hsExactZero ⟨hu1Zero, h⟩
        clear hsExactZero
        have hsLt : s < -95232 := by omega
        have hw0Bounds : 0 < w0 ∧ w0 < 95232 := by dsimp [w0, s] at *; constructor <;> omega
        have hrEqBorrow : Fq204.add u ct0 = Fq204.ofInt (((43 : Nat) : Int) * 190464 + (w0 + 1)) := by
          rw [hrEq]; apply Fq204.ext; apply Int.ofNat_inj.mp
          rw [Fq204.ofInt_val, Fq204.ofInt_val]; unfold mldsaQ
          have hDiff : ((u1 : Int) * 190464 + (u0 + e)) + ((8380417 : Nat) : Int) =
              ((43 : Nat) : Int) * 190464 + (w0 + 1) := by
            dsimp [w0, s] at *; omega
          rw [← Int.add_emod_right ((u1 : Int) * 190464 + (u0 + e)) ((8380417 : Nat) : Int), hDiff]
        have hdecR : decompose (Fq204.add u ct0) = (43, w0 + 1) := by
          rw [hrEqBorrow]
          exact decompose_ofInt_interior (u1 := 43) (u0 := w0 + 1) (by omega) (Or.inl (by omega)) (by omega)
        have hr1 : mldsaHighBits (Fq204.add u ct0) = 43 := by unfold mldsaHighBits; rw [hdecR]
        have hne : (43 : Nat) ≠ u1 := by omega
        have hPos : 0 < w0 + 1 := by omega
        change (let (r1, r0) := decompose (Fq204.add u ct0)
                if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
                else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
                else if r1 = 0 then 43 else r1 - 1) = u1
        rw [hdecR, hr1, decide_eq_true hne]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPos]
        omega
      else
        clear hsExactZero
        have hw0Bounds : 0 < w0 ∧ w0 ≤ 95232 := by dsimp [w0, s] at *; constructor <;> omega
        have hrEqBorrow : Fq204.add u ct0 = Fq204.ofInt (((u1 - 1 : Nat) : Int) * 190464 + w0) := by
          rw [hrEq]; apply congrArg Fq204.ofInt; dsimp [w0, s]; omega
        have hdecR : decompose (Fq204.add u ct0) = (u1 - 1, w0) := by
          rw [hrEqBorrow]
          exact decompose_ofInt_interior (u1 := u1 - 1) (u0 := w0) (by omega) (Or.inl (by omega)) (by omega)
        have hr1 : mldsaHighBits (Fq204.add u ct0) = u1 - 1 := by unfold mldsaHighBits; rw [hdecR]
        have hne : u1 - 1 ≠ u1 := by omega
        have hPos : 0 < w0 := by omega
        have hnTop : (u1 - 1) + 1 ≠ 44 := by omega
        change (let (r1, r0) := decompose (Fq204.add u ct0)
                if !decide (mldsaHighBits (Fq204.add u ct0) ≠ u1) then r1
                else if 0 < r0 then if r1 + 1 = 44 then 0 else r1 + 1
                else if r1 = 0 then 43 else r1 - 1) = u1
        rw [hdecR, hr1, decide_eq_true hne]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPos, hnTop]
        omega

/-- **`#tooth` (`tooth_useHint_fails_when_ct0_ge_gamma2`)**:
    Dropping the `< γ_2` norm bound on `c * t0` breaks `UseHint` recovery even when
    `‖LowBits(u)‖_∞ < γ_2 - β` (`95000 < 95154`). -/
theorem tooth_useHint_fails_when_ct0_ge_gamma2 :
    let u : Fq204 := ⟨95000, by decide⟩
    let ct0 : Fq204 := ⟨95465, by decide⟩
    (mldsaLowBits u).natAbs < mldsa44Gamma2 - mldsa44Beta ∧
    mldsa44Gamma2 < Fq204.centeredAbs ct0 ∧
    useHint (makeHint (Fq204.neg ct0) (Fq204.add u ct0)) (Fq204.add u ct0) ≠ mldsaHighBits u := by
  decide

/-! #### Module-Lattice Lifting ($R_q^4$ & $R_q^{4 \times 4}$) & `highBits_az_sub_ct_eq_w1` -/

/-- `ML-DSA-44` length-4 module vector over $R_q = \mathbb{Z}_q[X]/(X^{256} + 1)$. -/
abbrev PolyVec4 := Fin 4 → Poly256

/-- `ML-DSA-44` $4 \times 4$ public matrix over $R_q$. -/
abbrev PolyMat4 := Fin 4 → Fin 4 → Poly256

def addVec4 (u v : PolyVec4) : PolyVec4 := fun i => PolyTree.add (u i) (v i)
def subVec4 (u v : PolyVec4) : PolyVec4 := fun i => PolyTree.sub (u i) (v i)
def negVec4 (u : PolyVec4) : PolyVec4 := fun i => PolyTree.neg (u i)
def mulPolyVec4 (c : Poly256) (v : PolyVec4) : PolyVec4 := fun i => negacyclicMul c (v i)

def matVecMul4 (A : PolyMat4) (v : PolyVec4) : PolyVec4 := fun i =>
  PolyTree.add
    (PolyTree.add (negacyclicMul (A i ⟨0, by decide⟩) (v ⟨0, by decide⟩))
                  (negacyclicMul (A i ⟨1, by decide⟩) (v ⟨1, by decide⟩)))
    (PolyTree.add (negacyclicMul (A i ⟨2, by decide⟩) (v ⟨2, by decide⟩))
                  (negacyclicMul (A i ⟨3, by decide⟩) (v ⟨3, by decide⟩)))

theorem matVecMul4_add (A : PolyMat4) (u v : PolyVec4) :
    matVecMul4 A (addVec4 u v) = addVec4 (matVecMul4 A u) (matVecMul4 A v) := by
  funext i
  dsimp only [matVecMul4, addVec4]
  rw [negacyclicMul_left_distrib, negacyclicMul_left_distrib,
      negacyclicMul_left_distrib, negacyclicMul_left_distrib,
      polyTree_add_add_comm (negacyclicMul _ (u ⟨0, _⟩)),
      polyTree_add_add_comm (negacyclicMul _ (u ⟨2, _⟩)),
      polyTree_add_add_comm (PolyTree.add _ _)]

theorem matVecMul4_mulPoly (A : PolyMat4) (c : Poly256) (v : PolyVec4) :
    matVecMul4 A (mulPolyVec4 c v) = mulPolyVec4 c (matVecMul4 A v) := by
  funext i
  dsimp only [matVecMul4, mulPolyVec4]
  have hSwapMul : ∀ x y z : Poly256, negacyclicMul x (negacyclicMul y z) =
      negacyclicMul y (negacyclicMul x z) := fun x y z => by
    rw [← negacyclicMul_assoc, negacyclicMul_comm x y, negacyclicMul_assoc]
  simp only [negacyclicMul_left_distrib, hSwapMul (A i _) c]

/-- Inductive tree of natural-number `HighBits` values ($2^d$ integers in $[0, 44)$). -/
inductive NatTree : Nat → Type where
  | leaf (n : Nat) : NatTree 0
  | branch {d : Nat} (lo hi : NatTree d) : NatTree (d + 1)
  deriving DecidableEq, Repr

/-- Inductive tree of boolean hint flags ($2^d$ bits). -/
inductive HintTree : Nat → Type where
  | leaf (b : Bool) : HintTree 0
  | branch {d : Nat} (lo hi : HintTree d) : HintTree (d + 1)
  deriving DecidableEq, Repr

def HintTree.weight : {d : Nat} → HintTree d → Nat
  | 0, .leaf b => if b then 1 else 0
  | _ + 1, .branch h0 h1 => weight h0 + weight h1

def power2RoundHighTree : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf r => .leaf (Fq204.ofNat ((power2Round r).1 * 8192))
  | _ + 1, .branch lo hi => .branch (power2RoundHighTree lo) (power2RoundHighTree hi)

def power2RoundLowTree : {d : Nat} → PolyTree d → PolyTree d
  | 0, .leaf r => .leaf (Fq204.ofInt (power2Round r).2)
  | _ + 1, .branch lo hi => .branch (power2RoundLowTree lo) (power2RoundLowTree hi)

theorem power2RoundTree_reconstruct : ∀ {d : Nat} (p : PolyTree d),
    PolyTree.add (power2RoundHighTree p) (power2RoundLowTree p) = p
  | 0, .leaf r => congrArg PolyTree.leaf <| by
    have hmul : Fq204.ofNat ((power2Round r).1 * 8192) =
        Fq204.mul (Fq204.ofNat (power2Round r).1) (Fq204.ofNat 8192) := by
      apply Fq204.ext; simp [Fq204.ofNat_val, Fq204.mul_val, Nat.mul_mod]
    rw [hmul]
    exact (power2Round_reconstruct r).2.2.2.2
  | _ + 1, .branch lo hi => by
    simp only [power2RoundHighTree, power2RoundLowTree, PolyTree.add, power2RoundTree_reconstruct]

def highBitsTree : {d : Nat} → PolyTree d → NatTree d
  | 0, .leaf r => .leaf (mldsaHighBits r)
  | _ + 1, .branch lo hi => .branch (highBitsTree lo) (highBitsTree hi)

def lowBitsNormTree : {d : Nat} → PolyTree d → Nat
  | 0, .leaf r => (mldsaLowBits r).natAbs
  | _ + 1, .branch lo hi => max (lowBitsNormTree lo) (lowBitsNormTree hi)

def makeHintTree : {d : Nat} → PolyTree d → PolyTree d → HintTree d
  | 0, .leaf z, .leaf r => .leaf (makeHint z r)
  | _ + 1, .branch z0 z1, .branch r0 r1 => .branch (makeHintTree z0 r0) (makeHintTree z1 r1)

def useHintTree : {d : Nat} → HintTree d → PolyTree d → NatTree d
  | 0, .leaf h, .leaf r => .leaf (useHint h r)
  | _ + 1, .branch h0 h1, .branch r0 r1 => .branch (useHintTree h0 r0) (useHintTree h1 r1)

theorem useHintTree_makeHintTree : ∀ {d : Nat} (u ct0 : PolyTree d),
    lowBitsNormTree u < 95232 →
    PolyTree.infNorm ct0 < 95232 →
    useHintTree (makeHintTree (PolyTree.neg ct0) (PolyTree.add u ct0)) (PolyTree.add u ct0) =
      highBitsTree u
  | 0, .leaf u, .leaf ct0, hLow, hCt0 =>
    congrArg NatTree.leaf (useHint_makeHint_eq_highBits u ct0 hLow hCt0)
  | _ + 1, .branch u0 u1, .branch c0 c1, hLow, hCt0 => by
    simp only [lowBitsNormTree, PolyTree.infNorm] at hLow hCt0
    simp only [PolyTree.neg, PolyTree.add, makeHintTree, useHintTree, highBitsTree,
      useHintTree_makeHintTree u0 c0 (by omega) (by omega),
      useHintTree_makeHintTree u1 c1 (by omega) (by omega)]

theorem highBitsTree_sub_eq_of_lowBits_lt : ∀ {d : Nat} (w cs2 : PolyTree d) {beta : Nat},
    beta ≤ 95232 →
    lowBitsNormTree (PolyTree.sub w cs2) < 95232 - beta →
    PolyTree.infNorm cs2 ≤ beta →
    highBitsTree (PolyTree.sub w cs2) = highBitsTree w
  | 0, .leaf w, .leaf cs2, _, hB, hLow, hCs2 =>
    congrArg NatTree.leaf (highBits_sub_eq_of_lowBits_lt w cs2 hB hLow hCs2)
  | _ + 1, .branch w0 w1, .branch c0 c1, _, hB, hLow, hCs2 => by
    simp only [PolyTree.sub, lowBitsNormTree, PolyTree.infNorm] at hLow hCs2
    simp only [PolyTree.sub, highBitsTree,
      highBitsTree_sub_eq_of_lowBits_lt w0 c0 hB (by omega) (by omega),
      highBitsTree_sub_eq_of_lowBits_lt w1 c1 hB (by omega) (by omega)]

def power2RoundHighVec4 (t : PolyVec4) : PolyVec4 := fun i => power2RoundHighTree (t i)
def power2RoundLowVec4 (t : PolyVec4) : PolyVec4 := fun i => power2RoundLowTree (t i)
def highBitsVec4 (v : PolyVec4) : Fin 4 → NatTree 8 := fun i => highBitsTree (v i)
def makeHintVec4 (z r : PolyVec4) : Fin 4 → HintTree 8 := fun i => makeHintTree (z i) (r i)
def useHintVec4 (h : Fin 4 → HintTree 8) (r : PolyVec4) : Fin 4 → NatTree 8 :=
  fun i => useHintTree (h i) (r i)

def infNormVec4 (v : PolyVec4) : Nat :=
  max (max (PolyTree.infNorm (v ⟨0, by decide⟩)) (PolyTree.infNorm (v ⟨1, by decide⟩)))
      (max (PolyTree.infNorm (v ⟨2, by decide⟩)) (PolyTree.infNorm (v ⟨3, by decide⟩)))

def lowBitsNormVec4 (v : PolyVec4) : Nat :=
  max (max (lowBitsNormTree (v ⟨0, by decide⟩)) (lowBitsNormTree (v ⟨1, by decide⟩)))
      (max (lowBitsNormTree (v ⟨2, by decide⟩)) (lowBitsNormTree (v ⟨3, by decide⟩)))

def hintWeightVec4 (h : Fin 4 → HintTree 8) : Nat :=
  HintTree.weight (h ⟨0, by decide⟩) + HintTree.weight (h ⟨1, by decide⟩) +
  HintTree.weight (h ⟨2, by decide⟩) + HintTree.weight (h ⟨3, by decide⟩)

/-- **Module-Lattice Verification Identity (`az_sub_ct1_eq_w_sub_cs2_add_ct0`)**:
    Over $R_q^4$, whenever $z = y + c \cdot s_1$, $w = A \cdot y$, and $t = A \cdot s_1 + s_2 = t_1 \cdot 2^d + t_0$,
    $A \cdot z - c \cdot (t_1 \cdot 2^d) = (w - c \cdot s_2) + c \cdot t_0$ identically. -/
theorem az_sub_ct1_eq_w_sub_cs2_add_ct0
    (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256) :
    let t := addVec4 (matVecMul4 A s1) s2
    let t1Scaled := power2RoundHighVec4 t
    let t0 := power2RoundLowVec4 t
    let w := matVecMul4 A y
    let z := addVec4 y (mulPolyVec4 c s1)
    subVec4 (matVecMul4 A z) (mulPolyVec4 c t1Scaled) =
      addVec4 (subVec4 w (mulPolyVec4 c s2)) (mulPolyVec4 c t0) := by
  intro t t1Scaled t0 w z
  have htSplit : addVec4 t1Scaled t0 = t := by
    funext i; exact power2RoundTree_reconstruct (t i)
  have hAz : matVecMul4 A z = addVec4 w (mulPolyVec4 c (matVecMul4 A s1)) := by
    dsimp [z, w]; rw [matVecMul4_add, matVecMul4_mulPoly]
  rw [hAz]
  funext i
  have htRow : PolyTree.add (t1Scaled i) (t0 i) = PolyTree.add (matVecMul4 A s1 i) (s2 i) :=
    congrFun htSplit i
  dsimp only [addVec4, subVec4, mulPolyVec4]
  apply poly256_add_left_cancel (a := negacyclicMul c (t1Scaled i))
  have hSubCancel : ∀ x y : Poly256, PolyTree.add y (PolyTree.sub x y) = x := fun x y => by
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm y, polyTree_add_assoc,
        polyTree_add_left_neg, polyTree_add_zero]
  rw [hSubCancel]
  have hRhs :
      PolyTree.add (negacyclicMul c (t1Scaled i))
        (PolyTree.add (PolyTree.sub (w i) (negacyclicMul c (s2 i))) (negacyclicMul c (t0 i))) =
      PolyTree.add (PolyTree.sub (w i) (negacyclicMul c (s2 i)))
        (negacyclicMul c (PolyTree.add (t1Scaled i) (t0 i))) := by
    rw [negacyclicMul_left_distrib, polyTree_add_comm (negacyclicMul c (t1Scaled i)),
        polyTree_add_assoc, polyTree_add_comm (negacyclicMul c (t0 i))]
  rw [hRhs, htRow, negacyclicMul_left_distrib,
      polyTree_add_comm (negacyclicMul c (matVecMul4 A s1 i)) (negacyclicMul c (s2 i)),
      ← polyTree_add_assoc, polyTree_add_comm (PolyTree.sub (w i) _), hSubCancel]

/-- **Flagship §1 Theorem — Exact `HighBits` Shift Lemma (`highBits_az_sub_ct_eq_w1`)**:
    Over $R_q = \mathbb{Z}_{8380417}[X]/(X^{256} + 1)$ (`ML-DSA-44`, $k = \ell = 4$), whenever
    $z = y + c \cdot s_1$, $w = A \cdot y$, $t = A \cdot s_1 + s_2$,
    $\|\text{LowBits}(w - c \cdot s_2)\|_\infty < \gamma_2 - \beta$, and $\|c \cdot t_0\|_\infty < \gamma_2$,
    `UseHint(MakeHint(-c*t0, w - c*s2 + c*t0), A*z - c*t1*2^d) = HighBits(w - c*s2)`. -/
theorem highBits_az_sub_ct_eq_w1
    (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256) (beta : Nat)
    (hLow : lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2)) < mldsa44Gamma2 - beta)
    (hCt0 : infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2))) < mldsa44Gamma2) :
    let t := addVec4 (matVecMul4 A s1) s2
    let t1Scaled := power2RoundHighVec4 t
    let t0 := power2RoundLowVec4 t
    let w := matVecMul4 A y
    let z := addVec4 y (mulPolyVec4 c s1)
    let u := subVec4 w (mulPolyVec4 c s2)
    let ct0 := mulPolyVec4 c t0
    useHintVec4 (makeHintVec4 (negVec4 ct0) (addVec4 u ct0))
                (subVec4 (matVecMul4 A z) (mulPolyVec4 c t1Scaled)) =
      highBitsVec4 u := by
  intro t t1Scaled t0 w z u ct0
  have hId := az_sub_ct1_eq_w_sub_cs2_add_ct0 A s1 s2 y c
  dsimp only at hId
  rw [hId]
  funext i
  have hFinCases : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    rcases i with ⟨idx, hidx⟩
    have hIdx : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hIdx with rfl | rfl | rfl | rfl <;> simp
  rcases hFinCases with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [useHintVec4, makeHintVec4, highBitsVec4, negVec4, addVec4, u, ct0, w, t0, t]
    unfold lowBitsNormVec4 mldsa44Gamma2 at hLow
    unfold infNormVec4 mldsa44Gamma2 at hCt0
    exact useHintTree_makeHintTree _ _ (by omega) (by omega)

def idMat4 : PolyMat4 :=
  fun i j => if i = j then PolyTree.constUnit 8 else PolyTree.zero 8

private theorem matVecMul4_idMat4 (v : PolyVec4) : matVecMul4 idMat4 v = v := by
  funext i
  have hFinCases : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    rcases i with ⟨idx, hidx⟩
    have hIdx : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hIdx with rfl | rfl | rfl | rfl <;> simp
  rcases hFinCases with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [matVecMul4, idMat4]
    simp only [↓reduceIte, Fin.mk.injEq, Nat.reduceEqDiff,
      negacyclicMul_one_left, negacyclicMul_zero_left,
      polyTree_add_zero, polyTree_zero_add]

/-- Cyclic coordinate shift: row `i` selects coordinate `i + 1`. Not the identity. -/
def shiftMat4 : PolyMat4 :=
  fun i j => if (i.val + 1) % 4 = j.val then PolyTree.constUnit 8 else PolyTree.zero 8

private theorem matVecMul4_shiftMat4_const (p : Poly256) :
    matVecMul4 shiftMat4 (fun _ => p) = fun _ => p := by
  funext i
  have hFinCases : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    rcases i with ⟨idx, hidx⟩
    have hIdx : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hIdx with rfl | rfl | rfl | rfl <;> simp
  rcases hFinCases with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [matVecMul4, shiftMat4]
    simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff,
      negacyclicMul_one_left, negacyclicMul_zero_left,
      polyTree_add_zero, polyTree_zero_add]

theorem shiftMat4_ne_idMat4 : shiftMat4 ≠ idMat4 := by
  intro h
  have h00 := congrFun (congrFun h ⟨0, by decide⟩) ⟨0, by decide⟩
  simp only [shiftMat4, idMat4, ↓reduceIte, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff] at h00
  exact absurd h00 (by decide)

def polyTreeConstLeaf : (d : Nat) → Fq204 → PolyTree d
  | 0, x => .leaf x
  | d + 1, x => .branch (polyTreeConstLeaf d x) (polyTreeConstLeaf d x)

private theorem polyTreeConstLeaf_zero_eq : ∀ (d : Nat), polyTreeConstLeaf d Fq204.zero = PolyTree.zero d
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.zero, polyTreeConstLeaf_zero_eq d]

private theorem polyTreeConstLeaf_add (a b : Fq204) : ∀ (d : Nat),
    PolyTree.add (polyTreeConstLeaf d a) (polyTreeConstLeaf d b) = polyTreeConstLeaf d (Fq204.add a b)
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.add, polyTreeConstLeaf_add a b d]

private theorem polyTreeConstLeaf_neg (a : Fq204) : ∀ (d : Nat),
    PolyTree.neg (polyTreeConstLeaf d a) = polyTreeConstLeaf d (Fq204.neg a)
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.neg, polyTreeConstLeaf_neg a d]

private theorem polyTreeConstLeaf_infNorm (a : Fq204) : ∀ (d : Nat),
    PolyTree.infNorm (polyTreeConstLeaf d a) = Fq204.centeredAbs a
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, PolyTree.infNorm, polyTreeConstLeaf_infNorm a d, Nat.max_self]

private theorem polyTreeConstLeaf_lowBitsNorm (a : Fq204) : ∀ (d : Nat),
    lowBitsNormTree (polyTreeConstLeaf d a) = (mldsaLowBits a).natAbs
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, lowBitsNormTree, polyTreeConstLeaf_lowBitsNorm a d, Nat.max_self]

private theorem polyTreeConstLeaf_power2RoundLow (a : Fq204) : ∀ (d : Nat),
    power2RoundLowTree (polyTreeConstLeaf d a) = polyTreeConstLeaf d (Fq204.ofInt (power2Round a).2)
  | 0 => rfl
  | d + 1 => by simp only [polyTreeConstLeaf, power2RoundLowTree, polyTreeConstLeaf_power2RoundLow a d]

private theorem polyTreeConstLeaf_hintWeight (z r : Fq204) : ∀ (d : Nat),
    HintTree.weight (makeHintTree (polyTreeConstLeaf d z) (polyTreeConstLeaf d r)) =
      (2 ^ d) * (if makeHint z r then 1 else 0)
  | 0 => by simp [polyTreeConstLeaf, makeHintTree, HintTree.weight]
  | d + 1 => by
    simp only [polyTreeConstLeaf, makeHintTree, HintTree.weight,
      polyTreeConstLeaf_hintWeight z r d, Nat.pow_succ]
    cases makeHint z r <;> simp <;> omega

/-- Non-vacuous inhabitedness witness for `highBits_az_sub_ct_eq_w1` with nonzero $A, s_1, s_2, y, c$. -/
theorem highBits_az_sub_ct_eq_w1_inhabited :
    ∃ (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256),
      c ≠ PolyTree.zero 8 ∧
      lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2)) < mldsa44Gamma2 - mldsa44Beta ∧
      infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2))) < mldsa44Gamma2 := by
  let p1 : Poly256 := polyTreeConstLeaf 8 Fq204.one
  let v1 : PolyVec4 := fun _ => p1
  refine ⟨idMat4, v1, v1, v1, PolyTree.constUnit 8, ?_, ?_, ?_⟩
  · decide
  · have hMv : matVecMul4 idMat4 v1 = v1 := matVecMul4_idMat4 v1
    have hMul : mulPolyVec4 (PolyTree.constUnit 8) v1 = v1 := by
      funext i; exact negacyclicMul_one_left (v1 i)
    rw [hMv, hMul]
    have hSub : subVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 Fq204.zero) := by
      funext i
      dsimp only [subVec4, v1]
      rw [polyTree_sub_eq_add_neg, polyTree_add_comm, polyTree_add_left_neg, polyTreeConstLeaf_zero_eq]
    rw [hSub]
    unfold lowBitsNormVec4
    dsimp only
    simp only [polyTreeConstLeaf_lowBitsNorm, Nat.max_self]
    decide
  · have hMv : matVecMul4 idMat4 v1 = v1 := matVecMul4_idMat4 v1
    rw [hMv]
    have hMul : ∀ w : PolyVec4, mulPolyVec4 (PolyTree.constUnit 8) w = w := fun w => by
      funext i; exact negacyclicMul_one_left (w i)
    rw [hMul]
    have hAdd : addVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 (Fq204.add Fq204.one Fq204.one)) := by
      funext i; exact polyTreeConstLeaf_add Fq204.one Fq204.one 8
    rw [hAdd]
    unfold infNormVec4 power2RoundLowVec4
    dsimp only
    simp only [polyTreeConstLeaf_power2RoundLow, polyTreeConstLeaf_infNorm, Nat.max_self]
    decide

/-! ## §2. 2-Phase Committed Threshold `ML-DSA-44` DKG & Aggregate Rejection-Barrier Security (`P0-05`–`P0-07`, `P1-09`) -/

/-! ### §2.1 Constructive Honest-Holder Coverage (`subset_honest_holder_exists`, `P0-07`) & Subset Intersection -/

def natMemBool (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => decide (x = y) || natMemBool x ys

private theorem natMemBool_eq_true_iff (x : Nat) :
    ∀ (l : List Nat), natMemBool x l = true ↔ x ∈ l
  | [] => by simp [natMemBool]
  | y :: ys => by
    simp only [natMemBool, Bool.or_eq_true, decide_eq_true_eq,
      natMemBool_eq_true_iff x ys, List.mem_cons]

private theorem natMemBool_eq_false_iff (x : Nat) (l : List Nat) :
    natMemBool x l = false ↔ x ∉ l := by
  constructor
  · intro hf hm
    rw [(natMemBool_eq_true_iff x l).mpr hm] at hf
    cases hf
  · intro hnm
    cases hb : natMemBool x l
    · rfl
    · exact False.elim (hnm ((natMemBool_eq_true_iff x l).mp hb))

private def eraseFirstNat (x : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseFirstNat x ys

private theorem eraseFirstNat_length_succ {x : Nat} :
    ∀ {l : List Nat}, natMemBool x l = true → (eraseFirstNat x l).length + 1 = l.length
  | [], h => by cases h
  | y :: ys, h => by
    dsimp only [eraseFirstNat]
    if hxy : x = y then
      simp [hxy]
    else
      simp only [natMemBool, decide_eq_false hxy, Bool.false_or] at h
      simp only [hxy, ↓reduceIte, List.length_cons]
      have ih := eraseFirstNat_length_succ h
      omega

private theorem natMemBool_eraseFirstNat_of_ne {z x : Nat} (hne : z ≠ x) :
    ∀ {l : List Nat}, natMemBool z l = true → natMemBool z (eraseFirstNat x l) = true
  | [], h => by cases h
  | y :: ys, h => by
    dsimp only [eraseFirstNat]
    if hxy : x = y then
      subst hxy
      simp only [natMemBool, decide_eq_false hne, Bool.false_or] at h
      simp [h]
    else
      simp only [hxy, ↓reduceIte, natMemBool]
      simp only [natMemBool, Bool.or_eq_true] at h
      rcases h with hzy | hTail
      · simp [hzy]
      · simp [natMemBool_eraseFirstNat_of_ne hne hTail]

private theorem natNodup_length_le_of_subset :
    ∀ {T : List Nat} (C : List Nat),
      T.Nodup →
      (∀ x ∈ T, natMemBool x C = true) →
      T.length ≤ C.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, C, hNodup, hSub => by
    rcases List.nodup_cons.mp hNodup with ⟨hxNotMem, hxsNodup⟩
    have hxMemC : natMemBool x C = true := hSub x (.head xs)
    have hLenC := eraseFirstNat_length_succ hxMemC
    have hSubTail : ∀ z ∈ xs, natMemBool z (eraseFirstNat x C) = true := by
      intro z hz
      have hzx : z ≠ x := fun hEq => hxNotMem (hEq ▸ hz)
      exact natMemBool_eraseFirstNat_of_ne hzx (hSub z (.tail x hz))
    have ih := natNodup_length_le_of_subset (eraseFirstNat x C) hxsNodup hSubTail
    simp only [List.length_cons]
    omega

/-- Constructive (`0 Classical.choice`) finder returning the first party in subset `T`
    outside corrupt set `C`. -/
def findHonestHolder (C : List Nat) : List Nat → Option Nat
  | [] => none
  | x :: xs => if natMemBool x C then findHonestHolder C xs else some x

theorem findHonestHolder_some_spec {C : List Nat} :
    ∀ {T : List Nat} {h : Nat},
      findHonestHolder C T = some h → h ∈ T ∧ h ∉ C
  | [], _, hEq => by cases hEq
  | x :: xs, h, hEq => by
    dsimp only [findHonestHolder] at hEq
    cases hb : natMemBool x C
    · rw [hb] at hEq
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hEq
      subst hEq
      exact ⟨.head xs, (natMemBool_eq_false_iff x C).mp hb⟩
    · rw [hb] at hEq
      simp only [↓reduceIte] at hEq
      obtain ⟨hInXs, hNotC⟩ := findHonestHolder_some_spec hEq
      exact ⟨.tail x hInXs, hNotC⟩

theorem findHonestHolder_none_spec {C : List Nat} :
    ∀ {T : List Nat},
      findHonestHolder C T = none → ∀ x ∈ T, natMemBool x C = true
  | [], _, _, hMem => nomatch hMem
  | x :: xs, hNone, z, hMem => by
    dsimp only [findHonestHolder] at hNone
    cases hb : natMemBool x C
    · rw [hb] at hNone; cases hNone
    · rw [hb] at hNone
      simp only [↓reduceIte] at hNone
      rcases List.mem_cons.mp hMem with rfl | hzXs
      · exact hb
      · exact findHonestHolder_none_spec hNone z hzXs

/-- Replicated subset share record $(s_{1,T}, s_{2,T}, t_T)$ verified locally by every honest holder of $T$. -/
structure SubsetShareRecord where
  s1 : PolyVec4
  s2 : PolyVec4
  publicT : PolyVec4

def polyVec4EqBool (u v : PolyVec4) : Bool :=
  decide (u ⟨0, by decide⟩ = v ⟨0, by decide⟩) &&
  decide (u ⟨1, by decide⟩ = v ⟨1, by decide⟩) &&
  decide (u ⟨2, by decide⟩ = v ⟨2, by decide⟩) &&
  decide (u ⟨3, by decide⟩ = v ⟨3, by decide⟩)

theorem polyVec4EqBool_eq_true_iff (u v : PolyVec4) :
    polyVec4EqBool u v = true ↔ u = v := by
  unfold polyVec4EqBool
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    funext i
    rcases i with ⟨idx, hidx⟩
    have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hCases with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rintro rfl
    exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- Local subset-share relation & $\ell_\infty$ bound checked by every honest holder of subset `T`. -/
def validSubsetShare (A : PolyMat4) (etaSub : Nat) (sh : SubsetShareRecord) : Bool :=
  polyVec4EqBool sh.publicT (addVec4 (matVecMul4 A sh.s1) sh.s2) &&
  decide (infNormVec4 sh.s1 ≤ etaSub) &&
  decide (infNormVec4 sh.s2 ≤ etaSub)

theorem validSubsetShare_eq_true_iff (A : PolyMat4) (etaSub : Nat) (sh : SubsetShareRecord) :
    validSubsetShare A etaSub sh = true ↔
      sh.publicT = addVec4 (matVecMul4 A sh.s1) sh.s2 ∧
      infNormVec4 sh.s1 ≤ etaSub ∧
      infNormVec4 sh.s2 ≤ etaSub := by
  unfold validSubsetShare
  simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff, decide_eq_true_eq, and_assoc]

/-- **Flagship §2.1 Theorem — Constructive Honest-Holder Coverage (`subset_honest_holder_exists`, `P0-07`)**:
    For every threshold configuration $(t, n)$ with $t \ge 1$ and $n \ge 2t - 1$, every corrupt list
    `C` (`C.Nodup`, `C.length ≤ t - 1`), and every replicated subset `T` (`T.Nodup`, `T.length = n - t + 1`):
    1. Constructive `findHonestHolder C T` (`0 Classical.choice`) returns `some h` with `h ∈ T ∧ h ∉ C`;
    2. Whenever every honest custodian `p ∉ C` enforces `validSubsetShare A etaSub sh = true` on the
       subsets `p ∈ T` it holds, subset `T` is guaranteed to satisfy both the linear relation
       `sh.publicT = A * sh.s1 + sh.s2` and the short-secret bounds `‖sh.s1‖_∞ ≤ etaSub ∧ ‖sh.s2‖_∞ ≤ etaSub`. -/
theorem subset_honest_holder_exists
    {t n : Nat} (ht : 1 ≤ t) (hn : 2 * t - 1 ≤ n)
    {C T : List Nat} (hCLen : C.length ≤ t - 1)
    (hTNodup : T.Nodup) (hTLen : T.length = n - t + 1)
    (A : PolyMat4) (etaSub : Nat) (sh : SubsetShareRecord) :
    (∃ h : Nat, findHonestHolder C T = some h ∧ h ∈ T ∧ h ∉ C) ∧
    ((∀ p : Nat, p ∈ T → p ∉ C → validSubsetShare A etaSub sh = true) →
      sh.publicT = addVec4 (matVecMul4 A sh.s1) sh.s2 ∧
      infNormVec4 sh.s1 ≤ etaSub ∧
      infNormVec4 sh.s2 ≤ etaSub) := by
  have hEx : ∃ h : Nat, findHonestHolder C T = some h ∧ h ∈ T ∧ h ∉ C := by
    cases hOpt : findHonestHolder C T with
    | some h =>
      obtain ⟨hInT, hNotC⟩ := findHonestHolder_some_spec hOpt
      exact ⟨h, rfl, hInT, hNotC⟩
    | none =>
      have hAll := findHonestHolder_none_spec hOpt
      have hLe := natNodup_length_le_of_subset C hTNodup hAll
      omega
  refine ⟨hEx, ?_⟩
  intro hHonestCheck
  rcases hEx with ⟨h, _, hInT, hNotC⟩
  exact (validSubsetShare_eq_true_iff A etaSub sh).mp (hHonestCheck h hInT hNotC)

/-- **`#tooth` (`tooth_dkg_2of2_lacks_honest_holder_coverage`)**:
    Violating $n \ge 2t - 1$ at $(t = 2, n = 2)$ ($2 < 2 \cdot 2 - 1 = 3$) shrinks replicated subsets to
    size $n - t + 1 = 1$, allowing 1 corrupt party `C = [0]` to monopolize subset `T = [0]` with
    zero honest holders (`findHonestHolder C T = none`) and forge an invalid relation $t_T \ne A s_1 + s_2$! -/
theorem tooth_dkg_2of2_lacks_honest_holder_coverage :
    let t := 2
    let n := 2
    let C : List Nat := [0]
    let T : List Nat := [0]
    let badShare : SubsetShareRecord := {
      s1 := fun _ => PolyTree.zero 8
      s2 := fun _ => PolyTree.zero 8
      publicT := fun _ => PolyTree.constUnit 8
    }
    n < 2 * t - 1 ∧
    C.Nodup ∧ C.length ≤ t - 1 ∧
    T.Nodup ∧ T.length = n - t + 1 ∧
    findHonestHolder C T = none ∧
    (∀ p : Nat, p ∈ T → p ∉ C → validSubsetShare idMat4 mldsa44Eta badShare = true) ∧
    badShare.publicT ≠ addVec4 (matVecMul4 idMat4 badShare.s1) badShare.s2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, ?_, ?_⟩
  · intro p hpT hpNotC
    rcases List.mem_singleton.mp hpT with rfl
    exact False.elim (hpNotC (.head []))
  · intro hEq
    have h0 := congrFun hEq ⟨0, by decide⟩
    have hMv := congrFun (matVecMul4_idMat4 (fun _ => PolyTree.zero 8)) ⟨0, by decide⟩
    dsimp only [addVec4] at h0
    rw [hMv, polyTree_add_zero] at h0
    revert h0; decide

/-- Constructive intersection witness for any two replicated subsets of size $n - t + 1$ when $n \ge 2t - 1$:
    `findCommonParty T₁ T₂` returns `some p` with `p ∈ T₁ ∧ p ∈ T₂` (certifying degree-2 cross-term coverage!). -/
def findCommonParty (T₁ T₂ : List Nat) : Option Nat :=
  findHonestHolder [] (T₁.filter (fun x => natMemBool x T₂))

theorem replicated_subsets_intersect
    {t n : Nat} (ht : 1 ≤ t) (hn : 2 * t - 1 ≤ n)
    {T₁ T₂ : List Nat}
    (h1Nodup : T₁.Nodup) (h2Nodup : T₂.Nodup)
    (h1Bounds : ∀ x ∈ T₁, x < n) (h2Bounds : ∀ x ∈ T₂, x < n)
    (h1Len : T₁.length = n - t + 1) (h2Len : T₂.length = n - t + 1) :
    ∃ p : Nat, p ∈ T₁ ∧ p ∈ T₂ := by
  cases hCommon : T₁.filter (fun x => natMemBool x T₂) with
  | cons p rest =>
    have hpMem : p ∈ T₁.filter (fun x => natMemBool x T₂) := by rw [hCommon]; exact .head rest
    rw [List.mem_filter] at hpMem
    exact ⟨p, hpMem.1, (natMemBool_eq_true_iff p T₂).mp hpMem.2⟩
  | nil =>
    have hDisj : ∀ a ∈ T₁, ∀ b ∈ T₂, a ≠ b := by
      intro a ha b hb hEq
      subst hEq
      have haFilt : a ∈ T₁.filter (fun x => natMemBool x T₂) :=
        List.mem_filter.mpr ⟨ha, (natMemBool_eq_true_iff a T₂).mpr hb⟩
      rw [hCommon] at haFilt
      cases haFilt
    have hAppNodup : (T₁ ++ T₂).Nodup := List.nodup_append.mpr ⟨h1Nodup, h2Nodup, hDisj⟩
    have hInRange : ∀ z ∈ T₁ ++ T₂, natMemBool z (List.range n) = true := by
      intro z hz
      rw [natMemBool_eq_true_iff, List.mem_range]
      rcases List.mem_append.mp hz with hz1 | hz2
      · exact h1Bounds z hz1
      · exact h2Bounds z hz2
    have hLe := natNodup_length_le_of_subset (List.range n) hAppNodup hInRange
    rw [List.length_append, List.length_range] at hLe
    omega

/-! ### §2.2 Exact 4-Bit Algebraic Nibble Rejection Circuit (`dkg_nibble_rejection_circuit_exact`, `P1-09`) -/

/-- Exact 4-bit MPC nibble circuit from `threshold_mldsa.rs:377-392` over `Fq204`,
    returning `(is15, coeff)` where `coeff = 2 - (nib mod 5)` for all `nib < 15`. -/
def dkgNibbleCircuit (b0 b1 b2 b3 : Fq204) : Fq204 × Fq204 :=
  let p01 := Fq204.mul b0 b1
  let p12 := Fq204.mul b1 b2
  let p23 := Fq204.mul b2 b3
  let or12 := Fq204.sub (Fq204.add b1 b2) p12
  let or01 := Fq204.sub (Fq204.add b0 b1) p01
  let atLeast10 := Fq204.mul b3 or12
  let lowPart := Fq204.mul b2 or01
  let is15 := Fq204.mul p01 p23
  let atLeast5 := Fq204.sub (Fq204.add b3 lowPart) (Fq204.mul b3 lowPart)
  let comp :=
    Fq204.add (Fq204.add b0 (Fq204.mul (Fq204.ofNat 2) b1))
              (Fq204.add (Fq204.mul (Fq204.ofNat 4) b2) (Fq204.mul (Fq204.ofNat 8) b3))
  let coeff :=
    Fq204.add (Fq204.sub (Fq204.ofNat 2) comp)
              (Fq204.mul (Fq204.ofNat 5) (Fq204.add atLeast5 atLeast10))
  (is15, coeff)

def nibbleBitsToFq204 (nib : Nat) : Fq204 × Fq204 × Fq204 × Fq204 :=
  (Fq204.ofNat (nib % 2),
   Fq204.ofNat ((nib / 2) % 2),
   Fq204.ofNat ((nib / 4) % 2),
   Fq204.ofNat ((nib / 8) % 2))

def evalNibbleCircuitNat (nib : Nat) : Fq204 × Fq204 :=
  let (b0, b1, b2, b3) := nibbleBitsToFq204 nib
  dkgNibbleCircuit b0 b1 b2 b3

/-- **Exact 4-Bit DKG Nibble Rejection & Uniformity Theorem (`dkg_nibble_rejection_circuit_exact`, `P1-09`)**:
    1. Over all 16 4-bit inputs `nib ∈ [0, 16)`, `is15 = 1 ↔ nib = 15` and `is15 = 0 ↔ nib < 15`;
    2. For all 15 accepted nibbles `nib < 15`, `coeff = Fq204.ofInt (2 - (nib % 5))` with
       `centeredAbs coeff ≤ mldsa44Eta` (`= 2`);
    3. Every target coefficient in `{-2, -1, 0, 1, 2}` has **exact multiplicity 3** across `[0, 15)`
       (zero modulo bias), whereas `#tooth` omitting `nib = 15` rejection admits `(evalNibbleCircuitNat 15).2 = -3`
       with `centeredAbs = 3 > mldsa44Eta`, violating the short-key norm bound! -/
theorem dkg_nibble_rejection_circuit_exact :
    (∀ nib : Fin 16,
      ((evalNibbleCircuitNat nib.val).1 = Fq204.one ↔ nib.val = 15) ∧
      ((evalNibbleCircuitNat nib.val).1 = Fq204.zero ↔ nib.val < 15) ∧
      (nib.val < 15 →
        (evalNibbleCircuitNat nib.val).2 = Fq204.ofInt (2 - ((nib.val % 5 : Nat) : Int)) ∧
        Fq204.centeredAbs (evalNibbleCircuitNat nib.val).2 ≤ mldsa44Eta)) ∧
    (∀ k ∈ ([-2, -1, 0, 1, 2] : List Int),
      ((List.range 15).filter (fun nib => decide ((evalNibbleCircuitNat nib).2 = Fq204.ofInt k))).length = 3) ∧
    ((evalNibbleCircuitNat 15).2 = Fq204.ofInt (-3) ∧
     mldsa44Eta < Fq204.centeredAbs (evalNibbleCircuitNat 15).2) := by
  decide

/-! ### §2.3 2-Phase Salted Commitment Anti-Rogue-Key Theorem (`dkg_phase2_commit_blocks_rogue_key`, `P0-05`) -/

/-- Canonical fixed-width byte encoding of a $2^d$-coefficient `PolyTree` (`4 * 2^d` bytes). -/
def encodePolyTreeBytes : {d : Nat} → PolyTree d → List UInt8
  | 0, .leaf x => encodeU32BeNat x.val
  | _ + 1, .branch l r => encodePolyTreeBytes l ++ encodePolyTreeBytes r

theorem encodePolyTreeBytes_length : ∀ {d : Nat} (p : PolyTree d),
    (encodePolyTreeBytes p).length = 4 * (2 ^ d)
  | 0, .leaf x => by simp [encodePolyTreeBytes, encodeU32BeNat_length]
  | d + 1, .branch l r => by
    simp only [encodePolyTreeBytes, List.length_append,
      encodePolyTreeBytes_length l, encodePolyTreeBytes_length r, Nat.pow_succ]
    omega

private theorem append_inj_of_eq_len {α : Type} :
    ∀ {l1 r1 l2 r2 : List α},
      l1.length = l2.length →
      l1 ++ r1 = l2 ++ r2 →
      l1 = l2 ∧ r1 = r2
  | [], r1, [], r2, _, hEq => ⟨rfl, hEq⟩
  | _ :: _, _, [], _, hLen, _ => by cases hLen
  | [], _, _ :: _, _, hLen, _ => by cases hLen
  | a :: l1, r1, b :: l2, r2, hLen, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    injection hEq with hHead hTail
    obtain ⟨hL, hR⟩ := append_inj_of_eq_len hLen hTail
    exact ⟨by rw [hHead, hL], hR⟩

theorem encodePolyTreeBytes_injective : ∀ {d : Nat} {p q : PolyTree d},
    encodePolyTreeBytes p = encodePolyTreeBytes q → p = q
  | 0, .leaf x, .leaf y, hEq => by
    dsimp only [encodePolyTreeBytes] at hEq
    have hxLt : x.val < 2 ^ 32 := Nat.lt_trans x.isLt (by decide)
    have hyLt : y.val < 2 ^ 32 := Nat.lt_trans y.isLt (by decide)
    have hDec := congrArg decodeU32BeNat hEq
    rw [decodeU32BeNat_encodeU32BeNat hxLt, decodeU32BeNat_encodeU32BeNat hyLt] at hDec
    injection hDec with hVal
    exact congrArg PolyTree.leaf (Fq204.ext hVal)
  | d + 1, .branch l1 r1, .branch l2 r2, hEq => by
    have hLen : (encodePolyTreeBytes l1).length = (encodePolyTreeBytes l2).length := by
      rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
    obtain ⟨hL, hR⟩ := append_inj_of_eq_len hLen hEq
    rw [encodePolyTreeBytes_injective hL, encodePolyTreeBytes_injective hR]

/-- Fixed 4096-byte canonical serialization of `PolyVec4` (`4 * 1024 = 4096` bytes). -/
def encodePolyVec4Bytes (v : PolyVec4) : List UInt8 :=
  encodePolyTreeBytes (v ⟨0, by decide⟩) ++
  encodePolyTreeBytes (v ⟨1, by decide⟩) ++
  encodePolyTreeBytes (v ⟨2, by decide⟩) ++
  encodePolyTreeBytes (v ⟨3, by decide⟩)

theorem encodePolyVec4Bytes_length (v : PolyVec4) :
    (encodePolyVec4Bytes v).length = 4096 := by
  unfold encodePolyVec4Bytes
  simp only [List.length_append, encodePolyTreeBytes_length]

theorem encodePolyVec4Bytes_injective {u v : PolyVec4}
    (hEq : encodePolyVec4Bytes u = encodePolyVec4Bytes v) : u = v := by
  unfold encodePolyVec4Bytes at hEq
  simp only [List.append_assoc] at hEq
  have hL0 : (encodePolyTreeBytes (u ⟨0, by decide⟩)).length =
      (encodePolyTreeBytes (v ⟨0, by decide⟩)).length := by
    rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
  obtain ⟨e0, r0⟩ := append_inj_of_eq_len hL0 hEq
  have hL1 : (encodePolyTreeBytes (u ⟨1, by decide⟩)).length =
      (encodePolyTreeBytes (v ⟨1, by decide⟩)).length := by
    rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
  obtain ⟨e1, r1⟩ := append_inj_of_eq_len hL1 r0
  have hL2 : (encodePolyTreeBytes (u ⟨2, by decide⟩)).length =
      (encodePolyTreeBytes (v ⟨2, by decide⟩)).length := by
    rw [encodePolyTreeBytes_length, encodePolyTreeBytes_length]
  obtain ⟨e2, e3⟩ := append_inj_of_eq_len hL2 r1
  have p0 := encodePolyTreeBytes_injective e0
  have p1 := encodePolyTreeBytes_injective e1
  have p2 := encodePolyTreeBytes_injective e2
  have p3 := encodePolyTreeBytes_injective e3
  funext i
  rcases i with ⟨idx, hidx⟩
  have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl
  · exact p0
  · exact p1
  · exact p2
  · exact p3

private theorem ite_true_of {α : Type} {c : Prop} [Decidable c] (h : c) (t e : α) :
    (if c then t else e) = t := by
  split <;> rename_i hc
  · rfl
  · exact False.elim (hc h)

private theorem ite_false_of {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (t e : α) :
    (if c then t else e) = e := by
  split <;> rename_i hc
  · exact False.elim (h hc)
  · rfl

/-- Exact little-endian `u64` frame body `(u64_le(f.len()) || f)*` matching
    `qsag_accel::keccak::cshake256_framed_xof` (`keccak.rs:281-284`). -/
def encodeFramesU64LeBody : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => (encodeNatLeBytes 8 f.length ++ f) ++ encodeFramesU64LeBody fs

/-- Exact little-endian `u64` framed slice list `u64_le(frames.len()) || (u64_le(f.len()) || f)*`
    matching `qsag_accel::keccak::cshake256_framed_xof` (`keccak.rs:280-284`). -/
def encodeFramesU64Le (frames : List (List UInt8)) : List UInt8 :=
  encodeNatLeBytes 8 frames.length ++ encodeFramesU64LeBody frames

private theorem encodeFramesU64LeBody_injective_of_len :
    ∀ {fs gs : List (List UInt8)},
      fs.length = gs.length →
      (∀ f ∈ fs, f.length < 256 ^ 8) →
      (∀ g ∈ gs, g.length < 256 ^ 8) →
      encodeFramesU64LeBody fs = encodeFramesU64LeBody gs →
      fs = gs
  | [], [], _, _, _, _ => rfl
  | f :: fs, g :: gs, hCnt, hfB, hgB, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hCnt
    dsimp only [encodeFramesU64LeBody] at hEq
    rw [List.append_assoc, List.append_assoc] at hEq
    have hL8 : (encodeNatLeBytes 8 f.length).length = (encodeNatLeBytes 8 g.length).length := by
      rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
    obtain ⟨hLenBytes, hRest⟩ := append_inj_of_eq_len hL8 hEq
    have hfLt : f.length < 256 ^ 8 := hfB f (.head fs)
    have hgLt : g.length < 256 ^ 8 := hgB g (.head gs)
    have hDec := congrArg decodeNatLeBytes hLenBytes
    rw [decodeNatLeBytes_encodeNatLeBytes 8 f.length hfLt,
        decodeNatLeBytes_encodeNatLeBytes 8 g.length hgLt] at hDec
    obtain ⟨hFG, hTail⟩ := append_inj_of_eq_len hDec hRest
    have hTailEq := encodeFramesU64LeBody_injective_of_len hCnt
      (fun x hx => hfB x (.tail f hx)) (fun y hy => hgB y (.tail g hy)) hTail
    rw [hFG, hTailEq]

theorem encodeFramesU64Le_injective {fs gs : List (List UInt8)}
    (hCntF : fs.length < 256 ^ 8) (hCntG : gs.length < 256 ^ 8)
    (hfB : ∀ f ∈ fs, f.length < 256 ^ 8)
    (hgB : ∀ g ∈ gs, g.length < 256 ^ 8)
    (hEq : encodeFramesU64Le fs = encodeFramesU64Le gs) : fs = gs := by
  unfold encodeFramesU64Le at hEq
  have hL8 : (encodeNatLeBytes 8 fs.length).length = (encodeNatLeBytes 8 gs.length).length := by
    rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
  obtain ⟨hCntBytes, hBodyEq⟩ := append_inj_of_eq_len hL8 hEq
  have hCntEq : fs.length = gs.length := by
    have hd := congrArg decodeNatLeBytes hCntBytes
    rwa [decodeNatLeBytes_encodeNatLeBytes 8 fs.length hCntF,
         decodeNatLeBytes_encodeNatLeBytes 8 gs.length hCntG] at hd
  exact encodeFramesU64LeBody_injective_of_len hCntEq hfB hgB hBodyEq

/-- Exact SP 800-185 + `u64_le` sponge preimage absorbed by `cshake256_framed_xof` (`keccak.rs:277-286`). -/
def cshake256FramedPreimage (customization : List UInt8) (frames : List (List UInt8)) : List UInt8 :=
  if customization = [] then
    encodeFramesU64Le frames
  else
    customizationPrefix customization ++ encodeFramesU64Le frames

/-- Concrete 32-byte `cshake256_framed_32` matching `qsag_accel::keccak::cshake256_framed_32` (`keccak.rs:291-295`). -/
def cshake256FramedBytes (customization : List UInt8) (frames : List (List UInt8)) : List UInt8 :=
  cshake256Bytes customization (encodeFramesU64Le frames)

theorem cshake256FramedBytes_eq_sponge (customization : List UInt8) (frames : List (List UInt8)) :
    cshake256FramedBytes customization frames =
      squeezeXofAux 32 (absorbPadded (padForRate
        (cshake256FramedPreimage customization frames)
        (if customization = [] then 0x1f else 0x04))) := by
  unfold cshake256FramedBytes cshake256FramedPreimage cshake256Bytes cshake256Xof
  rfl

@[simp] theorem cshake256FramedBytes_length (customization : List UInt8) (frames : List (List UInt8)) :
    (cshake256FramedBytes customization frames).length = 32 := by
  unfold cshake256FramedBytes
  exact cshake256Bytes_length customization (encodeFramesU64Le frames)

theorem cshake256FramedPreimage_frames_injective {customization : List UInt8}
    {fs gs : List (List UInt8)}
    (hCntF : fs.length < 256 ^ 8) (hCntG : gs.length < 256 ^ 8)
    (hfB : ∀ f ∈ fs, f.length < 256 ^ 8)
    (hgB : ∀ g ∈ gs, g.length < 256 ^ 8)
    (hEq : cshake256FramedPreimage customization fs = cshake256FramedPreimage customization gs) :
    fs = gs := by
  unfold cshake256FramedPreimage at hEq
  if hEmpty : customization = [] then
    rw [ite_true_of hEmpty, ite_true_of hEmpty] at hEq
    exact encodeFramesU64Le_injective hCntF hCntG hfB hgB hEq
  else
    rw [ite_false_of hEmpty, ite_false_of hEmpty] at hEq
    obtain ⟨_, hFrEq⟩ := append_inj_of_eq_len rfl hEq
    exact encodeFramesU64Le_injective hCntF hCntG hfB hgB hFrEq

/-- Little-endian `u32` (`v.to_le_bytes()`) polynomial serialization matching `threshold_mldsa.rs:615-618`. -/
def encodePolyTreeBytesLe : {d : Nat} → PolyTree d → List UInt8
  | 0, .leaf x => encodeNatLeBytes 4 x.val
  | _ + 1, .branch l r => encodePolyTreeBytesLe l ++ encodePolyTreeBytesLe r

theorem encodePolyTreeBytesLe_length : ∀ {d : Nat} (p : PolyTree d),
    (encodePolyTreeBytesLe p).length = 4 * (2 ^ d)
  | 0, .leaf x => by simp [encodePolyTreeBytesLe, encodeNatLeBytes_length]
  | d + 1, .branch l r => by
    simp only [encodePolyTreeBytesLe, List.length_append,
      encodePolyTreeBytesLe_length l, encodePolyTreeBytesLe_length r, Nat.pow_succ]
    omega

theorem encodePolyTreeBytesLe_injective : ∀ {d : Nat} {p q : PolyTree d},
    encodePolyTreeBytesLe p = encodePolyTreeBytesLe q → p = q
  | 0, .leaf x, .leaf y, hEq => by
    dsimp only [encodePolyTreeBytesLe] at hEq
    have hxLt : x.val < 256 ^ 4 := Nat.lt_trans x.isLt (by decide)
    have hyLt : y.val < 256 ^ 4 := Nat.lt_trans y.isLt (by decide)
    have hDec := congrArg decodeNatLeBytes hEq
    rw [decodeNatLeBytes_encodeNatLeBytes 4 x.val hxLt,
        decodeNatLeBytes_encodeNatLeBytes 4 y.val hyLt] at hDec
    exact congrArg PolyTree.leaf (Fq204.ext hDec)
  | _ + 1, .branch l1 r1, .branch l2 r2, hEq => by
    have hLen : (encodePolyTreeBytesLe l1).length = (encodePolyTreeBytesLe l2).length := by
      rw [encodePolyTreeBytesLe_length, encodePolyTreeBytesLe_length]
    obtain ⟨hL, hR⟩ := append_inj_of_eq_len hLen hEq
    rw [encodePolyTreeBytesLe_injective hL, encodePolyTreeBytesLe_injective hR]

/-- Fixed 4096-byte little-endian canonical serialization of `PolyVec4` (`threshold_mldsa.rs:615-618`). -/
def encodePolyVec4BytesLe (v : PolyVec4) : List UInt8 :=
  encodePolyTreeBytesLe (v ⟨0, by decide⟩) ++
  encodePolyTreeBytesLe (v ⟨1, by decide⟩) ++
  encodePolyTreeBytesLe (v ⟨2, by decide⟩) ++
  encodePolyTreeBytesLe (v ⟨3, by decide⟩)

theorem encodePolyVec4BytesLe_length (v : PolyVec4) :
    (encodePolyVec4BytesLe v).length = 4096 := by
  unfold encodePolyVec4BytesLe
  simp only [List.length_append, encodePolyTreeBytesLe_length]

theorem encodePolyVec4BytesLe_injective {u v : PolyVec4}
    (hEq : encodePolyVec4BytesLe u = encodePolyVec4BytesLe v) : u = v := by
  unfold encodePolyVec4BytesLe at hEq
  simp only [List.append_assoc] at hEq
  have hL0 : (encodePolyTreeBytesLe (u ⟨0, by decide⟩)).length =
      (encodePolyTreeBytesLe (v ⟨0, by decide⟩)).length := by
    rw [encodePolyTreeBytesLe_length, encodePolyTreeBytesLe_length]
  obtain ⟨e0, r0⟩ := append_inj_of_eq_len hL0 hEq
  have hL1 : (encodePolyTreeBytesLe (u ⟨1, by decide⟩)).length =
      (encodePolyTreeBytesLe (v ⟨1, by decide⟩)).length := by
    rw [encodePolyTreeBytesLe_length, encodePolyTreeBytesLe_length]
  obtain ⟨e1, r1⟩ := append_inj_of_eq_len hL1 r0
  have hL2 : (encodePolyTreeBytesLe (u ⟨2, by decide⟩)).length =
      (encodePolyTreeBytesLe (v ⟨2, by decide⟩)).length := by
    rw [encodePolyTreeBytesLe_length, encodePolyTreeBytesLe_length]
  obtain ⟨e2, e3⟩ := append_inj_of_eq_len hL2 r1
  have p0 := encodePolyTreeBytesLe_injective e0
  have p1 := encodePolyTreeBytesLe_injective e1
  have p2 := encodePolyTreeBytesLe_injective e2
  have p3 := encodePolyTreeBytesLe_injective e3
  funext ⟨idx, hidx⟩
  have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl
  · exact p0
  · exact p1
  · exact p2
  · exact p3

/-- Degree-6 verification extension field $\mathbb{F}_q[X]/(X^6 - 7)$ (`EXT_DEGREE = 6`, `EXT_NONRESIDUE = 7`,
    `rss_mpc.rs:52-56`) used by `rss_mpc::Engine` batch inner-product multiplication verification. -/
structure Ext6Fq204 where
  a0 : Fq204
  a1 : Fq204
  a2 : Fq204
  a3 : Fq204
  a4 : Fq204
  a5 : Fq204
  deriving DecidableEq, Repr

def ext6Zero : Ext6Fq204 := ⟨Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩
def ext6Nonresidue : Fq204 := Fq204.ofNat 7

def ext6EmbedFq (x : Fq204) : Ext6Fq204 :=
  ⟨x, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩

def ext6Add (x y : Ext6Fq204) : Ext6Fq204 :=
  ⟨Fq204.add x.a0 y.a0, Fq204.add x.a1 y.a1, Fq204.add x.a2 y.a2,
   Fq204.add x.a3 y.a3, Fq204.add x.a4 y.a4, Fq204.add x.a5 y.a5⟩

def ext6Sub (x y : Ext6Fq204) : Ext6Fq204 :=
  ⟨Fq204.sub x.a0 y.a0, Fq204.sub x.a1 y.a1, Fq204.sub x.a2 y.a2,
   Fq204.sub x.a3 y.a3, Fq204.sub x.a4 y.a4, Fq204.sub x.a5 y.a5⟩

/-- Base-field scalar multiplication `k_scale(x, s)` in $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:336-338`). -/
def ext6Scale (x : Ext6Fq204) (s : Fq204) : Ext6Fq204 :=
  ⟨Fq204.mul x.a0 s, Fq204.mul x.a1 s, Fq204.mul x.a2 s,
   Fq204.mul x.a3 s, Fq204.mul x.a4 s, Fq204.mul x.a5 s⟩

/-- Multiplication in $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:53-56`, reducing $X^{6+k} \mapsto 7 X^k$). -/
def ext6Mul (x y : Ext6Fq204) : Ext6Fq204 :=
  let nr := ext6Nonresidue
  let m (a b : Fq204) := Fq204.mul a b
  let ad (a b : Fq204) := Fq204.add a b
  let hi0 := ad (m x.a1 y.a5) (ad (m x.a2 y.a4) (ad (m x.a3 y.a3) (ad (m x.a4 y.a2) (m x.a5 y.a1))))
  let hi1 := ad (m x.a2 y.a5) (ad (m x.a3 y.a4) (ad (m x.a4 y.a3) (m x.a5 y.a2)))
  let hi2 := ad (m x.a3 y.a5) (ad (m x.a4 y.a4) (m x.a5 y.a3))
  let hi3 := ad (m x.a4 y.a5) (m x.a5 y.a4)
  let hi4 := m x.a5 y.a5
  ⟨ad (m x.a0 y.a0) (m nr hi0),
   ad (ad (m x.a0 y.a1) (m x.a1 y.a0)) (m nr hi1),
   ad (ad (m x.a0 y.a2) (ad (m x.a1 y.a1) (m x.a2 y.a0))) (m nr hi2),
   ad (ad (m x.a0 y.a3) (ad (m x.a1 y.a2) (ad (m x.a2 y.a1) (m x.a3 y.a0)))) (m nr hi3),
   ad (ad (m x.a0 y.a4) (ad (m x.a1 y.a3) (ad (m x.a2 y.a2) (ad (m x.a3 y.a1) (m x.a4 y.a0))))) (m nr hi4),
   ad (m x.a0 y.a5) (ad (m x.a1 y.a4) (ad (m x.a2 y.a3) (ad (m x.a3 y.a2) (ad (m x.a4 y.a1) (m x.a5 y.a0)))))⟩

private theorem fq204_add_sub_cancel_left (r v : Fq204) : Fq204.sub (Fq204.add r v) r = v := by
  rw [← Fq204.ofInt_nat r, ← Fq204.ofInt_nat v, Fq204.ofInt_add, Fq204.ofInt_sub]
  congr 1; omega

private theorem fq204_sub_add_cancel_left (r y : Fq204) : Fq204.add r (Fq204.sub y r) = y := by
  rw [← Fq204.ofInt_nat r, ← Fq204.ofInt_nat y, Fq204.ofInt_sub, Fq204.ofInt_add]
  congr 1; omega

private theorem ext6Add_sub_cancel (rest v : Ext6Fq204) : ext6Sub (ext6Add rest v) rest = v := by
  rcases rest with ⟨r0, r1, r2, r3, r4, r5⟩
  rcases v with ⟨v0, v1, v2, v3, v4, v5⟩
  simp only [ext6Add, ext6Sub, fq204_add_sub_cancel_left]

private theorem ext6Sub_add_cancel (rest y : Ext6Fq204) : ext6Add rest (ext6Sub y rest) = y := by
  rcases rest with ⟨r0, r1, r2, r3, r4, r5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  simp only [ext6Add, ext6Sub, fq204_sub_add_cancel_left]

theorem ext6Scale_mul (x : Ext6Fq204) (a b : Fq204) :
    ext6Scale (ext6Scale x a) b = ext6Scale x (Fq204.mul a b) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, Fq204.mul_assoc]

theorem ext6Scale_one (x : Ext6Fq204) : ext6Scale x Fq204.one = x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, Fq204.mul_one]

/-- Constructive `Ext6Fq204` bijection `chi ↦ rest + k_scale(chi, delta)` for any nonzero gate error
    `delta ≠ 0` (`rss_mpc.rs:1066-1095`): proves that across all $q^6 = 8380417^6 > 2^{137}$ extension
    challenges `chi : Ext6Fq204`, **at most one** `chi` cancels `rest` to `ext6Zero`! -/
def ext6BatchChallengeEquiv (delta : Fq204) (hDelta : delta ≠ Fq204.zero) (rest : Ext6Fq204) :
    SimpleEquiv Ext6Fq204 Ext6Fq204 where
  toFun chi := ext6Add rest (ext6Scale chi delta)
  invFun out := ext6Scale (ext6Sub out rest) (Fq204.inv delta)
  left_inv chi := by
    rw [ext6Add_sub_cancel, ext6Scale_mul, Fq204.mul_inv_cancel hDelta, ext6Scale_one]
  right_inv out := by
    rw [ext6Scale_mul, Fq204.mul_comm (Fq204.inv delta) delta, Fq204.mul_inv_cancel hDelta,
        ext6Scale_one, ext6Sub_add_cancel]

private def fq204PowModAux (base : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, exp, acc =>
    if exp = 0 then acc
    else
      let acc' := if exp % 2 = 1 then (acc * base) % mldsaQ else acc
      fq204PowModAux ((base * base) % mldsaQ) fuel (exp / 2) acc'

def fq204PowModNat (base exp : Nat) : Nat :=
  fq204PowModAux (base % mldsaQ) 28 exp 1

private theorem nodup_map_on_list_fq {α β : Type} (f : α → β) :
    ∀ {xs : List α}, xs.Nodup → (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) → (xs.map f).Nodup
  | [], _, _ => .nil
  | x :: xs, .cons hNotMem hTail, hInj => by
    simp only [List.map_cons]
    refine .cons ?_ (nodup_map_on_list_fq f hTail (fun a ha b hb => hInj a (.tail _ ha) b (.tail _ hb)))
    intro y hy hEq
    rcases List.mem_map.mp hy with ⟨z, hzMem, rfl⟩
    have hxz := hInj x (.head _) z (.tail _ hzMem) hEq
    exact hNotMem z hzMem hxz

private theorem exists_mem_of_filter_length_lt_fq {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.filter p).length < xs.length → ∃ x ∈ xs, p x = false
  | [], h => by simp at h
  | x :: xs, h => by
    cases hpx : p x
    · exact ⟨x, .head _, hpx⟩
    · simp only [List.filter_cons_of_pos hpx, List.length_cons] at h
      obtain ⟨y, hyMem, hyFalse⟩ := exists_mem_of_filter_length_lt_fq p xs (by omega)
      exact ⟨y, .tail _ hyMem, hyFalse⟩

private theorem exists_eval_nonzero_fq204 :
    ∀ (cs : List Fq204), cs.length < mldsaQ →
      (∃ c ∈ cs, c ≠ Fq204.zero) →
      ∃ x : Fq204, RoundPoly.evalCoeffs cs x ≠ CommRingOps.zero
  | [], _, ⟨_, hMem, _⟩ => by cases hMem
  | c₀ :: tail, hLen, ⟨c, hMem, hcNe⟩ => by
    if hc0Ne : c₀ ≠ Fq204.zero then
      refine ⟨Fq204.zero, ?_⟩
      change Fq204.add c₀ (Fq204.mul Fq204.zero (RoundPoly.evalCoeffs tail Fq204.zero)) ≠ Fq204.zero
      rw [Fq204.zero_mul, Fq204.add_zero]
      exact hc0Ne
    else
      have hc0Eq : c₀ = Fq204.zero := by
        cases decEq c₀ Fq204.zero with
        | isTrue h => exact h
        | isFalse h => exact False.elim (hc0Ne h)
      subst hc0Eq
      have hTailEx : ∃ c' ∈ tail, c' ≠ Fq204.zero := by
        rcases List.mem_cons.mp hMem with rfl | hInTail
        · exact False.elim (hcNe rfl)
        · exact ⟨c, hInTail, hcNe⟩
      have hTailPos : 1 ≤ tail.length := by
        rcases hTailEx with ⟨_, hm, _⟩
        cases tail with
        | nil => cases hm
        | cons _ _ => simp only [List.length_cons]; omega
      simp only [List.length_cons] at hLen
      obtain ⟨x₁, hx₁⟩ := exists_eval_nonzero_fq204 tail (by omega) hTailEx
      let d := tail.length - 1
      let grid : List Fq204 := (List.range (d + 1)).map (fun i => Fq204.ofNat (i + 1))
      have hGridLen : grid.length = d + 1 := by simp [grid]
      have hGridNodup : grid.Nodup := by
        apply nodup_map_on_list_fq _ (Qsag.Constructive.nodup_range (d + 1))
        intro a ha b hb hEq
        have haLt : a + 1 < mldsaQ := by have := List.mem_range.mp ha; omega
        have hbLt : b + 1 < mldsaQ := by have := List.mem_range.mp hb; omega
        have hVal := congrArg Fq204.val hEq
        simp only [Fq204.ofNat_val, Nat.mod_eq_of_lt haLt, Nat.mod_eq_of_lt hbLt] at hVal
        omega
      have hRootsLe :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = CommRingOps.zero))).length ≤ d :=
        RoundPoly.roots_nodup_length_le d tail grid hGridNodup (by omega) ⟨x₁, hx₁⟩
      have hFiltLt :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = CommRingOps.zero))).length < grid.length := by
        rw [hGridLen]; omega
      obtain ⟨x₀, hx₀Mem, hx₀False⟩ := exists_mem_of_filter_length_lt_fq
        (fun r => decide (RoundPoly.evalCoeffs tail r = CommRingOps.zero)) grid hFiltLt
      have hx₀NeZero : x₀ ≠ Fq204.zero := by
        rcases List.mem_map.mp hx₀Mem with ⟨idx, hIdxRange, rfl⟩
        have hIdxLt : idx + 1 < mldsaQ := by have := List.mem_range.mp hIdxRange; omega
        intro hZero
        have hv := congrArg Fq204.val hZero
        simp only [Fq204.ofNat_val, Nat.mod_eq_of_lt hIdxLt, Fq204.zero_val] at hv
        omega
      have hEvalTailNe : RoundPoly.evalCoeffs tail x₀ ≠ CommRingOps.zero := by
        intro hZero
        rw [decide_eq_true hZero] at hx₀False
        cases hx₀False
      refine ⟨x₀, ?_⟩
      change Fq204.add Fq204.zero (Fq204.mul x₀ (RoundPoly.evalCoeffs tail x₀)) ≠ Fq204.zero
      rw [Fq204.zero_add]
      intro hProdZero
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hProdZero with h1 | h2
      · exact hx₀NeZero h1
      · exact hEvalTailNe h2

/-- **Numeric Modulus Certificate & Base-Scalar Batch Bound for $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:53-56, 1066-1206`)**:
    1. Serret–Kummer binomial irreducibility certificate for $X^6 - 7$ over $\mathbb{F}_{8380417}$:
       $6 \mid (q - 1)$, $7^{(q-1)/2} \equiv q - 1 \not\equiv 1 \pmod q$ ($7$ is a quadratic non-residue),
       $7^{(q-1)/3} \not\equiv 1 \pmod q$ ($7$ is a cubic non-residue), and $2^{137} < q^6$.
    2. Unique `Ext6Fq204` batch root: for any nonzero base-field gate error $\Delta \ne 0$ and arbitrary
       batch accumulator `rest`, `ext6Add rest (ext6Scale chi Δ) = ext6Zero` holds for **at most 1**
       challenge `chi : Ext6Fq204` (`(ext6BatchChallengeEquiv Δ hΔ rest).invFun ext6Zero`).
    3. Recursive polynomial folding bound (`rss_mpc.rs:1120-1171`, `FOLD = 8`): any degree-$\le D$
       ($D + 1 < q$) folding discrepancy polynomial with a nonzero coefficient has $\le D$ roots
       in any duplicate-free point set `S : List Fq204`. -/
theorem rss_ext6_modulus_certificate_and_batch_sacrifice_sound :
    ((mldsaQ - 1) % 6 = 0 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 2) = mldsaQ - 1 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 2) ≠ 1 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 3) ≠ 1 ∧
     2 ^ 137 < mldsaQ ^ 6) ∧
    (∀ (delta : Fq204) (_hDelta : delta ≠ Fq204.zero) (rest chi₁ chi₂ : Ext6Fq204),
      ext6Add rest (ext6Scale chi₁ delta) = ext6Zero →
      ext6Add rest (ext6Scale chi₂ delta) = ext6Zero →
      chi₁ = chi₂) ∧
    (∀ (D : Nat) (cs S : List Fq204),
      D + 1 < mldsaQ →
      cs.length ≤ D + 1 →
      S.Nodup →
      (∃ c ∈ cs, c ≠ Fq204.zero) →
      (S.filter (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero))).length ≤ D) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro delta hDelta rest chi₁ chi₂ h1 h2
    let eqv := ext6BatchChallengeEquiv delta hDelta rest
    have hEq : eqv.toFun chi₁ = eqv.toFun chi₂ := h1.trans h2.symm
    have hInv := congrArg eqv.invFun hEq
    rwa [eqv.left_inv, eqv.left_inv] at hInv
  · intro D cs S hDLt hLen hNodup hNz
    obtain ⟨x₀, hx₀⟩ := exists_eval_nonzero_fq204 cs (by omega) hNz
    exact RoundPoly.roots_nodup_length_le D cs S hNodup hLen ⟨x₀, hx₀⟩

/-- Domain tag `"QSAG.RSS.VIEW.DIGEST.V1"` (`rss_mpc.rs:1180`, 23 bytes). -/
def rssViewDigestTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x53, 0x53, 0x2E, 0x56, 0x49, 0x45,
   0x57, 0x2E, 0x44, 0x49, 0x47, 0x45, 0x53, 0x54, 0x2E, 0x56, 0x31]

def rssViewDigestPreimage (seedKey viewBytes : List UInt8) : List UInt8 :=
  cshake256FramedPreimage rssViewDigestTag [seedKey, viewBytes]

/-- Domain tag `"QSAG.TMLDSA.DKG.CONFIRM.V1"` (`threshold_mldsa.rs:582`, 26 bytes). -/
def dkgConfirmDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4D, 0x4C, 0x44, 0x53, 0x41, 0x2E, 0x44, 0x4B,
   0x47, 0x2E, 0x43, 0x4F, 0x4E, 0x46, 0x49, 0x52, 0x4D, 0x2E, 0x56, 0x31]

/-- Exact `cshake256_framed_32(b"QSAG.TMLDSA.DKG.CONFIRM.V1", &[session_id, &matrix_seed, &pk_bytes])`
    preimage (`threshold_mldsa.rs:581-585`). -/
def dkgConfirmPreimage (sessionId matrixSeed pkBytes : List UInt8) : List UInt8 :=
  cshake256FramedPreimage dkgConfirmDomainTag [sessionId, matrixSeed, pkBytes]

def dkgConfirmDigest (H : List UInt8 → List UInt8) (sessionId matrixSeed pkBytes : List UInt8) : List UInt8 :=
  H (dkgConfirmPreimage sessionId matrixSeed pkBytes)

def rssZeroVec4 : PolyVec4 := fun _ => PolyTree.zero 8

def rssSumVec4List : List PolyVec4 → PolyVec4
  | [] => rssZeroVec4
  | v :: vsl => addVec4 v (rssSumVec4List vsl)

private theorem matVecMul4_rssZeroVec4 (A : PolyMat4) :
    matVecMul4 A rssZeroVec4 = rssZeroVec4 := by
  funext i
  dsimp only [matVecMul4, rssZeroVec4]
  have hMul0 : ∀ p : Poly256, negacyclicMul p (PolyTree.zero 8) = PolyTree.zero 8 :=
    LawfulCommRing.mul_zero
  simp only [hMul0, polyTree_add_zero]

private theorem addVec4_assoc (a b c : PolyVec4) :
    addVec4 (addVec4 a b) c = addVec4 a (addVec4 b c) := by
  funext i; exact polyTree_add_assoc (a i) (b i) (c i)

private theorem addVec4_comm (a b : PolyVec4) :
    addVec4 a b = addVec4 b a := by
  funext i; exact polyTree_add_comm (a i) (b i)

private theorem addVec4_rssZero_right (a : PolyVec4) :
    addVec4 a rssZeroVec4 = a := by
  funext i; exact polyTree_add_zero (a i)

private theorem addVec4_left_neg (a : PolyVec4) :
    addVec4 (negVec4 a) a = rssZeroVec4 := by
  funext i; exact polyTree_add_left_neg (a i)

private theorem subVec4_eq_add_neg (a b : PolyVec4) :
    subVec4 a b = addVec4 a (negVec4 b) := by
  funext i; exact polyTree_sub_eq_add_neg (a i) (b i)

private theorem matVecMul4_rssSumVec4List (A : PolyMat4) :
    ∀ (vsl : List PolyVec4),
      matVecMul4 A (rssSumVec4List vsl) = rssSumVec4List (vsl.map (matVecMul4 A))
  | [] => matVecMul4_rssZeroVec4 A
  | v :: vsl => by
    simp only [rssSumVec4List, List.map_cons, matVecMul4_add, matVecMul4_rssSumVec4List A vsl]

private theorem rssSumVec4List_add_zip :
    ∀ (xs ys : List PolyVec4),
      xs.length = ys.length →
      rssSumVec4List (List.zipWith addVec4 xs ys) = addVec4 (rssSumVec4List xs) (rssSumVec4List ys)
  | [], [], _ => by
    simp only [List.zipWith, rssSumVec4List, addVec4_rssZero_right]
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | x :: xs, y :: ys, h => by
    simp only [List.length_cons] at h
    have ih := rssSumVec4List_add_zip xs ys (Nat.succ.inj h)
    simp only [List.zipWith, rssSumVec4List, ih]
    rw [addVec4_assoc x y (addVec4 (rssSumVec4List xs) (rssSumVec4List ys)),
        ← addVec4_assoc y (rssSumVec4List xs) (rssSumVec4List ys),
        addVec4_comm y (rssSumVec4List xs),
        addVec4_assoc (rssSumVec4List xs) y (rssSumVec4List ys),
        ← addVec4_assoc x (rssSumVec4List xs) (addVec4 y (rssSumVec4List ys))]

/-- **`#tooth` (`tooth_uncommitted_dkg_rogue_key_forgery`)**:
    Without pre-opening share commitments and `"QSAG.TMLDSA.DKG.CONFIRM.V1"` transcript confirmation,
    a rushing adversary observing honest public contribution `t₀ : PolyVec4` chooses `t_bad := subVec4 tStar t₀`
    so the aggregate public vector `addVec4 t₀ t_bad` equals ANY target `tStar` (e.g. a known-trapdoor key)! -/
theorem tooth_uncommitted_dkg_rogue_key_forgery (t₀ tStar : PolyVec4) :
    addVec4 t₀ (subVec4 tStar t₀) = tStar := by
  rw [subVec4_eq_add_neg, addVec4_comm tStar (negVec4 t₀),
      ← addVec4_assoc t₀ (negVec4 t₀) tStar,
      addVec4_comm t₀ (negVec4 t₀), addVec4_left_neg,
      addVec4_comm rssZeroVec4 tStar, addVec4_rssZero_right]

/-- **Flagship §2.3 Theorem — `(t, m)` RSS Subset-Key Consistency & `"QSAG.TMLDSA.DKG.CONFIRM.V1"`
    Transcript Binding (`dkg_confirm_transcript_binding_and_rss_consistency`, `threshold_mldsa.rs:503-620`)**:
    1. **Honest-Holder Coverage & RSS Public-Key Homomorphism**: Whenever $1 \le t$ and $2t - 1 \le m$,
       every $(m - t + 1)$-subset $T$ has $\ge 1$ honest custodian outside any $(t - 1)$-corrupt coalition
       (`subset_honest_holder_exists`), AND summing subset public shares $t_T = A \cdot s_{1,T} + s_{2,T}$
       reconstructs the exact ML-DSA-44 key relation $t = A \cdot (\sum_T s_{1,T}) + (\sum_T s_{2,T})$.
    2. **`"QSAG.TMLDSA.DKG.CONFIRM.V1"` Equivocation / Mismatch Detection**: If all honest custodians check
       pairwise equality of `dkgConfirmDigest H sessionId matrixSeed pkBytes` (`threshold_mldsa.rs:581-600`),
       any disagreement on `(sessionId, matrixSeed, pkBytes)` (`< 256^8` bytes) either causes immediate DKG
       rejection or exhibits an explicit length-framed `cshake256_framed_32` collision under `H`! -/
theorem dkg_confirm_transcript_binding_and_rss_consistency
    (H : List UInt8 → List UInt8) :
    (∀ (t m : Nat) (subset corrupt : List Nat),
      1 ≤ t → 2 * t - 1 ≤ m →
      corrupt.length ≤ t - 1 →
      subset.Nodup → subset.length = m - t + 1 →
      ∃ h ∈ subset, h ∉ corrupt) ∧
    (∀ (A : PolyMat4) (s1Subs s2Subs : List PolyVec4),
      s1Subs.length = s2Subs.length →
      rssSumVec4List (List.zipWith (fun s1 s2 => addVec4 (matVecMul4 A s1) s2) s1Subs s2Subs) =
        addVec4 (matVecMul4 A (rssSumVec4List s1Subs)) (rssSumVec4List s2Subs)) ∧
    (∀ (sid₁ sid₂ mSeed₁ mSeed₂ pk₁ pk₂ : List UInt8),
      sid₁.length < 256 ^ 8 → sid₂.length < 256 ^ 8 →
      mSeed₁.length < 256 ^ 8 → mSeed₂.length < 256 ^ 8 →
      pk₁.length < 256 ^ 8 → pk₂.length < 256 ^ 8 →
      (sid₂, mSeed₂, pk₂) ≠ (sid₁, mSeed₁, pk₁) →
      dkgConfirmDigest H sid₁ mSeed₁ pk₁ ≠ dkgConfirmDigest H sid₂ mSeed₂ pk₂ ∨
        (dkgConfirmPreimage sid₁ mSeed₁ pk₁ ≠ dkgConfirmPreimage sid₂ mSeed₂ pk₂ ∧
         H (dkgConfirmPreimage sid₁ mSeed₁ pk₁) = H (dkgConfirmPreimage sid₂ mSeed₂ pk₂))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t m subset corrupt ht hm hCLen hSNd hSLen
    obtain ⟨h, _, hIn, hNotIn⟩ :=
      (subset_honest_holder_exists ht hm hCLen hSNd hSLen idMat4 0
        ⟨rssZeroVec4, rssZeroVec4, rssZeroVec4⟩).1
    exact ⟨h, hIn, hNotIn⟩
  · intro A s1Subs s2Subs hLen
    have hZipEq :
        List.zipWith (fun s1 s2 => addVec4 (matVecMul4 A s1) s2) s1Subs s2Subs =
          List.zipWith addVec4 (s1Subs.map (matVecMul4 A)) s2Subs := by
      induction s1Subs generalizing s2Subs with
      | nil => cases s2Subs <;> rfl
      | cons x xs ih =>
        cases s2Subs with
        | nil => cases hLen
        | cons y ys =>
          simp only [List.length_cons] at hLen
          simp only [List.zipWith, List.map_cons, ih ys (Nat.succ.inj hLen)]
    rw [hZipEq, rssSumVec4List_add_zip _ _ (by rw [List.length_map, hLen]), ← matVecMul4_rssSumVec4List]
  · intro sid₁ sid₂ mSeed₁ mSeed₂ pk₁ pk₂ hs1 hs2 hm1 hm2 hp1 hp2 hNe
    if hDigEq : dkgConfirmDigest H sid₁ mSeed₁ pk₁ = dkgConfirmDigest H sid₂ mSeed₂ pk₂ then
      right
      refine ⟨?_, hDigEq⟩
      intro hPreEq
      unfold dkgConfirmPreimage at hPreEq
      have hAll1 : ∀ f ∈ [sid₁, mSeed₁, pk₁], f.length < 256 ^ 8 := by
        intro f hf
        rcases List.mem_cons.mp hf with rfl | h1
        · exact hs1
        · rcases List.mem_cons.mp h1 with rfl | h2
          · exact hm1
          · rcases List.mem_cons.mp h2 with rfl | h3
            · exact hp1
            · cases h3
      have hAll2 : ∀ g ∈ [sid₂, mSeed₂, pk₂], g.length < 256 ^ 8 := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | h1
        · exact hs2
        · rcases List.mem_cons.mp h1 with rfl | h2
          · exact hm2
          · rcases List.mem_cons.mp h2 with rfl | h3
            · exact hp2
            · cases h3
      have hFrEq := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hPreEq
      injection hFrEq with eSid t1
      injection t1 with eSeed t2
      injection t2 with ePk _
      exact hNe (by rw [eSid, eSeed, ePk])
    else
      exact Or.inl hDigEq

/-! ### §2.4 Aggregate Rejection-Barrier Zero-Leakage, `u_com` Binding & Standalone FIPS 204 `mldsaVerify` (`P0-06`) -/

/-- **`#tooth` (`premature_z_release_leaks_s2_boundary`)**:
    If `z = y + c * s1` is prematurely released on an aborted signing attempt where
    `mldsa44Gamma2 - mldsa44Beta ≤ lowBitsNormVec4 (w - c * s2)`, ANY observer holding only public
    `(A, t = A*s1 + s2, c, z)` computes `A * z - c * t = w - c * s2` identically and directly observes
    the secret-dependent `s2` boundary alignment `γ₂ - β ≤ ‖LowBits(w - c * s2)‖_∞`! -/
theorem premature_z_release_leaks_s2_boundary
    (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256)
    (hBoundaryAbort :
      mldsa44Gamma2 - mldsa44Beta ≤ lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2))) :
    let t := addVec4 (matVecMul4 A s1) s2
    let w := matVecMul4 A y
    let z := addVec4 y (mulPolyVec4 c s1)
    let publicRecovered := subVec4 (matVecMul4 A z) (mulPolyVec4 c t)
    publicRecovered = subVec4 w (mulPolyVec4 c s2) ∧
    mldsa44Gamma2 - mldsa44Beta ≤ lowBitsNormVec4 publicRecovered := by
  intro t w z publicRecovered
  have hRecover : publicRecovered = subVec4 w (mulPolyVec4 c s2) := by
    dsimp only [publicRecovered, z, w, t]
    rw [matVecMul4_add, matVecMul4_mulPoly]
    funext i
    dsimp only [addVec4, subVec4, mulPolyVec4]
    rw [negacyclicMul_left_distrib]
    let wy := matVecMul4 A y i
    let u1 := negacyclicMul c (matVecMul4 A s1 i)
    let u2 := negacyclicMul c (s2 i)
    change PolyTree.sub (PolyTree.add wy u1) (PolyTree.add u1 u2) = PolyTree.sub wy u2
    apply poly256_add_left_cancel (a := PolyTree.add u1 u2)
    have hL :
        PolyTree.add (PolyTree.add u1 u2) (PolyTree.sub (PolyTree.add wy u1) (PolyTree.add u1 u2)) =
          PolyTree.add wy u1 := by
      rw [polyTree_sub_eq_add_neg,
          polyTree_add_comm (PolyTree.add wy u1) (PolyTree.neg (PolyTree.add u1 u2)),
          ← polyTree_add_assoc (PolyTree.add u1 u2) (PolyTree.neg (PolyTree.add u1 u2)) (PolyTree.add wy u1),
          polyTree_add_comm (PolyTree.add u1 u2) (PolyTree.neg (PolyTree.add u1 u2)),
          polyTree_add_left_neg, polyTree_add_comm (PolyTree.zero 8), polyTree_add_zero]
    have hR :
        PolyTree.add (PolyTree.add u1 u2) (PolyTree.sub wy u2) = PolyTree.add wy u1 := by
      rw [polyTree_sub_eq_add_neg, polyTree_add_comm wy (PolyTree.neg u2),
          polyTree_add_assoc u1 u2 (PolyTree.add (PolyTree.neg u2) wy),
          ← polyTree_add_assoc u2 (PolyTree.neg u2) wy,
          polyTree_add_comm u2 (PolyTree.neg u2), polyTree_add_left_neg,
          polyTree_add_comm (PolyTree.zero 8) wy, polyTree_add_zero,
          polyTree_add_comm u1 wy]
    exact hL.trans hR.symm
  exact ⟨hRecover, hRecover.symm ▸ hBoundaryAbort⟩

/-- A boundary abort with genuinely nonzero secret vectors, tied to the leakage experiment. -/
theorem premature_z_release_leaks_s2_boundary_inhabited :
    ∃ (A : PolyMat4) (s1 s2 y : PolyVec4) (c : Poly256),
      s1 ≠ (fun _ => PolyTree.zero 8) ∧
      s2 ≠ (fun _ => PolyTree.zero 8) ∧
      c ≠ PolyTree.zero 8 ∧
      mldsa44Gamma2 - mldsa44Beta ≤ lowBitsNormVec4 (subVec4 (matVecMul4 A y) (mulPolyVec4 c s2)) ∧
      subVec4 (matVecMul4 A (addVec4 y (mulPolyVec4 c s1)))
        (mulPolyVec4 c (addVec4 (matVecMul4 A s1) s2)) =
        subVec4 (matVecMul4 A y) (mulPolyVec4 c s2) := by
  let v1 : PolyVec4 := fun _ => polyTreeConstLeaf 8 Fq204.one
  let yHi : PolyVec4 := fun _ => polyTreeConstLeaf 8 ⟨95201, by decide⟩
  have hn : v1 ≠ (fun _ => PolyTree.zero 8) := by
    intro h
    have he := congrFun h (0 : Fin 4)
    have hv := congrArg PolyTree.infNorm he
    simp only [v1, polyTreeConstLeaf_infNorm] at hv
    change 1 = 0 at hv
    omega
  have hb : mldsa44Gamma2 - mldsa44Beta ≤
      lowBitsNormVec4 (subVec4 (matVecMul4 idMat4 yHi)
        (mulPolyVec4 (PolyTree.constUnit 8) v1)) := by
    rw [matVecMul4_idMat4]
    have hm : mulPolyVec4 (PolyTree.constUnit 8) v1 = v1 := by
      funext i; exact negacyclicMul_one_left (v1 i)
    rw [hm]
    unfold lowBitsNormVec4 subVec4
    dsimp only [yHi, v1]
    simp only [polyTree_sub_eq_add_neg, polyTreeConstLeaf_neg,
      polyTreeConstLeaf_add, polyTreeConstLeaf_lowBitsNorm, Nat.max_self]
    decide
  exact ⟨idMat4, v1, v1, yHi, PolyTree.constUnit 8, hn, hn, by decide, hb,
    (premature_z_release_leaks_s2_boundary idMat4 v1 v1 yHi (PolyTree.constUnit 8) hb).1⟩

/-- Tree-lifted centered residual norm `‖(r - w1 * 2γ₂) mod± q‖_∞` (`threshold_mldsa.rs:789-799`). -/
def centeredDiffNormTree : {d : Nat} → PolyTree d → NatTree d → Nat
  | 0, .leaf r, .leaf w1 => Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat (w1 * 190464)))
  | _ + 1, .branch r0 r1, .branch w0 w1 =>
    max (centeredDiffNormTree r0 w0) (centeredDiffNormTree r1 w1)

private theorem polyTreeConstLeaf_centeredDiffNorm (r w : Fq204) : ∀ (d : Nat),
    centeredDiffNormTree (polyTreeConstLeaf d r) (highBitsTree (polyTreeConstLeaf d w)) =
      Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat ((mldsaHighBits w) * 190464)))
  | 0 => rfl
  | d + 1 => by
    simp only [polyTreeConstLeaf, highBitsTree, centeredDiffNormTree,
      polyTreeConstLeaf_centeredDiffNorm r w d, Nat.max_self]

def natTreeAllLt44 : {d : Nat} → NatTree d → Prop
  | 0, .leaf w1 => w1 < 44
  | _ + 1, .branch w0 w1 => natTreeAllLt44 w0 ∧ natTreeAllLt44 w1

theorem highBitsTree_allLt44 : ∀ {d : Nat} (p : PolyTree d), natTreeAllLt44 (highBitsTree p)
  | 0, .leaf r => (decompose_reconstruct r).1
  | _ + 1, .branch p0 p1 => And.intro (highBitsTree_allLt44 p0) (highBitsTree_allLt44 p1)

theorem centeredDiffNormTree_lt_iff : ∀ {d : Nat} (r : PolyTree d) (w1 : NatTree d) {B : Nat},
    natTreeAllLt44 w1 → B ≤ 95232 →
    (centeredDiffNormTree r w1 < B ↔ lowBitsNormTree r < B ∧ highBitsTree r = w1)
  | 0, .leaf r, .leaf w1, B, hw1, hB => by
    simp only [centeredDiffNormTree, lowBitsNormTree, highBitsTree, NatTree.leaf.injEq]
    exact centered_diff_lt_iff_lowBits_and_highBits r hw1 hB
  | _ + 1, .branch r0 r1, .branch w0 w1, B, hw, hB => by
    rcases hw with ⟨hw0, hw1⟩
    simp only [centeredDiffNormTree, lowBitsNormTree, highBitsTree, NatTree.branch.injEq]
    have ih0 := centeredDiffNormTree_lt_iff r0 w0 hw0 hB
    have ih1 := centeredDiffNormTree_lt_iff r1 w1 hw1 hB
    constructor
    · intro hLt
      have h0 : centeredDiffNormTree r0 w0 < B := by omega
      have h1 : centeredDiffNormTree r1 w1 < B := by omega
      obtain ⟨l0, e0⟩ := ih0.mp h0
      obtain ⟨l1, e1⟩ := ih1.mp h1
      exact ⟨by omega, e0, e1⟩
    · rintro ⟨hLow, e0, e1⟩
      have h0 : centeredDiffNormTree r0 w0 < B := ih0.mpr ⟨by omega, e0⟩
      have h1 : centeredDiffNormTree r1 w1 < B := ih1.mpr ⟨by omega, e1⟩
      omega

def centeredDiffNormVec4 (r : PolyVec4) (w1 : Fin 4 → NatTree 8) : Nat :=
  max (max (centeredDiffNormTree (r ⟨0, by decide⟩) (w1 ⟨0, by decide⟩))
           (centeredDiffNormTree (r ⟨1, by decide⟩) (w1 ⟨1, by decide⟩)))
      (max (centeredDiffNormTree (r ⟨2, by decide⟩) (w1 ⟨2, by decide⟩))
           (centeredDiffNormTree (r ⟨3, by decide⟩) (w1 ⟨3, by decide⟩)))

theorem centeredDiffNormVec4_lt_iff (r w : PolyVec4) {B : Nat} (hB : B ≤ 95232) :
    centeredDiffNormVec4 r (highBitsVec4 w) < B ↔
      lowBitsNormVec4 r < B ∧ highBitsVec4 r = highBitsVec4 w := by
  unfold centeredDiffNormVec4 lowBitsNormVec4
  have ih0 := centeredDiffNormTree_lt_iff (r ⟨0, by decide⟩) (highBitsTree (w ⟨0, by decide⟩))
    (highBitsTree_allLt44 _) hB
  have ih1 := centeredDiffNormTree_lt_iff (r ⟨1, by decide⟩) (highBitsTree (w ⟨1, by decide⟩))
    (highBitsTree_allLt44 _) hB
  have ih2 := centeredDiffNormTree_lt_iff (r ⟨2, by decide⟩) (highBitsTree (w ⟨2, by decide⟩))
    (highBitsTree_allLt44 _) hB
  have ih3 := centeredDiffNormTree_lt_iff (r ⟨3, by decide⟩) (highBitsTree (w ⟨3, by decide⟩))
    (highBitsTree_allLt44 _) hB
  dsimp only [highBitsVec4]
  constructor
  · intro hLt
    obtain ⟨l0, e0⟩ := ih0.mp (by omega)
    obtain ⟨l1, e1⟩ := ih1.mp (by omega)
    obtain ⟨l2, e2⟩ := ih2.mp (by omega)
    obtain ⟨l3, e3⟩ := ih3.mp (by omega)
    refine ⟨by omega, ?_⟩
    funext i
    rcases i with ⟨idx, hidx⟩
    have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
    rcases hCases with rfl | rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  · rintro ⟨hLow, hEq⟩
    have e0 := congrFun hEq ⟨0, by decide⟩
    have e1 := congrFun hEq ⟨1, by decide⟩
    have e2 := congrFun hEq ⟨2, by decide⟩
    have e3 := congrFun hEq ⟨3, by decide⟩
    have c0 := ih0.mpr ⟨by omega, e0⟩
    have c1 := ih1.mpr ⟨by omega, e1⟩
    have c2 := ih2.mpr ⟨by omega, e2⟩
    have c3 := ih3.mpr ⟨by omega, e3⟩
    omega

/-- Parameterized ML-DSA-44 algebraic verification core (legacy MIR bridge API):
    Checks `‖z‖_∞ < γ₁ - β`, `weight(h) ≤ ω`, and `c_tilde = H(μ, UseHint(h, A*z - c*t1*2^d))`. -/
@[expose] def mldsaVerify
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (A : PolyMat4) (t1Scaled : PolyVec4) (mu : List UInt8)
    (cTilde : List UInt8) (z : PolyVec4) (h : Fin 4 → HintTree 8) : Bool :=
  let c := sampleInBall cTilde
  let w1Prime := useHintVec4 h (subVec4 (matVecMul4 A z) (mulPolyVec4 c t1Scaled))
  decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
  decide (hintWeightVec4 h ≤ mldsa44Omega) &&
  decide (cTilde = chalHash mu w1Prime)

/-- Persistent custodian state for `(t, m)` RSS `threshold_sign_mldsa_party` (`threshold_mldsa.rs:772-1055`):
    holds current signing `epoch`, monotonic `nextAttempt` burn counter, matrix `A`, and RSS subset
    key vectors `(s1Subsets, s2Subsets)` for the aggregate reference computation. -/
structure RssMlDsaSignerState where
  epoch : Nat
  nextAttempt : Nat
  A : PolyMat4
  s1Subsets : List PolyVec4
  s2Subsets : List PolyVec4

/-- Supplied multiplication outputs consumed by the signing transition. These are checked
    against the operands, rather than accepting a caller's success flag. This is an exact
    aggregate checker; a private distributed sacrifice implementation needs a separate refinement. -/
structure RssSignProducts where
  w : PolyVec4
  cs1 : PolyVec4
  cs2 : PolyVec4
  ct0 : PolyVec4

def rssComputeProducts
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (mu : List UInt8) (ySubsets : List PolyVec4) : RssSignProducts :=
  let s1 := rssSumVec4List st.s1Subsets
  let s2 := rssSumVec4List st.s2Subsets
  let w := matVecMul4 st.A (rssSumVec4List ySubsets)
  let c := sampleInBall (chalHash mu (highBitsVec4 w))
  { w := w, cs1 := mulPolyVec4 c s1, cs2 := mulPolyVec4 c s2,
    ct0 := mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2)) }

/-- Single RSS signing-attempt input (`threshold_mldsa.rs:795-975`):
    binds `(epoch, sessionId, attempt)`, message representative `mu`, RSS nonce shares `ySubsets`,
    caller-provided masks `(maskW, maskZ, maskLow)`, and raw multiplication outputs. -/
structure RssMlDsaAttemptInput where
  epoch : Nat
  sessionId : List UInt8
  attempt : Nat
  mu : List UInt8
  ySubsets : List PolyVec4
  maskW : PolyVec4
  maskZ : PolyVec4
  maskLow : PolyVec4
  products : RssSignProducts

def rssProductsValid
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) : Bool :=
  let expected := rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets
  polyVec4EqBool inp.products.w expected.w &&
  polyVec4EqBool inp.products.cs1 expected.cs1 &&
  polyVec4EqBool inp.products.cs2 expected.cs2 &&
  polyVec4EqBool inp.products.ct0 expected.ct0

theorem rssProductsValid_eq_true_iff
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    rssProductsValid chalHash sampleInBall st inp = true ↔
      inp.products = rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets := by
  simp only [rssProductsValid, Bool.and_eq_true, polyVec4EqBool_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨hw, hs1⟩, hs2⟩, ht⟩
    revert hw hs1 hs2 ht
    generalize rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets = expected
    generalize inp.products = supplied
    cases supplied
    cases expected
    intro hw hs1 hs2 ht
    simp_all
  · intro h
    rw [h]
    exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- Emitted standalone FIPS 204 signature + burned attempt counter. -/
structure ThresholdSignSig where
  cTilde : List UInt8
  z : PolyVec4
  h : Fin 4 → HintTree 8
  usedAttempt : Nat

/-- Exact public transcript opened during a `threshold_sign_mldsa_party` attempt (`threshold_mldsa.rs:940-1015`):
    even when `rejectBit = true` (unmasked `(z, h)` suppressed!), the protocol publicly opens the `< q`-masked
    vectors `(openedMaskedW, openedMaskedZ, openedMaskedLow)`, rounded `openedW1 = HighBits(w)`, and `rejectBit`. -/
structure RssSignPublicAbortView where
  openedMaskedW : PolyVec4
  openedW1 : Fin 4 → NatTree 8
  openedMaskedZ : PolyVec4
  openedMaskedLow : PolyVec4
  rejectBit : Bool
  usedAttempt : Nat

/-- Pre-open gate abort reasons (prior to opening `RssSignPublicAbortView`). -/
inductive RssPreOpenAbortReason where
  | attemptReplay
  | mpcSacrificeFailed
  deriving DecidableEq, Repr

/-- Constructive `< q` additive mask bijection `m ↦ addVec4 target m` on `PolyVec4` (`rss_mpc.rs`). -/
def rssMaskAddEquiv (target : PolyVec4) : SimpleEquiv PolyVec4 PolyVec4 where
  toFun m := addVec4 target m
  invFun v := subVec4 v target
  left_inv m := by
    rw [subVec4_eq_add_neg, addVec4_comm target m,
        addVec4_assoc m target (negVec4 target),
        addVec4_comm target (negVec4 target), addVec4_left_neg, addVec4_rssZero_right]
  right_inv v := by
    rw [subVec4_eq_add_neg, addVec4_comm v (negVec4 target),
        ← addVec4_assoc target (negVec4 target) v,
        addVec4_comm target (negVec4 target), addVec4_left_neg,
        addVec4_comm rssZeroVec4 v, addVec4_rssZero_right]

private def seRefl (α : Type) : SimpleEquiv α α where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

private def seSymm {α β : Type} (e : SimpleEquiv α β) : SimpleEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

private def seTrans {α β γ : Type} (e₁ : SimpleEquiv α β) (e₂ : SimpleEquiv β γ) : SimpleEquiv α γ where
  toFun x := e₂.toFun (e₁.toFun x)
  invFun z := e₁.invFun (e₂.invFun z)
  left_inv x := by rw [e₂.left_inv, e₁.left_inv]
  right_inv z := by rw [e₁.right_inv, e₂.right_inv]

private def seProdCongr {α₁ α₂ β₁ β₂ : Type}
    (eA : SimpleEquiv α₁ α₂) (eB : SimpleEquiv β₁ β₂) :
    SimpleEquiv (α₁ × β₁) (α₂ × β₂) where
  toFun p := (eA.toFun p.1, eB.toFun p.2)
  invFun q := (eA.invFun q.1, eB.invFun q.2)
  left_inv := fun ⟨a, b⟩ => by dsimp only; rw [eA.left_inv a, eB.left_inv b]
  right_inv := fun ⟨c, d⟩ => by dsimp only; rw [eA.right_inv c, eB.right_inv d]

private def sePiCongrRight {ι : Type} {α β : ι → Type}
    (es : ∀ i, SimpleEquiv (α i) (β i)) :
    SimpleEquiv (∀ i, α i) (∀ i, β i) where
  toFun f i := (es i).toFun (f i)
  invFun g i := (es i).invFun (g i)
  left_inv f := funext fun i => (es i).left_inv (f i)
  right_inv g := funext fun i => (es i).right_inv (g i)

private def seDepProd {α₁ α₂ β₁ β₂ : Type}
    (eqA : SimpleEquiv α₁ α₂)
    (eqB : α₁ → SimpleEquiv β₁ β₂) :
    SimpleEquiv (α₁ × β₁) (α₂ × β₂) where
  toFun p := (eqA.toFun p.1, (eqB p.1).toFun p.2)
  invFun q :=
    let a := eqA.invFun q.1
    (a, (eqB a).invFun q.2)
  left_inv := fun ⟨a, b⟩ => by
    dsimp only
    rw [eqA.left_inv a, (eqB a).left_inv b]
  right_inv := fun ⟨c, d⟩ => by
    dsimp only
    rw [eqA.right_inv c, (eqB (eqA.invFun c)).right_inv d]

/-- Triple `< q` RSS mask bijection over `(maskW, maskZ, maskLow)`. -/
def rssMaskTripleEquiv (w z u : PolyVec4) :
    SimpleEquiv (PolyVec4 × PolyVec4 × PolyVec4) (PolyVec4 × PolyVec4 × PolyVec4) :=
  seProdCongr (rssMaskAddEquiv w)
    (seProdCongr (rssMaskAddEquiv z) (rssMaskAddEquiv u))

/-- Explicit leakage-parameterized abort simulator (`threshold_mldsa.rs:940-1015`):
    given **only** the public ideal abort leakage `(leakedW1, rejectBit := true, usedAttempt)` and uniform
    simulator masks `simMasks` (zero secret shares `s1Subsets, s2Subsets, ySubsets`!), constructs the corresponding
    `RssSignPublicAbortView`. Equality of distributions additionally requires independent uniform masks. -/
def rssAbortSimulator
    (leakedW1 : Fin 4 → NatTree 8) (usedAttempt : Nat)
    (simMasks : PolyVec4 × PolyVec4 × PolyVec4) : RssSignPublicAbortView :=
  { openedMaskedW := simMasks.1
    openedW1 := leakedW1
    openedMaskedZ := simMasks.2.1
    openedMaskedLow := simMasks.2.2
    rejectBit := true
    usedAttempt := usedAttempt }

private def mkRssSignAttemptOutcome
    (stBurned : RssMlDsaSignerState) (usedAttempt : Nat)
    (cTilde : List UInt8) (w z u maskW maskZ maskLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8) (h : Fin 4 → HintTree 8) (accept : Bool) :
    StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason :=
  let publicView : RssSignPublicAbortView :=
    { openedMaskedW := addVec4 w maskW
      openedW1 := w1
      openedMaskedZ := addVec4 z maskZ
      openedMaskedLow := addVec4 u maskLow
      rejectBit := !accept
      usedAttempt := usedAttempt }
  match accept with
  | true =>
    .ok stBurned (publicView, some { cTilde := cTilde, z := z, h := h, usedAttempt := usedAttempt })
  | false =>
    .ok stBurned (publicView, none)

private theorem mkRssSignAttemptOutcome_ne_err
    {stBurned st' : RssMlDsaSignerState} {usedAttempt : Nat}
    {cTilde : List UInt8} {w z u maskW maskZ maskLow : PolyVec4}
    {w1 : Fin 4 → NatTree 8} {h : Fin 4 → HintTree 8} {accept : Bool}
    {err : RssPreOpenAbortReason} :
    mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept ≠
      .err st' err := by
  unfold mkRssSignAttemptOutcome
  cases accept <;> intro hc <;> cases hc

private theorem mkRssSignAttemptOutcome_eq_ok
    {stBurned st' : RssMlDsaSignerState} {usedAttempt : Nat}
    {cTilde : List UInt8} {w z u maskW maskZ maskLow : PolyVec4}
    {w1 : Fin 4 → NatTree 8} {h : Fin 4 → HintTree 8} {accept : Bool}
    {pubView : RssSignPublicAbortView} {mSig : Option ThresholdSignSig}
    (hOk : mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept =
           .ok st' (pubView, mSig)) :
    st' = stBurned ∧
    pubView = { openedMaskedW := addVec4 w maskW, openedW1 := w1,
                openedMaskedZ := addVec4 z maskZ, openedMaskedLow := addVec4 u maskLow,
                rejectBit := !accept, usedAttempt := usedAttempt } ∧
    ((accept = true ∧ mSig = some { cTilde := cTilde, z := z, h := h, usedAttempt := usedAttempt }) ∨
     (accept = false ∧ mSig = none)) := by
  unfold mkRssSignAttemptOutcome at hOk
  cases accept with
  | true =>
    injection hOk with hSt hPair
    injection hPair with hPub hSig
    exact ⟨hSt.symm, hPub.symm, Or.inl ⟨rfl, hSig.symm⟩⟩
  | false =>
    injection hOk with hSt hPair
    injection hPair with hPub hSig
    exact ⟨hSt.symm, hPub.symm, Or.inr ⟨rfl, hSig.symm⟩⟩

private theorem mkRssSignAttemptOutcome_true
    (stBurned : RssMlDsaSignerState) (usedAttempt : Nat)
    (cTilde : List UInt8) (w z u maskW maskZ maskLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8) (h : Fin 4 → HintTree 8) {accept : Bool}
    (hAcc : accept = true) :
    mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept =
      .ok stBurned
        ({ openedMaskedW := addVec4 w maskW, openedW1 := w1,
           openedMaskedZ := addVec4 z maskZ, openedMaskedLow := addVec4 u maskLow,
           rejectBit := false, usedAttempt := usedAttempt },
         some { cTilde := cTilde, z := z, h := h, usedAttempt := usedAttempt }) := by
  subst hAcc
  rfl

private theorem mkRssSignAttemptOutcome_false
    (stBurned : RssMlDsaSignerState) (usedAttempt : Nat)
    (cTilde : List UInt8) (w z u maskW maskZ maskLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8) (h : Fin 4 → HintTree 8) {accept : Bool}
    (hAcc : accept = false) :
    mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept =
      .ok stBurned
        ({ openedMaskedW := addVec4 w maskW, openedW1 := w1,
           openedMaskedZ := addVec4 z maskZ, openedMaskedLow := addVec4 u maskLow,
           rejectBit := true, usedAttempt := usedAttempt },
         none) := by
  subst hAcc
  rfl

/-- Signing computation on products that have already been checked: response, hint and the
    rejection predicate. Shared by the exact-product reference transition and by the
    sacrifice-gated transition. -/
def rssSignCore
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (stBurned : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason :=
  let y := rssSumVec4List inp.ySubsets
  let w := inp.products.w
  let w1 := highBitsVec4 w
  let cTilde := chalHash inp.mu w1
  let ct0 := inp.products.ct0
  let z := addVec4 y inp.products.cs1
  let u := subVec4 w inp.products.cs2
  let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
  let accept : Bool :=
    decide (infNormVec4 ct0 < mldsa44Gamma2) &&
    decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
    decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
    decide (hintWeightVec4 h ≤ mldsa44Omega)
  mkRssSignAttemptOutcome stBurned inp.attempt cTilde w z u
    inp.maskW inp.maskZ inp.maskLow w1 h accept

/-- Per-attempt RSS transition of `threshold_sign_mldsa_party` (`threshold_mldsa.rs:795-1055`):
    - Enforces `(inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt)` and immediately burns
      `nextAttempt := st.nextAttempt + 1` BEFORE Phase 1;
    - Requires `rssProductsValid chalHash sampleInBall st inp = true` (exact aggregate product validation);
    - Evaluates `w1 = HighBits(w)`, `c = SampleInBall(H(μ, w1))`, and the RSS rejection predicate
      `accept`;
    - On rejection (`accept = false`), emits `(publicView, none)` (`rejectBit = true`, no separate unmasked `z` field);
    - On acceptance (`accept = true`), emits `(publicView, some sig)` (`rejectBit = false`). -/
@[expose] def rssThresholdSignStep
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason :=
  match decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
  | false => .err st .attemptReplay
  | true =>
    let stBurned : RssMlDsaSignerState := { st with nextAttempt := st.nextAttempt + 1 }
    match rssProductsValid chalHash sampleInBall st inp with
    | false => .err stBurned .mpcSacrificeFailed
    | true => rssSignCore chalHash stBurned inp

/-- Canonical `PartyMachine` instantiation of `rssThresholdSignStep`. -/
def rssThresholdSignMachine
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    PartyMachine RssMlDsaSignerState RssMlDsaAttemptInput
      (RssSignPublicAbortView × Option ThresholdSignSig) :=
  PartyMachine.ofOutcome (rssThresholdSignStep chalHash sampleInBall)

/-- An attempt that passes the replay check, carries the exact products and satisfies the
    rejection predicate is accepted: the machine burns the attempt and releases the signature.
    Stated over arbitrary `st` and `inp`, so a concrete witness applies it instead of unfolding
    the transition on concrete polynomials. -/
theorem rssThresholdSignMachine_step_accept
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (hEpoch : inp.epoch = st.epoch) (hAttempt : inp.attempt = st.nextAttempt)
    (hProducts : inp.products = rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets) :
    let s1 := rssSumVec4List st.s1Subsets
    let s2 := rssSumVec4List st.s2Subsets
    let y := rssSumVec4List inp.ySubsets
    let t0 := power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2)
    let w := matVecMul4 st.A y
    let w1 := highBitsVec4 w
    let cTilde := chalHash inp.mu w1
    let c := sampleInBall cTilde
    let ct0 := mulPolyVec4 c t0
    let z := addVec4 y (mulPolyVec4 c s1)
    let u := subVec4 w (mulPolyVec4 c s2)
    let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
    (decide (infNormVec4 ct0 < mldsa44Gamma2) &&
     decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
     decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
     decide (hintWeightVec4 h ≤ mldsa44Omega)) = true →
    (rssThresholdSignMachine chalHash sampleInBall).step st inp =
      some ({ st with nextAttempt := st.nextAttempt + 1 },
        ({ openedMaskedW := addVec4 w inp.maskW,
           openedW1 := w1,
           openedMaskedZ := addVec4 z inp.maskZ,
           openedMaskedLow := addVec4 u inp.maskLow,
           rejectBit := false,
           usedAttempt := inp.attempt },
         some { cTilde := cTilde, z := z, h := h, usedAttempt := inp.attempt })) := by
  intro s1 s2 y t0 w w1 cTilde c ct0 z u h hAccept
  have hRun : rssThresholdSignStep chalHash sampleInBall st inp =
      .ok { st with nextAttempt := st.nextAttempt + 1 }
        ({ openedMaskedW := addVec4 w inp.maskW,
           openedW1 := w1,
           openedMaskedZ := addVec4 z inp.maskZ,
           openedMaskedLow := addVec4 u inp.maskLow,
           rejectBit := false,
           usedAttempt := inp.attempt },
         some { cTilde := cTilde, z := z, h := h, usedAttempt := inp.attempt }) := by
    unfold rssThresholdSignStep rssSignCore
    rw [decide_eq_true (⟨hEpoch, hAttempt⟩ : inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt)]
    rw [(rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mpr hProducts]
    rw [hProducts]
    dsimp only [rssComputeProducts]
    exact mkRssSignAttemptOutcome_true
      { st with nextAttempt := st.nextAttempt + 1 } inp.attempt
      cTilde w z u inp.maskW inp.maskZ inp.maskLow w1 h hAccept
  dsimp only [rssThresholdSignMachine, PartyMachine.ofOutcome]
  rw [hRun]

private theorem rssThresholdSignStep_ok_meta
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st st' : RssMlDsaSignerState} {inp : RssMlDsaAttemptInput}
    {pubView : RssSignPublicAbortView} {mSig : Option ThresholdSignSig}
    (hOk : rssThresholdSignStep chalHash sampleInBall st inp = .ok st' (pubView, mSig)) :
    inp.epoch = st.epoch ∧
    inp.attempt = st.nextAttempt ∧
    st'.epoch = st.epoch ∧
    st'.nextAttempt = st.nextAttempt + 1 ∧
    pubView.usedAttempt = st.nextAttempt ∧
    (∀ sig, mSig = some sig →
      pubView.rejectBit = false ∧
      sig.usedAttempt = st.nextAttempt ∧
      mldsaVerify chalHash sampleInBall st.A
        (power2RoundHighVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))
        inp.mu sig.cTilde sig.z sig.h = true) := by
  unfold rssThresholdSignStep rssSignCore at hOk
  cases hGate : decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
  | false => rw [hGate] at hOk; cases hOk
  | true =>
    rw [hGate] at hOk
    obtain ⟨hEp, hAtt⟩ := of_decide_eq_true hGate
    cases hSac : rssProductsValid chalHash sampleInBall st inp with
    | false => rw [hSac] at hOk; cases hOk
    | true =>
      rw [hSac] at hOk
      rw [(rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp hSac] at hOk
      dsimp only [rssComputeProducts] at hOk
      obtain ⟨hSt, hPub, hBranch⟩ := mkRssSignAttemptOutcome_eq_ok hOk
      subst hSt hPub
      refine ⟨hEp, hAtt, rfl, rfl, hAtt, ?_⟩
      intro sig hSome
      rcases hBranch with ⟨hAcc, hSigEq⟩ | ⟨_, hNone⟩
      · rw [hSigEq] at hSome
        injection hSome with hSig
        subst hSig
        rw [hAcc]
        dsimp only [Bool.not_true]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hAcc
        rcases hAcc with ⟨⟨⟨hCt0Lt, hzLt⟩, hDiffLt⟩, hWeightLe⟩
        have hB : mldsa44Gamma2 - mldsa44Beta ≤ 95232 := by decide
        obtain ⟨hLowLt, hHighEq⟩ := (centeredDiffNormVec4_lt_iff _ _ hB).mp hDiffLt
        refine ⟨rfl, hAtt, ?_⟩
        unfold mldsaVerify
        dsimp only
        have hUseHint := highBits_az_sub_ct_eq_w1 st.A
          (rssSumVec4List st.s1Subsets) (rssSumVec4List st.s2Subsets)
          (rssSumVec4List inp.ySubsets)
          (sampleInBall (chalHash inp.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
          mldsa44Beta hLowLt hCt0Lt
        dsimp only at hUseHint
        rw [hUseHint, hHighEq]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hzLt, hWeightLe⟩, trivial⟩
      · rw [hNone] at hSome
        cases hSome

private theorem rssThresholdSignStep_err_attempt
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    let nextSt := (rssThresholdSignMachine chalHash sampleInBall).errStep st inp
    st.nextAttempt ≤ nextSt.nextAttempt ∧
    ((inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) →
      nextSt.nextAttempt = st.nextAttempt + 1) := by
  dsimp only [rssThresholdSignMachine, PartyMachine.ofOutcome]
  cases hOut : rssThresholdSignStep chalHash sampleInBall st inp with
  | ok st' outPair =>
    rcases outPair with ⟨pubView, mSig⟩
    obtain ⟨_, _, _, hNext, _⟩ := rssThresholdSignStep_ok_meta hOut
    dsimp only
    exact ⟨by omega, fun _ => hNext⟩
  | err st' _ =>
    dsimp only
    unfold rssThresholdSignStep rssSignCore at hOut
    cases hGate : decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
    | false =>
      rw [hGate] at hOut
      injection hOut with hSt _
      subst hSt
      exact ⟨Nat.le_refl _, fun hg => by rw [decide_eq_true hg] at hGate; cases hGate⟩
    | true =>
      rw [hGate] at hOut
      cases hSac : rssProductsValid chalHash sampleInBall st inp with
      | false =>
        rw [hSac] at hOut
        injection hOut with hSt _
        subst hSt
        exact ⟨by dsimp only; omega, fun _ => rfl⟩
      | true =>
        rw [hSac] at hOut
        exact False.elim (mkRssSignAttemptOutcome_ne_err hOut)

private theorem rssThresholdSignMachine_attempt_mono
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st₀ st_final : RssMlDsaSignerState}
    {trace : List (RssMlDsaAttemptInput × (RssSignPublicAbortView × Option ThresholdSignSig))}
    (hTr : (rssThresholdSignMachine chalHash sampleInBall).ValidTrace st₀ trace st_final) :
    st₀.nextAttempt ≤ st_final.nextAttempt ∧
    (∀ p ∈ trace, st₀.nextAttempt ≤ p.2.1.usedAttempt) ∧
    trace.Pairwise (fun p₁ p₂ => p₁.2.1.usedAttempt ≠ p₂.2.1.usedAttempt) := by
  induction hTr with
  | nil =>
    exact ⟨Nat.le_refl _, (fun _ hm => by cases hm), List.Pairwise.nil⟩
  | @accept sCur sNext sEnd inp out rest hStep _ ih =>
    dsimp only [rssThresholdSignMachine, PartyMachine.ofOutcome] at hStep
    cases hOut : rssThresholdSignStep chalHash sampleInBall sCur inp with
    | err _ _ => rw [hOut] at hStep; cases hStep
    | ok sOk outOk =>
      rw [hOut] at hStep
      injection hStep with hPair
      injection hPair with hStEq hOutEq
      subst hStEq hOutEq
      rcases outOk with ⟨pubView, mSig⟩
      obtain ⟨_, _, _, hNext, hUsed, _⟩ := rssThresholdSignStep_ok_meta hOut
      obtain ⟨hMonoTail, hGeTail, hPairTail⟩ := ih
      refine ⟨by omega, ?_, List.Pairwise.cons ?_ hPairTail⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hMem
        · dsimp only; omega
        · have h1 := hGeTail p hMem; omega
      · intro p₂ hp₂
        have h1 := hGeTail p₂ hp₂
        dsimp only; omega
  | @reject sCur sEnd inp rest _hNone _ ih =>
    obtain ⟨hErrGe, _⟩ := rssThresholdSignStep_err_attempt chalHash sampleInBall sCur inp
    obtain ⟨hMonoTail, hGeTail, hPairTail⟩ := ih
    refine ⟨by omega, fun p hp => ?_, hPairTail⟩
    have h1 := hGeTail p hp; omega

/-- **Flagship §2.4 Theorem — `(t, m)` Aggregate Rejection-Sampling Mask Bijection, RAM Attempt Counter &
    Parameterized Verification Completeness (`threshold_mldsa_rss_abort_leakage_and_completeness`, fixing `C0-1`)**:
    1. **Honest Abort Transcript & Unmasked-`z` Suppression (`rejectBit = true`)**: Whenever a valid
       attempt (`inp.epoch = st.epoch`, `inp.attempt = st.nextAttempt`, `rssProductsValid chalHash sampleInBall st inp = true`)
       violates `‖z‖_∞ < γ₁ - β`, `‖LowBits(w - c*s2)‖_∞ < γ₂ - β`, or `HighBits(w - c*s2) = HighBits(w)`,
       `rssThresholdSignStep` emits `(pubView, none)` (`pubView.rejectBit = true`, `pubView.openedW1 = HighBits(w)`,
       no separate unmasked `(z, h)` field) and burns `st'.nextAttempt = st.nextAttempt + 1`.
    2. **Explicit Leakage-Parameterized Abort Simulation (`rssAbortSimulator` + `rssMaskTripleEquiv`)**:
       Conditioned on the exact ideal abort leakage `(HighBits(w), rejectBit := true, inp.attempt)`,
       the `< q` RSS masks `(maskW, maskZ, maskLow)` map onto `(openedMaskedW, openedMaskedZ, openedMaskedLow)`
       via the constructive group bijection `rssMaskTripleEquiv w z u`, so `rssAbortSimulator` reproduces
       `pubView` identically with **zero** access to secret shares `(s1Subsets, s2Subsets, ySubsets)`!
    3. **Multi-Turn Attempt-Burn Uniqueness (`PartyMachine.ValidTrace`)**: Across ANY multi-turn trace of
       interleaved rejected and accepted attempts, `nextAttempt` is monotonically non-decreasing and every
       emitted transcript uses a strictly distinct `usedAttempt` index.
    4. **Parameterized algebraic `mldsaVerify` completeness**: Every accepted signature `some sig` satisfies
       `pubView.rejectBit = false` and `mldsaVerify = true` under the RSS aggregate public key! -/
theorem threshold_mldsa_rss_abort_leakage_and_completeness
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    let M := rssThresholdSignMachine chalHash sampleInBall
    (∀ (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput),
      inp.epoch = st.epoch →
      inp.attempt = st.nextAttempt →
      rssProductsValid chalHash sampleInBall st inp = true →
      let s1 := rssSumVec4List st.s1Subsets
      let s2 := rssSumVec4List st.s2Subsets
      let y := rssSumVec4List inp.ySubsets
      let w := matVecMul4 st.A y
      let w1 := highBitsVec4 w
      let c := sampleInBall (chalHash inp.mu w1)
      let z := addVec4 y (mulPolyVec4 c s1)
      let u := subVec4 w (mulPolyVec4 c s2)
      (¬ (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) ∨
       ¬ (lowBitsNormVec4 u < mldsa44Gamma2 - mldsa44Beta) ∨
       highBitsVec4 u ≠ w1) →
      ∃ (st' : RssMlDsaSignerState) (pubView : RssSignPublicAbortView),
        M.step st inp = some (st', (pubView, none)) ∧
        st'.nextAttempt = st.nextAttempt + 1 ∧
        pubView.rejectBit = true ∧
        pubView.openedW1 = w1 ∧
        rssAbortSimulator w1 inp.attempt
          ((rssMaskTripleEquiv w z u).toFun (inp.maskW, inp.maskZ, inp.maskLow)) = pubView) ∧
    (∀ (st₀ st_final : RssMlDsaSignerState)
       (trace : List (RssMlDsaAttemptInput × (RssSignPublicAbortView × Option ThresholdSignSig))),
      M.ValidTrace st₀ trace st_final →
      st₀.nextAttempt ≤ st_final.nextAttempt ∧
      trace.Pairwise (fun p₁ p₂ => p₁.2.1.usedAttempt ≠ p₂.2.1.usedAttempt)) ∧
    (∀ (st st' : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
       (pubView : RssSignPublicAbortView) (sig : ThresholdSignSig),
      M.step st inp = some (st', (pubView, some sig)) →
      pubView.rejectBit = false ∧
      mldsaVerify chalHash sampleInBall st.A
        (power2RoundHighVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))
        inp.mu sig.cTilde sig.z sig.h = true) := by
  intro M
  refine ⟨?_, ?_, ?_⟩
  · intro st inp hEp hAtt hSac s1 s2 y w w1 c z u hRejCond
    have hAccFalse :
        (decide (infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))) < mldsa44Gamma2) &&
         decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
         decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
         decide (hintWeightVec4 (makeHintVec4
           (negVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))
           (addVec4 u (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))) ≤ mldsa44Omega)) = false := by
      cases hBool :
          (decide (infNormVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))) < mldsa44Gamma2) &&
           decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
           decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta) &&
           decide (hintWeightVec4 (makeHintVec4
             (negVec4 (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))
             (addVec4 u (mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))))) ≤ mldsa44Omega)) with
      | false => rfl
      | true =>
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hBool
        rcases hBool with ⟨⟨⟨_, hzLt⟩, hDiffLt⟩, _⟩
        have hB : mldsa44Gamma2 - mldsa44Beta ≤ 95232 := by decide
        obtain ⟨hLowLt, hHighEq⟩ := (centeredDiffNormVec4_lt_iff u w hB).mp hDiffLt
        rcases hRejCond with hBadZ | hBadLow | hBadHigh
        · exact hBadZ hzLt
        · exact hBadLow hLowLt
        · exact hBadHigh hHighEq
    let stBurned : RssMlDsaSignerState := { st with nextAttempt := st.nextAttempt + 1 }
    let pubView : RssSignPublicAbortView :=
      { openedMaskedW := addVec4 w inp.maskW
        openedW1 := w1
        openedMaskedZ := addVec4 z inp.maskZ
        openedMaskedLow := addVec4 u inp.maskLow
        rejectBit := true
        usedAttempt := inp.attempt }
    refine ⟨stBurned, pubView, ?_, rfl, rfl, rfl, rfl⟩
    dsimp only [M, rssThresholdSignMachine, PartyMachine.ofOutcome]
    have hStepFalse : rssThresholdSignStep chalHash sampleInBall st inp = .ok stBurned (pubView, none) := by
      unfold rssThresholdSignStep rssSignCore
      rw [decide_eq_true ⟨hEp, hAtt⟩, hSac]
      rw [(rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp hSac]
      dsimp only [rssComputeProducts]
      exact mkRssSignAttemptOutcome_false stBurned inp.attempt (chalHash inp.mu w1)
        w z u inp.maskW inp.maskZ inp.maskLow w1 _ hAccFalse
    rw [hStepFalse]
  · intro st₀ st_final trace hTr
    obtain ⟨hMono, _, hPair⟩ := rssThresholdSignMachine_attempt_mono hTr
    exact ⟨hMono, hPair⟩
  · intro st st' inp pubView sig hStep
    dsimp only [M, rssThresholdSignMachine, PartyMachine.ofOutcome] at hStep
    cases hOut : rssThresholdSignStep chalHash sampleInBall st inp with
    | err _ _ => rw [hOut] at hStep; cases hStep
    | ok stOk outOk =>
      rw [hOut] at hStep
      injection hStep with hPair
      injection hPair with hStEq hOutEq
      subst hStEq hOutEq
      have hSpec := (rssThresholdSignStep_ok_meta hOut).2.2.2.2.2 sig rfl
      exact ⟨hSpec.1, hSpec.2.2⟩

private def natTreeList204 : {d : Nat} → NatTree d → List Nat
  | 0, .leaf n => [n]
  | _ + 1, .branch l r => natTreeList204 l ++ natTreeList204 r

private def packSix204 : List Nat → List UInt8
  | a :: b :: c :: d :: rest =>
    UInt8.ofNat (a + 64 * b) :: UInt8.ofNat (b / 4 + 16 * c) ::
      UInt8.ofNat (c / 16 + 4 * d) :: packSix204 rest
  | _ => []

def mldsa44ChallengeHash (mu : List UInt8) (w1 : Fin 4 → NatTree 8) : List UInt8 :=
  shake256Xof 32 (mu ++ ((List.finRange 4).flatMap (fun i => packSix204 (natTreeList204 (w1 i)))))

/-- Non-vacuous inhabitedness witness for `rssThresholdSignMachine` exercising BOTH:
    (i) an accepted RSS attempt emitting `some sig` with `mldsaVerify = true` and `rejectBit = false`, AND
    (ii) a boundary-rejected RSS attempt emitting `(pubViewRej, none)` with `rejectBit = true`! -/
theorem threshold_mldsa_rss_inhabited :
    ∃ (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
      (sampleInBall : List UInt8 → Poly256)
      (st stAcc stRej : RssMlDsaSignerState)
      (inpAcc inpRej : RssMlDsaAttemptInput)
      (pubAcc pubRej : RssSignPublicAbortView)
      (sig : ThresholdSignSig),
      (rssThresholdSignMachine chalHash sampleInBall).step st inpAcc = some (stAcc, (pubAcc, some sig)) ∧
      pubAcc.rejectBit = false ∧
      mldsaVerify chalHash sampleInBall st.A
        (power2RoundHighVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))
        inpAcc.mu sig.cTilde sig.z sig.h = true ∧
      (rssThresholdSignMachine chalHash sampleInBall).step st inpRej = some (stRej, (pubRej, none)) ∧
      pubRej.rejectBit = true ∧
      st.epoch = 0 ∧ st.nextAttempt = 0 ∧
      inpAcc.products = rssComputeProducts chalHash sampleInBall st inpAcc.mu inpAcc.ySubsets ∧
      rssSumVec4List st.s1Subsets ≠ rssZeroVec4 := by
  let chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8 := mldsa44ChallengeHash
  let sampleInBall : List UInt8 → Poly256 := fun _ => PolyTree.constUnit 8
  let p1 : Poly256 := polyTreeConstLeaf 8 Fq204.one
  let v1 : PolyVec4 := fun _ => p1
  let yBad : PolyVec4 := fun _ => polyTreeConstLeaf 8 ⟨131072, by decide⟩
  let st : RssMlDsaSignerState :=
    { epoch := 0, nextAttempt := 0, A := shiftMat4, s1Subsets := [v1], s2Subsets := [v1] }
  let inpAcc : RssMlDsaAttemptInput :=
    { epoch := 0, sessionId := [0x01], attempt := 0, mu := [0x42],
      ySubsets := [v1], maskW := v1, maskZ := v1, maskLow := v1,
      products := rssComputeProducts chalHash sampleInBall st [0x42] [v1] }
  let inpRej : RssMlDsaAttemptInput :=
    { epoch := 0, sessionId := [0x01], attempt := 0, mu := [0x42],
      ySubsets := [yBad], maskW := v1, maskZ := v1, maskLow := v1,
      products := rssComputeProducts chalHash sampleInBall st [0x42] [yBad] }
  have hSum1 : rssSumVec4List [v1] = v1 := by
    dsimp only [rssSumVec4List]; exact addVec4_rssZero_right v1
  have hSumBad : rssSumVec4List [yBad] = yBad := by
    dsimp only [rssSumVec4List]; exact addVec4_rssZero_right yBad
  have hMv : matVecMul4 shiftMat4 v1 = v1 := matVecMul4_shiftMat4_const p1
  have hMul1 : ∀ w : PolyVec4, mulPolyVec4 (PolyTree.constUnit 8) w = w := fun w => by
    funext i; exact negacyclicMul_one_left (w i)
  have hAddV1 : addVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 (Fq204.add Fq204.one Fq204.one)) := by
    funext i; exact polyTreeConstLeaf_add Fq204.one Fq204.one 8
  have hSubSelf : subVec4 v1 v1 = (fun _ => polyTreeConstLeaf 8 Fq204.zero) := by
    funext i; dsimp only [subVec4, v1]
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm, polyTree_add_left_neg, polyTreeConstLeaf_zero_eq]
  have hCt0 : infNormVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))) <
      mldsa44Gamma2 := by
    rw [hMv, hMul1, hAddV1]
    unfold infNormVec4 power2RoundLowVec4
    dsimp only
    simp only [polyTreeConstLeaf_power2RoundLow, polyTreeConstLeaf_infNorm, Nat.max_self]
    decide
  have hZ : infNormVec4 (addVec4 v1 (mulPolyVec4 (PolyTree.constUnit 8) v1)) < mldsa44Gamma1 - mldsa44Beta := by
    rw [hMul1, hAddV1]
    unfold infNormVec4
    dsimp only
    simp only [polyTreeConstLeaf_infNorm, Nat.max_self]
    decide
  have hDiff : centeredDiffNormVec4 (subVec4 (matVecMul4 shiftMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
      (highBitsVec4 (matVecMul4 shiftMat4 v1)) < mldsa44Gamma2 - mldsa44Beta := by
    rw [hMv, hMul1, hSubSelf]
    unfold centeredDiffNormVec4 highBitsVec4
    dsimp only [v1, p1]
    simp only [polyTreeConstLeaf_centeredDiffNorm, Nat.max_self]
    decide
  have hW : hintWeightVec4 (makeHintVec4
      (negVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))))
      (addVec4 (subVec4 (matVecMul4 shiftMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
               (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))))) ≤
      mldsa44Omega := by
    rw [hMv, hMul1, hMul1, hSubSelf, hAddV1]
    unfold hintWeightVec4 makeHintVec4 negVec4 addVec4 power2RoundLowVec4
    dsimp only
    simp only [polyTreeConstLeaf_power2RoundLow, polyTreeConstLeaf_neg,
      polyTreeConstLeaf_add, polyTreeConstLeaf_hintWeight]
    decide
  have hAcc :
      (decide (infNormVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))) < mldsa44Gamma2) &&
       decide (infNormVec4 (addVec4 v1 (mulPolyVec4 (PolyTree.constUnit 8) v1)) < mldsa44Gamma1 - mldsa44Beta) &&
       decide (centeredDiffNormVec4 (subVec4 (matVecMul4 shiftMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
         (highBitsVec4 (matVecMul4 shiftMat4 v1)) < mldsa44Gamma2 - mldsa44Beta) &&
       decide (hintWeightVec4 (makeHintVec4
         (negVec4 (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))))
         (addVec4 (subVec4 (matVecMul4 shiftMat4 v1) (mulPolyVec4 (PolyTree.constUnit 8) v1))
                  (mulPolyVec4 (PolyTree.constUnit 8) (power2RoundLowVec4 (addVec4 (matVecMul4 shiftMat4 v1) v1))))) ≤ mldsa44Omega)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hCt0, hZ⟩, hDiff⟩, hW⟩
  have hZBad : ¬ (infNormVec4 (addVec4 (rssSumVec4List inpRej.ySubsets)
      (mulPolyVec4 (sampleInBall (chalHash inpRej.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpRej.ySubsets)))))
        (rssSumVec4List st.s1Subsets))) < mldsa44Gamma1 - mldsa44Beta) := by
    dsimp only [st, inpRej, sampleInBall, chalHash]
    rw [hSumBad, hSum1, hMul1]
    have hAddBad : addVec4 yBad v1 = (fun _ => polyTreeConstLeaf 8 (Fq204.add ⟨131072, by decide⟩ Fq204.one)) := by
      funext i; exact polyTreeConstLeaf_add ⟨131072, by decide⟩ Fq204.one 8
    rw [hAddBad]
    unfold infNormVec4
    dsimp only
    simp only [polyTreeConstLeaf_infNorm, Nat.max_self]
    decide
  obtain ⟨stRej, pubRej, hStepRej, _, hRejBit, _, _⟩ :=
    (threshold_mldsa_rss_abort_leakage_and_completeness chalHash sampleInBall).1 st inpRej rfl rfl
      ((rssProductsValid_eq_true_iff chalHash sampleInBall st inpRej).mpr rfl) (Or.inl hZBad)
  have hAccFull :
      (decide (infNormVec4 (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
        (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))) < mldsa44Gamma2) &&
       decide (infNormVec4 (addVec4 (rssSumVec4List inpAcc.ySubsets)
         (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
           (rssSumVec4List st.s1Subsets))) < mldsa44Gamma1 - mldsa44Beta) &&
       decide (centeredDiffNormVec4
         (subVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets))
           (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
             (rssSumVec4List st.s2Subsets)))
         (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets))) < mldsa44Gamma2 - mldsa44Beta) &&
       decide (hintWeightVec4 (makeHintVec4
         (negVec4 (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
           (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))))
         (addVec4 (subVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets))
           (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
             (rssSumVec4List st.s2Subsets)))
           (mulPolyVec4 (sampleInBall (chalHash inpAcc.mu (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inpAcc.ySubsets)))))
             (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets)) (rssSumVec4List st.s2Subsets)))))) ≤ mldsa44Omega)) = true := by
    dsimp only [st, inpAcc, sampleInBall, chalHash]
    rw [hSum1]
    exact hAcc
  let s1Acc := rssSumVec4List st.s1Subsets
  let s2Acc := rssSumVec4List st.s2Subsets
  let yAcc := rssSumVec4List inpAcc.ySubsets
  let t0Acc := power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1Acc) s2Acc)
  let wAcc := matVecMul4 st.A yAcc
  let w1Acc := highBitsVec4 wAcc
  let cTildeAcc := chalHash inpAcc.mu w1Acc
  let cAcc := sampleInBall cTildeAcc
  let ct0Acc := mulPolyVec4 cAcc t0Acc
  let zAcc := addVec4 yAcc (mulPolyVec4 cAcc s1Acc)
  let uAcc := subVec4 wAcc (mulPolyVec4 cAcc s2Acc)
  let hintAcc := makeHintVec4 (negVec4 ct0Acc) (addVec4 uAcc ct0Acc)
  have hStepAcc :
      (rssThresholdSignMachine chalHash sampleInBall).step st inpAcc =
        some ({ st with nextAttempt := st.nextAttempt + 1 },
          ({ openedMaskedW := addVec4 wAcc inpAcc.maskW,
             openedW1 := w1Acc,
             openedMaskedZ := addVec4 zAcc inpAcc.maskZ,
             openedMaskedLow := addVec4 uAcc inpAcc.maskLow,
             rejectBit := false,
             usedAttempt := inpAcc.attempt },
           some { cTilde := cTildeAcc,
                  z := zAcc,
                  h := hintAcc,
                  usedAttempt := inpAcc.attempt })) :=
    rssThresholdSignMachine_step_accept chalHash sampleInBall st inpAcc rfl rfl rfl hAccFull
  obtain ⟨hRejFalse, hVer⟩ :=
    (threshold_mldsa_rss_abort_leakage_and_completeness chalHash sampleInBall).2.2 _ _ _ _ _ hStepAcc
  have hNz : rssSumVec4List st.s1Subsets ≠ rssZeroVec4 := by
    dsimp only [st]
    rw [hSum1]
    intro h
    have he : polyTreeConstLeaf 8 Fq204.one = PolyTree.zero 8 := congrFun h (0 : Fin 4)
    have hv := congrArg PolyTree.infNorm he
    rw [polyTreeConstLeaf_infNorm] at hv
    change 1 = 0 at hv
    omega
  exact ⟨chalHash, sampleInBall, st, _, stRej, inpAcc, inpRej, _, pubRej, _,
         hStepAcc, hRejFalse, hVer, hStepRej, hRejBit, rfl, rfl, rfl, hNz⟩

/-! ## §3. Dealerless 2-of-5 Replicated Poseidon2 Threshold OPRF (`voprf.rs` / `toprf_engine.rs`, `P0-08`–`P0-09`) -/

/-! ### §3.1 Combinatorial $\binom{5}{3} = 10$ Subset Coverage & Cross-Term Holder Invariant -/

/-- Exact ascending enumeration of all $\binom{5}{3} = 10$ 3-server subsets of `Fin 5`. -/
def subsets3Of5 : List (List (Fin 5)) :=
  [ [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4],
    [0, 3, 4], [1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4] ]

/-- **Combinatorial $\binom{5}{3} = 10$ Pairwise Intersection Theorem (`subsets3Of5_intersect_nonempty`)**:
    Every pair `(A, B)` of 3-server subsets in `(t = 2, n = 5)` replicated secret sharing shares
    at least $3 + 3 - 5 = 1$ common server (`∃ s : Fin 5, s ∈ A ∧ s ∈ B`). -/
theorem subsets3Of5_intersect_nonempty :
    subsets3Of5.length = 10 ∧
    subsets3Of5.Nodup ∧
    (∀ A ∈ subsets3Of5, A.length = 3 ∧ A.Nodup) ∧
    (∀ A ∈ subsets3Of5, ∀ B ∈ subsets3Of5, ∃ s : Fin 5, s ∈ A ∧ s ∈ B) := by
  decide

/-- **`#tooth` (`tooth_subsets2Of5_disjoint`)**:
    Shrinking subset size from $3$ to $2$ on $n = 5$ servers ($t = 3$, violating $5 \ge 2 \cdot 3 - 1$? No:
    $5 = 2 \cdot 3 - 1$ has subset size $5 - 3 + 1 = 3$, whereas $t = 4$ has subset size $2 < 5/2$)
    admits disjoint subsets `[0, 1]` and `[2, 3]` with **zero** common server to evaluate cross-products! -/
theorem tooth_subsets2Of5_disjoint :
    let A : List (Fin 5) := [0, 1]
    let B : List (Fin 5) := [2, 3]
    A.length = 2 ∧ B.length = 2 ∧ A.Nodup ∧ B.Nodup ∧
    (∀ s : Fin 5, ¬ (s ∈ A ∧ s ∈ B)) := by
  decide

def fin5List : List (Fin 5) := [0, 1, 2, 3, 4]

/-- The 4 servers holding additive component `c` (`party != c`, `voprf.rs:410, 514, 598`). -/
def fin5Others (c : Fin 5) : List (Fin 5) :=
  fin5List.filter (fun p => decide (p ≠ c))

/-- The 3 ascending holders of ordered cross-term `(i, j)` (`i ≠ j`), matching `toprf_engine.rs:103-113`. -/
def toprfHolders (i j : Fin 5) : List (Fin 5) :=
  fin5List.filter (fun p => decide (p ≠ i) && decide (p ≠ j))

/-- Every component `c` is held by 4 distinct servers, and every off-diagonal cross-term `(i, j)` (`i ≠ j`)
    is held by a 3-server subset `toprfHolders i j ∈ subsets3Of5`! -/
theorem toprfHolders_spec :
    (∀ c : Fin 5,
      (fin5Others c).length = 4 ∧
      (fin5Others c).Nodup ∧
      (∀ p : Fin 5, p ∈ fin5Others c ↔ p ≠ c)) ∧
    (∀ i j : Fin 5, i ≠ j →
      (toprfHolders i j).length = 3 ∧
      (toprfHolders i j).Nodup ∧
      (toprfHolders i j ∈ subsets3Of5) ∧
      (∀ p : Fin 5, p ∈ toprfHolders i j ↔ (p ≠ i ∧ p ≠ j))) := by
  decide

private theorem fin5Others_0 : fin5Others 0 = [1, 2, 3, 4] := by decide
private theorem fin5Others_1 : fin5Others 1 = [0, 2, 3, 4] := by decide
private theorem fin5Others_2 : fin5Others 2 = [0, 1, 3, 4] := by decide
private theorem fin5Others_3 : fin5Others 3 = [0, 1, 2, 4] := by decide
private theorem fin5Others_4 : fin5Others 4 = [0, 1, 2, 3] := by decide

/-! ### §3.2 Exact 5-Component Replicated Arithmetic Engine & 30-Round `Poseidon2` Simulation -/

/-- 5-component additive wire `Wire = [u64; 5]` over `Goldilocks` (`toprf_engine.rs:38`). -/
abbrev ToprfWire := Fin 5 → Goldilocks

/-- Sum of all 5 additive components of a `ToprfWire`. -/
def sumWire5 (w : ToprfWire) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.add
      (Goldilocks.add (Goldilocks.add (w 0) (w 1)) (w 2))
      (w 3))
    (w 4)

def sumGoldList : List Goldilocks → Goldilocks
  | [] => Goldilocks.zero
  | a :: as => Goldilocks.add a (sumGoldList as)

/-- Exact 5-component replicated multiplication `z = x * y` (`toprf_engine.rs:244-300`):
    - Component `c` accumulates diagonal `x_c * y_c`,
    - Outgoing masks `+ ∑_{j ≠ c} mask(c, j)` (`z[i] += r`),
    - Incoming masked cross-terms `+ ∑_{i ≠ c} (x_i * y_c - mask(i, c))` (`z[j] += x_i * y_j - r`). -/
def toprfMulWire (x y : ToprfWire) (mask : Fin 5 → Fin 5 → Goldilocks) : ToprfWire :=
  fun c =>
    let diag := Goldilocks.mul (x c) (y c)
    let outMasks := sumGoldList ((fin5Others c).map (fun j => mask c j))
    let inTerms := sumGoldList ((fin5Others c).map (fun i =>
      Goldilocks.sub (Goldilocks.mul (x i) (y c)) (mask i c)))
    Goldilocks.add (Goldilocks.add diag outMasks) inTerms

/-- **5-Component Replicated Multiplication Soundness (`toprfMulWire_sum`)**:
    For ANY 20 off-diagonal masks `mask i j`, all `+ mask(i, j)` and `- mask(i, j)` terms cancel
    exact-algebraically across components `i` and `j`, leaving all 25 terms `∑_{i,j} x_i * y_j = (∑ x_i)*(∑ y_j)`. -/
theorem toprfMulWire_sum (x y : ToprfWire) (mask : Fin 5 → Fin 5 → Goldilocks) :
    sumWire5 (toprfMulWire x y mask) = Goldilocks.mul (sumWire5 x) (sumWire5 y) := by
  unfold sumWire5 toprfMulWire
  rw [fin5Others_0, fin5Others_1, fin5Others_2, fin5Others_3, fin5Others_4]
  dsimp only [List.map, sumGoldList]
  have hz : Goldilocks.zero = goldOfInt 0 := rfl
  rw [hz,
      ← goldOfInt_nat (x 0), ← goldOfInt_nat (x 1), ← goldOfInt_nat (x 2),
      ← goldOfInt_nat (x 3), ← goldOfInt_nat (x 4),
      ← goldOfInt_nat (y 0), ← goldOfInt_nat (y 1), ← goldOfInt_nat (y 2),
      ← goldOfInt_nat (y 3), ← goldOfInt_nat (y 4),
      ← goldOfInt_nat (mask 0 1), ← goldOfInt_nat (mask 0 2), ← goldOfInt_nat (mask 0 3), ← goldOfInt_nat (mask 0 4),
      ← goldOfInt_nat (mask 1 0), ← goldOfInt_nat (mask 1 2), ← goldOfInt_nat (mask 1 3), ← goldOfInt_nat (mask 1 4),
      ← goldOfInt_nat (mask 2 0), ← goldOfInt_nat (mask 2 1), ← goldOfInt_nat (mask 2 3), ← goldOfInt_nat (mask 2 4),
      ← goldOfInt_nat (mask 3 0), ← goldOfInt_nat (mask 3 1), ← goldOfInt_nat (mask 3 2), ← goldOfInt_nat (mask 3 4),
      ← goldOfInt_nat (mask 4 0), ← goldOfInt_nat (mask 4 1), ← goldOfInt_nat (mask 4 2), ← goldOfInt_nat (mask 4 3)]
  simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
  congr 1
  simp only [Int.add_mul, Int.mul_add]
  omega

/-- Replicated depth-3 S-box `x ↦ x^7` (`x^2 -> (x^3, x^4) -> x^7`, `toprf_engine.rs:305-313`). -/
def toprfSboxWire (w : ToprfWire)
    (m1 m2 m3 m4 : Fin 5 → Fin 5 → Goldilocks) : ToprfWire :=
  let x2 := toprfMulWire w w m1
  let x3 := toprfMulWire x2 w m2
  let x4 := toprfMulWire x2 x2 m3
  toprfMulWire x3 x4 m4

theorem toprfSboxWire_sum (w : ToprfWire) (m1 m2 m3 m4 : Fin 5 → Fin 5 → Goldilocks) :
    sumWire5 (toprfSboxWire w m1 m2 m3 m4) = sbox7 (sumWire5 w) := by
  unfold toprfSboxWire sbox7
  dsimp only
  simp only [toprfMulWire_sum]

/-- 5-component replicated Width-12 `Poseidon2` state (`[Wire; 12]`, `toprf_engine.rs:83`). -/
abbrev ToprfState12 := Fin 5 → Poseidon2State12

/-- Reconstruct plaintext `Poseidon2State12` by summing the 5 replicated component columns. -/
def sumToprfState12 (st : ToprfState12) : Poseidon2State12 :=
  state12Add (state12Add (state12Add (state12Add (st 0) (st 1)) (st 2)) (st 3)) (st 4)

private theorem sumToprfState12_lanes (st : ToprfState12) :
    sumToprfState12 st =
      ⟨⟨sumWire5 (fun c => (st c).b0.x0), sumWire5 (fun c => (st c).b0.x1),
        sumWire5 (fun c => (st c).b0.x2), sumWire5 (fun c => (st c).b0.x3)⟩,
       ⟨sumWire5 (fun c => (st c).b1.x0), sumWire5 (fun c => (st c).b1.x1),
        sumWire5 (fun c => (st c).b1.x2), sumWire5 (fun c => (st c).b1.x3)⟩,
       ⟨sumWire5 (fun c => (st c).b2.x0), sumWire5 (fun c => (st c).b2.x1),
        sumWire5 (fun c => (st c).b2.x2), sumWire5 (fun c => (st c).b2.x3)⟩⟩ := by
  unfold sumToprfState12 sumWire5
  simp only [state12Add_eq, lane4Add_eq]

/-- Public constant addition into component `0` (`if party != 0 { st[0] = gl_add(st[0], v) }`, `toprf_engine.rs:96-100`). -/
def toprfAddPublicState12 (rc : Poseidon2State12) (st : ToprfState12) : ToprfState12 :=
  fun c => if c = 0 then state12Add (st 0) rc else st c

private theorem sumWire5_add_comp0 (w : ToprfWire) (v : Goldilocks) :
    sumWire5 (fun c => if c = 0 then Goldilocks.add (w 0) v else w c) =
      Goldilocks.add (sumWire5 w) v := by
  unfold sumWire5
  have h1 : (1 : Fin 5) ≠ 0 := by decide
  have h2 : (2 : Fin 5) ≠ 0 := by decide
  have h3 : (3 : Fin 5) ≠ 0 := by decide
  have h4 : (4 : Fin 5) ≠ 0 := by decide
  simp only [↓reduceIte, h1, h2, h3, h4]
  rw [← goldOfInt_nat (w 0), ← goldOfInt_nat (w 1), ← goldOfInt_nat (w 2),
      ← goldOfInt_nat (w 3), ← goldOfInt_nat (w 4), ← goldOfInt_nat v]
  simp only [goldOfInt_add]
  congr 1
  omega

theorem sumToprfState12_addPublic (rc : Poseidon2State12) (st : ToprfState12) :
    sumToprfState12 (toprfAddPublicState12 rc st) = state12Add (sumToprfState12 st) rc := by
  rw [sumToprfState12_lanes, sumToprfState12_lanes, state12Add_eq]
  dsimp only [toprfAddPublicState12]
  have hProj : ∀ (f : Poseidon2State12 → Goldilocks)
      (hf : ∀ a b, f (state12Add a b) = Goldilocks.add (f a) (f b)),
      (fun c : Fin 5 => f (if c = 0 then state12Add (st 0) rc else st c)) =
        (fun c : Fin 5 => if c = 0 then Goldilocks.add (f (st 0)) (f rc) else f (st c)) := by
    intro f hf
    funext c
    by_cases hc : c = 0
    · subst hc; simp only [↓reduceIte, hf]
    · simp only [hc, ↓reduceIte]
  rw [hProj (fun q => q.b0.x0) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b0.x1) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b0.x2) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b0.x3) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b1.x0) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b1.x1) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b1.x2) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b1.x3) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b2.x0) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b2.x1) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b2.x2) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      hProj (fun q => q.b2.x3) (fun a b => by simp [state12Add_eq, lane4Add_eq]),
      sumWire5_add_comp0 (fun c => (st c).b0.x0),
      sumWire5_add_comp0 (fun c => (st c).b0.x1),
      sumWire5_add_comp0 (fun c => (st c).b0.x2),
      sumWire5_add_comp0 (fun c => (st c).b0.x3),
      sumWire5_add_comp0 (fun c => (st c).b1.x0),
      sumWire5_add_comp0 (fun c => (st c).b1.x1),
      sumWire5_add_comp0 (fun c => (st c).b1.x2),
      sumWire5_add_comp0 (fun c => (st c).b1.x3),
      sumWire5_add_comp0 (fun c => (st c).b2.x0),
      sumWire5_add_comp0 (fun c => (st c).b2.x1),
      sumWire5_add_comp0 (fun c => (st c).b2.x2),
      sumWire5_add_comp0 (fun c => (st c).b2.x3)]
  simp only [lane4Add_eq]

private theorem sumToprfState12_applyME (f : Fin 5 → Poseidon2State12) :
    sumToprfState12 (fun c => applyME (f c)) = applyME (sumToprfState12 f) := by
  unfold sumToprfState12
  rw [← applyME_add, ← applyME_add, ← applyME_add, ← applyME_add]

private theorem sumToprfState12_applyMI (f : Fin 5 → Poseidon2State12) :
    sumToprfState12 (fun c => applyMI (f c)) = applyMI (sumToprfState12 f) := by
  unfold sumToprfState12
  rw [← applyMI_add, ← applyMI_add, ← applyMI_add, ← applyMI_add]

/-- Per-S-box 4-gate mask bundle (`m1, m2, m3, m4 : Fin 5 → Fin 5 → Goldilocks`). -/
structure SboxMask4 where
  m1 : Fin 5 → Fin 5 → Goldilocks
  m2 : Fin 5 → Fin 5 → Goldilocks
  m3 : Fin 5 → Fin 5 → Goldilocks
  m4 : Fin 5 → Fin 5 → Goldilocks

/-- Replicated external full-width S-box + `applyME` round (`toprf_engine.rs:318-337`). -/
def toprfExtRound (masks : Fin 12 → SboxMask4) (rc : Poseidon2State12) (st : ToprfState12) : ToprfState12 :=
  let s := toprfAddPublicState12 rc st
  let sb (idx : Fin 12) (f : Poseidon2State12 → Goldilocks) : ToprfWire :=
    let m := masks idx
    toprfSboxWire (fun c => f (s c)) m.m1 m.m2 m.m3 m.m4
  let y0 := sb ⟨0, by decide⟩ (fun q => q.b0.x0)
  let y1 := sb ⟨1, by decide⟩ (fun q => q.b0.x1)
  let y2 := sb ⟨2, by decide⟩ (fun q => q.b0.x2)
  let y3 := sb ⟨3, by decide⟩ (fun q => q.b0.x3)
  let y4 := sb ⟨4, by decide⟩ (fun q => q.b1.x0)
  let y5 := sb ⟨5, by decide⟩ (fun q => q.b1.x1)
  let y6 := sb ⟨6, by decide⟩ (fun q => q.b1.x2)
  let y7 := sb ⟨7, by decide⟩ (fun q => q.b1.x3)
  let y8 := sb ⟨8, by decide⟩ (fun q => q.b2.x0)
  let y9 := sb ⟨9, by decide⟩ (fun q => q.b2.x1)
  let y10 := sb ⟨10, by decide⟩ (fun q => q.b2.x2)
  let y11 := sb ⟨11, by decide⟩ (fun q => q.b2.x3)
  fun c => applyME ⟨⟨y0 c, y1 c, y2 c, y3 c⟩, ⟨y4 c, y5 c, y6 c, y7 c⟩, ⟨y8 c, y9 c, y10 c, y11 c⟩⟩

/-- Replicated internal lane-0 S-box + `applyMI` round (`toprf_engine.rs:318-337`). -/
def toprfIntRound (m : SboxMask4) (rc : Goldilocks) (st : ToprfState12) : ToprfState12 :=
  let w0 : ToprfWire := fun c => if c = 0 then Goldilocks.add (st 0).b0.x0 rc else (st c).b0.x0
  let y0 := toprfSboxWire w0 m.m1 m.m2 m.m3 m.m4
  fun c => applyMI ⟨⟨y0 c, (st c).b0.x1, (st c).b0.x2, (st c).b0.x3⟩, (st c).b1, (st c).b2⟩

theorem sumToprfState12_extRound (masks : Fin 12 → SboxMask4) (rc : Poseidon2State12) (st : ToprfState12) :
    sumToprfState12 (toprfExtRound masks rc st) = externalRound rc (sumToprfState12 st) := by
  unfold toprfExtRound
  dsimp only
  rw [sumToprfState12_applyME, externalRound_eq, ← sumToprfState12_addPublic rc st]
  congr 1
  rw [sumToprfState12_lanes, sboxState12_eq, sumToprfState12_lanes]
  dsimp only
  simp only [toprfSboxWire_sum]

theorem sumToprfState12_intRound (m : SboxMask4) (rc : Goldilocks) (st : ToprfState12) :
    sumToprfState12 (toprfIntRound m rc st) = internalRound rc (sumToprfState12 st) := by
  unfold toprfIntRound
  dsimp only
  rw [sumToprfState12_applyMI, internalRound_eq]
  congr 1
  rw [sumToprfState12_lanes, sumToprfState12_lanes]
  dsimp only
  rw [toprfSboxWire_sum, sumWire5_add_comp0 (fun c => (st c).b0.x0)]

/-- Mask schedule for all 30 rounds (`4` initial external + `22` internal + `4` terminal external) of `poseidon2Perm12`. -/
structure ToprfPerm12Masks where
  initExt : Nat → Fin 12 → SboxMask4
  internal : Nat → SboxMask4
  termExt : Nat → Fin 12 → SboxMask4

def runToprfRoundsIdx {α : Type} (step : Nat → α → ToprfState12 → ToprfState12) :
    Nat → List α → ToprfState12 → ToprfState12
  | _, [], st => st
  | idx, c :: cs, st => runToprfRoundsIdx step (idx + 1) cs (step idx c st)

private theorem sumToprfState12_runExtRounds (maskFn : Nat → Fin 12 → SboxMask4) :
    ∀ (idx : Nat) (rcs : List Poseidon2State12) (st : ToprfState12),
      sumToprfState12 (runToprfRoundsIdx (fun r rc s => toprfExtRound (maskFn r) rc s) idx rcs st) =
        runRounds externalRound rcs (sumToprfState12 st)
  | _, [], st => by rw [runRounds_nil]; rfl
  | idx, rc :: rcs, st => by
    dsimp only [runToprfRoundsIdx]
    rw [runRounds_cons, ← sumToprfState12_extRound (maskFn idx) rc st]
    exact sumToprfState12_runExtRounds maskFn (idx + 1) rcs _

private theorem sumToprfState12_runIntRounds (maskFn : Nat → SboxMask4) :
    ∀ (idx : Nat) (rcs : List Goldilocks) (st : ToprfState12),
      sumToprfState12 (runToprfRoundsIdx (fun r rc s => toprfIntRound (maskFn r) rc s) idx rcs st) =
        runRounds internalRound rcs (sumToprfState12 st)
  | _, [], st => by rw [runRounds_nil]; rfl
  | idx, rc :: rcs, st => by
    dsimp only [runToprfRoundsIdx]
    rw [runRounds_cons, ← sumToprfState12_intRound (maskFn idx) rc st]
    exact sumToprfState12_runIntRounds maskFn (idx + 1) rcs _

/-- Full 30-round replicated Width-12 `Poseidon2` evaluation (`Engine::permute`, `toprf_engine.rs:314-340`). -/
def toprfEvalPerm12 (masks : ToprfPerm12Masks) (init : ToprfState12) : ToprfState12 :=
  let s0 : ToprfState12 := fun c => applyME (init c)
  let s1 := runToprfRoundsIdx (fun r rc s => toprfExtRound (masks.initExt r) rc s) 0 poseidon2InitialExtConsts s0
  let s2 := runToprfRoundsIdx (fun r rc s => toprfIntRound (masks.internal r) rc s) 0 poseidon2InternalConsts s1
  runToprfRoundsIdx (fun r rc s => toprfExtRound (masks.termExt r) rc s) 0 poseidon2TerminalExtConsts s2

/-- **End-to-End 30-Round Replicated `Poseidon2` Simulation Theorem (`toprfEvalPerm12_sum`)**:
    Across all 4 initial external rounds, 22 internal rounds, and 4 terminal external rounds,
    summing the 5 replicated server components equals `poseidon2Perm12 (sumToprfState12 init)` identically! -/
theorem toprfEvalPerm12_sum (masks : ToprfPerm12Masks) (init : ToprfState12) :
    sumToprfState12 (toprfEvalPerm12 masks init) = poseidon2Perm12 (sumToprfState12 init) := by
  unfold toprfEvalPerm12 poseidon2Perm12
  dsimp only
  rw [sumToprfState12_runExtRounds, sumToprfState12_runIntRounds, sumToprfState12_runExtRounds]
  unfold sumToprfState12
  rw [← applyME_add, ← applyME_add, ← applyME_add, ← applyME_add]

/-- Plaintext Width-12 `Poseidon2` keyed OPRF core `F(k, x)` (`voprf.rs:530-535`):
    rate `b0 = input`, domain/padding `b1 = [1, 0, 0, 0x544f50524631]`, capacity `b2 = key`,
    squeezing the 4-limb (`256`-bit) rate output `b0`. -/
@[expose] def toprfPlaintext (key input : Lane4) : Lane4 :=
  let padLane : Lane4 :=
    ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.ofNat 0x544f50524631⟩
  (poseidon2Perm12 ⟨input, padLane, key⟩).b0

/-- Initialize the 5-component replicated TOPRF state from shared `inputWire` and `keyWire` (`voprf.rs:529-535`). -/
def toprfInitPrfState (keyShares inputShares : Fin 5 → Lane4) : ToprfState12 :=
  let padLane : Lane4 :=
    ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.ofNat 0x544f50524631⟩
  fun c => ⟨inputShares c, if c = 0 then padLane else lane4Zero, keyShares c⟩

def sumLane4Shares5 (sh : Fin 5 → Lane4) : Lane4 :=
  lane4Add (lane4Add (lane4Add (lane4Add (sh 0) (sh 1)) (sh 2)) (sh 3)) (sh 4)

theorem toprfEvalPrf_sum (masks : ToprfPerm12Masks) (keyShares inputShares : Fin 5 → Lane4) :
    (sumToprfState12 (toprfEvalPerm12 masks (toprfInitPrfState keyShares inputShares))).b0 =
      toprfPlaintext (sumLane4Shares5 keyShares) (sumLane4Shares5 inputShares) := by
  rw [toprfEvalPerm12_sum]
  unfold toprfPlaintext
  dsimp only
  have hInit :
      sumToprfState12 (toprfInitPrfState keyShares inputShares) =
        ⟨sumLane4Shares5 inputShares,
         ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.ofNat 0x544f50524631⟩,
         sumLane4Shares5 keyShares⟩ := by
    unfold sumToprfState12 toprfInitPrfState sumLane4Shares5
    have h1 : (1 : Fin 5) ≠ 0 := by decide
    have h2 : (2 : Fin 5) ≠ 0 := by decide
    have h3 : (3 : Fin 5) ≠ 0 := by decide
    have h4 : (4 : Fin 5) ≠ 0 := by decide
    simp only [state12Add_eq, ↓reduceIte, h1, h2, h3, h4, lane4Zero_eq, lane4Add_eq]
    have hAddZ : ∀ x : Goldilocks, Goldilocks.add x Goldilocks.zero = x := LawfulCommRing.add_zero
    simp only [hAddZ]
  rw [hInit]

/-! ### §3.3 1-Byzantine Reshare & Finalize Error-Correction (`toprf_2of5_corrects_one_malicious_server`) -/

/-- 2-of-3 majority decoder on `Option α` where `none` models malformed/omitted erasures (`toprf_engine.rs:183-189`). -/
def majority2Of3 {α : Type} [DecidableEq α] (m0 m1 m2 : Option α) : Option α :=
  match m0, m1, m2 with
  | some v0, some v1, _ => if v0 = v1 then some v0 else
      match m2 with
      | some v2 => if v0 = v2 then some v0 else if v1 = v2 then some v1 else none
      | none => none
  | some v0, none, some v2 => if v0 = v2 then some v0 else none
  | none, some v1, some v2 => if v1 = v2 then some v1 else none
  | _, _, _ => none

theorem majority2Of3_of_two_honest {α : Type} [DecidableEq α] (honest : α)
    (m0 m1 m2 : Option α)
    (hTwo : (m0 = some honest ∧ m1 = some honest) ∨
            (m0 = some honest ∧ m2 = some honest) ∨
            (m1 = some honest ∧ m2 = some honest)) :
    majority2Of3 m0 m1 m2 = some honest := by
  rcases hTwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [majority2Of3]
  · cases m1 with
    | none => simp [majority2Of3]
    | some v1 =>
      unfold majority2Of3
      by_cases hv : honest = v1 <;> simp [hv]
  · cases m0 with
    | none => simp [majority2Of3]
    | some v0 =>
      unfold majority2Of3
      by_cases hv : v0 = honest
      · subst hv; simp
      · simp [hv]

/-- Canonical 8-byte little-endian serialization of a `Goldilocks` vector (`toprf_engine.rs:62-64, 119-122`). -/
def encodeGoldilocksVecLe : List Goldilocks → List UInt8
  | [] => []
  | x :: xs => encodeNatLeBytes 8 x.val ++ encodeGoldilocksVecLe xs

theorem encodeGoldilocksVecLe_length (xs : List Goldilocks) :
    (encodeGoldilocksVecLe xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeGoldilocksVecLe, List.length_append, List.length_cons, encodeNatLeBytes_length, ih]
    omega

theorem encodeGoldilocksVecLe_injective :
    ∀ {xs ys : List Goldilocks},
      encodeGoldilocksVecLe xs = encodeGoldilocksVecLe ys → xs = ys
  | [], [], _ => rfl
  | [], y :: ys, h => by
    have hL := congrArg List.length h
    rw [encodeGoldilocksVecLe_length, encodeGoldilocksVecLe_length] at hL
    simp at hL
  | x :: xs, [], h => by
    have hL := congrArg List.length h
    rw [encodeGoldilocksVecLe_length, encodeGoldilocksVecLe_length] at hL
    simp at hL
  | x :: xs, y :: ys, h => by
    simp only [encodeGoldilocksVecLe] at h
    have hLen8 : (encodeNatLeBytes 8 x.val).length = (encodeNatLeBytes 8 y.val).length := by
      rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
    obtain ⟨hHead, hTail⟩ := append_inj_of_eq_len hLen8 h
    have hxPow : x.val < 256 ^ 8 := Nat.lt_trans x.isLt (by decide)
    have hyPow : y.val < 256 ^ 8 := Nat.lt_trans y.isLt (by decide)
    have hVal : x.val = y.val := by
      have hd := congrArg decodeNatLeBytes hHead
      rwa [decodeNatLeBytes_encodeNatLeBytes 8 x.val hxPow,
           decodeNatLeBytes_encodeNatLeBytes 8 y.val hyPow] at hd
    rw [Goldilocks.ext hVal, encodeGoldilocksVecLe_injective hTail]

/-- Domain tag `"QSAG.TOPRF.RESHARE.DIGEST.V2"` (`toprf_engine.rs:124`, 28 bytes). -/
def toprfReshareDigestTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4F, 0x50, 0x52, 0x46, 0x2E, 0x52, 0x45, 0x53,
   0x48, 0x41, 0x52, 0x45, 0x2E, 0x44, 0x49, 0x47, 0x45, 0x53, 0x54, 0x2E, 0x56, 0x32]

/-- Exact `cshake256_framed_32(b"QSAG.TOPRF.RESHARE.DIGEST.V2", &[context, &layer.to_le_bytes(), &[i, j], &payload])`
    sponge preimage (`toprf_engine.rs:118-127`). -/
def toprfGroupDigestPreimage (ctx : List UInt8) (layer : UInt64) (i j : Fin 5)
    (vals : List Goldilocks) : List UInt8 :=
  cshake256FramedPreimage toprfReshareDigestTag
    [ctx, FixedCodec.u64le.encode layer, [UInt8.ofNat i.val, UInt8.ofNat j.val],
     encodeGoldilocksVecLe vals]

def toprfGroupDigest (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (i j : Fin 5) (vals : List Goldilocks) : List UInt8 :=
  H (toprfGroupDigestPreimage ctx layer i j vals)

/-- Mode A (`gates ≤ 4`, `toprf_engine.rs:183-194`): 3-vector majority decoding over the 3 holders of `(i, j)`. -/
def decodeGroupSmall (m0 m1 m2 : Option (List Goldilocks)) : Option (List Goldilocks) :=
  majority2Of3 m0 m1 m2

/-- Mode B (`gates > 4`, `toprf_engine.rs:195-213`): 2-vector (`m0, m1`) + 1-digest (`md`) decoding!
    Accepts iff `m0 = some v ∧ m1 = some v` OR `md = some d` matches `m0` (checked first) or `m1`. -/
def decodeGroupLarge (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (i j : Fin 5) (m0 m1 : Option (List Goldilocks)) (md : Option (List UInt8)) :
    Option (List Goldilocks) :=
  match m0, m1 with
  | some v0, some v1 =>
    if v0 = v1 then some v0
    else
      match md with
      | some d =>
        if toprfGroupDigest H ctx layer i j v0 = d then some v0
        else if toprfGroupDigest H ctx layer i j v1 = d then some v1
        else none
      | none => none
  | some v0, none =>
    match md with
    | some d => if toprfGroupDigest H ctx layer i j v0 = d then some v0 else none
    | none => none
  | none, some v1 =>
    match md with
    | some d => if toprfGroupDigest H ctx layer i j v1 = d then some v1 else none
    | none => none
  | none, none => none

/-- 3-of-4 client output component majority (`voprf.rs:593-610`): accepts `v` iff `≥ 3` of the 4 component
    holders submit `some v` (`none` models missing/malformed/wrong-context server responses). -/
def majority3Of4 {α : Type} [DecidableEq α] (c0 c1 c2 c3 : Option α) : Option α :=
  let list := [c0, c1, c2, c3]
  let count (v : α) : Nat := (list.filter (fun x => decide (x = some v))).length
  match c0 with
  | some v => if 3 ≤ count v then some v else
      match c1 with
      | some v1 => if 3 ≤ count v1 then some v1 else none
      | none => none
  | none =>
    match c1 with
    | some v1 => if 3 ≤ count v1 then some v1 else none
    | none => none

theorem majority3Of4_of_three_honest {α : Type} [DecidableEq α] (honest : α)
    (c0 c1 c2 c3 : Option α)
    (hThree :
      (c1 = some honest ∧ c2 = some honest ∧ c3 = some honest) ∨
      (c0 = some honest ∧ c2 = some honest ∧ c3 = some honest) ∨
      (c0 = some honest ∧ c1 = some honest ∧ c3 = some honest) ∨
      (c0 = some honest ∧ c1 = some honest ∧ c2 = some honest)) :
    majority3Of4 c0 c1 c2 c3 = some honest := by
  rcases hThree with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · cases c0 with
    | none => simp [majority3Of4]
    | some v0 =>
      unfold majority3Of4
      by_cases hv : v0 = honest
      · subst hv; simp
      · have hne : some honest ≠ some v0 := fun h => hv (Option.some.inj h).symm
        simp [hv, hne]
  · cases c1 with
    | none => simp [majority3Of4]
    | some v1 =>
      unfold majority3Of4
      by_cases hv : v1 = honest <;> simp [hv]
  · cases c2 with
    | none => simp [majority3Of4]
    | some v2 =>
      unfold majority3Of4
      by_cases hv : v2 = honest <;> simp [hv]
  · cases c3 with
    | none => simp [majority3Of4]
    | some v3 =>
      unfold majority3Of4
      by_cases hv : v3 = honest <;> simp [hv]

/-- Client 3-of-4 finalization across all 5 components of a `Lane4` output (`voprf.rs:586-633`). -/
def clientFinalizeLane4 (serverOut : Fin 5 → Option (Fin 5 → Lane4)) : Option Lane4 :=
  let decodeComp (c : Fin 5) : Option Lane4 :=
    match fin5Others c with
    | [p0, p1, p2, p3] =>
      majority3Of4
        ((serverOut p0).map (fun f => f c))
        ((serverOut p1).map (fun f => f c))
        ((serverOut p2).map (fun f => f c))
        ((serverOut p3).map (fun f => f c))
    | _ => none
  match decodeComp 0, decodeComp 1, decodeComp 2, decodeComp 3, decodeComp 4 with
  | some s0, some s1, some s2, some s3, some s4 =>
    some (lane4Add (lane4Add (lane4Add (lane4Add s0 s1) s2) s3) s4)
  | _, _, _, _, _ => none

private theorem fin5_four_others_three_honest (c bad : Fin 5) :
    match fin5Others c with
    | [p0, p1, p2, p3] =>
      (p1 ≠ bad ∧ p2 ≠ bad ∧ p3 ≠ bad) ∨
      (p0 ≠ bad ∧ p2 ≠ bad ∧ p3 ≠ bad) ∨
      (p0 ≠ bad ∧ p1 ≠ bad ∧ p3 ≠ bad) ∨
      (p0 ≠ bad ∧ p1 ≠ bad ∧ p2 ≠ bad)
    | _ => False := by
  have hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
    revert c; decide
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · rw [fin5Others_0]; dsimp only; revert bad; decide
  · rw [fin5Others_1]; dsimp only; revert bad; decide
  · rw [fin5Others_2]; dsimp only; revert bad; decide
  · rw [fin5Others_3]; dsimp only; revert bad; decide
  · rw [fin5Others_4]; dsimp only; revert bad; decide

/-- **Flagship §3.3 Theorem — 1-Byzantine TOPRF Reshare & Finalize Error Correction
    (`toprf_2of5_corrects_one_malicious_server`, `P0-08`–`P0-09`)**:
    Against ANY single malicious/Byzantine server `bad : Fin 5` injecting arbitrary forged values,
    corrupted digests, or missing/truncated erasures (`none`):
    1. **Small-Layer 3-Vector Majority (`gates ≤ 4`, `decodeGroupSmall`):** For any 3 distinct holders
       `(h0, h1, h2)` (`h0 ≠ h1, h0 ≠ h2, h1 ≠ h2`), `decodeGroupSmall` **unconditionally** recovers
       `some honestVec` with zero cryptographic assumptions!
    2. **Large-Layer 2-Vector + 1-Digest (`gates > 4`, `decodeGroupLarge`):** For any 3 distinct holders
       `(hv0, hv1, hd)`, EITHER `decodeGroupLarge` recovers `some honestVec`, OR `bad = hv0` forged a
       distinct `forgedVec ≠ honestVec` exhibiting a length-framed `QSAG.TOPRF.RESHARE.DIGEST.V2` hash collision!
    3. **Client 3-of-4 Finalize (`clientFinalizeLane4`):** Conditional on correct honest engine outputs.
       `toprfActiveClient204_correct` below derives these outputs for the full-value transport. -/
theorem toprf_2of5_corrects_one_malicious_server
    (H : List UInt8 → List UInt8)
    (ctx : List UInt8) (layer : UInt64) (i j : Fin 5)
    (hCtx : ctx.length < 2 ^ 20)
    (bad : Fin 5) :
    -- (1) Small-layer 3-vector majority unconditionally corrects 1 Byzantine server:
    (∀ (h0 h1 h2 : Fin 5) (honestVec : List Goldilocks)
       (m0 m1 m2 : Option (List Goldilocks)),
      h0 ≠ h1 → h0 ≠ h2 → h1 ≠ h2 →
      (h0 ≠ bad → m0 = some honestVec) →
      (h1 ≠ bad → m1 = some honestVec) →
      (h2 ≠ bad → m2 = some honestVec) →
      decodeGroupSmall m0 m1 m2 = some honestVec) ∧
    -- (2) Large-layer 2-vector + 1-digest recovers `some honestVec` OR exhibits an explicit hash collision:
    (∀ (hv0 hv1 hd : Fin 5) (honestVec : List Goldilocks)
       (m0 m1 : Option (List Goldilocks)) (md : Option (List UInt8)),
      hv0 ≠ hv1 → hv0 ≠ hd → hv1 ≠ hd →
      honestVec.length < 2 ^ 20 →
      (∀ v0, m0 = some v0 → v0.length < 2 ^ 20) →
      (hv0 ≠ bad → m0 = some honestVec) →
      (hv1 ≠ bad → m1 = some honestVec) →
      (hd ≠ bad → md = some (toprfGroupDigest H ctx layer i j honestVec)) →
      decodeGroupLarge H ctx layer i j m0 m1 md = some honestVec ∨
        ∃ forgedVec : List Goldilocks,
          m0 = some forgedVec ∧
          forgedVec ≠ honestVec ∧
          toprfGroupDigestPreimage ctx layer i j forgedVec ≠
            toprfGroupDigestPreimage ctx layer i j honestVec ∧
          H (toprfGroupDigestPreimage ctx layer i j forgedVec) =
            H (toprfGroupDigestPreimage ctx layer i j honestVec)) ∧
    -- (3) Client finalization conditional on honest engine outputs:
    (∀ (masks : ToprfPerm12Masks) (keyShares inputShares : Fin 5 → Lane4)
       (serverOut : Fin 5 → Option (Fin 5 → Lane4)),
      (∀ p : Fin 5, p ≠ bad →
        serverOut p = some (fun c => (toprfEvalPerm12 masks (toprfInitPrfState keyShares inputShares) c).b0)) →
      clientFinalizeLane4 serverOut =
        some (toprfPlaintext (sumLane4Shares5 keyShares) (sumLane4Shares5 inputShares))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0 h1 h2 honestVec m0 m1 m2 h01 h02 h12 hm0 hm1 hm2
    unfold decodeGroupSmall
    apply majority2Of3_of_two_honest
    if hb0 : h0 = bad then
      subst hb0
      exact Or.inr (Or.inr ⟨hm1 (Ne.symm h01), hm2 (Ne.symm h02)⟩)
    else if hb1 : h1 = bad then
      subst hb1
      exact Or.inr (Or.inl ⟨hm0 hb0, hm2 (Ne.symm h12)⟩)
    else
      exact Or.inl ⟨hm0 hb0, hm1 hb1⟩
  · intro hv0 hv1 hd honestVec m0 m1 md h01 h0d h1d hLenH hLenM0 hm0 hm1 hmd
    if hb0 : hv0 = bad then
      subst hb0
      have hm1Eq : m1 = some honestVec := hm1 (Ne.symm h01)
      have hmdEq : md = some (toprfGroupDigest H ctx layer i j honestVec) := hmd (Ne.symm h0d)
      rw [hm1Eq, hmdEq]
      cases hm0Case : m0 with
      | none =>
        left
        simp [decodeGroupLarge]
      | some v0 =>
        if hvEq : v0 = honestVec then
          subst hvEq
          left
          simp [decodeGroupLarge]
        else
          if hDigEq : toprfGroupDigest H ctx layer i j v0 = toprfGroupDigest H ctx layer i j honestVec then
            right
            refine ⟨v0, rfl, hvEq, ?_, hDigEq⟩
            intro hPreEq
            unfold toprfGroupDigestPreimage at hPreEq
            have hV0Lt : v0.length < 2 ^ 20 := hLenM0 v0 hm0Case
            have hAll1 : ∀ x ∈ [ctx, FixedCodec.u64le.encode layer, [UInt8.ofNat i.val, UInt8.ofNat j.val],
                                encodeGoldilocksVecLe v0], x.length < 256 ^ 8 := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx1
              · omega
              · rcases List.mem_cons.mp hx1 with rfl | hx2
                · rw [FixedCodec.u64le.encode_len]; decide
                · rcases List.mem_cons.mp hx2 with rfl | hx3
                  · dsimp only [List.length_cons, List.length_nil]; decide
                  · rcases List.mem_cons.mp hx3 with rfl | hx4
                    · rw [encodeGoldilocksVecLe_length]; omega
                    · cases hx4
            have hAll2 : ∀ y ∈ [ctx, FixedCodec.u64le.encode layer, [UInt8.ofNat i.val, UInt8.ofNat j.val],
                                encodeGoldilocksVecLe honestVec], y.length < 256 ^ 8 := by
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy1
              · omega
              · rcases List.mem_cons.mp hy1 with rfl | hy2
                · rw [FixedCodec.u64le.encode_len]; decide
                · rcases List.mem_cons.mp hy2 with rfl | hy3
                  · dsimp only [List.length_cons, List.length_nil]; decide
                  · rcases List.mem_cons.mp hy3 with rfl | hy4
                    · rw [encodeGoldilocksVecLe_length]; omega
                    · cases hy4
            have hListEq := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hPreEq
            injection hListEq with _ t1
            injection t1 with _ t2
            injection t2 with _ t3
            injection t3 with hVecBytes _
            exact hvEq (encodeGoldilocksVecLe_injective hVecBytes)
          else
            left
            simp [decodeGroupLarge, hvEq, hDigEq]
    else if hb1 : hv1 = bad then
      subst hb1
      left
      have hm0Eq : m0 = some honestVec := hm0 hb0
      have hmdEq : md = some (toprfGroupDigest H ctx layer i j honestVec) := hmd (Ne.symm h1d)
      rw [hm0Eq, hmdEq]
      cases m1 with
      | none => simp [decodeGroupLarge]
      | some v1 =>
        unfold decodeGroupLarge
        by_cases hv : honestVec = v1 <;> simp [hv]
    else
      left
      rw [hm0 hb0, hm1 hb1]
      simp [decodeGroupLarge]
  · intro masks keyShares inputShares serverOut hHonestOut
    let evalSt := toprfEvalPerm12 masks (toprfInitPrfState keyShares inputShares)
    have hComp : ∀ c : Fin 5,
        (match fin5Others c with
         | [p0, p1, p2, p3] =>
           majority3Of4
             ((serverOut p0).map (fun f => f c))
             ((serverOut p1).map (fun f => f c))
             ((serverOut p2).map (fun f => f c))
             ((serverOut p3).map (fun f => f c))
         | _ => none) = some (evalSt c).b0 := by
      intro c
      have h3 := fin5_four_others_three_honest c bad
      cases hOthers : fin5Others c with
      | nil => rw [hOthers] at h3; exact False.elim h3
      | cons p0 r0 =>
        cases r0 with
        | nil => rw [hOthers] at h3; exact False.elim h3
        | cons p1 r1 =>
          cases r1 with
          | nil => rw [hOthers] at h3; exact False.elim h3
          | cons p2 r2 =>
            cases r2 with
            | nil => rw [hOthers] at h3; exact False.elim h3
            | cons p3 r3 =>
              cases r3 with
              | cons _ _ => rw [hOthers] at h3; exact False.elim h3
              | nil =>
                rw [hOthers] at h3
                apply majority3Of4_of_three_honest
                rcases h3 with ⟨n1, n2, n3⟩ | ⟨n0, n2, n3⟩ | ⟨n0, n1, n3⟩ | ⟨n0, n1, n2⟩
                · exact Or.inl ⟨by rw [hHonestOut p1 n1]; rfl,
                                by rw [hHonestOut p2 n2]; rfl,
                                by rw [hHonestOut p3 n3]; rfl⟩
                · exact Or.inr (Or.inl ⟨by rw [hHonestOut p0 n0]; rfl,
                                        by rw [hHonestOut p2 n2]; rfl,
                                        by rw [hHonestOut p3 n3]; rfl⟩)
                · exact Or.inr (Or.inr (Or.inl ⟨by rw [hHonestOut p0 n0]; rfl,
                                                by rw [hHonestOut p1 n1]; rfl,
                                                by rw [hHonestOut p3 n3]; rfl⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨by rw [hHonestOut p0 n0]; rfl,
                                                by rw [hHonestOut p1 n1]; rfl,
                                                by rw [hHonestOut p2 n2]; rfl⟩))
    unfold clientFinalizeLane4
    dsimp only
    rw [hComp 0, hComp 1, hComp 2, hComp 3, hComp 4]
    dsimp only
    apply congrArg some
    have hPrf := toprfEvalPrf_sum masks keyShares inputShares
    rw [sumToprfState12_lanes] at hPrf
    dsimp only at hPrf
    simp only [lane4Add_eq, sumWire5] at hPrf ⊢
    exact hPrf

/-- **`#tooth` (`tooth_toprf_two_corrupt_servers_can_forge_majority`)**:
    When 2 servers (`bad1 = 1, bad2 = 2`) collude among the 3 cross-term holders `toprfHolders 0 4 = [1, 2, 3]`
    (violating the $t' = 1$ Byzantine corruption bound of 2-of-5 TOPRF), BOTH `decodeGroupSmall` AND
    `decodeGroupLarge` (even under an injective identity hash `H = id`!) silently accept `forgedVec ≠ honestVec`! -/
theorem tooth_toprf_two_corrupt_servers_can_forge_majority :
    let honestVec : List Goldilocks := [Goldilocks.zero]
    let forgedVec : List Goldilocks := [Goldilocks.one]
    toprfHolders 0 4 = [1, 2, 3] ∧
    forgedVec ≠ honestVec ∧
    decodeGroupSmall (some forgedVec) (some forgedVec) (some honestVec) = some forgedVec ∧
    decodeGroupLarge id [0x07] 0 0 4 (some forgedVec) (some forgedVec)
      (some (toprfGroupDigest id [0x07] 0 0 4 honestVec)) = some forgedVec := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro h
    injection h with h10
    have hv := congrArg Goldilocks.val h10
    simp at hv
  · simp [decodeGroupSmall, majority2Of3]
  · simp [decodeGroupLarge]

/-- Non-vacuous inhabitedness witness for 2-of-5 TOPRF correcting an omitted/corrupt server response. -/
theorem toprf_2of5_inhabited :
    ∃ (masks : ToprfPerm12Masks) (keyShares inputShares : Fin 5 → Lane4)
      (serverOut : Fin 5 → Option (Fin 5 → Lane4)),
      serverOut 0 = none ∧
      (∀ p : Fin 5, p ≠ 0 →
        serverOut p = some (fun c => (toprfEvalPerm12 masks (toprfInitPrfState keyShares inputShares) c).b0)) ∧
      clientFinalizeLane4 serverOut =
        some (toprfPlaintext (sumLane4Shares5 keyShares) (sumLane4Shares5 inputShares)) := by
  let zMask : SboxMask4 := {
    m1 := fun _ _ => Goldilocks.zero
    m2 := fun _ _ => Goldilocks.zero
    m3 := fun _ _ => Goldilocks.zero
    m4 := fun _ _ => Goldilocks.zero
  }
  let masks : ToprfPerm12Masks := {
    initExt := fun _ _ => zMask
    internal := fun _ => zMask
    termExt := fun _ _ => zMask
  }
  let kSh : Fin 5 → Lane4 := fun _ => lane4Zero
  let iSh : Fin 5 → Lane4 := fun _ => lane4Zero
  let evalSt := toprfEvalPerm12 masks (toprfInitPrfState kSh iSh)
  let serverOut : Fin 5 → Option (Fin 5 → Lane4) :=
    fun p => if p = 0 then none else some (fun c => (evalSt c).b0)
  have hHon : ∀ p : Fin 5, p ≠ 0 →
      serverOut p = some (fun c => (toprfEvalPerm12 masks (toprfInitPrfState kSh iSh) c).b0) :=
    fun p hp => by simp [serverOut, evalSt, hp]
  refine ⟨masks, kSh, iSh, serverOut, rfl, hHon, ?_⟩
  exact (toprf_2of5_corrects_one_malicious_server id [] 0 0 1 (by decide) 0).2.2 masks kSh iSh serverOut hHon

/-! ### §3.4 1-Curious-Server Privacy (`toprf_one_curious_server_hiding`) & Input-Root Binding -/

abbrev GoldQuad := Goldilocks × Goldilocks × Goldilocks × Goldilocks

/-- Client 5-component share encoding of `val` from 4 uniform coins `r = (r0, r1, r2, r3)` (`voprf.rs:423-426`). -/
def clientShareWire (val : Goldilocks) (r : GoldQuad) : ToprfWire
  | 0 => r.1
  | 1 => r.2.1
  | 2 => r.2.2.1
  | 3 => r.2.2.2
  | 4 => Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val r.1) r.2.1) r.2.2.1) r.2.2.2

/-- The 4 shares `(w c)_{c ≠ p}` delivered to server `p` (`voprf.rs:427-433`: component `p` is zeroed/omitted!). -/
def clientViewAtServer (p : Fin 5) (w : ToprfWire) : GoldQuad :=
  match p with
  | ⟨0, _⟩ => (w 1, w 2, w 3, w 4)
  | ⟨1, _⟩ => (w 0, w 2, w 3, w 4)
  | ⟨2, _⟩ => (w 0, w 1, w 3, w 4)
  | ⟨3, _⟩ => (w 0, w 1, w 2, w 4)
  | ⟨4, _⟩ => (w 0, w 1, w 2, w 3)

/-- Explicit inverse recovering the 4 client sharing coins `r` from server `p`'s observed 4-share view `v`. -/
def clientCoinsFromServerView (p : Fin 5) (val : Goldilocks) (v : GoldQuad) : GoldQuad :=
  let missing := Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val v.1) v.2.1) v.2.2.1) v.2.2.2
  match p with
  | ⟨0, _⟩ => (missing, v.1, v.2.1, v.2.2.1)
  | ⟨1, _⟩ => (v.1, missing, v.2.1, v.2.2.1)
  | ⟨2, _⟩ => (v.1, v.2.1, missing, v.2.2.1)
  | ⟨3, _⟩ => (v.1, v.2.1, v.2.2.1, missing)
  | ⟨4, _⟩ => v

/-- Per-gate incoming view `(t_0 - r_0, t_1 - r_1, t_2 - r_2, t_3 - r_3)` received by server `p` (`toprf_engine.rs:17-20`). -/
def serverGateMaskedView (terms masks : GoldQuad) : GoldQuad :=
  (Goldilocks.sub terms.1 masks.1,
   Goldilocks.sub terms.2.1 masks.2.1,
   Goldilocks.sub terms.2.2.1 masks.2.2.1,
   Goldilocks.sub terms.2.2.2 masks.2.2.2)

private theorem gold_sub_sub_self (t r : Goldilocks) :
    Goldilocks.sub t (Goldilocks.sub t r) = r := by
  rw [← goldOfInt_nat t, ← goldOfInt_nat r]
  simp only [goldOfInt_sub]
  congr 1; omega

/-- **Flagship §3.4a Theorem — 1-Curious-Server Input & Gate-View Hiding (`toprf_one_curious_server_hiding`)**:
    For EVERY single curious server `p : Fin 5`:
    1. `sumWire5 (clientShareWire val r) = val` for all `val` and coins `r`;
    2. There is an explicit `SimpleEquiv GoldQuad GoldQuad` between uniform client coins `r` and server `p`'s
       observed 4-component share view `clientViewAtServer p (clientShareWire val r)` — hence for ANY two
       client inputs `valA, valB : Goldilocks`, composing `(equiv p valB)⁻¹ ∘ (equiv p valA)` gives a
       constructive coin bijection producing **identical** views at server `p`!
    3. Per multiplication gate, `serverGateMaskedView terms` is a self-inverse `SimpleEquiv GoldQuad GoldQuad`
       mapping the 4 masks derived from `seed(p, p)` (the unique seed missing from server `p`!) onto server `p`'s
       4 incoming cross-term messages! -/
theorem toprf_one_curious_server_hiding :
    (∀ (val : Goldilocks) (r : GoldQuad), sumWire5 (clientShareWire val r) = val) ∧
    (∀ (p : Fin 5) (val : Goldilocks),
      ∃ eqv : SimpleEquiv GoldQuad GoldQuad,
        (∀ r : GoldQuad, eqv.toFun r = clientViewAtServer p (clientShareWire val r))) ∧
    (∀ (terms : GoldQuad),
      ∃ eqv : SimpleEquiv GoldQuad GoldQuad,
        (∀ masks : GoldQuad, eqv.toFun masks = serverGateMaskedView terms masks) ∧
        (∀ view : GoldQuad, eqv.invFun view = serverGateMaskedView terms view)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro val ⟨r0, r1, r2, r3⟩
    unfold sumWire5 clientShareWire
    dsimp only
    rw [← goldOfInt_nat val, ← goldOfInt_nat r0, ← goldOfInt_nat r1,
        ← goldOfInt_nat r2, ← goldOfInt_nat r3]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1; omega
  · intro p val
    have hSub4_0 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val b) c) d)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d) = a := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hSub4_1 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) c) d)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d) = b := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hSub4_2 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) d)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d) = c := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hSub4_3 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d) = d := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hRInv_0 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d)) a) b) c = d := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hRInv_1 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d)) b) c = d := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    have hRInv_2 : ∀ a b c d : Goldilocks,
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b)
          (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val a) b) c) d)) c = d := by
      intro a b c d
      rw [← goldOfInt_nat val, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
      simp only [goldOfInt_sub]; congr 1; omega
    refine ⟨{
      toFun := fun r => clientViewAtServer p (clientShareWire val r)
      invFun := clientCoinsFromServerView p val
      left_inv := ?_
      right_inv := ?_
    }, fun _ => rfl⟩
    · intro ⟨r0, r1, r2, r3⟩
      rcases p with ⟨pv, hpv⟩
      have hCases : pv = 0 ∨ pv = 1 ∨ pv = 2 ∨ pv = 3 ∨ pv = 4 := by omega
      rcases hCases with rfl | rfl | rfl | rfl | rfl
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_0]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_1]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_2]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_3]
      · rfl
    · intro ⟨v0, v1, v2, v3⟩
      rcases p with ⟨pv, hpv⟩
      have hCases : pv = 0 ∨ pv = 1 ∨ pv = 2 ∨ pv = 3 ∨ pv = 4 := by omega
      rcases hCases with rfl | rfl | rfl | rfl | rfl
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hRInv_0]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hRInv_1]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hRInv_2]
      · dsimp only [clientViewAtServer, clientCoinsFromServerView, clientShareWire]; rw [hSub4_3]
      · rfl
  · intro terms
    refine ⟨{
      toFun := serverGateMaskedView terms
      invFun := serverGateMaskedView terms
      left_inv := fun ⟨m0, m1, m2, m3⟩ => by
        unfold serverGateMaskedView
        dsimp only
        rw [gold_sub_sub_self, gold_sub_sub_self, gold_sub_sub_self, gold_sub_sub_self]
      right_inv := fun ⟨v0, v1, v2, v3⟩ => by
        unfold serverGateMaskedView
        dsimp only
        rw [gold_sub_sub_self, gold_sub_sub_self, gold_sub_sub_self, gold_sub_sub_self]
    }, fun _ => rfl, fun _ => rfl⟩

/-- TOPRF evaluation session context matching `voprf::Context` (`voprf.rs:360-386`). -/
structure ToprfEvalContext where
  key : List UInt8
  session : List UInt8
  counter : UInt64
  items : UInt64
  deriving DecidableEq, Repr

/-- Domain tag `"QSAG.TOPRF.EVAL.V1"` (`voprf.rs:378`, 18 bytes). -/
def toprfEvalContextTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4F, 0x50, 0x52,
   0x46, 0x2E, 0x45, 0x56, 0x41, 0x4C, 0x2E, 0x56, 0x31]

/-- Exact `Context::base_digest()` sponge preimage (`voprf.rs:376-386`):
    `cshake256_framed_32(b"QSAG.TOPRF.EVAL.V1", &[&key, &session, &counter.to_le_bytes(), &items.to_le_bytes()])`. -/
def toprfContextBasePreimage (ctx : ToprfEvalContext) : List UInt8 :=
  cshake256FramedPreimage toprfEvalContextTag
    [ctx.key, ctx.session, FixedCodec.u64le.encode ctx.counter, FixedCodec.u64le.encode ctx.items]

def toprfContextBaseDigest (H : List UInt8 → List UInt8) (ctx : ToprfEvalContext) : List UInt8 :=
  H (toprfContextBasePreimage ctx)

theorem toprfContextBasePreimage_injective {ctx₁ ctx₂ : ToprfEvalContext}
    (hk₁ : ctx₁.key.length < 256 ^ 8) (hs₁ : ctx₁.session.length < 256 ^ 8)
    (hk₂ : ctx₂.key.length < 256 ^ 8) (hs₂ : ctx₂.session.length < 256 ^ 8)
    (hEq : toprfContextBasePreimage ctx₁ = toprfContextBasePreimage ctx₂) :
    ctx₁ = ctx₂ := by
  unfold toprfContextBasePreimage at hEq
  have hAll₁ : ∀ f ∈ [ctx₁.key, ctx₁.session, FixedCodec.u64le.encode ctx₁.counter,
                      FixedCodec.u64le.encode ctx₁.items], f.length < 256 ^ 8 := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | h1
    · exact hk₁
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hs₁
      · rcases List.mem_cons.mp h2 with rfl | h3
        · rw [FixedCodec.u64le.encode_len]; decide
        · rcases List.mem_cons.mp h3 with rfl | h4
          · rw [FixedCodec.u64le.encode_len]; decide
          · cases h4
  have hAll₂ : ∀ g ∈ [ctx₂.key, ctx₂.session, FixedCodec.u64le.encode ctx₂.counter,
                      FixedCodec.u64le.encode ctx₂.items], g.length < 256 ^ 8 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | h1
    · exact hk₂
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hs₂
      · rcases List.mem_cons.mp h2 with rfl | h3
        · rw [FixedCodec.u64le.encode_len]; decide
        · rcases List.mem_cons.mp h3 with rfl | h4
          · rw [FixedCodec.u64le.encode_len]; decide
          · cases h4
  have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll₁ hAll₂ hEq
  injection hFr with eKey t1
  injection t1 with eSes t2
  injection t2 with eCnt t3
  injection t3 with eItm _
  have hCnt : ctx₁.counter = ctx₂.counter := FixedCodec.u64le.encode_injective eCnt
  have hItm : ctx₁.items = ctx₂.items := FixedCodec.u64le.encode_injective eItm
  rcases ctx₁ with ⟨k1, s1, c1, i1⟩
  rcases ctx₂ with ⟨k2, s2, c2, i2⟩
  dsimp only at eKey eSes hCnt hItm
  subst eKey eSes hCnt hItm
  rfl

/-- Domain tag `"QSAG.TOPRF.INPUT.COMMIT.V1"` (`voprf.rs:403`, 26 bytes). -/
def toprfInputCommitTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4F, 0x50, 0x52, 0x46, 0x2E, 0x49, 0x4E,
   0x50, 0x55, 0x54, 0x2E, 0x43, 0x4F, 0x4D, 0x4D, 0x49, 0x54, 0x2E, 0x56, 0x31]

/-- Domain tag `"QSAG.TOPRF.INPUT.BIND.V1"` (`voprf.rs:482, 575`, 24 bytes). -/
def toprfInputBindTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4F, 0x50, 0x52, 0x46, 0x2E, 0x49,
   0x4E, 0x50, 0x55, 0x54, 0x2E, 0x42, 0x49, 0x4E, 0x44, 0x2E, 0x56, 0x31]

/-- Exact `input_commitment(request, component)` sponge preimage (`voprf.rs:395-411`):
    absorbs `[&request.context.base_digest(), &[component as u8], &request.salts[component], &payload]`. -/
def toprfInputCommitPreimage (baseDigest : List UInt8) (c : Fin 5)
    (salt : List UInt8) (shares : List Goldilocks) : List UInt8 :=
  cshake256FramedPreimage toprfInputCommitTag
    [baseDigest, [UInt8.ofNat c.val], salt, encodeGoldilocksVecLe shares]

def toprfInputCommit (H : List UInt8 → List UInt8) (baseDigest : List UInt8) (c : Fin 5)
    (salt : List UInt8) (shares : List Goldilocks) : List UInt8 :=
  H (toprfInputCommitPreimage baseDigest c salt shares)

/-- **`#tooth` (`tooth_omitting_base_digest_allows_cross_session_replay`)**:
    A broken input commitment omitting `context.base_digest()` produces **byte-identical** commitments
    across distinct sessions/counters `ctx₁ ≠ ctx₂` (`rfl`), whereas `toprfContextBasePreimage` strictly
    separates `ctx₁` and `ctx₂` and `toprfInputCommitPreimage` strictly separates any two distinct
    `< 256^8`-byte base digests (including 32-byte `cshake256Bytes` digests)! -/
theorem tooth_omitting_base_digest_allows_cross_session_replay :
    let brokenPreimage (c : Fin 5) (salt : List UInt8) (shares : List Goldilocks) : List UInt8 :=
      cshake256FramedPreimage toprfInputCommitTag [[UInt8.ofNat c.val], salt, encodeGoldilocksVecLe shares]
    let ctx₁ : ToprfEvalContext := { key := [0x11], session := [0xA1], counter := 0, items := 1 }
    let ctx₂ : ToprfEvalContext := { key := [0x11], session := [0xB2], counter := 1, items := 1 }
    let H₀ : List UInt8 → List UInt8 := fun bs =>
      if bs = toprfContextBasePreimage ctx₁ then [0x01] else [0x02]
    ctx₁ ≠ ctx₂ ∧
    toprfContextBasePreimage ctx₁ ≠ toprfContextBasePreimage ctx₂ ∧
    brokenPreimage 0 [0x55] [Goldilocks.one] = brokenPreimage 0 [0x55] [Goldilocks.one] ∧
    toprfInputCommit id (toprfContextBaseDigest H₀ ctx₁) 0 [0x55] [Goldilocks.one] ≠
      toprfInputCommit id (toprfContextBaseDigest H₀ ctx₂) 0 [0x55] [Goldilocks.one] := by
  have hPreNe :
      toprfContextBasePreimage { key := [0x11], session := [0xA1], counter := 0, items := 1 } ≠
        toprfContextBasePreimage { key := [0x11], session := [0xB2], counter := 1, items := 1 } := by
    intro hBaseEq
    have hCtxEq := toprfContextBasePreimage_injective (by simp) (by simp) (by simp) (by simp) hBaseEq
    injection hCtxEq with _ eSes _ _
    cases eSes
  refine ⟨by decide, hPreNe, rfl, ?_⟩
  intro hEq
  dsimp only [toprfInputCommit, toprfContextBaseDigest, id] at hEq
  rw [ite_true_of rfl, ite_false_of (Ne.symm hPreNe)] at hEq
  have hEncLen : (encodeGoldilocksVecLe [Goldilocks.one]).length < 256 ^ 8 := by
    rw [encodeGoldilocksVecLe_length]; decide
  have hAll1 : ∀ f ∈ [([0x01] : List UInt8), [UInt8.ofNat (0 : Fin 5).val], ([0x55] : List UInt8),
                      encodeGoldilocksVecLe [Goldilocks.one]], f.length < 256 ^ 8 := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | t1
    · decide
    · rcases List.mem_cons.mp t1 with rfl | t2
      · decide
      · rcases List.mem_cons.mp t2 with rfl | t3
        · decide
        · rcases List.mem_cons.mp t3 with rfl | t4
          · exact hEncLen
          · cases t4
  have hAll2 : ∀ g ∈ [([0x02] : List UInt8), [UInt8.ofNat (0 : Fin 5).val], ([0x55] : List UInt8),
                      encodeGoldilocksVecLe [Goldilocks.one]], g.length < 256 ^ 8 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | t1
    · decide
    · rcases List.mem_cons.mp t1 with rfl | t2
      · decide
      · rcases List.mem_cons.mp t2 with rfl | t3
        · decide
        · rcases List.mem_cons.mp t3 with rfl | t4
          · exact hEncLen
          · cases t4
  have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hEq
  injection hFr with eBase _
  cases eBase

/-- 4-holder unanimity check on component `c` (`voprf.rs:511-525`): all 4 servers `p ≠ c` must broadcast
    the identical 32-byte commitment digest `expected`! -/
def checkComponentUnanimity (c : Fin 5) (broadcastDigests : Fin 5 → List UInt8) : Bool :=
  match fin5Others c with
  | [p0, p1, p2, p3] =>
    decide (broadcastDigests p0 = broadcastDigests p1) &&
    decide (broadcastDigests p0 = broadcastDigests p2) &&
    decide (broadcastDigests p0 = broadcastDigests p3)
  | _ => false

/-- Exact `cshake256_framed_32(b"QSAG.TOPRF.INPUT.BIND.V1", &[input])` sponge preimage (`voprf.rs:482, 575`). -/
def toprfInputBindPreimage (input : List UInt8) : List UInt8 :=
  cshake256FramedPreimage toprfInputBindTag [input]

/-- Client `Evaluation::value_for` (`voprf.rs:571-580`): verifies `evalKey = expectedKey` and looks up
    `H (toprfInputBindPreimage queriedInput)` inside the enrolled `inputDigests`. -/
def toprfValueFor (H : List UInt8 → List UInt8)
    (expectedKey evalKey : List UInt8)
    (enrolledInputs : List (List UInt8))
    (values : List (List UInt8))
    (queriedInput : List UInt8) : Option (List UInt8) :=
  if evalKey = expectedKey then
    let target := H (toprfInputBindPreimage queriedInput)
    let rec findIdx : List (List UInt8) → List (List UInt8) → Option (List UInt8)
      | d :: ds, v :: vsl => if d = target then some v else findIdx ds vsl
      | _, _ => none
    findIdx (enrolledInputs.map (fun x => H (toprfInputBindPreimage x))) values
  else
    none

private theorem checkComponentUnanimity_eq_of_mem {c p q : Fin 5}
    {digests : Fin 5 → List UInt8}
    (hUnan : checkComponentUnanimity c digests = true)
    (hp : p ≠ c) (hq : q ≠ c) :
    digests p = digests q := by
  have hPair :
      ∀ (c p q : Fin 5), p ≠ c → q ≠ c →
        match fin5Others c with
        | [p0, p1, p2, p3] =>
          (p = p0 ∨ p = p1 ∨ p = p2 ∨ p = p3) ∧
          (q = p0 ∨ q = p1 ∨ q = p2 ∨ q = p3)
        | _ => False := by
    intro c0
    have hc : c0 = 0 ∨ c0 = 1 ∨ c0 = 2 ∨ c0 = 3 ∨ c0 = 4 := by
      revert c0; decide
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · rw [fin5Others_0]; dsimp only; decide
    · rw [fin5Others_1]; dsimp only; decide
    · rw [fin5Others_2]; dsimp only; decide
    · rw [fin5Others_3]; dsimp only; decide
    · rw [fin5Others_4]; dsimp only; decide
  have hpq := hPair c p q hp hq
  unfold checkComponentUnanimity at hUnan
  cases hOthers : fin5Others c with
  | nil => rw [hOthers] at hpq; exact False.elim hpq
  | cons p0 r0 =>
    cases r0 with
    | nil => rw [hOthers] at hpq; exact False.elim hpq
    | cons p1 r1 =>
      cases r1 with
      | nil => rw [hOthers] at hpq; exact False.elim hpq
      | cons p2 r2 =>
        cases r2 with
        | nil => rw [hOthers] at hpq; exact False.elim hpq
        | cons p3 r3 =>
          cases r3 with
          | cons _ _ => rw [hOthers] at hpq; exact False.elim hpq
          | nil =>
            rw [hOthers] at hUnan hpq
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hUnan
            rcases hUnan with ⟨⟨e01, e02⟩, e03⟩
            rcases hpq with ⟨hpCases, hqCases⟩
            have hpEq0 : digests p = digests p0 := by
              rcases hpCases with rfl | rfl | rfl | rfl
              · rfl
              · exact e01.symm
              · exact e02.symm
              · exact e03.symm
            have hqEq0 : digests q = digests p0 := by
              rcases hqCases with rfl | rfl | rfl | rfl
              · rfl
              · exact e01.symm
              · exact e02.symm
              · exact e03.symm
            exact hpEq0.trans hqEq0.symm

/-- **Flagship §3.4b Theorem — Context-Bound Salted Input-Root Equivocation & Relabeling Security
    (`toprf_input_root_blocks_relabeling_and_equivocation`, `voprf.rs:376-411, 501-580`, fixing `C0-2`)**:
    1. **4-Holder Unanimity + `context.base_digest()` Binding**: Whenever a malicious client delivers
       distinct `(ctx₁, salt₁, sh₁) ≠ (ctx₂, salt₂, sh₂)` for component `c` to ANY two honest holders
       `h₁, h₂ ≠ c`, `checkComponentUnanimity` rejects (`= false`) unless `H` collides on length-framed
       `"QSAG.TOPRF.EVAL.V1"` (`toprfContextBasePreimage`) or `"QSAG.TOPRF.INPUT.COMMIT.V1"`
       (`toprfInputCommitPreimage`)!
    2. **`#tooth` (Majority vs Unanimity)**: A 3-of-4 majority check allows 1 corrupt server + 2 honest
       servers holding `dA` to outvote honest server `4` holding `dB ≠ dA`!
    3. **Input-Binding Blocks Cross-Input Output Relabeling**: Querying `toprfValueFor` on any `queried ∉ enrolled`
       returns `none` unless `H` collides on length-framed `"QSAG.TOPRF.INPUT.BIND.V1"`! -/
theorem toprf_input_root_blocks_relabeling_and_equivocation
    (H : List UInt8 → List UInt8) :
    (∀ (c h₁ h₂ : Fin 5) (ctx₁ ctx₂ : ToprfEvalContext)
       (salt₁ salt₂ : List UInt8) (sh₁ sh₂ : List Goldilocks)
       (digests : Fin 5 → List UInt8),
      h₁ ≠ c → h₂ ≠ c →
      ctx₁.key.length < 256 ^ 8 → ctx₁.session.length < 256 ^ 8 →
      ctx₂.key.length < 256 ^ 8 → ctx₂.session.length < 256 ^ 8 →
      (toprfContextBaseDigest H ctx₁).length < 256 ^ 8 →
      (toprfContextBaseDigest H ctx₂).length < 256 ^ 8 →
      salt₁.length < 256 ^ 8 → salt₂.length < 256 ^ 8 →
      sh₁.length < 2 ^ 56 → sh₂.length < 2 ^ 56 →
      (ctx₁, salt₁, sh₁) ≠ (ctx₂, salt₂, sh₂) →
      digests h₁ = toprfInputCommit H (toprfContextBaseDigest H ctx₁) c salt₁ sh₁ →
      digests h₂ = toprfInputCommit H (toprfContextBaseDigest H ctx₂) c salt₂ sh₂ →
      checkComponentUnanimity c digests = false ∨
        (toprfContextBasePreimage ctx₁ ≠ toprfContextBasePreimage ctx₂ ∧
         H (toprfContextBasePreimage ctx₁) = H (toprfContextBasePreimage ctx₂)) ∨
        (toprfInputCommitPreimage (toprfContextBaseDigest H ctx₁) c salt₁ sh₁ ≠
           toprfInputCommitPreimage (toprfContextBaseDigest H ctx₂) c salt₂ sh₂ ∧
         H (toprfInputCommitPreimage (toprfContextBaseDigest H ctx₁) c salt₁ sh₁) =
           H (toprfInputCommitPreimage (toprfContextBaseDigest H ctx₂) c salt₂ sh₂))) ∧
    (majority3Of4 (some ([0x01] : List UInt8)) (some [0x01]) (some [0x01]) (some [0x02]) = some [0x01] ∧
     checkComponentUnanimity 0 (fun p => if p = 4 then [0x02] else [0x01]) = false) ∧
    (∀ (expectedKey evalKey queried : List UInt8) (enrolled values : List (List UInt8)),
      queried.length < 256 ^ 8 →
      (∀ x ∈ enrolled, x.length < 256 ^ 8) →
      queried ∉ enrolled →
      toprfValueFor H expectedKey evalKey enrolled values queried = none ∨
        ∃ x ∈ enrolled,
          toprfInputBindPreimage x ≠ toprfInputBindPreimage queried ∧
          H (toprfInputBindPreimage x) = H (toprfInputBindPreimage queried)) := by
  refine ⟨?_, ⟨by decide, by decide⟩, ?_⟩
  · intro c h₁ h₂ ctx₁ ctx₂ salt₁ salt₂ sh₁ sh₂ digests hh1 hh2 hk1 hs1 hk2 hs2 hbd1 hbd2 hslt1 hslt2 hsh1 hsh2 hNe hd1 hd2
    cases hUnan : checkComponentUnanimity c digests with
    | false => exact Or.inl rfl
    | true =>
      have hDigEq := checkComponentUnanimity_eq_of_mem hUnan hh1 hh2
      rw [hd1, hd2] at hDigEq
      let bd₁ := toprfContextBaseDigest H ctx₁
      let bd₂ := toprfContextBaseDigest H ctx₂
      if hPreEq : toprfInputCommitPreimage bd₁ c salt₁ sh₁ = toprfInputCommitPreimage bd₂ c salt₂ sh₂ then
        have hAll1 : ∀ f ∈ [bd₁, [UInt8.ofNat c.val], salt₁, encodeGoldilocksVecLe sh₁], f.length < 256 ^ 8 := by
          intro f hf
          rcases List.mem_cons.mp hf with rfl | t1
          · exact hbd1
          · rcases List.mem_cons.mp t1 with rfl | t2
            · dsimp only [List.length_cons, List.length_nil]; decide
            · rcases List.mem_cons.mp t2 with rfl | t3
              · exact hslt1
              · rcases List.mem_cons.mp t3 with rfl | t4
                · rw [encodeGoldilocksVecLe_length]; omega
                · cases t4
        have hAll2 : ∀ g ∈ [bd₂, [UInt8.ofNat c.val], salt₂, encodeGoldilocksVecLe sh₂], g.length < 256 ^ 8 := by
          intro g hg
          rcases List.mem_cons.mp hg with rfl | t1
          · exact hbd2
          · rcases List.mem_cons.mp t1 with rfl | t2
            · dsimp only [List.length_cons, List.length_nil]; decide
            · rcases List.mem_cons.mp t2 with rfl | t3
              · exact hslt2
              · rcases List.mem_cons.mp t3 with rfl | t4
                · rw [encodeGoldilocksVecLe_length]; omega
                · cases t4
        have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hPreEq
        injection hFr with eBd t1
        injection t1 with _ t2
        injection t2 with eSalt t3
        injection t3 with eShBytes _
        have eSh := encodeGoldilocksVecLe_injective eShBytes
        if hCtxEq : ctx₁ = ctx₂ then
          exfalso
          exact hNe (by rw [hCtxEq, eSalt, eSh])
        else
          right; left
          refine ⟨fun hBasePreEq => hCtxEq (toprfContextBasePreimage_injective hk1 hs1 hk2 hs2 hBasePreEq), eBd⟩
      else
        exact Or.inr (Or.inr ⟨hPreEq, hDigEq⟩)
  · intro expectedKey evalKey queried enrolled values hQLen hEnrLen hNotMem
    unfold toprfValueFor
    if hKey : evalKey = expectedKey then
      rw [ite_true_of hKey]
      dsimp only
      induction enrolled generalizing values with
      | nil =>
        left
        cases values <;> rfl
      | cons x xs ih =>
        cases values with
        | nil => left; rfl
        | cons v vsl =>
          dsimp only [List.map, toprfValueFor.findIdx]
          if hHit : H (toprfInputBindPreimage x) = H (toprfInputBindPreimage queried) then
            right
            have hxNeQ : x ≠ queried := fun hEq => hNotMem (hEq ▸ .head xs)
            refine ⟨x, .head xs, ?_, hHit⟩
            intro hPreEq
            unfold toprfInputBindPreimage at hPreEq
            have hxLen : x.length < 256 ^ 8 := hEnrLen x (.head xs)
            have hAll1 : ∀ f ∈ [x], f.length < 256 ^ 8 := by
              intro f hf; rcases List.mem_cons.mp hf with rfl | h0; exact hxLen; cases h0
            have hAll2 : ∀ g ∈ [queried], g.length < 256 ^ 8 := by
              intro g hg; rcases List.mem_cons.mp hg with rfl | h0; exact hQLen; cases h0
            have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hPreEq
            injection hFr with hxEqQ _
            exact hxNeQ hxEqQ
          else
            rw [ite_false_of hHit]
            have ihRes := ih vsl (fun z hz => hEnrLen z (.tail x hz)) (fun hq => hNotMem (.tail x hq))
            rcases ihRes with hNone | ⟨z, hzMem, hPreNe, hCol⟩
            · exact Or.inl hNone
            · exact Or.inr ⟨z, .tail x hzMem, hPreNe, hCol⟩
    else
      rw [ite_false_of hKey]
      exact Or.inl rfl

/-! ## §4. `BlindVC` Rate-6/Capacity-6 6-Limb `absorbRate6Sponge3` Commitment & ZKBoo Selective Disclosure (`blind_vc.rs`, fixing `C0-3` & `C1-2`) -/

/-! ### §4.1 6-Limb `Lane6` Digests, `ZkSoundnessProfile` (ROM vs QROM) & Arity-Framed `absorbRate6Sponge3` Binding -/

/-- Maximum canonical Goldilocks attributes per `BlindVC` credential (`MAX_VC_ATTRS = 32`, `blind_vc.rs:43`). -/
def vcMaxAttrs : Nat := 32

/-- Small-credential 3-block ZKBoo rate-6 attribute slot ceiling (`6` slots in `absorbRate6Sponge3`). -/
def vcSmallMaxAttrs : Nat := 6

/-- Deployed Poseidon2 Merkle accumulator depth (`VC_ACCUMULATOR_DEPTH = 20`, `blind_vc.rs:45`). -/
def vcAccumulatorDepth : Nat := 20

/-- ZKBoo soundness profile (`ZkSoundnessProfile`, `blind_vc.rs:47, 780-810`, fixing `C1-2`):
    - `.classical128`: `219` repetitions (`(2/3)^219 < 2^{-128}` classical ROM soundness,
      whereas `2^{-130} < (2/3)^219` yields `< 65`-bit security against QROM Grover challenge grinding);
    - `.quantum128`: `438` repetitions (`VC_ZKBOO_REPS = 438`, default post-quantum profile:
      `(2/3)^438 < 2^{-256}`, sustaining `≥ 128`-bit QROM soundness against $O(2^{k/2})$ Grover
      amplitude amplification over Fiat-Shamir challenge grinding). -/
inductive ZkSoundnessProfile where
  | classical128
  | quantum128
  deriving DecidableEq, Repr

def ZkSoundnessProfile.repetitions : ZkSoundnessProfile → Nat
  | .classical128 => 219
  | .quantum128 => 438

/-- Default post-quantum ZKBoo repetition count (`VC_ZKBOO_REPS = 438`, `blind_vc.rs:47`). -/
def vcZkBooReps : Nat := ZkSoundnessProfile.quantum128.repetitions

/-- Legacy classical-ROM repetition count (`219`, `ZkSoundnessProfile::Classical128`). -/
def vcClassicalZkBooReps : Nat := ZkSoundnessProfile.classical128.repetitions

set_option exponentiation.threshold 1024 in
/-- Parameter arithmetic for 219 and 438 repetitions. These inequalities
alone are neither a ROM nor a QROM adversary theorem: they contain no oracle
query budget, commitment failure term, or adaptive Fiat–Shamir simulation. -/
theorem zkSoundnessProfile_rom_vs_qrom_bounds :
    ZkSoundnessProfile.classical128.repetitions = 219 ∧
    ZkSoundnessProfile.quantum128.repetitions = 438 ∧
    vcZkBooReps = 438 ∧
    ratLe (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions)
      (1, 2 ^ 128) ∧
    ratLe (1, 2 ^ 130)
      (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions) ∧
    ratLe (2 ^ ZkSoundnessProfile.quantum128.repetitions, 3 ^ ZkSoundnessProfile.quantum128.repetitions)
      (1, 2 ^ 256) := by
  unfold ZkSoundnessProfile.repetitions vcZkBooReps ratLe
  decide

/-- 6-limb Goldilocks digest (`[u64; 6]`, `VC_DIGEST_LIMBS = 6`, `blind_vc.rs:41`):
    6-limb rate/capacity (`p^6 > 2^{383}`), providing `> 191`-bit classical birthday and
    `≥ 128`-bit (`p^2 > 2^{127.9999999996}`) post-quantum BHT / CNS sponge security. -/
structure Lane6 where
  x0 : Goldilocks
  x1 : Goldilocks
  x2 : Goldilocks
  x3 : Goldilocks
  x4 : Goldilocks
  x5 : Goldilocks
  deriving DecidableEq, Repr

theorem Lane6.ext {a b : Lane6}
    (h0 : a.x0 = b.x0) (h1 : a.x1 = b.x1) (h2 : a.x2 = b.x2)
    (h3 : a.x3 = b.x3) (h4 : a.x4 = b.x4) (h5 : a.x5 = b.x5) : a = b := by
  cases a; cases b; subst h0 h1 h2 h3 h4 h5; rfl

def lane6Zero : Lane6 :=
  ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
   Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

def lane6Add (a b : Lane6) : Lane6 :=
  ⟨Goldilocks.add a.x0 b.x0, Goldilocks.add a.x1 b.x1, Goldilocks.add a.x2 b.x2,
   Goldilocks.add a.x3 b.x3, Goldilocks.add a.x4 b.x4, Goldilocks.add a.x5 b.x5⟩

def lane6Sub (a b : Lane6) : Lane6 :=
  ⟨Goldilocks.sub a.x0 b.x0, Goldilocks.sub a.x1 b.x1, Goldilocks.sub a.x2 b.x2,
   Goldilocks.sub a.x3 b.x3, Goldilocks.sub a.x4 b.x4, Goldilocks.sub a.x5 b.x5⟩

def lane6Scale (c : Goldilocks) (a : Lane6) : Lane6 :=
  ⟨Goldilocks.mul c a.x0, Goldilocks.mul c a.x1, Goldilocks.mul c a.x2,
   Goldilocks.mul c a.x3, Goldilocks.mul c a.x4, Goldilocks.mul c a.x5⟩

def state12Rate6 (st : Poseidon2State12) : Lane6 :=
  ⟨st.b0.x0, st.b0.x1, st.b0.x2, st.b0.x3, st.b1.x0, st.b1.x1⟩

def state12Cap6 (st : Poseidon2State12) : Lane6 :=
  ⟨st.b1.x2, st.b1.x3, st.b2.x0, st.b2.x1, st.b2.x2, st.b2.x3⟩

def mkState12Of6 (rate cap : Lane6) : Poseidon2State12 :=
  ⟨⟨rate.x0, rate.x1, rate.x2, rate.x3⟩,
   ⟨rate.x4, rate.x5, cap.x0, cap.x1⟩,
   ⟨cap.x2, cap.x3, cap.x4, cap.x5⟩⟩

private theorem state12Rate6_mk (r c : Lane6) : state12Rate6 (mkState12Of6 r c) = r := rfl
private theorem state12Cap6_mk (r c : Lane6) : state12Cap6 (mkState12Of6 r c) = c := rfl

private theorem mkState12Of6_eta (st : Poseidon2State12) :
    mkState12Of6 (state12Rate6 st) (state12Cap6 st) = st := by
  rcases st with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩
  rfl

/-- Domain tag `"VCATTRV1"` (`0x5643_4154_5452_5631`, `blind_vc.rs:53`). -/
def vcAttrCommitTag : UInt64 := 0x5643415454525631

/-- Domain tag `"VCPRESV1"` (`0x5643_5052_4553_5631`, `blind_vc.rs:54`). -/
def vcPresCommitTag : UInt64 := 0x5643505245535631

/-- Domain tag `"VCSCOPV1"` (`0x5643_5343_4F50_5631`, `blind_vc.rs:55`). -/
def vcScopeTagDom : UInt64 := 0x564353434F505631

/-- Domain tag `"VCMKLEV1"` (`0x5643_4D4B_4C45_5631`, `blind_vc.rs:56`). -/
def vcMerkleNodeTag : UInt64 := 0x56434D4B4C455631

/-- Exact 3-permutation Width-12 (`rate = 6, capacity = 6`) `Poseidon2` sponge (`blind_vc.rs:98-115`):
    absorbs three 6-limb rate chunks `(c0, c1, c2)` with capacity `lane6Zero` and outputs the
    permuted 12-limb state (whose 6-limb rate `state12Rate6` is the 6-limb digest). -/
@[expose] def absorbRate6Sponge3 (c0 c1 c2 : Lane6) : Poseidon2State12 :=
  let p1 := poseidon2Perm12 (mkState12Of6 c0 lane6Zero)
  let p2 := poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 p1) c1) (state12Cap6 p1))
  poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 p2) c2) (state12Cap6 p2))

private theorem gold_add_left_cancel_vc {a b c : Goldilocks}
    (h : Goldilocks.add a b = Goldilocks.add a c) : b = c := by
  have hs := congrArg (fun z => Goldilocks.sub z a) h
  have hCancel : ∀ x y : Goldilocks, Goldilocks.sub (Goldilocks.add x y) x = y := fun x y => by
    rw [← goldOfInt_nat x, ← goldOfInt_nat y]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1; omega
  rwa [hCancel, hCancel] at hs

private theorem gold_add_right_cancel_vc {a b c : Goldilocks}
    (h : Goldilocks.add a c = Goldilocks.add b c) : a = b := by
  have hs := congrArg (fun z => Goldilocks.sub z c) h
  have hCancel : ∀ x y : Goldilocks, Goldilocks.sub (Goldilocks.add x y) y = x := fun x y => by
    rw [← goldOfInt_nat x, ← goldOfInt_nat y]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1; omega
  rwa [hCancel, hCancel] at hs

private theorem lane6Add_left_cancel {a b c : Lane6}
    (h : lane6Add a b = lane6Add a c) : b = c :=
  Lane6.ext
    (gold_add_left_cancel_vc (congrArg Lane6.x0 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x1 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x2 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x3 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x4 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x5 h))

/-- Equal output halves of a public permutation. This unrestricted relation
is not a hardness assumption; use `blindVcReachableBinding204` to retain sponge reachability. -/
def Poseidon2Perm12Sponge6Collision (stA stB : Poseidon2State12) : Prop :=
  stA ≠ stB ∧
  (state12Rate6 (poseidon2Perm12 stA) = state12Rate6 (poseidon2Perm12 stB) ∨
   state12Cap6 (poseidon2Perm12 stA) = state12Cap6 (poseidon2Perm12 stB))

/-- Constructive sponge collision reduction (`0 Classical.choice`):
    any two distinct 3-chunk sequences `(c0₁, c1₁, c2₁) ≠ (c0₂, c1₂, c2₂)` colliding on
    `state12Rate6 (absorbRate6Sponge3 ...)` exhibit an explicit `Poseidon2Perm12Sponge6Collision`. -/
theorem absorbRate6Sponge3_collision_reduction
    {c0₁ c1₁ c2₁ c0₂ c1₂ c2₂ : Lane6}
    (hNe : (c0₁, c1₁, c2₁) ≠ (c0₂, c1₂, c2₂))
    (hDig : state12Rate6 (absorbRate6Sponge3 c0₁ c1₁ c2₁) =
            state12Rate6 (absorbRate6Sponge3 c0₂ c1₂ c2₂)) :
    ∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB := by
  let s1₁ := mkState12Of6 c0₁ lane6Zero
  let s1₂ := mkState12Of6 c0₂ lane6Zero
  let p1₁ := poseidon2Perm12 s1₁
  let p1₂ := poseidon2Perm12 s1₂
  let s2₁ := mkState12Of6 (lane6Add (state12Rate6 p1₁) c1₁) (state12Cap6 p1₁)
  let s2₂ := mkState12Of6 (lane6Add (state12Rate6 p1₂) c1₂) (state12Cap6 p1₂)
  let p2₁ := poseidon2Perm12 s2₁
  let p2₂ := poseidon2Perm12 s2₂
  let s3₁ := mkState12Of6 (lane6Add (state12Rate6 p2₁) c2₁) (state12Cap6 p2₁)
  let s3₂ := mkState12Of6 (lane6Add (state12Rate6 p2₂) c2₂) (state12Cap6 p2₂)
  if h3 : s3₁ = s3₂ then
    if h2 : s2₁ = s2₂ then
      have hp2 : p2₁ = p2₂ := congrArg poseidon2Perm12 h2
      have hRate3 : lane6Add (state12Rate6 p2₁) c2₁ = lane6Add (state12Rate6 p2₂) c2₂ := by
        have hr := congrArg state12Rate6 h3
        rwa [state12Rate6_mk, state12Rate6_mk] at hr
      rw [hp2] at hRate3
      have hc2 : c2₁ = c2₂ := lane6Add_left_cancel hRate3
      if h1 : s1₁ = s1₂ then
        have hp1 : p1₁ = p1₂ := congrArg poseidon2Perm12 h1
        have hRate2 : lane6Add (state12Rate6 p1₁) c1₁ = lane6Add (state12Rate6 p1₂) c1₂ := by
          have hr := congrArg state12Rate6 h2
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        rw [hp1] at hRate2
        have hc1 : c1₁ = c1₂ := lane6Add_left_cancel hRate2
        have hc0 : c0₁ = c0₂ := by
          have hr := congrArg state12Rate6 h1
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        exact False.elim (hNe (by rw [hc0, hc1, hc2]))
      else
        have hCap1 : state12Cap6 p1₁ = state12Cap6 p1₂ := by
          have hc := congrArg state12Cap6 h2
          rwa [state12Cap6_mk, state12Cap6_mk] at hc
        exact ⟨s1₁, s1₂, h1, Or.inr hCap1⟩
    else
      have hCap2 : state12Cap6 p2₁ = state12Cap6 p2₂ := by
        have hc := congrArg state12Cap6 h3
        rwa [state12Cap6_mk, state12Cap6_mk] at hc
      exact ⟨s2₁, s2₂, h2, Or.inr hCap2⟩
  else
    exact ⟨s3₁, s3₂, h3, Or.inl hDig⟩

/-- Fixed-arity 3-block ZKBoo credential schema (`1 ≤ arity ≤ 6`; full `1 ≤ arity ≤ 32` is
    formalized by `computeVcPoseidon2CommitFull` below, matching `MAX_VC_ATTRS = 32` in `blind_vc.rs:43`). -/
structure VcSchema where
  schemaId : UInt64
  arity : Nat
  hArityPos : 1 ≤ arity
  hArityLe : arity ≤ vcSmallMaxAttrs
  deriving DecidableEq, Repr

theorem VcSchema.ext {s₁ s₂ : VcSchema}
    (hId : s₁.schemaId = s₂.schemaId) (hAr : s₁.arity = s₂.arity) : s₁ = s₂ := by
  cases s₁; cases s₂; dsimp only at hId hAr; subst hId hAr; rfl

/-- Low 32-bit limb `schema_id & 0xffff_ffff` (`blind_vc.rs:129, 155, 181`). -/
def vcSchemaLo (sid : UInt64) : Goldilocks :=
  Goldilocks.ofNat (sid.toNat % 4294967296)

/-- High 32-bit limb combined with reduced 64-bit domain tag (`blind_vc.rs:130, 156, 184`). -/
def vcSchemaHiWithTag (sid tag : UInt64) : Goldilocks :=
  Goldilocks.add (Goldilocks.ofNat (sid.toNat / 4294967296)) (Goldilocks.ofNat tag.toNat)

/-- Zero-extended slot lookup `attrs[idx]` (`blind_vc.rs:839-845`). -/
def vcAttrAt (attrs : List Goldilocks) (idx : Nat) : Goldilocks :=
  (attrs[idx]?).getD Goldilocks.zero

/-- 13-limb + `1` separator rate-6 chunking for `compute_vc_poseidon2_commit` (`blind_vc.rs:118-137`):
    explicitly absorbs `Goldilocks.ofNat schema.arity` in `c2.x0` followed by separator `1` in `c2.x1`! -/
def vcCommitChunks (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) :
    Lane6 × Lane6 × Lane6 :=
  (⟨vcAttrAt attrs 0, vcAttrAt attrs 1, vcAttrAt attrs 2,
    vcAttrAt attrs 3, vcAttrAt attrs 4, vcAttrAt attrs 5⟩,
   ⟨blind.x0, blind.x1, blind.x2, blind.x3,
    vcSchemaLo schema.schemaId, vcSchemaHiWithTag schema.schemaId tag⟩,
   ⟨Goldilocks.ofNat schema.arity, Goldilocks.one,
    Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

/-- Arity-framed 6-limb `BlindVC` commitment (`blind_vc.rs:112-138`, fixing `C0-3`):
    enforces `attrs.length = schema.arity` (`1 ≤ arity ≤ 6`), absorbs `schema.arity` into the
    3-permutation rate-6/capacity-6 sponge, and squeezes the 6-limb (`> 383`-bit) digest `Lane6`. -/
@[expose] def computeVcPoseidon2Commit
    (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) : Option Lane6 :=
  if attrs.length = schema.arity then
    let (c0, c1, c2) := vcCommitChunks schema attrs blind tag
    some (state12Rate6 (absorbRate6Sponge3 c0 c1 c2))
  else
    none

private theorem vcSchema_limbs_injective {sid₁ sid₂ tag : UInt64}
    (hLo : vcSchemaLo sid₁ = vcSchemaLo sid₂)
    (hHi : vcSchemaHiWithTag sid₁ tag = vcSchemaHiWithTag sid₂ tag) :
    sid₁ = sid₂ := by
  have hx := sid₁.toNat_lt_size
  have hy := sid₂.toNat_lt_size
  have hp : 4294967296 < goldilocksPrime := by decide
  have hPos : 0 < 4294967296 := by decide
  have hxl : sid₁.toNat % 4294967296 < goldilocksPrime :=
    Nat.lt_trans (Nat.mod_lt sid₁.toNat hPos) hp
  have hyl : sid₂.toNat % 4294967296 < goldilocksPrime :=
    Nat.lt_trans (Nat.mod_lt sid₂.toNat hPos) hp
  have hdiv1 : sid₁.toNat / 4294967296 < 4294967296 := by
    change sid₁.toNat < 18446744073709551616 at hx
    omega
  have hdiv2 : sid₂.toNat / 4294967296 < 4294967296 := by
    change sid₂.toNat < 18446744073709551616 at hy
    omega
  have hxh : sid₁.toNat / 4294967296 < goldilocksPrime := Nat.lt_trans hdiv1 hp
  have hyh : sid₂.toNat / 4294967296 < goldilocksPrime := Nat.lt_trans hdiv2 hp
  have hLoVal := congrArg Goldilocks.val hLo
  simp only [vcSchemaLo, Goldilocks.ofNat_val, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] at hLoVal
  have hHiSub := gold_add_right_cancel_vc hHi
  have hHiVal := congrArg Goldilocks.val hHiSub
  simp only [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hxh, Nat.mod_eq_of_lt hyh] at hHiVal
  apply UInt64.toNat_inj.mp
  omega

private theorem vcCommitChunks_injective
    {schema₁ schema₂ : VcSchema} {attrs₁ attrs₂ : List Goldilocks}
    {blind₁ blind₂ : Lane4} {tag : UInt64}
    (hLen₁ : attrs₁.length = schema₁.arity)
    (hLen₂ : attrs₂.length = schema₂.arity)
    (hEq : vcCommitChunks schema₁ attrs₁ blind₁ tag = vcCommitChunks schema₂ attrs₂ blind₂ tag) :
    schema₁ = schema₂ ∧ attrs₁ = attrs₂ ∧ blind₁ = blind₂ := by
  have hArVal := congrArg (fun p => p.2.2.x0.val) hEq
  dsimp only [vcCommitChunks] at hArVal
  have hp6 : 6 < goldilocksPrime := by decide
  have hArLt₁ : schema₁.arity < goldilocksPrime := by
    have hLe := schema₁.hArityLe
    unfold vcSmallMaxAttrs at hLe
    omega
  have hArLt₂ : schema₂.arity < goldilocksPrime := by
    have hLe := schema₂.hArityLe
    unfold vcSmallMaxAttrs at hLe
    omega
  simp only [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hArLt₁, Nat.mod_eq_of_lt hArLt₂] at hArVal
  have hSid : schema₁.schemaId = schema₂.schemaId :=
    vcSchema_limbs_injective
      (congrArg (fun p => p.2.1.x4) hEq)
      (congrArg (fun p => p.2.1.x5) hEq)
  have hSchema : schema₁ = schema₂ := VcSchema.ext hSid hArVal
  have hBlind : blind₁ = blind₂ :=
    Lane4.ext
      (congrArg (fun p => p.2.1.x0) hEq)
      (congrArg (fun p => p.2.1.x1) hEq)
      (congrArg (fun p => p.2.1.x2) hEq)
      (congrArg (fun p => p.2.1.x3) hEq)
  have h0 : vcAttrAt attrs₁ 0 = vcAttrAt attrs₂ 0 := congrArg (fun p => p.1.x0) hEq
  have h1 : vcAttrAt attrs₁ 1 = vcAttrAt attrs₂ 1 := congrArg (fun p => p.1.x1) hEq
  have h2 : vcAttrAt attrs₁ 2 = vcAttrAt attrs₂ 2 := congrArg (fun p => p.1.x2) hEq
  have h3 : vcAttrAt attrs₁ 3 = vcAttrAt attrs₂ 3 := congrArg (fun p => p.1.x3) hEq
  have h4 : vcAttrAt attrs₁ 4 = vcAttrAt attrs₂ 4 := congrArg (fun p => p.1.x4) hEq
  have h5 : vcAttrAt attrs₁ 5 = vcAttrAt attrs₂ 5 := congrArg (fun p => p.1.x5) hEq
  have hLenEq : attrs₁.length = attrs₂.length := by omega
  have hAttrs : attrs₁ = attrs₂ := by
    apply List.ext_getElem hLenEq
    intro i hi1 hi2
    have hLe1 : attrs₁.length ≤ 6 := hLen₁ ▸ schema₁.hArityLe
    have hiMax : i < 6 := by omega
    have hGet1 : vcAttrAt attrs₁ i = attrs₁[i] := by
      unfold vcAttrAt; rw [List.getElem?_eq_getElem hi1]; rfl
    have hGet2 : vcAttrAt attrs₂ i = attrs₂[i] := by
      unfold vcAttrAt; rw [List.getElem?_eq_getElem hi2]; rfl
    rw [← hGet1, ← hGet2]
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  exact ⟨hSchema, hAttrs, hBlind⟩

set_option exponentiation.threshold 1024 in
/-- **Flagship §4.1 Theorem — `BlindVC` 6-Limb Arity-Framed Sponge Commitment Binding
    (`blind_vc_commit_binding_reduces_to_sponge12_collision`, fixing `C0-3`)**:
    1. **Explicit Arity Framing**: `computeVcPoseidon2Commit` accepts iff `1 ≤ attrs.length = schema.arity ≤ 6`;
    2. **Same-Arity & Cross-Arity Binding Reduction**: ANY two distinct openings
       `(schema₁, attrs₁, blind₁) ≠ (schema₂, attrs₂, blind₂)` (including cross-arity `[x]` vs `[x, 0]`)
       yielding `some c` constructively exhibit `Poseidon2Perm12Sponge6Collision stA stB`;
    3. **Cross-Domain Non-Confusion**: `vcAttrCommitTag` and `vcPresCommitTag` chunk tuples are disjoint;
    4. **Full 384-Bit Digest Space**: `2 ^ 383 < goldilocksPrime ^ 6`. -/
theorem blind_vc_commit_binding_reduces_to_sponge12_collision :
    (∀ (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) (c : Lane6),
      computeVcPoseidon2Commit schema attrs blind tag = some c →
      1 ≤ attrs.length ∧ attrs.length = schema.arity ∧ attrs.length ≤ vcSmallMaxAttrs) ∧
    (∀ (schema₁ schema₂ : VcSchema) (attrs₁ attrs₂ : List Goldilocks)
       (blind₁ blind₂ : Lane4) (tag : UInt64) (c : Lane6),
      computeVcPoseidon2Commit schema₁ attrs₁ blind₁ tag = some c →
      computeVcPoseidon2Commit schema₂ attrs₂ blind₂ tag = some c →
      (schema₁, attrs₁, blind₁) ≠ (schema₂, attrs₂, blind₂) →
      ∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB) ∧
    (∀ (s₁ s₂ : VcSchema) (attrs₁ attrs₂ : List Goldilocks) (blind₁ blind₂ : Lane4),
      s₁.schemaId = s₂.schemaId →
      vcCommitChunks s₁ attrs₁ blind₁ vcAttrCommitTag ≠
        vcCommitChunks s₂ attrs₂ blind₂ vcPresCommitTag) ∧
    2 ^ 383 < goldilocksPrime ^ 6 := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro schema attrs blind tag c hCom
    unfold computeVcPoseidon2Commit at hCom
    if hLen : attrs.length = schema.arity then
      exact ⟨hLen ▸ schema.hArityPos, hLen, hLen ▸ schema.hArityLe⟩
    else
      rw [ite_false_of hLen] at hCom; cases hCom
  · intro schema₁ schema₂ attrs₁ attrs₂ blind₁ blind₂ tag c hCom1 hCom2 hNe
    unfold computeVcPoseidon2Commit at hCom1 hCom2
    if hLen1 : attrs₁.length = schema₁.arity then
      rw [ite_true_of hLen1] at hCom1
      if hLen2 : attrs₂.length = schema₂.arity then
        rw [ite_true_of hLen2] at hCom2
        injection hCom1 with hc1
        injection hCom2 with hc2
        have hChunksNe : vcCommitChunks schema₁ attrs₁ blind₁ tag ≠ vcCommitChunks schema₂ attrs₂ blind₂ tag := by
          intro hEq
          obtain ⟨hs, ha, hb⟩ := vcCommitChunks_injective hLen1 hLen2 hEq
          exact hNe (by rw [hs, ha, hb])
        exact absorbRate6Sponge3_collision_reduction hChunksNe (hc1.trans hc2.symm)
      else
        rw [ite_false_of hLen2] at hCom2; cases hCom2
    else
      rw [ite_false_of hLen1] at hCom1; cases hCom1
  · intro s₁ s₂ attrs₁ attrs₂ blind₁ blind₂ hSid hEq
    have hHi := congrArg (fun p => p.2.1.x5) hEq
    dsimp only [vcCommitChunks] at hHi
    rw [hSid] at hHi
    have hTagEq := gold_add_left_cancel_vc hHi
    have hValEq := congrArg Goldilocks.val hTagEq
    have hNeVal : (Goldilocks.ofNat vcAttrCommitTag.toNat).val ≠
        (Goldilocks.ofNat vcPresCommitTag.toNat).val := by
      unfold vcAttrCommitTag vcPresCommitTag
      simp only [Goldilocks.ofNat_val]
      decide
    exact hNeVal hValEq

/-- **`#tooth` (`tooth_unframed_trailing_zero_collision`, `C0-3`)**:
    Omitting `schema.arity` from chunk `c2` makes `(arity = 1, [x])` and `(arity = 2, [x, 0])`
    absorb **identical** sponge blocks (`rfl` — zero permutation collision needed!), whereas
    `vcCommitChunks` strictly separates `(s₁, [x])` from `(s₂, [x, 0])` and `computeVcPoseidon2Commit`
    deterministically rejects wrong-arity `[x, 0]` (`= none`)! -/
theorem tooth_unframed_trailing_zero_collision (sid : UInt64) (x : Goldilocks) (blind : Lane4) (tag : UInt64) :
    let s₁ : VcSchema := ⟨sid, 1, by decide, by decide⟩
    let s₂ : VcSchema := ⟨sid, 2, by decide, by decide⟩
    let unframedChunks (attrs : List Goldilocks) : Lane6 × Lane6 × Lane6 :=
      (⟨vcAttrAt attrs 0, vcAttrAt attrs 1, vcAttrAt attrs 2,
        vcAttrAt attrs 3, vcAttrAt attrs 4, vcAttrAt attrs 5⟩,
       ⟨blind.x0, blind.x1, blind.x2, blind.x3, vcSchemaLo sid, vcSchemaHiWithTag sid tag⟩,
       ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)
    [x] ≠ [x, Goldilocks.zero] ∧
    unframedChunks [x] = unframedChunks [x, Goldilocks.zero] ∧
    vcCommitChunks s₁ [x] blind tag ≠ vcCommitChunks s₂ [x, Goldilocks.zero] blind tag ∧
    computeVcPoseidon2Commit s₁ [x, Goldilocks.zero] blind tag = none := by
  refine ⟨(by intro h; injection h with _ hNil; cases hNil), rfl, ?_, rfl⟩
  intro hEq
  obtain ⟨hS, _, _⟩ := vcCommitChunks_injective rfl rfl hEq
  have hAr := congrArg VcSchema.arity hS
  cases hAr

/-! ### §4.2 6-Limb Scope Tag, Merkle Accumulator & Algebraic Boolean Gate Soundness -/

/-- 12-limb + `1` separator rate-6 chunks for `compute_vc_scope_tag` (`blind_vc.rs:145-169`). -/
def vcScopeChunks (sid : UInt64) (holderBlind scopeLimbs : Lane4) : Lane6 × Lane6 × Lane6 :=
  (⟨holderBlind.x0, holderBlind.x1, holderBlind.x2, holderBlind.x3, scopeLimbs.x0, scopeLimbs.x1⟩,
   ⟨scopeLimbs.x2, scopeLimbs.x3, Goldilocks.zero, Goldilocks.zero,
    vcSchemaLo sid, vcSchemaHiWithTag sid vcScopeTagDom⟩,
   ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero,
    Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

/-- 6-limb scope-bound pseudonym/nullifier `compute_vc_scope_tag` (`blind_vc.rs:145-170`). -/
def computeVcScopeTag (sid : UInt64) (holderBlind scopeLimbs : Lane4) : Lane6 :=
  let (c0, c1, c2) := vcScopeChunks sid holderBlind scopeLimbs
  state12Rate6 (absorbRate6Sponge3 c0 c1 c2)

/-- 16-limb + `1` separator rate-6 chunks for `merkle_hash_pair` (`blind_vc.rs:175-199`). -/
def vcMerkleChunks (left right : Lane6) (epoch : UInt64) (layer : Nat) : Lane6 × Lane6 × Lane6 :=
  (left,
   right,
   ⟨vcSchemaLo epoch, Goldilocks.ofNat layer,
    Goldilocks.ofNat vcMerkleNodeTag.toNat, vcSchemaHiWithTag epoch poseidon2ConstIV,
    Goldilocks.one, Goldilocks.zero⟩)

/-- Domain-separated 6-limb Merkle parent hash `merkle_hash_pair` (`blind_vc.rs:175-200`). -/
def vcMerkleHashPair (left right : Lane6) (epoch : UInt64) (layer : Nat) : Lane6 :=
  let (c0, c1, c2) := vcMerkleChunks left right epoch layer
  state12Rate6 (absorbRate6Sponge3 c0 c1 c2)

/-- Arithmetic 6-limb Merkle branch selector (`blind_vc.rs:2000-2035`):
    `delta = b * (sib - cur)`, `left = cur + delta`, `right = sib - delta`. -/
def vcMerkleStepArith (epoch : UInt64) (layer : Nat) (cur sib : Lane6) (b : Goldilocks) : Lane6 :=
  let delta := lane6Scale b (lane6Sub sib cur)
  let left := lane6Add cur delta
  let right := lane6Sub sib delta
  vcMerkleHashPair left right epoch layer

def evalVcMerklePathFrom (epoch : UInt64) : Nat → Lane6 → List (Goldilocks × Lane6) → Lane6
  | _, cur, [] => cur
  | layer, cur, (b, sib) :: rest =>
    evalVcMerklePathFrom epoch (layer + 1) (vcMerkleStepArith epoch layer cur sib b) rest

/-- Boolean 6-limb Merkle path specification (`false` => `cur` is left child, `true` => `cur` is right child). -/
def evalVcMerklePathBool (epoch : UInt64) : Nat → Lane6 → List (Bool × Lane6) → Lane6
  | _, cur, [] => cur
  | layer, cur, (false, sib) :: rest =>
    evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair cur sib epoch layer) rest
  | layer, cur, (true, sib) :: rest =>
    evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair sib cur epoch layer) rest

/-- Over prime field `Goldilocks`, `b * (1 - b) = 0` holds iff `b = 0 ∨ b = 1` (`blind_vc.rs:1994-1996`). -/
theorem goldilocks_bool_gate_zero_or_one (b : Goldilocks)
    (hZero : Goldilocks.mul b (Goldilocks.sub Goldilocks.one b) = Goldilocks.zero) :
    b = Goldilocks.zero ∨ b = Goldilocks.one := by
  have hVal := congrArg Goldilocks.val hZero
  rw [Goldilocks.mul_val, Goldilocks.zero_val] at hVal
  have hDvd : goldilocksPrime ∣ b.val * (Goldilocks.sub Goldilocks.one b).val :=
    Nat.dvd_of_mod_eq_zero hVal
  if hb0 : b.val = 0 then
    exact Or.inl (Goldilocks.ext hb0)
  else
    right
    have hbLt := b.isLt
    have hNotDvdB : ¬ (goldilocksPrime ∣ b.val) := by
      intro hd
      have hle := Nat.le_of_dvd (by omega) hd
      omega
    have hDvdSub : goldilocksPrime ∣ (Goldilocks.sub Goldilocks.one b).val :=
      (goldilocksPrime_isPrime ()).dvd_mul hDvd hNotDvdB
    have hSubLt := (Goldilocks.sub Goldilocks.one b).isLt
    have hSubVal0 : (Goldilocks.sub Goldilocks.one b).val = 0 := by
      if hs0 : (Goldilocks.sub Goldilocks.one b).val = 0 then exact hs0
      else
        have hle := Nat.le_of_dvd (by omega) hDvdSub
        omega
    have hSubEq0 : Goldilocks.sub Goldilocks.one b = Goldilocks.zero := Goldilocks.ext hSubVal0
    have hAdd := congrArg (fun z => Goldilocks.add z b) hSubEq0
    have hLhs : Goldilocks.add (Goldilocks.sub Goldilocks.one b) b = Goldilocks.one := by
      rw [← goldOfInt_nat Goldilocks.one, ← goldOfInt_nat b]
      simp only [goldOfInt_sub, goldOfInt_add]; congr 1; omega
    have hRhs : Goldilocks.add Goldilocks.zero b = b := by
      rw [← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat b]
      simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1; omega
    rw [hLhs, hRhs] at hAdd
    exact hAdd.symm

private theorem vcMerkleStepArith_zero (epoch : UInt64) (layer : Nat) (cur sib : Lane6) :
    vcMerkleStepArith epoch layer cur sib Goldilocks.zero = vcMerkleHashPair cur sib epoch layer := by
  unfold vcMerkleStepArith lane6Scale lane6Sub lane6Add
  dsimp only
  have hL : ∀ c s : Goldilocks, Goldilocks.add c (Goldilocks.mul Goldilocks.zero (Goldilocks.sub s c)) = c := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.zero]
    simp only [Goldilocks.zero_val, goldOfInt_sub, goldOfInt_mul, goldOfInt_add]
    congr 1; simp
  have hR : ∀ c s : Goldilocks, Goldilocks.sub s (Goldilocks.mul Goldilocks.zero (Goldilocks.sub s c)) = s := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.zero]
    simp only [Goldilocks.zero_val, goldOfInt_sub, goldOfInt_mul]
    congr 1; simp
  simp only [hL, hR]

private theorem vcMerkleStepArith_one (epoch : UInt64) (layer : Nat) (cur sib : Lane6) :
    vcMerkleStepArith epoch layer cur sib Goldilocks.one = vcMerkleHashPair sib cur epoch layer := by
  unfold vcMerkleStepArith lane6Scale lane6Sub lane6Add
  dsimp only
  have hL : ∀ c s : Goldilocks, Goldilocks.add c (Goldilocks.mul Goldilocks.one (Goldilocks.sub s c)) = s := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.one]
    simp only [Goldilocks.one_val, goldOfInt_sub, goldOfInt_mul, goldOfInt_add]
    congr 1; omega
  have hR : ∀ c s : Goldilocks, Goldilocks.sub s (Goldilocks.mul Goldilocks.one (Goldilocks.sub s c)) = c := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.one]
    simp only [Goldilocks.one_val, goldOfInt_sub, goldOfInt_mul]
    congr 1; omega
  simp only [hL, hR]

theorem evalVcMerklePathFrom_eq_bool (epoch : UInt64) :
    ∀ (layer : Nat) (cur : Lane6) (steps : List (Goldilocks × Lane6)),
      (∀ p ∈ steps, p.1 = Goldilocks.zero ∨ p.1 = Goldilocks.one) →
      ∃ boolSteps : List (Bool × Lane6),
        boolSteps.length = steps.length ∧
        evalVcMerklePathFrom epoch layer cur steps =
          evalVcMerklePathBool epoch layer cur boolSteps
  | _, cur, [], _ => ⟨[], rfl, rfl⟩
  | layer, cur, (b, sib) :: rest, hAll => by
    have hb := hAll (b, sib) (.head rest)
    have hRest : ∀ p ∈ rest, p.1 = Goldilocks.zero ∨ p.1 = Goldilocks.one :=
      fun p hp => hAll p (.tail _ hp)
    rcases hb with rfl | rfl
    · obtain ⟨bs, hLen, hEq⟩ :=
        evalVcMerklePathFrom_eq_bool epoch (layer + 1) (vcMerkleHashPair cur sib epoch layer) rest hRest
      refine ⟨(false, sib) :: bs, by simp [hLen], ?_⟩
      dsimp only [evalVcMerklePathFrom, evalVcMerklePathBool]
      rw [vcMerkleStepArith_zero, hEq]
    · obtain ⟨bs, hLen, hEq⟩ :=
        evalVcMerklePathFrom_eq_bool epoch (layer + 1) (vcMerkleHashPair sib cur epoch layer) rest hRest
      refine ⟨(true, sib) :: bs, by simp [hLen], ?_⟩
      dsimp only [evalVcMerklePathFrom, evalVcMerklePathBool]
      rw [vcMerkleStepArith_one, hEq]

/-! ### §4.3 `Vec`, `SimpleEquiv` Combinators, PRG Coin Tapes & 3-Party `absorbRate6Sponge3` + 6-Limb Merkle ZKBoo Verifier -/

/-- Length-indexed constructive vector (`0` Mathlib dependencies, explicit `DecidableEq`). -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

def Vec.head {α : Type} {n : Nat} : Vec α (n + 1) → α
  | .cons x _ => x

def Vec.tail {α : Type} {n : Nat} : Vec α (n + 1) → Vec α n
  | .cons _ xs => xs

private theorem Vec.eta_cons {α : Type} {n : Nat} (v : Vec α (n + 1)) :
    Vec.cons v.head v.tail = v := by
  cases v; rfl

def Vec.toList {α : Type} : {n : Nat} → Vec α n → List α
  | 0, .nil => []
  | _ + 1, .cons x xs => x :: xs.toList

theorem Vec.toList_length {α : Type} : ∀ {n : Nat} (v : Vec α n), v.toList.length = n
  | 0, .nil => rfl
  | _ + 1, .cons _ xs => by simp [Vec.toList, Vec.toList_length xs]

theorem Vec.toList_injective {α : Type} : ∀ {n : Nat} {u v : Vec α n},
    u.toList = v.toList → u = v
  | 0, .nil, .nil, _ => rfl
  | _ + 1, .cons x xs, .cons y ys, h => by
    simp only [Vec.toList] at h
    injection h with hx hxs
    rw [hx, Vec.toList_injective hxs]

def Vec.ofList {α : Type} : (xs : List α) → Vec α xs.length
  | [] => .nil
  | x :: xs => .cons x (Vec.ofList xs)

theorem Vec.toList_ofList {α : Type} : ∀ (xs : List α), (Vec.ofList xs).toList = xs
  | [] => rfl
  | x :: xs => by simp [Vec.ofList, Vec.toList, Vec.toList_ofList xs]

def Vec.replicate {α : Type} : (n : Nat) → α → Vec α n
  | 0, _ => .nil
  | n + 1, x => .cons x (Vec.replicate n x)

private theorem Vec.cons_inj {α : Type} {n : Nat} {x y : α} {xs ys : Vec α n}
    (h : Vec.cons x xs = Vec.cons y ys) : x = y ∧ xs = ys := by
  cases h
  exact ⟨rfl, rfl⟩

def Vec.decEq {α : Type} [DecidableEq α] : {n : Nat} → (u v : Vec α n) → Decidable (u = v)
  | 0, .nil, .nil => isTrue rfl
  | _ + 1, .cons x xs, .cons y ys =>
    match _root_.decEq x y, Vec.decEq xs ys with
    | isTrue hx, isTrue hxs => isTrue (by subst hx hxs; rfl)
    | isFalse hx, _ => isFalse (fun h => hx (Vec.cons_inj h).1)
    | _, isFalse hxs => isFalse (fun h => hxs (Vec.cons_inj h).2)

instance {α : Type} [DecidableEq α] {n : Nat} : DecidableEq (Vec α n) := Vec.decEq

/-- Dependent `Vec` cons bijection (`0 Classical.choice`) for multi-round / multi-level simulation. -/
private def seDepConsToFun {α β : Type} {n : Nat}
    (eqHead : SimpleEquiv α β)
    (eqTail : α → SimpleEquiv (Vec α n) (Vec β n)) :
    Vec α (n + 1) → Vec β (n + 1)
  | .cons x xs => .cons (eqHead.toFun x) ((eqTail x).toFun xs)

private def seDepConsInvFun {α β : Type} {n : Nat}
    (eqHead : SimpleEquiv α β)
    (eqTail : α → SimpleEquiv (Vec α n) (Vec β n)) :
    Vec β (n + 1) → Vec α (n + 1)
  | .cons y ys =>
    let x := eqHead.invFun y
    .cons x ((eqTail x).invFun ys)

private def seDepCons {α β : Type} {n : Nat}
    (eqHead : SimpleEquiv α β)
    (eqTail : α → SimpleEquiv (Vec α n) (Vec β n)) :
    SimpleEquiv (Vec α (n + 1)) (Vec β (n + 1)) where
  toFun := seDepConsToFun eqHead eqTail
  invFun := seDepConsInvFun eqHead eqTail
  left_inv
    | .cons x xs => by
      simp only [seDepConsToFun, seDepConsInvFun]
      rw [eqHead.left_inv x, (eqTail x).left_inv xs]
  right_inv
    | .cons y ys => by
      simp only [seDepConsToFun, seDepConsInvFun]
      rw [eqHead.right_inv y, (eqTail (eqHead.invFun y)).right_inv ys]

private def seVecCongr {α β : Type} : {n : Nat} → (Fin n → SimpleEquiv α β) → SimpleEquiv (Vec α n) (Vec β n)
  | 0, _ =>
    { toFun := fun _ => .nil
      invFun := fun _ => .nil
      left_inv := fun | .nil => rfl
      right_inv := fun | .nil => rfl }
  | n + 1, fs =>
    seDepCons (fs ⟨0, Nat.zero_lt_succ n⟩)
      (fun _ => seVecCongr (fun i => fs ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

abbrev VcWire3 := Fin 3 → Goldilocks
abbrev VcLane4_3 := Fin 3 → Lane4
abbrev VcLane6_3 := Fin 3 → Lane6
abbrev VcState12_3 := Fin 3 → Poseidon2State12

/-- Cyclic adjacent ZKBoo party `(e + 1) % 3` (`blind_vc.rs:334, 1916`). -/
def vcNextParty3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

/-- Unopened 3rd ZKBoo party `(e + 2) % 3` (`blind_vc.rs:766`). -/
def vcUnopenedParty3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

/-- Assemble a 3-party assignment from values at `(e, (e+1)%3, (e+2)%3)`. -/
def mkParty3At {α : Type} (e : Fin 3) (vE vE1 vU : α) : Fin 3 → α :=
  match e with
  | ⟨0, _⟩ => fun | ⟨0, _⟩ => vE | ⟨1, _⟩ => vE1 | ⟨2, _⟩ => vU
  | ⟨1, _⟩ => fun | ⟨0, _⟩ => vU | ⟨1, _⟩ => vE  | ⟨2, _⟩ => vE1
  | ⟨2, _⟩ => fun | ⟨0, _⟩ => vE1 | ⟨1, _⟩ => vU | ⟨2, _⟩ => vE

private theorem fin3_eq_012 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨iv, hiv⟩
  have hc : iv = 0 ∨ iv = 1 ∨ iv = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem fin3_all {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  rcases fin3_eq_012 i with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

private theorem mkParty3At_e {α : Type} (e : Fin 3) (vE vE1 vU : α) :
    mkParty3At e vE vE1 vU e = vE := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

private theorem mkParty3At_next {α : Type} (e : Fin 3) (vE vE1 vU : α) :
    mkParty3At e vE vE1 vU (vcNextParty3 e) = vE1 := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

private theorem mkParty3At_unopened {α : Type} (e : Fin 3) (vE vE1 vU : α) :
    mkParty3At e vE vE1 vU (vcUnopenedParty3 e) = vU := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

private theorem mkParty3At_eta {α : Type} (e : Fin 3) (f : Fin 3 → α) :
    mkParty3At e (f e) (f (vcNextParty3 e)) (f (vcUnopenedParty3 e)) = f := by
  funext i
  rcases fin3_eq_012 e with rfl | rfl | rfl <;>
    rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl

private theorem vcNextParty3_next_eq_unopened (e : Fin 3) :
    vcNextParty3 (vcNextParty3 e) = vcUnopenedParty3 e := by
  rcases fin3_eq_012 e with rfl | rfl | rfl <;> rfl

def vcSum3 (w : VcWire3) : Goldilocks :=
  Goldilocks.add (Goldilocks.add (w 0) (w 1)) (w 2)

def vcSumLane4_3 (w : VcLane4_3) : Lane4 :=
  lane4Add (lane4Add (w 0) (w 1)) (w 2)

def vcSumLane6_3 (w : VcLane6_3) : Lane6 :=
  lane6Add (lane6Add (w 0) (w 1)) (w 2)

def vcSumState12_3 (st : VcState12_3) : Poseidon2State12 :=
  state12Add (state12Add (st 0) (st 1)) (st 2)

private theorem vcSumLane4_3_eq (w : VcLane4_3) :
    vcSumLane4_3 w =
      ⟨vcSum3 (fun i => (w i).x0), vcSum3 (fun i => (w i).x1),
       vcSum3 (fun i => (w i).x2), vcSum3 (fun i => (w i).x3)⟩ := by
  unfold vcSumLane4_3 vcSum3
  simp only [lane4Add_eq]

private theorem vcSumLane6_3_eq (w : VcLane6_3) :
    vcSumLane6_3 w =
      ⟨vcSum3 (fun i => (w i).x0), vcSum3 (fun i => (w i).x1),
       vcSum3 (fun i => (w i).x2), vcSum3 (fun i => (w i).x3),
       vcSum3 (fun i => (w i).x4), vcSum3 (fun i => (w i).x5)⟩ := rfl

private theorem vcSumState12_3_lanes (st : VcState12_3) :
    vcSumState12_3 st =
      ⟨vcSumLane4_3 (fun i => (st i).b0),
       vcSumLane4_3 (fun i => (st i).b1),
       vcSumLane4_3 (fun i => (st i).b2)⟩ := by
  unfold vcSumState12_3 vcSumLane4_3
  simp only [state12Add_eq, lane4Add_eq]

private theorem vcSumState12_3_of6 (r c : VcLane6_3) :
    vcSumState12_3 (fun i => mkState12Of6 (r i) (c i)) =
      mkState12Of6 (vcSumLane6_3 r) (vcSumLane6_3 c) := by
  rw [vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, mkState12Of6, vcSumLane6_3_eq]

private theorem state12Rate6_vcSum (st : VcState12_3) :
    state12Rate6 (vcSumState12_3 st) = vcSumLane6_3 (fun i => state12Rate6 (st i)) := by
  rw [vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, state12Rate6, vcSumLane6_3_eq]

private theorem state12Cap6_vcSum (st : VcState12_3) :
    state12Cap6 (vcSumState12_3 st) = vcSumLane6_3 (fun i => state12Cap6 (st i)) := by
  rw [vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, state12Cap6, vcSumLane6_3_eq]

private theorem vcSum3_zero : vcSum3 (fun _ => Goldilocks.zero) = Goldilocks.zero := by
  unfold vcSum3
  rw [← goldOfInt_nat Goldilocks.zero]
  simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1

private theorem vcSumLane6_3_zero : vcSumLane6_3 (fun _ => lane6Zero) = lane6Zero := by
  rw [vcSumLane6_3_eq]
  simp only [lane6Zero, vcSum3_zero]

private theorem vcSum3_add (a b : VcWire3) :
    vcSum3 (fun i => Goldilocks.add (a i) (b i)) = Goldilocks.add (vcSum3 a) (vcSum3 b) := by
  unfold vcSum3
  dsimp only
  rw [← goldOfInt_nat (a 0), ← goldOfInt_nat (b 0), ← goldOfInt_nat (a 1),
      ← goldOfInt_nat (b 1), ← goldOfInt_nat (a 2), ← goldOfInt_nat (b 2)]
  simp only [goldOfInt_add]; congr 1; omega

private theorem vcSum3_sub (a b : VcWire3) :
    vcSum3 (fun i => Goldilocks.sub (a i) (b i)) = Goldilocks.sub (vcSum3 a) (vcSum3 b) := by
  unfold vcSum3
  dsimp only
  rw [← goldOfInt_nat (a 0), ← goldOfInt_nat (b 0), ← goldOfInt_nat (a 1),
      ← goldOfInt_nat (b 1), ← goldOfInt_nat (a 2), ← goldOfInt_nat (b 2)]
  simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega

private theorem vcSumLane6_3_add (a b : VcLane6_3) :
    vcSumLane6_3 (fun i => lane6Add (a i) (b i)) = lane6Add (vcSumLane6_3 a) (vcSumLane6_3 b) := by
  simp only [vcSumLane6_3_eq, lane6Add, vcSum3_add]

private theorem vcUnopened_of_sum3 (e : Fin 3) {w : VcWire3} {target : Goldilocks}
    (hSum : vcSum3 w = target) :
    w = mkParty3At e (w e) (w (vcNextParty3 e))
          (Goldilocks.sub (Goldilocks.sub target (w e)) (w (vcNextParty3 e))) := by
  rw [← hSum]
  have hUn : w (vcUnopenedParty3 e) =
      Goldilocks.sub (Goldilocks.sub (vcSum3 w) (w e)) (w (vcNextParty3 e)) := by
    unfold vcSum3
    rcases fin3_eq_012 e with rfl | rfl | rfl <;>
      (dsimp only [vcNextParty3, vcUnopenedParty3];
       rw [← goldOfInt_nat (w 0), ← goldOfInt_nat (w 1), ← goldOfInt_nat (w 2)];
       simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega)
  rw [← hUn, mkParty3At_eta]

private theorem vcUnopened_of_sumLane6_3 (e : Fin 3) {w : VcLane6_3} {target : Lane6}
    (hSum : vcSumLane6_3 w = target) :
    w = mkParty3At e (w e) (w (vcNextParty3 e))
          (lane6Sub (lane6Sub target (w e)) (w (vcNextParty3 e))) := by
  have hx0 := vcUnopened_of_sum3 e (w := fun i => (w i).x0) (congrArg Lane6.x0 hSum)
  have hx1 := vcUnopened_of_sum3 e (w := fun i => (w i).x1) (congrArg Lane6.x1 hSum)
  have hx2 := vcUnopened_of_sum3 e (w := fun i => (w i).x2) (congrArg Lane6.x2 hSum)
  have hx3 := vcUnopened_of_sum3 e (w := fun i => (w i).x3) (congrArg Lane6.x3 hSum)
  have hx4 := vcUnopened_of_sum3 e (w := fun i => (w i).x4) (congrArg Lane6.x4 hSum)
  have hx5 := vcUnopened_of_sum3 e (w := fun i => (w i).x5) (congrArg Lane6.x5 hSum)
  funext i
  apply Lane6.ext
  · have h := congrFun hx0 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx1 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx2 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx3 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx4 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h
  · have h := congrFun hx5 i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> exact h

/-- Opened 2-party wire projection `(w e, w ((e + 1) % 3))`. -/
def vcPairAt (w : VcWire3) (e : Fin 3) : Goldilocks × Goldilocks :=
  (w e, w (vcNextParty3 e))

def vcPairAtLane6 (w : VcLane6_3) (e : Fin 3) : Lane6 × Lane6 :=
  (w e, w (vcNextParty3 e))

def vcPairAtState12 (st : VcState12_3) (e : Fin 3) : Poseidon2State12 × Poseidon2State12 :=
  (st e, st (vcNextParty3 e))

/-- 2-party public constant addition `ZkBooVerifierTape::add_const` (`blind_vc.rs:352-359`). -/
def vcPairAddConst (e : Fin 3) (x : Goldilocks × Goldilocks) (c : Goldilocks) :
    Goldilocks × Goldilocks :=
  if e = 0 then (Goldilocks.add x.1 c, x.2)
  else if vcNextParty3 e = 0 then (x.1, Goldilocks.add x.2 c)
  else x

def vcWireAddConst3 (w : VcWire3) (c : Goldilocks) : VcWire3 :=
  fun i => if i = 0 then Goldilocks.add (w 0) c else w i

def vcConstWire3 (c : Goldilocks) : VcWire3 :=
  fun i => if i = 0 then c else Goldilocks.zero

def vcConstPair (e : Fin 3) (c : Goldilocks) : Goldilocks × Goldilocks :=
  vcPairAddConst e (Goldilocks.zero, Goldilocks.zero) c

private theorem vcPairAddConst_spec (w : VcWire3) (c : Goldilocks) (e : Fin 3) :
    vcPairAddConst e (vcPairAt w e) c = vcPairAt (vcWireAddConst3 w c) e := by
  rcases e with ⟨ev, hev⟩
  have hCases : ev = 0 ∨ ev = 1 ∨ ev = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> rfl

private theorem vcConstPair_spec (c : Goldilocks) (e : Fin 3) :
    vcConstPair e c = vcPairAt (vcConstWire3 c) e := by
  have hz : Goldilocks.add Goldilocks.zero c = c := by
    rw [← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat c]
    simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1; omega
  have he : e = 0 ∨ e = 1 ∨ e = 2 := by revert e; decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  rcases he with rfl | rfl | rfl
  · simp only [vcConstPair, vcPairAddConst, vcPairAt, vcConstWire3, vcNextParty3, ↓reduceIte, h10, hz]
  · simp only [vcConstPair, vcPairAddConst, vcPairAt, vcConstWire3, vcNextParty3, ↓reduceIte, h10, h20]
  · simp only [vcConstPair, vcPairAddConst, vcPairAt, vcConstWire3, vcNextParty3, ↓reduceIte, h20, hz]

private theorem vcSum3_addConst (w : VcWire3) (c : Goldilocks) :
    vcSum3 (vcWireAddConst3 w c) = Goldilocks.add (vcSum3 w) c := by
  unfold vcSum3 vcWireAddConst3
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  simp only [↓reduceIte, h1, h2]
  rw [← goldOfInt_nat (w 0), ← goldOfInt_nat (w 1), ← goldOfInt_nat (w 2), ← goldOfInt_nat c]
  simp only [goldOfInt_add]; congr 1; omega

private theorem vcSum3_constWire (c : Goldilocks) :
    vcSum3 (vcConstWire3 c) = c := by
  unfold vcSum3 vcConstWire3
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  simp only [↓reduceIte, h1, h2]
  rw [← goldOfInt_nat c, ← goldOfInt_nat Goldilocks.zero]
  simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1

/-- Structured per-party gate randomness types for `"QSAG.VC.ZKBOO_R.V1"` PRG expansion. -/
abbrev SboxCoins := Goldilocks × Goldilocks × Goldilocks × Goldilocks

structure ExtRoundCoins where
  s0 : SboxCoins
  s1 : SboxCoins
  s2 : SboxCoins
  s3 : SboxCoins
  s4 : SboxCoins
  s5 : SboxCoins
  s6 : SboxCoins
  s7 : SboxCoins
  s8 : SboxCoins
  s9 : SboxCoins
  s10 : SboxCoins
  s11 : SboxCoins
  deriving DecidableEq, Repr

structure Perm12Coins where
  initExt : Vec ExtRoundCoins poseidon2InitialExtConsts.length
  internal : Vec SboxCoins poseidon2InternalConsts.length
  termExt : Vec ExtRoundCoins poseidon2TerminalExtConsts.length
  deriving DecidableEq

structure Sponge3Coins where
  perm1 : Perm12Coins
  perm2 : Perm12Coins
  perm3 : Perm12Coins
  deriving DecidableEq

structure MerkleLevelCoins where
  boolR : Goldilocks
  sel0R : Goldilocks
  sel1R : Goldilocks
  sel2R : Goldilocks
  sel3R : Goldilocks
  sel4R : Goldilocks
  sel5R : Goldilocks
  hashCoins : Sponge3Coins
  deriving DecidableEq

structure PartyGateCoins (treeDepth : Nat) where
  attrCoins : Sponge3Coins
  presCoins : Sponge3Coins
  scopeCoins : Sponge3Coins
  merkleCoins : Vec MerkleLevelCoins treeDepth
  deriving DecidableEq

/-- Domain tag `"QSAG.VC.ZKBOO_R.V1"` (`blind_vc.rs:259`, 18 bytes) for party PRG tape expansion. -/
def vcZkBooPrgTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x56, 0x43, 0x2E, 0x5A,
   0x4B, 0x42, 0x4F, 0x4F, 0x5F, 0x52, 0x2E, 0x56, 0x31]

/-- Generic context indices are injective even beyond the u64 range. -/
theorem contextIndex204_injective {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)).1

/-- Unbounded counters in the Lean credential tape domain. -/
def vcPrgContext204 (seed : Vec UInt8 32) (rep : Nat) (party : Fin 3) (word : Nat) :
    List (List UInt8) :=
  [seed.toList, leb128 rep, [UInt8.ofNat party.val], leb128 word]

theorem vcPrgContext204_indices {seed : Vec UInt8 32} {party : Fin 3}
    {rep rep' word word' : Nat}
    (h : vcPrgContext204 seed rep party word = vcPrgContext204 seed rep' party word') :
    rep = rep' ∧ word = word' := by
  simp only [vcPrgContext204, List.cons.injEq] at h
  exact ⟨contextIndex204_injective h.2.1, contextIndex204_injective h.2.2.2.1⟩

def vcChallengeContext204 (digest : List UInt8) (rep : Nat) : List (List UInt8) :=
  [digest, leb128 rep]

theorem vcChallengeContext204_index {digest : List UInt8} {a b : Nat}
    (h : vcChallengeContext204 digest a = vcChallengeContext204 digest b) : a = b := by
  simp only [vcChallengeContext204, List.cons.injEq] at h
  exact contextIndex204_injective h.2.1

/-- Counter-mode Goldilocks PRG word stream under `"QSAG.VC.ZKBOO_R.V1"` (`blind_vc.rs:336-350`). -/
def vcPrgStreamAt (repIdx : Nat) (partyIdx : Fin 3) (tapeSeed : Vec UInt8 32) (wordIdx : Nat) : Goldilocks :=
  let blk := cshake256FramedBytes vcZkBooPrgTag
    (vcPrgContext204 tapeSeed repIdx partyIdx wordIdx)
  Goldilocks.ofNat (decodeNatLeBytes (blk.take 8))

private def sampleSboxCoins (st : Nat → Goldilocks) (pos : Nat) : SboxCoins × Nat :=
  ((st pos, st (pos + 1), st (pos + 2), st (pos + 3)), pos + 4)

private def sampleExtRoundCoins (st : Nat → Goldilocks) (pos : Nat) : ExtRoundCoins × Nat :=
  let (s0, p0) := sampleSboxCoins st pos
  let (s1, p1) := sampleSboxCoins st p0
  let (s2, p2) := sampleSboxCoins st p1
  let (s3, p3) := sampleSboxCoins st p2
  let (s4, p4) := sampleSboxCoins st p3
  let (s5, p5) := sampleSboxCoins st p4
  let (s6, p6) := sampleSboxCoins st p5
  let (s7, p7) := sampleSboxCoins st p6
  let (s8, p8) := sampleSboxCoins st p7
  let (s9, p9) := sampleSboxCoins st p8
  let (s10, p10) := sampleSboxCoins st p9
  let (s11, p11) := sampleSboxCoins st p10
  (⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, p11)

private def sampleVecFrom {α : Type} (samp : (Nat → Goldilocks) → Nat → α × Nat)
    (st : Nat → Goldilocks) : (n : Nat) → Nat → Vec α n × Nat
  | 0, pos => (.nil, pos)
  | n + 1, pos =>
    let (h, p1) := samp st pos
    let (t, p2) := sampleVecFrom samp st n p1
    (.cons h t, p2)

private def samplePerm12Coins (st : Nat → Goldilocks) (pos : Nat) : Perm12Coins × Nat :=
  let (c1, p1) := sampleVecFrom sampleExtRoundCoins st poseidon2InitialExtConsts.length pos
  let (c2, p2) := sampleVecFrom sampleSboxCoins st poseidon2InternalConsts.length p1
  let (c3, p3) := sampleVecFrom sampleExtRoundCoins st poseidon2TerminalExtConsts.length p2
  (⟨c1, c2, c3⟩, p3)

private def sampleSponge3Coins (st : Nat → Goldilocks) (pos : Nat) : Sponge3Coins × Nat :=
  let (q1, p1) := samplePerm12Coins st pos
  let (q2, p2) := samplePerm12Coins st p1
  let (q3, p3) := samplePerm12Coins st p2
  (⟨q1, q2, q3⟩, p3)

private def sampleMerkleLevelCoins (st : Nat → Goldilocks) (pos : Nat) : MerkleLevelCoins × Nat :=
  let b := st pos
  let g0 := st (pos + 1); let g1 := st (pos + 2); let g2 := st (pos + 3)
  let g3 := st (pos + 4); let g4 := st (pos + 5); let g5 := st (pos + 6)
  let (hc, pNext) := sampleSponge3Coins st (pos + 7)
  (⟨b, g0, g1, g2, g3, g4, g5, hc⟩, pNext)

/-- Concrete `"QSAG.VC.ZKBOO_R.V1"` party PRG tape expansion (`blind_vc.rs:336-350`). -/
def vcExpandPartyCoins (treeDepth : Nat) (repIdx : Nat) (partyIdx : Fin 3) (tapeSeed : Vec UInt8 32) :
    PartyGateCoins treeDepth :=
  let st := vcPrgStreamAt repIdx partyIdx tapeSeed
  let (ac, p1) := sampleSponge3Coins st 0
  let (pc, p2) := sampleSponge3Coins st p1
  let (sc, p3) := sampleSponge3Coins st p2
  let (mc, _) := sampleVecFrom sampleMerkleLevelCoins st treeDepth p3
  ⟨ac, pc, sc, mc⟩

/-- Expected ZKBoo multiplication share `x_e * y_e + x_e * y_{e+1} + x_{e+1} * y_e + r_e - r_{e+1}`
    (`blind_vc.rs:368-373`). -/
def vcMulExpectedPair (xe xe1 ye ye1 re re1 : Goldilocks) : Goldilocks :=
  let cross := Goldilocks.add (Goldilocks.mul xe ye)
    (Goldilocks.add (Goldilocks.mul xe ye1) (Goldilocks.mul xe1 ye))
  Goldilocks.sub (Goldilocks.add cross re) re1

def vcMulGate3 (a b r : VcWire3) : VcWire3 :=
  fun i => vcMulExpectedPair (a i) (a (vcNextParty3 i)) (b i) (b (vcNextParty3 i)) (r i) (r (vcNextParty3 i))

theorem vcMulGate3_sum (a b r : VcWire3) :
    vcSum3 (vcMulGate3 a b r) = Goldilocks.mul (vcSum3 a) (vcSum3 b) := by
  unfold vcSum3 vcMulGate3 vcMulExpectedPair vcNextParty3
  dsimp only
  rw [← goldOfInt_nat (a 0), ← goldOfInt_nat (a 1), ← goldOfInt_nat (a 2),
      ← goldOfInt_nat (b 0), ← goldOfInt_nat (b 1), ← goldOfInt_nat (b 2),
      ← goldOfInt_nat (r 0), ← goldOfInt_nat (r 1), ← goldOfInt_nat (r 2)]
  simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
  congr 1
  simp only [Int.add_mul, Int.mul_add]
  omega

structure PartyMulView where
  r : Goldilocks
  out : Goldilocks
  deriving DecidableEq, Repr

def pairCheckMul (x y : Goldilocks × Goldilocks) (gE gE1 : PartyMulView) :
    Option (Goldilocks × Goldilocks) :=
  if gE.out = vcMulExpectedPair x.1 x.2 y.1 y.2 gE.r gE1.r then
    some (gE.out, gE1.out)
  else
    none

def honestMulView3 (a b r : VcWire3) : Fin 3 → PartyMulView :=
  fun i => { r := r i, out := vcMulGate3 a b r i }

private theorem pairCheckMul_step {wx wy : VcWire3} {g : Fin 3 → PartyMulView} {e : Fin 3}
    {outP : Goldilocks × Goldilocks}
    (hOk : pairCheckMul (vcPairAt wx e) (vcPairAt wy e) (g e) (g (vcNextParty3 e)) = some outP) :
    outP = vcPairAt (fun i => (g i).out) e ∧
    (g e).out = vcMulGate3 wx wy (fun i => (g i).r) e := by
  unfold pairCheckMul vcPairAt at hOk
  dsimp only at hOk
  if hEq : (g e).out = vcMulExpectedPair (wx e) (wx (vcNextParty3 e)) (wy e) (wy (vcNextParty3 e))
      (g e).r (g (vcNextParty3 e)).r then
    rw [ite_true_of hEq] at hOk
    injection hOk with hPair
    exact ⟨hPair.symm, hEq⟩
  else
    rw [ite_false_of hEq] at hOk; cases hOk

private theorem pairCheckMul_honest (wx wy r : VcWire3) (e : Fin 3) :
    pairCheckMul (vcPairAt wx e) (vcPairAt wy e)
      (honestMulView3 wx wy r e) (honestMulView3 wx wy r (vcNextParty3 e)) =
      some (vcPairAt (vcMulGate3 wx wy r) e) := by
  unfold pairCheckMul honestMulView3 vcPairAt vcMulGate3
  dsimp only
  simp only [↓reduceIte]

private theorem pairCheckMul_extract3 {wx wy : VcWire3} {g : Fin 3 → PartyMulView}
    {o0 o1 o2 : Goldilocks × Goldilocks}
    (h0 : pairCheckMul (vcPairAt wx 0) (vcPairAt wy 0) (g 0) (g 1) = some o0)
    (h1 : pairCheckMul (vcPairAt wx 1) (vcPairAt wy 1) (g 1) (g 2) = some o1)
    (h2 : pairCheckMul (vcPairAt wx 2) (vcPairAt wy 2) (g 2) (g 0) = some o2) :
    vcSum3 (fun i => (g i).out) = Goldilocks.mul (vcSum3 wx) (vcSum3 wy) := by
  have hFun : (fun i => (g i).out) = vcMulGate3 wx wy (fun i => (g i).r) :=
    funext (fin3_all (pairCheckMul_step h0).2 (pairCheckMul_step h1).2 (pairCheckMul_step h2).2)
  rw [hFun, vcMulGate3_sum]

structure PartySboxView where
  g1 : PartyMulView
  g2 : PartyMulView
  g3 : PartyMulView
  g4 : PartyMulView
  deriving DecidableEq, Repr

def extractSboxCoins (sv : PartySboxView) : SboxCoins :=
  (sv.g1.r, sv.g2.r, sv.g3.r, sv.g4.r)

def pairCheckSbox (x : Goldilocks × Goldilocks) (sE sE1 : PartySboxView) :
    Option (Goldilocks × Goldilocks) :=
  match pairCheckMul x x sE.g1 sE1.g1 with
  | none => none
  | some x2 =>
    match pairCheckMul x2 x sE.g2 sE1.g2 with
    | none => none
    | some x3 =>
      match pairCheckMul x2 x2 sE.g3 sE1.g3 with
      | none => none
      | some x4 => pairCheckMul x4 x3 sE.g4 sE1.g4

def honestSboxView3 (wx : VcWire3) (sc : Fin 3 → SboxCoins) : (Fin 3 → PartySboxView) × VcWire3 :=
  let r1 : VcWire3 := fun i => (sc i).1
  let r2 : VcWire3 := fun i => (sc i).2.1
  let r3 : VcWire3 := fun i => (sc i).2.2.1
  let r4 : VcWire3 := fun i => (sc i).2.2.2
  let g1 := honestMulView3 wx wx r1
  let w2 := vcMulGate3 wx wx r1
  let g2 := honestMulView3 w2 wx r2
  let w3 := vcMulGate3 w2 wx r2
  let g3 := honestMulView3 w2 w2 r3
  let w4 := vcMulGate3 w2 w2 r3
  let g4 := honestMulView3 w4 w3 r4
  let w7 := vcMulGate3 w4 w3 r4
  (fun i => ⟨g1 i, g2 i, g3 i, g4 i⟩, w7)

private theorem extractSboxCoins_honest (wx : VcWire3) (sc : Fin 3 → SboxCoins) (i : Fin 3) :
    extractSboxCoins ((honestSboxView3 wx sc).1 i) = sc i := rfl

private theorem honestSboxView3_sum (wx : VcWire3) (sc : Fin 3 → SboxCoins) :
    vcSum3 (honestSboxView3 wx sc).2 = sbox7 (vcSum3 wx) := by
  unfold honestSboxView3 sbox7
  dsimp only
  simp only [vcMulGate3_sum]
  have hComm : ∀ u v : Goldilocks, Goldilocks.mul u v = Goldilocks.mul v u := fun u v => by
    rw [← goldOfInt_nat u, ← goldOfInt_nat v]
    simp only [goldOfInt_mul]; congr 1; exact Int.mul_comm _ _
  exact hComm _ _

private theorem pairCheckSbox_honest (wx : VcWire3) (sc : Fin 3 → SboxCoins) (e : Fin 3) :
    pairCheckSbox (vcPairAt wx e) ((honestSboxView3 wx sc).1 e) ((honestSboxView3 wx sc).1 (vcNextParty3 e)) =
      some (vcPairAt (honestSboxView3 wx sc).2 e) := by
  unfold pairCheckSbox honestSboxView3
  dsimp only
  rw [pairCheckMul_honest]; dsimp only
  rw [pairCheckMul_honest]; dsimp only
  rw [pairCheckMul_honest]; dsimp only
  rw [pairCheckMul_honest]

private theorem pairCheckSbox_step {wx : VcWire3} {sv : Fin 3 → PartySboxView} {e : Fin 3}
    {outP : Goldilocks × Goldilocks}
    (hOk : pairCheckSbox (vcPairAt wx e) (sv e) (sv (vcNextParty3 e)) = some outP) :
    outP = vcPairAt (fun i => (sv i).g4.out) e ∧
    pairCheckMul (vcPairAt wx e) (vcPairAt wx e) (sv e).g1 (sv (vcNextParty3 e)).g1 =
      some (vcPairAt (fun i => (sv i).g1.out) e) ∧
    pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt wx e) (sv e).g2 (sv (vcNextParty3 e)).g2 =
      some (vcPairAt (fun i => (sv i).g2.out) e) ∧
    pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt (fun i => (sv i).g1.out) e)
      (sv e).g3 (sv (vcNextParty3 e)).g3 = some (vcPairAt (fun i => (sv i).g3.out) e) ∧
    pairCheckMul (vcPairAt (fun i => (sv i).g3.out) e) (vcPairAt (fun i => (sv i).g2.out) e)
      (sv e).g4 (sv (vcNextParty3 e)).g4 = some (vcPairAt (fun i => (sv i).g4.out) e) := by
  unfold pairCheckSbox at hOk
  cases hm1 : pairCheckMul (vcPairAt wx e) (vcPairAt wx e) (sv e).g1 (sv (vcNextParty3 e)).g1 with
  | none => rw [hm1] at hOk; cases hOk
  | some x2 =>
    rw [hm1] at hOk; dsimp only at hOk
    obtain ⟨hx2, _⟩ := pairCheckMul_step (g := fun i => (sv i).g1) hm1
    subst hx2
    cases hm2 : pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt wx e)
        (sv e).g2 (sv (vcNextParty3 e)).g2 with
    | none => rw [hm2] at hOk; cases hOk
    | some x3 =>
      rw [hm2] at hOk; dsimp only at hOk
      obtain ⟨hx3, _⟩ := pairCheckMul_step (g := fun i => (sv i).g2) hm2
      subst hx3
      cases hm3 : pairCheckMul (vcPairAt (fun i => (sv i).g1.out) e) (vcPairAt (fun i => (sv i).g1.out) e)
          (sv e).g3 (sv (vcNextParty3 e)).g3 with
      | none => rw [hm3] at hOk; cases hOk
      | some x4 =>
        rw [hm3] at hOk; dsimp only at hOk
        obtain ⟨hx4, _⟩ := pairCheckMul_step (g := fun i => (sv i).g3) hm3
        subst hx4
        obtain ⟨hx7, _⟩ := pairCheckMul_step (g := fun i => (sv i).g4) hOk
        subst hx7
        exact ⟨rfl, rfl, rfl, rfl, hOk⟩

private theorem pairCheckSbox_extract3 {wx : VcWire3} {sv : Fin 3 → PartySboxView}
    {o0 o1 o2 : Goldilocks × Goldilocks}
    (h0 : pairCheckSbox (vcPairAt wx 0) (sv 0) (sv 1) = some o0)
    (h1 : pairCheckSbox (vcPairAt wx 1) (sv 1) (sv 2) = some o1)
    (h2 : pairCheckSbox (vcPairAt wx 2) (sv 2) (sv 0) = some o2) :
    vcSum3 (fun i => (sv i).g4.out) = sbox7 (vcSum3 wx) := by
  obtain ⟨_, m10, m20, m30, m40⟩ := pairCheckSbox_step h0
  obtain ⟨_, m11, m21, m31, m41⟩ := pairCheckSbox_step h1
  obtain ⟨_, m12, m22, m32, m42⟩ := pairCheckSbox_step h2
  dsimp only [vcNextParty3] at m10 m20 m30 m40 m11 m21 m31 m41 m12 m22 m32 m42
  have s1 := pairCheckMul_extract3 (g := fun i => (sv i).g1) m10 m11 m12
  have s2 := pairCheckMul_extract3 (g := fun i => (sv i).g2) m20 m21 m22
  have s3 := pairCheckMul_extract3 (g := fun i => (sv i).g3) m30 m31 m32
  have s4 := pairCheckMul_extract3 (g := fun i => (sv i).g4) m40 m41 m42
  unfold sbox7
  dsimp only
  rw [s4, s3, s2, s1]
  have hComm : ∀ u v : Goldilocks, Goldilocks.mul u v = Goldilocks.mul v u := fun u v => by
    rw [← goldOfInt_nat u, ← goldOfInt_nat v]
    simp only [goldOfInt_mul]; congr 1; exact Int.mul_comm _ _
  exact hComm _ _

structure PartyExtRoundView where
  s0 : PartySboxView
  s1 : PartySboxView
  s2 : PartySboxView
  s3 : PartySboxView
  s4 : PartySboxView
  s5 : PartySboxView
  s6 : PartySboxView
  s7 : PartySboxView
  s8 : PartySboxView
  s9 : PartySboxView
  s10 : PartySboxView
  s11 : PartySboxView
  deriving DecidableEq, Repr

def extractExtRoundCoins (rv : PartyExtRoundView) : ExtRoundCoins :=
  ⟨extractSboxCoins rv.s0, extractSboxCoins rv.s1, extractSboxCoins rv.s2, extractSboxCoins rv.s3,
   extractSboxCoins rv.s4, extractSboxCoins rv.s5, extractSboxCoins rv.s6, extractSboxCoins rv.s7,
   extractSboxCoins rv.s8, extractSboxCoins rv.s9, extractSboxCoins rv.s10, extractSboxCoins rv.s11⟩

def pairCheckExtRound (e : Fin 3) (rc : Poseidon2State12)
    (vE vE1 : PartyExtRoundView) (st : Poseidon2State12 × Poseidon2State12) :
    Option (Poseidon2State12 × Poseidon2State12) :=
  let chk (f : Poseidon2State12 → Goldilocks) (sE sE1 : PartySboxView) :=
    pairCheckSbox (vcPairAddConst e (f st.1, f st.2) (f rc)) sE sE1
  match chk (·.b0.x0) vE.s0 vE1.s0, chk (·.b0.x1) vE.s1 vE1.s1,
        chk (·.b0.x2) vE.s2 vE1.s2, chk (·.b0.x3) vE.s3 vE1.s3,
        chk (·.b1.x0) vE.s4 vE1.s4, chk (·.b1.x1) vE.s5 vE1.s5,
        chk (·.b1.x2) vE.s6 vE1.s6, chk (·.b1.x3) vE.s7 vE1.s7,
        chk (·.b2.x0) vE.s8 vE1.s8, chk (·.b2.x1) vE.s9 vE1.s9,
        chk (·.b2.x2) vE.s10 vE1.s10, chk (·.b2.x3) vE.s11 vE1.s11 with
  | some y0, some y1, some y2, some y3, some y4, some y5,
    some y6, some y7, some y8, some y9, some y10, some y11 =>
    some (applyME ⟨⟨y0.1, y1.1, y2.1, y3.1⟩, ⟨y4.1, y5.1, y6.1, y7.1⟩, ⟨y8.1, y9.1, y10.1, y11.1⟩⟩,
          applyME ⟨⟨y0.2, y1.2, y2.2, y3.2⟩, ⟨y4.2, y5.2, y6.2, y7.2⟩, ⟨y8.2, y9.2, y10.2, y11.2⟩⟩)
  | _, _, _, _, _, _, _, _, _, _, _, _ => none

def vcExtRoundOut3 (rv : Fin 3 → PartyExtRoundView) : VcState12_3 :=
  fun i =>
    applyME ⟨⟨(rv i).s0.g4.out, (rv i).s1.g4.out, (rv i).s2.g4.out, (rv i).s3.g4.out⟩,
             ⟨(rv i).s4.g4.out, (rv i).s5.g4.out, (rv i).s6.g4.out, (rv i).s7.g4.out⟩,
             ⟨(rv i).s8.g4.out, (rv i).s9.g4.out, (rv i).s10.g4.out, (rv i).s11.g4.out⟩⟩

def honestExtRound3 (rc : Poseidon2State12) (st : VcState12_3) (ec : Fin 3 → ExtRoundCoins) :
    (Fin 3 → PartyExtRoundView) × VcState12_3 :=
  let mk (f : Poseidon2State12 → Goldilocks) (sel : ExtRoundCoins → SboxCoins) :=
    honestSboxView3 (vcWireAddConst3 (fun i => f (st i)) (f rc)) (fun i => sel (ec i))
  let r0 := mk (·.b0.x0) (·.s0); let r1 := mk (·.b0.x1) (·.s1)
  let r2 := mk (·.b0.x2) (·.s2); let r3 := mk (·.b0.x3) (·.s3)
  let r4 := mk (·.b1.x0) (·.s4); let r5 := mk (·.b1.x1) (·.s5)
  let r6 := mk (·.b1.x2) (·.s6); let r7 := mk (·.b1.x3) (·.s7)
  let r8 := mk (·.b2.x0) (·.s8); let r9 := mk (·.b2.x1) (·.s9)
  let r10 := mk (·.b2.x2) (·.s10); let r11 := mk (·.b2.x3) (·.s11)
  let rv : Fin 3 → PartyExtRoundView := fun i =>
    ⟨r0.1 i, r1.1 i, r2.1 i, r3.1 i, r4.1 i, r5.1 i,
     r6.1 i, r7.1 i, r8.1 i, r9.1 i, r10.1 i, r11.1 i⟩
  (rv, vcExtRoundOut3 rv)

private theorem extractExtRoundCoins_honest (rc : Poseidon2State12) (st : VcState12_3)
    (ec : Fin 3 → ExtRoundCoins) (i : Fin 3) :
    extractExtRoundCoins ((honestExtRound3 rc st ec).1 i) = ec i := rfl

private theorem pairCheckExtRound_honest (rc : Poseidon2State12) (st : VcState12_3)
    (ec : Fin 3 → ExtRoundCoins) (e : Fin 3) :
    pairCheckExtRound e rc ((honestExtRound3 rc st ec).1 e) ((honestExtRound3 rc st ec).1 (vcNextParty3 e))
      (vcPairAtState12 st e) = some (vcPairAtState12 (honestExtRound3 rc st ec).2 e) := by
  unfold pairCheckExtRound honestExtRound3 vcPairAtState12 vcExtRoundOut3
  dsimp only
  have hAt : ∀ f : Poseidon2State12 → Goldilocks,
      vcPairAddConst e (f (st e), f (st (vcNextParty3 e))) (f rc) =
        vcPairAt (vcWireAddConst3 (fun i => f (st i)) (f rc)) e :=
    fun f => vcPairAddConst_spec (fun i => f (st i)) (f rc) e
  rw [hAt (·.b0.x0), hAt (·.b0.x1), hAt (·.b0.x2), hAt (·.b0.x3),
      hAt (·.b1.x0), hAt (·.b1.x1), hAt (·.b1.x2), hAt (·.b1.x3),
      hAt (·.b2.x0), hAt (·.b2.x1), hAt (·.b2.x2), hAt (·.b2.x3),
      pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest,
      pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest,
      pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest, pairCheckSbox_honest]
  rfl

private theorem pairCheckExtRound_step {rc : Poseidon2State12} {st : VcState12_3}
    {rv : Fin 3 → PartyExtRoundView} {e : Fin 3} {outSt : Poseidon2State12 × Poseidon2State12}
    (hOk : pairCheckExtRound e rc (rv e) (rv (vcNextParty3 e)) (vcPairAtState12 st e) = some outSt) :
    outSt = vcPairAtState12 (vcExtRoundOut3 rv) e ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc.b0.x0) e) (rv e).s0 (rv (vcNextParty3 e)).s0 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x1) rc.b0.x1) e) (rv e).s1 (rv (vcNextParty3 e)).s1 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x2) rc.b0.x2) e) (rv e).s2 (rv (vcNextParty3 e)).s2 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x3) rc.b0.x3) e) (rv e).s3 (rv (vcNextParty3 e)).s3 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x0) rc.b1.x0) e) (rv e).s4 (rv (vcNextParty3 e)).s4 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x1) rc.b1.x1) e) (rv e).s5 (rv (vcNextParty3 e)).s5 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x2) rc.b1.x2) e) (rv e).s6 (rv (vcNextParty3 e)).s6 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x3) rc.b1.x3) e) (rv e).s7 (rv (vcNextParty3 e)).s7 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x0) rc.b2.x0) e) (rv e).s8 (rv (vcNextParty3 e)).s8 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x1) rc.b2.x1) e) (rv e).s9 (rv (vcNextParty3 e)).s9 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x2) rc.b2.x2) e) (rv e).s10 (rv (vcNextParty3 e)).s10 = some o) ∧
    (∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x3) rc.b2.x3) e) (rv e).s11 (rv (vcNextParty3 e)).s11 = some o) := by
  unfold pairCheckExtRound vcPairAtState12 at hOk
  dsimp only at hOk
  have hAt : ∀ f : Poseidon2State12 → Goldilocks,
      vcPairAddConst e (f (st e), f (st (vcNextParty3 e))) (f rc) =
        vcPairAt (vcWireAddConst3 (fun i => f (st i)) (f rc)) e :=
    fun f => vcPairAddConst_spec (fun i => f (st i)) (f rc) e
  rw [hAt (·.b0.x0), hAt (·.b0.x1), hAt (·.b0.x2), hAt (·.b0.x3),
      hAt (·.b1.x0), hAt (·.b1.x1), hAt (·.b1.x2), hAt (·.b1.x3),
      hAt (·.b2.x0), hAt (·.b2.x1), hAt (·.b2.x2), hAt (·.b2.x3)] at hOk
  cases hs0 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc.b0.x0) e) (rv e).s0 (rv (vcNextParty3 e)).s0 with
  | none => rw [hs0] at hOk; cases hOk
  | some y0 =>
  cases hs1 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x1) rc.b0.x1) e) (rv e).s1 (rv (vcNextParty3 e)).s1 with
  | none => rw [hs0, hs1] at hOk; cases hOk
  | some y1 =>
  cases hs2 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x2) rc.b0.x2) e) (rv e).s2 (rv (vcNextParty3 e)).s2 with
  | none => rw [hs0, hs1, hs2] at hOk; cases hOk
  | some y2 =>
  cases hs3 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x3) rc.b0.x3) e) (rv e).s3 (rv (vcNextParty3 e)).s3 with
  | none => rw [hs0, hs1, hs2, hs3] at hOk; cases hOk
  | some y3 =>
  cases hs4 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x0) rc.b1.x0) e) (rv e).s4 (rv (vcNextParty3 e)).s4 with
  | none => rw [hs0, hs1, hs2, hs3, hs4] at hOk; cases hOk
  | some y4 =>
  cases hs5 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x1) rc.b1.x1) e) (rv e).s5 (rv (vcNextParty3 e)).s5 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5] at hOk; cases hOk
  | some y5 =>
  cases hs6 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x2) rc.b1.x2) e) (rv e).s6 (rv (vcNextParty3 e)).s6 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6] at hOk; cases hOk
  | some y6 =>
  cases hs7 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b1.x3) rc.b1.x3) e) (rv e).s7 (rv (vcNextParty3 e)).s7 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at hOk; cases hOk
  | some y7 =>
  cases hs8 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x0) rc.b2.x0) e) (rv e).s8 (rv (vcNextParty3 e)).s8 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at hOk; cases hOk
  | some y8 =>
  cases hs9 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x1) rc.b2.x1) e) (rv e).s9 (rv (vcNextParty3 e)).s9 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at hOk; cases hOk
  | some y9 =>
  cases hs10 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x2) rc.b2.x2) e) (rv e).s10 (rv (vcNextParty3 e)).s10 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10] at hOk; cases hOk
  | some y10 =>
  cases hs11 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b2.x3) rc.b2.x3) e) (rv e).s11 (rv (vcNextParty3 e)).s11 with
  | none => rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at hOk; cases hOk
  | some y11 =>
    rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at hOk
    injection hOk with hPair
    rw [(pairCheckSbox_step (sv := fun i => (rv i).s0) hs0).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s1) hs1).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s2) hs2).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s3) hs3).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s4) hs4).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s5) hs5).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s6) hs6).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s7) hs7).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s8) hs8).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s9) hs9).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s10) hs10).1,
        (pairCheckSbox_step (sv := fun i => (rv i).s11) hs11).1] at hPair
    exact ⟨hPair.symm, ⟨y0, rfl⟩, ⟨y1, rfl⟩, ⟨y2, rfl⟩, ⟨y3, rfl⟩, ⟨y4, rfl⟩, ⟨y5, rfl⟩,
      ⟨y6, rfl⟩, ⟨y7, rfl⟩, ⟨y8, rfl⟩, ⟨y9, rfl⟩, ⟨y10, rfl⟩, ⟨y11, rfl⟩⟩

private theorem vcSumState12_3_applyME (f : VcState12_3) :
    vcSumState12_3 (fun i => applyME (f i)) = applyME (vcSumState12_3 f) := by
  unfold vcSumState12_3
  rw [← applyME_add, ← applyME_add]

private theorem vcSumState12_3_applyMI (f : VcState12_3) :
    vcSumState12_3 (fun i => applyMI (f i)) = applyMI (vcSumState12_3 f) := by
  unfold vcSumState12_3
  rw [← applyMI_add, ← applyMI_add]

private theorem pairCheckExtRound_extract3 {rc : Poseidon2State12} {st : VcState12_3}
    {rv : Fin 3 → PartyExtRoundView} {o0 o1 o2 : Poseidon2State12 × Poseidon2State12}
    (h0 : pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) = some o0)
    (h1 : pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) = some o1)
    (h2 : pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) = some o2) :
    vcSumState12_3 (vcExtRoundOut3 rv) = externalRound rc (vcSumState12_3 st) := by
  obtain ⟨_, ⟨_, a0⟩, ⟨_, a1⟩, ⟨_, a2⟩, ⟨_, a3⟩, ⟨_, a4⟩, ⟨_, a5⟩,
             ⟨_, a6⟩, ⟨_, a7⟩, ⟨_, a8⟩, ⟨_, a9⟩, ⟨_, a10⟩, ⟨_, a11⟩⟩ := pairCheckExtRound_step h0
  obtain ⟨_, ⟨_, b0⟩, ⟨_, b1⟩, ⟨_, b2⟩, ⟨_, b3⟩, ⟨_, b4⟩, ⟨_, b5⟩,
             ⟨_, b6⟩, ⟨_, b7⟩, ⟨_, b8⟩, ⟨_, b9⟩, ⟨_, b10⟩, ⟨_, b11⟩⟩ := pairCheckExtRound_step h1
  obtain ⟨_, ⟨_, c0⟩, ⟨_, c1⟩, ⟨_, c2⟩, ⟨_, c3⟩, ⟨_, c4⟩, ⟨_, c5⟩,
             ⟨_, c6⟩, ⟨_, c7⟩, ⟨_, c8⟩, ⟨_, c9⟩, ⟨_, c10⟩, ⟨_, c11⟩⟩ := pairCheckExtRound_step h2
  dsimp only [vcNextParty3] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  dsimp only [vcNextParty3] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  dsimp only [vcNextParty3] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
  unfold vcExtRoundOut3
  rw [vcSumState12_3_applyME, externalRound_eq]
  congr 1
  rw [vcSumState12_3_lanes, sboxState12_eq, state12Add_eq, vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq, lane4Add_eq]
  rw [pairCheckSbox_extract3 (sv := fun i => (rv i).s0) a0 b0 c0,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s1) a1 b1 c1,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s2) a2 b2 c2,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s3) a3 b3 c3,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s4) a4 b4 c4,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s5) a5 b5 c5,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s6) a6 b6 c6,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s7) a7 b7 c7,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s8) a8 b8 c8,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s9) a9 b9 c9,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s10) a10 b10 c10,
      pairCheckSbox_extract3 (sv := fun i => (rv i).s11) a11 b11 c11]
  simp only [vcSum3_addConst]

def pairCheckIntRound (e : Fin 3) (rc : Goldilocks)
    (vE vE1 : PartySboxView) (st : Poseidon2State12 × Poseidon2State12) :
    Option (Poseidon2State12 × Poseidon2State12) :=
  match pairCheckSbox (vcPairAddConst e (st.1.b0.x0, st.2.b0.x0) rc) vE vE1 with
  | none => none
  | some y0 =>
    some (applyMI ⟨⟨y0.1, st.1.b0.x1, st.1.b0.x2, st.1.b0.x3⟩, st.1.b1, st.1.b2⟩,
          applyMI ⟨⟨y0.2, st.2.b0.x1, st.2.b0.x2, st.2.b0.x3⟩, st.2.b1, st.2.b2⟩)

def vcIntRoundOut3 (st : VcState12_3) (sv : Fin 3 → PartySboxView) : VcState12_3 :=
  fun i => applyMI ⟨⟨(sv i).g4.out, (st i).b0.x1, (st i).b0.x2, (st i).b0.x3⟩, (st i).b1, (st i).b2⟩

def honestIntRound3 (rc : Goldilocks) (st : VcState12_3) (sc : Fin 3 → SboxCoins) :
    (Fin 3 → PartySboxView) × VcState12_3 :=
  let r0 := honestSboxView3 (vcWireAddConst3 (fun i => (st i).b0.x0) rc) sc
  (r0.1, vcIntRoundOut3 st r0.1)

private theorem pairCheckIntRound_honest (rc : Goldilocks) (st : VcState12_3)
    (sc : Fin 3 → SboxCoins) (e : Fin 3) :
    pairCheckIntRound e rc ((honestIntRound3 rc st sc).1 e) ((honestIntRound3 rc st sc).1 (vcNextParty3 e))
      (vcPairAtState12 st e) = some (vcPairAtState12 (honestIntRound3 rc st sc).2 e) := by
  unfold pairCheckIntRound honestIntRound3 vcPairAtState12 vcIntRoundOut3
  dsimp only
  have hAdd : vcPairAddConst e ((st e).b0.x0, (st (vcNextParty3 e)).b0.x0) rc =
      vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e :=
    vcPairAddConst_spec (fun i => (st i).b0.x0) rc e
  rw [hAdd, pairCheckSbox_honest]
  rfl

private theorem pairCheckIntRound_step {rc : Goldilocks} {st : VcState12_3}
    {sv : Fin 3 → PartySboxView} {e : Fin 3} {outSt : Poseidon2State12 × Poseidon2State12}
    (hOk : pairCheckIntRound e rc (sv e) (sv (vcNextParty3 e)) (vcPairAtState12 st e) = some outSt) :
    outSt = vcPairAtState12 (vcIntRoundOut3 st sv) e ∧
    ∃ o, pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e) (sv e) (sv (vcNextParty3 e)) = some o := by
  unfold pairCheckIntRound vcPairAtState12 at hOk
  dsimp only at hOk
  have hAdd : vcPairAddConst e ((st e).b0.x0, (st (vcNextParty3 e)).b0.x0) rc =
      vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e :=
    vcPairAddConst_spec (fun i => (st i).b0.x0) rc e
  rw [hAdd] at hOk
  cases hs0 : pairCheckSbox (vcPairAt (vcWireAddConst3 (fun i => (st i).b0.x0) rc) e) (sv e) (sv (vcNextParty3 e)) with
  | none => rw [hs0] at hOk; cases hOk
  | some y0 =>
    rw [hs0] at hOk
    injection hOk with hPair
    rw [(pairCheckSbox_step hs0).1] at hPair
    exact ⟨hPair.symm, ⟨y0, rfl⟩⟩

private theorem pairCheckIntRound_extract3 {rc : Goldilocks} {st : VcState12_3}
    {sv : Fin 3 → PartySboxView} {o0 o1 o2 : Poseidon2State12 × Poseidon2State12}
    (h0 : pairCheckIntRound 0 rc (sv 0) (sv 1) (vcPairAtState12 st 0) = some o0)
    (h1 : pairCheckIntRound 1 rc (sv 1) (sv 2) (vcPairAtState12 st 1) = some o1)
    (h2 : pairCheckIntRound 2 rc (sv 2) (sv 0) (vcPairAtState12 st 2) = some o2) :
    vcSumState12_3 (vcIntRoundOut3 st sv) = internalRound rc (vcSumState12_3 st) := by
  obtain ⟨_, ⟨_, a0⟩⟩ := pairCheckIntRound_step h0
  obtain ⟨_, ⟨_, b0⟩⟩ := pairCheckIntRound_step h1
  obtain ⟨_, ⟨_, c0⟩⟩ := pairCheckIntRound_step h2
  dsimp only [vcNextParty3] at a0 b0 c0
  unfold vcIntRoundOut3
  rw [vcSumState12_3_applyMI, internalRound_eq]
  congr 1
  rw [vcSumState12_3_lanes, vcSumState12_3_lanes]
  simp only [vcSumLane4_3_eq]
  rw [pairCheckSbox_extract3 a0 b0 c0, vcSum3_addConst]

def pairCheckExtRounds (e : Fin 3) :
    List Poseidon2State12 → List PartyExtRoundView → List PartyExtRoundView →
    Poseidon2State12 × Poseidon2State12 → Option (Poseidon2State12 × Poseidon2State12)
  | [], [], [], st => some st
  | rc :: rcs, vE :: vsE, vE1 :: vsE1, st =>
    match pairCheckExtRound e rc vE vE1 st with
    | none => none
    | some st' => pairCheckExtRounds e rcs vsE vsE1 st'
  | _, _, _, _ => none

def pairCheckIntRounds (e : Fin 3) :
    List Goldilocks → List PartySboxView → List PartySboxView →
    Poseidon2State12 × Poseidon2State12 → Option (Poseidon2State12 × Poseidon2State12)
  | [], [], [], st => some st
  | rc :: rcs, vE :: vsE, vE1 :: vsE1, st =>
    match pairCheckIntRound e rc vE vE1 st with
    | none => none
    | some st' => pairCheckIntRounds e rcs vsE vsE1 st'
  | _, _, _, _ => none

def honestExtRounds3 :
    (rcs : List Poseidon2State12) → VcState12_3 → (Fin 3 → Vec ExtRoundCoins rcs.length) →
    (Fin 3 → List PartyExtRoundView) × VcState12_3
  | [], st, _ => (fun _ => [], st)
  | rc :: rcs, st, cs =>
    let rHead := honestExtRound3 rc st (fun i => (cs i).head)
    let rTail := honestExtRounds3 rcs rHead.2 (fun i => (cs i).tail)
    (fun i => rHead.1 i :: rTail.1 i, rTail.2)

def honestIntRounds3 :
    (rcs : List Goldilocks) → VcState12_3 → (Fin 3 → Vec SboxCoins rcs.length) →
    (Fin 3 → List PartySboxView) × VcState12_3
  | [], st, _ => (fun _ => [], st)
  | rc :: rcs, st, cs =>
    let rHead := honestIntRound3 rc st (fun i => (cs i).head)
    let rTail := honestIntRounds3 rcs rHead.2 (fun i => (cs i).tail)
    (fun i => rHead.1 i :: rTail.1 i, rTail.2)

def extractExtRoundsCoins :
    (rcs : List Poseidon2State12) → List PartyExtRoundView → Option (Vec ExtRoundCoins rcs.length)
  | [], [] => some .nil
  | _ :: rcs, v :: vsl => (extractExtRoundsCoins rcs vsl).map (Vec.cons (extractExtRoundCoins v))
  | _, _ => none

def extractIntRoundsCoins :
    (rcs : List Goldilocks) → List PartySboxView → Option (Vec SboxCoins rcs.length)
  | [], [] => some .nil
  | _ :: rcs, v :: vsl => (extractIntRoundsCoins rcs vsl).map (Vec.cons (extractSboxCoins v))
  | _, _ => none

private theorem extractExtRoundsCoins_honest :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3) (cs : Fin 3 → Vec ExtRoundCoins rcs.length) (i : Fin 3),
      extractExtRoundsCoins rcs ((honestExtRounds3 rcs st cs).1 i) = some (cs i)
  | [], _, cs, i => by cases cs i; rfl
  | rc :: rcs, st, cs, i => by
    dsimp only [honestExtRounds3, extractExtRoundsCoins]
    rw [extractExtRoundsCoins_honest rcs (honestExtRound3 rc st (fun j => (cs j).head)).2 (fun j => (cs j).tail) i]
    dsimp only [Option.map]
    rw [extractExtRoundCoins_honest, Vec.eta_cons]

private theorem extractIntRoundsCoins_honest :
    ∀ (rcs : List Goldilocks) (st : VcState12_3) (cs : Fin 3 → Vec SboxCoins rcs.length) (i : Fin 3),
      extractIntRoundsCoins rcs ((honestIntRounds3 rcs st cs).1 i) = some (cs i)
  | [], _, cs, i => by cases cs i; rfl
  | rc :: rcs, st, cs, i => by
    dsimp only [honestIntRounds3, extractIntRoundsCoins]
    rw [extractIntRoundsCoins_honest rcs (honestIntRound3 rc st (fun j => (cs j).head)).2 (fun j => (cs j).tail) i]
    dsimp only [Option.map]
    change some (Vec.cons (cs i).head (cs i).tail) = some (cs i)
    rw [Vec.eta_cons]

private theorem pairCheckExtRounds_honest :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3) (cs : Fin 3 → Vec ExtRoundCoins rcs.length) (e : Fin 3),
      pairCheckExtRounds e rcs ((honestExtRounds3 rcs st cs).1 e)
        ((honestExtRounds3 rcs st cs).1 (vcNextParty3 e)) (vcPairAtState12 st e) =
        some (vcPairAtState12 (honestExtRounds3 rcs st cs).2 e)
  | [], _, _, _ => rfl
  | rc :: rcs, st, cs, e => by
    dsimp only [honestExtRounds3, pairCheckExtRounds]
    rw [pairCheckExtRound_honest]
    exact pairCheckExtRounds_honest rcs (honestExtRound3 rc st (fun i => (cs i).head)).2 (fun i => (cs i).tail) e

private theorem pairCheckIntRounds_honest :
    ∀ (rcs : List Goldilocks) (st : VcState12_3) (cs : Fin 3 → Vec SboxCoins rcs.length) (e : Fin 3),
      pairCheckIntRounds e rcs ((honestIntRounds3 rcs st cs).1 e)
        ((honestIntRounds3 rcs st cs).1 (vcNextParty3 e)) (vcPairAtState12 st e) =
        some (vcPairAtState12 (honestIntRounds3 rcs st cs).2 e)
  | [], _, _, _ => rfl
  | rc :: rcs, st, cs, e => by
    dsimp only [honestIntRounds3, pairCheckIntRounds]
    rw [pairCheckIntRound_honest]
    exact pairCheckIntRounds_honest rcs (honestIntRound3 rc st (fun i => (cs i).head)).2 (fun i => (cs i).tail) e

private theorem pairCheckExtRounds_extract3 :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3) (vsl : Fin 3 → List PartyExtRoundView)
      {o0 o1 o2 : Poseidon2State12 × Poseidon2State12},
      pairCheckExtRounds 0 rcs (vsl 0) (vsl 1) (vcPairAtState12 st 0) = some o0 →
      pairCheckExtRounds 1 rcs (vsl 1) (vsl 2) (vcPairAtState12 st 1) = some o1 →
      pairCheckExtRounds 2 rcs (vsl 2) (vsl 0) (vcPairAtState12 st 2) = some o2 →
      ∃ stOut : VcState12_3,
        o0 = vcPairAtState12 stOut 0 ∧
        o1 = vcPairAtState12 stOut 1 ∧
        o2 = vcPairAtState12 stOut 2 ∧
        vcSumState12_3 stOut = runRounds externalRound rcs (vcSumState12_3 st)
  | [], st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | cons _ _ => rw [hv0] at h0; cases h0
    | nil =>
      cases hv1 : vsl 1 with
      | cons _ _ => rw [hv0, hv1] at h0; cases h0
      | nil =>
        cases hv2 : vsl 2 with
        | cons _ _ => rw [hv1, hv2] at h1; cases h1
        | nil =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckExtRounds] at h0 h1 h2
          injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
          rw [runRounds_nil]
          exact ⟨st, ho0.symm, ho1.symm, ho2.symm, rfl⟩
  | rc :: rcs, st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | nil => rw [hv0] at h0; cases h0
    | cons r0 rs0 =>
      cases hv1 : vsl 1 with
      | nil => rw [hv0, hv1] at h0; cases h0
      | cons r1 rs1 =>
        cases hv2 : vsl 2 with
        | nil => rw [hv1, hv2] at h1; cases h1
        | cons r2 rs2 =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckExtRounds] at h0 h1 h2
          let rv : Fin 3 → PartyExtRoundView := fun | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2
          let rs : Fin 3 → List PartyExtRoundView := fun | ⟨0, _⟩ => rs0 | ⟨1, _⟩ => rs1 | ⟨2, _⟩ => rs2
          cases hm0 : pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with
          | none => change (match pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => _) = some o0 at h0; rw [hm0] at h0; cases h0
          | some m0 =>
            cases hm1 : pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with
            | none => change (match pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => _) = some o1 at h1; rw [hm1] at h1; cases h1
            | some m1 =>
              cases hm2 : pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with
              | none => change (match pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => _) = some o2 at h2; rw [hm2] at h2; cases h2
              | some m2 =>
                change (match pairCheckExtRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => pairCheckExtRounds 0 rcs (rs 0) (rs 1) st') = some o0 at h0
                change (match pairCheckExtRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => pairCheckExtRounds 1 rcs (rs 1) (rs 2) st') = some o1 at h1
                change (match pairCheckExtRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => pairCheckExtRounds 2 rcs (rs 2) (rs 0) st') = some o2 at h2
                rw [hm0] at h0; rw [hm1] at h1; rw [hm2] at h2
                rw [(pairCheckExtRound_step hm0).1] at h0
                rw [(pairCheckExtRound_step hm1).1] at h1
                rw [(pairCheckExtRound_step hm2).1] at h2
                obtain ⟨stOut, e0, e1, e2, hSum⟩ :=
                  pairCheckExtRounds_extract3 rcs (vcExtRoundOut3 rv) rs h0 h1 h2
                rw [runRounds_cons, ← pairCheckExtRound_extract3 hm0 hm1 hm2]
                exact ⟨stOut, e0, e1, e2, hSum⟩

private theorem pairCheckIntRounds_extract3 :
    ∀ (rcs : List Goldilocks) (st : VcState12_3) (vsl : Fin 3 → List PartySboxView)
      {o0 o1 o2 : Poseidon2State12 × Poseidon2State12},
      pairCheckIntRounds 0 rcs (vsl 0) (vsl 1) (vcPairAtState12 st 0) = some o0 →
      pairCheckIntRounds 1 rcs (vsl 1) (vsl 2) (vcPairAtState12 st 1) = some o1 →
      pairCheckIntRounds 2 rcs (vsl 2) (vsl 0) (vcPairAtState12 st 2) = some o2 →
      ∃ stOut : VcState12_3,
        o0 = vcPairAtState12 stOut 0 ∧
        o1 = vcPairAtState12 stOut 1 ∧
        o2 = vcPairAtState12 stOut 2 ∧
        vcSumState12_3 stOut = runRounds internalRound rcs (vcSumState12_3 st)
  | [], st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | cons _ _ => rw [hv0] at h0; cases h0
    | nil =>
      cases hv1 : vsl 1 with
      | cons _ _ => rw [hv0, hv1] at h0; cases h0
      | nil =>
        cases hv2 : vsl 2 with
        | cons _ _ => rw [hv1, hv2] at h1; cases h1
        | nil =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckIntRounds] at h0 h1 h2
          injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
          rw [runRounds_nil]
          exact ⟨st, ho0.symm, ho1.symm, ho2.symm, rfl⟩
  | rc :: rcs, st, vsl, o0, o1, o2, h0, h1, h2 => by
    cases hv0 : vsl 0 with
    | nil => rw [hv0] at h0; cases h0
    | cons r0 rs0 =>
      cases hv1 : vsl 1 with
      | nil => rw [hv0, hv1] at h0; cases h0
      | cons r1 rs1 =>
        cases hv2 : vsl 2 with
        | nil => rw [hv1, hv2] at h1; cases h1
        | cons r2 rs2 =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckIntRounds] at h0 h1 h2
          let rv : Fin 3 → PartySboxView := fun | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2
          let rs : Fin 3 → List PartySboxView := fun | ⟨0, _⟩ => rs0 | ⟨1, _⟩ => rs1 | ⟨2, _⟩ => rs2
          cases hm0 : pairCheckIntRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with
          | none => change (match pairCheckIntRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => _) = some o0 at h0; rw [hm0] at h0; cases h0
          | some m0 =>
            cases hm1 : pairCheckIntRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with
            | none => change (match pairCheckIntRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => _) = some o1 at h1; rw [hm1] at h1; cases h1
            | some m1 =>
              cases hm2 : pairCheckIntRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with
              | none => change (match pairCheckIntRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => _) = some o2 at h2; rw [hm2] at h2; cases h2
              | some m2 =>
                change (match pairCheckIntRound 0 rc (rv 0) (rv 1) (vcPairAtState12 st 0) with | none => none | some st' => pairCheckIntRounds 0 rcs (rs 0) (rs 1) st') = some o0 at h0
                change (match pairCheckIntRound 1 rc (rv 1) (rv 2) (vcPairAtState12 st 1) with | none => none | some st' => pairCheckIntRounds 1 rcs (rs 1) (rs 2) st') = some o1 at h1
                change (match pairCheckIntRound 2 rc (rv 2) (rv 0) (vcPairAtState12 st 2) with | none => none | some st' => pairCheckIntRounds 2 rcs (rs 2) (rs 0) st') = some o2 at h2
                rw [hm0] at h0; rw [hm1] at h1; rw [hm2] at h2
                rw [(pairCheckIntRound_step hm0).1] at h0
                rw [(pairCheckIntRound_step hm1).1] at h1
                rw [(pairCheckIntRound_step hm2).1] at h2
                obtain ⟨stOut, e0, e1, e2, hSum⟩ :=
                  pairCheckIntRounds_extract3 rcs (vcIntRoundOut3 st rv) rs h0 h1 h2
                rw [runRounds_cons, ← pairCheckIntRound_extract3 hm0 hm1 hm2]
                exact ⟨stOut, e0, e1, e2, hSum⟩

structure PartyPerm12View where
  initExt : List PartyExtRoundView
  internal : List PartySboxView
  termExt : List PartyExtRoundView
  deriving DecidableEq, Repr

def extractPerm12Coins (pv : PartyPerm12View) : Option Perm12Coins :=
  match extractExtRoundsCoins poseidon2InitialExtConsts pv.initExt,
        extractIntRoundsCoins poseidon2InternalConsts pv.internal,
        extractExtRoundsCoins poseidon2TerminalExtConsts pv.termExt with
  | some c1, some c2, some c3 => some ⟨c1, c2, c3⟩
  | _, _, _ => none

def pairCheckRawPerm12 (e : Fin 3) (vE vE1 : PartyPerm12View)
    (st : Poseidon2State12 × Poseidon2State12) : Option (Poseidon2State12 × Poseidon2State12) :=
  let s0 := (applyME st.1, applyME st.2)
  match pairCheckExtRounds e poseidon2InitialExtConsts vE.initExt vE1.initExt s0 with
  | none => none
  | some s1 =>
    match pairCheckIntRounds e poseidon2InternalConsts vE.internal vE1.internal s1 with
    | none => none
    | some s2 => pairCheckExtRounds e poseidon2TerminalExtConsts vE.termExt vE1.termExt s2

def honestRawPerm12_3 (st : VcState12_3) (pc : Fin 3 → Perm12Coins) :
    (Fin 3 → PartyPerm12View) × VcState12_3 :=
  let s0 : VcState12_3 := fun i => applyME (st i)
  let r1 := honestExtRounds3 poseidon2InitialExtConsts s0 (fun i => (pc i).initExt)
  let r2 := honestIntRounds3 poseidon2InternalConsts r1.2 (fun i => (pc i).internal)
  let r3 := honestExtRounds3 poseidon2TerminalExtConsts r2.2 (fun i => (pc i).termExt)
  (fun i => ⟨r1.1 i, r2.1 i, r3.1 i⟩, r3.2)

private theorem extractPerm12Coins_honest (st : VcState12_3) (pc : Fin 3 → Perm12Coins) (i : Fin 3) :
    extractPerm12Coins ((honestRawPerm12_3 st pc).1 i) = some (pc i) := by
  unfold extractPerm12Coins honestRawPerm12_3
  dsimp only
  rw [extractExtRoundsCoins_honest, extractIntRoundsCoins_honest, extractExtRoundsCoins_honest]

private theorem pairCheckRawPerm12_honest (st : VcState12_3) (pc : Fin 3 → Perm12Coins) (e : Fin 3) :
    pairCheckRawPerm12 e ((honestRawPerm12_3 st pc).1 e) ((honestRawPerm12_3 st pc).1 (vcNextParty3 e))
      (vcPairAtState12 st e) = some (vcPairAtState12 (honestRawPerm12_3 st pc).2 e) := by
  unfold pairCheckRawPerm12 honestRawPerm12_3
  dsimp only
  have hs0 : (applyME (vcPairAtState12 st e).1, applyME (vcPairAtState12 st e).2) =
      vcPairAtState12 (fun i => applyME (st i)) e := rfl
  rw [hs0, pairCheckExtRounds_honest]; dsimp only
  rw [pairCheckIntRounds_honest]; dsimp only
  rw [pairCheckExtRounds_honest]

private theorem pairCheckRawPerm12_extract3 {st : VcState12_3} {pv : Fin 3 → PartyPerm12View}
    {o0 o1 o2 : Poseidon2State12 × Poseidon2State12}
    (h0 : pairCheckRawPerm12 0 (pv 0) (pv 1) (vcPairAtState12 st 0) = some o0)
    (h1 : pairCheckRawPerm12 1 (pv 1) (pv 2) (vcPairAtState12 st 1) = some o1)
    (h2 : pairCheckRawPerm12 2 (pv 2) (pv 0) (vcPairAtState12 st 2) = some o2) :
    ∃ stOut : VcState12_3,
      o0 = vcPairAtState12 stOut 0 ∧
      o1 = vcPairAtState12 stOut 1 ∧
      o2 = vcPairAtState12 stOut 2 ∧
      vcSumState12_3 stOut = poseidon2Perm12 (vcSumState12_3 st) := by
  unfold pairCheckRawPerm12 at h0 h1 h2
  let s0 : VcState12_3 := fun i => applyME (st i)
  change (match pairCheckExtRounds 0 poseidon2InitialExtConsts (pv 0).initExt (pv 1).initExt (vcPairAtState12 s0 0) with | none => none | some s1 => _) = some o0 at h0
  change (match pairCheckExtRounds 1 poseidon2InitialExtConsts (pv 1).initExt (pv 2).initExt (vcPairAtState12 s0 1) with | none => none | some s1 => _) = some o1 at h1
  change (match pairCheckExtRounds 2 poseidon2InitialExtConsts (pv 2).initExt (pv 0).initExt (vcPairAtState12 s0 2) with | none => none | some s1 => _) = some o2 at h2
  cases a0 : pairCheckExtRounds 0 poseidon2InitialExtConsts (pv 0).initExt (pv 1).initExt (vcPairAtState12 s0 0) with
  | none => rw [a0] at h0; cases h0
  | some u0 =>
  cases a1 : pairCheckExtRounds 1 poseidon2InitialExtConsts (pv 1).initExt (pv 2).initExt (vcPairAtState12 s0 1) with
  | none => rw [a1] at h1; cases h1
  | some u1 =>
  cases a2 : pairCheckExtRounds 2 poseidon2InitialExtConsts (pv 2).initExt (pv 0).initExt (vcPairAtState12 s0 2) with
  | none => rw [a2] at h2; cases h2
  | some u2 =>
    rw [a0] at h0; rw [a1] at h1; rw [a2] at h2
    obtain ⟨st1, hu0, hu1, hu2, hSum1⟩ :=
      pairCheckExtRounds_extract3 poseidon2InitialExtConsts s0 (fun i => (pv i).initExt) a0 a1 a2
    rw [hu0] at h0; rw [hu1] at h1; rw [hu2] at h2
    dsimp only at h0 h1 h2
    cases b0 : pairCheckIntRounds 0 poseidon2InternalConsts (pv 0).internal (pv 1).internal (vcPairAtState12 st1 0) with
    | none => rw [b0] at h0; cases h0
    | some v0 =>
    cases b1 : pairCheckIntRounds 1 poseidon2InternalConsts (pv 1).internal (pv 2).internal (vcPairAtState12 st1 1) with
    | none => rw [b1] at h1; cases h1
    | some v1 =>
    cases b2 : pairCheckIntRounds 2 poseidon2InternalConsts (pv 2).internal (pv 0).internal (vcPairAtState12 st1 2) with
    | none => rw [b2] at h2; cases h2
    | some v2 =>
      rw [b0] at h0; rw [b1] at h1; rw [b2] at h2
      obtain ⟨st2, hv0, hv1, hv2, hSum2⟩ :=
        pairCheckIntRounds_extract3 poseidon2InternalConsts st1 (fun i => (pv i).internal) b0 b1 b2
      rw [hv0] at h0; rw [hv1] at h1; rw [hv2] at h2
      dsimp only at h0 h1 h2
      obtain ⟨st3, hw0, hw1, hw2, hSum3⟩ :=
        pairCheckExtRounds_extract3 poseidon2TerminalExtConsts st2 (fun i => (pv i).termExt) h0 h1 h2
      refine ⟨st3, hw0, hw1, hw2, ?_⟩
      unfold poseidon2Perm12
      dsimp only
      rw [hSum3, hSum2, hSum1, vcSumState12_3_applyME]

/-- Single party's view for 3-permutation rate-6/capacity-6 `absorbRate6Sponge3` (`blind_vc.rs:390-405`). -/
structure PartySponge3PermView where
  perm1 : PartyPerm12View
  perm2 : PartyPerm12View
  perm3 : PartyPerm12View
  deriving DecidableEq, Repr

def extractSponge3Coins (sv : PartySponge3PermView) : Option Sponge3Coins :=
  match extractPerm12Coins sv.perm1, extractPerm12Coins sv.perm2, extractPerm12Coins sv.perm3 with
  | some c1, some c2, some c3 => some ⟨c1, c2, c3⟩
  | _, _, _ => none

def pairCheckSponge3Perm (e : Fin 3) (vE vE1 : PartySponge3PermView)
    (c0 c1 c2 : Lane6 × Lane6) : Option (Lane6 × Lane6) :=
  let s1 := (mkState12Of6 c0.1 lane6Zero, mkState12Of6 c0.2 lane6Zero)
  match pairCheckRawPerm12 e vE.perm1 vE1.perm1 s1 with
  | none => none
  | some p1 =>
    let s2 := (mkState12Of6 (lane6Add (state12Rate6 p1.1) c1.1) (state12Cap6 p1.1),
               mkState12Of6 (lane6Add (state12Rate6 p1.2) c1.2) (state12Cap6 p1.2))
    match pairCheckRawPerm12 e vE.perm2 vE1.perm2 s2 with
    | none => none
    | some p2 =>
      let s3 := (mkState12Of6 (lane6Add (state12Rate6 p2.1) c2.1) (state12Cap6 p2.1),
                 mkState12Of6 (lane6Add (state12Rate6 p2.2) c2.2) (state12Cap6 p2.2))
      match pairCheckRawPerm12 e vE.perm3 vE1.perm3 s3 with
      | none => none
      | some p3 => some (state12Rate6 p3.1, state12Rate6 p3.2)

def honestSponge3Perm3 (c0 c1 c2 : VcLane6_3) (sc : Fin 3 → Sponge3Coins) :
    (Fin 3 → PartySponge3PermView) × VcLane6_3 :=
  let s1 : VcState12_3 := fun i => mkState12Of6 (c0 i) lane6Zero
  let r1 := honestRawPerm12_3 s1 (fun i => (sc i).perm1)
  let s2 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (r1.2 i)) (c1 i)) (state12Cap6 (r1.2 i))
  let r2 := honestRawPerm12_3 s2 (fun i => (sc i).perm2)
  let s3 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (r2.2 i)) (c2 i)) (state12Cap6 (r2.2 i))
  let r3 := honestRawPerm12_3 s3 (fun i => (sc i).perm3)
  (fun i => ⟨r1.1 i, r2.1 i, r3.1 i⟩, fun i => state12Rate6 (r3.2 i))

private theorem extractSponge3Coins_honest (c0 c1 c2 : VcLane6_3) (sc : Fin 3 → Sponge3Coins) (i : Fin 3) :
    extractSponge3Coins ((honestSponge3Perm3 c0 c1 c2 sc).1 i) = some (sc i) := by
  unfold extractSponge3Coins honestSponge3Perm3
  dsimp only
  rw [extractPerm12Coins_honest, extractPerm12Coins_honest, extractPerm12Coins_honest]

private theorem pairCheckSponge3Perm_honest (c0 c1 c2 : VcLane6_3)
    (sc : Fin 3 → Sponge3Coins) (e : Fin 3) :
    pairCheckSponge3Perm e ((honestSponge3Perm3 c0 c1 c2 sc).1 e)
      ((honestSponge3Perm3 c0 c1 c2 sc).1 (vcNextParty3 e))
      (vcPairAtLane6 c0 e) (vcPairAtLane6 c1 e) (vcPairAtLane6 c2 e) =
      some (vcPairAtLane6 (honestSponge3Perm3 c0 c1 c2 sc).2 e) := by
  unfold pairCheckSponge3Perm honestSponge3Perm3 vcPairAtLane6
  dsimp only
  have hs1 : (mkState12Of6 (c0 e) lane6Zero, mkState12Of6 (c0 (vcNextParty3 e)) lane6Zero) =
      vcPairAtState12 (fun i => mkState12Of6 (c0 i) lane6Zero) e := rfl
  rw [hs1, pairCheckRawPerm12_honest]; dsimp only
  let p1 := (honestRawPerm12_3 (fun i => mkState12Of6 (c0 i) lane6Zero) (fun i => (sc i).perm1)).2
  have hs2 : (mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p1 e).1) (c1 e)) (state12Cap6 (vcPairAtState12 p1 e).1),
              mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p1 e).2) (c1 (vcNextParty3 e))) (state12Cap6 (vcPairAtState12 p1 e).2)) =
      vcPairAtState12 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))) e := rfl
  rw [hs2, pairCheckRawPerm12_honest]; dsimp only
  let p2 := (honestRawPerm12_3 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))) (fun i => (sc i).perm2)).2
  have hs3 : (mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p2 e).1) (c2 e)) (state12Cap6 (vcPairAtState12 p2 e).1),
              mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p2 e).2) (c2 (vcNextParty3 e))) (state12Cap6 (vcPairAtState12 p2 e).2)) =
      vcPairAtState12 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p2 i)) (c2 i)) (state12Cap6 (p2 i))) e := rfl
  rw [hs3, pairCheckRawPerm12_honest]
  rfl

private theorem pairCheckSponge3Perm_extract3 {c0 c1 c2 : VcLane6_3}
    {sv : Fin 3 → PartySponge3PermView} {o0 o1 o2 : Lane6 × Lane6}
    (h0 : pairCheckSponge3Perm 0 (sv 0) (sv 1) (vcPairAtLane6 c0 0) (vcPairAtLane6 c1 0) (vcPairAtLane6 c2 0) = some o0)
    (h1 : pairCheckSponge3Perm 1 (sv 1) (sv 2) (vcPairAtLane6 c0 1) (vcPairAtLane6 c1 1) (vcPairAtLane6 c2 1) = some o1)
    (h2 : pairCheckSponge3Perm 2 (sv 2) (sv 0) (vcPairAtLane6 c0 2) (vcPairAtLane6 c1 2) (vcPairAtLane6 c2 2) = some o2) :
    ∃ out6 : VcLane6_3,
      o0 = vcPairAtLane6 out6 0 ∧
      o1 = vcPairAtLane6 out6 1 ∧
      o2 = vcPairAtLane6 out6 2 ∧
      vcSumLane6_3 out6 =
        state12Rate6 (absorbRate6Sponge3 (vcSumLane6_3 c0) (vcSumLane6_3 c1) (vcSumLane6_3 c2)) := by
  unfold pairCheckSponge3Perm at h0 h1 h2
  let s1 : VcState12_3 := fun i => mkState12Of6 (c0 i) lane6Zero
  change (match pairCheckRawPerm12 0 (sv 0).perm1 (sv 1).perm1 (vcPairAtState12 s1 0) with | none => none | some p1 => _) = some o0 at h0
  change (match pairCheckRawPerm12 1 (sv 1).perm1 (sv 2).perm1 (vcPairAtState12 s1 1) with | none => none | some p1 => _) = some o1 at h1
  change (match pairCheckRawPerm12 2 (sv 2).perm1 (sv 0).perm1 (vcPairAtState12 s1 2) with | none => none | some p1 => _) = some o2 at h2
  cases a0 : pairCheckRawPerm12 0 (sv 0).perm1 (sv 1).perm1 (vcPairAtState12 s1 0) with
  | none => rw [a0] at h0; cases h0
  | some u0 =>
  cases a1 : pairCheckRawPerm12 1 (sv 1).perm1 (sv 2).perm1 (vcPairAtState12 s1 1) with
  | none => rw [a1] at h1; cases h1
  | some u1 =>
  cases a2 : pairCheckRawPerm12 2 (sv 2).perm1 (sv 0).perm1 (vcPairAtState12 s1 2) with
  | none => rw [a2] at h2; cases h2
  | some u2 =>
    rw [a0] at h0; rw [a1] at h1; rw [a2] at h2
    obtain ⟨p1, hu0, hu1, hu2, hSum1⟩ :=
      pairCheckRawPerm12_extract3 (pv := fun i => (sv i).perm1) a0 a1 a2
    rw [hu0] at h0; rw [hu1] at h1; rw [hu2] at h2
    dsimp only at h0 h1 h2
    let s2 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))
    change (match pairCheckRawPerm12 0 (sv 0).perm2 (sv 1).perm2 (vcPairAtState12 s2 0) with | none => none | some p2 => _) = some o0 at h0
    change (match pairCheckRawPerm12 1 (sv 1).perm2 (sv 2).perm2 (vcPairAtState12 s2 1) with | none => none | some p2 => _) = some o1 at h1
    change (match pairCheckRawPerm12 2 (sv 2).perm2 (sv 0).perm2 (vcPairAtState12 s2 2) with | none => none | some p2 => _) = some o2 at h2
    cases b0 : pairCheckRawPerm12 0 (sv 0).perm2 (sv 1).perm2 (vcPairAtState12 s2 0) with
    | none => rw [b0] at h0; cases h0
    | some v0 =>
    cases b1 : pairCheckRawPerm12 1 (sv 1).perm2 (sv 2).perm2 (vcPairAtState12 s2 1) with
    | none => rw [b1] at h1; cases h1
    | some v1 =>
    cases b2 : pairCheckRawPerm12 2 (sv 2).perm2 (sv 0).perm2 (vcPairAtState12 s2 2) with
    | none => rw [b2] at h2; cases h2
    | some v2 =>
      rw [b0] at h0; rw [b1] at h1; rw [b2] at h2
      obtain ⟨p2, hv0, hv1, hv2, hSum2⟩ :=
        pairCheckRawPerm12_extract3 (pv := fun i => (sv i).perm2) b0 b1 b2
      rw [hv0] at h0; rw [hv1] at h1; rw [hv2] at h2
      dsimp only at h0 h1 h2
      let s3 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (p2 i)) (c2 i)) (state12Cap6 (p2 i))
      change (match pairCheckRawPerm12 0 (sv 0).perm3 (sv 1).perm3 (vcPairAtState12 s3 0) with | none => none | some p3 => _) = some o0 at h0
      change (match pairCheckRawPerm12 1 (sv 1).perm3 (sv 2).perm3 (vcPairAtState12 s3 1) with | none => none | some p3 => _) = some o1 at h1
      change (match pairCheckRawPerm12 2 (sv 2).perm3 (sv 0).perm3 (vcPairAtState12 s3 2) with | none => none | some p3 => _) = some o2 at h2
      cases d0 : pairCheckRawPerm12 0 (sv 0).perm3 (sv 1).perm3 (vcPairAtState12 s3 0) with
      | none => rw [d0] at h0; cases h0
      | some w0 =>
      cases d1 : pairCheckRawPerm12 1 (sv 1).perm3 (sv 2).perm3 (vcPairAtState12 s3 1) with
      | none => rw [d1] at h1; cases h1
      | some w1 =>
      cases d2 : pairCheckRawPerm12 2 (sv 2).perm3 (sv 0).perm3 (vcPairAtState12 s3 2) with
      | none => rw [d2] at h2; cases h2
      | some w2 =>
        rw [d0] at h0; rw [d1] at h1; rw [d2] at h2
        obtain ⟨p3, hw0, hw1, hw2, hSum3⟩ :=
          pairCheckRawPerm12_extract3 (pv := fun i => (sv i).perm3) d0 d1 d2
        rw [hw0] at h0; rw [hw1] at h1; rw [hw2] at h2
        injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
        refine ⟨fun i => state12Rate6 (p3 i), ho0.symm, ho1.symm, ho2.symm, ?_⟩
        rw [← state12Rate6_vcSum, hSum3]
        have hs1Eq : vcSumState12_3 s1 = mkState12Of6 (vcSumLane6_3 c0) lane6Zero := by
          dsimp only [s1]; rw [vcSumState12_3_of6, vcSumLane6_3_zero]
        have hs2Eq : vcSumState12_3 s2 =
            mkState12Of6 (lane6Add (state12Rate6 (vcSumState12_3 p1)) (vcSumLane6_3 c1))
              (state12Cap6 (vcSumState12_3 p1)) := by
          dsimp only [s2]
          rw [vcSumState12_3_of6, vcSumLane6_3_add, ← state12Rate6_vcSum, ← state12Cap6_vcSum]
        have hs3Eq : vcSumState12_3 s3 =
            mkState12Of6 (lane6Add (state12Rate6 (vcSumState12_3 p2)) (vcSumLane6_3 c2))
              (state12Cap6 (vcSumState12_3 p2)) := by
          dsimp only [s3]
          rw [vcSumState12_3_of6, vcSumLane6_3_add, ← state12Rate6_vcSum, ← state12Cap6_vcSum]
        rw [hs3Eq, hSum2, hs2Eq, hSum1, hs1Eq]
        rfl

private theorem honestSponge3Perm3_sum (c0 c1 c2 : VcLane6_3) (sc : Fin 3 → Sponge3Coins) :
    vcSumLane6_3 (honestSponge3Perm3 c0 c1 c2 sc).2 =
      state12Rate6 (absorbRate6Sponge3 (vcSumLane6_3 c0) (vcSumLane6_3 c1) (vcSumLane6_3 c2)) := by
  have h0 := pairCheckSponge3Perm_honest c0 c1 c2 sc 0
  have h1 := pairCheckSponge3Perm_honest c0 c1 c2 sc 1
  have h2 := pairCheckSponge3Perm_honest c0 c1 c2 sc 2
  obtain ⟨out6, e0, e1, _, hSum⟩ := pairCheckSponge3Perm_extract3 h0 h1 h2
  have hEq : (honestSponge3Perm3 c0 c1 c2 sc).2 = out6 := by
    apply funext
    refine fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1)
  rwa [hEq]

/-- Single party's view for one 6-limb Merkle accumulator level (`blind_vc.rs:1993-2038`). -/
structure PartyMerkleLevelView where
  bitShare : Goldilocks
  sibShare : Lane6
  boolGate : PartyMulView
  sel0 : PartyMulView
  sel1 : PartyMulView
  sel2 : PartyMulView
  sel3 : PartyMulView
  sel4 : PartyMulView
  sel5 : PartyMulView
  hashView : PartySponge3PermView
  deriving DecidableEq, Repr

def extractMerkleLevelCoins (lv : PartyMerkleLevelView) : Option MerkleLevelCoins :=
  (extractSponge3Coins lv.hashView).map (fun hc =>
    ⟨lv.boolGate.r, lv.sel0.r, lv.sel1.r, lv.sel2.r, lv.sel3.r, lv.sel4.r, lv.sel5.r, hc⟩)

def pairSubGold (a b : Goldilocks × Goldilocks) : Goldilocks × Goldilocks :=
  (Goldilocks.sub a.1 b.1, Goldilocks.sub a.2 b.2)

def pairAddGold (a b : Goldilocks × Goldilocks) : Goldilocks × Goldilocks :=
  (Goldilocks.add a.1 b.1, Goldilocks.add a.2 b.2)

/-- Verify one 6-limb Merkle level at challenge `e`, returning `(nextCurNodePair, boolZeroPair)`. -/
def pairCheckMerkleLevel (e : Fin 3) (epoch : UInt64) (layer : Nat)
    (cur : Lane6 × Lane6) (lvE lvE1 : PartyMerkleLevelView) :
    Option ((Lane6 × Lane6) × (Goldilocks × Goldilocks)) :=
  let b := (lvE.bitShare, lvE1.bitShare)
  let oneWire := vcConstPair e Goldilocks.one
  let oneMinusB := pairSubGold oneWire b
  match pairCheckMul b oneMinusB lvE.boolGate lvE1.boolGate with
  | none => none
  | some boolZero =>
    let d0 := pairSubGold (lvE.sibShare.x0, lvE1.sibShare.x0) (cur.1.x0, cur.2.x0)
    let d1 := pairSubGold (lvE.sibShare.x1, lvE1.sibShare.x1) (cur.1.x1, cur.2.x1)
    let d2 := pairSubGold (lvE.sibShare.x2, lvE1.sibShare.x2) (cur.1.x2, cur.2.x2)
    let d3 := pairSubGold (lvE.sibShare.x3, lvE1.sibShare.x3) (cur.1.x3, cur.2.x3)
    let d4 := pairSubGold (lvE.sibShare.x4, lvE1.sibShare.x4) (cur.1.x4, cur.2.x4)
    let d5 := pairSubGold (lvE.sibShare.x5, lvE1.sibShare.x5) (cur.1.x5, cur.2.x5)
    match pairCheckMul b d0 lvE.sel0 lvE1.sel0,
          pairCheckMul b d1 lvE.sel1 lvE1.sel1,
          pairCheckMul b d2 lvE.sel2 lvE1.sel2,
          pairCheckMul b d3 lvE.sel3 lvE1.sel3,
          pairCheckMul b d4 lvE.sel4 lvE1.sel4,
          pairCheckMul b d5 lvE.sel5 lvE1.sel5 with
    | some del0, some del1, some del2, some del3, some del4, some del5 =>
      let l0 := pairAddGold (cur.1.x0, cur.2.x0) del0
      let l1 := pairAddGold (cur.1.x1, cur.2.x1) del1
      let l2 := pairAddGold (cur.1.x2, cur.2.x2) del2
      let l3 := pairAddGold (cur.1.x3, cur.2.x3) del3
      let l4 := pairAddGold (cur.1.x4, cur.2.x4) del4
      let l5 := pairAddGold (cur.1.x5, cur.2.x5) del5
      let r0 := pairSubGold (lvE.sibShare.x0, lvE1.sibShare.x0) del0
      let r1 := pairSubGold (lvE.sibShare.x1, lvE1.sibShare.x1) del1
      let r2 := pairSubGold (lvE.sibShare.x2, lvE1.sibShare.x2) del2
      let r3 := pairSubGold (lvE.sibShare.x3, lvE1.sibShare.x3) del3
      let r4 := pairSubGold (lvE.sibShare.x4, lvE1.sibShare.x4) del4
      let r5 := pairSubGold (lvE.sibShare.x5, lvE1.sibShare.x5) del5
      let k0 := vcConstPair e (vcSchemaLo epoch)
      let k1 := vcConstPair e (Goldilocks.ofNat layer)
      let k2 := vcConstPair e (Goldilocks.ofNat vcMerkleNodeTag.toNat)
      let k3 := vcConstPair e (vcSchemaHiWithTag epoch poseidon2ConstIV)
      let k4 := vcConstPair e Goldilocks.one
      let c0Pair : Lane6 × Lane6 := (⟨l0.1, l1.1, l2.1, l3.1, l4.1, l5.1⟩, ⟨l0.2, l1.2, l2.2, l3.2, l4.2, l5.2⟩)
      let c1Pair : Lane6 × Lane6 := (⟨r0.1, r1.1, r2.1, r3.1, r4.1, r5.1⟩, ⟨r0.2, r1.2, r2.2, r3.2, r4.2, r5.2⟩)
      let c2Pair : Lane6 × Lane6 :=
        (⟨k0.1, k1.1, k2.1, k3.1, k4.1, Goldilocks.zero⟩,
         ⟨k0.2, k1.2, k2.2, k3.2, k4.2, Goldilocks.zero⟩)
      match pairCheckSponge3Perm e lvE.hashView lvE1.hashView c0Pair c1Pair c2Pair with
      | none => none
      | some nextPair => some (nextPair, boolZero)
    | _, _, _, _, _, _ => none

def honestMerkleLevel3 (epoch : UInt64) (layer : Nat) (cur : VcLane6_3)
    (b : VcWire3) (sib : VcLane6_3) (mc : Fin 3 → MerkleLevelCoins) :
    (Fin 3 → PartyMerkleLevelView) × VcLane6_3 × VcWire3 :=
  let oneMinusB : VcWire3 := fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (b i)
  let bg := honestMulView3 b oneMinusB (fun i => (mc i).boolR)
  let bz := vcMulGate3 b oneMinusB (fun i => (mc i).boolR)
  let d0 : VcWire3 := fun i => Goldilocks.sub (sib i).x0 (cur i).x0
  let d1 : VcWire3 := fun i => Goldilocks.sub (sib i).x1 (cur i).x1
  let d2 : VcWire3 := fun i => Goldilocks.sub (sib i).x2 (cur i).x2
  let d3 : VcWire3 := fun i => Goldilocks.sub (sib i).x3 (cur i).x3
  let d4 : VcWire3 := fun i => Goldilocks.sub (sib i).x4 (cur i).x4
  let d5 : VcWire3 := fun i => Goldilocks.sub (sib i).x5 (cur i).x5
  let s0 := honestMulView3 b d0 (fun i => (mc i).sel0R); let del0 := vcMulGate3 b d0 (fun i => (mc i).sel0R)
  let s1 := honestMulView3 b d1 (fun i => (mc i).sel1R); let del1 := vcMulGate3 b d1 (fun i => (mc i).sel1R)
  let s2 := honestMulView3 b d2 (fun i => (mc i).sel2R); let del2 := vcMulGate3 b d2 (fun i => (mc i).sel2R)
  let s3 := honestMulView3 b d3 (fun i => (mc i).sel3R); let del3 := vcMulGate3 b d3 (fun i => (mc i).sel3R)
  let s4 := honestMulView3 b d4 (fun i => (mc i).sel4R); let del4 := vcMulGate3 b d4 (fun i => (mc i).sel4R)
  let s5 := honestMulView3 b d5 (fun i => (mc i).sel5R); let del5 := vcMulGate3 b d5 (fun i => (mc i).sel5R)
  let c0 : VcLane6_3 := fun i =>
    ⟨Goldilocks.add (cur i).x0 (del0 i), Goldilocks.add (cur i).x1 (del1 i),
     Goldilocks.add (cur i).x2 (del2 i), Goldilocks.add (cur i).x3 (del3 i),
     Goldilocks.add (cur i).x4 (del4 i), Goldilocks.add (cur i).x5 (del5 i)⟩
  let c1 : VcLane6_3 := fun i =>
    ⟨Goldilocks.sub (sib i).x0 (del0 i), Goldilocks.sub (sib i).x1 (del1 i),
     Goldilocks.sub (sib i).x2 (del2 i), Goldilocks.sub (sib i).x3 (del3 i),
     Goldilocks.sub (sib i).x4 (del4 i), Goldilocks.sub (sib i).x5 (del5 i)⟩
  let c2 : VcLane6_3 := fun i =>
    ⟨vcConstWire3 (vcSchemaLo epoch) i,
     vcConstWire3 (Goldilocks.ofNat layer) i,
     vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
     vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
     vcConstWire3 Goldilocks.one i,
     Goldilocks.zero⟩
  let sp := honestSponge3Perm3 c0 c1 c2 (fun i => (mc i).hashCoins)
  (fun i => ⟨b i, sib i, bg i, s0 i, s1 i, s2 i, s3 i, s4 i, s5 i, sp.1 i⟩, sp.2, bz)

private theorem extractMerkleLevelCoins_honest (epoch : UInt64) (layer : Nat) (cur : VcLane6_3)
    (b : VcWire3) (sib : VcLane6_3) (mc : Fin 3 → MerkleLevelCoins) (i : Fin 3) :
    extractMerkleLevelCoins ((honestMerkleLevel3 epoch layer cur b sib mc).1 i) = some (mc i) := by
  unfold extractMerkleLevelCoins honestMerkleLevel3 honestMulView3
  dsimp only
  simp only [extractSponge3Coins_honest, Option.map]

private theorem pairCheckMerkleLevel_honest (epoch : UInt64) (layer : Nat)
    (cur : VcLane6_3) (b : VcWire3) (sib : VcLane6_3) (mc : Fin 3 → MerkleLevelCoins) (e : Fin 3) :
    pairCheckMerkleLevel e epoch layer (vcPairAtLane6 cur e)
      ((honestMerkleLevel3 epoch layer cur b sib mc).1 e)
      ((honestMerkleLevel3 epoch layer cur b sib mc).1 (vcNextParty3 e)) =
      some (vcPairAtLane6 (honestMerkleLevel3 epoch layer cur b sib mc).2.1 e,
            vcPairAt (honestMerkleLevel3 epoch layer cur b sib mc).2.2 e) := by
  unfold pairCheckMerkleLevel honestMerkleLevel3 vcPairAtLane6
  dsimp only
  rw [vcConstPair_spec Goldilocks.one e,
      vcConstPair_spec (vcSchemaLo epoch) e,
      vcConstPair_spec (Goldilocks.ofNat layer) e,
      vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) e,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) e]
  have hOneSub : pairSubGold (vcPairAt (vcConstWire3 Goldilocks.one) e) (b e, b (vcNextParty3 e)) =
      vcPairAt (fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (b i)) e := rfl
  have hbPair : (b e, b (vcNextParty3 e)) = vcPairAt b e := rfl
  have hd0 : pairSubGold ((sib e).x0, (sib (vcNextParty3 e)).x0) ((cur e).x0, (cur (vcNextParty3 e)).x0) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x0 (cur i).x0) e := rfl
  have hd1 : pairSubGold ((sib e).x1, (sib (vcNextParty3 e)).x1) ((cur e).x1, (cur (vcNextParty3 e)).x1) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x1 (cur i).x1) e := rfl
  have hd2 : pairSubGold ((sib e).x2, (sib (vcNextParty3 e)).x2) ((cur e).x2, (cur (vcNextParty3 e)).x2) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x2 (cur i).x2) e := rfl
  have hd3 : pairSubGold ((sib e).x3, (sib (vcNextParty3 e)).x3) ((cur e).x3, (cur (vcNextParty3 e)).x3) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x3 (cur i).x3) e := rfl
  have hd4 : pairSubGold ((sib e).x4, (sib (vcNextParty3 e)).x4) ((cur e).x4, (cur (vcNextParty3 e)).x4) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x4 (cur i).x4) e := rfl
  have hd5 : pairSubGold ((sib e).x5, (sib (vcNextParty3 e)).x5) ((cur e).x5, (cur (vcNextParty3 e)).x5) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x5 (cur i).x5) e := rfl
  rw [hOneSub, hbPair, pairCheckMul_honest, hd0, hd1, hd2, hd3, hd4, hd5,
      pairCheckMul_honest, pairCheckMul_honest, pairCheckMul_honest,
      pairCheckMul_honest, pairCheckMul_honest, pairCheckMul_honest]
  dsimp only
  have hsp := pairCheckSponge3Perm_honest
    (fun i =>
      ⟨Goldilocks.add (cur i).x0 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x0 (cur k).x0) (fun k => (mc k).sel0R) i),
       Goldilocks.add (cur i).x1 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x1 (cur k).x1) (fun k => (mc k).sel1R) i),
       Goldilocks.add (cur i).x2 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x2 (cur k).x2) (fun k => (mc k).sel2R) i),
       Goldilocks.add (cur i).x3 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x3 (cur k).x3) (fun k => (mc k).sel3R) i),
       Goldilocks.add (cur i).x4 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x4 (cur k).x4) (fun k => (mc k).sel4R) i),
       Goldilocks.add (cur i).x5 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x5 (cur k).x5) (fun k => (mc k).sel5R) i)⟩)
    (fun i =>
      ⟨Goldilocks.sub (sib i).x0 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x0 (cur k).x0) (fun k => (mc k).sel0R) i),
       Goldilocks.sub (sib i).x1 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x1 (cur k).x1) (fun k => (mc k).sel1R) i),
       Goldilocks.sub (sib i).x2 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x2 (cur k).x2) (fun k => (mc k).sel2R) i),
       Goldilocks.sub (sib i).x3 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x3 (cur k).x3) (fun k => (mc k).sel3R) i),
       Goldilocks.sub (sib i).x4 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x4 (cur k).x4) (fun k => (mc k).sel4R) i),
       Goldilocks.sub (sib i).x5 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x5 (cur k).x5) (fun k => (mc k).sel5R) i)⟩)
    (fun i =>
      ⟨vcConstWire3 (vcSchemaLo epoch) i,
       vcConstWire3 (Goldilocks.ofNat layer) i,
       vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
       vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
       vcConstWire3 Goldilocks.one i,
       Goldilocks.zero⟩)
    (fun i => (mc i).hashCoins) e
  dsimp only [vcPairAtLane6, pairAddGold, pairSubGold, vcPairAt] at hsp ⊢
  rw [hsp]

private theorem pairCheckMerkleLevel_extract3 {epoch : UInt64} {layer : Nat}
    {cur : VcLane6_3} {lv : Fin 3 → PartyMerkleLevelView}
    {o0 o1 o2 : (Lane6 × Lane6) × (Goldilocks × Goldilocks)}
    (h0 : pairCheckMerkleLevel 0 epoch layer (vcPairAtLane6 cur 0) (lv 0) (lv 1) = some o0)
    (h1 : pairCheckMerkleLevel 1 epoch layer (vcPairAtLane6 cur 1) (lv 1) (lv 2) = some o1)
    (h2 : pairCheckMerkleLevel 2 epoch layer (vcPairAtLane6 cur 2) (lv 2) (lv 0) = some o2) :
    ∃ (nextCur : VcLane6_3) (bz : VcWire3),
      o0 = (vcPairAtLane6 nextCur 0, vcPairAt bz 0) ∧
      o1 = (vcPairAtLane6 nextCur 1, vcPairAt bz 1) ∧
      o2 = (vcPairAtLane6 nextCur 2, vcPairAt bz 2) ∧
      vcSum3 bz = Goldilocks.mul (vcSum3 (fun i => (lv i).bitShare))
        (Goldilocks.sub Goldilocks.one (vcSum3 (fun i => (lv i).bitShare))) ∧
      vcSumLane6_3 nextCur =
        vcMerkleStepArith epoch layer (vcSumLane6_3 cur)
          (vcSumLane6_3 (fun i => (lv i).sibShare)) (vcSum3 (fun i => (lv i).bitShare)) := by
  unfold pairCheckMerkleLevel at h0 h1 h2
  rw [vcConstPair_spec Goldilocks.one 0, vcConstPair_spec (vcSchemaLo epoch) 0,
      vcConstPair_spec (Goldilocks.ofNat layer) 0, vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) 0,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) 0] at h0
  rw [vcConstPair_spec Goldilocks.one 1, vcConstPair_spec (vcSchemaLo epoch) 1,
      vcConstPair_spec (Goldilocks.ofNat layer) 1, vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) 1,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) 1] at h1
  rw [vcConstPair_spec Goldilocks.one 2, vcConstPair_spec (vcSchemaLo epoch) 2,
      vcConstPair_spec (Goldilocks.ofNat layer) 2, vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) 2,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) 2] at h2
  let bw : VcWire3 := fun i => (lv i).bitShare
  let omb : VcWire3 := fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (bw i)
  dsimp only [vcPairAtLane6, vcPairAt, vcNextParty3, pairSubGold, pairAddGold] at h0 h1 h2
  cases hb0 : pairCheckMul (vcPairAt bw 0) (vcPairAt omb 0) (lv 0).boolGate (lv 1).boolGate with
  | none => have hb0' := hb0; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb0'; rw [hb0'] at h0; cases h0
  | some bz0 =>
  cases hb1 : pairCheckMul (vcPairAt bw 1) (vcPairAt omb 1) (lv 1).boolGate (lv 2).boolGate with
  | none => have hb1' := hb1; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb1'; rw [hb1'] at h1; cases h1
  | some bz1 =>
  cases hb2 : pairCheckMul (vcPairAt bw 2) (vcPairAt omb 2) (lv 2).boolGate (lv 0).boolGate with
  | none => have hb2' := hb2; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb2'; rw [hb2'] at h2; cases h2
  | some bz2 =>
    have hb0' := hb0; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb0'
    have hb1' := hb1; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb1'
    have hb2' := hb2; dsimp only [bw, omb, vcPairAt, vcNextParty3] at hb2'
    rw [hb0'] at h0; rw [hb1'] at h1; rw [hb2'] at h2
    dsimp only at h0 h1 h2
    let dw0 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x0 (cur i).x0
    let dw1 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x1 (cur i).x1
    let dw2 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x2 (cur i).x2
    let dw3 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x3 (cur i).x3
    let dw4 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x4 (cur i).x4
    let dw5 : VcWire3 := fun i => Goldilocks.sub (lv i).sibShare.x5 (cur i).x5
    cases s00 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw0 0) (lv 0).sel0 (lv 1).sel0 with
    | none => have u := s00; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u00 := s00; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u00; rw [u00] at h0
    cases s10 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw1 0) (lv 0).sel1 (lv 1).sel1 with
    | none => have u := s10; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u10 := s10; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u10; rw [u10] at h0
    cases s20 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw2 0) (lv 0).sel2 (lv 1).sel2 with
    | none => have u := s20; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u20 := s20; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u20; rw [u20] at h0
    cases s30 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw3 0) (lv 0).sel3 (lv 1).sel3 with
    | none => have u := s30; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u30 := s30; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u30; rw [u30] at h0
    cases s40 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw4 0) (lv 0).sel4 (lv 1).sel4 with
    | none => have u := s40; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u40 := s40; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u40; rw [u40] at h0
    cases s50 : pairCheckMul (vcPairAt bw 0) (vcPairAt dw5 0) (lv 0).sel5 (lv 1).sel5 with
    | none => have u := s50; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u; rw [u] at h0; cases h0
    | some _ =>
    have u50 := s50; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u50; rw [u50] at h0
    cases s01 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw0 1) (lv 1).sel0 (lv 2).sel0 with
    | none => have u := s01; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u01 := s01; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u01; rw [u01] at h1
    cases s11 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw1 1) (lv 1).sel1 (lv 2).sel1 with
    | none => have u := s11; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u11 := s11; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u11; rw [u11] at h1
    cases s21 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw2 1) (lv 1).sel2 (lv 2).sel2 with
    | none => have u := s21; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u21 := s21; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u21; rw [u21] at h1
    cases s31 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw3 1) (lv 1).sel3 (lv 2).sel3 with
    | none => have u := s31; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u31 := s31; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u31; rw [u31] at h1
    cases s41 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw4 1) (lv 1).sel4 (lv 2).sel4 with
    | none => have u := s41; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u41 := s41; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u41; rw [u41] at h1
    cases s51 : pairCheckMul (vcPairAt bw 1) (vcPairAt dw5 1) (lv 1).sel5 (lv 2).sel5 with
    | none => have u := s51; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u; rw [u] at h1; cases h1
    | some _ =>
    have u51 := s51; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u51; rw [u51] at h1
    cases s02 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw0 2) (lv 2).sel0 (lv 0).sel0 with
    | none => have u := s02; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u02 := s02; dsimp only [bw, dw0, vcPairAt, vcNextParty3] at u02; rw [u02] at h2
    cases s12 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw1 2) (lv 2).sel1 (lv 0).sel1 with
    | none => have u := s12; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u12 := s12; dsimp only [bw, dw1, vcPairAt, vcNextParty3] at u12; rw [u12] at h2
    cases s22 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw2 2) (lv 2).sel2 (lv 0).sel2 with
    | none => have u := s22; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u22 := s22; dsimp only [bw, dw2, vcPairAt, vcNextParty3] at u22; rw [u22] at h2
    cases s32 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw3 2) (lv 2).sel3 (lv 0).sel3 with
    | none => have u := s32; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u32 := s32; dsimp only [bw, dw3, vcPairAt, vcNextParty3] at u32; rw [u32] at h2
    cases s42 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw4 2) (lv 2).sel4 (lv 0).sel4 with
    | none => have u := s42; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
    have u42 := s42; dsimp only [bw, dw4, vcPairAt, vcNextParty3] at u42; rw [u42] at h2
    cases s52 : pairCheckMul (vcPairAt bw 2) (vcPairAt dw5 2) (lv 2).sel5 (lv 0).sel5 with
    | none => have u := s52; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u; rw [u] at h2; cases h2
    | some _ =>
      have u52 := s52; dsimp only [bw, dw5, vcPairAt, vcNextParty3] at u52; rw [u52] at h2
      dsimp only at h0 h1 h2
      rw [(pairCheckMul_step (g := fun i => (lv i).boolGate) (e := 0) hb0).1] at h0
      rw [(pairCheckMul_step (g := fun i => (lv i).boolGate) (e := 1) hb1).1] at h1
      rw [(pairCheckMul_step (g := fun i => (lv i).boolGate) (e := 2) hb2).1] at h2
      rw [(pairCheckMul_step (g := fun i => (lv i).sel0) (e := 0) s00).1,
          (pairCheckMul_step (g := fun i => (lv i).sel1) (e := 0) s10).1,
          (pairCheckMul_step (g := fun i => (lv i).sel2) (e := 0) s20).1,
          (pairCheckMul_step (g := fun i => (lv i).sel3) (e := 0) s30).1,
          (pairCheckMul_step (g := fun i => (lv i).sel4) (e := 0) s40).1,
          (pairCheckMul_step (g := fun i => (lv i).sel5) (e := 0) s50).1] at h0
      rw [(pairCheckMul_step (g := fun i => (lv i).sel0) (e := 1) s01).1,
          (pairCheckMul_step (g := fun i => (lv i).sel1) (e := 1) s11).1,
          (pairCheckMul_step (g := fun i => (lv i).sel2) (e := 1) s21).1,
          (pairCheckMul_step (g := fun i => (lv i).sel3) (e := 1) s31).1,
          (pairCheckMul_step (g := fun i => (lv i).sel4) (e := 1) s41).1,
          (pairCheckMul_step (g := fun i => (lv i).sel5) (e := 1) s51).1] at h1
      rw [(pairCheckMul_step (g := fun i => (lv i).sel0) (e := 2) s02).1,
          (pairCheckMul_step (g := fun i => (lv i).sel1) (e := 2) s12).1,
          (pairCheckMul_step (g := fun i => (lv i).sel2) (e := 2) s22).1,
          (pairCheckMul_step (g := fun i => (lv i).sel3) (e := 2) s32).1,
          (pairCheckMul_step (g := fun i => (lv i).sel4) (e := 2) s42).1,
          (pairCheckMul_step (g := fun i => (lv i).sel5) (e := 2) s52).1] at h2
      dsimp only [vcPairAt, vcNextParty3] at h0 h1 h2
      let c0_3 : VcLane6_3 := fun i =>
        ⟨Goldilocks.add (cur i).x0 (lv i).sel0.out, Goldilocks.add (cur i).x1 (lv i).sel1.out,
         Goldilocks.add (cur i).x2 (lv i).sel2.out, Goldilocks.add (cur i).x3 (lv i).sel3.out,
         Goldilocks.add (cur i).x4 (lv i).sel4.out, Goldilocks.add (cur i).x5 (lv i).sel5.out⟩
      let c1_3 : VcLane6_3 := fun i =>
        ⟨Goldilocks.sub (lv i).sibShare.x0 (lv i).sel0.out, Goldilocks.sub (lv i).sibShare.x1 (lv i).sel1.out,
         Goldilocks.sub (lv i).sibShare.x2 (lv i).sel2.out, Goldilocks.sub (lv i).sibShare.x3 (lv i).sel3.out,
         Goldilocks.sub (lv i).sibShare.x4 (lv i).sel4.out, Goldilocks.sub (lv i).sibShare.x5 (lv i).sel5.out⟩
      let c2_3 : VcLane6_3 := fun i =>
        ⟨vcConstWire3 (vcSchemaLo epoch) i,
         vcConstWire3 (Goldilocks.ofNat layer) i,
         vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
         vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
         vcConstWire3 Goldilocks.one i,
         Goldilocks.zero⟩
      cases sp0 : pairCheckSponge3Perm 0 (lv 0).hashView (lv 1).hashView
          (vcPairAtLane6 c0_3 0) (vcPairAtLane6 c1_3 0) (vcPairAtLane6 c2_3 0) with
      | none => have sp0' := sp0; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp0'; rw [sp0'] at h0; cases h0
      | some u0 =>
      cases sp1 : pairCheckSponge3Perm 1 (lv 1).hashView (lv 2).hashView
          (vcPairAtLane6 c0_3 1) (vcPairAtLane6 c1_3 1) (vcPairAtLane6 c2_3 1) with
      | none => have sp1' := sp1; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp1'; rw [sp1'] at h1; cases h1
      | some u1 =>
      cases sp2 : pairCheckSponge3Perm 2 (lv 2).hashView (lv 0).hashView
          (vcPairAtLane6 c0_3 2) (vcPairAtLane6 c1_3 2) (vcPairAtLane6 c2_3 2) with
      | none => have sp2' := sp2; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp2'; rw [sp2'] at h2; cases h2
      | some u2 =>
        have sp0' := sp0; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp0'
        have sp1' := sp1; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp1'
        have sp2' := sp2; dsimp only [c0_3, c1_3, c2_3, vcPairAtLane6, vcNextParty3] at sp2'
        rw [sp0'] at h0; rw [sp1'] at h1; rw [sp2'] at h2
        dsimp only at h0 h1 h2
        obtain ⟨nextCur, hu0, hu1, hu2, hSpSum⟩ :=
          pairCheckSponge3Perm_extract3 (sv := fun i => (lv i).hashView) sp0 sp1 sp2
        rw [hu0] at h0; rw [hu1] at h1; rw [hu2] at h2
        injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
        refine ⟨nextCur, fun i => (lv i).boolGate.out, ho0.symm, ho1.symm, ho2.symm, ?_, ?_⟩
        · have hBz := pairCheckMul_extract3 (g := fun i => (lv i).boolGate) hb0 hb1 hb2
          rw [hBz]; congr 1; dsimp only [omb]; rw [vcSum3_sub, vcSum3_constWire]
        · rw [hSpSum]
          unfold vcMerkleStepArith vcMerkleHashPair vcMerkleChunks lane6Add lane6Sub lane6Scale
          dsimp only
          congr 1
          simp only [vcSumLane6_3_eq]
          dsimp only [c0_3, c1_3, c2_3]
          simp only [vcSum3_add, vcSum3_sub, vcSum3_constWire, vcSum3_zero]
          rw [pairCheckMul_extract3 (g := fun i => (lv i).sel0) s00 s01 s02,
              pairCheckMul_extract3 (g := fun i => (lv i).sel1) s10 s11 s12,
              pairCheckMul_extract3 (g := fun i => (lv i).sel2) s20 s21 s22,
              pairCheckMul_extract3 (g := fun i => (lv i).sel3) s30 s31 s32,
              pairCheckMul_extract3 (g := fun i => (lv i).sel4) s40 s41 s42,
              pairCheckMul_extract3 (g := fun i => (lv i).sel5) s50 s51 s52]
          dsimp only [bw, dw0, dw1, dw2, dw3, dw4, dw5]
          simp only [vcSum3_sub]

def pairCheckMerklePath (e : Fin 3) (epoch : UInt64) :
    Nat → (Lane6 × Lane6) → List PartyMerkleLevelView → List PartyMerkleLevelView →
    Option ((Lane6 × Lane6) × List (Goldilocks × Goldilocks))
  | _, cur, [], [] => some (cur, [])
  | layer, cur, lvE :: restE, lvE1 :: restE1 =>
    match pairCheckMerkleLevel e epoch layer cur lvE lvE1 with
    | none => none
    | some (nextCur, bz) =>
      match pairCheckMerklePath e epoch (layer + 1) nextCur restE restE1 with
      | none => none
      | some (rootPair, bzs) => some (rootPair, bz :: bzs)
  | _, _, _, _ => none

def extractMerklePathCoins : (D : Nat) → List PartyMerkleLevelView → Option (Vec MerkleLevelCoins D)
  | 0, [] => some .nil
  | d + 1, lv :: rest =>
    match extractMerkleLevelCoins lv, extractMerklePathCoins d rest with
    | some hc, some tc => some (.cons hc tc)
    | _, _ => none
  | _, _ => none

def honestMerklePath3 (epoch : UInt64) :
    {D : Nat} → Nat → VcLane6_3 → Vec (VcWire3 × VcLane6_3) D → (Fin 3 → Vec MerkleLevelCoins D) →
    (Fin 3 → List PartyMerkleLevelView) × VcLane6_3 × List VcWire3
  | 0, _, cur, .nil, _ => (fun _ => [], cur, [])
  | _ + 1, layer, cur, .cons (b, sib) rest, mcs =>
    let step := honestMerkleLevel3 epoch layer cur b sib (fun i => (mcs i).head)
    let tail := honestMerklePath3 epoch (layer + 1) step.2.1 rest (fun i => (mcs i).tail)
    (fun i => step.1 i :: tail.1 i, tail.2.1, step.2.2 :: tail.2.2)

private theorem honestMerklePath3_length (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3) (steps : Vec (VcWire3 × VcLane6_3) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D) (i : Fin 3),
      ((honestMerklePath3 epoch layer cur steps mcs).1 i).length = D
  | 0, _, _, .nil, _, _ => rfl
  | _ + 1, layer, cur, .cons (_, _) rest, mcs, i => by
    simp only [honestMerklePath3, List.length_cons]
    rw [honestMerklePath3_length epoch (layer + 1) _ rest (fun j => (mcs j).tail) i]

private theorem extractMerklePathCoins_honest (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3) (steps : Vec (VcWire3 × VcLane6_3) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D) (i : Fin 3),
      extractMerklePathCoins D ((honestMerklePath3 epoch layer cur steps mcs).1 i) = some (mcs i)
  | 0, _, _, .nil, mcs, i => by cases mcs i; rfl
  | _ + 1, layer, cur, .cons (b, sib) rest, mcs, i => by
    simp only [honestMerklePath3, extractMerklePathCoins]
    rw [extractMerkleLevelCoins_honest,
        extractMerklePathCoins_honest epoch (layer + 1) _ rest (fun j => (mcs j).tail) i]
    dsimp only
    rw [Vec.eta_cons]

private theorem pairCheckMerklePath_honest (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3) (steps : Vec (VcWire3 × VcLane6_3) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D) (e : Fin 3),
      pairCheckMerklePath e epoch layer (vcPairAtLane6 cur e)
        ((honestMerklePath3 epoch layer cur steps mcs).1 e)
        ((honestMerklePath3 epoch layer cur steps mcs).1 (vcNextParty3 e)) =
        some (vcPairAtLane6 (honestMerklePath3 epoch layer cur steps mcs).2.1 e,
              (honestMerklePath3 epoch layer cur steps mcs).2.2.map (fun w => vcPairAt w e))
  | 0, _, _, .nil, _, _ => rfl
  | _ + 1, layer, cur, .cons (b, sib) rest, mcs, e => by
    simp only [honestMerklePath3, pairCheckMerklePath, List.map]
    rw [pairCheckMerkleLevel_honest]; dsimp only
    rw [pairCheckMerklePath_honest epoch (layer + 1) _ rest (fun i => (mcs i).tail) e]

private theorem pairCheckMerklePath_extract3 (epoch : UInt64) :
    ∀ (depth layer : Nat) (cur : VcLane6_3) (lvs : Fin 3 → List PartyMerkleLevelView)
      {o0 o1 o2 : (Lane6 × Lane6) × List (Goldilocks × Goldilocks)},
      (lvs 0).length = depth →
      pairCheckMerklePath 0 epoch layer (vcPairAtLane6 cur 0) (lvs 0) (lvs 1) = some o0 →
      pairCheckMerklePath 1 epoch layer (vcPairAtLane6 cur 1) (lvs 1) (lvs 2) = some o1 →
      pairCheckMerklePath 2 epoch layer (vcPairAtLane6 cur 2) (lvs 2) (lvs 0) = some o2 →
      ∃ (root3 : VcLane6_3) (bzs3 : List VcWire3) (steps : List (Goldilocks × Lane6)),
        steps.length = depth ∧
        o0 = (vcPairAtLane6 root3 0, bzs3.map (fun w => vcPairAt w 0)) ∧
        o1 = (vcPairAtLane6 root3 1, bzs3.map (fun w => vcPairAt w 1)) ∧
        o2 = (vcPairAtLane6 root3 2, bzs3.map (fun w => vcPairAt w 2)) ∧
        ((∀ z ∈ bzs3, vcSum3 z = Goldilocks.zero) →
          ∀ p ∈ steps, p.1 = Goldilocks.zero ∨ p.1 = Goldilocks.one) ∧
        vcSumLane6_3 root3 = evalVcMerklePathFrom epoch layer (vcSumLane6_3 cur) steps
  | 0, layer, cur, lvs, o0, o1, o2, hLen0, h0, h1, h2 => by
    cases hv0 : lvs 0 with
    | cons _ _ => rw [hv0] at hLen0; cases hLen0
    | nil =>
      cases hv1 : lvs 1 with
      | cons _ _ => rw [hv0, hv1] at h0; cases h0
      | nil =>
        cases hv2 : lvs 2 with
        | cons _ _ => rw [hv1, hv2] at h1; cases h1
        | nil =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckMerklePath] at h0 h1 h2
          injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
          exact ⟨cur, [], [], rfl, ho0.symm, ho1.symm, ho2.symm, (fun _ _ hp => nomatch hp), rfl⟩
  | depth + 1, layer, cur, lvs, o0, o1, o2, hLen0, h0, h1, h2 => by
    cases hv0 : lvs 0 with
    | nil => rw [hv0] at hLen0; cases hLen0
    | cons r0 rs0 =>
      rw [hv0] at hLen0; simp only [List.length_cons] at hLen0
      cases hv1 : lvs 1 with
      | nil => rw [hv0, hv1] at h0; cases h0
      | cons r1 rs1 =>
        cases hv2 : lvs 2 with
        | nil => rw [hv1, hv2] at h1; cases h1
        | cons r2 rs2 =>
          rw [hv0, hv1] at h0; rw [hv1, hv2] at h1; rw [hv2, hv0] at h2
          dsimp only [pairCheckMerklePath] at h0 h1 h2
          let lv : Fin 3 → PartyMerkleLevelView := fun | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2
          let rs : Fin 3 → List PartyMerkleLevelView := fun | ⟨0, _⟩ => rs0 | ⟨1, _⟩ => rs1 | ⟨2, _⟩ => rs2
          cases m0 : pairCheckMerkleLevel 0 epoch layer (vcPairAtLane6 cur 0) (lv 0) (lv 1) with
          | none => have m0' := m0; dsimp only [lv] at m0'; rw [m0'] at h0; cases h0
          | some p0 =>
          cases m1 : pairCheckMerkleLevel 1 epoch layer (vcPairAtLane6 cur 1) (lv 1) (lv 2) with
          | none => have m1' := m1; dsimp only [lv] at m1'; rw [m1'] at h1; cases h1
          | some p1 =>
          cases m2 : pairCheckMerkleLevel 2 epoch layer (vcPairAtLane6 cur 2) (lv 2) (lv 0) with
          | none => have m2' := m2; dsimp only [lv] at m2'; rw [m2'] at h2; cases h2
          | some p2 =>
            have m0' := m0; dsimp only [lv] at m0'
            have m1' := m1; dsimp only [lv] at m1'
            have m2' := m2; dsimp only [lv] at m2'
            rw [m0'] at h0; rw [m1'] at h1; rw [m2'] at h2
            obtain ⟨nextCur, bz, ep0, ep1, ep2, hBzEq, hNextEq⟩ := pairCheckMerkleLevel_extract3 m0 m1 m2
            rw [ep0] at h0; rw [ep1] at h1; rw [ep2] at h2
            dsimp only at h0 h1 h2
            cases t0 : pairCheckMerklePath 0 epoch (layer + 1) (vcPairAtLane6 nextCur 0) (rs 0) (rs 1) with
            | none => have t0' := t0; dsimp only [rs] at t0'; rw [t0'] at h0; cases h0
            | some q0 =>
            cases t1 : pairCheckMerklePath 1 epoch (layer + 1) (vcPairAtLane6 nextCur 1) (rs 1) (rs 2) with
            | none => have t1' := t1; dsimp only [rs] at t1'; rw [t1'] at h1; cases h1
            | some q1 =>
            cases t2 : pairCheckMerklePath 2 epoch (layer + 1) (vcPairAtLane6 nextCur 2) (rs 2) (rs 0) with
            | none => have t2' := t2; dsimp only [rs] at t2'; rw [t2'] at h2; cases h2
            | some q2 =>
              have t0' := t0; dsimp only [rs] at t0'
              have t1' := t1; dsimp only [rs] at t1'
              have t2' := t2; dsimp only [rs] at t2'
              rw [t0'] at h0; rw [t1'] at h1; rw [t2'] at h2
              obtain ⟨root3, bzs3, stepsRest, hSLen, eq0, eq1, eq2, hBoolRest, hRootSum⟩ :=
                pairCheckMerklePath_extract3 epoch depth (layer + 1) nextCur rs (by dsimp [rs]; omega) t0 t1 t2
              rw [eq0] at h0; rw [eq1] at h1; rw [eq2] at h2
              dsimp only at h0 h1 h2
              injection h0 with ho0; injection h1 with ho1; injection h2 with ho2
              let bVal := vcSum3 (fun i => (lv i).bitShare)
              let sibVal := vcSumLane6_3 (fun i => (lv i).sibShare)
              refine ⟨root3, bz :: bzs3, (bVal, sibVal) :: stepsRest,
                by simp [hSLen], ho0.symm, ho1.symm, ho2.symm, ?_, ?_⟩
              · intro hAllZ p hp
                rcases List.mem_cons.mp hp with rfl | hpRest
                · have h0Bz : vcSum3 bz = Goldilocks.zero := hAllZ bz (.head bzs3)
                  rw [hBzEq] at h0Bz
                  exact goldilocks_bool_gate_zero_or_one bVal h0Bz
                · exact hBoolRest (fun z hz => hAllZ z (.tail bz hz)) p hpRest
              · dsimp only [evalVcMerklePathFrom]
                rw [← hNextEq]
                exact hRootSum


/-! ### §4.4 Round-1 View Commitments, PRG Tape Replay, Strict Ascending `Nodup`, Fiat-Shamir & 3-Challenge Extraction -/

/-- Concrete 3-party tuple (`DecidableEq`-friendly carrier isomorphic to `Fin 3 → α`). -/
structure Triple3 (α : Type) where
  s0 : α
  s1 : α
  s2 : α
  deriving DecidableEq, Repr

def Triple3.get {α : Type} (t : Triple3 α) : Fin 3 → α
  | ⟨0, _⟩ => t.s0
  | ⟨1, _⟩ => t.s1
  | ⟨2, _⟩ => t.s2

def Triple3.ofFn {α : Type} (f : Fin 3 → α) : Triple3 α :=
  ⟨f 0, f 1, f 2⟩

private theorem Triple3.get_ofFn {α : Type} (f : Fin 3 → α) (i : Fin 3) :
    (Triple3.ofFn f).get i = f i := by
  rcases i with ⟨iv, hiv⟩
  have hc : iv = 0 ∨ iv = 1 ∨ iv = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rfl

private theorem Triple3.ofFn_get {α : Type} (t : Triple3 α) :
    Triple3.ofFn t.get = t := by
  cases t; rfl

private theorem Triple3.ext_get {α : Type} {a b : Triple3 α}
    (h : ∀ i : Fin 3, a.get i = b.get i) : a = b := by
  cases a; cases b
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  dsimp only [Triple3.get] at h0 h1 h2
  subst h0 h1 h2; rfl

/-- Single party's full ZKBoo repetition view (`blind_vc.rs:258-325, 1805-1905`), carrying
    explicit 32-byte PRG `tapeSeed`, 32-byte broadcast commitment `commitSalt`, secret-shared
    input wires, and all gate transcripts across `attrSponge`, `merkleLevels`, `presSponge`, and `scopeSponge`. -/
structure PartyVcRepView where
  tapeSeed : Vec UInt8 32
  commitSalt : Vec UInt8 32
  attrShares : List Goldilocks
  holderBlindShare : Lane4
  presBlindShare : Lane4
  attrSponge : PartySponge3PermView
  merkleLevels : List PartyMerkleLevelView
  presSponge : PartySponge3PermView
  scopeSponge : PartySponge3PermView
  deriving DecidableEq

/-- Extract the structured gate coin tape embedded inside `v` (`none` if round/path lengths mismatch). -/
def extractPartyGateCoins (treeDepth : Nat) (v : PartyVcRepView) : Option (PartyGateCoins treeDepth) :=
  match extractSponge3Coins v.attrSponge,
        extractSponge3Coins v.presSponge,
        extractSponge3Coins v.scopeSponge,
        extractMerklePathCoins treeDepth v.merkleLevels with
  | some ac, some pc, some sc, some mc => some ⟨ac, pc, sc, mc⟩
  | _, _, _, _ => none

/-- Verifier PRG replay check (`blind_vc.rs:365-366, 2203-2210`): every multiplication gate's
    randomness coin `r` inside `v` must match `prgExpand treeDepth repIdx partyIdx v.tapeSeed`. -/
def checkPartyPrgTape
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (treeDepth : Nat) (repIdx : Nat) (partyIdx : Fin 3) (v : PartyVcRepView) : Bool :=
  decide (extractPartyGateCoins treeDepth v = some (prgExpand treeDepth repIdx partyIdx v.tapeSeed))

/-- Single party's final output shares (`VC_FINAL_OUTPUTS = 18 + treeDepth`, `blind_vc.rs:2384-2385`). -/
structure VcPartyFinalOut where
  rootShare : Lane6
  presShare : Lane6
  scopeShare : Lane6
  boolZeroShares : List Goldilocks
  deriving DecidableEq, Repr

/-- All 3 parties' Round-1 final output shares (`final_outs_all3`, `blind_vc.rs:2366-2382`). -/
structure VcRepFinalOuts3 where
  rootShares : Triple3 Lane6
  presShares : Triple3 Lane6
  scopeShares : Triple3 Lane6
  boolZeroShares : List (Triple3 Goldilocks)
  deriving DecidableEq, Repr

def vcPartyFinalOutAt (fo : VcRepFinalOuts3) (i : Fin 3) : VcPartyFinalOut :=
  { rootShare := fo.rootShares.get i
    presShare := fo.presShares.get i
    scopeShare := fo.scopeShares.get i
    boolZeroShares := fo.boolZeroShares.map (fun t => t.get i) }

/-- Opened ZKBoo repetition proof (`OpenedBlindVcRep`, `blind_vc.rs:760-775, 2180-2415`, fixing `C0-3`):
    contains Fiat-Shamir challenge `e ∈ {0, 1, 2}`, full opened `PartyVcRepView` pair `(viewE, viewE1)`
    (with `tapeSeed` and `commitSalt`), the 3rd party's Round-1 `unopenedCommit`, and `finalOuts`. -/
structure OpenedBlindVcRep where
  e : Fin 3
  viewE : PartyVcRepView
  viewE1 : PartyVcRepView
  unopenedCommit : List UInt8
  finalOuts : VcRepFinalOuts3
  deriving DecidableEq

/-- Full 3-party pre-opening repetition bundle held by the prover in Round 1. -/
structure BlindVcRepTriple where
  views : Fin 3 → PartyVcRepView
  finalOuts : VcRepFinalOuts3

/-- Selective-disclosure presentation bundle (`BlindVcPresentation`, `blind_vc.rs:740-778`). -/
structure BlindVcPresentation where
  presentationNonce : Vec UInt8 32
  issuerEpoch : UInt64
  schemaId : UInt64
  accumulatorRoot : Lane6
  issuerRootTag : Vec UInt8 32
  verifierScopeLimbs : Lane4
  disclosedAttrs : List (Nat × Goldilocks)
  presCommit : Lane6
  scopeTag : Lane6
  openedReps : List OpenedBlindVcRep
  deriving DecidableEq

/-- Strict ascending + `< arity` disclosed attribute check (`blind_vc.rs:2131-2139`, fixing `C0-3`):
    enforced directly inside `verifyBlindVcPresentation` rather than assumed as an external theorem hypothesis. -/
def vcCheckDisclosedStrictAscAux (arity prev : Nat) : List (Nat × Goldilocks) → Bool
  | [] => true
  | (idx, _) :: rest =>
    decide (prev < idx) && decide (idx < arity) && vcCheckDisclosedStrictAscAux arity idx rest

def vcCheckDisclosedStrictAsc (arity : Nat) : List (Nat × Goldilocks) → Bool
  | [] => true
  | (idx, _) :: rest => decide (idx < arity) && vcCheckDisclosedStrictAscAux arity idx rest

private theorem vcCheckDisclosedStrictAscAux_gt :
    ∀ (arity prev : Nat) (xs : List (Nat × Goldilocks)),
      vcCheckDisclosedStrictAscAux arity prev xs = true →
      ∀ p ∈ xs, prev < p.1 ∧ p.1 < arity
  | _, _, [], _, _, hp => nomatch hp
  | arity, prev, (idx, val) :: rest, hOk, p, hp => by
    simp only [vcCheckDisclosedStrictAscAux, Bool.and_eq_true, decide_eq_true_eq] at hOk
    rcases hOk with ⟨⟨hPrev, hAr⟩, hRest⟩
    rcases List.mem_cons.mp hp with rfl | hpTail
    · exact ⟨hPrev, hAr⟩
    · obtain ⟨hGt, hLt⟩ := vcCheckDisclosedStrictAscAux_gt arity idx rest hRest p hpTail
      exact ⟨Nat.lt_trans hPrev hGt, hLt⟩

private theorem vcCheckDisclosedStrictAscAux_nodup :
    ∀ (arity prev : Nat) (xs : List (Nat × Goldilocks)),
      vcCheckDisclosedStrictAscAux arity prev xs = true →
      (xs.map Prod.fst).Nodup
  | _, _, [], _ => List.Pairwise.nil
  | arity, prev, (idx, _) :: rest, hOk => by
    simp only [vcCheckDisclosedStrictAscAux, Bool.and_eq_true, decide_eq_true_eq] at hOk
    rcases hOk with ⟨_, hRest⟩
    dsimp only [List.map]
    apply List.nodup_cons.mpr
    refine ⟨?_, vcCheckDisclosedStrictAscAux_nodup arity idx rest hRest⟩
    intro hMem
    obtain ⟨p, hpMem, hpEq⟩ := List.mem_map.mp hMem
    obtain ⟨hGt, _⟩ := vcCheckDisclosedStrictAscAux_gt arity idx rest hRest p hpMem
    omega

/-- Verifier-enforced strict ascending check implies both `< arity` bounds AND `(disclosed.map Prod.fst).Nodup`. -/
theorem vcCheckDisclosedStrictAsc_bounds_and_nodup {arity : Nat} {disclosed : List (Nat × Goldilocks)}
    (hAsc : vcCheckDisclosedStrictAsc arity disclosed = true) :
    (∀ p ∈ disclosed, p.1 < arity) ∧ (disclosed.map Prod.fst).Nodup := by
  cases disclosed with
  | nil => exact ⟨(fun _ hp => nomatch hp), List.Pairwise.nil⟩
  | cons hd tl =>
    rcases hd with ⟨idx, val⟩
    simp only [vcCheckDisclosedStrictAsc, Bool.and_eq_true, decide_eq_true_eq] at hAsc
    rcases hAsc with ⟨hAr, hAux⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hpTl
      · exact hAr
      · exact (vcCheckDisclosedStrictAscAux_gt arity idx tl hAux p hpTl).2
    · dsimp only [List.map]
      apply List.nodup_cons.mpr
      refine ⟨?_, vcCheckDisclosedStrictAscAux_nodup arity idx tl hAux⟩
      intro hMem
      obtain ⟨p, hpMem, hpEq⟩ := List.mem_map.mp hMem
      obtain ⟨hGt, _⟩ := vcCheckDisclosedStrictAscAux_gt arity idx tl hAux p hpMem
      omega

/-- **`#tooth` (`tooth_duplicate_disclosed_indices_rejected`, `C0-3`)**:
    Bounds-only checking (`∀ p ∈ xs, p.1 < 2`) accepts duplicate contradictory disclosures
    `[(0, v₁), (0, v₂)]` and unsorted `[(1, v₁), (0, v₂)]`, whereas `vcCheckDisclosedStrictAsc`
    deterministically rejects both! -/
theorem tooth_duplicate_disclosed_indices_rejected (v₁ v₂ : Goldilocks) :
    (∀ p ∈ ([(0, v₁), (0, v₂)] : List (Nat × Goldilocks)), p.1 < 2) ∧
    vcCheckDisclosedStrictAsc 2 [(0, v₁), (0, v₂)] = false ∧
    vcCheckDisclosedStrictAsc 2 [(1, v₁), (0, v₂)] = false := by
  refine ⟨?_, rfl, rfl⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp1
  · dsimp only; decide
  · rcases List.mem_cons.mp hp1 with rfl | hp2
    · dsimp only; decide
    · cases hp2

def vcLookupDisclosed : List (Nat × Goldilocks) → Nat → Option Goldilocks
  | [], _ => none
  | (i, v) :: rest, idx => if i = idx then some v else vcLookupDisclosed rest idx

private theorem vcLookupDisclosed_eq_some_of_nodup :
    ∀ {disclosed : List (Nat × Goldilocks)} {idx : Nat} {val : Goldilocks},
      (disclosed.map Prod.fst).Nodup →
      (idx, val) ∈ disclosed →
      vcLookupDisclosed disclosed idx = some val
  | [], _, _, _, hMem => nomatch hMem
  | (i, v) :: rest, idx, val, hNodup, hMem => by
    dsimp only [List.map] at hNodup
    rcases List.nodup_cons.mp hNodup with ⟨hiNotMem, hRestNodup⟩
    rcases List.mem_cons.mp hMem with hEq | hTail
    · injection hEq with hi hv
      subst hi hv
      simp [vcLookupDisclosed]
    · have hNe : i ≠ idx := by
        intro hEqIdx
        subst hEqIdx
        exact hiNotMem (List.mem_map.mpr ⟨(i, val), hTail, rfl⟩)
      simp only [vcLookupDisclosed, ite_false_of hNe]
      exact vcLookupDisclosed_eq_some_of_nodup hRestNodup hTail

private theorem vcLookupDisclosed_mem :
    ∀ {disclosed : List (Nat × Goldilocks)} {idx : Nat} {val : Goldilocks},
      vcLookupDisclosed disclosed idx = some val →
      (idx, val) ∈ disclosed
  | [], _, _, h => by cases h
  | (i, v) :: rest, idx, val, h => by
    unfold vcLookupDisclosed at h
    if hEq : i = idx then
      rw [ite_true_of hEq] at h
      injection h with hv
      subst hEq hv
      exact .head rest
    else
      rw [ite_false_of hEq] at h
      exact .tail _ (vcLookupDisclosed_mem h)

/-- Publicly pinned share value for a disclosed attribute (`party 0 => val, party 1,2 => 0`). -/
def vcExpectedDisclosedShare (partyIdx : Fin 3) (val : Goldilocks) : Goldilocks :=
  if partyIdx = 0 then val else Goldilocks.zero

def vcCheckPartyDisclosedShares (partyIdx : Fin 3) (attrShares : List Goldilocks) :
    List (Nat × Goldilocks) → Bool
  | [] => true
  | (idx, val) :: rest =>
    decide (attrShares[idx]? = some (vcExpectedDisclosedShare partyIdx val)) &&
    vcCheckPartyDisclosedShares partyIdx attrShares rest

private theorem vcCheckPartyDisclosedShares_mem {partyIdx : Fin 3} {attrShares : List Goldilocks}
    {disclosed : List (Nat × Goldilocks)}
    (hOk : vcCheckPartyDisclosedShares partyIdx attrShares disclosed = true) :
    ∀ p ∈ disclosed, attrShares[p.1]? = some (vcExpectedDisclosedShare partyIdx p.2) := by
  induction disclosed with
  | nil => intro _ hp; nomatch hp
  | cons hd tl ih =>
    rcases hd with ⟨idx, val⟩
    simp only [vcCheckPartyDisclosedShares, Bool.and_eq_true, decide_eq_true_eq] at hOk
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hpTl
    · exact hOk.1
    · exact ih hOk.2 p hpTl

/-- Domain tag `"QSAG.VC.VIEW_COM.V1"` (`blind_vc.rs:516`, 19 bytes). -/
def vcViewCommitTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x56, 0x43, 0x2E, 0x56, 0x49,
   0x45, 0x57, 0x5F, 0x43, 0x4F, 0x4D, 0x2E, 0x56, 0x31]

/-- Domain tag `"QSAG.COMMIT.V1"` (14 bytes) for salted Round-1 party-view commitments. -/
def vcMpcCommitTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x43, 0x4F, 0x4D, 0x4D, 0x49, 0x54, 0x2E, 0x56, 0x31]

/-- Domain tag `"QSAG.BLIND_VC.SD_LIMBO.V1"` (`blind_vc.rs:3224, 3822`, 25 bytes). -/
def vcSdZkDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x42, 0x4C, 0x49, 0x4E, 0x44, 0x5F,
   0x56, 0x43, 0x2E, 0x53, 0x44, 0x5F, 0x4C, 0x49, 0x4D, 0x42, 0x4F,
   0x2E, 0x56, 0x31]

/-- Alias for `"QSAG.BLIND_VC.SD_LIMBO.V1"` (`blind_vc.rs:3224, 3822`). -/
abbrev vcSdLimboDomainTag : List UInt8 := vcSdZkDomainTag

/-- Domain tag `"QSAG.MLDSA.NONCE_BURN.V2"` (`threshold_mldsa.rs:419`, 24 bytes) for durable
    nonce-burn MAC records (superseding retired `"QSAG.MLDSA.MASK_NONCE.V1"`). -/
def mldsaNonceBurnDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x4D, 0x4C, 0x44, 0x53, 0x41, 0x2E, 0x4E,
   0x4F, 0x4E, 0x43, 0x45, 0x5F, 0x42, 0x55, 0x52, 0x4E, 0x2E, 0x56, 0x32]

/-- Length-framed `cshake256_framed_32` preimage under `"QSAG.MLDSA.NONCE_BURN.V2"`. -/
def mldsaNonceBurnPreimage (macKey lockId body : List UInt8) : List UInt8 :=
  cshake256FramedPreimage mldsaNonceBurnDomainTag [macKey, lockId, body]

/-- Profile tag `"QSAG.VC.PROFILE.Quantum128:438"` (`blind_vc.rs:1746, 2166`, 30 bytes). -/
def vcProfileQuantumTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x56, 0x43, 0x2E, 0x50, 0x52,
   0x4F, 0x46, 0x49, 0x4C, 0x45, 0x2E, 0x51, 0x75, 0x61, 0x6E,
   0x74, 0x75, 0x6D, 0x31, 0x32, 0x38, 0x3A, 0x34, 0x33, 0x38]

/-- Fiat-Shamir transcript tags `"QSAG.FS.INIT.V1"`, `"QSAG.FS.ABSORB.V1"`, `"QSAG.FS.SQUEEZE.V1"`. -/
def vcFsInitTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x46, 0x53, 0x2E, 0x49, 0x4E, 0x49, 0x54, 0x2E, 0x56, 0x31]

def vcFsAbsorbTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x46, 0x53, 0x2E, 0x41, 0x42, 0x53, 0x4F, 0x52, 0x42, 0x2E, 0x56, 0x31]

def vcFsSqueezeTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x46, 0x53, 0x2E, 0x53, 0x51, 0x55, 0x45, 0x45, 0x5A, 0x45, 0x2E, 0x56, 0x31]

/-- Right-associated `u64_le`-framed chain hash over arbitrary-length frame lists:
    every sponge invocation absorbs `≤ 3` bounded frames (`< 256 ^ 8`), avoiding any upper-bound
    hypotheses on list length (`poseidon2InitialExtConsts.length`, `treeDepth`, `repetitions`). -/
def foldFramesHash (H : List UInt8 → List UInt8) (tag : List UInt8) : List (List UInt8) → List UInt8
  | [] => H (cshake256FramedPreimage tag [])
  | x :: xs => H (cshake256FramedPreimage tag [[0x01], x, foldFramesHash H tag xs])

private theorem foldFramesHash_length_lt {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8) (tag : List UInt8) (xs : List (List UInt8)) :
    (foldFramesHash H tag xs).length < 256 ^ 8 := by
  cases xs <;> simp only [foldFramesHash] <;> exact hHLen _

/-- Constructive collision reduction (`0 Classical.choice`) for `foldFramesHash`:
    whenever `∀ m, (H m).length < 256 ^ 8` and leaf frames satisfy `< 256 ^ 8`, any `xs ≠ ys`
    colliding under `foldFramesHash H tag` exhibit an explicit `H`-collision `m₁ ≠ m₂ ∧ H m₁ = H m₂`. -/
def foldFramesHashCollision
    {H : List UInt8 → List UInt8} {tag : List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {xs ys : List (List UInt8)}
    (hxB : ∀ f ∈ xs, f.length < 256 ^ 8)
    (hyB : ∀ g ∈ ys, g.length < 256 ^ 8)
    (hNe : xs ≠ ys)
    (hEq : foldFramesHash H tag xs = foldFramesHash H tag ys) :
    Σ m₁ : List UInt8, {m₂ : List UInt8 // m₁ ≠ m₂ ∧ H m₁ = H m₂} := by
  have h1Lt : ([0x01] : List UInt8).length < 256 ^ 8 := by simp only [List.length]; decide
  match xs, ys with
  | [], [] => exact False.elim (hNe rfl)
  | [], y :: ys =>
      simp only [foldFramesHash] at hEq
      refine ⟨cshake256FramedPreimage tag [],
              cshake256FramedPreimage tag [[0x01], y, foldFramesHash H tag ys], ?_, hEq⟩
      intro hPre
      have hR : ∀ g ∈ [[0x01], y, foldFramesHash H tag ys], g.length < 256 ^ 8 := by
        intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with h0 | h1 | h2 | h3
        · rw [h0]; exact h1Lt
        · rw [h1]; exact hyB y (.head ys)
        · rw [h2]; exact foldFramesHash_length_lt hHLen tag ys
        · cases h3
      have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp)
        (by intro _ hf; cases hf) hR hPre
      cases hFr
  | x :: xs, [] =>
      simp only [foldFramesHash] at hEq
      refine ⟨cshake256FramedPreimage tag [[0x01], x, foldFramesHash H tag xs],
              cshake256FramedPreimage tag [], ?_, hEq⟩
      intro hPre
      have hL : ∀ f ∈ [[0x01], x, foldFramesHash H tag xs], f.length < 256 ^ 8 := by
        intro f hf
        simp only [List.mem_cons] at hf
        rcases hf with h0 | h1 | h2 | h3
        · rw [h0]; exact h1Lt
        · rw [h1]; exact hxB x (.head xs)
        · rw [h2]; exact foldFramesHash_length_lt hHLen tag xs
        · cases h3
      have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp)
        hL (by intro _ hg; cases hg) hPre
      cases hFr
  | x :: xs, y :: ys =>
      simp only [foldFramesHash] at hEq
      let d₁ := foldFramesHash H tag xs
      let d₂ := foldFramesHash H tag ys
      have hL : ∀ f ∈ [[0x01], x, d₁], f.length < 256 ^ 8 := by
        intro f hf
        simp only [List.mem_cons] at hf
        rcases hf with h0 | h1 | h2 | h3
        · rw [h0]; exact h1Lt
        · rw [h1]; exact hxB x (.head xs)
        · rw [h2]; exact foldFramesHash_length_lt hHLen tag xs
        · cases h3
      have hR : ∀ g ∈ [[0x01], y, d₂], g.length < 256 ^ 8 := by
        intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with h0 | h1 | h2 | h3
        · rw [h0]; exact h1Lt
        · rw [h1]; exact hyB y (.head ys)
        · rw [h2]; exact foldFramesHash_length_lt hHLen tag ys
        · cases h3
      if hSub : d₁ = d₂ then
        if hx : x = y then
          have hTailNe : xs ≠ ys := fun h => hNe (by rw [hx, h])
          exact foldFramesHashCollision hHLen (fun f hf => hxB f (.tail x hf)) (fun g hg => hyB g (.tail y hg)) hTailNe hSub
        else
          refine ⟨cshake256FramedPreimage tag [[0x01], x, d₁],
                  cshake256FramedPreimage tag [[0x01], y, d₂], ?_, hEq⟩
          intro hPre
          have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hL hR hPre
          injection hFr with _ h1
          injection h1 with hxEq _
          exact hx hxEq
      else
        refine ⟨cshake256FramedPreimage tag [[0x01], x, d₁],
                cshake256FramedPreimage tag [[0x01], y, d₂], ?_, hEq⟩
        intro hPre
        have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hL hR hPre
        injection hFr with _ h1
        injection h1 with _ h2
        injection h2 with hdEq _
        exact hSub hdEq
termination_by xs.length

theorem foldFramesHash_collision_of_ne
    {H : List UInt8 → List UInt8} {tag : List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {xs ys : List (List UInt8)}
    (hxB : ∀ f ∈ xs, f.length < 256 ^ 8)
    (hyB : ∀ g ∈ ys, g.length < 256 ^ 8)
    (hNe : xs ≠ ys)
    (hEq : foldFramesHash H tag xs = foldFramesHash H tag ys) :
    ∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂ := by
  obtain ⟨m₁, m₂, h⟩ := foldFramesHashCollision hHLen hxB hyB hNe hEq
  exact ⟨m₁, m₂, h⟩

/-- Prefix-free structural frame serializer combinators (`∀ f, f.length ≤ 48 < 256 ^ 8`). -/
private def serListFrames {α : Type} (serElem : α → List (List UInt8)) : List α → List (List UInt8)
  | [] => [[0x00]]
  | x :: xs => [0x01] :: (serElem x ++ serListFrames serElem xs)

private theorem serListFrames_len_lt {α : Type} {serElem : α → List (List UInt8)}
    (hElem : ∀ (a : α) (f : List UInt8), f ∈ serElem a → f.length < 256 ^ 8) :
    ∀ (xs : List α) (f : List UInt8), f ∈ serListFrames serElem xs → f.length < 256 ^ 8
  | [], f, hf => by
    rcases List.mem_cons.mp hf with rfl | hNil
    · simp only [List.length]; decide
    · cases hNil
  | x :: xs, f, hf => by
    rcases List.mem_cons.mp hf with rfl | hRest
    · simp only [List.length]; decide
    · rcases List.mem_append.mp hRest with hE | hT
      · exact hElem x f hE
      · exact serListFrames_len_lt hElem xs f hT

private theorem serListFrames_prefix_inj {α : Type} {serElem : α → List (List UInt8)}
    (hElemInj : ∀ (a₁ a₂ : α) (r₁ r₂ : List (List UInt8)),
      serElem a₁ ++ r₁ = serElem a₂ ++ r₂ → a₁ = a₂ ∧ r₁ = r₂) :
    ∀ (xs₁ xs₂ : List α) (r₁ r₂ : List (List UInt8)),
      serListFrames serElem xs₁ ++ r₁ = serListFrames serElem xs₂ ++ r₂ → xs₁ = xs₂ ∧ r₁ = r₂
  | [], [], r₁, r₂, h => by
    dsimp only [serListFrames, List.cons_append, List.nil_append] at h
    injection h with _ hr
    exact ⟨rfl, hr⟩
  | [], _ :: _, _, _, h => by
    dsimp only [serListFrames, List.cons_append, List.nil_append] at h
    injection h with hTag _; cases hTag
  | _ :: _, [], _, _, h => by
    dsimp only [serListFrames, List.cons_append, List.nil_append] at h
    injection h with hTag _; cases hTag
  | x :: xs, y :: ys, r₁, r₂, h => by
    dsimp only [serListFrames, List.cons_append] at h
    injection h with _ hBody
    rw [List.append_assoc, List.append_assoc] at hBody
    obtain ⟨hxy, hRest⟩ := hElemInj x y _ _ hBody
    obtain ⟨hxs, hr⟩ := serListFrames_prefix_inj hElemInj xs ys r₁ r₂ hRest
    subst hxy hxs
    exact ⟨rfl, hr⟩

private def serGoldFrame (x : Goldilocks) : List (List UInt8) :=
  [encodeGoldilocksVecLe [x]]

private theorem serGoldFrame_inj {x y : Goldilocks} {r₁ r₂ : List (List UInt8)}
    (h : serGoldFrame x ++ r₁ = serGoldFrame y ++ r₂) : x = y ∧ r₁ = r₂ := by
  dsimp only [serGoldFrame, List.cons_append, List.nil_append] at h
  injection h with hx hr
  have hList := encodeGoldilocksVecLe_injective hx
  injection hList with hxy _
  exact ⟨hxy, hr⟩

private theorem serGoldFrame_len (x : Goldilocks) (f : List UInt8) (hf : f ∈ serGoldFrame x) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [encodeGoldilocksVecLe_length]; simp only [List.length]; decide
  · cases hNil

private def serLane4Frame (x : Lane4) : List (List UInt8) :=
  [encodeGoldilocksVecLe [x.x0, x.x1, x.x2, x.x3]]

private theorem serLane4Frame_inj {x y : Lane4} {r₁ r₂ : List (List UInt8)}
    (h : serLane4Frame x ++ r₁ = serLane4Frame y ++ r₂) : x = y ∧ r₁ = r₂ := by
  dsimp only [serLane4Frame, List.cons_append, List.nil_append] at h
  injection h with hx hr
  have hList := encodeGoldilocksVecLe_injective hx
  injection hList with h0 t1; injection t1 with h1 t2; injection t2 with h2 t3; injection t3 with h3 _
  exact ⟨Lane4.ext h0 h1 h2 h3, hr⟩

private theorem serLane4Frame_len (x : Lane4) (f : List UInt8) (hf : f ∈ serLane4Frame x) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [encodeGoldilocksVecLe_length]; simp only [List.length]; decide
  · cases hNil

private def serLane6Frame (x : Lane6) : List (List UInt8) :=
  [encodeGoldilocksVecLe [x.x0, x.x1, x.x2, x.x3, x.x4, x.x5]]

private theorem serLane6Frame_inj {x y : Lane6} {r₁ r₂ : List (List UInt8)}
    (h : serLane6Frame x ++ r₁ = serLane6Frame y ++ r₂) : x = y ∧ r₁ = r₂ := by
  dsimp only [serLane6Frame, List.cons_append, List.nil_append] at h
  injection h with hx hr
  have hList := encodeGoldilocksVecLe_injective hx
  injection hList with h0 t1; injection t1 with h1 t2; injection t2 with h2 t3
  injection t3 with h3 t4; injection t4 with h4 t5; injection t5 with h5 _
  exact ⟨Lane6.ext h0 h1 h2 h3 h4 h5, hr⟩

private theorem serLane6Frame_len (x : Lane6) (f : List UInt8) (hf : f ∈ serLane6Frame x) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [encodeGoldilocksVecLe_length]; simp only [List.length]; decide
  · cases hNil

private def serMulFrame (g : PartyMulView) : List (List UInt8) :=
  [encodeGoldilocksVecLe [g.r, g.out]]

private theorem serMulFrame_inj {a b : PartyMulView} {r₁ r₂ : List (List UInt8)}
    (h : serMulFrame a ++ r₁ = serMulFrame b ++ r₂) : a = b ∧ r₁ = r₂ := by
  dsimp only [serMulFrame, List.cons_append, List.nil_append] at h
  injection h with hx hr
  have hList := encodeGoldilocksVecLe_injective hx
  injection hList with h0 t1; injection t1 with h1 _
  refine ⟨?_, hr⟩
  rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩
  dsimp only at h0 h1
  rw [h0, h1]

private theorem serMulFrame_len (a : PartyMulView) (f : List UInt8) (hf : f ∈ serMulFrame a) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [encodeGoldilocksVecLe_length]; simp only [List.length]; decide
  · cases hNil

private def serSboxFrames (s : PartySboxView) : List (List UInt8) :=
  serMulFrame s.g1 ++ serMulFrame s.g2 ++ serMulFrame s.g3 ++ serMulFrame s.g4

private theorem serSboxFrames_inj {a b : PartySboxView} {r₁ r₂ : List (List UInt8)}
    (h : serSboxFrames a ++ r₁ = serSboxFrames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serSboxFrames at h
  simp only [List.append_assoc] at h
  rcases serMulFrame_inj h with ⟨e1, h1⟩
  rcases serMulFrame_inj h1 with ⟨e2, h2⟩
  rcases serMulFrame_inj h2 with ⟨e3, h3⟩
  rcases serMulFrame_inj h3 with ⟨e4, h4⟩
  refine ⟨?_, h4⟩
  rcases a with ⟨_, _, _, _⟩; rcases b with ⟨_, _, _, _⟩
  dsimp only at e1 e2 e3 e4
  rw [e1, e2, e3, e4]

private theorem serSboxFrames_len (s : PartySboxView) (f : List UInt8) (hf : f ∈ serSboxFrames s) :
    f.length < 256 ^ 8 := by
  unfold serSboxFrames at hf
  rcases List.mem_append.mp hf with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exact serMulFrame_len _ f h1
      · exact serMulFrame_len _ f h2
    · exact serMulFrame_len _ f h3
  · exact serMulFrame_len _ f h4

private def serExtRoundFrames (rv : PartyExtRoundView) : List (List UInt8) :=
  serSboxFrames rv.s0 ++ serSboxFrames rv.s1 ++ serSboxFrames rv.s2 ++ serSboxFrames rv.s3 ++
  serSboxFrames rv.s4 ++ serSboxFrames rv.s5 ++ serSboxFrames rv.s6 ++ serSboxFrames rv.s7 ++
  serSboxFrames rv.s8 ++ serSboxFrames rv.s9 ++ serSboxFrames rv.s10 ++ serSboxFrames rv.s11

private theorem serExtRoundFrames_inj {a b : PartyExtRoundView} {r₁ r₂ : List (List UInt8)}
    (h : serExtRoundFrames a ++ r₁ = serExtRoundFrames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serExtRoundFrames at h
  simp only [List.append_assoc] at h
  rcases serSboxFrames_inj h with ⟨e0, h0⟩; rcases serSboxFrames_inj h0 with ⟨e1, h1⟩
  rcases serSboxFrames_inj h1 with ⟨e2, h2⟩; rcases serSboxFrames_inj h2 with ⟨e3, h3⟩
  rcases serSboxFrames_inj h3 with ⟨e4, h4⟩; rcases serSboxFrames_inj h4 with ⟨e5, h5⟩
  rcases serSboxFrames_inj h5 with ⟨e6, h6⟩; rcases serSboxFrames_inj h6 with ⟨e7, h7⟩
  rcases serSboxFrames_inj h7 with ⟨e8, h8⟩; rcases serSboxFrames_inj h8 with ⟨e9, h9⟩
  rcases serSboxFrames_inj h9 with ⟨e10, h10⟩; rcases serSboxFrames_inj h10 with ⟨e11, h11⟩
  refine ⟨?_, h11⟩
  rcases a with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases b with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  dsimp only at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]

private theorem serExtRoundFrames_len (rv : PartyExtRoundView) (f : List UInt8)
    (hf : f ∈ serExtRoundFrames rv) : f.length < 256 ^ 8 := by
  unfold serExtRoundFrames at hf
  simp only [List.mem_append] at hf
  rcases hf with (((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11)
  · exact serSboxFrames_len _ f h0
  · exact serSboxFrames_len _ f h1
  · exact serSboxFrames_len _ f h2
  · exact serSboxFrames_len _ f h3
  · exact serSboxFrames_len _ f h4
  · exact serSboxFrames_len _ f h5
  · exact serSboxFrames_len _ f h6
  · exact serSboxFrames_len _ f h7
  · exact serSboxFrames_len _ f h8
  · exact serSboxFrames_len _ f h9
  · exact serSboxFrames_len _ f h10
  · exact serSboxFrames_len _ f h11

private def serPerm12Frames (pv : PartyPerm12View) : List (List UInt8) :=
  serListFrames serExtRoundFrames pv.initExt ++
  serListFrames serSboxFrames pv.internal ++
  serListFrames serExtRoundFrames pv.termExt

private theorem serPerm12Frames_inj {a b : PartyPerm12View} {r₁ r₂ : List (List UInt8)}
    (h : serPerm12Frames a ++ r₁ = serPerm12Frames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serPerm12Frames at h
  simp only [List.append_assoc] at h
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serExtRoundFrames_inj) a.initExt b.initExt _ _ h with ⟨e1, h1⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serSboxFrames_inj) a.internal b.internal _ _ h1 with ⟨e2, h2⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serExtRoundFrames_inj) a.termExt b.termExt _ _ h2 with ⟨e3, h3⟩
  refine ⟨?_, h3⟩
  rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩
  dsimp only at e1 e2 e3
  rw [e1, e2, e3]

private theorem serPerm12Frames_len (pv : PartyPerm12View) (f : List UInt8)
    (hf : f ∈ serPerm12Frames pv) : f.length < 256 ^ 8 := by
  unfold serPerm12Frames at hf
  simp only [List.mem_append] at hf
  rcases hf with (h1 | h2) | h3
  · exact serListFrames_len_lt serExtRoundFrames_len _ f h1
  · exact serListFrames_len_lt serSboxFrames_len _ f h2
  · exact serListFrames_len_lt serExtRoundFrames_len _ f h3

private def serSponge3Frames (sv : PartySponge3PermView) : List (List UInt8) :=
  serPerm12Frames sv.perm1 ++ serPerm12Frames sv.perm2 ++ serPerm12Frames sv.perm3

private theorem serSponge3Frames_inj {a b : PartySponge3PermView} {r₁ r₂ : List (List UInt8)}
    (h : serSponge3Frames a ++ r₁ = serSponge3Frames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serSponge3Frames at h
  simp only [List.append_assoc] at h
  rcases serPerm12Frames_inj h with ⟨e1, h1⟩
  rcases serPerm12Frames_inj h1 with ⟨e2, h2⟩
  rcases serPerm12Frames_inj h2 with ⟨e3, h3⟩
  refine ⟨?_, h3⟩
  rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩
  dsimp only at e1 e2 e3
  rw [e1, e2, e3]

private theorem serSponge3Frames_len (sv : PartySponge3PermView) (f : List UInt8)
    (hf : f ∈ serSponge3Frames sv) : f.length < 256 ^ 8 := by
  unfold serSponge3Frames at hf
  simp only [List.mem_append] at hf
  rcases hf with (h1 | h2) | h3
  · exact serPerm12Frames_len _ f h1
  · exact serPerm12Frames_len _ f h2
  · exact serPerm12Frames_len _ f h3

private def serMerkleLevelFrames (lv : PartyMerkleLevelView) : List (List UInt8) :=
  serGoldFrame lv.bitShare ++ serLane6Frame lv.sibShare ++
  serMulFrame lv.boolGate ++ serMulFrame lv.sel0 ++ serMulFrame lv.sel1 ++
  serMulFrame lv.sel2 ++ serMulFrame lv.sel3 ++ serMulFrame lv.sel4 ++
  serMulFrame lv.sel5 ++ serSponge3Frames lv.hashView

private theorem serMerkleLevelFrames_inj {a b : PartyMerkleLevelView} {r₁ r₂ : List (List UInt8)}
    (h : serMerkleLevelFrames a ++ r₁ = serMerkleLevelFrames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serMerkleLevelFrames at h
  simp only [List.append_assoc] at h
  rcases serGoldFrame_inj h with ⟨eb, h0⟩
  rcases serLane6Frame_inj h0 with ⟨es, h1⟩
  rcases serMulFrame_inj h1 with ⟨ebg, h2⟩
  rcases serMulFrame_inj h2 with ⟨e0, h3⟩; rcases serMulFrame_inj h3 with ⟨e1, h4⟩
  rcases serMulFrame_inj h4 with ⟨e2, h5⟩; rcases serMulFrame_inj h5 with ⟨e3, h6⟩
  rcases serMulFrame_inj h6 with ⟨e4, h7⟩; rcases serMulFrame_inj h7 with ⟨e5, h8⟩
  rcases serSponge3Frames_inj h8 with ⟨eh, h9⟩
  refine ⟨?_, h9⟩
  rcases a with ⟨_, _, _, _, _, _, _, _, _, _⟩
  rcases b with ⟨_, _, _, _, _, _, _, _, _, _⟩
  dsimp only at eb es ebg e0 e1 e2 e3 e4 e5 eh
  rw [eb, es, ebg, e0, e1, e2, e3, e4, e5, eh]

private theorem serMerkleLevelFrames_len (lv : PartyMerkleLevelView) (f : List UInt8)
    (hf : f ∈ serMerkleLevelFrames lv) : f.length < 256 ^ 8 := by
  unfold serMerkleLevelFrames at hf
  simp only [List.mem_append] at hf
  rcases hf with (((((((((hb | hs) | hbg) | h0) | h1) | h2) | h3) | h4) | h5) | hh)
  · exact serGoldFrame_len _ f hb
  · exact serLane6Frame_len _ f hs
  · exact serMulFrame_len _ f hbg
  · exact serMulFrame_len _ f h0
  · exact serMulFrame_len _ f h1
  · exact serMulFrame_len _ f h2
  · exact serMulFrame_len _ f h3
  · exact serMulFrame_len _ f h4
  · exact serMulFrame_len _ f h5
  · exact serSponge3Frames_len _ f hh

private def serVec32Frame (v : Vec UInt8 32) : List (List UInt8) := [v.toList]

private theorem serVec32Frame_inj {a b : Vec UInt8 32} {r₁ r₂ : List (List UInt8)}
    (h : serVec32Frame a ++ r₁ = serVec32Frame b ++ r₂) : a = b ∧ r₁ = r₂ := by
  dsimp only [serVec32Frame, List.cons_append, List.nil_append] at h
  injection h with hv hr
  exact ⟨Vec.toList_injective hv, hr⟩

private theorem serVec32Frame_len (a : Vec UInt8 32) (f : List UInt8) (hf : f ∈ serVec32Frame a) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [Vec.toList_length]; decide
  · cases hNil

/-- Full injective frame serialization of `(v.tapeSeed, v.attrShares, v.holderBlindShare,
    v.presBlindShare, v.attrSponge, v.merkleLevels, v.presSponge, v.scopeSponge, partyOut)`
    for `"QSAG.VC.VIEW_COM.V1"` (`digest_party_view`, `blind_vc.rs:514-530, 2386-2387`). -/
def serPartyViewDigestFrames (v : PartyVcRepView) (fo : VcPartyFinalOut) : List (List UInt8) :=
  serVec32Frame v.tapeSeed ++
  serListFrames serGoldFrame v.attrShares ++
  serLane4Frame v.holderBlindShare ++
  serLane4Frame v.presBlindShare ++
  serSponge3Frames v.attrSponge ++
  serListFrames serMerkleLevelFrames v.merkleLevels ++
  serSponge3Frames v.presSponge ++
  serSponge3Frames v.scopeSponge ++
  serLane6Frame fo.rootShare ++
  serLane6Frame fo.presShare ++
  serLane6Frame fo.scopeShare ++
  serListFrames serGoldFrame fo.boolZeroShares

private theorem serPartyViewDigestFrames_len (v : PartyVcRepView) (fo : VcPartyFinalOut) :
    ∀ f ∈ serPartyViewDigestFrames v fo, f.length < 256 ^ 8 := by
  intro f hf
  unfold serPartyViewDigestFrames at hf
  simp only [List.mem_append] at hf
  rcases hf with (((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11)
  · exact serVec32Frame_len _ f h0
  · exact serListFrames_len_lt serGoldFrame_len _ f h1
  · exact serLane4Frame_len _ f h2
  · exact serLane4Frame_len _ f h3
  · exact serSponge3Frames_len _ f h4
  · exact serListFrames_len_lt serMerkleLevelFrames_len _ f h5
  · exact serSponge3Frames_len _ f h6
  · exact serSponge3Frames_len _ f h7
  · exact serLane6Frame_len _ f h8
  · exact serLane6Frame_len _ f h9
  · exact serLane6Frame_len _ f h10
  · exact serListFrames_len_lt serGoldFrame_len _ f h11

/-- Two party views with identical `commitSalt` and identical `serPartyViewDigestFrames` are equal. -/
private theorem serPartyViewDigestFrames_injective
    {v₁ v₂ : PartyVcRepView} {fo₁ fo₂ : VcPartyFinalOut}
    (hSalt : v₁.commitSalt = v₂.commitSalt)
    (hEq : serPartyViewDigestFrames v₁ fo₁ = serPartyViewDigestFrames v₂ fo₂) :
    v₁ = v₂ ∧ fo₁ = fo₂ := by
  have hApp : serPartyViewDigestFrames v₁ fo₁ ++ [] = serPartyViewDigestFrames v₂ fo₂ ++ [] := by
    simp [hEq]
  unfold serPartyViewDigestFrames at hApp
  simp only [List.append_assoc] at hApp
  rcases serVec32Frame_inj hApp with ⟨eSeed, h0⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serGoldFrame_inj) _ _ _ _ h0 with ⟨eAttrs, h1⟩
  rcases serLane4Frame_inj h1 with ⟨eHb, h2⟩
  rcases serLane4Frame_inj h2 with ⟨ePb, h3⟩
  rcases serSponge3Frames_inj h3 with ⟨eAs, h4⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serMerkleLevelFrames_inj) _ _ _ _ h4 with ⟨eMk, h5⟩
  rcases serSponge3Frames_inj h5 with ⟨ePs, h6⟩
  rcases serSponge3Frames_inj h6 with ⟨eSs, h7⟩
  rcases serLane6Frame_inj h7 with ⟨eFr, h8⟩
  rcases serLane6Frame_inj h8 with ⟨eFp, h9⟩
  rcases serLane6Frame_inj h9 with ⟨eFs, h10⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serGoldFrame_inj) _ _ _ _ h10 with ⟨eFb, _⟩
  refine ⟨?_, ?_⟩
  · rcases v₁ with ⟨_, _, _, _, _, _, _, _, _⟩
    rcases v₂ with ⟨_, _, _, _, _, _, _, _, _⟩
    dsimp only at hSalt eSeed eAttrs eHb ePb eAs eMk ePs eSs
    rw [hSalt, eSeed, eAttrs, eHb, ePb, eAs, eMk, ePs, eSs]
  · rcases fo₁ with ⟨_, _, _, _⟩
    rcases fo₂ with ⟨_, _, _, _⟩
    dsimp only at eFr eFp eFs eFb
    rw [eFr, eFp, eFs, eFb]

/-- `"QSAG.VC.VIEW_COM.V1"` party-view digest (`digest_party_view`, `blind_vc.rs:514-530`). -/
def vcViewDigest (H : List UInt8 → List UInt8) (v : PartyVcRepView) (fo : VcPartyFinalOut) : List UInt8 :=
  foldFramesHash H vcViewCommitTag (serPartyViewDigestFrames v fo)

/-- Salted `"QSAG.COMMIT.V1"` Round-1 broadcast commitment (`commit_mpc_broadcast`, `blind_vc.rs:2388-2401`). -/
def vcCommitPartyViewPreimage (presNonce : Vec UInt8 32) (repIdx : Nat) (partyIdx : Fin 3)
    (viewDigest : List UInt8) (salt : Vec UInt8 32) : List UInt8 :=
  cshake256FramedPreimage vcMpcCommitTag
    [presNonce.toList, encodeNatLeBytes 8 repIdx, [UInt8.ofNat partyIdx.val], viewDigest, salt.toList]

def vcCommitPartyView (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (partyIdx : Fin 3) (v : PartyVcRepView) (fo : VcPartyFinalOut) : List UInt8 :=
  H (vcCommitPartyViewPreimage presNonce repIdx partyIdx (vcViewDigest H v fo) v.commitSalt)

/-- Constructive commitment binding (`0 Classical.choice`): any `(v₁, fo₁) ≠ (v₂, fo₂)` colliding
    on `vcCommitPartyView` constructively exhibit an explicit `H`-collision under either
    `"QSAG.COMMIT.V1"` or `"QSAG.VC.VIEW_COM.V1"`. -/
def vcCommitPartyViewCollision
    {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {presNonce : Vec UInt8 32} {repIdx : Nat} {partyIdx : Fin 3}
    {v₁ v₂ : PartyVcRepView} {fo₁ fo₂ : VcPartyFinalOut}
    (hNe : (v₁, fo₁) ≠ (v₂, fo₂))
    (hComEq : vcCommitPartyView H presNonce repIdx partyIdx v₁ fo₁ =
              vcCommitPartyView H presNonce repIdx partyIdx v₂ fo₂) :
    Σ m₁ : List UInt8, {m₂ : List UInt8 // m₁ ≠ m₂ ∧ H m₁ = H m₂} := by
  let d₁ := vcViewDigest H v₁ fo₁
  let d₂ := vcViewDigest H v₂ fo₂
  let pre₁ := vcCommitPartyViewPreimage presNonce repIdx partyIdx d₁ v₁.commitSalt
  let pre₂ := vcCommitPartyViewPreimage presNonce repIdx partyIdx d₂ v₂.commitSalt
  have hPreFrames : ∀ (d : List UInt8) (s : Vec UInt8 32),
      d.length < 256 ^ 8 →
      ∀ f ∈ [presNonce.toList, encodeNatLeBytes 8 repIdx, [UInt8.ofNat partyIdx.val], d, s.toList],
        f.length < 256 ^ 8 := by
    intro d s hd f hf
    rcases List.mem_cons.mp hf with rfl | h1
    · rw [Vec.toList_length]; decide
    · rcases List.mem_cons.mp h1 with rfl | h2
      · rw [encodeNatLeBytes_length]; decide
      · rcases List.mem_cons.mp h2 with rfl | h3
        · simp only [List.length]; decide
        · rcases List.mem_cons.mp h3 with rfl | h4
          · exact hd
          · rcases List.mem_cons.mp h4 with rfl | h5
            · rw [Vec.toList_length]; decide
            · cases h5
  if hPreEq : pre₁ = pre₂ then
    have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp)
      (hPreFrames d₁ v₁.commitSalt (hHLen _))
      (hPreFrames d₂ v₂.commitSalt (hHLen _)) hPreEq
    injection hFr with _ t1; injection t1 with _ t2; injection t2 with _ t3
    injection t3 with hdEq t4; injection t4 with hSaltList _
    have hSaltEq : v₁.commitSalt = v₂.commitSalt := Vec.toList_injective hSaltList
    have hFramesNe : serPartyViewDigestFrames v₁ fo₁ ≠ serPartyViewDigestFrames v₂ fo₂ := by
      intro hSerEq
      obtain ⟨hv, hfo⟩ := serPartyViewDigestFrames_injective hSaltEq hSerEq
      exact hNe (by rw [hv, hfo])
    exact foldFramesHashCollision hHLen
      (serPartyViewDigestFrames_len v₁ fo₁)
      (serPartyViewDigestFrames_len v₂ fo₂) hFramesNe hdEq
  else
    exact ⟨pre₁, pre₂, hPreEq, hComEq⟩

theorem vcCommitPartyView_binding
    {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {presNonce : Vec UInt8 32} {repIdx : Nat} {partyIdx : Fin 3}
    {v₁ v₂ : PartyVcRepView} {fo₁ fo₂ : VcPartyFinalOut}
    (hNe : (v₁, fo₁) ≠ (v₂, fo₂))
    (hComEq : vcCommitPartyView H presNonce repIdx partyIdx v₁ fo₁ =
              vcCommitPartyView H presNonce repIdx partyIdx v₂ fo₂) :
    ∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂ := by
  obtain ⟨m₁, m₂, h⟩ := vcCommitPartyViewCollision hHLen hNe hComEq
  exact ⟨m₁, m₂, h⟩

/-- Reconstruct Round-1 `(com_0, com_1, com_2)` from an opened repetition (`blind_vc.rs:2388-2406`). -/
def reconstructRepCommits (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (o : OpenedBlindVcRep) : Triple3 (List UInt8) :=
  let comE := vcCommitPartyView H presNonce repIdx o.e o.viewE (vcPartyFinalOutAt o.finalOuts o.e)
  let comE1 := vcCommitPartyView H presNonce repIdx (vcNextParty3 o.e) o.viewE1
    (vcPartyFinalOutAt o.finalOuts (vcNextParty3 o.e))
  Triple3.ofFn (mkParty3At o.e comE comE1 o.unopenedCommit)

def reconstructRepRound1 (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (o : OpenedBlindVcRep) : Triple3 (List UInt8) × VcRepFinalOuts3 :=
  (reconstructRepCommits H presNonce repIdx o, o.finalOuts)

def reconstructAllRepRound1 (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32) :
    Nat → List OpenedBlindVcRep → List (Triple3 (List UInt8) × VcRepFinalOuts3)
  | _, [] => []
  | repIdx, o :: rest => reconstructRepRound1 H presNonce repIdx o ::
      reconstructAllRepRound1 H presNonce (repIdx + 1) rest

/-- Open a 3-party repetition bundle at challenge `e ∈ {0, 1, 2}`. -/
def openBlindVcRep (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (triple : BlindVcRepTriple) (e : Fin 3) : OpenedBlindVcRep :=
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  { e := e
    viewE := triple.views e
    viewE1 := triple.views e1
    unopenedCommit := vcCommitPartyView H presNonce repIdx e2 (triple.views e2)
      (vcPartyFinalOutAt triple.finalOuts e2)
    finalOuts := triple.finalOuts }

private theorem reconstructRepRound1_openBlindVcRep (H : List UInt8 → List UInt8)
    (presNonce : Vec UInt8 32) (repIdx : Nat) (triple : BlindVcRepTriple) (e : Fin 3) :
    reconstructRepRound1 H presNonce repIdx (openBlindVcRep H presNonce repIdx triple e) =
      (Triple3.ofFn (fun i => vcCommitPartyView H presNonce repIdx i (triple.views i)
         (vcPartyFinalOutAt triple.finalOuts i)),
       triple.finalOuts) := by
  unfold reconstructRepRound1 reconstructRepCommits openBlindVcRep
  dsimp only
  refine Prod.ext ?_ rfl
  apply Triple3.ext_get
  intro i
  rw [Triple3.get_ofFn, Triple3.get_ofFn]
  let f : Fin 3 → List UInt8 := fun j =>
    vcCommitPartyView H presNonce repIdx j (triple.views j) (vcPartyFinalOutAt triple.finalOuts j)
  change mkParty3At e (f e) (f (vcNextParty3 e)) (f (vcUnopenedParty3 e)) i = f i
  rw [mkParty3At_eta]

/-- Serialize public selective-disclosure statement + Round-1 bundle for Fiat-Shamir challenge derivation
    (`"QSAG.FS.INIT.V1"` + `"QSAG.FS.ABSORB.V1"` + `"QSAG.FS.SQUEEZE.V1"`, `blind_vc.rs:2152-2418`). -/
private def serDisclosedFrames : List (Nat × Goldilocks) → List (List UInt8)
  | [] => [[0x00]]
  | (idx, val) :: rest => [([0x01] : List UInt8), encodeNatLeBytes 8 idx, encodeGoldilocksVecLe [val]].flatten ::
      serDisclosedFrames rest

private def serRound1ItemFrames (item : Triple3 (List UInt8) × VcRepFinalOuts3) : List (List UInt8) :=
  [item.1.s0, item.1.s1, item.1.s2] ++
  serLane6Frame item.2.rootShares.s0 ++ serLane6Frame item.2.rootShares.s1 ++ serLane6Frame item.2.rootShares.s2 ++
  serLane6Frame item.2.presShares.s0 ++ serLane6Frame item.2.presShares.s1 ++ serLane6Frame item.2.presShares.s2 ++
  serLane6Frame item.2.scopeShares.s0 ++ serLane6Frame item.2.scopeShares.s1 ++ serLane6Frame item.2.scopeShares.s2 ++
  (item.2.boolZeroShares.map (fun t => encodeGoldilocksVecLe [t.s0, t.s1, t.s2]))

def deriveBlindVcTranscriptDigest (H : List UInt8 → List UInt8)
    (verifierChallenge : List UInt8) (profile : ZkSoundnessProfile)
    (expectedSchema : VcSchema) (treeDepth : Nat)
    (presNonce issuerRootTag : Vec UInt8 32) (issuerEpoch : UInt64)
    (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
    (disclosed : List (Nat × Goldilocks))
    (allRound1 : List (Triple3 (List UInt8) × VcRepFinalOuts3)) : List UInt8 :=
  let profileTag := match profile with
    | .quantum128 => vcProfileQuantumTag
    | .classical128 => []
  let initDigest := H (cshake256FramedPreimage vcFsInitTag
    ([vcSdZkDomainTag, profileTag,
      encodeNatLeBytes 8 expectedSchema.schemaId.toNat,
      encodeNatLeBytes 8 expectedSchema.arity,
      leb128 treeDepth,
      encodeNatLeBytes 8 profile.repetitions,
      presNonce.toList,
      encodeNatLeBytes 8 issuerEpoch.toNat,
      issuerRootTag.toList,
      verifierChallenge] ++
     serLane6Frame accRoot ++ serLane6Frame presCommit ++ serLane6Frame scopeTag ++
     serLane4Frame verifierScopeLimbs ++ serDisclosedFrames disclosed))
  let r1Digest := foldFramesHash H vcFsAbsorbTag
    (allRound1.foldr (fun it acc => serRound1ItemFrames it ++ acc) [])
  H (cshake256FramedPreimage vcFsAbsorbTag [initDigest, r1Digest])

def deriveBlindVcChallengeAt (H : List UInt8 → List UInt8)
    (trDigest : List UInt8) (repIdx : Nat) : Fin 3 :=
  let sq := H (cshake256FramedPreimage vcFsSqueezeTag (vcChallengeContext204 trDigest repIdx))
  ⟨decodeNatLeBytes (sq.take 8) % 3, Nat.mod_lt _ (by decide)⟩

/-- Check all boolean-gate output wire shares: each `(z_0, z_1, z_2)` sums to `0` and matches `(z_e, z_{e+1})`. -/
def checkBoolZeroOutputs (e : Fin 3) :
    List (Goldilocks × Goldilocks) → List (Triple3 Goldilocks) → Bool
  | [], [] => true
  | (ze, ze1) :: restPairs, tz :: restTriples =>
    decide (tz.get e = ze) &&
    decide (tz.get (vcNextParty3 e) = ze1) &&
    decide (vcSum3 tz.get = Goldilocks.zero) &&
    checkBoolZeroOutputs e restPairs restTriples
  | _, _ => false

private theorem checkBoolZeroOutputs_spec (e : Fin 3) :
    ∀ (pairs : List (Goldilocks × Goldilocks)) (triples : List (Triple3 Goldilocks)),
      checkBoolZeroOutputs e pairs triples = true ↔
        pairs = triples.map (fun t => vcPairAt t.get e) ∧
        (∀ t ∈ triples, vcSum3 t.get = Goldilocks.zero)
  | [], [] => by simp [checkBoolZeroOutputs]
  | [], _ :: _ => by simp [checkBoolZeroOutputs]
  | _ :: _, [] => by simp [checkBoolZeroOutputs]
  | (ze, ze1) :: ps, tz :: ts => by
    simp only [checkBoolZeroOutputs, Bool.and_eq_true, decide_eq_true_eq, List.map, List.cons.injEq]
    rw [checkBoolZeroOutputs_spec e ps ts]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hSum⟩, hPs, hAll⟩
      refine ⟨⟨Prod.ext h1.symm h2.symm, hPs⟩, ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | hTail
      · exact hSum
      · exact hAll t hTail
    · rintro ⟨⟨hHead, hPs⟩, hAll⟩
      injection hHead with h1 h2
      exact ⟨⟨⟨h1.symm, h2.symm⟩, hAll tz (.head ts)⟩, hPs, fun t ht => hAll t (.tail tz ht)⟩

/-- Construct 2-party rate-6 commit chunks for `pairCheckSponge3Perm` (`vcAttrCommitTag` / `vcPresCommitTag`). -/
def vcPairCommitChunks (e : Fin 3) (schema : VcSchema)
    (attrsE attrsE1 : List Goldilocks) (blindE blindE1 : Lane4) (tag : UInt64) :
    (Lane6 × Lane6) × (Lane6 × Lane6) × (Lane6 × Lane6) :=
  let sLo := vcConstPair e (vcSchemaLo schema.schemaId)
  let sHi := vcConstPair e (vcSchemaHiWithTag schema.schemaId tag)
  let sAr := vcConstPair e (Goldilocks.ofNat schema.arity)
  let sOne := vcConstPair e Goldilocks.one
  let c0 : Lane6 × Lane6 :=
    (⟨vcAttrAt attrsE 0, vcAttrAt attrsE 1, vcAttrAt attrsE 2,
      vcAttrAt attrsE 3, vcAttrAt attrsE 4, vcAttrAt attrsE 5⟩,
     ⟨vcAttrAt attrsE1 0, vcAttrAt attrsE1 1, vcAttrAt attrsE1 2,
      vcAttrAt attrsE1 3, vcAttrAt attrsE1 4, vcAttrAt attrsE1 5⟩)
  let c1 : Lane6 × Lane6 :=
    (⟨blindE.x0, blindE.x1, blindE.x2, blindE.x3, sLo.1, sHi.1⟩,
     ⟨blindE1.x0, blindE1.x1, blindE1.x2, blindE1.x3, sLo.2, sHi.2⟩)
  let c2 : Lane6 × Lane6 :=
    (⟨sAr.1, sOne.1, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
     ⟨sAr.2, sOne.2, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)
  (c0, c1, c2)

/-- Construct 2-party rate-6 scope chunks for `pairCheckSponge3Perm` (`vcScopeTagDom`). -/
def vcPairScopeChunks (e : Fin 3) (sid : UInt64)
    (hbE hbE1 : Lane4) (scopeLimbs : Lane4) :
    (Lane6 × Lane6) × (Lane6 × Lane6) × (Lane6 × Lane6) :=
  let sc0 := vcConstPair e scopeLimbs.x0
  let sc1 := vcConstPair e scopeLimbs.x1
  let sc2 := vcConstPair e scopeLimbs.x2
  let sc3 := vcConstPair e scopeLimbs.x3
  let sLo := vcConstPair e (vcSchemaLo sid)
  let sHi := vcConstPair e (vcSchemaHiWithTag sid vcScopeTagDom)
  let sOne := vcConstPair e Goldilocks.one
  let c0 : Lane6 × Lane6 :=
    (⟨hbE.x0, hbE.x1, hbE.x2, hbE.x3, sc0.1, sc1.1⟩,
     ⟨hbE1.x0, hbE1.x1, hbE1.x2, hbE1.x3, sc0.2, sc1.2⟩)
  let c1 : Lane6 × Lane6 :=
    (⟨sc2.1, sc3.1, Goldilocks.zero, Goldilocks.zero, sLo.1, sHi.1⟩,
     ⟨sc2.2, sc3.2, Goldilocks.zero, Goldilocks.zero, sLo.2, sHi.2⟩)
  let c2 : Lane6 × Lane6 :=
    (⟨sOne.1, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
     ⟨sOne.2, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)
  (c0, c1, c2)

/-- Full per-repetition ZKBoo verifier (`blind_vc.rs:2180-2415`, fixing `C0-3`):
    enforces challenge match `o.e = expectedE`, strict ascending `disclosed`, `attrShares.length = schema.arity`,
    pinned disclosed shares, PRG tape replay (`checkPartyPrgTape`) on BOTH `viewE` and `viewE1`,
    all 4 `absorbRate6Sponge3` / `treeDepth` Merkle subcircuits, and 3-share output reconstruction. -/
def verifyOpenedBlindVcRep
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (schema : VcSchema) (issuerEpoch : UInt64) (treeDepth : Nat)
    (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
    (disclosed : List (Nat × Goldilocks))
    (repIdx : Nat) (expectedE : Fin 3) (o : OpenedBlindVcRep) : Bool :=
  let e := o.e
  let e1 := vcNextParty3 e
  if !(decide (e = expectedE) &&
       vcCheckDisclosedStrictAsc schema.arity disclosed &&
       decide (o.viewE.attrShares.length = schema.arity) &&
       decide (o.viewE1.attrShares.length = schema.arity) &&
       decide (o.viewE.merkleLevels.length = treeDepth) &&
       decide (o.viewE1.merkleLevels.length = treeDepth) &&
       vcCheckPartyDisclosedShares e o.viewE.attrShares disclosed &&
       vcCheckPartyDisclosedShares e1 o.viewE1.attrShares disclosed &&
       checkPartyPrgTape prgExpand treeDepth repIdx e o.viewE &&
       checkPartyPrgTape prgExpand treeDepth repIdx e1 o.viewE1) then
    false
  else
    let (ac0, ac1, ac2) := vcPairCommitChunks e schema
      o.viewE.attrShares o.viewE1.attrShares
      o.viewE.holderBlindShare o.viewE1.holderBlindShare vcAttrCommitTag
    let (pc0, pc1, pc2) := vcPairCommitChunks e schema
      o.viewE.attrShares o.viewE1.attrShares
      o.viewE.presBlindShare o.viewE1.presBlindShare vcPresCommitTag
    let (sc0, sc1, sc2) := vcPairScopeChunks e schema.schemaId
      o.viewE.holderBlindShare o.viewE1.holderBlindShare verifierScopeLimbs
    match pairCheckSponge3Perm e o.viewE.attrSponge o.viewE1.attrSponge ac0 ac1 ac2,
          pairCheckSponge3Perm e o.viewE.presSponge o.viewE1.presSponge pc0 pc1 pc2,
          pairCheckSponge3Perm e o.viewE.scopeSponge o.viewE1.scopeSponge sc0 sc1 sc2 with
    | some leafPair, some presPair, some scopePair =>
      match pairCheckMerklePath e issuerEpoch 0 leafPair o.viewE.merkleLevels o.viewE1.merkleLevels with
      | none => false
      | some (rootPair, boolZeroPairs) =>
        decide (vcPairAtLane6 o.finalOuts.rootShares.get e = rootPair) &&
        decide (vcSumLane6_3 o.finalOuts.rootShares.get = accRoot) &&
        decide (vcPairAtLane6 o.finalOuts.presShares.get e = presPair) &&
        decide (vcSumLane6_3 o.finalOuts.presShares.get = presCommit) &&
        decide (vcPairAtLane6 o.finalOuts.scopeShares.get e = scopePair) &&
        decide (vcSumLane6_3 o.finalOuts.scopeShares.get = scopeTag) &&
        checkBoolZeroOutputs e boolZeroPairs o.finalOuts.boolZeroShares
    | _, _, _ => false

def verifyAllBlindVcReps
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (trDigest : List UInt8)
    (schema : VcSchema) (issuerEpoch : UInt64) (treeDepth : Nat)
    (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
    (disclosed : List (Nat × Goldilocks)) :
    Nat → List OpenedBlindVcRep → Bool
  | _, [] => true
  | repIdx, o :: rest =>
    let expectedE := deriveBlindVcChallengeAt H trDigest repIdx
    verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expectedE o &&
    verifyAllBlindVcReps H prgExpand trDigest schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed (repIdx + 1) rest

/-- Full selective-disclosure presentation verifier (`verify_presentation_with_profile`,
    `blind_vc.rs:2120-2425`, fixing `C0-3` & `C1-2`):
    enforces `schemaId` match, strict ascending `disclosedAttrs` (`< arity` + `Nodup`),
    `openedReps.length = profile.repetitions` (`438` for `.quantum128`, `219` for `.classical128`),
    Round-1 `"QSAG.VC.VIEW_COM.V1"` + `"QSAG.COMMIT.V1"` commitment reconstruction,
    `"QSAG.FS.INIT/ABSORB/SQUEEZE.V1"` Fiat-Shamir challenge derivation, and PRG-checked ZKBoo replay!
    The accumulator root, issuer tag, epoch and verifier scope are read from `pres`, so this
    function checks a presentation against the context it carries. A relying party uses
    `verifyBlindVcPresentationTrusted`, which fixes that context first. -/
@[expose] def verifyBlindVcPresentation
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (expectedSchema : VcSchema) (treeDepth : Nat)
    (verifierChallenge : List UInt8)
    (pres : BlindVcPresentation) : Bool :=
  if !(decide (pres.schemaId = expectedSchema.schemaId) &&
       vcCheckDisclosedStrictAsc expectedSchema.arity pres.disclosedAttrs &&
       decide (pres.openedReps.length = profile.repetitions)) then
    false
  else
    let allRound1 := reconstructAllRepRound1 H pres.presentationNonce 0 pres.openedReps
    let trDigest := deriveBlindVcTranscriptDigest H verifierChallenge profile expectedSchema treeDepth
      pres.presentationNonce pres.issuerRootTag pres.issuerEpoch
      pres.accumulatorRoot pres.presCommit pres.scopeTag pres.verifierScopeLimbs
      pres.disclosedAttrs allRound1
    verifyAllBlindVcReps H prgExpand trDigest expectedSchema pres.issuerEpoch treeDepth
      pres.accumulatorRoot pres.presCommit pres.scopeTag pres.verifierScopeLimbs
      pres.disclosedAttrs 0 pres.openedReps

/-- Reconstruct the secret attribute list `[a_0, ..., a_{arity-1}]` from a 3-party view triple. -/
def vcReconstructAttrs3 (arity : Nat) (v : Fin 3 → PartyVcRepView) : List Goldilocks :=
  (List.range arity).map (fun k => vcSum3 (fun i => vcAttrAt (v i).attrShares k))

private theorem vcReconstructAttrs3_length (arity : Nat) (v : Fin 3 → PartyVcRepView) :
    (vcReconstructAttrs3 arity v).length = arity := by
  simp [vcReconstructAttrs3]

private theorem vcAttrAt_reconstructAttrs3 {arity : Nat} {v : Fin 3 → PartyVcRepView}
    (hLen : ∀ i : Fin 3, ((v i).attrShares).length = arity) (k : Nat) :
    vcAttrAt (vcReconstructAttrs3 arity v) k = vcSum3 (fun i => vcAttrAt (v i).attrShares k) := by
  unfold vcReconstructAttrs3
  if hk : k < arity then
    have hkRange : k < (List.range arity).length := by simp [hk]
    unfold vcAttrAt
    rw [List.getElem?_map, List.getElem?_eq_getElem hkRange, List.getElem_range]
    rfl
  else
    have hkRange : ((List.range arity).map (fun idx => vcSum3 (fun i => vcAttrAt (v i).attrShares idx)))[k]? = none := by
      apply List.getElem?_eq_none
      simp; omega
    have hLhs : vcAttrAt ((List.range arity).map (fun idx => vcSum3 (fun i => vcAttrAt (v i).attrShares idx))) k = Goldilocks.zero := by
      simp only [vcAttrAt] at hkRange ⊢
      rw [hkRange]
      rfl
    rw [hLhs]
    have hNone : ∀ i : Fin 3, ((v i).attrShares)[k]? = none := fun i => by
      apply List.getElem?_eq_none
      rw [hLen i]; omega
    have hFun0 : (fun i => vcAttrAt (v i).attrShares k) = (fun _ => Goldilocks.zero) := by
      funext i; unfold vcAttrAt; rw [hNone i]; rfl
    rw [hFun0, vcSum3_zero]

private def vcCommitChunks3 (schema : VcSchema) (attrShares : Fin 3 → List Goldilocks)
    (blindShares : VcLane4_3) (tag : UInt64) : VcLane6_3 × VcLane6_3 × VcLane6_3 :=
  (fun i =>
    ⟨vcAttrAt (attrShares i) 0, vcAttrAt (attrShares i) 1, vcAttrAt (attrShares i) 2,
     vcAttrAt (attrShares i) 3, vcAttrAt (attrShares i) 4, vcAttrAt (attrShares i) 5⟩,
   fun i =>
    ⟨(blindShares i).x0, (blindShares i).x1, (blindShares i).x2, (blindShares i).x3,
     vcConstWire3 (vcSchemaLo schema.schemaId) i,
     vcConstWire3 (vcSchemaHiWithTag schema.schemaId tag) i⟩,
   fun i =>
    ⟨vcConstWire3 (Goldilocks.ofNat schema.arity) i,
     vcConstWire3 Goldilocks.one i,
     Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

private theorem vcPairCommitChunks_spec (e : Fin 3) (schema : VcSchema)
    (attrShares : Fin 3 → List Goldilocks) (blindShares : VcLane4_3) (tag : UInt64) :
    vcPairCommitChunks e schema (attrShares e) (attrShares (vcNextParty3 e))
      (blindShares e) (blindShares (vcNextParty3 e)) tag =
      let (c0, c1, c2) := vcCommitChunks3 schema attrShares blindShares tag
      (vcPairAtLane6 c0 e, vcPairAtLane6 c1 e, vcPairAtLane6 c2 e) := by
  unfold vcPairCommitChunks vcCommitChunks3
  rw [vcConstPair_spec (vcSchemaLo schema.schemaId) e,
      vcConstPair_spec (vcSchemaHiWithTag schema.schemaId tag) e,
      vcConstPair_spec (Goldilocks.ofNat schema.arity) e,
      vcConstPair_spec Goldilocks.one e]
  rfl

private def vcScopeChunks3 (sid : UInt64) (hbShares : VcLane4_3) (scopeLimbs : Lane4) :
    VcLane6_3 × VcLane6_3 × VcLane6_3 :=
  (fun i =>
    ⟨(hbShares i).x0, (hbShares i).x1, (hbShares i).x2, (hbShares i).x3,
     vcConstWire3 scopeLimbs.x0 i, vcConstWire3 scopeLimbs.x1 i⟩,
   fun i =>
    ⟨vcConstWire3 scopeLimbs.x2 i, vcConstWire3 scopeLimbs.x3 i,
     Goldilocks.zero, Goldilocks.zero,
     vcConstWire3 (vcSchemaLo sid) i, vcConstWire3 (vcSchemaHiWithTag sid vcScopeTagDom) i⟩,
   fun i =>
    ⟨vcConstWire3 Goldilocks.one i, Goldilocks.zero, Goldilocks.zero,
     Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

private theorem vcPairScopeChunks_spec (e : Fin 3) (sid : UInt64)
    (hbShares : VcLane4_3) (scopeLimbs : Lane4) :
    vcPairScopeChunks e sid (hbShares e) (hbShares (vcNextParty3 e)) scopeLimbs =
      let (c0, c1, c2) := vcScopeChunks3 sid hbShares scopeLimbs
      (vcPairAtLane6 c0 e, vcPairAtLane6 c1 e, vcPairAtLane6 c2 e) := by
  unfold vcPairScopeChunks vcScopeChunks3
  rw [vcConstPair_spec scopeLimbs.x0 e, vcConstPair_spec scopeLimbs.x1 e,
      vcConstPair_spec scopeLimbs.x2 e, vcConstPair_spec scopeLimbs.x3 e,
      vcConstPair_spec (vcSchemaLo sid) e, vcConstPair_spec (vcSchemaHiWithTag sid vcScopeTagDom) e,
      vcConstPair_spec Goldilocks.one e]
  rfl

/- **Constructive 3-Challenge Special Soundness + Round-1 Commitment Extraction (`0 Classical.choice`, fixing `C0-3`)**:
    Given 3 accepting openings `(o0, o1, o2)` at challenges `(0, 1, 2)` sharing the SAME Round-1
    `(commits, finalOuts)` transcript (with ZERO external `Nodup` assumption — derived directly from
    `verifyOpenedBlindVcRep`!), **either** an explicit `H`-collision is constructively exhibited,
    **or** a complete valid credential + boolean Merkle witness `(attrs, holderBlind, presBlind, leafCommit, boolSteps)`
    is extracted! -/
/-- A collision in one of the three concrete overlapping view pairs of a rewound table.
This finite event says nothing about collisions at unrelated hash inputs. -/
@[expose] def VcRewoundCommitConflict (H : List UInt8 → List UInt8)
    (nonce : Vec UInt8 32) (repIdx : Nat) (o0 o1 o2 : OpenedBlindVcRep) : Prop :=
  (o0.viewE1 ≠ o1.viewE ∧
    vcCommitPartyView H nonce repIdx 1 o0.viewE1 (vcPartyFinalOutAt o1.finalOuts 1) =
    vcCommitPartyView H nonce repIdx 1 o1.viewE (vcPartyFinalOutAt o1.finalOuts 1)) ∨
  (o1.viewE1 ≠ o2.viewE ∧
    vcCommitPartyView H nonce repIdx 2 o1.viewE1 (vcPartyFinalOutAt o2.finalOuts 2) =
    vcCommitPartyView H nonce repIdx 2 o2.viewE (vcPartyFinalOutAt o2.finalOuts 2)) ∨
  (o2.viewE1 ≠ o0.viewE ∧
    vcCommitPartyView H nonce repIdx 0 o2.viewE1 (vcPartyFinalOutAt o0.finalOuts 0) =
    vcCommitPartyView H nonce repIdx 0 o0.viewE (vcPartyFinalOutAt o0.finalOuts 0))

instance (H : List UInt8 → List UInt8) (nonce : Vec UInt8 32)
    (repIdx : Nat) (o0 o1 o2 : OpenedBlindVcRep) :
    Decidable (VcRewoundCommitConflict H nonce repIdx o0 o1 o2) :=
  by unfold VcRewoundCommitConflict; infer_instance

/-- The finite event identifies which actual committed view pair breaks binding. -/
theorem vcRewoundCommitConflict_hash_collision
    {H : List UInt8 → List UInt8} (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {nonce : Vec UInt8 32} {repIdx : Nat} {o0 o1 o2 : OpenedBlindVcRep}
    (h : VcRewoundCommitConflict H nonce repIdx o0 o1 o2) :
    ∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂ := by
  rcases h with h | h | h
  all_goals exact vcCommitPartyView_binding hHLen (fun he => h.1 (congrArg Prod.fst he)) h.2

theorem verifyOpenedBlindVcRep_extract3_finite_conflict
    {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {presNonce : Vec UInt8 32} {schema : VcSchema} {issuerEpoch : UInt64} {treeDepth : Nat}
    {accRoot presCommit scopeTag : Lane6} {verifierScopeLimbs : Lane4}
    {disclosed : List (Nat × Goldilocks)} {repIdx : Nat}
    {o0 o1 o2 : OpenedBlindVcRep}
    (hR1_01 : reconstructRepRound1 H presNonce repIdx o0 = reconstructRepRound1 H presNonce repIdx o1)
    (hR1_12 : reconstructRepRound1 H presNonce repIdx o1 = reconstructRepRound1 H presNonce repIdx o2)
    (hVer0 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 0 o0 = true)
    (hVer1 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 1 o1 = true)
    (hVer2 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 2 o2 = true) :
    VcRewoundCommitConflict H presNonce repIdx o0 o1 o2 ∨
    ∃ (attrs : List Goldilocks) (holderBlind presBlind : Lane4)
      (leafCommit : Lane6) (boolSteps : List (Bool × Lane6)),
      (disclosed.map Prod.fst).Nodup ∧
      attrs.length = schema.arity ∧
      (∀ p ∈ disclosed, p.1 < schema.arity ∧ attrs[p.1]? = some p.2) ∧
      computeVcPoseidon2Commit schema attrs holderBlind vcAttrCommitTag = some leafCommit ∧
      boolSteps.length = treeDepth ∧
      evalVcMerklePathBool issuerEpoch 0 leafCommit boolSteps = accRoot ∧
      computeVcPoseidon2Commit schema attrs presBlind vcPresCommitTag = some presCommit ∧
      computeVcScopeTag schema.schemaId holderBlind verifierScopeLimbs = scopeTag := by
  have hUnpack : ∀ {expE : Fin 3} {o : OpenedBlindVcRep},
      verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
        accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expE o = true →
      o.e = expE ∧
      vcCheckDisclosedStrictAsc schema.arity disclosed = true ∧
      o.viewE.attrShares.length = schema.arity ∧
      o.viewE1.attrShares.length = schema.arity ∧
      o.viewE.merkleLevels.length = treeDepth := by
    intro expE o hV
    unfold verifyOpenedBlindVcRep at hV
    dsimp only at hV
    cases hG :
        (decide (o.e = expE) &&
         vcCheckDisclosedStrictAsc schema.arity disclosed &&
         decide (o.viewE.attrShares.length = schema.arity) &&
         decide (o.viewE1.attrShares.length = schema.arity) &&
         decide (o.viewE.merkleLevels.length = treeDepth) &&
         decide (o.viewE1.merkleLevels.length = treeDepth) &&
         vcCheckPartyDisclosedShares o.e o.viewE.attrShares disclosed &&
         vcCheckPartyDisclosedShares (vcNextParty3 o.e) o.viewE1.attrShares disclosed &&
         checkPartyPrgTape prgExpand treeDepth repIdx o.e o.viewE &&
         checkPartyPrgTape prgExpand treeDepth repIdx (vcNextParty3 o.e) o.viewE1) with
    | false => rw [hG] at hV; cases hV
    | true =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
      exact ⟨hG.1.1.1.1.1.1.1.1.1, hG.1.1.1.1.1.1.1.1.2,
             hG.1.1.1.1.1.1.1.2, hG.1.1.1.1.1.1.2, hG.1.1.1.1.1.2⟩
  obtain ⟨he0, hAsc, _, _, _⟩ := hUnpack hVer0
  obtain ⟨he1, _, _, _, _⟩ := hUnpack hVer1
  obtain ⟨he2, _, _, _, _⟩ := hUnpack hVer2
  have hFo01 : o0.finalOuts = o1.finalOuts := congrArg Prod.snd hR1_01
  have hFo12 : o1.finalOuts = o2.finalOuts := congrArg Prod.snd hR1_12
  have hCom01 : reconstructRepCommits H presNonce repIdx o0 = reconstructRepCommits H presNonce repIdx o1 :=
    congrArg Prod.fst hR1_01
  have hCom12 : reconstructRepCommits H presNonce repIdx o1 = reconstructRepCommits H presNonce repIdx o2 :=
    congrArg Prod.fst hR1_12
  if hv1 : o0.viewE1 ≠ o1.viewE then
    left
    have hc1 := congrArg (fun t => t.get 1) hCom01
    unfold reconstructRepCommits at hc1
    rw [he0, he1, hFo01, Triple3.get_ofFn, Triple3.get_ofFn] at hc1
    dsimp only [vcNextParty3, mkParty3At] at hc1
    exact Or.inl ⟨hv1, hc1⟩
  else if hv2 : o1.viewE1 ≠ o2.viewE then
    left
    have hc2 := congrArg (fun t => t.get 2) hCom12
    unfold reconstructRepCommits at hc2
    rw [he1, he2, hFo12, Triple3.get_ofFn, Triple3.get_ofFn] at hc2
    dsimp only [vcNextParty3, mkParty3At] at hc2
    exact Or.inr (Or.inl ⟨hv2, hc2⟩)
  else if hv0 : o2.viewE1 ≠ o0.viewE then
    left
    have hFo20 : o2.finalOuts = o0.finalOuts := (hFo01.trans hFo12).symm
    have hc0 := congrArg (fun t => t.get 0) (hCom01.trans hCom12).symm
    unfold reconstructRepCommits at hc0
    rw [he2, he0, hFo20, Triple3.get_ofFn, Triple3.get_ofFn] at hc0
    dsimp only [vcNextParty3, mkParty3At] at hc0
    exact Or.inr (Or.inr ⟨hv0, hc0⟩)
  else
    right
    have hv1Eq : o0.viewE1 = o1.viewE := Decidable.of_not_not hv1
    have hv2Eq : o1.viewE1 = o2.viewE := Decidable.of_not_not hv2
    have hv0Eq : o2.viewE1 = o0.viewE := Decidable.of_not_not hv0
    let v : Fin 3 → PartyVcRepView
      | ⟨0, _⟩ => o0.viewE
      | ⟨1, _⟩ => o1.viewE
      | ⟨2, _⟩ => o2.viewE
    let fo := o0.finalOuts
    have hStepBody : ∀ {expE : Fin 3} {o : OpenedBlindVcRep},
        o.e = expE → o.viewE = v expE → o.viewE1 = v (vcNextParty3 expE) → o.finalOuts = fo →
        verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
          accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expE o = true →
        (v expE).attrShares.length = schema.arity ∧
        (v expE).merkleLevels.length = treeDepth ∧
        vcCheckPartyDisclosedShares expE (v expE).attrShares disclosed = true ∧
        ∃ leafPair presPair scopePair boolZeroPairs,
          pairCheckSponge3Perm expE (v expE).attrSponge (v (vcNextParty3 expE)).attrSponge
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).holderBlindShare (v (vcNextParty3 expE)).holderBlindShare vcAttrCommitTag).1
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).holderBlindShare (v (vcNextParty3 expE)).holderBlindShare vcAttrCommitTag).2.1
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).holderBlindShare (v (vcNextParty3 expE)).holderBlindShare vcAttrCommitTag).2.2 = some leafPair ∧
          pairCheckSponge3Perm expE (v expE).presSponge (v (vcNextParty3 expE)).presSponge
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).presBlindShare (v (vcNextParty3 expE)).presBlindShare vcPresCommitTag).1
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).presBlindShare (v (vcNextParty3 expE)).presBlindShare vcPresCommitTag).2.1
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).presBlindShare (v (vcNextParty3 expE)).presBlindShare vcPresCommitTag).2.2 = some presPair ∧
          pairCheckSponge3Perm expE (v expE).scopeSponge (v (vcNextParty3 expE)).scopeSponge
            (vcPairScopeChunks expE schema.schemaId (v expE).holderBlindShare
              (v (vcNextParty3 expE)).holderBlindShare verifierScopeLimbs).1
            (vcPairScopeChunks expE schema.schemaId (v expE).holderBlindShare
              (v (vcNextParty3 expE)).holderBlindShare verifierScopeLimbs).2.1
            (vcPairScopeChunks expE schema.schemaId (v expE).holderBlindShare
              (v (vcNextParty3 expE)).holderBlindShare verifierScopeLimbs).2.2 = some scopePair ∧
          pairCheckMerklePath expE issuerEpoch 0 leafPair
            (v expE).merkleLevels (v (vcNextParty3 expE)).merkleLevels =
              some (vcPairAtLane6 fo.rootShares.get expE, boolZeroPairs) ∧
          vcSumLane6_3 fo.rootShares.get = accRoot ∧
          vcPairAtLane6 fo.presShares.get expE = presPair ∧
          vcSumLane6_3 fo.presShares.get = presCommit ∧
          vcPairAtLane6 fo.scopeShares.get expE = scopePair ∧
          vcSumLane6_3 fo.scopeShares.get = scopeTag ∧
          checkBoolZeroOutputs expE boolZeroPairs fo.boolZeroShares = true := by
      intro expE o he hve hve1 hfo hV
      unfold verifyOpenedBlindVcRep at hV
      rw [he, hve, hve1, hfo] at hV
      dsimp only at hV
      cases hG :
          (decide (expE = expE) &&
           vcCheckDisclosedStrictAsc schema.arity disclosed &&
           decide ((v expE).attrShares.length = schema.arity) &&
           decide ((v (vcNextParty3 expE)).attrShares.length = schema.arity) &&
           decide ((v expE).merkleLevels.length = treeDepth) &&
           decide ((v (vcNextParty3 expE)).merkleLevels.length = treeDepth) &&
           vcCheckPartyDisclosedShares expE (v expE).attrShares disclosed &&
           vcCheckPartyDisclosedShares (vcNextParty3 expE) (v (vcNextParty3 expE)).attrShares disclosed &&
           checkPartyPrgTape prgExpand treeDepth repIdx expE (v expE) &&
           checkPartyPrgTape prgExpand treeDepth repIdx (vcNextParty3 expE) (v (vcNextParty3 expE))) with
      | false => rw [hG] at hV; cases hV
      | true =>
        rw [hG] at hV
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hV
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
        refine ⟨hG.1.1.1.1.1.1.1.2, hG.1.1.1.1.1.2, hG.1.1.1.2, ?_⟩
        cases ha : pairCheckSponge3Perm expE (v expE).attrSponge (v (vcNextParty3 expE)).attrSponge _ _ _ with
        | none => rw [ha] at hV; cases hV
        | some lp =>
        cases hp : pairCheckSponge3Perm expE (v expE).presSponge (v (vcNextParty3 expE)).presSponge _ _ _ with
        | none => rw [ha, hp] at hV; cases hV
        | some pp =>
        cases hs : pairCheckSponge3Perm expE (v expE).scopeSponge (v (vcNextParty3 expE)).scopeSponge _ _ _ with
        | none => rw [ha, hp, hs] at hV; cases hV
        | some sp =>
          rw [ha, hp, hs] at hV
          dsimp only at hV
          cases hm : pairCheckMerklePath expE issuerEpoch 0 lp (v expE).merkleLevels (v (vcNextParty3 expE)).merkleLevels with
          | none => rw [hm] at hV; cases hV
          | some mkOut =>
            rw [hm] at hV
            rcases mkOut with ⟨rp, bzp⟩
            dsimp only at hV
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hV
            rcases hV with ⟨⟨⟨⟨⟨⟨hRp, hAcc⟩, hPp⟩, hPres⟩, hSp⟩, hSc⟩, hBz⟩
            subst hRp
            exact ⟨lp, pp, sp, bzp, rfl, rfl, rfl, hm, hAcc, hPp, hPres, hSp, hSc, hBz⟩
    obtain ⟨hLen0, hMkLen0, hDisc0, lp0, pp0, sp0, bzp0, ha0, hp0, hs0, hm0, hAccSum, hPp0, hPresSum, hSp0, hScSum, hBz0⟩ :=
      hStepBody he0 rfl hv1Eq rfl hVer0
    obtain ⟨hLen1, _, hDisc1, lp1, pp1, sp1, bzp1, ha1, hp1, hs1, hm1, _, hPp1, _, hSp1, _, hBz1⟩ :=
      hStepBody he1 rfl hv2Eq hFo01.symm hVer1
    obtain ⟨hLen2, _, hDisc2, lp2, pp2, sp2, bzp2, ha2, hp2, hs2, hm2, _, hPp2, _, hSp2, _, _⟩ :=
      hStepBody he2 rfl hv0Eq (hFo01.trans hFo12).symm hVer2
    have hAllLen : ∀ i : Fin 3, ((v i).attrShares).length = schema.arity :=
      fin3_all hLen0 hLen1 hLen2
    rw [vcPairCommitChunks_spec 0 schema (fun i => (v i).attrShares) (fun i => (v i).holderBlindShare) vcAttrCommitTag] at ha0
    rw [vcPairCommitChunks_spec 1 schema (fun i => (v i).attrShares) (fun i => (v i).holderBlindShare) vcAttrCommitTag] at ha1
    rw [vcPairCommitChunks_spec 2 schema (fun i => (v i).attrShares) (fun i => (v i).holderBlindShare) vcAttrCommitTag] at ha2
    rw [vcPairCommitChunks_spec 0 schema (fun i => (v i).attrShares) (fun i => (v i).presBlindShare) vcPresCommitTag] at hp0
    rw [vcPairCommitChunks_spec 1 schema (fun i => (v i).attrShares) (fun i => (v i).presBlindShare) vcPresCommitTag] at hp1
    rw [vcPairCommitChunks_spec 2 schema (fun i => (v i).attrShares) (fun i => (v i).presBlindShare) vcPresCommitTag] at hp2
    rw [vcPairScopeChunks_spec 0 schema.schemaId (fun i => (v i).holderBlindShare) verifierScopeLimbs] at hs0
    rw [vcPairScopeChunks_spec 1 schema.schemaId (fun i => (v i).holderBlindShare) verifierScopeLimbs] at hs1
    rw [vcPairScopeChunks_spec 2 schema.schemaId (fun i => (v i).holderBlindShare) verifierScopeLimbs] at hs2
    obtain ⟨leaf3, hlp0, hlp1, hlp2, hLeafSum⟩ :=
      pairCheckSponge3Perm_extract3 (sv := fun i => (v i).attrSponge) ha0 ha1 ha2
    obtain ⟨pres3, hpp0', hpp1', _, hPresSpongeSum⟩ :=
      pairCheckSponge3Perm_extract3 (sv := fun i => (v i).presSponge) hp0 hp1 hp2
    obtain ⟨scope3, hsp0', hsp1', _, hScopeSpongeSum⟩ :=
      pairCheckSponge3Perm_extract3 (sv := fun i => (v i).scopeSponge) hs0 hs1 hs2
    rw [hlp0] at hm0; rw [hlp1] at hm1; rw [hlp2] at hm2
    obtain ⟨root3, bzs3, arithSteps, hArithLen, hmr0, hmr1, _, hBoolGateImp, hRootMerkleSum⟩ :=
      pairCheckMerklePath_extract3 issuerEpoch treeDepth 0 leaf3 (fun i => (v i).merkleLevels) hMkLen0 hm0 hm1 hm2
    have hPresEq : fo.presShares.get = pres3 := by
      have e0 := hPp0.trans hpp0'
      have e1 := hPp1.trans hpp1'
      exact funext (fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1))
    have hScopeEq : fo.scopeShares.get = scope3 := by
      have e0 := hSp0.trans hsp0'
      have e1 := hSp1.trans hsp1'
      exact funext (fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1))
    have hRootEq : fo.rootShares.get = root3 := by
      have e0 := congrArg Prod.fst hmr0
      have e1 := congrArg Prod.fst hmr1
      exact funext (fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1))
    obtain ⟨hBzp0Eq, hFoBoolZero⟩ := (checkBoolZeroOutputs_spec 0 bzp0 fo.boolZeroShares).mp hBz0
    obtain ⟨hBzp1Eq, _⟩ := (checkBoolZeroOutputs_spec 1 bzp1 fo.boolZeroShares).mp hBz1
    have hBzsZero : ∀ z ∈ bzs3, vcSum3 z = Goldilocks.zero := by
      have hMap0 : fo.boolZeroShares.map (fun t => vcPairAt t.get 0) = bzs3.map (fun w => vcPairAt w 0) :=
        hBzp0Eq.symm.trans (congrArg Prod.snd hmr0)
      have hMap1 : fo.boolZeroShares.map (fun t => vcPairAt t.get 1) = bzs3.map (fun w => vcPairAt w 1) :=
        hBzp1Eq.symm.trans (congrArg Prod.snd hmr1)
      have hZipGet : ∀ (ts : List (Triple3 Goldilocks)) (ws : List VcWire3),
          ts.map (fun t => vcPairAt t.get 0) = ws.map (fun w => vcPairAt w 0) →
          ts.map (fun t => vcPairAt t.get 1) = ws.map (fun w => vcPairAt w 1) →
          ts.map Triple3.get = ws := by
        intro ts
        induction ts with
        | nil =>
          intro ws hM0 _
          cases ws with
          | nil => rfl
          | cons _ _ => cases hM0
        | cons t ts ih =>
          intro ws hM0 hM1
          cases ws with
          | nil => cases hM0
          | cons w ws =>
            dsimp only [List.map] at hM0 hM1 ⊢
            injection hM0 with hw0 hRest0
            injection hM1 with hw1 hRest1
            have htw : t.get = w :=
              funext (fin3_all (congrArg Prod.fst hw0) (congrArg Prod.snd hw0) (congrArg Prod.snd hw1))
            rw [htw, ih ws hRest0 hRest1]
      have hListEq := hZipGet fo.boolZeroShares bzs3 hMap0 hMap1
      rw [← hListEq]
      intro z hz
      obtain ⟨t, htMem, rfl⟩ := List.mem_map.mp hz
      exact hFoBoolZero t htMem
    obtain ⟨boolSteps, hBoolStepsLen, hEvalBool⟩ :=
      evalVcMerklePathFrom_eq_bool issuerEpoch 0 (vcSumLane6_3 leaf3) arithSteps (hBoolGateImp hBzsZero)
    obtain ⟨hBounds, hNodup⟩ := vcCheckDisclosedStrictAsc_bounds_and_nodup hAsc
    let attrs := vcReconstructAttrs3 schema.arity v
    let holderBlind := vcSumLane4_3 (fun i => (v i).holderBlindShare)
    let presBlind := vcSumLane4_3 (fun i => (v i).presBlindShare)
    have hAttrsLen : attrs.length = schema.arity := vcReconstructAttrs3_length schema.arity v
    have hChunksSum : ∀ (blindShares : VcLane4_3) (tag : UInt64),
        let (c0, c1, c2) := vcCommitChunks3 schema (fun i => (v i).attrShares) blindShares tag
        (vcSumLane6_3 c0, vcSumLane6_3 c1, vcSumLane6_3 c2) =
          vcCommitChunks schema attrs (vcSumLane4_3 blindShares) tag := by
      intro blindShares tag
      unfold vcCommitChunks3 vcCommitChunks
      dsimp only
      simp only [vcSumLane6_3_eq, vcSumLane4_3_eq, vcSum3_constWire, vcSum3_zero,
        ← vcAttrAt_reconstructAttrs3 hAllLen]
      rfl
    have hScopeChunksSum :
        let (c0, c1, c2) := vcScopeChunks3 schema.schemaId (fun i => (v i).holderBlindShare) verifierScopeLimbs
        (vcSumLane6_3 c0, vcSumLane6_3 c1, vcSumLane6_3 c2) =
          vcScopeChunks schema.schemaId holderBlind verifierScopeLimbs := by
      unfold vcScopeChunks3 vcScopeChunks
      dsimp only [holderBlind]
      simp only [vcSumLane6_3_eq, vcSumLane4_3_eq, vcSum3_constWire, vcSum3_zero]
    refine ⟨attrs, holderBlind, presBlind, vcSumLane6_3 leaf3, boolSteps,
      hNodup, hAttrsLen, ?_, ?_, hBoolStepsLen.trans hArithLen, ?_, ?_, ?_⟩
    · intro p hp
      have hpLt : p.1 < schema.arity := hBounds p hp
      refine ⟨hpLt, ?_⟩
      have h0p := vcCheckPartyDisclosedShares_mem hDisc0 p hp
      have h1p := vcCheckPartyDisclosedShares_mem hDisc1 p hp
      have h2p := vcCheckPartyDisclosedShares_mem hDisc2 p hp
      have hpRange : p.1 < (List.range schema.arity).length := by simp [hpLt]
      dsimp only [attrs, vcReconstructAttrs3]
      rw [List.getElem?_map, List.getElem?_eq_getElem hpRange, List.getElem_range]
      apply congrArg some
      have ha0Eq : vcAttrAt (v 0).attrShares p.1 = vcExpectedDisclosedShare 0 p.2 := by
        unfold vcAttrAt; rw [h0p]; rfl
      have ha1Eq : vcAttrAt (v 1).attrShares p.1 = vcExpectedDisclosedShare 1 p.2 := by
        unfold vcAttrAt; rw [h1p]; rfl
      have ha2Eq : vcAttrAt (v 2).attrShares p.1 = vcExpectedDisclosedShare 2 p.2 := by
        unfold vcAttrAt; rw [h2p]; rfl
      unfold vcSum3
      dsimp only
      rw [ha0Eq, ha1Eq, ha2Eq]
      dsimp only [vcExpectedDisclosedShare, ↓reduceIte]
      have h10 : (1 : Fin 3) ≠ 0 := by decide
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      simp only [h10, h20, ↓reduceIte]
      rw [← goldOfInt_nat p.2, ← goldOfInt_nat Goldilocks.zero]
      simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1
    · unfold computeVcPoseidon2Commit
      rw [ite_true_of hAttrsLen]
      have hCS := hChunksSum (fun i => (v i).holderBlindShare) vcAttrCommitTag
      dsimp only at hCS
      rw [← hCS]
      dsimp only
      rw [← hLeafSum]
    · rw [← hEvalBool, ← hRootMerkleSum, ← hRootEq, hAccSum]
    · unfold computeVcPoseidon2Commit
      rw [ite_true_of hAttrsLen]
      have hCS := hChunksSum (fun i => (v i).presBlindShare) vcPresCommitTag
      dsimp only at hCS
      rw [← hCS]
      dsimp only
      rw [← hPresSpongeSum, ← hPresEq, hPresSum]
    · unfold computeVcScopeTag
      have hSC := hScopeChunksSum
      dsimp only at hSC
      rw [← hSC]
      dsimp only
      rw [← hScopeSpongeSum, ← hScopeEq, hScSum]

theorem verifyOpenedBlindVcRep_extract3_from_rewound
    {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {presNonce : Vec UInt8 32} {schema : VcSchema} {issuerEpoch : UInt64} {treeDepth : Nat}
    {accRoot presCommit scopeTag : Lane6} {verifierScopeLimbs : Lane4}
    {disclosed : List (Nat × Goldilocks)} {repIdx : Nat}
    {o0 o1 o2 : OpenedBlindVcRep}
    (hR1_01 : reconstructRepRound1 H presNonce repIdx o0 = reconstructRepRound1 H presNonce repIdx o1)
    (hR1_12 : reconstructRepRound1 H presNonce repIdx o1 = reconstructRepRound1 H presNonce repIdx o2)
    (hVer0 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 0 o0 = true)
    (hVer1 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 1 o1 = true)
    (hVer2 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 2 o2 = true) :
    (∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂) ∨
    ∃ (attrs : List Goldilocks) (holderBlind presBlind : Lane4)
      (leafCommit : Lane6) (boolSteps : List (Bool × Lane6)),
      (disclosed.map Prod.fst).Nodup ∧
      attrs.length = schema.arity ∧
      (∀ p ∈ disclosed, p.1 < schema.arity ∧ attrs[p.1]? = some p.2) ∧
      computeVcPoseidon2Commit schema attrs holderBlind vcAttrCommitTag = some leafCommit ∧
      boolSteps.length = treeDepth ∧
      evalVcMerklePathBool issuerEpoch 0 leafCommit boolSteps = accRoot ∧
      computeVcPoseidon2Commit schema attrs presBlind vcPresCommitTag = some presCommit ∧
      computeVcScopeTag schema.schemaId holderBlind verifierScopeLimbs = scopeTag := by
  rcases verifyOpenedBlindVcRep_extract3_finite_conflict hR1_01 hR1_12 hVer0 hVer1 hVer2 with h | h
  · exact Or.inl (vcRewoundCommitConflict_hash_collision hHLen h)
  · exact Or.inr h

/-! ### §4.5 Full `OpenedBlindVcRep` Simulation (`zkMultiRepViewEquiv`), Flagship Soundness/Hiding & 2-Phase Prover -/

/-- Self-inverse field subtraction bijection `x ↦ K - x` (`0 Classical.choice`). -/
def goldSubFromConstEquiv (K : Goldilocks) : SimpleEquiv Goldilocks Goldilocks where
  toFun x := Goldilocks.sub K x
  invFun y := Goldilocks.sub K y
  left_inv x := by
    rw [← goldOfInt_nat K, ← goldOfInt_nat x]
    simp only [goldOfInt_sub]; congr 1; omega
  right_inv y := by
    rw [← goldOfInt_nat K, ← goldOfInt_nat y]
    simp only [goldOfInt_sub]; congr 1; omega

/-- 3-party additive wire sharing of `secret` from two uniform shares `coins = (c0, c1)`. -/
def vcShareWire3 (secret : Goldilocks) (coins : Goldilocks × Goldilocks) : VcWire3
  | ⟨0, _⟩ => coins.1
  | ⟨1, _⟩ => coins.2
  | ⟨2, _⟩ => Goldilocks.sub (Goldilocks.sub secret coins.1) coins.2

private theorem vcSum3_shareWire3 (secret : Goldilocks) (coins : Goldilocks × Goldilocks) :
    vcSum3 (vcShareWire3 secret coins) = secret := by
  unfold vcSum3 vcShareWire3
  dsimp only
  rw [← goldOfInt_nat secret, ← goldOfInt_nat coins.1, ← goldOfInt_nat coins.2]
  simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega

/-- Constructive bijection (`0 Classical.choice`) between prover sharing coins `(c0, c1)` and
    the opened 2-party wire pair `(w_e, w_{(e+1)%3})` for any `secret : Goldilocks`. -/
def vcOpenedShareEquiv3 (e : Fin 3) (secret : Goldilocks) :
    SimpleEquiv (Goldilocks × Goldilocks) (Goldilocks × Goldilocks) where
  toFun c := vcPairAt (vcShareWire3 secret c) e
  invFun p :=
    match e with
    | ⟨0, _⟩ => (p.1, p.2)
    | ⟨1, _⟩ => (Goldilocks.sub (Goldilocks.sub secret p.1) p.2, p.1)
    | ⟨2, _⟩ => (p.2, Goldilocks.sub (Goldilocks.sub secret p.1) p.2)
  left_inv := fun ⟨c0, c1⟩ => by
    rcases fin3_eq_012 e with rfl | rfl | rfl
    · rfl
    · dsimp only [vcPairAt, vcShareWire3, vcNextParty3]
      refine Prod.ext ?_ rfl
      rw [← goldOfInt_nat secret, ← goldOfInt_nat c0, ← goldOfInt_nat c1]
      simp only [goldOfInt_sub]; congr 1; omega
    · dsimp only [vcPairAt, vcShareWire3, vcNextParty3]
      refine Prod.ext rfl ?_
      rw [← goldOfInt_nat secret, ← goldOfInt_nat c0, ← goldOfInt_nat c1]
      simp only [goldOfInt_sub]; congr 1; omega
  right_inv := fun ⟨p0, p1⟩ => by
    rcases fin3_eq_012 e with rfl | rfl | rfl
    · rfl
    · dsimp only [vcPairAt, vcShareWire3, vcNextParty3]
      refine Prod.ext rfl ?_
      rw [← goldOfInt_nat secret, ← goldOfInt_nat p0, ← goldOfInt_nat p1]
      simp only [goldOfInt_sub]; congr 1; omega
    · dsimp only [vcPairAt, vcShareWire3, vcNextParty3]
      refine Prod.ext ?_ rfl
      rw [← goldOfInt_nat secret, ← goldOfInt_nat p0, ← goldOfInt_nat p1]
      simp only [goldOfInt_sub]; congr 1; omega

def vcShareLane4_3 (secret : Lane4) (coins : Lane4 × Lane4) : VcLane4_3 :=
  fun i =>
    ⟨vcShareWire3 secret.x0 (coins.1.x0, coins.2.x0) i,
     vcShareWire3 secret.x1 (coins.1.x1, coins.2.x1) i,
     vcShareWire3 secret.x2 (coins.1.x2, coins.2.x2) i,
     vcShareWire3 secret.x3 (coins.1.x3, coins.2.x3) i⟩

private theorem vcSumLane4_3_share (secret : Lane4) (coins : Lane4 × Lane4) :
    vcSumLane4_3 (vcShareLane4_3 secret coins) = secret := by
  rw [vcSumLane4_3_eq]
  unfold vcShareLane4_3
  dsimp only
  rw [vcSum3_shareWire3, vcSum3_shareWire3, vcSum3_shareWire3, vcSum3_shareWire3]

private def lane4PairTupleEquiv :
    SimpleEquiv (Lane4 × Lane4)
      ((Goldilocks × Goldilocks) × (Goldilocks × Goldilocks) ×
       (Goldilocks × Goldilocks) × (Goldilocks × Goldilocks)) where
  toFun p := ((p.1.x0, p.2.x0), (p.1.x1, p.2.x1), (p.1.x2, p.2.x2), (p.1.x3, p.2.x3))
  invFun q := (⟨q.1.1, q.2.1.1, q.2.2.1.1, q.2.2.2.1⟩, ⟨q.1.2, q.2.1.2, q.2.2.1.2, q.2.2.2.2⟩)
  left_inv := fun ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ => rfl

def vcLane4OpenedShareEquiv3 (e : Fin 3) (secret : Lane4) :
    SimpleEquiv (Lane4 × Lane4) (Lane4 × Lane4) :=
  seTrans lane4PairTupleEquiv
    (seTrans
      (seProdCongr (vcOpenedShareEquiv3 e secret.x0)
        (seProdCongr (vcOpenedShareEquiv3 e secret.x1)
          (seProdCongr (vcOpenedShareEquiv3 e secret.x2)
            (vcOpenedShareEquiv3 e secret.x3))))
      (seSymm lane4PairTupleEquiv))

private theorem vcLane4OpenedShareEquiv3_toFun (e : Fin 3) (secret : Lane4) (coins : Lane4 × Lane4) :
    (vcLane4OpenedShareEquiv3 e secret).toFun coins =
      (vcShareLane4_3 secret coins e, vcShareLane4_3 secret coins (vcNextParty3 e)) := rfl

def vcShareLane6_3 (secret : Lane6) (coins : Lane6 × Lane6) : VcLane6_3 :=
  fun i =>
    ⟨vcShareWire3 secret.x0 (coins.1.x0, coins.2.x0) i,
     vcShareWire3 secret.x1 (coins.1.x1, coins.2.x1) i,
     vcShareWire3 secret.x2 (coins.1.x2, coins.2.x2) i,
     vcShareWire3 secret.x3 (coins.1.x3, coins.2.x3) i,
     vcShareWire3 secret.x4 (coins.1.x4, coins.2.x4) i,
     vcShareWire3 secret.x5 (coins.1.x5, coins.2.x5) i⟩

private theorem vcSumLane6_3_share (secret : Lane6) (coins : Lane6 × Lane6) :
    vcSumLane6_3 (vcShareLane6_3 secret coins) = secret := by
  rw [vcSumLane6_3_eq]
  unfold vcShareLane6_3
  dsimp only
  rw [vcSum3_shareWire3, vcSum3_shareWire3, vcSum3_shareWire3,
      vcSum3_shareWire3, vcSum3_shareWire3, vcSum3_shareWire3]

private def lane6PairTupleEquiv :
    SimpleEquiv (Lane6 × Lane6)
      ((Goldilocks × Goldilocks) × (Goldilocks × Goldilocks) × (Goldilocks × Goldilocks) ×
       (Goldilocks × Goldilocks) × (Goldilocks × Goldilocks) × (Goldilocks × Goldilocks)) where
  toFun p := ((p.1.x0, p.2.x0), (p.1.x1, p.2.x1), (p.1.x2, p.2.x2),
              (p.1.x3, p.2.x3), (p.1.x4, p.2.x4), (p.1.x5, p.2.x5))
  invFun q :=
    (⟨q.1.1, q.2.1.1, q.2.2.1.1, q.2.2.2.1.1, q.2.2.2.2.1.1, q.2.2.2.2.2.1⟩,
     ⟨q.1.2, q.2.1.2, q.2.2.1.2, q.2.2.2.1.2, q.2.2.2.2.1.2, q.2.2.2.2.2.2⟩)
  left_inv := fun ⟨⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ => rfl

def vcLane6OpenedShareEquiv3 (e : Fin 3) (secret : Lane6) :
    SimpleEquiv (Lane6 × Lane6) (Lane6 × Lane6) :=
  seTrans lane6PairTupleEquiv
    (seTrans
      (seProdCongr (vcOpenedShareEquiv3 e secret.x0)
        (seProdCongr (vcOpenedShareEquiv3 e secret.x1)
          (seProdCongr (vcOpenedShareEquiv3 e secret.x2)
            (seProdCongr (vcOpenedShareEquiv3 e secret.x3)
              (seProdCongr (vcOpenedShareEquiv3 e secret.x4)
                (vcOpenedShareEquiv3 e secret.x5))))))
      (seSymm lane6PairTupleEquiv))

private theorem vcLane6OpenedShareEquiv3_toFun (e : Fin 3) (secret : Lane6) (coins : Lane6 × Lane6) :
    (vcLane6OpenedShareEquiv3 e secret).toFun coins = vcPairAtLane6 (vcShareLane6_3 secret coins) e := rfl

/-- Bitwise `UInt8` XOR helpers (`0` `ofReduceBool`, `0 Classical.choice`). -/
private theorem uint8_xor_self_left (b m : UInt8) : b ^^^ (b ^^^ m) = m := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
  cases b.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;> rfl

private theorem uint8_xor_zero_right (b : UInt8) : b ^^^ 0 = b := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
  rw [show (0 : UInt8).toBitVec = 0#8 from rfl, BitVec.getLsbD_zero]
  cases b.toBitVec.getLsbD i <;> rfl

def xorBytesWithVec : {n : Nat} → List UInt8 → Vec UInt8 n → Vec UInt8 n
  | 0, _, .nil => .nil
  | _ + 1, [], .cons m ms => .cons m (xorBytesWithVec [] ms)
  | _ + 1, b :: bs, .cons m ms => .cons (b ^^^ m) (xorBytesWithVec bs ms)

private theorem xorBytesWithVec_involutive :
    ∀ {n : Nat} (bs : List UInt8) (v : Vec UInt8 n),
      xorBytesWithVec bs (xorBytesWithVec bs v) = v
  | 0, _, .nil => rfl
  | _ + 1, [], .cons m ms => by
    simp only [xorBytesWithVec]
    rw [xorBytesWithVec_involutive [] ms]
  | _ + 1, b :: bs, .cons m ms => by
    simp only [xorBytesWithVec]
    rw [uint8_xor_self_left, xorBytesWithVec_involutive bs ms]

private theorem xorBytesWithVec_zero_toList :
    ∀ {n : Nat} {bs : List UInt8},
      bs.length = n →
      (xorBytesWithVec bs (Vec.replicate n 0)).toList = bs
  | 0, [], _ => rfl
  | n + 1, b :: bs, hLen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [Vec.replicate, xorBytesWithVec, Vec.toList]
    rw [uint8_xor_zero_right, xorBytesWithVec_zero_toList hLen]

def xorBytesWithVecEquiv {n : Nat} (bs : List UInt8) : SimpleEquiv (Vec UInt8 n) (Vec UInt8 n) where
  toFun v := xorBytesWithVec bs v
  invFun v := xorBytesWithVec bs v
  left_inv := xorBytesWithVec_involutive bs
  right_inv := xorBytesWithVec_involutive bs

/-- Attribute slot sharing: pins disclosed slots to `(val, 0, 0)` and secret-shares undisclosed slots. -/
def vcShareAttrs3 (disclosed : List (Nat × Goldilocks)) :
    {n : Nat} → Nat → Vec Goldilocks n → Vec (Goldilocks × Goldilocks) n → Fin 3 → List Goldilocks
  | 0, _, .nil, .nil, _ => []
  | _ + 1, slot, .cons a as, .cons c cs, i =>
    let headShare :=
      match vcLookupDisclosed disclosed slot with
      | some _ => vcConstWire3 a i
      | none => vcShareWire3 a c i
    headShare :: vcShareAttrs3 disclosed (slot + 1) as cs i

/-- Simulator attribute-pair builder (ZERO secret witness inputs!). -/
def simAttrPairs (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    {n : Nat} → Nat → Vec (Goldilocks × Goldilocks) n → List Goldilocks × List Goldilocks
  | 0, _, .nil => ([], [])
  | _ + 1, slot, .cons p ps =>
    let hp :=
      match vcLookupDisclosed disclosed slot with
      | some pubVal => vcConstPair e pubVal
      | none => p
    let tp := simAttrPairs e disclosed (slot + 1) ps
    (hp.1 :: tp.1, hp.2 :: tp.2)

def vcAttrSharesEquiv3 (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    {n : Nat} → Nat → Vec Goldilocks n →
    SimpleEquiv (Vec (Goldilocks × Goldilocks) n) (Vec (Goldilocks × Goldilocks) n)
  | 0, _, .nil => seRefl _
  | _ + 1, slot, .cons a as =>
    let headEq :=
      match vcLookupDisclosed disclosed slot with
      | some _ => seRefl (Goldilocks × Goldilocks)
      | none => vcOpenedShareEquiv3 e a
    seDepCons headEq (fun _ => vcAttrSharesEquiv3 e disclosed (slot + 1) as)

private theorem simAttrPairs_length (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (ps : Vec (Goldilocks × Goldilocks) n),
      (simAttrPairs e disclosed slot ps).1.length = n ∧
      (simAttrPairs e disclosed slot ps).2.length = n
  | 0, _, .nil => ⟨rfl, rfl⟩
  | _ + 1, slot, .cons _ ps => by
    obtain ⟨h1, h2⟩ := simAttrPairs_length e disclosed (slot + 1) ps
    simp only [simAttrPairs, List.length_cons]
    exact ⟨by omega, by omega⟩

private theorem simAttrPairs_getElem? (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (ps : Vec (Goldilocks × Goldilocks) n) (k : Nat) (hk : k < n),
      ((simAttrPairs e disclosed slot ps).1[k]?, (simAttrPairs e disclosed slot ps).2[k]?) =
        match vcLookupDisclosed disclosed (slot + k) with
        | some pubVal => (some (vcConstPair e pubVal).1, some (vcConstPair e pubVal).2)
        | none => (some (ps.toList[k]'(by rw [Vec.toList_length]; exact hk)).1,
                   some (ps.toList[k]'(by rw [Vec.toList_length]; exact hk)).2)
  | 0, _, .nil, _, hk => nomatch hk
  | _ + 1, slot, .cons p ps, 0, _ => by
    simp only [simAttrPairs, Vec.toList, List.getElem?_cons_zero, List.getElem_cons_zero, Nat.add_zero]
    cases vcLookupDisclosed disclosed slot <;> rfl
  | _ + 1, slot, .cons p ps, k + 1, hk => by
    have hk' : k < _ := Nat.lt_of_succ_lt_succ hk
    simp only [simAttrPairs, Vec.toList, List.getElem?_cons_succ, List.getElem_cons_succ]
    rw [simAttrPairs_getElem? e disclosed (slot + 1) ps k hk']
    have hSlot : slot + 1 + k = slot + (k + 1) := by omega
    simp only [hSlot]

private theorem simAttrPairs_disclosed_ok (e : Fin 3) {arity : Nat} {disclosed : List (Nat × Goldilocks)}
    (hAsc : vcCheckDisclosedStrictAsc arity disclosed = true)
    (ps : Vec (Goldilocks × Goldilocks) arity) :
    vcCheckPartyDisclosedShares e (simAttrPairs e disclosed 0 ps).1 disclosed = true ∧
    vcCheckPartyDisclosedShares (vcNextParty3 e) (simAttrPairs e disclosed 0 ps).2 disclosed = true := by
  obtain ⟨hBounds, hNodup⟩ := vcCheckDisclosedStrictAsc_bounds_and_nodup hAsc
  have hAt : ∀ idx val, (idx, val) ∈ disclosed →
      (simAttrPairs e disclosed 0 ps).1[idx]? = some (vcExpectedDisclosedShare e val) ∧
      (simAttrPairs e disclosed 0 ps).2[idx]? = some (vcExpectedDisclosedShare (vcNextParty3 e) val) := by
    intro idx val hMem
    have hLt : idx < arity := hBounds (idx, val) hMem
    have hLook : vcLookupDisclosed disclosed idx = some val := vcLookupDisclosed_eq_some_of_nodup hNodup hMem
    have hGet := simAttrPairs_getElem? e disclosed 0 ps idx hLt
    rw [Nat.zero_add, hLook] at hGet
    dsimp only at hGet
    rw [vcConstPair_spec val e] at hGet
    injection hGet with h1 h2
    exact ⟨h1, h2⟩
  have hLoop : ∀ sub : List (Nat × Goldilocks),
      (∀ p ∈ sub, p ∈ disclosed) →
      vcCheckPartyDisclosedShares e (simAttrPairs e disclosed 0 ps).1 sub = true ∧
      vcCheckPartyDisclosedShares (vcNextParty3 e) (simAttrPairs e disclosed 0 ps).2 sub = true := by
    intro sub hSub
    induction sub with
    | nil => exact ⟨rfl, rfl⟩
    | cons hd tl ih =>
      rcases hd with ⟨idx, val⟩
      obtain ⟨h1, h2⟩ := hAt idx val (hSub (idx, val) (.head tl))
      obtain ⟨ih1, ih2⟩ := ih (fun q hq => hSub q (.tail _ hq))
      refine ⟨?_, ?_⟩
      · simp only [vcCheckPartyDisclosedShares, h1, ih1, decide_true, Bool.and_self]
      · simp only [vcCheckPartyDisclosedShares, h2, ih2, decide_true, Bool.and_self]
  exact hLoop disclosed (fun _ hp => hp)

private theorem simAttrPairs_eq_honest (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (attrs : Vec Goldilocks n) (coins : Vec (Goldilocks × Goldilocks) n),
      (∀ k : Nat, (hk : k < n) → ∀ pubVal, vcLookupDisclosed disclosed (slot + k) = some pubVal →
        attrs.toList[k]'(by rw [Vec.toList_length]; exact hk) = pubVal) →
      simAttrPairs e disclosed slot ((vcAttrSharesEquiv3 e disclosed slot attrs).toFun coins) =
        (vcShareAttrs3 disclosed slot attrs coins e,
         vcShareAttrs3 disclosed slot attrs coins (vcNextParty3 e))
  | 0, _, .nil, .nil, _ => rfl
  | _ + 1, slot, .cons a as, .cons c cs, hPin => by
    simp only [vcAttrSharesEquiv3, seDepCons, seDepConsToFun, simAttrPairs, vcShareAttrs3]
    have hTail := simAttrPairs_eq_honest e disclosed (slot + 1) as cs (fun k hk pv hL => by
      have hSlot : slot + 1 + k = slot + (k + 1) := by omega
      rw [hSlot] at hL
      exact hPin (k + 1) (Nat.succ_lt_succ hk) pv hL)
    rw [hTail]
    cases hLook : vcLookupDisclosed disclosed slot with
    | none =>
      dsimp only [vcOpenedShareEquiv3, vcPairAt]
    | some pubVal =>
      have haEq : a = pubVal := by
        have h0 := hPin 0 (Nat.zero_lt_succ _) pubVal (by rw [Nat.add_zero]; exact hLook)
        simpa [Vec.toList] using h0
      rw [haEq]
      dsimp only [seRefl]
      rw [vcConstPair_spec pubVal e]
      rfl

private theorem vcShareAttrs3_length (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (attrs : Vec Goldilocks n) (coins : Vec (Goldilocks × Goldilocks) n) (i : Fin 3),
      (vcShareAttrs3 disclosed slot attrs coins i).length = n
  | 0, _, .nil, .nil, _ => rfl
  | _ + 1, slot, .cons _ as, .cons _ cs, i => by
    simp only [vcShareAttrs3, List.length_cons]
    rw [vcShareAttrs3_length disclosed (slot + 1) as cs i]

private theorem vcShareAttrs3_sum_getElem? (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (attrs : Vec Goldilocks n) (coins : Vec (Goldilocks × Goldilocks) n) (k : Nat),
      vcSum3 (fun i => vcAttrAt (vcShareAttrs3 disclosed slot attrs coins i) k) =
        vcAttrAt attrs.toList k
  | 0, _, .nil, .nil, k => by
    unfold vcAttrAt
    simp only [vcShareAttrs3, Vec.toList, List.getElem?_nil, Option.getD]
    exact vcSum3_zero
  | _ + 1, slot, .cons a as, .cons c cs, 0 => by
    unfold vcAttrAt
    simp only [vcShareAttrs3, Vec.toList, List.getElem?_cons_zero, Option.getD]
    cases vcLookupDisclosed disclosed slot with
    | some _ => exact vcSum3_constWire a
    | none => exact vcSum3_shareWire3 a c
  | _ + 1, slot, .cons _ as, .cons _ cs, k + 1 => by
    have ih := vcShareAttrs3_sum_getElem? disclosed (slot + 1) as cs k
    unfold vcAttrAt at ih ⊢
    simp only [vcShareAttrs3, Vec.toList, List.getElem?_cons_succ]
    exact ih

/-- Share boolean Merkle path witness `Vec (Bool × Lane6) D` into `Vec (VcWire3 × VcLane6_3) D`. -/
def vcShareMerkleSteps3 :
    {D : Nat} → Vec (Bool × Lane6) D → Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D →
    Vec (VcWire3 × VcLane6_3) D
  | 0, .nil, .nil => .nil
  | _ + 1, .cons (b, sib) rest, .cons (bc, sc) cs =>
    let bGold := if b then Goldilocks.one else Goldilocks.zero
    .cons (vcShareWire3 bGold bc, vcShareLane6_3 sib sc) (vcShareMerkleSteps3 rest cs)

def vcMerkleStepsEquiv3 (e : Fin 3) :
    {D : Nat} → Vec (Bool × Lane6) D →
    SimpleEquiv (Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D)
                (Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D)
  | 0, .nil => seRefl _
  | _ + 1, .cons (b, sib) rest =>
    let bGold := if b then Goldilocks.one else Goldilocks.zero
    seDepCons
      (seProdCongr (vcOpenedShareEquiv3 e bGold) (vcLane6OpenedShareEquiv3 e sib))
      (fun _ => vcMerkleStepsEquiv3 e rest)

/-! #### Gate-by-Gate Full-Circuit Simulator & `SimpleEquiv` Coin-to-Output Bijections -/

/-- Simulator step for one ZKBoo multiplication gate (ZERO secret witness inputs!). -/
def simMulGate (px py : Goldilocks × Goldilocks) (rE rE1 simOutE1 : Goldilocks) :
    (PartyMulView × PartyMulView) × (Goldilocks × Goldilocks) :=
  let outE := vcMulExpectedPair px.1 px.2 py.1 py.2 rE rE1
  (({ r := rE, out := outE }, { r := rE1, out := simOutE1 }), (outE, simOutE1))

/-- Bijection mapping unopened coin `rU` to party `(e+1)%3`'s multiplication output share `out_{e+1}`. -/
def mulGateOutEquiv (e : Fin 3) (wx wy : VcWire3) (rE1 : Goldilocks) :
    SimpleEquiv Goldilocks Goldilocks :=
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  let crossE1 := Goldilocks.add (Goldilocks.mul (wx e1) (wy e1))
    (Goldilocks.add (Goldilocks.mul (wx e1) (wy e2)) (Goldilocks.mul (wx e2) (wy e1)))
  goldSubFromConstEquiv (Goldilocks.add crossE1 rE1)

private theorem simMulGate_eq_honest (e : Fin 3) (wx wy : VcWire3) (rE rE1 rU : Goldilocks) :
    let r := mkParty3At e rE rE1 rU
    simMulGate (vcPairAt wx e) (vcPairAt wy e) rE rE1 ((mulGateOutEquiv e wx wy rE1).toFun rU) =
      ((honestMulView3 wx wy r e, honestMulView3 wx wy r (vcNextParty3 e)),
       vcPairAt (vcMulGate3 wx wy r) e) := by
  unfold simMulGate mulGateOutEquiv goldSubFromConstEquiv honestMulView3 vcMulGate3 vcPairAt vcMulExpectedPair
  dsimp only
  rw [mkParty3At_e, mkParty3At_next, vcNextParty3_next_eq_unopened, mkParty3At_unopened]

private theorem pairCheckMul_sim (px py : Goldilocks × Goldilocks) (rE rE1 simOutE1 : Goldilocks) :
    pairCheckMul px py (simMulGate px py rE rE1 simOutE1).1.1
      (simMulGate px py rE rE1 simOutE1).1.2 =
      some (simMulGate px py rE rE1 simOutE1).2 := by
  unfold pairCheckMul simMulGate
  dsimp only
  simp only [↓reduceIte]

/-- Simulator step for one S-box (`x ↦ x^7`, 4 multiplication gates, ZERO secret witness inputs!). -/
def simSbox (px : Goldilocks × Goldilocks) (scE scE1 simOutE1 : SboxCoins) :
    (PartySboxView × PartySboxView) × (Goldilocks × Goldilocks) :=
  let m1 := simMulGate px px scE.1 scE1.1 simOutE1.1
  let m2 := simMulGate m1.2 px scE.2.1 scE1.2.1 simOutE1.2.1
  let m3 := simMulGate m1.2 m1.2 scE.2.2.1 scE1.2.2.1 simOutE1.2.2.1
  let m4 := simMulGate m3.2 m2.2 scE.2.2.2 scE1.2.2.2 simOutE1.2.2.2
  ((⟨m1.1.1, m2.1.1, m3.1.1, m4.1.1⟩, ⟨m1.1.2, m2.1.2, m3.1.2, m4.1.2⟩), m4.2)

def sboxOutEquiv (e : Fin 3) (wx : VcWire3) (scE scE1 : SboxCoins) :
    SimpleEquiv SboxCoins SboxCoins :=
  seDepProd (mulGateOutEquiv e wx wx scE1.1) fun r1U =>
    let w2 := vcMulGate3 wx wx (mkParty3At e scE.1 scE1.1 r1U)
    seDepProd (mulGateOutEquiv e w2 wx scE1.2.1) fun r2U =>
      let w3 := vcMulGate3 w2 wx (mkParty3At e scE.2.1 scE1.2.1 r2U)
      seDepProd (mulGateOutEquiv e w2 w2 scE1.2.2.1) fun r3U =>
        let w4 := vcMulGate3 w2 w2 (mkParty3At e scE.2.2.1 scE1.2.2.1 r3U)
        mulGateOutEquiv e w4 w3 scE1.2.2.2

private theorem simSbox_eq_honest (e : Fin 3) (wx : VcWire3) (scE scE1 scU : SboxCoins) :
    let sc := mkParty3At e scE scE1 scU
    simSbox (vcPairAt wx e) scE scE1 ((sboxOutEquiv e wx scE scE1).toFun scU) =
      (((honestSboxView3 wx sc).1 e, (honestSboxView3 wx sc).1 (vcNextParty3 e)),
       vcPairAt (honestSboxView3 wx sc).2 e) := by
  rcases scE with ⟨r1E, r2E, r3E, r4E⟩
  rcases scE1 with ⟨r1E1, r2E1, r3E1, r4E1⟩
  rcases scU with ⟨r1U, r2U, r3U, r4U⟩
  dsimp only [sboxOutEquiv, seDepProd, simSbox, honestSboxView3]
  have hProj1 : (fun i => (mkParty3At e (r1E, r2E, r3E, r4E) (r1E1, r2E1, r3E1, r4E1) (r1U, r2U, r3U, r4U) i).1) =
      mkParty3At e r1E r1E1 r1U := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hProj2 : (fun i => (mkParty3At e (r1E, r2E, r3E, r4E) (r1E1, r2E1, r3E1, r4E1) (r1U, r2U, r3U, r4U) i).2.1) =
      mkParty3At e r2E r2E1 r2U := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hProj3 : (fun i => (mkParty3At e (r1E, r2E, r3E, r4E) (r1E1, r2E1, r3E1, r4E1) (r1U, r2U, r3U, r4U) i).2.2.1) =
      mkParty3At e r3E r3E1 r3U := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hProj4 : (fun i => (mkParty3At e (r1E, r2E, r3E, r4E) (r1E1, r2E1, r3E1, r4E1) (r1U, r2U, r3U, r4U) i).2.2.2) =
      mkParty3At e r4E r4E1 r4U := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  rw [hProj1, hProj2, hProj3, hProj4]
  rw [simMulGate_eq_honest]; dsimp only
  rw [simMulGate_eq_honest]; dsimp only
  rw [simMulGate_eq_honest]; dsimp only
  rw [simMulGate_eq_honest]

private theorem extractSboxCoins_sim (px : Goldilocks × Goldilocks) (scE scE1 simOutE1 : SboxCoins) :
    extractSboxCoins (simSbox px scE scE1 simOutE1).1.1 = scE ∧
    extractSboxCoins (simSbox px scE scE1 simOutE1).1.2 = scE1 := by
  rcases scE with ⟨_, _, _, _⟩
  rcases scE1 with ⟨_, _, _, _⟩
  exact ⟨rfl, rfl⟩

private theorem pairCheckSbox_sim (px : Goldilocks × Goldilocks) (scE scE1 simOutE1 : SboxCoins) :
    pairCheckSbox px (simSbox px scE scE1 simOutE1).1.1 (simSbox px scE scE1 simOutE1).1.2 =
      some (simSbox px scE scE1 simOutE1).2 := by
  unfold pairCheckSbox simSbox
  dsimp only
  rw [pairCheckMul_sim]; dsimp only
  rw [pairCheckMul_sim]; dsimp only
  rw [pairCheckMul_sim]; dsimp only
  rw [pairCheckMul_sim]

private def extRoundCoinsTupleEquiv :
    SimpleEquiv ExtRoundCoins
      (SboxCoins × SboxCoins × SboxCoins × SboxCoins × SboxCoins × SboxCoins ×
       SboxCoins × SboxCoins × SboxCoins × SboxCoins × SboxCoins × SboxCoins) where
  toFun c := (c.s0, c.s1, c.s2, c.s3, c.s4, c.s5, c.s6, c.s7, c.s8, c.s9, c.s10, c.s11)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1,
               t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1,
               t.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.2⟩
  left_inv := fun ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ => rfl

def simExtRound (e : Fin 3) (rc : Poseidon2State12)
    (st : Poseidon2State12 × Poseidon2State12) (ecE ecE1 simOutE1 : ExtRoundCoins) :
    (PartyExtRoundView × PartyExtRoundView) × (Poseidon2State12 × Poseidon2State12) :=
  let run (f : Poseidon2State12 → Goldilocks) (sel : ExtRoundCoins → SboxCoins) :=
    simSbox (vcPairAddConst e (f st.1, f st.2) (f rc)) (sel ecE) (sel ecE1) (sel simOutE1)
  let r0 := run (·.b0.x0) (·.s0); let r1 := run (·.b0.x1) (·.s1)
  let r2 := run (·.b0.x2) (·.s2); let r3 := run (·.b0.x3) (·.s3)
  let r4 := run (·.b1.x0) (·.s4); let r5 := run (·.b1.x1) (·.s5)
  let r6 := run (·.b1.x2) (·.s6); let r7 := run (·.b1.x3) (·.s7)
  let r8 := run (·.b2.x0) (·.s8); let r9 := run (·.b2.x1) (·.s9)
  let r10 := run (·.b2.x2) (·.s10); let r11 := run (·.b2.x3) (·.s11)
  ((⟨r0.1.1, r1.1.1, r2.1.1, r3.1.1, r4.1.1, r5.1.1, r6.1.1, r7.1.1, r8.1.1, r9.1.1, r10.1.1, r11.1.1⟩,
    ⟨r0.1.2, r1.1.2, r2.1.2, r3.1.2, r4.1.2, r5.1.2, r6.1.2, r7.1.2, r8.1.2, r9.1.2, r10.1.2, r11.1.2⟩),
   (applyME ⟨⟨r0.2.1, r1.2.1, r2.2.1, r3.2.1⟩, ⟨r4.2.1, r5.2.1, r6.2.1, r7.2.1⟩, ⟨r8.2.1, r9.2.1, r10.2.1, r11.2.1⟩⟩,
    applyME ⟨⟨r0.2.2, r1.2.2, r2.2.2, r3.2.2⟩, ⟨r4.2.2, r5.2.2, r6.2.2, r7.2.2⟩, ⟨r8.2.2, r9.2.2, r10.2.2, r11.2.2⟩⟩))

def extRoundOutEquiv (e : Fin 3) (rc : Poseidon2State12) (st : VcState12_3)
    (ecE ecE1 : ExtRoundCoins) : SimpleEquiv ExtRoundCoins ExtRoundCoins :=
  let eqLane (f : Poseidon2State12 → Goldilocks) (sel : ExtRoundCoins → SboxCoins) :=
    sboxOutEquiv e (vcWireAddConst3 (fun i => f (st i)) (f rc)) (sel ecE) (sel ecE1)
  seTrans extRoundCoinsTupleEquiv
    (seTrans
      (seProdCongr (eqLane (·.b0.x0) (·.s0))
      (seProdCongr (eqLane (·.b0.x1) (·.s1))
      (seProdCongr (eqLane (·.b0.x2) (·.s2))
      (seProdCongr (eqLane (·.b0.x3) (·.s3))
      (seProdCongr (eqLane (·.b1.x0) (·.s4))
      (seProdCongr (eqLane (·.b1.x1) (·.s5))
      (seProdCongr (eqLane (·.b1.x2) (·.s6))
      (seProdCongr (eqLane (·.b1.x3) (·.s7))
      (seProdCongr (eqLane (·.b2.x0) (·.s8))
      (seProdCongr (eqLane (·.b2.x1) (·.s9))
      (seProdCongr (eqLane (·.b2.x2) (·.s10))
                   (eqLane (·.b2.x3) (·.s11)))))))))))))
      (seSymm extRoundCoinsTupleEquiv))

private theorem simExtRound_eq_honest (e : Fin 3) (rc : Poseidon2State12) (st : VcState12_3)
    (ecE ecE1 ecU : ExtRoundCoins) :
    let ec := mkParty3At e ecE ecE1 ecU
    simExtRound e rc (vcPairAtState12 st e) ecE ecE1 ((extRoundOutEquiv e rc st ecE ecE1).toFun ecU) =
      (((honestExtRound3 rc st ec).1 e, (honestExtRound3 rc st ec).1 (vcNextParty3 e)),
       vcPairAtState12 (honestExtRound3 rc st ec).2 e) := by
  have hAt : ∀ f : Poseidon2State12 → Goldilocks,
      vcPairAddConst e (f (st e), f (st (vcNextParty3 e))) (f rc) =
        vcPairAt (vcWireAddConst3 (fun i => f (st i)) (f rc)) e :=
    fun f => vcPairAddConst_spec (fun i => f (st i)) (f rc) e
  have hSel : ∀ sel : ExtRoundCoins → SboxCoins,
      (fun i => sel (mkParty3At e ecE ecE1 ecU i)) = mkParty3At e (sel ecE) (sel ecE1) (sel ecU) := by
    intro sel; funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  unfold simExtRound extRoundOutEquiv honestExtRound3 vcPairAtState12 vcExtRoundOut3
  dsimp only [seTrans, seProdCongr, seSymm, extRoundCoinsTupleEquiv]
  rw [hAt (·.b0.x0), hAt (·.b0.x1), hAt (·.b0.x2), hAt (·.b0.x3),
      hAt (·.b1.x0), hAt (·.b1.x1), hAt (·.b1.x2), hAt (·.b1.x3),
      hAt (·.b2.x0), hAt (·.b2.x1), hAt (·.b2.x2), hAt (·.b2.x3),
      hSel (·.s0), hSel (·.s1), hSel (·.s2), hSel (·.s3),
      hSel (·.s4), hSel (·.s5), hSel (·.s6), hSel (·.s7),
      hSel (·.s8), hSel (·.s9), hSel (·.s10), hSel (·.s11),
      simSbox_eq_honest, simSbox_eq_honest, simSbox_eq_honest, simSbox_eq_honest,
      simSbox_eq_honest, simSbox_eq_honest, simSbox_eq_honest, simSbox_eq_honest,
      simSbox_eq_honest, simSbox_eq_honest, simSbox_eq_honest, simSbox_eq_honest]
  rfl

private theorem extractExtRoundCoins_sim (e : Fin 3) (rc : Poseidon2State12)
    (st : Poseidon2State12 × Poseidon2State12) (ecE ecE1 simOutE1 : ExtRoundCoins) :
    extractExtRoundCoins (simExtRound e rc st ecE ecE1 simOutE1).1.1 = ecE ∧
    extractExtRoundCoins (simExtRound e rc st ecE ecE1 simOutE1).1.2 = ecE1 := by
  rcases ecE with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  rcases ecE1 with ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩
  unfold extractExtRoundCoins simExtRound
  dsimp only
  simp only [(extractSboxCoins_sim _ _ _ _).1, (extractSboxCoins_sim _ _ _ _).2, and_self]

private theorem pairCheckExtRound_sim (e : Fin 3) (rc : Poseidon2State12)
    (st : Poseidon2State12 × Poseidon2State12) (ecE ecE1 simOutE1 : ExtRoundCoins) :
    pairCheckExtRound e rc (simExtRound e rc st ecE ecE1 simOutE1).1.1
      (simExtRound e rc st ecE ecE1 simOutE1).1.2 st =
      some (simExtRound e rc st ecE ecE1 simOutE1).2 := by
  unfold pairCheckExtRound simExtRound
  dsimp only
  simp only [pairCheckSbox_sim]

def simIntRound (e : Fin 3) (rc : Goldilocks)
    (st : Poseidon2State12 × Poseidon2State12) (scE scE1 simOutE1 : SboxCoins) :
    (PartySboxView × PartySboxView) × (Poseidon2State12 × Poseidon2State12) :=
  let r0 := simSbox (vcPairAddConst e (st.1.b0.x0, st.2.b0.x0) rc) scE scE1 simOutE1
  (r0.1,
   (applyMI ⟨⟨r0.2.1, st.1.b0.x1, st.1.b0.x2, st.1.b0.x3⟩, st.1.b1, st.1.b2⟩,
    applyMI ⟨⟨r0.2.2, st.2.b0.x1, st.2.b0.x2, st.2.b0.x3⟩, st.2.b1, st.2.b2⟩))

def intRoundOutEquiv (e : Fin 3) (rc : Goldilocks) (st : VcState12_3)
    (scE scE1 : SboxCoins) : SimpleEquiv SboxCoins SboxCoins :=
  sboxOutEquiv e (vcWireAddConst3 (fun i => (st i).b0.x0) rc) scE scE1

private theorem simIntRound_eq_honest (e : Fin 3) (rc : Goldilocks) (st : VcState12_3)
    (scE scE1 scU : SboxCoins) :
    let sc := mkParty3At e scE scE1 scU
    simIntRound e rc (vcPairAtState12 st e) scE scE1 ((intRoundOutEquiv e rc st scE scE1).toFun scU) =
      (((honestIntRound3 rc st sc).1 e, (honestIntRound3 rc st sc).1 (vcNextParty3 e)),
       vcPairAtState12 (honestIntRound3 rc st sc).2 e) := by
  unfold simIntRound intRoundOutEquiv honestIntRound3 vcPairAtState12 vcIntRoundOut3
  dsimp only
  rw [show ((st e).b0.x0, (st (vcNextParty3 e)).b0.x0) = vcPairAt (fun i => (st i).b0.x0) e from rfl,
      vcPairAddConst_spec (fun i => (st i).b0.x0) rc e, simSbox_eq_honest]
  rfl

private theorem pairCheckIntRound_sim (e : Fin 3) (rc : Goldilocks)
    (st : Poseidon2State12 × Poseidon2State12) (scE scE1 simOutE1 : SboxCoins) :
    pairCheckIntRound e rc (simIntRound e rc st scE scE1 simOutE1).1.1
      (simIntRound e rc st scE scE1 simOutE1).1.2 st =
      some (simIntRound e rc st scE scE1 simOutE1).2 := by
  unfold pairCheckIntRound simIntRound
  dsimp only
  rw [pairCheckSbox_sim]

def simExtRounds (e : Fin 3) :
    (rcs : List Poseidon2State12) → (Poseidon2State12 × Poseidon2State12) →
    Vec ExtRoundCoins rcs.length → Vec ExtRoundCoins rcs.length → Vec ExtRoundCoins rcs.length →
    (List PartyExtRoundView × List PartyExtRoundView) × (Poseidon2State12 × Poseidon2State12)
  | [], st, .nil, .nil, .nil => (([], []), st)
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 =>
    let hd := simExtRound e rc st cE cE1 oE1
    let tl := simExtRounds e rcs hd.2 csE csE1 osE1
    ((hd.1.1 :: tl.1.1, hd.1.2 :: tl.1.2), tl.2)

def extRoundsOutEquiv (e : Fin 3) :
    (rcs : List Poseidon2State12) → VcState12_3 →
    Vec ExtRoundCoins rcs.length → Vec ExtRoundCoins rcs.length →
    SimpleEquiv (Vec ExtRoundCoins rcs.length) (Vec ExtRoundCoins rcs.length)
  | [], _, .nil, .nil => seRefl _
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1 =>
    seDepCons (extRoundOutEquiv e rc st cE cE1) fun cU =>
      extRoundsOutEquiv e rcs (honestExtRound3 rc st (mkParty3At e cE cE1 cU)).2 csE csE1

private theorem simExtRounds_eq_honest (e : Fin 3) :
    ∀ (rcs : List Poseidon2State12) (st : VcState12_3)
      (csE csE1 csU : Vec ExtRoundCoins rcs.length),
      let cs := mkParty3At e csE csE1 csU
      simExtRounds e rcs (vcPairAtState12 st e) csE csE1
        ((extRoundsOutEquiv e rcs st csE csE1).toFun csU) =
        (((honestExtRounds3 rcs st cs).1 e, (honestExtRounds3 rcs st cs).1 (vcNextParty3 e)),
         vcPairAtState12 (honestExtRounds3 rcs st cs).2 e)
  | [], _, .nil, .nil, .nil => rfl
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1, .cons cU csU => by
    simp only [extRoundsOutEquiv, seDepCons, seDepConsToFun, simExtRounds, honestExtRounds3]
    have hHead : (fun i => (mkParty3At e (Vec.cons cE csE) (Vec.cons cE1 csE1) (Vec.cons cU csU) i).head) =
        mkParty3At e cE cE1 cU := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hTail : (fun i => (mkParty3At e (Vec.cons cE csE) (Vec.cons cE1 csE1) (Vec.cons cU csU) i).tail) =
        mkParty3At e csE csE1 csU := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    rw [hHead, hTail, simExtRound_eq_honest]
    dsimp only
    rw [simExtRounds_eq_honest e rcs _ csE csE1 csU]

private theorem extractExtRoundsCoins_sim (e : Fin 3) :
    ∀ (rcs : List Poseidon2State12) (st : Poseidon2State12 × Poseidon2State12)
      (csE csE1 osE1 : Vec ExtRoundCoins rcs.length),
      extractExtRoundsCoins rcs (simExtRounds e rcs st csE csE1 osE1).1.1 = some csE ∧
      extractExtRoundsCoins rcs (simExtRounds e rcs st csE csE1 osE1).1.2 = some csE1
  | [], _, .nil, .nil, .nil => ⟨rfl, rfl⟩
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 => by
    simp only [simExtRounds, extractExtRoundsCoins]
    obtain ⟨ih1, ih2⟩ := extractExtRoundsCoins_sim e rcs (simExtRound e rc st cE cE1 oE1).2 csE csE1 osE1
    obtain ⟨h1, h2⟩ := extractExtRoundCoins_sim e rc st cE cE1 oE1
    rw [ih1, ih2, h1, h2]
    exact ⟨rfl, rfl⟩

private theorem pairCheckExtRounds_sim (e : Fin 3) :
    ∀ (rcs : List Poseidon2State12) (st : Poseidon2State12 × Poseidon2State12)
      (csE csE1 osE1 : Vec ExtRoundCoins rcs.length),
      pairCheckExtRounds e rcs (simExtRounds e rcs st csE csE1 osE1).1.1
        (simExtRounds e rcs st csE csE1 osE1).1.2 st =
        some (simExtRounds e rcs st csE csE1 osE1).2
  | [], _, .nil, .nil, .nil => rfl
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 => by
    simp only [simExtRounds, pairCheckExtRounds]
    rw [pairCheckExtRound_sim]
    exact pairCheckExtRounds_sim e rcs _ csE csE1 osE1

def simIntRounds (e : Fin 3) :
    (rcs : List Goldilocks) → (Poseidon2State12 × Poseidon2State12) →
    Vec SboxCoins rcs.length → Vec SboxCoins rcs.length → Vec SboxCoins rcs.length →
    (List PartySboxView × List PartySboxView) × (Poseidon2State12 × Poseidon2State12)
  | [], st, .nil, .nil, .nil => (([], []), st)
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 =>
    let hd := simIntRound e rc st cE cE1 oE1
    let tl := simIntRounds e rcs hd.2 csE csE1 osE1
    ((hd.1.1 :: tl.1.1, hd.1.2 :: tl.1.2), tl.2)

def intRoundsOutEquiv (e : Fin 3) :
    (rcs : List Goldilocks) → VcState12_3 →
    Vec SboxCoins rcs.length → Vec SboxCoins rcs.length →
    SimpleEquiv (Vec SboxCoins rcs.length) (Vec SboxCoins rcs.length)
  | [], _, .nil, .nil => seRefl _
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1 =>
    seDepCons (intRoundOutEquiv e rc st cE cE1) fun cU =>
      intRoundsOutEquiv e rcs (honestIntRound3 rc st (mkParty3At e cE cE1 cU)).2 csE csE1

private theorem simIntRounds_eq_honest (e : Fin 3) :
    ∀ (rcs : List Goldilocks) (st : VcState12_3)
      (csE csE1 csU : Vec SboxCoins rcs.length),
      let cs := mkParty3At e csE csE1 csU
      simIntRounds e rcs (vcPairAtState12 st e) csE csE1
        ((intRoundsOutEquiv e rcs st csE csE1).toFun csU) =
        (((honestIntRounds3 rcs st cs).1 e, (honestIntRounds3 rcs st cs).1 (vcNextParty3 e)),
         vcPairAtState12 (honestIntRounds3 rcs st cs).2 e)
  | [], _, .nil, .nil, .nil => rfl
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1, .cons cU csU => by
    simp only [intRoundsOutEquiv, seDepCons, seDepConsToFun, simIntRounds, honestIntRounds3]
    have hHead : (fun i => (mkParty3At e (Vec.cons cE csE) (Vec.cons cE1 csE1) (Vec.cons cU csU) i).head) =
        mkParty3At e cE cE1 cU := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hTail : (fun i => (mkParty3At e (Vec.cons cE csE) (Vec.cons cE1 csE1) (Vec.cons cU csU) i).tail) =
        mkParty3At e csE csE1 csU := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    rw [hHead, hTail, simIntRound_eq_honest]
    dsimp only
    rw [simIntRounds_eq_honest e rcs _ csE csE1 csU]

private theorem extractIntRoundsCoins_sim (e : Fin 3) :
    ∀ (rcs : List Goldilocks) (st : Poseidon2State12 × Poseidon2State12)
      (csE csE1 osE1 : Vec SboxCoins rcs.length),
      extractIntRoundsCoins rcs (simIntRounds e rcs st csE csE1 osE1).1.1 = some csE ∧
      extractIntRoundsCoins rcs (simIntRounds e rcs st csE csE1 osE1).1.2 = some csE1
  | [], _, .nil, .nil, .nil => ⟨rfl, rfl⟩
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 => by
    simp only [simIntRounds, extractIntRoundsCoins]
    obtain ⟨ih1, ih2⟩ := extractIntRoundsCoins_sim e rcs (simIntRound e rc st cE cE1 oE1).2 csE csE1 osE1
    obtain ⟨h1, h2⟩ := extractSboxCoins_sim (vcPairAddConst e (st.1.b0.x0, st.2.b0.x0) rc) cE cE1 oE1
    dsimp only [simIntRound] at *
    rw [ih1, ih2, h1, h2]
    exact ⟨rfl, rfl⟩

private theorem pairCheckIntRounds_sim (e : Fin 3) :
    ∀ (rcs : List Goldilocks) (st : Poseidon2State12 × Poseidon2State12)
      (csE csE1 osE1 : Vec SboxCoins rcs.length),
      pairCheckIntRounds e rcs (simIntRounds e rcs st csE csE1 osE1).1.1
        (simIntRounds e rcs st csE csE1 osE1).1.2 st =
        some (simIntRounds e rcs st csE csE1 osE1).2
  | [], _, .nil, .nil, .nil => rfl
  | rc :: rcs, st, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 => by
    simp only [simIntRounds, pairCheckIntRounds]
    rw [pairCheckIntRound_sim]
    exact pairCheckIntRounds_sim e rcs _ csE csE1 osE1

private def perm12CoinsTupleEquiv :
    SimpleEquiv Perm12Coins
      (Vec ExtRoundCoins poseidon2InitialExtConsts.length ×
       Vec SboxCoins poseidon2InternalConsts.length ×
       Vec ExtRoundCoins poseidon2TerminalExtConsts.length) where
  toFun c := (c.initExt, c.internal, c.termExt)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

def simRawPerm12 (e : Fin 3) (st : Poseidon2State12 × Poseidon2State12)
    (pcE pcE1 osE1 : Perm12Coins) :
    (PartyPerm12View × PartyPerm12View) × (Poseidon2State12 × Poseidon2State12) :=
  let s0 := (applyME st.1, applyME st.2)
  let r1 := simExtRounds e poseidon2InitialExtConsts s0 pcE.initExt pcE1.initExt osE1.initExt
  let r2 := simIntRounds e poseidon2InternalConsts r1.2 pcE.internal pcE1.internal osE1.internal
  let r3 := simExtRounds e poseidon2TerminalExtConsts r2.2 pcE.termExt pcE1.termExt osE1.termExt
  ((⟨r1.1.1, r2.1.1, r3.1.1⟩, ⟨r1.1.2, r2.1.2, r3.1.2⟩), r3.2)

def perm12OutEquiv (e : Fin 3) (st : VcState12_3) (pcE pcE1 : Perm12Coins) :
    SimpleEquiv Perm12Coins Perm12Coins :=
  let s0 : VcState12_3 := fun i => applyME (st i)
  seTrans perm12CoinsTupleEquiv
    (seTrans
      (seDepProd (extRoundsOutEquiv e poseidon2InitialExtConsts s0 pcE.initExt pcE1.initExt) fun c1U =>
        let st1 := (honestExtRounds3 poseidon2InitialExtConsts s0 (mkParty3At e pcE.initExt pcE1.initExt c1U)).2
        seDepProd (intRoundsOutEquiv e poseidon2InternalConsts st1 pcE.internal pcE1.internal) fun c2U =>
          let st2 := (honestIntRounds3 poseidon2InternalConsts st1 (mkParty3At e pcE.internal pcE1.internal c2U)).2
          extRoundsOutEquiv e poseidon2TerminalExtConsts st2 pcE.termExt pcE1.termExt)
      (seSymm perm12CoinsTupleEquiv))

private theorem simRawPerm12_eq_honest (e : Fin 3) (st : VcState12_3) (pcE pcE1 pcU : Perm12Coins) :
    let pc := mkParty3At e pcE pcE1 pcU
    simRawPerm12 e (vcPairAtState12 st e) pcE pcE1 ((perm12OutEquiv e st pcE pcE1).toFun pcU) =
      (((honestRawPerm12_3 st pc).1 e, (honestRawPerm12_3 st pc).1 (vcNextParty3 e)),
       vcPairAtState12 (honestRawPerm12_3 st pc).2 e) := by
  have h1 : (fun i => (mkParty3At e pcE pcE1 pcU i).initExt) = mkParty3At e pcE.initExt pcE1.initExt pcU.initExt := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have h2 : (fun i => (mkParty3At e pcE pcE1 pcU i).internal) = mkParty3At e pcE.internal pcE1.internal pcU.internal := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have h3 : (fun i => (mkParty3At e pcE pcE1 pcU i).termExt) = mkParty3At e pcE.termExt pcE1.termExt pcU.termExt := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  unfold simRawPerm12 perm12OutEquiv honestRawPerm12_3
  dsimp only [seTrans, seDepProd, seSymm, perm12CoinsTupleEquiv]
  rw [h1, h2, h3]
  have hs0 : (applyME (vcPairAtState12 st e).1, applyME (vcPairAtState12 st e).2) =
      vcPairAtState12 (fun i => applyME (st i)) e := rfl
  rw [hs0, simExtRounds_eq_honest]; dsimp only
  rw [simIntRounds_eq_honest]; dsimp only
  rw [simExtRounds_eq_honest]

private theorem extractPerm12Coins_sim (e : Fin 3) (st : Poseidon2State12 × Poseidon2State12)
    (pcE pcE1 osE1 : Perm12Coins) :
    extractPerm12Coins (simRawPerm12 e st pcE pcE1 osE1).1.1 = some pcE ∧
    extractPerm12Coins (simRawPerm12 e st pcE pcE1 osE1).1.2 = some pcE1 := by
  rcases pcE with ⟨a1, a2, a3⟩
  rcases pcE1 with ⟨b1, b2, b3⟩
  unfold extractPerm12Coins simRawPerm12
  dsimp only
  obtain ⟨e1, f1⟩ := extractExtRoundsCoins_sim e poseidon2InitialExtConsts _ a1 b1 osE1.initExt
  obtain ⟨e2, f2⟩ := extractIntRoundsCoins_sim e poseidon2InternalConsts _ a2 b2 osE1.internal
  obtain ⟨e3, f3⟩ := extractExtRoundsCoins_sim e poseidon2TerminalExtConsts _ a3 b3 osE1.termExt
  rw [e1, e2, e3, f1, f2, f3]
  exact ⟨rfl, rfl⟩

private theorem pairCheckRawPerm12_sim (e : Fin 3) (st : Poseidon2State12 × Poseidon2State12)
    (pcE pcE1 osE1 : Perm12Coins) :
    pairCheckRawPerm12 e (simRawPerm12 e st pcE pcE1 osE1).1.1
      (simRawPerm12 e st pcE pcE1 osE1).1.2 st =
      some (simRawPerm12 e st pcE pcE1 osE1).2 := by
  unfold pairCheckRawPerm12 simRawPerm12
  dsimp only
  rw [pairCheckExtRounds_sim]; dsimp only
  rw [pairCheckIntRounds_sim]; dsimp only
  rw [pairCheckExtRounds_sim]

private def sponge3CoinsTupleEquiv :
    SimpleEquiv Sponge3Coins (Perm12Coins × Perm12Coins × Perm12Coins) where
  toFun c := (c.perm1, c.perm2, c.perm3)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

def simSponge3Perm (e : Fin 3) (c0 c1 c2 : Lane6 × Lane6)
    (scE scE1 osE1 : Sponge3Coins) :
    (PartySponge3PermView × PartySponge3PermView) × (Lane6 × Lane6) :=
  let s1 := (mkState12Of6 c0.1 lane6Zero, mkState12Of6 c0.2 lane6Zero)
  let r1 := simRawPerm12 e s1 scE.perm1 scE1.perm1 osE1.perm1
  let s2 := (mkState12Of6 (lane6Add (state12Rate6 r1.2.1) c1.1) (state12Cap6 r1.2.1),
             mkState12Of6 (lane6Add (state12Rate6 r1.2.2) c1.2) (state12Cap6 r1.2.2))
  let r2 := simRawPerm12 e s2 scE.perm2 scE1.perm2 osE1.perm2
  let s3 := (mkState12Of6 (lane6Add (state12Rate6 r2.2.1) c2.1) (state12Cap6 r2.2.1),
             mkState12Of6 (lane6Add (state12Rate6 r2.2.2) c2.2) (state12Cap6 r2.2.2))
  let r3 := simRawPerm12 e s3 scE.perm3 scE1.perm3 osE1.perm3
  ((⟨r1.1.1, r2.1.1, r3.1.1⟩, ⟨r1.1.2, r2.1.2, r3.1.2⟩), (state12Rate6 r3.2.1, state12Rate6 r3.2.2))

def sponge3OutEquiv (e : Fin 3) (c0 c1 c2 : VcLane6_3) (scE scE1 : Sponge3Coins) :
    SimpleEquiv Sponge3Coins Sponge3Coins :=
  let s1 : VcState12_3 := fun i => mkState12Of6 (c0 i) lane6Zero
  seTrans sponge3CoinsTupleEquiv
    (seTrans
      (seDepProd (perm12OutEquiv e s1 scE.perm1 scE1.perm1) fun p1U =>
        let p1 := (honestRawPerm12_3 s1 (mkParty3At e scE.perm1 scE1.perm1 p1U)).2
        let s2 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))
        seDepProd (perm12OutEquiv e s2 scE.perm2 scE1.perm2) fun p2U =>
          let p2 := (honestRawPerm12_3 s2 (mkParty3At e scE.perm2 scE1.perm2 p2U)).2
          let s3 : VcState12_3 := fun i => mkState12Of6 (lane6Add (state12Rate6 (p2 i)) (c2 i)) (state12Cap6 (p2 i))
          perm12OutEquiv e s3 scE.perm3 scE1.perm3)
      (seSymm sponge3CoinsTupleEquiv))

private theorem simSponge3Perm_eq_honest (e : Fin 3) (c0 c1 c2 : VcLane6_3)
    (scE scE1 scU : Sponge3Coins) :
    let sc := mkParty3At e scE scE1 scU
    simSponge3Perm e (vcPairAtLane6 c0 e) (vcPairAtLane6 c1 e) (vcPairAtLane6 c2 e)
      scE scE1 ((sponge3OutEquiv e c0 c1 c2 scE scE1).toFun scU) =
      (((honestSponge3Perm3 c0 c1 c2 sc).1 e, (honestSponge3Perm3 c0 c1 c2 sc).1 (vcNextParty3 e)),
       vcPairAtLane6 (honestSponge3Perm3 c0 c1 c2 sc).2 e) := by
  have h1 : (fun i => (mkParty3At e scE scE1 scU i).perm1) = mkParty3At e scE.perm1 scE1.perm1 scU.perm1 := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have h2 : (fun i => (mkParty3At e scE scE1 scU i).perm2) = mkParty3At e scE.perm2 scE1.perm2 scU.perm2 := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have h3 : (fun i => (mkParty3At e scE scE1 scU i).perm3) = mkParty3At e scE.perm3 scE1.perm3 scU.perm3 := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  unfold simSponge3Perm sponge3OutEquiv honestSponge3Perm3 vcPairAtLane6
  dsimp only [seTrans, seDepProd, seSymm, sponge3CoinsTupleEquiv]
  rw [h1, h2, h3]
  have hs1 : (mkState12Of6 (c0 e) lane6Zero, mkState12Of6 (c0 (vcNextParty3 e)) lane6Zero) =
      vcPairAtState12 (fun i => mkState12Of6 (c0 i) lane6Zero) e := rfl
  rw [hs1, simRawPerm12_eq_honest]; dsimp only
  let p1 := (honestRawPerm12_3 (fun i => mkState12Of6 (c0 i) lane6Zero) (mkParty3At e scE.perm1 scE1.perm1 scU.perm1)).2
  have hs2 : (mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p1 e).1) (c1 e)) (state12Cap6 (vcPairAtState12 p1 e).1),
              mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p1 e).2) (c1 (vcNextParty3 e))) (state12Cap6 (vcPairAtState12 p1 e).2)) =
      vcPairAtState12 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i))) e := rfl
  rw [hs2, simRawPerm12_eq_honest]; dsimp only
  let p2 := (honestRawPerm12_3 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p1 i)) (c1 i)) (state12Cap6 (p1 i)))
    (mkParty3At e scE.perm2 scE1.perm2 scU.perm2)).2
  have hs3 : (mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p2 e).1) (c2 e)) (state12Cap6 (vcPairAtState12 p2 e).1),
              mkState12Of6 (lane6Add (state12Rate6 (vcPairAtState12 p2 e).2) (c2 (vcNextParty3 e))) (state12Cap6 (vcPairAtState12 p2 e).2)) =
      vcPairAtState12 (fun i => mkState12Of6 (lane6Add (state12Rate6 (p2 i)) (c2 i)) (state12Cap6 (p2 i))) e := rfl
  rw [hs3, simRawPerm12_eq_honest]
  rfl

private theorem extractSponge3Coins_sim (e : Fin 3) (c0 c1 c2 : Lane6 × Lane6)
    (scE scE1 osE1 : Sponge3Coins) :
    extractSponge3Coins (simSponge3Perm e c0 c1 c2 scE scE1 osE1).1.1 = some scE ∧
    extractSponge3Coins (simSponge3Perm e c0 c1 c2 scE scE1 osE1).1.2 = some scE1 := by
  rcases scE with ⟨a1, a2, a3⟩
  rcases scE1 with ⟨b1, b2, b3⟩
  unfold extractSponge3Coins simSponge3Perm
  dsimp only
  obtain ⟨e1, f1⟩ := extractPerm12Coins_sim e _ a1 b1 osE1.perm1
  obtain ⟨e2, f2⟩ := extractPerm12Coins_sim e _ a2 b2 osE1.perm2
  obtain ⟨e3, f3⟩ := extractPerm12Coins_sim e _ a3 b3 osE1.perm3
  rw [e1, e2, e3, f1, f2, f3]
  exact ⟨rfl, rfl⟩

private theorem pairCheckSponge3Perm_sim (e : Fin 3) (c0 c1 c2 : Lane6 × Lane6)
    (scE scE1 osE1 : Sponge3Coins) :
    pairCheckSponge3Perm e (simSponge3Perm e c0 c1 c2 scE scE1 osE1).1.1
      (simSponge3Perm e c0 c1 c2 scE scE1 osE1).1.2 c0 c1 c2 =
      some (simSponge3Perm e c0 c1 c2 scE scE1 osE1).2 := by
  unfold pairCheckSponge3Perm simSponge3Perm
  dsimp only
  rw [pairCheckRawPerm12_sim]; dsimp only
  rw [pairCheckRawPerm12_sim]; dsimp only
  rw [pairCheckRawPerm12_sim]

private def merkleLevelCoinsTupleEquiv :
    SimpleEquiv MerkleLevelCoins
      (Goldilocks × (Goldilocks × Goldilocks × Goldilocks × Goldilocks × Goldilocks × Goldilocks) × Sponge3Coins) where
  toFun m := (m.boolR, (m.sel0R, m.sel1R, m.sel2R, m.sel3R, m.sel4R, m.sel5R), m.hashCoins)
  invFun t := ⟨t.1, t.2.1.1, t.2.1.2.1, t.2.1.2.2.1, t.2.1.2.2.2.1, t.2.1.2.2.2.2.1, t.2.1.2.2.2.2.2, t.2.2⟩
  left_inv := fun ⟨_, _, _, _, _, _, _, _⟩ => rfl
  right_inv := fun ⟨_, ⟨_, _, _, _, _, _⟩, _⟩ => rfl

def simMerkleLevel (e : Fin 3) (epoch : UInt64) (layer : Nat)
    (cur : Lane6 × Lane6) (b : Goldilocks × Goldilocks) (sib : Lane6 × Lane6)
    (mcE mcE1 osE1 : MerkleLevelCoins) :
    (PartyMerkleLevelView × PartyMerkleLevelView) × (Lane6 × Lane6) × (Goldilocks × Goldilocks) :=
  let oneMinusB := pairSubGold (vcConstPair e Goldilocks.one) b
  let bg := simMulGate b oneMinusB mcE.boolR mcE1.boolR osE1.boolR
  let m0 := simMulGate b (pairSubGold (sib.1.x0, sib.2.x0) (cur.1.x0, cur.2.x0)) mcE.sel0R mcE1.sel0R osE1.sel0R
  let m1 := simMulGate b (pairSubGold (sib.1.x1, sib.2.x1) (cur.1.x1, cur.2.x1)) mcE.sel1R mcE1.sel1R osE1.sel1R
  let m2 := simMulGate b (pairSubGold (sib.1.x2, sib.2.x2) (cur.1.x2, cur.2.x2)) mcE.sel2R mcE1.sel2R osE1.sel2R
  let m3 := simMulGate b (pairSubGold (sib.1.x3, sib.2.x3) (cur.1.x3, cur.2.x3)) mcE.sel3R mcE1.sel3R osE1.sel3R
  let m4 := simMulGate b (pairSubGold (sib.1.x4, sib.2.x4) (cur.1.x4, cur.2.x4)) mcE.sel4R mcE1.sel4R osE1.sel4R
  let m5 := simMulGate b (pairSubGold (sib.1.x5, sib.2.x5) (cur.1.x5, cur.2.x5)) mcE.sel5R mcE1.sel5R osE1.sel5R
  let l0 := pairAddGold (cur.1.x0, cur.2.x0) m0.2; let l1 := pairAddGold (cur.1.x1, cur.2.x1) m1.2
  let l2 := pairAddGold (cur.1.x2, cur.2.x2) m2.2; let l3 := pairAddGold (cur.1.x3, cur.2.x3) m3.2
  let l4 := pairAddGold (cur.1.x4, cur.2.x4) m4.2; let l5 := pairAddGold (cur.1.x5, cur.2.x5) m5.2
  let r0 := pairSubGold (sib.1.x0, sib.2.x0) m0.2; let r1 := pairSubGold (sib.1.x1, sib.2.x1) m1.2
  let r2 := pairSubGold (sib.1.x2, sib.2.x2) m2.2; let r3 := pairSubGold (sib.1.x3, sib.2.x3) m3.2
  let r4 := pairSubGold (sib.1.x4, sib.2.x4) m4.2; let r5 := pairSubGold (sib.1.x5, sib.2.x5) m5.2
  let k0 := vcConstPair e (vcSchemaLo epoch)
  let k1 := vcConstPair e (Goldilocks.ofNat layer)
  let k2 := vcConstPair e (Goldilocks.ofNat vcMerkleNodeTag.toNat)
  let k3 := vcConstPair e (vcSchemaHiWithTag epoch poseidon2ConstIV)
  let k4 := vcConstPair e Goldilocks.one
  let c0P : Lane6 × Lane6 := (⟨l0.1, l1.1, l2.1, l3.1, l4.1, l5.1⟩, ⟨l0.2, l1.2, l2.2, l3.2, l4.2, l5.2⟩)
  let c1P : Lane6 × Lane6 := (⟨r0.1, r1.1, r2.1, r3.1, r4.1, r5.1⟩, ⟨r0.2, r1.2, r2.2, r3.2, r4.2, r5.2⟩)
  let c2P : Lane6 × Lane6 := (⟨k0.1, k1.1, k2.1, k3.1, k4.1, Goldilocks.zero⟩,
                              ⟨k0.2, k1.2, k2.2, k3.2, k4.2, Goldilocks.zero⟩)
  let sp := simSponge3Perm e c0P c1P c2P mcE.hashCoins mcE1.hashCoins osE1.hashCoins
  ((⟨b.1, sib.1, bg.1.1, m0.1.1, m1.1.1, m2.1.1, m3.1.1, m4.1.1, m5.1.1, sp.1.1⟩,
    ⟨b.2, sib.2, bg.1.2, m0.1.2, m1.1.2, m2.1.2, m3.1.2, m4.1.2, m5.1.2, sp.1.2⟩),
   sp.2, bg.2)

def merkleLevelOutEquiv (e : Fin 3) (epoch : UInt64) (layer : Nat)
    (cur : VcLane6_3) (b : VcWire3) (sib : VcLane6_3) (mcE mcE1 : MerkleLevelCoins) :
    SimpleEquiv MerkleLevelCoins MerkleLevelCoins :=
  let oneMinusB : VcWire3 := fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (b i)
  let d0 : VcWire3 := fun i => Goldilocks.sub (sib i).x0 (cur i).x0
  let d1 : VcWire3 := fun i => Goldilocks.sub (sib i).x1 (cur i).x1
  let d2 : VcWire3 := fun i => Goldilocks.sub (sib i).x2 (cur i).x2
  let d3 : VcWire3 := fun i => Goldilocks.sub (sib i).x3 (cur i).x3
  let d4 : VcWire3 := fun i => Goldilocks.sub (sib i).x4 (cur i).x4
  let d5 : VcWire3 := fun i => Goldilocks.sub (sib i).x5 (cur i).x5
  let selEq :=
    seProdCongr (mulGateOutEquiv e b d0 mcE1.sel0R)
    (seProdCongr (mulGateOutEquiv e b d1 mcE1.sel1R)
    (seProdCongr (mulGateOutEquiv e b d2 mcE1.sel2R)
    (seProdCongr (mulGateOutEquiv e b d3 mcE1.sel3R)
    (seProdCongr (mulGateOutEquiv e b d4 mcE1.sel4R)
                 (mulGateOutEquiv e b d5 mcE1.sel5R)))))
  seTrans merkleLevelCoinsTupleEquiv
    (seTrans
      (seProdCongr (mulGateOutEquiv e b oneMinusB mcE1.boolR)
        (seDepProd selEq fun ⟨u0, u1, u2, u3, u4, u5⟩ =>
          let del0 := vcMulGate3 b d0 (mkParty3At e mcE.sel0R mcE1.sel0R u0)
          let del1 := vcMulGate3 b d1 (mkParty3At e mcE.sel1R mcE1.sel1R u1)
          let del2 := vcMulGate3 b d2 (mkParty3At e mcE.sel2R mcE1.sel2R u2)
          let del3 := vcMulGate3 b d3 (mkParty3At e mcE.sel3R mcE1.sel3R u3)
          let del4 := vcMulGate3 b d4 (mkParty3At e mcE.sel4R mcE1.sel4R u4)
          let del5 := vcMulGate3 b d5 (mkParty3At e mcE.sel5R mcE1.sel5R u5)
          let c0 : VcLane6_3 := fun i =>
            ⟨Goldilocks.add (cur i).x0 (del0 i), Goldilocks.add (cur i).x1 (del1 i),
             Goldilocks.add (cur i).x2 (del2 i), Goldilocks.add (cur i).x3 (del3 i),
             Goldilocks.add (cur i).x4 (del4 i), Goldilocks.add (cur i).x5 (del5 i)⟩
          let c1 : VcLane6_3 := fun i =>
            ⟨Goldilocks.sub (sib i).x0 (del0 i), Goldilocks.sub (sib i).x1 (del1 i),
             Goldilocks.sub (sib i).x2 (del2 i), Goldilocks.sub (sib i).x3 (del3 i),
             Goldilocks.sub (sib i).x4 (del4 i), Goldilocks.sub (sib i).x5 (del5 i)⟩
          let c2 : VcLane6_3 := fun i =>
            ⟨vcConstWire3 (vcSchemaLo epoch) i, vcConstWire3 (Goldilocks.ofNat layer) i,
             vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
             vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
             vcConstWire3 Goldilocks.one i, Goldilocks.zero⟩
          sponge3OutEquiv e c0 c1 c2 mcE.hashCoins mcE1.hashCoins))
      (seSymm merkleLevelCoinsTupleEquiv))

private theorem simMerkleLevel_eq_honest (e : Fin 3) (epoch : UInt64) (layer : Nat)
    (cur : VcLane6_3) (b : VcWire3) (sib : VcLane6_3) (mcE mcE1 mcU : MerkleLevelCoins) :
    let mc := mkParty3At e mcE mcE1 mcU
    simMerkleLevel e epoch layer (vcPairAtLane6 cur e) (vcPairAt b e) (vcPairAtLane6 sib e)
      mcE mcE1 ((merkleLevelOutEquiv e epoch layer cur b sib mcE mcE1).toFun mcU) =
      (((honestMerkleLevel3 epoch layer cur b sib mc).1 e,
        (honestMerkleLevel3 epoch layer cur b sib mc).1 (vcNextParty3 e)),
       vcPairAtLane6 (honestMerkleLevel3 epoch layer cur b sib mc).2.1 e,
       vcPairAt (honestMerkleLevel3 epoch layer cur b sib mc).2.2 e) := by
  have hProj : ∀ f : MerkleLevelCoins → Goldilocks,
      (fun i => f (mkParty3At e mcE mcE1 mcU i)) = mkParty3At e (f mcE) (f mcE1) (f mcU) := by
    intro f; funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hHash : (fun i => (mkParty3At e mcE mcE1 mcU i).hashCoins) =
      mkParty3At e mcE.hashCoins mcE1.hashCoins mcU.hashCoins := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  unfold simMerkleLevel merkleLevelOutEquiv honestMerkleLevel3 vcPairAtLane6
  dsimp only [seTrans, seProdCongr, seDepProd, seSymm,
    merkleLevelCoinsTupleEquiv]
  rw [hProj (·.boolR), hProj (·.sel0R), hProj (·.sel1R), hProj (·.sel2R),
      hProj (·.sel3R), hProj (·.sel4R), hProj (·.sel5R), hHash]
  rw [vcConstPair_spec Goldilocks.one e,
      vcConstPair_spec (vcSchemaLo epoch) e,
      vcConstPair_spec (Goldilocks.ofNat layer) e,
      vcConstPair_spec (Goldilocks.ofNat vcMerkleNodeTag.toNat) e,
      vcConstPair_spec (vcSchemaHiWithTag epoch poseidon2ConstIV) e]
  have hOneSub : pairSubGold (vcPairAt (vcConstWire3 Goldilocks.one) e) (vcPairAt b e) =
      vcPairAt (fun i => Goldilocks.sub (vcConstWire3 Goldilocks.one i) (b i)) e := rfl
  have hd0 : pairSubGold ((sib e).x0, (sib (vcNextParty3 e)).x0) ((cur e).x0, (cur (vcNextParty3 e)).x0) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x0 (cur i).x0) e := rfl
  have hd1 : pairSubGold ((sib e).x1, (sib (vcNextParty3 e)).x1) ((cur e).x1, (cur (vcNextParty3 e)).x1) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x1 (cur i).x1) e := rfl
  have hd2 : pairSubGold ((sib e).x2, (sib (vcNextParty3 e)).x2) ((cur e).x2, (cur (vcNextParty3 e)).x2) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x2 (cur i).x2) e := rfl
  have hd3 : pairSubGold ((sib e).x3, (sib (vcNextParty3 e)).x3) ((cur e).x3, (cur (vcNextParty3 e)).x3) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x3 (cur i).x3) e := rfl
  have hd4 : pairSubGold ((sib e).x4, (sib (vcNextParty3 e)).x4) ((cur e).x4, (cur (vcNextParty3 e)).x4) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x4 (cur i).x4) e := rfl
  have hd5 : pairSubGold ((sib e).x5, (sib (vcNextParty3 e)).x5) ((cur e).x5, (cur (vcNextParty3 e)).x5) =
      vcPairAt (fun i => Goldilocks.sub (sib i).x5 (cur i).x5) e := rfl
  rw [hOneSub, hd0, hd1, hd2, hd3, hd4, hd5,
      simMulGate_eq_honest, simMulGate_eq_honest, simMulGate_eq_honest, simMulGate_eq_honest,
      simMulGate_eq_honest, simMulGate_eq_honest, simMulGate_eq_honest]
  dsimp only
  have hsp := simSponge3Perm_eq_honest e
    (fun i =>
      ⟨Goldilocks.add (cur i).x0 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x0 (cur k).x0) (mkParty3At e mcE.sel0R mcE1.sel0R mcU.sel0R) i),
       Goldilocks.add (cur i).x1 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x1 (cur k).x1) (mkParty3At e mcE.sel1R mcE1.sel1R mcU.sel1R) i),
       Goldilocks.add (cur i).x2 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x2 (cur k).x2) (mkParty3At e mcE.sel2R mcE1.sel2R mcU.sel2R) i),
       Goldilocks.add (cur i).x3 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x3 (cur k).x3) (mkParty3At e mcE.sel3R mcE1.sel3R mcU.sel3R) i),
       Goldilocks.add (cur i).x4 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x4 (cur k).x4) (mkParty3At e mcE.sel4R mcE1.sel4R mcU.sel4R) i),
       Goldilocks.add (cur i).x5 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x5 (cur k).x5) (mkParty3At e mcE.sel5R mcE1.sel5R mcU.sel5R) i)⟩)
    (fun i =>
      ⟨Goldilocks.sub (sib i).x0 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x0 (cur k).x0) (mkParty3At e mcE.sel0R mcE1.sel0R mcU.sel0R) i),
       Goldilocks.sub (sib i).x1 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x1 (cur k).x1) (mkParty3At e mcE.sel1R mcE1.sel1R mcU.sel1R) i),
       Goldilocks.sub (sib i).x2 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x2 (cur k).x2) (mkParty3At e mcE.sel2R mcE1.sel2R mcU.sel2R) i),
       Goldilocks.sub (sib i).x3 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x3 (cur k).x3) (mkParty3At e mcE.sel3R mcE1.sel3R mcU.sel3R) i),
       Goldilocks.sub (sib i).x4 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x4 (cur k).x4) (mkParty3At e mcE.sel4R mcE1.sel4R mcU.sel4R) i),
       Goldilocks.sub (sib i).x5 (vcMulGate3 b (fun k => Goldilocks.sub (sib k).x5 (cur k).x5) (mkParty3At e mcE.sel5R mcE1.sel5R mcU.sel5R) i)⟩)
    (fun i =>
      ⟨vcConstWire3 (vcSchemaLo epoch) i, vcConstWire3 (Goldilocks.ofNat layer) i,
       vcConstWire3 (Goldilocks.ofNat vcMerkleNodeTag.toNat) i,
       vcConstWire3 (vcSchemaHiWithTag epoch poseidon2ConstIV) i,
       vcConstWire3 Goldilocks.one i, Goldilocks.zero⟩)
    mcE.hashCoins mcE1.hashCoins mcU.hashCoins
  dsimp only [vcPairAtLane6, pairAddGold, pairSubGold, vcPairAt] at hsp ⊢
  rw [hsp]

private theorem extractMerkleLevelCoins_sim (e : Fin 3) (epoch : UInt64) (layer : Nat)
    (cur : Lane6 × Lane6) (b : Goldilocks × Goldilocks) (sib : Lane6 × Lane6)
    (mcE mcE1 osE1 : MerkleLevelCoins) :
    extractMerkleLevelCoins (simMerkleLevel e epoch layer cur b sib mcE mcE1 osE1).1.1 = some mcE ∧
    extractMerkleLevelCoins (simMerkleLevel e epoch layer cur b sib mcE mcE1 osE1).1.2 = some mcE1 := by
  rcases mcE with ⟨_, _, _, _, _, _, _, hcE⟩
  rcases mcE1 with ⟨_, _, _, _, _, _, _, hcE1⟩
  unfold extractMerkleLevelCoins simMerkleLevel
  dsimp only
  obtain ⟨h1, h2⟩ := extractSponge3Coins_sim e _ _ _ hcE hcE1 osE1.hashCoins
  rw [h1, h2]
  exact ⟨rfl, rfl⟩

private theorem pairCheckMerkleLevel_sim (e : Fin 3) (epoch : UInt64) (layer : Nat)
    (cur : Lane6 × Lane6) (b : Goldilocks × Goldilocks) (sib : Lane6 × Lane6)
    (mcE mcE1 osE1 : MerkleLevelCoins) :
    pairCheckMerkleLevel e epoch layer cur
      (simMerkleLevel e epoch layer cur b sib mcE mcE1 osE1).1.1
      (simMerkleLevel e epoch layer cur b sib mcE mcE1 osE1).1.2 =
      some (simMerkleLevel e epoch layer cur b sib mcE mcE1 osE1).2 := by
  unfold pairCheckMerkleLevel simMerkleLevel
  dsimp only
  rw [pairCheckMul_sim]; dsimp only
  rw [pairCheckMul_sim, pairCheckMul_sim, pairCheckMul_sim,
      pairCheckMul_sim, pairCheckMul_sim, pairCheckMul_sim]; dsimp only
  rw [pairCheckSponge3Perm_sim]

def simMerklePath (e : Fin 3) (epoch : UInt64) :
    {D : Nat} → Nat → (Lane6 × Lane6) →
    Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D →
    Vec MerkleLevelCoins D → Vec MerkleLevelCoins D → Vec MerkleLevelCoins D →
    (List PartyMerkleLevelView × List PartyMerkleLevelView) × (Lane6 × Lane6) × List (Goldilocks × Goldilocks)
  | 0, _, cur, .nil, .nil, .nil, .nil => (([], []), cur, [])
  | _ + 1, layer, cur, .cons (bp, sp) restIn, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 =>
    let hd := simMerkleLevel e epoch layer cur bp sp cE cE1 oE1
    let tl := simMerklePath e epoch (layer + 1) hd.2.1 restIn csE csE1 osE1
    ((hd.1.1 :: tl.1.1, hd.1.2 :: tl.1.2), tl.2.1, hd.2.2 :: tl.2.2)

def merklePathOutEquiv (e : Fin 3) (epoch : UInt64) :
    {D : Nat} → Nat → VcLane6_3 → Vec (VcWire3 × VcLane6_3) D →
    Vec MerkleLevelCoins D → Vec MerkleLevelCoins D →
    SimpleEquiv (Vec MerkleLevelCoins D) (Vec MerkleLevelCoins D)
  | 0, _, _, .nil, .nil, .nil => seRefl _
  | _ + 1, layer, cur, .cons (b, sib) rest, .cons cE csE, .cons cE1 csE1 =>
    seDepCons (merkleLevelOutEquiv e epoch layer cur b sib cE cE1) fun cU =>
      let nextCur := (honestMerkleLevel3 epoch layer cur b sib (mkParty3At e cE cE1 cU)).2.1
      merklePathOutEquiv e epoch (layer + 1) nextCur rest csE csE1

private theorem simMerklePath_eq_honest (e : Fin 3) (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : VcLane6_3)
      (witSteps : Vec (Bool × Lane6) D)
      (stepCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D)
      (csE csE1 csU : Vec MerkleLevelCoins D),
      let steps3 := vcShareMerkleSteps3 witSteps stepCoins
      let cs := mkParty3At e csE csE1 csU
      simMerklePath e epoch layer (vcPairAtLane6 cur e)
        ((vcMerkleStepsEquiv3 e witSteps).toFun stepCoins) csE csE1
        ((merklePathOutEquiv e epoch layer cur steps3 csE csE1).toFun csU) =
        (((honestMerklePath3 epoch layer cur steps3 cs).1 e,
          (honestMerklePath3 epoch layer cur steps3 cs).1 (vcNextParty3 e)),
         vcPairAtLane6 (honestMerklePath3 epoch layer cur steps3 cs).2.1 e,
         (honestMerklePath3 epoch layer cur steps3 cs).2.2.map (fun w => vcPairAt w e))
  | 0, _, _, .nil, .nil, .nil, .nil, .nil => rfl
  | _ + 1, layer, cur, .cons (b, sib) restW, .cons (bc, sc) restC, .cons cE csE, .cons cE1 csE1, .cons cU csU => by
    simp only [vcShareMerkleSteps3, vcMerkleStepsEquiv3, merklePathOutEquiv,
      seDepCons, seDepConsToFun, seProdCongr, simMerklePath, honestMerklePath3, List.map]
    have hHead : (fun i => (mkParty3At e (Vec.cons cE csE) (Vec.cons cE1 csE1) (Vec.cons cU csU) i).head) =
        mkParty3At e cE cE1 cU := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hTail : (fun i => (mkParty3At e (Vec.cons cE csE) (Vec.cons cE1 csE1) (Vec.cons cU csU) i).tail) =
        mkParty3At e csE csE1 csU := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    rw [hHead, hTail]
    have hbEq : (vcOpenedShareEquiv3 e (if b = true then Goldilocks.one else Goldilocks.zero)).1 bc =
        vcPairAt (vcShareWire3 (if b = true then Goldilocks.one else Goldilocks.zero) bc) e := rfl
    have hsEq : (vcLane6OpenedShareEquiv3 e sib).1 sc = vcPairAtLane6 (vcShareLane6_3 sib sc) e := rfl
    simp only [hbEq, hsEq, simMerkleLevel_eq_honest]
    rw [simMerklePath_eq_honest e epoch (layer + 1) _ restW restC csE csE1 csU]

private theorem simMerklePath_length (e : Fin 3) (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : Lane6 × Lane6)
      (inSteps : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D)
      (csE csE1 osE1 : Vec MerkleLevelCoins D),
      (simMerklePath e epoch layer cur inSteps csE csE1 osE1).1.1.length = D ∧
      (simMerklePath e epoch layer cur inSteps csE csE1 osE1).1.2.length = D
  | 0, _, _, .nil, .nil, .nil, .nil => ⟨rfl, rfl⟩
  | _ + 1, layer, cur, .cons (bp, sp) restIn, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 => by
    obtain ⟨h1, h2⟩ := simMerklePath_length e epoch (layer + 1)
      (simMerkleLevel e epoch layer cur bp sp cE cE1 oE1).2.1 restIn csE csE1 osE1
    simp only [simMerklePath, List.length_cons]
    exact ⟨by omega, by omega⟩

private theorem extractMerklePathCoins_sim (e : Fin 3) (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : Lane6 × Lane6)
      (inSteps : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D)
      (csE csE1 osE1 : Vec MerkleLevelCoins D),
      extractMerklePathCoins D (simMerklePath e epoch layer cur inSteps csE csE1 osE1).1.1 = some csE ∧
      extractMerklePathCoins D (simMerklePath e epoch layer cur inSteps csE csE1 osE1).1.2 = some csE1
  | 0, _, _, .nil, .nil, .nil, .nil => ⟨rfl, rfl⟩
  | _ + 1, layer, cur, .cons (bp, sp) restIn, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 => by
    simp only [simMerklePath, extractMerklePathCoins]
    obtain ⟨h1, h2⟩ := extractMerkleLevelCoins_sim e epoch layer cur bp sp cE cE1 oE1
    obtain ⟨ih1, ih2⟩ := extractMerklePathCoins_sim e epoch (layer + 1) _ restIn csE csE1 osE1
    rw [h1, h2, ih1, ih2]
    exact ⟨rfl, rfl⟩

private theorem pairCheckMerklePath_sim (e : Fin 3) (epoch : UInt64) :
    ∀ {D : Nat} (layer : Nat) (cur : Lane6 × Lane6)
      (inSteps : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D)
      (csE csE1 osE1 : Vec MerkleLevelCoins D),
      pairCheckMerklePath e epoch layer cur
        (simMerklePath e epoch layer cur inSteps csE csE1 osE1).1.1
        (simMerklePath e epoch layer cur inSteps csE csE1 osE1).1.2 =
        some (simMerklePath e epoch layer cur inSteps csE csE1 osE1).2
  | 0, _, _, .nil, .nil, .nil, .nil => rfl
  | _ + 1, layer, cur, .cons (bp, sp) restIn, .cons cE csE, .cons cE1 csE1, .cons oE1 osE1 => by
    simp only [simMerklePath, pairCheckMerklePath]
    rw [pairCheckMerkleLevel_sim]; dsimp only
    rw [pairCheckMerklePath_sim e epoch (layer + 1) _ restIn csE csE1 osE1]

/-! #### Public Statement, Secret Witness, Full `OpenedBlindVcRep` Simulator & `zkMultiRepViewEquiv` -/

/-- Public statement for `BlindVC` selective disclosure. -/
structure BlindVcPublicStatement where
  schema : VcSchema
  treeDepth : Nat
  presNonce : Vec UInt8 32
  issuerEpoch : UInt64
  accumulatorRoot : Lane6
  presCommit : Lane6
  scopeTag : Lane6
  verifierScopeLimbs : Lane4
  disclosedAttrs : List (Nat × Goldilocks)

/-- Holder's secret credential + boolean Merkle accumulator witness. -/
structure BlindVcSecretWitness (arity treeDepth : Nat) where
  attrs : Vec Goldilocks arity
  holderBlind : Lane4
  presBlind : Lane4
  merkleSteps : Vec (Bool × Lane6) treeDepth

/-- Validity relation connecting `BlindVcSecretWitness` to `BlindVcPublicStatement`. -/
def BlindVcWitnessValid (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth) : Prop :=
  vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true ∧
  (∀ p ∈ stmt.disclosedAttrs, wit.attrs.toList[p.1]? = some p.2) ∧
  (∃ leaf : Lane6,
    computeVcPoseidon2Commit stmt.schema wit.attrs.toList wit.holderBlind vcAttrCommitTag = some leaf ∧
    evalVcMerklePathBool stmt.issuerEpoch 0 leaf wit.merkleSteps.toList = stmt.accumulatorRoot) ∧
  computeVcPoseidon2Commit stmt.schema wit.attrs.toList wit.presBlind vcPresCommitTag = some stmt.presCommit ∧
  computeVcScopeTag stmt.schema.schemaId wit.holderBlind stmt.verifierScopeLimbs = stmt.scopeTag

/-- Per-repetition randomness space shared by Hybrid-1 honest execution and the zero-knowledge simulator. -/
structure RepRandomness (arity treeDepth : Nat) where
  seedE : Vec UInt8 32
  seedE1 : Vec UInt8 32
  saltE : Vec UInt8 32
  saltE1 : Vec UInt8 32
  attrShareCoins : Vec (Goldilocks × Goldilocks) arity
  holderBlindCoins : Lane4 × Lane4
  presBlindCoins : Lane4 × Lane4
  merkleStepCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) treeDepth
  gateCoins : PartyGateCoins treeDepth
  unopenedCommitCoins : Vec UInt8 32

private def partyGateCoinsTupleEquiv {D : Nat} :
    SimpleEquiv (PartyGateCoins D)
      (Sponge3Coins × Sponge3Coins × Sponge3Coins × Vec MerkleLevelCoins D) where
  toFun g := (g.attrCoins, g.presCoins, g.scopeCoins, g.merkleCoins)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _⟩ => rfl

/-- Constructive 3-share output completion from public `target` and opened `(sE, sE1)`. -/
def completeLane6Shares3 (e : Fin 3) (target : Lane6) (pair : Lane6 × Lane6) : Triple3 Lane6 :=
  Triple3.ofFn (mkParty3At e pair.1 pair.2 (lane6Sub (lane6Sub target pair.1) pair.2))

def completeZeroShares3 (e : Fin 3) (pairs : List (Goldilocks × Goldilocks)) : List (Triple3 Goldilocks) :=
  pairs.map (fun p => Triple3.ofFn (mkParty3At e p.1 p.2 (Goldilocks.sub (Goldilocks.sub Goldilocks.zero p.1) p.2)))

/-- **Zero-Knowledge Simulator (`simulateOpenedBlindVcRep`, fixing `C0-3`)**:
    Takes **ONLY** the public statement `stmt`, repetition index `repIdx`, challenge `e`, and
    uniform `simRand : RepRandomness` (**ZERO** secret witness arguments!), expands real PRG tapes
    from `(seedE, seedE1)`, and produces a complete `OpenedBlindVcRep` (`viewE`, `viewE1`,
    `unopenedCommit`, `finalOuts`). -/
def simulateOpenedBlindVcRep
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement) (repIdx : Nat) (e : Fin 3)
    (simRand : RepRandomness stmt.schema.arity stmt.treeDepth) : OpenedBlindVcRep :=
  let e1 := vcNextParty3 e
  let gE := prgExpand stmt.treeDepth repIdx e simRand.seedE
  let gE1 := prgExpand stmt.treeDepth repIdx e1 simRand.seedE1
  let (attrsE, attrsE1) := simAttrPairs e stmt.disclosedAttrs 0 simRand.attrShareCoins
  let (hbE, hbE1) := simRand.holderBlindCoins
  let (pbE, pbE1) := simRand.presBlindCoins
  let (ac0, ac1, ac2) := vcPairCommitChunks e stmt.schema attrsE attrsE1 hbE hbE1 vcAttrCommitTag
  let (pc0, pc1, pc2) := vcPairCommitChunks e stmt.schema attrsE attrsE1 pbE pbE1 vcPresCommitTag
  let (sc0, sc1, sc2) := vcPairScopeChunks e stmt.schema.schemaId hbE hbE1 stmt.verifierScopeLimbs
  let attrSim := simSponge3Perm e ac0 ac1 ac2 gE.attrCoins gE1.attrCoins simRand.gateCoins.attrCoins
  let presSim := simSponge3Perm e pc0 pc1 pc2 gE.presCoins gE1.presCoins simRand.gateCoins.presCoins
  let scopeSim := simSponge3Perm e sc0 sc1 sc2 gE.scopeCoins gE1.scopeCoins simRand.gateCoins.scopeCoins
  let mkSim := simMerklePath e stmt.issuerEpoch 0 attrSim.2 simRand.merkleStepCoins
    gE.merkleCoins gE1.merkleCoins simRand.gateCoins.merkleCoins
  let viewE : PartyVcRepView :=
    { tapeSeed := simRand.seedE
      commitSalt := simRand.saltE
      attrShares := attrsE
      holderBlindShare := hbE
      presBlindShare := pbE
      attrSponge := attrSim.1.1
      merkleLevels := mkSim.1.1
      presSponge := presSim.1.1
      scopeSponge := scopeSim.1.1 }
  let viewE1 : PartyVcRepView :=
    { tapeSeed := simRand.seedE1
      commitSalt := simRand.saltE1
      attrShares := attrsE1
      holderBlindShare := hbE1
      presBlindShare := pbE1
      attrSponge := attrSim.1.2
      merkleLevels := mkSim.1.2
      presSponge := presSim.1.2
      scopeSponge := scopeSim.1.2 }
  let finalOuts : VcRepFinalOuts3 :=
    { rootShares := completeLane6Shares3 e stmt.accumulatorRoot mkSim.2.1
      presShares := completeLane6Shares3 e stmt.presCommit presSim.2
      scopeShares := completeLane6Shares3 e stmt.scopeTag scopeSim.2
      boolZeroShares := completeZeroShares3 e mkSim.2.2 }
  { e := e
    viewE := viewE
    viewE1 := viewE1
    unopenedCommit := simRand.unopenedCommitCoins.toList
    finalOuts := finalOuts }

/-- Build a full 3-party `BlindVcRepTriple` from 3 party coin tapes `(g 0, g 1, g 2)`. -/
def buildHonestBlindVcTriple
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth)
    (gateCoins3 : Fin 3 → PartyGateCoins stmt.treeDepth) : BlindVcRepTriple :=
  let attrShares := vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins
  let hbShares := vcShareLane4_3 wit.holderBlind hbCoins
  let pbShares := vcShareLane4_3 wit.presBlind pbCoins
  let mkSteps3 := vcShareMerkleSteps3 wit.merkleSteps mkCoins
  let (ac0, ac1, ac2) := vcCommitChunks3 stmt.schema attrShares hbShares vcAttrCommitTag
  let (pc0, pc1, pc2) := vcCommitChunks3 stmt.schema attrShares pbShares vcPresCommitTag
  let (sc0, sc1, sc2) := vcScopeChunks3 stmt.schema.schemaId hbShares stmt.verifierScopeLimbs
  let attrRun := honestSponge3Perm3 ac0 ac1 ac2 (fun i => (gateCoins3 i).attrCoins)
  let presRun := honestSponge3Perm3 pc0 pc1 pc2 (fun i => (gateCoins3 i).presCoins)
  let scopeRun := honestSponge3Perm3 sc0 sc1 sc2 (fun i => (gateCoins3 i).scopeCoins)
  let mkRun := honestMerklePath3 stmt.issuerEpoch 0 attrRun.2 mkSteps3 (fun i => (gateCoins3 i).merkleCoins)
  { views := fun i =>
      { tapeSeed := seeds i
        commitSalt := salts i
        attrShares := attrShares i
        holderBlindShare := hbShares i
        presBlindShare := pbShares i
        attrSponge := attrRun.1 i
        merkleLevels := mkRun.1 i
        presSponge := presRun.1 i
        scopeSponge := scopeRun.1 i }
    finalOuts :=
      { rootShares := Triple3.ofFn mkRun.2.1
        presShares := Triple3.ofFn presRun.2
        scopeShares := Triple3.ofFn scopeRun.2
        boolZeroShares := mkRun.2.2.map Triple3.ofFn } }

/-- Hybrid-1 honest repetition opening (`[GMO16, Lemma 4.2]`):
    opened parties `e` and `(e+1)%3` expand real PRG tapes `prgExpand ... seedE` and `prgExpand ... seedE1`
    and real salted commitments, while the unopened 3rd party `(e+2)%3` uses uniform gate coins
    `hRand.gateCoins` and XOR-masked commitment `hRand.unopenedCommitCoins`. -/
def honestHybrid1Rep
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (repIdx : Nat) (e : Fin 3)
    (hRand : RepRandomness stmt.schema.arity stmt.treeDepth) : OpenedBlindVcRep :=
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  let gE := prgExpand stmt.treeDepth repIdx e hRand.seedE
  let gE1 := prgExpand stmt.treeDepth repIdx e1 hRand.seedE1
  let seeds := mkParty3At e hRand.seedE hRand.seedE1 (Vec.replicate 32 0)
  let salts := mkParty3At e hRand.saltE hRand.saltE1 (Vec.replicate 32 0)
  let gateCoins3 := mkParty3At e gE gE1 hRand.gateCoins
  let triple := buildHonestBlindVcTriple stmt wit seeds salts
    hRand.attrShareCoins hRand.holderBlindCoins hRand.presBlindCoins hRand.merkleStepCoins gateCoins3
  let rawComU := vcCommitPartyView H stmt.presNonce repIdx e2 (triple.views e2)
    (vcPartyFinalOutAt triple.finalOuts e2)
  { e := e
    viewE := triple.views e
    viewE1 := triple.views e1
    unopenedCommit := (xorBytesWithVec rawComU hRand.unopenedCommitCoins).toList
    finalOuts := triple.finalOuts }

/-- Real-world PRG prover triple (`Hybrid 0`) from 3 `(tapeSeed, commitSalt)` pairs:
    opening `honestPrgTriple` at `e` is literally `honestHybrid1Rep` at
    `gateCoins := prgExpand ... seedU` and `unopenedCommitCoins := Vec.replicate 32 0`! -/
def honestPrgTriple
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (repIdx : Nat)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth) :
    BlindVcRepTriple :=
  buildHonestBlindVcTriple stmt wit seeds salts attrCoins hbCoins pbCoins mkCoins
    (fun i => prgExpand stmt.treeDepth repIdx i (seeds i))

private theorem vcMerkleStepSum_bool :
    ∀ {D : Nat} (epoch : UInt64) (layer : Nat) (cur : VcLane6_3)
      (witSteps : Vec (Bool × Lane6) D)
      (stepCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D)
      (mcs : Fin 3 → Vec MerkleLevelCoins D),
      let run := honestMerklePath3 epoch layer cur (vcShareMerkleSteps3 witSteps stepCoins) mcs
      vcSumLane6_3 run.2.1 = evalVcMerklePathBool epoch layer (vcSumLane6_3 cur) witSteps.toList ∧
      ∀ z ∈ run.2.2, vcSum3 z = Goldilocks.zero
  | 0, _, _, _, .nil, .nil, _ => ⟨rfl, fun _ hz => nomatch hz⟩
  | _ + 1, epoch, layer, cur, .cons (b, sib) restW, .cons (bc, sc) restC, mcs => by
    simp only [vcShareMerkleSteps3, honestMerklePath3, Vec.toList]
    let bGold := if b = true then Goldilocks.one else Goldilocks.zero
    let bw := vcShareWire3 bGold bc
    let sw := vcShareLane6_3 sib sc
    have h0 := pairCheckMerkleLevel_honest epoch layer cur bw sw (fun i => (mcs i).head) 0
    have h1 := pairCheckMerkleLevel_honest epoch layer cur bw sw (fun i => (mcs i).head) 1
    have h2 := pairCheckMerkleLevel_honest epoch layer cur bw sw (fun i => (mcs i).head) 2
    obtain ⟨nextCur, bz, ep0, ep1, _, hBzSum, hNextSum⟩ := pairCheckMerkleLevel_extract3 h0 h1 h2
    have hNextEq : (honestMerkleLevel3 epoch layer cur bw sw (fun i => (mcs i).head)).2.1 = nextCur := by
      have e0 := congrArg Prod.fst ep0; have e1 := congrArg Prod.fst ep1
      exact funext (fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1))
    have hBzEq : (honestMerkleLevel3 epoch layer cur bw sw (fun i => (mcs i).head)).2.2 = bz := by
      have e0 := congrArg Prod.snd ep0; have e1 := congrArg Prod.snd ep1
      exact funext (fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1))
    have hLvBit : (fun i => ((honestMerkleLevel3 epoch layer cur bw sw (fun i => (mcs i).head)).1 i).bitShare) = bw := rfl
    have hLvSib : (fun i => ((honestMerkleLevel3 epoch layer cur bw sw (fun i => (mcs i).head)).1 i).sibShare) = sw := rfl
    have hbSum : vcSum3 bw = bGold := vcSum3_shareWire3 bGold bc
    have hsSum : vcSumLane6_3 sw = sib := vcSumLane6_3_share sib sc
    obtain ⟨ihRoot, ihZeros⟩ := vcMerkleStepSum_bool epoch (layer + 1)
      (honestMerkleLevel3 epoch layer cur bw sw (fun i => (mcs i).head)).2.1 restW restC (fun i => (mcs i).tail)
    refine ⟨?_, ?_⟩
    · rw [ihRoot, hNextEq, hNextSum, hLvBit, hLvSib, hbSum, hsSum]
      cases b with
      | false =>
        have hbG : bGold = Goldilocks.zero := rfl
        rw [hbG, vcMerkleStepArith_zero]
        simp only [evalVcMerklePathBool]
      | true =>
        have hbG : bGold = Goldilocks.one := rfl
        rw [hbG, vcMerkleStepArith_one]
        simp only [evalVcMerklePathBool]
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hzTail
      · rw [hBzEq, hBzSum, hLvBit, hbSum]
        cases b with
        | false =>
          have hbG : bGold = Goldilocks.zero := rfl
          rw [hbG, ← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat Goldilocks.one]
          simp only [Goldilocks.zero_val, goldOfInt_sub, goldOfInt_mul]; congr 1
        | true =>
          have hbG : bGold = Goldilocks.one := rfl
          rw [hbG, ← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat Goldilocks.one]
          simp only [Goldilocks.zero_val, Goldilocks.one_val, goldOfInt_sub, goldOfInt_mul]; congr 1
      · exact ihZeros z hzTail

private theorem buildHonestBlindVcTriple_sums
    {stmt : BlindVcPublicStatement}
    {wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth}
    (hValid : BlindVcWitnessValid stmt wit)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth)
    (gateCoins3 : Fin 3 → PartyGateCoins stmt.treeDepth) :
    let tr := buildHonestBlindVcTriple stmt wit seeds salts attrCoins hbCoins pbCoins mkCoins gateCoins3
    vcSumLane6_3 tr.finalOuts.rootShares.get = stmt.accumulatorRoot ∧
    vcSumLane6_3 tr.finalOuts.presShares.get = stmt.presCommit ∧
    vcSumLane6_3 tr.finalOuts.scopeShares.get = stmt.scopeTag ∧
    (∀ t ∈ tr.finalOuts.boolZeroShares, vcSum3 t.get = Goldilocks.zero) := by
  rcases hValid with ⟨_, _, ⟨leaf, hAttrCom, hMkEval⟩, hPresCom, hScopeEval⟩
  unfold buildHonestBlindVcTriple
  dsimp only
  have hGetFn : ∀ {α : Type} (f : Fin 3 → α), (Triple3.ofFn f).get = f :=
    fun f => funext (Triple3.get_ofFn f)
  rw [hGetFn, hGetFn, hGetFn]
  have hAttrsLen : wit.attrs.toList.length = stmt.schema.arity := Vec.toList_length wit.attrs
  unfold computeVcPoseidon2Commit at hAttrCom hPresCom
  rw [ite_true_of hAttrsLen] at hAttrCom hPresCom
  injection hAttrCom with hLeafEq
  injection hPresCom with hPresEq
  have hChunksEq : ∀ (blind : Lane4) (bCoins : Lane4 × Lane4) (tag : UInt64),
      let (c0, c1, c2) := vcCommitChunks3 stmt.schema
        (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins)
        (vcShareLane4_3 blind bCoins) tag
      (vcSumLane6_3 c0, vcSumLane6_3 c1, vcSumLane6_3 c2) =
        vcCommitChunks stmt.schema wit.attrs.toList blind tag := by
    intro blind bCoins tag
    unfold vcCommitChunks3 vcCommitChunks vcShareLane4_3
    dsimp only
    simp only [vcSumLane6_3_eq, vcSum3_constWire, vcSum3_zero,
      vcShareAttrs3_sum_getElem?, vcSum3_shareWire3]
  have hAC := hChunksEq wit.holderBlind hbCoins vcAttrCommitTag
  dsimp only at hAC
  injection hAC with hac0 hacRest; injection hacRest with hac1 hac2
  have hPC := hChunksEq wit.presBlind pbCoins vcPresCommitTag
  dsimp only at hPC
  injection hPC with hpc0 hpcRest; injection hpcRest with hpc1 hpc2
  have hSC :
      let (c0, c1, c2) := vcScopeChunks3 stmt.schema.schemaId
        (vcShareLane4_3 wit.holderBlind hbCoins) stmt.verifierScopeLimbs
      (vcSumLane6_3 c0, vcSumLane6_3 c1, vcSumLane6_3 c2) =
        vcScopeChunks stmt.schema.schemaId wit.holderBlind stmt.verifierScopeLimbs := by
    unfold vcScopeChunks3 vcScopeChunks vcShareLane4_3
    dsimp only
    simp only [vcSumLane6_3_eq, vcSum3_constWire, vcSum3_zero, vcSum3_shareWire3]
  dsimp only at hSC
  injection hSC with hsc0 hscRest; injection hscRest with hsc1 hsc2
  let ac := vcCommitChunks3 stmt.schema
    (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins)
    (vcShareLane4_3 wit.holderBlind hbCoins) vcAttrCommitTag
  let pc := vcCommitChunks3 stmt.schema
    (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins)
    (vcShareLane4_3 wit.presBlind pbCoins) vcPresCommitTag
  let sc := vcScopeChunks3 stmt.schema.schemaId
    (vcShareLane4_3 wit.holderBlind hbCoins) stmt.verifierScopeLimbs
  have hAttrSum : vcSumLane6_3 (honestSponge3Perm3 ac.1 ac.2.1 ac.2.2 (fun i => (gateCoins3 i).attrCoins)).2 = leaf := by
    rw [honestSponge3Perm3_sum, hac0, hac1, hac2]; exact hLeafEq
  have hPresSum : vcSumLane6_3 (honestSponge3Perm3 pc.1 pc.2.1 pc.2.2 (fun i => (gateCoins3 i).presCoins)).2 = stmt.presCommit := by
    rw [honestSponge3Perm3_sum, hpc0, hpc1, hpc2]; exact hPresEq
  have hScopeSum : vcSumLane6_3 (honestSponge3Perm3 sc.1 sc.2.1 sc.2.2 (fun i => (gateCoins3 i).scopeCoins)).2 = stmt.scopeTag := by
    rw [honestSponge3Perm3_sum, hsc0, hsc1, hsc2]; exact hScopeEval
  obtain ⟨hMkRoot, hMkZeros⟩ := vcMerkleStepSum_bool stmt.issuerEpoch 0
    (honestSponge3Perm3 ac.1 ac.2.1 ac.2.2 (fun i => (gateCoins3 i).attrCoins)).2
    wit.merkleSteps mkCoins (fun i => (gateCoins3 i).merkleCoins)
  rw [hAttrSum, hMkEval] at hMkRoot
  refine ⟨hMkRoot, hPresSum, hScopeSum, ?_⟩
  intro t ht
  obtain ⟨z, hzMem, rfl⟩ := List.mem_map.mp ht
  rw [hGetFn]
  exact hMkZeros z hzMem

/-- Bijection on `PartyGateCoins` mapping unopened party coins `gU` to simulated `gateOutsE1`. -/
def partyGateOutEquiv (e : Fin 3) (stmt : BlindVcPublicStatement)
    (attrShares : Fin 3 → List Goldilocks)
    (hbShares pbShares : VcLane4_3)
    (mkSteps3 : Vec (VcWire3 × VcLane6_3) stmt.treeDepth)
    (gE gE1 : PartyGateCoins stmt.treeDepth) :
    SimpleEquiv (PartyGateCoins stmt.treeDepth) (PartyGateCoins stmt.treeDepth) :=
  let (ac0, ac1, ac2) := vcCommitChunks3 stmt.schema attrShares hbShares vcAttrCommitTag
  let (pc0, pc1, pc2) := vcCommitChunks3 stmt.schema attrShares pbShares vcPresCommitTag
  let (sc0, sc1, sc2) := vcScopeChunks3 stmt.schema.schemaId hbShares stmt.verifierScopeLimbs
  seTrans partyGateCoinsTupleEquiv
    (seTrans
      (seDepProd (sponge3OutEquiv e ac0 ac1 ac2 gE.attrCoins gE1.attrCoins) fun acU =>
        let leaf3 := (honestSponge3Perm3 ac0 ac1 ac2 (mkParty3At e gE.attrCoins gE1.attrCoins acU)).2
        seProdCongr (sponge3OutEquiv e pc0 pc1 pc2 gE.presCoins gE1.presCoins)
          (seProdCongr (sponge3OutEquiv e sc0 sc1 sc2 gE.scopeCoins gE1.scopeCoins)
            (merklePathOutEquiv e stmt.issuerEpoch 0 leaf3 mkSteps3 gE.merkleCoins gE1.merkleCoins)))
      (seSymm partyGateCoinsTupleEquiv))

private def repRandomnessTupleEquiv {A D : Nat} :
    SimpleEquiv (RepRandomness A D)
      ((Vec UInt8 32 × Vec UInt8 32 × Vec UInt8 32 × Vec UInt8 32) ×
       ((Vec (Goldilocks × Goldilocks) A × (Lane4 × Lane4) × (Lane4 × Lane4) ×
         Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D) ×
        (PartyGateCoins D × Vec UInt8 32))) where
  toFun r := ((r.seedE, r.seedE1, r.saltE, r.saltE1),
              ((r.attrShareCoins, r.holderBlindCoins, r.presBlindCoins, r.merkleStepCoins),
               (r.gateCoins, r.unopenedCommitCoins)))
  invFun t := ⟨t.1.1, t.1.2.1, t.1.2.2.1, t.1.2.2.2,
               t.2.1.1, t.2.1.2.1, t.2.1.2.2.1, t.2.1.2.2.2,
               t.2.2.1, t.2.2.2⟩
  left_inv := fun ⟨_, _, _, _, _, _, _, _, _, _⟩ => rfl
  right_inv := fun ⟨⟨_, _, _, _⟩, ⟨⟨_, _, _, _⟩, ⟨_, _⟩⟩⟩ => rfl

/-- **Full-Repetition Zero-Knowledge Bijection (`zkOpenedRepFullEquiv`, `0 Classical.choice`, fixing `C0-3`)**:
    Maps the prover's Hybrid-1 randomness space bijectively onto the simulator's randomness space
    such that `honestHybrid1Rep` and `simulateOpenedBlindVcRep` output the **EXACT SAME**
    `OpenedBlindVcRep` (`viewE`, `viewE1`, `unopenedCommit`, AND `finalOuts`)! -/
def zkOpenedRepFullEquiv
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (repIdx : Nat) (e : Fin 3) :
    SimpleEquiv (RepRandomness stmt.schema.arity stmt.treeDepth)
                (RepRandomness stmt.schema.arity stmt.treeDepth) :=
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  let inEq :=
    seProdCongr (vcAttrSharesEquiv3 e stmt.disclosedAttrs 0 wit.attrs)
      (seProdCongr (vcLane4OpenedShareEquiv3 e wit.holderBlind)
        (seProdCongr (vcLane4OpenedShareEquiv3 e wit.presBlind)
          (vcMerkleStepsEquiv3 e wit.merkleSteps)))
  seTrans repRandomnessTupleEquiv
    (seTrans
      (seDepProd (seRefl _) fun ⟨seedE, seedE1, saltE, saltE1⟩ =>
        let gE := prgExpand stmt.treeDepth repIdx e seedE
        let gE1 := prgExpand stmt.treeDepth repIdx e1 seedE1
        seDepProd inEq fun ⟨attrCoins, hbCoins, pbCoins, mkCoins⟩ =>
          let attrShares := vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins
          let hbShares := vcShareLane4_3 wit.holderBlind hbCoins
          let pbShares := vcShareLane4_3 wit.presBlind pbCoins
          let mkSteps3 := vcShareMerkleSteps3 wit.merkleSteps mkCoins
          seDepProd (partyGateOutEquiv e stmt attrShares hbShares pbShares mkSteps3 gE gE1) fun gateU =>
            let seeds := mkParty3At e seedE seedE1 (Vec.replicate 32 0)
            let salts := mkParty3At e saltE saltE1 (Vec.replicate 32 0)
            let gateCoins3 := mkParty3At e gE gE1 gateU
            let triple := buildHonestBlindVcTriple stmt wit seeds salts attrCoins hbCoins pbCoins mkCoins gateCoins3
            let rawComU := vcCommitPartyView H stmt.presNonce repIdx e2 (triple.views e2)
              (vcPartyFinalOutAt triple.finalOuts e2)
            xorBytesWithVecEquiv rawComU)
      (seSymm repRandomnessTupleEquiv))

/-- **Exact Full-View Simulation Theorem (`zkOpenedRepFullEquiv_simulates`, fixing `C0-3`)**:
    For every valid secret witness `wit` and every randomness draw `hRand`,
    `honestHybrid1Rep` equals `simulateOpenedBlindVcRep` across ALL fields of `OpenedBlindVcRep`! -/
theorem zkOpenedRepFullEquiv_simulates
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (repIdx : Nat) (e : Fin 3)
    (hRand : RepRandomness stmt.schema.arity stmt.treeDepth) :
    honestHybrid1Rep H prgExpand stmt wit repIdx e hRand =
      simulateOpenedBlindVcRep prgExpand stmt repIdx e
        ((zkOpenedRepFullEquiv H prgExpand stmt wit repIdx e).toFun hRand) := by
  have hPin : ∀ k : Nat, (hk : k < stmt.schema.arity) → ∀ pubVal,
      vcLookupDisclosed stmt.disclosedAttrs (0 + k) = some pubVal →
      wit.attrs.toList[k]'(by rw [Vec.toList_length]; exact hk) = pubVal := by
    intro k hk pubVal hLook
    rw [Nat.zero_add] at hLook
    have hSome := hValid.2.1 (k, pubVal) (vcLookupDisclosed_mem hLook)
    rw [List.getElem?_eq_getElem (by rw [Vec.toList_length]; exact hk)] at hSome
    injection hSome
  obtain ⟨hRootSum, hPresSum, hScopeSum, hBoolZeros⟩ :=
    buildHonestBlindVcTriple_sums hValid
      (mkParty3At e hRand.seedE hRand.seedE1 (Vec.replicate 32 0))
      (mkParty3At e hRand.saltE hRand.saltE1 (Vec.replicate 32 0))
      hRand.attrShareCoins hRand.holderBlindCoins hRand.presBlindCoins hRand.merkleStepCoins
      (mkParty3At e (prgExpand stmt.treeDepth repIdx e hRand.seedE)
        (prgExpand stmt.treeDepth repIdx (vcNextParty3 e) hRand.seedE1) hRand.gateCoins)
  rcases hRand with ⟨seedE, seedE1, saltE, saltE1, attrC, hbC, pbC, mkC, gateU, comMask⟩
  let e1 := vcNextParty3 e
  let gE := prgExpand stmt.treeDepth repIdx e seedE
  let gE1 := prgExpand stmt.treeDepth repIdx e1 seedE1
  have hAttrSim : simAttrPairs e stmt.disclosedAttrs 0
      ((vcAttrSharesEquiv3 e stmt.disclosedAttrs 0 wit.attrs).1 attrC) =
      (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrC e,
       vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrC (vcNextParty3 e)) :=
    simAttrPairs_eq_honest e stmt.disclosedAttrs 0 wit.attrs attrC hPin
  have hHbFst : ((vcLane4OpenedShareEquiv3 e wit.holderBlind).toFun hbC).fst =
      vcShareLane4_3 wit.holderBlind hbC e := rfl
  have hHbSnd : ((vcLane4OpenedShareEquiv3 e wit.holderBlind).toFun hbC).snd =
      vcShareLane4_3 wit.holderBlind hbC (vcNextParty3 e) := rfl
  have hPbFst : ((vcLane4OpenedShareEquiv3 e wit.presBlind).toFun pbC).fst =
      vcShareLane4_3 wit.presBlind pbC e := rfl
  have hPbSnd : ((vcLane4OpenedShareEquiv3 e wit.presBlind).toFun pbC).snd =
      vcShareLane4_3 wit.presBlind pbC (vcNextParty3 e) := rfl
  unfold honestHybrid1Rep simulateOpenedBlindVcRep zkOpenedRepFullEquiv partyGateOutEquiv buildHonestBlindVcTriple
  dsimp only [seTrans, seDepProd, seProdCongr, seRefl,
    seSymm, repRandomnessTupleEquiv, partyGateCoinsTupleEquiv, xorBytesWithVecEquiv]
  rw [hAttrSim, hHbFst, hHbSnd, hPbFst, hPbSnd]
  dsimp only
  rw [vcPairCommitChunks_spec e stmt.schema
        (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrC)
        (vcShareLane4_3 wit.holderBlind hbC) vcAttrCommitTag,
      vcPairCommitChunks_spec e stmt.schema
        (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrC)
        (vcShareLane4_3 wit.presBlind pbC) vcPresCommitTag,
      vcPairScopeChunks_spec e stmt.schema.schemaId
        (vcShareLane4_3 wit.holderBlind hbC) stmt.verifierScopeLimbs]
  dsimp only
  have hgAttr : (fun i => (mkParty3At e gE gE1 gateU i).attrCoins) =
      mkParty3At e gE.attrCoins gE1.attrCoins gateU.attrCoins := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hgPres : (fun i => (mkParty3At e gE gE1 gateU i).presCoins) =
      mkParty3At e gE.presCoins gE1.presCoins gateU.presCoins := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hgScope : (fun i => (mkParty3At e gE gE1 gateU i).scopeCoins) =
      mkParty3At e gE.scopeCoins gE1.scopeCoins gateU.scopeCoins := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hgMk : (fun i => (mkParty3At e gE gE1 gateU i).merkleCoins) =
      mkParty3At e gE.merkleCoins gE1.merkleCoins gateU.merkleCoins := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  rw [hgAttr, hgPres, hgScope, hgMk]
  rw [simSponge3Perm_eq_honest, simSponge3Perm_eq_honest, simSponge3Perm_eq_honest]
  dsimp only
  rw [simMerklePath_eq_honest]
  dsimp only
  rw [mkParty3At_e, mkParty3At_next, mkParty3At_e, mkParty3At_next]
  congr 1
  unfold buildHonestBlindVcTriple at hRootSum hPresSum hScopeSum hBoolZeros
  dsimp only at hRootSum hPresSum hScopeSum hBoolZeros
  rw [hgAttr, hgMk] at hRootSum hBoolZeros
  rw [hgPres] at hPresSum
  rw [hgScope] at hScopeSum
  have hGetFn : ∀ {α : Type} (f : Fin 3 → α), (Triple3.ofFn f).get = f :=
    fun f => funext (Triple3.get_ofFn f)
  rw [hGetFn] at hRootSum hPresSum hScopeSum
  have hR := vcUnopened_of_sumLane6_3 e hRootSum
  have hP := vcUnopened_of_sumLane6_3 e hPresSum
  have hS := vcUnopened_of_sumLane6_3 e hScopeSum
  unfold completeLane6Shares3 completeZeroShares3 vcPairAtLane6
  congr 1
  · exact congrArg Triple3.ofFn hR
  · exact congrArg Triple3.ofFn hP
  · exact congrArg Triple3.ofFn hS
  · rw [List.map_map]
    have hMapEq : ∀ (bzs : List VcWire3),
        (∀ t ∈ List.map Triple3.ofFn bzs, vcSum3 t.get = Goldilocks.zero) →
        List.map Triple3.ofFn bzs =
          List.map ((fun p : Goldilocks × Goldilocks =>
            Triple3.ofFn (mkParty3At e p.1 p.2
              (Goldilocks.sub (Goldilocks.sub Goldilocks.zero p.1) p.2))) ∘
            (fun w => vcPairAt w e)) bzs := by
      intro bzs hBZ
      induction bzs with
      | nil => rfl
      | cons z zs ih =>
        dsimp only [List.map, Function.comp, vcPairAt]
        have hzSum : vcSum3 z = Goldilocks.zero := by
          have hm := hBZ (Triple3.ofFn z) (.head _)
          rwa [hGetFn] at hm
        have hz0 := vcUnopened_of_sum3 e hzSum
        rw [← congrArg Triple3.ofFn hz0, ih (fun t ht => hBZ t (.tail _ ht))]
        rfl
    exact hMapEq _ hBoolZeros

/-- Every simulated `OpenedBlindVcRep` passes `verifyOpenedBlindVcRep = true` (including
    `checkPartyPrgTape` on BOTH `viewE` and `viewE1`) whenever `stmt.disclosedAttrs` is strictly ascending. -/
theorem simulateOpenedBlindVcRep_verifies
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (hAsc : vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true)
    (repIdx : Nat) (e : Fin 3)
    (simRand : RepRandomness stmt.schema.arity stmt.treeDepth) :
    verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
      stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
      stmt.disclosedAttrs repIdx e (simulateOpenedBlindVcRep prgExpand stmt repIdx e simRand) = true := by
  let o := simulateOpenedBlindVcRep prgExpand stmt repIdx e simRand
  obtain ⟨hALen1, hALen2⟩ := simAttrPairs_length e stmt.disclosedAttrs 0 simRand.attrShareCoins
  obtain ⟨hDisc1, hDisc2⟩ := simAttrPairs_disclosed_ok e hAsc simRand.attrShareCoins
  let gE := prgExpand stmt.treeDepth repIdx e simRand.seedE
  let gE1 := prgExpand stmt.treeDepth repIdx (vcNextParty3 e) simRand.seedE1
  obtain ⟨hMkLen1, hMkLen2⟩ := simMerklePath_length e stmt.issuerEpoch 0 _ simRand.merkleStepCoins
    gE.merkleCoins gE1.merkleCoins simRand.gateCoins.merkleCoins
  have hTapeE : checkPartyPrgTape prgExpand stmt.treeDepth repIdx e o.viewE = true := by
    unfold checkPartyPrgTape
    apply decide_eq_true
    unfold extractPartyGateCoins
    dsimp only [o, simulateOpenedBlindVcRep]
    rw [(extractSponge3Coins_sim e _ _ _ gE.attrCoins gE1.attrCoins _).1,
        (extractSponge3Coins_sim e _ _ _ gE.presCoins gE1.presCoins _).1,
        (extractSponge3Coins_sim e _ _ _ gE.scopeCoins gE1.scopeCoins _).1,
        (extractMerklePathCoins_sim e stmt.issuerEpoch 0 _ _ gE.merkleCoins gE1.merkleCoins _).1]
  have hTapeE1 : checkPartyPrgTape prgExpand stmt.treeDepth repIdx (vcNextParty3 e) o.viewE1 = true := by
    unfold checkPartyPrgTape
    apply decide_eq_true
    unfold extractPartyGateCoins
    dsimp only [o, simulateOpenedBlindVcRep]
    rw [(extractSponge3Coins_sim e _ _ _ gE.attrCoins gE1.attrCoins _).2,
        (extractSponge3Coins_sim e _ _ _ gE.presCoins gE1.presCoins _).2,
        (extractSponge3Coins_sim e _ _ _ gE.scopeCoins gE1.scopeCoins _).2,
        (extractMerklePathCoins_sim e stmt.issuerEpoch 0 _ _ gE.merkleCoins gE1.merkleCoins _).2]
  change verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
    stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
    stmt.disclosedAttrs repIdx e o = true
  unfold verifyOpenedBlindVcRep
  dsimp only
  have hGuardTrue :
      (decide (o.e = e) &&
       vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs &&
       decide (o.viewE.attrShares.length = stmt.schema.arity) &&
       decide (o.viewE1.attrShares.length = stmt.schema.arity) &&
       decide (o.viewE.merkleLevels.length = stmt.treeDepth) &&
       decide (o.viewE1.merkleLevels.length = stmt.treeDepth) &&
       vcCheckPartyDisclosedShares o.e o.viewE.attrShares stmt.disclosedAttrs &&
       vcCheckPartyDisclosedShares (vcNextParty3 o.e) o.viewE1.attrShares stmt.disclosedAttrs &&
       checkPartyPrgTape prgExpand stmt.treeDepth repIdx o.e o.viewE &&
       checkPartyPrgTape prgExpand stmt.treeDepth repIdx (vcNextParty3 o.e) o.viewE1) = true := by
    have hoe : o.e = e := rfl
    have ha1 : o.viewE.attrShares.length = stmt.schema.arity := hALen1
    have ha2 : o.viewE1.attrShares.length = stmt.schema.arity := hALen2
    have hm1 : o.viewE.merkleLevels.length = stmt.treeDepth := hMkLen1
    have hm2 : o.viewE1.merkleLevels.length = stmt.treeDepth := hMkLen2
    have hd1 : vcCheckPartyDisclosedShares e o.viewE.attrShares stmt.disclosedAttrs = true := hDisc1
    have hd2 : vcCheckPartyDisclosedShares (vcNextParty3 e) o.viewE1.attrShares stmt.disclosedAttrs = true := hDisc2
    rw [hoe, decide_eq_true rfl, hAsc,
        decide_eq_true ha1, decide_eq_true ha2,
        decide_eq_true hm1, decide_eq_true hm2,
        hd1, hd2, hTapeE, hTapeE1]
    rfl
  rw [hGuardTrue]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  dsimp only [o, simulateOpenedBlindVcRep]
  rw [pairCheckSponge3Perm_sim, pairCheckSponge3Perm_sim, pairCheckSponge3Perm_sim]
  dsimp only
  rw [pairCheckMerklePath_sim]
  dsimp only
  have hCompletePair : ∀ (target : Lane6) (p : Lane6 × Lane6),
      vcPairAtLane6 (completeLane6Shares3 e target p).get e = p := by
    intro target ⟨p1, p2⟩
    unfold completeLane6Shares3 vcPairAtLane6
    rw [Triple3.get_ofFn, Triple3.get_ofFn, mkParty3At_e, mkParty3At_next]
  have hCompleteSum : ∀ (target : Lane6) (p : Lane6 × Lane6),
      vcSumLane6_3 (completeLane6Shares3 e target p).get = target := by
    intro target ⟨p1, p2⟩
    unfold completeLane6Shares3
    have hGet : (Triple3.ofFn (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2))).get =
        mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) := funext (Triple3.get_ofFn _)
    rw [hGet, vcSumLane6_3_eq]
    have hScalar : ∀ (t a b : Goldilocks),
        vcSum3 (fun i => mkParty3At e a b (Goldilocks.sub (Goldilocks.sub t a) b) i) = t := by
      intro t a b
      unfold vcSum3
      rcases fin3_eq_012 e with rfl | rfl | rfl <;>
        (dsimp only [mkParty3At];
         rw [← goldOfInt_nat t, ← goldOfInt_nat a, ← goldOfInt_nat b];
         simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega)
    have hProj0 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x0) =
        (fun i => mkParty3At e p1.x0 p2.x0 (Goldilocks.sub (Goldilocks.sub target.x0 p1.x0) p2.x0) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj1 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x1) =
        (fun i => mkParty3At e p1.x1 p2.x1 (Goldilocks.sub (Goldilocks.sub target.x1 p1.x1) p2.x1) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj2 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x2) =
        (fun i => mkParty3At e p1.x2 p2.x2 (Goldilocks.sub (Goldilocks.sub target.x2 p1.x2) p2.x2) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj3 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x3) =
        (fun i => mkParty3At e p1.x3 p2.x3 (Goldilocks.sub (Goldilocks.sub target.x3 p1.x3) p2.x3) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj4 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x4) =
        (fun i => mkParty3At e p1.x4 p2.x4 (Goldilocks.sub (Goldilocks.sub target.x4 p1.x4) p2.x4) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj5 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x5) =
        (fun i => mkParty3At e p1.x5 p2.x5 (Goldilocks.sub (Goldilocks.sub target.x5 p1.x5) p2.x5) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    rw [hProj0, hProj1, hProj2, hProj3, hProj4, hProj5,
        hScalar, hScalar, hScalar, hScalar, hScalar, hScalar]
  have hBzOk : ∀ pairs : List (Goldilocks × Goldilocks),
      checkBoolZeroOutputs e pairs (completeZeroShares3 e pairs) = true := by
    intro pairs
    rw [checkBoolZeroOutputs_spec]
    refine ⟨?_, ?_⟩
    · induction pairs with
      | nil => rfl
      | cons hd tl ih =>
        rcases hd with ⟨a, b⟩
        unfold completeZeroShares3 at ih ⊢
        dsimp only [List.map]
        rw [← ih]
        congr 1
        unfold vcPairAt
        rw [Triple3.get_ofFn, Triple3.get_ofFn, mkParty3At_e, mkParty3At_next]
    · intro t ht
      obtain ⟨⟨a, b⟩, _, rfl⟩ := List.mem_map.mp ht
      have hGet : (Triple3.ofFn (mkParty3At e a b (Goldilocks.sub (Goldilocks.sub Goldilocks.zero a) b))).get =
          mkParty3At e a b (Goldilocks.sub (Goldilocks.sub Goldilocks.zero a) b) := funext (Triple3.get_ofFn _)
      rw [hGet]
      unfold vcSum3
      rcases fin3_eq_012 e with rfl | rfl | rfl <;>
        (dsimp only [mkParty3At];
         rw [← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat a, ← goldOfInt_nat b];
         simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega)
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨decide_eq_true (hCompletePair _ _), decide_eq_true (hCompleteSum _ _)⟩,
            decide_eq_true (hCompletePair _ _)⟩, decide_eq_true (hCompleteSum _ _)⟩,
          decide_eq_true (hCompletePair _ _)⟩, decide_eq_true (hCompleteSum _ _)⟩, hBzOk _⟩

/-- Multi-repetition 2-witness indistinguishability bijection (`zkMultiRepViewEquiv`, `0 Classical.choice`, fixing `C0-3`):
    for ANY two valid secret witnesses `wit₁, wit₂` matching the same public statement `stmt` and any
    challenge vector `chals : Fin R → Fin 3`, maps `wit₁`'s randomness space bijectively onto `wit₂`'s
    randomness space so that all `R` full `OpenedBlindVcRep` views are **structurally identical**! -/
def zkMultiRepViewEquiv
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (R : Nat) (stmt : BlindVcPublicStatement)
    (wit₁ wit₂ : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (chals : Fin R → Fin 3) :
    SimpleEquiv (Fin R → RepRandomness stmt.schema.arity stmt.treeDepth)
                (Fin R → RepRandomness stmt.schema.arity stmt.treeDepth) :=
  sePiCongrRight fun r =>
    seTrans
      (zkOpenedRepFullEquiv H prgExpand stmt wit₁ r.val (chals r))
      (seSymm (zkOpenedRepFullEquiv H prgExpand stmt wit₂ r.val (chals r)))

theorem zkMultiRepViewEquiv_indistinguishable
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (R : Nat) (stmt : BlindVcPublicStatement)
    (wit₁ wit₂ : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid₁ : BlindVcWitnessValid stmt wit₁)
    (hValid₂ : BlindVcWitnessValid stmt wit₂)
    (chals : Fin R → Fin 3)
    (rands₁ : Fin R → RepRandomness stmt.schema.arity stmt.treeDepth) :
    let rands₂ := (zkMultiRepViewEquiv H prgExpand R stmt wit₁ wit₂ chals).toFun rands₁
    ∀ r : Fin R,
      honestHybrid1Rep H prgExpand stmt wit₁ r.val (chals r) (rands₁ r) =
        simulateOpenedBlindVcRep prgExpand stmt r.val (chals r)
          ((zkOpenedRepFullEquiv H prgExpand stmt wit₁ r.val (chals r)).toFun (rands₁ r)) ∧
      honestHybrid1Rep H prgExpand stmt wit₁ r.val (chals r) (rands₁ r) =
        honestHybrid1Rep H prgExpand stmt wit₂ r.val (chals r) (rands₂ r) := by
  intro rands₂ r
  have h1 := zkOpenedRepFullEquiv_simulates H prgExpand stmt wit₁ hValid₁ r.val (chals r) (rands₁ r)
  have h2 := zkOpenedRepFullEquiv_simulates H prgExpand stmt wit₂ hValid₂ r.val (chals r) (rands₂ r)
  refine ⟨h1, ?_⟩
  rw [h1, h2]
  dsimp only [rands₂, zkMultiRepViewEquiv, sePiCongrRight, seTrans, seSymm]
  rw [(zkOpenedRepFullEquiv H prgExpand stmt wit₂ r.val (chals r)).right_inv]

def vecOfListPad : (n : Nat) → List UInt8 → Vec UInt8 n
  | 0, _ => .nil
  | n + 1, [] => .cons 0 (vecOfListPad n [])
  | n + 1, b :: bs => .cons b (vecOfListPad n bs)

private theorem vecOfListPad_toList :
    ∀ {n : Nat} {bs : List UInt8},
      bs.length = n → (vecOfListPad n bs).toList = bs
  | 0, [], _ => rfl
  | n + 1, b :: bs, hLen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [vecOfListPad, Vec.toList]
    rw [vecOfListPad_toList hLen]

private theorem buildHonestBlindVcTriple_views_and_outs
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (seeds₁ seeds₂ salts₁ salts₂ : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth)
    (gateCoins3 : Fin 3 → PartyGateCoins stmt.treeDepth)
    (e : Fin 3)
    (hsE : seeds₁ e = seeds₂ e)
    (hsE1 : seeds₁ (vcNextParty3 e) = seeds₂ (vcNextParty3 e))
    (htE : salts₁ e = salts₂ e)
    (htE1 : salts₁ (vcNextParty3 e) = salts₂ (vcNextParty3 e)) :
    let tr₁ := buildHonestBlindVcTriple stmt wit seeds₁ salts₁ attrCoins hbCoins pbCoins mkCoins gateCoins3
    let tr₂ := buildHonestBlindVcTriple stmt wit seeds₂ salts₂ attrCoins hbCoins pbCoins mkCoins gateCoins3
    tr₁.views e = tr₂.views e ∧
    tr₁.views (vcNextParty3 e) = tr₂.views (vcNextParty3 e) ∧
    tr₁.finalOuts = tr₂.finalOuts := by
  dsimp only [buildHonestBlindVcTriple]
  rw [hsE, hsE1, htE, htE1]
  exact ⟨rfl, rfl, rfl⟩

/-- Connect real-world PRG prover (`honestPrgTriple`, Hybrid 0) unconditionally to `honestHybrid1Rep`
    and `simulateOpenedBlindVcRep`: for EVERY 32-byte hash `H` and EVERY `(seeds, salts)` triple,
    opening `honestPrgTriple` at `e` equals `honestHybrid1Rep` (and hence `simulateOpenedBlindVcRep`
    for valid witnesses) across all fields of `OpenedBlindVcRep`! -/
theorem openBlindVcRep_honestPrgTriple_eq_hybrid1
    {H : List UInt8 → List UInt8} (hH32 : ∀ m, (H m).length = 32)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (repIdx : Nat) (e : Fin 3)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth) :
    let e1 := vcNextParty3 e
    let e2 := vcUnopenedParty3 e
    let tr := honestPrgTriple prgExpand stmt wit repIdx seeds salts attrCoins hbCoins pbCoins mkCoins
    let gE := prgExpand stmt.treeDepth repIdx e (seeds e)
    let gE1 := prgExpand stmt.treeDepth repIdx e1 (seeds e1)
    let gU := prgExpand stmt.treeDepth repIdx e2 (seeds e2)
    let tr₀ := buildHonestBlindVcTriple stmt wit
      (mkParty3At e (seeds e) (seeds e1) (Vec.replicate 32 0))
      (mkParty3At e (salts e) (salts e1) (Vec.replicate 32 0))
      attrCoins hbCoins pbCoins mkCoins (mkParty3At e gE gE1 gU)
    let rawComU := vcCommitPartyView H stmt.presNonce repIdx e2 (tr₀.views e2)
      (vcPartyFinalOutAt tr₀.finalOuts e2)
    let realComU := vcCommitPartyView H stmt.presNonce repIdx e2 (tr.views e2)
      (vcPartyFinalOutAt tr.finalOuts e2)
    openBlindVcRep H stmt.presNonce repIdx tr e =
      honestHybrid1Rep H prgExpand stmt wit repIdx e
        { seedE := seeds e
          seedE1 := seeds e1
          saltE := salts e
          saltE1 := salts e1
          attrShareCoins := attrCoins
          holderBlindCoins := hbCoins
          presBlindCoins := pbCoins
          merkleStepCoins := mkCoins
          gateCoins := gU
          unopenedCommitCoins := xorBytesWithVec rawComU (vecOfListPad 32 realComU) } := by
  intro e1 e2 tr gE gE1 gU tr₀ rawComU realComU
  have hGateEq : (fun i => prgExpand stmt.treeDepth repIdx i (seeds i)) = mkParty3At e gE gE1 gU :=
    (mkParty3At_eta e (fun i => prgExpand stmt.treeDepth repIdx i (seeds i))).symm
  have hTrEq : tr = buildHonestBlindVcTriple stmt wit seeds salts attrCoins hbCoins pbCoins mkCoins
      (mkParty3At e gE gE1 gU) := by
    dsimp only [tr, honestPrgTriple]
    rw [hGateEq]
  obtain ⟨hvE, hvE1, hFo⟩ := buildHonestBlindVcTriple_views_and_outs stmt wit
    seeds (mkParty3At e (seeds e) (seeds e1) (Vec.replicate 32 0))
    salts (mkParty3At e (salts e) (salts e1) (Vec.replicate 32 0))
    attrCoins hbCoins pbCoins mkCoins (mkParty3At e gE gE1 gU) e
    (mkParty3At_e e (seeds e) (seeds e1) _).symm
    (mkParty3At_next e (seeds e) (seeds e1) _).symm
    (mkParty3At_e e (salts e) (salts e1) _).symm
    (mkParty3At_next e (salts e) (salts e1) _).symm
  have hReal32 : realComU.length = 32 := by
    dsimp only [realComU, vcCommitPartyView]
    exact hH32 _
  unfold openBlindVcRep honestHybrid1Rep
  dsimp only [e1, e2, gE, gE1, gU, tr₀, rawComU]
  rw [xorBytesWithVec_involutive, vecOfListPad_toList hReal32]
  dsimp only [realComU, e1, e2]
  rw [hTrEq, hvE, hvE1, hFo]

/-- Every opened repetition of `honestPrgTriple` for a valid witness passes `verifyOpenedBlindVcRep = true`
    (for arbitrary `H`, `prgExpand`, `seeds`, and `salts`). -/
theorem openBlindVcRep_honestPrgTriple_verifies
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (repIdx : Nat) (e : Fin 3)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth) :
    verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
      stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
      stmt.disclosedAttrs repIdx e
      (openBlindVcRep H stmt.presNonce repIdx
        (honestPrgTriple prgExpand stmt wit repIdx seeds salts attrCoins hbCoins pbCoins mkCoins) e) = true := by
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  let gE := prgExpand stmt.treeDepth repIdx e (seeds e)
  let gE1 := prgExpand stmt.treeDepth repIdx e1 (seeds e1)
  let gU := prgExpand stmt.treeDepth repIdx e2 (seeds e2)
  let hRand0 : RepRandomness stmt.schema.arity stmt.treeDepth :=
    { seedE := seeds e
      seedE1 := seeds e1
      saltE := salts e
      saltE1 := salts e1
      attrShareCoins := attrCoins
      holderBlindCoins := hbCoins
      presBlindCoins := pbCoins
      merkleStepCoins := mkCoins
      gateCoins := gU
      unopenedCommitCoins := Vec.replicate 32 0 }
  let oReal := openBlindVcRep H stmt.presNonce repIdx
    (honestPrgTriple prgExpand stmt wit repIdx seeds salts attrCoins hbCoins pbCoins mkCoins) e
  let oHyb := honestHybrid1Rep H prgExpand stmt wit repIdx e hRand0
  have hIgnoreUc : verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
      stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
      stmt.disclosedAttrs repIdx e oReal =
      verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
        stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
        stmt.disclosedAttrs repIdx e { oReal with unopenedCommit := oHyb.unopenedCommit } := rfl
  have hOpenedEq : { oReal with unopenedCommit := oHyb.unopenedCommit } = oHyb := by
    have hGateEq : (fun i => prgExpand stmt.treeDepth repIdx i (seeds i)) = mkParty3At e gE gE1 gU :=
      (mkParty3At_eta e (fun i => prgExpand stmt.treeDepth repIdx i (seeds i))).symm
    obtain ⟨hvE, hvE1, hFo⟩ := buildHonestBlindVcTriple_views_and_outs stmt wit
      seeds (mkParty3At e (seeds e) (seeds e1) (Vec.replicate 32 0))
      salts (mkParty3At e (salts e) (salts e1) (Vec.replicate 32 0))
      attrCoins hbCoins pbCoins mkCoins (mkParty3At e gE gE1 gU) e
      (mkParty3At_e e (seeds e) (seeds e1) _).symm
      (mkParty3At_next e (seeds e) (seeds e1) _).symm
      (mkParty3At_e e (salts e) (salts e1) _).symm
      (mkParty3At_next e (salts e) (salts e1) _).symm
    dsimp only [oReal, oHyb, openBlindVcRep, honestHybrid1Rep, honestPrgTriple, hRand0, e1, e2, gE, gE1, gU]
    rw [hGateEq, hvE, hvE1, hFo]
  change verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
    stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
    stmt.disclosedAttrs repIdx e oReal = true
  rw [hIgnoreUc, hOpenedEq]
  dsimp only [oHyb]
  rw [zkOpenedRepFullEquiv_simulates H prgExpand stmt wit hValid repIdx e hRand0]
  exact simulateOpenedBlindVcRep_verifies prgExpand stmt hValid.1 repIdx e _

/-! #### 2-Phase Fiat-Shamir Prover (`proveBlindVcPresentation`), Flagship Theorem, `#tooth` & Inhabitedness -/

/-- Per-repetition prover randomness `(seeds, salts, wire share coins)` for `proveBlindVcPresentation`. -/
structure ProverRepCoins (arity treeDepth : Nat) where
  seeds : Fin 3 → Vec UInt8 32
  salts : Fin 3 → Vec UInt8 32
  attrCoins : Vec (Goldilocks × Goldilocks) arity
  hbCoins : Lane4 × Lane4
  pbCoins : Lane4 × Lane4
  mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) treeDepth

def buildProverTriplesFrom
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    Nat → Nat → List BlindVcRepTriple
  | _, 0 => []
  | repIdx, count + 1 =>
    let c := proverCoins repIdx
    honestPrgTriple prgExpand stmt wit repIdx c.seeds c.salts c.attrCoins c.hbCoins c.pbCoins c.mkCoins ::
      buildProverTriplesFrom prgExpand stmt wit proverCoins (repIdx + 1) count

def tripleRound1 (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (tr : BlindVcRepTriple) : Triple3 (List UInt8) × VcRepFinalOuts3 :=
  (Triple3.ofFn (fun i => vcCommitPartyView H presNonce repIdx i (tr.views i)
     (vcPartyFinalOutAt tripleFinal i)),
   tr.finalOuts)
where
  tripleFinal := tr.finalOuts

def allTripleRound1From (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32) :
    Nat → List BlindVcRepTriple → List (Triple3 (List UInt8) × VcRepFinalOuts3)
  | _, [] => []
  | repIdx, tr :: rest => tripleRound1 H presNonce repIdx tr ::
      allTripleRound1From H presNonce (repIdx + 1) rest

def openAllTriplesFrom (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (trDigest : List UInt8) : Nat → List BlindVcRepTriple → List OpenedBlindVcRep
  | _, [] => []
  | repIdx, tr :: rest =>
    openBlindVcRep H presNonce repIdx tr (deriveBlindVcChallengeAt H trDigest repIdx) ::
      openAllTriplesFrom H presNonce trDigest (repIdx + 1) rest

/-- Constructive 2-phase Fiat-Shamir prover (`prove_selective_disclosure_with_profile`, `blind_vc.rs:1960-2118`):
    1. Executes all `profile.repetitions` 3-party ZKBoo instances from PRG seeds and commits all 3 party views;
    2. Derives `"QSAG.FS.INIT/ABSORB/SQUEEZE.V1"` Fiat-Shamir challenges `e_r ∈ {0, 1, 2}` from the full Round-1 bundle;
    3. Opens `(view[e_r], view[(e_r + 1) % 3], com[(e_r + 2) % 3], finalOuts)`. -/
def proveBlindVcPresentation
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (stmt : BlindVcPublicStatement)
    (issuerRootTag : Vec UInt8 32)
    (verifierChallenge : List UInt8)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    BlindVcPresentation :=
  let triples := buildProverTriplesFrom prgExpand stmt wit proverCoins 0 profile.repetitions
  let allRound1 := allTripleRound1From H stmt.presNonce 0 triples
  let trDigest := deriveBlindVcTranscriptDigest H verifierChallenge profile stmt.schema stmt.treeDepth
    stmt.presNonce issuerRootTag stmt.issuerEpoch
    stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
    stmt.disclosedAttrs allRound1
  { presentationNonce := stmt.presNonce
    issuerEpoch := stmt.issuerEpoch
    schemaId := stmt.schema.schemaId
    accumulatorRoot := stmt.accumulatorRoot
    issuerRootTag := issuerRootTag
    verifierScopeLimbs := stmt.verifierScopeLimbs
    disclosedAttrs := stmt.disclosedAttrs
    presCommit := stmt.presCommit
    scopeTag := stmt.scopeTag
    openedReps := openAllTriplesFrom H stmt.presNonce trDigest 0 triples }

private theorem buildProverTriplesFrom_length
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    ∀ (repIdx count : Nat),
      (buildProverTriplesFrom prgExpand stmt wit proverCoins repIdx count).length = count
  | _, 0 => rfl
  | repIdx, count + 1 => by
    dsimp only [buildProverTriplesFrom, List.length_cons]
    rw [buildProverTriplesFrom_length prgExpand stmt wit proverCoins (repIdx + 1) count]

private theorem openAllTriplesFrom_length (H : List UInt8 → List UInt8)
    (presNonce : Vec UInt8 32) (trDigest : List UInt8) :
    ∀ (repIdx : Nat) (trs : List BlindVcRepTriple),
      (openAllTriplesFrom H presNonce trDigest repIdx trs).length = trs.length
  | _, [] => rfl
  | repIdx, _ :: rest => by
    dsimp only [openAllTriplesFrom, List.length_cons]
    rw [openAllTriplesFrom_length H presNonce trDigest (repIdx + 1) rest]

private theorem reconstructAllRepRound1_openAllTriplesFrom (H : List UInt8 → List UInt8)
    (presNonce : Vec UInt8 32) (trDigest : List UInt8) :
    ∀ (repIdx : Nat) (trs : List BlindVcRepTriple),
      reconstructAllRepRound1 H presNonce repIdx (openAllTriplesFrom H presNonce trDigest repIdx trs) =
        allTripleRound1From H presNonce repIdx trs
  | _, [] => rfl
  | repIdx, tr :: rest => by
    dsimp only [openAllTriplesFrom, reconstructAllRepRound1, allTripleRound1From,
      tripleRound1, tripleRound1.tripleFinal]
    rw [reconstructRepRound1_openBlindVcRep,
        reconstructAllRepRound1_openAllTriplesFrom H presNonce trDigest (repIdx + 1) rest]

private theorem verifyAllBlindVcReps_proverTriples
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth)
    (trDigest : List UInt8) :
    ∀ (repIdx count : Nat),
      verifyAllBlindVcReps H prgExpand trDigest stmt.schema stmt.issuerEpoch stmt.treeDepth
        stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
        stmt.disclosedAttrs repIdx
        (openAllTriplesFrom H stmt.presNonce trDigest repIdx
          (buildProverTriplesFrom prgExpand stmt wit proverCoins repIdx count)) = true
  | _, 0 => rfl
  | repIdx, count + 1 => by
    dsimp only [buildProverTriplesFrom, openAllTriplesFrom, verifyAllBlindVcReps]
    rw [openBlindVcRep_honestPrgTriple_verifies H prgExpand stmt wit hValid repIdx
          (deriveBlindVcChallengeAt H trDigest repIdx),
        verifyAllBlindVcReps_proverTriples H prgExpand stmt wit hValid proverCoins trDigest (repIdx + 1) count]
    rfl

/-- **2-Phase Fiat-Shamir Prover Completeness (`proveBlindVcPresentation_verifies`)**:
    For EVERY hash `H`, PRG `prgExpand`, soundness profile `profile`, and valid secret witness `wit`,
    `proveBlindVcPresentation` produces `profile.repetitions` opened repetitions accepted by
    `verifyBlindVcPresentation = true`! -/
theorem proveBlindVcPresentation_verifies
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (stmt : BlindVcPublicStatement)
    (issuerRootTag : Vec UInt8 32)
    (verifierChallenge : List UInt8)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    let pres := proveBlindVcPresentation H prgExpand profile stmt issuerRootTag verifierChallenge wit proverCoins
    pres.openedReps.length = profile.repetitions ∧
    verifyBlindVcPresentation H prgExpand profile stmt.schema stmt.treeDepth verifierChallenge pres = true := by
  intro pres
  have hLen : pres.openedReps.length = profile.repetitions := by
    dsimp only [pres, proveBlindVcPresentation]
    rw [openAllTriplesFrom_length, buildProverTriplesFrom_length]
  refine ⟨hLen, ?_⟩
  unfold verifyBlindVcPresentation
  have hTopGuard :
      (decide (pres.schemaId = stmt.schema.schemaId) &&
       vcCheckDisclosedStrictAsc stmt.schema.arity pres.disclosedAttrs &&
       decide (pres.openedReps.length = profile.repetitions)) = true := by
    have hSid : pres.schemaId = stmt.schema.schemaId := rfl
    have hDisc : pres.disclosedAttrs = stmt.disclosedAttrs := rfl
    rw [hSid, decide_eq_true rfl, hDisc, hValid.1, decide_eq_true hLen]
    rfl
  rw [hTopGuard]
  dsimp only [Bool.not_true, ↓reduceIte, pres, proveBlindVcPresentation]
  rw [reconstructAllRepRound1_openAllTriplesFrom]
  exact verifyAllBlindVcReps_proverTriples H prgExpand stmt wit hValid proverCoins _ 0 profile.repetitions

/-- Verifier-enforced structural invariants extracted directly from `verifyBlindVcPresentation = true`
    (fixing `C0-3` & `C1-2`: strict ascending `Nodup` and `profile.repetitions` are checked inside the verifier). -/
theorem verifyBlindVcPresentation_enforces_guards
    {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {profile : ZkSoundnessProfile}
    {expectedSchema : VcSchema} {treeDepth : Nat}
    {verifierChallenge : List UInt8}
    {pres : BlindVcPresentation}
    (hVer : verifyBlindVcPresentation H prgExpand profile expectedSchema treeDepth verifierChallenge pres = true) :
    pres.schemaId = expectedSchema.schemaId ∧
    pres.openedReps.length = profile.repetitions ∧
    (∀ p ∈ pres.disclosedAttrs, p.1 < expectedSchema.arity) ∧
    (pres.disclosedAttrs.map Prod.fst).Nodup := by
  unfold verifyBlindVcPresentation at hVer
  cases hG :
      (decide (pres.schemaId = expectedSchema.schemaId) &&
       vcCheckDisclosedStrictAsc expectedSchema.arity pres.disclosedAttrs &&
       decide (pres.openedReps.length = profile.repetitions)) with
  | false => rw [hG] at hVer; cases hVer
  | true =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
    obtain ⟨hBounds, hNodup⟩ := vcCheckDisclosedStrictAsc_bounds_and_nodup hG.1.2
    exact ⟨hG.1.1, hG.2, hBounds, hNodup⟩

set_option exponentiation.threshold 1024 in
/-- Verifier checks, prover completeness, commitment-bound special soundness,
repetition parameter arithmetic, and hybrid-1 fixed-challenge simulation.
The hiding component uses independent hidden tapes and an independently masked
unopened commitment. This theorem does not prove the real-to-hybrid PRG and
commitment-hiding hops, or adaptive ROM/QROM security. -/
theorem blind_vc_zkboo_selective_disclosure_sound_and_hiding
    {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D) :
    -- (1) Verifier-enforced schema, repetition count, `< arity` bounds, and `Nodup`
    (∀ (profile : ZkSoundnessProfile) (expectedSchema : VcSchema) (treeDepth : Nat)
       (verifierChallenge : List UInt8) (pres : BlindVcPresentation),
      verifyBlindVcPresentation H prgExpand profile expectedSchema treeDepth verifierChallenge pres = true →
      pres.schemaId = expectedSchema.schemaId ∧
      pres.openedReps.length = profile.repetitions ∧
      (∀ p ∈ pres.disclosedAttrs, p.1 < expectedSchema.arity) ∧
      (pres.disclosedAttrs.map Prod.fst).Nodup) ∧
    -- (2) Constructive 2-phase Fiat-Shamir prover completeness
    (∀ (profile : ZkSoundnessProfile) (stmt : BlindVcPublicStatement)
       (issuerRootTag : Vec UInt8 32) (verifierChallenge : List UInt8)
       (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth),
      BlindVcWitnessValid stmt wit →
      ∀ proverCoins,
        verifyBlindVcPresentation H prgExpand profile stmt.schema stmt.treeDepth verifierChallenge
          (proveBlindVcPresentation H prgExpand profile stmt issuerRootTag verifierChallenge wit proverCoins) = true) ∧
    -- (3) Round-1 commitment-bound 3-challenge special soundness (zero external `Nodup` premise)
    (∀ (presNonce : Vec UInt8 32) (schema : VcSchema) (issuerEpoch : UInt64) (treeDepth : Nat)
       (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
       (disclosed : List (Nat × Goldilocks)) (repIdx : Nat),
      ∀ (o0 o1 o2 : OpenedBlindVcRep),
        reconstructRepRound1 H presNonce repIdx o0 = reconstructRepRound1 H presNonce repIdx o1 →
        reconstructRepRound1 H presNonce repIdx o1 = reconstructRepRound1 H presNonce repIdx o2 →
        verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
          accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 0 o0 = true →
        verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
          accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 1 o1 = true →
        verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
          accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 2 o2 = true →
        (∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂) ∨
        ∃ (attrs : List Goldilocks) (holderBlind presBlind : Lane4)
          (leafCommit : Lane6) (boolSteps : List (Bool × Lane6)),
          (disclosed.map Prod.fst).Nodup ∧
          attrs.length = schema.arity ∧
          (∀ p ∈ disclosed, p.1 < schema.arity ∧ attrs[p.1]? = some p.2) ∧
          computeVcPoseidon2Commit schema attrs holderBlind vcAttrCommitTag = some leafCommit ∧
          boolSteps.length = treeDepth ∧
          evalVcMerklePathBool issuerEpoch 0 leafCommit boolSteps = accRoot ∧
          computeVcPoseidon2Commit schema attrs presBlind vcPresCommitTag = some presCommit ∧
          computeVcScopeTag schema.schemaId holderBlind verifierScopeLimbs = scopeTag) ∧
    -- (4) Fixed-challenge survival count and repetition parameter arithmetic
    ((∀ bad : Fin 3, ((List.finRange 3).filter (fun e => vcUnopenedParty3 e == bad)).length = 1 ∧
       ((List.finRange 3).filter (fun e => vcUnopenedParty3 e != bad)).length = 2) ∧
     ZkSoundnessProfile.classical128.repetitions = 219 ∧
     ZkSoundnessProfile.quantum128.repetitions = 438 ∧
     ratLe (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions) (1, 2 ^ 128) ∧
     ratLe (1, 2 ^ 130) (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions) ∧
     ratLe (2 ^ ZkSoundnessProfile.quantum128.repetitions, 3 ^ ZkSoundnessProfile.quantum128.repetitions) (1, 2 ^ 256)) ∧
    -- (5) Full `OpenedBlindVcRep` simulation & multi-rep 2-witness indistinguishability
    (∀ (R : Nat) (stmt : BlindVcPublicStatement)
       (wit₁ wit₂ : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth),
      BlindVcWitnessValid stmt wit₁ →
      BlindVcWitnessValid stmt wit₂ →
      ∀ (chals : Fin R → Fin 3) (rands₁ : Fin R → RepRandomness stmt.schema.arity stmt.treeDepth) (r : Fin R),
        let rands₂ := (zkMultiRepViewEquiv H prgExpand R stmt wit₁ wit₂ chals).toFun rands₁
        honestHybrid1Rep H prgExpand stmt wit₁ r.val (chals r) (rands₁ r) =
          simulateOpenedBlindVcRep prgExpand stmt r.val (chals r)
            ((zkOpenedRepFullEquiv H prgExpand stmt wit₁ r.val (chals r)).toFun (rands₁ r)) ∧
        honestHybrid1Rep H prgExpand stmt wit₁ r.val (chals r) (rands₁ r) =
          honestHybrid1Rep H prgExpand stmt wit₂ r.val (chals r) (rands₂ r)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro profile expectedSchema treeDepth verifierChallenge pres hVer
    exact verifyBlindVcPresentation_enforces_guards hVer
  · intro profile stmt issuerRootTag verifierChallenge wit hValid proverCoins
    exact (proveBlindVcPresentation_verifies H prgExpand profile stmt issuerRootTag verifierChallenge wit hValid proverCoins).2
  · intro presNonce schema issuerEpoch treeDepth accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx
      o0 o1 o2 hR1_01 hR1_12 hV0 hV1 hV2
    exact verifyOpenedBlindVcRep_extract3_from_rewound hHLen hR1_01 hR1_12 hV0 hV1 hV2
  · refine ⟨?_, zkSoundnessProfile_rom_vs_qrom_bounds.1, zkSoundnessProfile_rom_vs_qrom_bounds.2.1,
      zkSoundnessProfile_rom_vs_qrom_bounds.2.2.2.1, zkSoundnessProfile_rom_vs_qrom_bounds.2.2.2.2.1,
      zkSoundnessProfile_rom_vs_qrom_bounds.2.2.2.2.2⟩
    intro bad
    rcases fin3_eq_012 bad with rfl | rfl | rfl <;> decide
  · intro R stmt wit₁ wit₂ hV1 hV2 chals rands₁ r
    exact zkMultiRepViewEquiv_indistinguishable H prgExpand R stmt wit₁ wit₂ hV1 hV2 chals rands₁ r

/-- **`#tooth` (`tooth_blind_vc_wrong_schema_or_challenge_rejected`, `C0-3` & `C1-2`)**:
    Mutation-sensitivity witness proving that:
    1. Wrong `schemaId` (`pres.schemaId ≠ expectedSchema.schemaId`) deterministically rejects;
    2. Duplicate disclosed index (`pres.disclosedAttrs = [(0, v₁), (0, v₂)]`) deterministically rejects;
    3. Profile downgrade (`pres.openedReps.length = 219` against `.quantum128` requiring `438`) deterministically rejects;
    4. Wrong repetition challenge (`o.e ≠ expectedE`) deterministically rejects `verifyOpenedBlindVcRep`. -/
theorem tooth_blind_vc_wrong_schema_or_challenge_rejected
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (expectedSchema : VcSchema) (treeDepth : Nat) (verifierChallenge : List UInt8) :
    (∀ pres : BlindVcPresentation,
      pres.schemaId ≠ expectedSchema.schemaId →
      verifyBlindVcPresentation H prgExpand .quantum128 expectedSchema treeDepth verifierChallenge pres = false) ∧
    (∀ (pres : BlindVcPresentation) (v₁ v₂ : Goldilocks),
      pres.disclosedAttrs = [(0, v₁), (0, v₂)] →
      verifyBlindVcPresentation H prgExpand .quantum128 expectedSchema treeDepth verifierChallenge pres = false) ∧
    (∀ pres : BlindVcPresentation,
      pres.openedReps.length = ZkSoundnessProfile.classical128.repetitions →
      verifyBlindVcPresentation H prgExpand .quantum128 expectedSchema treeDepth verifierChallenge pres = false) ∧
    (∀ (issuerEpoch : UInt64) (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
       (disclosed : List (Nat × Goldilocks)) (repIdx : Nat) (expectedE : Fin 3) (o : OpenedBlindVcRep),
      o.e ≠ expectedE →
      verifyOpenedBlindVcRep prgExpand expectedSchema issuerEpoch treeDepth
        accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expectedE o = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pres hNe
    unfold verifyBlindVcPresentation
    rw [decide_eq_false hNe]
    rfl
  · intro pres v₁ v₂ hDisc
    unfold verifyBlindVcPresentation
    have hAscFalse : vcCheckDisclosedStrictAsc expectedSchema.arity [(0, v₁), (0, v₂)] = false := by
      unfold vcCheckDisclosedStrictAsc vcCheckDisclosedStrictAscAux
      simp
    rw [hDisc, hAscFalse]
    simp
  · intro pres hLen219
    unfold verifyBlindVcPresentation
    have hNe : pres.openedReps.length ≠ ZkSoundnessProfile.quantum128.repetitions := by
      rw [hLen219]; decide
    rw [decide_eq_false hNe]
    simp
  · intro issuerEpoch accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expectedE o hNe
    unfold verifyOpenedBlindVcRep
    dsimp only
    rw [decide_eq_false hNe]
    rfl

/-- Concrete 32-byte SP 800-185 (`0x04`-delimited) Keccak-f[1600] XOF evaluator:
    on every non-empty domain tag `tag`, `vcKeccakSponge32 (cshake256FramedPreimage tag frames)`
    equals `cshake256FramedBytes tag frames` byte-for-byte (`keccak.rs:291-295`). -/
def vcKeccakSponge32 (pre : List UInt8) : List UInt8 :=
  squeezeXofAux 32 (absorbPadded (padForRate pre 0x04))

theorem vcKeccakSponge32_eq_cshake256FramedBytes {tag : List UInt8} (hNonEmpty : tag ≠ [])
    (frames : List (List UInt8)) :
    vcKeccakSponge32 (cshake256FramedPreimage tag frames) = cshake256FramedBytes tag frames := by
  rw [cshake256FramedBytes_eq_sponge, ite_false_of hNonEmpty]
  rfl

theorem vcKeccakSponge32_length (pre : List UInt8) : (vcKeccakSponge32 pre).length = 32 := by
  unfold vcKeccakSponge32
  exact squeezeXofAux_length 32 _

/-- **Concrete `Quantum128` (`438`-Repetition) Inhabitedness Witness (`blind_vc_presentation_inhabited`,
    fixing `C0-3` & `C1-2`)**:
    Instantiates the full 2-phase Fiat-Shamir prover & verifier over `vcKeccakSponge32`,
    `"QSAG.VC.ZKBOO_R.V1"` `vcExpandPartyCoins`, `ZkSoundnessProfile.quantum128` (`438` repetitions),
    `vcAccumulatorDepth = 20`, and non-empty selective disclosure `[(0, 42)]`
    (with **ZERO** `fun _ _ _ => 0` constant-challenge mocks!). -/
theorem blind_vc_presentation_inhabited :
    ∃ (schema : VcSchema) (pres : BlindVcPresentation),
      schema = ⟨1, 2, by decide, by decide⟩ ∧
      pres.openedReps.length = 438 ∧
      pres.disclosedAttrs = [(0, Goldilocks.ofNat 42)] ∧
      verifyBlindVcPresentation vcKeccakSponge32 vcExpandPartyCoins .quantum128
        schema vcAccumulatorDepth [0xA5, 0x5A] pres = true := by
  let schema : VcSchema := ⟨1, 2, by decide, by decide⟩
  let attrsVec : Vec Goldilocks 2 := .cons (Goldilocks.ofNat 42) (.cons (Goldilocks.ofNat 99) .nil)
  let hb : Lane4 := ⟨Goldilocks.ofNat 7, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let pb : Lane4 := ⟨Goldilocks.ofNat 11, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let mkSteps : Vec (Bool × Lane6) vcAccumulatorDepth := Vec.replicate vcAccumulatorDepth (false, lane6Zero)
  let ac := vcCommitChunks schema attrsVec.toList hb vcAttrCommitTag
  let leaf : Lane6 := state12Rate6 (absorbRate6Sponge3 ac.1 ac.2.1 ac.2.2)
  let pc := vcCommitChunks schema attrsVec.toList pb vcPresCommitTag
  let presCom : Lane6 := state12Rate6 (absorbRate6Sponge3 pc.1 pc.2.1 pc.2.2)
  let scopeLimbs : Lane4 := ⟨Goldilocks.ofNat 3, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let stmt : BlindVcPublicStatement :=
    { schema := schema
      treeDepth := vcAccumulatorDepth
      presNonce := Vec.replicate 32 0x11
      issuerEpoch := 1
      accumulatorRoot := evalVcMerklePathBool 1 0 leaf mkSteps.toList
      presCommit := presCom
      scopeTag := computeVcScopeTag schema.schemaId hb scopeLimbs
      verifierScopeLimbs := scopeLimbs
      disclosedAttrs := [(0, Goldilocks.ofNat 42)] }
  let wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth :=
    { attrs := attrsVec
      holderBlind := hb
      presBlind := pb
      merkleSteps := mkSteps }
  have hValid : BlindVcWitnessValid stmt wit := by
    refine ⟨?_, ?_, ⟨leaf, ?_, rfl⟩, ?_, rfl⟩
    · simp [stmt, schema, vcCheckDisclosedStrictAsc, vcCheckDisclosedStrictAscAux]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hNil
      · simp only [wit, attrsVec, Vec.toList, List.getElem?_cons_zero]
      · cases hNil
    · dsimp only [stmt, wit]
      unfold computeVcPoseidon2Commit
      rw [ite_true_of (Vec.toList_length attrsVec)]
    · dsimp only [stmt, wit]
      unfold computeVcPoseidon2Commit
      rw [ite_true_of (Vec.toList_length attrsVec)]
  let zeroCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth := fun _ =>
    { seeds := fun i => Vec.replicate 32 (UInt8.ofNat (i.val + 1))
      salts := fun i => Vec.replicate 32 (UInt8.ofNat (i.val + 17))
      attrCoins := Vec.replicate 2 (Goldilocks.zero, Goldilocks.zero)
      hbCoins := (lane4Zero, lane4Zero)
      pbCoins := (lane4Zero, lane4Zero)
      mkCoins := Vec.replicate vcAccumulatorDepth ((Goldilocks.zero, Goldilocks.zero), (lane6Zero, lane6Zero)) }
  let pres := proveBlindVcPresentation vcKeccakSponge32 vcExpandPartyCoins .quantum128
    stmt (Vec.replicate 32 0x22) [0xA5, 0x5A] wit zeroCoins
  obtain ⟨hLen, hVer⟩ := proveBlindVcPresentation_verifies vcKeccakSponge32 vcExpandPartyCoins .quantum128
    stmt (Vec.replicate 32 0x22) [0xA5, 0x5A] wit hValid zeroCoins
  exact ⟨schema, pres, rfl, hLen, rfl, hVer⟩


/-! ## Relying-party verification against an authenticated issuer context -/

/-- What the relying party trusts before it sees a presentation. -/
structure BlindVcTrustedContext where
  accumulatorRoot : Lane6
  issuerRootTag : Vec UInt8 32
  issuerEpoch : UInt64
  verifierScopeLimbs : Lane4

/-- Presentation verifier for a relying party. The issuer context is supplied by the
    verifier and compared before any transcript is derived, so a prover cannot present
    membership in a tree of its own making. -/
def verifyBlindVcPresentationTrusted
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (trusted : BlindVcTrustedContext)
    (expectedSchema : VcSchema) (treeDepth : Nat)
    (verifierChallenge : List UInt8)
    (pres : BlindVcPresentation) : Bool :=
  decide (pres.accumulatorRoot = trusted.accumulatorRoot ∧
    pres.issuerRootTag = trusted.issuerRootTag ∧
    pres.issuerEpoch = trusted.issuerEpoch ∧
    pres.verifierScopeLimbs = trusted.verifierScopeLimbs) &&
  verifyBlindVcPresentation H prgExpand profile expectedSchema treeDepth verifierChallenge pres

/-- An accepted presentation carries exactly the trusted context and satisfies the relation
    verifier, so every soundness statement about `verifyBlindVcPresentation` applies to it
    with the verifier's own root, issuer tag, epoch and scope. -/
theorem verifyBlindVcPresentationTrusted_context
    {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {profile : ZkSoundnessProfile} {trusted : BlindVcTrustedContext}
    {expectedSchema : VcSchema} {treeDepth : Nat} {verifierChallenge : List UInt8}
    {pres : BlindVcPresentation}
    (h : verifyBlindVcPresentationTrusted H prgExpand profile trusted expectedSchema treeDepth
      verifierChallenge pres = true) :
    pres.accumulatorRoot = trusted.accumulatorRoot ∧
    pres.issuerRootTag = trusted.issuerRootTag ∧
    pres.issuerEpoch = trusted.issuerEpoch ∧
    pres.verifierScopeLimbs = trusted.verifierScopeLimbs ∧
    verifyBlindVcPresentation H prgExpand profile expectedSchema treeDepth
      verifierChallenge pres = true := by
  unfold verifyBlindVcPresentationTrusted at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := of_decide_eq_true h.1
  exact ⟨h1, h2, h3, h4, h.2⟩

/-- A presentation built over any other accumulator root is rejected, whatever proof it
    carries. -/
theorem tooth_verifyBlindVcPresentationTrusted_foreign_root
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile) (trusted : BlindVcTrustedContext)
    (expectedSchema : VcSchema) (treeDepth : Nat) (verifierChallenge : List UInt8)
    (pres : BlindVcPresentation)
    (hRoot : pres.accumulatorRoot ≠ trusted.accumulatorRoot) :
    verifyBlindVcPresentationTrusted H prgExpand profile trusted expectedSchema treeDepth
      verifierChallenge pres = false := by
  cases h : verifyBlindVcPresentationTrusted H prgExpand profile trusted expectedSchema
      treeDepth verifierChallenge pres with
  | false => rfl
  | true => exact False.elim (hRoot (verifyBlindVcPresentationTrusted_context h).1)

/-- The honest prover is accepted under the context of its own public statement. -/
theorem proveBlindVcPresentation_verifies_trusted
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (stmt : BlindVcPublicStatement)
    (issuerRootTag : Vec UInt8 32)
    (verifierChallenge : List UInt8)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    verifyBlindVcPresentationTrusted H prgExpand profile
      ⟨stmt.accumulatorRoot, issuerRootTag, stmt.issuerEpoch, stmt.verifierScopeLimbs⟩
      stmt.schema stmt.treeDepth verifierChallenge
      (proveBlindVcPresentation H prgExpand profile stmt issuerRootTag verifierChallenge wit
        proverCoins) = true := by
  obtain ⟨_, hVer⟩ := proveBlindVcPresentation_verifies H prgExpand profile stmt issuerRootTag
    verifierChallenge wit hValid proverCoins
  unfold verifyBlindVcPresentationTrusted
  rw [hVer, Bool.and_true]
  exact decide_eq_true ⟨rfl, rfl, rfl, rfl⟩


/-! ## Checked transform and serialization boundaries

The generic helpers imported from `AdvancedMpcAndCreds` are not used below. In particular,
interpolation uses the proved inverse NTT, and LDE length is the source length times blowup.
-/

structure CosetDomain204 where
  blowup : Nat
  shift : Fq204
  root : Fq204

def cosetDomain204Valid (d : CosetDomain204) : Bool :=
  decide (0 < d.blowup) && decide (d.shift ≠ Fq204.zero) &&
  decide (Fq204.pow d.root (256 * d.blowup) = Fq204.one) &&
  decide (((List.range (256 * d.blowup)).map (Fq204.pow d.root)).Nodup)

/-- Interpolate the source NTT evaluations, then evaluate on the validated multiplicative coset.
    Duplicate domain points, zero shift, and zero blowup are rejected. -/
def cosetLde204 (d : CosetDomain204) (evals : Poly256) : Option (List Fq204) :=
  if cosetDomain204Valid d then
    some ((List.range (256 * d.blowup)).map (fun i =>
      evalPoly204 (PolyTree.toList (fips204InvNtt evals))
        (Fq204.mul d.shift (Fq204.pow d.root i))))
  else none

theorem cosetLde204_size {d : CosetDomain204} {evals : Poly256} {out : List Fq204}
    (h : cosetLde204 d evals = some out) :
    out.length = (PolyTree.toList evals).length * d.blowup := by
  unfold cosetLde204 at h
  split at h
  · cases h
    simp only [List.length_map, List.length_range, PolyTree.length_toList]
  · cases h

theorem cosetLde204_ntt (d : CosetDomain204) (p : Poly256)
    (h : cosetDomain204Valid d = true) :
    cosetLde204 d (fips204Ntt p) = some
      ((List.range (256 * d.blowup)).map (fun i =>
        evalPoly204 (PolyTree.toList p) (Fq204.mul d.shift (Fq204.pow d.root i)))) := by
  simp only [cosetLde204, h, ↓reduceIte, fips204InvNtt_ntt]

/-- No power `ζ^d` with `0 < d < 512` has residue `1`: one modular power per exponent. -/
private theorem mldsaZeta_pow_ne_one_check :
    (List.range 512).all (fun d => d == 0 || 1753 ^ d % mldsaQ != 1) = true := by
  decide +kernel

/-- The first 512 powers of `ζ = 1753` are pairwise distinct: `ζ^i = ζ^j` with `i < j < 512`
    gives `ζ^(j-i) = 1` after cancelling `ζ^i` against `ζ^(512-i)`. -/
private theorem mldsaZeta_pow_ne_of_lt {i j : Nat} (hij : i < j) (hj : j < 512) :
    Fq204.pow mldsaZeta i ≠ Fq204.pow mldsaZeta j := by
  intro hEq
  have hInv : Fq204.mul (Fq204.pow mldsaZeta (512 - i)) (Fq204.pow mldsaZeta i) = Fq204.one := by
    rw [← Fq204.pow_add, Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_trans hij hj)),
      mldsaZeta_pow512_eq_one]
  have hOne : Fq204.pow mldsaZeta (j - i) = Fq204.one := by
    rw [← Fq204.one_mul (Fq204.pow mldsaZeta (j - i)), ← hInv, Fq204.mul_assoc, ← Fq204.pow_add,
      Nat.add_sub_of_le (Nat.le_of_lt hij), ← hEq, hInv]
  have hVal : 1753 ^ (j - i) % mldsaQ = 1 :=
    (Fq204.pow_val mldsaZeta (j - i)).symm.trans (congrArg Fq204.val hOne)
  have hChk : ((j - i) == 0 || 1753 ^ (j - i) % mldsaQ != 1) = true :=
    List.all_eq_true.mp mldsaZeta_pow_ne_one_check (j - i)
      (List.mem_range.mpr (Nat.lt_of_le_of_lt (Nat.sub_le j i) hj))
  rcases Bool.or_eq_true_iff.mp hChk with h0 | hne
  · exact Nat.sub_ne_zero_of_lt hij (beq_iff_eq.mp h0)
  · exact bne_iff_ne.mp hne hVal

private theorem mldsaZeta_pow_injOn {i j : Nat} (hi : i < 512) (hj : j < 512) (hne : i ≠ j) :
    Fq204.pow mldsaZeta i ≠ Fq204.pow mldsaZeta j := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact mldsaZeta_pow_ne_of_lt h hj
  · exact fun hEq => mldsaZeta_pow_ne_of_lt h hi hEq.symm

/-- The four validity conditions, stated as propositions about an arbitrary domain. -/
theorem cosetDomain204Valid_of {d : CosetDomain204}
    (hBlowup : 0 < d.blowup) (hShift : d.shift ≠ Fq204.zero)
    (hRoot : Fq204.pow d.root (256 * d.blowup) = Fq204.one)
    (hNodup : ((List.range (256 * d.blowup)).map (Fq204.pow d.root)).Nodup) :
    cosetDomain204Valid d = true := by
  unfold cosetDomain204Valid
  rw [decide_eq_true hBlowup, decide_eq_true hShift, decide_eq_true hRoot, decide_eq_true hNodup]
  rfl

/-- A valid blowup-2 domain exists: the 512th root of unity `1753` with coset shift `7`.
    All 512 domain points are distinct. -/
theorem cosetDomain204_inhabited :
    cosetDomain204Valid ⟨2, Fq204.ofNat 7, mldsaZeta⟩ = true :=
  cosetDomain204Valid_of (by decide) (by decide) mldsaZeta_pow512_eq_one
    (List.pairwise_map.mpr (List.Pairwise.imp_of_mem
      (fun hi hj hne => mldsaZeta_pow_injOn (List.mem_range.mp hi) (List.mem_range.mp hj) hne)
      (Constructive.nodup_range 512)))

theorem tooth_cosetLde204_zero_shift (d : CosetDomain204) (p : Poly256)
    (h : d.shift = Fq204.zero) : cosetLde204 d p = none := by
  simp [cosetLde204, cosetDomain204Valid, h]

/-- Raw-input boundary: unlike a saturating natural subtraction, this rejects every `v ≥ q`. -/
def canonicalNorm204 (bound : Nat) (coeffs : List Nat) : Bool :=
  coeffs.all (fun v => decide (v < mldsaQ ∧ min v (mldsaQ - v) < bound))

theorem canonicalNorm204_sound {b : Nat} {xs : List Nat}
    (h : canonicalNorm204 b xs = true) :
    ∀ v ∈ xs, v < mldsaQ ∧ min v (mldsaQ - v) < b := by
  simpa only [canonicalNorm204, List.all_eq_true, decide_eq_true_eq] using h

theorem tooth_canonicalNorm204_rejects_q : canonicalNorm204 1 [mldsaQ] = false := by
  decide

theorem tooth_canonicalNorm204_noncanonical (v b : Nat) (h : mldsaQ ≤ v) :
    canonicalNorm204 b [v] = false := by
  have hn : ¬ v < mldsaQ := by omega
  simp [canonicalNorm204, hn]

/-- Bounded byte strings are mandatory at the four-byte framing boundary. -/
structure Frame204 where
  bytes : List UInt8
  bounded : bytes.length < 2 ^ 32

def merkleLeafPreimage204 (leaf : Frame204) : List UInt8 :=
  [0] ++ frameBytes leaf.bytes

def merkleNodePreimage204 (left right : Frame204) : List UInt8 :=
  [1] ++ frameBytes left.bytes ++ frameBytes right.bytes

theorem merkleLeafPreimage204_injective {a b : Frame204}
    (h : merkleLeafPreimage204 a = merkleLeafPreimage204 b) : a.bytes = b.bytes := by
  apply FramedBytesCodec.frameBytes_injective a.bounded b.bounded
  exact List.append_cancel_left h

theorem merkleNodePreimage204_injective {a b c d : Frame204}
    (h : merkleNodePreimage204 a b = merkleNodePreimage204 c d) :
    a.bytes = c.bytes ∧ b.bytes = d.bytes := by
  have hp := congrArg List.tail h
  change frameBytes a.bytes ++ frameBytes b.bytes =
    frameBytes c.bytes ++ frameBytes d.bytes at hp
  obtain ⟨hl, hr⟩ := (FramedBytesCodec.prefix_free_injective a.bounded c.bounded).mp hp
  exact ⟨hl, FramedBytesCodec.frameBytes_injective b.bounded d.bounded hr⟩

theorem tooth_merkle204_leaf_node_disjoint (a b c : Frame204) :
    merkleLeafPreimage204 a ≠ merkleNodePreimage204 b c := by
  intro h
  have ht := congrArg List.head? h
  change some (0 : UInt8) = some 1 at ht
  cases ht

/-! ## Concrete FIPS 204 byte verifier

The legacy `mldsaVerify` signature is retained for `MirSpecBridge`. The entry point below
fixes SHAKE, matrix expansion, challenge sampling, packing, and strict signature decoding.
Rejection samplers have an explicit byte budget and return failure on exhaustion; no
modulo fallback or padded challenge is accepted. Proving a sufficient budget for every
SHAKE stream is deliberately not assumed.
-/

private def xorRate168204 (s : KState) (block : List UInt8) : KState :=
  let t := xorRate136 s block
  { t with a17 := t.a17 ^^^ loadLe64 block 17,
           a18 := t.a18 ^^^ loadLe64 block 18,
           a19 := t.a19 ^^^ loadLe64 block 19,
           a20 := t.a20 ^^^ loadLe64 block 20 }

private def pad168204 (bytes : List UInt8) : List UInt8 :=
  let count := 168 - bytes.length % 168
  if count = 1 then bytes ++ [0x9f]
  else bytes ++ [0x1f] ++ List.replicate (count - 2) 0 ++ [0x80]

private def absorb168204 : Nat → KState → List UInt8 → KState
  | 0, s, _ => s
  | n + 1, s, bs => absorb168204 n (keccakF1600 (xorRate168204 s (bs.take 168))) (bs.drop 168)

private def rate168Bytes204 (s : KState) : List UInt8 :=
  rateBlockBytes s ++ encodeNatLeBytes 8 s.a17.toNat ++ encodeNatLeBytes 8 s.a18.toNat ++
    encodeNatLeBytes 8 s.a19.toNat ++ encodeNatLeBytes 8 s.a20.toNat

private def squeeze168204 : Nat → Nat → KState → List UInt8
  | 0, _, _ => []
  | n + 1, count, s =>
    if count ≤ 168 then (rate168Bytes204 s).take count
    else rate168Bytes204 s ++ squeeze168204 n (count - 168) (keccakF1600 s)

def shake128Xof204 (count : Nat) (msg : List UInt8) : List UInt8 :=
  let padded := pad168204 msg
  squeeze168204 (count / 168 + 1) count
    (absorb168204 (padded.length / 168) zeroKState padded)

private def readBits204 (bs : List UInt8) (offset width : Nat) : Nat :=
  ((List.range width).map (fun j =>
    (((bs.getD ((offset + j) / 8) 0).toNat / 2 ^ ((offset + j) % 8)) % 2) * 2 ^ j)).sum

private def sampleBall204Aux (signs : Nat) (i : Nat) (cs : List Fq204) :
    List UInt8 → Option Poly256
  | [] => if i = 256 then some (PolyTree.ofList 8 cs) else none
  | b :: bs =>
    if i = 256 then some (PolyTree.ofList 8 cs)
    else if b.toNat ≤ i then
      let next := (cs.set i (cs.getD b.toNat Fq204.zero)).set b.toNat
        (if signs % 2 = 0 then Fq204.one else Fq204.neg Fq204.one)
      sampleBall204Aux (signs / 2) (i + 1) next bs
    else sampleBall204Aux signs i cs bs

def sampleInBall204 (byteBudget : Nat) (seed : List UInt8) : Option Poly256 :=
  let stream := shake256Xof (8 + byteBudget) seed
  sampleBall204Aux (readBits204 stream 0 64) 217 (List.replicate 256 Fq204.zero) (stream.drop 8)

private def rejNtt204Aux : Nat → Nat → List UInt8 → List Fq204 → Option Poly256
  | 0, _, _, _ => none
  | fuel + 1, count, bs, acc =>
    if count = 256 then some (PolyTree.ofList 8 acc.reverse)
    else match bs with
    | b0 :: b1 :: b2 :: rest =>
      let v := b0.toNat + 256 * b1.toNat + 65536 * (b2.toNat % 128)
      if hv : v < mldsaQ then rejNtt204Aux fuel (count + 1) rest (⟨v, hv⟩ :: acc)
      else rejNtt204Aux fuel count rest acc
    | _ => none

def expandA204 (byteBudget : Nat) (rho : List UInt8) : Option PolyMat4 := do
  if rho.length ≠ 32 then none else do
    let entries ← (List.range 16).mapM (fun ij =>
      rejNtt204Aux (byteBudget + 1) 0
        (shake128Xof204 byteBudget (rho ++ [UInt8.ofNat (ij % 4), UInt8.ofNat (ij / 4)])) [])
    pure (fun i j => fips204InvNtt (entries.getD (4 * i.val + j.val) (PolyTree.zero 8)))

private def hintTree204 : (d : Nat) → List Bool → HintTree d
  | 0, bs => .leaf (bs.headD false)
  | d + 1, bs => .branch (hintTree204 d (bs.take (2 ^ d))) (hintTree204 d (bs.drop (2 ^ d)))

private def decodeHintRows204 (bytes : List UInt8) : Nat → Nat → Nat → Option (List (HintTree 8))
  | 0, _, start =>
    if (bytes.drop start |>.take (80 - start)).all (fun b => b == 0) then some [] else none
  | n + 1, row, start => do
    let stop := (bytes.getD (80 + row) 0).toNat
    if stop < start ∨ 80 < stop then none else do
      let indices := (bytes.drop start |>.take (stop - start)).map UInt8.toNat
      if ¬ indices.Pairwise (· < ·) then none else do
        let rest ← decodeHintRows204 bytes n (row + 1) stop
        pure (hintTree204 8 ((List.range 256).map (fun j => decide (j ∈ indices))) :: rest)

structure DecodedSignature204 where
  challenge : List UInt8
  z : PolyVec4
  hints : Fin 4 → HintTree 8

def decodeSignature204 (sig : List UInt8) : Option DecodedSignature204 := do
  if sig.length ≠ 2420 then none else do
    let hs ← decodeHintRows204 (sig.drop 2336) 4 0 0
    pure
      { challenge := sig.take 32
        z := fun i => PolyTree.ofList 8 ((List.range 256).map (fun j =>
          Fq204.ofInt (131072 - Int.ofNat (readBits204 sig (256 + i.val * 4608 + 18 * j) 18))))
        hints := fun i => hs.getD i.val (hintTree204 8 []) }

/-- Standalone, pure ML-DSA-44 verifier on wire bytes. Budget exhaustion fails closed.
    `t1` is decoded as ten-bit unsigned coefficients and scaled by `2^13` exactly once. -/
def mldsaVerifyBytes204 (byteBudget : Nat) (pk msg ctx sig : List UInt8) : Bool :=
  if pk.length ≠ 1312 ∨ 255 < ctx.length then false else
  match expandA204 byteBudget (pk.take 32), decodeSignature204 sig with
  | some A, some decoded =>
    match sampleInBall204 byteBudget decoded.challenge with
    | none => false
    | some c =>
      let t1Scaled : PolyVec4 := fun i => PolyTree.ofList 8 ((List.range 256).map (fun j =>
        Fq204.ofNat (8192 * readBits204 pk (256 + i.val * 2560 + 10 * j) 10)))
      let mu := shake256Xof 64 (shake256Xof 64 pk ++ [0, UInt8.ofNat ctx.length] ++ ctx ++ msg)
      mldsaVerify mldsa44ChallengeHash (fun _ => c) A t1Scaled mu
        decoded.challenge decoded.z decoded.hints
  | _, _ => false

theorem tooth_mldsaVerifyBytes204_bad_key_length (fuel : Nat) (pk msg ctx sig : List UInt8)
    (h : pk.length ≠ 1312) : mldsaVerifyBytes204 fuel pk msg ctx sig = false := by
  simp [mldsaVerifyBytes204, h]

theorem tooth_decodeSignature204_bad_length (sig : List UInt8) (h : sig.length ≠ 2420) :
    decodeSignature204 sig = none := by
  simp [decodeSignature204, h]


/-! ## Transcript-computed multiplication check

The signing transition below does not receive a success flag. It receives, for every
multiplication it consumes, a list of gates in the NTT domain together with one sacrificial
triple per gate, and computes the verdict from the three values each gate opens. Operands
and products are base-field elements; the challenge and the triple masks are extension
elements, and extension elements are only ever scaled by base-field elements. Uniqueness of
the bad challenge therefore needs only inversion in the base field.

The opened pair `(rho, sigma)` is a bijective image of the triple masks `(a, b)`; `tau` is
zero in every honest execution. The engine's recursive inner-product compression of the same
check additionally multiplies extension elements and so relies on the extension modulus being
irreducible, which the numeric certificate above does not prove. Per-party share views and
the MAC layer are not modelled: the gate values here are the reconstructed ones.
-/

/-- One checked multiplication `z = x * y` with its sacrificial triple `(a, b, c)`. -/
structure SacGate204 where
  x : Fq204
  y : Fq204
  z : Fq204
  a : Ext6Fq204
  b : Fq204
  c : Ext6Fq204

/-- The values opened for one gate. -/
structure SacOpening204 where
  rho : Ext6Fq204
  sigma : Fq204
  tau : Ext6Fq204

def sacOpen204 (chi : Ext6Fq204) (g : SacGate204) : SacOpening204 :=
  { rho := ext6Sub (ext6Scale chi g.x) g.a
    sigma := Fq204.sub g.y g.b
    tau :=
      ext6Sub
        (ext6Sub (ext6Sub (ext6Scale chi g.z) g.c) (ext6Scale g.a (Fq204.sub g.y g.b)))
        (ext6Scale (ext6Sub (ext6Scale chi g.x) g.a) (Fq204.add g.b (Fq204.sub g.y g.b))) }

def sacVerdict204 (o : SacOpening204) : Bool := decide (o.tau = ext6Zero)

def sacAccept204 (chi : Ext6Fq204) (g : SacGate204) : Bool := sacVerdict204 (sacOpen204 chi g)

def sacGateError204 (g : SacGate204) : Fq204 := Fq204.sub g.z (Fq204.mul g.x g.y)

def sacTripleError204 (g : SacGate204) : Ext6Fq204 := ext6Sub g.c (ext6Scale g.a g.b)

/-- The single challenge under which a gate with multiplication error `d ≠ 0` is accepted. -/
def sacBadChallenge204 (g : SacGate204) : Ext6Fq204 :=
  ext6Scale (sacTripleError204 g) (Fq204.inv (sacGateError204 g))

private theorem sac_coord204 (k x y z a b c : Fq204) :
    Fq204.sub (Fq204.sub (Fq204.sub (Fq204.mul k z) c) (Fq204.mul a (Fq204.sub y b)))
        (Fq204.mul (Fq204.sub (Fq204.mul k x) a) (Fq204.add b (Fq204.sub y b))) =
      Fq204.sub (Fq204.mul k (Fq204.sub z (Fq204.mul x y))) (Fq204.sub c (Fq204.mul a b)) := by
  rw [← Fq204.ofInt_nat k, ← Fq204.ofInt_nat x, ← Fq204.ofInt_nat y, ← Fq204.ofInt_nat z,
    ← Fq204.ofInt_nat a, ← Fq204.ofInt_nat b, ← Fq204.ofInt_nat c]
  simp only [Fq204.ofInt_mul, Fq204.ofInt_sub, Fq204.ofInt_add]
  congr 1
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_add, ← Int.mul_assoc]
  omega

private theorem fq204_eq_of_sub_eq_zero {a b : Fq204} (h : Fq204.sub a b = Fq204.zero) : a = b := by
  have hc := fq204_sub_add_cancel_left b a
  rw [h, Fq204.add_zero] at hc
  exact hc.symm

private theorem fq204_sub_self (a : Fq204) : Fq204.sub a a = Fq204.zero := by
  rw [Fq204.sub_eq_add_neg, Fq204.add_right_neg]

private theorem fq204_sub_sub_self (t r : Fq204) : Fq204.sub t (Fq204.sub t r) = r := by
  rw [← Fq204.ofInt_nat t, ← Fq204.ofInt_nat r]
  simp only [Fq204.ofInt_sub]
  congr 1
  omega

private theorem ext6_sub_sub_self (t r : Ext6Fq204) : ext6Sub t (ext6Sub t r) = r := by
  rcases t with ⟨t0, t1, t2, t3, t4, t5⟩
  rcases r with ⟨r0, r1, r2, r3, r4, r5⟩
  simp only [ext6Sub, fq204_sub_sub_self]

private theorem sac_solve204 {k d t : Fq204} (hd : d ≠ Fq204.zero)
    (h : Fq204.sub (Fq204.mul k d) t = Fq204.zero) : k = Fq204.mul t (Fq204.inv d) := by
  have he := fq204_eq_of_sub_eq_zero h
  rw [← he, Fq204.mul_assoc, Fq204.mul_inv_cancel hd, Fq204.mul_one]

/-- The opened check value is `chi * (z - x*y) - (c - a*b)`. -/
theorem sacOpen204_tau (chi : Ext6Fq204) (g : SacGate204) :
    (sacOpen204 chi g).tau =
      ext6Sub (ext6Scale chi (sacGateError204 g)) (sacTripleError204 g) := by
  rcases chi with ⟨k0, k1, k2, k3, k4, k5⟩
  rcases g with ⟨x, y, z, ⟨a0, a1, a2, a3, a4, a5⟩, b, ⟨c0, c1, c2, c3, c4, c5⟩⟩
  simp only [sacOpen204, sacGateError204, sacTripleError204, ext6Sub, ext6Scale, sac_coord204]

/-- An accepted gate is a correct multiplication unless the challenge is the one bad value
    determined by the gate. The bad value does not depend on the challenge. -/
theorem sacAccept204_sound {chi : Ext6Fq204} {g : SacGate204}
    (h : sacAccept204 chi g = true) :
    g.z = Fq204.mul g.x g.y ∨ chi = sacBadChallenge204 g := by
  unfold sacAccept204 sacVerdict204 at h
  rw [sacOpen204_tau] at h
  have hTau := of_decide_eq_true h
  if hd : sacGateError204 g = Fq204.zero then
    exact Or.inl (fq204_eq_of_sub_eq_zero hd)
  else
    refine Or.inr ?_
    unfold sacBadChallenge204
    generalize sacGateError204 g = d at hTau hd
    generalize sacTripleError204 g = t at hTau
    rcases chi with ⟨k0, k1, k2, k3, k4, k5⟩
    rcases t with ⟨t0, t1, t2, t3, t4, t5⟩
    simp only [ext6Sub, ext6Scale, ext6Zero, Ext6Fq204.mk.injEq] at hTau ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hTau
    exact ⟨sac_solve204 hd h0, sac_solve204 hd h1, sac_solve204 hd h2,
      sac_solve204 hd h3, sac_solve204 hd h4, sac_solve204 hd h5⟩

/-- A correct gate with a correct triple is accepted under every challenge. -/
theorem sacAccept204_complete (chi : Ext6Fq204) {g : SacGate204}
    (hz : g.z = Fq204.mul g.x g.y) (hc : g.c = ext6Scale g.a g.b) :
    sacAccept204 chi g = true := by
  unfold sacAccept204 sacVerdict204
  rw [sacOpen204_tau]
  apply decide_eq_true
  unfold sacGateError204 sacTripleError204
  rw [hz, hc, fq204_sub_self]
  generalize ext6Scale g.a g.b = t
  rcases chi with ⟨k0, k1, k2, k3, k4, k5⟩
  rcases t with ⟨t0, t1, t2, t3, t4, t5⟩
  simp only [ext6Sub, ext6Scale, ext6Zero, Fq204.mul_zero, fq204_sub_self]

theorem tooth_sacAccept204_rejects_corrupt {chi : Ext6Fq204} {g : SacGate204}
    (hz : g.z ≠ Fq204.mul g.x g.y) (hchi : chi ≠ sacBadChallenge204 g) :
    sacAccept204 chi g = false := by
  cases h : sacAccept204 chi g with
  | false => rfl
  | true =>
    rcases sacAccept204_sound h with hg | hb
    · exact False.elim (hz hg)
    · exact False.elim (hchi hb)

/-- Why the challenge must be sampled after the gate values are fixed: a prover who knows
    the challenge in advance passes the check on a wrong product. -/
theorem sac204_predicted_challenge_accepts_corrupt {g : SacGate204}
    (hd : sacGateError204 g ≠ Fq204.zero) :
    sacAccept204 (sacBadChallenge204 g) g = true := by
  unfold sacAccept204 sacVerdict204
  rw [sacOpen204_tau]
  apply decide_eq_true
  unfold sacBadChallenge204
  generalize sacGateError204 g = d at hd
  generalize sacTripleError204 g = t
  rcases t with ⟨t0, t1, t2, t3, t4, t5⟩
  simp only [ext6Sub, ext6Scale, ext6Zero, Fq204.mul_assoc, Fq204.inv_mul_cancel hd,
    Fq204.mul_one, fq204_sub_self]

/-- For a fixed challenge and fixed operands, the triple masks `(a, b)` and the opened pair
    `(rho, sigma)` determine each other. Uniform masks give a uniform opening. -/
def sacOpeningMaskEquiv204 (chi : Ext6Fq204) (x y : Fq204) :
    SimpleEquiv (Ext6Fq204 × Fq204) (Ext6Fq204 × Fq204) where
  toFun m := (ext6Sub (ext6Scale chi x) m.1, Fq204.sub y m.2)
  invFun o := (ext6Sub (ext6Scale chi x) o.1, Fq204.sub y o.2)
  left_inv m := by
    rcases m with ⟨a, b⟩
    simp only [ext6_sub_sub_self, fq204_sub_sub_self]
  right_inv o := by
    rcases o with ⟨r, s⟩
    simp only [ext6_sub_sub_self, fq204_sub_sub_self]

theorem sacOpen204_masked (chi : Ext6Fq204) (g : SacGate204) :
    ((sacOpen204 chi g).rho, (sacOpen204 chi g).sigma) =
      (sacOpeningMaskEquiv204 chi g.x g.y).toFun (g.a, g.b) := by
  rfl

def sacAcceptAll204 (chi : Ext6Fq204) (gs : List SacGate204) : Bool :=
  gs.all (sacAccept204 chi)

/-- Batch soundness: either every gate is a correct multiplication, or the challenge lies
    in a list of at most `gs.length` values fixed by the gates alone. -/
theorem sacAcceptAll204_sound {chi : Ext6Fq204} :
    ∀ {gs : List SacGate204}, sacAcceptAll204 chi gs = true →
      (∀ g ∈ gs, g.z = Fq204.mul g.x g.y) ∨ chi ∈ gs.map sacBadChallenge204
  | [], _ => Or.inl (fun _ hg => nomatch hg)
  | g :: gs, h => by
    unfold sacAcceptAll204 at h
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases sacAccept204_sound h.1 with hg | hb
    · rcases sacAcceptAll204_sound (gs := gs) h.2 with ht | hb
      · refine Or.inl ?_
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hin
        · exact hg
        · exact ht g' hin
      · exact Or.inr (.tail _ hb)
    · subst hb
      exact Or.inr (.head _)

theorem sacBadChallenges204_length (gs : List SacGate204) :
    (gs.map sacBadChallenge204).length = gs.length :=
  List.length_map _

/-- The 256 NTT-domain slots of a claimed ring product `z = x * y`. -/
def nttSlots204 (x y z : Poly256) : List (Fq204 × Fq204 × Fq204) :=
  (PolyTree.toList (fips204Ntt x)).zip
    ((PolyTree.toList (fips204Ntt y)).zip (PolyTree.toList (fips204Ntt z)))

private theorem zip3_append204 {d : Nat} (p0 p1 q0 q1 r0 r1 : PolyTree d) :
    (PolyTree.toList p0 ++ PolyTree.toList p1).zip
        ((PolyTree.toList q0 ++ PolyTree.toList q1).zip
          (PolyTree.toList r0 ++ PolyTree.toList r1)) =
      (PolyTree.toList p0).zip ((PolyTree.toList q0).zip (PolyTree.toList r0)) ++
        (PolyTree.toList p1).zip ((PolyTree.toList q1).zip (PolyTree.toList r1)) := by
  have hq : (PolyTree.toList q0).length = (PolyTree.toList r0).length := by
    rw [PolyTree.length_toList, PolyTree.length_toList]
  have hp : (PolyTree.toList p0).length =
      ((PolyTree.toList q0).zip (PolyTree.toList r0)).length := by
    rw [List.length_zip, PolyTree.length_toList, PolyTree.length_toList,
      PolyTree.length_toList, Nat.min_self]
  rw [List.zip_append hq, List.zip_append hp]

private theorem pointwiseMul_of_slots204 : ∀ {d : Nat} (p q r : PolyTree d),
    (∀ m ∈ (PolyTree.toList p).zip ((PolyTree.toList q).zip (PolyTree.toList r)),
      m.2.2 = Fq204.mul m.1 m.2.1) → PolyTree.pointwiseMul p q = r
  | 0, .leaf a, .leaf b, .leaf c, h => by
    have hm := h (a, b, c) (.head _)
    simp only [PolyTree.pointwiseMul]
    exact congrArg PolyTree.leaf hm.symm
  | d + 1, .branch p0 p1, .branch q0 q1, .branch r0 r1, h => by
    simp only [PolyTree.toList] at h
    rw [zip3_append204] at h
    simp only [PolyTree.pointwiseMul]
    rw [pointwiseMul_of_slots204 p0 q0 r0 (fun m hm => h m (List.mem_append_left _ hm)),
      pointwiseMul_of_slots204 p1 q1 r1 (fun m hm => h m (List.mem_append_right _ hm))]

private theorem slots_of_pointwiseMul204 : ∀ {d : Nat} (p q : PolyTree d)
    (m : Fq204 × Fq204 × Fq204),
    m ∈ (PolyTree.toList p).zip
      ((PolyTree.toList q).zip (PolyTree.toList (PolyTree.pointwiseMul p q))) →
      m.2.2 = Fq204.mul m.1 m.2.1
  | 0, .leaf a, .leaf b, m, hm => by
    have he : m = (a, b, Fq204.mul a b) := by
      rcases hm with _ | ⟨_, hnil⟩
      · rfl
      · exact nomatch hnil
    rw [he]
  | d + 1, .branch p0 p1, .branch q0 q1, m, hm => by
    simp only [PolyTree.toList, PolyTree.pointwiseMul] at hm
    rw [zip3_append204] at hm
    rcases List.mem_append.mp hm with h0 | h1
    · exact slots_of_pointwiseMul204 p0 q0 m h0
    · exact slots_of_pointwiseMul204 p1 q1 m h1

def sacGateOperands204 (g : SacGate204) : Fq204 × Fq204 × Fq204 := (g.x, g.y, g.z)

/-- The gate list is bound to the polynomials the signer actually consumes. -/
def sacBinds204 (gs : List SacGate204) (x y z : Poly256) : Bool :=
  decide (gs.map sacGateOperands204 = nttSlots204 x y z)

/-- Checked ring product: binding plus the sacrifice verdict over all 256 slots. -/
def sacProductOk204 (chi : Ext6Fq204) (gs : List SacGate204) (x y z : Poly256) : Bool :=
  sacBinds204 gs x y z && sacAcceptAll204 chi gs

theorem sacPolyProduct204_sound {chi : Ext6Fq204} {gs : List SacGate204} {x y z : Poly256}
    (h : sacProductOk204 chi gs x y z = true) :
    z = negacyclicMul x y ∨ chi ∈ gs.map sacBadChallenge204 := by
  unfold sacProductOk204 at h
  simp only [Bool.and_eq_true] at h
  rcases sacAcceptAll204_sound h.2 with hAll | hBad
  · refine Or.inl ?_
    have hSlots : gs.map sacGateOperands204 = nttSlots204 x y z := of_decide_eq_true h.1
    apply fips204Ntt_injective
    rw [fips204Ntt_negacyclicMul]
    refine (pointwiseMul_of_slots204 _ _ _ ?_).symm
    intro m hm
    have hm' : m ∈ gs.map sacGateOperands204 := by
      rw [hSlots]
      exact hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm'
    exact hAll g hg
  · exact Or.inr hBad

/-- Honest gate list for `z = x * y`, with triple masks `(a, b)` and `c = a * b`. -/
def sacHonestGates204 (a : Ext6Fq204) (b : Fq204) (x y : Poly256) : List SacGate204 :=
  (nttSlots204 x y (negacyclicMul x y)).map
    (fun m => { x := m.1, y := m.2.1, z := m.2.2, a := a, b := b, c := ext6Scale a b })

private theorem map_operands_honest204 (a : Ext6Fq204) (b : Fq204) :
    ∀ ms : List (Fq204 × Fq204 × Fq204),
      (ms.map (fun m =>
        ({ x := m.1, y := m.2.1, z := m.2.2, a := a, b := b, c := ext6Scale a b } : SacGate204))).map
          sacGateOperands204 = ms
  | [] => rfl
  | m :: ms => by
    rw [List.map_cons, List.map_cons, map_operands_honest204 a b ms]
    rfl

theorem sacHonestGates204_ok (chi a : Ext6Fq204) (b : Fq204) (x y : Poly256) :
    sacProductOk204 chi (sacHonestGates204 a b x y) x y (negacyclicMul x y) = true := by
  unfold sacProductOk204
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold sacBinds204 sacHonestGates204
    exact decide_eq_true (map_operands_honest204 a b _)
  · unfold sacAcceptAll204 sacHonestGates204
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
    refine sacAccept204_complete chi ?_ rfl
    have hm' : m ∈ (PolyTree.toList (fips204Ntt x)).zip
        ((PolyTree.toList (fips204Ntt y)).zip
          (PolyTree.toList (PolyTree.pointwiseMul (fips204Ntt x) (fips204Ntt y)))) := by
      rw [← fips204Ntt_negacyclicMul]
      exact hm
    exact slots_of_pointwiseMul204 _ _ m hm'

/-- Sacrifice transcript for the twelve secret-dependent ring products of one signing
    attempt. `w = A * y` is a public-matrix image of the shared nonce and is recomputed. -/
structure RssSacrificeTranscript204 where
  cs1 : Fin 4 → List SacGate204
  cs2 : Fin 4 → List SacGate204
  ct0 : Fin 4 → List SacGate204

/-- Challenges under which some corrupted product of this transcript would be accepted.
    The list is a function of the gate values alone. -/
def rssSacrificeBadChallenges204 (T : RssSacrificeTranscript204) : List Ext6Fq204 :=
  (List.finRange 4).flatMap
    (fun i => (T.cs1 i ++ T.cs2 i ++ T.ct0 i).map sacBadChallenge204)

private def fin4All204 (f : Fin 4 → Bool) : Bool :=
  f ⟨0, by decide⟩ && f ⟨1, by decide⟩ && f ⟨2, by decide⟩ && f ⟨3, by decide⟩

private theorem fin4All204_true {f : Fin 4 → Bool} (h : fin4All204 f = true) :
    ∀ i, f i = true := by
  unfold fin4All204 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  intro i
  rcases i with ⟨idx, hidx⟩
  have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private theorem fin4All204_of_forall {f : Fin 4 → Bool} (h : ∀ i, f i = true) :
    fin4All204 f = true := by
  unfold fin4All204
  simp only [h, Bool.and_self]

def rssSacrificedProductsValid
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) : Bool :=
  polyVec4EqBool inp.products.w (matVecMul4 st.A (rssSumVec4List inp.ySubsets)) &&
  fin4All204 (fun i => sacProductOk204 chi (T.cs1 i)
    (sampleInBall (chalHash inp.mu
      (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
    (rssSumVec4List st.s1Subsets i) (inp.products.cs1 i)) &&
  fin4All204 (fun i => sacProductOk204 chi (T.cs2 i)
    (sampleInBall (chalHash inp.mu
      (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
    (rssSumVec4List st.s2Subsets i) (inp.products.cs2 i)) &&
  fin4All204 (fun i => sacProductOk204 chi (T.ct0 i)
    (sampleInBall (chalHash inp.mu
      (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
    (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets))
      (rssSumVec4List st.s2Subsets)) i) (inp.products.ct0 i))

private theorem sacVec204_sound {chi : Ext6Fq204} {gs : Fin 4 → List SacGate204}
    {c : Poly256} {s p : PolyVec4} {bad : List Ext6Fq204}
    (hbad : ∀ i, ∀ k ∈ (gs i).map sacBadChallenge204, k ∈ bad)
    (h : fin4All204 (fun i => sacProductOk204 chi (gs i) c (s i) (p i)) = true) :
    p = mulPolyVec4 c s ∨ chi ∈ bad := by
  have step : ∀ i : Fin 4, p i = negacyclicMul c (s i) ∨ chi ∈ bad := by
    intro i
    have hok : sacProductOk204 chi (gs i) c (s i) (p i) = true := fin4All204_true h i
    rcases sacPolyProduct204_sound hok with hz | hb
    · exact Or.inl hz
    · exact Or.inr (hbad i _ hb)
  rcases step ⟨0, by decide⟩ with h0 | hb
  · rcases step ⟨1, by decide⟩ with h1 | hb
    · rcases step ⟨2, by decide⟩ with h2 | hb
      · rcases step ⟨3, by decide⟩ with h3 | hb
        · refine Or.inl ?_
          funext i
          rcases i with ⟨idx, hidx⟩
          have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
          rcases hCases with rfl | rfl | rfl | rfl
          · exact h0
          · exact h1
          · exact h2
          · exact h3
        · exact Or.inr hb
      · exact Or.inr hb
    · exact Or.inr hb
  · exact Or.inr hb

/-- The transcript-computed verdict implies the exact product relation, except when the
    challenge is one of the bad values fixed by the transcript. -/
theorem rssSacrificedProductsValid_sound
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (h : rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true) :
    rssProductsValid chalHash sampleInBall st inp = true ∨
      chi ∈ rssSacrificeBadChallenges204 T := by
  unfold rssSacrificedProductsValid at h
  simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff] at h
  obtain ⟨⟨⟨hw, h1⟩, h2⟩, h3⟩ := h
  have b1 : ∀ i, ∀ k ∈ (T.cs1 i).map sacBadChallenge204,
      k ∈ rssSacrificeBadChallenges204 T := fun i k hk =>
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by
      rw [List.map_append, List.map_append]
      exact List.mem_append_left _ (List.mem_append_left _ hk)⟩
  have b2 : ∀ i, ∀ k ∈ (T.cs2 i).map sacBadChallenge204,
      k ∈ rssSacrificeBadChallenges204 T := fun i k hk =>
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by
      rw [List.map_append, List.map_append]
      exact List.mem_append_left _ (List.mem_append_right _ hk)⟩
  have b3 : ∀ i, ∀ k ∈ (T.ct0 i).map sacBadChallenge204,
      k ∈ rssSacrificeBadChallenges204 T := fun i k hk =>
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by
      rw [List.map_append, List.map_append]
      exact List.mem_append_right _ hk⟩
  rcases sacVec204_sound b1 h1 with e1 | hb
  · rcases sacVec204_sound b2 h2 with e2 | hb
    · rcases sacVec204_sound b3 h3 with e3 | hb
      · refine Or.inl ?_
        unfold rssProductsValid
        simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff]
        exact ⟨⟨⟨hw, e1⟩, e2⟩, e3⟩
      · exact Or.inr hb
    · exact Or.inr hb
  · exact Or.inr hb

theorem tooth_rssSacrificedProductsValid_corrupt
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (hbad : inp.products ≠ rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets)
    (hchi : chi ∉ rssSacrificeBadChallenges204 T) :
    rssSacrificedProductsValid chalHash sampleInBall st inp chi T = false := by
  cases h : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
  | false => rfl
  | true =>
    rcases rssSacrificedProductsValid_sound chalHash sampleInBall st inp chi T h with hv | hb
    · exact False.elim (hbad ((rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp hv))
    · exact False.elim (hchi hb)

/-- Honest transcript for an attempt, with triple masks `(a, b)`. -/
def rssHonestSacrifice204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (a : Ext6Fq204) (b : Fq204) : RssSacrificeTranscript204 :=
  { cs1 := fun i => sacHonestGates204 a b
      (sampleInBall (chalHash inp.mu
        (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
      (rssSumVec4List st.s1Subsets i)
    cs2 := fun i => sacHonestGates204 a b
      (sampleInBall (chalHash inp.mu
        (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
      (rssSumVec4List st.s2Subsets i)
    ct0 := fun i => sacHonestGates204 a b
      (sampleInBall (chalHash inp.mu
        (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
      (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets))
        (rssSumVec4List st.s2Subsets)) i) }

/-- The check is satisfiable: correct products with the honest transcript pass under every
    challenge and every choice of triple masks. -/
theorem rssSacrificedProductsValid_complete
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi a : Ext6Fq204) (b : Fq204)
    (hp : inp.products = rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets) :
    rssSacrificedProductsValid chalHash sampleInBall st inp chi
      (rssHonestSacrifice204 chalHash sampleInBall st inp a b) = true := by
  unfold rssSacrificedProductsValid
  rw [hp]
  simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff]
  refine ⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩
  · exact fin4All204_of_forall (fun i => sacHonestGates204_ok chi a b _ _)
  · exact fin4All204_of_forall (fun i => sacHonestGates204_ok chi a b _ _)
  · exact fin4All204_of_forall (fun i => sacHonestGates204_ok chi a b _ _)

/-- Signing transition gated by the transcript-computed verdict. No exact-product oracle
    is consulted: the consumed products are whatever the sacrifice accepted. -/
@[expose] def rssSacrificedSignStep
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason :=
  match decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
  | false => .err st .attemptReplay
  | true =>
    match rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
    | false => .err { st with nextAttempt := st.nextAttempt + 1 } .mpcSacrificeFailed
    | true => rssSignCore chalHash { st with nextAttempt := st.nextAttempt + 1 } inp

theorem rssSacrificedSignStep_eq_of_valid
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (h : rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true)
    (hv : rssProductsValid chalHash sampleInBall st inp = true) :
    rssSacrificedSignStep chalHash sampleInBall st inp chi T =
      rssThresholdSignStep chalHash sampleInBall st inp := by
  unfold rssSacrificedSignStep rssThresholdSignStep
  rw [h, hv]

/-- The sacrificed transition refines the exact-product reference transition, except on the
    bad-challenge event. -/
theorem rssSacrificedSignStep_refines
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (h : rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true) :
    rssSacrificedSignStep chalHash sampleInBall st inp chi T =
        rssThresholdSignStep chalHash sampleInBall st inp ∨
      chi ∈ rssSacrificeBadChallenges204 T := by
  rcases rssSacrificedProductsValid_sound chalHash sampleInBall st inp chi T h with hv | hb
  · exact Or.inl (rssSacrificedSignStep_eq_of_valid chalHash sampleInBall st inp chi T h hv)
  · exact Or.inr hb

private theorem rssSacrificedSignStep_ok_valid
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st st' : RssMlDsaSignerState} {inp : RssMlDsaAttemptInput}
    {chi : Ext6Fq204} {T : RssSacrificeTranscript204}
    {out : RssSignPublicAbortView × Option ThresholdSignSig}
    (hok : rssSacrificedSignStep chalHash sampleInBall st inp chi T = .ok st' out) :
    rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true := by
  cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
  | true => rfl
  | false =>
    unfold rssSacrificedSignStep at hok
    rw [hv] at hok
    cases hg : decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
    | false => rw [hg] at hok; cases hok
    | true => rw [hg] at hok; cases hok

/-- The signature released by a transition outcome, if any. -/
def rssStepReleased204 :
    StepOutcome RssMlDsaSignerState (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason → Option ThresholdSignSig
  | .ok _ out => out.2
  | .err _ _ => none

private theorem mkRssSignAttemptOutcome_released
    (stBurned : RssMlDsaSignerState) (usedAttempt : Nat)
    (cTilde : List UInt8) (w z u maskW maskZ maskLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8) (h : Fin 4 → HintTree 8) (accept : Bool) :
    rssStepReleased204
        (mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept) =
      match accept with
      | true => some { cTilde := cTilde, z := z, h := h, usedAttempt := usedAttempt }
      | false => none := by
  unfold mkRssSignAttemptOutcome
  cases accept <;> rfl

/-- The attempt with its three caller-selected masks replaced. -/
def rssRemask204 (inp : RssMlDsaAttemptInput) (maskW maskZ maskLow : PolyVec4) :
    RssMlDsaAttemptInput :=
  { inp with maskW := maskW, maskZ := maskZ, maskLow := maskLow }

private theorem rssSignCore_released_mask_independent
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (stBurned : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (maskW maskZ maskLow : PolyVec4) :
    rssStepReleased204 (rssSignCore chalHash stBurned (rssRemask204 inp maskW maskZ maskLow)) =
      rssStepReleased204 (rssSignCore chalHash stBurned inp) := by
  unfold rssSignCore
  dsimp only [rssRemask204]
  rw [mkRssSignAttemptOutcome_released, mkRssSignAttemptOutcome_released]

private theorem rssSacrificedSignStep_released
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    rssStepReleased204 (rssSacrificedSignStep chalHash sampleInBall st inp chi T) =
      if (decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) &&
          rssSacrificedProductsValid chalHash sampleInBall st inp chi T) = true then
        rssStepReleased204
          (rssSignCore chalHash { st with nextAttempt := st.nextAttempt + 1 } inp)
      else none := by
  unfold rssSacrificedSignStep
  cases hg : decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
  | false => rfl
  | true =>
    cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
    | false => rfl
    | true => rfl

/-- The released signature does not depend on the masks the caller selected. -/
theorem rssSacrificedSignStep_released_mask_independent
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (maskW maskZ maskLow : PolyVec4) :
    rssStepReleased204 (rssSacrificedSignStep chalHash sampleInBall st
        (rssRemask204 inp maskW maskZ maskLow) chi T) =
      rssStepReleased204 (rssSacrificedSignStep chalHash sampleInBall st inp chi T) := by
  have hc : (decide ((rssRemask204 inp maskW maskZ maskLow).epoch = st.epoch ∧
        (rssRemask204 inp maskW maskZ maskLow).attempt = st.nextAttempt) &&
      rssSacrificedProductsValid chalHash sampleInBall st
        (rssRemask204 inp maskW maskZ maskLow) chi T) =
      (decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) &&
        rssSacrificedProductsValid chalHash sampleInBall st inp chi T) := by
    rfl
  rw [rssSacrificedSignStep_released, rssSacrificedSignStep_released, hc,
    rssSignCore_released_mask_independent]

/-! ## Durable reservation composed with checked signing

The durable record below contains both the existing epoch journal and exact nonce material.
Keeping the material (rather than just an attempt identifier or its hash) makes non-reuse
independent of a hash-collision assumption. A real store must persist both fields atomically.
The disk outcome is an environment event, not a protocol-validation input.
-/

structure RssDurableDisk204 where
  journal : DurableNonceBurnStore
  burnedNonces : List (List UInt8)

structure RssDurableSigner204 where
  key : RssMlDsaSignerState
  disk : RssDurableDisk204

inductive RssDiskOutcome204 where
  | committed
  | failed
  deriving DecidableEq

def rssNonceMaterial204 (inp : RssMlDsaAttemptInput) : List UInt8 :=
  encodePolyVec4Bytes (rssSumVec4List inp.ySubsets)

/-- Reserve before running any check or releasing any signing output. The nonce ledger is
    global to this key, so changing the session, epoch, attempt, or share decomposition does
    not permit reuse of the aggregate nonce. -/
def rssDurableReserve204 (party : UInt16) (diskResult : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput) : Bool × RssDurableSigner204 :=
  if inp.epoch ≠ st.key.epoch ∨ inp.attempt ≠ st.key.nextAttempt ∨
      2 ^ 64 ≤ inp.epoch ∨ 2 ^ 32 ≤ inp.attempt ∨ rssNonceMaterial204 inp ∈ st.disk.burnedNonces then
    (false, st)
  else
    match durableBurnReserve st.disk.journal party (UInt64.ofNat inp.epoch)
        inp.sessionId (UInt32.ofNat inp.attempt) (decide (diskResult = .committed)) with
    | (true, journal) =>
      (true,
        { key := { st.key with
            epoch := st.key.epoch + 1
            nextAttempt := st.key.nextAttempt + 1 }
          disk :=
            { journal := journal
              burnedNonces := rssNonceMaterial204 inp :: st.disk.burnedNonces } })
    | (false, journal) =>
      (false,
        { key := st.key
          disk :=
            { journal := journal
              burnedNonces := st.disk.burnedNonces } })

/-- Only a final signature escapes the durable boundary. Rejected attempts expose neither
    individual norms nor the masked vectors of the reference transition. The reservation is
    evaluated first; the sacrificed transition's output is discarded unless it succeeded. -/
def rssDurableSign204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (diskResult : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    RssDurableSigner204 × Option ThresholdSignSig :=
  ((rssDurableReserve204 party diskResult st inp).2,
    match (rssDurableReserve204 party diskResult st inp).1 with
    | false => none
    | true =>
      rssStepReleased204 (rssSacrificedSignStep chalHash sampleInBall st.key inp chi T))

/-- The durable signer released `sig` for this attempt. -/
def RssDurableReleased204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (diskResult : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig) : Prop :=
  (rssDurableSign204 chalHash sampleInBall party diskResult st inp chi T).2 = some sig

/-- A crash loses volatile memory. The epoch is rebuilt from the journal, the in-epoch
    attempt counter restarts, and the burned-nonce ledger is exactly what was on disk. -/
def rssDurableRecover204 (party : UInt16) (st : RssDurableSigner204) : RssDurableSigner204 :=
  { key := { st.key with
      epoch := persistedNextEpochNat st.disk.journal.keyId party st.disk.journal.burns
      nextAttempt := 0 }
    disk := st.disk }

theorem rssDurableReserve204_burns {party : UInt16} {result : RssDiskOutcome204}
    {st : RssDurableSigner204} {inp : RssMlDsaAttemptInput}
    (h : (rssDurableReserve204 party result st inp).1 = true) :
    (rssDurableReserve204 party result st inp).2.disk.burnedNonces =
      rssNonceMaterial204 inp :: st.disk.burnedNonces := by
  unfold rssDurableReserve204 at h ⊢
  split
  · rename_i hc
    rw [ite_true_of hc] at h
    cases h
  · rename_i hc
    rw [ite_false_of hc] at h
    split
    · rfl
    · rename_i hm
      rw [hm] at h
      cases h

theorem rssDurableReserve204_monotone (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput) :
    ∀ material ∈ st.disk.burnedNonces,
      material ∈ (rssDurableReserve204 party result st inp).2.disk.burnedNonces := by
  intro material hm
  unfold rssDurableReserve204
  split
  · exact hm
  · split
    · exact .tail _ hm
    · exact hm

theorem tooth_rssDurableReserve204_nonce_replay (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (h : rssNonceMaterial204 inp ∈ st.disk.burnedNonces) :
    (rssDurableReserve204 party result st inp).1 = false := by
  unfold rssDurableReserve204
  rw [ite_true_of (Or.inr (Or.inr (Or.inr (Or.inr h))))]

/-- A failed durable write refuses the reservation, whatever the journal contained. -/
theorem rssDurableReserve204_failed_write (party : UInt16)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput) :
    (rssDurableReserve204 party .failed st inp).1 = false := by
  unfold rssDurableReserve204
  split
  · rfl
  · have hw := durableBurnReserve_failed_write st.disk.journal party (UInt64.ofNat inp.epoch)
      inp.sessionId (UInt32.ofNat inp.attempt)
    have hd : decide (RssDiskOutcome204.failed = RssDiskOutcome204.committed) = false := by decide
    rw [hd]
    split
    · rename_i hm
      rw [hm] at hw
      cases hw
    · rfl

/-- The durable state returned by signing is exactly the state committed by reservation. -/
theorem rssDurableSign204_state
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    (rssDurableSign204 chalHash sampleInBall party result st inp chi T).1 =
      (rssDurableReserve204 party result st inp).2 := by
  rfl

/-- No reservation, no output: a refused reservation releases nothing. -/
theorem rssDurableSign204_none_of_refused
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (h : (rssDurableReserve204 party result st inp).1 = false) :
    (rssDurableSign204 chalHash sampleInBall party result st inp chi T).2 = none := by
  unfold rssDurableSign204
  dsimp only
  rw [h]

theorem rssDurableSign204_reserved_of_release
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig)
    (h : RssDurableReleased204 chalHash sampleInBall party result st inp chi T sig) :
    (rssDurableReserve204 party result st inp).1 = true := by
  cases hr : (rssDurableReserve204 party result st inp).1 with
  | true => rfl
  | false =>
    unfold RssDurableReleased204 at h
    rw [rssDurableSign204_none_of_refused chalHash sampleInBall party result st inp chi T hr] at h
    cases h

theorem rssDurableSign204_release_burned
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig)
    (h : RssDurableReleased204 chalHash sampleInBall party result st inp chi T sig) :
    rssNonceMaterial204 inp ∈
      (rssDurableSign204 chalHash sampleInBall party result st inp chi T).1.disk.burnedNonces := by
  rw [rssDurableSign204_state,
    rssDurableReserve204_burns
      (rssDurableSign204_reserved_of_release chalHash sampleInBall party result st inp chi T sig h)]
  exact .head _

/-- Every released signature verifies under the signer's public key, unless the sacrifice
    challenge is one of the bad values fixed by the transcript. -/
theorem rssDurableSign204_release_verifies
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig)
    (h : RssDurableReleased204 chalHash sampleInBall party result st inp chi T sig) :
    mldsaVerify chalHash sampleInBall st.key.A
        (power2RoundHighVec4 (addVec4 (matVecMul4 st.key.A (rssSumVec4List st.key.s1Subsets))
          (rssSumVec4List st.key.s2Subsets)))
        inp.mu sig.cTilde sig.z sig.h = true ∨
      chi ∈ rssSacrificeBadChallenges204 T := by
  have hres := rssDurableSign204_reserved_of_release chalHash sampleInBall party result st inp chi T sig h
  unfold RssDurableReleased204 rssDurableSign204 at h
  dsimp only at h
  rw [hres] at h
  dsimp only at h
  cases hstep : rssSacrificedSignStep chalHash sampleInBall st.key inp chi T with
  | err next reason => rw [hstep] at h; cases h
  | ok next out =>
    rw [hstep] at h
    rcases out with ⟨view, msig⟩
    have hsig : msig = some sig := h
    subst hsig
    rcases rssSacrificedSignStep_refines chalHash sampleInBall st.key inp chi T
        (rssSacrificedSignStep_ok_valid hstep) with heq | hb
    · rw [heq] at hstep
      exact Or.inl ((rssThresholdSignStep_ok_meta hstep).2.2.2.2.2 sig rfl).2.2
    · exact Or.inr hb

/-- The released value does not depend on the masks the caller selected, so a zero or
    otherwise chosen mask cannot move information across the durable boundary. -/
theorem rssDurableSign204_mask_independent
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (maskW maskZ maskLow : PolyVec4) :
    (rssDurableSign204 chalHash sampleInBall party result st
        (rssRemask204 inp maskW maskZ maskLow) chi T).2 =
      (rssDurableSign204 chalHash sampleInBall party result st inp chi T).2 := by
  have hr : rssDurableReserve204 party result st (rssRemask204 inp maskW maskZ maskLow) =
      rssDurableReserve204 party result st inp := by
    rfl
  unfold rssDurableSign204
  dsimp only
  rw [hr, rssSacrificedSignStep_released_mask_independent]

theorem rssDurableRecover204_preserves_burns (party : UInt16) (st : RssDurableSigner204) :
    (rssDurableRecover204 party st).disk = st.disk := by
  rfl

theorem tooth_rssDurableSign204_failed_write
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    (rssDurableSign204 chalHash sampleInBall party .failed st inp chi T).2 = none :=
  rssDurableSign204_none_of_refused chalHash sampleInBall party .failed st inp chi T
    (rssDurableReserve204_failed_write party st inp)

inductive RssDurableTransition204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) (party : UInt16) :
    RssDurableSigner204 → RssDurableSigner204 → Prop where
  | sign (st : RssDurableSigner204) (result : RssDiskOutcome204) (inp : RssMlDsaAttemptInput)
      (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
      RssDurableTransition204 chalHash sampleInBall party st
        (rssDurableSign204 chalHash sampleInBall party result st inp chi T).1
  | crash (st : RssDurableSigner204) :
      RssDurableTransition204 chalHash sampleInBall party st (rssDurableRecover204 party st)

inductive RssDurableTrace204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) (party : UInt16) :
    RssDurableSigner204 → RssDurableSigner204 → Prop where
  | nil (st : RssDurableSigner204) : RssDurableTrace204 chalHash sampleInBall party st st
  | cons {a b c : RssDurableSigner204} :
      RssDurableTransition204 chalHash sampleInBall party a b →
      RssDurableTrace204 chalHash sampleInBall party b c →
      RssDurableTrace204 chalHash sampleInBall party a c

theorem rssDurableTransition204_monotone
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16} {a b : RssDurableSigner204}
    (h : RssDurableTransition204 chalHash sampleInBall party a b) :
    ∀ material ∈ a.disk.burnedNonces, material ∈ b.disk.burnedNonces := by
  intro material hm
  cases h with
  | sign result inp chi T =>
    rw [rssDurableSign204_state]
    exact rssDurableReserve204_monotone party result a inp material hm
  | crash => exact hm

theorem rssDurableTrace204_monotone
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16} {a b : RssDurableSigner204}
    (h : RssDurableTrace204 chalHash sampleInBall party a b) :
    ∀ material ∈ a.disk.burnedNonces, material ∈ b.disk.burnedNonces := by
  induction h with
  | nil => exact fun _ hm => hm
  | cons step _ ih =>
    intro material hm
    exact ih material (rssDurableTransition204_monotone step material hm)

/-- Replay remains rejected after any number of intervening signs, failures, and crashes. -/
theorem tooth_rssDurableTrace204_replay
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16} {a b : RssDurableSigner204}
    (h : RssDurableTrace204 chalHash sampleInBall party a b)
    (inp : RssMlDsaAttemptInput) (result : RssDiskOutcome204)
    (hb : rssNonceMaterial204 inp ∈ a.disk.burnedNonces) :
    (rssDurableReserve204 party result b inp).1 = false :=
  tooth_rssDurableReserve204_nonce_replay party result b inp (rssDurableTrace204_monotone h _ hb)

/-- Two signatures released anywhere along one durable execution, with arbitrary signing
    attempts, failed writes and crashes in between, never share an aggregate nonce. The
    session, epoch, attempt and share decomposition of the second attempt are unconstrained. -/
theorem rssDurable204_released_nonces_distinct
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16}
    {a b : RssDurableSigner204} {r₁ r₂ : RssDiskOutcome204}
    {inp₁ inp₂ : RssMlDsaAttemptInput} {chi₁ chi₂ : Ext6Fq204}
    {T₁ T₂ : RssSacrificeTranscript204} {sig₁ sig₂ : ThresholdSignSig}
    (h₁ : RssDurableReleased204 chalHash sampleInBall party r₁ a inp₁ chi₁ T₁ sig₁)
    (htr : RssDurableTrace204 chalHash sampleInBall party
      (rssDurableSign204 chalHash sampleInBall party r₁ a inp₁ chi₁ T₁).1 b)
    (h₂ : RssDurableReleased204 chalHash sampleInBall party r₂ b inp₂ chi₂ T₂ sig₂) :
    rssSumVec4List inp₁.ySubsets ≠ rssSumVec4List inp₂.ySubsets := by
  intro hEq
  have hBurned := rssDurableTrace204_monotone htr _
    (rssDurableSign204_release_burned chalHash sampleInBall party r₁ a inp₁ chi₁ T₁ sig₁ h₁)
  have hMat : rssNonceMaterial204 inp₂ = rssNonceMaterial204 inp₁ := by
    unfold rssNonceMaterial204
    rw [hEq]
  have hRefused := tooth_rssDurableReserve204_nonce_replay party r₂ b inp₂ (hMat ▸ hBurned)
  unfold RssDurableReleased204 at h₂
  rw [rssDurableSign204_none_of_refused chalHash sampleInBall party r₂ b inp₂ chi₂ T₂ hRefused] at h₂
  cases h₂

/-- The same nonce is also refused when it is offered again after any execution. -/
theorem tooth_rssDurable204_reuse_after_release
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16}
    {a b : RssDurableSigner204} {r₁ r₂ : RssDiskOutcome204}
    {inp₁ inp₂ : RssMlDsaAttemptInput} {chi₁ chi₂ : Ext6Fq204}
    {T₁ T₂ : RssSacrificeTranscript204} {sig₁ : ThresholdSignSig}
    (h₁ : RssDurableReleased204 chalHash sampleInBall party r₁ a inp₁ chi₁ T₁ sig₁)
    (htr : RssDurableTrace204 chalHash sampleInBall party
      (rssDurableSign204 chalHash sampleInBall party r₁ a inp₁ chi₁ T₁).1 b)
    (hEq : rssSumVec4List inp₂.ySubsets = rssSumVec4List inp₁.ySubsets) :
    (rssDurableSign204 chalHash sampleInBall party r₂ b inp₂ chi₂ T₂).2 = none := by
  have hBurned := rssDurableTrace204_monotone htr _
    (rssDurableSign204_release_burned chalHash sampleInBall party r₁ a inp₁ chi₁ T₁ sig₁ h₁)
  have hMat : rssNonceMaterial204 inp₂ = rssNonceMaterial204 inp₁ := by
    unfold rssNonceMaterial204
    rw [hEq]
  exact rssDurableSign204_none_of_refused chalHash sampleInBall party r₂ b inp₂ chi₂ T₂
    (tooth_rssDurableReserve204_nonce_replay party r₂ b inp₂ (hMat ▸ hBurned))

private theorem rssDurableReserve204_ok_of {party : UInt16} {result : RssDiskOutcome204}
    {st : RssDurableSigner204} {inp : RssMlDsaAttemptInput}
    (hc : ¬ (inp.epoch ≠ st.key.epoch ∨ inp.attempt ≠ st.key.nextAttempt ∨
      2 ^ 64 ≤ inp.epoch ∨ 2 ^ 32 ≤ inp.attempt ∨
      rssNonceMaterial204 inp ∈ st.disk.burnedNonces))
    (hr : (durableBurnReserve st.disk.journal party (UInt64.ofNat inp.epoch)
      inp.sessionId (UInt32.ofNat inp.attempt) (decide (result = .committed))).1 = true) :
    (rssDurableReserve204 party result st inp).1 = true := by
  unfold rssDurableReserve204
  rw [ite_false_of hc]
  split
  · rfl
  · rename_i hm
    rw [hm] at hr
    cases hr

private theorem rssThresholdSignMachine_step_ok
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st st' : RssMlDsaSignerState} {inp : RssMlDsaAttemptInput}
    {out : RssSignPublicAbortView × Option ThresholdSignSig}
    (h : (rssThresholdSignMachine chalHash sampleInBall).step st inp = some (st', out)) :
    rssThresholdSignStep chalHash sampleInBall st inp = .ok st' out := by
  dsimp only [rssThresholdSignMachine, PartyMachine.ofOutcome] at h
  cases hs : rssThresholdSignStep chalHash sampleInBall st inp with
  | err next reason => rw [hs] at h; cases h
  | ok next o =>
    rw [hs] at h
    injection h with hp
    injection hp with h1 h2
    rw [h1, h2]

/-- The durable sacrificed signer releases a signature in a reachable execution: a fresh
    journal, a committed write, nonzero key shares, nonzero triple masks and the honest
    sacrifice transcript. -/
theorem rssDurableSign204_inhabited :
    ∃ (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
      (sampleInBall : List UInt8 → Poly256)
      (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
      (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig),
      RssDurableReleased204 chalHash sampleInBall 0 .committed st inp chi T sig ∧
      rssSumVec4List st.key.s1Subsets ≠ rssZeroVec4 := by
  obtain ⟨chalHash, sampleInBall, st, stAcc, _, inpAcc, _, pubAcc, _, sig,
    hStep, _, _, _, _, hEp, hAtt, hProd, hNz⟩ := threshold_mldsa_rss_inhabited
  have hOk := rssThresholdSignMachine_step_ok hStep
  obtain ⟨hInpEp, hInpAtt, _⟩ := rssThresholdSignStep_ok_meta hOk
  have he0 : inpAcc.epoch = 0 := hInpEp.trans hEp
  have ha0 : inpAcc.attempt = 0 := hInpAtt.trans hAtt
  refine ⟨chalHash, sampleInBall, ⟨st, ⟨⟨[], [], false⟩, []⟩⟩, inpAcc, (⟨Fq204.ofNat 3, Fq204.one, Fq204.zero, Fq204.ofNat 5, Fq204.zero, Fq204.ofNat 2⟩ : Ext6Fq204),
    rssHonestSacrifice204 chalHash sampleInBall st inpAcc (⟨Fq204.ofNat 2, Fq204.ofNat 7, Fq204.zero, Fq204.one, Fq204.zero, Fq204.zero⟩ : Ext6Fq204) Fq204.one,
    sig, ?_, hNz⟩
  have hValid := rssSacrificedProductsValid_complete chalHash sampleInBall st inpAcc
    (⟨Fq204.ofNat 3, Fq204.one, Fq204.zero, Fq204.ofNat 5, Fq204.zero, Fq204.ofNat 2⟩ : Ext6Fq204) (⟨Fq204.ofNat 2, Fq204.ofNat 7, Fq204.zero, Fq204.one, Fq204.zero, Fq204.zero⟩ : Ext6Fq204) Fq204.one hProd
  have hEq := rssSacrificedSignStep_eq_of_valid chalHash sampleInBall st inpAcc (⟨Fq204.ofNat 3, Fq204.one, Fq204.zero, Fq204.ofNat 5, Fq204.zero, Fq204.ofNat 2⟩ : Ext6Fq204) _ hValid
    ((rssProductsValid_eq_true_iff chalHash sampleInBall st inpAcc).mpr hProd)
  have hRes : (rssDurableReserve204 0 .committed
      (⟨st, ⟨⟨[], [], false⟩, []⟩⟩ : RssDurableSigner204) inpAcc).1 = true := by
    apply rssDurableReserve204_ok_of
    · intro hc
      rcases hc with hc | hc | hc | hc | hc
      · exact hc hInpEp
      · exact hc hInpAtt
      · rw [he0] at hc
        exact absurd hc (by decide)
      · rw [ha0] at hc
        exact absurd hc (by decide)
      · exact nomatch hc
    · dsimp only
      rw [he0, ha0]
      exact durableBurnReserve_empty _ _ _ _ _ (by decide)
  unfold RssDurableReleased204 rssDurableSign204
  dsimp only
  rw [hRes]
  dsimp only
  rw [hEq, hOk]
  rfl

theorem tooth_rssProductsValid_corrupted_output
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (h : inp.products.cs1 ≠ (rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets).cs1) :
    rssProductsValid chalHash sampleInBall st inp = false := by
  cases hv : rssProductsValid chalHash sampleInBall st inp with
  | false => rfl
  | true =>
    exact False.elim (h (congrArg RssSignProducts.cs1
      ((rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp hv)))

/-! ## Commit / freeze / reveal DKG

Commitments bind the complete canonical share record and salt. The phase boundary is
explicit: every participant commits before any reveal is accepted, and no commitment
can be replaced after freezing. Hash binding remains a cryptographic assumption.
-/

structure DkgCommitState204 where
  participants : Nat
  session : Frame204
  commitments : List (List UInt8)
  frozen : Bool
  revealed : List SubsetShareRecord

def dkgSharePreimage204 (session salt : Frame204) (sh : SubsetShareRecord) : List UInt8 :=
  cshake256FramedPreimage dkgConfirmDomainTag
    [session.bytes, salt.bytes, encodePolyVec4Bytes sh.s1, encodePolyVec4Bytes sh.s2, encodePolyVec4Bytes sh.publicT]

def dkgCommit204 (st : DkgCommitState204) (digest : List UInt8) : Option DkgCommitState204 :=
  if st.frozen || decide (st.participants ≤ st.commitments.length) then none
  else some { st with commitments := st.commitments ++ [digest] }

def dkgFreeze204 (st : DkgCommitState204) : Option DkgCommitState204 :=
  if st.frozen || decide (st.participants = 0 ∨ st.commitments.length ≠ st.participants) then none
  else some { st with frozen := true }

def dkgReveal204 (H : List UInt8 → List UInt8) (A : PolyMat4) (eta : Nat)
    (st : DkgCommitState204) (salt : Frame204) (sh : SubsetShareRecord) : Option DkgCommitState204 :=
  if st.frozen && decide (st.commitments.length = st.participants) &&
      decide (st.revealed.length < st.participants) &&
      decide (H (dkgSharePreimage204 st.session salt sh) = st.commitments.getD st.revealed.length []) &&
      validSubsetShare A eta sh then
    some { st with revealed := st.revealed ++ [sh] }
  else none

theorem tooth_dkgReveal204_before_freeze (H : List UInt8 → List UInt8) (A : PolyMat4)
    (eta : Nat) (st : DkgCommitState204) (salt : Frame204) (sh : SubsetShareRecord)
    (h : st.frozen = false) : dkgReveal204 H A eta st salt sh = none := by
  simp [dkgReveal204, h]

theorem tooth_dkgCommit204_after_freeze (st : DkgCommitState204) (digest : List UInt8)
    (h : st.frozen = true) : dkgCommit204 st digest = none := by
  simp [dkgCommit204, h]

theorem dkgReveal204_valid_share {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {st next : DkgCommitState204} {salt : Frame204} {sh : SubsetShareRecord}
    (h : dkgReveal204 H A eta st salt sh = some next) :
    st.frozen = true ∧ st.commitments.length = st.participants ∧
      sh.publicT = addVec4 (matVecMul4 A sh.s1) sh.s2 ∧
      infNormVec4 sh.s1 ≤ eta ∧ infNormVec4 sh.s2 ≤ eta := by
  unfold dkgReveal204 at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact ⟨hg.1.1.1.1, hg.1.1.1.2, (validSubsetShare_eq_true_iff A eta sh).mp hg.2⟩
  · cases h

/-- A collision of the commitment hash: two distinct preimages with one digest. -/
def HashCollision204 (H : List UInt8 → List UInt8) : Prop :=
  ∃ a b : List UInt8, a ≠ b ∧ H a = H b

/-- The collision-freeness premise used below is satisfiable (by an injective function);
    for a compressing hash it is the collision-resistance assumption. -/
theorem hashCollision204_free_id : ¬ HashCollision204 id :=
  fun ⟨_, _, hne, h⟩ => hne h

private theorem dkgFrames204_bounded (session salt : Frame204) (sh : SubsetShareRecord) :
    ∀ f ∈ [session.bytes, salt.bytes, encodePolyVec4Bytes sh.s1, encodePolyVec4Bytes sh.s2,
      encodePolyVec4Bytes sh.publicT], f.length < 256 ^ 8 := by
  intro f hf
  have hb32 : (2 : Nat) ^ 32 < 256 ^ 8 := by decide
  have hv : (4096 : Nat) < 256 ^ 8 := by decide
  rcases List.mem_cons.mp hf with rfl | hf
  · exact Nat.lt_trans session.bounded hb32
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact Nat.lt_trans salt.bounded hb32
    · rcases List.mem_cons.mp hf with rfl | hf
      · rw [encodePolyVec4Bytes_length]; exact hv
      · rcases List.mem_cons.mp hf with rfl | hf
        · rw [encodePolyVec4Bytes_length]; exact hv
        · rcases List.mem_cons.mp hf with rfl | hf
          · rw [encodePolyVec4Bytes_length]; exact hv
          · exact nomatch hf

/-- The commitment preimage determines the salt and every field of the share record. -/
theorem dkgSharePreimage204_injective {session salt salt' : Frame204}
    {sh sh' : SubsetShareRecord}
    (h : dkgSharePreimage204 session salt sh = dkgSharePreimage204 session salt' sh') :
    salt.bytes = salt'.bytes ∧ sh = sh' := by
  rcases sh with ⟨a, b, c⟩
  rcases sh' with ⟨a', b', c'⟩
  unfold dkgSharePreimage204 at h
  have h5 : (5 : Nat) < 256 ^ 8 := by decide
  have hfs := cshake256FramedPreimage_frames_injective (by exact h5) (by exact h5)
    (dkgFrames204_bounded session salt ⟨a, b, c⟩)
    (dkgFrames204_bounded session salt' ⟨a', b', c'⟩) h
  have h1 := List.cons.inj (List.cons.inj hfs).2
  have h2 := List.cons.inj h1.2
  have h3 := List.cons.inj h2.2
  have h4 := List.cons.inj h3.2
  have ea : a = a' := encodePolyVec4Bytes_injective h2.1
  have eb : b = b' := encodePolyVec4Bytes_injective h3.1
  have ec : c = c' := encodePolyVec4Bytes_injective h4.1
  subst ea eb ec
  exact ⟨h1.1, rfl⟩

private theorem dkgReveal204_some {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {st next : DkgCommitState204} {salt : Frame204} {sh : SubsetShareRecord}
    (h : dkgReveal204 H A eta st salt sh = some next) :
    st.frozen = true ∧
      H (dkgSharePreimage204 st.session salt sh) = st.commitments.getD st.revealed.length [] ∧
      next = { st with revealed := st.revealed ++ [sh] } := by
  unfold dkgReveal204 at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    injection h with h
    exact ⟨hg.1.1.1.1, hg.1.2, h.symm⟩
  · cases h

private theorem dkgCommit204_some {st next : DkgCommitState204} {digest : List UInt8}
    (h : dkgCommit204 st digest = some next) :
    st.frozen = false ∧ next = { st with commitments := st.commitments ++ [digest] } := by
  unfold dkgCommit204 at h
  split at h
  · cases h
  · rename_i hg
    injection h with h
    refine ⟨?_, h.symm⟩
    cases hf : st.frozen with
    | false => rfl
    | true =>
      rw [hf] at hg
      exact False.elim (hg rfl)

private theorem dkgFreeze204_some {st next : DkgCommitState204}
    (h : dkgFreeze204 st = some next) :
    st.frozen = false ∧ st.commitments.length = st.participants ∧
      next = { st with frozen := true } := by
  unfold dkgFreeze204 at h
  split at h
  · cases h
  · rename_i hg
    injection h with h
    cases hf : st.frozen with
    | true =>
      rw [hf] at hg
      exact False.elim (hg rfl)
    | false =>
      rw [hf] at hg
      have hP : ¬ (st.participants = 0 ∨ st.commitments.length ≠ st.participants) :=
        fun p => hg (decide_eq_true p)
      exact ⟨rfl, Decidable.byContradiction (fun hne => hP (Or.inr hne)), h.symm⟩

/-- Binding of a reveal to the frozen commitment at its position: two accepted openings of
    one commitment agree in salt and in every share field, or exhibit a hash collision. -/
theorem dkgReveal204_binding {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {st st' next next' : DkgCommitState204} {salt salt' : Frame204}
    {sh sh' : SubsetShareRecord}
    (hs : st'.session = st.session) (hc : st'.commitments = st.commitments)
    (hk : st'.revealed.length = st.revealed.length)
    (h : dkgReveal204 H A eta st salt sh = some next)
    (h' : dkgReveal204 H A eta st' salt' sh' = some next') :
    (salt.bytes = salt'.bytes ∧ sh = sh') ∨ HashCollision204 H := by
  obtain ⟨_, hh, _⟩ := dkgReveal204_some h
  obtain ⟨_, hh', _⟩ := dkgReveal204_some h'
  rw [hs, hc, hk] at hh'
  if hp : dkgSharePreimage204 st.session salt sh = dkgSharePreimage204 st.session salt' sh' then
    exact Or.inl (dkgSharePreimage204_injective hp)
  else
    exact Or.inr ⟨_, _, hp, hh.trans hh'.symm⟩

/-- One DKG protocol move. -/
inductive DkgStep204 (H : List UInt8 → List UInt8) (A : PolyMat4) (eta : Nat) :
    DkgCommitState204 → DkgCommitState204 → Prop where
  | commit {st next : DkgCommitState204} (digest : List UInt8) :
      dkgCommit204 st digest = some next → DkgStep204 H A eta st next
  | freeze {st next : DkgCommitState204} :
      dkgFreeze204 st = some next → DkgStep204 H A eta st next
  | reveal {st next : DkgCommitState204} (salt : Frame204) (sh : SubsetShareRecord) :
      dkgReveal204 H A eta st salt sh = some next → DkgStep204 H A eta st next

inductive DkgTrace204 (H : List UInt8 → List UInt8) (A : PolyMat4) (eta : Nat) :
    DkgCommitState204 → DkgCommitState204 → Prop where
  | nil (st : DkgCommitState204) : DkgTrace204 H A eta st st
  | cons {a b c : DkgCommitState204} :
      DkgStep204 H A eta a b → DkgTrace204 H A eta b c → DkgTrace204 H A eta a c

theorem dkgStep204_frozen_stable {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {a b : DkgCommitState204} (h : DkgStep204 H A eta a b) (hf : a.frozen = true) :
    b.frozen = true ∧ b.commitments = a.commitments ∧ b.session = a.session := by
  cases h with
  | commit digest hc =>
    have hn := (dkgCommit204_some hc).1
    rw [hf] at hn
    cases hn
  | freeze hz =>
    have hn := (dkgFreeze204_some hz).1
    rw [hf] at hn
    cases hn
  | reveal salt sh hr =>
    obtain ⟨_, _, hn⟩ := dkgReveal204_some hr
    subst hn
    exact ⟨hf, rfl, rfl⟩

/-- After freezing, no execution changes the commitment list or the session. -/
theorem dkgTrace204_frozen_stable {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {a b : DkgCommitState204} (h : DkgTrace204 H A eta a b) :
    a.frozen = true →
      b.frozen = true ∧ b.commitments = a.commitments ∧ b.session = a.session := by
  induction h with
  | nil st => exact fun hf => ⟨hf, rfl, rfl⟩
  | cons step _ ih =>
    intro hf
    obtain ⟨hf1, hc1, hs1⟩ := dkgStep204_frozen_stable step hf
    obtain ⟨hf2, hc2, hs2⟩ := ih hf1
    exact ⟨hf2, hc2.trans hc1, hs2.trans hs1⟩

/-- No share is revealed in any execution before the commitment list is frozen. -/
theorem dkgTrace204_no_reveal_before_freeze {H : List UInt8 → List UInt8} {A : PolyMat4}
    {eta : Nat} {a b : DkgCommitState204} (h : DkgTrace204 H A eta a b) :
    (a.frozen = false → a.revealed = []) → b.frozen = false → b.revealed = [] := by
  induction h with
  | nil st => exact fun ha => ha
  | cons step _ ih =>
    intro ha
    apply ih
    intro hbf
    cases step with
    | commit digest hc =>
      obtain ⟨hfa, hn⟩ := dkgCommit204_some hc
      subst hn
      exact ha hfa
    | freeze hz =>
      obtain ⟨_, _, hn⟩ := dkgFreeze204_some hz
      subst hn
      exact Bool.noConfusion hbf
    | reveal salt sh hr =>
      obtain ⟨hfa, _, hn⟩ := dkgReveal204_some hr
      subst hn
      have hfb : _ = false := hbf
      rw [hfa] at hfb
      exact Bool.noConfusion hfb

/-- Once the commitment list is frozen, the share accepted at each position is fixed up to
    a hash collision on every continuation: what a participant reveals cannot be chosen
    after seeing what the others revealed. -/
theorem dkg204_reveal_determined_at_freeze {H : List UInt8 → List UInt8} {A : PolyMat4}
    {eta : Nat} {a b b' n n' : DkgCommitState204} {salt salt' : Frame204}
    {sh sh' : SubsetShareRecord}
    (hf : a.frozen = true)
    (hb : DkgTrace204 H A eta a b) (hb' : DkgTrace204 H A eta a b')
    (hk : b'.revealed.length = b.revealed.length)
    (h : dkgReveal204 H A eta b salt sh = some n)
    (h' : dkgReveal204 H A eta b' salt' sh' = some n') :
    (salt.bytes = salt'.bytes ∧ sh = sh') ∨ HashCollision204 H := by
  obtain ⟨_, hc, hs⟩ := dkgTrace204_frozen_stable hb hf
  obtain ⟨_, hc', hs'⟩ := dkgTrace204_frozen_stable hb' hf
  exact dkgReveal204_binding (hs'.trans hs.symm) (hc'.trans hc.symm) hk h h'

/-- A complete commit, freeze, reveal execution with a nonzero share exists. -/
theorem dkg204_honest_run_inhabited :
    ∃ (H : List UInt8 → List UInt8) (A : PolyMat4) (init final : DkgCommitState204)
      (sh : SubsetShareRecord),
      DkgTrace204 H A 2 init final ∧ init.frozen = false ∧ init.revealed = [] ∧
      final.revealed = [sh] ∧ sh.s1 ≠ rssZeroVec4 := by
  have hn : infNormVec4 (fun _ => polyTreeConstLeaf 8 Fq204.one) ≤ 2 := by
    unfold infNormVec4
    simp only [polyTreeConstLeaf_infNorm, Nat.max_self]
    decide
  have hvalid : validSubsetShare idMat4 2
      ⟨fun _ => polyTreeConstLeaf 8 Fq204.one, fun _ => polyTreeConstLeaf 8 Fq204.one,
        addVec4 (matVecMul4 idMat4 (fun _ => polyTreeConstLeaf 8 Fq204.one))
          (fun _ => polyTreeConstLeaf 8 Fq204.one)⟩ = true :=
    (validSubsetShare_eq_true_iff _ _ _).mpr ⟨rfl, hn, hn⟩
  generalize hsh : (⟨fun _ => polyTreeConstLeaf 8 Fq204.one,
      fun _ => polyTreeConstLeaf 8 Fq204.one,
      addVec4 (matVecMul4 idMat4 (fun _ => polyTreeConstLeaf 8 Fq204.one))
        (fun _ => polyTreeConstLeaf 8 Fq204.one)⟩ : SubsetShareRecord) = sh at hvalid
  have hs1 : sh.s1 ≠ rssZeroVec4 := by
    rw [← hsh]
    intro h
    have he : polyTreeConstLeaf 8 Fq204.one = PolyTree.zero 8 := congrFun h (0 : Fin 4)
    have hv := congrArg PolyTree.infNorm he
    rw [polyTreeConstLeaf_infNorm] at hv
    change 1 = 0 at hv
    omega
  generalize hd : dkgSharePreimage204 ⟨[], by decide⟩ ⟨[], by decide⟩ sh = d
  have hc : dkgCommit204 ⟨1, ⟨[], by decide⟩, [], false, []⟩ d =
      some ⟨1, ⟨[], by decide⟩, [d], false, []⟩ := by
    rfl
  have hz : dkgFreeze204 ⟨1, ⟨[], by decide⟩, [d], false, []⟩ =
      some ⟨1, ⟨[], by decide⟩, [d], true, []⟩ := by
    rfl
  have hr : dkgReveal204 id idMat4 2 ⟨1, ⟨[], by decide⟩, [d], true, []⟩ ⟨[], by decide⟩ sh =
      some ⟨1, ⟨[], by decide⟩, [d], true, [sh]⟩ := by
    unfold dkgReveal204
    dsimp only
    rw [hd, hvalid]
    have hdec : decide (id d = [d].getD ([] : List SubsetShareRecord).length []) = true :=
      decide_eq_true rfl
    rw [hdec]
    rfl
  exact ⟨id, idMat4, _, _, sh,
    .cons (.commit d hc) (.cons (.freeze hz) (.cons (.reveal _ sh hr) (.nil _))),
    rfl, rfl, rfl, hs1⟩

/-! ## Sequential fresh-mask transcript bijection

Unlike a product of marginal claims, this experiment allows each gate's terms to depend
on the complete preceding transcript. Each list position consumes a distinct independent
quadruple. This proves the uniform-tape experiment; a PRSS implementation still requires
its own joint PRG hybrid, and must never reuse a tape position.
-/

private theorem serverGateMaskedView_involutive (terms masks : GoldQuad) :
    serverGateMaskedView terms (serverGateMaskedView terms masks) = masks := by
  rcases terms with ⟨a, b, c, d⟩
  rcases masks with ⟨w, x, y, z⟩
  simp only [serverGateMaskedView, gold_sub_sub_self]

def toprfJointMaskedView (terms : Nat → List GoldQuad → GoldQuad) :
    Nat → List GoldQuad → List GoldQuad → List GoldQuad
  | _, _, [] => []
  | i, history, mask :: masks =>
    let msg := serverGateMaskedView (terms i history) mask
    msg :: toprfJointMaskedView terms (i + 1) (history ++ [msg]) masks

def toprfJointMaskRecovery (terms : Nat → List GoldQuad → GoldQuad) :
    Nat → List GoldQuad → List GoldQuad → List GoldQuad
  | _, _, [] => []
  | i, history, msg :: msgs =>
    serverGateMaskedView (terms i history) msg ::
      toprfJointMaskRecovery terms (i + 1) (history ++ [msg]) msgs

private theorem toprfJointMaskRecovery_left (terms : Nat → List GoldQuad → GoldQuad) :
    ∀ (coins : List GoldQuad) (i : Nat) (history : List GoldQuad),
    toprfJointMaskRecovery terms i history (toprfJointMaskedView terms i history coins) = coins
  | [], _, _ => rfl
  | _ :: coins, i, history => by
    simp only [toprfJointMaskedView, toprfJointMaskRecovery,
      serverGateMaskedView_involutive, toprfJointMaskRecovery_left terms coins]

private theorem toprfJointMaskRecovery_right (terms : Nat → List GoldQuad → GoldQuad) :
    ∀ (msgs : List GoldQuad) (i : Nat) (history : List GoldQuad),
    toprfJointMaskedView terms i history (toprfJointMaskRecovery terms i history msgs) = msgs
  | [], _, _ => rfl
  | _ :: msgs, i, history => by
    simp only [toprfJointMaskedView, toprfJointMaskRecovery,
      serverGateMaskedView_involutive, toprfJointMaskRecovery_right terms msgs]

def toprfJointTranscriptEquiv (terms : Nat → List GoldQuad → GoldQuad) :
    SimpleEquiv (List GoldQuad) (List GoldQuad) where
  toFun := toprfJointMaskedView terms 0 []
  invFun := toprfJointMaskRecovery terms 0 []
  left_inv coins := toprfJointMaskRecovery_left terms coins 0 []
  right_inv msgs := toprfJointMaskRecovery_right terms msgs 0 []

theorem toprfJointTranscript_two_secrets
    (termsA termsB : Nat → List GoldQuad → GoldQuad) (coins : List GoldQuad) :
    toprfJointMaskedView termsB 0 []
      (toprfJointMaskRecovery termsB 0 [] (toprfJointMaskedView termsA 0 [] coins)) =
        toprfJointMaskedView termsA 0 [] coins :=
  toprfJointMaskRecovery_right termsB _ 0 []

/-- Uniform tapes have a fixed length; the simulator preserves that support exactly. -/
theorem toprfJointMaskRecovery_length (terms : Nat → List GoldQuad → GoldQuad) :
    ∀ (msgs : List GoldQuad) (i : Nat) (history : List GoldQuad),
      (toprfJointMaskRecovery terms i history msgs).length = msgs.length
  | [], _, _ => rfl
  | _ :: msgs, i, history => by
    simp only [toprfJointMaskRecovery, List.length_cons, toprfJointMaskRecovery_length terms msgs]


theorem toprfJointMaskedView_length (terms : Nat → List GoldQuad → GoldQuad) :
    ∀ (coins : List GoldQuad) (i : Nat) (history : List GoldQuad),
      (toprfJointMaskedView terms i history coins).length = coins.length
  | [], _, _ => rfl
  | _ :: coins, i, history => by
    simp only [toprfJointMaskedView, List.length_cons, toprfJointMaskedView_length terms coins]

/-- Everything one server sees of a client input followed by a run of multiplication
    gates: its four input components, then one masked message per gate. The gate terms may
    depend on the server's own input view, on the gate index and on all earlier messages. -/
def toprfServerJointView204 (p : Fin 5) (val : Goldilocks)
    (terms : GoldQuad → Nat → List GoldQuad → GoldQuad)
    (coins : GoldQuad × List GoldQuad) : GoldQuad × List GoldQuad :=
  (clientViewAtServer p (clientShareWire val coins.1),
    toprfJointMaskedView (terms (clientViewAtServer p (clientShareWire val coins.1))) 0 []
      coins.2)

/-- Joint-view simulation over the input sharing and every gate at once: for any two client
    inputs and any two secret-dependent term schedules there is one bijection on the whole
    coin tape (input coins and all gate masks) carrying the first view to the second. The
    marginal statements above do not imply this; the bijection here is built sequentially.
    The tape positions are independent uniform field elements; replacing them by a seed
    expansion is a pseudorandomness assumption that this theorem does not discharge. -/
theorem toprf_joint_view_simulation (p : Fin 5) (valA valB : Goldilocks)
    (termsA termsB : GoldQuad → Nat → List GoldQuad → GoldQuad) :
    ∃ e : SimpleEquiv (GoldQuad × List GoldQuad) (GoldQuad × List GoldQuad),
      ∀ coins : GoldQuad × List GoldQuad,
        toprfServerJointView204 p valA termsA coins =
            toprfServerJointView204 p valB termsB (e.toFun coins) ∧
          (e.toFun coins).2.length = coins.2.length := by
  obtain ⟨eA, hA⟩ := toprf_one_curious_server_hiding.2.1 p valA
  obtain ⟨eB, hB⟩ := toprf_one_curious_server_hiding.2.1 p valB
  refine ⟨
    { toFun := fun c =>
        (eB.invFun (eA.toFun c.1),
          toprfJointMaskRecovery (termsB (eA.toFun c.1)) 0 []
            (toprfJointMaskedView (termsA (eA.toFun c.1)) 0 [] c.2))
      invFun := fun c =>
        (eA.invFun (eB.toFun c.1),
          toprfJointMaskRecovery (termsA (eB.toFun c.1)) 0 []
            (toprfJointMaskedView (termsB (eB.toFun c.1)) 0 [] c.2))
      left_inv := ?_
      right_inv := ?_ }, ?_⟩
  · intro c
    rcases c with ⟨r, t⟩
    simp only [eB.right_inv, eA.left_inv, toprfJointMaskRecovery_right,
      toprfJointMaskRecovery_left]
  · intro c
    rcases c with ⟨r, t⟩
    simp only [eA.right_inv, eB.left_inv, toprfJointMaskRecovery_right,
      toprfJointMaskRecovery_left]
  · intro c
    rcases c with ⟨r, t⟩
    refine ⟨?_, ?_⟩
    · unfold toprfServerJointView204
      simp only [← hA, ← hB, eB.right_inv, toprfJointMaskRecovery_right]
    · simp only [toprfJointMaskRecovery_length, toprfJointMaskedView_length]

/-- The simulation is not vacuous in the secret: with the gate terms fixed, two different
    client inputs give different views on the same tape, so the coin bijection is doing
    the work. -/
theorem tooth_toprf_joint_view_depends_on_secret (r : GoldQuad) (t : List GoldQuad)
    (terms : GoldQuad → Nat → List GoldQuad → GoldQuad) (valA valB : Goldilocks)
    (h : valA ≠ valB) :
    toprfServerJointView204 0 valA terms (r, t) ≠ toprfServerJointView204 0 valB terms (r, t) := by
  intro hv
  have h1 := congrArg (fun v => v.1.2.2.2) hv
  rcases r with ⟨r0, r1, r2, r3⟩
  have hw : ∀ val : Goldilocks,
      (toprfServerJointView204 0 val terms ((r0, r1, r2, r3), t)).1.2.2.2 =
        Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub val r0) r1) r2) r3 :=
    fun _ => rfl
  rw [hw valA, hw valB] at h1
  apply h
  have key : ∀ v : Goldilocks,
      Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.add
        (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.sub v r0) r1) r2) r3)
          r3) r2) r1) r0 = v := by
    intro v
    rw [← goldOfInt_nat v, ← goldOfInt_nat r0, ← goldOfInt_nat r1, ← goldOfInt_nat r2,
      ← goldOfInt_nat r3]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1
    omega
  rw [← key valA, ← key valB, h1]


/-! ## Active reshare execution through all Poseidon2 rounds

The execution is written once, over an abstract cross-term transport, and instantiated
twice: with three full-value holder messages per term (unconditional), and with the
optimized two-value, one-digest transport (correct or a hash collision). One fixed Byzantine
party may erase or replace every message it sends. The Poseidon2 protocol is an RSS
arithmetic protocol with no discrete-log group, so there is no DLEQ statement to check here:
correction of the malicious server is by holder redundancy at every multiplication and by
the 3-of-4 vote at finalization.
-/

abbrev ToprfFault204 := List Nat → Fin 5 → Fin 5 → Goldilocks → Option Goldilocks

/-- A cross-term transport: what the receivers decode for the term of gate `gate` between
    components `i` and `j` whose honest value is `term`. -/
abbrev ToprfCross204 := List Nat → Fin 5 → Fin 5 → Goldilocks → Option Goldilocks

private theorem toprfThreeHoldersDistinct204 (i j : Fin 5) :
    (toprfHolders i j).getD 0 0 ≠ (toprfHolders i j).getD 1 0 ∧
    (toprfHolders i j).getD 0 0 ≠ (toprfHolders i j).getD 2 0 ∧
    (toprfHolders i j).getD 1 0 ≠ (toprfHolders i j).getD 2 0 := by
  revert i j
  decide

def toprfActiveCross204 (bad : Fin 5) (fault : ToprfFault204) : ToprfCross204 :=
  fun gate i j term =>
    majority2Of3
      (if (toprfHolders i j).getD 0 0 = bad then fault gate i j term else some term)
      (if (toprfHolders i j).getD 1 0 = bad then fault gate i j term else some term)
      (if (toprfHolders i j).getD 2 0 = bad then fault gate i j term else some term)

theorem toprfActiveCross204_correct (bad : Fin 5) (fault : ToprfFault204) (gate : List Nat)
    (i j : Fin 5) (term : Goldilocks) :
    toprfActiveCross204 bad fault gate i j term = some term := by
  obtain ⟨h01, h02, h12⟩ := toprfThreeHoldersDistinct204 i j
  unfold toprfActiveCross204
  apply majority2Of3_of_two_honest
  by_cases h0 : (toprfHolders i j).getD 0 0 = bad
  · have h1 : (toprfHolders i j).getD 1 0 ≠ bad := fun h => h01 (h0.trans h.symm)
    have h2 : (toprfHolders i j).getD 2 0 ≠ bad := fun h => h02 (h0.trans h.symm)
    exact Or.inr (Or.inr ⟨ite_false_of h1 _ _, ite_false_of h2 _ _⟩)
  · by_cases h1 : (toprfHolders i j).getD 1 0 = bad
    · have h2 : (toprfHolders i j).getD 2 0 ≠ bad := fun h => h12 (h1.trans h.symm)
      exact Or.inr (Or.inl ⟨ite_false_of h0 _ _, ite_false_of h2 _ _⟩)
    · exact Or.inl ⟨ite_false_of h0 _ _, ite_false_of h1 _ _⟩

/-- The decoded values themselves feed every multiplication output. A failed decoder
    contributes zero; the theorems below show when that cannot happen. -/
def toprfActiveMul204 (cross : ToprfCross204) (gate : List Nat)
    (x y : ToprfWire) (mask : Fin 5 → Fin 5 → Goldilocks) : ToprfWire :=
  fun c =>
    let diag := (cross gate c c (Goldilocks.mul (x c) (y c))).getD Goldilocks.zero
    let outgoing := sumGoldList ((fin5Others c).map (fun j => mask c j))
    let incoming := sumGoldList ((fin5Others c).map (fun i =>
      (cross gate i c (Goldilocks.sub (Goldilocks.mul (x i) (y c)) (mask i c))).getD
        Goldilocks.zero))
    Goldilocks.add (Goldilocks.add diag outgoing) incoming

theorem toprfActiveMul204_eq (cross : ToprfCross204)
    (hc : ∀ gate i j term, cross gate i j term = some term) (gate : List Nat)
    (x y : ToprfWire) (mask : Fin 5 → Fin 5 → Goldilocks) :
    toprfActiveMul204 cross gate x y mask = toprfMulWire x y mask := by
  funext c
  simp only [toprfActiveMul204, toprfMulWire, hc, Option.getD_some]

def toprfActiveSbox204 (cross : ToprfCross204) (gate : List Nat)
    (w : ToprfWire) (m1 m2 m3 m4 : Fin 5 → Fin 5 → Goldilocks) : ToprfWire :=
  let x2 := toprfActiveMul204 cross (gate ++ [0]) w w m1
  let x3 := toprfActiveMul204 cross (gate ++ [1]) x2 w m2
  let x4 := toprfActiveMul204 cross (gate ++ [2]) x2 x2 m3
  toprfActiveMul204 cross (gate ++ [3]) x3 x4 m4

theorem toprfActiveSbox204_eq (cross : ToprfCross204)
    (hc : ∀ gate i j term, cross gate i j term = some term) (gate : List Nat)
    (w : ToprfWire) (m1 m2 m3 m4 : Fin 5 → Fin 5 → Goldilocks) :
    toprfActiveSbox204 cross gate w m1 m2 m3 m4 = toprfSboxWire w m1 m2 m3 m4 := by
  simp only [toprfActiveSbox204, toprfSboxWire, toprfActiveMul204_eq cross hc]

def toprfActiveExtRound204 (cross : ToprfCross204) (gate : List Nat)
    (masks : Fin 12 → SboxMask4) (rc : Poseidon2State12) (st : ToprfState12) : ToprfState12 :=
  let s := toprfAddPublicState12 rc st
  let sb (idx : Fin 12) (f : Poseidon2State12 → Goldilocks) : ToprfWire :=
    let m := masks idx
    toprfActiveSbox204 cross (gate ++ [idx.val]) (fun c => f (s c)) m.m1 m.m2 m.m3 m.m4
  let y0 := sb ⟨0, by decide⟩ (fun q => q.b0.x0)
  let y1 := sb ⟨1, by decide⟩ (fun q => q.b0.x1)
  let y2 := sb ⟨2, by decide⟩ (fun q => q.b0.x2)
  let y3 := sb ⟨3, by decide⟩ (fun q => q.b0.x3)
  let y4 := sb ⟨4, by decide⟩ (fun q => q.b1.x0)
  let y5 := sb ⟨5, by decide⟩ (fun q => q.b1.x1)
  let y6 := sb ⟨6, by decide⟩ (fun q => q.b1.x2)
  let y7 := sb ⟨7, by decide⟩ (fun q => q.b1.x3)
  let y8 := sb ⟨8, by decide⟩ (fun q => q.b2.x0)
  let y9 := sb ⟨9, by decide⟩ (fun q => q.b2.x1)
  let y10 := sb ⟨10, by decide⟩ (fun q => q.b2.x2)
  let y11 := sb ⟨11, by decide⟩ (fun q => q.b2.x3)
  fun c => applyME ⟨⟨y0 c, y1 c, y2 c, y3 c⟩, ⟨y4 c, y5 c, y6 c, y7 c⟩, ⟨y8 c, y9 c, y10 c, y11 c⟩⟩

def toprfActiveIntRound204 (cross : ToprfCross204) (gate : List Nat) (m : SboxMask4)
    (rc : Goldilocks) (st : ToprfState12) : ToprfState12 :=
  let w0 : ToprfWire := fun c => if c = 0 then Goldilocks.add (st 0).b0.x0 rc else (st c).b0.x0
  let y0 := toprfActiveSbox204 cross (gate ++ [0]) w0 m.m1 m.m2 m.m3 m.m4
  fun c => applyMI ⟨⟨y0 c, (st c).b0.x1, (st c).b0.x2, (st c).b0.x3⟩, (st c).b1, (st c).b2⟩

theorem toprfActiveExtRound204_eq (cross : ToprfCross204)
    (hc : ∀ gate i j term, cross gate i j term = some term) (gate : List Nat)
    (m : Fin 12 → SboxMask4) (rc : Poseidon2State12) (st : ToprfState12) :
    toprfActiveExtRound204 cross gate m rc st = toprfExtRound m rc st := by
  simp only [toprfActiveExtRound204, toprfExtRound, toprfActiveSbox204_eq cross hc]

theorem toprfActiveIntRound204_eq (cross : ToprfCross204)
    (hc : ∀ gate i j term, cross gate i j term = some term) (gate : List Nat)
    (m : SboxMask4) (rc : Goldilocks) (st : ToprfState12) :
    toprfActiveIntRound204 cross gate m rc st = toprfIntRound m rc st := by
  simp only [toprfActiveIntRound204, toprfIntRound, toprfActiveSbox204_eq cross hc]

def toprfActivePerm204 (cross : ToprfCross204)
    (masks : ToprfPerm12Masks) (init : ToprfState12) : ToprfState12 :=
  let s0 : ToprfState12 := fun c => applyME (init c)
  let s1 := runToprfRoundsIdx
    (fun r rc s => toprfActiveExtRound204 cross [0, r] (masks.initExt r) rc s)
    0 poseidon2InitialExtConsts s0
  let s2 := runToprfRoundsIdx
    (fun r rc s => toprfActiveIntRound204 cross [1, r] (masks.internal r) rc s)
    0 poseidon2InternalConsts s1
  runToprfRoundsIdx
    (fun r rc s => toprfActiveExtRound204 cross [2, r] (masks.termExt r) rc s)
    0 poseidon2TerminalExtConsts s2

/-- Honest engine outputs are derived through decoded messages at every multiplication of
    every round, rather than assumed as a final-output premise. -/
theorem toprfActivePerm204_eq (cross : ToprfCross204)
    (hc : ∀ gate i j term, cross gate i j term = some term)
    (masks : ToprfPerm12Masks) (init : ToprfState12) :
    toprfActivePerm204 cross masks init = toprfEvalPerm12 masks init := by
  simp only [toprfActivePerm204, toprfEvalPerm12,
    toprfActiveExtRound204_eq cross hc, toprfActiveIntRound204_eq cross hc]

def toprfActiveClient204 (bad : Fin 5) (cross : ToprfCross204)
    (masks : ToprfPerm12Masks) (keys inputs : Fin 5 → Lane4)
    (forgedFinal : Option (Fin 5 → Lane4)) : Option Lane4 :=
  clientFinalizeLane4 (fun p =>
    if p = bad then forgedFinal
    else some (fun c => (toprfActivePerm204 cross masks (toprfInitPrfState keys inputs) c).b0))

theorem toprfActiveClient204_correct_of (bad : Fin 5) (cross : ToprfCross204)
    (hc : ∀ gate i j term, cross gate i j term = some term)
    (masks : ToprfPerm12Masks) (keys inputs : Fin 5 → Lane4)
    (forgedFinal : Option (Fin 5 → Lane4)) :
    toprfActiveClient204 bad cross masks keys inputs forgedFinal =
      some (toprfPlaintext (sumLane4Shares5 keys) (sumLane4Shares5 inputs)) := by
  unfold toprfActiveClient204
  rw [toprfActivePerm204_eq cross hc]
  exact (toprf_2of5_corrects_one_malicious_server id [] 0 0 1 (by decide) bad).2.2
    masks keys inputs _ (fun p hp => ite_false_of hp _ _)

/-- Full-value transport: the client output is correct against one malicious server that
    deviates at every multiplication of all 30 rounds and at finalization. -/
theorem toprfActiveClient204_correct (bad : Fin 5) (fault : ToprfFault204)
    (masks : ToprfPerm12Masks) (keys inputs : Fin 5 → Lane4)
    (forgedFinal : Option (Fin 5 → Lane4)) :
    toprfActiveClient204 bad (toprfActiveCross204 bad fault) masks keys inputs forgedFinal =
      some (toprfPlaintext (sumLane4Shares5 keys) (sumLane4Shares5 inputs)) :=
  toprfActiveClient204_correct_of bad _ (toprfActiveCross204_correct bad fault)
    masks keys inputs forgedFinal

abbrev ToprfVecFault204 := List Nat → Fin 5 → Fin 5 → Goldilocks → Option (List Goldilocks)
abbrev ToprfDigestFault204 := List Nat → Fin 5 → Fin 5 → Goldilocks → Option (List UInt8)

/-- Receivers discard vectors at or above the framing bound before decoding. -/
def toprfBoundedVec204 : Option (List Goldilocks) → Option (List Goldilocks)
  | some v => if v.length < 2 ^ 20 then some v else none
  | none => none

private theorem toprfBoundedVec204_bound {m : Option (List Goldilocks)} {v : List Goldilocks}
    (h : toprfBoundedVec204 m = some v) : v.length < 2 ^ 20 := by
  cases m with
  | none => cases h
  | some w =>
    simp only [toprfBoundedVec204] at h
    split at h
    · rename_i hl
      injection h with h
      rw [← h]
      exact hl
    · cases h

/-- Optimized transport: two holders send the value, the third sends a digest, and the
    receiver runs the large-layer decoder on the one-element group. -/
def toprfDigestCross204 (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (bad : Fin 5) (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204) :
    ToprfCross204 :=
  fun gate i j term =>
    match decodeGroupLarge H ctx layer i j
      (if (toprfHolders i j).getD 0 0 = bad then toprfBoundedVec204 (fault gate i j term)
        else some [term])
      (if (toprfHolders i j).getD 1 0 = bad then toprfBoundedVec204 (fault gate i j term)
        else some [term])
      (if (toprfHolders i j).getD 2 0 = bad then faultDigest gate i j term
        else some (toprfGroupDigest H ctx layer i j [term])) with
    | some [v] => some v
    | _ => none

/-- Every decoded cross term of the digest transport is the honest one, or the malicious
    holder has produced an explicit collision of the reshare digest. -/
theorem toprfDigestCross204_correct_or_collision
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (hCtx : ctx.length < 2 ^ 20) (bad : Fin 5)
    (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204)
    (gate : List Nat) (i j : Fin 5) (term : Goldilocks) :
    toprfDigestCross204 H ctx layer bad fault faultDigest gate i j term = some term ∨
      HashCollision204 H := by
  obtain ⟨h01, h02, h12⟩ := toprfThreeHoldersDistinct204 i j
  have hLen : ∀ v0 : List Goldilocks,
      (if (toprfHolders i j).getD 0 0 = bad then toprfBoundedVec204 (fault gate i j term)
        else some [term]) = some v0 → v0.length < 2 ^ 20 := by
    intro v0 hv
    if hb : (toprfHolders i j).getD 0 0 = bad then
      rw [ite_true_of hb] at hv
      exact toprfBoundedVec204_bound hv
    else
      rw [ite_false_of hb] at hv
      injection hv with hv
      rw [← hv]
      exact (by decide : (1 : Nat) < 2 ^ 20)
  have hDec := (toprf_2of5_corrects_one_malicious_server H ctx layer i j hCtx bad).2.1
    ((toprfHolders i j).getD 0 0) ((toprfHolders i j).getD 1 0) ((toprfHolders i j).getD 2 0)
    [term]
    (if (toprfHolders i j).getD 0 0 = bad then toprfBoundedVec204 (fault gate i j term)
      else some [term])
    (if (toprfHolders i j).getD 1 0 = bad then toprfBoundedVec204 (fault gate i j term)
      else some [term])
    (if (toprfHolders i j).getD 2 0 = bad then faultDigest gate i j term
      else some (toprfGroupDigest H ctx layer i j [term]))
    h01 h02 h12 (by decide : (1 : Nat) < 2 ^ 20) hLen
    (fun hn => ite_false_of hn _ _) (fun hn => ite_false_of hn _ _)
    (fun hn => ite_false_of hn _ _)
  unfold toprfDigestCross204
  rcases hDec with hOk | ⟨forged, _, _, hne, heq⟩
  · rw [hOk]
    exact Or.inl rfl
  · exact Or.inr ⟨_, _, hne, heq⟩

private theorem gold_one_ne_zero204 : Goldilocks.one ≠ Goldilocks.zero := by
  intro h
  have hv := congrArg Goldilocks.val h
  exact absurd hv (by decide)

/-- The same cross-term transport with the holder vote removed: the first holder's message
    is consumed as received. -/
def toprfUncheckedCross204 (bad : Fin 5) (fault : ToprfFault204) : ToprfCross204 :=
  fun gate i j term =>
    if (toprfHolders i j).getD 0 0 = bad then fault gate i j term else some term

/-- Removing the holder vote admits a forged multiplication message immediately: the first
    holder of cross-term `(0, 1)` is server `2`, and its forged value replaces the honest one. -/
theorem tooth_toprf_unchecked_cross_message :
    toprfUncheckedCross204 2 (fun _ _ _ _ => some Goldilocks.one) [] 0 1 Goldilocks.zero ≠
      some Goldilocks.zero := by
  intro h
  have hEval : toprfUncheckedCross204 2 (fun _ _ _ _ => some Goldilocks.one) [] 0 1
      Goldilocks.zero = some Goldilocks.one := by
    rfl
  rw [hEval] at h
  exact gold_one_ne_zero204 (Option.some.inj h)



theorem tooth_contextIndex204_no_u64_wrap : leb128 0 ≠ leb128 (2 ^ 64) := by
  intro h
  have he := contextIndex204_injective h
  omega

def RssProductsChecked204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) : Prop :=
  rssProductsValid chalHash sampleInBall st inp = true

theorem rssProductsChecked204_sound
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (h : RssProductsChecked204 chalHash sampleInBall st inp) :
    inp.products = rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets :=
  (rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp h

theorem rssProductsChecked204_inhabited
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    ∃ checked : RssMlDsaAttemptInput, RssProductsChecked204 chalHash sampleInBall st checked := by
  refine ⟨{ inp with products := rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets }, ?_⟩
  exact (rssProductsValid_eq_true_iff chalHash sampleInBall st _).mpr rfl

theorem tooth_toprfActiveCross204_forgery :
    toprfActiveCross204 0 (fun _ _ _ _ => some Goldilocks.one) [] 0 1 Goldilocks.zero ≠
      some Goldilocks.one := by
  rw [toprfActiveCross204_correct]
  intro h
  exact gold_one_ne_zero204 (Option.some.inj h).symm


/-- A corrupt *consumed* response product is rejected by the signing state machine itself,
    while its attempt is burned. This tests the checker/consumer connection. -/
theorem tooth_rssThresholdSignStep_corrupt_product
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (hep : inp.epoch = st.epoch) (hatt : inp.attempt = st.nextAttempt)
    (hbad : inp.products.cs1 ≠ (rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets).cs1) :
    rssThresholdSignStep chalHash sampleInBall st inp =
      .err { st with nextAttempt := st.nextAttempt + 1 } .mpcSacrificeFailed := by
  unfold rssThresholdSignStep rssSignCore
  rw [decide_eq_true ⟨hep, hatt⟩,
    tooth_rssProductsValid_corrupted_output chalHash sampleInBall st inp hbad]

/-- Acceptance of the byte verifier enforces the same response and hint bounds as the
    algebraic core, on the *decoded wire signature*. -/
theorem mldsaVerifyBytes204_bounds (budget : Nat) (pk msg ctx sig : List UInt8)
    (h : mldsaVerifyBytes204 budget pk msg ctx sig = true) :
    ∃ decoded : DecodedSignature204,
      decodeSignature204 sig = some decoded ∧
      infNormVec4 decoded.z < mldsa44Gamma1 - mldsa44Beta ∧
      hintWeightVec4 decoded.hints ≤ mldsa44Omega := by
  unfold mldsaVerifyBytes204 at h
  split at h
  · cases h
  · cases ha : expandA204 budget (pk.take 32) with
    | none => simp only [ha] at h; cases h
    | some A =>
      cases hd : decodeSignature204 sig with
      | none => simp only [ha, hd] at h; cases h
      | some decoded =>
        rw [ha, hd] at h
        dsimp only at h
        cases hc : sampleInBall204 budget decoded.challenge with
        | none => simp [hc] at h
        | some c =>
          rw [hc] at h
          simp only [mldsaVerify, Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨decoded, rfl, h.1.1, h.1.2⟩


/-! ## Constructive transport certificates and production group scheduling -/

structure ToprfCollisionWitness204 (H : List UInt8 → List UInt8) where
  left : List UInt8
  right : List UInt8
  distinct : left ≠ right
  sameDigest : H left = H right

/-- The bad first vector is already present in the received message. No witness
is chosen from a propositional existential. -/
def toprfDecodeExtract204
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (i j : Fin 5) (honest : List Goldilocks)
    (m0 m1 : Option (List Goldilocks)) (md : Option (List UInt8))
    (cert : decodeGroupLarge H ctx layer i j m0 m1 md = some honest ∨
      ∃ forged, m0 = some forged ∧ forged ≠ honest ∧
        toprfGroupDigestPreimage ctx layer i j forged ≠
          toprfGroupDigestPreimage ctx layer i j honest ∧
        H (toprfGroupDigestPreimage ctx layer i j forged) =
          H (toprfGroupDigestPreimage ctx layer i j honest)) :
    PSum (decodeGroupLarge H ctx layer i j m0 m1 md = some honest)
      (ToprfCollisionWitness204 H) :=
  if h : decodeGroupLarge H ctx layer i j m0 m1 md = some honest then .inl h
  else .inr {
    left := toprfGroupDigestPreimage ctx layer i j (m0.getD [])
    right := toprfGroupDigestPreimage ctx layer i j honest
    distinct := by
      rcases cert with ok | ⟨v, hv, _, hn, _⟩
      · exact False.elim (h ok)
      · simpa only [hv, Option.getD_some] using hn
    sameDigest := by
      rcases cert with ok | ⟨v, hv, _, _, he⟩
      · exact False.elim (h ok)
      · simpa only [hv, Option.getD_some] using he }

/-- Sorted value senders after removing the rotating digest sender. -/
def toprfGroupRoles204 (i j : Fin 5) : Fin 5 × Fin 5 × Fin 5 :=
  let hs := toprfHolders i j
  match (i.val + j.val) % 3 with
  | 0 => (hs.getD 1 0, hs.getD 2 0, hs.getD 0 0)
  | 1 => (hs.getD 0 0, hs.getD 2 0, hs.getD 1 0)
  | _ => (hs.getD 0 0, hs.getD 1 0, hs.getD 2 0)

theorem toprfGroupRoles204_distinct (i j : Fin 5) :
    (toprfGroupRoles204 i j).1 ≠ (toprfGroupRoles204 i j).2.1 ∧
    (toprfGroupRoles204 i j).1 ≠ (toprfGroupRoles204 i j).2.2 ∧
    (toprfGroupRoles204 i j).2.1 ≠ (toprfGroupRoles204 i j).2.2 := by
  revert i j
  decide

theorem toprfGroupRoles204_digest (i j : Fin 5) :
    (toprfGroupRoles204 i j).2.2 =
      (toprfHolders i j).getD ((i.val + j.val) % 3) 0 := by
  revert i j
  decide

/-- Rust's four-gate threshold and rotating digest holder, for a vector of
arbitrary length (not a single-term surrogate). -/
def toprfGroupTransport204 (H : List UInt8 → List UInt8) (ctx : List UInt8)
    (layer : UInt64) (i j bad : Fin 5) (honest : List Goldilocks)
    (fault : Option (List Goldilocks)) (faultDigest : Option (List UInt8)) :
    Option (List Goldilocks) :=
  let roles := toprfGroupRoles204 i j
  let message p := if p = bad then toprfBoundedVec204 fault else some honest
  if honest.length ≤ 4 then
    decodeGroupSmall (message roles.1) (message roles.2.1) (message roles.2.2)
  else
    decodeGroupLarge H ctx layer i j (message roles.1) (message roles.2.1)
      (if roles.2.2 = bad then faultDigest
       else some (toprfGroupDigest H ctx layer i j honest))

def toprfGroupTransport204_extract (H : List UInt8 → List UInt8) (ctx : List UInt8)
    (layer : UInt64) (i j bad : Fin 5) (honest : List Goldilocks)
    (fault : Option (List Goldilocks)) (faultDigest : Option (List UInt8))
    (hctx : ctx.length < 2 ^ 20) (hlen : honest.length < 2 ^ 20) :
    PSum (toprfGroupTransport204 H ctx layer i j bad honest fault faultDigest = some honest)
      (ToprfCollisionWitness204 H) := by
  obtain ⟨h01, h02, h12⟩ := toprfGroupRoles204_distinct i j
  let roles := toprfGroupRoles204 i j
  let message (p : Fin 5) := if p = bad then toprfBoundedVec204 fault else some honest
  have hm : ∀ p, p ≠ bad → message p = some honest :=
    fun p hp => ite_false_of hp _ _
  have hb : ∀ v, message roles.1 = some v → v.length < 2 ^ 20 := by
    intro v hv
    if h : roles.1 = bad then
      have hv' : toprfBoundedVec204 fault = some v := by simpa [message, h] using hv
      exact toprfBoundedVec204_bound hv'
    else
      rw [hm _ h] at hv
      cases hv
      exact hlen
  unfold toprfGroupTransport204
  split
  · exact .inl ((toprf_2of5_corrects_one_malicious_server H ctx layer i j hctx bad).1
      roles.1 roles.2.1 roles.2.2 honest _ _ _ h01 h02 h12
      (hm _) (hm _) (hm _))
  · exact toprfDecodeExtract204 H ctx layer i j honest _ _ _
      ((toprf_2of5_corrects_one_malicious_server H ctx layer i j hctx bad).2.1
        roles.1 roles.2.1 roles.2.2 honest _ _ _ h01 h02 h12 hlen hb
        (hm _) (hm _) (fun hp => ite_false_of hp _ _))

/-- The legacy single-term transport also has a data-valued extractor. -/
def toprfDigestCross204_extract
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (hCtx : ctx.length < 2 ^ 20) (bad : Fin 5)
    (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204)
    (gate : List Nat) (i j : Fin 5) (term : Goldilocks) :
    PSum (toprfDigestCross204 H ctx layer bad fault faultDigest gate i j term = some term)
      (ToprfCollisionWitness204 H) := by
  obtain ⟨h01, h02, h12⟩ := toprfThreeHoldersDistinct204 i j
  let message (p : Fin 5) :=
    if p = bad then toprfBoundedVec204 (fault gate i j term) else some [term]
  have hm : ∀ p, p ≠ bad → message p = some [term] := fun p hp => ite_false_of hp _ _
  have hb : ∀ v, message ((toprfHolders i j).getD 0 0) = some v → v.length < 2 ^ 20 := by
    intro v hv
    if h : (toprfHolders i j).getD 0 0 = bad then
      have hv' : toprfBoundedVec204 (fault gate i j term) = some v := by
        change (if (toprfHolders i j).getD 0 0 = bad then _ else _) = _ at hv
        rw [ite_true_of h] at hv
        exact hv
      exact toprfBoundedVec204_bound hv'
    else
      rw [hm _ h] at hv
      cases hv
      exact (by decide : (1 : Nat) < 2 ^ 20)
  have cert := (toprf_2of5_corrects_one_malicious_server H ctx layer i j hCtx bad).2.1
    ((toprfHolders i j).getD 0 0) ((toprfHolders i j).getD 1 0) ((toprfHolders i j).getD 2 0)
    [term] _ _
    (if (toprfHolders i j).getD 2 0 = bad then faultDigest gate i j term
      else some (toprfGroupDigest H ctx layer i j [term]))
    h01 h02 h12 (by decide : (1 : Nat) < 2 ^ 20) hb (hm _) (hm _) (fun hp => ite_false_of hp _ _)
  match toprfDecodeExtract204 H ctx layer i j [term] _ _ _ cert with
  | .inl h => exact .inl (by unfold toprfDigestCross204; rw [h])
  | .inr c => exact .inr c

/-- Sequence finitely many proof-producing checks; failure contains actual data. -/
def finiteChecks204 {E : Type} : {n : Nat} → {P : Fin n → Prop} →
    (∀ i, PSum (P i) E) → PSum (∀ i, P i) E
  | 0, _, _ => .inl (fun i => Fin.elim0 i)
  | n + 1, P, check =>
    match check 0 with
    | .inr e => .inr e
    | .inl h0 =>
      match finiteChecks204 (P := fun i : Fin n => P i.succ) (fun i => check i.succ) with
      | .inr e => .inr e
      | .inl hs => .inl (fun i => Fin.cases h0 hs i)


/-- Lift the data-valued cross-term certificate through every consumed term. -/
def toprfMulExtract204 {E : Type} (cross : ToprfCross204)
    (check : ∀ gate i j term, PSum (cross gate i j term = some term) E)
    (gate : List Nat) (x y : ToprfWire) (mask : Fin 5 → Fin 5 → Goldilocks) :
    PSum (toprfActiveMul204 cross gate x y mask = toprfMulWire x y mask) E := by
  match finiteChecks204 (fun c => check gate c c (Goldilocks.mul (x c) (y c))) with
  | .inr e => exact .inr e
  | .inl hd =>
    let incoming (c i : Fin 5) :
        PSum (i ≠ c → cross gate i c
          (Goldilocks.sub (Goldilocks.mul (x i) (y c)) (mask i c)) =
            some (Goldilocks.sub (Goldilocks.mul (x i) (y c)) (mask i c))) E :=
      if h : i = c then .inl (fun hn => False.elim (hn h))
      else match check gate i c (Goldilocks.sub (Goldilocks.mul (x i) (y c)) (mask i c)) with
        | .inr e => .inr e
        | .inl he => .inl (fun _ => he)
    match finiteChecks204 (fun c => finiteChecks204 (incoming c)) with
    | .inr e => exact .inr e
    | .inl hi =>
      exact .inl (by
        funext c
        have hm : (fin5Others c).map (fun i =>
            (cross gate i c (Goldilocks.sub (Goldilocks.mul (x i) (y c)) (mask i c))).getD
              Goldilocks.zero) =
            (fin5Others c).map (fun i => Goldilocks.sub (Goldilocks.mul (x i) (y c)) (mask i c)) := by
          apply List.map_congr_left
          intro i hmem
          have hn : i ≠ c := of_decide_eq_true (List.mem_filter.mp hmem).2
          rw [hi c i hn]
          rfl
        simp only [toprfActiveMul204, toprfMulWire, hd, hm, Option.getD_some])

def toprfSboxExtract204 {E : Type} (cross : ToprfCross204)
    (check : ∀ gate i j term, PSum (cross gate i j term = some term) E)
    (gate : List Nat) (w : ToprfWire) (m1 m2 m3 m4 : Fin 5 → Fin 5 → Goldilocks) :
    PSum (toprfActiveSbox204 cross gate w m1 m2 m3 m4 = toprfSboxWire w m1 m2 m3 m4) E := by
  let x2 := toprfMulWire w w m1
  let x3 := toprfMulWire x2 w m2
  let x4 := toprfMulWire x2 x2 m3
  match toprfMulExtract204 cross check (gate ++ [0]) w w m1 with
  | .inr e => exact .inr e
  | .inl h1 =>
    match toprfMulExtract204 cross check (gate ++ [1]) x2 w m2 with
    | .inr e => exact .inr e
    | .inl h2 =>
      match toprfMulExtract204 cross check (gate ++ [2]) x2 x2 m3 with
      | .inr e => exact .inr e
      | .inl h3 =>
        match toprfMulExtract204 cross check (gate ++ [3]) x3 x4 m4 with
        | .inr e => exact .inr e
        | .inl h4 =>
          exact .inl (by dsimp only [toprfActiveSbox204, toprfSboxWire]; rw [h1, h2, h3, h4])

def toprfCoord204 (i : Fin 12) (s : Poseidon2State12) : Goldilocks :=
  match i.val with
  | 0 => s.b0.x0 | 1 => s.b0.x1 | 2 => s.b0.x2 | 3 => s.b0.x3
  | 4 => s.b1.x0 | 5 => s.b1.x1 | 6 => s.b1.x2 | 7 => s.b1.x3
  | 8 => s.b2.x0 | 9 => s.b2.x1 | 10 => s.b2.x2 | _ => s.b2.x3

def toprfExtExtract204 {E : Type} (cross : ToprfCross204)
    (check : ∀ gate i j term, PSum (cross gate i j term = some term) E)
    (gate : List Nat) (m : Fin 12 → SboxMask4) (rc : Poseidon2State12) (st : ToprfState12) :
    PSum (toprfActiveExtRound204 cross gate m rc st = toprfExtRound m rc st) E := by
  match finiteChecks204 (fun i : Fin 12 => toprfSboxExtract204 cross check
    (gate ++ [i.val]) (fun c => toprfCoord204 i (toprfAddPublicState12 rc st c))
    (m i).m1 (m i).m2 (m i).m3 (m i).m4) with
  | .inr e => exact .inr e
  | .inl h =>
    exact .inl (by
      have h0 := h ⟨0, by decide⟩
      simp only [toprfCoord204] at h0
      have h1 := h ⟨1, by decide⟩
      simp only [toprfCoord204] at h1
      have h2 := h ⟨2, by decide⟩
      simp only [toprfCoord204] at h2
      have h3 := h ⟨3, by decide⟩
      simp only [toprfCoord204] at h3
      have h4 := h ⟨4, by decide⟩
      simp only [toprfCoord204] at h4
      have h5 := h ⟨5, by decide⟩
      simp only [toprfCoord204] at h5
      have h6 := h ⟨6, by decide⟩
      simp only [toprfCoord204] at h6
      have h7 := h ⟨7, by decide⟩
      simp only [toprfCoord204] at h7
      have h8 := h ⟨8, by decide⟩
      simp only [toprfCoord204] at h8
      have h9 := h ⟨9, by decide⟩
      simp only [toprfCoord204] at h9
      have h10 := h ⟨10, by decide⟩
      simp only [toprfCoord204] at h10
      have h11 := h ⟨11, by decide⟩
      simp only [toprfCoord204] at h11
      dsimp only [toprfActiveExtRound204, toprfExtRound]
      rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11])

def toprfIntExtract204 {E : Type} (cross : ToprfCross204)
    (check : ∀ gate i j term, PSum (cross gate i j term = some term) E)
    (gate : List Nat) (m : SboxMask4) (rc : Goldilocks) (st : ToprfState12) :
    PSum (toprfActiveIntRound204 cross gate m rc st = toprfIntRound m rc st) E := by
  match toprfSboxExtract204 cross check (gate ++ [0])
    (fun c => if c = 0 then Goldilocks.add (st 0).b0.x0 rc else (st c).b0.x0)
    m.m1 m.m2 m.m3 m.m4 with
  | .inr e => exact .inr e
  | .inl h => exact .inl (by dsimp only [toprfActiveIntRound204, toprfIntRound]; rw [h])

def toprfRoundsExtract204 {E A : Type}
    (actual ideal : Nat → A → ToprfState12 → ToprfState12)
    (check : ∀ r a st, PSum (actual r a st = ideal r a st) E) :
    ∀ (r : Nat) (rounds : List A) (st : ToprfState12),
      PSum (runToprfRoundsIdx actual r rounds st = runToprfRoundsIdx ideal r rounds st) E
  | _, [], _ => .inl rfl
  | r, a :: rest, st =>
    match check r a st with
    | .inr e => .inr e
    | .inl h =>
      match toprfRoundsExtract204 actual ideal check (r + 1) rest (ideal r a st) with
      | .inr e => .inr e
      | .inl hs => .inl (by simp only [runToprfRoundsIdx, h, hs])

/-- All 30 Poseidon rounds, with no global collision-freeness premise. -/
def toprfPermExtract204 {E : Type} (cross : ToprfCross204)
    (check : ∀ gate i j term, PSum (cross gate i j term = some term) E)
    (masks : ToprfPerm12Masks) (init : ToprfState12) :
    PSum (toprfActivePerm204 cross masks init = toprfEvalPerm12 masks init) E := by
  let s0 : ToprfState12 := fun c => applyME (init c)
  let s1 := runToprfRoundsIdx (fun r rc s => toprfExtRound (masks.initExt r) rc s)
    0 poseidon2InitialExtConsts s0
  let s2 := runToprfRoundsIdx (fun r rc s => toprfIntRound (masks.internal r) rc s)
    0 poseidon2InternalConsts s1
  match toprfRoundsExtract204 _ _
    (fun r rc st => toprfExtExtract204 cross check [0, r] (masks.initExt r) rc st)
    0 poseidon2InitialExtConsts s0 with
  | .inr e => exact .inr e
  | .inl h1 =>
    match toprfRoundsExtract204 _ _
      (fun r rc st => toprfIntExtract204 cross check [1, r] (masks.internal r) rc st)
      0 poseidon2InternalConsts s1 with
    | .inr e => exact .inr e
    | .inl h2 =>
      match toprfRoundsExtract204 _ _
        (fun r rc st => toprfExtExtract204 cross check [2, r] (masks.termExt r) rc st)
        0 poseidon2TerminalExtConsts s2 with
      | .inr e => exact .inr e
      | .inl h3 => exact .inl (by dsimp only [toprfActivePerm204, toprfEvalPerm12]; rw [h1, h2, h3])

def toprfDigestClient204_extract
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (hctx : ctx.length < 2 ^ 20) (bad : Fin 5)
    (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204)
    (masks : ToprfPerm12Masks) (keys inputs : Fin 5 → Lane4)
    (forgedFinal : Option (Fin 5 → Lane4)) :
    PSum (toprfActiveClient204 bad (toprfDigestCross204 H ctx layer bad fault faultDigest)
        masks keys inputs forgedFinal =
      some (toprfPlaintext (sumLane4Shares5 keys) (sumLane4Shares5 inputs)))
      (ToprfCollisionWitness204 H) := by
  match toprfPermExtract204 _ (toprfDigestCross204_extract H ctx layer hctx bad fault faultDigest)
    masks (toprfInitPrfState keys inputs) with
  | .inr collision => exact .inr collision
  | .inl h =>
    exact .inl (by
      unfold toprfActiveClient204
      rw [h]
      exact (toprf_2of5_corrects_one_malicious_server id [] 0 0 1 (by decide) bad).2.2
        masks keys inputs _ (fun p hp => ite_false_of hp _ _))


/-! ## Finite adaptive cross-term execution program -/

structure ToprfTraceCall204 where
  gate : List Nat
  sender : Fin 5
  receiver : Fin 5
  term : Goldilocks

abbrev ToprfTraceProgram204 (A : Type) := OracleComp ToprfTraceCall204 (Option Goldilocks) A

def toprfTraceOracle204 (cross : ToprfCross204) (q : ToprfTraceCall204) : Option Goldilocks :=
  cross q.gate q.sender q.receiver q.term

def toprfTraceCollect204 {A : Type} : (n : Nat) → (Fin n → ToprfTraceProgram204 A) →
    ToprfTraceProgram204 (Fin n → A)
  | 0, _ => .pure Fin.elim0
  | n + 1, f => (f 0).bind fun x =>
      (toprfTraceCollect204 n (fun i => f i.succ)).bind fun xs => .pure (Fin.cases x xs)

theorem eval_toprfTraceCollect204 {A : Type} (O : ToprfTraceCall204 → Option Goldilocks) :
    ∀ (n : Nat) (f : Fin n → ToprfTraceProgram204 A),
      evalOracleComp O (toprfTraceCollect204 n f) = fun i => evalOracleComp O (f i)
  | 0, _ => by funext i; exact Fin.elim0 i
  | n + 1, f => by
    simp only [toprfTraceCollect204, evalOracleComp_bind, evalOracleComp_pure,
      eval_toprfTraceCollect204 O n]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

def toprfTraceMul204 (gate : List Nat) (x y : ToprfWire)
    (mask : Fin 5 → Fin 5 → Goldilocks) : ToprfTraceProgram204 ToprfWire :=
  (toprfTraceCollect204 5 (fun c => toprfTraceCollect204 5 (fun i =>
    let term := if i = c then Goldilocks.mul (x i) (y c)
      else Goldilocks.sub (Goldilocks.mul (x i) (y c)) (mask i c)
    .query ⟨gate, i, c, term⟩ OracleComp.pure))).bind fun values =>
    .pure (fun c => Goldilocks.add
      (Goldilocks.add ((values c c).getD Goldilocks.zero)
        (sumGoldList ((fin5Others c).map (fun j => mask c j))))
      (sumGoldList ((fin5Others c).map (fun i => (values c i).getD Goldilocks.zero))))

theorem eval_toprfTraceMul204 (cross : ToprfCross204) (gate : List Nat) (x y : ToprfWire)
    (mask : Fin 5 → Fin 5 → Goldilocks) :
    evalOracleComp (toprfTraceOracle204 cross) (toprfTraceMul204 gate x y mask) =
      toprfActiveMul204 cross gate x y mask := by
  simp only [toprfTraceMul204, evalOracleComp_bind, eval_toprfTraceCollect204,
    evalOracleComp_query, evalOracleComp_pure, toprfTraceOracle204, ↓reduceIte]
  funext c
  unfold toprfActiveMul204
  congr 1
  congr 1
  apply List.map_congr_left
  intro i hi
  have hn : i ≠ c := of_decide_eq_true (List.mem_filter.mp hi).2
  simp only [hn, ↓reduceIte]

def toprfTraceSbox204 (gate : List Nat) (w : ToprfWire)
    (m1 m2 m3 m4 : Fin 5 → Fin 5 → Goldilocks) : ToprfTraceProgram204 ToprfWire :=
  (toprfTraceMul204 (gate ++ [0]) w w m1).bind fun x2 =>
  (toprfTraceMul204 (gate ++ [1]) x2 w m2).bind fun x3 =>
  (toprfTraceMul204 (gate ++ [2]) x2 x2 m3).bind fun x4 =>
    toprfTraceMul204 (gate ++ [3]) x3 x4 m4

theorem eval_toprfTraceSbox204 (cross : ToprfCross204) (gate : List Nat) (w : ToprfWire)
    (m1 m2 m3 m4 : Fin 5 → Fin 5 → Goldilocks) :
    evalOracleComp (toprfTraceOracle204 cross) (toprfTraceSbox204 gate w m1 m2 m3 m4) =
      toprfActiveSbox204 cross gate w m1 m2 m3 m4 := by
  simp only [toprfTraceSbox204, evalOracleComp_bind, eval_toprfTraceMul204, toprfActiveSbox204]

def toprfTraceExt204 (gate : List Nat) (m : Fin 12 → SboxMask4)
    (rc : Poseidon2State12) (st : ToprfState12) : ToprfTraceProgram204 ToprfState12 :=
  (toprfTraceCollect204 12 (fun i =>
    toprfTraceSbox204 (gate ++ [i.val])
      (fun c => toprfCoord204 i (toprfAddPublicState12 rc st c))
      (m i).m1 (m i).m2 (m i).m3 (m i).m4)).bind fun y =>
    .pure (fun c => applyME
      ⟨⟨y 0 c, y 1 c, y 2 c, y 3 c⟩,
       ⟨y 4 c, y 5 c, y 6 c, y 7 c⟩,
       ⟨y 8 c, y 9 c, y 10 c, y 11 c⟩⟩)

theorem eval_toprfTraceExt204 (cross : ToprfCross204) (gate : List Nat)
    (m : Fin 12 → SboxMask4) (rc : Poseidon2State12) (st : ToprfState12) :
    evalOracleComp (toprfTraceOracle204 cross) (toprfTraceExt204 gate m rc st) =
      toprfActiveExtRound204 cross gate m rc st := by
  simp only [toprfTraceExt204, evalOracleComp_bind, eval_toprfTraceCollect204,
    eval_toprfTraceSbox204, evalOracleComp_pure, toprfCoord204, toprfActiveExtRound204]
  rfl

def toprfTraceInt204 (gate : List Nat) (m : SboxMask4)
    (rc : Goldilocks) (st : ToprfState12) : ToprfTraceProgram204 ToprfState12 :=
  (toprfTraceSbox204 (gate ++ [0])
    (fun c => if c = 0 then Goldilocks.add (st 0).b0.x0 rc else (st c).b0.x0)
    m.m1 m.m2 m.m3 m.m4).bind fun y =>
    .pure (fun c => applyMI ⟨⟨y c, (st c).b0.x1, (st c).b0.x2, (st c).b0.x3⟩,
      (st c).b1, (st c).b2⟩)

theorem eval_toprfTraceInt204 (cross : ToprfCross204) (gate : List Nat)
    (m : SboxMask4) (rc : Goldilocks) (st : ToprfState12) :
    evalOracleComp (toprfTraceOracle204 cross) (toprfTraceInt204 gate m rc st) =
      toprfActiveIntRound204 cross gate m rc st := by
  simp only [toprfTraceInt204, evalOracleComp_bind, eval_toprfTraceSbox204,
    evalOracleComp_pure, toprfActiveIntRound204]

def toprfTraceRounds204 {A : Type} (round : Nat → A → ToprfState12 → ToprfTraceProgram204 ToprfState12) :
    Nat → List A → ToprfState12 → ToprfTraceProgram204 ToprfState12
  | _, [], st => .pure st
  | r, a :: rest, st => (round r a st).bind fun next => toprfTraceRounds204 round (r + 1) rest next

theorem eval_toprfTraceRounds204 {A : Type} (cross : ToprfCross204)
    (round : Nat → A → ToprfState12 → ToprfTraceProgram204 ToprfState12)
    (actual : Nat → A → ToprfState12 → ToprfState12)
    (h : ∀ r a st, evalOracleComp (toprfTraceOracle204 cross) (round r a st) = actual r a st) :
    ∀ (rounds : List A) (r : Nat) (st : ToprfState12),
      evalOracleComp (toprfTraceOracle204 cross) (toprfTraceRounds204 round r rounds st) =
        runToprfRoundsIdx actual r rounds st
  | [], _, _ => by rw [toprfTraceRounds204, evalOracleComp_pure]; rfl
  | a :: rest, r, st => by
    rw [toprfTraceRounds204, evalOracleComp_bind, h, eval_toprfTraceRounds204 cross round actual h]
    rfl

def toprfTracePerm204 (m : ToprfPerm12Masks) (init : ToprfState12) :
    ToprfTraceProgram204 ToprfState12 :=
  (toprfTraceRounds204 (fun r rc st => toprfTraceExt204 [0, r] (m.initExt r) rc st)
    0 poseidon2InitialExtConsts (fun c => applyME (init c))).bind fun s1 =>
  (toprfTraceRounds204 (fun r rc st => toprfTraceInt204 [1, r] (m.internal r) rc st)
    0 poseidon2InternalConsts s1).bind fun s2 =>
    toprfTraceRounds204 (fun r rc st => toprfTraceExt204 [2, r] (m.termExt r) rc st)
      0 poseidon2TerminalExtConsts s2

theorem eval_toprfTracePerm204 (cross : ToprfCross204) (m : ToprfPerm12Masks) (init : ToprfState12) :
    evalOracleComp (toprfTraceOracle204 cross) (toprfTracePerm204 m init) =
      toprfActivePerm204 cross m init := by
  simp only [toprfTracePerm204, evalOracleComp_bind,
    eval_toprfTraceRounds204 cross _ _ (fun r rc st => eval_toprfTraceExt204 cross [0, r] (m.initExt r) rc st),
    eval_toprfTraceRounds204 cross _ _ (fun r rc st => eval_toprfTraceInt204 cross [1, r] (m.internal r) rc st),
    eval_toprfTraceRounds204 cross _ _ (fun r rc st => eval_toprfTraceExt204 cross [2, r] (m.termExt r) rc st),
    toprfActivePerm204]

/-- The two digest inputs associated with a consumed transport call: its received first
value vector and its honest digest value. This finite overapproximation is independent of
which comparison fails, and contains at most two inputs per consumed cross-term call. -/
def toprfTraceCallInputs204 (ctx : List UInt8) (layer : UInt64) (bad : Fin 5)
    (fault : ToprfVecFault204) (q : ToprfTraceCall204) : List (List UInt8) :=
  let m0 := if (toprfHolders q.sender q.receiver).getD 0 0 = bad
    then toprfBoundedVec204 (fault q.gate q.sender q.receiver q.term) else some [q.term]
  [toprfGroupDigestPreimage ctx layer q.sender q.receiver (m0.getD []),
   toprfGroupDigestPreimage ctx layer q.sender q.receiver [q.term]]

structure ToprfObservedCollision204 (H : List UInt8 → List UInt8)
    (inputs : List (List UInt8)) extends ToprfCollisionWitness204 H where
  left_mem : left ∈ inputs
  right_mem : right ∈ inputs

def toprfDecodeObserved204
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (i j : Fin 5) (honest : List Goldilocks)
    (m0 m1 : Option (List Goldilocks)) (md : Option (List UInt8))
    (cert : decodeGroupLarge H ctx layer i j m0 m1 md = some honest ∨
      ∃ forged, m0 = some forged ∧ forged ≠ honest ∧
        toprfGroupDigestPreimage ctx layer i j forged ≠
          toprfGroupDigestPreimage ctx layer i j honest ∧
        H (toprfGroupDigestPreimage ctx layer i j forged) =
          H (toprfGroupDigestPreimage ctx layer i j honest)) :
    PSum (decodeGroupLarge H ctx layer i j m0 m1 md = some honest)
      (ToprfObservedCollision204 H
        [toprfGroupDigestPreimage ctx layer i j (m0.getD []),
         toprfGroupDigestPreimage ctx layer i j honest]) :=
  if h : decodeGroupLarge H ctx layer i j m0 m1 md = some honest then .inl h
  else .inr {
    left := toprfGroupDigestPreimage ctx layer i j (m0.getD [])
    right := toprfGroupDigestPreimage ctx layer i j honest
    distinct := by
      rcases cert with ok | ⟨v, hv, _, hn, _⟩
      · exact False.elim (h ok)
      · simpa only [hv, Option.getD_some] using hn
    sameDigest := by
      rcases cert with ok | ⟨v, hv, _, _, he⟩
      · exact False.elim (h ok)
      · simpa only [hv, Option.getD_some] using he
    left_mem := .head _
    right_mem := .tail _ (.head _) }

def toprfDigestCross204_extract_observed
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (hCtx : ctx.length < 2 ^ 20) (bad : Fin 5)
    (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204) (q : ToprfTraceCall204) :
    PSum (toprfDigestCross204 H ctx layer bad fault faultDigest q.gate q.sender q.receiver q.term = some q.term)
      (ToprfObservedCollision204 H (toprfTraceCallInputs204 ctx layer bad fault q)) := by
  obtain ⟨h01, h02, h12⟩ := toprfThreeHoldersDistinct204 q.sender q.receiver
  let message (p : Fin 5) :=
    if p = bad then toprfBoundedVec204 (fault q.gate q.sender q.receiver q.term) else some [q.term]
  have hm : ∀ p, p ≠ bad → message p = some [q.term] := fun p hp => ite_false_of hp _ _
  have hb : ∀ v, message ((toprfHolders q.sender q.receiver).getD 0 0) = some v → v.length < 2 ^ 20 := by
    intro v hv
    if h : (toprfHolders q.sender q.receiver).getD 0 0 = bad then
      have hv' : toprfBoundedVec204 (fault q.gate q.sender q.receiver q.term) = some v := by
        simpa only [message, h, ↓reduceIte] using hv
      exact toprfBoundedVec204_bound hv'
    else
      rw [hm _ h] at hv
      cases hv
      exact (by decide : (1 : Nat) < 2 ^ 20)
  have cert := (toprf_2of5_corrects_one_malicious_server H ctx layer q.sender q.receiver hCtx bad).2.1
    ((toprfHolders q.sender q.receiver).getD 0 0)
    ((toprfHolders q.sender q.receiver).getD 1 0)
    ((toprfHolders q.sender q.receiver).getD 2 0) [q.term] _ _
    (if (toprfHolders q.sender q.receiver).getD 2 0 = bad then faultDigest q.gate q.sender q.receiver q.term
      else some (toprfGroupDigest H ctx layer q.sender q.receiver [q.term]))
    h01 h02 h12 (by decide : (1 : Nat) < 2 ^ 20) hb (hm _) (hm _) (fun hp => ite_false_of hp _ _)
  match toprfDecodeObserved204 H ctx layer q.sender q.receiver [q.term] _ _ _ cert with
  | .inl h => exact .inl (by unfold toprfDigestCross204; rw [h])
  | .inr c => exact .inr c

/-- Audit the consumed call log. A failure carries both concrete inputs and their membership
in the full finite transport-input table, rather than an unrestricted hash-collision existential. -/
def toprfAuditTrace204
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (hCtx : ctx.length < 2 ^ 20) (bad : Fin 5)
    (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204) :
    (calls : List ToprfTraceCall204) →
    PSum (∀ q ∈ calls,
      toprfDigestCross204 H ctx layer bad fault faultDigest q.gate q.sender q.receiver q.term = some q.term)
      (ToprfObservedCollision204 H (calls.flatMap (toprfTraceCallInputs204 ctx layer bad fault)))
  | [] => .inl (fun _ h => False.elim (List.not_mem_nil h))
  | q :: rest =>
    match toprfDigestCross204_extract_observed H ctx layer hCtx bad fault faultDigest q with
    | .inr c => .inr {
        toToprfCollisionWitness204 := c.toToprfCollisionWitness204
        left_mem := List.mem_flatMap.mpr ⟨q, .head _, c.left_mem⟩
        right_mem := List.mem_flatMap.mpr ⟨q, .head _, c.right_mem⟩ }
    | .inl hq =>
      match toprfAuditTrace204 H ctx layer hCtx bad fault faultDigest rest with
      | .inr c => .inr {
          toToprfCollisionWitness204 := c.toToprfCollisionWitness204
          left_mem := List.mem_append_right _ c.left_mem
          right_mem := List.mem_append_right _ c.right_mem }
      | .inl hs => .inl (fun t ht => by
          rcases List.mem_cons.mp ht with he | he
          · cases he; exact hq
          · exact hs t he)

def toprfDigestObservedInputs204 (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (bad : Fin 5) (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204)
    (masks : ToprfPerm12Masks) (keys inputs : Fin 5 → Lane4) : List (List UInt8) :=
  (queryLog (toprfTraceOracle204 (toprfDigestCross204 H ctx layer bad fault faultDigest))
    (toprfTracePerm204 masks (toprfInitPrfState keys inputs))).flatMap
      (toprfTraceCallInputs204 ctx layer bad fault)

/-- Full 30-round client execution: either the output is correct, or the execution yields an
explicit collision whose two inputs are in its finite observed transport-input table. -/
def toprfDigestClient204_extract_observed
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (hCtx : ctx.length < 2 ^ 20) (bad : Fin 5)
    (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204)
    (masks : ToprfPerm12Masks) (keys inputs : Fin 5 → Lane4)
    (forgedFinal : Option (Fin 5 → Lane4)) :
    PSum (toprfActiveClient204 bad (toprfDigestCross204 H ctx layer bad fault faultDigest)
        masks keys inputs forgedFinal =
      some (toprfPlaintext (sumLane4Shares5 keys) (sumLane4Shares5 inputs)))
      (ToprfObservedCollision204 H
        (toprfDigestObservedInputs204 H ctx layer bad fault faultDigest masks keys inputs)) := by
  let actual := toprfDigestCross204 H ctx layer bad fault faultDigest
  let ideal : ToprfCross204 := fun _ _ _ term => some term
  let program := toprfTracePerm204 masks (toprfInitPrfState keys inputs)
  match toprfAuditTrace204 H ctx layer hCtx bad fault faultDigest
      (queryLog (toprfTraceOracle204 actual) program) with
  | .inr c => exact .inr c
  | .inl h =>
    have hp := evalOracleComp_agree_on_queryLog (toprfTraceOracle204 actual)
      (toprfTraceOracle204 ideal) program h
    rw [eval_toprfTracePerm204, eval_toprfTracePerm204] at hp
    have he := hp.trans (toprfActivePerm204_eq ideal (fun _ _ _ _ => rfl) masks _)
    exact .inl (by
      unfold toprfActiveClient204
      rw [he]
      exact (toprf_2of5_corrects_one_malicious_server id [] 0 0 1 (by decide) bad).2.2
        masks keys inputs _ (fun p hp => ite_false_of hp _ _))

theorem toprfDigestClient204_correct_of_collision_free
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (hCtx : ctx.length < 2 ^ 20) (bad : Fin 5)
    (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204)
    (masks : ToprfPerm12Masks) (keys inputs : Fin 5 → Lane4)
    (forgedFinal : Option (Fin 5 → Lane4))
    (hFree : ∀ a ∈ toprfDigestObservedInputs204 H ctx layer bad fault faultDigest masks keys inputs,
      ∀ b ∈ toprfDigestObservedInputs204 H ctx layer bad fault faultDigest masks keys inputs,
      H a = H b → a = b) :
    toprfActiveClient204 bad (toprfDigestCross204 H ctx layer bad fault faultDigest)
        masks keys inputs forgedFinal =
      some (toprfPlaintext (sumLane4Shares5 keys) (sumLane4Shares5 inputs)) := by
  match toprfDigestClient204_extract_observed H ctx layer hCtx bad fault faultDigest masks keys inputs forgedFinal with
  | .inl h => exact h
  | .inr c => exact False.elim (c.distinct (hFree _ c.left_mem _ c.right_mem c.sameDigest))

#verify_constructive toprfDigestClient204_correct_of_collision_free

/-- There are two candidate digest inputs per cross-term call in the finite adaptive log. -/
theorem toprfTraceInputs204_length (ctx : List UInt8) (layer : UInt64) (bad : Fin 5)
    (fault : ToprfVecFault204) : ∀ calls : List ToprfTraceCall204,
    (calls.flatMap (toprfTraceCallInputs204 ctx layer bad fault)).length = 2 * calls.length
  | [] => rfl
  | q :: rest => by
    rw [List.flatMap_cons, List.length_append, toprfTraceInputs204_length ctx layer bad fault rest]
    change 2 + 2 * rest.length = 2 * (rest.length + 1)
    omega

theorem toprfDigestObservedInputs204_length (H : List UInt8 → List UInt8) (ctx : List UInt8)
    (layer : UInt64) (bad : Fin 5) (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204)
    (masks : ToprfPerm12Masks) (keys inputs : Fin 5 → Lane4) :
    (toprfDigestObservedInputs204 H ctx layer bad fault faultDigest masks keys inputs).length =
      2 * (queryLog (toprfTraceOracle204 (toprfDigestCross204 H ctx layer bad fault faultDigest))
        (toprfTracePerm204 masks (toprfInitPrfState keys inputs))).length :=
  toprfTraceInputs204_length ctx layer bad fault _

/-! ## Authenticated replicated shares and a masked rejection observation

This local view model includes both held components and their MAC shares.
It describes a uniform sharing experiment; seed expansion and a distributed
implementation refinement remain separate obligations.
-/

structure RssAuthShare204 where
  value : Fq204
  mac : Fq204
  deriving DecidableEq

abbrev RssAuthCoins204 := RssAuthShare204 × RssAuthShare204

def rssNextParty204 (p : Fin 3) : Fin 3 := ⟨(p.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
def rssLastParty204 (p : Fin 3) : Fin 3 := ⟨(p.val + 2) % 3, Nat.mod_lt _ (by decide)⟩

private theorem rssPartyIndices204 (p : Fin 3) :
    rssNextParty204 p ≠ p ∧ rssLastParty204 p ≠ p ∧ rssLastParty204 p ≠ rssNextParty204 p := by
  revert p
  decide

/-- Party `p` holds the two components other than `p`. Both the value and MAC
sum are completed at the missing component. -/
def rssAuthSharing204 (p : Fin 3) (key secret : Fq204) (r : RssAuthCoins204) :
    Fin 3 → RssAuthShare204 := fun i =>
  if i = p then
    ⟨Fq204.sub (Fq204.sub secret r.1.value) r.2.value,
     Fq204.sub (Fq204.sub (Fq204.mul key secret) r.1.mac) r.2.mac⟩
  else if i = rssNextParty204 p then r.1 else r.2

def rssAuthPartyView204 (p : Fin 3) (shares : Fin 3 → RssAuthShare204) : RssAuthCoins204 :=
  (shares (rssNextParty204 p), shares (rssLastParty204 p))

theorem rssAuthPartyView204_simulated (p : Fin 3) (key secret : Fq204) (r : RssAuthCoins204) :
    rssAuthPartyView204 p (rssAuthSharing204 p key secret r) = r := by
  obtain ⟨h1, h2, h3⟩ := rssPartyIndices204 p
  simp only [rssAuthPartyView204, rssAuthSharing204, ite_false_of h1, ite_false_of h2,
    ite_false_of h3, ite_true]

private theorem fq_sub_sub_add_add204 (s a b : Fq204) :
    Fq204.add (Fq204.add (Fq204.sub (Fq204.sub s a) b) a) b = s := by
  rw [← Fq204.ofInt_nat s, ← Fq204.ofInt_nat a, ← Fq204.ofInt_nat b]
  simp only [Fq204.ofInt_sub, Fq204.ofInt_add]
  congr 1
  omega

/-- Reconstruction of both channels establishes the global MAC invariant. -/
theorem rssAuthSharing204_reconstruct (p : Fin 3) (key secret : Fq204) (r : RssAuthCoins204) :
    let sh := rssAuthSharing204 p key secret r
    Fq204.add (Fq204.add (sh p).value (sh (rssNextParty204 p)).value)
      (sh (rssLastParty204 p)).value = secret ∧
    Fq204.add (Fq204.add (sh p).mac (sh (rssNextParty204 p)).mac)
      (sh (rssLastParty204 p)).mac = Fq204.mul key secret := by
  obtain ⟨h1, h2, h3⟩ := rssPartyIndices204 p
  simp only [rssAuthSharing204, ite_false_of h1, ite_false_of h2, ite_false_of h3,
    ite_true, fq_sub_sub_add_add204, and_self]

/-- The observation before unmasking the rejection bit. Revealing the bit
itself is deliberately not claimed private. -/
def rssMaskedRejectView204 (p : Fin 3) (key secret : Fq204) (reject : Bool)
    (coins : RssAuthCoins204 × Bool) : RssAuthCoins204 × Bool :=
  (rssAuthPartyView204 p (rssAuthSharing204 p key secret coins.1), reject.xor coins.2)

def rssRejectCoinBijection204 (a b : Bool) :
    SimpleEquiv (RssAuthCoins204 × Bool) (RssAuthCoins204 × Bool) where
  toFun c := (c.1, b.xor (a.xor c.2))
  invFun c := (c.1, a.xor (b.xor c.2))
  left_inv c := by rcases c with ⟨r, m⟩; cases a <;> cases b <;> cases m <;> rfl
  right_inv c := by rcases c with ⟨r, m⟩; cases a <;> cases b <;> cases m <;> rfl

/-- One coin bijection preserves the joint per-party share/MAC view and the
masked rejection bit, even when rejection depends arbitrarily on the secret. -/
theorem rssMaskedRejectView204_private (p : Fin 3) (key s t : Fq204)
    (reject : Fq204 → Bool) (c : RssAuthCoins204 × Bool) :
    rssMaskedRejectView204 p key s (reject s) c =
      rssMaskedRejectView204 p key t (reject t)
        ((rssRejectCoinBijection204 (reject s) (reject t)).toFun c) := by
  simp only [rssMaskedRejectView204, rssAuthPartyView204_simulated, rssRejectCoinBijection204]
  rcases c with ⟨r, m⟩
  cases reject s <;> cases reject t <;> cases m <;> rfl


/-! ## Binary modular powers and Rabin unit certificates for the extension

The normal form of `X^n` modulo `X^6 - 7` is `7^(n/6) X^(n%6)`.
The certificates below provide quotient-ring inverses of `X^(q^2)-X` and
`X^(q^3)-X`, and the sixth Frobenius identity. The section after them turns the same
Frobenius scalars into an inverse for every nonzero element.
-/

def ext6Monomial204 (degree : Nat) (coefficient : Fq204) : Ext6Fq204 :=
  match degree with
  | 0 => ⟨coefficient, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩
  | 1 => ⟨Fq204.zero, coefficient, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩
  | 2 => ⟨Fq204.zero, Fq204.zero, coefficient, Fq204.zero, Fq204.zero, Fq204.zero⟩
  | 3 => ⟨Fq204.zero, Fq204.zero, Fq204.zero, coefficient, Fq204.zero, Fq204.zero⟩
  | 4 => ⟨Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, coefficient, Fq204.zero⟩
  | _ => ⟨Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, coefficient⟩

def ext6XPower204 (n : Nat) : Ext6Fq204 :=
  ext6Monomial204 (n % 6) (Fq204.pow (Fq204.ofNat 7) (n / 6))

/-- Logarithmic coefficient exponentiation for the binomial normal form. -/
def ext6XPowerFast204 (fuel n : Nat) : Ext6Fq204 :=
  ext6Monomial204 (n % 6) (Fq204.ofNat (modPowFuel fuel 7 (n / 6) mldsaQ))

theorem ext6XPowerFast204_correct (fuel n : Nat) (h : n / 6 < 2 ^ fuel) :
    ext6XPowerFast204 fuel n = ext6XPower204 n := by
  unfold ext6XPowerFast204 ext6XPower204
  congr 1
  apply Fq204.ext
  rw [Fq204.ofNat_val, modPowFuel_eq_pow_mod fuel 7 (n / 6) mldsaQ h,
    Nat.mod_mod, Fq204.pow_val]
  rfl

theorem ext6XPower204_succ (n : Nat) :
    ext6Mul (ext6XPower204 n) (ext6Monomial204 1 Fq204.one) = ext6XPower204 (n + 1) := by
  have hr : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hr with h | h | h | h | h | h
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 1 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero]
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 2 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 3 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 4 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 5 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  · have hd : (n + 1) / 6 = n / 6 + 1 := by omega
    have hm : (n + 1) % 6 = 0 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
    rw [Fq204.pow, Fq204.mul_comm]
    rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Explicit units modulo the actual multiplication law; these are the two
coprimality certificates required for degree six. -/
theorem ext6RabinUnits204 :
    ext6Mul (ext6Sub (ext6XPowerFast204 160 (mldsaQ ^ 2)) (ext6Monomial204 1 Fq204.one))
      (ext6Monomial204 5 (Fq204.ofNat 2748270)) = ext6EmbedFq Fq204.one ∧
    ext6Mul (ext6Sub (ext6XPowerFast204 160 (mldsaQ ^ 3)) (ext6Monomial204 1 Fq204.one))
      (ext6Monomial204 5 (Fq204.ofNat 2993006)) = ext6EmbedFq Fq204.one ∧
    ext6XPowerFast204 160 (mldsaQ ^ 6) = ext6Monomial204 1 Fq204.one := by
  have h2 : ext6XPowerFast204 160 (mldsaQ ^ 2) = ext6Monomial204 1 (Fq204.ofNat 949247) := by decide
  have h3 : ext6XPowerFast204 160 (mldsaQ ^ 3) = ext6Monomial204 1 (Fq204.ofNat 8380416) := by decide
  have h6 : ext6XPowerFast204 160 (mldsaQ ^ 6) = ext6Monomial204 1 Fq204.one := by decide
  rw [h2, h3, h6]
  decide


/-- The same certificates for powers characterized by the multiplication
recurrence, rather than just for the fast evaluator. -/
theorem ext6RabinCertificate204 :
    ext6Mul (ext6Sub (ext6XPower204 (mldsaQ ^ 2)) (ext6Monomial204 1 Fq204.one))
      (ext6Monomial204 5 (Fq204.ofNat 2748270)) = ext6EmbedFq Fq204.one ∧
    ext6Mul (ext6Sub (ext6XPower204 (mldsaQ ^ 3)) (ext6Monomial204 1 Fq204.one))
      (ext6Monomial204 5 (Fq204.ofNat 2993006)) = ext6EmbedFq Fq204.one ∧
    ext6XPower204 (mldsaQ ^ 6) = ext6Monomial204 1 Fq204.one := by
  rw [← ext6XPowerFast204_correct 160 (mldsaQ ^ 2) (by decide),
    ← ext6XPowerFast204_correct 160 (mldsaQ ^ 3) (by decide),
    ← ext6XPowerFast204_correct 160 (mldsaQ ^ 6) (by decide)]
  exact ext6RabinUnits204


/-! ## The extension ring is a field

`Ext6Fq204` is `F_q[X]/(X^6 - 7)`. The `q`-th power map is a ring endomorphism in
characteristic `q` (`ext6Pow_add_frobenius`), fixes the base field
(`ext6Pow_embed_frobenius`), and sends `X` to `ζ X` with `ζ = 7^((q-1)/6)`, so it acts on
coordinates by `a_i ↦ ζ^i a_i` (`ext6Pow_frobenius`). The Rabin conditions say that
`X^(q^2) ≠ X` and `X^(q^3) ≠ X` while `X^(q^6) = X`; in coordinates, an element fixed by
the second and third Frobenius iterates is a base-field constant
(`ext6_rabin_fixed_is_constant`). The norm `a · a^q ⋯ a^(q^5)` is such an element and is
nonzero when `a` is, which gives an explicit inverse (`ext6Inv`, `ext6Mul_inv_cancel`),
zero-divisor freedom (`ext6Mul_eq_zero`) and irreducibility of the modulus
(`ext6Modulus_irreducible`).
-/

section Ext6Field

local instance : Std.Associative Fq204.add := ⟨Fq204.add_assoc⟩
local instance : Std.Commutative Fq204.add := ⟨Fq204.add_comm⟩
local instance : Std.Associative Fq204.mul := ⟨Fq204.mul_assoc⟩
local instance : Std.Commutative Fq204.mul := ⟨Fq204.mul_comm⟩

def ext6One : Ext6Fq204 := ext6EmbedFq Fq204.one

theorem ext6Add_assoc (x y z : Ext6Fq204) :
    ext6Add (ext6Add x y) z = ext6Add x (ext6Add y z) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  rcases z with ⟨z0, z1, z2, z3, z4, z5⟩
  simp only [ext6Add, Fq204.add_assoc]

theorem ext6Add_comm (x y : Ext6Fq204) : ext6Add x y = ext6Add y x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  simp only [ext6Add, Ext6Fq204.mk.injEq]
  exact ⟨Fq204.add_comm _ _, Fq204.add_comm _ _, Fq204.add_comm _ _, Fq204.add_comm _ _,
    Fq204.add_comm _ _, Fq204.add_comm _ _⟩

theorem ext6Add_zero (x : Ext6Fq204) : ext6Add x ext6Zero = x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Add, ext6Zero, Fq204.add_zero]

theorem ext6Zero_add (x : Ext6Fq204) : ext6Add ext6Zero x = x := by
  rw [ext6Add_comm, ext6Add_zero]

theorem ext6Add_add_add_comm (a b c d : Ext6Fq204) :
    ext6Add (ext6Add a b) (ext6Add c d) = ext6Add (ext6Add a c) (ext6Add b d) := by
  rw [ext6Add_assoc, ext6Add_assoc, ← ext6Add_assoc b c d, ext6Add_comm b c,
    ext6Add_assoc c b d]

local instance : Std.Associative ext6Add := ⟨ext6Add_assoc⟩
local instance : Std.Commutative ext6Add := ⟨ext6Add_comm⟩

theorem ext6Mul_comm (x y : Ext6Fq204) : ext6Mul x y = ext6Mul y x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  simp only [ext6Mul, Ext6Fq204.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ac_rfl

set_option maxHeartbeats 4000000 in
theorem ext6Mul_assoc (x y z : Ext6Fq204) :
    ext6Mul (ext6Mul x y) z = ext6Mul x (ext6Mul y z) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  rcases z with ⟨z0, z1, z2, z3, z4, z5⟩
  simp only [ext6Mul, Ext6Fq204.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Fq204.left_distrib, Fq204.right_distrib]; ac_rfl)

theorem ext6Mul_add (x y z : Ext6Fq204) :
    ext6Mul x (ext6Add y z) = ext6Add (ext6Mul x y) (ext6Mul x z) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  rcases z with ⟨z0, z1, z2, z3, z4, z5⟩
  simp only [ext6Mul, ext6Add, Ext6Fq204.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Fq204.left_distrib]; ac_rfl)

theorem ext6Add_mul (x y z : Ext6Fq204) :
    ext6Mul (ext6Add x y) z = ext6Add (ext6Mul x z) (ext6Mul y z) := by
  rw [ext6Mul_comm, ext6Mul_add, ext6Mul_comm z x, ext6Mul_comm z y]

theorem ext6Mul_one (x : Ext6Fq204) : ext6Mul x ext6One = x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Mul, ext6One, ext6EmbedFq, Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero,
    Fq204.zero_add]

theorem ext6One_mul (x : Ext6Fq204) : ext6Mul ext6One x = x := by
  rw [ext6Mul_comm, ext6Mul_one]

theorem ext6Mul_zero (x : Ext6Fq204) : ext6Mul x ext6Zero = ext6Zero := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Mul, ext6Zero, Fq204.mul_zero, Fq204.add_zero]

theorem ext6Zero_mul (x : Ext6Fq204) : ext6Mul ext6Zero x = ext6Zero := by
  rw [ext6Mul_comm, ext6Mul_zero]

local instance : Std.Associative ext6Mul := ⟨ext6Mul_assoc⟩
local instance : Std.Commutative ext6Mul := ⟨ext6Mul_comm⟩

theorem ext6Scale_eq_mul_embed (x : Ext6Fq204) (s : Fq204) :
    ext6Scale x s = ext6Mul x (ext6EmbedFq s) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Mul, ext6Scale, ext6EmbedFq, Fq204.mul_zero, Fq204.add_zero, Fq204.zero_add]

theorem ext6Mul_scale_right (x y : Ext6Fq204) (s : Fq204) :
    ext6Mul x (ext6Scale y s) = ext6Scale (ext6Mul x y) s := by
  rw [ext6Scale_eq_mul_embed, ext6Scale_eq_mul_embed, ext6Mul_assoc]

theorem ext6Mul_scale_left (x y : Ext6Fq204) (s : Fq204) :
    ext6Mul (ext6Scale x s) y = ext6Scale (ext6Mul x y) s := by
  rw [ext6Mul_comm, ext6Mul_scale_right, ext6Mul_comm]

theorem ext6Scale_zero (x : Ext6Fq204) : ext6Scale x Fq204.zero = ext6Zero := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, ext6Zero, Fq204.mul_zero]

theorem ext6Scale_add_scalar (x : Ext6Fq204) (s t : Fq204) :
    ext6Scale x (Fq204.add s t) = ext6Add (ext6Scale x s) (ext6Scale x t) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, ext6Add, Fq204.left_distrib]

theorem ext6Scale_embed (c s : Fq204) :
    ext6Scale (ext6EmbedFq c) s = ext6EmbedFq (Fq204.mul c s) := by
  simp only [ext6Scale, ext6EmbedFq, Fq204.zero_mul]

theorem ext6Embed_add (a b : Fq204) :
    ext6EmbedFq (Fq204.add a b) = ext6Add (ext6EmbedFq a) (ext6EmbedFq b) := by
  simp only [ext6EmbedFq, ext6Add, Fq204.add_zero]

/-- Powers under the extension multiplication. -/
def ext6Pow (a : Ext6Fq204) : Nat → Ext6Fq204
  | 0 => ext6One
  | n + 1 => ext6Mul (ext6Pow a n) a

theorem ext6Pow_zero (a : Ext6Fq204) : ext6Pow a 0 = ext6One := by rfl

theorem ext6Pow_succ (a : Ext6Fq204) (n : Nat) :
    ext6Pow a (n + 1) = ext6Mul (ext6Pow a n) a := by rfl

theorem ext6Pow_one (a : Ext6Fq204) : ext6Pow a 1 = a := by
  rw [ext6Pow_succ, ext6Pow_zero, ext6One_mul]

theorem ext6Pow_add (a : Ext6Fq204) (m n : Nat) :
    ext6Pow a (m + n) = ext6Mul (ext6Pow a m) (ext6Pow a n) := by
  induction n with
  | zero => rw [Nat.add_zero, ext6Pow_zero, ext6Mul_one]
  | succ n ih => rw [← Nat.add_assoc, ext6Pow_succ, ext6Pow_succ, ih, ext6Mul_assoc]

theorem ext6Pow_mul (a : Ext6Fq204) (m n : Nat) :
    ext6Pow a (m * n) = ext6Pow (ext6Pow a m) n := by
  induction n with
  | zero => rw [Nat.mul_zero, ext6Pow_zero, ext6Pow_zero]
  | succ n ih => rw [Nat.mul_succ, ext6Pow_add, ih, ext6Pow_succ]

theorem ext6Mul_pow (a b : Ext6Fq204) (n : Nat) :
    ext6Pow (ext6Mul a b) n = ext6Mul (ext6Pow a n) (ext6Pow b n) := by
  induction n with
  | zero => rw [ext6Pow_zero, ext6Pow_zero, ext6Pow_zero, ext6Mul_one]
  | succ n ih =>
    rw [ext6Pow_succ, ext6Pow_succ, ext6Pow_succ, ih]
    ac_rfl

theorem ext6Pow_one_base (n : Nat) : ext6Pow ext6One n = ext6One := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ext6Pow_succ, ih, ext6Mul_one]

theorem ext6Pow_zero_base {n : Nat} (hn : 0 < n) : ext6Pow ext6Zero n = ext6Zero := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ext6Pow_succ, ext6Mul_zero]

theorem ext6Pow_scale (a : Ext6Fq204) (s : Fq204) (n : Nat) :
    ext6Pow (ext6Scale a s) n = ext6Scale (ext6Pow a n) (Fq204.pow s n) := by
  induction n with
  | zero =>
    rw [ext6Pow_zero, ext6Pow_zero]
    exact (ext6Scale_one _).symm
  | succ n ih =>
    rw [ext6Pow_succ, ext6Pow_succ, ih, ext6Mul_scale_right, ext6Mul_scale_left, ext6Scale_mul]
    rfl

/-! ### Binomial coefficients and the characteristic-`q` power of a sum -/

private def choose204 : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose204 n k + choose204 n (k + 1)

private theorem choose204_zero_right (n : Nat) : choose204 n 0 = 1 := by
  cases n <;> rfl

private theorem choose204_succ_succ (n k : Nat) :
    choose204 (n + 1) (k + 1) = choose204 n k + choose204 n (k + 1) := rfl

private theorem choose204_eq_zero_of_lt : ∀ (n k : Nat), n < k → choose204 n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose204_succ_succ, choose204_eq_zero_of_lt n k (by omega),
      choose204_eq_zero_of_lt n (k + 1) (by omega)]

private theorem choose204_self : ∀ n : Nat, choose204 n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [choose204_succ_succ, choose204_self n, choose204_eq_zero_of_lt n (n + 1) (by omega)]

private theorem choose204_one_right : ∀ n : Nat, choose204 n 1 = n
  | 0 => rfl
  | n + 1 => by
    rw [choose204_succ_succ, choose204_zero_right, choose204_one_right n]
    omega

private theorem succ_mul_choose204 :
    ∀ n k : Nat, (k + 1) * choose204 (n + 1) (k + 1) = (n + 1) * choose204 n k
  | 0, 0 => by decide
  | 0, k + 1 => by
    rw [choose204_succ_succ, choose204_eq_zero_of_lt 0 (k + 1) (by omega),
      choose204_eq_zero_of_lt 0 (k + 1 + 1) (by omega)]
    omega
  | n + 1, 0 => by
    rw [choose204_one_right, choose204_zero_right]
    omega
  | n + 1, k + 1 => by
    have h1 := succ_mul_choose204 n k
    have h2 := succ_mul_choose204 n (k + 1)
    rw [choose204_succ_succ (n + 1) (k + 1)]
    rw [choose204_succ_succ n k] at h1 ⊢
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul] at h1 h2 ⊢
    omega

private theorem mldsaQ_dvd_choose204 {k : Nat} (hk0 : 0 < k) (hk : k < mldsaQ) :
    mldsaQ ∣ choose204 mldsaQ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := succ_mul_choose204 (mldsaQ - 1) j
  have hq : mldsaQ - 1 + 1 = mldsaQ := by decide
  rw [hq] at h
  have hdvd : mldsaQ ∣ (j + 1) * choose204 mldsaQ (j + 1) := ⟨_, h⟩
  exact mldsaQ_isPrime.dvd_mul hdvd (fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega)

private theorem fq204_ofNat_add (a b : Nat) :
    Fq204.ofNat (a + b) = Fq204.add (Fq204.ofNat a) (Fq204.ofNat b) := by
  apply Fq204.ext
  rw [Fq204.add_val, Fq204.ofNat_val, Fq204.ofNat_val, Fq204.ofNat_val, ← Nat.add_mod]

private theorem fq204_ofNat_one : Fq204.ofNat 1 = Fq204.one := by decide

private theorem fq204_ofNat_zero : Fq204.ofNat 0 = Fq204.zero := by decide

private theorem fq204_ofNat_eq_zero_of_dvd {n : Nat} (h : mldsaQ ∣ n) :
    Fq204.ofNat n = Fq204.zero := by
  apply Fq204.ext
  rw [Fq204.ofNat_val, Nat.mod_eq_zero_of_dvd h]
  rfl

/-- `ext6Binom x y n k` is the degree-`k` term of `(x + y)^n`, built by Pascal's rule. -/
private def ext6Binom (x y : Ext6Fq204) : Nat → Nat → Ext6Fq204
  | 0, 0 => ext6One
  | 0, _ + 1 => ext6Zero
  | n + 1, 0 => ext6Mul (ext6Binom x y n 0) y
  | n + 1, k + 1 =>
    ext6Add (ext6Mul (ext6Binom x y n (k + 1)) y) (ext6Mul (ext6Binom x y n k) x)

private def ext6BinomSum (x y : Ext6Fq204) (n : Nat) : Nat → Ext6Fq204
  | 0 => ext6Zero
  | m + 1 => ext6Add (ext6BinomSum x y n m) (ext6Binom x y n m)

private theorem ext6BinomSum_succ (x y : Ext6Fq204) (n m : Nat) :
    ext6BinomSum x y n (m + 1) = ext6Add (ext6BinomSum x y n m) (ext6Binom x y n m) := rfl

private theorem ext6Binom_zero_succ (x y : Ext6Fq204) (k : Nat) :
    ext6Binom x y 0 (k + 1) = ext6Zero := rfl

private theorem ext6Binom_zero_zero (x y : Ext6Fq204) : ext6Binom x y 0 0 = ext6One := rfl

private theorem ext6BinomSum_zero (x y : Ext6Fq204) (n : Nat) :
    ext6BinomSum x y n 0 = ext6Zero := rfl

private theorem ext6Binom_succ_zero (x y : Ext6Fq204) (n : Nat) :
    ext6Binom x y (n + 1) 0 = ext6Mul (ext6Binom x y n 0) y := rfl

private theorem ext6Binom_succ_succ (x y : Ext6Fq204) (n k : Nat) :
    ext6Binom x y (n + 1) (k + 1) =
      ext6Add (ext6Mul (ext6Binom x y n (k + 1)) y) (ext6Mul (ext6Binom x y n k) x) := rfl

private theorem ext6BinomSum_succ_row (x y : Ext6Fq204) (n m : Nat) :
    ext6BinomSum x y (n + 1) (m + 1) =
      ext6Add (ext6Mul (ext6BinomSum x y n (m + 1)) y) (ext6Mul (ext6BinomSum x y n m) x) := by
  induction m with
  | zero =>
    rw [ext6BinomSum_succ, ext6BinomSum_succ, ext6Binom_succ_zero, ext6BinomSum_zero,
      ext6BinomSum_zero, ext6Zero_add, ext6Zero_add, ext6Zero_mul, ext6Add_zero]
  | succ m ih =>
    have hx : ext6Mul (ext6BinomSum x y n (m + 1)) x =
        ext6Add (ext6Mul (ext6BinomSum x y n m) x) (ext6Mul (ext6Binom x y n m) x) := by
      rw [ext6BinomSum_succ, ext6Add_mul]
    rw [ext6BinomSum_succ x y (n + 1), ih, ext6Binom_succ_succ,
      ext6BinomSum_succ x y n (m + 1), ext6Add_mul, hx]
    exact ext6Add_add_add_comm _ _ _ _

private theorem ext6Binom_closed (x y : Ext6Fq204) (n : Nat) :
    (∀ k, n < k → ext6Binom x y n k = ext6Zero) ∧
    (∀ k j, k + j = n → ext6Binom x y n k =
      ext6Scale (ext6Mul (ext6Pow x k) (ext6Pow y j)) (Fq204.ofNat (choose204 n k))) := by
  induction n with
  | zero =>
    refine ⟨fun k hk => ?_, fun k j h => ?_⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ext6Binom_zero_succ x y k'
    · have hk0 : k = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hk0
      subst hj0
      rw [ext6Pow_zero, ext6Pow_zero, ext6Mul_one, choose204_zero_right, fq204_ofNat_one,
        ext6Scale_one, ext6Binom_zero_zero]
  | succ n ih =>
    obtain ⟨ihZ, ihC⟩ := ih
    refine ⟨fun k hk => ?_, fun k j h => ?_⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [ext6Binom_succ_succ, ihZ (k' + 1) (by omega), ihZ k' (by omega), ext6Zero_mul,
        ext6Zero_mul, ext6Add_zero]
    · cases k with
      | zero =>
        have hj : j = n + 1 := by omega
        subst hj
        rw [ext6Binom_succ_zero, ihC 0 n (by omega), choose204_zero_right, choose204_zero_right,
          fq204_ofNat_one, ext6Scale_one, ext6Scale_one, ext6Pow_zero, ext6One_mul, ext6One_mul,
          ext6Pow_succ]
      | succ k' =>
        have hkj : k' + j = n := by omega
        have hSecond : ext6Mul (ext6Mul (ext6Pow x k') (ext6Pow y j)) x =
            ext6Mul (ext6Pow x (k' + 1)) (ext6Pow y j) := by
          rw [ext6Pow_succ, ext6Mul_assoc, ext6Mul_comm (ext6Pow y j) x, ← ext6Mul_assoc]
        have hFirst : ext6Mul (ext6Binom x y n (k' + 1)) y =
            ext6Scale (ext6Mul (ext6Pow x (k' + 1)) (ext6Pow y j))
              (Fq204.ofNat (choose204 n (k' + 1))) := by
          cases j with
          | zero =>
            rw [ihZ (k' + 1) (by omega), choose204_eq_zero_of_lt n (k' + 1) (by omega),
              fq204_ofNat_zero, ext6Scale_zero, ext6Zero_mul]
          | succ j' =>
            rw [ihC (k' + 1) j' (by omega), ext6Mul_scale_left, ext6Pow_succ y j',
              ext6Mul_assoc]
        rw [ext6Binom_succ_succ, hFirst, ihC k' j hkj, ext6Mul_scale_left, hSecond,
          choose204_succ_succ, fq204_ofNat_add, ext6Scale_add_scalar, ext6Add_comm]

private theorem ext6Pow_add_base (x y : Ext6Fq204) (n : Nat) :
    ext6Pow (ext6Add x y) n = ext6BinomSum x y n (n + 1) := by
  induction n with
  | zero =>
    rw [ext6Pow_zero, ext6BinomSum_succ, ext6BinomSum_zero, ext6Binom_zero_zero, ext6Zero_add]
  | succ n ih =>
    have hz : ext6BinomSum x y n (n + 1 + 1) = ext6BinomSum x y n (n + 1) := by
      rw [ext6BinomSum_succ x y n (n + 1), (ext6Binom_closed x y n).1 (n + 1) (by omega),
        ext6Add_zero]
    rw [ext6Pow_succ, ext6BinomSum_succ_row, ih, hz, ext6Mul_add, ext6Add_comm]

private theorem ext6BinomSum_of_middle_zero (x y : Ext6Fq204) (n m : Nat)
    (h : ∀ k, 0 < k → k < m + 1 → ext6Binom x y n k = ext6Zero) :
    ext6BinomSum x y n (m + 1) = ext6Binom x y n 0 := by
  induction m with
  | zero => rw [ext6BinomSum_succ, ext6BinomSum_zero, ext6Zero_add]
  | succ m ih =>
    rw [ext6BinomSum_succ, ih (fun k h0 hk => h k h0 (by omega)),
      h (m + 1) (by omega) (by omega), ext6Add_zero]

/-- The `q`-th power map is additive on the extension. -/
theorem ext6Pow_add_frobenius (x y : Ext6Fq204) :
    ext6Pow (ext6Add x y) mldsaQ = ext6Add (ext6Pow x mldsaQ) (ext6Pow y mldsaQ) := by
  obtain ⟨hZero, hClosed⟩ := ext6Binom_closed x y mldsaQ
  have hMid : ∀ k, 0 < k → k < (mldsaQ - 1) + 1 → ext6Binom x y mldsaQ k = ext6Zero := by
    intro k hk0 hk
    have hkq : k < mldsaQ := by
      have hq : mldsaQ - 1 + 1 = mldsaQ := by decide
      omega
    rw [hClosed k (mldsaQ - k) (by omega),
      fq204_ofNat_eq_zero_of_dvd (mldsaQ_dvd_choose204 hk0 hkq), ext6Scale_zero]
  have hSum := ext6BinomSum_of_middle_zero x y mldsaQ (mldsaQ - 1) hMid
  have hq : mldsaQ - 1 + 1 = mldsaQ := by decide
  rw [hq] at hSum
  rw [ext6Pow_add_base, ext6BinomSum_succ, hSum, hClosed 0 mldsaQ (Nat.zero_add _),
    hClosed mldsaQ 0 (Nat.add_zero _), choose204_zero_right, choose204_self, fq204_ofNat_one,
    ext6Scale_one, ext6Scale_one, ext6Pow_zero, ext6Pow_zero, ext6One_mul, ext6Mul_one,
    ext6Add_comm]

/-- Fermat's little theorem for base-field constants, inside the extension. -/
theorem ext6Pow_embed_frobenius (c : Fq204) :
    ext6Pow (ext6EmbedFq c) mldsaQ = ext6EmbedFq c := by
  have h : ∀ n : Nat,
      ext6Pow (ext6EmbedFq (Fq204.ofNat n)) mldsaQ = ext6EmbedFq (Fq204.ofNat n) := by
    intro n
    induction n with
    | zero =>
      have hz : ext6EmbedFq (Fq204.ofNat 0) = ext6Zero := by decide
      rw [hz]
      exact ext6Pow_zero_base (by decide)
    | succ n ih =>
      rw [fq204_ofNat_add, ext6Embed_add, ext6Pow_add_frobenius, ih, fq204_ofNat_one]
      show ext6Add _ (ext6Pow ext6One mldsaQ) = _
      rw [ext6Pow_one_base]
      rfl
  have hc : Fq204.ofNat c.val = c :=
    Fq204.ext (by rw [Fq204.ofNat_val]; exact Nat.mod_eq_of_lt c.isLt)
  rw [← hc]
  exact h c.val

/-! ### Frobenius in coordinates -/

/-- `ζ = 7^((q-1)/6)`, the scalar with `X^q = ζ X`. It has multiplicative order six. -/
def ext6FrobeniusZeta : Fq204 := Fq204.ofNat 949248

/-- Coordinate action `a_i ↦ c^i a_i`, the substitution `X ↦ c X`. -/
def ext6Twist (c : Fq204) (a : Ext6Fq204) : Ext6Fq204 :=
  let c2 := Fq204.mul c c
  let c3 := Fq204.mul c2 c
  let c4 := Fq204.mul c3 c
  let c5 := Fq204.mul c4 c
  ⟨a.a0, Fq204.mul a.a1 c, Fq204.mul a.a2 c2, Fq204.mul a.a3 c3, Fq204.mul a.a4 c4,
    Fq204.mul a.a5 c5⟩

theorem ext6Twist_twist (c d : Fq204) (a : Ext6Fq204) :
    ext6Twist c (ext6Twist d a) = ext6Twist (Fq204.mul d c) a := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5⟩
  simp only [ext6Twist, Ext6Fq204.mk.injEq]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩ <;> ac_rfl

theorem ext6Twist_one (a : Ext6Fq204) : ext6Twist Fq204.one a = a := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5⟩
  simp only [ext6Twist, Fq204.mul_one]

theorem ext6Pow_X (n : Nat) :
    ext6Pow (ext6Monomial204 1 Fq204.one) n = ext6XPower204 n := by
  induction n with
  | zero => decide
  | succ n ih => rw [ext6Pow_succ, ih, ext6XPower204_succ]

set_option maxRecDepth 8192 in
theorem ext6XPower204_q :
    ext6XPower204 mldsaQ = ext6Scale (ext6Monomial204 1 Fq204.one) ext6FrobeniusZeta := by
  rw [← ext6XPowerFast204_correct 24 mldsaQ (by decide)]
  decide

private def ext6Term (i : Nat) (c : Fq204) : Ext6Fq204 :=
  ext6Mul (ext6EmbedFq c) (ext6Pow (ext6Monomial204 1 Fq204.one) i)

private theorem ext6Term_frobenius (i : Nat) (c : Fq204) :
    ext6Pow (ext6Term i c) mldsaQ =
      ext6Mul (ext6EmbedFq c)
        (ext6Scale (ext6Pow (ext6Monomial204 1 Fq204.one) i) (Fq204.pow ext6FrobeniusZeta i)) := by
  rw [ext6Term, ext6Mul_pow, ext6Pow_embed_frobenius, ← ext6Pow_mul, Nat.mul_comm, ext6Pow_mul,
    ext6Pow_X mldsaQ, ext6XPower204_q, ext6Pow_scale]

private theorem ext6Pow_X_small :
    ext6Pow (ext6Monomial204 1 Fq204.one) 0 = ext6Monomial204 0 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 1 = ext6Monomial204 1 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 2 = ext6Monomial204 2 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 3 = ext6Monomial204 3 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 4 = ext6Monomial204 4 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 5 = ext6Monomial204 5 Fq204.one := by
  decide

/-- **Frobenius in coordinates.** `a^q = (a_0, ζ a_1, ζ^2 a_2, …, ζ^5 a_5)`. -/
theorem ext6Pow_frobenius (a : Ext6Fq204) :
    ext6Pow a mldsaQ = ext6Twist ext6FrobeniusZeta a := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5⟩
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := ext6Pow_X_small
  have hdecomp : (⟨a0, a1, a2, a3, a4, a5⟩ : Ext6Fq204) =
      ext6Add (ext6Term 0 a0) (ext6Add (ext6Term 1 a1) (ext6Add (ext6Term 2 a2)
        (ext6Add (ext6Term 3 a3) (ext6Add (ext6Term 4 a4) (ext6Term 5 a5))))) := by
    simp only [ext6Term, h0, h1, h2, h3, h4, h5]
    simp only [ext6Monomial204, ext6Mul, ext6EmbedFq, ext6Add,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  rw [congrArg (fun t => ext6Pow t mldsaQ) hdecomp]
  simp only [ext6Pow_add_frobenius, ext6Term_frobenius]
  simp only [h0, h1, h2, h3, h4, h5]
  simp only [ext6Monomial204, ext6Mul, ext6EmbedFq, ext6Add, ext6Scale,
    ext6Twist, Fq204.pow,
    Fq204.mul_zero, Fq204.zero_mul, Fq204.mul_one, Fq204.one_mul, Fq204.add_zero,
    Fq204.zero_add]

private theorem ext6Zeta_powers :
    Fq204.mul ext6FrobeniusZeta ext6FrobeniusZeta = Fq204.ofNat 949247 ∧
    Fq204.mul (Fq204.ofNat 949247) ext6FrobeniusZeta = Fq204.ofNat 8380416 ∧
    Fq204.mul (Fq204.ofNat 8380416) ext6FrobeniusZeta = Fq204.ofNat 7431169 ∧
    Fq204.mul (Fq204.ofNat 7431169) ext6FrobeniusZeta = Fq204.ofNat 7431170 ∧
    Fq204.mul (Fq204.ofNat 7431170) ext6FrobeniusZeta = Fq204.one := by
  decide

/-- Frobenius iterates in coordinates. The scalars `949247` and `8380416` of the second
and third iterate are the ones in `ext6RabinUnits204`; the sixth iterate is the identity. -/
theorem ext6Pow_frobenius_iterates (a : Ext6Fq204) :
    ext6Pow a (mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 949247) a ∧
    ext6Pow a (mldsaQ * mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 8380416) a ∧
    ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 7431169) a ∧
    ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ) =
      ext6Twist (Fq204.ofNat 7431170) a ∧
    ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ) = a := by
  obtain ⟨z2, z3, z4, z5, z6⟩ := ext6Zeta_powers
  have e2 : ext6Pow a (mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 949247) a := by
    rw [ext6Pow_mul, ext6Pow_frobenius, ext6Pow_frobenius, ext6Twist_twist, z2]
  have e3 : ext6Pow a (mldsaQ * mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 8380416) a := by
    rw [ext6Pow_mul, e2, ext6Pow_frobenius, ext6Twist_twist, z3]
  have e4 : ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ) =
      ext6Twist (Fq204.ofNat 7431169) a := by
    rw [ext6Pow_mul, e3, ext6Pow_frobenius, ext6Twist_twist, z4]
  have e5 : ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ) =
      ext6Twist (Fq204.ofNat 7431170) a := by
    rw [ext6Pow_mul, e4, ext6Pow_frobenius, ext6Twist_twist, z5]
  refine ⟨e2, e3, e4, e5, ?_⟩
  rw [ext6Pow_mul, e5, ext6Pow_frobenius, ext6Twist_twist, z6, ext6Twist_one]

private theorem fq204_eq_zero_of_mul_fixed {x c : Fq204} (hc : c ≠ Fq204.one)
    (h : Fq204.mul x c = x) : x = Fq204.zero := by
  if hx : x = Fq204.zero then exact hx
  else
    exfalso
    apply hc
    have h1 := congrArg (Fq204.mul (Fq204.inv x)) h
    rwa [← Fq204.mul_assoc, Fq204.inv_mul_cancel hx, Fq204.one_mul] at h1

/-- **Rabin's criterion in coordinates.** An element fixed by the second and the third
Frobenius iterate lies in the base field: the second iterate kills the coordinates of
degree `1, 2, 4, 5` and the third those of degree `1, 3, 5`. -/
theorem ext6_rabin_fixed_is_constant (n : Ext6Fq204)
    (h2 : ext6Pow n (mldsaQ * mldsaQ) = n)
    (h3 : ext6Pow n (mldsaQ * mldsaQ * mldsaQ) = n) :
    n = ext6EmbedFq n.a0 := by
  obtain ⟨e2, e3, _⟩ := ext6Pow_frobenius_iterates n
  rw [e2] at h2
  rw [e3] at h3
  rcases n with ⟨n0, n1, n2, n3, n4, n5⟩
  simp only [ext6Twist, Ext6Fq204.mk.injEq] at h2 h3
  obtain ⟨_, h21, h22, _, h24, h25⟩ := h2
  obtain ⟨_, _, _, h33, _, _⟩ := h3
  have z1 := fq204_eq_zero_of_mul_fixed (by decide) h21
  have z2 := fq204_eq_zero_of_mul_fixed (by decide) h22
  have z3 := fq204_eq_zero_of_mul_fixed (by decide) h33
  have z4 := fq204_eq_zero_of_mul_fixed (by decide) h24
  have z5 := fq204_eq_zero_of_mul_fixed (by decide) h25
  simp only [ext6EmbedFq, z1, z2, z3, z4, z5]

/-! ### Inverse, zero-divisor freedom, irreducibility -/

/-- Product of the five nontrivial Frobenius conjugates of `a`. -/
def ext6ConjProduct (a : Ext6Fq204) : Ext6Fq204 :=
  ext6Mul (ext6Twist ext6FrobeniusZeta a)
    (ext6Mul (ext6Twist (Fq204.ofNat 949247) a)
      (ext6Mul (ext6Twist (Fq204.ofNat 8380416) a)
        (ext6Mul (ext6Twist (Fq204.ofNat 7431169) a) (ext6Twist (Fq204.ofNat 7431170) a))))

/-- Field norm `a · a^q ⋯ a^(q^5)`. -/
def ext6Norm (a : Ext6Fq204) : Ext6Fq204 := ext6Mul a (ext6ConjProduct a)

theorem ext6Norm_def (a : Ext6Fq204) : ext6Mul a (ext6ConjProduct a) = ext6Norm a := by rfl

/-- Executable inverse: conjugate product divided by the base-field norm. -/
def ext6Inv (a : Ext6Fq204) : Ext6Fq204 :=
  ext6Scale (ext6ConjProduct a) (Fq204.inv (ext6Norm a).a0)

private def ext6NormExponent : Nat :=
  1 + (mldsaQ + (mldsaQ * mldsaQ + (mldsaQ * mldsaQ * mldsaQ +
    (mldsaQ * mldsaQ * mldsaQ * mldsaQ + mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ))))

private theorem ext6Norm_eq_pow (a : Ext6Fq204) : ext6Norm a = ext6Pow a ext6NormExponent := by
  obtain ⟨e2, e3, e4, e5, _⟩ := ext6Pow_frobenius_iterates a
  rw [ext6NormExponent, ext6Pow_add, ext6Pow_add, ext6Pow_add, ext6Pow_add, ext6Pow_add,
    ext6Pow_one, ext6Pow_frobenius, e2, e3, e4, e5]
  rfl

theorem ext6Norm_frobenius_fixed (a : Ext6Fq204) :
    ext6Pow (ext6Norm a) mldsaQ = ext6Norm a := by
  obtain ⟨z2, z3, z4, z5, z6⟩ := ext6Zeta_powers
  simp only [ext6Norm, ext6ConjProduct, ext6Mul_pow]
  simp only [ext6Pow_frobenius, ext6Twist_twist, z2, z3, z4, z5, z6, ext6Twist_one]
  ac_rfl

theorem ext6Norm_is_constant (a : Ext6Fq204) :
    ext6Norm a = ext6EmbedFq (ext6Norm a).a0 := by
  have h1 := ext6Norm_frobenius_fixed a
  apply ext6_rabin_fixed_is_constant
  · rw [ext6Pow_mul, h1, h1]
  · rw [ext6Pow_mul, ext6Pow_mul, h1, h1, h1]

theorem ext6Norm_ne_zero {a : Ext6Fq204} (ha : a ≠ ext6Zero) : ext6Norm a ≠ ext6Zero := by
  intro hN
  apply ha
  have h6 := (ext6Pow_frobenius_iterates a).2.2.2.2
  have hE : mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ =
      ext6NormExponent * (mldsaQ - 1) + 1 := by decide
  rw [hE, ext6Pow_succ, ext6Pow_mul, ← ext6Norm_eq_pow, hN,
    ext6Pow_zero_base (by decide), ext6Zero_mul] at h6
  exact h6.symm

/-- **Every nonzero element of the extension is invertible.** -/
theorem ext6Mul_inv_cancel {a : Ext6Fq204} (ha : a ≠ ext6Zero) :
    ext6Mul a (ext6Inv a) = ext6One := by
  have hConst := ext6Norm_is_constant a
  have hN0 : (ext6Norm a).a0 ≠ Fq204.zero := fun h0 =>
    ext6Norm_ne_zero ha (hConst.trans (by rw [h0]; rfl))
  have hKey : ext6Mul a (ext6Inv a) =
      ext6Scale (ext6Norm a) (Fq204.inv (ext6Norm a).a0) := by
    rw [ext6Inv, ext6Mul_scale_right, ext6Norm_def]
  have hS : ext6Scale (ext6Norm a) (Fq204.inv (ext6Norm a).a0) =
      ext6Scale (ext6EmbedFq (ext6Norm a).a0) (Fq204.inv (ext6Norm a).a0) :=
    congrArg (fun t => ext6Scale t (Fq204.inv (ext6Norm a).a0)) hConst
  rw [hKey, hS, ext6Scale_embed, Fq204.mul_inv_cancel hN0]
  rfl

/-- **Zero-divisor freedom of `F_q[X]/(X^6 - 7)`.** -/
theorem ext6Mul_eq_zero {a b : Ext6Fq204} (h : ext6Mul a b = ext6Zero) :
    a = ext6Zero ∨ b = ext6Zero := by
  if ha : a = ext6Zero then exact .inl ha
  else
    right
    have h1 := congrArg (ext6Mul (ext6Inv a)) h
    rwa [← ext6Mul_assoc, ext6Mul_comm (ext6Inv a) a, ext6Mul_inv_cancel ha, ext6One_mul,
      ext6Mul_zero] at h1

/-- The eleven coefficients of the unreduced product of two polynomials of degree at most
five; `ext6Mul` is this product with `X^(6+k)` replaced by `7 X^k`. -/
def ext6ProductCoeffs (x y : Ext6Fq204) : List Fq204 :=
  let m (a b : Fq204) := Fq204.mul a b
  let ad (a b : Fq204) := Fq204.add a b
  [m x.a0 y.a0,
   ad (m x.a0 y.a1) (m x.a1 y.a0),
   ad (m x.a0 y.a2) (ad (m x.a1 y.a1) (m x.a2 y.a0)),
   ad (m x.a0 y.a3) (ad (m x.a1 y.a2) (ad (m x.a2 y.a1) (m x.a3 y.a0))),
   ad (m x.a0 y.a4) (ad (m x.a1 y.a3) (ad (m x.a2 y.a2) (ad (m x.a3 y.a1) (m x.a4 y.a0)))),
   ad (m x.a0 y.a5) (ad (m x.a1 y.a4) (ad (m x.a2 y.a3) (ad (m x.a3 y.a2)
     (ad (m x.a4 y.a1) (m x.a5 y.a0))))),
   ad (m x.a1 y.a5) (ad (m x.a2 y.a4) (ad (m x.a3 y.a3) (ad (m x.a4 y.a2) (m x.a5 y.a1)))),
   ad (m x.a2 y.a5) (ad (m x.a3 y.a4) (ad (m x.a4 y.a3) (m x.a5 y.a2))),
   ad (m x.a3 y.a5) (ad (m x.a4 y.a4) (m x.a5 y.a3)),
   ad (m x.a4 y.a5) (m x.a5 y.a4),
   m x.a5 y.a5]

/-- **Irreducibility of `X^6 - 7` over `F_q`.** No two polynomials of degree at most five
multiply to `X^6 - 7`; a proper factorization of a degree-six polynomial has both factors
of degree at most five. -/
theorem ext6Modulus_irreducible (g h : Ext6Fq204) :
    ext6ProductCoeffs g h ≠
      [Fq204.neg ext6Nonresidue, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero,
       Fq204.one, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero] := by
  intro hEq
  have hMul : ext6Mul g h = ext6Zero := by
    rcases g with ⟨g0, g1, g2, g3, g4, g5⟩
    rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
    simp only [ext6ProductCoeffs, List.cons.injEq, and_true] at hEq
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hEq
    simp only [ext6Mul, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]
    decide
  have hOne : (ext6ProductCoeffs g h).getD 6 Fq204.zero = Fq204.one := by rw [hEq]; rfl
  rcases ext6Mul_eq_zero hMul with hz | hz
  · subst hz
    simp only [ext6ProductCoeffs, ext6Zero, Fq204.zero_mul, Fq204.add_zero] at hOne
    exact absurd hOne (by decide)
  · subst hz
    simp only [ext6ProductCoeffs, ext6Zero, Fq204.mul_zero, Fq204.add_zero] at hOne
    exact absurd hOne (by decide)

def ext6Neg (x : Ext6Fq204) : Ext6Fq204 :=
  ⟨Fq204.neg x.a0, Fq204.neg x.a1, Fq204.neg x.a2, Fq204.neg x.a3, Fq204.neg x.a4,
    Fq204.neg x.a5⟩

instance : CommRingOps Ext6Fq204 where
  zero := ext6Zero
  one := ext6One
  add := ext6Add
  mul := ext6Mul
  neg := ext6Neg
  sub := ext6Sub

instance : LawfulCommRing Ext6Fq204 where
  add_assoc := ext6Add_assoc
  add_comm := ext6Add_comm
  zero_add := ext6Zero_add
  add_zero := ext6Add_zero
  add_left_neg := fun x => by
    rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
    show ext6Add (ext6Neg _) _ = ext6Zero
    simp only [ext6Add, ext6Neg, ext6Zero, Fq204.add_left_neg]
  sub_eq_add_neg := fun x y => by
    rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
    rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
    show ext6Sub _ _ = ext6Add _ (ext6Neg _)
    simp only [ext6Add, ext6Neg, ext6Sub, Fq204.sub_eq_add_neg]
  mul_assoc := ext6Mul_assoc
  mul_comm := ext6Mul_comm
  one_mul := ext6One_mul
  mul_one := ext6Mul_one
  left_distrib := ext6Mul_add
  right_distrib := ext6Add_mul

instance : NoZeroDivisors Ext6Fq204 where
  eq_zero_or_eq_zero_of_mul_eq_zero := ext6Mul_eq_zero

theorem ext6Inv_zero : ext6Inv ext6Zero = ext6Zero := by
  have hTwist : ∀ c : Fq204, ext6Twist c ext6Zero = ext6Zero := fun c => by
    unfold ext6Twist ext6Zero
    dsimp only
    simp only [Fq204.zero_mul]
  have hConj : ext6ConjProduct ext6Zero = ext6Zero := by
    unfold ext6ConjProduct
    rw [hTwist, ext6Zero_mul]
  unfold ext6Inv
  rw [hConj]
  unfold ext6Scale ext6Zero
  dsimp only
  simp only [Fq204.zero_mul]

/-- The verification extension as a field, with the executable inverse `ext6Inv`. -/
instance : LawfulField Ext6Fq204 where
  inv := ext6Inv
  zero_ne_one := by decide
  inv_zero := ext6Inv_zero
  mul_inv_cancel := ext6Mul_inv_cancel

end Ext6Field

/-! ### Root counting over the extension challenge space

`rss_mpc.rs` draws the batching coin `lambda` and every folding coin `xi` from the
extension. With the field structure above, a discrepancy polynomial with extension
coefficients has no more roots than its degree, so a wrong multiplication triple
survives batching with at most `gates` values of `lambda` and a wrong folding round with
at most `2 (FOLD - 1) = 14` values of `xi`.
-/

private theorem exists_eval_nonzero_ext6 :
    ∀ (cs : List Ext6Fq204), cs.length < mldsaQ →
      (∃ c ∈ cs, c ≠ ext6Zero) →
      ∃ x : Ext6Fq204, RoundPoly.evalCoeffs cs x ≠ ext6Zero
  | [], _, ⟨_, hMem, _⟩ => by cases hMem
  | c₀ :: tail, hLen, ⟨c, hMem, hcNe⟩ => by
    if hc0Ne : c₀ ≠ ext6Zero then
      refine ⟨ext6Zero, ?_⟩
      change ext6Add c₀ (ext6Mul ext6Zero (RoundPoly.evalCoeffs tail ext6Zero)) ≠ ext6Zero
      rw [ext6Zero_mul, ext6Add_zero]
      exact hc0Ne
    else
      have hc0Eq : c₀ = ext6Zero := by
        cases decEq c₀ ext6Zero with
        | isTrue h => exact h
        | isFalse h => exact False.elim (hc0Ne h)
      subst hc0Eq
      have hTailEx : ∃ c' ∈ tail, c' ≠ ext6Zero := by
        rcases List.mem_cons.mp hMem with rfl | hInTail
        · exact False.elim (hcNe rfl)
        · exact ⟨c, hInTail, hcNe⟩
      have hTailPos : 1 ≤ tail.length := by
        rcases hTailEx with ⟨_, hm, _⟩
        cases tail with
        | nil => cases hm
        | cons _ _ => simp only [List.length_cons]; omega
      simp only [List.length_cons] at hLen
      obtain ⟨x₁, hx₁⟩ := exists_eval_nonzero_ext6 tail (by omega) hTailEx
      let d := tail.length - 1
      let grid : List Ext6Fq204 :=
        (List.range (d + 1)).map (fun i => ext6EmbedFq (Fq204.ofNat (i + 1)))
      have hGridLen : grid.length = d + 1 := by simp [grid]
      have hGridNodup : grid.Nodup := by
        apply nodup_map_on_list_fq _ (Qsag.Constructive.nodup_range (d + 1))
        intro a ha b hb hEq
        have haLt : a + 1 < mldsaQ := by have := List.mem_range.mp ha; omega
        have hbLt : b + 1 < mldsaQ := by have := List.mem_range.mp hb; omega
        have hVal := congrArg (fun e : Ext6Fq204 => e.a0.val) hEq
        simp only [ext6EmbedFq, Fq204.ofNat_val, Nat.mod_eq_of_lt haLt,
          Nat.mod_eq_of_lt hbLt] at hVal
        omega
      have hRootsLe :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = ext6Zero))).length ≤ d :=
        RoundPoly.roots_nodup_length_le d tail grid hGridNodup (by omega) ⟨x₁, hx₁⟩
      have hFiltLt :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = ext6Zero))).length <
            grid.length := by
        rw [hGridLen]; omega
      obtain ⟨x₀, hx₀Mem, hx₀False⟩ := exists_mem_of_filter_length_lt_fq
        (fun r => decide (RoundPoly.evalCoeffs tail r = ext6Zero)) grid hFiltLt
      have hx₀NeZero : x₀ ≠ ext6Zero := by
        rcases List.mem_map.mp hx₀Mem with ⟨idx, hIdxRange, rfl⟩
        have hIdxLt : idx + 1 < mldsaQ := by have := List.mem_range.mp hIdxRange; omega
        intro hZero
        have hv := congrArg (fun e : Ext6Fq204 => e.a0.val) hZero
        simp only [ext6EmbedFq, ext6Zero, Fq204.ofNat_val, Nat.mod_eq_of_lt hIdxLt,
          Fq204.zero_val] at hv
        omega
      have hEvalTailNe : RoundPoly.evalCoeffs tail x₀ ≠ ext6Zero := by
        intro hZero
        rw [decide_eq_true hZero] at hx₀False
        cases hx₀False
      refine ⟨x₀, ?_⟩
      change ext6Add ext6Zero (ext6Mul x₀ (RoundPoly.evalCoeffs tail x₀)) ≠ ext6Zero
      rw [ext6Zero_add]
      intro hProdZero
      rcases ext6Mul_eq_zero hProdZero with h1 | h2
      · exact hx₀NeZero h1
      · exact hEvalTailNe h2

/-- **Batching and folding coins are drawn from a field.** A polynomial over the
extension of formal degree at most `D` with a nonzero coefficient vanishes on at most `D`
points of any duplicate-free list of extension challenges. -/
theorem rss_ext6_discrepancy_roots_le (D : Nat) (cs S : List Ext6Fq204)
    (hD : D + 1 < mldsaQ) (hLen : cs.length ≤ D + 1) (hNodup : S.Nodup)
    (hNz : ∃ c ∈ cs, c ≠ ext6Zero) :
    (S.filter (fun xi => decide (RoundPoly.evalCoeffs cs xi = ext6Zero))).length ≤ D := by
  obtain ⟨x₀, hx₀⟩ := exists_eval_nonzero_ext6 cs (by omega) hNz
  exact RoundPoly.roots_nodup_length_le D cs S hNodup hLen ⟨x₀, hx₀⟩

/-- One folding round of `Engine::verify` (`FOLD = 8`): the round polynomial has degree
at most fourteen, so at most fourteen folding coins hide a wrong round. -/
theorem rss_ext6_fold_round_roots_le (cs S : List Ext6Fq204)
    (hLen : cs.length ≤ 15) (hNodup : S.Nodup) (hNz : ∃ c ∈ cs, c ≠ ext6Zero) :
    (S.filter (fun xi => decide (RoundPoly.evalCoeffs cs xi = ext6Zero))).length ≤ 14 :=
  rss_ext6_discrepancy_roots_le 14 cs S (by decide) hLen hNodup hNz

/-- The nonzero-coefficient premise is needed: the zero polynomial vanishes everywhere. -/
theorem tooth_rss_ext6_zero_discrepancy_all_roots :
    ∃ S : List Ext6Fq204, S.Nodup ∧
      (S.filter (fun xi => decide (RoundPoly.evalCoeffs [ext6Zero] xi = ext6Zero))).length = 2 :=
  ⟨[ext6Zero, ext6One], by decide, by decide⟩

/-- The inverse is specific to nonzero elements. -/
theorem tooth_ext6Inv_zero_not_inverse :
    ext6Mul ext6Zero (ext6Inv ext6Zero) ≠ ext6One := by
  rw [ext6Zero_mul]
  decide

/-- The third Frobenius iterate alone does not cut out the base field: `X^2` is fixed by
it and is not a constant, so the second-iterate condition of the criterion is needed. -/
theorem tooth_ext6_third_iterate_fixes_nonconstant :
    ∃ n : Ext6Fq204, ext6Pow n (mldsaQ * mldsaQ * mldsaQ) = n ∧ n ≠ ext6EmbedFq n.a0 := by
  refine ⟨ext6Monomial204 2 Fq204.one, ?_, by decide⟩
  rw [(ext6Pow_frobenius_iterates _).2.1]
  decide

/-- A reducible modulus is rejected by the same coefficient test: `X^6 - 1` factors. -/
theorem tooth_ext6_unit_modulus_factors :
    ∃ g h : Ext6Fq204, ext6ProductCoeffs g h =
      [Fq204.neg Fq204.one, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero,
       Fq204.one, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero] :=
  ⟨⟨Fq204.neg Fq204.one, Fq204.zero, Fq204.zero, Fq204.one, Fq204.zero, Fq204.zero⟩,
   ⟨Fq204.one, Fq204.zero, Fq204.zero, Fq204.one, Fq204.zero, Fq204.zero⟩, by decide⟩

theorem ext6Inv_inhabited :
    ∃ a : Ext6Fq204, a ≠ ext6Zero ∧ ext6Mul a (ext6Inv a) = ext6One :=
  ⟨ext6Monomial204 1 Fq204.one, by decide, ext6Mul_inv_cancel (by decide)⟩

/-! ## Seed expansion: the multi-key hybrid

In `rss_mpc.rs` every replicated component draws its masks from a tape expanded from
that component's own subset key (`Prss::elements`). The theorems above are stated for
independent uniform tapes. This section is the reduction between the two experiments.

Both tape samplers read one coin from a common space `Fin N`: `real r` is the tape
expanded from the key encoded by `r`, `ideal r` an independently sampled tape. A
distinguisher sees the list of all `m` tapes. Hybrid `j` replaces the first `j` tapes.
Neighbouring hybrids differ in one tape, and for every fixing of the other tapes the
distinguisher restricted to that position is a single-key adversary; `hPRF` bounds
exactly these adversaries. All hit counts share the denominator `N^m`, so dividing the
conclusion by `N^m` gives `m` times the single-key advantage `ε / N`.
-/

def prssGap (a b : Nat) : Nat := (a - b) + (b - a)

theorem prssGap_triangle (a b c : Nat) : prssGap a c ≤ prssGap a b + prssGap b c := by
  unfold prssGap
  omega

private theorem prssGap_self (a : Nat) : prssGap a a = 0 := by
  unfold prssGap
  omega

private theorem prssGap_add_le (a b c d : Nat) :
    prssGap (a + c) (b + d) ≤ prssGap a b + prssGap c d := by
  unfold prssGap
  omega

private theorem prssGap_qsum_le {n : Nat} (f g : Fin n → Nat) :
    prssGap (qsum n f) (qsum n g) ≤ qsum n (fun i => prssGap (f i) (g i)) := by
  have h1 : qsum n f ≤ qsum n g + qsum n (fun i => prssGap (f i) (g i)) := by
    rw [← qsum_add]
    exact qsum_le_qsum (fun i => by unfold prssGap; omega)
  have h2 : qsum n g ≤ qsum n f + qsum n (fun i => prssGap (f i) (g i)) := by
    rw [← qsum_add]
    exact qsum_le_qsum (fun i => by unfold prssGap; omega)
  unfold prssGap at *
  omega

/-- Sum over all coin vectors for `m` keys. -/
def prssCoinSum (N : Nat) : (m : Nat) → (List (Fin N) → Nat) → Nat
  | 0, f => f []
  | m + 1, f => qsum N (fun r => prssCoinSum N m (fun rs => f (r :: rs)))

private theorem prssCoinSum_succ (N m : Nat) (f : List (Fin N) → Nat) :
    prssCoinSum N (m + 1) f = qsum N (fun r => prssCoinSum N m (fun rs => f (r :: rs))) := by
  rfl

private theorem prssCoinSum_const (N : Nat) (c : Nat) :
    ∀ m : Nat, prssCoinSum N m (fun _ => c) = N ^ m * c := by
  intro m
  induction m with
  | zero => simp only [prssCoinSum, Nat.pow_zero, Nat.one_mul]
  | succ m ih =>
    rw [prssCoinSum_succ, qsum_congr (fun _ => ih), qsum_const, Nat.pow_succ,
      Nat.mul_comm (N ^ m) N, Nat.mul_assoc]

private theorem prssCoinSum_le (N : Nat) (m : Nat) :
    ∀ (f g : List (Fin N) → Nat), (∀ rs, f rs ≤ g rs) →
      prssCoinSum N m f ≤ prssCoinSum N m g := by
  induction m with
  | zero => intro f g h; exact h []
  | succ m ih =>
    intro f g h
    rw [prssCoinSum_succ, prssCoinSum_succ]
    exact qsum_le_qsum (fun r => ih _ _ (fun rs => h (r :: rs)))

private theorem prssGap_coinSum_le (N : Nat) (m : Nat) :
    ∀ (f g : List (Fin N) → Nat),
      prssGap (prssCoinSum N m f) (prssCoinSum N m g) ≤
        prssCoinSum N m (fun rs => prssGap (f rs) (g rs)) := by
  induction m with
  | zero => intro f g; exact Nat.le_refl _
  | succ m ih =>
    intro f g
    rw [prssCoinSum_succ, prssCoinSum_succ, prssCoinSum_succ]
    exact Nat.le_trans (prssGap_qsum_le _ _) (qsum_le_qsum (fun r => ih _ _))

private theorem prssCoinSum_qsum_comm (N : Nat) (m : Nat) :
    ∀ (F : Fin N → List (Fin N) → Nat),
      qsum N (fun r => prssCoinSum N m (fun rs => F r rs)) =
        prssCoinSum N m (fun rs => qsum N (fun r => F r rs)) := by
  induction m with
  | zero => intro F; rfl
  | succ m ih =>
    intro F
    rw [prssCoinSum_succ]
    have h1 : qsum N (fun r => prssCoinSum N (m + 1) (fun rs => F r rs)) =
        qsum N (fun r => qsum N (fun r' =>
          prssCoinSum N m (fun rs => F r (r' :: rs)))) :=
      qsum_congr (fun r => prssCoinSum_succ N m _)
    rw [h1, qsum_comm]
    exact qsum_congr (fun r' => ih (fun r rs => F r (r' :: rs)))

/-- Hybrid `j`: the first `j` tapes are ideal, the remaining ones are expanded from keys. -/
def prssHybridTapes {O : Type} {N : Nat} (real ideal : Fin N → O) :
    Nat → List (Fin N) → List O
  | _, [] => []
  | 0, r :: rs => real r :: prssHybridTapes real ideal 0 rs
  | j + 1, r :: rs => ideal r :: prssHybridTapes real ideal j rs

def prssHybridHits {O : Type} {N : Nat} (real ideal : Fin N → O) (m j : Nat)
    (D : List O → Bool) : Nat :=
  prssCoinSum N m (fun rs => (D (prssHybridTapes real ideal j rs)).toNat)

/-- Every tape expanded from its own key. -/
def prssRealHits {O : Type} {N : Nat} (real : Fin N → O) (m : Nat) (D : List O → Bool) : Nat :=
  prssCoinSum N m (fun rs => (D (rs.map real)).toNat)

/-- Every tape sampled independently. -/
def prssIdealHits {O : Type} {N : Nat} (ideal : Fin N → O) (m : Nat) (D : List O → Bool) :
    Nat :=
  prssCoinSum N m (fun rs => (D (rs.map ideal)).toNat)

private theorem prssHybridHits_zero_succ {O : Type} {N : Nat} (real ideal : Fin N → O)
    (m : Nat) (D : List O → Bool) :
    prssHybridHits real ideal (m + 1) 0 D =
      qsum N (fun r => prssHybridHits real ideal m 0 (fun t => D (real r :: t))) := by
  rfl

private theorem prssHybridHits_succ_succ {O : Type} {N : Nat} (real ideal : Fin N → O)
    (m j : Nat) (D : List O → Bool) :
    prssHybridHits real ideal (m + 1) (j + 1) D =
      qsum N (fun r => prssHybridHits real ideal m j (fun t => D (ideal r :: t))) := by
  rfl

theorem prssHybridHits_zero {O : Type} {N : Nat} (real ideal : Fin N → O) (m : Nat) :
    ∀ D : List O → Bool, prssHybridHits real ideal m 0 D = prssRealHits real m D := by
  induction m with
  | zero => intro D; rfl
  | succ m ih =>
    intro D
    rw [prssHybridHits_zero_succ, qsum_congr (fun r => ih _)]
    rfl

theorem prssHybridHits_all {O : Type} {N : Nat} (real ideal : Fin N → O) (m : Nat) :
    ∀ D : List O → Bool, prssHybridHits real ideal m m D = prssIdealHits ideal m D := by
  induction m with
  | zero => intro D; rfl
  | succ m ih =>
    intro D
    rw [prssHybridHits_succ_succ, qsum_congr (fun r => ih _)]
    rfl

/-- The single-key assumption, for the adversaries the hybrid produces: the
distinguisher with every other tape fixed. -/
def PrssSingleKeyBound {O : Type} {N : Nat} (real ideal : Fin N → O) (D : List O → Bool)
    (ε : Nat) : Prop :=
  ∀ pre post : List O,
    prssGap (qsum N (fun r => (D (pre ++ real r :: post)).toNat))
      (qsum N (fun r => (D (pre ++ ideal r :: post)).toNat)) ≤ ε

private theorem prssSingleKeyBound_cons {O : Type} {N : Nat} {real ideal : Fin N → O}
    {D : List O → Bool} {ε : Nat} (h : PrssSingleKeyBound real ideal D ε) (o : O) :
    PrssSingleKeyBound real ideal (fun t => D (o :: t)) ε :=
  fun pre post => h (o :: pre) post

/-- Neighbouring hybrids differ by the single-key bound, summed over the other coins. -/
theorem prssHybrid_step {O : Type} {N : Nat} (real ideal : Fin N → O) (ε : Nat) :
    ∀ (j m : Nat) (D : List O → Bool), j < m → PrssSingleKeyBound real ideal D ε →
      prssGap (prssHybridHits real ideal m j D) (prssHybridHits real ideal m (j + 1) D) ≤
        N ^ (m - 1) * ε := by
  intro j
  induction j with
  | zero =>
    intro m D hm hPRF
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hL : prssHybridHits real ideal (m' + 1) 0 D =
        prssCoinSum N m' (fun rs => qsum N (fun r =>
          (D (real r :: prssHybridTapes real ideal 0 rs)).toNat)) :=
      prssCoinSum_qsum_comm N m' _
    have hR : prssHybridHits real ideal (m' + 1) 1 D =
        prssCoinSum N m' (fun rs => qsum N (fun r =>
          (D (ideal r :: prssHybridTapes real ideal 0 rs)).toNat)) :=
      prssCoinSum_qsum_comm N m' _
    rw [hL, hR, Nat.add_sub_cancel, ← prssCoinSum_const N ε m']
    exact Nat.le_trans (prssGap_coinSum_le N m' _ _)
      (prssCoinSum_le N m' _ _ (fun rs => hPRF [] _))
  | succ j ih =>
    intro m D hm hPRF
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, m' = k + 1 := ⟨m' - 1, by omega⟩
    rw [prssHybridHits_succ_succ, prssHybridHits_succ_succ]
    refine Nat.le_trans (prssGap_qsum_le _ _) ?_
    have hEach : ∀ r : Fin N,
        prssGap (prssHybridHits real ideal (k + 1) j (fun t => D (ideal r :: t)))
          (prssHybridHits real ideal (k + 1) (j + 1) (fun t => D (ideal r :: t))) ≤
          N ^ k * ε := fun r =>
      ih (k + 1) _ (by omega) (prssSingleKeyBound_cons hPRF (ideal r))
    refine Nat.le_trans (qsum_le_qsum hEach) ?_
    rw [qsum_const, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm (N ^ k) N, Nat.mul_assoc]
    exact Nat.le_refl _

/-- **Multi-key seed-expansion hybrid.** Replacing all `m` key-expanded tapes by
independent tapes changes any distinguisher's hit count by at most `m N^(m-1) ε`, that
is, its acceptance probability by at most `m (ε / N)`. -/
theorem prss_multi_key_hybrid {O : Type} {N : Nat} (real ideal : Fin N → O) (m : Nat)
    (D : List O → Bool) (ε : Nat) (hPRF : PrssSingleKeyBound real ideal D ε) :
    prssGap (prssRealHits real m D) (prssIdealHits ideal m D) ≤ m * (N ^ (m - 1) * ε) := by
  have hAll : ∀ k : Nat, k ≤ m →
      prssGap (prssHybridHits real ideal m 0 D) (prssHybridHits real ideal m k D) ≤
        k * (N ^ (m - 1) * ε) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [prssGap_self]
      exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := prssHybrid_step real ideal ε k m D (by omega) hPRF
      have h3 := prssGap_triangle (prssHybridHits real ideal m 0 D)
        (prssHybridHits real ideal m k D) (prssHybridHits real ideal m (k + 1) D)
      rw [Nat.succ_mul]
      omega
  have h := hAll m (Nat.le_refl m)
  rwa [prssHybridHits_zero, prssHybridHits_all] at h

/-- The three subset keys of the two-of-three replicated sharing. -/
theorem prss_three_key_hybrid {O : Type} {N : Nat} (real ideal : Fin N → O)
    (D : List O → Bool) (ε : Nat) (hPRF : PrssSingleKeyBound real ideal D ε) :
    prssGap (prssRealHits real 3 D) (prssIdealHits ideal 3 D) ≤ 3 * (N ^ 2 * ε) :=
  prss_multi_key_hybrid real ideal 3 D ε hPRF

/-- The single-key bound is needed: an expansion whose tape differs from every ideal
tape is told apart by reading one entry. -/
theorem tooth_prss_constant_expansion_distinguished :
    ∃ D : List Bool → Bool,
      prssGap (prssRealHits (N := 1) (fun _ => false) 1 D)
        (prssIdealHits (N := 1) (fun _ => true) 1 D) ≠ 0 := by
  refine ⟨fun t => t.headD false, ?_⟩
  show prssGap (qsum 1 (fun _ => 0)) (qsum 1 (fun _ => 1)) ≠ 0
  rw [qsum_const, qsum_const]
  decide

private def prssSwap2 (r : Fin 2) : Fin 2 := ⟨1 - r.val, by omega⟩

/-- A two-coin instance in which the two samplers are different functions with the same
distribution; the bound holds with `ε = 0` for a distinguisher that reads a tape. -/
theorem prss_multi_key_hybrid_inhabited :
    ∃ (D : List Bool → Bool) (ε : Nat),
      PrssSingleKeyBound (N := 2) (fun r => decide (r.val = 1)) (fun r => decide (r.val = 0)) D ε ∧
      prssGap (prssRealHits (N := 2) (fun r => decide (r.val = 1)) 3 D)
        (prssIdealHits (N := 2) (fun r => decide (r.val = 0)) 3 D) ≤ 3 * (2 ^ 2 * ε) := by
  have hBound : PrssSingleKeyBound (N := 2) (fun r => decide (r.val = 1))
      (fun r => decide (r.val = 0)) (fun t => t.headD false) 0 := by
    intro pre post
    have hSwap : ∀ r : Fin 2, prssSwap2 (prssSwap2 r) = r := by decide
    have hId : ∀ r : Fin 2, decide (r.val = 0) = decide ((prssSwap2 r).val = 1) := by decide
    have hEq : qsum 2 (fun r => ((pre ++ decide (r.val = 0) :: post).headD false).toNat) =
        qsum 2 (fun r => ((pre ++ decide (r.val = 1) :: post).headD false).toNat) := by
      rw [qsum_congr (fun r => by rw [hId r])]
      exact qsum_perm_invariant prssSwap2 prssSwap2 hSwap hSwap
        (fun r => ((pre ++ decide (r.val = 1) :: post).headD false).toNat)
    show prssGap (qsum 2 (fun r => ((pre ++ decide (r.val = 1) :: post).headD false).toNat))
      (qsum 2 (fun r => ((pre ++ decide (r.val = 0) :: post).headD false).toNat)) ≤ 0
    rw [hEq, prssGap_self]
    exact Nat.le_refl 0
  exact ⟨fun t => t.headD false, 0, hBound, prss_multi_key_hybrid _ _ 3 _ 0 hBound⟩

/-- Actual permutation inputs on the three-chunk, zero-capacity sponge path. -/
def spongeTrace204 (chunks : Lane6 × Lane6 × Lane6) (r : Fin 3) : Poseidon2State12 :=
  let s1 := mkState12Of6 chunks.1 lane6Zero
  let p1 := poseidon2Perm12 s1
  let s2 := mkState12Of6 (lane6Add (state12Rate6 p1) chunks.2.1) (state12Cap6 p1)
  let p2 := poseidon2Perm12 s2
  let s3 := mkState12Of6 (lane6Add (state12Rate6 p2) chunks.2.2) (state12Cap6 p2)
  match r.val with | 0 => s1 | 1 => s2 | _ => s3

/-- Collision extraction retaining reachability from the supplied sponge
messages. Unrestricted rate/capacity collisions are not assumed hard. -/
def absorbRate6Sponge3_reachable_collision204
    {c0₁ c1₁ c2₁ c0₂ c1₂ c2₂ : Lane6}
    (hNe : (c0₁, c1₁, c2₁) ≠ (c0₂, c1₂, c2₂))
    (hDig : state12Rate6 (absorbRate6Sponge3 c0₁ c1₁ c2₁) =
            state12Rate6 (absorbRate6Sponge3 c0₂ c1₂ c2₂)) :
    { r : Fin 3 // Poseidon2Perm12Sponge6Collision
      (spongeTrace204 (c0₁, c1₁, c2₁) r) (spongeTrace204 (c0₂, c1₂, c2₂) r) } := by
  let s1₁ := mkState12Of6 c0₁ lane6Zero
  let s1₂ := mkState12Of6 c0₂ lane6Zero
  let p1₁ := poseidon2Perm12 s1₁
  let p1₂ := poseidon2Perm12 s1₂
  let s2₁ := mkState12Of6 (lane6Add (state12Rate6 p1₁) c1₁) (state12Cap6 p1₁)
  let s2₂ := mkState12Of6 (lane6Add (state12Rate6 p1₂) c1₂) (state12Cap6 p1₂)
  let p2₁ := poseidon2Perm12 s2₁
  let p2₂ := poseidon2Perm12 s2₂
  let s3₁ := mkState12Of6 (lane6Add (state12Rate6 p2₁) c2₁) (state12Cap6 p2₁)
  let s3₂ := mkState12Of6 (lane6Add (state12Rate6 p2₂) c2₂) (state12Cap6 p2₂)
  if h3 : s3₁ = s3₂ then
    if h2 : s2₁ = s2₂ then
      have hp2 : p2₁ = p2₂ := congrArg poseidon2Perm12 h2
      have hRate3 : lane6Add (state12Rate6 p2₁) c2₁ = lane6Add (state12Rate6 p2₂) c2₂ := by
        have hr := congrArg state12Rate6 h3
        rwa [state12Rate6_mk, state12Rate6_mk] at hr
      rw [hp2] at hRate3
      have hc2 : c2₁ = c2₂ := lane6Add_left_cancel hRate3
      if h1 : s1₁ = s1₂ then
        have hp1 : p1₁ = p1₂ := congrArg poseidon2Perm12 h1
        have hRate2 : lane6Add (state12Rate6 p1₁) c1₁ = lane6Add (state12Rate6 p1₂) c1₂ := by
          have hr := congrArg state12Rate6 h2
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        rw [hp1] at hRate2
        have hc1 : c1₁ = c1₂ := lane6Add_left_cancel hRate2
        have hc0 : c0₁ = c0₂ := by
          have hr := congrArg state12Rate6 h1
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        exact False.elim (hNe (by rw [hc0, hc1, hc2]))
      else
        have hCap1 : state12Cap6 p1₁ = state12Cap6 p1₂ := by
          have hc := congrArg state12Cap6 h2
          rwa [state12Cap6_mk, state12Cap6_mk] at hc
        refine ⟨⟨0, by decide⟩, ?_⟩
        simpa only [spongeTrace204] using
          (show Poseidon2Perm12Sponge6Collision s1₁ s1₂ from ⟨h1, Or.inr hCap1⟩)
    else
      have hCap2 : state12Cap6 p2₁ = state12Cap6 p2₂ := by
        have hc := congrArg state12Cap6 h3
        rwa [state12Cap6_mk, state12Cap6_mk] at hc
      refine ⟨⟨1, by decide⟩, ?_⟩
      simpa only [spongeTrace204] using
        (show Poseidon2Perm12Sponge6Collision s2₁ s2₂ from ⟨h2, Or.inr hCap2⟩)
  else
    refine ⟨⟨2, by decide⟩, ?_⟩
    simpa only [spongeTrace204] using
      (show Poseidon2Perm12Sponge6Collision s3₁ s3₂ from ⟨h3, Or.inl hDig⟩)


/-- Binding failure reduces to two reachable states on the paths of the actual
well-formed credential openings. This is a reduction, not an assertion of
collision resistance for arbitrary halves of a public permutation. -/
def blindVcReachableBinding204
    (schema₁ schema₂ : VcSchema) (attrs₁ attrs₂ : List Goldilocks)
    (blind₁ blind₂ : Lane4) (tag : UInt64) (c : Lane6)
    (h1 : computeVcPoseidon2Commit schema₁ attrs₁ blind₁ tag = some c)
    (h2 : computeVcPoseidon2Commit schema₂ attrs₂ blind₂ tag = some c)
    (hne : (schema₁, attrs₁, blind₁) ≠ (schema₂, attrs₂, blind₂)) :
    { r : Fin 3 // Poseidon2Perm12Sponge6Collision
      (spongeTrace204 (vcCommitChunks schema₁ attrs₁ blind₁ tag) r)
      (spongeTrace204 (vcCommitChunks schema₂ attrs₂ blind₂ tag) r) } := by
  have hl1 := (blind_vc_commit_binding_reduces_to_sponge12_collision.1
    schema₁ attrs₁ blind₁ tag c h1).2.1
  have hl2 := (blind_vc_commit_binding_reduces_to_sponge12_collision.1
    schema₂ attrs₂ blind₂ tag c h2).2.1
  apply absorbRate6Sponge3_reachable_collision204
  · intro he
    obtain ⟨hs, ha, hb⟩ := vcCommitChunks_injective hl1 hl2 he
    exact hne (by rw [hs, ha, hb])
  · unfold computeVcPoseidon2Commit at h1 h2
    rw [ite_true_of hl1] at h1
    rw [ite_true_of hl2] at h2
    exact (Option.some.inj h1).trans (Option.some.inj h2).symm

-- Structural registrations. These are not claims that source mutants have been executed.
#tooth_pair mldsaVerifyBytes204_bounds vs tooth_mldsaVerifyBytes204_bad_key_length
#tooth_pair cosetLde204_size vs tooth_cosetLde204_zero_shift
#tooth_pair canonicalNorm204_sound vs tooth_canonicalNorm204_noncanonical
#tooth_pair merkleNodePreimage204_injective vs tooth_merkle204_leaf_node_disjoint
#tooth_pair rssProductsValid_eq_true_iff vs tooth_rssProductsValid_corrupted_output
#tooth_pair rssDurableReserve204_burns vs tooth_rssDurableReserve204_nonce_replay
#tooth_pair rssDurableSign204_release_burned vs tooth_rssDurableSign204_failed_write
#tooth_pair dkgReveal204_valid_share vs tooth_dkgReveal204_before_freeze
#tooth_pair toprfActiveCross204_correct vs tooth_toprfActiveCross204_forgery
#tooth_pair contextIndex204_injective vs tooth_contextIndex204_no_u64_wrap
#tooth_pair rssDurableTrace204_monotone vs tooth_rssDurableTrace204_replay
#verify_inhabited rssProductsChecked204_sound rssProductsChecked204_inhabited
#tooth_pair sacAccept204_sound vs tooth_sacAccept204_rejects_corrupt
#tooth_pair rssSacrificedProductsValid_sound vs tooth_rssSacrificedProductsValid_corrupt
#tooth_pair rssDurable204_released_nonces_distinct vs tooth_rssDurable204_reuse_after_release
#tooth_pair dkgReveal204_binding vs tooth_dkgCommit204_after_freeze
#tooth_pair toprfDigestCross204_correct_or_collision vs tooth_toprf_unchecked_cross_message
#tooth_pair toprf_joint_view_simulation vs tooth_toprf_joint_view_depends_on_secret
#verify_inhabited rssDurableSign204_release_verifies rssDurableSign204_inhabited
#tooth_pair verifyBlindVcPresentationTrusted_context vs tooth_verifyBlindVcPresentationTrusted_foreign_root
#tooth_pair ext6Mul_inv_cancel vs tooth_ext6Inv_zero_not_inverse
#tooth_pair ext6_rabin_fixed_is_constant vs tooth_ext6_third_iterate_fixes_nonconstant
#tooth_pair ext6Modulus_irreducible vs tooth_ext6_unit_modulus_factors
#tooth_pair rss_ext6_discrepancy_roots_le vs tooth_rss_ext6_zero_discrepancy_all_roots
#verify_inhabited ext6Mul_inv_cancel ext6Inv_inhabited
#tooth_pair prss_multi_key_hybrid vs tooth_prss_constant_expansion_distinguished
#verify_inhabited prss_multi_key_hybrid prss_multi_key_hybrid_inhabited
#verify_constructive subsets3Of5_intersect_nonempty
#verify_constructive tooth_subsets2Of5_disjoint
#verify_constructive toprfHolders_spec
#verify_constructive blind_vc_zkboo_selective_disclosure_sound_and_hiding

/-! ### Exports for lane cred-mig -/

theorem Vec.toList_nil {α : Type} : (Vec.nil : Vec α 0).toList = [] := by rfl

theorem Vec.toList_cons {α : Type} {n : Nat} (x : α) (xs : Vec α n) :
    (Vec.cons x xs).toList = x :: xs.toList := by rfl

theorem evalVcMerklePathBool_nil (epoch : UInt64) (layer : Nat) (cur : Lane6) :
    evalVcMerklePathBool epoch layer cur [] = cur := by rfl

theorem evalVcMerklePathBool_cons_false (epoch : UInt64) (layer : Nat) (cur sib : Lane6)
    (rest : List (Bool × Lane6)) :
    evalVcMerklePathBool epoch layer cur ((false, sib) :: rest) =
      evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair cur sib epoch layer) rest := by rfl

theorem evalVcMerklePathBool_cons_true (epoch : UInt64) (layer : Nat) (cur sib : Lane6)
    (rest : List (Bool × Lane6)) :
    evalVcMerklePathBool epoch layer cur ((true, sib) :: rest) =
      evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair sib cur epoch layer) rest := by rfl

theorem vcMerkleHashPair_eq (left right : Lane6) (epoch : UInt64) (layer : Nat) :
    vcMerkleHashPair left right epoch layer =
      state12Rate6 (absorbRate6Sponge3 (vcMerkleChunks left right epoch layer).1
        (vcMerkleChunks left right epoch layer).2.1 (vcMerkleChunks left right epoch layer).2.2) := by
  rfl

/-- The two children are the first two rate chunks of a Merkle node preimage. -/
theorem vcMerkleChunks_children_inj {l r l' r' : Lane6} {epoch : UInt64} {layer : Nat}
    (h : vcMerkleChunks l r epoch layer = vcMerkleChunks l' r' epoch layer) : l = l' ∧ r = r' :=
  ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h⟩

/-- An accepted opened repetition checked the disclosed-index list of the statement. -/
theorem verifyOpenedBlindVcRep_disclosedStrictAsc
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {schema : VcSchema} {issuerEpoch : UInt64} {treeDepth : Nat}
    {accRoot presCommit scopeTag : Lane6} {verifierScopeLimbs : Lane4}
    {disclosed : List (Nat × Goldilocks)} {repIdx : Nat} {expectedE : Fin 3}
    {o : OpenedBlindVcRep}
    (h : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth accRoot presCommit scopeTag
      verifierScopeLimbs disclosed repIdx expectedE o = true) :
    vcCheckDisclosedStrictAsc schema.arity disclosed = true := by
  unfold verifyOpenedBlindVcRep at h; dsimp only at h
  cases hG :
      (decide (o.e = expectedE) &&
       vcCheckDisclosedStrictAsc schema.arity disclosed &&
       decide (o.viewE.attrShares.length = schema.arity) &&
       decide (o.viewE1.attrShares.length = schema.arity) &&
       decide (o.viewE.merkleLevels.length = treeDepth) &&
       decide (o.viewE1.merkleLevels.length = treeDepth) &&
       vcCheckPartyDisclosedShares o.e o.viewE.attrShares disclosed &&
       vcCheckPartyDisclosedShares (vcNextParty3 o.e) o.viewE1.attrShares disclosed &&
       checkPartyPrgTape prgExpand treeDepth repIdx o.e o.viewE &&
       checkPartyPrgTape prgExpand treeDepth repIdx (vcNextParty3 o.e) o.viewE1) with
  | false => rw [hG] at h; cases h
  | true => simp only [Bool.and_eq_true] at hG; exact hG.1.1.1.1.1.1.1.1.2

theorem blindVcWitnessValid_iff (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth) :
    BlindVcWitnessValid stmt wit ↔
      (vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true ∧
      (∀ p ∈ stmt.disclosedAttrs, wit.attrs.toList[p.1]? = some p.2) ∧
      (∃ leaf : Lane6,
        computeVcPoseidon2Commit stmt.schema wit.attrs.toList wit.holderBlind vcAttrCommitTag =
          some leaf ∧
        evalVcMerklePathBool stmt.issuerEpoch 0 leaf wit.merkleSteps.toList =
          stmt.accumulatorRoot) ∧
      computeVcPoseidon2Commit stmt.schema wit.attrs.toList wit.presBlind vcPresCommitTag =
        some stmt.presCommit ∧
      computeVcScopeTag stmt.schema.schemaId wit.holderBlind stmt.verifierScopeLimbs =
        stmt.scopeTag) := Iff.rfl

/-- The three openings of one honest repetition agree on every overlapping view. -/
theorem vcRewoundCommitConflict_honest_table
    (H : List UInt8 → List UInt8) (nonce : Vec UInt8 32) (idx : Nat)
    (tr : BlindVcRepTriple) :
    ¬ VcRewoundCommitConflict H nonce idx
      (openBlindVcRep H nonce idx tr 0)
      (openBlindVcRep H nonce idx tr 1)
      (openBlindVcRep H nonce idx tr 2) := by
  simp only [VcRewoundCommitConflict, openBlindVcRep, vcNextParty3,
    ne_eq, not_true_eq_false, false_and, or_self, not_false_eq_true]
/-- An accepting run of the wire verifier decodes a key and a signature that the algebraic
core accepts at the FIPS 204 message representative of `(pk, ctx, msg)`. -/
theorem mldsaVerifyBytes204_accepts_core {budget : Nat} {pk msg ctx sig : List UInt8}
    (h : mldsaVerifyBytes204 budget pk msg ctx sig = true) :
    ∃ (A : PolyMat4) (t1Scaled : PolyVec4) (c : Poly256) (decoded : DecodedSignature204),
      decodeSignature204 sig = some decoded ∧
      mldsaVerify mldsa44ChallengeHash (fun _ => c) A t1Scaled
        (shake256Xof 64 (shake256Xof 64 pk ++ [0, UInt8.ofNat ctx.length] ++ ctx ++ msg))
        decoded.challenge decoded.z decoded.hints = true := by
  unfold mldsaVerifyBytes204 at h
  split at h
  · cases h
  · cases ha : expandA204 budget (pk.take 32) with
    | none => simp only [ha] at h; cases h
    | some A =>
      cases hd : decodeSignature204 sig with
      | none => simp only [ha, hd] at h; cases h
      | some decoded =>
        rw [ha, hd] at h
        dsimp only at h
        cases hc : sampleInBall204 budget decoded.challenge with
        | none => simp [hc] at h
        | some c =>
          rw [hc] at h
          exact ⟨A, _, c, decoded, rfl, h⟩

set_option exponentiation.threshold 1024 in
/-- **Rate-6 / Capacity-6 Width-12 `sponge12` 6-Limb Coherence (`blindVc_sponge12_rate6_cap6_six_limb_coherence`)**:
    Locks `BlindVcCollisionFinder` directly to `crates/qsag-cred/src/blind_vc.rs:43, 137-268`:
    1. `vcMaxAttrs = 32` (`MAX_VC_ATTRS = 32`); on the 3-block ZKBoo circuit (`schema : VcSchema`,
       `1 ≤ schema.arity ≤ 6`), `computeVcPoseidon2Commit` accepts iff `attrs.length = schema.arity`,
       absorbs `schema.arity` at `c2.x0` and `10*` pad `1` at `c2.x1` into `absorbRate6Sponge3`
       (with 6 zero-initialized capacity lanes), and squeezes 6 limbs (`Lane6`, `> 2^383` states);
    2. `computeVcScopeTag` absorbs two 6-limb blocks plus the full-block `10*` pad `⟨1, 0, 0, 0, 0, 0⟩`
       (`N = 12` multiple of rate `6`) into `absorbRate6Sponge3` and squeezes 6 limbs (`Lane6`);
    3. `vcMerkleHashPair` absorbs left/right 6-limb child digests plus 4 domain limbs and `10*` pad `1`
       at `c2.x4` (`N = 16`) into `absorbRate6Sponge3` and squeezes 6 limbs (`Lane6`). -/
theorem blindVc_sponge12_rate6_cap6_six_limb_coherence
    (schema : VcSchema) (attrs : List Goldilocks) (blind scopeLimbs : Lane4)
    (tag epoch : UInt64) (left right : Lane6) (layer : Nat) :
    ((attrs.length = schema.arity →
        (vcCommitChunks schema attrs blind tag).2.2 =
          ⟨Goldilocks.ofNat schema.arity, Goldilocks.one,
           Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ ∧
        computeVcPoseidon2Commit schema attrs blind tag =
          some (state12Rate6 (absorbRate6Sponge3
            (vcCommitChunks schema attrs blind tag).1
            (vcCommitChunks schema attrs blind tag).2.1
            (vcCommitChunks schema attrs blind tag).2.2))) ∧
     (attrs.length ≠ schema.arity → computeVcPoseidon2Commit schema attrs blind tag = none)) ∧
    ((vcScopeChunks schema.schemaId blind scopeLimbs).2.2 =
        ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero,
         Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ ∧
     computeVcScopeTag schema.schemaId blind scopeLimbs =
        state12Rate6 (absorbRate6Sponge3
          (vcScopeChunks schema.schemaId blind scopeLimbs).1
          (vcScopeChunks schema.schemaId blind scopeLimbs).2.1
          (vcScopeChunks schema.schemaId blind scopeLimbs).2.2)) ∧
    ((vcMerkleChunks left right epoch layer).2.2.x4 = Goldilocks.one ∧
     (vcMerkleChunks left right epoch layer).2.2.x5 = Goldilocks.zero ∧
     vcMerkleHashPair left right epoch layer =
        state12Rate6 (absorbRate6Sponge3 left right
          (vcMerkleChunks left right epoch layer).2.2)) ∧
    state12Cap6 (mkState12Of6 (vcCommitChunks schema attrs blind tag).1 lane6Zero) = lane6Zero ∧
    2 ^ 383 < goldilocksPrime ^ 6 := by
  refine ⟨⟨fun hEq => ⟨rfl, ?_⟩, fun hNe => ?_⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, by decide⟩
  · unfold computeVcPoseidon2Commit; simp only [hEq, ↓reduceIte]
  · unfold computeVcPoseidon2Commit; simp only [hNe, ↓reduceIte]

/-! ## Multi-Block `MAX_VC_ATTRS = 32` `sponge12` Commitment & `"QSAG.MLDSA.NONCE_BURN.V2"` Parity (`C5 #5, #6`) -/

/-- Structural 6-limb rate-block chunker for `sponge12` (`blind_vc.rs:137-154`). -/
def limbsToLane6Blocks : List Goldilocks → List Lane6
  | [] => []
  | [x0] => [⟨x0, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩]
  | [x0, x1] => [⟨x0, x1, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩]
  | [x0, x1, x2] => [⟨x0, x1, x2, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩]
  | [x0, x1, x2, x3] => [⟨x0, x1, x2, x3, Goldilocks.zero, Goldilocks.zero⟩]
  | [x0, x1, x2, x3, x4] => [⟨x0, x1, x2, x3, x4, Goldilocks.zero⟩]
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest =>
    ⟨x0, x1, x2, x3, x4, x5⟩ :: limbsToLane6Blocks rest

private def stripLastLane6 : Lane6 → List Goldilocks
  | ⟨x0, x1, x2, x3, x4, x5⟩ =>
    if x5 ≠ Goldilocks.zero then [x0, x1, x2, x3, x4]
    else if x4 ≠ Goldilocks.zero then [x0, x1, x2, x3]
    else if x3 ≠ Goldilocks.zero then [x0, x1, x2]
    else if x2 ≠ Goldilocks.zero then [x0, x1]
    else if x1 ≠ Goldilocks.zero then [x0]
    else []

private def decodePad1Blocks : List Lane6 → List Goldilocks
  | [] => []
  | [last] => stripLastLane6 last
  | c :: b :: rest => [c.x0, c.x1, c.x2, c.x3, c.x4, c.x5] ++ decodePad1Blocks (b :: rest)

private theorem limbsToLane6Blocks_pad1_nonempty :
    ∀ xs : List Goldilocks, limbsToLane6Blocks (xs ++ [Goldilocks.one]) ≠ []
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => by simp [limbsToLane6Blocks]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ => by simp [limbsToLane6Blocks]

private theorem decodePad1Blocks_limbsToLane6Blocks :
    ∀ xs : List Goldilocks, decodePad1Blocks (limbsToLane6Blocks (xs ++ [Goldilocks.one])) = xs
  | [] => by decide
  | [x0] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | [x0, x1] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | [x0, x1, x2] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | [x0, x1, x2, x3] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | [x0, x1, x2, x3, x4] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest => by
    have hNe := limbsToLane6Blocks_pad1_nonempty rest
    have ih := decodePad1Blocks_limbsToLane6Blocks rest
    simp only [List.cons_append, limbsToLane6Blocks]
    cases hBlk : limbsToLane6Blocks (rest ++ [Goldilocks.one]) with
    | nil => exact absurd hBlk hNe
    | cons b bs =>
      rw [hBlk] at ih
      simp only [decodePad1Blocks, ih]
      rfl

theorem limbsToLane6Blocks_pad1_injective {xs ys : List Goldilocks}
    (hEq : limbsToLane6Blocks (xs ++ [Goldilocks.one]) = limbsToLane6Blocks (ys ++ [Goldilocks.one])) :
    xs = ys := by
  have hDec := congrArg decodePad1Blocks hEq
  rwa [decodePad1Blocks_limbsToLane6Blocks, decodePad1Blocks_limbsToLane6Blocks] at hDec

/-- Multi-block Width-12 (`rate = 6, capacity = 6`) `sponge12` absorption from state `st`. -/
def sponge12AbsorbFrom (st : Poseidon2State12) : List Lane6 → Poseidon2State12
  | [] => st
  | c :: cs =>
    let stNext := poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 st) c) (state12Cap6 st))
    sponge12AbsorbFrom stNext cs

/-- Multi-block `sponge12` starting from the all-zero 12-limb state (`blind_vc.rs:137-154`). -/
def absorbRate6SpongeBlocks (blocks : List Lane6) : Poseidon2State12 :=
  sponge12AbsorbFrom (mkState12Of6 lane6Zero lane6Zero) blocks

private def sponge12Rev : List Lane6 → Poseidon2State12
  | [] => mkState12Of6 lane6Zero lane6Zero
  | c :: prevRev =>
    let prev := sponge12Rev prevRev
    poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 prev) c) (state12Cap6 prev))

private theorem sponge12AbsorbFrom_append (st : Poseidon2State12) :
    ∀ (as bs : List Lane6),
      sponge12AbsorbFrom st (as ++ bs) = sponge12AbsorbFrom (sponge12AbsorbFrom st as) bs
  | [], _ => rfl
  | _ :: as, bs => sponge12AbsorbFrom_append _ as bs

private theorem absorbRate6SpongeBlocks_eq_rev :
    ∀ bs : List Lane6, absorbRate6SpongeBlocks bs = sponge12Rev bs.reverse
  | [] => rfl
  | c :: cs => by
    unfold absorbRate6SpongeBlocks at *
    have hRev : (c :: cs).reverse = cs.reverse ++ [c] := List.reverse_cons
    rw [hRev]
    have hInd : ∀ r : List Lane6,
        sponge12Rev r = sponge12AbsorbFrom (mkState12Of6 lane6Zero lane6Zero) r.reverse := by
      intro r
      induction r with
      | nil => rfl
      | cons d ds ih =>
        simp only [List.reverse_cons, sponge12AbsorbFrom_append, ← ih]
        rfl
    rw [hInd (cs.reverse ++ [c]), List.reverse_append, List.reverse_singleton,
        List.reverse_reverse, List.singleton_append]

private theorem lane6Add_zero_left (c : Lane6) : lane6Add lane6Zero c = c := by
  have hz : ∀ x : Goldilocks, Goldilocks.zero.add x = x := fun x => LawfulCommRing.zero_add x
  rcases c with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [lane6Add, lane6Zero, hz]

theorem absorbRate6SpongeBlocks_three_eq (c0 c1 c2 : Lane6) :
    absorbRate6SpongeBlocks [c0, c1, c2] = absorbRate6Sponge3 c0 c1 c2 := by
  dsimp only [absorbRate6SpongeBlocks, sponge12AbsorbFrom, absorbRate6Sponge3]
  rw [state12Rate6_mk, state12Cap6_mk, lane6Add_zero_left]

/-- Non-initial sponge permutation input whose output capacity vanishes (`6` Goldilocks zeros, `< 2^-383`). -/
def Poseidon2Perm12ZeroCapRoot (st : Poseidon2State12) : Prop :=
  state12Cap6 (poseidon2Perm12 st) = lane6Zero

private theorem sponge12Rev_cap_collision_or_zero_root :
    ∀ {r₁ r₂ : List Lane6},
      r₁ ≠ r₂ →
      state12Cap6 (sponge12Rev r₁) = state12Cap6 (sponge12Rev r₂) →
      (∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB) ∨
      (∃ st : Poseidon2State12, Poseidon2Perm12ZeroCapRoot st)
  | [], [], hNe, _ => False.elim (hNe rfl)
  | [], c₂ :: t₂, _, hCap => by
    dsimp only [sponge12Rev, state12Cap6_mk] at hCap
    exact Or.inr ⟨_, hCap.symm⟩
  | c₁ :: t₁, [], _, hCap => by
    dsimp only [sponge12Rev, state12Cap6_mk] at hCap
    exact Or.inr ⟨_, hCap⟩
  | c₁ :: t₁, c₂ :: t₂, hNe, hCap => by
    let p₁ := sponge12Rev t₁
    let p₂ := sponge12Rev t₂
    let s₁ := mkState12Of6 (lane6Add (state12Rate6 p₁) c₁) (state12Cap6 p₁)
    let s₂ := mkState12Of6 (lane6Add (state12Rate6 p₂) c₂) (state12Cap6 p₂)
    if hs : s₁ = s₂ then
      have hCapPrev : state12Cap6 p₁ = state12Cap6 p₂ := by
        have hc := congrArg state12Cap6 hs
        rwa [state12Cap6_mk, state12Cap6_mk] at hc
      if ht : t₁ = t₂ then
        subst ht
        have hRate : lane6Add (state12Rate6 p₁) c₁ = lane6Add (state12Rate6 p₁) c₂ := by
          have hr := congrArg state12Rate6 hs
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        exact False.elim (hNe (congrArg (· :: t₁) (lane6Add_left_cancel hRate)))
      else
        exact sponge12Rev_cap_collision_or_zero_root ht hCapPrev
    else
      exact Or.inl ⟨s₁, s₂, hs, Or.inr hCap⟩

theorem absorbRate6SpongeBlocks_collision_reduction {bs₁ bs₂ : List Lane6}
    (hNe₁ : bs₁ ≠ []) (hNe₂ : bs₂ ≠ []) (hDiff : bs₁ ≠ bs₂)
    (hDig : state12Rate6 (absorbRate6SpongeBlocks bs₁) =
            state12Rate6 (absorbRate6SpongeBlocks bs₂)) :
    (∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB) ∨
    (∃ st : Poseidon2State12, Poseidon2Perm12ZeroCapRoot st) := by
  rw [absorbRate6SpongeBlocks_eq_rev, absorbRate6SpongeBlocks_eq_rev] at hDig
  have hrNe₁ : bs₁.reverse ≠ [] := fun h => hNe₁ (by simpa using congrArg List.reverse h)
  have hrNe₂ : bs₂.reverse ≠ [] := fun h => hNe₂ (by simpa using congrArg List.reverse h)
  have hrDiff : bs₁.reverse ≠ bs₂.reverse :=
    fun h => hDiff (by simpa using congrArg List.reverse h)
  match hR1 : bs₁.reverse, hR2 : bs₂.reverse with
  | [], _ => exact False.elim (hrNe₁ hR1)
  | _, [] => exact False.elim (hrNe₂ hR2)
  | c₁ :: t₁, c₂ :: t₂ =>
    rw [hR1, hR2] at hDig hrDiff
    let p₁ := sponge12Rev t₁
    let p₂ := sponge12Rev t₂
    let s₁ := mkState12Of6 (lane6Add (state12Rate6 p₁) c₁) (state12Cap6 p₁)
    let s₂ := mkState12Of6 (lane6Add (state12Rate6 p₂) c₂) (state12Cap6 p₂)
    if hs : s₁ = s₂ then
      have hCapPrev : state12Cap6 p₁ = state12Cap6 p₂ := by
        have hc := congrArg state12Cap6 hs
        rwa [state12Cap6_mk, state12Cap6_mk] at hc
      if ht : t₁ = t₂ then
        subst ht
        have hRate : lane6Add (state12Rate6 p₁) c₁ = lane6Add (state12Rate6 p₁) c₂ := by
          have hr := congrArg state12Rate6 hs
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        exact False.elim (hrDiff (congrArg (· :: t₁) (lane6Add_left_cancel hRate)))
      else
        exact sponge12Rev_cap_collision_or_zero_root ht hCapPrev
    else
      exact Or.inl ⟨s₁, s₂, hs, Or.inl hDig⟩

/-- Zero-pad attribute limbs to `max attrs.length 6` slots (`padded[..attrs.len().max(6)]`, `blind_vc.rs:178-179`). -/
def vcPadAttrs (attrs : List Goldilocks) : List Goldilocks :=
  attrs ++ List.replicate (6 - attrs.length) Goldilocks.zero

/-- 7-limb metadata & blind trailer `[blind[0..4], schema_lo, schema_hi + tag, arity]` (`blind_vc.rs:180-185`). -/
def vcCommitTrailerLimbs (schemaId : UInt64) (arity : Nat) (blind : Lane4) (tag : UInt64) :
    List Goldilocks :=
  [blind.x0, blind.x1, blind.x2, blind.x3,
   vcSchemaLo schemaId, vcSchemaHiWithTag schemaId tag, Goldilocks.ofNat arity]

/-- Rate-6 `Lane6` block sequence absorbed by `compute_vc_poseidon2_commit` (`blind_vc.rs:159-190`). -/
def vcCommitFullBlocks (schemaId : UInt64) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) :
    List Lane6 :=
  limbsToLane6Blocks
    (vcPadAttrs attrs ++ vcCommitTrailerLimbs schemaId attrs.length blind tag ++ [Goldilocks.one])

/-- **Full `MAX_VC_ATTRS = 32` `Poseidon2` Credential Commitment (`computeVcPoseidon2CommitFull`, `C5 #5`)**:
    Matches `blind_vc.rs:159-190`: accepts iff `1 ≤ attrs.length ≤ vcMaxAttrs` (`= 32`), pads small
    attribute vectors to 6 slots while absorbing all `7..32` attributes into rate-6 / capacity-6
    `absorbRate6SpongeBlocks`, and squeezes the 6-limb digest `Lane6`. -/
def computeVcPoseidon2CommitFull
    (schemaId : UInt64) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) : Option Lane6 :=
  if decide (1 ≤ attrs.length ∧ attrs.length ≤ vcMaxAttrs) then
    some (state12Rate6 (absorbRate6SpongeBlocks (vcCommitFullBlocks schemaId attrs blind tag)))
  else
    none

/-- Exact equivalence between `computeVcPoseidon2CommitFull` (`1 ≤ arity ≤ 32`) and the 3-block
    ZKBoo `computeVcPoseidon2Commit` whenever `schema : VcSchema` (`1 ≤ schema.arity ≤ 6`) and
    `attrs.length = schema.arity`. -/
theorem computeVcPoseidon2CommitFull_eq_small
    (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64)
    (hLen : attrs.length = schema.arity) :
    computeVcPoseidon2CommitFull schema.schemaId attrs blind tag =
      computeVcPoseidon2Commit schema attrs blind tag := by
  have hPos : 1 ≤ attrs.length := hLen ▸ schema.hArityPos
  have hLe6 : attrs.length ≤ 6 := hLen ▸ schema.hArityLe
  have hLe32 : attrs.length ≤ vcMaxAttrs := Nat.le_trans hLe6 (by decide)
  have hRange : decide (1 ≤ attrs.length ∧ attrs.length ≤ vcMaxAttrs) = true :=
    decide_eq_true ⟨hPos, hLe32⟩
  unfold computeVcPoseidon2CommitFull computeVcPoseidon2Commit
  rw [hRange]
  simp only [hLen, ↓reduceIte]
  congr 1
  have hBlks : vcCommitFullBlocks schema.schemaId attrs blind tag =
      [(vcCommitChunks schema attrs blind tag).1,
       (vcCommitChunks schema attrs blind tag).2.1,
       (vcCommitChunks schema attrs blind tag).2.2] := by
    unfold vcCommitFullBlocks vcPadAttrs vcCommitTrailerLimbs vcCommitChunks
    rw [← hLen]
    match attrs, hPos, hLe6 with
    | [a0], _, _ => rfl
    | [a0, a1], _, _ => rfl
    | [a0, a1, a2], _, _ => rfl
    | [a0, a1, a2, a3], _, _ => rfl
    | [a0, a1, a2, a3, a4], _, _ => rfl
    | [a0, a1, a2, a3, a4, a5], _, _ => rfl
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, h6 => simp at h6
  rw [hBlks, absorbRate6SpongeBlocks_three_eq]

private theorem vcCommitFullBlocks_injective
    {sid₁ sid₂ : UInt64} {attrs₁ attrs₂ : List Goldilocks} {blind₁ blind₂ : Lane4} {tag : UInt64}
    (hLe₁ : attrs₁.length ≤ vcMaxAttrs) (hLe₂ : attrs₂.length ≤ vcMaxAttrs)
    (hEq : vcCommitFullBlocks sid₁ attrs₁ blind₁ tag = vcCommitFullBlocks sid₂ attrs₂ blind₂ tag) :
    sid₁ = sid₂ ∧ attrs₁ = attrs₂ ∧ blind₁ = blind₂ := by
  unfold vcCommitFullBlocks at hEq
  have hMsgEq := limbsToLane6Blocks_pad1_injective hEq
  have hRevEq := congrArg List.reverse hMsgEq
  simp only [vcCommitTrailerLimbs, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at hRevEq
  injection hRevEq with hAr t1
  injection t1 with hHi t2
  injection t2 with hLo t3
  injection t3 with hb3 t4
  injection t4 with hb2 t5
  injection t5 with hb1 t6
  injection t6 with hb0 hPadRevEq
  have hp32 : vcMaxAttrs < goldilocksPrime := by decide
  have hLt₁ : attrs₁.length < goldilocksPrime := Nat.lt_of_le_of_lt hLe₁ hp32
  have hLt₂ : attrs₂.length < goldilocksPrime := Nat.lt_of_le_of_lt hLe₂ hp32
  have hLenEq : attrs₁.length = attrs₂.length := by
    have hv := congrArg Goldilocks.val hAr
    simp only [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hLt₁, Nat.mod_eq_of_lt hLt₂] at hv
    exact hv
  have hSid : sid₁ = sid₂ := vcSchema_limbs_injective hLo hHi
  have hBlind : blind₁ = blind₂ := Lane4.ext hb0 hb1 hb2 hb3
  have hPadEq : vcPadAttrs attrs₁ = vcPadAttrs attrs₂ := by
    simpa only [List.reverse_reverse] using congrArg List.reverse hPadRevEq
  unfold vcPadAttrs at hPadEq
  have hAttrs : attrs₁ = attrs₂ := (List.append_inj hPadEq hLenEq).1
  exact ⟨hSid, hAttrs, hBlind⟩

/-- **Full `1 ≤ arity ≤ 32` `BlindVC` Commitment Acceptance & Sponge Binding
    (`computeVcPoseidon2CommitFull_arity32_binding`, `C5 #5`)**:
    1. `vcMaxAttrs = 32` (`MAX_VC_ATTRS = 32`); `computeVcPoseidon2CommitFull` accepts iff
       `1 ≤ attrs.length ∧ attrs.length ≤ 32` (including full 32-attribute credentials);
    2. Any two distinct openings `(sid₁, attrs₁, blind₁) ≠ (sid₂, attrs₂, blind₂)` yielding `some c`
       constructively exhibit either `Poseidon2Perm12Sponge6Collision` or `Poseidon2Perm12ZeroCapRoot`. -/
theorem computeVcPoseidon2CommitFull_arity32_binding :
    vcMaxAttrs = 32 ∧
    (∀ (sid : UInt64) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64),
      (computeVcPoseidon2CommitFull sid attrs blind tag).isSome = true ↔
        1 ≤ attrs.length ∧ attrs.length ≤ 32) ∧
    (∀ (sid₁ sid₂ : UInt64) (attrs₁ attrs₂ : List Goldilocks)
       (blind₁ blind₂ : Lane4) (tag : UInt64) (c : Lane6),
      computeVcPoseidon2CommitFull sid₁ attrs₁ blind₁ tag = some c →
      computeVcPoseidon2CommitFull sid₂ attrs₂ blind₂ tag = some c →
      (sid₁, attrs₁, blind₁) ≠ (sid₂, attrs₂, blind₂) →
      (∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB) ∨
      (∃ st : Poseidon2State12, Poseidon2Perm12ZeroCapRoot st)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro sid attrs blind tag
    unfold computeVcPoseidon2CommitFull vcMaxAttrs
    if h : 1 ≤ attrs.length ∧ attrs.length ≤ 32 then
      simp [h]
    else
      simp [h]
  · intro sid₁ sid₂ attrs₁ attrs₂ blind₁ blind₂ tag c h1 h2 hNe
    unfold computeVcPoseidon2CommitFull at h1 h2
    cases hOk1 : decide (1 ≤ attrs₁.length ∧ attrs₁.length ≤ vcMaxAttrs) with
    | false => rw [hOk1] at h1; cases h1
    | true =>
      cases hOk2 : decide (1 ≤ attrs₂.length ∧ attrs₂.length ≤ vcMaxAttrs) with
      | false => rw [hOk2] at h2; cases h2
      | true =>
        rw [hOk1] at h1
        rw [hOk2] at h2
        simp only [↓reduceIte, Option.some.injEq] at h1 h2
        have hb1 := (of_decide_eq_true hOk1).2
        have hb2 := (of_decide_eq_true hOk2).2
        have hBlkDiff : vcCommitFullBlocks sid₁ attrs₁ blind₁ tag ≠
            vcCommitFullBlocks sid₂ attrs₂ blind₂ tag := by
          intro hEq
          obtain ⟨hs, ha, hbl⟩ := vcCommitFullBlocks_injective hb1 hb2 hEq
          exact hNe (by rw [hs, ha, hbl])
        exact absorbRate6SpongeBlocks_collision_reduction
          (limbsToLane6Blocks_pad1_nonempty _)
          (limbsToLane6Blocks_pad1_nonempty _)
          hBlkDiff (h1.trans h2.symm)

/-- **`#tooth` (`tooth_computeVcPoseidon2CommitFull_rejects_arity33`)**:
    `computeVcPoseidon2CommitFull` rejects attribute lists exceeding `vcMaxAttrs = 32` (`= none`). -/
theorem tooth_computeVcPoseidon2CommitFull_rejects_arity33 :
    ∃ (sid : UInt64) (attrs : List Goldilocks) (blind : Lane4),
      vcMaxAttrs < attrs.length ∧
      computeVcPoseidon2CommitFull sid attrs blind vcAttrCommitTag = none := by
  refine ⟨0, List.replicate 33 Goldilocks.one,
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, by decide, ?_⟩
  unfold computeVcPoseidon2CommitFull vcMaxAttrs
  simp

/-- Framed preimage injectivity and domain-tag parity for `"QSAG.MLDSA.NONCE_BURN.V2"` and
    `"QSAG.BLIND_VC.SD_LIMBO.V1"` (`C5 #6`). -/
theorem mldsaNonceBurnPreimage_injective
    {k₁ k₂ l₁ l₂ b₁ b₂ : List UInt8}
    (hk₁ : k₁.length < 256 ^ 8) (hk₂ : k₂.length < 256 ^ 8)
    (hl₁ : l₁.length < 256 ^ 8) (hl₂ : l₂.length < 256 ^ 8)
    (hb₁ : b₁.length < 256 ^ 8) (hb₂ : b₂.length < 256 ^ 8)
    (hEq : mldsaNonceBurnPreimage k₁ l₁ b₁ = mldsaNonceBurnPreimage k₂ l₂ b₂) :
    k₁ = k₂ ∧ l₁ = l₂ ∧ b₁ = b₂ ∧
    mldsaNonceBurnDomainTag =
      (['Q', 'S', 'A', 'G', '.', 'M', 'L', 'D', 'S', 'A', '.',
        'N', 'O', 'N', 'C', 'E', '_', 'B', 'U', 'R', 'N', '.', 'V', '2'].map
        (fun c => UInt8.ofNat c.toNat)) ∧
    vcSdLimboDomainTag =
      (['Q', 'S', 'A', 'G', '.', 'B', 'L', 'I', 'N', 'D', '_', 'V', 'C', '.',
        'S', 'D', '_', 'L', 'I', 'M', 'B', 'O', '.', 'V', '1'].map
        (fun c => UInt8.ofNat c.toNat)) := by
  unfold mldsaNonceBurnPreimage at hEq
  have hAll1 : ∀ f ∈ [k₁, l₁, b₁], f.length < 256 ^ 8 := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | h1
    · exact hk₁
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hl₁
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact hb₁
        · cases h3
  have hAll2 : ∀ g ∈ [k₂, l₂, b₂], g.length < 256 ^ 8 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | h1
    · exact hk₂
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hl₂
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact hb₂
        · cases h3
  have hFrEq := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hEq
  injection hFrEq with ek t1
  injection t1 with el t2
  injection t2 with eb _
  exact ⟨ek, el, eb, by decide, by decide⟩

/-! ## Shamir Threshold ML-DSA (`n ≤ 64`, `2t - 1 ≤ m ≤ 16`) Conversion & Byzantine Soundness (`C5 #6`) -/

/-- Maximum custodian count for Shamir threshold ML-DSA (`MAX_THRESHOLD_MLDSA_PARTIES = 64`). -/
def shamirMldsaMaxCustodians : Nat := 64

/-- Maximum RSS signing-engine quorum size (`MAX_MPC_PARTIES = 16`). -/
def shamirMldsaMaxQuorum : Nat := 16

/-- Parameter validation matching `ThresholdMlDsaDkgConfig::validate_shamir` and
    `threshold_sign_mldsa_party` (`threshold_mldsa_shamir.rs:77-88`, `threshold_mldsa.rs:2117-2125`):
    `2 ≤ t`, `n ≤ 64`, `2t - 1 ≤ n`, and `2t - 1 ≤ m ≤ 16` (hence `t ≤ 8`). -/
def shamirMldsaParamsValid (t n m : Nat) : Bool :=
  decide (2 ≤ t) &&
  decide (n ≤ shamirMldsaMaxCustodians) &&
  decide (2 * t - 1 ≤ n) &&
  decide (2 * t - 1 ≤ m) &&
  decide (m ≤ shamirMldsaMaxQuorum)

theorem shamirMldsaParamsValid_bounds {t n m : Nat}
    (h : shamirMldsaParamsValid t n m = true) :
    2 ≤ t ∧ t ≤ 8 ∧ n ≤ 64 ∧ 2 * t - 1 ≤ n ∧ 2 * t - 1 ≤ m ∧ m ≤ 16 := by
  unfold shamirMldsaParamsValid shamirMldsaMaxCustodians shamirMldsaMaxQuorum at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1.1, by omega, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private def polyAddCoeffs204 : List Fq204 → List Fq204 → List Fq204
  | [], ds => ds
  | cs, [] => cs
  | c :: cs, d :: ds => Fq204.add c d :: polyAddCoeffs204 cs ds

private theorem polyAddCoeffs204_length :
    ∀ (cs ds : List Fq204), (polyAddCoeffs204 cs ds).length = Nat.max cs.length ds.length
  | [], ds => by simp [polyAddCoeffs204]
  | c :: cs, [] => by simp [polyAddCoeffs204]
  | c :: cs, d :: ds => by
    simp [polyAddCoeffs204, polyAddCoeffs204_length cs ds, Nat.succ_max_succ]

private theorem evalCoeffs_polyAddCoeffs204 :
    ∀ (cs ds : List Fq204) (x : Fq204),
      RoundPoly.evalCoeffs (polyAddCoeffs204 cs ds) x =
        Fq204.add (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x)
  | [], ds, x => by
    change RoundPoly.evalCoeffs ds x = Fq204.add Fq204.zero (RoundPoly.evalCoeffs ds x)
    exact (Fq204.zero_add _).symm
  | c :: cs, [], x => by
    change RoundPoly.evalCoeffs (c :: cs) x = Fq204.add (RoundPoly.evalCoeffs (c :: cs) x) Fq204.zero
    exact (Fq204.add_zero _).symm
  | c :: cs, d :: ds, x => by
    simp only [polyAddCoeffs204, RoundPoly.evalCoeffs_cons, evalCoeffs_polyAddCoeffs204 cs ds x]
    change Fq204.add (Fq204.add c d)
        (Fq204.mul x (Fq204.add (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x))) =
      Fq204.add (Fq204.add c (Fq204.mul x (RoundPoly.evalCoeffs cs x)))
        (Fq204.add d (Fq204.mul x (RoundPoly.evalCoeffs ds x)))
    rw [Fq204.left_distrib,
        Fq204.add_assoc c d _,
        ← Fq204.add_assoc d _ _,
        Fq204.add_comm d (Fq204.mul x (RoundPoly.evalCoeffs cs x)),
        Fq204.add_assoc (Fq204.mul x (RoundPoly.evalCoeffs cs x)) d _,
        ← Fq204.add_assoc c _ _]

def eraseFirstFq204 (x : Fq204) : List Fq204 → List Fq204
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseFirstFq204 x ys

private theorem eraseFirstFq204_length_of_mem {x : Fq204} :
    ∀ {xs : List Fq204}, x ∈ xs → (eraseFirstFq204 x xs).length + 1 = xs.length
  | [], h => nomatch h
  | y :: ys, h => by
    unfold eraseFirstFq204
    if hxy : x = y then
      simp [hxy]
    else
      rcases List.mem_cons.mp h with rfl | hm
      · exact absurd rfl hxy
      · simp only [hxy, ↓reduceIte, List.length_cons]
        have ih := eraseFirstFq204_length_of_mem hm
        omega

private theorem mem_eraseFirstFq204_of_ne {y x : Fq204} (hne : y ≠ x) :
    ∀ {xs : List Fq204}, y ∈ xs → y ∈ eraseFirstFq204 x xs
  | [], h => nomatch h
  | z :: zs, h => by
    unfold eraseFirstFq204
    if hxz : x = z then
      subst hxz
      rcases List.mem_cons.mp h with rfl | hm
      · exact absurd rfl hne
      · simp [hm]
    else
      simp only [hxz, ↓reduceIte, List.mem_cons]
      rcases List.mem_cons.mp h with rfl | hm
      · exact Or.inl rfl
      · exact Or.inr (mem_eraseFirstFq204_of_ne hne hm)

private theorem not_mem_eraseFirstFq204_of_nodup {x : Fq204} :
    ∀ {xs : List Fq204}, xs.Nodup → x ∉ eraseFirstFq204 x xs
  | [], _ => by simp [eraseFirstFq204]
  | y :: ys, .cons hnot hnd => by
    unfold eraseFirstFq204
    if hxy : x = y then
      subst hxy
      simp only [↓reduceIte]
      exact fun hm => hnot x hm rfl
    else
      simp only [hxy, ↓reduceIte, List.mem_cons]
      rintro (hFalse | hm)
      · exact hFalse.elim
      · exact not_mem_eraseFirstFq204_of_nodup hnd hm

/-- Lagrange basis polynomial `L_{pt}(X) = (∏_{o ∈ nodes \ {pt}} (X - o)) · (∏_{o ∈ nodes \ {pt}} (pt - o))⁻¹`
    over `Fq204` (`lagrange_weights`, `threshold_mldsa.rs:2027-2042`). -/
def lagrangeBasisCoeffs204 (nodes : List Fq204) (pt : Fq204) : List Fq204 :=
  let others := eraseFirstFq204 pt nodes
  let denom := RoundPoly.evalCoeffs (RoundPoly.vanishingCoeffs others) pt
  (RoundPoly.vanishingCoeffs others).map (Fq204.mul (Fq204.inv denom))

def lagrangeWeightAt204 (nodes : List Fq204) (pt target : Fq204) : Fq204 :=
  RoundPoly.evalCoeffs (lagrangeBasisCoeffs204 nodes pt) target

/-- Lagrange weights mapping degree-`< nodes.length` evaluations at `nodes` to the evaluation at `target`
    (`threshold_mldsa.rs:2027-2042`). -/
def lagrangeWeightsFq204 (nodes : List Fq204) (target : Fq204) : List Fq204 :=
  nodes.map (fun pt => lagrangeWeightAt204 nodes pt target)

private theorem lagrangeWeightAt204_kron {nodes : List Fq204} (hNd : nodes.Nodup)
    {pt y : Fq204} (_hPt : pt ∈ nodes) (hY : y ∈ nodes) :
    lagrangeWeightAt204 nodes pt y = if y = pt then Fq204.one else Fq204.zero := by
  unfold lagrangeWeightAt204 lagrangeBasisCoeffs204
  dsimp only
  have hMap : ∀ (s : Fq204) (cs : List Fq204) (z : Fq204),
      RoundPoly.evalCoeffs (cs.map (Fq204.mul s)) z = Fq204.mul s (RoundPoly.evalCoeffs cs z) :=
    fun s cs z => RoundPoly.evalCoeffs_map_mul s cs z
  rw [hMap]
  if hyEq : y = pt then
    subst hyEq
    simp only [↓reduceIte]
    have hNotMem : y ∉ eraseFirstFq204 y nodes := not_mem_eraseFirstFq204_of_nodup hNd
    have hDenNz : RoundPoly.evalCoeffs (RoundPoly.vanishingCoeffs (eraseFirstFq204 y nodes)) y ≠
        CommRingOps.zero :=
      RoundPoly.evalCoeffs_vanishingCoeffs_ne_zero (by decide) _ y hNotMem
    rw [Fq204.mul_comm, Fq204.mul_inv_cancel hDenNz]
  else
    simp only [hyEq, ↓reduceIte]
    have hIn : y ∈ eraseFirstFq204 pt nodes := mem_eraseFirstFq204_of_ne hyEq hY
    have hVan : RoundPoly.evalCoeffs (RoundPoly.vanishingCoeffs (eraseFirstFq204 pt nodes)) y =
        CommRingOps.zero :=
      RoundPoly.evalCoeffs_vanishingCoeffs_of_mem _ y hIn
    rw [hVan]
    exact Fq204.mul_zero _

private def lagrangeInterpLoop204 (allNodes : List Fq204) : List Fq204 → List Fq204 → List Fq204
  | [], _ => []
  | _, [] => []
  | pt :: ptsRest, sh :: shRest =>
    polyAddCoeffs204 ((lagrangeBasisCoeffs204 allNodes pt).map (Fq204.mul sh))
      (lagrangeInterpLoop204 allNodes ptsRest shRest)

/-- Explicit degree-`< nodes.length` Lagrange interpolant over `Fq204`. -/
def lagrangeInterpCoeffs204 (nodes shares : List Fq204) : List Fq204 :=
  lagrangeInterpLoop204 nodes nodes shares

private theorem lagrangeInterpLoop204_length_le (allNodes : List Fq204) :
    ∀ (curNodes curShares : List Fq204),
      (∀ pt ∈ curNodes, pt ∈ allNodes) →
      (lagrangeInterpLoop204 allNodes curNodes curShares).length ≤ allNodes.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], _ => Nat.zero_le _
  | pt :: ptsRest, sh :: shRest, hSub => by
    simp only [lagrangeInterpLoop204, polyAddCoeffs204_length, List.length_map]
    have hBasisLen : (lagrangeBasisCoeffs204 allNodes pt).length = allNodes.length := by
      unfold lagrangeBasisCoeffs204
      simp only [List.length_map, RoundPoly.vanishingCoeffs_length]
      exact eraseFirstFq204_length_of_mem (hSub pt (.head _))
    have ih := lagrangeInterpLoop204_length_le allNodes ptsRest shRest
      (fun z hz => hSub z (.tail _ hz))
    rw [hBasisLen]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, ih⟩

private theorem lagrangeInterpLoop204_eval_eq_dot (allNodes : List Fq204) (target : Fq204) :
    ∀ (curNodes curShares : List Fq204),
      RoundPoly.evalCoeffs (lagrangeInterpLoop204 allNodes curNodes curShares) target =
        ringDot (curNodes.map (fun pt => lagrangeWeightAt204 allNodes pt target)) curShares
  | [], _ => by simp [lagrangeInterpLoop204, ringDot]
  | _ :: _, [] => by simp [lagrangeInterpLoop204, ringDot]
  | pt :: ptsRest, sh :: shRest => by
    simp only [lagrangeInterpLoop204, List.map_cons, evalCoeffs_polyAddCoeffs204,
      lagrangeInterpLoop204_eval_eq_dot allNodes target ptsRest shRest]
    have hTerm : RoundPoly.evalCoeffs ((lagrangeBasisCoeffs204 allNodes pt).map (Fq204.mul sh)) target =
        Fq204.mul (lagrangeWeightAt204 allNodes pt target) sh := by
      have hMap := RoundPoly.evalCoeffs_map_mul sh (lagrangeBasisCoeffs204 allNodes pt) target
      exact hMap.trans (Fq204.mul_comm sh _)
    rw [hTerm]
    rfl

private theorem ringDot_kron_mem {allNodes : List Fq204} (hNd : allNodes.Nodup) :
    ∀ {curNodes curShares : List Fq204},
      curNodes.Nodup →
      (∀ pt ∈ curNodes, pt ∈ allNodes) →
      ∀ {p : Fq204 × Fq204},
        p ∈ List.zip curNodes curShares →
        ringDot (curNodes.map (fun pt => lagrangeWeightAt204 allNodes pt p.1)) curShares = p.2
  | [], _, _, _, _, hp => nomatch hp
  | _ :: _, [], _, _, _, hp => nomatch hp
  | pt :: ptsRest, sh :: shRest, .cons hnot hndRest, hSub, ⟨x, y⟩, hp => by
    have hZeroNotIn : ∀ {ns ss : List Fq204} {z : Fq204},
        z ∈ allNodes →
        (∀ q ∈ ns, q ∈ allNodes) →
        (∀ q ∈ ns, z ≠ q) →
        ringDot (ns.map (fun q => lagrangeWeightAt204 allNodes q z)) ss = Fq204.zero := by
      intro ns
      induction ns with
      | nil => intro _ _ _ _ _; rfl
      | cons q qs ihq =>
        intro ss z hzIn hSubQ hNeQ
        cases ss with
        | nil => rfl
        | cons s ss' =>
          simp only [List.map_cons, ringDot, dotVec]
          have hw0 : lagrangeWeightAt204 allNodes q z = Fq204.zero := by
            rw [lagrangeWeightAt204_kron hNd (hSubQ q (.head _)) hzIn]
            have hne : z ≠ q := hNeQ q (.head _)
            simp [hne]
          rw [hw0]
          change Fq204.add (Fq204.mul Fq204.zero s)
              (ringDot (qs.map (fun q' => lagrangeWeightAt204 allNodes q' z)) ss') = Fq204.zero
          rw [Fq204.zero_mul, Fq204.zero_add]
          exact ihq hzIn (fun q' hq' => hSubQ q' (.tail _ hq'))
            (fun q' hq' => hNeQ q' (.tail _ hq'))
    rcases List.mem_cons.mp hp with hHead | hTail
    · cases hHead
      dsimp only
      simp only [List.map_cons, ringDot, dotVec]
      have hw1 : lagrangeWeightAt204 allNodes pt pt = Fq204.one := by
        rw [lagrangeWeightAt204_kron hNd (hSub pt (.head _)) (hSub pt (.head _))]
        simp
      rw [hw1]
      change Fq204.add (Fq204.mul Fq204.one sh)
          (ringDot (ptsRest.map (fun q => lagrangeWeightAt204 allNodes q pt)) shRest) = sh
      rw [Fq204.one_mul,
          hZeroNotIn (hSub pt (.head _)) (fun q hq => hSub q (.tail _ hq))
            (fun q hq heq => hnot q hq heq),
          Fq204.add_zero]
    · dsimp only
      simp only [List.map_cons, ringDot, dotVec]
      have hxInRest : x ∈ ptsRest := by
        have hFst := List.of_mem_zip hTail
        exact hFst.1
      have hxNePt : x ≠ pt := fun heq => hnot x hxInRest heq.symm
      have hw0 : lagrangeWeightAt204 allNodes pt x = Fq204.zero := by
        rw [lagrangeWeightAt204_kron hNd (hSub pt (.head _)) (hSub x (.tail _ hxInRest))]
        simp [hxNePt]
      rw [hw0]
      change Fq204.add (Fq204.mul Fq204.zero sh)
          (ringDot (ptsRest.map (fun q => lagrangeWeightAt204 allNodes q x)) shRest) = y
      rw [Fq204.zero_mul, Fq204.zero_add]
      exact ringDot_kron_mem hNd hndRest (fun q hq => hSub q (.tail _ hq)) hTail

private theorem poly204_eq_of_agree_ge_t {t : Nat} (ht : 1 ≤ t)
    {Q P S : List Fq204}
    (hQLen : Q.length ≤ t) (hPLen : P.length ≤ t)
    (hSNd : S.Nodup) (hSCard : t ≤ S.length)
    (hAgree : ∀ x ∈ S, RoundPoly.evalCoeffs Q x = RoundPoly.evalCoeffs P x)
    (target : Fq204) :
    RoundPoly.evalCoeffs Q target = RoundPoly.evalCoeffs P target := by
  if hEq : RoundPoly.evalCoeffs Q target = RoundPoly.evalCoeffs P target then
    exact hEq
  else
    exfalso
    let diff := RoundPoly.subCoeffs Q P
    have hDiffLen : diff.length ≤ (t - 1) + 1 := by
      dsimp only [diff]
      rw [RoundPoly.subCoeffs_length]
      have hMax : Nat.max Q.length P.length ≤ t := Nat.max_le.mpr ⟨hQLen, hPLen⟩
      omega
    have hDiffTargetNz : RoundPoly.evalCoeffs diff target ≠ CommRingOps.zero := by
      dsimp only [diff]
      rw [RoundPoly.evalCoeffs_sub]
      exact fun hz => hEq (LawfulCommRing.sub_eq_zero_iff.mp hz)
    have hFiltGen : ∀ (U : List Fq204),
        (∀ x ∈ U, RoundPoly.evalCoeffs Q x = RoundPoly.evalCoeffs P x) →
        U.filter (fun r => decide (RoundPoly.evalCoeffs diff r = CommRingOps.zero)) = U := by
      intro U
      induction U with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro hAg
        have hx0 : RoundPoly.evalCoeffs diff x = CommRingOps.zero := by
          dsimp only [diff]
          rw [RoundPoly.evalCoeffs_sub, hAg x (.head _), LawfulCommRing.sub_self]
        simp only [List.filter_cons, decide_eq_true hx0, ↓reduceIte]
        exact congrArg (x :: ·) (ih (fun y hy => hAg y (.tail _ hy)))
    have hFiltEq := hFiltGen S hAgree
    have hRootsLe := RoundPoly.roots_nodup_length_le (t - 1) diff S hSNd hDiffLen ⟨target, hDiffTargetNz⟩
    rw [hFiltEq] at hRootsLe
    omega

/-- Exact Shamir-to-additive signing session key conversion (`shamir_session_key`,
    `threshold_mldsa.rs:2055-2085`): uses the first `t` quorum shares to define the degree-`< t`
    interpolant, checks that all remaining `m - t` quorum shares vanish against their Lagrange
    predictions (`KeyShareInconsistent` otherwise), and returns the `t` additive shares
    `λ_i(0) · share_i` summing to `P(0)`. -/
def shamirSessionKeyConvert (t : Nat) (pts shares : List Fq204) : Option (List Fq204) :=
  if decide (1 ≤ t ∧ t ≤ pts.length ∧ pts.length = shares.length) then
    let ptsBase := pts.take t
    let sharesBase := shares.take t
    let extraPairs := (List.zip pts shares).drop t
    let checksOk := extraPairs.all (fun ps =>
      decide (Fq204.sub ps.2 (ringDot (lagrangeWeightsFq204 ptsBase ps.1) sharesBase) = Fq204.zero))
    if checksOk then
      some (List.zipWith Fq204.mul (lagrangeWeightsFq204 ptsBase Fq204.zero) sharesBase)
    else
      none
  else
    none

private theorem sum_zipWith_mul_eq_ringDot :
    ∀ (ws ss : List Fq204),
      (List.zipWith Fq204.mul ws ss).foldr Fq204.add Fq204.zero = ringDot ws ss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | w :: ws, s :: ss => by
    simp only [List.zipWith_cons_cons, List.foldr_cons, ringDot, dotVec]
    exact congrArg (Fq204.add (Fq204.mul w s)) (sum_zipWith_mul_eq_ringDot ws ss)

private theorem nodup_take_of_nodup {α : Type} :
    ∀ (k : Nat) {xs : List α}, xs.Nodup → (xs.take k).Nodup
  | 0, _, _ => .nil
  | _ + 1, [], _ => .nil
  | k + 1, _ :: _xs, .cons hnot hnd =>
    .cons (fun z hz => hnot z (List.mem_of_mem_take hz)) (nodup_take_of_nodup k hnd)

private theorem take_map_fq204 {α β : Type} (f : α → β) :
    ∀ (k : Nat) (xs : List α), (xs.map f).take k = (xs.take k).map f
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => congrArg (f x :: ·) (take_map_fq204 f k xs)

private theorem mem_zip_map_self {α β : Type} (f : α → β) :
    ∀ {xs : List α} {x : α}, x ∈ xs → (x, f x) ∈ List.zip xs (xs.map f)
  | [], _, hx => nomatch hx
  | a :: as, _, hx => by
    rcases List.mem_cons.mp hx with rfl | hTl
    · exact .head _
    · exact .tail _ (mem_zip_map_self f hTl)

/-- **Shamir Threshold ML-DSA Conversion Completeness (`shamirSessionKey_complete`, `C5 #6`)**:
    For any valid parameter tuple `(t, n, m)` (`n ≤ 64`, `2t - 1 ≤ m ≤ 16`), distinct quorum
    evaluation points `pts` of size `m`, and degree-`< t` secret polynomial `coeffs`,
    honest Shamir shares `pts.map (RoundPoly.evalCoeffs coeffs)` pass all `m - t` syndrome checks
    and convert into additive shares whose sum equals the exact secret `RoundPoly.evalCoeffs coeffs 0`. -/
theorem shamirSessionKey_complete {t n m : Nat}
    (hParams : shamirMldsaParamsValid t n m = true)
    (pts coeffs : List Fq204)
    (hPtsNd : pts.Nodup) (hPtsLen : pts.length = m)
    (hDeg : coeffs.length ≤ t) :
    let shares := pts.map (RoundPoly.evalCoeffs coeffs)
    ∃ additiveShares : List Fq204,
      shamirSessionKeyConvert t pts shares = some additiveShares ∧
      additiveShares.length = t ∧
      additiveShares.foldr Fq204.add Fq204.zero = RoundPoly.evalCoeffs coeffs Fq204.zero := by
  obtain ⟨ht2, _, _, _, hmLo, _⟩ := shamirMldsaParamsValid_bounds hParams
  have ht1 : 1 ≤ t := by omega
  have htLe : t ≤ pts.length := by omega
  let shares := pts.map (RoundPoly.evalCoeffs coeffs)
  have hShLen : pts.length = shares.length := (List.length_map _).symm
  let ptsBase := pts.take t
  let sharesBase := shares.take t
  have hBaseNd : ptsBase.Nodup := nodup_take_of_nodup t hPtsNd
  have hBaseLen : ptsBase.length = t := List.length_take_of_le htLe
  have hShBaseEq : sharesBase = ptsBase.map (RoundPoly.evalCoeffs coeffs) := by
    dsimp only [sharesBase, shares, ptsBase]
    exact take_map_fq204 _ t pts
  let Q := lagrangeInterpCoeffs204 ptsBase sharesBase
  have hQLen : Q.length ≤ t := by
    have hL := lagrangeInterpLoop204_length_le ptsBase ptsBase sharesBase (fun _ h => h)
    rwa [hBaseLen] at hL
  have hQAgreeBase : ∀ x ∈ ptsBase, RoundPoly.evalCoeffs Q x = RoundPoly.evalCoeffs coeffs x := by
    intro x hx
    have hPairMem : (x, RoundPoly.evalCoeffs coeffs x) ∈ List.zip ptsBase sharesBase := by
      rw [hShBaseEq]
      exact mem_zip_map_self _ hx
    have hEvalDot := lagrangeInterpLoop204_eval_eq_dot ptsBase x ptsBase sharesBase
    have hKron := ringDot_kron_mem hBaseNd hBaseNd (fun _ h => h) hPairMem
    exact hEvalDot.trans hKron
  have hQEqAll : ∀ target : Fq204, RoundPoly.evalCoeffs Q target = RoundPoly.evalCoeffs coeffs target :=
    poly204_eq_of_agree_ge_t ht1 hQLen hDeg hBaseNd (Nat.le_of_eq hBaseLen.symm) hQAgreeBase
  have hChecksOk : ((List.zip pts shares).drop t).all (fun ps =>
      decide (Fq204.sub ps.2 (ringDot (lagrangeWeightsFq204 ptsBase ps.1) sharesBase) = Fq204.zero)) = true := by
    apply List.all_eq_true.mpr
    intro ps hps
    have hInZip : ps ∈ List.zip pts shares := List.mem_of_mem_drop hps
    have hPs2 : ps.2 = RoundPoly.evalCoeffs coeffs ps.1 := by
      dsimp only [shares] at hInZip
      have hZipMap : ∀ xs : List Fq204, ∀ p ∈ List.zip xs (xs.map (RoundPoly.evalCoeffs coeffs)),
          p.2 = RoundPoly.evalCoeffs coeffs p.1 := by
        intro xs
        induction xs with
        | nil => intro _ hp; nomatch hp
        | cons a as iha =>
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hTl
          · rfl
          · exact iha p hTl
      exact hZipMap pts ps hInZip
    apply decide_eq_true
    have hDot : ringDot (lagrangeWeightsFq204 ptsBase ps.1) sharesBase = RoundPoly.evalCoeffs Q ps.1 :=
      (lagrangeInterpLoop204_eval_eq_dot ptsBase ps.1 ptsBase sharesBase).symm
    rw [hDot, hQEqAll ps.1, hPs2, fq204_sub_self]
  let out := List.zipWith Fq204.mul (lagrangeWeightsFq204 ptsBase Fq204.zero) sharesBase
  refine ⟨out, ?_, ?_, ?_⟩
  · unfold shamirSessionKeyConvert
    have hGuard : decide (1 ≤ t ∧ t ≤ pts.length ∧ pts.length = shares.length) = true :=
      decide_eq_true ⟨ht1, htLe, hShLen⟩
    rw [hGuard]
    dsimp only
    rw [hChecksOk]
    rfl
  · dsimp only [out, lagrangeWeightsFq204, sharesBase]
    rw [List.length_zipWith, List.length_map, hBaseLen, List.length_take_of_le (by omega), Nat.min_self]
  · dsimp only [out]
    rw [sum_zipWith_mul_eq_ringDot]
    have hDot0 : ringDot (lagrangeWeightsFq204 ptsBase Fq204.zero) sharesBase =
        RoundPoly.evalCoeffs Q Fq204.zero :=
      (lagrangeInterpLoop204_eval_eq_dot ptsBase Fq204.zero ptsBase sharesBase).symm
    rw [hDot0, hQEqAll Fq204.zero]

private theorem filter_partition_length {α : Type} (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length
  | [] => rfl
  | x :: xs => by
    have ih := filter_partition_length p xs
    cases hpx : p x <;> simp [hpx] <;> omega

private theorem zip_take_eq {α β : Type} :
    ∀ (k : Nat) (xs : List α) (ys : List β),
      (List.zip xs ys).take k = List.zip (xs.take k) (ys.take k)
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, _ :: _, [] => rfl
  | k + 1, x :: xs, y :: ys => congrArg ((x, y) :: ·) (zip_take_eq k xs ys)

private theorem nodup_map_fst_of_sublist {α β : Type} (p : α × β → Bool) :
    ∀ {xs : List α} {ys : List β},
      xs.Nodup → (((List.zip xs ys).filter p).map Prod.fst).Nodup
  | [], _, _ => .nil
  | _ :: _, [], _ => .nil
  | x :: xs, y :: ys, .cons hnot hnd => by
    simp only [List.zip_cons_cons, List.filter_cons]
    cases p (x, y) with
    | false => exact nodup_map_fst_of_sublist p hnd
    | true =>
      simp only [↓reduceIte, List.map_cons]
      refine .cons ?_ (nodup_map_fst_of_sublist p hnd)
      intro z hz
      obtain ⟨pair, hMemFilt, rfl⟩ := List.mem_map.mp hz
      have hInZip := (List.mem_filter.mp hMemFilt).1
      exact hnot pair.1 (List.of_mem_zip hInZip).1

/-- **Shamir Threshold ML-DSA Byzantine Conversion Soundness (`shamirSessionKey_byzantine_sound`, `C5 #6`)**:
    For any valid `(t, n, m)` (`n ≤ 64`, `2t - 1 ≤ m ≤ 16`), distinct quorum points `pts` of size `m`,
    degree-`< t` secret polynomial `coeffs`, and submitted quorum shares `shares` with **at most `t - 1`
    corrupt shares**, if `shamirSessionKeyConvert t pts shares = some additiveShares`, then the
    converted additive shares sum to the **exact** secret `RoundPoly.evalCoeffs coeffs 0`! -/
theorem shamirSessionKey_byzantine_sound {t n m : Nat}
    (hParams : shamirMldsaParamsValid t n m = true)
    {pts coeffs shares additiveShares : List Fq204}
    (hPtsNd : pts.Nodup) (hLens : (pts.length, shares.length) = (m, m))
    (hDeg : coeffs.length ≤ t)
    (hCorruptLe :
      ((List.zip pts shares).filter
        (fun ps => decide (ps.2 ≠ RoundPoly.evalCoeffs coeffs ps.1))).length ≤ t - 1)
    (hConv : shamirSessionKeyConvert t pts shares = some additiveShares) :
    additiveShares.foldr Fq204.add Fq204.zero = RoundPoly.evalCoeffs coeffs Fq204.zero := by
  have hPtsLen : pts.length = m := (Prod.mk.injEq _ _ _ _).mp hLens |>.1
  have hShLen : shares.length = m := (Prod.mk.injEq _ _ _ _).mp hLens |>.2
  obtain ⟨ht2, _, _, _, hmLo, _⟩ := shamirMldsaParamsValid_bounds hParams
  have ht1 : 1 ≤ t := by omega
  have htLe : t ≤ pts.length := by omega
  unfold shamirSessionKeyConvert at hConv
  have hGuard : decide (1 ≤ t ∧ t ≤ pts.length ∧ pts.length = shares.length) = true :=
    decide_eq_true ⟨ht1, htLe, hPtsLen.trans hShLen.symm⟩
  rw [hGuard] at hConv
  dsimp only at hConv
  let ptsBase := pts.take t
  let sharesBase := shares.take t
  let extraPairs := (List.zip pts shares).drop t
  cases hChecks : extraPairs.all (fun ps =>
      decide (Fq204.sub ps.2 (ringDot (lagrangeWeightsFq204 ptsBase ps.1) sharesBase) = Fq204.zero)) with
  | false => rw [hChecks] at hConv; cases hConv
  | true =>
    rw [hChecks] at hConv
    simp only [↓reduceIte, Option.some.injEq] at hConv
    subst hConv
    have hBaseNd : ptsBase.Nodup := nodup_take_of_nodup t hPtsNd
    have hBaseLen : ptsBase.length = t := List.length_take_of_le htLe
    let Q := lagrangeInterpCoeffs204 ptsBase sharesBase
    have hQLen : Q.length ≤ t := by
      have hL := lagrangeInterpLoop204_length_le ptsBase ptsBase sharesBase (fun _ h => h)
      rwa [hBaseLen] at hL
    have hPairOnQ : ∀ ps ∈ List.zip pts shares, RoundPoly.evalCoeffs Q ps.1 = ps.2 := by
      intro ps hMem
      rw [← List.take_append_drop t (List.zip pts shares)] at hMem
      rcases List.mem_append.mp hMem with hInTake | hInDrop
      · rw [zip_take_eq t pts shares] at hInTake
        have hEval := lagrangeInterpLoop204_eval_eq_dot ptsBase ps.1 ptsBase sharesBase
        have hKron := ringDot_kron_mem hBaseNd hBaseNd (fun _ h => h) hInTake
        exact hEval.trans hKron
      · have hChk := of_decide_eq_true (List.all_eq_true.mp hChecks ps hInDrop)
        have hEqDot := fq204_eq_of_sub_eq_zero hChk
        have hEval := lagrangeInterpLoop204_eval_eq_dot ptsBase ps.1 ptsBase sharesBase
        exact hEval.trans hEqDot.symm
    let isBad : Fq204 × Fq204 → Bool := fun ps => decide (ps.2 ≠ RoundPoly.evalCoeffs coeffs ps.1)
    let honestPairs := (List.zip pts shares).filter (fun ps => !isBad ps)
    have hZipLen : (List.zip pts shares).length = m := by
      rw [List.length_zip, hPtsLen, hShLen, Nat.min_self]
    have hPart := filter_partition_length isBad (List.zip pts shares)
    have hHonestLen : t ≤ honestPairs.length := by
      dsimp only [honestPairs, isBad] at hPart ⊢
      omega
    let honestPts := honestPairs.map Prod.fst
    have hHonestPtsNd : honestPts.Nodup := nodup_map_fst_of_sublist (fun ps => !isBad ps) hPtsNd
    have hHonestPtsLen : t ≤ honestPts.length := by
      dsimp only [honestPts]; rwa [List.length_map]
    have hAgreeHonest : ∀ x ∈ honestPts,
        RoundPoly.evalCoeffs Q x = RoundPoly.evalCoeffs coeffs x := by
      intro x hx
      obtain ⟨ps, hpsMem, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hInZip, hNotBad⟩ := List.mem_filter.mp hpsMem
      have hGood : ps.2 = RoundPoly.evalCoeffs coeffs ps.1 := by
        dsimp only [isBad] at hNotBad
        if hEq : ps.2 = RoundPoly.evalCoeffs coeffs ps.1 then
          exact hEq
        else
          simp [hEq] at hNotBad
      exact (hPairOnQ ps hInZip).trans hGood
    have hAt0 := poly204_eq_of_agree_ge_t ht1 hQLen hDeg hHonestPtsNd hHonestPtsLen hAgreeHonest Fq204.zero
    rw [sum_zipWith_mul_eq_ringDot]
    exact (lagrangeInterpLoop204_eval_eq_dot ptsBase Fq204.zero ptsBase sharesBase).symm.trans hAt0

/-- **`#tooth` (`tooth_shamirSessionKey_corrupt_threshold_forges`)**:
    When `t` custodians are corrupt (violating `≤ t - 1`, or when `m = t` omits the `m - t`
    syndrome checks), a forged degree-`< t` share vector passes `shamirSessionKeyConvert` while
    reconstructing a forged secret `≠ RoundPoly.evalCoeffs coeffs 0`! -/
theorem tooth_shamirSessionKey_corrupt_threshold_forges :
    ∃ (pts coeffs forgedShares out : List Fq204),
      shamirMldsaParamsValid 2 64 3 = true ∧
      pts.Nodup ∧ pts.length = 3 ∧ forgedShares.length = 3 ∧ coeffs.length ≤ 2 ∧
      shamirSessionKeyConvert 2 pts forgedShares = some out ∧
      out.foldr Fq204.add Fq204.zero ≠ RoundPoly.evalCoeffs coeffs Fq204.zero := by
  let pts : List Fq204 := [Fq204.ofNat 1, Fq204.ofNat 2, Fq204.ofNat 3]
  let coeffs : List Fq204 := [Fq204.zero, Fq204.zero]
  -- Forged linear polynomial `f(X) = 3 - X` agrees with `coeffs = 0` at `X = 3` (`1` honest party,
  -- `2 = t` corrupt parties at `X = 1, 2`) and reconstructs `f(0) = 3 ≠ 0`!
  let forgedPoly : List Fq204 := [Fq204.ofNat 3, Fq204.neg Fq204.one]
  let forgedShares : List Fq204 := pts.map (RoundPoly.evalCoeffs forgedPoly)
  obtain ⟨out, hConv, _, hSum⟩ :=
    shamirSessionKey_complete (t := 2) (n := 64) (m := 3) (by decide) pts forgedPoly
      (.cons (fun x hx heq => by subst heq; revert hx; decide)
        (.cons (fun x hx heq => by subst heq; revert hx; decide)
          (.cons (fun _ h => nomatch h) .nil)))
      rfl (by decide)
  refine ⟨pts, coeffs, forgedShares, out, by decide,
    .cons (fun x hx heq => by subst heq; revert hx; decide)
      (.cons (fun x hx heq => by subst heq; revert hx; decide)
        (.cons (fun _ h => nomatch h) .nil)),
    rfl, rfl, by decide, hConv, ?_⟩
  rw [hSum]
  decide

theorem inhabited_shamirSessionKey_byzantine_sound :
    ∃ (t n m : Nat) (pts coeffs shares additiveShares : List Fq204),
      shamirMldsaParamsValid t n m = true ∧
      pts.Nodup ∧ (pts.length, shares.length) = (m, m) ∧ coeffs.length ≤ t ∧
      ((List.zip pts shares).filter
        (fun ps => decide (ps.2 ≠ RoundPoly.evalCoeffs coeffs ps.1))).length ≤ t - 1 ∧
      shamirSessionKeyConvert t pts shares = some additiveShares := by
  have hNd : ([Fq204.ofNat 1, Fq204.ofNat 2, Fq204.ofNat 3] : List Fq204).Nodup :=
    .cons (fun x hx heq => by subst heq; revert hx; decide)
      (.cons (fun x hx heq => by subst heq; revert hx; decide)
        (.cons (fun _ h => nomatch h) .nil))
  exact ⟨2, 64, 3,
    [Fq204.ofNat 1, Fq204.ofNat 2, Fq204.ofNat 3],
    [],
    [Fq204.zero, Fq204.zero, Fq204.zero],
    [Fq204.zero, Fq204.zero],
    by decide, hNd, rfl, by decide, by decide, by decide⟩

#verify_constructive
  computeVcPoseidon2CommitFull_eq_small
  computeVcPoseidon2CommitFull_arity32_binding
  mldsaNonceBurnPreimage_injective
  shamirSessionKey_complete
  shamirSessionKey_byzantine_sound

#tooth_pair computeVcPoseidon2CommitFull_arity32_binding vs tooth_computeVcPoseidon2CommitFull_rejects_arity33
#tooth_pair shamirSessionKey_byzantine_sound vs tooth_shamirSessionKey_corrupt_threshold_forges
#verify_inhabited shamirSessionKey_byzantine_sound inhabited_shamirSessionKey_byzantine_sound

/-! ## Exports for `SacrificeFreezeSample` ↔ `rssSacrificedSignStep` Bridge (`L-Ex-15`) -/

/-- All multiplication sacrifice gates in one `RssSacrificeTranscript204`. -/
def rssTranscriptAllGates204 (T : RssSacrificeTranscript204) : List SacGate204 :=
  (List.finRange 4).flatMap (fun i => T.cs1 i ++ T.cs2 i ++ T.ct0 i)

theorem ext6Zero_eq : ext6Zero =
    ⟨Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩ := by
  unfold ext6Zero; rfl

theorem ext6Sub_eq (x y : Ext6Fq204) : ext6Sub x y =
    ⟨Fq204.sub x.a0 y.a0, Fq204.sub x.a1 y.a1, Fq204.sub x.a2 y.a2,
     Fq204.sub x.a3 y.a3, Fq204.sub x.a4 y.a4, Fq204.sub x.a5 y.a5⟩ := by
  unfold ext6Sub; rfl

theorem ext6Scale_eq (x : Ext6Fq204) (s : Fq204) : ext6Scale x s =
    ⟨Fq204.mul x.a0 s, Fq204.mul x.a1 s, Fq204.mul x.a2 s,
     Fq204.mul x.a3 s, Fq204.mul x.a4 s, Fq204.mul x.a5 s⟩ := by
  unfold ext6Scale; rfl

theorem sacTripleError204_eq (g : SacGate204) :
    sacTripleError204 g = ext6Sub g.c (ext6Scale g.a g.b) := by
  unfold sacTripleError204; rfl

theorem sacAccept204_iff_tau_eq (chi : Ext6Fq204) (g : SacGate204) :
    sacAccept204 chi g = true ↔
      ext6Sub (ext6Scale chi (sacGateError204 g)) (sacTripleError204 g) = ext6Zero := by
  unfold sacAccept204 sacVerdict204
  rw [sacOpen204_tau, decide_eq_true_eq]

private theorem exists_bad_gate_of_binds_and_poly_ne
    {gs : List SacGate204} {x y z : Poly256}
    (hBinds : sacBinds204 gs x y z = true)
    (hPolyNe : z ≠ negacyclicMul x y) :
    ∃ g ∈ gs, sacGateError204 g ≠ Fq204.zero := by
  have hNotAll : ¬ (∀ g ∈ gs, sacGateError204 g = Fq204.zero) := by
    intro hAllZero
    apply hPolyNe
    have hSlots : gs.map sacGateOperands204 = nttSlots204 x y z := of_decide_eq_true hBinds
    apply fips204Ntt_injective
    rw [fips204Ntt_negacyclicMul]
    refine (pointwiseMul_of_slots204 _ _ _ ?_).symm
    intro m hm
    have hm' : m ∈ gs.map sacGateOperands204 := by rw [hSlots]; exact hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm'
    exact fq204_eq_of_sub_eq_zero (hAllZero g hg)
  have hFind : ∀ (xs : List SacGate204),
      ¬ (∀ g ∈ xs, sacGateError204 g = Fq204.zero) →
      ∃ g ∈ xs, sacGateError204 g ≠ Fq204.zero := by
    intro xs
    induction xs with
    | nil => intro h; exact False.elim (h (fun _ hm => nomatch hm))
    | cons g rest ih =>
      intro h
      if hg0 : sacGateError204 g = Fq204.zero then
        have hRest : ¬ (∀ g' ∈ rest, sacGateError204 g' = Fq204.zero) := by
          intro hAllR
          apply h
          intro g' hm
          rcases List.mem_cons.mp hm with rfl | hIn
          · exact hg0
          · exact hAllR g' hIn
        obtain ⟨g', hg'In, hg'Nz⟩ := ih hRest
        exact ⟨g', .tail _ hg'In, hg'Nz⟩
      else
        exact ⟨g, .head _, hg0⟩
  exact hFind gs hNotAll

private theorem find_diff_fin4 {p q : PolyVec4} (hNe : p ≠ q) :
    ∃ i : Fin 4, p i ≠ q i := by
  if h0 : p ⟨0, by decide⟩ = q ⟨0, by decide⟩ then
    if h1 : p ⟨1, by decide⟩ = q ⟨1, by decide⟩ then
      if h2 : p ⟨2, by decide⟩ = q ⟨2, by decide⟩ then
        if h3 : p ⟨3, by decide⟩ = q ⟨3, by decide⟩ then
          exfalso
          apply hNe
          funext ⟨idx, hidx⟩
          have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
          rcases hCases with rfl | rfl | rfl | rfl
          · exact h0
          · exact h1
          · exact h2
          · exact h3
        else exact ⟨⟨3, by decide⟩, h3⟩
      else exact ⟨⟨2, by decide⟩, h2⟩
    else exact ⟨⟨1, by decide⟩, h1⟩
  else exact ⟨⟨0, by decide⟩, h0⟩

/-- **Challenge-Independent Forged-Gate Extraction (`rssSacrificedProductsValid_forged_exists_bad_gate`, `L-Ex-15`)**:
    Whenever `inp.products ≠ rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets`,
    EITHER `rssSacrificedProductsValid` rejects **every** challenge `chi : Ext6Fq204` (`= false`),
    OR there exists a **fixed** gate `g ∈ rssTranscriptAllGates204 T` (independent of `chi`!) with
    `sacGateError204 g ≠ 0` such that every accepted challenge `chi` satisfies BOTH
    `sacAccept204 chi g = true` AND `chi = sacBadChallenge204 g`! -/
theorem rssSacrificedProductsValid_forged_exists_bad_gate
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (T : RssSacrificeTranscript204)
    (hForged : inp.products ≠ rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets) :
    (∀ chi : Ext6Fq204, rssSacrificedProductsValid chalHash sampleInBall st inp chi T = false) ∨
    ∃ g ∈ rssTranscriptAllGates204 T,
      sacGateError204 g ≠ Fq204.zero ∧
      (∀ chi : Ext6Fq204,
        rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true →
        sacAccept204 chi g = true ∧ chi = sacBadChallenge204 g) ∧
      (∀ chi : Ext6Fq204,
        rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true →
        ∀ g' ∈ rssTranscriptAllGates204 T, sacAccept204 chi g' = true) := by
  let wExp := matVecMul4 st.A (rssSumVec4List inp.ySubsets)
  let cPoly := sampleInBall (chalHash inp.mu (highBitsVec4 wExp))
  let s1 := rssSumVec4List st.s1Subsets
  let s2 := rssSumVec4List st.s2Subsets
  let t0 := power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2)
  have hAllGatesAcc : ∀ chi : Ext6Fq204,
      rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true →
      ∀ g' ∈ rssTranscriptAllGates204 T, sacAccept204 chi g' = true := by
    intro chi hVal g' hg'
    unfold rssSacrificedProductsValid at hVal
    simp only [Bool.and_eq_true] at hVal
    obtain ⟨⟨⟨_, hc1⟩, hc2⟩, hc3⟩ := hVal
    obtain ⟨i, _, hInI⟩ := List.mem_flatMap.mp hg'
    rcases List.mem_append.mp hInI with hIn12 | hIn3
    · rcases List.mem_append.mp hIn12 with hIn1 | hIn2
      · have hOk := fin4All204_true hc1 i
        unfold sacProductOk204 sacAcceptAll204 at hOk
        simp only [Bool.and_eq_true] at hOk
        exact List.all_eq_true.mp hOk.2 g' hIn1
      · have hOk := fin4All204_true hc2 i
        unfold sacProductOk204 sacAcceptAll204 at hOk
        simp only [Bool.and_eq_true] at hOk
        exact List.all_eq_true.mp hOk.2 g' hIn2
    · have hOk := fin4All204_true hc3 i
      unfold sacProductOk204 sacAcceptAll204 at hOk
      simp only [Bool.and_eq_true] at hOk
      exact List.all_eq_true.mp hOk.2 g' hIn3
  if hw : polyVec4EqBool inp.products.w wExp = true then
    if hb1 : fin4All204 (fun i => sacBinds204 (T.cs1 i) cPoly (s1 i) (inp.products.cs1 i)) = true then
      if hb2 : fin4All204 (fun i => sacBinds204 (T.cs2 i) cPoly (s2 i) (inp.products.cs2 i)) = true then
        if hb3 : fin4All204 (fun i => sacBinds204 (T.ct0 i) cPoly (t0 i) (inp.products.ct0 i)) = true then
          have hDiff : inp.products.cs1 ≠ mulPolyVec4 cPoly s1 ∨
              inp.products.cs2 ≠ mulPolyVec4 cPoly s2 ∨
              inp.products.ct0 ≠ mulPolyVec4 cPoly t0 := by
            if he1 : polyVec4EqBool inp.products.cs1 (mulPolyVec4 cPoly s1) = true then
              if he2 : polyVec4EqBool inp.products.cs2 (mulPolyVec4 cPoly s2) = true then
                if he3 : polyVec4EqBool inp.products.ct0 (mulPolyVec4 cPoly t0) = true then
                  exfalso
                  apply hForged
                  apply (rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp
                  unfold rssProductsValid
                  simp only [Bool.and_eq_true]
                  exact ⟨⟨⟨hw, he1⟩, he2⟩, he3⟩
                else
                  exact Or.inr (Or.inr (fun h => by
                    rw [(polyVec4EqBool_eq_true_iff _ _).mpr h] at he3; exact he3 rfl))
              else
                exact Or.inr (Or.inl (fun h => by
                  rw [(polyVec4EqBool_eq_true_iff _ _).mpr h] at he2; exact he2 rfl))
            else
              exact Or.inl (fun h => by
                rw [(polyVec4EqBool_eq_true_iff _ _).mpr h] at he1; exact he1 rfl)
          have hBadGate : ∃ g ∈ rssTranscriptAllGates204 T, sacGateError204 g ≠ Fq204.zero := by
            rcases hDiff with hNe1 | hNe2 | hNe3
            · obtain ⟨i, hiNe⟩ := find_diff_fin4 hNe1
              obtain ⟨g, hgIn, hgNz⟩ :=
                exists_bad_gate_of_binds_and_poly_ne (fin4All204_true hb1 i) hiNe
              exact ⟨g, List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
                List.mem_append_left _ (List.mem_append_left _ hgIn)⟩, hgNz⟩
            · obtain ⟨i, hiNe⟩ := find_diff_fin4 hNe2
              obtain ⟨g, hgIn, hgNz⟩ :=
                exists_bad_gate_of_binds_and_poly_ne (fin4All204_true hb2 i) hiNe
              exact ⟨g, List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
                List.mem_append_left _ (List.mem_append_right _ hgIn)⟩, hgNz⟩
            · obtain ⟨i, hiNe⟩ := find_diff_fin4 hNe3
              obtain ⟨g, hgIn, hgNz⟩ :=
                exists_bad_gate_of_binds_and_poly_ne (fin4All204_true hb3 i) hiNe
              exact ⟨g, List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
                List.mem_append_right _ hgIn⟩, hgNz⟩
          obtain ⟨g, hgMem, hgNz⟩ := hBadGate
          refine Or.inr ⟨g, hgMem, hgNz, ?_, hAllGatesAcc⟩
          intro chi hVal
          have hAccG := hAllGatesAcc chi hVal g hgMem
          rcases sacAccept204_sound hAccG with hMulEq | hChiBad
          · exfalso
            apply hgNz
            unfold sacGateError204
            rw [hMulEq, fq204_sub_self]
          · exact ⟨hAccG, hChiBad⟩
        else
          refine Or.inl (fun chi => ?_)
          cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
          | false => rfl
          | true =>
            exfalso; apply hb3
            unfold rssSacrificedProductsValid at hv
            simp only [Bool.and_eq_true] at hv
            apply fin4All204_of_forall; intro i
            have hOk := fin4All204_true hv.2 i
            unfold sacProductOk204 at hOk
            exact (Bool.and_eq_true _ _).mp hOk |>.1
      else
        refine Or.inl (fun chi => ?_)
        cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
        | false => rfl
        | true =>
          exfalso; apply hb2
          unfold rssSacrificedProductsValid at hv
          simp only [Bool.and_eq_true] at hv
          apply fin4All204_of_forall; intro i
          have hOk := fin4All204_true hv.1.2 i
          unfold sacProductOk204 at hOk
          exact (Bool.and_eq_true _ _).mp hOk |>.1
    else
      refine Or.inl (fun chi => ?_)
      cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
      | false => rfl
      | true =>
        exfalso; apply hb1
        unfold rssSacrificedProductsValid at hv
        simp only [Bool.and_eq_true] at hv
        apply fin4All204_of_forall; intro i
        have hOk := fin4All204_true hv.1.1.2 i
        unfold sacProductOk204 at hOk
        exact (Bool.and_eq_true _ _).mp hOk |>.1
  else
    refine Or.inl (fun chi => ?_)
    cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
    | false => rfl
    | true =>
      exfalso; apply hw
      unfold rssSacrificedProductsValid at hv
      simp only [Bool.and_eq_true] at hv
      exact hv.1.1.1

/-- Fitted gate list for an arbitrary claimed polynomial `z` when the sacrifice challenge `chi`
    is revealed before freezing the transcript (`L-Ex-15` swapped-order `#tooth` support). -/
def sacFittedGates204 (chi : Ext6Fq204) (x y z : Poly256) : List SacGate204 :=
  (nttSlots204 x y z).map (fun m =>
    { x := m.1
      y := m.2.1
      z := m.2.2
      a := ext6Zero
      b := Fq204.zero
      c := ext6Scale chi (Fq204.sub m.2.2 (Fq204.mul m.1 m.2.1)) })

private theorem map_operands_fitted204 (chi : Ext6Fq204) :
    ∀ ms : List (Fq204 × Fq204 × Fq204),
      (ms.map (fun m =>
        ({ x := m.1, y := m.2.1, z := m.2.2, a := ext6Zero, b := Fq204.zero,
           c := ext6Scale chi (Fq204.sub m.2.2 (Fq204.mul m.1 m.2.1)) } : SacGate204))).map
        sacGateOperands204 = ms
  | [] => rfl
  | m :: ms => by
    rw [List.map_cons, List.map_cons, map_operands_fitted204 chi ms]
    rfl

private theorem sacFittedGates204_ok (chi : Ext6Fq204) (x y z : Poly256) :
    sacProductOk204 chi (sacFittedGates204 chi x y z) x y z = true := by
  unfold sacProductOk204
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true (map_operands_fitted204 chi _), ?_⟩
  unfold sacAcceptAll204 sacFittedGates204
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hg
  rw [sacAccept204_iff_tau_eq, sacGateError204, sacTripleError204]
  dsimp only
  rw [ext6_sub_sub_self]
  decide

/-- Swapped-order fitted sacrifice transcript for any claimed `inp.products` when `chi` is
    sampled before freezing `T` (`L-Ex-15`). -/
def rssFittedSacrifice204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) : RssSacrificeTranscript204 :=
  let cPoly := sampleInBall (chalHash inp.mu
    (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets))))
  let s1 := rssSumVec4List st.s1Subsets
  let s2 := rssSumVec4List st.s2Subsets
  let t0 := power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2)
  { cs1 := fun i => sacFittedGates204 chi cPoly (s1 i) (inp.products.cs1 i)
    cs2 := fun i => sacFittedGates204 chi cPoly (s2 i) (inp.products.cs2 i)
    ct0 := fun i => sacFittedGates204 chi cPoly (t0 i) (inp.products.ct0 i) }

theorem rssSacrificedProductsValid_fitted_accepts
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204)
    (hw : inp.products.w = matVecMul4 st.A (rssSumVec4List inp.ySubsets)) :
    rssSacrificedProductsValid chalHash sampleInBall st inp chi
      (rssFittedSacrifice204 chalHash sampleInBall st inp chi) = true := by
  unfold rssSacrificedProductsValid rssFittedSacrifice204
  dsimp only
  simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff]
  exact ⟨⟨⟨hw,
    fin4All204_of_forall (fun i => sacFittedGates204_ok chi _ _ _)⟩,
    fin4All204_of_forall (fun i => sacFittedGates204_ok chi _ _ _)⟩,
    fin4All204_of_forall (fun i => sacFittedGates204_ok chi _ _ _)⟩

#verify_constructive
  rssSacrificedProductsValid_forged_exists_bad_gate
  rssSacrificedProductsValid_fitted_accepts

-- (end exports for lane cred-mig)

theorem rssMaskAddEquiv_toFun (target m : PolyVec4) :
    (rssMaskAddEquiv target).toFun m = addVec4 target m := by unfold rssMaskAddEquiv; rfl

theorem rssMaskAddEquiv_invFun (target m : PolyVec4) :
    (rssMaskAddEquiv target).invFun m = subVec4 m target := by unfold rssMaskAddEquiv; rfl

theorem sacGateError204_eq (g : SacGate204) :
    sacGateError204 g = Fq204.sub g.z (Fq204.mul g.x g.y) := by unfold sacGateError204; rfl

private theorem mkRssSignAttemptOutcome_nextState
    (stBurned : RssMlDsaSignerState) (usedAttempt : Nat)
    (cTilde : List UInt8) (w z u maskW maskZ maskLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8) (h : Fin 4 → HintTree 8) (accept : Bool) :
    (mkRssSignAttemptOutcome stBurned usedAttempt cTilde w z u maskW maskZ maskLow w1 h accept).nextState = stBurned := by
  cases accept <;> rfl

theorem rssSignCore_nextState
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    (rssSignCore chalHash st inp).nextState = st := by
  unfold rssSignCore
  dsimp only
  exact mkRssSignAttemptOutcome_nextState _ _ _ _ _ _ _ _ _ _ _ _

theorem rssSignCore_is_ok
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (stBurned : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    ∃ out, rssSignCore chalHash stBurned inp = .ok stBurned out := by
  unfold rssSignCore mkRssSignAttemptOutcome
  dsimp only
  split <;> exact ⟨_, rfl⟩

end Qsag

/-! ### Exports for lane mir -/

public section
namespace Qsag

theorem addVec4_apply (u v : PolyVec4) (i : Fin 4) :
    addVec4 u v i = PolyTree.add (u i) (v i) := by
  unfold addVec4
  rfl

theorem subVec4_apply (u v : PolyVec4) (i : Fin 4) :
    subVec4 u v i = PolyTree.sub (u i) (v i) := by
  unfold subVec4
  rfl

theorem HintTree.weight_leaf (b : Bool) :
    (HintTree.leaf b).weight = if b then 1 else 0 := by
  unfold HintTree.weight
  rfl

theorem HintTree.weight_branch {d : Nat} (h0 h1 : HintTree d) :
    (HintTree.branch h0 h1).weight = h0.weight + h1.weight := by
  rw [HintTree.weight]

theorem centeredDiffNormTree_leaf (r : Fq204) (w1 : Nat) :
    centeredDiffNormTree (.leaf r) (.leaf w1) =
      Fq204.centeredAbs (Fq204.sub r (Fq204.ofNat (w1 * 190464))) := by
  unfold centeredDiffNormTree
  rfl

theorem centeredDiffNormTree_branch {d : Nat} (r0 r1 : PolyTree d) (w0 w1 : NatTree d) :
    centeredDiffNormTree (.branch r0 r1) (.branch w0 w1) =
      max (centeredDiffNormTree r0 w0) (centeredDiffNormTree r1 w1) := by
  rw [centeredDiffNormTree]

theorem infNormVec4_eq (v : PolyVec4) :
    infNormVec4 v =
      max (max (PolyTree.infNorm (v ⟨0, by decide⟩)) (PolyTree.infNorm (v ⟨1, by decide⟩)))
          (max (PolyTree.infNorm (v ⟨2, by decide⟩)) (PolyTree.infNorm (v ⟨3, by decide⟩))) := by
  unfold infNormVec4
  rfl

theorem hintWeightVec4_eq (h : Fin 4 → HintTree 8) :
    hintWeightVec4 h =
      HintTree.weight (h ⟨0, by decide⟩) + HintTree.weight (h ⟨1, by decide⟩) +
      HintTree.weight (h ⟨2, by decide⟩) + HintTree.weight (h ⟨3, by decide⟩) := by
  unfold hintWeightVec4
  rfl

theorem centeredDiffNormVec4_eq (r : PolyVec4) (w1 : Fin 4 → NatTree 8) :
    centeredDiffNormVec4 r w1 =
      max (max (centeredDiffNormTree (r ⟨0, by decide⟩) (w1 ⟨0, by decide⟩))
               (centeredDiffNormTree (r ⟨1, by decide⟩) (w1 ⟨1, by decide⟩)))
          (max (centeredDiffNormTree (r ⟨2, by decide⟩) (w1 ⟨2, by decide⟩))
               (centeredDiffNormTree (r ⟨3, by decide⟩) (w1 ⟨3, by decide⟩))) := by
  unfold centeredDiffNormVec4
  rfl

/-! ### Exports and executed controls for `Tests/CredentialsTeeth`

The bodies these controls execute are sealed outside this module. -/

/-- The all-`false` hint vector, as decoded from an empty hint encoding. -/
def mldsaZeroHints204 : Fin 4 → HintTree 8 := fun _ => hintTree204 8 []

/-- With the challenge hash that returns its message representative, the zero key and the zero
    response, the algebraic core accepts every `μ` presented as its own challenge bytes. -/
theorem mldsaVerify_echo_zero_accepts (mu : List UInt8) :
    mldsaVerify (fun m _ => m) (fun _ => PolyTree.zero 8) (fun _ _ => PolyTree.zero 8)
      (fun _ => PolyTree.zero 8) mu mu (fun _ => PolyTree.zero 8) mldsaZeroHints204 = true := by
  have h1 : infNormVec4 (fun _ => PolyTree.zero 8) < mldsa44Gamma1 - mldsa44Beta := by
    decide +kernel
  have h2 : hintWeightVec4 mldsaZeroHints204 ≤ mldsa44Omega := by decide +kernel
  unfold mldsaVerify
  simp only [decide_eq_true h1, decide_eq_true h2, decide_true, Bool.and_self]

theorem vcSmallMaxAttrs_eq : vcSmallMaxAttrs = 6 := by rfl

/-- A valid witness needs strictly ascending, in-range disclosed indices. -/
theorem BlindVcWitnessValid.strictAsc {stmt : BlindVcPublicStatement}
    {wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth}
    (h : BlindVcWitnessValid stmt wit) :
    vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true := h.1

/-- The third role of group `(0, 1)` is not the fixed third holder: roles rotate. (Audited in
    `Tests/CredentialsTeeth`; proved here, where both bodies are visible.) -/
theorem toprfRotation204_not_constant :
    (toprfGroupRoles204 0 1).2.2 ≠ (toprfHolders 0 1).getD 2 0 := by decide

#export_eqns Vec.replicate vcCommitPartyView ext6EmbedFq ext6Add

#verify_constructive mldsaVerify_echo_zero_accepts vcSmallMaxAttrs_eq
  BlindVcWitnessValid.strictAsc toprfRotation204_not_constant

end Qsag
