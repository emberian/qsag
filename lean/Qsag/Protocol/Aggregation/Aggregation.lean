module
/-
# Succinct Post-Quantum Signature Aggregation over `GoldilocksExt4` Multi-Stage WHIR

Formalization of `K`-to-`1` succinct post-quantum signature aggregation and disjoint `2`-to-`1`
merge trees over the quartic Goldilocks extension field `Aggregation.GoldilocksExt4`
(`p = 2^64 - 2^32 + 1`, `p^4 > 2^255`):

1. **Bitmap Conservation & `Digest5` Full-256-Bit Injection (§1–§2):**
   Exact popcount conservation across disjoint validator bitmaps (`popcount_union_disjoint_eq_add`),
   `#tooth` overlapping-signer rejection, and lossless `4 × 56 + 32 = 256`-bit `Digest5` packing.
2. **Quartic Extension Field `Aggregation.GoldilocksExt4` (§4):**
   Complete `CommRingOps`, `LawfulCommRing`, `uBasis_not_square`, `norm_ne_zero`, constructive
   inversion `inv` (`mul_inv_cancel`), `NoZeroDivisors`, 32-byte canonical injective codec
   (`encodeBytes32_injective`, `decodeBytes32_encodeBytes32`), coset duet folding (`foldDuetExt4`),
   and Lagrange / Factor-Theorem root bounds (`ext4_poly_roots_le_degree`,
   `sumcheck_degree8_ext4_roots_le_eight`, `whir_coset_duet_ext4_roots_le_one`,
   `whir_ood_pin_roots_le_degree`).
3. **2-Regime Unconditional `[BCIKS20]` Johnson WHIR Schedule Ladder (§5):**
   Exact `(4, 16, 64, 256)` rate-escalating schedules matching `crates/qsag-agg/src/pcs.rs` across
   both unconditional `WhirSecurityRegime` profiles (`bciksJohnsonClassical128` wire tag `2` and
   default `bciksJohnsonQrom128` wire tag `4`, with retired capacity-proximity wire tags `0, 1, 3`
   rejected), proving positive Johnson proximity slack (`+1` query at classical-128 -> `eta = 1/512`,
   `+2` queries at QROM-128 -> `eta = 1/1024`, with explicit finite `[BCIKS20]` list bounds
   `L <= 256` and `L <= 512`) and `ProductionAggParams`.
4. **Succinct Multi-Stage WHIR + OOD + PoW + Degree-8 Sumcheck Verifier (§6–§8):**
   Instance-bound Fiat–Shamir transcript, degree-8 row sumcheck over `GoldilocksExt4`, multi-stage
   WHIR verifier (`verifySuccinctAggregate`, `verifyAggregatedSignature`, `MergeNode`,
   `verifyMergeTree` — zero plaintext `List PqHashSig` openings), per-stage OOD list-pinning,
   degree-2 shift/OOD sumcheck, 16-bit `cSHAKE256` Proof-of-Work (`verifyWhirStagePow`, the deployed
   `"QSAG.PCS.POW2/v1"` function over a 32-byte digest and little-endian nonce), distinct
   sorted fiber openings (`strictlyIncreasing`), constructive `0 Classical.choice` `PSum` knowledge
   soundness (`succinct_aggregation_knowledge_soundness`, `succinct_merge_tree_knowledge_soundness`),
   and end-to-end unforgeability reduction (`qsag_aggregate_unforgeability_reduction`) into
   `extractReachableHypertreeForgery`, whose upper-layer oracle premise ranges only over
   `ReachableUpperHypertreePos`, together with the premise-free signing-log instantiations
   `qsag_aggregate_unforgeability_reduction_of_statelessLog` and
   `qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog`.
5. **Transcript-Bound Challenge & Query Soundness Counting (§9–§10):**
   Adaptive `challengeVectors` union bounds and `aggDistinctTuples` falling-factorial query bounds over
   concrete `Nodup` `List Aggregation.GoldilocksExt4` domains across both unconditional
   `WhirSecurityRegime`s.
6. **Genuine Reed–Solomon + Degree-7 S-Box Trace-Decoding `RowArithmetization.Lawful` (§11–§12):**
   Concrete blowup-4 -> blowup-16 2-stage WHIR arithmetization (`rsSbox7TraceArith_lawful`) where
   `isStageCodeword 0` checks real base-field Reed–Solomon evaluation constraints on 8th roots of
   unity (`#tooth` `tooth_corrupted_round0_symbol_rejected`), `decodeSigs` extracts `List PqHashSig`
   directly from the committed trace polynomial (`decodeSbox7Sigs_nonconstant`), and an explicit
   end-to-end 2-stage WHIR proof passes `verifySuccinctAggregate` and `verifyMergeTree`.
7. **Full multi-round algebraic traces and succinct composition (§14):**
   `checkSbox7Trace_sound` checks every RS-encoded transition and inter-round link.
   `sbox7WhirChain_sound` composes accepted instance-bound proofs through the actual extractor,
   yielding the iterated output or an identified round break; nine-round soundness and
   constructive arbitrary-round completeness are included. The deployed StepOp AIR is separate.
-/

public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HypertreeEufCma

public import Qsag.Tactic.AssuranceKit

public import Qsag.Math.QuarticExt4

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. `SignerBitmap` Disjointness & Exact Stake-Popcount Conservation -/

/-- Boolean participation vector across a committee of `N` validators (`Simulates` `BitVec N`). -/
abbrev SignerBitmapSpec := List Bool

def bitmapDisjointSpec : SignerBitmapSpec → SignerBitmapSpec → Bool
  | [], _ => true
  | _, [] => true
  | a :: as, b :: bs => (!(a && b)) && bitmapDisjointSpec as bs

def bitmapUnionSpec : SignerBitmapSpec → SignerBitmapSpec → SignerBitmapSpec
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a || b) :: bitmapUnionSpec as bs

def bitmapPopcountSpec : SignerBitmapSpec → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + bitmapPopcountSpec bs

/-- **Exact Stake Conservation Under Disjoint Union (`popcount_union_disjoint_eq_add`)**:
    Whenever `bitmapDisjointSpec b1 b2 = true` and `b1.length = b2.length`, the union bitmap has
    popcount **strictly equal** to `popcount b1 + popcount b2`. -/
theorem popcount_union_disjoint_eq_add :
    ∀ (b1 b2 : SignerBitmapSpec),
      b1.length = b2.length →
      bitmapDisjointSpec b1 b2 = true →
      bitmapPopcountSpec (bitmapUnionSpec b1 b2) =
        bitmapPopcountSpec b1 + bitmapPopcountSpec b2
  | [], [], _, _ => rfl
  | _ :: _, [], hLen, _ => by cases hLen
  | [], _ :: _, hLen, _ => by cases hLen
  | a :: as, b :: bs, hLen, hDisj => by
    simp only [bitmapDisjointSpec, Bool.and_eq_true] at hDisj
    have ih := popcount_union_disjoint_eq_add as bs (Nat.succ.inj hLen) hDisj.2
    simp only [bitmapUnionSpec, bitmapPopcountSpec, ih]
    cases a <;> cases b <;> simp at hDisj ⊢ <;> omega

/-- **`#tooth` Overlapping Signer Rejection (`overlapping_merge_rejected`)**:
    If validator index `idx` is active in BOTH `b1` and `b2`, `bitmapDisjointSpec b1 b2 = false`,
    blocking 2-to-1 merge verification from double-counting validator weight. -/
theorem overlapping_merge_rejected :
    ∀ (b1 b2 : SignerBitmapSpec) (idx : Nat),
      idx < b1.length → idx < b2.length →
      b1.getD idx false = true →
      b2.getD idx false = true →
      bitmapDisjointSpec b1 b2 = false
  | [], _, _, h1, _, _, _ => by simp at h1
  | _, [], _, _, h2, _, _ => by simp at h2
  | a :: _, b :: _, 0, _, _, ha, hb => by
    simp only [List.getD_cons_zero] at ha hb
    simp [bitmapDisjointSpec, ha, hb]
  | a :: as, b :: bs, idx + 1, h1, h2, ha, hb => by
    simp only [List.getD_cons_succ] at ha hb
    have ih := overlapping_merge_rejected as bs idx
      (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2) ha hb
    simp [bitmapDisjointSpec, ih]

/-- Packed `BitVec n` execution carrier matching `SignerBitmap` in `crates/qsag-agg/src/lib.rs`. -/
@[expose] def checkDisjointBitmaps {n : Nat} (b1 b2 : BitVec n) : Bool :=
  (b1 &&& b2) == 0#n

theorem checkDisjointBitmaps_false_of_shared_bit {n : Nat} (b1 b2 : BitVec n)
    (i : Nat) (_hi : i < n)
    (h1 : b1.getLsbD i = true) (h2 : b2.getLsbD i = true) :
    checkDisjointBitmaps b1 b2 = false := by
  unfold checkDisjointBitmaps
  cases hEq : ((b1 &&& b2) == 0#n)
  · rfl
  · exfalso
    have hZ : (b1 &&& b2) = 0#n := eq_of_beq hEq
    have hBit := congrArg (fun v : BitVec n => v.getLsbD i) hZ
    simp only [BitVec.getLsbD_and, h1, h2, Bool.and_self, BitVec.getLsbD_zero] at hBit
    cases hBit

/-! ## 2. Full-256-Bit 5-Limb `Digest5` Injection (`[P1-01]`) -/

/-- Lossless 256-bit digest carrier over `Goldilocks` (`4 × 56 + 32 = 256` bits, `[P1-01]`):
    matches `Digest5` in `crates/qsag-agg/src/trace.rs` where every limb `< 2^56 < p`. -/
structure Digest5 where
  limb0 : Goldilocks
  limb1 : Goldilocks
  limb2 : Goldilocks
  limb3 : Goldilocks
  limb4 : Goldilocks
  deriving DecidableEq, Repr

theorem lt_goldilocks_of_lt_pow56 {v : Nat} (h : v < 2 ^ 56) : v < goldilocksPrime := by
  have hBound : (2 : Nat) ^ 56 < goldilocksPrime := by decide
  exact Nat.lt_trans h hBound

theorem lt_goldilocks_of_lt_pow32 {v : Nat} (h : v < 2 ^ 32) : v < goldilocksPrime := by
  have hBound : (2 : Nat) ^ 32 < goldilocksPrime := by decide
  exact Nat.lt_trans h hBound

/-- Pack a full 256-bit `BitVec 256` into `Digest5` with zero truncation. -/
@[expose] def digest5FromBitVec256 (d : BitVec 256) : Digest5 :=
  let l0 := (d.extractLsb' 0 56).toNat
  let l1 := (d.extractLsb' 56 56).toNat
  let l2 := (d.extractLsb' 112 56).toNat
  let l3 := (d.extractLsb' 168 56).toNat
  let l4 := (d.extractLsb' 224 32).toNat
  { limb0 := ⟨l0, lt_goldilocks_of_lt_pow56 (BitVec.isLt _)⟩
    limb1 := ⟨l1, lt_goldilocks_of_lt_pow56 (BitVec.isLt _)⟩
    limb2 := ⟨l2, lt_goldilocks_of_lt_pow56 (BitVec.isLt _)⟩
    limb3 := ⟨l3, lt_goldilocks_of_lt_pow56 (BitVec.isLt _)⟩
    limb4 := ⟨l4, lt_goldilocks_of_lt_pow32 (BitVec.isLt _)⟩ }

/-- **Full-256-Bit `Digest5` Injectivity (`digest5FromBitVec256_injective`, `[P1-01]`)**:
    Distinct 256-bit roots or message digests NEVER collide in `Digest5`. -/
theorem digest5FromBitVec256_injective {d1 d2 : BitVec 256}
    (h : digest5FromBitVec256 d1 = digest5FromBitVec256 d2) : d1 = d2 := by
  have h0 : (d1.extractLsb' 0 56).toNat = (d2.extractLsb' 0 56).toNat := congrArg (fun x => x.limb0.val) h
  have h1 : (d1.extractLsb' 56 56).toNat = (d2.extractLsb' 56 56).toNat := congrArg (fun x => x.limb1.val) h
  have h2 : (d1.extractLsb' 112 56).toNat = (d2.extractLsb' 112 56).toNat := congrArg (fun x => x.limb2.val) h
  have h3 : (d1.extractLsb' 168 56).toNat = (d2.extractLsb' 168 56).toNat := congrArg (fun x => x.limb3.val) h
  have h4 : (d1.extractLsb' 224 32).toNat = (d2.extractLsb' 224 32).toNat := congrArg (fun x => x.limb4.val) h
  have b0 := BitVec.eq_of_toNat_eq h0
  have b1 := BitVec.eq_of_toNat_eq h1
  have b2 := BitVec.eq_of_toNat_eq h2
  have b3 := BitVec.eq_of_toNat_eq h3
  have b4 := BitVec.eq_of_toNat_eq h4
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  if c0 : i < 56 then
    have e := congrArg (fun v => v.getLsbD i) b0
    simpa [BitVec.getLsbD_extractLsb', c0] using e
  else if c1 : i < 112 then
    have e := congrArg (fun v => v.getLsbD (i - 56)) b1
    have hSub : i - 56 < 56 := by omega
    have hAdd : 56 + (i - 56) = i := by omega
    simpa [BitVec.getLsbD_extractLsb', hSub, hAdd] using e
  else if c2 : i < 168 then
    have e := congrArg (fun v => v.getLsbD (i - 112)) b2
    have hSub : i - 112 < 56 := by omega
    have hAdd : 112 + (i - 112) = i := by omega
    simpa [BitVec.getLsbD_extractLsb', hSub, hAdd] using e
  else if c3 : i < 224 then
    have e := congrArg (fun v => v.getLsbD (i - 168)) b3
    have hSub : i - 168 < 56 := by omega
    have hAdd : 168 + (i - 168) = i := by omega
    simpa [BitVec.getLsbD_extractLsb', hSub, hAdd] using e
  else
    have e := congrArg (fun v => v.getLsbD (i - 224)) b4
    have hSub : i - 224 < 32 := by omega
    have hAdd : 224 + (i - 224) = i := by omega
    simpa [BitVec.getLsbD_extractLsb', hSub, hAdd] using e

/-! ## 3. Multilinear Quartet Folding Helper & Commitment-Before-Challenge `#tooth` -/

/-- Exact 2-step multilinear quartet folding operator over `GoldilocksExt2` retained for KAT vector
    conformance (`KatGen.lean`):
    `fold4(q0, q1, q2, q3; ra, rb) = (q0 + ra*(q1 - q0)) + rb*((q2 + ra*(q3 - q2)) - (q0 + ra*(q1 - q0)))`. -/
@[expose] def basefoldQuartet (q0 q1 q2 q3 ra rb : GoldilocksExt2) : GoldilocksExt2 :=
  let lo := CommRingOps.add q0 (CommRingOps.mul ra (CommRingOps.sub q1 q0))
  let hi := CommRingOps.add q2 (CommRingOps.mul ra (CommRingOps.sub q3 q2))
  CommRingOps.add lo (CommRingOps.mul rb (CommRingOps.sub hi lo))

/-- **`#tooth` Pre-Challenge Forgery Attack (`prechallenge_fold_forgery_attack`, `[P0-01]`)**:
    Squeezing folding challenges `(ra, rb)` (`ra ≠ 0, rb ≠ 0`) before committing `(q0, q1, q2, q3)`
    lets a malicious prover solve for `q3Star` hitting ANY target `vStar` identically. -/
theorem prechallenge_fold_forgery_attack
    (q0 q1 q2 vStar ra rb : GoldilocksExt2)
    (hra : ra ≠ GoldilocksExt2.zero) (hrb : rb ≠ GoldilocksExt2.zero) :
    let lo := CommRingOps.add q0 (CommRingOps.mul ra (CommRingOps.sub q1 q0))
    let targetHi := CommRingOps.add lo (CommRingOps.mul (GoldilocksExt2.inv rb) (CommRingOps.sub vStar lo))
    let q3Star := CommRingOps.add q2 (CommRingOps.mul (GoldilocksExt2.inv ra) (CommRingOps.sub targetHi q2))
    basefoldQuartet q0 q1 q2 q3Star ra rb = vStar := by
  intro lo targetHi q3Star
  have hSubAdd : ∀ (a b : GoldilocksExt2),
      CommRingOps.sub (CommRingOps.add a b) a = b := fun a b => by
    rw [LawfulCommRing.add_comm a b, LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  have hAddSub : ∀ (a b : GoldilocksExt2),
      CommRingOps.add a (CommRingOps.sub b a) = b := fun a b =>
    LawfulCommRing.add_sub_cancel_left a b
  have hHi : CommRingOps.add q2 (CommRingOps.mul ra (CommRingOps.sub q3Star q2)) = targetHi := by
    dsimp only [q3Star]
    rw [hSubAdd, ← LawfulCommRing.mul_assoc, GoldilocksExt2.mul_inv_cancel hra,
        LawfulCommRing.one_mul, hAddSub]
  unfold basefoldQuartet
  change CommRingOps.add lo (CommRingOps.mul rb
    (CommRingOps.sub (CommRingOps.add q2 (CommRingOps.mul ra (CommRingOps.sub q3Star q2))) lo)) = vStar
  rw [hHi]
  dsimp only [targetHi]
  rw [hSubAdd, ← LawfulCommRing.mul_assoc, GoldilocksExt2.mul_inv_cancel hrb,
      LawfulCommRing.one_mul, hAddSub]

/-! ## 4. Quartic Extension Field `Aggregation.GoldilocksExt4` (`p^4 > 2^255`) -/

namespace Aggregation

/-! Quartic extension $\mathbb{F}_{p^4} = \mathbb{F}_{p^2}[v] / (v^2 - u)$ where
    $u = \texttt{GoldilocksExt2.uBasis}$ ($u^2 = 7$), matching `GoldilocksExt4` in
    `crates/qsag-agg/src/field.rs` (`|\mathbb{F}_{p^4}| = p^4 > 2^{255}`). -/
/-- Quartic challenge field multiplicative inverse law (`z ≠ 0 → z * z⁻¹ = 1`). -/
theorem goldilocksExt4_mul_inv_cancel {z : GoldilocksExt4} (hz : z ≠ GoldilocksExt4.zero) :
    CommRingOps.mul z (GoldilocksExt4.inv z) = CommRingOps.one :=
  GoldilocksExt4.mul_inv_cancel hz

/-- Canonical 32-byte `GoldilocksExt4` byte-framing injectivity. -/
theorem goldilocksExt4_encodeBytes32_injective {x y : GoldilocksExt4}
    (h : GoldilocksExt4.encodeBytes32 x = GoldilocksExt4.encodeBytes32 y) : x = y :=
  GoldilocksExt4.encodeBytes32_injective h

/-- Quartic challenge field cardinality lower bound: `|F_{p^4}| = p^4 > 2^255`. -/
theorem goldilocksExt4_card_gt_two_pow_255 : 2 ^ 255 < goldilocksPrime ^ 4 := by decide

/-- Quartic challenge field cardinality upper bound: `|F_{p^4}| = p^4 < 2^256`. -/
theorem goldilocksExt4_card_lt_two_pow_256 : goldilocksPrime ^ 4 < 2 ^ 256 := by decide

/-- **Schwartz–Zippel Root Bound over `GoldilocksExt4` (`ext4_poly_roots_le_degree`)**:
    Any two distinct polynomials of degree at most `maxDegree` over `GoldilocksExt4` agree at
    at most `maxDegree` points in any duplicate-free list `S`. -/
theorem ext4_poly_roots_le_degree (maxDegree : Nat)
    (claimedPoly honestPoly : List GoldilocksExt4) (S : List GoldilocksExt4)
    (hNodup : S.Nodup)
    (hLenC : claimedPoly.length ≤ maxDegree + 1) (hLenH : honestPoly.length ≤ maxDegree + 1)
    (hDiff : ∃ x₀ : GoldilocksExt4,
      RoundPoly.evalCoeffs claimedPoly x₀ ≠ RoundPoly.evalCoeffs honestPoly x₀) :
    (S.filter (fun r =>
      decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r))).length ≤
      maxDegree := by
  let diff := RoundPoly.subCoeffs claimedPoly honestPoly
  have hDiffLen : diff.length ≤ maxDegree + 1 := by
    dsimp only [diff]
    rw [RoundPoly.subCoeffs_length]
    exact Nat.max_le.mpr ⟨hLenC, hLenH⟩
  obtain ⟨x₀, hx₀⟩ := hDiff
  have hNz : ∃ x : GoldilocksExt4, RoundPoly.evalCoeffs diff x ≠ GoldilocksExt4.zero := by
    refine ⟨x₀, ?_⟩
    rw [RoundPoly.evalCoeffs_sub]
    exact fun hZ => hx₀ (LawfulCommRing.sub_eq_zero_iff.mp hZ)
  have hBound := RoundPoly.roots_nodup_length_le maxDegree diff S hNodup hDiffLen hNz
  have hFiltEq : S.filter (fun r =>
      decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r)) =
      S.filter (fun r => decide (RoundPoly.evalCoeffs diff r = GoldilocksExt4.zero)) := by
    congr 1
    funext r
    dsimp only [diff]
    rw [RoundPoly.evalCoeffs_sub]
    by_cases hEq : RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r
    · have hZ : CommRingOps.sub (RoundPoly.evalCoeffs honestPoly r)
          (RoundPoly.evalCoeffs honestPoly r) = GoldilocksExt4.zero :=
        LawfulCommRing.sub_self _
      simp only [hEq, hZ, decide_true]
    · have hNzR : CommRingOps.sub (RoundPoly.evalCoeffs claimedPoly r)
          (RoundPoly.evalCoeffs honestPoly r) ≠ GoldilocksExt4.zero :=
        fun hZ => hEq (LawfulCommRing.sub_eq_zero_iff.mp hZ)
      simp [hEq, hNzR]
  rw [hFiltEq]
  exact hBound

theorem sumcheck_degree8_ext4_roots_le_eight
    (claimedPoly honestPoly : List GoldilocksExt4) (S : List GoldilocksExt4)
    (hNodup : S.Nodup)
    (hLenC : claimedPoly.length ≤ 9) (hLenH : honestPoly.length ≤ 9)
    (hDiff : ∃ x₀ : GoldilocksExt4,
      RoundPoly.evalCoeffs claimedPoly x₀ ≠ RoundPoly.evalCoeffs honestPoly x₀) :
    (S.filter (fun r =>
      decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r))).length ≤ 8 := by
  exact ext4_poly_roots_le_degree 8 claimedPoly honestPoly S hNodup hLenC hLenH hDiff

/-- **WHIR Out-of-Domain (OOD) List-Pinning Bound (`whir_ood_pin_roots_le_degree`)**:
    Any two distinct list-decoded candidate polynomials `candA, candB` of univariate degree `≤ d`
    collide at at most `d` OOD challenges `z_ood ∈ S` (`d / p^4 < d / 2^255`). -/
theorem whir_ood_pin_roots_le_degree (d : Nat)
    (candA candB : List GoldilocksExt4) (S : List GoldilocksExt4)
    (hNodup : S.Nodup)
    (hLenA : candA.length ≤ d + 1) (hLenB : candB.length ≤ d + 1)
    (hDiff : ∃ z₀ : GoldilocksExt4,
      RoundPoly.evalCoeffs candA z₀ ≠ RoundPoly.evalCoeffs candB z₀) :
    (S.filter (fun z =>
      decide (RoundPoly.evalCoeffs candA z = RoundPoly.evalCoeffs candB z))).length ≤ d := by
  exact ext4_poly_roots_le_degree d candA candB S hNodup hLenA hLenB hDiff

/-- Quartic WHIR coset duet folding operator over `GoldilocksExt4` with base-field inverse twiddles
    `invTwo = 2^-1` and `invTwoY0 = (2 * y_0)^-1` (`pcs.rs`). -/
def foldDuetExt4 (v0 v1 : GoldilocksExt4) (invTwoY0 invTwo : Goldilocks)
    (r : GoldilocksExt4) : GoldilocksExt4 :=
  let even := CommRingOps.mul (CommRingOps.add v0 v1) (GoldilocksExt4.embedBase invTwo)
  let odd := CommRingOps.mul (CommRingOps.sub v0 v1) (GoldilocksExt4.embedBase invTwoY0)
  CommRingOps.add even (CommRingOps.mul r odd)

/-- Committed `GoldilocksExt4` coset duet soundness: at most `1` challenge `r ∈ S` hits a cheated
    next-layer value (`1 / p^4 < 2^-255`). -/
theorem whir_coset_duet_ext4_roots_le_one
    (v0 v1 next : GoldilocksExt4) (invTwoY0 invTwo : Goldilocks)
    (S : List GoldilocksExt4) (hS : S.Nodup)
    (hne : ∃ r, foldDuetExt4 v0 v1 invTwoY0 invTwo r ≠ next) :
    (S.filter (fun r => decide (foldDuetExt4 v0 v1 invTwoY0 invTwo r = next))).length ≤ 1 := by
  let even := CommRingOps.mul (CommRingOps.add v0 v1) (GoldilocksExt4.embedBase invTwo)
  let odd := CommRingOps.mul (CommRingOps.sub v0 v1) (GoldilocksExt4.embedBase invTwoY0)
  have he : ∀ r, RoundPoly.evalCoeffs [even, odd] r = foldDuetExt4 v0 v1 invTwoY0 invTwo r := by
    intro r
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rfl
  have hc : ∀ r, RoundPoly.evalCoeffs [next] r = next := by
    intro r
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  have hd : ∃ r, RoundPoly.evalCoeffs [even, odd] r ≠ RoundPoly.evalCoeffs [next] r := by
    simpa only [he, hc] using hne
  have bound := ext4_poly_roots_le_degree 1 [even, odd] [next] S hS
    (by simp) (by simp) hd
  simpa only [he, hc] using bound

/-- **`#tooth` Coset Twiddle Sensitivity (`coset_twiddle_ext4_omission_detected`)**:
    Altering or omitting the inverse coset twiddle `invTwoY0` changes `foldDuetExt4`. -/
theorem coset_twiddle_ext4_omission_detected :
    foldDuetExt4 GoldilocksExt4.one GoldilocksExt4.zero
      (Goldilocks.ofNat 2) (Goldilocks.ofNat 3) GoldilocksExt4.one ≠
    foldDuetExt4 GoldilocksExt4.one GoldilocksExt4.zero
      (Goldilocks.ofNat 1) (Goldilocks.ofNat 3) GoldilocksExt4.one := by
  decide +kernel

/-- **`#tooth` Mandatory Terminal Sumcheck Evaluation Check (`terminal_check_ext4_omission_unsound`)**:
    Omitting the terminal check `finalSumcheckClaim = pcsOpenedEval` lets a constant polynomial
    `[halfClaim]` pass `s(0) + s(1) = forgedClaim` with zero connection to the committed trace. -/
theorem terminal_check_ext4_omission_unsound (halfClaim : GoldilocksExt4) :
    let forgedClaim := CommRingOps.add halfClaim halfClaim
    let fakePoly : List GoldilocksExt4 := [halfClaim]
    CommRingOps.add (RoundPoly.evalCoeffs fakePoly GoldilocksExt4.zero)
                    (RoundPoly.evalCoeffs fakePoly GoldilocksExt4.one) = forgedClaim := by
  simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-! ## 5. Unconditional `[BCIKS20]` Johnson WHIR Schedule Ladder -/

/-- `pcs.rs:WhirSecurityRegime`: the six wire-decodable query-accounting regimes
    (`#[repr(u8)]` tags `2, 4, 5, 6, 7, 8`; retired capacity tags `0, 1, 3` are rejected).
    - `bciksJohnsonClassical128` (tag `2`): `q = (129, 65, 44, 33)`, 16-bit PoW.
    - `bciksJohnsonQrom128` (tag `4`, default): `q = (258, 130, 88, 66)`, 16-bit PoW.
    - `cdhz25JohnsonQrom128` (tag `5`): `q = (202, 102, 70, 52)`, 16-bit PoW, `cSHAKE256`.
    - `cdhz25ZeroPowQrom128` (tag `6`): `q = (216, 109, 74, 56)`, no PoW, `cSHAKE256`.
    - `poseidon2Cdhz25JohnsonQrom128` (tag `7`): the tag-5 table over the Poseidon2 canopy.
    - `poseidon2Cdhz25ZeroPowQrom128` (tag `8`): the tag-6 table over the Poseidon2 canopy.
    Only tag `4` has 128 nominal Grover round bits; see `WhirSecurityRegime.qromGroverRoundBits`. -/
inductive WhirSecurityRegime where
  | bciksJohnsonClassical128
  | bciksJohnsonQrom128
  | cdhz25JohnsonQrom128
  | cdhz25ZeroPowQrom128
  | poseidon2Cdhz25JohnsonQrom128
  | poseidon2Cdhz25ZeroPowQrom128
  deriving DecidableEq, Repr

def WhirSecurityRegime.defaultRegime : WhirSecurityRegime := .bciksJohnsonQrom128

/-- `WhirSecurityRegime::ALL`. -/
def WhirSecurityRegime.all : List WhirSecurityRegime :=
  [.bciksJohnsonClassical128, .bciksJohnsonQrom128, .cdhz25JohnsonQrom128,
   .cdhz25ZeroPowQrom128, .poseidon2Cdhz25JohnsonQrom128, .poseidon2Cdhz25ZeroPowQrom128]

theorem WhirSecurityRegime.mem_all (r : WhirSecurityRegime) : r ∈ WhirSecurityRegime.all := by
  cases r <;> decide

def WhirSecurityRegime.tagByte : WhirSecurityRegime → UInt8
  | .bciksJohnsonClassical128 => 2
  | .bciksJohnsonQrom128 => 4
  | .cdhz25JohnsonQrom128 => 5
  | .cdhz25ZeroPowQrom128 => 6
  | .poseidon2Cdhz25JohnsonQrom128 => 7
  | .poseidon2Cdhz25ZeroPowQrom128 => 8

/-- `WhirSecurityRegime::from_u8`: accepts exactly the wire tags `2, 4, 5, 6, 7, 8`. -/
def WhirSecurityRegime.decodeTag? (tag : UInt8) : Option WhirSecurityRegime :=
  if tag = 2 then some .bciksJohnsonClassical128
  else if tag = 4 then some .bciksJohnsonQrom128
  else if tag = 5 then some .cdhz25JohnsonQrom128
  else if tag = 6 then some .cdhz25ZeroPowQrom128
  else if tag = 7 then some .poseidon2Cdhz25JohnsonQrom128
  else if tag = 8 then some .poseidon2Cdhz25ZeroPowQrom128
  else none

theorem WhirSecurityRegime.decodeTag?_tagByte (r : WhirSecurityRegime) :
    WhirSecurityRegime.decodeTag? r.tagByte = some r := by
  cases r <;> rfl

theorem WhirSecurityRegime.tagByte_of_decodeTag? {tag : UInt8} {r : WhirSecurityRegime}
    (h : WhirSecurityRegime.decodeTag? tag = some r) :
    r.tagByte = tag := by
  unfold WhirSecurityRegime.decodeTag? at h
  by_cases h2 : tag = 2
  · rw [ite_eq_left h2] at h; cases h; exact h2.symm
  rw [ite_eq_right h2] at h
  by_cases h4 : tag = 4
  · rw [ite_eq_left h4] at h; cases h; exact h4.symm
  rw [ite_eq_right h4] at h
  by_cases h5 : tag = 5
  · rw [ite_eq_left h5] at h; cases h; exact h5.symm
  rw [ite_eq_right h5] at h
  by_cases h6 : tag = 6
  · rw [ite_eq_left h6] at h; cases h; exact h6.symm
  rw [ite_eq_right h6] at h
  by_cases h7 : tag = 7
  · rw [ite_eq_left h7] at h; cases h; exact h7.symm
  rw [ite_eq_right h7] at h
  by_cases h8 : tag = 8
  · rw [ite_eq_left h8] at h; cases h; exact h8.symm
  rw [ite_eq_right h8] at h
  cases h

theorem WhirSecurityRegime.tagByte_injective {r1 r2 : WhirSecurityRegime}
    (h : r1.tagByte = r2.tagByte) : r1 = r2 := by
  have h1 := WhirSecurityRegime.decodeTag?_tagByte r1
  rw [h, WhirSecurityRegime.decodeTag?_tagByte r2] at h1
  exact (Option.some.inj h1).symm

/-- A tag decodes exactly when it is one of the six `repr(u8)` values. -/
theorem WhirSecurityRegime.decodeTag?_isSome_iff (tag : UInt8) :
    (WhirSecurityRegime.decodeTag? tag).isSome = true ↔
      tag = 2 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8 := by
  constructor
  · intro h
    cases hd : WhirSecurityRegime.decodeTag? tag with
    | none => rw [hd] at h; cases h
    | some r =>
      have ht := WhirSecurityRegime.tagByte_of_decodeTag? hd
      cases r
      · exact .inl ht.symm
      · exact .inr (.inl ht.symm)
      · exact .inr (.inr (.inl ht.symm))
      · exact .inr (.inr (.inr (.inl ht.symm)))
      · exact .inr (.inr (.inr (.inr (.inl ht.symm))))
      · exact .inr (.inr (.inr (.inr (.inr ht.symm))))
  · rintro (h | h | h | h | h | h) <;> rw [h] <;> rfl

/-- `WhirSecurityRegime::pow_bits`. -/
def WhirSecurityRegime.powBits : WhirSecurityRegime → Nat
  | .cdhz25ZeroPowQrom128 | .poseidon2Cdhz25ZeroPowQrom128 => 0
  | _ => 16

/-- `WhirSecurityRegime::pure_query_target_bits`: the exponent `t` such that every stage's
    distinct-fiber query error is below `2^-t` (`whirRegime_positive_slack`). -/
@[expose] def WhirSecurityRegime.pureQueryTargetBits : WhirSecurityRegime → Nat
  | .bciksJohnsonClassical128 => 128
  | .bciksJohnsonQrom128 => 256
  | .cdhz25JohnsonQrom128 | .poseidon2Cdhz25JohnsonQrom128 => 200
  | .cdhz25ZeroPowQrom128 | .poseidon2Cdhz25ZeroPowQrom128 => 214

/-- `WhirSecurityRegime::classical_fs_round_bits`: query target plus PoW bits. -/
def WhirSecurityRegime.classicalFsRoundBits (r : WhirSecurityRegime) : Nat :=
  r.pureQueryTargetBits + r.powBits

/-- `WhirSecurityRegime::qrom_grover_round_bits`: nominal single-round Grover search work.
    A per-round estimate, not a composed QROM security bound. -/
def WhirSecurityRegime.qromGroverRoundBits (r : WhirSecurityRegime) : Nat :=
  r.classicalFsRoundBits / 2

/-- `WhirSecurityRegime::meets_unconditional_grover_128_floor`. -/
def WhirSecurityRegime.meetsUnconditionalGrover128Floor (r : WhirSecurityRegime) : Bool :=
  decide (128 ≤ r.qromGroverRoundBits)

/-- `WhirSecurityRegime::meets_bounded_qrom_128_profile`: the four CDHZ25 regimes. -/
def WhirSecurityRegime.meetsBoundedQrom128Profile : WhirSecurityRegime → Bool
  | .cdhz25JohnsonQrom128 | .cdhz25ZeroPowQrom128
  | .poseidon2Cdhz25JohnsonQrom128 | .poseidon2Cdhz25ZeroPowQrom128 => true
  | _ => false

/-- `WhirSecurityRegime::meets_qrom_128_floor`: the aggregate authorization policy. Despite the
    Rust name, `true` does not mean 128 bits of unconditional Grover work. -/
def WhirSecurityRegime.meetsQrom128Floor (r : WhirSecurityRegime) : Bool :=
  r.meetsUnconditionalGrover128Floor || r.meetsBoundedQrom128Profile

/-- `WhirSecurityRegime::uses_poseidon2_canopy`. -/
def WhirSecurityRegime.usesPoseidon2Canopy : WhirSecurityRegime → Bool
  | .poseidon2Cdhz25JohnsonQrom128 | .poseidon2Cdhz25ZeroPowQrom128 => true
  | _ => false

/-- `log2` of the oracle-query budget a bounded-query profile is accounted at (doc comment of
    `WhirSecurityRegime`): `Q ≤ 2^38` for the 16-bit-PoW CDHZ25 table, `Q + 1 ≤ 2^40` for the
    zero-PoW table. The two Johnson regimes carry no query bound. -/
def WhirSecurityRegime.boundedQueryLog2? : WhirSecurityRegime → Option Nat
  | .cdhz25JohnsonQrom128 | .poseidon2Cdhz25JohnsonQrom128 => some 38
  | .cdhz25ZeroPowQrom128 | .poseidon2Cdhz25ZeroPowQrom128 => some 40
  | _ => none

/-- Denominator of the proximity slack `η = 1 / slackDen` at which
    `whirRegime_positive_slack` holds. -/
def WhirSecurityRegime.slackDen : WhirSecurityRegime → Nat
  | .bciksJohnsonQrom128 => 1024
  | _ => 512

/-- `#tooth`: retired capacity-proximity wire tags `0`, `1`, and `3` are rejected (`none`) by
    `WhirSecurityRegime.decodeTag?`. -/
theorem tooth_whirSecurityRegime_decodeTag_rejects_retired :
    WhirSecurityRegime.decodeTag? 0 = none ∧
    WhirSecurityRegime.decodeTag? 1 = none ∧
    WhirSecurityRegime.decodeTag? 3 = none := by
  decide

/-- Per-stage WHIR rate-escalation specification (`B_s = (4, 16, 64, 256)`). -/
structure WhirStageSpec where
  stageIdx : Nat
  blowup : Nat
  johnsonSqrtBlowup : Nat
  numQueries : Nat
  powBits : Nat
  deriving DecidableEq, Repr

/-- Full 4-stage `(4, 16, 64, 256)` WHIR schedule for each `WhirSecurityRegime`
    (`WhirSecurityRegime::minimum_queries` at `log2 B = 2, 4, 6, 8`, with `pow_bits`). -/
@[expose] def whirSchedule4Stage : WhirSecurityRegime → List WhirStageSpec
  | .bciksJohnsonClassical128 =>
    [ ⟨0, 4, 2, 129, 16⟩, ⟨1, 16, 4, 65, 16⟩, ⟨2, 64, 8, 44, 16⟩, ⟨3, 256, 16, 33, 16⟩ ]
  | .bciksJohnsonQrom128 =>
    [ ⟨0, 4, 2, 258, 16⟩, ⟨1, 16, 4, 130, 16⟩, ⟨2, 64, 8, 88, 16⟩, ⟨3, 256, 16, 66, 16⟩ ]
  | .cdhz25JohnsonQrom128 | .poseidon2Cdhz25JohnsonQrom128 =>
    [ ⟨0, 4, 2, 202, 16⟩, ⟨1, 16, 4, 102, 16⟩, ⟨2, 64, 8, 70, 16⟩, ⟨3, 256, 16, 52, 16⟩ ]
  | .cdhz25ZeroPowQrom128 | .poseidon2Cdhz25ZeroPowQrom128 =>
    [ ⟨0, 4, 2, 216, 0⟩, ⟨1, 16, 4, 109, 0⟩, ⟨2, 64, 8, 74, 0⟩, ⟨3, 256, 16, 56, 0⟩ ]

/-- 3-stage `(4, 16, 64)` WHIR schedule at `num_vars = 20` (`K = 8` shard). -/
def whirScheduleNv20 (r : WhirSecurityRegime) : List WhirStageSpec :=
  (whirSchedule4Stage r).take 3

/-- Every stage in every regime has exact integer square blowup `johnsonSqrtBlowup ^ 2 = blowup`. -/
theorem whirSchedule4Stage_sqrt_sq (r : WhirSecurityRegime) :
    ∀ s ∈ whirSchedule4Stage r, s.johnsonSqrtBlowup ^ 2 = s.blowup := by
  cases r <;> decide

/-- `#tooth`: historical capacity-proximity query counts `[128, 64, 43, 32]` across blowups
    `(4, 16, 64, 256)` (`√B = (2, 4, 8, 16)`) fail the unconditional `[BCIKS20]` Johnson 256-bit
    bound at every stage (`(√B_s)^{q_s} < 2^256` and
    `¬ ((1024 / √B_s + 1)^{q_s} * 2^256 < 1024^{q_s})`). -/
theorem tooth_retired_capacity_queries_fail_johnson_qrom256 :
    ∀ p ∈ ([(2, 128), (4, 64), (8, 43), (16, 32)] : List (Nat × Nat)),
      p.1 ^ p.2 < 2 ^ 256 ∧
      ¬ ((1024 / p.1 + 1) ^ p.2 * 2 ^ 256 < 1024 ^ p.2) := by
  decide +kernel

/-- **Unconditional `[BCIKS20]` Classical-128 Positive Johnson Proximity Slack
    (`bciksJohnsonClassical128_positive_slack`)**:
    With `+1` query (`q = (129, 65, 44, 33)`), EVERY stage satisfies `(1 / √B_s + η)^{q_s} < 2^-128`
    at concrete positive proximity slack `η = 1 / 512 > 0` (yielding explicit finite `[BCIKS20]`
    list-decoding bound `L ≤ 1 / (2η) = 256`). -/
theorem bciksJohnsonClassical128_positive_slack :
    ∀ s ∈ whirSchedule4Stage .bciksJohnsonClassical128,
      2 ^ 128 < s.johnsonSqrtBlowup ^ s.numQueries ∧
      (512 / s.johnsonSqrtBlowup + 1) ^ s.numQueries * 2 ^ 128 < 512 ^ s.numQueries := by
  decide

/-- **Unconditional `[BCIKS20]` QROM-128 Positive Johnson Proximity Slack
    (`bciksJohnsonQrom128_positive_slack`)**:
    With `+2` queries (`q = (258, 130, 88, 66)`), EVERY stage satisfies `(1 / √B_s + η)^{q_s} < 2^-256`
    at concrete positive proximity slack `η = 1 / 1024 > 0` (yielding explicit finite `[BCIKS20]`
    list-decoding bound `L ≤ 1 / (2η) = 512` and `136` QROM Grover round-search bits). -/
theorem bciksJohnsonQrom128_positive_slack :
    ∀ s ∈ whirSchedule4Stage .bciksJohnsonQrom128,
      2 ^ 256 < s.johnsonSqrtBlowup ^ s.numQueries ∧
      (1024 / s.johnsonSqrtBlowup + 1) ^ s.numQueries * 2 ^ 256 < 1024 ^ s.numQueries := by
  decide +kernel

/-- The Johnson schedules are the deployed `minimum_queries` formulas: `⌈256 / log₂ B⌉ + 1` at
    classical-128 and `⌈512 / log₂ B⌉ + 2` at QROM-128, with `log₂ B = 2 * log₂ √B`. -/
theorem bciksJohnson_schedules_eq_minimum_queries :
    (whirSchedule4Stage .bciksJohnsonClassical128).map (·.numQueries) =
      [2, 4, 6, 8].map (fun logB => (256 + logB - 1) / logB + 1) ∧
    (whirSchedule4Stage .bciksJohnsonQrom128).map (·.numQueries) =
      [2, 4, 6, 8].map (fun logB => (512 + logB - 1) / logB + 2) ∧
    (whirSchedule4Stage .bciksJohnsonQrom128).map (·.blowup) = [2, 4, 6, 8].map (2 ^ ·) := by
  decide

/-- **Per-regime query target with positive proximity slack.** In every one of the six
    regimes, every stage satisfies `(1 / √B_s + η)^{q_s} < 2^-t` at `η = 1 / r.slackDen > 0`,
    where `t = r.pureQueryTargetBits` is that regime's own target: `128, 256, 200, 214, 200,
    214` for tags `2, 4, 5, 6, 7, 8`. -/
theorem whirRegime_positive_slack (r : WhirSecurityRegime) :
    ∀ s ∈ whirSchedule4Stage r,
      2 ^ r.pureQueryTargetBits < s.johnsonSqrtBlowup ^ s.numQueries ∧
      (r.slackDen / s.johnsonSqrtBlowup + 1) ^ s.numQueries * 2 ^ r.pureQueryTargetBits <
        r.slackDen ^ s.numQueries ∧
      r.slackDen / s.johnsonSqrtBlowup + 1 ≤ r.slackDen ∧
      s.powBits = r.powBits := by
  cases r <;> decide +kernel

/-- **(a) The unconditional Grover-floor regime.** Exactly one of the six regimes, the default
    `bciksJohnsonQrom128` (tag `4`), has at least 128 nominal Grover round bits; it has 136. -/
theorem whirRegime_unconditional_grover_floor (r : WhirSecurityRegime) :
    (r.meetsUnconditionalGrover128Floor = true ↔ r = .bciksJohnsonQrom128) ∧
    WhirSecurityRegime.bciksJohnsonQrom128.qromGroverRoundBits = 136 := by
  cases r <;> decide

/-- **(b) The bounded-query profiles.** The four CDHZ25 regimes (tags `5, 6, 7, 8`) are exactly
    the regimes with `meetsBoundedQrom128Profile`. None reaches the 128-bit nominal Grover
    floor: tags `5, 7` have 108 bits at an accounted budget `Q ≤ 2^38`, tags `6, 8` have 107
    bits at `Q + 1 ≤ 2^40`. -/
theorem whirRegime_bounded_query_profiles (r : WhirSecurityRegime) :
    (r.meetsBoundedQrom128Profile = true ↔
      r = .cdhz25JohnsonQrom128 ∨ r = .cdhz25ZeroPowQrom128 ∨
      r = .poseidon2Cdhz25JohnsonQrom128 ∨ r = .poseidon2Cdhz25ZeroPowQrom128) ∧
    (r.meetsBoundedQrom128Profile = true → r.meetsUnconditionalGrover128Floor = false) ∧
    (r = .cdhz25JohnsonQrom128 ∨ r = .poseidon2Cdhz25JohnsonQrom128 →
      r.qromGroverRoundBits = 108 ∧ r.boundedQueryLog2? = some 38) ∧
    (r = .cdhz25ZeroPowQrom128 ∨ r = .poseidon2Cdhz25ZeroPowQrom128 →
      r.qromGroverRoundBits = 107 ∧ r.boundedQueryLog2? = some 40) := by
  cases r <;> decide

/-- Nominal Grover round bits of the six regimes in tag order `2, 4, 5, 6, 7, 8`; the
    classical regime (tag `2`) has 72 and is never authorized for aggregates. -/
theorem whirRegime_grover_round_bits_table :
    WhirSecurityRegime.all.map (·.qromGroverRoundBits) = [72, 136, 108, 107, 108, 107] ∧
    WhirSecurityRegime.all.map (·.meetsQrom128Floor) = [false, true, true, true, true, true] ∧
    WhirSecurityRegime.all.map (·.tagByte) = [2, 4, 5, 6, 7, 8] := by
  decide

/-- **Quadratic-search accounting of the bounded-query profiles.** With per-round failure
    probability `2^-(classicalFsRoundBits)` and at most `Q ≤ 2^b` oracle queries, `b` the
    profile's accounted budget, the search numerator `4 * Q^2` leaves at least 128 bits:
    `4 * Q^2 * 2^128 ≤ 2^(classicalFsRoundBits)`. This is arithmetic on the nominal round
    figure, not a QROM reduction. -/
theorem whirRegime_bounded_query_search_accounting (r : WhirSecurityRegime) (b Q : Nat)
    (hb : r.boundedQueryLog2? = some b) (hQ : Q ≤ 2 ^ b) :
    4 * Q ^ 2 * 2 ^ 128 ≤ 2 ^ r.classicalFsRoundBits := by
  have hmono : 4 * Q ^ 2 * 2 ^ 128 ≤ 4 * (2 ^ b) ^ 2 * 2 ^ 128 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hQ 2))
  refine Nat.le_trans hmono ?_
  cases r
  · cases hb
  · cases hb
  · cases Option.some.inj hb; decide
  · cases Option.some.inj hb; decide
  · cases Option.some.inj hb; decide
  · cases Option.some.inj hb; decide

set_option exponentiation.threshold 512 in
/-- The same accounting for the unconditional regime up to `Q ≤ 2^64` queries. -/
theorem whirRegime_unconditional_search_accounting (Q : Nat) (hQ : Q ≤ 2 ^ 64) :
    4 * Q ^ 2 * 2 ^ 128 ≤
      2 ^ WhirSecurityRegime.bciksJohnsonQrom128.classicalFsRoundBits :=
  Nat.le_trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hQ 2))) (by decide)

/-- `#tooth`: the superseded `+1` QROM stage-0 count `257` is not a stage of the deployed
    `bciksJohnsonQrom128` schedule. -/
theorem tooth_bciksJohnsonQrom128_stage0_is_not_257 :
    (⟨0, 4, 2, 257, 16⟩ : WhirStageSpec) ∉ whirSchedule4Stage .bciksJohnsonQrom128 := by
  decide

end Aggregation

/-- Parameters of the production `GoldilocksExt4` WHIR succinct aggregation proof system,
    aligned with `crates/qsag-agg/src/{pcs,arithmetize,trace,lib}.rs`. -/
structure ProductionAggParams where
  rowSumcheckDegree : Nat
  logTraceCols : Nat
  maxPcsVars : Nat
  rsBlowup : Nat
  /-- Wire/parser query cap (`NUM_PCS_QUERIES` in `pcs.rs`); active counts come from the schedule. -/
  maxQueryCap : Nat
  stageBlowups : List Nat
  classicalJohnsonQueries : List Nat
  defaultQromQueries : List Nat
  johnsonQromQueries : List Nat
  earlyStopVars : Nat
  maxFoldStepVars : Nat
  pcsSumcheckDegree : Nat
  powBits : Nat
  maxWhirStages : Nat
  maxMergeDepth : Nat
  fieldSize : Nat
  deriving DecidableEq, Repr

def productionAggParams : ProductionAggParams where
  rowSumcheckDegree := 8
  logTraceCols := 8
  maxPcsVars := 28
  rsBlowup := 4
  maxQueryCap := 512
  stageBlowups := [4, 16, 64, 256]
  classicalJohnsonQueries := [129, 65, 44, 33]
  defaultQromQueries := [258, 130, 88, 66]
  johnsonQromQueries := [258, 130, 88, 66]
  earlyStopVars := 8
  maxFoldStepVars := 6
  pcsSumcheckDegree := 2
  powBits := 16
  maxWhirStages := 4
  maxMergeDepth := 16
  fieldSize := goldilocksPrime ^ 4

def ProductionAggParams.maxRowRounds (p : ProductionAggParams) : Nat := p.maxPcsVars - p.logTraceCols
def ProductionAggParams.maxFoldRounds (p : ProductionAggParams) : Nat := p.maxPcsVars - p.earlyStopVars
def ProductionAggParams.maxStage0Domain (p : ProductionAggParams) : Nat := 2 ^ p.maxPcsVars * p.rsBlowup
def ProductionAggParams.maxQueryGroups (p : ProductionAggParams) : Nat :=
  p.maxStage0Domain / 2 ^ p.maxFoldStepVars

theorem productionAggParams_derived :
    productionAggParams.maxRowRounds = 20 ∧
    productionAggParams.maxFoldRounds = 20 ∧
    productionAggParams.maxStage0Domain = 2 ^ 30 ∧
    productionAggParams.maxQueryGroups = 2 ^ 24 ∧
    2 ^ 255 < productionAggParams.fieldSize := by
  decide

/-- The production query lists are the unconditional `bciksJohnsonClassical128` and default
    `bciksJohnsonQrom128` schedules, and every scheduled query count in every regime fits under
    the wire cap `maxQueryCap = 512`. -/
theorem productionAggParams_queries_match_schedule :
    productionAggParams.classicalJohnsonQueries =
      (Aggregation.whirSchedule4Stage .bciksJohnsonClassical128).map (·.numQueries) ∧
    productionAggParams.defaultQromQueries =
      (Aggregation.whirSchedule4Stage .bciksJohnsonQrom128).map (·.numQueries) ∧
    productionAggParams.johnsonQromQueries =
      (Aggregation.whirSchedule4Stage .bciksJohnsonQrom128).map (·.numQueries) ∧
    (∀ r : Aggregation.WhirSecurityRegime, ∀ s ∈ Aggregation.whirSchedule4Stage r,
      s.numQueries ≤ productionAggParams.maxQueryCap) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro r
  cases r <;> decide

/-- `#tooth`: the superseded cap `257` would reject the deployed `bciksJohnsonQrom128` stage-0
    query count. -/
theorem tooth_productionAggParams_cap_257_rejects_johnson_qrom :
    ¬ (∀ s ∈ Aggregation.whirSchedule4Stage .bciksJohnsonQrom128, s.numQueries ≤ 257) := by
  decide

namespace Aggregation

/-! ## 6. Degree-8 `GoldilocksExt4` Sumcheck & Constructive Divergence Extractor (`0 Classical`) -/

/-- Transcript-indexed hit where two unequal polynomials of degree `≤ maxDeg` over `GoldilocksExt4`
    agree at the verifier's round challenge. -/
structure SumcheckSchwartzZippelHit (maxDeg : Nat)
    (claimedPolys honestPolys : List (List GoldilocksExt4))
    (challenges : List GoldilocksExt4) where
  roundIdx : Nat
  claimedPoly : List GoldilocksExt4
  honestPoly : List GoldilocksExt4
  challenge : GoldilocksExt4
  claimed_at : claimedPolys[roundIdx]? = some claimedPoly
  honest_at : honestPolys[roundIdx]? = some honestPoly
  challenge_at : challenges[roundIdx]? = some challenge
  lenClaimed : claimedPoly.length ≤ maxDeg + 1
  lenHonest : honestPoly.length ≤ maxDeg + 1
  diffPoint : GoldilocksExt4
  polyNe : RoundPoly.evalCoeffs claimedPoly diffPoint ≠ RoundPoly.evalCoeffs honestPoly diffPoint
  hitEq : RoundPoly.evalCoeffs claimedPoly challenge = RoundPoly.evalCoeffs honestPoly challenge

/-- Parametric univariate sumcheck chain verifier (`p.length ≤ maxDeg + 1`, `P(0) + P(1) == curClaim`,
    advancing `curClaim := P(r)` down to `termEval`). -/
def verifySumcheckChainDeg (maxDeg : Nat) :
    GoldilocksExt4 → List (List GoldilocksExt4) → List GoldilocksExt4 → GoldilocksExt4 → Bool
  | curClaim, [], [], termEval => curClaim == termEval
  | curClaim, p :: ps, r :: rs, termEval =>
    decide (p.length ≤ maxDeg + 1) &&
    (CommRingOps.add (RoundPoly.evalCoeffs p GoldilocksExt4.zero)
                     (RoundPoly.evalCoeffs p GoldilocksExt4.one) == curClaim) &&
    verifySumcheckChainDeg maxDeg (RoundPoly.evalCoeffs p r) ps rs termEval
  | _, _, _, _ => false

/-- Degree-8 row sumcheck verifier over `GoldilocksExt4`. -/
abbrev verifySumcheckChain := verifySumcheckChainDeg 8

/-- Degree-2 WHIR per-stage shift/OOD sumcheck verifier over `GoldilocksExt4`. -/
abbrev verifyShiftSumcheckChain := verifySumcheckChainDeg 2

/-- **`#tooth` Ninth-Degree Row Polynomial Rejection (`sumcheck_degree9_rejected`)**:
    A round polynomial with `> 9` coefficients (`deg ≥ 9`) is unconditionally rejected. -/
theorem sumcheck_degree9_rejected (claim terminal : GoldilocksExt4)
    (p : List GoldilocksExt4) (ps : List (List GoldilocksExt4))
    (r : GoldilocksExt4) (rs : List GoldilocksExt4) (h : 9 < p.length) :
    verifySumcheckChain claim (p :: ps) (r :: rs) terminal = false := by
  simp only [verifySumcheckChain, verifySumcheckChainDeg, show ¬ p.length ≤ 9 by omega,
    decide_false, Bool.false_and]

/-- **`#tooth` Cubic Shift Polynomial Rejection (`shift_sumcheck_degree3_rejected`)**:
    A per-stage shift/OOD sumcheck polynomial with `> 3` coefficients (`deg ≥ 3`) is rejected. -/
theorem shift_sumcheck_degree3_rejected (claim terminal : GoldilocksExt4)
    (p : List GoldilocksExt4) (ps : List (List GoldilocksExt4))
    (r : GoldilocksExt4) (rs : List GoldilocksExt4) (h : 3 < p.length) :
    verifyShiftSumcheckChain claim (p :: ps) (r :: rs) terminal = false := by
  simp only [verifyShiftSumcheckChain, verifySumcheckChainDeg, show ¬ p.length ≤ 3 by omega,
    decide_false, Bool.false_and]

/-- Succinct aggregated signature header + degree-8 `GoldilocksExt4` row sumcheck certificate
    (carrying zero plaintext `PqHashSig` elements). -/
structure AggregatedSignature where
  suite : TweakableHashSuite
  params : PqHashParams
  regime : WhirSecurityRegime := .bciksJohnsonQrom128
  bitmap : SignerBitmapSpec
  signerCount : Nat
  traceCommitment : List UInt8
  claimedSum : GoldilocksExt4
  roundPolys : List (List GoldilocksExt4)
  challenges : List GoldilocksExt4
  terminalEval : GoldilocksExt4
  childrenCommitment : Option (List UInt8 × List UInt8) := none

/-- Algebra-only sumcheck check (intentionally insufficient without WHIR PCS verification;
    retained for `verifyDisjointMerge` and the `zero_certificate_passes_algebra` counterexample). -/
def verifyAggregateAlgebra (committee : List PqPublicKey) (agg : AggregatedSignature) : Bool :=
  (agg.bitmap.length == committee.length) &&
  (agg.signerCount == bitmapPopcountSpec agg.bitmap) &&
  decide (0 < agg.signerCount) &&
  decide (0 < agg.roundPolys.length) &&
  (agg.claimedSum == GoldilocksExt4.zero) &&
  verifySumcheckChain agg.claimedSum agg.roundPolys agg.challenges agg.terminalEval

/-- Disjoint 2-to-1 bitmap + algebraic merge check. -/
def verifyDisjointMerge (committee : List PqPublicKey)
    (left right merged : AggregatedSignature) : Bool :=
  verifyAggregateAlgebra committee left &&
  verifyAggregateAlgebra committee right &&
  bitmapDisjointSpec left.bitmap right.bitmap &&
  (merged.bitmap == bitmapUnionSpec left.bitmap right.bitmap) &&
  verifyAggregateAlgebra committee merged

theorem merge_aggregates_disjoint_sound (committee : List PqPublicKey)
    (left right merged : AggregatedSignature)
    (hOk : verifyDisjointMerge committee left right merged = true) :
    bitmapDisjointSpec left.bitmap right.bitmap = true ∧
    merged.bitmap = bitmapUnionSpec left.bitmap right.bitmap ∧
    merged.signerCount = left.signerCount + right.signerCount := by
  unfold verifyDisjointMerge at hOk
  rcases Bool.and_eq_true_iff.mp hOk with ⟨h1234, hVerM⟩
  rcases Bool.and_eq_true_iff.mp h1234 with ⟨h123, hBmEq⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, hDisj⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hVerL, hVerR⟩
  have hBm : merged.bitmap = bitmapUnionSpec left.bitmap right.bitmap := eq_of_beq hBmEq
  unfold verifyAggregateAlgebra at hVerL hVerR hVerM
  rcases Bool.and_eq_true_iff.mp hVerL with ⟨hL12345, _⟩
  rcases Bool.and_eq_true_iff.mp hL12345 with ⟨hL1234, _⟩
  rcases Bool.and_eq_true_iff.mp hL1234 with ⟨hL123, _⟩
  rcases Bool.and_eq_true_iff.mp hL123 with ⟨hL12, _⟩
  rcases Bool.and_eq_true_iff.mp hL12 with ⟨hLenL, hCntL⟩
  rcases Bool.and_eq_true_iff.mp hVerR with ⟨hR12345, _⟩
  rcases Bool.and_eq_true_iff.mp hR12345 with ⟨hR1234, _⟩
  rcases Bool.and_eq_true_iff.mp hR1234 with ⟨hR123, _⟩
  rcases Bool.and_eq_true_iff.mp hR123 with ⟨hR12, _⟩
  rcases Bool.and_eq_true_iff.mp hR12 with ⟨hLenR, hCntR⟩
  rcases Bool.and_eq_true_iff.mp hVerM with ⟨hM12345, _⟩
  rcases Bool.and_eq_true_iff.mp hM12345 with ⟨hM1234, _⟩
  rcases Bool.and_eq_true_iff.mp hM1234 with ⟨hM123, _⟩
  rcases Bool.and_eq_true_iff.mp hM123 with ⟨hM12, _⟩
  rcases Bool.and_eq_true_iff.mp hM12 with ⟨_, hCntM⟩
  have hLenEq : left.bitmap.length = right.bitmap.length :=
    (eq_of_beq hLenL).trans (eq_of_beq hLenR).symm
  have hPop := popcount_union_disjoint_eq_add left.bitmap right.bitmap hLenEq hDisj
  refine ⟨hDisj, hBm, ?_⟩
  rw [eq_of_beq hCntM, hBm, hPop, ← eq_of_beq hCntL, ← eq_of_beq hCntR]

theorem verifySumcheckChainDeg_zeroPolys (maxDeg : Nat) :
    ∀ (challenges : List GoldilocksExt4),
      verifySumcheckChainDeg maxDeg GoldilocksExt4.zero
        (challenges.map (fun _ => [GoldilocksExt4.zero]))
        challenges GoldilocksExt4.zero = true
  | [] => by simp [verifySumcheckChainDeg]
  | r :: rs => by
    have ih := verifySumcheckChainDeg_zeroPolys maxDeg rs
    have hEv0 : RoundPoly.evalCoeffs [GoldilocksExt4.zero] GoldilocksExt4.zero =
        GoldilocksExt4.zero := by
      simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    have hEv1 : RoundPoly.evalCoeffs [GoldilocksExt4.zero] GoldilocksExt4.one =
        GoldilocksExt4.zero := by
      simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    have hEvR : RoundPoly.evalCoeffs [GoldilocksExt4.zero] r = GoldilocksExt4.zero := by
      simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    have hAdd0 : CommRingOps.add GoldilocksExt4.zero GoldilocksExt4.zero =
        GoldilocksExt4.zero := LawfulCommRing.add_zero GoldilocksExt4.zero
    simp [verifySumcheckChainDeg, hEv0, hEv1, hEvR, hAdd0, ih]

/-- **`#tooth` Counterexample to Algebra-Only Verification (`zero_certificate_passes_algebra`)**:
    Without WHIR PCS verification, an all-zero polynomial chain passes `verifyAggregateAlgebra`. -/
theorem zero_certificate_passes_algebra (suite : TweakableHashSuite) (params : PqHashParams)
    (committee : List PqPublicKey) (bitmap : SignerBitmapSpec)
    (traceComm : List UInt8) (challenges : List GoldilocksExt4)
    (hLen : bitmap.length = committee.length)
    (hPos : 0 < bitmapPopcountSpec bitmap)
    (hVars : 0 < challenges.length) :
    verifyAggregateAlgebra committee
      { suite := suite, params := params, bitmap := bitmap,
        signerCount := bitmapPopcountSpec bitmap, traceCommitment := traceComm,
        claimedSum := GoldilocksExt4.zero,
        roundPolys := challenges.map (fun _ => [GoldilocksExt4.zero]),
        challenges := challenges, terminalEval := GoldilocksExt4.zero } = true := by
  simp [verifyAggregateAlgebra, verifySumcheckChain, hLen, hPos, hVars,
        verifySumcheckChainDeg_zeroPolys]

/-- Constructive check of every active signer bit `i` in `bitmap` against `verifyPqHashSig`
    (used exclusively in the extractor's target relation, never by the succinct verifier). -/
def checkAllActiveSigners (suite : TweakableHashSuite) (params : PqHashParams)
    (msg : List UInt8) : List PqPublicKey → SignerBitmapSpec → List PqHashSig → Bool
  | [], [], _ => true
  | pk :: pks, active :: bs, sig :: sigs =>
    (if active then verifyPqHashSig suite params pk msg sig else true) &&
    checkAllActiveSigners suite params msg pks bs sigs
  | _, _, _ => false

/-- Constructive `Type`-valued witness projection (`0 Classical.choice`) returning the concrete
    `PqHashSig` for active signer index `i`. -/
def extractActiveSignerSig (suite : TweakableHashSuite) (params : PqHashParams)
    (msg : List UInt8) :
    ∀ (pks : List PqPublicKey) (bs : SignerBitmapSpec) (sigs : List PqHashSig) (i : Nat)
      (hPk : i < pks.length) (hB : i < bs.length),
      checkAllActiveSigners suite params msg pks bs sigs = true →
      bs[i]'hB = true →
      { sig : PqHashSig // verifyPqHashSig suite params (pks[i]'hPk) msg sig = true }
  | [], _, _, _, hPk, _, _, _ => False.elim (by simp at hPk)
  | _ :: _, [], _, _, _, hB, _, _ => False.elim (by simp at hB)
  | _ :: _, _ :: _, [], _, _, _, hAll, _ => False.elim (by simp [checkAllActiveSigners] at hAll)
  | _ :: _, b :: _, sig :: _, 0, _, _, hAll, hbTrue =>
    ⟨sig, by
      simp only [List.getElem_cons_zero] at hbTrue ⊢
      simp only [checkAllActiveSigners, hbTrue, ↓reduceIte, Bool.and_eq_true] at hAll
      exact hAll.1⟩
  | _ :: pks, _ :: bs, _ :: sigs, i + 1, hPk, hB, hAll, hbTrue =>
    extractActiveSignerSig suite params msg pks bs sigs i
      (Nat.lt_of_succ_lt_succ hPk) (Nat.lt_of_succ_lt_succ hB)
      (Bool.and_eq_true_iff.mp hAll).2 hbTrue

theorem checkAllActiveSigners_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (msg : List UInt8)
    (pks : List PqPublicKey) (bs : SignerBitmapSpec) (sigs : List PqHashSig) (i : Nat)
    (hPk : i < pks.length) (hB : i < bs.length)
    (hAll : checkAllActiveSigners suite params msg pks bs sigs = true)
    (hbTrue : bs[i]'hB = true) :
    ∃ sig, verifyPqHashSig suite params (pks[i]'hPk) msg sig = true := by
  let ⟨sig, hVer⟩ := extractActiveSignerSig suite params msg pks bs sigs i hPk hB hAll hbTrue
  exact ⟨sig, hVer⟩

/-- **Constructive Round-by-Round `GoldilocksExt4` Sumcheck Divergence Extractor
    (`extractSumcheckHitFromChain`, `0 Classical.choice`)**:
    Whenever `curClaim ≠ honestClaim` at the start of `verifySumcheckChainDeg maxDeg` while both
    chains accept and agree at `termEval`, constructively locates the exact first round where
    `claimedPoly` and `honestPoly` disagree on `{0, 1}` yet collide at verifier challenge `r`. -/
def extractSumcheckHitFromChain (maxDeg : Nat)
    (claimedPolys : List (List GoldilocksExt4)) :
    ∀ (curClaim honestClaim : GoldilocksExt4)
      (honestPolys : List (List GoldilocksExt4))
      (challenges : List GoldilocksExt4)
      (termEval : GoldilocksExt4),
      curClaim ≠ honestClaim →
      verifySumcheckChainDeg maxDeg curClaim claimedPolys challenges termEval = true →
      verifySumcheckChainDeg maxDeg honestClaim honestPolys challenges termEval = true →
      SumcheckSchwartzZippelHit maxDeg claimedPolys honestPolys challenges :=
  match claimedPolys with
  | [] => fun curClaim honestClaim honestPolys challenges termEval hNe hVerC hVerH =>
    match honestPolys, challenges with
    | [], [] =>
      False.elim (by
        simp only [verifySumcheckChainDeg, beq_iff_eq] at hVerC hVerH
        exact hNe (hVerC.trans hVerH.symm))
    | _ :: _, [] => False.elim (by simp [verifySumcheckChainDeg] at hVerH)
    | _, _ :: _ => False.elim (by simp [verifySumcheckChainDeg] at hVerC)
  | pC :: psC => fun curClaim honestClaim honestPolys challenges termEval hNe hVerC hVerH =>
    match honestPolys, challenges with
    | _, [] => False.elim (by simp [verifySumcheckChainDeg] at hVerC)
    | [], _ :: _ => False.elim (by simp [verifySumcheckChainDeg] at hVerH)
    | pH :: psH, r :: rs =>
      have hUnpackC : pC.length ≤ maxDeg + 1 ∧
          CommRingOps.add (RoundPoly.evalCoeffs pC GoldilocksExt4.zero)
                          (RoundPoly.evalCoeffs pC GoldilocksExt4.one) = curClaim ∧
          verifySumcheckChainDeg maxDeg (RoundPoly.evalCoeffs pC r) psC rs termEval = true := by
        simp only [verifySumcheckChainDeg, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hVerC
        exact ⟨hVerC.1.1, hVerC.1.2, hVerC.2⟩
      have hUnpackH : pH.length ≤ maxDeg + 1 ∧
          CommRingOps.add (RoundPoly.evalCoeffs pH GoldilocksExt4.zero)
                          (RoundPoly.evalCoeffs pH GoldilocksExt4.one) = honestClaim ∧
          verifySumcheckChainDeg maxDeg (RoundPoly.evalCoeffs pH r) psH rs termEval = true := by
        simp only [verifySumcheckChainDeg, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hVerH
        exact ⟨hVerH.1.1, hVerH.1.2, hVerH.2⟩
      let diffPt : GoldilocksExt4 :=
        if RoundPoly.evalCoeffs pC GoldilocksExt4.zero ≠ RoundPoly.evalCoeffs pH GoldilocksExt4.zero
        then GoldilocksExt4.zero
        else GoldilocksExt4.one
      have hDiffPt : RoundPoly.evalCoeffs pC diffPt ≠ RoundPoly.evalCoeffs pH diffPt := by
        dsimp only [diffPt]
        if h0 : RoundPoly.evalCoeffs pC GoldilocksExt4.zero ≠
            RoundPoly.evalCoeffs pH GoldilocksExt4.zero then
          simp [h0]
        else
          have hEq0 : RoundPoly.evalCoeffs pC GoldilocksExt4.zero =
              RoundPoly.evalCoeffs pH GoldilocksExt4.zero :=
            Decidable.of_not_not h0
          simp only [h0, ↓reduceIte]
          intro hEq1
          apply hNe
          rw [← hUnpackC.2.1, ← hUnpackH.2.1, hEq0, hEq1]
      if hHit : RoundPoly.evalCoeffs pC r = RoundPoly.evalCoeffs pH r then
        { roundIdx := 0
          claimedPoly := pC
          honestPoly := pH
          challenge := r
          claimed_at := rfl
          honest_at := rfl
          challenge_at := rfl
          lenClaimed := hUnpackC.1
          lenHonest := hUnpackH.1
          diffPoint := diffPt
          polyNe := hDiffPt
          hitEq := hHit }
      else
        let hit := extractSumcheckHitFromChain maxDeg psC
          (RoundPoly.evalCoeffs pC r) (RoundPoly.evalCoeffs pH r)
          psH rs termEval hHit hUnpackC.2.2 hUnpackH.2.2
        { roundIdx := hit.roundIdx + 1
          claimedPoly := hit.claimedPoly
          honestPoly := hit.honestPoly
          challenge := hit.challenge
          claimed_at := hit.claimed_at
          honest_at := hit.honest_at
          challenge_at := hit.challenge_at
          lenClaimed := hit.lenClaimed
          lenHonest := hit.lenHonest
          diffPoint := hit.diffPoint
          polyNe := hit.polyNe
          hitEq := hit.hitEq }
termination_by structural claimedPolys

/-- Honest round polynomials generated adaptively from the challenge prefix. -/
def adaptivePolysAux {α β : Type} (poly : List α → β) : List α → List α → List β
  | _, [] => []
  | pre, r :: rs => poly pre :: adaptivePolysAux poly (r :: pre) rs

def adaptivePolys {α β : Type} (poly : List α → β) (challenges : List α) : List β :=
  adaptivePolysAux poly [] challenges

/-! ## 7. Multi-Stage `GoldilocksExt4` WHIR + OOD + PoW + Merkle Duet Verifier -/

/-- Public aggregation statement bound into the Fiat–Shamir transcript before any challenge. -/
structure AggPublicInstance where
  suite : TweakableHashSuite
  params : PqHashParams
  regime : WhirSecurityRegime := .bciksJohnsonQrom128
  message : List UInt8
  committee : List PqPublicKey
  signingModeDigest : List UInt8

/-- Canonical little-endian base-256 byte framing of arbitrary `Nat` values (`0 ↦ []`). -/
def encodeNatBytes : Nat → List UInt8
  | 0 => []
  | n + 1 => UInt8.ofNat ((n + 1) % 256) :: encodeNatBytes ((n + 1) / 256)
termination_by n => n

theorem encodeNatBytes_injective {a : Nat} :
    ∀ {b : Nat}, encodeNatBytes a = encodeNatBytes b → a = b := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b h
    cases a with
    | zero =>
      cases b with
      | zero => rfl
      | succ b' => rw [encodeNatBytes, encodeNatBytes] at h; cases h
    | succ a' =>
      cases b with
      | zero => rw [encodeNatBytes, encodeNatBytes] at h; cases h
      | succ b' =>
        rw [encodeNatBytes, encodeNatBytes] at h
        obtain ⟨hHead, hTail⟩ := List.cons.inj h
        have hToNat : ((a' + 1) % 256) % 256 = ((b' + 1) % 256) % 256 :=
          congrArg UInt8.toNat hHead
        have hDiv : (a' + 1) / 256 = (b' + 1) / 256 :=
          ih ((a' + 1) / 256) (Nat.div_lt_self (Nat.succ_pos a') (by decide)) hTail
        omega

def encodeBoolByte (b : Bool) : UInt8 := if b then 1 else 0

theorem encodeBoolByte_injective {x y : Bool} (h : encodeBoolByte x = encodeBoolByte y) :
    x = y := by
  cases x <;> cases y <;> first | rfl | cases h

private theorem list_map_inj {α β : Type} {f : α → β}
    (hf : ∀ {x y : α}, f x = f y → x = y) :
    ∀ {xs ys : List α}, xs.map f = ys.map f → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    obtain ⟨hxy, hrest⟩ := List.cons.inj h
    rw [hf hxy, list_map_inj hf hrest]

def encodeAggPqPublicKey (pk : PqPublicKey) : List UInt8 :=
  encodeMultiFrame [pk.pkSeed, pk.pkRoot]

theorem encodeAggPqPublicKey_injective {p1 p2 : PqPublicKey}
    (h : encodeAggPqPublicKey p1 = encodeAggPqPublicKey p2) : p1 = p2 := by
  cases p1; cases p2
  have hf := encodeMultiFrame_injective h
  obtain ⟨hs, hf⟩ := List.cons.inj hf
  obtain ⟨hr, _⟩ := List.cons.inj hf
  simp only [PqPublicKey.mk.injEq]
  exact ⟨hs, hr⟩

def encodeAggCommittee (committee : List PqPublicKey) : List UInt8 :=
  encodeMultiFrame (committee.map encodeAggPqPublicKey)

theorem encodeAggCommittee_injective {c1 c2 : List PqPublicKey}
    (h : encodeAggCommittee c1 = encodeAggCommittee c2) : c1 = c2 :=
  list_map_inj encodeAggPqPublicKey_injective (encodeMultiFrame_injective h)

def encodeAggPqHashParams (p : PqHashParams) : List UInt8 :=
  encodeMultiFrame [encodeNatBytes p.w, encodeNatBytes p.ell1,
    encodeNatBytes p.subtreeHeight, encodeNatBytes p.numLayers,
    encodeNatBytes p.forsTrees, encodeNatBytes p.forsHeight,
    encodeNatBytes p.maxSigsLog2, [encodeBoolByte p.statefulJorts]]

theorem encodeAggPqHashParams_injective {p1 p2 : PqHashParams}
    (h : encodeAggPqHashParams p1 = encodeAggPqHashParams p2) : p1 = p2 := by
  cases p1; cases p2
  have hf := encodeMultiFrame_injective h
  obtain ⟨e1, hf⟩ := List.cons.inj hf
  obtain ⟨e2, hf⟩ := List.cons.inj hf
  obtain ⟨e3, hf⟩ := List.cons.inj hf
  obtain ⟨e4, hf⟩ := List.cons.inj hf
  obtain ⟨e5, hf⟩ := List.cons.inj hf
  obtain ⟨e6, hf⟩ := List.cons.inj hf
  obtain ⟨e7, hf⟩ := List.cons.inj hf
  obtain ⟨e8, _⟩ := List.cons.inj hf
  have eb := encodeBoolByte_injective (List.cons.inj e8).1
  simp only [PqHashParams.mk.injEq]
  exact ⟨encodeNatBytes_injective e1, encodeNatBytes_injective e2,
    encodeNatBytes_injective e3, encodeNatBytes_injective e4,
    encodeNatBytes_injective e5, encodeNatBytes_injective e6,
    encodeNatBytes_injective e7, eb⟩

def encodeChildrenCommitment : Option (List UInt8 × List UInt8) → List UInt8
  | none => [0]
  | some (left, right) => 1 :: encodeMultiFrame [left, right]

theorem encodeChildrenCommitment_injective {c1 c2 : Option (List UInt8 × List UInt8)}
    (h : encodeChildrenCommitment c1 = encodeChildrenCommitment c2) : c1 = c2 := by
  cases c1 with
  | none =>
    cases c2 with
    | none => rfl
    | some p => cases p; cases h
  | some p1 =>
    rcases p1 with ⟨l1, r1⟩
    cases c2 with
    | none => cases h
    | some p2 =>
      rcases p2 with ⟨l2, r2⟩
      have hf := encodeMultiFrame_injective (List.cons.inj h).2
      obtain ⟨hl, hf⟩ := List.cons.inj hf
      obtain ⟨hr, _⟩ := List.cons.inj hf
      rw [hl, hr]

/-- Canonical injective instance framing binding `message`, `signingModeDigest`, `regime`,
    `suite.suiteId`, `committee`, `params`, `bitmap`, `traceCommitment`, and
    `childrenCommitment`. -/
def aggregateInstanceFrame (inst : AggPublicInstance) (agg : AggregatedSignature) : List UInt8 :=
  encodeMultiFrame [inst.message, inst.signingModeDigest, [inst.regime.tagByte],
    inst.suite.suiteId,
    encodeAggCommittee inst.committee,
    encodeAggPqHashParams inst.params,
    agg.bitmap.map encodeBoolByte,
    agg.traceCommitment,
    encodeChildrenCommitment agg.childrenCommitment]

/-- **Full Pre-Locked Instance & Header Framing Injectivity (`aggregateInstanceFrame_injective`)**:
    Equality of `aggregateInstanceFrame` implies field-by-field equality across all nine public
    instance and aggregate-header fields (`message`, `signingModeDigest`, `regime`, `suite.suiteId`,
    `committee`, `params`, `bitmap`, `traceCommitment`, `childrenCommitment`). -/
theorem aggregateInstanceFrame_injective (first second : AggPublicInstance)
    (a b : AggregatedSignature)
    (h : aggregateInstanceFrame first a = aggregateInstanceFrame second b) :
    first.message = second.message ∧
    first.signingModeDigest = second.signingModeDigest ∧
    first.regime = second.regime ∧
    first.suite.suiteId = second.suite.suiteId ∧
    first.committee = second.committee ∧
    first.params = second.params ∧
    a.bitmap = b.bitmap ∧
    a.traceCommitment = b.traceCommitment ∧
    a.childrenCommitment = b.childrenCommitment := by
  have hf := encodeMultiFrame_injective h
  obtain ⟨hMsg, hf⟩ := List.cons.inj hf
  obtain ⟨hMode, hf⟩ := List.cons.inj hf
  obtain ⟨hReg, hf⟩ := List.cons.inj hf
  obtain ⟨hSuite, hf⟩ := List.cons.inj hf
  obtain ⟨hComm, hf⟩ := List.cons.inj hf
  obtain ⟨hParams, hf⟩ := List.cons.inj hf
  obtain ⟨hBm, hf⟩ := List.cons.inj hf
  obtain ⟨hTr, hf⟩ := List.cons.inj hf
  obtain ⟨hCh, _⟩ := List.cons.inj hf
  exact ⟨hMsg, hMode, WhirSecurityRegime.tagByte_injective (List.cons.inj hReg).1,
    hSuite, encodeAggCommittee_injective hComm, encodeAggPqHashParams_injective hParams,
    list_map_inj encodeBoolByte_injective hBm, hTr, encodeChildrenCommitment_injective hCh⟩

theorem aggregate_frame_message_binding (first second : AggPublicInstance)
    (a b : AggregatedSignature)
    (h : aggregateInstanceFrame first a = aggregateInstanceFrame second b) :
    first.message = second.message :=
  (aggregateInstanceFrame_injective first second a b h).1

theorem aggregate_frame_regime_binding (first second : AggPublicInstance)
    (a b : AggregatedSignature)
    (h : aggregateInstanceFrame first a = aggregateInstanceFrame second b) :
    first.regime = second.regime :=
  (aggregateInstanceFrame_injective first second a b h).2.2.1

/-- Canonical byte framing of a polynomial over `GoldilocksExt4`. -/
def encodePolyExt4 (p : List GoldilocksExt4) : List UInt8 :=
  encodeMultiFrame (p.map GoldilocksExt4.encodeBytes32)

/-- Deterministic Fiat–Shamir `GoldilocksExt4` challenge squeeze (`32` bytes -> `4` `Goldilocks` limbs). -/
def squeezeExt4Challenge (domainTag : List UInt8) (frame : List UInt8) : GoldilocksExt4 :=
  let bytes := cshake256Bytes domainTag frame
  let c00 := Goldilocks.ofNat (ofBE (bytes.take 8))
  let c01 := Goldilocks.ofNat (ofBE ((bytes.drop 8).take 8))
  let c10 := Goldilocks.ofNat (ofBE ((bytes.drop 16).take 8))
  let c11 := Goldilocks.ofNat (ofBE ((bytes.drop 24).take 8))
  ⟨⟨c00, c01⟩, ⟨c10, c11⟩⟩

/-- Derive degree-8 row-sumcheck challenges sequentially after absorbing each round polynomial. -/
def deriveRowSumcheckChallenges (prior : List UInt8) :
    List (List GoldilocksExt4) → List GoldilocksExt4
  | [] => []
  | p :: ps =>
    let frame := encodeMultiFrame [prior, encodePolyExt4 p]
    let r := squeezeExt4Challenge "LEAF_SC_CHAL".toUTF8.toList frame
    r :: deriveRowSumcheckChallenges frame ps

def rowSumcheckTranscriptTail (prior : List UInt8) : List (List GoldilocksExt4) → List UInt8
  | [] => prior
  | p :: ps => rowSumcheckTranscriptTail (encodeMultiFrame [prior, encodePolyExt4 p]) ps

/-- Hash used for Merkle-Canopy leaves and internal nodes (`CANOPY_MIDSTATE`). -/
def pcsMerkleHash : Hash := cshake256Bytes "QSAG.PCS.CANOPY/v2".toUTF8.toList

def merkleNodeFrame (idx : Nat) (node sib : List UInt8) : List UInt8 :=
  encodeMultiFrame (if idx % 2 = 0 then [node, sib] else [sib, node])

theorem merkleNodeFrame_node_injective {idx : Nat} {n1 s1 n2 s2 : List UInt8}
    (h : merkleNodeFrame idx n1 s1 = merkleNodeFrame idx n2 s2) : n1 = n2 := by
  have hinj := encodeMultiFrame_injective h
  by_cases hpar : idx % 2 = 0
  · simp only [hpar, ↓reduceIte] at hinj
    exact (List.cons.inj hinj).1
  · simp only [hpar, ↓reduceIte] at hinj
    exact (List.cons.inj (List.cons.inj hinj).2).1

def merklePathRoot (H : Hash) : List UInt8 → Nat → List (List UInt8) → List UInt8
  | node, _, [] => node
  | node, idx, sib :: rest => merklePathRoot H (H (merkleNodeFrame idx node sib)) (idx / 2) rest

/-- Constructive (`0 Classical.choice`) Merkle collision extractor along two equal-length paths. -/
def merklePathCollision (H : Hash) :
    ∀ (p1 p2 : List (List UInt8)) (n1 n2 : List UInt8) (idx : Nat),
      p1.length = p2.length → n1 ≠ n2 →
      merklePathRoot H n1 idx p1 = merklePathRoot H n2 idx p2 → HashCollisionWitness H
  | [], [], _, _, _, _, hne, hroot => False.elim (hne hroot)
  | [], _ :: _, _, _, _, hlen, _, _ => False.elim (Nat.succ_ne_zero _ hlen.symm)
  | _ :: _, [], _, _, _, hlen, _, _ => False.elim (Nat.succ_ne_zero _ hlen)
  | s1 :: r1, s2 :: r2, n1, n2, idx, hlen, hne, hroot =>
    if hH : H (merkleNodeFrame idx n1 s1) = H (merkleNodeFrame idx n2 s2) then
      ⟨merkleNodeFrame idx n1 s1, merkleNodeFrame idx n2 s2,
        fun h => hne (merkleNodeFrame_node_injective h), hH⟩
    else
      merklePathCollision H r1 r2 _ _ (idx / 2) (Nat.succ.inj hlen) hH hroot

/-- Stage-and-layer domain-separated leaf preimage of coset duet `(v0, v1)` over `GoldilocksExt4`. -/
def duetLeafFrame (stageIdx layer g : Nat) (v0 v1 : GoldilocksExt4) : List UInt8 :=
  encodeMultiFrame [(toString stageIdx).toUTF8.toList, (toString layer).toUTF8.toList,
    (toString g).toUTF8.toList, GoldilocksExt4.encodeBytes32 v0, GoldilocksExt4.encodeBytes32 v1]

theorem duetLeafFrame_injective {stageIdx layer g : Nat} {v0 v1 t0 t1 : GoldilocksExt4}
    (h : duetLeafFrame stageIdx layer g v0 v1 = duetLeafFrame stageIdx layer g t0 t1) :
    v0 = t0 ∧ v1 = t1 := by
  have h1 := (List.cons.inj (encodeMultiFrame_injective h)).2
  have h2 := (List.cons.inj h1).2
  have h3 := (List.cons.inj h2).2
  have h4 := List.cons.inj h3
  exact ⟨GoldilocksExt4.encodeBytes32_injective h4.1,
    GoldilocksExt4.encodeBytes32_injective (List.cons.inj h4.2).1⟩

def duetOpeningCollision (stageIdx layer g : Nat) (v0 v1 t0 t1 : GoldilocksExt4)
    (p1 p2 : List (List UInt8)) (root : List UInt8)
    (hne : ¬ (v0 = t0 ∧ v1 = t1)) (hlen : p1.length = p2.length)
    (h1 : merklePathRoot pcsMerkleHash (pcsMerkleHash (duetLeafFrame stageIdx layer g v0 v1)) g p1 = root)
    (h2 : merklePathRoot pcsMerkleHash (pcsMerkleHash (duetLeafFrame stageIdx layer g t0 t1)) g p2 = root) :
    HashCollisionWitness pcsMerkleHash :=
  if hH : pcsMerkleHash (duetLeafFrame stageIdx layer g v0 v1) =
      pcsMerkleHash (duetLeafFrame stageIdx layer g t0 t1) then
    ⟨duetLeafFrame stageIdx layer g v0 v1, duetLeafFrame stageIdx layer g t0 t1,
      fun h => hne (duetLeafFrame_injective h), hH⟩
  else
    merklePathCollision pcsMerkleHash p1 p2 _ _ g hlen hH (h1.trans h2.symm)

def merkleDepthFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n ≤ 1 then 0 else merkleDepthFuel fuel (n / 2) + 1

def merkleDepth (n : Nat) : Nat := merkleDepthFuel n n

/-- Kernel-reducible witness seed `"WHIR_STAGE_POW"` (`pcs.rs` stage PoW transcript label)
    avoiding `@[extern] String.toUTF8` during kernel reduction of 16-bit PoW KAT proofs. -/
def powWitnessSeed : List UInt8 :=
  [0x57, 0x48, 0x49, 0x52, 0x5f, 0x53, 0x54, 0x41, 0x47, 0x45, 0x5f, 0x50, 0x4f, 0x57]

/-- The low `w` bytes of `n` in little-endian order (`u64::to_le_bytes` at `w = 8`). -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: leBytes w (n / 256)

/-- Little-endian byte list decoded as a natural number (`u64::from_le_bytes` on 8 bytes). -/
def ofLeBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * ofLeBytes bs

@[simp] theorem length_leBytes (w n : Nat) : (leBytes w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [leBytes, ih]

theorem ofLeBytes_leBytes (w n : Nat) : ofLeBytes (leBytes w n) = n % 256 ^ w := by
  induction w generalizing n with
  | zero => simp only [leBytes, ofLeBytes, Nat.pow_zero, Nat.mod_one]
  | succ w ih =>
    have hb : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      rw [UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    rw [leBytes, ofLeBytes, ih, hb, Nat.pow_succ, Nat.mul_comm (256 ^ w) 256]
    let p := 256 ^ w
    have hpPos : 0 < p := Nat.pow_pos (by decide : 0 < 256)
    have hr0 : n % 256 < 256 := Nat.mod_lt n (by decide)
    have hr1 : (n / 256) % p < p := Nat.mod_lt (n / 256) hpPos
    have hBound : n % 256 + 256 * ((n / 256) % p) < 256 * p := by
      have h1 : (n / 256) % p + 1 ≤ p := hr1
      have h2 := Nat.mul_le_mul_left 256 h1
      omega
    have hDecomp : n = (n % 256 + 256 * ((n / 256) % p)) + (256 * p) * ((n / 256) / p) := by
      have e0 := (Nat.div_add_mod n 256).symm
      have e1 := (Nat.div_add_mod (n / 256) p).symm
      calc
        n = 256 * (n / 256) + n % 256 := e0
        _ = 256 * (p * ((n / 256) / p) + (n / 256) % p) + n % 256 := by rw [← e1]
        _ = (n % 256 + 256 * ((n / 256) % p)) + (256 * p) * ((n / 256) / p) := by
          rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_comm _ (n % 256), Nat.add_assoc,
              Nat.add_comm (256 * ((n / 256) % p))]
    conv => rhs; rw [hDecomp]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hBound]

/-- Customization string `"QSAG.PCS.POW2/v1"` of the deployed per-stage grinding hash (`POW_CUSTOM`
    in `crates/qsag-agg/src/sponge.rs`, whose `cSHAKE256` midstate is `POW_MIDSTATE`), written as
    kernel-reducible UTF-8 bytes so `decide +kernel` reduces `verifyWhirStagePow` directly. -/
def whirPowCustomization : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x43, 0x53, 0x2e, 0x50, 0x4f, 0x57, 0x32, 0x2f, 0x76, 0x31]

/-- The 64-bit grinding word of `cshake256_pow_u64_single` (`sponge.rs`): `cSHAKE256` under
    `whirPowCustomization` of the 40-byte buffer `chal ++ nonce.to_le_bytes()`, with the first
    eight output bytes read as a little-endian `u64`. -/
def whirPowWord (chal : List UInt8) (powNonce : Nat) : Nat :=
  ofLeBytes ((cshake256Bytes whirPowCustomization (chal ++ leBytes 8 powNonce)).take 8)

/-- The low-bit predicate of the production extracted PoW gate. The production mask
supports at most 32 bits; hash selection and the zero-PoW nonce rule are separate. -/
def whirStagePowMask (word powBits : Nat) : Bool :=
  decide (powBits ≤ 32 ∧ word % 2 ^ powBits = 0)

/-- **Per-Stage WHIR Proof-of-Work (`verifyWhirStagePow`)**, the function of `verify_pcs_pow` in
    `crates/qsag-agg/src/pcs.rs`: require nonce zero when `powBits = 0`; otherwise the challenge must be a
    32-byte digest, the nonce a `u64`, and the low `powBits` bits of `whirPowWord chal powNonce`
    must all be zero (`word & ((1 << powBits) - 1) == 0`).

    Only this function is the deployed one. The 32-byte challenge the deployed verifier feeds it
    is the running digest of its Fiat–Shamir transcript, which this module does not model;
    `verifyOneWhirStage` feeds it `stagePowDigest` of this module's own transcript frame. -/
def verifyWhirStagePow (chal : List UInt8) (powNonce powBits : Nat) : Bool :=
  if powBits = 0 then decide (powNonce = 0)
  else if chal.length = 32 ∧ powNonce < 2 ^ 64 then
    whirStagePowMask (whirPowWord chal powNonce) powBits
  else false

/-- Kernel-reducible UTF-8 bytes of `"QSAG.AGG.FS_TRANSCRIPT/v1"` (`sponge.rs`). -/
def tagStagePowDigest : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x41, 0x47, 0x47, 0x2e, 0x46, 0x53, 0x5f, 0x54, 0x52,
   0x41, 0x4e, 0x53, 0x43, 0x52, 0x49, 0x50, 0x54, 0x2f, 0x76, 0x31]

/-- 32-byte digest of this module's stage transcript frame, the challenge handed to
    `verifyWhirStagePow`. -/
def stagePowDigest (seed : List UInt8) : List UInt8 :=
  cshake256Bytes tagStagePowDigest seed

@[simp] theorem stagePowDigest_length (seed : List UInt8) : (stagePowDigest seed).length = 32 :=
  cshake256Bytes_length _ _

/-- At `powBits = 16` acceptance is exactly "the first two digest bytes are zero", for every
    32-byte challenge and `u64` nonce. -/
theorem verifyWhirStagePow_16_iff (chal : List UInt8) (powNonce : Nat)
    (hLen : chal.length = 32) (hNonce : powNonce < 2 ^ 64) :
    verifyWhirStagePow chal powNonce 16 = true ↔
      ((cshake256Bytes whirPowCustomization (chal ++ leBytes 8 powNonce)).take 2).all
        (· == 0) = true := by
  have hGuard : (chal.length = 32 ∧ powNonce < 2 ^ 64) := ⟨hLen, hNonce⟩
  unfold verifyWhirStagePow whirStagePowMask whirPowWord
  have h16 : ¬ ((16 : Nat) = 0) := by decide
  rw [ite_eq_right_of_eq_false _ _ (eq_false h16), ite_eq_left_of_eq_true _ _ (eq_true hGuard),
    decide_eq_true_iff]
  simp only [show (16 : Nat) ≤ 32 from by decide, true_and]
  have hDigLen := cshake256Bytes_length whirPowCustomization (chal ++ leBytes 8 powNonce)
  generalize cshake256Bytes whirPowCustomization (chal ++ leBytes 8 powNonce) = dig at hDigLen ⊢
  rcases dig with _ | ⟨b0, _ | ⟨b1, rest⟩⟩
  · simp at hDigLen
  · simp at hDigLen
  · show ofLeBytes (b0 :: b1 :: rest.take 6) % 2 ^ 16 = 0 ↔ [b0, b1].all (· == 0) = true
    have h0 := b0.toNat_lt
    have h1 := b1.toNat_lt
    simp only [ofLeBytes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      beq_iff_eq]
    generalize ofLeBytes (rest.take 6) = r
    constructor
    · intro h
      have hb0 : b0.toNat = 0 := by omega
      have hb1 : b1.toNat = 0 := by omega
      exact ⟨UInt8.toNat_inj.mp (hb0.trans UInt8.toNat_zero.symm),
        UInt8.toNat_inj.mp (hb1.trans UInt8.toNat_zero.symm)⟩
    · rintro ⟨hb0, hb1⟩
      rw [hb0, hb1, UInt8.toNat_zero]
      omega

/-- `#tooth`: a challenge that is not a 32-byte digest is rejected at every positive difficulty,
    as is a nonce outside `u64`. -/
theorem tooth_whir_pow_rejects_malformed_inputs (chal : List UInt8) (powNonce powBits : Nat)
    (hBits : powBits ≠ 0) (hBad : chal.length ≠ 32 ∨ 2 ^ 64 ≤ powNonce) :
    verifyWhirStagePow chal powNonce powBits = false := by
  unfold verifyWhirStagePow
  rw [ite_eq_right_of_eq_false _ _ (eq_false hBits)]
  apply ite_eq_right_of_eq_false
  apply eq_false
  rintro ⟨hLen, hNonce⟩
  rcases hBad with h | h
  · exact h hLen
  · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hNonce h)

/-- Public domain parameters of a single WHIR rate-escalation stage `s`.
    When `bindRowChallenges = true`, intra-stage coset folding evaluates directly at the
    Fiat–Shamir row-sumcheck challenges (committed after `stageRoot` and `roundPolys`), while
    `shiftPolys` still run against fresh `shiftChallenges`. -/
structure WhirStageDomain where
  stageIdx : Nat
  blowup : Nat
  groups0 : Nat
  foldLayers : Nat
  numQueries : Nat
  powBits : Nat
  invTwo : Goldilocks
  invTwoY0 : Nat → Nat → Goldilocks
  sampleFuel : Nat
  bindRowChallenges : Bool := false

/-- Public multi-stage WHIR domain schedule. -/
structure WhirDomain where
  stages : List WhirStageDomain

structure FoldLayerOpening where
  v0 : GoldilocksExt4
  v1 : GoldilocksExt4
  path : List (List UInt8)

/-- Authenticated coset fiber opening for one stage query: `layers` walks the intra-stage fold
    tree, and `nextStageBridge` authenticates the resulting folded value directly against the
    next WHIR stage's Merkle root (`none` on the final stage, which checks `finalWord`). -/
structure StageQueryOpening where
  index : Nat
  layers : List FoldLayerOpening
  nextStageBridge : Option FoldLayerOpening := none

/-- Number of out-of-domain samples squeezed per WHIR stage (`pcs.rs::OOD_SAMPLES = 2`). -/
def whirOodSamples : Nat := 2

/-- Proof transcript data for one WHIR stage `s`:
    `stageRoot` -> squeeze dual `oodChallenges` (`OOD_SAMPLES = 2`) -> absorb dual `oodEvals` ->
    interleaved degree-2 shift/OOD sumcheck (`shiftPolys`, `layerRoots`, `shiftChallenges`) ->
    `powNonce` -> `queries`. -/
structure WhirStageProof where
  stageRoot : List UInt8
  oodChallenges : GoldilocksExt4 × GoldilocksExt4
  oodEvals : GoldilocksExt4 × GoldilocksExt4
  shiftClaim : GoldilocksExt4
  shiftPolys : List (List GoldilocksExt4)
  layerRoots : List (List UInt8)
  shiftChallenges : List GoldilocksExt4
  foldChallenges : List GoldilocksExt4
  shiftTerminalEval : GoldilocksExt4
  powNonce : Nat
  queries : List StageQueryOpening

/-- First Fiat–Shamir OOD sample of a stage (`OOD_SAMPLES = 2`). -/
def WhirStageProof.oodChallenge (sp : WhirStageProof) : GoldilocksExt4 :=
  sp.oodChallenges.1

/-- Second Fiat–Shamir OOD sample of a stage (`OOD_SAMPLES = 2`). -/
def WhirStageProof.oodChallenge2 (sp : WhirStageProof) : GoldilocksExt4 :=
  sp.oodChallenges.2

/-- First OOD evaluation of a stage (`OOD_SAMPLES = 2`). -/
def WhirStageProof.oodEval (sp : WhirStageProof) : GoldilocksExt4 :=
  sp.oodEvals.1

/-- Second OOD evaluation of a stage (`OOD_SAMPLES = 2`). -/
def WhirStageProof.oodEval2 (sp : WhirStageProof) : GoldilocksExt4 :=
  sp.oodEvals.2

/-- Complete succinct `GoldilocksExt4` WHIR aggregate certificate: zero `PqHashSig` lists. -/
structure SuccinctAggregateProof where
  agg : AggregatedSignature
  stages : List WhirStageProof
  finalWord : List GoldilocksExt4

def stageAllRoots (sp : WhirStageProof) : List (List UInt8) :=
  sp.stageRoot :: sp.layerRoots

/-- Squeeze the `OOD_SAMPLES = 2` Fiat–Shamir OOD points `(z_ood_0, z_ood_1)` after absorbing
    `stageRoot` (`"WHIR_OOD_CHAL"` in `pcs.rs`). -/
def deriveStageOodChallenges (prior : List UInt8) (stageRoot : List UInt8) :
    GoldilocksExt4 × GoldilocksExt4 :=
  let frame0 := encodeMultiFrame [prior, stageRoot]
  let z0 := squeezeExt4Challenge "WHIR_OOD_CHAL".toUTF8.toList frame0
  let frame1 := encodeMultiFrame [frame0, GoldilocksExt4.encodeBytes32 z0]
  let z1 := squeezeExt4Challenge "WHIR_OOD_CHAL".toUTF8.toList frame1
  (z0, z1)

/-- First Fiat–Shamir OOD point `z_ood_0` of `deriveStageOodChallenges`. -/
def deriveStageOodChallenge (prior : List UInt8) (stageRoot : List UInt8) : GoldilocksExt4 :=
  (deriveStageOodChallenges prior stageRoot).1

/-- Transcript state after absorbing `stageRoot`, both `OOD_SAMPLES = 2` evaluations `oodEvals`,
    and `shiftClaim`. -/
def stagePostOodTranscript (prior : List UInt8) (sp : WhirStageProof) : List UInt8 :=
  encodeMultiFrame [prior, sp.stageRoot,
    GoldilocksExt4.encodeBytes32 sp.oodEvals.1,
    GoldilocksExt4.encodeBytes32 sp.oodEvals.2,
    GoldilocksExt4.encodeBytes32 sp.shiftClaim]

/-- Interleaved per-stage shift/fold challenge derivation (`[stageRoot] ++ layerRoots` paired with
    `shiftPolys`). -/
def deriveStageShiftChallenges (prior : List UInt8) :
    List (List UInt8) → List (List GoldilocksExt4) → List GoldilocksExt4
  | root :: roots, p :: ps =>
    let frame := encodeMultiFrame [prior, root, encodePolyExt4 p]
    let α := squeezeExt4Challenge "WHIR_AFFINE_ALPHA".toUTF8.toList frame
    α :: deriveStageShiftChallenges frame roots ps
  | _, _ => []

def stageFoldTranscriptTail (prior : List UInt8) :
    List (List UInt8) → List (List GoldilocksExt4) → List UInt8
  | root :: roots, p :: ps =>
    stageFoldTranscriptTail (encodeMultiFrame [prior, root, encodePolyExt4 p]) roots ps
  | _, _ => prior

/-- Transcript frame whose `stagePowDigest` feeds `verifyWhirStagePow` for stage `sp`
    (incorporates `finalWord` if final stage). -/
def stagePowSeed (prior : List UInt8) (sp : WhirStageProof)
    (nextRoot? : Option (List UInt8)) (finalWord : List GoldilocksExt4) : List UInt8 :=
  let foldTail := stageFoldTranscriptTail (stagePostOodTranscript prior sp)
    (stageAllRoots sp) sp.shiftPolys
  match nextRoot? with
  | some nextRoot => encodeMultiFrame [foldTail, nextRoot]
  | none => encodeMultiFrame [foldTail, encodePolyExt4 finalWord]

/-- Query-sampling seed after binding `powNonce`. -/
def stageQuerySeed (powSeed : List UInt8) (powNonce : Nat) : List UInt8 :=
  encodeMultiFrame [powSeed, be 8 powNonce]

def sortedInsertDistinct (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys else if x = y then y :: ys else y :: sortedInsertDistinct x ys

def sampleDistinctLoop (cand : Nat → Nat) (target : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, k, acc =>
    if target ≤ acc.length then acc
    else sampleDistinctLoop cand target fuel (k + 1) (sortedInsertDistinct (cand k) acc)

def scanFillDistinct (target : Nat) : List Nat → List Nat → List Nat
  | [], acc => acc
  | x :: xs, acc =>
    if target ≤ acc.length then acc
    else scanFillDistinct target xs (sortedInsertDistinct x acc)

def squeezeQueryIndex (seed : List UInt8) (groups k : Nat) : Nat :=
  ofBE ((cshake256Bytes "WHIR_QUERIES_S00".toUTF8.toList
    (encodeMultiFrame [seed, (toString k).toUTF8.toList])).take 8) % groups

def deriveStageQueryIndices (sdom : WhirStageDomain) (qSeed : List UInt8) : List Nat :=
  let target := min sdom.numQueries sdom.groups0
  let sampled := sampleDistinctLoop (squeezeQueryIndex qSeed sdom.groups0)
    target sdom.sampleFuel 0 []
  scanFillDistinct target (List.range sdom.groups0) sampled

def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: ys => decide (x < y) && strictlyIncreasing (y :: ys)

theorem strictlyIncreasing_head_lt :
    ∀ (l : List Nat) (x : Nat), strictlyIncreasing (x :: l) = true → ∀ y ∈ l, x < y
  | [], _, _, _, hy => by cases hy
  | z :: zs, x, h, y, hy => by
    have h' := Bool.and_eq_true_iff.mp h
    have hxz : x < z := of_decide_eq_true h'.1
    rcases List.mem_cons.mp hy with e | e
    · rw [e]; exact hxz
    · exact Nat.lt_trans hxz (strictlyIncreasing_head_lt zs z h'.2 y e)

theorem strictlyIncreasing_nodup : ∀ (l : List Nat), strictlyIncreasing l = true → l.Nodup
  | [], _ => List.Pairwise.nil
  | x :: l, h => by
    have htail : strictlyIncreasing l = true := by
      cases l with
      | nil => rfl
      | cons z zs => exact (Bool.and_eq_true_iff.mp h).2
    exact List.nodup_cons.mpr
      ⟨fun hm => Nat.lt_irrefl x (strictlyIncreasing_head_lt l x h x hm),
        strictlyIncreasing_nodup l htail⟩

theorem mem_sortedInsertDistinct {x z : Nat} :
    ∀ {l : List Nat}, z ∈ sortedInsertDistinct x l → z = x ∨ z ∈ l
  | [], h => .inl (List.mem_singleton.mp h)
  | y :: ys, h => by
    simp only [sortedInsertDistinct] at h
    if hlt : x < y then
      simp only [hlt, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | rfl | hm
      · exact .inl rfl
      · exact .inr (.head _)
      · exact .inr (.tail _ hm)
    else if heq : x = y then
      subst heq
      simp only [Nat.lt_irrefl, ↓reduceIte] at h
      exact .inr h
    else
      simp only [hlt, heq, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | hm
      · exact .inr (.head _)
      · rcases mem_sortedInsertDistinct hm with rfl | hm'
        · exact .inl rfl
        · exact .inr (.tail _ hm')

theorem strictlyIncreasing_sortedInsertDistinct (x : Nat) :
    ∀ (l : List Nat), strictlyIncreasing l = true →
      strictlyIncreasing (sortedInsertDistinct x l) = true
  | [], _ => rfl
  | y :: ys, h => by
    simp only [sortedInsertDistinct]
    if hlt : x < y then
      simp only [hlt, ↓reduceIte, strictlyIncreasing, decide_true, Bool.true_and]
      exact h
    else if heq : x = y then
      subst heq
      simp only [Nat.lt_irrefl, ↓reduceIte]
      exact h
    else
      have hyx : y < x := by omega
      simp only [hlt, heq, ↓reduceIte]
      have hTail : strictlyIncreasing ys = true := by
        cases ys with
        | nil => rfl
        | cons z zs => exact (Bool.and_eq_true_iff.mp h).2
      have ih := strictlyIncreasing_sortedInsertDistinct x ys hTail
      cases hIns : sortedInsertDistinct x ys with
      | nil => rfl
      | cons w ws =>
        rw [hIns] at ih
        have hwMem : w ∈ sortedInsertDistinct x ys := by rw [hIns]; exact .head _
        have hyw : y < w := by
          rcases mem_sortedInsertDistinct hwMem with rfl | hm
          · exact hyx
          · exact strictlyIncreasing_head_lt ys y h w hm
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hyw, ih⟩

theorem strictlyIncreasing_sampleDistinctLoop (cand : Nat → Nat) (target : Nat) :
    ∀ (fuel k : Nat) (acc : List Nat),
      strictlyIncreasing acc = true →
      strictlyIncreasing (sampleDistinctLoop cand target fuel k acc) = true
  | 0, _, _, hAcc => hAcc
  | fuel + 1, k, acc, hAcc => by
    simp only [sampleDistinctLoop]
    split
    · exact hAcc
    · exact strictlyIncreasing_sampleDistinctLoop cand target fuel (k + 1)
        (sortedInsertDistinct (cand k) acc)
        (strictlyIncreasing_sortedInsertDistinct (cand k) acc hAcc)

theorem mem_sampleDistinctLoop_lt {cand : Nat → Nat} {bound : Nat}
    (hCand : ∀ k, cand k < bound) (target : Nat) :
    ∀ (fuel k : Nat) (acc : List Nat),
      (∀ y ∈ acc, y < bound) →
      ∀ z ∈ sampleDistinctLoop cand target fuel k acc, z < bound
  | 0, _, _, hAcc, z, hz => hAcc z hz
  | fuel + 1, k, acc, hAcc, z, hz => by
    simp only [sampleDistinctLoop] at hz
    split at hz
    · exact hAcc z hz
    · exact mem_sampleDistinctLoop_lt hCand target fuel (k + 1)
        (sortedInsertDistinct (cand k) acc)
        (fun w hw => by
          rcases mem_sortedInsertDistinct hw with rfl | hm
          · exact hCand k
          · exact hAcc w hm) z hz

theorem length_sortedInsertDistinct_of_not_mem (x : Nat) :
    ∀ (l : List Nat), x ∉ l → (sortedInsertDistinct x l).length = l.length + 1
  | [], _ => rfl
  | y :: ys, hNot => by
    simp only [sortedInsertDistinct]
    if hlt : x < y then
      simp [hlt]
    else if heq : x = y then
      exact False.elim (hNot (heq ▸ .head _))
    else
      simp only [hlt, heq, ↓reduceIte, List.length_cons]
      have hNotYs : x ∉ ys := fun hm => hNot (.tail _ hm)
      rw [length_sortedInsertDistinct_of_not_mem x ys hNotYs]

theorem mem_sortedInsertDistinct_iff {x z : Nat} {l : List Nat} :
    z ∈ sortedInsertDistinct x l ↔ z = x ∨ z ∈ l := by
  constructor
  · exact mem_sortedInsertDistinct
  · intro h
    induction l with
    | nil =>
      rcases h with rfl | hm
      · exact .head _
      · cases hm
    | cons y ys ih =>
      simp only [sortedInsertDistinct]
      if hlt : x < y then
        simp only [hlt, ↓reduceIte, List.mem_cons]
        rcases h with rfl | hm
        · exact .inl rfl
        · exact .inr (List.mem_cons.mp hm)
      else if heq : x = y then
        subst heq
        simp only [Nat.lt_irrefl, ↓reduceIte]
        rcases h with rfl | hm
        · exact .head _
        · exact hm
      else
        simp only [hlt, heq, ↓reduceIte, List.mem_cons]
        rcases h with rfl | hm
        · exact .inr (ih (.inl rfl))
        · rcases List.mem_cons.mp hm with rfl | hms
          · exact .inl rfl
          · exact .inr (ih (.inr hms))

theorem length_sortedInsertDistinct_le (x : Nat) :
    ∀ (l : List Nat), (sortedInsertDistinct x l).length ≤ l.length + 1
  | [] => Nat.le_refl 1
  | y :: ys => by
    simp only [sortedInsertDistinct]
    if hlt : x < y then
      simp [hlt]
    else if heq : x = y then
      subst heq
      simp only [Nat.lt_irrefl, ↓reduceIte]
      omega
    else
      simp only [hlt, heq, ↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ (length_sortedInsertDistinct_le x ys)

theorem length_sortedInsertDistinct_of_mem (x : Nat) :
    ∀ (l : List Nat), strictlyIncreasing l = true → x ∈ l →
      (sortedInsertDistinct x l).length = l.length
  | [], _, hMem => by cases hMem
  | y :: ys, hInc, hMem => by
    simp only [sortedInsertDistinct]
    if hlt : x < y then
      exfalso
      rcases List.mem_cons.mp hMem with rfl | hm
      · exact Nat.lt_irrefl _ hlt
      · exact Nat.lt_asymm hlt (strictlyIncreasing_head_lt ys y hInc x hm)
    else if heq : x = y then
      subst heq
      simp only [Nat.lt_irrefl, ↓reduceIte]
    else
      have hTail : strictlyIncreasing ys = true := by
        cases ys with
        | nil => rfl
        | cons z zs => exact (Bool.and_eq_true_iff.mp hInc).2
      have hmYs : x ∈ ys := by
        rcases List.mem_cons.mp hMem with rfl | hm
        · exact False.elim (heq rfl)
        · exact hm
      simp only [hlt, heq, ↓reduceIte, List.length_cons]
      exact congrArg Nat.succ (length_sortedInsertDistinct_of_mem x ys hTail hmYs)

theorem length_sampleDistinctLoop_le (cand : Nat → Nat) (target : Nat) :
    ∀ (fuel k : Nat) (acc : List Nat),
      acc.length ≤ target →
      (sampleDistinctLoop cand target fuel k acc).length ≤ target
  | 0, _, _, hLe => hLe
  | fuel + 1, k, acc, hLe => by
    simp only [sampleDistinctLoop]
    if hT : target ≤ acc.length then
      simp [hT, hLe]
    else
      simp only [hT, ↓reduceIte]
      have hIns := length_sortedInsertDistinct_le (cand k) acc
      exact length_sampleDistinctLoop_le cand target fuel (k + 1) _ (by omega)

theorem strictlyIncreasing_scanFillDistinct (target : Nat) :
    ∀ (xs acc : List Nat),
      strictlyIncreasing acc = true →
      strictlyIncreasing (scanFillDistinct target xs acc) = true
  | [], _, hAcc => hAcc
  | x :: xs, acc, hAcc => by
    simp only [scanFillDistinct]
    split
    · exact hAcc
    · exact strictlyIncreasing_scanFillDistinct target xs _
        (strictlyIncreasing_sortedInsertDistinct x acc hAcc)

theorem mem_scanFillDistinct_lt {bound : Nat} (target : Nat) :
    ∀ (xs acc : List Nat),
      (∀ y ∈ xs, y < bound) →
      (∀ y ∈ acc, y < bound) →
      ∀ z ∈ scanFillDistinct target xs acc, z < bound
  | [], acc, _, hAcc, z, hz => hAcc z hz
  | x :: xs, acc, hXs, hAcc, z, hz => by
    simp only [scanFillDistinct] at hz
    split at hz
    · exact hAcc z hz
    · exact mem_scanFillDistinct_lt target xs _
        (fun y hy => hXs y (.tail _ hy))
        (fun w hw => by
          rcases mem_sortedInsertDistinct hw with hEq | hm
          · rw [hEq]; exact hXs x (.head _)
          · exact hAcc w hm) z hz

private theorem filter_ne_length_lt_of_mem (x : Nat) :
    ∀ (acc : List Nat), x ∈ acc → (acc.filter (fun z => decide (z ≠ x))).length < acc.length
  | [], hm => by cases hm
  | a :: as, hm => by
    rcases List.mem_cons.mp hm with hEq | hms
    · subst hEq
      simp only [List.filter, ne_eq, not_true_eq_false, decide_false, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ as)
    · have ih := filter_ne_length_lt_of_mem x as hms
      cases hd : decide (a ≠ x) <;> simp only [List.filter, hd, List.length_cons] <;> omega

private theorem nodup_length_le_missing_add_acc :
    ∀ (xs : List Nat), xs.Nodup →
      ∀ (acc : List Nat),
        xs.length ≤ (xs.filter (fun z => decide (z ∉ acc))).length + acc.length
  | [], _, _ => Nat.zero_le _
  | x :: xs, hNd, acc => by
    obtain ⟨hxNot, hNdXs⟩ := List.nodup_cons.mp hNd
    if hxAcc : x ∈ acc then
      let acc0 := acc.filter (fun z => decide (z ≠ x))
      have hLt : acc0.length < acc.length := filter_ne_length_lt_of_mem x acc hxAcc
      have hFiltEq : xs.filter (fun z => decide (z ∉ acc0)) =
          xs.filter (fun z => decide (z ∉ acc)) := by
        apply List.filter_congr
        intro z hz
        have hzx : z ≠ x := fun hEq => hxNot (hEq ▸ hz)
        by_cases hzAcc : z ∈ acc
        · have hzAcc0 : z ∈ acc0 := List.mem_filter.mpr ⟨hzAcc, decide_eq_true hzx⟩
          simp [hzAcc, hzAcc0]
        · have hzNot0 : z ∉ acc0 := fun hm => hzAcc (List.mem_filter.mp hm).1
          simp [hzAcc, hzNot0]
      have ih := nodup_length_le_missing_add_acc xs hNdXs acc0
      rw [hFiltEq] at ih
      simp only [List.filter, hxAcc, not_true_eq_false, decide_false, List.length_cons]
      omega
    else
      have ih := nodup_length_le_missing_add_acc xs hNdXs acc
      simp only [List.filter, hxAcc, not_false_eq_true, decide_true, List.length_cons]
      omega

theorem length_scanFillDistinct (target : Nat) :
    ∀ (xs acc : List Nat),
      strictlyIncreasing acc = true →
      xs.Nodup →
      acc.length ≤ target →
      target ≤ (xs.filter (fun z => decide (z ∉ acc))).length + acc.length →
      (scanFillDistinct target xs acc).length = target
  | [], acc, _, _, hLe, hGe => by
    simp only [scanFillDistinct, List.filter, List.length_nil, Nat.zero_add] at hGe ⊢
    omega
  | x :: xs, acc, hInc, hNd, hLe, hGe => by
    simp only [scanFillDistinct]
    if hT : target ≤ acc.length then
      simp only [hT, ↓reduceIte]
      omega
    else
      simp only [hT, ↓reduceIte]
      obtain ⟨hxNot, hNdXs⟩ := List.nodup_cons.mp hNd
      let acc' := sortedInsertDistinct x acc
      have hInc' : strictlyIncreasing acc' = true :=
        strictlyIncreasing_sortedInsertDistinct x acc hInc
      have hFiltEq : xs.filter (fun z => decide (z ∉ acc')) =
          xs.filter (fun z => decide (z ∉ acc)) := by
        apply List.filter_congr
        intro z hz
        have hzx : z ≠ x := fun hEq => hxNot (hEq ▸ hz)
        by_cases hzAcc : z ∈ acc
        · have hzAcc' : z ∈ acc' := mem_sortedInsertDistinct_iff.mpr (.inr hzAcc)
          simp [hzAcc, hzAcc']
        · have hzNot' : z ∉ acc' := fun hm => by
            rcases mem_sortedInsertDistinct_iff.mp hm with hEq | hmAcc
            · exact hzx hEq
            · exact hzAcc hmAcc
          simp [hzAcc, hzNot']
      if hxAcc : x ∈ acc then
        have hLenEq : acc'.length = acc.length :=
          length_sortedInsertDistinct_of_mem x acc hInc hxAcc
        simp only [List.filter, hxAcc, not_true_eq_false, decide_false] at hGe
        exact length_scanFillDistinct target xs acc' hInc' hNdXs
          (by omega) (by rw [hFiltEq, hLenEq]; exact hGe)
      else
        have hLenSucc : acc'.length = acc.length + 1 :=
          length_sortedInsertDistinct_of_not_mem x acc hxAcc
        simp only [List.filter, hxAcc, not_false_eq_true, decide_true, List.length_cons] at hGe
        exact length_scanFillDistinct target xs acc' hInc' hNdXs
          (by omega) (by rw [hFiltEq, hLenSucc]; omega)

private theorem pairwise_snoc {α : Type} {R : α → α → Prop} {l : List α} {a : α}
    (hl : List.Pairwise R l) (ha : ∀ x ∈ l, R x a) : List.Pairwise R (l ++ [a]) := by
  induction hl with
  | nil => exact .cons (fun _ h => nomatch h) .nil
  | cons hhd _ ih =>
    exact .cons
      (fun y hy => match List.mem_append.mp hy with
        | .inl hyl => hhd y hyl
        | .inr hya => List.mem_singleton.mp hya ▸ ha _ (.head _))
      (ih (fun x hx => ha x (.tail _ hx)))

private theorem nodup_range_constructive : ∀ (n : Nat), (List.range n).Nodup
  | 0 => .nil
  | n + 1 => by
    rw [List.range_succ]
    exact pairwise_snoc (nodup_range_constructive n)
      (fun x hx hEq => Nat.ne_of_lt (List.mem_range.mp hx) hEq)

theorem deriveStageQueryIndices_props (sdom : WhirStageDomain) (qSeed : List UInt8)
    (hGroups : 0 < sdom.groups0) :
    let qs := deriveStageQueryIndices sdom qSeed
    strictlyIncreasing qs = true ∧
    qs.length = min sdom.numQueries sdom.groups0 ∧
    (∀ z ∈ qs, z < sdom.groups0) := by
  dsimp only [deriveStageQueryIndices]
  let target := min sdom.numQueries sdom.groups0
  let sampled := sampleDistinctLoop (squeezeQueryIndex qSeed sdom.groups0)
    target sdom.sampleFuel 0 []
  have hIncS : strictlyIncreasing sampled = true :=
    strictlyIncreasing_sampleDistinctLoop _ target sdom.sampleFuel 0 [] rfl
  have hLtS : ∀ y ∈ sampled, y < sdom.groups0 :=
    mem_sampleDistinctLoop_lt (fun k => Nat.mod_lt _ hGroups) target sdom.sampleFuel 0 []
      (fun _ hm => by cases hm)
  have hLenS : sampled.length ≤ target :=
    length_sampleDistinctLoop_le _ target sdom.sampleFuel 0 [] (Nat.zero_le _)
  have hNdRange := nodup_range_constructive sdom.groups0
  have hRange := nodup_length_le_missing_add_acc (List.range sdom.groups0) hNdRange sampled
  rw [List.length_range] at hRange
  have hTargetLe : target ≤ sdom.groups0 := Nat.min_le_right _ _
  refine ⟨strictlyIncreasing_scanFillDistinct target _ sampled hIncS,
    length_scanFillDistinct target _ sampled hIncS hNdRange hLenS (by omega),
    mem_scanFillDistinct_lt target _ sampled (fun _ hy => List.mem_range.mp hy) hLtS⟩

def expectedSlotOk (expected : Option GoldilocksExt4) (slot : Nat)
    (v0 v1 : GoldilocksExt4) : Bool :=
  match expected with
  | none => true
  | some e => decide ((if slot = 0 then v0 else v1) = e)

def finalValueOk (finalWord : List GoldilocksExt4) (idx : Nat)
    (expected : Option GoldilocksExt4) : Bool :=
  match expected with
  | none => false
  | some e => decide (finalWord[idx]? = some e)

/-- Verify a stage's terminal value: against `nextStageRoot` via `bridgeOp` if an intermediate
    WHIR stage, or against `finalWord` if the final WHIR stage. -/
def verifyStageTerminalTarget (nextStageInfo : Option (WhirStageDomain × List UInt8))
    (finalWord : List GoldilocksExt4) (idx : Nat) (expected : Option GoldilocksExt4)
    (bridgeOp : Option FoldLayerOpening) : Bool :=
  match nextStageInfo, bridgeOp with
  | none, none => finalValueOk finalWord idx expected
  | some (nextDom, nextRoot), some br =>
    decide (0 < nextDom.groups0) &&
    expectedSlotOk expected (idx / nextDom.groups0) br.v0 br.v1 &&
    decide (br.path.length = merkleDepth nextDom.groups0) &&
    decide (merklePathRoot pcsMerkleHash
      (pcsMerkleHash (duetLeafFrame nextDom.stageIdx 0 (idx % nextDom.groups0) br.v0 br.v1))
      (idx % nextDom.groups0) br.path = nextRoot)
  | _, _ => false

/-- Intra-stage Merkle duet trajectory verifier over `GoldilocksExt4`. -/
def verifyStageTrajectory (sdom : WhirStageDomain)
    (nextStageInfo : Option (WhirStageDomain × List UInt8))
    (finalWord : List GoldilocksExt4) (bridgeOp : Option FoldLayerOpening) :
    Nat → Nat → Nat → Option GoldilocksExt4 → List (List UInt8) → List GoldilocksExt4 →
      List FoldLayerOpening → Bool
  | _, _, idx, expected, [], [], [] =>
    verifyStageTerminalTarget nextStageInfo finalWord idx expected bridgeOp
  | layer, groups, idx, expected, root :: roots, α :: αs, op :: ops =>
    decide (0 < groups) &&
    expectedSlotOk expected (idx / groups) op.v0 op.v1 &&
    decide (op.path.length = merkleDepth groups) &&
    decide (merklePathRoot pcsMerkleHash
      (pcsMerkleHash (duetLeafFrame sdom.stageIdx layer (idx % groups) op.v0 op.v1))
      (idx % groups) op.path = root) &&
    verifyStageTrajectory sdom nextStageInfo finalWord bridgeOp
      (layer + 1) (groups / 2) (idx % groups)
      (some (foldDuetExt4 op.v0 op.v1 (sdom.invTwoY0 layer (idx % groups)) sdom.invTwo α))
      roots αs ops
  | _, _, _, _, _, _, _ => false

/-- Verify one WHIR stage's header, dual OOD challenges (`OOD_SAMPLES = 2`), degree-2 shift
    sumcheck, PoW, and queries. -/
def verifyOneWhirStage (rowChallenges : List GoldilocksExt4)
    (finalWord : List GoldilocksExt4) (prior : List UInt8)
    (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextStageInfo : Option (WhirStageDomain × List UInt8)) : Bool :=
  let nextRoot? := nextStageInfo.map Prod.snd
  let pSeed := stagePowSeed prior sp nextRoot? finalWord
  let qSeed := stageQuerySeed pSeed sp.powNonce
  let expectedFold := if sdom.bindRowChallenges then rowChallenges
                      else sp.shiftChallenges
  decide (sp.oodChallenges = deriveStageOodChallenges prior sp.stageRoot) &&
  decide ((stageAllRoots sp).length = sdom.foldLayers) &&
  decide (sp.shiftPolys.length = sdom.foldLayers) &&
  decide (sp.shiftChallenges =
    deriveStageShiftChallenges (stagePostOodTranscript prior sp) (stageAllRoots sp) sp.shiftPolys) &&
  decide (sp.foldChallenges = expectedFold) &&
  decide (sp.foldChallenges.length = sdom.foldLayers) &&
  verifyShiftSumcheckChain sp.shiftClaim sp.shiftPolys sp.shiftChallenges sp.shiftTerminalEval &&
  verifyWhirStagePow (stagePowDigest pSeed) sp.powNonce sdom.powBits &&
  decide (sp.queries.map (·.index) = deriveStageQueryIndices sdom qSeed) &&
  strictlyIncreasing (sp.queries.map (·.index)) &&
  decide (sp.queries.length = min sdom.numQueries sdom.groups0) &&
  sp.queries.all (fun q =>
    decide (q.index < sdom.groups0) &&
    verifyStageTrajectory sdom nextStageInfo finalWord q.nextStageBridge
      0 sdom.groups0 q.index none (stageAllRoots sp) sp.foldChallenges q.layers)

/-- Verify all WHIR stages sequentially, threading the Fiat–Shamir transcript from stage to stage. -/
def verifyWhirStages (rowChallenges : List GoldilocksExt4) (finalWord : List GoldilocksExt4) :
    List UInt8 → List WhirStageDomain → List WhirStageProof → Bool
  | _, [], [] => true
  | prior, [sdom], [sp] =>
    verifyOneWhirStage rowChallenges finalWord prior sdom sp none
  | prior, sdom :: nextDom :: restDoms, sp :: nextSp :: restProofs =>
    let pSeed := stagePowSeed prior sp (some nextSp.stageRoot) finalWord
    let qSeed := stageQuerySeed pSeed sp.powNonce
    verifyOneWhirStage rowChallenges finalWord prior sdom sp (some (nextDom, nextSp.stageRoot)) &&
    verifyWhirStages rowChallenges finalWord qSeed (nextDom :: restDoms) (nextSp :: restProofs)
  | _, _, _ => false

def collectAllFoldChallenges (proof : SuccinctAggregateProof) : List GoldilocksExt4 :=
  proof.stages.flatMap (·.foldChallenges)

/-- Public data of the row arithmetization over `GoldilocksExt4`:
    - `decodeSigs`: extracts `List PqHashSig` from the committed Round-0 codeword `table0`
    - `honestClaim` / `honestRound`: honest degree-8 row-sumcheck polynomial schedule
    - `terminal`: verifier's algebraic gate evaluator on `(finalWord, rowChallenges, foldChallenges)`
    - `isStageCodeword`: Reed–Solomon codeword predicate for stage position `pos` (`pos = 0` is Round-0)
    - `isFinalCodeword`: Reed–Solomon early-stop codeword predicate on `finalWord`. -/
structure RowArithmetization where
  decodeSigs : List GoldilocksExt4 → List PqHashSig
  honestClaim : List GoldilocksExt4 → GoldilocksExt4
  honestRound : List GoldilocksExt4 → List GoldilocksExt4 → List GoldilocksExt4
  terminal : List GoldilocksExt4 → List GoldilocksExt4 → List GoldilocksExt4 → GoldilocksExt4
  isStageCodeword : Nat → List GoldilocksExt4 → Bool
  isFinalCodeword : List GoldilocksExt4 → Bool

def RowArithmetization.isRound0Codeword (arith : RowArithmetization)
    (table0 : List GoldilocksExt4) : Bool :=
  arith.isStageCodeword 0 table0

/-- **Succinct Multi-Stage `GoldilocksExt4` WHIR Aggregate Verifier (`verifySuccinctAggregate`)**:
    Verifies instance framing, regime match, degree-8 row sumcheck, Stage-0 root binding to
    `agg.traceCommitment`, multi-stage WHIR OOD + degree-2 shift sumcheck + PoW + distinct fiber
    trajectories, early-stop Reed–Solomon codeword `isFinalCodeword`, and terminal evaluation link.
    Receives **zero** plaintext `PqHashSig` signatures. -/
def verifySuccinctAggregate (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fsTranscript : List UInt8) : Bool :=
  match proof.stages with
  | [] => false
  | sp0 :: _ =>
    decide (fsTranscript = aggregateInstanceFrame inst proof.agg) &&
    decide (proof.agg.regime = inst.regime) &&
    decide (proof.agg.suite.suiteId = inst.suite.suiteId) &&
    decide (proof.agg.params = inst.params) &&
    decide (sp0.stageRoot = proof.agg.traceCommitment) &&
    decide (proof.agg.challenges = deriveRowSumcheckChallenges fsTranscript proof.agg.roundPolys) &&
    verifyAggregateAlgebra inst.committee proof.agg &&
    decide (proof.agg.terminalEval =
      arith.terminal proof.finalWord proof.agg.challenges (collectAllFoldChallenges proof)) &&
    arith.isFinalCodeword proof.finalWord &&
    verifyWhirStages proof.agg.challenges proof.finalWord
      (rowSumcheckTranscriptTail fsTranscript proof.agg.roundPolys)
      dom.stages proof.stages

/-- Succinct signature-aggregation verifier entry point (upgraded in place: zero plaintext
    `openedSignatures : List PqHashSig`). -/
abbrev verifyAggregatedSignature := verifySuccinctAggregate

/-- Recursive disjoint 2-to-1 merge tree of succinct WHIR certificates (zero plaintext signatures). -/
inductive MergeNode where
  | leaf (proof : SuccinctAggregateProof) (transcript : List UInt8)
  | branch (proof : SuccinctAggregateProof) (transcript : List UInt8) (left right : MergeNode)

def MergeNode.proof : MergeNode → SuccinctAggregateProof
  | .leaf p _ => p
  | .branch p _ _ _ => p

def MergeNode.certificate (n : MergeNode) : AggregatedSignature := n.proof.agg

/-- Recursive merge-tree verifier checking child commitments, disjoint validator bitmaps,
    union conservation, and full succinct `GoldilocksExt4` WHIR verification at every node. -/
def verifyMergeTree (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) : Nat → MergeNode → Bool
  | 0, _ => false
  | _ + 1, .leaf p fs =>
    p.agg.childrenCommitment.isNone && verifySuccinctAggregate arith dom inst p fs
  | budget + 1, .branch p fs left right =>
    decide (p.agg.childrenCommitment =
      some (left.certificate.traceCommitment, right.certificate.traceCommitment)) &&
    verifyMergeTree arith dom inst budget left &&
    verifyMergeTree arith dom inst budget right &&
    bitmapDisjointSpec left.certificate.bitmap right.certificate.bitmap &&
    decide (p.agg.bitmap = bitmapUnionSpec left.certificate.bitmap right.certificate.bitmap) &&
    verifySuccinctAggregate arith dom inst p fs

abbrev SuccinctMergeNode := MergeNode
abbrev verifySuccinctMergeTree := verifyMergeTree

theorem merge_tree_rejects_invalid_child (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (budget : Nat)
    (p : SuccinctAggregateProof) (fs : List UInt8) (left right : MergeNode)
    (h : verifyMergeTree arith dom inst budget left = false ∨
         verifyMergeTree arith dom inst budget right = false) :
    verifyMergeTree arith dom inst (budget + 1) (.branch p fs left right) = false := by
  rcases h with h | h <;> simp only [verifyMergeTree, h, Bool.false_and, Bool.and_false]

theorem merge_tree_rejects_overlap (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (budget : Nat)
    (p : SuccinctAggregateProof) (fs : List UInt8) (left right : MergeNode)
    (h : bitmapDisjointSpec left.certificate.bitmap right.certificate.bitmap = false) :
    verifyMergeTree arith dom inst (budget + 1) (.branch p fs left right) = false := by
  simp only [verifyMergeTree, h, Bool.false_and, Bool.and_false]

theorem merge_tree_rejects_child_commitment (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (budget : Nat)
    (p : SuccinctAggregateProof) (fs : List UInt8) (left right : MergeNode)
    (h : p.agg.childrenCommitment ≠
      some (left.certificate.traceCommitment, right.certificate.traceCommitment)) :
    verifyMergeTree arith dom inst (budget + 1) (.branch p fs left right) = false := by
  simp only [verifyMergeTree, decide_eq_false h, Bool.false_and]

theorem merge_tree_depth_exhausted (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (tree : MergeNode) :
    verifyMergeTree arith dom inst 0 tree = false := by rfl

/-! ## 8. Constructive Multi-Stage WHIR Knowledge Soundness & Unforgeability Reduction -/

def stageTerminalTableOk (nextStageOpt : Option (WhirStageDomain × List GoldilocksExt4))
    (finalWord : List GoldilocksExt4) (idx : Nat) (expected : Option GoldilocksExt4) : Bool :=
  match nextStageOpt with
  | none => finalValueOk finalWord idx expected
  | some (nextDom, nextTable0) =>
    decide (0 < nextDom.groups0) &&
    expectedSlotOk expected (idx / nextDom.groups0)
      (nextTable0.getD (idx % nextDom.groups0) CommRingOps.zero)
      (nextTable0.getD (idx % nextDom.groups0 + nextDom.groups0) CommRingOps.zero)

def stageTableTrajectoryOk (sdom : WhirStageDomain)
    (nextStageOpt : Option (WhirStageDomain × List GoldilocksExt4))
    (finalWord : List GoldilocksExt4) :
    Nat → Nat → Nat → Option GoldilocksExt4 → List (List GoldilocksExt4) →
      List GoldilocksExt4 → Bool
  | _, _, idx, expected, [], [] => stageTerminalTableOk nextStageOpt finalWord idx expected
  | layer, groups, idx, expected, w :: ws, α :: αs =>
    decide (0 < groups) &&
    expectedSlotOk expected (idx / groups)
      (w.getD (idx % groups) CommRingOps.zero)
      (w.getD (idx % groups + groups) CommRingOps.zero) &&
    stageTableTrajectoryOk sdom nextStageOpt finalWord (layer + 1) (groups / 2) (idx % groups)
      (some (foldDuetExt4 (w.getD (idx % groups) CommRingOps.zero)
        (w.getD (idx % groups + groups) CommRingOps.zero)
        (sdom.invTwoY0 layer (idx % groups)) sdom.invTwo α)) ws αs
  | _, _, _, _, _, _ => false

/-- Binding predicate stating `tables` are the Merkle-committed layer tables of stage `stageIdx`. -/
def StageLayersBound (authPath : Nat → Nat → Nat → List (List UInt8)) (stageIdx : Nat) :
    Nat → Nat → List (List GoldilocksExt4) → List (List UInt8) → Prop
  | _, _, [], [] => True
  | layer, groups, w :: ws, root :: roots =>
    (∀ g, g < groups →
      merklePathRoot pcsMerkleHash
        (pcsMerkleHash (duetLeafFrame stageIdx layer g (w.getD g CommRingOps.zero)
          (w.getD (g + groups) CommRingOps.zero))) g (authPath stageIdx layer g) = root ∧
      (authPath stageIdx layer g).length = merkleDepth groups) ∧
    StageLayersBound authPath stageIdx (layer + 1) (groups / 2) ws roots
  | _, _, _, _ => False

/-- Binding predicate across all WHIR stages in `dom.stages` and `proof.stages`. -/
def StagesBound (authPath : Nat → Nat → Nat → List (List UInt8)) :
    List WhirStageDomain → List (List (List GoldilocksExt4)) → List WhirStageProof → Prop
  | [], [], [] => True
  | sdom :: sdoms, stTables :: restTables, sp :: sps =>
    stTables ≠ [] ∧
    StageLayersBound authPath sdom.stageIdx 0 sdom.groups0 stTables (stageAllRoots sp) ∧
    StagesBound authPath sdoms restTables sps
  | _, _, _ => False

def StageNextBound (authPath : Nat → Nat → Nat → List (List UInt8)) :
    Option (WhirStageDomain × List UInt8) → Option (WhirStageDomain × List GoldilocksExt4) → Prop
  | none, none => True
  | some (nd, nr), some (nd', nt0) =>
    nd = nd' ∧
    (∀ g, g < nd.groups0 →
      merklePathRoot pcsMerkleHash
        (pcsMerkleHash (duetLeafFrame nd.stageIdx 0 g (nt0.getD g CommRingOps.zero)
          (nt0.getD (g + nd.groups0) CommRingOps.zero))) g (authPath nd.stageIdx 0 g) = nr ∧
      (authPath nd.stageIdx 0 g).length = merkleDepth nd.groups0)
  | _, _ => False

def stageTerminalSound (authPath : Nat → Nat → Nat → List (List UInt8))
    (nextStageInfo : Option (WhirStageDomain × List UInt8))
    (nextStageOpt : Option (WhirStageDomain × List GoldilocksExt4))
    (finalWord : List GoldilocksExt4) (idx : Nat) (expected : Option GoldilocksExt4)
    (bridgeOp : Option FoldLayerOpening)
    (hTerm : verifyStageTerminalTarget nextStageInfo finalWord idx expected bridgeOp = true)
    (hNextBound : StageNextBound authPath nextStageInfo nextStageOpt) :
    PSum (HashCollisionWitness pcsMerkleHash)
      (PLift (stageTerminalTableOk nextStageOpt finalWord idx expected = true)) :=
  match nextStageInfo, nextStageOpt, bridgeOp with
  | none, none, none => .inr ⟨hTerm⟩
  | none, none, some _ => False.elim (by simp [verifyStageTerminalTarget] at hTerm)
  | none, some _, _ => False.elim hNextBound
  | some _, none, _ => False.elim hNextBound
  | some _, some _, none => False.elim (by simp [verifyStageTerminalTarget] at hTerm)
  | some (nd, nr), some (nd', nt0), some br =>
    have hEqDom : nd = nd' := hNextBound.1
    have hU : 0 < nd.groups0 ∧ expectedSlotOk expected (idx / nd.groups0) br.v0 br.v1 = true ∧
        br.path.length = merkleDepth nd.groups0 ∧
        merklePathRoot pcsMerkleHash
          (pcsMerkleHash (duetLeafFrame nd.stageIdx 0 (idx % nd.groups0) br.v0 br.v1))
          (idx % nd.groups0) br.path = nr := by
      have h0 : (decide (0 < nd.groups0) &&
          expectedSlotOk expected (idx / nd.groups0) br.v0 br.v1 &&
          decide (br.path.length = merkleDepth nd.groups0) &&
          decide (merklePathRoot pcsMerkleHash
            (pcsMerkleHash (duetLeafFrame nd.stageIdx 0 (idx % nd.groups0) br.v0 br.v1))
            (idx % nd.groups0) br.path = nr)) = true := hTerm
      rcases Bool.and_eq_true_iff.mp h0 with ⟨h0, c4⟩
      rcases Bool.and_eq_true_iff.mp h0 with ⟨h0, c3⟩
      rcases Bool.and_eq_true_iff.mp h0 with ⟨c1, c2⟩
      exact ⟨of_decide_eq_true c1, c2, of_decide_eq_true c3, of_decide_eq_true c4⟩
    have hBg := hNextBound.2 (idx % nd.groups0) (Nat.mod_lt _ hU.1)
    if hMatch : br.v0 = nt0.getD (idx % nd.groups0) CommRingOps.zero ∧
        br.v1 = nt0.getD (idx % nd.groups0 + nd.groups0) CommRingOps.zero then
      .inr ⟨by
        subst hEqDom
        show (decide (0 < nd.groups0) &&
          expectedSlotOk expected (idx / nd.groups0)
            (nt0.getD (idx % nd.groups0) CommRingOps.zero)
            (nt0.getD (idx % nd.groups0 + nd.groups0) CommRingOps.zero)) = true
        rw [← hMatch.1, ← hMatch.2]
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hU.1, hU.2.1⟩⟩
    else
      .inl (duetOpeningCollision nd.stageIdx 0 (idx % nd.groups0) br.v0 br.v1 _ _
        br.path (authPath nd.stageIdx 0 (idx % nd.groups0)) nr hMatch
        (hU.2.2.1.trans hBg.2.symm) hU.2.2.2 hBg.1)

def stageTrajectorySound (sdom : WhirStageDomain)
    (nextStageInfo : Option (WhirStageDomain × List UInt8))
    (nextStageOpt : Option (WhirStageDomain × List GoldilocksExt4))
    (finalWord : List GoldilocksExt4) (bridgeOp : Option FoldLayerOpening)
    (authPath : Nat → Nat → Nat → List (List UInt8))
    (roots : List (List UInt8)) :
    ∀ (αs : List GoldilocksExt4) (ops : List FoldLayerOpening)
      (tables : List (List GoldilocksExt4)) (layer groups idx : Nat)
      (expected : Option GoldilocksExt4),
      verifyStageTrajectory sdom nextStageInfo finalWord bridgeOp
        layer groups idx expected roots αs ops = true →
      StageLayersBound authPath sdom.stageIdx layer groups tables roots →
      StageNextBound authPath nextStageInfo nextStageOpt →
      PSum (HashCollisionWitness pcsMerkleHash)
        (PLift (stageTableTrajectoryOk sdom nextStageOpt finalWord
          layer groups idx expected tables αs = true)) :=
  match roots with
  | [] => fun αs ops tables _ _ idx expected hV hB hN =>
    match αs, ops, tables with
    | [], [], [] =>
      stageTerminalSound authPath nextStageInfo nextStageOpt finalWord idx expected bridgeOp hV hN
    | [], [], _ :: _ => False.elim hB
    | [], _ :: _, _ => False.elim (by simp [verifyStageTrajectory] at hV)
    | _ :: _, ops, _ => False.elim (by cases ops <;> simp [verifyStageTrajectory] at hV)
  | root :: roots => fun αs ops tables layer groups idx expected hV hB hN =>
    match αs, ops, tables with
    | [], ops, _ => False.elim (by cases ops <;> simp [verifyStageTrajectory] at hV)
    | _ :: _, [], _ => False.elim (by simp [verifyStageTrajectory] at hV)
    | _ :: _, _ :: _, [] => False.elim hB
    | α :: αs, op :: ops, w :: ws =>
      have hU : 0 < groups ∧ expectedSlotOk expected (idx / groups) op.v0 op.v1 = true ∧
          op.path.length = merkleDepth groups ∧
          merklePathRoot pcsMerkleHash
            (pcsMerkleHash (duetLeafFrame sdom.stageIdx layer (idx % groups) op.v0 op.v1))
            (idx % groups) op.path = root ∧
          verifyStageTrajectory sdom nextStageInfo finalWord bridgeOp (layer + 1) (groups / 2)
            (idx % groups)
            (some (foldDuetExt4 op.v0 op.v1 (sdom.invTwoY0 layer (idx % groups)) sdom.invTwo α))
            roots αs ops = true := by
        have h0 : (decide (0 < groups) &&
            expectedSlotOk expected (idx / groups) op.v0 op.v1 &&
            decide (op.path.length = merkleDepth groups) &&
            decide (merklePathRoot pcsMerkleHash
              (pcsMerkleHash (duetLeafFrame sdom.stageIdx layer (idx % groups) op.v0 op.v1))
              (idx % groups) op.path = root) &&
            verifyStageTrajectory sdom nextStageInfo finalWord bridgeOp (layer + 1) (groups / 2)
              (idx % groups)
              (some (foldDuetExt4 op.v0 op.v1 (sdom.invTwoY0 layer (idx % groups)) sdom.invTwo α))
              roots αs ops) = true := hV
        rcases Bool.and_eq_true_iff.mp h0 with ⟨h0, h5⟩
        rcases Bool.and_eq_true_iff.mp h0 with ⟨h0, h4⟩
        rcases Bool.and_eq_true_iff.mp h0 with ⟨h0, h3⟩
        rcases Bool.and_eq_true_iff.mp h0 with ⟨h1, h2⟩
        exact ⟨of_decide_eq_true h1, h2, of_decide_eq_true h3, of_decide_eq_true h4, h5⟩
      have hBg := hB.1 (idx % groups) (Nat.mod_lt _ hU.1)
      if hEq : op.v0 = w.getD (idx % groups) CommRingOps.zero ∧
          op.v1 = w.getD (idx % groups + groups) CommRingOps.zero then
        match stageTrajectorySound sdom nextStageInfo nextStageOpt finalWord bridgeOp authPath
            roots αs ops ws (layer + 1) (groups / 2) (idx % groups) _ hU.2.2.2.2 hB.2 hN with
        | .inl c => .inl c
        | .inr ⟨hT⟩ => .inr ⟨by
            show (decide (0 < groups) &&
              expectedSlotOk expected (idx / groups)
                (w.getD (idx % groups) CommRingOps.zero)
                (w.getD (idx % groups + groups) CommRingOps.zero) &&
              stageTableTrajectoryOk sdom nextStageOpt finalWord (layer + 1) (groups / 2)
                (idx % groups)
                (some (foldDuetExt4 (w.getD (idx % groups) CommRingOps.zero)
                  (w.getD (idx % groups + groups) CommRingOps.zero)
                  (sdom.invTwoY0 layer (idx % groups)) sdom.invTwo α)) ws αs) = true
            rw [← hEq.1, ← hEq.2]
            exact Bool.and_eq_true_iff.mpr
              ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hU.1, hU.2.1⟩, hT⟩⟩
      else
        .inl (duetOpeningCollision sdom.stageIdx layer (idx % groups) op.v0 op.v1 _ _ op.path
          (authPath sdom.stageIdx layer (idx % groups)) root hEq
          (hU.2.2.1.trans hBg.2.symm) hU.2.2.2.1 hBg.1)
termination_by structural roots

def stageQueriesSound (sdom : WhirStageDomain)
    (nextStageInfo : Option (WhirStageDomain × List UInt8))
    (nextStageOpt : Option (WhirStageDomain × List GoldilocksExt4))
    (finalWord : List GoldilocksExt4)
    (authPath : Nat → Nat → Nat → List (List UInt8))
    (roots : List (List UInt8)) (αs : List GoldilocksExt4)
    (tables : List (List GoldilocksExt4)) :
    ∀ (qs : List StageQueryOpening),
      qs.all (fun q => decide (q.index < sdom.groups0) &&
        verifyStageTrajectory sdom nextStageInfo finalWord q.nextStageBridge
          0 sdom.groups0 q.index none roots αs q.layers) = true →
      StageLayersBound authPath sdom.stageIdx 0 sdom.groups0 tables roots →
      StageNextBound authPath nextStageInfo nextStageOpt →
      PSum (HashCollisionWitness pcsMerkleHash)
        (PLift (∀ q ∈ qs, q.index < sdom.groups0 ∧
          stageTableTrajectoryOk sdom nextStageOpt finalWord
            0 sdom.groups0 q.index none tables αs = true))
  | [], _, _, _ => .inr ⟨fun _ hq => by cases hq⟩
  | q :: qs, hAll, hB, hN =>
    have hSplit := Bool.and_eq_true_iff.mp hAll
    have hq := Bool.and_eq_true_iff.mp hSplit.1
    match stageTrajectorySound sdom nextStageInfo nextStageOpt finalWord q.nextStageBridge
        authPath roots αs q.layers tables 0 sdom.groups0 q.index none hq.2 hB hN with
    | .inl c => .inl c
    | .inr ⟨h1⟩ =>
      match stageQueriesSound sdom nextStageInfo nextStageOpt finalWord authPath roots αs
          tables qs hSplit.2 hB hN with
      | .inl c => .inl c
      | .inr ⟨h2⟩ => .inr ⟨fun q' hq' => by
          rcases List.mem_cons.mp hq' with e | e
          · rw [e]; exact ⟨of_decide_eq_true hq.1, h1⟩
          · exact h2 q' e⟩

/-- Constructive bounded search (`0 Classical.choice`) for the first index `< n` failing `ok`. -/
def firstFailBelow (ok : Nat → Bool) :
    (n : Nat) → PSum { i : Nat // i < n ∧ ok i = false } (PLift (∀ i, i < n → ok i = true))
  | 0 => .inr ⟨fun i h => absurd h (Nat.not_lt_zero i)⟩
  | n + 1 =>
    match firstFailBelow ok n with
    | .inl ⟨i, hi, hb⟩ => .inl ⟨i, Nat.lt_succ_of_lt hi, hb⟩
    | .inr ⟨hall⟩ =>
      if h : ok n = true then
        .inr ⟨fun i hi => by
          rcases Nat.lt_or_ge i n with hlt | hge
          · exact hall i hlt
          · have hEq : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
            rw [hEq]; exact h⟩
      else .inl ⟨n, Nat.lt_succ_self n, Bool.eq_false_iff.mpr h⟩

/-- Transcript-indexed query-miss witness at identified WHIR stage `stagePos`. -/
structure WhirStageQueryMiss (finalWord : List GoldilocksExt4)
    (dom : WhirDomain) (allTables : List (List (List GoldilocksExt4)))
    (proof : SuccinctAggregateProof) where
  stagePos : Nat
  sdom : WhirStageDomain
  sp : WhirStageProof
  stTables : List (List GoldilocksExt4)
  nextStageOpt : Option (WhirStageDomain × List GoldilocksExt4)
  dom_at : dom.stages[stagePos]? = some sdom
  proof_at : proof.stages[stagePos]? = some sp
  tables_at : allTables[stagePos]? = some stTables
  badIndex : Nat
  badIndex_lt : badIndex < sdom.groups0
  bad : stageTableTrajectoryOk sdom nextStageOpt finalWord 0 sdom.groups0
          badIndex none stTables sp.foldChallenges = false
  queries_distinct : (sp.queries.map (·.index)).Nodup
  queries_count : (sp.queries.map (·.index)).length = min sdom.numQueries sdom.groups0
  queries_good : ∀ i ∈ sp.queries.map (·.index), i < sdom.groups0 ∧
    stageTableTrajectoryOk sdom nextStageOpt finalWord 0 sdom.groups0
      i none stTables sp.foldChallenges = true

/-- Predicate asserting that EVERY coset index in EVERY WHIR stage folds consistently. -/
def AllStagesConsistent (finalWord : List GoldilocksExt4) :
    List WhirStageDomain → List (List (List GoldilocksExt4)) → List WhirStageProof → Prop
  | [], [], [] => True
  | [sdom], [stTables], [sp] =>
    ∀ i, i < sdom.groups0 →
      stageTableTrajectoryOk sdom none finalWord 0 sdom.groups0
        i none stTables sp.foldChallenges = true
  | sdom :: nextDom :: restDoms, stTables :: nextTables :: restTables, sp :: nextSp :: restProofs =>
    (∀ i, i < sdom.groups0 →
      stageTableTrajectoryOk sdom (some (nextDom, nextTables.headD [])) finalWord
        0 sdom.groups0 i none stTables sp.foldChallenges = true) ∧
    AllStagesConsistent finalWord (nextDom :: restDoms) (nextTables :: restTables)
      (nextSp :: restProofs)
  | _, _, _ => False

/-- Transcript-indexed proximity-gap hit: at identified stage `stagePos`, the committed stage
    word is NOT a valid stage Reed–Solomon codeword (`isStageCodeword stagePos = false`), yet all
    stage trajectories fold consistently into `finalWord` (`isFinalCodeword = true`). -/
structure WhirProximityHit (arith : RowArithmetization) (dom : WhirDomain)
    (finalWord : List GoldilocksExt4) (allTables : List (List (List GoldilocksExt4)))
    (proof : SuccinctAggregateProof) where
  stagePos : Nat
  sdom : WhirStageDomain
  stTables : List (List GoldilocksExt4)
  dom_at : dom.stages[stagePos]? = some sdom
  tables_at : allTables[stagePos]? = some stTables
  stage_not_codeword : arith.isStageCodeword stagePos (stTables.headD []) = false
  final_in_code : arith.isFinalCodeword finalWord = true
  all_consistent : AllStagesConsistent finalWord dom.stages allTables proof.stages

private theorem unpack_one_stage_verify {rowChallenges finalWord : List GoldilocksExt4}
    {prior : List UInt8} {sdom : WhirStageDomain} {sp : WhirStageProof}
    {nextInfo : Option (WhirStageDomain × List UInt8)}
    (h : verifyOneWhirStage rowChallenges finalWord prior sdom sp nextInfo = true) :
    strictlyIncreasing (sp.queries.map (·.index)) = true ∧
    sp.queries.length = min sdom.numQueries sdom.groups0 ∧
    sp.queries.all (fun q =>
      decide (q.index < sdom.groups0) &&
      verifyStageTrajectory sdom nextInfo finalWord q.nextStageBridge
        0 sdom.groups0 q.index none (stageAllRoots sp) sp.foldChallenges q.layers) = true := by
  unfold verifyOneWhirStage at h
  dsimp only at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h, c12⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, c11⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨_, c10⟩
  exact ⟨c10, of_decide_eq_true c11, c12⟩

private theorem headRootBound {authPath : Nat → Nat → Nat → List (List UInt8)}
    {nd : WhirStageDomain} {nt : List (List GoldilocksExt4)} {nsp : WhirStageProof}
    (hne : nt ≠ [])
    (hB : StageLayersBound authPath nd.stageIdx 0 nd.groups0 nt (stageAllRoots nsp)) :
    ∀ g, g < nd.groups0 →
      merklePathRoot pcsMerkleHash
        (pcsMerkleHash (duetLeafFrame nd.stageIdx 0 g
          ((nt.headD []).getD g CommRingOps.zero)
          ((nt.headD []).getD (g + nd.groups0) CommRingOps.zero)))
        g (authPath nd.stageIdx 0 g) = nsp.stageRoot ∧
      (authPath nd.stageIdx 0 g).length = merkleDepth nd.groups0 := by
  cases nt with
  | nil => exact False.elim (hne rfl)
  | cons w0 _ => exact hB.1

/-- Constructively walk all WHIR stages: extract a Merkle hash collision, a concrete
    `WhirStageQueryMiss` at an identified stage, or prove `AllStagesConsistent`. -/
def checkAllWhirStagesQueries (rowChallenges finalWord : List GoldilocksExt4)
    (authPath : Nat → Nat → Nat → List (List UInt8)) :
    ∀ (prior : List UInt8) (sdoms : List WhirStageDomain)
      (allTables : List (List (List GoldilocksExt4))) (sps : List WhirStageProof),
      verifyWhirStages rowChallenges finalWord prior sdoms sps = true →
      StagesBound authPath sdoms allTables sps →
      PSum (HashCollisionWitness pcsMerkleHash)
        (PSum
          (Sigma fun pos : Nat =>
            Sigma fun sdom : WhirStageDomain =>
              Sigma fun sp : WhirStageProof =>
                Sigma fun stTables : List (List GoldilocksExt4) =>
                  Sigma fun nextOpt : Option (WhirStageDomain × List GoldilocksExt4) =>
                    { idx : Nat //
                      sdoms[pos]? = some sdom ∧ sps[pos]? = some sp ∧
                      allTables[pos]? = some stTables ∧ idx < sdom.groups0 ∧
                      stageTableTrajectoryOk sdom nextOpt finalWord 0 sdom.groups0
                        idx none stTables sp.foldChallenges = false ∧
                      (sp.queries.map (·.index)).Nodup ∧
                      (sp.queries.map (·.index)).length = min sdom.numQueries sdom.groups0 ∧
                      (∀ j ∈ sp.queries.map (·.index), j < sdom.groups0 ∧
                        stageTableTrajectoryOk sdom nextOpt finalWord 0 sdom.groups0
                          j none stTables sp.foldChallenges = true) })
          (PLift (AllStagesConsistent finalWord sdoms allTables sps)))
  | _, [], [], [], _, _ => .inr (.inr ⟨trivial⟩)
  | _, [], _ :: _, _, _, hB => False.elim hB
  | _, [], [], _ :: _, _, hB => False.elim hB
  | _, _ :: _, [], _, _, hB => False.elim hB
  | _, _ :: _, _ :: _, [], _, hB => False.elim hB
  | prior, [sdom], [stTables], [sp], hVer, hB =>
    have hU := unpack_one_stage_verify hVer
    match stageQueriesSound sdom none none finalWord authPath (stageAllRoots sp)
        sp.foldChallenges stTables sp.queries hU.2.2 hB.2.1 trivial with
    | .inl col => .inl col
    | .inr ⟨hQ⟩ =>
      match firstFailBelow (fun i => stageTableTrajectoryOk sdom none finalWord
          0 sdom.groups0 i none stTables sp.foldChallenges) sdom.groups0 with
      | .inl ⟨badIdx, hLt, hBad⟩ =>
        .inr (.inl ⟨0, sdom, sp, stTables, none, ⟨badIdx, rfl, rfl, rfl, hLt, hBad,
          strictlyIncreasing_nodup _ hU.1,
          by rw [List.length_map]; exact hU.2.1,
          fun j hj => by
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hj
            exact hQ q hq⟩⟩)
      | .inr ⟨hAll⟩ => .inr (.inr ⟨hAll⟩)
  | _, [_], _ :: _ :: _, [_], _, hB => False.elim hB.2.2
  | _, [_], [_], _ :: _ :: _, hVer, _ =>
    False.elim (by simp [verifyWhirStages] at hVer)
  | _, [_], _ :: _ :: _, _ :: _ :: _, _, hB => False.elim hB.2.2
  | _, _ :: _ :: _, [_], [_], _, hB => False.elim hB.2.2
  | _, _ :: _ :: _, [_], _ :: _ :: _, _, hB => False.elim hB.2.2
  | _, _ :: _ :: _, _ :: _ :: _, [_], _, hB => False.elim hB.2.2
  | prior, sdom :: nextDom :: restDoms, stTables :: nextTables :: restTables,
      sp :: nextSp :: restProofs, hVer, hB =>
    have hSplit := Bool.and_eq_true_iff.mp hVer
    have hU := unpack_one_stage_verify hSplit.1
    have hNextRoot := headRootBound hB.2.2.1 hB.2.2.2.1
    match stageQueriesSound sdom (some (nextDom, nextSp.stageRoot))
        (some (nextDom, nextTables.headD [])) finalWord authPath (stageAllRoots sp)
        sp.foldChallenges stTables sp.queries hU.2.2 hB.2.1 ⟨rfl, hNextRoot⟩ with
    | .inl col => .inl col
    | .inr ⟨hQ⟩ =>
      match firstFailBelow (fun i =>
          stageTableTrajectoryOk sdom (some (nextDom, nextTables.headD [])) finalWord
            0 sdom.groups0 i none stTables sp.foldChallenges) sdom.groups0 with
      | .inl ⟨badIdx, hLt, hBad⟩ =>
        .inr (.inl ⟨0, sdom, sp, stTables, some (nextDom, nextTables.headD []),
          ⟨badIdx, rfl, rfl, rfl, hLt, hBad,
            strictlyIncreasing_nodup _ hU.1,
            by rw [List.length_map]; exact hU.2.1,
            fun j hj => by
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hj
              exact hQ q hq⟩⟩)
      | .inr ⟨hStage0⟩ =>
        match checkAllWhirStagesQueries rowChallenges finalWord authPath _ (nextDom :: restDoms)
            (nextTables :: restTables) (nextSp :: restProofs) hSplit.2 hB.2.2 with
        | .inl col => .inl col
        | .inr (.inl ⟨pos, sd, sp', st, nOpt, ⟨bi, hdAt, hpAt, htAt, rest⟩⟩) =>
          .inr (.inl ⟨pos + 1, sd, sp', st, nOpt, ⟨bi, hdAt, hpAt, htAt, rest⟩⟩)
        | .inr (.inr ⟨hRest⟩) => .inr (.inr ⟨⟨hStage0, hRest⟩⟩)

/-- Constructively check `isStageCodeword (basePos + pos)` across every WHIR stage (`0 Classical`). -/
def checkAllStageCodewordsAux (arith : RowArithmetization) :
    ∀ (basePos : Nat) (sdoms : List WhirStageDomain) (allTables : List (List (List GoldilocksExt4))),
      sdoms.length = allTables.length →
      PSum
        (Sigma fun pos : Nat =>
          Sigma fun sdom : WhirStageDomain =>
            Sigma fun stTables : List (List GoldilocksExt4) =>
              PLift (sdoms[pos]? = some sdom ∧ allTables[pos]? = some stTables ∧
                arith.isStageCodeword (basePos + pos) (stTables.headD []) = false))
        (PLift (∀ pos sdom stTables,
          sdoms[pos]? = some sdom → allTables[pos]? = some stTables →
          arith.isStageCodeword (basePos + pos) (stTables.headD []) = true))
  | _, [], [], _ => .inr ⟨fun pos _ _ h => by cases pos <;> cases h⟩
  | _, [], _ :: _, hL => False.elim (Nat.zero_ne_add_one _ hL)
  | _, _ :: _, [], hL => False.elim (Nat.add_one_ne_zero _ hL)
  | basePos, sdom :: sdoms, stTables :: restTables, hL =>
    if hOk : arith.isStageCodeword basePos (stTables.headD []) = true then
      match checkAllStageCodewordsAux arith (basePos + 1) sdoms restTables (Nat.succ.inj hL) with
      | .inl ⟨pos, sd, st, ⟨hd, ht, hf⟩⟩ =>
        .inl ⟨pos + 1, sd, st, ⟨hd, ht, by
          have hAdd : basePos + (pos + 1) = (basePos + 1) + pos := by omega
          rwa [hAdd]⟩⟩
      | .inr ⟨hRest⟩ => .inr ⟨fun pos sd st hd ht => by
          cases pos with
          | zero =>
            cases hd; cases ht
            simpa only [Nat.add_zero] using hOk
          | succ k =>
            have hAdd : basePos + (k + 1) = (basePos + 1) + k := by omega
            rw [hAdd]
            exact hRest k sd st hd ht⟩
    else
      .inl ⟨0, sdom, stTables, ⟨rfl, rfl, by
        simpa only [Nat.add_zero] using Bool.eq_false_iff.mpr hOk⟩⟩

theorem stagesBound_lengths {authPath : Nat → Nat → Nat → List (List UInt8)}
    {sdoms : List WhirStageDomain} {allTables : List (List (List GoldilocksExt4))}
    {sps : List WhirStageProof}
    (h : StagesBound authPath sdoms allTables sps) :
    sdoms.length = allTables.length ∧ sdoms.length = sps.length := by
  induction sdoms generalizing allTables sps with
  | nil =>
    cases allTables with
    | nil =>
      cases sps with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ _ => exact False.elim h
    | cons _ _ => exact False.elim h
  | cons _ sdoms ih =>
    cases allTables with
    | nil => exact False.elim h
    | cons _ restTables =>
      cases sps with
      | nil => exact False.elim h
      | cons _ restSps =>
        obtain ⟨h1, h2⟩ := ih h.2.2
        exact ⟨congrArg Nat.succ h1, congrArg Nat.succ h2⟩

/-- Lawfulness contract on a multi-stage `GoldilocksExt4` WHIR row arithmetization:
    - `complete`: whenever every stage table is a valid stage Reed–Solomon codeword, `verifyWhirStages`
      accepts, and all stage trajectories fold consistently into `finalWord`, the honest degree-8
      row-sumcheck chain verifies against `arith.terminal`.
    - `sound`: for any valid Round-0 codeword `table0` whose decoded signatures fail
      `checkAllActiveSigners`, the honest row-sumcheck claim `arith.honestClaim table0` is nonzero. -/
structure RowArithmetization.Lawful (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) : Prop where
  complete : ∀ (allTables : List (List (List GoldilocksExt4)))
      (proof : SuccinctAggregateProof) (prior : List UInt8),
    dom.stages.length = allTables.length →
    (∀ pos sdom stTables,
      dom.stages[pos]? = some sdom → allTables[pos]? = some stTables →
      arith.isStageCodeword pos (stTables.headD []) = true) →
    arith.isFinalCodeword proof.finalWord = true →
    verifyWhirStages proof.agg.challenges proof.finalWord prior dom.stages proof.stages = true →
    AllStagesConsistent proof.finalWord dom.stages allTables proof.stages →
    verifySumcheckChain (arith.honestClaim ((allTables.headD []).headD []))
      (adaptivePolys (arith.honestRound ((allTables.headD []).headD [])) proof.agg.challenges)
      proof.agg.challenges
      (arith.terminal proof.finalWord proof.agg.challenges (collectAllFoldChallenges proof)) = true
  sound : ∀ (table0 : List GoldilocksExt4) (bitmap : SignerBitmapSpec),
    arith.isRound0Codeword table0 = true →
    bitmap.length = inst.committee.length →
    checkAllActiveSigners inst.suite inst.params inst.message inst.committee bitmap
      (arith.decodeSigs table0) = false →
    arith.honestClaim table0 ≠ GoldilocksExt4.zero

/-- Committed multi-stage tables and Merkle authentication paths read by the extractor. -/
structure SuccinctExtractionView where
  allTables : List (List (List GoldilocksExt4))
  authPath : Nat → Nat → Nat → List (List UInt8)

end Aggregation

/-- Extraction outcome of `succinct_aggregation_knowledge_soundness`: valid `PqHashSig` witnesses
    for every active signer, or one of four concrete transcript-indexed break witnesses over
    `Aggregation.GoldilocksExt4`. -/
@[expose] def SuccinctOutcome (arith : Aggregation.RowArithmetization)
    (dom : Aggregation.WhirDomain) (inst : Aggregation.AggPublicInstance)
    (proof : Aggregation.SuccinctAggregateProof)
    (view : Aggregation.SuccinctExtractionView) : Type :=
  let table0 := (view.allTables.headD []).headD []
  PSum { _u : Unit // Aggregation.checkAllActiveSigners inst.suite inst.params inst.message
      inst.committee proof.agg.bitmap (arith.decodeSigs table0) = true }
    (PSum (Aggregation.SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
        (Aggregation.adaptivePolys (arith.honestRound table0) proof.agg.challenges)
        proof.agg.challenges)
      (PSum (HashCollisionWitness Aggregation.pcsMerkleHash)
        (PSum (Aggregation.WhirStageQueryMiss proof.finalWord dom view.allTables proof)
          (Aggregation.WhirProximityHit arith dom proof.finalWord view.allTables proof))))

namespace Aggregation

theorem succinct_acceptance_facts (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (h : verifySuccinctAggregate arith dom inst proof fs = true) :
    fs = aggregateInstanceFrame inst proof.agg ∧
    proof.agg.regime = inst.regime ∧
    proof.agg.challenges = deriveRowSumcheckChallenges fs proof.agg.roundPolys ∧
    verifyAggregateAlgebra inst.committee proof.agg = true ∧
    proof.agg.terminalEval =
      arith.terminal proof.finalWord proof.agg.challenges (collectAllFoldChallenges proof) ∧
    arith.isFinalCodeword proof.finalWord = true ∧
    verifyWhirStages proof.agg.challenges proof.finalWord
      (rowSumcheckTranscriptTail fs proof.agg.roundPolys)
      dom.stages proof.stages = true := by
  unfold verifySuccinctAggregate at h
  cases hSt : proof.stages with
  | nil => rw [hSt] at h; cases h
  | cons sp0 sps =>
    rw [hSt] at h
    dsimp only at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h, c8⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, c7⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, c6⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, c5⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, c4⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨c1, c2⟩
    exact ⟨of_decide_eq_true c1, of_decide_eq_true c2, of_decide_eq_true c4, c5,
      of_decide_eq_true c6, c7, c8⟩

theorem succinct_acceptance_header_facts (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (h : verifySuccinctAggregate arith dom inst proof fs = true) :
    proof.agg.regime = inst.regime ∧
    proof.agg.suite.suiteId = inst.suite.suiteId ∧
    proof.agg.params = inst.params := by
  unfold verifySuccinctAggregate at h
  cases hSt : proof.stages with
  | nil => rw [hSt] at h; cases h
  | cons sp0 sps =>
    rw [hSt] at h
    dsimp only at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, cParams⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨h, cSuite⟩
    rcases Bool.and_eq_true_iff.mp h with ⟨_, cReg⟩
    exact ⟨of_decide_eq_true cReg, of_decide_eq_true cSuite, of_decide_eq_true cParams⟩

theorem verifyAggregateAlgebra_facts (committee : List PqPublicKey) (agg : AggregatedSignature)
    (h : verifyAggregateAlgebra committee agg = true) :
    agg.bitmap.length = committee.length ∧ agg.claimedSum = GoldilocksExt4.zero ∧
    verifySumcheckChain agg.claimedSum agg.roundPolys agg.challenges agg.terminalEval = true := by
  unfold verifyAggregateAlgebra at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h, hChain⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, hZero⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨hLen, _⟩
  exact ⟨eq_of_beq hLen, eq_of_beq hZero, hChain⟩

/-- **Constructive `0 Classical.choice` Knowledge Soundness of Multi-Stage `GoldilocksExt4` WHIR
    (`succinct_aggregation_knowledge_soundness`)**:
    Given an accepting `SuccinctAggregateProof` and committed stage tables `view`, constructively
    outputs valid `PqHashSig` witnesses for every active validator bit or a concrete
    `SumcheckSchwartzZippelHit`, `HashCollisionWitness`, `WhirStageQueryMiss`, or
    `WhirProximityHit`. -/
def succinct_aggregation_knowledge_soundness (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    SuccinctOutcome arith dom inst proof view :=
  have hF := succinct_acceptance_facts arith dom inst proof fs hAccept
  have hLens := stagesBound_lengths hBound
  match checkAllWhirStagesQueries proof.agg.challenges proof.finalWord view.authPath
      (rowSumcheckTranscriptTail fs proof.agg.roundPolys)
      dom.stages view.allTables proof.stages hF.2.2.2.2.2.2 hBound with
  | .inl col => .inr (.inr (.inl col))
  | .inr (.inl ⟨pos, sdom, sp, stTables, nextOpt,
      ⟨badIdx, hdAt, hpAt, htAt, hLt, hBad, hNd, hCnt, hGood⟩⟩) =>
    .inr (.inr (.inr (.inl
      { stagePos := pos, sdom := sdom, sp := sp, stTables := stTables, nextStageOpt := nextOpt,
        dom_at := hdAt, proof_at := hpAt, tables_at := htAt,
        badIndex := badIdx, badIndex_lt := hLt, bad := hBad,
        queries_distinct := hNd, queries_count := hCnt, queries_good := hGood })))
  | .inr (.inr ⟨hAllCons⟩) =>
    match checkAllStageCodewordsAux arith 0 dom.stages view.allTables hLens.1 with
    | .inl ⟨pos, sdom, stTables, ⟨hdAt, htAt, hNotCw⟩⟩ =>
      .inr (.inr (.inr (.inr
        { stagePos := pos, sdom := sdom, stTables := stTables,
          dom_at := hdAt, tables_at := htAt,
          stage_not_codeword := by simpa only [Nat.zero_add] using hNotCw,
          final_in_code := hF.2.2.2.2.2.1,
          all_consistent := hAllCons })))
    | .inr ⟨hAllCw0⟩ =>
      have hAllCw : ∀ pos sdom stTables,
          dom.stages[pos]? = some sdom → view.allTables[pos]? = some stTables →
          arith.isStageCodeword pos (stTables.headD []) = true := fun pos sdom stTables hd ht => by
        simpa only [Nat.zero_add] using hAllCw0 pos sdom stTables hd ht
      let table0 := (view.allTables.headD []).headD []
      have hCode0 : arith.isRound0Codeword table0 = true := by
        cases hP : proof.stages with
        | nil =>
          unfold verifySuccinctAggregate at hAccept
          rw [hP] at hAccept; cases hAccept
        | cons sp0 sps =>
          cases hD : dom.stages with
          | nil =>
            have hL2 := hLens.2; rw [hD, hP] at hL2; cases hL2
          | cons sd0 sds =>
            cases hT : view.allTables with
            | nil =>
              have hL1 := hLens.1; rw [hD, hT] at hL1; cases hL1
            | cons st0 sts =>
              have h0 := hAllCw 0 sd0 st0 (by simp [hD]) (by simp [hT])
              dsimp only [table0, RowArithmetization.isRound0Codeword]
              simpa only [hT, List.headD_cons] using h0
      if hSigs : checkAllActiveSigners inst.suite inst.params inst.message inst.committee
          proof.agg.bitmap (arith.decodeSigs table0) = true then
        .inl ⟨(), hSigs⟩
      else
        have hAlg := verifyAggregateAlgebra_facts inst.committee proof.agg hF.2.2.2.1
        have hHon := law.complete view.allTables proof
          (rowSumcheckTranscriptTail fs proof.agg.roundPolys)
          hLens.1 hAllCw hF.2.2.2.2.2.1 hF.2.2.2.2.2.2 hAllCons
        have hNz := law.sound table0 proof.agg.bitmap hCode0 hAlg.1 (Bool.eq_false_iff.mpr hSigs)
        .inr (.inl (extractSumcheckHitFromChain 8 proof.agg.roundPolys proof.agg.claimedSum
          (arith.honestClaim table0)
          (adaptivePolys (arith.honestRound table0) proof.agg.challenges)
          proof.agg.challenges proof.agg.terminalEval
          (by rw [hAlg.2.1]; exact fun h => hNz h.symm) hAlg.2.2
          (by rw [hF.2.2.2.2.1]; exact hHon)))

/-- Per-signer witness extraction (`0 Classical.choice`) from an accepted WHIR certificate. -/
def succinct_aggregation_signer_extraction (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages)
    (i : Nat) (hi : i < inst.committee.length) (hb : i < proof.agg.bitmap.length)
    (active : proof.agg.bitmap[i]'hb = true) :
    let table0 := (view.allTables.headD []).headD []
    PSum { sig : PqHashSig //
        verifyPqHashSig inst.suite inst.params (inst.committee[i]'hi) inst.message sig = true }
      (PSum (SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
          (adaptivePolys (arith.honestRound table0) proof.agg.challenges)
          proof.agg.challenges)
        (PSum (HashCollisionWitness pcsMerkleHash)
          (PSum (WhirStageQueryMiss proof.finalWord dom view.allTables proof)
            (WhirProximityHit arith dom proof.finalWord view.allTables proof)))) :=
  match succinct_aggregation_knowledge_soundness arith dom inst law proof fs view hAccept hBound with
  | .inl ⟨_, hAll⟩ =>
    .inl (extractActiveSignerSig inst.suite inst.params inst.message inst.committee
      proof.agg.bitmap _ i hi hb hAll active)
  | .inr brk => .inr brk

/-- **End-to-End Succinct `GoldilocksExt4` WHIR Aggregation Unforgeability Reduction
    (`qsag_aggregate_unforgeability_reduction`, `0 Classical.choice`)**:
    Welds `verifySuccinctAggregate` + `succinct_aggregation_signer_extraction` directly into
    `extractReachableHypertreeForgery` (`Qsag.HypertreeEufCma`) with zero black-box `hHonestSound`
    premise and zero plaintext signatures in the verifier.

    The upper-layer oracle premise `hUpperOracle` ranges only over
    `ReachableUpperHypertreePos inst.params l g` (`0 < l < numLayers`, `g` inside the layer), the
    positions a verification walk visits, so it is dischargeable from a finite signing log. The
    two instantiations that discharge every oracle premise from an executed signing oracle are
    `qsag_aggregate_unforgeability_reduction_of_statelessLog` and
    `qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog`. Both production geometries
    `(w, ℓ₁) ∈ {(4, 128), (16, 64)}` are covered. -/
def qsag_aggregate_unforgeability_reduction
    (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (i : Nat) (hPk : i < inst.committee.length) (hB : i < proof.agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : inst.committee[i]'hPk = derivePublicKey inst.suite inst.params sk_i)
    (hActive_i : proof.agg.bitmap[i]'hB = true)
    (queriedMsgs : List (List UInt8))
    (qOracle : QueriedWotsOracle)
    (revealedFors : List (UInt64 × Nat × Nat))
    (hGeom : (inst.params.w = 4 ∧ inst.params.ell1 = 128) ∨
      (inst.params.w = 16 ∧ inst.params.ell1 = 64))
    (hFreshMsg : inst.message ∉ queriedMsgs)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages)
    (hStatefulLeaf0Msg : ∀ sig : PqHashSig, inst.params.statefulJorts = true →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        ∃ mPrev ∈ queriedMsgs,
          hRoot = thPreHash inst.suite sk_i.pkSeed
            (derivePublicKey inst.suite inst.params sk_i).pkRoot mPrev)
    (hStatelessLayer0Root : ∀ sig : PqHashSig, inst.params.statefulJorts = false →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        hRoot = computeForsPk inst.suite inst.params sk_i
          (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight))
    (hUpperOracle : ∀ (l : Nat) (g : Nat), ReachableUpperHypertreePos inst.params l g →
      let hRoot0 := computeXmssSubtreeRoot inst.suite inst.params sk_i
        (UInt32.ofNat (l - 1)) (UInt64.ofNat g)
      (∀ hRand hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot0, hCtr, hChains) →
        let hmH := thHashMsg inst.suite hRand sk_i.pkSeed
          (derivePublicKey inst.suite inst.params sk_i).pkRoot hRoot0
          (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (UInt32.ofNat (g % 2 ^ inst.params.subtreeHeight)) hCtr
        let digH := extractBaseWDigits inst.params.w inst.params.ell1 hmH
        checkTargetSum inst.params.w inst.params.ell1 inst.params.targetSum digH = true ∧
        recoverWotsPkFromSig inst.suite inst.params sk_i.pkSeed (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight) digH hChains =
        computeWotsPk inst.suite inst.params sk_i (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight)) ∧
      (∀ hRand hR hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight) = some (hRand, hR, hCtr, hChains) → hR = hRoot0))
    (hLayer0Valid : ∀ sig : PqHashSig, ∀ hRand hRoot0 hCtr hChains,
      qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot0, hCtr, hChains) →
      let hmH := thHashMsg inst.suite hRand sk_i.pkSeed
        (derivePublicKey inst.suite inst.params sk_i).pkRoot hRoot0
        0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight)) hCtr
      let digH := extractBaseWDigits inst.params.w inst.params.ell1 hmH
      checkTargetSum inst.params.w inst.params.ell1 inst.params.targetSum digH = true ∧
      recoverWotsPkFromSig inst.suite inst.params sk_i.pkSeed 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) digH hChains =
      computeWotsPk inst.suite inst.params sk_i 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight)) :
    let table0 := (view.allTables.headD []).headD []
    PSum (Sigma fun sig_i : PqHashSig =>
            HypertreeForgeryBreak inst.suite inst.params sk_i inst.message sig_i revealedFors)
      (PSum (SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
          (adaptivePolys (arith.honestRound table0) proof.agg.challenges)
          proof.agg.challenges)
        (PSum (HashCollisionWitness pcsMerkleHash)
          (PSum (WhirStageQueryMiss proof.finalWord dom view.allTables proof)
            (WhirProximityHit arith dom proof.finalWord view.allTables proof)))) :=
  match succinct_aggregation_signer_extraction arith dom inst law proof fs view
          hAccept hBound i hPk hB hActive_i with
  | .inr brk => .inr brk
  | .inl ⟨sig_i, hVer_i⟩ =>
    have hVerKey : verifyPqHashSig inst.suite inst.params
        (derivePublicKey inst.suite inst.params sk_i) inst.message sig_i = true := by
      rw [← hKey_i]; exact hVer_i
    .inl ⟨sig_i, extractReachableHypertreeForgery inst.suite inst.params sk_i inst.message sig_i
      queriedMsgs qOracle revealedFors hGeom hFreshMsg hVerKey
      (hStatefulLeaf0Msg sig_i) (hStatelessLayer0Root sig_i)
      hUpperOracle (hLayer0Valid sig_i)⟩

/-- **Aggregation unforgeability against an executed stateless signing oracle
    (`qsag_aggregate_unforgeability_reduction_of_statelessLog`, `0 Classical.choice`)**:
    signer `i` answers the arbitrary query list `queries` through `signingOracleLog`. An accepted
    succinct aggregate whose bitmap marks signer `i` active, on a message absent from that log,
    yields a `HypertreeForgeryBreak` against signer `i` whose revealed FORS leaves are exactly
    those the log opened, or one of the four proof-system break witnesses. There is no
    caller-supplied oracle and no oracle premise: all of them are discharged from the log by
    `extractReachableHypertreeForgery_of_statelessLog`. -/
def qsag_aggregate_unforgeability_reduction_of_statelessLog
    (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (i : Nat) (hPk : i < inst.committee.length) (hB : i < proof.agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : inst.committee[i]'hPk = derivePublicKey inst.suite inst.params sk_i)
    (hActive_i : proof.agg.bitmap[i]'hB = true)
    (queries : List PqSigningQuery)
    (hGeom : (inst.params.w = 4 ∧ inst.params.ell1 = 128) ∨
      (inst.params.w = 16 ∧ inst.params.ell1 = 64))
    (hStateless : inst.params.statefulJorts = false)
    (hLayers : inst.params.numLayers ≤ 2 ^ 32)
    (hFreshMsg : inst.message ∉
      (signingOracleLog inst.suite inst.params sk_i queries).map Prod.fst)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    let table0 := (view.allTables.headD []).headD []
    PSum (Sigma fun sig_i : PqHashSig =>
            HypertreeForgeryBreak inst.suite inst.params sk_i inst.message sig_i
              ((signingOracleLog inst.suite inst.params sk_i queries).flatMap fun e =>
                (List.range inst.params.forsTrees).map fun j =>
                  (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ inst.params.subtreeHeight),
                   e.2.leafGlobalIdx % 2 ^ inst.params.subtreeHeight,
                   sigForsLeafIdx inst.suite inst.params
                     (derivePublicKey inst.suite inst.params sk_i) e.1 e.2 j)))
      (PSum (SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
          (adaptivePolys (arith.honestRound table0) proof.agg.challenges)
          proof.agg.challenges)
        (PSum (HashCollisionWitness pcsMerkleHash)
          (PSum (WhirStageQueryMiss proof.finalWord dom view.allTables proof)
            (WhirProximityHit arith dom proof.finalWord view.allTables proof)))) :=
  match succinct_aggregation_signer_extraction arith dom inst law proof fs view
          hAccept hBound i hPk hB hActive_i with
  | .inr brk => .inr brk
  | .inl ⟨sig_i, hVer_i⟩ =>
    have hVerKey : verifyPqHashSig inst.suite inst.params
        (derivePublicKey inst.suite inst.params sk_i) inst.message sig_i = true := by
      rw [← hKey_i]; exact hVer_i
    .inl ⟨sig_i, extractReachableHypertreeForgery_of_statelessLog inst.suite inst.params sk_i
      queries inst.message sig_i hGeom hStateless hLayers hFreshMsg hVerKey⟩

/-- **Aggregation unforgeability against an executed checked stateful signing oracle
    (`qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog`, `0 Classical.choice`)**:
    the stateful counterpart of `qsag_aggregate_unforgeability_reduction_of_statelessLog`. Signer
    `i` runs `execCheckedStatefulOracle` from `initCheckedStatefulLatch` on the arbitrary query
    list `queries`; freshness is stated against the log that run emitted, and every oracle
    premise is discharged from it by `extractReachableHypertreeForgery_of_checkedStatefulLog`. -/
def qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog
    (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (i : Nat) (hPk : i < inst.committee.length) (hB : i < proof.agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : inst.committee[i]'hPk = derivePublicKey inst.suite inst.params sk_i)
    (hActive_i : proof.agg.bitmap[i]'hB = true)
    (queries : List CheckedStatefulQuery)
    (hGeom : (inst.params.w = 4 ∧ inst.params.ell1 = 128) ∨
      (inst.params.w = 16 ∧ inst.params.ell1 = 64))
    (hValidParams : inst.params.checkedStatefulValid = true)
    (hFreshMsg : inst.message ∉
      ((execCheckedStatefulOracle inst.suite inst.params sk_i initCheckedStatefulLatch
        queries).emittedLog.map fun e => e.2.1))
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    let table0 := (view.allTables.headD []).headD []
    PSum (Sigma fun sig_i : PqHashSig =>
            HypertreeForgeryBreak inst.suite inst.params sk_i inst.message sig_i [])
      (PSum (SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
          (adaptivePolys (arith.honestRound table0) proof.agg.challenges)
          proof.agg.challenges)
        (PSum (HashCollisionWitness pcsMerkleHash)
          (PSum (WhirStageQueryMiss proof.finalWord dom view.allTables proof)
            (WhirProximityHit arith dom proof.finalWord view.allTables proof)))) :=
  match succinct_aggregation_signer_extraction arith dom inst law proof fs view
          hAccept hBound i hPk hB hActive_i with
  | .inr brk => .inr brk
  | .inl ⟨sig_i, hVer_i⟩ =>
    have hVerKey : verifyPqHashSig inst.suite inst.params
        (derivePublicKey inst.suite inst.params sk_i) inst.message sig_i = true := by
      rw [← hKey_i]; exact hVer_i
    .inl ⟨sig_i, extractReachableHypertreeForgery_of_checkedStatefulLog inst.suite inst.params
      sk_i queries inst.message sig_i hGeom hValidParams hFreshMsg hVerKey⟩

/-- Extraction view tree matching `MergeNode`. -/
inductive SuccinctViewTree where
  | leaf (view : SuccinctExtractionView)
  | branch (view : SuccinctExtractionView) (left right : SuccinctViewTree)

def ViewTreeBound (dom : WhirDomain) : MergeNode → SuccinctViewTree → Prop
  | .leaf p _, .leaf v => StagesBound v.authPath dom.stages v.allTables p.stages
  | .branch p _ left right, .branch v vl vr =>
    StagesBound v.authPath dom.stages v.allTables p.stages ∧
    ViewTreeBound dom left vl ∧ ViewTreeBound dom right vr
  | _, _ => False

end Aggregation

/-- Node-by-node knowledge-soundness outcome across an entire recursive `MergeNode` tree. -/
@[expose] def SuccinctTreeOutcome (arith : Aggregation.RowArithmetization)
    (dom : Aggregation.WhirDomain) (inst : Aggregation.AggPublicInstance) :
    Aggregation.MergeNode → Aggregation.SuccinctViewTree → Type
  | .leaf p _, .leaf v => SuccinctOutcome arith dom inst p v
  | .branch p _ left right, .branch v vl vr =>
    SuccinctOutcome arith dom inst p v × SuccinctTreeOutcome arith dom inst left vl ×
      SuccinctTreeOutcome arith dom inst right vr
  | _, _ => PUnit

namespace Aggregation

theorem succinct_merge_tree_children_sound (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (budget : Nat) (p : SuccinctAggregateProof) (fs : List UInt8)
    (left right : MergeNode)
    (h : verifyMergeTree arith dom inst (budget + 1) (.branch p fs left right) = true) :
    verifyMergeTree arith dom inst budget left = true ∧
    verifyMergeTree arith dom inst budget right = true ∧
    p.agg.childrenCommitment =
      some (left.certificate.traceCommitment, right.certificate.traceCommitment) ∧
    bitmapDisjointSpec left.certificate.bitmap right.certificate.bitmap = true ∧
    p.agg.bitmap = bitmapUnionSpec left.certificate.bitmap right.certificate.bitmap ∧
    verifySuccinctAggregate arith dom inst p fs = true := by
  have h' : (decide (p.agg.childrenCommitment =
        some (left.certificate.traceCommitment, right.certificate.traceCommitment)) &&
      verifyMergeTree arith dom inst budget left &&
      verifyMergeTree arith dom inst budget right &&
      bitmapDisjointSpec left.certificate.bitmap right.certificate.bitmap &&
      decide (p.agg.bitmap = bitmapUnionSpec left.certificate.bitmap right.certificate.bitmap) &&
      verifySuccinctAggregate arith dom inst p fs) = true := h
  rcases Bool.and_eq_true_iff.mp h' with ⟨h', hNode⟩
  rcases Bool.and_eq_true_iff.mp h' with ⟨h', hUnion⟩
  rcases Bool.and_eq_true_iff.mp h' with ⟨h', hDisj⟩
  rcases Bool.and_eq_true_iff.mp h' with ⟨h', hRight⟩
  rcases Bool.and_eq_true_iff.mp h' with ⟨hComm, hLeft⟩
  exact ⟨hLeft, hRight, of_decide_eq_true hComm, hDisj, of_decide_eq_true hUnion, hNode⟩

/-- **Knowledge Soundness of Recursive Succinct Merge Trees (`succinct_merge_tree_knowledge_soundness`,
    `0 Classical.choice`)**:
    Every node of an accepted `MergeNode` tree constructively yields valid `PqHashSig` witnesses
    for all active signers or a concrete transcript-indexed WHIR break witness at that node. -/
def succinct_merge_tree_knowledge_soundness (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst) :
    ∀ (budget : Nat) (node : MergeNode) (views : SuccinctViewTree),
      verifyMergeTree arith dom inst budget node = true →
      ViewTreeBound dom node views → SuccinctTreeOutcome arith dom inst node views
  | 0, _, _, h, _ => False.elim (Bool.false_ne_true h)
  | _ + 1, .leaf p fs, .leaf v, h, hB =>
    succinct_aggregation_knowledge_soundness arith dom inst law p fs v
      (Bool.and_eq_true_iff.mp h).2 hB
  | _ + 1, .leaf _ _, .branch _ _ _, _, hB => False.elim hB
  | _ + 1, .branch _ _ _ _, .leaf _, _, hB => False.elim hB
  | budget + 1, .branch p fs left right, .branch v vl vr, h, hB =>
    have hU := succinct_merge_tree_children_sound arith dom inst budget p fs left right h
    (succinct_aggregation_knowledge_soundness arith dom inst law p fs v hU.2.2.2.2.2 hB.1,
      succinct_merge_tree_knowledge_soundness arith dom inst law budget left vl hU.1 hB.2.1,
      succinct_merge_tree_knowledge_soundness arith dom inst law budget right vr hU.2.1 hB.2.2)

/-- Propositional projection of `SuccinctOutcome`: either every active validator bit in
    `proof.agg.bitmap` decodes from the committed Round-0 codeword `table0` to a valid
    `verifyPqHashSig` signature, or one of the four transcript-indexed WHIR break witnesses
    is inhabited. -/
def SuccinctSoundOutcomeProp (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof)
    (view : SuccinctExtractionView) : Prop :=
  let table0 := (view.allTables.headD []).headD []
  checkAllActiveSigners inst.suite inst.params inst.message inst.committee
    proof.agg.bitmap (arith.decodeSigs table0) = true ∨
  Nonempty (SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
    (adaptivePolys (arith.honestRound table0) proof.agg.challenges)
    proof.agg.challenges) ∨
  Nonempty (HashCollisionWitness pcsMerkleHash) ∨
  Nonempty (WhirStageQueryMiss proof.finalWord dom view.allTables proof) ∨
  Nonempty (WhirProximityHit arith dom proof.finalWord view.allTables proof)

theorem succinctOutcome_to_prop {arith : RowArithmetization} {dom : WhirDomain}
    {inst : AggPublicInstance} {proof : SuccinctAggregateProof} {view : SuccinctExtractionView}
    (out : SuccinctOutcome arith dom inst proof view) :
    SuccinctSoundOutcomeProp arith dom inst proof view :=
  match out with
  | .inl ⟨_, hAll⟩ => .inl hAll
  | .inr (.inl hit) => .inr (.inl ⟨hit⟩)
  | .inr (.inr (.inl col)) => .inr (.inr (.inl ⟨col⟩))
  | .inr (.inr (.inr (.inl miss))) => .inr (.inr (.inr (.inl ⟨miss⟩)))
  | .inr (.inr (.inr (.inr prox))) => .inr (.inr (.inr (.inr ⟨prox⟩)))

/-- **`Prop` Knowledge Soundness of Multi-Stage `GoldilocksExt4` WHIR
    (`succinct_aggregation_knowledge_soundness_thm`)**:
    Proved directly by projecting the constructive `0 Classical.choice` `PSum` extractor
    `succinct_aggregation_knowledge_soundness`. -/
theorem succinct_aggregation_knowledge_soundness_thm (arith : RowArithmetization)
    (dom : WhirDomain) (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    SuccinctSoundOutcomeProp arith dom inst proof view :=
  succinctOutcome_to_prop
    (succinct_aggregation_knowledge_soundness arith dom inst law proof fs view hAccept hBound)

/-- Propositional projection of the end-to-end hypertree EUF-CMA + WHIR unforgeability reduction. -/
def SuccinctUnforgeabilityProp (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (sk_i : PqSecretKey)
    (revealedFors : List (UInt64 × Nat × Nat))
    (proof : SuccinctAggregateProof) (view : SuccinctExtractionView) : Prop :=
  let table0 := (view.allTables.headD []).headD []
  (∃ sig_i : PqHashSig,
    Nonempty (HypertreeForgeryBreak inst.suite inst.params sk_i inst.message sig_i revealedFors)) ∨
  Nonempty (SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
    (adaptivePolys (arith.honestRound table0) proof.agg.challenges)
    proof.agg.challenges) ∨
  Nonempty (HashCollisionWitness pcsMerkleHash) ∨
  Nonempty (WhirStageQueryMiss proof.finalWord dom view.allTables proof) ∨
  Nonempty (WhirProximityHit arith dom proof.finalWord view.allTables proof)

private theorem unforgeabilityOutcome_to_prop {arith : RowArithmetization} {dom : WhirDomain}
    {inst : AggPublicInstance} {sk_i : PqSecretKey}
    {revealedFors : List (UInt64 × Nat × Nat)}
    {proof : SuccinctAggregateProof} {view : SuccinctExtractionView}
    (out :
      let table0 := (view.allTables.headD []).headD []
      PSum (Sigma fun sig_i : PqHashSig =>
              HypertreeForgeryBreak inst.suite inst.params sk_i inst.message sig_i revealedFors)
        (PSum (SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
            (adaptivePolys (arith.honestRound table0) proof.agg.challenges)
            proof.agg.challenges)
          (PSum (HashCollisionWitness pcsMerkleHash)
            (PSum (WhirStageQueryMiss proof.finalWord dom view.allTables proof)
              (WhirProximityHit arith dom proof.finalWord view.allTables proof))))) :
    SuccinctUnforgeabilityProp arith dom inst sk_i revealedFors proof view :=
  match out with
  | .inl ⟨sig_i, brk⟩ => .inl ⟨sig_i, ⟨brk⟩⟩
  | .inr (.inl hit) => .inr (.inl ⟨hit⟩)
  | .inr (.inr (.inl col)) => .inr (.inr (.inl ⟨col⟩))
  | .inr (.inr (.inr (.inl miss))) => .inr (.inr (.inr (.inl ⟨miss⟩)))
  | .inr (.inr (.inr (.inr prox))) => .inr (.inr (.inr (.inr ⟨prox⟩)))

/-- **`Prop` End-to-End Succinct `GoldilocksExt4` WHIR Aggregation Unforgeability Reduction
    (`qsag_aggregate_unforgeability_reduction_thm`)**:
    Proved directly by projecting the constructive `0 Classical.choice` extractor
    `qsag_aggregate_unforgeability_reduction`. -/
theorem qsag_aggregate_unforgeability_reduction_thm
    (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (i : Nat) (hPk : i < inst.committee.length) (hB : i < proof.agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : inst.committee[i]'hPk = derivePublicKey inst.suite inst.params sk_i)
    (hActive_i : proof.agg.bitmap[i]'hB = true)
    (queriedMsgs : List (List UInt8))
    (qOracle : QueriedWotsOracle)
    (revealedFors : List (UInt64 × Nat × Nat))
    (hGeom : (inst.params.w = 4 ∧ inst.params.ell1 = 128) ∨
      (inst.params.w = 16 ∧ inst.params.ell1 = 64))
    (hFreshMsg : inst.message ∉ queriedMsgs)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages)
    (hStatefulLeaf0Msg : ∀ sig : PqHashSig, inst.params.statefulJorts = true →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        ∃ mPrev ∈ queriedMsgs,
          hRoot = thPreHash inst.suite sk_i.pkSeed
            (derivePublicKey inst.suite inst.params sk_i).pkRoot mPrev)
    (hStatelessLayer0Root : ∀ sig : PqHashSig, inst.params.statefulJorts = false →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        hRoot = computeForsPk inst.suite inst.params sk_i
          (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight))
    (hUpperOracle : ∀ (l : Nat) (g : Nat), ReachableUpperHypertreePos inst.params l g →
      let hRoot0 := computeXmssSubtreeRoot inst.suite inst.params sk_i
        (UInt32.ofNat (l - 1)) (UInt64.ofNat g)
      (∀ hRand hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot0, hCtr, hChains) →
        let hmH := thHashMsg inst.suite hRand sk_i.pkSeed
          (derivePublicKey inst.suite inst.params sk_i).pkRoot hRoot0
          (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (UInt32.ofNat (g % 2 ^ inst.params.subtreeHeight)) hCtr
        let digH := extractBaseWDigits inst.params.w inst.params.ell1 hmH
        checkTargetSum inst.params.w inst.params.ell1 inst.params.targetSum digH = true ∧
        recoverWotsPkFromSig inst.suite inst.params sk_i.pkSeed (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight) digH hChains =
        computeWotsPk inst.suite inst.params sk_i (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight)) ∧
      (∀ hRand hR hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight) = some (hRand, hR, hCtr, hChains) → hR = hRoot0))
    (hLayer0Valid : ∀ sig : PqHashSig, ∀ hRand hRoot0 hCtr hChains,
      qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot0, hCtr, hChains) →
      let hmH := thHashMsg inst.suite hRand sk_i.pkSeed
        (derivePublicKey inst.suite inst.params sk_i).pkRoot hRoot0
        0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight)) hCtr
      let digH := extractBaseWDigits inst.params.w inst.params.ell1 hmH
      checkTargetSum inst.params.w inst.params.ell1 inst.params.targetSum digH = true ∧
      recoverWotsPkFromSig inst.suite inst.params sk_i.pkSeed 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) digH hChains =
      computeWotsPk inst.suite inst.params sk_i 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight)) :
    SuccinctUnforgeabilityProp arith dom inst sk_i revealedFors proof view :=
  unforgeabilityOutcome_to_prop
    (qsag_aggregate_unforgeability_reduction arith dom inst law proof fs view i hPk hB sk_i hKey_i
      hActive_i queriedMsgs qOracle revealedFors hGeom hFreshMsg hAccept hBound
      hStatefulLeaf0Msg hStatelessLayer0Root hUpperOracle hLayer0Valid)

/-- **`Prop` Unforgeability Reduction Against an Executed Stateless Signing Oracle
    (`qsag_aggregate_unforgeability_reduction_of_statelessLog_thm`)**. -/
theorem qsag_aggregate_unforgeability_reduction_of_statelessLog_thm
    (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (i : Nat) (hPk : i < inst.committee.length) (hB : i < proof.agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : inst.committee[i]'hPk = derivePublicKey inst.suite inst.params sk_i)
    (hActive_i : proof.agg.bitmap[i]'hB = true)
    (queries : List PqSigningQuery)
    (hGeom : (inst.params.w = 4 ∧ inst.params.ell1 = 128) ∨
      (inst.params.w = 16 ∧ inst.params.ell1 = 64))
    (hStateless : inst.params.statefulJorts = false)
    (hLayers : inst.params.numLayers ≤ 2 ^ 32)
    (hFreshMsg : inst.message ∉
      (signingOracleLog inst.suite inst.params sk_i queries).map Prod.fst)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    SuccinctUnforgeabilityProp arith dom inst sk_i
      ((signingOracleLog inst.suite inst.params sk_i queries).flatMap fun e =>
        (List.range inst.params.forsTrees).map fun j =>
          (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ inst.params.subtreeHeight),
           e.2.leafGlobalIdx % 2 ^ inst.params.subtreeHeight,
           sigForsLeafIdx inst.suite inst.params
             (derivePublicKey inst.suite inst.params sk_i) e.1 e.2 j))
      proof view :=
  unforgeabilityOutcome_to_prop
    (qsag_aggregate_unforgeability_reduction_of_statelessLog arith dom inst law proof fs view
      i hPk hB sk_i hKey_i hActive_i queries hGeom hStateless hLayers hFreshMsg hAccept hBound)

/-- **`Prop` Unforgeability Reduction Against an Executed Checked Stateful Signing Oracle
    (`qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog_thm`)**. -/
theorem qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog_thm
    (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (i : Nat) (hPk : i < inst.committee.length) (hB : i < proof.agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : inst.committee[i]'hPk = derivePublicKey inst.suite inst.params sk_i)
    (hActive_i : proof.agg.bitmap[i]'hB = true)
    (queries : List CheckedStatefulQuery)
    (hGeom : (inst.params.w = 4 ∧ inst.params.ell1 = 128) ∨
      (inst.params.w = 16 ∧ inst.params.ell1 = 64))
    (hValidParams : inst.params.checkedStatefulValid = true)
    (hFreshMsg : inst.message ∉
      ((execCheckedStatefulOracle inst.suite inst.params sk_i initCheckedStatefulLatch
        queries).emittedLog.map fun e => e.2.1))
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    SuccinctUnforgeabilityProp arith dom inst sk_i [] proof view :=
  unforgeabilityOutcome_to_prop
    (qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog arith dom inst law proof fs view
      i hPk hB sk_i hKey_i hActive_i queries hGeom hValidParams hFreshMsg hAccept hBound)

theorem verifyMergeTree_bitmap_length (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (budget : Nat) (node : MergeNode)
    (h : verifyMergeTree arith dom inst budget node = true) :
    node.certificate.bitmap.length = inst.committee.length := by
  cases budget with
  | zero => cases h
  | succ b =>
    cases node with
    | leaf p fs =>
      have hAcc := (Bool.and_eq_true_iff.mp h).2
      exact (verifyAggregateAlgebra_facts inst.committee p.agg
        (succinct_acceptance_facts arith dom inst p fs hAcc).2.2.2.1).1
    | branch p fs left right =>
      have hAcc := (succinct_merge_tree_children_sound arith dom inst b p fs left right h).2.2.2.2.2
      exact (verifyAggregateAlgebra_facts inst.committee p.agg
        (succinct_acceptance_facts arith dom inst p fs hAcc).2.2.2.1).1

/-- Recursive propositional knowledge soundness + disjoint stake-popcount conservation across an
    entire accepted `MergeNode` tree. -/
def SuccinctMergeTreeSoundProp (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) : MergeNode → SuccinctViewTree → Prop
  | .leaf p _, .leaf v => SuccinctSoundOutcomeProp arith dom inst p v
  | .branch p _ left right, .branch v vl vr =>
    SuccinctSoundOutcomeProp arith dom inst p v ∧
    p.agg.childrenCommitment =
      some (left.certificate.traceCommitment, right.certificate.traceCommitment) ∧
    bitmapDisjointSpec left.certificate.bitmap right.certificate.bitmap = true ∧
    p.agg.bitmap = bitmapUnionSpec left.certificate.bitmap right.certificate.bitmap ∧
    bitmapPopcountSpec p.agg.bitmap =
      bitmapPopcountSpec left.certificate.bitmap + bitmapPopcountSpec right.certificate.bitmap ∧
    SuccinctMergeTreeSoundProp arith dom inst left vl ∧
    SuccinctMergeTreeSoundProp arith dom inst right vr
  | _, _ => False

/-- **`Prop` Knowledge Soundness & Stake Conservation of Recursive Succinct Merge Trees
    (`succinct_merge_tree_knowledge_soundness_thm`)**:
    Proved directly by combining the constructive `0 Classical.choice` extractor
    `succinct_merge_tree_knowledge_soundness` with `popcount_union_disjoint_eq_add` at every
    internal branch node. -/
theorem succinct_merge_tree_knowledge_soundness_thm (arith : RowArithmetization)
    (dom : WhirDomain) (inst : AggPublicInstance) (law : arith.Lawful dom inst) :
    ∀ (budget : Nat) (node : MergeNode) (views : SuccinctViewTree),
      verifyMergeTree arith dom inst budget node = true →
      ViewTreeBound dom node views →
      SuccinctMergeTreeSoundProp arith dom inst node views
  | 0, _, _, h, _ => False.elim (Bool.false_ne_true h)
  | b + 1, .leaf p fs, .leaf v, h, hB =>
    succinctOutcome_to_prop
      (succinct_merge_tree_knowledge_soundness arith dom inst law (b + 1) (.leaf p fs) (.leaf v) h hB)
  | _ + 1, .leaf _ _, .branch _ _ _, _, hB => False.elim hB
  | _ + 1, .branch _ _ _ _, .leaf _, _, hB => False.elim hB
  | budget + 1, .branch p fs left right, .branch v vl vr, h, hB => by
    have hTree := succinct_merge_tree_knowledge_soundness arith dom inst law
      (budget + 1) (.branch p fs left right) (.branch v vl vr) h hB
    have hU := succinct_merge_tree_children_sound arith dom inst budget p fs left right h
    have hLenL := verifyMergeTree_bitmap_length arith dom inst budget left hU.1
    have hLenR := verifyMergeTree_bitmap_length arith dom inst budget right hU.2.1
    have hPop : bitmapPopcountSpec p.agg.bitmap =
        bitmapPopcountSpec left.certificate.bitmap +
          bitmapPopcountSpec right.certificate.bitmap := by
      rw [hU.2.2.2.2.1]
      exact popcount_union_disjoint_eq_add left.certificate.bitmap right.certificate.bitmap
        (hLenL.trans hLenR.symm) hU.2.2.2.1
    exact ⟨succinctOutcome_to_prop hTree.1, hU.2.2.1, hU.2.2.2.1, hU.2.2.2.2.1, hPop,
      succinct_merge_tree_knowledge_soundness_thm arith dom inst law budget left vl hU.1 hB.2.1,
      succinct_merge_tree_knowledge_soundness_thm arith dom inst law budget right vr hU.2.1 hB.2.2⟩

end Aggregation

/-! ## 9. Adaptive Challenge-Vector & Falling-Factorial Query Counting Foundations -/

private theorem filter_const_false {α : Type} : ∀ (l : List α), l.filter (fun _ => false) = []
  | [] => rfl
  | _ :: xs => filter_const_false xs

theorem filter_length_le_self {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.filter p).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := filter_length_le_self p xs
    cases hp : p x
    · simp only [List.filter, hp, List.length_cons]; exact Nat.le_succ_of_le ih
    · simp only [List.filter, hp, List.length_cons]; exact Nat.succ_le_succ ih

theorem filter_flatMap_eq {α β : Type} (p : β → Bool) (f : α → List β) :
    ∀ (l : List α), (l.flatMap f).filter p = l.flatMap (fun x => (f x).filter p)
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.flatMap_cons, List.filter_append, filter_flatMap_eq p f xs]

theorem filter_map_length {α β : Type} (p : β → Bool) (f : α → β) :
    ∀ (l : List α), ((l.map f).filter p).length = (l.filter (fun x => p (f x))).length
  | [] => rfl
  | x :: xs => by
    have ih := filter_map_length p f xs
    cases hp : p (f x)
    · simp only [List.map, List.filter, hp]; exact ih
    · simp only [List.map, List.filter, hp, List.length_cons]; exact congrArg Nat.succ ih

private theorem length_flatMap_const {α β : Type} (k : Nat) (f : α → List β) :
    ∀ (l : List α), (∀ c ∈ l, (f c).length = k) → (l.flatMap f).length = l.length * k
  | [], _ => by show 0 = 0 * k; rw [Nat.zero_mul]
  | c :: l, h => by
    have ih := length_flatMap_const k f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc := h c (List.mem_cons_self ..)
    rw [List.flatMap_cons, List.length_append, ih, hc, List.length_cons, Nat.add_mul, Nat.one_mul,
      Nat.add_comm]

theorem length_flatMap_le_split {α β : Type} (b : α → Bool) (T M : Nat) (f : α → List β) :
    ∀ (l : List α), (∀ c ∈ l, (f c).length ≤ if b c = true then T else M) →
      (l.flatMap f).length ≤ (l.filter b).length * T + l.length * M
  | [], _ => Nat.zero_le _
  | c :: l, h => by
    have ih := length_flatMap_le_split b T M f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc := h c (List.mem_cons_self ..)
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    cases hb : b c
    · rw [hb] at hc; have _ : (f c).length ≤ M := hc
      simp only [List.filter, hb]; omega
    · rw [hb] at hc; have _ : (f c).length ≤ T := hc
      simp only [List.filter, hb, List.length_cons]; rw [Nat.add_mul, Nat.one_mul]; omega

/-- All length-`n` challenge vectors over `S`. -/
def challengeVectors {α : Type} (S : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => S.flatMap (fun r => (challengeVectors S n).map (fun rs => r :: rs))

theorem challengeVectors_zero {α : Type} (S : List α) : challengeVectors S 0 = [[]] := by rfl

theorem challengeVectors_succ {α : Type} (S : List α) (n : Nat) :
    challengeVectors S (n + 1) =
      S.flatMap (fun r => (challengeVectors S n).map (fun rs => r :: rs)) := by rfl

theorem challengeVectors_length {α : Type} (S : List α) :
    ∀ (n : Nat), (challengeVectors S n).length = S.length ^ n
  | 0 => rfl
  | n + 1 => by
    show (S.flatMap (fun r => (challengeVectors S n).map (fun rs => r :: rs))).length = _
    rw [length_flatMap_const (S.length ^ n) _ S
      (fun r _ => by rw [List.length_map, challengeVectors_length S n]),
      Nat.pow_succ, Nat.mul_comm]

def anyRoundEvent {α : Type} : (List α → α → Bool) → List α → Bool
  | _, [] => false
  | E, r :: rs => E [] r || anyRoundEvent (fun pre => E (r :: pre)) rs

def roundBoundSum : (Nat → Nat) → Nat → Nat
  | _, 0 => 0
  | d, n + 1 => d 0 + roundBoundSum (fun j => d (j + 1)) n

/-- **Adaptive Union Bound (`anyRoundEvent_count_le`)**:
    Over any challenge domain `S`, if each round `j` has at most `d j` bad challenges conditioned
    on any prefix, at most `(d 0 + ... + d (n - 1)) * |S|^(n - 1)` challenge vectors trigger `E`. -/
theorem anyRoundEvent_count_le {α : Type} (S : List α) :
    ∀ (n : Nat) (E : List α → α → Bool) (d : Nat → Nat),
      (∀ pre, (S.filter (E pre)).length ≤ d pre.length) →
      ((challengeVectors S n).filter (anyRoundEvent E)).length ≤
        roundBoundSum d n * S.length ^ (n - 1)
  | 0, E, _, _ => by
    show (([[]] : List (List α)).filter (anyRoundEvent E)).length ≤ _
    simp only [List.filter, anyRoundEvent]; exact Nat.zero_le _
  | n + 1, E, d, h => by
    show ((S.flatMap (fun r => (challengeVectors S n).map (fun rs => r :: rs))).filter
      (anyRoundEvent E)).length ≤ (d 0 + roundBoundSum (fun j => d (j + 1)) n) * S.length ^ (n + 1 - 1)
    rw [filter_flatMap_eq, Nat.add_sub_cancel]
    let M := roundBoundSum (fun j => d (j + 1)) n * S.length ^ (n - 1)
    have hEach : ∀ r ∈ S,
        (((challengeVectors S n).map (fun rs => r :: rs)).filter (anyRoundEvent E)).length ≤
          if E [] r = true then S.length ^ n else M := by
      intro r _
      rw [filter_map_length]
      cases hE : E [] r
      · have hfun : (fun rs => anyRoundEvent E (r :: rs)) =
            anyRoundEvent (fun pre => E (r :: pre)) := by
          funext rs; show (E [] r || anyRoundEvent (fun pre => E (r :: pre)) rs) = _
          rw [hE]; rfl
        rw [hfun]
        exact anyRoundEvent_count_le S n (fun pre => E (r :: pre)) (fun j => d (j + 1))
          (fun pre => h (r :: pre))
      · have hle := filter_length_le_self (fun rs => anyRoundEvent E (r :: rs)) (challengeVectors S n)
        rw [challengeVectors_length] at hle; exact hle
    have hSplit := length_flatMap_le_split (E []) (S.length ^ n) M
      (fun r => ((challengeVectors S n).map (fun rs => r :: rs)).filter (anyRoundEvent E)) S hEach
    have hA : (S.filter (E [])).length * S.length ^ n ≤ d 0 * S.length ^ n :=
      Nat.mul_le_mul_right _ (h [])
    have hB : S.length * M ≤ roundBoundSum (fun j => d (j + 1)) n * S.length ^ n := by
      cases n with
      | zero =>
        show S.length * (0 * S.length ^ (0 - 1)) ≤ _
        rw [Nat.zero_mul, Nat.mul_zero]; exact Nat.zero_le _
      | succ k =>
        show S.length * (roundBoundSum (fun j => d (j + 1)) (k + 1) * S.length ^ (k + 1 - 1)) ≤ _
        rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm S.length (S.length ^ k)]
        exact Nat.le_refl _
    rw [Nat.add_mul]
    exact Nat.le_trans hSplit (Nat.add_le_add hA hB)

def eraseFirstAt {α : Type} : Nat → List α → List α
  | _, [] => []
  | 0, _ :: xs => xs
  | i + 1, x :: xs => x :: eraseFirstAt i xs

theorem eraseFirstAt_length {α : Type} :
    ∀ (i : Nat) (l : List α), i < l.length → (eraseFirstAt i l).length = l.length - 1
  | 0, _ :: _, _ => rfl
  | _ + 1, [], h => absurd h (Nat.not_lt_zero _)
  | i + 1, _ :: xs, h => by
    have ih := eraseFirstAt_length i xs (Nat.lt_of_succ_lt_succ h)
    cases xs with
    | nil => exact absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
    | cons _ _ => exact congrArg Nat.succ ih

def countGood {α : Type} (p : α → Bool) (l : List α) : Nat := (l.filter p).length

theorem countGood_add_complement {α : Type} (p : α → Bool) :
    ∀ (l : List α), countGood p l + countGood (fun x => !p x) l = l.length
  | [] => rfl
  | x :: xs => by
    have ih := countGood_add_complement p xs
    cases hp : p x <;>
      simp only [countGood, List.filter, hp, Bool.not_true, Bool.not_false, List.length_cons] at ih ⊢ <;>
      omega

theorem countGood_eraseFirstAt_good {α : Type} (p : α → Bool) :
    ∀ (i : Nat) (l : List α) (hi : i < l.length), p (l[i]'hi) = true →
      countGood p (eraseFirstAt i l) + 1 = countGood p l
  | 0, x :: _, _, hx => by
    have hx' : p x = true := hx
    simp only [eraseFirstAt, countGood, List.filter, hx', List.length_cons]
  | i + 1, y :: xs, hi, hx => by
    have ih := countGood_eraseFirstAt_good p i xs (Nat.lt_of_succ_lt_succ hi) hx
    cases hpy : p y
    · simp only [eraseFirstAt, countGood, List.filter, hpy]
      exact ih
    · simp only [eraseFirstAt, countGood, List.filter, hpy, List.length_cons] at ih ⊢
      omega

/-- Ordered `q`-tuples drawn without replacement from `dom`. -/
def aggDistinctTuples {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | q + 1, dom =>
    (List.range dom.length).flatMap (fun i =>
      match dom[i]? with
      | none => []
      | some x => (aggDistinctTuples q (eraseFirstAt i dom)).map (fun rest => x :: rest))

def fallingFactorial : Nat → Nat → Nat
  | _, 0 => 1
  | n, q + 1 => n * fallingFactorial (n - 1) q

theorem fallingFactorial_pos : ∀ (n q : Nat), q ≤ n → 0 < fallingFactorial n q
  | _, 0, _ => Nat.one_pos
  | n, q + 1, h => by
    show 0 < n * fallingFactorial (n - 1) q
    exact Nat.mul_pos (Nat.lt_of_lt_of_le (Nat.succ_pos q) h)
      (fallingFactorial_pos (n - 1) q (Nat.le_sub_of_add_le h))

theorem fallingFactorial_of_lt : ∀ (n q : Nat), n < q → fallingFactorial n q = 0
  | 0, _ + 1, _ => Nat.zero_mul _
  | k + 1, q + 1, h => by
    show (k + 1) * fallingFactorial k q = 0
    rw [fallingFactorial_of_lt k q (Nat.lt_of_succ_lt_succ h), Nat.mul_zero]

theorem aggDistinctTuples_length {α : Type} :
    ∀ (q : Nat) (dom : List α),
      (aggDistinctTuples q dom).length = fallingFactorial dom.length q
  | 0, _ => rfl
  | q + 1, dom => by
    show ((List.range dom.length).flatMap _).length = dom.length * fallingFactorial (dom.length - 1) q
    have hEach : ∀ i ∈ List.range dom.length,
        (match dom[i]? with
          | none => []
          | some x => (aggDistinctTuples q (eraseFirstAt i dom)).map (fun rest => x :: rest)).length =
          fallingFactorial (dom.length - 1) q := by
      intro i hi
      have hlt : i < dom.length := List.mem_range.mp hi
      rw [List.getElem?_eq_getElem hlt, List.length_map, aggDistinctTuples_length q,
        eraseFirstAt_length i dom hlt]
    rw [length_flatMap_const _ _ (List.range dom.length) hEach, List.length_range]

private theorem range_filter_getElem_length {α : Type} (p : α → Bool) (dom : List α) :
    ((List.range dom.length).filter (fun i =>
      match dom[i]? with | none => false | some x => p x)).length = countGood p dom := by
  induction dom with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons]
    have h0 : (match (x :: xs)[0]? with | none => false | some y => p y) = p x := rfl
    have hS : ∀ j, (match (x :: xs)[j + 1]? with | none => false | some y => p y) =
        (match xs[j]? with | none => false | some y => p y) := fun _ => rfl
    rw [h0]
    have hm := filter_map_length
      (fun i => match (x :: xs)[i]? with | none => false | some y => p y) Nat.succ (List.range xs.length)
    simp only [hS] at hm
    cases hp : p x
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, countGood, List.filter]
      exact hm.trans ih
    · simp only [hp, ↓reduceIte, List.length_cons, countGood, List.filter]
      exact congrArg Nat.succ (hm.trans ih)

theorem aggDistinctTuples_all_good_length {α : Type} (p : α → Bool) :
    ∀ (q : Nat) (dom : List α),
      ((aggDistinctTuples q dom).filter (fun t => t.all p)).length =
        fallingFactorial (countGood p dom) q
  | 0, _ => rfl
  | q + 1, dom => by
    show (((List.range dom.length).flatMap _).filter (fun (t : List α) => t.all p)).length =
      countGood p dom * fallingFactorial (countGood p dom - 1) q
    rw [filter_flatMap_eq]
    let isGoodIdx : Nat → Bool := fun i => match dom[i]? with | none => false | some x => p x
    let F : Nat → List (List α) := fun i =>
      (match dom[i]? with
        | none => []
        | some x => (aggDistinctTuples q (eraseFirstAt i dom)).map (fun rest => x :: rest)).filter
          (fun t => t.all p)
    have hBadZero : ∀ i ∈ List.range dom.length, isGoodIdx i = false → (F i).length = 0 := by
      intro i hi hfg
      have hlt : i < dom.length := List.mem_range.mp hi
      have hpx : p (dom[i]'hlt) = false := by
        dsimp only [isGoodIdx] at hfg; rw [List.getElem?_eq_getElem hlt] at hfg; exact hfg
      dsimp only [F]
      rw [List.getElem?_eq_getElem hlt, filter_map_length]
      have hfun : (fun rest : List α => (dom[i] :: rest).all p) = fun _ => false := by
        funext rest; show (p dom[i] && rest.all p) = false; rw [hpx, Bool.false_and]
      rw [hfun, filter_const_false]; rfl
    have hGoodConst : ∀ i ∈ List.range dom.length, isGoodIdx i = true →
        (F i).length = fallingFactorial (countGood p dom - 1) q := by
      intro i hi hfg
      have hlt : i < dom.length := List.mem_range.mp hi
      have hpx : p (dom[i]'hlt) = true := by
        dsimp only [isGoodIdx] at hfg; rw [List.getElem?_eq_getElem hlt] at hfg; exact hfg
      dsimp only [F]
      rw [List.getElem?_eq_getElem hlt, filter_map_length]
      have hfun : (fun rest : List α => (dom[i] :: rest).all p) = fun rest => rest.all p := by
        funext rest; show (p dom[i] && rest.all p) = rest.all p; rw [hpx, Bool.true_and]
      rw [hfun, aggDistinctTuples_all_good_length p q (eraseFirstAt i dom)]
      have hcnt := countGood_eraseFirstAt_good p i dom hlt hpx
      have hsub : countGood p (eraseFirstAt i dom) = countGood p dom - 1 := by omega
      rw [hsub]
    have hLe := length_flatMap_le_split isGoodIdx (fallingFactorial (countGood p dom - 1) q) 0 F
      (List.range dom.length) (fun i hi => by
        cases hb : isGoodIdx i
        · rw [hBadZero i hi hb]; exact Nat.zero_le 0
        · rw [hGoodConst i hi hb]; exact Nat.le_refl _)
    rw [Nat.mul_zero, Nat.add_zero, range_filter_getElem_length] at hLe
    have hGe : countGood p dom * fallingFactorial (countGood p dom - 1) q ≤
        ((List.range dom.length).flatMap F).length := by
      have hSub : ((List.range dom.length).filter isGoodIdx).flatMap F =
          (List.range dom.length).flatMap (fun i => if isGoodIdx i then F i else []) := by
        induction (List.range dom.length) with
        | nil => rfl
        | cons a as ih =>
          cases hb : isGoodIdx a <;> simp [List.filter, hb, ih]
      have hEqLen : (((List.range dom.length).filter isGoodIdx).flatMap F).length =
          countGood p dom * fallingFactorial (countGood p dom - 1) q := by
        rw [length_flatMap_const (fallingFactorial (countGood p dom - 1) q) F
          ((List.range dom.length).filter isGoodIdx)
          (fun i hi => by
            have hm := List.mem_filter.mp hi
            exact hGoodConst i hm.1 hm.2),
          range_filter_getElem_length]
      rw [← hEqLen, hSub]
      have hEqAll : ∀ l : List Nat, (∀ i ∈ l, isGoodIdx i = false → F i = []) →
          (l.flatMap (fun i => if isGoodIdx i then F i else [])).length = (l.flatMap F).length := by
        intro l hl
        induction l with
        | nil => rfl
        | cons a as ih =>
          cases hb : isGoodIdx a
          · rw [List.flatMap_cons, List.flatMap_cons, hl a (.head _) hb]
            simp [hb, ih (fun i hi => hl i (.tail _ hi))]
          · simp [hb, ih (fun i hi => hl i (.tail _ hi))]
      rw [hEqAll (List.range dom.length) (fun i hi hb =>
        List.eq_nil_of_length_eq_zero (hBadZero i hi hb))]
      exact Nat.le_refl _
    exact Nat.le_antisymm hLe hGe

private theorem fallingFactorial_mul_pow_le (a b : Nat) (hab : a ≤ b) :
    ∀ (q g n : Nat), g ≤ n → b * g ≤ a * n →
      fallingFactorial g q * b ^ q ≤ a ^ q * fallingFactorial n q
  | 0, _, _, _, _ => by
    show 1 * 1 ≤ 1 * 1; exact Nat.le_refl 1
  | q + 1, g, n, hgn, hbg => by
    rcases Nat.eq_zero_or_pos g with rfl | hgpos
    · simp only [fallingFactorial, Nat.zero_mul]
      exact Nat.zero_le _
    · have h1 : b * (g - 1) ≤ a * (n - 1) := by
        rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one, Nat.mul_one]
        omega
      have ih := fallingFactorial_mul_pow_le a b hab q (g - 1) (n - 1)
        (Nat.sub_le_sub_right hgn 1) h1
      show g * fallingFactorial (g - 1) q * (b ^ q * b) ≤
        a ^ q * a * (n * fallingFactorial (n - 1) q)
      have lhsEq : g * fallingFactorial (g - 1) q * (b ^ q * b) =
          (b * g) * (fallingFactorial (g - 1) q * b ^ q) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have rhsEq : a ^ q * a * (n * fallingFactorial (n - 1) q) =
          (a * n) * (a ^ q * fallingFactorial (n - 1) q) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [lhsEq, rhsEq]
      exact Nat.mul_le_mul hbg ih

/-- **General Without-Replacement Query-Miss Bound (`whir_query_miss_bound`)**:
    Whenever `bad` has relative density at least `dn / dd`, the count of `q`-query tuples missing
    `bad` entirely satisfies `missCount * dd ^ q ≤ (dd - dn) ^ q * totalTuples`. -/
theorem whir_query_miss_bound {α : Type} (bad : α → Bool) (dom : List α) (q dn dd : Nat)
    (hfar : dn * dom.length ≤ dd * countGood bad dom) :
    ((aggDistinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length * dd ^ q ≤
      (dd - dn) ^ q * (aggDistinctTuples q dom).length := by
  rw [aggDistinctTuples_all_good_length, aggDistinctTuples_length]
  have hsum := countGood_add_complement bad dom
  have hGN : countGood (fun x => !bad x) dom ≤ dom.length := by omega
  apply fallingFactorial_mul_pow_le (dd - dn) dd (Nat.sub_le dd dn) q _ _ hGN
  rw [Nat.sub_mul]
  have e : dd * dom.length = dd * countGood (fun x => !bad x) dom + dd * countGood bad dom := by
    rw [← Nat.mul_add, Nat.add_comm, hsum]
  omega

/-! ## 10. Transcript-Bound WHIR Proximity, OOD, Fold & Query Soundness (`GoldilocksExt4`) -/

namespace Aggregation

/-- Tracked committed coset duet over `GoldilocksExt4`. -/
structure TrackedDuetExt4 where
  v0 : GoldilocksExt4
  v1 : GoldilocksExt4
  invTwoY0 : Goldilocks
  invTwo : Goldilocks
  next : GoldilocksExt4

def foldDuetExt4Event (d : TrackedDuetExt4) (r : GoldilocksExt4) : Bool :=
  (decide (foldDuetExt4 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.zero ≠ d.next) ||
    decide (foldDuetExt4 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.one ≠ d.next)) &&
  decide (foldDuetExt4 d.v0 d.v1 d.invTwoY0 d.invTwo r = d.next)

theorem foldDuetExt4Event_roots_le_one (d : TrackedDuetExt4) (S : List GoldilocksExt4)
    (hS : S.Nodup) : (S.filter (foldDuetExt4Event d)).length ≤ 1 := by
  cases hg : (decide (foldDuetExt4 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.zero ≠ d.next) ||
      decide (foldDuetExt4 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.one ≠ d.next)) with
  | false =>
    have hfun : foldDuetExt4Event d = fun _ => false := by
      funext r; unfold foldDuetExt4Event; rw [hg]; rfl
    rw [hfun, filter_const_false]; exact Nat.zero_le 1
  | true =>
    have hfun : foldDuetExt4Event d =
        fun r => decide (foldDuetExt4 d.v0 d.v1 d.invTwoY0 d.invTwo r = d.next) := by
      funext r; unfold foldDuetExt4Event; rw [hg]; rfl
    rw [hfun]
    have hne : ∃ r, foldDuetExt4 d.v0 d.v1 d.invTwoY0 d.invTwo r ≠ d.next := by
      cases h0 : decide (foldDuetExt4 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.zero ≠ d.next) with
      | true => exact ⟨_, of_decide_eq_true h0⟩
      | false => rw [h0] at hg; exact ⟨_, of_decide_eq_true hg⟩
    exact whir_coset_duet_ext4_roots_le_one d.v0 d.v1 d.next d.invTwoY0 d.invTwo S hS hne

private theorem filter_or_length_le {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (l.filter (fun x => p x || q x)).length ≤
      (l.filter p).length + (l.filter q).length
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := filter_or_length_le p q xs
    cases hp : p x <;> cases hq : q x <;>
      simp only [List.filter, hp, hq, Bool.or_self, Bool.or_true, Bool.or_false,
        List.length_cons] <;> omega

private theorem filter_any_length_le {α β : Type} (S : List α) (ev : β → α → Bool) (k : Nat) :
    ∀ (ds : List β), (∀ d ∈ ds, (S.filter (ev d)).length ≤ k) →
      (S.filter (fun r => ds.any (fun d => ev d r))).length ≤ ds.length * k
  | [], _ => by
    show (S.filter (fun _ => false)).length ≤ _
    rw [filter_const_false]; exact Nat.zero_le _
  | d :: ds, h => by
    have ih := filter_any_length_le S ev k ds (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hd := h d (List.mem_cons_self ..)
    have hor := filter_or_length_le (ev d) (fun r => ds.any (fun d => ev d r)) S
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    have hor' : (S.filter (fun r => (d :: ds).any (fun d => ev d r))).length ≤
        (S.filter (ev d)).length + (S.filter (fun r => ds.any (fun d => ev d r))).length := hor
    omega

/-- Tracked pair of unequal list-decoded WHIR polynomials of degree `≤ maxDeg` tested by `z_ood`. -/
structure TrackedOodPair (maxDeg : Nat) where
  candA : List GoldilocksExt4
  candB : List GoldilocksExt4
  lenA : candA.length ≤ maxDeg + 1
  lenB : candB.length ≤ maxDeg + 1
  witnessPt : GoldilocksExt4

def oodPairEvent {maxDeg : Nat} (p : TrackedOodPair maxDeg) (z : GoldilocksExt4) : Bool :=
  decide (RoundPoly.evalCoeffs p.candA p.witnessPt ≠ RoundPoly.evalCoeffs p.candB p.witnessPt) &&
  decide (RoundPoly.evalCoeffs p.candA z = RoundPoly.evalCoeffs p.candB z)

theorem oodPairEvent_roots_le {maxDeg : Nat} (p : TrackedOodPair maxDeg)
    (S : List GoldilocksExt4) (hS : S.Nodup) :
    (S.filter (oodPairEvent p)).length ≤ maxDeg := by
  cases hg : decide (RoundPoly.evalCoeffs p.candA p.witnessPt ≠
      RoundPoly.evalCoeffs p.candB p.witnessPt) with
  | false =>
    have hfun : oodPairEvent p = fun _ => false := by
      funext z; unfold oodPairEvent; rw [hg]; rfl
    rw [hfun, filter_const_false]; exact Nat.zero_le _
  | true =>
    have hfun : oodPairEvent p =
        fun z => decide (RoundPoly.evalCoeffs p.candA z = RoundPoly.evalCoeffs p.candB z) := by
      funext z; unfold oodPairEvent; rw [hg, Bool.true_and]
    rw [hfun]
    exact whir_ood_pin_roots_le_degree maxDeg p.candA p.candB S hS p.lenA p.lenB
      ⟨p.witnessPt, of_decide_eq_true hg⟩

/-- **OOD List-Pinning Multi-Stage Challenge Bound (`whir_ood_hit_challenges_le`)**:
    Across `n` WHIR stages with at most `pairsPerStage` list-decoding candidate pairs of degree
    `≤ maxDeg` per stage, at most `n * (pairsPerStage * maxDeg) * |S|^(n - 1)` OOD challenge
    vectors suffer a list-pinning collision. -/
theorem whir_ood_hit_challenges_le (maxDeg : Nat) (S : List GoldilocksExt4) (hS : S.Nodup)
    (n pairsPerStage : Nat)
    (tracked : List GoldilocksExt4 → List (TrackedOodPair maxDeg))
    (hPairs : ∀ pre, (tracked pre).length ≤ pairsPerStage) :
    ((challengeVectors S n).filter
      (anyRoundEvent (fun pre z => (tracked pre).any (fun p => oodPairEvent p z)))).length ≤
      roundBoundSum (fun _ => pairsPerStage * maxDeg) n * S.length ^ (n - 1) := by
  apply anyRoundEvent_count_le S n _ (fun _ => pairsPerStage * maxDeg)
  intro pre
  exact Nat.le_trans
    (filter_any_length_le S oodPairEvent maxDeg (tracked pre)
      (fun p _ => oodPairEvent_roots_le p S hS))
    (Nat.mul_le_mul_right maxDeg (hPairs pre))

private theorem strict_query_miss_from_slack {α : Type} (bad : α → Bool) (dom : List α)
    (q alphaNum den b : Nat)
    (hdom : q ≤ dom.length)
    (hle : alphaNum ≤ den)
    (hfar : (den - alphaNum) * dom.length ≤ den * countGood bad dom)
    (hSlack : alphaNum ^ q * 2 ^ b < den ^ q) :
    ((aggDistinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length * 2 ^ b <
      (aggDistinctTuples q dom).length := by
  have hb := whir_query_miss_bound bad dom q (den - alphaNum) den hfar
  have hSub : den - (den - alphaNum) = alphaNum := by omega
  rw [hSub] at hb
  have hT : 0 < (aggDistinctTuples q dom).length := by
    rw [aggDistinctTuples_length]; exact fallingFactorial_pos _ _ hdom
  rcases Nat.lt_or_ge
    (((aggDistinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length * 2 ^ b)
    (aggDistinctTuples q dom).length with hlt | hge
  · exact hlt
  · exfalso
    generalize ((aggDistinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length = X at hb hge
    generalize (aggDistinctTuples q dom).length = T at hb hge hT
    generalize alphaNum ^ q = M at hb hSlack
    generalize den ^ q = K at hb hSlack
    have hX : 0 < X := by
      cases X with
      | zero => rw [Nat.zero_mul] at hge; exact absurd hT (Nat.not_lt.mpr hge)
      | succ k => exact Nat.succ_pos k
    have h1 : M * T ≤ M * (X * 2 ^ b) := Nat.mul_le_mul_left M hge
    have h2 : M * (X * 2 ^ b) = X * (M * 2 ^ b) := Nat.mul_left_comm M X (2 ^ b)
    have h3 : X * (M * 2 ^ b) < X * K := Nat.mul_lt_mul_of_pos_left hSlack hX
    rw [h2] at h1
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h3 (Nat.le_trans hb h1))

/-- **Unconditional `[BCIKS20]` Classical-128 Per-Stage Query Bound
    (`whir_bciksJohnsonClassical128_query_miss_lt`)**:
    For EVERY stage `s ∈ whirSchedule4Stage .bciksJohnsonClassical128` (`q = (129, 65, 44, 33)`),
    whenever `bad` has relative density `≥ 1 - (1 / √B_s + 1 / 512)` (positive proximity slack
    `η = 1 / 512 > 0`, finite Johnson list size `L ≤ 256`), fewer than a `2^-128` fraction of
    distinct query tuples miss `bad`. -/
theorem whir_bciksJohnsonClassical128_query_miss_lt {α : Type}
    (s : WhirStageSpec) (hs : s ∈ whirSchedule4Stage .bciksJohnsonClassical128)
    (bad : α → Bool) (dom : List α)
    (hdom : s.numQueries ≤ dom.length)
    (hfar : (512 - (512 / s.johnsonSqrtBlowup + 1)) * dom.length ≤ 512 * countGood bad dom) :
    ((aggDistinctTuples s.numQueries dom).filter (fun t => t.all (fun x => !bad x))).length *
      2 ^ 128 < (aggDistinctTuples s.numQueries dom).length := by
  have hSlack := (bciksJohnsonClassical128_positive_slack s hs).2
  have hAllLe : ∀ st ∈ whirSchedule4Stage .bciksJohnsonClassical128,
      512 / st.johnsonSqrtBlowup + 1 ≤ 512 := by decide
  exact strict_query_miss_from_slack bad dom s.numQueries
    (512 / s.johnsonSqrtBlowup + 1) 512 128 hdom (hAllLe s hs) hfar hSlack

/-- **Unconditional `[BCIKS20]` QROM-128 Per-Stage Query Bound
    (`whir_bciksJohnsonQrom128_query_miss_lt`)**:
    For EVERY stage `s ∈ whirSchedule4Stage .bciksJohnsonQrom128` (`q = (258, 130, 88, 66)`),
    whenever `bad` has relative density `≥ 1 - (1 / √B_s + 1 / 1024)` (positive proximity slack
    `η = 1 / 1024 > 0`, finite Johnson list size `L ≤ 512`), fewer than a `2^-256` fraction of
    distinct query tuples miss `bad` (`+ 16`b PoW = `136` QROM Grover bits). -/
theorem whir_bciksJohnsonQrom128_query_miss_lt {α : Type}
    (s : WhirStageSpec) (hs : s ∈ whirSchedule4Stage .bciksJohnsonQrom128)
    (bad : α → Bool) (dom : List α)
    (hdom : s.numQueries ≤ dom.length)
    (hfar : (1024 - (1024 / s.johnsonSqrtBlowup + 1)) * dom.length ≤ 1024 * countGood bad dom) :
    ((aggDistinctTuples s.numQueries dom).filter (fun t => t.all (fun x => !bad x))).length *
      2 ^ 256 < (aggDistinctTuples s.numQueries dom).length := by
  have hSlack := (bciksJohnsonQrom128_positive_slack s hs).2
  have hAllLe : ∀ st ∈ whirSchedule4Stage .bciksJohnsonQrom128,
      1024 / st.johnsonSqrtBlowup + 1 ≤ 1024 := by decide
  exact strict_query_miss_from_slack bad dom s.numQueries
    (1024 / s.johnsonSqrtBlowup + 1) 1024 256 hdom (hAllLe s hs) hfar hSlack

/-- **Per-stage query bound in every regime, at the regime's own target.** For every stage of
    every one of the six regimes, if `bad` has relative density at least
    `1 - (1 / √B_s + 1 / r.slackDen)`, fewer than a `2^-(r.pureQueryTargetBits)` fraction of
    distinct query tuples miss `bad`. The exponent is `128, 256, 200, 214, 200, 214` for tags
    `2, 4, 5, 6, 7, 8`; no common 128-bit Grover figure follows from it. -/
theorem whir_regime_query_miss_lt {α : Type} (r : WhirSecurityRegime)
    (s : WhirStageSpec) (hs : s ∈ whirSchedule4Stage r)
    (bad : α → Bool) (dom : List α)
    (hdom : s.numQueries ≤ dom.length)
    (hfar : (r.slackDen - (r.slackDen / s.johnsonSqrtBlowup + 1)) * dom.length ≤
      r.slackDen * countGood bad dom) :
    ((aggDistinctTuples s.numQueries dom).filter (fun t => t.all (fun x => !bad x))).length *
      2 ^ r.pureQueryTargetBits < (aggDistinctTuples s.numQueries dom).length := by
  obtain ⟨_, hSlack, hLe, _⟩ := whirRegime_positive_slack r s hs
  exact strict_query_miss_from_slack bad dom s.numQueries
    (r.slackDen / s.johnsonSqrtBlowup + 1) r.slackDen r.pureQueryTargetBits hdom hLe hfar hSlack

private theorem length_flatMap_scaled_le {α β : Type} (b : α → Bool) (K U V : Nat)
    (f : α → List β) :
    ∀ (l : List α), (∀ c ∈ l, (f c).length * K ≤ if b c = true then U else V) →
      (l.flatMap f).length * K ≤ (l.filter b).length * U + l.length * V
  | [], _ => by show 0 * K ≤ _; rw [Nat.zero_mul]; exact Nat.zero_le _
  | c :: l, h => by
    have ih := length_flatMap_scaled_le b K U V f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc := h c (List.mem_cons_self ..)
    rw [List.flatMap_cons, List.length_append, Nat.add_mul, List.length_cons,
      Nat.add_mul l.length 1 V, Nat.one_mul]
    cases hb : b c
    · rw [hb] at hc; have _ : (f c).length * K ≤ V := hc
      simp only [List.filter, hb]; omega
    · rw [hb] at hc; have _ : (f c).length * K ≤ U := hc
      simp only [List.filter, hb, List.length_cons]; rw [Nat.add_mul, Nat.one_mul]; omega

def badTranscriptPairs {α β : Type} (S : List α) (n : Nat) (E : List α → α → Bool)
    (dom : List β) (q : Nat) (bad : List α → β → Bool) : List (List α × List β) :=
  (challengeVectors S n).flatMap (fun cs =>
    ((aggDistinctTuples q dom).filter
      (fun t => anyRoundEvent E cs || t.all (fun x => !bad cs x))).map (fun t => (cs, t)))

theorem transcript_bad_pairs_le {α β : Type} (S : List α) (n : Nat)
    (E : List α → α → Bool) (d : Nat → Nat)
    (hE : ∀ pre, (S.filter (E pre)).length ≤ d pre.length)
    (dom : List β) (q dn dd : Nat) (bad : List α → β → Bool)
    (hfar : ∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
      dn * dom.length ≤ dd * countGood (bad cs) dom) :
    (badTranscriptPairs S n E dom q bad).length * dd ^ q ≤
      (roundBoundSum d n * S.length ^ (n - 1) * dd ^ q + S.length ^ n * (dd - dn) ^ q) *
        (aggDistinctTuples q dom).length := by
  have hEach : ∀ cs ∈ challengeVectors S n,
      (((aggDistinctTuples q dom).filter
        (fun t => anyRoundEvent E cs || t.all (fun x => !bad cs x))).map
          (fun t => (cs, t))).length * dd ^ q ≤
        if anyRoundEvent E cs = true then (aggDistinctTuples q dom).length * dd ^ q
        else (dd - dn) ^ q * (aggDistinctTuples q dom).length := by
    intro cs hcs
    rw [List.length_map]
    cases hEv : anyRoundEvent E cs
    · exact whir_query_miss_bound (bad cs) dom q dn dd (hfar cs hcs hEv)
    · exact Nat.mul_le_mul_right _ (filter_length_le_self _ _)
  have hSplit := length_flatMap_scaled_le (anyRoundEvent E) (dd ^ q)
    ((aggDistinctTuples q dom).length * dd ^ q) ((dd - dn) ^ q * (aggDistinctTuples q dom).length)
    (fun cs => ((aggDistinctTuples q dom).filter
      (fun t => anyRoundEvent E cs || t.all (fun x => !bad cs x))).map (fun t => (cs, t)))
    (challengeVectors S n) hEach
  have hCnt := anyRoundEvent_count_le S n E d hE
  rw [challengeVectors_length] at hSplit
  refine Nat.le_trans hSplit ?_
  rw [Nat.add_mul]
  apply Nat.add_le_add
  · have h1 := Nat.mul_le_mul_right ((aggDistinctTuples q dom).length * dd ^ q) hCnt
    have e : roundBoundSum d n * S.length ^ (n - 1) * ((aggDistinctTuples q dom).length * dd ^ q) =
        roundBoundSum d n * S.length ^ (n - 1) * dd ^ q * (aggDistinctTuples q dom).length := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [e] at h1; exact h1
  · exact Nat.le_of_eq (Nat.mul_assoc _ _ _).symm

private theorem error_arith (X D A s M K T c : Nat)
    (h1 : X * K ≤ (D * A * K + s * A * M) * T)
    (hD : 2 * (D * c) ≤ s) (hM : 2 * (M * c) < K)
    (hA : 0 < A) (hT : 0 < T) (hs : 0 < s) : X * c < s * A * T := by
  rcases Nat.lt_or_ge (X * c) (s * A * T) with hlt | hge
  · exact hlt
  · exfalso
    have hP : 0 < s * A * T := Nat.mul_pos (Nat.mul_pos hs hA) hT
    have e1 : 2 * c * ((D * A * K + s * A * M) * T) =
        2 * (D * c) * (A * K * T) + 2 * (M * c) * (s * A * T) := by
      rw [Nat.add_mul, Nat.mul_add]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h1' : 2 * c * (X * K) ≤ 2 * (D * c) * (A * K * T) + 2 * (M * c) * (s * A * T) := by
      rw [← e1]; exact Nat.mul_le_mul_left _ h1
    have h2 : 2 * (D * c) * (A * K * T) ≤ K * (s * A * T) := by
      have h := Nat.mul_le_mul_right (A * K * T) hD
      have e : s * (A * K * T) = K * (s * A * T) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      rw [e] at h; exact h
    have h3 : 2 * (M * c) * (s * A * T) < K * (s * A * T) := Nat.mul_lt_mul_of_pos_right hM hP
    have h4 : 2 * (K * (s * A * T)) ≤ 2 * c * (X * K) := by
      have h := Nat.mul_le_mul_left (2 * K) hge
      have e : 2 * K * (X * c) = 2 * c * (X * K) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e, Nat.mul_assoc] at h; exact h
    have h5 := Nat.lt_of_le_of_lt (Nat.le_trans h4 h1') (Nat.add_lt_add_of_le_of_lt h2 h3)
    rw [Nat.two_mul] at h5
    exact Nat.lt_irrefl _ h5

/-- Production `GoldilocksExt4` WHIR challenge-event budget covering 20 degree-8 row-sumcheck
    rounds, 20 degree-2 shift-sumcheck rounds (`MAX_PCS_NUM_VARS = 28`), 4 OOD list-pinning stages (`L ≤ 512`, `d ≤ 2^24`),
    and parameterized `[BCIKS20]` correlated-agreement events (`≤ 2^44`, leaving `> 210` bits over
    `p^4 > 2^255`). -/
def productionExt4RoundEventBudget : Nat :=
  productionAggParams.maxRowRounds * productionAggParams.rowSumcheckDegree +
  productionAggParams.maxFoldRounds * productionAggParams.pcsSumcheckDegree +
  2 ^ 44

/-- **Joint `GoldilocksExt4` WHIR Unconditional `[BCIKS20]` Classical-128 Transcript Soundness
    (`whir_bciksJohnsonClassical128_total_error_bound`)**:
    Over `S : List GoldilocksExt4` (`p^4 ≤ S.length`), with challenge events bounded by
    `productionExt4RoundEventBudget` (`< 2^-210`) and Stage-0 `BciksJohnsonClassical128` queries
    (`q_0 = 129`, `η = 1 / 512 > 0`), the total bad `(challengeVector, queryTuple)` fraction is
    strictly `< 2^-127` (`< 2^-210 + 2^-128`). -/
theorem whir_bciksJohnsonClassical128_total_error_bound {β : Type}
    (S : List GoldilocksExt4) (n : Nat) (hn : 0 < n)
    (E : List GoldilocksExt4 → GoldilocksExt4 → Bool) (d : Nat → Nat)
    (hE : ∀ pre, (S.filter (E pre)).length ≤ d pre.length)
    (hBudget : roundBoundSum d n ≤ productionExt4RoundEventBudget)
    (hField : productionAggParams.fieldSize ≤ S.length)
    (dom : List β) (hdom : 129 ≤ dom.length)
    (bad : List GoldilocksExt4 → β → Bool)
    (hfar : ∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
      (512 - 257) * dom.length ≤ 512 * countGood (bad cs) dom) :
    (badTranscriptPairs S n E dom 129 bad).length * 2 ^ 127 <
      S.length ^ n * (aggDistinctTuples 129 dom).length := by
  have hJoint := transcript_bad_pairs_le S n E d hE dom 129 (512 - 257) 512 bad hfar
  have hSub : 512 - (512 - 257) = 257 := rfl
  rw [hSub] at hJoint
  have hT : 0 < (aggDistinctTuples 129 dom).length := by
    rw [aggDistinctTuples_length]; exact fallingFactorial_pos _ _ hdom
  have hField' : goldilocksPrime ^ 4 ≤ S.length := hField
  have hs : 0 < S.length := Nat.lt_of_lt_of_le (by decide : 0 < goldilocksPrime ^ 4) hField'
  have hC : 2 * (productionExt4RoundEventBudget * 2 ^ 127) ≤ goldilocksPrime ^ 4 := by decide
  have hM : 2 * (257 ^ 129 * 2 ^ 127) < 512 ^ 129 := by decide
  have hD : 2 * (roundBoundSum d n * 2 ^ 127) ≤ S.length :=
    Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2 ^ 127) hBudget))
      (Nat.le_trans hC hField')
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ k =>
    have hpow : S.length ^ (k + 1) = S.length * S.length ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [Nat.add_sub_cancel, hpow] at hJoint
    rw [hpow]
    exact error_arith _ _ _ _ _ _ _ _ hJoint hD hM (Nat.pow_pos hs) hT hs

/-- **Joint `GoldilocksExt4` WHIR Unconditional `[BCIKS20]` QROM-128 Multi-Stage Transcript
    Soundness (`whir_bciksJohnsonQrom128_total_error_bound`)**:
    For EVERY stage `s ∈ whirSchedule4Stage .bciksJohnsonQrom128` (`q = (258, 130, 88, 66)`,
    positive Johnson proximity slack `η = 1 / 1024 > 0`, list size `L ≤ 512`), over any
    `S : List GoldilocksExt4` (`p^4 ≤ S.length`) with challenge events bounded by
    `productionExt4RoundEventBudget` (`< 2^-211`), the joint bad `(challengeVector, queryTuple)`
    fraction is strictly `< 2^-210` (`< 2^-211 + 2^-256`, yielding `> 128` QROM bits against
    `Q_RO ≤ 2^40` challenge queries and `16`-bit PoW Grover query grinding). -/
theorem whir_bciksJohnsonQrom128_total_error_bound {β : Type}
    (s : WhirStageSpec) (hs : s ∈ whirSchedule4Stage .bciksJohnsonQrom128)
    (S : List GoldilocksExt4) (n : Nat) (hn : 0 < n)
    (E : List GoldilocksExt4 → GoldilocksExt4 → Bool) (d : Nat → Nat)
    (hE : ∀ pre, (S.filter (E pre)).length ≤ d pre.length)
    (hBudget : roundBoundSum d n ≤ productionExt4RoundEventBudget)
    (hField : productionAggParams.fieldSize ≤ S.length)
    (dom : List β) (hdom : s.numQueries ≤ dom.length)
    (bad : List GoldilocksExt4 → β → Bool)
    (hfar : ∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
      (1024 - (1024 / s.johnsonSqrtBlowup + 1)) * dom.length ≤ 1024 * countGood (bad cs) dom) :
    (badTranscriptPairs S n E dom s.numQueries bad).length * 2 ^ 210 <
      S.length ^ n * (aggDistinctTuples s.numQueries dom).length := by
  have hAllLe : ∀ st ∈ whirSchedule4Stage .bciksJohnsonQrom128,
      1024 / st.johnsonSqrtBlowup + 1 ≤ 1024 := by decide
  have hLe : 1024 / s.johnsonSqrtBlowup + 1 ≤ 1024 := hAllLe s hs
  have hSub : 1024 - (1024 - (1024 / s.johnsonSqrtBlowup + 1)) =
      1024 / s.johnsonSqrtBlowup + 1 := Nat.sub_sub_self hLe
  have hJoint := transcript_bad_pairs_le S n E d hE dom s.numQueries
    (1024 - (1024 / s.johnsonSqrtBlowup + 1)) 1024 bad hfar
  rw [hSub] at hJoint
  have hT : 0 < (aggDistinctTuples s.numQueries dom).length := by
    rw [aggDistinctTuples_length]; exact fallingFactorial_pos _ _ hdom
  have hField' : goldilocksPrime ^ 4 ≤ S.length := hField
  have hsPos : 0 < S.length := Nat.lt_of_lt_of_le (by decide : 0 < goldilocksPrime ^ 4) hField'
  have hC : 2 * (productionExt4RoundEventBudget * 2 ^ 210) ≤ goldilocksPrime ^ 4 := by decide
  have hSlack := (bciksJohnsonQrom128_positive_slack s hs).2
  have hM : 2 * ((1024 / s.johnsonSqrtBlowup + 1) ^ s.numQueries * 2 ^ 210) <
      1024 ^ s.numQueries := by
    have hPowLe : 2 * 2 ^ 210 ≤ 2 ^ 256 := by decide
    have hRewrite : 2 * ((1024 / s.johnsonSqrtBlowup + 1) ^ s.numQueries * 2 ^ 210) =
        (1024 / s.johnsonSqrtBlowup + 1) ^ s.numQueries * (2 * 2 ^ 210) := by
      simp only [Nat.mul_assoc, Nat.mul_comm]
    rw [hRewrite]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hPowLe) hSlack
  have hD : 2 * (roundBoundSum d n * 2 ^ 210) ≤ S.length :=
    Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2 ^ 210) hBudget))
      (Nat.le_trans hC hField')
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ k =>
    have hpow : S.length ^ (k + 1) = S.length * S.length ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [Nat.add_sub_cancel, hpow] at hJoint
    rw [hpow]
    exact error_arith _ _ _ _ _ _ _ _ hJoint hD hM (Nat.pow_pos hsPos) hT hsPos

/-- Concrete duplicate-free `List GoldilocksExt4` sample of size `k` (eliminating `List Unit`). -/
def canonicalExt4Sample (k : Nat) : List GoldilocksExt4 :=
  (List.range k).map (fun i => GoldilocksExt4.embedBase (Goldilocks.ofNat i))

theorem canonicalExt4Sample_length (k : Nat) : (canonicalExt4Sample k).length = k := by
  simp [canonicalExt4Sample]

theorem canonicalExt4Sample_nodup {k : Nat} (hk : k ≤ goldilocksPrime) :
    (canonicalExt4Sample k).Nodup := by
  unfold canonicalExt4Sample
  have hRange := nodup_range_constructive k
  have hInjOn : ∀ a b, a < k → b < k →
      GoldilocksExt4.embedBase (Goldilocks.ofNat a) =
      GoldilocksExt4.embedBase (Goldilocks.ofNat b) → a = b := by
    intro a b ha hb hEq
    have hBase := GoldilocksExt4.embedBase_injective hEq
    have hVal := congrArg Goldilocks.val hBase
    simp only [Goldilocks.ofNat_val] at hVal
    rwa [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha hk),
         Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb hk)] at hVal
  have hAux : ∀ {xs : List Nat}, xs.Nodup → (∀ z ∈ xs, z < k) →
      (xs.map (fun i => GoldilocksExt4.embedBase (Goldilocks.ofNat i))).Nodup := by
    intro xs hnd hlt
    induction hnd with
    | nil => exact .nil
    | @cons x rest hrel hndRest ih =>
      refine .cons (fun b hb heq => ?_) (ih (fun z hz => hlt z (.tail _ hz)))
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      exact hrel y hy (hInjOn x y (hlt x (.head _)) (hlt y (.tail _ hy)) heq)
  exact hAux hRange (fun z hz => List.mem_range.mp hz)

private theorem countGood_lt_range (m : Nat) :
    ∀ (n : Nat), countGood (fun i => decide (i < m)) (List.range n) = min m n
  | 0 => by simp [countGood]
  | n + 1 => by
    rw [countGood, List.range_succ, List.filter_append, List.length_append]
    have ih : (List.filter (fun i => decide (i < m)) (List.range n)).length = min m n :=
      countGood_lt_range m n
    rw [ih]
    by_cases hlt : n < m <;> simp [hlt] <;> omega

/-- Non-`Unit` `GoldilocksExt4` + positive-slack `[BCIKS20]` satisfiability witness. -/
theorem whir_bciksJohnson_hypotheses_satisfiable :
    ∃ (S : List GoldilocksExt4) (s : WhirStageSpec) (dom : List Nat) (bad : Nat → Bool),
      S.Nodup ∧ 256 ≤ S.length ∧
      s ∈ whirSchedule4Stage .bciksJohnsonClassical128 ∧
      s.numQueries ≤ dom.length ∧
      (512 - (512 / s.johnsonSqrtBlowup + 1)) * dom.length ≤ 512 * countGood bad dom ∧
      countGood bad dom < dom.length := by
  refine ⟨canonicalExt4Sample 256, ⟨0, 4, 2, 129, 16⟩, List.range 512, fun i => decide (i < 255),
    canonicalExt4Sample_nodup (by decide), by simp [canonicalExt4Sample_length],
    by decide, by simp, ?_, ?_⟩
  · rw [countGood_lt_range, List.length_range, Nat.min_eq_left (by omega : 255 ≤ 512)]
    dsimp only
    omega
  · rw [countGood_lt_range, List.length_range, Nat.min_eq_left (by omega : 255 ≤ 512)]
    omega

/-! ## 10b. The squeezed challenge is weighted, not uniform

`squeezeExt4Challenge` reads 32 XOF bytes as four 64-bit words and reduces each mod
`p = 2^64 - 2^32 + 1`. Uniform bytes therefore give the uniform distribution on the `2^256`
word quadruples `wordQuadPool`, and a field element `z` receives exactly
`ext4WordMultiplicity z ≤ 16` of them (`wordQuadPool_fiber_length`; `0` receives 16). The bounds
of §4 and §10 count over a duplicate-free list `S` of field elements, i.e. a uniform field
challenge. This section restates each of them over `wordQuadPool`: an event hit by at most `d`
field elements is hit by at most `16 * d` of the `2^256` word quadruples
(`squeezed_event_count_le`), so every `d / p^4` becomes `16 * d / 2^256`. -/

/-- The four words of a 32-byte string, big-endian, in limb order `c0.c0, c0.c1, c1.c0, c1.c1`. -/
def wordsOfBytes32 (bytes : List UInt8) : Nat × Nat × Nat × Nat :=
  (ofBE (bytes.take 8), ofBE ((bytes.drop 8).take 8), ofBE ((bytes.drop 16).take 8),
    ofBE ((bytes.drop 24).take 8))

/-- The four 64-bit words `squeezeExt4Challenge` reduces. -/
def squeezeExt4Words (domainTag frame : List UInt8) : Nat × Nat × Nat × Nat :=
  wordsOfBytes32 (cshake256Bytes domainTag frame)

/-- The squeezed challenge is the limbwise reduction of the squeezed words. -/
theorem squeezeExt4Challenge_eq_ofWordQuad (domainTag frame : List UInt8) :
    squeezeExt4Challenge domainTag frame = ofWordQuad (squeezeExt4Words domainTag frame) :=
  (ofWordQuad_mk _ _ _ _).symm

private theorem ofBE_take8_lt (bs : List UInt8) : ofBE (bs.take 8) < 2 ^ 64 := by
  have hl : (bs.take 8).length ≤ 8 := by
    rw [List.length_take]; exact Nat.min_le_left 8 _
  exact Nat.lt_of_lt_of_le (ofBE_lt (bs.take 8))
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) hl) (by decide))

theorem wordsOfBytes32_mem (bytes : List UInt8) : wordsOfBytes32 bytes ∈ wordQuadPool :=
  mem_wordQuadPool.mpr ⟨ofBE_take8_lt _, ofBE_take8_lt _, ofBE_take8_lt _, ofBE_take8_lt _⟩

theorem squeezeExt4Words_mem (domainTag frame : List UInt8) :
    squeezeExt4Words domainTag frame ∈ wordQuadPool :=
  wordsOfBytes32_mem _

/-- 32 bytes are recovered from their four words: `wordsOfBytes32` is injective on 32-byte
    strings. -/
theorem wordsOfBytes32_bytes (bytes : List UInt8) (hLen : bytes.length = 32) :
    be 8 (wordsOfBytes32 bytes).1 ++ (be 8 (wordsOfBytes32 bytes).2.1 ++
      (be 8 (wordsOfBytes32 bytes).2.2.1 ++ be 8 (wordsOfBytes32 bytes).2.2.2)) = bytes := by
  have h0 : (bytes.take 8).length = 8 := by rw [List.length_take, hLen]; rfl
  have h1 : ((bytes.drop 8).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hLen]; rfl
  have h2 : ((bytes.drop 16).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hLen]; rfl
  have h3 : ((bytes.drop 24).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hLen]; rfl
  have e0 := be_ofBE (bytes.take 8)
  have e1 := be_ofBE ((bytes.drop 8).take 8)
  have e2 := be_ofBE ((bytes.drop 16).take 8)
  have e3 := be_ofBE ((bytes.drop 24).take 8)
  rw [h0] at e0; rw [h1] at e1; rw [h2] at e2; rw [h3] at e3
  show be 8 (ofBE (bytes.take 8)) ++ (be 8 (ofBE ((bytes.drop 8).take 8)) ++
    (be 8 (ofBE ((bytes.drop 16).take 8)) ++ be 8 (ofBE ((bytes.drop 24).take 8)))) = bytes
  rw [e0, e1, e2, e3]
  have t3 : (bytes.drop 24).take 8 = bytes.drop 24 :=
    List.take_of_length_le (by rw [List.length_drop, hLen]; decide)
  have d16 : bytes.drop 24 = (bytes.drop 16).drop 8 := by rw [List.drop_drop]
  have d8 : bytes.drop 16 = (bytes.drop 8).drop 8 := by rw [List.drop_drop]
  rw [t3, d16, List.take_append_drop, d8, List.take_append_drop, List.take_append_drop]

/-- Every word quadruple is the reading of a 32-byte string: with `wordsOfBytes32_bytes`,
    32-byte strings and `wordQuadPool` are in bijection. -/
theorem wordsOfBytes32_surjective (q : Nat × Nat × Nat × Nat) (hq : q ∈ wordQuadPool) :
    ∃ bytes : List UInt8, bytes.length = 32 ∧ wordsOfBytes32 bytes = q := by
  obtain ⟨h0, h1, h2, h3⟩ := mem_wordQuadPool.mp hq
  have hb : ∀ {w : Nat}, w < 2 ^ 64 → w < 256 ^ 8 := fun h => Nat.lt_of_lt_of_le h (by decide)
  obtain ⟨w0, w1, w2, w3⟩ := q
  refine ⟨be 8 w0 ++ (be 8 w1 ++ (be 8 w2 ++ be 8 w3)), by simp [length_be], ?_⟩
  have t0 : (be 8 w0 ++ (be 8 w1 ++ (be 8 w2 ++ be 8 w3))).take 8 = be 8 w0 :=
    List.take_left' (length_be 8 w0)
  have d8 : (be 8 w0 ++ (be 8 w1 ++ (be 8 w2 ++ be 8 w3))).drop 8 =
      be 8 w1 ++ (be 8 w2 ++ be 8 w3) := List.drop_left' (length_be 8 w0)
  have d16 : (be 8 w0 ++ (be 8 w1 ++ (be 8 w2 ++ be 8 w3))).drop 16 = be 8 w2 ++ be 8 w3 := by
    have h16 : (16 : Nat) = 8 + 8 := rfl
    rw [h16, ← List.drop_drop, d8, List.drop_left' (length_be 8 w1)]
  have d24 : (be 8 w0 ++ (be 8 w1 ++ (be 8 w2 ++ be 8 w3))).drop 24 = be 8 w3 := by
    have h24 : (24 : Nat) = 16 + 8 := rfl
    rw [h24, ← List.drop_drop, d16, List.drop_left' (length_be 8 w2)]
  show (ofBE ((be 8 w0 ++ (be 8 w1 ++ (be 8 w2 ++ be 8 w3))).take 8),
    ofBE (((be 8 w0 ++ (be 8 w1 ++ (be 8 w2 ++ be 8 w3))).drop 8).take 8),
    ofBE (((be 8 w0 ++ (be 8 w1 ++ (be 8 w2 ++ be 8 w3))).drop 16).take 8),
    ofBE (((be 8 w0 ++ (be 8 w1 ++ (be 8 w2 ++ be 8 w3))).drop 24).take 8)) = (w0, w1, w2, w3)
  rw [t0, d8, d16, d24, List.take_left' (length_be 8 w1), List.take_left' (length_be 8 w2),
    List.take_of_length_le (Nat.le_of_eq (length_be 8 w3)),
    ofBE_be (hb h0), ofBE_be (hb h1), ofBE_be (hb h2), ofBE_be (hb h3)]

/-- **Uniform-to-squeezed transfer.** If an event is hit by at most `d` elements of every
    duplicate-free list of field elements, it is hit by at most `16 * d` of the `2^256` word
    quadruples. The factor is the maximal preimage multiplicity `ext4WordMultiplicity 0 = 16`. -/
theorem squeezed_event_count_le (E : GoldilocksExt4 → Bool) (d : Nat)
    (hE : ∀ T : List GoldilocksExt4, T.Nodup → (T.filter E).length ≤ d) :
    (wordQuadPool.filter (fun q => E (ofWordQuad q))).length ≤ 16 * d := by
  have hfamE : ∀ fam : List GoldilocksExt4, (∀ z ∈ fam, E z = true) → fam.filter E = fam := by
    intro fam
    induction fam with
    | nil => intro _; rfl
    | cons z tl ih =>
      intro h
      rw [List.filter_cons, ite_eq_left (h z (.head _)),
        ih (fun y hy => h y (.tail _ hy))]
  have hmemE : ∀ z ∈ JohnsonBound.dedupFirst
      ((wordQuadPool.filter (fun q => E (ofWordQuad q))).map ofWordQuad), E z = true := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((JohnsonBound.mem_dedupFirst_iff z _).mp hz)
    exact (List.mem_filter.mp hq).2
  have hfam := hE _ (JohnsonBound.dedupFirst_nodup
    ((wordQuadPool.filter (fun q => E (ofWordQuad q))).map ofWordQuad))
  rw [hfamE _ hmemE] at hfam
  have hpart := JohnsonBound.count_partition_le ofWordQuad 16
    (wordQuadPool.filter (fun q => E (ofWordQuad q)))
    (JohnsonBound.dedupFirst ((wordQuadPool.filter (fun q => E (ofWordQuad q))).map ofWordQuad))
    (fun q hq => (JohnsonBound.mem_dedupFirst_iff _ _).mpr (List.mem_map.mpr ⟨q, hq, rfl⟩))
    (fun z _ => by
      rw [List.filter_filter]
      exact Nat.le_trans
        (filter_sub_length_le _ (fun q => decide (ofWordQuad q = z))
          (fun q h => (Bool.and_eq_true_iff.mp h).1) wordQuadPool)
        (wordQuadPool_fiber_le_sixteen z))
  rw [Nat.mul_comm] at hpart
  exact Nat.le_trans hpart (Nat.mul_le_mul_left 16 hfam)

/-- Squeezed form of `ext4_poly_roots_le_degree`: two distinct polynomials of degree at most
    `maxDegree` agree at the reduction of at most `16 * maxDegree` of the `2^256` word
    quadruples. -/
theorem ext4_poly_squeezed_roots_le (maxDegree : Nat)
    (claimedPoly honestPoly : List GoldilocksExt4)
    (hLenC : claimedPoly.length ≤ maxDegree + 1) (hLenH : honestPoly.length ≤ maxDegree + 1)
    (hDiff : ∃ x₀ : GoldilocksExt4,
      RoundPoly.evalCoeffs claimedPoly x₀ ≠ RoundPoly.evalCoeffs honestPoly x₀) :
    (wordQuadPool.filter (fun q =>
      decide (RoundPoly.evalCoeffs claimedPoly (ofWordQuad q) =
        RoundPoly.evalCoeffs honestPoly (ofWordQuad q)))).length ≤ 16 * maxDegree :=
  squeezed_event_count_le
    (fun r => decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r))
    maxDegree
    (fun T hT => ext4_poly_roots_le_degree maxDegree claimedPoly honestPoly T hT hLenC hLenH hDiff)

/-- Squeezed form of `sumcheck_degree8_ext4_roots_le_eight`: `128 / 2^256` per round. -/
theorem sumcheck_degree8_squeezed_roots_le
    (claimedPoly honestPoly : List GoldilocksExt4)
    (hLenC : claimedPoly.length ≤ 9) (hLenH : honestPoly.length ≤ 9)
    (hDiff : ∃ x₀ : GoldilocksExt4,
      RoundPoly.evalCoeffs claimedPoly x₀ ≠ RoundPoly.evalCoeffs honestPoly x₀) :
    (wordQuadPool.filter (fun q =>
      decide (RoundPoly.evalCoeffs claimedPoly (ofWordQuad q) =
        RoundPoly.evalCoeffs honestPoly (ofWordQuad q)))).length ≤ 128 :=
  ext4_poly_squeezed_roots_le 8 claimedPoly honestPoly hLenC hLenH hDiff

/-- Squeezed form of `whir_ood_pin_roots_le_degree`: `16 * d / 2^256` per candidate pair. -/
theorem whir_ood_pin_squeezed_roots_le (d : Nat)
    (candA candB : List GoldilocksExt4)
    (hLenA : candA.length ≤ d + 1) (hLenB : candB.length ≤ d + 1)
    (hDiff : ∃ z₀ : GoldilocksExt4,
      RoundPoly.evalCoeffs candA z₀ ≠ RoundPoly.evalCoeffs candB z₀) :
    (wordQuadPool.filter (fun q =>
      decide (RoundPoly.evalCoeffs candA (ofWordQuad q) =
        RoundPoly.evalCoeffs candB (ofWordQuad q)))).length ≤ 16 * d :=
  ext4_poly_squeezed_roots_le d candA candB hLenA hLenB hDiff

/-- Squeezed form of `whir_coset_duet_ext4_roots_le_one`: at most 16 of the `2^256` word
    quadruples fold a cheated duet onto the claimed next-layer value. -/
theorem whir_coset_duet_squeezed_roots_le
    (v0 v1 next : GoldilocksExt4) (invTwoY0 invTwo : Goldilocks)
    (hne : ∃ r, foldDuetExt4 v0 v1 invTwoY0 invTwo r ≠ next) :
    (wordQuadPool.filter (fun q =>
      decide (foldDuetExt4 v0 v1 invTwoY0 invTwo (ofWordQuad q) = next))).length ≤ 16 :=
  squeezed_event_count_le
    (fun r => decide (foldDuetExt4 v0 v1 invTwoY0 invTwo r = next)) 1
    (fun T hT => whir_coset_duet_ext4_roots_le_one v0 v1 next invTwoY0 invTwo T hT hne)

theorem foldDuetExt4Event_squeezed_le (d : TrackedDuetExt4) :
    (wordQuadPool.filter (fun q => foldDuetExt4Event d (ofWordQuad q))).length ≤ 16 :=
  squeezed_event_count_le (foldDuetExt4Event d) 1
    (fun T hT => foldDuetExt4Event_roots_le_one d T hT)

theorem oodPairEvent_squeezed_le {maxDeg : Nat} (p : TrackedOodPair maxDeg) :
    (wordQuadPool.filter (fun q => oodPairEvent p (ofWordQuad q))).length ≤ 16 * maxDeg :=
  squeezed_event_count_le (oodPairEvent p) maxDeg (fun T hT => oodPairEvent_roots_le p T hT)

/-- A round event on reduced challenges, read on the words. -/
theorem anyRoundEvent_map {α β : Type} (f : α → β) :
    ∀ (cs : List α) (E : List β → β → Bool),
      anyRoundEvent (fun pre x => E (pre.map f) (f x)) cs = anyRoundEvent E (cs.map f)
  | [], _ => rfl
  | r :: rs, E => by
    show (E [] (f r) || anyRoundEvent (fun pre x => E (f r :: pre.map f) (f x)) rs) =
      (E [] (f r) || anyRoundEvent (fun pre => E (f r :: pre)) (rs.map f))
    rw [← anyRoundEvent_map f rs (fun pre => E (f r :: pre))]

theorem roundBoundSum_mul (c : Nat) :
    ∀ (n : Nat) (d : Nat → Nat), roundBoundSum (fun j => c * d j) n = c * roundBoundSum d n
  | 0, _ => (Nat.mul_zero c).symm
  | n + 1, d => by
    show c * d 0 + roundBoundSum (fun j => c * d (j + 1)) n =
      c * (d 0 + roundBoundSum (fun j => d (j + 1)) n)
    rw [roundBoundSum_mul c n (fun j => d (j + 1)), Nat.mul_add]

/-- **Adaptive union bound for squeezed challenges.** If round `j` has at most `d j` bad field
    elements after any prefix, at most `16 * (d 0 + … + d (n-1)) * (2^256)^(n-1)` of the
    `(2^256)^n` word-quadruple vectors trigger a round event. -/
theorem squeezed_anyRoundEvent_count_le (n : Nat)
    (E : List GoldilocksExt4 → GoldilocksExt4 → Bool) (d : Nat → Nat)
    (hE : ∀ (pre T : List GoldilocksExt4), T.Nodup → (T.filter (E pre)).length ≤ d pre.length) :
    ((challengeVectors wordQuadPool n).filter
      (fun qs => anyRoundEvent E (qs.map ofWordQuad))).length ≤
      16 * roundBoundSum d n * (2 ^ 256) ^ (n - 1) := by
  have hfun : (fun qs : List (Nat × Nat × Nat × Nat) => anyRoundEvent E (qs.map ofWordQuad)) =
      anyRoundEvent (fun pre q => E (pre.map ofWordQuad) (ofWordQuad q)) := by
    funext qs
    exact (anyRoundEvent_map ofWordQuad qs E).symm
  have h := anyRoundEvent_count_le wordQuadPool n
    (fun pre q => E (pre.map ofWordQuad) (ofWordQuad q)) (fun j => 16 * d j)
    (fun pre => by
      have hp := squeezed_event_count_le (E (pre.map ofWordQuad)) (d (pre.map ofWordQuad).length)
        (hE (pre.map ofWordQuad))
      rw [List.length_map] at hp
      exact hp)
  rw [roundBoundSum_mul, wordQuadPool_length] at h
  rw [hfun]
  exact h

/-- Squeezed form of `whir_ood_hit_challenges_le`. -/
theorem whir_ood_hit_squeezed_challenges_le (maxDeg n pairsPerStage : Nat)
    (tracked : List GoldilocksExt4 → List (TrackedOodPair maxDeg))
    (hPairs : ∀ pre, (tracked pre).length ≤ pairsPerStage) :
    ((challengeVectors wordQuadPool n).filter (fun qs =>
      anyRoundEvent (fun pre z => (tracked pre).any (fun p => oodPairEvent p z))
        (qs.map ofWordQuad))).length ≤
      16 * roundBoundSum (fun _ => pairsPerStage * maxDeg) n * (2 ^ 256) ^ (n - 1) :=
  squeezed_anyRoundEvent_count_le n
    (fun pre z => (tracked pre).any (fun p => oodPairEvent p z)) (fun _ => pairsPerStage * maxDeg)
    (fun pre T hT => Nat.le_trans
      (filter_any_length_le T oodPairEvent maxDeg (tracked pre)
        (fun p _ => oodPairEvent_roots_le p T hT))
      (Nat.mul_le_mul_right maxDeg (hPairs pre)))

private theorem squeezed_total_error {β : Type} (n : Nat) (hn : 0 < n)
    (E : List GoldilocksExt4 → GoldilocksExt4 → Bool) (d : Nat → Nat)
    (hE : ∀ (pre T : List GoldilocksExt4), T.Nodup → (T.filter (E pre)).length ≤ d pre.length)
    (dom : List β) (q dn dd c B : Nat) (bad : List GoldilocksExt4 → β → Bool)
    (hfar : ∀ qs ∈ challengeVectors wordQuadPool n,
      anyRoundEvent E (qs.map ofWordQuad) = false →
        dn * dom.length ≤ dd * countGood (bad (qs.map ofWordQuad)) dom)
    (hq : q ≤ dom.length) (hBudget : roundBoundSum d n ≤ B)
    (hC : 2 * (16 * B * c) ≤ 2 ^ 256) (hM : 2 * ((dd - dn) ^ q * c) < dd ^ q) :
    (badTranscriptPairs wordQuadPool n (fun pre w => E (pre.map ofWordQuad) (ofWordQuad w))
      dom q (fun qs => bad (qs.map ofWordQuad))).length * c <
      (2 ^ 256) ^ n * (aggDistinctTuples q dom).length := by
  have hE' : ∀ pre : List (Nat × Nat × Nat × Nat),
      (wordQuadPool.filter (fun w => E (pre.map ofWordQuad) (ofWordQuad w))).length ≤
        16 * d pre.length := by
    intro pre
    have hp := squeezed_event_count_le (E (pre.map ofWordQuad)) (d (pre.map ofWordQuad).length)
      (hE (pre.map ofWordQuad))
    rw [List.length_map] at hp
    exact hp
  have hJoint := transcript_bad_pairs_le wordQuadPool n
    (fun pre w => E (pre.map ofWordQuad) (ofWordQuad w)) (fun j => 16 * d j) hE' dom q dn dd
    (fun qs => bad (qs.map ofWordQuad))
    (fun qs hqs hev => hfar qs hqs ((anyRoundEvent_map ofWordQuad qs E).symm.trans hev))
  have hT : 0 < (aggDistinctTuples q dom).length := by
    rw [aggDistinctTuples_length]; exact fallingFactorial_pos _ _ hq
  have hs : 0 < wordQuadPool.length := by rw [wordQuadPool_length]; decide
  have hD : 2 * (roundBoundSum (fun j => 16 * d j) n * c) ≤ wordQuadPool.length := by
    rw [roundBoundSum_mul, wordQuadPool_length]
    exact Nat.le_trans
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right c (Nat.mul_le_mul_left 16 hBudget))) hC
  rw [← wordQuadPool_length]
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ k =>
    have hpow : wordQuadPool.length ^ (k + 1) = wordQuadPool.length * wordQuadPool.length ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [Nat.add_sub_cancel, hpow] at hJoint
    rw [hpow]
    exact error_arith _ _ _ _ _ _ _ _ hJoint hD hM (Nat.pow_pos hs) hT hs

/-- **Classical-128 transcript soundness for squeezed challenges.** The statement of
    `whir_bciksJohnsonClassical128_total_error_bound` over the `(2^256)^n` word-quadruple
    vectors the transcript really samples, with per-round bad counts `d` given for field
    elements. The factor 16 is absorbed: the bad fraction is still `< 2^-127`. -/
theorem whir_bciksJohnsonClassical128_squeezed_total_error_bound {β : Type}
    (n : Nat) (hn : 0 < n)
    (E : List GoldilocksExt4 → GoldilocksExt4 → Bool) (d : Nat → Nat)
    (hE : ∀ (pre T : List GoldilocksExt4), T.Nodup → (T.filter (E pre)).length ≤ d pre.length)
    (hBudget : roundBoundSum d n ≤ productionExt4RoundEventBudget)
    (dom : List β) (hdom : 129 ≤ dom.length)
    (bad : List GoldilocksExt4 → β → Bool)
    (hfar : ∀ qs ∈ challengeVectors wordQuadPool n,
      anyRoundEvent E (qs.map ofWordQuad) = false →
        (512 - 257) * dom.length ≤ 512 * countGood (bad (qs.map ofWordQuad)) dom) :
    (badTranscriptPairs wordQuadPool n (fun pre w => E (pre.map ofWordQuad) (ofWordQuad w))
      dom 129 (fun qs => bad (qs.map ofWordQuad))).length * 2 ^ 127 <
      (2 ^ 256) ^ n * (aggDistinctTuples 129 dom).length :=
  squeezed_total_error n hn E d hE dom 129 (512 - 257) 512 (2 ^ 127)
    productionExt4RoundEventBudget bad hfar hdom hBudget (by decide) (by decide)

/-- **QROM-128 multi-stage transcript soundness for squeezed challenges.** Over the word
    quadruples the transcript really samples, the bound of
    `whir_bciksJohnsonQrom128_total_error_bound` holds with `2^-206` in place of `2^-210`: the
    challenge-event term is `16 * productionExt4RoundEventBudget / 2^256 < 2^-207`. `2^-210`
    is not provable from this budget (`squeezed_budget_exceeds_two_pow_neg_210`). -/
theorem whir_bciksJohnsonQrom128_squeezed_total_error_bound {β : Type}
    (s : WhirStageSpec) (hs : s ∈ whirSchedule4Stage .bciksJohnsonQrom128)
    (n : Nat) (hn : 0 < n)
    (E : List GoldilocksExt4 → GoldilocksExt4 → Bool) (d : Nat → Nat)
    (hE : ∀ (pre T : List GoldilocksExt4), T.Nodup → (T.filter (E pre)).length ≤ d pre.length)
    (hBudget : roundBoundSum d n ≤ productionExt4RoundEventBudget)
    (dom : List β) (hdom : s.numQueries ≤ dom.length)
    (bad : List GoldilocksExt4 → β → Bool)
    (hfar : ∀ qs ∈ challengeVectors wordQuadPool n,
      anyRoundEvent E (qs.map ofWordQuad) = false →
        (1024 - (1024 / s.johnsonSqrtBlowup + 1)) * dom.length ≤
          1024 * countGood (bad (qs.map ofWordQuad)) dom) :
    (badTranscriptPairs wordQuadPool n (fun pre w => E (pre.map ofWordQuad) (ofWordQuad w))
      dom s.numQueries (fun qs => bad (qs.map ofWordQuad))).length * 2 ^ 206 <
      (2 ^ 256) ^ n * (aggDistinctTuples s.numQueries dom).length := by
  have hAllLe : ∀ st ∈ whirSchedule4Stage .bciksJohnsonQrom128,
      1024 / st.johnsonSqrtBlowup + 1 ≤ 1024 := by decide
  have hSub : 1024 - (1024 - (1024 / s.johnsonSqrtBlowup + 1)) =
      1024 / s.johnsonSqrtBlowup + 1 := Nat.sub_sub_self (hAllLe s hs)
  have hSlack := (bciksJohnsonQrom128_positive_slack s hs).2
  have hM : 2 * ((1024 - (1024 - (1024 / s.johnsonSqrtBlowup + 1))) ^ s.numQueries * 2 ^ 206) <
      1024 ^ s.numQueries := by
    rw [hSub]
    have hPowLe : 2 * 2 ^ 206 ≤ 2 ^ 256 := by decide
    have hRewrite : 2 * ((1024 / s.johnsonSqrtBlowup + 1) ^ s.numQueries * 2 ^ 206) =
        (1024 / s.johnsonSqrtBlowup + 1) ^ s.numQueries * (2 * 2 ^ 206) := by
      simp only [Nat.mul_assoc, Nat.mul_comm]
    rw [hRewrite]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hPowLe) hSlack
  exact squeezed_total_error n hn E d hE dom s.numQueries
    (1024 - (1024 / s.johnsonSqrtBlowup + 1)) 1024 (2 ^ 206)
    productionExt4RoundEventBudget bad hfar hdom hBudget (by decide) hM

/-- With the factor 16 the production challenge-event budget no longer fits under `2^-210`:
    `2 * (16 * budget * 2^210) > 2^256`, while it does fit under `2^-206`. -/
theorem squeezed_budget_exceeds_two_pow_neg_210 :
    2 ^ 256 < 2 * (16 * productionExt4RoundEventBudget * 2 ^ 210) ∧
    2 * (16 * productionExt4RoundEventBudget * 2 ^ 206) ≤ 2 ^ 256 := by
  decide

/-! ## 11. Genuine Reed–Solomon + Degree-7 S-Box `RowArithmetization.Lawful` Instance -/

private def decodeLeb128 : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else
      match decodeLeb128 rest with
      | some (hi, tail) => some ((b.toNat - 128) + 128 * hi, tail)
      | none => none

private def decodeFields : Nat → List UInt8 → Option (List (List UInt8))
  | 0, [] => some []
  | 0, _ :: _ => none
  | k + 1, bs =>
    match decodeLeb128 bs with
    | none => none
    | some (len, rest) =>
      if len ≤ rest.length then
        match decodeFields k (rest.drop len) with
        | some tl => some (rest.take len :: tl)
        | none => none
      else none

private def decodeMultiFrame (bs : List UInt8) : Option (List (List UInt8)) :=
  match decodeLeb128 bs with
  | none => none
  | some (cnt, rest) => decodeFields cnt rest

private theorem uint8_toNat_of_lt_256 {n : Nat} (hn : n < 256) :
    (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

private theorem decodeLeb128_leb128Aux :
    ∀ (f n : Nat) (rest : List UInt8),
      n ≤ f →
      decodeLeb128 (leb128Aux f n ++ rest) = some (n, rest)
  | 0, n, rest, hn => by
    have hz : n = 0 := by omega
    subst hz; rw [leb128Aux_zero]; rfl
  | f + 1, n, rest, hn => by
    rw [leb128Aux_succ]
    by_cases hlt : n < 128
    · simp only [hlt, ↓reduceIte, List.singleton_append, decodeLeb128,
        uint8_toNat_of_lt_256 (by omega : n < 256)]
    · have hb : (UInt8.ofNat (128 + n % 128)).toNat = 128 + n % 128 :=
        uint8_toNat_of_lt_256 (by omega)
      have hNotLt : ¬ (128 + n % 128 < 128) := by omega
      have ih := decodeLeb128_leb128Aux f (n / 128) rest (by omega)
      simp only [hlt, ↓reduceIte, List.cons_append, decodeLeb128, hb, hNotLt, ih]
      congr 1; congr 1; omega

private theorem decodeLeb128_leb128 (n : Nat) (rest : List UInt8) :
    decodeLeb128 (leb128 n ++ rest) = some (n, rest) :=
  decodeLeb128_leb128Aux n n rest (Nat.le_refl n)

private theorem decodeFields_encodeByteFields :
    ∀ (fields : List (List UInt8)),
      decodeFields fields.length (encodeByteFields fields) = some fields
  | [] => by rw [encodeByteFields_nil]; rfl
  | f :: fs => by
    have hRest := decodeFields_encodeByteFields fs
    rw [List.length_cons, encodeByteFields_cons, encodeListField_eq, List.append_assoc]
    unfold decodeFields
    rw [decodeLeb128_leb128]
    dsimp only
    have hLe : f.length ≤ (f ++ encodeByteFields fs).length := by simp
    have hDrop : (f ++ encodeByteFields fs).drop f.length = encodeByteFields fs :=
      List.drop_left' rfl
    have hTake : (f ++ encodeByteFields fs).take f.length = f :=
      List.take_left' rfl
    simp only [hLe, ↓reduceIte, hDrop, hRest, hTake]

private theorem decodeMultiFrame_encodeMultiFrame (fields : List (List UInt8)) :
    decodeMultiFrame (encodeMultiFrame fields) = some fields := by
  unfold decodeMultiFrame encodeMultiFrame
  rw [decodeLeb128_leb128]
  exact decodeFields_encodeByteFields fields

/-- Degree-7 Goldilocks S-box $x \mapsto x^7$ (`gcd(7, p - 1) = 1`). -/
def pow7Goldilocks (x : Goldilocks) : Goldilocks :=
  let x2 := CommRingOps.mul x x
  let x4 := CommRingOps.mul x2 x2
  let x6 := CommRingOps.mul x4 x2
  CommRingOps.mul x6 x

def pow7Ext4 (x : GoldilocksExt4) : GoldilocksExt4 :=
  let x2 := CommRingOps.mul x x
  let x4 := CommRingOps.mul x2 x2
  let x6 := CommRingOps.mul x4 x2
  CommRingOps.mul x6 x

theorem embedBase_pow7 (x : Goldilocks) :
    GoldilocksExt4.embedBase (pow7Goldilocks x) = pow7Ext4 (GoldilocksExt4.embedBase x) := by
  unfold pow7Goldilocks pow7Ext4
  simp only [GoldilocksExt4.embedBase_mul]

/-- Algebraic degree-7 S-box `TweakableHashSuite` (`rawHash_len = 32`) whose 1-layer stateful WOTS
    chain computes `x_0^7 + seed` over `Goldilocks`. -/
def sbox7RawHash (pre : List UInt8) : List UInt8 :=
  match decodeMultiFrame pre with
  | some [role, seedBytes, _adrsBytes, xBytes] =>
    if role == tagThF then
      let x := Goldilocks.ofNat (ofBE xBytes)
      let s := Goldilocks.ofNat (ofBE seedBytes)
      be 32 (CommRingOps.add (pow7Goldilocks x) s).val
    else
      0x40 :: be 31 0
  | some [role, _seedBytes, _adrsBytes, e0Bytes, e1Bytes] =>
    if role == tagThTl then
      let e0 := Goldilocks.ofNat (ofBE e0Bytes)
      let e1 := Goldilocks.ofNat (ofBE e1Bytes)
      be 32 (CommRingOps.add e0 e1).val
    else
      0x40 :: be 31 0
  | _ => 0x40 :: be 31 0

theorem sbox7RawHash_len (pre : List UInt8) : (sbox7RawHash pre).length = 32 := by
  unfold sbox7RawHash
  split
  · split <;> simp [length_be]
  · split <;> simp [length_be]
  · simp [length_be]

def sbox7FieldSuite : TweakableHashSuite where
  suiteId := "QSAG.PQ.SUITE.SBOX7/v1".toUTF8.toList
  rawHash := sbox7RawHash
  rawHash_len := sbox7RawHash_len

def sbox7Params : PqHashParams := ⟨2, 2, 0, 1, 0, 0, 0, true⟩

def mkSbox7Pk (seed root : Goldilocks) : PqPublicKey :=
  { pkSeed := be 32 seed.val, pkRoot := be 32 root.val }

def mkSbox7Sig (x0 : Goldilocks) : PqHashSig :=
  { rRand := []
    msgTswCtr := 0
    leafGlobalIdx := 0
    forsOpenings := []
    layerSigs := [{ tswCtr := 0, wotsChains := [be 32 x0.val, be 32 0], authPath := [] }] }

private theorem goldilocks_ofNat_ofBE_be32 (g : Goldilocks) :
    Goldilocks.ofNat (ofBE (be 32 g.val)) = g := by
  have hb : goldilocksPrime < 256 ^ 32 := by decide
  rw [ofBE_be (Nat.lt_trans g.isLt hb)]
  exact Goldilocks.ext (Nat.mod_eq_of_lt g.isLt)

private theorem uint8_beq_self (x : UInt8) : (x == x) = true :=
  Nat.beq_refl x.toBitVec.toNat

private theorem list_uint8_beq_self : ∀ (xs : List UInt8), (xs == xs) = true
  | [] => rfl
  | x :: xs => by
    change ((x == x) && (xs == xs)) = true
    rw [uint8_beq_self x, list_uint8_beq_self xs]
    rfl

/-- Exact equivalence between `verifyPqHashSig` on `mkSbox7Sig x0` and the degree-7 field equation
    `x0^7 + seed = root` in `Goldilocks`! -/
theorem verifyPqHashSig_sbox7_iff (seed root x0 : Goldilocks) (msg : List UInt8) :
    verifyPqHashSig sbox7FieldSuite sbox7Params (mkSbox7Pk seed root) msg (mkSbox7Sig x0) =
      decide (CommRingOps.add (pow7Goldilocks x0) seed = root) := by
  have hHmsg : ∀ (mu : List UInt8),
      let hmsg := thHashMsg sbox7FieldSuite [] (be 32 seed.val) (be 32 root.val) mu 0 0 0 0
      extractBaseWDigits 2 2 hmsg = [0, 1] := by
    intro mu
    have hCallGen : ∀ (cIdx : UInt32), thCall sbox7FieldSuite tagHMsg (be 32 seed.val)
        ⟨0, 0, .wotsHash, 0, cIdx, UInt32.ofNat 0⟩ [[], be 32 root.val, mu, be 4 0] =
        0x40 :: be 31 0 := by
      intro cIdx
      simp only [thCall_eq, sbox7FieldSuite, sbox7RawHash, thPreimage_eq]
      simp only [List.cons_append, List.nil_append]
      rw [decodeMultiFrame_encodeMultiFrame]
    dsimp only
    simp only [thHashMsg_eq]
    rw [hCallGen 0, hCallGen 1, extractBaseWDigits_eq]
    decide
  have hChain : thChainF sbox7FieldSuite (be 32 seed.val) ⟨0, 0, .wotsHash, 0, 0, 0⟩
      (be 32 x0.val) = be 32 (CommRingOps.add (pow7Goldilocks x0) seed).val := by
    simp only [thChainF_eq, thCall_eq, sbox7FieldSuite, sbox7RawHash, thPreimage_eq]
    simp only [List.cons_append, List.nil_append]
    rw [decodeMultiFrame_encodeMultiFrame]
    simp only [list_uint8_beq_self, ↓reduceIte, goldilocks_ofNat_ofBE_be32]
  let end0 := CommRingOps.add (pow7Goldilocks x0) seed
  have hTl : thTweakTl sbox7FieldSuite (be 32 seed.val) ⟨0, 0, .wotsPk, 0, 0, 0⟩
      [be 32 end0.val, be 32 0] = be 32 end0.val := by
    simp only [thTweakTl_eq, thCall_eq, sbox7FieldSuite, sbox7RawHash, thPreimage_eq]
    simp only [List.cons_append, List.nil_append]
    rw [decodeMultiFrame_encodeMultiFrame]
    have hZero : Goldilocks.ofNat (ofBE (be 32 0)) = Goldilocks.zero := by
      simpa using goldilocks_ofNat_ofBE_be32 Goldilocks.zero
    simp only [list_uint8_beq_self, ↓reduceIte, goldilocks_ofNat_ofBE_be32, hZero]
    exact congrArg (fun g : Goldilocks => be 32 g.val) (LawfulCommRing.add_zero end0)
  unfold verifyPqHashSig mkSbox7Pk mkSbox7Sig
  simp only [Bool.not_true, ↓reduceIte, sbox7Params, ne_eq, not_true_eq_false,
    Nat.mul_zero, Nat.pow_zero, Nat.lt_one_iff, List.isEmpty_nil, PqHashParams.wellFormed_eq]
  let mu := thPreHash sbox7FieldSuite (be 32 seed.val) (be 32 root.val) msg
  change (match verifyHypertreeLayers sbox7FieldSuite ⟨2, 2, 0, 1, 0, 0, 0, true⟩
      (be 32 seed.val) (be 32 root.val) [] 0 0 mu
      [{ tswCtr := 0, wotsChains := [be 32 x0.val, be 32 0], authPath := [] }] with
    | some computedTopRoot => decide (computedTopRoot = be 32 root.val)
    | none => false) = decide (end0 = root)
  simp only [verifyHypertreeLayers_nil, verifyHypertreeLayers_cons]
  have hU32 : UInt32.ofNat 0 = 0 := rfl
  have hU64 : UInt64.ofNat 0 = 0 := rfl
  simp only [Nat.pow_zero, Nat.mod_one, Nat.div_one, hU32, hU64]
  rw [hHmsg mu]
  have hTgt : checkTargetSum 2 2 (PqHashParams.targetSum ⟨2, 2, 0, 1, 0, 0, 0, true⟩) [0, 1] =
      true := by simp only [PqHashParams.targetSum_eq, checkTargetSum, sumDigits_nil, sumDigits_cons]; decide
  rw [hTgt]
  simp only [Bool.not_true, ↓reduceIte, List.length_cons, List.length_nil, ne_eq, not_true_eq_false]
  have hRec : recoverWotsPkFromSig sbox7FieldSuite ⟨2, 2, 0, 1, 0, 0, 0, true⟩ (be 32 seed.val)
      0 0 0 [0, 1] [be 32 x0.val, be 32 0] = be 32 end0.val := by
    simp only [recoverWotsPkFromSig_eq, recoverWotsEndpoints_eq]
    have hRange : List.range 2 = [0, 1] := rfl
    rw [hRange]
    simp only [List.map, List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, Nat.sub_self,
      wotsChainSteps_zero, wotsChainSteps_succ, hU32]
    rw [hChain, hTl]
  rw [hRec]
  simp only [walkMerkleAuthPath, Bool.false_eq_true, ↓reduceIte]
  have hb : goldilocksPrime < 256 ^ 32 := by decide
  if hEq : end0 = root then
    have hBeEq : be 32 end0.val = be 32 root.val := congrArg (fun g : Goldilocks => be 32 g.val) hEq
    rw [decide_eq_true hBeEq, decide_eq_true hEq]
  else
    have hNeBe : be 32 end0.val ≠ be 32 root.val := fun hBe =>
      hEq (Goldilocks.ext (be_injective (Nat.lt_trans end0.isLt hb) (Nat.lt_trans root.isLt hb) hBe))
    rw [decide_eq_false hNeBe, decide_eq_false hEq]

/-- Primitive 8th root of unity in `Goldilocks` (`(2^24)^4 = 2^96 ≡ -1 (mod p)`). -/
def omega8 : Goldilocks := ⟨2 ^ 24, by decide⟩

/-- Multiplicative inverse of `2` in `Goldilocks` (`(p + 1) / 2 = 2^63 - 2^31 + 1`), given as a
    direct literal so WHNF never unfolds 64-step Fermat exponentiation. -/
def invTwoGold : Goldilocks := ⟨9223372034707292161, by decide⟩

def powGold (base : Goldilocks) : Nat → Goldilocks
  | 0 => Goldilocks.one
  | k + 1 => CommRingOps.mul (powGold base k) base

def omega8Domain : List GoldilocksExt4 :=
  (List.range 8).map (fun j => GoldilocksExt4.embedBase (powGold omega8 j))

private theorem omega8_pow_inj {i j : Nat} (hi : i < 8) (hj : j < 8)
    (h : powGold omega8 i = powGold omega8 j) : i = j := by
  have hv : (powGold omega8 i).val = (powGold omega8 j).val := congrArg Goldilocks.val h
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> try omega
  all_goals (rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> try omega)
  all_goals (first | rfl | exact absurd hv (by decide))

private theorem omega8Domain_getD_inj {i j : Nat} (hi : i < 8) (hj : j < 8)
    (h : omega8Domain.getD i GoldilocksExt4.zero = omega8Domain.getD j GoldilocksExt4.zero) :
    i = j := by
  have hiL : i < omega8Domain.length := by simpa [omega8Domain] using hi
  have hjL : j < omega8Domain.length := by simpa [omega8Domain] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjL, Option.getD_some] at h
  simp only [omega8Domain, List.getElem_map, List.getElem_range] at h
  exact omega8_pow_inj hi hj (GoldilocksExt4.embedBase_injective h)

theorem omega8Domain_nodup : omega8Domain.Nodup := by
  unfold omega8Domain
  have hAux : ∀ {xs : List Nat}, xs.Nodup → (∀ z ∈ xs, z < 8) →
      (xs.map (fun j => GoldilocksExt4.embedBase (powGold omega8 j))).Nodup := by
    intro xs hnd hlt
    induction hnd with
    | nil => exact .nil
    | @cons x rest hrel hndRest ih =>
      refine .cons (fun b hb heq => ?_) (ih (fun z hz => hlt z (.tail _ hz)))
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      exact hrel y hy (omega8_pow_inj (hlt x (.head _)) (hlt y (.tail _ hy))
        (GoldilocksExt4.embedBase_injective heq))
  exact hAux (nodup_range_constructive 8) (fun z hz => List.mem_range.mp hz)

/-- Standard blowup-4 Reed–Solomon encoding of `P(Y) = a0 + a1 * Y` on `omega8Domain` (`8` points). -/
def encodeLinearRs8 (a0 a1 : Goldilocks) : List GoldilocksExt4 :=
  omega8Domain.map (RoundPoly.evalCoeffs
    [GoldilocksExt4.embedBase a0, GoldilocksExt4.embedBase a1])

/-- Deterministic coset-duet interpolation at `(omega_8^0, omega_8^4) = (1, -1)`. -/
def recoverLinearCoeffs8 (table0 : List GoldilocksExt4) : GoldilocksExt4 × GoldilocksExt4 :=
  let t0 := table0.getD 0 GoldilocksExt4.zero
  let t4 := table0.getD 4 GoldilocksExt4.zero
  let inv2 := GoldilocksExt4.embedBase invTwoGold
  (CommRingOps.mul (CommRingOps.add t0 t4) inv2,
   CommRingOps.mul (CommRingOps.sub t0 t4) inv2)

/-- Genuine base-field blowup-4 Reed–Solomon codeword predicate (`length = 8`, all entries in
    `F_p`, and all `8` evaluations match the degree-`< 2` interpolated polynomial). -/
def isLinearBaseRs8 (table0 : List GoldilocksExt4) : Bool :=
  (table0.length == 8) &&
  table0.all GoldilocksExt4.isBase &&
  let c := recoverLinearCoeffs8 table0
  (List.range 8).all (fun j =>
    table0.getD j GoldilocksExt4.zero ==
      RoundPoly.evalCoeffs [c.1, c.2] (omega8Domain.getD j GoldilocksExt4.zero))

theorem isLinearBaseRs8_eval_at {table0 : List GoldilocksExt4}
    (h : isLinearBaseRs8 table0 = true) {j : Nat} (hj : j < 8) :
    table0.getD j GoldilocksExt4.zero =
      RoundPoly.evalCoeffs [(recoverLinearCoeffs8 table0).1, (recoverLinearCoeffs8 table0).2]
        (omega8Domain.getD j GoldilocksExt4.zero) := by
  unfold isLinearBaseRs8 at h
  rcases Bool.and_eq_true_iff.mp h with ⟨_, hAll⟩
  have hMem : j ∈ List.range 8 := List.mem_range.mpr hj
  exact eq_of_beq (List.all_eq_true.mp hAll j hMem)

private theorem ext4Zero_eq_ringZero : (GoldilocksExt4.zero : GoldilocksExt4) = CommRingOps.zero := by rfl
private theorem ext4One_eq_ringOne : (GoldilocksExt4.one : GoldilocksExt4) = CommRingOps.one := by rfl

theorem isLinearBaseRs8_encodeLinearRs8 (a0 a1 : Goldilocks) :
    isLinearBaseRs8 (encodeLinearRs8 a0 a1) = true ∧
    recoverLinearCoeffs8 (encodeLinearRs8 a0 a1) =
      (GoldilocksExt4.embedBase a0, GoldilocksExt4.embedBase a1) := by
  have hTwoInv : CommRingOps.mul (CommRingOps.add CommRingOps.one CommRingOps.one)
      (GoldilocksExt4.embedBase invTwoGold) = GoldilocksExt4.one := by decide +kernel
  have hOmega0 : omega8Domain.getD 0 GoldilocksExt4.zero = CommRingOps.one := by decide +kernel
  have hOmega4 : omega8Domain.getD 4 GoldilocksExt4.zero =
      CommRingOps.neg CommRingOps.one := by decide +kernel
  let c0 := GoldilocksExt4.embedBase a0
  let c1 := GoldilocksExt4.embedBase a1
  have hGet : ∀ j, j < 8 →
      (encodeLinearRs8 a0 a1).getD j GoldilocksExt4.zero =
        RoundPoly.evalCoeffs [c0, c1] (omega8Domain.getD j GoldilocksExt4.zero) := by
    intro j hj
    have hjDom : j < omega8Domain.length := by simpa [omega8Domain] using hj
    rw [List.getD_eq_getElem?_getD, encodeLinearRs8, List.getElem?_map,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjDom]
    rfl
  have ht0 : (encodeLinearRs8 a0 a1).getD 0 GoldilocksExt4.zero = CommRingOps.add c0 c1 := by
    rw [hGet 0 (by decide), hOmega0]
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
      LawfulCommRing.one_mul]
  have ht4 : (encodeLinearRs8 a0 a1).getD 4 GoldilocksExt4.zero = CommRingOps.sub c0 c1 := by
    rw [hGet 4 (by decide), hOmega4]
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rw [LawfulCommRing.neg_mul, LawfulCommRing.one_mul, ← LawfulCommRing.sub_eq_add_neg]
  have hRec : recoverLinearCoeffs8 (encodeLinearRs8 a0 a1) = (c0, c1) := by
    unfold recoverLinearCoeffs8
    dsimp only
    rw [ht0, ht4]
    have hSum : CommRingOps.add (CommRingOps.add c0 c1) (CommRingOps.sub c0 c1) =
        CommRingOps.mul c0 (CommRingOps.add CommRingOps.one CommRingOps.one) := by
      rw [LawfulCommRing.left_distrib, LawfulCommRing.mul_one,
          LawfulCommRing.sub_eq_add_neg c0 c1, LawfulCommRing.add_add_add_comm,
          LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
    have hDiff : CommRingOps.sub (CommRingOps.add c0 c1) (CommRingOps.sub c0 c1) =
        CommRingOps.mul c1 (CommRingOps.add CommRingOps.one CommRingOps.one) := by
      apply LawfulCommRing.add_left_cancel (a := CommRingOps.sub c0 c1)
      rw [LawfulCommRing.add_sub_cancel_left, LawfulCommRing.left_distrib,
          LawfulCommRing.mul_one, LawfulCommRing.sub_eq_add_neg c0 c1,
          LawfulCommRing.add_assoc c0 (CommRingOps.neg c1) (CommRingOps.add c1 c1),
          ← LawfulCommRing.add_assoc (CommRingOps.neg c1) c1 c1,
          LawfulCommRing.add_left_neg, LawfulCommRing.zero_add]
    rw [hSum, hDiff, LawfulCommRing.mul_assoc c0, LawfulCommRing.mul_assoc c1,
        hTwoInv, ext4One_eq_ringOne, LawfulCommRing.mul_one, LawfulCommRing.mul_one]
  refine ⟨?_, hRec⟩
  unfold isLinearBaseRs8
  dsimp only
  rw [hRec]
  dsimp only [c0, c1]
  have hLen : ((encodeLinearRs8 a0 a1).length == 8) = true := by simp [encodeLinearRs8, omega8Domain]
  have hBaseAll : (encodeLinearRs8 a0 a1).all GoldilocksExt4.isBase = true := by
    apply List.all_eq_true.mpr
    intro z hz
    unfold encodeLinearRs8 omega8Domain at hz
    rw [List.map_map] at hz
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hz
    dsimp only [Function.comp_apply]
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rw [← GoldilocksExt4.embedBase_mul, ← GoldilocksExt4.embedBase_add]
    exact GoldilocksExt4.isBase_embedBase _
  have hEvalAll : (List.range 8).all (fun j =>
      (encodeLinearRs8 a0 a1).getD j GoldilocksExt4.zero ==
        RoundPoly.evalCoeffs [GoldilocksExt4.embedBase a0, GoldilocksExt4.embedBase a1]
          (omega8Domain.getD j GoldilocksExt4.zero)) = true := by
    apply List.all_eq_true.mpr
    intro j hj
    exact beq_iff_eq.mpr (hGet j (List.mem_range.mp hj))
  rw [hLen, hBaseAll, hEvalAll]
  rfl

private theorem getD_set_ne {α : Type} (l : List α) (idx j : Nat) (v dflt : α) (hne : j ≠ idx) :
    (l.set idx v).getD j dflt = l.getD j dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm hne)]

private theorem getD_set_eq {α : Type} (l : List α) (idx : Nat) (v dflt : α)
    (hlt : idx < l.length) : (l.set idx v).getD idx dflt = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlt, Option.getD_some]

private theorem degree1_unique_from_two_points (p1 p2 : List GoldilocksExt4)
    (x1 x2 z : GoldilocksExt4)
    (hxNe : x1 ≠ x2) (hp1 : p1.length ≤ 2) (hp2 : p2.length ≤ 2)
    (h1 : RoundPoly.evalCoeffs p1 x1 = RoundPoly.evalCoeffs p2 x1)
    (h2 : RoundPoly.evalCoeffs p1 x2 = RoundPoly.evalCoeffs p2 x2)
    (hz : RoundPoly.evalCoeffs p1 z ≠ RoundPoly.evalCoeffs p2 z) : False := by
  have hNd : [x1, x2].Nodup := by simp [hxNe]
  have hRoots := ext4_poly_roots_le_degree 1 p1 p2 [x1, x2] hNd hp1 hp2 ⟨z, hz⟩
  simp only [List.filter, h1, h2, decide_true, List.length_cons, List.length_nil] at hRoots
  omega

/-- **`#tooth` Minimum-Distance Corruption Rejection (`tooth_corrupted_round0_symbol_rejected`)**:
    Mutating ANY single symbol at ANY index `idx < 8` of ANY valid Round-0 codeword forces
    `isLinearBaseRs8 = false` (proving `isRound0Codeword` is a genuine minimum-distance-7
    Reed–Solomon check, never `fun _ => true`). -/
theorem tooth_corrupted_round0_symbol_rejected (table0 : List GoldilocksExt4)
    (idx : Nat) (v' : GoldilocksExt4)
    (hValid : isLinearBaseRs8 table0 = true)
    (hIdx : idx < 8)
    (hMut : v' ≠ table0.getD idx GoldilocksExt4.zero) :
    isLinearBaseRs8 (table0.set idx v') = false := by
  apply Bool.eq_false_iff.mpr
  intro hBad
  have hLen8 : table0.length = 8 := by
    unfold isLinearBaseRs8 at hValid
    exact eq_of_beq (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hValid).1).1
  have hPair : ∃ j1 j2 : Nat, j1 < 8 ∧ j2 < 8 ∧ j1 ≠ idx ∧ j2 ≠ idx ∧ j1 ≠ j2 := by
    rcases idx with _ | _ | idx
    · exact ⟨1, 2, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by omega, by omega, by decide⟩
  obtain ⟨j1, j2, hj1Lt, hj2Lt, hj1Ne, hj2Ne, hj12Ne⟩ := hPair
  have hxNe : omega8Domain.getD j1 GoldilocksExt4.zero ≠
      omega8Domain.getD j2 GoldilocksExt4.zero := fun hEq =>
    hj12Ne (omega8Domain_getD_inj hj1Lt hj2Lt hEq)
  have hAgree1 : RoundPoly.evalCoeffs
      [(recoverLinearCoeffs8 table0).1, (recoverLinearCoeffs8 table0).2]
      (omega8Domain.getD j1 GoldilocksExt4.zero) =
      RoundPoly.evalCoeffs
        [(recoverLinearCoeffs8 (table0.set idx v')).1, (recoverLinearCoeffs8 (table0.set idx v')).2]
        (omega8Domain.getD j1 GoldilocksExt4.zero) := by
    have e1 := isLinearBaseRs8_eval_at hValid hj1Lt
    have e2 := isLinearBaseRs8_eval_at hBad hj1Lt
    rw [getD_set_ne _ _ _ _ _ hj1Ne] at e2
    exact e1.symm.trans e2
  have hAgree2 : RoundPoly.evalCoeffs
      [(recoverLinearCoeffs8 table0).1, (recoverLinearCoeffs8 table0).2]
      (omega8Domain.getD j2 GoldilocksExt4.zero) =
      RoundPoly.evalCoeffs
        [(recoverLinearCoeffs8 (table0.set idx v')).1, (recoverLinearCoeffs8 (table0.set idx v')).2]
        (omega8Domain.getD j2 GoldilocksExt4.zero) := by
    have e1 := isLinearBaseRs8_eval_at hValid hj2Lt
    have e2 := isLinearBaseRs8_eval_at hBad hj2Lt
    rw [getD_set_ne _ _ _ _ _ hj2Ne] at e2
    exact e1.symm.trans e2
  have hDisagreeIdx : RoundPoly.evalCoeffs
      [(recoverLinearCoeffs8 table0).1, (recoverLinearCoeffs8 table0).2]
      (omega8Domain.getD idx GoldilocksExt4.zero) ≠
      RoundPoly.evalCoeffs
        [(recoverLinearCoeffs8 (table0.set idx v')).1, (recoverLinearCoeffs8 (table0.set idx v')).2]
        (omega8Domain.getD idx GoldilocksExt4.zero) := by
    have e1 := isLinearBaseRs8_eval_at hValid hIdx
    have e2 := isLinearBaseRs8_eval_at hBad hIdx
    rw [getD_set_eq table0 idx v' GoldilocksExt4.zero (hLen8 ▸ hIdx)] at e2
    rw [← e1, ← e2]
    exact fun hEq => hMut hEq.symm
  exact degree1_unique_from_two_points _ _ _ _ _ hxNe (by simp) (by simp)
    hAgree1 hAgree2 hDisagreeIdx

/-- Constant Reed–Solomon codeword predicate of exact length `expectedLen ≥ 2`. -/
def isConstExt4Rs (expectedLen : Nat) (w : List GoldilocksExt4) : Bool :=
  (w.length == expectedLen) &&
  w.all (fun x => x == w.getD 0 GoldilocksExt4.zero)

theorem isConstExt4Rs_replicate (expectedLen : Nat) (v : GoldilocksExt4) :
    isConstExt4Rs expectedLen (List.replicate expectedLen v) = true := by
  unfold isConstExt4Rs
  simp only [List.length_replicate, beq_self_eq_true, Bool.true_and]
  apply List.all_eq_true.mpr
  intro x hx
  have hxEq := List.eq_of_mem_replicate hx
  subst hxEq
  cases expectedLen with
  | zero => cases hx
  | succ k => simp [List.replicate_succ]

theorem isConstExt4Rs_eq_head {expectedLen : Nat} {w : List GoldilocksExt4}
    (h : isConstExt4Rs expectedLen w = true) {j : Nat} (hj : j < expectedLen) :
    w.getD j GoldilocksExt4.zero = w.getD 0 GoldilocksExt4.zero := by
  unfold isConstExt4Rs at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hLen, hAll⟩
  have hjLt : j < w.length := (eq_of_beq hLen) ▸ hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjLt, Option.getD_some]
  exact eq_of_beq (List.all_eq_true.mp hAll _ (List.getElem_mem hjLt))

/-- `#tooth` Corrupting a single symbol of `finalWord` (`length = 8`) rejects `isFinalCodeword`. -/
theorem tooth_corrupted_final_symbol_rejected (v v' : GoldilocksExt4) (hNe : v' ≠ v) :
    isConstExt4Rs 8 ((List.replicate 8 v).set 3 v') = false := by
  apply Bool.eq_false_iff.mpr
  intro hOk
  have h3 := isConstExt4Rs_eq_head hOk (j := 3) (by decide)
  rw [getD_set_eq _ 3 v' _ (by simp), getD_set_ne _ 3 0 v' _ (by decide)] at h3
  simp only [List.replicate_succ, List.getD_cons_zero] at h3
  exact hNe h3

/-- Polynomial algebra combinators over `GoldilocksExt4` for building the exact degree-8 row gate. -/
def polyAdd : List GoldilocksExt4 → List GoldilocksExt4 → List GoldilocksExt4
  | [], qs => qs
  | ps, [] => ps
  | p :: ps, q :: qs => CommRingOps.add p q :: polyAdd ps qs

def polyScale (c : GoldilocksExt4) : List GoldilocksExt4 → List GoldilocksExt4
  | [] => []
  | p :: ps => CommRingOps.mul c p :: polyScale c ps

def polyMul : List GoldilocksExt4 → List GoldilocksExt4 → List GoldilocksExt4
  | [], _ => []
  | p :: ps, qs => polyAdd (polyScale p qs) (GoldilocksExt4.zero :: polyMul ps qs)

theorem evalCoeffs_polyAdd :
    ∀ (ps qs : List GoldilocksExt4) (x : GoldilocksExt4),
      RoundPoly.evalCoeffs (polyAdd ps qs) x =
        CommRingOps.add (RoundPoly.evalCoeffs ps x) (RoundPoly.evalCoeffs qs x)
  | [], qs, x => by simp [polyAdd, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | p :: ps, [], x => by simp [polyAdd, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | p :: ps, q :: qs, x => by
    simp only [polyAdd, RoundPoly.evalCoeffs, evalCoeffs_polyAdd ps qs x]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem evalCoeffs_polyScale (c : GoldilocksExt4) :
    ∀ (ps : List GoldilocksExt4) (x : GoldilocksExt4),
      RoundPoly.evalCoeffs (polyScale c ps) x =
        CommRingOps.mul c (RoundPoly.evalCoeffs ps x)
  | [], x => by simp [polyScale, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | p :: ps, x => by
    simp only [polyScale, RoundPoly.evalCoeffs, evalCoeffs_polyScale c ps x]
    rw [LawfulCommRing.left_distrib, ← LawfulCommRing.mul_assoc,
        LawfulCommRing.mul_comm x c, LawfulCommRing.mul_assoc]

theorem evalCoeffs_polyMul :
    ∀ (ps qs : List GoldilocksExt4) (x : GoldilocksExt4),
      RoundPoly.evalCoeffs (polyMul ps qs) x =
        CommRingOps.mul (RoundPoly.evalCoeffs ps x) (RoundPoly.evalCoeffs qs x)
  | [], qs, x => by simp [polyMul, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | p :: ps, qs, x => by
    simp only [polyMul, evalCoeffs_polyAdd, evalCoeffs_polyScale,
      RoundPoly.evalCoeffs, evalCoeffs_polyMul ps qs x]
    rw [ext4Zero_eq_ringZero, LawfulCommRing.zero_add,
        LawfulCommRing.right_distrib, LawfulCommRing.mul_assoc]

theorem length_polyAdd :
    ∀ (ps qs : List GoldilocksExt4), (polyAdd ps qs).length = max ps.length qs.length
  | [], qs => by simp [polyAdd]
  | p :: ps, [] => by simp [polyAdd]
  | p :: ps, q :: qs => by simp [polyAdd, length_polyAdd ps qs, Nat.succ_max_succ]

theorem length_polyScale (c : GoldilocksExt4) (ps : List GoldilocksExt4) :
    (polyScale c ps).length = ps.length := by
  induction ps with
  | nil => rfl
  | cons _ tl ih => simp [polyScale, ih]

theorem length_polyMul_le :
    ∀ (ps qs : List GoldilocksExt4) (m n : Nat),
      ps.length ≤ m + 1 → qs.length ≤ n + 1 →
      (polyMul ps qs).length ≤ m + n + 1
  | [], _, m, n, _, _ => by simp [polyMul]
  | [p], qs, m, n, _, hq => by
    simp only [polyMul, length_polyAdd, length_polyScale, List.length_cons, List.length_nil]
    exact Nat.max_le.mpr ⟨by omega, by omega⟩
  | p :: p2 :: ps, qs, 0, _, hp, _ => by simp at hp
  | p :: p2 :: ps, qs, m + 1, n, hp, hq => by
    have ih := length_polyMul_le (p2 :: ps) qs m n (by simp at hp ⊢; omega) hq
    show (polyAdd (polyScale p qs) (GoldilocksExt4.zero :: polyMul (p2 :: ps) qs)).length ≤
      m + 1 + n + 1
    rw [length_polyAdd, length_polyScale, List.length_cons]
    exact Nat.max_le.mpr ⟨by omega, by omega⟩

/-- Honest degree-8 row gate polynomial `(1 - Y) * ((c0 + c1 * Y)^7 + delta)` (`length ≤ 9`),
    factored through `delta = seed - root` so equal differences unify without unfolding `polyMul`. -/
private def honestSbox7RoundPolyDelta (delta : Goldilocks) (table0 : List GoldilocksExt4) :
    List GoldilocksExt4 :=
  let c := recoverLinearCoeffs8 table0
  let lin := [c.1, c.2]
  let lin2 := polyMul lin lin
  let lin4 := polyMul lin2 lin2
  let lin6 := polyMul lin4 lin2
  let lin7 := polyMul lin6 lin
  let gate7 := polyAdd lin7 [GoldilocksExt4.embedBase delta]
  let sel0 := [GoldilocksExt4.one, CommRingOps.neg GoldilocksExt4.one]
  polyMul sel0 gate7

/-- Honest degree-8 row gate polynomial `(1 - Y) * ((c0 + c1 * Y)^7 + seed - root)` (`length ≤ 9`). -/
def honestSbox7RoundPoly (seed root : Goldilocks) (table0 : List GoldilocksExt4) :
    List GoldilocksExt4 :=
  honestSbox7RoundPolyDelta (CommRingOps.sub seed root) table0

theorem honestSbox7RoundPoly_length_le_9 (seed root : Goldilocks) (table0 : List GoldilocksExt4) :
    (honestSbox7RoundPoly seed root table0).length ≤ 9 := by
  unfold honestSbox7RoundPoly honestSbox7RoundPolyDelta
  dsimp only
  let lin := [ (recoverLinearCoeffs8 table0).1, (recoverLinearCoeffs8 table0).2 ]
  let lin2 := polyMul lin lin
  let lin4 := polyMul lin2 lin2
  let lin6 := polyMul lin4 lin2
  let lin7 := polyMul lin6 lin
  let gate7 := polyAdd lin7 [GoldilocksExt4.embedBase (CommRingOps.sub seed root)]
  let sel0 := [GoldilocksExt4.one, CommRingOps.neg GoldilocksExt4.one]
  have l1 : lin.length ≤ 1 + 1 := by simp [lin]
  have l2 := length_polyMul_le lin lin 1 1 l1 l1
  have l4 := length_polyMul_le lin2 lin2 2 2 l2 l2
  have l6 := length_polyMul_le lin4 lin2 4 2 l4 l2
  have l7 := length_polyMul_le lin6 lin 6 1 l6 l1
  have lg7 : gate7.length ≤ 7 + 1 := by
    dsimp only [gate7]
    rw [length_polyAdd]
    exact Nat.max_le.mpr ⟨l7, by simp⟩
  exact length_polyMul_le sel0 gate7 1 7 (by simp [sel0]) lg7

theorem honestSbox7RoundPoly_eval (seed root : Goldilocks) (table0 : List GoldilocksExt4)
    (y : GoldilocksExt4) :
    RoundPoly.evalCoeffs (honestSbox7RoundPoly seed root table0) y =
      CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one y)
        (CommRingOps.add
          (pow7Ext4 (CommRingOps.add (recoverLinearCoeffs8 table0).1
            (CommRingOps.mul y (recoverLinearCoeffs8 table0).2)))
          (GoldilocksExt4.embedBase (CommRingOps.sub seed root))) := by
  unfold honestSbox7RoundPoly honestSbox7RoundPolyDelta
  dsimp only
  simp only [evalCoeffs_polyMul, evalCoeffs_polyAdd, RoundPoly.evalCoeffs,
    LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [ext4One_eq_ringOne, LawfulCommRing.mul_neg,
      LawfulCommRing.mul_one, ← LawfulCommRing.sub_eq_add_neg]
  rfl

/-- Genuine trace witness decoder: extracts `[mkSbox7Sig x0]` from the interpolated `Y = 0`
    evaluation of `table0` (zero hardcoded `sigA`!). -/
def decodeSbox7Sigs (table0 : List GoldilocksExt4) : List PqHashSig :=
  [mkSbox7Sig (recoverLinearCoeffs8 table0).1.c0.c0]

/-- **`decodeSbox7Sigs_nonconstant`**: distinct committed witnesses `x ≠ y` decode to distinct
    `PqHashSig` lists, proving `decodeSbox7Sigs` genuinely reads `table0`. -/
theorem decodeSbox7Sigs_nonconstant {x y b1 b2 : Goldilocks} (hne : x ≠ y) :
    decodeSbox7Sigs (encodeLinearRs8 x b1) ≠ decodeSbox7Sigs (encodeLinearRs8 y b2) := by
  intro hEq
  unfold decodeSbox7Sigs at hEq
  rw [(isLinearBaseRs8_encodeLinearRs8 x b1).2, (isLinearBaseRs8_encodeLinearRs8 y b2).2] at hEq
  simp only [List.cons.injEq, and_true, GoldilocksExt4.embedBase_c0_c0] at hEq
  have hChains := congrArg (fun s : PqHashSig => (s.layerSigs.headD ⟨0, [], []⟩).wotsChains.headD []) hEq
  simp only [mkSbox7Sig, List.headD_cons] at hChains
  have hb : goldilocksPrime < 256 ^ 32 := by decide
  exact hne (Goldilocks.ext (be_injective (Nat.lt_trans x.isLt hb) (Nat.lt_trans y.isLt hb) hChains))

/-- Non-recursive inverse of `omega_8^g` via `omega_8^8 = 1` (`powGold omega8 ((8 - g % 8) % 8)`). -/
def invOmega8Pow (g : Nat) : Goldilocks :=
  powGold omega8 ((8 - g % 8) % 8)

/-- 2-stage rate-escalating WHIR domain (`Stage 0: blowup = 4, groups0 = 4`;
    `Stage 1: blowup = 16, groups0 = 8`). -/
def sbox7Stage0Dom : WhirStageDomain where
  stageIdx := 0
  blowup := 4
  groups0 := 4
  foldLayers := 1
  numQueries := 4
  powBits := 0
  invTwo := invTwoGold
  invTwoY0 := fun _ g => CommRingOps.mul invTwoGold (invOmega8Pow g)
  sampleFuel := 16
  bindRowChallenges := true

def sbox7Stage1Dom : WhirStageDomain where
  stageIdx := 1
  blowup := 16
  groups0 := 8
  foldLayers := 1
  numQueries := 4
  powBits := 0
  invTwo := invTwoGold
  invTwoY0 := fun _ _ => invTwoGold
  sampleFuel := 16
  bindRowChallenges := false

def rsSbox7WhirDomain : WhirDomain := { stages := [sbox7Stage0Dom, sbox7Stage1Dom] }

def rsSbox7Inst (seed root : Goldilocks) (msg : List UInt8) : AggPublicInstance where
  suite := sbox7FieldSuite
  params := sbox7Params
  regime := .bciksJohnsonQrom128
  message := msg
  committee := [mkSbox7Pk seed root]
  signingModeDigest := "QSAG.SBOX7.MODE/v2".toUTF8.toList

private def rsSbox7TraceArithDelta (delta : Goldilocks) : RowArithmetization where
  decodeSigs := decodeSbox7Sigs
  honestClaim := fun table0 =>
    let p := honestSbox7RoundPolyDelta delta table0
    CommRingOps.add (RoundPoly.evalCoeffs p GoldilocksExt4.zero)
                    (RoundPoly.evalCoeffs p GoldilocksExt4.one)
  honestRound := fun table0 _ => honestSbox7RoundPolyDelta delta table0
  terminal := fun finalWord rowChallenges _ =>
    let r0 := rowChallenges.headD GoldilocksExt4.zero
    let pr0 := finalWord.getD 0 GoldilocksExt4.zero
    CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one r0)
      (CommRingOps.add (pow7Ext4 pr0)
        (GoldilocksExt4.embedBase delta))
  isStageCodeword := fun pos w =>
    if pos = 0 then isLinearBaseRs8 w
    else isConstExt4Rs 16 w
  isFinalCodeword := isConstExt4Rs 8

def rsSbox7TraceArith (seed root : Goldilocks) : RowArithmetization :=
  rsSbox7TraceArithDelta (CommRingOps.sub seed root)

private theorem foldDuetExt4_const (v : GoldilocksExt4) (twY : Goldilocks)
    (r : GoldilocksExt4) :
    foldDuetExt4 v v twY invTwoGold r = v := by
  have hTwoInv : CommRingOps.mul (CommRingOps.add CommRingOps.one CommRingOps.one)
      (GoldilocksExt4.embedBase invTwoGold) = CommRingOps.one := by decide +kernel
  have hSum : CommRingOps.add v v =
      CommRingOps.mul v (CommRingOps.add CommRingOps.one CommRingOps.one) := by
    rw [LawfulCommRing.left_distrib, LawfulCommRing.mul_one]
  unfold foldDuetExt4
  dsimp only
  rw [LawfulCommRing.sub_self, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero, hSum, LawfulCommRing.mul_assoc, hTwoInv, LawfulCommRing.mul_one]

theorem foldDuetExt4_encodeLinearRs8_all (a0 a1 : Goldilocks) (r : GoldilocksExt4)
    {g : Nat} (hg : g < 4) :
    foldDuetExt4 ((encodeLinearRs8 a0 a1).getD g GoldilocksExt4.zero)
      ((encodeLinearRs8 a0 a1).getD (g + 4) GoldilocksExt4.zero)
      (sbox7Stage0Dom.invTwoY0 0 g) sbox7Stage0Dom.invTwo r =
      CommRingOps.add (GoldilocksExt4.embedBase a0)
        (CommRingOps.mul r (GoldilocksExt4.embedBase a1)) := by
  let c0 := GoldilocksExt4.embedBase a0
  let c1 := GoldilocksExt4.embedBase a1
  let wg := omega8Domain.getD g GoldilocksExt4.zero
  have hGet : ∀ j, j < 8 →
      (encodeLinearRs8 a0 a1).getD j GoldilocksExt4.zero =
        CommRingOps.add c0 (CommRingOps.mul (omega8Domain.getD j GoldilocksExt4.zero) c1) := by
    intro j hj
    have hjDom : j < omega8Domain.length := by simpa [omega8Domain] using hj
    rw [List.getD_eq_getElem?_getD, encodeLinearRs8, List.getElem?_map,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjDom]
    simp only [Option.map_some, Option.getD_some, RoundPoly.evalCoeffs,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rfl
  have hNeg : omega8Domain.getD (g + 4) GoldilocksExt4.zero = CommRingOps.neg wg := by
    dsimp only [wg]
    rcases g with _ | _ | _ | _ | g
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · omega
  have hTw : CommRingOps.mul (CommRingOps.add wg wg)
      (GoldilocksExt4.embedBase (CommRingOps.mul invTwoGold (invOmega8Pow g))) =
      CommRingOps.one := by
    dsimp only [wg]
    rcases g with _ | _ | _ | _ | g
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · omega
  have hTwoInv : CommRingOps.mul (CommRingOps.add CommRingOps.one CommRingOps.one)
      (GoldilocksExt4.embedBase invTwoGold) = CommRingOps.one := by decide +kernel
  rw [hGet g (by omega), hGet (g + 4) (by omega), hNeg]
  have hAdd : CommRingOps.add (CommRingOps.add c0 (CommRingOps.mul wg c1))
      (CommRingOps.add c0 (CommRingOps.mul (CommRingOps.neg wg) c1)) =
      CommRingOps.mul c0 (CommRingOps.add CommRingOps.one CommRingOps.one) := by
    rw [LawfulCommRing.neg_mul, LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero,
        LawfulCommRing.left_distrib, LawfulCommRing.mul_one]
  have hSub : CommRingOps.sub (CommRingOps.add c0 (CommRingOps.mul wg c1))
      (CommRingOps.add c0 (CommRingOps.mul (CommRingOps.neg wg) c1)) =
      CommRingOps.mul c1 (CommRingOps.add wg wg) := by
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add c0 (CommRingOps.mul (CommRingOps.neg wg) c1))
    rw [LawfulCommRing.add_sub_cancel_left, LawfulCommRing.neg_mul,
        LawfulCommRing.left_distrib, LawfulCommRing.mul_comm c1 wg,
        LawfulCommRing.add_assoc c0,
        ← LawfulCommRing.add_assoc (CommRingOps.neg (CommRingOps.mul wg c1)),
        LawfulCommRing.add_left_neg, LawfulCommRing.zero_add]
  unfold foldDuetExt4
  dsimp only [sbox7Stage0Dom]
  rw [hAdd, hSub, LawfulCommRing.mul_assoc c0, hTwoInv, LawfulCommRing.mul_one,
      LawfulCommRing.mul_assoc c1, hTw, LawfulCommRing.mul_one]

private theorem unpack_stage_foldChallenges {rowChallenges finalWord : List GoldilocksExt4}
    {prior : List UInt8} {sdom : WhirStageDomain} {sp : WhirStageProof}
    {nextInfo : Option (WhirStageDomain × List UInt8)}
    (h : verifyOneWhirStage rowChallenges finalWord prior sdom sp nextInfo = true) :
    sp.foldChallenges = (if sdom.bindRowChallenges then rowChallenges else sp.shiftChallenges) ∧
    sp.foldChallenges.length = sdom.foldLayers := by
  unfold verifyOneWhirStage at h
  dsimp only at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, c6⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨_, c5⟩
  exact ⟨of_decide_eq_true c5, of_decide_eq_true c6⟩

private theorem verifyWhirStages_length_eq {rc fw : List GoldilocksExt4} :
    ∀ {prior : List UInt8} {ds : List WhirStageDomain} {ps : List WhirStageProof},
      verifyWhirStages rc fw prior ds ps = true → ds.length = ps.length
  | _, [], [], _ => rfl
  | _, [_], [_], _ => rfl
  | _, _ :: _ :: _, _ :: _ :: _, h => by
    unfold verifyWhirStages at h
    exact congrArg Nat.succ (verifyWhirStages_length_eq (Bool.and_eq_true_iff.mp h).2)
  | _, [], _ :: _, h => Bool.noConfusion h
  | _, [_], [], h => Bool.noConfusion h
  | _, _ :: _ :: _, [], h => Bool.noConfusion h
  | _, [_], _ :: _ :: _, h => Bool.noConfusion h
  | _, _ :: _ :: _, [_], h => Bool.noConfusion h

private theorem invTwoGold_mul_invOmega8Pow_zero :
    CommRingOps.mul invTwoGold (invOmega8Pow 0) = invTwoGold := by
  decide +kernel

private theorem sbox7_sumcheck_step_complete (p : List GoldilocksExt4)
    (r0 t : GoldilocksExt4) (hDeg : p.length ≤ 9) (hEv : RoundPoly.evalCoeffs p r0 = t) :
    verifySumcheckChain (CommRingOps.add (RoundPoly.evalCoeffs p GoldilocksExt4.zero)
      (RoundPoly.evalCoeffs p GoldilocksExt4.one)) [p] [r0] t = true := by
  simp only [verifySumcheckChain, verifySumcheckChainDeg, hDeg, decide_true,
    hEv, beq_self_eq_true, Bool.and_self]

private theorem sbox7_sum_zero_sound (seed root x : Goldilocks) (c1 : GoldilocksExt4)
    (hZero : CommRingOps.add
      (CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one GoldilocksExt4.zero)
        (CommRingOps.add
          (pow7Ext4 (CommRingOps.add (GoldilocksExt4.embedBase x)
            (CommRingOps.mul GoldilocksExt4.zero c1)))
          (GoldilocksExt4.embedBase (CommRingOps.sub seed root))))
      (CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one GoldilocksExt4.one)
        (CommRingOps.add
          (pow7Ext4 (CommRingOps.add (GoldilocksExt4.embedBase x)
            (CommRingOps.mul GoldilocksExt4.one c1)))
          (GoldilocksExt4.embedBase (CommRingOps.sub seed root)))) =
      GoldilocksExt4.zero) :
    CommRingOps.add (pow7Goldilocks x) seed = root := by
  rw [ext4Zero_eq_ringZero, ext4One_eq_ringOne,
      LawfulCommRing.sub_self, LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
      LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
      LawfulCommRing.sub_zero, LawfulCommRing.one_mul,
      ← embedBase_pow7, ← GoldilocksExt4.embedBase_add] at hZero
  have hZero' : GoldilocksExt4.embedBase (CommRingOps.add (pow7Goldilocks x)
      (CommRingOps.sub seed root)) = GoldilocksExt4.embedBase CommRingOps.zero := by
    simpa only [Goldilocks.ring_zero, GoldilocksExt4.embedBase_zero, GoldilocksExt4.zero_eq_ringZero] using hZero
  have hSubZero : CommRingOps.add (pow7Goldilocks x) (CommRingOps.sub seed root) =
      CommRingOps.zero := GoldilocksExt4.embedBase_injective hZero'
  apply LawfulCommRing.add_left_cancel (a := CommRingOps.neg root)
  rw [LawfulCommRing.add_comm (CommRingOps.neg root) root,
      LawfulCommRing.add_right_neg,
      LawfulCommRing.add_comm (CommRingOps.neg root) _,
      LawfulCommRing.add_assoc (pow7Goldilocks x) seed (CommRingOps.neg root),
      ← LawfulCommRing.sub_eq_add_neg seed root]
  exact hSubZero

private theorem sbox7_sum_zero_complete (seed x0 : Goldilocks) (c1 : GoldilocksExt4) :
    let root := CommRingOps.add (pow7Goldilocks x0) seed
    CommRingOps.add
      (CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one GoldilocksExt4.zero)
        (CommRingOps.add
          (pow7Ext4 (CommRingOps.add (GoldilocksExt4.embedBase x0)
            (CommRingOps.mul GoldilocksExt4.zero c1)))
          (GoldilocksExt4.embedBase (CommRingOps.sub seed root))))
      (CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one GoldilocksExt4.one)
        (CommRingOps.add
          (pow7Ext4 (CommRingOps.add (GoldilocksExt4.embedBase x0)
            (CommRingOps.mul GoldilocksExt4.one c1)))
          (GoldilocksExt4.embedBase (CommRingOps.sub seed root)))) =
      GoldilocksExt4.zero := by
  intro root
  rw [ext4Zero_eq_ringZero, ext4One_eq_ringOne,
      LawfulCommRing.sub_self, LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
      LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
      LawfulCommRing.sub_zero, LawfulCommRing.one_mul,
      ← embedBase_pow7, ← GoldilocksExt4.embedBase_add]
  have hBaseZero : CommRingOps.add (pow7Goldilocks x0) (CommRingOps.sub seed root) =
      CommRingOps.zero := by
    dsimp only [root]
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.add (pow7Goldilocks x0) seed)
    rw [LawfulCommRing.add_zero,
        LawfulCommRing.add_comm (pow7Goldilocks x0) (CommRingOps.sub seed _),
        ← LawfulCommRing.add_assoc,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_comm seed (pow7Goldilocks x0)]
  rw [hBaseZero]
  rfl

/-- **Genuine Non-Trivial `RowArithmetization.Lawful` Instance (`rsSbox7TraceArith_lawful`)**:
    Proves `complete` and `sound` for the blowup-4 -> blowup-16 2-stage WHIR degree-7 S-box
    arithmetization with real Reed–Solomon codeword checks and real trace witness decoding. -/
theorem rsSbox7TraceArith_lawful (seed root : Goldilocks) (msg : List UInt8) :
    (rsSbox7TraceArith seed root).Lawful rsSbox7WhirDomain (rsSbox7Inst seed root msg) where
  complete allTables proof prior hLen hAllCw hFinalCw hVerWhir hAllCons := by
    have hTblShape : ∃ st0 st1, allTables = [st0, st1] := by
      cases allTables with
      | nil => cases hLen
      | cons st0 r1 =>
        cases r1 with
        | nil => cases hLen
        | cons st1 r2 =>
          cases r2 with
          | nil => exact ⟨st0, st1, rfl⟩
          | cons _ _ =>
            exfalso
            simp only [rsSbox7WhirDomain, List.length_cons, List.length_nil] at hLen
            omega
    obtain ⟨st0, st1, rfl⟩ := hTblShape
    have hLenP : rsSbox7WhirDomain.stages.length = proof.stages.length :=
      verifyWhirStages_length_eq hVerWhir
    have hPrfShape : ∃ sp0 sp1, proof.stages = [sp0, sp1] := by
      cases hP : proof.stages with
      | nil => rw [hP] at hLenP; cases hLenP
      | cons sp0 r1 =>
        cases r1 with
        | nil => rw [hP] at hLenP; cases hLenP
        | cons sp1 r2 =>
          cases r2 with
          | nil => exact ⟨sp0, sp1, rfl⟩
          | cons _ _ =>
            exfalso
            rw [hP] at hLenP
            simp only [rsSbox7WhirDomain, List.length_cons, List.length_nil] at hLenP
            omega
    obtain ⟨sp0, sp1, hStagesEq⟩ := hPrfShape
    rw [hStagesEq] at hVerWhir hAllCons
    simp only [rsSbox7WhirDomain, verifyWhirStages, Bool.and_eq_true] at hVerWhir
    have hFold0 := unpack_stage_foldChallenges hVerWhir.1
    have hFold1 := unpack_stage_foldChallenges hVerWhir.2
    simp only [sbox7Stage0Dom, ↓reduceIte] at hFold0
    simp only [sbox7Stage1Dom, Bool.false_eq_true, ↓reduceIte] at hFold1
    have hChallShape : ∃ r0, proof.agg.challenges = [r0] ∧ sp0.foldChallenges = [r0] := by
      cases hC : proof.agg.challenges with
      | nil => rw [hFold0.1, hC] at hFold0; cases hFold0.2
      | cons r0 rs =>
        cases rs with
        | nil => exact ⟨r0, rfl, by rw [hFold0.1, hC]⟩
        | cons _ _ =>
          exfalso
          have hL0 := hFold0.2
          rw [hFold0.1, hC] at hL0
          simp only [List.length_cons] at hL0
          omega
    obtain ⟨r0, hChEq, hFold0Eq⟩ := hChallShape
    have hFold1Shape : ∃ α1, sp1.foldChallenges = [α1] := by
      cases hF1 : sp1.foldChallenges with
      | nil => rw [hF1] at hFold1; cases hFold1.2
      | cons α1 αs =>
        cases αs with
        | nil => exact ⟨α1, rfl⟩
        | cons _ _ =>
          exfalso
          have hL1 := hFold1.2
          rw [hF1] at hL1
          simp only [List.length_cons] at hL1
          omega
    obtain ⟨α1, hFold1Eq⟩ := hFold1Shape
    simp only [rsSbox7WhirDomain, AllStagesConsistent] at hAllCons
    have hCons0 := hAllCons.1 0 (by decide)
    have hCons1 := hAllCons.2 0 (by decide)
    rw [hFold0Eq] at hCons0
    rw [hFold1Eq] at hCons1
    let table0 := st0.headD []
    let table1 := st1.headD []
    have hSt0 : ∃ rest0, st0 = table0 :: rest0 ∧ rest0 = [] := by
      cases st0 with
      | nil => simp [stageTableTrajectoryOk] at hCons0
      | cons w0 ws0 =>
        cases ws0 with
        | nil => exact ⟨[], rfl, rfl⟩
        | cons _ _ => simp [stageTableTrajectoryOk] at hCons0
    obtain ⟨_, hSt0Eq, rfl⟩ := hSt0
    have hSt1 : ∃ rest1, st1 = table1 :: rest1 ∧ rest1 = [] := by
      cases st1 with
      | nil => simp [stageTableTrajectoryOk] at hCons1
      | cons w1 ws1 =>
        cases ws1 with
        | nil => exact ⟨[], rfl, rfl⟩
        | cons _ _ => simp [stageTableTrajectoryOk] at hCons1
    obtain ⟨_, hSt1Eq, rfl⟩ := hSt1
    rw [hSt0Eq] at hCons0
    rw [hSt1Eq] at hCons1
    simp only [sbox7Stage0Dom, stageTableTrajectoryOk, stageTerminalTableOk,
      expectedSlotOk, Nat.zero_mod, Nat.zero_div, Nat.zero_add, ↓reduceIte,
      Bool.and_eq_true, decide_eq_true_eq] at hCons0
    rw [invTwoGold_mul_invOmega8Pow_zero] at hCons0
    have hT1_0 : table1.getD 0 CommRingOps.zero =
        CommRingOps.add (recoverLinearCoeffs8 table0).1
          (CommRingOps.mul r0 (recoverLinearCoeffs8 table0).2) := hCons0.2.2
    have hCw1 : isConstExt4Rs 16 table1 = true := by
      simpa [rsSbox7TraceArith, rsSbox7TraceArithDelta, table1] using
        hAllCw 1 sbox7Stage1Dom [table1] rfl (by simp [hSt1Eq])
    have hT1_8 : table1.getD 8 CommRingOps.zero = table1.getD 0 CommRingOps.zero := by
      rw [← ext4Zero_eq_ringZero]
      exact isConstExt4Rs_eq_head hCw1 (by decide)
    simp only [sbox7Stage1Dom, stageTableTrajectoryOk, stageTerminalTableOk,
      finalValueOk, expectedSlotOk, Nat.zero_mod, Nat.zero_add,
      Bool.and_eq_true, decide_eq_true_eq] at hCons1
    rw [hT1_8, foldDuetExt4_const] at hCons1
    have hFinal0 : proof.finalWord.getD 0 GoldilocksExt4.zero =
        CommRingOps.add (recoverLinearCoeffs8 table0).1
          (CommRingOps.mul r0 (recoverLinearCoeffs8 table0).2) := by
      rw [List.getD_eq_getElem?_getD, hCons1.2, Option.getD_some, hT1_0]
    have hGoalEq :
        verifySumcheckChain ((rsSbox7TraceArith seed root).honestClaim (([st0, st1].headD []).headD []))
          (adaptivePolys ((rsSbox7TraceArith seed root).honestRound (([st0, st1].headD []).headD []))
            proof.agg.challenges)
          proof.agg.challenges
          ((rsSbox7TraceArith seed root).terminal proof.finalWord proof.agg.challenges
            (collectAllFoldChallenges proof)) =
        verifySumcheckChain
          (CommRingOps.add (RoundPoly.evalCoeffs (honestSbox7RoundPoly seed root table0) GoldilocksExt4.zero)
            (RoundPoly.evalCoeffs (honestSbox7RoundPoly seed root table0) GoldilocksExt4.one))
          [honestSbox7RoundPoly seed root table0] [r0]
          (CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one r0)
            (CommRingOps.add (pow7Ext4 (proof.finalWord.getD 0 GoldilocksExt4.zero))
              (GoldilocksExt4.embedBase (CommRingOps.sub seed root)))) := by
      rw [hChEq, hSt0Eq]
      rfl
    rw [hGoalEq, hFinal0]
    exact sbox7_sumcheck_step_complete (honestSbox7RoundPoly seed root table0) r0 _
      (honestSbox7RoundPoly_length_le_9 seed root table0)
      (honestSbox7RoundPoly_eval seed root table0 r0)
  sound table0 bitmap hCode0 hBmLen hSigsFalse := by
    cases bitmap with
    | nil => cases hBmLen
    | cons b0 bs =>
      cases bs with
      | cons _ _ =>
        exfalso
        simp only [rsSbox7Inst, List.length_cons, List.length_nil] at hBmLen
        omega
      | nil =>
        simp only [rsSbox7Inst, rsSbox7TraceArith, rsSbox7TraceArithDelta, decodeSbox7Sigs,
          checkAllActiveSigners, Bool.and_true] at hSigsFalse
        cases b0 with
        | false => nomatch hSigsFalse
        | true =>
          simp only [↓reduceIte, verifyPqHashSig_sbox7_iff, decide_eq_false_iff_not] at hSigsFalse
          have hBaseAll : table0.all GoldilocksExt4.isBase = true ∧ table0.length = 8 := by
            simp only [RowArithmetization.isRound0Codeword, rsSbox7TraceArith,
              rsSbox7TraceArithDelta, ↓reduceIte,
              isLinearBaseRs8, Bool.and_eq_true, beq_iff_eq] at hCode0
            exact ⟨hCode0.1.2, hCode0.1.1⟩
          have ht0Base : GoldilocksExt4.isBase (table0.getD 0 GoldilocksExt4.zero) = true := by
            have h0Lt : 0 < table0.length := by omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0Lt, Option.getD_some]
            exact List.all_eq_true.mp hBaseAll.1 _ (List.getElem_mem h0Lt)
          have ht4Base : GoldilocksExt4.isBase (table0.getD 4 GoldilocksExt4.zero) = true := by
            have h4Lt : 4 < table0.length := by omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h4Lt, Option.getD_some]
            exact List.all_eq_true.mp hBaseAll.1 _ (List.getElem_mem h4Lt)
          have hc0Base : (recoverLinearCoeffs8 table0).1 =
              GoldilocksExt4.embedBase (recoverLinearCoeffs8 table0).1.c0.c0 := by
            apply GoldilocksExt4.eq_embedBase_of_isBase
            dsimp only [recoverLinearCoeffs8]
            rw [GoldilocksExt4.eq_embedBase_of_isBase ht0Base,
                GoldilocksExt4.eq_embedBase_of_isBase ht4Base,
                ← GoldilocksExt4.embedBase_add, ← GoldilocksExt4.embedBase_mul]
            exact GoldilocksExt4.isBase_embedBase _
          intro hZero
          change CommRingOps.add
            (RoundPoly.evalCoeffs (honestSbox7RoundPoly seed root table0) GoldilocksExt4.zero)
            (RoundPoly.evalCoeffs (honestSbox7RoundPoly seed root table0) GoldilocksExt4.one) =
            GoldilocksExt4.zero at hZero
          rw [honestSbox7RoundPoly_eval seed root table0 GoldilocksExt4.zero,
              honestSbox7RoundPoly_eval seed root table0 GoldilocksExt4.one,
              hc0Base] at hZero
          exact hSigsFalse (sbox7_sum_zero_sound seed root
            (recoverLinearCoeffs8 table0).1.c0.c0 (recoverLinearCoeffs8 table0).2 hZero)

/-! ## 12. End-to-End 2-Stage WHIR Prover Witness & `#tooth` Regressions -/

attribute [local irreducible] cshake256Bytes pcsMerkleHash squeezeExt4Challenge
  deriveStageQueryIndices honestSbox7RoundPoly honestSbox7RoundPolyDelta pow7Ext4 pow7Goldilocks

def hashPairLayer (H : Hash) (leafAt : Nat → List UInt8) : Nat → List UInt8 :=
  fun j => H (encodeMultiFrame [leafAt (2 * j), leafAt (2 * j + 1)])

def buildMerkleRootByDepth (H : Hash) : (d : Nat) → (Nat → List UInt8) → List UInt8
  | 0, leafAt => leafAt 0
  | d + 1, leafAt => buildMerkleRootByDepth H d (hashPairLayer H leafAt)

def buildMerklePathByDepth (H : Hash) : (d : Nat) → (Nat → List UInt8) → Nat → List (List UInt8)
  | 0, _, _ => []
  | d + 1, leafAt, idx =>
    let sib := if idx % 2 = 0 then leafAt (idx + 1) else leafAt (idx - 1)
    sib :: buildMerklePathByDepth H d (hashPairLayer H leafAt) (idx / 2)

theorem buildMerklePathByDepth_length (H : Hash) :
    ∀ (d : Nat) (leafAt : Nat → List UInt8) (idx : Nat),
      (buildMerklePathByDepth H d leafAt idx).length = d
  | 0, _, _ => rfl
  | d + 1, leafAt, idx => by
    simp [buildMerklePathByDepth, buildMerklePathByDepth_length H d]

theorem buildMerklePathByDepth_root (H : Hash) :
    ∀ (d : Nat) (leafAt : Nat → List UInt8) (idx : Nat),
      idx < 2 ^ d →
      merklePathRoot H (leafAt idx) idx (buildMerklePathByDepth H d leafAt idx) =
        buildMerkleRootByDepth H d leafAt
  | 0, leafAt, idx, hLt => by
    have h0 : idx = 0 := by omega
    subst h0; rfl
  | d + 1, leafAt, idx, hLt => by
    have hDiv : idx / 2 < 2 ^ d := by
      rw [Nat.pow_succ] at hLt; omega
    simp only [buildMerklePathByDepth, merklePathRoot, buildMerkleRootByDepth]
    have hNode : H (merkleNodeFrame idx (leafAt idx)
        (if idx % 2 = 0 then leafAt (idx + 1) else leafAt (idx - 1))) =
        hashPairLayer H leafAt (idx / 2) := by
      unfold merkleNodeFrame hashPairLayer
      by_cases hPar : idx % 2 = 0
      · have e0 : 2 * (idx / 2) = idx := by omega
        simp only [hPar, ↓reduceIte, e0]
      · have e1 : 2 * (idx / 2) + 1 = idx := by omega
        have e0 : 2 * (idx / 2) = idx - 1 := by omega
        simp only [hPar, ↓reduceIte]
        rw [e1, e0]
    rw [hNode]
    exact buildMerklePathByDepth_root H d (hashPairLayer H leafAt) (idx / 2) hDiv

private theorem map_const_deriveStageShiftChallenges_one (prior r : List UInt8)
    (p : List GoldilocksExt4) :
    (deriveStageShiftChallenges prior [r] [p]).map (fun _ => [GoldilocksExt4.zero]) =
      [[GoldilocksExt4.zero]] := rfl

private theorem replicate8_getD_zero (v : GoldilocksExt4) :
    (List.replicate 8 v).getD 0 GoldilocksExt4.zero = v := rfl

private def sbox7Leaf0 (table0 : List GoldilocksExt4) (g : Nat) : List UInt8 :=
  pcsMerkleHash (duetLeafFrame 0 0 g
    (table0.getD g GoldilocksExt4.zero) (table0.getD (g + 4) GoldilocksExt4.zero))

private def sbox7Leaf1 (table1 : List GoldilocksExt4) (g : Nat) : List UInt8 :=
  pcsMerkleHash (duetLeafFrame 1 0 g
    (table1.getD g GoldilocksExt4.zero) (table1.getD (g + 8) GoldilocksExt4.zero))

private def sbox7Stage0Proof (x0 b1 : Goldilocks) (prior0 root1 : List UInt8)
    (rowChalls : List GoldilocksExt4) (pr0 : GoldilocksExt4) : WhirStageProof :=
  let table0 := encodeLinearRs8 x0 b1
  let leaf0 := sbox7Leaf0 table0
  let root0 := buildMerkleRootByDepth pcsMerkleHash 2 leaf0
  let finalWord := List.replicate 8 pr0
  let oods0 := deriveStageOodChallenges prior0 root0
  let oodEval0_0 := CommRingOps.add (GoldilocksExt4.embedBase x0)
    (CommRingOps.mul oods0.1 (GoldilocksExt4.embedBase b1))
  let oodEval0_1 := CommRingOps.add (GoldilocksExt4.embedBase x0)
    (CommRingOps.mul oods0.2 (GoldilocksExt4.embedBase b1))
  let sp0Pre : WhirStageProof :=
    { stageRoot := root0, oodChallenges := oods0, oodEvals := (oodEval0_0, oodEval0_1),
      shiftClaim := GoldilocksExt4.zero, shiftPolys := [[GoldilocksExt4.zero]],
      layerRoots := [], shiftChallenges := [], foldChallenges := [],
      shiftTerminalEval := GoldilocksExt4.zero, powNonce := 0, queries := [] }
  let shiftCh0 := deriveStageShiftChallenges (stagePostOodTranscript prior0 sp0Pre)
    [root0] [[GoldilocksExt4.zero]]
  let pSeed0 := stagePowSeed prior0 sp0Pre (some root1) finalWord
  let qSeed0 := stageQuerySeed pSeed0 0
  let qIdx0 := deriveStageQueryIndices sbox7Stage0Dom qSeed0
  let leaf1 := sbox7Leaf1 (List.replicate 16 pr0)
  let qs0 := qIdx0.map (fun idx =>
    ({ index := idx
       layers := [{ v0 := table0.getD idx GoldilocksExt4.zero
                    v1 := table0.getD (idx + 4) GoldilocksExt4.zero
                    path := buildMerklePathByDepth pcsMerkleHash 2 leaf0 idx }]
       nextStageBridge := some
         { v0 := pr0
           v1 := pr0
           path := buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx } } : StageQueryOpening))
  { sp0Pre with shiftChallenges := shiftCh0, foldChallenges := rowChalls, queries := qs0 }

private def sbox7Stage1Proof (prior1 : List UInt8) (pr0 : GoldilocksExt4) : WhirStageProof :=
  let table1 := List.replicate 16 pr0
  let leaf1 := sbox7Leaf1 table1
  let root1 := buildMerkleRootByDepth pcsMerkleHash 3 leaf1
  let finalWord := List.replicate 8 pr0
  let oods1 := deriveStageOodChallenges prior1 root1
  let sp1Pre : WhirStageProof :=
    { stageRoot := root1, oodChallenges := oods1, oodEvals := (pr0, pr0),
      shiftClaim := GoldilocksExt4.zero, shiftPolys := [[GoldilocksExt4.zero]],
      layerRoots := [], shiftChallenges := [], foldChallenges := [],
      shiftTerminalEval := GoldilocksExt4.zero, powNonce := 0, queries := [] }
  let shiftCh1 := deriveStageShiftChallenges (stagePostOodTranscript prior1 sp1Pre)
    [root1] [[GoldilocksExt4.zero]]
  let pSeed1 := stagePowSeed prior1 sp1Pre none finalWord
  let qSeed1 := stageQuerySeed pSeed1 0
  let qIdx1 := deriveStageQueryIndices sbox7Stage1Dom qSeed1
  let qs1 := qIdx1.map (fun idx =>
    ({ index := idx
       layers := [{ v0 := pr0
                    v1 := pr0
                    path := buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx }]
       nextStageBridge := none } : StageQueryOpening))
  { sp1Pre with shiftChallenges := shiftCh1, foldChallenges := shiftCh1, queries := qs1 }

private theorem sbox7Stage0Proof_stageRoot (x0 b1 : Goldilocks) (prior0 root1 : List UInt8)
    (rowChalls : List GoldilocksExt4) (pr0 : GoldilocksExt4) :
    (sbox7Stage0Proof x0 b1 prior0 root1 rowChalls pr0).stageRoot =
      buildMerkleRootByDepth pcsMerkleHash 2 (sbox7Leaf0 (encodeLinearRs8 x0 b1)) := rfl

private theorem sbox7Stage0Proof_allRoots (x0 b1 : Goldilocks) (prior0 root1 : List UInt8)
    (rowChalls : List GoldilocksExt4) (pr0 : GoldilocksExt4) :
    stageAllRoots (sbox7Stage0Proof x0 b1 prior0 root1 rowChalls pr0) =
      [buildMerkleRootByDepth pcsMerkleHash 2 (sbox7Leaf0 (encodeLinearRs8 x0 b1))] := rfl

private theorem sbox7Stage1Proof_stageRoot (prior1 : List UInt8) (pr0 : GoldilocksExt4) :
    (sbox7Stage1Proof prior1 pr0).stageRoot =
      buildMerkleRootByDepth pcsMerkleHash 3 (sbox7Leaf1 (List.replicate 16 pr0)) := rfl

private theorem sbox7Stage1Proof_allRoots (prior1 : List UInt8) (pr0 : GoldilocksExt4) :
    stageAllRoots (sbox7Stage1Proof prior1 pr0) =
      [buildMerkleRootByDepth pcsMerkleHash 3 (sbox7Leaf1 (List.replicate 16 pr0))] := rfl

private theorem verifyOneWhirStage_sbox7Stage0Proof (x0 b1 : Goldilocks)
    (prior0 : List UInt8) (rowChalls : List GoldilocksExt4) (r0 : GoldilocksExt4)
    (hRowChallsEq : rowChalls = [r0]) :
    let pr0 := CommRingOps.add (GoldilocksExt4.embedBase x0)
      (CommRingOps.mul r0 (GoldilocksExt4.embedBase b1))
    let root1 := buildMerkleRootByDepth pcsMerkleHash 3 (sbox7Leaf1 (List.replicate 16 pr0))
    verifyOneWhirStage rowChalls (List.replicate 8 pr0) prior0 sbox7Stage0Dom
      (sbox7Stage0Proof x0 b1 prior0 root1 rowChalls pr0)
      (some (sbox7Stage1Dom, root1)) = true := by
  intro pr0 root1
  let table0 := encodeLinearRs8 x0 b1
  let leaf0 := sbox7Leaf0 table0
  let root0 := buildMerkleRootByDepth pcsMerkleHash 2 leaf0
  let finalWord := List.replicate 8 pr0
  let oods0 := deriveStageOodChallenges prior0 root0
  let oodEval0_0 := CommRingOps.add (GoldilocksExt4.embedBase x0)
    (CommRingOps.mul oods0.1 (GoldilocksExt4.embedBase b1))
  let oodEval0_1 := CommRingOps.add (GoldilocksExt4.embedBase x0)
    (CommRingOps.mul oods0.2 (GoldilocksExt4.embedBase b1))
  let sp0Pre : WhirStageProof :=
    { stageRoot := root0, oodChallenges := oods0, oodEvals := (oodEval0_0, oodEval0_1),
      shiftClaim := GoldilocksExt4.zero, shiftPolys := [[GoldilocksExt4.zero]],
      layerRoots := [], shiftChallenges := [], foldChallenges := [],
      shiftTerminalEval := GoldilocksExt4.zero, powNonce := 0, queries := [] }
  let shiftCh0 := deriveStageShiftChallenges (stagePostOodTranscript prior0 sp0Pre)
    [root0] [[GoldilocksExt4.zero]]
  let pSeed0 := stagePowSeed prior0 sp0Pre (some root1) finalWord
  let qSeed0 := stageQuerySeed pSeed0 0
  let qIdx0 := deriveStageQueryIndices sbox7Stage0Dom qSeed0
  let table1 := List.replicate 16 pr0
  let leaf1 := sbox7Leaf1 table1
  let qs0 := qIdx0.map (fun idx =>
    ({ index := idx
       layers := [{ v0 := table0.getD idx GoldilocksExt4.zero
                    v1 := table0.getD (idx + 4) GoldilocksExt4.zero
                    path := buildMerklePathByDepth pcsMerkleHash 2 leaf0 idx }]
       nextStageBridge := some
         { v0 := pr0
           v1 := pr0
           path := buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx } } : StageQueryOpening))
  let sp0 : WhirStageProof :=
    { sp0Pre with shiftChallenges := shiftCh0, foldChallenges := rowChalls, queries := qs0 }
  change verifyOneWhirStage rowChalls finalWord prior0 sbox7Stage0Dom sp0
    (some (sbox7Stage1Dom, root1)) = true
  have hTable1Get : ∀ j, j < 16 → table1.getD j GoldilocksExt4.zero = pr0 := by
    intro j hj
    have hjLt : j < table1.length := by simpa [table1] using hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjLt, Option.getD_some]
    exact List.getElem_replicate hjLt
  have hDepth4 : merkleDepth 4 = 2 := rfl
  have hDepth8 : merkleDepth 8 = 3 := rfl
  unfold verifyOneWhirStage
  dsimp only [Option.map]
  have hPowSeed0 : stagePowSeed prior0 sp0 (some root1) finalWord = pSeed0 := rfl
  have hQSeed0 : stageQuerySeed pSeed0 sp0.powNonce = qSeed0 := rfl
  have hOod0 : sp0.oodChallenges = deriveStageOodChallenges prior0 sp0.stageRoot := rfl
  have hRootsLen0 : (stageAllRoots sp0).length = sbox7Stage0Dom.foldLayers := rfl
  have hPolysLen0 : sp0.shiftPolys.length = sbox7Stage0Dom.foldLayers := rfl
  have hShiftCh0 : sp0.shiftChallenges =
      deriveStageShiftChallenges (stagePostOodTranscript prior0 sp0)
        (stageAllRoots sp0) sp0.shiftPolys := rfl
  have hFoldCh0 : sp0.foldChallenges =
      (if sbox7Stage0Dom.bindRowChallenges then rowChalls else sp0.shiftChallenges) := rfl
  have hFoldLen0 : sp0.foldChallenges.length = sbox7Stage0Dom.foldLayers := by
    dsimp only [sp0, sbox7Stage0Dom]
    rw [hRowChallsEq]
    rfl
  have hShiftOk0 : verifyShiftSumcheckChain sp0.shiftClaim sp0.shiftPolys
      sp0.shiftChallenges sp0.shiftTerminalEval = true := by
    dsimp only [sp0, sp0Pre]
    rw [← map_const_deriveStageShiftChallenges_one (stagePostOodTranscript prior0 sp0Pre)
      root0 [GoldilocksExt4.zero]]
    exact verifySumcheckChainDeg_zeroPolys 2 shiftCh0
  have hPowOk0 : verifyWhirStagePow (stagePowDigest pSeed0) sp0.powNonce
      sbox7Stage0Dom.powBits = true := rfl
  have hQp0 := deriveStageQueryIndices_props sbox7Stage0Dom qSeed0 (by decide)
  have hMapIdx0 : sp0.queries.map (·.index) = qIdx0 := by
    dsimp only [sp0, qs0]
    rw [List.map_map]
    exact List.map_id _
  have hQIdx0Eq : qIdx0 = deriveStageQueryIndices sbox7Stage0Dom qSeed0 := rfl
  have hLenQs0 : sp0.queries.length = min sbox7Stage0Dom.numQueries sbox7Stage0Dom.groups0 := by
    dsimp only [sp0, qs0]
    rw [List.length_map]
    exact hQp0.2.1
  rw [hPowSeed0, hQSeed0, decide_eq_true hOod0, decide_eq_true hRootsLen0,
      decide_eq_true hPolysLen0, decide_eq_true hShiftCh0, decide_eq_true hFoldCh0,
      decide_eq_true hFoldLen0, hShiftOk0, hPowOk0, hMapIdx0, decide_eq_true hQIdx0Eq,
      hQp0.1, decide_eq_true hLenQs0]
  simp only [Bool.true_and]
  have hRoots0 : stageAllRoots sp0 = [root0] := rfl
  have hFold0Eq : sp0.foldChallenges = [r0] := hRowChallsEq
  rw [hRoots0, hFold0Eq]
  dsimp only [sp0, qs0]
  apply List.all_eq_true.mpr
  intro q hq
  obtain ⟨idx, hIdxMem, rfl⟩ := List.mem_map.mp hq
  have hIdxLt : idx < 4 := hQp0.2.2 idx hIdxMem
  have hMod4 : idx % 4 = idx := Nat.mod_eq_of_lt hIdxLt
  have hMod8 : idx % 8 = idx := Nat.mod_eq_of_lt (by omega)
  have hDiv8 : idx / 8 = 0 := Nat.div_eq_of_lt (by omega)
  have hFoldIdx : foldDuetExt4 (table0.getD idx GoldilocksExt4.zero)
      (table0.getD (idx + 4) GoldilocksExt4.zero)
      (CommRingOps.mul invTwoGold (invOmega8Pow idx)) invTwoGold r0 = pr0 :=
    foldDuetExt4_encodeLinearRs8_all x0 b1 r0 hIdxLt
  have hRootPath0 : merklePathRoot pcsMerkleHash (leaf0 idx) idx
      (buildMerklePathByDepth pcsMerkleHash 2 leaf0 idx) = root0 :=
    buildMerklePathByDepth_root pcsMerkleHash 2 leaf0 idx hIdxLt
  have hLenPath0 := buildMerklePathByDepth_length pcsMerkleHash 2 leaf0 idx
  have hRootPath1 : merklePathRoot pcsMerkleHash (leaf1 idx) idx
      (buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx) = root1 :=
    buildMerklePathByDepth_root pcsMerkleHash 3 leaf1 idx (by omega)
  have hLenPath1 := buildMerklePathByDepth_length pcsMerkleHash 3 leaf1 idx
  have hLeaf0Eq : pcsMerkleHash (duetLeafFrame 0 0 idx (table0.getD idx GoldilocksExt4.zero)
      (table0.getD (idx + 4) GoldilocksExt4.zero)) = leaf0 idx := rfl
  have hLeaf1Eq : pcsMerkleHash (duetLeafFrame 1 0 idx pr0 pr0) = leaf1 idx := by
    dsimp only [leaf1, sbox7Leaf1]
    rw [hTable1Get idx (by omega), hTable1Get (idx + 8) (by omega)]
  have h4Pos : (0 : Nat) < 4 := by decide
  have h8Pos : (0 : Nat) < 8 := by decide
  simp only [sbox7Stage0Dom, sbox7Stage1Dom, hIdxLt, h4Pos, h8Pos, decide_true, Bool.true_and,
    verifyStageTrajectory, verifyStageTerminalTarget, expectedSlotOk,
    hMod4, hMod8, hDiv8, hDepth4, hDepth8, hLenPath0, hLenPath1, ↓reduceIte]
  rw [hLeaf0Eq, hRootPath0, hFoldIdx, hLeaf1Eq, hRootPath1]
  simp

private theorem verifyOneWhirStage_sbox7Stage1Proof (rowChalls : List GoldilocksExt4)
    (prior1 : List UInt8) (pr0 : GoldilocksExt4) :
    verifyOneWhirStage rowChalls (List.replicate 8 pr0) prior1 sbox7Stage1Dom
      (sbox7Stage1Proof prior1 pr0) none = true := by
  let table1 := List.replicate 16 pr0
  let leaf1 := sbox7Leaf1 table1
  let root1 := buildMerkleRootByDepth pcsMerkleHash 3 leaf1
  let finalWord := List.replicate 8 pr0
  let oods1 := deriveStageOodChallenges prior1 root1
  let sp1Pre : WhirStageProof :=
    { stageRoot := root1, oodChallenges := oods1, oodEvals := (pr0, pr0),
      shiftClaim := GoldilocksExt4.zero, shiftPolys := [[GoldilocksExt4.zero]],
      layerRoots := [], shiftChallenges := [], foldChallenges := [],
      shiftTerminalEval := GoldilocksExt4.zero, powNonce := 0, queries := [] }
  let shiftCh1 := deriveStageShiftChallenges (stagePostOodTranscript prior1 sp1Pre)
    [root1] [[GoldilocksExt4.zero]]
  let pSeed1 := stagePowSeed prior1 sp1Pre none finalWord
  let qSeed1 := stageQuerySeed pSeed1 0
  let qIdx1 := deriveStageQueryIndices sbox7Stage1Dom qSeed1
  let qs1 := qIdx1.map (fun idx =>
    ({ index := idx
       layers := [{ v0 := pr0
                    v1 := pr0
                    path := buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx }]
       nextStageBridge := none } : StageQueryOpening))
  let sp1 : WhirStageProof :=
    { sp1Pre with shiftChallenges := shiftCh1, foldChallenges := shiftCh1, queries := qs1 }
  change verifyOneWhirStage rowChalls finalWord prior1 sbox7Stage1Dom sp1 none = true
  have hTable1Get : ∀ j, j < 16 → table1.getD j GoldilocksExt4.zero = pr0 := by
    intro j hj
    have hjLt : j < table1.length := by simpa [table1] using hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjLt, Option.getD_some]
    exact List.getElem_replicate hjLt
  have hFinalGet : ∀ j, j < 8 → finalWord[j]? = some pr0 := by
    intro j hj
    have hjLt : j < finalWord.length := by simpa [finalWord] using hj
    rw [List.getElem?_eq_getElem hjLt, List.getElem_replicate]
  have hDepth8 : merkleDepth 8 = 3 := rfl
  unfold verifyOneWhirStage
  dsimp only [Option.map]
  have hPowSeed1 : stagePowSeed prior1 sp1 none finalWord = pSeed1 := rfl
  have hQSeed1 : stageQuerySeed pSeed1 sp1.powNonce = qSeed1 := rfl
  have hOod1 : sp1.oodChallenges = deriveStageOodChallenges prior1 sp1.stageRoot := rfl
  have hRootsLen1 : (stageAllRoots sp1).length = sbox7Stage1Dom.foldLayers := rfl
  have hPolysLen1 : sp1.shiftPolys.length = sbox7Stage1Dom.foldLayers := rfl
  have hShiftCh1 : sp1.shiftChallenges =
      deriveStageShiftChallenges (stagePostOodTranscript prior1 sp1)
        (stageAllRoots sp1) sp1.shiftPolys := rfl
  have hFoldCh1 : sp1.foldChallenges =
      (if sbox7Stage1Dom.bindRowChallenges then rowChalls else sp1.shiftChallenges) := rfl
  have hFoldLen1 : sp1.foldChallenges.length = sbox7Stage1Dom.foldLayers := rfl
  have hShiftOk1 : verifyShiftSumcheckChain sp1.shiftClaim sp1.shiftPolys
      sp1.shiftChallenges sp1.shiftTerminalEval = true := by
    dsimp only [sp1, sp1Pre]
    rw [← map_const_deriveStageShiftChallenges_one (stagePostOodTranscript prior1 sp1Pre)
      root1 [GoldilocksExt4.zero]]
    exact verifySumcheckChainDeg_zeroPolys 2 shiftCh1
  have hPowOk1 : verifyWhirStagePow (stagePowDigest pSeed1) sp1.powNonce
      sbox7Stage1Dom.powBits = true := rfl
  have hQp1 := deriveStageQueryIndices_props sbox7Stage1Dom qSeed1 (by decide)
  have hMapIdx1 : sp1.queries.map (·.index) = qIdx1 := by
    dsimp only [sp1, qs1]
    rw [List.map_map]
    exact List.map_id _
  have hQIdx1Eq : qIdx1 = deriveStageQueryIndices sbox7Stage1Dom qSeed1 := rfl
  have hLenQs1 : sp1.queries.length = min sbox7Stage1Dom.numQueries sbox7Stage1Dom.groups0 := by
    dsimp only [sp1, qs1]
    rw [List.length_map]
    exact hQp1.2.1
  rw [hPowSeed1, hQSeed1, decide_eq_true hOod1, decide_eq_true hRootsLen1,
      decide_eq_true hPolysLen1, decide_eq_true hShiftCh1, decide_eq_true hFoldCh1,
      decide_eq_true hFoldLen1, hShiftOk1, hPowOk1, hMapIdx1, decide_eq_true hQIdx1Eq,
      hQp1.1, decide_eq_true hLenQs1]
  simp only [Bool.true_and]
  let α1 := shiftCh1.headD GoldilocksExt4.zero
  have hRoots1 : stageAllRoots sp1 = [root1] := rfl
  have hFold1Eq : sp1.foldChallenges = [α1] := rfl
  rw [hRoots1, hFold1Eq]
  dsimp only [sp1, qs1]
  apply List.all_eq_true.mpr
  intro q hq
  obtain ⟨idx, hIdxMem, rfl⟩ := List.mem_map.mp hq
  have hIdxLt : idx < 8 := hQp1.2.2 idx hIdxMem
  have hMod8 : idx % 8 = idx := Nat.mod_eq_of_lt hIdxLt
  have hRootPath1 : merklePathRoot pcsMerkleHash (leaf1 idx) idx
      (buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx) = root1 :=
    buildMerklePathByDepth_root pcsMerkleHash 3 leaf1 idx hIdxLt
  have hLenPath1 := buildMerklePathByDepth_length pcsMerkleHash 3 leaf1 idx
  have hLeaf1Eq : pcsMerkleHash (duetLeafFrame 1 0 idx pr0 pr0) = leaf1 idx := by
    dsimp only [leaf1, sbox7Leaf1]
    rw [hTable1Get idx (by omega), hTable1Get (idx + 8) (by omega)]
  have h8Pos : (0 : Nat) < 8 := by decide
  simp only [sbox7Stage1Dom, hIdxLt, h8Pos, decide_true, Bool.true_and, verifyStageTrajectory,
    verifyStageTerminalTarget, finalValueOk, expectedSlotOk,
    hMod8, hDepth8, hLenPath1, foldDuetExt4_const]
  rw [hLeaf1Eq, hRootPath1, hFinalGet idx hIdxLt]
  simp

private theorem aggregateInstanceFrame_congr (inst : AggPublicInstance)
    (a b : AggregatedSignature)
    (h1 : a.bitmap = b.bitmap) (h2 : a.traceCommitment = b.traceCommitment)
    (h3 : a.childrenCommitment = b.childrenCommitment) :
    aggregateInstanceFrame inst a = aggregateInstanceFrame inst b := by
  unfold aggregateInstanceFrame
  rw [h1, h2, h3]

attribute [local irreducible] sbox7Stage0Proof sbox7Stage1Proof
  buildMerkleRootByDepth buildMerklePathByDepth encodeLinearRs8
  aggregateInstanceFrame rowSumcheckTranscriptTail stagePowSeed stageQuerySeed
  Goldilocks.add Goldilocks.mul Goldilocks.sub Goldilocks.neg
  GoldilocksExt2.add GoldilocksExt2.mul GoldilocksExt2.sub GoldilocksExt2.neg
  QuarticGoldilocks.add QuarticGoldilocks.mul QuarticGoldilocks.sub QuarticGoldilocks.neg

/-- Constructive end-to-end 2-stage `GoldilocksExt4` WHIR prover for `rsSbox7TraceArith`. -/
def buildHonestSbox7WhirBundle (seed x0 b1 : Goldilocks) (msg : List UInt8) :
    SuccinctAggregateProof × List UInt8 × SuccinctExtractionView :=
  let root := CommRingOps.add (pow7Goldilocks x0) seed
  let inst := rsSbox7Inst seed root msg
  let table0 := encodeLinearRs8 x0 b1
  let leaf0 := sbox7Leaf0 table0
  let root0 := buildMerkleRootByDepth pcsMerkleHash 2 leaf0
  let pRow := honestSbox7RoundPoly seed root table0
  let aggStub : AggregatedSignature :=
    { suite := sbox7FieldSuite, params := sbox7Params, regime := .bciksJohnsonQrom128,
      bitmap := [true], signerCount := 1, traceCommitment := root0,
      claimedSum := GoldilocksExt4.zero, roundPolys := [], challenges := [],
      terminalEval := GoldilocksExt4.zero, childrenCommitment := none }
  let fs := aggregateInstanceFrame inst aggStub
  let rowChalls := deriveRowSumcheckChallenges fs [pRow]
  let r0 := rowChalls.headD GoldilocksExt4.zero
  let pr0 := CommRingOps.add (GoldilocksExt4.embedBase x0)
    (CommRingOps.mul r0 (GoldilocksExt4.embedBase b1))
  let agg : AggregatedSignature :=
    { suite := sbox7FieldSuite, params := sbox7Params, regime := .bciksJohnsonQrom128,
      bitmap := [true], signerCount := 1, traceCommitment := root0,
      claimedSum := GoldilocksExt4.zero, roundPolys := [pRow], challenges := rowChalls,
      terminalEval := RoundPoly.evalCoeffs pRow r0, childrenCommitment := none }
  let table1 := List.replicate 16 pr0
  let leaf1 := sbox7Leaf1 table1
  let root1 := buildMerkleRootByDepth pcsMerkleHash 3 leaf1
  let finalWord := List.replicate 8 pr0
  let prior0 := rowSumcheckTranscriptTail fs [pRow]
  let sp0 := sbox7Stage0Proof x0 b1 prior0 root1 rowChalls pr0
  let prior1 := stageQuerySeed (stagePowSeed prior0 sp0 (some root1) finalWord) sp0.powNonce
  let sp1 := sbox7Stage1Proof prior1 pr0
  let authPath : Nat → Nat → Nat → List (List UInt8) := fun stIdx _ g =>
    if stIdx = 0 then buildMerklePathByDepth pcsMerkleHash 2 leaf0 g
    else buildMerklePathByDepth pcsMerkleHash 3 leaf1 g
  ({ agg := agg, stages := [sp0, sp1], finalWord := finalWord },
   fs,
   { allTables := [[table0], [table1]], authPath := authPath })

set_option maxHeartbeats 1000000 in
/-- **Completeness of Honest 2-Stage `GoldilocksExt4` WHIR Prover (`honestSbox7WhirProof_accepts`)**:
    For every valid degree-7 S-box witness `(seed, x0, b1, msg)`, the constructed 2-stage WHIR
    proof passes `verifySuccinctAggregate` and satisfies `StagesBound` with zero `cSHAKE256`
    axioms or shortcuts. -/
theorem honestSbox7WhirProof_accepts (seed x0 b1 : Goldilocks) (msg : List UInt8) :
    let root := CommRingOps.add (pow7Goldilocks x0) seed
    let bundle := buildHonestSbox7WhirBundle seed x0 b1 msg
    verifySuccinctAggregate (rsSbox7TraceArith seed root) rsSbox7WhirDomain
      (rsSbox7Inst seed root msg) bundle.1 bundle.2.1 = true ∧
    StagesBound bundle.2.2.authPath rsSbox7WhirDomain.stages bundle.2.2.allTables bundle.1.stages := by
  intro root bundle
  let inst := rsSbox7Inst seed root msg
  let table0 := encodeLinearRs8 x0 b1
  let leaf0 := sbox7Leaf0 table0
  let root0 := buildMerkleRootByDepth pcsMerkleHash 2 leaf0
  let pRow := honestSbox7RoundPoly seed root table0
  let aggStub : AggregatedSignature :=
    { suite := sbox7FieldSuite, params := sbox7Params, regime := .bciksJohnsonQrom128,
      bitmap := [true], signerCount := 1, traceCommitment := root0,
      claimedSum := GoldilocksExt4.zero, roundPolys := [], challenges := [],
      terminalEval := GoldilocksExt4.zero, childrenCommitment := none }
  let fs := aggregateInstanceFrame inst aggStub
  let rowChalls := deriveRowSumcheckChallenges fs [pRow]
  let r0 := rowChalls.headD GoldilocksExt4.zero
  let pr0 := CommRingOps.add (GoldilocksExt4.embedBase x0)
    (CommRingOps.mul r0 (GoldilocksExt4.embedBase b1))
  let agg : AggregatedSignature :=
    { suite := sbox7FieldSuite, params := sbox7Params, regime := .bciksJohnsonQrom128,
      bitmap := [true], signerCount := 1, traceCommitment := root0,
      claimedSum := GoldilocksExt4.zero, roundPolys := [pRow], challenges := rowChalls,
      terminalEval := RoundPoly.evalCoeffs pRow r0, childrenCommitment := none }
  let table1 := List.replicate 16 pr0
  let leaf1 := sbox7Leaf1 table1
  let root1 := buildMerkleRootByDepth pcsMerkleHash 3 leaf1
  let finalWord := List.replicate 8 pr0
  let prior0 := rowSumcheckTranscriptTail fs [pRow]
  let sp0 := sbox7Stage0Proof x0 b1 prior0 root1 rowChalls pr0
  let prior1 := stageQuerySeed (stagePowSeed prior0 sp0 (some root1) finalWord) sp0.powNonce
  let sp1 := sbox7Stage1Proof prior1 pr0
  let authPath : Nat → Nat → Nat → List (List UInt8) := fun stIdx _ g =>
    if stIdx = 0 then buildMerklePathByDepth pcsMerkleHash 2 leaf0 g
    else buildMerklePathByDepth pcsMerkleHash 3 leaf1 g
  change verifySuccinctAggregate (rsSbox7TraceArith seed root) rsSbox7WhirDomain
      inst { agg := agg, stages := [sp0, sp1], finalWord := finalWord } fs = true ∧
    StagesBound authPath rsSbox7WhirDomain.stages [[table0], [table1]] [sp0, sp1]
  have hRowChallsEq : rowChalls = [r0] := rfl
  have hRec0 := (isLinearBaseRs8_encodeLinearRs8 x0 b1).2
  have hSumZero : CommRingOps.add (RoundPoly.evalCoeffs pRow GoldilocksExt4.zero)
      (RoundPoly.evalCoeffs pRow GoldilocksExt4.one) = GoldilocksExt4.zero := by
    dsimp only [pRow, table0]
    rw [honestSbox7RoundPoly_eval seed root (encodeLinearRs8 x0 b1) GoldilocksExt4.zero,
        honestSbox7RoundPoly_eval seed root (encodeLinearRs8 x0 b1) GoldilocksExt4.one, hRec0]
    exact sbox7_sum_zero_complete seed x0 (GoldilocksExt4.embedBase b1)
  have hDepth4 : merkleDepth 4 = 2 := rfl
  have hDepth8 : merkleDepth 8 = 3 := rfl
  have hBound : StagesBound authPath rsSbox7WhirDomain.stages [[table0], [table1]] [sp0, sp1] := by
    simp only [StagesBound, rsSbox7WhirDomain, sp0, sp1]
    rw [sbox7Stage0Proof_allRoots, sbox7Stage1Proof_allRoots]
    refine ⟨List.cons_ne_nil _ _, ⟨?_, trivial⟩, List.cons_ne_nil _ _, ⟨?_, trivial⟩, trivial⟩
    · intro g hg
      have hg4 : g < 2 ^ 2 := hg
      dsimp only [authPath, sbox7Stage0Dom]
      simp only [↓reduceIte, hDepth4]
      exact ⟨buildMerklePathByDepth_root pcsMerkleHash 2 leaf0 g hg4,
        buildMerklePathByDepth_length pcsMerkleHash 2 leaf0 g⟩
    · intro g hg
      have hg8 : g < 2 ^ 3 := hg
      dsimp only [authPath, sbox7Stage1Dom]
      simp only [Nat.one_ne_zero, ↓reduceIte, hDepth8]
      exact ⟨buildMerklePathByDepth_root pcsMerkleHash 3 leaf1 g hg8,
        buildMerklePathByDepth_length pcsMerkleHash 3 leaf1 g⟩
  refine ⟨?_, hBound⟩
  unfold verifySuccinctAggregate
  dsimp only
  have hFs : fs = aggregateInstanceFrame inst agg :=
    aggregateInstanceFrame_congr inst aggStub agg rfl rfl rfl
  have hReg : agg.regime = inst.regime := rfl
  have hSuite : agg.suite.suiteId = inst.suite.suiteId := rfl
  have hParams : agg.params = inst.params := rfl
  have hRoot : sp0.stageRoot = agg.traceCommitment :=
    sbox7Stage0Proof_stageRoot x0 b1 prior0 root1 rowChalls pr0
  have hCh : agg.challenges = deriveRowSumcheckChallenges fs agg.roundPolys := rfl
  have hScOk : verifySumcheckChain GoldilocksExt4.zero [pRow] rowChalls
      (RoundPoly.evalCoeffs pRow r0) = true := by
    rw [hRowChallsEq, ← hSumZero]
    exact sbox7_sumcheck_step_complete pRow r0 (RoundPoly.evalCoeffs pRow r0)
      (honestSbox7RoundPoly_length_le_9 seed root table0) rfl
  have hAlgOk : verifyAggregateAlgebra inst.committee agg = true := by
    unfold verifyAggregateAlgebra
    dsimp only [inst, rsSbox7Inst, agg, List.length_cons, List.length_nil, bitmapPopcountSpec]
    rw [hScOk, beq_self_eq_true]
    rfl
  have hTermEq : agg.terminalEval =
      (rsSbox7TraceArith seed root).terminal finalWord agg.challenges
        (collectAllFoldChallenges { agg := agg, stages := [sp0, sp1], finalWord := finalWord }) := by
    dsimp only [agg, rsSbox7TraceArith, rsSbox7TraceArithDelta, finalWord]
    rw [replicate8_getD_zero pr0]
    dsimp only [pRow, table0, r0, pr0]
    rw [honestSbox7RoundPoly_eval seed root (encodeLinearRs8 x0 b1)
          (rowChalls.headD GoldilocksExt4.zero), hRec0]
  have hFinalCw : (rsSbox7TraceArith seed root).isFinalCodeword finalWord = true :=
    isConstExt4Rs_replicate 8 pr0
  rw [decide_eq_true hFs, decide_eq_true hReg, decide_eq_true hSuite, decide_eq_true hParams,
      decide_eq_true hRoot, decide_eq_true hCh, hAlgOk, decide_eq_true hTermEq, hFinalCw]
  simp only [Bool.true_and, rsSbox7WhirDomain, verifyWhirStages]
  rw [sbox7Stage1Proof_stageRoot prior1 pr0]
  exact Bool.and_eq_true_iff.mpr
    ⟨verifyOneWhirStage_sbox7Stage0Proof x0 b1 prior0 rowChalls r0 hRowChallsEq,
     verifyOneWhirStage_sbox7Stage1Proof rowChalls prior1 pr0⟩

/-- **Non-Vacuity of `succinct_aggregation_knowledge_soundness` & `succinct_merge_tree_knowledge_soundness`
    (`succinct_knowledge_soundness_hypotheses_satisfiable`)**:
    Exhibits a concrete non-trivial `RowArithmetization.Lawful` instance, 2-stage WHIR domain,
    public instance, accepting `SuccinctAggregateProof`, `StagesBound` witness, and accepting
    `MergeNode` tree whose Round-0 codeword decodes to a valid `verifyPqHashSig` signature. -/
theorem succinct_knowledge_soundness_hypotheses_satisfiable :
    ∃ (arith : RowArithmetization) (dom : WhirDomain) (inst : AggPublicInstance)
      (_law : arith.Lawful dom inst) (proof : SuccinctAggregateProof)
      (fs : List UInt8) (view : SuccinctExtractionView),
      verifySuccinctAggregate arith dom inst proof fs = true ∧
      StagesBound view.authPath dom.stages view.allTables proof.stages ∧
      verifyMergeTree arith dom inst 1 (.leaf proof fs) = true ∧
      ViewTreeBound dom (.leaf proof fs) (.leaf view) ∧
      checkAllActiveSigners inst.suite inst.params inst.message inst.committee
        proof.agg.bitmap (arith.decodeSigs ((view.allTables.headD []).headD [])) = true := by
  let seed := Goldilocks.ofNat 11
  let x0 := Goldilocks.ofNat 3
  let b1 := Goldilocks.ofNat 5
  let msg := "QSAG.HEM.MSG/v2".toUTF8.toList
  let root := CommRingOps.add (pow7Goldilocks x0) seed
  let bundle := buildHonestSbox7WhirBundle seed x0 b1 msg
  have hAcc : verifySuccinctAggregate (rsSbox7TraceArith seed root) rsSbox7WhirDomain
      (rsSbox7Inst seed root msg) bundle.1 bundle.2.1 = true ∧
      StagesBound bundle.2.2.authPath rsSbox7WhirDomain.stages bundle.2.2.allTables bundle.1.stages :=
    honestSbox7WhirProof_accepts seed x0 b1 msg
  refine ⟨rsSbox7TraceArith seed root, rsSbox7WhirDomain, rsSbox7Inst seed root msg,
    rsSbox7TraceArith_lawful seed root msg, bundle.1, bundle.2.1, bundle.2.2,
    hAcc.1, hAcc.2, ?_, hAcc.2, ?_⟩
  · have hNone : bundle.1.agg.childrenCommitment.isNone = true := rfl
    simp only [verifyMergeTree, hNone, hAcc.1, Bool.and_self]
  · dsimp only [rsSbox7Inst, rsSbox7TraceArith, rsSbox7TraceArithDelta, bundle,
      buildHonestSbox7WhirBundle, List.headD_cons, checkAllActiveSigners, decodeSbox7Sigs]
    rw [(isLinearBaseRs8_encodeLinearRs8 x0 b1).2]
    simp [verifyPqHashSig_sbox7_iff, root]

attribute [local semireducible] cshake256Bytes pcsMerkleHash squeezeExt4Challenge
  deriveStageQueryIndices honestSbox7RoundPoly honestSbox7RoundPolyDelta pow7Ext4 pow7Goldilocks
  sbox7Stage0Proof sbox7Stage1Proof
  buildMerkleRootByDepth buildMerklePathByDepth encodeLinearRs8
  aggregateInstanceFrame rowSumcheckTranscriptTail stagePowSeed stageQuerySeed
  Goldilocks.add Goldilocks.mul Goldilocks.sub Goldilocks.neg
  GoldilocksExt2.add GoldilocksExt2.mul GoldilocksExt2.sub GoldilocksExt2.neg
  QuarticGoldilocks.add QuarticGoldilocks.mul QuarticGoldilocks.sub QuarticGoldilocks.neg

/-- `#tooth` `strictlyIncreasing` rejects repeated query indices. -/
theorem strictlyIncreasing_rejects_repeat (x : Nat) (xs : List Nat) :
    strictlyIncreasing (x :: x :: xs) = false := by
  simp [strictlyIncreasing]

/-- `#tooth` `verifyOneWhirStage` rejects duplicate query openings. -/
theorem succinct_duplicate_query_rejected (rowChalls finalWord : List GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextInfo : Option (WhirStageDomain × List UInt8))
    (q q' : StageQueryOpening) (qs : List StageQueryOpening)
    (hEq : sp.queries = q :: q' :: qs) (hDup : q.index = q'.index) :
    verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = false := by
  unfold verifyOneWhirStage
  rw [hEq, List.map_cons, List.map_cons, hDup, strictlyIncreasing_rejects_repeat]
  simp [Bool.and_false, Bool.false_and]

/-- `#tooth` `verifyOneWhirStage` rejects forged OOD challenge `oodChallenge ≠ deriveStageOodChallenge`. -/
theorem tooth_whir_wrong_ood_challenge_rejected (rowChalls finalWord : List GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextInfo : Option (WhirStageDomain × List UInt8))
    (hBad : sp.oodChallenge ≠ deriveStageOodChallenge prior sp.stageRoot) :
    verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = false := by
  have hPairNe : sp.oodChallenges ≠ deriveStageOodChallenges prior sp.stageRoot :=
    fun hEq => hBad (congrArg Prod.fst hEq)
  unfold verifyOneWhirStage
  simp [decide_eq_false hPairNe]

/-- `#tooth` `verifyOneWhirStage` rejects a forged second OOD challenge
    `oodChallenge2 ≠ (deriveStageOodChallenges prior sp.stageRoot).2` (`OOD_SAMPLES = 2`). -/
theorem tooth_whir_wrong_second_ood_challenge_rejected (rowChalls finalWord : List GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextInfo : Option (WhirStageDomain × List UInt8))
    (hBad : sp.oodChallenge2 ≠ (deriveStageOodChallenges prior sp.stageRoot).2) :
    verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = false := by
  have hPairNe : sp.oodChallenges ≠ deriveStageOodChallenges prior sp.stageRoot :=
    fun hEq => hBad (congrArg Prod.snd hEq)
  unfold verifyOneWhirStage
  simp [decide_eq_false hPairNe]

/-- `#tooth` Both `OOD_SAMPLES = 2` evaluations are injectively framed into `stagePostOodTranscript`:
    mutating `oodEvals.2` strictly changes `stagePostOodTranscript`. -/
theorem tooth_whir_second_ood_eval_mutates_shift_transcript (prior : List UInt8)
    (sp : WhirStageProof) (e2' : GoldilocksExt4) (hNe : sp.oodEvals.2 ≠ e2') :
    stagePostOodTranscript prior sp ≠
      stagePostOodTranscript prior { sp with oodEvals := (sp.oodEvals.1, e2') } := by
  intro hEq
  have hFrames := encodeMultiFrame_injective hEq
  have hTail1 := (List.cons.inj hFrames).2
  have hTail2 := (List.cons.inj hTail1).2
  have hTail3 := (List.cons.inj hTail2).2
  have hEncEq := (List.cons.inj hTail3).1
  exact hNe (GoldilocksExt4.encodeBytes32_injective hEncEq)

/-- `#tooth` `verifyOneWhirStage` rejects invalid Proof-of-Work nonces. -/
theorem tooth_whir_bad_pow_rejected (rowChalls finalWord : List GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextInfo : Option (WhirStageDomain × List UInt8))
    (hBad : verifyWhirStagePow
      (stagePowDigest (stagePowSeed prior sp (nextInfo.map Prod.snd) finalWord))
      sp.powNonce sdom.powBits = false) :
    verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = false := by
  unfold verifyOneWhirStage
  dsimp only
  rw [hBad]
  simp [Bool.and_false, Bool.false_and]

/-- `#tooth` `verifyOneWhirStage` rejects degree-3+ per-stage shift polynomials. -/
theorem tooth_whir_shift_degree3_rejected (rowChalls finalWord : List GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextInfo : Option (WhirStageDomain × List UInt8))
    (p : List GoldilocksExt4) (ps : List (List GoldilocksExt4))
    (α : GoldilocksExt4) (αs : List GoldilocksExt4)
    (hp : sp.shiftPolys = p :: ps) (hc : sp.shiftChallenges = α :: αs) (hDeg : 3 < p.length) :
    verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = false := by
  unfold verifyOneWhirStage
  dsimp only
  rw [hp, hc, shift_sumcheck_degree3_rejected _ _ p ps α αs hDeg]
  simp [Bool.and_false, Bool.false_and]

/-- `#tooth` `verifySuccinctAggregate` rejects degree-9+ row-sumcheck polynomials. -/
theorem succinct_degree9_round_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (p : List GoldilocksExt4) (ps : List (List GoldilocksExt4))
    (r : GoldilocksExt4) (rs : List GoldilocksExt4)
    (hp : proof.agg.roundPolys = p :: ps) (hc : proof.agg.challenges = r :: rs)
    (hDeg : 9 < p.length) :
    verifySuccinctAggregate arith dom inst proof fs = false := by
  unfold verifySuccinctAggregate
  cases proof.stages with
  | nil => rfl
  | cons sp0 sps =>
    have hAlg : verifyAggregateAlgebra inst.committee proof.agg = false := by
      unfold verifyAggregateAlgebra
      rw [hp, hc, sumcheck_degree9_rejected _ _ p ps r rs hDeg, Bool.and_false]
    simp [hAlg]

/-- `#tooth` `verifySuccinctAggregate` rejects mismatched `WhirSecurityRegime`. -/
theorem tooth_whir_wrong_regime_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hNe : proof.agg.regime ≠ inst.regime) :
    verifySuccinctAggregate arith dom inst proof fs = false := by
  unfold verifySuccinctAggregate
  cases proof.stages with
  | nil => rfl
  | cons _ _ => simp [decide_eq_false hNe]

/-- `#tooth` `verifySuccinctAggregate` rejects uncommitted Stage-0 Merkle root. -/
theorem tooth_whir_uncommitted_stage0_root_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (sp0 : WhirStageProof) (sps : List WhirStageProof)
    (hSt : proof.stages = sp0 :: sps)
    (hNe : sp0.stageRoot ≠ proof.agg.traceCommitment) :
    verifySuccinctAggregate arith dom inst proof fs = false := by
  unfold verifySuccinctAggregate
  rw [hSt]
  simp [decide_eq_false hNe]

/-- `#tooth` `verifyStageTrajectory` rejects final-stage fold mismatch against `finalWord`. -/
theorem trajectory_wrong_final_fold_rejected (sdom : WhirStageDomain)
    (finalWord : List GoldilocksExt4) (layer groups idx : Nat)
    (expected : Option GoldilocksExt4) (root : List UInt8) (α : GoldilocksExt4)
    (op : FoldLayerOpening)
    (hMismatch : finalWord[idx % groups]? ≠
      some (foldDuetExt4 op.v0 op.v1 (sdom.invTwoY0 layer (idx % groups)) sdom.invTwo α)) :
    verifyStageTrajectory sdom none finalWord none layer groups idx expected [root] [α] [op] =
      false := by
  simp [verifyStageTrajectory, verifyStageTerminalTarget, finalValueOk, decide_eq_false hMismatch]

/-- `#tooth` `verifyStageTrajectory` rejects intermediate-stage fold mismatch across stage bridge. -/
theorem trajectory_wrong_intermediate_fold_rejected (sdom nextDom : WhirStageDomain)
    (nextRoot : List UInt8) (finalWord : List GoldilocksExt4) (br : FoldLayerOpening)
    (layer groups idx : Nat) (expected : Option GoldilocksExt4)
    (root : List UInt8) (α : GoldilocksExt4) (op : FoldLayerOpening)
    (hMismatch : (if (idx % groups) / nextDom.groups0 = 0 then br.v0 else br.v1) ≠
      foldDuetExt4 op.v0 op.v1 (sdom.invTwoY0 layer (idx % groups)) sdom.invTwo α) :
    verifyStageTrajectory sdom (some (nextDom, nextRoot)) finalWord (some br)
      layer groups idx expected [root] [α] [op] = false := by
  simp only [verifyStageTrajectory, verifyStageTerminalTarget, expectedSlotOk,
    decide_eq_false hMismatch, Bool.and_false, Bool.false_and]

/-- `#tooth` `verifySuccinctAggregate` rejects wrong Fiat–Shamir transcript frame. -/
theorem aggregate_wrong_instance_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hNe : fs ≠ aggregateInstanceFrame inst proof.agg) :
    verifySuccinctAggregate arith dom inst proof fs = false := by
  unfold verifySuccinctAggregate
  cases proof.stages with
  | nil => rfl
  | cons _ _ => simp [decide_eq_false hNe]

/-- `#tooth` `verifySuccinctAggregate` rejects message substitution on the same transcript. -/
theorem aggregate_message_substitution_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst1 inst2 : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hMsg : inst1.message ≠ inst2.message)
    (hAcc1 : verifySuccinctAggregate arith dom inst1 proof fs = true) :
    verifySuccinctAggregate arith dom inst2 proof fs = false := by
  have hFs1 := (succinct_acceptance_facts arith dom inst1 proof fs hAcc1).1
  refine aggregate_wrong_instance_rejected arith dom inst2 proof fs (fun hFs2 => hMsg ?_)
  exact aggregate_frame_message_binding inst1 inst2 proof.agg proof.agg (hFs1.symm.trans hFs2)

/-- `#tooth` `verifySuccinctAggregate` rejects mismatched `TweakableHashSuite.suiteId`. -/
theorem tooth_whir_wrong_suite_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hNe : proof.agg.suite.suiteId ≠ inst.suite.suiteId) :
    verifySuccinctAggregate arith dom inst proof fs = false := by
  unfold verifySuccinctAggregate
  cases proof.stages with
  | nil => rfl
  | cons _ _ => simp [decide_eq_false hNe]

/-- `#tooth` `verifySuccinctAggregate` rejects mismatched `PqHashParams` header. -/
theorem tooth_whir_wrong_params_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hNe : proof.agg.params ≠ inst.params) :
    verifySuccinctAggregate arith dom inst proof fs = false := by
  unfold verifySuccinctAggregate
  cases proof.stages with
  | nil => rfl
  | cons _ _ => simp [decide_eq_false hNe]

/-- `#tooth` `verifySuccinctAggregate` rejects committee substitution on the same transcript. -/
theorem aggregate_committee_substitution_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst1 inst2 : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hComm : inst1.committee ≠ inst2.committee)
    (hAcc1 : verifySuccinctAggregate arith dom inst1 proof fs = true) :
    verifySuccinctAggregate arith dom inst2 proof fs = false := by
  have hFs1 := (succinct_acceptance_facts arith dom inst1 proof fs hAcc1).1
  refine aggregate_wrong_instance_rejected arith dom inst2 proof fs (fun hFs2 => hComm ?_)
  exact (aggregateInstanceFrame_injective inst1 inst2 proof.agg proof.agg
    (hFs1.symm.trans hFs2)).2.2.2.2.1

/-- `#tooth` `verifySuccinctAggregate` rejects parameter substitution on the same transcript. -/
theorem aggregate_params_substitution_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst1 inst2 : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hPar : inst1.params ≠ inst2.params)
    (hAcc1 : verifySuccinctAggregate arith dom inst1 proof fs = true) :
    verifySuccinctAggregate arith dom inst2 proof fs = false := by
  have hFs1 := (succinct_acceptance_facts arith dom inst1 proof fs hAcc1).1
  refine aggregate_wrong_instance_rejected arith dom inst2 proof fs (fun hFs2 => hPar ?_)
  exact (aggregateInstanceFrame_injective inst1 inst2 proof.agg proof.agg
    (hFs1.symm.trans hFs2)).2.2.2.2.2.1

/-! ## 14. Multi-round algebraic S-box traces

Each round commits an eight-symbol Reed–Solomon word whose two coefficients are the input
and output states. The degree-seven constraint and adjacent-state equality are checked for
EVERY round; the final state is bound to the public root. Nine rounds is a specialization,
not a truncation to the first transition. This scalar algebraic trace is not the deployed
256-column StepOp machine or a proof of Poseidon2's linear layers.
-/

def evalSbox7Rounds : List Goldilocks → Goldilocks → Goldilocks
  | [], x => x
  | seed :: seeds, x => evalSbox7Rounds seeds (CommRingOps.add (pow7Goldilocks x) seed)

/-- Decode both boundary states from the committed polynomial, not an external witness. -/
def sbox7TraceStates (word : List GoldilocksExt4) : Goldilocks × Goldilocks :=
  let c := recoverLinearCoeffs8 word
  (c.1.c0.c0, c.2.c0.c0)

def checkSbox7Trace : List Goldilocks → Goldilocks → Goldilocks →
    List (List GoldilocksExt4) → Bool
  | [], x, root, [] => decide (x = root)
  | seed :: seeds, x, root, word :: words =>
    let states := sbox7TraceStates word
    isLinearBaseRs8 word && decide (states.1 = x) &&
      decide (states.2 = CommRingOps.add (pow7Goldilocks states.1) seed) &&
      checkSbox7Trace seeds states.2 root words
  | _, _, _, _ => false

/-- All rounds, all RS symbols, all links and the terminal root are constrained. -/
theorem checkSbox7Trace_sound (seeds : List Goldilocks) (x root : Goldilocks)
    (words : List (List GoldilocksExt4))
    (h : checkSbox7Trace seeds x root words = true) :
    words.length = seeds.length ∧ evalSbox7Rounds seeds x = root := by
  induction seeds generalizing x words with
  | nil =>
    cases words with
    | nil => exact ⟨rfl, of_decide_eq_true h⟩
    | cons w ws => simp [checkSbox7Trace] at h
  | cons seed seeds ih =>
    cases words with
    | nil => simp [checkSbox7Trace] at h
    | cons word words =>
      simp only [checkSbox7Trace, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨_, hx⟩, hy⟩, ht⟩ := h
      obtain ⟨hlen, hout⟩ := ih _ words ht
      refine ⟨congrArg Nat.succ hlen, ?_⟩
      simpa only [evalSbox7Rounds, hy, hx] using hout

def buildSbox7Trace : List Goldilocks → Goldilocks → List (List GoldilocksExt4)
  | [], _ => []
  | seed :: seeds, x =>
    let y := CommRingOps.add (pow7Goldilocks x) seed
    encodeLinearRs8 x y :: buildSbox7Trace seeds y

theorem sbox7TraceStates_encode (x y : Goldilocks) :
    sbox7TraceStates (encodeLinearRs8 x y) = (x, y) := by
  unfold sbox7TraceStates
  rw [(isLinearBaseRs8_encodeLinearRs8 x y).2]
  rfl

/-- Constructive completeness for arbitrary input, constants and number of rounds. -/
theorem checkSbox7Trace_complete (seeds : List Goldilocks) (x : Goldilocks) :
    checkSbox7Trace seeds x (evalSbox7Rounds seeds x) (buildSbox7Trace seeds x) = true := by
  induction seeds generalizing x with
  | nil => simp [buildSbox7Trace, checkSbox7Trace, evalSbox7Rounds]
  | cons seed seeds ih =>
    simp only [buildSbox7Trace, checkSbox7Trace, evalSbox7Rounds,
      sbox7TraceStates_encode, (isLinearBaseRs8_encodeLinearRs8 _ _).1,
      decide_true, Bool.true_and]
    exact ih _

/-- Nine algebraic rounds: rejects both missing/extra words and a substituted final root. -/
def checkNineRoundSbox7Trace (seeds : List Goldilocks) (x root : Goldilocks)
    (words : List (List GoldilocksExt4)) : Bool :=
  decide (seeds.length = 9) && checkSbox7Trace seeds x root words

theorem nineRoundSbox7Trace_sound (seeds : List Goldilocks) (x root : Goldilocks)
    (words : List (List GoldilocksExt4))
    (h : checkNineRoundSbox7Trace seeds x root words = true) :
    seeds.length = 9 ∧ words.length = 9 ∧ evalSbox7Rounds seeds x = root := by
  obtain ⟨hn, ht⟩ := Bool.and_eq_true_iff.mp h
  have hn := of_decide_eq_true hn
  obtain ⟨hlen, hout⟩ := checkSbox7Trace_sound seeds x root words ht
  exact ⟨hn, hlen.trans hn, hout⟩

theorem nineRoundSbox7Trace_complete (seeds : List Goldilocks) (x : Goldilocks)
    (hn : seeds.length = 9) :
    checkNineRoundSbox7Trace seeds x (evalSbox7Rounds seeds x)
      (buildSbox7Trace seeds x) = true := by
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hn, checkSbox7Trace_complete seeds x⟩

theorem sbox7Trace_wrong_root_rejected (seeds : List Goldilocks) (x root : Goldilocks)
    (words : List (List GoldilocksExt4)) (hroot : evalSbox7Rounds seeds x ≠ root) :
    checkSbox7Trace seeds x root words = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact hroot (checkSbox7Trace_sound seeds x root words h).2

/-- The same decoded transition also verifies under the algebraic signature suite used by
`rsSbox7TraceArith_lawful`; this connects trace constraints to its signature relation. -/
theorem sbox7Trace_head_signature (seed : Goldilocks) (seeds : List Goldilocks)
    (x root : Goldilocks) (word : List GoldilocksExt4) (words : List (List GoldilocksExt4))
    (msg : List UInt8) (h : checkSbox7Trace (seed :: seeds) x root (word :: words) = true) :
    verifyPqHashSig sbox7FieldSuite sbox7Params
      (mkSbox7Pk seed (sbox7TraceStates word).2) msg (mkSbox7Sig x) = true := by
  simp only [checkSbox7Trace, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hx⟩, hy⟩, _⟩ := h
  rw [verifyPqHashSig_sbox7_iff]
  exact decide_eq_true (by simpa only [hx] using hy.symm)

/-! ### Composition through the succinct extractor

A chain carries a separate, instance-bound WHIR proof for each nonlinear round. Its extraction
views bind the recovered input to the preceding public output. This is a composition theorem
for arbitrarily many proofs (nine included), not a claim that one two-stage proof represents
nine S-box rounds, nor a deployed StepOp AIR completeness result.
-/

structure Sbox7WhirRound where
  seed : Goldilocks
  root : Goldilocks
  proof : SuccinctAggregateProof
  fs : List UInt8
  view : SuccinctExtractionView

def Sbox7WhirRoundBreak (r : Sbox7WhirRound) : Prop :=
  Nonempty (SumcheckSchwartzZippelHit 8 r.proof.agg.roundPolys
    (adaptivePolys ((rsSbox7TraceArith r.seed r.root).honestRound
      ((r.view.allTables.headD []).headD [])) r.proof.agg.challenges)
    r.proof.agg.challenges) ∨
  Nonempty (HashCollisionWitness pcsMerkleHash) ∨
  Nonempty (WhirStageQueryMiss r.proof.finalWord rsSbox7WhirDomain r.view.allTables r.proof) ∨
  Nonempty (WhirProximityHit (rsSbox7TraceArith r.seed r.root) rsSbox7WhirDomain
    r.proof.finalWord r.view.allTables r.proof)

/-- Every proof is accepted and every extraction input is linked. No soundness conclusion is
assumed: false rounds are exposed by the extractor as concrete break witnesses. -/
def Sbox7WhirChainAccepted (msg : List UInt8) :
    Goldilocks → Goldilocks → List Sbox7WhirRound → Prop
  | x, root, [] => x = root
  | x, root, r :: rs =>
    verifySuccinctAggregate (rsSbox7TraceArith r.seed r.root) rsSbox7WhirDomain
      (rsSbox7Inst r.seed r.root msg) r.proof r.fs = true ∧
    StagesBound r.view.authPath rsSbox7WhirDomain.stages r.view.allTables r.proof.stages ∧
    r.proof.agg.bitmap = [true] ∧
    (recoverLinearCoeffs8 ((r.view.allTables.headD []).headD [])).1.c0.c0 = x ∧
    Sbox7WhirChainAccepted msg r.root root rs

/-- Full multi-round WHIR composition: correct iterated S-box evaluation, or an identified
round with a sumcheck, Merkle, query-miss or proximity break. -/
theorem sbox7WhirChain_sound (msg : List UInt8) (x root : Goldilocks)
    (rounds : List Sbox7WhirRound) (h : Sbox7WhirChainAccepted msg x root rounds) :
    evalSbox7Rounds (rounds.map (·.seed)) x = root ∨
      ∃ r ∈ rounds, Sbox7WhirRoundBreak r := by
  induction rounds generalizing x with
  | nil => exact Or.inl h
  | cons r rs ih =>
    obtain ⟨ha, hb, hbitmap, hx, ht⟩ := h
    have hs := succinct_aggregation_knowledge_soundness_thm
      (rsSbox7TraceArith r.seed r.root) rsSbox7WhirDomain (rsSbox7Inst r.seed r.root msg)
      (rsSbox7TraceArith_lawful r.seed r.root msg) r.proof r.fs r.view ha hb
    change _ ∨ Sbox7WhirRoundBreak r at hs
    rcases hs with hv | hbad
    · simp only [rsSbox7Inst, rsSbox7TraceArith, rsSbox7TraceArithDelta,
        decodeSbox7Sigs, hbitmap, checkAllActiveSigners, Bool.and_true,
        ↓reduceIte, verifyPqHashSig_sbox7_iff, decide_eq_true_eq, hx] at hv
      rcases ih r.root ht with hout | htail
      · exact Or.inl (by simpa only [List.map_cons, evalSbox7Rounds, hv] using hout)
      · obtain ⟨bad, hmem, hbad⟩ := htail
        exact Or.inr ⟨bad, List.mem_cons_of_mem r hmem, hbad⟩
    · exact Or.inr ⟨r, List.mem_cons_self, hbad⟩

def buildSbox7WhirChain (msg : List UInt8) : List Goldilocks → Goldilocks → List Sbox7WhirRound
  | [], _ => []
  | seed :: seeds, x =>
    let y := CommRingOps.add (pow7Goldilocks x) seed
    let bundle := buildHonestSbox7WhirBundle seed x y msg
    { seed := seed, root := y, proof := bundle.1, fs := bundle.2.1, view := bundle.2.2 } ::
      buildSbox7WhirChain msg seeds y

/-- Inhabited multi-round acceptance for arbitrary round constants and initial state. -/
theorem sbox7WhirChain_complete (msg : List UInt8) (seeds : List Goldilocks) (x : Goldilocks) :
    Sbox7WhirChainAccepted msg x (evalSbox7Rounds seeds x) (buildSbox7WhirChain msg seeds x) := by
  induction seeds generalizing x with
  | nil => rfl
  | cons seed seeds ih =>
    have h := honestSbox7WhirProof_accepts seed x (CommRingOps.add (pow7Goldilocks x) seed) msg
    refine ⟨h.1, h.2, rfl, ?_, ih _⟩
    change (recoverLinearCoeffs8 (encodeLinearRs8 x _)).1.c0.c0 = x
    rw [(isLinearBaseRs8_encodeLinearRs8 x _).2]
    rfl

theorem buildSbox7WhirChain_seeds (msg : List UInt8) (seeds : List Goldilocks) (x : Goldilocks) :
    (buildSbox7WhirChain msg seeds x).map (·.seed) = seeds := by
  induction seeds generalizing x with
  | nil => rfl
  | cons seed seeds ih =>
    change seed :: (buildSbox7WhirChain msg seeds _).map (·.seed) = seed :: seeds
    rw [ih]

/-- Exactly nine accepted nonlinear rounds, with the same concrete break alternatives. -/
theorem nineRoundSbox7Whir_sound (msg : List UInt8) (x root : Goldilocks)
    (rounds : List Sbox7WhirRound) (hn : rounds.length = 9)
    (h : Sbox7WhirChainAccepted msg x root rounds) :
    (rounds.map (·.seed)).length = 9 ∧
      (evalSbox7Rounds (rounds.map (·.seed)) x = root ∨
        ∃ r ∈ rounds, Sbox7WhirRoundBreak r) :=
  ⟨(List.length_map ..).trans hn, sbox7WhirChain_sound msg x root rounds h⟩

/-! ### Exports for lane agg-recursive -/

theorem bitmapPopcountSpec_nil : bitmapPopcountSpec [] = 0 := by rfl

theorem bitmapPopcountSpec_cons (b : Bool) (bs : SignerBitmapSpec) :
    bitmapPopcountSpec (b :: bs) = (if b then 1 else 0) + bitmapPopcountSpec bs := by rfl

theorem checkAllActiveSigners_nil_nil (suite : TweakableHashSuite) (params : PqHashParams)
    (msg : List UInt8) (sigs : List PqHashSig) :
    checkAllActiveSigners suite params msg [] [] sigs = true := by rfl

theorem checkAllActiveSigners_cons_cons_cons (suite : TweakableHashSuite) (params : PqHashParams)
    (msg : List UInt8) (pk : PqPublicKey) (pks : List PqPublicKey) (active : Bool)
    (bs : SignerBitmapSpec) (sig : PqHashSig) (sigs : List PqHashSig) :
    checkAllActiveSigners suite params msg (pk :: pks) (active :: bs) (sig :: sigs) =
      ((if active then verifyPqHashSig suite params pk msg sig else true) &&
        checkAllActiveSigners suite params msg pks bs sigs) := by rfl

theorem checkAllActiveSigners_nil_cons (suite : TweakableHashSuite) (params : PqHashParams)
    (msg : List UInt8) (active : Bool) (bs : SignerBitmapSpec) (sigs : List PqHashSig) :
    checkAllActiveSigners suite params msg [] (active :: bs) sigs = false := by rfl

theorem checkAllActiveSigners_cons_nil (suite : TweakableHashSuite) (params : PqHashParams)
    (msg : List UInt8) (pk : PqPublicKey) (pks : List PqPublicKey) (sigs : List PqHashSig) :
    checkAllActiveSigners suite params msg (pk :: pks) [] sigs = false := by rfl

theorem checkAllActiveSigners_cons_cons_nil (suite : TweakableHashSuite) (params : PqHashParams)
    (msg : List UInt8) (pk : PqPublicKey) (pks : List PqPublicKey) (active : Bool)
    (bs : SignerBitmapSpec) :
    checkAllActiveSigners suite params msg (pk :: pks) (active :: bs) [] = false := by rfl

theorem stageLayersBound_nil_nil (authPath : Nat → Nat → Nat → List (List UInt8))
    (stageIdx layer groups : Nat) :
    StageLayersBound authPath stageIdx layer groups [] [] := trivial

theorem stageLayersBound_cons_cons_iff (authPath : Nat → Nat → Nat → List (List UInt8))
    (stageIdx layer groups : Nat) (w : List GoldilocksExt4) (ws : List (List GoldilocksExt4))
    (root : List UInt8) (roots : List (List UInt8)) :
    StageLayersBound authPath stageIdx layer groups (w :: ws) (root :: roots) ↔
      ((∀ g, g < groups →
        merklePathRoot pcsMerkleHash
          (pcsMerkleHash (duetLeafFrame stageIdx layer g (w.getD g CommRingOps.zero)
            (w.getD (g + groups) CommRingOps.zero))) g (authPath stageIdx layer g) = root ∧
        (authPath stageIdx layer g).length = merkleDepth groups) ∧
      StageLayersBound authPath stageIdx (layer + 1) (groups / 2) ws roots) := Iff.rfl

theorem not_stageLayersBound_nil_cons (authPath : Nat → Nat → Nat → List (List UInt8))
    (stageIdx layer groups : Nat) (root : List UInt8) (roots : List (List UInt8)) :
    ¬ StageLayersBound authPath stageIdx layer groups [] (root :: roots) := fun h => h

theorem not_stageLayersBound_cons_nil (authPath : Nat → Nat → Nat → List (List UInt8))
    (stageIdx layer groups : Nat) (w : List GoldilocksExt4) (ws : List (List GoldilocksExt4)) :
    ¬ StageLayersBound authPath stageIdx layer groups (w :: ws) [] := fun h => h

theorem stagesBound_nil_nil_nil (authPath : Nat → Nat → Nat → List (List UInt8)) :
    StagesBound authPath [] [] [] := trivial

theorem stagesBound_cons_cons_cons_iff (authPath : Nat → Nat → Nat → List (List UInt8))
    (sdom : WhirStageDomain) (sdoms : List WhirStageDomain)
    (stTables : List (List GoldilocksExt4)) (restTables : List (List (List GoldilocksExt4)))
    (sp : WhirStageProof) (sps : List WhirStageProof) :
    StagesBound authPath (sdom :: sdoms) (stTables :: restTables) (sp :: sps) ↔
      (stTables ≠ [] ∧
        StageLayersBound authPath sdom.stageIdx 0 sdom.groups0 stTables (stageAllRoots sp) ∧
        StagesBound authPath sdoms restTables sps) := Iff.rfl

/-- An accepted WHIR stage carries exactly `sdom.foldLayers` layer roots. -/
theorem verifyOneWhirStage_stageAllRoots_length {rowChallenges finalWord : List GoldilocksExt4}
    {prior : List UInt8} {sdom : WhirStageDomain} {sp : WhirStageProof}
    {nextStageInfo : Option (WhirStageDomain × List UInt8)}
    (h : verifyOneWhirStage rowChallenges finalWord prior sdom sp nextStageInfo = true) :
    (stageAllRoots sp).length = sdom.foldLayers := by
  unfold verifyOneWhirStage at h
  dsimp only at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨_, hRoots⟩
  exact of_decide_eq_true hRoots

theorem verifyWhirStages_singleton (rowChallenges finalWord : List GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof) :
    verifyWhirStages rowChallenges finalWord prior [sdom] [sp] =
      verifyOneWhirStage rowChallenges finalWord prior sdom sp none := by rfl

theorem verifyWhirStages_cons_cons (rowChallenges finalWord : List GoldilocksExt4)
    (prior : List UInt8) (sdom nextDom : WhirStageDomain) (restDoms : List WhirStageDomain)
    (sp nextSp : WhirStageProof) (restProofs : List WhirStageProof) :
    verifyWhirStages rowChallenges finalWord prior (sdom :: nextDom :: restDoms)
        (sp :: nextSp :: restProofs) =
      (verifyOneWhirStage rowChallenges finalWord prior sdom sp
          (some (nextDom, nextSp.stageRoot)) &&
        verifyWhirStages rowChallenges finalWord
          (stageQuerySeed (stagePowSeed prior sp (some nextSp.stageRoot) finalWord) sp.powNonce)
          (nextDom :: restDoms) (nextSp :: restProofs)) := by rfl

/-- `verifyWhirStages` accepts only stage lists of one common length. -/
theorem verifyWhirStages_accept_length_eq (rowChallenges finalWord : List GoldilocksExt4) :
    ∀ (prior : List UInt8) (sdoms : List WhirStageDomain) (sps : List WhirStageProof),
      verifyWhirStages rowChallenges finalWord prior sdoms sps = true → sdoms.length = sps.length
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => absurd h Bool.false_ne_true
  | _, [_], [], h => absurd h Bool.false_ne_true
  | _, _ :: _ :: _, [], h => absurd h Bool.false_ne_true
  | _, [_], [_], _ => rfl
  | _, [_], _ :: _ :: _, h => absurd h Bool.false_ne_true
  | _, _ :: _ :: _, [_], h => absurd h Bool.false_ne_true
  | prior, sdom :: nextDom :: restDoms, sp :: nextSp :: restProofs, h => by
    rw [verifyWhirStages_cons_cons] at h
    exact congrArg Nat.succ (verifyWhirStages_accept_length_eq rowChallenges finalWord _
      (nextDom :: restDoms) (nextSp :: restProofs) (Bool.and_eq_true_iff.mp h).2)

end Aggregation

end Qsag
end


public section
#export_eqns Qsag.Aggregation.foldDuetExt4
end

public section
namespace Qsag.Aggregation
/-- Disabling PoW does not admit an unbound prover nonce. -/
theorem verifyWhirStagePow_zero_iff (chal : List UInt8) (nonce : Nat) :
    verifyWhirStagePow chal nonce 0 = true ↔ nonce = 0 := by
  simp [verifyWhirStagePow]
#export_eqns whirStagePowMask
end Qsag.Aggregation
end
