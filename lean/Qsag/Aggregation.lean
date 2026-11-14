module
/-
# Aggregation algebra and transparent reference verification

The bitmap, polynomial root-count and coset-duet results are unconditional algebraic results.
`verifyAggregateAlgebra` alone accepts signature-free zero certificates; its explicit regression
records that limitation. `verifyAggregatedSignature` additionally checks opened signatures, the
public instance, trace commitment and an interleaved reference Fiat–Shamir schedule. Its extractor
requires no honest-trace soundness premise, but is linear-size and is not the production succinct PCS.

The older `extractAggregateWitnessOrBreak` and `qsag_aggregate_unforgeability_reduction` remain
conditional on `hHonestSound` and on the hypertree extractor's oracle hypotheses. They are not
knowledge-soundness proofs for the production aggregation implementation.

Sections 5-13 add the production parameter record, counting bounds for the degree-8 sumcheck
(adaptive union bound over challenge vectors) and for distinct BaseFold queries, and
`verifySuccinctAggregate`, a succinct verifier model with Merkle-opened query trajectories.
`succinct_aggregation_knowledge_soundness` is relative to a `RowArithmetization.Lawful` instance
(none is built for the production AIR) and has two query-phase outcomes whose probability is
not bounded here: `FoldProximityHit`, and `BaseFoldQueryMiss` when the inconsistent set is
sparse. The counts are over uniformly drawn challenges and query tuples; the Fiat–Shamir
transformation is not analysed in the random-oracle model.
-/

public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.Keccak
public import Qsag.HashSigs
public import Qsag.HypertreeEufCma
public import Qsag.MaliciousSecurity

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. `SignerBitmap` Disjointness & Exact Stake-Popcount Conservation -/

/-- Boolean participation vector across a committee of $N$ validators (`Simulates` `BitVec N`). -/
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
    blocking 2-to-1 recursive aggregation from double-counting validator weight! -/
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
    matches `Digest5` in `crates/qsag-agg/src/trace.rs` where every limb $< 2^{56} < p$. -/
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
    Distinct 256-bit roots or message digests NEVER collide in `Digest5` (eliminating the 32-bit
    truncation weakness of 4×56-bit limbs). -/
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

/-! ## 3. Interleaved `BaseFold` + Sumcheck Soundness (`[P0-01]`) & `#tooth` Attacks -/

/-- Exact 2-step multilinear quartet folding operator over `GoldilocksExt2` matching `fold_table_4`
    in `crates/qsag-agg/src/pcs.rs`:
    `fold4(q0, q1, q2, q3; ra, rb) = (q0 + ra*(q1 - q0)) + rb*((q2 + ra*(q3 - q2)) - (q0 + ra*(q1 - q0)))`. -/
@[expose] def basefoldQuartet (q0 q1 q2 q3 ra rb : GoldilocksExt2) : GoldilocksExt2 :=
  let lo := CommRingOps.add q0 (CommRingOps.mul ra (CommRingOps.sub q1 q0))
  let hi := CommRingOps.add q2 (CommRingOps.mul ra (CommRingOps.sub q3 q2))
  CommRingOps.add lo (CommRingOps.mul rb (CommRingOps.sub hi lo))

/-- **`#tooth` Pre-Challenge `BaseFold` Forgery Attack (`prechallenge_fold_forgery_attack`, `[P0-01]`)**:
    If a broken Fiat–Shamir schedule squeezes folding challenges `(ra, rb)` (`ra ≠ 0, rb ≠ 0`)
    **before** committing the quartet `(q0, q1, q2, q3)`, a malicious prover can choose `q3*` to hit
    **ANY** arbitrary forged value `vStar : GoldilocksExt2` identically!
    (This is the exact algebra behind `[P0-01]` that collapsed soundness from $2^{-128}$ to $(3/4)^{64}$
    before we interleaved `comm_k` absorption strictly prior to squeezing `(ra, rb)`!) -/
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
  change CommRingOps.add lo (CommRingOps.mul rb (CommRingOps.sub (CommRingOps.add q2 (CommRingOps.mul ra (CommRingOps.sub q3Star q2))) lo)) = vStar
  rw [hHi]
  dsimp only [targetHi]
  rw [hSubAdd, ← LawfulCommRing.mul_assoc, GoldilocksExt2.mul_inv_cancel hrb,
      LawfulCommRing.one_mul, hAddSub]

/-- **Interleaved Commitment-Before-Challenge Quartet Soundness (`basefold_committed_quartet_roots_le_one`)**:
    Once `(q0, q1, q2, q3)` and `nextVal` are committed **before** squeezing `rb` (for fixed `ra`),
    `basefoldQuartet q0 q1 q2 q3 ra rb - nextVal` is a degree-$\le 1$ polynomial in `rb`, so if it is
    non-trivial at ANY evaluation point `rb₀`, at most **1** challenge `rb ∈ S` in any `Nodup` domain `S`
    passes (`1 / |\mathbb{F}_{p^2}| \approx 2^{-128}`)! -/
theorem basefold_committed_quartet_roots_le_one
    (q0 q1 q2 q3 ra nextVal : GoldilocksExt2) (S : List GoldilocksExt2)
    (hNodup : S.Nodup)
    (hCheat : ∃ rb₀ : GoldilocksExt2, basefoldQuartet q0 q1 q2 q3 ra rb₀ ≠ nextVal) :
    (S.filter (fun rb => decide (basefoldQuartet q0 q1 q2 q3 ra rb = nextVal))).length ≤ 1 := by
  let lo := CommRingOps.add q0 (CommRingOps.mul ra (CommRingOps.sub q1 q0))
  let hi := CommRingOps.add q2 (CommRingOps.mul ra (CommRingOps.sub q3 q2))
  let cs : List GoldilocksExt2 := [CommRingOps.sub lo nextVal, CommRingOps.sub hi lo]
  have hEvEq : ∀ rb : GoldilocksExt2,
      RoundPoly.evalCoeffs cs rb = CommRingOps.sub (basefoldQuartet q0 q1 q2 q3 ra rb) nextVal := by
    intro rb
    dsimp only [cs, RoundPoly.evalCoeffs]
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    change CommRingOps.add (CommRingOps.sub lo nextVal) (CommRingOps.mul rb (CommRingOps.sub hi lo)) =
      CommRingOps.sub (CommRingOps.add lo (CommRingOps.mul rb (CommRingOps.sub hi lo))) nextVal
    rw [LawfulCommRing.sub_eq_add_neg lo nextVal,
        LawfulCommRing.sub_eq_add_neg (CommRingOps.add lo (CommRingOps.mul rb (CommRingOps.sub hi lo))) nextVal,
        LawfulCommRing.add_assoc, LawfulCommRing.add_comm (CommRingOps.neg nextVal),
        ← LawfulCommRing.add_assoc]
  obtain ⟨rb₀, hNe₀⟩ := hCheat
  have hNz : ∃ x₀ : GoldilocksExt2, RoundPoly.evalCoeffs cs x₀ ≠ GoldilocksExt2.zero := by
    refine ⟨rb₀, ?_⟩
    rw [hEvEq rb₀]
    exact fun hSub => hNe₀ (LawfulCommRing.sub_eq_zero_iff.mp hSub)
  have hBound := RoundPoly.roots_nodup_length_le 1 cs S hNodup (by simp [cs]) hNz
  have hFiltEq : S.filter (fun rb => decide (basefoldQuartet q0 q1 q2 q3 ra rb = nextVal)) =
      S.filter (fun rb => decide (RoundPoly.evalCoeffs cs rb = GoldilocksExt2.zero)) := by
    congr 1
    funext rb
    rw [hEvEq rb]
    by_cases hEq : basefoldQuartet q0 q1 q2 q3 ra rb = nextVal
    · have hZ : CommRingOps.sub nextVal nextVal = GoldilocksExt2.zero :=
        LawfulCommRing.sub_self nextVal
      simp only [hEq, hZ, decide_true]
    · have hNzRb : CommRingOps.sub (basefoldQuartet q0 q1 q2 q3 ra rb) nextVal ≠ GoldilocksExt2.zero :=
        fun hZ => hEq (LawfulCommRing.sub_eq_zero_iff.mp hZ)
      simp [hEq, hNzRb]
  rw [hFiltEq]
  exact hBound

/-- Distinct polynomials of degree at most `maxDegree` agree at at most that many points. -/
theorem sumcheck_round_roots_le_degree (maxDegree : Nat)
    (claimedPoly honestPoly : List GoldilocksExt2) (S : List GoldilocksExt2)
    (hNodup : S.Nodup)
    (hLenC : claimedPoly.length ≤ maxDegree + 1) (hLenH : honestPoly.length ≤ maxDegree + 1)
    (hDiff : ∃ x₀ : GoldilocksExt2, RoundPoly.evalCoeffs claimedPoly x₀ ≠ RoundPoly.evalCoeffs honestPoly x₀) :
    (S.filter (fun r => decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r))).length ≤ maxDegree := by
  let diff := RoundPoly.subCoeffs claimedPoly honestPoly
  have hDiffLen : diff.length ≤ maxDegree + 1 := by
    dsimp only [diff]
    rw [RoundPoly.subCoeffs_length]
    exact Nat.max_le.mpr ⟨hLenC, hLenH⟩
  obtain ⟨x₀, hx₀⟩ := hDiff
  have hNz : ∃ x : GoldilocksExt2, RoundPoly.evalCoeffs diff x ≠ GoldilocksExt2.zero := by
    refine ⟨x₀, ?_⟩
    rw [RoundPoly.evalCoeffs_sub]
    exact fun hZ => hx₀ (LawfulCommRing.sub_eq_zero_iff.mp hZ)
  have hBound := RoundPoly.roots_nodup_length_le maxDegree diff S hNodup hDiffLen hNz
  have hFiltEq : S.filter (fun r => decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r)) =
      S.filter (fun r => decide (RoundPoly.evalCoeffs diff r = GoldilocksExt2.zero)) := by
    congr 1
    funext r
    dsimp only [diff]
    rw [RoundPoly.evalCoeffs_sub]
    by_cases hEq : RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r
    · have hZ : CommRingOps.sub (RoundPoly.evalCoeffs honestPoly r) (RoundPoly.evalCoeffs honestPoly r) = GoldilocksExt2.zero :=
        LawfulCommRing.sub_self _
      simp only [hEq, hZ, decide_true]
    · have hNzR : CommRingOps.sub (RoundPoly.evalCoeffs claimedPoly r) (RoundPoly.evalCoeffs honestPoly r) ≠ GoldilocksExt2.zero :=
        fun hZ => hEq (LawfulCommRing.sub_eq_zero_iff.mp hZ)
      simp [hEq, hNzR]
  rw [hFiltEq]
  exact hBound

/-- Production coset duet: the two values are at opposite points, with supplied inverse twiddles.
    Matches `pcs.rs::fold_duet_ext2`; unlike Boolean interpolation this uses both inverse factors. -/
def foldDuetExt2 (v0 v1 : GoldilocksExt2) (invTwoY0 invTwo : Goldilocks)
    (r : GoldilocksExt2) : GoldilocksExt2 :=
  let even := CommRingOps.mul (CommRingOps.add v0 v1) (GoldilocksExt2.ofBase invTwo)
  let odd := CommRingOps.mul (CommRingOps.sub v0 v1) (GoldilocksExt2.ofBase invTwoY0)
  CommRingOps.add even (CommRingOps.mul r odd)

/-- A committed coset duet is affine in its challenge, so a nonzero residual has at most one root. -/
theorem basefold_coset_duet_roots_le_one
    (v0 v1 next : GoldilocksExt2) (invTwoY0 invTwo : Goldilocks)
    (S : List GoldilocksExt2) (hS : S.Nodup)
    (hne : ∃ r, foldDuetExt2 v0 v1 invTwoY0 invTwo r ≠ next) :
    (S.filter (fun r => decide (foldDuetExt2 v0 v1 invTwoY0 invTwo r = next))).length ≤ 1 := by
  let even := CommRingOps.mul (CommRingOps.add v0 v1) (GoldilocksExt2.ofBase invTwo)
  let odd := CommRingOps.mul (CommRingOps.sub v0 v1) (GoldilocksExt2.ofBase invTwoY0)
  have he : ∀ r, RoundPoly.evalCoeffs [even, odd] r = foldDuetExt2 v0 v1 invTwoY0 invTwo r := by
    intro r
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rfl
  have hc : ∀ r, RoundPoly.evalCoeffs [next] r = next := by
    intro r
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  have hd : ∃ r, RoundPoly.evalCoeffs [even, odd] r ≠ RoundPoly.evalCoeffs [next] r := by
    simpa only [he, hc] using hne
  have bound := sumcheck_round_roots_le_degree 1 [even, odd] [next] S hS
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil]; omega) hd
  simpa only [he, hc] using bound

/-- Regression: omitting the coset inverse changes the folded value. -/
theorem coset_twiddle_omission_detected :
    foldDuetExt2 GoldilocksExt2.one GoldilocksExt2.zero
      (Goldilocks.ofNat 2) (Goldilocks.ofNat 3) GoldilocksExt2.one ≠
    foldDuetExt2 GoldilocksExt2.one GoldilocksExt2.zero
      (Goldilocks.ofNat 1) (Goldilocks.ofNat 3) GoldilocksExt2.one := by
  decide +kernel

/-- Specializations of the arbitrary-degree round bound. -/
theorem sumcheck_cubic_round_roots_le_three
    (claimedPoly honestPoly : List GoldilocksExt2) (S : List GoldilocksExt2)
    (hNodup : S.Nodup)
    (hLenC : claimedPoly.length ≤ 4) (hLenH : honestPoly.length ≤ 4)
    (hDiff : ∃ x₀ : GoldilocksExt2, RoundPoly.evalCoeffs claimedPoly x₀ ≠ RoundPoly.evalCoeffs honestPoly x₀) :
    (S.filter (fun r => decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r))).length ≤ 3 :=
  sumcheck_round_roots_le_degree 3 claimedPoly honestPoly S hNodup hLenC hLenH hDiff

theorem sumcheck_degree8_round_roots_le_eight
    (claimedPoly honestPoly : List GoldilocksExt2) (S : List GoldilocksExt2)
    (hNodup : S.Nodup)
    (hLenC : claimedPoly.length ≤ 9) (hLenH : honestPoly.length ≤ 9)
    (hDiff : ∃ x₀ : GoldilocksExt2, RoundPoly.evalCoeffs claimedPoly x₀ ≠ RoundPoly.evalCoeffs honestPoly x₀) :
    (S.filter (fun r => decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r))).length ≤ 8 :=
  sumcheck_round_roots_le_degree 8 claimedPoly honestPoly S hNodup hLenC hLenH hDiff

/-- **`#tooth` Mandatory Terminal Sumcheck Evaluation Check (`terminal_check_omission_unsound`)**:
    Omitting the terminal check `finalSumcheckClaim = pcsOpenedEval` allows a constant polynomial
    `s(X) = [halfClaim]` (`halfClaim + halfClaim = forgedClaim`) to pass `s(0) + s(1) = forgedClaim`
    for ANY `forgedClaim` with zero connection to the committed trace! -/
theorem terminal_check_omission_unsound (halfClaim : GoldilocksExt2) :
    let forgedClaim := CommRingOps.add halfClaim halfClaim
    let fakePoly : List GoldilocksExt2 := [halfClaim]
    CommRingOps.add (RoundPoly.evalCoeffs fakePoly GoldilocksExt2.zero)
                    (RoundPoly.evalCoeffs fakePoly GoldilocksExt2.one) = forgedClaim := by
  simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-! ## 4. $K$-to-$1$ Succinct Aggregation, Disjoint 2-to-1 Merge & Constructive Knowledge Extractor -/

/-- Transcript-indexed hit where two unequal degree-eight polynomials agree at the actual round challenge. -/
structure SumcheckSchwartzZippelHit
    (claimedPolys honestPolys : List (List GoldilocksExt2))
    (challenges : List GoldilocksExt2) where
  roundIdx    : Nat
  claimedPoly : List GoldilocksExt2
  honestPoly  : List GoldilocksExt2
  challenge   : GoldilocksExt2
  claimed_at : claimedPolys[roundIdx]? = some claimedPoly
  honest_at : honestPolys[roundIdx]? = some honestPoly
  challenge_at : challenges[roundIdx]? = some challenge
  lenClaimed  : claimedPoly.length ≤ 9
  lenHonest   : honestPoly.length ≤ 9
  diffPoint   : GoldilocksExt2
  polyNe      : RoundPoly.evalCoeffs claimedPoly diffPoint ≠ RoundPoly.evalCoeffs honestPoly diffPoint
  hitEq       : RoundPoly.evalCoeffs claimedPoly challenge = RoundPoly.evalCoeffs honestPoly challenge

/-- Succinct aggregated signature certificate over a `committee : List PqPublicKey` and `message`. -/
structure AggregatedSignature where
  suite           : TweakableHashSuite
  params          : PqHashParams
  bitmap          : SignerBitmapSpec
  signerCount     : Nat
  traceCommitment : List UInt8
  claimedSum      : GoldilocksExt2
  roundPolys      : List (List GoldilocksExt2)
  challenges      : List GoldilocksExt2
  terminalEval    : GoldilocksExt2
  childrenCommitment : Option (List UInt8 × List UInt8) := none

/-- Sumcheck round-by-round algebraic verifier (`s_j(0) + s_j(1) = claim_j` -> `claim_{j+1} = s_j(r_j)`,
    terminating at `claim_last = terminalEval`). -/
def verifySumcheckChain : GoldilocksExt2 → List (List GoldilocksExt2) → List GoldilocksExt2 → GoldilocksExt2 → Bool
  | curClaim, [], [], termEval => curClaim == termEval
  | curClaim, p :: ps, r :: rs, termEval =>
    (p.length ≤ 9) &&
    (CommRingOps.add (RoundPoly.evalCoeffs p GoldilocksExt2.zero)
                     (RoundPoly.evalCoeffs p GoldilocksExt2.one) == curClaim) &&
    verifySumcheckChain (RoundPoly.evalCoeffs p r) ps rs termEval
  | _, _, _, _ => false

/-- Algebra-only check. This is not a signature verifier: it does not check a committed witness. -/
@[expose] def verifyAggregateAlgebra (committee : List PqPublicKey) (agg : AggregatedSignature) : Bool :=
  (agg.bitmap.length == committee.length) &&
  (agg.signerCount == bitmapPopcountSpec agg.bitmap) &&
  (0 < agg.signerCount) &&
  (0 < agg.roundPolys.length) &&
  (agg.claimedSum == GoldilocksExt2.zero) &&
  verifySumcheckChain agg.claimedSum agg.roundPolys agg.challenges agg.terminalEval

/-- Disjoint 2-to-1 recursive folding verifier (`merge_aggregates` in `crates/qsag-agg/src/lib.rs`). -/
@[expose] def verifyDisjointMerge (committee : List PqPublicKey)
    (left right merged : AggregatedSignature) : Bool :=
  verifyAggregateAlgebra committee left &&
  verifyAggregateAlgebra committee right &&
  bitmapDisjointSpec left.bitmap right.bitmap &&
  (merged.bitmap == bitmapUnionSpec left.bitmap right.bitmap) &&
  verifyAggregateAlgebra committee merged

/-- **2-to-1 Disjoint Recursive Merge Soundness (`merge_aggregates_disjoint_sound`)**:
    Any accepted 2-to-1 merge strictly enforces disjoint bitmaps and exact additive signer count
    `merged.signerCount = left.signerCount + right.signerCount`! -/
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

private theorem verifySumcheckChain_zeroPolys :
    ∀ (challenges : List GoldilocksExt2),
      verifySumcheckChain GoldilocksExt2.zero
        (challenges.map (fun _ => [GoldilocksExt2.zero]))
        challenges GoldilocksExt2.zero = true
  | [] => by simp [verifySumcheckChain]
  | r :: rs => by
    have ih := verifySumcheckChain_zeroPolys rs
    have hEv0 : RoundPoly.evalCoeffs [GoldilocksExt2.zero] GoldilocksExt2.zero = GoldilocksExt2.zero := by
      simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    have hEv1 : RoundPoly.evalCoeffs [GoldilocksExt2.zero] GoldilocksExt2.one = GoldilocksExt2.zero := by
      simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    have hEvR : RoundPoly.evalCoeffs [GoldilocksExt2.zero] r = GoldilocksExt2.zero := by
      simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    have hAdd0 : CommRingOps.add GoldilocksExt2.zero GoldilocksExt2.zero = GoldilocksExt2.zero :=
      LawfulCommRing.add_zero GoldilocksExt2.zero
    simp [verifySumcheckChain, hEv0, hEv1, hEvR, hAdd0, ih]

/-- Legacy zero-polynomial certificate constructor. It consumes no signatures and is not a prover. -/
def buildHonestAggregate (suite : TweakableHashSuite) (params : PqHashParams)
    (_committee : List PqPublicKey) (bitmap : SignerBitmapSpec)
    (traceComm : List UInt8) (challenges : List GoldilocksExt2) :
    AggregatedSignature :=
  { suite           := suite
    params          := params
    bitmap          := bitmap
    signerCount     := bitmapPopcountSpec bitmap
    traceCommitment := traceComm
    claimedSum      := GoldilocksExt2.zero
    roundPolys      := challenges.map (fun _ => [GoldilocksExt2.zero])
    challenges      := challenges
    terminalEval    := GoldilocksExt2.zero }

/-- **Counterexample to algebra-only signature verification (`zero_certificate_passes_algebra`)**:
    For any committee, non-empty signer bitmap (`0 < bitmapPopcountSpec bitmap`), and non-empty
    challenge schedule (`0 < challenges.length`), `buildHonestAggregate` passes `verifyAggregateAlgebra`. -/
theorem zero_certificate_passes_algebra (suite : TweakableHashSuite) (params : PqHashParams)
    (committee : List PqPublicKey) (bitmap : SignerBitmapSpec)
    (traceComm : List UInt8) (challenges : List GoldilocksExt2)
    (hLen : bitmap.length = committee.length)
    (hPos : 0 < bitmapPopcountSpec bitmap)
    (hVars : 0 < challenges.length) :
    verifyAggregateAlgebra committee
      (buildHonestAggregate suite params committee bitmap traceComm challenges) = true := by
  simp [verifyAggregateAlgebra, buildHonestAggregate, hLen, hPos, hVars,
        verifySumcheckChain_zeroPolys]

/-- Constructive check of every active signer bit $i$ in `bitmap` against `verifyPqHashSig`. -/
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
  | pk :: pks, b :: bs, sig :: sigs, 0, _, _, hAll, hbTrue =>
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
    ∃ sig, verifyPqHashSig suite params (pks[i]'hPk) msg sig = true :=
  let ⟨sig, hVer⟩ := extractActiveSignerSig suite params msg pks bs sigs i hPk hB hAll hbTrue
  ⟨sig, hVer⟩

/-- **Constructive Round-by-Round Sumcheck Divergence Extractor (`extractSumcheckHitFromChain`)**:
    Walks `(claimedPolys, honestPolys, challenges)` simultaneously with **`0 Classical.choice`**:
    whenever `curClaim ≠ honestClaim` at the start of the Sumcheck chain while both chains pass
    `verifySumcheckChain` and agree at `terminalEval`, constructively locates the **exact** first round
    `roundIdx` where `claimedPoly` and `honestPoly` disagree at `diffPoint ∈ {0, 1}` yet collide at
    verifier challenge `r`, outputting a concrete `SumcheckSchwartzZippelHit`! -/
def extractSumcheckHitFromChain
    (claimedPolys : List (List GoldilocksExt2)) :
    ∀ (curClaim honestClaim : GoldilocksExt2)
      (honestPolys : List (List GoldilocksExt2))
      (challenges : List GoldilocksExt2)
      (termEval : GoldilocksExt2),
      curClaim ≠ honestClaim →
      verifySumcheckChain curClaim claimedPolys challenges termEval = true →
      verifySumcheckChain honestClaim honestPolys challenges termEval = true →
      SumcheckSchwartzZippelHit claimedPolys honestPolys challenges :=
  match claimedPolys with
  | [] => fun curClaim honestClaim honestPolys challenges termEval hNe hVerC hVerH =>
    match honestPolys, challenges with
    | [], [] =>
      False.elim (by
        simp only [verifySumcheckChain, beq_iff_eq] at hVerC hVerH
        exact hNe (hVerC.trans hVerH.symm))
    | _ :: _, [] => False.elim (by simp [verifySumcheckChain] at hVerH)
    | _, _ :: _ => False.elim (by simp [verifySumcheckChain] at hVerC)
  | pC :: psC => fun curClaim honestClaim honestPolys challenges termEval hNe hVerC hVerH =>
    match honestPolys, challenges with
    | _, [] => False.elim (by simp [verifySumcheckChain] at hVerC)
    | [], _ :: _ => False.elim (by simp [verifySumcheckChain] at hVerH)
    | pH :: psH, r :: rs =>
      have hUnpackC : pC.length ≤ 9 ∧
          CommRingOps.add (RoundPoly.evalCoeffs pC GoldilocksExt2.zero)
                          (RoundPoly.evalCoeffs pC GoldilocksExt2.one) = curClaim ∧
          verifySumcheckChain (RoundPoly.evalCoeffs pC r) psC rs termEval = true := by
        simp only [verifySumcheckChain, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hVerC
        exact ⟨hVerC.1.1, hVerC.1.2, hVerC.2⟩
      have hUnpackH : pH.length ≤ 9 ∧
          CommRingOps.add (RoundPoly.evalCoeffs pH GoldilocksExt2.zero)
                          (RoundPoly.evalCoeffs pH GoldilocksExt2.one) = honestClaim ∧
          verifySumcheckChain (RoundPoly.evalCoeffs pH r) psH rs termEval = true := by
        simp only [verifySumcheckChain, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hVerH
        exact ⟨hVerH.1.1, hVerH.1.2, hVerH.2⟩
      let diffPt : GoldilocksExt2 :=
        if RoundPoly.evalCoeffs pC GoldilocksExt2.zero ≠ RoundPoly.evalCoeffs pH GoldilocksExt2.zero
        then GoldilocksExt2.zero
        else GoldilocksExt2.one
      have hDiffPt : RoundPoly.evalCoeffs pC diffPt ≠ RoundPoly.evalCoeffs pH diffPt := by
        dsimp only [diffPt]
        if h0 : RoundPoly.evalCoeffs pC GoldilocksExt2.zero ≠ RoundPoly.evalCoeffs pH GoldilocksExt2.zero then
          simp [h0]
        else
          have hEq0 : RoundPoly.evalCoeffs pC GoldilocksExt2.zero = RoundPoly.evalCoeffs pH GoldilocksExt2.zero :=
            Decidable.of_not_not h0
          simp only [h0, ↓reduceIte]
          intro hEq1
          apply hNe
          rw [← hUnpackC.2.1, ← hUnpackH.2.1, hEq0, hEq1]
      if hHit : RoundPoly.evalCoeffs pC r = RoundPoly.evalCoeffs pH r then
        { roundIdx    := 0
          claimedPoly := pC
          honestPoly  := pH
          challenge   := r
          claimed_at := rfl
          honest_at := rfl
          challenge_at := rfl
          lenClaimed  := hUnpackC.1
          lenHonest   := hUnpackH.1
          diffPoint   := diffPt
          polyNe      := hDiffPt
          hitEq       := hHit }
      else
        let hit := extractSumcheckHitFromChain psC
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

/-- Committed prover witness table opened by the Argument-of-Knowledge extractor. -/
structure CommittedAggregateTrace (committee : List PqPublicKey) (msg : List UInt8)
    (agg : AggregatedSignature) where
  sigs         : List PqHashSig
  encodeTrace  : List PqHashSig → List UInt8
  commHash     : Hash
  honestClaim  : GoldilocksExt2
  honestPolys  : List (List GoldilocksExt2)

/-- **Constructive `0 Classical.choice` Argument-of-Knowledge Extractor (`extractAggregateWitnessOrBreak`)**:
    Given an accepted `AggregatedSignature` (`verifyAggregateAlgebra committee agg = true`) and a
    committed trace opening `tr` (`tr.commHash (tr.encodeTrace tr.sigs) = agg.traceCommitment`):
    1. Either every active validator bit in `agg.bitmap` holds a valid `PqHashSig`
       (`checkAllActiveSigners = true`),
    2. Or if a distinct preimage `altPreimage ≠ tr.encodeTrace tr.sigs` also hashes to
       `agg.traceCommitment`, extracts a concrete `HashCollisionWitness tr.commHash`,
    3. Or when the invalid trace forces non-zero honest batch constraint sum
       (`tr.honestClaim ≠ GoldilocksExt2.zero`) while agreeing with the opened PCS evaluation
       `agg.terminalEval`, constructively extracts a concrete `SumcheckSchwartzZippelHit` via
       `extractSumcheckHitFromChain`! -/
def extractAggregateWitnessOrBreak
    (committee : List PqPublicKey) (msg : List UInt8) (agg : AggregatedSignature)
    (tr : CommittedAggregateTrace committee msg agg)
    (canonicalPreimage : List UInt8)
    (hVerAgg : verifyAggregateAlgebra committee agg = true)
    (hOpen : tr.commHash (tr.encodeTrace tr.sigs) = agg.traceCommitment)
    (hCanon : tr.commHash canonicalPreimage = agg.traceCommitment)
    (hHonestSound :
      checkAllActiveSigners agg.suite agg.params msg committee agg.bitmap tr.sigs = false →
      tr.encodeTrace tr.sigs = canonicalPreimage →
      tr.honestClaim ≠ GoldilocksExt2.zero ∧
      verifySumcheckChain tr.honestClaim tr.honestPolys agg.challenges agg.terminalEval = true) :
    PSum { _u : Unit // checkAllActiveSigners agg.suite agg.params msg committee agg.bitmap tr.sigs = true }
         (PSum (HashCollisionWitness tr.commHash)
           (SumcheckSchwartzZippelHit agg.roundPolys tr.honestPolys agg.challenges)) :=
  if hChk : checkAllActiveSigners agg.suite agg.params msg committee agg.bitmap tr.sigs = true then
    .inl ⟨(), hChk⟩
  else
    have hChkFalse : checkAllActiveSigners agg.suite agg.params msg committee agg.bitmap tr.sigs = false :=
      Bool.eq_false_iff.mpr hChk
    if hEqPre : tr.encodeTrace tr.sigs = canonicalPreimage then
      let ⟨hClaimNz, hHonChain⟩ := hHonestSound hChkFalse hEqPre
      have hAggChain : verifySumcheckChain agg.claimedSum agg.roundPolys agg.challenges agg.terminalEval = true ∧
          agg.claimedSum = GoldilocksExt2.zero := by
        unfold verifyAggregateAlgebra at hVerAgg
        rcases Bool.and_eq_true_iff.mp hVerAgg with ⟨h12345, hSc⟩
        rcases Bool.and_eq_true_iff.mp h12345 with ⟨_, hZ⟩
        exact ⟨hSc, eq_of_beq hZ⟩
      have hNeClaim : agg.claimedSum ≠ tr.honestClaim := by
        rw [hAggChain.2]
        exact fun hEq => hClaimNz hEq.symm
      .inr (.inr (extractSumcheckHitFromChain agg.roundPolys agg.claimedSum tr.honestClaim
        tr.honestPolys agg.challenges agg.terminalEval
        hNeClaim hAggChain.1 hHonChain))
    else
      .inr (.inl ⟨tr.encodeTrace tr.sigs, canonicalPreimage, hEqPre, hOpen.trans hCanon.symm⟩)

/-- **End-to-End Succinct $K$-to-$1$ PQ Aggregation Unforgeability Reduction
    (`qsag_aggregate_unforgeability_reduction`)**:
    Welds `verifyAggregateAlgebra` + `extractAggregateWitnessOrBreak` + `extractActiveSignerSig`
    directly into `extractFullHypertreeForgery` (`Qsag.HypertreeEufCma`) with **`0 Classical.choice`**:
    Whenever an adversary produces an accepted `AggregatedSignature` with active bit `agg.bitmap[i] = true`
    for an honest validator `committee[i] = derivePublicKey agg.suite agg.params sk_i` who never signed
    `msg` (`msg ∉ queriedMsgs`), this extractor constructively outputs ONE OF:
    1. A concrete underlying PQ primitive break `HypertreeForgeryBreak` (`WotsBackwardInversionWitness`,
       `ForsPreimageWitness`, `HashCollisionWitness`, or stateless `ForsSubsetCoverWitness`),
    2. A trace-commitment `HashCollisionWitness tr.commHash`, OR
    3. A concrete `SumcheckSchwartzZippelHit` (bounded by $\le 8 / |\mathbb{F}_{p^2}|$ per round via
       `sumcheck_degree8_round_roots_le_eight`)! -/
def qsag_aggregate_unforgeability_reduction
    (committee : List PqPublicKey) (msg : List UInt8) (agg : AggregatedSignature)
    (tr : CommittedAggregateTrace committee msg agg)
    (canonicalPreimage : List UInt8)
    (i : Nat) (hPk : i < committee.length) (hB : i < agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : committee[i]'hPk = derivePublicKey agg.suite agg.params sk_i)
    (hActive_i : agg.bitmap[i]'hB = true)
    (queriedMsgs : List (List UInt8))
    (qOracle : QueriedWotsOracle)
    (revealedFors : List (UInt64 × Nat × Nat))
    (hParams4_128 : agg.params.w = 4 ∧ agg.params.ell1 = 128)
    (hFreshMsg : msg ∉ queriedMsgs)
    (hVerAgg : verifyAggregateAlgebra committee agg = true)
    (hOpen : tr.commHash (tr.encodeTrace tr.sigs) = agg.traceCommitment)
    (hCanon : tr.commHash canonicalPreimage = agg.traceCommitment)
    (hHonestSound :
      checkAllActiveSigners agg.suite agg.params msg committee agg.bitmap tr.sigs = false →
      tr.encodeTrace tr.sigs = canonicalPreimage →
      tr.honestClaim ≠ GoldilocksExt2.zero ∧
      verifySumcheckChain tr.honestClaim tr.honestPolys agg.challenges agg.terminalEval = true)
    (hStatefulLeaf0Msg : ∀ sig : PqHashSig, agg.params.statefulJorts = true →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ agg.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ agg.params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        ∃ mPrev ∈ queriedMsgs,
          hRoot = thPreHash agg.suite sk_i.pkSeed (derivePublicKey agg.suite agg.params sk_i).pkRoot mPrev)
    (hStatelessLayer0Root : ∀ sig : PqHashSig, agg.params.statefulJorts = false →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ agg.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ agg.params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        hRoot = computeForsPk agg.suite agg.params sk_i
          (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ agg.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ agg.params.subtreeHeight))
    (hUpperOracle : ∀ (l : Nat) (g : Nat), 0 < l →
      let hRoot0 := computeXmssSubtreeRoot agg.suite agg.params sk_i (UInt32.ofNat (l - 1)) (UInt64.ofNat g)
      (∀ hRand hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ agg.params.subtreeHeight)) (g % 2 ^ agg.params.subtreeHeight) =
          some (hRand, hRoot0, hCtr, hChains) →
        let hmH := thHashMsg agg.suite hRand sk_i.pkSeed (derivePublicKey agg.suite agg.params sk_i).pkRoot hRoot0
          (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ agg.params.subtreeHeight))
          (UInt32.ofNat (g % 2 ^ agg.params.subtreeHeight)) hCtr
        let digH := extractBaseWDigits agg.params.w agg.params.ell1 hmH
        checkTargetSum agg.params.w agg.params.ell1 agg.params.targetSum digH = true ∧
        recoverWotsPkFromSig agg.suite agg.params sk_i.pkSeed (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ agg.params.subtreeHeight)) (g % 2 ^ agg.params.subtreeHeight) digH hChains =
        computeWotsPk agg.suite agg.params sk_i (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ agg.params.subtreeHeight)) (g % 2 ^ agg.params.subtreeHeight)) ∧
      (∀ hRand hR hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ agg.params.subtreeHeight)) (g % 2 ^ agg.params.subtreeHeight) =
          some (hRand, hR, hCtr, hChains) → hR = hRoot0))
    (hLayer0Valid : ∀ sig : PqHashSig, ∀ hRand hRoot0 hCtr hChains,
      qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ agg.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ agg.params.subtreeHeight) = some (hRand, hRoot0, hCtr, hChains) →
      let hmH := thHashMsg agg.suite hRand sk_i.pkSeed (derivePublicKey agg.suite agg.params sk_i).pkRoot hRoot0
        0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ agg.params.subtreeHeight))
        (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ agg.params.subtreeHeight)) hCtr
      let digH := extractBaseWDigits agg.params.w agg.params.ell1 hmH
      checkTargetSum agg.params.w agg.params.ell1 agg.params.targetSum digH = true ∧
      recoverWotsPkFromSig agg.suite agg.params sk_i.pkSeed 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ agg.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ agg.params.subtreeHeight) digH hChains =
      computeWotsPk agg.suite agg.params sk_i 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ agg.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ agg.params.subtreeHeight)) :
    PSum (Sigma fun sig_i : PqHashSig =>
            HypertreeForgeryBreak agg.suite agg.params sk_i msg sig_i revealedFors)
         (PSum (HashCollisionWitness tr.commHash)
           (SumcheckSchwartzZippelHit agg.roundPolys tr.honestPolys agg.challenges)) :=
  match extractAggregateWitnessOrBreak committee msg agg tr canonicalPreimage
          hVerAgg hOpen hCanon hHonestSound with
  | .inr brk => .inr brk
  | .inl ⟨_, hAllOk⟩ =>
    let ⟨sig_i, hVer_i⟩ := extractActiveSignerSig agg.suite agg.params msg
      committee agg.bitmap tr.sigs i hPk hB hAllOk hActive_i
    have hVerKey : verifyPqHashSig agg.suite agg.params
        (derivePublicKey agg.suite agg.params sk_i) msg sig_i = true := by
      rw [← hKey_i]; exact hVer_i
    .inl ⟨sig_i, extractFullHypertreeForgery agg.suite agg.params sk_i msg sig_i
      queriedMsgs qOracle revealedFors hParams4_128 hFreshMsg hVerKey
      (hStatefulLeaf0Msg sig_i) (hStatelessLayer0Root sig_i)
      hUpperOracle (hLayer0Valid sig_i)⟩

/-! ## Transparent reference verification

This gate verifies the opened signatures themselves. It is deliberately linear in committee size;
replacing those openings by a succinct PCS proof still requires the production trace refinement.
The algebra-only checker above is retained for counterexamples and conditional reductions.
-/

structure AggPublicInstance where
  suite : TweakableHashSuite
  params : PqHashParams
  message : List UInt8
  committee : List PqPublicKey
  signingModeDigest : List UInt8

/-- Canonical framing for the reference gate; the suite and parameters are trusted instance inputs. -/
def aggregateInstanceFrame (inst : AggPublicInstance) (agg : AggregatedSignature) : List UInt8 :=
  encodeMultiFrame [inst.message, inst.signingModeDigest,
    encodeMultiFrame (inst.committee.map (fun pk => encodeMultiFrame [pk.pkSeed, pk.pkRoot])),
    encodeMultiFrame ([inst.params.w, inst.params.ell1, inst.params.subtreeHeight,
      inst.params.numLayers, inst.params.forsTrees, inst.params.forsHeight,
      inst.params.maxSigsLog2].map (fun n => (toString n).toUTF8.toList)),
    [if inst.params.statefulJorts then 1 else 0],
    agg.bitmap.map (fun b => if b then 1 else 0), agg.traceCommitment,
    match agg.childrenCommitment with
    | none => []
    | some (left, right) => encodeMultiFrame [left, right]]

def encodeAggregateSignature (sig : PqHashSig) : List UInt8 :=
  encodeMultiFrame [sig.rRand, (toString sig.msgTswCtr).toUTF8.toList,
    (toString sig.leafGlobalIdx).toUTF8.toList,
    encodeMultiFrame (sig.forsOpenings.map (fun op => encodeMultiFrame
      [op.secretVal, encodeMultiFrame op.authPath])),
    encodeMultiFrame (sig.layerSigs.map (fun layer => encodeMultiFrame
      [(toString layer.tswCtr).toUTF8.toList, encodeMultiFrame layer.wotsChains,
        encodeMultiFrame layer.authPath]))]

def aggregateTraceCommitment (sigs : List PqHashSig) : List UInt8 :=
  cshake256Bytes "QSAG.AGG.REFERENCE.TRACE/v1".toUTF8.toList
    (encodeMultiFrame (sigs.map encodeAggregateSignature))

def encodeRoundPoly (p : List GoldilocksExt2) : List UInt8 :=
  encodeMultiFrame (p.map (fun x => be 8 x.c0.val ++ be 8 x.c1.val))

/-- Each challenge absorbs its polynomial and every preceding round, after the instance commitment. -/
def deriveAggregateChallenges (prior : List UInt8) : List (List GoldilocksExt2) → List GoldilocksExt2
  | [] => []
  | p :: ps =>
    let frame := encodeMultiFrame [prior, encodeRoundPoly p]
    let bytes := cshake256Bytes "QSAG.AGG.REFERENCE.FS/v1".toUTF8.toList frame
    let natOf := fun bs : List UInt8 => bs.foldl (fun n b => 256 * n + b.toNat) 0
    let r : GoldilocksExt2 := ⟨Goldilocks.ofNat (natOf (bytes.take 16)),
      Goldilocks.ofNat (natOf (bytes.drop 16))⟩
    r :: deriveAggregateChallenges frame ps

/-- Instance-bound transparent gate. Empty/signature-free certificates fail before algebra checking. -/
def verifyAggregatedSignature (inst : AggPublicInstance) (agg : AggregatedSignature)
    (openedSignatures : List PqHashSig) (fsTranscript : List UInt8) : Bool :=
  decide (openedSignatures.length = inst.committee.length) &&
  decide (fsTranscript = aggregateInstanceFrame inst agg) &&
  decide (agg.traceCommitment = aggregateTraceCommitment openedSignatures) &&
  decide (agg.challenges = deriveAggregateChallenges fsTranscript agg.roundPolys) &&
  verifyAggregateAlgebra inst.committee agg &&
  checkAllActiveSigners inst.suite inst.params inst.message inst.committee agg.bitmap openedSignatures

/-- No cryptographic soundness premise: the actual opened signatures pass the actual signature checker. -/
theorem aggregate_opened_signatures_sound (inst : AggPublicInstance) (agg : AggregatedSignature)
    (sigs : List PqHashSig) (fs : List UInt8)
    (h : verifyAggregatedSignature inst agg sigs fs = true) :
    checkAllActiveSigners inst.suite inst.params inst.message inst.committee agg.bitmap sigs = true :=
  (Bool.and_eq_true_iff.mp h).2

/-- Constructive extraction for any active signer, without an assumed honest-trace soundness premise. -/
def extractVerifiedAggregateSigner (inst : AggPublicInstance) (agg : AggregatedSignature)
    (sigs : List PqHashSig) (fs : List UInt8) (i : Nat)
    (hi : i < inst.committee.length) (hb : i < agg.bitmap.length)
    (h : verifyAggregatedSignature inst agg sigs fs = true) (active : agg.bitmap[i]'hb = true) :
    { sig : PqHashSig // verifyPqHashSig inst.suite inst.params (inst.committee[i]'hi) inst.message sig = true } :=
  extractActiveSignerSig inst.suite inst.params inst.message inst.committee agg.bitmap sigs i hi hb
    (aggregate_opened_signatures_sound inst agg sigs fs h) active

/-- Regression: a signature-free certificate cannot satisfy the reference verifier for any committee. -/
theorem zero_certificate_rejected (inst : AggPublicInstance) (agg : AggregatedSignature)
    (fs : List UInt8) : verifyAggregatedSignature inst agg [] fs = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [verifyAggregatedSignature, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hLen, _⟩, _⟩, _⟩, hAlg⟩, _⟩ := h
  simp only [verifyAggregateAlgebra, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hAlg
  obtain ⟨⟨⟨⟨⟨hBitmapLen, hCount⟩, hPos⟩, _⟩, _⟩, _⟩ := hAlg
  have hb : agg.bitmap = [] := List.eq_nil_of_length_eq_zero (by
    simp only [List.length_nil] at hLen
    omega)
  rw [hb] at hCount
  simp only [bitmapPopcountSpec] at hCount
  omega

/-- Regression: changing the public instance frame invalidates the transcript before algebra checks. -/
theorem aggregate_wrong_instance_rejected (inst : AggPublicInstance) (agg : AggregatedSignature)
    (sigs : List PqHashSig) (fs : List UInt8) (h : fs ≠ aggregateInstanceFrame inst agg) :
    verifyAggregatedSignature inst agg sigs fs = false := by
  simp only [verifyAggregatedSignature, decide_eq_false h, Bool.and_false, Bool.false_and]

/-- Regression: challenges supplied by the prover cannot override the Fiat–Shamir schedule. -/
theorem aggregate_wrong_challenges_rejected (inst : AggPublicInstance) (agg : AggregatedSignature)
    (sigs : List PqHashSig) (fs : List UInt8)
    (h : agg.challenges ≠ deriveAggregateChallenges fs agg.roundPolys) :
    verifyAggregatedSignature inst agg sigs fs = false := by
  simp only [verifyAggregatedSignature, decide_eq_false h, Bool.and_false, Bool.false_and]

inductive MergeNode where
  | leaf (certificate : AggregatedSignature) (signatures : List PqHashSig) (transcript : List UInt8)
  | branch (certificate : AggregatedSignature) (signatures : List PqHashSig) (transcript : List UInt8)
      (left right : MergeNode)

def MergeNode.certificate : MergeNode → AggregatedSignature
  | .leaf agg _ _ => agg
  | .branch agg _ _ _ _ => agg

/-- Every child is verified against the same message/committee/mode; overlap is rejected at every branch. -/
def verifyMergeTree (inst : AggPublicInstance) : Nat → MergeNode → Bool
  | 0, _ => false
  | _ + 1, .leaf agg sigs fs =>
    agg.childrenCommitment.isNone && verifyAggregatedSignature inst agg sigs fs
  | budget + 1, .branch agg sigs fs left right =>
    decide (agg.childrenCommitment = some (left.certificate.traceCommitment, right.certificate.traceCommitment)) &&
    verifyMergeTree inst budget left && verifyMergeTree inst budget right &&
    bitmapDisjointSpec left.certificate.bitmap right.certificate.bitmap &&
    decide (agg.bitmap = bitmapUnionSpec left.certificate.bitmap right.certificate.bitmap) &&
    verifyAggregatedSignature inst agg sigs fs

theorem merge_tree_rejects_invalid_child (inst : AggPublicInstance) (budget : Nat)
    (agg : AggregatedSignature) (sigs : List PqHashSig) (fs : List UInt8) (left right : MergeNode)
    (h : verifyMergeTree inst budget left = false ∨ verifyMergeTree inst budget right = false) :
    verifyMergeTree inst (budget + 1) (.branch agg sigs fs left right) = false := by
  rcases h with h | h <;> simp only [verifyMergeTree, h, Bool.false_and, Bool.and_false]

theorem merge_tree_rejects_overlap (inst : AggPublicInstance) (budget : Nat)
    (agg : AggregatedSignature) (sigs : List PqHashSig) (fs : List UInt8) (left right : MergeNode)
    (h : bitmapDisjointSpec left.certificate.bitmap right.certificate.bitmap = false) :
    verifyMergeTree inst (budget + 1) (.branch agg sigs fs left right) = false := by
  simp only [verifyMergeTree, h, Bool.false_and, Bool.and_false]

/-- Child commitment substitution is rejected even if all signature and bitmap checks pass. -/
theorem merge_tree_rejects_child_commitment (inst : AggPublicInstance) (budget : Nat)
    (agg : AggregatedSignature) (sigs : List PqHashSig) (fs : List UInt8) (left right : MergeNode)
    (h : agg.childrenCommitment ≠ some (left.certificate.traceCommitment, right.certificate.traceCommitment)) :
    verifyMergeTree inst (budget + 1) (.branch agg sigs fs left right) = false := by
  simp only [verifyMergeTree, decide_eq_false h, Bool.false_and]

theorem merge_tree_depth_exhausted (inst : AggPublicInstance) (tree : MergeNode) :
    verifyMergeTree inst 0 tree = false := by rfl

/-- A ninth-degree round is rejected even if its evaluations would satisfy the chain. -/
theorem sumcheck_degree9_rejected (claim terminal : GoldilocksExt2)
    (p : List GoldilocksExt2) (ps : List (List GoldilocksExt2))
    (r : GoldilocksExt2) (rs : List GoldilocksExt2) (h : 9 < p.length) :
    verifySumcheckChain claim (p :: ps) (r :: rs) terminal = false := by
  simp only [verifySumcheckChain, show ¬ p.length ≤ 9 by omega, decide_false, Bool.false_and]

/-- Instance framing binds the message before any hash or signature assumption is used. -/
theorem aggregate_frame_message_binding (first second : AggPublicInstance)
    (a b : AggregatedSignature)
    (h : aggregateInstanceFrame first a = aggregateInstanceFrame second b) :
    first.message = second.message := by
  have hf := encodeMultiFrame_injective h
  exact (List.cons.inj hf).1

theorem aggregate_message_substitution_rejected (first second : AggPublicInstance)
    (agg : AggregatedSignature) (sigs : List PqHashSig) (h : first.message ≠ second.message) :
    verifyAggregatedSignature second agg sigs (aggregateInstanceFrame first agg) = false :=
  aggregate_wrong_instance_rejected second agg sigs _
    (fun hf => h (aggregate_frame_message_binding first second agg agg hf))

/-- Accepted reference certificates expose all binding checks as well as valid signatures. -/
theorem aggregate_acceptance_binding (inst : AggPublicInstance) (agg : AggregatedSignature)
    (sigs : List PqHashSig) (fs : List UInt8)
    (h : verifyAggregatedSignature inst agg sigs fs = true) :
    fs = aggregateInstanceFrame inst agg ∧
    agg.traceCommitment = aggregateTraceCommitment sigs ∧
    agg.challenges = deriveAggregateChallenges fs agg.roundPolys ∧
    checkAllActiveSigners inst.suite inst.params inst.message inst.committee agg.bitmap sigs = true := by
  simp only [verifyAggregatedSignature, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hf⟩, hc⟩, hr⟩, _⟩, hs⟩ := h
  exact ⟨hf, hc, hr, hs⟩

theorem merge_tree_children_sound (inst : AggPublicInstance) (budget : Nat)
    (agg : AggregatedSignature) (sigs : List PqHashSig) (fs : List UInt8) (left right : MergeNode)
    (h : verifyMergeTree inst (budget + 1) (.branch agg sigs fs left right) = true) :
    verifyMergeTree inst budget left = true ∧ verifyMergeTree inst budget right = true ∧
    agg.childrenCommitment = some (left.certificate.traceCommitment, right.certificate.traceCommitment) := by
  simp only [verifyMergeTree, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hc, hl⟩, hr⟩, _⟩, _⟩, _⟩ := h
  exact ⟨hl, hr, hc⟩

/-! ## 5. Production succinct-aggregation parameters

Constants read from the Rust implementation (`crates/qsag-agg/src`). -/

/-- Parameters of the production succinct aggregation proof system. -/
structure ProductionAggParams where
  /-- `ROW_SUMCHECK_DEGREE`, `arithmetize.rs:46`. -/
  rowSumcheckDegree : Nat
  /-- `LOG_TRACE_COLS`, `trace.rs:25`. -/
  logTraceCols : Nat
  /-- Largest accepted PCS variable count: `num_vars > 24` is rejected, `pcs.rs:1542`. -/
  maxPcsVars : Nat
  /-- `RS_BLOWUP` (inverse code rate), `pcs.rs:33`. -/
  rsBlowup : Nat
  /-- `NUM_PCS_QUERIES`, `pcs.rs:35`. -/
  numQueries : Nat
  /-- `EARLY_STOP_VARS`, `pcs.rs:52`. -/
  earlyStopVars : Nat
  /-- `MAX_FOLD_STEP_VARS` (log2 of the committed coset-group arity), `pcs.rs:54`. -/
  maxFoldStepVars : Nat
  /-- Degree of the interleaved PCS sumcheck round polynomials (`[GoldilocksExt2; 3]`), `pcs.rs:588`. -/
  pcsSumcheckDegree : Nat
  /-- `PCS_POW_BITS`, `pcs.rs:50`. Not counted in any bound below. -/
  powBits : Nat
  /-- `MAX_MERGE_TREE_DEPTH`, `lib.rs:54`. -/
  maxMergeDepth : Nat
  /-- Order of the challenge field `GoldilocksExt2` (`GOLDILOCKS_PRIME` squared, `field.rs:10`). -/
  fieldSize : Nat

def productionAggParams : ProductionAggParams where
  rowSumcheckDegree := 8
  logTraceCols := 8
  maxPcsVars := 24
  rsBlowup := 16
  numQueries := 160
  earlyStopVars := 7
  maxFoldStepVars := 4
  pcsSumcheckDegree := 2
  powBits := 16
  maxMergeDepth := 16
  fieldSize := goldilocksPrime ^ 2

/-- Row-sumcheck rounds: `log_rows = num_vars - LOG_TRACE_COLS` (`arithmetize.rs:1256`). -/
def ProductionAggParams.maxRowRounds (p : ProductionAggParams) : Nat := p.maxPcsVars - p.logTraceCols

/-- Folding challenges: `fold_vars = num_vars - early_stop` (`pcs.rs:1546`). -/
def ProductionAggParams.maxFoldRounds (p : ProductionAggParams) : Nat := p.maxPcsVars - p.earlyStopVars

/-- Round-0 evaluation domain: `(1 << num_vars) * RS_BLOWUP` (`pcs.rs:1555`). -/
def ProductionAggParams.maxDomain (p : ProductionAggParams) : Nat := 2 ^ p.maxPcsVars * p.rsBlowup

/-- Round-0 query domain: coset groups, `domain_0 / expected_arity_0` (`pcs.rs:1556`). -/
def ProductionAggParams.maxQueryGroups (p : ProductionAggParams) : Nat :=
  p.maxDomain / 2 ^ p.maxFoldStepVars

theorem productionAggParams_derived :
    productionAggParams.maxRowRounds = 16 ∧ productionAggParams.maxFoldRounds = 17 ∧
    productionAggParams.maxDomain = 2 ^ 28 ∧ productionAggParams.maxQueryGroups = 2 ^ 24 := by
  decide

