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

/-! ## 6. Counting challenge vectors: adaptive union bound -/

private theorem filter_const_false {α : Type} : ∀ (l : List α), l.filter (fun _ => false) = []
  | [] => rfl
  | _ :: xs => filter_const_false xs

private theorem filter_eq_nil_of_forall {α : Type} {p : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = false) → l.filter p = []
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (List.mem_cons_self ..)
    simp only [List.filter, hx]
    exact filter_eq_nil_of_forall xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

private theorem filter_eq_self_of_all {α : Type} {p : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = true) → l.filter p = l
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (List.mem_cons_self ..)
    simp only [List.filter, hx]
    exact congrArg (x :: ·) (filter_eq_self_of_all xs (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem filter_length_le_self {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.filter p).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := filter_length_le_self p xs
    cases hp : p x
    · simp only [List.filter, hp, List.length_cons]
      exact Nat.le_succ_of_le ih
    · simp only [List.filter, hp, List.length_cons]
      exact Nat.succ_le_succ ih

private theorem filter_length_mono {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | x :: xs, h => by
    have ih := filter_length_mono xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hp : p x
    · cases hq : q x
      · simp only [List.filter, hp, hq]
        exact ih
      · simp only [List.filter, hp, hq, List.length_cons]
        exact Nat.le_succ_of_le ih
    · have hq := h x (List.mem_cons_self ..) hp
      simp only [List.filter, hp, hq, List.length_cons]
      exact Nat.succ_le_succ ih

private theorem filter_flatMap_eq {α β : Type} (p : β → Bool) (f : α → List β) :
    ∀ (l : List α), (l.flatMap f).filter p = l.flatMap (fun x => (f x).filter p)
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.flatMap_cons, List.filter_append, filter_flatMap_eq p f xs]

private theorem filter_map_length {α β : Type} (p : β → Bool) (f : α → β) :
    ∀ (l : List α), ((l.map f).filter p).length = (l.filter (fun x => p (f x))).length
  | [] => rfl
  | x :: xs => by
    have ih := filter_map_length p f xs
    cases hp : p (f x)
    · simp only [List.map, List.filter, hp]
      exact ih
    · simp only [List.map, List.filter, hp, List.length_cons]
      exact congrArg Nat.succ ih

private theorem length_flatMap_const {α β : Type} (k : Nat) (f : α → List β) :
    ∀ (l : List α), (∀ c ∈ l, (f c).length = k) → (l.flatMap f).length = l.length * k
  | [], _ => by
    show 0 = 0 * k
    rw [Nat.zero_mul]
  | c :: l, h => by
    have ih := length_flatMap_const k f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc := h c (List.mem_cons_self ..)
    rw [List.flatMap_cons, List.length_append, ih, hc, List.length_cons, Nat.add_mul, Nat.one_mul,
      Nat.add_comm]

/-- Weighted sum bound: elements flagged by `b` contribute at most `T`, the others at most `M`. -/
private theorem length_flatMap_le_split {α β : Type} (b : α → Bool) (T M : Nat) (f : α → List β) :
    ∀ (l : List α), (∀ c ∈ l, (f c).length ≤ if b c = true then T else M) →
      (l.flatMap f).length ≤ (l.filter b).length * T + l.length * M
  | [], _ => Nat.zero_le _
  | c :: l, h => by
    have ih := length_flatMap_le_split b T M f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc := h c (List.mem_cons_self ..)
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    cases hb : b c
    · rw [hb] at hc
      have hc' : (f c).length ≤ M := hc
      simp only [List.filter, hb]
      omega
    · rw [hb] at hc
      have hc' : (f c).length ≤ T := hc
      simp only [List.filter, hb, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- All length-`n` challenge vectors over the challenge list `S`. -/
def challengeVectors {α : Type} (S : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => S.flatMap (fun r => (challengeVectors S n).map (fun rs => r :: rs))

theorem challengeVectors_length {α : Type} (S : List α) :
    ∀ (n : Nat), (challengeVectors S n).length = S.length ^ n
  | 0 => rfl
  | n + 1 => by
    show (S.flatMap (fun r => (challengeVectors S n).map (fun rs => r :: rs))).length = _
    rw [length_flatMap_const (S.length ^ n) _ S
      (fun r _ => by rw [List.length_map, challengeVectors_length S n]),
      Nat.pow_succ, Nat.mul_comm]

theorem length_of_mem_challengeVectors {α : Type} (S : List α) :
    ∀ (n : Nat) (rs : List α), rs ∈ challengeVectors S n → rs.length = n
  | 0, rs, h => by
    have hrs : rs = [] := List.mem_singleton.mp h
    rw [hrs]
    rfl
  | n + 1, rs, h => by
    have h' : rs ∈ S.flatMap (fun r => (challengeVectors S n).map (fun rs => r :: rs)) := h
    rw [List.mem_flatMap] at h'
    obtain ⟨r, _, hr⟩ := h'
    rw [List.mem_map] at hr
    obtain ⟨tl, htl, hEq⟩ := hr
    rw [← hEq, List.length_cons, length_of_mem_challengeVectors S n tl htl]

/-- A per-round event that may depend on every earlier challenge (the prefix, oldest first)
    occurs in at least one round of the challenge vector. -/
def anyRoundEvent {α : Type} : (List α → α → Bool) → List α → Bool
  | _, [] => false
  | E, r :: rs => E [] r || anyRoundEvent (fun pre => E (r :: pre)) rs

/-- `d 0 + d 1 + ... + d (n - 1)`. -/
def roundBoundSum : (Nat → Nat) → Nat → Nat
  | _, 0 => 0
  | d, n + 1 => d 0 + roundBoundSum (fun j => d (j + 1)) n

theorem roundBoundSum_const (d : Nat) : ∀ (n : Nat), roundBoundSum (fun _ => d) n = n * d
  | 0 => by
    show 0 = 0 * d
    rw [Nat.zero_mul]
  | n + 1 => by
    show d + roundBoundSum (fun _ => d) n = (n + 1) * d
    rw [roundBoundSum_const d n, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- **Adaptive union bound.** If for every prefix at most `d (prefix length)` challenges of `S`
    trigger the round event, then at most `(d 0 + ... + d (n-1)) * |S|^(n-1)` of the `|S|^n`
    challenge vectors trigger it in some round. -/
theorem anyRoundEvent_count_le {α : Type} (S : List α) :
    ∀ (n : Nat) (E : List α → α → Bool) (d : Nat → Nat),
      (∀ pre, (S.filter (E pre)).length ≤ d pre.length) →
      ((challengeVectors S n).filter (anyRoundEvent E)).length ≤
        roundBoundSum d n * S.length ^ (n - 1)
  | 0, E, d, _ => by
    show (([[]] : List (List α)).filter (anyRoundEvent E)).length ≤ _
    simp only [List.filter, anyRoundEvent]
    exact Nat.zero_le _
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
          funext rs
          show (E [] r || anyRoundEvent (fun pre => E (r :: pre)) rs) = _
          rw [hE]
          rfl
        rw [hfun]
        exact anyRoundEvent_count_le S n (fun pre => E (r :: pre)) (fun j => d (j + 1))
          (fun pre => h (r :: pre))
      · have hle := filter_length_le_self (fun rs => anyRoundEvent E (r :: rs)) (challengeVectors S n)
        rw [challengeVectors_length] at hle
        exact hle
    have hSplit := length_flatMap_le_split (E []) (S.length ^ n) M
      (fun r => ((challengeVectors S n).map (fun rs => r :: rs)).filter (anyRoundEvent E)) S hEach
    have h0 : (S.filter (E [])).length ≤ d 0 := h []
    have hA : (S.filter (E [])).length * S.length ^ n ≤ d 0 * S.length ^ n :=
      Nat.mul_le_mul_right _ h0
    have hB : S.length * M ≤ roundBoundSum (fun j => d (j + 1)) n * S.length ^ n := by
      cases n with
      | zero =>
        show S.length * (0 * S.length ^ (0 - 1)) ≤ _
        rw [Nat.zero_mul, Nat.mul_zero]
        exact Nat.zero_le _
      | succ k =>
        show S.length * (roundBoundSum (fun j => d (j + 1)) (k + 1) * S.length ^ (k + 1 - 1)) ≤ _
        rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm S.length (S.length ^ k)]
        exact Nat.le_refl _
    rw [Nat.add_mul]
    exact Nat.le_trans hSplit (Nat.add_le_add hA hB)

/-- Uniform per-round bound `d`: at most `n * d * |S|^(n-1)` challenge vectors trigger the event. -/
theorem anyRoundEvent_count_le_uniform {α : Type} (S : List α) (n d : Nat)
    (E : List α → α → Bool) (h : ∀ pre, (S.filter (E pre)).length ≤ d) :
    ((challengeVectors S n).filter (anyRoundEvent E)).length ≤ n * d * S.length ^ (n - 1) := by
  have hb := anyRoundEvent_count_le S n E (fun _ => d) h
  rw [roundBoundSum_const] at hb
  exact hb

/-! ## 7. Degree-8 sumcheck: counting bound against adaptive provers -/

/-- Round polynomials of a prover whose round-`j` message is a function of the challenges
    `r_0, ..., r_{j-1}` already issued. -/
def adaptivePolys : (List GoldilocksExt2 → List GoldilocksExt2) → List GoldilocksExt2 →
    List (List GoldilocksExt2)
  | _, [] => []
  | strat, r :: rs => strat [] :: adaptivePolys (fun pre => strat (r :: pre)) rs

/-- Nine distinct field points; two polynomials of degree at most eight that agree on all of them
    agree everywhere. -/
def sumcheckProbePoints : List GoldilocksExt2 :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8].map (fun k => GoldilocksExt2.ofBase (Goldilocks.ofNat k))

theorem sumcheckProbePoints_nodup : sumcheckProbePoints.Nodup := by decide +kernel

/-- Decidable form of "the two round polynomials are different functions". -/
def roundPolysDiffer (c h : List GoldilocksExt2) : Bool :=
  sumcheckProbePoints.any
    (fun x => decide (RoundPoly.evalCoeffs c x ≠ RoundPoly.evalCoeffs h x))

theorem exists_of_roundPolysDiffer (c h : List GoldilocksExt2) (hb : roundPolysDiffer c h = true) :
    ∃ x : GoldilocksExt2, RoundPoly.evalCoeffs c x ≠ RoundPoly.evalCoeffs h x := by
  obtain ⟨x, _, hx⟩ := List.any_eq_true.mp hb
  exact ⟨x, of_decide_eq_true hx⟩

theorem roundPolysDiffer_of_exists (c h : List GoldilocksExt2)
    (hc : c.length ≤ 9) (hh : h.length ≤ 9)
    (hd : ∃ x : GoldilocksExt2, RoundPoly.evalCoeffs c x ≠ RoundPoly.evalCoeffs h x) :
    roundPolysDiffer c h = true := by
  cases hb : roundPolysDiffer c h with
  | true => rfl
  | false =>
    exfalso
    have hall : ∀ x ∈ sumcheckProbePoints,
        decide (RoundPoly.evalCoeffs c x = RoundPoly.evalCoeffs h x) = true := by
      intro x hx
      apply decide_eq_true
      apply Decidable.of_not_not
      intro hne
      have ht : roundPolysDiffer c h = true := List.any_eq_true.mpr ⟨x, hx, decide_eq_true hne⟩
      rw [hb] at ht
      cases ht
    have hbound := sumcheck_round_roots_le_degree 8 c h sumcheckProbePoints
      sumcheckProbePoints_nodup hc hh hd
    rw [filter_eq_self_of_all _ hall] at hbound
    exact absurd hbound (by decide)

/-- Round event: both polynomials have at most nine coefficients, are different functions, and
    agree at the round challenge. -/
def sumcheckRoundEvent (claimed honest : List GoldilocksExt2 → List GoldilocksExt2)
    (pre : List GoldilocksExt2) (r : GoldilocksExt2) : Bool :=
  (decide ((claimed pre).length ≤ 9) && decide ((honest pre).length ≤ 9) &&
    roundPolysDiffer (claimed pre) (honest pre)) &&
  decide (RoundPoly.evalCoeffs (claimed pre) r = RoundPoly.evalCoeffs (honest pre) r)

/-- Some round of the transcript `(adaptivePolys claimed rs, adaptivePolys honest rs, rs)` is a
    Schwartz–Zippel hit. -/
def sumcheckHitOccurs (claimed honest : List GoldilocksExt2 → List GoldilocksExt2)
    (rs : List GoldilocksExt2) : Bool :=
  anyRoundEvent (sumcheckRoundEvent claimed honest) rs

theorem sumcheckRoundEvent_roots_le_eight
    (claimed honest : List GoldilocksExt2 → List GoldilocksExt2) (S : List GoldilocksExt2)
    (hS : S.Nodup) (pre : List GoldilocksExt2) :
    (S.filter (sumcheckRoundEvent claimed honest pre)).length ≤ 8 := by
  cases hg : (decide ((claimed pre).length ≤ 9) && decide ((honest pre).length ≤ 9) &&
      roundPolysDiffer (claimed pre) (honest pre)) with
  | false =>
    have hfun : sumcheckRoundEvent claimed honest pre = fun _ => false := by
      funext r
      unfold sumcheckRoundEvent
      rw [hg]
      rfl
    rw [hfun, filter_const_false]
    exact Nat.zero_le 8
  | true =>
    have hfun : sumcheckRoundEvent claimed honest pre = fun r =>
        decide (RoundPoly.evalCoeffs (claimed pre) r = RoundPoly.evalCoeffs (honest pre) r) := by
      funext r
      unfold sumcheckRoundEvent
      rw [hg]
      rfl
    rw [hfun]
    rcases Bool.and_eq_true_iff.mp hg with ⟨hlen, hdiff⟩
    rcases Bool.and_eq_true_iff.mp hlen with ⟨hc, hh⟩
    exact sumcheck_degree8_round_roots_le_eight _ _ S hS (of_decide_eq_true hc)
      (of_decide_eq_true hh) (exists_of_roundPolysDiffer _ _ hdiff)

/-- Every transcript-indexed hit of an adaptive transcript is seen by `sumcheckHitOccurs`. -/
theorem sumcheckHitOccurs_of_round :
    ∀ (rs : List GoldilocksExt2) (claimed honest : List GoldilocksExt2 → List GoldilocksExt2)
      (i : Nat) (cp hp : List GoldilocksExt2) (ch : GoldilocksExt2),
      (adaptivePolys claimed rs)[i]? = some cp →
      (adaptivePolys honest rs)[i]? = some hp →
      rs[i]? = some ch →
      cp.length ≤ 9 → hp.length ≤ 9 →
      (∃ x : GoldilocksExt2, RoundPoly.evalCoeffs cp x ≠ RoundPoly.evalCoeffs hp x) →
      RoundPoly.evalCoeffs cp ch = RoundPoly.evalCoeffs hp ch →
      sumcheckHitOccurs claimed honest rs = true
  | [], _, _, _, _, _, _, _, _, hch, _, _, _, _ => by
    simp only [List.getElem?_nil] at hch
    cases hch
  | r :: rs, claimed, honest, 0, cp, hp, ch, hc, hh, hch, lc, lh, hd, he => by
    have hc' : claimed [] = cp := Option.some.inj hc
    have hh' : honest [] = hp := Option.some.inj hh
    have hch' : r = ch := Option.some.inj hch
    subst hc' hh' hch'
    have hEv : sumcheckRoundEvent claimed honest [] r = true :=
      Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨decide_eq_true lc, decide_eq_true lh⟩, roundPolysDiffer_of_exists _ _ lc lh hd⟩,
        decide_eq_true he⟩
    show (sumcheckRoundEvent claimed honest [] r ||
      anyRoundEvent (fun pre => sumcheckRoundEvent claimed honest (r :: pre)) rs) = true
    rw [hEv]
    rfl
  | r :: rs, claimed, honest, i + 1, cp, hp, ch, hc, hh, hch, lc, lh, hd, he => by
    have ih : anyRoundEvent (fun pre => sumcheckRoundEvent claimed honest (r :: pre)) rs = true :=
      sumcheckHitOccurs_of_round rs (fun pre => claimed (r :: pre)) (fun pre => honest (r :: pre))
        i cp hp ch hc hh hch lc lh hd he
    show (sumcheckRoundEvent claimed honest [] r ||
      anyRoundEvent (fun pre => sumcheckRoundEvent claimed honest (r :: pre)) rs) = true
    rw [ih]
    exact Bool.or_true _

theorem sumcheckHitOccurs_of_hit (claimed honest : List GoldilocksExt2 → List GoldilocksExt2)
    (rs : List GoldilocksExt2)
    (hit : SumcheckSchwartzZippelHit (adaptivePolys claimed rs) (adaptivePolys honest rs) rs) :
    sumcheckHitOccurs claimed honest rs = true :=
  sumcheckHitOccurs_of_round rs claimed honest hit.roundIdx hit.claimedPoly hit.honestPoly
    hit.challenge hit.claimed_at hit.honest_at hit.challenge_at hit.lenClaimed hit.lenHonest
    ⟨hit.diffPoint, hit.polyNe⟩ hit.hitEq

/-- A false claim accepted against the same terminal value as the honest chain forces a hit. -/
theorem sumcheck_false_claim_accept_forces_hit
    (claimed honest : List GoldilocksExt2 → List GoldilocksExt2)
    (curClaim honestClaim : GoldilocksExt2) (rs : List GoldilocksExt2) (termEval : GoldilocksExt2)
    (hNe : curClaim ≠ honestClaim)
    (hC : verifySumcheckChain curClaim (adaptivePolys claimed rs) rs termEval = true)
    (hH : verifySumcheckChain honestClaim (adaptivePolys honest rs) rs termEval = true) :
    sumcheckHitOccurs claimed honest rs = true :=
  sumcheckHitOccurs_of_hit claimed honest rs
    (extractSumcheckHitFromChain _ curClaim honestClaim _ rs termEval hNe hC hH)

/-- At most `n * 8 * |S|^(n-1)` of the `|S|^n` challenge vectors produce a hit, for any adaptive
    prover and honest strategies and any duplicate-free challenge list `S`. -/
theorem sumcheck_hit_challenges_le (S : List GoldilocksExt2) (hS : S.Nodup) (n : Nat)
    (claimed honest : List GoldilocksExt2 → List GoldilocksExt2) :
    ((challengeVectors S n).filter (sumcheckHitOccurs claimed honest)).length ≤
      n * 8 * S.length ^ (n - 1) :=
  anyRoundEvent_count_le_uniform S n 8 (sumcheckRoundEvent claimed honest)
    (sumcheckRoundEvent_roots_le_eight claimed honest S hS)

/-- No challenge vector lets a false claim pass without a hit. `termEval rs` is the terminal
    value both chains are checked against (the committed-polynomial evaluation). -/
theorem sumcheck_false_claim_accepting_without_hit_count_zero
    (S : List GoldilocksExt2) (n : Nat)
    (claimed honest : List GoldilocksExt2 → List GoldilocksExt2)
    (curClaim honestClaim : GoldilocksExt2) (termEval : List GoldilocksExt2 → GoldilocksExt2)
    (hNe : curClaim ≠ honestClaim)
    (hHonest : ∀ rs ∈ challengeVectors S n,
      verifySumcheckChain honestClaim (adaptivePolys honest rs) rs (termEval rs) = true) :
    ((challengeVectors S n).filter (fun rs =>
      verifySumcheckChain curClaim (adaptivePolys claimed rs) rs (termEval rs) &&
      !sumcheckHitOccurs claimed honest rs)).length = 0 := by
  rw [filter_eq_nil_of_forall]
  · rfl
  · intro rs hrs
    cases hAcc : verifySumcheckChain curClaim (adaptivePolys claimed rs) rs (termEval rs)
    · rfl
    · rw [sumcheck_false_claim_accept_forces_hit claimed honest curClaim honestClaim rs
        (termEval rs) hNe hAcc (hHonest rs hrs)]
      rfl

/-- **Sumcheck soundness count.** A false claim is accepted on at most `n * 8 * |S|^(n-1)` of
    the `|S|^n` challenge vectors. -/
theorem sumcheck_false_claim_accepting_challenges_le
    (S : List GoldilocksExt2) (hS : S.Nodup) (n : Nat)
    (claimed honest : List GoldilocksExt2 → List GoldilocksExt2)
    (curClaim honestClaim : GoldilocksExt2) (termEval : List GoldilocksExt2 → GoldilocksExt2)
    (hNe : curClaim ≠ honestClaim)
    (hHonest : ∀ rs ∈ challengeVectors S n,
      verifySumcheckChain honestClaim (adaptivePolys honest rs) rs (termEval rs) = true) :
    ((challengeVectors S n).filter (fun rs =>
      verifySumcheckChain curClaim (adaptivePolys claimed rs) rs (termEval rs))).length ≤
      n * 8 * S.length ^ (n - 1) :=
  Nat.le_trans
    (filter_length_mono (challengeVectors S n) (fun rs hrs hAcc =>
      sumcheck_false_claim_accept_forces_hit claimed honest curClaim honestClaim rs (termEval rs)
        hNe hAcc (hHonest rs hrs)))
    (sumcheck_hit_challenges_le S hS n claimed honest)

/-- Production instantiation: with at most 16 degree-8 rounds over a challenge set at least as
    large as `GoldilocksExt2`, the accepting fraction is below `2^-120`. -/
theorem sumcheck_production_error_lt (s n : Nat) (hn0 : 0 < n)
    (hn : n ≤ productionAggParams.maxRowRounds) (hs : productionAggParams.fieldSize ≤ s) :
    (n * productionAggParams.rowSumcheckDegree * s ^ (n - 1)) * 2 ^ 120 < s ^ n := by
  cases n with
  | zero => exact absurd hn0 (Nat.lt_irrefl 0)
  | succ k =>
    have hn' : k + 1 ≤ 16 := hn
    have hs' : goldilocksPrime ^ 2 ≤ s := hs
    have h1 : (k + 1) * 8 * 2 ^ 120 < s :=
      Nat.lt_of_le_of_lt
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hn'))
        (Nat.lt_of_lt_of_le (by decide : 16 * 8 * 2 ^ 120 < goldilocksPrime ^ 2) hs')
    have hsPos : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le _) h1
    have hpos : 0 < s ^ k := Nat.pow_pos hsPos
    show (k + 1) * 8 * s ^ (k + 1 - 1) * 2 ^ 120 < s ^ (k + 1)
    have hpow : s ^ (k + 1) = s * s ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [Nat.add_sub_cancel, Nat.mul_right_comm, hpow]
    exact Nat.mul_lt_mul_of_pos_right h1 hpos

/-- Toy honest prover for `g(x, y) = x * y`: round polynomials `X` and `r₁ * Y`. -/
private def toyHonestStrategy : List GoldilocksExt2 → List GoldilocksExt2
  | [] => [CommRingOps.zero, CommRingOps.one]
  | r :: _ => [CommRingOps.zero, r]

private def toyTerminal : List GoldilocksExt2 → GoldilocksExt2
  | [r₁, r₂] => CommRingOps.mul r₁ r₂
  | _ => CommRingOps.zero

private theorem evalCoeffs_pair (a b x : GoldilocksExt2) :
    RoundPoly.evalCoeffs [a, b] x = CommRingOps.add a (CommRingOps.mul x b) := by
  simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-- Inhabitedness of the counting hypotheses: a genuine two-round sumcheck (for `x * y`, true
    sum `1`) whose honest chain verifies at every challenge vector, a false claim `0`, and a
    cheating prover that is accepted at the challenge vector `(0, 0)`. -/
theorem sumcheck_counting_hypotheses_satisfiable :
    ∃ (honest claimed : List GoldilocksExt2 → List GoldilocksExt2)
      (honestClaim curClaim : GoldilocksExt2) (termEval : List GoldilocksExt2 → GoldilocksExt2),
      curClaim ≠ honestClaim ∧
      (∀ (S : List GoldilocksExt2), ∀ rs ∈ challengeVectors S 2,
        verifySumcheckChain honestClaim (adaptivePolys honest rs) rs (termEval rs) = true) ∧
      (∃ rs : List GoldilocksExt2, rs.length = 2 ∧
        verifySumcheckChain curClaim (adaptivePolys claimed rs) rs (termEval rs) = true) := by
  refine ⟨toyHonestStrategy, fun _ => [CommRingOps.zero], CommRingOps.one, CommRingOps.zero,
    toyTerminal, by decide +kernel, ?_, ⟨[CommRingOps.zero, CommRingOps.zero], rfl, by decide +kernel⟩⟩
  intro S rs hrs
  have hlen := length_of_mem_challengeVectors S 2 rs hrs
  match rs, hlen with
  | [r₁, r₂], _ =>
    have hz : (CommRingOps.zero : GoldilocksExt2) = GoldilocksExt2.zero := rfl
    have ho : (CommRingOps.one : GoldilocksExt2) = GoldilocksExt2.one := rfl
    simp only [adaptivePolys, toyHonestStrategy, toyTerminal, verifySumcheckChain,
      evalCoeffs_pair, ← hz, ← ho, List.length_cons, List.length_nil,
      LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
      LawfulCommRing.zero_add, LawfulCommRing.one_mul, LawfulCommRing.mul_one,
      LawfulCommRing.mul_comm r₂ r₁, beq_self_eq_true, Bool.and_true, Bool.and_self,
      decide_eq_true_eq]
    decide

/-! ## 8. BaseFold query phase: counting distinct query tuples

`pcs.rs:36-45` (`sample_pcs_queries`) inserts squeezed indices into a `BTreeSet` until it holds
`min(NUM_PCS_QUERIES, domain)` of them: the verifier queries a set of *distinct* round-0 coset
groups. The counting below is over ordered tuples of pairwise distinct positions; every
`q`-subset corresponds to the same number `q!` of such tuples, so the fractions coincide (that
correspondence is not formalised here). -/

/-- Every way of removing one position from a list: the removed element and the remainder. -/
def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | x :: xs => (x, xs) :: (picks xs).map (fun p => (p.1, x :: p.2))

/-- Ordered `q`-tuples drawn from pairwise distinct positions of `dom`. -/
def distinctTuples {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | q + 1, dom => (picks dom).flatMap (fun p => (distinctTuples q p.2).map (fun t => p.1 :: t))

/-- `n * (n - 1) * ... * (n - q + 1)`. -/
def fallingFactorial : Nat → Nat → Nat
  | _, 0 => 1
  | n, q + 1 => n * fallingFactorial (n - 1) q

/-- Number of positions of `l` satisfying `good`. -/
def countGood {α : Type} (good : α → Bool) (l : List α) : Nat := (l.filter good).length

private theorem countGood_cons {α : Type} (good : α → Bool) (x : α) (xs : List α) :
    countGood good (x :: xs) = (if good x = true then 1 else 0) + countGood good xs := by
  cases hg : good x
  · simp only [countGood, List.filter, hg]
    show _ = 0 + _
    rw [Nat.zero_add]
  · simp only [countGood, List.filter, hg, List.length_cons]
    show _ = 1 + _
    rw [Nat.add_comm]

private theorem countGood_const_true {α : Type} :
    ∀ (l : List α), countGood (fun _ => true) l = l.length
  | [] => rfl
  | x :: xs => by
    rw [countGood_cons, countGood_const_true xs, List.length_cons]
    show 1 + xs.length = xs.length + 1
    rw [Nat.add_comm]

theorem countGood_not_add {α : Type} (bad : α → Bool) :
    ∀ (l : List α), countGood (fun x => !bad x) l + countGood bad l = l.length
  | [] => rfl
  | x :: xs => by
    have ih := countGood_not_add bad xs
    rw [countGood_cons, countGood_cons, List.length_cons]
    cases hb : bad x
    · show (1 + _) + (0 + _) = _
      omega
    · show (0 + _) + (1 + _) = _
      omega

private theorem picks_map_fst {α : Type} : ∀ (l : List α), (picks l).map Prod.fst = l
  | [] => rfl
  | x :: xs => by
    show x :: ((picks xs).map (fun p => (p.1, x :: p.2))).map Prod.fst = x :: xs
    rw [List.map_map]
    exact congrArg (x :: ·) (picks_map_fst xs)

private theorem picks_good_split {α : Type} (good : α → Bool) :
    ∀ (l : List α) (p : α × List α), p ∈ picks l →
      countGood good p.2 + (if good p.1 = true then 1 else 0) = countGood good l
  | [], _, h => by cases h
  | x :: xs, p, h => by
    rcases List.mem_cons.mp h with hp | hp
    · rw [hp, countGood_cons, Nat.add_comm]
    · obtain ⟨p', hp', hEq⟩ := List.mem_map.mp hp
      have ih := picks_good_split good xs p' hp'
      rw [← hEq]
      show countGood good (x :: p'.2) + (if good p'.1 = true then 1 else 0) = _
      rw [countGood_cons, countGood_cons]
      omega

private theorem picks_spec {α : Type} :
    ∀ (l : List α) (p : α × List α), p ∈ picks l → l.Nodup →
      p.1 ∈ l ∧ p.1 ∉ p.2 ∧ p.2.Nodup ∧ ∀ y ∈ p.2, y ∈ l
  | [], _, h, _ => by cases h
  | x :: xs, p, h, hnd => by
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hxs : xs.Nodup := (List.nodup_cons.mp hnd).2
    rcases List.mem_cons.mp h with hp | hp
    · rw [hp]
      exact ⟨List.mem_cons_self .., hx, hxs, fun y hy => List.mem_cons_of_mem _ hy⟩
    · obtain ⟨p', hp', hEq⟩ := List.mem_map.mp hp
      obtain ⟨h0, h1, h2, h3⟩ := picks_spec xs p' hp' hxs
      rw [← hEq]
      refine ⟨List.mem_cons_of_mem _ h0, ?_, List.nodup_cons.mpr ⟨fun hm => hx (h3 x hm), h2⟩, ?_⟩
      · intro hm
        rcases List.mem_cons.mp hm with e | e
        · exact hx (e ▸ h0)
        · exact h1 e
      · intro y hy
        rcases List.mem_cons.mp hy with e | e
        · rw [e]
          exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (h3 y e)

/-- Tuples drawn from a duplicate-free domain have pairwise distinct entries, all in the domain. -/
theorem distinctTuples_nodup {α : Type} :
    ∀ (q : Nat) (dom : List α) (t : List α), dom.Nodup → t ∈ distinctTuples q dom →
      t.Nodup ∧ t.length = q ∧ ∀ y ∈ t, y ∈ dom
  | 0, _, t, _, h => by
    have ht : t = [] := List.mem_singleton.mp h
    rw [ht]
    exact ⟨List.Pairwise.nil, rfl, fun y hy => by cases hy⟩
  | q + 1, dom, t, hnd, h => by
    have h' : t ∈ (picks dom).flatMap
        (fun p => (distinctTuples q p.2).map (fun t => p.1 :: t)) := h
    obtain ⟨p, hp, ht⟩ := List.mem_flatMap.mp h'
    obtain ⟨tl, htl, hEq⟩ := List.mem_map.mp ht
    obtain ⟨h0, h1, h2, h3⟩ := picks_spec dom p hp hnd
    obtain ⟨i1, i2, i3⟩ := distinctTuples_nodup q p.2 tl h2 htl
    rw [← hEq]
    refine ⟨List.nodup_cons.mpr ⟨fun hm => h1 (i3 p.1 hm), i1⟩, ?_, ?_⟩
    · rw [List.length_cons, i2]
    · intro y hy
      rcases List.mem_cons.mp hy with e | e
      · rw [e]
        exact h0
      · exact h3 y (i3 y e)

private theorem length_flatMap_picks {α β : Type} (good : α → Bool) (c : Nat)
    (F : α × List α → List β) :
    ∀ (ps : List (α × List α)),
      (∀ p ∈ ps, (F p).length = if good p.1 = true then c else 0) →
      (ps.flatMap F).length = countGood good (ps.map Prod.fst) * c
  | [], _ => by
    show 0 = 0 * c
    rw [Nat.zero_mul]
  | p :: ps, h => by
    have ih := length_flatMap_picks good c F ps (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hp := h p (List.mem_cons_self ..)
    rw [List.flatMap_cons, List.length_append, ih, hp]
    show _ = countGood good (p.1 :: ps.map Prod.fst) * c
    rw [countGood_cons, Nat.add_mul]
    cases hg : good p.1
    · show 0 + _ = 0 * c + _
      rw [Nat.zero_mul]
    · show c + _ = 1 * c + _
      rw [Nat.one_mul]

/-- Exact count: tuples all of whose positions are good. -/
theorem distinctTuples_all_good_length {α : Type} (good : α → Bool) :
    ∀ (q : Nat) (dom : List α),
      ((distinctTuples q dom).filter (fun t => t.all good)).length =
        fallingFactorial (countGood good dom) q
  | 0, _ => rfl
  | q + 1, dom => by
    show (((picks dom).flatMap (fun p => (distinctTuples q p.2).map (fun t => p.1 :: t))).filter
      (fun t => t.all good)).length =
        countGood good dom * fallingFactorial (countGood good dom - 1) q
    have hEach : ∀ p ∈ picks dom,
        (((distinctTuples q p.2).map (fun t => p.1 :: t)).filter (fun t => t.all good)).length =
          if good p.1 = true then fallingFactorial (countGood good dom - 1) q else 0 := by
      intro p hp
      rw [filter_map_length]
      have hsplit := picks_good_split good dom p hp
      cases hg : good p.1
      · have hfun : (fun t : List α => (p.1 :: t).all good) = fun _ => false := by
          funext t
          show (good p.1 && t.all good) = false
          rw [hg]
          rfl
        rw [hfun, filter_const_false]
        rfl
      · have hfun : (fun t : List α => (p.1 :: t).all good) = fun t => t.all good := by
          funext t
          show (good p.1 && t.all good) = t.all good
          rw [hg]
          rfl
        rw [hfun, distinctTuples_all_good_length good q p.2]
        rw [hg] at hsplit
        have h1 : countGood good p.2 + 1 = countGood good dom := hsplit
        have h2 : countGood good p.2 = countGood good dom - 1 := by omega
        rw [h2]
        rfl
    rw [filter_flatMap_eq, length_flatMap_picks good _ _ (picks dom) hEach, picks_map_fst]

private theorem all_const_true {α : Type} : ∀ (t : List α), t.all (fun _ => true) = true
  | [] => rfl
  | _ :: xs => all_const_true xs

/-- Exact count of all distinct-position tuples. -/
theorem distinctTuples_length {α : Type} (q : Nat) (dom : List α) :
    (distinctTuples q dom).length = fallingFactorial dom.length q := by
  have h := distinctTuples_all_good_length (fun _ : α => true) q dom
  rw [filter_eq_self_of_all _ (fun t _ => all_const_true t), countGood_const_true] at h
  exact h

theorem fallingFactorial_pos : ∀ (q n : Nat), q ≤ n → 0 < fallingFactorial n q
  | 0, _, _ => Nat.one_pos
  | q + 1, 0, h => absurd h (Nat.not_succ_le_zero q)
  | q + 1, n + 1, h => by
    show 0 < (n + 1) * fallingFactorial (n + 1 - 1) q
    rw [Nat.add_sub_cancel]
    exact Nat.mul_pos (Nat.succ_pos n) (fallingFactorial_pos q n (Nat.le_of_succ_le_succ h))

/-- If `G / N ≤ a / b ≤ 1` then `G(G-1)...(G-q+1) / N(N-1)...(N-q+1) ≤ (a / b)^q`. -/
theorem fallingFactorial_mul_pow_le (a b : Nat) (hab : a ≤ b) :
    ∀ (q G N : Nat), G ≤ N → G * b ≤ a * N →
      fallingFactorial G q * b ^ q ≤ a ^ q * fallingFactorial N q
  | 0, _, _, _, _ => Nat.le_refl 1
  | q + 1, 0, N, _, _ => by
    show 0 * fallingFactorial (0 - 1) q * b ^ (q + 1) ≤ _
    rw [Nat.zero_mul, Nat.zero_mul]
    exact Nat.zero_le _
  | q + 1, G + 1, 0, hGN, _ => absurd hGN (Nat.not_succ_le_zero G)
  | q + 1, G + 1, N + 1, hGN, hfar => by
    have hGN' : G ≤ N := Nat.le_of_succ_le_succ hGN
    have hfar' : G * b ≤ a * N := by
      have e1 : (G + 1) * b = G * b + b := by rw [Nat.add_mul, Nat.one_mul]
      have e2 : a * (N + 1) = a * N + a := by rw [Nat.mul_add, Nat.mul_one]
      rw [e1, e2] at hfar
      omega
    have ih := fallingFactorial_mul_pow_le a b hab q G N hGN' hfar'
    show (G + 1) * fallingFactorial (G + 1 - 1) q * b ^ (q + 1) ≤
      a ^ (q + 1) * ((N + 1) * fallingFactorial (N + 1 - 1) q)
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.pow_succ, Nat.pow_succ]
    have hL : (G + 1) * fallingFactorial G q * (b ^ q * b) =
        ((G + 1) * b) * (fallingFactorial G q * b ^ q) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hR : a ^ q * a * ((N + 1) * fallingFactorial N q) =
        (a * (N + 1)) * (a ^ q * fallingFactorial N q) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hL, hR]
    exact Nat.mul_le_mul hfar ih

/-- **Query-miss count (exact Nat inequality).** If the bad positions are at least a `dn / dd`
    fraction of the query domain, then among all ordered tuples of `q` distinct positions the
    fraction that misses every bad position is at most `((dd - dn) / dd)^q`. -/
theorem basefold_query_miss_bound {α : Type} (bad : α → Bool) (dom : List α) (q dn dd : Nat)
    (hfar : dn * dom.length ≤ dd * countGood bad dom) :
    ((distinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length * dd ^ q ≤
      (dd - dn) ^ q * (distinctTuples q dom).length := by
  rw [distinctTuples_all_good_length, distinctTuples_length]
  have hsum := countGood_not_add bad dom
  have hGN : countGood (fun x => !bad x) dom ≤ dom.length := by omega
  apply fallingFactorial_mul_pow_le (dd - dn) dd (Nat.sub_le dd dn) q _ _ hGN
  rw [Nat.sub_mul, Nat.mul_comm (countGood (fun x => !bad x) dom) dd]
  have e : dd * dom.length =
      dd * countGood (fun x => !bad x) dom + dd * countGood bad dom := by
    rw [← Nat.mul_add, hsum]
  omega

/-- `(17/32)^160 < 2^-145`: the unique-decoding query error for rate `1/16` and 160 queries. -/
theorem basefold_production_query_exponent :
    (2 * productionAggParams.rsBlowup - (productionAggParams.rsBlowup - 1)) ^
        productionAggParams.numQueries * 2 ^ 145 <
      (2 * productionAggParams.rsBlowup) ^ productionAggParams.numQueries := by
  decide

/-- The exponent 145 is the true one for these parameters: `(17/32)^160 > 2^-147`. -/
theorem basefold_production_query_exponent_tight :
    (2 * productionAggParams.rsBlowup) ^ productionAggParams.numQueries <
      (2 * productionAggParams.rsBlowup - (productionAggParams.rsBlowup - 1)) ^
        productionAggParams.numQueries * 2 ^ 147 := by
  decide

/-- **Production query bound.** With `NUM_PCS_QUERIES = 160` distinct queries and a bad set of
    relative size at least `(1 - 1/16) / 2 = 15/32` (the unique-decoding radius of the rate-1/16
    code), fewer than a `2^-145` fraction of the query tuples miss the bad set. -/
theorem basefold_production_query_miss_lt {α : Type} (bad : α → Bool) (dom : List α)
    (hdom : productionAggParams.numQueries ≤ dom.length)
    (hfar : (productionAggParams.rsBlowup - 1) * dom.length ≤
      2 * productionAggParams.rsBlowup * countGood bad dom) :
    ((distinctTuples productionAggParams.numQueries dom).filter
      (fun t => t.all (fun x => !bad x))).length * 2 ^ 145 <
      (distinctTuples productionAggParams.numQueries dom).length := by
  have hb := basefold_query_miss_bound bad dom productionAggParams.numQueries
    (productionAggParams.rsBlowup - 1) (2 * productionAggParams.rsBlowup) hfar
  have hT : 0 < (distinctTuples productionAggParams.numQueries dom).length := by
    rw [distinctTuples_length]
    exact fallingFactorial_pos _ _ hdom
  have hK := basefold_production_query_exponent
  rcases Nat.lt_or_ge
    (((distinctTuples productionAggParams.numQueries dom).filter
      (fun t => t.all (fun x => !bad x))).length * 2 ^ 145)
    (distinctTuples productionAggParams.numQueries dom).length with hlt | hge
  · exact hlt
  · exfalso
    generalize ((distinctTuples productionAggParams.numQueries dom).filter
      (fun t => t.all (fun x => !bad x))).length = X at hb hge
    generalize (distinctTuples productionAggParams.numQueries dom).length = T at hb hge hT
    generalize (2 * productionAggParams.rsBlowup - (productionAggParams.rsBlowup - 1)) ^
      productionAggParams.numQueries = M at hb hK
    generalize (2 * productionAggParams.rsBlowup) ^ productionAggParams.numQueries = K at hb hK
    have hX : 0 < X := by
      cases X with
      | zero =>
        rw [Nat.zero_mul] at hge
        exact absurd hT (Nat.not_lt.mpr hge)
      | succ k => exact Nat.succ_pos k
    have h1 : M * T ≤ M * (X * 2 ^ 145) := Nat.mul_le_mul_left M hge
    have h2 : M * (X * 2 ^ 145) = X * (M * 2 ^ 145) := Nat.mul_left_comm M X (2 ^ 145)
    have h3 : X * (M * 2 ^ 145) < X * K := Nat.mul_lt_mul_of_pos_left hK hX
    rw [h2] at h1
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h3 (Nat.le_trans hb h1))

/-! ## 9. BaseFold fold consistency: per-round challenge count -/

/-- A committed coset duet together with a candidate folded value fixed before the challenge. -/
structure TrackedDuet where
  v0 : GoldilocksExt2
  v1 : GoldilocksExt2
  invTwoY0 : Goldilocks
  invTwo : Goldilocks
  next : GoldilocksExt2

/-- The duet folds to the candidate at challenge `r` although it does not at `0` or not at `1`
    (so the affine fold relation is not an identity in the challenge). -/
def foldDuetEvent (d : TrackedDuet) (r : GoldilocksExt2) : Bool :=
  (decide (foldDuetExt2 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.zero ≠ d.next) ||
    decide (foldDuetExt2 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.one ≠ d.next)) &&
  decide (foldDuetExt2 d.v0 d.v1 d.invTwoY0 d.invTwo r = d.next)

theorem foldDuetEvent_roots_le_one (d : TrackedDuet) (S : List GoldilocksExt2) (hS : S.Nodup) :
    (S.filter (foldDuetEvent d)).length ≤ 1 := by
  cases hg : (decide (foldDuetExt2 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.zero ≠ d.next) ||
      decide (foldDuetExt2 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.one ≠ d.next)) with
  | false =>
    have hfun : foldDuetEvent d = fun _ => false := by
      funext r
      unfold foldDuetEvent
      rw [hg]
      rfl
    rw [hfun, filter_const_false]
    exact Nat.zero_le 1
  | true =>
    have hfun : foldDuetEvent d =
        fun r => decide (foldDuetExt2 d.v0 d.v1 d.invTwoY0 d.invTwo r = d.next) := by
      funext r
      unfold foldDuetEvent
      rw [hg]
      rfl
    rw [hfun]
    have hne : ∃ r, foldDuetExt2 d.v0 d.v1 d.invTwoY0 d.invTwo r ≠ d.next := by
      cases h0 : decide (foldDuetExt2 d.v0 d.v1 d.invTwoY0 d.invTwo CommRingOps.zero ≠ d.next) with
      | true => exact ⟨_, of_decide_eq_true h0⟩
      | false =>
        rw [h0] at hg
        exact ⟨_, of_decide_eq_true hg⟩
    exact basefold_coset_duet_roots_le_one d.v0 d.v1 d.next d.invTwoY0 d.invTwo S hS hne

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
    rw [filter_const_false]
    exact Nat.zero_le _
  | d :: ds, h => by
    have ih := filter_any_length_le S ev k ds (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hd := h d (List.mem_cons_self ..)
    have hor := filter_or_length_le (ev d) (fun r => ds.any (fun d => ev d r)) S
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    have hor' : (S.filter (fun r => (d :: ds).any (fun d => ev d r))).length ≤
        (S.filter (ev d)).length + (S.filter (fun r => ds.any (fun d => ev d r))).length := hor
    omega

/-- Some tracked duet of the round is a fold event. The tracked duets may depend on all earlier
    challenges. -/
def foldRoundEvent (tracked : List GoldilocksExt2 → List TrackedDuet)
    (pre : List GoldilocksExt2) (r : GoldilocksExt2) : Bool :=
  (tracked pre).any (fun d => foldDuetEvent d r)

theorem foldRoundEvent_roots_le (tracked : List GoldilocksExt2 → List TrackedDuet)
    (S : List GoldilocksExt2) (hS : S.Nodup) (pre : List GoldilocksExt2) :
    (S.filter (foldRoundEvent tracked pre)).length ≤ (tracked pre).length := by
  have h := filter_any_length_le S foldDuetEvent 1 (tracked pre)
    (fun d _ => foldDuetEvent_roots_le_one d S hS)
  rw [Nat.mul_one] at h
  exact h

/-- **Fold-challenge count.** With at most `m` tracked committed duets per round, at most
    `n * m * |S|^(n-1)` of the `|S|^n` folding-challenge vectors make some tracked duet fold to
    its pre-committed candidate without doing so identically. -/
theorem basefold_fold_hit_challenges_le (S : List GoldilocksExt2) (hS : S.Nodup) (n m : Nat)
    (tracked : List GoldilocksExt2 → List TrackedDuet)
    (hm : ∀ pre, (tracked pre).length ≤ m) :
    ((challengeVectors S n).filter (anyRoundEvent (foldRoundEvent tracked))).length ≤
      n * m * S.length ^ (n - 1) :=
  anyRoundEvent_count_le_uniform S n m (foldRoundEvent tracked)
    (fun pre => Nat.le_trans (foldRoundEvent_roots_le tracked S hS pre) (hm pre))

/-! ## 10. Succinct aggregate verifier with a Merkle-opened BaseFold query phase

Model (see the notes at `verifySuccinctAggregate`): an interleaved commit / degree-8 sumcheck /
arity-2 fold protocol. Round `j` absorbs the layer-`j` Merkle root and the round polynomial before
its challenge is derived; that one challenge is both the sumcheck challenge and the folding
challenge of layer `j`. After the last round the final word is absorbed and distinct query
positions are derived. Each query opens one coset duet per layer with a Merkle path and the
verifier recomputes `foldDuetExt2` along the trajectory down to the final word. -/

/-- Hash used for Merkle leaves and nodes of the succinct model. -/
def pcsMerkleHash : Hash := cshake256Bytes "QSAG.AGG.SUCCINCT.MERKLE/v1".toUTF8.toList

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

/-- Root recomputed from a node, its index and the sibling path. -/
def merklePathRoot (H : Hash) : List UInt8 → Nat → List (List UInt8) → List UInt8
  | node, _, [] => node
  | node, idx, sib :: rest => merklePathRoot H (H (merkleNodeFrame idx node sib)) (idx / 2) rest

/-- Two equally long paths from different nodes at the same index to the same root contain a
    collision of `H`, located constructively. -/
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

def encodeExt2 (x : GoldilocksExt2) : List UInt8 := be 8 x.c0.val ++ be 8 x.c1.val

theorem encodeExt2_injective {x y : GoldilocksExt2} (h : encodeExt2 x = encodeExt2 y) : x = y := by
  have hb : goldilocksPrime < 256 ^ 8 := by decide
  have hsplit := List.append_inj h (by rw [length_be, length_be])
  have h0 := be_injective (Nat.lt_trans x.c0.isLt hb) (Nat.lt_trans y.c0.isLt hb) hsplit.1
  have h1 := be_injective (Nat.lt_trans x.c1.isLt hb) (Nat.lt_trans y.c1.isLt hb) hsplit.2
  exact GoldilocksExt2.ext (Goldilocks.ext h0) (Goldilocks.ext h1)

/-- Leaf preimage of the coset duet `(v0, v1)` of group `g` in fold layer `layer`. -/
def duetLeafFrame (layer g : Nat) (v0 v1 : GoldilocksExt2) : List UInt8 :=
  encodeMultiFrame [(toString layer).toUTF8.toList, (toString g).toUTF8.toList,
    encodeExt2 v0, encodeExt2 v1]

theorem duetLeafFrame_injective {layer g : Nat} {v0 v1 t0 t1 : GoldilocksExt2}
    (h : duetLeafFrame layer g v0 v1 = duetLeafFrame layer g t0 t1) : v0 = t0 ∧ v1 = t1 := by
  have h1 := (List.cons.inj (encodeMultiFrame_injective h)).2
  have h2 := (List.cons.inj h1).2
  have h3 := List.cons.inj h2
  exact ⟨encodeExt2_injective h3.1, encodeExt2_injective (List.cons.inj h3.2).1⟩

/-- Two authenticated openings of the same leaf position with different duets give a collision. -/
def duetOpeningCollision (layer g : Nat) (v0 v1 t0 t1 : GoldilocksExt2)
    (p1 p2 : List (List UInt8)) (root : List UInt8)
    (hne : ¬ (v0 = t0 ∧ v1 = t1)) (hlen : p1.length = p2.length)
    (h1 : merklePathRoot pcsMerkleHash (pcsMerkleHash (duetLeafFrame layer g v0 v1)) g p1 = root)
    (h2 : merklePathRoot pcsMerkleHash (pcsMerkleHash (duetLeafFrame layer g t0 t1)) g p2 = root) :
    HashCollisionWitness pcsMerkleHash :=
  if hH : pcsMerkleHash (duetLeafFrame layer g v0 v1) = pcsMerkleHash (duetLeafFrame layer g t0 t1) then
    ⟨duetLeafFrame layer g v0 v1, duetLeafFrame layer g t0 t1,
      fun h => hne (duetLeafFrame_injective h), hH⟩
  else
    merklePathCollision pcsMerkleHash p1 p2 _ _ g hlen hH (h1.trans h2.symm)

def merkleDepthFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n ≤ 1 then 0 else merkleDepthFuel fuel (n / 2) + 1

/-- Path length of a Merkle tree with `n` leaves. -/
def merkleDepth (n : Nat) : Nat := merkleDepthFuel n n

/-- Public description of the folding domain. `invTwoY0 layer g` is the inverse twiddle
    `(2 * y0)^-1` of coset group `g` in layer `layer` (`inv_two * inv_y0`, `pcs.rs:971`). -/
structure FoldDomain where
  groups0 : Nat
  numQueries : Nat
  invTwo : Goldilocks
  invTwoY0 : Nat → Nat → Goldilocks
  sampleFuel : Nat

structure FoldLayerOpening where
  v0 : GoldilocksExt2
  v1 : GoldilocksExt2
  path : List (List UInt8)

structure QueryOpening where
  index : Nat
  layers : List FoldLayerOpening

/-- Succinct certificate: `agg.traceCommitment` is the layer-0 Merkle root; no signature is opened. -/
structure SuccinctAggregateProof where
  agg : AggregatedSignature
  layerRoots : List (List UInt8)
  finalWord : List GoldilocksExt2
  queries : List QueryOpening

def succinctRoots (proof : SuccinctAggregateProof) : List (List UInt8) :=
  proof.agg.traceCommitment :: proof.layerRoots

/-- Round `j` challenge: derived after absorbing the layer-`j` root and the round polynomial. -/
def deriveInterleavedChallenges (prior : List UInt8) :
    List (List UInt8) → List (List GoldilocksExt2) → List GoldilocksExt2
  | root :: roots, p :: ps =>
    let frame := encodeMultiFrame [prior, root, encodeRoundPoly p]
    let bytes := cshake256Bytes "QSAG.AGG.SUCCINCT.FS/v1".toUTF8.toList frame
    let natOf := fun bs : List UInt8 => bs.foldl (fun n b => 256 * n + b.toNat) 0
    let r : GoldilocksExt2 := ⟨Goldilocks.ofNat (natOf (bytes.take 16)),
      Goldilocks.ofNat (natOf (bytes.drop 16))⟩
    r :: deriveInterleavedChallenges frame roots ps
  | _, _ => []

def interleavedTranscriptTail (prior : List UInt8) :
    List (List UInt8) → List (List GoldilocksExt2) → List UInt8
  | root :: roots, p :: ps =>
    interleavedTranscriptTail (encodeMultiFrame [prior, root, encodeRoundPoly p]) roots ps
  | _, _ => prior

/-- Query seed: the whole interleaved transcript followed by the final word. -/
def succinctQuerySeed (fsTranscript : List UInt8) (proof : SuccinctAggregateProof) : List UInt8 :=
  encodeMultiFrame [interleavedTranscriptTail fsTranscript (succinctRoots proof) proof.agg.roundPolys,
    encodeRoundPoly proof.finalWord]

def sortedInsertDistinct (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys else if x = y then y :: ys else y :: sortedInsertDistinct x ys

/-- Rejection sampling into a sorted set until it holds `target` distinct indices
    (`sample_pcs_queries`, `pcs.rs:36-45`). -/
def sampleDistinctLoop (cand : Nat → Nat) (target : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, k, acc =>
    if target ≤ acc.length then acc
    else sampleDistinctLoop cand target fuel (k + 1) (sortedInsertDistinct (cand k) acc)

def squeezeQueryIndex (seed : List UInt8) (groups k : Nat) : Nat :=
  ((cshake256Bytes "QSAG.AGG.SUCCINCT.QUERY/v1".toUTF8.toList
    (encodeMultiFrame [seed, (toString k).toUTF8.toList])).take 8).foldl
      (fun n b => 256 * n + b.toNat) 0 % groups

def deriveQueryIndices (dom : FoldDomain) (seed : List UInt8) : List Nat :=
  sampleDistinctLoop (squeezeQueryIndex seed dom.groups0) (min dom.numQueries dom.groups0)
    dom.sampleFuel 0 []

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
    · rw [e]
      exact hxz
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

/-- The value folded from the previous layer must sit in the right slot of the opened duet. -/
def expectedSlotOk (expected : Option GoldilocksExt2) (slot : Nat) (v0 v1 : GoldilocksExt2) : Bool :=
  match expected with
  | none => true
  | some e => decide ((if slot = 0 then v0 else v1) = e)

def finalValueOk (finalWord : List GoldilocksExt2) (idx : Nat)
    (expected : Option GoldilocksExt2) : Bool :=
  match expected with
  | none => false
  | some e => decide (finalWord[idx]? = some e)

/-- One query trajectory: Merkle-authenticated duet per layer, fold check between layers
    (`pcs.rs:1717-1744`), final-word check (`pcs.rs:1764-1768`). `groups` halves per layer. -/
def verifyTrajectory (dom : FoldDomain) (finalWord : List GoldilocksExt2) :
    Nat → Nat → Nat → Option GoldilocksExt2 → List (List UInt8) → List GoldilocksExt2 →
      List FoldLayerOpening → Bool
  | _, _, idx, expected, [], [], [] => finalValueOk finalWord idx expected
  | layer, groups, idx, expected, root :: roots, α :: αs, op :: ops =>
    decide (0 < groups) &&
    expectedSlotOk expected (idx / groups) op.v0 op.v1 &&
    decide (op.path.length = merkleDepth groups) &&
    decide (merklePathRoot pcsMerkleHash
      (pcsMerkleHash (duetLeafFrame layer (idx % groups) op.v0 op.v1)) (idx % groups) op.path = root) &&
    verifyTrajectory dom finalWord (layer + 1) (groups / 2) (idx % groups)
      (some (foldDuetExt2 op.v0 op.v1 (dom.invTwoY0 layer (idx % groups)) dom.invTwo α))
      roots αs ops
  | _, _, _, _, _, _, _ => false

/-- Public data of the row arithmetization. `terminal` is what the verifier computes from the
    final word; the other fields describe the honest prover and the witness decoding and are used
    only by the extractor. -/
structure RowArithmetization where
  decodeSigs : List GoldilocksExt2 → List PqHashSig
  honestClaim : List GoldilocksExt2 → GoldilocksExt2
  honestRound : List GoldilocksExt2 → List GoldilocksExt2 → List GoldilocksExt2
  terminal : List GoldilocksExt2 → List GoldilocksExt2 → GoldilocksExt2
  isRound0Codeword : List GoldilocksExt2 → Bool
  isFinalCodeword : List GoldilocksExt2 → Bool

/-- Succinct verifier. It never sees a signature.

    Deviations from `basefold_verify_with_kernel_fn` (`pcs.rs:1529`) and `verify_leaf_shard`
    (`arithmetize.rs:1092`): one interleaved degree-8 sumcheck instead of a 16-round row sumcheck
    followed by a 17-round degree-2 PCS sumcheck linked through claimed column evaluations;
    arity-2 folding with one committed layer per variable instead of arity-16 groups; the final
    word is supplied and checked by `arith.isFinalCodeword` instead of being Reed–Solomon encoded
    from early-stop evaluations; the batching challenges, the proof-of-work nonce, leaf salts,
    canopy caps and Merkle multiproof deduplication are not modelled. -/
def verifySuccinctAggregate (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fsTranscript : List UInt8) : Bool :=
  decide (fsTranscript = aggregateInstanceFrame inst proof.agg) &&
  decide ((succinctRoots proof).length = proof.agg.roundPolys.length) &&
  decide (proof.agg.challenges =
    deriveInterleavedChallenges fsTranscript (succinctRoots proof) proof.agg.roundPolys) &&
  verifyAggregateAlgebra inst.committee proof.agg &&
  decide (proof.agg.terminalEval = arith.terminal proof.finalWord proof.agg.challenges) &&
  arith.isFinalCodeword proof.finalWord &&
  decide (proof.queries.map (fun q => q.index) =
    deriveQueryIndices dom (succinctQuerySeed fsTranscript proof)) &&
  strictlyIncreasing (proof.queries.map (fun q => q.index)) &&
  decide (proof.queries.length = min dom.numQueries dom.groups0) &&
  proof.queries.all (fun q => decide (q.index < dom.groups0) &&
    verifyTrajectory dom proof.finalWord 0 dom.groups0 q.index none (succinctRoots proof)
      proof.agg.challenges q.layers)

theorem succinct_acceptance_facts (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (h : verifySuccinctAggregate arith dom inst proof fs = true) :
    fs = aggregateInstanceFrame inst proof.agg ∧
    proof.agg.challenges =
      deriveInterleavedChallenges fs (succinctRoots proof) proof.agg.roundPolys ∧
    verifyAggregateAlgebra inst.committee proof.agg = true ∧
    proof.agg.terminalEval = arith.terminal proof.finalWord proof.agg.challenges ∧
    arith.isFinalCodeword proof.finalWord = true ∧
    proof.queries.map (fun q => q.index) =
      deriveQueryIndices dom (succinctQuerySeed fs proof) ∧
    strictlyIncreasing (proof.queries.map (fun q => q.index)) = true ∧
    proof.queries.length = min dom.numQueries dom.groups0 ∧
    proof.queries.all (fun q => decide (q.index < dom.groups0) &&
      verifyTrajectory dom proof.finalWord 0 dom.groups0 q.index none (succinctRoots proof)
        proof.agg.challenges q.layers) = true := by
  unfold verifySuccinctAggregate at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h, h10⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, h9⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, h8⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, h7⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, h6⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, h5⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, h4⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, h3⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h1, _⟩
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h3, h4, of_decide_eq_true h5, h6,
    of_decide_eq_true h7, h8, of_decide_eq_true h9, h10⟩

theorem verifyAggregateAlgebra_facts (committee : List PqPublicKey) (agg : AggregatedSignature)
    (h : verifyAggregateAlgebra committee agg = true) :
    agg.bitmap.length = committee.length ∧ agg.claimedSum = GoldilocksExt2.zero ∧
    verifySumcheckChain agg.claimedSum agg.roundPolys agg.challenges agg.terminalEval = true := by
  unfold verifyAggregateAlgebra at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h, hChain⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, hZero⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨hLen, _⟩
  exact ⟨eq_of_beq hLen, eq_of_beq hZero, hChain⟩

/-- Accepted query positions are pairwise distinct and in range. -/
theorem succinct_accepted_queries_distinct (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (h : verifySuccinctAggregate arith dom inst proof fs = true) :
    (proof.queries.map (fun q => q.index)).Nodup ∧
    (proof.queries.map (fun q => q.index)).length = min dom.numQueries dom.groups0 := by
  have hF := succinct_acceptance_facts arith dom inst proof fs h
  refine ⟨strictlyIncreasing_nodup _ hF.2.2.2.2.2.2.1, ?_⟩
  rw [List.length_map]
  exact hF.2.2.2.2.2.2.2.1

/-! ### Committed tables and the deterministic query-phase reduction -/

/-- The trajectory of round-0 group `idx` read from committed layer tables instead of openings. -/
def tableTrajectoryOk (dom : FoldDomain) (finalWord : List GoldilocksExt2) :
    Nat → Nat → Nat → Option GoldilocksExt2 → List (List GoldilocksExt2) →
      List GoldilocksExt2 → Bool
  | _, _, idx, expected, [], [] => finalValueOk finalWord idx expected
  | layer, groups, idx, expected, w :: ws, α :: αs =>
    decide (0 < groups) &&
    expectedSlotOk expected (idx / groups)
      (w.getD (idx % groups) CommRingOps.zero) (w.getD (idx % groups + groups) CommRingOps.zero) &&
    tableTrajectoryOk dom finalWord (layer + 1) (groups / 2) (idx % groups)
      (some (foldDuetExt2 (w.getD (idx % groups) CommRingOps.zero)
        (w.getD (idx % groups + groups) CommRingOps.zero)
        (dom.invTwoY0 layer (idx % groups)) dom.invTwo α)) ws αs
  | _, _, _, _, _, _ => false

/-- The layer tables are what the Merkle roots commit to: every leaf of every layer has an
    authentication path to the corresponding root. These are equations between hash values. -/
def LayersBound (authPath : Nat → Nat → List (List UInt8)) :
    Nat → Nat → List (List GoldilocksExt2) → List (List UInt8) → Prop
  | _, _, [], [] => True
  | layer, groups, w :: ws, root :: roots =>
    (∀ g, g < groups →
      merklePathRoot pcsMerkleHash
        (pcsMerkleHash (duetLeafFrame layer g (w.getD g CommRingOps.zero)
          (w.getD (g + groups) CommRingOps.zero))) g (authPath layer g) = root ∧
      (authPath layer g).length = merkleDepth groups) ∧
    LayersBound authPath (layer + 1) (groups / 2) ws roots
  | _, _, _, _ => False

/-- An accepted trajectory either reads exactly the committed tables or exhibits a collision. -/
def trajectorySound (dom : FoldDomain) (finalWord : List GoldilocksExt2)
    (authPath : Nat → Nat → List (List UInt8)) :
    ∀ (roots : List (List UInt8)) (αs : List GoldilocksExt2) (ops : List FoldLayerOpening)
      (tables : List (List GoldilocksExt2)) (layer groups idx : Nat)
      (expected : Option GoldilocksExt2),
      verifyTrajectory dom finalWord layer groups idx expected roots αs ops = true →
      LayersBound authPath layer groups tables roots →
      PSum (HashCollisionWitness pcsMerkleHash)
        (PLift (tableTrajectoryOk dom finalWord layer groups idx expected tables αs = true))
  | [], [], [], [], _, _, _, _, hV, _ => .inr ⟨hV⟩
  | [], [], [], _ :: _, _, _, _, _, _, hB => False.elim hB
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, hB => False.elim hB
  | [], [], _ :: _, _, _, _, _, _, hV, _ => False.elim (by simp [verifyTrajectory] at hV)
  | [], _ :: _, ops, _, _, _, _, _, hV, _ =>
    False.elim (by cases ops <;> simp [verifyTrajectory] at hV)
  | _ :: _, [], ops, _, _, _, _, _, hV, _ =>
    False.elim (by cases ops <;> simp [verifyTrajectory] at hV)
  | _ :: _, _ :: _, [], _, _, _, _, _, hV, _ => False.elim (by simp [verifyTrajectory] at hV)
  | root :: roots, α :: αs, op :: ops, w :: ws, layer, groups, idx, expected, hV, hB =>
    have hU : 0 < groups ∧ expectedSlotOk expected (idx / groups) op.v0 op.v1 = true ∧
        op.path.length = merkleDepth groups ∧
        merklePathRoot pcsMerkleHash
          (pcsMerkleHash (duetLeafFrame layer (idx % groups) op.v0 op.v1))
          (idx % groups) op.path = root ∧
        verifyTrajectory dom finalWord (layer + 1) (groups / 2) (idx % groups)
          (some (foldDuetExt2 op.v0 op.v1 (dom.invTwoY0 layer (idx % groups)) dom.invTwo α))
          roots αs ops = true := by
      have h : (decide (0 < groups) &&
          expectedSlotOk expected (idx / groups) op.v0 op.v1 &&
          decide (op.path.length = merkleDepth groups) &&
          decide (merklePathRoot pcsMerkleHash
            (pcsMerkleHash (duetLeafFrame layer (idx % groups) op.v0 op.v1))
            (idx % groups) op.path = root) &&
          verifyTrajectory dom finalWord (layer + 1) (groups / 2) (idx % groups)
            (some (foldDuetExt2 op.v0 op.v1 (dom.invTwoY0 layer (idx % groups)) dom.invTwo α))
            roots αs ops) = true := hV
      rcases Bool.and_eq_true_iff.mp h with ⟨h, h5⟩
      rcases Bool.and_eq_true_iff.mp h with ⟨h, h4⟩
      rcases Bool.and_eq_true_iff.mp h with ⟨h, h3⟩
      rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
      exact ⟨of_decide_eq_true h1, h2, of_decide_eq_true h3, of_decide_eq_true h4, h5⟩
    have hBg := hB.1 (idx % groups) (Nat.mod_lt _ hU.1)
    if hEq : op.v0 = w.getD (idx % groups) CommRingOps.zero ∧
        op.v1 = w.getD (idx % groups + groups) CommRingOps.zero then
      match trajectorySound dom finalWord authPath roots αs ops ws (layer + 1) (groups / 2)
          (idx % groups) _ hU.2.2.2.2 hB.2 with
      | .inl c => .inl c
      | .inr ⟨hT⟩ => .inr ⟨by
          show (decide (0 < groups) &&
            expectedSlotOk expected (idx / groups)
              (w.getD (idx % groups) CommRingOps.zero)
              (w.getD (idx % groups + groups) CommRingOps.zero) &&
            tableTrajectoryOk dom finalWord (layer + 1) (groups / 2) (idx % groups)
              (some (foldDuetExt2 (w.getD (idx % groups) CommRingOps.zero)
                (w.getD (idx % groups + groups) CommRingOps.zero)
                (dom.invTwoY0 layer (idx % groups)) dom.invTwo α)) ws αs) = true
          rw [← hEq.1, ← hEq.2]
          exact Bool.and_eq_true_iff.mpr
            ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hU.1, hU.2.1⟩, hT⟩⟩
    else
      .inl (duetOpeningCollision layer (idx % groups) op.v0 op.v1 _ _ op.path
        (authPath layer (idx % groups)) root hEq (hU.2.2.1.trans hBg.2.symm) hU.2.2.2.1 hBg.1)

/-- All accepted queries read the committed tables, or a collision is exhibited. -/
def queriesSound (dom : FoldDomain) (finalWord : List GoldilocksExt2)
    (authPath : Nat → Nat → List (List UInt8)) (roots : List (List UInt8))
    (αs : List GoldilocksExt2) (tables : List (List GoldilocksExt2)) :
    ∀ (qs : List QueryOpening),
      qs.all (fun q => decide (q.index < dom.groups0) &&
        verifyTrajectory dom finalWord 0 dom.groups0 q.index none roots αs q.layers) = true →
      LayersBound authPath 0 dom.groups0 tables roots →
      PSum (HashCollisionWitness pcsMerkleHash)
        (PLift (∀ q ∈ qs, q.index < dom.groups0 ∧
          tableTrajectoryOk dom finalWord 0 dom.groups0 q.index none tables αs = true))
  | [], _, _ => .inr ⟨fun _ hq => by cases hq⟩
  | q :: qs, hAll, hB =>
    have hSplit : (decide (q.index < dom.groups0) &&
          verifyTrajectory dom finalWord 0 dom.groups0 q.index none roots αs q.layers) = true ∧
        qs.all (fun q => decide (q.index < dom.groups0) &&
          verifyTrajectory dom finalWord 0 dom.groups0 q.index none roots αs q.layers) = true :=
      Bool.and_eq_true_iff.mp hAll
    have hq := Bool.and_eq_true_iff.mp hSplit.1
    match trajectorySound dom finalWord authPath roots αs q.layers tables 0 dom.groups0
        q.index none hq.2 hB with
    | .inl c => .inl c
    | .inr ⟨h1⟩ =>
      match queriesSound dom finalWord authPath roots αs tables qs hSplit.2 hB with
      | .inl c => .inl c
      | .inr ⟨h2⟩ => .inr ⟨fun q' hq' => by
          rcases List.mem_cons.mp hq' with e | e
          · rw [e]
            exact ⟨of_decide_eq_true hq.1, h1⟩
          · exact h2 q' e⟩

/-- Constructive bounded search for the first index below `n` on which `ok` fails. -/
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
            rw [hEq]
            exact h⟩
      else .inl ⟨n, Nat.lt_succ_self n, Bool.eq_false_iff.mpr h⟩

/-! ### Break witnesses of the query phase -/

/-- The committed tables are inconsistent along the trajectory of an identified round-0 group,
    yet every Fiat–Shamir-sampled (pairwise distinct) query position has a consistent trajectory.
    `basefold_query_miss_bound` counts the query tuples for which this can happen, as a function
    of how many round-0 groups are inconsistent.

    On its own this is not a rare event: corrupting a single unqueried position produces it. It
    is rare only when the inconsistent set is dense; the unique-decoding argument that a sparse
    inconsistent set leaves the extracted witness unchanged is not carried out in this file. -/
structure BaseFoldQueryMiss (dom : FoldDomain) (finalWord : List GoldilocksExt2)
    (tables : List (List GoldilocksExt2)) (challenges : List GoldilocksExt2)
    (queryIndices : List Nat) where
  badIndex : Nat
  badIndex_lt : badIndex < dom.groups0
  bad : tableTrajectoryOk dom finalWord 0 dom.groups0 badIndex none tables challenges = false
  queries_distinct : queryIndices.Nodup
  queries_count : queryIndices.length = min dom.numQueries dom.groups0
  queries_good : ∀ i ∈ queryIndices, i < dom.groups0 ∧
    tableTrajectoryOk dom finalWord 0 dom.groups0 i none tables challenges = true

/-- The committed round-0 table is not a codeword, yet under the Fiat–Shamir folding challenges
    every trajectory of the committed tables folds consistently into a final codeword. This is the
    proximity-gap failure event; its probability is NOT bounded in this file. -/
structure FoldProximityHit (arith : RowArithmetization) (dom : FoldDomain)
    (finalWord : List GoldilocksExt2) (tables : List (List GoldilocksExt2))
    (challenges : List GoldilocksExt2) where
  round0_not_codeword : arith.isRound0Codeword (tables.headD []) = false
  final_in_code : arith.isFinalCodeword finalWord = true
  all_consistent : ∀ i, i < dom.groups0 →
    tableTrajectoryOk dom finalWord 0 dom.groups0 i none tables challenges = true

/-- Obligations on a row arithmetization. `complete`: for a round-0 codeword whose committed
    layers fold consistently everywhere, the honest sumcheck chain verifies against the terminal
    value computed from the final word. `sound`: a decoded witness that fails signature
    verification for an active signer has a nonzero constraint sum.

    No instance for the production AIR (`trace.rs`) is constructed here, and `sound` as stated
    has no batching-failure alternative, which a production instance would need. -/
structure RowArithmetization.Lawful (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) : Prop where
  complete : ∀ (tables : List (List GoldilocksExt2)) (challenges finalWord : List GoldilocksExt2),
    arith.isRound0Codeword (tables.headD []) = true →
    (∀ i, i < dom.groups0 →
      tableTrajectoryOk dom finalWord 0 dom.groups0 i none tables challenges = true) →
    verifySumcheckChain (arith.honestClaim (tables.headD []))
      (adaptivePolys (arith.honestRound (tables.headD [])) challenges) challenges
      (arith.terminal finalWord challenges) = true
  sound : ∀ (table0 : List GoldilocksExt2) (bitmap : SignerBitmapSpec),
    bitmap.length = inst.committee.length →
    checkAllActiveSigners inst.suite inst.params inst.message inst.committee bitmap
      (arith.decodeSigs table0) = false →
    arith.honestClaim table0 ≠ GoldilocksExt2.zero

/-- What the extractor reads from the prover's hash queries: the committed layer tables and an
    authentication path for every leaf. -/
structure SuccinctExtractionView where
  tables : List (List GoldilocksExt2)
  authPath : Nat → Nat → List (List UInt8)

/-- Result of extraction: valid signatures for all active signers, or one of four
    transcript-indexed break witnesses. -/
@[expose] def SuccinctOutcome (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof)
    (view : SuccinctExtractionView) : Type :=
  PSum { _u : Unit // checkAllActiveSigners inst.suite inst.params inst.message inst.committee
      proof.agg.bitmap (arith.decodeSigs (view.tables.headD [])) = true }
    (PSum (SumcheckSchwartzZippelHit proof.agg.roundPolys
        (adaptivePolys (arith.honestRound (view.tables.headD [])) proof.agg.challenges)
        proof.agg.challenges)
      (PSum (HashCollisionWitness pcsMerkleHash)
        (PSum (BaseFoldQueryMiss dom proof.finalWord view.tables proof.agg.challenges
            (proof.queries.map (fun q => q.index)))
          (FoldProximityHit arith dom proof.finalWord view.tables proof.agg.challenges))))

/-- **Knowledge soundness of the succinct aggregate verifier, relative to a lawful row
    arithmetization.** From an accepting certificate (challenges and query positions derived by
    Fiat–Shamir) and the committed tables behind its Merkle roots, the extractor returns valid
    signatures for every active signer, or a Schwartz–Zippel hit at an identified sumcheck
    round, or a Merkle hash collision, or an identified inconsistent trajectory missed by all
    sampled queries, or a proximity-gap hit of the folding challenges. -/
def succinct_aggregation_knowledge_soundness (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : LayersBound view.authPath 0 dom.groups0 view.tables (succinctRoots proof)) :
    SuccinctOutcome arith dom inst proof view :=
  have hF := succinct_acceptance_facts arith dom inst proof fs hAccept
  match queriesSound dom proof.finalWord view.authPath (succinctRoots proof) proof.agg.challenges
      view.tables proof.queries hF.2.2.2.2.2.2.2.2 hBound with
  | .inl c => .inr (.inr (.inl c))
  | .inr ⟨hQ⟩ =>
    match firstFailBelow (fun i => tableTrajectoryOk dom proof.finalWord 0 dom.groups0 i none
        view.tables proof.agg.challenges) dom.groups0 with
    | .inl ⟨i, hi, hbad⟩ =>
      .inr (.inr (.inr (.inl
        { badIndex := i
          badIndex_lt := hi
          bad := hbad
          queries_distinct := strictlyIncreasing_nodup _ hF.2.2.2.2.2.2.1
          queries_count := by
            rw [List.length_map]
            exact hF.2.2.2.2.2.2.2.1
          queries_good := fun j hj => by
            obtain ⟨q, hq, hEq⟩ := List.mem_map.mp hj
            rw [← hEq]
            exact hQ q hq })))
    | .inr ⟨hAll⟩ =>
      if hCode : arith.isRound0Codeword (view.tables.headD []) = true then
        if hSigs : checkAllActiveSigners inst.suite inst.params inst.message inst.committee
            proof.agg.bitmap (arith.decodeSigs (view.tables.headD [])) = true then
          .inl ⟨(), hSigs⟩
        else
          have hAlg := verifyAggregateAlgebra_facts inst.committee proof.agg hF.2.2.1
          have hHon := law.complete view.tables proof.agg.challenges proof.finalWord hCode hAll
          have hNz := law.sound (view.tables.headD []) proof.agg.bitmap hAlg.1
            (Bool.eq_false_iff.mpr hSigs)
          .inr (.inl (extractSumcheckHitFromChain proof.agg.roundPolys proof.agg.claimedSum
            (arith.honestClaim (view.tables.headD []))
            (adaptivePolys (arith.honestRound (view.tables.headD [])) proof.agg.challenges)
            proof.agg.challenges proof.agg.terminalEval
            (by rw [hAlg.2.1]; exact fun h => hNz h.symm) hAlg.2.2
            (by rw [hF.2.2.2.1]; exact hHon)))
      else
        .inr (.inr (.inr (.inr
          { round0_not_codeword := Bool.eq_false_iff.mpr hCode
            final_in_code := hF.2.2.2.2.1
            all_consistent := hAll })))

/-- Per-signer form: a verifying signature of active signer `i`, or a break witness. -/
def succinct_aggregation_signer_extraction (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : LayersBound view.authPath 0 dom.groups0 view.tables (succinctRoots proof))
    (i : Nat) (hi : i < inst.committee.length) (hb : i < proof.agg.bitmap.length)
    (active : proof.agg.bitmap[i]'hb = true) :
    PSum { sig : PqHashSig //
        verifyPqHashSig inst.suite inst.params (inst.committee[i]'hi) inst.message sig = true }
      (PSum (SumcheckSchwartzZippelHit proof.agg.roundPolys
          (adaptivePolys (arith.honestRound (view.tables.headD [])) proof.agg.challenges)
          proof.agg.challenges)
        (PSum (HashCollisionWitness pcsMerkleHash)
          (PSum (BaseFoldQueryMiss dom proof.finalWord view.tables proof.agg.challenges
              (proof.queries.map (fun q => q.index)))
            (FoldProximityHit arith dom proof.finalWord view.tables proof.agg.challenges)))) :=
  match succinct_aggregation_knowledge_soundness arith dom inst law proof fs view hAccept hBound with
  | .inl ⟨_, hAll⟩ =>
    .inl (extractActiveSignerSig inst.suite inst.params inst.message inst.committee
      proof.agg.bitmap _ i hi hb hAll active)
  | .inr brk => .inr brk

/-! ## 11. Recursive merge trees -/

/-- Property of an accepted reference merge tree: at every node the opened signatures verify for
    every active signer, and every branch is a disjoint union of its children. -/
def mergeTreeAllSound (inst : AggPublicInstance) : MergeNode → Prop
  | .leaf agg sigs _ =>
    checkAllActiveSigners inst.suite inst.params inst.message inst.committee agg.bitmap sigs = true
  | .branch agg sigs _ left right =>
    checkAllActiveSigners inst.suite inst.params inst.message inst.committee agg.bitmap sigs = true ∧
    bitmapDisjointSpec left.certificate.bitmap right.certificate.bitmap = true ∧
    agg.bitmap = bitmapUnionSpec left.certificate.bitmap right.certificate.bitmap ∧
    mergeTreeAllSound inst left ∧ mergeTreeAllSound inst right

/-- Induction over the reference merge tree accepted by `verifyMergeTree`. Unconditional: the
    reference verifier opens every signature at every node. -/
theorem merge_tree_all_nodes_sound (inst : AggPublicInstance) :
    ∀ (budget : Nat) (tree : MergeNode),
      verifyMergeTree inst budget tree = true → mergeTreeAllSound inst tree
  | 0, _, h => False.elim (Bool.false_ne_true h)
  | _ + 1, .leaf agg sigs fs, h =>
    aggregate_opened_signatures_sound inst agg sigs fs (Bool.and_eq_true_iff.mp h).2
  | budget + 1, .branch agg sigs fs left right, h => by
    have h' : (decide (agg.childrenCommitment =
          some (left.certificate.traceCommitment, right.certificate.traceCommitment)) &&
        verifyMergeTree inst budget left && verifyMergeTree inst budget right &&
        bitmapDisjointSpec left.certificate.bitmap right.certificate.bitmap &&
        decide (agg.bitmap = bitmapUnionSpec left.certificate.bitmap right.certificate.bitmap) &&
        verifyAggregatedSignature inst agg sigs fs) = true := h
    rcases Bool.and_eq_true_iff.mp h' with ⟨h', hNode⟩
    rcases Bool.and_eq_true_iff.mp h' with ⟨h', hUnion⟩
    rcases Bool.and_eq_true_iff.mp h' with ⟨h', hDisj⟩
    rcases Bool.and_eq_true_iff.mp h' with ⟨h', hRight⟩
    rcases Bool.and_eq_true_iff.mp h' with ⟨_, hLeft⟩
    exact ⟨aggregate_opened_signatures_sound inst agg sigs fs hNode, hDisj,
      of_decide_eq_true hUnion, merge_tree_all_nodes_sound inst budget left hLeft,
      merge_tree_all_nodes_sound inst budget right hRight⟩

/-- Merge tree of succinct certificates (same shape as `MergeNode`, without opened signatures). -/
inductive SuccinctMergeNode where
  | leaf (proof : SuccinctAggregateProof) (transcript : List UInt8)
  | branch (proof : SuccinctAggregateProof) (transcript : List UInt8)
      (left right : SuccinctMergeNode)

def SuccinctMergeNode.proof : SuccinctMergeNode → SuccinctAggregateProof
  | .leaf p _ => p
  | .branch p _ _ _ => p

/-- `verifyMergeTree` with every node checked by `verifySuccinctAggregate`. -/
def verifySuccinctMergeTree (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) : Nat → SuccinctMergeNode → Bool
  | 0, _ => false
  | _ + 1, .leaf p fs =>
    p.agg.childrenCommitment.isNone && verifySuccinctAggregate arith dom inst p fs
  | budget + 1, .branch p fs left right =>
    decide (p.agg.childrenCommitment =
      some (left.proof.agg.traceCommitment, right.proof.agg.traceCommitment)) &&
    verifySuccinctMergeTree arith dom inst budget left &&
    verifySuccinctMergeTree arith dom inst budget right &&
    bitmapDisjointSpec left.proof.agg.bitmap right.proof.agg.bitmap &&
    decide (p.agg.bitmap = bitmapUnionSpec left.proof.agg.bitmap right.proof.agg.bitmap) &&
    verifySuccinctAggregate arith dom inst p fs

/-- One extraction view per node of the merge tree. -/
inductive SuccinctViewTree where
  | leaf (view : SuccinctExtractionView)
  | branch (view : SuccinctExtractionView) (left right : SuccinctViewTree)

def ViewTreeBound (dom : FoldDomain) : SuccinctMergeNode → SuccinctViewTree → Prop
  | .leaf p _, .leaf v => LayersBound v.authPath 0 dom.groups0 v.tables (succinctRoots p)
  | .branch p _ left right, .branch v vl vr =>
    LayersBound v.authPath 0 dom.groups0 v.tables (succinctRoots p) ∧
    ViewTreeBound dom left vl ∧ ViewTreeBound dom right vr
  | _, _ => False

/-- An outcome at every node of the tree. -/
@[expose] def SuccinctTreeOutcome (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) : SuccinctMergeNode → SuccinctViewTree → Type
  | .leaf p _, .leaf v => SuccinctOutcome arith dom inst p v
  | .branch p _ left right, .branch v vl vr =>
    SuccinctOutcome arith dom inst p v × SuccinctTreeOutcome arith dom inst left vl ×
      SuccinctTreeOutcome arith dom inst right vr
  | _, _ => PUnit

theorem succinct_merge_tree_children_sound (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (budget : Nat) (p : SuccinctAggregateProof) (fs : List UInt8)
    (left right : SuccinctMergeNode)
    (h : verifySuccinctMergeTree arith dom inst (budget + 1) (.branch p fs left right) = true) :
    verifySuccinctMergeTree arith dom inst budget left = true ∧
    verifySuccinctMergeTree arith dom inst budget right = true ∧
    p.agg.childrenCommitment =
      some (left.proof.agg.traceCommitment, right.proof.agg.traceCommitment) ∧
    bitmapDisjointSpec left.proof.agg.bitmap right.proof.agg.bitmap = true ∧
    p.agg.bitmap = bitmapUnionSpec left.proof.agg.bitmap right.proof.agg.bitmap ∧
    verifySuccinctAggregate arith dom inst p fs = true := by
  have h' : (decide (p.agg.childrenCommitment =
        some (left.proof.agg.traceCommitment, right.proof.agg.traceCommitment)) &&
      verifySuccinctMergeTree arith dom inst budget left &&
      verifySuccinctMergeTree arith dom inst budget right &&
      bitmapDisjointSpec left.proof.agg.bitmap right.proof.agg.bitmap &&
      decide (p.agg.bitmap = bitmapUnionSpec left.proof.agg.bitmap right.proof.agg.bitmap) &&
      verifySuccinctAggregate arith dom inst p fs) = true := h
  rcases Bool.and_eq_true_iff.mp h' with ⟨h', hNode⟩
  rcases Bool.and_eq_true_iff.mp h' with ⟨h', hUnion⟩
  rcases Bool.and_eq_true_iff.mp h' with ⟨h', hDisj⟩
  rcases Bool.and_eq_true_iff.mp h' with ⟨h', hRight⟩
  rcases Bool.and_eq_true_iff.mp h' with ⟨hComm, hLeft⟩
  exact ⟨hLeft, hRight, of_decide_eq_true hComm, hDisj, of_decide_eq_true hUnion, hNode⟩

/-- **Knowledge soundness of the recursive succinct merge verifier**, by induction over the tree:
    every node of an accepted tree yields valid signatures for all of its active signers or one
    of the transcript-indexed break witnesses of that node. -/
def succinct_merge_tree_knowledge_soundness (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst) :
    ∀ (budget : Nat) (node : SuccinctMergeNode) (views : SuccinctViewTree),
      verifySuccinctMergeTree arith dom inst budget node = true →
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

/-! ## 12. Total counted soundness error -/

private theorem length_flatMap_scaled_le {α β : Type} (b : α → Bool) (K U V : Nat)
    (f : α → List β) :
    ∀ (l : List α), (∀ c ∈ l, (f c).length * K ≤ if b c = true then U else V) →
      (l.flatMap f).length * K ≤ (l.filter b).length * U + l.length * V
  | [], _ => by
    show 0 * K ≤ _
    rw [Nat.zero_mul]
    exact Nat.zero_le _
  | c :: l, h => by
    have ih := length_flatMap_scaled_le b K U V f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc := h c (List.mem_cons_self ..)
    rw [List.flatMap_cons, List.length_append, Nat.add_mul, List.length_cons,
      Nat.add_mul l.length 1 V, Nat.one_mul]
    cases hb : b c
    · rw [hb] at hc
      have hc' : (f c).length * K ≤ V := hc
      simp only [List.filter, hb]
      omega
    · rw [hb] at hc
      have hc' : (f c).length * K ≤ U := hc
      simp only [List.filter, hb, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- Pairs (challenge vector, tuple of distinct query positions) on which a round event occurs
    or every query misses the bad set determined by the challenge vector. -/
def badTranscriptPairs {α β : Type} (S : List α) (n : Nat) (E : List α → α → Bool)
    (dom : List β) (q : Nat) (bad : List α → β → Bool) : List (List α × List β) :=
  (challengeVectors S n).flatMap (fun cs =>
    ((distinctTuples q dom).filter
      (fun t => anyRoundEvent E cs || t.all (fun x => !bad cs x))).map (fun t => (cs, t)))

/-- **Joint count.** Round events bounded per round by `d`, and a bad set of relative size at
    least `dn / dd` whenever no round event occurs: the bad (challenge vector, query tuple)
    pairs are at most the sum of the challenge term and the query term. -/
theorem transcript_bad_pairs_le {α β : Type} (S : List α) (n : Nat)
    (E : List α → α → Bool) (d : Nat → Nat)
    (hE : ∀ pre, (S.filter (E pre)).length ≤ d pre.length)
    (dom : List β) (q dn dd : Nat) (bad : List α → β → Bool)
    (hfar : ∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
      dn * dom.length ≤ dd * countGood (bad cs) dom) :
    (badTranscriptPairs S n E dom q bad).length * dd ^ q ≤
      (roundBoundSum d n * S.length ^ (n - 1) * dd ^ q + S.length ^ n * (dd - dn) ^ q) *
        (distinctTuples q dom).length := by
  have hEach : ∀ cs ∈ challengeVectors S n,
      (((distinctTuples q dom).filter
        (fun t => anyRoundEvent E cs || t.all (fun x => !bad cs x))).map
          (fun t => (cs, t))).length * dd ^ q ≤
        if anyRoundEvent E cs = true then (distinctTuples q dom).length * dd ^ q
        else (dd - dn) ^ q * (distinctTuples q dom).length := by
    intro cs hcs
    rw [List.length_map]
    cases hEv : anyRoundEvent E cs
    · show ((distinctTuples q dom).filter
        (fun t => t.all (fun x => !bad cs x))).length * dd ^ q ≤
          (dd - dn) ^ q * (distinctTuples q dom).length
      exact basefold_query_miss_bound (bad cs) dom q dn dd (hfar cs hcs hEv)
    · exact Nat.mul_le_mul_right _ (filter_length_le_self _ _)
  have hSplit := length_flatMap_scaled_le (anyRoundEvent E) (dd ^ q)
    ((distinctTuples q dom).length * dd ^ q) ((dd - dn) ^ q * (distinctTuples q dom).length)
    (fun cs => ((distinctTuples q dom).filter
      (fun t => anyRoundEvent E cs || t.all (fun x => !bad cs x))).map (fun t => (cs, t)))
    (challengeVectors S n) hEach
  have hCnt := anyRoundEvent_count_le S n E d hE
  rw [challengeVectors_length] at hSplit
  refine Nat.le_trans hSplit ?_
  rw [Nat.add_mul]
  apply Nat.add_le_add
  · have h1 := Nat.mul_le_mul_right ((distinctTuples q dom).length * dd ^ q) hCnt
    have e : roundBoundSum d n * S.length ^ (n - 1) * ((distinctTuples q dom).length * dd ^ q) =
        roundBoundSum d n * S.length ^ (n - 1) * dd ^ q * (distinctTuples q dom).length := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [e] at h1
    exact h1
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
      rw [← e1]
      exact Nat.mul_le_mul_left _ h1
    have h2 : 2 * (D * c) * (A * K * T) ≤ K * (s * A * T) := by
      have h := Nat.mul_le_mul_right (A * K * T) hD
      have e : s * (A * K * T) = K * (s * A * T) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      rw [e] at h
      exact h
    have h3 : 2 * (M * c) * (s * A * T) < K * (s * A * T) := Nat.mul_lt_mul_of_pos_right hM hP
    have h4 : 2 * (K * (s * A * T)) ≤ 2 * c * (X * K) := by
      have h := Nat.mul_le_mul_left (2 * K) hge
      have e : 2 * K * (X * c) = 2 * c * (X * K) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e, Nat.mul_assoc] at h
      exact h
    have h5 := Nat.lt_of_le_of_lt (Nat.le_trans h4 h1') (Nat.add_lt_add_of_le_of_lt h2 h3)
    rw [Nat.two_mul] at h5
    exact Nat.lt_irrefl _ h5

/-- Budget of per-round challenge events for the production schedule: 16 row-sumcheck rounds of
    degree 8, then 17 folding rounds each carrying a degree-2 sumcheck polynomial and one tracked
    fold event per position of the largest evaluation domain (`2^28`). -/
def productionRoundEventBudget : Nat :=
  productionAggParams.maxRowRounds * productionAggParams.rowSumcheckDegree +
  productionAggParams.maxFoldRounds *
    (productionAggParams.pcsSumcheckDegree + productionAggParams.maxDomain)

theorem productionRoundEventBudget_eq : productionRoundEventBudget = 16 * 8 + 17 * (2 + 2 ^ 28) := by
  decide

/-- Sumcheck-only budget: 16 row-sumcheck rounds of degree 8 and 17 PCS-sumcheck rounds of
    degree 2, with no tracked fold event. -/
def productionSumcheckEventBudget : Nat :=
  productionAggParams.maxRowRounds * productionAggParams.rowSumcheckDegree +
  productionAggParams.maxFoldRounds * productionAggParams.pcsSumcheckDegree

private theorem error_bound_general {α β : Type} (S : List α) (n : Nat)
    (hn : 0 < n) (E : List α → α → Bool) (d : Nat → Nat)
    (hE : ∀ pre, (S.filter (E pre)).length ≤ d pre.length)
    (budget c : Nat) (hBudget : roundBoundSum d n ≤ budget)
    (hC : 2 * (budget * c) ≤ goldilocksPrime ^ 2)
    (hM : 2 * ((2 * productionAggParams.rsBlowup - (productionAggParams.rsBlowup - 1)) ^
      productionAggParams.numQueries * c) <
      (2 * productionAggParams.rsBlowup) ^ productionAggParams.numQueries)
    (hField : productionAggParams.fieldSize ≤ S.length)
    (dom : List β) (hdom : productionAggParams.numQueries ≤ dom.length)
    (bad : List α → β → Bool)
    (hfar : ∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
      (productionAggParams.rsBlowup - 1) * dom.length ≤
        2 * productionAggParams.rsBlowup * countGood (bad cs) dom) :
    (badTranscriptPairs S n E dom productionAggParams.numQueries bad).length * c <
      S.length ^ n * (distinctTuples productionAggParams.numQueries dom).length := by
  have hJoint := transcript_bad_pairs_le S n E d hE dom productionAggParams.numQueries
    (productionAggParams.rsBlowup - 1) (2 * productionAggParams.rsBlowup) bad hfar
  have hT : 0 < (distinctTuples productionAggParams.numQueries dom).length := by
    rw [distinctTuples_length]
    exact fallingFactorial_pos _ _ hdom
  have hField' : goldilocksPrime ^ 2 ≤ S.length := hField
  have hs : 0 < S.length := Nat.lt_of_lt_of_le (by decide : 0 < goldilocksPrime ^ 2) hField'
  have hD : 2 * (roundBoundSum d n * c) ≤ S.length :=
    Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right c hBudget))
      (Nat.le_trans hC hField')
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ k =>
    have hpow : S.length ^ (k + 1) = S.length * S.length ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [Nat.add_sub_cancel, hpow] at hJoint
    rw [hpow]
    exact error_arith _ _ _ _ _ _ _ _ hJoint hD hM (Nat.pow_pos hs) hT hs

/-- **Total counted soundness error with the production parameters.** Over a challenge set at
    least as large as `GoldilocksExt2`, with per-round challenge events within
    `productionRoundEventBudget`, 160 distinct queries, and a bad query set of relative size at
    least `15/32` whenever no challenge event occurs, fewer than a `2^-93` fraction of all
    (challenge vector, query tuple) pairs are bad: the challenge term is below `2^-94` and the
    query term below `2^-145`.

    This counts the sumcheck hits, the tracked fold hits and the query misses. The density
    hypothesis `hfar` (distance preservation of folding) is an assumption here, and the
    `FoldProximityHit` branch of the extractor is not covered by this count. -/
theorem succinct_aggregation_soundness_error_bound {α β : Type} (S : List α) (n : Nat)
    (hn : 0 < n) (E : List α → α → Bool) (d : Nat → Nat)
    (hE : ∀ pre, (S.filter (E pre)).length ≤ d pre.length)
    (hBudget : roundBoundSum d n ≤ productionRoundEventBudget)
    (hField : productionAggParams.fieldSize ≤ S.length)
    (dom : List β) (hdom : productionAggParams.numQueries ≤ dom.length)
    (bad : List α → β → Bool)
    (hfar : ∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
      (productionAggParams.rsBlowup - 1) * dom.length ≤
        2 * productionAggParams.rsBlowup * countGood (bad cs) dom) :
    (badTranscriptPairs S n E dom productionAggParams.numQueries bad).length * 2 ^ 93 <
      S.length ^ n * (distinctTuples productionAggParams.numQueries dom).length :=
  error_bound_general S n hn E d hE productionRoundEventBudget (2 ^ 93) hBudget (by decide)
    (by decide) hField dom hdom bad hfar

/-- The same count with sumcheck hits only (`productionSumcheckEventBudget`, no tracked fold
    event): the bad fraction is below `2^-119`. -/
theorem succinct_aggregation_sumcheck_query_error_bound {α β : Type} (S : List α) (n : Nat)
    (hn : 0 < n) (E : List α → α → Bool) (d : Nat → Nat)
    (hE : ∀ pre, (S.filter (E pre)).length ≤ d pre.length)
    (hBudget : roundBoundSum d n ≤ productionSumcheckEventBudget)
    (hField : productionAggParams.fieldSize ≤ S.length)
    (dom : List β) (hdom : productionAggParams.numQueries ≤ dom.length)
    (bad : List α → β → Bool)
    (hfar : ∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
      (productionAggParams.rsBlowup - 1) * dom.length ≤
        2 * productionAggParams.rsBlowup * countGood (bad cs) dom) :
    (badTranscriptPairs S n E dom productionAggParams.numQueries bad).length * 2 ^ 119 <
      S.length ^ n * (distinctTuples productionAggParams.numQueries dom).length :=
  error_bound_general S n hn E d hE productionSumcheckEventBudget (2 ^ 119) hBudget (by decide)
    (by decide) hField dom hdom bad hfar

/-! ## 13. Inhabitedness witnesses and negative regressions -/

/-- The query-bound hypotheses are satisfiable, tightly: 160 positions of which exactly 75 are
    bad is relative distance exactly `15/32`. -/
theorem basefold_query_hypotheses_satisfiable :
    ∃ (dom : List Nat) (bad : Nat → Bool),
      productionAggParams.numQueries ≤ dom.length ∧
      (productionAggParams.rsBlowup - 1) * dom.length ≤
        2 * productionAggParams.rsBlowup * countGood bad dom ∧
      countGood bad dom < dom.length :=
  ⟨List.range 160, fun i => decide (i < 75), by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- The hypotheses of the total error bound are jointly satisfiable. -/
theorem succinct_error_bound_hypotheses_satisfiable :
    ∃ (S : List Unit) (n : Nat) (E : List Unit → Unit → Bool) (d : Nat → Nat)
      (dom : List Nat) (bad : List Unit → Nat → Bool),
      0 < n ∧ (∀ pre, (S.filter (E pre)).length ≤ d pre.length) ∧
      roundBoundSum d n ≤ productionRoundEventBudget ∧
      productionAggParams.fieldSize ≤ S.length ∧
      productionAggParams.numQueries ≤ dom.length ∧
      (∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
        (productionAggParams.rsBlowup - 1) * dom.length ≤
          2 * productionAggParams.rsBlowup * countGood (bad cs) dom) := by
  refine ⟨List.replicate (goldilocksPrime ^ 2) (), 1, fun _ _ => false, fun _ => 0,
    List.range 160, fun _ i => decide (i < 75), Nat.one_pos, ?_, by decide, ?_, by decide +kernel,
    fun _ _ _ => (by decide +kernel :
      (productionAggParams.rsBlowup - 1) * (List.range 160).length ≤
        2 * productionAggParams.rsBlowup *
          countGood (fun i => decide (i < 75)) (List.range 160))⟩
  · intro pre
    rw [filter_const_false]
    exact Nat.le_refl 0
  · rw [List.length_replicate]
    exact Nat.le_refl _

theorem foldDuetExt2_zero_zero (invTwoY0 invTwo : Goldilocks) (r : GoldilocksExt2) :
    foldDuetExt2 CommRingOps.zero CommRingOps.zero invTwoY0 invTwo r = CommRingOps.zero := by
  unfold foldDuetExt2
  simp only [LawfulCommRing.add_zero, LawfulCommRing.sub_self, LawfulCommRing.zero_mul,
    LawfulCommRing.mul_zero]

private def toyDomain (invTwo twY : Goldilocks) : FoldDomain :=
  { groups0 := 1, numQueries := 160, invTwo := invTwo, invTwoY0 := fun _ _ => twY, sampleFuel := 1 }

private def toyPoly (invTwo twY : Goldilocks) (t : List GoldilocksExt2) : List GoldilocksExt2 :=
  [CommRingOps.mul (CommRingOps.add (t.getD 0 CommRingOps.zero) (t.getD 1 CommRingOps.zero))
      (GoldilocksExt2.ofBase invTwo),
   CommRingOps.mul (CommRingOps.sub (t.getD 0 CommRingOps.zero) (t.getD 1 CommRingOps.zero))
      (GoldilocksExt2.ofBase twY)]

private def toyClaim (invTwo twY : Goldilocks) (t : List GoldilocksExt2) : GoldilocksExt2 :=
  CommRingOps.add (RoundPoly.evalCoeffs (toyPoly invTwo twY t) GoldilocksExt2.zero)
    (RoundPoly.evalCoeffs (toyPoly invTwo twY t) GoldilocksExt2.one)

/-- Toy arithmetization over a two-point domain (one coset duet, one fold): the committed word
    encodes the affine polynomial `W`; the constraint is `W(0) + W(1) = 0`, and the committed
    word decodes to `sigA` exactly when the constraint holds. -/
private def toyArith (invTwo twY : Goldilocks) (sigA sigB : PqHashSig) : RowArithmetization :=
  { decodeSigs := fun t => [if toyClaim invTwo twY t = GoldilocksExt2.zero then sigA else sigB]
    honestClaim := toyClaim invTwo twY
    honestRound := fun t _ => toyPoly invTwo twY t
    terminal := fun fw _ => fw.getD 0 CommRingOps.zero
    isRound0Codeword := fun _ => true
    isFinalCodeword := fun _ => true }

private def toyInst (suite : TweakableHashSuite) (params : PqHashParams) (msg : List UInt8)
    (pk : PqPublicKey) : AggPublicInstance :=
  { suite := suite, params := params, message := msg, committee := [pk], signingModeDigest := [] }

private theorem toyArith_lawful (invTwo twY : Goldilocks) (suite : TweakableHashSuite)
    (params : PqHashParams) (msg : List UInt8) (pk : PqPublicKey) (sigA sigB : PqHashSig)
    (hA : verifyPqHashSig suite params pk msg sigA = true) :
    (toyArith invTwo twY sigA sigB).Lawful (toyDomain invTwo twY) (toyInst suite params msg pk) where
  complete := by
    intro tables challenges finalWord _ hAll
    have h0 : tableTrajectoryOk (toyDomain invTwo twY) finalWord 0 1 0 none tables challenges =
        true := hAll 0 Nat.one_pos
    cases tables with
    | nil => cases challenges <;> exact absurd h0 Bool.false_ne_true
    | cons w ws =>
      cases challenges with
      | nil => exact absurd h0 Bool.false_ne_true
      | cons α αs =>
        cases ws with
        | cons w2 ws2 => cases αs <;> exact absurd h0 Bool.false_ne_true
        | nil =>
          cases αs with
          | cons α2 αs2 => exact absurd h0 Bool.false_ne_true
          | nil =>
            have h0' : (decide (0 < 1) &&
                expectedSlotOk none (0 / 1) (w.getD 0 CommRingOps.zero) (w.getD 1 CommRingOps.zero) &&
                finalValueOk finalWord 0 (some (foldDuetExt2 (w.getD 0 CommRingOps.zero)
                  (w.getD 1 CommRingOps.zero) twY invTwo α))) = true := h0
            have hfw : finalWord[0]? = some (foldDuetExt2 (w.getD 0 CommRingOps.zero)
                (w.getD 1 CommRingOps.zero) twY invTwo α) :=
              of_decide_eq_true (Bool.and_eq_true_iff.mp h0').2
            have h3 : RoundPoly.evalCoeffs (toyPoly invTwo twY w) α =
                finalWord.getD 0 CommRingOps.zero := by
              rw [List.getD_eq_getElem?_getD, hfw, Option.getD_some]
              unfold toyPoly
              rw [evalCoeffs_pair]
              rfl
            show (decide ((toyPoly invTwo twY w).length ≤ 9) &&
              (CommRingOps.add (RoundPoly.evalCoeffs (toyPoly invTwo twY w) GoldilocksExt2.zero)
                (RoundPoly.evalCoeffs (toyPoly invTwo twY w) GoldilocksExt2.one) ==
                toyClaim invTwo twY w) &&
              (RoundPoly.evalCoeffs (toyPoly invTwo twY w) α ==
                finalWord.getD 0 CommRingOps.zero)) = true
            exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl, beq_iff_eq.mpr rfl⟩,
              beq_iff_eq.mpr h3⟩
  sound := by
    intro table0 bitmap hlen hfalse hz
    have hz' : toyClaim invTwo twY table0 = GoldilocksExt2.zero := hz
    have hdec : (toyArith invTwo twY sigA sigB).decodeSigs table0 = [sigA] := by
      show [if toyClaim invTwo twY table0 = GoldilocksExt2.zero then sigA else sigB] = [sigA]
      simp only [hz', ↓reduceIte]
    rw [hdec] at hfalse
    have hlen' : bitmap.length = 1 := hlen
    cases bitmap with
    | nil => exact absurd hlen' Nat.zero_ne_one
    | cons b bs =>
      cases bs with
      | cons b2 bs2 => exact Nat.succ_ne_zero _ (Nat.succ.inj hlen')
      | nil =>
        have hfalse' : ((if b = true then verifyPqHashSig suite params pk msg sigA else true) &&
            true) = false := hfalse
        rw [hA] at hfalse'
        cases b <;> cases hfalse'

private def toyRoot0 : List UInt8 :=
  pcsMerkleHash (duetLeafFrame 0 0 CommRingOps.zero CommRingOps.zero)

private def toyAggPre (suite : TweakableHashSuite) (params : PqHashParams) : AggregatedSignature :=
  { suite := suite, params := params, bitmap := [true], signerCount := 1,
    traceCommitment := toyRoot0, claimedSum := GoldilocksExt2.zero,
    roundPolys := [[GoldilocksExt2.zero]], challenges := [], terminalEval := CommRingOps.zero }

private def toyFs (inst : AggPublicInstance) : List UInt8 :=
  aggregateInstanceFrame inst (toyAggPre inst.suite inst.params)

private def toyOpening : FoldLayerOpening :=
  { v0 := CommRingOps.zero, v1 := CommRingOps.zero, path := [] }

private def toyQuery : QueryOpening := { index := 0, layers := [toyOpening] }

private def toyAgg (inst : AggPublicInstance) : AggregatedSignature :=
  { suite := inst.suite, params := inst.params, bitmap := [true], signerCount := 1,
    traceCommitment := toyRoot0, claimedSum := GoldilocksExt2.zero,
    roundPolys := [[GoldilocksExt2.zero]],
    challenges := deriveInterleavedChallenges (toyFs inst) [toyRoot0] [[GoldilocksExt2.zero]],
    terminalEval := CommRingOps.zero }

private def toyProof (inst : AggPublicInstance) : SuccinctAggregateProof :=
  { agg := toyAgg inst, layerRoots := [], finalWord := [CommRingOps.zero], queries := [toyQuery] }

private def toyView : SuccinctExtractionView :=
  { tables := [[CommRingOps.zero, CommRingOps.zero]], authPath := fun _ _ => [] }

private theorem toyProof_accepts (invTwo twY : Goldilocks) (suite : TweakableHashSuite)
    (params : PqHashParams) (msg : List UInt8) (pk : PqPublicKey) (sigA sigB : PqHashSig) :
    verifySuccinctAggregate (toyArith invTwo twY sigA sigB) (toyDomain invTwo twY)
      (toyInst suite params msg pk) (toyProof (toyInst suite params msg pk))
      (toyFs (toyInst suite params msg pk)) = true := by
  obtain ⟨r, hr⟩ : ∃ r, deriveInterleavedChallenges (toyFs (toyInst suite params msg pk))
      [toyRoot0] [[GoldilocksExt2.zero]] = [r] := ⟨_, rfl⟩
  have hChain : verifySumcheckChain GoldilocksExt2.zero [[GoldilocksExt2.zero]] [r]
      GoldilocksExt2.zero = true := verifySumcheckChain_zeroPolys [r]
  have c4 : verifyAggregateAlgebra [pk] (toyProof (toyInst suite params msg pk)).agg = true := by
    show verifySumcheckChain GoldilocksExt2.zero [[GoldilocksExt2.zero]]
      (deriveInterleavedChallenges (toyFs (toyInst suite params msg pk)) [toyRoot0]
        [[GoldilocksExt2.zero]]) GoldilocksExt2.zero = true
    rw [hr]
    exact hChain
  have c7 : [0] = deriveQueryIndices (toyDomain invTwo twY)
      (succinctQuerySeed (toyFs (toyInst suite params msg pk))
        (toyProof (toyInst suite params msg pk))) := by
    show [0] = [squeezeQueryIndex _ 1 0]
    unfold squeezeQueryIndex
    rw [Nat.mod_one]
  have hFinal : finalValueOk [CommRingOps.zero] 0
      (some (foldDuetExt2 CommRingOps.zero CommRingOps.zero twY invTwo r)) = true := by
    rw [foldDuetExt2_zero_zero]
    exact decide_eq_true rfl
  have hTraj : verifyTrajectory (toyDomain invTwo twY) [CommRingOps.zero] 0 1 0 none
      [toyRoot0] [r]
      [toyOpening] = true := by
    show (decide (0 < 1) &&
      expectedSlotOk none (0 / 1) CommRingOps.zero CommRingOps.zero &&
      decide (([] : List (List UInt8)).length = merkleDepth 1) &&
      decide (merklePathRoot pcsMerkleHash
        (pcsMerkleHash (duetLeafFrame 0 0 CommRingOps.zero CommRingOps.zero)) 0 [] = toyRoot0) &&
      finalValueOk [CommRingOps.zero] 0
        (some (foldDuetExt2 CommRingOps.zero CommRingOps.zero twY invTwo r))) = true
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true Nat.one_pos, rfl⟩, decide_eq_true rfl⟩,
      decide_eq_true rfl⟩, hFinal⟩
  have c10 : (toyProof (toyInst suite params msg pk)).queries.all (fun q =>
      decide (q.index < (toyDomain invTwo twY).groups0) &&
      verifyTrajectory (toyDomain invTwo twY) (toyProof (toyInst suite params msg pk)).finalWord 0
        (toyDomain invTwo twY).groups0 q.index none
        (succinctRoots (toyProof (toyInst suite params msg pk)))
        (toyProof (toyInst suite params msg pk)).agg.challenges q.layers) = true := by
    show (decide (0 < 1) &&
      verifyTrajectory (toyDomain invTwo twY) [CommRingOps.zero] 0 1 0 none [toyRoot0]
        (deriveInterleavedChallenges (toyFs (toyInst suite params msg pk)) [toyRoot0]
          [[GoldilocksExt2.zero]])
        [toyOpening] && true) = true
    rw [hr, hTraj]
    rfl
  have mk : ∀ {a b : Bool}, a = true → b = true → (a && b) = true :=
    fun ha hb => Bool.and_eq_true_iff.mpr ⟨ha, hb⟩
  exact mk (mk (mk (mk (mk (mk (mk (mk (mk (decide_eq_true rfl) (decide_eq_true rfl))
    (decide_eq_true rfl)) c4) (decide_eq_true rfl)) rfl) (decide_eq_true c7)) rfl)
    (decide_eq_true rfl)) c10

private theorem toyView_bound (inst : AggPublicInstance) (invTwo twY : Goldilocks) :
    LayersBound toyView.authPath 0 (toyDomain invTwo twY).groups0 toyView.tables
      (succinctRoots (toyProof inst)) := by
  refine ⟨fun g hg => ?_, trivial⟩
  have hg' : g < 1 := hg
  cases g with
  | zero => exact ⟨rfl, rfl⟩
  | succ k => exact absurd (Nat.lt_of_succ_lt_succ hg') (Nat.not_lt_zero k)

/-- Inhabitedness of the knowledge-soundness hypotheses: given one verifying signature there are a
    lawful arithmetization, an accepting succinct certificate and a bound extraction view. -/
theorem succinct_knowledge_soundness_hypotheses_satisfiable (suite : TweakableHashSuite)
    (params : PqHashParams) (msg : List UInt8) (pk : PqPublicKey) (sigA : PqHashSig)
    (hA : verifyPqHashSig suite params pk msg sigA = true) :
    ∃ (arith : RowArithmetization) (dom : FoldDomain) (inst : AggPublicInstance)
      (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView),
      arith.Lawful dom inst ∧
      verifySuccinctAggregate arith dom inst proof fs = true ∧
      LayersBound view.authPath 0 dom.groups0 view.tables (succinctRoots proof) ∧
      verifySuccinctMergeTree arith dom inst 1 (.leaf proof fs) = true ∧
      ViewTreeBound dom (.leaf proof fs) (.leaf view) :=
  ⟨toyArith (Goldilocks.ofNat 3) (Goldilocks.ofNat 5) sigA sigA,
    toyDomain (Goldilocks.ofNat 3) (Goldilocks.ofNat 5), toyInst suite params msg pk,
    toyProof (toyInst suite params msg pk), toyFs (toyInst suite params msg pk), toyView,
    toyArith_lawful _ _ suite params msg pk sigA sigA hA,
    toyProof_accepts _ _ suite params msg pk sigA sigA,
    toyView_bound _ _ _,
    Bool.and_eq_true_iff.mpr ⟨rfl, toyProof_accepts _ _ suite params msg pk sigA sigA⟩,
    toyView_bound _ _ _⟩

/-- Regression: a round polynomial with ten or more coefficients (degree nine) is rejected by the
    succinct verifier. -/
theorem succinct_degree9_round_rejected (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (p : List GoldilocksExt2) (ps : List (List GoldilocksExt2))
    (hPolys : proof.agg.roundPolys = p :: ps) (hDeg : 9 < p.length) :
    verifySuccinctAggregate arith dom inst proof fs = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hAlg := verifyAggregateAlgebra_facts inst.committee proof.agg
    (succinct_acceptance_facts arith dom inst proof fs h).2.2.1
  have hChain := hAlg.2.2
  rw [hPolys] at hChain
  cases hc : proof.agg.challenges with
  | nil =>
    rw [hc] at hChain
    exact Bool.false_ne_true hChain
  | cons r rs =>
    rw [hc, sumcheck_degree9_rejected _ _ p ps r rs hDeg] at hChain
    exact Bool.false_ne_true hChain

/-- Regression: a wrong folded value against the final word is rejected. -/
theorem trajectory_wrong_final_fold_rejected (dom : FoldDomain) (finalWord : List GoldilocksExt2)
    (layer groups idx : Nat) (expected : Option GoldilocksExt2) (root : List UInt8)
    (α : GoldilocksExt2) (op : FoldLayerOpening)
    (hWrong : finalWord[idx % groups]? ≠
      some (foldDuetExt2 op.v0 op.v1 (dom.invTwoY0 layer (idx % groups)) dom.invTwo α)) :
    verifyTrajectory dom finalWord layer groups idx expected [root] [α] [op] = false := by
  show (decide (0 < groups) && expectedSlotOk expected (idx / groups) op.v0 op.v1 &&
    decide (op.path.length = merkleDepth groups) &&
    decide (merklePathRoot pcsMerkleHash
      (pcsMerkleHash (duetLeafFrame layer (idx % groups) op.v0 op.v1)) (idx % groups) op.path =
        root) &&
    decide (finalWord[idx % groups]? =
      some (foldDuetExt2 op.v0 op.v1 (dom.invTwoY0 layer (idx % groups)) dom.invTwo α))) = false
  rw [decide_eq_false hWrong]
  exact Bool.and_false _

/-- Regression: an opened duet whose slot does not carry the value folded from the previous
    layer is rejected. -/
theorem trajectory_wrong_intermediate_fold_rejected (dom : FoldDomain)
    (finalWord : List GoldilocksExt2) (layer groups idx : Nat) (e : GoldilocksExt2)
    (root : List UInt8) (roots : List (List UInt8)) (α : GoldilocksExt2)
    (αs : List GoldilocksExt2) (op : FoldLayerOpening) (ops : List FoldLayerOpening)
    (hWrong : (if idx / groups = 0 then op.v0 else op.v1) ≠ e) :
    verifyTrajectory dom finalWord layer groups idx (some e) (root :: roots) (α :: αs)
      (op :: ops) = false := by
  show (decide (0 < groups) &&
    decide ((if idx / groups = 0 then op.v0 else op.v1) = e) &&
    decide (op.path.length = merkleDepth groups) &&
    decide (merklePathRoot pcsMerkleHash
      (pcsMerkleHash (duetLeafFrame layer (idx % groups) op.v0 op.v1)) (idx % groups) op.path =
        root) &&
    verifyTrajectory dom finalWord (layer + 1) (groups / 2) (idx % groups)
      (some (foldDuetExt2 op.v0 op.v1 (dom.invTwoY0 layer (idx % groups)) dom.invTwo α))
      roots αs ops) = false
  rw [decide_eq_false hWrong, Bool.and_false, Bool.false_and, Bool.false_and, Bool.false_and]

/-- Regression: a certificate that repeats a query position is rejected. -/
theorem succinct_duplicate_query_rejected (arith : RowArithmetization) (dom : FoldDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hDup : ¬ (proof.queries.map (fun q => q.index)).Nodup) :
    verifySuccinctAggregate arith dom inst proof fs = false :=
  Bool.eq_false_iff.mpr
    (fun h => hDup (succinct_accepted_queries_distinct arith dom inst proof fs h).1)

/-- Regression: a concrete repeated position fails the distinctness check. -/
theorem strictlyIncreasing_rejects_repeat (i : Nat) (rest : List Nat) :
    strictlyIncreasing (i :: i :: rest) = false := by
  show (decide (i < i) && strictlyIncreasing (i :: rest)) = false
  rw [decide_eq_false (Nat.lt_irrefl i)]
  rfl

end Qsag
end
