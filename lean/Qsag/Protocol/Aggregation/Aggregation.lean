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
import all Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
import all Qsag.Oracle.Keccak
public import Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HypertreeEufCma

public import Qsag.Tactic.AssuranceKit

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

/-- Quartic extension $\mathbb{F}_{p^4} = \mathbb{F}_{p^2}[v] / (v^2 - u)$ where
    $u = \texttt{GoldilocksExt2.uBasis}$ ($u^2 = 7$), matching `GoldilocksExt4` in
    `crates/qsag-agg/src/field.rs` (`|\mathbb{F}_{p^4}| = p^4 > 2^{255}`). -/
structure GoldilocksExt4 where
  c0 : GoldilocksExt2
  c1 : GoldilocksExt2
  deriving DecidableEq, Repr

namespace GoldilocksExt4

def nonResidue : GoldilocksExt2 := GoldilocksExt2.uBasis

theorem ext {x y : GoldilocksExt4} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; simp only at h0 h1; subst h0 h1; rfl

def ofExt2 (a : GoldilocksExt2) : GoldilocksExt4 := ⟨a, CommRingOps.zero⟩
def embedBase (a : Goldilocks) : GoldilocksExt4 := ofExt2 (GoldilocksExt2.ofBase a)
def zero : GoldilocksExt4 := ⟨CommRingOps.zero, CommRingOps.zero⟩
def one : GoldilocksExt4 := ⟨CommRingOps.one, CommRingOps.zero⟩
def vBasis : GoldilocksExt4 := ⟨CommRingOps.zero, CommRingOps.one⟩

instance : Inhabited GoldilocksExt4 := ⟨zero⟩

@[simp] theorem ofExt2_c0 (a : GoldilocksExt2) : (ofExt2 a).c0 = a := by rfl
@[simp] theorem ofExt2_c1 (a : GoldilocksExt2) : (ofExt2 a).c1 = CommRingOps.zero := by rfl
@[simp] theorem embedBase_c0_c0 (a : Goldilocks) : (embedBase a).c0.c0 = a := by rfl

def add (x y : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.add x.c0 y.c0, CommRingOps.add x.c1 y.c1⟩

def neg (x : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.neg x.c0, CommRingOps.neg x.c1⟩

def sub (x y : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.sub x.c0 y.c0, CommRingOps.sub x.c1 y.c1⟩

def mul (x y : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.add (CommRingOps.mul x.c0 y.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)),
   CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)⟩

instance : CommRingOps GoldilocksExt4 where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub

instance : LawfulCommRing GoldilocksExt4 where
  add_assoc x y z := by
    exact ext (LawfulCommRing.add_assoc x.c0 y.c0 z.c0)
      (LawfulCommRing.add_assoc x.c1 y.c1 z.c1)
  add_comm x y := by
    exact ext (LawfulCommRing.add_comm x.c0 y.c0)
      (LawfulCommRing.add_comm x.c1 y.c1)
  zero_add x := by
    exact ext (LawfulCommRing.zero_add x.c0) (LawfulCommRing.zero_add x.c1)
  add_zero x := by
    exact ext (LawfulCommRing.add_zero x.c0) (LawfulCommRing.add_zero x.c1)
  add_left_neg x := by
    exact ext (LawfulCommRing.add_left_neg x.c0) (LawfulCommRing.add_left_neg x.c1)
  sub_eq_add_neg x y := by
    exact ext (LawfulCommRing.sub_eq_add_neg x.c0 y.c0)
      (LawfulCommRing.sub_eq_add_neg x.c1 y.c1)
  mul_comm x y := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 y.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) =
        CommRingOps.add (CommRingOps.mul y.c0 x.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 x.c1))
      rw [LawfulCommRing.mul_comm x.c0 y.c0, LawfulCommRing.mul_comm x.c1 y.c1]
    · change CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0) =
        CommRingOps.add (CommRingOps.mul y.c0 x.c1) (CommRingOps.mul y.c1 x.c0)
      rw [LawfulCommRing.mul_comm x.c0 y.c1, LawfulCommRing.mul_comm x.c1 y.c0,
          LawfulCommRing.add_comm]
  one_mul x := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul CommRingOps.one x.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul CommRingOps.zero x.c1)) = x.c0
      rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero,
          LawfulCommRing.add_zero]
    · change CommRingOps.add (CommRingOps.mul CommRingOps.one x.c1)
          (CommRingOps.mul CommRingOps.zero x.c0) = x.c1
      rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
  mul_one x := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 CommRingOps.one)
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 CommRingOps.zero)) = x.c0
      rw [LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
          LawfulCommRing.add_zero]
    · change CommRingOps.add (CommRingOps.mul x.c0 CommRingOps.zero)
          (CommRingOps.mul x.c1 CommRingOps.one) = x.c1
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.zero_add]
  left_distrib x y z := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 (CommRingOps.add y.c0 z.c0))
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.add y.c1 z.c1))) =
        CommRingOps.add
          (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)))
          (CommRingOps.add (CommRingOps.mul x.c0 z.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 z.c1)))
      rw [LawfulCommRing.left_distrib x.c0 y.c0 z.c0,
          LawfulCommRing.left_distrib x.c1 y.c1 z.c1,
          LawfulCommRing.left_distrib nonResidue (CommRingOps.mul x.c1 y.c1) (CommRingOps.mul x.c1 z.c1),
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 y.c0) (CommRingOps.mul x.c0 z.c0)]
    · change CommRingOps.add (CommRingOps.mul x.c0 (CommRingOps.add y.c1 z.c1))
          (CommRingOps.mul x.c1 (CommRingOps.add y.c0 z.c0)) =
        CommRingOps.add
          (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0))
          (CommRingOps.add (CommRingOps.mul x.c0 z.c1) (CommRingOps.mul x.c1 z.c0))
      rw [LawfulCommRing.left_distrib x.c0 y.c1 z.c1,
          LawfulCommRing.left_distrib x.c1 y.c0 z.c0,
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c0 z.c1)]
  right_distrib x y z := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c1)) =
        CommRingOps.add
          (CommRingOps.add (CommRingOps.mul x.c0 z.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 z.c1)))
          (CommRingOps.add (CommRingOps.mul y.c0 z.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)))
      rw [LawfulCommRing.right_distrib x.c0 y.c0 z.c0,
          LawfulCommRing.right_distrib x.c1 y.c1 z.c1,
          LawfulCommRing.left_distrib nonResidue (CommRingOps.mul x.c1 z.c1) (CommRingOps.mul y.c1 z.c1),
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 z.c0) (CommRingOps.mul y.c0 z.c0)]
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c1)
          (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c0) =
        CommRingOps.add
          (CommRingOps.add (CommRingOps.mul x.c0 z.c1) (CommRingOps.mul x.c1 z.c0))
          (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0))
      rw [LawfulCommRing.right_distrib x.c0 y.c0 z.c1,
          LawfulCommRing.right_distrib x.c1 y.c1 z.c0,
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 z.c1) (CommRingOps.mul y.c0 z.c1)]
  mul_assoc x y z := by
    apply ext
    · change CommRingOps.add
          (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1))) z.c0)
          (CommRingOps.mul nonResidue
            (CommRingOps.mul
              (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)) z.c1)) =
        CommRingOps.add
          (CommRingOps.mul x.c0
            (CommRingOps.add (CommRingOps.mul y.c0 z.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))))
          (CommRingOps.mul nonResidue
            (CommRingOps.mul x.c1
              (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0))))
      rw [LawfulCommRing.right_distrib (CommRingOps.mul x.c0 y.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c0,
          LawfulCommRing.right_distrib (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0) z.c1,
          LawfulCommRing.left_distrib nonResidue
            (CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c1)
            (CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c1),
          LawfulCommRing.left_distrib x.c0 (CommRingOps.mul y.c0 z.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)),
          LawfulCommRing.left_distrib x.c1 (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0),
          LawfulCommRing.left_distrib nonResidue
            (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c1))
            (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0))]
      have t1 : CommRingOps.mul (CommRingOps.mul x.c0 y.c0) z.c0 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c0) :=
        LawfulCommRing.mul_assoc x.c0 y.c0 z.c0
      have t2 : CommRingOps.mul (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c0 =
          CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0)) := by
        rw [LawfulCommRing.mul_assoc nonResidue (CommRingOps.mul x.c1 y.c1) z.c0,
            LawfulCommRing.mul_assoc x.c1 y.c1 z.c0]
      have t3 : CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c1) =
          CommRingOps.mul x.c0 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc x.c0 y.c1 z.c1,
            ← LawfulCommRing.mul_assoc nonResidue x.c0 (CommRingOps.mul y.c1 z.c1),
            LawfulCommRing.mul_comm nonResidue x.c0,
            LawfulCommRing.mul_assoc x.c0 nonResidue (CommRingOps.mul y.c1 z.c1)]
      have t4 : CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c1) =
          CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c1)) := by
        rw [LawfulCommRing.mul_assoc x.c1 y.c0 z.c1]
      rw [t1, t2, t3, t4,
          LawfulCommRing.add_add_add_comm
            (CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c0))
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0))),
          LawfulCommRing.add_comm
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0)))
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c1)))]
    · change CommRingOps.add
          (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1))) z.c1)
          (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)) z.c0) =
        CommRingOps.add
          (CommRingOps.mul x.c0
            (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0)))
          (CommRingOps.mul x.c1
            (CommRingOps.add (CommRingOps.mul y.c0 z.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))))
      rw [LawfulCommRing.right_distrib (CommRingOps.mul x.c0 y.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c1,
          LawfulCommRing.right_distrib (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0) z.c0,
          LawfulCommRing.left_distrib x.c0 (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0),
          LawfulCommRing.left_distrib x.c1 (CommRingOps.mul y.c0 z.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))]
      have s1 : CommRingOps.mul (CommRingOps.mul x.c0 y.c0) z.c1 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c1) :=
        LawfulCommRing.mul_assoc x.c0 y.c0 z.c1
      have s2 : CommRingOps.mul (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c1 =
          CommRingOps.mul x.c1 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc nonResidue (CommRingOps.mul x.c1 y.c1) z.c1,
            LawfulCommRing.mul_assoc x.c1 y.c1 z.c1,
            ← LawfulCommRing.mul_assoc nonResidue x.c1 (CommRingOps.mul y.c1 z.c1),
            LawfulCommRing.mul_comm nonResidue x.c1,
            LawfulCommRing.mul_assoc x.c1 nonResidue (CommRingOps.mul y.c1 z.c1)]
      have s3 : CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c0 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c1 z.c0) :=
        LawfulCommRing.mul_assoc x.c0 y.c1 z.c0
      have s4 : CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c0 =
          CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c0) :=
        LawfulCommRing.mul_assoc x.c1 y.c0 z.c0
      rw [s1, s2, s3, s4,
          LawfulCommRing.add_add_add_comm
            (CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c1))
            (CommRingOps.mul x.c1 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))),
          LawfulCommRing.add_comm
            (CommRingOps.mul x.c1 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)))
            (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c0))]

theorem zero_eq_ringZero : zero = CommRingOps.zero := rfl

theorem one_eq_ringOne : one = CommRingOps.one := rfl

/-- Square root of `-1` in `Goldilocks` (`(2^48)^2 = 2^96 ≡ -1 (mod p)`). -/
def sqrtNegOne : Goldilocks := ⟨2 ^ 48, by decide⟩

theorem sqrtNegOne_sq :
    CommRingOps.mul sqrtNegOne sqrtNegOne = CommRingOps.neg CommRingOps.one := by
  decide +kernel

/-- **`uBasis_not_square`**: `u = (0, 1) ∈ GoldilocksExt2` has no square root in `GoldilocksExt2`,
    so $v^2 - u$ is irreducible over $\mathbb{F}_{p^2}$. -/
theorem uBasis_not_square (z : GoldilocksExt2) :
    CommRingOps.mul z z ≠ nonResidue := by
  intro hsq
  have hc0 : CommRingOps.add (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) =
      CommRingOps.zero := congrArg GoldilocksExt2.c0 hsq
  have hc1 : CommRingOps.add (CommRingOps.mul z.c0 z.c1) (CommRingOps.mul z.c1 z.c0) =
      Goldilocks.one := congrArg GoldilocksExt2.c1 hsq
  have hbNe : z.c1 ≠ Goldilocks.zero := by
    intro hb0
    rw [hb0] at hc1
    change CommRingOps.add (CommRingOps.mul z.c0 CommRingOps.zero)
      (CommRingOps.mul CommRingOps.zero z.c0) = Goldilocks.one at hc1
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hc1
    exact absurd hc1 (by decide)
  have haSqEq : CommRingOps.mul z.c0 z.c0 =
      CommRingOps.neg (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) := by
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1))
    rw [LawfulCommRing.add_comm _ (CommRingOps.mul z.c0 z.c0), hc0,
        LawfulCommRing.add_right_neg]
  let q := CommRingOps.mul z.c0 (Goldilocks.inv z.c1)
  let w := CommRingOps.mul q sqrtNegOne
  have hqSq : CommRingOps.mul q q = CommRingOps.neg GoldilocksExt2.nonResidue := by
    dsimp only [q]
    have hassoc : CommRingOps.mul (CommRingOps.mul z.c0 (Goldilocks.inv z.c1))
        (CommRingOps.mul z.c0 (Goldilocks.inv z.c1)) =
        CommRingOps.mul (CommRingOps.mul z.c0 z.c0)
          (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) := by
      rw [LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
          ← LawfulCommRing.mul_assoc (Goldilocks.inv z.c1) z.c0 _,
          LawfulCommRing.mul_comm (Goldilocks.inv z.c1) z.c0,
          LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
          ← LawfulCommRing.mul_assoc z.c0 z.c0 _]
    have hcancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
        (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) = CommRingOps.one := by
      rw [LawfulCommRing.mul_assoc z.c1 z.c1 _,
          ← LawfulCommRing.mul_assoc z.c1 (Goldilocks.inv z.c1) _,
          Goldilocks.mul_inv_cancel hbNe, LawfulCommRing.one_mul,
          Goldilocks.mul_inv_cancel hbNe]
    rw [hassoc, haSqEq, LawfulCommRing.neg_mul,
        LawfulCommRing.mul_assoc GoldilocksExt2.nonResidue, hcancel, LawfulCommRing.mul_one]
  have hwSq : CommRingOps.mul w w = GoldilocksExt2.nonResidue := by
    dsimp only [w]
    have hassoc : CommRingOps.mul (CommRingOps.mul q sqrtNegOne) (CommRingOps.mul q sqrtNegOne) =
        CommRingOps.mul (CommRingOps.mul q q) (CommRingOps.mul sqrtNegOne sqrtNegOne) := by
      rw [LawfulCommRing.mul_assoc q sqrtNegOne _,
          ← LawfulCommRing.mul_assoc sqrtNegOne q _,
          LawfulCommRing.mul_comm sqrtNegOne q,
          LawfulCommRing.mul_assoc q sqrtNegOne _,
          ← LawfulCommRing.mul_assoc q q _]
    rw [hassoc, hqSq, sqrtNegOne_sq, LawfulCommRing.neg_mul, LawfulCommRing.mul_neg,
        LawfulCommRing.mul_one]
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.neg GoldilocksExt2.nonResidue)
    rw [LawfulCommRing.add_right_neg, LawfulCommRing.add_left_neg]
  exact GoldilocksExt2.nonResidue_not_square w hwSq

def norm (z : GoldilocksExt4) : GoldilocksExt2 :=
  CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
    (CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1))

theorem norm_ne_zero {z : GoldilocksExt4} (hz : z ≠ zero) :
    norm z ≠ GoldilocksExt2.zero := by
  intro hnorm
  change CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1)) =
      CommRingOps.zero at hnorm
  have hEq : CommRingOps.mul z.c0 z.c0 =
      CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1) :=
    LawfulCommRing.sub_eq_zero_iff.mp hnorm
  if hc1 : z.c1 = GoldilocksExt2.zero then
    have hrhs : CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1) =
        GoldilocksExt2.zero := by
      rw [hc1]
      change CommRingOps.mul nonResidue
        (CommRingOps.mul CommRingOps.zero CommRingOps.zero) = CommRingOps.zero
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero]
    rw [hrhs] at hEq
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hEq with hc0 | hc0 <;>
      exact hz (ext hc0 hc1)
  else
    let q := CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1)
    have hqSq : CommRingOps.mul q q = nonResidue := by
      dsimp only [q]
      have hassoc : CommRingOps.mul (CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1))
          (CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1)) =
          CommRingOps.mul (CommRingOps.mul z.c0 z.c0)
            (CommRingOps.mul (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1)) := by
        rw [LawfulCommRing.mul_assoc z.c0 (GoldilocksExt2.inv z.c1) _,
            ← LawfulCommRing.mul_assoc (GoldilocksExt2.inv z.c1) z.c0 _,
            LawfulCommRing.mul_comm (GoldilocksExt2.inv z.c1) z.c0,
            LawfulCommRing.mul_assoc z.c0 (GoldilocksExt2.inv z.c1) _,
            ← LawfulCommRing.mul_assoc z.c0 z.c0 _]
      rw [hassoc, hEq, LawfulCommRing.mul_assoc nonResidue]
      have hcancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
          (CommRingOps.mul (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1)) =
          CommRingOps.one := by
        rw [LawfulCommRing.mul_assoc z.c1 z.c1 _,
            ← LawfulCommRing.mul_assoc z.c1 (GoldilocksExt2.inv z.c1) _,
            GoldilocksExt2.mul_inv_cancel hc1, LawfulCommRing.one_mul,
            GoldilocksExt2.mul_inv_cancel hc1]
      rw [hcancel, LawfulCommRing.mul_one]
    exact uBasis_not_square q hqSq

/-- Constructive field inverse in `GoldilocksExt4` (`inv 0 = 0`). -/
def inv (z : GoldilocksExt4) : GoldilocksExt4 :=
  let invN := GoldilocksExt2.inv (norm z)
  ⟨CommRingOps.mul z.c0 invN, CommRingOps.neg (CommRingOps.mul z.c1 invN)⟩

theorem mul_inv_cancel {z : GoldilocksExt4} (hz : z ≠ zero) :
    CommRingOps.mul z (inv z) = CommRingOps.one := by
  have hnormNe := norm_ne_zero hz
  let invN := GoldilocksExt2.inv (norm z)
  apply ext
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.mul z.c0 invN))
        (CommRingOps.mul nonResidue
          (CommRingOps.mul z.c1 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))) =
      CommRingOps.one
    rw [← LawfulCommRing.mul_assoc z.c0 z.c0 invN,
        LawfulCommRing.mul_neg z.c1, LawfulCommRing.mul_neg nonResidue,
        ← LawfulCommRing.mul_assoc z.c1 z.c1 invN,
        ← LawfulCommRing.mul_assoc nonResidue _ invN,
        ← LawfulCommRing.sub_eq_add_neg,
        ← LawfulCommRing.sub_mul]
    exact GoldilocksExt2.mul_inv_cancel hnormNe
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))
        (CommRingOps.mul z.c1 (CommRingOps.mul z.c0 invN)) =
      CommRingOps.zero
    rw [LawfulCommRing.mul_neg,
        ← LawfulCommRing.mul_assoc z.c0 z.c1 invN,
        ← LawfulCommRing.mul_assoc z.c1 z.c0 invN,
        LawfulCommRing.mul_comm z.c1 z.c0,
        LawfulCommRing.add_left_neg]

theorem ofExt2_injective {a b : GoldilocksExt2} (h : ofExt2 a = ofExt2 b) : a = b := by
  exact congrArg c0 h

theorem ofExt2_add (a b : GoldilocksExt2) :
    ofExt2 (CommRingOps.add a b) = CommRingOps.add (ofExt2 a) (ofExt2 b) := by
  exact ext rfl (LawfulCommRing.add_zero _).symm

theorem ofExt2_sub (a b : GoldilocksExt2) :
    ofExt2 (CommRingOps.sub a b) = CommRingOps.sub (ofExt2 a) (ofExt2 b) := by
  exact ext rfl (LawfulCommRing.sub_self _).symm

theorem ofExt2_mul (a b : GoldilocksExt2) :
    ofExt2 (CommRingOps.mul a b) = CommRingOps.mul (ofExt2 a) (ofExt2 b) := by
  apply ext
  · change CommRingOps.mul a b =
      CommRingOps.add (CommRingOps.mul a b)
        (CommRingOps.mul nonResidue (CommRingOps.mul CommRingOps.zero CommRingOps.zero))
    rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  · change CommRingOps.zero =
      CommRingOps.add (CommRingOps.mul a CommRingOps.zero) (CommRingOps.mul CommRingOps.zero b)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

theorem embedBase_injective {a b : Goldilocks} (h : embedBase a = embedBase b) : a = b := by
  exact GoldilocksExt2.ofBase_injective (ofExt2_injective h)

theorem embedBase_add (a b : Goldilocks) :
    embedBase (CommRingOps.add a b) = CommRingOps.add (embedBase a) (embedBase b) := by
  unfold embedBase
  rw [GoldilocksExt2.ofBase_add, ofExt2_add]

theorem embedBase_sub (a b : Goldilocks) :
    embedBase (CommRingOps.sub a b) = CommRingOps.sub (embedBase a) (embedBase b) := by
  unfold embedBase
  rw [GoldilocksExt2.ofBase_sub, ofExt2_sub]

theorem embedBase_mul (a b : Goldilocks) :
    embedBase (CommRingOps.mul a b) = CommRingOps.mul (embedBase a) (embedBase b) := by
  unfold embedBase
  rw [GoldilocksExt2.ofBase_mul, ofExt2_mul]

/-- Base-field membership predicate `z ∈ F_p ↪ F_{p^4}`. -/
def isBase (z : GoldilocksExt4) : Bool :=
  (z.c0.c1 == Goldilocks.zero) && (z.c1 == GoldilocksExt2.zero)

theorem isBase_embedBase (a : Goldilocks) : isBase (embedBase a) = true := by
  simp [isBase, embedBase, ofExt2, GoldilocksExt2.ofBase, GoldilocksExt2.zero, CommRingOps.zero]

theorem eq_embedBase_of_isBase {z : GoldilocksExt4} (h : isBase z = true) :
    z = embedBase z.c0.c0 := by
  unfold isBase at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h01, h1⟩
  apply ext
  · exact GoldilocksExt2.ext rfl (eq_of_beq h01)
  · exact eq_of_beq h1

/-- Canonical 32-byte big-endian limb encoding (`4 × 8 = 32` bytes). -/
def encodeBytes32 (z : GoldilocksExt4) : List UInt8 :=
  be 8 z.c0.c0.val ++ (be 8 z.c0.c1.val ++ (be 8 z.c1.c0.val ++ be 8 z.c1.c1.val))

theorem encodeBytes32_length (z : GoldilocksExt4) : (encodeBytes32 z).length = 32 := by
  simp [encodeBytes32, length_be]

theorem encodeBytes32_injective {x y : GoldilocksExt4}
    (h : encodeBytes32 x = encodeBytes32 y) : x = y := by
  have hb : goldilocksPrime < 256 ^ 8 := by decide
  unfold encodeBytes32 at h
  obtain ⟨h00, r1⟩ := List.append_inj h (by simp [length_be])
  obtain ⟨h01, r2⟩ := List.append_inj r1 (by simp [length_be])
  obtain ⟨h10, h11⟩ := List.append_inj r2 (by simp [length_be])
  have e00 := be_injective (Nat.lt_trans x.c0.c0.isLt hb) (Nat.lt_trans y.c0.c0.isLt hb) h00
  have e01 := be_injective (Nat.lt_trans x.c0.c1.isLt hb) (Nat.lt_trans y.c0.c1.isLt hb) h01
  have e10 := be_injective (Nat.lt_trans x.c1.c0.isLt hb) (Nat.lt_trans y.c1.c0.isLt hb) h10
  have e11 := be_injective (Nat.lt_trans x.c1.c1.isLt hb) (Nat.lt_trans y.c1.c1.isLt hb) h11
  exact ext (GoldilocksExt2.ext (Goldilocks.ext e00) (Goldilocks.ext e01))
    (GoldilocksExt2.ext (Goldilocks.ext e10) (Goldilocks.ext e11))

/-- Checked canonical 32-byte decoder rejecting non-canonical (`≥ p`) 64-bit limbs. -/
def decodeBytes32 (bs : List UInt8) : Option GoldilocksExt4 :=
  if bs.length = 32 then
    let v00 := ofBE (bs.take 8)
    let v01 := ofBE ((bs.drop 8).take 8)
    let v10 := ofBE ((bs.drop 16).take 8)
    let v11 := ofBE ((bs.drop 24).take 8)
    if h00 : v00 < goldilocksPrime then
      if h01 : v01 < goldilocksPrime then
        if h10 : v10 < goldilocksPrime then
          if h11 : v11 < goldilocksPrime then
            some ⟨⟨⟨v00, h00⟩, ⟨v01, h01⟩⟩, ⟨⟨v10, h10⟩, ⟨v11, h11⟩⟩⟩
          else none
        else none
      else none
    else none
  else none

theorem decodeBytes32_encodeBytes32 (z : GoldilocksExt4) :
    decodeBytes32 (encodeBytes32 z) = some z := by
  have hb : goldilocksPrime < 256 ^ 8 := by decide
  have hLen := encodeBytes32_length z
  unfold decodeBytes32
  simp only [hLen, ↓reduceIte]
  have t00 : (encodeBytes32 z).take 8 = be 8 z.c0.c0.val := by
    unfold encodeBytes32
    rw [List.take_left' (length_be 8 z.c0.c0.val)]
  have d8 : (encodeBytes32 z).drop 8 =
      be 8 z.c0.c1.val ++ (be 8 z.c1.c0.val ++ be 8 z.c1.c1.val) := by
    unfold encodeBytes32
    rw [List.drop_left' (length_be 8 z.c0.c0.val)]
  have t01 : ((encodeBytes32 z).drop 8).take 8 = be 8 z.c0.c1.val := by
    rw [d8, List.take_left' (length_be 8 z.c0.c1.val)]
  have d16 : (encodeBytes32 z).drop 16 = be 8 z.c1.c0.val ++ be 8 z.c1.c1.val := by
    have h16 : (16 : Nat) = 8 + 8 := rfl
    rw [h16, ← List.drop_drop, d8, List.drop_left' (length_be 8 z.c0.c1.val)]
  have t10 : ((encodeBytes32 z).drop 16).take 8 = be 8 z.c1.c0.val := by
    rw [d16, List.take_left' (length_be 8 z.c1.c0.val)]
  have d24 : (encodeBytes32 z).drop 24 = be 8 z.c1.c1.val := by
    have h24 : (24 : Nat) = 16 + 8 := rfl
    rw [h24, ← List.drop_drop, d16, List.drop_left' (length_be 8 z.c1.c0.val)]
  have t11 : ((encodeBytes32 z).drop 24).take 8 = be 8 z.c1.c1.val := by
    rw [d24, List.take_of_length_le (Nat.le_of_eq (length_be 8 z.c1.c1.val))]
  rw [t00, t01, t10, t11,
      ofBE_be (Nat.lt_trans z.c0.c0.isLt hb),
      ofBE_be (Nat.lt_trans z.c0.c1.isLt hb),
      ofBE_be (Nat.lt_trans z.c1.c0.isLt hb),
      ofBE_be (Nat.lt_trans z.c1.c1.isLt hb)]
  simp only [z.c0.c0.isLt, z.c0.c1.isLt, z.c1.c0.isLt, z.c1.c1.isLt, ↓reduceDIte]

end GoldilocksExt4

instance : NoZeroDivisors GoldilocksExt4 where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    if ha : a = GoldilocksExt4.zero then
      exact .inl ha
    else
      right
      have hmul := congrArg (CommRingOps.mul (GoldilocksExt4.inv a)) h
      rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (GoldilocksExt4.inv a) a,
          GoldilocksExt4.mul_inv_cancel ha, LawfulCommRing.one_mul] at hmul
      exact hmul

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

/-- Exact 2-regime unconditional Johnson-radius security ladder matching `WhirSecurityRegime` in
    `crates/qsag-agg/src/pcs.rs` (`PCS_POW_BITS = 16` = `8` QROM Grover bits; retired capacity
    wire tags `0, 1, 3` are rejected on deserialization per `Crites & Stewart 2025/2046` and
    `Krachun-Kazanin-Habock 2026/782`):
    - `bciksJohnsonClassical128` (wire tag `2`): `q = (129, 65, 44, 33)` (`⌈256 / log₂ B⌉ + 1`;
      `+1` Johnson slack -> unconditional `< 2^-128` + `16`b PoW = `144` classical FS round bits)
    - `bciksJohnsonQrom128` (**DEFAULT**, wire tag `4`): `q = (258, 130, 88, 66)`
      (`⌈512 / log₂ B⌉ + 2`, as in `minimum_queries`; `+2` Johnson slack -> unconditional
      `< 2^-256` + `16`b PoW = `136` QROM Grover round-search bits). -/
inductive WhirSecurityRegime where
  | bciksJohnsonClassical128
  | bciksJohnsonQrom128
  deriving DecidableEq, Repr

def WhirSecurityRegime.defaultRegime : WhirSecurityRegime := .bciksJohnsonQrom128

def WhirSecurityRegime.tagByte : WhirSecurityRegime → UInt8
  | .bciksJohnsonClassical128 => 2
  | .bciksJohnsonQrom128 => 4

/-- Wire-tag decoder matching `WhirSecurityRegime::from_u8` in `crates/qsag-agg/src/pcs.rs`:
    accepts only wire tags `2` (`bciksJohnsonClassical128`) and `4` (`bciksJohnsonQrom128`),
    rejecting retired capacity-proximity tags `0`, `1`, and `3`. -/
def WhirSecurityRegime.decodeTag? : UInt8 → Option WhirSecurityRegime
  | 2 => some .bciksJohnsonClassical128
  | 4 => some .bciksJohnsonQrom128
  | _ => none

theorem WhirSecurityRegime.decodeTag?_tagByte (r : WhirSecurityRegime) :
    WhirSecurityRegime.decodeTag? r.tagByte = some r := by
  cases r <;> rfl

theorem WhirSecurityRegime.tagByte_of_decodeTag? {tag : UInt8} {r : WhirSecurityRegime}
    (h : WhirSecurityRegime.decodeTag? tag = some r) :
    r.tagByte = tag := by
  unfold WhirSecurityRegime.decodeTag? at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem WhirSecurityRegime.tagByte_injective {r1 r2 : WhirSecurityRegime}
    (h : r1.tagByte = r2.tagByte) : r1 = r2 := by
  cases r1 <;> cases r2 <;> first | rfl | cases h

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

/-- Full 4-stage `(4, 16, 64, 256)` WHIR schedule for each `WhirSecurityRegime`. -/
def whirSchedule4Stage : WhirSecurityRegime → List WhirStageSpec
  | .bciksJohnsonClassical128 =>
    [ ⟨0, 4, 2, 129, 16⟩, ⟨1, 16, 4, 65, 16⟩, ⟨2, 64, 8, 44, 16⟩, ⟨3, 256, 16, 33, 16⟩ ]
  | .bciksJohnsonQrom128 =>
    [ ⟨0, 4, 2, 258, 16⟩, ⟨1, 16, 4, 130, 16⟩, ⟨2, 64, 8, 88, 16⟩, ⟨3, 256, 16, 66, 16⟩ ]

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
  maxPcsVars := 24
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
    productionAggParams.maxRowRounds = 16 ∧
    productionAggParams.maxFoldRounds = 16 ∧
    productionAggParams.maxStage0Domain = 2 ^ 26 ∧
    productionAggParams.maxQueryGroups = 2 ^ 20 ∧
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
    let r := squeezeExt4Challenge "QSAG.AGG.WHIR.ROW_SC/v2".toUTF8.toList frame
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
