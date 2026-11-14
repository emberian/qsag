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
3. **5-Regime QROM Grover & `[BCIKS20]` Johnson WHIR Schedule Ladder (§5):**
   Exact `(4, 16, 64, 256)` rate-escalating schedules matching `crates/qsag-agg/src/pcs.rs` across
   all five `WhirSecurityRegime` profiles (`habr24Classical128`, `habr24Interactive128`,
   `bciksJohnsonClassical128`, default `habr24Qrom128`, and unconditional `bciksJohnsonQrom128`),
   proving positive Johnson proximity slack (`+1` query -> `eta = 1/512` and `eta = 1/1024` with
   explicit finite `[BCIKS20]` list bounds `L <= 256` and `L <= 512`) and `ProductionAggParams`.
4. **Succinct Multi-Stage WHIR + OOD + PoW + Degree-8 Sumcheck Verifier (§6–§8):**
   Instance-bound Fiat–Shamir transcript, degree-8 row sumcheck over `GoldilocksExt4`, multi-stage
   WHIR verifier (`verifySuccinctAggregate`, `verifyAggregatedSignature`, `MergeNode`,
   `verifyMergeTree` — zero plaintext `List PqHashSig` openings), per-stage OOD list-pinning,
   degree-2 shift/OOD sumcheck, 16-bit `cSHAKE256` Proof-of-Work (`verifyWhirStagePow`), distinct
   sorted fiber openings (`strictlyIncreasing`), constructive `0 Classical.choice` `PSum` knowledge
   soundness (`succinct_aggregation_knowledge_soundness`, `succinct_merge_tree_knowledge_soundness`),
   and end-to-end unforgeability reduction (`qsag_aggregate_unforgeability_reduction`) into
   `extractFullHypertreeForgery`.
5. **Transcript-Bound Challenge & Query Soundness Counting (§9–§10):**
   Adaptive `challengeVectors` union bounds and `distinctTuples` falling-factorial query bounds over
   concrete `Nodup` `List Aggregation.GoldilocksExt4` domains across all 5 `WhirSecurityRegime`s.
6. **Genuine Reed–Solomon + Degree-7 S-Box Trace-Decoding `RowArithmetization.Lawful` (§11–§12):**
   Concrete blowup-4 -> blowup-16 2-stage WHIR arithmetization (`rsSbox7TraceArith_lawful`) where
   `isStageCodeword 0` checks real base-field Reed–Solomon evaluation constraints on 8th roots of
   unity (`#tooth` `tooth_corrupted_round0_symbol_rejected`), `decodeSigs` extracts `List PqHashSig`
   directly from the committed trace polynomial (`decodeSbox7Sigs_nonconstant`), and an explicit
   end-to-end 2-stage WHIR proof passes `verifySuccinctAggregate` and `verifyMergeTree`.
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

@[simp] theorem ofExt2_c0 (a : GoldilocksExt2) : (ofExt2 a).c0 = a := rfl
@[simp] theorem ofExt2_c1 (a : GoldilocksExt2) : (ofExt2 a).c1 = CommRingOps.zero := rfl
@[simp] theorem embedBase_c0_c0 (a : Goldilocks) : (embedBase a).c0.c0 = a := rfl

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
  add_assoc x y z := ext (LawfulCommRing.add_assoc x.c0 y.c0 z.c0)
    (LawfulCommRing.add_assoc x.c1 y.c1 z.c1)
  add_comm x y := ext (LawfulCommRing.add_comm x.c0 y.c0)
    (LawfulCommRing.add_comm x.c1 y.c1)
  zero_add x := ext (LawfulCommRing.zero_add x.c0) (LawfulCommRing.zero_add x.c1)
  add_zero x := ext (LawfulCommRing.add_zero x.c0) (LawfulCommRing.add_zero x.c1)
  add_left_neg x := ext (LawfulCommRing.add_left_neg x.c0) (LawfulCommRing.add_left_neg x.c1)
  sub_eq_add_neg x y := ext (LawfulCommRing.sub_eq_add_neg x.c0 y.c0)
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
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.add y.c1 z.c1))) = _
      rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
    · change CommRingOps.add (CommRingOps.mul x.c0 (CommRingOps.add y.c1 z.c1))
          (CommRingOps.mul x.c1 (CommRingOps.add y.c0 z.c0)) = _
      rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
  right_distrib x y z := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c1)) = _
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c1)
          (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c0) = _
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
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
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
          LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
      have t1 : CommRingOps.mul (CommRingOps.mul x.c0 y.c0) z.c0 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c0) :=
        LawfulCommRing.mul_assoc _ _ _
      have t2 : CommRingOps.mul (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c0 =
          CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0)) := by
        rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc]
      have t3 : CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c1) =
          CommRingOps.mul x.c0 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc x.c0 y.c1 z.c1,
            ← LawfulCommRing.mul_assoc nonResidue x.c0 _,
            LawfulCommRing.mul_comm nonResidue x.c0,
            LawfulCommRing.mul_assoc]
      have t4 : CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c1) =
          CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c1)) := by
        rw [LawfulCommRing.mul_assoc]
      rw [t1, t2, t3, t4, LawfulCommRing.add_add_add_comm]
      congr 1
      exact LawfulCommRing.add_comm _ _
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
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
          LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
      have s1 : CommRingOps.mul (CommRingOps.mul x.c0 y.c0) z.c1 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c1) :=
        LawfulCommRing.mul_assoc _ _ _
      have s2 : CommRingOps.mul (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c1 =
          CommRingOps.mul x.c1 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc nonResidue _ z.c1,
            LawfulCommRing.mul_assoc x.c1 y.c1 z.c1,
            ← LawfulCommRing.mul_assoc nonResidue x.c1 _,
            LawfulCommRing.mul_comm nonResidue x.c1,
            LawfulCommRing.mul_assoc]
      have s3 : CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c0 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c1 z.c0) :=
        LawfulCommRing.mul_assoc _ _ _
      have s4 : CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c0 =
          CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c0) :=
        LawfulCommRing.mul_assoc _ _ _
      rw [s1, s2, s3, s4, LawfulCommRing.add_add_add_comm]
      congr 1
      exact LawfulCommRing.add_comm _ _

/-- Square root of `-1` in `Goldilocks` (`(2^48)^2 = 2^96 ≡ -1 (mod p)`). -/
def sqrtNegOne : Goldilocks := ⟨2 ^ 48, by decide⟩

theorem sqrtNegOne_sq :
    CommRingOps.mul sqrtNegOne sqrtNegOne = CommRingOps.neg CommRingOps.one := by
  decide

/-- **`uBasis_not_square`**: `u = (0, 1) ∈ GoldilocksExt2` has no square root in `GoldilocksExt2`,
    so $v^2 - u$ is irreducible over $\mathbb{F}_{p^2}$. -/
theorem uBasis_not_square (z : GoldilocksExt2) :
    CommRingOps.mul z z ≠ nonResidue := by
  intro hsq
  have hc0 : CommRingOps.add (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) =
      Goldilocks.zero := congrArg GoldilocksExt2.c0 hsq
  have hc1 : CommRingOps.add (CommRingOps.mul z.c0 z.c1) (CommRingOps.mul z.c1 z.c0) =
      Goldilocks.one := congrArg GoldilocksExt2.c1 hsq
  have hbNe : z.c1 ≠ Goldilocks.zero := by
    intro hb0
    rw [hb0] at hc1
    change CommRingOps.add (CommRingOps.mul z.c0 CommRingOps.zero)
      (CommRingOps.mul CommRingOps.zero z.c0) = Goldilocks.one at hc1
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hc1
    revert hc1
    decide
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
    rw [hassoc, haSqEq, ← LawfulCommRing.neg_mul,
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
    rw [hassoc, hqSq, sqrtNegOne_sq, ← LawfulCommRing.neg_mul, ← LawfulCommRing.mul_neg,
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

theorem ofExt2_injective {a b : GoldilocksExt2} (h : ofExt2 a = ofExt2 b) : a = b :=
  congrArg c0 h

theorem ofExt2_add (a b : GoldilocksExt2) :
    ofExt2 (CommRingOps.add a b) = CommRingOps.add (ofExt2 a) (ofExt2 b) :=
  ext rfl (LawfulCommRing.add_zero _).symm

theorem ofExt2_sub (a b : GoldilocksExt2) :
    ofExt2 (CommRingOps.sub a b) = CommRingOps.sub (ofExt2 a) (ofExt2 b) :=
  ext rfl (LawfulCommRing.sub_self _).symm

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

theorem embedBase_injective {a b : Goldilocks} (h : embedBase a = embedBase b) : a = b :=
  GoldilocksExt2.ofBase_injective (ofExt2_injective h)

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
    have h24 : (24 : Nat) = 8 + 16 := rfl
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
      decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r))).length ≤ 8 :=
  ext4_poly_roots_le_degree 8 claimedPoly honestPoly S hNodup hLenC hLenH hDiff

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
      decide (RoundPoly.evalCoeffs candA z = RoundPoly.evalCoeffs candB z))).length ≤ d :=
  ext4_poly_roots_le_degree d candA candB S hNodup hLenA hLenB hDiff

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

/-! ## 5. 5-Regime QROM Grover & `[BCIKS20]` Johnson WHIR Schedule Ladder -/

/-- Exact 5-regime security ladder matching `WhirSecurityRegime` in `crates/qsag-agg/src/pcs.rs`
    (`PCS_POW_BITS = 16` = `8` QROM Grover bits):
    - `habr24Classical128`: `q = (56, 28, 19, 14)` (`2^-112` `[HABR24]` + `16`b PoW = `128`b classical FS)
    - `habr24Interactive128`: `q = (64, 32, 22, 16)` (`2^-128` `[HABR24]`, `144`b classical FS)
    - `bciksJohnsonClassical128`: `q = (129, 65, 44, 33)` (`+1` Johnson slack -> unconditional `< 2^-128`)
    - `habr24Qrom128` (**DEFAULT**): `q = (128, 64, 43, 32)` (`2^-256` `[HABR24]` + `16`b PoW = `136` QROM bits)
    - `bciksJohnsonQrom128`: `q = (257, 129, 86, 65)` (`+1` Johnson slack -> unconditional `< 2^-256` + `16`b PoW = `136` QROM bits without `[HABR24]`). -/
inductive WhirSecurityRegime where
  | habr24Classical128
  | habr24Interactive128
  | bciksJohnsonClassical128
  | habr24Qrom128
  | bciksJohnsonQrom128
  deriving DecidableEq, Repr

def WhirSecurityRegime.defaultRegime : WhirSecurityRegime := .habr24Qrom128

def WhirSecurityRegime.tagByte : WhirSecurityRegime → UInt8
  | .habr24Classical128 => 0x01
  | .habr24Interactive128 => 0x02
  | .bciksJohnsonClassical128 => 0x03
  | .habr24Qrom128 => 0x04
  | .bciksJohnsonQrom128 => 0x05

theorem WhirSecurityRegime.tagByte_injective {r1 r2 : WhirSecurityRegime}
    (h : r1.tagByte = r2.tagByte) : r1 = r2 := by
  cases r1 <;> cases r2 <;> first | rfl | cases h

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
  | .habr24Classical128 =>
    [ ⟨0, 4, 2, 56, 16⟩, ⟨1, 16, 4, 28, 16⟩, ⟨2, 64, 8, 19, 16⟩, ⟨3, 256, 16, 14, 16⟩ ]
  | .habr24Interactive128 =>
    [ ⟨0, 4, 2, 64, 16⟩, ⟨1, 16, 4, 32, 16⟩, ⟨2, 64, 8, 22, 16⟩, ⟨3, 256, 16, 16, 16⟩ ]
  | .bciksJohnsonClassical128 =>
    [ ⟨0, 4, 2, 129, 16⟩, ⟨1, 16, 4, 65, 16⟩, ⟨2, 64, 8, 44, 16⟩, ⟨3, 256, 16, 33, 16⟩ ]
  | .habr24Qrom128 =>
    [ ⟨0, 4, 2, 128, 16⟩, ⟨1, 16, 4, 64, 16⟩, ⟨2, 64, 8, 43, 16⟩, ⟨3, 256, 16, 32, 16⟩ ]
  | .bciksJohnsonQrom128 =>
    [ ⟨0, 4, 2, 257, 16⟩, ⟨1, 16, 4, 129, 16⟩, ⟨2, 64, 8, 86, 16⟩, ⟨3, 256, 16, 65, 16⟩ ]

/-- 3-stage `(4, 16, 64)` WHIR schedule at `num_vars = 20` (`K = 8` shard). -/
def whirScheduleNv20 (r : WhirSecurityRegime) : List WhirStageSpec :=
  (whirSchedule4Stage r).take 3

/-- Every stage in every regime has exact integer square blowup `johnsonSqrtBlowup ^ 2 = blowup`. -/
theorem whirSchedule4Stage_sqrt_sq (r : WhirSecurityRegime) :
    ∀ s ∈ whirSchedule4Stage r, s.johnsonSqrtBlowup ^ 2 = s.blowup := by
  cases r <;> decide

/-- `Habr24Classical128`: `B_s ^ q_s ≥ 2^112` (`+ 16`b classical PoW = `128`b classical FS). -/
theorem habr24Classical128_stage_exponents :
    ∀ s ∈ whirSchedule4Stage .habr24Classical128, 2 ^ 112 ≤ s.blowup ^ s.numQueries := by
  decide

/-- `Habr24Interactive128`: `B_s ^ q_s ≥ 2^128` across `(4, 16, 64, 256)`. -/
theorem habr24Interactive128_stage_exponents :
    ∀ s ∈ whirSchedule4Stage .habr24Interactive128, 2 ^ 128 ≤ s.blowup ^ s.numQueries := by
  decide

/-- `Habr24Qrom128` (**DEFAULT**): `B_s ^ q_s ≥ 2^256` across `(4, 16, 64, 256)` (`+ 16`b PoW =
    `272` classical bits / `136` QROM Grover round-search bits, giving `≥ 128` QROM bits with
    `8`-bit multi-round slack). -/
theorem habr24Qrom128_stage_exponents :
    ∀ s ∈ whirSchedule4Stage .habr24Qrom128, 2 ^ 256 ≤ s.blowup ^ s.numQueries := by
  decide

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
    With `+1` query (`q = (257, 129, 86, 65)`), EVERY stage satisfies `(1 / √B_s + η)^{q_s} < 2^-256`
    at concrete positive proximity slack `η = 1 / 1024 > 0` (yielding explicit finite `[BCIKS20]`
    list-decoding bound `L ≤ 1 / (2η) = 512` and `136` QROM Grover round-search bits without
    `[HABR24]`). -/
theorem bciksJohnsonQrom128_positive_slack :
    ∀ s ∈ whirSchedule4Stage .bciksJohnsonQrom128,
      2 ^ 256 < s.johnsonSqrtBlowup ^ s.numQueries ∧
      (1024 / s.johnsonSqrtBlowup + 1) ^ s.numQueries * 2 ^ 256 < 1024 ^ s.numQueries := by
  decide

end Aggregation

/-- Parameters of the production `GoldilocksExt4` WHIR succinct aggregation proof system,
    aligned with `crates/qsag-agg/src/{pcs,arithmetize,trace,lib}.rs`. -/
structure ProductionAggParams where
  rowSumcheckDegree : Nat
  logTraceCols : Nat
  maxPcsVars : Nat
  rsBlowup : Nat
  maxQueryCap : Nat
  stageBlowups : List Nat
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
  maxQueryCap := 257
  stageBlowups := [4, 16, 64, 256]
  defaultQromQueries := [128, 64, 43, 32]
  johnsonQromQueries := [257, 129, 86, 65]
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
  regime : WhirSecurityRegime := .habr24Qrom128
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
    ∃ sig, verifyPqHashSig suite params (pks[i]'hPk) msg sig = true :=
  let ⟨sig, hVer⟩ := extractActiveSignerSig suite params msg pks bs sigs i hPk hB hAll hbTrue
  ⟨sig, hVer⟩

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
        exact ⟨hUnpackH.1.1, hUnpackH.1.2, hUnpackH.2⟩
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
  regime : WhirSecurityRegime := .habr24Qrom128
  message : List UInt8
  committee : List PqPublicKey
  signingModeDigest : List UInt8

/-- Canonical injective instance framing binding `message`, `signingModeDigest`, `regime`,
    `committee`, `params`, `bitmap`, `traceCommitment`, and `childrenCommitment`. -/
def aggregateInstanceFrame (inst : AggPublicInstance) (agg : AggregatedSignature) : List UInt8 :=
  encodeMultiFrame [inst.message, inst.signingModeDigest, [inst.regime.tagByte],
    encodeMultiFrame (inst.committee.map (fun pk => encodeMultiFrame [pk.pkSeed, pk.pkRoot])),
    encodeMultiFrame ([inst.params.w, inst.params.ell1, inst.params.subtreeHeight,
      inst.params.numLayers, inst.params.forsTrees, inst.params.forsHeight,
      inst.params.maxSigsLog2].map (fun n => (toString n).toUTF8.toList)),
    [if inst.params.statefulJorts then 1 else 0],
    agg.bitmap.map (fun b => if b then 1 else 0), agg.traceCommitment,
    match agg.childrenCommitment with
    | none => []
    | some (left, right) => encodeMultiFrame [left, right]]

theorem aggregate_frame_message_binding (first second : AggPublicInstance)
    (a b : AggregatedSignature)
    (h : aggregateInstanceFrame first a = aggregateInstanceFrame second b) :
    first.message = second.message :=
  (List.cons.inj (encodeMultiFrame_injective h)).1

theorem aggregate_frame_regime_binding (first second : AggPublicInstance)
    (a b : AggregatedSignature)
    (h : aggregateInstanceFrame first a = aggregateInstanceFrame second b) :
    first.regime = second.regime := by
  have hf := encodeMultiFrame_injective h
  have h2 := (List.cons.inj (List.cons.inj hf).2).2
  have hTag := List.cons.inj (List.cons.inj h2).1
  exact WhirSecurityRegime.tagByte_injective hTag.1

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

/-- **Per-Stage WHIR Transcript Proof-of-Work (`verifyWhirStagePow`, `POW_MIDSTATE`)**:
    Absorbs `(seed, be 8 powNonce)` under `"QSAG.PCS.POW/v2"` and checks that the top `powBits`
    bits of the 64-bit big-endian prefix are all `0` (`ofBE (digest.take 8) < 2^(64 - powBits)`). -/
def verifyWhirStagePow (seed : List UInt8) (powNonce powBits : Nat) : Bool :=
  if powBits = 0 then true
  else if powBits ≤ 64 then
    let digest := cshake256Bytes "QSAG.PCS.POW/v2".toUTF8.toList
      (encodeMultiFrame [seed, be 8 powNonce])
    decide (ofBE (digest.take 8) < 2 ^ (64 - powBits))
  else false

/-- Concrete inhabitedness witness: genuine 16-bit `cSHAKE256` Proof-of-Work (`powBits = 16`,
    nonce `28915`) verified directly by the Lean kernel. -/
theorem inhabited_whir_stage_pow_16 :
    verifyWhirStagePow "QSAG.POW.WITNESS/v2".toUTF8.toList 28915 16 = true := by
  decide +kernel

/-- `#tooth` Invalid PoW Nonce Rejection (`powNonce = 0` fails 16-bit PoW on the witness seed). -/
theorem tooth_whir_pow16_nonce0_rejected :
    verifyWhirStagePow "QSAG.POW.WITNESS/v2".toUTF8.toList 0 16 = false := by
  decide +kernel

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

/-- Proof transcript data for one WHIR stage `s`:
    `stageRoot` -> squeeze `oodChallenge` -> absorb `oodEval` -> interleaved degree-2 shift/OOD
    sumcheck (`shiftPolys`, `layerRoots`, `shiftChallenges`) -> `powNonce` -> `queries`. -/
structure WhirStageProof where
  stageRoot : List UInt8
  oodChallenge : GoldilocksExt4
  oodEval : GoldilocksExt4
  shiftClaim : GoldilocksExt4
  shiftPolys : List (List GoldilocksExt4)
  layerRoots : List (List UInt8)
  shiftChallenges : List GoldilocksExt4
  foldChallenges : List GoldilocksExt4
  shiftTerminalEval : GoldilocksExt4
  powNonce : Nat
  queries : List StageQueryOpening

/-- Complete succinct `GoldilocksExt4` WHIR aggregate certificate: zero `PqHashSig` lists. -/
structure SuccinctAggregateProof where
  agg : AggregatedSignature
  stages : List WhirStageProof
  finalWord : List GoldilocksExt4

def stageAllRoots (sp : WhirStageProof) : List (List UInt8) :=
  sp.stageRoot :: sp.layerRoots

/-- Squeeze the Fiat–Shamir OOD point `z_ood` after absorbing `stageRoot`. -/
def deriveStageOodChallenge (prior : List UInt8) (stageRoot : List UInt8) : GoldilocksExt4 :=
  squeezeExt4Challenge "QSAG.AGG.WHIR.OOD/v2".toUTF8.toList (encodeMultiFrame [prior, stageRoot])

/-- Transcript state after absorbing `stageRoot`, `oodEval`, and `shiftClaim`. -/
def stagePostOodTranscript (prior : List UInt8) (sp : WhirStageProof) : List UInt8 :=
  encodeMultiFrame [prior, sp.stageRoot, GoldilocksExt4.encodeBytes32 sp.oodEval,
    GoldilocksExt4.encodeBytes32 sp.shiftClaim]

/-- Interleaved per-stage shift/fold challenge derivation (`[stageRoot] ++ layerRoots` paired with
    `shiftPolys`). -/
def deriveStageShiftChallenges (prior : List UInt8) :
    List (List UInt8) → List (List GoldilocksExt4) → List GoldilocksExt4
  | root :: roots, p :: ps =>
    let frame := encodeMultiFrame [prior, root, encodePolyExt4 p]
    let α := squeezeExt4Challenge "QSAG.AGG.WHIR.FOLD/v2".toUTF8.toList frame
    α :: deriveStageShiftChallenges frame roots ps
  | _, _ => []

def stageFoldTranscriptTail (prior : List UInt8) :
    List (List UInt8) → List (List GoldilocksExt4) → List UInt8
  | root :: roots, p :: ps =>
    stageFoldTranscriptTail (encodeMultiFrame [prior, root, encodePolyExt4 p]) roots ps
  | _, _ => prior

/-- Seed feeding `verifyWhirStagePow` for stage `sp` (incorporates `finalWord` if final stage). -/
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
  ofBE ((cshake256Bytes "QSAG.AGG.WHIR.QUERY/v2".toUTF8.toList
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
      simp only [hlt, heq, ↓reduceIte] at h
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
      simp only [hlt, ↓reduceIte, strictlyIncreasing, decide_eq_true hlt, h, Bool.and_self]
    else if heq : x = y then
      simp only [hlt, heq, ↓reduceIte, h]
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
      exact False.elim (hNot (List.mem_cons_of_eq x heq))
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
        · exact .inr hm
      else if heq : x = y then
        simp only [hlt, heq, ↓reduceIte]
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
      simp [hlt, heq]
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
      simp [hlt, heq]
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
          rcases mem_sortedInsertDistinct hw with rfl | hm
          · exact hXs x (.head _)
          · exact hAcc w hm) z hz

private theorem filter_ne_length_lt_of_mem (x : Nat) :
    ∀ (acc : List Nat), x ∈ acc → (acc.filter (fun z => decide (z ≠ x))).length < acc.length
  | [], hm => by cases hm
  | a :: as, hm => by
    rcases List.mem_cons.mp hm with rfl | hms
    · simp only [List.filter, ne_eq, not_true_eq_false, decide_false, List.length_cons]
      have hLe := List.length_filter_le (fun z => decide (z ≠ x)) as
      omega
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
    simp only [scanFillDistinct, List.filter] at hGe ⊢
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
  have hRange := nodup_length_le_missing_add_acc (List.range sdom.groups0) List.nodup_range sampled
  rw [List.length_range] at hRange
  have hTargetLe : target ≤ sdom.groups0 := Nat.min_le_right _ _
  refine ⟨strictlyIncreasing_scanFillDistinct target _ sampled hIncS,
    length_scanFillDistinct target _ sampled hIncS List.nodup_range hLenS (by omega),
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

/-- Verify one WHIR stage's header, OOD challenge, degree-2 shift sumcheck, PoW, and queries. -/
def verifyOneWhirStage (rowChallenges : List GoldilocksExt4)
    (finalWord : List GoldilocksExt4) (prior : List UInt8)
    (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextStageInfo : Option (WhirStageDomain × List UInt8)) : Bool :=
  let nextRoot? := nextStageInfo.map Prod.snd
  let pSeed := stagePowSeed prior sp nextRoot? finalWord
  let qSeed := stageQuerySeed pSeed sp.powNonce
  let expectedFold := if sdom.bindRowChallenges then rowChallenges
                      else sp.shiftChallenges
  decide (sp.oodChallenge = deriveStageOodChallenge prior sp.stageRoot) &&
  decide ((stageAllRoots sp).length = sdom.foldLayers) &&
  decide (sp.shiftPolys.length = sdom.foldLayers) &&
  decide (sp.shiftChallenges =
    deriveStageShiftChallenges (stagePostOodTranscript prior sp) (stageAllRoots sp) sp.shiftPolys) &&
  decide (sp.foldChallenges = expectedFold) &&
  decide (sp.foldChallenges.length = sdom.foldLayers) &&
  verifyShiftSumcheckChain sp.shiftClaim sp.shiftPolys sp.shiftChallenges sp.shiftTerminalEval &&
  verifyWhirStagePow pSeed sp.powNonce sdom.powBits &&
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
    verifyMergeTree arith dom inst 0 tree = false := rfl

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

def stageTerminalSound (authPath : Nat → Nat → Nat → List (List UInt8))
    (nextStageInfo : Option (WhirStageDomain × List UInt8))
    (nextStageOpt : Option (WhirStageDomain × List GoldilocksExt4))
    (finalWord : List GoldilocksExt4) (idx : Nat) (expected : Option GoldilocksExt4)
    (bridgeOp : Option FoldLayerOpening)
    (hTerm : verifyStageTerminalTarget nextStageInfo finalWord idx expected bridgeOp = true)
    (hNextBound : match nextStageInfo, nextStageOpt with
      | none, none => True
      | some (nd, nr), some (nd', nt0) =>
        nd = nd' ∧
        (∀ g, g < nd.groups0 →
          merklePathRoot pcsMerkleHash
            (pcsMerkleHash (duetLeafFrame nd.stageIdx 0 g (nt0.getD g CommRingOps.zero)
              (nt0.getD (g + nd.groups0) CommRingOps.zero))) g (authPath nd.stageIdx 0 g) = nr ∧
          (authPath nd.stageIdx 0 g).length = merkleDepth nd.groups0)
      | _, _ => False) :
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
    (authPath : Nat → Nat → Nat → List (List UInt8)) :
    ∀ (roots : List (List UInt8)) (αs : List GoldilocksExt4) (ops : List FoldLayerOpening)
      (tables : List (List GoldilocksExt4)) (layer groups idx : Nat)
      (expected : Option GoldilocksExt4),
      verifyStageTrajectory sdom nextStageInfo finalWord bridgeOp
        layer groups idx expected roots αs ops = true →
      StageLayersBound authPath sdom.stageIdx layer groups tables roots →
      (match nextStageInfo, nextStageOpt with
        | none, none => True
        | some (nd, nr), some (nd', nt0) =>
          nd = nd' ∧
          (∀ g, g < nd.groups0 →
            merklePathRoot pcsMerkleHash
              (pcsMerkleHash (duetLeafFrame nd.stageIdx 0 g (nt0.getD g CommRingOps.zero)
                (nt0.getD (g + nd.groups0) CommRingOps.zero))) g (authPath nd.stageIdx 0 g) = nr ∧
            (authPath nd.stageIdx 0 g).length = merkleDepth nd.groups0)
        | _, _ => False) →
      PSum (HashCollisionWitness pcsMerkleHash)
        (PLift (stageTableTrajectoryOk sdom nextStageOpt finalWord
          layer groups idx expected tables αs = true))
  | [], [], [], [], _, _, idx, expected, hV, _, hN =>
    stageTerminalSound authPath nextStageInfo nextStageOpt finalWord idx expected bridgeOp hV hN
  | [], [], [], _ :: _, _, _, _, _, _, hB, _ => False.elim hB
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, hB, _ => False.elim hB
  | [], [], _ :: _, _, _, _, _, _, hV, _, _ => False.elim (by simp [verifyStageTrajectory] at hV)
  | [], _ :: _, ops, _, _, _, _, _, hV, _, _ =>
    False.elim (by cases ops <;> simp [verifyStageTrajectory] at hV)
  | _ :: _, [], ops, _, _, _, _, _, hV, _, _ =>
    False.elim (by cases ops <;> simp [verifyStageTrajectory] at hV)
  | _ :: _, _ :: _, [], _, _, _, _, _, hV, _, _ => False.elim (by simp [verifyStageTrajectory] at hV)
  | root :: roots, α :: αs, op :: ops, w :: ws, layer, groups, idx, expected, hV, hB, hN =>
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
      (match nextStageInfo, nextStageOpt with
        | none, none => True
        | some (nd, nr), some (nd', nt0) =>
          nd = nd' ∧
          (∀ g, g < nd.groups0 →
            merklePathRoot pcsMerkleHash
              (pcsMerkleHash (duetLeafFrame nd.stageIdx 0 g (nt0.getD g CommRingOps.zero)
                (nt0.getD (g + nd.groups0) CommRingOps.zero))) g (authPath nd.stageIdx 0 g) = nr ∧
            (authPath nd.stageIdx 0 g).length = merkleDepth nd.groups0)
        | _, _ => False) →
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

private def headRootBound {authPath : Nat → Nat → Nat → List (List UInt8)}
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
  | _, _ :: _ :: _, [_], _, _, hB => False.elim hB.2.2
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

theorem stagesBound_lengths {authPath : Nat → Nat → Nat → List (List UInt8)} :
    ∀ {sdoms : List WhirStageDomain} {allTables : List (List (List GoldilocksExt4))}
      {sps : List WhirStageProof},
      StagesBound authPath sdoms allTables sps →
      sdoms.length = allTables.length ∧ sdoms.length = sps.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, h => False.elim h
  | [], [], _ :: _, h => False.elim h
  | _ :: _, [], _, h => False.elim h
  | _ :: _, _ :: _, [], h => False.elim h
  | _ :: sdoms, _ :: restTables, _ :: sps, h => by
    obtain ⟨h1, h2⟩ := stagesBound_lengths h.2.2
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
    rcases Bool.and_eq_true_iff.mp h with ⟨c1, c2⟩
    exact ⟨of_decide_eq_true c1, of_decide_eq_true c2, of_decide_eq_true c4, c5,
      of_decide_eq_true c6, c7, c8⟩

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
    `extractFullHypertreeForgery` (`Qsag.HypertreeEufCma`) with zero black-box `hHonestSound`
    premise and zero plaintext signatures in the verifier. -/
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
    (hParams4_128 : inst.params.w = 4 ∧ inst.params.ell1 = 128)
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
    (hUpperOracle : ∀ (l : Nat) (g : Nat), 0 < l →
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
    .inl ⟨sig_i, extractFullHypertreeForgery inst.suite inst.params sk_i inst.message sig_i
      queriedMsgs qOracle revealedFors hParams4_128 hFreshMsg hVerKey
      (hStatefulLeaf0Msg sig_i) (hStatelessLayer0Root sig_i)
      hUpperOracle (hLayer0Valid sig_i)⟩

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

/-! ## 9. Adaptive Challenge-Vector & Falling-Factorial Query Counting Foundations -/

private theorem filter_const_false {α : Type} : ∀ (l : List α), l.filter (fun _ => false) = []
  | [] => rfl
  | _ :: xs => filter_const_false xs

private theorem filter_length_le_self {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.filter p).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := filter_length_le_self p xs
    cases hp : p x
    · simp only [List.filter, hp, List.length_cons]; exact Nat.le_succ_of_le ih
    · simp only [List.filter, hp, List.length_cons]; exact Nat.succ_le_succ ih

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

private theorem length_flatMap_le_split {α β : Type} (b : α → Bool) (T M : Nat) (f : α → List β) :
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
  | i + 1, _ :: xs, hi, hx => by
    have ih := countGood_eraseFirstAt_good p i xs (Nat.lt_of_succ_lt_succ hi) hx
    cases hpy : p _ <;>
      simp only [eraseFirstAt, countGood, List.filter, hpy, List.length_cons] at ih ⊢ <;>
      omega

/-- Ordered `q`-tuples drawn without replacement from `dom`. -/
def distinctTuples {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | q + 1, dom =>
    (List.range dom.length).flatMap (fun i =>
      match dom[i]? with
      | none => []
      | some x => (distinctTuples q (eraseFirstAt i dom)).map (fun rest => x :: rest))

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

theorem distinctTuples_length {α : Type} :
    ∀ (q : Nat) (dom : List α),
      (distinctTuples q dom).length = fallingFactorial dom.length q
  | 0, _ => rfl
  | q + 1, dom => by
    show ((List.range dom.length).flatMap _).length = dom.length * fallingFactorial (dom.length - 1) q
    have hEach : ∀ i ∈ List.range dom.length,
        (match dom[i]? with
          | none => []
          | some x => (distinctTuples q (eraseFirstAt i dom)).map (fun rest => x :: rest)).length =
          fallingFactorial (dom.length - 1) q := by
      intro i hi
      have hlt : i < dom.length := List.mem_range.mp hi
      rw [List.getElem?_eq_getElem hlt, List.length_map, distinctTuples_length q,
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
    · simp only [hp, ↓reduceIte, hm, ih, countGood, List.filter]
    · simp only [hp, ↓reduceIte, List.length_cons, hm, ih, countGood, List.filter]

theorem distinctTuples_all_good_length {α : Type} (p : α → Bool) :
    ∀ (q : Nat) (dom : List α),
      ((distinctTuples q dom).filter (fun t => t.all p)).length =
        fallingFactorial (countGood p dom) q
  | 0, _ => rfl
  | q + 1, dom => by
    show (((List.range dom.length).flatMap _).filter (fun t => t.all p)).length =
      countGood p dom * fallingFactorial (countGood p dom - 1) q
    rw [filter_flatMap_eq]
    let isGoodIdx : Nat → Bool := fun i => match dom[i]? with | none => false | some x => p x
    let F : Nat → List (List α) := fun i =>
      (match dom[i]? with
        | none => []
        | some x => (distinctTuples q (eraseFirstAt i dom)).map (fun rest => x :: rest)).filter
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
      rw [hfun, distinctTuples_all_good_length p q (eraseFirstAt i dom)]
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
    · show 0 * _ ≤ _
      rw [Nat.zero_mul]; exact Nat.zero_le _
    · have h1 : b * (g - 1) ≤ a * (n - 1) := by
        rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one, Nat.mul_one]
        exact Nat.sub_le_sub hbg hab
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
    ((distinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length * dd ^ q ≤
      (dd - dn) ^ q * (distinctTuples q dom).length := by
  rw [distinctTuples_all_good_length, distinctTuples_length]
  have hsum := countGood_add_complement bad dom
  have hGN : countGood (fun x => !bad x) dom ≤ dom.length := by omega
  apply fallingFactorial_mul_pow_le (dd - dn) dd (Nat.sub_le dd dn) q _ _ hGN
  rw [Nat.sub_mul, Nat.mul_comm (countGood (fun x => !bad x) dom) dd]
  have e : dd * dom.length = dd * countGood (fun x => !bad x) dom + dd * countGood bad dom := by
    rw [← Nat.mul_add, hsum]
  omega

/-! ## 10. Transcript-Bound WHIR Proximity, OOD, Fold & Query Soundness (`GoldilocksExt4`) -/

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
    ((distinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length * 2 ^ b <
      (distinctTuples q dom).length := by
  have hb := whir_query_miss_bound bad dom q (den - alphaNum) den hfar
  have hSub : den - (den - alphaNum) = alphaNum := by omega
  rw [hSub] at hb
  have hT : 0 < (distinctTuples q dom).length := by
    rw [distinctTuples_length]; exact fallingFactorial_pos _ _ hdom
  rcases Nat.lt_or_ge
    (((distinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length * 2 ^ b)
    (distinctTuples q dom).length with hlt | hge
  · exact hlt
  · exfalso
    generalize ((distinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length = X at hb hge
    generalize (distinctTuples q dom).length = T at hb hge hT
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
    ((distinctTuples s.numQueries dom).filter (fun t => t.all (fun x => !bad x))).length *
      2 ^ 128 < (distinctTuples s.numQueries dom).length := by
  have hSlack := (bciksJohnsonClassical128_positive_slack s hs).2
  have hLe : 512 / s.johnsonSqrtBlowup + 1 ≤ 512 := by
    revert hs; decide
  exact strict_query_miss_from_slack bad dom s.numQueries
    (512 / s.johnsonSqrtBlowup + 1) 512 128 hdom hLe hfar hSlack

/-- **Unconditional `[BCIKS20]` QROM-128 Per-Stage Query Bound
    (`whir_bciksJohnsonQrom128_query_miss_lt`)**:
    For EVERY stage `s ∈ whirSchedule4Stage .bciksJohnsonQrom128` (`q = (257, 129, 86, 65)`),
    whenever `bad` has relative density `≥ 1 - (1 / √B_s + 1 / 1024)` (positive proximity slack
    `η = 1 / 1024 > 0`, finite Johnson list size `L ≤ 512`), fewer than a `2^-256` fraction of
    distinct query tuples miss `bad` (`+ 16`b PoW = `136` QROM Grover bits without `[HABR24]`). -/
theorem whir_bciksJohnsonQrom128_query_miss_lt {α : Type}
    (s : WhirStageSpec) (hs : s ∈ whirSchedule4Stage .bciksJohnsonQrom128)
    (bad : α → Bool) (dom : List α)
    (hdom : s.numQueries ≤ dom.length)
    (hfar : (1024 - (1024 / s.johnsonSqrtBlowup + 1)) * dom.length ≤ 1024 * countGood bad dom) :
    ((distinctTuples s.numQueries dom).filter (fun t => t.all (fun x => !bad x))).length *
      2 ^ 256 < (distinctTuples s.numQueries dom).length := by
  have hSlack := (bciksJohnsonQrom128_positive_slack s hs).2
  have hLe : 1024 / s.johnsonSqrtBlowup + 1 ≤ 1024 := by
    revert hs; decide
  exact strict_query_miss_from_slack bad dom s.numQueries
    (1024 / s.johnsonSqrtBlowup + 1) 1024 256 hdom hLe hfar hSlack

/-- **Default `Habr24Qrom128` Per-Stage Query Bound (`whir_habr24Qrom128_query_miss_le`)**:
    For EVERY stage `s ∈ whirSchedule4Stage .habr24Qrom128` (`q = (128, 64, 43, 32)`), under
    `[HABR24]` proximity `(B_s - 1) / B_s`, `missCount * 2^256 ≤ totalTuples`. -/
theorem whir_habr24Qrom128_query_miss_le {α : Type}
    (s : WhirStageSpec) (hs : s ∈ whirSchedule4Stage .habr24Qrom128)
    (bad : α → Bool) (dom : List α)
    (hfar : (s.blowup - 1) * dom.length ≤ s.blowup * countGood bad dom) :
    ((distinctTuples s.numQueries dom).filter (fun t => t.all (fun x => !bad x))).length *
      2 ^ 256 ≤ (distinctTuples s.numQueries dom).length := by
  have hb := whir_query_miss_bound bad dom s.numQueries (s.blowup - 1) s.blowup hfar
  have hPos : 1 ≤ s.blowup := by revert hs; decide
  have hSub : s.blowup - (s.blowup - 1) = 1 := by omega
  rw [hSub, Nat.one_pow, Nat.one_mul] at hb
  exact Nat.le_trans
    (Nat.mul_le_mul_left _ (habr24Qrom128_stage_exponents s hs)) hb

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
    ((distinctTuples q dom).filter
      (fun t => anyRoundEvent E cs || t.all (fun x => !bad cs x))).map (fun t => (cs, t)))

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
    · exact whir_query_miss_bound (bad cs) dom q dn dd (hfar cs hcs hEv)
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

/-- Production `GoldilocksExt4` WHIR challenge-event budget covering 16 degree-8 row-sumcheck
    rounds, 16 degree-2 shift-sumcheck rounds, 4 OOD list-pinning stages (`L ≤ 512`, `d ≤ 2^24`),
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
      S.length ^ n * (distinctTuples 129 dom).length := by
  have hJoint := transcript_bad_pairs_le S n E d hE dom 129 (512 - 257) 512 bad hfar
  have hSub : 512 - (512 - 257) = 257 := rfl
  rw [hSub] at hJoint
  have hT : 0 < (distinctTuples 129 dom).length := by
    rw [distinctTuples_length]; exact fallingFactorial_pos _ _ hdom
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

/-- Concrete duplicate-free `List GoldilocksExt4` sample of size `k` (eliminating `List Unit`). -/
def canonicalExt4Sample (k : Nat) : List GoldilocksExt4 :=
  (List.range k).map (fun i => GoldilocksExt4.embedBase (Goldilocks.ofNat i))

theorem canonicalExt4Sample_length (k : Nat) : (canonicalExt4Sample k).length = k := by
  simp [canonicalExt4Sample]

theorem canonicalExt4Sample_nodup {k : Nat} (hk : k ≤ goldilocksPrime) :
    (canonicalExt4Sample k).Nodup := by
  unfold canonicalExt4Sample
  have hRange := List.nodup_range (n := k)
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

/-- Non-`Unit` `GoldilocksExt4` + positive-slack `[BCIKS20]` satisfiability witness. -/
theorem whir_bciksJohnson_hypotheses_satisfiable :
    ∃ (S : List GoldilocksExt4) (s : WhirStageSpec) (dom : List Nat) (bad : Nat → Bool),
      S.Nodup ∧ 256 ≤ S.length ∧
      s ∈ whirSchedule4Stage .bciksJohnsonClassical128 ∧
      s.numQueries ≤ dom.length ∧
      (512 - (512 / s.johnsonSqrtBlowup + 1)) * dom.length ≤ 512 * countGood bad dom ∧
      countGood bad dom < dom.length :=
  ⟨canonicalExt4Sample 256, ⟨0, 4, 2, 129, 16⟩, List.range 512, fun i => decide (i < 255),
    canonicalExt4Sample_nodup (by decide), by simp [canonicalExt4Sample_length],
    by decide, by decide, by decide +kernel, by decide +kernel⟩

/-! ## 11. Genuine Reed–Solomon + Degree-7 S-Box `RowArithmetization.Lawful` Instance -/

private def decodeSmallFields : Nat → List UInt8 → Option (List (List UInt8))
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => none
  | k + 1, lenByte :: rest =>
    let n := lenByte.toNat
    if n < 128 && n ≤ rest.length then
      match decodeSmallFields k (rest.drop n) with
      | some tl => some (rest.take n :: tl)
      | none => none
    else none

private def decodeSmallMultiFrame : List UInt8 → Option (List (List UInt8))
  | [] => none
  | cntByte :: rest =>
    if cntByte.toNat < 128 then decodeSmallFields cntByte.toNat rest else none

private theorem leb128_of_lt_128 {n : Nat} (hn : n < 128) : leb128 n = [UInt8.ofNat n] := by
  unfold leb128
  cases n with
  | zero => rfl
  | succ k => simp [leb128Aux, hn]

private theorem uint8_toNat_of_lt_128 {n : Nat} (hn : n < 128) :
    (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

private theorem decodeSmallFields_encodeByteFields :
    ∀ (fields : List (List UInt8)),
      (∀ f ∈ fields, f.length < 128) →
      decodeSmallFields fields.length (encodeByteFields fields) = some fields
  | [], _ => rfl
  | f :: fs, hSmall => by
    have hf : f.length < 128 := hSmall f (.head _)
    have hRest := decodeSmallFields_encodeByteFields fs (fun g hg => hSmall g (.tail _ hg))
    simp only [List.length_cons, encodeByteFields, encodeListField, leb128_of_lt_128 hf,
      List.singleton_append, List.cons_append, decodeSmallFields]
    rw [uint8_toNat_of_lt_128 hf]
    have hLe : f.length ≤ (f ++ encodeByteFields fs).length := by simp
    have hDrop : (f ++ encodeByteFields fs).drop f.length = encodeByteFields fs :=
      List.drop_left' rfl
    have hTake : (f ++ encodeByteFields fs).take f.length = f :=
      List.take_left' rfl
    simp only [hf, hLe, decide_true, Bool.and_self, ↓reduceIte, hDrop, hRest, hTake]

private theorem decodeSmallMultiFrame_encodeMultiFrame (fields : List (List UInt8))
    (hCnt : fields.length < 128) (hSmall : ∀ f ∈ fields, f.length < 128) :
    decodeSmallMultiFrame (encodeMultiFrame fields) = some fields := by
  simp only [encodeMultiFrame, leb128_of_lt_128 hCnt, List.singleton_append,
    decodeSmallMultiFrame, uint8_toNat_of_lt_128 hCnt, hCnt, ↓reduceIte]
  exact decodeSmallFields_encodeByteFields fields hSmall

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
  match decodeSmallMultiFrame pre with
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

/-- Exact equivalence between `verifyPqHashSig` on `mkSbox7Sig x0` and the degree-7 field equation
    `x0^7 + seed = root` in `Goldilocks`! -/
theorem verifyPqHashSig_sbox7_iff (seed root x0 : Goldilocks) (msg : List UInt8) :
    verifyPqHashSig sbox7FieldSuite sbox7Params (mkSbox7Pk seed root) msg (mkSbox7Sig x0) =
      decide (CommRingOps.add (pow7Goldilocks x0) seed = root) := by
  have hWf : sbox7Params.wellFormed = true := by decide
  have hHmsg : ∀ (mu : List UInt8),
      let hmsg := thHashMsg sbox7FieldSuite [] (be 32 seed.val) (be 32 root.val) mu 0 0 0 0
      extractBaseWDigits 2 2 hmsg = [0, 1] := by
    intro mu
    have hCall0 : thCall sbox7FieldSuite tagHMsg (be 32 seed.val)
        ⟨0, 0, .wotsHash, 0, 0, 0⟩ [[], be 32 root.val, mu, be 4 0] = 0x40 :: be 31 0 := by
      unfold thCall sbox7FieldSuite sbox7RawHash thPreimage
      dsimp only
      cases hDec : decodeSmallMultiFrame
        (encodeMultiFrame [tagHMsg, be 32 seed.val, encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩,
          [], be 32 root.val, mu, be 4 0]) with
      | none => rfl
      | some fs =>
        have hInj : fs.length = 7 := by
          -- If decodeSmallMultiFrame succeeded on 7 fields, cntByte = 7, so fs.length = 7!
          unfold encodeMultiFrame at hDec
          have h7 : leb128 ([tagHMsg, be 32 seed.val, encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩,
              [], be 32 root.val, mu, be 4 0].length) = [7] := rfl
          rw [h7, List.singleton_append] at hDec
          unfold decodeSmallMultiFrame at hDec
          simp only [show (7 : UInt8).toNat = 7 from rfl, show 7 < 128 by decide, ↓reduceIte] at hDec
          have hLenAux : ∀ (k : Nat) (bs : List UInt8) (out : List (List UInt8)),
              decodeSmallFields k bs = some out → out.length = k := by
            intro k
            induction k with
            | zero =>
              intro bs out hd
              cases bs <;> simp [decodeSmallFields] at hd
              subst hd; rfl
            | succ k ih =>
              intro bs out hd
              cases bs with
              | nil => simp [decodeSmallFields] at hd
              | cons b rest =>
                simp only [decodeSmallFields] at hd
                split at hd
                · split at hd
                  · rename_i tl htl
                    simp only [Option.some.injEq] at hd
                    rw [← hd, List.length_cons, ih _ _ htl]
                  · cases hd
                · cases hd
          exact hLenAux 7 _ fs hDec
        cases fs with
        | nil => cases hInj
        | cons f0 r1 => cases r1 with
          | nil => cases hInj
          | cons f1 r2 => cases r2 with
            | nil => cases hInj
            | cons f2 r3 => cases r3 with
              | nil => cases hInj
              | cons f3 r4 => cases r4 with
                | nil => cases hInj
                | cons f4 r5 => cases r5 with
                  | nil => cases hInj
                  | cons f5 r6 => simp at hInj; rfl
    show extractBaseWDigits 2 2
      (thCall sbox7FieldSuite tagHMsg (be 32 seed.val) ⟨0, 0, .wotsHash, 0, 0, 0⟩
        [[], be 32 root.val, mu, be 4 0] ++
       thCall sbox7FieldSuite tagHMsg (be 32 seed.val) ⟨0, 0, .wotsHash, 0, 1, 0⟩
        [[], be 32 root.val, mu, be 4 0]) = [0, 1]
    rw [hCall0]
    decide
  have hChain : thChainF sbox7FieldSuite (be 32 seed.val) ⟨0, 0, .wotsHash, 0, 0, 0⟩
      (be 32 x0.val) = be 32 (CommRingOps.add (pow7Goldilocks x0) seed).val := by
    unfold thChainF thCall sbox7FieldSuite sbox7RawHash thPreimage
    dsimp only
    have hFields := decodeSmallMultiFrame_encodeMultiFrame
      [tagThF, be 32 seed.val, encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩, be 32 x0.val]
      (by decide)
      (fun f hf => by
        rcases List.mem_cons.mp hf with rfl | hf
        · decide
        · rcases List.mem_cons.mp hf with rfl | hf
          · simp [length_be]
          · rcases List.mem_cons.mp hf with rfl | hf
            · rw [encodeAdrs_length]; decide
            · rcases List.mem_cons.mp hf with rfl | hf
              · simp [length_be]
              · cases hf)
    rw [hFields]
    simp only [beq_self_eq_true, ↓reduceIte, goldilocks_ofNat_ofBE_be32]
  let end0 := CommRingOps.add (pow7Goldilocks x0) seed
  have hTl : thTweakTl sbox7FieldSuite (be 32 seed.val) ⟨0, 0, .wotsPk, 0, 0, 0⟩
      [be 32 end0.val, be 32 0] = be 32 end0.val := by
    unfold thTweakTl thCall sbox7FieldSuite sbox7RawHash thPreimage
    dsimp only
    have hFields := decodeSmallMultiFrame_encodeMultiFrame
      [tagThTl, be 32 seed.val, encodeAdrs ⟨0, 0, .wotsPk, 0, 0, 0⟩, be 32 end0.val, be 32 0]
      (by decide)
      (fun f hf => by
        rcases List.mem_cons.mp hf with rfl | hf
        · decide
        · rcases List.mem_cons.mp hf with rfl | hf
          · simp [length_be]
          · rcases List.mem_cons.mp hf with rfl | hf
            · rw [encodeAdrs_length]; decide
            · rcases List.mem_cons.mp hf with rfl | hf
              · simp [length_be]
              · rcases List.mem_cons.mp hf with rfl | hf
                · simp [length_be]
                · cases hf)
    rw [hFields]
    have hZero : Goldilocks.ofNat (ofBE (be 32 0)) = Goldilocks.zero := by
      simpa using goldilocks_ofNat_ofBE_be32 Goldilocks.zero
    simp only [beq_self_eq_true, ↓reduceIte, goldilocks_ofNat_ofBE_be32, hZero]
    rw [show CommRingOps.add end0 Goldilocks.zero = end0 from LawfulCommRing.add_zero end0]
  unfold verifyPqHashSig mkSbox7Pk mkSbox7Sig
  simp only [hWf, Bool.not_true, ↓reduceIte, sbox7Params, ne_eq, not_true_eq_false,
    Nat.mul_zero, Nat.pow_zero, Nat.lt_one_iff, List.isEmpty_nil, Bool.or_false]
  let mu := thPreHash sbox7FieldSuite (be 32 seed.val) (be 32 root.val) msg
  change (match verifyHypertreeLayers sbox7FieldSuite ⟨2, 2, 0, 1, 0, 0, 0, true⟩
      (be 32 seed.val) (be 32 root.val) [] 0 0 mu
      [{ tswCtr := 0, wotsChains := [be 32 x0.val, be 32 0], authPath := [] }] with
    | some computedTopRoot => decide (computedTopRoot = be 32 root.val)
    | none => false) = decide (end0 = root)
  unfold verifyHypertreeLayers
  simp only [Nat.pow_zero, Nat.mod_one, Nat.div_one, UInt32.ofNat_zero, UInt64.ofNat_zero]
  rw [hHmsg mu]
  have hTgt : checkTargetSum 2 2 (PqHashParams.targetSum ⟨2, 2, 0, 1, 0, 0, 0, true⟩) [0, 1] =
      true := by decide
  rw [hTgt]
  simp only [Bool.not_true, ↓reduceIte, List.length_cons, List.length_nil, ne_eq, not_true_eq_false]
  have hRec : recoverWotsPkFromSig sbox7FieldSuite ⟨2, 2, 0, 1, 0, 0, 0, true⟩ (be 32 seed.val)
      0 0 0 [0, 1] [be 32 x0.val, be 32 0] = be 32 end0.val := by
    unfold recoverWotsPkFromSig recoverWotsEndpoints
    have hRange : List.range 2 = [0, 1] := rfl
    rw [hRange]
    simp only [List.map, List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, Nat.sub_self,
      wotsChainSteps]
    rw [hChain, hTl]
  rw [hRec]
  simp only [walkMerkleAuthPath, verifyHypertreeLayers]
  have hb : goldilocksPrime < 256 ^ 32 := by decide
  by_cases hEq : end0 = root
  · simp [hEq]
  · have hNeBe : be 32 end0.val ≠ be 32 root.val := fun hBe =>
      hEq (Goldilocks.ext (be_injective (Nat.lt_trans end0.isLt hb) (Nat.lt_trans root.isLt hb) hBe))
    simp [hEq, hNeBe]

/-- Primitive 8th root of unity in `Goldilocks` (`(2^24)^4 = 2^96 ≡ -1 (mod p)`). -/
def omega8 : Goldilocks := ⟨2 ^ 24, by decide⟩

def invTwoGold : Goldilocks := Goldilocks.inv (Goldilocks.ofNat 2)

def powGold (base : Goldilocks) : Nat → Goldilocks
  | 0 => Goldilocks.one
  | k + 1 => CommRingOps.mul (powGold base k) base

def omega8Domain : List GoldilocksExt4 :=
  (List.range 8).map (fun j => GoldilocksExt4.embedBase (powGold omega8 j))

theorem omega8Domain_nodup : omega8Domain.Nodup := by decide +kernel

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
  let (c0, c1) := recoverLinearCoeffs8 table0
  (List.range 8).all (fun j =>
    table0.getD j GoldilocksExt4.zero ==
      RoundPoly.evalCoeffs [c0, c1] (omega8Domain.getD j GoldilocksExt4.zero))

theorem isLinearBaseRs8_eval_at {table0 : List GoldilocksExt4}
    (h : isLinearBaseRs8 table0 = true) {j : Nat} (hj : j < 8) :
    let (c0, c1) := recoverLinearCoeffs8 table0
    table0.getD j GoldilocksExt4.zero =
      RoundPoly.evalCoeffs [c0, c1] (omega8Domain.getD j GoldilocksExt4.zero) := by
  unfold isLinearBaseRs8 at h
  rcases Bool.and_eq_true_iff.mp h with ⟨_, hAll⟩
  have hMem : j ∈ List.range 8 := List.mem_range.mpr hj
  exact eq_of_beq (List.all_eq_true.mp hAll j hMem)

theorem isLinearBaseRs8_encodeLinearRs8 (a0 a1 : Goldilocks) :
    isLinearBaseRs8 (encodeLinearRs8 a0 a1) = true ∧
    recoverLinearCoeffs8 (encodeLinearRs8 a0 a1) =
      (GoldilocksExt4.embedBase a0, GoldilocksExt4.embedBase a1) := by
  have hTwoInv : CommRingOps.mul (CommRingOps.add GoldilocksExt4.one GoldilocksExt4.one)
      (GoldilocksExt4.embedBase invTwoGold) = GoldilocksExt4.one := by decide +kernel
  have hOmega0 : omega8Domain.getD 0 GoldilocksExt4.zero = GoldilocksExt4.one := by decide +kernel
  have hOmega4 : omega8Domain.getD 4 GoldilocksExt4.zero =
      CommRingOps.neg GoldilocksExt4.one := by decide +kernel
  let c0 := GoldilocksExt4.embedBase a0
  let c1 := GoldilocksExt4.embedBase a1
  have hGet : ∀ j, j < 8 →
      (encodeLinearRs8 a0 a1).getD j GoldilocksExt4.zero =
        RoundPoly.evalCoeffs [c0, c1] (omega8Domain.getD j GoldilocksExt4.zero) := by
    intro j hj
    have hjDom : j < omega8Domain.length := by simpa [omega8Domain] using hj
    have hjEnc : j < (encodeLinearRs8 a0 a1).length := by simpa [encodeLinearRs8] using hjDom
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjEnc, Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjDom, Option.getD_some]
    simp [encodeLinearRs8]
  have ht0 : (encodeLinearRs8 a0 a1).getD 0 GoldilocksExt4.zero = CommRingOps.add c0 c1 := by
    rw [hGet 0 (by decide), hOmega0]
    simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
      LawfulCommRing.one_mul]
  have ht4 : (encodeLinearRs8 a0 a1).getD 4 GoldilocksExt4.zero = CommRingOps.sub c0 c1 := by
    rw [hGet 4 (by decide), hOmega4]
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rw [LawfulCommRing.neg_mul, LawfulCommRing.one_mul, ← LawfulCommRing.sub_eq_add_neg]
  have hRec : recoverLinearCoeffs8 (encodeLinearRs8 a0 a1) = (c0, c1) := by
    unfold recoverLinearCoeffs8
    rw [ht0, ht4]
    have hSum : CommRingOps.add (CommRingOps.add c0 c1) (CommRingOps.sub c0 c1) =
        CommRingOps.mul c0 (CommRingOps.add GoldilocksExt4.one GoldilocksExt4.one) := by
      rw [LawfulCommRing.left_distrib, LawfulCommRing.mul_one,
          LawfulCommRing.sub_eq_add_neg c0 c1, LawfulCommRing.add_add_add_comm,
          LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
    have hDiff : CommRingOps.sub (CommRingOps.add c0 c1) (CommRingOps.sub c0 c1) =
        CommRingOps.mul c1 (CommRingOps.add GoldilocksExt4.one GoldilocksExt4.one) := by
      apply LawfulCommRing.add_left_cancel (a := CommRingOps.sub c0 c1)
      rw [LawfulCommRing.add_sub_cancel_left, LawfulCommRing.left_distrib,
          LawfulCommRing.mul_one, LawfulCommRing.sub_eq_add_neg c0 c1,
          LawfulCommRing.add_add_add_comm, LawfulCommRing.neg_add_cancel_left]
    rw [hSum, hDiff, LawfulCommRing.mul_assoc c0, LawfulCommRing.mul_assoc c1,
        hTwoInv, LawfulCommRing.mul_one, LawfulCommRing.mul_one]
  refine ⟨?_, hRec⟩
  unfold isLinearBaseRs8
  rw [hRec]
  have hLen : ((encodeLinearRs8 a0 a1).length == 8) = true := by simp [encodeLinearRs8, omega8Domain]
  have hBaseAll : (encodeLinearRs8 a0 a1).all GoldilocksExt4.isBase = true := by
    apply List.all_eq_true.mpr
    intro z hz
    simp only [encodeLinearRs8, omega8Domain, List.mem_map, List.mem_range] at hz
    obtain ⟨j, _, rfl⟩ := hz
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rw [← GoldilocksExt4.embedBase_mul, ← GoldilocksExt4.embedBase_add]
    exact GoldilocksExt4.isBase_embedBase _
  have hEvalAll : (List.range 8).all (fun j =>
      (encodeLinearRs8 a0 a1).getD j GoldilocksExt4.zero ==
        RoundPoly.evalCoeffs [c0, c1] (omega8Domain.getD j GoldilocksExt4.zero)) = true := by
    apply List.all_eq_true.mpr
    intro j hj
    exact beq_iff_eq.mpr (hGet j (List.mem_range.mp hj))
  simp [hLen, hBaseAll, hEvalAll]

private theorem getD_set_ne {α : Type} (l : List α) (idx j : Nat) (v dflt : α) (hne : j ≠ idx) :
    (l.set idx v).getD j dflt = l.getD j dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm hne)]

private theorem getD_set_eq {α : Type} (l : List α) (idx : Nat) (v dflt : α)
    (hlt : idx < l.length) : (l.set idx v).getD idx dflt = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlt, Option.getD_some]

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
  let p1 := [ (recoverLinearCoeffs8 table0).1, (recoverLinearCoeffs8 table0).2 ]
  let p2 := [ (recoverLinearCoeffs8 (table0.set idx v')).1,
              (recoverLinearCoeffs8 (table0.set idx v')).2 ]
  let j1 := if idx = 0 then 1 else 0
  let j2 := if idx = 0 then 2 else if idx = 1 then 2 else 1
  have hj1Lt : j1 < 8 := by dsimp [j1]; split <;> omega
  have hj2Lt : j2 < 8 := by dsimp [j2]; split <;> try split <;> omega
  have hj1Ne : j1 ≠ idx := by dsimp [j1]; split <;> omega
  have hj2Ne : j2 ≠ idx := by dsimp [j2]; split <;> try split <;> omega
  let x1 := omega8Domain.getD j1 GoldilocksExt4.zero
  let x2 := omega8Domain.getD j2 GoldilocksExt4.zero
  have hxNe : x1 ≠ x2 := by
    dsimp [x1, x2, j1, j2]
    if h0 : idx = 0 then
      simp only [h0, ↓reduceIte]; decide +kernel
    else if h1 : idx = 1 then
      simp only [h0, h1, ↓reduceIte]; decide +kernel
    else
      simp only [h0, h1, ↓reduceIte]; decide +kernel
  have hNd2 : [x1, x2].Nodup := by simp [hxNe]
  have hAgree1 : RoundPoly.evalCoeffs p1 x1 = RoundPoly.evalCoeffs p2 x1 := by
    have e1 := isLinearBaseRs8_eval_at hValid hj1Lt
    have e2 := isLinearBaseRs8_eval_at hBad hj1Lt
    rw [getD_set_ne _ _ _ _ _ hj1Ne] at e2
    exact e1.symm.trans e2
  have hAgree2 : RoundPoly.evalCoeffs p1 x2 = RoundPoly.evalCoeffs p2 x2 := by
    have e1 := isLinearBaseRs8_eval_at hValid hj2Lt
    have e2 := isLinearBaseRs8_eval_at hBad hj2Lt
    rw [getD_set_ne _ _ _ _ _ hj2Ne] at e2
    exact e1.symm.trans e2
  have hDisagreeIdx : RoundPoly.evalCoeffs p1 (omega8Domain.getD idx GoldilocksExt4.zero) ≠
      RoundPoly.evalCoeffs p2 (omega8Domain.getD idx GoldilocksExt4.zero) := by
    have e1 := isLinearBaseRs8_eval_at hValid hIdx
    have e2 := isLinearBaseRs8_eval_at hBad hIdx
    rw [getD_set_eq table0 idx v' GoldilocksExt4.zero (hLen8 ▸ hIdx)] at e2
    rw [← e1, ← e2]
    exact fun hEq => hMut hEq.symm
  have hRoots := ext4_poly_roots_le_degree 1 p1 p2 [x1, x2] hNd2 (by simp [p1]) (by simp [p2])
    ⟨omega8Domain.getD idx GoldilocksExt4.zero, hDisagreeIdx⟩
  simp only [List.filter, hAgree1, hAgree2, decide_true, List.length_cons, List.length_nil] at hRoots
  omega

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
        LawfulCommRing.mul_comm c x, LawfulCommRing.mul_assoc]

theorem evalCoeffs_polyMul :
    ∀ (ps qs : List GoldilocksExt4) (x : GoldilocksExt4),
      RoundPoly.evalCoeffs (polyMul ps qs) x =
        CommRingOps.mul (RoundPoly.evalCoeffs ps x) (RoundPoly.evalCoeffs qs x)
  | [], qs, x => by simp [polyMul, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | p :: ps, qs, x => by
    simp only [polyMul, evalCoeffs_polyAdd, evalCoeffs_polyScale,
      RoundPoly.evalCoeffs, evalCoeffs_polyMul ps qs x]
    rw [LawfulCommRing.zero_add, LawfulCommRing.right_distrib, LawfulCommRing.mul_assoc]

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
  | p :: p2 :: ps, qs, 0, _, hp, _ => by simp at hp; omega
  | p :: p2 :: ps, qs, m + 1, n, hp, hq => by
    have ih := length_polyMul_le (p2 :: ps) qs m n (by simp at hp ⊢; omega) hq
    simp only [polyMul, length_polyAdd, length_polyScale, List.length_cons]
    exact Nat.max_le.mpr ⟨by omega, by omega⟩

/-- Honest degree-8 row gate polynomial `(1 - Y) * ((c0 + c1 * Y)^7 + seed - root)` (`length ≤ 9`). -/
def honestSbox7RoundPoly (seed root : Goldilocks) (table0 : List GoldilocksExt4) :
    List GoldilocksExt4 :=
  let (c0, c1) := recoverLinearCoeffs8 table0
  let lin := [c0, c1]
  let lin2 := polyMul lin lin
  let lin4 := polyMul lin2 lin2
  let lin6 := polyMul lin4 lin2
  let lin7 := polyMul lin6 lin
  let gate7 := polyAdd lin7 [GoldilocksExt4.embedBase (CommRingOps.sub seed root)]
  let sel0 := [GoldilocksExt4.one, CommRingOps.neg GoldilocksExt4.one]
  polyMul sel0 gate7

theorem honestSbox7RoundPoly_length_le_9 (seed root : Goldilocks) (table0 : List GoldilocksExt4) :
    (honestSbox7RoundPoly seed root table0).length ≤ 9 := by
  unfold honestSbox7RoundPoly
  dsimp only
  have l1 : [ (recoverLinearCoeffs8 table0).1, (recoverLinearCoeffs8 table0).2 ].length ≤ 1 + 1 := by simp
  have l2 := length_polyMul_le _ _ 1 1 l1 l1
  have l4 := length_polyMul_le _ _ 2 2 l2 l2
  have l6 := length_polyMul_le _ _ 4 2 l4 l2
  have l7 := length_polyMul_le _ _ 6 1 l6 l1
  have lg7 : (polyAdd _ [GoldilocksExt4.embedBase (CommRingOps.sub seed root)]).length ≤ 7 + 1 := by
    rw [length_polyAdd]; exact Nat.max_le.mpr ⟨l7, by simp⟩
  exact length_polyMul_le _ _ 1 7 (by simp) lg7

theorem honestSbox7RoundPoly_eval (seed root : Goldilocks) (table0 : List GoldilocksExt4)
    (y : GoldilocksExt4) :
    let (c0, c1) := recoverLinearCoeffs8 table0
    let py := CommRingOps.add c0 (CommRingOps.mul y c1)
    RoundPoly.evalCoeffs (honestSbox7RoundPoly seed root table0) y =
      CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one y)
        (CommRingOps.add (pow7Ext4 py)
          (GoldilocksExt4.embedBase (CommRingOps.sub seed root))) := by
  unfold honestSbox7RoundPoly
  dsimp only
  simp only [evalCoeffs_polyMul, evalCoeffs_polyAdd, RoundPoly.evalCoeffs,
    LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [LawfulCommRing.mul_neg, LawfulCommRing.mul_one, ← LawfulCommRing.sub_eq_add_neg]
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
  invTwoY0 := fun _ g => CommRingOps.mul invTwoGold (Goldilocks.inv (powGold omega8 g))
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
  regime := .habr24Qrom128
  message := msg
  committee := [mkSbox7Pk seed root]
  signingModeDigest := "QSAG.SBOX7.MODE/v2".toUTF8.toList

def rsSbox7TraceArith (seed root : Goldilocks) : RowArithmetization where
  decodeSigs := decodeSbox7Sigs
  honestClaim := fun table0 =>
    let p := honestSbox7RoundPoly seed root table0
    CommRingOps.add (RoundPoly.evalCoeffs p GoldilocksExt4.zero)
                    (RoundPoly.evalCoeffs p GoldilocksExt4.one)
  honestRound := fun table0 _ => honestSbox7RoundPoly seed root table0
  terminal := fun finalWord rowChallenges _ =>
    let r0 := rowChallenges.headD GoldilocksExt4.zero
    let pr0 := finalWord.getD 0 GoldilocksExt4.zero
    CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one r0)
      (CommRingOps.add (pow7Ext4 pr0)
        (GoldilocksExt4.embedBase (CommRingOps.sub seed root)))
  isStageCodeword := fun pos w =>
    if pos = 0 then isLinearBaseRs8 w
    else isConstExt4Rs 16 w
  isFinalCodeword := isConstExt4Rs 8

private theorem foldDuetExt4_const (v : GoldilocksExt4) (twY : Goldilocks)
    (r : GoldilocksExt4) :
    foldDuetExt4 v v twY invTwoGold r = v := by
  have hTwoInv : CommRingOps.mul (CommRingOps.add GoldilocksExt4.one GoldilocksExt4.one)
      (GoldilocksExt4.embedBase invTwoGold) = GoldilocksExt4.one := by decide +kernel
  have hSum : CommRingOps.add v v =
      CommRingOps.mul v (CommRingOps.add GoldilocksExt4.one GoldilocksExt4.one) := by
    rw [LawfulCommRing.left_distrib, LawfulCommRing.mul_one]
  unfold foldDuetExt4
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
    have hjEnc : j < (encodeLinearRs8 a0 a1).length := by simpa [encodeLinearRs8] using hjDom
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjEnc, Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjDom, Option.getD_some]
    simp [encodeLinearRs8, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  have hNeg : omega8Domain.getD (g + 4) GoldilocksExt4.zero = CommRingOps.neg wg := by
    dsimp only [wg]
    rcases g with _ | _ | _ | _ | g
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · omega
  have hTw : CommRingOps.mul (CommRingOps.add wg wg)
      (GoldilocksExt4.embedBase (sbox7Stage0Dom.invTwoY0 0 g)) = GoldilocksExt4.one := by
    dsimp only [wg]
    rcases g with _ | _ | _ | _ | g
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · omega
  have hTwoInv : CommRingOps.mul (CommRingOps.add GoldilocksExt4.one GoldilocksExt4.one)
      (GoldilocksExt4.embedBase invTwoGold) = GoldilocksExt4.one := by decide +kernel
  rw [hGet g (by omega), hGet (g + 4) (by omega), hNeg]
  have hAdd : CommRingOps.add (CommRingOps.add c0 (CommRingOps.mul wg c1))
      (CommRingOps.add c0 (CommRingOps.mul (CommRingOps.neg wg) c1)) =
      CommRingOps.mul c0 (CommRingOps.add GoldilocksExt4.one GoldilocksExt4.one) := by
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
          | cons _ _ => simp [rsSbox7WhirDomain] at hLen
    obtain ⟨st0, st1, rfl⟩ := hTblShape
    have hPrfShape : ∃ sp0 sp1, proof.stages = [sp0, sp1] := by
      cases hP : proof.stages with
      | nil => rw [hP] at hVerWhir; simp [rsSbox7WhirDomain, verifyWhirStages] at hVerWhir
      | cons sp0 r1 =>
        cases r1 with
        | nil => rw [hP] at hVerWhir; simp [rsSbox7WhirDomain, verifyWhirStages] at hVerWhir
        | cons sp1 r2 =>
          cases r2 with
          | nil => exact ⟨sp0, sp1, rfl⟩
          | cons _ _ =>
            rw [hP] at hVerWhir; simp [rsSbox7WhirDomain, verifyWhirStages] at hVerWhir
    obtain ⟨sp0, sp1, hStagesEq⟩ := hPrfShape
    rw [hStagesEq] at hVerWhir hAllCons
    simp only [rsSbox7WhirDomain, verifyWhirStages, Bool.and_eq_true] at hVerWhir
    have hFold0 := unpack_stage_foldChallenges hVerWhir.1
    have hFold1 := unpack_stage_foldChallenges hVerWhir.2
    simp only [sbox7Stage0Dom] at hFold0
    simp only [sbox7Stage1Dom] at hFold1
    have hChallShape : ∃ r0, proof.agg.challenges = [r0] ∧ sp0.foldChallenges = [r0] := by
      cases hC : proof.agg.challenges with
      | nil => rw [hFold0.1, hC] at hFold0; cases hFold0.2
      | cons r0 rs =>
        cases rs with
        | nil => exact ⟨r0, rfl, by rw [hFold0.1, hC]⟩
        | cons _ _ => rw [hFold0.1, hC] at hFold0; simp at hFold0
    obtain ⟨r0, hChEq, hFold0Eq⟩ := hChallShape
    have hFold1Shape : ∃ α1, sp1.foldChallenges = [α1] := by
      cases hF1 : sp1.foldChallenges with
      | nil => rw [hF1] at hFold1; cases hFold1.2
      | cons α1 αs =>
        cases αs with
        | nil => exact ⟨α1, rfl⟩
        | cons _ _ => rw [hF1] at hFold1; simp at hFold1
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
    have hTw0 : CommRingOps.mul invTwoGold (Goldilocks.inv (powGold omega8 0)) = invTwoGold := by
      decide +kernel
    rw [hTw0] at hCons0
    have hT1_0 : table1.getD 0 GoldilocksExt4.zero =
        CommRingOps.add (recoverLinearCoeffs8 table0).1
          (CommRingOps.mul r0 (recoverLinearCoeffs8 table0).2) := hCons0.2.2
    have hCw1 : isConstExt4Rs 16 table1 = true := by
      simpa [rsSbox7TraceArith, table1] using hAllCw 1 sbox7Stage1Dom [table1] rfl (by simp [hSt1Eq])
    have hT1_8 : table1.getD 8 GoldilocksExt4.zero = table1.getD 0 GoldilocksExt4.zero :=
      isConstExt4Rs_eq_head hCw1 (by decide)
    simp only [sbox7Stage1Dom, stageTableTrajectoryOk, stageTerminalTableOk,
      finalValueOk, expectedSlotOk, Nat.zero_mod, Nat.zero_div, Nat.zero_add,
      Bool.and_eq_true, decide_eq_true_eq] at hCons1
    rw [hT1_8, foldDuetExt4_const] at hCons1
    have hFinal0 : proof.finalWord.getD 0 GoldilocksExt4.zero =
        CommRingOps.add (recoverLinearCoeffs8 table0).1
          (CommRingOps.mul r0 (recoverLinearCoeffs8 table0).2) := by
      rw [List.getD_eq_getElem?_getD, hCons1.2.2, Option.getD_some, hT1_0]
    simp only [List.headD_cons, hSt0Eq, hChEq, adaptivePolys, adaptivePolysAux,
      rsSbox7TraceArith, verifySumcheckChain, verifySumcheckChainDeg]
    have hDeg := honestSbox7RoundPoly_length_le_9 seed root table0
    have hEv := honestSbox7RoundPoly_eval seed root table0 r0
    simp only [hDeg, decide_true, beq_self_eq_true, Bool.and_self, Bool.true_and, hFinal0]
    exact beq_iff_eq.mpr hEv
  sound table0 bitmap hCode0 hBmLen hSigsFalse := by
    cases bitmap with
    | nil => simp [rsSbox7Inst] at hBmLen
    | cons b0 bs =>
      cases bs with
      | cons _ _ => simp [rsSbox7Inst] at hBmLen
      | nil =>
        simp only [rsSbox7Inst, rsSbox7TraceArith, decodeSbox7Sigs,
          checkAllActiveSigners, Bool.and_true] at hSigsFalse
        cases b0 with
        | false => simp at hSigsFalse
        | true =>
          simp only [↓reduceIte, verifyPqHashSig_sbox7_iff, decide_eq_false_iff_not] at hSigsFalse
          have hBaseAll : table0.all GoldilocksExt4.isBase = true ∧ table0.length = 8 := by
            simp only [RowArithmetization.isRound0Codeword, rsSbox7TraceArith, ↓reduceIte,
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
          let c0 := (recoverLinearCoeffs8 table0).1
          have hc0Base : c0 = GoldilocksExt4.embedBase c0.c0.c0 := by
            apply GoldilocksExt4.eq_embedBase_of_isBase
            dsimp only [c0, recoverLinearCoeffs8]
            rw [GoldilocksExt4.eq_embedBase_of_isBase ht0Base,
                GoldilocksExt4.eq_embedBase_of_isBase ht4Base,
                ← GoldilocksExt4.embedBase_add, ← GoldilocksExt4.embedBase_mul]
            exact GoldilocksExt4.isBase_embedBase _
          intro hZero
          simp only [rsSbox7TraceArith] at hZero
          rw [honestSbox7RoundPoly_eval seed root table0 GoldilocksExt4.zero,
              honestSbox7RoundPoly_eval seed root table0 GoldilocksExt4.one] at hZero
          have hSub0 : CommRingOps.sub GoldilocksExt4.one GoldilocksExt4.zero =
              GoldilocksExt4.one := by
            rw [LawfulCommRing.sub_eq_add_neg]
            decide +kernel
          rw [LawfulCommRing.sub_self GoldilocksExt4.one,
              LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
              LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
              hSub0, LawfulCommRing.one_mul] at hZero
          change CommRingOps.add (pow7Ext4 c0)
            (GoldilocksExt4.embedBase (CommRingOps.sub seed root)) =
            GoldilocksExt4.embedBase Goldilocks.zero at hZero
          rw [hc0Base, ← embedBase_pow7, ← GoldilocksExt4.embedBase_add] at hZero
          have hBaseEq := GoldilocksExt4.embedBase_injective hZero
          apply hSigsFalse
          apply LawfulCommRing.add_left_cancel (a := CommRingOps.neg root)
          rw [LawfulCommRing.add_comm (CommRingOps.neg root) root,
              LawfulCommRing.add_right_neg,
              LawfulCommRing.add_comm (CommRingOps.neg root) _,
              ← LawfulCommRing.add_assoc (pow7Goldilocks c0.c0.c0) seed _,
              ← LawfulCommRing.sub_eq_add_neg seed root]
          exact hBaseEq

/-! ## 12. End-to-End 2-Stage WHIR Prover Witness & `#tooth` Regressions -/

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
        have e1 : 2 * (idx / 2) + 1 = idx + 1 := by omega
        simp [hPar, e0, e1]
      · have e0 : 2 * (idx / 2) = idx - 1 := by omega
        have e1 : 2 * (idx / 2) + 1 = idx := by omega
        simp [hPar, e0, e1]
    rw [hNode]
    exact buildMerklePathByDepth_root H d (hashPairLayer H leafAt) (idx / 2) hDiv

/-- Constructive end-to-end 2-stage `GoldilocksExt4` WHIR prover for `rsSbox7TraceArith`. -/
def buildHonestSbox7WhirBundle (seed x0 b1 : Goldilocks) (msg : List UInt8) :
    SuccinctAggregateProof × List UInt8 × SuccinctExtractionView :=
  let root := CommRingOps.add (pow7Goldilocks x0) seed
  let inst := rsSbox7Inst seed root msg
  let table0 := encodeLinearRs8 x0 b1
  let leaf0 : Nat → List UInt8 := fun g =>
    pcsMerkleHash (duetLeafFrame 0 0 g
      (table0.getD g GoldilocksExt4.zero) (table0.getD (g + 4) GoldilocksExt4.zero))
  let root0 := buildMerkleRootByDepth pcsMerkleHash 2 leaf0
  let pRow := honestSbox7RoundPoly seed root table0
  let aggStub : AggregatedSignature :=
    { suite := sbox7FieldSuite, params := sbox7Params, regime := .habr24Qrom128,
      bitmap := [true], signerCount := 1, traceCommitment := root0,
      claimedSum := GoldilocksExt4.zero, roundPolys := [], challenges := [],
      terminalEval := GoldilocksExt4.zero, childrenCommitment := none }
  let fs := aggregateInstanceFrame inst aggStub
  let rowChalls := deriveRowSumcheckChallenges fs [pRow]
  let r0 := rowChalls.headD GoldilocksExt4.zero
  let pr0 := CommRingOps.add (GoldilocksExt4.embedBase x0)
    (CommRingOps.mul r0 (GoldilocksExt4.embedBase b1))
  let termEval := RoundPoly.evalCoeffs pRow r0
  let agg : AggregatedSignature :=
    { suite := sbox7FieldSuite, params := sbox7Params, regime := .habr24Qrom128,
      bitmap := [true], signerCount := 1, traceCommitment := root0,
      claimedSum := GoldilocksExt4.zero, roundPolys := [pRow], challenges := rowChalls,
      terminalEval := termEval, childrenCommitment := none }
  let table1 := List.replicate 16 pr0
  let leaf1 : Nat → List UInt8 := fun g =>
    pcsMerkleHash (duetLeafFrame 1 0 g
      (table1.getD g GoldilocksExt4.zero) (table1.getD (g + 8) GoldilocksExt4.zero))
  let root1 := buildMerkleRootByDepth pcsMerkleHash 3 leaf1
  let finalWord := List.replicate 8 pr0
  let prior0 := rowSumcheckTranscriptTail fs [pRow]
  let ood0 := deriveStageOodChallenge prior0 root0
  let oodEval0 := CommRingOps.add (GoldilocksExt4.embedBase x0)
    (CommRingOps.mul ood0 (GoldilocksExt4.embedBase b1))
  let sp0Pre : WhirStageProof :=
    { stageRoot := root0, oodChallenge := ood0, oodEval := oodEval0,
      shiftClaim := GoldilocksExt4.zero, shiftPolys := [[GoldilocksExt4.zero]],
      layerRoots := [], shiftChallenges := [], foldChallenges := [],
      shiftTerminalEval := GoldilocksExt4.zero, powNonce := 0, queries := [] }
  let shiftCh0 := deriveStageShiftChallenges (stagePostOodTranscript prior0 sp0Pre)
    [root0] [[GoldilocksExt4.zero]]
  let pSeed0 := stagePowSeed prior0 sp0Pre (some root1) finalWord
  let qSeed0 := stageQuerySeed pSeed0 0
  let qIdx0 := deriveStageQueryIndices sbox7Stage0Dom qSeed0
  let qs0 := qIdx0.map (fun idx =>
    { index := idx
      layers := [{ v0 := table0.getD idx GoldilocksExt4.zero
                   v1 := table0.getD (idx + 4) GoldilocksExt4.zero
                   path := buildMerklePathByDepth pcsMerkleHash 2 leaf0 idx }]
      nextStageBridge := some
        { v0 := pr0
          v1 := pr0
          path := buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx } })
  let sp0 : WhirStageProof :=
    { sp0Pre with shiftChallenges := shiftCh0, foldChallenges := rowChalls, queries := qs0 }
  let prior1 := qSeed0
  let ood1 := deriveStageOodChallenge prior1 root1
  let sp1Pre : WhirStageProof :=
    { stageRoot := root1, oodChallenge := ood1, oodEval := pr0,
      shiftClaim := GoldilocksExt4.zero, shiftPolys := [[GoldilocksExt4.zero]],
      layerRoots := [], shiftChallenges := [], foldChallenges := [],
      shiftTerminalEval := GoldilocksExt4.zero, powNonce := 0, queries := [] }
  let shiftCh1 := deriveStageShiftChallenges (stagePostOodTranscript prior1 sp1Pre)
    [root1] [[GoldilocksExt4.zero]]
  let pSeed1 := stagePowSeed prior1 sp1Pre none finalWord
  let qSeed1 := stageQuerySeed pSeed1 0
  let qIdx1 := deriveStageQueryIndices sbox7Stage1Dom qSeed1
  let qs1 := qIdx1.map (fun idx =>
    { index := idx
      layers := [{ v0 := pr0
                   v1 := pr0
                   path := buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx }]
      nextStageBridge := none })
  let sp1 : WhirStageProof :=
    { sp1Pre with shiftChallenges := shiftCh1, foldChallenges := shiftCh1, queries := qs1 }
  let authPath : Nat → Nat → Nat → List (List UInt8) := fun stIdx _ g =>
    if stIdx = 0 then buildMerklePathByDepth pcsMerkleHash 2 leaf0 g
    else buildMerklePathByDepth pcsMerkleHash 3 leaf1 g
  ({ agg := agg, stages := [sp0, sp1], finalWord := finalWord },
   fs,
   { allTables := [[table0], [table1]], authPath := authPath })

/-- **Completeness of Honest 2-Stage `GoldilocksExt4` WHIR Prover (`honestSbox7WhirProof_accepts`)**:
    For every valid degree-7 S-box witness `(seed, x0, b1, msg)`, the constructed 2-stage WHIR
    proof passes `verifySuccinctAggregate` and satisfies `StagesBound` with zero `cSHAKE256`
    axioms or shortcuts. -/
theorem honestSbox7WhirProof_accepts (seed x0 b1 : Goldilocks) (msg : List UInt8) :
    let root := CommRingOps.add (pow7Goldilocks x0) seed
    let (proof, fs, view) := buildHonestSbox7WhirBundle seed x0 b1 msg
    verifySuccinctAggregate (rsSbox7TraceArith seed root) rsSbox7WhirDomain
      (rsSbox7Inst seed root msg) proof fs = true ∧
    StagesBound view.authPath rsSbox7WhirDomain.stages view.allTables proof.stages := by
  intro root
  dsimp only [buildHonestSbox7WhirBundle]
  let inst := rsSbox7Inst seed root msg
  let table0 := encodeLinearRs8 x0 b1
  let leaf0 : Nat → List UInt8 := fun g =>
    pcsMerkleHash (duetLeafFrame 0 0 g
      (table0.getD g GoldilocksExt4.zero) (table0.getD (g + 4) GoldilocksExt4.zero))
  let root0 := buildMerkleRootByDepth pcsMerkleHash 2 leaf0
  let pRow := honestSbox7RoundPoly seed root table0
  let aggStub : AggregatedSignature :=
    { suite := sbox7FieldSuite, params := sbox7Params, regime := .habr24Qrom128,
      bitmap := [true], signerCount := 1, traceCommitment := root0,
      claimedSum := GoldilocksExt4.zero, roundPolys := [], challenges := [],
      terminalEval := GoldilocksExt4.zero, childrenCommitment := none }
  let fs := aggregateInstanceFrame inst aggStub
  let rowChalls := deriveRowSumcheckChallenges fs [pRow]
  let r0 := rowChalls.headD GoldilocksExt4.zero
  let pr0 := CommRingOps.add (GoldilocksExt4.embedBase x0)
    (CommRingOps.mul r0 (GoldilocksExt4.embedBase b1))
  let table1 := List.replicate 16 pr0
  let leaf1 : Nat → List UInt8 := fun g =>
    pcsMerkleHash (duetLeafFrame 1 0 g
      (table1.getD g GoldilocksExt4.zero) (table1.getD (g + 8) GoldilocksExt4.zero))
  let root1 := buildMerkleRootByDepth pcsMerkleHash 3 leaf1
  let finalWord := List.replicate 8 pr0
  have hRowChallsEq : rowChalls = [r0] := rfl
  have hRec0 := (isLinearBaseRs8_encodeLinearRs8 x0 b1).2
  have hSumZero : CommRingOps.add (RoundPoly.evalCoeffs pRow GoldilocksExt4.zero)
      (RoundPoly.evalCoeffs pRow GoldilocksExt4.one) = GoldilocksExt4.zero := by
    dsimp only [pRow]
    rw [honestSbox7RoundPoly_eval seed root table0 GoldilocksExt4.zero,
        honestSbox7RoundPoly_eval seed root table0 GoldilocksExt4.one, hRec0]
    have hSub0 : CommRingOps.sub GoldilocksExt4.one GoldilocksExt4.zero =
        GoldilocksExt4.one := by
      rw [LawfulCommRing.sub_eq_add_neg]; decide +kernel
    rw [LawfulCommRing.sub_self GoldilocksExt4.one,
        LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
        LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
        hSub0, LawfulCommRing.one_mul, ← embedBase_pow7, ← GoldilocksExt4.embedBase_add]
    have hBaseZero : CommRingOps.add (pow7Goldilocks x0) (CommRingOps.sub seed root) =
        Goldilocks.zero := by
      dsimp only [root]
      apply LawfulCommRing.add_left_cancel (a := CommRingOps.add (pow7Goldilocks x0) seed)
      rw [LawfulCommRing.add_zero,
          LawfulCommRing.add_comm (pow7Goldilocks x0) (CommRingOps.sub seed _),
          ← LawfulCommRing.add_assoc,
          LawfulCommRing.add_comm (CommRingOps.add (pow7Goldilocks x0) seed) seed,
          LawfulCommRing.add_sub_cancel_left,
          LawfulCommRing.add_comm seed (pow7Goldilocks x0)]
    rw [hBaseZero]
    rfl
  have hTermEq : RoundPoly.evalCoeffs pRow r0 =
      (rsSbox7TraceArith seed root).terminal finalWord rowChalls
        (rowChalls ++ [squeezeExt4Challenge "QSAG.AGG.WHIR.FOLD/v2".toUTF8.toList
          (encodeMultiFrame [stagePostOodTranscript
            (stageQuerySeed (stagePowSeed (rowSumcheckTranscriptTail fs [pRow])
              { stageRoot := root0,
                oodChallenge := deriveStageOodChallenge (rowSumcheckTranscriptTail fs [pRow]) root0,
                oodEval := CommRingOps.add (GoldilocksExt4.embedBase x0)
                  (CommRingOps.mul (deriveStageOodChallenge (rowSumcheckTranscriptTail fs [pRow]) root0)
                    (GoldilocksExt4.embedBase b1)),
                shiftClaim := GoldilocksExt4.zero, shiftPolys := [[GoldilocksExt4.zero]],
                layerRoots := [], shiftChallenges := [], foldChallenges := [],
                shiftTerminalEval := GoldilocksExt4.zero, powNonce := 0, queries := [] }
              (some root1) finalWord) 0)
            { stageRoot := root1,
              oodChallenge := deriveStageOodChallenge
                (stageQuerySeed (stagePowSeed (rowSumcheckTranscriptTail fs [pRow])
                  { stageRoot := root0,
                    oodChallenge := deriveStageOodChallenge (rowSumcheckTranscriptTail fs [pRow]) root0,
                    oodEval := CommRingOps.add (GoldilocksExt4.embedBase x0)
                      (CommRingOps.mul (deriveStageOodChallenge (rowSumcheckTranscriptTail fs [pRow]) root0)
                        (GoldilocksExt4.embedBase b1)),
                    shiftClaim := GoldilocksExt4.zero, shiftPolys := [[GoldilocksExt4.zero]],
                    layerRoots := [], shiftChallenges := [], foldChallenges := [],
                    shiftTerminalEval := GoldilocksExt4.zero, powNonce := 0, queries := [] }
                  (some root1) finalWord) 0) root1,
              oodEval := pr0, shiftClaim := GoldilocksExt4.zero,
              shiftPolys := [[GoldilocksExt4.zero]], layerRoots := [], shiftChallenges := [],
              foldChallenges := [], shiftTerminalEval := GoldilocksExt4.zero,
              powNonce := 0, queries := [] },
            root1, encodePolyExt4 [GoldilocksExt4.zero]])]) := by
    dsimp only [pRow, rsSbox7TraceArith, finalWord]
    rw [honestSbox7RoundPoly_eval seed root table0 r0, hRec0]
    simp [List.replicate_succ]
  have hTable1Get : ∀ j, j < 16 → table1.getD j GoldilocksExt4.zero = pr0 := by
    intro j hj
    have hjLt : j < table1.length := by simpa [table1] using hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjLt, Option.getD_some]
    exact List.getElem_replicate hjLt
  have hFinalGet : ∀ j, j < 8 → finalWord[j]? = some pr0 := by
    intro j hj
    have hjLt : j < finalWord.length := by simpa [finalWord] using hj
    rw [List.getElem?_eq_getElem hjLt, List.getElem_replicate]
  have hDepth4 : merkleDepth 4 = 2 := rfl
  have hDepth8 : merkleDepth 8 = 3 := rfl
  have hBound : StagesBound
      (fun stIdx _ g =>
        if stIdx = 0 then buildMerklePathByDepth pcsMerkleHash 2 leaf0 g
        else buildMerklePathByDepth pcsMerkleHash 3 leaf1 g)
      rsSbox7WhirDomain.stages [[table0], [table1]] _ := by
    refine ⟨by simp, ⟨?_, trivial⟩, by simp, ⟨?_, trivial⟩, trivial⟩
    · intro g hg
      have hg4 : g < 2 ^ 2 := hg
      simp only [sbox7Stage0Dom, ↓reduceIte, hDepth4]
      exact ⟨buildMerklePathByDepth_root pcsMerkleHash 2 leaf0 g hg4,
        buildMerklePathByDepth_length pcsMerkleHash 2 leaf0 g⟩
    · intro g hg
      have hg8 : g < 2 ^ 3 := hg
      simp only [sbox7Stage1Dom, Nat.one_ne_zero, ↓reduceIte, hDepth8]
      exact ⟨buildMerklePathByDepth_root pcsMerkleHash 3 leaf1 g hg8,
        buildMerklePathByDepth_length pcsMerkleHash 3 leaf1 g⟩
  refine ⟨?_, hBound⟩
  unfold verifySuccinctAggregate
  dsimp only [collectAllFoldChallenges, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hFs : fs = aggregateInstanceFrame inst _ := rfl
  have hAlgOk : verifyAggregateAlgebra inst.committee _ = true := by
    unfold verifyAggregateAlgebra
    simp only [inst, rsSbox7Inst, bitmapPopcountSpec, List.length_cons, List.length_nil,
      beq_self_eq_true, Nat.lt_one_iff, pos_iff_ne_zero, ne_eq, Nat.one_ne_zero,
      not_false_eq_true, decide_true, Bool.and_self, Bool.true_and,
      verifySumcheckChain, verifySumcheckChainDeg]
    have hDeg := honestSbox7RoundPoly_length_le_9 seed root table0
    simp [pRow, hRowChallsEq, hDeg, hSumZero]
  have hFinalCw : (rsSbox7TraceArith seed root).isFinalCodeword finalWord = true :=
    isConstExt4Rs_replicate 8 pr0
  rw [decide_eq_true hFs, hAlgOk, decide_eq_true hTermEq.symm, hFinalCw]
  simp only [inst, rsSbox7Inst, decide_true, Bool.true_and, rsSbox7WhirDomain, verifyWhirStages]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · -- Stage 0 verification
    unfold verifyOneWhirStage
    dsimp only [sbox7Stage0Dom, stageAllRoots, stagePowSeed, stagePostOodTranscript,
      stageFoldTranscriptTail, Option.map]
    let pSeed0 := encodeMultiFrame [encodeMultiFrame [encodeMultiFrame
      [rowSumcheckTranscriptTail fs [pRow], root0,
        GoldilocksExt4.encodeBytes32 (CommRingOps.add (GoldilocksExt4.embedBase x0)
          (CommRingOps.mul (deriveStageOodChallenge (rowSumcheckTranscriptTail fs [pRow]) root0)
            (GoldilocksExt4.embedBase b1))),
        GoldilocksExt4.encodeBytes32 GoldilocksExt4.zero],
      root0, encodePolyExt4 [GoldilocksExt4.zero]], root1]
    let qSeed0 := stageQuerySeed pSeed0 0
    have hQp0 := deriveStageQueryIndices_props sbox7Stage0Dom qSeed0 (by decide)
    have hShift0 := verifySumcheckChainDeg_zeroPolys 2
      (deriveStageShiftChallenges _ [root0] [[GoldilocksExt4.zero]])
    simp only [deriveStageShiftChallenges, List.map] at hShift0 ⊢
    have hMapIdx0 : (List.map (fun idx =>
        ({ index := idx,
           layers := [{ v0 := table0.getD idx GoldilocksExt4.zero,
                        v1 := table0.getD (idx + 4) GoldilocksExt4.zero,
                        path := buildMerklePathByDepth pcsMerkleHash 2 leaf0 idx }],
           nextStageBridge := some
             { v0 := pr0, v1 := pr0,
               path := buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx } } : StageQueryOpening))
        (deriveStageQueryIndices sbox7Stage0Dom qSeed0)).map (·.index) =
        deriveStageQueryIndices sbox7Stage0Dom qSeed0 := by
      rw [List.map_map]; exact List.map_id _
    rw [hMapIdx0, hQp0.1]
    have hLenQs0 : (List.map _ (deriveStageQueryIndices sbox7Stage0Dom qSeed0)).length =
        min 4 4 := by
      rw [List.length_map]; exact hQp0.2.1
    rw [decide_eq_true hLenQs0]
    simp only [hRowChallsEq, List.length_cons, List.length_nil, ↓reduceIte, decide_true,
      hShift0, verifyWhirStagePow, Bool.true_and]
    apply List.all_eq_true.mpr
    intro q hq
    obtain ⟨idx, hIdxMem, rfl⟩ := List.mem_map.mp hq
    have hIdxLt : idx < 4 := hQp0.2.2 idx hIdxMem
    have hMod4 : idx % 4 = idx := Nat.mod_eq_of_lt hIdxLt
    have hMod8 : idx % 8 = idx := Nat.mod_eq_of_lt (by omega)
    have hDiv8 : idx / 8 = 0 := Nat.div_eq_of_lt (by omega)
    have hFoldIdx := foldDuetExt4_encodeLinearRs8_all x0 b1 r0 hIdxLt
    have hRootPath0 := buildMerklePathByDepth_root pcsMerkleHash 2 leaf0 idx hIdxLt
    have hLenPath0 := buildMerklePathByDepth_length pcsMerkleHash 2 leaf0 idx
    have hRootPath1 := buildMerklePathByDepth_root pcsMerkleHash 3 leaf1 idx (by omega)
    have hLenPath1 := buildMerklePathByDepth_length pcsMerkleHash 3 leaf1 idx
    have hLeaf1Eq : pcsMerkleHash (duetLeafFrame 1 0 idx pr0 pr0) = leaf1 idx := by
      dsimp only [leaf1]
      rw [hTable1Get idx (by omega), hTable1Get (idx + 8) (by omega)]
    simp only [hIdxLt, decide_true, Bool.true_and, verifyStageTrajectory,
      verifyStageTerminalTarget, sbox7Stage0Dom, sbox7Stage1Dom, expectedSlotOk,
      hMod4, hMod8, hDiv8, hDepth4, hDepth8, hLenPath0, hLenPath1, hRootPath0]
    dsimp only [table0, pr0] at hFoldIdx ⊢
    rw [hFoldIdx, hLeaf1Eq, hRootPath1]
    decide
  · -- Stage 1 verification
    unfold verifyOneWhirStage
    dsimp only [sbox7Stage1Dom, stageAllRoots, stagePowSeed, stagePostOodTranscript,
      stageFoldTranscriptTail, Option.map]
    let prior1 := stageQuerySeed
      (encodeMultiFrame [encodeMultiFrame [encodeMultiFrame
        [rowSumcheckTranscriptTail fs [pRow], root0,
          GoldilocksExt4.encodeBytes32 (CommRingOps.add (GoldilocksExt4.embedBase x0)
            (CommRingOps.mul (deriveStageOodChallenge (rowSumcheckTranscriptTail fs [pRow]) root0)
              (GoldilocksExt4.embedBase b1))),
          GoldilocksExt4.encodeBytes32 GoldilocksExt4.zero],
        root0, encodePolyExt4 [GoldilocksExt4.zero]], root1]) 0
    let pSeed1 := encodeMultiFrame [encodeMultiFrame [encodeMultiFrame
      [prior1, root1, GoldilocksExt4.encodeBytes32 pr0,
        GoldilocksExt4.encodeBytes32 GoldilocksExt4.zero],
      root1, encodePolyExt4 [GoldilocksExt4.zero]], encodePolyExt4 finalWord]
    let qSeed1 := stageQuerySeed pSeed1 0
    have hQp1 := deriveStageQueryIndices_props sbox7Stage1Dom qSeed1 (by decide)
    have hShift1 := verifySumcheckChainDeg_zeroPolys 2
      (deriveStageShiftChallenges _ [root1] [[GoldilocksExt4.zero]])
    simp only [deriveStageShiftChallenges, List.map] at hShift1 ⊢
    have hMapIdx1 : (List.map (fun idx =>
        ({ index := idx,
           layers := [{ v0 := pr0, v1 := pr0,
                        path := buildMerklePathByDepth pcsMerkleHash 3 leaf1 idx }],
           nextStageBridge := none } : StageQueryOpening))
        (deriveStageQueryIndices sbox7Stage1Dom qSeed1)).map (·.index) =
        deriveStageQueryIndices sbox7Stage1Dom qSeed1 := by
      rw [List.map_map]; exact List.map_id _
    rw [hMapIdx1, hQp1.1]
    have hLenQs1 : (List.map _ (deriveStageQueryIndices sbox7Stage1Dom qSeed1)).length =
        min 4 8 := by
      rw [List.length_map]; exact hQp1.2.1
    rw [decide_eq_true hLenQs1]
    simp only [List.length_cons, List.length_nil, Bool.false_eq_true, ↓reduceIte, decide_true,
      hShift1, verifyWhirStagePow, Bool.true_and]
    apply List.all_eq_true.mpr
    intro q hq
    obtain ⟨idx, hIdxMem, rfl⟩ := List.mem_map.mp hq
    have hIdxLt : idx < 8 := hQp1.2.2 idx hIdxMem
    have hMod8 : idx % 8 = idx := Nat.mod_eq_of_lt hIdxLt
    have hRootPath1 := buildMerklePathByDepth_root pcsMerkleHash 3 leaf1 idx hIdxLt
    have hLenPath1 := buildMerklePathByDepth_length pcsMerkleHash 3 leaf1 idx
    have hLeaf1Eq : pcsMerkleHash (duetLeafFrame 1 0 idx pr0 pr0) = leaf1 idx := by
      dsimp only [leaf1]
      rw [hTable1Get idx (by omega), hTable1Get (idx + 8) (by omega)]
    simp only [hIdxLt, decide_true, Bool.true_and, verifyStageTrajectory,
      verifyStageTerminalTarget, finalValueOk, expectedSlotOk,
      hMod8, hDepth8, hLenPath1, foldDuetExt4_const]
    rw [hLeaf1Eq, hRootPath1, hFinalGet idx hIdxLt]
    decide

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
  let msg := "QSAG.AGG.WITNESS.MSG/v2".toUTF8.toList
  let root := CommRingOps.add (pow7Goldilocks x0) seed
  let (proof, fs, view) := buildHonestSbox7WhirBundle seed x0 b1 msg
  have hAcc := honestSbox7WhirProof_accepts seed x0 b1 msg
  refine ⟨rsSbox7TraceArith seed root, rsSbox7WhirDomain, rsSbox7Inst seed root msg,
    rsSbox7TraceArith_lawful seed root msg, proof, fs, view,
    hAcc.1, hAcc.2, ?_, hAcc.2, ?_⟩
  · simp [verifyMergeTree, proof, buildHonestSbox7WhirBundle, hAcc.1]
  · dsimp only [rsSbox7Inst, rsSbox7TraceArith, proof, view, buildHonestSbox7WhirBundle,
      List.headD_cons, checkAllActiveSigners, decodeSbox7Sigs]
    rw [(isLinearBaseRs8_encodeLinearRs8 x0 b1).2]
    simp [GoldilocksExt4.embedBase_c0_c0, verifyPqHashSig_sbox7_iff, root]

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
  unfold verifyOneWhirStage
  simp [decide_eq_false hBad]

/-- `#tooth` `verifyOneWhirStage` rejects invalid Proof-of-Work nonces. -/
theorem tooth_whir_bad_pow_rejected (rowChalls finalWord : List GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextInfo : Option (WhirStageDomain × List UInt8))
    (hBad : verifyWhirStagePow (stagePowSeed prior sp (nextInfo.map Prod.snd) finalWord)
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
  simp [verifyStageTrajectory, verifyStageTerminalTarget, expectedSlotOk,
    decide_eq_false hMismatch.symm]

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

end Aggregation

end Qsag
end

