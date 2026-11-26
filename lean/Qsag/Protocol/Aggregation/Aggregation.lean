module


public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HypertreeEufCma

public import Qsag.Tactic.AssuranceKit

public import Qsag.Math.GoldilocksEncoding
public import Qsag.Math.QuinticExt5

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


namespace Aggregation


/-! ## 5. Unconditional `[BCIKS20]` Johnson WHIR Schedule Ladder -/


/-- Per-stage WHIR rate-escalation specification (`B_s = (4, 16, 64, 256)`). -/
structure WhirStageSpec where
  stageIdx : Nat
  blowup : Nat
  johnsonSqrtBlowup : Nat
  numQueries : Nat
  powBits : Nat
  deriving DecidableEq, Repr


/-- `#tooth`: historical capacity-proximity query counts `[128, 64, 43, 32]` across blowups
    `(4, 16, 64, 256)` (`√B = (2, 4, 8, 16)`) fail the unconditional `[BCIKS20]` Johnson 256-bit
    bound at every stage (`(√B_s)^{q_s} < 2^256` and
    `¬ ((1024 / √B_s + 1)^{q_s} * 2^256 < 1024^{q_s})`). -/
theorem tooth_retired_capacity_queries_fail_johnson_qrom256 :
    ∀ p ∈ ([(2, 128), (4, 64), (8, 43), (16, 32)] : List (Nat × Nat)),
      p.1 ^ p.2 < 2 ^ 256 ∧
      ¬ ((1024 / p.1 + 1) ^ p.2 * 2 ^ 256 < 1024 ^ p.2) := by
  decide +kernel


end Aggregation


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


def ProductionAggParams.maxRowRounds (p : ProductionAggParams) : Nat := p.maxPcsVars - p.logTraceCols
def ProductionAggParams.maxFoldRounds (p : ProductionAggParams) : Nat := p.maxPcsVars - p.earlyStopVars
def ProductionAggParams.maxStage0Domain (p : ProductionAggParams) : Nat := 2 ^ p.maxPcsVars * p.rsBlowup
def ProductionAggParams.maxQueryGroups (p : ProductionAggParams) : Nat :=
  p.maxStage0Domain / 2 ^ p.maxFoldStepVars


namespace Aggregation


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


/-- Honest round polynomials generated adaptively from the challenge prefix. -/
def adaptivePolysAux {α β : Type} (poly : List α → β) : List α → List α → List β
  | _, [] => []
  | pre, r :: rs => poly pre :: adaptivePolysAux poly (r :: pre) rs

def adaptivePolys {α β : Type} (poly : List α → β) (challenges : List α) : List β :=
  adaptivePolysAux poly [] challenges


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


/-- Number of out-of-domain samples squeezed per WHIR stage (`pcs.rs::OOD_SAMPLES = 2`). -/
def whirOodSamples : Nat := 2


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

/-- One draw from a singleton domain fills the query quota before scan-fill. -/
theorem scanFill_sample_singleton (cand : Nat → Nat) (h : cand 0 = 0) :
    scanFillDistinct 1 (List.range 1) (sampleDistinctLoop cand 1 2 0 []) = [0] := by
  simp [List.range_succ, sampleDistinctLoop, sortedInsertDistinct, scanFillDistinct, h]

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


/-! ## 8. Constructive Multi-Stage WHIR Knowledge Soundness & Unforgeability Reduction -/


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


end Aggregation


namespace Aggregation


end Aggregation


namespace Aggregation


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


namespace Aggregation


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


private theorem countGood_lt_range (m : Nat) :
    ∀ (n : Nat), countGood (fun i => decide (i < m)) (List.range n) = min m n
  | 0 => by simp [countGood]
  | n + 1 => by
    rw [countGood, List.range_succ, List.filter_append, List.length_append]
    have ih : (List.filter (fun i => decide (i < m)) (List.range n)).length = min m n :=
      countGood_lt_range m n
    rw [ih]
    by_cases hlt : n < m <;> simp [hlt] <;> omega


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


/-! ## 11. Genuine Reed–Solomon + Degree-7 S-Box `RowArithmetization.Lawful` Instance -/

def decodeLeb128 : List UInt8 → Option (Nat × List UInt8)
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

theorem decodeLeb128_leb128 (n : Nat) (rest : List UInt8) :
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


private theorem omega8_pow_inj {i j : Nat} (hi : i < 8) (hj : j < 8)
    (h : powGold omega8 i = powGold omega8 j) : i = j := by
  have hv : (powGold omega8 i).val = (powGold omega8 j).val := congrArg Goldilocks.val h
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> try omega
  all_goals (rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> try omega)
  all_goals (first | rfl | exact absurd hv (by decide))


private theorem getD_set_ne {α : Type} (l : List α) (idx j : Nat) (v dflt : α) (hne : j ≠ idx) :
    (l.set idx v).getD j dflt = l.getD j dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm hne)]

private theorem getD_set_eq {α : Type} (l : List α) (idx : Nat) (v dflt : α)
    (hlt : idx < l.length) : (l.set idx v).getD idx dflt = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlt, Option.getD_some]


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


private theorem invTwoGold_mul_invOmega8Pow_zero :
    CommRingOps.mul invTwoGold (invOmega8Pow 0) = invTwoGold := by
  decide +kernel


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
        simp only [hPar, ↓reduceIte, e0]
      · have e1 : 2 * (idx / 2) + 1 = idx := by omega
        have e0 : 2 * (idx / 2) = idx - 1 := by omega
        simp only [hPar, ↓reduceIte]
        rw [e1, e0]
    rw [hNode]
    exact buildMerklePathByDepth_root H d (hashPairLayer H leafAt) (idx / 2) hDiv


/-- `#tooth` `strictlyIncreasing` rejects repeated query indices. -/
theorem strictlyIncreasing_rejects_repeat (x : Nat) (xs : List Nat) :
    strictlyIncreasing (x :: x :: xs) = false := by
  simp [strictlyIncreasing]


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


/-! ### Composition through the succinct extractor

A chain carries a separate, instance-bound WHIR proof for each nonlinear round. Its extraction
views bind the recovered input to the preceding public output. This is a composition theorem
for arbitrarily many proofs (nine included), not a claim that one two-stage proof represents
nine S-box rounds, nor a deployed StepOp AIR completeness result.
-/


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


end Aggregation

end Qsag
end


public section

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

public section
namespace Qsag.Aggregation
#export_eqns whirOodSamples
#export_eqns merkleNodeFrame
/-- Kernel KAT for the stage PoW fixture; it does not assert transcript parity. -/
theorem stage_pow_fixture_accepts :
    verifyWhirStagePow (stagePowDigest powWitnessSeed) 70035 16 = true := by
  apply (verifyWhirStagePow_16_iff _ _ (stagePowDigest_length _) (by decide)).mpr
  exact cshake_stage_pow_fixture_70035
theorem stage_pow_fixture_rejects_zero :
    verifyWhirStagePow (stagePowDigest powWitnessSeed) 0 16 = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hx := (verifyWhirStagePow_16_iff _ _ (stagePowDigest_length _) (by decide)).mp h
  have hf := cshake_stage_pow_fixture_0
  exact Bool.false_ne_true (hf.symm.trans hx)
#verify_constructive decodeLeb128_leb128
  verifyWhirStagePow_16_iff stage_pow_fixture_accepts stage_pow_fixture_rejects_zero
end Qsag.Aggregation
end

/-! ### Sbox7 fixture facts

Projection and evaluation lemmas for the sealed Sbox7 fixture family (`rsSbox7Inst`, `mkSbox7Pk`,
`rsSbox7TraceArith`, `rsSbox7WhirDomain`, `buildHonestSbox7WhirBundle`). The recursive-aggregation
fixtures of `Poseidon2AlgebraicAndRecursiveHem` and `RecursivePoseidon2WhirSoundness` cite them; no
body is exposed. -/
public section
namespace Qsag.Aggregation

theorem pow7Goldilocks_zero : pow7Goldilocks Goldilocks.zero = Goldilocks.zero := by
  decide +kernel

theorem sbox7_root_of_zero_preimage (seed : Goldilocks) :
    CommRingOps.add (pow7Goldilocks Goldilocks.zero) seed = seed := by
  rw [pow7Goldilocks_zero]
  exact LawfulCommRing.zero_add seed


theorem sbox7Params_eq : sbox7Params = ⟨2, 2, 0, 1, 0, 0, 0, true⟩ := by rfl

theorem mkSbox7Pk_eq (seed root : Goldilocks) :
    mkSbox7Pk seed root = { pkSeed := be 32 seed.val, pkRoot := be 32 root.val } := by rfl

theorem mkSbox7Pk_zero_ne_one :
    ¬ ((mkSbox7Pk Goldilocks.zero Goldilocks.zero).pkSeed =
      (mkSbox7Pk Goldilocks.one Goldilocks.one).pkSeed) := by
  decide +kernel

theorem rsSbox7WhirDomain_stageIdx_nodup :
    (rsSbox7WhirDomain.stages.map (·.stageIdx)).Nodup := by decide +kernel

theorem rsSbox7WhirDomain_stages_length : rsSbox7WhirDomain.stages.length = 2 := by rfl

theorem rsSbox7WhirDomain_stages_eq :
    rsSbox7WhirDomain.stages = [sbox7Stage0Dom, sbox7Stage1Dom] := by rfl

theorem sbox7StageDoms_fold_shape :
    sbox7Stage0Dom.groups0 = 4 ∧ sbox7Stage0Dom.foldLayers = 1 ∧
      sbox7Stage1Dom.groups0 = 8 ∧ sbox7Stage1Dom.foldLayers = 1 := ⟨rfl, rfl, rfl, rfl⟩


#verify_constructive pow7Goldilocks_zero sbox7_root_of_zero_preimage
  sbox7Params_eq mkSbox7Pk_eq mkSbox7Pk_zero_ne_one
  rsSbox7WhirDomain_stageIdx_nodup rsSbox7WhirDomain_stages_length
  rsSbox7WhirDomain_stages_eq sbox7StageDoms_fold_shape
end Qsag.Aggregation
end
