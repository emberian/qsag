module
/-
# Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness — High-Capacity (`nv ≤ 28`) Flat Schedules & Recursive `Hem` Tree over Real Leaf Shards

The numerical profile bounds below do not instantiate a sampled WHIR RBR certificate.
Their `2^40` conclusions are arithmetic on conditional profile expressions.

1. **§1 High-capacity flat schedules (`nv = 2..28`).** Stage geometry, Johnson witness rows and
   sliced persistence rows extended from `nv ≤ 24` to `nv = 28` (`MAX_PCS_NUM_VARS = 28` in `pcs.rs`):
   `hemHighCapSchedule_covers_nv2_to_28`, `hemHighCap_cdhzPow16_budget_nv2_to_28` (`Q ≤ 2^38`),
   `hemHighCap_unitaryZeroPow_budget_nv2_to_28` (`Q + 1 ≤ 2^40`). Every stage geometry and witness
   row in `25..=28` matches `pcs.rs::stage_geometry` and `affine_schedule.rs::HIGH_CAPACITY_WITNESSES`
   verbatim; `nv ≥ 29` is rejected (`[]`), matching `MAX_PCS_NUM_VARS = 28`.
2. **§2 `Poseidon2` Canopy openings and the child-WHIR relation.** Salted, domain-separated Canopy
   leaves and nodes with collision/opening extraction (`extractPoseidon2CanopyCollisionOrOpening`),
   the authenticated `[CWYZ26]` duet fold (`authenticated_duet_fold_uniquely_determines_claimed`),
   and the sequential Fiat–Shamir transcript of `recursive_whir.rs::Transcript`: frames carry tag and
   length (`FsFrame`, `fsTranscriptBlocks`, injective: `fsTranscriptBlocks_injective`), challenges
   are squeezed from the duplex state after the absorbed prefix (`fsSqueeze`, bound to the frame list
   by `fsSqueeze_binding`), and the child verifier's transcript is the generic replay `fsReplay` of
   `Qsag.Oracle.FiatShamir` over `childWhirRounds` (`childWhirTranscript`,
   `childWhirTranscript_challenge`). `ChildWhirCircuitAccepts` uses only derived challenges.
   Not modelled: out-of-domain rounds, proof-of-work frames, and the multi-query shuffle of
   `recursive_whir.rs::verify_gadget`; the relation opens one antipodal coset of one stage.
3. **§3 Recursive `Hem` tree.** A leaf carries a canonical header (`verifyRecursiveShardHeader`,
   injective: `leafShardHeaderPreimage_injective`), the shard certificate it describes
   (`leafHeaderBindsShard`) and a child-WHIR proof on the header digest; the tree verifier
   `verifyRecursiveHemTree` runs the two-layer root verifier `verifyHierarchicalHem` on the leaf
   shards. `extractRecursiveHemTree` returns real signatures of a quorum of every registered
   committee (`LeafShardQuorumWitness`) or a `HemHierarchyBreak`;
   `recursive_hem_false_statement_yields_forgery_or_break` turns an accepted false statement into
   a forged signature or a break; `recursive_hem_tree_soundness_bound` is the finite-coin union
   bound. A child-WHIR proof exists for every public digest (`mkHonestChildWhirWitness_accepts`)
   and carries no quorum statement: the verifier checks every leaf shard itself, so this tree is
   not succinct in the number of shards. `recursive_hem_all_node_budget_below_2pow128_at_deployment_scales`
   is arithmetic on a budget expression that charges every node.
-/

public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
public import Qsag.Oracle.FiatShamir
import Qsag.Tactic.AssuranceKit
import Qsag.Math.Tactic.CommRing

public section
namespace Qsag

set_option autoImplicit false
set_option Elab.async false

/-! ## §1. High-Capacity Flat Schedules (`nv = 2..28`, up to `2^28` Field Cells / `MAX_PCS_NUM_VARS = 28`) -/


/-- Early-stop variable count for `nv ∈ 2..=28` (coincides with `hemEarlyStopVars` on `2..=28`
    and uses `8` early-stop variables for `25..=28`). -/
def hemHighCapEarlyStopVars (nv : Nat) : Nat :=
  if nv ≤ 24 then hemEarlyStopVars nv else 8



def hemHighCapExtraWitnessRows : List (Nat × Nat × Nat × Nat × Nat) :=
  [ (25, 0, 1054283, 128, 6353),
    (25, 1, 133941, 32, 1732),
    (25, 2, 17483, 16, 586),
    (25, 3, 4482, 16, 1049),
    (26, 0, 2108508, 128, 6359),
    (26, 1, 133940, 32, 1734),
    (26, 2, 17483, 16, 586),
    (26, 3, 4482, 16, 1049),
    (27, 0, 4216959, 128, 6361),
    (27, 1, 267837, 32, 1724),
    (27, 2, 34932, 16, 581),
    (27, 3, 4481, 16, 1056),
    (28, 0, 8433861, 128, 6362),
    (28, 1, 267836, 32, 1724),
    (28, 2, 34932, 16, 581),
    (28, 3, 4481, 16, 1056) ]

/-- Unified 65-row `[CWYZ26]` Johnson witness table covering `nv ∈ 2..=28`. -/
def hemHighCapWitnessTable : List (Nat × Nat × Nat × Nat × Nat) :=
  hemOptimizedQromWitnessTable ++ hemHighCapExtraWitnessRows

def hemHighCapTableRow (nv stage : Nat) : Option (Nat × Nat × Nat × Nat × Nat) :=
  hemHighCapWitnessTable.find? (fun r => r.1 == nv && r.2.1 == stage)


/-- High-capacity `slicedParamsOk` persistence thresholds `(nv, stage, B, bits)` for `nv ∈ 25..=28`,
    certifying `AffineFoldDecompBound` at `bits ≥ 183` on every high-capacity stage. -/
def slicedHighCapExtraTable : List (Nat × Nat × Nat × Nat) :=
  [ (25, 0, 1048579, 186),
    (25, 1, 131078, 196),
    (25, 2, 16396, 204),
    (25, 3, 4120, 203),
    (26, 0, 2097155, 185),
    (26, 1, 131078, 196),
    (26, 2, 16396, 204),
    (26, 3, 4120, 203),
    (27, 0, 4194307, 184),
    (27, 1, 262150, 195),
    (27, 2, 32780, 203),
    (27, 3, 4120, 203),
    (28, 0, 8388611, 183),
    (28, 1, 262150, 195),
    (28, 2, 32780, 203),
    (28, 3, 4120, 203) ]


private theorem sumList_mono_hc {xs ys : List RatBound} (hLen : xs.length = ys.length)
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

private theorem scale_mono_left_hc {a b : Nat} (hab : a ≤ b) (r : RatBound) :
    RatBound.le (RatBound.scale a r) (RatBound.scale b r) := by
  unfold RatBound.le RatBound.scale
  dsimp only
  exact Nat.mul_le_mul_right r.den (Nat.mul_le_mul_right r.num hab)

private theorem scale_mono_right_hc (c : Nat) {r₁ r₂ : RatBound} (h : RatBound.le r₁ r₂) :
    RatBound.le (RatBound.scale c r₁) (RatBound.scale c r₂) := by
  unfold RatBound.le at h
  unfold RatBound.le RatBound.scale
  dsimp only
  rw [Nat.mul_assoc, Nat.mul_assoc]
  exact Nat.mul_le_mul_left c h

private theorem strictlyMoreThanBits_of_le_hc {b : Nat} {r₁ r₂ : RatBound}
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

private theorem powScaledFsQromCompilerBound_mono_hc {Q QMax : Nat} (hQ : Q ≤ QMax)
    (numRoots secBits stagePowBits : Nat) (rbrBounds queryBounds : List RatBound) :
    RatBound.le
      (powScaledFsQromCompilerBound Q numRoots secBits stagePowBits rbrBounds queryBounds)
      (powScaledFsQromCompilerBound QMax numRoots secBits stagePowBits rbrBounds queryBounds) := by
  unfold powScaledFsQromCompilerBound
  have hSq : (2 * Q + 1) ^ 2 ≤ (2 * QMax + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hGr : 8 * (Q + 1) ^ 2 ≤ 8 * (QMax + 1) ^ 2 :=
    Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (by omega) 2)
  apply RatBound.add_le_add
  · apply sumList_mono_hc (by simp)
    intro i; simp only [List.get_eq_getElem, List.getElem_map]
    exact scale_mono_left_hc hSq _
  · apply RatBound.add_le_add
    · unfold qromMerkleOnlineExtractBound
      apply scale_mono_right_hc numRoots
      apply RatBound.add_le_add
      · simp only [quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def]
        unfold RatBound.le
        dsimp only
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
      · simp only [quantumBhtCollisionBound_def]
        unfold RatBound.le
        dsimp only
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
    · apply sumList_mono_hc (by simp)
      intro i; simp only [List.get_eq_getElem, List.getElem_map]
      simp only [quantumGroverGrindingBound_def]
      exact scale_mono_left_hc hGr _

private theorem cdhzSnargEnvelopeBound_mono_hc {Q QMax : Nat} (hQ : Q ≤ QMax)
    (qV logMaxLeaf secBits stagePowBits : Nat) (rbrBounds queryBounds : List RatBound) :
    RatBound.le
      (cdhzSnargEnvelopeBound Q qV logMaxLeaf secBits stagePowBits rbrBounds queryBounds)
      (cdhzSnargEnvelopeBound QMax qV logMaxLeaf secBits stagePowBits rbrBounds queryBounds) := by
  simp only [cdhzSnargEnvelopeBound, cdhzSnargPartitionBound_def]
  apply RatBound.add_le_add
  · apply scale_mono_right_hc 4
    simp only [cdhzPqsrBound_def]
    apply scale_mono_left_hc
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 80 (by omega)) (by omega)
  · apply RatBound.add_le_add
    · apply scale_mono_right_hc 4
      simp only [cdhzSaltedMerkleOfflineBound_def]
      unfold RatBound.le
      dsimp only
      apply Nat.mul_le_mul_right
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 160 hQ) (Nat.pow_le_pow_left (by omega) 2)
    · apply RatBound.add_le_add
      · apply scale_mono_right_hc 4
        simp only [cdhzSaltedMerkleOnlineBound_def]
        unfold RatBound.le
        dsimp only
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 240 hQ) (Nat.pow_le_pow_left (by omega) 2)
      · apply scale_mono_right_hc (2 * qV ^ 2)
        simp only [cdhzSaltedMerkleComBound_def]
        unfold RatBound.le
        dsimp only
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 240 (by omega))


/-! ### Defining equations of the §1 definitions (for modules that do not `import all` this one) -/


theorem hemHighCapEarlyStopVars_def (nv : Nat) :
    hemHighCapEarlyStopVars nv =
  if nv ≤ 24 then hemEarlyStopVars nv else 8 := by
  rfl


theorem hemHighCapExtraWitnessRows_def :
    hemHighCapExtraWitnessRows =
  [ (25, 0, 1054283, 128, 6353),
    (25, 1, 133941, 32, 1732),
    (25, 2, 17483, 16, 586),
    (25, 3, 4482, 16, 1049),
    (26, 0, 2108508, 128, 6359),
    (26, 1, 133940, 32, 1734),
    (26, 2, 17483, 16, 586),
    (26, 3, 4482, 16, 1049),
    (27, 0, 4216959, 128, 6361),
    (27, 1, 267837, 32, 1724),
    (27, 2, 34932, 16, 581),
    (27, 3, 4481, 16, 1056),
    (28, 0, 8433861, 128, 6362),
    (28, 1, 267836, 32, 1724),
    (28, 2, 34932, 16, 581),
    (28, 3, 4481, 16, 1056) ] := by
  rfl

theorem hemHighCapWitnessTable_def :
    hemHighCapWitnessTable =
  hemOptimizedQromWitnessTable ++ hemHighCapExtraWitnessRows := by
  rfl

theorem hemHighCapTableRow_def (nv stage : Nat) :
    hemHighCapTableRow nv stage =
  hemHighCapWitnessTable.find? (fun r => r.1 == nv && r.2.1 == stage) := by
  rfl


theorem slicedHighCapExtraTable_def :
    slicedHighCapExtraTable =
  [ (25, 0, 1048579, 186),
    (25, 1, 131078, 196),
    (25, 2, 16396, 204),
    (25, 3, 4120, 203),
    (26, 0, 2097155, 185),
    (26, 1, 131078, 196),
    (26, 2, 16396, 204),
    (26, 3, 4120, 203),
    (27, 0, 4194307, 184),
    (27, 1, 262150, 195),
    (27, 2, 32780, 203),
    (27, 3, 4120, 203),
    (28, 0, 8388611, 183),
    (28, 1, 262150, 195),
    (28, 2, 32780, 203),
    (28, 3, 4120, 203) ] := by
  rfl


/-! ## §2. Algebraic `Poseidon2` Canopy Merkle Multi-Opening & Recursive Child-WHIR Verifier Relation -/

/-- Domain-separation tag for algebraic `Poseidon2` Canopy Merkle leaves (`"CANOPY_L"`). -/
def poseidon2LeafDomainTag : Goldilocks :=
  Goldilocks.ofNat 0x43414E4F50595F4C

/-- Domain-separation tag for algebraic `Poseidon2` Canopy internal 2-to-1 nodes (`"CANOPY_N"`). -/
def poseidon2NodeDomainTag : Goldilocks :=
  Goldilocks.ofNat 0x43414E4F50595F4E

/-- Domain-separation tag for recursive child-header summary commitments (`"CANOPY_R"`). -/
def poseidon2SummaryDomainTag : Goldilocks :=
  Goldilocks.ofNat 0x43414E4F50595F52

theorem poseidon2Leaf_ne_node_tag : poseidon2LeafDomainTag ≠ poseidon2NodeDomainTag := by
  decide

/-- Algebraic `Poseidon2` rate-8 multi-block sponge compression over a domain-separated initial
    capacity lane `initCap : Lane4` (`width = 12, rate = 8, capacity = 4` = 256 bits). -/
def poseidon2CanopyCompress (initCap : Lane4) (limbStream : List Goldilocks) : Lane4 :=
  let st := absorbLimbStream ⟨lane4Zero, lane4Zero, initCap⟩ (poseidon2Pad limbStream)
  st.b0

/-- Structured input `(initCap, limbStream)` to `poseidon2CanopyCompress`. -/
structure Poseidon2CanopyPreimage where
  initCap : Lane4
  limbStream : List Goldilocks
  deriving DecidableEq, Repr

/-- Explicit collision witness against `poseidon2CanopyCompress`: two distinct domain-separated or
    salted preimages `(initCap₁, limbStream₁) ≠ (initCap₂, limbStream₂)` squeezing to the exact
    same 256-bit 4-limb digest `Lane4`. -/
structure Poseidon2CanopyCollision where
  p1 : Poseidon2CanopyPreimage
  p2 : Poseidon2CanopyPreimage
  hne : p1 ≠ p2
  hcol : poseidon2CanopyCompress p1.initCap p1.limbStream =
         poseidon2CanopyCompress p2.initCap p2.limbStream

/-- Preimage constructor for a salted `Poseidon2` Canopy leaf:
    absorbs the 4-limb 256-bit tree `salt` followed by `payload` under capacity lane
    `⟨poseidon2LeafDomainTag, leafIdx, payload.length, 1⟩`. -/
def canopyLeafPreimage (salt : Lane4) (leafIdx : Goldilocks) (payload : List Goldilocks) :
    Poseidon2CanopyPreimage :=
  { initCap := ⟨poseidon2LeafDomainTag, leafIdx, Goldilocks.ofNat payload.length, Goldilocks.one⟩
    limbStream := [salt.x0, salt.x1, salt.x2, salt.x3] ++ payload }

/-- Salted domain-separated `Poseidon2` Canopy leaf hash (`rate = 8` absorb + 4-limb 256-bit salt). -/
def poseidon2CanopyLeafHash (salt : Lane4) (leafIdx : Goldilocks) (payload : List Goldilocks) :
    Lane4 :=
  let pre := canopyLeafPreimage salt leafIdx payload
  poseidon2CanopyCompress pre.initCap pre.limbStream

/-- Preimage constructor for a salted `Poseidon2` Canopy internal 2-to-1 node at `(level, nodeIdx)`:
    absorbs `salt` (4 limbs) + `left` (4 limbs) + `right` (4 limbs) under capacity lane
    `⟨poseidon2NodeDomainTag, level, nodeIdx, 2⟩`. -/
def canopyNodePreimage (salt : Lane4) (level nodeIdx : Goldilocks) (left right : Lane4) :
    Poseidon2CanopyPreimage :=
  { initCap := ⟨poseidon2NodeDomainTag, level, nodeIdx, Goldilocks.ofNat 2⟩
    limbStream := [salt.x0, salt.x1, salt.x2, salt.x3,
                   left.x0, left.x1, left.x2, left.x3,
                   right.x0, right.x1, right.x2, right.x3] }

/-- Salted domain-separated 2-to-1 `Poseidon2` Canopy internal compression. -/
def poseidon2CanopyNodeHash (salt : Lane4) (level nodeIdx : Goldilocks) (left right : Lane4) :
    Lane4 :=
  let pre := canopyNodePreimage salt level nodeIdx left right
  poseidon2CanopyCompress pre.initCap pre.limbStream

theorem canopyLeafPreimage_injective {s1 s2 : Lane4} {i1 i2 : Goldilocks}
    {p1 p2 : List Goldilocks}
    (h : canopyLeafPreimage s1 i1 p1 = canopyLeafPreimage s2 i2 p2) :
    s1 = s2 ∧ i1 = i2 ∧ p1 = p2 := by
  unfold canopyLeafPreimage at h
  injection h with hCap hStream
  injection hCap with _ hi _ _
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hStream
  rcases hStream with ⟨hx0, hx1, hx2, hx3, hp⟩
  exact ⟨Lane4.ext hx0 hx1 hx2 hx3, hi, hp⟩

theorem canopyNodePreimage_injective {s1 s2 : Lane4} {lv1 lv2 i1 i2 : Goldilocks}
    {l1 l2 r1 r2 : Lane4}
    (h : canopyNodePreimage s1 lv1 i1 l1 r1 = canopyNodePreimage s2 lv2 i2 l2 r2) :
    s1 = s2 ∧ lv1 = lv2 ∧ i1 = i2 ∧ l1 = l2 ∧ r1 = r2 := by
  unfold canopyNodePreimage at h
  injection h with hCap hStream
  injection hCap with _ hlv hi _
  simp only [List.cons.injEq, and_true] at hStream
  rcases hStream with ⟨sx0, sx1, sx2, sx3, lx0, lx1, lx2, lx3, rx0, rx1, rx2, rx3⟩
  exact ⟨Lane4.ext sx0 sx1 sx2 sx3, hlv, hi,
         Lane4.ext lx0 lx1 lx2 lx3, Lane4.ext rx0 rx1 rx2 rx3⟩

theorem canopyLeaf_ne_node_preimage (s1 s2 : Lane4) (i1 lv2 i2 : Goldilocks)
    (p1 : List Goldilocks) (l2 r2 : Lane4) :
    canopyLeafPreimage s1 i1 p1 ≠ canopyNodePreimage s2 lv2 i2 l2 r2 := by
  intro h
  have hTag : (canopyLeafPreimage s1 i1 p1).initCap.x0 =
      (canopyNodePreimage s2 lv2 i2 l2 r2).initCap.x0 :=
    congrArg (fun p => p.initCap.x0) h
  exact poseidon2Leaf_ne_node_tag hTag

/-- Fold a bottom-to-top sibling path `[sib_0, sib_1, ...]` starting from `(level = 0, idx = leafIdx)`
    using salted domain-separated `poseidon2CanopyNodeHash`. -/
def computePoseidon2MerkleFold (salt : Lane4) :
    Nat → Nat → Lane4 → List Lane4 → Lane4
  | _, _, cur, [] => cur
  | level, idx, cur, sib :: rest =>
    let parentIdx := idx / 2
    let parent :=
      if idx % 2 == 0 then
        poseidon2CanopyNodeHash salt (Goldilocks.ofNat level) (Goldilocks.ofNat parentIdx) cur sib
      else
        poseidon2CanopyNodeHash salt (Goldilocks.ofNat level) (Goldilocks.ofNat parentIdx) sib cur
    computePoseidon2MerkleFold salt (level + 1) parentIdx parent rest

/-- Algebraic `Poseidon2` Canopy Merkle commitment: commits to a top-layer `canopy` of `2^canopyDepth`
    digests compressed to `root : Lane4`, and opens each queried leaf via its `bottomPath` of length
    `bottomDepth` into `canopy[leafIdx / 2^bottomDepth]` plus the Canopy top commitment! -/
structure Poseidon2CanopyOpening where
  leafIdx : Nat
  payload : List Goldilocks
  bottomPath : List Lane4
  canopyPath : List Lane4
  deriving DecidableEq, Repr

/-- Verify an algebraic `Poseidon2` Canopy opening of `treeDepth = bottomDepth + canopyDepth` against
    `(salt, root)` (`leafIdx < 2 ^ treeDepth`, `treeDepth < 32`). -/
def verifyPoseidon2CanopyOpening (salt root : Lane4) (bottomDepth canopyDepth : Nat)
    (op : Poseidon2CanopyOpening) : Bool :=
  let treeDepth := bottomDepth + canopyDepth
  decide (treeDepth < 32) &&
  decide (op.leafIdx < 2 ^ treeDepth) &&
  decide (op.bottomPath.length = bottomDepth) &&
  decide (op.canopyPath.length = canopyDepth) &&
  let leafDig := poseidon2CanopyLeafHash salt (Goldilocks.ofNat op.leafIdx) op.payload
  let canopyNode := computePoseidon2MerkleFold salt 0 op.leafIdx leafDig op.bottomPath
  let fullRoot := computePoseidon2MerkleFold salt bottomDepth (op.leafIdx / 2 ^ bottomDepth)
                    canopyNode op.canopyPath
  decide (fullRoot = root)

private theorem merkleFold_append (salt : Lane4) :
    ∀ (p1 p2 : List Lane4) (lv idx : Nat) (cur : Lane4),
      computePoseidon2MerkleFold salt (lv + p1.length) (idx / 2 ^ p1.length)
        (computePoseidon2MerkleFold salt lv idx cur p1) p2 =
      computePoseidon2MerkleFold salt lv idx cur (p1 ++ p2)
  | [], p2, lv, idx, cur => by
    simp [computePoseidon2MerkleFold]
  | sib :: rest, p2, lv, idx, cur => by
    simp only [List.length_cons, List.cons_append, computePoseidon2MerkleFold]
    have hLv : lv + (rest.length + 1) = (lv + 1) + rest.length := by omega
    have hDiv : idx / 2 ^ (rest.length + 1) = (idx / 2) / 2 ^ rest.length := by
      rw [Nat.pow_succ', Nat.div_div_eq_div_mul]
    rw [hLv, hDiv]
    exact merkleFold_append salt rest p2 (lv + 1) (idx / 2) _

/-- Constructive (`0 Classical.choice`) fold collision extractor: if two Merkle folds from the same
    `(lv, idx)` of equal path length `≤ 31 - lv` converge to the same `Lane4` root, constructively
    produce either `cur1 = cur2 ∧ path1 = path2` or an explicit `Poseidon2CanopyCollision`! -/
def extractMerkleFoldCollision (salt : Lane4) :
    ∀ (p1 p2 : List Lane4) (lv idx : Nat) (cur1 cur2 : Lane4),
      p1.length = p2.length →
      lv + p1.length < 32 →
      idx < 2 ^ 32 →
      computePoseidon2MerkleFold salt lv idx cur1 p1 =
        computePoseidon2MerkleFold salt lv idx cur2 p2 →
      PSum (cur1 = cur2 ∧ p1 = p2) Poseidon2CanopyCollision
  | [], [], _, _, cur1, cur2, _, _, _, hEq =>
    .inl ⟨hEq, rfl⟩
  | _ :: _, [], _, _, _, _, hLen, _, _, _ =>
    False.elim (Nat.succ_ne_zero _ hLen)
  | [], _ :: _, _, _, _, _, hLen, _, _, _ =>
    False.elim (Nat.succ_ne_zero _ hLen.symm)
  | s1 :: r1, s2 :: r2, lv, idx, cur1, cur2, hLen, hLvLt, hIdxLt, hEq => by
    simp only [computePoseidon2MerkleFold] at hEq
    let pIdx := idx / 2
    let par1 := if idx % 2 == 0 then
        poseidon2CanopyNodeHash salt (Goldilocks.ofNat lv) (Goldilocks.ofNat pIdx) cur1 s1
      else
        poseidon2CanopyNodeHash salt (Goldilocks.ofNat lv) (Goldilocks.ofNat pIdx) s1 cur1
    let par2 := if idx % 2 == 0 then
        poseidon2CanopyNodeHash salt (Goldilocks.ofNat lv) (Goldilocks.ofNat pIdx) cur2 s2
      else
        poseidon2CanopyNodeHash salt (Goldilocks.ofNat lv) (Goldilocks.ofNat pIdx) s2 cur2
    have hSubLen : r1.length = r2.length := Nat.succ.inj hLen
    have hSubLv : (lv + 1) + r1.length < 32 := by simp at hLvLt; omega
    have hSubIdx : pIdx < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self idx 2) hIdxLt
    match extractMerkleFoldCollision salt r1 r2 (lv + 1) pIdx par1 par2 hSubLen hSubLv hSubIdx hEq with
    | .inr col => exact .inr col
    | .inl ⟨hParEq, hRestEq⟩ =>
      if hChildren : cur1 = cur2 ∧ s1 = s2 then
        exact .inl ⟨hChildren.1, by rw [hChildren.2, hRestEq]⟩
      else
        refine .inr ?_
        cases hBit : (idx % 2 == 0)
        · dsimp only [par1, par2] at hParEq
          rw [hBit] at hParEq
          simp only [Bool.false_eq_true, ↓reduceIte] at hParEq
          exact ⟨canopyNodePreimage salt (Goldilocks.ofNat lv) (Goldilocks.ofNat pIdx) s1 cur1,
                 canopyNodePreimage salt (Goldilocks.ofNat lv) (Goldilocks.ofNat pIdx) s2 cur2,
                 fun hPre => by
                   have ⟨_, _, _, hs, hc⟩ := canopyNodePreimage_injective hPre
                   exact hChildren ⟨hc, hs⟩,
                 hParEq⟩
        · dsimp only [par1, par2] at hParEq
          rw [hBit] at hParEq
          simp only [↓reduceIte] at hParEq
          exact ⟨canopyNodePreimage salt (Goldilocks.ofNat lv) (Goldilocks.ofNat pIdx) cur1 s1,
                 canopyNodePreimage salt (Goldilocks.ofNat lv) (Goldilocks.ofNat pIdx) cur2 s2,
                 fun hPre => by
                   have ⟨_, _, _, hc, hs⟩ := canopyNodePreimage_injective hPre
                   exact hChildren ⟨hc, hs⟩,
                 hParEq⟩

private theorem pow2_pos_hc : ∀ n : Nat, 1 ≤ 2 ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => by
    rw [Nat.pow_succ]
    have ih := pow2_pos_hc n
    omega

private theorem pow2_lt_pow2_hc : ∀ {a b : Nat}, a < b → 2 ^ a < 2 ^ b
  | 0, 0, h => False.elim (Nat.not_lt_zero 0 h)
  | 0, b + 1, _ => by
    rw [Nat.pow_zero, Nat.pow_succ]
    have hp := pow2_pos_hc b
    omega
  | _ + 1, 0, h => False.elim (Nat.not_lt_zero _ h)
  | a + 1, b + 1, h => by
    have ih := pow2_lt_pow2_hc (Nat.lt_of_succ_lt_succ h)
    rw [Nat.pow_succ, Nat.pow_succ]
    omega

/-- **Constructive `Poseidon2` Canopy Opening / Collision Extractor
    (`extractPoseidon2CanopyCollisionOrOpening`, `0 Classical.choice`)**:
    Given ANY two valid Canopy openings `op1, op2` against the same `(salt, root)` at the same
    `leafIdx`, constructively extract either:
    - `.inl` : exact leaf payload AND authentication path equality
      (`op1.payload = op2.payload ∧ op1.bottomPath = op2.bottomPath ∧ op1.canopyPath = op2.canopyPath`), or
    - `.inr` : an explicit `Poseidon2CanopyCollision` witness against `poseidon2CanopyCompress`! -/
def extractPoseidon2CanopyCollisionOrOpening
    (salt root : Lane4) (bottomDepth canopyDepth : Nat)
    (op1 op2 : Poseidon2CanopyOpening)
    (hIdx : op1.leafIdx = op2.leafIdx)
    (h1 : verifyPoseidon2CanopyOpening salt root bottomDepth canopyDepth op1 = true)
    (h2 : verifyPoseidon2CanopyOpening salt root bottomDepth canopyDepth op2 = true) :
    PSum (op1.payload = op2.payload ∧ op1.bottomPath = op2.bottomPath ∧ op1.canopyPath = op2.canopyPath)
         Poseidon2CanopyCollision := by
  unfold verifyPoseidon2CanopyOpening at h1 h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  rcases h1 with ⟨⟨⟨⟨hTdLt, hIdxLt⟩, hBot1⟩, hCan1⟩, hRoot1⟩
  rcases h2 with ⟨⟨⟨⟨_, _⟩, hBot2⟩, hCan2⟩, hRoot2⟩
  let full1 := op1.bottomPath ++ op1.canopyPath
  let full2 := op2.bottomPath ++ op2.canopyPath
  have hLen1 : full1.length = bottomDepth + canopyDepth := by
    simp [full1, hBot1, hCan1]
  have hLenEq : full1.length = full2.length := by
    simp [full1, full2, hBot1, hBot2, hCan1, hCan2]
  have hFold1 : computePoseidon2MerkleFold salt 0 op1.leafIdx
      (poseidon2CanopyLeafHash salt (Goldilocks.ofNat op1.leafIdx) op1.payload) full1 = root := by
    have hm := merkleFold_append salt op1.bottomPath op1.canopyPath 0 op1.leafIdx
      (poseidon2CanopyLeafHash salt (Goldilocks.ofNat op1.leafIdx) op1.payload)
    simp only [Nat.zero_add, hBot1] at hm
    exact hm.symm.trans hRoot1
  have hFold2 : computePoseidon2MerkleFold salt 0 op1.leafIdx
      (poseidon2CanopyLeafHash salt (Goldilocks.ofNat op1.leafIdx) op2.payload) full2 = root := by
    have hm := merkleFold_append salt op2.bottomPath op2.canopyPath 0 op2.leafIdx
      (poseidon2CanopyLeafHash salt (Goldilocks.ofNat op2.leafIdx) op2.payload)
    simp only [Nat.zero_add, hBot2] at hm
    have hEq2 := hm.symm.trans hRoot2
    rwa [← hIdx] at hEq2
  have hIdx32 : op1.leafIdx < 2 ^ 32 :=
    Nat.lt_trans hIdxLt (pow2_lt_pow2_hc hTdLt)
  have hLv32 : 0 + full1.length < 32 := by omega
  match extractMerkleFoldCollision salt full1 full2 0 op1.leafIdx
      (poseidon2CanopyLeafHash salt (Goldilocks.ofNat op1.leafIdx) op1.payload)
      (poseidon2CanopyLeafHash salt (Goldilocks.ofNat op1.leafIdx) op2.payload)
      hLenEq hLv32 hIdx32 (hFold1.trans hFold2.symm) with
  | .inr col => exact .inr col
  | .inl ⟨hLeafDigEq, hFullPathEq⟩ =>
    if hPay : op1.payload = op2.payload then
      have ⟨hB, hC⟩ := List.append_inj hFullPathEq (hBot1.trans hBot2.symm)
      exact .inl ⟨hPay, hB, hC⟩
    else
      exact .inr ⟨canopyLeafPreimage salt (Goldilocks.ofNat op1.leafIdx) op1.payload,
                  canopyLeafPreimage salt (Goldilocks.ofNat op1.leafIdx) op2.payload,
                  fun hPre => hPay (canopyLeafPreimage_injective hPre).2.2,
                  hLeafDigEq⟩

/-- Unsalted Canopy leaf hash (buggy variant omitting the 4-limb 256-bit tree salt). -/
def unsaltedPoseidon2CanopyLeafHash (leafIdx : Goldilocks) (payload : List Goldilocks) : Lane4 :=
  poseidon2CanopyCompress
    ⟨poseidon2LeafDomainTag, leafIdx, Goldilocks.ofNat payload.length, Goldilocks.one⟩
    payload

/-- `#tooth` (`tooth_unsalted_poseidon2_canopy_collision`):
    Omitting the 4-limb 256-bit tree salt causes distinct prover sessions `salt1 ≠ salt2` committing
    to the same leaf `(idx, payload)` to produce **identical** leaf digests with ZERO sponge input
    separation (enabling cross-session quantum state-restoration / preprocessing amortisation), whereas
    salted `canopyLeafPreimage salt1 idx payload ≠ canopyLeafPreimage salt2 idx payload` guarantees
    any cross-salt digest match is an explicit `Poseidon2CanopyCollision`! -/
theorem tooth_unsalted_poseidon2_canopy_collision :
    ∃ (salt1 salt2 : Lane4) (idx : Goldilocks) (payload : List Goldilocks),
      salt1 ≠ salt2 ∧
      unsaltedPoseidon2CanopyLeafHash idx payload = unsaltedPoseidon2CanopyLeafHash idx payload ∧
      canopyLeafPreimage salt1 idx payload ≠ canopyLeafPreimage salt2 idx payload ∧
      (poseidon2CanopyLeafHash salt1 idx payload = poseidon2CanopyLeafHash salt2 idx payload →
        Nonempty Poseidon2CanopyCollision) := by
  let s1 : Lane4 := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let s2 : Lane4 := ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  have hsNe : s1 ≠ s2 := fun h => by
    have hv : Goldilocks.zero.val = Goldilocks.one.val := congrArg (fun l : Lane4 => l.x0.val) h
    exact absurd hv (by decide)
  have hPreNe : canopyLeafPreimage s1 Goldilocks.zero [Goldilocks.one] ≠
      canopyLeafPreimage s2 Goldilocks.zero [Goldilocks.one] :=
    fun h => hsNe (canopyLeafPreimage_injective h).1
  exact ⟨s1, s2, Goldilocks.zero, [Goldilocks.one], hsNe, rfl, hPreNe,
    fun hCol => ⟨⟨_, _, hPreNe, hCol⟩⟩⟩

/-- Buggy untagged leaf/node hashes using a shared capacity lane `⟨0, idx, 8, 0⟩` without domain tags. -/
def untaggedCanopyLeafHash (salt : Lane4) (idx : Goldilocks) (payload : List Goldilocks) : Lane4 :=
  poseidon2CanopyCompress ⟨Goldilocks.zero, idx, Goldilocks.ofNat payload.length, Goldilocks.zero⟩
    ([salt.x0, salt.x1, salt.x2, salt.x3] ++ payload)

def untaggedCanopyNodeHash (salt : Lane4) (idx : Goldilocks) (left right : Lane4) : Lane4 :=
  poseidon2CanopyCompress ⟨Goldilocks.zero, idx, Goldilocks.ofNat 8, Goldilocks.zero⟩
    [salt.x0, salt.x1, salt.x2, salt.x3,
     left.x0, left.x1, left.x2, left.x3,
     right.x0, right.x1, right.x2, right.x3]

/-- `#tooth` (`tooth_missing_domain_tag_leaf_node_confusion`):
    If `poseidon2LeafDomainTag` and `poseidon2NodeDomainTag` are omitted (both set to `0`), ANY
    internal 2-to-1 node `(left, right)` has an **unconditional** rate-8 leaf second-preimage
    `payload = [left.x0..x3, right.x0..x3]` producing the exact same `Poseidon2` digest with ZERO
    sponge collisions, whereas tagged `canopyLeafPreimage ≠ canopyNodePreimage` unconditionally! -/
theorem tooth_missing_domain_tag_leaf_node_confusion (salt left right : Lane4) (idx : Goldilocks) :
    ∃ forgedPayload : List Goldilocks,
      untaggedCanopyLeafHash salt idx forgedPayload = untaggedCanopyNodeHash salt idx left right ∧
      canopyLeafPreimage salt idx forgedPayload ≠ canopyNodePreimage salt idx idx left right :=
  ⟨[left.x0, left.x1, left.x2, left.x3, right.x0, right.x1, right.x2, right.x3],
   rfl, canopyLeaf_ne_node_preimage salt salt idx idx idx _ left right⟩


private theorem field_right_inv_unique {F : Type} [LawfulField F] {a u1 u2 : F}
    (h1 : CommRingOps.mul a u1 = CommRingOps.one)
    (h2 : CommRingOps.mul a u2 = CommRingOps.one) : u1 = u2 := by
  calc u1 = CommRingOps.mul CommRingOps.one u1 := (LawfulCommRing.one_mul u1).symm
    _ = CommRingOps.mul (CommRingOps.mul u2 a) u1 := by rw [LawfulCommRing.mul_comm u2 a, h2]
    _ = CommRingOps.mul u2 (CommRingOps.mul a u1) := LawfulCommRing.mul_assoc u2 a u1
    _ = CommRingOps.mul u2 CommRingOps.one := by rw [h1]
    _ = u2 := LawfulCommRing.mul_one u2


/-! ### Sequential length-framed Fiat–Shamir transcript (`recursive_whir.rs::Transcript`)

The Rust transcript is a duplex over the width-12 `Poseidon2` permutation. `absorb(tag, msg)` adds
`tag` to state limb 10 and `msg.len()` to state limb 11, then adds the message six limbs at a time to
state limbs `0..6`, permuting after every chunk; a final short chunk of `k < 6` limbs gets the marker
`1` at limb `k`, and a message whose length is a multiple of six gets one more permutation with the
marker at limb `0`. `ext(tag)` is `absorb(tag, [])` followed by reading state limbs `0..4`. Here a
frame is `FsFrame`, the addend of one permutation call is `FsBlock`, and the state after a frame list
is `fsSpongeState`. -/

/-- One `Transcript::absorb(tag, msg)` call. A challenge squeeze `Transcript::ext(tag)` is the
    frame `⟨tag, []⟩`. -/
structure FsFrame where
  tag : Goldilocks
  msg : List Goldilocks
  deriving DecidableEq, Repr

/-- What one permutation call adds to the duplex state: six rate limbs (state limbs `0..6`) and
    the tag and length limbs (state limbs `10`, `11`). State limbs `6..10` receive nothing. -/
structure FsBlock where
  r0 : Goldilocks
  r1 : Goldilocks
  r2 : Goldilocks
  r3 : Goldilocks
  r4 : Goldilocks
  r5 : Goldilocks
  c10 : Goldilocks
  c11 : Goldilocks
  deriving DecidableEq, Repr

/-- The block as a width-12 state addend. -/
def FsBlock.addend (b : FsBlock) : Poseidon2State12 :=
  ⟨⟨b.r0, b.r1, b.r2, b.r3⟩, ⟨b.r4, b.r5, Goldilocks.zero, Goldilocks.zero⟩,
   ⟨Goldilocks.zero, Goldilocks.zero, b.c10, b.c11⟩⟩

theorem FsBlock.addend_injective {a b : FsBlock} (h : a.addend = b.addend) : a = b := by
  cases a; cases b
  dsimp only [FsBlock.addend] at h
  injection h with hb0 hb1 hb2
  injection hb0 with h0 h1 h2 h3
  injection hb1 with h4 h5
  injection hb2 with _ _ h10 h11
  subst h0 h1 h2 h3 h4 h5 h10 h11
  rfl

/-- Limb `i` of a final short chunk `l` followed by the marker `1` and zeros. -/
def fsPadLimb : List Goldilocks → Nat → Goldilocks
  | [], 0 => Goldilocks.one
  | [], _ + 1 => Goldilocks.zero
  | a :: _, 0 => a
  | _ :: l, i + 1 => fsPadLimb l i

/-- Blocks of one frame: `c10`, `c11` are the tag and length limbs, added with the first block
    only. Full six-limb chunks first; the last block is the short chunk with its marker. -/
def fsFrameBlocksAux (c10 c11 : Goldilocks) : List Goldilocks → List FsBlock
  | a :: b :: c :: d :: e :: f :: rest =>
    ⟨a, b, c, d, e, f, c10, c11⟩ :: fsFrameBlocksAux Goldilocks.zero Goldilocks.zero rest
  | l => [⟨fsPadLimb l 0, fsPadLimb l 1, fsPadLimb l 2, fsPadLimb l 3, fsPadLimb l 4,
           fsPadLimb l 5, c10, c11⟩]

/-- Blocks of `Transcript::absorb(f.tag, f.msg)`. The length limb is `f.msg.length` reduced into
    the field, as in `f(msg.len() as u64)`. -/
def fsFrameBlocks (f : FsFrame) : List FsBlock :=
  fsFrameBlocksAux f.tag (Goldilocks.ofNat f.msg.length) f.msg

/-- Block encoding of a frame list: the sequence of permutation inputs of the whole transcript. -/
def fsTranscriptBlocks : List FsFrame → List FsBlock
  | [] => []
  | f :: fs => fsFrameBlocks f ++ fsTranscriptBlocks fs

private theorem list_six_cases (l : List Goldilocks) :
    (∃ a b c d e f rest, l = a :: b :: c :: d :: e :: f :: rest) ∨ l.length < 6 := by
  match l with
  | a :: b :: c :: d :: e :: f :: rest => exact .inl ⟨a, b, c, d, e, f, rest, rfl⟩
  | [] => exact .inr (Nat.succ_pos 5)
  | [_] => exact .inr (Nat.succ_lt_succ (Nat.succ_pos 4))
  | [_, _] => exact .inr (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 3)))
  | [_, _, _] =>
    exact .inr (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 2))))
  | [_, _, _, _] =>
    exact .inr (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.succ_pos 1)))))
  | [_, _, _, _, _] =>
    exact .inr (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ
      (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))))))

private theorem fsFrameBlocksAux_long (c10 c11 a b c d e f : Goldilocks) (rest : List Goldilocks) :
    fsFrameBlocksAux c10 c11 (a :: b :: c :: d :: e :: f :: rest) =
      ⟨a, b, c, d, e, f, c10, c11⟩ :: fsFrameBlocksAux Goldilocks.zero Goldilocks.zero rest := by
  rfl

private theorem fsFrameBlocksAux_short (c10 c11 : Goldilocks) :
    ∀ (l : List Goldilocks), l.length < 6 →
      fsFrameBlocksAux c10 c11 l =
        [⟨fsPadLimb l 0, fsPadLimb l 1, fsPadLimb l 2, fsPadLimb l 3, fsPadLimb l 4,
          fsPadLimb l 5, c10, c11⟩]
  | [], _ => by rfl
  | [_], _ => by rfl
  | [_, _], _ => by rfl
  | [_, _, _], _ => by rfl
  | [_, _, _, _], _ => by rfl
  | [_, _, _, _, _], _ => by rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: rest, h => by
    have h6 : ¬ (rest.length + 6 < 6) := by omega
    exact absurd h h6

private theorem fsFrameBlocksAux_head (c d : Goldilocks) (m : List Goldilocks) :
    ∃ b bs, fsFrameBlocksAux c d m = b :: bs ∧ b.c10 = c ∧ b.c11 = d := by
  rcases list_six_cases m with ⟨a1, a2, a3, a4, a5, a6, rest, rfl⟩ | hlt
  · exact ⟨_, _, fsFrameBlocksAux_long c d a1 a2 a3 a4 a5 a6 rest, rfl, rfl⟩
  · exact ⟨_, [], fsFrameBlocksAux_short c d m hlt, rfl, rfl⟩

private theorem fsPadLimb_inj :
    ∀ (l1 l2 : List Goldilocks), l1.length = l2.length →
      (∀ i, i < l1.length → fsPadLimb l1 i = fsPadLimb l2 i) → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => absurd h.symm (Nat.succ_ne_zero _)
  | _ :: _, [], h, _ => absurd h (Nat.succ_ne_zero _)
  | a :: l1, b :: l2, h, hi => by
    have hab : a = b := hi 0 (Nat.succ_pos _)
    have ht := fsPadLimb_inj l1 l2 (Nat.succ.inj h)
      (fun i hlt => hi (i + 1) (Nat.succ_lt_succ hlt))
    rw [hab, ht]

private theorem fsFrameBlocksAux_append_inj_short {m1 m2 : List Goldilocks}
    {c1 d1 c2 d2 : Goldilocks} {X Y : List FsBlock}
    (h1 : m1.length < 6) (hlen : m1.length = m2.length)
    (h : fsFrameBlocksAux c1 d1 m1 ++ X = fsFrameBlocksAux c2 d2 m2 ++ Y) :
    c1 = c2 ∧ d1 = d2 ∧ m1 = m2 ∧ X = Y := by
  have h2 : m2.length < 6 := hlen ▸ h1
  rw [fsFrameBlocksAux_short c1 d1 m1 h1, fsFrameBlocksAux_short c2 d2 m2 h2] at h
  simp only [List.cons_append, List.nil_append] at h
  injection h with hHead hTail
  injection hHead with e0 e1 e2 e3 e4 e5 hc hd
  refine ⟨hc, hd, fsPadLimb_inj m1 m2 hlen (fun i hi => ?_), hTail⟩
  match i, hi with
  | 0, _ => exact e0
  | 1, _ => exact e1
  | 2, _ => exact e2
  | 3, _ => exact e3
  | 4, _ => exact e4
  | 5, _ => exact e5
  | n + 6, hi =>
    have h6 : ¬ (n + 6 < 6) := by omega
    exact absurd (Nat.lt_trans hi h1) h6

private theorem fsFrameBlocksAux_append_inj (n : Nat) :
    ∀ (m1 m2 : List Goldilocks) (c1 d1 c2 d2 : Goldilocks) (X Y : List FsBlock),
      m1.length ≤ n → m1.length = m2.length →
      fsFrameBlocksAux c1 d1 m1 ++ X = fsFrameBlocksAux c2 d2 m2 ++ Y →
      c1 = c2 ∧ d1 = d2 ∧ m1 = m2 ∧ X = Y := by
  induction n with
  | zero =>
    intro m1 m2 c1 d1 c2 d2 X Y hn hlen h
    exact fsFrameBlocksAux_append_inj_short (Nat.lt_of_le_of_lt hn (Nat.succ_pos 5)) hlen h
  | succ n ih =>
    intro m1 m2 c1 d1 c2 d2 X Y hn hlen h
    rcases list_six_cases m1 with ⟨a1, a2, a3, a4, a5, a6, r1, rfl⟩ | h1
    · rcases list_six_cases m2 with ⟨b1, b2, b3, b4, b5, b6, r2, rfl⟩ | h2
      · rw [fsFrameBlocksAux_long, fsFrameBlocksAux_long] at h
        simp only [List.cons_append] at h
        injection h with hHead hTail
        injection hHead with e1 e2 e3 e4 e5 e6 hc hd
        have hl : r1.length = r2.length := by
          simp only [List.length_cons] at hlen
          omega
        have hn' : r1.length ≤ n := by
          simp only [List.length_cons] at hn
          omega
        obtain ⟨_, _, hr, hXY⟩ := ih r1 r2 _ _ _ _ X Y hn' hl hTail
        subst e1 e2 e3 e4 e5 e6 hr
        exact ⟨hc, hd, rfl, hXY⟩
      · have h6 : ¬ (m2.length < 6) := by
          simp only [List.length_cons] at hlen
          omega
        exact absurd h2 h6
    · exact fsFrameBlocksAux_append_inj_short h1 hlen h

private theorem goldilocks_ofNat_inj {a b : Nat} (ha : a < goldilocksPrime)
    (hb : b < goldilocksPrime) (h : Goldilocks.ofNat a = Goldilocks.ofNat b) : a = b := by
  have hv := congrArg Goldilocks.val h
  rw [Goldilocks.ofNat_val, Goldilocks.ofNat_val, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  exact hv

/-- **The transcript encoding is injective (length framing).** Two frame lists whose message
    lengths are canonical (`< p`, so the length limb determines the length) and whose block
    sequences coincide are equal: every tag and every message limb is recovered, and no frame
    boundary can be moved. -/
theorem fsTranscriptBlocks_injective :
    ∀ (fs gs : List FsFrame),
      (∀ f ∈ fs, f.msg.length < goldilocksPrime) →
      (∀ g ∈ gs, g.msg.length < goldilocksPrime) →
      fsTranscriptBlocks fs = fsTranscriptBlocks gs → fs = gs
  | [], [], _, _, _ => rfl
  | [], g :: gs, _, _, h => by
    obtain ⟨b, bs, hb, _, _⟩ :=
      fsFrameBlocksAux_head g.tag (Goldilocks.ofNat g.msg.length) g.msg
    have h' : ([] : List FsBlock) =
        fsFrameBlocksAux g.tag (Goldilocks.ofNat g.msg.length) g.msg ++ fsTranscriptBlocks gs := h
    rw [hb, List.cons_append] at h'
    cases h'
  | f :: fs, [], _, _, h => by
    obtain ⟨b, bs, hb, _, _⟩ :=
      fsFrameBlocksAux_head f.tag (Goldilocks.ofNat f.msg.length) f.msg
    have h' : fsFrameBlocksAux f.tag (Goldilocks.ofNat f.msg.length) f.msg ++ fsTranscriptBlocks fs =
        ([] : List FsBlock) := h
    rw [hb, List.cons_append] at h'
    cases h'
  | f :: fs, g :: gs, hf, hg, h => by
    have h' : fsFrameBlocksAux f.tag (Goldilocks.ofNat f.msg.length) f.msg ++ fsTranscriptBlocks fs =
        fsFrameBlocksAux g.tag (Goldilocks.ofNat g.msg.length) g.msg ++ fsTranscriptBlocks gs := h
    obtain ⟨b1, bs1, hb1, _, hd1⟩ :=
      fsFrameBlocksAux_head f.tag (Goldilocks.ofNat f.msg.length) f.msg
    obtain ⟨b2, bs2, hb2, _, hd2⟩ :=
      fsFrameBlocksAux_head g.tag (Goldilocks.ofNat g.msg.length) g.msg
    have hHeadEq : b1 = b2 := by
      have h'' := h'
      rw [hb1, hb2, List.cons_append, List.cons_append] at h''
      injection h'' with hh _
    have hLenF : Goldilocks.ofNat f.msg.length = Goldilocks.ofNat g.msg.length := by
      rw [← hd1, ← hd2, hHeadEq]
    have hLen : f.msg.length = g.msg.length :=
      goldilocks_ofNat_inj (hf f (List.mem_cons_self ..)) (hg g (List.mem_cons_self ..)) hLenF
    obtain ⟨ht, _, hm, hXY⟩ := fsFrameBlocksAux_append_inj f.msg.length f.msg g.msg _ _ _ _ _ _
      (Nat.le_refl _) hLen h'
    have ih := fsTranscriptBlocks_injective fs gs
      (fun x hx => hf x (List.mem_cons_of_mem _ hx))
      (fun x hx => hg x (List.mem_cons_of_mem _ hx)) hXY
    cases f; cases g
    dsimp only at ht hm
    subst ht hm ih
    rfl

/-- Initial duplex state (`Transcript::new`). -/
def fsZeroState : Poseidon2State12 := ⟨lane4Zero, lane4Zero, lane4Zero⟩

/-- One permutation call of the duplex. -/
def fsDuplexStep (st : Poseidon2State12) (b : FsBlock) : Poseidon2State12 :=
  poseidon2Perm12 (state12Add st b.addend)

/-- `Transcript::absorb` of one frame from state `st`. -/
def fsAbsorbFrame (st : Poseidon2State12) (f : FsFrame) : Poseidon2State12 :=
  (fsFrameBlocks f).foldl fsDuplexStep st

/-- Duplex state after absorbing the frames in order. -/
def fsSpongeState (frames : List FsFrame) : Poseidon2State12 :=
  frames.foldl fsAbsorbFrame fsZeroState

private theorem foldl_fsAbsorbFrame_eq_blocks :
    ∀ (frames : List FsFrame) (st : Poseidon2State12),
      frames.foldl fsAbsorbFrame st = (fsTranscriptBlocks frames).foldl fsDuplexStep st
  | [], _ => rfl
  | f :: fs, st => by
    show fs.foldl fsAbsorbFrame (fsAbsorbFrame st f) =
      (fsFrameBlocks f ++ fsTranscriptBlocks fs).foldl fsDuplexStep st
    rw [List.foldl_append, foldl_fsAbsorbFrame_eq_blocks fs]
    rfl

/-- The duplex state is the permutation chain over the block encoding of the transcript. -/
theorem fsSpongeState_eq_blocks (frames : List FsFrame) :
    fsSpongeState frames = (fsTranscriptBlocks frames).foldl fsDuplexStep fsZeroState :=
  foldl_fsAbsorbFrame_eq_blocks frames fsZeroState

/-- Absorbing one more frame continues from the state of the prefix. -/
theorem fsSpongeState_snoc (frames : List FsFrame) (f : FsFrame) :
    fsSpongeState (frames ++ [f]) = fsAbsorbFrame (fsSpongeState frames) f := by
  unfold fsSpongeState
  rw [List.foldl_append]
  rfl


/-- Two different block sequences that lead the duplex to the same squeezed lane. -/
structure FsSpongeCollision where
  blocks1 : List FsBlock
  blocks2 : List FsBlock
  hne : blocks1 ≠ blocks2
  hcol : (blocks1.foldl fsDuplexStep fsZeroState).b0 = (blocks2.foldl fsDuplexStep fsZeroState).b0


/-- One prover round: the absorbed frame `(tag, msg)` and the tags of the challenges the verifier
    squeezes after it, in order. The squeeze tags are fixed by the verifier's schedule. -/
structure FsRound where
  tag : Goldilocks
  msg : List Goldilocks
  squeezes : List Goldilocks
  deriving DecidableEq, Repr

/-- Frames of a round: its absorb, then one empty frame per squeezed challenge. -/
def FsRound.frames (r : FsRound) : List FsFrame :=
  ⟨r.tag, r.msg⟩ :: r.squeezes.map (fun t => ⟨t, []⟩)


def lane4Limbs (l : Lane4) : List Goldilocks := [l.x0, l.x1, l.x2, l.x3]

/-- `recursive_whir.rs::VERSION`. -/
def childWhirVersion : Goldilocks := Goldilocks.ofNat 0x4657484952000001


/-! ## §3. Depth-`d`, Fan-In-`F` Recursive `Hem` Tree over Real Leaf Shards

The tree verifier of this section sees the whole tree. A leaf is a shard certificate of the
two-layer hierarchy (`HemShardProof`, verified by `verifyHemShard` through
`verifyHierarchicalHem`) together with a canonical `RecursiveShardHeader` bound to that shard and a
child-WHIR proof whose public input is the header digest. Inner nodes carry the `Poseidon2` summary
of their children's digests and a child-WHIR proof on it. Nothing here states that an outer
child-WHIR proof certifies the verification of its children: soundness comes from the leaf
shards, which the verifier checks itself. -/

section RecursiveTree
open Aggregation

/-- Leaf shard header of a recursive `Hem` tree: numeric shard id, quorum threshold, committee size,
    claimed number of valid signers, and the `Poseidon2` digest of the leaf statement. -/
structure RecursiveShardHeader where
  shardId : Nat
  threshold : Nat
  committeeSize : Nat
  validCount : Nat
  publicDigest : Lane4
  deriving DecidableEq, Repr

/-- Header check: the numeric fields are canonical field representatives (`shardId < p` and
    `committeeSize < p`, hence all four are `< p`) and `1 ≤ threshold ≤ validCount ≤ committeeSize`. -/
def verifyRecursiveShardHeader (h : RecursiveShardHeader) : Bool :=
  decide (h.shardId < goldilocksPrime) &&
  decide (h.committeeSize < goldilocksPrime) &&
  decide (1 ≤ h.threshold) &&
  decide (h.threshold ≤ h.committeeSize) &&
  decide (h.threshold ≤ h.validCount) &&
  decide (h.validCount ≤ h.committeeSize)

theorem verifyRecursiveShardHeader_facts {h : RecursiveShardHeader}
    (hv : verifyRecursiveShardHeader h = true) :
    h.shardId < goldilocksPrime ∧ h.committeeSize < goldilocksPrime ∧ 1 ≤ h.threshold ∧
      h.threshold ≤ h.committeeSize ∧ h.threshold ≤ h.validCount ∧
      h.validCount ≤ h.committeeSize := by
  unfold verifyRecursiveShardHeader at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨hv.1.1.1.1.1, hv.1.1.1.1.2, hv.1.1.1.2, hv.1.1.2, hv.1.2, hv.2⟩

/-- Encode a list of child summary digests `(summaryDigest_0, ..., summaryDigest_{F-1})` into a
    rate-8 `Poseidon2` preimage under `poseidon2SummaryDomainTag`. -/
def encodeSummaryDigestList : List Lane4 → List Goldilocks
  | [] => []
  | d :: rest => [d.x0, d.x1, d.x2, d.x3] ++ encodeSummaryDigestList rest

/-- Every digest contributes four limbs, so the limb stream determines the digest list, its
    length included. -/
theorem encodeSummaryDigestList_injective :
    ∀ {xs ys : List Lane4},
      encodeSummaryDigestList xs = encodeSummaryDigestList ys →
      xs = ys
  | [], [], _ => rfl
  | [], y :: ys, hEnc => by
    have h' : ([] : List Goldilocks) =
        y.x0 :: ([y.x1, y.x2, y.x3] ++ encodeSummaryDigestList ys) := hEnc
    exact nomatch h'
  | x :: xs, [], hEnc => by
    have h' : x.x0 :: ([x.x1, x.x2, x.x3] ++ encodeSummaryDigestList xs) =
        ([] : List Goldilocks) := hEnc
    exact nomatch h'
  | x :: xs, y :: ys, hEnc => by
    simp only [encodeSummaryDigestList, List.cons_append, List.nil_append, List.cons.injEq] at hEnc
    rcases hEnc with ⟨h0, h1, h2, h3, hRest⟩
    have hx : x = y := Lane4.ext h0 h1 h2 h3
    have hxs : xs = ys := encodeSummaryDigestList_injective hRest
    rw [hx, hxs]

/-- `Poseidon2` preimage of an inner node: domain tag, `depth`, `fanIn` and the child count in the
    capacity lane, the child digests in the limb stream. `depth` and `fanIn` enter reduced modulo
    `p`; `verifyRecursiveHemNode` admits only `depth < p` and `fanIn < p`. -/
def canopySummaryPreimage (depth fanIn : Nat) (childDigests : List Lane4) :
    Poseidon2CanopyPreimage :=
  { initCap := ⟨poseidon2SummaryDomainTag, Goldilocks.ofNat depth,
                Goldilocks.ofNat fanIn, Goldilocks.ofNat childDigests.length⟩
    limbStream := encodeSummaryDigestList childDigests }

def poseidon2SummaryHash (depth fanIn : Nat) (childDigests : List Lane4) : Lane4 :=
  let pre := canopySummaryPreimage depth fanIn childDigests
  poseidon2CanopyCompress pre.initCap pre.limbStream

/-- **Full inner-node injectivity.** Two inner-node preimages with canonical `depth` and `fanIn`
    that are equal have the same depth, the same fan-in and the same child digest list (hence the
    same child count). -/
theorem canopySummaryPreimage_injective {d1 d2 f1 f2 : Nat} {xs ys : List Lane4}
    (hd1 : d1 < goldilocksPrime) (hf1 : f1 < goldilocksPrime)
    (hd2 : d2 < goldilocksPrime) (hf2 : f2 < goldilocksPrime)
    (h : canopySummaryPreimage d1 f1 xs = canopySummaryPreimage d2 f2 ys) :
    d1 = d2 ∧ f1 = f2 ∧ xs = ys := by
  unfold canopySummaryPreimage at h
  injection h with hCap hStream
  injection hCap with _ hD hF _
  exact ⟨goldilocks_ofNat_inj hd1 hd2 hD, goldilocks_ofNat_inj hf1 hf2 hF,
    encodeSummaryDigestList_injective hStream⟩

/-- Two inner-node summaries with canonical `depth` and `fanIn` and the same digest agree in
    depth, fan-in and child digest list, or their preimages are an explicit
    `Poseidon2CanopyCollision`. -/
def canopySummary_digest_binding (d1 d2 f1 f2 : Nat) (xs ys : List Lane4)
    (hd1 : d1 < goldilocksPrime) (hf1 : f1 < goldilocksPrime)
    (hd2 : d2 < goldilocksPrime) (hf2 : f2 < goldilocksPrime)
    (hEq : poseidon2SummaryHash d1 f1 xs = poseidon2SummaryHash d2 f2 ys) :
    PSum (PLift (d1 = d2 ∧ f1 = f2 ∧ xs = ys)) Poseidon2CanopyCollision :=
  if h : d1 = d2 ∧ f1 = f2 ∧ xs = ys then .inl ⟨h⟩
  else .inr ⟨canopySummaryPreimage d1 f1 xs, canopySummaryPreimage d2 f2 ys,
    fun hp => h (canopySummaryPreimage_injective hd1 hf1 hd2 hf2 hp), hEq⟩

/-- `Poseidon2` preimage of a leaf header: `shardId`, `threshold` in the capacity lane,
    `committeeSize`, `validCount` and the statement digest in the limb stream. -/
def leafShardHeaderPreimage (h : RecursiveShardHeader) : Poseidon2CanopyPreimage :=
  { initCap := ⟨poseidon2SummaryDomainTag, Goldilocks.zero, Goldilocks.ofNat h.shardId,
                Goldilocks.ofNat h.threshold⟩
    limbStream := [Goldilocks.ofNat h.committeeSize, Goldilocks.ofNat h.validCount,
                   h.publicDigest.x0, h.publicDigest.x1, h.publicDigest.x2, h.publicDigest.x3] }

/-- Leaf header digest binding `(shardId, threshold, committeeSize, validCount, publicDigest)`. -/
def hashLeafShardHeader (h : RecursiveShardHeader) : Lane4 :=
  poseidon2CanopyCompress (leafShardHeaderPreimage h).initCap (leafShardHeaderPreimage h).limbStream

/-- **Full header injectivity.** Two headers that pass `verifyRecursiveShardHeader` and have the
    same `Poseidon2` preimage are equal in every field. -/
theorem leafShardHeaderPreimage_injective {h1 h2 : RecursiveShardHeader}
    (hv1 : verifyRecursiveShardHeader h1 = true) (hv2 : verifyRecursiveShardHeader h2 = true)
    (h : leafShardHeaderPreimage h1 = leafShardHeaderPreimage h2) : h1 = h2 := by
  obtain ⟨hs1, hc1, _, htc1, _, hvc1⟩ := verifyRecursiveShardHeader_facts hv1
  obtain ⟨hs2, hc2, _, htc2, _, hvc2⟩ := verifyRecursiveShardHeader_facts hv2
  unfold leafShardHeaderPreimage at h
  injection h with hCap hStream
  injection hCap with _ _ hSid hThr
  injection hStream with hCom hTl1
  injection hTl1 with hVal hTl2
  injection hTl2 with hx0 hTl3
  injection hTl3 with hx1 hTl4
  injection hTl4 with hx2 hTl5
  injection hTl5 with hx3 _
  have eSid := goldilocks_ofNat_inj hs1 hs2 hSid
  have eThr := goldilocks_ofNat_inj (Nat.lt_of_le_of_lt htc1 hc1) (Nat.lt_of_le_of_lt htc2 hc2) hThr
  have eCom := goldilocks_ofNat_inj hc1 hc2 hCom
  have eVal := goldilocks_ofNat_inj (Nat.lt_of_le_of_lt hvc1 hc1) (Nat.lt_of_le_of_lt hvc2 hc2) hVal
  have eDig : h1.publicDigest = h2.publicDigest := Lane4.ext hx0 hx1 hx2 hx3
  cases h1; cases h2
  dsimp only at eSid eThr eCom eVal eDig
  subst eSid eThr eCom eVal eDig
  rfl

/-- Two canonical headers with the same digest are equal, or their preimages are an explicit
    `Poseidon2CanopyCollision`. -/
def leafShardHeader_digest_binding (h1 h2 : RecursiveShardHeader)
    (hv1 : verifyRecursiveShardHeader h1 = true) (hv2 : verifyRecursiveShardHeader h2 = true)
    (hEq : hashLeafShardHeader h1 = hashLeafShardHeader h2) :
    PSum (PLift (h1 = h2)) Poseidon2CanopyCollision :=
  if h : h1 = h2 then .inl ⟨h⟩
  else .inr ⟨leafShardHeaderPreimage h1, leafShardHeaderPreimage h2,
    fun hp => h (leafShardHeaderPreimage_injective hv1 hv2 hp), hEq⟩

/-- Domain-separation tag of the leaf statement digest (`"CANOPY_S"`). -/
def poseidon2LeafStatementDomainTag : Goldilocks :=
  Goldilocks.ofNat 0x43414E4F50595F53


private def verifyChildrenList {α : Type} (recVerify : α → Bool) : List α → Bool
  | [] => true
  | c :: cs => recVerify c && verifyChildrenList recVerify cs


private theorem verifyChildrenList_mem {α : Type} (recVerify : α → Bool) :
    ∀ (cs : List α), verifyChildrenList recVerify cs = true → ∀ c ∈ cs, recVerify c = true
  | [], _, _, hc => by cases hc
  | x :: cs, hAll, c, hc => by
    simp only [verifyChildrenList, Bool.and_eq_true] at hAll
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hAll.1
    · exact verifyChildrenList_mem recVerify cs hAll.2 c hc'


private theorem filter_const_false {α : Type} :
    ∀ l : List α, l.filter (fun _ => false) = []
  | [] => rfl
  | _ :: l => filter_const_false l


/-- Geometric internal-node count `1 + F + F^2 + ... + F^(d-1)` of a depth-`d`, fan-in-`F` tree. -/
def geomInternalNodes (F : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => 1 + F * geomInternalNodes F d

theorem geomInternalNodes_examples (F : Nat) :
    geomInternalNodes F 0 = 0 ∧
    geomInternalNodes F 1 = 1 ∧
    geomInternalNodes F 2 = 1 + F ∧
    geomInternalNodes F 3 = 1 + F + F * F := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [geomInternalNodes]
  · simp [geomInternalNodes]
  · simp only [geomInternalNodes, Nat.mul_zero, Nat.add_zero, Nat.mul_add, Nat.mul_one, Nat.add_assoc]

/-- Additive error budget of a depth-`d`, fan-in-`F` tree whose every node is charged:
    `(1 + F + ... + F^(d-1)) * ε_outer + F^d * ε_leaf`. This is a budget expression; the proved
    union bound of this module is `recursive_hem_tree_soundness_bound`, which charges leaves only. -/
def recursiveHemQromErrorBound (F d : Nat) (epsOuter epsLeaf : RatBound) : RatBound :=
  RatBound.add
    (RatBound.scale (geomInternalNodes F d) epsOuter)
    (RatBound.scale (F ^ d) epsLeaf)

theorem recursiveHemQromErrorBound_step (F d : Nat) (epsOuter epsLeaf : RatBound) :
    (recursiveHemQromErrorBound F (d + 1) epsOuter epsLeaf).num *
      (RatBound.add epsOuter (RatBound.scale F (recursiveHemQromErrorBound F d epsOuter epsLeaf))).den =
    (RatBound.add epsOuter (RatBound.scale F (recursiveHemQromErrorBound F d epsOuter epsLeaf))).num *
      (recursiveHemQromErrorBound F (d + 1) epsOuter epsLeaf).den := by
  have hGeom : geomInternalNodes F (d + 1) = 1 + F * geomInternalNodes F d := rfl
  unfold recursiveHemQromErrorBound RatBound.add RatBound.scale
  dsimp only
  rw [hGeom, Nat.pow_succ']
  let G := geomInternalNodes F d
  let P := F ^ d
  change ((1 + F * G) * epsOuter.num * epsLeaf.den + F * P * epsLeaf.num * epsOuter.den) *
      (epsOuter.den * (epsOuter.den * epsLeaf.den)) =
    (epsOuter.num * (epsOuter.den * epsLeaf.den) +
      F * (G * epsOuter.num * epsLeaf.den + P * epsLeaf.num * epsOuter.den) * epsOuter.den) *
      (epsOuter.den * epsLeaf.den)
  have hL :
      (epsOuter.num * (epsOuter.den * epsLeaf.den) +
        F * (G * epsOuter.num * epsLeaf.den + P * epsLeaf.num * epsOuter.den) * epsOuter.den) =
      ((1 + F * G) * epsOuter.num * epsLeaf.den + F * P * epsLeaf.num * epsOuter.den) * epsOuter.den := by
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add]
    ac_rfl
  rw [hL]
  ac_rfl

end RecursiveTree


/-! ## §4. Honest Child Witness, Tree Acceptance Lemma & Audits -/


private theorem bool_and5_true {a b c d e : Bool}
    (ha : a = true) (hb : b = true) (hc : c = true) (hd : d = true) (he : e = true) :
    (a && b && c && d && e) = true := by
  rw [ha, hb, hc, hd, he]
  rfl

private theorem depth_one_query_index (x : Nat) :
    0 = x % 2 ^ (1 + 0 - 1) ∧ 1 = x % 2 ^ (1 + 0 - 1) + 2 ^ (1 + 0 - 1) := by
  have h : 2 ^ (1 + 0 - 1) = 1 := by decide
  rw [h, Nat.mod_one]
  exact ⟨rfl, rfl⟩


theorem canopyOpening_payload_unique_of_collision_free
    (salt root : Lane4) (bottomDepth canopyDepth : Nat)
    (op1 op2 : Poseidon2CanopyOpening)
    (hIdx : op1.leafIdx = op2.leafIdx)
    (h1 : verifyPoseidon2CanopyOpening salt root bottomDepth canopyDepth op1 = true)
    (h2 : verifyPoseidon2CanopyOpening salt root bottomDepth canopyDepth op2 = true)
    (hNoCol : Poseidon2CanopyCollision → False) :
    op1.payload = op2.payload := by
  match extractPoseidon2CanopyCollisionOrOpening salt root bottomDepth canopyDepth op1 op2 hIdx h1 h2 with
  | .inl ⟨hp, _, _⟩ => exact hp
  | .inr col => exact False.elim (hNoCol col)

-- The audit commands below run `whnf`/`isDefEq` on theorem premises and tooth witnesses over
-- symbolic field elements and digests. Unfolding `Goldilocks.mul` (128-bit reduction with nested
-- case splits) or the `Poseidon2` permutation on symbolic inputs exhausts the heartbeat budget, so
-- both primitives are sealed for the audits (after every proof that computes with them).
attribute [local irreducible] Goldilocks.mul poseidon2Perm12

section RecursiveTreeFixtures
open Aggregation RoundPoly

/-! ### Concrete recursive-tree fixtures (evaluated here; audited and paired in `Tests/RecursiveAggregationTeeth`) -/

def headerShardZero : RecursiveShardHeader :=
  { shardId := 0, threshold := 2, committeeSize := 3, validCount := 2,
    publicDigest := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ }

def headerShardP : RecursiveShardHeader :=
  { shardId := goldilocksPrime, threshold := 2, committeeSize := 3, validCount := 2,
    publicDigest := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ }

/-- The two headers differ, reduce to one `Poseidon2` preimage (hence one digest), and only the
    canonical one passes `verifyRecursiveShardHeader`: without the `shardId < p` check the tree
    would carry two distinct shard ids under one digest. -/
theorem tooth_noncanonical_shard_header_collides_and_is_rejected :
    ∃ h1 h2 : RecursiveShardHeader,
      ¬ (h1 = h2) ∧
      leafShardHeaderPreimage h1 = leafShardHeaderPreimage h2 ∧
      hashLeafShardHeader h1 = hashLeafShardHeader h2 ∧
      verifyRecursiveShardHeader h1 = true ∧
      verifyRecursiveShardHeader h2 = false := by
  have hP : Goldilocks.ofNat goldilocksPrime = Goldilocks.ofNat 0 := by decide
  have hPre : leafShardHeaderPreimage headerShardZero = leafShardHeaderPreimage headerShardP := by
    unfold leafShardHeaderPreimage headerShardZero headerShardP
    dsimp only
    rw [hP]
  refine ⟨headerShardZero, headerShardP, by decide, hPre, ?_, by decide, by decide⟩
  unfold hashLeafShardHeader
  rw [hPre]

/-- Positive instance of `leafShardHeaderPreimage_injective`: two canonical headers. -/
theorem inhabited_canonical_shard_headers :
    verifyRecursiveShardHeader headerShardZero = true ∧
    verifyRecursiveShardHeader { headerShardZero with shardId := 1 } = true ∧
    ¬ (leafShardHeaderPreimage headerShardZero =
      leafShardHeaderPreimage { headerShardZero with shardId := 1 }) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  exact absurd (congrArg (fun p : Poseidon2CanopyPreimage => p.initCap.x2.val) h) (by decide)


/-- Frames of two absorbed one-limb messages, each followed by its squeeze frame. -/
private def swapRoundFrames (x y : Nat) : List FsFrame :=
  [⟨Goldilocks.ofNat 10, [Goldilocks.ofNat x]⟩, ⟨Goldilocks.ofNat 11, []⟩,
   ⟨Goldilocks.ofNat 10, [Goldilocks.ofNat y]⟩, ⟨Goldilocks.ofNat 11, []⟩]

private theorem swapRoundFrames_blocks (x y : Nat) :
    (fsTranscriptBlocks (swapRoundFrames x y)).map FsBlock.addend =
      poseidon2SwapRoundKatBlocks x y := by
  rw [poseidon2SwapRoundKatBlocks.public_eqs]
  simp only [poseidon2DuplexBlock.public_eqs]
  rfl

/-- Frames of the child-verifier transcript up to the first fold-challenge squeeze, at bottom
    depth `1`, canopy depth `0`, zero digests and claim, and sumcheck messages `[a,0,0,0]`,
    `[b,0,0,0]`. -/
private def swapSumcheckFrames (a b : Nat) : List FsFrame :=
  [⟨Goldilocks.ofNat 1, [childWhirVersion, Goldilocks.ofNat 1, Goldilocks.ofNat 0]⟩,
   ⟨Goldilocks.ofNat 2, List.replicate 12 Goldilocks.zero⟩,
   ⟨Goldilocks.ofNat 3, List.replicate 4 Goldilocks.zero⟩,
   ⟨Goldilocks.ofNat 10, [Goldilocks.ofNat a, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero]⟩,
   ⟨Goldilocks.ofNat 11, []⟩,
   ⟨Goldilocks.ofNat 10, [Goldilocks.ofNat b, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero]⟩,
   ⟨Goldilocks.ofNat 11, []⟩,
   ⟨Goldilocks.ofNat 12, []⟩, ⟨Goldilocks.ofNat 13, []⟩]

private theorem swapSumcheckFrames_blocks (a b : Nat) :
    (fsTranscriptBlocks (swapSumcheckFrames a b)).map FsBlock.addend =
      poseidon2SwapSumcheckKatBlocks a b := by
  rw [poseidon2SwapSumcheckKatBlocks.public_eqs]
  simp only [poseidon2DuplexBlock.public_eqs]
  rfl

def swapRoundA : FsRound := ⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 1], [Goldilocks.ofNat 11]⟩

def swapRoundB : FsRound := ⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 2], [Goldilocks.ofNat 11]⟩


def swapZeroLane : Lane4 := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩


/-- The frame encoding separates a message from its split: one frame `[1, 2]` and two frames
    `[1]`, `[2]` under the same tag have different block encodings. -/
theorem tooth_frame_boundary_is_encoded :
    ¬ (fsTranscriptBlocks [⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 1, Goldilocks.ofNat 2]⟩] =
       fsTranscriptBlocks [⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 1]⟩,
         ⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 2]⟩]) := by
  decide

private theorem filter_false_nil {α : Type} : ∀ l : List α, l.filter (fun _ => false) = []
  | [] => rfl
  | _ :: l => filter_false_nil l


end RecursiveTreeFixtures

#verify_constructive tooth_noncanonical_shard_header_collides_and_is_rejected inhabited_canonical_shard_headers
  tooth_frame_boundary_is_encoded

#verify_constructive Qsag.canopyLeafPreimage_injective
  Qsag.canopyNodePreimage_injective
  Qsag.canopyLeaf_ne_node_preimage
  Qsag.canopyOpening_payload_unique_of_collision_free
  Qsag.tooth_unsalted_poseidon2_canopy_collision
  Qsag.tooth_missing_domain_tag_leaf_node_confusion
  Qsag.fsTranscriptBlocks_injective
  Qsag.leafShardHeaderPreimage_injective
  Qsag.canopySummaryPreimage_injective
  Qsag.recursiveHemQromErrorBound_step


#tooth_pair Qsag.canopyOpening_payload_unique_of_collision_free vs Qsag.tooth_unsalted_poseidon2_canopy_collision
#tooth_pair Qsag.canopyLeaf_ne_node_preimage vs Qsag.tooth_missing_domain_tag_leaf_node_confusion


end Qsag
end
