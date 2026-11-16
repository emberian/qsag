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

/-- Extended WHIR folding geometry `(log₂ blowup, step_vars)` covering `nv ∈ 2..=28`
    (`pcs.rs::MAX_PCS_NUM_VARS = 28`), agreeing verbatim with `hemStageGeometry` and rejecting
    `nv ≥ 29` (`[]`). -/
def hemHighCapStageGeometry (nv : Nat) : List (Nat × Nat) :=
  if nv ≤ 24 then hemStageGeometry nv
  else if nv = 25 then [(2, 6), (4, 4), (6, 4), (8, 3)]
  else if nv = 26 then [(2, 6), (4, 5), (6, 4), (8, 3)]
  else if nv = 27 then [(2, 6), (4, 5), (6, 4), (8, 4)]
  else if nv = 28 then [(2, 6), (4, 6), (6, 4), (8, 4)]
  else []

/-- Early-stop variable count for `nv ∈ 2..=28` (coincides with `hemEarlyStopVars` on `2..=28`
    and uses `8` early-stop variables for `25..=28`). -/
def hemHighCapEarlyStopVars (nv : Nat) : Nat :=
  if nv ≤ 24 then hemEarlyStopVars nv else 8

/-- Resolved per-stage `(stageIdx, logBlowup, stepVars, n, d)` geometry for `nv ∈ 2..=28`. -/
def hemHighCapStageGeoms (nv : Nat) : List HemStageGeom :=
  hemStageGeomsAux 0 nv (hemHighCapStageGeometry nv)

/-- Schedule structural validity mirror (`1..4` stages, blowup in `{4, 16, 64, 256}`,
    `1 ≤ stepVars ≤ 6`, `earlyStopVars + ∑ stepVars = nv`, `1 ≤ earlyStopVars ≤ 8`). -/
def hemHighCapGeometryValid (nv : Nat) : Bool :=
  let g := hemHighCapStageGeometry nv
  decide (1 ≤ g.length ∧ g.length ≤ 4) &&
  g.all (fun p => (p.1 == 2 || p.1 == 4 || p.1 == 6 || p.1 == 8) &&
    decide (1 ≤ p.2 ∧ p.2 ≤ 6)) &&
  decide (hemHighCapEarlyStopVars nv + (g.map (·.2)).sum = nv) &&
  decide (1 ≤ hemHighCapEarlyStopVars nv ∧ hemHighCapEarlyStopVars nv ≤ 8)

/-- High-capacity `[CWYZ26]` Johnson witness rows `(num_vars, stage, A, m, D)` for `nv ∈ 25..=28`
    (`affine_schedule.rs::HIGH_CAPACITY_WITNESSES` verbatim), certified simultaneously across all
    four `HemOptimizedQromSchedule` regimes and `BciksJohnsonQrom128`. -/
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

def hemHighCapStageWitness (sched : HemOptimizedQromSchedule) (nv : Nat) (g : HemStageGeom) :
    Option WhirAffineWitness :=
  (hemHighCapTableRow nv g.stageIdx).map (fun r =>
    { n := g.n, d := g.d, sFolds := g.stepVars, A := r.2.2.1, B := r.2.2.1 - 1,
      m := r.2.2.2.1, D := r.2.2.2.2,
      queries := sched.minQueries g.logBlowup,
      queryTargetBits := sched.pureQueryTargetBits })

def hemHighCapStageCovered (sched : HemOptimizedQromSchedule) (q nv : Nat) (g : HemStageGeom) : Bool :=
  if hemOptimizedStageExhaustive sched g = true then
    (hemHighCapTableRow nv g.stageIdx).isNone
  else
    match hemHighCapStageWitness sched nv g with
    | none => false
    | some w => checkWhirAffineWitness w q && decide (whirAffineStageSimpleNum w + 1 < 1900)

/-- Non-exhaustive stage witnesses for `nv ∈ 2..=28` under `sched`. -/
def hemHighCapStageWitnesses (sched : HemOptimizedQromSchedule) (nv : Nat) : List WhirAffineWitness :=
  (hemHighCapStageGeoms nv).filterMap (fun g =>
    if hemOptimizedStageExhaustive sched g = true then none else hemHighCapStageWitness sched nv g)

/-- Pure distinct-fiber coset query bounds `(A + s_i)_{q_i} / (n)_{q_i}` for `nv ∈ 2..=28`. -/
def hemHighCapQueryBounds (sched : HemOptimizedQromSchedule) (nv : Nat) : List RatBound :=
  (hemHighCapStageWitnesses sched nv).map whirAffinePureQueryBoundOrOne

/-- Degree-3 sumcheck + round-0 cascade RBR profile bound for `nv ∈ 2..=28`, scaling the sumcheck
    round term as `3 * nv` (`= 72` at `nv = 24`, `= 84` at `nv = 28`). -/
def hemHighCapCascadeRbrBound (nv : Nat) : RatBound :=
  match hemHighCapStageWitnesses .cdhzPow16At2pow38 nv with
  | w :: _ =>
    ⟨15 * (whirAffineStageSimpleNum w / w.sFolds) + 3 * nv, goldilocksExt4Card, goldilocksExt4Card_pos⟩
  | [] =>
    ⟨3 * nv, goldilocksExt4Card, goldilocksExt4Card_pos⟩

/-- Multi-round RBR challenge bounds for `nv ∈ 2..=28` (cascade round + one folding round per
    non-exhaustive WHIR stage). -/
def hemHighCapFiveRoundRbrBounds (nv : Nat) : List RatBound :=
  hemHighCapCascadeRbrBound nv ::
    (hemHighCapStageWitnesses .cdhzPow16At2pow38 nv).map whirAffineEqualDegreeCommitFoldBound

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

def slicedHighCapRow (nv stage : Nat) : Option (Nat × Nat × Nat × Nat) :=
  if nv ≤ 24 then slicedStageRow nv stage
  else slicedHighCapExtraTable.find? (fun r => r.1 == nv && r.2.1 == stage)

/-- Proved `nonExcludedDecompBound_sliced` check for high-capacity stages `nv ∈ 25..=28` (`bits ≥ 183`). -/
def slicedHighCapStageCovered (q nv : Nat) (g : HemStageGeom) : Bool :=
  if nv ≤ 24 then slicedStageCovered q nv g
  else
    match hemHighCapTableRow nv g.stageIdx, slicedHighCapRow nv g.stageIdx with
    | some r, some w =>
      slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 &&
        decide (slicedStageCount q g r w * 2 ^ w.2.2.2 ≤ q * q) && decide (183 ≤ w.2.2.2)
    | _, _ => false

/-- Exact parity between `hemHighCapStageGeometry` and `hemStageGeometry` for all `nv : Nat`
    (including rejection `[]` above `MAX_PCS_NUM_VARS = 28`). -/
theorem hemHighCapStageGeometry_eq_hemStageGeometry (nv : Nat) :
    hemHighCapStageGeometry nv = hemStageGeometry nv := by
  unfold hemHighCapStageGeometry
  by_cases h24 : nv ≤ 24
  · simp only [h24, ↓reduceIte]
  · simp only [h24, ↓reduceIte]
    by_cases h28 : nv ≤ 28
    · have hcases : nv = 25 ∨ nv = 26 ∨ nv = 27 ∨ nv = 28 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;> decide
    · have h25 : ¬ nv = 25 := by omega
      have h26 : ¬ nv = 26 := by omega
      have h27 : ¬ nv = 27 := by omega
      have h28' : ¬ nv = 28 := by omega
      simp only [h25, h26, h27, h28', ↓reduceIte]
      exact (hemStageGeometry_nv25_to_28.2.2.2.2 nv (by omega)).symm

/-- **Universal High-Capacity WHIR Coverage Certificate (`hemHighCapSchedule_covers_nv2_to_28`)**:
    1. Every `nv ∈ 2..=28` satisfies `hemHighCapGeometryValid nv = true` (valid 1..4 stage geometry,
       `≤ 6` variables per stage, matching `pcs.rs::MAX_PCS_NUM_VARS = 28`), while `nv ≥ 29` is rejected;
    2. Every stage `g ∈ hemHighCapStageGeoms nv` across ALL `nv ∈ 2..=28` passes `checkWhirAffineWitness`
       at `q = p^4` with simple folding numerator `< 1900` under ALL FOUR QROM schedules
       (`unitaryPow16`, `cdhzPow16At2pow38`, `cdhz320Pow16At2pow40`, `unitaryZeroPow`);
    3. Every stage across ALL `nv ∈ 2..=28` is simultaneously covered by the proved
       `slicedParamsOk` decomposition bound (`bits ≥ 183`);
    4. For `nv ∈ 2..=24`, `hemHighCapTableRow` agrees identically with `hemOptimizedQromTableRow`. -/
theorem hemHighCapSchedule_covers_nv2_to_28 :
    (∀ nv : Nat, 2 ≤ nv → nv ≤ 28 → hemHighCapGeometryValid nv = true) ∧
    (∀ nv : Nat, 29 ≤ nv → hemHighCapStageGeometry nv = [] ∧ hemHighCapGeometryValid nv = false) ∧
    (∀ (sched : HemOptimizedQromSchedule) (nv : Nat), 2 ≤ nv → nv ≤ 28 →
      ∀ g ∈ hemHighCapStageGeoms nv,
        hemHighCapStageCovered sched (goldilocksPrime ^ 4) nv g = true) ∧
    (∀ nv : Nat, 2 ≤ nv → nv ≤ 28 →
      ∀ g ∈ hemHighCapStageGeoms nv,
        slicedHighCapStageCovered (goldilocksPrime ^ 4) nv g = true) ∧
    (∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ s : Nat, s < 4 →
      hemHighCapTableRow nv s = hemOptimizedQromTableRow nv s) := by
  have hGeom : ((List.range 27).all fun i => hemHighCapGeometryValid (i + 2)) = true := by
    decide +kernel
  have hU16 : ((List.range 27).all fun i =>
      (hemHighCapStageGeoms (i + 2)).all
        (hemHighCapStageCovered .unitaryPow16 (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  have hC38 : ((List.range 27).all fun i =>
      (hemHighCapStageGeoms (i + 2)).all
        (hemHighCapStageCovered .cdhzPow16At2pow38 (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  have hC40 : ((List.range 27).all fun i =>
      (hemHighCapStageGeoms (i + 2)).all
        (hemHighCapStageCovered .cdhz320Pow16At2pow40 (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  have hZ0 : ((List.range 27).all fun i =>
      (hemHighCapStageGeoms (i + 2)).all
        (hemHighCapStageCovered .unitaryZeroPow (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  have hSliced : ((List.range 4).all fun i =>
      (hemHighCapStageGeoms (i + 25)).all
        (slicedHighCapStageCovered (goldilocksPrime ^ 4) (i + 25))) = true := by
    decide +kernel
  have hParity : ((List.range 23).all fun i =>
      (List.range 4).all fun s =>
        decide (hemHighCapTableRow (i + 2) s = hemOptimizedQromTableRow (i + 2) s)) = true := by
    decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro nv h2 h28
    have h1 := List.all_eq_true.mp hGeom (nv - 2) (List.mem_range.mpr (by omega))
    have hEq : nv - 2 + 2 = nv := by omega
    rwa [hEq] at h1
  · intro nv h29
    have hEmpty : hemHighCapStageGeometry nv = [] := by
      rw [hemHighCapStageGeometry_eq_hemStageGeometry]
      exact hemStageGeometry_nv25_to_28.2.2.2.2 nv h29
    refine ⟨hEmpty, ?_⟩
    unfold hemHighCapGeometryValid
    rw [hEmpty]
    rfl
  · intro sched nv h2 h28 g hg
    have hEq : nv - 2 + 2 = nv := by omega
    cases sched with
    | unitaryPow16 =>
      have h1 := List.all_eq_true.mp hU16 (nv - 2) (List.mem_range.mpr (by omega))
      rw [hEq] at h1; exact List.all_eq_true.mp h1 g hg
    | cdhzPow16At2pow38 =>
      have h1 := List.all_eq_true.mp hC38 (nv - 2) (List.mem_range.mpr (by omega))
      rw [hEq] at h1; exact List.all_eq_true.mp h1 g hg
    | cdhz320Pow16At2pow40 =>
      have h1 := List.all_eq_true.mp hC40 (nv - 2) (List.mem_range.mpr (by omega))
      rw [hEq] at h1; exact List.all_eq_true.mp h1 g hg
    | unitaryZeroPow =>
      have h1 := List.all_eq_true.mp hZ0 (nv - 2) (List.mem_range.mpr (by omega))
      rw [hEq] at h1; exact List.all_eq_true.mp h1 g hg
  · intro nv h2 h28 g hg
    by_cases h24 : nv ≤ 24
    · have hgeoms : hemHighCapStageGeoms nv = hemStageGeoms nv := by
        simp only [hemHighCapStageGeoms, hemHighCapStageGeometry, h24, ↓reduceIte, hemStageGeoms]
      rw [hgeoms] at hg
      have hc := sliced_stage_table_covers_every_canonical_stage.1 nv h2 h24 g hg
      simpa only [slicedHighCapStageCovered, h24, ↓reduceIte] using hc
    · have h1 := List.all_eq_true.mp hSliced (nv - 25) (List.mem_range.mpr (by omega))
      have hEq : nv - 25 + 25 = nv := by omega
      rw [hEq] at h1
      exact List.all_eq_true.mp h1 g hg
  · intro nv h2 h24 s hs
    have h1 := List.all_eq_true.mp hParity (nv - 2) (List.mem_range.mpr (by omega))
    have hEq : nv - 2 + 2 = nv := by omega
    rw [hEq] at h1
    exact of_decide_eq_true (List.all_eq_true.mp h1 s (List.mem_range.mpr hs))


/-- Proved `AffineFoldDecompBound` on every high-capacity stage `nv ∈ 25..=28` via
    `slicedParamsOk_sound` (`bits ≥ 183`). -/
theorem highCap_stage_decomp_bound (nv : Nat) (h25 : 25 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemHighCapStageGeoms nv) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemHighCapTableRow nv g.stageIdx = some r ∧
      slicedHighCapRow nv g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      slicedStageCount (goldilocksPrime ^ 4) g r w * 2 ^ w.2.2.2 ≤
        goldilocksPrime ^ 4 * goldilocksPrime ^ 4 ∧
      183 ≤ w.2.2.2 := by
  have hc := hemHighCapSchedule_covers_nv2_to_28.2.2.2.1 nv (by omega) h28 g hg
  unfold slicedHighCapStageCovered at hc
  have hNot24 : ¬ (nv ≤ 24) := by omega
  simp only [hNot24, ↓reduceIte] at hc
  split at hc
  · next r w hr hw =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    exact ⟨r, w, hr, hw,
      fun D S hD hS hn => slicedParamsOk_sound g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2
        hc.1.1 D S hD hS hn,
      of_decide_eq_true hc.1.2, of_decide_eq_true hc.2⟩
  · exact absurd hc Bool.false_ne_true

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

/-- **High-Capacity `[CDHZ25]` Numerical Profile Budget Across `nv = 2..28` (`hemHighCap_cdhzPow16_budget_nv2_to_28`)**:
    `cdhzPow16At2pow38` (`q = (202, 102, 70, 52)` + 16-bit PoW, `426` total openings) achieves
    a numerical expression below `2^-128` across ALL `nv ∈ 2..=28` (`MAX_PCS_NUM_VARS = 28`)
    and ALL query partitions `wFs + wVc ≤ Q` up to `Q ≤ 2^38`! -/
theorem hemHighCap_cdhzPow16_budget_nv2_to_28 (nv Q wFs wVc : Nat)
    (h2 : 2 ≤ nv) (h28 : nv ≤ 28) (hQ : Q ≤ 2 ^ 38) (hPart : wFs + wVc ≤ Q) :
    strictlyMoreThanBits 128
      (cdhzSnargPartitionBound Q wFs wVc 426 (nv - 2) 256 16
        (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .cdhzPow16At2pow38 nv)) ∧
    atLeastBits 128
      (cdhzSnargPartitionBound Q wFs wVc 426 (nv - 2) 256 16
        (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .cdhzPow16At2pow38 nv)) := by
  have hAll : ((List.range 27).all fun i =>
      let v := i + 2
      decide (strictlyMoreThanBits 128
        (cdhzSnargEnvelopeBound (2 ^ 38) 426 (v - 2) 256 16
          (hemHighCapFiveRoundRbrBounds v) (hemHighCapQueryBounds .cdhzPow16At2pow38 v)))) = true := by
    simp only [cdhzSnargEnvelopeBound, cdhzSnargPartitionBound_def, cdhzPqsrBound_def, cdhzSaltedMerkleOfflineBound_def, cdhzSaltedMerkleOnlineBound_def, cdhzSaltedMerkleComBound_def, hemHighCapFiveRoundRbrBounds, hemHighCapCascadeRbrBound, hemHighCapQueryBounds, hemHighCapStageWitnesses, hemHighCapStageGeoms, hemHighCapStageGeometry, hemHighCapStageWitness, hemHighCapTableRow, hemHighCapWitnessTable, whirAffineStageSimpleNum_def]
    decide +kernel
  have hRow := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  dsimp only at hRow
  rw [hEq] at hRow
  have hTop : strictlyMoreThanBits 128
      (cdhzSnargEnvelopeBound (2 ^ 38) 426 (nv - 2) 256 16
        (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .cdhzPow16At2pow38 nv)) :=
    of_decide_eq_true hRow
  have hPartLe := cdhzSnargPartitionBound_le_envelope Q wFs wVc 426 (nv - 2) 256 16 hPart
    (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .cdhzPow16At2pow38 nv)
  have hEnvLe := cdhzSnargEnvelopeBound_mono_hc hQ 426 (nv - 2) 256 16
    (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .cdhzPow16At2pow38 nv)
  have hStrict := strictlyMoreThanBits_of_le_hc (RatBound.le_trans hPartLe hEnvLe) hTop
  exact ⟨hStrict, Nat.le_of_lt hStrict⟩

/-- **High-Capacity Zero-PoW Numerical Profile Budget Across `nv = 2..28` (`hemHighCap_unitaryZeroPow_budget_nv2_to_28`)**:
    `unitaryZeroPow` (`q = (216, 109, 74, 56)` + 0-bit PoW, `455` openings, zero PoW grinding) achieves
    a numerical expression below `2^-128` across ALL `nv ∈ 2..=28` and ALL `Q + 1 ≤ 2^40`! -/
theorem hemHighCap_unitaryZeroPow_budget_nv2_to_28 (nv Q : Nat)
    (h2 : 2 ≤ nv) (h28 : nv ≤ 28) (hQ : Q + 1 ≤ 2 ^ 40) :
    strictlyMoreThanBits 128
      (powScaledFsQromCompilerBound Q 5 256 0
        (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .unitaryZeroPow nv)) ∧
    atLeastBits 128
      (powScaledFsQromCompilerBound Q 5 256 0
        (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .unitaryZeroPow nv)) := by
  have hAll : ((List.range 27).all fun i =>
      let v := i + 2
      decide (strictlyMoreThanBits 128
        (powScaledFsQromCompilerBound (2 ^ 40 - 1) 5 256 0
          (hemHighCapFiveRoundRbrBounds v) (hemHighCapQueryBounds .unitaryZeroPow v)))) = true := by
    simp only [powScaledFsQromCompilerBound, qromMerkleOnlineExtractBound, hemHighCapFiveRoundRbrBounds, hemHighCapCascadeRbrBound, hemHighCapQueryBounds, hemHighCapStageWitnesses, hemHighCapStageGeoms, hemHighCapStageGeometry, hemHighCapStageWitness, hemHighCapTableRow, hemHighCapWitnessTable, whirAffineStageSimpleNum_def, quantumGroverGrindingBound_def, quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def]
    decide +kernel
  have hRow := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  dsimp only at hRow
  rw [hEq] at hRow
  have hTop : strictlyMoreThanBits 128
      (powScaledFsQromCompilerBound (2 ^ 40 - 1) 5 256 0
        (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .unitaryZeroPow nv)) :=
    of_decide_eq_true hRow
  have hLe := powScaledFsQromCompilerBound_mono_hc (Q := Q) (QMax := 2 ^ 40 - 1) (by omega) 5 256 0
    (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .unitaryZeroPow nv)
  have hStrict := strictlyMoreThanBits_of_le_hc hLe hTop
  exact ⟨hStrict, Nat.le_of_lt hStrict⟩

/-- Under-provisioned linear-SR query schedule at `nv = 28` (`q = (156, 79, 54, 41)`). -/
def hemNv28UnderqueriedBounds : List RatBound :=
  (hemHighCapStageWitnesses .unitaryZeroPow 28).zipWith
    (fun w q => whirAffinePureQueryBoundOrOne { w with queries := q })
    [156, 79, 54, 41]

set_option maxRecDepth 8192 in
/-- `#tooth`: at `nv = 28` (`MAX_PCS_NUM_VARS = 28`), sizing query counts for linear classical SR
    (`q = (156, 79, 54, 41)`) fails `< 2^-128` QROM security at `Q = 2^40 - 1` even with 16-bit PoW,
    certifying mutation sensitivity of `hemHighCap_unitaryZeroPow_budget_nv2_to_28`. -/
theorem tooth_highCap_nv28_underqueried_schedule_fails_qrom :
    ¬ atLeastBits 128
      (powScaledFsQromCompilerBound (2 ^ 40 - 1) 5 256 16
        (hemHighCapFiveRoundRbrBounds 28) hemNv28UnderqueriedBounds) := by
  simp only [hemNv28UnderqueriedBounds, powScaledFsQromCompilerBound, qromMerkleOnlineExtractBound, hemHighCapFiveRoundRbrBounds, hemHighCapCascadeRbrBound, hemHighCapStageWitnesses, hemHighCapStageGeoms, hemHighCapStageGeometry, hemHighCapStageWitness, hemHighCapTableRow, hemHighCapWitnessTable, whirAffineStageSimpleNum_def, quantumGroverGrindingBound_def, quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def]
  decide +kernel


/-! ### Defining equations of the §1 definitions (for modules that do not `import all` this one) -/

theorem hemHighCapStageGeometry_def (nv : Nat) :
    hemHighCapStageGeometry nv =
  if nv ≤ 24 then hemStageGeometry nv
  else if nv = 25 then [(2, 6), (4, 4), (6, 4), (8, 3)]
  else if nv = 26 then [(2, 6), (4, 5), (6, 4), (8, 3)]
  else if nv = 27 then [(2, 6), (4, 5), (6, 4), (8, 4)]
  else if nv = 28 then [(2, 6), (4, 6), (6, 4), (8, 4)]
  else [] := by
  rfl

theorem hemHighCapEarlyStopVars_def (nv : Nat) :
    hemHighCapEarlyStopVars nv =
  if nv ≤ 24 then hemEarlyStopVars nv else 8 := by
  rfl

theorem hemHighCapStageGeoms_def (nv : Nat) :
    hemHighCapStageGeoms nv =
  hemStageGeomsAux 0 nv (hemHighCapStageGeometry nv) := by
  rfl

theorem hemHighCapGeometryValid_def (nv : Nat) :
    hemHighCapGeometryValid nv =
  let g := hemHighCapStageGeometry nv
  decide (1 ≤ g.length ∧ g.length ≤ 4) &&
  g.all (fun p => (p.1 == 2 || p.1 == 4 || p.1 == 6 || p.1 == 8) &&
    decide (1 ≤ p.2 ∧ p.2 ≤ 6)) &&
  decide (hemHighCapEarlyStopVars nv + (g.map (·.2)).sum = nv) &&
  decide (1 ≤ hemHighCapEarlyStopVars nv ∧ hemHighCapEarlyStopVars nv ≤ 8) := by
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

theorem hemHighCapStageWitness_def (sched : HemOptimizedQromSchedule) (nv : Nat) (g : HemStageGeom) :
    hemHighCapStageWitness sched nv g =
  (hemHighCapTableRow nv g.stageIdx).map (fun r =>
    { n := g.n, d := g.d, sFolds := g.stepVars, A := r.2.2.1, B := r.2.2.1 - 1,
      m := r.2.2.2.1, D := r.2.2.2.2,
      queries := sched.minQueries g.logBlowup,
      queryTargetBits := sched.pureQueryTargetBits }) := by
  rfl

theorem hemHighCapStageCovered_def (sched : HemOptimizedQromSchedule) (q nv : Nat) (g : HemStageGeom) :
    hemHighCapStageCovered sched q nv g =
  if hemOptimizedStageExhaustive sched g = true then
    (hemHighCapTableRow nv g.stageIdx).isNone
  else
    match hemHighCapStageWitness sched nv g with
    | none => false
    | some w => checkWhirAffineWitness w q && decide (whirAffineStageSimpleNum w + 1 < 1900) := by
  rfl

theorem hemHighCapStageWitnesses_def (sched : HemOptimizedQromSchedule) (nv : Nat) :
    hemHighCapStageWitnesses sched nv =
  (hemHighCapStageGeoms nv).filterMap (fun g =>
    if hemOptimizedStageExhaustive sched g = true then none else hemHighCapStageWitness sched nv g) := by
  rfl

theorem hemHighCapQueryBounds_def (sched : HemOptimizedQromSchedule) (nv : Nat) :
    hemHighCapQueryBounds sched nv =
  (hemHighCapStageWitnesses sched nv).map whirAffinePureQueryBoundOrOne := by
  rfl

theorem hemHighCapCascadeRbrBound_def (nv : Nat) :
    hemHighCapCascadeRbrBound nv =
  match hemHighCapStageWitnesses .cdhzPow16At2pow38 nv with
  | w :: _ =>
    ⟨15 * (whirAffineStageSimpleNum w / w.sFolds) + 3 * nv, goldilocksExt4Card, goldilocksExt4Card_pos⟩
  | [] =>
    ⟨3 * nv, goldilocksExt4Card, goldilocksExt4Card_pos⟩ := by
  rfl

theorem hemHighCapFiveRoundRbrBounds_def (nv : Nat) :
    hemHighCapFiveRoundRbrBounds nv =
  hemHighCapCascadeRbrBound nv ::
    (hemHighCapStageWitnesses .cdhzPow16At2pow38 nv).map whirAffineEqualDegreeCommitFoldBound := by
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

theorem slicedHighCapRow_def (nv stage : Nat) :
    slicedHighCapRow nv stage =
  if nv ≤ 24 then slicedStageRow nv stage
  else slicedHighCapExtraTable.find? (fun r => r.1 == nv && r.2.1 == stage) := by
  rfl

theorem slicedHighCapStageCovered_def (q nv : Nat) (g : HemStageGeom) :
    slicedHighCapStageCovered q nv g =
  if nv ≤ 24 then slicedStageCovered q nv g
  else
    match hemHighCapTableRow nv g.stageIdx, slicedHighCapRow nv g.stageIdx with
    | some r, some w =>
      slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 &&
        decide (slicedStageCount q g r w * 2 ^ w.2.2.2 ≤ q * q) && decide (183 ≤ w.2.2.2)
    | _, _ => false := by
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

/-- Pack a `QuarticGoldilocks` extension element into 4 `Goldilocks` limbs (bijective). -/
def ext4ToLimbs (e : QuarticGoldilocks) : List Goldilocks :=
  [e.c0.c0, e.c0.c1, e.c1.c0, e.c1.c1]

def ext4ToLane4 (e : QuarticGoldilocks) : Lane4 :=
  ⟨e.c0.c0, e.c0.c1, e.c1.c0, e.c1.c1⟩

def lane4ToExt4 (l : Lane4) : QuarticGoldilocks :=
  ⟨⟨l.x0, l.x1⟩, ⟨l.x2, l.x3⟩⟩

theorem lane4ToExt4_ext4ToLane4 (e : QuarticGoldilocks) : lane4ToExt4 (ext4ToLane4 e) = e := by
  cases e with | mk c0 c1 => cases c0; cases c1; rfl

theorem ext4ToLimbs_injective {a b : QuarticGoldilocks} (h : ext4ToLimbs a = ext4ToLimbs b) :
    a = b := by
  cases a with | mk ac0 ac1 =>
    cases b with | mk bc0 bc1 =>
      cases ac0; cases ac1; cases bc0; cases bc1
      unfold ext4ToLimbs at h
      injection h with h0 htl1
      injection htl1 with h1 htl2
      injection htl2 with h2 htl3
      injection htl3 with h3 _
      subst h0 h1 h2 h3
      rfl

/-- Constant `2` and closed-form `2⁻¹` in `QuarticGoldilocks` (`(p + 1) / 2 mod p`). -/
def ext4Two : QuarticGoldilocks :=
  CommRingOps.add CommRingOps.one CommRingOps.one

def ext4InvTwo : QuarticGoldilocks :=
  ⟨⟨⟨(goldilocksPrime + 1) / 2, by decide⟩, Goldilocks.zero⟩,
   ⟨Goldilocks.zero, Goldilocks.zero⟩⟩

theorem ext4Two_ne_zero : ext4Two ≠ CommRingOps.zero := by
  decide

theorem ext4Two_mul_ext4InvTwo : CommRingOps.mul ext4Two ext4InvTwo = CommRingOps.one := by
  decide

/-- **`[CWYZ26]` Duet Fold Arithmetic Statement (`DuetFoldStatement`)**:
    Mirrors `crates/qsag-agg/src/recursive_fold.rs::DuetFoldStatement` over `QuarticGoldilocks`:
    folds antipodal coset evaluations `(v0, v1) = (f(x), f(-x))` under duet batching challenge
    `theta` and affine fold challenge `(alpha, beta)` into `claimed = f'(x^2)`. -/
structure DuetFoldStatement where
  v0 : QuarticGoldilocks
  v1 : QuarticGoldilocks
  theta : QuarticGoldilocks
  alpha : QuarticGoldilocks
  beta : QuarticGoldilocks
  x : QuarticGoldilocks
  x_sq : QuarticGoldilocks
  inv_two : QuarticGoldilocks
  inv_two_x : QuarticGoldilocks
  claimed : QuarticGoldilocks
  deriving DecidableEq, Repr

/-- Unauthenticated duet-fold gate: checks `2 * inv_two = 1`, `x_sq = x * x`, and
    `claimed = odd + gamma * (even + theta * odd)`, **omitting** `2 * x * inv_two_x = 1`! -/
def duetFoldUnauthenticatedGate (s : DuetFoldStatement) : Bool :=
  let even := CommRingOps.mul (CommRingOps.add s.v0 s.v1) s.inv_two
  let odd := CommRingOps.mul (CommRingOps.sub s.v0 s.v1) s.inv_two_x
  let gamma := CommRingOps.add s.alpha (CommRingOps.mul s.beta s.x_sq)
  let rhs := CommRingOps.add odd
    (CommRingOps.mul gamma (CommRingOps.add even (CommRingOps.mul s.theta odd)))
  decide (CommRingOps.mul ext4Two s.inv_two = CommRingOps.one) &&
  decide (s.x_sq = CommRingOps.mul s.x s.x) &&
  decide (s.claimed = rhs)

/-- **Authenticated `[CWYZ26]` Duet-Fold Relation (`duetFoldAuthenticated`)**:
    Enforces `duetFoldUnauthenticatedGate s` **together with** domain-generator inverse consistency
    `2 * x * inv_two_x = 1`! -/
def duetFoldAuthenticated (s : DuetFoldStatement) : Bool :=
  duetFoldUnauthenticatedGate s &&
  decide (CommRingOps.mul (CommRingOps.mul ext4Two s.x) s.inv_two_x = CommRingOps.one)

private theorem field_right_inv_unique {F : Type} [LawfulField F] {a u1 u2 : F}
    (h1 : CommRingOps.mul a u1 = CommRingOps.one)
    (h2 : CommRingOps.mul a u2 = CommRingOps.one) : u1 = u2 := by
  calc u1 = CommRingOps.mul CommRingOps.one u1 := (LawfulCommRing.one_mul u1).symm
    _ = CommRingOps.mul (CommRingOps.mul u2 a) u1 := by rw [LawfulCommRing.mul_comm u2 a, h2]
    _ = CommRingOps.mul u2 (CommRingOps.mul a u1) := LawfulCommRing.mul_assoc u2 a u1
    _ = CommRingOps.mul u2 CommRingOps.one := by rw [h1]
    _ = u2 := LawfulCommRing.mul_one u2

/-- **Authenticated Duet-Fold Soundness (`authenticated_duet_fold_uniquely_determines_claimed`)**:
    When `duetFoldAuthenticated` holds (enforcing `x_sq = x^2`, `2 * inv_two = 1`, AND
    `2 * x * inv_two_x = 1`), the auxiliary wires `(inv_two, x_sq, inv_two_x)` and the output
    `claimed` are **uniquely determined** by `(v0, v1, theta, alpha, beta, x)` — no adversary can
    deviate from the unique algebraic fold evaluation! -/
theorem authenticated_duet_fold_uniquely_determines_claimed (s1 s2 : DuetFoldStatement)
    (h1 : duetFoldAuthenticated s1 = true)
    (h2 : duetFoldAuthenticated s2 = true)
    (hv0 : s1.v0 = s2.v0) (hv1 : s1.v1 = s2.v1) (hth : s1.theta = s2.theta)
    (hal : s1.alpha = s2.alpha) (hbe : s1.beta = s2.beta) (hx : s1.x = s2.x) :
    s1.x ≠ CommRingOps.zero ∧
    s1.inv_two = s2.inv_two ∧
    s1.x_sq = s2.x_sq ∧
    s1.inv_two_x = s2.inv_two_x ∧
    s1.claimed = s2.claimed := by
  unfold duetFoldAuthenticated duetFoldUnauthenticatedGate at h1 h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  rcases h1 with ⟨⟨⟨hInv2_1, hxSq_1⟩, hCl_1⟩, hInv2x_1⟩
  rcases h2 with ⟨⟨⟨hInv2_2, hxSq_2⟩, hCl_2⟩, hInv2x_2⟩
  have hxNe0 : s1.x ≠ CommRingOps.zero := by
    intro hx0
    rw [hx0, LawfulCommRing.mul_zero, LawfulCommRing.zero_mul] at hInv2x_1
    exact LawfulField.zero_ne_one hInv2x_1
  have hEqInv2 : s1.inv_two = s2.inv_two := field_right_inv_unique hInv2_1 hInv2_2
  have hEqXsq : s1.x_sq = s2.x_sq := by rw [hxSq_1, hxSq_2, hx]
  have hInv2x_2' : CommRingOps.mul (CommRingOps.mul ext4Two s1.x) s2.inv_two_x = CommRingOps.one := by
    rwa [hx]
  have hEqInv2x : s1.inv_two_x = s2.inv_two_x := field_right_inv_unique hInv2x_1 hInv2x_2'
  refine ⟨hxNe0, hEqInv2, hEqXsq, hEqInv2x, ?_⟩
  rw [hCl_1, hCl_2, hv0, hv1, hth, hal, hbe, hEqInv2, hEqXsq, hEqInv2x]

/-- **Constructive Forger Witness for Unauthenticated `inv_two_x`
    (`tooth_unverified_inv_two_x_forges_duet_fold`)**:
    If `DuetFoldStatement` omits `2 * x * inv_two_x = 1` (`duetFoldUnauthenticatedGate`), then for
    **EVERY** `(v0, v1, theta, alpha, beta, x)` with `v0 ≠ v1` and non-degenerate fold multiplier
    `1 + (alpha + beta * x^2) * theta ≠ 0`, and for **EVERY** forged target `forgedClaimed : QuarticGoldilocks`,
    an explicit closed-form `inv_two_x` witness makes `duetFoldUnauthenticatedGate` accept `forgedClaimed`! -/
theorem tooth_unverified_inv_two_x_forges_duet_fold
    (v0 v1 theta alpha beta x forgedClaimed : QuarticGoldilocks)
    (hvNe : v0 ≠ v1)
    (hDenomNe :
      CommRingOps.add CommRingOps.one
        (CommRingOps.mul (CommRingOps.add alpha (CommRingOps.mul beta (CommRingOps.mul x x))) theta) ≠
      CommRingOps.zero) :
    ∃ inv_two_x_forge : QuarticGoldilocks,
      duetFoldUnauthenticatedGate
        { v0 := v0, v1 := v1, theta := theta, alpha := alpha, beta := beta,
          x := x, x_sq := CommRingOps.mul x x, inv_two := ext4InvTwo,
          inv_two_x := inv_two_x_forge, claimed := forgedClaimed } = true := by
  let x_sq := CommRingOps.mul x x
  let even := CommRingOps.mul (CommRingOps.add v0 v1) ext4InvTwo
  let gamma := CommRingOps.add alpha (CommRingOps.mul beta x_sq)
  let denom := CommRingOps.add CommRingOps.one (CommRingOps.mul gamma theta)
  let diff := CommRingOps.sub v0 v1
  have hDiffNe : diff ≠ CommRingOps.zero := fun h0 =>
    hvNe (LawfulCommRing.sub_eq_zero_iff.mp h0)
  let targetOdd := CommRingOps.mul (CommRingOps.sub forgedClaimed (CommRingOps.mul gamma even))
    (LawfulField.inv denom)
  let forgeW := CommRingOps.mul targetOdd (LawfulField.inv diff)
  refine ⟨forgeW, ?_⟩
  unfold duetFoldUnauthenticatedGate
  dsimp only
  have hOddEq : CommRingOps.mul diff forgeW = targetOdd := by
    dsimp only [forgeW]
    calc CommRingOps.mul diff (CommRingOps.mul targetOdd (LawfulField.inv diff))
        = CommRingOps.mul targetOdd (CommRingOps.mul diff (LawfulField.inv diff)) := by
            constructive_ring
      _ = CommRingOps.mul targetOdd CommRingOps.one := by
            rw [LawfulField.mul_inv_cancel hDiffNe]
      _ = targetOdd := LawfulCommRing.mul_one targetOdd
  have hRhsEq : CommRingOps.add (CommRingOps.mul diff forgeW)
      (CommRingOps.mul gamma (CommRingOps.add even (CommRingOps.mul theta (CommRingOps.mul diff forgeW)))) =
      forgedClaimed := by
    rw [hOddEq]
    have hLin : CommRingOps.add targetOdd
        (CommRingOps.mul gamma (CommRingOps.add even (CommRingOps.mul theta targetOdd))) =
        CommRingOps.add (CommRingOps.mul gamma even) (CommRingOps.mul targetOdd denom) := by
      dsimp only [denom]
      constructive_ring
    rw [hLin]
    dsimp only [targetOdd]
    have hCancel : CommRingOps.mul
        (CommRingOps.mul (CommRingOps.sub forgedClaimed (CommRingOps.mul gamma even)) (LawfulField.inv denom))
        denom = CommRingOps.sub forgedClaimed (CommRingOps.mul gamma even) := by
      calc CommRingOps.mul
            (CommRingOps.mul (CommRingOps.sub forgedClaimed (CommRingOps.mul gamma even)) (LawfulField.inv denom))
            denom
          = CommRingOps.mul (CommRingOps.sub forgedClaimed (CommRingOps.mul gamma even))
              (CommRingOps.mul denom (LawfulField.inv denom)) := by constructive_ring
        _ = CommRingOps.mul (CommRingOps.sub forgedClaimed (CommRingOps.mul gamma even))
              CommRingOps.one := by rw [LawfulField.mul_inv_cancel hDenomNe]
        _ = CommRingOps.sub forgedClaimed (CommRingOps.mul gamma even) :=
              LawfulCommRing.mul_one _
    rw [hCancel]
    constructive_ring
  rw [decide_eq_true ext4Two_mul_ext4InvTwo, decide_eq_true rfl, decide_eq_true hRhsEq.symm]
  rfl

/-- Concrete separation witness: a forged `DuetFoldStatement` accepted by `duetFoldUnauthenticatedGate`
    and rejected (`= false`) by `duetFoldAuthenticated`. -/
theorem tooth_unverified_inv_two_x_concrete_rejected :
    ∃ sForge : DuetFoldStatement,
      duetFoldUnauthenticatedGate sForge = true ∧
      duetFoldAuthenticated sForge = false := by
  let sForge : DuetFoldStatement :=
    { v0 := CommRingOps.one, v1 := CommRingOps.zero,
      theta := CommRingOps.zero, alpha := CommRingOps.zero, beta := CommRingOps.zero,
      x := CommRingOps.one, x_sq := CommRingOps.one,
      inv_two := ext4InvTwo,
      inv_two_x := CommRingOps.one,
      claimed := CommRingOps.one }
  exact ⟨sForge, by decide, by decide⟩

/-- Sumcheck univariate round chain: each round polynomial `p_i` has degree `≤ 3` (`p_i.length ≤ 4`),
    satisfies `p_i(0) + p_i(1) = curClaim`, and updates `curClaim := p_i(r_i)`. -/
def verifySumcheckChain :
    QuarticGoldilocks → List (List QuarticGoldilocks × QuarticGoldilocks) → Option QuarticGoldilocks
  | curClaim, [] => some curClaim
  | curClaim, (poly, chal) :: rest =>
    let v0 := RoundPoly.evalCoeffs poly CommRingOps.zero
    let v1 := RoundPoly.evalCoeffs poly CommRingOps.one
    if decide (poly.length ≤ 4) && decide (CommRingOps.add v0 v1 = curClaim) then
      verifySumcheckChain (RoundPoly.evalCoeffs poly chal) rest
    else
      none

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

theorem lane4ToExt4_injective {a b : Lane4} (h : lane4ToExt4 a = lane4ToExt4 b) : a = b := by
  cases a; cases b
  unfold lane4ToExt4 at h
  injection h with h0 h1
  injection h0 with e0 e1
  injection h1 with e2 e3
  dsimp only at e0 e1 e2 e3
  subst e0 e1 e2 e3
  rfl

/-- The challenge read after the frame list `frames`: state limbs `0..4` as an extension element
    (`Transcript::ext` reads them after its own empty frame, which is the last frame of `frames`). -/
def fsSqueeze (frames : List FsFrame) : QuarticGoldilocks :=
  lane4ToExt4 (fsSpongeState frames).b0

/-- Two different block sequences that lead the duplex to the same squeezed lane. -/
structure FsSpongeCollision where
  blocks1 : List FsBlock
  blocks2 : List FsBlock
  hne : blocks1 ≠ blocks2
  hcol : (blocks1.foldl fsDuplexStep fsZeroState).b0 = (blocks2.foldl fsDuplexStep fsZeroState).b0

/-- **Challenge binding.** Two canonical frame lists with the same squeezed challenge are equal,
    or their block encodings are an explicit `FsSpongeCollision`. -/
def fsSqueeze_binding (fs gs : List FsFrame)
    (hf : ∀ f ∈ fs, f.msg.length < goldilocksPrime)
    (hg : ∀ g ∈ gs, g.msg.length < goldilocksPrime)
    (hEq : fsSqueeze fs = fsSqueeze gs) :
    PSum (PLift (fs = gs)) FsSpongeCollision :=
  if h : fs = gs then .inl ⟨h⟩
  else
    .inr ⟨fsTranscriptBlocks fs, fsTranscriptBlocks gs,
      fun hb => h (fsTranscriptBlocks_injective fs gs hf hg hb), by
        have hL := lane4ToExt4_injective hEq
        rw [fsSpongeState_eq_blocks, fsSpongeState_eq_blocks] at hL
        exact hL⟩

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

/-- Challenges squeezed with tags `ts` after the frames `pre`: each squeeze absorbs its empty
    frame, so later challenges also depend on the earlier squeezes. -/
def fsSqueezeRun (pre : List FsFrame) : List Goldilocks → List QuarticGoldilocks
  | [] => []
  | t :: ts => fsSqueeze (pre ++ [⟨t, []⟩]) :: fsSqueezeRun (pre ++ [⟨t, []⟩]) ts

/-- Challenges of the LAST round of `rounds`, given the frames `acc` absorbed before `rounds`. -/
def fsDeriveAux (acc : List FsFrame) : List FsRound → List QuarticGoldilocks
  | [] => []
  | [r] => fsSqueezeRun (acc ++ [⟨r.tag, r.msg⟩]) r.squeezes
  | r :: r' :: rs => fsDeriveAux (acc ++ r.frames) (r' :: rs)

/-- **Challenge derivation of the child verifier**: the challenges of a round are squeezed from
    the duplex state after every earlier round (absorbs and squeezes) and the round's own absorb.
    This is the `derive` argument of `fsReplay`. -/
def fsDeriveChallenges (rounds : List FsRound) : List QuarticGoldilocks :=
  fsDeriveAux [] rounds

/-- Limbs of a list of extension elements (`Transcript::absorb_exts`). -/
def ext4ListLimbs : List QuarticGoldilocks → List Goldilocks
  | [] => []
  | e :: es => ext4ToLimbs e ++ ext4ListLimbs es

def lane4Limbs (l : Lane4) : List Goldilocks := [l.x0, l.x1, l.x2, l.x3]

/-- `recursive_whir.rs::VERSION`. -/
def childWhirVersion : Goldilocks := Goldilocks.ofNat 0x4657484952000001

/-- Prover rounds of the child verifier, in the absorb order of `recursive_whir.rs::verify_gadget`
    restricted to the objects of this model:
    `absorb(1, geometry)`, `absorb(2, public)`, `absorb(3, root)`, then for every sumcheck round
    `absorb(10, poly)` followed by `ext(11)`, then the (empty) shift-wire frame `absorb(12, [])`
    followed by `ext(13), ext(14), ext(15)` (`theta, alpha, beta`), then `absorb(21, final_coeffs)`
    followed by the query-index squeeze `ext(40)`. The final polynomial is absorbed before the
    query index is drawn. -/
def childWhirRounds (publicDigest : Lane4) (bottomDepth canopyDepth : Nat) (salt : Lane4)
    (initialClaim : QuarticGoldilocks) (canopyRoot : Lane4)
    (sumcheckPolys : List (List QuarticGoldilocks)) (earlyStopPoly : List QuarticGoldilocks) :
    List FsRound :=
  [ ⟨Goldilocks.ofNat 1,
      [childWhirVersion, Goldilocks.ofNat bottomDepth, Goldilocks.ofNat canopyDepth], []⟩,
    ⟨Goldilocks.ofNat 2,
      lane4Limbs publicDigest ++ lane4Limbs salt ++ ext4ToLimbs initialClaim, []⟩,
    ⟨Goldilocks.ofNat 3, lane4Limbs canopyRoot, []⟩ ] ++
  sumcheckPolys.map (fun p => ⟨Goldilocks.ofNat 10, ext4ListLimbs p, [Goldilocks.ofNat 11]⟩) ++
  [ ⟨Goldilocks.ofNat 12, [],
      [Goldilocks.ofNat 13, Goldilocks.ofNat 14, Goldilocks.ofNat 15]⟩,
    ⟨Goldilocks.ofNat 21, ext4ListLimbs earlyStopPoly, [Goldilocks.ofNat 40]⟩ ]

/-- The Fiat–Shamir transcript of the child verifier: every round with its derived challenges
    (`fsReplay` of `Qsag.Oracle.FiatShamir` with the duplex derivation). -/
def childWhirTranscript (publicDigest : Lane4) (bottomDepth canopyDepth : Nat) (salt : Lane4)
    (initialClaim : QuarticGoldilocks) (canopyRoot : Lane4)
    (sumcheckPolys : List (List QuarticGoldilocks)) (earlyStopPoly : List QuarticGoldilocks) :
    List (FsRound × List QuarticGoldilocks) :=
  fsReplay fsDeriveChallenges
    (childWhirRounds publicDigest bottomDepth canopyDepth salt initialClaim canopyRoot
      sumcheckPolys earlyStopPoly)

/-- The challenges the child verifier uses, read off `childWhirTranscript` by round position. -/
structure ChildWhirChallenges where
  sumcheck : List QuarticGoldilocks
  theta : QuarticGoldilocks
  alpha : QuarticGoldilocks
  beta : QuarticGoldilocks
  queryWord : Goldilocks
  deriving DecidableEq, Repr

def childWhirChallenges (publicDigest : Lane4) (bottomDepth canopyDepth : Nat) (salt : Lane4)
    (initialClaim : QuarticGoldilocks) (canopyRoot : Lane4)
    (sumcheckPolys : List (List QuarticGoldilocks)) (earlyStopPoly : List QuarticGoldilocks) :
    ChildWhirChallenges :=
  let cs := (childWhirTranscript publicDigest bottomDepth canopyDepth salt initialClaim canopyRoot
    sumcheckPolys earlyStopPoly).map Prod.snd
  let n := sumcheckPolys.length
  let fold := cs.getD (3 + n) []
  { sumcheck := ((cs.drop 3).take n).map (fun c => c.headD (CommRingOps.zero : QuarticGoldilocks))
    theta := fold.getD 0 CommRingOps.zero
    alpha := fold.getD 1 CommRingOps.zero
    beta := fold.getD 2 CommRingOps.zero
    queryWord := ((cs.getD (4 + n) []).headD (CommRingOps.zero : QuarticGoldilocks)).c0.c0 }

theorem childWhirRounds_length (publicDigest : Lane4) (bottomDepth canopyDepth : Nat) (salt : Lane4)
    (initialClaim : QuarticGoldilocks) (canopyRoot : Lane4)
    (sumcheckPolys : List (List QuarticGoldilocks)) (earlyStopPoly : List QuarticGoldilocks) :
    (childWhirRounds publicDigest bottomDepth canopyDepth salt initialClaim canopyRoot
      sumcheckPolys earlyStopPoly).length = sumcheckPolys.length + 5 := by
  unfold childWhirRounds
  rw [List.length_append, List.length_append, List.length_map]
  simp only [List.length_cons, List.length_nil]
  omega

/-- Every sumcheck round has exactly one derived challenge: `zip` in `ChildWhirCircuitAccepts`
    drops nothing. -/
theorem childWhirChallenges_sumcheck_length (publicDigest : Lane4) (bottomDepth canopyDepth : Nat)
    (salt : Lane4) (initialClaim : QuarticGoldilocks) (canopyRoot : Lane4)
    (sumcheckPolys : List (List QuarticGoldilocks)) (earlyStopPoly : List QuarticGoldilocks) :
    (childWhirChallenges publicDigest bottomDepth canopyDepth salt initialClaim canopyRoot
      sumcheckPolys earlyStopPoly).sumcheck.length = sumcheckPolys.length := by
  unfold childWhirChallenges childWhirTranscript
  dsimp only
  rw [List.length_map, List.length_take, List.length_drop, List.length_map, fsReplay_length,
    childWhirRounds_length]
  omega

/-- **Each child challenge is a function of the round prefix only**: the challenges of round `i`
    are `fsDeriveChallenges` of the first `i + 1` rounds. -/
theorem childWhirTranscript_challenge (publicDigest : Lane4) (bottomDepth canopyDepth : Nat)
    (salt : Lane4) (initialClaim : QuarticGoldilocks) (canopyRoot : Lane4)
    (sumcheckPolys : List (List QuarticGoldilocks)) (earlyStopPoly : List QuarticGoldilocks)
    (i : Nat) (hi : i < sumcheckPolys.length + 5) :
    ((childWhirTranscript publicDigest bottomDepth canopyDepth salt initialClaim canopyRoot
      sumcheckPolys earlyStopPoly).map Prod.snd)[i]? =
      some (fsDeriveChallenges ((childWhirRounds publicDigest bottomDepth canopyDepth salt
        initialClaim canopyRoot sumcheckPolys earlyStopPoly).take (i + 1))) := by
  unfold childWhirTranscript
  exact fsReplay_challenge fsDeriveChallenges _ i
    (by rw [childWhirRounds_length]; exact hi)

/-- Child-WHIR verifier witness: salted `Poseidon2` Canopy commitment, the sumcheck round
    polynomials in round order, the two openings of the queried antipodal coset, the `[CWYZ26]`
    duet-fold statement and the final early-stop polynomial. It carries no challenge: every
    challenge is derived by `childWhirChallenges`. -/
structure ChildWhirWitness where
  salt : Lane4
  canopyRoot : Lane4
  bottomDepth : Nat
  canopyDepth : Nat
  initialClaim : QuarticGoldilocks
  sumcheckPolys : List (List QuarticGoldilocks)
  opening0 : Poseidon2CanopyOpening
  opening1 : Poseidon2CanopyOpening
  duetFold : DuetFoldStatement
  earlyStopPoly : List QuarticGoldilocks
  deriving DecidableEq, Repr

/-- **Child-WHIR circuit relation (`ChildWhirCircuitAccepts`)**. With
    `ch := childWhirChallenges publicDigest …` (derived from the sequential transcript) and
    `groups := 2 ^ (treeDepth - 1)`, `g := ch.queryWord mod groups`:
    1. the sumcheck chain over `sumcheckPolys` with the derived round challenges ends in
       `duetFold.claimed`;
    2. the tree has depth at least one, and both openings verify against `(salt, canopyRoot)`;
    3. the openings are the derived antipodal coset `(g, g + groups)` and carry `(v0, v1)`;
    4. `duetFold` uses the derived `(theta, alpha, beta)` and satisfies `duetFoldAuthenticated`;
    5. the early-stop polynomial has at most `256` coefficients and evaluates to
       `duetFold.claimed` at `duetFold.x_sq`. -/
def ChildWhirCircuitAccepts (publicDigest : Lane4) (w : ChildWhirWitness) : Bool :=
  let ch := childWhirChallenges publicDigest w.bottomDepth w.canopyDepth w.salt w.initialClaim
    w.canopyRoot w.sumcheckPolys w.earlyStopPoly
  let groups := 2 ^ (w.bottomDepth + w.canopyDepth - 1)
  let g := ch.queryWord.val % groups
  decide (verifySumcheckChain w.initialClaim (w.sumcheckPolys.zip ch.sumcheck) =
    some w.duetFold.claimed) &&
  (decide (1 ≤ w.bottomDepth + w.canopyDepth) &&
  (verifyPoseidon2CanopyOpening w.salt w.canopyRoot w.bottomDepth w.canopyDepth w.opening0 &&
  (verifyPoseidon2CanopyOpening w.salt w.canopyRoot w.bottomDepth w.canopyDepth w.opening1 &&
  (decide (w.opening0.leafIdx = g) &&
  (decide (w.opening1.leafIdx = g + groups) &&
  (decide (w.opening0.payload = ext4ToLimbs w.duetFold.v0) &&
  (decide (w.opening1.payload = ext4ToLimbs w.duetFold.v1) &&
  (decide (w.duetFold.theta = ch.theta) &&
  (decide (w.duetFold.alpha = ch.alpha) &&
  (decide (w.duetFold.beta = ch.beta) &&
  (duetFoldAuthenticated w.duetFold &&
  (decide (w.earlyStopPoly.length ≤ 256) &&
  decide (RoundPoly.evalCoeffs w.earlyStopPoly w.duetFold.x_sq = w.duetFold.claimed)))))))))))))

/-- The conjuncts of `ChildWhirCircuitAccepts`. -/
theorem ChildWhirCircuitAccepts_iff (publicDigest : Lane4) (w : ChildWhirWitness) :
    ChildWhirCircuitAccepts publicDigest w = true ↔
    (verifySumcheckChain w.initialClaim (w.sumcheckPolys.zip
        (childWhirChallenges publicDigest w.bottomDepth w.canopyDepth w.salt w.initialClaim
          w.canopyRoot w.sumcheckPolys w.earlyStopPoly).sumcheck) = some w.duetFold.claimed ∧
     1 ≤ w.bottomDepth + w.canopyDepth ∧
     verifyPoseidon2CanopyOpening w.salt w.canopyRoot w.bottomDepth w.canopyDepth w.opening0 = true ∧
     verifyPoseidon2CanopyOpening w.salt w.canopyRoot w.bottomDepth w.canopyDepth w.opening1 = true ∧
     w.opening0.leafIdx =
       (childWhirChallenges publicDigest w.bottomDepth w.canopyDepth w.salt w.initialClaim
         w.canopyRoot w.sumcheckPolys w.earlyStopPoly).queryWord.val %
         2 ^ (w.bottomDepth + w.canopyDepth - 1) ∧
     w.opening1.leafIdx =
       (childWhirChallenges publicDigest w.bottomDepth w.canopyDepth w.salt w.initialClaim
         w.canopyRoot w.sumcheckPolys w.earlyStopPoly).queryWord.val %
         2 ^ (w.bottomDepth + w.canopyDepth - 1) + 2 ^ (w.bottomDepth + w.canopyDepth - 1) ∧
     w.opening0.payload = ext4ToLimbs w.duetFold.v0 ∧
     w.opening1.payload = ext4ToLimbs w.duetFold.v1 ∧
     w.duetFold.theta =
       (childWhirChallenges publicDigest w.bottomDepth w.canopyDepth w.salt w.initialClaim
         w.canopyRoot w.sumcheckPolys w.earlyStopPoly).theta ∧
     w.duetFold.alpha =
       (childWhirChallenges publicDigest w.bottomDepth w.canopyDepth w.salt w.initialClaim
         w.canopyRoot w.sumcheckPolys w.earlyStopPoly).alpha ∧
     w.duetFold.beta =
       (childWhirChallenges publicDigest w.bottomDepth w.canopyDepth w.salt w.initialClaim
         w.canopyRoot w.sumcheckPolys w.earlyStopPoly).beta ∧
     duetFoldAuthenticated w.duetFold = true ∧
     w.earlyStopPoly.length ≤ 256 ∧
     RoundPoly.evalCoeffs w.earlyStopPoly w.duetFold.x_sq = w.duetFold.claimed) := by
  unfold ChildWhirCircuitAccepts
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- Canopy multi-opening soundness for `ChildWhirCircuitAccepts`: two accepting witnesses over the
    same `(salt, canopyRoot, bottomDepth, canopyDepth)` that open the same first leaf carry the
    same `duetFold.v0`, or yield an explicit `Poseidon2CanopyCollision`. -/
def extractChildWhirOpeningConsistency (pub1 pub2 : Lane4) (w1 w2 : ChildWhirWitness)
    (hSalt : w1.salt = w2.salt) (hRoot : w1.canopyRoot = w2.canopyRoot)
    (hBot : w1.bottomDepth = w2.bottomDepth) (hCan : w1.canopyDepth = w2.canopyDepth)
    (hIdx : w1.opening0.leafIdx = w2.opening0.leafIdx)
    (hAcc1 : ChildWhirCircuitAccepts pub1 w1 = true)
    (hAcc2 : ChildWhirCircuitAccepts pub2 w2 = true) :
    PSum (w1.duetFold.v0 = w2.duetFold.v0) Poseidon2CanopyCollision := by
  have hF1 := (ChildWhirCircuitAccepts_iff pub1 w1).mp hAcc1
  have hF2 := (ChildWhirCircuitAccepts_iff pub2 w2).mp hAcc2
  have hOp1 := hF1.2.2.1
  have hPay1 := hF1.2.2.2.2.2.2.1
  have hOp2Raw := hF2.2.2.1
  have hPay2 := hF2.2.2.2.2.2.2.1
  rw [← hSalt, ← hRoot, ← hBot, ← hCan] at hOp2Raw
  match extractPoseidon2CanopyCollisionOrOpening w1.salt w1.canopyRoot w1.bottomDepth w1.canopyDepth
      w1.opening0 w2.opening0 hIdx hOp1 hOp2Raw with
  | .inr col => exact .inr col
  | .inl ⟨hPayEq, _, _⟩ =>
    rw [hPay1, hPay2] at hPayEq
    exact .inl (ext4ToLimbs_injective hPayEq)


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

/-- Length-framed bytes of a leaf statement: the registry commitment, the epoch floor, the
    message, the shard's registry row and its signer bitmap. -/
def encodeLeafShardStatement (registryDigest epochFloor msg : List UInt8) (s : HemShardProof) :
    List UInt8 :=
  encodeMultiFrame [registryDigest, epochFloor, msg, encodeRegistration s.registration,
    encodeBitmapBytes s.proof.agg.bitmap]

theorem encodeLeafShardStatement_injective {r1 e1 m1 r2 e2 m2 : List UInt8}
    {s1 s2 : HemShardProof}
    (h : encodeLeafShardStatement r1 e1 m1 s1 = encodeLeafShardStatement r2 e2 m2 s2) :
    r1 = r2 ∧ e1 = e2 ∧ m1 = m2 ∧ s1.registration = s2.registration ∧
      s1.proof.agg.bitmap = s2.proof.agg.bitmap := by
  have h0 := encodeMultiFrame_injective h
  obtain ⟨hr, h1⟩ := List.cons.inj h0
  obtain ⟨he, h2⟩ := List.cons.inj h1
  obtain ⟨hm, h3⟩ := List.cons.inj h2
  obtain ⟨hreg, h4⟩ := List.cons.inj h3
  obtain ⟨hbm, _⟩ := List.cons.inj h4
  exact ⟨hr, he, hm, encodeRegistration_injective hreg, encodeBitmapBytes_injective hbm⟩

def leafShardStatementPreimage (registryDigest epochFloor msg : List UInt8) (s : HemShardProof) :
    Poseidon2CanopyPreimage :=
  { initCap := ⟨poseidon2LeafStatementDomainTag, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
    limbStream := bytesToLimbs56 (encodeLeafShardStatement registryDigest epochFloor msg s) }

/-- `Poseidon2` digest of the leaf statement; the header's `publicDigest`. -/
def leafShardStatementDigest (registryDigest epochFloor msg : List UInt8) (s : HemShardProof) :
    Lane4 :=
  poseidon2CanopyCompress (leafShardStatementPreimage registryDigest epochFloor msg s).initCap
    (leafShardStatementPreimage registryDigest epochFloor msg s).limbStream

theorem leafShardStatementPreimage_injective {r1 e1 m1 r2 e2 m2 : List UInt8}
    {s1 s2 : HemShardProof}
    (h : leafShardStatementPreimage r1 e1 m1 s1 = leafShardStatementPreimage r2 e2 m2 s2) :
    r1 = r2 ∧ e1 = e2 ∧ m1 = m2 ∧ s1.registration = s2.registration ∧
      s1.proof.agg.bitmap = s2.proof.agg.bitmap := by
  unfold leafShardStatementPreimage at h
  injection h with _ hStream
  exact encodeLeafShardStatement_injective (bytesToLimbs56_injective hStream)

/-- The header is the header of this shard: numeric id, threshold, committee size, signer count
    and the statement digest all agree with the shard certificate. -/
def leafHeaderBindsShard (registryDigest epochFloor msg : List UInt8)
    (hdr : RecursiveShardHeader) (s : HemShardProof) : Bool :=
  decide (s.shardId = leb128 hdr.shardId) &&
  decide (hdr.threshold = s.threshold) &&
  decide (hdr.committeeSize = s.inst.committee.length) &&
  decide (hdr.validCount = bitmapPopcountSpec s.proof.agg.bitmap) &&
  decide (hdr.publicDigest = leafShardStatementDigest registryDigest epochFloor msg s)

theorem leafHeaderBindsShard_facts {registryDigest epochFloor msg : List UInt8}
    {hdr : RecursiveShardHeader} {s : HemShardProof}
    (h : leafHeaderBindsShard registryDigest epochFloor msg hdr s = true) :
    s.shardId = leb128 hdr.shardId ∧ hdr.threshold = s.threshold ∧
      hdr.committeeSize = s.inst.committee.length ∧
      hdr.validCount = bitmapPopcountSpec s.proof.agg.bitmap ∧
      hdr.publicDigest = leafShardStatementDigest registryDigest epochFloor msg s := by
  unfold leafHeaderBindsShard at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The header of shard `s` under numeric id `shardId`. -/
def mkLeafShardHeader (registryDigest epochFloor msg : List UInt8) (shardId : Nat)
    (s : HemShardProof) : RecursiveShardHeader :=
  { shardId := shardId
    threshold := s.threshold
    committeeSize := s.inst.committee.length
    validCount := bitmapPopcountSpec s.proof.agg.bitmap
    publicDigest := leafShardStatementDigest registryDigest epochFloor msg s }

theorem leafHeaderBindsShard_mk (registryDigest epochFloor msg : List UInt8) (shardId : Nat)
    (s : HemShardProof) (hId : s.shardId = leb128 shardId) :
    leafHeaderBindsShard registryDigest epochFloor msg
      (mkLeafShardHeader registryDigest epochFloor msg shardId s) s = true := by
  unfold leafHeaderBindsShard mkLeafShardHeader
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_true]
  exact hId

/-- Leaf certificate (`d = 0`): header, the shard certificate it describes, and a child-WHIR proof
    on the header digest. -/
structure RecursiveHemLeafCert where
  header : RecursiveShardHeader
  shard : HemShardProof
  leafProof : ChildWhirWitness

/-- Outer node certificate (`d + 1`) aggregating `children : List Child`. -/
structure RecursiveHemOuterCert (Child : Type) where
  summaryDigest : Lane4
  outerProof : ChildWhirWitness
  children : List Child

/-- Depth-`d` recursive `Hem` aggregate, by structural recursion on `d`:
    `RecursiveHemLeafCert` at depth `0`, `RecursiveHemOuterCert (RecursiveHemAggregate d)` at
    depth `d + 1`. -/
@[expose] def RecursiveHemAggregate : Nat → Type
  | 0 => RecursiveHemLeafCert
  | d + 1 => RecursiveHemOuterCert (RecursiveHemAggregate d)

/-- Summary digest propagated upward by a depth-`d` subtree. -/
def recursiveHemSummaryDigest : (d : Nat) → RecursiveHemAggregate d → Lane4
  | 0, leafCert => hashLeafShardHeader leafCert.header
  | _ + 1, nodeCert => nodeCert.summaryDigest

/-- All leaf certificates of a depth-`d` aggregate, left to right. -/
def recursiveHemLeafCerts : (d : Nat) → RecursiveHemAggregate d → List RecursiveHemLeafCert
  | 0, leafCert => [leafCert]
  | d + 1, nodeCert => nodeCert.children.flatMap (recursiveHemLeafCerts d)

/-- All leaf headers of a depth-`d` aggregate. -/
def recursiveHemLeafHeaders (d : Nat) (agg : RecursiveHemAggregate d) : List RecursiveShardHeader :=
  (recursiveHemLeafCerts d agg).map (·.header)

/-- All leaf shard certificates of a depth-`d` aggregate. -/
def recursiveHemLeafShards (d : Nat) (agg : RecursiveHemAggregate d) : List HemShardProof :=
  (recursiveHemLeafCerts d agg).map (·.shard)

private def verifyChildrenList {α : Type} (recVerify : α → Bool) : List α → Bool
  | [] => true
  | c :: cs => recVerify c && verifyChildrenList recVerify cs

/-- Node verifier. Leaf: canonical header with a valid quorum shape, header bound to the shard
    and to `(registryDigest, epochFloor, msg)`, and an accepting child-WHIR proof on the header
    digest. Inner node: canonical depth and fan-in (`d + 1 < p`, `F < p`), `F` children, the
    `Poseidon2` summary of their digests, an accepting child-WHIR proof on the summary, and every
    child. -/
def verifyRecursiveHemNode (registryDigest epochFloor msg : List UInt8) (F : Nat) :
    (d : Nat) → RecursiveHemAggregate d → Bool
  | 0, leafCert =>
    verifyRecursiveShardHeader leafCert.header &&
    leafHeaderBindsShard registryDigest epochFloor msg leafCert.header leafCert.shard &&
    ChildWhirCircuitAccepts (hashLeafShardHeader leafCert.header) leafCert.leafProof
  | d + 1, nodeCert =>
    decide (d + 1 < goldilocksPrime) &&
    decide (F < goldilocksPrime) &&
    decide (nodeCert.children.length = F) &&
    decide (poseidon2SummaryHash (d + 1) F
      (nodeCert.children.map (recursiveHemSummaryDigest d)) = nodeCert.summaryDigest) &&
    ChildWhirCircuitAccepts nodeCert.summaryDigest nodeCert.outerProof &&
    verifyChildrenList (verifyRecursiveHemNode registryDigest epochFloor msg F d) nodeCert.children

private theorem verifyRecursiveHemNode_zero (registryDigest epochFloor msg : List UInt8) (F : Nat)
    (leafCert : RecursiveHemLeafCert) :
    verifyRecursiveHemNode registryDigest epochFloor msg F 0 leafCert =
      (verifyRecursiveShardHeader leafCert.header &&
       leafHeaderBindsShard registryDigest epochFloor msg leafCert.header leafCert.shard &&
       ChildWhirCircuitAccepts (hashLeafShardHeader leafCert.header) leafCert.leafProof) := by rfl

private theorem verifyRecursiveHemNode_succ (registryDigest epochFloor msg : List UInt8) (F d : Nat)
    (nodeCert : RecursiveHemOuterCert (RecursiveHemAggregate d)) :
    verifyRecursiveHemNode registryDigest epochFloor msg F (d + 1) nodeCert =
      (decide (d + 1 < goldilocksPrime) &&
       decide (F < goldilocksPrime) &&
       decide (nodeCert.children.length = F) &&
       decide (poseidon2SummaryHash (d + 1) F
         (nodeCert.children.map (recursiveHemSummaryDigest d)) = nodeCert.summaryDigest) &&
       ChildWhirCircuitAccepts nodeCert.summaryDigest nodeCert.outerProof &&
       verifyChildrenList (verifyRecursiveHemNode registryDigest epochFloor msg F d)
         nodeCert.children) := by rfl

/-- An accepted inner node has canonical depth and fan-in, exactly `F` children, the `Poseidon2`
    summary of its children's digests as its digest, and an accepting child-WHIR proof on it. -/
theorem verifyRecursiveHemNode_inner_facts (registryDigest epochFloor msg : List UInt8) (F d : Nat)
    (nodeCert : RecursiveHemOuterCert (RecursiveHemAggregate d))
    (h : verifyRecursiveHemNode registryDigest epochFloor msg F (d + 1) nodeCert = true) :
    d + 1 < goldilocksPrime ∧ F < goldilocksPrime ∧ nodeCert.children.length = F ∧
      poseidon2SummaryHash (d + 1) F (nodeCert.children.map (recursiveHemSummaryDigest d)) =
        nodeCert.summaryDigest ∧
      ChildWhirCircuitAccepts nodeCert.summaryDigest nodeCert.outerProof = true := by
  replace h := (verifyRecursiveHemNode_succ registryDigest epochFloor msg F d nodeCert).symm.trans h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

/-- An inner node at a depth that is not a canonical field representative is rejected. -/
theorem verifyRecursiveHemNode_rejects_noncanonical_depth
    (registryDigest epochFloor msg : List UInt8) (F d : Nat)
    (nodeCert : RecursiveHemOuterCert (RecursiveHemAggregate d))
    (hd : goldilocksPrime ≤ d + 1) :
    verifyRecursiveHemNode registryDigest epochFloor msg F (d + 1) nodeCert = false := by
  rw [verifyRecursiveHemNode_succ, decide_eq_false (Nat.not_lt_of_ge hd)]
  simp only [Bool.false_and]

/-- An inner node with a fan-in that is not a canonical field representative is rejected. -/
theorem verifyRecursiveHemNode_rejects_noncanonical_fanIn
    (registryDigest epochFloor msg : List UInt8) (F d : Nat)
    (nodeCert : RecursiveHemOuterCert (RecursiveHemAggregate d))
    (hF : goldilocksPrime ≤ F) :
    verifyRecursiveHemNode registryDigest epochFloor msg F (d + 1) nodeCert = false := by
  rw [verifyRecursiveHemNode_succ, decide_eq_false (Nat.not_lt_of_ge hF)]
  simp only [Bool.and_false, Bool.false_and]

/-- **Inner-node digest binding.** Two accepted inner nodes with the same summary digest sit at
    the same depth, have the same fan-in and the same list of child digests, or their summary
    preimages are an explicit `Poseidon2CanopyCollision`. -/
def recursiveHemNode_summary_binding (registryDigest epochFloor msg : List UInt8)
    (F1 F2 d1 d2 : Nat)
    (n1 : RecursiveHemOuterCert (RecursiveHemAggregate d1))
    (n2 : RecursiveHemOuterCert (RecursiveHemAggregate d2))
    (h1 : verifyRecursiveHemNode registryDigest epochFloor msg F1 (d1 + 1) n1 = true)
    (h2 : verifyRecursiveHemNode registryDigest epochFloor msg F2 (d2 + 1) n2 = true)
    (hEq : n1.summaryDigest = n2.summaryDigest) :
    PSum (PLift (d1 = d2 ∧ F1 = F2 ∧
        n1.children.map (recursiveHemSummaryDigest d1) =
          n2.children.map (recursiveHemSummaryDigest d2)))
      Poseidon2CanopyCollision :=
  have f1 := verifyRecursiveHemNode_inner_facts registryDigest epochFloor msg F1 d1 n1 h1
  have f2 := verifyRecursiveHemNode_inner_facts registryDigest epochFloor msg F2 d2 n2 h2
  match canopySummary_digest_binding (d1 + 1) (d2 + 1) F1 F2
      (n1.children.map (recursiveHemSummaryDigest d1))
      (n2.children.map (recursiveHemSummaryDigest d2))
      f1.1 f1.2.1 f2.1 f2.2.1 (f1.2.2.2.1.trans (hEq.trans f2.2.2.2.1.symm)) with
  | .inl ⟨h⟩ => .inl ⟨⟨Nat.succ.inj h.1, h.2.1, h.2.2⟩⟩
  | .inr col => .inr col

/-- **Recursive tree verifier.** Every node passes `verifyRecursiveHemNode`, and the leaf shard
    certificates, left to right, pass the two-layer root verifier `verifyHierarchicalHem`: the
    registry commitment `H (encodeRegistry …) = registryDigest`, pairwise-distinct shard ids,
    pairwise-disjoint committees, and `verifyHemShard` on every shard (shard-scoped message,
    `1 ≤ threshold ≤ |committee|`, threshold met by the bitmap, accepting succinct aggregate). -/
def verifyRecursiveHemTree (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (F d : Nat) (agg : RecursiveHemAggregate d) :
    Bool :=
  verifyRecursiveHemNode registryDigest epochFloor msg F d agg &&
  verifyHierarchicalHem H arith dom registryDigest epochFloor msg (recursiveHemLeafShards d agg)

theorem verifyRecursiveHemTree_facts {H : Hash} {arith : RowArithmetization} {dom : WhirDomain}
    {registryDigest epochFloor msg : List UInt8} {F d : Nat} {agg : RecursiveHemAggregate d}
    (h : verifyRecursiveHemTree H arith dom registryDigest epochFloor msg F d agg = true) :
    verifyRecursiveHemNode registryDigest epochFloor msg F d agg = true ∧
    verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (recursiveHemLeafShards d agg) = true := by
  unfold verifyRecursiveHemTree at h
  exact Bool.and_eq_true_iff.mp h

private theorem verifyChildrenList_mem {α : Type} (recVerify : α → Bool) :
    ∀ (cs : List α), verifyChildrenList recVerify cs = true → ∀ c ∈ cs, recVerify c = true
  | [], _, _, hc => by cases hc
  | x :: cs, hAll, c, hc => by
    simp only [verifyChildrenList, Bool.and_eq_true] at hAll
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hAll.1
    · exact verifyChildrenList_mem recVerify cs hAll.2 c hc'

/-- Every leaf of an accepted node has a canonical header bound to its shard and an accepting
    child-WHIR proof on the header digest. -/
theorem verifyRecursiveHemNode_leaf_facts (registryDigest epochFloor msg : List UInt8) (F : Nat) :
    ∀ (d : Nat) (agg : RecursiveHemAggregate d),
      verifyRecursiveHemNode registryDigest epochFloor msg F d agg = true →
      ∀ leaf ∈ recursiveHemLeafCerts d agg,
        verifyRecursiveShardHeader leaf.header = true ∧
        leafHeaderBindsShard registryDigest epochFloor msg leaf.header leaf.shard = true ∧
        ChildWhirCircuitAccepts (hashLeafShardHeader leaf.header) leaf.leafProof = true
  | 0, leafCert, h, leaf, hMem => by
    have hMem' : leaf ∈ [leafCert] := hMem
    have hEq : leaf = leafCert := List.mem_singleton.mp hMem'
    replace h := (verifyRecursiveHemNode_zero registryDigest epochFloor msg F leafCert).symm.trans h
    simp only [Bool.and_eq_true] at h
    rw [hEq]
    exact ⟨h.1.1, h.1.2, h.2⟩
  | d + 1, nodeCert, h, leaf, hMem => by
    replace h := (verifyRecursiveHemNode_succ registryDigest epochFloor msg F d nodeCert).symm.trans h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hMem' : leaf ∈ nodeCert.children.flatMap (recursiveHemLeafCerts d) := hMem
    obtain ⟨c, hc, hl⟩ := List.mem_flatMap.mp hMem'
    exact verifyRecursiveHemNode_leaf_facts registryDigest epochFloor msg F d c
      (verifyChildrenList_mem _ _ h.2 c hc) leaf hl

/-- **Leaf relation witness.** For shard `s` on `(epochFloor, msg)` against `registry`: one
    signature per active committee slot of `s`, each valid under `verifyPqHashSig` for the slot's
    suite, parameters and key on `shardBoundMessage s.shardId epochFloor msg` (the `valid` field
    of `ExtractedQuorumSig`), at least `s.threshold` of them, and the shard's
    `(shardId, threshold, suiteId, params, committee)` row is a row of the registry. -/
structure LeafShardQuorumWitness (epochFloor msg : List UInt8) (registry : List ShardRegistration)
    (s : HemShardProof) where
  sigs : List (ExtractedQuorumSig epochFloor msg)
  slots_eq : sigs.map (·.slot) = shardActiveSlots s
  quorum : s.threshold ≤ sigs.length
  registered : s.registration ∈ registry

/-- What a leaf witness says about each of its signatures: it verifies under the shard's own
    suite and parameters, for a key of the shard's committee, on the shard-bound message. -/
theorem LeafShardQuorumWitness.sig_valid {epochFloor msg : List UInt8}
    {registry : List ShardRegistration} {s : HemShardProof}
    (w : LeafShardQuorumWitness epochFloor msg registry s)
    (q : ExtractedQuorumSig epochFloor msg) (hq : q ∈ w.sigs) :
    q.slot.pk ∈ s.inst.committee ∧
    verifyPqHashSig s.inst.suite s.inst.params q.slot.pk
      (shardBoundMessage s.shardId epochFloor msg) q.sig = true := by
  have hSlot : q.slot ∈ shardActiveSlots s := by
    rw [← w.slots_eq]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨hId, hSuite, hParams, hPk⟩ := mem_shardActiveSlots hSlot
  refine ⟨hPk, ?_⟩
  have hv := q.valid
  rw [hId, hSuite, hParams] at hv
  exact hv

/-- **A leaf witness contains a signature by a key outside any set of fewer than `threshold`
    committee keys.** If fewer than `s.threshold` committee keys satisfy `p`, some signature of
    the witness is by a committee key that does not. -/
theorem LeafShardQuorumWitness.exists_sig_not {epochFloor msg : List UInt8}
    {registry : List ShardRegistration} {s : HemShardProof}
    (w : LeafShardQuorumWitness epochFloor msg registry s) (p : PqPublicKey → Bool)
    (hFew : (s.inst.committee.filter p).length < s.threshold) :
    ∃ q ∈ w.sigs, p q.slot.pk = false := by
  have hLen : (shardActiveSlots s).length = w.sigs.length := by
    rw [← w.slots_eq, List.length_map]
  have hLt : (s.inst.committee.filter p).length < (shardActiveSlots s).length := by
    rw [hLen]
    exact Nat.lt_of_lt_of_le hFew w.quorum
  obtain ⟨sl, hsl, hp⟩ := exists_active_slot_not s p hLt
  rw [← w.slots_eq] at hsl
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hsl
  exact ⟨q, hq, hp⟩

/-- One leaf witness per shard, in order. -/
@[expose] def LeafQuorumWitnesses (epochFloor msg : List UInt8) (registry : List ShardRegistration) :
    List HemShardProof → Type
  | [] => PUnit
  | s :: rest =>
    LeafShardQuorumWitness epochFloor msg registry s ×
      LeafQuorumWitnesses epochFloor msg registry rest

theorem LeafQuorumWitnesses.nonempty_of_mem {epochFloor msg : List UInt8}
    {registry : List ShardRegistration} :
    ∀ (shards : List HemShardProof) (_ : LeafQuorumWitnesses epochFloor msg registry shards)
      (s : HemShardProof), s ∈ shards →
      Nonempty (LeafShardQuorumWitness epochFloor msg registry s)
  | [], _, _, h => by cases h
  | t :: rest, ws, s, h => by
    have ws' : LeafShardQuorumWitness epochFloor msg registry t ×
        LeafQuorumWitnesses epochFloor msg registry rest := ws
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨ws'.1⟩
    · exact LeafQuorumWitnesses.nonempty_of_mem rest ws'.2 s h'

/-- Extracted quorum of the whole tree: the leaf shards realise exactly the registry, and every
    leaf shard has its `LeafShardQuorumWitness`. -/
structure RecursiveHemQuorumWitness (epochFloor msg : List UInt8)
    (registry : List ShardRegistration) (shards : List HemShardProof) where
  registry_eq : shards.map HemShardProof.registration = registry
  leaves : LeafQuorumWitnesses epochFloor msg registry shards

/-- Leaf step: the leaf relation witness of one shard, or the single-layer break of its
    succinct aggregate (`HemShardBreak`: a sumcheck Schwartz–Zippel hit, a Merkle hash collision,
    a WHIR stage query miss, or a WHIR proximity hit). -/
def extractLeafQuorum (arith : RowArithmetization) (dom : WhirDomain)
    (epochFloor msg : List UInt8) (registry : List ShardRegistration)
    (e : HemShardEnv arith dom) (hReg : e.shard.registration ∈ registry)
    (h : verifyHemShard arith dom epochFloor msg e.shard = true) :
    PSum (LeafShardQuorumWitness epochFloor msg registry e.shard)
      (HemShardBreak arith dom e.shard.proof e.view) :=
  match extractShardQuorum arith dom epochFloor msg e h with
  | .inl ⟨sigs, hSlots, hLen⟩ =>
    .inl ⟨sigs, hSlots, by rw [hLen]; exact (verifyHemShard_facts h).2.2.2.1, hReg⟩
  | .inr brk => .inr brk

/-- Leaf-by-leaf walk: every shard's leaf witness, or the first shard index with a break. -/
def extractLeafQuorums (arith : RowArithmetization) (dom : WhirDomain)
    (epochFloor msg : List UInt8) (registry : List ShardRegistration) :
    (envs : List (HemShardEnv arith dom)) →
    (∀ e ∈ envs, e.shard.registration ∈ registry) →
    (∀ e ∈ envs, verifyHemShard arith dom epochFloor msg e.shard = true) →
    PSum (LeafQuorumWitnesses epochFloor msg registry (envs.map (·.shard)))
      (Σ j : Fin envs.length,
        HemShardBreak arith dom (envs.get j).shard.proof (envs.get j).view)
  | [], _, _ => .inl PUnit.unit
  | e :: es, hR, hV =>
    match extractLeafQuorum arith dom epochFloor msg registry e
        (hR e (List.mem_cons_self ..)) (hV e (List.mem_cons_self ..)) with
    | .inr brk => .inr ⟨⟨0, Nat.succ_pos _⟩, brk⟩
    | .inl w =>
      match extractLeafQuorums arith dom epochFloor msg registry es
          (fun e' he' => hR e' (List.mem_cons_of_mem _ he'))
          (fun e' he' => hV e' (List.mem_cons_of_mem _ he')) with
      | .inr ⟨⟨j, hj⟩, brk⟩ => .inr ⟨⟨j + 1, Nat.succ_lt_succ hj⟩, brk⟩
      | .inl ws => .inl (w, ws)

/-- **Recursive tree knowledge extractor (`extractRecursiveHemTree`).** From an accepting
    `verifyRecursiveHemTree` against the committed registry (`H (encodeRegistry registry) =
    registryDigest`) and the committed tables `envs` of the leaf shards, returns the
    `RecursiveHemQuorumWitness` (real signatures of a quorum of every registered committee on its
    shard-bound message), or a `HemHierarchyBreak`: a collision of `H` on the registry encoding,
    or a leaf index with a `HemShardBreak`. -/
def extractRecursiveHemTree (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (F d : Nat) (agg : RecursiveHemAggregate d)
    (envs : List (HemShardEnv arith dom))
    (hEnvs : envs.map (·.shard) = recursiveHemLeafShards d agg)
    (hAcc : verifyRecursiveHemTree H arith dom registryDigest epochFloor msg F d agg = true) :
    PSum (RecursiveHemQuorumWitness epochFloor msg registry (envs.map (·.shard)))
      (HemHierarchyBreak H arith dom envs) :=
  have hHier : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (envs.map (·.shard)) = true := by
    rw [hEnvs]
    exact (verifyRecursiveHemTree_facts hAcc).2
  have hF := verifyHierarchicalHem_facts hHier
  if hEq : (envs.map (·.shard)).map HemShardProof.registration = registry then
    match extractLeafQuorums arith dom epochFloor msg registry envs
        (fun e he => by
          rw [← hEq]
          exact List.mem_map.mpr ⟨e.shard, List.mem_map.mpr ⟨e, he, rfl⟩, rfl⟩)
        (fun e he => hF.2.2.2 e.shard (List.mem_map.mpr ⟨e, he, rfl⟩)) with
    | .inl ws => .inl ⟨hEq, ws⟩
    | .inr brk => .inr (.inr brk)
  else
    .inr (.inl (registryCollision H hF.1 hReg hEq))

private theorem filter_const_false {α : Type} :
    ∀ l : List α, l.filter (fun _ => false) = []
  | [] => rfl
  | _ :: l => filter_const_false l

/-- **Recursive soundness: an accepted false statement yields a forged quorum signature or a
    break (`recursive_hem_false_statement_yields_forgery_or_break`).**
    `signed pk m` is the signing log: key `pk` produced a signature on `m`. The statement certified
    by the tree is false when some leaf shard has fewer than `threshold` committee keys that
    signed its shard-bound message. If the tree is nevertheless accepted against the committed
    registry, then either there is a forgery — a registered shard, a key of its committee that
    never signed the shard-bound message, and a signature that `verifyPqHashSig` accepts for that
    key on that message under the shard's suite (whose `suiteId` is the registered one) and
    parameters — or a `HemHierarchyBreak` (registry hash collision, or a leaf index with a
    sumcheck Schwartz–Zippel hit, Merkle collision, WHIR query miss or WHIR proximity hit). -/
theorem recursive_hem_false_statement_yields_forgery_or_break
    (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (F d : Nat) (agg : RecursiveHemAggregate d)
    (envs : List (HemShardEnv arith dom))
    (hEnvs : envs.map (·.shard) = recursiveHemLeafShards d agg)
    (hAcc : verifyRecursiveHemTree H arith dom registryDigest epochFloor msg F d agg = true)
    (signed : PqPublicKey → List UInt8 → Bool)
    (hFalse : ∃ s ∈ recursiveHemLeafShards d agg,
      (s.inst.committee.filter
        (fun pk => signed pk (shardBoundMessage s.shardId epochFloor msg))).length < s.threshold) :
    (∃ (s : HemShardProof) (pk : PqPublicKey) (sig : PqHashSig),
      s ∈ recursiveHemLeafShards d agg ∧
      s.registration ∈ registry ∧
      pk ∈ s.inst.committee ∧
      signed pk (shardBoundMessage s.shardId epochFloor msg) = false ∧
      verifyPqHashSig s.inst.suite s.inst.params pk
        (shardBoundMessage s.shardId epochFloor msg) sig = true) ∨
    Nonempty (HemHierarchyBreak H arith dom envs) := by
  match extractRecursiveHemTree H arith dom registryDigest epochFloor msg registry hReg F d agg
      envs hEnvs hAcc with
  | .inr brk => exact .inr ⟨brk⟩
  | .inl w =>
    obtain ⟨s, hs, hFew⟩ := hFalse
    have hs' : s ∈ envs.map (·.shard) := by rw [hEnvs]; exact hs
    obtain ⟨lw⟩ := LeafQuorumWitnesses.nonempty_of_mem _ w.leaves s hs'
    obtain ⟨q, hq, hNot⟩ := lw.exists_sig_not
      (fun pk => signed pk (shardBoundMessage s.shardId epochFloor msg)) hFew
    obtain ⟨hPk, hValid⟩ := lw.sig_valid q hq
    exact .inl ⟨s, q.slot.pk, q.sig, hs, lw.registered, hPk, hNot, hValid⟩

/-- A leaf shard none of whose committee keys has ANY signature accepted by `verifyPqHashSig` on
    the shard-bound message cannot sit in an accepted tree, short of a break. -/
theorem recursive_hem_leaf_without_valid_signature_yields_break
    (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (F d : Nat) (agg : RecursiveHemAggregate d)
    (envs : List (HemShardEnv arith dom))
    (hEnvs : envs.map (·.shard) = recursiveHemLeafShards d agg)
    (hAcc : verifyRecursiveHemTree H arith dom registryDigest epochFloor msg F d agg = true)
    (hNoSig : ∃ s ∈ recursiveHemLeafShards d agg, ∀ pk ∈ s.inst.committee, ∀ sig : PqHashSig,
      verifyPqHashSig s.inst.suite s.inst.params pk
        (shardBoundMessage s.shardId epochFloor msg) sig = false) :
    Nonempty (HemHierarchyBreak H arith dom envs) := by
  match extractRecursiveHemTree H arith dom registryDigest epochFloor msg registry hReg F d agg
      envs hEnvs hAcc with
  | .inr brk => exact ⟨brk⟩
  | .inl w =>
    obtain ⟨s, hs, hNo⟩ := hNoSig
    have hs' : s ∈ envs.map (·.shard) := by rw [hEnvs]; exact hs
    obtain ⟨lw⟩ := LeafQuorumWitnesses.nonempty_of_mem _ w.leaves s hs'
    have hThr : 1 ≤ s.threshold :=
      (verifyHemShard_facts ((verifyHierarchicalHem_facts
        (verifyRecursiveHemTree_facts hAcc).2).2.2.2 s hs)).2.1
    have hFew : (s.inst.committee.filter (fun _ => false)).length < s.threshold := by
      rw [filter_const_false]
      exact hThr
    obtain ⟨q, hq, _⟩ := lw.exists_sig_not (fun _ => false) hFew
    obtain ⟨hPk, hValid⟩ := lw.sig_valid q hq
    rw [hNo q.slot.pk hPk q.sig] at hValid
    exact absurd hValid Bool.false_ne_true

/-- **Finite-coin union bound of the recursive tree.** `treeBad` marks coins where the tree is
    accepted against the authenticated registry although no `RecursiveHemQuorumWitness` exists;
    `rootBad` marks every coin whose run yields a `HashCollisionWitness H`; `shardBad j` marks
    every coin whose run has a `HemShardBreak` at leaf `j`. With at most `m` leaves,
    `#treeBad ≤ #rootBad + Σ_{j < m} #shardBad j`. Inner nodes contribute no term: the verifier
    checks every leaf itself. -/
theorem recursive_hem_tree_soundness_bound {Ω : Type} (coins : List Ω) (m : Nat)
    (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : Ω → List UInt8)
    (registry : Ω → List ShardRegistration)
    (F d : Nat) (agg : Ω → RecursiveHemAggregate d)
    (envs : Ω → List (HemShardEnv arith dom))
    (hEnvs : ∀ ω, (envs ω).map (·.shard) = recursiveHemLeafShards d (agg ω))
    (hLen : ∀ ω, (envs ω).length ≤ m)
    (treeBad rootBad : Ω → Bool) (shardBad : Nat → Ω → Bool)
    (hTree : ∀ ω, treeBad ω = true →
      verifyRecursiveHemTree H arith dom (registryDigest ω) (epochFloor ω) (msg ω) F d (agg ω)
        = true ∧
      (RecursiveHemQuorumWitness (epochFloor ω) (msg ω) (registry ω)
        ((envs ω).map (·.shard)) → False))
    (hRegAuth : ∀ ω, treeBad ω = true → H (encodeRegistry (registry ω)) = registryDigest ω)
    (hRoot : ∀ ω, HashCollisionWitness H → rootBad ω = true)
    (hShard : ∀ ω (j : Fin (envs ω).length),
      HemShardBreak arith dom ((envs ω).get j).shard.proof ((envs ω).get j).view →
      shardBad j.val ω = true) :
    countTrue treeBad coins ≤
      countTrue rootBad coins + sumOver m (fun j => countTrue (shardBad j) coins) := by
  apply countTrue_union_bound
  intro ω hb
  obtain ⟨hAcc, hNo⟩ := hTree ω hb
  match extractRecursiveHemTree H arith dom (registryDigest ω) (epochFloor ω) (msg ω) (registry ω)
      (hRegAuth ω hb) F d (agg ω) (envs ω) (hEnvs ω) hAcc with
  | .inl w => exact (hNo w).elim
  | .inr (.inl col) => exact .inl (hRoot ω col)
  | .inr (.inr ⟨j, brk⟩) =>
    exact .inr ⟨j.val, Nat.lt_of_lt_of_le j.isLt (hLen ω), hShard ω j brk⟩

/-- A leaf whose header reports `validCount < threshold` is rejected, whatever its shard
    certificate and child proof. -/
theorem tooth_sub_quorum_leaf_shard_rejected_by_recursive_tree
    (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8)
    (hdr : RecursiveShardHeader) (s : HemShardProof) (prf : ChildWhirWitness)
    (hSub : hdr.validCount < hdr.threshold) :
    verifyRecursiveHemTree H arith dom registryDigest epochFloor msg 16 0
      ({ header := hdr, shard := s, leafProof := prf } : RecursiveHemLeafCert) = false := by
  have hFalse : decide (hdr.threshold ≤ hdr.validCount) = false :=
    decide_eq_false (Nat.not_le_of_lt hSub)
  have hHdr : verifyRecursiveShardHeader hdr = false := by
    unfold verifyRecursiveShardHeader
    rw [hFalse, Bool.and_false, Bool.false_and]
  unfold verifyRecursiveHemTree
  rw [verifyRecursiveHemNode_zero]
  dsimp only
  rw [hHdr]
  rfl

/-- A leaf whose shard certificate fails `verifyHemShard` is rejected, whatever its header and
    however valid its child-WHIR proof: an accepting child proof alone carries no quorum. -/
theorem recursive_tree_rejects_leaf_with_failing_shard
    (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (F : Nat)
    (leaf : RecursiveHemLeafCert)
    (hShard : verifyHemShard arith dom epochFloor msg leaf.shard = false) :
    verifyRecursiveHemTree H arith dom registryDigest epochFloor msg F 0 leaf = false := by
  cases hAcc : verifyRecursiveHemTree H arith dom registryDigest epochFloor msg F 0 leaf with
  | false => rfl
  | true =>
    have hHier := (verifyRecursiveHemTree_facts hAcc).2
    have hMem : leaf.shard ∈ recursiveHemLeafShards 0 leaf := List.mem_singleton.mpr rfl
    have hOk := (verifyHierarchicalHem_facts hHier).2.2.2 leaf.shard hMem
    rw [hShard] at hOk
    exact absurd hOk Bool.false_ne_true

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

/-- Per-node `unitaryZeroPow` QROM compiler bound at `(nv, Q)`. -/
def hemHighCapZeroPowEps (nv Q : Nat) : RatBound :=
  powScaledFsQromCompilerBound Q 5 256 0
    (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .unitaryZeroPow nv)

set_option maxRecDepth 8192 in
/-- **Budget arithmetic at five deployment scales (`recursive_hem_all_node_budget_below_2pow128_at_deployment_scales`)**:
    `strictlyMoreThanBits 128` of the all-node budget expression `recursiveHemQromErrorBound`
    `(1 + F + ... + F^(d-1)) * ε_outer + F^d * ε_leaf`, with every `ε` the flat-schedule compiler
    bound `hemHighCapZeroPowEps`:
    1. `N = 1,500` (`d = 1, F = 16, K_shard = 94`) at `Q + 1 ≤ 2^38`;
    2. `N = 8,192` (`d = 1, F = 64, K_shard = 128`) at `Q + 1 ≤ 2^37`;
    3. `N = 16,384` (`d = 2, F = 16, K_shard = 64`) at `Q + 1 ≤ 2^36`;
    4. `N = 32,768` (`d = 2, F = 16, K_shard = 128`) at `Q + 1 ≤ 2^36`;
    5. `N = 1,048,576` (`d = 3, F = 16, K_shard = 256` at `Q + 1 ≤ 2^34`, and
       `d = 3, F = 64, K_shard = 4` at `Q + 1 ≤ 2^31`). -/
theorem recursive_hem_all_node_budget_below_2pow128_at_deployment_scales :
    (16 ^ 1 * 94 ≥ 1500 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 16 1
          (hemHighCapZeroPowEps 24 (2 ^ 38 - 1)) (hemHighCapZeroPowEps 24 (2 ^ 38 - 1)))) ∧
    (64 ^ 1 * 128 = 8192 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 64 1
          (hemHighCapZeroPowEps 26 (2 ^ 37 - 1)) (hemHighCapZeroPowEps 24 (2 ^ 37 - 1)))) ∧
    (16 ^ 2 * 64 = 16384 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 16 2
          (hemHighCapZeroPowEps 24 (2 ^ 36 - 1)) (hemHighCapZeroPowEps 24 (2 ^ 36 - 1)))) ∧
    (16 ^ 2 * 128 = 32768 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 16 2
          (hemHighCapZeroPowEps 24 (2 ^ 36 - 1)) (hemHighCapZeroPowEps 24 (2 ^ 36 - 1)))) ∧
    (16 ^ 3 * 256 = 1048576 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 16 3
          (hemHighCapZeroPowEps 24 (2 ^ 34 - 1)) (hemHighCapZeroPowEps 25 (2 ^ 34 - 1)))) ∧
    (64 ^ 3 * 4 = 1048576 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 64 3
          (hemHighCapZeroPowEps 26 (2 ^ 31 - 1)) (hemHighCapZeroPowEps 18 (2 ^ 31 - 1)))) := by
  have c1 : 16 ^ 1 * 94 ≥ 1500 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 16 1
          (hemHighCapZeroPowEps 24 (2 ^ 38 - 1)) (hemHighCapZeroPowEps 24 (2 ^ 38 - 1))) := by
    simp only [recursiveHemQromErrorBound, geomInternalNodes, hemHighCapZeroPowEps, powScaledFsQromCompilerBound, qromMerkleOnlineExtractBound, hemHighCapFiveRoundRbrBounds, hemHighCapCascadeRbrBound, hemHighCapQueryBounds, hemHighCapStageWitnesses, hemHighCapStageGeoms, hemHighCapStageGeometry, hemHighCapStageWitness, hemHighCapTableRow, hemHighCapWitnessTable, whirAffineStageSimpleNum_def, quantumGroverGrindingBound_def, quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def]
    decide +kernel
  have c2 : 64 ^ 1 * 128 = 8192 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 64 1
          (hemHighCapZeroPowEps 26 (2 ^ 37 - 1)) (hemHighCapZeroPowEps 24 (2 ^ 37 - 1))) := by
    simp only [recursiveHemQromErrorBound, geomInternalNodes, hemHighCapZeroPowEps, powScaledFsQromCompilerBound, qromMerkleOnlineExtractBound, hemHighCapFiveRoundRbrBounds, hemHighCapCascadeRbrBound, hemHighCapQueryBounds, hemHighCapStageWitnesses, hemHighCapStageGeoms, hemHighCapStageGeometry, hemHighCapStageWitness, hemHighCapTableRow, hemHighCapWitnessTable, whirAffineStageSimpleNum_def, quantumGroverGrindingBound_def, quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def]
    decide +kernel
  have c3 : 16 ^ 2 * 64 = 16384 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 16 2
          (hemHighCapZeroPowEps 24 (2 ^ 36 - 1)) (hemHighCapZeroPowEps 24 (2 ^ 36 - 1))) := by
    simp only [recursiveHemQromErrorBound, geomInternalNodes, hemHighCapZeroPowEps, powScaledFsQromCompilerBound, qromMerkleOnlineExtractBound, hemHighCapFiveRoundRbrBounds, hemHighCapCascadeRbrBound, hemHighCapQueryBounds, hemHighCapStageWitnesses, hemHighCapStageGeoms, hemHighCapStageGeometry, hemHighCapStageWitness, hemHighCapTableRow, hemHighCapWitnessTable, whirAffineStageSimpleNum_def, quantumGroverGrindingBound_def, quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def]
    decide +kernel
  have c4 : 16 ^ 2 * 128 = 32768 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 16 2
          (hemHighCapZeroPowEps 24 (2 ^ 36 - 1)) (hemHighCapZeroPowEps 24 (2 ^ 36 - 1))) := by
    simp only [recursiveHemQromErrorBound, geomInternalNodes, hemHighCapZeroPowEps, powScaledFsQromCompilerBound, qromMerkleOnlineExtractBound, hemHighCapFiveRoundRbrBounds, hemHighCapCascadeRbrBound, hemHighCapQueryBounds, hemHighCapStageWitnesses, hemHighCapStageGeoms, hemHighCapStageGeometry, hemHighCapStageWitness, hemHighCapTableRow, hemHighCapWitnessTable, whirAffineStageSimpleNum_def, quantumGroverGrindingBound_def, quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def]
    decide +kernel
  have c5 : 16 ^ 3 * 256 = 1048576 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 16 3
          (hemHighCapZeroPowEps 24 (2 ^ 34 - 1)) (hemHighCapZeroPowEps 25 (2 ^ 34 - 1))) := by
    simp only [recursiveHemQromErrorBound, geomInternalNodes, hemHighCapZeroPowEps, powScaledFsQromCompilerBound, qromMerkleOnlineExtractBound, hemHighCapFiveRoundRbrBounds, hemHighCapCascadeRbrBound, hemHighCapQueryBounds, hemHighCapStageWitnesses, hemHighCapStageGeoms, hemHighCapStageGeometry, hemHighCapStageWitness, hemHighCapTableRow, hemHighCapWitnessTable, whirAffineStageSimpleNum_def, quantumGroverGrindingBound_def, quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def]
    decide +kernel
  have c6 : 64 ^ 3 * 4 = 1048576 ∧
      strictlyMoreThanBits 128
        (recursiveHemQromErrorBound 64 3
          (hemHighCapZeroPowEps 26 (2 ^ 31 - 1)) (hemHighCapZeroPowEps 18 (2 ^ 31 - 1))) := by
    simp only [recursiveHemQromErrorBound, geomInternalNodes, hemHighCapZeroPowEps, powScaledFsQromCompilerBound, qromMerkleOnlineExtractBound, hemHighCapFiveRoundRbrBounds, hemHighCapCascadeRbrBound, hemHighCapQueryBounds, hemHighCapStageWitnesses, hemHighCapStageGeoms, hemHighCapStageGeometry, hemHighCapStageWitness, hemHighCapTableRow, hemHighCapWitnessTable, whirAffineStageSimpleNum_def, quantumGroverGrindingBound_def, quantumGroverSingleTargetBound_def, quantumZhandryMultiTargetBound_def, quantumBhtCollisionBound_def]
    decide +kernel
  exact ⟨c1, c2, c3, c4, c5, c6⟩


/-! ## §4. Honest Child Witness, Tree Acceptance Lemma & Audits -/

/-- An accepting `ChildWhirWitness` for any `(pub, salt : Lane4)` over a depth-1 `Poseidon2`
    Canopy (`bottomDepth = 1, canopyDepth = 0`, leaves `0` and `1`, all-zero codeword, no
    sumcheck round). A child-WHIR proof exists for EVERY public digest: it certifies an opening
    of a prover-chosen commitment and says nothing about the statement behind the digest. -/
def mkHonestChildWhirWitness (pub salt : Lane4) : ChildWhirWitness :=
  let zLimbs := ext4ToLimbs CommRingOps.zero
  let d0 := poseidon2CanopyLeafHash salt (Goldilocks.ofNat 0) zLimbs
  let d1 := poseidon2CanopyLeafHash salt (Goldilocks.ofNat 1) zLimbs
  let root := poseidon2CanopyNodeHash salt (Goldilocks.ofNat 0) (Goldilocks.ofNat 0) d0 d1
  let ch := childWhirChallenges pub 1 0 salt CommRingOps.zero root [] []
  { salt := salt
    canopyRoot := root
    bottomDepth := 1
    canopyDepth := 0
    initialClaim := CommRingOps.zero
    sumcheckPolys := []
    opening0 := { leafIdx := 0, payload := zLimbs, bottomPath := [d1], canopyPath := [] }
    opening1 := { leafIdx := 1, payload := zLimbs, bottomPath := [d0], canopyPath := [] }
    duetFold := {
      v0 := CommRingOps.zero, v1 := CommRingOps.zero,
      theta := ch.theta, alpha := ch.alpha, beta := ch.beta,
      x := CommRingOps.one, x_sq := CommRingOps.one,
      inv_two := ext4InvTwo, inv_two_x := ext4InvTwo,
      claimed := CommRingOps.zero
    }
    earlyStopPoly := [] }

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

theorem mkHonestChildWhirWitness_accepts (pub salt : Lane4) :
    ChildWhirCircuitAccepts pub (mkHonestChildWhirWitness pub salt) = true := by
  have hOp0 : verifyPoseidon2CanopyOpening salt
      (poseidon2CanopyNodeHash salt (Goldilocks.ofNat 0) (Goldilocks.ofNat 0)
        (poseidon2CanopyLeafHash salt (Goldilocks.ofNat 0) (ext4ToLimbs CommRingOps.zero))
        (poseidon2CanopyLeafHash salt (Goldilocks.ofNat 1) (ext4ToLimbs CommRingOps.zero)))
      1 0
      { leafIdx := 0, payload := ext4ToLimbs CommRingOps.zero,
        bottomPath := [poseidon2CanopyLeafHash salt (Goldilocks.ofNat 1) (ext4ToLimbs CommRingOps.zero)],
        canopyPath := [] } = true := by
    unfold verifyPoseidon2CanopyOpening
    dsimp only
    exact bool_and5_true
      (decide_eq_true (by decide : 1 + 0 < 32))
      (decide_eq_true (by decide : 0 < 2 ^ (1 + 0)))
      (decide_eq_true rfl) (decide_eq_true rfl) (decide_eq_true rfl)
  have hOp1 : verifyPoseidon2CanopyOpening salt
      (poseidon2CanopyNodeHash salt (Goldilocks.ofNat 0) (Goldilocks.ofNat 0)
        (poseidon2CanopyLeafHash salt (Goldilocks.ofNat 0) (ext4ToLimbs CommRingOps.zero))
        (poseidon2CanopyLeafHash salt (Goldilocks.ofNat 1) (ext4ToLimbs CommRingOps.zero)))
      1 0
      { leafIdx := 1, payload := ext4ToLimbs CommRingOps.zero,
        bottomPath := [poseidon2CanopyLeafHash salt (Goldilocks.ofNat 0) (ext4ToLimbs CommRingOps.zero)],
        canopyPath := [] } = true := by
    unfold verifyPoseidon2CanopyOpening
    dsimp only
    exact bool_and5_true
      (decide_eq_true (by decide : 1 + 0 < 32))
      (decide_eq_true (by decide : 1 < 2 ^ (1 + 0)))
      (decide_eq_true rfl) (decide_eq_true rfl) (decide_eq_true rfl)
  have hDuet : ∀ (th al be : QuarticGoldilocks),
      duetFoldAuthenticated
        { v0 := CommRingOps.zero, v1 := CommRingOps.zero,
          theta := th, alpha := al, beta := be,
          x := CommRingOps.one, x_sq := CommRingOps.one,
          inv_two := ext4InvTwo, inv_two_x := ext4InvTwo,
          claimed := CommRingOps.zero } = true := by
    intro th al be
    unfold duetFoldAuthenticated duetFoldUnauthenticatedGate
    dsimp only
    have hEven0 : CommRingOps.mul (CommRingOps.add (CommRingOps.zero : QuarticGoldilocks) CommRingOps.zero)
        ext4InvTwo = CommRingOps.zero := by
      rw [LawfulCommRing.zero_add, LawfulCommRing.zero_mul]
    have hOdd0 : CommRingOps.mul (CommRingOps.sub (CommRingOps.zero : QuarticGoldilocks) CommRingOps.zero)
        ext4InvTwo = CommRingOps.zero := by
      rw [LawfulCommRing.sub_self, LawfulCommRing.zero_mul]
    rw [hEven0, hOdd0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
        LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
        LawfulCommRing.mul_one, LawfulCommRing.mul_one]
    rw [decide_eq_true ext4Two_mul_ext4InvTwo, decide_eq_true rfl, decide_eq_true rfl]
    rfl
  refine (ChildWhirCircuitAccepts_iff pub (mkHonestChildWhirWitness pub salt)).mpr
    ⟨rfl, Nat.le_refl 1, hOp0, hOp1, (depth_one_query_index _).1, (depth_one_query_index _).2,
      rfl, rfl, rfl, rfl, rfl, hDuet _ _ _, Nat.zero_le _, RoundPoly.evalCoeffs_nil _⟩

theorem inhabited_childWhirCircuitAccepts :
    ∃ (pub : Lane4) (w : ChildWhirWitness), ChildWhirCircuitAccepts pub w = true :=
  ⟨lane4Zero, mkHonestChildWhirWitness lane4Zero lane4Zero,
   mkHonestChildWhirWitness_accepts lane4Zero lane4Zero⟩

/-- Acceptance of a depth-1, fan-in-2 tree: two leaves with canonical headers bound to their
    shards and accepting child proofs on their header digests, an accepting outer proof on the
    `Poseidon2` summary of both header digests, and the two shard certificates passing the
    two-layer root verifier. -/
theorem verifyRecursiveHemTree_depth1_pair (H : Hash) (arith : Aggregation.RowArithmetization)
    (dom : Aggregation.WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (l0 l1 : RecursiveHemLeafCert) (outer : ChildWhirWitness)
    (hH0 : verifyRecursiveShardHeader l0.header = true)
    (hH1 : verifyRecursiveShardHeader l1.header = true)
    (hB0 : leafHeaderBindsShard registryDigest epochFloor msg l0.header l0.shard = true)
    (hB1 : leafHeaderBindsShard registryDigest epochFloor msg l1.header l1.shard = true)
    (hP0 : ChildWhirCircuitAccepts (hashLeafShardHeader l0.header) l0.leafProof = true)
    (hP1 : ChildWhirCircuitAccepts (hashLeafShardHeader l1.header) l1.leafProof = true)
    (hOuter : ChildWhirCircuitAccepts
      (poseidon2SummaryHash 1 2 [hashLeafShardHeader l0.header, hashLeafShardHeader l1.header])
      outer = true)
    (hHier : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      [l0.shard, l1.shard] = true) :
    verifyRecursiveHemTree H arith dom registryDigest epochFloor msg 2 1
      ({ summaryDigest := poseidon2SummaryHash 1 2
           [hashLeafShardHeader l0.header, hashLeafShardHeader l1.header]
         outerProof := outer
         children := [l0, l1] } : RecursiveHemOuterCert (RecursiveHemAggregate 0)) = true := by
  have hLeaf0 : verifyRecursiveHemNode registryDigest epochFloor msg 2 0 l0 = true := by
    rw [verifyRecursiveHemNode_zero, hH0, hB0, hP0]
    rfl
  have hLeaf1 : verifyRecursiveHemNode registryDigest epochFloor msg 2 0 l1 = true := by
    rw [verifyRecursiveHemNode_zero, hH1, hB1, hP1]
    rfl
  have hChildren : verifyChildrenList (verifyRecursiveHemNode registryDigest epochFloor msg 2 0)
      [l0, l1] = true :=
    Bool.and_eq_true_iff.mpr ⟨hLeaf0, Bool.and_eq_true_iff.mpr ⟨hLeaf1, rfl⟩⟩
  unfold verifyRecursiveHemTree
  refine Bool.and_eq_true_iff.mpr ⟨?_, hHier⟩
  rw [verifyRecursiveHemNode_succ registryDigest epochFloor msg 2 0]
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true (by decide), decide_eq_true (by decide)⟩,
      decide_eq_true rfl⟩, decide_eq_true rfl⟩, hOuter⟩, hChildren⟩

theorem inhabited_hemHighCap_nv28_cdhz :
    ∃ (nv Q wFs wVc : Nat),
      2 ≤ nv ∧ nv ≤ 28 ∧ Q ≤ 2 ^ 38 ∧ wFs + wVc ≤ Q ∧
      nv = 28 ∧ Q = 2 ^ 38 ∧
      atLeastBits 128
        (cdhzSnargPartitionBound Q wFs wVc 426 (nv - 2) 256 16
          (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .cdhzPow16At2pow38 nv)) :=
  ⟨28, 2 ^ 38, 2 ^ 37, 2 ^ 37, by decide, by decide, Nat.le_refl _, by decide, rfl, rfl,
    (hemHighCap_cdhzPow16_budget_nv2_to_28 28 (2 ^ 38) (2 ^ 37) (2 ^ 37)
      (by decide) (by decide) (Nat.le_refl _) (by decide)).2⟩

theorem inhabited_hemHighCap_nv28_zeroPow :
    ∃ (nv Q : Nat),
      2 ≤ nv ∧ nv ≤ 28 ∧ Q + 1 ≤ 2 ^ 40 ∧ nv = 28 ∧ Q = 2 ^ 40 - 1 ∧
      atLeastBits 128
        (powScaledFsQromCompilerBound Q 5 256 0
          (hemHighCapFiveRoundRbrBounds nv) (hemHighCapQueryBounds .unitaryZeroPow nv)) :=
  ⟨28, 2 ^ 40 - 1, by decide, by decide, by decide, rfl, rfl,
    (hemHighCap_unitaryZeroPow_budget_nv2_to_28 28 (2 ^ 40 - 1) (by decide) (by decide) (by decide)).2⟩

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

#verify_constructive
  Qsag.hemHighCapStageGeometry_eq_hemStageGeometry
  Qsag.hemHighCapSchedule_covers_nv2_to_28
  Qsag.highCap_stage_decomp_bound
  Qsag.hemHighCap_cdhzPow16_budget_nv2_to_28
  Qsag.hemHighCap_unitaryZeroPow_budget_nv2_to_28
  Qsag.tooth_highCap_nv28_underqueried_schedule_fails_qrom
  Qsag.canopyLeafPreimage_injective
  Qsag.canopyNodePreimage_injective
  Qsag.canopyLeaf_ne_node_preimage
  Qsag.canopyOpening_payload_unique_of_collision_free
  Qsag.tooth_unsalted_poseidon2_canopy_collision
  Qsag.tooth_missing_domain_tag_leaf_node_confusion
  Qsag.authenticated_duet_fold_uniquely_determines_claimed
  Qsag.tooth_unverified_inv_two_x_forges_duet_fold
  Qsag.tooth_unverified_inv_two_x_concrete_rejected
  Qsag.fsTranscriptBlocks_injective
  Qsag.childWhirTranscript_challenge
  Qsag.leafShardHeaderPreimage_injective
  Qsag.canopySummaryPreimage_injective
  Qsag.verifyRecursiveHemNode_inner_facts
  Qsag.verifyRecursiveHemNode_rejects_noncanonical_depth
  Qsag.verifyRecursiveHemNode_rejects_noncanonical_fanIn
  Qsag.leafShardStatementPreimage_injective
  Qsag.mkHonestChildWhirWitness_accepts
  Qsag.inhabited_childWhirCircuitAccepts
  Qsag.recursiveHemQromErrorBound_step
  Qsag.recursive_hem_false_statement_yields_forgery_or_break
  Qsag.recursive_hem_leaf_without_valid_signature_yields_break
  Qsag.recursive_hem_tree_soundness_bound
  Qsag.recursive_hem_all_node_budget_below_2pow128_at_deployment_scales
  Qsag.tooth_sub_quorum_leaf_shard_rejected_by_recursive_tree
  Qsag.recursive_tree_rejects_leaf_with_failing_shard
  Qsag.verifyRecursiveHemTree_depth1_pair

#tooth_pair Qsag.hemHighCap_unitaryZeroPow_budget_nv2_to_28 vs Qsag.tooth_highCap_nv28_underqueried_schedule_fails_qrom
#tooth_pair Qsag.canopyOpening_payload_unique_of_collision_free vs Qsag.tooth_unsalted_poseidon2_canopy_collision
#tooth_pair Qsag.canopyLeaf_ne_node_preimage vs Qsag.tooth_missing_domain_tag_leaf_node_confusion
#tooth_pair Qsag.authenticated_duet_fold_uniquely_determines_claimed vs Qsag.tooth_unverified_inv_two_x_forges_duet_fold
#tooth_pair Qsag.verifyRecursiveHemTree_depth1_pair vs Qsag.tooth_sub_quorum_leaf_shard_rejected_by_recursive_tree

#verify_inhabited Qsag.hemHighCap_cdhzPow16_budget_nv2_to_28 Qsag.inhabited_hemHighCap_nv28_cdhz
#verify_inhabited Qsag.hemHighCap_unitaryZeroPow_budget_nv2_to_28 Qsag.inhabited_hemHighCap_nv28_zeroPow

end Qsag
end
