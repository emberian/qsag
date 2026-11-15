module
/-
# Classical Merkle Query-Table Extraction and Conditional QROM Target-Hit Bounds

Constructive classical extraction for tweaked Merkle paths (`merkleRootFromPath`) and
Steiner-deduplicated `CanopyMultiProof` commitments (`verifyCanopyMultiproof` from `pcs.rs`),
followed by a conditional quantum target-hit bound. These are separate interfaces: this module
does not construct a classical query table from a coherent quantum adversary, bound the
disturbance of extracting such a table, or instantiate the quantum covering/locality premises
from the classical classifier.

1. **Pre-Challenge Online Query-Table Extraction (`extractOnlineMerkleOpening`,
   `classifyOnlineMerkleOpening`, `onlineMerkle_preChallenge_unique`)**:
   Given ONLY a committed root `rt` and a classical table `queries` of `Q` recorded compression
   queries, `extractOnlineMerkleOpening` deterministically reconstructs `(leaf, path)` BEFORE any
   challenge index is squeezed. Any post-challenge accepted opening `(leaf, path)` constructively
   lands in `OnlineMerkleOutcome` (`Type`-valued):
   - `.extractedEq`: `(leaf, path)` equals the unique pre-challenge extracted opening;
   - `.queryCollision`: an explicit `MerkleTweakCollision H`;
   - `.unqueriedRootPreimage`: an unqueried input hashing directly to `rt` (`1` target); or
   - `.unqueriedChildPreimage`: an unqueried input hashing into `merkleChildTargets queries`
     (`2 * Q` targets).

2. **Steiner-Deduplicated `CanopyMultiProof` Online Extraction (`extractOnlineCanopyOpening`,
   `classifyOnlineCanopyOpening`, `onlineCanopy_preChallenge_unique`)**:
   Extends the constructive `Type`-valued online query-table dichotomy to `verifyCanopyMultiproof`
   (`pcs.rs`), splitting any accepted multi-opening into unique pre-challenge extraction,
   `CanopyRootCollision`, `CanopyNodeCollision`, unqueried root preimage (`1` target), or unqueried
   internal node preimage (`≤ 2 * Q + 1` targets).

3. **Unitary `QVec` / `GaussInt` Conditional Target-Hit Bound (`qrom_unitary_target_hit_bound`,
   `qrom_unitary_single_root_merkle_extract_bound`,
   `qrom_unitary_multiRoot_merkle_extract_bound`)**:
   Bounds an event supplied by the caller, assuming it is covered by hits on small target
   lists invariant under reprogramming the tested coordinate. Via `QromRbrRound` and
   `qrom_uniform_oracle_success_bound`, the result is dominated by
   `qromMerkleOnlineExtractBound numRoots w Q`:
   hitting `1` root target costs `≤ (2Q + 1)^2 / 2^w ≤ quantumGroverSingleTargetBound w Q`, and
   hitting `≤ 2Q + 1` query-child / collision targets costs
   `≤ (2Q + 1)^3 / 2^w ≤ 8(Q + 1)^3 / 2^w = quantumBhtCollisionBound w Q`.
   Instantiating those lists from adaptive quantum commitments, including collisions and
   post-challenge openings, remains a separate reduction obligation. The inhabitedness
   witness below is a zero-query singleton-target search event, not a Merkle execution.
-/

public import Qsag.Oracle.MultiRoundFsQrom
import all Qsag.Oracle.MultiRoundFsQrom
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
import all Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Pre-Challenge Online Extraction for Position-Tweaked `merkleRootFromPath` -/

/-- Constructive first-match lookup avoiding opaque library lemma dependencies. -/
def findFirst {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x = true then some x else findFirst p xs

theorem findFirst_some_spec {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {x : α}, findFirst p xs = some x → x ∈ xs ∧ p x = true
  | [], _, h => by cases h
  | y :: ys, x, h => by
    unfold findFirst at h
    cases hp : p y
    · rw [hp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases findFirst_some_spec p h with ⟨hm, hpx⟩
      exact ⟨.tail y hm, hpx⟩
    · rw [hp] at h; simp only [↓reduceIte, Option.some.injEq] at h
      subst h; exact ⟨.head ys, hp⟩

theorem findFirst_none_spec {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, findFirst p xs = none → ∀ x ∈ xs, p x = false
  | [], _, _, hx => nomatch hx
  | y :: ys, h, x, hx => by
    unfold findFirst at h
    cases hp : p y
    · rw [hp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases List.mem_cons.mp hx with rfl | htl
      · exact hp
      · exact findFirst_none_spec p h x htl
    · rw [hp] at h; simp only [↓reduceIte] at h; cases h

/-- One recorded compression query `(lvl, node, left, right) ↦ out` in a classical
    pre-challenge query table. Coherent QROM access does not itself provide such a record. -/
structure RecordedMerkleQuery (D : Type) where
  lvl : Nat
  node : Nat
  left : D
  right : D
  out : D
  deriving DecidableEq, Repr

/-- Consistency of a recorded query entry with compression oracle `H`. -/
@[expose] def merkleQueryConsistent {D : Type} (H : Nat → Nat → D → D → D)
    (q : RecordedMerkleQuery D) : Prop :=
  H q.lvl q.node q.left q.right = q.out

/-- Child digests `{q.left, q.right | q ∈ queries}` appearing in a recorded `Q`-query table. -/
def merkleChildTargets {D : Type} : List (RecordedMerkleQuery D) → List D
  | [] => []
  | q :: qs => q.left :: q.right :: merkleChildTargets qs

/-- Full pre-challenge target set `rt :: merkleChildTargets queries` (length `2 * Q + 1`). -/
def merklePreChallengeTargets {D : Type} (rt : D) (queries : List (RecordedMerkleQuery D)) :
    List D :=
  rt :: merkleChildTargets queries

theorem merkleChildTargets_length {D : Type} :
    ∀ (qs : List (RecordedMerkleQuery D)), (merkleChildTargets qs).length = 2 * qs.length
  | [] => rfl
  | _ :: qs => by
    simp only [merkleChildTargets, List.length_cons, merkleChildTargets_length qs]; omega

theorem merklePreChallengeTargets_length {D : Type} (rt : D)
    (qs : List (RecordedMerkleQuery D)) :
    (merklePreChallengeTargets rt qs).length = 2 * qs.length + 1 := by
  simp only [merklePreChallengeTargets, List.length_cons, merkleChildTargets_length]

private theorem mem_merkleChildTargets_of_mem {D : Type}
    {q : RecordedMerkleQuery D} {qs : List (RecordedMerkleQuery D)} (hq : q ∈ qs) :
    q.left ∈ merkleChildTargets qs ∧ q.right ∈ merkleChildTargets qs := by
  induction qs with
  | nil => nomatch hq
  | cons hd tl ih =>
    rcases List.mem_cons.mp hq with rfl | htl
    · exact ⟨.head _, .tail _ (.head _)⟩
    · rcases ih htl with ⟨hl, hr⟩
      exact ⟨.tail _ (.tail _ hl), .tail _ (.tail _ hr)⟩

/-- **Pre-challenge online opening extractor** for `merkleRootFromPath`: reconstructs `(leaf, path)`
    solely from `(rt, queries)` and `(lvl, depth, idx)` BEFORE any challenge is squeezed. -/
@[expose] def extractOnlineMerkleOpening {D : Type} [DecidableEq D]
    (rt : D) (queries : List (RecordedMerkleQuery D)) :
    Nat → Nat → Nat → Option (D × List D)
  | _, 0, _ => some (rt, [])
  | lvl, depth + 1, idx =>
    match extractOnlineMerkleOpening rt queries (lvl + 1) depth (idx / 2) with
    | none => none
    | some (parent, restPath) =>
      match findFirst (fun q =>
          decide (q.lvl = lvl) && decide (q.node = idx / 2) && decide (q.out = parent)) queries with
      | none => none
      | some q =>
        if idx % 2 = 0 then some (q.left, q.right :: restPath)
        else some (q.right, q.left :: restPath)

private theorem extractOnlineMerkleOpening_succ_child {D : Type} [DecidableEq D]
    (rt : D) (queries : List (RecordedMerkleQuery D))
    (lvl depth idx : Nat) (val : D) (pth : List D)
    (h : extractOnlineMerkleOpening rt queries lvl (depth + 1) idx = some (val, pth)) :
    val ∈ merkleChildTargets queries := by
  unfold extractOnlineMerkleOpening at h
  cases hUp : extractOnlineMerkleOpening rt queries (lvl + 1) depth (idx / 2) with
  | none => rw [hUp] at h; cases h
  | some pr =>
    rw [hUp] at h; dsimp only at h
    cases hFind : findFirst (fun q =>
        decide (q.lvl = lvl) && decide (q.node = idx / 2) && decide (q.out = pr.1)) queries with
    | none => rw [hFind] at h; cases h
    | some q =>
      rw [hFind] at h; dsimp only at h
      rcases mem_merkleChildTargets_of_mem (findFirst_some_spec _ hFind).1 with ⟨hL, hR⟩
      by_cases hPar : idx % 2 = 0
      · simp only [hPar, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact hL
      · simp only [hPar, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact hR

/-- `Type`-valued 4-way constructive online-extraction outcome for `merkleRootFromPath`. -/
inductive OnlineMerkleOutcome {D : Type} [DecidableEq D]
    (H : Nat → Nat → D → D → D) (rt : D) (queries : List (RecordedMerkleQuery D))
    (lvl depth idx : Nat) (leaf : D) (path : List D) : Type where
  | extractedEq
      (hExt : extractOnlineMerkleOpening rt queries lvl depth idx = some (leaf, path))
  | queryCollision
      (lvlC nodeC : Nat) (a b a' b' : D)
      (hNe : (a, b) ≠ (a', b'))
      (hEq : H lvlC nodeC a b = H lvlC nodeC a' b')
  | unqueriedRootPreimage
      (lvlU nodeU : Nat) (lU rU : D)
      (hOut : H lvlU nodeU lU rU = rt)
      (hUnq : ∀ q ∈ queries, ¬(q.lvl = lvlU ∧ q.node = nodeU ∧ q.left = lU ∧ q.right = rU))
  | unqueriedChildPreimage
      (lvlU nodeU : Nat) (lU rU outU : D)
      (hOut : H lvlU nodeU lU rU = outU)
      (hMem : outU ∈ merkleChildTargets queries)
      (hUnq : ∀ q ∈ queries, ¬(q.lvl = lvlU ∧ q.node = nodeU ∧ q.left = lU ∧ q.right = rU))

/-- Every `.queryCollision` branch immediately witnesses `MerkleTweakCollision H`. -/
theorem onlineMerkleOutcome_collision_sound {D : Type} [DecidableEq D]
    {H : Nat → Nat → D → D → D} {lvlC nodeC : Nat} {a b a' b' : D}
    (hNe : (a, b) ≠ (a', b')) (hEq : H lvlC nodeC a b = H lvlC nodeC a' b') :
    MerkleTweakCollision H :=
  ⟨lvlC, nodeC, a, b, a', b',
    if ha : a = a' then .inr (fun hb => hNe (Prod.ext ha hb)) else .inl ha, hEq⟩

/-- **Constructive `Type`-valued online Merkle query-table classifier** (`0 Classical.choice`). -/
def classifyOnlineMerkleOpening {D : Type} [DecidableEq D]
    (H : Nat → Nat → D → D → D) (rt : D) (queries : List (RecordedMerkleQuery D))
    (hCons : ∀ q ∈ queries, merkleQueryConsistent H q) :
    (lvl idx : Nat) → (leaf : D) → (path : List D) →
      merkleRootFromPath H lvl idx leaf path = rt →
      OnlineMerkleOutcome H rt queries lvl path.length idx leaf path
  | lvl, idx, leaf, [], hRoot =>
    .extractedEq (by have hEq : leaf = rt := hRoot; subst hEq; rfl)
  | lvl, idx, leaf, sib :: rest, hRoot => by
    let lCh := if idx % 2 = 0 then leaf else sib
    let rCh := if idx % 2 = 0 then sib else leaf
    let parent := H lvl (idx / 2) lCh rCh
    have hStepEq : (if idx % 2 = 0 then H lvl (idx / 2) leaf sib else H lvl (idx / 2) sib leaf) =
        parent := by
      dsimp only [parent, lCh, rCh]; by_cases hp : idx % 2 = 0 <;> simp [hp]
    have hRestRoot : merkleRootFromPath H (lvl + 1) (idx / 2) parent rest = rt := by
      unfold merkleRootFromPath at hRoot; rwa [hStepEq] at hRoot
    match classifyOnlineMerkleOpening H rt queries hCons (lvl + 1) (idx / 2) parent rest hRestRoot with
    | .queryCollision lc nc a b a' b' hNe hEq =>
      exact .queryCollision lc nc a b a' b' hNe hEq
    | .unqueriedRootPreimage lu nu lU rU hOut hUnq =>
      exact .unqueriedRootPreimage lu nu lU rU hOut hUnq
    | .unqueriedChildPreimage lu nu lU rU outU hOut hMem hUnq =>
      exact .unqueriedChildPreimage lu nu lU rU outU hOut hMem hUnq
    | .extractedEq hExtUp =>
      let pred := fun q : RecordedMerkleQuery D =>
        decide (q.lvl = lvl) && decide (q.node = idx / 2) && decide (q.out = parent)
      match hFind : findFirst pred queries with
      | none =>
        have hUnq : ∀ q ∈ queries, ¬(q.lvl = lvl ∧ q.node = idx / 2 ∧ q.left = lCh ∧ q.right = rCh) := by
          intro q hq ⟨hL, hN, hLc, hRc⟩
          have hFalse := findFirst_none_spec pred hFind q hq
          have hOutEq : q.out = parent := by
            have hc := hCons q hq; unfold merkleQueryConsistent at hc
            rw [← hc, hL, hN, hLc, hRc]
          dsimp only [pred] at hFalse
          simp only [hL, hN, hOutEq, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
        match rest, hExtUp with
        | [], hUp0 =>
          have hParRt : parent = rt := by
            simp only [List.length_nil, extractOnlineMerkleOpening,
              Option.some.injEq, Prod.mk.injEq] at hUp0
            exact hUp0.1.symm
          exact .unqueriedRootPreimage lvl (idx / 2) lCh rCh hParRt hUnq
        | _ :: tlRest, hUpS =>
          exact .unqueriedChildPreimage lvl (idx / 2) lCh rCh parent rfl
            (extractOnlineMerkleOpening_succ_child rt queries (lvl + 1) tlRest.length
              (idx / 2) parent _ hUpS) hUnq
      | some q =>
        rcases findFirst_some_spec pred hFind with ⟨hqMem, hqPred⟩
        dsimp only [pred] at hqPred
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hqPred
        rcases hqPred with ⟨⟨hqLvl, hqNode⟩, hqOut⟩
        if hPairEq : (q.left, q.right) = (lCh, rCh) then
          exact .extractedEq (by
            have hqL : q.left = lCh := (Prod.mk.inj hPairEq).1
            have hqR : q.right = rCh := (Prod.mk.inj hPairEq).2
            show extractOnlineMerkleOpening rt queries lvl (rest.length + 1) idx =
              some (leaf, sib :: rest)
            unfold extractOnlineMerkleOpening
            rw [hExtUp]; dsimp only; rw [hFind]; dsimp only
            by_cases hp : idx % 2 = 0 <;>
              (dsimp only [lCh, rCh] at hqL hqR; simp only [hp, ↓reduceIte] at hqL hqR ⊢; rw [hqL, hqR]))
        else
          have hColl : H lvl (idx / 2) q.left q.right = H lvl (idx / 2) lCh rCh := by
            have hc := hCons q hqMem; unfold merkleQueryConsistent at hc
            rw [← hqLvl, ← hqNode, hc, hqOut]; dsimp only [parent]; rw [hqLvl, hqNode]
          exact .queryCollision lvl (idx / 2) q.left q.right lCh rCh hPairEq hColl

/-- **Pre-challenge binding of online extraction**: any two openings `(leaf₁, path₁)` and
    `(leaf₂, path₂)` at `(lvl, depth, idx)` landing in `.extractedEq` coincide identically. -/
theorem onlineMerkle_preChallenge_unique {D : Type} [DecidableEq D]
    (rt : D) (queries : List (RecordedMerkleQuery D))
    (lvl depth idx : Nat) (leaf₁ leaf₂ : D) (path₁ path₂ : List D)
    (h₁ : extractOnlineMerkleOpening rt queries lvl depth idx = some (leaf₁, path₁))
    (h₂ : extractOnlineMerkleOpening rt queries lvl depth idx = some (leaf₂, path₂)) :
    leaf₁ = leaf₂ ∧ path₁ = path₂ :=
  Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))

/-- `#tooth` witness: with an empty pre-challenge query table (`queries = []`), a depth-1 opening
    cannot be online-extracted (`extractOnlineMerkleOpening = none`). -/
theorem tooth_onlineMerkle_empty_queries_unqueried_root :
    ¬ ∃ lp : Nat × List Nat,
      extractOnlineMerkleOpening 10 ([] : List (RecordedMerkleQuery Nat)) 0 1 0 = some lp := by
  rintro ⟨_, h⟩
  unfold extractOnlineMerkleOpening findFirst at h
  cases h

#tooth_pair Qsag.onlineMerkle_preChallenge_unique vs
  Qsag.tooth_onlineMerkle_empty_queries_unqueried_root


/-! ## §2. Pre-Challenge Online Extraction for `verifyCanopyMultiproof` (`pcs.rs`) -/

/-- Recorded `rootHash(logLeaves, top) ↦ out` query for `CanopyMultiProof`. -/
structure RecordedCanopyRootQuery (D : Type) where
  logLeaves : Nat
  top : D
  out : D
  deriving DecidableEq, Repr

/-- Recorded `nodeHash(idx, left, right) ↦ out` query for `CanopyMultiProof`. -/
structure RecordedCanopyNodeQuery (D : Type) where
  idx : Nat
  left : D
  right : D
  out : D
  deriving DecidableEq, Repr

def canopyNodeChildTargets {D : Type} : List (RecordedCanopyNodeQuery D) → List D
  | [] => []
  | q :: qs => q.left :: q.right :: canopyNodeChildTargets qs

theorem canopyNodeChildTargets_length {D : Type} :
    ∀ (qs : List (RecordedCanopyNodeQuery D)), (canopyNodeChildTargets qs).length = 2 * qs.length
  | [] => rfl
  | _ :: qs => by
    simp only [canopyNodeChildTargets, List.length_cons, canopyNodeChildTargets_length qs]; omega

private theorem mem_canopyNodeChildTargets_of_mem {D : Type}
    {q : RecordedCanopyNodeQuery D} {qs : List (RecordedCanopyNodeQuery D)} (hq : q ∈ qs) :
    q.left ∈ canopyNodeChildTargets qs ∧ q.right ∈ canopyNodeChildTargets qs := by
  induction qs with
  | nil => nomatch hq
  | cons hd tl ih =>
    rcases List.mem_cons.mp hq with rfl | htl
    · exact ⟨.head _, .tail _ (.head _)⟩
    · rcases ih htl with ⟨hl, hr⟩
      exact ⟨.tail _ (.tail _ hl), .tail _ (.tail _ hr)⟩

/-- Structural single-level top-down online extractor inverting `canopyLevelStep` using ONLY
    `(nodeQueries, activeIdxs, parents, remSibs)` (fuel = `activeIdxs.length`). -/
def extractOnlineCanopyStep {D : Type} [DecidableEq D]
    (nodeQueries : List (RecordedCanopyNodeQuery D)) :
    Nat → List Nat → List (Nat × D) → List D → Option (List (Nat × D) × List D)
  | 0, [], [], remSibs => some ([], remSibs)
  | _ + 1, [], [], remSibs => some ([], remSibs)
  | _ + 1, [u], [(pIdx, pDig)], remSibs =>
    if pIdx = u >>> 1 then
      match findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries with
      | none => none
      | some q =>
        if u &&& 1 = 0 then some ([(u, q.left)], q.right :: remSibs)
        else some ([(u, q.right)], q.left :: remSibs)
    else none
  | fuel + 1, u :: v :: tl, (pIdx, pDig) :: restParents, remSibs =>
    if pIdx = u >>> 1 then
      if v = u ^^^ 1 then
        match findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries,
              extractOnlineCanopyStep nodeQueries fuel tl restParents remSibs with
        | some q, some (tlAct, fullSibs) =>
          some ((u, q.left) :: (v, q.right) :: tlAct, fullSibs)
        | _, _ => none
      else
        match findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries,
              extractOnlineCanopyStep nodeQueries fuel (v :: tl) restParents remSibs with
        | some q, some (vTlAct, afterUSibs) =>
          if u &&& 1 = 0 then some ((u, q.left) :: vTlAct, q.right :: afterUSibs)
          else some ((u, q.right) :: vTlAct, q.left :: afterUSibs)
        | _, _ => none
    else none
  | _, _, _, _ => none

/-- Multi-level top-down online extractor inverting `canopyLevels` from `[(1, top₀)]`. -/
def extractOnlineCanopyLevels {D : Type} [DecidableEq D]
    (nodeQueries : List (RecordedCanopyNodeQuery D)) :
    Nat → List Nat → List (Nat × D) → List D → Option (List (Nat × D) × List D)
  | 0, activeIdxs, topParents, topSibs =>
    if activeIdxs = topParents.map Prod.fst then some (topParents, topSibs) else none
  | d + 1, activeIdxs, topParents, topSibs =>
    let nextIdxs := (steinerLevelStep activeIdxs).1
    match extractOnlineCanopyLevels nodeQueries d nextIdxs topParents topSibs with
    | none => none
    | some (parents, remSibs) =>
      extractOnlineCanopyStep nodeQueries activeIdxs.length activeIdxs parents remSibs

/-- **Pre-challenge online `CanopyMultiProof` extractor**: given `(commitment, rootQueries,
    nodeQueries, logLeaves, indices)`, reconstructs `(leaves, proof)` without seeing the prover's
    post-challenge leaf digests or sibling list. -/
@[expose] def extractOnlineCanopyOpening {D : Type} [DecidableEq D]
    (commitment : D)
    (rootQueries : List (RecordedCanopyRootQuery D))
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (logLeaves : Nat) (indices : List Nat) : Option (List (Nat × D) × List D) :=
  match findFirst (fun q => decide (q.logLeaves = logLeaves) && decide (q.out = commitment))
      rootQueries with
  | none => none
  | some rq =>
    match extractOnlineCanopyLevels nodeQueries logLeaves
        (indices.map (fun i => 2 ^ logLeaves + i)) [(1, rq.top)] [] with
    | none => none
    | some (shiftedLeaves, proof) =>
      some (List.zip indices (shiftedLeaves.map Prod.snd), proof)

private theorem zip_fst_snd_eq {α β : Type} :
    ∀ (xs : List (α × β)), List.zip (xs.map Prod.fst) (xs.map Prod.snd) = xs
  | [] => rfl
  | (_, _) :: tl => congrArg (List.cons _) (zip_fst_snd_eq tl)

private theorem map_snd_shift_eq {D : Type} (off : Nat) :
    ∀ (xs : List (Nat × D)), (xs.map (fun p => (off + p.1, p.2))).map Prod.snd = xs.map Prod.snd
  | [] => rfl
  | (_, _) :: tl => congrArg (List.cons _) (map_snd_shift_eq off tl)

private theorem map_fst_shift_eq {D : Type} (off : Nat) :
    ∀ (xs : List (Nat × D)),
      (xs.map (fun p => (off + p.1, p.2))).map Prod.fst = (xs.map Prod.fst).map (fun i => off + i)
  | [] => rfl
  | (_, _) :: tl => congrArg (List.cons _) (map_fst_shift_eq off tl)

private theorem extractOnlineCanopyStep_targets {D : Type} [DecidableEq D]
    (nodeQueries : List (RecordedCanopyNodeQuery D)) (top₀ : D) :
    ∀ (fuel : Nat) (idxs : List Nat) (parents : List (Nat × D)) (remSibs : List D)
      (act : List (Nat × D)) (sibs : List D),
      extractOnlineCanopyStep nodeQueries fuel idxs parents remSibs = some (act, sibs) →
      ∀ p ∈ act, p.2 ∈ top₀ :: canopyNodeChildTargets nodeQueries
  | 0, [], [], _, act, _, h, p, hp => by
    simp only [extractOnlineCanopyStep, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; nomatch hp
  | 0, _ :: _, _, _, _, _, h, _, _ => by cases h
  | 0, [], _ :: _, _, _, _, h, _, _ => by cases h
  | _ + 1, [], [], _, act, _, h, p, hp => by
    simp only [extractOnlineCanopyStep, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; nomatch hp
  | _ + 1, [], _ :: _, _, _, _, h, _, _ => by cases h
  | _ + 1, [_], [], _, _, _, h, _, _ => by cases h
  | _ + 1, [_], _ :: _ :: _, _, _, _, h, _, _ => by cases h
  | _ + 1, [u], [(pIdx, pDig)], remSibs, act, sibs, h, p, hp => by
    unfold extractOnlineCanopyStep at h
    by_cases hIdx : pIdx = u >>> 1
    · simp only [hIdx, ↓reduceIte] at h
      cases hF : findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries with
      | none => rw [hF] at h; cases h
      | some q =>
        rw [hF] at h; dsimp only at h
        rcases mem_canopyNodeChildTargets_of_mem (findFirst_some_spec _ hF).1 with ⟨hL, hR⟩
        by_cases hp0 : u &&& 1 = 0
        · simp only [hp0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1] at hp; rcases List.mem_singleton.mp hp with rfl; exact .tail _ hL
        · simp only [hp0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1] at hp; rcases List.mem_singleton.mp hp with rfl; exact .tail _ hR
    · simp only [hIdx, ↓reduceIte] at h; cases h
  | _ + 1, _ :: _ :: _, [], _, _, _, h, _, _ => by cases h
  | fuel + 1, u :: v :: tl, (pIdx, pDig) :: restP, remSibs, act, sibs, h, p, hp => by
    unfold extractOnlineCanopyStep at h
    by_cases hIdx : pIdx = u >>> 1
    · simp only [hIdx, ↓reduceIte] at h
      by_cases hv : v = u ^^^ 1
      · simp only [hv, ↓reduceIte] at h
        cases hF : findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries with
        | none => rw [hF] at h; cases h
        | some q =>
          rw [hF] at h
          cases hSub : extractOnlineCanopyStep nodeQueries fuel tl restP remSibs with
          | none => rw [hSub] at h; cases h
          | some sub =>
            rw [hSub] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases mem_canopyNodeChildTargets_of_mem (findFirst_some_spec _ hF).1 with ⟨hL, hR⟩
            rw [← h.1] at hp
            rcases List.mem_cons.mp hp with rfl | hp1
            · exact .tail _ hL
            · rcases List.mem_cons.mp hp1 with rfl | hp2
              · exact .tail _ hR
              · exact extractOnlineCanopyStep_targets nodeQueries top₀ fuel tl restP remSibs
                  sub.1 sub.2 hSub p hp2
      · simp only [hv, ↓reduceIte] at h
        cases hF : findFirst (fun q => decide (q.idx = u >>> 1) && decide (q.out = pDig)) nodeQueries with
        | none => rw [hF] at h; cases h
        | some q =>
          rw [hF] at h
          cases hSub : extractOnlineCanopyStep nodeQueries fuel (v :: tl) restP remSibs with
          | none => rw [hSub] at h; cases h
          | some sub =>
            rw [hSub] at h; dsimp only at h
            rcases mem_canopyNodeChildTargets_of_mem (findFirst_some_spec _ hF).1 with ⟨hL, hR⟩
            by_cases hp0 : u &&& 1 = 0
            · simp only [hp0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1] at hp
              rcases List.mem_cons.mp hp with rfl | hp1
              · exact .tail _ hL
              · exact extractOnlineCanopyStep_targets nodeQueries top₀ fuel (v :: tl) restP
                  remSibs sub.1 sub.2 hSub p hp1
            · simp only [hp0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1] at hp
              rcases List.mem_cons.mp hp with rfl | hp1
              · exact .tail _ hR
              · exact extractOnlineCanopyStep_targets nodeQueries top₀ fuel (v :: tl) restP
                  remSibs sub.1 sub.2 hSub p hp1
    · simp only [hIdx, ↓reduceIte] at h; cases h

private theorem extractOnlineCanopyLevels_targets {D : Type} [DecidableEq D]
    (nodeQueries : List (RecordedCanopyNodeQuery D)) (top₀ : D) :
    ∀ (d : Nat) (idxs : List Nat) (act : List (Nat × D)) (sibs : List D),
      extractOnlineCanopyLevels nodeQueries d idxs [(1, top₀)] [] = some (act, sibs) →
      ∀ p ∈ act, p.2 ∈ top₀ :: canopyNodeChildTargets nodeQueries
  | 0, idxs, act, sibs, h, p, hp => by
    unfold extractOnlineCanopyLevels at h
    by_cases hEq : idxs = [(1, top₀)].map Prod.fst
    · simp only [hEq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1] at hp; rcases List.mem_singleton.mp hp with rfl; exact .head _
    · simp only [hEq, ↓reduceIte] at h; cases h
  | d + 1, idxs, act, sibs, h, p, hp => by
    unfold extractOnlineCanopyLevels at h; dsimp only at h
    cases hUp : extractOnlineCanopyLevels nodeQueries d (steinerLevelStep idxs).1 [(1, top₀)] [] with
    | none => rw [hUp] at h; cases h
    | some up =>
      rw [hUp] at h; dsimp only at h
      exact extractOnlineCanopyStep_targets nodeQueries top₀ idxs.length idxs up.1 up.2 act sibs h p hp

/-- `Type`-valued 5-way constructive online extraction outcome for `verifyCanopyMultiproof`. -/
inductive OnlineCanopyOutcome {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (rootQueries : List (RecordedCanopyRootQuery D))
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (leaves : List (Nat × D)) (proof : List D) : Type where
  | extractedEq
      (hExt : extractOnlineCanopyOpening commitment rootQueries nodeQueries logLeaves
        (leaves.map Prod.fst) = some (leaves, proof))
  | rootCollision (c : CanopyRootCollision rootHash logLeaves)
  | nodeCollision (c : CanopyNodeCollision nodeHash)
  | unqueriedRootPreimage
      (topU : D)
      (hOut : rootHash logLeaves topU = commitment)
      (hUnq : ∀ q ∈ rootQueries, ¬(q.logLeaves = logLeaves ∧ q.top = topU))
  | unqueriedNodePreimage
      (top₀ : D) (idxU : Nat) (lU rU outU : D)
      (hRootMem : ∃ rq ∈ rootQueries, rq.logLeaves = logLeaves ∧ rq.top = top₀ ∧ rq.out = commitment)
      (hOut : nodeHash idxU lU rU = outU)
      (hMem : outU ∈ top₀ :: canopyNodeChildTargets nodeQueries)
      (hUnq : ∀ q ∈ nodeQueries, ¬(q.idx = idxU ∧ q.left = lU ∧ q.right = rU))

private inductive StepClassify {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (top₀ : D)
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (fuel : Nat) (active : List (Nat × D)) (sibs : List D)
    (parents : List (Nat × D)) (remSibs : List D) : Type where
  | ok (hExt : extractOnlineCanopyStep nodeQueries fuel (active.map Prod.fst) parents remSibs =
      some (active, sibs))
  | coll (c : CanopyNodeCollision nodeHash)
  | unq (idxU : Nat) (lU rU outU : D)
      (hOut : nodeHash idxU lU rU = outU)
      (hMem : outU ∈ top₀ :: canopyNodeChildTargets nodeQueries)
      (hUnq : ∀ q ∈ nodeQueries, ¬(q.idx = idxU ∧ q.left = lU ∧ q.right = rU))

private def classifyCanopyStep {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (top₀ : D)
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (hNodeCons : ∀ q ∈ nodeQueries, nodeHash q.idx q.left q.right = q.out) :
    (fuel : Nat) → (active : List (Nat × D)) → (sibs : List D) →
    (parents : List (Nat × D)) → (remSibs : List D) →
    active.length ≤ fuel →
    canopyLevelStep nodeHash active sibs = some (parents, remSibs) →
    (∀ p ∈ parents, p.2 ∈ top₀ :: canopyNodeChildTargets nodeQueries) →
    StepClassify nodeHash top₀ nodeQueries fuel active sibs parents remSibs
  | 0, active, sibs, parents, remSibs, hFuel, hStep, _ => by
    cases active with
    | nil =>
      exact .ok (by
        obtain ⟨hb, ht⟩ := canopyLevelStep_nil nodeHash hStep
        subst hb; subst ht; rfl)
    | cons _ _ => exact absurd hFuel (by simp)
  | fuel + 1, [], sibs, parents, remSibs, _, hStep, _ =>
    .ok (by
      obtain ⟨hb, ht⟩ := canopyLevelStep_nil nodeHash hStep
      subst hb; subst ht; rfl)
  | fuel + 1, [(u, hu)], [], _, _, _, hStep, _ => False.elim (by cases hStep)
  | fuel + 1, [(u, hu)], s :: afterS, parents, remSibs, _, hStep, hParTargets => by
    have hEqStep : parents = [(u >>> 1, canopyParentHash nodeHash u hu s)] ∧ afterS = remSibs := by
      simp only [canopyLevelStep, Option.some.injEq, Prod.mk.injEq] at hStep
      exact ⟨hStep.1.symm, hStep.2⟩
    let pDig := canopyParentHash nodeHash u hu s
    let lCh := if u &&& 1 = 0 then hu else s
    let rCh := if u &&& 1 = 0 then s else hu
    have hHashEq : nodeHash (u >>> 1) lCh rCh = pDig := by
      dsimp only [pDig, canopyParentHash, lCh, rCh]
      by_cases hp : u &&& 1 = 0 <;> simp only [hp, ↓reduceIte]
    have hMemT : pDig ∈ top₀ :: canopyNodeChildTargets nodeQueries :=
      hParTargets (u >>> 1, pDig) (by rw [hEqStep.1]; exact .head _)
    let pred := fun q : RecordedCanopyNodeQuery D =>
      decide (q.idx = u >>> 1) && decide (q.out = pDig)
    match hF : findFirst pred nodeQueries with
    | none =>
      refine .unq (u >>> 1) lCh rCh pDig hHashEq hMemT (fun q hq ⟨hI, hL, hR⟩ => ?_)
      have hFalse := findFirst_none_spec pred hF q hq
      have hOut : q.out = pDig := by rw [← hNodeCons q hq, hI, hL, hR, hHashEq]
      dsimp only [pred] at hFalse
      simp only [hI, hOut, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
    | some q =>
      rcases findFirst_some_spec pred hF with ⟨hqMem, hqP⟩
      dsimp only [pred] at hqP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hqP
      if hEq : (q.left, q.right) = (lCh, rCh) then
        exact .ok (by
          have hL : q.left = lCh := (Prod.mk.inj hEq).1
          have hR : q.right = rCh := (Prod.mk.inj hEq).2
          rw [hEqStep.1, hEqStep.2]
          show extractOnlineCanopyStep nodeQueries (fuel + 1) [u] [(u >>> 1, pDig)] remSibs =
            some ([(u, hu)], s :: remSibs)
          unfold extractOnlineCanopyStep
          dsimp only [pred] at hF
          simp only [↓reduceIte, hF]
          by_cases hp : u &&& 1 = 0 <;>
            (dsimp only [lCh, rCh] at hL hR; simp only [hp, ↓reduceIte] at hL hR ⊢; rw [hL, hR]))
      else
        exact .coll ⟨u >>> 1, q.left, q.right, lCh, rCh, hEq, by
          rw [← hqP.1, hNodeCons q hqMem, hqP.2, ← hHashEq, hqP.1]⟩
  | fuel + 1, (u, hu) :: (v, hv) :: tl, sibs, parents, remSibs, hFuel, hStep, hParTargets => by
    by_cases hv' : v = u ^^^ 1
    · match hSubOpt : canopyLevelStep nodeHash tl sibs with
      | none =>
        exact False.elim (by
          obtain ⟨_, hSub, _⟩ := canopyLevelStep_pair nodeHash hv' hStep
          rw [hSubOpt] at hSub; cases hSub)
      | some (subAct, subRem) =>
        have hShapePair : subRem = remSibs ∧
            parents = (u >>> 1, nodeHash (u >>> 1) hu hv) :: subAct := by
          obtain ⟨act', hSub, hb⟩ := canopyLevelStep_pair nodeHash hv' hStep
          rw [hSubOpt] at hSub
          injection hSub with hPr; injection hPr with hA hR
          subst hA; exact ⟨hR, hb⟩
        let pDig := nodeHash (u >>> 1) hu hv
        have hMemT : pDig ∈ top₀ :: canopyNodeChildTargets nodeQueries :=
          hParTargets (u >>> 1, pDig) (by rw [hShapePair.2]; exact .head _)
        have hTlFuel : tl.length ≤ fuel := by simp only [List.length_cons] at hFuel; omega
        let pred := fun q : RecordedCanopyNodeQuery D =>
          decide (q.idx = u >>> 1) && decide (q.out = pDig)
        match hF : findFirst pred nodeQueries with
        | none =>
          refine .unq (u >>> 1) hu hv pDig rfl hMemT (fun q hq ⟨hI, hL, hR⟩ => ?_)
          have hFalse := findFirst_none_spec pred hF q hq
          have hOut : q.out = pDig := by rw [← hNodeCons q hq, hI, hL, hR]
          dsimp only [pred] at hFalse
          simp only [hI, hOut, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
        | some q =>
          rcases findFirst_some_spec pred hF with ⟨hqMem, hqP⟩
          dsimp only [pred] at hqP
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hqP
          if hEq : (q.left, q.right) = (hu, hv) then
            have hSubStep : canopyLevelStep nodeHash tl sibs = some (subAct, remSibs) := by
              rw [← hShapePair.1]; exact hSubOpt
            match classifyCanopyStep nodeHash top₀ nodeQueries hNodeCons fuel tl sibs subAct remSibs
                hTlFuel hSubStep (fun p hp => hParTargets p (by rw [hShapePair.2]; exact .tail _ hp)) with
            | .coll c => exact .coll c
            | .unq idxU lU rU outU hO hM hU => exact .unq idxU lU rU outU hO hM hU
            | .ok hSubExt =>
              exact .ok (by
                have hL : q.left = hu := (Prod.mk.inj hEq).1
                have hR : q.right = hv := (Prod.mk.inj hEq).2
                rw [hShapePair.2]
                show extractOnlineCanopyStep nodeQueries (fuel + 1) (u :: v :: tl.map Prod.fst)
                    ((u >>> 1, pDig) :: subAct) remSibs =
                  some ((u, hu) :: (v, hv) :: tl, sibs)
                unfold extractOnlineCanopyStep
                dsimp only [pred] at hF
                simp only [↓reduceIte, hv', hF, hSubExt]
                rw [hL, hR])
          else
            exact .coll ⟨u >>> 1, q.left, q.right, hu, hv, hEq, by
              rw [← hqP.1, hNodeCons q hqMem, hqP.2]; dsimp only [pDig]; rw [hqP.1]⟩
    · match sibs, hStep with
      | [], hStepNil =>
        exact False.elim (by
          obtain ⟨_, _, _, hs, _, _⟩ := canopyLevelStep_solo nodeHash hv' hStepNil; cases hs)
      | s :: afterSibs, hStepCons =>
        match hSubOpt : canopyLevelStep nodeHash ((v, hv) :: tl) afterSibs with
        | none =>
          exact False.elim (by
            obtain ⟨_, _, _, hs, hSub, _⟩ := canopyLevelStep_solo nodeHash hv' hStepCons
            injection hs with _ hRestEq; subst hRestEq
            rw [hSubOpt] at hSub; cases hSub)
        | some (subAct, subRem) =>
          have hShapeSolo : subRem = remSibs ∧
              parents = (u >>> 1, canopyParentHash nodeHash u hu s) :: subAct := by
            obtain ⟨c, rest, act', hs, hSub, hb⟩ := canopyLevelStep_solo nodeHash hv' hStepCons
            injection hs with hcEq hRestEq; subst hcEq; subst hRestEq
            rw [hSubOpt] at hSub
            injection hSub with hPr; injection hPr with hA hR
            subst hA; exact ⟨hR, hb⟩
          let pDig := canopyParentHash nodeHash u hu s
          let lCh := if u &&& 1 = 0 then hu else s
          let rCh := if u &&& 1 = 0 then s else hu
          have hHashEq : nodeHash (u >>> 1) lCh rCh = pDig := by
            dsimp only [pDig, canopyParentHash, lCh, rCh]
            by_cases hp : u &&& 1 = 0 <;> simp only [hp, ↓reduceIte]
          have hMemT : pDig ∈ top₀ :: canopyNodeChildTargets nodeQueries :=
            hParTargets (u >>> 1, pDig) (by rw [hShapeSolo.2]; exact .head _)
          have hVTlFuel : ((v, hv) :: tl).length ≤ fuel := Nat.le_of_succ_le_succ hFuel
          let pred := fun q : RecordedCanopyNodeQuery D =>
            decide (q.idx = u >>> 1) && decide (q.out = pDig)
          match hF : findFirst pred nodeQueries with
          | none =>
            refine .unq (u >>> 1) lCh rCh pDig hHashEq hMemT (fun q hq ⟨hI, hL, hR⟩ => ?_)
            have hFalse := findFirst_none_spec pred hF q hq
            have hOut : q.out = pDig := by rw [← hNodeCons q hq, hI, hL, hR, hHashEq]
            dsimp only [pred] at hFalse
            simp only [hI, hOut, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
          | some q =>
            rcases findFirst_some_spec pred hF with ⟨hqMem, hqP⟩
            dsimp only [pred] at hqP
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hqP
            if hEq : (q.left, q.right) = (lCh, rCh) then
              have hSubStep : canopyLevelStep nodeHash ((v, hv) :: tl) afterSibs =
                  some (subAct, remSibs) := by rw [← hShapeSolo.1]; exact hSubOpt
              match classifyCanopyStep nodeHash top₀ nodeQueries hNodeCons fuel ((v, hv) :: tl)
                  afterSibs subAct remSibs hVTlFuel hSubStep
                  (fun p hp => hParTargets p (by rw [hShapeSolo.2]; exact .tail _ hp)) with
              | .coll c => exact .coll c
              | .unq idxU lU rU outU hO hM hU => exact .unq idxU lU rU outU hO hM hU
              | .ok hSubExt =>
                exact .ok (by
                  have hL : q.left = lCh := (Prod.mk.inj hEq).1
                  have hR : q.right = rCh := (Prod.mk.inj hEq).2
                  rw [hShapeSolo.2]
                  show extractOnlineCanopyStep nodeQueries (fuel + 1) (u :: v :: tl.map Prod.fst)
                      ((u >>> 1, pDig) :: subAct) remSibs =
                    some ((u, hu) :: (v, hv) :: tl, s :: afterSibs)
                  unfold extractOnlineCanopyStep
                  dsimp only [pred] at hF
                  dsimp only [List.map] at hSubExt
                  simp only [↓reduceIte, hv', hF, hSubExt]
                  by_cases hp : u &&& 1 = 0 <;>
                    (dsimp only [lCh, rCh] at hL hR; simp only [hp, ↓reduceIte] at hL hR ⊢; rw [hL, hR]))
            else
              exact .coll ⟨u >>> 1, q.left, q.right, lCh, rCh, hEq, by
                rw [← hqP.1, hNodeCons q hqMem, hqP.2, ← hHashEq, hqP.1]⟩

private inductive LevelsClassify {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (top₀ : D)
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (d : Nat) (active : List (Nat × D)) (sibs : List D) : Type where
  | ok (hExt : extractOnlineCanopyLevels nodeQueries d (active.map Prod.fst) [(1, top₀)] [] =
      some (active, sibs))
  | coll (c : CanopyNodeCollision nodeHash)
  | unq (idxU : Nat) (lU rU outU : D)
      (hOut : nodeHash idxU lU rU = outU)
      (hMem : outU ∈ top₀ :: canopyNodeChildTargets nodeQueries)
      (hUnq : ∀ q ∈ nodeQueries, ¬(q.idx = idxU ∧ q.left = lU ∧ q.right = rU))

private def classifyCanopyLevels {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (top₀ : D)
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (hNodeCons : ∀ q ∈ nodeQueries, nodeHash q.idx q.left q.right = q.out) :
    (d : Nat) → (active : List (Nat × D)) → (sibs : List D) →
    canopyLevels nodeHash d active sibs = some ([(1, top₀)], []) →
    LevelsClassify nodeHash top₀ nodeQueries d active sibs
  | 0, active, sibs, hLvls =>
    .ok (by
      simp only [canopyLevels, Option.some.injEq, Prod.mk.injEq] at hLvls
      rcases hLvls with ⟨rfl, rfl⟩; rfl)
  | d + 1, active, sibs, hLvls => by
    match hStep : canopyLevelStep nodeHash active sibs with
    | none =>
      exact False.elim (by
        obtain ⟨_, _, hs, _⟩ := canopyLevels_succ nodeHash hLvls
        rw [hStep] at hs; cases hs)
    | some (midAct, midSibs) =>
      have hRest : canopyLevels nodeHash d midAct midSibs = some ([(1, top₀)], []) := by
        obtain ⟨m, r, hs, hr⟩ := canopyLevels_succ nodeHash hLvls
        rw [hStep] at hs; injection hs with hPr; injection hPr with hm hr'
        subst hm; subst hr'; exact hr
      have hShape := (canopyLevelStep_shape nodeHash _ active sibs midAct midSibs
        (Nat.lt_succ_self _) hStep).1
      match classifyCanopyLevels nodeHash top₀ nodeQueries hNodeCons d midAct midSibs hRest with
      | .coll c => exact .coll c
      | .unq idxU lU rU outU hO hM hU => exact .unq idxU lU rU outU hO hM hU
      | .ok hUpExt =>
        have hUpTargets := extractOnlineCanopyLevels_targets nodeQueries top₀ d
          (midAct.map Prod.fst) midAct midSibs hUpExt
        match classifyCanopyStep nodeHash top₀ nodeQueries hNodeCons active.length active sibs
            midAct midSibs (Nat.le_refl _) hStep hUpTargets with
        | .coll c => exact .coll c
        | .unq idxU lU rU outU hO hM hU => exact .unq idxU lU rU outU hO hM hU
        | .ok hStepExt =>
          exact .ok (by
            show extractOnlineCanopyLevels nodeQueries (d + 1) (active.map Prod.fst) [(1, top₀)] [] =
              some (active, sibs)
            unfold extractOnlineCanopyLevels; dsimp only
            rw [← hShape, hUpExt]; dsimp only
            rw [List.length_map]; exact hStepExt)

/-- **Constructive `Type`-valued online `CanopyMultiProof` query-table classifier**
    (`0 Classical.choice`). -/
def classifyOnlineCanopyOpening {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (rootQueries : List (RecordedCanopyRootQuery D))
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (hRootCons : ∀ q ∈ rootQueries, rootHash q.logLeaves q.top = q.out)
    (hNodeCons : ∀ q ∈ nodeQueries, nodeHash q.idx q.left q.right = q.out)
    (leaves : List (Nat × D)) (proof : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    OnlineCanopyOutcome nodeHash rootHash logLeaves commitment rootQueries nodeQueries
      leaves proof := by
  match hLvlsOpt : canopyLevels nodeHash logLeaves
      (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof with
  | some ([(uTop, top)], []) =>
    have hTopSpec : uTop = 1 ∧ rootHash logLeaves top = commitment := by
      obtain ⟨top', hL, hR⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hLvlsOpt] at hL
      injection hL with hPr; injection hPr with hList _
      injection hList with hHead _; injection hHead with hu ht
      subst ht; exact ⟨hu, hR⟩
    let rPred := fun q : RecordedCanopyRootQuery D =>
      decide (q.logLeaves = logLeaves) && decide (q.out = commitment)
    match hRF : findFirst rPred rootQueries with
    | none =>
      refine .unqueriedRootPreimage top hTopSpec.2 (fun q hq ⟨hLL, hTop⟩ => ?_)
      have hFalse := findFirst_none_spec rPred hRF q hq
      have hOut : q.out = commitment := by rw [← hRootCons q hq, hLL, hTop, hTopSpec.2]
      dsimp only [rPred] at hFalse
      simp only [hLL, hOut, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
    | some rq =>
      rcases findFirst_some_spec rPred hRF with ⟨hrqMem, hrqP⟩
      dsimp only [rPred] at hrqP
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrqP
      if hTopEq : rq.top = top then
        have hLvlsRq : canopyLevels nodeHash logLeaves
            (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof = some ([(1, rq.top)], []) := by
          rw [hTopEq, ← hTopSpec.1]; exact hLvlsOpt
        match classifyCanopyLevels nodeHash rq.top nodeQueries hNodeCons logLeaves
            (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof hLvlsRq with
        | .coll c => exact .nodeCollision c
        | .unq idxU lU rU outU hO hM hU =>
          exact .unqueriedNodePreimage rq.top idxU lU rU outU
            ⟨rq, hrqMem, hrqP.1, rfl, hrqP.2⟩ hO hM hU
        | .ok hExtLvls =>
          exact .extractedEq (by
            unfold extractOnlineCanopyOpening
            rw [hRF]; dsimp only
            rw [map_fst_shift_eq (2 ^ logLeaves) leaves] at hExtLvls
            rw [hExtLvls]; dsimp only
            rw [map_snd_shift_eq (2 ^ logLeaves) leaves, zip_fst_snd_eq leaves])
      else
        exact .rootCollision ⟨rq.top, top, hTopEq, by
          have h1 := hRootCons rq hrqMem
          rw [hrqP.1, hrqP.2] at h1
          exact h1.trans hTopSpec.2.symm⟩
  | none =>
    exact False.elim (by
      obtain ⟨_, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hL] at hLvlsOpt; cases hLvlsOpt)
  | some ([], _) =>
    exact False.elim (by
      obtain ⟨_, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hL] at hLvlsOpt; injection hLvlsOpt with hp; injection hp with hl _; cases hl)
  | some (_ :: _ :: _, _) =>
    exact False.elim (by
      obtain ⟨_, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hL] at hLvlsOpt; injection hLvlsOpt with hp; injection hp with hl _
      injection hl with _ htl; cases htl)
  | some ([_], _ :: _) =>
    exact False.elim (by
      obtain ⟨_, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
      rw [hL] at hLvlsOpt; injection hLvlsOpt with hp; injection hp with _ hr; cases hr)

/-- **Pre-challenge binding of `CanopyMultiProof` online extraction**. -/
theorem onlineCanopy_preChallenge_unique {D : Type} [DecidableEq D]
    (commitment : D)
    (rootQueries : List (RecordedCanopyRootQuery D))
    (nodeQueries : List (RecordedCanopyNodeQuery D))
    (logLeaves : Nat) (leaves₁ leaves₂ : List (Nat × D)) (proof₁ proof₂ : List D)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (h₁ : extractOnlineCanopyOpening commitment rootQueries nodeQueries logLeaves
      (leaves₁.map Prod.fst) = some (leaves₁, proof₁))
    (h₂ : extractOnlineCanopyOpening commitment rootQueries nodeQueries logLeaves
      (leaves₂.map Prod.fst) = some (leaves₂, proof₂)) :
    leaves₁ = leaves₂ ∧ proof₁ = proof₂ := by
  rw [hIdx] at h₁
  exact Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))


/-! ## §3. Unitary `QVec` / `GaussInt` Quantum Online-Extraction Reduction (`qromMerkleOnlineExtractBound`) -/

private theorem qsum_ofFin_eq_single (w : Nat) (y : BitVec w) :
    qsum (2 ^ w) (fun j => if BitVec.ofFin j = y then 1 else 0) = 1 := by
  have hCongr : qsum (2 ^ w) (fun j => if BitVec.ofFin j = y then 1 else 0) =
      qsum (2 ^ w) (fun j => if j = y.toFin then 1 else 0) := by
    apply qsum_congr; intro j
    by_cases hj : j = y.toFin
    · subst hj; simp
    · have hne : BitVec.ofFin j ≠ y := fun he => hj (by rw [← he])
      simp [hj, hne]
  rw [hCongr, qsum_eq_indicator]

/-- At most `ts.length` values `j : Fin (2 ^ w)` land inside any target list `ts : List (BitVec w)`. -/
theorem qsum_ofFin_listHasElem_le_length (w : Nat) :
    ∀ (ts : List (BitVec w)),
      qsum (2 ^ w) (fun j => if listHasElem (BitVec.ofFin j) ts = true then 1 else 0) ≤ ts.length
  | [] => by simp only [listHasElem, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]; omega
  | t :: rest => by
    have ih := qsum_ofFin_listHasElem_le_length w rest
    have hSplit :
        qsum (2 ^ w) (fun j => if listHasElem (BitVec.ofFin j) (t :: rest) = true then 1 else 0) ≤
        qsum (2 ^ w) (fun j =>
          (if BitVec.ofFin j = t then 1 else 0) +
          (if listHasElem (BitVec.ofFin j) rest = true then 1 else 0)) := by
      apply qsum_le_qsum; intro j
      rw [listHasElem]
      by_cases hjt : BitVec.ofFin j = t
      · simp [hjt]
      · simp [hjt]
    rw [qsum_add, qsum_ofFin_eq_single w t] at hSplit
    simp only [List.length_cons]
    omega

/-- `QromRbrRound` for a coordinate `x = proj z` hashing into a target list of size `≤ T`
    that is invariant under reprogramming `x`. The definition does not assert that `x` was
    unqueried, or that the targets were extracted before a protocol challenge. -/
def qromTargetSetRound {cardX w : Nat} (H : Fin cardX → BitVec w)
    (proj : Fin cardX → Fin cardX)
    (targetSet : (Fin cardX → BitVec w) → Fin cardX → List (BitVec w))
    (T : Nat)
    (hLocal : ∀ (O : Fin cardX → BitVec w) (x : Fin cardX) (ch : BitVec w),
      targetSet (reprogramOracle O x ch) x = targetSet O x)
    (hCard : ∀ (O : Fin cardX → BitVec w) (x : Fin cardX), (targetSet O x).length ≤ T) :
    QromRbrRound cardX w H where
  proj := proj
  isDoomedAt := fun _ _ => true
  isLiveAfter := fun O x => listHasElem (O x) (targetSet O x)
  badCard := T
  doomed_local := fun _ _ => rfl
  flip_bound := fun x _ => by
    have hEq : ∀ j : Fin (2 ^ w),
        listHasElem ((reprogramOracle H x (BitVec.ofFin j)) x)
          (targetSet (reprogramOracle H x (BitVec.ofFin j)) x) =
        listHasElem (BitVec.ofFin j) (targetSet H x) := by
      intro j
      rw [hLocal H x (BitVec.ofFin j)]
      simp [reprogramOracle]
    rw [qsum_congr (fun j => by rw [hEq j])]
    exact Nat.le_trans (qsum_ofFin_listHasElem_le_length w (targetSet H x)) (hCard H x)

/-- **Unitary `QVec` / `GaussInt` Target-Set Preimage Bound (`qrom_unitary_target_hit_bound`)**. -/
theorem qrom_unitary_target_hit_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (proj : Fin cardX → Fin cardX)
    (targetSet : (Fin cardX → BitVec w) → Fin cardX → List (BitVec w))
    (T : Nat)
    (hLocal : ∀ (O : Fin cardX → BitVec w) (x : Fin cardX) (ch : BitVec w),
      targetSet (reprogramOracle O x ch) x = targetSet O x)
    (hCard : ∀ (O : Fin cardX → BitVec w) (x : Fin cardX), (targetSet O x).length ≤ T) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    let live := fun (O : Fin cardX → BitVec w) (x : Fin cardX) => listHasElem (O x) (targetSet O x)
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H =>
          qromOrdinaryFlipMass A H proj (fun _ _ => true) live),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * T, 2 ^ w, Nat.two_pow_pos w⟩ :=
  qrom_uniform_oracle_round_bound A
    (fun H => qromTargetSetRound H proj targetSet T hLocal hCard)
    proj (fun _ _ => true) (fun O x => listHasElem (O x) (targetSet O x)) T
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem twoQ_plus_one_sq_le_eight_Q_succ_sq (Q : Nat) :
    (2 * Q + 1) ^ 2 ≤ 8 * (Q + 1) ^ 2 := by
  have h1 : 2 * Q + 1 ≤ 2 * (Q + 1) := by omega
  have h2 : (2 * Q + 1) ^ 2 ≤ (2 * (Q + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : (2 * (Q + 1)) ^ 2 = 4 * (Q + 1) ^ 2 := by rw [Nat.mul_pow]
  rw [h3] at h2
  exact Nat.le_trans h2 (Nat.mul_le_mul_right ((Q + 1) ^ 2) (by decide : 4 ≤ 8))

private theorem twoQ_plus_one_cube_le_eight_Q_succ_cube (Q : Nat) :
    (2 * Q + 1) ^ 2 * (2 * Q + 1) ≤ 8 * (Q + 1) ^ 3 := by
  have hPow : (2 * Q + 1) ^ 2 * (2 * Q + 1) = (2 * Q + 1) ^ 3 := (Nat.pow_succ (2 * Q + 1) 2).symm
  have h1 : 2 * Q + 1 ≤ 2 * (Q + 1) := by omega
  have h2 : (2 * Q + 1) ^ 3 ≤ (2 * (Q + 1)) ^ 3 := Nat.pow_le_pow_left h1 3
  have h3 : (2 * (Q + 1)) ^ 3 = 8 * (Q + 1) ^ 3 := by rw [Nat.mul_pow]
  rw [hPow, ← h3]; exact h2

/-- Exact algebraic dominance of `qromMerkleOnlineExtractBound numRoots w Q` over the unitary
    Measure-and-Reprogram bound `(2Q + 1)^2 * (numRoots * (1 + (2Q + 1))) / 2^w`. -/
theorem unitary_merkle_raw_le_qromMerkleOnlineExtractBound (numRoots w Q : Nat) :
    RatBound.le
      ⟨(2 * Q + 1) ^ 2 * (numRoots * (1 + (2 * Q + 1))), 2 ^ w, Nat.two_pow_pos w⟩
      (qromMerkleOnlineExtractBound numRoots w Q) := by
  unfold qromMerkleOnlineExtractBound RatBound.scale RatBound.add
    quantumGroverSingleTargetBound quantumZhandryMultiTargetBound quantumBhtCollisionBound
    RatBound.le
  dsimp only
  have hPerRoot :
      (2 * Q + 1) ^ 2 * (1 + (2 * Q + 1)) ≤
        8 * 1 * (Q + 1) ^ 2 + 8 * (Q + 1) ^ 3 := by
    rw [Nat.mul_add, Nat.mul_one, show 8 * 1 = 8 from rfl]
    exact Nat.add_le_add (twoQ_plus_one_sq_le_eight_Q_succ_sq Q)
      (twoQ_plus_one_cube_le_eight_Q_succ_cube Q)
  have hScaled :
      (2 * Q + 1) ^ 2 * (numRoots * (1 + (2 * Q + 1))) ≤
        numRoots * (8 * 1 * (Q + 1) ^ 2 + 8 * (Q + 1) ^ 3) := by
    rw [← Nat.mul_assoc, Nat.mul_comm ((2 * Q + 1) ^ 2) numRoots, Nat.mul_assoc]
    exact Nat.mul_le_mul_left numRoots hPerRoot
  let S := 8 * 1 * (Q + 1) ^ 2 + 8 * (Q + 1) ^ 3
  let W := 2 ^ w
  have hRhsEq :
      numRoots * (8 * 1 * (Q + 1) ^ 2 * W + 8 * (Q + 1) ^ 3 * W) * W =
      numRoots * S * (W * W) := by
    dsimp only [S]
    rw [← Nat.add_mul (8 * 1 * (Q + 1) ^ 2) (8 * (Q + 1) ^ 3) W,
        ← Nat.mul_assoc numRoots _ W,
        Nat.mul_assoc (numRoots * _) W W]
  change (2 * Q + 1) ^ 2 * (numRoots * (1 + (2 * Q + 1))) * (W * W) ≤
    numRoots * (8 * 1 * (Q + 1) ^ 2 * W + 8 * (Q + 1) ^ 3 * W) * W
  rw [hRhsEq]
  exact Nat.mul_le_mul_right (W * W) hScaled

/-- Conditional target-hit union bound with the arithmetic Merkle extraction budget.
    `failExtract` is an arbitrary event. A protocol reduction must supply `hCover`, `hLocal`,
    and `hCard`; this theorem neither constructs a query table nor relates that event to
    `classifyOnlineMerkleOpening` or `classifyOnlineCanopyOpening`. -/
theorem qrom_unitary_multiRoot_merkle_extract_bound {cardX w cardAnc Q : Nat}
    (numRoots : Nat)
    (A : QuantumAdv cardX w cardAnc Q)
    (failExtract : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (proj : Fin (2 * numRoots) → Fin cardX → Fin cardX)
    (targetSet : Fin (2 * numRoots) → (Fin cardX → BitVec w) → Fin cardX → List (BitVec w))
    (hLocal : ∀ r O x ch, targetSet r (reprogramOracle O x ch) x = targetSet r O x)
    (hCard : ∀ r O x,
      (targetSet r O x).length ≤ (if r.1 % 2 = 0 then 1 else 2 * Q + 1))
    (hCover : ∀ H, QVec.queryMassOn (failExtract H) (runQuantumAdv A H) ≤
      qsum (2 * numRoots) (fun r =>
        qromOrdinaryFlipMass A H (proj r) (fun _ _ => true)
          (fun O x => listHasElem (O x) (targetSet r O x)))) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => QVec.queryMassOn (failExtract H) (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (qromMerkleOnlineExtractBound numRoots w Q) := by
  let bad : Fin (2 * numRoots) → Nat := fun r => if r.1 % 2 = 0 then 1 else 2 * Q + 1
  have hUnion := qrom_uniform_oracle_success_bound A failExtract
    (fun r H => qromTargetSetRound H (proj r) (targetSet r) (bad r) (hLocal r) (hCard r))
    proj (fun _ _ _ => true) (fun r O x => listHasElem (O x) (targetSet r O x)) bad
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) hCover
  have hSumBad : ∀ m : Nat,
      qsum (2 * m) (fun r : Fin (2 * m) => if r.1 % 2 = 0 then 1 else 2 * Q + 1) =
        m * (1 + (2 * Q + 1)) := by
    intro m
    induction m with
    | zero => simp [qsum]
    | succ k ih =>
      let C := 1 + (2 * Q + 1)
      have hStep2 : ∀ (n : Nat), n = 2 * k →
          qsum (n + 2) (fun r : Fin (n + 2) => if r.1 % 2 = 0 then 1 else 2 * Q + 1) =
            C + qsum n (fun r : Fin n => if r.1 % 2 = 0 then 1 else 2 * Q + 1) := by
        intro n _
        change qsum ((n + 1) + 1) _ = _
        simp only [qsum]
        have h1 : (0 + 1 : Nat) % 2 = 1 := rfl
        have hMod : ∀ (i : Fin n), (i.1 + 1 + 1) % 2 = i.1 % 2 := fun _ => by omega
        rw [qsum_congr (fun i => by rw [hMod i])]
        simp only [h1, Nat.one_ne_zero, ↓reduceIte]
        dsimp only [C]
        omega
      have hEq2 : 2 * (k + 1) = 2 * k + 2 := by omega
      have hGen : ∀ (N : Nat), N = 2 * k + 2 →
          qsum N (fun r : Fin N => if r.1 % 2 = 0 then 1 else 2 * Q + 1) =
            (k + 1) * C := by
        intro N hN; subst hN
        rw [hStep2 (2 * k) rfl, Nat.succ_mul k C]
        change C + qsum (2 * k) (fun r : Fin (2 * k) => if r.1 % 2 = 0 then 1 else 2 * Q + 1) =
          k * C + C
        rw [ih]
        exact Nat.add_comm C (k * C)
      exact hGen (2 * (k + 1)) hEq2
  have hBadEq : qsum (2 * numRoots) bad = numRoots * (1 + (2 * Q + 1)) := hSumBad numRoots
  rw [hBadEq] at hUnion
  exact RatBound.le_trans hUnion (unitary_merkle_raw_le_qromMerkleOnlineExtractBound numRoots w Q)

/-- Single-root specialization (`numRoots = 1`) of `qrom_unitary_multiRoot_merkle_extract_bound`. -/
theorem qrom_unitary_single_root_merkle_extract_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (failExtract : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (proj : Fin 2 → Fin cardX → Fin cardX)
    (targetSet : Fin 2 → (Fin cardX → BitVec w) → Fin cardX → List (BitVec w))
    (hLocal : ∀ r O x ch, targetSet r (reprogramOracle O x ch) x = targetSet r O x)
    (hCard : ∀ r O x, (targetSet r O x).length ≤ (if r.1 % 2 = 0 then 1 else 2 * Q + 1))
    (hCover : ∀ H, QVec.queryMassOn (failExtract H) (runQuantumAdv A H) ≤
      qsum 2 (fun r =>
        qromOrdinaryFlipMass A H (proj r) (fun _ _ => true)
          (fun O x => listHasElem (O x) (targetSet r O x)))) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => QVec.queryMassOn (failExtract H) (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (qromMerkleOnlineExtractBound 1 w Q) :=
  qrom_unitary_multiRoot_merkle_extract_bound 1 A failExtract proj targetSet hLocal hCard hCover

private def witnessInitVec : QVec 2 2 1 :=
  fun x y _ => if x.1 = 0 ∧ y.1 = 0 then ⟨1, 0⟩ else GaussInt.zero

private theorem witnessInitVec_pos : 0 < QVec.stateNormSq witnessInitVec := by decide

private def witnessQuantumAdv : QuantumAdv 2 2 1 0 :=
  { init := witnessInitVec, h_init_pos := witnessInitVec_pos, steps := fun t => Fin.elim0 t }

private def witnessFailExtract (H : Fin 2 → BitVec 2) (x : Fin 2) : Bool :=
  decide ((H x).toNat = 0)

private def witnessProj (_ : Fin (2 * 1)) (x : Fin 2) : Fin 2 := x

private def witnessTargetSet (_ : Fin (2 * 1)) (_ : Fin 2 → BitVec 2) (_ : Fin 2) :
    List (BitVec 2) := [0#2]

private theorem witnessCoverProof (H : Fin 2 → BitVec 2) :
    QVec.queryMassOn (witnessFailExtract H) (runQuantumAdv witnessQuantumAdv H) ≤
      qsum (2 * 1) (fun r =>
        qromOrdinaryFlipMass witnessQuantumAdv H (witnessProj r) (fun _ _ => true)
          (fun O x => listHasElem (O x) (witnessTargetSet r O x))) := by
  have hPt : ∀ (ψ : QVec 2 2 1) (x : Fin 2),
      QVec.queryWeight ψ x ≤ QVec.queryMassOn (fun z => decide (x = z)) ψ := by
    intro ψ ⟨i, hi⟩
    match i, hi with
    | 0, _ =>
      unfold QVec.queryMassOn qsum; dsimp only
      simp only [decide_true, ↓reduceIte]
      exact Nat.le_add_right _ _
    | 1, _ =>
      unfold QVec.queryMassOn
      simp only [qsum, Fin.ext_iff, Nat.one_ne_zero, Nat.zero_add, decide_false, decide_true,
        Bool.false_eq_true, ↓reduceIte]
      omega
  have hLe : QVec.queryMassOn (witnessFailExtract H) (runQuantumAdv witnessQuantumAdv H) ≤
      qromOrdinaryFlipMass witnessQuantumAdv H (witnessProj ⟨0, by omega⟩) (fun _ _ => true)
        (fun O x => listHasElem (O x) (witnessTargetSet ⟨0, by omega⟩ O x)) := by
    unfold QVec.queryMassOn qromOrdinaryFlipMass witnessFailExtract witnessProj witnessTargetSet
    apply qsum_le_qsum; intro x
    by_cases h0 : (H x).toNat = 0
    · have hBv : H x = 0#2 := BitVec.eq_of_toNat_eq h0
      have hElem : listHasElem (H x) [0#2] = true := by rw [hBv]; rfl
      simp only [h0, decide_true, Bool.true_and, hElem, ↓reduceIte]
      exact hPt (runQuantumAdv witnessQuantumAdv H) x
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact Nat.zero_le _
  exact Nat.le_trans hLe (Nat.le_add_right _ _)

/-- Inhabitedness of the conditional target-hit premises: zero queries, two-bit answers,
    and constant singleton targets. This is not an inhabited Merkle extraction execution. -/
theorem inhabited_qrom_unitary_merkle_extract :
    ∃ (cardX w cardAnc Q numRoots : Nat)
      (A : QuantumAdv cardX w cardAnc Q)
      (failExtract : (Fin cardX → BitVec w) → Fin cardX → Bool)
      (proj : Fin (2 * numRoots) → Fin cardX → Fin cardX)
      (targetSet : Fin (2 * numRoots) → (Fin cardX → BitVec w) → Fin cardX → List (BitVec w)),
      (∀ r O x ch, targetSet r (reprogramOracle O x ch) x = targetSet r O x) ∧
      (∀ r O x, (targetSet r O x).length ≤ (if r.1 % 2 = 0 then 1 else 2 * Q + 1)) ∧
      (∀ H, QVec.queryMassOn (failExtract H) (runQuantumAdv A H) ≤
        qsum (2 * numRoots) (fun r =>
          qromOrdinaryFlipMass A H (proj r) (fun _ _ => true)
            (fun O x => listHasElem (O x) (targetSet r O x)))) :=
  ⟨2, 2, 1, 0, 1, witnessQuantumAdv, witnessFailExtract, witnessProj, witnessTargetSet,
    (fun _ _ _ _ => rfl),
    (fun _ _ _ => by unfold witnessTargetSet; simp),
    witnessCoverProof⟩

#verify_inhabited
  Qsag.qrom_unitary_multiRoot_merkle_extract_bound
  Qsag.inhabited_qrom_unitary_merkle_extract

#verify_constructive
  Qsag.merkleChildTargets_length
  Qsag.merklePreChallengeTargets_length
  Qsag.onlineMerkleOutcome_collision_sound
  Qsag.onlineMerkle_preChallenge_unique
  Qsag.tooth_onlineMerkle_empty_queries_unqueried_root
  Qsag.onlineCanopy_preChallenge_unique
  Qsag.qsum_ofFin_listHasElem_le_length
  Qsag.qrom_unitary_target_hit_bound
  Qsag.unitary_merkle_raw_le_qromMerkleOnlineExtractBound
  Qsag.qrom_unitary_multiRoot_merkle_extract_bound
  Qsag.qrom_unitary_single_root_merkle_extract_bound
  Qsag.inhabited_qrom_unitary_merkle_extract

end Qsag
end
