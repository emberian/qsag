module
/-
# Unitary QROM Merkle Online Extraction (`merkleRootFromPath` & `verifyCanopyMultiproof`)

Constructive (`0 sorry`, `0` custom `axiom`, `0 Classical.choice`) quantum random-oracle online
extraction reduction for tweaked Merkle paths (`merkleRootFromPath`) and Steiner-deduplicated
`CanopyMultiProof` commitments (`verifyCanopyMultiproof` from `pcs.rs`):

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

3. **Unitary `QVec` / `GaussInt` Quantum Extraction Bound (`qrom_unitary_target_hit_bound`,
   `qrom_unitary_single_root_merkle_extract_bound`,
   `qrom_unitary_multiRoot_merkle_extract_bound`)**:
   Mechanizes `qromMerkleOnlineExtractBound numRoots w Q` directly from unitary
   `QVec` / `GaussInt` oracle executions via `QromRbrRound` and `qrom_uniform_oracle_success_bound`:
   hitting `1` root target costs `≤ (2Q + 1)^2 / 2^w ≤ quantumGroverSingleTargetBound w Q`, and
   hitting `≤ 2Q + 1` query-child / collision targets costs
   `≤ (2Q + 1)^3 / 2^w ≤ 8(Q + 1)^3 / 2^w = quantumBhtCollisionBound w Q`.
-/

public import Qsag.MultiRoundFsQrom
import all Qsag.MultiRoundFsQrom
public import Qsag.SuccinctAggregationIop
import all Qsag.SuccinctAggregationIop
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

/-- One recorded compression query `(lvl, node, left, right) ↦ out` in a pre-challenge QROM
    query table. -/
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
