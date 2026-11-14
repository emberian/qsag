module
/-
# Advanced MPC and credentials
Complete constructive kernel proofs with zero trust bypasses.
LAW-M1: public statements with a bounded exposed interface.
The models below describe arithmetic circuits and immutable committed views;
implementation refinement and cryptographic binding are separate obligations.
-/

public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Poseidon2
public import Qsag.Constructive

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. `FrontierSumFts` Prefix-Free Antichain Frontiers & Rank/Unrank Bijection -/

/-- Binary-tree root-to-leaf antichain frontier. -/
inductive FrontierAntichain : Type where
  | leafNode : FrontierAntichain
  | branchSplit : FrontierAntichain → FrontierAntichain → FrontierAntichain
  deriving DecidableEq, Repr

/-- Extract root-to-frontier bit paths (`false` = left child, `true` = right child). -/
def FrontierAntichain.paths : FrontierAntichain → List (List Bool)
  | .leafNode => [[]]
  | .branchSplit l r => (l.paths.map (false :: ·)) ++ (r.paths.map (true :: ·))

/-- Height bound predicate on a `FrontierAntichain`. -/
def FrontierAntichain.WithinHeight : FrontierAntichain → Nat → Prop
  | .leafNode, _ => True
  | .branchSplit _ _, 0 => False
  | .branchSplit l r, h + 1 => l.WithinHeight h ∧ r.WithinHeight h

/-- Prefix-free antichain relation: no two distinct frontier paths have one as a prefix of the other. -/
def IsPrefixFreeAntichain (ps : List (List Bool)) : Prop :=
  ps.Pairwise (fun u v => ¬ List.IsPrefix u v ∧ ¬ List.IsPrefix v u)

private theorem not_isPrefix_cons_same {b : Bool} {u v : List Bool}
    (h : ¬ List.IsPrefix u v) : ¬ List.IsPrefix (b :: u) (b :: v) := by
  intro ⟨t, ht⟩
  injection ht with _ htail
  exact h ⟨t, htail⟩

private theorem not_isPrefix_false_true (u v : List Bool) :
    ¬ List.IsPrefix (false :: u) (true :: v) := by
  intro ⟨t, ht⟩
  injection ht with hhead _
  cases hhead

private theorem not_isPrefix_true_false (u v : List Bool) :
    ¬ List.IsPrefix (true :: u) (false :: v) := by
  intro ⟨t, ht⟩
  injection ht with hhead _
  cases hhead

private theorem pairwise_map_cons_bit (b : Bool) {ps : List (List Bool)}
    (hp : IsPrefixFreeAntichain ps) :
    IsPrefixFreeAntichain (ps.map (b :: ·)) := by
  unfold IsPrefixFreeAntichain at *
  rw [List.pairwise_map]
  exact List.Pairwise.imp (fun h => ⟨not_isPrefix_cons_same h.1, not_isPrefix_cons_same h.2⟩) hp

/-- Every `FrontierAntichain` produces a strictly prefix-free antichain of tree paths. -/
theorem frontierAntichain_paths_prefixFree (c : FrontierAntichain) : IsPrefixFreeAntichain c.paths := by
  induction c with
  | leafNode =>
    unfold FrontierAntichain.paths IsPrefixFreeAntichain
    exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | branchSplit l r ihl ihr =>
    unfold FrontierAntichain.paths IsPrefixFreeAntichain
    rw [List.pairwise_append]
    refine ⟨pairwise_map_cons_bit false ihl, pairwise_map_cons_bit true ihr, ?_⟩
    intro a ha b hb
    rw [List.mem_map] at ha hb
    rcases ha with ⟨u, _, rfl⟩
    rcases hb with ⟨v, _, rfl⟩
    exact ⟨not_isPrefix_false_true u v, not_isPrefix_true_false v u⟩

/-- Recursive DP enumeration of height-`h`, size-`L` binary-tree antichain frontiers. -/
def enumFrontierAntichains : Nat → Nat → List FrontierAntichain
  | 0, L => if L == 1 then [.leafNode] else []
  | h + 1, L =>
    if L == 0 then []
    else if L == 1 then [.leafNode]
    else
      (List.range (L - 1)).flatMap (fun k =>
        let leftL := k + 1
        let rightL := L - leftL
        (enumFrontierAntichains h leftL).flatMap (fun lc =>
          (enumFrontierAntichains h rightL).map (fun rc => .branchSplit lc rc)))

/-- Recursive DP enumeration of length-`L` $w$-ary chain vectors summing to `S`. -/
def enumSumChains (w : Nat) : Nat → Nat → List (List Nat)
  | 0, S => if S == 0 then [[]] else []
  | L + 1, S =>
    (List.range (Nat.min w (S + 1))).flatMap (fun step =>
      (enumSumChains w L (S - step)).map (step :: ·))

/-- Cartesian enumeration of decorated `(FrontierAntichain × List Nat)` configurations. -/
def enumDecoratedFrontiers (h w L S : Nat) : List (FrontierAntichain × List Nat) :=
  (enumFrontierAntichains h L).flatMap (fun fc =>
    (enumSumChains w L S).map (fun ch => (fc, ch)))

/-- Deterministic rank over `(h, w, L, S)` decorated frontiers. -/
def frontierSumRank (h w L S : Nat) (cfg : FrontierAntichain × List Nat) : Option Nat :=
  let table := enumDecoratedFrontiers h w L S
  let idx := table.idxOf cfg
  if idx < table.length then some idx else none

/-- Deterministic unrank over `(h, w, L, S)` decorated frontiers. -/
def frontierSumUnrank (h w L S : Nat) (idx : Nat) : Option (FrontierAntichain × List Nat) :=
  (enumDecoratedFrontiers h w L S)[idx]?

private theorem nodup_append_of_disjoint {α : Type} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hDisj : ∀ x, x ∈ l₁ → x ∈ l₂ → False) :
    (l₁ ++ l₂).Nodup := by
  induction h₁ with
  | nil => exact h₂
  | @cons a as haNotMem _ ih =>
    simp only [List.cons_append]
    refine List.Pairwise.cons ?_ (ih (fun x hx1 hx2 => hDisj x (List.mem_cons_of_mem a hx1) hx2))
    intro b hb heq
    subst heq
    rw [List.mem_append] at hb
    rcases hb with hba | hbl2
    · exact haNotMem a hba rfl
    · exact hDisj a List.mem_cons_self hbl2

private theorem nodup_flatMap_of_disjoint {α β : Type} {xs : List α} {f : α → List β}
    (hxs : xs.Nodup)
    (hf : ∀ a ∈ xs, (f a).Nodup)
    (hDisj : xs.Pairwise (fun a₁ a₂ => ∀ y, y ∈ f a₁ → y ∈ f a₂ → False)) :
    (xs.flatMap f).Nodup := by
  induction hxs with
  | nil => exact List.Pairwise.nil
  | @cons a as _ _ ih =>
    rcases List.pairwise_cons.mp hDisj with ⟨hHeadDisj, hTailDisj⟩
    simp only [List.flatMap_cons]
    refine nodup_append_of_disjoint (hf a List.mem_cons_self)
      (ih (fun x hx => hf x (List.mem_cons_of_mem a hx)) hTailDisj) ?_
    intro y hy1 hy2
    rw [List.mem_flatMap] at hy2
    rcases hy2 with ⟨a₂, ha₂, hya₂⟩
    exact hHeadDisj a₂ ha₂ y hy1 hya₂

private theorem nodup_map_of_injective {α β : Type} {f : α → β}
    (hInj : ∀ x y, f x = f y → x = y) {xs : List α} (hnd : xs.Nodup) :
    (xs.map f).Nodup := by
  induction hnd with
  | nil => exact List.Pairwise.nil
  | @cons a as haNotMem _ ih =>
    simp only [List.map_cons]
    refine List.Pairwise.cons ?_ ih
    intro b hb heq
    rw [List.mem_map] at hb
    rcases hb with ⟨a', ha', rfl⟩
    exact haNotMem a' ha' (hInj a a' heq)

private theorem enumFrontierAntichains_spec (h : Nat) :
    ∀ L, (enumFrontierAntichains h L).Nodup ∧
      ∀ c ∈ enumFrontierAntichains h L, c.paths.length = L ∧ c.WithinHeight h := by
  induction h with
  | zero =>
    intro L
    unfold enumFrontierAntichains
    by_cases hL : L == 1
    · simp only [hL, ↓reduceIte]
      have hEq : L = 1 := LawfulBEq.eq_of_beq hL
      subst hEq
      refine ⟨List.Pairwise.cons (fun _ hm => nomatch hm) List.Pairwise.nil, ?_⟩
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨rfl, trivial⟩
    · simp [hL]
  | succ h ih =>
    intro L
    unfold enumFrontierAntichains
    by_cases h0 : L == 0
    · simp [h0]
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : L == 1
      · simp only [h1, ↓reduceIte]
        have hEq : L = 1 := LawfulBEq.eq_of_beq h1
        subst hEq
        refine ⟨List.Pairwise.cons (fun _ hm => nomatch hm) List.Pairwise.nil, ?_⟩
        intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨rfl, trivial⟩
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · apply nodup_flatMap_of_disjoint (Constructive.nodup_range _)
          · intro k _
            apply nodup_flatMap_of_disjoint (ih (k + 1)).1
            · intro lc _
              exact nodup_map_of_injective (fun _ _ heq => by injection heq) (ih (L - (k + 1))).1
            · apply List.Pairwise.imp _ (ih (k + 1)).1
              intro lc1 lc2 hne x hx1 hx2
              rw [List.mem_map] at hx1 hx2
              rcases hx1 with ⟨rc1, _, rfl⟩
              rcases hx2 with ⟨rc2, _, heq⟩
              injection heq with hl _
              exact hne hl.symm
          · apply List.Pairwise.imp _ (Constructive.nodup_range _)
            intro k1 k2 hkne x hx1 hx2
            rw [List.mem_flatMap] at hx1 hx2
            rcases hx1 with ⟨lc1, hlc1, hrc1⟩
            rcases hx2 with ⟨lc2, hlc2, hrc2⟩
            rw [List.mem_map] at hrc1 hrc2
            rcases hrc1 with ⟨rc1, _, rfl⟩
            rcases hrc2 with ⟨rc2, _, heq⟩
            injection heq with hl _
            rw [hl] at hlc2
            have hl1 := ((ih (k1 + 1)).2 lc1 hlc1).1
            have hl2 := ((ih (k2 + 1)).2 lc1 hlc2).1
            omega
        · intro c hc
          rw [List.mem_flatMap] at hc
          rcases hc with ⟨k, hk, hc1⟩
          rw [List.mem_range] at hk
          rw [List.mem_flatMap] at hc1
          rcases hc1 with ⟨lc, hlc, hrc⟩
          rw [List.mem_map] at hrc
          rcases hrc with ⟨rc, hrcMem, rfl⟩
          obtain ⟨hlLen, hlH⟩ := (ih (k + 1)).2 lc hlc
          obtain ⟨hrLen, hrH⟩ := (ih (L - (k + 1))).2 rc hrcMem
          refine ⟨?_, hlH, hrH⟩
          unfold FrontierAntichain.paths
          rw [List.length_append, List.length_map, List.length_map, hlLen, hrLen]
          omega

private theorem enumSumChains_spec (w L : Nat) :
    ∀ S, (enumSumChains w L S).Nodup ∧
      ∀ xs ∈ enumSumChains w L S, xs.length = L ∧ xs.foldr (· + ·) 0 = S ∧ (∀ a ∈ xs, a < w) := by
  induction L with
  | zero =>
    intro S
    unfold enumSumChains
    by_cases hS : S == 0
    · simp only [hS, ↓reduceIte]
      have hEq : S = 0 := LawfulBEq.eq_of_beq hS
      subst hEq
      refine ⟨List.Pairwise.cons (fun _ hm => nomatch hm) List.Pairwise.nil, ?_⟩
      intro xs hxs
      simp only [List.mem_singleton] at hxs
      subst hxs
      exact ⟨rfl, rfl, fun _ hm => nomatch hm⟩
    · simp [hS]
  | succ L ih =>
    intro S
    unfold enumSumChains
    refine ⟨?_, ?_⟩
    · apply nodup_flatMap_of_disjoint (Constructive.nodup_range _)
      · intro step _
        exact nodup_map_of_injective (fun _ _ heq => by injection heq) (ih (S - step)).1
      · apply List.Pairwise.imp _ (Constructive.nodup_range _)
        intro s1 s2 hsne x hx1 hx2
        rw [List.mem_map] at hx1 hx2
        rcases hx1 with ⟨t1, _, rfl⟩
        rcases hx2 with ⟨t2, _, heq⟩
        injection heq with hhead _
        exact hsne hhead.symm
    · intro xs hxs
      rw [List.mem_flatMap] at hxs
      rcases hxs with ⟨step, hstep, htail⟩
      rw [List.mem_range] at hstep
      rw [List.mem_map] at htail
      rcases htail with ⟨rest, hrest, rfl⟩
      obtain ⟨hrLen, hrSum, hrLt⟩ := (ih (S - step)).2 rest hrest
      have hMinW : Nat.min w (S + 1) ≤ w := Nat.min_le_left w (S + 1)
      have hMinS : Nat.min w (S + 1) ≤ S + 1 := Nat.min_le_right w (S + 1)
      have hStepW : step < w := by omega
      have hStepLeS : step ≤ S := by omega
      refine ⟨by simp [hrLen], ?_, ?_⟩
      · simp only [List.foldr_cons, hrSum]
        omega
      · intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | hmem
        · exact hStepW
        · exact hrLt a hmem

private theorem enumDecoratedFrontiers_nodup (h w L S : Nat) :
    (enumDecoratedFrontiers h w L S).Nodup := by
  unfold enumDecoratedFrontiers
  apply nodup_flatMap_of_disjoint (enumFrontierAntichains_spec h L).1
  · intro fc _
    exact nodup_map_of_injective (fun _ _ heq => by injection heq) (enumSumChains_spec w L S).1
  · apply List.Pairwise.imp _ (enumFrontierAntichains_spec h L).1
    intro fc1 fc2 hne x hx1 hx2
    rw [List.mem_map] at hx1 hx2
    rcases hx1 with ⟨ch1, _, rfl⟩
    rcases hx2 with ⟨ch2, _, heq⟩
    injection heq with hfc _
    exact hne hfc.symm

private theorem idxOf_getElem_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs : List α}, xs.Nodup → ∀ (i : Nat) (hi : i < xs.length), xs.idxOf xs[i] = i
  | [], _, i, hi => nomatch hi
  | x :: xs, _, 0, _ => by simp [List.idxOf_cons_self]
  | x :: xs, hnd, i + 1, hi => by
    rcases List.nodup_cons.mp hnd with ⟨hxNotMem, hndTail⟩
    have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
    have hNe : (x == xs[i]) = false := by
      by_cases hEq : x == xs[i]
      · exfalso
        have : x = xs[i] := LawfulBEq.eq_of_beq hEq
        subst this
        exact hxNotMem (List.getElem_mem hi')
      · simp [hEq]
    simp [List.getElem_cons_succ, List.idxOf_cons, hNe, idxOf_getElem_of_nodup hndTail i hi']

/-- **Theorem 1 (`frontierSumFts_rank_unrank_bijection`)**:
    `frontierSumRank` and `frontierSumUnrank` form an exact two-sided bijection between
    `[0, |(enumDecoratedFrontiers h w L S)|)` and valid decorated $(L, S)$ antichain frontiers,
    and every unranked configuration satisfies prefix-free antichain frontiers + exact chain sum $S$. -/
theorem frontierSumFts_rank_unrank_bijection (h w L S : Nat) :
    (∀ idx < (enumDecoratedFrontiers h w L S).length,
      ∃ cfg,
        frontierSumUnrank h w L S idx = some cfg ∧
        frontierSumRank h w L S cfg = some idx ∧
        IsPrefixFreeAntichain cfg.1.paths ∧
        cfg.1.paths.length = L ∧
        cfg.1.WithinHeight h ∧
        cfg.2.length = L ∧
        cfg.2.foldr (· + ·) 0 = S ∧
        (∀ a ∈ cfg.2, a < w)) ∧
    (∀ cfg ∈ enumDecoratedFrontiers h w L S,
      ∃ idx < (enumDecoratedFrontiers h w L S).length,
        frontierSumRank h w L S cfg = some idx ∧
        frontierSumUnrank h w L S idx = some cfg) := by
  have hnd := enumDecoratedFrontiers_nodup h w L S
  refine ⟨?_, ?_⟩
  · intro idx hlt
    let cfg := (enumDecoratedFrontiers h w L S)[idx]
    have hMem : cfg ∈ enumDecoratedFrontiers h w L S := List.getElem_mem hlt
    unfold enumDecoratedFrontiers at hMem
    rw [List.mem_flatMap] at hMem
    rcases hMem with ⟨fc, hfc, hch⟩
    rw [List.mem_map] at hch
    rcases hch with ⟨ch, hchMem, hEqCfg⟩
    obtain ⟨hfcLen, hfcH⟩ := (enumFrontierAntichains_spec h L).2 fc hfc
    obtain ⟨hchLen, hchSum, hchLt⟩ := (enumSumChains_spec w L S).2 ch hchMem
    refine ⟨cfg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold frontierSumUnrank
      exact List.getElem?_eq_getElem hlt
    · unfold frontierSumRank
      have hIdx : (enumDecoratedFrontiers h w L S).idxOf cfg = idx :=
        idxOf_getElem_of_nodup hnd idx hlt
      simp [cfg, hIdx, hlt]
    · rw [← hEqCfg]; exact frontierAntichain_paths_prefixFree fc
    · rw [← hEqCfg]; exact hfcLen
    · rw [← hEqCfg]; exact hfcH
    · rw [← hEqCfg]; exact hchLen
    · rw [← hEqCfg]; exact hchSum
    · rw [← hEqCfg]; exact hchLt
  · intro cfg hMem
    obtain ⟨idx, hlt, hGet⟩ := List.getElem_of_mem hMem
    refine ⟨idx, hlt, ?_, ?_⟩
    · unfold frontierSumRank
      subst hGet
      have hIdx := idxOf_getElem_of_nodup hnd idx hlt
      simp [hIdx, hlt]
    · unfold frontierSumUnrank
      rw [List.getElem?_eq_getElem hlt, hGet]

/-! ## 2. Beaver depth of shared circuit expressions -/

/-- Repeated subexpressions denote shared wires of a circuit DAG.
Squaring in GF(2^128) is linear over F_2. Opened Merkle parents
are plaintext operations and introduce no Beaver multiplication. -/
inductive MpcExpr where
  | pubInput : Nat → MpcExpr
  | secretShare : Nat → MpcExpr
  | xorLin : MpcExpr → MpcExpr → MpcExpr
  | frobeniusSqGf2_128 : MpcExpr → MpcExpr
  | beaverMul : MpcExpr → MpcExpr → MpcExpr
  | openAndPlainMerkleParent : MpcExpr → MpcExpr → MpcExpr

def MpcExpr.beaverDepth : MpcExpr → Nat
  | .pubInput _ | .secretShare _ => 0
  | .xorLin a b => Nat.max a.beaverDepth b.beaverDepth
  | .frobeniusSqGf2_128 a => a.beaverDepth
  | .beaverMul a b => Nat.max a.beaverDepth b.beaverDepth + 1
  | .openAndPlainMerkleParent a b => Nat.max a.beaverDepth b.beaverDepth

/-- Each cube round has one nonlinear layer, with a public round constant. -/
def cubePrfAst : Nat → MpcExpr → MpcExpr
  | 0, x => x
  | r + 1, x =>
    let y := MpcExpr.xorLin (cubePrfAst r x) (.pubInput r)
    .beaverMul y (.frobeniusSqGf2_128 y)

def parallelChainAst (rounds : Nat) : Nat → MpcExpr → MpcExpr
  | 0, x => x
  | w + 1, x => cubePrfAst rounds (parallelChainAst rounds w x)

/-- Distinct public path labels model parallel leaves; depth ignores their values. -/
def plainMerkleAst (leaf : Nat → MpcExpr) : Nat → Nat → MpcExpr
  | 0, label => leaf label
  | h + 1, label => .openAndPlainMerkleParent
      (plainMerkleAst leaf h (2 * label)) (plainMerkleAst leaf h (2 * label + 1))

def buildParallelSeededAst (rounds h w : Nat) : MpcExpr :=
  plainMerkleAst (fun label => parallelChainAst rounds w
    (cubePrfAst rounds (.xorLin (.secretShare 0) (.pubInput label)))) h 0

def internalChainedAst (rounds w : Nat) : Nat → MpcExpr → MpcExpr
  | 0, x => x
  | h + 1, x =>
    let parent := internalChainedAst rounds w h x
    .xorLin (parallelChainAst rounds w (.xorLin parent (.pubInput 0)))
      (parallelChainAst rounds w (.xorLin parent (.pubInput 1)))

def buildInternalChainedAst (rounds h w : Nat) : MpcExpr :=
  internalChainedAst rounds w h (.secretShare 0)

private theorem cubePrfAst_depth (rounds : Nat) (x : MpcExpr) :
    (cubePrfAst rounds x).beaverDepth = x.beaverDepth + rounds := by
  induction rounds with
  | zero => simp [cubePrfAst]
  | succ r ih => simp [cubePrfAst, MpcExpr.beaverDepth, ih, Nat.add_assoc]

private theorem parallelChainAst_depth (rounds w : Nat) (x : MpcExpr) :
    (parallelChainAst rounds w x).beaverDepth = x.beaverDepth + rounds * w := by
  induction w with
  | zero => simp [parallelChainAst]
  | succ w ih =>
    simp [parallelChainAst, cubePrfAst_depth, ih, Nat.mul_succ, Nat.add_assoc]

private theorem plainMerkleAst_depth (leaf : Nat → MpcExpr) (d : Nat)
    (hd : ∀ label, (leaf label).beaverDepth = d) (h label : Nat) :
    (plainMerkleAst leaf h label).beaverDepth = d := by
  induction h generalizing label with
  | zero => exact hd label
  | succ h ih => simp [plainMerkleAst, MpcExpr.beaverDepth, ih]

theorem buildParallelSeededAst_depth (rounds h w : Nat) :
    (buildParallelSeededAst rounds h w).beaverDepth = rounds * (1 + w) := by
  apply plainMerkleAst_depth
  intro label
  simp [parallelChainAst_depth, cubePrfAst_depth, MpcExpr.beaverDepth,
    Nat.mul_add]

private theorem internalChainedAst_depth (rounds w h : Nat) (x : MpcExpr) :
    (internalChainedAst rounds w h x).beaverDepth = x.beaverDepth + rounds * h * w := by
  induction h with
  | zero => simp [internalChainedAst]
  | succ h ih =>
    simp [internalChainedAst, MpcExpr.beaverDepth, parallelChainAst_depth, ih,
      Nat.mul_succ, Nat.add_mul, Nat.add_assoc]

theorem buildInternalChainedAst_depth (rounds h w : Nat) :
    (buildInternalChainedAst rounds h w).beaverDepth = rounds * h * w := by
  simp [buildInternalChainedAst, internalChainedAst_depth, MpcExpr.beaverDepth]

/-- Structural depth, height invariance, strict separation, and the 82-round profile. -/
theorem parallelSeededFts_mpc_depth_independent_of_height :
    (∀ rounds h₁ h₂ w,
      (buildParallelSeededAst rounds h₁ w).beaverDepth = rounds * (1 + w) ∧
      (buildParallelSeededAst rounds h₁ w).beaverDepth =
        (buildParallelSeededAst rounds h₂ w).beaverDepth) ∧
    (∀ rounds h w, 1 ≤ rounds → 2 ≤ h → 2 ≤ w →
      (buildParallelSeededAst rounds h w).beaverDepth <
        (buildInternalChainedAst rounds h w).beaverDepth) ∧
    ((buildParallelSeededAst 82 15 5).beaverDepth = 492 ∧
      (buildInternalChainedAst 82 15 5).beaverDepth = 6150) := by
  refine ⟨?_, ?_, ?_⟩
  · intro rounds h₁ h₂ w
    simp only [buildParallelSeededAst_depth, and_self]
  · intro rounds h w hr hh hw
    rw [buildParallelSeededAst_depth, buildInternalChainedAst_depth, Nat.mul_assoc]
    have h2w := Nat.mul_le_mul_right w hh
    have hlt : 1 + w < h * w := by omega
    exact Nat.mul_lt_mul_of_pos_left hlt (by omega)
  · rw [buildParallelSeededAst_depth, buildInternalChainedAst_depth]
    decide

/-! ## 3. Strict `Bech32m` (`0x2bc830a3`) vs Legacy `Bech32` (`1`) & GF(32) BCH Syndrome Soundness -/

/-- Legacy BIP-173 `Bech32` constant `1` (vulnerable to `'p'` zero-insertion length mutability). -/
@[expose] def BECH32_LEGACY_CONST : BitVec 30 := 1#30

/-- BIP-350 `Bech32m` constant `0x2bc830a3`. -/
@[expose] def BECH32M_CONST : BitVec 30 := 0x2bc830a3#30

/-- Exact 30-bit `Bech32`/`Bech32m` degree-6 BCH generator feedback over $\mathbb{F}_{32}$. -/
def bech32GenFeedback (top : BitVec 5) : BitVec 30 :=
  let g0 := if top.getLsbD 0 then 0x3b6a57b2#30 else 0#30
  let g1 := if top.getLsbD 1 then 0x26508e6d#30 else 0#30
  let g2 := if top.getLsbD 2 then 0x1ea119fa#30 else 0#30
  let g3 := if top.getLsbD 3 then 0x3d4233dd#30 else 0#30
  let g4 := if top.getLsbD 4 then 0x2a1462b3#30 else 0#30
  g0 ^^^ g1 ^^^ g2 ^^^ g3 ^^^ g4

/-- Single 5-bit character polymod step. -/
def bech32PolymodStep (chk : BitVec 30) (v : BitVec 5) : BitVec 30 :=
  ((chk <<< 5) ^^^ v.zeroExtend 30) ^^^ bech32GenFeedback (chk.extractLsb' 25 5)

/-- Polymod fold over an arbitrary list of 5-bit symbols from initial accumulator `chk`. -/
def bech32PolymodFrom (chk : BitVec 30) : List (BitVec 5) → BitVec 30
  | [] => chk
  | v :: vs => bech32PolymodFrom (bech32PolymodStep chk v) vs

/-- Strict `Bech32m` checksum predicate (`bech32PolymodFrom 1#30 cw == 0x2bc830a3#30`). -/
@[expose] def bech32mValid (cw : List (BitVec 5)) : Prop :=
  bech32PolymodFrom 1#30 cw = BECH32M_CONST

/-- Legacy `Bech32` checksum predicate (`bech32PolymodFrom 1#30 cw == 1#30`). -/
@[expose] def bech32LegacyValid (cw : List (BitVec 5)) : Prop :=
  bech32PolymodFrom 1#30 cw = BECH32_LEGACY_CONST

private theorem cond_xor_const (b1 b2 : Bool) (G : BitVec 30) :
    (if (b1 != b2) then G else 0#30) = (if b1 then G else 0#30) ^^^ (if b2 then G else 0#30) := by
  cases b1 <;> cases b2 <;> simp

private theorem bech32GenFeedback_xor (a b : BitVec 5) :
    bech32GenFeedback (a ^^^ b) = bech32GenFeedback a ^^^ bech32GenFeedback b := by
  unfold bech32GenFeedback
  simp only [BitVec.getLsbD_xor, cond_xor_const]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases (if a.getLsbD 0 then 0x3b6a57b2#30 else 0#30).getLsbD i <;>
  cases (if b.getLsbD 0 then 0x3b6a57b2#30 else 0#30).getLsbD i <;>
  cases (if a.getLsbD 1 then 0x26508e6d#30 else 0#30).getLsbD i <;>
  cases (if b.getLsbD 1 then 0x26508e6d#30 else 0#30).getLsbD i <;>
  cases (if a.getLsbD 2 then 0x1ea119fa#30 else 0#30).getLsbD i <;>
  cases (if b.getLsbD 2 then 0x1ea119fa#30 else 0#30).getLsbD i <;>
  cases (if a.getLsbD 3 then 0x3d4233dd#30 else 0#30).getLsbD i <;>
  cases (if b.getLsbD 3 then 0x3d4233dd#30 else 0#30).getLsbD i <;>
  cases (if a.getLsbD 4 then 0x2a1462b3#30 else 0#30).getLsbD i <;>
  cases (if b.getLsbD 4 then 0x2a1462b3#30 else 0#30).getLsbD i <;> rfl

private theorem extract25_xor (c1 c2 : BitVec 30) :
    (c1 ^^^ c2).extractLsb' 25 5 = c1.extractLsb' 25 5 ^^^ c2.extractLsb' 25 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

private theorem shiftLeft5_xor (c1 c2 : BitVec 30) :
    (c1 ^^^ c2) <<< 5 = (c1 <<< 5) ^^^ (c2 <<< 5) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h5 : i < 5 <;> simp [hi, h5]

private theorem zeroExtend30_xor (v1 v2 : BitVec 5) :
    (v1 ^^^ v2).zeroExtend 30 = v1.zeroExtend 30 ^^^ v2.zeroExtend 30 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h5 : i < 5 <;> simp [hi, h5]

private theorem bech32PolymodStep_xor (c1 c2 : BitVec 30) (v1 v2 : BitVec 5) :
    bech32PolymodStep (c1 ^^^ c2) (v1 ^^^ v2) =
      bech32PolymodStep c1 v1 ^^^ bech32PolymodStep c2 v2 := by
  unfold bech32PolymodStep
  rw [shiftLeft5_xor, zeroExtend30_xor, extract25_xor, bech32GenFeedback_xor]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases (c1 <<< 5).getLsbD i <;> cases (c2 <<< 5).getLsbD i <;>
  cases (v1.zeroExtend 30).getLsbD i <;> cases (v2.zeroExtend 30).getLsbD i <;>
  cases (bech32GenFeedback (c1.extractLsb' 25 5)).getLsbD i <;>
  cases (bech32GenFeedback (c2.extractLsb' 25 5)).getLsbD i <;> rfl

/-- Pointwise XOR of two 5-bit symbol lists. -/
def zipXor5 : List (BitVec 5) → List (BitVec 5) → List (BitVec 5)
  | x :: xs, y :: ys => (x ^^^ y) :: zipXor5 xs ys
  | _, _ => []

private theorem bech32PolymodFrom_xor :
    ∀ (xs ys : List (BitVec 5)), xs.length = ys.length →
      ∀ (c1 c2 : BitVec 30),
        bech32PolymodFrom (c1 ^^^ c2) (zipXor5 xs ys) =
          bech32PolymodFrom c1 xs ^^^ bech32PolymodFrom c2 ys
  | [], [], _, c1, c2 => rfl
  | x :: xs, y :: ys, hlen, c1, c2 => by
    simp only [List.length_cons] at hlen
    have htail : xs.length = ys.length := by omega
    unfold zipXor5 bech32PolymodFrom
    rw [bech32PolymodStep_xor]
    exact bech32PolymodFrom_xor xs ys htail _ _

/-- The 5 low-order bits `{0x12, 0x0d, 0x1a, 0x1d, 0x13}` of the Bech32 generator are linearly
    independent over $\mathbb{F}_2^5$: `extractLsb' 0 5 (bech32GenFeedback top) = 0#5 → top = 0#5`. -/
private theorem bech32GenFeedback_low5_injective :
    ∀ (top : BitVec 5), (bech32GenFeedback top).extractLsb' 0 5 = 0#5 → top = 0#5 := by
  decide

/-- Homogeneous step `v = 0#5` has trivial kernel on 30-bit syndromes! -/
private theorem bech32PolymodStep_zero_ne_zero {chk : BitVec 30} (hchk : chk ≠ 0#30) :
    bech32PolymodStep chk 0#5 ≠ 0#30 := by
  intro hEq
  have hLow : (bech32GenFeedback (chk.extractLsb' 25 5)).extractLsb' 0 5 = 0#5 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hBit : (bech32PolymodStep chk 0#5).getLsbD i = false := by rw [hEq]; simp
    unfold bech32PolymodStep at hBit
    have hi30 : i < 30 := by omega
    simp [hi30, hi] at hBit ⊢
    exact hBit
  have hTop0 : chk.extractLsb' 25 5 = 0#5 := bech32GenFeedback_low5_injective _ hLow
  have hGen0 : bech32GenFeedback (chk.extractLsb' 25 5) = 0#30 := by
    rw [hTop0]; rfl
  apply hchk
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases hj25 : j < 25
  · have hShift : (bech32PolymodStep chk 0#5).getLsbD (j + 5) = false := by
      rw [hEq]; simp
    unfold bech32PolymodStep at hShift
    rw [hGen0] at hShift
    have hj5_30 : j + 5 < 30 := by omega
    have hNotLt5 : ¬ (j + 5 < 5) := by omega
    simp [hj5_30, hNotLt5, hj] at hShift ⊢
    exact hShift
  · have hk : j - 25 < 5 := by omega
    have hTopBit : (chk.extractLsb' 25 5).getLsbD (j - 25) = false := by rw [hTop0]; simp
    simp [hk] at hTopBit
    have hIdx : 25 + (j - 25) = j := by omega
    rw [hIdx] at hTopBit
    simp [hj] at hTopBit ⊢
    exact hTopBit

private theorem bech32PolymodFrom_zeros_ne_zero :
    ∀ (k : Nat) {chk : BitVec 30}, chk ≠ 0#30 →
      bech32PolymodFrom chk (List.replicate k 0#5) ≠ 0#30
  | 0, _, hchk => hchk
  | k + 1, _, hchk =>
    bech32PolymodFrom_zeros_ne_zero k (bech32PolymodStep_zero_ne_zero hchk)

private theorem bech32PolymodFrom_zero_replicate (k : Nat) :
    bech32PolymodFrom 0#30 (List.replicate k 0#5) = 0#30 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold List.replicate bech32PolymodFrom
    have h0 : bech32PolymodStep 0#30 0#5 = 0#30 := rfl
    rw [h0]
    exact ih

/-- Single-symbol error vector of length `n` with `delta` at `pos` and `0#5` elsewhere. -/
def singleSubstErrorVec (n pos : Nat) (delta : BitVec 5) : List (BitVec 5) :=
  List.replicate pos 0#5 ++ (delta :: List.replicate (n - 1 - pos) 0#5)

private theorem bech32PolymodFrom_singleSubstError_ne_zero
    {n pos : Nat} (hpos : pos < n) {delta : BitVec 5} (hdelta : delta ≠ 0#5) :
    bech32PolymodFrom 0#30 (singleSubstErrorVec n pos delta) ≠ 0#30 := by
  unfold singleSubstErrorVec
  have hSplit : ∀ (pre suf : List (BitVec 5)) (c : BitVec 30),
      bech32PolymodFrom c (pre ++ suf) = bech32PolymodFrom (bech32PolymodFrom c pre) suf := by
    intro pre suf c
    induction pre generalizing c with
    | nil => rfl
    | cons a as ih => exact ih (bech32PolymodStep c a)
  rw [hSplit, bech32PolymodFrom_zero_replicate]
  unfold bech32PolymodFrom
  have hStepDelta : bech32PolymodStep 0#30 delta = delta.zeroExtend 30 := by
    unfold bech32PolymodStep
    have hg : bech32GenFeedback ((0#30).extractLsb' 25 5) = 0#30 := rfl
    rw [hg]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  rw [hStepDelta]
  have hNz : delta.zeroExtend 30 ≠ 0#30 := by
    intro hz
    apply hdelta
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hbi := congrArg (fun b => b.getLsbD i) hz
    have hi30 : i < 30 := by omega
    simp [hi30, hi] at hbi ⊢
    exact hbi
  let _ := hpos
  exact bech32PolymodFrom_zeros_ne_zero (n - 1 - pos) hNz

/-- **Theorem 3 (`bech32m_rejects_bech32_and_detects_single_subst`)**:
    1. `BECH32M_CONST ≠ BECH32_LEGACY_CONST`, so every legacy `Bech32` codeword is unconditionally
       rejected by `bech32mValid`;
    2. For **every** valid `Bech32m` codeword `cw` of **any** length `n`, any index `pos < cw.length`,
       and any non-zero 5-bit substitution error `delta ≠ 0#5`, the corrupted codeword
       `zipXor5 cw (singleSubstErrorVec cw.length pos delta)` is unconditionally rejected! -/
theorem bech32m_rejects_bech32_and_detects_single_subst :
    (BECH32M_CONST ≠ BECH32_LEGACY_CONST) ∧
    (∀ cw : List (BitVec 5), bech32LegacyValid cw → ¬ bech32mValid cw) ∧
    (∀ (cw : List (BitVec 5)) (pos : Nat) (delta : BitVec 5),
      bech32mValid cw →
      pos < cw.length →
      delta ≠ 0#5 →
      ¬ bech32mValid (zipXor5 cw (singleSubstErrorVec cw.length pos delta))) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro cw hLeg hM
    unfold bech32LegacyValid at hLeg
    unfold bech32mValid at hM
    rw [hLeg] at hM
    revert hM; decide
  · intro cw pos delta hValid hPos hDelta hMutValid
    unfold bech32mValid at hValid hMutValid
    have hErrLen : cw.length = (singleSubstErrorVec cw.length pos delta).length := by
      unfold singleSubstErrorVec
      rw [List.length_append, List.length_replicate, List.length_cons, List.length_replicate]
      omega
    have hInit : (1#30 : BitVec 30) = 1#30 ^^^ 0#30 := by decide
    rw [hInit, bech32PolymodFrom_xor cw _ hErrLen 1#30 0#30, hValid] at hMutValid
    have hSynZero : bech32PolymodFrom 0#30 (singleSubstErrorVec cw.length pos delta) = 0#30 := by
      have h1 := congrArg (fun x => BECH32M_CONST ^^^ x) hMutValid
      have hSelf : ∀ (a b : BitVec 30), a ^^^ (a ^^^ b) = b := by
        intro a b
        apply BitVec.eq_of_getLsbD_eq
        intro i _; simp
      have hSelf0 : BECH32M_CONST ^^^ BECH32M_CONST = 0#30 := by decide
      rw [hSelf, hSelf0] at h1
      exact h1
    exact bech32PolymodFrom_singleSubstError_ne_zero hPos hDelta hSynZero

/-! ## 4. `PiBlindVc` Unlinkable Blinding Bijection & Selective-Disclosure Soundness -/

/-- 4-limb Goldilocks 256-bit credential blinding carrier. -/
abbrev VcBlind4 := Goldilocks × Goldilocks × Goldilocks × Goldilocks

/-- Per-presentation credential re-blinding `b ⊕ δ` over `Goldilocks^4`. -/
def vcReblind (b delta : VcBlind4) : VcBlind4 :=
  (Goldilocks.add b.1 delta.1,
   Goldilocks.add b.2.1 delta.2.1,
   Goldilocks.add b.2.2.1 delta.2.2.1,
   Goldilocks.add b.2.2.2 delta.2.2.2)

/-- Exact inverse `y ⊖ b` recovering the per-presentation blinding offset `δ`. -/
def vcUnreblind (y b : VcBlind4) : VcBlind4 :=
  (Goldilocks.sub y.1 b.1,
   Goldilocks.sub y.2.1 b.2.1,
   Goldilocks.sub y.2.2.1 b.2.2.1,
   Goldilocks.sub y.2.2.2 b.2.2.2)

private theorem gl_sub_add_cancel_left (b d : Goldilocks) :
    Goldilocks.sub (Goldilocks.add b d) b = d := by
  change CommRingOps.sub (CommRingOps.add b d) b = d
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_comm b d, LawfulCommRing.add_assoc,
      LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

private theorem gl_add_sub_cancel (y b : Goldilocks) :
    Goldilocks.add b (Goldilocks.sub y b) = y :=
  LawfulCommRing.add_sub_cancel_left b y

/-- Selective-disclosure check over `(index, expectedValue)` pairs against an attribute list. -/
def matchesDisclosed (attrs : List Goldilocks) (disclosed : List (Nat × Goldilocks)) : Prop :=
  ∀ p ∈ disclosed, attrs[p.1]? = some p.2

/-- Canonical low/high 32-bit limbs, each strictly below the field modulus. -/
def encodeU64Limbs2 (x : UInt64) : Goldilocks × Goldilocks :=
  (Goldilocks.ofNat (x.toNat % 4294967296), Goldilocks.ofNat (x.toNat / 4294967296))

theorem encodeU64Limbs2_injective (x y : UInt64)
    (h : encodeU64Limbs2 x = encodeU64Limbs2 y) : x = y := by
  have hx := x.toNat_lt_size
  have hy := y.toNat_lt_size
  have hxl : x.toNat % 4294967296 < goldilocksPrime := by
    have := Nat.mod_lt x.toNat (by decide : 0 < 4294967296)
    have hp : 4294967296 < goldilocksPrime := by decide
    omega
  have hyl : y.toNat % 4294967296 < goldilocksPrime := by
    have := Nat.mod_lt y.toNat (by decide : 0 < 4294967296)
    have hp : 4294967296 < goldilocksPrime := by decide
    omega
  have hxh : x.toNat / 4294967296 < goldilocksPrime := by
    have hp : 4294967296 < goldilocksPrime := by decide
    change x.toNat < 18446744073709551616 at hx
    omega
  have hyh : y.toNat / 4294967296 < goldilocksPrime := by
    have hp : 4294967296 < goldilocksPrime := by decide
    change y.toNat < 18446744073709551616 at hy
    omega
  have hl := congrArg (fun z : Goldilocks × Goldilocks => z.1.val) h
  have hh := congrArg (fun z : Goldilocks × Goldilocks => z.2.val) h
  simp only [encodeU64Limbs2, Goldilocks.ofNat_val,
    Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] at hl
  simp only [encodeU64Limbs2, Goldilocks.ofNat_val,
    Nat.mod_eq_of_lt hxh, Nat.mod_eq_of_lt hyh] at hh
  apply UInt64.toNat_inj.mp
  omega

/-- Three virtual parties, with cyclic adjacent openings. -/
def nextParty (i : Fin 3) : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

private theorem nextParty_zero : nextParty 0 = 1 := rfl
private theorem nextParty_one : nextParty 1 = 2 := rfl
private theorem nextParty_two : nextParty 2 = 0 := rfl

def sumShares3 (s : Fin 3 → Goldilocks) : Goldilocks :=
  CommRingOps.add (s 0) (CommRingOps.add (s 1) (s 2))

private theorem gl_add_left_comm (a b c : Goldilocks) :
    CommRingOps.add a (CommRingOps.add b c) =
      CommRingOps.add b (CommRingOps.add a c) := by
  rw [← LawfulCommRing.add_assoc, LawfulCommRing.add_comm a b,
    LawfulCommRing.add_assoc]

private theorem sumShares3_add (a b : Fin 3 → Goldilocks) :
    sumShares3 (fun i => CommRingOps.add (a i) (b i)) =
      CommRingOps.add (sumShares3 a) (sumShares3 b) := by
  simp only [sumShares3, LawfulCommRing.add_assoc, gl_add_left_comm]

/-- Arithmetic ZKBoo multiplication: each party uses its own and its neighbor's
wires and tapes. All nine product terms occur exactly once in the sum. -/
def zkBooMulShare (a b tape : Fin 3 → Goldilocks) (i : Fin 3) : Goldilocks :=
  CommRingOps.add
    (CommRingOps.add (CommRingOps.mul (a i) (b i))
      (CommRingOps.add (CommRingOps.mul (a i) (b (nextParty i)))
        (CommRingOps.mul (a (nextParty i)) (b i))))
    (CommRingOps.sub (tape i) (tape (nextParty i)))

private theorem sumShares3_tape (tape : Fin 3 → Goldilocks) :
    sumShares3 (fun i => CommRingOps.sub (tape i) (tape (nextParty i))) =
      CommRingOps.zero := by
  change CommRingOps.add (CommRingOps.sub (tape 0) (tape 1))
    (CommRingOps.add (CommRingOps.sub (tape 1) (tape 2))
      (CommRingOps.sub (tape 2) (tape 0))) = CommRingOps.zero
  simp only [LawfulCommRing.sub_eq_add_neg]
  calc
    _ = CommRingOps.add (CommRingOps.add (tape 0) (CommRingOps.neg (tape 0)))
        (CommRingOps.add (CommRingOps.add (tape 1) (CommRingOps.neg (tape 1)))
          (CommRingOps.add (tape 2) (CommRingOps.neg (tape 2)))) := by
      simp only [LawfulCommRing.add_assoc, LawfulCommRing.add_comm, gl_add_left_comm]
    _ = _ := by rw [LawfulCommRing.add_right_neg, LawfulCommRing.add_right_neg,
      LawfulCommRing.add_right_neg, LawfulCommRing.add_zero, LawfulCommRing.add_zero]

private theorem zkBooMulShare_sum (a b tape : Fin 3 → Goldilocks) :
    sumShares3 (zkBooMulShare a b tape) =
      CommRingOps.mul (sumShares3 a) (sumShares3 b) := by
  unfold zkBooMulShare
  rw [sumShares3_add, sumShares3_tape, LawfulCommRing.add_zero]
  simp only [sumShares3, nextParty_zero, nextParty_one, nextParty_two,
    LawfulCommRing.left_distrib,
    LawfulCommRing.right_distrib]
  simp only [LawfulCommRing.add_assoc, LawfulCommRing.add_comm, gl_add_left_comm]

/-- Constructive (`0 Classical.choice`) explicit bijection carrier for hiding/unlinkability proofs. -/
structure CredBijection (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

/-- Full-width 6-limb Goldilocks commitment/scope-tag digest (`> 383` bits, matching `[u64; 6]`
    `compute_vc_poseidon2_commit` and `compute_vc_scope_tag` in `crates/qsag-cred/src/blind_vc.rs`). -/
structure VcDigest6 where
  d0 : Goldilocks
  d1 : Goldilocks
  d2 : Goldilocks
  d3 : Goldilocks
  d4 : Goldilocks
  d5 : Goldilocks
  deriving DecidableEq, Repr

namespace VcDigest6

theorem ext {a b : VcDigest6}
    (h0 : a.d0 = b.d0) (h1 : a.d1 = b.d1) (h2 : a.d2 = b.d2)
    (h3 : a.d3 = b.d3) (h4 : a.d4 = b.d4) (h5 : a.d5 = b.d5) : a = b := by
  cases a; cases b; simp only at *; subst h0 h1 h2 h3 h4 h5; rfl

end VcDigest6

def sumDigest6Shares3 (s : Fin 3 → VcDigest6) : VcDigest6 :=
  { d0 := sumShares3 (fun i => (s i).d0)
    d1 := sumShares3 (fun i => (s i).d1)
    d2 := sumShares3 (fun i => (s i).d2)
    d3 := sumShares3 (fun i => (s i).d3)
    d4 := sumShares3 (fun i => (s i).d4)
    d5 := sumShares3 (fun i => (s i).d5) }

/-- General arithmetic credential circuit with explicit multiplication gate IDs (`gateId : Nat`)
    so per-gate PRG masks expand deterministically from committed per-party `tapeSeed`s. -/
inductive CredCircuit (n : Nat) where
  | attr : Fin n → CredCircuit n
  | blind : Fin 4 → CredCircuit n
  | constant : Goldilocks → CredCircuit n
  | add : CredCircuit n → CredCircuit n → CredCircuit n
  | mul : Nat → CredCircuit n → CredCircuit n → CredCircuit n
  deriving DecidableEq, Repr

/-- Six-limb parallel circuit bundle evaluating a full `VcDigest6` commitment or scope tag. -/
structure CredCircuit6 (n : Nat) where
  c0 : CredCircuit n
  c1 : CredCircuit n
  c2 : CredCircuit n
  c3 : CredCircuit n
  c4 : CredCircuit n
  c5 : CredCircuit n
  deriving DecidableEq, Repr

def blindLimb (b : VcBlind4) (i : Fin 4) : Goldilocks :=
  if i.val = 0 then b.1 else if i.val = 1 then b.2.1
  else if i.val = 2 then b.2.2.1 else b.2.2.2

def evalCommit {n : Nat} (attrs : List Goldilocks) (blind : VcBlind4) :
    CredCircuit n → Goldilocks
  | .attr j => (attrs[j.val]?).getD Goldilocks.zero
  | .blind j => blindLimb blind j
  | .constant c => c
  | .add a b => CommRingOps.add (evalCommit attrs blind a) (evalCommit attrs blind b)
  | .mul _ a b => CommRingOps.mul (evalCommit attrs blind a) (evalCommit attrs blind b)

def evalCommit6 {n : Nat} (attrs : List Goldilocks) (blind : VcBlind4) (cs : CredCircuit6 n) :
    VcDigest6 :=
  { d0 := evalCommit attrs blind cs.c0
    d1 := evalCommit attrs blind cs.c1
    d2 := evalCommit attrs blind cs.c2
    d3 := evalCommit attrs blind cs.c3
    d4 := evalCommit attrs blind cs.c4
    d5 := evalCommit attrs blind cs.c5 }

/-- Complete single-party view committed in Round 1 before Fiat-Shamir challenge derivation:
    binds attribute shares, 4-limb blind share, PRG `tapeSeed`, commitment `salt`, gate wire trace,
    6-limb commitment share, 6-limb scope-tag share, and public-slot output shares. -/
structure PartyCredView (n : Nat) where
  attrShares : List Goldilocks
  blindShare : VcBlind4
  tapeSeed : List UInt8
  salt : List UInt8
  wires : CredCircuit n → Goldilocks
  commitShare : VcDigest6
  scopeShare : VcDigest6
  publicAttrOutputs : Nat → Goldilocks

/-- Pre-challenge committed 3-party ZKBoo credential repetition over full 6-limb commitments,
    deterministic PRG tape expansion, and Round-1 party view commitments (`partyCommits`). -/
structure ZkBooCredTriple where
  attrCount : Nat
  parties : Fin 3 → PartyCredView attrCount
  partyCommits : Fin 3 → List UInt8
  commitCircuits : CredCircuit6 attrCount
  scopeCircuits : CredCircuit6 attrCount
  expectedCommit : VcDigest6
  expectedScopeTag : VcDigest6
  issuerSlots : List (Nat × Goldilocks)
  disclosed : List (Nat × Goldilocks)

def reconAttrs (t : ZkBooCredTriple) : List Goldilocks :=
  List.ofFn (fun j : Fin t.attrCount =>
    sumShares3 (fun i => (((t.parties i).attrShares)[j.val]?).getD Goldilocks.zero))

def reconBlind (t : ZkBooCredTriple) : VcBlind4 :=
  (sumShares3 (fun i => (t.parties i).blindShare.1),
   sumShares3 (fun i => (t.parties i).blindShare.2.1),
   sumShares3 (fun i => (t.parties i).blindShare.2.2.1),
   sumShares3 (fun i => (t.parties i).blindShare.2.2.2))

private theorem reconBlind_limb (t : ZkBooCredTriple) (j : Fin 4) :
    blindLimb (reconBlind t) j = sumShares3 (fun i => blindLimb (t.parties i).blindShare j) := by
  by_cases h0 : j.val = 0 <;> by_cases h1 : j.val = 1 <;>
    by_cases h2 : j.val = 2 <;> simp [blindLimb, reconBlind, h0, h1, h2]

/-- Computable (`0 Classical.choice`, `0 noncomputable`) gate-by-gate verifier for party `i`
    using only party `i` and `nextParty i`'s views and deterministic PRG tape expansion. -/
def checkCredView (expandTape : List UInt8 → Nat → Goldilocks)
    (t : ZkBooCredTriple) : CredCircuit t.attrCount → Fin 3 → Bool
  | .attr j, i =>
    decide ((t.parties i).wires (.attr j) = (((t.parties i).attrShares)[j.val]?).getD Goldilocks.zero)
  | .blind j, i =>
    decide ((t.parties i).wires (.blind j) = blindLimb (t.parties i).blindShare j)
  | .constant c, i =>
    decide ((t.parties i).wires (.constant c) = if i.val = 0 then c else CommRingOps.zero)
  | .add a b, i =>
    checkCredView expandTape t a i &&
    checkCredView expandTape t b i &&
    decide ((t.parties i).wires (.add a b) =
      CommRingOps.add ((t.parties i).wires a) ((t.parties i).wires b))
  | .mul gid a b, i =>
    let wA : Fin 3 → Goldilocks := fun p => (t.parties p).wires a
    let wB : Fin 3 → Goldilocks := fun p => (t.parties p).wires b
    let tape : Fin 3 → Goldilocks := fun p => expandTape (t.parties p).tapeSeed gid
    checkCredView expandTape t a i &&
    checkCredView expandTape t b i &&
    decide ((t.parties i).wires (.mul gid a b) = zkBooMulShare wA wB tape i)

def checkCredView6 (expandTape : List UInt8 → Nat → Goldilocks)
    (t : ZkBooCredTriple) (cs : CredCircuit6 t.attrCount) (i : Fin 3) : Bool :=
  checkCredView expandTape t cs.c0 i &&
  checkCredView expandTape t cs.c1 i &&
  checkCredView expandTape t cs.c2 i &&
  checkCredView expandTape t cs.c3 i &&
  checkCredView expandTape t cs.c4 i &&
  checkCredView expandTape t cs.c5 i

def checkDigest6ShareMatch {n : Nat} (v : PartyCredView n) (cs : CredCircuit6 n)
    (out : VcDigest6) : Bool :=
  decide (out.d0 = v.wires cs.c0) &&
  decide (out.d1 = v.wires cs.c1) &&
  decide (out.d2 = v.wires cs.c2) &&
  decide (out.d3 = v.wires cs.c3) &&
  decide (out.d4 = v.wires cs.c4) &&
  decide (out.d5 = v.wires cs.c5)

def checkPublicSlots (t : ZkBooCredTriple) (slots : List (Nat × Goldilocks)) : Bool :=
  slots.all (fun p =>
    decide (p.1 < t.attrCount) &&
    decide (sumShares3 (fun i => (t.parties i).publicAttrOutputs p.1) = p.2))

def checkOpenedSlots (t : ZkBooCredTriple) (i : Fin 3) (slots : List (Nat × Goldilocks)) : Bool :=
  slots.all (fun p =>
    decide ((t.parties i).publicAttrOutputs p.1 =
      (((t.parties i).attrShares)[p.1]?).getD Goldilocks.zero))

/-- Computable (`Bool`-valued, `0 noncomputable`) 2-of-3 ZKBoo verifier checking:
    (1) Round-1 party view commitments for `chal` and `nextParty chal`,
    (2) PRG-expanded gate replay for all 6 commitment limbs and all 6 scope-tag limbs,
    (3) 6-limb commitment & scope-tag output reconstruction, and
    (4) disclosed/issuer public slot consistency. -/
def checkOpenedPair
    (commitView : (n : Nat) → Fin 3 → PartyCredView n → List UInt8)
    (expandTape : List UInt8 → Nat → Goldilocks)
    (t : ZkBooCredTriple) (chal : Fin 3) : Bool :=
  let next := nextParty chal
  let allSlots := t.disclosed ++ t.issuerSlots
  decide (commitView t.attrCount chal (t.parties chal) = t.partyCommits chal) &&
  decide (commitView t.attrCount next (t.parties next) = t.partyCommits next) &&
  checkCredView6 expandTape t t.commitCircuits chal &&
  checkCredView6 expandTape t t.scopeCircuits chal &&
  checkDigest6ShareMatch (t.parties chal) t.commitCircuits (t.parties chal).commitShare &&
  checkDigest6ShareMatch (t.parties next) t.commitCircuits (t.parties next).commitShare &&
  checkDigest6ShareMatch (t.parties chal) t.scopeCircuits (t.parties chal).scopeShare &&
  checkDigest6ShareMatch (t.parties next) t.scopeCircuits (t.parties next).scopeShare &&
  decide (sumDigest6Shares3 (fun i => (t.parties i).commitShare) = t.expectedCommit) &&
  decide (sumDigest6Shares3 (fun i => (t.parties i).scopeShare) = t.expectedScopeTag) &&
  checkPublicSlots t allSlots &&
  checkOpenedSlots t chal allSlots &&
  checkOpenedSlots t next allSlots &&
  decide ((t.parties chal).attrShares.length = t.attrCount) &&
  decide ((t.parties next).attrShares.length = t.attrCount)

def matchesIssuerSlots (attrs : List Goldilocks) (slots : List (Nat × Goldilocks)) : Prop :=
  ∀ p ∈ slots, attrs[p.1]? = some p.2

private theorem three_parties {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ i, P i := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    have := i.isLt
    have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hv with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases hi with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

private theorem checkCredView_reconstruct
    (expandTape : List UInt8 → Nat → Goldilocks)
    (t : ZkBooCredTriple)
    (e : CredCircuit t.attrCount)
    (hv : ∀ i, checkCredView expandTape t e i = true) :
    sumShares3 (fun i => (t.parties i).wires e) = evalCommit (reconAttrs t) (reconBlind t) e := by
  revert hv
  induction e with
  | attr j =>
    intro hv
    have he : (fun i => (t.parties i).wires (.attr j)) =
        (fun i => (((t.parties i).attrShares)[j.val]?).getD Goldilocks.zero) := by
      funext i
      have hi := hv i
      simp only [checkCredView, decide_eq_true_eq] at hi
      exact hi
    rw [he]
    simp [evalCommit, reconAttrs, j.isLt]
  | blind j =>
    intro hv
    have he : (fun i => (t.parties i).wires (.blind j)) =
        (fun i => blindLimb (t.parties i).blindShare j) := by
      funext i
      have hi := hv i
      simp only [checkCredView, decide_eq_true_eq] at hi
      exact hi
    rw [he]
    exact (reconBlind_limb t j).symm
  | constant c =>
    intro hv
    have he : (fun i => (t.parties i).wires (.constant c)) =
        (fun i : Fin 3 => if i.val = 0 then c else CommRingOps.zero) := by
      funext i
      have hi := hv i
      simp only [checkCredView, decide_eq_true_eq] at hi
      exact hi
    rw [he]
    simp [sumShares3, evalCommit, LawfulCommRing.add_zero]
  | add a b ha hb =>
    intro hv
    have hSplit : ∀ i, checkCredView expandTape t a i = true ∧
        checkCredView expandTape t b i = true ∧
        (t.parties i).wires (.add a b) =
          CommRingOps.add ((t.parties i).wires a) ((t.parties i).wires b) := by
      intro i
      have hi := hv i
      simp only [checkCredView, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨hi.1.1, hi.1.2, hi.2⟩
    have he : (fun i => (t.parties i).wires (.add a b)) =
        (fun i => CommRingOps.add ((t.parties i).wires a) ((t.parties i).wires b)) :=
      funext (fun i => (hSplit i).2.2)
    simp only [evalCommit, he, sumShares3_add,
      ha (fun i => (hSplit i).1), hb (fun i => (hSplit i).2.1)]
  | mul gid a b ha hb =>
    intro hv
    have hSplit : ∀ i, checkCredView expandTape t a i = true ∧
        checkCredView expandTape t b i = true ∧
        (t.parties i).wires (.mul gid a b) =
          zkBooMulShare (fun p => (t.parties p).wires a)
            (fun p => (t.parties p).wires b)
            (fun p => expandTape (t.parties p).tapeSeed gid) i := by
      intro i
      have hi := hv i
      simp only [checkCredView, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨hi.1.1, hi.1.2, hi.2⟩
    have he : (fun i => (t.parties i).wires (.mul gid a b)) =
        zkBooMulShare (fun p => (t.parties p).wires a)
          (fun p => (t.parties p).wires b)
          (fun p => expandTape (t.parties p).tapeSeed gid) :=
      funext (fun i => (hSplit i).2.2)
    simp only [evalCommit, he, zkBooMulShare_sum,
      ha (fun i => (hSplit i).1), hb (fun i => (hSplit i).2.1)]

private theorem checkCredView6_reconstruct
    (expandTape : List UInt8 → Nat → Goldilocks)
    (t : ZkBooCredTriple)
    (cs : CredCircuit6 t.attrCount)
    (hv : ∀ i, checkCredView6 expandTape t cs i = true)
    (outShares : Fin 3 → VcDigest6)
    (hMatch : ∀ i, checkDigest6ShareMatch (t.parties i) cs (outShares i) = true) :
    sumDigest6Shares3 outShares = evalCommit6 (reconAttrs t) (reconBlind t) cs := by
  have hUnpackView : ∀ i,
      checkCredView expandTape t cs.c0 i = true ∧
      checkCredView expandTape t cs.c1 i = true ∧
      checkCredView expandTape t cs.c2 i = true ∧
      checkCredView expandTape t cs.c3 i = true ∧
      checkCredView expandTape t cs.c4 i = true ∧
      checkCredView expandTape t cs.c5 i = true := by
    intro i
    have hi := hv i
    simp only [checkCredView6, Bool.and_eq_true] at hi
    exact ⟨hi.1.1.1.1.1, hi.1.1.1.1.2, hi.1.1.1.2, hi.1.1.2, hi.1.2, hi.2⟩
  have hUnpackOut : ∀ i,
      (outShares i).d0 = (t.parties i).wires cs.c0 ∧
      (outShares i).d1 = (t.parties i).wires cs.c1 ∧
      (outShares i).d2 = (t.parties i).wires cs.c2 ∧
      (outShares i).d3 = (t.parties i).wires cs.c3 ∧
      (outShares i).d4 = (t.parties i).wires cs.c4 ∧
      (outShares i).d5 = (t.parties i).wires cs.c5 := by
    intro i
    have hm := hMatch i
    simp only [checkDigest6ShareMatch, Bool.and_eq_true, decide_eq_true_eq] at hm
    exact ⟨hm.1.1.1.1.1, hm.1.1.1.1.2, hm.1.1.1.2, hm.1.1.2, hm.1.2, hm.2⟩
  apply VcDigest6.ext
  · change sumShares3 (fun i => (outShares i).d0) = evalCommit (reconAttrs t) (reconBlind t) cs.c0
    have he : (fun i => (outShares i).d0) = (fun i => (t.parties i).wires cs.c0) :=
      funext (fun i => (hUnpackOut i).1)
    rw [he]
    exact checkCredView_reconstruct expandTape t cs.c0 (fun i => (hUnpackView i).1)
  · change sumShares3 (fun i => (outShares i).d1) = evalCommit (reconAttrs t) (reconBlind t) cs.c1
    have he : (fun i => (outShares i).d1) = (fun i => (t.parties i).wires cs.c1) :=
      funext (fun i => (hUnpackOut i).2.1)
    rw [he]
    exact checkCredView_reconstruct expandTape t cs.c1 (fun i => (hUnpackView i).2.1)
  · change sumShares3 (fun i => (outShares i).d2) = evalCommit (reconAttrs t) (reconBlind t) cs.c2
    have he : (fun i => (outShares i).d2) = (fun i => (t.parties i).wires cs.c2) :=
      funext (fun i => (hUnpackOut i).2.2.1)
    rw [he]
    exact checkCredView_reconstruct expandTape t cs.c2 (fun i => (hUnpackView i).2.2.1)
  · change sumShares3 (fun i => (outShares i).d3) = evalCommit (reconAttrs t) (reconBlind t) cs.c3
    have he : (fun i => (outShares i).d3) = (fun i => (t.parties i).wires cs.c3) :=
      funext (fun i => (hUnpackOut i).2.2.2.1)
    rw [he]
    exact checkCredView_reconstruct expandTape t cs.c3 (fun i => (hUnpackView i).2.2.2.1)
  · change sumShares3 (fun i => (outShares i).d4) = evalCommit (reconAttrs t) (reconBlind t) cs.c4
    have he : (fun i => (outShares i).d4) = (fun i => (t.parties i).wires cs.c4) :=
      funext (fun i => (hUnpackOut i).2.2.2.2.1)
    rw [he]
    exact checkCredView_reconstruct expandTape t cs.c4 (fun i => (hUnpackView i).2.2.2.2.1)
  · change sumShares3 (fun i => (outShares i).d5) = evalCommit (reconAttrs t) (reconBlind t) cs.c5
    have he : (fun i => (outShares i).d5) = (fun i => (t.parties i).wires cs.c5) :=
      funext (fun i => (hUnpackOut i).2.2.2.2.2)
    rw [he]
    exact checkCredView_reconstruct expandTape t cs.c5 (fun i => (hUnpackView i).2.2.2.2.2)

/-- 3-special soundness for a committed ZKBoo triple: accepting all 3 challenges extracts a valid
    witness `(reconAttrs t, reconBlind t)` matching all 6 commitment limbs, all 6 scope-tag limbs,
    disclosed attributes,issuer slots, and all 3 party view commitments. -/
theorem zkBooCred_extract
    (commitView : (n : Nat) → Fin 3 → PartyCredView n → List UInt8)
    (expandTape : List UInt8 → Nat → Goldilocks)
    (t : ZkBooCredTriple)
    (h0 : checkOpenedPair commitView expandTape t 0 = true)
    (h1 : checkOpenedPair commitView expandTape t 1 = true)
    (h2 : checkOpenedPair commitView expandTape t 2 = true) :
    (∀ i : Fin 3, commitView t.attrCount i (t.parties i) = t.partyCommits i) ∧
    evalCommit6 (reconAttrs t) (reconBlind t) t.commitCircuits = t.expectedCommit ∧
    evalCommit6 (reconAttrs t) (reconBlind t) t.scopeCircuits = t.expectedScopeTag ∧
    matchesDisclosed (reconAttrs t) t.disclosed ∧
    matchesIssuerSlots (reconAttrs t) t.issuerSlots := by
  have hall := three_parties (P := fun i => checkOpenedPair commitView expandTape t i = true) h0 h1 h2
  have hUnpack : ∀ i : Fin 3,
      commitView t.attrCount i (t.parties i) = t.partyCommits i ∧
      checkCredView6 expandTape t t.commitCircuits i = true ∧
      checkCredView6 expandTape t t.scopeCircuits i = true ∧
      checkDigest6ShareMatch (t.parties i) t.commitCircuits (t.parties i).commitShare = true ∧
      checkDigest6ShareMatch (t.parties i) t.scopeCircuits (t.parties i).scopeShare = true ∧
      sumDigest6Shares3 (fun p => (t.parties p).commitShare) = t.expectedCommit ∧
      sumDigest6Shares3 (fun p => (t.parties p).scopeShare) = t.expectedScopeTag ∧
      checkPublicSlots t (t.disclosed ++ t.issuerSlots) = true ∧
      checkOpenedSlots t i (t.disclosed ++ t.issuerSlots) = true := by
    intro i
    have hi := hall i
    simp only [checkOpenedPair, Bool.and_eq_true, decide_eq_true_eq] at hi
    exact ⟨hi.1.1.1.1.1.1.1.1.1.1.1.1.1.1,
           hi.1.1.1.1.1.1.1.1.1.1.1.1.2,
           hi.1.1.1.1.1.1.1.1.1.1.1.2,
           hi.1.1.1.1.1.1.1.1.1.1.2,
           hi.1.1.1.1.1.1.1.1.2,
           hi.1.1.1.1.1.1.2,
           hi.1.1.1.1.1.2,
           hi.1.1.1.1.2,
           hi.1.1.1.2⟩
  have hCommit : evalCommit6 (reconAttrs t) (reconBlind t) t.commitCircuits = t.expectedCommit := by
    rw [← checkCredView6_reconstruct expandTape t t.commitCircuits
          (fun i => (hUnpack i).2.1) (fun i => (t.parties i).commitShare)
          (fun i => (hUnpack i).2.2.2.1)]
    exact (hUnpack 0).2.2.2.2.2.1
  have hScope : evalCommit6 (reconAttrs t) (reconBlind t) t.scopeCircuits = t.expectedScopeTag := by
    rw [← checkCredView6_reconstruct expandTape t t.scopeCircuits
          (fun i => (hUnpack i).2.2.1) (fun i => (t.parties i).scopeShare)
          (fun i => (hUnpack i).2.2.2.2.1)]
    exact (hUnpack 0).2.2.2.2.2.2.1
  have hslots : ∀ p ∈ t.disclosed ++ t.issuerSlots, (reconAttrs t)[p.1]? = some p.2 := by
    intro p hp
    have hPub := (List.all_eq_true.mp (hUnpack 0).2.2.2.2.2.2.2.1) p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPub
    obtain ⟨hlt, hsum⟩ := hPub
    have he : (fun i => (t.parties i).publicAttrOutputs p.1) =
        (fun i => (((t.parties i).attrShares)[p.1]?).getD Goldilocks.zero) := by
      funext i
      have hOpen := (List.all_eq_true.mp (hUnpack i).2.2.2.2.2.2.2.2) p hp
      exact of_decide_eq_true hOpen
    rw [he] at hsum
    simp [reconAttrs, hlt, hsum]
  refine ⟨fun i => (hUnpack i).1, hCommit, hScope, ?_, ?_⟩
  · intro p hp; exact hslots p (List.mem_append.mpr (Or.inl hp))
  · intro p hp; exact hslots p (List.mem_append.mpr (Or.inr hp))

/-- Constructive (`0 Classical.choice`) per-repetition soundness bound: any invalid committed triple
    is rejected by at least 1 of the 3 ternary challenges (`≤ 2/3` soundness error per repetition). -/
