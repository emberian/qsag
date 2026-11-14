module
/-
# Advanced MPC and credentials
Constructive arithmetic models and explicit protocol boundaries.
LAW-M1: public statements with a bounded exposed interface.
The models below describe arithmetic circuits and immutable committed views;
implementation refinement and cryptographic binding are separate obligations.
-/

public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Poseidon2
public import Qsag.Constructive
public import Qsag.Keccak
public import Qsag.Tactic.AssuranceKit

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
  | v :: rest => bech32PolymodFrom (bech32PolymodStep chk v) rest

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
    {n pos : Nat} {delta : BitVec 5} (hdelta : delta ≠ 0#5) :
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
    exact bech32PolymodFrom_singleSubstError_ne_zero hDelta hSynZero

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

/-- Constructive (constructive) explicit bijection carrier for hiding/unlinkability proofs. -/
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

/-- Legacy arithmetic oracle view. The function-valued wires are NOT a finite
    serializable transcript. Use `BlindVcWire.PartyView` for wire-format reasoning;
    no privacy/computational binding claim follows for this legacy carrier. -/
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

/-- Computable (constructive) gate-by-gate verifier for party `i`
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

/-- Fixed-triple reconstruction: accepting all 3 challenges of the SAME triple extracts a valid
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

/-- Constructive (constructive) per-repetition soundness bound: any invalid committed triple
    is rejected by at least 1 of the 3 ternary challenges. A probability interpretation
    requires an independent uniform challenge; this is not a Fiat–Shamir theorem. -/
theorem zkBooCred_invalid_rejected
    (commitView : (n : Nat) → Fin 3 → PartyCredView n → List UInt8)
    (expandTape : List UInt8 → Nat → Goldilocks)
    (t : ZkBooCredTriple)
    (hbad : ¬ (evalCommit6 (reconAttrs t) (reconBlind t) t.commitCircuits = t.expectedCommit ∧
      evalCommit6 (reconAttrs t) (reconBlind t) t.scopeCircuits = t.expectedScopeTag ∧
      matchesDisclosed (reconAttrs t) t.disclosed ∧
      matchesIssuerSlots (reconAttrs t) t.issuerSlots)) :
    ∃ chal : Fin 3, checkOpenedPair commitView expandTape t chal = false := by
  cases h0 : checkOpenedPair commitView expandTape t 0 with
  | false => exact ⟨0, h0⟩
  | true =>
    cases h1 : checkOpenedPair commitView expandTape t 1 with
    | false => exact ⟨1, h1⟩
    | true =>
      cases h2 : checkOpenedPair commitView expandTape t 2 with
      | false => exact ⟨2, h2⟩
      | true =>
        obtain ⟨_, hc, hs, hd, hi⟩ := zkBooCred_extract commitView expandTape t h0 h1 h2
        exact False.elim (hbad ⟨hc, hs, hd, hi⟩)

/-- 3-share additive encoding of a secret wire `secret` using two uniform Goldilocks coins `(r0, r1)`. -/
def credShareWire3 (secret r0 r1 : Goldilocks) : Fin 3 → Goldilocks
  | ⟨0, _⟩ => r0
  | ⟨1, _⟩ => r1
  | ⟨2, _⟩ => Goldilocks.sub (Goldilocks.sub secret r0) r1

theorem credShareWire3_sum (secret r0 r1 : Goldilocks) :
    sumShares3 (credShareWire3 secret r0 r1) = secret := by
  unfold sumShares3 credShareWire3
  dsimp only
  change CommRingOps.add r0
    (CommRingOps.add r1 (CommRingOps.sub (CommRingOps.sub secret r0) r1)) = secret
  rw [LawfulCommRing.add_sub_cancel_left r1, LawfulCommRing.add_sub_cancel_left r0]

def credSharePairView (chal : Fin 3) (secret : Goldilocks) (coins : Goldilocks × Goldilocks) :
    Goldilocks × Goldilocks :=
  let w := credShareWire3 secret coins.1 coins.2
  (w chal, w (nextParty chal))

def credSharePairInv (chal : Fin 3) (secret : Goldilocks) (pair : Goldilocks × Goldilocks) :
    Goldilocks × Goldilocks :=
  match chal with
  | ⟨0, _⟩ => pair
  | ⟨1, _⟩ => (Goldilocks.sub (Goldilocks.sub secret pair.1) pair.2, pair.1)
  | ⟨2, _⟩ => (pair.2, Goldilocks.sub (Goldilocks.sub secret pair.2) pair.1)

private theorem gl_sub_sub_cancel_r0 (s r0 r1 : Goldilocks) :
    Goldilocks.sub (Goldilocks.sub s r1) (Goldilocks.sub (Goldilocks.sub s r0) r1) = r0 := by
  change CommRingOps.sub (CommRingOps.sub s r1) (CommRingOps.sub (CommRingOps.sub s r0) r1) = r0
  apply LawfulCommRing.add_left_cancel (a := CommRingOps.sub (CommRingOps.sub s r0) r1)
  rw [LawfulCommRing.add_sub_cancel_left]
  apply LawfulCommRing.add_left_cancel (a := r1)
  rw [LawfulCommRing.add_sub_cancel_left, ← LawfulCommRing.add_assoc,
      LawfulCommRing.add_sub_cancel_left, LawfulCommRing.add_comm _ r0,
      LawfulCommRing.add_sub_cancel_left]

private theorem gl_sub_sub_cancel_r1 (s r0 r1 : Goldilocks) :
    Goldilocks.sub (Goldilocks.sub s r0) (Goldilocks.sub (Goldilocks.sub s r0) r1) = r1 := by
  change CommRingOps.sub (CommRingOps.sub s r0) (CommRingOps.sub (CommRingOps.sub s r0) r1) = r1
  apply LawfulCommRing.add_left_cancel (a := CommRingOps.sub (CommRingOps.sub s r0) r1)
  rw [LawfulCommRing.add_sub_cancel_left, LawfulCommRing.add_comm _ r1,
      LawfulCommRing.add_sub_cancel_left]

private theorem gl_sub_sub_comm_local (s a b : Goldilocks) :
    Goldilocks.sub (Goldilocks.sub s a) b = Goldilocks.sub (Goldilocks.sub s b) a := by
  change CommRingOps.sub (CommRingOps.sub s a) b = CommRingOps.sub (CommRingOps.sub s b) a
  simp only [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc]
  rw [LawfulCommRing.add_comm (CommRingOps.neg a) (CommRingOps.neg b)]

/-- Constructive (constructive) bijection between uniform sharing coins `(r0, r1)` and ANY
    opened 2-party adjacent wire view `(w_e, w_{e+1})`: proves perfect 2-of-3 hiding of every
    undisclosed attribute and blinding limb! -/
def credSharePairBijection (chal : Fin 3) (secret : Goldilocks) :
    CredBijection (Goldilocks × Goldilocks) (Goldilocks × Goldilocks) where
  toFun := credSharePairView chal secret
  invFun := credSharePairInv chal secret
  left_inv := fun ⟨r0, r1⟩ => by
    rcases chal with ⟨cv, hcv⟩
    have hCases : cv = 0 ∨ cv = 1 ∨ cv = 2 := by omega
    rcases hCases with rfl | rfl | rfl
    · rfl
    · dsimp only [credSharePairView, credSharePairInv, credShareWire3, nextParty]
      exact Prod.ext (gl_sub_sub_cancel_r0 secret r0 r1) rfl
    · dsimp only [credSharePairView, credSharePairInv, credShareWire3, nextParty]
      exact Prod.ext rfl (gl_sub_sub_cancel_r1 secret r0 r1)
  right_inv := fun ⟨v0, v1⟩ => by
    rcases chal with ⟨cv, hcv⟩
    have hCases : cv = 0 ∨ cv = 1 ∨ cv = 2 := by omega
    rcases hCases with rfl | rfl | rfl
    · rfl
    · dsimp only [credSharePairView, credSharePairInv, credShareWire3, nextParty]
      refine Prod.ext rfl ?_
      rw [gl_sub_sub_comm_local secret (Goldilocks.sub (Goldilocks.sub secret v0) v1) v0,
          gl_sub_sub_cancel_r1 secret v0 v1]
    · dsimp only [credSharePairView, credSharePairInv, credShareWire3, nextParty]
      exact Prod.ext (gl_sub_sub_cancel_r1 secret v1 v0) rfl

/-- Translation bijection for the blind alone. This does not establish privacy of
    commitments, scope tags, issuer observations, or complete presentations. -/
def vcReblindBijection (holderBlind : VcBlind4) : CredBijection VcBlind4 VcBlind4 where
  toFun := vcReblind holderBlind
  invFun := fun y => vcUnreblind y holderBlind
  left_inv := fun ⟨d0, d1, d2, d3⟩ => by
    unfold vcReblind vcUnreblind
    simp only [gl_sub_add_cancel_left]
  right_inv := fun ⟨y0, y1, y2, y3⟩ => by
    unfold vcReblind vcUnreblind
    simp only [gl_add_sub_cancel]

private def mkEquivocatingTriple0 (chal : Fin 3) : ZkBooCredTriple :=
  let zeroC6 : CredCircuit6 0 :=
    ⟨.constant Goldilocks.zero, .constant Goldilocks.zero, .constant Goldilocks.zero,
     .constant Goldilocks.zero, .constant Goldilocks.zero, .constant Goldilocks.zero⟩
  let forgedDigest : VcDigest6 :=
    ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero,
     Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let zeroDigest : VcDigest6 :=
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
     Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let unopened : Fin 3 := nextParty (nextParty chal)
  { attrCount := 0
    parties := fun i =>
      { attrShares := []
        blindShare := (Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero)
        tapeSeed := []
        salt := []
        wires := fun _ => Goldilocks.zero
        commitShare := if i = unopened then forgedDigest else zeroDigest
        scopeShare := zeroDigest
        publicAttrOutputs := fun _ => Goldilocks.zero }
    partyCommits := fun _ => []
    commitCircuits := zeroC6
    scopeCircuits := zeroC6
    expectedCommit := forgedDigest
    expectedScopeTag := zeroDigest
    issuerSlots := []
    disclosed := [] }

/-- **`#tooth` (`tooth_uncommitted_views_allow_adaptive_equivocation`)**:
    Without non-trivial Round-1 view commitments (modeled by a degenerate constant `commitView := fun _ _ _ => []`),
    an adversary with NO witness can craft 3 challenge-dependent triples `(t_0, t_1, t_2)` with identical
    public `partyCommits = fun _ => []` such that `checkOpenedPair ... t_e e = true` for EVERY `e ∈ {0, 1, 2}`
    on the unsatisfiable circuit `constant 0 = 1`! -/
theorem tooth_uncommitted_views_allow_adaptive_equivocation :
    let trivialCommit : (n : Nat) → Fin 3 → PartyCredView n → List UInt8 := fun _ _ _ => []
    let zeroTape : List UInt8 → Nat → Goldilocks := fun _ _ => Goldilocks.zero
    let zeroC6 : CredCircuit6 0 :=
      ⟨.constant Goldilocks.zero, .constant Goldilocks.zero, .constant Goldilocks.zero,
       .constant Goldilocks.zero, .constant Goldilocks.zero, .constant Goldilocks.zero⟩
    let forgedDigest : VcDigest6 :=
      ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero,
       Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
    let zeroDigest : VcDigest6 :=
      ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
       Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
    (∀ attrs blind, evalCommit6 attrs blind zeroC6 ≠ forgedDigest) ∧
    (∀ chal : Fin 3, ∃ t : ZkBooCredTriple,
      ∃ hAttr : t.attrCount = 0,
      t.partyCommits = (fun _ => []) ∧
      hAttr ▸ t.commitCircuits = zeroC6 ∧
      t.expectedCommit = forgedDigest ∧
      t.expectedScopeTag = zeroDigest ∧
      checkOpenedPair trivialCommit zeroTape t chal = true) := by
  intro trivialCommit zeroTape zeroC6 forgedDigest zeroDigest
  refine ⟨?_, ?_⟩
  · intro attrs blind hEq
    have hd0 := congrArg VcDigest6.d0 hEq
    have hv := congrArg Goldilocks.val hd0
    simp [evalCommit6, evalCommit, zeroC6, forgedDigest] at hv
  · intro chal
    refine ⟨mkEquivocatingTriple0 chal, rfl, rfl, rfl, rfl, rfl, ?_⟩
    have hz : (CommRingOps.zero : Goldilocks) = Goldilocks.zero := rfl
    rcases chal with ⟨cv, hcv⟩
    have hCases : cv = 0 ∨ cv = 1 ∨ cv = 2 := by omega
    rcases hCases with rfl | rfl | rfl <;>
      simp [checkOpenedPair, mkEquivocatingTriple0, checkCredView6, checkCredView,
            checkDigest6ShareMatch, checkPublicSlots, checkOpenedSlots,
            sumDigest6Shares3, sumShares3, nextParty,
            trivialCommit, zeroTape,
            ← hz, LawfulCommRing.add_zero, LawfulCommRing.zero_add]

/-- Local reblinding and single-wire hiding, plus fixed-triple arithmetic reconstruction.
The historical name is retained for source compatibility. No distribution of complete
presentations or Fiat–Shamir/QROM adversary is modeled by this theorem. -/
theorem blind_vc_selective_disclosure_sound_and_unlinkable :
    (∀ b : VcBlind4,
      (∀ delta : VcBlind4, (vcReblindBijection b).invFun ((vcReblindBijection b).toFun delta) = delta) ∧
      (∀ y : VcBlind4, (vcReblindBijection b).toFun ((vcReblindBijection b).invFun y) = y)) ∧
    (∀ (chal : Fin 3) (secretA secretB : Goldilocks),
      ∃ coinBij : CredBijection (Goldilocks × Goldilocks) (Goldilocks × Goldilocks),
        ∀ coinsA : Goldilocks × Goldilocks,
          credSharePairView chal secretB (coinBij.toFun coinsA) =
            credSharePairView chal secretA coinsA) ∧
    (∀ x y : UInt64, encodeU64Limbs2 x = encodeU64Limbs2 y → x = y) ∧
    (∀ (commitView : (n : Nat) → Fin 3 → PartyCredView n → List UInt8)
       (expandTape : List UInt8 → Nat → Goldilocks)
       (t : ZkBooCredTriple),
      checkOpenedPair commitView expandTape t 0 = true →
      checkOpenedPair commitView expandTape t 1 = true →
      checkOpenedPair commitView expandTape t 2 = true →
      evalCommit6 (reconAttrs t) (reconBlind t) t.commitCircuits = t.expectedCommit ∧
      evalCommit6 (reconAttrs t) (reconBlind t) t.scopeCircuits = t.expectedScopeTag ∧
      matchesDisclosed (reconAttrs t) t.disclosed ∧
      matchesIssuerSlots (reconAttrs t) t.issuerSlots) := by
  refine ⟨?_, ?_, encodeU64Limbs2_injective, ?_⟩
  · intro b
    exact ⟨(vcReblindBijection b).left_inv, (vcReblindBijection b).right_inv⟩
  · intro chal secretA secretB
    let bA := credSharePairBijection chal secretA
    let bB := credSharePairBijection chal secretB
    refine ⟨{
      toFun := fun c => bB.invFun (bA.toFun c)
      invFun := fun c => bA.invFun (bB.toFun c)
      left_inv := fun c => by simp only [bB.right_inv, bA.left_inv]
      right_inv := fun c => by simp only [bA.right_inv, bB.left_inv]
    }, ?_⟩
    intro coinsA
    exact bB.right_inv (bA.toFun coinsA)
  · intro commitView expandTape t h0 h1 h2
    obtain ⟨_, hc, hs, hd, hi⟩ := zkBooCred_extract commitView expandTape t h0 h1 h2
    exact ⟨hc, hs, hd, hi⟩

/-! ## 5. Crash-Persistent `FsNonceBurnStore` & Threshold RSS Nonce-Reuse Key Extraction -/

/-- Lattice Schnorr / `FIPS 204` partial or reconstructed response $z = y + c \cdot s_1$ over ring `R`. -/
@[expose] def mldsaLinearResponse {R : Type} [CommRingOps R] (y c s1 : R) : R :=
  CommRingOps.add y (CommRingOps.mul c s1)

def ringSumList {R : Type} [CommRingOps R] : List R → R
  | [] => CommRingOps.zero
  | x :: xs => CommRingOps.add x (ringSumList xs)

/-- Threshold RSS subset-component response vector `[y_0 + c * s1_0, ..., y_{K-1} + c * s1_{K-1}]`
    (`threshold_mldsa.rs:865-870`). -/
def rssSubsetResponses {R : Type} [CommRingOps R] (c : R) : List R → List R → List R
  | y :: ys, s :: ss => mldsaLinearResponse y c s :: rssSubsetResponses c ys ss
  | _, _ => []

theorem rssSubsetResponses_sum {R : Type} [LawfulCommRing R] (c : R)
    (yShares : List R) :
    ∀ (s1Shares : List R),
      yShares.length = s1Shares.length →
      ringSumList (rssSubsetResponses c yShares s1Shares) =
        mldsaLinearResponse (ringSumList yShares) c (ringSumList s1Shares) := by
  induction yShares with
  | nil =>
    intro s1Shares hLen
    cases s1Shares with
    | nil =>
      simp only [rssSubsetResponses, ringSumList, mldsaLinearResponse,
        LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | cons _ _ => cases hLen
  | cons y ys ih =>
    intro s1Shares hLen
    cases s1Shares with
    | nil => cases hLen
    | cons s ss =>
      have hTail : ys.length = ss.length := Nat.succ.inj hLen
      simp only [rssSubsetResponses, ringSumList, ih ss hTail,
        mldsaLinearResponse, LawfulCommRing.left_distrib]
      rw [LawfulCommRing.add_add_add_comm]

/-- Centered modulo-`q` infinity-norm check (`threshold_mldsa.rs:660-682, 873-883`):
    every coefficient `v < q` satisfies centered `|v|_± < bound` iff `v < bound ∨ q - bound < v`. -/
def checkCenteredInfNorm (q bound : Nat) (coeffs : List Nat) : Bool :=
  coeffs.all (fun v => decide (v < q) && (decide (v < bound) || decide (q < v + bound)))

/-- Durable 46-byte + 32-byte key-bound attempt record matching `FsNonceBurnStore`
    (`crates/qsag-cred/src/threshold_mldsa.rs:153-213`):
    binds `(key_id, party_id, epoch, session_id, attempt)` across process restarts. -/
structure DurableBurnRow where
  keyId : List UInt8
  partyId : UInt16
  epoch : UInt64
  sessionId : List UInt8
  attempt : UInt32
  deriving DecidableEq, Repr

/-- Crash-atomic persistent burn ledger (`FsNonceBurnStore` disk state + poison latch). -/
structure DurableNonceBurnStore where
  keyId : List UInt8
  burns : List DurableBurnRow
  poisoned : Bool
  deriving DecidableEq, Repr

/-- Exact `FsNonceBurnStore::available` check (`threshold_mldsa.rs:208-212`):
    rejects if `poisoned`, if `epoch == u64::MAX`, or if ANY persisted row for `(keyId, partyId)`
    has `row.epoch >= epoch` OR `(row.sessionId == sessionId && row.attempt == attempt)`. -/
def burnRowConflicts (keyId : List UInt8) (partyId : UInt16)
    (epoch : UInt64) (sessionId : List UInt8) (attempt : UInt32) (row : DurableBurnRow) : Bool :=
  decide (row.keyId = keyId) &&
  decide (row.partyId = partyId) &&
  (decide (epoch.toNat ≤ row.epoch.toNat) ||
   (decide (row.sessionId = sessionId) && decide (row.attempt = attempt)))

def durableBurnAvailable (store : DurableNonceBurnStore)
    (partyId : UInt16) (epoch : UInt64) (sessionId : List UInt8) (attempt : UInt32) : Bool :=
  !store.poisoned &&
  decide (epoch.toNat + 1 < 2 ^ 64) &&
  store.burns.all (fun row => !burnRowConflicts store.keyId partyId epoch sessionId attempt row)

/-- Atomic `FsNonceBurnStore::reserve` (`threshold_mldsa.rs:217-225`):
    checks `durableBurnAvailable`; if atomic disk `replace` fails (`diskWriteOk = false`),
    poisons the store and refuses to release the nonce! -/
def durableBurnReserve (store : DurableNonceBurnStore)
    (partyId : UInt16) (epoch : UInt64) (sessionId : List UInt8) (attempt : UInt32)
    (diskWriteOk : Bool) : Bool × DurableNonceBurnStore :=
  if durableBurnAvailable store partyId epoch sessionId attempt then
    if diskWriteOk then
      let row : DurableBurnRow :=
        { keyId := store.keyId, partyId := partyId, epoch := epoch,
          sessionId := sessionId, attempt := attempt }
      (true, { store with burns := store.burns ++ [row] })
    else
      (false, { store with poisoned := true })
  else
    (false, store)

/-- Durable epoch recovery `FsNonceBurnStore::next_epoch` (`threshold_mldsa.rs:227-232`):
    returns `max { row.epoch + 1 | row ∈ burns, row.keyId = keyId ∧ row.partyId = partyId }` (or `0`). -/
def persistedNextEpochNat (keyId : List UInt8) (partyId : UInt16) : List DurableBurnRow → Nat
  | [] => 0
  | r :: rs =>
    let rest := persistedNextEpochNat keyId partyId rs
    if r.keyId = keyId ∧ r.partyId = partyId then
      Nat.max (r.epoch.toNat + 1) rest
    else
      rest

/-- Combined signer custodian RAM + durable disk state across signing attempts and OS crashes. -/
structure SignerCrashState where
  ramNextEpoch : Nat
  store : DurableNonceBurnStore
  deriving DecidableEq, Repr

/-- Recover `ramNextEpoch` after restart (`ThresholdMlDsaSignerShare::recover_epoch_from_store`,
    `threshold_mldsa.rs:342-345`). -/
def recoverSignerEpoch (st : SignerCrashState) (partyId : UInt16) : SignerCrashState :=
  { st with
    ramNextEpoch := Nat.max st.ramNextEpoch (persistedNextEpochNat st.store.keyId partyId st.store.burns) }

/-- Observable signing attempt event emitted ONLY when `durableBurnReserve` returns `true`. -/
structure PersistentNonceEvent where
  partyId : UInt16
  epoch : UInt64
  sessionId : List UInt8
  attempt : UInt32
  normAccepted : Bool
  deriving DecidableEq, Repr

/-- Multi-session, crash-inclusive state transitions of a threshold ML-DSA custodian:
    includes accepted signatures, norm-rejected attempts (`||z|| >= gamma1 - beta` or `||r0|| >= gamma2 - beta`),
    failed disk writes (which poison the store and emit NO signing message), AND arbitrary process crashes
    that wipe RAM (`ramNextEpoch := 0`) followed by `recoverSignerEpoch`! -/
inductive PersistentNonceStep (partyId : UInt16) :
    SignerCrashState → Option PersistentNonceEvent → SignerCrashState → Prop where
  | reserveAttempt (st : SignerCrashState) (epoch : UInt64)
      (sid : List UInt8) (att : UInt32) (normOk : Bool)
      (hEpochEq : epoch.toNat = st.ramNextEpoch)
      (hRes : (durableBurnReserve st.store partyId epoch sid att true).1 = true) :
      PersistentNonceStep partyId st
        (some { partyId := partyId, epoch := epoch, sessionId := sid,
                attempt := att, normAccepted := normOk })
        { ramNextEpoch := st.ramNextEpoch + 1
          store := (durableBurnReserve st.store partyId epoch sid att true).2 }
  | diskWriteFailure (st : SignerCrashState) (epoch : UInt64) (sid : List UInt8) (att : UInt32) :
      PersistentNonceStep partyId st none
        { st with store := (durableBurnReserve st.store partyId epoch sid att false).2 }
  | crashAndRecover (st : SignerCrashState) :
      PersistentNonceStep partyId st none
        (recoverSignerEpoch { ramNextEpoch := 0, store := st.store } partyId)

inductive ValidPersistentNonceTrace (partyId : UInt16) :
    SignerCrashState → List PersistentNonceEvent → SignerCrashState → Prop where
  | nil (st : SignerCrashState) : ValidPersistentNonceTrace partyId st [] st
  | consSome {st₀ st₁ st₂ : SignerCrashState} {ev : PersistentNonceEvent}
      {rest : List PersistentNonceEvent}
      (hStep : PersistentNonceStep partyId st₀ (some ev) st₁)
      (hTail : ValidPersistentNonceTrace partyId st₁ rest st₂) :
      ValidPersistentNonceTrace partyId st₀ (ev :: rest) st₂
  | consSilent {st₀ st₁ st₂ : SignerCrashState} {rest : List PersistentNonceEvent}
      (hStep : PersistentNonceStep partyId st₀ none st₁)
      (hTail : ValidPersistentNonceTrace partyId st₁ rest st₂) :
      ValidPersistentNonceTrace partyId st₀ rest st₂

private theorem durableBurnReserve_true_iff
    (store : DurableNonceBurnStore) (partyId : UInt16) (epoch : UInt64)
    (sid : List UInt8) (att : UInt32) :
    (durableBurnReserve store partyId epoch sid att true).1 = true ↔
      durableBurnAvailable store partyId epoch sid att = true := by
  unfold durableBurnReserve
  cases durableBurnAvailable store partyId epoch sid att <;> rfl

private theorem persistentStep_burns_sublist {partyId : UInt16}
    {st₀ st₁ : SignerCrashState} {oev : Option PersistentNonceEvent}
    (hStep : PersistentNonceStep partyId st₀ oev st₁) :
    st₀.store.keyId = st₁.store.keyId ∧
    ∀ row ∈ st₀.store.burns, row ∈ st₁.store.burns := by
  cases hStep with
  | reserveAttempt epoch sid att normOk _ hRes =>
    have hAv := (durableBurnReserve_true_iff st₀.store partyId epoch sid att).mp hRes
    dsimp only
    simp [durableBurnReserve, hAv]
    exact fun row hm => Or.inl hm
  | diskWriteFailure epoch sid att =>
    dsimp only
    cases hAv : durableBurnAvailable st₀.store partyId epoch sid att <;>
      simp [durableBurnReserve, hAv]
  | crashAndRecover =>
    exact ⟨rfl, fun _ hm => hm⟩

private theorem validPersistentTrace_burns_mono {partyId : UInt16}
    {st₀ st₂ : SignerCrashState} {evs : List PersistentNonceEvent}
    (hTr : ValidPersistentNonceTrace partyId st₀ evs st₂) :
    st₀.store.keyId = st₂.store.keyId ∧
    ∀ row ∈ st₀.store.burns, row ∈ st₂.store.burns := by
  induction hTr with
  | nil _ => exact ⟨rfl, fun _ hm => hm⟩
  | consSome hStep _ ih =>
    obtain ⟨hk1, hsub1⟩ := persistentStep_burns_sublist hStep
    obtain ⟨hk2, hsub2⟩ := ih
    exact ⟨hk1.trans hk2, fun r hr => hsub2 r (hsub1 r hr)⟩
  | consSilent hStep _ ih =>
    obtain ⟨hk1, hsub1⟩ := persistentStep_burns_sublist hStep
    obtain ⟨hk2, hsub2⟩ := ih
    exact ⟨hk1.trans hk2, fun r hr => hsub2 r (hsub1 r hr)⟩

private theorem validPersistentTrace_event_conflict_free {partyId : UInt16}
    {st₀ st₂ : SignerCrashState} {evs : List PersistentNonceEvent}
    (hTr : ValidPersistentNonceTrace partyId st₀ evs st₂) :
    (∀ row ∈ st₀.store.burns, row.keyId = st₀.store.keyId → row.partyId = partyId →
      ∀ e ∈ evs, row.epoch.toNat < e.epoch.toNat ∧ ¬ (row.sessionId = e.sessionId ∧ row.attempt = e.attempt)) ∧
    evs.Pairwise (fun e₁ e₂ =>
      e₁.epoch.toNat < e₂.epoch.toNat ∧
      e₁.epoch ≠ e₂.epoch ∧
      (e₁.sessionId, e₁.attempt) ≠ (e₂.sessionId, e₂.attempt)) := by
  induction hTr with
  | nil _ =>
    exact ⟨(fun _ _ _ _ _ hm => nomatch hm), List.Pairwise.nil⟩
  | consSilent hStep _ ih =>
    obtain ⟨hkStep, hSubStep⟩ := persistentStep_burns_sublist hStep
    refine ⟨?_, ih.2⟩
    intro row hMem hKey hPid e he
    exact ih.1 row (hSubStep row hMem) (hKey.trans hkStep) hPid e he
  | @consSome st _ _ _ _ hStep _ ih =>
    cases hStep with
    | reserveAttempt epoch sid att normOk _ hRes =>
      have hAv := (durableBurnReserve_true_iff st.store partyId epoch sid att).mp hRes
      have hStoreNext : (durableBurnReserve st.store partyId epoch sid att true).2 =
          { st.store with burns := st.store.burns ++
              [{ keyId := st.store.keyId, partyId := partyId, epoch := epoch,
                 sessionId := sid, attempt := att }] } := by
        simp only [durableBurnReserve, hAv, ↓reduceIte]
      have hOldVsHead : ∀ row ∈ st.store.burns, row.keyId = st.store.keyId → row.partyId = partyId →
          row.epoch.toNat < epoch.toNat ∧ ¬ (row.sessionId = sid ∧ row.attempt = att) := by
        intro row hMem hKey hPid
        unfold durableBurnAvailable at hAv
        simp only [Bool.and_eq_true] at hAv
        have hNoConf := List.all_eq_true.mp hAv.2 row hMem
        unfold burnRowConflicts at hNoConf
        simp only [hKey, hPid, decide_true, Bool.true_and, Bool.not_eq_true',
          Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hNoConf
        refine ⟨by omega, ?_⟩
        rintro ⟨hSid, hAtt⟩
        rcases hNoConf.2 with hBadSid | hBadAtt
        · exact hBadSid hSid
        · exact hBadAtt hAtt
      refine ⟨?_, ?_⟩
      · intro row hMem hKey hPid e he
        rcases List.mem_cons.mp he with rfl | heRest
        · exact hOldVsHead row hMem hKey hPid
        · have hMemNext : row ∈ (durableBurnReserve st.store partyId epoch sid att true).2.burns := by
            rw [hStoreNext]; exact List.mem_append.mpr (Or.inl hMem)
          have hKeyNext : row.keyId = (durableBurnReserve st.store partyId epoch sid att true).2.keyId := by
            rw [hStoreNext]; exact hKey
          exact ih.1 row hMemNext hKeyNext hPid e heRest
      · refine List.Pairwise.cons ?_ ih.2
        intro e₂ he₂
        let newRow : DurableBurnRow :=
          { keyId := st.store.keyId, partyId := partyId, epoch := epoch,
            sessionId := sid, attempt := att }
        have hMemNew : newRow ∈ (durableBurnReserve st.store partyId epoch sid att true).2.burns := by
          rw [hStoreNext]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
        have hKeyNew : newRow.keyId = (durableBurnReserve st.store partyId epoch sid att true).2.keyId := by
          rw [hStoreNext]
        obtain ⟨hLt, hNeSA⟩ := ih.1 newRow hMemNew hKeyNew rfl e₂ he₂
        refine ⟨hLt, ?_, ?_⟩
        · intro hEqEp
          have hEp : epoch = e₂.epoch := hEqEp
          have hLt' : epoch.toNat < e₂.epoch.toNat := hLt
          rw [hEp] at hLt'
          exact Nat.lt_irrefl _ hLt'
        · intro hEqPair
          injection hEqPair with hS hA
          exact hNeSA ⟨hS, hA⟩

/-- **`#tooth` (`tooth_ram_only_crash_without_recovery_reuses_epoch_zero`)**:
    If a signer initializes `next_epoch = 0` in RAM and crashes without checking persistent storage
    (replacing `DurableNonceBurnStore` with an ephemeral RAM counter reset on restart), two sessions
    before and after restart BOTH mint `epoch = 0` and expose `s1` via `mldsaLinearResponse`! -/
theorem tooth_ram_only_crash_without_recovery_reuses_epoch_zero :
    let ephemeralBeforeCrash : SignerCrashState :=
      { ramNextEpoch := 0, store := { keyId := [0x42], burns := [], poisoned := false } }
    let afterWipedDiskCrash : SignerCrashState :=
      { ramNextEpoch := 0, store := { keyId := [0x42], burns := [], poisoned := false } }
    (durableBurnReserve ephemeralBeforeCrash.store 1 0 [0xAA] 0 true).1 = true ∧
    (durableBurnReserve afterWipedDiskCrash.store 1 0 [0xBB] 0 true).1 = true ∧
    recoverSignerEpoch
      { ramNextEpoch := 0
        store := (durableBurnReserve ephemeralBeforeCrash.store 1 0 [0xAA] 0 true).2 } 1 =
      { ramNextEpoch := 1
        store := (durableBurnReserve ephemeralBeforeCrash.store 1 0 [0xAA] 0 true).2 } := by
  decide

/-- **`#tooth` (`tooth_ignoring_session_attempt_permits_duplicate_attempt`)**:
    A defective burn filter checking ONLY `row.epoch >= epoch` (ignoring `(sessionId, attempt)`)
    accepts a replay of the exact same `(sessionId = [0xAA], attempt = 0)` at `epoch = 1`, whereas
    `durableBurnAvailable` deterministically rejects it (`= false`)! -/
theorem tooth_ignoring_session_attempt_permits_duplicate_attempt :
    let s0 : DurableNonceBurnStore := { keyId := [0x42], burns := [], poisoned := false }
    let s1 := (durableBurnReserve s0 1 0 [0xAA] 0 true).2
    let buggyEpochOnlyCheck (st : DurableNonceBurnStore) (pid : UInt16) (ep : UInt64) : Bool :=
      st.burns.all (fun r => !(decide (r.keyId = st.keyId) && decide (r.partyId = pid) && decide (ep.toNat ≤ r.epoch.toNat)))
    buggyEpochOnlyCheck s1 1 1 = true ∧
    durableBurnAvailable s1 1 1 [0xAA] 0 = false := by
  decide

/-- **Theorem 5 (`threshold_mldsa_nonce_reuse_extracts_sk_and_typestate_prevents`)**:
    1. **Threshold RSS Share Reconstruction & Nonce-Reuse Key Extraction**:
       Summing custodian subset shares `rssSubsetResponses c yShares s1Shares` equals
       `mldsaLinearResponse (sum yShares) c (sum s1Shares)`, and reusing the masking shares `yShares`
       across ANY two challenges `c₁, c₂` with invertible `c₁ - c₂` cancels every RSS mask and recovers
       the full long-term secret `ringSumList s1Shares` in 1 subtraction!
    2. **Crash-Persistent Multi-Session Non-Reuse (`FsNonceBurnStore` + `recoverSignerEpoch`)**:
       Across EVERY reachable trace `ValidPersistentNonceTrace` (arbitrarily interleaving accepted
       signatures, norm-rejected retries, disk-failure poisonings, and RAM-wiping OS crashes),
       every pair of permitted attempts has strictly increasing `epoch` AND distinct `(sessionId, attempt)`! -/
theorem threshold_mldsa_nonce_reuse_extracts_sk_and_typestate_prevents :
    (∀ {R : Type} [LawfulCommRing R] (yShares s1Shares : List R) (c₁ c₂ invDiff : R),
      yShares.length = s1Shares.length →
      let z₁ := ringSumList (rssSubsetResponses c₁ yShares s1Shares)
      let z₂ := ringSumList (rssSubsetResponses c₂ yShares s1Shares)
      CommRingOps.sub z₁ z₂ =
        CommRingOps.mul (CommRingOps.sub c₁ c₂) (ringSumList s1Shares) ∧
      (CommRingOps.mul invDiff (CommRingOps.sub c₁ c₂) = CommRingOps.one →
        CommRingOps.mul invDiff (CommRingOps.sub z₁ z₂) = ringSumList s1Shares)) ∧
    (∀ (partyId : UInt16) (st₀ st₂ : SignerCrashState) (trace : List PersistentNonceEvent),
      ValidPersistentNonceTrace partyId st₀ trace st₂ →
      trace.Pairwise (fun e₁ e₂ =>
        e₁.epoch.toNat < e₂.epoch.toNat ∧
        e₁.epoch ≠ e₂.epoch ∧
        (e₁.sessionId, e₁.attempt) ≠ (e₂.sessionId, e₂.attempt))) := by
  refine ⟨?_, ?_⟩
  · intro R _ yShares s1Shares c₁ c₂ invDiff hLen
    dsimp only
    rw [rssSubsetResponses_sum c₁ yShares s1Shares hLen,
        rssSubsetResponses_sum c₂ yShares s1Shares hLen]
    let y := ringSumList yShares
    let s₁ := ringSumList s1Shares
    have hDiff :
        CommRingOps.sub (mldsaLinearResponse y c₁ s₁) (mldsaLinearResponse y c₂ s₁) =
          CommRingOps.mul (CommRingOps.sub c₁ c₂) s₁ := by
      unfold mldsaLinearResponse
      rw [LawfulCommRing.sub_eq_add_neg,
          LawfulCommRing.add_comm y (CommRingOps.mul c₁ s₁)]
      have hNegAdd :
          CommRingOps.neg (CommRingOps.add y (CommRingOps.mul c₂ s₁)) =
            CommRingOps.add (CommRingOps.neg y) (CommRingOps.neg (CommRingOps.mul c₂ s₁)) := by
        apply LawfulCommRing.add_left_cancel (a := CommRingOps.add y (CommRingOps.mul c₂ s₁))
        rw [LawfulCommRing.add_right_neg,
            LawfulCommRing.add_add_add_comm,
            LawfulCommRing.add_right_neg,
            LawfulCommRing.add_right_neg,
            LawfulCommRing.add_zero]
      rw [hNegAdd,
          LawfulCommRing.add_assoc,
          ← LawfulCommRing.add_assoc y (CommRingOps.neg y) _,
          LawfulCommRing.add_right_neg,
          LawfulCommRing.zero_add,
          ← LawfulCommRing.neg_mul,
          ← LawfulCommRing.right_distrib,
          ← LawfulCommRing.sub_eq_add_neg]
    refine ⟨hDiff, ?_⟩
    intro hInv
    rw [hDiff, ← LawfulCommRing.mul_assoc, hInv, LawfulCommRing.one_mul]
  · intro partyId st₀ st₂ trace hTr
    exact (validPersistentTrace_event_conflict_free hTr).2

/-! ## 6. Concrete Limb/Karatsuba/Butterfly `AcceleratorBackend` `Spec ↔ Exec` Refinement -/

/-- Functional specification of the 6 batch kernels in `qsag_accel::AcceleratorBackend`. -/
structure AcceleratorBackendSpec where
  batchKeccakF1600 : List (List UInt64) → List (List UInt64)
  batchPoseidon2Perm12 : List (List Goldilocks) → List (List Goldilocks)
  goldilocksNtt : List Goldilocks → List Goldilocks → Bool → List Goldilocks
  cosetLdeExt2 : List (Goldilocks × Goldilocks) → Nat → Goldilocks → List (Goldilocks × Goldilocks)
  merkleLayerPoseidon2At : List (List Goldilocks) → List Goldilocks → Nat → Nat → List (List Goldilocks)
  bdozGf2128BatchDot : List (BitVec 128 × BitVec 128) → List (BitVec 128 × BitVec 128) → (BitVec 128 × BitVec 128)

/-- Pointwise behavioral refinement relation between an `Exec` hardware/SIMD backend and a `Spec` backend. -/
@[expose] def AcceleratorSimulates (hw cpuRef : AcceleratorBackendSpec) : Prop :=
  (∀ states, hw.batchKeccakF1600 states = cpuRef.batchKeccakF1600 states) ∧
  (∀ states, hw.batchPoseidon2Perm12 states = cpuRef.batchPoseidon2Perm12 states) ∧
  (∀ buf tw inv, hw.goldilocksNtt buf tw inv = cpuRef.goldilocksNtt buf tw inv) ∧
  (∀ evals blowup shift, hw.cosetLdeExt2 evals blowup shift = cpuRef.cosetLdeExt2 evals blowup shift) ∧
  (∀ children pkSeed layer startIdx,
    hw.merkleLayerPoseidon2At children pkSeed layer startIdx =
      cpuRef.merkleLayerPoseidon2At children pkSeed layer startIdx) ∧
  (∀ shares weights, hw.bdozGf2128BatchDot shares weights = cpuRef.bdozGf2128BatchDot shares weights)

/-- Ascending coefficient representation (`Spec` polynomial evaluator). -/
def hornerEval {R : Type} [CommRingOps R] : List R → R → R
  | [], _ => CommRingOps.zero
  | c :: cs, x => CommRingOps.add c (CommRingOps.mul x (hornerEval cs x))

/-- Coefficient `i` is multiplied by `gamma^i` (`Exec` coset pre-scaler). -/
def scalePowers {R : Type} [CommRingOps R] : List R → R → List R
  | [], _ => []
  | c :: cs, gamma => c :: (scalePowers cs gamma).map (CommRingOps.mul gamma)

private theorem hornerEval_scale {R : Type} [LawfulCommRing R]
    (cs : List R) (gamma x : R) :
    hornerEval (cs.map (CommRingOps.mul gamma)) x =
      CommRingOps.mul gamma (hornerEval cs x) := by
  induction cs with
  | nil => simp only [List.map_nil, hornerEval, LawfulCommRing.mul_zero]
  | cons c cs ih =>
    simp only [List.map_cons, hornerEval, ih, LawfulCommRing.left_distrib]
    rw [← LawfulCommRing.mul_assoc x gamma, LawfulCommRing.mul_comm x gamma,
      LawfulCommRing.mul_assoc]

theorem hornerEval_cosetShift_eq {R : Type} [LawfulCommRing R]
    (coeffs : List R) (gamma x : R) :
    hornerEval (scalePowers coeffs gamma) x =
      hornerEval coeffs (CommRingOps.mul gamma x) := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
    simp only [scalePowers, hornerEval, hornerEval_scale, ih]
    rw [← LawfulCommRing.mul_assoc x gamma, LawfulCommRing.mul_comm x gamma]

theorem cosetShift_spec_iff_exec {R : Type} [LawfulCommRing R]
    (coeffs : List R) (gamma x value : R) :
    hornerEval (scalePowers coeffs gamma) x = value ↔
      hornerEval coeffs (CommRingOps.mul gamma x) = value := by
  rw [hornerEval_cosetShift_eq]

/-! ### 6.1 Concrete Kernel 1: Cooley-Tukey Even/Odd Radix-2 Butterfly NTT vs Direct `hornerEval` -/

/-- Extract even-index coefficients `[c_0, c_2, c_4, ...]` for Cooley-Tukey radix-2 split. -/
def evenCoeffs {R : Type} : List R → List R
  | [] => []
  | [c0] => [c0]
  | c0 :: _ :: rest => c0 :: evenCoeffs rest

/-- Extract odd-index coefficients `[c_1, c_3, c_5, ...]` for Cooley-Tukey radix-2 split. -/
def oddCoeffs {R : Type} : List R → List R
  | [] => []
  | [_] => []
  | _ :: c1 :: rest => c1 :: oddCoeffs rest

/-- **Cooley-Tukey Radix-2 Butterfly Identity (`hornerEval_eq_even_add_mul_odd`)**:
    Over EVERY `LawfulCommRing R`, direct Horner evaluation `P(x)` equals the radix-2 butterfly
    combination `E(x^2) + x * O(x^2)`! -/
theorem hornerEval_eq_even_add_mul_odd {R : Type} [LawfulCommRing R] :
    ∀ (coeffs : List R) (x : R),
      hornerEval coeffs x =
        CommRingOps.add
          (hornerEval (evenCoeffs coeffs) (CommRingOps.mul x x))
          (CommRingOps.mul x (hornerEval (oddCoeffs coeffs) (CommRingOps.mul x x)))
  | [], x => by
    simp [evenCoeffs, oddCoeffs, hornerEval, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | [c0], x => by
    simp [evenCoeffs, oddCoeffs, hornerEval, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | c0 :: c1 :: rest, x => by
    have ih := hornerEval_eq_even_add_mul_odd rest x
    simp only [evenCoeffs, oddCoeffs, hornerEval]
    rw [ih]
    let E := hornerEval (evenCoeffs rest) (CommRingOps.mul x x)
    let O := hornerEval (oddCoeffs rest) (CommRingOps.mul x x)
    let xx := CommRingOps.mul x x
    change CommRingOps.add c0 (CommRingOps.mul x (CommRingOps.add c1
        (CommRingOps.mul x (CommRingOps.add E (CommRingOps.mul x O))))) =
      CommRingOps.add (CommRingOps.add c0 (CommRingOps.mul xx E))
        (CommRingOps.mul x (CommRingOps.add c1 (CommRingOps.mul xx O)))
    rw [LawfulCommRing.left_distrib x c1 _,
        LawfulCommRing.left_distrib x E (CommRingOps.mul x O),
        LawfulCommRing.left_distrib x (CommRingOps.mul x E) (CommRingOps.mul x (CommRingOps.mul x O)),
        ← LawfulCommRing.mul_assoc x x E,
        ← LawfulCommRing.mul_assoc x x (CommRingOps.mul x O),
        LawfulCommRing.left_distrib x c1 (CommRingOps.mul xx O),
        ← LawfulCommRing.mul_assoc x xx O,
        LawfulCommRing.mul_comm x xx,
        LawfulCommRing.mul_assoc xx x O]
    change CommRingOps.add c0 (CommRingOps.add (CommRingOps.mul x c1)
        (CommRingOps.add (CommRingOps.mul xx E) (CommRingOps.mul xx (CommRingOps.mul x O)))) =
      CommRingOps.add (CommRingOps.add c0 (CommRingOps.mul xx E))
        (CommRingOps.add (CommRingOps.mul x c1) (CommRingOps.mul xx (CommRingOps.mul x O)))
    rw [LawfulCommRing.add_assoc c0 (CommRingOps.mul xx E) _,
        ← LawfulCommRing.add_assoc (CommRingOps.mul xx E) (CommRingOps.mul x c1) _,
        LawfulCommRing.add_comm (CommRingOps.mul xx E) (CommRingOps.mul x c1),
        LawfulCommRing.add_assoc (CommRingOps.mul x c1) (CommRingOps.mul xx E) _]

/-- Legacy point-evaluation helper. `inv` negates evaluation points; it is NOT an
    inverse NTT. The name is retained for callers of the accelerator model. -/
def goldilocksNttSpec (buf twiddles : List Goldilocks) (inv : Bool) : List Goldilocks :=
  twiddles.map (fun w =>
    let pt := if inv then Goldilocks.neg w else w
    hornerEval buf pt)

/-- `Exec` NTT kernel: Cooley-Tukey even/odd split + hardware 128-to-64 shift-mask `goldilocksReduce128Spec`
    butterfly `E(pt^2) + pt * O(pt^2)`. -/
def glMulShiftMaskExec (a b : Goldilocks) : Goldilocks :=
  let prod := a.val * b.val
  let lo := prod % (2 ^ 64)
  let hi := prod / (2 ^ 64)
  have hLo : lo < 2 ^ 64 := Nat.mod_lt prod (by decide)
  have hHi : hi < 2 ^ 64 :=
    Goldilocks.div64_lt_of_lt_square _
      (Nat.mul_lt_mul'' (Goldilocks.val_lt_two_pow_64 a) (Goldilocks.val_lt_two_pow_64 b))
  ⟨goldilocksReduce128Spec lo hi, (goldilocksReduce128Spec_sound hLo hHi).1⟩

theorem glMulShiftMaskExec_eq_mul (a b : Goldilocks) :
    glMulShiftMaskExec a b = CommRingOps.mul a b := by rfl

def goldilocksNttButterflyExec (buf twiddles : List Goldilocks) (inv : Bool) : List Goldilocks :=
  let evens := evenCoeffs buf
  let odds := oddCoeffs buf
  twiddles.map (fun w =>
    let pt := if inv then Goldilocks.neg w else w
    let ptSq := glMulShiftMaskExec pt pt
    let eVal := hornerEval evens ptSq
    let oVal := hornerEval odds ptSq
    Goldilocks.add eVal (glMulShiftMaskExec pt oVal))

theorem goldilocksNttButterflyExec_refines_spec (buf twiddles : List Goldilocks) (inv : Bool) :
    goldilocksNttButterflyExec buf twiddles inv = goldilocksNttSpec buf twiddles inv := by
  unfold goldilocksNttButterflyExec goldilocksNttSpec
  apply List.map_congr_left
  intro w _
  dsimp only
  let pt := if inv then Goldilocks.neg w else w
  change CommRingOps.add
      (hornerEval (evenCoeffs buf) (CommRingOps.mul pt pt))
      (CommRingOps.mul pt (hornerEval (oddCoeffs buf) (CommRingOps.mul pt pt))) =
    hornerEval buf pt
  exact (hornerEval_eq_even_add_mul_odd buf pt).symm

/-! ### 6.2 Concrete Kernel 2: 3-Mul Karatsuba `GoldilocksExt2` + Coset Pre-Scaling vs 4-Mul Schoolbook -/

def ext2NonResidue7 : Goldilocks := Goldilocks.ofNat 7

def ext2ZeroSpec : GoldilocksExt2 := ⟨Goldilocks.zero, Goldilocks.zero⟩

def ext2OfBaseSpec (a : Goldilocks) : GoldilocksExt2 := ⟨a, Goldilocks.zero⟩

def ext2AddSpec (a b : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨Goldilocks.add a.c0 b.c0, Goldilocks.add a.c1 b.c1⟩

def ext2ScaleBase (g : Goldilocks) (z : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨Goldilocks.mul g z.c0, Goldilocks.mul g z.c1⟩

/-- Textbook 4-multiplication schoolbook product in $\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$:
    computes `(a0*b0 + 7*(a1*b1), a0*b1 + a1*b0)` using 4 base-field products (`Spec`). -/
def ext2MulSchoolbookSpec (a b : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨Goldilocks.add (Goldilocks.mul a.c0 b.c0)
      (Goldilocks.mul ext2NonResidue7 (Goldilocks.mul a.c1 b.c1)),
   Goldilocks.add (Goldilocks.mul a.c0 b.c1) (Goldilocks.mul a.c1 b.c0)⟩

/-- 3-multiplication Karatsuba product in $\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$:
    computes `v0 = a0*b0`, `v1 = a1*b1`, `vSum = (a0+a1)*(b0+b1)`, returning
    `(v0 + 7*v1, vSum - v0 - v1)` using 3 general products instead of 4 schoolbook products! -/
def ext2MulKaratsubaExec (a b : GoldilocksExt2) : GoldilocksExt2 :=
  let v0 := glMulShiftMaskExec a.c0 b.c0
  let v1 := glMulShiftMaskExec a.c1 b.c1
  let sumA := Goldilocks.add a.c0 a.c1
  let sumB := Goldilocks.add b.c0 b.c1
  let vSum := glMulShiftMaskExec sumA sumB
  let c0 := Goldilocks.add v0 (glMulShiftMaskExec ext2NonResidue7 v1)
  let c1 := Goldilocks.sub (Goldilocks.sub vSum v0) v1
  ⟨c0, c1⟩

theorem ext2MulKaratsubaExec_eq_schoolbook (a b : GoldilocksExt2) :
    ext2MulKaratsubaExec a b = ext2MulSchoolbookSpec a b := by
  apply GoldilocksExt2.ext
  · rfl
  · unfold ext2MulKaratsubaExec ext2MulSchoolbookSpec
    dsimp only
    change CommRingOps.sub
        (CommRingOps.sub
          (CommRingOps.mul (CommRingOps.add a.c0 a.c1) (CommRingOps.add b.c0 b.c1))
          (CommRingOps.mul a.c0 b.c0))
        (CommRingOps.mul a.c1 b.c1) =
      CommRingOps.add (CommRingOps.mul a.c0 b.c1) (CommRingOps.mul a.c1 b.c0)
    rw [LawfulCommRing.right_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
    let p00 := CommRingOps.mul a.c0 b.c0
    let p01 := CommRingOps.mul a.c0 b.c1
    let p10 := CommRingOps.mul a.c1 b.c0
    let p11 := CommRingOps.mul a.c1 b.c1
    change CommRingOps.sub
        (CommRingOps.sub (CommRingOps.add (CommRingOps.add p00 p01) (CommRingOps.add p10 p11)) p00)
        p11 = CommRingOps.add p01 p10
    have h1 : CommRingOps.sub
        (CommRingOps.add (CommRingOps.add p00 p01) (CommRingOps.add p10 p11)) p00 =
        CommRingOps.add p11 (CommRingOps.add p01 p10) := by
      apply LawfulCommRing.add_left_cancel (a := p00)
      rw [LawfulCommRing.add_sub_cancel_left]
      simp only [LawfulCommRing.add_assoc, LawfulCommRing.add_comm]
    rw [h1]
    apply LawfulCommRing.add_left_cancel (a := p11)
    rw [LawfulCommRing.add_sub_cancel_left]

private theorem ext2MulSchoolbookSpec_ofBase (g : Goldilocks) (x : GoldilocksExt2) :
    ext2MulSchoolbookSpec (ext2OfBaseSpec g) x = ext2ScaleBase g x := by
  apply GoldilocksExt2.ext
  · unfold ext2MulSchoolbookSpec ext2OfBaseSpec ext2ScaleBase
    dsimp only
    change CommRingOps.add (CommRingOps.mul g x.c0)
      (CommRingOps.mul ext2NonResidue7 (CommRingOps.mul CommRingOps.zero x.c1)) =
      CommRingOps.mul g x.c0
    rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  · unfold ext2MulSchoolbookSpec ext2OfBaseSpec ext2ScaleBase
    dsimp only
    change CommRingOps.add (CommRingOps.mul g x.c1) (CommRingOps.mul CommRingOps.zero x.c0) =
      CommRingOps.mul g x.c1
    rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

private theorem ext2ScaleBase_mul_left (g : Goldilocks) (x y : GoldilocksExt2) :
    ext2MulSchoolbookSpec (ext2ScaleBase g x) y =
      ext2ScaleBase g (ext2MulSchoolbookSpec x y) := by
  apply GoldilocksExt2.ext
  · unfold ext2MulSchoolbookSpec ext2ScaleBase
    dsimp only
    change CommRingOps.add
        (CommRingOps.mul (CommRingOps.mul g x.c0) y.c0)
        (CommRingOps.mul ext2NonResidue7 (CommRingOps.mul (CommRingOps.mul g x.c1) y.c1)) =
      CommRingOps.mul g
        (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
          (CommRingOps.mul ext2NonResidue7 (CommRingOps.mul x.c1 y.c1)))
    rw [LawfulCommRing.left_distrib,
        LawfulCommRing.mul_assoc g x.c0 y.c0,
        LawfulCommRing.mul_assoc g x.c1 y.c1,
        ← LawfulCommRing.mul_assoc ext2NonResidue7 g _,
        LawfulCommRing.mul_comm ext2NonResidue7 g,
        LawfulCommRing.mul_assoc g ext2NonResidue7 _]
  · unfold ext2MulSchoolbookSpec ext2ScaleBase
    dsimp only
    change CommRingOps.add
        (CommRingOps.mul (CommRingOps.mul g x.c0) y.c1)
        (CommRingOps.mul (CommRingOps.mul g x.c1) y.c0) =
      CommRingOps.mul g
        (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0))
    rw [LawfulCommRing.left_distrib,
        LawfulCommRing.mul_assoc g x.c0 y.c1,
        LawfulCommRing.mul_assoc g x.c1 y.c0]

private theorem ext2ScaleBase_mul_right (g : Goldilocks) (x y : GoldilocksExt2) :
    ext2MulSchoolbookSpec x (ext2ScaleBase g y) =
      ext2ScaleBase g (ext2MulSchoolbookSpec x y) := by
  apply GoldilocksExt2.ext
  · unfold ext2MulSchoolbookSpec ext2ScaleBase
    dsimp only
    change CommRingOps.add
        (CommRingOps.mul x.c0 (CommRingOps.mul g y.c0))
        (CommRingOps.mul ext2NonResidue7 (CommRingOps.mul x.c1 (CommRingOps.mul g y.c1))) =
      CommRingOps.mul g
        (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
          (CommRingOps.mul ext2NonResidue7 (CommRingOps.mul x.c1 y.c1)))
    rw [LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc x.c0 g y.c0,
        LawfulCommRing.mul_comm x.c0 g,
        LawfulCommRing.mul_assoc g x.c0 y.c0,
        ← LawfulCommRing.mul_assoc x.c1 g y.c1,
        LawfulCommRing.mul_comm x.c1 g,
        LawfulCommRing.mul_assoc g x.c1 y.c1,
        ← LawfulCommRing.mul_assoc ext2NonResidue7 g _,
        LawfulCommRing.mul_comm ext2NonResidue7 g,
        LawfulCommRing.mul_assoc g ext2NonResidue7 _]
  · unfold ext2MulSchoolbookSpec ext2ScaleBase
    dsimp only
    change CommRingOps.add
        (CommRingOps.mul x.c0 (CommRingOps.mul g y.c1))
        (CommRingOps.mul x.c1 (CommRingOps.mul g y.c0)) =
      CommRingOps.mul g
        (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0))
    rw [LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc x.c0 g y.c1,
        LawfulCommRing.mul_comm x.c0 g,
        LawfulCommRing.mul_assoc g x.c0 y.c1,
        ← LawfulCommRing.mul_assoc x.c1 g y.c0,
        LawfulCommRing.mul_comm x.c1 g,
        LawfulCommRing.mul_assoc g x.c1 y.c0]

private theorem ext2ScaleBase_add (g : Goldilocks) (a b : GoldilocksExt2) :
    ext2ScaleBase g (ext2AddSpec a b) = ext2AddSpec (ext2ScaleBase g a) (ext2ScaleBase g b) := by
  apply GoldilocksExt2.ext
  · exact LawfulCommRing.left_distrib g a.c0 b.c0
  · exact LawfulCommRing.left_distrib g a.c1 b.c1

def hornerEvalExt2Schoolbook : List GoldilocksExt2 → GoldilocksExt2 → GoldilocksExt2
  | [], _ => ext2ZeroSpec
  | c :: cs, x => ext2AddSpec c (ext2MulSchoolbookSpec x (hornerEvalExt2Schoolbook cs x))

def hornerEvalExt2Karatsuba : List GoldilocksExt2 → GoldilocksExt2 → GoldilocksExt2
  | [], _ => ext2ZeroSpec
  | c :: cs, x => ext2AddSpec c (ext2MulKaratsubaExec x (hornerEvalExt2Karatsuba cs x))

def scalePowersExt2Base : List GoldilocksExt2 → Goldilocks → List GoldilocksExt2
  | [], _ => []
  | c :: cs, gamma => c :: (scalePowersExt2Base cs gamma).map (ext2ScaleBase gamma)

theorem hornerEvalExt2Karatsuba_eq_schoolbook (coeffs : List GoldilocksExt2) (x : GoldilocksExt2) :
    hornerEvalExt2Karatsuba coeffs x = hornerEvalExt2Schoolbook coeffs x := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
    simp only [hornerEvalExt2Karatsuba, hornerEvalExt2Schoolbook, ih,
      ext2MulKaratsubaExec_eq_schoolbook]

private theorem hornerEvalExt2Schoolbook_scaleBase
    (cs : List GoldilocksExt2) (gamma : Goldilocks) (x : GoldilocksExt2) :
    hornerEvalExt2Schoolbook (cs.map (ext2ScaleBase gamma)) x =
      ext2ScaleBase gamma (hornerEvalExt2Schoolbook cs x) := by
  induction cs with
  | nil =>
    apply GoldilocksExt2.ext <;> exact (LawfulCommRing.mul_zero gamma).symm
  | cons c cs ih =>
    simp only [List.map_cons, hornerEvalExt2Schoolbook, ih,
      ext2ScaleBase_mul_right, ext2ScaleBase_add]

private theorem hornerEvalExt2Schoolbook_cosetShift
    (coeffs : List GoldilocksExt2) (gamma : Goldilocks) (x : GoldilocksExt2) :
    hornerEvalExt2Schoolbook (scalePowersExt2Base coeffs gamma) x =
      hornerEvalExt2Schoolbook coeffs (ext2MulSchoolbookSpec (ext2OfBaseSpec gamma) x) := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
    simp only [scalePowersExt2Base, hornerEvalExt2Schoolbook,
      hornerEvalExt2Schoolbook_scaleBase, ih, ext2MulSchoolbookSpec_ofBase,
      ext2ScaleBase_mul_left, ext2ScaleBase_mul_right]

def cosetDomainPoints (blowup : Nat) : List GoldilocksExt2 :=
  (List.range blowup).map (fun i => ext2OfBaseSpec (Goldilocks.ofNat (i + 1)))

/-- Legacy Horner evaluation at consecutive shifted points. The input is treated
    as coefficients and `blowup` is the output count; this is not a coset LDE. -/
def cosetLdeExt2Spec (evals : List (Goldilocks × Goldilocks)) (blowup : Nat) (shift : Goldilocks) :
    List (Goldilocks × Goldilocks) :=
  let coeffs := evals.map (fun p => (⟨p.1, p.2⟩ : GoldilocksExt2))
  let shiftExt := ext2OfBaseSpec shift
  (cosetDomainPoints blowup).map (fun x =>
    let y := hornerEvalExt2Schoolbook coeffs (ext2MulSchoolbookSpec shiftExt x)
    (y.c0, y.c1))

/-- `Exec` Coset LDE: pre-scales coefficients once via `scalePowersExt2Base` and evaluates on unshifted points `x`
    using 3-mul `ext2MulKaratsubaExec`! -/
def cosetLdeExt2KaratsubaExec (evals : List (Goldilocks × Goldilocks)) (blowup : Nat) (shift : Goldilocks) :
    List (Goldilocks × Goldilocks) :=
  let coeffs := evals.map (fun p => (⟨p.1, p.2⟩ : GoldilocksExt2))
  let scaled := scalePowersExt2Base coeffs shift
  (cosetDomainPoints blowup).map (fun x =>
    let y := hornerEvalExt2Karatsuba scaled x
    (y.c0, y.c1))

theorem cosetLdeExt2KaratsubaExec_refines_spec
    (evals : List (Goldilocks × Goldilocks)) (blowup : Nat) (shift : Goldilocks) :
    cosetLdeExt2KaratsubaExec evals blowup shift = cosetLdeExt2Spec evals blowup shift := by
  unfold cosetLdeExt2KaratsubaExec cosetLdeExt2Spec
  apply List.map_congr_left
  intro x _
  dsimp only
  rw [hornerEvalExt2Karatsuba_eq_schoolbook, hornerEvalExt2Schoolbook_cosetShift]

/-! ### 6.3 Concrete Kernel 3: Packed `BitVec 128` Carryless Karatsuba `GF(2^128)` Inner Product vs `Tower128` -/

/-- `Spec` 2-lane `GF(2^128)` inner product over algebraic Wiedemann `Tower128` (`TowerElem 7`). -/
def gf2128BatchDotSpec :
    List (BitVec 128 × BitVec 128) → List (BitVec 128 × BitVec 128) → (BitVec 128 × BitVec 128)
  | (s0, s1) :: ss, (w0, w1) :: ws =>
    let rest := gf2128BatchDotSpec ss ws
    let p0 := towerAdd 7 (towerMul 7 (unpackTower 7 s0) (unpackTower 7 w0)) (unpackTower 7 rest.1)
    let p1 := towerAdd 7 (towerMul 7 (unpackTower 7 s1) (unpackTower 7 w1)) (unpackTower 7 rest.2)
    (packTower 7 p0, packTower 7 p1)
  | _, _ => (0#128, 0#128)

/-- `Exec` 2-lane `GF(2^128)` inner product using packed 128-bit BitVec XOR (`^^^`) and recursive
    bit-sliced Karatsuba `mulExec 7`! -/
def gf2128BatchDotExec :
    List (BitVec 128 × BitVec 128) → List (BitVec 128 × BitVec 128) → (BitVec 128 × BitVec 128)
  | (s0, s1) :: ss, (w0, w1) :: ws =>
    let rest := gf2128BatchDotExec ss ws
    (mulExec 7 s0 w0 ^^^ rest.1, mulExec 7 s1 w1 ^^^ rest.2)
  | _, _ => (0#128, 0#128)

theorem gf2128BatchDotExec_refines_spec :
    ∀ (shares weights : List (BitVec 128 × BitVec 128)),
      gf2128BatchDotExec shares weights = gf2128BatchDotSpec shares weights
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (s0, s1) :: ss, (w0, w1) :: ws => by
    simp only [gf2128BatchDotExec, gf2128BatchDotSpec, gf2128BatchDotExec_refines_spec ss ws]
    have hMul0 : mulExec 7 s0 w0 = packTower 7 (towerMul 7 (unpackTower 7 s0) (unpackTower 7 w0)) := by
      conv => lhs; rw [← packTower_unpackTower 7 s0, ← packTower_unpackTower 7 w0]
      exact mulExec_refines 7 (unpackTower 7 s0) (unpackTower 7 w0)
    have hMul1 : mulExec 7 s1 w1 = packTower 7 (towerMul 7 (unpackTower 7 s1) (unpackTower 7 w1)) := by
      conv => lhs; rw [← packTower_unpackTower 7 s1, ← packTower_unpackTower 7 w1]
      exact mulExec_refines 7 (unpackTower 7 s1) (unpackTower 7 w1)
    rw [hMul0, hMul1, packTower_add 7, packTower_add 7,
        packTower_unpackTower 7, packTower_unpackTower 7]

/-! ### 6.4 Concrete `Keccak`, `Poseidon2`, and Merkle Layer `Spec` vs `Exec` Backends -/

def packKState25 (xs : List UInt64) : KState :=
  let g (i : Nat) := (xs[i]?).getD 0
  ⟨g 0, g 1, g 2, g 3, g 4,
   g 5, g 6, g 7, g 8, g 9,
   g 10, g 11, g 12, g 13, g 14,
   g 15, g 16, g 17, g 18, g 19,
   g 20, g 21, g 22, g 23, g 24⟩

def unpackKState25 (s : KState) : List UInt64 :=
  [s.a0, s.a1, s.a2, s.a3, s.a4,
   s.a5, s.a6, s.a7, s.a8, s.a9,
   s.a10, s.a11, s.a12, s.a13, s.a14,
   s.a15, s.a16, s.a17, s.a18, s.a19,
   s.a20, s.a21, s.a22, s.a23, s.a24]

def packState12 (xs : List Goldilocks) : Poseidon2State12 :=
  let g (i : Nat) := (xs[i]?).getD Goldilocks.zero
  ⟨⟨g 0, g 1, g 2, g 3⟩, ⟨g 4, g 5, g 6, g 7⟩, ⟨g 8, g 9, g 10, g 11⟩⟩

def unpackState12 (s : Poseidon2State12) : List Goldilocks :=
  [s.b0.x0, s.b0.x1, s.b0.x2, s.b0.x3,
   s.b1.x0, s.b1.x1, s.b1.x2, s.b1.x3,
   s.b2.x0, s.b2.x1, s.b2.x2, s.b2.x3]

def merklePairCompress (left right pkSeed : List Goldilocks) (layer idx : Nat) : List Goldilocks :=
  let gL (i : Nat) := (left[i]?).getD Goldilocks.zero
  let gR (i : Nat) := (right[i]?).getD Goldilocks.zero
  let s0 := (pkSeed[0]?).getD Goldilocks.zero
  let s1 := (pkSeed[1]?).getD Goldilocks.zero
  let st : Poseidon2State12 :=
    ⟨⟨gL 0, gL 1, gL 2, gL 3⟩,
     ⟨gR 0, gR 1, gR 2, gR 3⟩,
     ⟨s0, s1, Goldilocks.ofNat layer, Goldilocks.ofNat idx⟩⟩
  let out := poseidon2Perm12 st
  [out.b0.x0, out.b0.x1, out.b0.x2, out.b0.x3]

def merkleLayerCompressAt : List (List Goldilocks) → List Goldilocks → Nat → Nat → List (List Goldilocks)
  | l :: r :: rest, pkSeed, layer, idx =>
    merklePairCompress l r pkSeed layer idx :: merkleLayerCompressAt rest pkSeed layer (idx + 1)
  | [single], pkSeed, layer, idx =>
    [merklePairCompress single [] pkSeed layer idx]
  | [], _, _, _ => []

/-- Tail-recursive accumulator `Exec` schedule for batch Merkle layer compression (matching iterative
    SIMD chunk loop vs recursive `merkleLayerCompressAt`). -/
def merkleLayerCompressLoop :
    List (List Goldilocks) → List Goldilocks → Nat → Nat → List (List Goldilocks) → List (List Goldilocks)
  | l :: r :: rest, pkSeed, layer, idx, acc =>
    merkleLayerCompressLoop rest pkSeed layer (idx + 1)
      (merklePairCompress l r pkSeed layer idx :: acc)
  | [single], pkSeed, layer, idx, acc =>
    (merklePairCompress single [] pkSeed layer idx :: acc).reverse
  | [], _, _, _, acc => acc.reverse

private theorem merkleLayerCompressLoop_eq
    (pkSeed : List Goldilocks) (layer : Nat) :
    ∀ (nodes : List (List Goldilocks)) (idx : Nat) (acc : List (List Goldilocks)),
      merkleLayerCompressLoop nodes pkSeed layer idx acc =
        acc.reverse ++ merkleLayerCompressAt nodes pkSeed layer idx
  | [], _, acc => by simp [merkleLayerCompressLoop, merkleLayerCompressAt]
  | [single], idx, acc => by
    simp [merkleLayerCompressLoop, merkleLayerCompressAt]
  | l :: r :: rest, idx, acc => by
    simp only [merkleLayerCompressLoop, merkleLayerCompressAt,
      merkleLayerCompressLoop_eq pkSeed layer rest (idx + 1)
        (merklePairCompress l r pkSeed layer idx :: acc),
      List.reverse_cons, List.append_assoc, List.singleton_append]

def batchKeccakSpec (states : List (List UInt64)) : List (List UInt64) :=
  states.map (fun st => unpackKState25 (keccakF1600 (packKState25 st)))

def batchKeccakLoop : List (List UInt64) → List (List UInt64) → List (List UInt64)
  | [], acc => acc.reverse
  | st :: rest, acc =>
    batchKeccakLoop rest (unpackKState25 (keccakF1600 (packKState25 st)) :: acc)

private theorem batchKeccakLoop_eq :
    ∀ (states acc : List (List UInt64)),
      batchKeccakLoop states acc = acc.reverse ++ batchKeccakSpec states
  | [], acc => by simp [batchKeccakLoop, batchKeccakSpec]
  | st :: rest, acc => by
    unfold batchKeccakLoop batchKeccakSpec
    rw [List.map_cons, batchKeccakLoop_eq rest _]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, batchKeccakSpec]

def batchPoseidon2Spec (states : List (List Goldilocks)) : List (List Goldilocks) :=
  states.map (fun st => unpackState12 (poseidon2Perm12 (packState12 st)))

def batchPoseidon2Loop : List (List Goldilocks) → List (List Goldilocks) → List (List Goldilocks)
  | [], acc => acc.reverse
  | st :: rest, acc =>
    batchPoseidon2Loop rest (unpackState12 (poseidon2Perm12 (packState12 st)) :: acc)

private theorem batchPoseidon2Loop_eq :
    ∀ (states acc : List (List Goldilocks)),
      batchPoseidon2Loop states acc = acc.reverse ++ batchPoseidon2Spec states
  | [], acc => by simp [batchPoseidon2Loop, batchPoseidon2Spec]
  | st :: rest, acc => by
    unfold batchPoseidon2Loop batchPoseidon2Spec
    rw [List.map_cons, batchPoseidon2Loop_eq rest _]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, batchPoseidon2Spec]

/-- Clean algebraic `CpuReferenceBackend` (`Spec`):
    uses direct `hornerEval` NTT, 4-mul schoolbook point-shifted `Ext2` LDE, and `Tower128` inner product. -/
def cpuSpecBackend : AcceleratorBackendSpec where
  batchKeccakF1600 := batchKeccakSpec
  batchPoseidon2Perm12 := batchPoseidon2Spec
  goldilocksNtt := goldilocksNttSpec
  cosetLdeExt2 := cosetLdeExt2Spec
  merkleLayerPoseidon2At := merkleLayerCompressAt
  bdozGf2128BatchDot := gf2128BatchDotSpec

/-- Concrete limb/SIMD `Exec` backend (`simdExecBackend`):
    uses iterative batch loops, Cooley-Tukey even/odd radix-2 butterfly + 128-to-64 shift-mask Goldilocks
    reduction, `scalePowersExt2Base` + 3-mul Karatsuba `Ext2` LDE, and packed `BitVec 128` `mulExec 7` inner product! -/
def simdExecBackend : AcceleratorBackendSpec where
  batchKeccakF1600 := fun states => batchKeccakLoop states []
  batchPoseidon2Perm12 := fun states => batchPoseidon2Loop states []
  goldilocksNtt := goldilocksNttButterflyExec
  cosetLdeExt2 := cosetLdeExt2KaratsubaExec
  merkleLayerPoseidon2At := fun children pkSeed layer startIdx =>
    merkleLayerCompressLoop children pkSeed layer startIdx []
  bdozGf2128BatchDot := gf2128BatchDotExec

/-- **Concrete Backend Refinement Theorem (`simdExec_simulates_cpuSpec`)**:
    Proves `AcceleratorSimulates simdExecBackend cpuSpecBackend` WITHOUT assuming `hw.f = cpuRef.f`! -/
theorem simdExec_simulates_cpuSpec : AcceleratorSimulates simdExecBackend cpuSpecBackend := by
  refine ⟨?_, ?_, goldilocksNttButterflyExec_refines_spec,
          cosetLdeExt2KaratsubaExec_refines_spec, ?_, gf2128BatchDotExec_refines_spec⟩
  · intro states
    simpa [simdExecBackend, cpuSpecBackend] using batchKeccakLoop_eq states []
  · intro states
    simpa [simdExecBackend, cpuSpecBackend] using batchPoseidon2Loop_eq states []
  · intro children pkSeed layer startIdx
    simpa [simdExecBackend, cpuSpecBackend] using
      merkleLayerCompressLoop_eq pkSeed layer children startIdx []

/-- **`#tooth` (`tooth_karatsuba_missing_cross_sub_corrupts_lde`)**:
    A buggy Karatsuba `Ext2` kernel omitting `- v0 - v1` on the imaginary limb computes
    `(1 + u) * (1 + u) = 8 + 4u` instead of `8 + 2u` (`u^2 = 7`), violating `ext2MulSchoolbookSpec`! -/
theorem tooth_karatsuba_missing_cross_sub_corrupts_lde :
    let u1 : GoldilocksExt2 := ⟨Goldilocks.one, Goldilocks.one⟩
    let buggyKaratsuba (a b : GoldilocksExt2) : GoldilocksExt2 :=
      let v0 := glMulShiftMaskExec a.c0 b.c0
      let v1 := glMulShiftMaskExec a.c1 b.c1
      let vSum := glMulShiftMaskExec (Goldilocks.add a.c0 a.c1) (Goldilocks.add b.c0 b.c1)
      ⟨Goldilocks.add v0 (glMulShiftMaskExec ext2NonResidue7 v1), vSum⟩
    ext2MulKaratsubaExec u1 u1 = ext2MulSchoolbookSpec u1 u1 ∧
    buggyKaratsuba u1 u1 ≠ ext2MulSchoolbookSpec u1 u1 := by
  intro u1 buggyKaratsuba
  refine ⟨ext2MulKaratsubaExec_eq_schoolbook u1 u1, ?_⟩
  intro hEq
  have hv := congrArg (fun z : GoldilocksExt2 => z.c1.val) hEq
  revert hv
  decide

/-- Upward traversal starts at layer zero and increments after each reduction. -/
def evalMerkleLayersFrom (backend : AcceleratorBackendSpec) (pkSeed : List Goldilocks) :
    Nat → Nat → List (List Goldilocks) → List (List Goldilocks)
  | 0, _, nodes => nodes
  | remaining + 1, layer, nodes =>
    evalMerkleLayersFrom backend pkSeed remaining (layer + 1)
      (backend.merkleLayerPoseidon2At nodes pkSeed layer 0)

def evalMerkleTreeLayers (backend : AcceleratorBackendSpec) (pkSeed : List Goldilocks)
    (treeDepth : Nat) (nodes : List (List Goldilocks)) : List (List Goldilocks) :=
  evalMerkleLayersFrom backend pkSeed treeDepth 0 nodes

def merkleLayerSchedule (treeDepth : Nat) : List Nat := List.range treeDepth

theorem merkleLayerSchedule_bounds (d layer : Nat) :
    layer ∈ merkleLayerSchedule d ↔ layer < d := List.mem_range

/-- Legacy composition of point-evaluation and Merkle helpers. This is not a
    verified BaseFold encoder: interpolation and multiplicative domains are absent. -/
def evalBaseFoldCommitPipeline
    (backend : AcceleratorBackendSpec)
    (polyBuf twiddles : List Goldilocks)
    (blowup treeDepth : Nat)
    (cosetShift : Goldilocks)
    (pkSeed : List Goldilocks) : List (List Goldilocks) :=
  let nttCoeffs := backend.goldilocksNtt polyBuf twiddles true
  let extPairs := nttCoeffs.map (fun c => (c, Goldilocks.zero))
  let ldeCodeword := backend.cosetLdeExt2 extPairs blowup cosetShift
  let codewordLeaves := ldeCodeword.map (fun p => [p.1, p.2, Goldilocks.zero, Goldilocks.zero])
  evalMerkleTreeLayers backend pkSeed treeDepth codewordLeaves

private theorem evalMerkleLayersFrom_simulates
    {hw cpuRef : AcceleratorBackendSpec} (hSim : AcceleratorSimulates hw cpuRef)
    (pkSeed : List Goldilocks) :
    ∀ (d layer : Nat) (nodes : List (List Goldilocks)),
      evalMerkleLayersFrom hw pkSeed d layer nodes =
        evalMerkleLayersFrom cpuRef pkSeed d layer nodes
  | 0, _, _ => rfl
  | d + 1, layer, nodes => by
    simp only [evalMerkleLayersFrom, hSim.2.2.2.2.1]
    exact evalMerkleLayersFrom_simulates hSim pkSeed d (layer + 1) _

private theorem evalMerkleTreeLayers_simulates
    {hw cpuRef : AcceleratorBackendSpec} (hSim : AcceleratorSimulates hw cpuRef)
    (pkSeed : List Goldilocks) (d : Nat) (nodes : List (List Goldilocks)) :
    evalMerkleTreeLayers hw pkSeed d nodes = evalMerkleTreeLayers cpuRef pkSeed d nodes :=
  evalMerkleLayersFrom_simulates hSim pkSeed d 0 nodes

theorem cosetShift_merkle_refines
    {hw cpuRef : AcceleratorBackendSpec} (hSim : AcceleratorSimulates hw cpuRef)
    (coeffs : List Goldilocks) (gamma : Goldilocks) (points pkSeed : List Goldilocks)
    (d : Nat) :
    evalMerkleTreeLayers hw pkSeed d
      (points.map (fun x => [hornerEval (scalePowers coeffs gamma) x])) =
    evalMerkleTreeLayers cpuRef pkSeed d
      (points.map (fun x => [hornerEval coeffs (CommRingOps.mul gamma x)])) := by
  simp only [hornerEval_cosetShift_eq]
  exact evalMerkleTreeLayers_simulates hSim pkSeed d _

/-- Agreement of the two executable arithmetic helper backends and their composition.
This establishes neither an inverse NTT nor BaseFold encoding nor collision resistance.
The last clause transports equality; its historical distinctness argument is redundant. -/
theorem accelerator_backend_simulation_sound :
    AcceleratorSimulates simdExecBackend cpuSpecBackend ∧
    (∀ (buf tw : List Goldilocks) (inv : Bool),
      goldilocksNttButterflyExec buf tw inv = goldilocksNttSpec buf tw inv) ∧
    (∀ (a b : GoldilocksExt2),
      ext2MulKaratsubaExec a b = ext2MulSchoolbookSpec a b) ∧
    (∀ (shares weights : List (BitVec 128 × BitVec 128)),
      gf2128BatchDotExec shares weights = gf2128BatchDotSpec shares weights) ∧
    (∀ polyBuf twiddles blowup treeDepth cosetShift pkSeed,
      evalBaseFoldCommitPipeline simdExecBackend polyBuf twiddles blowup treeDepth cosetShift pkSeed =
        evalBaseFoldCommitPipeline cpuSpecBackend polyBuf twiddles blowup treeDepth cosetShift pkSeed) ∧
    (∀ p1 p2 tw blowup d shift pkSeed,
      p1 ≠ p2 →
      evalBaseFoldCommitPipeline simdExecBackend p1 tw blowup d shift pkSeed =
        evalBaseFoldCommitPipeline simdExecBackend p2 tw blowup d shift pkSeed →
      evalBaseFoldCommitPipeline cpuSpecBackend p1 tw blowup d shift pkSeed =
        evalBaseFoldCommitPipeline cpuSpecBackend p2 tw blowup d shift pkSeed) := by
  have hSim := simdExec_simulates_cpuSpec
  have hPipe :
      ∀ polyBuf twiddles blowup treeDepth cosetShift pkSeed,
        evalBaseFoldCommitPipeline simdExecBackend polyBuf twiddles blowup treeDepth cosetShift pkSeed =
          evalBaseFoldCommitPipeline cpuSpecBackend polyBuf twiddles blowup treeDepth cosetShift pkSeed := by
    intro polyBuf twiddles blowup treeDepth cosetShift pkSeed
    simp only [evalBaseFoldCommitPipeline, hSim.2.2.1, hSim.2.2.2.1]
    exact evalMerkleTreeLayers_simulates hSim pkSeed treeDepth _
  refine ⟨hSim, goldilocksNttButterflyExec_refines_spec, ext2MulKaratsubaExec_eq_schoolbook,
          gf2128BatchDotExec_refines_spec, hPipe, ?_⟩
  intro p1 p2 tw blowup d shift pkSeed _ hCol
  rw [← hPipe p1, ← hPipe p2]
  exact hCol


/-! ## BlindVC wire boundary

These definitions follow `blind_vc.rs` and `keccak.rs`, rather than the historical
function-valued `PartyCredView`. Hash computations use the concrete Keccak module.
Signature verification remains an explicit cryptographic interface: pinning a key
is not a proof of ML-DSA unforgeability. Likewise, no claim of statistical hiding
is made for a deterministic Poseidon sponge with arbitrary secret attributes.
-/
namespace BlindVcWire

abbrev Bytes := List UInt8
abbrev Bytes32 := { bs : Bytes // bs.length = 32 }

def ascii (s : String) : Bytes := s.toUTF8.toList

def le (width n : Nat) : Bytes := (be width n).reverse

def words (xs : List Goldilocks) : Bytes := xs.flatMap (fun x => le 8 x.val)

def framed (frames : List Bytes) : Bytes :=
  le 8 frames.length ++ frames.flatMap (fun f => le 8 f.length ++ f)

def hashFrames (domain : String) (frames : List Bytes) : Bytes32 :=
  ⟨cshake256Bytes (ascii domain) (framed frames), cshake256Bytes_length _ _⟩

/-- Finite flat wire view. Counts cannot silently truncate to u32. Salt is a
separate commitment frame, not part of the SHAKE party-view digest. -/
structure PartyView where
  seed : Bytes32
  inputs : List Goldilocks
  gates : List Goldilocks
  outputs : List Goldilocks
  inputsBound : inputs.length < 2^32
  gatesBound : gates.length < 2^32
  outputsBound : outputs.length < 2^32

/-- Exact bytes absorbed by Rust `digest_party_view`, before SHAKE finalization. -/
def viewBytes (v : PartyView) : Bytes :=
  ascii "QSAG.VC.VIEW_COM.V1" ++ v.seed.val ++
  le 4 v.inputs.length ++ words v.inputs ++
  le 4 v.gates.length ++ words v.gates ++
  le 4 v.outputs.length ++ words v.outputs

def viewDigest (v : PartyView) : Bytes32 :=
  ⟨shake256Xof 32 (viewBytes v), shake256Xof_length _ _⟩

def commitmentFrames (sid : Bytes32) (round : UInt32) (party : Fin 3)
    (digest salt : Bytes32) : List Bytes :=
  [sid.val, le 4 round.toNat, le 2 party.val, digest.val, salt.val]

def commit (sid : Bytes32) (round : UInt32) (party : Fin 3)
    (v : PartyView) (salt : Bytes32) : Bytes32 :=
  hashFrames "QSAG.COMMIT.V1" (commitmentFrames sid round party (viewDigest v) salt)

theorem le_injective {width a b : Nat} (ha : a < 256^width) (hb : b < 256^width)
    (h : le width a = le width b) : a = b := by
  apply be_injective ha hb
  have hr := congrArg List.reverse h
  simpa [le] using hr

theorem words_length (xs : List Goldilocks) : (words xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (le 8 x.val ++ words xs).length = 8 * (xs.length + 1)
    rw [List.length_append, ih]
    simp [le, Nat.mul_add, Nat.add_comm]

theorem words_injective (xs ys : List Goldilocks) (h : words xs = words ys) : xs = ys := by
  have hl : xs.length = ys.length := by
    have := congrArg List.length h
    rw [words_length, words_length] at this
    omega
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      change le 8 x.val ++ words xs = le 8 y.val ++ words ys at h
      have hp := List.append_inj h (by simp [le])
      have hx : x = y := Goldilocks.ext (le_injective
        (by simpa using Goldilocks.val_lt_two_pow_64 x)
        (by simpa using Goldilocks.val_lt_two_pow_64 y) hp.1)
      subst y
      congr 1
      exact ih ys hp.2 (Nat.succ.inj hl)

/-- Fixed chunk lengths make concatenation injective. -/
theorem chunks_injective (xs ys : List Bytes)
    (hl : xs.map List.length = ys.map List.length)
    (h : xs.flatten = ys.flatten) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at hl
      change x ++ xs.flatten = y ++ ys.flatten at h
      have hp := List.append_inj h hl.1
      rw [hp.1, ih ys hl.2 hp.2]

/-- Flat serialization retains every wire, with no missing-tail/zero-padding alias.
The hypothesis fixes the validated circuit shape, not the secret values. -/
theorem viewBytes_injective_of_shape (a b : PartyView)
    (hi : a.inputs.length = b.inputs.length)
    (hg : a.gates.length = b.gates.length)
    (ho : a.outputs.length = b.outputs.length)
    (h : viewBytes a = viewBytes b) :
    a.seed.val = b.seed.val ∧ a.inputs = b.inputs ∧ a.gates = b.gates ∧ a.outputs = b.outputs := by
  let parts := fun v : PartyView =>
    [ascii "QSAG.VC.VIEW_COM.V1", v.seed.val, le 4 v.inputs.length, words v.inputs,
      le 4 v.gates.length, words v.gates, le 4 v.outputs.length, words v.outputs]
  have hlen : (parts a).map List.length = (parts b).map List.length := by
    simp [parts, le, words_length, a.seed.property, b.seed.property, hi, hg, ho]
  have hflat : (parts a).flatten = (parts b).flatten := by
    simpa [parts, viewBytes, List.append_assoc] using h
  have he := chunks_injective (parts a) (parts b) hlen hflat
  simp only [parts, List.cons.injEq] at he
  exact ⟨he.2.1, words_injective _ _ he.2.2.2.1,
    words_injective _ _ he.2.2.2.2.2.1, words_injective _ _ he.2.2.2.2.2.2.2.1⟩

/-- Bounded, flat DAG: every operand refers to an earlier wire. Multiplication
mask IDs are the gate positions themselves, so separate gates cannot alias. -/
inductive Gate (available : Nat) where
  | constant : Goldilocks → Gate available
  | add : Fin available → Fin available → Gate available
  | mul : Fin available → Fin available → Gate available

structure Circuit (inputs gates outputs : Nat) where
  gate : (i : Fin gates) → Gate (inputs + i.val)
  output : Fin outputs → Fin (inputs + gates)

def maskId {gates : Nat} (i : Fin gates) : Nat := i.val

theorem maskId_injective {gates : Nat} (a b : Fin gates)
    (h : maskId a = maskId b) : a = b := Fin.ext h

/-- Commitment and scope circuits share one allocation. The second allocation
starts after ALL gates in the first, including linear gates. -/
theorem maskDomains_disjoint (commitGates scopeGates : Nat)
    (a : Fin commitGates) (b : Fin scopeGates) :
    a.val ≠ commitGates + b.val := by have := a.isLt; omega

def shapeOK (inputs gates outputs : Nat) (v : PartyView) : Bool :=
  decide (v.inputs.length = inputs ∧ v.gates.length = gates ∧ v.outputs.length = outputs)

/-- The wire object is bounded even before a circuit-specific shape check. -/
theorem viewSizeBound (v : PartyView) :
    v.inputs.length + v.gates.length + v.outputs.length < 3 * 2^32 := by
  have := v.inputsBound; have := v.gatesBound; have := v.outputsBound
  omega

structure Transcript where
  chain : Bytes32
  round : UInt64
  absorbed : Bool

def init (protocol : String) (instanceBytes : Bytes) : Transcript :=
  ⟨hashFrames "QSAG.FS.INIT.V1" [ascii protocol, instanceBytes], 0, true⟩

/-- Rust's labeled absorb transition, including the payload. -/
def absorbMessage (tr : Transcript) (label : String) (payload : Bytes) : Transcript :=
  { tr with
    chain := hashFrames "QSAG.FS.ABSORB.V1"
      [tr.chain.val, le 8 tr.round.toNat, ascii label, payload]
    absorbed := true }

/-- Reject overflow instead of permitting a wrapped round identifier. -/
def squeeze (tr : Transcript) (label : String) (count : Nat) :
    Option (Bytes × Transcript) :=
  if tr.absorbed && decide (tr.round.toNat + 1 < 2^64) then
    let fs := [tr.chain.val, le 8 tr.round.toNat, ascii label]
    some (cshake256Xof count (ascii "QSAG.FS.SQUEEZE.V1") (framed fs),
      ⟨hashFrames "QSAG.FS.RATCHET.V1" fs, tr.round + 1, false⟩)
  else none

theorem squeeze_requires_absorb (tr : Transcript) (label : String) (count : Nat)
    (h : tr.absorbed = false) : squeeze tr label count = none := by
  simp [squeeze, h]

def fiveTrits (b : UInt8) : List (Fin 3) :=
  if b.toNat < 243 then
    (List.range 5).map (fun i => ⟨(b.toNat / 3^i) % 3, Nat.mod_lt _ (by decide)⟩)
  else []

/-- Fuel counts extension blocks. Exhaustion is explicit; it never returns a
short challenge vector or reduces a rejected byte modulo three. -/
def extendTrits : Nat → Transcript → UInt32 → Nat → List (Fin 3) →
    Option (List (Fin 3) × Transcript)
  | 0, tr, _, count, acc =>
    if acc.length ≥ count then some (acc.take count, tr) else none
  | fuel + 1, tr, extra, count, acc =>
    if acc.length ≥ count then some (acc.take count, tr) else
    if extra.toNat + 1 < 2^32 then do
      let (raw, next) ← squeeze
        (absorbMessage tr "VC_TRIT_EXTEND" (le 4 extra.toNat))
        "VC_ZKBOO_OPEN_TRITS_MORE" 64
      extendTrits fuel next (extra + 1) count (acc ++ raw.flatMap fiveTrits)
    else none

def challenges (fuel : Nat) (tr : Transcript) (count : Nat) :
    Option (List (Fin 3) × Transcript) := do
  let (raw, next) ← squeeze tr "VC_ZKBOO_OPEN_TRITS" 64
  extendTrits fuel next 0 count (raw.flatMap fiveTrits)

private def countRangeAux (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countRangeAux p n (if p n then acc + 1 else acc)

private theorem countRangeAux_add (p : Nat → Bool) :
    ∀ (n acc : Nat), countRangeAux p n acc = acc + countRangeAux p n 0
  | 0, acc => by simp [countRangeAux]
  | n + 1, acc => by
    unfold countRangeAux
    rw [countRangeAux_add p n _, countRangeAux_add p n (if p n then 1 else 0)]
    cases p n <;> omega

private theorem filter_range_length_eq_countRangeAux (p : Nat → Bool) :
    ∀ (n : Nat), ((List.range n).filter p).length = countRangeAux p n 0
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append,
        filter_range_length_eq_countRangeAux p n]
    unfold countRangeAux
    rw [countRangeAux_add p n (if p n then 1 else 0)]
    cases p n <;> simp [List.filter] <;> omega

/-- Each position of the accepted 243-byte alphabet has exactly 81 preimages
for each trit. This is a finite counting fact, not a randomness claim about SHAKE. -/
theorem accepted_trit_fibers :
    ∀ i ∈ List.range 5, ∀ t ∈ List.range 3,
      ((List.range 243).filter (fun b => (b / 3^i) % 3 == t)).length = 81 := by
  intro i hi t ht
  rw [filter_range_length_eq_countRangeAux]
  revert t
  revert i
  decide

/-- Accepted bytes have unique five-digit ternary expansions. -/
theorem accepted_five_trits_injective (a b : Nat) (ha : a < 243) (hb : b < 243)
    (h0 : a % 3 = b % 3) (h1 : (a / 3) % 3 = (b / 3) % 3)
    (h2 : (a / 9) % 3 = (b / 9) % 3)
    (h3 : (a / 27) % 3 = (b / 27) % 3)
    (h4 : (a / 81) % 3 = (b / 81) % 3) : a = b := by
  omega

/-- Rejection sampling, as in `sample_canonical_gl_vec`. -/
def fieldCandidate (w : UInt64) : Option Goldilocks :=
  if h : w.toNat < goldilocksPrime then some ⟨w.toNat, h⟩ else none

theorem fieldCandidate_exact (w : UInt64) (x : Goldilocks) :
    fieldCandidate w = some x ↔ w.toNat = x.val := by
  unfold fieldCandidate
  split
  next h =>
    constructor
    · intro he; cases he; rfl
    · intro he; congr 1; exact Goldilocks.ext he
  next h =>
    constructor
    · intro he; cases he
    · intro he; exact False.elim (h (by rw [he]; exact x.isLt))

/-- Exactly one accepted 64-bit word for every field value. Together with
independent uniform raw words this supplies the uniform rejection-sampling law. -/
def fieldAcceptedBijection :
    CredBijection { w : UInt64 // w.toNat < goldilocksPrime } Goldilocks where
  toFun := fun w => ⟨w.val.toNat, w.property⟩
  invFun := fun x => ⟨UInt64.ofNat x.val, by
    simpa [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Goldilocks.val_lt_two_pow_64 x)] using x.isLt⟩
  left_inv := by
    intro w
    exact Subtype.ext UInt64.ofNat_toNat
  right_inv := by
    intro x
    apply Goldilocks.ext
    simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Goldilocks.val_lt_two_pow_64 x)]

structure IssuerContext where
  oprfKeyDigest : Bytes32
  epoch : UInt64
  root : Fin 6 → Goldilocks
  rootTag : Bytes32

/-- Fields signed by the issuer, in Rust order. The public ML-DSA key is pinned
by the caller, not accepted from the presentation. -/
def rootMessage (ctx : IssuerContext) : Bytes :=
  ascii "QSAG.VC.ROOT_ATTEST.V1" ++ ctx.oprfKeyDigest.val ++ le 8 ctx.epoch.toNat ++
    words (List.ofFn ctx.root) ++ ctx.rootTag.val

def rootTag (ctx : IssuerContext) : Bytes32 :=
  hashFrames "QSAG.VC.ACC_ROOT_TAG.V1"
    [ctx.oprfKeyDigest.val, le 8 ctx.epoch.toNat, words (List.ofFn ctx.root)]

structure Attestation where
  context : IssuerContext
  mldsaKey : Bytes
  signature : Bytes

/-- The signature primitive has the argument order key, message, context, signature. -/
def verifyAttestation (verifySig : Bytes → Bytes → Bytes → Bytes → Bool)
    (expectedKey : Bytes) (expectedOprf : Bytes32) (a : Attestation) : Bool :=
  decide (a.mldsaKey = expectedKey) &&
  decide (a.context.oprfKeyDigest.val = expectedOprf.val) &&
  decide (a.context.rootTag.val = (rootTag a.context).val) &&
  verifySig expectedKey (rootMessage a.context) (ascii "QSAG.VC.ROOT_ATTEST.CTX.V1") a.signature

theorem substituted_key_rejected (verifySig : Bytes → Bytes → Bytes → Bytes → Bool)
    (key : Bytes) (oprf : Bytes32) (a : Attestation) (h : a.mldsaKey ≠ key) :
    verifyAttestation verifySig key oprf a = false := by
  simp [verifyAttestation, h]

theorem attestation_uses_expected_key
    (verifySig : Bytes → Bytes → Bytes → Bytes → Bool)
    (key : Bytes) (oprf : Bytes32) (a : Attestation)
    (h : verifyAttestation verifySig key oprf a = true) :
    a.mldsaKey = key ∧ a.context.oprfKeyDigest.val = oprf.val ∧
    verifySig key (rootMessage a.context) (ascii "QSAG.VC.ROOT_ATTEST.CTX.V1") a.signature = true := by
  simp only [verifyAttestation, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.2⟩

/-- Public policy includes all stable leakage. Equality is deliberately checked
before invoking the relation verifier. The latter must check membership against
this expected root; the legacy `checkOpenedPair` has no membership circuit. -/
structure Policy where
  issuerKey : Bytes
  oprfDigest : Bytes
  epoch : UInt64
  root : List Goldilocks
  tag : Bytes
  schema : UInt64
  arity : Fin 7
  scope : Bytes
  challenge : Bytes
  scopedId : Option Bytes
  disclosed : List (Nat × Goldilocks)
  deriving DecidableEq

def verifyPresentation {Proof : Type} (expected supplied : Policy)
    (verifyRelation : Policy → Proof → Bool) (proof : Proof) : Bool :=
  decide (supplied = expected) && verifyRelation expected proof

def PolicyAccepted {Proof : Type} (expected supplied : Policy)
    (verifyRelation : Policy → Proof → Bool) (proof : Proof) : Prop :=
  verifyPresentation expected supplied verifyRelation proof = true

theorem presentation_context_authenticated {Proof : Type} (expected supplied : Policy)
    (verifyRelation : Policy → Proof → Bool) (proof : Proof)
    (h : PolicyAccepted expected supplied verifyRelation proof) : supplied = expected := by
  simp only [PolicyAccepted, verifyPresentation, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem tooth_substituted_context_rejected {Proof : Type} (expected supplied : Policy)
    (verifyRelation : Policy → Proof → Bool) (proof : Proof) (h : supplied ≠ expected) :
    verifyPresentation expected supplied verifyRelation proof = false := by
  simp [verifyPresentation, h]

/-- Nonzero epoch/schema and disclosed value; an interface witness, not a FIPS
signature test vector or production credential proof. -/
def examplePolicy : Policy :=
  ⟨[1], [2], 7, [Goldilocks.one], [3], 11, ⟨1, by decide⟩,
    [4], [5], none, [(0, Goldilocks.one)]⟩

theorem authenticated_boundary_inhabited :
    ∃ expected supplied : Policy,
      PolicyAccepted expected supplied (fun (_ : Policy) (_ : Unit) => true) () ∧
      expected.epoch ≠ 0 := by
  exact ⟨examplePolicy, examplePolicy, by simp [PolicyAccepted, verifyPresentation], by decide⟩

#tooth_pair presentation_context_authenticated vs tooth_substituted_context_rejected
#verify_inhabited presentation_context_authenticated authenticated_boundary_inhabited

/-- Compose signature verification, trusted root matching, and the presentation
policy guard. The proof relation is invoked with the trusted policy only. -/
def verifyCredentialPresentation {Proof : Type}
    (verifySig : Bytes → Bytes → Bytes → Bytes → Bool)
    (expectedOprf : Bytes32) (trusted : Attestation) (expected supplied : Policy)
    (verifyRelation : Policy → Proof → Bool) (proof : Proof) : Bool :=
  verifyAttestation verifySig expected.issuerKey expectedOprf trusted &&
  decide (expected.oprfDigest = expectedOprf.val ∧
    expected.epoch = trusted.context.epoch ∧
    expected.root = List.ofFn trusted.context.root ∧
    expected.tag = trusted.context.rootTag.val) &&
  verifyPresentation expected supplied verifyRelation proof

theorem credential_acceptance_authenticates {Proof : Type}
    (verifySig : Bytes → Bytes → Bytes → Bytes → Bool)
    (expectedOprf : Bytes32) (trusted : Attestation) (expected supplied : Policy)
    (verifyRelation : Policy → Proof → Bool) (proof : Proof)
    (h : verifyCredentialPresentation verifySig expectedOprf trusted expected supplied
      verifyRelation proof = true) :
    supplied = expected ∧
    verifySig expected.issuerKey (rootMessage trusted.context)
      (ascii "QSAG.VC.ROOT_ATTEST.CTX.V1") trusted.signature = true ∧
    expected.root = List.ofFn trusted.context.root := by
  simp only [verifyCredentialPresentation, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨presentation_context_authenticated _ _ _ _ h.2,
    (attestation_uses_expected_key _ _ _ _ h.1.1).2.2, h.1.2.2.2.1⟩

theorem tooth_forged_issuer_context {Proof : Type}
    (verifySig : Bytes → Bytes → Bytes → Bytes → Bool)
    (expectedOprf : Bytes32) (trusted : Attestation) (expected supplied : Policy)
    (verifyRelation : Policy → Proof → Bool) (proof : Proof)
    (h : trusted.mldsaKey ≠ expected.issuerKey) :
    verifyCredentialPresentation verifySig expectedOprf trusted expected supplied
      verifyRelation proof = false := by
  simp [verifyCredentialPresentation, substituted_key_rejected _ _ _ _ h]

#tooth_pair credential_acceptance_authenticates vs tooth_forged_issuer_context

/-- Fixed-length public statement fields, in `serialize_sd_instance` order. -/
structure SdInstance where
  arity : Fin 7
  nonce : Bytes32
  epoch : UInt64
  schema : UInt64
  issuerTag : Bytes32
  root : Fin 6 → Goldilocks
  scope : Fin 4 → Goldilocks
  presCommit : Fin 6 → Goldilocks
  scopeTag : Fin 6 → Goldilocks
  disclosed : List (UInt32 × Goldilocks)
  disclosedBound : disclosed.length ≤ 6

def sdBytes (s : SdInstance) : Bytes :=
  le 8 s.arity.val ++ s.nonce.val ++ le 8 s.epoch.toNat ++ le 8 s.schema.toNat ++
  s.issuerTag.val ++ words (List.ofFn s.root ++ List.ofFn s.scope ++
    List.ofFn s.presCommit ++ List.ofFn s.scopeTag) ++
  le 4 s.disclosed.length ++ s.disclosed.flatMap (fun p => le 4 p.1.toNat ++ le 8 p.2.val)

inductive Profile where
  | classical219
  | grinding438
  deriving DecidableEq

def Profile.repetitions : Profile → Nat
  | .classical219 => 219
  | .grinding438 => 438

/-- The 438 profile name is a grinding parameter, not a QROM security theorem. -/
def sdTranscript (s : SdInstance) (challenge : Bytes32) (profile : Profile) : Transcript :=
  let instanceBytes := sdBytes s ++ challenge.val ++
    if profile = .grinding438 then ascii "QSAG.VC.PROFILE.Quantum128:438" else []
  let tr := init "QSAG.BLIND_VC.SD_ZK.V1" instanceBytes
  if profile = .grinding438 then
    absorbMessage tr "VC_SOUNDNESS_PROFILE" (ascii "Quantum128:438") else tr

structure RoundOne where
  commits : Fin 3 → Bytes32
  outputs : Fin 38 → Fin 3 → Goldilocks

/-- Rust writes commitments party-major, then output words output-major. -/
def roundOneBytes (r : RoundOne) : Bytes :=
  (List.ofFn r.commits).flatMap Subtype.val ++
    (List.ofFn r.outputs).flatMap (fun row => words (List.ofFn row))

def presentationChallenges (fuel : Nat) (s : SdInstance) (challenge : Bytes32)
    (profile : Profile) (rounds : Fin profile.repetitions → RoundOne) :=
  challenges fuel (absorbMessage (sdTranscript s challenge profile) "VC_SD_R1_COMMITS"
    ((List.ofFn rounds).flatMap roundOneBytes)) profile.repetitions

/-- A nonempty, nonzero flat view fixture for cross-language serialization tests. -/
def viewFixture : PartyView :=
  { seed := ⟨List.replicate 32 1, by simp⟩
    inputs := [Goldilocks.ofNat 2]
    gates := [Goldilocks.ofNat 3]
    outputs := [Goldilocks.ofNat 4]
    inputsBound := by decide
    gatesBound := by decide
    outputsBound := by decide }

theorem view_wire_known_answer :
    viewBytes viewFixture = ascii "QSAG.VC.VIEW_COM.V1" ++ List.replicate 32 1 ++
      [1,0,0,0, 2,0,0,0,0,0,0,0,
       1,0,0,0, 3,0,0,0,0,0,0,0,
       1,0,0,0, 4,0,0,0,0,0,0,0] := by
  simp only [viewBytes, viewFixture, words, List.flatMap_cons, List.flatMap_nil,
    Goldilocks.ofNat_val, List.append_assoc]
  congr 1
  decide

/-- Width mutation witnesses exercise the actual commitment frame constructor. -/
theorem commitment_widths (sid digest salt : Bytes32) (r : UInt32) (p : Fin 3) :
    (commitmentFrames sid r p digest salt).map List.length = [32, 4, 2, 32, 32] := by
  simp [commitmentFrames, le, sid.property, digest.property, salt.property]

theorem tooth_wrong_party_width : le 2 1 ≠ le 1 1 := by decide

theorem tooth_rejected_byte : fiveTrits 243 = [] := by decide

theorem tooth_modulo_trits_biased :
    ((List.range 256).filter (fun b => b % 3 == 0)).length = 86 ∧
    ((List.range 256).filter (fun b => b % 3 == 1)).length = 85 := by decide


/-- A collision between precisely the two submitted, reachable framed inputs.
The candidate frames remain parameters of the proposition: they cannot be replaced
by arbitrary invertible-permutation states or unrelated sponge preimages. -/
def FramedCollision (H : Bytes → Bytes) (domain : Bytes) (x y : List Bytes) : Prop :=
  framed x ≠ framed y ∧ H (domain ++ framed x) = H (domain ++ framed y)

theorem committed_openings_equal_or_collision
    (H : Bytes → Bytes) (domain : Bytes) (x y : List Bytes)
    (h : H (domain ++ framed x) = H (domain ++ framed y)) :
    framed x = framed y ∨ FramedCollision H domain x y := by
  by_cases he : framed x = framed y
  · exact Or.inl he
  · exact Or.inr ⟨he, h⟩

/-- Two independent openings of one commitment either have the same framed
preimage, or those exact openings exhibit a collision. This is a reduction step,
not a hardness assumption or the circuit's special-soundness theorem. -/
theorem rewound_openings_bound (H : Bytes → Bytes) (domain digest : Bytes)
    (x y : List Bytes)
    (hx : H (domain ++ framed x) = digest) (hy : H (domain ++ framed y) = digest) :
    framed x = framed y ∨ FramedCollision H domain x y :=
  committed_openings_equal_or_collision H domain x y (hx.trans hy.symm)

/-- Scoped mode's equality distinguisher: fresh coins do not remove a stable tag. -/
theorem tooth_scoped_tags_link (tag : Nat → Nat) (a b : Nat) (h : tag a ≠ tag b) :
    (tag a, tag a) ≠ (tag a, tag b) := by
  intro he
  exact h (congrArg Prod.snd he)

/-- A revealing commitment remains revealing for every fresh uniform blind.
Fresh randomness by itself cannot establish the requested general hiding claim. -/
theorem tooth_fresh_blinds_do_not_hide_arbitrary_commitments
    (a b : Goldilocks) (h : a ≠ b) :
    ∀ r s : VcBlind4, (fun x (_ : VcBlind4) => x) a r ≠
      (fun x (_ : VcBlind4) => x) b s := by
  intro _ _
  exact h

/-- An adaptive oracle can select an accepting challenge at every repetition.
The fixed-transcript two-of-three count alone gives no oracle-security bound. -/
theorem tooth_adaptive_challenge_oracle (rounds : Nat) :
    (∀ _ : Fin rounds, (fun c : Fin 3 => c.val < 2) (0 : Fin 3)) ∧
    ¬ (∀ c : Fin 3, c.val < 2) := by
  exact ⟨fun _ => by decide, fun h => by have := h 2; omega⟩

end BlindVcWire

/-- Canonical coefficients are necessary even when the centered residue is zero. -/
theorem tooth_norm_rejects_modulus :
    checkCenteredInfNorm 8380417 1 [8380417] = false := by decide

end Qsag
end
