module
/-
# Advanced MPC, Accelerated Proof Kernels, and Anonymous Credentials
Constructive arithmetic models, hardware-refining proof kernels, MAC-authenticated
durable threshold ML-DSA nonce journals, and credential arithmetic and wire models.
The finite wire boundary authenticates the supplied issuer context. `PresentationView`
proves that one repetition's opened view (both opened parties' wires and tapes, and the
third output shares) is perfectly simulated from the public outputs when tapes are uniform
and every multiplication has its own mask index.
`repeated_presentation_privacy` composes the fixed-challenge opened-view hybrid with a
joint input-and-gate coin bijection for any finite number of repetitions.
`adaptive_challenge_presentation_privacy` removes the fixed challenges: for any challenge
function of the first message, the complete transcript (commitments, derived challenges,
responses) is preserved by a coin translation, provided the commitment can be moved
between views by a salt translation. That the deployed hash commitment has this property
up to a computational bound, the seed-to-tape PRG step, hiding of the public outputs
themselves (fresh-mode unlinkability beyond `fresh_public_output_unlinkability`'s
explicit coupling premise), and ROM/QROM reductions remain separate obligations;
repetition counts do not establish them.
LAW-M1: public statements with a bounded exposed interface (`<= 12` `@[expose]`).
-/

public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Oracle.Poseidon2
public import Qsag.Tactic.Prelude
public import Qsag.Oracle.Keccak
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
theorem blind_vc_local_reblinding_and_special_soundness :
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

/-- Compatibility name for the local masking and fixed-triple result above.
It does not assert unlinkability of complete presentations. -/
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
      matchesIssuerSlots (reconAttrs t) t.issuerSlots) :=
  blind_vc_local_reblinding_and_special_soundness

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
    exact (validPersistentNonceTrace_alias hTr)
where
  validPersistentNonceTrace_alias {partyId : UInt16} {st₀ st₂ : SignerCrashState}
      {trace : List PersistentNonceEvent}
      (hTr : ValidPersistentNonceTrace partyId st₀ trace st₂) :=
    (validPersistentTrace_event_conflict_free hTr).2

/-! ### 5.1 MAC-Authenticated `FsNonceBurnStore` (`QSCBURN2`), Monotonic Generation Floor & Key-Bound Masking Nonce Derivation -/

abbrev BurnBytes8 := { bs : List UInt8 // bs.length = 8 }
abbrev BurnBytes16 := { bs : List UInt8 // bs.length = 16 }
abbrev BurnBytes32 := { bs : List UInt8 // bs.length = 32 }

def burnLeBytes (width n : Nat) : List UInt8 := (be width n).reverse

private theorem burnLeBytes_length (width n : Nat) : (burnLeBytes width n).length = width := by
  simp [burnLeBytes, length_be]

private theorem burnChunks_injective (xs ys : List (List UInt8))
    (hl : xs.map List.length = ys.map List.length)
    (h : xs.flatten = ys.flatten) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases hl
  | cons x xs ih =>
    cases ys with
    | nil => cases hl
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at hl
      change x ++ xs.flatten = y ++ ys.flatten at h
      have hp := List.append_inj h hl.1
      rw [hp.1, ih ys hl.2 hp.2]

private theorem burnLeBytes_injective {width a b : Nat}
    (ha : a < 256 ^ width) (hb : b < 256 ^ width)
    (h : burnLeBytes width a = burnLeBytes width b) : a = b := by
  apply be_injective ha hb
  have hr := congrArg List.reverse h
  simpa [burnLeBytes] using hr

/-- Fixed 46-byte persisted attempt tuple `(party_id: u16, epoch: u64, session_id: [u8; 32], attempt: u32)`
    matching `FsNonceBurnStore::encode` / `open_at_least` (`threshold_mldsa.rs:285-294, 309-314`). -/
structure AuthenticatedBurnRow where
  partyId : UInt16
  epoch : UInt64
  sessionId : BurnBytes32
  attempt : UInt32
  deriving DecidableEq

def encodeAuthBurnRow (r : AuthenticatedBurnRow) : List UInt8 :=
  burnLeBytes 2 r.partyId.toNat ++
  burnLeBytes 8 r.epoch.toNat ++
  r.sessionId.val ++
  burnLeBytes 4 r.attempt.toNat

theorem encodeAuthBurnRow_length (r : AuthenticatedBurnRow) :
    (encodeAuthBurnRow r).length = 46 := by
  simp [encodeAuthBurnRow, burnLeBytes_length, r.sessionId.property]

theorem encodeAuthBurnRow_injective {a b : AuthenticatedBurnRow}
    (h : encodeAuthBurnRow a = encodeAuthBurnRow b) : a = b := by
  let parts := fun r : AuthenticatedBurnRow =>
    [burnLeBytes 2 r.partyId.toNat, burnLeBytes 8 r.epoch.toNat,
     r.sessionId.val, burnLeBytes 4 r.attempt.toNat]
  have hlen : (parts a).map List.length = (parts b).map List.length := by
    simp [parts, burnLeBytes_length, a.sessionId.property, b.sessionId.property]
  have hflat : (parts a).flatten = (parts b).flatten := by
    simpa [parts, encodeAuthBurnRow, List.append_assoc] using h
  have he := burnChunks_injective (parts a) (parts b) hlen hflat
  simp only [parts, List.cons.injEq] at he
  have hp : a.partyId = b.partyId := UInt16.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
    (burnLeBytes_injective (by simpa using a.partyId.toNat_lt) (by simpa using b.partyId.toNat_lt) he.1))
  have hep : a.epoch = b.epoch := UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
    (burnLeBytes_injective (by simpa using a.epoch.toNat_lt) (by simpa using b.epoch.toNat_lt) he.2.1))
  have hs : a.sessionId = b.sessionId := Subtype.ext he.2.2.1
  have hat : a.attempt = b.attempt := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
    (burnLeBytes_injective (by simpa using a.attempt.toNat_lt) (by simpa using b.attempt.toNat_lt) he.2.2.2.1))
  cases a; cases b; simp only at hp hep hs hat; subst hp hep hs hat; rfl

theorem encodeAuthBurnRows_injective :
    ∀ (xs ys : List AuthenticatedBurnRow),
      xs.flatMap encodeAuthBurnRow = ys.flatMap encodeAuthBurnRow → xs = ys
  | [], [] => fun _ => rfl
  | [], y :: ys => fun h => by
    have hl := congrArg List.length h
    simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append,
      encodeAuthBurnRow_length] at hl
    omega
  | x :: xs, [] => fun h => by
    have hl := congrArg List.length h
    simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append,
      encodeAuthBurnRow_length] at hl
    omega
  | x :: xs, y :: ys => fun h => by
    simp only [List.flatMap_cons] at h
    have hp := List.append_inj h (by simp [encodeAuthBurnRow_length])
    rw [encodeAuthBurnRow_injective hp.1, encodeAuthBurnRows_injective xs ys hp.2]

/-- On-disk `QSCBURN2` authenticated ledger record (`threshold_mldsa.rs:246-321`):
    binds `.lock` sidecar `(dev, ino)` (`lockId`), `LockedRecord::lock_seal` (`lockSeal`),
    `keyId`, monotonic `generation`, and 46-byte `rows` under a 32-byte framed cSHAKE256 MAC tag. -/
structure AuthenticatedBurnRecord where
  lockSeal : BurnBytes8
  keyId : BurnBytes32
  generation : UInt64
  rows : List AuthenticatedBurnRow
  rowsBound : rows.length < 2 ^ 64
  macTag : BurnBytes32
  deriving DecidableEq

def burnRecordBodyBytes (record : AuthenticatedBurnRecord) : List UInt8 :=
  "QSCBURN2".toUTF8.toList ++
  record.lockSeal.val ++
  record.keyId.val ++
  burnLeBytes 8 record.generation.toNat ++
  burnLeBytes 8 record.rows.length ++
  record.rows.flatMap encodeAuthBurnRow

theorem burnRecordBodyBytes_injective {a b : AuthenticatedBurnRecord}
    (h : burnRecordBodyBytes a = burnRecordBodyBytes b) :
    a.lockSeal = b.lockSeal ∧ a.keyId = b.keyId ∧
    a.generation = b.generation ∧ a.rows = b.rows := by
  let header := fun r : AuthenticatedBurnRecord =>
    ["QSCBURN2".toUTF8.toList, r.lockSeal.val, r.keyId.val,
     burnLeBytes 8 r.generation.toNat, burnLeBytes 8 r.rows.length]
  have hSplit :
      (header a).flatten ++ a.rows.flatMap encodeAuthBurnRow =
      (header b).flatten ++ b.rows.flatMap encodeAuthBurnRow := by
    simpa [header, burnRecordBodyBytes, List.append_assoc] using h
  have hHdrLen : (header a).flatten.length = (header b).flatten.length := by
    simp [header, burnLeBytes_length, a.lockSeal.property, b.lockSeal.property,
      a.keyId.property, b.keyId.property]
  have hPair := List.append_inj hSplit hHdrLen
  have hChunkLen : (header a).map List.length = (header b).map List.length := by
    simp [header, burnLeBytes_length, a.lockSeal.property, b.lockSeal.property,
      a.keyId.property, b.keyId.property]
  have he := burnChunks_injective (header a) (header b) hChunkLen hPair.1
  simp only [header, List.cons.injEq] at he
  have hGenEq : a.generation = b.generation := UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
    (burnLeBytes_injective (by simpa using a.generation.toNat_lt) (by simpa using b.generation.toNat_lt) he.2.2.2.1))
  exact ⟨Subtype.ext he.2.1, Subtype.ext he.2.2.1, hGenEq,
    encodeAuthBurnRows_injective a.rows b.rows hPair.2⟩

def burnFramedMacInput (macKey : BurnBytes32) (lockId : BurnBytes16) (body : List UInt8) : List UInt8 :=
  let frames : List (List UInt8) := [macKey.val, lockId.val, body]
  burnLeBytes 8 frames.length ++ frames.flatMap (fun f => burnLeBytes 8 f.length ++ f)

def computeBurnRecordMac (macKey : BurnBytes32) (lockId : BurnBytes16) (body : List UInt8) : BurnBytes32 :=
  ⟨cshake256Bytes ("QSAG.MLDSA.NONCE_BURN.V2".toUTF8.toList) (burnFramedMacInput macKey lockId body),
   cshake256Bytes_length _ _⟩

def replayAuthBurnRows (store : DurableNonceBurnStore) :
    List AuthenticatedBurnRow → Option DurableNonceBurnStore
  | [] => some store
  | r :: rest =>
    let res := durableBurnReserve store r.partyId r.epoch r.sessionId.val r.attempt true
    if res.1 then replayAuthBurnRows res.2 rest else none

/-- Exact `FsNonceBurnStore::open_at_least` verifier (`threshold_mldsa.rs:235-296`):
    enforces constant-time MAC match over `(macKey, lockId, body)`, `lockSeal` & `keyId` pinning,
    monotonic `minExpectedGeneration ≤ generation`, `rows.length ≤ generation`, and conflict-free row replay. -/
def openAuthenticatedBurnStoreAtLeast
    (macKey : BurnBytes32) (expectedLockId : BurnBytes16)
    (expectedLockSeal : BurnBytes8) (expectedKeyId : BurnBytes32)
    (minExpectedGeneration : UInt64)
    (record : AuthenticatedBurnRecord) : Option DurableNonceBurnStore :=
  if decide (record.macTag = computeBurnRecordMac macKey expectedLockId (burnRecordBodyBytes record)) &&
     decide (record.lockSeal = expectedLockSeal) &&
     decide (record.keyId = expectedKeyId) &&
     decide (minExpectedGeneration.toNat ≤ record.generation.toNat) &&
     decide (record.rows.length ≤ record.generation.toNat) then
    replayAuthBurnRows { keyId := expectedKeyId.val, burns := [], poisoned := false } record.rows
  else
    none

/-- Explicit cSHAKE256 MAC collision witness on `"QSAG.MLDSA.NONCE_BURN.V2"`. -/
def BurnRecordMacCollision (macKey : BurnBytes32) (lockId : BurnBytes16)
    (body1 body2 : List UInt8) : Prop :=
  body1 ≠ body2 ∧
  computeBurnRecordMac macKey lockId body1 = computeBurnRecordMac macKey lockId body2

/-- Framed key-bound masking-nonce derivation preimage binding `(keyId, partyId, epoch, sessionId, attempt)`
    prior to domain-separated `"QSAG.MLDSA.NONCE_BURN.V2"` PRF evaluation. -/
def encodeMaskNonceTuple (keyId : List UInt8) (ev : PersistentNonceEvent) : List UInt8 :=
  burnLeBytes 8 keyId.length ++ keyId ++
  burnLeBytes 2 ev.partyId.toNat ++
  burnLeBytes 8 ev.epoch.toNat ++
  burnLeBytes 8 ev.sessionId.length ++ ev.sessionId ++
  burnLeBytes 4 ev.attempt.toNat

def deriveAttemptMaskNonceSeed (secretKeySeed : BurnBytes32)
    (keyId : List UInt8) (ev : PersistentNonceEvent) : BurnBytes32 :=
  ⟨cshake256Bytes ("QSAG.MLDSA.NONCE_BURN.V2".toUTF8.toList)
     (secretKeySeed.val ++ encodeMaskNonceTuple keyId ev),
   cshake256Bytes_length _ _⟩

theorem encodeMaskNonceTuple_injective_of_key {keyId : List UInt8}
    (_hk : keyId.length < 256 ^ 8)
    {e1 e2 : PersistentNonceEvent}
    (hs1 : e1.sessionId.length < 256 ^ 8)
    (hs2 : e2.sessionId.length < 256 ^ 8)
    (hEq : encodeMaskNonceTuple keyId e1 = encodeMaskNonceTuple keyId e2) :
    e1.partyId = e2.partyId ∧ e1.epoch = e2.epoch ∧
    e1.sessionId = e2.sessionId ∧ e1.attempt = e2.attempt := by
  let pre := fun ev : PersistentNonceEvent =>
    [burnLeBytes 8 keyId.length, keyId, burnLeBytes 2 ev.partyId.toNat,
     burnLeBytes 8 ev.epoch.toNat, burnLeBytes 8 ev.sessionId.length]
  have hSplit :
      (pre e1).flatten ++ (e1.sessionId ++ burnLeBytes 4 e1.attempt.toNat) =
      (pre e2).flatten ++ (e2.sessionId ++ burnLeBytes 4 e2.attempt.toNat) := by
    simpa [pre, encodeMaskNonceTuple, List.append_assoc] using hEq
  have hPreLen : (pre e1).flatten.length = (pre e2).flatten.length := by
    simp [pre, burnLeBytes_length]
  have hPair := List.append_inj hSplit hPreLen
  have hChunkLen : (pre e1).map List.length = (pre e2).map List.length := by
    simp [pre, burnLeBytes_length]
  have he := burnChunks_injective (pre e1) (pre e2) hChunkLen hPair.1
  simp only [pre, List.cons.injEq] at he
  have hLenEq : e1.sessionId.length = e2.sessionId.length :=
    burnLeBytes_injective hs1 hs2 he.2.2.2.2.1
  have hS := List.append_inj hPair.2 hLenEq
  have hpEq : e1.partyId = e2.partyId := UInt16.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
    (burnLeBytes_injective (by simpa using e1.partyId.toNat_lt) (by simpa using e2.partyId.toNat_lt) he.2.2.1))
  have heEq : e1.epoch = e2.epoch := UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
    (burnLeBytes_injective (by simpa using e1.epoch.toNat_lt) (by simpa using e2.epoch.toNat_lt) he.2.2.2.1))
  have haEq : e1.attempt = e2.attempt := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
    (burnLeBytes_injective (by simpa using e1.attempt.toNat_lt) (by simpa using e2.attempt.toNat_lt) hS.2))
  exact ⟨hpEq, heEq, hS.1, haEq⟩

/-- **Theorem 5B (`authenticated_nonce_burn_open_at_least_and_derivation_sound`)**:
    1. **Rollback Rejection (`open_at_least`)**: Any replayed disk record with
       `record.generation < minExpectedGeneration` is unconditionally rejected (`= none`).
    2. **MAC + Lock-Inode + Seal Pinning**: Any accepted record matches `expectedLockSeal`,
       `expectedKeyId`, `minExpectedGeneration ≤ record.generation`, and `computeBurnRecordMac`;
       two records with distinct `(lockSeal, keyId, generation, rows)` sharing a MAC tag yield
       an explicit `BurnRecordMacCollision` on `"QSAG.MLDSA.NONCE_BURN.V2"`.
    3. **End-to-End Trace Masking-Nonce Input Distinctness**: Along EVERY reachable
       `ValidPersistentNonceTrace`, the framed key-bound masking-nonce preimages
       `trace.map (encodeMaskNonceTuple st₀.store.keyId)` are strictly pairwise distinct (`Nodup`),
       connecting durable burn reservation directly to distinct per-attempt masking nonces! -/
theorem authenticated_nonce_burn_open_at_least_and_derivation_sound :
    (∀ macKey lockId lkSeal keyId minGen record,
      record.generation.toNat < minGen.toNat →
      openAuthenticatedBurnStoreAtLeast macKey lockId lkSeal keyId minGen record = none) ∧
    (∀ macKey lockId lkSeal keyId minGen record st,
      openAuthenticatedBurnStoreAtLeast macKey lockId lkSeal keyId minGen record = some st →
      record.lockSeal = lkSeal ∧ record.keyId = keyId ∧
      minGen.toNat ≤ record.generation.toNat ∧
      record.macTag = computeBurnRecordMac macKey lockId (burnRecordBodyBytes record)) ∧
    (∀ macKey lockId (r1 r2 : AuthenticatedBurnRecord),
      computeBurnRecordMac macKey lockId (burnRecordBodyBytes r1) =
        computeBurnRecordMac macKey lockId (burnRecordBodyBytes r2) →
      (r1.lockSeal = r2.lockSeal ∧ r1.keyId = r2.keyId ∧
       r1.generation = r2.generation ∧ r1.rows = r2.rows) ∨
      BurnRecordMacCollision macKey lockId (burnRecordBodyBytes r1) (burnRecordBodyBytes r2)) ∧
    (∀ (partyId : UInt16) (st₀ st₂ : SignerCrashState) (trace : List PersistentNonceEvent),
      st₀.store.keyId.length < 256 ^ 8 →
      (∀ ev ∈ trace, ev.sessionId.length < 256 ^ 8) →
      ValidPersistentNonceTrace partyId st₀ trace st₂ →
      (trace.map (encodeMaskNonceTuple st₀.store.keyId)).Nodup) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro macKey lockId lkSeal keyId minGen record hLt
    have hNotLe : ¬ (minGen.toNat ≤ record.generation.toNat) := by omega
    simp [openAuthenticatedBurnStoreAtLeast, hNotLe]
  · intro macKey lockId lkSeal keyId minGen record st hOpen
    unfold openAuthenticatedBurnStoreAtLeast at hOpen
    split at hOpen
    · next hCond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
      exact ⟨hCond.1.1.1.2, hCond.1.1.2, hCond.1.2, hCond.1.1.1.1⟩
    · cases hOpen
  · intro macKey lockId r1 r2 hMac
    by_cases hBody : burnRecordBodyBytes r1 = burnRecordBodyBytes r2
    · exact Or.inl (burnRecordBodyBytes_injective hBody)
    · exact Or.inr ⟨hBody, hMac⟩
  · intro partyId st₀ st₂ trace hk hsBounded hTr
    have hPw := (validPersistentTrace_event_conflict_free hTr).2
    clear hTr
    induction hPw with
    | nil => exact List.Pairwise.nil
    | @cons a rest hRel hRest ih =>
      have ih' := ih (fun ev hev => hsBounded ev (List.mem_cons.mpr (Or.inr hev)))
      simp only [List.map_cons]
      refine List.Pairwise.cons ?_ ih'
      intro b hb hEq
      rw [List.mem_map] at hb
      rcases hb with ⟨y, hy, rfl⟩
      have hInj := encodeMaskNonceTuple_injective_of_key hk
        (hsBounded a (List.mem_cons.mpr (Or.inl rfl)))
        (hsBounded y (List.mem_cons.mpr (Or.inr hy)))
        hEq
      exact (hRel y hy).2.1 hInj.2.1

def staleGen0Fixture (macKey : BurnBytes32) (lockId : BurnBytes16)
    (lkSeal : BurnBytes8) (keyId : BurnBytes32) : AuthenticatedBurnRecord :=
  let body0 : List UInt8 :=
    "QSCBURN2".toUTF8.toList ++ lkSeal.val ++ keyId.val ++
    burnLeBytes 8 0 ++ burnLeBytes 8 0
  { lockSeal := lkSeal, keyId := keyId, generation := 0, rows := [],
    rowsBound := by decide,
    macTag := computeBurnRecordMac macKey lockId body0 }

/-- **`#tooth` (`tooth_missing_generation_floor_accepts_stale_snapshot_rollback`)**:
    If an attacker replays a valid MAC-authenticated `generation = 0` empty burn file after the
    custodian already advanced to `generation = 1`, opening with `minExpectedGeneration = 0`
    (`open`) accepts the rolled-back empty store, whereas `openAuthenticatedBurnStoreAtLeast`
    with `minExpectedGeneration = 1` deterministically rejects it (`= none`)! -/
theorem tooth_missing_generation_floor_accepts_stale_snapshot_rollback
    (macKey : BurnBytes32) (lockId : BurnBytes16)
    (lkSeal : BurnBytes8) (keyId : BurnBytes32) :
    openAuthenticatedBurnStoreAtLeast macKey lockId lkSeal keyId 0
      (staleGen0Fixture macKey lockId lkSeal keyId) ≠
    openAuthenticatedBurnStoreAtLeast macKey lockId lkSeal keyId 1
      (staleGen0Fixture macKey lockId lkSeal keyId) := by
  have h0 : openAuthenticatedBurnStoreAtLeast macKey lockId lkSeal keyId 0
      (staleGen0Fixture macKey lockId lkSeal keyId) =
      some { keyId := keyId.val, burns := [], poisoned := false } := by
    have hMac : (staleGen0Fixture macKey lockId lkSeal keyId).macTag =
        computeBurnRecordMac macKey lockId
          (burnRecordBodyBytes (staleGen0Fixture macKey lockId lkSeal keyId)) := by
      simp [staleGen0Fixture, burnRecordBodyBytes, List.append_assoc]
    unfold openAuthenticatedBurnStoreAtLeast
    rw [hMac]
    simp [staleGen0Fixture, replayAuthBurnRows]
  have h1 : openAuthenticatedBurnStoreAtLeast macKey lockId lkSeal keyId 1
      (staleGen0Fixture macKey lockId lkSeal keyId) = none :=
    authenticated_nonce_burn_open_at_least_and_derivation_sound.1
      macKey lockId lkSeal keyId 1 (staleGen0Fixture macKey lockId lkSeal keyId)
      (by simp [staleGen0Fixture])
  rw [h0, h1]
  intro hBad
  cases hBad

#tooth_pair authenticated_nonce_burn_open_at_least_and_derivation_sound vs
  tooth_missing_generation_floor_accepts_stale_snapshot_rollback

#tooth_pair authenticated_nonce_burn_open_at_least_and_derivation_sound vs
  tooth_missing_generation_floor_accepts_stale_snapshot_rollback

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

/-- Point-evaluation schedule with optional sign negation on evaluation points
    (used by `AcceleratorBackendSpec.goldilocksNtt`; see `nttForward` / `nttInverse`
    in §6.5 for the normalized root-of-unity forward/inverse NTT roundtrip). -/
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

/-- Point-shifted `GoldilocksExt2` Horner evaluation helper for `AcceleratorBackendSpec.cosetLdeExt2`
    (see `multiplicativeCosetLdeExec_eq_spec` in §6.5 for the full `n * blowup` multiplicative-coset LDE). -/
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

/-- Composed point-evaluation, Karatsuba `Ext2` evaluation, and Merkle layer reduction schedule
    (paired in §6.5 with `nttInverse_nttForward_roundtrip`, `multiplicativeCosetLdeExec_eq_spec`,
    and fixed-width collision-bound `merkleCompleteTree_binding_or_collision`). -/
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

/-- Behavioral refinement `AcceleratorSimulates simdExecBackend cpuSpecBackend` across all 6
    `AcceleratorBackendSpec` batch kernels and their composed evaluation/Merkle pipeline. -/
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
      evalBaseFoldCommitPipeline simdExecBackend p1 tw blowup d shift pkSeed =
        evalBaseFoldCommitPipeline simdExecBackend p2 tw blowup d shift pkSeed ↔
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
  intro p1 p2 tw blowup d shift pkSeed
  rw [hPipe p1, hPipe p2]

/-! ### 6.5 Normalized Root-of-Unity Forward/Inverse NTT, `n * blowup` Multiplicative-Coset LDE,
            and Fixed-Width 4-Limb `pkSeed` Complete-Tree Merkle Binding -/

def glPow (x : Goldilocks) : Nat → Goldilocks
  | 0 => CommRingOps.one
  | k + 1 => CommRingOps.mul x (glPow x k)

private theorem glPow_one : ∀ k : Nat, glPow CommRingOps.one k = CommRingOps.one
  | 0 => rfl
  | k + 1 => by simp only [glPow, glPow_one k, LawfulCommRing.one_mul]

private theorem glPow_add (x : Goldilocks) :
    ∀ (a b : Nat), glPow x (a + b) = CommRingOps.mul (glPow x a) (glPow x b)
  | 0, b => by simp only [Nat.zero_add, glPow, LawfulCommRing.one_mul]
  | a + 1, b => by
    simp only [Nat.succ_add, glPow, glPow_add x a b, LawfulCommRing.mul_assoc]

private theorem glPow_mul (x : Goldilocks) :
    ∀ (a b : Nat), glPow x (a * b) = glPow (glPow x a) b
  | a, 0 => rfl
  | a, b + 1 => by
    rw [Nat.mul_succ, Nat.add_comm (a * b) a, glPow_add, glPow_mul x a b]
    rfl

private theorem glPow_mul_distrib (x y : Goldilocks) :
    ∀ (k : Nat), glPow (CommRingOps.mul x y) k = CommRingOps.mul (glPow x k) (glPow y k)
  | 0 => by simp only [glPow, LawfulCommRing.one_mul]
  | k + 1 => by
    simp only [glPow, glPow_mul_distrib x y k]
    rw [LawfulCommRing.mul_assoc x y _,
        ← LawfulCommRing.mul_assoc y (glPow x k) (glPow y k),
        LawfulCommRing.mul_comm y (glPow x k),
        LawfulCommRing.mul_assoc (glPow x k) y (glPow y k),
        ← LawfulCommRing.mul_assoc x (glPow x k) _]

def glRangeSum : Nat → (Nat → Goldilocks) → Goldilocks
  | 0, _ => CommRingOps.zero
  | n + 1, f => CommRingOps.add (glRangeSum n f) (f n)

private theorem glRangeSum_congr {n : Nat} {f g : Nat → Goldilocks}
    (h : ∀ i < n, f i = g i) : glRangeSum n f = glRangeSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [glRangeSum, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

private theorem glRangeSum_zero : ∀ n : Nat, glRangeSum n (fun _ => CommRingOps.zero) = CommRingOps.zero
  | 0 => rfl
  | n + 1 => by simp only [glRangeSum, glRangeSum_zero n, LawfulCommRing.add_zero]

private theorem glRangeSum_const_one : ∀ n : Nat, glRangeSum n (fun _ => CommRingOps.one) = Goldilocks.ofNat n
  | 0 => rfl
  | n + 1 => by
    simp only [glRangeSum, glRangeSum_const_one n]
    apply Goldilocks.ext
    change (Goldilocks.add (Goldilocks.ofNat n) Goldilocks.one).val = (Goldilocks.ofNat (n + 1)).val
    rw [Goldilocks.add_val, Goldilocks.ofNat_val, Goldilocks.one_val, Goldilocks.ofNat_val, Nat.mod_add_mod]

private theorem glRangeSum_mul_left (c : Goldilocks) :
    ∀ (n : Nat) (f : Nat → Goldilocks),
      CommRingOps.mul c (glRangeSum n f) = glRangeSum n (fun i => CommRingOps.mul c (f i))
  | 0, _ => LawfulCommRing.mul_zero c
  | n + 1, f => by
    simp only [glRangeSum, LawfulCommRing.left_distrib, glRangeSum_mul_left c n f]

private theorem glRangeSum_mul_right (c : Goldilocks) :
    ∀ (n : Nat) (f : Nat → Goldilocks),
      CommRingOps.mul (glRangeSum n f) c = glRangeSum n (fun i => CommRingOps.mul (f i) c)
  | 0, _ => LawfulCommRing.zero_mul c
  | n + 1, f => by
    simp only [glRangeSum, LawfulCommRing.right_distrib, glRangeSum_mul_right c n f]

private theorem glRangeSum_add :
    ∀ (n : Nat) (f g : Nat → Goldilocks),
      glRangeSum n (fun i => CommRingOps.add (f i) (g i)) =
        CommRingOps.add (glRangeSum n f) (glRangeSum n g)
  | 0, _, _ => (LawfulCommRing.add_zero CommRingOps.zero).symm
  | n + 1, f, g => by
    simp only [glRangeSum, glRangeSum_add n f g, LawfulCommRing.add_add_add_comm]

private theorem glRangeSum_swap :
    ∀ (n m : Nat) (f : Nat → Nat → Goldilocks),
      glRangeSum n (fun i => glRangeSum m (fun j => f i j)) =
        glRangeSum m (fun j => glRangeSum n (fun i => f i j))
  | 0, m, _ => (glRangeSum_zero m).symm
  | n + 1, m, f => by
    simp only [glRangeSum, glRangeSum_swap n m f, ← glRangeSum_add]

private theorem glGeomSum_telescopes (r : Goldilocks) :
    ∀ n : Nat,
      CommRingOps.mul (CommRingOps.sub r CommRingOps.one) (glRangeSum n (fun j => glPow r j)) =
        CommRingOps.sub (glPow r n) CommRingOps.one
  | 0 => by simp only [glRangeSum, glPow, LawfulCommRing.mul_zero, LawfulCommRing.sub_self]
  | n + 1 => by
    simp only [glRangeSum, LawfulCommRing.left_distrib, glGeomSum_telescopes r n]
    rw [LawfulCommRing.sub_mul, LawfulCommRing.one_mul]
    change CommRingOps.add (CommRingOps.sub (glPow r n) CommRingOps.one)
        (CommRingOps.sub (glPow r (n + 1)) (glPow r n)) =
      CommRingOps.sub (glPow r (n + 1)) CommRingOps.one
    rw [LawfulCommRing.add_comm (CommRingOps.sub (glPow r n) _) _,
        LawfulCommRing.sub_eq_add_neg (glPow r (n + 1)) (glPow r n),
        LawfulCommRing.add_assoc,
        LawfulCommRing.add_comm (CommRingOps.neg (glPow r n)) _,
        LawfulCommRing.sub_eq_add_neg (glPow r n) CommRingOps.one,
        LawfulCommRing.add_assoc (glPow r n) _ _,
        LawfulCommRing.add_comm (CommRingOps.neg CommRingOps.one) (CommRingOps.neg (glPow r n)),
        ← LawfulCommRing.add_assoc (glPow r n) (CommRingOps.neg (glPow r n)) _,
        LawfulCommRing.add_right_neg, LawfulCommRing.zero_add,
        ← LawfulCommRing.sub_eq_add_neg]

private theorem glGeomSum_eq_zero_of_root {r : Goldilocks} {n : Nat}
    (hRoot : glPow r n = CommRingOps.one) (hNeOne : r ≠ CommRingOps.one) :
    glRangeSum n (fun j => glPow r j) = CommRingOps.zero := by
  have hSubNe : CommRingOps.sub r CommRingOps.one ≠ CommRingOps.zero :=
    fun hz => hNeOne (LawfulCommRing.sub_eq_zero_iff.mp hz)
  have hProd : CommRingOps.mul (CommRingOps.sub r CommRingOps.one)
      (glRangeSum n (fun j => glPow r j)) = CommRingOps.zero := by
    rw [glGeomSum_telescopes, hRoot, LawfulCommRing.sub_self]
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hProd with hBad | hZero
  · exact False.elim (hSubNe hBad)
  · exact hZero

private theorem glRangeSum_single_of_eq {n m : Nat} (hm : m < n)
    (f : Nat → Goldilocks) (hZero : ∀ k < n, k ≠ m → f k = CommRingOps.zero) :
    glRangeSum n f = f m := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold glRangeSum
    by_cases hmn : m = n
    · subst hmn
      have hPre : glRangeSum m f = CommRingOps.zero := by
        rw [glRangeSum_congr (g := fun _ => CommRingOps.zero)
          (fun k hk => hZero k (Nat.lt_succ_of_lt hk) (Nat.ne_of_lt hk)), glRangeSum_zero]
      rw [hPre, LawfulCommRing.zero_add]
    · have hmLt : m < n := by omega
      rw [ih hmLt (fun k hk hne => hZero k (Nat.lt_succ_of_lt hk) hne),
          hZero n (Nat.lt_succ_self n) (Ne.symm hmn),
          LawfulCommRing.add_zero]

/-- Certified primitive $n$-th root-of-unity domain over `Goldilocks`, bundling $\omega$, $\omega^{-1}$,
    and length normalizer $n^{-1}$ with constructive primitivity (`\omega^d \neq 1` for $0 < d < n$). -/
structure NttDomain (n : Nat) where
  hPos : 0 < n
  omega : Goldilocks
  omegaInv : Goldilocks
  nInv : Goldilocks
  hPowN : glPow omega n = CommRingOps.one
  hOmegaInv : CommRingOps.mul omega omegaInv = CommRingOps.one
  hNInv : CommRingOps.mul nInv (Goldilocks.ofNat n) = CommRingOps.one
  hPrim : ∀ d : Nat, 0 < d → d < n → glPow omega d ≠ CommRingOps.one

private theorem glPow_val (x : Goldilocks) :
    ∀ k : Nat, (glPow x k).val = (x.val ^ k) % goldilocksPrime
  | 0 => rfl
  | k + 1 => by
    simp only [glPow]
    change (Goldilocks.mul x (glPow x k)).val = (x.val ^ (k + 1)) % goldilocksPrime
    rw [Goldilocks.mul_val, glPow_val x k, Nat.mul_mod_mod, Nat.pow_succ, Nat.mul_comm]

/-- Concrete primitive 8th-root-of-unity `Goldilocks` NTT domain ($\omega = 2^{24}$, $\omega^4 = 2^{96} \equiv -1 \pmod p$). -/
def goldilocksNttDomain8 : NttDomain 8 where
  hPos := by decide
  omega := Goldilocks.ofNat (2 ^ 24)
  omegaInv := Goldilocks.inv (Goldilocks.ofNat (2 ^ 24))
  nInv := Goldilocks.inv (Goldilocks.ofNat 8)
  hPowN := by
    apply Goldilocks.ext
    rw [glPow_val, Goldilocks.ofNat_val]
    change (((2 ^ 24) % goldilocksPrime) ^ 8) % goldilocksPrime = 1
    decide
  hOmegaInv := Goldilocks.mul_inv_cancel (fun h => by
    have hv := congrArg Goldilocks.val h
    simp only [Goldilocks.ofNat_val, Goldilocks.zero_val] at hv
    revert hv; decide)
  hNInv := by
    rw [LawfulCommRing.mul_comm]
    exact Goldilocks.mul_inv_cancel (fun h => by
      have hv := congrArg Goldilocks.val h
      simp only [Goldilocks.ofNat_val, Goldilocks.zero_val] at hv
      revert hv; decide)
  hPrim := by
    intro d hd0 hd8 hEq
    have hv := congrArg Goldilocks.val hEq
    rw [glPow_val, Goldilocks.ofNat_val] at hv
    change (((2 ^ 24) % goldilocksPrime) ^ d) % goldilocksPrime = 1 at hv
    have hCases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (revert hv; decide)

/-- Forward $n$-point Number-Theoretic Transform $\hat{a}_j = \sum_{k=0}^{n-1} a_k \omega^{j k}$. -/
def nttForward {n : Nat} (dom : NttDomain n) (coeffs : Fin n → Goldilocks) (j : Fin n) : Goldilocks :=
  glRangeSum n (fun k =>
    if hk : k < n then CommRingOps.mul (coeffs ⟨k, hk⟩) (glPow dom.omega (k * j.val))
    else CommRingOps.zero)

/-- Normalized $n$-point Inverse Number-Theoretic Transform $a_m = n^{-1} \sum_{j=0}^{n-1} \hat{a}_j (\omega^{-1})^{j m}$. -/
def nttInverse {n : Nat} (dom : NttDomain n) (evals : Fin n → Goldilocks) (m : Fin n) : Goldilocks :=
  CommRingOps.mul dom.nInv
    (glRangeSum n (fun j =>
      if hj : j < n then CommRingOps.mul (evals ⟨j, hj⟩) (glPow dom.omegaInv (m.val * j))
      else CommRingOps.zero))

private theorem dom_omegaInv_pow_n {n : Nat} (dom : NttDomain n) :
    glPow dom.omegaInv n = CommRingOps.one := by
  have h1 : CommRingOps.mul (glPow dom.omega n) (glPow dom.omegaInv n) = CommRingOps.one := by
    rw [← glPow_mul_distrib, dom.hOmegaInv, glPow_one]
  rwa [dom.hPowN, LawfulCommRing.one_mul] at h1

/-- **Genuine Forward/Inverse NTT Roundtrip Theorem (`nttInverse_nttForward_roundtrip`)**:
    Over EVERY certified `NttDomain n`, `nttInverse dom (nttForward dom coeffs) = coeffs`
    and `nttForward dom (nttInverse dom evals) = evals`! -/
theorem nttInverse_nttForward_roundtrip {n : Nat} (dom : NttDomain n) :
    (∀ coeffs : Fin n → Goldilocks, nttInverse dom (nttForward dom coeffs) = coeffs) ∧
    (∀ evals : Fin n → Goldilocks, nttForward dom (nttInverse dom evals) = evals) := by
  have hInvFwd : ∀ (d : NttDomain n) (coeffs : Fin n → Goldilocks) (m : Fin n),
      nttInverse d (nttForward d coeffs) m = coeffs m := by
    intro d coeffs m
    unfold nttInverse nttForward
    have hStripJ :
        glRangeSum n (fun j =>
          if hj : j < n then
            CommRingOps.mul
              (glRangeSum n (fun k =>
                if hk : k < n then CommRingOps.mul (coeffs ⟨k, hk⟩) (glPow d.omega (k * j))
                else CommRingOps.zero))
              (glPow d.omegaInv (m.val * j))
          else CommRingOps.zero) =
        glRangeSum n (fun j =>
          glRangeSum n (fun k =>
            CommRingOps.mul
              (if hk : k < n then coeffs ⟨k, hk⟩ else CommRingOps.zero)
              (glPow (CommRingOps.mul (glPow d.omega k) (glPow d.omegaInv m.val)) j))) := by
      apply glRangeSum_congr
      intro j hj
      simp only [hj, ↓reduceDIte, glRangeSum_mul_right]
      apply glRangeSum_congr
      intro k hk
      simp only [hk, ↓reduceDIte, LawfulCommRing.mul_assoc, glPow_mul_distrib,
        ← glPow_mul]
    rw [hStripJ, glRangeSum_swap]
    have hPullC :
        glRangeSum n (fun k =>
          glRangeSum n (fun j =>
            CommRingOps.mul
              (if hk : k < n then coeffs ⟨k, hk⟩ else CommRingOps.zero)
              (glPow (CommRingOps.mul (glPow d.omega k) (glPow d.omegaInv m.val)) j))) =
        glRangeSum n (fun k =>
          CommRingOps.mul
            (if hk : k < n then coeffs ⟨k, hk⟩ else CommRingOps.zero)
            (glRangeSum n (fun j =>
              glPow (CommRingOps.mul (glPow d.omega k) (glPow d.omegaInv m.val)) j))) := by
      apply glRangeSum_congr
      intro k _
      exact (glRangeSum_mul_left _ n _).symm
    rw [hPullC]
    have hOrthog : ∀ k < n, k ≠ m.val →
        CommRingOps.mul
          (if hk : k < n then coeffs ⟨k, hk⟩ else CommRingOps.zero)
          (glRangeSum n (fun j =>
            glPow (CommRingOps.mul (glPow d.omega k) (glPow d.omegaInv m.val)) j)) =
        CommRingOps.zero := by
      intro k hk hne
      let r := CommRingOps.mul (glPow d.omega k) (glPow d.omegaInv m.val)
      have hRoot : glPow r n = CommRingOps.one := by
        dsimp only [r]
        rw [glPow_mul_distrib, ← glPow_mul, ← glPow_mul, Nat.mul_comm k n, Nat.mul_comm m.val n,
            glPow_mul d.omega n k, glPow_mul d.omegaInv n m.val, d.hPowN, dom_omegaInv_pow_n d,
            glPow_one, glPow_one, LawfulCommRing.one_mul]
      have hNeOne : r ≠ CommRingOps.one := by
        intro hr1
        by_cases hlt : m.val < k
        · let diff := k - m.val
          have hDiffPos : 0 < diff := by omega
          have hDiffLt : diff < n := by omega
          have hkEq : k = diff + m.val := by omega
          have hrEq : r = glPow d.omega diff := by
            dsimp only [r]
            rw [hkEq, glPow_add, LawfulCommRing.mul_assoc, ← glPow_mul_distrib,
                d.hOmegaInv, glPow_one, LawfulCommRing.mul_one]
          rw [hrEq] at hr1
          exact d.hPrim diff hDiffPos hDiffLt hr1
        · have hlt' : k < m.val := by omega
          let diff := m.val - k
          have hDiffPos : 0 < diff := by omega
          have hDiffLt : diff < n := by omega
          have hmEq : m.val = diff + k := by omega
          have hCancel : CommRingOps.mul (glPow d.omega diff) r = CommRingOps.one := by
            dsimp only [r]
            rw [← LawfulCommRing.mul_assoc, ← glPow_add, ← hmEq,
                ← glPow_mul_distrib, d.hOmegaInv, glPow_one]
          have hEqDiff : glPow d.omega diff = CommRingOps.one := by
            calc glPow d.omega diff
              _ = CommRingOps.mul (glPow d.omega diff) CommRingOps.one := (LawfulCommRing.mul_one _).symm
              _ = CommRingOps.mul (glPow d.omega diff) r := by rw [hr1]
              _ = CommRingOps.one := hCancel
          exact d.hPrim diff hDiffPos hDiffLt hEqDiff
      have hSum0 := glGeomSum_eq_zero_of_root hRoot hNeOne
      change CommRingOps.mul _ (glRangeSum n (fun j => glPow r j)) = CommRingOps.zero
      rw [hSum0, LawfulCommRing.mul_zero]
    rw [glRangeSum_single_of_eq m.isLt _ hOrthog]
    simp only [m.isLt, ↓reduceDIte]
    have hDiag : CommRingOps.mul (glPow d.omega m.val) (glPow d.omegaInv m.val) = CommRingOps.one := by
      rw [← glPow_mul_distrib, d.hOmegaInv, glPow_one]
    rw [hDiag]
    have hOnes : glRangeSum n (fun j => glPow CommRingOps.one j) = Goldilocks.ofNat n := by
      rw [glRangeSum_congr (g := fun _ => CommRingOps.one) (fun j _ => glPow_one j),
          glRangeSum_const_one]
    rw [hOnes, LawfulCommRing.mul_comm (coeffs m) (Goldilocks.ofNat n),
        ← LawfulCommRing.mul_assoc, d.hNInv, LawfulCommRing.one_mul]
  refine ⟨fun coeffs => funext (hInvFwd dom coeffs), ?_⟩
  intro evals
  funext j
  -- Dual domain swapping `omega` and `omegaInv`:
  let dualDom : NttDomain n :=
    { hPos := dom.hPos
      omega := dom.omegaInv
      omegaInv := dom.omega
      nInv := dom.nInv
      hPowN := dom_omegaInv_pow_n dom
      hOmegaInv := by rw [LawfulCommRing.mul_comm]; exact dom.hOmegaInv
      hNInv := dom.hNInv
      hPrim := by
        intro d hd0 hdn hInv1
        apply dom.hPrim d hd0 hdn
        have hProd : CommRingOps.mul (glPow dom.omega d) (glPow dom.omegaInv d) = CommRingOps.one := by
          rw [← glPow_mul_distrib, dom.hOmegaInv, glPow_one]
        rwa [hInv1, LawfulCommRing.mul_one] at hProd }
  have hDual := hInvFwd dualDom evals j
  unfold nttInverse nttForward at hDual ⊢
  dsimp only [dualDom] at hDual ⊢
  have hPull :
      glRangeSum n (fun k =>
        if hk : k < n then
          CommRingOps.mul
            (CommRingOps.mul dom.nInv
              (glRangeSum n (fun i =>
                if hi : i < n then CommRingOps.mul (evals ⟨i, hi⟩) (glPow dom.omegaInv (k * i))
                else CommRingOps.zero)))
            (glPow dom.omega (k * j.val))
        else CommRingOps.zero) =
      CommRingOps.mul dom.nInv
        (glRangeSum n (fun k =>
          if hk : k < n then
            CommRingOps.mul
              (glRangeSum n (fun i =>
                if hi : i < n then CommRingOps.mul (evals ⟨i, hi⟩) (glPow dom.omegaInv (i * k))
                else CommRingOps.zero))
              (glPow dom.omega (j.val * k))
          else CommRingOps.zero)) := by
    rw [glRangeSum_mul_left]
    apply glRangeSum_congr
    intro k hk
    simp only [hk, ↓reduceDIte, LawfulCommRing.mul_assoc, Nat.mul_comm k j.val]
    congr 2
    apply glRangeSum_congr
    intro i hi
    simp only [hi, ↓reduceDIte, Nat.mul_comm k i]
  exact hPull.trans hDual

/-- **`#tooth` (`tooth_negated_twiddle_not_inverse_ntt`)**:
    Negating evaluation points (`goldilocksNttSpec ... true`) on `[1, 0]` over twiddles `[1, -1]`
    maps `[1, 0] ↦ [1, 1] ↦ [2, 2] ≠ [1, 0]`, whereas `nttInverse goldilocksNttDomain8`
    inverts `nttForward goldilocksNttDomain8` identically! -/
theorem tooth_negated_twiddle_not_inverse_ntt :
    goldilocksNttSpec
      (goldilocksNttSpec [Goldilocks.one, Goldilocks.zero]
        [Goldilocks.one, Goldilocks.neg Goldilocks.one] false)
      [Goldilocks.one, Goldilocks.neg Goldilocks.one] true ≠
    [Goldilocks.one, Goldilocks.zero] := by
  intro hEq
  have hv := congrArg (fun xs => xs.map Goldilocks.val) hEq
  simp only [goldilocksNttSpec, hornerEval, List.map, Bool.false_eq_true, ↓reduceIte] at hv
  change [((CommRingOps.add (CommRingOps.add Goldilocks.one (CommRingOps.mul Goldilocks.one CommRingOps.zero))
      (CommRingOps.mul (Goldilocks.neg Goldilocks.one)
        (CommRingOps.add (CommRingOps.add Goldilocks.one (CommRingOps.mul (Goldilocks.neg Goldilocks.one) CommRingOps.zero))
          (CommRingOps.mul (Goldilocks.neg Goldilocks.one) CommRingOps.zero))))).val, _] =
    [1, 0] at hv
  injection hv with hv0 hv1
  injection hv1 with hv1' _
  simp only [CommRingOps.add, CommRingOps.mul, CommRingOps.zero, Goldilocks.add_val,
    Goldilocks.mul_val, Goldilocks.neg_val, Goldilocks.one_val, Goldilocks.zero_val] at hv1'
  revert hv1'
  decide

#tooth_pair goldilocksNttButterflyExec_refines_spec vs tooth_negated_twiddle_not_inverse_ntt

/-- Genuine multiplicative-coset Low-Degree Extension (`Spec` vs Cooley-Tukey pre-scaled `Exec`):
    interpolates `evals : Fin n → Goldilocks` via `nttInverse srcDom`, requires non-zero `shift ≠ 0`,
    and evaluates at all `n * blowup` coset points `shift * ω_{n*blowup}^j`. -/
def multiplicativeCosetLdeSpec {n blowup : Nat}
    (srcDom : NttDomain n) (ldeDom : NttDomain (n * blowup))
    (shift : Goldilocks) (evals : Fin n → Goldilocks) : List Goldilocks :=
  let coeffs := List.ofFn (nttInverse srcDom evals)
  (List.range (n * blowup)).map (fun j =>
    hornerEval coeffs (CommRingOps.mul shift (glPow ldeDom.omega j)))

def multiplicativeCosetLdeExec {n blowup : Nat}
    (srcDom : NttDomain n) (ldeDom : NttDomain (n * blowup))
    (shift : Goldilocks) (evals : Fin n → Goldilocks) : List Goldilocks :=
  let coeffs := List.ofFn (nttInverse srcDom evals)
  let scaled := scalePowers coeffs shift
  let twiddles := (List.range (n * blowup)).map (fun j => glPow ldeDom.omega j)
  goldilocksNttButterflyExec scaled twiddles false

theorem multiplicativeCosetLdeExec_eq_spec {n blowup : Nat}
    (srcDom : NttDomain n) (ldeDom : NttDomain (n * blowup))
    (shift : Goldilocks) (hShiftNeZero : shift ≠ Goldilocks.zero)
    (evals : Fin n → Goldilocks) :
    (∀ x y : Goldilocks, CommRingOps.mul shift x = CommRingOps.mul shift y → x = y) ∧
    (multiplicativeCosetLdeExec srcDom ldeDom shift evals).length = n * blowup ∧
    multiplicativeCosetLdeExec srcDom ldeDom shift evals =
      multiplicativeCosetLdeSpec srcDom ldeDom shift evals := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hMul
    have hSub : CommRingOps.mul shift (CommRingOps.sub x y) = CommRingOps.zero := by
      rw [LawfulCommRing.mul_sub, hMul, LawfulCommRing.sub_self]
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hSub with hBad | hDiff0
    · exact False.elim (hShiftNeZero hBad)
    · exact LawfulCommRing.sub_eq_zero_iff.mp hDiff0
  · simp [multiplicativeCosetLdeExec, goldilocksNttButterflyExec]
  · unfold multiplicativeCosetLdeExec multiplicativeCosetLdeSpec
    rw [goldilocksNttButterflyExec_refines_spec]
    unfold goldilocksNttSpec
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, Bool.false_eq_true, ↓reduceIte, hornerEval_cosetShift_eq]

/-- Fixed-width 4-limb Merkle digest and 4-limb public seed (`MerkleNode4`, `MerkleSeed4`),
    eliminating variable-length zero-padding / tail-truncation and odd-sibling structural aliases. -/
abbrev MerkleNode4 := Fin 4 → Goldilocks
abbrev MerkleSeed4 := Fin 4 → Goldilocks

/-- 2-block width-12 `Poseidon2` compression encoding ALL 4 limbs of `left`, ALL 4 limbs of `right`,
    ALL 4 limbs of `pkSeed`, AND bounded `(layer < 32, idx < 2^32)` with domain tag `1`. -/
def merkleFixedBlock1 (left right : MerkleNode4) (pkSeed : MerkleSeed4) : Poseidon2State12 :=
  ⟨⟨left 0, left 1, left 2, left 3⟩,
   ⟨right 0, right 1, right 2, right 3⟩,
   ⟨pkSeed 0, pkSeed 1, pkSeed 2, pkSeed 3⟩⟩

theorem merkleFixedBlock1_injective {l1 r1 : MerkleNode4} {s1 : MerkleSeed4}
    {l2 r2 : MerkleNode4} {s2 : MerkleSeed4}
    (h : merkleFixedBlock1 l1 r1 s1 = merkleFixedBlock1 l2 r2 s2) :
    l1 = l2 ∧ r1 = r2 ∧ s1 = s2 := by
  unfold merkleFixedBlock1 at h
  injection h with hb0 hb1 hb2
  injection hb0 with hl0 hl1 hl2 hl3
  injection hb1 with hr0 hr1 hr2 hr3
  injection hb2 with hs0 hs1 hs2 hs3
  refine ⟨?_, ?_, ?_⟩
  · funext i
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by have := i.isLt; omega
    rcases hi with h0 | h1 | h2 | h3
    · rw [show i = 0 from Fin.ext h0]; exact hl0
    · rw [show i = 1 from Fin.ext h1]; exact hl1
    · rw [show i = 2 from Fin.ext h2]; exact hl2
    · rw [show i = 3 from Fin.ext h3]; exact hl3
  · funext i
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by have := i.isLt; omega
    rcases hi with h0 | h1 | h2 | h3
    · rw [show i = 0 from Fin.ext h0]; exact hr0
    · rw [show i = 1 from Fin.ext h1]; exact hr1
    · rw [show i = 2 from Fin.ext h2]; exact hr2
    · rw [show i = 3 from Fin.ext h3]; exact hr3
  · funext i
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by have := i.isLt; omega
    rcases hi with h0 | h1 | h2 | h3
    · rw [show i = 0 from Fin.ext h0]; exact hs0
    · rw [show i = 1 from Fin.ext h1]; exact hs1
    · rw [show i = 2 from Fin.ext h2]; exact hs2
    · rw [show i = 3 from Fin.ext h3]; exact hs3

def merkleCompressFixed4 (left right : MerkleNode4) (pkSeed : MerkleSeed4)
    (layer : Fin 32) (idx : Fin (2 ^ 32)) : MerkleNode4 :=
  let mid := poseidon2Perm12 (merkleFixedBlock1 left right pkSeed)
  let st2 : Poseidon2State12 :=
    ⟨mid.b0, mid.b1,
     ⟨Goldilocks.add mid.b2.x0 (Goldilocks.ofNat layer.val),
      Goldilocks.add mid.b2.x1 (Goldilocks.ofNat idx.val),
      Goldilocks.add mid.b2.x2 Goldilocks.one,
      mid.b2.x3⟩⟩
  let out := poseidon2Perm12 st2
  fun i =>
    if i.val = 0 then out.b0.x0
    else if i.val = 1 then out.b0.x1
    else if i.val = 2 then out.b0.x2
    else out.b0.x3

/-- Explicit reachable Merkle pair-compression collision at `(pkSeed, layer, idx)`. -/
def MerkleFixedCompressCollision (pkSeed : MerkleSeed4) (layer : Fin 32) (idx : Fin (2 ^ 32)) : Prop :=
  ∃ (l1 r1 l2 r2 : MerkleNode4),
    (l1, r1) ≠ (l2, r2) ∧
    merkleCompressFixed4 l1 r1 pkSeed layer idx = merkleCompressFixed4 l2 r2 pkSeed layer idx

def merkleNode4Eq (a b : MerkleNode4) : Bool :=
  decide ((a 0).val = (b 0).val ∧ (a 1).val = (b 1).val ∧
          (a 2).val = (b 2).val ∧ (a 3).val = (b 3).val)

theorem merkleNode4Eq_iff (a b : MerkleNode4) :
    merkleNode4Eq a b = true ↔ a = b := by
  unfold merkleNode4Eq
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    apply Goldilocks.ext
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by have := i.isLt; omega
    rcases hi with h | h | h | h
    · rw [show i = 0 from Fin.ext h]; exact h0
    · rw [show i = 1 from Fin.ext h]; exact h1
    · rw [show i = 2 from Fin.ext h]; exact h2
    · rw [show i = 3 from Fin.ext h]; exact h3
  · intro h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Checked even-pair complete-tree layer reduction: rejects empty or odd-cardinality layers (`none`). -/
def merkleCompleteLayerChecked (pkSeed : MerkleSeed4) (layer : Fin 32) :
    List MerkleNode4 → Nat → Option (List MerkleNode4)
  | [], _ => some []
  | [_], _ => none
  | l :: r :: rest, idx =>
    if hIdx : idx < 2 ^ 32 then do
      let tail ← merkleCompleteLayerChecked pkSeed layer rest (idx + 1)
      some (merkleCompressFixed4 l r pkSeed layer ⟨idx, hIdx⟩ :: tail)
    else none

theorem merkleCompleteLayerChecked_binding_or_collision
    (pkSeed : MerkleSeed4) (layer : Fin 32) :
    ∀ (xs ys : List MerkleNode4) (idx : Nat) (out : List MerkleNode4),
      merkleCompleteLayerChecked pkSeed layer xs idx = some out →
      merkleCompleteLayerChecked pkSeed layer ys idx = some out →
      xs = ys ∨ ∃ j : Fin (2 ^ 32), MerkleFixedCompressCollision pkSeed layer j
  | [], [], _, _, _, _ => Or.inl rfl
  | [], [_], _, _, _, hy => by simp [merkleCompleteLayerChecked] at hy
  | [], _ :: _ :: _, _, _, hx, hy => by
    simp only [merkleCompleteLayerChecked] at hx hy
    injection hx with hx0; subst hx0
    split at hy
    · cases hm : merkleCompleteLayerChecked pkSeed layer _ _
      · rw [hm] at hy; cases hy
      · rw [hm] at hy; cases hy
    · cases hy
  | [_], _, _, _, hx, _ => by simp [merkleCompleteLayerChecked] at hx
  | _ :: _ :: _, [], _, _, hx, hy => by
    simp only [merkleCompleteLayerChecked] at hx hy
    injection hy with hy0; subst hy0
    split at hx
    · cases hm : merkleCompleteLayerChecked pkSeed layer _ _
      · rw [hm] at hx; cases hx
      · rw [hm] at hx; cases hx
    · cases hx
  | _ :: _ :: _, [_], _, _, _, hy => by simp [merkleCompleteLayerChecked] at hy
  | l1 :: r1 :: xs, l2 :: r2 :: ys, idx, out, hx, hy => by
    simp only [merkleCompleteLayerChecked] at hx hy
    split at hx
    · next hIdx =>
      simp only [hIdx, ↓reduceDIte] at hy
      cases htx : merkleCompleteLayerChecked pkSeed layer xs (idx + 1) with
      | none => rw [htx] at hx; cases hx
      | some tx =>
        cases hty : merkleCompleteLayerChecked pkSeed layer ys (idx + 1) with
        | none => rw [hty] at hy; cases hy
        | some ty =>
          rw [htx] at hx
          rw [hty] at hy
          dsimp [Bind.bind, Option.bind] at hx hy
          have hComb : merkleCompressFixed4 l1 r1 pkSeed layer ⟨idx, hIdx⟩ :: tx =
              merkleCompressFixed4 l2 r2 pkSeed layer ⟨idx, hIdx⟩ :: ty :=
            Option.some.inj (hx.trans hy.symm)
          injection hComb with hHead hTail
          subst hTail
          cases hEq : (merkleNode4Eq l1 l2 && merkleNode4Eq r1 r2) with
          | true =>
            rw [Bool.and_eq_true, merkleNode4Eq_iff, merkleNode4Eq_iff] at hEq
            rcases hEq with ⟨hl, hr⟩
            subst hl hr
            rcases merkleCompleteLayerChecked_binding_or_collision pkSeed layer xs ys (idx + 1) tx htx hty with
              hRestEq | hCol
            · exact Or.inl (by rw [hRestEq])
            · exact Or.inr hCol
          | false =>
            have hPairNe : (l1, r1) ≠ (l2, r2) := by
              intro hPair
              injection hPair with hl hr
              have hTrue : (merkleNode4Eq l1 l2 && merkleNode4Eq r1 r2) = true := by
                rw [Bool.and_eq_true, merkleNode4Eq_iff, merkleNode4Eq_iff]
                exact ⟨hl, hr⟩
              rw [hEq] at hTrue
              cases hTrue
            exact Or.inr ⟨⟨idx, hIdx⟩, l1, r1, l2, r2, hPairNe, hHead⟩
    · cases hx

/-- **`#tooth` (`tooth_unpadded_list_merkle_aliases_empty_and_zero`)**:
    `merkleCompleteLayerChecked` deterministically rejects singleton (`xs.length = 1`) layers (`= none`),
    closing odd-sibling structural aliasing! -/
theorem tooth_unpadded_list_merkle_aliases_empty_and_zero
    (pkSeed : MerkleSeed4) (layer : Fin 32) (idx : Nat)
    (xs : List MerkleNode4) (hSingleton : xs.length = 1) :
    merkleCompleteLayerChecked pkSeed layer xs idx = none := by
  rcases xs with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · cases hSingleton
  · simp [merkleCompleteLayerChecked]
  · cases hSingleton

#tooth_pair merkleCompleteLayerChecked_binding_or_collision vs
  tooth_unpadded_list_merkle_aliases_empty_and_zero


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
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases hl
  | cons x xs ih =>
    cases ys with
    | nil => cases hl
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

/-- Count prefixes recover the shape as well as every secret wire. Thus the
wire encoding is injective without assuming equal circuit sizes beforehand. -/
theorem viewBytes_injective (a b : PartyView) (h : viewBytes a = viewBytes b) :
    a.seed.val = b.seed.val ∧ a.inputs = b.inputs ∧
    a.gates = b.gates ∧ a.outputs = b.outputs := by
  simp only [viewBytes, List.append_assoc] at h
  have hDomain := List.append_inj h (by rfl)
  have hSeed := List.append_inj hDomain.2 (by rw [a.seed.property, b.seed.property])
  have hInputsCount := List.append_inj hSeed.2 (by simp [le])
  have hi : a.inputs.length = b.inputs.length := le_injective
    (by simpa using a.inputsBound) (by simpa using b.inputsBound) hInputsCount.1
  have hInputs := List.append_inj hInputsCount.2 (by rw [words_length, words_length, hi])
  have hGatesCount := List.append_inj hInputs.2 (by simp [le])
  have hg : a.gates.length = b.gates.length := le_injective
    (by simpa using a.gatesBound) (by simpa using b.gatesBound) hGatesCount.1
  have hGates := List.append_inj hGatesCount.2 (by rw [words_length, words_length, hg])
  have hOutputsCount := List.append_inj hGates.2 (by simp [le])
  exact ⟨hSeed.1, words_injective _ _ hInputs.1,
    words_injective _ _ hGates.1, words_injective _ _ hOutputsCount.2⟩

/-- Dropping counts would let an input word become a gate word. The actual
serializer distinguishes those traces even though their flat words coincide. -/
theorem tooth_omitted_counts_alias_wire_roles :
    ∃ xs ys : List Goldilocks,
      words (xs ++ ys) = words (ys ++ xs) ∧ xs ≠ ys := by
  exact ⟨[Goldilocks.one], [], rfl, by intro h; cases h⟩

#tooth_pair viewBytes_injective vs tooth_omitted_counts_alias_wire_roles

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

private theorem block_trit_eq {s q r : Nat} (hs : 0 < s) :
    ((q * (3 * s) + r) / s) % 3 = (r / s) % 3 := by
  have hMul : q * (3 * s) = s * (3 * q) := by
    rw [← Nat.mul_assoc q 3 s, Nat.mul_comm q 3, Nat.mul_comm (3 * q) s]
  rw [hMul, Nat.add_comm (s * (3 * q)) r, Nat.add_mul_div_left r (3 * q) hs,
      Nat.add_mul_mod_self_left]

private theorem filter_nil_constructive {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x ≠ true) : xs.filter p = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = false := Bool.eq_false_iff.mpr (h x (.head _))
    simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun y hy => h y (.tail _ hy))

private theorem filter_range_three_mul {s t : Nat} (hs : 0 < s) (ht : t < 3) :
    ((List.range (3 * s)).filter (fun r => (r / s) % 3 == t)).length = s := by
  have hSplit : 3 * s = s + s + s := by omega
  rw [hSplit, List.range_add, List.range_add, List.filter_append, List.filter_append,
      List.length_append, List.length_append, List.filter_map, List.filter_map,
      List.length_map, List.length_map]
  have h0 : (List.range s).filter (fun r => (r / s) % 3 == t) =
      if 0 == t then List.range s else [] := by
    split
    · next h0t =>
      rw [List.filter_eq_self]
      intro r hr
      rw [List.mem_range] at hr
      rw [Nat.div_eq_of_lt hr, Nat.zero_mod]
      exact h0t
    · next h0t =>
      apply filter_nil_constructive
      intro r hr
      rw [List.mem_range] at hr
      rw [Nat.div_eq_of_lt hr, Nat.zero_mod]
      exact h0t
  have h1 : (List.range s).filter ((fun r => (r / s) % 3 == t) ∘ (s + ·)) =
      if 1 == t then List.range s else [] := by
    have hDiv1 : ∀ r < s, ((s + r) / s) % 3 = 1 := by
      intro r hr
      have hs1 : s + r = r + s * 1 := by omega
      rw [hs1, Nat.add_mul_div_left r 1 hs, Nat.div_eq_of_lt hr]
    split
    · next h1t =>
      rw [List.filter_eq_self]
      intro r hr
      rw [List.mem_range] at hr
      simpa only [Function.comp_apply, hDiv1 r hr] using h1t
    · next h1t =>
      apply filter_nil_constructive
      intro r hr
      rw [List.mem_range] at hr
      simpa only [Function.comp_apply, hDiv1 r hr] using h1t
  have h2 : (List.range s).filter ((fun r => (r / s) % 3 == t) ∘ (s + s + ·)) =
      if 2 == t then List.range s else [] := by
    have hDiv2 : ∀ r < s, ((s + s + r) / s) % 3 = 2 := by
      intro r hr
      have hs2 : s + s + r = r + s * 2 := by omega
      rw [hs2, Nat.add_mul_div_left r 2 hs, Nat.div_eq_of_lt hr]
    split
    · next h2t =>
      rw [List.filter_eq_self]
      intro r hr
      rw [List.mem_range] at hr
      simpa only [Function.comp_apply, hDiv2 r hr] using h2t
    · next h2t =>
      apply filter_nil_constructive
      intro r hr
      rw [List.mem_range] at hr
      simpa only [Function.comp_apply, hDiv2 r hr] using h2t
  rw [h0, h1, h2]
  have htCases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases htCases with rfl | rfl | rfl <;>
    simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
      List.length_range, List.length_nil] <;> omega


private theorem filter_range_blocks (m : Nat) {s t : Nat} (hs : 0 < s) (ht : t < 3) :
    ((List.range (m * (3 * s))).filter (fun b => (b / s) % 3 == t)).length = m * s := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hMul : (m + 1) * (3 * s) = m * (3 * s) + 3 * s := Nat.succ_mul m (3 * s)
    rw [hMul, List.range_add, List.filter_append, List.length_append, ih, List.filter_map,
        List.length_map]
    have hCongr :
        (List.range (3 * s)).filter ((fun b => (b / s) % 3 == t) ∘ (m * (3 * s) + ·)) =
          (List.range (3 * s)).filter (fun r => (r / s) % 3 == t) := by
      apply List.filter_congr
      intro r _
      simp only [Function.comp, block_trit_eq hs]
    rw [hCongr, filter_range_three_mul hs ht, Nat.succ_mul]

/-- Each position of the accepted 243-byte alphabet has exactly 81 preimages
for each trit. -/
theorem accepted_trit_fibers :
    ∀ i ∈ List.range 5, ∀ t ∈ List.range 3,
      ((List.range 243).filter (fun b => (b / 3^i) % 3 == t)).length = 81 := by
  intro i hi t ht
  rw [List.mem_range] at hi ht
  have h1 := filter_range_blocks (3 ^ (4 - i)) (s := 3 ^ i) (t := t)
    (Nat.pow_pos (by decide)) ht
  rcases i with _ | _ | _ | _ | _ | i
  · exact h1
  · exact h1
  · exact h1
  · exact h1
  · exact h1
  · omega

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
  let tr := init "QSAG.BVC.SD.LIMBO256.V2\x00" instanceBytes
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


/-- All raw 64-bit preimages of reduction modulo Goldilocks. The low
`2^32 - 1` residues have two preimages; all other residues have one. -/
def reducedWordPreimages (x : Goldilocks) : List Nat :=
  if x.val < 2 ^ 32 - 1 then [x.val, x.val + goldilocksPrime] else [x.val]

theorem reducedWordPreimages_complete (x : Goldilocks) (w : Nat) :
    w ∈ reducedWordPreimages x ↔ w < 2 ^ 64 ∧ w % goldilocksPrime = x.val := by
  have hx := x.isLt
  have quotient (hw : w < 2 ^ 64) (hn : ¬ w < goldilocksPrime) : w / goldilocksPrime = 1 := by
    change w < 18446744073709551616 at hw
    change ¬ w < 18446744069414584321 at hn
    change w / 18446744069414584321 = 1
    omega
  unfold reducedWordPreimages
  split
  next hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      rcases h with rfl | rfl
      · exact ⟨by change x.val < 18446744069414584321 at hx; omega, Nat.mod_eq_of_lt hx⟩
      · refine ⟨?_, ?_⟩
        · change x.val + 18446744069414584321 < 18446744073709551616
          change x.val < 4294967295 at hs
          omega
        · rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hx]
    · intro ⟨hw, hm⟩
      if hn : w < goldilocksPrime then
        exact .inl ((Nat.mod_eq_of_lt hn).symm.trans hm)
      else
        have he := Nat.mod_add_div w goldilocksPrime
        rw [hm, quotient hw hn, Nat.mul_one] at he
        exact .inr he.symm
  next hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      subst w
      exact ⟨by change x.val < 18446744069414584321 at hx; omega, Nat.mod_eq_of_lt hx⟩
    · intro ⟨hw, hm⟩
      if hn : w < goldilocksPrime then
        exact (Nat.mod_eq_of_lt hn).symm.trans hm
      else
        have he := Nat.mod_add_div w goldilocksPrime
        rw [hm, quotient hw hn, Nat.mul_one] at he
        change x.val + 18446744069414584321 = w at he
        change ¬ x.val < 4294967295 at hs
        change w < 18446744073709551616 at hw
        omega

theorem reducedWordPreimages_nodup (x : Goldilocks) :
    (reducedWordPreimages x).Nodup := by
  unfold reducedWordPreimages
  split
  · refine .cons ?_ (.cons ?_ .nil)
    · intro y hy he
      cases hy with
      | head =>
        have hp : 0 < goldilocksPrime := by decide
        omega
      | tail _ h => cases h
    · intro y hy
      cases hy
  · exact .cons (fun _ h => nomatch h) .nil

/-- Twice the total-variation distance, multiplied by `2^64 * p`.
The two terms are the low and high residue classes from the exact fiber theorem:
low residues have mass `2/2^64`, high residues have mass `1/2^64`. -/
def reducedWordTwiceTvNumerator : Nat :=
  (2 ^ 32 - 1) * (2 * goldilocksPrime - 2 ^ 64) +
    (goldilocksPrime - (2 ^ 32 - 1)) * (2 ^ 64 - goldilocksPrime)

/-- The modulo sampler has distance strictly below `2^-32` from uniform;
this is cross-multiplied integer arithmetic, with no floating-point estimate. -/
theorem reducedWord_statistical_distance_bound :
    reducedWordTwiceTvNumerator * 2 ^ 32 <
      2 * (2 ^ 64 * goldilocksPrime) := by decide

/-- The rejection sampler's failure probability per word is exactly
`(2^32 - 1)/2^64`, below `2^-32`. Conditional on acceptance it is exactly
uniform, by `fieldAcceptedBijection`, rather than merely close to uniform. -/
theorem canonicalWord_rejection_bound :
    2 ^ 64 - goldilocksPrime = 2 ^ 32 - 1 ∧
    (2 ^ 64 - goldilocksPrime) * 2 ^ 32 < 2 ^ 64 := by decide


/-- Exact counts for the legacy 64-bit modulo-three challenge sampler. -/
def tritWordCount (t : Fin 3) : Nat := 2 ^ 64 / 3 + if t.val = 0 then 1 else 0

/-- Enumerating one trit's fiber requires no enumeration of the 64-bit space. -/
def tritWordFiber (t : Fin 3) :
    CredBijection { w : Nat // w < 2 ^ 64 ∧ w % 3 = t.val } (Fin (tritWordCount t)) where
  toFun w := ⟨w.val / 3, by
    have hw := w.property
    have ht := t.isLt
    unfold tritWordCount
    split <;> omega⟩
  invFun j := ⟨3 * j.val + t.val, by
    have hj := j.isLt
    have ht := t.isLt
    unfold tritWordCount at hj
    split at hj <;> constructor <;> omega⟩
  left_inv w := by
    apply Subtype.ext
    have hw := w.property
    dsimp only
    omega
  right_inv j := by
    apply Fin.ext
    have ht := t.isLt
    dsimp only
    omega

/-- The worst two accepted trits have mass `(2*floor(2^64/3)+1)/2^64`,
not exactly `2/3`. Repetition arithmetic must charge this term when the
challenge source is modulo reduction rather than unbiased rejection. -/
theorem tritWord_two_accepting_bound (a b : Fin 3) (hne : a ≠ b) :
    tritWordCount a + tritWordCount b ≤ 2 * (2 ^ 64 / 3) + 1 := by
  have hab : a.val ≠ b.val := fun h => hne (Fin.ext h)
  unfold tritWordCount
  split <;> split <;> omega


/-- Finite sum, retaining a symbolic upper bound for large field alphabets. -/
def samplerSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => samplerSum n f + f n

theorem samplerSum_split (r a b : Nat) : ∀ n,
    samplerSum n (fun x => if x < r then a else b) = min n r * a + (n - r) * b := by
  intro n
  induction n with
  | zero => simp [samplerSum]
  | succ n ih =>
    rw [samplerSum, ih]
    by_cases h : n < r
    · have hn : n ≤ r := by omega
      have hs : n + 1 ≤ r := by omega
      simp only [h, ↓reduceIte]
      rw [Nat.min_eq_left hn, Nat.min_eq_left hs,
        Nat.sub_eq_zero_of_le hn, Nat.sub_eq_zero_of_le hs]
      simp [Nat.add_mul]
    · have hn : r ≤ n := by omega
      have hs : r ≤ n + 1 := by omega
      have hd : n + 1 - r = (n - r) + 1 := by omega
      simp only [h, ↓reduceIte]
      rw [Nat.min_eq_right hn, Nat.min_eq_right hs, hd]
      simp [Nat.add_mul, Nat.add_assoc]

/-- The defining finite sum for twice TV, scaled by `2^64 * p`. Each term
uses the exact fiber multiplicity established by `reducedWordPreimages_complete`. -/
def reducedWordTvSum : Nat :=
  samplerSum goldilocksPrime (fun x =>
    let count := if x < 2 ^ 32 - 1 then 2 else 1
    (goldilocksPrime * count - 2 ^ 64) + (2 ^ 64 - goldilocksPrime * count))

theorem reducedWordTvSum_exact : reducedWordTvSum = reducedWordTwiceTvNumerator := by
  have hterms : (fun x : Nat =>
      let count := if x < 2 ^ 32 - 1 then 2 else 1
      (goldilocksPrime * count - 2 ^ 64) + (2 ^ 64 - goldilocksPrime * count)) =
      (fun x => if x < 2 ^ 32 - 1 then 2 * goldilocksPrime - 2 ^ 64
        else 2 ^ 64 - goldilocksPrime) := by
    funext x
    by_cases h : x < 2 ^ 32 - 1
    · simp only [h, ↓reduceIte] <;> decide
    · simp only [h, ↓reduceIte] <;> decide
  unfold reducedWordTvSum
  rw [hterms, samplerSum_split]
  rfl

theorem reducedWordTvSum_bound :
    reducedWordTvSum * 2 ^ 32 < 2 * (2 ^ 64 * goldilocksPrime) := by
  rw [reducedWordTvSum_exact]
  exact reducedWord_statistical_distance_bound

end BlindVcWire

/-! ## Opened-view simulation for one presentation repetition

One ZKBoo repetition over a straight-line Goldilocks circuit, with the gate
engine of `blind_vc.rs` (`mul_gate`: `z_m = cross_m + r_m[g] - r_{m+1}[g]`,
mask index `g` is the gate position). The verifier's whole view of that
repetition is modelled: every wire of both opened parties, both opened tapes,
and the third party's output shares. For uniform tapes this view is a function
of the opened input shares, the public outputs and fresh coins, through an
explicit coin bijection.

What this does not cover: tapes here are uniform field elements, not the
SHAKE expansion of 32-byte seeds; the commitment to the unopened view enters
only through the salt-translation property stated in the adaptive-challenge
section; and the public outputs themselves (commitment digest, scope tag,
disclosed attributes) are leakage by definition. -/
namespace PresentationView

abbrev Share3 := Fin 3 → Goldilocks
abbrev GateCoin := Goldilocks × Goldilocks × Goldilocks
abbrev OpenPair := Goldilocks × Goldilocks

/-- Operands index earlier wires. A multiplication's mask index is its position
    in the gate list, so two gates never share a tape entry. -/
inductive Gate where
  | constant (c : Goldilocks)
  | add (l r : Nat)
  | mul (l r : Nat)
  deriving DecidableEq

def zeroShare : Share3 := fun _ => CommRingOps.zero

def wire (ws : List Share3) (i : Nat) : Share3 := ws.getD i zeroShare

/-- Tape entries of one gate by role: opened party `e`, its opened neighbour,
    and the unopened party. -/
def tapeOf (e : Fin 3) (c : GateCoin) : Share3 :=
  fun p => if p = e then c.1 else if p = nextParty e then c.2.1 else c.2.2

private theorem nextParty_ne (e : Fin 3) : nextParty e ≠ e := by
  revert e; decide

private theorem nextParty2_ne (e : Fin 3) : nextParty (nextParty e) ≠ e := by
  revert e; decide

private theorem nextParty2_ne_next (e : Fin 3) : nextParty (nextParty e) ≠ nextParty e := by
  revert e; decide

theorem tapeOf_self (e : Fin 3) (c : GateCoin) : tapeOf e c e = c.1 := by
  simp only [tapeOf, ↓reduceIte]

theorem tapeOf_next (e : Fin 3) (c : GateCoin) : tapeOf e c (nextParty e) = c.2.1 := by
  simp only [tapeOf, nextParty_ne e, ↓reduceIte]

theorem tapeOf_next2 (e : Fin 3) (c : GateCoin) :
    tapeOf e c (nextParty (nextParty e)) = c.2.2 := by
  simp only [tapeOf, nextParty2_ne e, nextParty2_ne_next e, ↓reduceIte]

def crossAt (a b : Share3) (i : Fin 3) : Goldilocks :=
  CommRingOps.add (CommRingOps.mul (a i) (b i))
    (CommRingOps.add (CommRingOps.mul (a i) (b (nextParty i)))
      (CommRingOps.mul (a (nextParty i)) (b i)))

private theorem zkBooMulShare_eq_cross (a b tape : Share3) (i : Fin 3) :
    zkBooMulShare a b tape i =
      CommRingOps.add (crossAt a b i) (CommRingOps.sub (tape i) (tape (nextParty i))) := rfl

/-- The prover's gate step on all three parties. -/
def realGate (g : Gate) (tape : Share3) (ws : List Share3) : Share3 :=
  match g with
  | .constant c => fun p => if p.val = 0 then c else CommRingOps.zero
  | .add l r => fun p => CommRingOps.add (wire ws l p) (wire ws r p)
  | .mul l r => zkBooMulShare (wire ws l) (wire ws r) tape

/-- Real coin to simulator coin: the unopened tape entry is traded for the
    neighbour's output share at a multiplication. -/
def simCoin (e : Fin 3) (g : Gate) (ws : List Share3) (c : GateCoin) : GateCoin :=
  match g with
  | .mul l r => (c.1, c.2.1, zkBooMulShare (wire ws l) (wire ws r) (tapeOf e c) (nextParty e))
  | _ => c

def realCoin (e : Fin 3) (g : Gate) (ws : List Share3) (c : GateCoin) : GateCoin :=
  match g with
  | .mul l r =>
    (c.1, c.2.1,
      CommRingOps.sub
        (CommRingOps.add (crossAt (wire ws l) (wire ws r) (nextParty e)) c.2.1) c.2.2)
  | _ => c

private theorem gl_mask_roundtrip (X b c : Goldilocks) :
    CommRingOps.sub (CommRingOps.add X b) (CommRingOps.add X (CommRingOps.sub b c)) = c := by
  have h : CommRingOps.add X b =
      CommRingOps.add (CommRingOps.add X (CommRingOps.sub b c)) c := by
    rw [LawfulCommRing.add_assoc, LawfulCommRing.add_comm (CommRingOps.sub b c) c,
      LawfulCommRing.add_sub_cancel_left]
  rw [h]
  exact gl_sub_add_cancel_left _ _

private theorem gl_mask_roundtrip' (X b z : Goldilocks) :
    CommRingOps.add X (CommRingOps.sub b (CommRingOps.sub (CommRingOps.add X b) z)) = z := by
  have hv : CommRingOps.add z (CommRingOps.sub (CommRingOps.add X b) z) = CommRingOps.add X b :=
    LawfulCommRing.add_sub_cancel_left z _
  generalize CommRingOps.sub (CommRingOps.add X b) z = v at hv ⊢
  rw [LawfulCommRing.sub_eq_add_neg, ← LawfulCommRing.add_assoc, ← hv,
    LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

theorem realCoin_simCoin (e : Fin 3) (g : Gate) (ws : List Share3) (c : GateCoin) :
    realCoin e g ws (simCoin e g ws c) = c := by
  cases g with
  | constant k => rfl
  | add l r => rfl
  | mul l r =>
    obtain ⟨tA, tB, tC⟩ := c
    simp only [realCoin, simCoin, zkBooMulShare_eq_cross, tapeOf_next, tapeOf_next2,
      gl_mask_roundtrip]

theorem simCoin_realCoin (e : Fin 3) (g : Gate) (ws : List Share3) (c : GateCoin) :
    simCoin e g ws (realCoin e g ws c) = c := by
  cases g with
  | constant k => rfl
  | add l r => rfl
  | mul l r =>
    obtain ⟨tA, tB, z⟩ := c
    simp only [realCoin, simCoin, zkBooMulShare_eq_cross, tapeOf_next, tapeOf_next2,
      gl_mask_roundtrip']

/-- The prover's run: one coin triple per gate, wires appended in order. -/
def realRun (e : Fin 3) : List Gate → List Share3 → List GateCoin → List Share3
  | g :: gs, ws, c :: cs => realRun e gs (ws ++ [realGate g (tapeOf e c) ws]) cs
  | _, ws, _ => ws

def toSim (e : Fin 3) : List Gate → List Share3 → List GateCoin → List GateCoin
  | g :: gs, ws, c :: cs =>
    simCoin e g ws c :: toSim e gs (ws ++ [realGate g (tapeOf e c) ws]) cs
  | _, _, cs => cs

def toReal (e : Fin 3) : List Gate → List Share3 → List GateCoin → List GateCoin
  | g :: gs, ws, c :: cs =>
    realCoin e g ws c ::
      toReal e gs (ws ++ [realGate g (tapeOf e (realCoin e g ws c)) ws]) cs
  | _, _, cs => cs

theorem toReal_toSim (e : Fin 3) : ∀ (gates : List Gate) (ws : List Share3)
    (cs : List GateCoin), toReal e gates ws (toSim e gates ws cs) = cs := by
  intro gates
  induction gates with
  | nil => intro ws cs; rfl
  | cons g gs ih =>
    intro ws cs
    cases cs with
    | nil => rfl
    | cons c cs =>
      show realCoin e g ws (simCoin e g ws c) ::
          toReal e gs (ws ++ [realGate g (tapeOf e (realCoin e g ws (simCoin e g ws c))) ws])
            (toSim e gs (ws ++ [realGate g (tapeOf e c) ws]) cs) = c :: cs
      rw [realCoin_simCoin, ih]

theorem toSim_toReal (e : Fin 3) : ∀ (gates : List Gate) (ws : List Share3)
    (cs : List GateCoin), toSim e gates ws (toReal e gates ws cs) = cs := by
  intro gates
  induction gates with
  | nil => intro ws cs; rfl
  | cons g gs ih =>
    intro ws cs
    cases cs with
    | nil => rfl
    | cons c cs =>
      show simCoin e g ws (realCoin e g ws c) ::
          toSim e gs (ws ++ [realGate g (tapeOf e (realCoin e g ws c)) ws])
            (toReal e gs (ws ++ [realGate g (tapeOf e (realCoin e g ws c)) ws]) cs) = c :: cs
      rw [simCoin_realCoin, ih]

theorem toSim_length (e : Fin 3) : ∀ (gates : List Gate) (ws : List Share3)
    (cs : List GateCoin), (toSim e gates ws cs).length = cs.length := by
  intro gates
  induction gates with
  | nil => intro ws cs; rfl
  | cons g gs ih =>
    intro ws cs
    cases cs with
    | nil => rfl
    | cons c cs =>
      show (simCoin e g ws c :: toSim e gs (ws ++ [realGate g (tapeOf e c) ws]) cs).length =
        (c :: cs).length
      rw [List.length_cons, List.length_cons, ih]

theorem toReal_length (e : Fin 3) : ∀ (gates : List Gate) (ws : List Share3)
    (cs : List GateCoin), (toReal e gates ws cs).length = cs.length := by
  intro gates
  induction gates with
  | nil => intro ws cs; rfl
  | cons g gs ih =>
    intro ws cs
    cases cs with
    | nil => rfl
    | cons c cs =>
      show (realCoin e g ws c ::
          toReal e gs (ws ++ [realGate g (tapeOf e (realCoin e g ws c)) ws]) cs).length =
        (c :: cs).length
      rw [List.length_cons, List.length_cons, ih]

def tapePair (c : GateCoin) : OpenPair := (c.1, c.2.1)

theorem toSim_tapePairs (e : Fin 3) : ∀ (gates : List Gate) (ws : List Share3)
    (cs : List GateCoin), (toSim e gates ws cs).map tapePair = cs.map tapePair := by
  intro gates
  induction gates with
  | nil => intro ws cs; rfl
  | cons g gs ih =>
    intro ws cs
    cases cs with
    | nil => rfl
    | cons c cs =>
      have hc : tapePair (simCoin e g ws c) = tapePair c := by cases g <;> rfl
      show tapePair (simCoin e g ws c) ::
          (toSim e gs (ws ++ [realGate g (tapeOf e c) ws]) cs).map tapePair =
        tapePair c :: cs.map tapePair
      rw [hc, ih]

def openPair (e : Fin 3) (w : Share3) : OpenPair := (w e, w (nextParty e))

def pairWire (ps : List OpenPair) (i : Nat) : OpenPair :=
  ps.getD i (CommRingOps.zero, CommRingOps.zero)

def crossPair (x y : OpenPair) : Goldilocks :=
  CommRingOps.add (CommRingOps.mul x.1 y.1)
    (CommRingOps.add (CommRingOps.mul x.1 y.2) (CommRingOps.mul x.2 y.1))

/-- The simulator's gate step: it sees only the two opened parties. At a
    multiplication the neighbour's output is the fresh coin `c.2.2`. -/
def simGate (e : Fin 3) (g : Gate) (c : GateCoin) (ps : List OpenPair) : OpenPair :=
  match g with
  | .constant k =>
    (if e.val = 0 then k else CommRingOps.zero,
     if (nextParty e).val = 0 then k else CommRingOps.zero)
  | .add l r =>
    (CommRingOps.add (pairWire ps l).1 (pairWire ps r).1,
     CommRingOps.add (pairWire ps l).2 (pairWire ps r).2)
  | .mul l r =>
    (CommRingOps.add (crossPair (pairWire ps l) (pairWire ps r)) (CommRingOps.sub c.1 c.2.1),
     c.2.2)

def simRun (e : Fin 3) : List Gate → List OpenPair → List GateCoin → List OpenPair
  | g :: gs, ps, c :: cs => simRun e gs (ps ++ [simGate e g c ps]) cs
  | _, ps, _ => ps

theorem pairWire_map (e : Fin 3) : ∀ (ws : List Share3) (i : Nat),
    pairWire (ws.map (openPair e)) i = openPair e (wire ws i)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: ws, i + 1 => pairWire_map e ws i

theorem openPair_realGate (e : Fin 3) (g : Gate) (ws : List Share3) (c : GateCoin) :
    openPair e (realGate g (tapeOf e c) ws) =
      simGate e g (simCoin e g ws c) (ws.map (openPair e)) := by
  cases g with
  | constant k => rfl
  | add l r =>
    show (CommRingOps.add (wire ws l e) (wire ws r e),
        CommRingOps.add (wire ws l (nextParty e)) (wire ws r (nextParty e))) =
      (CommRingOps.add (pairWire (ws.map (openPair e)) l).1 (pairWire (ws.map (openPair e)) r).1,
       CommRingOps.add (pairWire (ws.map (openPair e)) l).2 (pairWire (ws.map (openPair e)) r).2)
    rw [pairWire_map, pairWire_map]
    rfl
  | mul l r =>
    show (zkBooMulShare (wire ws l) (wire ws r) (tapeOf e c) e,
        zkBooMulShare (wire ws l) (wire ws r) (tapeOf e c) (nextParty e)) =
      (CommRingOps.add (crossPair (pairWire (ws.map (openPair e)) l)
          (pairWire (ws.map (openPair e)) r)) (CommRingOps.sub c.1 c.2.1),
       zkBooMulShare (wire ws l) (wire ws r) (tapeOf e c) (nextParty e))
    rw [pairWire_map, pairWire_map,
      zkBooMulShare_eq_cross (wire ws l) (wire ws r) (tapeOf e c) e, tapeOf_self, tapeOf_next]
    rfl

theorem realRun_openPairs (e : Fin 3) : ∀ (gates : List Gate) (ws : List Share3)
    (cs : List GateCoin),
    (realRun e gates ws cs).map (openPair e) =
      simRun e gates (ws.map (openPair e)) (toSim e gates ws cs) := by
  intro gates
  induction gates with
  | nil => intro ws cs; rfl
  | cons g gs ih =>
    intro ws cs
    cases cs with
    | nil => rfl
    | cons c cs =>
      show (realRun e gs (ws ++ [realGate g (tapeOf e c) ws]) cs).map (openPair e) =
        simRun e gs (ws.map (openPair e) ++
            [simGate e g (simCoin e g ws c) (ws.map (openPair e))])
          (toSim e gs (ws ++ [realGate g (tapeOf e c) ws]) cs)
      rw [ih, List.map_append, List.map_cons, List.map_nil, openPair_realGate]

def plainGate (g : Gate) (xs : List Goldilocks) : Goldilocks :=
  match g with
  | .constant c => c
  | .add l r => CommRingOps.add (xs.getD l CommRingOps.zero) (xs.getD r CommRingOps.zero)
  | .mul l r => CommRingOps.mul (xs.getD l CommRingOps.zero) (xs.getD r CommRingOps.zero)

/-- The circuit on plain values. -/
def plainRun : List Gate → List Goldilocks → List Goldilocks
  | [], xs => xs
  | g :: gs, xs => plainRun gs (xs ++ [plainGate g xs])

theorem sumShares3_wire : ∀ (ws : List Share3) (i : Nat),
    sumShares3 (wire ws i) = (ws.map sumShares3).getD i CommRingOps.zero
  | [], _ => by
    show CommRingOps.add (CommRingOps.zero : Goldilocks)
      (CommRingOps.add CommRingOps.zero CommRingOps.zero) = CommRingOps.zero
    rw [LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  | _ :: _, 0 => rfl
  | _ :: ws, i + 1 => sumShares3_wire ws i

theorem sumShares3_realGate (g : Gate) (tape : Share3) (ws : List Share3) :
    sumShares3 (realGate g tape ws) = plainGate g (ws.map sumShares3) := by
  cases g with
  | constant k =>
    show CommRingOps.add k (CommRingOps.add CommRingOps.zero CommRingOps.zero) = k
    rw [LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  | add l r =>
    exact (sumShares3_add (wire ws l) (wire ws r)).trans
      (by rw [sumShares3_wire, sumShares3_wire]; rfl)
  | mul l r =>
    show sumShares3 (zkBooMulShare (wire ws l) (wire ws r) tape) = _
    rw [zkBooMulShare_sum, sumShares3_wire, sumShares3_wire]
    rfl

/-- Reconstruction of every wire equals the plain circuit, for any coins. -/
theorem realRun_sum (e : Fin 3) : ∀ (gates : List Gate) (ws : List Share3)
    (cs : List GateCoin), gates.length ≤ cs.length →
    (realRun e gates ws cs).map sumShares3 = plainRun gates (ws.map sumShares3) := by
  intro gates
  induction gates with
  | nil => intro ws cs _; rfl
  | cons g gs ih =>
    intro ws cs h
    cases cs with
    | nil => exact absurd h (Nat.not_succ_le_zero _)
    | cons c cs =>
      show (realRun e gs (ws ++ [realGate g (tapeOf e c) ws]) cs).map sumShares3 =
        plainRun gs (ws.map sumShares3 ++ [plainGate g (ws.map sumShares3)])
      rw [ih _ _ (Nat.le_of_succ_le_succ h), List.map_append, List.map_cons, List.map_nil,
        sumShares3_realGate]

/-- What the verifier receives for one repetition with challenge `e`: all wires
    of the two opened parties, their tapes, and the third output shares. -/
def realView (e : Fin 3) (gates : List Gate) (outs : List Nat) (ins : List Share3)
    (coins : List GateCoin) : List OpenPair × List OpenPair × List Goldilocks :=
  ((realRun e gates ins coins).map (openPair e),
   coins.map tapePair,
   outs.map (fun o => wire (realRun e gates ins coins) o (nextParty (nextParty e))))

/-- The values of the designated output wires: the statement's public part. -/
def publicOutputs (gates : List Gate) (outs : List Nat) (xs : List Goldilocks) :
    List Goldilocks :=
  outs.map (fun o => (plainRun gates xs).getD o CommRingOps.zero)

def thirdShares (ps : List OpenPair) : List Nat → List Goldilocks → List Goldilocks
  | o :: os, y :: ys =>
    CommRingOps.sub (CommRingOps.sub y (pairWire ps o).1) (pairWire ps o).2 ::
      thirdShares ps os ys
  | _, _ => []

/-- The simulator: opened input shares, public outputs and coins only. -/
def simView (e : Fin 3) (gates : List Gate) (outs : List Nat) (inPairs : List OpenPair)
    (ys : List Goldilocks) (simCoins : List GateCoin) :
    List OpenPair × List OpenPair × List Goldilocks :=
  (simRun e gates inPairs simCoins,
   simCoins.map tapePair,
   thirdShares (simRun e gates inPairs simCoins) outs ys)

private theorem third_share_eq (w : Share3) : ∀ e : Fin 3,
    CommRingOps.sub (CommRingOps.sub (sumShares3 w) (w e)) (w (nextParty e)) =
      w (nextParty (nextParty e)) := by
  apply three_parties
  · show CommRingOps.sub (CommRingOps.sub
        (CommRingOps.add (w 0) (CommRingOps.add (w 1) (w 2))) (w 0)) (w 1) = w 2
    rw [show CommRingOps.sub (CommRingOps.add (w 0) (CommRingOps.add (w 1) (w 2))) (w 0) =
        CommRingOps.add (w 1) (w 2) from gl_sub_add_cancel_left _ _]
    exact gl_sub_add_cancel_left _ _
  · show CommRingOps.sub (CommRingOps.sub
        (CommRingOps.add (w 0) (CommRingOps.add (w 1) (w 2))) (w 1)) (w 2) = w 0
    rw [gl_add_left_comm (w 0) (w 1) (w 2), LawfulCommRing.add_comm (w 0) (w 2),
      show CommRingOps.sub (CommRingOps.add (w 1) (CommRingOps.add (w 2) (w 0))) (w 1) =
        CommRingOps.add (w 2) (w 0) from gl_sub_add_cancel_left _ _]
    exact gl_sub_add_cancel_left _ _
  · show CommRingOps.sub (CommRingOps.sub
        (CommRingOps.add (w 0) (CommRingOps.add (w 1) (w 2))) (w 2)) (w 0) = w 1
    rw [LawfulCommRing.add_comm (w 1) (w 2), gl_add_left_comm (w 0) (w 2) (w 1),
      show CommRingOps.sub (CommRingOps.add (w 2) (CommRingOps.add (w 0) (w 1))) (w 2) =
        CommRingOps.add (w 0) (w 1) from gl_sub_add_cancel_left _ _]
    exact gl_sub_add_cancel_left _ _

theorem thirdShares_real (e : Fin 3) (ws : List Share3) : ∀ outs : List Nat,
    outs.map (fun o => wire ws o (nextParty (nextParty e))) =
      thirdShares (ws.map (openPair e)) outs
        (outs.map (fun o => (ws.map sumShares3).getD o CommRingOps.zero)) := by
  intro outs
  induction outs with
  | nil => rfl
  | cons o os ih =>
    show wire ws o (nextParty (nextParty e)) ::
        os.map (fun o => wire ws o (nextParty (nextParty e))) =
      CommRingOps.sub (CommRingOps.sub ((ws.map sumShares3).getD o CommRingOps.zero)
          (pairWire (ws.map (openPair e)) o).1) (pairWire (ws.map (openPair e)) o).2 ::
        thirdShares (ws.map (openPair e)) os
          (os.map (fun o => (ws.map sumShares3).getD o CommRingOps.zero))
    rw [← ih, pairWire_map, ← sumShares3_wire]
    show _ = CommRingOps.sub (CommRingOps.sub (sumShares3 (wire ws o)) (wire ws o e))
        (wire ws o (nextParty e)) :: _
    rw [third_share_eq]

/-- **Perfect simulation of the opened view.** The real view equals the
    simulator's output on the translated coins, and the simulator reads the
    witness only through the opened input shares and the public outputs. -/
theorem opened_view_perfectly_simulated (e : Fin 3) (gates : List Gate) (outs : List Nat)
    (ins : List Share3) (coins : List GateCoin) (hLen : gates.length ≤ coins.length) :
    realView e gates outs ins coins =
      simView e gates outs (ins.map (openPair e))
        (publicOutputs gates outs (ins.map sumShares3)) (toSim e gates ins coins) := by
  have h1 := realRun_openPairs e gates ins coins
  have h2 := toSim_tapePairs e gates ins coins
  have h3 := thirdShares_real e (realRun e gates ins coins) outs
  rw [realRun_sum e gates ins coins hLen] at h3
  unfold realView simView publicOutputs
  rw [← h1, h2, ← h3]

/-- Coin translation between two input sharings; a bijection with no side
    condition, preserving the number of coins. -/
def viewCoinBijection (e : Fin 3) (gates : List Gate) (ins ins' : List Share3) :
    CredBijection (List GateCoin) (List GateCoin) where
  toFun cs := toReal e gates ins' (toSim e gates ins cs)
  invFun cs := toReal e gates ins (toSim e gates ins' cs)
  left_inv cs := by
    show toReal e gates ins (toSim e gates ins' (toReal e gates ins' (toSim e gates ins cs))) = cs
    rw [toSim_toReal, toReal_toSim]
  right_inv cs := by
    show toReal e gates ins' (toSim e gates ins (toReal e gates ins (toSim e gates ins' cs))) = cs
    rw [toSim_toReal, toReal_toSim]

theorem viewCoinBijection_length (e : Fin 3) (gates : List Gate) (ins ins' : List Share3)
    (cs : List GateCoin) : ((viewCoinBijection e gates ins ins').toFun cs).length = cs.length := by
  show (toReal e gates ins' (toSim e gates ins cs)).length = cs.length
  rw [toReal_length, toSim_length]

/-- Two sharings with the same opened input shares and the same public outputs
    give the same view once coins are translated: the views are identically
    distributed for uniform coins. -/
theorem opened_views_coincide_given_equal_leakage (e : Fin 3) (gates : List Gate)
    (outs : List Nat) (ins ins' : List Share3) (coins : List GateCoin)
    (hOpen : ins.map (openPair e) = ins'.map (openPair e))
    (hLeak : publicOutputs gates outs (ins.map sumShares3) =
      publicOutputs gates outs (ins'.map sumShares3))
    (hLen : gates.length ≤ coins.length) :
    realView e gates outs ins coins =
      realView e gates outs ins' ((viewCoinBijection e gates ins ins').toFun coins) := by
  have hLen' : gates.length ≤ ((viewCoinBijection e gates ins ins').toFun coins).length := by
    rw [viewCoinBijection_length]
    exact hLen
  rw [opened_view_perfectly_simulated e gates outs ins coins hLen,
    opened_view_perfectly_simulated e gates outs ins' _ hLen', hOpen, hLeak]
  show _ = simView e gates outs (ins'.map (openPair e))
    (publicOutputs gates outs (ins'.map sumShares3))
    (toSim e gates ins' (toReal e gates ins' (toSim e gates ins coins)))
  rw [toSim_toReal]

/-- Additive sharing of each witness value from two coins per input. -/
def shareInputs : List Goldilocks → List (Goldilocks × Goldilocks) → List Share3
  | x :: xs, r :: rs => credShareWire3 x r.1 r.2 :: shareInputs xs rs
  | _, _ => []

/-- Input-coin translation from witness `xs` to witness `xs'`. -/
def recoin (e : Fin 3) :
    List Goldilocks → List Goldilocks → List (Goldilocks × Goldilocks) →
      List (Goldilocks × Goldilocks)
  | x :: xs, x' :: xs', r :: rs =>
    (credSharePairBijection e x').invFun ((credSharePairBijection e x).toFun r) ::
      recoin e xs xs' rs
  | _, _, rs => rs

theorem recoin_recoin (e : Fin 3) : ∀ (xs xs' : List Goldilocks)
    (rs : List (Goldilocks × Goldilocks)), recoin e xs' xs (recoin e xs xs' rs) = rs := by
  intro xs
  induction xs with
  | nil => intro xs' rs; cases xs' <;> rfl
  | cons x xs ih =>
    intro xs' rs
    cases xs' with
    | nil => rfl
    | cons x' xs' =>
      cases rs with
      | nil => rfl
      | cons r rs =>
        show (credSharePairBijection e x).invFun ((credSharePairBijection e x').toFun
            ((credSharePairBijection e x').invFun ((credSharePairBijection e x).toFun r))) ::
          recoin e xs' xs (recoin e xs xs' rs) = r :: rs
        rw [(credSharePairBijection e x').right_inv, (credSharePairBijection e x).left_inv, ih]

theorem recoin_length (e : Fin 3) : ∀ (xs xs' : List Goldilocks)
    (rs : List (Goldilocks × Goldilocks)), (recoin e xs xs' rs).length = rs.length := by
  intro xs
  induction xs with
  | nil => intro xs' rs; rfl
  | cons x xs ih =>
    intro xs' rs
    cases xs' with
    | nil => rfl
    | cons x' xs' =>
      cases rs with
      | nil => rfl
      | cons r rs =>
        show (_ :: recoin e xs xs' rs).length = (r :: rs).length
        rw [List.length_cons, List.length_cons, ih]

def inputCoinBijection (e : Fin 3) (xs xs' : List Goldilocks) :
    CredBijection (List (Goldilocks × Goldilocks)) (List (Goldilocks × Goldilocks)) where
  toFun := recoin e xs xs'
  invFun := recoin e xs' xs
  left_inv := recoin_recoin e xs xs'
  right_inv := recoin_recoin e xs' xs

theorem shareInputs_sum : ∀ (xs : List Goldilocks) (rs : List (Goldilocks × Goldilocks)),
    rs.length = xs.length → (shareInputs xs rs).map sumShares3 = xs := by
  intro xs
  induction xs with
  | nil => intro rs _; rfl
  | cons x xs ih =>
    intro rs h
    cases rs with
    | nil => exact absurd h.symm (Nat.succ_ne_zero _)
    | cons r rs =>
      show sumShares3 (credShareWire3 x r.1 r.2) :: (shareInputs xs rs).map sumShares3 = x :: xs
      rw [credShareWire3_sum, ih rs (Nat.succ.inj h)]

theorem shareInputs_open (e : Fin 3) : ∀ (xs xs' : List Goldilocks)
    (rs : List (Goldilocks × Goldilocks)), xs.length = xs'.length → rs.length = xs.length →
    (shareInputs xs rs).map (openPair e) =
      (shareInputs xs' (recoin e xs xs' rs)).map (openPair e) := by
  intro xs
  induction xs with
  | nil =>
    intro xs' rs hx _
    cases xs' with
    | nil => rfl
    | cons _ _ => exact absurd hx.symm (Nat.succ_ne_zero _)
  | cons x xs ih =>
    intro xs' rs hx hr
    cases xs' with
    | nil => exact absurd hx (Nat.succ_ne_zero _)
    | cons x' xs' =>
      cases rs with
      | nil => exact absurd hr.symm (Nat.succ_ne_zero _)
      | cons r rs =>
        show (credSharePairBijection e x).toFun r :: (shareInputs xs rs).map (openPair e) =
          (credSharePairBijection e x').toFun
              ((credSharePairBijection e x').invFun ((credSharePairBijection e x).toFun r)) ::
            (shareInputs xs' (recoin e xs xs' rs)).map (openPair e)
        rw [(credSharePairBijection e x').right_inv,
          ih xs' rs (Nat.succ.inj hx) (Nat.succ.inj hr)]

/-- **One repetition's view hides the witness given the public outputs.** For
    two witnesses with equal public outputs, translating the input coins and
    then the gate coins by explicit bijections turns one prover's opened view
    into the other's. With uniform coins the two views are identically
    distributed; nothing but the public outputs can link them. -/
theorem presentation_view_depends_only_on_public_outputs
    (e : Fin 3) (gates : List Gate) (outs : List Nat) (xs xs' : List Goldilocks)
    (hLenX : xs.length = xs'.length)
    (hLeak : publicOutputs gates outs xs = publicOutputs gates outs xs')
    (rs : List (Goldilocks × Goldilocks)) (cs : List GateCoin)
    (hRs : rs.length = xs.length) (hCs : gates.length ≤ cs.length) :
    realView e gates outs (shareInputs xs rs) cs =
      realView e gates outs
        (shareInputs xs' ((inputCoinBijection e xs xs').toFun rs))
        ((viewCoinBijection e gates (shareInputs xs rs)
          (shareInputs xs' ((inputCoinBijection e xs xs').toFun rs))).toFun cs) := by
  have hRs' : (recoin e xs xs' rs).length = xs'.length := by
    rw [recoin_length, hRs, hLenX]
  apply opened_views_coincide_given_equal_leakage e gates outs _ _ cs
  · exact shareInputs_open e xs xs' rs hLenX hRs
  · show publicOutputs gates outs ((shareInputs xs rs).map sumShares3) =
      publicOutputs gates outs ((shareInputs xs' (recoin e xs xs' rs)).map sumShares3)
    rw [shareInputs_sum xs rs hRs, shareInputs_sum xs' _ hRs', hLeak]
  · exact hCs

/-- Outputs recomputed from a view alone. -/
def reconOutputs (ps : List OpenPair) : List Nat → List Goldilocks → List Goldilocks
  | o :: os, t :: ts =>
    CommRingOps.add (CommRingOps.add (pairWire ps o).1 (pairWire ps o).2) t ::
      reconOutputs ps os ts
  | _, _ => []

private theorem sum_by_role (w : Share3) : ∀ e : Fin 3,
    CommRingOps.add (CommRingOps.add (w e) (w (nextParty e))) (w (nextParty (nextParty e))) =
      sumShares3 w := by
  apply three_parties
  · show CommRingOps.add (CommRingOps.add (w 0) (w 1)) (w 2) =
      CommRingOps.add (w 0) (CommRingOps.add (w 1) (w 2))
    rw [LawfulCommRing.add_assoc]
  · show CommRingOps.add (CommRingOps.add (w 1) (w 2)) (w 0) =
      CommRingOps.add (w 0) (CommRingOps.add (w 1) (w 2))
    rw [LawfulCommRing.add_comm]
  · show CommRingOps.add (CommRingOps.add (w 2) (w 0)) (w 1) =
      CommRingOps.add (w 0) (CommRingOps.add (w 1) (w 2))
    rw [LawfulCommRing.add_comm (w 2) (w 0), LawfulCommRing.add_assoc,
      LawfulCommRing.add_comm (w 2) (w 1)]

theorem reconOutputs_real (e : Fin 3) (ws : List Share3) : ∀ outs : List Nat,
    reconOutputs (ws.map (openPair e)) outs
        (outs.map (fun o => wire ws o (nextParty (nextParty e)))) =
      outs.map (fun o => (ws.map sumShares3).getD o CommRingOps.zero) := by
  intro outs
  induction outs with
  | nil => rfl
  | cons o os ih =>
    show CommRingOps.add (CommRingOps.add (pairWire (ws.map (openPair e)) o).1
          (pairWire (ws.map (openPair e)) o).2) (wire ws o (nextParty (nextParty e))) ::
        reconOutputs (ws.map (openPair e)) os
          (os.map (fun o => wire ws o (nextParty (nextParty e)))) =
      (ws.map sumShares3).getD o CommRingOps.zero ::
        os.map (fun o => (ws.map sumShares3).getD o CommRingOps.zero)
    rw [ih, pairWire_map, ← sumShares3_wire]
    show CommRingOps.add (CommRingOps.add (wire ws o e) (wire ws o (nextParty e)))
        (wire ws o (nextParty (nextParty e))) :: _ = _
    rw [sum_by_role]

/-- The public outputs are leakage: two presentations whose public outputs
    differ (a stable scope tag against a different holder's tag) are told apart
    on every pair of coin choices. -/
theorem tooth_distinct_public_outputs_distinguish (e : Fin 3) (gates : List Gate)
    (outs : List Nat) (ins ins' : List Share3) (cs cs' : List GateCoin)
    (hCs : gates.length ≤ cs.length) (hCs' : gates.length ≤ cs'.length)
    (hNe : publicOutputs gates outs (ins.map sumShares3) ≠
      publicOutputs gates outs (ins'.map sumShares3)) :
    realView e gates outs ins cs ≠ realView e gates outs ins' cs' := by
  intro hEq
  apply hNe
  have hR := congrArg (fun v : List OpenPair × List OpenPair × List Goldilocks =>
    reconOutputs v.1 outs v.2.2) hEq
  have hL := reconOutputs_real e (realRun e gates ins cs) outs
  have hL' := reconOutputs_real e (realRun e gates ins' cs') outs
  rw [realRun_sum e gates ins cs hCs] at hL
  rw [realRun_sum e gates ins' cs' hCs'] at hL'
  exact hL.symm.trans (hR.trans hL')

#tooth_pair Qsag.PresentationView.presentation_view_depends_only_on_public_outputs vs
  Qsag.PresentationView.tooth_distinct_public_outputs_distinguish

/-- The mutant in which every gate reuses one tape entry. -/
def realRunAliased (e : Fin 3) (c : GateCoin) : List Gate → List Share3 → List Share3
  | [], ws => ws
  | g :: gs, ws => realRunAliased e c gs (ws ++ [realGate g (tapeOf e c) ws])

/-- Mask indices must be distinct. With one tape entry shared by two
    multiplications, two sharings with identical opened inputs (and no outputs
    at all) have opened wires that differ for every choice of coins: the
    difference of the neighbour's two gate outputs exposes the hidden share. -/
theorem tooth_aliased_mask_index_leaks_hidden_share :
    ∃ (gates : List Gate) (ins ins' : List Share3),
      ins.map (openPair 0) = ins'.map (openPair 0) ∧
      ∀ c c' : GateCoin,
        (realRunAliased 0 c gates ins).map (openPair 0) ≠
          (realRunAliased 0 c' gates ins').map (openPair 0) := by
  let u : Share3 := fun p => if p.val = 1 then CommRingOps.one else CommRingOps.zero
  let v' : Share3 := fun p => if p.val = 2 then CommRingOps.one else CommRingOps.zero
  refine ⟨[.mul 0 1, .mul 2 2], [u, zeroShare, zeroShare], [u, v', zeroShare], rfl, ?_⟩
  intro c c' h
  have h3 := congrArg (fun l : List OpenPair =>
    (l.getD 3 (CommRingOps.zero, CommRingOps.zero)).2) h
  have h4 := congrArg (fun l : List OpenPair =>
    (l.getD 4 (CommRingOps.zero, CommRingOps.zero)).2) h
  change CommRingOps.add (crossAt u zeroShare 1) (CommRingOps.sub c.2.1 c.2.2) =
    CommRingOps.add (crossAt u v' 1) (CommRingOps.sub c'.2.1 c'.2.2) at h3
  change CommRingOps.add (crossAt zeroShare zeroShare 1) (CommRingOps.sub c.2.1 c.2.2) =
    CommRingOps.add (crossAt zeroShare zeroShare 1) (CommRingOps.sub c'.2.1 c'.2.2) at h4
  have hm := LawfulCommRing.add_left_cancel h4
  rw [hm, LawfulCommRing.add_comm (crossAt u zeroShare 1),
    LawfulCommRing.add_comm (crossAt u v' 1)] at h3
  have hx := LawfulCommRing.add_left_cancel h3
  change CommRingOps.add (CommRingOps.mul (CommRingOps.one : Goldilocks) CommRingOps.zero)
      (CommRingOps.add (CommRingOps.mul CommRingOps.one CommRingOps.zero)
        (CommRingOps.mul CommRingOps.zero CommRingOps.zero)) =
    CommRingOps.add (CommRingOps.mul (CommRingOps.one : Goldilocks) CommRingOps.zero)
      (CommRingOps.add (CommRingOps.mul CommRingOps.one CommRingOps.one)
        (CommRingOps.mul CommRingOps.zero CommRingOps.zero)) at hx
  rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.mul_one,
    LawfulCommRing.add_zero, LawfulCommRing.add_zero, LawfulCommRing.add_zero,
    LawfulCommRing.zero_add] at hx
  have hv := congrArg Goldilocks.val hx
  change (0 : Nat) = 1 at hv
  omega

#tooth_pair Qsag.PresentationView.opened_view_perfectly_simulated vs
  Qsag.PresentationView.tooth_aliased_mask_index_leaks_hidden_share


/-- Joint input and gate coins. Gate translation depends on the input coins;
this dependence is retained in the inverse, rather than treating marginals as independent. -/
abbrev JointCoins := List (Goldilocks × Goldilocks) × List GateCoin

def jointCoinBijection (e : Fin 3) (gates : List Gate) (xs ys : List Goldilocks) :
    CredBijection JointCoins JointCoins where
  toFun c :=
    let r := (inputCoinBijection e xs ys).toFun c.1
    (r, (viewCoinBijection e gates (shareInputs xs c.1) (shareInputs ys r)).toFun c.2)
  invFun c :=
    let r := (inputCoinBijection e xs ys).invFun c.1
    (r, (viewCoinBijection e gates (shareInputs xs r) (shareInputs ys c.1)).invFun c.2)
  left_inv c := by
    rcases c with ⟨r, t⟩
    dsimp only
    rw [(inputCoinBijection e xs ys).left_inv,
      (viewCoinBijection e gates _ _).left_inv]
  right_inv c := by
    rcases c with ⟨r, t⟩
    dsimp only
    rw [(inputCoinBijection e xs ys).right_inv,
      (viewCoinBijection e gates _ _).right_inv]

/-- Any number of independently coined repetitions, with a separate challenge
at each position. This is the fixed-challenge hybrid, not a claim that hashing
commitments gives an independent challenge. -/
def repeatedCoinBijection {n : Nat} (es : Fin n → Fin 3)
    (gates : List Gate) (xs ys : List Goldilocks) :
    CredBijection (Fin n → JointCoins) (Fin n → JointCoins) where
  toFun c i := (jointCoinBijection (es i) gates xs ys).toFun (c i)
  invFun c i := (jointCoinBijection (es i) gates xs ys).invFun (c i)
  left_inv c := by funext i; exact (jointCoinBijection (es i) gates xs ys).left_inv (c i)
  right_inv c := by funext i; exact (jointCoinBijection (es i) gates xs ys).right_inv (c i)

def repeatedView {n : Nat} (es : Fin n → Fin 3) (gates : List Gate)
    (outs : List Nat) (xs : List Goldilocks) (c : Fin n → JointCoins) :=
  fun i => realView (es i) gates outs (shareInputs xs (c i).1) (c i).2

theorem repeated_presentation_privacy {n : Nat} (es : Fin n → Fin 3)
    (gates : List Gate) (outs : List Nat) (xs ys : List Goldilocks)
    (hlen : xs.length = ys.length)
    (hpub : publicOutputs gates outs xs = publicOutputs gates outs ys)
    (c : Fin n → JointCoins)
    (hr : ∀ i, (c i).1.length = xs.length)
    (ht : ∀ i, gates.length ≤ (c i).2.length) :
    repeatedView es gates outs xs c =
      repeatedView es gates outs ys ((repeatedCoinBijection es gates xs ys).toFun c) := by
  funext i
  exact presentation_view_depends_only_on_public_outputs (es i) gates outs xs ys
    hlen hpub (c i).1 (c i).2 (hr i) (ht i)

/-- Deterministic postprocessing preserves the joint view equality. For example,
this covers hashing the simulated opened views together; it does not supply
hiding of the unopened commitment or justify an adaptive FS challenge. -/
theorem repeated_privacy_postprocess {n : Nat} {Output : Type}
    (es : Fin n → Fin 3) (gates : List Gate) (outs : List Nat)
    (xs ys : List Goldilocks) (hlen : xs.length = ys.length)
    (hpub : publicOutputs gates outs xs = publicOutputs gates outs ys)
    (c : Fin n → JointCoins) (hr : ∀ i, (c i).1.length = xs.length)
    (ht : ∀ i, gates.length ≤ (c i).2.length)
    (observe : (Fin n → List OpenPair × List OpenPair × List Goldilocks) → Output) :
    observe (repeatedView es gates outs xs c) =
      observe (repeatedView es gates outs ys
        ((repeatedCoinBijection es gates xs ys).toFun c)) :=
  congrArg observe (repeated_presentation_privacy es gates outs xs ys hlen hpub c hr ht)


/-- Fresh-mode output hiding composes with opened-view hiding. The outer
bijection is the explicit output-hiding hypothesis: fresh randomness alone
cannot supply it for an arbitrary commitment function. -/
def freshCoinBijection {R : Type} {n : Nat} (outputCoins : CredBijection R R)
    (es : Fin n → Fin 3) (gates : List Gate) (xs ys : R → List Goldilocks) :
    CredBijection (R × (Fin n → JointCoins)) (R × (Fin n → JointCoins)) where
  toFun c := (outputCoins.toFun c.1,
    (repeatedCoinBijection es gates (xs c.1) (ys (outputCoins.toFun c.1))).toFun c.2)
  invFun c := (outputCoins.invFun c.1,
    (repeatedCoinBijection es gates (xs (outputCoins.invFun c.1)) (ys c.1)).invFun c.2)
  left_inv c := by
    rcases c with ⟨r, t⟩
    dsimp only
    rw [outputCoins.left_inv, (repeatedCoinBijection es gates _ _).left_inv]
  right_inv c := by
    rcases c with ⟨r, t⟩
    dsimp only
    rw [outputCoins.right_inv, (repeatedCoinBijection es gates _ _).right_inv]

/-- The observer receives public outputs together with every opened repetition.
A coupling of the fresh public outputs lifts to this complete hybrid observation. -/
theorem fresh_public_output_unlinkability {R : Type} {n : Nat}
    (outputCoins : CredBijection R R) (es : Fin n → Fin 3)
    (gates : List Gate) (outs : List Nat) (xs ys : R → List Goldilocks)
    (hlen : ∀ r, (xs r).length = (ys (outputCoins.toFun r)).length)
    (hhide : ∀ r, publicOutputs gates outs (xs r) =
      publicOutputs gates outs (ys (outputCoins.toFun r)))
    (c : R × (Fin n → JointCoins))
    (hr : ∀ i, (c.2 i).1.length = (xs c.1).length)
    (ht : ∀ i, gates.length ≤ (c.2 i).2.length) :
    (publicOutputs gates outs (xs c.1), repeatedView es gates outs (xs c.1) c.2) =
      let d := (freshCoinBijection outputCoins es gates xs ys).toFun c
      (publicOutputs gates outs (ys d.1), repeatedView es gates outs (ys d.1) d.2) := by
  apply Prod.ext
  · exact hhide c.1
  · exact repeated_presentation_privacy es gates outs _ _ (hlen c.1) (hhide c.1) c.2 hr ht

/-! ### Adaptive challenges

The repeated-view theorem above fixes the challenges before the coins are drawn. In the
presentation the challenges are a function of the first message, the commitments to all
three party views of every repetition. This section removes the fixed-challenge
restriction for an arbitrary challenge function `chal`, under one stated property of the
commitment: translating the salt moves a commitment from any view to any other
(`hCom`, `hInv`; a one-time-pad commitment has it, and
`tooth_fresh_blinds_do_not_hide_arbitrary_commitments` shows a commitment without it
does not hide). The prover's run is written with party-indexed tapes and does not
mention a challenge. The coin translation reads the challenge off the first message,
translates the two opened parties' coins as before, and moves the unopened party's
salt; the first message is unchanged, so the challenge is too.
-/

/-- A party-indexed tape entry read in the roles of challenge `e`. -/
def roleOf (e : Fin 3) (t : Share3) : GateCoin :=
  (t e, t (nextParty e), t (nextParty (nextParty e)))

private theorem party_cases :
    ∀ e p : Fin 3, p = e ∨ p = nextParty e ∨ p = nextParty (nextParty e) := by decide

theorem tapeOf_roleOf (e : Fin 3) (t : Share3) : tapeOf e (roleOf e t) = t := by
  funext p
  rcases party_cases e p with h | h | h
  · rw [h]; exact tapeOf_self _ _
  · rw [h]; exact tapeOf_next _ _
  · rw [h]; exact tapeOf_next2 _ _

theorem roleOf_tapeOf (e : Fin 3) (c : GateCoin) : roleOf e (tapeOf e c) = c := by
  rcases c with ⟨a, b, d⟩
  simp only [roleOf, tapeOf_self, tapeOf_next, tapeOf_next2]

private theorem map_roleOf_tapeOf (e : Fin 3) (cs : List GateCoin) :
    (cs.map (tapeOf e)).map (roleOf e) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, List.map_cons, roleOf_tapeOf, ih]

private theorem map_tapeOf_roleOf (e : Fin 3) (ts : List Share3) :
    (ts.map (roleOf e)).map (tapeOf e) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [List.map_cons, List.map_cons, tapeOf_roleOf, ih]

/-- The prover's run from party-indexed tapes. No challenge is involved. -/
def partyRun : List Gate → List Share3 → List Share3 → List Share3
  | g :: gs, ws, t :: ts => partyRun gs (ws ++ [realGate g t ws]) ts
  | _, ws, _ => ws

theorem realRun_eq_partyRun (e : Fin 3) : ∀ (gates : List Gate) (ws : List Share3)
    (cs : List GateCoin), realRun e gates ws cs = partyRun gates ws (cs.map (tapeOf e)) := by
  intro gates
  induction gates with
  | nil => intro ws cs; cases cs <;> rfl
  | cons g gs ih =>
    intro ws cs
    cases cs with
    | nil => rfl
    | cons c cs => exact ih _ cs

/-- What a party commits to: its wire shares and its tape. -/
abbrev CommittedView := List Goldilocks × List Goldilocks

def committedView (p : Fin 3) (run tapes : List Share3) : CommittedView :=
  (run.map (fun w => w p), tapes.map (fun t => t p))

/-- Coins of one repetition: input-sharing coins, party-indexed tapes, commitment salts. -/
abbrev RepCoins (S : Type) := List (Goldilocks × Goldilocks) × List Share3 × (Fin 3 → S)

def repCommits {S K : Type} (com : CommittedView → S → K) (gates : List Gate)
    (xs : List Goldilocks) (c : RepCoins S) : Fin 3 → K :=
  fun p => com (committedView p (partyRun gates (shareInputs xs c.1) c.2.1) c.2.1) (c.2.2 p)

/-- The response to challenge `e`: the opened view and the two opened salts. -/
def repOpened {S : Type} (e : Fin 3) (gates : List Gate) (outs : List Nat)
    (xs : List Goldilocks) (c : RepCoins S) :
    (List OpenPair × List OpenPair × List Goldilocks) × S × S :=
  (realView e gates outs (shareInputs xs c.1) (c.2.1.map (roleOf e)), c.2.2 e,
    c.2.2 (nextParty e))

def recoinInputs (e : Fin 3) (xs ys : List Goldilocks) (rs : List (Goldilocks × Goldilocks)) :
    List (Goldilocks × Goldilocks) :=
  (inputCoinBijection e xs ys).toFun rs

def recoinTapes (e : Fin 3) (gates : List Gate) (xs ys : List Goldilocks)
    (rs : List (Goldilocks × Goldilocks)) (ts : List Share3) : List Share3 :=
  ((viewCoinBijection e gates (shareInputs xs rs)
    (shareInputs ys (recoinInputs e xs ys rs))).toFun (ts.map (roleOf e))).map (tapeOf e)

def hiddenView (e : Fin 3) (gates : List Gate) (xs : List Goldilocks)
    (rs : List (Goldilocks × Goldilocks)) (ts : List Share3) : CommittedView :=
  committedView (nextParty (nextParty e)) (partyRun gates (shareInputs xs rs) ts) ts

def recoinSalts {S : Type} (hide : CommittedView → CommittedView → S → S) (e : Fin 3)
    (v v' : CommittedView) (s : Fin 3 → S) : Fin 3 → S :=
  fun p => if p = nextParty (nextParty e) then hide v v' (s p) else s p

/-- Coin translation of one repetition for challenge `e`. -/
def repRecoin {S : Type} (hide : CommittedView → CommittedView → S → S) (e : Fin 3)
    (gates : List Gate) (xs ys : List Goldilocks) (c : RepCoins S) : RepCoins S :=
  (recoinInputs e xs ys c.1, recoinTapes e gates xs ys c.1 c.2.1,
    recoinSalts hide e (hiddenView e gates xs c.1 c.2.1)
      (hiddenView e gates ys (recoinInputs e xs ys c.1) (recoinTapes e gates xs ys c.1 c.2.1))
      c.2.2)

theorem recoinInputs_inv (e : Fin 3) (xs ys : List Goldilocks)
    (rs : List (Goldilocks × Goldilocks)) :
    recoinInputs e ys xs (recoinInputs e xs ys rs) = rs :=
  recoin_recoin e xs ys rs

theorem recoinTapes_inv (e : Fin 3) (gates : List Gate) (xs ys : List Goldilocks)
    (rs : List (Goldilocks × Goldilocks)) (ts : List Share3) :
    recoinTapes e gates ys xs (recoinInputs e xs ys rs) (recoinTapes e gates xs ys rs ts) =
      ts := by
  unfold recoinTapes
  rw [recoinInputs_inv, map_roleOf_tapeOf]
  have h := (viewCoinBijection e gates (shareInputs xs rs)
    (shareInputs ys (recoinInputs e xs ys rs))).left_inv (ts.map (roleOf e))
  have h' : (viewCoinBijection e gates (shareInputs ys (recoinInputs e xs ys rs))
      (shareInputs xs rs)).toFun
      ((viewCoinBijection e gates (shareInputs xs rs)
        (shareInputs ys (recoinInputs e xs ys rs))).toFun (ts.map (roleOf e))) =
      ts.map (roleOf e) := h
  rw [h', map_tapeOf_roleOf]

theorem recoinSalts_inv {S : Type} (hide : CommittedView → CommittedView → S → S)
    (hInv : ∀ v v' s, hide v' v (hide v v' s) = s) (e : Fin 3) (v v' : CommittedView)
    (s : Fin 3 → S) : recoinSalts hide e v' v (recoinSalts hide e v v' s) = s := by
  funext p
  if hp : p = nextParty (nextParty e) then
    simp only [recoinSalts, hp, ↓reduceIte, hInv]
  else
    simp only [recoinSalts, hp, ↓reduceIte]

/-- The translation in the other direction undoes it, for every coin vector. -/
theorem repRecoin_inv {S : Type} (hide : CommittedView → CommittedView → S → S)
    (hInv : ∀ v v' s, hide v' v (hide v v' s) = s) (e : Fin 3) (gates : List Gate)
    (xs ys : List Goldilocks) (c : RepCoins S) :
    repRecoin hide e gates ys xs (repRecoin hide e gates xs ys c) = c := by
  rcases c with ⟨rs, ts, salts⟩
  simp only [repRecoin, hiddenView, recoinInputs_inv, recoinTapes_inv]
  rw [recoinSalts_inv hide hInv]

private theorem repRecoin_view {S : Type} (hide : CommittedView → CommittedView → S → S)
    (e : Fin 3) (gates : List Gate) (outs : List Nat) (xs ys : List Goldilocks)
    (hlen : xs.length = ys.length)
    (hpub : publicOutputs gates outs xs = publicOutputs gates outs ys)
    (c : RepCoins S) (hr : c.1.length = xs.length) (ht : gates.length ≤ c.2.1.length) :
    realView e gates outs (shareInputs xs c.1) (c.2.1.map (roleOf e)) =
      realView e gates outs (shareInputs ys (repRecoin hide e gates xs ys c).1)
        ((repRecoin hide e gates xs ys c).2.1.map (roleOf e)) := by
  have hv := presentation_view_depends_only_on_public_outputs e gates outs xs ys hlen hpub
    c.1 (c.2.1.map (roleOf e)) hr (by rw [List.length_map]; exact ht)
  show _ = realView e gates outs (shareInputs ys (recoinInputs e xs ys c.1))
    ((recoinTapes e gates xs ys c.1 c.2.1).map (roleOf e))
  unfold recoinTapes
  rw [map_roleOf_tapeOf]
  exact hv

/-- The response is unchanged. -/
theorem repRecoin_opened {S : Type} (hide : CommittedView → CommittedView → S → S)
    (e : Fin 3) (gates : List Gate) (outs : List Nat) (xs ys : List Goldilocks)
    (hlen : xs.length = ys.length)
    (hpub : publicOutputs gates outs xs = publicOutputs gates outs ys)
    (c : RepCoins S) (hr : c.1.length = xs.length) (ht : gates.length ≤ c.2.1.length) :
    repOpened e gates outs xs c = repOpened e gates outs ys (repRecoin hide e gates xs ys c) := by
  have hv := repRecoin_view hide e gates outs xs ys hlen hpub c hr ht
  have h1 : (repRecoin hide e gates xs ys c).2.2 e = c.2.2 e := by
    show (if e = nextParty (nextParty e) then _ else c.2.2 e) = c.2.2 e
    rw [ite_eq_right (fun h => nextParty2_ne e h.symm)]
  have h2 : (repRecoin hide e gates xs ys c).2.2 (nextParty e) = c.2.2 (nextParty e) := by
    show (if nextParty e = nextParty (nextParty e) then _ else c.2.2 (nextParty e)) = _
    rw [ite_eq_right (fun h => nextParty2_ne_next e h.symm)]
  unfold repOpened
  rw [← hv, h1, h2]

private theorem committedView_of_opened (e : Fin 3) (runX runY tsX : List Share3)
    (csY : List GateCoin)
    (hRun : runX.map (openPair e) = runY.map (openPair e))
    (hTape : (tsX.map (roleOf e)).map tapePair = csY.map tapePair) :
    committedView e runX tsX = committedView e runY (csY.map (tapeOf e)) ∧
    committedView (nextParty e) runX tsX =
      committedView (nextParty e) runY (csY.map (tapeOf e)) := by
  have hR1 := congrArg (List.map Prod.fst) hRun
  have hR2 := congrArg (List.map Prod.snd) hRun
  have hT1 := congrArg (List.map Prod.fst) hTape
  have hT2 := congrArg (List.map Prod.snd) hTape
  simp only [List.map_map] at hR1 hR2 hT1 hT2
  have hY1 : (csY.map (tapeOf e)).map (fun t => t e) = csY.map (Prod.fst ∘ tapePair) := by
    rw [List.map_map]
    exact List.map_congr_left (fun c _ => tapeOf_self e c)
  have hY2 : (csY.map (tapeOf e)).map (fun t => t (nextParty e)) =
      csY.map (Prod.snd ∘ tapePair) := by
    rw [List.map_map]
    exact List.map_congr_left (fun c _ => tapeOf_next e c)
  refine ⟨Prod.ext hR1 ?_, Prod.ext hR2 ?_⟩
  · show tsX.map (fun t => t e) = (csY.map (tapeOf e)).map (fun t => t e)
    rw [hY1, ← hT1]
    rfl
  · show tsX.map (fun t => t (nextParty e)) =
      (csY.map (tapeOf e)).map (fun t => t (nextParty e))
    rw [hY2, ← hT2]
    rfl

/-- The first message is unchanged: the opened parties commit to the same views with the
same salts, and the unopened party's salt is moved along with its view. -/
theorem repRecoin_commits {S K : Type} (com : CommittedView → S → K)
    (hide : CommittedView → CommittedView → S → S)
    (hCom : ∀ v v' s, com v s = com v' (hide v v' s))
    (e : Fin 3) (gates : List Gate) (outs : List Nat) (xs ys : List Goldilocks)
    (hlen : xs.length = ys.length)
    (hpub : publicOutputs gates outs xs = publicOutputs gates outs ys)
    (c : RepCoins S) (hr : c.1.length = xs.length) (ht : gates.length ≤ c.2.1.length) :
    repCommits com gates ys (repRecoin hide e gates xs ys c) = repCommits com gates xs c := by
  have hv := presentation_view_depends_only_on_public_outputs e gates outs xs ys hlen hpub
    c.1 (c.2.1.map (roleOf e)) hr (by rw [List.length_map]; exact ht)
  have hRun := congrArg Prod.fst hv
  have hTape := congrArg (fun v => v.2.1) hv
  simp only [realView] at hRun hTape
  rw [realRun_eq_partyRun, realRun_eq_partyRun, map_tapeOf_roleOf] at hRun
  obtain ⟨hE, hN⟩ := committedView_of_opened e _ _ c.2.1 _ hRun hTape
  funext p
  rcases party_cases e p with h | h | h
  · rw [h]
    show com (committedView e _ (recoinTapes e gates xs ys c.1 c.2.1))
      (if e = nextParty (nextParty e) then _ else c.2.2 e) = com _ (c.2.2 e)
    rw [ite_eq_right (fun h => nextParty2_ne e h.symm)]
    exact congrArg (fun v => com v (c.2.2 e)) hE.symm
  · rw [h]
    show com (committedView (nextParty e) _ (recoinTapes e gates xs ys c.1 c.2.1))
      (if nextParty e = nextParty (nextParty e) then _ else c.2.2 (nextParty e)) = com _ _
    rw [ite_eq_right (fun h => nextParty2_ne_next e h.symm)]
    exact congrArg (fun v => com v (c.2.2 (nextParty e))) hN.symm
  · rw [h]
    show com (hiddenView e gates ys (recoinInputs e xs ys c.1)
        (recoinTapes e gates xs ys c.1 c.2.1))
      (if nextParty (nextParty e) = nextParty (nextParty e) then
        hide (hiddenView e gates xs c.1 c.2.1)
          (hiddenView e gates ys (recoinInputs e xs ys c.1)
            (recoinTapes e gates xs ys c.1 c.2.1)) (c.2.2 (nextParty (nextParty e)))
        else c.2.2 (nextParty (nextParty e))) =
      com (hiddenView e gates xs c.1 c.2.1) (c.2.2 (nextParty (nextParty e)))
    rw [ite_eq_left rfl]
    exact (hCom _ _ _).symm

/-- Challenges computed from the first message. -/
def fsChallenges {S K : Type} {n : Nat} (com : CommittedView → S → K)
    (chal : (Fin n → Fin 3 → K) → Fin n → Fin 3) (gates : List Gate) (xs : List Goldilocks)
    (c : Fin n → RepCoins S) : Fin n → Fin 3 :=
  chal (fun i => repCommits com gates xs (c i))

/-- Everything the verifier receives: first message, derived challenges, responses. -/
def fsTranscript {S K : Type} {n : Nat} (com : CommittedView → S → K)
    (chal : (Fin n → Fin 3 → K) → Fin n → Fin 3) (gates : List Gate) (outs : List Nat)
    (xs : List Goldilocks) (c : Fin n → RepCoins S) :=
  ((fun i => repCommits com gates xs (c i)), fsChallenges com chal gates xs c,
    fun i => repOpened (fsChallenges com chal gates xs c i) gates outs xs (c i))

def fsRecoin {S K : Type} {n : Nat} (com : CommittedView → S → K)
    (hide : CommittedView → CommittedView → S → S)
    (chal : (Fin n → Fin 3 → K) → Fin n → Fin 3) (gates : List Gate) (xs ys : List Goldilocks)
    (c : Fin n → RepCoins S) : Fin n → RepCoins S :=
  fun i => repRecoin hide (fsChallenges com chal gates xs c i) gates xs ys (c i)

/-- **Presentation privacy with challenges derived from the first message.** For two
witnesses with equal public outputs and any challenge function, `fsRecoin` carries
well-formed coins for one witness to well-formed coins for the other with the same
complete transcript, and the translation in the other direction undoes it. Applied in
both directions this is a bijection of the well-formed coin spaces, so with uniform
coins the two transcripts are identically distributed. -/
theorem adaptive_challenge_presentation_privacy {S K : Type} {n : Nat}
    (com : CommittedView → S → K) (hide : CommittedView → CommittedView → S → S)
    (hCom : ∀ v v' s, com v s = com v' (hide v v' s))
    (hInv : ∀ v v' s, hide v' v (hide v v' s) = s)
    (chal : (Fin n → Fin 3 → K) → Fin n → Fin 3)
    (gates : List Gate) (outs : List Nat) (xs ys : List Goldilocks)
    (hlen : xs.length = ys.length)
    (hpub : publicOutputs gates outs xs = publicOutputs gates outs ys)
    (c : Fin n → RepCoins S)
    (hr : ∀ i, (c i).1.length = xs.length) (ht : ∀ i, gates.length ≤ (c i).2.1.length) :
    fsTranscript com chal gates outs xs c =
        fsTranscript com chal gates outs ys (fsRecoin com hide chal gates xs ys c) ∧
      fsRecoin com hide chal gates ys xs (fsRecoin com hide chal gates xs ys c) = c ∧
      (∀ i, (fsRecoin com hide chal gates xs ys c i).1.length = ys.length) ∧
      (∀ i, gates.length ≤ (fsRecoin com hide chal gates xs ys c i).2.1.length) := by
  have hC : (fun i => repCommits com gates ys (fsRecoin com hide chal gates xs ys c i)) =
      (fun i => repCommits com gates xs (c i)) :=
    funext (fun i => repRecoin_commits com hide hCom _ gates outs xs ys hlen hpub (c i)
      (hr i) (ht i))
  have hE : fsChallenges com chal gates ys (fsRecoin com hide chal gates xs ys c) =
      fsChallenges com chal gates xs c := congrArg chal hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Prod.ext hC.symm (Prod.ext hE.symm (funext (fun i => ?_)))
    show repOpened (fsChallenges com chal gates xs c i) gates outs xs (c i) =
      repOpened (fsChallenges com chal gates ys (fsRecoin com hide chal gates xs ys c) i)
        gates outs ys (fsRecoin com hide chal gates xs ys c i)
    rw [hE]
    exact repRecoin_opened hide _ gates outs xs ys hlen hpub (c i) (hr i) (ht i)
  · funext i
    show repRecoin hide (fsChallenges com chal gates ys (fsRecoin com hide chal gates xs ys c) i)
      gates ys xs (fsRecoin com hide chal gates xs ys c i) = c i
    rw [hE]
    exact repRecoin_inv hide hInv _ gates xs ys (c i)
  · intro i
    show (recoin _ xs ys (c i).1).length = ys.length
    rw [recoin_length, hr i, hlen]
  · intro i
    show gates.length ≤ (List.map (tapeOf _) ((viewCoinBijection _ gates _ _).toFun
      ((c i).2.1.map (roleOf _)))).length
    rw [List.length_map, viewCoinBijection_length, List.length_map]
    exact ht i

private theorem gl_add_sub_cancel (a b : Goldilocks) :
    CommRingOps.sub (CommRingOps.add a b) a = b :=
  LawfulCommRing.add_left_cancel (LawfulCommRing.add_sub_cancel_left a (CommRingOps.add a b))

/-- The commitment property is satisfiable: a one-time pad over the first committed
share. -/
theorem adaptive_challenge_hiding_inhabited :
    ∃ (com : CommittedView → Goldilocks → Goldilocks)
      (hide : CommittedView → CommittedView → Goldilocks → Goldilocks),
      (∀ v v' s, com v s = com v' (hide v v' s)) ∧
      (∀ v v' s, hide v' v (hide v v' s) = s) := by
  refine ⟨fun v s => CommRingOps.add (v.1.headD CommRingOps.zero) s,
    fun v v' s => CommRingOps.sub (CommRingOps.add (v.1.headD CommRingOps.zero) s)
      (v'.1.headD CommRingOps.zero), ?_, ?_⟩
  · intro v v' s
    exact (LawfulCommRing.add_sub_cancel_left _ _).symm
  · intro v v' s
    show CommRingOps.sub (CommRingOps.add (v'.1.headD CommRingOps.zero)
      (CommRingOps.sub (CommRingOps.add (v.1.headD CommRingOps.zero) s)
        (v'.1.headD CommRingOps.zero))) (v.1.headD CommRingOps.zero) = s
    rw [LawfulCommRing.add_sub_cancel_left, gl_add_sub_cancel]

end PresentationView

#tooth_pair Qsag.PresentationView.adaptive_challenge_presentation_privacy vs
  Qsag.PresentationView.tooth_distinct_public_outputs_distinguish

/-- Canonical coefficients are necessary even when the centered residue is zero. -/
theorem tooth_norm_rejects_modulus :
    checkCenteredInfNorm 8380417 1 [8380417] = false := by decide

/-! ## Selective-disclosure presentation: `N = 256` seed tree and hidden-party opening

`prove_selective_disclosure` / `verify_presentation` of `crates/qsag-cred/src/blind_vc.rs` run
`sd_repetitions` (33 at `Quantum128`) repetitions of a `VC_SD_LIMBO_PARTIES = 256` party
MPC-in-the-head check over `GF(p^5)`. Each repetition expands a depth-`VC_SD_GGM_DEPTH = 8`
binary seed tree, commits to every party's leaf, and opens all parties but one by revealing the
eight sibling seeds on the hidden party's path (`extract_ggm_copath`,
`reconstruct_ggm_leaves_256`).

This section models the seed tree and the last (opening) round only. The check values of a
repetition are a table `defect : Fin 256 → GF(p^5)` supplied to the opening check; how the
verifier derives them from the opened parties' tapes, the folding weights and the evaluation
point is not modelled here. The count over all three challenge rounds is in
`Qsag.Protocol.Credentials.RepetitionCutAndChoose`.

Representation: paths and copaths are listed from the root down (Rust lists the copath from
the leaf up), and the PRG takes the heap index of the node it expands (root `1`), which
determines the `(depth, node_idx)` pair that `ggm_expand_children` absorbs. -/

inductive CredentialVec (α : Type) : Nat → Type
  | nil : CredentialVec α 0
  | cons {n : Nat} : α → CredentialVec α n → CredentialVec α (n + 1)
  deriving DecidableEq, Repr

/-- `VC_SD_LIMBO_PARTIES`. -/
def credentialSdParties : Nat := 256
/-- `VC_SD_GGM_DEPTH`. -/
def credentialSdGgmDepth : Nat := 8
/-- `ZkSoundnessProfile::Quantum128.sd_repetitions()`. -/
def credentialSdRepetitions : Nat := 33
/-- `ZkSoundnessProfile::Classical128.sd_repetitions()`. -/
def credentialSdRepetitionsClassical : Nat := 17

theorem credentialSdParties_eq : credentialSdParties = 256 := by rfl
theorem credentialSdGgmDepth_eq : credentialSdGgmDepth = 8 := by rfl
theorem credentialSdRepetitions_eq : credentialSdRepetitions = 33 := by rfl
theorem credentialSdRepetitionsClassical_eq : credentialSdRepetitionsClassical = 17 := by rfl

/-- Coefficients of an element of `GF(p)[T]/(T^5 - 3)`, lowest degree first (`Fp5`). Only
    equality with zero is used below. -/
abbrev CredentialFp5 := Fin 5 → Goldilocks

instance : DecidableEq CredentialFp5 := fun a b =>
  if h : (List.finRange 5).all (fun i => decide (a i = b i)) = true then
    .isTrue (funext (fun i => of_decide_eq_true
      (List.all_eq_true.mp h i (List.mem_finRange i))))
  else .isFalse (fun he => h (by subst he; simp))

/-- `Fp5::ZERO`. -/
def credentialFp5Zero : CredentialFp5 := fun _ => Goldilocks.zero

theorem credentialFp5Zero_apply (i : Fin 5) : credentialFp5Zero i = Goldilocks.zero := by rfl

abbrev CredentialGgmSeed := BitVec 256
/-- Length-doubling expansion of one tree node: heap index and seed to the two child seeds. -/
abbrev CredentialGgmPrg := Nat → CredentialGgmSeed → CredentialGgmSeed × CredentialGgmSeed

/-- Root-to-leaf branch bits of leaf `i` in a depth-`d` tree. -/
def credentialGgmPath : (d : Nat) → Nat → CredentialVec Bool d
  | 0, _ => .nil
  | d + 1, i => .cons (decide (i / 2 ^ d % 2 = 1)) (credentialGgmPath d i)

/-- Leaf seed reached from `seed` at heap index `node` along `path`. -/
def credentialGgmLeaf (prg : CredentialGgmPrg) :
    {d : Nat} → Nat → CredentialGgmSeed → CredentialVec Bool d → CredentialGgmSeed
  | 0, _, seed, .nil => seed
  | _ + 1, node, seed, .cons b path =>
    credentialGgmLeaf prg (2 * node + if b then 1 else 0)
      (if b then (prg node seed).2 else (prg node seed).1) path

/-- Sibling seeds along `path`, root level first. -/
def credentialGgmCopath (prg : CredentialGgmPrg) :
    {d : Nat} → Nat → CredentialGgmSeed → CredentialVec Bool d → CredentialVec CredentialGgmSeed d
  | 0, _, _, .nil => .nil
  | _ + 1, node, seed, .cons b path =>
    .cons (if b then (prg node seed).1 else (prg node seed).2)
      (credentialGgmCopath prg (2 * node + if b then 1 else 0)
        (if b then (prg node seed).2 else (prg node seed).1) path)

/-- Leaf seed at `path` recomputed from the copath of `hidden`; `0` at the hidden leaf itself,
    whose seed the copath does not determine. -/
def credentialGgmRecover (prg : CredentialGgmPrg) :
    {d : Nat} → Nat → CredentialVec Bool d → CredentialVec CredentialGgmSeed d →
      CredentialVec Bool d → CredentialGgmSeed
  | 0, _, .nil, .nil, .nil => 0#256
  | _ + 1, node, .cons h hidden, .cons sibling rest, .cons b path =>
    if b = h then credentialGgmRecover prg (2 * node + if h then 1 else 0) hidden rest path
    else credentialGgmLeaf prg (2 * node + if b then 1 else 0) sibling path

/-- **Copath reconstruction.** From the copath of the hidden leaf the verifier recomputes every
    other leaf seed of the tree, for every PRG and every depth. -/
theorem credentialGgmRecover_exact (prg : CredentialGgmPrg) :
    ∀ {d : Nat} (node : Nat) (seed : CredentialGgmSeed) (hidden path : CredentialVec Bool d),
      credentialGgmRecover prg node hidden (credentialGgmCopath prg node seed hidden) path =
        if path = hidden then 0#256 else credentialGgmLeaf prg node seed path
  | 0, _, _, .nil, .nil => rfl
  | _ + 1, node, seed, .cons h hidden, .cons b path => by
    cases h <;> cases b <;>
      simp [credentialGgmRecover, credentialGgmCopath, credentialGgmLeaf, credentialGgmRecover_exact]

/-- The opening of one repetition (`OpenedLimboRepetition`: `hidden_party`, `ggm_copath`,
    `com_1_hidden`). -/
structure CredentialGgmOpening where
  hidden : Fin credentialSdParties
  copath : CredentialVec CredentialGgmSeed credentialSdGgmDepth
  hiddenCommitment : List UInt8

/-- Leaf seed of `party` recomputed from the opening. -/
def CredentialGgmOpening.leafSeed (prg : CredentialGgmPrg) (o : CredentialGgmOpening)
    (party : Fin credentialSdParties) : CredentialGgmSeed :=
  credentialGgmRecover prg 1 (credentialGgmPath credentialSdGgmDepth o.hidden.val) o.copath
    (credentialGgmPath credentialSdGgmDepth party.val)

/-- Round-1 commitment check of one repetition: the hidden party's commitment is the one
    supplied, and every other party's commitment is recomputed from its reconstructed leaf seed.
    `commit` stands for `commit_limbo_party_r1` with nonce, repetition, salt and auxiliary digest
    fixed. -/
def verifyCredentialGgmOpening (prg : CredentialGgmPrg)
    (commit : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (commitments : Fin credentialSdParties → List UInt8) (o : CredentialGgmOpening) : Bool :=
  decide (o.hiddenCommitment = commitments o.hidden) &&
    (List.finRange credentialSdParties).all (fun p =>
      decide (p = o.hidden) || decide (commit p (o.leafSeed prg p) = commitments p))

/-- An accepted opening recomputes the committed value of every opened party. -/
theorem verifyCredentialGgmOpening_opened (prg : CredentialGgmPrg)
    (commit : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (commitments : Fin credentialSdParties → List UInt8) (o : CredentialGgmOpening)
    (h : verifyCredentialGgmOpening prg commit commitments o = true)
    (party : Fin credentialSdParties) (hOpen : party ≠ o.hidden) :
    commit party (o.leafSeed prg party) = commitments party := by
  unfold verifyCredentialGgmOpening at h
  rw [Bool.and_eq_true] at h
  have hp := List.all_eq_true.mp h.2 party (List.mem_finRange party)
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hp
  exact hp.resolve_left hOpen

/-- **Two openings agree on every commonly opened party, or collide.** If two accepted openings
    of the same round-1 commitments (for hash-based commitments `H ∘ encode`) reconstruct
    different preimages at a party both open, those preimages are a collision of `H`. -/
theorem credentialGgm_overlap_same_digest
    (prg : CredentialGgmPrg) (H : List UInt8 → List UInt8)
    (encode : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (commitments : Fin credentialSdParties → List UInt8)
    (a b : CredentialGgmOpening) (party : Fin credentialSdParties)
    (ha : verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments a = true)
    (hb : verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments b = true)
    (hpa : party ≠ a.hidden) (hpb : party ≠ b.hidden) :
    H (encode party (a.leafSeed prg party)) = H (encode party (b.leafSeed prg party)) :=
  (verifyCredentialGgmOpening_opened prg _ commitments a ha party hpa).trans
    (verifyCredentialGgmOpening_opened prg _ commitments b hb party hpb).symm

/-- Opening check against the check values of a repetition: every opened party's value is
    zero. -/
def credentialGgmCheckDefects {n : Nat} (defect : Fin n → CredentialFp5) (hidden : Fin n) : Bool :=
  (List.finRange n).all (fun p => decide (p = hidden) || decide (defect p = credentialFp5Zero))

/-- A nonzero check value passes the opening check only when its party is the hidden one. -/
theorem credentialGgmCheckDefects_unique {n : Nat} (defect : Fin n → CredentialFp5)
    (bad : Fin n) (hBad : defect bad ≠ credentialFp5Zero) (hidden : Fin n)
    (h : credentialGgmCheckDefects defect hidden = true) : hidden = bad := by
  have hp := List.all_eq_true.mp h bad (List.mem_finRange bad)
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hp
  exact (hp.resolve_right hBad).symm

/-- With all check values zero every hidden party passes. -/
theorem credentialGgmCheckDefects_zero {n : Nat} (hidden : Fin n) :
    credentialGgmCheckDefects (fun _ : Fin n => credentialFp5Zero) hidden = true := by
  apply List.all_eq_true.mpr
  intro p _
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact Or.inr rfl

/-- The presentation's opening round: one opening per repetition, each checked against that
    repetition's commitments and check values. -/
def credentialGgmPresentationAccepts
    (prg : CredentialGgmPrg)
    (commit : Nat → Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (commitments : Nat → Fin credentialSdParties → List UInt8)
    (defect : Nat → Fin credentialSdParties → CredentialFp5)
    (openings : Fin credentialSdRepetitions → CredentialGgmOpening) : Bool :=
  (List.finRange credentialSdRepetitions).all fun r =>
    verifyCredentialGgmOpening prg (commit r.val) (commitments r.val) (openings r) &&
      credentialGgmCheckDefects (defect r.val) (openings r).hidden

/-- **Opening round.** If every repetition has a nonzero check value at party `bad r`, an
    accepted presentation hides exactly `bad r` in every repetition: one hidden-party vector
    out of `256^33`. The nonzero check values are a hypothesis here. -/
theorem credentialGgmPresentation_unique
    (prg : CredentialGgmPrg)
    (commit : Nat → Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (commitments : Nat → Fin credentialSdParties → List UInt8)
    (defect : Nat → Fin credentialSdParties → CredentialFp5)
    (bad : Fin credentialSdRepetitions → Fin credentialSdParties)
    (hBad : ∀ r, defect r.val (bad r) ≠ credentialFp5Zero)
    (openings : Fin credentialSdRepetitions → CredentialGgmOpening)
    (h : credentialGgmPresentationAccepts prg commit commitments defect openings = true) :
    ∀ r, (openings r).hidden = bad r := by
  intro r
  have hr := List.all_eq_true.mp h r (List.mem_finRange r)
  rw [Bool.and_eq_true] at hr
  exact credentialGgmCheckDefects_unique _ _ (hBad r) _ hr.2

set_option exponentiation.threshold 512 in
/-- Size of the hidden-party challenge space: `256 = 2^8` parties, `256^33 = 2^264`, and
    `256^17 = 2^136` for the classical profile. -/
theorem credentialGgm_challenge_space :
    credentialSdParties = 2 ^ credentialSdGgmDepth ∧
    credentialSdParties ^ credentialSdRepetitions = 2 ^ 264 ∧
    credentialSdParties ^ credentialSdRepetitionsClassical = 2 ^ 136 := by decide +kernel

set_option maxRecDepth 4096 in
#verify_constructive credentialGgmRecover_exact verifyCredentialGgmOpening_opened
  credentialGgm_overlap_same_digest credentialGgmCheckDefects_unique
  credentialGgmCheckDefects_zero credentialGgmPresentation_unique credentialGgm_challenge_space

-- Equation used by `Tests/CredentialsTeeth`; no body is exposed.
#export_eqns credentialGgmCheckDefects

theorem durableBurnReserve_empty (keyId sid : List UInt8) (party : UInt16)
    (epoch : UInt64) (attempt : UInt32) (hEpoch : epoch.toNat + 1 < 2 ^ 64) :
    (durableBurnReserve ⟨keyId, [], false⟩ party epoch sid attempt true).1 = true := by
  simp only [durableBurnReserve, durableBurnAvailable, hEpoch, decide_true,
    Bool.not_false, Bool.true_and, List.all_nil, ↓reduceIte]

theorem durableBurnReserve_failed_write (store : DurableNonceBurnStore)
    (party : UInt16) (epoch : UInt64) (sid : List UInt8) (att : UInt32) :
    (durableBurnReserve store party epoch sid att false).1 = false := by
  unfold durableBurnReserve
  cases durableBurnAvailable store party epoch sid att <;> rfl


end Qsag
end
