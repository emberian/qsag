module
/-
# Qsag.Protocol.Signing.PorsFpSecurity: `PORS+FP` openings and the subset-cover bound

A model of `crates/qsag-core/src/pors_fp.rs` over an abstract hash suite, and an independent
derivation of its few-time security figures.

The suite has a leaf hash (index, secret) and a node hash (height and index of the parent,
two children); `pk_seed`, the tree address and the key pair are fixed inside it. `porsFpRoot`
follows `pors_fp_root` check by check; `octopusPositions` is `octopus_positions`; `select` is
`pors_fp_select` on the words read from the XOF; `forgeryBitsMilli` is `forgery_bits_milli`.

1. Canonical bounded multiproof (`porsFpRoot_some_shape`). An accepted opening has a sorted,
   distinct, in-range index set of `reveal` entries inside the pruning bound, one secret per
   index, and exactly as many nodes as the canonical position list. Unsorted or repeated
   indices, a node too many or too few, and any multiproof above `max_auth_nodes` are refused.
2. Completeness (`porsFpRoot_complete`) and binding (`porsFpRoot_binding`,
   `opening_against_honest_root`). The tree's own secrets and nodes open every admissible
   set; a second opening to the same root is equal to the first or exhibits a collision of
   the leaf hash or of the node hash, as an explicit pair of inputs.
3. Selection (`select_admissible`). What the selection returns is admissible.
4. Subset cover. `subsetsFrom` lists the sorted distinct `k`-subsets of an interval, each
   once (`mem_subsetsFrom`, `nodup_subsetsFrom`), `C(n, k)` of them. Those made of marked
   positions only are `C(c, k)` for `c` marked positions (`covered_subsets_count`), after `g`
   signatures `c ≤ g k` (`revealed_count_le`), and `C` is monotone (`choose_mono`). The ratio
   `C(c, k) / C(t, k)` equals the ratio of falling factorials (`choose_cross`), which for
   `k = 28` is a product of 28 factors. `forgery_fraction_bound` puts these together for any
   acceptance test, so pruning and the draw budget do not weaken it.
5. `SHA3_128F` (2048 leaves, 28 revealed). After `r = 1, 2, 3, 4` signatures on one tree the
   fraction of selectable subsets that lie inside the revealed leaves is at most `2^(-209)`,
   `2^(-157)`, `2^(-136)`, `2^(-122)` (`sha3_128f_forgery_bound`). For exactly `28 r` revealed
   leaves these floors are exact (`sha3_128f_binomial_bits`); to a thousandth of a bit the
   values are 209.788, 157.024, 136.093 and 122.451 (`sha3_128f_millibits`).

Comparison with the Rust file. `forgery_bits_milli` returns 209767, 156999, 136068, 122425
(`sha3_128f_rust_estimate`), each a true lower bound (`sha3_128f_rust_estimate_sound`); its
whole-bit readings 209, 156, 136, 122 are therefore sound, and the second is one below the
true floor 157. The figures 210.2, 157.5, 136.3, 122.2 that the Rust test comment calls exact
are not: the first three are above the true values.

Not covered. That the selection is uniform over the subsets (it is, by symmetry, for a random
oracle; here the count is over the list of subsets). The bound is per message-hash
evaluation; grinding, second preimages on the tree, the hypertree above and reuse of a
hypertree leaf are outside it. The byte encodings (`to_wire_bytes`, `from_wire_bytes`) are
not modelled. `forgeryBitsMilli` is checked at the four deployed points, not for all
parameters.

Model notes. Indices are `Nat`, not `u32`. One level of the reconstruction is `applyPlan`
over the grouping `plan`; the Rust loop carries index and node as a pair.
-/

public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.PorsFpSecurity
set_option autoImplicit false

/-! ## 1. Parameters and index sets -/

structure Params where
  treeHeight : Nat
  reveal : Nat
  maxAuthNodes : Nat

def Params.leaves (p : Params) : Nat := 2 ^ p.treeHeight

def Params.wellFormed (p : Params) : Bool :=
  decide (1 ≤ p.treeHeight) && decide (p.treeHeight ≤ 20) && decide (1 ≤ p.reveal) &&
    decide (p.reveal ≤ 1024) && decide (p.reveal ≤ p.leaves / 2) &&
    decide (1 ≤ p.maxAuthNodes) && decide (p.maxAuthNodes ≤ p.reveal * p.treeHeight)

def Params.drawBudget (p : Params) : Nat := 2 * p.reveal + 32

def Params.openingBytesMax (p : Params) : Nat := 32 * p.reveal + 2 + 32 * p.maxAuthNodes

/-- `PorsFpParams::SHA3_128F`. -/
def sha3_128f : Params := ⟨11, 28, 128⟩

/-- `PorsFpParams::TEST_SMALL`. -/
def testSmall : Params := ⟨5, 6, 9⟩

theorem wellFormed_reveal_pos (p : Params) (h : p.wellFormed = true) : 1 ≤ p.reveal := by
  simp only [Params.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2

/-- The `windows(2)` test of the Rust code. -/
def strictIncB : List Nat → Bool
  | x :: y :: rest => decide (x < y) && strictIncB (y :: rest)
  | _ => true

abbrev StrictInc (l : List Nat) : Prop := l.Pairwise fun a b => a < b

theorem strictIncB_iff (l : List Nat) : strictIncB l = true ↔ StrictInc l := by
  induction l with
  | nil => exact ⟨fun _ => List.Pairwise.nil, fun _ => rfl⟩
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨fun _ => List.pairwise_singleton _ _, fun _ => rfl⟩
    | cons y rest =>
      have hstep : strictIncB (x :: y :: rest) = (decide (x < y) && strictIncB (y :: rest)) := by
        rfl
      rw [hstep, Bool.and_eq_true, decide_eq_true_iff, ih]
      constructor
      · intro ⟨hxy, hrest⟩
        refine List.pairwise_cons.mpr ⟨fun a ha => ?_, hrest⟩
        rcases List.mem_cons.mp ha with heq | hmem
        · rw [heq]
          exact hxy
        · exact Nat.lt_trans hxy ((List.pairwise_cons.mp hrest).1 a hmem)
      · intro h
        exact ⟨(List.pairwise_cons.mp h).1 y List.mem_cons_self, (List.pairwise_cons.mp h).2⟩

theorem le_getLast (l : List Nat) (hs : StrictInc l) (x : Nat) (hx : x ∈ l) :
    x ≤ l.getLast?.getD 0 := by
  induction l generalizing x with
  | nil => exact absurd hx List.not_mem_nil
  | cons a t ih =>
    cases t with
    | nil =>
      rw [List.mem_singleton.mp hx]
      exact Nat.le_refl _
    | cons b t' =>
      have hp := List.pairwise_cons.mp hs
      rw [List.getLast?_cons_cons]
      rcases List.mem_cons.mp hx with heq | hmem
      · rw [heq]
        have hab : a < b := hp.1 b List.mem_cons_self
        exact Nat.le_trans (Nat.le_of_lt hab) (ih hp.2 b List.mem_cons_self)
      · exact ih hp.2 x hmem

theorem getLast_mem (l : List Nat) (h : l ≠ []) : l.getLast?.getD 0 ∈ l := by
  induction l with
  | nil => exact absurd rfl h
  | cons a t ih =>
    cases t with
    | nil => exact List.mem_cons_self
    | cons b t' =>
      rw [List.getLast?_cons_cons]
      exact List.mem_cons_of_mem _ (ih (List.cons_ne_nil _ _))

/-! ## 2. The canonical multiproof ("Octopus")

`plan` groups one level of a sorted index list: an even index followed by its successor is a
pair and needs no node; any other index needs its sibling. -/

def sibling (x : Nat) : Nat := if x % 2 = 0 then x + 1 else x - 1

def plan : List Nat → List (Nat × Bool)
  | [] => []
  | [x] => [(x, false)]
  | x :: y :: rest =>
    if x % 2 = 0 ∧ y = x + 1 then (x, true) :: plan rest else (x, false) :: plan (y :: rest)

def parents (idx : List Nat) : List Nat := (plan idx).map fun g => g.1 / 2

def siblings (idx : List Nat) : List Nat :=
  ((plan idx).filter fun g => !g.2).map fun g => sibling g.1

/-- Positions `(height, index)` of the multiproof nodes over `n` levels starting at `lvl`. -/
def octopusFrom : Nat → Nat → List Nat → List (Nat × Nat)
  | 0, _, _ => []
  | n + 1, lvl, idx =>
    (siblings idx).map (fun i => (lvl, i)) ++ octopusFrom n (lvl + 1) (parents idx)

/-- `octopus_positions`. -/
def octopusPositions (treeHeight : Nat) (idx : List Nat) : Option (List (Nat × Nat)) :=
  if decide (31 < treeHeight) || idx.isEmpty || !strictIncB idx ||
      !decide (idx.getLast?.getD 0 < 2 ^ treeHeight) then none
  else some (octopusFrom treeHeight 0 idx)

theorem sibling_odd {x : Nat} (h : x % 2 = 1) : sibling x = x - 1 := by
  unfold sibling
  split
  · exfalso
    omega
  · rfl

theorem sibling_even {x : Nat} (h : x % 2 = 0) : sibling x = x + 1 := by
  unfold sibling
  split
  · rfl
  · contradiction

theorem plan_one (x : Nat) : plan [x] = [(x, false)] := by rfl

theorem plan_pair {x y : Nat} (rest : List Nat) (h : x % 2 = 0 ∧ y = x + 1) :
    plan (x :: y :: rest) = (x, true) :: plan rest := by
  rw [plan]
  split
  · rfl
  · contradiction

theorem plan_single {x y : Nat} (rest : List Nat) (h : ¬ (x % 2 = 0 ∧ y = x + 1)) :
    plan (x :: y :: rest) = (x, false) :: plan (y :: rest) := by
  rw [plan]
  split
  · contradiction
  · rfl

theorem parents_one (x : Nat) : parents [x] = [x / 2] := by rfl

theorem parents_pair {x y : Nat} (rest : List Nat) (h : x % 2 = 0 ∧ y = x + 1) :
    parents (x :: y :: rest) = x / 2 :: parents rest := by
  unfold parents
  rw [plan_pair rest h]
  rfl

theorem parents_single {x y : Nat} (rest : List Nat) (h : ¬ (x % 2 = 0 ∧ y = x + 1)) :
    parents (x :: y :: rest) = x / 2 :: parents (y :: rest) := by
  unfold parents
  rw [plan_single rest h]
  rfl

theorem siblings_one (x : Nat) : siblings [x] = [sibling x] := by rfl

theorem siblings_pair {x y : Nat} (rest : List Nat) (h : x % 2 = 0 ∧ y = x + 1) :
    siblings (x :: y :: rest) = siblings rest := by
  unfold siblings
  rw [plan_pair rest h]
  rfl

theorem siblings_single {x y : Nat} (rest : List Nat) (h : ¬ (x % 2 = 0 ∧ y = x + 1)) :
    siblings (x :: y :: rest) = sibling x :: siblings (y :: rest) := by
  unfold siblings
  rw [plan_single rest h]
  rfl

theorem siblings_length (idx : List Nat) :
    (siblings idx).length = ((plan idx).filter fun g => !g.2).length := by
  unfold siblings
  rw [List.length_map]

theorem octopusFrom_succ (n lvl : Nat) (idx : List Nat) :
    octopusFrom (n + 1) lvl idx =
      (siblings idx).map (fun i => (lvl, i)) ++ octopusFrom n (lvl + 1) (parents idx) := by rfl

theorem fst_mem_of_mem_plan : ∀ (idx : List Nat) (g : Nat × Bool), g ∈ plan idx → g.1 ∈ idx := by
  intro idx
  induction idx using plan.induct with
  | case1 =>
    intro g hg
    exact absurd hg List.not_mem_nil
  | case2 x =>
    intro g hg
    rw [plan_one] at hg
    rw [List.mem_singleton.mp hg]
    exact List.mem_cons_self
  | case3 x y rest h ih =>
    intro g hg
    rw [plan_pair rest h] at hg
    rcases List.mem_cons.mp hg with heq | hmem
    · rw [heq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih g hmem))
  | case4 x y rest h ih =>
    intro g hg
    rw [plan_single rest h] at hg
    rcases List.mem_cons.mp hg with heq | hmem
    · rw [heq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih g hmem)

theorem mem_parents {idx : List Nat} {z : Nat} (h : z ∈ parents idx) :
    ∃ y, y ∈ idx ∧ z = y / 2 := by
  obtain ⟨g, hg, hz⟩ := List.mem_map.mp h
  exact ⟨g.1, fst_mem_of_mem_plan idx g hg, hz.symm⟩

theorem parents_ne_nil : ∀ idx : List Nat, idx ≠ [] → parents idx ≠ [] := by
  intro idx
  induction idx using plan.induct with
  | case1 => intro h; exact absurd rfl h
  | case2 x => intro _; exact List.cons_ne_nil _ _
  | case3 x y rest h _ =>
    intro _
    rw [parents_pair rest h]
    exact List.cons_ne_nil _ _
  | case4 x y rest h _ =>
    intro _
    rw [parents_single rest h]
    exact List.cons_ne_nil _ _

/-- Merging preserves strict order: the next level is again a sorted distinct index set. -/
theorem parents_strictInc : ∀ idx : List Nat, StrictInc idx → StrictInc (parents idx) := by
  intro idx
  induction idx using plan.induct with
  | case1 => intro _; exact List.Pairwise.nil
  | case2 x => intro _; exact List.pairwise_singleton _ _
  | case3 x y rest h ih =>
    intro hs
    rw [parents_pair rest h]
    have hx := List.pairwise_cons.mp hs
    have hy := List.pairwise_cons.mp hx.2
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ih hy.2⟩
    obtain ⟨w, hw, hzw⟩ := mem_parents hz
    have h1 : y < w := hy.1 w hw
    have h2 : x % 2 = 0 := h.1
    have h3 : y = x + 1 := h.2
    show x / 2 < z
    omega
  | case4 x y rest h ih =>
    intro hs
    rw [parents_single rest h]
    have hx := List.pairwise_cons.mp hs
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ih hx.2⟩
    obtain ⟨w, hw, hzw⟩ := mem_parents hz
    have hxy : x < y := hx.1 y List.mem_cons_self
    have hyw : y ≤ w := by
      rcases List.mem_cons.mp hw with heq | hmem
      · exact Nat.le_of_eq heq.symm
      · have hlt : y < w := (List.pairwise_cons.mp hx.2).1 w hmem
        exact Nat.le_of_lt hlt
    show x / 2 < z
    by_cases hpar : x % 2 = 0
    · have hne : ¬ y = x + 1 := fun e => h ⟨hpar, e⟩
      omega
    · omega

def iterParents : Nat → List Nat → List Nat
  | 0, idx => idx
  | n + 1, idx => iterParents n (parents idx)

/-- After `n` levels a sorted nonempty index set below `2^n` has become the single root. -/
theorem iterParents_top : ∀ (n : Nat) (idx : List Nat), StrictInc idx → idx ≠ [] →
    (∀ x ∈ idx, x < 2 ^ n) → iterParents n idx = [0] := by
  intro n
  induction n with
  | zero =>
    intro idx hs hne hr
    cases idx with
    | nil => exact absurd rfl hne
    | cons a t =>
      have ha : a < 1 := hr a List.mem_cons_self
      cases t with
      | nil =>
        have h0 : a = 0 := by omega
        rw [h0]
        rfl
      | cons b t' =>
        have hab : a < b := (List.pairwise_cons.mp hs).1 b List.mem_cons_self
        have hb : b < 1 := hr b (List.mem_cons_of_mem _ List.mem_cons_self)
        omega
  | succ n ih =>
    intro idx hs hne hr
    show iterParents n (parents idx) = [0]
    refine ih (parents idx) (parents_strictInc idx hs) (parents_ne_nil idx hne) fun z hz => ?_
    obtain ⟨y, hy, hzy⟩ := mem_parents hz
    have hy2 : y < 2 ^ (n + 1) := hr y hy
    rw [Nat.pow_succ] at hy2
    omega

/-! ## 3. Root reconstruction (`pors_fp_root`) -/

structure HashSuite (S D : Type) where
  /-- `pors_leaf_hash`: leaf index and revealed secret. -/
  leaf : Nat → S → D
  /-- `th_node_h` at the address of the parent: its height, its index, left and right child. -/
  node : Nat → Nat → D → D → D

variable {S D : Type}

/-- A node that is not paired takes the next multiproof node on the side its parity says. -/
def combine (H : Nat → D → D → D) (x : Nat) (n a : D) : D :=
  if x % 2 = 1 then H (x / 2) a n else H (x / 2) n a

theorem combine_odd (H : Nat → D → D → D) {x : Nat} (n a : D) (h : x % 2 = 1) :
    combine H x n a = H (x / 2) a n := by
  unfold combine
  split
  · rfl
  · contradiction

theorem combine_even (H : Nat → D → D → D) {x : Nat} (n a : D) (h : ¬ x % 2 = 1) :
    combine H x n a = H (x / 2) n a := by
  unfold combine
  split
  · contradiction
  · rfl

def consOut (d : D) : Option (List D × List D) → Option (List D × List D)
  | none => none
  | some r => some (d :: r.1, r.2)

/-- One level of the loop of `pors_fp_root`: the nodes of the current level, the unread
multiproof, and the result: the nodes of the next level and what is left of the multiproof.
The indices travel separately (`plan`, `parents`); the Rust code zips them with the nodes. -/
def applyPlan (H : Nat → D → D → D) :
    List (Nat × Bool) → List D → List D → Option (List D × List D)
  | [], [], auth => some ([], auth)
  | [], _ :: _, _ => none
  | (x, true) :: ps, n :: m :: nodes, auth => consOut (H (x / 2) n m) (applyPlan H ps nodes auth)
  | (_, true) :: _, _, _ => none
  | (x, false) :: ps, n :: nodes, a :: auth =>
    consOut (combine H x n a) (applyPlan H ps nodes auth)
  | (_, false) :: _, _, _ => none

def climb (H : Nat → Nat → D → D → D) :
    Nat → Nat → List Nat → List D → List D → Option (List D × List D)
  | 0, _, _, nodes, auth => some (nodes, auth)
  | n + 1, lvl, idx, nodes, auth =>
    match applyPlan (H (lvl + 1)) (plan idx) nodes auth with
    | none => none
    | some r => climb H n (lvl + 1) (parents idx) r.1 r.2

def headerOk (p : Params) (idx : List Nat) (secretsLen authLen : Nat) : Bool :=
  p.wellFormed && decide (idx.length = p.reveal) && decide (secretsLen = p.reveal) &&
    decide (authLen ≤ p.maxAuthNodes) && strictIncB idx &&
    decide (idx.getLast?.getD 0 < p.leaves)

def topOf : Option (List D × List D) → Option D
  | some ([r], []) => some r
  | _ => none

/-- `pors_fp_root`. -/
@[expose] def porsFpRoot (p : Params) (suite : HashSuite S D) (idx : List Nat) (secrets : List S)
    (auth : List D) : Option D :=
  if headerOk p idx secrets.length auth.length then
    topOf (climb suite.node p.treeHeight 0 idx (List.zipWith suite.leaf idx secrets) auth)
  else none

/-- The index sets a signature may use: sorted, distinct, `reveal` many, in range, and with a
multiproof inside the pruning bound. -/
structure Admissible (p : Params) (idx : List Nat) : Prop where
  strict : StrictInc idx
  length : idx.length = p.reveal
  range : ∀ x ∈ idx, x < p.leaves
  pruned : (octopusFrom p.treeHeight 0 idx).length ≤ p.maxAuthNodes

theorem consOut_eq_some {d : D} {o : Option (List D × List D)} {out rem : List D} :
    consOut d o = some (out, rem) ↔ ∃ out', o = some (out', rem) ∧ out = d :: out' := by
  cases o with
  | none => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | some r =>
    obtain ⟨o1, o2⟩ := r
    constructor
    · intro h
      cases h
      exact ⟨o1, rfl, rfl⟩
    · intro ⟨out', ho, hout⟩
      cases ho
      rw [hout]
      rfl

theorem applyPlan_nil (H : Nat → D → D → D) (nodes auth out rem : List D) :
    applyPlan H [] nodes auth = some (out, rem) ↔ nodes = [] ∧ out = [] ∧ rem = auth := by
  cases nodes with
  | nil =>
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl, rfl⟩
    · intro ⟨_, h2, h3⟩
      rw [h2, h3]
      rfl
  | cons n t => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩

theorem applyPlan_pair (H : Nat → D → D → D) (x : Nat) (ps : List (Nat × Bool))
    (nodes auth out rem : List D) :
    applyPlan H ((x, true) :: ps) nodes auth = some (out, rem) ↔
      ∃ n m nodes' out', nodes = n :: m :: nodes' ∧
        applyPlan H ps nodes' auth = some (out', rem) ∧ out = H (x / 2) n m :: out' := by
  match nodes with
  | [] => exact ⟨fun h => (nomatch h), fun ⟨_, _, _, _, h, _⟩ => (nomatch h)⟩
  | [_] => exact ⟨fun h => (nomatch h), fun ⟨_, _, _, _, h, _⟩ => (nomatch h)⟩
  | n :: m :: nodes' =>
    have e : applyPlan H ((x, true) :: ps) (n :: m :: nodes') auth =
        consOut (H (x / 2) n m) (applyPlan H ps nodes' auth) := by rfl
    rw [e, consOut_eq_some]
    constructor
    · intro ⟨out', h1, h2⟩
      exact ⟨n, m, nodes', out', rfl, h1, h2⟩
    · intro ⟨n', m', t, out', hn, h1, h2⟩
      cases hn
      exact ⟨out', h1, h2⟩

theorem applyPlan_single (H : Nat → D → D → D) (x : Nat) (ps : List (Nat × Bool))
    (nodes auth out rem : List D) :
    applyPlan H ((x, false) :: ps) nodes auth = some (out, rem) ↔
      ∃ n nodes' a auth' out', nodes = n :: nodes' ∧ auth = a :: auth' ∧
        applyPlan H ps nodes' auth' = some (out', rem) ∧ out = combine H x n a :: out' := by
  match nodes, auth with
  | [], [] => exact ⟨fun h => (nomatch h), fun ⟨_, _, _, _, _, h, _⟩ => (nomatch h)⟩
  | [], _ :: _ => exact ⟨fun h => (nomatch h), fun ⟨_, _, _, _, _, h, _⟩ => (nomatch h)⟩
  | _ :: _, [] => exact ⟨fun h => (nomatch h), fun ⟨_, _, _, _, _, _, h, _⟩ => (nomatch h)⟩
  | n :: nodes', a :: auth' =>
    have e : applyPlan H ((x, false) :: ps) (n :: nodes') (a :: auth') =
        consOut (combine H x n a) (applyPlan H ps nodes' auth') := by rfl
    rw [e, consOut_eq_some]
    constructor
    · intro ⟨out', h1, h2⟩
      exact ⟨n, nodes', a, auth', out', rfl, rfl, h1, h2⟩
    · intro ⟨n', t, a', at', out', hn, ha, h1, h2⟩
      cases hn
      cases ha
      exact ⟨out', h1, h2⟩

theorem climb_succ (H : Nat → Nat → D → D → D) (n lvl : Nat) (idx : List Nat)
    (nodes auth : List D) :
    climb H (n + 1) lvl idx nodes auth =
      (match applyPlan (H (lvl + 1)) (plan idx) nodes auth with
        | none => none
        | some r => climb H n (lvl + 1) (parents idx) r.1 r.2) := by rfl

theorem topOf_eq_some (o : Option (List D × List D)) (r : D) :
    topOf o = some r ↔ o = some ([r], []) := by
  constructor
  · intro h
    unfold topOf at h
    split at h
    · cases h
      rfl
    · cases h
  · intro h
    rw [h]
    rfl

theorem headerOk_iff (p : Params) (idx : List Nat) (sl al : Nat) :
    headerOk p idx sl al = true ↔
      p.wellFormed = true ∧ idx.length = p.reveal ∧ sl = p.reveal ∧ al ≤ p.maxAuthNodes ∧
        StrictInc idx ∧ idx.getLast?.getD 0 < p.leaves := by
  simp only [headerOk, Bool.and_eq_true, decide_eq_true_eq, strictIncB_iff, and_assoc]

theorem porsFpRoot_eq_some_iff (p : Params) (suite : HashSuite S D) (idx : List Nat)
    (secrets : List S) (auth : List D) (r : D) :
    porsFpRoot p suite idx secrets auth = some r ↔
      headerOk p idx secrets.length auth.length = true ∧
        climb suite.node p.treeHeight 0 idx (List.zipWith suite.leaf idx secrets) auth =
          some ([r], []) := by
  unfold porsFpRoot
  cases hh : headerOk p idx secrets.length auth.length
  · exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩
  · show topOf _ = some r ↔ _
    rw [topOf_eq_some]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

/-! ## 4. The multiproof is canonical -/

theorem applyPlan_consumed (H : Nat → D → D → D) : ∀ (ps : List (Nat × Bool))
    (nodes auth out rem : List D), applyPlan H ps nodes auth = some (out, rem) →
    ∃ used, auth = used ++ rem ∧ used.length = (ps.filter fun g => !g.2).length := by
  intro ps
  induction ps with
  | nil =>
    intro nodes auth out rem h
    obtain ⟨_, _, h3⟩ := (applyPlan_nil H nodes auth out rem).mp h
    exact ⟨[], h3.symm, rfl⟩
  | cons g ps ih =>
    intro nodes auth out rem h
    obtain ⟨x, b⟩ := g
    cases b with
    | true =>
      obtain ⟨n, m, t, o, _, ht, _⟩ := (applyPlan_pair H x ps nodes auth out rem).mp h
      obtain ⟨used, hu, hl⟩ := ih t auth o rem ht
      exact ⟨used, hu, hl⟩
    | false =>
      obtain ⟨n, t, a, at', o, _, ha, ht, _⟩ := (applyPlan_single H x ps nodes auth out rem).mp h
      obtain ⟨used, hu, hl⟩ := ih t at' o rem ht
      refine ⟨a :: used, ?_, ?_⟩
      · rw [ha, hu]
        rfl
      · show used.length + 1 = (List.filter (fun g => !g.2) ps).length + 1
        rw [hl]

theorem climb_consumed (H : Nat → Nat → D → D → D) : ∀ (n lvl : Nat) (idx : List Nat)
    (nodes auth top rem : List D), climb H n lvl idx nodes auth = some (top, rem) →
    ∃ used, auth = used ++ rem ∧ used.length = (octopusFrom n lvl idx).length := by
  intro n
  induction n with
  | zero =>
    intro lvl idx nodes auth top rem h
    cases h
    exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    intro lvl idx nodes auth top rem h
    rw [climb_succ] at h
    cases happ : applyPlan (H (lvl + 1)) (plan idx) nodes auth with
    | none =>
      rw [happ] at h
      cases h
    | some r =>
      rw [happ] at h
      obtain ⟨r1, r2⟩ := r
      obtain ⟨u1, hu1, hl1⟩ := applyPlan_consumed (H (lvl + 1)) (plan idx) nodes auth r1 r2 happ
      obtain ⟨u2, hu2, hl2⟩ := ih (lvl + 1) (parents idx) r1 r2 top rem h
      refine ⟨u1 ++ u2, ?_, ?_⟩
      · rw [hu1, hu2, List.append_assoc]
      · rw [List.length_append, hl1, hl2, octopusFrom_succ, List.length_append, List.length_map,
          siblings_length]

/-- **Canonical bounded multiproof.** An opening is accepted only for an admissible index set
(sorted, distinct, in range, `reveal` many, pruned), with one secret per index, and with a
multiproof of exactly as many nodes as the canonical position list has. -/
theorem porsFpRoot_some_shape (p : Params) (suite : HashSuite S D) (idx : List Nat)
    (secrets : List S) (auth : List D) (r : D)
    (h : porsFpRoot p suite idx secrets auth = some r) :
    p.wellFormed = true ∧ Admissible p idx ∧ secrets.length = p.reveal ∧
      auth.length = (octopusFrom p.treeHeight 0 idx).length := by
  obtain ⟨hh, hc⟩ := (porsFpRoot_eq_some_iff p suite idx secrets auth r).mp h
  obtain ⟨hw, hlen, hsl, hal, hs, hlast⟩ := (headerOk_iff p idx _ _).mp hh
  obtain ⟨used, hu, hul⟩ := climb_consumed suite.node _ _ _ _ _ _ _ hc
  have hauth : auth.length = (octopusFrom p.treeHeight 0 idx).length := by
    rw [hu, List.append_nil, hul]
  exact ⟨hw, ⟨hs, hlen, fun x hx => Nat.lt_of_le_of_lt (le_getLast idx hs x hx) hlast,
    by rw [← hauth]; exact hal⟩, hsl, hauth⟩

theorem porsFpRoot_none_of (p : Params) (suite : HashSuite S D) (idx : List Nat)
    (secrets : List S) (auth : List D)
    (hbad : ∀ r, ¬ (porsFpRoot p suite idx secrets auth = some r)) :
    porsFpRoot p suite idx secrets auth = none := by
  cases hres : porsFpRoot p suite idx secrets auth with
  | none => rfl
  | some r => exact absurd hres (hbad r)

/-- Unsorted or repeated indices are rejected. -/
theorem unsorted_rejected (p : Params) (suite : HashSuite S D) (idx : List Nat)
    (secrets : List S) (auth : List D) (h : ¬ StrictInc idx) :
    porsFpRoot p suite idx secrets auth = none :=
  porsFpRoot_none_of p suite idx secrets auth fun r hr =>
    h (porsFpRoot_some_shape p suite idx secrets auth r hr).2.1.strict

/-- A multiproof above the pruning bound is rejected, whatever it contains. -/
theorem oversized_rejected (p : Params) (suite : HashSuite S D) (idx : List Nat)
    (secrets : List S) (auth : List D) (h : p.maxAuthNodes < auth.length) :
    porsFpRoot p suite idx secrets auth = none :=
  porsFpRoot_none_of p suite idx secrets auth fun r hr => by
    have hs := porsFpRoot_some_shape p suite idx secrets auth r hr
    have h1 := hs.2.1.pruned
    have h2 := hs.2.2.2
    omega

/-- One node too many or too few is rejected. -/
theorem noncanonical_length_rejected (p : Params) (suite : HashSuite S D) (idx : List Nat)
    (secrets : List S) (auth : List D)
    (h : auth.length ≠ (octopusFrom p.treeHeight 0 idx).length) :
    porsFpRoot p suite idx secrets auth = none :=
  porsFpRoot_none_of p suite idx secrets auth fun r hr =>
    h (porsFpRoot_some_shape p suite idx secrets auth r hr).2.2.2

/-! ## 5. Completeness: the honest opening of an admissible set is accepted -/

/-- The tree over the leaf hashes of the secrets `sec`. -/
def honestTree (suite : HashSuite S D) (sec : Nat → S) : Nat → Nat → D
  | 0, i => suite.leaf i (sec i)
  | l + 1, i =>
    suite.node (l + 1) i (honestTree suite sec l (2 * i)) (honestTree suite sec l (2 * i + 1))

/-- `pors_fp_auth`: the tree nodes at the canonical positions. -/
def honestAuth (suite : HashSuite S D) (sec : Nat → S) (treeHeight : Nat) (idx : List Nat) :
    List D :=
  (octopusFrom treeHeight 0 idx).map fun q => honestTree suite sec q.1 q.2

theorem combine_honest (suite : HashSuite S D) (sec : Nat → S) (l x : Nat) :
    combine (suite.node (l + 1)) x (honestTree suite sec l x)
      (honestTree suite sec l (sibling x)) = honestTree suite sec (l + 1) (x / 2) := by
  show _ = suite.node (l + 1) (x / 2) (honestTree suite sec l (2 * (x / 2)))
    (honestTree suite sec l (2 * (x / 2) + 1))
  by_cases hx : x % 2 = 1
  · have e1 : 2 * (x / 2) = x - 1 := by omega
    have e2 : 2 * (x / 2) + 1 = x := by omega
    rw [combine_odd _ _ _ hx, sibling_odd hx, e2, e1]
  · have e1 : 2 * (x / 2) = x := by omega
    have h0 : x % 2 = 0 := by omega
    rw [combine_even _ _ _ hx, sibling_even h0, e1]

theorem pair_honest (suite : HashSuite S D) (sec : Nat → S) (l : Nat) {x : Nat}
    (h : x % 2 = 0) :
    suite.node (l + 1) (x / 2) (honestTree suite sec l x) (honestTree suite sec l (x + 1)) =
      honestTree suite sec (l + 1) (x / 2) := by
  show _ = suite.node (l + 1) (x / 2) (honestTree suite sec l (2 * (x / 2)))
    (honestTree suite sec l (2 * (x / 2) + 1))
  have e1 : 2 * (x / 2) = x := by omega
  rw [e1]

theorem applyPlan_honest (suite : HashSuite S D) (sec : Nat → S) (l : Nat) :
    ∀ (idx : List Nat) (rem : List D),
    applyPlan (suite.node (l + 1)) (plan idx) (idx.map (honestTree suite sec l))
      ((siblings idx).map (honestTree suite sec l) ++ rem) =
    some ((parents idx).map (honestTree suite sec (l + 1)), rem) := by
  intro idx
  induction idx using plan.induct with
  | case1 =>
    intro rem
    rfl
  | case2 x =>
    intro rem
    rw [plan_one, siblings_one, parents_one]
    show consOut (combine (suite.node (l + 1)) x (honestTree suite sec l x)
      (honestTree suite sec l (sibling x))) (some ([], rem)) = _
    rw [combine_honest]
    rfl
  | case3 x y rest h ih =>
    intro rem
    rw [plan_pair rest h, siblings_pair rest h, parents_pair rest h]
    show consOut (suite.node (l + 1) (x / 2) (honestTree suite sec l x) (honestTree suite sec l y))
      (applyPlan (suite.node (l + 1)) (plan rest) (rest.map (honestTree suite sec l))
        ((siblings rest).map (honestTree suite sec l) ++ rem)) = _
    rw [ih rem, h.2, pair_honest suite sec l h.1]
    rfl
  | case4 x y rest h ih =>
    intro rem
    rw [plan_single rest h, siblings_single rest h, parents_single rest h]
    show consOut (combine (suite.node (l + 1)) x (honestTree suite sec l x)
        (honestTree suite sec l (sibling x)))
      (applyPlan (suite.node (l + 1)) (plan (y :: rest))
        ((y :: rest).map (honestTree suite sec l))
        ((siblings (y :: rest)).map (honestTree suite sec l) ++ rem)) = _
    rw [ih rem, combine_honest]
    rfl

theorem climb_honest (suite : HashSuite S D) (sec : Nat → S) : ∀ (n lvl : Nat) (idx : List Nat)
    (rem : List D),
    climb suite.node n lvl idx (idx.map (honestTree suite sec lvl))
      ((octopusFrom n lvl idx).map (fun q => honestTree suite sec q.1 q.2) ++ rem) =
    some ((iterParents n idx).map (honestTree suite sec (lvl + n)), rem) := by
  intro n
  induction n with
  | zero =>
    intro lvl idx rem
    rfl
  | succ n ih =>
    intro lvl idx rem
    have hauth : (octopusFrom (n + 1) lvl idx).map (fun q => honestTree suite sec q.1 q.2) ++ rem =
        (siblings idx).map (honestTree suite sec lvl) ++
          ((octopusFrom n (lvl + 1) (parents idx)).map (fun q => honestTree suite sec q.1 q.2)
            ++ rem) := by
      rw [octopusFrom_succ, List.map_append, List.map_map, List.append_assoc]
      rfl
    rw [climb_succ, hauth, applyPlan_honest suite sec lvl idx]
    have hlvl : lvl + (n + 1) = lvl + 1 + n := by omega
    rw [hlvl]
    exact ih (lvl + 1) (parents idx) rem

theorem zipWith_leaf_map (suite : HashSuite S D) (sec : Nat → S) (idx : List Nat) :
    List.zipWith suite.leaf idx (idx.map sec) = idx.map (honestTree suite sec 0) := by
  induction idx with
  | nil => rfl
  | cons i idx ih =>
    rw [List.map_cons, List.map_cons, List.zipWith_cons_cons, ih]
    rfl

/-- **Authentication-path completeness.** For every admissible index set the secrets of the
tree and the nodes at the canonical positions reconstruct the root. -/
theorem porsFpRoot_complete (p : Params) (suite : HashSuite S D) (sec : Nat → S)
    (idx : List Nat) (hw : p.wellFormed = true) (hadm : Admissible p idx) :
    porsFpRoot p suite idx (idx.map sec) (honestAuth suite sec p.treeHeight idx) =
      some (honestTree suite sec p.treeHeight 0) := by
  have hk := wellFormed_reveal_pos p hw
  have hne : idx ≠ [] := by
    intro e
    have hl := hadm.length
    rw [e] at hl
    have h0 : 0 = p.reveal := hl
    omega
  rw [porsFpRoot_eq_some_iff]
  refine ⟨(headerOk_iff p idx _ _).mpr ⟨hw, hadm.length, ?_, ?_, hadm.strict,
    hadm.range _ (getLast_mem idx hne)⟩, ?_⟩
  · rw [List.length_map]
    exact hadm.length
  · unfold honestAuth
    rw [List.length_map]
    exact hadm.pruned
  · have hc := climb_honest suite sec p.treeHeight 0 idx []
    rw [List.append_nil, iterParents_top p.treeHeight idx hadm.strict hne hadm.range,
      Nat.zero_add] at hc
    rw [zipWith_leaf_map]
    exact hc

/-! ## 6. Binding: a second opening to the same root is a hash collision -/

def HCollision (H : Nat → D → D → D) : Prop :=
  ∃ i a b a' b', (a ≠ a' ∨ b ≠ b') ∧ H i a b = H i a' b'

/-- Two different child pairs with one parent, at some height and index. -/
def NodeCollision (suite : HashSuite S D) : Prop :=
  ∃ l i a b a' b', (a ≠ a' ∨ b ≠ b') ∧ suite.node l i a b = suite.node l i a' b'

/-- Two different secrets with one leaf hash at one index. -/
def LeafCollision (suite : HashSuite S D) : Prop :=
  ∃ i s s', s ≠ s' ∧ suite.leaf i s = suite.leaf i s'

theorem inj_or_collision [DecidableEq D] (H : Nat → D → D → D) {i : Nat} {a b a' b' : D}
    (h : H i a b = H i a' b') : (a = a' ∧ b = b') ∨ HCollision H := by
  by_cases ha : a = a'
  · by_cases hb : b = b'
    · exact .inl ⟨ha, hb⟩
    · exact .inr ⟨i, a, b, a', b', .inr hb, h⟩
  · exact .inr ⟨i, a, b, a', b', .inl ha, h⟩

theorem applyPlan_binding [DecidableEq D] (H : Nat → D → D → D) : ∀ (ps : List (Nat × Bool))
    (nodes nodes' auth auth' out rem : List D),
    applyPlan H ps nodes auth = some (out, rem) → applyPlan H ps nodes' auth' = some (out, rem) →
    (nodes = nodes' ∧ auth = auth') ∨ HCollision H := by
  intro ps
  induction ps with
  | nil =>
    intro nodes nodes' auth auth' out rem h h'
    obtain ⟨h1, _, h3⟩ := (applyPlan_nil H nodes auth out rem).mp h
    obtain ⟨h1', _, h3'⟩ := (applyPlan_nil H nodes' auth' out rem).mp h'
    exact .inl ⟨h1.trans h1'.symm, h3.symm.trans h3'⟩
  | cons g ps ih =>
    intro nodes nodes' auth auth' out rem h h'
    obtain ⟨x, b⟩ := g
    cases b with
    | true =>
      obtain ⟨n, m, t, o, hn, ht, ho⟩ := (applyPlan_pair H x ps nodes auth out rem).mp h
      obtain ⟨n', m', t', o', hn', ht', ho'⟩ := (applyPlan_pair H x ps nodes' auth' out rem).mp h'
      rw [ho] at ho'
      have hhead := (List.cons.inj ho').1
      have htail := (List.cons.inj ho').2
      rw [← htail] at ht'
      rcases ih t t' auth auth' o rem ht ht' with ⟨e1, e2⟩ | hc
      · rcases inj_or_collision H hhead with ⟨e3, e4⟩ | hc
        · left
          rw [hn, hn', e1, e3, e4]
          exact ⟨rfl, e2⟩
        · exact .inr hc
      · exact .inr hc
    | false =>
      obtain ⟨n, t, a, at₁, o, hn, ha, ht, ho⟩ := (applyPlan_single H x ps nodes auth out rem).mp h
      obtain ⟨n', t', a', at₂, o', hn', ha', ht', ho'⟩ :=
        (applyPlan_single H x ps nodes' auth' out rem).mp h'
      rw [ho] at ho'
      have hhead : combine H x n a = combine H x n' a' := (List.cons.inj ho').1
      have htail := (List.cons.inj ho').2
      rw [← htail] at ht'
      rcases ih t t' at₁ at₂ o rem ht ht' with ⟨e1, e2⟩ | hc
      · have hna : (n = n' ∧ a = a') ∨ HCollision H := by
          by_cases hx : x % 2 = 1
          · rw [combine_odd H n a hx, combine_odd H n' a' hx] at hhead
            rcases inj_or_collision H hhead with ⟨e3, e4⟩ | hc
            · exact .inl ⟨e4, e3⟩
            · exact .inr hc
          · rw [combine_even H n a hx, combine_even H n' a' hx] at hhead
            rcases inj_or_collision H hhead with ⟨e3, e4⟩ | hc
            · exact .inl ⟨e3, e4⟩
            · exact .inr hc
        rcases hna with ⟨e3, e4⟩ | hc
        · left
          rw [hn, hn', ha, ha', e1, e2, e3, e4]
          exact ⟨rfl, rfl⟩
        · exact .inr hc
      · exact .inr hc

theorem climb_binding [DecidableEq D] (H : Nat → Nat → D → D → D) : ∀ (n lvl : Nat)
    (idx : List Nat) (nodes nodes' auth auth' top rem : List D),
    climb H n lvl idx nodes auth = some (top, rem) →
    climb H n lvl idx nodes' auth' = some (top, rem) →
    (nodes = nodes' ∧ auth = auth') ∨ ∃ l, HCollision (H l) := by
  intro n
  induction n with
  | zero =>
    intro lvl idx nodes nodes' auth auth' top rem h h'
    cases h
    cases h'
    exact .inl ⟨rfl, rfl⟩
  | succ n ih =>
    intro lvl idx nodes nodes' auth auth' top rem h h'
    rw [climb_succ] at h h'
    cases happ : applyPlan (H (lvl + 1)) (plan idx) nodes auth with
    | none =>
      rw [happ] at h
      cases h
    | some r =>
      cases happ' : applyPlan (H (lvl + 1)) (plan idx) nodes' auth' with
      | none =>
        rw [happ'] at h'
        cases h'
      | some r' =>
        rw [happ] at h
        rw [happ'] at h'
        obtain ⟨r1, r2⟩ := r
        obtain ⟨r1', r2'⟩ := r'
        rcases ih (lvl + 1) (parents idx) r1 r1' r2 r2' top rem h h' with ⟨e1, e2⟩ | hc
        · rw [← e1, ← e2] at happ'
          rcases applyPlan_binding (H (lvl + 1)) (plan idx) nodes nodes' auth auth' r1 r2 happ
            happ' with hb | hc
          · exact .inl hb
          · exact .inr ⟨lvl + 1, hc⟩
        · exact .inr hc

theorem zipWith_leaf_binding [DecidableEq S] (suite : HashSuite S D) : ∀ (idx : List Nat)
    (secs secs' : List S), secs.length = idx.length → secs'.length = idx.length →
    List.zipWith suite.leaf idx secs = List.zipWith suite.leaf idx secs' →
    secs = secs' ∨ LeafCollision suite := by
  intro idx
  induction idx with
  | nil =>
    intro secs secs' h h' _
    cases secs with
    | nil =>
      cases secs' with
      | nil => exact .inl rfl
      | cons _ _ => exact absurd h' (Nat.succ_ne_zero _)
    | cons _ _ => exact absurd h (Nat.succ_ne_zero _)
  | cons i idx ih =>
    intro secs secs' h h' hz
    cases secs with
    | nil => exact absurd h.symm (Nat.succ_ne_zero _)
    | cons s t =>
      cases secs' with
      | nil => exact absurd h'.symm (Nat.succ_ne_zero _)
      | cons s' t' =>
        rw [List.zipWith_cons_cons, List.zipWith_cons_cons] at hz
        have hz' := List.cons.inj hz
        rcases ih t t' (Nat.succ.inj h) (Nat.succ.inj h') hz'.2 with e | hc
        · by_cases hs : s = s'
          · left
            rw [hs, e]
          · exact .inr ⟨i, s, s', hs, hz'.1⟩
        · exact .inr hc

/-- **Authentication-path binding.** Two accepted openings of one index set to one root are
the same opening, or they exhibit a collision of the leaf hash or of the node hash. -/
