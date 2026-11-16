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
theorem porsFpRoot_binding [DecidableEq S] [DecidableEq D] (p : Params) (suite : HashSuite S D)
    (idx : List Nat) (secs secs' : List S) (auth auth' : List D) (r : D)
    (h : porsFpRoot p suite idx secs auth = some r)
    (h' : porsFpRoot p suite idx secs' auth' = some r) :
    (secs = secs' ∧ auth = auth') ∨ LeafCollision suite ∨ NodeCollision suite := by
  obtain ⟨hh, hc⟩ := (porsFpRoot_eq_some_iff p suite idx secs auth r).mp h
  obtain ⟨hh', hc'⟩ := (porsFpRoot_eq_some_iff p suite idx secs' auth' r).mp h'
  have hl := (headerOk_iff p idx _ _).mp hh
  have hl' := (headerOk_iff p idx _ _).mp hh'
  rcases climb_binding suite.node _ _ _ _ _ _ _ _ _ hc hc' with ⟨e1, e2⟩ | ⟨l, hcol⟩
  · rcases zipWith_leaf_binding suite idx secs secs' (hl.2.2.1.trans hl.2.1.symm)
      (hl'.2.2.1.trans hl'.2.1.symm) e1 with e | hcl
    · exact .inl ⟨e, e2⟩
    · exact .inr (.inl hcl)
  · obtain ⟨i, a, b, a', b', hne, heq⟩ := hcol
    exact .inr (.inr ⟨l, i, a, b, a', b', hne, heq⟩)

/-- An opening accepted against the root of the signer's tree reveals the signer's secrets
at those indices and carries the tree's own nodes, or it exhibits a collision. -/
theorem opening_against_honest_root [DecidableEq S] [DecidableEq D] (p : Params)
    (suite : HashSuite S D) (sec : Nat → S) (idx : List Nat) (secs : List S) (auth : List D)
    (h : porsFpRoot p suite idx secs auth = some (honestTree suite sec p.treeHeight 0)) :
    (secs = idx.map sec ∧ auth = honestAuth suite sec p.treeHeight idx) ∨
      LeafCollision suite ∨ NodeCollision suite := by
  have hs := porsFpRoot_some_shape p suite idx secs auth _ h
  exact porsFpRoot_binding p suite idx secs (idx.map sec) auth
    (honestAuth suite sec p.treeHeight idx) _ h
    (porsFpRoot_complete p suite sec idx hs.1 hs.2.1)

/-! ## 7. Index selection (`pors_fp_select`) -/

def insertSorted (v : Nat) : List Nat → List Nat
  | [] => [v]
  | x :: xs => if v < x then v :: x :: xs else x :: insertSorted v xs

def sortNat (l : List Nat) : List Nat := l.foldr insertSorted []

/-- The draw loop: stop at `k` values, skip a word already drawn. -/
def drawDistinct (k : Nat) : List Nat → List Nat → List Nat
  | [], acc => acc
  | v :: ws, acc =>
    if acc.length = k then acc
    else if v ∈ acc then drawDistinct k ws acc else drawDistinct k ws (acc ++ [v])

def drawn (p : Params) (words : List Nat) : List Nat :=
  drawDistinct p.reveal ((words.take p.drawBudget).map fun w => w % p.leaves) []

/-- `pors_fp_select` on the 32-bit words read from the message XOF. -/
def select (p : Params) (words : List Nat) : Option (List Nat) :=
  if p.wellFormed && decide ((drawn p words).length = p.reveal) &&
      decide ((octopusFrom p.treeHeight 0 (sortNat (drawn p words))).length ≤ p.maxAuthNodes)
  then some (sortNat (drawn p words)) else none

theorem insertSorted_cons (v x : Nat) (xs : List Nat) :
    insertSorted v (x :: xs) = if v < x then v :: x :: xs else x :: insertSorted v xs := by rfl

theorem mem_insertSorted (v y : Nat) (l : List Nat) : y ∈ insertSorted v l ↔ y = v ∨ y ∈ l := by
  induction l with
  | nil =>
    show y ∈ [v] ↔ _
    exact ⟨fun h => .inl (List.mem_singleton.mp h),
      fun h => h.elim (fun e => List.mem_singleton.mpr e) (fun h => absurd h List.not_mem_nil)⟩
  | cons x xs ih =>
    rw [insertSorted_cons]
    split
    · exact List.mem_cons
    · rw [List.mem_cons, ih, List.mem_cons]
      exact ⟨fun h => h.elim (fun e => .inr (.inl e)) (fun h => h.elim .inl (fun h => .inr (.inr h))),
        fun h => h.elim (fun e => .inr (.inl e)) (fun h => h.elim .inl (fun h => .inr (.inr h)))⟩

theorem length_insertSorted (v : Nat) (l : List Nat) :
    (insertSorted v l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [insertSorted_cons]
    split
    · rfl
    · rw [List.length_cons, ih, List.length_cons]

theorem insertSorted_strictInc (v : Nat) (l : List Nat) (hs : StrictInc l) (hv : v ∉ l) :
    StrictInc (insertSorted v l) := by
  induction l with
  | nil => exact List.pairwise_singleton _ _
  | cons x xs ih =>
    have hp := List.pairwise_cons.mp hs
    rw [insertSorted_cons]
    split
    · rename_i hvx
      refine List.pairwise_cons.mpr ⟨fun a ha => ?_, hs⟩
      rcases List.mem_cons.mp ha with heq | hmem
      · rw [heq]
        exact hvx
      · have hxa : x < a := hp.1 a hmem
        exact Nat.lt_trans hvx hxa
    · rename_i hvx
      have hne : ¬ v = x := fun e => hv (by rw [e]; exact List.mem_cons_self)
      have hxv : x < v := by omega
      refine List.pairwise_cons.mpr ⟨fun a ha => ?_,
        ih hp.2 fun h => hv (List.mem_cons_of_mem _ h)⟩
      rcases (mem_insertSorted v a xs).mp ha with heq | hmem
      · rw [heq]
        exact hxv
      · exact hp.1 a hmem

theorem sortNat_cons (x : Nat) (l : List Nat) : sortNat (x :: l) = insertSorted x (sortNat l) := by
  rfl

theorem mem_sortNat (y : Nat) (l : List Nat) : y ∈ sortNat l ↔ y ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons x xs ih => rw [sortNat_cons, mem_insertSorted, ih, List.mem_cons]

theorem length_sortNat (l : List Nat) : (sortNat l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [sortNat_cons, length_insertSorted, ih, List.length_cons]

theorem sortNat_strictInc (l : List Nat) (hn : l.Nodup) : StrictInc (sortNat l) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    have hc := List.nodup_cons.mp hn
    rw [sortNat_cons]
    exact insertSorted_strictInc x _ (ih hc.2) fun h => hc.1 ((mem_sortNat x xs).mp h)

theorem drawDistinct_full {k v : Nat} (ws : List Nat) {acc : List Nat} (h : acc.length = k) :
    drawDistinct k (v :: ws) acc = acc := by
  rw [drawDistinct]
  split
  · rfl
  · contradiction

theorem drawDistinct_dup {k v : Nat} (ws : List Nat) {acc : List Nat} (h : ¬ acc.length = k)
    (hm : v ∈ acc) : drawDistinct k (v :: ws) acc = drawDistinct k ws acc := by
  rw [drawDistinct]
  split
  · contradiction
  · rfl

theorem drawDistinct_new {k v : Nat} (ws : List Nat) {acc : List Nat} (h : ¬ acc.length = k)
    (hm : v ∉ acc) : drawDistinct k (v :: ws) acc = drawDistinct k ws (acc ++ [v]) := by
  rw [drawDistinct]
  split
  · contradiction
  · rfl

theorem drawDistinct_inv (k t : Nat) : ∀ (ws acc : List Nat), (∀ v ∈ ws, v < t) → acc.Nodup →
    (∀ x ∈ acc, x < t) →
    (drawDistinct k ws acc).Nodup ∧ ∀ x ∈ drawDistinct k ws acc, x < t := by
  intro ws
  induction ws with
  | nil =>
    intro acc _ hn hr
    exact ⟨hn, hr⟩
  | cons v ws ih =>
    intro acc hws hn hr
    have hws' : ∀ w ∈ ws, w < t := fun w hw => hws w (List.mem_cons_of_mem _ hw)
    by_cases h1 : acc.length = k
    · rw [drawDistinct_full ws h1]
      exact ⟨hn, hr⟩
    · by_cases hm : v ∈ acc
      · rw [drawDistinct_dup ws h1 hm]
        exact ih acc hws' hn hr
      · rw [drawDistinct_new ws h1 hm]
        refine ih (acc ++ [v]) hws' ?_ ?_
        · refine List.nodup_append.mpr ⟨hn, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton.mp hb]
          exact fun e => hm (e ▸ ha)
        · intro x hx
          rcases List.mem_append.mp hx with hin | hlast
          · exact hr x hin
          · rw [List.mem_singleton.mp hlast]
            exact hws v List.mem_cons_self

/-- **Selection.** Every subset the selection returns is admissible: sorted, distinct,
`reveal` many, in range, and inside the pruning bound. -/
theorem select_admissible (p : Params) (words : List Nat) (idx : List Nat)
    (h : select p words = some idx) : Admissible p idx := by
  have hinv := drawDistinct_inv p.reveal p.leaves
    ((words.take p.drawBudget).map fun w => w % p.leaves) []
    (fun v hv => by
      obtain ⟨w, _, hw⟩ := List.mem_map.mp hv
      rw [← hw]
      exact Nat.mod_lt _ (Nat.two_pow_pos _))
    List.Pairwise.nil (fun x hx => absurd hx List.not_mem_nil)
  unfold select at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨sortNat_strictInc _ hinv.1, by rw [length_sortNat]; exact hc.1.2,
      fun x hx => hinv.2 x ((mem_sortNat x _).mp hx), hc.2⟩
  · cases h

/-- A selected subset opens: the honest opening of what `select` returns is accepted. -/
theorem selected_subset_opens (p : Params) (suite : HashSuite S D) (sec : Nat → S)
    (words : List Nat) (idx : List Nat) (hw : p.wellFormed = true)
    (h : select p words = some idx) :
    porsFpRoot p suite idx (idx.map sec) (honestAuth suite sec p.treeHeight idx) =
      some (honestTree suite sec p.treeHeight 0) :=
  porsFpRoot_complete p suite sec idx hw (select_admissible p words idx h)

/-! ## 8. Counting subsets

`subsetsFrom k lo n` lists the strictly increasing `k`-element index lists inside
`[lo, lo + n)`, each once. The counts below are proved for arbitrary sizes; nothing here is
evaluated on a concrete tree. -/

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

def subsetsFrom : Nat → Nat → Nat → List (List Nat)
  | 0, _, _ => [[]]
  | _ + 1, _, 0 => []
  | k + 1, lo, n + 1 =>
    (subsetsFrom k (lo + 1) n).map (fun s => lo :: s) ++ subsetsFrom (k + 1) (lo + 1) n

theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := by rfl

theorem choose_succ_succ (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := by rfl

theorem subsetsFrom_zero (lo n : Nat) : subsetsFrom 0 lo n = [[]] := by cases n <;> rfl

theorem subsetsFrom_succ (k lo n : Nat) :
    subsetsFrom (k + 1) lo (n + 1) =
      (subsetsFrom k (lo + 1) n).map (fun s => lo :: s) ++ subsetsFrom (k + 1) (lo + 1) n := by
  rfl

theorem length_subsetsFrom : ∀ (n k lo : Nat), (subsetsFrom k lo n).length = choose n k := by
  intro n
  induction n with
  | zero =>
    intro k lo
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ n ih =>
    intro k lo
    cases k with
    | zero => rw [subsetsFrom_zero, choose_zero_right]; rfl
    | succ k =>
      rw [subsetsFrom_succ, List.length_append, List.length_map, ih, ih, choose_succ_succ]

theorem lt_shift {x lo n : Nat} (h : x < lo + 1 + n) : x < lo + (n + 1) := by omega

theorem lt_unshift {x lo n : Nat} (h : x < lo + (n + 1)) : x < lo + 1 + n := by omega

/-- The enumeration is exactly the sorted distinct `k`-subsets of the interval. -/
theorem mem_subsetsFrom : ∀ (n k lo : Nat) (s : List Nat),
    s ∈ subsetsFrom k lo n ↔
      StrictInc s ∧ s.length = k ∧ ∀ x ∈ s, lo ≤ x ∧ x < lo + n := by
  intro n
  induction n with
  | zero =>
    intro k lo s
    cases k with
    | zero =>
      rw [subsetsFrom_zero, List.mem_singleton]
      constructor
      · intro h
        rw [h]
        exact ⟨List.Pairwise.nil, rfl, fun x hx => absurd hx List.not_mem_nil⟩
      · intro h
        cases s with
        | nil => rfl
        | cons a t => exact absurd h.2.1 (Nat.succ_ne_zero _)
    | succ k =>
      constructor
      · intro h
        exact absurd h List.not_mem_nil
      · intro h
        cases s with
        | nil => exact absurd h.2.1.symm (Nat.succ_ne_zero _)
        | cons a t =>
          have ha := h.2.2 a List.mem_cons_self
          exact absurd ha.2 (Nat.not_lt.mpr ha.1)
  | succ n ih =>
    intro k lo s
    cases k with
    | zero =>
      rw [subsetsFrom_zero, List.mem_singleton]
      constructor
      · intro h
        rw [h]
        exact ⟨List.Pairwise.nil, rfl, fun x hx => absurd hx List.not_mem_nil⟩
      · intro h
        cases s with
        | nil => rfl
        | cons a t => exact absurd h.2.1 (Nat.succ_ne_zero _)
    | succ k =>
      rw [subsetsFrom_succ, List.mem_append, List.mem_map]
      constructor
      · intro h
        rcases h with ⟨s', hs', heq⟩ | hright
        · obtain ⟨hst, hlen, hr⟩ := (ih k (lo + 1) s').mp hs'
          rw [← heq]
          refine ⟨List.pairwise_cons.mpr ⟨fun a ha => ?_, hst⟩, by rw [List.length_cons, hlen],
            fun x hx => ?_⟩
          · exact (hr a ha).1
          · rcases List.mem_cons.mp hx with hx0 | hxs
            · rw [hx0]
              exact ⟨Nat.le_refl _, Nat.lt_succ_of_le (Nat.le_add_right _ _)⟩
            · exact ⟨Nat.le_of_succ_le (hr x hxs).1, lt_shift (hr x hxs).2⟩
        · obtain ⟨hst, hlen, hr⟩ := (ih (k + 1) (lo + 1) s).mp hright
          exact ⟨hst, hlen, fun x hx => ⟨Nat.le_of_succ_le (hr x hx).1, lt_shift (hr x hx).2⟩⟩
      · intro ⟨hst, hlen, hr⟩
        cases s with
        | nil => exact absurd hlen.symm (Nat.succ_ne_zero _)
        | cons a t =>
          have hp := List.pairwise_cons.mp hst
          have ha := hr a List.mem_cons_self
          by_cases hal : a = lo
          · left
            refine ⟨t, (ih k (lo + 1) t).mpr ⟨hp.2, Nat.succ.inj hlen, fun y hy => ?_⟩, by rw [hal]⟩
            have h1 : a < y := hp.1 y hy
            rw [hal] at h1
            exact ⟨h1, lt_unshift (hr y (List.mem_cons_of_mem _ hy)).2⟩
          · right
            refine (ih (k + 1) (lo + 1) (a :: t)).mpr ⟨hst, hlen, fun y hy => ?_⟩
            rcases List.mem_cons.mp hy with hy0 | hyt
            · rw [hy0]
              exact ⟨Nat.lt_of_le_of_ne ha.1 (fun e => hal e.symm), lt_unshift ha.2⟩
            · have h1 : a < y := hp.1 y hyt
              exact ⟨Nat.lt_of_le_of_lt ha.1 h1, lt_unshift (hr y (List.mem_cons_of_mem _ hyt)).2⟩

/-- No subset is listed twice. -/
theorem nodup_subsetsFrom : ∀ (n k lo : Nat), (subsetsFrom k lo n).Nodup := by
  intro n
  induction n with
  | zero =>
    intro k lo
    cases k with
    | zero => exact List.pairwise_singleton _ _
    | succ k => exact List.Pairwise.nil
  | succ n ih =>
    intro k lo
    cases k with
    | zero =>
      rw [subsetsFrom_zero]
      exact List.pairwise_singleton _ _
    | succ k =>
      rw [subsetsFrom_succ]
      refine List.nodup_append.mpr ⟨?_, ih (k + 1) (lo + 1), fun a ha b hb e => ?_⟩
      · refine List.pairwise_map.mpr (List.Pairwise.imp (fun hne e => hne ?_) (ih k (lo + 1)))
        exact (List.cons.inj e).2
      · obtain ⟨s', _, heq⟩ := List.mem_map.mp ha
        rw [← e, ← heq] at hb
        have hlo := ((mem_subsetsFrom n (k + 1) (lo + 1) (lo :: s')).mp hb).2.2 lo List.mem_cons_self
        exact Nat.not_succ_le_self lo hlo.1

/-- Number of marked positions of `[lo, lo + n)`. -/
def covCount (cov : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | lo, n + 1 => (if cov lo then 1 else 0) + covCount cov (lo + 1) n

theorem covCount_succ (cov : Nat → Bool) (lo n : Nat) :
    covCount cov lo (n + 1) = (if cov lo then 1 else 0) + covCount cov (lo + 1) n := by rfl

theorem filter_all_map_cons_pos (cov : Nat → Bool) (a : Nat) (l : List (List Nat))
    (h : cov a = true) :
    (l.map fun s => a :: s).filter (fun s => s.all cov) =
      (l.filter fun s => s.all cov).map fun s => a :: s := by
  rw [List.filter_map]
  refine congrArg (List.map fun s => a :: s) (List.filter_congr fun s _ => ?_)
  show (a :: s).all cov = s.all cov
  rw [List.all_cons, h, Bool.true_and]

theorem filter_all_map_cons_neg (cov : Nat → Bool) (a : Nat) (l : List (List Nat))
    (h : cov a = false) : (l.map fun s => a :: s).filter (fun s => s.all cov) = [] := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [List.map_cons, List.filter_cons_of_neg (p := fun s => s.all cov) (a := a :: s)
      (by
        show ¬ (a :: s).all cov = true
        rw [List.all_cons, h, Bool.false_and]
        exact Bool.false_ne_true)]
    exact ih

/-- **Subset-cover count.** The `k`-subsets all of whose members are marked are as many as the
`k`-subsets of the marked positions. -/
theorem covered_subsets_count (cov : Nat → Bool) : ∀ (n k lo : Nat),
    ((subsetsFrom k lo n).filter fun s => s.all cov).length = choose (covCount cov lo n) k := by
  intro n
  induction n with
  | zero =>
    intro k lo
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ n ih =>
    intro k lo
    cases k with
    | zero =>
      rw [subsetsFrom_zero, choose_zero_right]
      rfl
    | succ k =>
      rw [subsetsFrom_succ, List.filter_append, List.length_append, ih (k + 1) (lo + 1),
        covCount_succ]
      cases hc : cov lo
      · rw [filter_all_map_cons_neg cov lo _ hc]
        show 0 + choose _ _ = choose (0 + _) _
        rw [Nat.zero_add, Nat.zero_add]
      · rw [filter_all_map_cons_pos cov lo _ hc, List.length_map, ih k (lo + 1)]
        show _ = choose (1 + covCount cov (lo + 1) n) (k + 1)
        rw [Nat.add_comm 1, choose_succ_succ]

theorem choose_le_succ (n k : Nat) : choose n k ≤ choose (n + 1) k := by
  cases k with
  | zero =>
    rw [choose_zero_right, choose_zero_right]
    exact Nat.le_refl _
  | succ k =>
    rw [choose_succ_succ]
    exact Nat.le_add_left _ _

/-- Binomial dominance in the upper argument. -/
theorem choose_mono (k : Nat) {a b : Nat} (h : a ≤ b) : choose a k ≤ choose b k := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (choose_le_succ _ k)

/-- Absorption: `(k + 1) * C(n + 1, k + 1) = (n + 1) * C(n, k)`. -/
theorem succ_mul_choose (n k : Nat) :
    (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ n ih =>
    cases k with
    | zero =>
      have h1 := ih 0
      rw [choose_zero_right] at h1
      rw [choose_succ_succ (n + 1) 0, choose_zero_right]
      omega
    | succ j =>
      have h1 := ih j
      have h2 := ih (j + 1)
      have hc : choose (n + 1) (j + 1) = choose n j + choose n (j + 1) := choose_succ_succ n j
      rw [choose_succ_succ (n + 1) (j + 1), Nat.mul_add, h2, Nat.add_one_mul (j + 1), h1,
        Nat.add_one_mul (n + 1) (choose (n + 1) (j + 1)), hc, Nat.mul_add]
      omega

def fact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * fact k

/-- The falling factorial `n (n - 1) ⋯ (n - k + 1)`. -/
def ffTop : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (n + 1) * ffTop n k

theorem choose_mul_fact (n k : Nat) : choose n k * fact k = ffTop n k := by
  induction k generalizing n with
  | zero =>
    rw [choose_zero_right]
    cases n <;> rfl
  | succ k ih =>
    cases n with
    | zero =>
      rw [choose_zero_succ, Nat.zero_mul]
      rfl
    | succ n =>
      show choose (n + 1) (k + 1) * ((k + 1) * fact k) = (n + 1) * ffTop n k
      rw [← ih n, ← Nat.mul_assoc, Nat.mul_comm (choose (n + 1) (k + 1)) (k + 1),
        succ_mul_choose, Nat.mul_assoc]

/-- The binomial ratio is the falling-factorial ratio: `C(c,k) / C(t,k) = c^(k) / t^(k)`. -/
theorem choose_cross (c t k : Nat) : choose c k * ffTop t k = choose t k * ffTop c k := by
  rw [← choose_mul_fact t k, ← choose_mul_fact c k]
  exact Nat.mul_left_comm _ _ _

/-- `num / den ≤ 2^(-e)`. -/
@[expose] def AtLeastBits (e num den : Nat) : Prop := 2 ^ e * num ≤ den

/-- `num / den > 2^(-e)`. -/
def BelowBits (e num den : Nat) : Prop := den < 2 ^ e * num

theorem atLeastBits_choose_of_ffTop {c t k e : Nat} (hpos : 0 < ffTop c k)
    (h : AtLeastBits e (ffTop c k) (ffTop t k)) : AtLeastBits e (choose c k) (choose t k) := by
  unfold AtLeastBits at h ⊢
  have h1 : choose c k * (2 ^ e * ffTop c k) ≤ choose c k * ffTop t k := Nat.mul_le_mul_left _ h
  rw [choose_cross c t k] at h1
  have h3 : 2 ^ e * choose c k * ffTop c k = choose c k * (2 ^ e * ffTop c k) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_left_comm _ _ _
  rw [← h3] at h1
  exact Nat.le_of_mul_le_mul_right h1 hpos

theorem belowBits_choose_of_ffTop {c t k e : Nat} (hpos : 0 < ffTop c k)
    (h : BelowBits e (ffTop c k) (ffTop t k)) : BelowBits e (choose c k) (choose t k) := by
  unfold BelowBits at h ⊢
  have hcpos : 0 < choose c k := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have hf := choose_mul_fact c k
    rw [h0, Nat.zero_mul] at hf
    rw [← hf] at hpos
    exact Nat.lt_irrefl _ hpos
  refine Nat.lt_of_not_le fun hle => ?_
  have h1 : 2 ^ e * choose c k * ffTop c k ≤ choose t k * ffTop c k := Nat.mul_le_mul_right _ hle
  rw [← choose_cross c t k] at h1
  have h2 : choose c k * ffTop t k < choose c k * (2 ^ e * ffTop c k) :=
    Nat.mul_lt_mul_of_pos_left h hcpos
  have h3 : 2 ^ e * choose c k * ffTop c k = choose c k * (2 ^ e * ffTop c k) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_left_comm _ _ _
  rw [h3] at h1
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 h1)

/-! ## 9. The subset-cover bound -/

theorem filter_length_lt {α : Type} (q : α → Bool) (l : List α) (a : α) (ha : a ∈ l)
    (hq : q a = false) : (l.filter q).length < l.length := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons x xs ih =>
    cases hx : q x
    · rw [List.filter_cons_of_neg (by rw [hx]; exact Bool.false_ne_true)]
      exact Nat.lt_succ_of_le (List.length_filter_le q xs)
    · rw [List.filter_cons_of_pos hx]
      rcases List.mem_cons.mp ha with heq | hmem
      · rw [heq, hx] at hq
        cases hq
      · exact Nat.succ_lt_succ (ih hmem)

theorem covCount_congr (cov cov' : Nat → Bool) : ∀ (n lo : Nat),
    (∀ x, lo ≤ x → x < lo + n → cov x = cov' x) → covCount cov lo n = covCount cov' lo n := by
  intro n
  induction n with
  | zero =>
    intro lo _
    rfl
  | succ n ih =>
    intro lo h
    rw [covCount_succ, covCount_succ, h lo (Nat.le_refl _) (by omega),
      ih (lo + 1) fun x h1 h2 => h x (by omega) (by omega)]

/-- The marked positions that lie in a list are at most as many as its entries. -/
theorem covCount_mem_le : ∀ (n lo : Nat) (L : List Nat),
    covCount (fun x => decide (x ∈ L)) lo n ≤ L.length := by
  intro n
  induction n with
  | zero =>
    intro lo L
    exact Nat.zero_le _
  | succ n ih =>
    intro lo L
    rw [covCount_succ]
    show (if decide (lo ∈ L) = true then 1 else 0) + covCount (fun x => decide (x ∈ L)) (lo + 1) n
      ≤ L.length
    by_cases hmem : lo ∈ L
    · have hlt := filter_length_lt (fun y => !decide (y = lo)) L lo hmem
        (by show (!decide (lo = lo)) = false; rw [decide_eq_true rfl]; rfl)
      have hcongr := covCount_congr (fun x => decide (x ∈ L))
        (fun x => decide (x ∈ L.filter fun y => !decide (y = lo))) n (lo + 1) (fun x h1 _ => by
          have hne : ¬ x = lo := by omega
          show decide (x ∈ L) = decide (x ∈ L.filter fun y => !decide (y = lo))
          by_cases hx : x ∈ L
          · rw [decide_eq_true hx, decide_eq_true (List.mem_filter.mpr
              ⟨hx, by show (!decide (x = lo)) = true; rw [decide_eq_false hne]; rfl⟩)]
          · rw [decide_eq_false hx, decide_eq_false (fun h => hx (List.mem_filter.mp h).1)])
      have hih := ih (lo + 1) (L.filter fun y => !decide (y = lo))
      have h1 : (if decide (lo ∈ L) = true then 1 else 0) = 1 := by
        rw [decide_eq_true hmem]
        rfl
      rw [h1, hcongr]
      omega
    · have h0 : (if decide (lo ∈ L) = true then 1 else 0) = 0 := by
        rw [decide_eq_false hmem]
        rfl
      rw [h0, Nat.zero_add]
      exact ih (lo + 1) L

/-- The leaves made public by a list of signatures, each given by its index set. -/
def revealedBy (sigs : List (List Nat)) : Nat → Bool := fun x => decide (x ∈ sigs.flatten)

theorem flatten_length_of_uniform (k : Nat) : ∀ sigs : List (List Nat),
    (∀ s ∈ sigs, s.length = k) → sigs.flatten.length = sigs.length * k := by
  intro sigs
  induction sigs with
  | nil =>
    intro _
    exact (Nat.zero_mul k).symm
  | cons s t ih =>
    intro h
    rw [List.flatten_cons, List.length_append, h s List.mem_cons_self,
      ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs'), List.length_cons, Nat.add_one_mul,
      Nat.add_comm]

/-- After `g` signatures of `k` leaves each at most `g * k` leaves are public. -/
theorem revealed_count_le (sigs : List (List Nat)) (k t : Nat) (h : ∀ s ∈ sigs, s.length = k) :
    covCount (revealedBy sigs) 0 t ≤ sigs.length * k := by
  rw [← flatten_length_of_uniform k sigs h]
  exact covCount_mem_le t 0 sigs.flatten

/-- All sorted distinct `reveal`-subsets of the leaves. -/
def subsets (p : Params) : List (List Nat) := subsetsFrom p.reveal 0 p.leaves

/-- The subsets that pass an acceptance test (the pruning test, the draw budget, anything)
and consist of public leaves only: the message-hash outputs that make a forgery. -/
def coverWins (p : Params) (acc : List Nat → Bool) (cov : Nat → Bool) : List (List Nat) :=
  (subsets p).filter fun s => acc s && s.all cov

theorem mem_subsets_iff (p : Params) (s : List Nat) :
    s ∈ subsets p ↔ StrictInc s ∧ s.length = p.reveal ∧ ∀ x ∈ s, x < p.leaves := by
  unfold subsets
  rw [mem_subsetsFrom]
  constructor
  · intro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun x hx => ?_⟩
    have hx2 := (h3 x hx).2
    rw [Nat.zero_add] at hx2
    exact hx2
  · intro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun x hx => ⟨Nat.zero_le _, ?_⟩⟩
    rw [Nat.zero_add]
    exact h3 x hx

/-- The admissible index sets are the listed subsets that pass the pruning test. -/
theorem admissible_iff (p : Params) (idx : List Nat) :
    Admissible p idx ↔
      idx ∈ subsets p ∧ (octopusFrom p.treeHeight 0 idx).length ≤ p.maxAuthNodes := by
  rw [mem_subsets_iff]
  exact ⟨fun h => ⟨⟨h.strict, h.length, h.range⟩, h.pruned⟩,
    fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩⟩

theorem subsets_nodup (p : Params) : (subsets p).Nodup := nodup_subsetsFrom _ _ _

theorem subsets_length (p : Params) : (subsets p).length = choose p.leaves p.reveal :=
  length_subsetsFrom _ _ _

theorem coverWins_length_le (p : Params) (acc : List Nat → Bool) (cov : Nat → Bool) :
    (coverWins p acc cov).length ≤ choose (covCount cov 0 p.leaves) p.reveal := by
  have e : coverWins p acc cov =
      ((subsetsFrom p.reveal 0 p.leaves).filter fun s => s.all cov).filter acc :=
    List.filter_filter.symm
  rw [e]
  exact Nat.le_trans (List.length_filter_le _ _)
    (Nat.le_of_eq (covered_subsets_count cov p.leaves p.reveal 0))

/-- Without an acceptance test the count is exact. -/
theorem coverWins_all_length (p : Params) (cov : Nat → Bool) :
    (coverWins p (fun _ => true) cov).length = choose (covCount cov 0 p.leaves) p.reveal :=
  covered_subsets_count cov p.leaves p.reveal 0

/-- **Subset-cover bound.** After at most `r` signatures under one tree, the subsets that
would be a forgery are at most a `2^(-e)` fraction of all subsets, whenever the
falling-factorial ratio `(r k)^(k) / t^(k)` is at most `2^(-e)`. The acceptance test `acc`
is arbitrary: pruning removes subsets and cannot raise the fraction. -/
theorem forgery_fraction_bound (p : Params) (acc : List Nat → Bool) (sigs : List (List Nat))
    (r e : Nat) (hk : ∀ s ∈ sigs, s.length = p.reveal) (hsigs : sigs.length ≤ r)
    (hb : AtLeastBits e (ffTop (r * p.reveal) p.reveal) (ffTop p.leaves p.reveal))
    (hpos : 0 < ffTop (r * p.reveal) p.reveal) :
    AtLeastBits e (coverWins p acc (revealedBy sigs)).length (subsets p).length := by
  have h1 := atLeastBits_choose_of_ffTop hpos hb
  unfold AtLeastBits at h1 ⊢
  rw [subsets_length]
  have hc : covCount (revealedBy sigs) 0 p.leaves ≤ r * p.reveal :=
    Nat.le_trans (revealed_count_le sigs p.reveal p.leaves hk) (Nat.mul_le_mul_right _ hsigs)
  exact Nat.le_trans (Nat.mul_le_mul_left _
    (Nat.le_trans (coverWins_length_le p acc _) (choose_mono p.reveal hc))) h1

/-! ## 10. `SHA3_128F`: 2048 leaves, 28 revealed

The four ratios `(28 r)^(28) / 2048^(28)` are products of 28 factors each; the kernel
multiplies them out. No subset is enumerated. -/

/-- Floor of `-log2` of the forgery fraction after `r` signatures on one tree. -/
def sha3Bits : Nat → Nat
  | 1 => 209
  | 2 => 157
  | 3 => 136
  | 4 => 122
  | _ => 0

theorem sha3_128f_ff_pos :
    0 < ffTop 28 28 ∧ 0 < ffTop 56 28 ∧ 0 < ffTop 84 28 ∧ 0 < ffTop 112 28 := by
  decide +kernel

/-- The floors are exact: each ratio is at most `2^(-b)` and above `2^(-(b+1))`. -/
theorem sha3_128f_ff_bits :
    (AtLeastBits 209 (ffTop 28 28) (ffTop 2048 28) ∧
      BelowBits 210 (ffTop 28 28) (ffTop 2048 28)) ∧
    (AtLeastBits 157 (ffTop 56 28) (ffTop 2048 28) ∧
      BelowBits 158 (ffTop 56 28) (ffTop 2048 28)) ∧
    (AtLeastBits 136 (ffTop 84 28) (ffTop 2048 28) ∧
      BelowBits 137 (ffTop 84 28) (ffTop 2048 28)) ∧
    (AtLeastBits 122 (ffTop 112 28) (ffTop 2048 28) ∧
      BelowBits 123 (ffTop 112 28) (ffTop 2048 28)) := by
  unfold AtLeastBits BelowBits
  decide +kernel

/-- **Exact binomial bounds.** `C(28 r, 28) / C(2048, 28)` lies in `(2^(-(b+1)), 2^(-b)]` for
`b = 209, 157, 136, 122` at `r = 1, 2, 3, 4`. -/
theorem sha3_128f_binomial_bits :
    (AtLeastBits 209 (choose 28 28) (choose 2048 28) ∧
      BelowBits 210 (choose 28 28) (choose 2048 28)) ∧
    (AtLeastBits 157 (choose 56 28) (choose 2048 28) ∧
      BelowBits 158 (choose 56 28) (choose 2048 28)) ∧
    (AtLeastBits 136 (choose 84 28) (choose 2048 28) ∧
      BelowBits 137 (choose 84 28) (choose 2048 28)) ∧
    (AtLeastBits 122 (choose 112 28) (choose 2048 28) ∧
      BelowBits 123 (choose 112 28) (choose 2048 28)) :=
  ⟨⟨atLeastBits_choose_of_ffTop sha3_128f_ff_pos.1 sha3_128f_ff_bits.1.1,
      belowBits_choose_of_ffTop sha3_128f_ff_pos.1 sha3_128f_ff_bits.1.2⟩,
    ⟨atLeastBits_choose_of_ffTop sha3_128f_ff_pos.2.1 sha3_128f_ff_bits.2.1.1,
      belowBits_choose_of_ffTop sha3_128f_ff_pos.2.1 sha3_128f_ff_bits.2.1.2⟩,
    ⟨atLeastBits_choose_of_ffTop sha3_128f_ff_pos.2.2.1 sha3_128f_ff_bits.2.2.1.1,
      belowBits_choose_of_ffTop sha3_128f_ff_pos.2.2.1 sha3_128f_ff_bits.2.2.1.2⟩,
    ⟨atLeastBits_choose_of_ffTop sha3_128f_ff_pos.2.2.2 sha3_128f_ff_bits.2.2.2.1,
      belowBits_choose_of_ffTop sha3_128f_ff_pos.2.2.2 sha3_128f_ff_bits.2.2.2.2⟩⟩

/-- **`SHA3_128F` few-time bound.** After at most `r ∈ {1, 2, 3, 4}` signatures under one
tree, at most a `2^(-209)`, `2^(-157)`, `2^(-136)`, `2^(-122)` fraction of the subsets a
message hash can select consists of revealed leaves, under any acceptance test. -/
theorem sha3_128f_forgery_bound (acc : List Nat → Bool) (sigs : List (List Nat)) (r : Nat)
    (hk : ∀ s ∈ sigs, s.length = sha3_128f.reveal) (hsigs : sigs.length ≤ r)
    (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    AtLeastBits (sha3Bits r) (coverWins sha3_128f acc (revealedBy sigs)).length
      (subsets sha3_128f).length := by
  have hcases : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hcases with h | h | h | h
  · rw [h] at hsigs ⊢
    exact forgery_fraction_bound sha3_128f acc sigs 1 209 hk hsigs sha3_128f_ff_bits.1.1
      sha3_128f_ff_pos.1
  · rw [h] at hsigs ⊢
    exact forgery_fraction_bound sha3_128f acc sigs 2 157 hk hsigs sha3_128f_ff_bits.2.1.1
      sha3_128f_ff_pos.2.1
  · rw [h] at hsigs ⊢
    exact forgery_fraction_bound sha3_128f acc sigs 3 136 hk hsigs sha3_128f_ff_bits.2.2.1.1
      sha3_128f_ff_pos.2.2.1
  · rw [h] at hsigs ⊢
    exact forgery_fraction_bound sha3_128f acc sigs 4 122 hk hsigs sha3_128f_ff_bits.2.2.2.1
      sha3_128f_ff_pos.2.2.2

/-- `m` is the floor of `1000 * log2 (den / num)`. -/
def MilliFloor (m num den : Nat) : Prop :=
  2 ^ m * num ^ 1000 ≤ den ^ 1000 ∧ den ^ 1000 < 2 ^ (m + 1) * num ^ 1000

/-- `1000 * log2 (den / num) ≥ m`. -/
def MilliAtLeast (m num den : Nat) : Prop := 2 ^ m * num ^ 1000 ≤ den ^ 1000

/-- The four values to a thousandth of a bit: 209.788, 157.024, 136.093, 122.451. -/
theorem sha3_128f_millibits :
    MilliFloor 209788 (ffTop 28 28) (ffTop 2048 28) ∧
    MilliFloor 157024 (ffTop 56 28) (ffTop 2048 28) ∧
    MilliFloor 136093 (ffTop 84 28) (ffTop 2048 28) ∧
    MilliFloor 122451 (ffTop 112 28) (ffTop 2048 28) := by
  unfold MilliFloor
  decide +kernel

/-! ### The Rust estimate `forgery_bits_milli`

A transcription over `Nat`. The Rust code works in `u64`/`u128`; the squaring stays below
`2^128` because the mantissa stays below `2^64`, which is not proved here. -/

def log2Loop : Nat → Nat → Nat → Nat
  | 0, _, frac => frac
  | n + 1, y, frac =>
    if ((y * y) >>> 63) >>> 64 ≠ 0 then log2Loop n (((y * y) >>> 63) >>> 1) (2 * frac + 1)
    else log2Loop n ((y * y) >>> 63) (2 * frac)

/-- `log2_milli_floor`. -/
def log2MilliFloor (x : Nat) : Nat :=
  1000 * x.log2 + ((1000 * log2Loop 20 (x <<< (63 - x.log2)) 0) >>> 20)

/-- `PorsFpParams::forgery_bits_milli`. -/
def forgeryBitsMilli (p : Params) (signatures : Nat) : Option Nat :=
  if p.wellFormed && !decide (signatures = 0) then
    some ((List.range p.reveal).foldl (fun bits i =>
      bits + (log2MilliFloor (p.leaves - i) -
        (log2MilliFloor (min (p.reveal * signatures) p.leaves - i) +
          if 2 ^ (min (p.reveal * signatures) p.leaves - i).log2 =
            min (p.reveal * signatures) p.leaves - i then 0 else 1))) 0)
  else none

/-- What the deployed function returns at `SHA3_128F`. -/
theorem sha3_128f_rust_estimate :
    forgeryBitsMilli sha3_128f 1 = some 209767 ∧ forgeryBitsMilli sha3_128f 2 = some 156999 ∧
    forgeryBitsMilli sha3_128f 3 = some 136068 ∧ forgeryBitsMilli sha3_128f 4 = some 122425 := by
  decide +kernel

/-- Those four values are true lower bounds (each within 26 thousandths of a bit). -/
theorem sha3_128f_rust_estimate_sound :
    MilliAtLeast 209767 (ffTop 28 28) (ffTop 2048 28) ∧
    MilliAtLeast 156999 (ffTop 56 28) (ffTop 2048 28) ∧
    MilliAtLeast 136068 (ffTop 84 28) (ffTop 2048 28) ∧
    MilliAtLeast 122425 (ffTop 112 28) (ffTop 2048 28) := by
  unfold MilliAtLeast
  decide +kernel

/-- Distinctness is what the bound rests on: if a repeated index were accepted, covering
would cost `(28 / 2048)^28`, and 209 bits would not hold even after one signature. -/
theorem sha3_128f_bound_fails_without_distinctness : ¬ AtLeastBits 209 (28 ^ 28) (2048 ^ 28) := by
  unfold AtLeastBits
  decide +kernel

/-! ## 11. Test vectors, a worked instance and a mutated verifier -/

theorem sha3_128f_wellFormed :
    sha3_128f.wellFormed = true ∧ testSmall.wellFormed = true ∧
      sha3_128f.openingBytesMax = 4994 := by decide

/-- The vectors of the Rust test `octopus_is_minimal_and_matches_a_brute_force_cover`. -/
theorem octopus_vectors :
    octopusPositions 3 [0, 1, 6] = some [(0, 7), (1, 1), (1, 2)] ∧
    octopusPositions 3 [0, 1, 2, 3, 4, 5, 6, 7] = some [] ∧
    octopusPositions 3 [5] = some [(0, 4), (1, 3), (2, 0)] ∧
    octopusPositions 3 [] = none ∧ octopusPositions 3 [1, 1] = none ∧
    octopusPositions 3 [2, 1] = none ∧ octopusPositions 3 [8] = none := by decide

/-- A hash that records its inputs: collision-free by construction. -/
inductive DemoNode where
  | leaf (i s : Nat)
  | node (l i : Nat) (a b : DemoNode)
  deriving DecidableEq

def demoSuite : HashSuite Nat DemoNode := ⟨DemoNode.leaf, DemoNode.node⟩

def demoParams : Params := ⟨2, 2, 4⟩

def demoSecret (i : Nat) : Nat := 7 + i

def demoRoot : DemoNode := honestTree demoSuite demoSecret 2 0

def demoIdx : List Nat := [0, 2]

theorem demo_wellFormed : demoParams.wellFormed = true := by decide

theorem demo_admissible : Admissible demoParams demoIdx :=
  ⟨(strictIncB_iff _).mp (by decide), by decide, by decide, by decide⟩

theorem demo_honest_opening_accepted :
    porsFpRoot demoParams demoSuite demoIdx (demoIdx.map demoSecret)
      (honestAuth demoSuite demoSecret demoParams.treeHeight demoIdx) = some demoRoot :=
  porsFpRoot_complete demoParams demoSuite demoSecret demoIdx demo_wellFormed demo_admissible

/-- The same subset under a pruning bound of one node: the honest opening is refused. -/
theorem demo_pruned_opening_rejected :
    porsFpRoot ⟨2, 2, 1⟩ demoSuite demoIdx (demoIdx.map demoSecret)
      (honestAuth demoSuite demoSecret 2 demoIdx) = none := by rfl

def headerOkLax (p : Params) (idx : List Nat) (secretsLen authLen : Nat) : Bool :=
  p.wellFormed && decide (idx.length = p.reveal) && decide (secretsLen = p.reveal) &&
    decide (authLen ≤ p.maxAuthNodes) && decide (idx.getLast?.getD 0 < p.leaves)

def topOfLax : Option (List D × List D) → Option D
  | some (r :: _, []) => some r
  | _ => none

/-- `pors_fp_root` without the strict-order test and reading the root from the first top
node instead of demanding exactly one. Dropping the order test alone accepts nothing new on
the instances tried here, because unsorted input leaves more than one top node; both
changes together do. -/
def porsFpRootLax (p : Params) (suite : HashSuite S D) (idx : List Nat) (secrets : List S)
    (auth : List D) : Option D :=
  if headerOkLax p idx secrets.length auth.length then
    topOfLax (climb suite.node p.treeHeight 0 idx (List.zipWith suite.leaf idx secrets) auth)
  else none

def demoUnsortedIdx : List Nat := [2, 0]

def demoJunk : DemoNode := DemoNode.leaf 0 0

/-- Leaf 2 is opened honestly; the entry for leaf 0 carries a wrong secret and junk nodes. -/
def demoUnsortedSecrets : List Nat := [9, 99]

def demoUnsortedAuth : List DemoNode :=
  [honestTree demoSuite demoSecret 0 3, demoJunk, honestTree demoSuite demoSecret 1 0, demoJunk]

theorem demo_unsorted_rejected :
    porsFpRoot demoParams demoSuite demoUnsortedIdx demoUnsortedSecrets demoUnsortedAuth =
      none := by rfl

theorem demo_unsorted_accepted_by_lax :
    porsFpRootLax demoParams demoSuite demoUnsortedIdx demoUnsortedSecrets demoUnsortedAuth =
      some demoRoot := by rfl

theorem demo_duplicate_rejected :
    porsFpRoot demoParams demoSuite [2, 2] [9, 9] demoUnsortedAuth = none := by rfl

theorem demo_duplicate_accepted_by_lax :
    porsFpRootLax demoParams demoSuite [2, 2] [9, 9]
      [honestTree demoSuite demoSecret 0 3, honestTree demoSuite demoSecret 0 3,
        honestTree demoSuite demoSecret 1 0, honestTree demoSuite demoSecret 1 0] =
      some demoRoot := by rfl

/-- A suite with a constant hash: every opening of the right shape gives the same root. -/
def demoCollidingSuite : HashSuite Nat Nat := ⟨fun _ _ => 0, fun _ _ _ _ => 0⟩

theorem demo_colliding_opening_a :
    porsFpRoot demoParams demoCollidingSuite demoIdx [1, 2] [0, 0] = some 0 := by rfl

theorem demo_colliding_opening_b :
    porsFpRoot demoParams demoCollidingSuite demoIdx [3, 4] [0, 0] = some 0 := by rfl

def demoSigs : List (List Nat) := [List.range 28]

theorem demo_sigs_uniform : ∀ s ∈ demoSigs, s.length = sha3_128f.reveal := by decide

theorem demo_sigs_count : demoSigs.length ≤ 1 := by decide

theorem sha3_128f_ff_bits_one :
    AtLeastBits 209 (ffTop (1 * sha3_128f.reveal) sha3_128f.reveal)
      (ffTop sha3_128f.leaves sha3_128f.reveal) := sha3_128f_ff_bits.1.1

theorem sha3_128f_ff_pos_one : 0 < ffTop (1 * sha3_128f.reveal) sha3_128f.reveal :=
  sha3_128f_ff_pos.1

#verify_constructive porsFpRoot_some_shape unsorted_rejected oversized_rejected
  noncanonical_length_rejected porsFpRoot_complete porsFpRoot_binding
  opening_against_honest_root select_admissible selected_subset_opens mem_subsetsFrom
  nodup_subsetsFrom covered_subsets_count choose_mono choose_cross
  atLeastBits_choose_of_ffTop belowBits_choose_of_ffTop revealed_count_le admissible_iff
  coverWins_length_le forgery_fraction_bound sha3_128f_ff_bits sha3_128f_binomial_bits
  sha3_128f_forgery_bound sha3_128f_millibits sha3_128f_rust_estimate
  sha3_128f_rust_estimate_sound sha3_128f_bound_fails_without_distinctness
  demo_honest_opening_accepted demo_unsorted_rejected demo_unsorted_accepted_by_lax

end Qsag.PorsFpSecurity
