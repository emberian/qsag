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

public import Qsag.Spec.Parameters
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HypertreeEufCma
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

/-! ## 12. `PorsFpOpening` Wire Codec, `AdrsKind.porsPrf`/`porsTree`, and `BaggySha3_128f` Hypertree EUF-CMA

Connects `PORS+FP` directly to `HashSigs` (`AdrsKind.porsPrf = 7`, `AdrsKind.porsTree = 8`),
`crates/qsag-core/src/pors_fp.rs:189-265`, and `crates/qsag-core/src/baggy.rs`:
1. `porsAdrs`, `porsPrfAdrs`, `porsLeafAdrs`, `porsNodeAdrs`, and `porsTweakableSuite` with
   domain-separation from all WOTS+C / XMSS / FORS address roles and collision lifting to
   `HashCollisionWitness suite.rawHash`.
2. `PorsFpOpening` canonical wire codec (`secrets || be 2 auth.length || auth`), prefix-free
   round-trip `PorsFpOpening.fromWireBytes_toWireBytes_append`, and `≤ 4,994 B` bound at `sha3_128f`.
3. `BaggyParams`, `BaggySha3_128f` (`d = 16, h' = 2`, `PORS+FP` `sha3_128f` bottom + 16 `WOTS+C`
   layers, `TAG_BAGGY_HMSG = "QSAG.BAGGY.HMSG/v2"`), `BaggySig` wire codec round-trip, and exact
   worst-case wire byte bound `≤ 71,654 B` matching `Spec.baggySha3_128fProfile.maxSigBytes`.
4. Executable `baggyVerify`, path-completeness `baggyHonestPathNode_top`, and constructive
   (`0 Classical.choice`) multi-query hypertree-over-`PORS+FP` EUF-CMA reduction (`extractBaggyForgery`,
   `baggy_sha3_128f_multi_query_euf_cma_reduction`, `baggy_sha3_128f_euf_cma_gameBound`). -/

/-- `pors_adrs` (`crates/qsag-core/src/pors_fp.rs:229-238`). -/
def porsAdrs (kind : AdrsKind) (tree : UInt64) (keyPair height index : UInt32) : HashAdrs :=
  ⟨0, tree, kind, keyPair, height, index⟩

/-- `pors_prf_adrs` (`AdrsKind::PorsPrf = 7`, `pors_fp.rs:241-243`). -/
def porsPrfAdrs (tree : UInt64) (keyPair leaf : UInt32) : HashAdrs :=
  porsAdrs .porsPrf tree keyPair 0 leaf

/-- `pors_leaf_adrs` (`AdrsKind::PorsTree = 8`, `pors_fp.rs:246-248`). -/
def porsLeafAdrs (tree : UInt64) (keyPair leaf : UInt32) : HashAdrs :=
  porsAdrs .porsTree tree keyPair 0 leaf

/-- Internal node address at height `height ≥ 1` (`AdrsKind::PorsTree = 8`, `pors_fp.rs:273`). -/
def porsNodeAdrs (tree : UInt64) (keyPair height index : UInt32) : HashAdrs :=
  porsAdrs .porsTree tree keyPair height index

theorem porsPrfAdrs_encode_ne_porsLeafAdrs (t₁ t₂ : UInt64) (kp₁ l₁ kp₂ l₂ : UInt32) :
    encodeAdrs (porsPrfAdrs t₁ kp₁ l₁) ≠ encodeAdrs (porsLeafAdrs t₂ kp₂ l₂) := by
  intro hEq
  have hKind := congrArg HashAdrs.kind (encodeAdrs_injective hEq)
  nomatch hKind

theorem porsPrfAdrs_eq (tree : UInt64) (keyPair leaf : UInt32) :
    porsPrfAdrs tree keyPair leaf = ⟨0, tree, .porsPrf, keyPair, 0, leaf⟩ := by
  (conv => lhs; unfold porsPrfAdrs) <;> rfl

theorem porsLeafAdrs_eq (tree : UInt64) (keyPair leaf : UInt32) :
    porsLeafAdrs tree keyPair leaf = ⟨0, tree, .porsTree, keyPair, 0, leaf⟩ := by
  (conv => lhs; unfold porsLeafAdrs) <;> rfl

theorem honestTree_succ (suite : HashSuite S D) (sec : Nat → S) (l i : Nat) :
    honestTree suite sec (l + 1) i =
      suite.node (l + 1) i (honestTree suite sec l (2 * i)) (honestTree suite sec l (2 * i + 1)) := by
  (conv => lhs; unfold honestTree) <;> rfl

theorem select_range28_sha3_128f :
    select sha3_128f (List.range 28) = some (List.range 28) := by
  decide

theorem sha3_128f_eq : sha3_128f = ⟨11, 28, 128⟩ := by unfold sha3_128f; rfl

theorem porsAdrs_encode_disjoint_from_nonPors (kind : AdrsKind)
    (hPors : kind = .porsPrf ∨ kind = .porsTree)
    (t : UInt64) (kp h idx : UInt32) (other : HashAdrs)
    (hOther : other.kind ≠ .porsPrf ∧ other.kind ≠ .porsTree) :
    encodeAdrs (porsAdrs kind t kp h idx) ≠ encodeAdrs other := by
  intro hEq
  have hK := congrArg HashAdrs.kind (encodeAdrs_injective hEq)
  dsimp only [porsAdrs] at hK
  rcases hPors with rfl | rfl
  · exact hOther.1 hK.symm
  · exact hOther.2 hK.symm

/-- Secret derivation for leaf `i` of `PORS+FP` instance `(tree, keyPair)` (`AdrsKind.porsPrf`). -/
def porsSecretLeaf (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree : UInt64) (keyPair : UInt32) (i : Nat) : List UInt8 :=
  thSecretPrf suite sk.pkSeed sk.skSeed (porsPrfAdrs tree keyPair (UInt32.ofNat i))

/-- Concrete `PORS+FP` `HashSuite` instantiated over `TweakableHashSuite` (`pors_fp.rs:251-274`). -/
def porsTweakableSuite (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (tree : UInt64) (keyPair : UInt32) : HashSuite (List UInt8) (List UInt8) where
  leaf i sec := thChainF suite pkSeed (porsLeafAdrs tree keyPair (UInt32.ofNat i)) sec
  node lvl idx l r :=
    thNodeH suite pkSeed (porsNodeAdrs tree keyPair (UInt32.ofNat lvl) (UInt32.ofNat idx)) l r

theorem porsTweakableSuite_honestTree_length (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (tree : UInt64) (keyPair : UInt32) (sec : Nat → List UInt8) :
    ∀ (lvl idx : Nat),
      (honestTree (porsTweakableSuite suite pkSeed tree keyPair) sec lvl idx).length = 32
  | 0, idx => by
    show (thChainF suite pkSeed (porsLeafAdrs tree keyPair (UInt32.ofNat idx)) (sec idx)).length = 32
    rw [thChainF_eq]
    exact thCall_length suite _ _ _ _
  | lvl + 1, idx => by
    show (thNodeH suite pkSeed
      (porsNodeAdrs tree keyPair (UInt32.ofNat (lvl + 1)) (UInt32.ofNat idx)) _ _).length = 32
    rw [thNodeH_eq]
    exact thCall_length suite _ _ _ _

/-- Constructive collision lift: any leaf or node collision in `porsTweakableSuite` yields a
    concrete `HashCollisionWitness suite.rawHash`. -/
def liftPorsLeafCollision (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (tree : UInt64) (keyPair : UInt32) (i : Nat) {s s' : List UInt8}
    (hNe : s ≠ s')
    (hEq : (porsTweakableSuite suite pkSeed tree keyPair).leaf i s =
      (porsTweakableSuite suite pkSeed tree keyPair).leaf i s') :
    HashCollisionWitness suite.rawHash := by
  dsimp only [porsTweakableSuite] at hEq
  rw [thChainF_eq, thChainF_eq] at hEq
  exact match thCall_binds_or_collision suite hEq with
    | .inl ⟨_, _, _, hArgs⟩ => False.elim (hNe (List.cons.inj hArgs).1)
    | .inr col => col

def liftPorsNodeCollision (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (tree : UInt64) (keyPair : UInt32) (lvl idx : Nat) {a b a' b' : List UInt8}
    (hNe : a ≠ a' ∨ b ≠ b')
    (hEq : (porsTweakableSuite suite pkSeed tree keyPair).node lvl idx a b =
      (porsTweakableSuite suite pkSeed tree keyPair).node lvl idx a' b') :
    HashCollisionWitness suite.rawHash := by
  dsimp only [porsTweakableSuite] at hEq
  rw [thNodeH_eq, thNodeH_eq] at hEq
  exact match thCall_binds_or_collision suite hEq with
    | .inl ⟨_, _, _, hArgs⟩ => False.elim (by
        have h1 := (List.cons.inj hArgs).1
        have h2 := (List.cons.inj (List.cons.inj hArgs).2).1
        exact hNe.elim (fun ha => ha h1) (fun hb => hb h2))
    | .inr col => col

/-! ### 12.1 `PorsFpOpening` Wire Codec (`secrets || be 2 auth.length || auth`) -/

/-- Split the leading `32 * k` bytes of `bs` into `k` 32-byte chunks. -/
def takeChunks32 : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | k + 1, bs => bs.take 32 :: takeChunks32 k (bs.drop 32)

private theorem flatten_length_32 :
    ∀ (xs : List (List UInt8)), (∀ x ∈ xs, x.length = 32) → xs.flatten.length = 32 * xs.length
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.flatten_cons, List.length_append, h x List.mem_cons_self,
      flatten_length_32 xs (fun y hy => h y (List.mem_cons_of_mem _ hy)), List.length_cons]
    omega

private theorem take_append_exact {α : Type} :
    ∀ (xs rest : List α) (n : Nat), xs.length = n → (xs ++ rest).take n = xs ∧ (xs ++ rest).drop n = rest
  | [], rest, 0, _ => ⟨rfl, rfl⟩
  | [], _, _ + 1, h => nomatch h
  | _ :: _, _, 0, h => nomatch h
  | x :: xs, rest, n + 1, h => by
    obtain ⟨hT, hD⟩ := take_append_exact xs rest n (Nat.succ.inj h)
    exact ⟨congrArg (x :: ·) hT, hD⟩

private theorem takeChunks32_flatten :
    ∀ (xs : List (List UInt8)), (∀ x ∈ xs, x.length = 32) → ∀ (rest : List UInt8),
      takeChunks32 xs.length (xs.flatten ++ rest) = xs ∧
      (xs.flatten ++ rest).drop (32 * xs.length) = rest
  | [], _, rest => ⟨rfl, rfl⟩
  | x :: xs, h, rest => by
    have hx := h x List.mem_cons_self
    have hxs : ∀ y ∈ xs, y.length = 32 := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.flatten_cons, List.append_assoc, List.length_cons]
    obtain ⟨hTakeX, hDropX⟩ := take_append_exact x (xs.flatten ++ rest) 32 hx
    obtain ⟨ihChunks, ihDrop⟩ := takeChunks32_flatten xs hxs rest
    refine ⟨?_, ?_⟩
    · show (x ++ (xs.flatten ++ rest)).take 32 ::
        takeChunks32 xs.length ((x ++ (xs.flatten ++ rest)).drop 32) = x :: xs
      rw [hTakeX, hDropX, ihChunks]
    · have hMul : 32 * (xs.length + 1) = 32 + 32 * xs.length := by omega
      rw [hMul, ← List.drop_drop, hDropX, ihDrop]

private theorem takeChunks32_shape :
    ∀ (k : Nat) (bs : List UInt8), 32 * k ≤ bs.length →
      (takeChunks32 k bs).length = k ∧
      (∀ c ∈ takeChunks32 k bs, c.length = 32) ∧
      (takeChunks32 k bs).flatten = bs.take (32 * k)
  | 0, bs, _ => by
    refine ⟨rfl, ?_, ?_⟩
    · intro c h; nomatch h
    · simp [takeChunks32]
  | k + 1, bs, hLe => by
    have h32 : 32 ≤ bs.length := by omega
    have hDrop : 32 * k ≤ (bs.drop 32).length := by rw [List.length_drop]; omega
    obtain ⟨ihL, ihAll, ihFlat⟩ := takeChunks32_shape k (bs.drop 32) hDrop
    refine ⟨congrArg Nat.succ ihL, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hTl
      · exact List.length_take_of_le h32
      · exact ihAll c hTl
    · show bs.take 32 ++ (takeChunks32 k (bs.drop 32)).flatten = bs.take (32 * (k + 1))
      rw [ihFlat]
      have hMul : 32 * (k + 1) = 32 + 32 * k := by omega
      rw [hMul]
      clear ihL ihAll ihFlat hLe h32 hDrop
      suffices ∀ (a b : Nat) (l : List UInt8), l.take a ++ (l.drop a).take b = l.take (a + b) from
        this 32 (32 * k) bs
      intro a
      induction a with
      | zero => intro b l; rw [Nat.zero_add]; rfl
      | succ a ihA =>
        intro b l
        cases l with
        | nil => simp
        | cons hd tl =>
          rw [Nat.succ_add]
          exact congrArg (hd :: ·) (ihA b tl)

/-- Revealed leaf secrets and canonical multiproof (`crates/qsag-core/src/pors_fp.rs:189-192`). -/
structure PorsFpOpening where
  secrets : List (List UInt8)
  auth : List (List UInt8)
  deriving DecidableEq, Repr

/-- Shape predicate for a serializable `PorsFpOpening` under `p : Params`. -/
@[expose] def PorsFpOpening.WellShaped (p : Params) (o : PorsFpOpening) : Prop :=
  o.secrets.length = p.reveal ∧
  (∀ s ∈ o.secrets, s.length = 32) ∧
  o.auth.length ≤ p.maxAuthNodes ∧
  (∀ a ∈ o.auth, a.length = 32)

/-- `PorsFpOpening::to_wire_bytes` (`secrets || be16(auth.len()) || auth`, `pors_fp.rs:196-202`). -/
@[expose] def PorsFpOpening.toWireBytes (o : PorsFpOpening) : List UInt8 :=
  o.secrets.flatten ++ be 2 o.auth.length ++ o.auth.flatten

/-- `PorsFpOpening::from_wire_bytes` (`pors_fp.rs:206-226`). -/
def PorsFpOpening.fromWireBytes (p : Params) (raw : List UInt8) : Option (PorsFpOpening × Nat) :=
  if !p.wellFormed then none
  else
    let secretBytes := 32 * p.reveal
    if raw.length < secretBytes + 2 then none
    else
      let count := ofBE ((raw.drop secretBytes).take 2)
      if p.maxAuthNodes < count then none
      else
        let used := secretBytes + 2 + 32 * count
        if raw.length < used then none
        else
          some (⟨takeChunks32 p.reveal (raw.take secretBytes),
                 takeChunks32 count ((raw.drop (secretBytes + 2)).take (32 * count))⟩, used)

theorem PorsFpOpening.toWireBytes_length (p : Params) (o : PorsFpOpening)
    (hShape : o.WellShaped p) :
    o.toWireBytes.length = 32 * p.reveal + 2 + 32 * o.auth.length ∧
    o.toWireBytes.length ≤ p.openingBytesMax := by
  obtain ⟨hSL, hS32, hAL, hA32⟩ := hShape
  unfold PorsFpOpening.toWireBytes Params.openingBytesMax
  rw [List.length_append, List.length_append, flatten_length_32 _ hS32, hSL,
    length_be, flatten_length_32 _ hA32]
  exact ⟨rfl, by omega⟩

theorem sha3_128f_opening_wire_le_4994 (o : PorsFpOpening) (hShape : o.WellShaped sha3_128f) :
    o.toWireBytes.length ≤ 4994 :=
  (o.toWireBytes_length sha3_128f hShape).2

private theorem maxAuthNodes_lt_65536 (p : Params) (hw : p.wellFormed = true) :
    p.maxAuthNodes < 256 ^ 2 := by
  simp only [Params.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  have h1 : p.treeHeight ≤ 20 := hw.1.1.1.1.1.2
  have h2 : p.reveal ≤ 1024 := hw.1.1.1.2
  have h3 : p.maxAuthNodes ≤ p.reveal * p.treeHeight := hw.2
  have hProd : p.reveal * p.treeHeight ≤ 1024 * 20 := Nat.mul_le_mul h2 h1
  omega

/-- **Prefix-Free Round-Trip for `PorsFpOpening` (`fromWireBytes_toWireBytes_append`).** -/
theorem PorsFpOpening.fromWireBytes_toWireBytes_append (p : Params) (hw : p.wellFormed = true)
    (o : PorsFpOpening) (hShape : o.WellShaped p) (rest : List UInt8) :
    PorsFpOpening.fromWireBytes p (o.toWireBytes ++ rest) = some (o, o.toWireBytes.length) := by
  obtain ⟨hSL, hS32, hAL, hA32⟩ := hShape
  have hSecLen : o.secrets.flatten.length = 32 * p.reveal :=
    (flatten_length_32 _ hS32).trans (congrArg (32 * ·) hSL)
  have hAuthLen : o.auth.flatten.length = 32 * o.auth.length := flatten_length_32 _ hA32
  have hWireLen := (o.toWireBytes_length p ⟨hSL, hS32, hAL, hA32⟩).1
  have hCntLt : o.auth.length < 256 ^ 2 := Nat.lt_of_le_of_lt hAL (maxAuthNodes_lt_65536 p hw)
  unfold PorsFpOpening.fromWireBytes
  rw [hw]
  dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hRawEq : o.toWireBytes ++ rest =
      o.secrets.flatten ++ (be 2 o.auth.length ++ (o.auth.flatten ++ rest)) := by
    unfold PorsFpOpening.toWireBytes
    simp only [List.append_assoc]
  have hLen1 : ¬ (o.toWireBytes ++ rest).length < 32 * p.reveal + 2 := by
    rw [List.length_append, hWireLen]; omega
  rw [ite_eq_right hLen1]
  obtain ⟨hTakeSec, hDropSec⟩ :=
    take_append_exact o.secrets.flatten (be 2 o.auth.length ++ (o.auth.flatten ++ rest))
      (32 * p.reveal) hSecLen
  obtain ⟨hTakeCnt, hDropCnt⟩ :=
    take_append_exact (be 2 o.auth.length) (o.auth.flatten ++ rest) 2 (length_be 2 _)
  have hDrop1 : (o.toWireBytes ++ rest).drop (32 * p.reveal) =
      be 2 o.auth.length ++ (o.auth.flatten ++ rest) := by
    rw [hRawEq]; exact hDropSec
  have hCountEq : ofBE (((o.toWireBytes ++ rest).drop (32 * p.reveal)).take 2) = o.auth.length := by
    rw [hDrop1, hTakeCnt, ofBE_be hCntLt]
  rw [hCountEq, ite_eq_right (Nat.not_lt_of_ge hAL)]
  have hLen2 : ¬ (o.toWireBytes ++ rest).length < 32 * p.reveal + 2 + 32 * o.auth.length := by
    rw [List.length_append, hWireLen]; omega
  rw [ite_eq_right hLen2]
  have hDrop2 : (o.toWireBytes ++ rest).drop (32 * p.reveal + 2) = o.auth.flatten ++ rest := by
    rw [← List.drop_drop, hDrop1, hDropCnt]
  obtain ⟨hTakeAuth, _⟩ := take_append_exact o.auth.flatten rest (32 * o.auth.length) hAuthLen
  have hSecChunks : takeChunks32 p.reveal ((o.toWireBytes ++ rest).take (32 * p.reveal)) =
      o.secrets := by
    rw [hRawEq, hTakeSec, ← hSL]
    have h := (takeChunks32_flatten o.secrets hS32 []).1
    rwa [List.append_nil] at h
  have hAuthChunks : takeChunks32 o.auth.length
      (((o.toWireBytes ++ rest).drop (32 * p.reveal + 2)).take (32 * o.auth.length)) = o.auth := by
    rw [hDrop2, hTakeAuth]
    have h := (takeChunks32_flatten o.auth hA32 []).1
    rwa [List.append_nil] at h
  rw [hSecChunks, hAuthChunks, hWireLen]
  cases o; rfl

theorem PorsFpOpening.toWireBytes_prefix_injective (p : Params) (hw : p.wellFormed = true)
    {o₁ o₂ : PorsFpOpening} (h₁ : o₁.WellShaped p) (h₂ : o₂.WellShaped p)
    {rest₁ rest₂ : List UInt8}
    (hEq : o₁.toWireBytes ++ rest₁ = o₂.toWireBytes ++ rest₂) :
    o₁ = o₂ ∧ rest₁ = rest₂ := by
  have hDec := congrArg (PorsFpOpening.fromWireBytes p) hEq
  rw [o₁.fromWireBytes_toWireBytes_append p hw h₁ rest₁,
      o₂.fromWireBytes_toWireBytes_append p hw h₂ rest₂] at hDec
  injection hDec with hPair
  obtain ⟨rfl, _⟩ := Prod.mk.inj hPair
  exact ⟨rfl, List.append_cancel_left hEq⟩

/-! ### 12.2 `Baggy` Role Tags, `BaggySha3_128f` Parameters & `BaggySig` `≤ 71,654 B` Wire Codec -/

def tagBaggyOptRand : List UInt8 := "QSAG.BAGGY.OPTRAND/v1".toUTF8.toList
def tagBaggyR       : List UInt8 := "QSAG.BAGGY.R/v1".toUTF8.toList
/-- Message hash XOF tag of the `PORS+FP` `Baggy` suite (`baggy.rs:110`). -/
def TAG_BAGGY_HMSG  : List UInt8 := "QSAG.BAGGY.HMSG/v2".toUTF8.toList
abbrev tagBaggyHmsg : List UInt8 := TAG_BAGGY_HMSG
def tagBaggyDigest  : List UInt8 := "QSAG.BAGGY.DIGEST/v1".toUTF8.toList
def tagBaggyParams  : List UInt8 := "QSAG.BAGGY.PARAMS/v1".toUTF8.toList
def tagBaggyKeyId   : List UInt8 := "QSAG.BAGGY.KEYID/v1".toUTF8.toList

theorem tag_baggy_hmsg_eq : TAG_BAGGY_HMSG = "QSAG.BAGGY.HMSG/v2".toUTF8.toList := by
  (conv => lhs; unfold TAG_BAGGY_HMSG) <;> rfl

/-- `WotsCParams` (`crates/qsag-core/src/wots_c.rs:44-70`). -/
structure WotsCParams where
  chains : Nat
  zeroDigits : Nat
  targetSum : Nat
  deriving DecidableEq, Repr

def WotsCParams.v128 : WotsCParams := ⟨128, 0, 192⟩

def WotsCParams.wellFormed (w : WotsCParams) : Bool :=
  decide (w = WotsCParams.v128)

/-- `BaggyParams` (`crates/qsag-core/src/baggy.rs:131-140`). -/
structure BaggyParams where
  wots : WotsCParams
  subtreeHeight : Nat
  numLayers : Nat
  maxGrind : Nat
  pors : Params

def BaggyParams.totalHeight (bp : BaggyParams) : Nat :=
  bp.subtreeHeight * bp.numLayers

def BaggyParams.wellFormed (bp : BaggyParams) : Bool :=
  bp.wots.wellFormed &&
  decide (1 ≤ bp.subtreeHeight) && decide (bp.subtreeHeight ≤ 8) &&
  decide (1 ≤ bp.numLayers) && decide (bp.numLayers ≤ 62) &&
  decide (bp.totalHeight ≤ 62) &&
  decide (bp.maxGrind ≤ 2 ^ 32) && decide (0 < bp.maxGrind) &&
  bp.pors.wellFormed

/-- Exact worst-case signature byte bound `BaggyParams::sig_bytes_checked` (`baggy.rs:189-213`). -/
def BaggyParams.sigBytesMax (bp : BaggyParams) : Nat :=
  36 + bp.pors.openingBytesMax +
    bp.numLayers * (4 + 32 * bp.wots.chains + 32 * bp.subtreeHeight)

/-- `BaggyParams::path_at` (`baggy.rs:259-265`): `(keyPair, tree)` at `layer`. -/
@[expose] def BaggyParams.pathAt (bp : BaggyParams) (leafIdx layer : Nat) : UInt32 × UInt64 :=
  let shifted := leafIdx / 2 ^ (bp.subtreeHeight * layer)
  (UInt32.ofNat (shifted % 2 ^ bp.subtreeHeight), UInt64.ofNat (shifted / 2 ^ bp.subtreeHeight))

/-- **`BaggyParams::SHA3_128F`** (`baggy.rs:145-151`): `d = 16, h' = 2`, `WOTS+C` `V128`,
    `max_grind = 2^26`, `PORS+FP` `SHA3_128F` (`h = 11, k = 28, m = 128`), max `71,654` bytes. -/
@[expose] def BaggySha3_128f : BaggyParams where
  wots := WotsCParams.v128
  subtreeHeight := 2
  numLayers := 16
  maxGrind := 2 ^ 26
  pors := sha3_128f

abbrev BaggyParams.sha3_128f : BaggyParams := BaggySha3_128f

def BaggyParams.testSmall : BaggyParams where
  wots := WotsCParams.v128
  subtreeHeight := 2
  numLayers := 3
  maxGrind := 2 ^ 26
  pors := Qsag.PorsFpSecurity.testSmall

theorem baggySha3_128f_parity :
    BaggySha3_128f.wellFormed = true ∧
    BaggySha3_128f.totalHeight = 32 ∧
    BaggySha3_128f.sigBytesMax = 71654 ∧
    BaggySha3_128f.sigBytesMax = Spec.baggySha3_128fProfile.maxSigBytes ∧
    BaggyParams.testSmall.wellFormed = true := by
  rw [Spec.baggySha3_128fProfile_maxSigBytes]
  decide

/-- One hypertree layer signature (`BaggyLayerSig`, `baggy.rs:571-575`). -/
structure BaggyLayerSig where
  ctr : Nat
  chains : List (List UInt8)
  auth : List (List UInt8)
  deriving DecidableEq, Repr

@[expose] def BaggyLayerSig.WellShaped (bp : BaggyParams) (l : BaggyLayerSig) : Prop :=
  l.ctr < bp.maxGrind ∧
  l.chains.length = bp.wots.chains ∧
  (∀ c ∈ l.chains, c.length = 32) ∧
  l.auth.length = bp.subtreeHeight ∧
  (∀ a ∈ l.auth, a.length = 32)

def BaggyLayerSig.toWireBytes (l : BaggyLayerSig) : List UInt8 :=
  be 4 l.ctr ++ l.chains.flatten ++ l.auth.flatten

/-- Full `Baggy` signature (`BaggySig`, `baggy.rs:579-585`). -/
structure BaggySig where
  r : List UInt8
  msgCtr : Nat
  pors : PorsFpOpening
  layers : List BaggyLayerSig
  deriving DecidableEq, Repr

@[expose] def BaggySig.WellShaped (bp : BaggyParams) (sig : BaggySig) : Prop :=
  sig.r.length = 32 ∧
  sig.msgCtr < bp.maxGrind ∧
  sig.pors.WellShaped bp.pors ∧
  sig.layers.length = bp.numLayers ∧
  (∀ l ∈ sig.layers, l.WellShaped bp)

/-- `BaggySig::to_wire_bytes` (`r || be32(msg_ctr) || pors || layers`, `baggy.rs:590-601`). -/
@[expose] def BaggySig.toWireBytes (sig : BaggySig) : List UInt8 :=
  sig.r ++ be 4 sig.msgCtr ++ sig.pors.toWireBytes ++
    (sig.layers.map BaggyLayerSig.toWireBytes).flatten

private def parseBaggyLayers (bp : BaggyParams) :
    Nat → List UInt8 → Option (List BaggyLayerSig × List UInt8)
  | 0, rest => some ([], rest)
  | n + 1, rest =>
    let layerBytes := 4 + 32 * bp.wots.chains + 32 * bp.subtreeHeight
    if rest.length < layerBytes then none
    else
      let ctr := ofBE (rest.take 4)
      if bp.maxGrind ≤ ctr then none
      else
        let chains := takeChunks32 bp.wots.chains ((rest.drop 4).take (32 * bp.wots.chains))
        let auth := takeChunks32 bp.subtreeHeight
          ((rest.drop (4 + 32 * bp.wots.chains)).take (32 * bp.subtreeHeight))
        match parseBaggyLayers bp n (rest.drop layerBytes) with
        | none => none
        | some (ls, rem) => some (⟨ctr, chains, auth⟩ :: ls, rem)

/-- `BaggySig::from_wire_bytes` (`baggy.rs:606-639`). -/
def BaggySig.fromWireBytes (bp : BaggyParams) (raw : List UInt8) : Option BaggySig :=
  if !bp.wellFormed || decide (bp.sigBytesMax < raw.length) || decide (raw.length < 36) then none
  else
    let r := raw.take 32
    let msgCtr := ofBE ((raw.drop 32).take 4)
    if bp.maxGrind ≤ msgCtr then none
    else
      match PorsFpOpening.fromWireBytes bp.pors (raw.drop 36) with
      | none => none
      | some (pors, used) =>
        match parseBaggyLayers bp bp.numLayers ((raw.drop 36).drop used) with
        | some (layers, []) => some ⟨r, msgCtr, pors, layers⟩
        | _ => none

private theorem layers_wire_length (bp : BaggyParams) :
    ∀ (ls : List BaggyLayerSig), (∀ l ∈ ls, l.WellShaped bp) →
      (ls.map BaggyLayerSig.toWireBytes).flatten.length =
        ls.length * (4 + 32 * bp.wots.chains + 32 * bp.subtreeHeight)
  | [], _ => by simp
  | l :: ls, h => by
    obtain ⟨_, hCL, hC32, hAL, hA32⟩ := h l List.mem_cons_self
    have hOne : l.toWireBytes.length = 4 + 32 * bp.wots.chains + 32 * bp.subtreeHeight := by
      unfold BaggyLayerSig.toWireBytes
      rw [List.length_append, List.length_append, length_be,
        flatten_length_32 _ hC32, hCL, flatten_length_32 _ hA32, hAL]
    rw [List.map_cons, List.flatten_cons, List.length_append, hOne,
      layers_wire_length bp ls (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- **Exact Wire Byte Bound for `BaggySig` (`≤ 71,654 B` at `BaggySha3_128f`).** -/
theorem BaggySig.toWireBytes_length_le (bp : BaggyParams) (sig : BaggySig)
    (hShape : sig.WellShaped bp) :
    sig.toWireBytes.length =
      36 + sig.pors.toWireBytes.length +
        bp.numLayers * (4 + 32 * bp.wots.chains + 32 * bp.subtreeHeight) ∧
    sig.toWireBytes.length ≤ bp.sigBytesMax := by
  obtain ⟨hRL, _, hPors, hLL, hLAll⟩ := hShape
  have hPorsB := sig.pors.toWireBytes_length bp.pors hPors
  have hLayLen := layers_wire_length bp sig.layers hLAll
  rw [hLL] at hLayLen
  unfold BaggySig.toWireBytes BaggyParams.sigBytesMax
  rw [List.length_append, List.length_append, List.length_append, hRL, length_be, hLayLen]
  exact ⟨by omega, by omega⟩

theorem baggySha3_128f_sig_wire_le_71654 (sig : BaggySig)
    (hShape : sig.WellShaped BaggySha3_128f) :
    sig.toWireBytes.length ≤ 71654 :=
  (sig.toWireBytes_length_le BaggySha3_128f hShape).2

private theorem maxGrind_lt_u32 (bp : BaggyParams) (hw : bp.wellFormed = true) :
    bp.maxGrind ≤ 256 ^ 4 := by
  simp only [BaggyParams.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  have h : bp.maxGrind ≤ 2 ^ 32 := hw.1.1.2
  have hPow : (2 : Nat) ^ 32 = 256 ^ 4 := by decide
  omega

private theorem parseBaggyLayers_roundtrip (bp : BaggyParams) (hw : bp.wellFormed = true) :
    ∀ (ls : List BaggyLayerSig), (∀ l ∈ ls, l.WellShaped bp) → ∀ (rem : List UInt8),
      parseBaggyLayers bp ls.length ((ls.map BaggyLayerSig.toWireBytes).flatten ++ rem) =
        some (ls, rem)
  | [], _, rem => rfl
  | l :: ls, hAll, rem => by
    obtain ⟨hCtr, hCL, hC32, hAL, hA32⟩ := hAll l List.mem_cons_self
    have hTailAll : ∀ x ∈ ls, x.WellShaped bp := fun x hx => hAll x (List.mem_cons_of_mem _ hx)
    have hCtrU32 : l.ctr < 256 ^ 4 := Nat.lt_of_lt_of_le hCtr (maxGrind_lt_u32 bp hw)
    have hCLen : l.chains.flatten.length = 32 * bp.wots.chains :=
      (flatten_length_32 _ hC32).trans (congrArg (32 * ·) hCL)
    have hALen : l.auth.flatten.length = 32 * bp.subtreeHeight :=
      (flatten_length_32 _ hA32).trans (congrArg (32 * ·) hAL)
    let tailBytes := (ls.map BaggyLayerSig.toWireBytes).flatten ++ rem
    have hStream : ((l :: ls).map BaggyLayerSig.toWireBytes).flatten ++ rem =
        be 4 l.ctr ++ (l.chains.flatten ++ (l.auth.flatten ++ tailBytes)) := by
      simp only [List.map_cons, List.flatten_cons, BaggyLayerSig.toWireBytes, List.append_assoc,
        tailBytes]
    rw [List.length_cons, hStream]
    unfold parseBaggyLayers
    have hNotShort : ¬ (be 4 l.ctr ++ (l.chains.flatten ++ (l.auth.flatten ++ tailBytes))).length <
        4 + 32 * bp.wots.chains + 32 * bp.subtreeHeight := by
      rw [List.length_append, List.length_append, List.length_append, length_be, hCLen, hALen]
      omega
    rw [ite_eq_right hNotShort]
    obtain ⟨hTakeCtr, hDropCtr⟩ :=
      take_append_exact (be 4 l.ctr) (l.chains.flatten ++ (l.auth.flatten ++ tailBytes)) 4
        (length_be 4 _)
    rw [hTakeCtr, ofBE_be hCtrU32, ite_eq_right (Nat.not_le_of_lt hCtr)]
    obtain ⟨hTakeC, hDropC⟩ :=
      take_append_exact l.chains.flatten (l.auth.flatten ++ tailBytes) (32 * bp.wots.chains) hCLen
    obtain ⟨hTakeA, hDropA⟩ :=
      take_append_exact l.auth.flatten tailBytes (32 * bp.subtreeHeight) hALen
    have hDrop2 : (be 4 l.ctr ++ (l.chains.flatten ++ (l.auth.flatten ++ tailBytes))).drop
        (4 + 32 * bp.wots.chains) = l.auth.flatten ++ tailBytes := by
      rw [← List.drop_drop, hDropCtr, hDropC]
    have hDrop3 : (be 4 l.ctr ++ (l.chains.flatten ++ (l.auth.flatten ++ tailBytes))).drop
        (4 + 32 * bp.wots.chains + 32 * bp.subtreeHeight) = tailBytes := by
      rw [← List.drop_drop, hDrop2, hDropA]
    have hCChunks : takeChunks32 bp.wots.chains l.chains.flatten = l.chains := by
      rw [← hCL]
      have h := (takeChunks32_flatten l.chains hC32 []).1
      rwa [List.append_nil] at h
    have hAChunks : takeChunks32 bp.subtreeHeight l.auth.flatten = l.auth := by
      rw [← hAL]
      have h := (takeChunks32_flatten l.auth hA32 []).1
      rwa [List.append_nil] at h
    rw [hDropCtr, hTakeC, hCChunks, hDrop2, hTakeA, hAChunks, hDrop3,
      parseBaggyLayers_roundtrip bp hw ls hTailAll rem]

/-- **Exact Wire Codec Round-Trip for `BaggySig` (`fromWireBytes_toWireBytes`).** -/
theorem BaggySig.fromWireBytes_toWireBytes (bp : BaggyParams) (hw : bp.wellFormed = true)
    (sig : BaggySig) (hShape : sig.WellShaped bp) :
    BaggySig.fromWireBytes bp sig.toWireBytes = some sig := by
  obtain ⟨hLenEq, hLenMax⟩ := sig.toWireBytes_length_le bp hShape
  obtain ⟨hRL, hCtr, hPors, hLL, hLAll⟩ := hShape
  have hCtrU32 : sig.msgCtr < 256 ^ 4 := Nat.lt_of_lt_of_le hCtr (maxGrind_lt_u32 bp hw)
  unfold BaggySig.fromWireBytes
  have hGuard : (!bp.wellFormed || decide (bp.sigBytesMax < sig.toWireBytes.length) ||
      decide (sig.toWireBytes.length < 36)) = false := by
    rw [hw, decide_eq_false (Nat.not_lt_of_ge hLenMax),
      decide_eq_false (by rw [hLenEq]; omega)]
    rfl
  rw [hGuard]
  dsimp only [Bool.false_eq_true, ↓reduceIte]
  let tailAfterHdr := sig.pors.toWireBytes ++ (sig.layers.map BaggyLayerSig.toWireBytes).flatten
  have hWireSplit : sig.toWireBytes = sig.r ++ (be 4 sig.msgCtr ++ tailAfterHdr) := by
    unfold BaggySig.toWireBytes
    simp only [List.append_assoc, tailAfterHdr]
  obtain ⟨hTakeR, hDropR⟩ :=
    take_append_exact sig.r (be 4 sig.msgCtr ++ tailAfterHdr) 32 hRL
  obtain ⟨hTakeCtr, hDropCtr⟩ :=
    take_append_exact (be 4 sig.msgCtr) tailAfterHdr 4 (length_be 4 _)
  have hDrop36 : sig.toWireBytes.drop 36 = tailAfterHdr := by
    have h36 : (36 : Nat) = 32 + 4 := rfl
    rw [h36, ← List.drop_drop, hWireSplit, hDropR, hDropCtr]
  have hDrop32Take4 : (sig.toWireBytes.drop 32).take 4 = be 4 sig.msgCtr := by
    rw [hWireSplit, hDropR, hTakeCtr]
  have hTake32 : sig.toWireBytes.take 32 = sig.r := by
    rw [hWireSplit, hTakeR]
  rw [hTake32, hDrop32Take4, ofBE_be hCtrU32, ite_eq_right (Nat.not_le_of_lt hCtr), hDrop36]
  dsimp only [tailAfterHdr]
  rw [sig.pors.fromWireBytes_toWireBytes_append bp.pors
      (by simp only [BaggyParams.wellFormed, Bool.and_eq_true] at hw; exact hw.2) hPors]
  obtain ⟨_, hDropPors⟩ :=
    take_append_exact sig.pors.toWireBytes (sig.layers.map BaggyLayerSig.toWireBytes).flatten
      sig.pors.toWireBytes.length rfl
  simp only [Bool.false_eq_true, ↓reduceIte] at *
  rw [hDropPors]
  have hLayEq : parseBaggyLayers bp bp.numLayers
      ((sig.layers.map BaggyLayerSig.toWireBytes).flatten ++ []) = some (sig.layers, []) := by
    rw [← hLL]
    exact parseBaggyLayers_roundtrip bp hw sig.layers hLAll []
  rw [List.append_nil] at hLayEq
  rw [hLayEq]

theorem BaggySig.fromWireBytes_oversized_none (bp : BaggyParams) (raw : List UInt8)
    (hOver : bp.sigBytesMax < raw.length) :
    BaggySig.fromWireBytes bp raw = none := by
  unfold BaggySig.fromWireBytes
  rw [decide_eq_true hOver, Bool.or_true, Bool.true_or]
  rfl

theorem PorsFpOpening.fromWireBytes_oversized_auth_none (p : Params) (raw : List UInt8)
    (hOver : p.maxAuthNodes < ofBE ((raw.drop (32 * p.reveal)).take 2)) :
    PorsFpOpening.fromWireBytes p raw = none := by
  unfold PorsFpOpening.fromWireBytes
  cases !p.wellFormed
  · dsimp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · split <;> rfl
  · rfl

theorem porsSecretLeaf_length (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree : UInt64) (keyPair : UInt32) (i : Nat) :
    (porsSecretLeaf suite sk tree keyPair i).length = 32 := by
  unfold porsSecretLeaf
  rw [thSecretPrf_eq]
  exact thCall_length suite _ _ _ _

theorem porsHonestAuth_length_le (p : Params) (suite : HashSuite S D) (sec : Nat → S)
    (idx : List Nat) (hAdm : Admissible p idx) :
    (honestAuth suite sec p.treeHeight idx).length ≤ p.maxAuthNodes := by
  unfold honestAuth
  rw [List.length_map]
  exact hAdm.pruned

theorem porsTweakableSuite_honestAuth_all_len32 (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (tree : UInt64) (keyPair : UInt32) (sec : Nat → List UInt8) (h : Nat) (idx : List Nat) :
    ∀ a ∈ honestAuth (porsTweakableSuite suite pkSeed tree keyPair) sec h idx, a.length = 32 := by
  intro a ha
  unfold honestAuth at ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
  exact porsTweakableSuite_honestTree_length suite pkSeed tree keyPair sec q.1 q.2

theorem porsTweakableSuite_node_eq (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (tree : UInt64) (keyPair : UInt32) (lvl idx : Nat) (l r : List UInt8) :
    (porsTweakableSuite suite pkSeed tree keyPair).node lvl idx l r =
      thNodeH suite pkSeed (porsNodeAdrs tree keyPair (UInt32.ofNat lvl) (UInt32.ofNat idx)) l r := by
  (conv => lhs; unfold porsTweakableSuite) <;> rfl

theorem BaggyParams.pathAt_zero (bp : BaggyParams) (lvl : Nat) :
    bp.pathAt 0 lvl = (0, 0) := by
  unfold BaggyParams.pathAt
  simp [Nat.zero_div, Nat.zero_mod]

/-! ### 12.3 `Baggy` Hypertree-over-`PORS+FP` Verifier, Completeness & Multi-Query EUF-CMA Reduction -/

/-- `PqHashParams` projection of `BaggyParams`'s `WOTS+C` (`w = 4, ell1 = 128`) layer geometry. -/
def baggyWotsPqParams (bp : BaggyParams) : PqHashParams :=
  ⟨4, 128, bp.subtreeHeight, bp.numLayers, 0, 0, 1, false⟩

/-- `wots_c_digest_adrs` + `TAG_BAGGY_DIGEST` layer hash (`baggy.rs:916-929`). -/
def baggyLayerDigest (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (keyPair : UInt32) (node : List UInt8) (ctr : Nat) :
    List UInt8 :=
  thCall suite tagBaggyDigest pkSeed
    ⟨layer, tree, .wotsHash, keyPair, 0, UInt32.ofNat ctr⟩ [node, be 4 ctr]

/-- Abstract/instantiable `select_at` XOF stream reader (`TAG_BAGGY_HMSG` on
    `encodeMultiFrame [r, pkSeed, pkRoot, mu, be 4 msgCtr]`, `baggy.rs:829-848`):
    returns `(32-bit words for pors_fp_select, 64-bit word for leaf_idx)`. -/
@[expose, reducible] def BaggyHmsgStream := List UInt8 → List Nat × Nat

/-- Concrete `select_at` (`baggy.rs:829-848`) parameterized by the `TAG_BAGGY_HMSG` XOF stream. -/
def baggySelectAt (hmsgXof : BaggyHmsgStream) (bp : BaggyParams) (pk : PqPublicKey)
    (r mu : List UInt8) (msgCtr : Nat) : Option (List Nat × Nat) :=
  let frame := encodeMultiFrame [r, pk.pkSeed, pk.pkRoot, mu, be 4 msgCtr]
  let words := (hmsgXof frame).1
  let leafWord := (hmsgXof frame).2
  match select bp.pors words with
  | none => none
  | some idxs => some (idxs, leafWord % 2 ^ bp.totalHeight)

theorem baggySelectAt_admissible (hmsgXof : BaggyHmsgStream) (bp : BaggyParams)
    (pk : PqPublicKey) (r mu : List UInt8) (msgCtr : Nat) {idxs : List Nat} {leafIdx : Nat}
    (h : baggySelectAt hmsgXof bp pk r mu msgCtr = some (idxs, leafIdx)) :
    Admissible bp.pors idxs ∧ leafIdx < 2 ^ bp.totalHeight := by
  unfold baggySelectAt at h
  dsimp only at h
  cases hSel : select bp.pors (hmsgXof (encodeMultiFrame [r, pk.pkSeed, pk.pkRoot, mu, be 4 msgCtr])).1 with
  | none => rw [hSel] at h; cases h
  | some s =>
    rw [hSel] at h
    injection h with hPair
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPair
    exact ⟨select_admissible bp.pors _ s hSel, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Recompute one `Baggy` hypertree layer root (`layer_root`, `baggy.rs:932-968`). -/
def baggyLayerRoot (suite : TweakableHashSuite) (bp : BaggyParams) (pkSeed : List UInt8)
    (layer : Nat) (tree : UInt64) (kp : UInt32) (node : List UInt8)
    (lsig : BaggyLayerSig) : Option (List UInt8) :=
  if !decide (lsig.ctr < bp.maxGrind) || !decide (lsig.chains.length = 128) ||
      !lsig.chains.all (fun c => decide (c.length = 32)) ||
      !decide (lsig.auth.length = bp.subtreeHeight) ||
      !lsig.auth.all (fun a => decide (a.length = 32)) then
    none
  else
    let dg := baggyLayerDigest suite pkSeed (UInt32.ofNat layer) tree kp node lsig.ctr
    let digits := extractBaseWDigits 4 128 dg
    if !checkTargetSum 4 128 192 digits then none
    else
      let wotsLeaf := recoverWotsPkFromSig suite (baggyWotsPqParams bp) pkSeed
        (UInt32.ofNat layer) tree kp.toNat digits lsig.chains
      walkMerkleAuthPath suite pkSeed (UInt32.ofNat layer) tree .tree
        bp.subtreeHeight 0 kp.toNat wotsLeaf lsig.auth

/-- Climb `layers` starting at layer `lvl` from bottom PORS+FP root `curNode`. -/
def baggyClimbLayers (suite : TweakableHashSuite) (bp : BaggyParams) (pkSeed : List UInt8)
    (leafIdx : Nat) : Nat → List UInt8 → List BaggyLayerSig → Option (List UInt8)
  | _, curNode, [] => some curNode
  | lvl, curNode, lsig :: rest =>
    let (kp, tree) := bp.pathAt leafIdx lvl
    match baggyLayerRoot suite bp pkSeed lvl tree kp curNode lsig with
    | none => none
    | some nextNode => baggyClimbLayers suite bp pkSeed leafIdx (lvl + 1) nextNode rest

/-- **`baggy_verify` (`crates/qsag-core/src/baggy.rs:971-1010`).** -/
@[expose] def baggyVerify (suite : TweakableHashSuite) (hmsgXof : BaggyHmsgStream)
    (bp : BaggyParams) (pk : PqPublicKey) (msg : List UInt8) (sig : BaggySig) : Bool :=
  if !bp.wellFormed || !decide (sig.r.length = 32) ||
      !decide (sig.layers.length = bp.numLayers) ||
      !decide (sig.msgCtr < bp.maxGrind) ||
      !sig.pors.secrets.all (fun s => decide (s.length = 32)) ||
      !sig.pors.auth.all (fun a => decide (a.length = 32)) then
    false
  else
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    match baggySelectAt hmsgXof bp pk sig.r mu sig.msgCtr with
    | none => false
    | some (idxs, leafIdx) =>
      let kp0 := (bp.pathAt leafIdx 0).1
      let tree0 := (bp.pathAt leafIdx 0).2
      match porsFpRoot bp.pors (porsTweakableSuite suite pk.pkSeed tree0 kp0)
          idxs sig.pors.secrets sig.pors.auth with
      | none => false
      | some node0 =>
        match baggyClimbLayers suite bp pk.pkSeed leafIdx 0 node0 sig.layers with
        | none => false
        | some topRoot => decide (topRoot = pk.pkRoot)

/-- Honest PORS+FP root at hypertree bottom leaf `(tree0, kp0)`. -/
def baggyHonestPorsRoot (suite : TweakableHashSuite) (bp : BaggyParams) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 : UInt32) : List UInt8 :=
  honestTree (porsTweakableSuite suite sk.pkSeed tree0 kp0)
    (porsSecretLeaf suite sk tree0 kp0) bp.pors.treeHeight 0

/-- Honest subtree root at hypertree layer `layer` (`0 ≤ layer < bp.numLayers`). -/
def baggyHonestSubtreeRoot (suite : TweakableHashSuite) (bp : BaggyParams) (sk : PqSecretKey)
    (layer : Nat) (tree : UInt64) : List UInt8 :=
  computeXmssSubtreeRoot suite (baggyWotsPqParams bp) sk (UInt32.ofNat layer) tree

/-- Derive canonical `Baggy` `PqPublicKey` from top subtree `(numLayers - 1, 0)`. -/
def baggyDerivePublicKey (suite : TweakableHashSuite) (bp : BaggyParams) (sk : PqSecretKey) :
    PqPublicKey :=
  ⟨sk.pkSeed, baggyHonestSubtreeRoot suite bp sk (bp.numLayers - 1) 0⟩

theorem baggyVerify_high_ctr_false (suite : TweakableHashSuite) (hmsgXof : BaggyHmsgStream)
    (bp : BaggyParams) (pk : PqPublicKey) (msg : List UInt8) (sig : BaggySig)
    (hCtr : bp.maxGrind ≤ sig.msgCtr) :
    baggyVerify suite hmsgXof bp pk msg sig = false := by
  unfold baggyVerify
  rw [decide_eq_false (Nat.not_lt_of_ge hCtr)]
  simp only [Bool.not_false, Bool.or_true, Bool.true_or, ↓reduceIte]

theorem baggyDerivePublicKey_eq (suite : TweakableHashSuite) (bp : BaggyParams) (sk : PqSecretKey) :
    baggyDerivePublicKey suite bp sk =
      ⟨sk.pkSeed, computeXmssSubtreeRoot suite (baggyWotsPqParams bp) sk
        (UInt32.ofNat (bp.numLayers - 1)) 0⟩ := by
  (conv => lhs; unfold baggyDerivePublicKey) <;> rfl

theorem baggyWotsPqParams_eq (bp : BaggyParams) :
    baggyWotsPqParams bp = ⟨4, 128, bp.subtreeHeight, bp.numLayers, 0, 0, 1, false⟩ := by
  (conv => lhs; unfold baggyWotsPqParams) <;> rfl

theorem baggySelectAt_eq (hmsgXof : BaggyHmsgStream) (bp : BaggyParams) (pk : PqPublicKey)
    (r mu : List UInt8) (msgCtr : Nat) :
    baggySelectAt hmsgXof bp pk r mu msgCtr =
      let frame := encodeMultiFrame [r, pk.pkSeed, pk.pkRoot, mu, be 4 msgCtr]
      let words := (hmsgXof frame).1
  let leafWord := (hmsgXof frame).2
      match select bp.pors words with
      | none => none
      | some idxs => some (idxs, leafWord % 2 ^ bp.totalHeight) := by
  (conv => lhs; unfold baggySelectAt) <;> rfl

theorem baggyClimbLayers_nil (suite : TweakableHashSuite) (bp : BaggyParams) (pkSeed : List UInt8)
    (leafIdx lvl : Nat) (curNode : List UInt8) :
    baggyClimbLayers suite bp pkSeed leafIdx lvl curNode [] = some curNode := by
  (conv => lhs; unfold baggyClimbLayers) <;> rfl

theorem baggyClimbLayers_cons (suite : TweakableHashSuite) (bp : BaggyParams) (pkSeed : List UInt8)
    (leafIdx lvl : Nat) (curNode : List UInt8) (lsig : BaggyLayerSig) (rest : List BaggyLayerSig) :
    baggyClimbLayers suite bp pkSeed leafIdx lvl curNode (lsig :: rest) =
      let (kp, tree) := bp.pathAt leafIdx lvl
      match baggyLayerRoot suite bp pkSeed lvl tree kp curNode lsig with
      | none => none
      | some nextNode => baggyClimbLayers suite bp pkSeed leafIdx (lvl + 1) nextNode rest := by
  (conv => lhs; unfold baggyClimbLayers) <;> rfl

theorem baggyLayerRoot_eq (suite : TweakableHashSuite) (bp : BaggyParams) (pkSeed : List UInt8)
    (layer : Nat) (tree : UInt64) (kp : UInt32) (node : List UInt8) (lsig : BaggyLayerSig) :
    baggyLayerRoot suite bp pkSeed layer tree kp node lsig =
      if !decide (lsig.ctr < bp.maxGrind) || !decide (lsig.chains.length = 128) ||
          !lsig.chains.all (fun c => decide (c.length = 32)) ||
          !decide (lsig.auth.length = bp.subtreeHeight) ||
          !lsig.auth.all (fun a => decide (a.length = 32)) then
        none
      else
        let dg := thCall suite tagBaggyDigest pkSeed
          ⟨UInt32.ofNat layer, tree, .wotsHash, kp, 0, UInt32.ofNat lsig.ctr⟩ [node, be 4 lsig.ctr]
        let digits := extractBaseWDigits 4 128 dg
        if !checkTargetSum 4 128 192 digits then none
        else
          let wotsLeaf := recoverWotsPkFromSig suite (baggyWotsPqParams bp) pkSeed
            (UInt32.ofNat layer) tree kp.toNat digits lsig.chains
          walkMerkleAuthPath suite pkSeed (UInt32.ofNat layer) tree .tree
            bp.subtreeHeight 0 kp.toNat wotsLeaf lsig.auth := by
  (conv => lhs; unfold baggyLayerRoot) <;> rfl

/-- Honest node expected on `leafIdx`'s path before climbing layer `lvl`:
    at `lvl = 0` it is the honest `PORS+FP` root; at `lvl = l + 1` it is the honest subtree root
    of layer `l`. -/
def baggyHonestPathNode (suite : TweakableHashSuite) (bp : BaggyParams) (sk : PqSecretKey)
    (leafIdx : Nat) : Nat → List UInt8
  | 0 =>
    let (kp0, tree0) := bp.pathAt leafIdx 0
    baggyHonestPorsRoot suite bp sk tree0 kp0
  | l + 1 =>
    let (_, tree) := bp.pathAt leafIdx l
    baggyHonestSubtreeRoot suite bp sk l tree

theorem baggyHonestPathNode_top (suite : TweakableHashSuite) (bp : BaggyParams) (sk : PqSecretKey)
    (hw : bp.wellFormed = true) {leafIdx : Nat} (hLeaf : leafIdx < 2 ^ bp.totalHeight) :
    baggyHonestPathNode suite bp sk leafIdx bp.numLayers =
      (baggyDerivePublicKey suite bp sk).pkRoot := by
  simp only [BaggyParams.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hdPos : 1 ≤ bp.numLayers := hw.1.1.1.1.1.2
  have hdSplit : bp.numLayers = (bp.numLayers - 1) + 1 := (Nat.sub_add_cancel hdPos).symm
  rw [hdSplit]
  unfold baggyHonestPathNode baggyDerivePublicKey
  dsimp only [Nat.add_sub_cancel]
  have hTree0 : (bp.pathAt leafIdx (bp.numLayers - 1)).2 = 0 := by
    unfold BaggyParams.pathAt
    dsimp only
    have hTot : bp.totalHeight = bp.subtreeHeight * (bp.numLayers - 1) + bp.subtreeHeight := by
      unfold BaggyParams.totalHeight
      conv => lhs; rw [hdSplit, Nat.mul_add, Nat.mul_one]
    rw [hTot, Nat.pow_add] at hLeaf
    have hDiv1 : leafIdx / 2 ^ (bp.subtreeHeight * (bp.numLayers - 1)) < 2 ^ bp.subtreeHeight :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        (by rw [Nat.mul_comm] at hLeaf; exact hLeaf)
    have hDiv2 : (leafIdx / 2 ^ (bp.subtreeHeight * (bp.numLayers - 1))) / 2 ^ bp.subtreeHeight = 0 :=
      Nat.div_eq_of_lt hDiv1
    rw [hDiv2]
    rfl
  rw [hTree0]

/-- Signed query record in an honest `FirstSignedLedger`-guarded `Baggy` transcript:
    stores the signed message, its `BaggySig`, and proof that it was honestly generated under `sk`. -/
structure HonestBaggySignedEntry (suite : TweakableHashSuite) (hmsgXof : BaggyHmsgStream)
    (bp : BaggyParams) (sk : PqSecretKey) where
  msg : List UInt8
  sig : BaggySig
  idxs : List Nat
  leafIdx : Nat
  selected : baggySelectAt hmsgXof bp (baggyDerivePublicKey suite bp sk) sig.r
    (thPreHash suite sk.pkSeed (baggyDerivePublicKey suite bp sk).pkRoot msg) sig.msgCtr =
    some (idxs, leafIdx)
  layers_len : sig.layers.length = bp.numLayers
  honest_layers : ∀ l : Nat, (hl : l < sig.layers.length) →
    let (kp, tree) := bp.pathAt leafIdx l
    let lsig := sig.layers[l]'hl
    let dg := baggyLayerDigest suite sk.pkSeed (UInt32.ofNat l) tree kp
      (baggyHonestPathNode suite bp sk leafIdx l) lsig.ctr
    let digits := extractBaseWDigits 4 128 dg
    checkTargetSum 4 128 192 digits = true ∧
    lsig.chains = (List.range 128).map (fun r =>
      wotsChainSteps suite sk.pkSeed (UInt32.ofNat l) tree kp.toNat r 0 (digits.getD r 0)
        (wotsSecretBase suite sk (UInt32.ofNat l) tree kp.toNat r))

/-- `FirstSignedLedger` invariant (`baggy.rs:361-389`): any two honest signatures traversing the
    same static key `(layer, tree, kp)` sign the same node `baggyHonestPathNode` with the same
    counter `ctr` (hence open the exact same digit vector). -/
def FirstSignedConsistent {suite : TweakableHashSuite} {hmsgXof : BaggyHmsgStream}
    {bp : BaggyParams} {sk : PqSecretKey}
    (log : List (HonestBaggySignedEntry suite hmsgXof bp sk)) : Prop :=
  ∀ e₁ ∈ log, ∀ e₂ ∈ log, ∀ l : Nat, (hl₁ : l < e₁.sig.layers.length) →
    (hl₂ : l < e₂.sig.layers.length) →
    bp.pathAt e₁.leafIdx l = bp.pathAt e₂.leafIdx l →
    (e₁.sig.layers[l]'hl₁).ctr = (e₂.sig.layers[l]'hl₂).ctr

/-- Constructive (`Type`-valued, `0 Classical.choice`) forgery break witness for `Baggy`:
    every valid forgery against an honestly signed multi-query `Baggy` log constructively yields
    (1) a fresh `TAG_BAGGY_HMSG` `PORS+FP` subset cover (`porsItsr`),
    (2) an explicit byte-hash collision (`hashCollision`), or
    (3) an unopened `PORS+FP` leaf preimage or `WOTS+C` chain backward-inversion preimage
        (`secretPreimage`). -/
inductive BaggyForgeryBreak (suite : TweakableHashSuite) (hmsgXof : BaggyHmsgStream)
    (bp : BaggyParams) (sk : PqSecretKey)
    (log : List (HonestBaggySignedEntry suite hmsgXof bp sk)) : Type where
  | porsItsr
      (rStar muStar : List UInt8) (ctrStar leafIdx : Nat) (idxsStar : List Nat)
      (hSel : baggySelectAt hmsgXof bp (baggyDerivePublicKey suite bp sk) rStar muStar ctrStar =
        some (idxsStar, leafIdx))
      (hFreshHmsg : ∀ e ∈ log,
        encodeMultiFrame [rStar, sk.pkSeed, (baggyDerivePublicKey suite bp sk).pkRoot,
          muStar, be 4 ctrStar] ≠
        encodeMultiFrame [e.sig.r, sk.pkSeed, (baggyDerivePublicKey suite bp sk).pkRoot,
          thPreHash suite sk.pkSeed (baggyDerivePublicKey suite bp sk).pkRoot e.msg,
          be 4 e.sig.msgCtr])
      (hCovered : ∀ u ∈ idxsStar,
        ∃ e ∈ log, bp.pathAt e.leafIdx 0 = bp.pathAt leafIdx 0 ∧ u ∈ e.idxs)
  | hashCollision (col : HashCollisionWitness suite.rawHash)
  | porsUnopenedPreimage
      (tree0 : UInt64) (kp0 : UInt32) (leafPos : Nat) (candSecret : List UInt8)
      (hUnopened : ∀ e ∈ log, bp.pathAt e.leafIdx 0 = (kp0, tree0) → leafPos ∉ e.idxs)
      (hPre : thChainF suite sk.pkSeed (porsLeafAdrs tree0 kp0 (UInt32.ofNat leafPos)) candSecret =
        (porsTweakableSuite suite sk.pkSeed tree0 kp0).leaf leafPos
          (porsSecretLeaf suite sk tree0 kp0 leafPos))
  | wotsBackwardPreimage (inv : WotsBackwardInversionWitness suite sk.pkSeed)

private def findLtThree : List Nat → Nat → Option Nat
  | [], _ => none
  | d :: ds, idx => if d < 3 then some idx else findLtThree ds (idx + 1)

private theorem findLtThree_spec :
    ∀ (ds : List Nat) (idx r : Nat),
      findLtThree ds idx = some r → idx ≤ r ∧ ds.getD (r - idx) 0 < 3
  | [], _, _, h => nomatch h
  | d :: ds, idx, r, h => by
    unfold findLtThree at h
    by_cases hd : d < 3
    · rw [ite_eq_left hd] at h
      injection h with hEq; subst hEq
      rw [Nat.sub_self]
      exact ⟨Nat.le_refl _, hd⟩
    · rw [ite_eq_right hd] at h
      obtain ⟨hLe, hLt⟩ := findLtThree_spec ds (idx + 1) r h
      have hSub : r - idx = (r - (idx + 1)) + 1 := by omega
      rw [hSub]
      exact ⟨by omega, hLt⟩

private theorem findLtThree_exists_of_sumDigits_lt :
    ∀ (ds : List Nat) (idx : Nat),
      sumDigits ds < 3 * ds.length → ∃ r, findLtThree ds idx = some r
  | [], _, h => by rw [sumDigits_nil] at h; exact absurd h (Nat.lt_irrefl 0)
  | d :: ds, idx, h => by
    unfold findLtThree
    by_cases hd : d < 3
    · exact ⟨idx, ite_eq_left hd⟩
    · rw [ite_eq_right hd]
      rw [sumDigits_cons, List.length_cons] at h
      exact findLtThree_exists_of_sumDigits_lt ds (idx + 1) (by omega)

private theorem findLtThree_lt_len :
    ∀ (ds : List Nat) (idx r : Nat), findLtThree ds idx = some r → r < idx + ds.length
  | [], _, _, h => nomatch h
  | d :: ds, idx, r, h => by
    unfold findLtThree at h
    by_cases hd : d < 3
    · rw [ite_eq_left hd] at h; injection h with hEq; subst hEq; rw [List.length_cons]; omega
    · rw [ite_eq_right hd] at h
      have ih := findLtThree_lt_len ds (idx + 1) r h
      rw [List.length_cons]; omega

private theorem list_getD_range_map {α : Type} (n : Nat) (f : Nat → α) (d : α) {r : Nat}
    (hr : r < n) : ((List.range n).map f).getD r d = f r := by
  have hLen : ((List.range n).map f).length = n := by rw [List.length_map, List.length_range]
  have hrL : r < ((List.range n).map f).length := by rw [hLen]; exact hr
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrL]
  simp

private def extractUnopenedWotsLayer (suite : TweakableHashSuite) (bp : BaggyParams)
    (sk : PqSecretKey) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digits : List Nat) (forgedChains : List (List UInt8))
    (hValid : checkTargetSum 4 128 192 digits = true)
    (hSamePk : recoverWotsPkFromSig suite (baggyWotsPqParams bp) sk.pkSeed layer tree kp
        digits forgedChains =
      computeWotsPk suite (baggyWotsPqParams bp) sk layer tree kp) :
    PSum (WotsBackwardInversionWitness suite sk.pkSeed) (HashCollisionWitness suite.rawHash) :=
  let endF := recoverWotsEndpoints suite (baggyWotsPqParams bp) sk.pkSeed layer tree kp digits forgedChains
  let endH := computeWotsEndpoints suite (baggyWotsPqParams bp) sk layer tree kp
  if hEndNe : endF ≠ endH then
    have hTlEq : thTweakTl suite sk.pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩ endF =
        thTweakTl suite sk.pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩ endH := by
      rw [recoverWotsPkFromSig_eq] at hSamePk
      rw [computeWotsPk_eq, ← computeWotsEndpoints_eq] at hSamePk
      exact hSamePk
    match thCall_binds_or_collision suite (t₁ := tagThTl) (t₂ := tagThTl)
      (p₁ := sk.pkSeed) (p₂ := sk.pkSeed)
      (a₁ := ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩)
      (a₂ := ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩)
      (xs₁ := endF) (xs₂ := endH) (by rwa [thTweakTl_eq, thTweakTl_eq] at hTlEq) with
    | .inl ⟨_, _, _, hEq⟩ => False.elim (hEndNe hEq)
    | .inr col => .inr col
  else
    have hEndEq : endF = endH := Decidable.of_not_not hEndNe
    have hLenD := ((checkTargetSum_iff 4 128 192 digits).mp hValid).1
    have hSumD := ((checkTargetSum_iff 4 128 192 digits).mp hValid).2.2
    have hEx : ∃ r, findLtThree digits 0 = some r := by
      refine findLtThree_exists_of_sumDigits_lt digits 0 ?_
      rw [hSumD, hLenD]
      decide
    match hFind : findLtThree digits 0 with
    | none => False.elim (by obtain ⟨_, hr⟩ := hEx; rw [hFind] at hr; cases hr)
    | some r =>
      have hSpec := findLtThree_spec digits 0 r hFind
      have hsLt : digits.getD r 0 < 3 := by simpa using hSpec.2
      have hrLt128 : r < 128 := by
        have hLt := findLtThree_lt_len digits 0 r hFind
        omega
      let s₂ := digits.getD r 0
      let sig₂ := forgedChains.getD r []
      let preVal := wotsChainSteps suite sk.pkSeed layer tree kp r s₂ (2 - s₂) sig₂
      let endVal := endH.getD r []
      have hInv : thChainF suite sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat 2⟩ preVal =
          endVal := by
        have hEndFR : endF.getD r [] =
            wotsChainSteps suite sk.pkSeed layer tree kp r s₂ (3 - s₂) sig₂ := by
          dsimp only [endF]
          rw [recoverWotsEndpoints_eq]
          exact list_getD_range_map 128 _ [] hrLt128
        have hSplit3 : 3 - s₂ = (2 - s₂) + 1 := by omega
        have hAdd2 : s₂ + (2 - s₂) = 2 := by omega
        have hComp := wotsChainSteps_add suite sk.pkSeed layer tree kp r (2 - s₂) 1 s₂ sig₂
        rw [hAdd2, ← hSplit3] at hComp
        rw [wotsChainSteps_succ, wotsChainSteps_zero] at hComp
        exact hComp.trans (hEndFR.symm.trans (congrArg (fun l => l.getD r []) hEndEq))
      .inl
        { layer := layer
          tree := tree
          kp := kp
          chain := r
          step := 2
          revealedStep := 3
          step_lt := by decide
          preimage := preVal
          revealedVal := endVal
          invertsChain := hInv }

private def extractPorsPlanCollision (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 : UInt32) (lvl : Nat) :
    ∀ (ps : List (Nat × Bool)) (ns ns' as_ as' oM rM : List (List UInt8)),
      (ns ≠ ns' ∨ as_ ≠ as') →
      applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps ns as_ = some (oM, rM) →
      applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps ns' as' = some (oM, rM) →
      HashCollisionWitness suite.rawHash
  | [], ns, ns', as_, as', oM, rM, hN, hp1, hp2 => by
    obtain ⟨hn1, _, hr1⟩ := (applyPlan_nil _ ns as_ oM rM).mp hp1
    obtain ⟨hn2, _, hr2⟩ := (applyPlan_nil _ ns' as' oM rM).mp hp2
    exact False.elim (hN.elim (fun h => h (hn1.trans hn2.symm))
      (fun h => h (hr1.symm.trans hr2)))
  | g :: ps, ns, ns', as_, as', oM, rM, hN, hp1, hp2 => by
    obtain ⟨x, b⟩ := g
    cases b with
    | true =>
      match ns, ns' with
      | n1 :: m1 :: t1, n2 :: m2 :: t2 =>
        change consOut ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1) (x / 2) n1 m1)
          (applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps t1 as_) = some (oM, rM) at hp1
        change consOut ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1) (x / 2) n2 m2)
          (applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps t2 as') = some (oM, rM) at hp2
        cases hSub1 : applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps t1 as_ with
        | none => rw [hSub1] at hp1; cases hp1
        | some s1 =>
          cases hSub2 : applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps t2 as' with
          | none => rw [hSub2] at hp2; cases hp2
          | some s2 =>
            rw [hSub1] at hp1; rw [hSub2] at hp2
            injection hp1 with hp1'
            injection hp2 with hp2'
            have hEqO := (Prod.mk.inj hp1').1.trans (Prod.mk.inj hp2').1.symm
            have hEqR := (Prod.mk.inj hp1').2.trans (Prod.mk.inj hp2').2.symm
            have hHead := (List.cons.inj hEqO).1
            have hTail := (List.cons.inj hEqO).2
            have hsEq : s2 = s1 := Prod.ext hTail.symm hEqR.symm
            rw [hsEq] at hSub2
            if hChildNe : n1 ≠ n2 ∨ m1 ≠ m2 then
              exact liftPorsNodeCollision suite sk.pkSeed tree0 kp0 (lvl + 1) (x / 2)
                hChildNe hHead
            else
              have hnEq : n1 = n2 := Decidable.of_not_not (fun h => hChildNe (.inl h))
              have hmEq : m1 = m2 := Decidable.of_not_not (fun h => hChildNe (.inr h))
              have hSubNe : t1 ≠ t2 ∨ as_ ≠ as' := by
                rcases hN with hNs | hAs
                · exact .inl (fun ht => hNs (by rw [hnEq, hmEq, ht]))
                · exact .inr hAs
              exact extractPorsPlanCollision suite sk tree0 kp0 lvl ps t1 t2 as_ as' s1.1 s1.2 hSubNe hSub1 hSub2
      | [], _ => cases hp1
      | [_], _ => cases hp1
      | _ :: _ :: _, [] => cases hp2
      | _ :: _ :: _, [_] => cases hp2
    | false =>
      match ns, as_, ns', as' with
      | n1 :: t1, a1 :: at1, n2 :: t2, a2 :: at2 =>
        change consOut (combine ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) x n1 a1)
          (applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps t1 at1) = some (oM, rM) at hp1
        change consOut (combine ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) x n2 a2)
          (applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps t2 at2) = some (oM, rM) at hp2
        cases hSub1 : applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps t1 at1 with
        | none => rw [hSub1] at hp1; cases hp1
        | some s1 =>
          cases hSub2 : applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) ps t2 at2 with
          | none => rw [hSub2] at hp2; cases hp2
          | some s2 =>
            rw [hSub1] at hp1; rw [hSub2] at hp2
            injection hp1 with hp1'
            injection hp2 with hp2'
            have hEqO := (Prod.mk.inj hp1').1.trans (Prod.mk.inj hp2').1.symm
            have hEqR := (Prod.mk.inj hp1').2.trans (Prod.mk.inj hp2').2.symm
            have hHead := (List.cons.inj hEqO).1
            have hTail := (List.cons.inj hEqO).2
            have hsEq : s2 = s1 := Prod.ext hTail.symm hEqR.symm
            rw [hsEq] at hSub2
            if hChildNe : n1 ≠ n2 ∨ a1 ≠ a2 then
              if hxOdd : x % 2 = 1 then
                rw [combine_odd _ _ _ hxOdd, combine_odd _ _ _ hxOdd] at hHead
                exact liftPorsNodeCollision suite sk.pkSeed tree0 kp0 (lvl + 1) (x / 2)
                  (hChildNe.elim .inr .inl) hHead
              else
                rw [combine_even _ _ _ hxOdd, combine_even _ _ _ hxOdd] at hHead
                exact liftPorsNodeCollision suite sk.pkSeed tree0 kp0 (lvl + 1) (x / 2)
                  hChildNe hHead
            else
              have hnEq : n1 = n2 := Decidable.of_not_not (fun h => hChildNe (.inl h))
              have haEq : a1 = a2 := Decidable.of_not_not (fun h => hChildNe (.inr h))
              have hSubNe : t1 ≠ t2 ∨ at1 ≠ at2 := by
                rcases hN with hNs | hAs
                · exact .inl (fun ht => hNs (by rw [hnEq, ht]))
                · exact .inr (fun hat => hAs (by rw [haEq, hat]))
              exact extractPorsPlanCollision suite sk tree0 kp0 lvl ps t1 t2 at1 at2 s1.1 s1.2 hSubNe hSub1 hSub2
      | [], _, _, _ => cases hp1
      | _ :: _, [], _, _ => cases hp1
      | _ :: _, _ :: _, [], _ => cases hp2
      | _ :: _, _ :: _, _ :: _, [] => cases hp2

private def extractPorsClimbCollision (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 : UInt32) :
    ∀ (n lvl : Nat) (ix : List Nat) (nodes nodes' auth auth' top rem : List (List UInt8)),
      (nodes ≠ nodes' ∨ auth ≠ auth') →
      climb (porsTweakableSuite suite sk.pkSeed tree0 kp0).node n lvl ix nodes auth = some (top, rem) →
      climb (porsTweakableSuite suite sk.pkSeed tree0 kp0).node n lvl ix nodes' auth' = some (top, rem) →
      HashCollisionWitness suite.rawHash
  | 0, lvl, ix, nodes, nodes', auth, auth', top, rem, hNe, hC1, hC2 => by
    cases hC1; cases hC2
    exact False.elim (hNe.elim (fun h => h rfl) (fun h => h rfl))
  | n + 1, lvl, ix, nodes, nodes', auth, auth', top, rem, hNe, hC1, hC2 => by
    rw [climb_succ] at hC1 hC2
    cases hA1 : applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) (plan ix) nodes auth with
    | none => rw [hA1] at hC1; cases hC1
    | some r1 =>
      cases hA2 : applyPlan ((porsTweakableSuite suite sk.pkSeed tree0 kp0).node (lvl + 1)) (plan ix) nodes' auth' with
      | none => rw [hA2] at hC2; cases hC2
      | some r2 =>
        rw [hA1] at hC1; rw [hA2] at hC2
        if hRNe : r1.1 ≠ r2.1 ∨ r1.2 ≠ r2.2 then
          exact extractPorsClimbCollision suite sk tree0 kp0 n (lvl + 1) (parents ix) r1.1 r2.1 r1.2 r2.2 top rem hRNe hC1 hC2
        else
          have hR1Eq : r1.1 = r2.1 := Decidable.of_not_not (fun h => hRNe (.inl h))
          have hR2Eq : r1.2 = r2.2 := Decidable.of_not_not (fun h => hRNe (.inr h))
          have hREq : r2 = r1 := Prod.ext hR1Eq.symm hR2Eq.symm
          rw [hREq] at hA2
          exact extractPorsPlanCollision suite sk tree0 kp0 lvl (plan ix)
            nodes nodes' auth auth' r1.1 r1.2 hNe hA1 hA2

private def extractPorsLeafCollision (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 : UInt32) :
    ∀ (ix : List Nat) (ss : List (List UInt8)), ss.length = ix.length →
      ss ≠ ix.map (porsSecretLeaf suite sk tree0 kp0) →
      List.zipWith (porsTweakableSuite suite sk.pkSeed tree0 kp0).leaf ix ss =
        List.zipWith (porsTweakableSuite suite sk.pkSeed tree0 kp0).leaf ix (ix.map (porsSecretLeaf suite sk tree0 kp0)) →
      HashCollisionWitness suite.rawHash
  | [], ss, hL, hNe, _ => by
    cases ss with | nil => exact False.elim (hNe rfl) | cons _ _ => cases hL
  | u :: us, ss, hL, hNe, hZ => by
    cases ss with
    | nil => cases hL
    | cons s0 st =>
      rw [List.map_cons, List.zipWith_cons_cons, List.zipWith_cons_cons] at hZ
      if hs0 : s0 = (porsSecretLeaf suite sk tree0 kp0) u then
        exact extractPorsLeafCollision suite sk tree0 kp0 us st (Nat.succ.inj hL) (fun hSt => hNe (by rw [List.map_cons, hs0, hSt]))
          (List.cons.inj hZ).2
      else
        exact liftPorsLeafCollision suite sk.pkSeed tree0 kp0 u hs0 (List.cons.inj hZ).1

/-- Constructive `Type`-valued PORS+FP binding extractor (`0 Classical.choice`) lifting
    `opening_against_honest_root` directly to `PSum` over `HashCollisionWitness suite.rawHash`. -/
def extractPorsOpeningOrCollision (p : Params) (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 : UInt32) (idxs : List Nat) (o : PorsFpOpening)
    (hRoot : porsFpRoot p (porsTweakableSuite suite sk.pkSeed tree0 kp0) idxs o.secrets o.auth =
      some (baggyHonestPorsRoot suite ⟨WotsCParams.v128, 2, 16, 2 ^ 26, p⟩ sk tree0 kp0)) :
    PSum
      (o.secrets = idxs.map (porsSecretLeaf suite sk tree0 kp0) ∧
        o.auth = honestAuth (porsTweakableSuite suite sk.pkSeed tree0 kp0)
          (porsSecretLeaf suite sk tree0 kp0) p.treeHeight idxs)
      (HashCollisionWitness suite.rawHash) := by
  let tSuite := porsTweakableSuite suite sk.pkSeed tree0 kp0
  let sec := porsSecretLeaf suite sk tree0 kp0
  if hEq : o.secrets = idxs.map sec ∧ o.auth = honestAuth tSuite sec p.treeHeight idxs then
    exact .inl hEq
  else
    have hShape := porsFpRoot_some_shape p tSuite idxs o.secrets o.auth _ hRoot
    have hHon := porsFpRoot_complete p tSuite sec idxs hShape.1 hShape.2.1
    have h1 := ((porsFpRoot_eq_some_iff p tSuite idxs o.secrets o.auth _).mp hRoot).2
    have h2 := ((porsFpRoot_eq_some_iff p tSuite idxs (idxs.map sec)
      (honestAuth tSuite sec p.treeHeight idxs) _).mp hHon).2
    if hSecEq : o.secrets = idxs.map sec then
      rw [hSecEq] at h1
      exact .inr (extractPorsClimbCollision suite sk tree0 kp0 p.treeHeight 0 idxs _ _
        o.auth _ _ [] (.inr (fun hA => hEq ⟨hSecEq, hA⟩)) h1 h2)
    else if hZEq : List.zipWith tSuite.leaf idxs o.secrets = List.zipWith tSuite.leaf idxs (idxs.map sec) then
      exact .inr (extractPorsLeafCollision suite sk tree0 kp0 idxs o.secrets
        (hShape.2.2.1.trans hShape.2.1.length.symm) hSecEq hZEq)
    else
      exact .inr (extractPorsClimbCollision suite sk tree0 kp0 p.treeHeight 0 idxs _ _
        o.auth _ _ [] (.inl hZEq) h1 h2)

private def findSignedAtKey {suite : TweakableHashSuite} {hmsgXof : BaggyHmsgStream}
    {bp : BaggyParams} {sk : PqSecretKey}
    (lvl : Nat) (kp : UInt32) (tree : UInt64) :
    List (HonestBaggySignedEntry suite hmsgXof bp sk) →
      Option (HonestBaggySignedEntry suite hmsgXof bp sk)
  | [] => none
  | e :: es => if bp.pathAt e.leafIdx lvl = (kp, tree) then some e else findSignedAtKey lvl kp tree es

private theorem findSignedAtKey_some {suite : TweakableHashSuite} {hmsgXof : BaggyHmsgStream}
    {bp : BaggyParams} {sk : PqSecretKey}
    {lvl : Nat} {kp : UInt32} {tree : UInt64} :
    ∀ {log : List (HonestBaggySignedEntry suite hmsgXof bp sk)}
      {e : HonestBaggySignedEntry suite hmsgXof bp sk},
      findSignedAtKey lvl kp tree log = some e → e ∈ log ∧ bp.pathAt e.leafIdx lvl = (kp, tree)
  | [], _, h => nomatch h
  | x :: xs, e, h => by
    unfold findSignedAtKey at h
    by_cases hp : bp.pathAt x.leafIdx lvl = (kp, tree)
    · rw [ite_eq_left hp] at h; injection h with hEq; subst hEq; exact ⟨List.Mem.head _, hp⟩
    · rw [ite_eq_right hp] at h
      obtain ⟨hM, hP⟩ := findSignedAtKey_some h
      exact ⟨List.Mem.tail _ hM, hP⟩

private def extractBaggyLayers {suite : TweakableHashSuite} {hmsgXof : BaggyHmsgStream}
    {bp : BaggyParams} (hw : bp.wellFormed = true) {sk : PqSecretKey}
    (log : List (HonestBaggySignedEntry suite hmsgXof bp sk))
    (leafIdx : Nat) (hLeafLt : leafIdx < 2 ^ bp.totalHeight) :
    ∀ (lvl : Nat) (curNode : List UInt8) (layers : List BaggyLayerSig) (topRoot : List UInt8),
      lvl + layers.length = bp.numLayers →
      baggyClimbLayers suite bp sk.pkSeed leafIdx lvl curNode layers = some topRoot →
      topRoot = baggyHonestPathNode suite bp sk leafIdx bp.numLayers →
      PSum (curNode = baggyHonestPathNode suite bp sk leafIdx lvl)
        (PSum (WotsBackwardInversionWitness suite sk.pkSeed) (HashCollisionWitness suite.rawHash))
  | lvl, curNode, [], topRoot, hSum, hClimb, hTop => by
    injection hClimb with hEq
    simp only [List.length_nil, Nat.add_zero] at hSum
    rw [hEq, hTop, ← hSum]
    exact .inl rfl
  | lvl, curNode, lsig :: rest, topRoot, hSum, hClimb, hTop => by
    unfold baggyClimbLayers at hClimb
    rcases hPath : bp.pathAt leafIdx lvl with ⟨kp, tree⟩
    simp only [hPath] at hClimb
    cases hRootL : baggyLayerRoot suite bp sk.pkSeed lvl tree kp curNode lsig with
    | none => rw [hRootL] at hClimb; cases hClimb
    | some nextNode =>
      rw [hRootL] at hClimb
      have hSum' : (lvl + 1) + rest.length = bp.numLayers := by
        rw [List.length_cons] at hSum; omega
      match extractBaggyLayers hw log leafIdx hLeafLt (lvl + 1) nextNode rest topRoot hSum' hClimb hTop with
      | .inr brk => exact .inr brk
      | .inl hNextHonest =>
        if hCurEq : curNode = baggyHonestPathNode suite bp sk leafIdx lvl then
          exact .inl hCurEq
        else
          have hwUnpack := hw
          simp only [BaggyParams.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hwUnpack
          have hSubLe8 : bp.subtreeHeight ≤ 8 := hwUnpack.1.1.1.1.1.1.2
          have hTotLe62 : bp.totalHeight ≤ 62 := hwUnpack.1.1.1.2
          unfold baggyLayerRoot at hRootL
          cases hShapeG : (!decide (lsig.ctr < bp.maxGrind) || !decide (lsig.chains.length = 128) ||
              !lsig.chains.all (fun c => decide (c.length = 32)) ||
              !decide (lsig.auth.length = bp.subtreeHeight) ||
              !lsig.auth.all (fun a => decide (a.length = 32)))
          · rw [hShapeG] at hRootL
            dsimp only [Bool.false_eq_true, ↓reduceIte] at hRootL
            let dg := baggyLayerDigest suite sk.pkSeed (UInt32.ofNat lvl) tree kp curNode lsig.ctr
            let digits := extractBaseWDigits 4 128 dg
            cases hTS : checkTargetSum 4 128 192 digits
            · simp only [dg, digits, hTS] at hRootL; cases hRootL
            · simp only [dg, digits, hTS, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRootL
              let wotsLeaf := recoverWotsPkFromSig suite (baggyWotsPqParams bp) sk.pkSeed
                (UInt32.ofNat lvl) tree kp.toNat digits lsig.chains
              let honestLeaf := computeWotsPk suite (baggyWotsPqParams bp) sk
                (UInt32.ofNat lvl) tree kp.toNat
              let honestPath := buildMerkleAuthPath suite sk.pkSeed (UInt32.ofNat lvl) tree .tree
                (computeWotsPk suite (baggyWotsPqParams bp) sk (UInt32.ofNat lvl) tree)
                bp.subtreeHeight 0 kp.toNat
              have hPow32 : 2 ^ bp.subtreeHeight < 2 ^ 32 :=
                by
                  have hStep : 2 ^ bp.subtreeHeight < 2 ^ (bp.subtreeHeight + 1) := by
                    rw [Nat.pow_succ]
                    have hPos := Nat.two_pow_pos bp.subtreeHeight
                    omega
                  exact Nat.lt_of_lt_of_le hStep (Nat.pow_le_pow_right (by decide) (by omega))
              have hKpLt : kp.toNat < 2 ^ bp.subtreeHeight := by
                have hMod : (leafIdx / 2 ^ (bp.subtreeHeight * lvl)) % 2 ^ bp.subtreeHeight <
                    2 ^ bp.subtreeHeight := Nat.mod_lt _ (Nat.two_pow_pos _)
                have hKpEq : kp = UInt32.ofNat ((leafIdx / 2 ^ (bp.subtreeHeight * lvl)) %
                    2 ^ bp.subtreeHeight) := (congrArg Prod.fst hPath).symm
                rw [hKpEq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hMod hPow32)]
                exact hMod
              have hHonWalk : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat lvl) tree .tree
                  bp.subtreeHeight 0 kp.toNat honestLeaf honestPath =
                  some (baggyHonestPathNode suite bp sk leafIdx (lvl + 1)) := by
                have hW := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed
                  (UInt32.ofNat lvl) tree .tree
                  (computeWotsPk suite (baggyWotsPqParams bp) sk (UInt32.ofNat lvl) tree)
                  bp.subtreeHeight 0 kp.toNat hKpLt
                simp only [Nat.zero_mul, Nat.zero_add] at hW
                have hNodeEq : baggyHonestPathNode suite bp sk leafIdx (lvl + 1) =
                    computeMerkleNode suite sk.pkSeed (UInt32.ofNat lvl) tree .tree
                      (computeWotsPk suite (baggyWotsPqParams bp) sk (UInt32.ofNat lvl) tree)
                      bp.subtreeHeight 0 := by
                  simp only [baggyHonestPathNode, hPath, baggyHonestSubtreeRoot]
                  change computeXmssSubtreeRoot _ _ _ _ tree = _
                  exact computeXmssSubtreeRoot_eq _ _ _ _ _
                rw [hNodeEq]
                exact hW
              rw [hNextHonest] at hRootL
              if hLeafNe : wotsLeaf ≠ honestLeaf ∨ lsig.auth ≠ honestPath then
                exact .inr (.inr (walkMerkleAuthPath_collision_extract suite sk.pkSeed
                  (UInt32.ofNat lvl) tree .tree bp.subtreeHeight 0 kp.toNat hLeafNe hRootL hHonWalk))
              else
                have hSameWotsPk : wotsLeaf = honestLeaf :=
                  Decidable.of_not_not (fun h => hLeafNe (.inl h))
                match hSigned : findSignedAtKey lvl kp tree log with
                | none =>
                  exact .inr (extractUnopenedWotsLayer suite bp sk (UInt32.ofNat lvl) tree kp.toNat
                    digits lsig.chains hTS hSameWotsPk)
                | some entry =>
                  obtain ⟨_, hPathEq⟩ := findSignedAtKey_some hSigned
                  have hEntryLeafLt := (baggySelectAt_admissible hmsgXof bp _ _ _ _ entry.selected).2
                  have hlEntry : lvl < entry.sig.layers.length := by
                    rw [entry.layers_len]; omega
                  have hEntryHon := entry.honest_layers lvl hlEntry
                  dsimp only at hEntryHon
                  have hPathSym : bp.pathAt entry.leafIdx lvl = (kp, tree) := hPathEq
                  rw [hPathSym] at hEntryHon
                  let dgHon := baggyLayerDigest suite sk.pkSeed (UInt32.ofNat lvl) tree kp
                    (baggyHonestPathNode suite bp sk entry.leafIdx lvl)
                    (entry.sig.layers[lvl]'hlEntry).ctr
                  let digitsHon := extractBaseWDigits 4 128 dgHon
                  have hNodeSame : baggyHonestPathNode suite bp sk entry.leafIdx lvl =
                      baggyHonestPathNode suite bp sk leafIdx lvl := by
                    cases lvl with
                    | zero => simp only [baggyHonestPathNode, hPathSym, hPath]
                    | succ l' =>
                      unfold baggyHonestPathNode
                      have hTreeSame : (bp.pathAt entry.leafIdx l').2 = (bp.pathAt leafIdx l').2 := by
                        unfold BaggyParams.pathAt at hPathSym ⊢
                        dsimp only at hPathSym ⊢
                        have hMulS : bp.subtreeHeight * (l' + 1) =
                            bp.subtreeHeight * l' + bp.subtreeHeight := Nat.mul_succ _ _
                        have hDivE : entry.leafIdx / 2 ^ (bp.subtreeHeight * l') / 2 ^ bp.subtreeHeight =
                            entry.leafIdx / 2 ^ (bp.subtreeHeight * (l' + 1)) := by
                          rw [hMulS, Nat.pow_add, Nat.div_div_eq_div_mul]
                        have hDivL : leafIdx / 2 ^ (bp.subtreeHeight * l') / 2 ^ bp.subtreeHeight =
                            leafIdx / 2 ^ (bp.subtreeHeight * (l' + 1)) := by
                          rw [hMulS, Nat.pow_add, Nat.div_div_eq_div_mul]
                        rw [hDivE, hDivL]
                        let sE := entry.leafIdx / 2 ^ (bp.subtreeHeight * (l' + 1))
                        let sL := leafIdx / 2 ^ (bp.subtreeHeight * (l' + 1))
                        have hsE64 : sE < 2 ^ 64 :=
                          Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
                            (Nat.lt_of_lt_of_le hEntryLeafLt
                              (Nat.pow_le_pow_right (by decide) (by omega)))
                        have hsL64 : sL < 2 ^ 64 :=
                          Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
                            (Nat.lt_of_lt_of_le hLeafLt
                              (Nat.pow_le_pow_right (by decide) (by omega)))
                        have hBoth := hPathSym.trans hPath.symm
                        have h1N := congrArg UInt32.toNat (congrArg Prod.fst hBoth)
                        have h2N := congrArg UInt64.toNat (congrArg Prod.snd hBoth)
                        change (UInt32.ofNat (sE % 2 ^ bp.subtreeHeight)).toNat =
                          (UInt32.ofNat (sL % 2 ^ bp.subtreeHeight)).toNat at h1N
                        change (UInt64.ofNat (sE / 2 ^ bp.subtreeHeight)).toNat =
                          (UInt64.ofNat (sL / 2 ^ bp.subtreeHeight)).toNat at h2N
                        rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                          Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) hPow32),
                          Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) hPow32)] at h1N
                        rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat',
                          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hsE64),
                          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hsL64)] at h2N
                        have hsEq : sE = sL := by
                          have d1 := Nat.div_add_mod sE (2 ^ bp.subtreeHeight)
                          have d2 := Nat.div_add_mod sL (2 ^ bp.subtreeHeight)
                          rw [h1N, h2N] at d1
                          exact d1.symm.trans d2
                        exact congrArg UInt64.ofNat hsEq
                      simp only [baggyHonestPathNode] at *
                      rw [hTreeSame]
                  if hDigitsEq : digits = digitsHon then
                    have hDgEq : dg = dgHon :=
                      production_digits_inj ⟨4, 128, 1, 1, 0, 0, 1, true⟩ (.inl rfl) (by rw [PqHashParams.productionWellFormed_eq]; decide)
                        (thCall_length _ _ _ _ _) (thCall_length _ _ _ _ _) hDigitsEq
                    exact .inr (.inr (match thCall_binds_or_collision suite hDgEq with
                      | .inl ⟨_, _, _, hArgs⟩ =>
                        False.elim (hCurEq ((List.cons.inj hArgs).1.trans hNodeSame))
                      | .inr col => col))
                  else
                    have hHonValid : checkTargetSum (baggyWotsPqParams bp).w
                        (baggyWotsPqParams bp).ell1 (baggyWotsPqParams bp).targetSum digitsHon = true := by
                      rw [baggyWotsPqParams_eq, PqHashParams.targetSum_eq]
                      simpa only [Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv] using hEntryHon.1
                    have hForgeValid : checkTargetSum (baggyWotsPqParams bp).w
                        (baggyWotsPqParams bp).ell1 (baggyWotsPqParams bp).targetSum digits = true := by
                      rw [baggyWotsPqParams_eq, PqHashParams.targetSum_eq]
                      simpa only [Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv] using hTS
                    have hHonPkEq : recoverWotsPkFromSig suite (baggyWotsPqParams bp) sk.pkSeed
                        (UInt32.ofNat lvl) tree kp.toNat digitsHon
                        (entry.sig.layers[lvl]'hlEntry).chains = honestLeaf := by
                      rw [hEntryHon.2]
                      exact recoverWotsPkFromSig_eq_computeWotsPk suite (baggyWotsPqParams bp) sk
                        (UInt32.ofNat lvl) tree kp.toNat digitsHon hHonValid
                    exact .inr (extractPqHashForgery suite (baggyWotsPqParams bp) sk.pkSeed
                      (UInt32.ofNat lvl) tree kp.toNat digitsHon digits
                      (entry.sig.layers[lvl]'hlEntry).chains lsig.chains
                      hHonValid hForgeValid (Ne.symm hDigitsEq) (hSameWotsPk.trans hHonPkEq.symm))
          · rw [hShapeG] at hRootL; cases hRootL

private def findPreHashCollision {suite : TweakableHashSuite} {hmsgXof : BaggyHmsgStream}
    {bp : BaggyParams} {sk : PqSecretKey} (msgStar : List UInt8) :
    List (HonestBaggySignedEntry suite hmsgXof bp sk) →
      Option (HonestBaggySignedEntry suite hmsgXof bp sk)
  | [] => none
  | e :: es =>
    let pk := baggyDerivePublicKey suite bp sk
    if thPreHash suite sk.pkSeed pk.pkRoot msgStar = thPreHash suite sk.pkSeed pk.pkRoot e.msg then
      some e
    else
      findPreHashCollision msgStar es

private theorem findPreHashCollision_spec {suite : TweakableHashSuite} {hmsgXof : BaggyHmsgStream}
    {bp : BaggyParams} {sk : PqSecretKey} (msgStar : List UInt8) :
    ∀ (log : List (HonestBaggySignedEntry suite hmsgXof bp sk)),
      match findPreHashCollision msgStar log with
      | some e =>
        e ∈ log ∧
        thPreHash suite sk.pkSeed (baggyDerivePublicKey suite bp sk).pkRoot msgStar =
          thPreHash suite sk.pkSeed (baggyDerivePublicKey suite bp sk).pkRoot e.msg
      | none =>
        ∀ e ∈ log,
          thPreHash suite sk.pkSeed (baggyDerivePublicKey suite bp sk).pkRoot msgStar ≠
            thPreHash suite sk.pkSeed (baggyDerivePublicKey suite bp sk).pkRoot e.msg
  | [] => fun _ h => nomatch h
  | e :: es => by
    unfold findPreHashCollision
    dsimp only
    by_cases hEq : thPreHash suite sk.pkSeed (baggyDerivePublicKey suite bp sk).pkRoot msgStar =
        thPreHash suite sk.pkSeed (baggyDerivePublicKey suite bp sk).pkRoot e.msg
    · rw [ite_eq_left hEq]; exact ⟨List.Mem.head _, hEq⟩
    · rw [ite_eq_right hEq]
      have ih := findPreHashCollision_spec msgStar es
      cases hTail : findPreHashCollision msgStar es with
      | some e' =>
        simp only [hTail] at ih
        exact ⟨List.Mem.tail _ ih.1, ih.2⟩
      | none =>
        simp only [hTail] at ih
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hTl
        · exact hEq
        · exact ih x hTl

private def findUnopenedPorsPos {suite : TweakableHashSuite} {hmsgXof : BaggyHmsgStream}
    {bp : BaggyParams} {sk : PqSecretKey}
    (log : List (HonestBaggySignedEntry suite hmsgXof bp sk))
    (kp0 : UInt32) (tree0 : UInt64) : List Nat → Option Nat
  | [] => none
  | u :: us =>
    if log.any (fun e => decide (bp.pathAt e.leafIdx 0 = (kp0, tree0) ∧ u ∈ e.idxs)) then
      findUnopenedPorsPos log kp0 tree0 us
    else
      some u

private theorem findUnopenedPorsPos_spec {suite : TweakableHashSuite} {hmsgXof : BaggyHmsgStream}
    {bp : BaggyParams} {sk : PqSecretKey}
    (log : List (HonestBaggySignedEntry suite hmsgXof bp sk))
    (kp0 : UInt32) (tree0 : UInt64) :
    ∀ (idxs : List Nat),
      match findUnopenedPorsPos log kp0 tree0 idxs with
      | some u => u ∈ idxs ∧ ∀ e ∈ log, bp.pathAt e.leafIdx 0 = (kp0, tree0) → u ∉ e.idxs
      | none => ∀ u ∈ idxs, ∃ e ∈ log, bp.pathAt e.leafIdx 0 = (kp0, tree0) ∧ u ∈ e.idxs
  | [] => fun _ h => nomatch h
  | u :: us => by
    unfold findUnopenedPorsPos
    cases hAny : log.any (fun e => decide (bp.pathAt e.leafIdx 0 = (kp0, tree0) ∧ u ∈ e.idxs))
    · refine ⟨List.Mem.head _, fun e he hPath hu => ?_⟩
      have hTrue : log.any (fun e => decide (bp.pathAt e.leafIdx 0 = (kp0, tree0) ∧ u ∈ e.idxs)) =
          true := List.any_eq_true.mpr ⟨e, he, decide_eq_true ⟨hPath, hu⟩⟩
      rw [hTrue] at hAny; cases hAny
    · have ih := findUnopenedPorsPos_spec log kp0 tree0 us
      cases hTail : findUnopenedPorsPos log kp0 tree0 us with
      | some u' =>
        simp only [hTail] at ih
        exact ⟨List.Mem.tail _ ih.1, ih.2⟩
      | none =>
        simp only [hTail] at ih
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hTl
        · obtain ⟨e, he, hDec⟩ := List.any_eq_true.mp hAny
          exact ⟨e, he, of_decide_eq_true hDec⟩
        · exact ih x hTl

/-- **Constructive Multi-Query Hypertree-over-`PORS+FP` EUF-CMA Extractor (`0 Classical.choice`).**
    Given any multi-query honestly signed `Baggy` transcript `log` and any fresh message `msgStar`
    (`msgStar ∉ log.map (·.msg)`) accepted by `baggyVerify`, constructively extracts a typed
    `BaggyForgeryBreak` (`porsItsr`, `hashCollision`, `porsUnopenedPreimage`, or
    `wotsBackwardPreimage`). -/
def extractBaggyForgery (suite : TweakableHashSuite) (hmsgXof : BaggyHmsgStream)
    (bp : BaggyParams) (sk : PqSecretKey)
    (log : List (HonestBaggySignedEntry suite hmsgXof bp sk))
    (msgStar : List UInt8) (sigStar : BaggySig)
    (hFresh : ∀ e ∈ log, e.msg ≠ msgStar)
    (hAccept : baggyVerify suite hmsgXof bp (baggyDerivePublicKey suite bp sk) msgStar sigStar =
      true) :
    BaggyForgeryBreak suite hmsgXof bp sk log := by
  let pk := baggyDerivePublicKey suite bp sk
  unfold baggyVerify at hAccept
  cases hHdr : (!bp.wellFormed || !decide (sigStar.r.length = 32) ||
      !decide (sigStar.layers.length = bp.numLayers) ||
      !decide (sigStar.msgCtr < bp.maxGrind) ||
      !sigStar.pors.secrets.all (fun s => decide (s.length = 32)) ||
      !sigStar.pors.auth.all (fun a => decide (a.length = 32)))
  · rw [hHdr] at hAccept
    dsimp only [Bool.false_eq_true, ↓reduceIte] at hAccept
    have hw : bp.wellFormed = true := by
      cases h : bp.wellFormed
      · simp [h] at hHdr
      · rfl
    have hLayLen : sigStar.layers.length = bp.numLayers := by
      by_cases h : sigStar.layers.length = bp.numLayers
      · exact h
      · simp [hw, h] at hHdr
    let muStar := thPreHash suite pk.pkSeed pk.pkRoot msgStar
    change (match baggySelectAt hmsgXof bp pk sigStar.r muStar sigStar.msgCtr with
      | none => false
      | some (idxs, leafIdx) =>
        match porsFpRoot bp.pors (porsTweakableSuite suite pk.pkSeed (bp.pathAt leafIdx 0).2 (bp.pathAt leafIdx 0).1) idxs sigStar.pors.secrets sigStar.pors.auth with
        | none => false
        | some node0 =>
          match baggyClimbLayers suite bp pk.pkSeed leafIdx 0 node0 sigStar.layers with
          | none => false
          | some topRoot => decide (topRoot = pk.pkRoot)) = true at hAccept
    cases hSel : baggySelectAt hmsgXof bp pk sigStar.r muStar sigStar.msgCtr with
    | none => simp only [hSel, Bool.false_eq_true] at hAccept
    | some selPair =>
      simp only [hSel] at hAccept
      obtain ⟨idxsStar, leafIdx⟩ := selPair
      have hLeafLt := (baggySelectAt_admissible hmsgXof bp pk sigStar.r muStar sigStar.msgCtr hSel).2
      rcases hPath0 : bp.pathAt leafIdx 0 with ⟨kp0, tree0⟩
      simp only [hPath0] at hAccept
      cases hPors : porsFpRoot bp.pors (porsTweakableSuite suite pk.pkSeed tree0 kp0)
          idxsStar sigStar.pors.secrets sigStar.pors.auth with
      | none => simp only [hPors] at hAccept; cases hAccept
      | some node0 =>
        simp only [hPors] at hAccept
        cases hClimb : baggyClimbLayers suite bp pk.pkSeed leafIdx 0 node0 sigStar.layers with
        | none => rw [hClimb] at hAccept; cases hAccept
        | some topRoot =>
          rw [hClimb] at hAccept
          have hTopEq : topRoot = baggyHonestPathNode suite bp sk leafIdx bp.numLayers :=
            (of_decide_eq_true hAccept).trans (baggyHonestPathNode_top suite bp sk hw hLeafLt).symm
          have hSum0 : 0 + sigStar.layers.length = bp.numLayers := by rw [Nat.zero_add, hLayLen]
          match extractBaggyLayers hw log leafIdx hLeafLt 0 node0 sigStar.layers topRoot
              hSum0 hClimb hTopEq with
          | .inr (.inl inv) => exact .wotsBackwardPreimage inv
          | .inr (.inr col) => exact .hashCollision col
          | .inl hNode0Honest =>
            have hPorsHon : porsFpRoot bp.pors (porsTweakableSuite suite sk.pkSeed tree0 kp0)
                idxsStar sigStar.pors.secrets sigStar.pors.auth =
                some (baggyHonestPorsRoot suite ⟨WotsCParams.v128, 2, 16, 2 ^ 26, bp.pors⟩ sk
                  tree0 kp0) := by
              dsimp only [pk, baggyDerivePublicKey] at hPors
              rw [hPors, hNode0Honest]
              simp only [baggyHonestPathNode, hPath0, baggyHonestPorsRoot]
            match extractPorsOpeningOrCollision bp.pors suite sk tree0 kp0 idxsStar
                sigStar.pors hPorsHon with
            | .inr col => exact .hashCollision col
            | .inl ⟨hSecretsEq, _⟩ =>
              have hPreSpec := findPreHashCollision_spec (hmsgXof := hmsgXof) msgStar log
              cases hPreFind : findPreHashCollision msgStar log with
              | some eCol =>
                rw [hPreFind] at hPreSpec
                have hPreEq := hPreSpec.2
                rw [thPreHash_eq, thPreHash_eq] at hPreEq
                exact match thCall_binds_or_collision suite hPreEq with
                  | .inl ⟨_, _, _, hArgs⟩ =>
                    False.elim (hFresh eCol hPreSpec.1
                      (List.cons.inj (List.cons.inj hArgs).2).1.symm)
                  | .inr col => .hashCollision col
              | none =>
                rw [hPreFind] at hPreSpec
                have hPosSpec := findUnopenedPorsPos_spec log kp0 tree0 idxsStar
                cases hPosFind : findUnopenedPorsPos log kp0 tree0 idxsStar with
                | some u =>
                  rw [hPosFind] at hPosSpec
                  exact .porsUnopenedPreimage tree0 kp0 u
                    (porsSecretLeaf suite sk tree0 kp0 u) hPosSpec.2 rfl
                | none =>
                  rw [hPosFind] at hPosSpec
                  exact .porsItsr sigStar.r muStar sigStar.msgCtr leafIdx idxsStar hSel
                    (fun e he hFrameEq => by
                      have hListEq := encodeMultiFrame_injective hFrameEq
                      have hMuEq := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj hListEq).2).2).2).1
                      exact hPreSpec e he hMuEq)
                    (fun u hu => by simpa only [hPath0] using hPosSpec u hu)
  · rw [hHdr] at hAccept; cases hAccept

/-- Decidable check for whether a `BaggyForgeryBreak` falls into the `PORS+FP` ITSR branch,
    collision branch, or secret-preimage branch (`PORS+FP` leaf or `WOTS+C` chain). -/
def BaggyForgeryBreak.branch {suite : TweakableHashSuite} {hmsgXof : BaggyHmsgStream}
    {bp : BaggyParams} {sk : PqSecretKey}
    {log : List (HonestBaggySignedEntry suite hmsgXof bp sk)} :
    BaggyForgeryBreak suite hmsgXof bp sk log → Fin 3
  | .porsItsr .. => ⟨0, by decide⟩
  | .hashCollision _ => ⟨1, by decide⟩
  | .porsUnopenedPreimage .. => ⟨2, by decide⟩
  | .wotsBackwardPreimage _ => ⟨2, by decide⟩

/-- **`BaggySha3_128f` Multi-Query EUF-CMA Pointwise Reduction Theorem.**
    Every fresh verifying `BaggySha3_128f` signature against a multi-query transcript `log`
    constructively yields a `BaggyForgeryBreak` (`porsItsr`, `hashCollision`,
    `porsUnopenedPreimage`, or `wotsBackwardPreimage`). -/
theorem baggy_sha3_128f_multi_query_euf_cma_reduction
    (suite : TweakableHashSuite) (hmsgXof : BaggyHmsgStream) (sk : PqSecretKey)
    (log : List (HonestBaggySignedEntry suite hmsgXof BaggySha3_128f sk))
    (msgStar : List UInt8) (sigStar : BaggySig)
    (hFresh : ∀ e ∈ log, e.msg ≠ msgStar)
    (hAccept : baggyVerify suite hmsgXof BaggySha3_128f
      (baggyDerivePublicKey suite BaggySha3_128f sk) msgStar sigStar = true) :
    Nonempty (BaggyForgeryBreak suite hmsgXof BaggySha3_128f sk log) :=
  ⟨extractBaggyForgery suite hmsgXof BaggySha3_128f sk log msgStar sigStar hFresh hAccept⟩

/-- **`BaggySha3_128f` Multi-Query EUF-CMA Reduction Theorem (`Spec.GameBound` Form).**
    Over any finite coin space `Fin n`, every coin on which a multi-query `BaggySha3_128f` run
    produces a fresh verifying signature constructively triggers `itsrEvent` (`PORS+FP` subset
    cover under `TAG_BAGGY_HMSG`), `colEvent` (`HashCollisionWitness suite.rawHash`), or
    `preEvent` (unopened `PORS+FP` leaf or `WOTS+C` backward-chain preimage), bounding
    `forgerGame.winProb ≤ (εItsr + εCol) + εPre`. -/
theorem baggy_sha3_128f_euf_cma_gameBound {n : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (hmsgXof : BaggyHmsgStream)
    (skOf : Fin n → PqSecretKey)
    (logOf : (ω : Fin n) → List (HonestBaggySignedEntry suite hmsgXof BaggySha3_128f (skOf ω)))
    (forgerOut : Fin n → List UInt8 × BaggySig)
    (itsrEvent colEvent preEvent : Fin n → Bool)
    {εItsr εCol εPre : Spec.RatBound}
    (hItsr : ∀ ω (rStar muStar : List UInt8) (ctrStar leafIdx : Nat) (idxsStar : List Nat),
      baggySelectAt hmsgXof BaggySha3_128f (baggyDerivePublicKey suite BaggySha3_128f (skOf ω))
        rStar muStar ctrStar = some (idxsStar, leafIdx) →
      (∀ u ∈ idxsStar, ∃ e ∈ logOf ω,
        BaggySha3_128f.pathAt e.leafIdx 0 = BaggySha3_128f.pathAt leafIdx 0 ∧ u ∈ e.idxs) →
      itsrEvent ω = true)
    (hCol : ∀ ω, Nonempty (HashCollisionWitness suite.rawHash) → colEvent ω = true)
    (hPre : ∀ ω,
      (∃ tree0 kp0 u cand,
        (∀ e ∈ logOf ω, BaggySha3_128f.pathAt e.leafIdx 0 = (kp0, tree0) → u ∉ e.idxs) ∧
        thChainF suite (skOf ω).pkSeed (porsLeafAdrs tree0 kp0 (UInt32.ofNat u)) cand =
          (porsTweakableSuite suite (skOf ω).pkSeed tree0 kp0).leaf u
            (porsSecretLeaf suite (skOf ω) tree0 kp0 u)) ∨
      Nonempty (WotsBackwardInversionWitness suite (skOf ω).pkSeed) →
      preEvent ω = true)
    (hBItsr : Spec.GameBound (Spec.FinGame.mk hPos itsrEvent).winProb εItsr)
    (hBCol : Spec.GameBound (Spec.FinGame.mk hPos colEvent).winProb εCol)
    (hBPre : Spec.GameBound (Spec.FinGame.mk hPos preEvent).winProb εPre) :
    let forgerGame : Spec.FinGame n :=
      ⟨hPos, fun ω =>
        baggyVerify suite hmsgXof BaggySha3_128f
          (baggyDerivePublicKey suite BaggySha3_128f (skOf ω))
          (forgerOut ω).1 (forgerOut ω).2 &&
        decide ((forgerOut ω).1 ∉ (logOf ω).map HonestBaggySignedEntry.msg)⟩
    Spec.GameBound forgerGame.winProb ((εItsr.add εCol).add εPre) := by
  intro forgerGame
  refine Spec.event_le_three_reductions forgerGame
    (Spec.FinGame.mk hPos itsrEvent)
    (Spec.FinGame.mk hPos colEvent)
    (Spec.FinGame.mk hPos preEvent)
    (fun ω hWin => ?_) hBItsr hBCol hBPre
  have hAnd : (baggyVerify suite hmsgXof BaggySha3_128f
      (baggyDerivePublicKey suite BaggySha3_128f (skOf ω))
      (forgerOut ω).1 (forgerOut ω).2 &&
    decide ((forgerOut ω).1 ∉ (logOf ω).map HonestBaggySignedEntry.msg)) = true := hWin
  obtain ⟨hVer, hNotMem⟩ := Bool.and_eq_true _ _ |>.mp hAnd
  have hFresh : ∀ e ∈ logOf ω, e.msg ≠ (forgerOut ω).1 := fun e he hEq =>
    of_decide_eq_true hNotMem (List.mem_map.mpr ⟨e, he, hEq⟩)
  match extractBaggyForgery suite hmsgXof BaggySha3_128f (skOf ω) (logOf ω)
      (forgerOut ω).1 (forgerOut ω).2 hFresh hVer with
  | .porsItsr rS muS ctrS lI idxsS hSel _ hCov =>
    exact .inl (hItsr ω rS muS ctrS lI idxsS hSel hCov)
  | .hashCollision col =>
    exact .inr (.inl (hCol ω ⟨col⟩))
  | .porsUnopenedPreimage t0 kp0 u cand hUn hPr =>
    exact .inr (.inr (hPre ω (.inl ⟨t0, kp0, u, cand, hUn, hPr⟩)))
  | .wotsBackwardPreimage inv =>
    exact .inr (.inr (hPre ω (.inr ⟨inv⟩)))

#verify_constructive porsFpRoot_some_shape unsorted_rejected oversized_rejected
  noncanonical_length_rejected porsFpRoot_complete porsFpRoot_binding
  opening_against_honest_root select_admissible selected_subset_opens mem_subsetsFrom
  nodup_subsetsFrom covered_subsets_count choose_mono choose_cross
  atLeastBits_choose_of_ffTop belowBits_choose_of_ffTop revealed_count_le admissible_iff
  coverWins_length_le forgery_fraction_bound sha3_128f_ff_bits sha3_128f_binomial_bits
  sha3_128f_forgery_bound sha3_128f_millibits sha3_128f_rust_estimate
  sha3_128f_rust_estimate_sound sha3_128f_bound_fails_without_distinctness
  demo_honest_opening_accepted demo_unsorted_rejected demo_unsorted_accepted_by_lax
  porsPrfAdrs_encode_ne_porsLeafAdrs porsAdrs_encode_disjoint_from_nonPors
  porsTweakableSuite_honestTree_length PorsFpOpening.toWireBytes_length
  sha3_128f_opening_wire_le_4994 PorsFpOpening.fromWireBytes_toWireBytes_append
  PorsFpOpening.toWireBytes_prefix_injective baggySha3_128f_parity
  BaggySig.toWireBytes_length_le baggySha3_128f_sig_wire_le_71654
  BaggySig.fromWireBytes_toWireBytes baggySelectAt_admissible
  baggyHonestPathNode_top
  baggy_sha3_128f_multi_query_euf_cma_reduction baggy_sha3_128f_euf_cma_gameBound

#verify_kernel extractBaggyForgery extractPorsOpeningOrCollision

end Qsag.PorsFpSecurity
