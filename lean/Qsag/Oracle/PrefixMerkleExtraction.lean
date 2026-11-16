module
/-
# Qsag.Oracle.PrefixMerkleExtraction — extraction from the pre-challenge query log

`Qsag.Oracle.Qrom` extracts a Merkle opening from the records of the complete query log and
reads the root from the final output (`measuredMerkleFailure`, `MerkleOpeningReadout`). Nothing
there says the extracted opening existed before the verifier's challenge. This module states
the temporal experiment and proves extraction from the permitted prefix.

## The experiment

A `TwoPhaseAdversary` is a pair of deterministic adaptive oracle programs:

1. `commit` asks exactly `Q₁` queries and outputs the Merkle root together with a state;
2. the challenge `ch` is then fixed, independently of the oracle;
3. `respond st ch` asks exactly `Q₂` further queries and outputs an opening
   (position, leaf digest, authentication path);
4. the verifier recomputes the root along the path with `d` oracle evaluations.

Fewer queries are modelled by padding (`QueryProg.padTo`): a repeated address never triggers
any of the events counted below.

## What is proved

* `prefixCommitted A L lvl H` is the opening table extracted from the Phase-1 records and the
  Phase-1 root. Its definition has no challenge argument and it does not change when the
  oracle is reprogrammed outside the Phase-1 log (`prefixCommitted_reprogram_of_fresh`).
* `prefixFailure_cover`: an accepted opening that differs from the prefix-extracted one forces
  a fresh-address hit at one of the `Q₁ + Q₂ + d` steps of the run. A Phase-1 step hits an
  earlier Phase-1 answer (collision). A Phase-2 step or a verifier evaluation hits a target
  fixed by Phase 1. Phase-2 queries are charged as their own `Q₂` terms of the union bound;
  their records are never used for extraction.
* `prefix_extraction_failure_bound`: over a uniform oracle `Fin cardX → BitVec w`, for every
  fixed challenge, the failing oracles number at most
  `(d + Q₂ + Q₁) * (3 * Q₁ + 1) / 2 ^ w` of all oracles.
* `lateOpen_final_log_extracts_uncommitted`: extraction from the final log returns an opening
  for a root whose only preimage query was made after the challenge, while prefix extraction
  returns `none` and the run is classified as a failure.

## Scope

The adversary here is classical: its queries are addresses, not superpositions. The transfer
of measured-log statements to coherent executions is exactly as scoped in `Qrom.lean`, under
the caller-supplied premise `ClassicalQueryAddresses` (`Qrom.lean:5913`); this module does not
weaken, discharge or use that premise, and it proves nothing about superposition queries.
A challenge derived from the oracle (Fiat–Shamir squeeze) is not modelled: `ch` is a parameter
independent of `H`.

`pathRoot`, `pathPoints`, `records`, `childTargets` have the bodies of `merkleRootFromPath`
read through `MerkleAddressLayout.hash`, `merklePathPoints`, `merkleRecords`,
`merkleChildTargets` in `Qrom.lean`; those bodies are not exposed there, so they are restated.
The extractor itself is `Qsag.extractOnlineMerkleOpening`, unchanged.
-/
public import Qsag.Oracle.Qrom
public section
namespace Qsag.PrefixMerkleExtraction
set_option autoImplicit false

/-! ## §1. Deterministic adaptive query programs with an exact query count -/

/-- A deterministic adaptive oracle program that asks exactly `q` queries. -/
inductive QueryProg (X Y α : Type) : Nat → Type where
  | ret : α → QueryProg X Y α 0
  | ask {q : Nat} : X → (Y → QueryProg X Y α q) → QueryProg X Y α (q + 1)

namespace QueryProg
variable {X Y α β : Type}

/-- Output of the program under oracle `H`. -/
def eval (H : X → Y) : {q : Nat} → QueryProg X Y α q → α
  | _, .ret a => a
  | _, .ask x k => eval H (k (H x))

/-- Query addresses under oracle `H`, oldest first. -/
def log (H : X → Y) : {q : Nat} → QueryProg X Y α q → List X
  | _, .ret _ => []
  | _, .ask x k => x :: log H (k (H x))

/-- Sequential composition: run `p`, then the program chosen by its output. -/
def bind : {q : Nat} → QueryProg X Y α q → {r : Nat} → (α → QueryProg X Y β r) →
    QueryProg X Y β (r + q)
  | _, .ret a, _, f => f a
  | _, .ask x k, _, f => .ask x (fun y => bind (k y) f)

/-- `k` queries to a fixed address, discarding the answers. -/
def idle (x0 : X) : (k : Nat) → α → QueryProg X Y α k
  | 0, a => .ret a
  | k + 1, a => .ask x0 (fun _ => idle x0 k a)

/-- Pad a program with `k` trailing queries to a fixed address. -/
def padTo (x0 : X) (k : Nat) {q : Nat} (p : QueryProg X Y α q) : QueryProg X Y α (k + q) :=
  p.bind (idle x0 k)

theorem eval_ret (H : X → Y) (a : α) : (QueryProg.ret a : QueryProg X Y α 0).eval H = a := by rfl

theorem eval_ask (H : X → Y) {q : Nat} (x : X) (k : Y → QueryProg X Y α q) :
    (QueryProg.ask x k).eval H = (k (H x)).eval H := by rfl

theorem log_ret (H : X → Y) (a : α) : (QueryProg.ret a : QueryProg X Y α 0).log H = [] := by rfl

theorem log_ask (H : X → Y) {q : Nat} (x : X) (k : Y → QueryProg X Y α q) :
    (QueryProg.ask x k).log H = x :: (k (H x)).log H := by rfl

theorem log_length (H : X → Y) {q : Nat} (p : QueryProg X Y α q) : (p.log H).length = q := by
  induction p with
  | ret a => rfl
  | ask x k ih => exact congrArg Nat.succ (ih (H x))

theorem eval_bind (H : X → Y) {q : Nat} (p : QueryProg X Y α q) {r : Nat}
    (f : α → QueryProg X Y β r) : (p.bind f).eval H = (f (p.eval H)).eval H := by
  induction p with
  | ret a => rfl
  | ask x k ih => exact ih (H x)

theorem log_bind (H : X → Y) {q : Nat} (p : QueryProg X Y α q) {r : Nat}
    (f : α → QueryProg X Y β r) : (p.bind f).log H = p.log H ++ (f (p.eval H)).log H := by
  induction p with
  | ret a => rfl
  | ask x k ih => exact congrArg (fun l => x :: l) (ih (H x))

theorem eval_idle (H : X → Y) (x0 : X) : ∀ (k : Nat) (a : α),
    (idle (Y := Y) x0 k a).eval H = a
  | 0, _ => rfl
  | k + 1, a => eval_idle H x0 k a

theorem eval_padTo (H : X → Y) (x0 : X) (k : Nat) {q : Nat} (p : QueryProg X Y α q) :
    (p.padTo x0 k).eval H = p.eval H :=
  (eval_bind H p (idle x0 k)).trans (eval_idle H x0 k _)

end QueryProg

/-! ## §2. List facts used for first occurrences and prefixes -/

theorem getElem?_lt_length {β : Type} : ∀ (l : List β) (s : Nat) (a : β),
    l[s]? = some a → s < l.length
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, _ => Nat.succ_pos _
  | _ :: t, s + 1, a, h => Nat.succ_lt_succ (getElem?_lt_length t s a h)

theorem getElem?_none_of_length_le {β : Type} : ∀ (l : List β) (s : Nat),
    l.length ≤ s → l[s]? = none
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: t, s + 1, h => getElem?_none_of_length_le t s (Nat.le_of_succ_le_succ h)

theorem length_le_of_getElem?_none {β : Type} : ∀ (l : List β) (s : Nat),
    l[s]? = none → l.length ≤ s
  | [], _, _ => Nat.zero_le _
  | _ :: _, 0, h => nomatch h
  | _ :: t, s + 1, h => Nat.succ_le_succ (length_le_of_getElem?_none t s h)

/-- Two lists with equal `(s + 1)`-prefixes have equal `s`-prefixes and equal entries at `s`. -/
theorem take_of_take_succ {β : Type} : ∀ (s : Nat) (l l' : List β),
    l.take (s + 1) = l'.take (s + 1) → l.take s = l'.take s ∧ l[s]? = l'[s]?
  | 0, [], [], _ => ⟨rfl, rfl⟩
  | 0, [], _ :: _, h => nomatch h
  | 0, _ :: _, [], h => nomatch h
  | 0, x :: _, y :: _, h => ⟨rfl, congrArg some (List.cons.inj h).1⟩
  | _ + 1, [], [], _ => ⟨rfl, rfl⟩
  | _ + 1, [], _ :: _, h => nomatch h
  | _ + 1, _ :: _, [], h => nomatch h
  | s + 1, x :: t, y :: t', h => by
    have hc := List.cons.inj h
    have ih := take_of_take_succ s t t' hc.2
    exact ⟨by show x :: t.take s = y :: t'.take s; rw [hc.1, ih.1], ih.2⟩

/-- Every member of a list has a first occurrence. -/
theorem first_occurrence {β : Type} [DecidableEq β] (a : β) : ∀ (l : List β), a ∈ l →
    ∃ s, l[s]? = some a ∧ ¬ (a ∈ l.take s)
  | [], h => nomatch h
  | x :: t, h => by
    by_cases hax : a = x
    · exact ⟨0, congrArg some hax.symm, fun hm => nomatch hm⟩
    · have ht : a ∈ t := by
        cases h with
        | head => exact absurd rfl hax
        | tail _ h' => exact h'
      obtain ⟨s, hs, hfr⟩ := first_occurrence a t ht
      refine ⟨s + 1, hs, fun hm => ?_⟩
      have hm' : a ∈ x :: t.take s := hm
      cases hm' with
      | head => exact hax rfl
      | tail _ h' => exact hfr h'

/-- An entry at an earlier index lies in every longer prefix. -/
theorem mem_take_of_getElem? {β : Type} : ∀ (l : List β) (i j : Nat) (x : β),
    l[i]? = some x → i < j → x ∈ l.take j
  | [], _, _, _, h, _ => nomatch h
  | _ :: _, _, 0, _, _, hij => absurd hij (Nat.not_lt_zero _)
  | y :: t, 0, j + 1, x, h, _ => by
    have hyx : y = x := Option.some.inj h
    show x ∈ y :: t.take j
    rw [hyx]
    exact .head _
  | y :: t, i + 1, j + 1, x, h, hij => by
    show x ∈ y :: t.take j
    exact .tail _ (mem_take_of_getElem? t i j x h (Nat.lt_of_succ_lt_succ hij))

/-- Inside the first list, an appended list has the same entries and prefixes. -/
theorem append_getElem?_take {β : Type} (l₂ : List β) : ∀ (l₁ : List β) (j : Nat) (y : β),
    l₁[j]? = some y → (l₁ ++ l₂)[j]? = some y ∧ (l₁ ++ l₂).take j = l₁.take j
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, h => ⟨h, rfl⟩
  | x :: t, j + 1, y, h => by
    have ih := append_getElem?_take l₂ t j y h
    exact ⟨ih.1, by show x :: (t ++ l₂).take j = x :: t.take j; rw [ih.2]⟩

/-- An entry of `l₁ ++ l₂` that is not a member of `l₁` sits at or beyond `l₁.length`. -/
theorem append_index_ge {β : Type} (l₂ : List β) (a : β) : ∀ (l₁ : List β) (s : Nat),
    (l₁ ++ l₂)[s]? = some a → ¬ (a ∈ l₁) → ¬ (s < l₁.length)
  | [], _, _, _ => Nat.not_lt_zero _
  | x :: _, 0, h, hn => by
    have hxa : x = a := Option.some.inj h
    exact absurd (hxa ▸ List.Mem.head _) hn
  | _ :: t, s + 1, h, hn => fun hlt =>
    append_index_ge l₂ a t s h (fun hm => hn (.tail _ hm)) (Nat.lt_of_succ_lt_succ hlt)

/-- A prefix reaching past `l₁` contains all of `l₁`. -/
theorem mem_take_append_of_ge {β : Type} (l₂ : List β) : ∀ (l₁ : List β) (s : Nat),
    ¬ (s < l₁.length) → ∀ x, x ∈ l₁ → x ∈ (l₁ ++ l₂).take s
  | [], _, _, _, hx => nomatch hx
  | _ :: _, 0, h, _, _ => absurd (Nat.succ_pos _) h
  | y :: t, s + 1, h, x, hx => by
    show x ∈ y :: (t ++ l₂).take s
    cases hx with
    | head => exact .head _
    | tail _ hx' =>
      exact .tail _ (mem_take_append_of_ge l₂ t s (fun hlt => h (Nat.succ_lt_succ hlt)) x hx')

theorem length_take_le_self {β : Type} : ∀ (s : Nat) (l : List β), (l.take s).length ≤ s
  | 0, _ => Nat.le_refl 0
  | _ + 1, [] => Nat.zero_le _
  | s + 1, _ :: t => Nat.succ_le_succ (length_take_le_self s t)

theorem not_mem_of_listHasElem_false {β : Type} [DecidableEq β] {x : β} {ys : List β}
    (h : listHasElem x ys = false) : ¬ (x ∈ ys) :=
  fun hm => Bool.noConfusion (h.symm.trans ((listHasElem_eq_true_iff x ys).mpr hm))

theorem listHasElem_false_of_not_mem {β : Type} [DecidableEq β] {x : β} {ys : List β}
    (h : ¬ (x ∈ ys)) : listHasElem x ys = false := by
  cases hc : listHasElem x ys
  · rfl
  · exact absurd ((listHasElem_eq_true_iff x ys).mp hc) h

theorem le_qsum_term {n : Nat} (f : Fin n → Nat) (k : Fin n) : f k ≤ qsum n f := by
  rw [← qsum_ite_eq n k (f k)]
  refine qsum_le_qsum (fun i => ?_)
  by_cases h : i = k
  · rw [ite_eq_left h, h]
    exact Nat.le_refl _
  · rw [ite_eq_right h]
    exact Nat.zero_le _

/-! ## §3. Locality of a run under reprogramming at an unqueried address -/

section Locality
variable {n w : Nat} {α : Type}

/-- Reprogramming the oracle at an address outside the first `s` queries leaves the first
    `s + 1` query addresses unchanged. -/
theorem log_take_reprogram (H : Fin n → BitVec w) (a : Fin n) (c : BitVec w) {q : Nat}
    (p : QueryProg (Fin n) (BitVec w) α q) : ∀ s : Nat, ¬ (a ∈ (p.log H).take s) →
      (p.log (reprogramOracle H a c)).take (s + 1) = (p.log H).take (s + 1) := by
  induction p with
  | ret r => intro s _; rfl
  | ask x k ih =>
    intro s hs
    cases s with
    | zero => rfl
    | succ s =>
      have hs' : ¬ (a ∈ x :: ((k (H x)).log H).take s) := hs
      have hxa : x ≠ a := fun h => hs' (h ▸ List.Mem.head _)
      show x :: ((k (reprogramOracle H a c x)).log (reprogramOracle H a c)).take (s + 1) =
        x :: ((k (H x)).log H).take (s + 1)
      rw [reprogramOracle_of_ne H a c x hxa]
      exact congrArg (fun l => x :: l) (ih (H x) s (fun hm => hs' (.tail _ hm)))

/-- Reprogramming the oracle at an address the program never queries changes neither its
    output nor its log. -/
theorem eval_log_reprogram (H : Fin n → BitVec w) (a : Fin n) (c : BitVec w) {q : Nat}
    (p : QueryProg (Fin n) (BitVec w) α q) : ¬ (a ∈ p.log H) →
      p.eval (reprogramOracle H a c) = p.eval H ∧ p.log (reprogramOracle H a c) = p.log H := by
  induction p with
  | ret r => intro _; exact ⟨rfl, rfl⟩
  | ask x k ih =>
    intro hs
    have hs' : ¬ (a ∈ x :: (k (H x)).log H) := hs
    have hxa : x ≠ a := fun h => hs' (h ▸ List.Mem.head _)
    have h := ih (H x) (fun hm => hs' (.tail _ hm))
    constructor
    · show (k (reprogramOracle H a c x)).eval (reprogramOracle H a c) = (k (H x)).eval H
      rw [reprogramOracle_of_ne H a c x hxa]
      exact h.1
    · show x :: (k (reprogramOracle H a c x)).log (reprogramOracle H a c) =
        x :: (k (H x)).log H
      rw [reprogramOracle_of_ne H a c x hxa, h.2]

end Locality

/-! ## §4. A fresh-address bound for oracle-dependent addresses -/

/-- Lazy sampling at an oracle-dependent address `p H`. Unlike `Qsag.uniform_fresh_point_bound`
    the invariance hypotheses are required only where the flag `ok H` holds, which is what an
    adaptive run provides: the address of a query is stable under reprogramming at that address
    only if the address was not asked before. -/
theorem conditional_fresh_point_bound (w n : Nat)
    (p : (Fin n → BitVec w) → Fin n) (ok : (Fin n → BitVec w) → Bool)
    (T : (Fin n → BitVec w) → List (BitVec w)) (K : Nat)
    (hp : ∀ H ch, ok H = true → p (reprogramOracle H (p H) ch) = p H)
    (hok : ∀ H ch, ok H = true → ok (reprogramOracle H (p H) ch) = true)
    (hT : ∀ H ch, ok H = true → T (reprogramOracle H (p H) ch) = T H)
    (hK : ∀ H, ok H = true → (T H).length ≤ K) :
    2 ^ w * uniformOracleSum w n (fun H =>
      if (ok H && listHasElem (H (p H)) (T H)) = true then 1 else 0) ≤
      K * uniformOracleSum w n (fun _ => 1) := by
  let g : (Fin n → BitVec w) → Nat := fun H =>
    if (ok H && listHasElem (H (p H)) (T H)) = true then 1 else 0
  let f : Fin n → (Fin n → BitVec w) → Nat := fun x H => if x = p H then g H else 0
  have hDecomp : ∀ H, g H = qsum n (fun x => f x H) :=
    fun H => (qsum_ite_eq n (p H) (g H)).symm
  have hBack : ∀ (H : Fin n → BitVec w) (x : Fin n) (ch : BitVec w),
      x = p (reprogramOracle H x ch) → ok (reprogramOracle H x ch) = true →
      x = p H ∧ ok H = true := by
    intro H x ch hx hOk'
    have h1 := hp (reprogramOracle H x ch) (H x) hOk'
    have h2 := hok (reprogramOracle H x ch) (H x) hOk'
    rw [← hx, reprogramOracle_undo] at h1 h2
    exact ⟨h1.symm, h2⟩
  have hPt : ∀ x H, qsum (2 ^ w) (fun j => f x (reprogramOracle H x (BitVec.ofFin j))) ≤
      (if x = p H then K * 1 else 0) := by
    intro x H
    have hZero : ¬ (x = p H ∧ ok H = true) →
        ∀ j : Fin (2 ^ w), f x (reprogramOracle H x (BitVec.ofFin j)) = 0 := by
      intro hNot j
      show (if x = p (reprogramOracle H x (BitVec.ofFin j)) then
        g (reprogramOracle H x (BitVec.ofFin j)) else 0) = 0
      by_cases hxj : x = p (reprogramOracle H x (BitVec.ofFin j))
      · rw [ite_eq_left hxj]
        show (if (ok (reprogramOracle H x (BitVec.ofFin j)) &&
          listHasElem (reprogramOracle H x (BitVec.ofFin j)
            (p (reprogramOracle H x (BitVec.ofFin j))))
            (T (reprogramOracle H x (BitVec.ofFin j)))) = true then 1 else 0) = 0
        cases hOkj : ok (reprogramOracle H x (BitVec.ofFin j))
        · rfl
        · exact absurd (hBack H x _ hxj hOkj) hNot
      · exact ite_eq_right hxj
    by_cases hx : x = p H
    · rw [ite_eq_left hx]
      cases hOk : ok H with
      | false =>
        have hz := hZero (fun h => Bool.noConfusion (hOk.symm.trans h.2))
        rw [qsum_congr hz, qsum_const, Nat.mul_zero]
        exact Nat.zero_le _
      | true =>
        subst hx
        have hEq : ∀ j : Fin (2 ^ w),
            f (p H) (reprogramOracle H (p H) (BitVec.ofFin j)) =
              (if listHasElem (BitVec.ofFin j) (T H) = true then 1 else 0) := by
          intro j
          simp only [f, g, hp H _ hOk, hok H _ hOk, hT H _ hOk,
            reprogramOracle_self, Bool.true_and, ↓reduceIte]
        rw [qsum_congr hEq, Nat.mul_one]
        exact Nat.le_trans (qsum_ofFin_listHasElem_le_length w (T H)) (hK H hOk)
    · rw [ite_eq_right hx]
      have hz := hZero (fun h => hx h.1)
      rw [qsum_congr hz, qsum_const, Nat.mul_zero]
      exact Nat.le_refl 0
  have h1 : 2 ^ w * uniformOracleSum w n g =
      qsum n (fun x => uniformOracleSum w n (fun H =>
        qsum (2 ^ w) (fun j => f x (reprogramOracle H x (BitVec.ofFin j))))) := by
    rw [uniformOracleSum_congr w n g _ hDecomp, uniformOracleSum_qsum w n n (fun H x => f x H),
      ← qsum_mul_left]
    exact qsum_congr (fun x => (uniformOracleSum_resample w n x (f x)).symm)
  have h2 : qsum n (fun x => uniformOracleSum w n (fun H =>
        qsum (2 ^ w) (fun j => f x (reprogramOracle H x (BitVec.ofFin j))))) ≤
      qsum n (fun x => uniformOracleSum w n (fun H => if x = p H then K * 1 else 0)) :=
    qsum_le_qsum (fun x => uniformOracleSum_le w n _ _ (hPt x))
  have h3 : qsum n (fun x => uniformOracleSum w n (fun H =>
        if x = p H then K * 1 else 0)) = K * uniformOracleSum w n (fun _ => 1) := by
    rw [← uniformOracleSum_qsum w n n (fun H x => if x = p H then K * 1 else 0),
      uniformOracleSum_congr w n _ _ (fun H => qsum_ite_eq n (p H) (K * 1)),
      uniformOracleSum_mul]
  show 2 ^ w * uniformOracleSum w n g ≤ K * uniformOracleSum w n (fun _ => 1)
  rw [h1, ← h3]
  exact h2

/-! ## §5. Merkle paths, records and the classification of an accepted opening -/

section Merkle
variable {cardX w : Nat}

/-- Oracle address of the compression step that hashes `cur` with its sibling. -/
def stepAddr (L : MerkleAddressLayout cardX w) (lvl idx : Nat) (cur sib : BitVec w) :
    Fin cardX :=
  L.encode lvl (idx / 2) (if idx % 2 = 0 then cur else sib) (if idx % 2 = 0 then sib else cur)

/-- Root recomputed from a node digest and its authentication path through the oracle. -/
def pathRoot (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) :
    Nat → Nat → BitVec w → List (BitVec w) → BitVec w
  | _, _, cur, [] => cur
  | lvl, idx, cur, sib :: rest =>
    pathRoot L H (lvl + 1) (idx / 2) (H (stepAddr L lvl idx cur sib)) rest

/-- Oracle addresses evaluated by `pathRoot`, leaf side first. -/
def pathPoints (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) :
    Nat → Nat → BitVec w → List (BitVec w) → List (Fin cardX)
  | _, _, _, [] => []
  | lvl, idx, cur, sib :: rest =>
    stepAddr L lvl idx cur sib ::
      pathPoints L H (lvl + 1) (idx / 2) (H (stepAddr L lvl idx cur sib)) rest

theorem pathRoot_nil (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w)
    (lvl idx : Nat) (cur : BitVec w) : pathRoot L H lvl idx cur [] = cur := by rfl

theorem pathRoot_cons (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w)
    (lvl idx : Nat) (cur sib : BitVec w) (rest : List (BitVec w)) :
    pathRoot L H lvl idx cur (sib :: rest) =
      pathRoot L H (lvl + 1) (idx / 2) (H (stepAddr L lvl idx cur sib)) rest := by rfl

/-- The classical record of one query, if its address is a compression input. -/
def recordOf (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) (x : Fin cardX) :
    Option (RecordedMerkleQuery (BitVec w)) :=
  match L.decode x with
  | none => none
  | some (l, n, u, v) => some ⟨l, n, u, v, H x⟩

/-- Records of a query log. -/
def records (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) :
    List (Fin cardX) → List (RecordedMerkleQuery (BitVec w))
  | [] => []
  | x :: xs =>
    match recordOf L H x with
    | none => records L H xs
    | some q => q :: records L H xs

theorem records_nil (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) :
    records L H [] = [] := by rfl

theorem recordOf_some (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w)
    (x : Fin cardX) (q : RecordedMerkleQuery (BitVec w)) (h : recordOf L H x = some q) :
    L.decode x = some (q.lvl, q.node, q.left, q.right) ∧ q.out = H x := by
  unfold recordOf at h
  cases hd : L.decode x with
  | none => rw [hd] at h; cases h
  | some τ =>
    obtain ⟨l, n, u, v⟩ := τ
    rw [hd] at h
    have h' : some (⟨l, n, u, v, H x⟩ : RecordedMerkleQuery (BitVec w)) = some q := h
    cases h'
    exact ⟨rfl, rfl⟩

theorem recordOf_of_decode (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w)
    (x : Fin cardX) (l n : Nat) (u v : BitVec w) (h : L.decode x = some (l, n, u, v)) :
    recordOf L H x = some ⟨l, n, u, v, H x⟩ := by
  unfold recordOf
  rw [h]

theorem records_cons_some (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w)
    (x : Fin cardX) (xs : List (Fin cardX)) (q : RecordedMerkleQuery (BitVec w))
    (h : recordOf L H x = some q) : records L H (x :: xs) = q :: records L H xs := by
  show (match recordOf L H x with
    | none => records L H xs
    | some q => q :: records L H xs) = _
  rw [h]

theorem records_cons_none (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w)
    (x : Fin cardX) (xs : List (Fin cardX)) (h : recordOf L H x = none) :
    records L H (x :: xs) = records L H xs := by
  show (match recordOf L H x with
    | none => records L H xs
    | some q => q :: records L H xs) = _
  rw [h]

theorem mem_records (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) :
    ∀ (xs : List (Fin cardX)) (q : RecordedMerkleQuery (BitVec w)), q ∈ records L H xs →
      ∃ x, x ∈ xs ∧ recordOf L H x = some q
  | [], _, h => nomatch h
  | y :: ys, q, h => by
    cases hr : recordOf L H y with
    | none =>
      rw [records_cons_none L H y ys hr] at h
      obtain ⟨x, hx, hq⟩ := mem_records L H ys q h
      exact ⟨x, .tail _ hx, hq⟩
    | some q' =>
      rw [records_cons_some L H y ys q' hr] at h
      cases h with
      | head => exact ⟨y, .head _, hr⟩
      | tail _ h' =>
        obtain ⟨x, hx, hq⟩ := mem_records L H ys q h'
        exact ⟨x, .tail _ hx, hq⟩

theorem mem_records_of (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) :
    ∀ (xs : List (Fin cardX)) (x : Fin cardX) (q : RecordedMerkleQuery (BitVec w)),
      x ∈ xs → recordOf L H x = some q → q ∈ records L H xs
  | [], _, _, h, _ => nomatch h
  | y :: ys, x, q, h, hq => by
    cases h with
    | head =>
      rw [records_cons_some L H y ys q hq]
      exact .head _
    | tail _ h' =>
      have ih := mem_records_of L H ys x q h' hq
      cases hr : recordOf L H y with
      | none => rw [records_cons_none L H y ys hr]; exact ih
      | some q' => rw [records_cons_some L H y ys q' hr]; exact .tail _ ih

theorem records_length_le (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) :
    ∀ (xs : List (Fin cardX)), (records L H xs).length ≤ xs.length
  | [] => Nat.le_refl 0
  | y :: ys => by
    have ih := records_length_le L H ys
    cases hr : recordOf L H y with
    | none => rw [records_cons_none L H y ys hr]; exact Nat.le_succ_of_le ih
    | some q' => rw [records_cons_some L H y ys q' hr]; exact Nat.succ_le_succ ih

/-- Records do not change when the oracle is reprogrammed at an address outside the log. -/
theorem records_reprogram_of_fresh (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (a : Fin cardX) (c : BitVec w) :
    ∀ (xs : List (Fin cardX)), ¬ (a ∈ xs) →
      records L (reprogramOracle H a c) xs = records L H xs
  | [], _ => rfl
  | y :: ys, h => by
    have hya : y ≠ a := fun he => h (he ▸ List.Mem.head _)
    have hRec : recordOf L (reprogramOracle H a c) y = recordOf L H y := by
      unfold recordOf
      rw [reprogramOracle_of_ne H a c y hya]
    have ih := records_reprogram_of_fresh L H a c ys (fun hm => h (.tail _ hm))
    cases hr : recordOf L H y with
    | none =>
      rw [records_cons_none L H y ys hr, records_cons_none L _ y ys (hRec.trans hr), ih]
    | some q' =>
      rw [records_cons_some L H y ys q' hr, records_cons_some L _ y ys q' (hRec.trans hr), ih]

/-- Child digests named in a list of records. -/
def childTargets {D : Type} : List (RecordedMerkleQuery D) → List D
  | [] => []
  | q :: qs => q.left :: q.right :: childTargets qs

theorem childTargets_length {D : Type} : ∀ (qs : List (RecordedMerkleQuery D)),
    (childTargets qs).length = 2 * qs.length
  | [] => rfl
  | _ :: qs => by
    show (childTargets qs).length + 1 + 1 = 2 * (qs.length + 1)
    rw [childTargets_length qs]
    omega

theorem mem_childTargets_of_mem {D : Type} {q : RecordedMerkleQuery D} :
    ∀ {qs : List (RecordedMerkleQuery D)}, q ∈ qs →
      q.left ∈ childTargets qs ∧ q.right ∈ childTargets qs
  | [], h => nomatch h
  | _ :: _, h => by
    cases h with
    | head => exact ⟨.head _, .tail _ (.head _)⟩
    | tail _ h' =>
      obtain ⟨hl, hr⟩ := mem_childTargets_of_mem h'
      exact ⟨.tail _ (.tail _ hl), .tail _ (.tail _ hr)⟩

/-- A digest extracted at positive depth is a child named in some record. -/
theorem extract_succ_child {D : Type} [DecidableEq D]
    (rt : D) (queries : List (RecordedMerkleQuery D))
    (lvl depth idx : Nat) (val : D) (pth : List D)
    (h : extractOnlineMerkleOpening rt queries lvl (depth + 1) idx = some (val, pth)) :
    val ∈ childTargets queries := by
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
      obtain ⟨hL, hR⟩ := mem_childTargets_of_mem (findFirst_some_spec _ hFind).1
      by_cases hPar : idx % 2 = 0
      · simp only [hPar, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact hL
      · simp only [hPar, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact hR

/-- Targets fixed by a query log and a root: the root, the children named in the records of
    the log, and the answers in the log. -/
def prefixTargets (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w)
    (xs : List (Fin cardX)) (rt : BitVec w) : List (BitVec w) :=
  rt :: (childTargets (records L H xs) ++ xs.map H)

theorem prefixTargets_length (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w)
    (xs : List (Fin cardX)) (rt : BitVec w) :
    (prefixTargets L H xs rt).length ≤ 3 * xs.length + 1 := by
  have hRec := records_length_le L H xs
  show (childTargets (records L H xs) ++ xs.map H).length + 1 ≤ 3 * xs.length + 1
  rw [List.length_append, childTargets_length, List.length_map]
  omega

theorem prefixTargets_reprogram_of_fresh (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (a : Fin cardX) (c : BitVec w) (xs : List (Fin cardX))
    (rt : BitVec w) (h : ¬ (a ∈ xs)) :
    prefixTargets L (reprogramOracle H a c) xs rt = prefixTargets L H xs rt := by
  show rt :: (childTargets (records L (reprogramOracle H a c) xs) ++
    xs.map (reprogramOracle H a c)) = rt :: (childTargets (records L H xs) ++ xs.map H)
  rw [records_reprogram_of_fresh L H a c xs h,
    map_reprogram_of_fresh H a c xs (listHasElem_false_of_not_mem h)]

/-- **Classification against an arbitrary log.** An opening that verifies against the oracle
    either equals the opening extracted from the records of the log `xs`, or the verifier
    evaluated an address outside `xs` whose answer lies in the targets fixed by `xs`, or two
    distinct addresses of `xs` received the same answer. `xs` is any list: below it is the
    Phase-1 log, not the final one. -/
theorem prefix_opening_classification (L : MerkleAddressLayout cardX w)
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (rt : BitVec w) :
    ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w),
    lvl + path.length ≤ L.levels → idx < L.nodes →
    pathRoot L H lvl idx cur path = rt →
    extractOnlineMerkleOpening rt (records L H xs) lvl path.length idx = some (cur, path) ∨
    (∃ a, a ∈ pathPoints L H lvl idx cur path ∧ ¬ (a ∈ xs) ∧
      H a ∈ prefixTargets L H xs rt) ∨
    (∃ x x', x ∈ xs ∧ x' ∈ xs ∧ x ≠ x' ∧ H x = H x')
  | [], lvl, idx, cur, _, _, hRoot => by
    have hEq : cur = rt := hRoot
    subst hEq
    exact Or.inl rfl
  | sib :: rest, lvl, idx, cur, hLvl, hIdx, hRoot => by
    have hLen : (sib :: rest).length = rest.length + 1 := rfl
    have hl : lvl < L.levels := by omega
    have hn : idx / 2 < L.nodes := Nat.lt_of_le_of_lt (Nat.div_le_self idx 2) hIdx
    let lCh := if idx % 2 = 0 then cur else sib
    let rCh := if idx % 2 = 0 then sib else cur
    let a := L.encode lvl (idx / 2) lCh rCh
    let parent := H a
    have hRoot' : pathRoot L H (lvl + 1) (idx / 2) parent rest = rt := hRoot
    have hDecA : L.decode a = some (lvl, idx / 2, lCh, rCh) :=
      L.decode_encode lvl (idx / 2) lCh rCh hl hn
    have hParentTarget : extractOnlineMerkleOpening rt (records L H xs) (lvl + 1)
        rest.length (idx / 2) = some (parent, rest) →
        parent ∈ prefixTargets L H xs rt := by
      intro hExtUp
      cases rest with
      | nil =>
        have hPar : parent = rt := by
          simp only [List.length_nil, extractOnlineMerkleOpening, Option.some.injEq,
            Prod.mk.injEq] at hExtUp
          exact hExtUp.1.symm
        rw [hPar]
        exact .head _
      | cons s tl =>
        exact .tail _ (List.mem_append.mpr (Or.inl
          (extract_succ_child rt (records L H xs) (lvl + 1) tl.length (idx / 2) parent _
            hExtUp)))
    rcases prefix_opening_classification L H xs rt rest (lvl + 1) (idx / 2) parent
        (by omega) hn hRoot' with hExtUp | ⟨a', ha', hFresh, hHit⟩ | hColl
    · let pred := fun q : RecordedMerkleQuery (BitVec w) =>
        decide (q.lvl = lvl) && decide (q.node = idx / 2) && decide (q.out = parent)
      cases hFind : findFirst pred (records L H xs) with
      | none =>
        have hFreshA : ¬ (a ∈ xs) := by
          intro haMem
          have hMemRec := mem_records_of L H xs a _ haMem
            (recordOf_of_decode L H a lvl (idx / 2) lCh rCh hDecA)
          have hFalse := findFirst_none_spec pred hFind _ hMemRec
          simp only [pred, parent, decide_true, Bool.and_self, Bool.true_eq_false] at hFalse
        exact Or.inr (Or.inl ⟨a, .head _, hFreshA, hParentTarget hExtUp⟩)
      | some q =>
        obtain ⟨hqMem, hqPred⟩ := findFirst_some_spec pred hFind
        simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hqPred
        obtain ⟨⟨hqLvl, hqNode⟩, hqOut⟩ := hqPred
        obtain ⟨x, hxMem, hxRec⟩ := mem_records L H xs q hqMem
        obtain ⟨hDecX, hOutX⟩ := recordOf_some L H x q hxRec
        have hAns : H x = H a := hOutX.symm.trans hqOut
        by_cases hxa : x = a
        · rw [hxa, hDecA] at hDecX
          have hTup := Option.some.inj hDecX
          have hqL : q.left = lCh := (congrArg (fun τ => τ.2.2.1) hTup).symm
          have hqR : q.right = rCh := (congrArg (fun τ => τ.2.2.2) hTup).symm
          refine Or.inl ?_
          show extractOnlineMerkleOpening rt (records L H xs) lvl (rest.length + 1) idx =
            some (cur, sib :: rest)
          unfold extractOnlineMerkleOpening
          rw [hExtUp]
          dsimp only
          rw [hFind]
          dsimp only
          by_cases hp : idx % 2 = 0
          · dsimp only [lCh, rCh] at hqL hqR
            simp only [hp, ↓reduceIte] at hqL hqR ⊢
            rw [hqL, hqR]
          · dsimp only [lCh, rCh] at hqL hqR
            simp only [hp, ↓reduceIte] at hqL hqR ⊢
            rw [hqL, hqR]
        · cases hc : listHasElem a xs with
          | true =>
            exact Or.inr (Or.inr ⟨x, a, hxMem, (listHasElem_eq_true_iff a xs).mp hc, hxa, hAns⟩)
          | false =>
            refine Or.inr (Or.inl ⟨a, .head _, not_mem_of_listHasElem_false hc, ?_⟩)
            refine .tail _ (List.mem_append.mpr (Or.inr ?_))
            show H a ∈ xs.map H
            rw [← hAns]
            exact List.mem_map_of_mem hxMem
    · exact Or.inr (Or.inl ⟨a', .tail _ ha', hFresh, hHit⟩)
    · exact Or.inr (Or.inr hColl)

/-- The verifier as a program: `d` compression evaluations along the path. A path shorter
    than `d` is padded with evaluations whose result is discarded. -/
def verifyProg (L : MerkleAddressLayout cardX w) : (d : Nat) → Nat → Nat → BitVec w →
    List (BitVec w) → QueryProg (Fin cardX) (BitVec w) (BitVec w) d
  | 0, _, _, cur, _ => .ret cur
  | d + 1, lvl, idx, cur, [] =>
    .ask (stepAddr L lvl idx cur cur) (fun _ => verifyProg L d (lvl + 1) (idx / 2) cur [])
  | d + 1, lvl, idx, cur, sib :: rest =>
    .ask (stepAddr L lvl idx cur sib) (fun y => verifyProg L d (lvl + 1) (idx / 2) y rest)

theorem verifyProg_log (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) :
    ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w),
      (verifyProg L path.length lvl idx cur path).log H = pathPoints L H lvl idx cur path
  | [], _, _, _ => rfl
  | sib :: rest, lvl, idx, cur => by
    show stepAddr L lvl idx cur sib ::
      (verifyProg L rest.length (lvl + 1) (idx / 2) (H (stepAddr L lvl idx cur sib)) rest).log H
        = stepAddr L lvl idx cur sib ::
          pathPoints L H (lvl + 1) (idx / 2) (H (stepAddr L lvl idx cur sib)) rest
    rw [verifyProg_log L H rest]

theorem verifyProg_eval (L : MerkleAddressLayout cardX w) (H : Fin cardX → BitVec w) :
    ∀ (path : List (BitVec w)) (lvl idx : Nat) (cur : BitVec w),
      (verifyProg L path.length lvl idx cur path).eval H = pathRoot L H lvl idx cur path
  | [], _, _, _ => rfl
  | sib :: rest, lvl, idx, cur =>
    verifyProg_eval L H rest (lvl + 1) (idx / 2) (H (stepAddr L lvl idx cur sib))

end Merkle

/-! ## §6. The two-phase commitment / challenge experiment -/

/-- An opening as output after the challenge. It carries no root: the root is the one
    emitted by `commit` before the challenge. -/
structure PrefixOpening (w : Nat) where
  idx : Nat
  leaf : BitVec w
  path : List (BitVec w)

/-- Phase 1 emits a root and a state after exactly `Q₁` queries; Phase 2 receives the state
    and the challenge and emits an opening after exactly `Q₂` queries. -/
structure TwoPhaseAdversary (cardX w Q₁ Q₂ : Nat) (St Chal : Type) where
  commit : QueryProg (Fin cardX) (BitVec w) (BitVec w × St) Q₁
  respond : St → Chal → QueryProg (Fin cardX) (BitVec w) (PrefixOpening w) Q₂

section Experiment
variable {cardX w Q₁ Q₂ : Nat} {St Chal : Type}

/-- The root emitted before the challenge. -/
def committedRoot (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (H : Fin cardX → BitVec w) :
    BitVec w := (A.commit.eval H).1

/-- The Phase-1 query log. -/
def commitLog (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (H : Fin cardX → BitVec w) :
    List (Fin cardX) := A.commit.log H

/-- The opening emitted after the challenge. -/
def opening (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (H : Fin cardX → BitVec w)
    (ch : Chal) : PrefixOpening w := (A.respond (A.commit.eval H).2 ch).eval H

/-- The Phase-2 query log. -/
def responseLog (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (H : Fin cardX → BitVec w)
    (ch : Chal) : List (Fin cardX) := (A.respond (A.commit.eval H).2 ch).log H

/-- The whole run as one program: Phase 1, Phase 2, then the verifier's `d` evaluations. -/
def experiment (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (ch : Chal) : QueryProg (Fin cardX) (BitVec w) (BitVec w) (d + Q₂ + Q₁) :=
  A.commit.bind (fun cs => (A.respond cs.2 ch).bind
    (fun op => verifyProg L d lvl op.idx op.leaf op.path))

theorem experiment_log (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (ch : Chal) (H : Fin cardX → BitVec w) :
    (experiment A L lvl d ch).log H = commitLog A H ++ (responseLog A H ch ++
      (verifyProg L d lvl (opening A H ch).idx (opening A H ch).leaf
        (opening A H ch).path).log H) := by
  show (A.commit.bind _).log H = _
  rw [QueryProg.log_bind, QueryProg.log_bind]
  rfl

theorem commitLog_length (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (H : Fin cardX → BitVec w) : (commitLog A H).length = Q₁ :=
  QueryProg.log_length H A.commit

/-- The verifier accepts: the path has the tree depth, the position is in range, and the
    path recomputes the root emitted in Phase 1. -/
@[expose] def accepts (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (H : Fin cardX → BitVec w) (ch : Chal) : Bool :=
  decide ((opening A H ch).path.length = d) && decide ((opening A H ch).idx < L.nodes) &&
  decide (pathRoot L H lvl (opening A H ch).idx (opening A H ch).leaf (opening A H ch).path =
    committedRoot A H)

/-- **The pre-challenge commitment.** The opening table extracted from the Phase-1 root and
    the records of the Phase-1 log. There is no challenge argument. -/
@[expose] def prefixCommitted (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl : Nat) (H : Fin cardX → BitVec w)
    (idx len : Nat) : Option (BitVec w × List (BitVec w)) :=
  extractOnlineMerkleOpening (committedRoot A H) (records L H (commitLog A H)) lvl len idx

/-- Extraction from the final log, as in `Qrom.lean`: Phase-2 records are also consulted.
    This is the extractor the temporal experiment must not use. -/
@[expose] def finalLogExtract (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl : Nat) (H : Fin cardX → BitVec w) (ch : Chal)
    (idx len : Nat) : Option (BitVec w × List (BitVec w)) :=
  extractOnlineMerkleOpening (committedRoot A H)
    (records L H (commitLog A H ++ responseLog A H ch)) lvl len idx

/-- Prefix-extraction failure: the verifier accepts an opening that is not the one committed
    before the challenge. -/
@[expose] def prefixFailure (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (H : Fin cardX → BitVec w) (ch : Chal) :
    Bool :=
  accepts A L lvl d H ch &&
  !decide (prefixCommitted A L lvl H (opening A H ch).idx (opening A H ch).path.length =
    some ((opening A H ch).leaf, (opening A H ch).path))

/-- The commitment is a function of the Phase-1 transcript: reprogramming the oracle outside
    the Phase-1 log changes neither the root nor the extracted table. -/
theorem prefixCommitted_reprogram_of_fresh (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl : Nat) (H : Fin cardX → BitVec w) (a : Fin cardX)
    (c : BitVec w) (h : ¬ (a ∈ commitLog A H)) :
    committedRoot A (reprogramOracle H a c) = committedRoot A H ∧
    prefixCommitted A L lvl (reprogramOracle H a c) = prefixCommitted A L lvl H := by
  obtain ⟨hE, hLg⟩ := eval_log_reprogram H a c A.commit h
  have hRoot : committedRoot A (reprogramOracle H a c) = committedRoot A H :=
    congrArg Prod.fst hE
  have hLog : commitLog A (reprogramOracle H a c) = commitLog A H := hLg
  refine ⟨hRoot, ?_⟩
  funext idx len
  show extractOnlineMerkleOpening (committedRoot A (reprogramOracle H a c))
    (records L (reprogramOracle H a c) (commitLog A (reprogramOracle H a c))) lvl len idx =
    extractOnlineMerkleOpening (committedRoot A H) (records L H (commitLog A H)) lvl len idx
  rw [hRoot, hLog, records_reprogram_of_fresh L H a c (commitLog A H) h]

theorem bool_not_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b
  · cases h
  · rfl

/-- An accepted opening outside the failure event is the pre-challenge commitment. -/
theorem accepted_opening_is_prefixCommitted (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (H : Fin cardX → BitVec w) (ch : Chal)
    (hAcc : accepts A L lvl d H ch = true) (hOk : prefixFailure A L lvl d H ch = false) :
    prefixCommitted A L lvl H (opening A H ch).idx (opening A H ch).path.length =
      some ((opening A H ch).leaf, (opening A H ch).path) := by
  unfold prefixFailure at hOk
  rw [hAcc, Bool.true_and] at hOk
  exact of_decide_eq_true (bool_not_eq_false hOk)

/-- **Binding across challenges.** Two challenges answered with accepted openings of the same
    position and depth give the same leaf and path, unless one of the runs is a failure. -/
theorem two_challenge_binding (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (H : Fin cardX → BitVec w) (ch ch' : Chal)
    (hAcc : accepts A L lvl d H ch = true) (hAcc' : accepts A L lvl d H ch' = true)
    (hOk : prefixFailure A L lvl d H ch = false) (hOk' : prefixFailure A L lvl d H ch' = false)
    (hIdx : (opening A H ch).idx = (opening A H ch').idx)
    (hLen : (opening A H ch).path.length = (opening A H ch').path.length) :
    (opening A H ch).leaf = (opening A H ch').leaf ∧
    (opening A H ch).path = (opening A H ch').path := by
  have h1 := accepted_opening_is_prefixCommitted A L lvl d H ch hAcc hOk
  have h2 := accepted_opening_is_prefixCommitted A L lvl d H ch' hAcc' hOk'
  rw [hIdx, hLen] at h1
  exact Prod.mk.inj (Option.some.inj (h1.symm.trans h2))

/-! ### Step events -/

/-- Targets for step `s` of the run. A Phase-1 step is charged against the answers already
    received (collision); every later step is charged against the targets fixed by Phase 1. -/
def stepTargets (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (ch : Chal) (s : Nat) (H : Fin cardX → BitVec w) : List (BitVec w) :=
  if s < Q₁ then (((experiment A L lvl d ch).log H).take s).map H
  else prefixTargets L H (commitLog A H) (committedRoot A H)

/-- Step `s` exists and asks an address not asked before. -/
def stepFresh (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (ch : Chal) (s : Nat) (H : Fin cardX → BitVec w) : Bool :=
  match ((experiment A L lvl d ch).log H)[s]? with
  | none => false
  | some a => !listHasElem a (((experiment A L lvl d ch).log H).take s)

/-- Step `s` asks a fresh address and its answer lands in the step's targets. -/
def stepHit (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (ch : Chal) (s : Nat) (H : Fin cardX → BitVec w) : Bool :=
  match ((experiment A L lvl d ch).log H)[s]? with
  | none => false
  | some a => !listHasElem a (((experiment A L lvl d ch).log H).take s) &&
      listHasElem (H a) (stepTargets A L lvl d ch s H)

theorem stepHit_of (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (ch : Chal) (s : Nat)
    (H : Fin cardX → BitVec w) (a : Fin cardX)
    (hs : ((experiment A L lvl d ch).log H)[s]? = some a)
    (hFresh : ¬ (a ∈ ((experiment A L lvl d ch).log H).take s))
    (hHit : H a ∈ stepTargets A L lvl d ch s H) :
    stepHit A L lvl d ch s H = true := by
  unfold stepHit
  rw [hs]
  show (!listHasElem a (((experiment A L lvl d ch).log H).take s) &&
    listHasElem (H a) (stepTargets A L lvl d ch s H)) = true
  rw [listHasElem_false_of_not_mem hFresh, (listHasElem_eq_true_iff _ _).mpr hHit]
  rfl

theorem stepHit_lt (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (ch : Chal) (s : Nat)
    (H : Fin cardX → BitVec w) (h : stepHit A L lvl d ch s H = true) : s < d + Q₂ + Q₁ := by
  unfold stepHit at h
  cases hs : ((experiment A L lvl d ch).log H)[s]? with
  | none => rw [hs] at h; cases h
  | some a =>
    have hlt := getElem?_lt_length _ s a hs
    rw [QueryProg.log_length] at hlt
    exact hlt

/-- **Cover of the failure event.** If the verifier accepts an opening that differs from the
    pre-challenge commitment, some step of the run asked a fresh address whose answer landed
    in that step's targets. Phase-2 queries enter only as such steps. -/
theorem prefixFailure_cover (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (hLvl : lvl + d ≤ L.levels)
    (H : Fin cardX → BitVec w) (ch : Chal) (hFail : prefixFailure A L lvl d H ch = true) :
    ∃ s : Fin (d + Q₂ + Q₁), stepHit A L lvl d ch s.1 H = true := by
  suffices hEx : ∃ s : Nat, stepHit A L lvl d ch s H = true by
    obtain ⟨s, hs⟩ := hEx
    exact ⟨⟨s, stepHit_lt A L lvl d ch s H hs⟩, hs⟩
  simp only [prefixFailure, accepts, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hFail
  obtain ⟨⟨⟨hLen, hIdx⟩, hRoot⟩, hNot⟩ := hFail
  subst hLen
  have hFull := experiment_log A L lvl (opening A H ch).path.length ch H
  rw [verifyProg_log] at hFull
  have hQ := commitLog_length A H
  rcases prefix_opening_classification L H (commitLog A H) (committedRoot A H)
      (opening A H ch).path lvl (opening A H ch).idx (opening A H ch).leaf hLvl hIdx hRoot with
    hExt | ⟨a, haPts, haFresh, haHit⟩ | ⟨x, x', hx, hx', hne, hEq⟩
  · exact absurd hExt hNot
  · -- an address outside the Phase-1 log: charge its first occurrence in the run
    have haFull : a ∈ (experiment A L lvl (opening A H ch).path.length ch).log H := by
      rw [hFull]
      exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr haPts)))
    obtain ⟨s, hs, hsFresh⟩ := first_occurrence a _ haFull
    have hGe : ¬ (s < Q₁) := by
      have h := hs
      rw [hFull] at h
      have := append_index_ge _ a (commitLog A H) s h haFresh
      rwa [hQ] at this
    refine ⟨s, stepHit_of A L lvl _ ch s H a hs hsFresh ?_⟩
    unfold stepTargets
    rw [ite_eq_right hGe]
    exact haHit
  · -- two Phase-1 addresses with one answer: charge the later first occurrence
    have key : ∀ (i j : Nat) (y y' : Fin cardX), (commitLog A H)[i]? = some y →
        (commitLog A H)[j]? = some y' → ¬ (y' ∈ (commitLog A H).take j) → i < j →
        H y' = H y → ∃ s : Nat, stepHit A L lvl (opening A H ch).path.length ch s H = true := by
      intro i j y y' hi hj hjFresh hij hAns
      have hApp := append_getElem?_take (responseLog A H ch ++
        pathPoints L H lvl (opening A H ch).idx (opening A H ch).leaf (opening A H ch).path)
        (commitLog A H) j y' hj
      rw [← hFull] at hApp
      have hjLt : j < Q₁ := by
        have := getElem?_lt_length _ j y' hj
        rwa [hQ] at this
      refine ⟨j, stepHit_of A L lvl _ ch j H y' hApp.1 (by rw [hApp.2]; exact hjFresh) ?_⟩
      unfold stepTargets
      rw [ite_eq_left hjLt, hApp.2, hAns]
      exact List.mem_map_of_mem (mem_take_of_getElem? _ i j y hi hij)
    obtain ⟨i, hi, hiFresh⟩ := first_occurrence x _ hx
    obtain ⟨j, hj, hjFresh⟩ := first_occurrence x' _ hx'
    rcases Nat.lt_or_ge i j with hij | hji
    · exact key i j x x' hi hj hjFresh hij hEq.symm
    · rcases Nat.lt_or_eq_of_le hji with hlt | heq
      · exact key j i x' x hj hi hiFresh hlt hEq
      · rw [heq] at hj
        exact absurd (Option.some.inj (hi.symm.trans hj)) hne

/-- **One step of the union bound.** Over a uniform oracle, the oracles for which step `s`
    asks a fresh address whose answer lands in the step's targets are at most
    `(3 * Q₁ + 1) / 2 ^ w` of all oracles. -/
theorem stepHit_bound (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (ch : Chal) (s : Nat) :
    2 ^ w * uniformOracleSum w cardX
        (fun H => if stepHit A L lvl d ch s H = true then 1 else 0) ≤
      (3 * Q₁ + 1) * uniformOracleSum w cardX (fun _ => 1) := by
  cases h0 : ((experiment A L lvl d ch).log (fun _ => 0#w))[s]? with
  | none =>
    have hLen := length_le_of_getElem?_none _ s h0
    rw [QueryProg.log_length] at hLen
    have hz : ∀ H : Fin cardX → BitVec w,
        (if stepHit A L lvl d ch s H = true then 1 else 0) = 0 * 1 := by
      intro H
      have hNone : ((experiment A L lvl d ch).log H)[s]? = none :=
        getElem?_none_of_length_le _ s (by rw [QueryProg.log_length]; exact hLen)
      unfold stepHit
      rw [hNone]
      rfl
    rw [uniformOracleSum_congr w cardX _ _ hz, uniformOracleSum_mul, Nat.zero_mul, Nat.mul_zero]
    exact Nat.zero_le _
  | some x0 =>
    let lg : (Fin cardX → BitVec w) → List (Fin cardX) := fun H => (experiment A L lvl d ch).log H
    let p : (Fin cardX → BitVec w) → Fin cardX := fun H => ((lg H)[s]?).getD x0
    have hShape : ∀ H, stepHit A L lvl d ch s H =
        (stepFresh A L lvl d ch s H && listHasElem (H (p H)) (stepTargets A L lvl d ch s H)) := by
      intro H
      unfold stepHit stepFresh
      show _ = ((match (lg H)[s]? with
        | none => false
        | some a => !listHasElem a ((lg H).take s)) &&
        listHasElem (H (((lg H)[s]?).getD x0)) (stepTargets A L lvl d ch s H))
      cases (lg H)[s]? <;> rfl
    -- consequences of freshness at step `s`
    have hLoc : ∀ (H : Fin cardX → BitVec w) (c : BitVec w), stepFresh A L lvl d ch s H = true →
        ∃ a, (lg H)[s]? = some a ∧ p H = a ∧ listHasElem a ((lg H).take s) = false ∧
          (lg (reprogramOracle H a c)).take s = (lg H).take s ∧
          (lg (reprogramOracle H a c))[s]? = some a := by
      intro H c hF
      unfold stepFresh at hF
      cases hs : (lg H)[s]? with
      | none =>
        have hs' : ((experiment A L lvl d ch).log H)[s]? = none := hs
        rw [hs'] at hF
        cases hF
      | some a =>
        have hs' : ((experiment A L lvl d ch).log H)[s]? = some a := hs
        rw [hs'] at hF
        have hFr : listHasElem a ((lg H).take s) = false := bool_not_eq_true hF
        have hT := take_of_take_succ s _ _ (log_take_reprogram H a c (experiment A L lvl d ch) s
          (not_mem_of_listHasElem_false hFr))
        refine ⟨a, rfl, ?_, hFr, hT.1, hT.2.trans hs⟩
        show ((lg H)[s]?).getD x0 = a
        rw [hs]
        rfl
    have hRes := conditional_fresh_point_bound w cardX p (stepFresh A L lvl d ch s)
      (stepTargets A L lvl d ch s) (3 * Q₁ + 1) ?_ ?_ ?_ ?_
    · rw [uniformOracleSum_congr w cardX _ _ (fun H => by rw [hShape H])]
      exact hRes
    · intro H c hF
      obtain ⟨a, _, hpa, _, _, hsa⟩ := hLoc H c hF
      rw [hpa]
      show ((lg (reprogramOracle H a c))[s]?).getD x0 = a
      rw [hsa]
      rfl
    · intro H c hF
      obtain ⟨a, _, hpa, hFr, hTake, hsa⟩ := hLoc H c hF
      rw [hpa]
      unfold stepFresh
      have hsa' : ((experiment A L lvl d ch).log (reprogramOracle H a c))[s]? = some a := hsa
      have hTake' : ((experiment A L lvl d ch).log (reprogramOracle H a c)).take s =
          (lg H).take s := hTake
      rw [hsa']
      show (!listHasElem a (((experiment A L lvl d ch).log (reprogramOracle H a c)).take s)) = true
      rw [hTake', hFr]
      rfl
    · intro H c hF
      obtain ⟨a, _, hpa, hFr, hTake, _⟩ := hLoc H c hF
      rw [hpa]
      unfold stepTargets
      by_cases hlt : s < Q₁
      · rw [ite_eq_left hlt, ite_eq_left hlt]
        have hTake' : ((experiment A L lvl d ch).log (reprogramOracle H a c)).take s =
            ((experiment A L lvl d ch).log H).take s := hTake
        rw [hTake']
        exact map_reprogram_of_fresh H a c _ hFr
      · rw [ite_eq_right hlt, ite_eq_right hlt]
        have hNotCommit : ¬ (a ∈ commitLog A H) := by
          intro hm
          have hge : ¬ (s < (commitLog A H).length) := by rw [commitLog_length]; exact hlt
          have hIn := mem_take_append_of_ge (responseLog A H ch ++
            (verifyProg L d lvl (opening A H ch).idx (opening A H ch).leaf
              (opening A H ch).path).log H) (commitLog A H) s hge a hm
          rw [← experiment_log A L lvl d ch H] at hIn
          exact not_mem_of_listHasElem_false hFr hIn
        obtain ⟨hE, hLg⟩ := eval_log_reprogram H a c A.commit hNotCommit
        have hRoot : committedRoot A (reprogramOracle H a c) = committedRoot A H :=
          congrArg Prod.fst hE
        have hLog : commitLog A (reprogramOracle H a c) = commitLog A H := hLg
        rw [hRoot, hLog]
        exact prefixTargets_reprogram_of_fresh L H a c _ _ hNotCommit
    · intro H _
      unfold stepTargets
      by_cases hlt : s < Q₁
      · rw [ite_eq_left hlt, List.length_map]
        have := length_take_le_self s ((experiment A L lvl d ch).log H)
        omega
      · rw [ite_eq_right hlt]
        have := prefixTargets_length L H (commitLog A H) (committedRoot A H)
        rw [commitLog_length] at this
        exact this

/-- **Prefix extraction bound.** For every adversary, every fixed challenge and a uniformly
    random oracle `Fin cardX → BitVec w`: the oracles under which the verifier accepts an
    opening other than the one extracted from the Phase-1 log are at most
    `(d + Q₂ + Q₁) * (3 * Q₁ + 1) / 2 ^ w` of all `(2 ^ w) ^ cardX` oracles. The `Q₂` Phase-2
    queries and the `d` verifier evaluations are separate terms of the union; the extractor
    reads none of them. -/
theorem prefix_extraction_failure_bound (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (hLvl : lvl + d ≤ L.levels) (ch : Chal) :
    2 ^ w * uniformOracleSum w cardX
        (fun H => if prefixFailure A L lvl d H ch = true then 1 else 0) ≤
      ((d + Q₂ + Q₁) * (3 * Q₁ + 1)) * (2 ^ w) ^ cardX := by
  have hCover : ∀ H : Fin cardX → BitVec w,
      (if prefixFailure A L lvl d H ch = true then 1 else 0) ≤
        qsum (d + Q₂ + Q₁) (fun s => if stepHit A L lvl d ch s.1 H = true then 1 else 0) := by
    intro H
    cases hF : prefixFailure A L lvl d H ch with
    | false => exact Nat.zero_le _
    | true =>
      obtain ⟨s, hs⟩ := prefixFailure_cover A L lvl d hLvl H ch hF
      have hTerm := le_qsum_term
        (fun s : Fin (d + Q₂ + Q₁) => if stepHit A L lvl d ch s.1 H = true then 1 else 0) s
      have h1 : (if stepHit A L lvl d ch s.1 H = true then 1 else 0) = 1 := ite_eq_left hs
      rw [h1] at hTerm
      exact hTerm
  have hSum := uniformOracleSum_le w cardX _ _ hCover
  rw [uniformOracleSum_qsum w cardX (d + Q₂ + Q₁)
    (fun H s => if stepHit A L lvl d ch s.1 H = true then 1 else 0)] at hSum
  have hSteps : 2 ^ w * qsum (d + Q₂ + Q₁) (fun s => uniformOracleSum w cardX
      (fun H => if stepHit A L lvl d ch s.1 H = true then 1 else 0)) ≤
      (d + Q₂ + Q₁) * ((3 * Q₁ + 1) * uniformOracleSum w cardX (fun _ => 1)) := by
    rw [← qsum_mul_left, ← qsum_const (d + Q₂ + Q₁)]
    exact qsum_le_qsum (fun s => stepHit_bound A L lvl d ch s.1)
  refine Nat.le_trans (Nat.mul_le_mul_left (2 ^ w) hSum) (Nat.le_trans hSteps (Nat.le_of_eq ?_))
  rw [uniformOracleSum_const, Nat.mul_one, Nat.mul_assoc]

/-- The same bound averaged over `cardC` challenges chosen independently of the oracle. -/
theorem prefix_extraction_failure_bound_challenges (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (hLvl : lvl + d ≤ L.levels)
    (cardC : Nat) (chal : Fin cardC → Chal) :
    2 ^ w * qsum cardC (fun c => uniformOracleSum w cardX
        (fun H => if prefixFailure A L lvl d H (chal c) = true then 1 else 0)) ≤
      cardC * (((d + Q₂ + Q₁) * (3 * Q₁ + 1)) * (2 ^ w) ^ cardX) := by
  rw [← qsum_mul_left, ← qsum_const cardC]
  exact qsum_le_qsum (fun c => prefix_extraction_failure_bound A L lvl d hLvl (chal c))

end Experiment

/-! ## §7. Final-log extraction accepts an uncommitted root -/

section LateOpen
variable {cardX w : Nat}

theorem findFirst_nil {β : Type} (p : β → Bool) : findFirst p [] = none := by
  cases h : findFirst p [] with
  | none => rfl
  | some x => exact nomatch (findFirst_some_spec p h).1

theorem findFirst_singleton {β : Type} (p : β → Bool) (q : β) (hq : p q = true) :
    findFirst p [q] = some q := by
  cases h : findFirst p [q] with
  | none => exact Bool.noConfusion ((findFirst_none_spec p h q (.head _)).symm.trans hq)
  | some x =>
    have hm := (findFirst_some_spec p h).1
    cases hm with
    | head => rfl
    | tail _ h' => exact nomatch h'

/-- The adversary that commits to a root without any query and asks the single compression
    input only after the challenge. -/
def lateOpenAdversary (L : MerkleAddressLayout cardX w) (rt u v : BitVec w) (Chal : Type) :
    TwoPhaseAdversary cardX w 0 1 Unit Chal where
  commit := .ret (rt, ())
  respond _ _ := .ask (L.encode 0 0 u v) (fun _ => .ret ⟨0, u, [v]⟩)

/-- **Final-log extraction is not pre-challenge extraction.** Against the late-opening
    adversary, under any oracle that maps the compression input `(u, v)` to the announced
    root, the verifier accepts, extraction from the final log returns the opening `(u, [v])`,
    and extraction from the Phase-1 log returns `none`: nothing was committed before the
    challenge, and the run is counted as a failure by `prefixFailure`. -/
theorem lateOpen_final_log_extracts_uncommitted (L : MerkleAddressLayout cardX w)
    (hLv : 0 < L.levels) (hNd : 0 < L.nodes) (H : Fin cardX → BitVec w) (rt u v : BitVec w)
    (hH : H (L.encode 0 0 u v) = rt) {Chal : Type} (ch : Chal) :
    accepts (lateOpenAdversary L rt u v Chal) L 0 1 H ch = true ∧
    finalLogExtract (lateOpenAdversary L rt u v Chal) L 0 H ch 0 1 = some (u, [v]) ∧
    prefixCommitted (lateOpenAdversary L rt u v Chal) L 0 H 0 1 = none ∧
    prefixFailure (lateOpenAdversary L rt u v Chal) L 0 1 H ch = true := by
  have hAcc : accepts (lateOpenAdversary L rt u v Chal) L 0 1 H ch = true := by
    have hOp : opening (lateOpenAdversary L rt u v Chal) H ch = ⟨0, u, [v]⟩ := rfl
    have hRt : committedRoot (lateOpenAdversary L rt u v Chal) H = rt := rfl
    have hPath : pathRoot L H 0 0 u [v] = rt := by
      rw [pathRoot_cons, pathRoot_nil]
      exact hH
    unfold accepts
    rw [hOp, hRt]
    show (decide (([v] : List (BitVec w)).length = 1) && decide (0 < L.nodes) &&
      decide (pathRoot L H 0 0 u [v] = rt)) = true
    rw [decide_eq_true hNd, decide_eq_true hPath]
    rfl
  have hPre : prefixCommitted (lateOpenAdversary L rt u v Chal) L 0 H 0 1 = none := by
    show extractOnlineMerkleOpening rt [] 0 (0 + 1) 0 = none
    unfold extractOnlineMerkleOpening
    have hUp : extractOnlineMerkleOpening rt ([] : List (RecordedMerkleQuery (BitVec w)))
        (0 + 1) 0 (0 / 2) = some (rt, []) := rfl
    rw [hUp]
    dsimp only
    rw [findFirst_nil]
  have hFin : finalLogExtract (lateOpenAdversary L rt u v Chal) L 0 H ch 0 1 = some (u, [v]) := by
    have hRec : records L H [L.encode 0 0 u v] = [⟨0, 0, u, v, rt⟩] := by
      rw [records_cons_some L H _ [] ⟨0, 0, u, v, H (L.encode 0 0 u v)⟩
        (recordOf_of_decode L H _ 0 0 u v (L.decode_encode 0 0 u v hLv hNd)), hH]
      rfl
    show extractOnlineMerkleOpening rt (records L H [L.encode 0 0 u v]) 0 (0 + 1) 0 =
      some (u, [v])
    rw [hRec]
    unfold extractOnlineMerkleOpening
    have hUp : extractOnlineMerkleOpening rt
        [(⟨0, 0, u, v, rt⟩ : RecordedMerkleQuery (BitVec w))] (0 + 1) 0 (0 / 2) =
        some (rt, []) := rfl
    rw [hUp]
    dsimp only
    rw [findFirst_singleton _ (⟨0, 0, u, v, rt⟩ : RecordedMerkleQuery (BitVec w))
      (by simp only [decide_true, Bool.and_self])]
    rfl
  refine ⟨hAcc, hFin, hPre, ?_⟩
  unfold prefixFailure
  rw [hAcc, Bool.true_and]
  show (!decide (prefixCommitted (lateOpenAdversary L rt u v Chal) L 0 H 0 1 =
    some (u, [v]))) = true
  rw [hPre]
  rfl

end LateOpen

end Qsag.PrefixMerkleExtraction
