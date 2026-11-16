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
