module
public import Qsag.Oracle.Spn
public import Qsag.Math.Counting
public import Qsag.Spec.Assumptions
public import Qsag.Oracle.SpongeTwoWayIndifferentiability

public section
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag.LazyPermutation
abbrev Perm (n : Nat) := PublicPermutation (Fin n)
abbrev Dir := PublicPermutationDirection

private def flip (p : PublicPermutation α) : PublicPermutation α :=
  ⟨p.inverse, p.forward, p.forward_inverse, p.inverse_forward⟩

private theorem qsum_eq_sampleSum : ∀ (n : Nat) (f : Fin n → Nat), qsum n f = Spec.sampleSum n f
  | 0, _ => rfl
  | n + 1, f => by
    show f ⟨0, Nat.zero_lt_succ n⟩ + qsum n _ = f ⟨0, Nat.zero_lt_succ n⟩ + Spec.sampleSum n _
    rw [qsum_eq_sampleSum n]

/-- A sum over a split coin space is the iterated sum over its two coordinates. -/
private theorem qsum_coinSplit {n nC nA : Nat} (π : Spec.CoinSplit n nC nA) (w : Fin n → Nat) :
    qsum n w = qsum nC (fun c => qsum nA (fun a => w (π.pair c a))) :=
  (qsum_eq_sampleSum n w).trans <|
    (π.sampleSum_eq w).trans <|
      (qsum_eq_sampleSum nC _).symm.trans <|
        qsum_congr (fun _ => (qsum_eq_sampleSum nA _).symm)

private theorem perm_ext (p q : PublicPermutation α) (h : ∀ x, p.forward x = q.forward x) : p = q := by
  have hi : p.inverse = q.inverse := funext fun x => by
    calc p.inverse x = p.inverse (q.forward (q.inverse x)) := congrArg _ (q.forward_inverse x).symm
         _ = q.inverse x := (congrArg p.inverse (h _).symm).trans (p.inverse_forward _)
  cases p; cases q; cases funext h; cases hi; rfl

private def swapZero (a z : Fin (n+1)) : Fin (n+1) :=
  if z = 0 then a else if z = a then 0 else z

private theorem swap_twice (a z : Fin (n+1)) : swapZero a (swapZero a z) = z := by
  by_cases hz : z = 0 <;> by_cases ha : z = a <;> by_cases h : a = 0 <;> simp_all [swapZero]

/-- Index zero is the selected entry. The remaining indices enumerate its complement. -/
private def layout (a : Fin (n+1)) : SimpleEquiv (Option (Fin n)) (Fin (n+1)) where
  toFun o := swapZero a (o.elim 0 Fin.succ)
  invFun z := if h : swapZero a z = 0 then none else some ((swapZero a z).pred h)
  left_inv o := by
    cases o with
    | none => simp [swap_twice]
    | some i => simp [swap_twice, Fin.succ_ne_zero]
  right_inv z := by
    split
    · next h => simpa only [Option.elim_none, ← h] using swap_twice a z
    · simp [swap_twice]

private def liftMap (a b : Fin (n+1)) (f : Fin n → Fin n) (z : Fin (n+1)) :=
  (layout b).toFun (((layout a).invFun z).map f)

private theorem lift_at (a b : Fin (n+1)) (f : Fin n → Fin n) (o : Option (Fin n)) :
    liftMap a b f ((layout a).toFun o) = (layout b).toFun (o.map f) := by
  unfold liftMap
  rw [SimpleEquiv.left_inv]

private theorem layout_none (a : Fin (n+1)) : (layout a).toFun none = a := by
  simp [layout, swapZero]

private def extend (a b : Fin (n+1)) (p : Perm n) : Perm (n+1) where
  forward := liftMap a b p.forward
  inverse := liftMap b a p.inverse
  inverse_forward x := by
    rw [← (layout a).right_inv x]
    generalize (layout a).invFun x = o
    rw [lift_at, lift_at]
    cases o <;> simp [p.inverse_forward]
  forward_inverse x := by
    rw [← (layout b).right_inv x]
    generalize (layout b).invFun x = o
    rw [lift_at, lift_at]
    cases o <;> simp [p.forward_inverse]

private theorem extend_first (a b : Fin (n+1)) (p : Perm n) : (extend a b p).forward a = b := by
  change liftMap a b p.forward a = b
  simpa only [layout_none, Option.map_none] using lift_at a b p.forward none

private theorem layout_inj (a : Fin (n+1)) {u v : Option (Fin n)}
    (h : (layout a).toFun u = (layout a).toFun v) : u = v := by
  simpa only [SimpleEquiv.left_inv] using congrArg (layout a).invFun h

private def residual (p : Perm (n+1)) (a b : Fin (n+1)) (hab : p.forward a = b) (i : Fin n) :
    Fin n :=
  let z := p.forward ((layout a).toFun (some i))
  let o := (layout b).invFun z
  o.get (by
    cases e : o with
    | some j => rfl
    | none =>
      have h : z = b := ((layout b).right_inv z).symm.trans
        ((congrArg (layout b).toFun e).trans (layout_none b))
      have h' := congrArg p.inverse (h.trans hab.symm)
      simp only [z, p.inverse_forward] at h'
      have absurdEq : some i = none := layout_inj a (h'.trans (layout_none a).symm)
      cases absurdEq)

private theorem residual_spec (p : Perm (n+1)) (a b : Fin (n+1)) (hab : p.forward a = b)
    (i : Fin n) : (layout b).toFun (some (residual p a b hab i)) =
      p.forward ((layout a).toFun (some i)) := by
  unfold residual
  simp only [Option.some_get, SimpleEquiv.right_inv]

private def restrict (p : Perm (n+1)) (a b : Fin (n+1)) (h : p.forward a = b) : Perm n :=
  let hi : (flip p).forward b = a := (congrArg p.inverse h.symm).trans (p.inverse_forward a)
  { forward := residual p a b h
    inverse := residual (flip p) b a hi
    inverse_forward := fun i => Option.some.inj (layout_inj a (by
      rw [residual_spec, residual_spec]
      exact p.inverse_forward _))
    forward_inverse := fun i => Option.some.inj (layout_inj b (by
      rw [residual_spec, residual_spec]
      exact p.forward_inverse _)) }

private theorem rebuild (p : Perm (n+1)) (a b : Fin (n+1)) (h : p.forward a = b) :
    extend a b (restrict p a b h) = p := by
  apply perm_ext
  intro x
  rw [← (layout a).right_inv x]
  cases (layout a).invFun x with
  | none => simpa only [layout_none, extend_first] using h.symm
  | some i => exact (lift_at ..).trans (residual_spec p a b h i)

private theorem recover_tail (a b : Fin (n+1)) (p : Perm n) :
    restrict (extend a b p) a b (extend_first a b p) = p := by
  apply perm_ext
  intro i
  apply Option.some.inj
  apply layout_inj b
  exact (residual_spec _ a b (extend_first a b p) i).trans (lift_at a b p.forward (some i))

private theorem recover_at_answer (a b : Fin (n+1)) (p : Perm n) (z : Fin (n+1))
    (e : (extend a b p).forward a = z) : restrict (extend a b p) a z e = p := by
  have hz := e.symm.trans (extend_first a b p)
  revert e
  rw [hz]
  exact fun _ => recover_tail a b p

/-- Splitting a bijection at an arbitrary forward or inverse input. -/
private def fiber (d : Dir) (a : Fin (n+1)) : SimpleEquiv (Fin (n+1) × Perm n) (Perm (n+1)) :=
  match d with
  | .forward =>
    { toFun := fun (b,p) => extend a b p
      invFun := fun p => (p.forward a, restrict p a (p.forward a) rfl)
      left_inv := fun (b,p) => by
        apply Prod.ext (extend_first ..)
        exact recover_at_answer _ _ _ _ rfl
      right_inv := fun p => rebuild p a _ rfl }
  | .inverse =>
    { toFun := fun (b,p) => flip (extend a b p)
      invFun := fun p => (p.inverse a, restrict (flip p) a (p.inverse a) rfl)
      left_inv := fun (b,p) => by
        apply Prod.ext (extend_first ..)
        exact recover_at_answer _ _ _ _ rfl
      right_inv := fun p => congrArg flip (rebuild (flip p) a _ rfl) }

abbrev Program (n : Nat) (R : Type) := PublicPermutationProgram (Fin n) R

def eval (p : Perm n) : Program n R → R
  | .done r => r
  | .query d x k => eval p (k (publicPermutationQuery p d x))

private def orientation : Dir → Dir → Dir
  | .forward, d => d
  | .inverse, .inverse => .forward
  | .inverse, .forward => .inverse

private def ends (a b : α) : Dir → α × α
  | .forward => (a,b)
  | .inverse => (b,a)

private theorem query_fiber (d e : Dir) (a b z : Fin (n+1)) (p : Perm n) :
    publicPermutationQuery ((fiber d a).toFun (b,p)) e z =
      let dir := orientation d e
      let (src,dst) := ends a b dir
      liftMap src dst (publicPermutationQuery p dir) z := by
  cases d <;> cases e <;> rfl

private theorem fiber_answer (d : Dir) (a b : Fin (n+1)) (p : Perm n) :
    publicPermutationQuery ((fiber d a).toFun (b,p)) d a = b := by
  cases d <;> exact extend_first .. 

/-- Specialize all subsequent queries to the chosen edge. Hits consume no new digit.
A miss in either direction addresses the residual bijection on one fewer point. -/
def specialize (d : Dir) (a b : Fin (n+1)) : Program (n+1) R → Program n R
  | .done r => .done r
  | .query e z k =>
    let dir := orientation d e
    let (src,dst) := ends a b dir
    match (layout src).invFun z with
    | none => specialize d a b (k dst)
    | some i => .query dir i (fun j => specialize d a b (k ((layout dst).toFun (some j))))

private theorem eval_specialize (d : Dir) (a b : Fin (n+1)) (p : Perm n) (A : Program (n+1) R) :
    eval p (specialize d a b A) = eval ((fiber d a).toFun (b,p)) A := by
  induction A with
  | done => rfl
  | query e z k ih =>
    rw [specialize, eval, query_fiber]
    dsimp only
    unfold liftMap
    split
    · next h => rw [h]; simp only [Option.map_none, layout_none]; exact ih _
    · next i h => rw [h]; exact ih _

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

private def zeroEnum : SimpleEquiv (Fin 1) (Perm 0) where
  toFun _ := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim .. 
  right_inv p := perm_ext _ p (fun x => Fin.elim0 x)

/-- A uniform digit and an independent residual coin. Different answers may choose
different enumerations of the residual space. -/
private def branch (d : Dir) (x : Fin (n+1))
    (next : Fin (n+1) → SimpleEquiv (Fin (factorial n)) (Perm n)) :
    SimpleEquiv (Fin (factorial (n+1))) (Perm (n+1)) :=
  let split := Spec.CoinSplit.prod (n+1) (factorial n)
  let f := fiber d x
  { toFun := fun i => f.toFun (split.chal i, (next (split.chal i)).toFun (split.advc i))
    invFun := fun p => let (b,t) := f.invFun p; split.pair b ((next b).invFun t)
    left_inv := fun i => by simp only [f.left_inv, SimpleEquiv.left_inv]; exact split.pair_eta i
    right_inv := fun p => by simp only [split.chal_pair, split.advc_pair, SimpleEquiv.right_inv]; exact f.right_inv p }

/-- Fixed enumeration, independent of all queries. -/
def upfront : (n : Nat) → SimpleEquiv (Fin (factorial n)) (Perm n)
  | 0 => zeroEnum
  | n+1 => branch .forward 0 (fun _ => upfront n)

/-- Complete unused entries after termination to count every run on the same N! coins. -/
def completion : {n : Nat} → Program n R → SimpleEquiv (Fin (factorial n)) (Perm n)
  | 0, _ => zeroEnum
  | n+1, .done _ => upfront (n+1)
  | _+1, .query d x k => branch d x (fun b => completion (specialize d x b (k b)))

/-- Executable sampler. Only a new partial-table edge consumes a mixed-radix digit.
Programs may query beyond N, repeat queries, reverse edges and stop early. -/
def lazyRun : {n : Nat} → Program n R → Fin (factorial n) → R
  | _, .done r, _ => r
  | 0, .query _ x _, _ => Fin.elim0 x
  | n+1, .query d x k, i =>
    let split := Spec.CoinSplit.prod (n+1) (factorial n)
    let b := split.chal i
    lazyRun (specialize d x b (k b)) (split.advc i)

theorem lazy_completion : ∀ {n} (A : Program n R) (i : Fin (factorial n)),
    lazyRun A i = eval ((completion A).toFun i) A
  | 0, .done _, _ => rfl
  | 0, .query _ x _, _ => Fin.elim0 x
  | _+1, .done _, _ => rfl
  | n+1, .query d x k, i => by
    let split := Spec.CoinSplit.prod (n+1) (factorial n)
    let b := split.chal i
    let rest := specialize d x b (k b)
    let p := (completion rest).toFun (split.advc i)
    change lazyRun rest (split.advc i) = eval ((fiber d x).toFun (b,p))
      (k (publicPermutationQuery ((fiber d x).toFun (b,p)) d x))
    rw [fiber_answer]
    exact (lazy_completion rest _).trans (eval_specialize d x b p (k b))

theorem equal_distribution (A : Program n R) (weight : R → Nat) :
    qsum (factorial n) (fun i => weight (lazyRun A i)) =
      qsum (factorial n) (fun i => weight (eval ((upfront n).toFun i) A)) := by
  let u := upfront n
  let c := completion A
  let f := fun i => u.invFun (c.toFun i)
  let g := fun i => c.invFun (u.toFun i)
  have left : ∀ i, g (f i) = i := fun i => by simp only [f, g, u.right_inv, c.left_inv]
  have right : ∀ i, f (g i) = i := fun i => by simp only [f, g, c.right_inv, u.left_inv]
  have h := qsum_perm_invariant f g left right (fun i => weight (eval (u.toFun i) A))
  simpa only [f, u.right_inv, lazy_completion, u, c] using h

/-- With m+1 unused points (N-k after k distinct edges), each possible next answer
has m! completions among (m+1)! residual bijections, in either direction. -/
theorem fresh_answer_completions (d : Dir) (x y : Fin (m+1)) :
    qsum (factorial (m+1)) (fun i =>
      if publicPermutationQuery ((upfront _).toFun i) d x = y then 1 else 0) = factorial m := by
  let u := upfront (m+1)
  let c := branch d x (fun _ => upfront m)
  let f := fun i => u.invFun (c.toFun i)
  let g := fun i => c.invFun (u.toFun i)
  have he := qsum_perm_invariant f g
    (fun i => by simp only [f,g,u.right_inv,c.left_inv])
    (fun i => by simp only [f,g,c.right_inv,u.left_inv])
    (fun i => if publicPermutationQuery (u.toFun i) d x = y then 1 else 0)
  simp only [f,u.right_inv] at he
  apply he.symm.trans
  let π := Spec.CoinSplit.prod (m+1) (factorial m)
  refine (qsum_coinSplit π (fun i => if publicPermutationQuery (c.toFun i) d x = y then 1 else 0)).trans ?_
  apply (qsum_congr (g := fun z => if z = y then factorial m else 0) ?_).trans (qsum_ite_eq ..)
  intro z
  have answer (i : Fin (factorial m)) :
      publicPermutationQuery (c.toFun (π.pair z i)) d x = z :=
    (fiber_answer d x _ _).trans (π.chal_pair _ _)
  simp only [answer, qsum_const]
  split <;> simp_all

abbrev Transcript (n : Nat) := List (Dir × Fin n × Fin n)

/-- Keep both query directions, their inputs and their answers in chronological order. -/
def record (history : Transcript n) : Program n R → Program n (Transcript n × R)
  | .done r => .done (history.reverse,r)
  | .query d x k => .query d x (fun b => record ((d,x,b)::history) (k b))

theorem joint_transcript_distribution (A : Program n R) (event : Transcript n × R → Bool) :
    qsum (factorial n) (fun i => (event (lazyRun (record [] A) i)).toNat) =
      qsum (factorial n) (fun i => (event (eval ((upfront n).toFun i) (record [] A))).toNat) :=
  equal_distribution _ (fun x => (event x).toNat)

open SpongeIndiff

private def pack (x : SpSt r c) := (Spec.CoinSplit.prod r c).pair x.1 x.2
private def unpack (i : Fin (r*c)) : SpSt r c :=
  ((Spec.CoinSplit.prod r c).chal i, (Spec.CoinSplit.prod r c).advc i)
private theorem unpack_pack (x : SpSt r c) : unpack (pack x) = x := by
  simp [pack, unpack, Spec.CoinSplit.chal_pair, Spec.CoinSplit.advc_pair]
private theorem pack_unpack (i : Fin (r*c)) : pack (unpack i) = i :=
  (Spec.CoinSplit.prod r c).pair_eta _

/-- Expand sponge nodes to primitive queries following the same block transitions as realWalk. -/
def blocks (ops : AbsorbOps β r) (k : SpSt r c → Program (r*c) O) :
    SpSt r c → List β → Program (r*c) O
  | s, [] => k s
  | s, b::bs => .query .forward (pack (ops.xorB s.1 b,s.2)) (fun z => blocks ops k (unpack z) bs)

def sponge (ops : AbsorbOps β r) (s0 : SpSt r c) : SpAdv β r c O → Program (r*c) O
  | .done o => .done o
  | .fwd x k => .query .forward (pack x) (fun z => sponge ops s0 (k (unpack z)))
  | .inv y k => .query .inverse (pack y) (fun z => sponge ops s0 (k (unpack z)))
  | .node bs k => blocks ops (fun z => sponge ops s0 (k z.1)) s0 bs

private def replay : Program (r*c) O → PermTable r c → List (SpSt r c) → Option O
  | .done o, _, _ => some o
  | .query d x k, τ, coins => do
    let (y,τ',tail) ← match d with
      | .forward => realFwd τ coins (unpack x)
      | .inverse => realInv τ coins (unpack x)
    replay (k (pack y)) τ' tail

private theorem replay_blocks (ops : AbsorbOps β r) (k : SpSt r c → Program (r*c) O)
    (bs : List β) (s : SpSt r c) (τ : PermTable r c) (coins : List (SpSt r c)) :
    replay (blocks ops k s bs) τ coins =
      (realWalk ops τ coins s bs).bind (fun (z,t,rest) => replay (k z) t rest) := by
  induction bs generalizing s τ coins with
  | nil => rw [realWalk.public_eq_1]; rfl
  | cons b bs ih =>
    simp only [blocks, replay, unpack_pack, realWalk.public_eqs]
    cases realFwd τ coins (ops.xorB s.1 b,s.2) with
    | none => rfl
    | some resp => obtain ⟨z,t,tail⟩ := resp; simpa [unpack_pack] using ih z t tail

private theorem replay_sponge (ops : AbsorbOps β r) (s0 : SpSt r c) (A : SpAdv β r c O)
    (τ : PermTable r c) (ω : List (SpSt r c)) :
    replay (sponge ops s0 A) τ ω = realRun ops s0 A τ ω := by
  induction A generalizing τ ω with
  | done => rw [realRun.public_eq_1]; rfl
  | node bs k ih =>
    rw [sponge, replay_blocks, realRun.public_eq_2]
    cases realWalk ops τ ω s0 bs with
    | none => rfl
    | some resp => obtain ⟨z,t,rest⟩ := resp; exact ih _ _ _
  | fwd x k ih =>
    simp only [sponge, replay, unpack_pack, realRun.public_eqs]
    cases realFwd τ ω x with
    | none => rfl
    | some resp => obtain ⟨z,t,rest⟩ := resp; simpa [unpack_pack] using ih z t rest
  | inv x k ih =>
    simp only [sponge, replay, unpack_pack, realRun.public_eqs]
    cases realInv τ ω x with
    | none => rfl
    | some resp => obtain ⟨z,t,rest⟩ := resp; simpa [unpack_pack] using ih z t rest

def requests (p : Perm n) : Program n O → Transcript n
  | .done _ => []
  | .query d x k =>
    let b := publicPermutationQuery p d x
    (d,x,b)::requests p (k b)

private theorem eval_record (p : Perm n) (A : Program n O) (hist : Transcript n) :
    eval p (record hist A) = (hist.reverse ++ requests p A, eval p A) := by
  induction A generalizing hist with
  | done => simp [record, eval, requests]
  | query d x k ih => simp [record, eval, requests, ih, List.append_assoc]

/-- Give the bounded-tape evaluator one coin for each newly revealed edge, in query order. -/
def freshTape (τ : PermTable r c) : Transcript (r*c) → List (SpSt r c)
  | [] => []
  | (d,x,b)::rest =>
    let e := match d with
      | .forward => (unpack x, unpack b)
      | .inverse => (unpack b, unpack x)
    if e ∈ τ then freshTape τ rest else unpack b :: freshTape (e::τ) rest

private def Agrees (p : Perm (r*c)) (τ : PermTable r c) :=
  ∀ x y, (x,y) ∈ τ → p.forward (pack x) = pack y

private theorem agrees_cons {p : Perm (r*c)} {τ : PermTable r c} {x y : SpSt r c}
    (h : Agrees p τ) (e : p.forward (pack x) = pack y) : Agrees p ((x,y)::τ) := by
  intro a b hm
  rcases List.mem_cons.mp hm with he | ht
  · cases he; exact e
  · exact h _ _ ht

private theorem unique_out {p : Perm (r*c)} {τ : PermTable r c} (h : Agrees p τ)
    {x y z : SpSt r c} (a : (x,y) ∈ τ) (b : p.forward (pack x) = pack z) : y = z := by
  simpa only [unpack_pack] using congrArg unpack ((h _ _ a).symm.trans b)

private theorem unique_in {p : Perm (r*c)} {τ : PermTable r c} (h : Agrees p τ)
    {x y z : SpSt r c} (a : (x,y) ∈ τ) (b : p.forward (pack z) = pack y) : x = z := by
  have eq := congrArg p.inverse ((h _ _ a).trans b.symm)
  simp only [p.inverse_forward] at eq
  simpa only [unpack_pack] using congrArg unpack eq

private theorem replay_requests (p : Perm (r*c)) (A : Program (r*c) O) (τ : PermTable r c)
    (h : Agrees p τ) :
    replay A τ (freshTape τ (requests p A)) = some (eval p A) := by
  induction A generalizing τ with
  | done => rfl
  | query d x k ih =>
    cases d with
    | forward =>
      let a : SpSt r c := unpack x
      let b : SpSt r c := unpack (p.forward x)
      have e : p.forward (pack a) = pack b := by simp [a,b,pack_unpack]
      change (realFwd τ (if (a,b) ∈ τ then _ else b :: _) a).bind _ = _
      by_cases hm : (a,b) ∈ τ
      · rw [ite_eq_left hm, realFwd_known (fun _ _ _ ha hb => unique_out h ha (h _ _ hb)) hm]
        simpa only [Option.bind_some, a, b, pack_unpack, eval, publicPermutationQuery] using ih (p.forward x) τ h
      · have hi z (hz : (a,z) ∈ τ) := hm ((unique_out h hz e) ▸ hz)
        have ho z (hz : (z,b) ∈ τ) := hm ((unique_in h hz e) ▸ hz)
        rw [ite_eq_right hm, realFwd_fresh hi ho]
        simpa only [Option.bind_some, a, b, pack_unpack, eval, publicPermutationQuery] using ih (p.forward x) _ (agrees_cons h e)
    | inverse =>
      let a : SpSt r c := unpack x
      let b : SpSt r c := unpack (p.inverse x)
      have e : p.forward (pack b) = pack a := by simp [a,b,pack_unpack,p.forward_inverse]
      change (realInv τ (if (b,a) ∈ τ then _ else b :: _) a).bind _ = _
      by_cases hm : (b,a) ∈ τ
      · rw [ite_eq_left hm, realInv_known (fun _ _ _ ha hb => unique_in h ha (h _ _ hb)) hm]
        simpa only [Option.bind_some, a, b, pack_unpack, eval, publicPermutationQuery] using ih (p.inverse x) τ h
      · have hi z (hz : (z,a) ∈ τ) := hm ((unique_in h hz e) ▸ hz)
        have ho z (hz : (b,z) ∈ τ) := hm ((unique_out h hz e) ▸ hz)
        rw [ite_eq_right hm, realInv_fresh hi ho]
        simpa only [Option.bind_some, a, b, pack_unpack, eval, publicPermutationQuery] using ih (p.inverse x) _ (agrees_cons h e)

/-- Exact pushforward through the bounded-tape evaluator, with without-replacement coins.
The node, forward and inverse ports share one permutation and one evolving table. -/
theorem sponge_realRun_fisher_yates (ops : AbsorbOps β r) (s0 : SpSt r c)
    (A : SpAdv β r c O) (weight : Option O → Nat) :
    qsum (factorial (r*c)) (fun i =>
      weight (realRun ops s0 A [] (freshTape [] (lazyRun (record [] (sponge ops s0 A)) i).1))) =
    qsum (factorial (r*c)) (fun i => weight (some (eval ((upfront _).toFun i) (sponge ops s0 A)))) := by
  let B := sponge ops s0 A
  let w := fun v : Transcript (r*c) × O => weight (realRun ops s0 A [] (freshTape [] v.1))
  apply (equal_distribution (record [] B) w).trans
  apply congrArg (qsum _)
  funext i
  have replayed := replay_requests ((upfront _).toFun i) B [] (fun _ _ h => nomatch h)
  rw [replay_sponge] at replayed
  simp only [w, eval_record, List.reverse_nil, List.nil_append]
  exact congrArg weight replayed

/-- Two fresh forward inputs and two equal candidate coins exhaust the original bounded tape. -/
theorem finite_tape_exhaustion :
    realRun (bvAbsorbOps 1) ((0,0) : SpSt 2 1)
      (.fwd (0,0) (fun _ => .fwd (1,0) (fun _ => .done true))) [] [(0,0),(0,0)] = none := by
  simp +decide [realRun.public_eqs, realFwd.public_eqs, drawFreshOut.public_eqs,
    permFwd?.public_eqs, permInv?.public_eqs, List.find?]

#print axioms fresh_answer_completions
#print axioms joint_transcript_distribution
#print axioms sponge_realRun_fisher_yates
#print axioms finite_tape_exhaustion

/-! ## Transferring bounded-tape advantage to the full permutation

Count successful bounded runs from below, once for each verdict. Cached queries move
deterministically. At a miss, all unused answers have equally many permutation completions;
a used candidate consumes a coin and leaves the query pending. -/

private def opposite : Dir → Dir
  | .forward => .inverse
  | .inverse => .forward

private def edge (d : Dir) (x y : Fin (r*c)) : SpSt r c × SpSt r c :=
  match d with
  | .forward => (unpack x, unpack y)
  | .inverse => (unpack y, unpack x)

private def lookup (τ : PermTable r c) (d : Dir) (x : Fin (r*c)) : Option (SpSt r c) :=
  match d with
  | .forward => permFwd? τ (unpack x)
  | .inverse => permInv? τ (unpack x)

private theorem lookup_mem {τ : PermTable r c} {d x y} (h : lookup τ d x = some y) :
    edge d x (pack y) ∈ τ := by
  cases d <;> simp only [lookup, permFwd?.public_eqs, permInv?.public_eqs, Option.map_eq_some_iff] at h <;>
    obtain ⟨⟨a,b⟩,he,rfl⟩ := h <;>
    have hm := List.mem_of_find?_eq_some he <;>
    have test := List.find?_some he <;>
    simp only [decide_eq_true_eq] at test <;> simp only [edge, unpack_pack] <;> simpa only [test] using hm

private theorem missing_edge {τ : PermTable r c} {d x} (h : lookup τ d x = none)
    (y : Fin (r*c)) : edge d x y ∉ τ := by
  cases d <;> intro hm <;>
    simp only [lookup, permFwd?.public_eqs, permInv?.public_eqs, Option.map_eq_none_iff] at h <;>
    have test := List.find?_eq_none.mp h _ hm <;> exact test (by simp [edge])

private theorem agree_edge (p : Perm (r*c)) (d : Dir) (x y : Fin (r*c)) :
    p.forward (pack (edge d x y).1) = pack (edge d x y).2 ↔ publicPermutationQuery p d x = y := by
  cases d <;> simp only [edge, pack_unpack, publicPermutationQuery]
  exact ⟨fun h => (congrArg p.inverse h).symm.trans (p.inverse_forward _),
      fun h => (congrArg p.forward h.symm).trans (p.forward_inverse _)⟩

private theorem lookup_answer {τ : PermTable r c} {d x y} (h : lookup τ d x = some y)
    {p : Perm (r*c)} (ok : Agrees p τ) : publicPermutationQuery p d x = pack y :=
  (agree_edge ..).mp (ok _ _ (lookup_mem h))

private instance agreesDec (p : Perm (r*c)) (τ : PermTable r c) : Decidable (Agrees p τ) :=
  decidable_of_iff (τ.all (fun (x,y) => decide (p.forward (pack x) = pack y)) = true)
    ⟨fun h x y hm => of_decide_eq_true (List.all_eq_true.mp h (x,y) hm),
      fun h => List.all_eq_true.mpr (fun (x,y) he => decide_eq_true (h x y he))⟩

private theorem agrees_edge_iff {p : Perm (r*c)} {d x y} {τ : PermTable r c} :
    Agrees p (edge d x y :: τ) ↔ Agrees p τ ∧ publicPermutationQuery p d x = y := by
  constructor
  · intro h
    exact ⟨fun _ _ hm => h _ _ (.tail _ hm), (agree_edge ..).mp (h _ _ (.head _))⟩
  · intro ⟨h,e⟩
    exact agrees_cons h ((agree_edge ..).mpr e)

private def swapAt (a b z : Fin n) := if z = a then b else if z = b then a else z
private theorem swapAt_twice (a b z : Fin n) : swapAt a b (swapAt a b z) = z := by
  by_cases ha : z = a <;> by_cases hb : z = b <;> by_cases eq : a = b <;> simp_all [swapAt]

private def exchangeOut (a b : Fin n) (p : Perm n) : Perm n where
  forward z := swapAt a b (p.forward z)
  inverse z := p.inverse (swapAt a b z)
  inverse_forward _ := by rw [swapAt_twice, p.inverse_forward]
  forward_inverse _ := by rw [p.forward_inverse, swapAt_twice]

private def exchange (d : Dir) (a b : Fin n) (p : Perm n) :=
  match d with
  | .forward => exchangeOut a b p
  | .inverse => flip (exchangeOut a b (flip p))

private theorem exchange_twice (d : Dir) (a b : Fin n) (p : Perm n) :
    exchange d a b (exchange d a b p) = p := by
  cases d <;> apply perm_ext <;> intro x <;> simp [exchange, exchangeOut, flip, swapAt_twice]

private theorem exchange_query (d : Dir) (a b x : Fin n) (p : Perm n) :
    publicPermutationQuery (exchange d a b p) d x = swapAt a b (publicPermutationQuery p d x) := by
  cases d <;> rfl

private theorem exchange_agrees {τ : PermTable r c} {d a b}
    (ha : lookup τ (opposite d) a = none) (hb : lookup τ (opposite d) b = none)
    (p : Perm (r*c)) (h : Agrees p τ) : Agrees (exchange d a b p) τ := by
  intro x y hm
  cases d with
  | forward =>
    have ne {z} (hz : lookup τ .inverse z = none) : pack y ≠ z := by
      intro eq
      subst z
      exact missing_edge hz (pack x) (by simpa only [edge, unpack_pack] using hm)
    change swapAt a b (p.forward (pack x)) = pack y
    simp [h _ _ hm, swapAt, ne ha, ne hb]
  | inverse =>
    have ne {z} (hz : lookup τ .forward z = none) : pack x ≠ z := by
      intro eq
      subst z
      exact missing_edge hz (pack y) (by simpa only [edge, unpack_pack] using hm)
    change p.forward (swapAt a b (pack x)) = pack y
    simp [swapAt, ne ha, ne hb, h _ _ hm]

private def mass (τ : PermTable r c) (weight : Perm (r*c) → Nat) :=
  qsum (factorial (r*c)) fun i =>
    let p := (upfront _).toFun i
    if Agrees p τ then weight p else 0

private theorem branch_mass (τ : PermTable r c) (d : Dir) (x : Fin (r*c))
    (weight : Fin (r*c) → Perm (r*c) → Nat) :
    qsum (r*c) (fun y => mass (edge d x y :: τ) (weight y)) =
      mass τ (fun p => weight (publicPermutationQuery p d x) p) := by
  unfold mass
  rw [qsum_comm]
  apply qsum_congr
  intro i
  let p := (upfront _).toFun i
  by_cases ok : Agrees p τ
  · change qsum _ (fun y => if Agrees p (edge d x y::τ) then weight y p else 0) = _
    simp only [agrees_edge_iff, ok, true_and]
    apply (qsum_congr (g := fun y => if y = publicPermutationQuery p d x
      then weight (publicPermutationQuery p d x) p else 0) ?_).trans
    · simpa only [p, ok, ↓reduceIte] using qsum_ite_eq _ (publicPermutationQuery p d x) (weight _ p)
    · intro y
      by_cases eq : y = publicPermutationQuery p d x <;> simp [Ne.symm, *]
  · simp only [agrees_edge_iff, show ¬ Agrees ((upfront _).toFun i) τ from ok,
      false_and, ↓reduceIte, qsum_const, Nat.mul_zero]

private theorem equal_fresh_fibers (τ : PermTable r c) (d : Dir) (x a b : Fin (r*c))
    (ha : lookup τ (opposite d) a = none) (hb : lookup τ (opposite d) b = none) :
    mass (edge d x a :: τ) (fun _ => 1) = mass (edge d x b :: τ) (fun _ => 1) := by
  let E : SimpleEquiv (Perm (r*c)) (Perm (r*c)) :=
    ⟨exchange d a b, exchange d a b, exchange_twice d a b, exchange_twice d a b⟩
  apply Eq.trans _ (qsum_bijection_invariant (upfront _) E
    (fun p => if Agrees p (edge d x b :: τ) then 1 else 0))
  apply qsum_congr
  intro i
  let p := (upfront _).toFun i
  change (if Agrees p (edge d x a :: τ) then 1 else 0) =
    (if Agrees (exchange d a b p) (edge d x b :: τ) then 1 else 0)
  have iff : Agrees (exchange d a b p) τ ↔ Agrees p τ := ⟨fun h => by
    simpa only [exchange_twice] using exchange_agrees ha hb _ h, exchange_agrees ha hb _⟩
  simp only [agrees_edge_iff, iff, exchange_query]
  have sw (z : Fin (r*c)) : swapAt a b z = b ↔ z = a := by
    by_cases h : z = a
    · simp [swapAt,h]
    · by_cases hb : z = b
      · subst z; simp [swapAt,h,Ne.symm h]
      · simp [swapAt,h,hb]
  simp only [sw]

private theorem occupied_mass (τ : PermTable r c) (d : Dir) (x y : Fin (r*c))
    (hx : lookup τ d x = none) (hy : lookup τ (opposite d) y ≠ none)
    (w : Perm (r*c) → Nat) : mass (edge d x y :: τ) w = 0 := by
  obtain ⟨z,hz⟩ := Option.ne_none_iff_exists'.mp hy
  have impossible (p : Perm (r*c)) (h : Agrees p (edge d x y :: τ)) : False := by
    obtain ⟨ok,ans⟩ := agrees_edge_iff.mp h
    have eq := lookup_answer hz ok
    have hm := lookup_mem hz
    cases d with
    | forward =>
      change p.forward x = y at ans
      change p.inverse y = pack z at eq
      rw [← ans,p.inverse_forward] at eq
      exact missing_edge hx y (by simpa only [eq,edge,opposite] using hm)
    | inverse =>
      change p.inverse x = y at ans
      change p.forward y = pack z at eq
      rw [← ans,p.forward_inverse] at eq
      exact missing_edge hx y (by simpa only [eq,edge,opposite] using hm)
  unfold mass
  exact (qsum_congr (g := fun _ => 0) (fun i => ite_eq_right (impossible _))).trans
    ((qsum_const _ 0).trans (Nat.mul_zero _))

private def tapes (n : Nat) : Nat → (List (Fin n) → Nat) → Nat
  | 0,f => f []
  | k+1,f => qsum n (fun d => tapes n k (fun t => f (d::t)))

private theorem tapes_const (n k a : Nat) :
    tapes n k (fun _ => a) = Spec.roCoinPow n k * a := by
  induction k with
  | zero => exact (Nat.one_mul _).symm
  | succ k ih => simp only [tapes, ih, qsum_const, Nat.mul_assoc]

private theorem tapes_encode (k : Nat) (f : List (SpSt r c) → Nat) :
    tapes (r*c) k (fun t => f (t.map unpack)) =
      qsum (Spec.roCoinPow (r*c) k) (fun i => f (coinList k i)) := by
  induction k generalizing f with
  | zero => simp only [coinList_zero]; change f [] = qsum 1 (fun _ => f []); simp [qsum_const]
  | succ k ih =>
    let s := Spec.CoinSplit.prod (r*c) (Spec.roCoinPow (r*c) k)
    rw [qsum_coinSplit s]
    apply qsum_congr
    intro d
    apply (ih (fun t => f (unpack d :: t))).trans
    apply qsum_congr
    intro i
    exact congrArg f (coinList_pair k d i).symm

private def success (A : Program (r*c) Bool) (τ : PermTable r c) (v : Bool) (t : List (Fin (r*c))) :=
  (decide (replay A τ (t.map unpack) = some v)).toNat

private theorem replay_hit {τ : PermTable r c} {d x y} (h : lookup τ d x = some y)
    (k : Fin (r*c) → Program (r*c) O) (ω) :
    replay (.query d x k) τ ω = replay (k (pack y)) τ ω := by
  cases d <;> simp only [lookup] at h <;> simp [replay, realFwd.public_eqs, realInv.public_eqs, h]

private theorem replay_empty {τ : PermTable r c} {d x} (h : lookup τ d x = none)
    (k : Fin (r*c) → Program (r*c) O) : replay (.query d x k) τ [] = none := by
  cases d <;> simp only [lookup] at h <;> simp [replay, realFwd.public_eqs, realInv.public_eqs, h, drawFreshIn.public_eqs, drawFreshOut.public_eqs]

private theorem replay_head {τ : PermTable r c} {d x} (h : lookup τ d x = none)
    (k : Fin (r*c) → Program (r*c) O) (y : Fin (r*c)) (tail : List (SpSt r c)) :
    replay (.query d x k) τ (unpack y :: tail) =
      if lookup τ (opposite d) y = none then replay (k y) (edge d x y :: τ) tail
      else replay (.query d x k) τ tail := by
  cases d <;> simp only [lookup] at h
  · cases hh : permInv? τ (unpack y) <;>
      simp [replay, realFwd.public_eqs, h, drawFreshOut.public_eqs, hh, lookup, opposite, edge, pack_unpack]
  · cases hh : permFwd? τ (unpack y) <;>
      simp [replay, realInv.public_eqs, h, drawFreshIn.public_eqs, hh, lookup, opposite, edge, pack_unpack]

/-- Algebra of a fresh step: the unused branches partition both the completion space
and its successful subset. All used branches retry from the same state. -/
private theorem retry_sum {n : Nat} (free : Fin n → Bool) (coins wins raw : Fin n → Nat)
    (C W T : Nat)
    (hc : qsum n coins = C) (hw : qsum n wins = W)
    (equal : ∀ a b, free a = true → free b = true → coins a = coins b)
    (zero : ∀ a, free a = false → coins a = 0 ∧ wins a = 0)
    (fresh : ∀ a, free a = true → coins a * raw a ≤ T * wins a)
    (used : ∀ a, free a = false → C * raw a ≤ T * W) :
    C * qsum n raw ≤ (n*T)*W := by
  let M := qsum n (fun a => (free a).toNat)
  let U := qsum n (fun a => (!(free a)).toNat)
  have total : U + M = n := by
    unfold U M
    rw [← qsum_add]
    exact (qsum_congr (g := fun _ => 1) (fun i => by cases free i <;> decide)).trans
      ((qsum_const _ _).trans (Nat.mul_one _))
  have scale (a : Fin n) (h : free a = true) : C = M * coins a := by
    rw [← hc, ← qsum_mul_right]
    apply qsum_congr
    intro j
    cases hj : free j with
    | false => simpa only [hj, Bool.toNat_false, Nat.zero_mul] using (zero j hj).1
    | true => simpa only [hj, Bool.toNat_true, Nat.one_mul] using equal j a hj h
  have per (a : Fin n) : C * raw a ≤ (!(free a)).toNat * (T*W) + (M*T)*wins a := by
    cases h : free a with
    | true =>
      simp only [Bool.not_true, Bool.toNat_false, Nat.zero_mul, Nat.zero_add]
      rw [scale a h, Nat.mul_assoc, Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (fresh a h)
    | false => simpa only [Bool.not_false, Bool.toNat_true, Nat.one_mul,
        (zero a h).2, Nat.mul_zero, Nat.add_zero] using used a h
  rw [← qsum_mul_left]
  apply Nat.le_trans (qsum_le_qsum per)
  rw [qsum_add, qsum_mul_right, qsum_mul_left, hw]
  change U * (T*W) + (M*T)*W ≤ _
  rw [← Nat.mul_assoc, ← Nat.add_mul, ← Nat.add_mul, total]
  exact Nat.le_refl _

/-- Bounded IID rejection is a subdistribution of the upfront game, for either verdict.
Multiplying by the number of compatible permutations avoids division at empty fibers. -/
private theorem bounded_success (K : Nat) (A : Program (r*c) Bool) (τ : PermTable r c) (v : Bool) :
    mass τ (fun _ => 1) * tapes (r*c) K (success A τ v) ≤
      Spec.roCoinPow (r*c) K * mass τ (fun p => (decide (eval p A = v)).toNat) := by
  induction K generalizing A τ with
  | zero =>
    induction A with
    | done o =>
      by_cases e : o = v <;> simp [success, tapes, replay, eval, e, mass, Spec.roCoinPow]
    | query d x k ih =>
      cases h : lookup τ d x with
      | none => simp [tapes, success, replay_empty h]
      | some y =>
        have ih' := ih (pack y)
        simp only [tapes, success, replay_hit h, List.map_nil] at ih' ⊢
        apply Nat.le_trans ih' (Nat.le_of_eq ?_)
        congr 1
        apply qsum_congr
        intro i
        dsimp only
        by_cases ok : Agrees ((upfront _).toFun i) τ
        · simp only [ok, ↓reduceIte, eval, lookup_answer h ok]
        · simp only [ok, ↓reduceIte]
  | succ K outer =>
    induction A with
    | done o =>
      have eq : success (.done o) τ v = fun _ => (decide (o = v)).toNat := by
        funext t; simp [success,replay]
      rw [eq,tapes_const]
      by_cases e : o = v <;> simp [eval, e, mass, Nat.mul_comm, qsum_const]
    | query d x k ih =>
      cases h : lookup τ d x with
      | some y =>
        have eq : success (.query d x k) τ v = success (k (pack y)) τ v := by
          funext t; simp [success, replay_hit h]
        rw [eq]
        apply Nat.le_trans (ih (pack y)) (Nat.le_of_eq ?_)
        congr 1
        apply qsum_congr
        intro i
        dsimp only
        by_cases ok : Agrees ((upfront _).toFun i) τ
        · simp only [ok, ↓reduceIte, eval, lookup_answer h ok]
        · simp only [ok, ↓reduceIte]
      | none =>
        let free (y : Fin (r*c)) := (lookup τ (opposite d) y).isNone
        let T := Spec.roCoinPow (r*c) K
        let raw (y : Fin (r*c)) := tapes _ K (fun t => success (.query d x k) τ v (y::t))
        let win (y : Fin (r*c)) (p : Perm (r*c)) := (decide (eval p (k y) = v)).toNat
        apply retry_sum free (fun y => mass (edge d x y :: τ) (fun _ => 1))
          (fun y => mass (edge d x y :: τ) (win y)) raw _ _ T
        · exact branch_mass τ d x (fun _ _ => 1)
        · exact branch_mass τ d x win
        · intro a b ha hb
          exact equal_fresh_fibers τ d x a b (Option.isNone_iff_eq_none.mp ha)
            (Option.isNone_iff_eq_none.mp hb)
        · intro a ha
          have ne : lookup τ (opposite d) a ≠ none := fun e => by simp [free,e] at ha
          exact ⟨occupied_mass _ _ _ _ h ne _, occupied_mass _ _ _ _ h ne _⟩
        · intro a ha
          have he := Option.isNone_iff_eq_none.mp ha
          have eq : raw a = tapes _ K (success (k a) (edge d x a :: τ) v) := by
            unfold raw
            apply congrArg (tapes _ K)
            funext t; simp [success, replay_head h, he]
          rw [eq]
          exact outer _ _
        · intro a ha
          have ne : lookup τ (opposite d) a ≠ none := fun e => by simp [free,e] at ha
          have eq : raw a = tapes _ K (success (.query d x k) τ v) := by
            unfold raw
            apply congrArg (tapes _ K)
            funext t; simp [success, replay_head h, ne]
          rw [eq]
          exact outer _ _

private theorem factorial_pos : ∀ n, 0 < factorial n
  | 0 => Nat.one_pos
  | n+1 => Nat.mul_pos (Nat.succ_pos _) (factorial_pos n)

def upfrontGame (ops : AbsorbOps β r) (s0 : SpSt r c) (A : SpAdv β r c Bool) :
    Spec.FinGame (factorial (r*c)) :=
  ⟨factorial_pos _,fun i => eval ((upfront _).toFun i) (sponge ops s0 A)⟩

private def verdictCount (n : Nat) (f : Fin n → Bool) (v : Bool) :=
  qsum n (fun i => (decide (f i = v)).toNat)

private theorem verdicts_total (n : Nat) (f : Fin n → Bool) :
    verdictCount n f false + verdictCount n f true = n := by
  unfold verdictCount
  rw [← qsum_add]
  exact (qsum_congr (g := fun _ => 1) (fun i => by cases f i <;> decide)).trans
    ((qsum_const _ _).trans (Nat.mul_one _))

private theorem verdict_true (G : Spec.FinGame n) : verdictCount n G.win true = G.winCount := by
  rw [Spec.FinGame.winCount_eq, ← qsum_eq_sampleSum]
  exact qsum_congr (fun i => by cases G.win i <;> rfl)

private def rawCount (ops : AbsorbOps β r) (s0 : SpSt r c) (A : SpAdv β r c Bool) (K : Nat)
    (v : Bool) := qsum (Spec.roCoinPow (r*c) K) (fun i =>
      (decide (realRun ops s0 A [] (coinList K i) = some v)).toNat)

private theorem raw_le_upfront (ops : AbsorbOps β r) (s0 : SpSt r c) (A : SpAdv β r c Bool)
    (K : Nat) (v : Bool) : factorial (r*c) * rawCount ops s0 A K v ≤
      Spec.roCoinPow (r*c) K * verdictCount _ (upfrontGame ops s0 A).win v := by
  have h := bounded_success K (sponge ops s0 A) [] v
  have empty (p : Perm (r*c)) : Agrees p ([] : PermTable r c) := fun _ _ h => nomatch h
  have count : mass ([] : PermTable r c) (fun _ => 1) = factorial (r*c) := by
    unfold mass
    exact (qsum_congr (g := fun _ => 1) (fun i => ite_eq_left (empty _))).trans
      ((qsum_const _ _).trans (Nat.mul_one _))
  have raw : tapes (r*c) K (success (sponge ops s0 A) [] v) = rawCount ops s0 A K v := by
    apply Eq.trans _ (tapes_encode K (fun t => (decide (realRun ops s0 A [] t = some v)).toNat))
    apply congrArg (tapes _ K)
    funext t
    simp only [success,replay_sponge]
  rw [count,raw] at h
  apply Nat.le_trans h (Nat.le_of_eq ?_)
  congr 1

private theorem completions_counts (hr : 0 < r) (hc : 0 < c) (ops : AbsorbOps β r)
    (s0 : SpSt r c) (A : SpAdv β r c Bool) (K : Nat) :
    (realGameWithCompletion hr hc ops s0 A K (fun _ => false)).winCount = rawCount ops s0 A K true ∧
    (realGameWithCompletion hr hc ops s0 A K (fun _ => true)).winCount + rawCount ops s0 A K false =
      Spec.roCoinPow (r*c) K := by
  simp only [Spec.FinGame.winCount_eq, ← qsum_eq_sampleSum, realGameWithCompletion_win, rawCount]
  constructor
  · apply qsum_congr
    intro i
    exact (show ∀ z : Option Bool, (if z.getD false then 1 else 0) =
      (decide (z = some true)).toNat from by intro z; cases z with
        | none => rfl
        | some b => cases b <;> rfl) _
  · rw [← qsum_add]
    apply (qsum_congr (g := fun _ => 1) ?_).trans ((qsum_const _ _).trans (Nat.mul_one _))
    intro i
    exact (show ∀ z : Option Bool, (if z.getD true then 1 else 0) +
      (decide (z = some false)).toNat = 1 from by intro z; cases z with
        | none => rfl
        | some b => cases b <;> rfl) _

private theorem abs_between {a x b y : Nat} (lo : a ≤ x) (hi : x ≤ b) :
    natAbsDiff x y ≤ max (natAbsDiff a y) (natAbsDiff b y) := by
  simp only [natAbsDiff_eq]
  split <;> split <;> split <;> omega

/-- Exact difference of the full-permutation and ideal-oracle probabilities on their
common product denominator. -/
def upfrontAdvantage [DecidableEq β] (hr : 0 < r) (hc : 0 < c) (ops : AbsorbOps β r)
    (s0 : SpSt r c) (A : SpAdv β r c Bool) (K : Nat) : Spec.RatBound :=
  let T := Spec.roCoinPow (r*c) K
  let F := factorial (r*c)
  ⟨natAbsDiff (T * (upfrontGame ops s0 A).winCount)
      (F * (privateOracleGame hr hc ops s0 A K).winCount),
    F*T, Nat.mul_pos (factorial_pos _) (Spec.roCoinPow_pos (Nat.mul_pos hr hc) _)⟩

theorem full_permutation_two_way_bound [DecidableEq β] (hr : 0 < r) (hc : 0 < c)
    (ops : AbsorbOps β r) (s0 : SpSt r c) (A : SpAdv β r c Bool) (K : Nat)
    (budget : BlockCost A K) : Spec.GameBound (upfrontAdvantage hr hc ops s0 A K) ⟨K*(K+1),c,hc⟩ := by
  let F := factorial (r*c)
  let T := Spec.roCoinPow (r*c) K
  let up := (upfrontGame ops s0 A).winCount
  let ideal := (privateOracleGame hr hc ops s0 A K).winCount
  let bot := (realGameWithCompletion hr hc ops s0 A K (fun _ => false)).winCount
  let top := (realGameWithCompletion hr hc ops s0 A K (fun _ => true)).winCount
  obtain ⟨lowCount,highCount⟩ := completions_counts hr hc ops s0 A K
  have low : F*bot ≤ T*up := by
    simpa only [F,bot,up,lowCount,verdict_true,T] using raw_le_upfront ops s0 A K true
  have high : T*up ≤ F*top := by
    let loses := verdictCount _ (upfrontGame ops s0 A).win false
    let bad := rawCount ops s0 A K false
    have bound : F*bad ≤ T*loses := raw_le_upfront ops s0 A K false
    have total : loses + up = F := by
      simpa only [verdict_true,loses,up,F] using verdicts_total _ (upfrontGame ops s0 A).win
    have e1 : T*loses + T*up = T*F := (Nat.mul_add ..).symm.trans (congrArg (T * ·) total)
    have e2 : F*top + F*bad = F*T := (Nat.mul_add ..).symm.trans (congrArg (F * ·) highCount)
    rw [Nat.mul_comm T F] at e1
    omega
  have endpoint (b : Bool) :
      natAbsDiff (realGameWithCompletion hr hc ops s0 A K (fun _ => b)).winCount ideal * c ≤
        (K*(K+1))*T := by
    rw [natAbsDiff_eq]
    exact sponge_completed_two_way_bound hr hc ops s0 A K budget (fun _ => b)
  have scale (b : Bool) : (F * natAbsDiff (realGameWithCompletion hr hc ops s0 A K
      (fun _ => b)).winCount ideal) * c ≤ (K*(K+1))*(F*T) := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left F (endpoint b)
  have between := abs_between (y := F*ideal) low high
  rw [natAbsDiff_mul_left, natAbsDiff_mul_left] at between
  change natAbsDiff (T*up) (F*ideal) * c ≤ (K*(K+1))*(F*T)
  apply Nat.le_trans (Nat.mul_le_mul_right c between)
  by_cases h : F*natAbsDiff bot ideal ≤ F*natAbsDiff top ideal
  · rw [Nat.max_eq_right h]; exact scale true
  · rw [Nat.max_eq_left (by omega)]; exact scale false

set_option exponentiation.threshold 2048 in
theorem byte_full_permutation_431_bits (A : ByteAdv Bool) (K : Nat) (hK : K ≤ 2^40)
    (budget : BlockCost A.toBlocks K) :
    (upfrontAdvantage (Nat.two_pow_pos 1088) (Nat.two_pow_pos 512) (bvAbsorbOps 1088)
      (0,0) A.toBlocks K).atLeastBits 431 :=
  Spec.GameBound.atLeastBits (full_permutation_two_way_bound _ _ _ _ _ _ budget) (keccak_budget_margin K hK)

#print axioms full_permutation_two_way_bound
#print axioms byte_full_permutation_431_bits
end Qsag.LazyPermutation
