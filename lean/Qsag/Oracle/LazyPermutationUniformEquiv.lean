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

/-- Give the FB5 evaluator one coin for each newly revealed edge, in query order. -/
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

/-- Exact pushforward through FB5's own evaluator, with without-replacement coins.
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
