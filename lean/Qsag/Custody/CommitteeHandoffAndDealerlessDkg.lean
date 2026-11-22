module
public import Qsag.Math.Goldilocks
public import Qsag.Math.Counting
public import Qsag.Spec.Assumptions
import Qsag.Tactic.Prelude

public section
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag.CommitteeHandoffJorts

abbrev Party := Fin 5
abbrev Votes := Party → Bool

def count (v : Votes) : Nat :=
  (v 0).toNat + (v 1).toNat + (v 2).toNat + (v 3).toNat + (v 4).toNat

private theorem local_bound (a b c : Bool) (h : ¬ (a = true ∧ b = true ∧ c = false)) :
    a.toNat + b.toNat ≤ 1 + c.toNat := by
  cases a <;> cases b <;> cases c <;> first | decide | exact False.elim (h ⟨rfl, rfl, rfl⟩)

theorem honest_intersection (a b corrupt : Votes)
    (h : 5 + count corrupt < count a + count b) :
    ∃ p, a p = true ∧ b p = true ∧ corrupt p = false := by
  by_cases ex : ∃ p, a p = true ∧ b p = true ∧ corrupt p = false
  · exact ex
  · have hb (p : Party) := local_bound (a p) (b p) (corrupt p) (fun hp => ex ⟨p, hp⟩)
    have := hb 0
    have := hb 1
    have := hb 2
    have := hb 3
    have := hb 4
    unfold count at h
    omega

theorem four_vote_intersection {a b corrupt : Votes} (ha : 4 ≤ count a)
    (hb : 4 ≤ count b) (hc : count corrupt ≤ 2) :
    ∃ p, a p = true ∧ b p = true ∧ corrupt p = false :=
  honest_intersection _ _ _ (by omega)

structure Lease where
  lo : Nat
  hi : Nat
  members : Votes
  nonempty : lo < hi
  threshold : count members = 3

def Covers (l : Lease) (leaf : Nat) := l.lo ≤ leaf ∧ leaf < l.hi

/-- An anchored log of distinct reservations. Retrying the same binding leaves it unchanged. -/
inductive LockHistory : Nat → List Lease → Prop
  | genesis : LockHistory 0 []
  | reserve : LockHistory w log → w ≤ l.lo → LockHistory l.hi (l :: log)

theorem LockHistory.highWater {w log} (h : LockHistory w log) {l : Lease} (hm : l ∈ log) :
    l.hi ≤ w := by
  induction h with
  | genesis => cases hm
  | reserve old advances ih =>
    rcases List.mem_cons.mp hm with rfl | ht
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih ht) (Nat.le_trans advances (Nat.le_of_lt ‹Lease›.nonempty))

theorem LockHistory.binding {w log} (h : LockHistory w log) {a b : Lease} {i : Nat}
    (ha : a ∈ log) (hb : b ∈ log) (ca : Covers a i) (cb : Covers b i) : a = b := by
  induction h with
  | genesis => cases ha
  | reserve old advances ih =>
    rcases List.mem_cons.mp ha with rfl | hta <;> rcases List.mem_cons.mp hb with rfl | htb
    · rfl
    · have := old.highWater htb
      obtain ⟨_, _⟩ := cb
      obtain ⟨_, _⟩ := ca
      exfalso
      omega
    · have := old.highWater hta
      obtain ⟨_, _⟩ := cb
      obtain ⟨_, _⟩ := ca
      exfalso
      omega
    · exact ih hta htb

def Backed (logs : Party → List Lease) (v : Votes) (l : Lease) :=
  ∀ p, v p = true → l ∈ logs p

theorem four_vote_safety {logs : Party → List Lease} {a b corrupt : Votes}
    {s t : Lease} {i : Nat} (ha : 4 ≤ count a) (hb : 4 ≤ count b) (hc : count corrupt ≤ 2)
    (locked : ∀ p, corrupt p = false → ∃ w, LockHistory w (logs p))
    (sa : Backed logs a s) (tb : Backed logs b t) (cs : Covers s i) (ct : Covers t i) :
    s = t := by
  obtain ⟨p, ap, bp, hp⟩ := four_vote_intersection ha hb hc
  obtain ⟨_, hist⟩ := locked p hp
  exact hist.binding (sa p ap) (tb p bp) cs ct

theorem three_vote_lock_safety {logs : Party → List Lease} {a b : Votes} {s t : Lease} {i : Nat}
    (ha : 3 ≤ count a) (hb : 3 ≤ count b)
    (locked : ∀ p, ∃ w, LockHistory w (logs p))
    (sa : Backed logs a s) (tb : Backed logs b t) (cs : Covers s i) (ct : Covers t i) :
    s = t := by
  obtain ⟨p, ap, bp, _⟩ := honest_intersection a b (fun _ => false)
    (by change 5 + 0 < _; omega)
  obtain ⟨_, hist⟩ := locked p
  exact hist.binding (sa p ap) (tb p bp) cs ct

def leftThree : Votes := fun p => decide (p.val < 3)
def rightThree : Votes := fun p => decide (2 ≤ p.val)
private def leftLease : Lease := ⟨0, 1, leftThree, by decide, by decide⟩
private def rightLease : Lease := ⟨0, 1, rightThree, by decide, by decide⟩

theorem tooth_three_vote_single_equivocator :
    ∃ (logs : Party → List Lease) (a b : Votes) (s t : Lease),
      count a = 3 ∧ count b = 3 ∧ Backed logs a s ∧ Backed logs b t ∧
      (∀ p : Party, p ≠ 2 → LockHistory 1 (logs p)) ∧ Covers s 0 ∧ Covers t 0 ∧ s ≠ t := by
  let logs : Party → List Lease := fun p =>
    if p.val < 2 then [leftLease] else if p.val = 2 then [leftLease, rightLease] else [rightLease]
  refine ⟨logs, leftThree, rightThree, leftLease, rightLease, by decide, by decide, ?_, ?_, ?_,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  · intro p hp
    have h : p.val < 3 := of_decide_eq_true hp
    by_cases h' : p.val < 2
    · simp [logs, h']
    · have h2 : p.val = 2 := by omega
      simp [logs, h2]
  · intro p hp
    have h : 2 ≤ p.val := of_decide_eq_true hp
    have h' : ¬ p.val < 2 := by omega
    by_cases h2 : p.val = 2 <;> simp [logs, h', h2]
  · intro p hp
    have h : p.val ≠ 2 := fun e => hp (Fin.ext e)
    simp [logs, h]
    split
    · exact LockHistory.reserve (l := leftLease) .genesis (Nat.zero_le _)
    · exact LockHistory.reserve (l := rightLease) .genesis (Nat.zero_le _)
  · intro he
    have := congrArg (fun l : Lease => l.members 0) he
    exact Bool.noConfusion this

#print axioms four_vote_safety
#print axioms honest_intersection
#print axioms three_vote_lock_safety
#print axioms tooth_three_vote_single_equivocator
#tooth_pair three_vote_lock_safety vs tooth_three_vote_single_equivocator
end Qsag.CommitteeHandoffJorts

namespace Qsag.DealerlessPersonalReleaseDkg
open CommRingOps LawfulCommRing
abbrev Columns (width : Nat) := Fin width → Goldilocks

/-- The aggregate of all dealers except the selected honest one. -/
def sumOthers {w} (others : List (Columns w)) (j : Fin w) : Goldilocks :=
  others.foldr (fun row acc => add (row j) acc) zero

def enroll {w} (others : List (Columns w)) (honest : Columns w) : Columns w :=
  fun j => add (sumOthers others j) (honest j)

/-- Exactly one honest random tape per aggregate, for every fixed tuple of other tapes. -/
theorem uniform_columns {w} (others : List (Columns w)) (target : Columns w) :
    ∃ tape, enroll others tape = target ∧ ∀ tape', enroll others tape' = target → tape' = tape := by
  let tape : Columns w := fun j => sub (target j) (sumOthers others j)
  have he : enroll others tape = target := funext fun _ => add_sub_cancel_left _ _
  exact ⟨tape, he, fun _ h => funext fun j => add_left_cancel (congrFun (h.trans he.symm) j)⟩

/-- Binary row projection received by an owner, in one field lane. -/
def project {w} (row : List (Fin w)) (x : Columns w) : Goldilocks :=
  row.foldr (fun j acc => add (x j) acc) zero

private theorem project_add {w} (row : List (Fin w)) (x y : Columns w) :
    project row (fun j => add (x j) (y j)) = add (project row x) (project row y) := by
  induction row with
  | nil => exact (zero_add _).symm
  | cons j js ih => exact (congrArg (add _) ih).trans (add_add_add_comm ..)

/-- Translation by a kernel vector preserves every corrupt row, including each sender's
own projection when the translation is made on the honest sender's tape. -/
theorem row_view_translation {w} (rows : List (List (Fin w))) (shift : Columns w)
    (hk : ∀ row ∈ rows, project row shift = zero) (x : Columns w) :
    rows.map (fun row => project row (fun j => add (x j) (shift j))) =
      rows.map (fun row => project row x) := by
  apply List.map_congr_left
  intro row hm
  rw [project_add, hk row hm, add_zero]

def fieldEnum : SimpleEquiv (Fin goldilocksPrime) Goldilocks where
  toFun x := ⟨x.val,x.isLt⟩
  invFun x := ⟨x.val,x.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

def tapeCount : Nat → Nat
  | 0 => 1
  | w+1 => goldilocksPrime * tapeCount w

/-- One independent radix-p digit per column (including all four lanes and all batches
when these are flattened as in enrollment). -/
def columnEnum : (w : Nat) → SimpleEquiv (Fin (tapeCount w)) (Columns w)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => (0 : Fin 1)
      left_inv := fun _ => @Subsingleton.elim (Fin 1) _ _ _
      right_inv := fun _ => funext fun i => Fin.elim0 i }
  | w+1 =>
    let split := Spec.CoinSplit.prod goldilocksPrime (tapeCount w)
    let tail := columnEnum w
    { toFun := fun c => Fin.cases (fieldEnum.toFun (split.chal c)) (tail.toFun (split.advc c))
      invFun := fun x => split.pair (fieldEnum.invFun (x 0)) (tail.invFun (fun i => x i.succ))
      left_inv := fun c => by
        simp only [Fin.cases_zero, Fin.cases_succ, fieldEnum.left_inv, tail.left_inv]
        exact split.pair_eta c
      right_inv := fun x => by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cases_zero, split.chal_pair, fieldEnum.right_inv]
        · simp only [Fin.cases_succ, split.advc_pair, tail.right_inv] }

/-- Conditioning on any fixed other-dealer tapes preserves the uniform joint law, in
the library's finite-game sense. The input sampler covers every possible honest tape. -/
theorem conditional_uniform {w n} (sample : Fin n → Columns w)
    (uniform : Spec.UniformOn (fun _ => True) sample) (others : List (Columns w)) :
    Spec.UniformOn (fun _ => True) (fun coin => enroll others (sample coin)) where
  mem _ := True.intro
  injective i j he := uniform.injective i j (funext fun k => add_left_cancel (congrFun he k))
  surjective target _ := by
    obtain ⟨tape,ht,_⟩ := uniform_columns others target
    obtain ⟨c,hc⟩ := uniform.surjective tape trivial
    exact ⟨c, hc ▸ ht⟩

theorem dealerless_sum_uniform {w} (others : List (Columns w)) :
    Spec.UniformOn (fun _ => True) (fun c => enroll others ((columnEnum w).toFun c)) := by
  apply conditional_uniform
  exact ⟨fun _ => trivial, fun i j h => by
    simpa only [SimpleEquiv.left_inv] using congrArg (columnEnum w).invFun h,
    fun x _ => ⟨_, (columnEnum w).right_inv x⟩⟩

def view {w} (rows : List (List (Fin w))) (x : Columns w) :=
  rows.map (fun r => project r x)

/-- Secret privacy for an unauthorized row set. A kernel direction with unit secret
coordinate is the MSP privacy witness. Multiplying it by any field delta preserves the view. -/
private theorem project_scale {w} (r : List (Fin w)) (c : Goldilocks) (v : Columns w) :
    project r (fun i => mul c (v i)) = mul c (project r v) := by
  induction r with
  | nil => exact (mul_zero _).symm
  | cons j js ih => exact (congrArg (add _) ih).trans (left_distrib ..).symm

abbrev secretFiber {w} (j : Fin w) (rows : List (List (Fin w))) (obs : List Goldilocks)
    (s : Goldilocks) := {x : Columns w // x j = s ∧ view rows x = obs}

theorem secret_view_fibers {w} (j : Fin w) (rows : List (List (Fin w)))
    (v : Columns w) (vj : v j = one) (kernel : ∀ r ∈ rows, project r v = zero)
    (obs : List Goldilocks) (a b : Goldilocks) :
    Nonempty (SimpleEquiv (secretFiber j rows obs a) (secretFiber j rows obs b)) := by
  let shift : Columns w := fun i => mul (sub b a) (v i)
  have hk : ∀ r ∈ rows, project r shift = zero := fun r hr => by
    simp only [shift, project_scale, kernel r hr, mul_zero]
  have hn : ∀ r ∈ rows, project r (fun i => neg (shift i)) = zero := by
    intro r hr
    apply add_left_cancel (a := project r shift)
    rw [← project_add, add_zero]
    have z : (fun i => add (shift i) (neg (shift i))) = (fun _ => zero) :=
      funext fun _ => add_right_neg _
    rw [z, hk r hr]
    exact (show ∀ rr : List (Fin w), project rr (fun _ => zero) = zero from by
      intro rr
      induction rr with
      | nil => rfl
      | cons _ _ ih => exact (zero_add _).trans ih) r
  have s : add a (shift j) = b := by rw [show shift j = sub b a by simp [shift, vj, mul_one],
    add_sub_cancel_left]
  refine ⟨{ toFun := fun x => ⟨fun i => add (x.val i) (shift i), ?_, ?_⟩
            invFun := fun y => ⟨fun i => add (y.val i) (neg (shift i)), ?_, ?_⟩
            left_inv := ?_
            right_inv := ?_ }⟩
  · exact (congrArg (fun u => add u (shift j)) x.property.1).trans s
  · exact (row_view_translation rows shift hk x.val).trans x.property.2
  · change add (y.val j) (neg (shift j)) = a
    rw [y.property.1, ← s, add_assoc, add_right_neg, add_zero]
  · exact (row_view_translation rows _ hn y.val).trans y.property.2
  · intro x
    exact Subtype.ext (funext fun i => by simp only [add_assoc, add_right_neg, add_zero])
  · intro y
    exact Subtype.ext (funext fun i => by simp only [add_assoc, add_left_neg, add_zero])

theorem tooth_full_columns_revealed_projection (x y : Columns 2)
    (hv : project [1] x = project [1] y) : ¬ x 1 ≠ y 1 := by
  change add (x 1) zero = add (y 1) zero at hv
  rw [add_zero, add_zero] at hv
  exact fun hn => hn hv

/-- Rust's pre-enrollment guard consumes one optional reconstruction-weight vector per
singleton from the MSP solver, after validating the roster and full reconstruction. -/
def eligible {W : Type} (singletons : List (Option W)) : Bool :=
  !(singletons.any Option.isSome)

theorem singleton_reconstruction_rejected {W} {results : List (Option W)} {weights : W}
    (h : some weights ∈ results) : eligible results = false := by
  have : results.any Option.isSome = true := List.any_eq_true.mpr ⟨_, h, rfl⟩
  simp [eligible, this]

/-- Semantic reference solver for the singleton test. It enumerates coefficients over
the finite field. Rust uses elimination to search the same row span. -/
structure SpanProgram (w : Nat) where
  owners : List (Nat × List (Fin w))
  secret : Fin w

def ownerRows (P : SpanProgram w) (p : Nat) : List (List (Fin w)) :=
  P.owners.filterMap fun (owner,row) => if owner = p then some row else none

/-- The binary MSP incidence matrix multiplied on the left by the proposed weights. -/
def combo (rows : List (List (Fin w))) (weights : Columns rows.length) (j : Fin w) : Goldilocks :=
  (List.finRange rows.length).foldr
    (fun i s => if j ∈ rows[i] then add (weights i) s else s) zero

def reconstructs (P : SpanProgram w) (p : Nat) (v : Columns (ownerRows P p).length) : Bool :=
  (List.finRange w).all (fun j => decide (combo (ownerRows P p) v j =
    (if j = P.secret then one else zero)))

def solveSingleton (P : SpanProgram w) (p : Nat) :=
  let n := (ownerRows P p).length
  (List.finRange (tapeCount n)).find? fun c => reconstructs P p ((columnEnum n).toFun c)

theorem rejects_singleton_span (P : SpanProgram w) (roster : List Nat) (p : Nat)
    (hp : p ∈ roster) (v : Columns (ownerRows P p).length) (hv : reconstructs P p v = true) :
    eligible (roster.map (fun i => (solveSingleton P i).map Fin.val)) = false := by
  let e := columnEnum (ownerRows P p).length
  let c := e.invFun v
  have hc : reconstructs P p (e.toFun c) = true := by simpa only [c,e.right_inv] using hv
  cases he : solveSingleton P p with
  | none =>
    have hno := List.find?_eq_none.mp he c (List.mem_finRange _)
    exact False.elim (hno hc)
  | some d =>
    exact singleton_reconstruction_rejected (weights := d.val)
      (List.mem_map.mpr ⟨p,hp,by simp [he]⟩)

/-- Even a single allowed mask row excludes some aggregate column vectors from every
posterior fiber. A joint uniform sampler must reach those vectors. -/
theorem full_vector_uniform_given_row_impossible {n} (sample : Fin n → Columns 2)
    (seen : ∀ c, project [1] (sample c) = zero) :
    ¬ Spec.UniformOn (fun _ => True) sample := by
  intro h
  obtain ⟨c,hc⟩ := h.surjective (fun _ => one) trivial
  have eq := seen c
  rw [hc] at eq
  exact LawfulField.one_ne_zero ((add_zero _).symm.trans eq)

/-- A binary three-party access structure. The first two owners receive the masks;
the third receives the secret plus both masks. Any two mask owners see their own
coordinates exactly, even when the secret remains uniform. -/
def threeColumns (s a b : Goldilocks) : Columns 3 :=
  fun i => if i.val = 0 then s else if i.val = 1 then a else b

theorem three_party_reconstruct (x : Columns 3) :
    sub (sub (project [0,1,2] x) (project [2] x)) (project [1] x) = x 0 := by
  change sub (sub (add (x 0) (add (x 1) (add (x 2) zero))) (add (x 2) zero))
    (add (x 1) zero) = x 0
  simp only [add_zero, sub_eq_add_neg, add_assoc, add_right_neg]

theorem two_mask_owners_view (s a b : Goldilocks) :
    view [[1],[2]] (threeColumns s a b) = [a,b] := by
  change [add a zero, add b zero] = [a,b]
  simp only [add_zero]

theorem two_mask_owners_hide_secret (s t : Goldilocks) (obs : List Goldilocks) :
    Nonempty (SimpleEquiv (secretFiber (0 : Fin 3) [[1],[2]] obs s)
      (secretFiber (0 : Fin 3) [[1],[2]] obs t)) := by
  apply secret_view_fibers _ _ (threeColumns one zero zero) rfl _ obs s t
  intro row hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact add_zero _
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact add_zero _
    · cases hr

/-- Every two-owner view in the three-party program has the same number of tapes
for each possible secret. The missing row determines which mask absorbs a secret shift. -/
theorem any_two_owners_hide_secret (rows : List (List (Fin 3)))
    (pair : rows = [[1],[2]] ∨ rows = [[1],[0,1,2]] ∨ rows = [[2],[0,1,2]])
    (s t : Goldilocks) (obs : List Goldilocks) :
    Nonempty (SimpleEquiv (secretFiber (0 : Fin 3) rows obs s)
      (secretFiber (0 : Fin 3) rows obs t)) := by
  rcases pair with rfl | rfl | rfl
  · exact two_mask_owners_hide_secret s t obs
  · apply secret_view_fibers _ _ (threeColumns one zero (neg one)) rfl _ obs s t
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact add_zero _
    · rcases List.mem_cons.mp hr with rfl | hr
      · change add one (add zero (add (neg one) zero)) = zero
        simp only [zero_add, add_zero, add_right_neg]
      · cases hr
  · apply secret_view_fibers _ _ (threeColumns one (neg one) zero) rfl _ obs s t
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact add_zero _
    · rcases List.mem_cons.mp hr with rfl | hr
      · change add one (add (neg one) (add zero zero)) = zero
        simp only [add_zero, add_right_neg]
      · cases hr

def passes (error maskError challenge : Goldilocks) : Prop :=
  add maskError (mul error challenge) = zero

theorem projection_error_at_most_one {e m a b : Goldilocks} (he : e ≠ zero)
    (ha : passes e m a) (hb : passes e m b) : a = b := by
  have h : mul e a = mul e b := add_left_cancel (ha.trans hb.symm)
  have h' := congrArg (mul (LawfulField.inv e)) h
  simpa only [← mul_assoc, LawfulField.inv_mul_cancel he, one_mul] using h'

theorem affine_error_at_most_one {e m a b : Goldilocks} (nonzero : e ≠ zero ∨ m ≠ zero)
    (ha : passes e m a) (hb : passes e m b) : a = b := by
  by_cases he : e = zero
  · have hm := nonzero.resolve_left (fun h => h he)
    exact False.elim (hm (by simpa only [passes, he, zero_mul, add_zero] using ha))
  · exact projection_error_at_most_one he ha hb

theorem tooth_projection_check_tight :
    ∃ e m : Goldilocks, e ≠ zero ∧ passes e m zero ∧ ¬ passes e m one := by
  refine ⟨one, zero, LawfulField.one_ne_zero, ?_, ?_⟩
  · simp [passes, mul_zero, zero_add]
  · simp [passes, one_mul, zero_add, LawfulField.one_ne_zero]

theorem uniform_challenge_accept_count {e m : Goldilocks} (nonzero : e ≠ zero ∨ m ≠ zero) :
    qsum goldilocksPrime (fun x : Fin goldilocksPrime =>
      if decide (add m (mul e (fieldEnum.toFun x)) = zero) then 1 else 0) ≤ 1 := by
  apply qsum_indicator_le_one_of_unique goldilocksPrime
    (fun x => decide (add m (mul e (fieldEnum.toFun x)) = zero))
  intro a b ha hb
  have a0 : add m (mul e (fieldEnum.toFun a)) = zero := of_decide_eq_true ha
  have b0 : add m (mul e (fieldEnum.toFun b)) = zero := of_decide_eq_true hb
  have eq := affine_error_at_most_one nonzero a0 b0
  exact (fieldEnum.left_inv a).symm.trans ((congrArg fieldEnum.invFun eq).trans (fieldEnum.left_inv b))

#print axioms uniform_challenge_accept_count
#print axioms dealerless_sum_uniform
#print axioms rejects_singleton_span
#print axioms full_vector_uniform_given_row_impossible
#print axioms two_mask_owners_hide_secret
#print axioms any_two_owners_hide_secret
#print axioms three_party_reconstruct
#print axioms affine_error_at_most_one
#print axioms conditional_uniform
#print axioms secret_view_fibers
#print axioms projection_error_at_most_one
#print axioms singleton_reconstruction_rejected
#print axioms tooth_full_columns_revealed_projection
#tooth_pair projection_error_at_most_one vs tooth_projection_check_tight
end Qsag.DealerlessPersonalReleaseDkg
