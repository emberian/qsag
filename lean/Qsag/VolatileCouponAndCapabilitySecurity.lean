import Lean

/-!
Security boundaries for volatile coupons and indexed one-time capability bundles.
This file is independent of the Qsag import graph. Theorems are constructive.

These are algebraic/trace reductions, not concrete cSHAKE, PORS+FP, or WOTS+C
EUF-CMA bounds. Cryptographic failures appear as explicit collision/forgery events.
The RAM model excludes live-memory cloning, swap, dumps, and deterministic reminting.
A disk reboot loses availability of all outstanding coupons. It does not restore them.

QS-B requires the availability premise q + f ≤ n. The weaker q ≤ n in the lane
brief is false. MAYO rollback exposes an oil-subspace vector, not automatically a
basis or the entire key. Different messages need not produce independent vectors.
-/

namespace Qsag.VolatileCoupon

/- Standalone negative-witness declaration; no dependency on repository tactics. -/
macro "#tooth " n:ident " : " p:term " := " v:term : command =>
  `(theorem $n : $p := $v)

set_option autoImplicit false

 theorem qsB_minimum (n t f q : Nat) (ht : 1 ≤ t)
    (hf : f = t - 1) (hsafety : n + f < 2 * q)
    (havailable : q + f ≤ n) : 3 * t - 2 ≤ n := by omega

#tooth tooth_q_le_n_is_insufficient :
    3 + (2 - 1) < 2 * 3 ∧ 3 ≤ 3 ∧ ¬ (3 * 2 - 2 ≤ (3 : Nat)) := by decide

 theorem qsB_excluded_wallet_quorums (n t f q : Nat)
    (hpair : (t = 2 ∧ n = 3) ∨ (t = 3 ∧ n = 4) ∨
      (t = 3 ∧ n = 5) ∨ (t = 5 ∧ n = 7) ∨ (t = n ∧ 2 ≤ t))
    (hf : f = t - 1) (hs : n + f < 2 * q) (ha : q + f ≤ n) : False := by
  rcases hpair with h | h | h | h | h <;> omega

/- XOR vector space: addition is coordinatewise XOR. -/
def vxor {I : Type} (a b : I → Bool) : I → Bool := fun i => a i ^^ b i

def ColSpan {I J : Type} (O : (I → Bool) → (J → Bool)) (s : J → Bool) : Prop :=
  ∃ o, O o = s

 theorem mayo_rollback_difference {I J : Type} (O : (I → Bool) → (J → Bool))
    (hlinear : ∀ a b, O (vxor a b) = vxor (O a) (O b))
    (v : J → Bool) (o o' : I → Bool) :
    vxor (vxor v (O o)) (vxor v (O o')) = O (vxor o o') := by
  rw [hlinear]
  funext j
  simp only [vxor]
  cases v j <;> cases O o j <;> cases O o' j <;> rfl

 theorem mayo_rollback_subspace_leak {I J : Type} (O : (I → Bool) → (J → Bool))
    (hlinear : ∀ a b, O (vxor a b) = vxor (O a) (O b))
    (v : J → Bool) (o o' : I → Bool) :
    ColSpan O (vxor (vxor v (O o)) (vxor v (O o'))) :=
  ⟨vxor o o', (mayo_rollback_difference O hlinear v o o').symm⟩

#tooth tooth_reused_vinegar_reveals_nonzero_oil :
    ((true ^^ true) ^^ (true ^^ false)) = true := by decide

/- One leaked column does not determine a two-column matrix. -/
#tooth tooth_one_difference_not_full_key_recovery :
    let O₀ := fun p : Bool × Bool => p.1
    let O₁ := fun p : Bool × Bool => p.1 ^^ p.2
    O₀ (true, false) = O₁ (true, false) ∧ O₀ (false, true) ≠ O₁ (false, true) := by
  decide

/- A hash-chain opening at d exposes precisely the forward direction, absent inversion. -/
def Reachable (d target : List Nat) : Prop :=
  d.length = target.length ∧ ∀ j : Nat, d[j]?.getD 0 ≤ target[j]?.getD 0

 theorem min_exposure (a b target : Nat) (ha : a ≤ target ∨ b ≤ target) :
    min a b ≤ target := by omega

/- Equal-sum, base-four codewords: collusion opens a third codeword neither branch opens.
The witness describes codeword exposure; finding a message for it still costs grinding. -/
#tooth tooth_compact_fanout_strips_codeword_restriction :
    let a := [0, 2, 1]; let b := [2, 0, 1]; let c := [1, 1, 1]
    a.foldl (· + ·) 0 = 3 ∧ b.foldl (· + ·) 0 = 3 ∧
    c.foldl (· + ·) 0 = 3 ∧ ¬ Reachable a c ∧ ¬ Reachable b c ∧
    Reachable [0, 0, 1] c := by
  dsimp
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_⟩
  · intro h; have h1 := h.2 1; simp at h1
  · intro h; have h0 := h.2 0; simp at h0
  · intro j
    cases j with
    | zero => decide
    | succ j => cases j with
      | zero => decide
      | succ j => cases j <;> simp

/- Domain-separated indexed leaf encoding and ordered internal node hashing. -/
inductive MerkleInput (D : Type) where
  | leaf : Nat → D → MerkleInput D
  | node : D → D → MerkleInput D
  deriving DecidableEq

def Collision {D : Type} (H : MerkleInput D → D) : Prop :=
  ∃ x y, x ≠ y ∧ H x = H y

/- Authentication paths include orientation; the index is additionally bound at the leaf. -/
def root {D : Type} (H : MerkleInput D → D) : D → List (Bool × D) → D
  | x, [] => x
  | x, (left, sibling) :: rest =>
    root H (if left then H (.node x sibling) else H (.node sibling x)) rest

 theorem root_eq_extract {D : Type} [DecidableEq D] (H : MerkleInput D → D)
    (x y : D) (p q : List (Bool × D)) (hlen : p.length = q.length)
    (horient : p.map Prod.fst = q.map Prod.fst)
    (hroot : root H x p = root H y q) : x = y ∨ Collision H := by
  induction p generalizing x y q with
  | nil =>
    cases q with
    | nil => exact Or.inl hroot
    | cons _ _ => exact False.elim (Nat.noConfusion hlen)
  | cons a p ih =>
    cases q with
    | nil => exact False.elim (Nat.noConfusion hlen)
    | cons b q =>
      have hlen' : p.length = q.length := by simpa using hlen
      let u : MerkleInput D := if a.1 then .node x a.2 else .node a.2 x
      let v : MerkleInput D := if b.1 then .node y b.2 else .node b.2 y
      have hr : root H (H u) p = root H (H v) q := by
        cases ha : a.1 <;> cases hb : b.1 <;>
          simpa only [root, u, v, ha, hb, Bool.false_eq_true, ↓reduceIte] using hroot
      have hab : a.1 = b.1 := (List.cons.inj horient).1
      have htail : p.map Prod.fst = q.map Prod.fst := (List.cons.inj horient).2
      rcases ih (H u) (H v) q hlen' htail hr with heq | hc
      · cases Decidable.em (u = v) with
        | inl huv =>
          apply Or.inl
          cases ha : a.1 with
          | false =>
            have hb : b.1 = false := hab.symm.trans ha
            have hn : MerkleInput.node a.2 x = .node b.2 y := by
              simpa only [u, v, ha, hb, Bool.false_eq_true, ↓reduceIte] using huv
            exact (MerkleInput.node.inj hn).2
          | true =>
            have hb : b.1 = true := hab.symm.trans ha
            have hn : MerkleInput.node x a.2 = .node y b.2 := by
              simpa only [u, v, ha, hb, ↓reduceIte] using huv
            exact (MerkleInput.node.inj hn).1
        | inr huv => exact Or.inr ⟨u, v, huv, heq⟩
      · exact Or.inr hc

/- An accepted opening of a different key at a fixed index extracts a hash collision.
The depth is arbitrary. A bundle of B leaves uses any d with B ≤ 2^d; choosing the
least such d gives ceil(log₂ B). Padded indices ≥ B must be rejected by the verifier. -/
 theorem indexed_bundle_key_binding {D : Type} [DecidableEq D]
    (H : MerkleInput D → D) (index : Nat) (pk pk' : D)
    (p q : List (Bool × D)) (hlen : p.length = q.length)
    (horient : p.map Prod.fst = q.map Prod.fst)
    (hr : root H (H (.leaf index pk)) p = root H (H (.leaf index pk')) q) :
    pk = pk' ∨ Collision H := by
  rcases root_eq_extract H _ _ p q hlen horient hr with heq | hc
  · cases Decidable.em (pk = pk') with
    | inl hk => exact Or.inl hk
    | inr hk => exact Or.inr ⟨.leaf index pk, .leaf index pk', by intro h; cases h; exact hk rfl, heq⟩
  · exact Or.inr hc

/- Bundle reduction: accepting a new message under a certified index yields either
an observed Merkle collision or an accepted new-message signature for its real OTS key.
An OTS security theorem/bound can then be applied to the second event. -/
 theorem indexed_bundle_unforgeability_reduction {D M Sig : Type} [DecidableEq D]
    (H : MerkleInput D → D) (verify : D → M → Sig → Prop)
    (index : Nat) (pk pk' : D) (p q : List (Bool × D))
    (hlen : p.length = q.length) (ho : p.map Prod.fst = q.map Prod.fst)
    (hr : root H (H (.leaf index pk)) p = root H (H (.leaf index pk')) q)
    (m old : M) (sig : Sig) (hfresh : m ≠ old) (hv : verify pk' m sig) :
    Collision H ∨ (m ≠ old ∧ verify pk m sig) := by
  rcases indexed_bundle_key_binding H index pk pk' p q hlen ho hr with hk | hc
  · exact Or.inr ⟨hfresh, hk ▸ hv⟩
  · exact Or.inl hc

/- Without an index in the leaf hash, a leaf can be relabeled across a bundle. -/
#tooth tooth_unindexed_leaf_relabel :
    let H := fun (_index : Nat) (pk : Nat) => pk + 1
    H 0 7 = H 1 7 ∧ (0 : Nat) ≠ 1 := by decide

structure Request where
  publicKey : List UInt8
  message : List UInt8
  members : List Nat
  couponIds : List (List UInt8)
  counter : Nat
  expiry : Nat
  deriving DecidableEq

/- Authentication binds the entire canonical request, including counter and expiry.
This is a collision-event reduction; it does not assume a finite MAC is injective. -/
 theorem authenticated_request_binding {Tag : Type} (mac : Request → Tag)
    (committed received : Request) (ha : mac received = mac committed) :
    received = committed ∨ (received ≠ committed ∧ mac received = mac committed) := by
  cases Decidable.em (received = committed) with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr ⟨h, ha⟩

/- Dropping the child-root from authentication admits two conflicting cache entries. -/
#tooth tooth_unauthenticated_waistband :
    let omittedRootMac := fun (pk : Nat) (_childRoot : Nat) => pk
    omittedRootMac 7 0 = omittedRootMac 7 1 ∧ (0 : Nat) ≠ 1 := by decide

/- Slot transition: authentication, expiry and codeword checks precede consumption.
A successful operation removes the entire slot before returning a selected opening. -/
def consume {M : Type} (ready authorized : Bool) (request : M) : Bool × Option M :=
  if ready && authorized then (false, some request) else (ready, none)

 theorem invalid_request_preserves_coupon {M : Type} (ready : Bool) (m : M) :
    consume ready false m = (ready, none) := by cases ready <;> rfl

 theorem burn_before_release {M : Type} (ready auth : Bool) (m out : M)
    (h : (consume ready auth m).2 = some out) :
    (consume ready auth m).1 = false ∧ out = m := by
  cases ready <;> cases auth <;> simp_all [consume]

 theorem spent_never_releases {M : Type} (auth : Bool) (m : M) :
    consume false auth m = (false, none) := rfl

 theorem one_slot_cannot_release_twice {M : Type} (ready a b : Bool)
    (m m' out out' : M) (h : (consume ready a m).2 = some out) :
    (consume (consume ready a m).1 b m').2 ≠ some out' := by
  rw [(burn_before_release ready a m out h).1]
  simp [consume]

/- All-of-S reconstruction: each accepted opening includes every minting member.
`honest` identifies a required member. Local one-time release therefore rules out
split-brain completion without any BFT quorum geometry or network synchrony. -/
 theorem fixed_subset_split_brain_impossible {Party M : Type}
    (members : List Party) (honest : Party) (hh : honest ∈ members)
    (released : Party → M → Prop) (m m' : M) (hne : m ≠ m')
    (once : ∀ x y, released honest x → released honest y → x = y)
    (complete : ∀ p, p ∈ members → released p m)
    (complete' : ∀ p, p ∈ members → released p m') : False :=
  hne (once m m' (complete honest hh) (complete' honest hh))

/- Counting corrupt entries avoids any classical finite-set choice. With distinct
members this is exactly the corruption count of the minting subset. -/
def corruptCount {P : Type} (bad : P → Bool) : List P → Nat
  | [] => 0
  | p :: ps => (if bad p then 1 else 0) + corruptCount bad ps

 theorem honest_member_of_corruption_bound {P : Type} (bad : P → Bool)
    (members : List P) (h : corruptCount bad members < members.length) :
    ∃ p, p ∈ members ∧ bad p = false := by
  induction members with
  | nil => simp [corruptCount] at h
  | cons p ps ih =>
    cases hp : bad p with
    | false => exact ⟨p, by simp, hp⟩
    | true =>
      have htail : corruptCount bad ps < ps.length := by
        simp [corruptCount, hp] at h
        omega
      obtain ⟨x, hx, hb⟩ := ih htail
      exact ⟨x, by simp [hx], hb⟩

 theorem arbitrary_threshold_has_required_honest_member {P : Type}
    (n t : Nat) (members : List P) (bad : P → Bool)
    (_ht : 2 ≤ t) (_hn : t ≤ n) (hs : members.length = t)
    (hf : corruptCount bad members < t) :
    ∃ p, p ∈ members ∧ bad p = false :=
  honest_member_of_corruption_bound bad members (by omega)

/- A threshold-shared coupon across the full committee is unsafe: corrupt member 0
can join honest 1 and honest 2 in separate 2-of-3 completions. -/
#tooth tooth_threshold_coupon_partition :
    let a := [0, 1]; let b := [0, 2]
    a.length = 2 ∧ b.length = 2 ∧
    (∀ p : Nat, p ∈ a → p ∈ b → p = 0) := by
  simp

#tooth tooth_live_ram_clone_releases_twice :
    (consume true true 0).2 = some 0 ∧ (consume true true 1).2 = some 1 := by decide

#tooth tooth_no_request_authentication_depletes_pool :
    (consume true true 0).1 = false ∧ (consume true false 0).1 = true := by decide

/- Only long-term shares are serialized. OS entropy and volatile slots are absent
from this type, so restoring a disk image cannot restore a coupon. This does not
cover a VM snapshot including RAM or replay of the OS randomness source. -/
structure Disk (Share : Type) where
  longTermShares : List Share

structure Runtime (Share : Type) where
  disk : Disk Share
  coupons : List Nat

def reboot {Share : Type} (d : Disk Share) : Runtime Share := ⟨d, []⟩

 theorem disk_rewind_has_no_coupons {Share : Type} (snapshot : Disk Share) :
    (reboot snapshot).coupons = [] := rfl

 theorem online_transition_has_zero_disk_writes {Share : Type}
    (s : Runtime Share) (remaining : List Nat) :
    ({ s with coupons := remaining } : Runtime Share).disk = s.disk := rfl

/- A chosen public coin can be searched after observing it; a fixed request with a
hidden independent uniform bit has one success out of two, regardless of its choice.
This finite experiment isolates adaptivity; it is not a quantitative PORS security bound. -/
def coinWins (request coin : Bool) : Bool := request ^^ coin

 theorem secret_coin_fixed_request_balanced (request : Bool) :
    ([false, true].filter (coinWins request)).length = 1 := by cases request <;> rfl

#tooth tooth_public_coin_adaptive_grinding_bias :
    ([false, true].filter (fun coin => coinWins (!coin) coin)).length = 2 := by decide

end Qsag.VolatileCoupon

#print axioms Qsag.VolatileCoupon.qsB_minimum
#print axioms Qsag.VolatileCoupon.mayo_rollback_subspace_leak
#print axioms Qsag.VolatileCoupon.indexed_bundle_unforgeability_reduction
#print axioms Qsag.VolatileCoupon.one_slot_cannot_release_twice
#print axioms Qsag.VolatileCoupon.arbitrary_threshold_has_required_honest_member
#print axioms Qsag.VolatileCoupon.fixed_subset_split_brain_impossible
#print axioms Qsag.VolatileCoupon.secret_coin_fixed_request_balanced

#print axioms Qsag.VolatileCoupon.root_eq_extract
#print axioms Qsag.VolatileCoupon.indexed_bundle_key_binding
/- Fail the build if any theorem or definition in this standalone namespace gains
an unapproved dependency. Read the kernel environment, including async proofs. -/
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    if (`Qsag.VolatileCoupon).isPrefixOf n then
      for ax in (← Lean.collectAxioms n) do
        unless ax == `propext || ax == `Quot.sound do
          throwError "unapproved dependency {ax} in {n}"
      count := count + 1
  Lean.logInfo m!"VolatileCoupon axiom audit: {count} declarations checked"
