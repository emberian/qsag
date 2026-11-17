module
public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
public import Qsag.Custody.MacaroonAttenuation
import Qsag.Tactic.AssuranceKit

/-!
Security boundaries for volatile coupons and indexed one-time capability bundles.
QS-B enrollment facts are stated over `QsBQuorumConfig` from
`Qsag.Custody.JortsBeltLatchAndQuorumSwitching`. The last section gates a coupon slot by the
macaroon verifier of `Qsag.Custody.MacaroonAttenuation`. The rest is self-contained.

The statements about XOR shares, hash chains, Merkle bundles, request tags and slots are trace
reductions: a cryptographic failure appears in the conclusion as an explicit collision or
forgery event, and no statement here is a probability bound for cSHAKE or WOTS+C. The `PORS+FP`
opening, its binding to the root and its few-time subset-cover bound are proved in the module
`Qsag.Protocol.Signing.PorsFpSecurity`; macaroon attenuation, chain editing and discharge binding
are proved in the module `Qsag.Custody.MacaroonAttenuation`.

The RAM model excludes live-memory cloning, swap, dumps, and deterministic reminting.
A disk reboot loses availability of all outstanding coupons. It does not restore them.

QS-B requires the availability premise q + f ≤ n. The weaker q ≤ n is not enough. MAYO rollback
exposes an oil-subspace vector, not automatically a basis or the entire key. Different messages
need not produce independent vectors.
-/

public section
namespace Qsag.VolatileCoupon

set_option autoImplicit false

/-- A valid QS-B enrollment (`QsBQuorumConfig.valid`) at the largest tolerated corruption
`f = t - 1` needs `n ≥ 3t - 2` parties. -/
theorem qsB_minimum (c : QsBQuorumConfig) (hvalid : c.valid = true) (hf : c.f = c.t - 1) :
    3 * c.t - 2 ≤ c.n := by
  obtain ⟨_, _, hft, _, _, _, hn, _⟩ := (QsBQuorumConfig.valid_iff c).mp hvalid
  omega

theorem qsB_excluded_wallet_quorums (c : QsBQuorumConfig)
    (hpair : (c.t = 2 ∧ c.n = 3) ∨ (c.t = 3 ∧ c.n = 4) ∨
      (c.t = 3 ∧ c.n = 5) ∨ (c.t = 5 ∧ c.n = 7) ∨ (c.t = c.n ∧ 2 ≤ c.t))
    (hf : c.f = c.t - 1) : ¬ (c.valid = true) := by
  intro hvalid
  have hmin := qsB_minimum c hvalid hf
  rcases hpair with h | h | h | h | h <;> omega

/- XOR vector space: addition is coordinatewise XOR. -/
def vxor {I : Type} (a b : I → Bool) : I → Bool := fun i => a i ^^ b i

/- The unknown all-of-S additive share is a one-time pad. Translation by the
known corrupt shares is its own inverse, so it permutes uniform bit vectors.
Independent masking of every staged chain state is a required minting invariant. -/
theorem unseen_additive_share_translation_involutive {I : Type} (known missing : I → Bool) :
    vxor known (vxor known missing) = missing := by
  funext i
  simp only [vxor]
  cases known i <;> cases missing i <;> rfl

theorem unseen_additive_share_translation_injective {I : Type}
    (known a b : I → Bool) (h : vxor known a = vxor known b) : a = b := by
  have hh := congrArg (vxor known) h
  rw [unseen_additive_share_translation_involutive,
    unseen_additive_share_translation_involutive] at hh
  exact hh

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

/- A hash-chain opening at d exposes precisely the forward direction, absent inversion. -/
def Reachable (d target : List Nat) : Prop :=
  d.length = target.length ∧ ∀ j : Nat, d[j]?.getD 0 ≤ target[j]?.getD 0

theorem min_exposure (a b target : Nat) (ha : a ≤ target ∨ b ≤ target) :
    min a b ≤ target := by omega

theorem min_exposure_iff (a b target : Nat) :
    min a b ≤ target ↔ a ≤ target ∨ b ≤ target := by
  constructor
  · intro h
    cases Decidable.em (a ≤ target) with
    | inl ha => exact Or.inl ha
    | inr ha => exact Or.inr (by omega)
  · exact min_exposure a b target

/- The equal-sum restriction is load-bearing for a one-time chain key. Moving
only forward cannot produce a different valid codeword with the same sum.
A different message with the same codeword remains a separate digest-collision
event; this theorem does not assume that hashing messages is injective. -/
def digitSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + digitSum xs

inductive ForwardSteps : List Nat → List Nat → Prop where
  | nil : ForwardSteps [] []
  | cons {a b : Nat} {as bs : List Nat} :
      a ≤ b → ForwardSteps as bs → ForwardSteps (a :: as) (b :: bs)

theorem forward_steps_sum_monotone (a b : List Nat)
    (h : ForwardSteps a b) : digitSum a ≤ digitSum b := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons hab _ ih => simp only [digitSum]; omega

theorem equal_sum_forward_codeword_unique (a b : List Nat)
    (h : ForwardSteps a b) (hs : digitSum a = digitSum b) : a = b := by
  induction h with
  | nil => rfl
  | @cons a b as bs hab htail ih =>
    have hm := forward_steps_sum_monotone as bs htail
    simp only [digitSum] at hs
    have heq : a = b := by omega
    have hsum : digitSum as = digitSum bs := by omega
    rw [heq, ih hsum]

theorem distinct_equal_sum_codeword_not_forward_reachable (a b : List Nat)
    (hs : digitSum a = digitSum b) (hne : a ≠ b) :
    ¬ ForwardSteps a b := by
  intro h
  exact hne (equal_sum_forward_codeword_unique a b h hs)

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

structure Request where
  publicKey : List UInt8
  message : List UInt8
  members : List Nat
  couponIds : List (List UInt8)
  counter : Nat
  expiry : Nat
  deriving DecidableEq

/-- Two different inputs with one output. -/
def Collides {A D : Type} (h : A → D) : Prop := ∃ x y, x ≠ y ∧ h x = h y

/-- Public authentication evidence for the complete request commitment under an initiator
    MAC. The evidence carries the exact tag equality used by collision extraction. -/
structure RequestAuthenticated {D Tag : Type} (commit : Request → D) (mac : D → Tag)
    (committed received : Request) : Prop where
  tags_equal : mac (commit received) = mac (commit committed)

/-- Request authentication as in `SignRequest::authorize` and `CouponSlots::open` (Rust): the tag
is the keyed function `mac` of the commitment `commit` to the canonical request (coupon identity,
hence public key, member set and expiry; message; counter). A request accepted with the tag of the
committed request is that request, or the two requests are a collision of `commit`, or their two
different commitments are a collision of `mac` under the initiator key. Neither function is
assumed injective. -/
theorem authenticated_request_binding {D Tag : Type} [DecidableEq D]
    (commit : Request → D) (mac : D → Tag) (committed received : Request)
    (ha : RequestAuthenticated commit mac committed received) :
    received = committed ∨ Collides commit ∨ Collides mac := by
  cases Decidable.em (received = committed) with
  | inl h => exact .inl h
  | inr h =>
    cases Decidable.em (commit received = commit committed) with
    | inl hc => exact .inr (.inl ⟨received, committed, h, hc⟩)
    | inr hc => exact .inr (.inr ⟨commit received, commit committed, hc, ha.tags_equal⟩)

/- Slot transition: authentication, expiry and codeword checks precede consumption.
A successful operation removes the entire slot before returning a selected opening.
`authorized` is the conjunction of the checks made before the slot is touched. In
`CouponSlots::open` (Rust) these are the initiator tag on the request commitment, the expiry,
the Waistband tag and the coupon identity. -/
def consume {M : Type} (ready authorized : Bool) (request : M) : Bool × Option M :=
  if ready && authorized then (false, some request) else (ready, none)

theorem invalid_request_preserves_coupon {M : Type} (ready : Bool) (m : M) :
    consume ready false m = (ready, none) := by cases ready <;> rfl

theorem burn_before_release {M : Type} (ready auth : Bool) (m out : M)
    (h : (consume ready auth m).2 = some out) :
    (consume ready auth m).1 = false ∧ out = m := by
  cases ready <;> cases auth <;> simp_all [consume]

theorem spent_never_releases {M : Type} (auth : Bool) (m : M) :
    consume false auth m = (false, none) := by rfl

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
    (t : Nat) (members : List P) (bad : P → Bool)
    (hs : members.length = t)
    (hf : corruptCount bad members < t) :
    ∃ p, p ∈ members ∧ bad p = false :=
  honest_member_of_corruption_bound bad members (by omega)

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
    (reboot snapshot).coupons = [] := by rfl

theorem online_transition_has_zero_disk_writes {Share : Type}
    (s : Runtime Share) (remaining : List Nat) :
    ({ s with coupons := remaining } : Runtime Share).disk = s.disk := rfl

/- A chosen public coin can be searched after observing it; a fixed request with a
hidden independent uniform bit has one success out of two, regardless of its choice.
This finite experiment isolates adaptivity. The quantitative few-time bound for the deployed
`PORS+FP` parameters is `Qsag.PorsFpSecurity.sha3_128f_forgery_bound`. -/
def coinWins (request coin : Bool) : Bool := request ^^ coin

theorem secret_coin_fixed_request_balanced (request : Bool) :
    ([false, true].filter (coinWins request)).length = 1 := by cases request <;> rfl

/-! ### A slot gated by a macaroon

`CouponSlots::open` authorizes with the initiator tag; the crates do not put a macaroon in front
of a coupon. This section is the composition for a service that does: the slot's authorization
bit is the verdict of `MacaroonAttenuation.verifierVerify` on the presented token, request and
discharges. A release then carries the macaroon guarantees: it is an authorized request, an
attenuated token releases only what its parent releases, a first-party caveat that fails blocks
the release, and one discharge serves two tokens only when their binding commitments agree. -/

section CapabilityGate
open MacaroonAttenuation
variable {B T M : Type}

def consumeUnderCapability [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (dep : Deployment B) (tok : Token B T) (r : MacaroonAttenuation.Request B)
    (ds : List (Discharge B T)) (ready : Bool) (m : M) : Bool × Option M :=
  consume ready (decide (verifierVerify S dep tok r ds = .ok ())) m

/-- A release happened under an accepted presentation, burned the slot and returned the request. -/
theorem capability_release_verified [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (dep : Deployment B) (tok : Token B T) (r : MacaroonAttenuation.Request B)
    (ds : List (Discharge B T)) (ready : Bool) (m out : M)
    (h : (consumeUnderCapability S dep tok r ds ready m).2 = some out) :
    (consumeUnderCapability S dep tok r ds ready m).1 = false ∧ out = m ∧
      verifierVerify S dep tok r ds = .ok () := by
  unfold consumeUnderCapability at h ⊢
  refine ⟨(burn_before_release ready _ m out h).1, (burn_before_release ready _ m out h).2, ?_⟩
  cases hv : decide (verifierVerify S dep tok r ds = .ok ()) with
  | true => exact of_decide_eq_true hv
  | false =>
    rw [hv, invalid_request_preserves_coupon] at h
    cases h

/-- The slot releases only for a request the deployment grants the token, when every presented
discharge is under the key the deployment's registry holds for it. -/
theorem capability_release_authorized [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (dep : Deployment B) (tok : Token B T) (r : MacaroonAttenuation.Request B)
    (ds : List (Discharge B T)) (ready : Bool) (m out : M)
    (hreg : ∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier)
    (h : (consumeUnderCapability S dep tok r ds ready m).2 = some out) :
    (consumeUnderCapability S dep tok r ds ready m).1 = false ∧ out = m ∧
      Authorized S tok dep r := by
  obtain ⟨hb, ho, hv⟩ := capability_release_verified S dep tok r ds ready m out h
  exact ⟨hb, ho, ds, hreg, hv⟩

/-- A ready slot releases for every authorized request. -/
theorem capability_authorized_releases [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (dep : Deployment B) (tok : Token B T) (r : MacaroonAttenuation.Request B) (m : M)
    (h : Authorized S tok dep r) :
    ∃ ds : List (Discharge B T), (∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier) ∧
      consumeUnderCapability S dep tok r ds true m = (false, some m) := by
  obtain ⟨ds, hreg, hv⟩ := h
  refine ⟨ds, hreg, ?_⟩
  unfold consumeUnderCapability consume
  rw [decide_eq_true hv]
  rfl

/-- Attenuation cannot widen what a slot releases: a release under an attenuated token is also
obtainable, for the same request, under the genuine token it was attenuated from. -/
theorem attenuated_capability_release_narrows [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (dep : Deployment B) (tok tok' : Token B T) (c : Caveat B)
    (r : MacaroonAttenuation.Request B) (ds : List (Discharge B T)) (ready : Bool) (m out : M)
    (hatt : attenuate S tok c = .ok tok') (hgen : Genuine S dep tok)
    (hreg : ∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier)
    (h : (consumeUnderCapability S dep tok' r ds ready m).2 = some out) :
    ∃ ds' : List (Discharge B T), (∀ d ∈ ds', d.rootKey = dep.registry d.token.identifier) ∧
      consumeUnderCapability S dep tok r ds' true m = (false, some m) :=
  capability_authorized_releases S dep tok r m
    (attenuation_narrows S tok tok' c dep r hatt hgen
      (capability_release_authorized S dep tok' r ds ready m out hreg h).2.2)

/-- A first-party caveat that the request fails blocks the release, whatever is presented. -/
theorem failed_caveat_blocks_capability_release [DecidableEq B] [DecidableEq T]
    (S : MacSuite B T) (dep : Deployment B) (tok tok' : Token B T) (c : Caveat B)
    (r : MacaroonAttenuation.Request B) (ds : List (Discharge B T)) (ready : Bool) (m : M)
    (hatt : attenuate S tok c = .ok tok') (hgen : Genuine S dep tok)
    (hfp : c.isThirdParty = false) (hfail : c.holds r = false)
    (hreg : ∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier) :
    (consumeUnderCapability S dep tok' r ds ready m).2 = none := by
  cases h : (consumeUnderCapability S dep tok' r ds ready m).2 with
  | none => rfl
  | some out =>
    have hauth := (capability_release_authorized S dep tok' r ds ready m out hreg h).2.2
    have hholds := ((attenuation_firstParty_exact S tok tok' c dep r hatt hgen hfp).mp hauth).2
    rw [hfail] at hholds
    cases hholds

/-- One discharge presented in two releases, under any two tokens and deployments, forces the
two tokens to have the same binding commitment. -/
theorem capability_release_discharge_not_transplantable [DecidableEq B] [DecidableEq T]
    (S : MacSuite B T) (dep₁ dep₂ : Deployment B) (tok₁ tok₂ : Token B T)
    (r₁ r₂ : MacaroonAttenuation.Request B) (ds₁ ds₂ : List (Discharge B T))
    (ready₁ ready₂ : Bool) (m₁ m₂ out₁ out₂ : M) (d : Discharge B T)
    (h₁ : (consumeUnderCapability S dep₁ tok₁ r₁ ds₁ ready₁ m₁).2 = some out₁)
    (h₂ : (consumeUnderCapability S dep₂ tok₂ r₂ ds₂ ready₂ m₂).2 = some out₂)
    (hd₁ : d ∈ ds₁) (hd₂ : d ∈ ds₂) : S.bind tok₁.tag = S.bind tok₂.tag := by
  have hv₁ := (capability_release_verified S dep₁ tok₁ r₁ ds₁ ready₁ m₁ out₁ h₁).2.2
  have hv₂ := (capability_release_verified S dep₂ tok₂ r₂ ds₂ ready₂ m₂ out₂ h₂).2.2
  have hg₁ := ((verifierVerify_ok_iff S dep₁ tok₁ r₁ ds₁).mp hv₁).1
  have hg₂ := ((verifierVerify_ok_iff S dep₂ tok₂ r₂ ds₂).mp hv₂).1
  exact discharge_not_transplantable S dep₁.key dep₂.key tok₁ tok₂ r₁ r₂ ds₁ ds₂ d
    ((verifierVerify_eq_verify_ok S dep₁ tok₁ r₁ ds₁ (Genuine.bindings hg₁).1 (Genuine.bindings hg₁).2).mp hv₁)
    ((verifierVerify_eq_verify_ok S dep₂ tok₂ r₂ ds₂ (Genuine.bindings hg₂).1 (Genuine.bindings hg₂).2).mp hv₂) hd₁ hd₂

end CapabilityGate

-- Equations for the concrete runs of `Tests/CapabilityTeeth`; no body is exposed.
#export_eqns Reachable Collides consume coinWins consumeUnderCapability

end Qsag.VolatileCoupon
end

#verify_constructive Qsag.VolatileCoupon.qsB_minimum
#verify_constructive Qsag.VolatileCoupon.mayo_rollback_subspace_leak
#verify_constructive Qsag.VolatileCoupon.root_eq_extract
#verify_constructive Qsag.VolatileCoupon.indexed_bundle_key_binding
#verify_constructive Qsag.VolatileCoupon.indexed_bundle_unforgeability_reduction
#verify_constructive Qsag.VolatileCoupon.authenticated_request_binding
#verify_constructive Qsag.VolatileCoupon.one_slot_cannot_release_twice
#verify_constructive Qsag.VolatileCoupon.arbitrary_threshold_has_required_honest_member
#verify_constructive Qsag.VolatileCoupon.fixed_subset_split_brain_impossible
#verify_constructive Qsag.VolatileCoupon.secret_coin_fixed_request_balanced
#verify_constructive Qsag.VolatileCoupon.capability_release_authorized
#verify_constructive Qsag.VolatileCoupon.attenuated_capability_release_narrows
#verify_constructive Qsag.VolatileCoupon.failed_caveat_blocks_capability_release
#verify_constructive Qsag.VolatileCoupon.capability_release_discharge_not_transplantable
