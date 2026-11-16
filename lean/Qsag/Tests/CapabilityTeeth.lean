module
/-
# Qsag.Tests.CapabilityTeeth: audits for the macaroon and `PORS+FP` leaves

Each audited statement is restated here and proved by the library theorem of the same name,
so the audit commands read the statement and a body of this module. An inhabitedness witness
gives concrete values for all premises of its theorem at once. A tooth is a concrete run on
which a verifier with one check removed accepts and the real verifier refuses, or a concrete
instance on which the conclusion fails once a hypothesis is dropped.

The concrete facts of the macaroon and `PORS+FP` leaves are proved in the two library modules,
where the definitions unfold. The last part holds the negative witnesses of
`Qsag.Custody.VolatileCoupon` and the audits of its macaroon-gated slot.
-/

public import Qsag.Custody.MacaroonAttenuation
public import Qsag.Protocol.Signing.PorsFpSecurity
public import Qsag.Custody.VolatileCoupon
import all Qsag.Custody.MacaroonAttenuation
import all Qsag.Custody.VolatileCoupon
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.CapabilityTeeth
set_option autoImplicit false

section Macaroon
open MacaroonAttenuation
variable {B T : Type}

theorem attenuation_narrows_audited [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (tok tok' : Token B T) (c : Caveat B) (dep : Deployment B) (r : Request B)
    (hatt : attenuate S tok c = .ok tok') (hgen : Genuine S dep tok)
    (h : Authorized S tok' dep r) : Authorized S tok dep r :=
  attenuation_narrows S tok tok' c dep r hatt hgen h

theorem inhabited_attenuation :
    ∃ (S : MacSuite Nat DemoTag) (tok tok' : Token Nat DemoTag) (c : Caveat Nat)
      (dep : Deployment Nat) (r : Request Nat),
      attenuate S tok c = .ok tok' ∧ Genuine S dep tok ∧ Authorized S tok' dep r :=
  ⟨demoSuite, demoScoped, demoParent, .thirdParty 5, demoDeployment, demoRequest,
    demo_attenuate_thirdParty, demo_scoped_genuine, demo_parent_authorized⟩

/-- Narrowing can be strict: an expiry caveat removes a request the token had. -/
theorem tooth_attenuation_strictly_narrows :
    ∃ tok tok' : Token Nat DemoTag,
      attenuate demoSuite tok (.expiresAt 5#64) = .ok tok' ∧
        Authorized demoSuite tok demoDeployment demoRequest ∧
        ¬ Authorized demoSuite tok' demoDeployment demoRequest :=
  ⟨demoScoped, demoExpired, demo_attenuate_expiry, demo_scoped_authorized,
    demo_expired_not_authorized⟩

#verify_inhabited attenuation_narrows_audited inhabited_attenuation
#tooth_pair attenuation_narrows_audited vs tooth_attenuation_strictly_narrows

theorem edit_yields_cascade_forgery_audited [DecidableEq B] (S : MacSuite B T) (ρ : T)
    (cs cs' : List (Caveat B)) (t t' : T) (hne : ¬ cs <+: cs') (h : chainFrom S ρ cs = t)
    (h' : chainFrom S ρ cs' = t') :
    (editWitness cs cs' t').Wins S (chainFrom S ρ (cs.take (commonLen cs cs'))) t :=
  edit_yields_cascade_forgery S ρ cs cs' t t' hne h h'

theorem inhabited_edit :
    ∃ (S : MacSuite Nat DemoTag) (ρ : DemoTag) (cs cs' : List (Caveat Nat)) (t t' : DemoTag),
      ¬ cs <+: cs' ∧ chainFrom S ρ cs = t ∧ chainFrom S ρ cs' = t' :=
  ⟨demoSuite, demoRootTag, demoExpiredCaveats, demoScopedCaveats, demoExpired.tag,
    demoScoped.tag, demo_edit_not_prefix, demo_chain_expired, demo_chain_scoped⟩

theorem accepted_edit_audited [DecidableEq B] [DecidableEq T] (S : MacSuite B T) (key : B)
    (q m : Token B T) (r : Request B) (ds : List (Discharge B T)) (hq : Authentic S key q)
    (hacc : verify S key m r ds = .ok ()) (hd : m.discharge = q.discharge)
    (hi : m.identifier = q.identifier) (ha : m.audience = q.audience)
    (hnew : ¬ IsAttenuationOf m q) :
    (editWitness q.caveats m.caveats m.tag).Wins S
      (chainFrom S (rootTag S key q) (q.caveats.take (commonLen q.caveats m.caveats))) q.tag :=
  accepted_edit_yields_cascade_forgery S key q m r ds hq hacc hd hi ha hnew

/-- **Stripped caveat.** With the chained-tag check removed, the token whose expiry caveat
was cut out is accepted; the real verifier answers `InvalidTag`. -/
theorem tooth_stripped_caveat_accepted_without_tag_check :
    ∃ tok : Token Nat DemoTag,
      verifyNoTag demoSuite tok demoRequest [] = .ok () ∧
        verify demoSuite 1 tok demoRequest [] = .error .invalidTag :=
  ⟨demoStripped, demo_stripped_accepted_without_tag_check, demo_stripped_rejected⟩

#verify_inhabited edit_yields_cascade_forgery_audited inhabited_edit
#tooth_pair accepted_edit_audited vs tooth_stripped_caveat_accepted_without_tag_check

theorem accepted_discharge_bound_audited [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (key : B) (tok : Token B T) (r : Request B) (ds : List (Discharge B T)) (id : B)
    (hacc : verify S key tok r ds = .ok ()) (hid : Caveat.thirdParty id ∈ tok.caveats) :
    ∃ d, (ds.filter fun d => decide (d.token.identifier = id)) = [d] ∧
      d.token.discharge = true ∧ d.token.audience = r.audience ∧
      Authentic S d.rootKey d.token ∧
      Caveat.bindToParent (S.bind tok.tag) ∈ d.token.caveats ∧
      ∀ b, Caveat.bindToParent b ∈ d.token.caveats → b = S.bind tok.tag :=
  accepted_discharge_bound S key tok r ds id hacc hid

theorem inhabited_discharge :
    ∃ (S : MacSuite Nat DemoTag) (key : Nat) (tok : Token Nat DemoTag) (r : Request Nat)
      (ds : List (Discharge Nat DemoTag)) (id : Nat),
      verify S key tok r ds = .ok () ∧ Caveat.thirdParty id ∈ tok.caveats :=
  ⟨demoSuite, 1, demoParent, demoRequest, [⟨demoBound, 6⟩], 5, demo_parent_accepted,
    demo_parent_has_thirdParty⟩

/-- **Unbound discharge.** With the parent-binding check removed, the discharge as the third
party issued it is accepted; the real verifier answers `UnboundDischarge`. -/
theorem tooth_unbound_discharge_accepted_without_binding_check :
    ∃ d : Token Nat DemoTag,
      verifyUnbound demoSuite 1 demoParent demoRequest [⟨d, 6⟩] = .ok () ∧
        verify demoSuite 1 demoParent demoRequest [⟨d, 6⟩] = .error .unboundDischarge :=
  ⟨demoUnbound, demo_unbound_accepted_without_binding_check, demo_unbound_rejected⟩

/-- A discharge bound to one token is refused for a sibling with the same caveat. -/
theorem tooth_transplanted_discharge_rejected :
    verify demoSuite 1 demoSibling demoRequest [⟨demoBound, 6⟩] = .error .denied :=
  demo_transplant_rejected

theorem discharge_not_transplantable_audited [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (key₁ key₂ : B) (tok₁ tok₂ : Token B T) (r₁ r₂ : Request B)
    (ds₁ ds₂ : List (Discharge B T)) (d : Discharge B T)
    (h₁ : verify S key₁ tok₁ r₁ ds₁ = .ok ()) (h₂ : verify S key₂ tok₂ r₂ ds₂ = .ok ())
    (hd₁ : d ∈ ds₁) (hd₂ : d ∈ ds₂) : S.bind tok₁.tag = S.bind tok₂.tag :=
  discharge_not_transplantable S key₁ key₂ tok₁ tok₂ r₁ r₂ ds₁ ds₂ d h₁ h₂ hd₁ hd₂

#verify_inhabited accepted_discharge_bound_audited inhabited_discharge
#tooth_pair accepted_discharge_bound_audited vs
  tooth_unbound_discharge_accepted_without_binding_check
theorem tooth_transplanted_discharge_cannot_accept :
    verify demoSuite 1 demoSibling demoRequest [⟨demoBound, 6⟩] ≠ .ok () := by
  rw [demo_transplant_rejected]
  decide

#tooth_pair discharge_not_transplantable_audited vs tooth_transplanted_discharge_cannot_accept

end Macaroon

section PorsFp
open PorsFpSecurity
variable {S D : Type}

theorem porsFpRoot_some_shape_audited (p : Params) (suite : HashSuite S D) (idx : List Nat)
    (secrets : List S) (auth : List D) (r : D)
    (h : porsFpRoot p suite idx secrets auth = some r) :
    p.wellFormed = true ∧ Admissible p idx ∧ secrets.length = p.reveal ∧
      auth.length = (octopusFrom p.treeHeight 0 idx).length :=
  porsFpRoot_some_shape p suite idx secrets auth r h

theorem inhabited_opening :
    ∃ (p : Params) (suite : HashSuite Nat DemoNode) (idx : List Nat) (secrets : List Nat)
      (auth : List DemoNode) (r : DemoNode), porsFpRoot p suite idx secrets auth = some r :=
  ⟨demoParams, demoSuite, demoIdx, demoIdx.map demoSecret,
    honestAuth demoSuite demoSecret demoParams.treeHeight demoIdx, demoRoot,
    demo_honest_opening_accepted⟩

/-- **Unsorted subset.** A root function without the order test that reads the first top node
accepts the index list `[2, 0]`, where only leaf 2 is opened honestly; the real one refuses. -/
theorem tooth_unsorted_subset_accepted_by_lax_root :
    ∃ (idx secrets : List Nat) (auth : List DemoNode),
      porsFpRootLax demoParams demoSuite idx secrets auth = some demoRoot ∧
        porsFpRoot demoParams demoSuite idx secrets auth = none :=
  ⟨demoUnsortedIdx, demoUnsortedSecrets, demoUnsortedAuth, demo_unsorted_accepted_by_lax,
    demo_unsorted_rejected⟩

#verify_inhabited porsFpRoot_some_shape_audited inhabited_opening
#tooth_pair porsFpRoot_some_shape_audited vs tooth_unsorted_subset_accepted_by_lax_root

theorem porsFpRoot_complete_audited (p : Params) (suite : HashSuite S D) (sec : Nat → S)
    (idx : List Nat) (hw : p.wellFormed = true) (hadm : Admissible p idx) :
    porsFpRoot p suite idx (idx.map sec) (honestAuth suite sec p.treeHeight idx) =
      some (honestTree suite sec p.treeHeight 0) :=
  porsFpRoot_complete p suite sec idx hw hadm

theorem inhabited_admissible :
    ∃ (_suite : HashSuite Nat DemoNode) (p : Params) (idx : List Nat),
      p.wellFormed = true ∧ Admissible p idx :=
  ⟨demoSuite, demoParams, demoIdx, demo_wellFormed, demo_admissible⟩

/-- Outside the pruning bound the honest opening is refused. -/
theorem tooth_pruned_opening_rejected :
    porsFpRoot ⟨2, 2, 1⟩ demoSuite demoIdx (demoIdx.map demoSecret)
      (honestAuth demoSuite demoSecret 2 demoIdx) = none :=
  demo_pruned_opening_rejected

#verify_inhabited porsFpRoot_complete_audited inhabited_admissible
#tooth_pair porsFpRoot_complete_audited vs tooth_pruned_opening_rejected

theorem porsFpRoot_binding_audited [DecidableEq S] [DecidableEq D] (p : Params)
    (suite : HashSuite S D) (idx : List Nat) (secs secs' : List S) (auth auth' : List D) (r : D)
    (h : porsFpRoot p suite idx secs auth = some r)
    (h' : porsFpRoot p suite idx secs' auth' = some r) :
    (secs = secs' ∧ auth = auth') ∨ LeafCollision suite ∨ NodeCollision suite :=
  porsFpRoot_binding p suite idx secs secs' auth auth' r h h'

/-- The collision alternative is needed: under a constant hash two different secret lists
open the same index set to the same root. -/
theorem tooth_colliding_hash_opens_twice :
    ∃ secs secs' : List Nat, secs ≠ secs' ∧
      porsFpRoot demoParams demoCollidingSuite demoIdx secs [0, 0] = some 0 ∧
      porsFpRoot demoParams demoCollidingSuite demoIdx secs' [0, 0] = some 0 :=
  ⟨[1, 2], [3, 4], by decide, demo_colliding_opening_a, demo_colliding_opening_b⟩

#verify_inhabited porsFpRoot_binding_audited inhabited_opening
#tooth_pair porsFpRoot_binding_audited vs tooth_colliding_hash_opens_twice

theorem forgery_fraction_bound_audited (p : Params) (acc : List Nat → Bool)
    (sigs : List (List Nat)) (r e : Nat) (hk : ∀ s ∈ sigs, s.length = p.reveal)
    (hsigs : sigs.length ≤ r)
    (hb : AtLeastBits e (ffTop (r * p.reveal) p.reveal) (ffTop p.leaves p.reveal))
    (hpos : 0 < ffTop (r * p.reveal) p.reveal) :
    AtLeastBits e (coverWins p acc (revealedBy sigs)).length (subsets p).length :=
  forgery_fraction_bound p acc sigs r e hk hsigs hb hpos

theorem inhabited_cover_bound :
    ∃ (p : Params) (sigs : List (List Nat)) (r e : Nat),
      (∀ s ∈ sigs, s.length = p.reveal) ∧ sigs.length ≤ r ∧
        AtLeastBits e (ffTop (r * p.reveal) p.reveal) (ffTop p.leaves p.reveal) ∧
        0 < ffTop (r * p.reveal) p.reveal :=
  ⟨sha3_128f, demoSigs, 1, 209, demo_sigs_uniform, demo_sigs_count, sha3_128f_ff_bits_one,
    sha3_128f_ff_pos_one⟩

theorem sha3_128f_forgery_bound_audited (acc : List Nat → Bool) (sigs : List (List Nat))
    (r : Nat) (hk : ∀ s ∈ sigs, s.length = sha3_128f.reveal) (hsigs : sigs.length ≤ r)
    (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    AtLeastBits (sha3Bits r) (coverWins sha3_128f acc (revealedBy sigs)).length
      (subsets sha3_128f).length :=
  sha3_128f_forgery_bound acc sigs r hk hsigs hr1 hr4

theorem inhabited_sha3_bound :
    ∃ (sigs : List (List Nat)) (r : Nat),
      (∀ s ∈ sigs, s.length = sha3_128f.reveal) ∧ sigs.length ≤ r ∧ 1 ≤ r ∧ r ≤ 4 :=
  ⟨demoSigs, 1, demo_sigs_uniform, demo_sigs_count, Nat.le_refl 1, by decide⟩

/-- Without distinct indices the 209-bit bound is false at one signature. -/
theorem tooth_bound_fails_without_distinctness : ¬ AtLeastBits 209 (28 ^ 28) (2048 ^ 28) :=
  sha3_128f_bound_fails_without_distinctness

#verify_inhabited forgery_fraction_bound_audited inhabited_cover_bound
#verify_inhabited sha3_128f_forgery_bound_audited inhabited_sha3_bound
#tooth_pair forgery_fraction_bound_audited vs tooth_bound_fails_without_distinctness
#tooth_pair sha3_128f_forgery_bound_audited vs tooth_bound_fails_without_distinctness

end PorsFp

end Qsag.CapabilityTeeth

/-! ## `Qsag.Custody.VolatileCoupon` -/

namespace Qsag.VolatileCoupon
set_option autoImplicit false

theorem tooth_q_le_n_is_insufficient :
    3 + (2 - 1) < 2 * 3 ∧ 3 ≤ 3 ∧ ¬ (3 * 2 - 2 ≤ (3 : Nat)) := by decide

theorem tooth_reused_vinegar_reveals_nonzero_oil :
    ((true ^^ true) ^^ (true ^^ false)) = true := by decide

/- One leaked column does not determine a two-column matrix. -/
theorem tooth_one_difference_not_full_key_recovery :
    let O₀ := fun p : Bool × Bool => p.1
    let O₁ := fun p : Bool × Bool => p.1 ^^ p.2
    O₀ (true, false) = O₁ (true, false) ∧ O₀ (false, true) ≠ O₁ (false, true) := by
  decide

/- Equal-sum, base-four codewords: collusion opens a third codeword neither branch opens.
The witness describes codeword exposure; finding a message for it still costs grinding. -/
theorem tooth_compact_fanout_strips_codeword_restriction :
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

/- Without an index in the leaf hash, a leaf can be relabeled across a bundle. -/
theorem tooth_unindexed_leaf_relabel :
    let H := fun (_index : Nat) (pk : Nat) => pk + 1
    H 0 7 = H 1 7 ∧ (0 : Nat) ≠ 1 := by decide

/- Dropping the child-root from authentication admits two conflicting cache entries. -/
theorem tooth_unauthenticated_waistband :
    let omittedRootMac := fun (pk : Nat) (_childRoot : Nat) => pk
    omittedRootMac 7 0 = omittedRootMac 7 1 ∧ (0 : Nat) ≠ 1 := by decide

/- A threshold-shared coupon across the full committee is unsafe: corrupt member 0
can join honest 1 and honest 2 in separate 2-of-3 completions. -/
theorem tooth_threshold_coupon_partition :
    let a := [0, 1]; let b := [0, 2]
    a.length = 2 ∧ b.length = 2 ∧
    (∀ p : Nat, p ∈ a → p ∈ b → p = 0) := by
  simp

theorem tooth_live_ram_clone_releases_twice :
    (consume true true 0).2 = some 0 ∧ (consume true true 1).2 = some 1 := by decide

theorem tooth_no_request_authentication_depletes_pool :
    (consume true true 0).1 = false ∧ (consume true false 0).1 = true := by decide

theorem tooth_public_coin_adaptive_grinding_bias :
    ([false, true].filter (fun coin => coinWins (!coin) coin)).length = 2 := by decide

/-! ### Request authentication -/

theorem authenticated_request_binding_audited {D Tag : Type} [DecidableEq D]
    (commit : Request → D) (mac : D → Tag) (committed received : Request)
    (ha : RequestAuthenticated commit mac committed received) :
    received = committed ∨ Collides commit ∨ Collides mac :=
  authenticated_request_binding commit mac committed received ha

def demoCommitted : Request := ⟨[], [1], [0, 1], [], 0, 9⟩
def demoReceived : Request := ⟨[], [1], [0, 1], [], 1, 9⟩

/-- A tag function that ignores its input accepts a request with another counter. -/
theorem inhabited_request_binding :
    ∃ (commit : Request → Nat) (mac : Nat → Nat) (committed received : Request),
      RequestAuthenticated commit mac committed received ∧ Collides mac :=
  ⟨fun r => r.counter, fun _ : Nat => 0, demoCommitted, demoReceived,
    ⟨rfl⟩, ⟨0, 1, by decide, rfl⟩⟩

/-- Without the equal-tag premise nothing is bound: with injective commitment and tag functions
two different requests satisfy none of the three alternatives. -/
theorem tooth_unequal_tags_bind_nothing :
    ∃ committed received : Request,
      ¬ (received = committed ∨ Collides (fun r : Request => r) ∨
        Collides (fun r : Request => r)) :=
  ⟨demoCommitted, demoReceived, fun h =>
    h.elim (fun he => absurd he (by decide))
      (fun h => h.elim (fun ⟨_, _, hne, he⟩ => hne he) (fun ⟨_, _, hne, he⟩ => hne he))⟩

#verify_inhabited authenticated_request_binding_audited inhabited_request_binding
#tooth_pair authenticated_request_binding_audited vs tooth_unequal_tags_bind_nothing

/-! ### The macaroon-gated slot -/

section CapabilityGate
open MacaroonAttenuation
variable {B T M : Type}

theorem capability_release_authorized_audited [DecidableEq B] [DecidableEq T] (S : MacSuite B T)
    (dep : Deployment B) (tok : Token B T) (r : MacaroonAttenuation.Request B)
    (ds : List (Discharge B T)) (ready : Bool) (m out : M)
    (hreg : ∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier)
    (h : (consumeUnderCapability S dep tok r ds ready m).2 = some out) :
    (consumeUnderCapability S dep tok r ds ready m).1 = false ∧ out = m ∧
      Authorized S tok dep r :=
  capability_release_authorized S dep tok r ds ready m out hreg h

theorem demo_registry : ∀ d ∈ [(⟨demoBound, 6⟩ : Discharge Nat DemoTag)],
    d.rootKey = demoDeployment.registry d.token.identifier :=
  fun d hd => by rw [List.mem_singleton.mp hd]; rfl

theorem demo_parent_releases :
    (consumeUnderCapability demoSuite demoDeployment demoParent demoRequest [⟨demoBound, 6⟩]
      true (7 : Nat)).2 = some 7 := by decide

theorem inhabited_capability_release :
    ∃ (S : MacSuite Nat DemoTag) (dep : Deployment Nat) (tok : Token Nat DemoTag)
      (r : MacaroonAttenuation.Request Nat) (ds : List (Discharge Nat DemoTag)) (ready : Bool)
      (m out : Nat),
      (∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier) ∧
      (consumeUnderCapability S dep tok r ds ready m).2 = some out :=
  ⟨demoSuite, demoDeployment, demoParent, demoRequest, [⟨demoBound, 6⟩], true, 7, 7,
    demo_registry, demo_parent_releases⟩

/-- A slot whose authorization bit is not tied to the verifier releases for a token the
deployment does not grant the request. -/
theorem tooth_ungated_slot_releases_unauthorized :
    ∃ tok : Token Nat DemoTag, (consume true true (7 : Nat)).2 = some 7 ∧
      ¬ Authorized demoSuite tok demoDeployment demoRequest :=
  ⟨demoExpired, by decide, demo_expired_not_authorized⟩

#verify_inhabited capability_release_authorized_audited inhabited_capability_release
#tooth_pair capability_release_authorized_audited vs tooth_ungated_slot_releases_unauthorized

theorem attenuated_capability_release_narrows_audited [DecidableEq B] [DecidableEq T]
    (S : MacSuite B T) (dep : Deployment B) (tok tok' : Token B T) (c : Caveat B)
    (r : MacaroonAttenuation.Request B) (ds : List (Discharge B T)) (ready : Bool) (m out : M)
    (hatt : attenuate S tok c = .ok tok') (hgen : Genuine S dep tok)
    (hreg : ∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier)
    (h : (consumeUnderCapability S dep tok' r ds ready m).2 = some out) :
    ∃ ds' : List (Discharge B T), (∀ d ∈ ds', d.rootKey = dep.registry d.token.identifier) ∧
      consumeUnderCapability S dep tok r ds' true m = (false, some m) :=
  attenuated_capability_release_narrows S dep tok tok' c r ds ready m out hatt hgen hreg h

theorem inhabited_attenuated_release :
    ∃ (S : MacSuite Nat DemoTag) (dep : Deployment Nat) (tok tok' : Token Nat DemoTag)
      (c : Caveat Nat) (r : MacaroonAttenuation.Request Nat) (ds : List (Discharge Nat DemoTag))
      (ready : Bool) (m out : Nat),
      attenuate S tok c = .ok tok' ∧ Genuine S dep tok ∧
      (∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier) ∧
      (consumeUnderCapability S dep tok' r ds ready m).2 = some out :=
  ⟨demoSuite, demoDeployment, demoScoped, demoParent, .thirdParty 5, demoRequest,
    [⟨demoBound, 6⟩], true, 7, 7, demo_attenuate_thirdParty, demo_scoped_genuine, demo_registry,
    demo_parent_releases⟩

/-- The narrowing is strict: the parent releases a request that its attenuation refuses. -/
theorem tooth_attenuated_capability_release_strict :
    ∃ tok tok' : Token Nat DemoTag,
      attenuate demoSuite tok (.expiresAt 5#64) = .ok tok' ∧
      consumeUnderCapability demoSuite demoDeployment tok demoRequest [] true (7 : Nat) =
        (false, some 7) ∧
      (consumeUnderCapability demoSuite demoDeployment tok' demoRequest [] true (7 : Nat)).2 =
        none :=
  ⟨demoScoped, demoExpired, demo_attenuate_expiry, by decide, by decide⟩

#verify_inhabited attenuated_capability_release_narrows_audited inhabited_attenuated_release
#tooth_pair attenuated_capability_release_narrows_audited vs tooth_attenuated_capability_release_strict

theorem failed_caveat_blocks_capability_release_audited [DecidableEq B] [DecidableEq T]
    (S : MacSuite B T) (dep : Deployment B) (tok tok' : Token B T) (c : Caveat B)
    (r : MacaroonAttenuation.Request B) (ds : List (Discharge B T)) (ready : Bool) (m : M)
    (hatt : attenuate S tok c = .ok tok') (hgen : Genuine S dep tok)
    (hfp : c.isThirdParty = false) (hfail : c.holds r = false)
    (hreg : ∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier) :
    (consumeUnderCapability S dep tok' r ds ready m).2 = none :=
  failed_caveat_blocks_capability_release S dep tok tok' c r ds ready m hatt hgen hfp hfail hreg

theorem inhabited_failed_caveat :
    ∃ (S : MacSuite Nat DemoTag) (dep : Deployment Nat) (tok tok' : Token Nat DemoTag)
      (c : Caveat Nat) (r : MacaroonAttenuation.Request Nat) (ds : List (Discharge Nat DemoTag)),
      attenuate S tok c = .ok tok' ∧ Genuine S dep tok ∧ c.isThirdParty = false ∧
      c.holds r = false ∧ (∀ d ∈ ds, d.rootKey = dep.registry d.token.identifier) :=
  ⟨demoSuite, demoDeployment, demoScoped, demoExpired, .expiresAt 5#64, demoRequest, [],
    demo_attenuate_expiry, demo_scoped_genuine, rfl, by decide, fun _ hd => nomatch hd⟩

def demoNotBefore : Token Nat DemoTag :=
  ⟨false, 4, 2, [.resource 3, .notBefore 1#64], ⟨1, false, 4, 2, [.resource 3, .notBefore 1#64]⟩⟩

/-- A first-party caveat that the request meets does not block the release. -/
theorem tooth_satisfied_caveat_does_not_block :
    ∃ tok' : Token Nat DemoTag,
      attenuate demoSuite demoScoped (.notBefore 1#64) = .ok tok' ∧
      ¬ ((consumeUnderCapability demoSuite demoDeployment tok' demoRequest [] true (7 : Nat)).2 =
        none) :=
  ⟨demoNotBefore, rfl, by decide⟩

#verify_inhabited failed_caveat_blocks_capability_release_audited inhabited_failed_caveat
#tooth_pair failed_caveat_blocks_capability_release_audited vs tooth_satisfied_caveat_does_not_block

theorem capability_release_discharge_not_transplantable_audited [DecidableEq B] [DecidableEq T]
    (S : MacSuite B T) (dep₁ dep₂ : Deployment B) (tok₁ tok₂ : Token B T)
    (r₁ r₂ : MacaroonAttenuation.Request B) (ds₁ ds₂ : List (Discharge B T))
    (ready₁ ready₂ : Bool) (m₁ m₂ out₁ out₂ : M) (d : Discharge B T)
    (h₁ : (consumeUnderCapability S dep₁ tok₁ r₁ ds₁ ready₁ m₁).2 = some out₁)
    (h₂ : (consumeUnderCapability S dep₂ tok₂ r₂ ds₂ ready₂ m₂).2 = some out₂)
    (hd₁ : d ∈ ds₁) (hd₂ : d ∈ ds₂) : S.bind tok₁.tag = S.bind tok₂.tag :=
  capability_release_discharge_not_transplantable S dep₁ dep₂ tok₁ tok₂ r₁ r₂ ds₁ ds₂
    ready₁ ready₂ m₁ m₂ out₁ out₂ d h₁ h₂ hd₁ hd₂

/-- The discharge bound to `demoParent` releases nothing for the sibling token that carries the
same third-party caveat. -/
theorem tooth_transplanted_discharge_releases_nothing :
    (consumeUnderCapability demoSuite demoDeployment demoSibling demoRequest [⟨demoBound, 6⟩]
      true (7 : Nat)).2 = none := by decide

theorem tooth_transplanted_discharge_cannot_release :
    (consumeUnderCapability demoSuite demoDeployment demoSibling demoRequest [⟨demoBound, 6⟩]
      true (7 : Nat)).2 ≠ some 7 := by
  rw [tooth_transplanted_discharge_releases_nothing]
  decide

#tooth_pair capability_release_discharge_not_transplantable_audited vs tooth_transplanted_discharge_cannot_release

end CapabilityGate

end Qsag.VolatileCoupon
