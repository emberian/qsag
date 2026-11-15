module
public import Qsag.Custody.SeparatedCustodyPolicy
import all Qsag.Custody.SeparatedCustodyPolicy
import all Qsag.Custody.CompleteMediationBoundary
import all Qsag.Custody.SeparatedCustodyCore
import Qsag.Tactic.AssuranceKit

/-! A finer-grained executable release path for the separate-key approval
construction. Reservation is still an atomic durable specification operation;
this module does not claim fsync refinement or a distributed threshold signer.

Consumption, actual partial production signing, and publication are separate
steps. `produced` is semantic observer history: a computed signature can be
useful even when the process crashes before returning it. It is not a disk log
that recovery may erase. Crashes discard both volatile continuations and buffers.
-/
public section
namespace Qsag.Custody.Release
set_option autoImplicit false

structure State where
  custody : PolicyVault
  pending : Option Intent := none
  buffered : Option Certificate := none
  produced : List (Intent × Option Certificate) := []
  published : List Certificate := []

def start (custody : PolicyVault) : State := ⟨custody, none, none, [], []⟩

/-- The exact state mutation of `release`, without invoking its producer. -/
def consume (anchor : Nat) (v : Vault) (r : Intent) : Vault × Bool :=
  if v.poisoned || decide (v.durable.anchor ≠ anchor) then
    ({ v with poisoned := true, active := none }, false)
  else if v.active = some r then
    ({ v with active := none, attempted := r :: v.attempted }, true)
  else (v, false)

theorem consume_state (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) :
    (consume anchor v r).1 = (release cfg sk party anchor v r).1 := by
  unfold consume release
  split <;> first | rfl | (split <;> rfl)

def begin (anchor : Nat) (s : State) (r : Intent) : State :=
  let result := consume anchor s.custody.vault r
  { s with
    custody := ⟨s.custody.policy, result.1⟩,
    pending := if result.2 then some r else none, buffered := none }

/-- Call the actual partial production signer once. Both failure and success
remain observable attempts; only success creates a potentially useful output. -/
def compute (cfg : SigningConfig) (sk : PqSecretKey) (s : State) : State :=
  match s.pending with
  | none => s
  | some r =>
    let out := (sign cfg sk s.custody.policy.party r).map
      (fun sig => ⟨s.custody.policy.party, r, sig⟩)
    { s with pending := none, buffered := out, produced := (r, out) :: s.produced }

def publish (s : State) : State :=
  match s.buffered with
  | none => s
  | some c => { s with buffered := none, published := c :: s.published }

def crash (s : State) : State :=
  { s with
    custody := ⟨s.custody.policy, forget s.custody.vault⟩,
    pending := none, buffered := none }

def reserve (p : RoundPolicy) (cap anchor : Nat) (s : State)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) : State :=
  { s with
    custody := mintTransaction p cap anchor s.custody tx tags timestamp round leaf ops,
    pending := none, buffered := none }

/-- Successful continuation has exactly the original producer semantics. -/
theorem compute_begin_output (cfg : SigningConfig) (sk : PqSecretKey)
    (anchor : Nat) (s : State) (r : Intent) :
    (compute cfg sk (begin anchor s r)).buffered =
      (release cfg sk s.custody.policy.party anchor s.custody.vault r).2 := by
  by_cases hp : (s.custody.vault.poisoned || decide (s.custody.vault.durable.anchor ≠ anchor)) = true
  · simp only [begin, consume, release, hp, ↓reduceIte, Bool.false_eq_true, compute]
  · by_cases ha : s.custody.vault.active = some r <;>
      simp only [begin, consume, release, hp, ha, ↓reduceIte, Bool.false_eq_true, compute]

theorem compute_local (cfg : SigningConfig) (sk : PqSecretKey) (s : State) :
    (compute cfg sk s).custody = s.custody := by
  unfold compute
  split <;> rfl

theorem compute_idempotent (cfg : SigningConfig) (sk : PqSecretKey) (s : State) :
    compute cfg sk (compute cfg sk s) = compute cfg sk s := by
  cases hp : s.pending <;> simp [compute, hp]

/-- A crash after consumption cannot repeat the producer call. -/
theorem crash_cancels_producer (cfg : SigningConfig) (sk : PqSecretKey) (s : State) :
    compute cfg sk (crash s) = crash s := by simp only [crash, compute]

/-- Potentially useful outputs survive in the observer history even when the
volatile output buffer is lost before publication. No refund follows a crash. -/
theorem crash_retains_effects (s : State) :
    (crash s).produced = s.produced ∧
    (crash s).published = s.published ∧
    (crash s).custody.policy = s.custody.policy ∧
    (crash s).custody.vault.durable = s.custody.vault.durable ∧
    (crash s).custody.vault.attempted = s.custody.vault.attempted :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem crash_no_return (s : State) : publish (crash s) = crash s := by simp only [crash, publish]

theorem publish_once (s : State) : publish (publish s) = publish s := by
  cases hb : s.buffered <;> simp [publish, hb]

/-- Every new computed certificate comes from the actual production signer,
including its actual identity, intent and optional failure semantics. -/
theorem computed_output (cfg : SigningConfig) (sk : PqSecretKey) (s : State)
    (r : Intent) (hp : s.pending = some r) :
    (compute cfg sk s).produced =
      (r, (sign cfg sk s.custody.policy.party r).map
        (fun sig => ⟨s.custody.policy.party, r, sig⟩)) :: s.produced := by
  simp only [compute, hp]

inductive Command where
  | reserve (anchor : Nat) (tx : TransactionIntent) (tags : List InitiatorPeerTag)
      (timestamp round leaf : Nat) (ops : List RoundOpening)
  | begin (anchor : Nat) (intent : Intent)
  | compute
  | publish
  | crash

def step (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy) (cap : Nat)
    (s : State) : Command → State
  | .reserve a tx tags time round leaf ops => reserve p cap a s tx tags time round leaf ops
  | .begin a r => begin a s r
  | .compute => compute cfg sk s
  | .publish => publish s
  | .crash => crash s

def run (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy) (cap : Nat) :
    State → List Command → State
  | s, [] => s
  | s, c :: cs => run cfg sk p cap (step cfg sk p cap s c) cs

theorem step_safe (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy)
    (cap : Nat) (s : State) (c : Command) (h : Safe p cap s.custody.vault) :
    Safe p cap (step cfg sk p cap s c).custody.vault := by
  cases c with
  | reserve a tx tags time round leaf ops =>
    exact mintTransaction_safe p cap a s.custody tx tags time round leaf ops h
  | begin a r =>
    change Safe p cap (consume a s.custody.vault r).1
    rw [consume_state cfg sk s.custody.policy.party]
    exact release_safe cfg sk s.custody.policy.party a p cap s.custody.vault r h
  | compute =>
    change Safe p cap (compute cfg sk s).custody.vault
    rw [compute_local]
    exact h
  | publish =>
    change Safe p cap (publish s).custody.vault
    unfold publish
    split <;> exact h
  | crash => exact forget_safe p cap s.custody.vault h

theorem run_safe (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy)
    (cap : Nat) (s : State) (cs : List Command) (h : Safe p cap s.custody.vault) :
    Safe p cap (run cfg sk p cap s cs).custody.vault := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_safe cfg sk p cap s c h)

/-- A production call cannot become disconnected from its retained reservation.
`attempted` conservatively includes a consumed continuation lost before compute;
`produced` records the exact calls that actually reached the producer. -/
structure Accounted (s : State) : Prop where
  pending : ∀ r, s.pending = some r → r ∈ s.custody.vault.attempted
  produced : ∀ r out, (r, out) ∈ s.produced → r ∈ s.custody.vault.attempted

theorem start_accounted (v : PolicyVault) : Accounted (start v) := by
  constructor
  · intro r h; cases h
  · intro r out h; cases h

theorem consume_monotone (a : Nat) (v : Vault) (r q : Intent)
    (h : q ∈ v.attempted) : q ∈ (consume a v r).1.attempted := by
  unfold consume
  split
  · exact h
  · split
    · exact List.mem_cons_of_mem _ h
    · exact h

theorem begin_accounted (a : Nat) (s : State) (r : Intent)
    (h : Accounted s) : Accounted (begin a s r) := by
  constructor
  · intro q hp
    by_cases hpo : (s.custody.vault.poisoned || decide (s.custody.vault.durable.anchor ≠ a)) = true
    · simp only [begin, consume, hpo, ↓reduceIte, Bool.false_eq_true] at hp
      cases hp
    · by_cases hac : s.custody.vault.active = some r
      · simp only [begin, consume, hpo, hac, ↓reduceIte] at hp ⊢
        have he : r = q := Option.some.inj hp
        subst q
        exact List.mem_cons_self
      · simp only [begin, consume, hpo, hac, ↓reduceIte, Bool.false_eq_true] at hp
        cases hp
  · intro q out hm
    exact consume_monotone a s.custody.vault r q (h.produced q out hm)

theorem compute_accounted (cfg : SigningConfig) (sk : PqSecretKey) (s : State)
    (h : Accounted s) : Accounted (compute cfg sk s) := by
  cases hp : s.pending with
  | none => simpa only [compute, hp] using h
  | some r =>
    simp only [compute, hp]
    constructor
    · intro q hq; cases hq
    · intro q out hm
      rcases List.mem_cons.mp hm with he | hold
      · have hq : q = r := congrArg Prod.fst he
        rw [hq]
        exact h.pending r hp
      · exact h.produced q out hold

theorem step_accounted (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy)
    (cap : Nat) (s : State) (c : Command) (h : Accounted s) :
    Accounted (step cfg sk p cap s c) := by
  cases c with
  | begin a r => exact begin_accounted a s r h
  | compute => exact compute_accounted cfg sk s h
  | publish =>
    change Accounted (publish s)
    unfold publish
    split
    · exact h
    · exact ⟨h.pending, h.produced⟩
  | crash => exact ⟨(fun _ he => by cases he), h.produced⟩
  | reserve a tx tags time round leaf ops =>
    constructor
    · intro r hr; cases hr
    · intro r out hm
      change r ∈ (mintTransaction p cap a s.custody tx tags time round leaf ops).vault.attempted
      rw [mintTransaction_attempted]
      exact h.produced r out hm

theorem run_accounted (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy)
    (cap : Nat) (s : State) (cs : List Command) (h : Accounted s) :
    Accounted (run cfg sk p cap s cs) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_accounted cfg sk p cap s c h)

/-- Any actual producer output (including an abort or an unpublished useful
certificate) in any crashed/interleaved local trace has a retained MAC-gated burn.
The burn provenance is derived from transitions, not supplied as a refinement. -/
theorem produced_has_burn (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy)
    (cap : Nat) (policy : AuthenticatedPolicyState) (cs : List Command)
    (r : Intent) (out : Option Certificate)
    (hm : (r, out) ∈ (run cfg sk p cap (start ⟨policy, initial⟩) cs).produced) :
    ∃ b ∈ (run cfg sk p cap (start ⟨policy, initial⟩) cs).custody.vault.durable.burned,
      b.intent = r ∧ checkRound p b.intent b.digest b.openings = true := by
  have ha := run_accounted cfg sk p cap (start ⟨policy, initial⟩) cs (start_accounted _)
  have hs := run_safe cfg sk p cap (start ⟨policy, initial⟩) cs (initial_safe p cap)
  obtain ⟨b, hb, he⟩ := hs.attemptedBurned r (ha.produced r out hm)
  exact ⟨b, hb, he, (hs.approved b hb).1⟩

/-- The successful no-crash path refines the actual policy entry point; its
soundness theorem therefore applies without any supplied admission judgement. -/
def transaction (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy)
    (cap anchor : Nat) (s : State) (tx : TransactionIntent)
    (tags : List InitiatorPeerTag) (timestamp round leaf : Nat) (ops : List RoundOpening) : State :=
  let reserved := reserve p cap anchor s tx tags timestamp round leaf ops
  compute cfg sk (begin reserved.custody.vault.durable.anchor reserved
    (transactionIntent tx round leaf))

theorem transaction_custody (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy)
    (cap anchor : Nat) (s : State) (tx : TransactionIntent)
    (tags : List InitiatorPeerTag) (timestamp round leaf : Nat) (ops : List RoundOpening) :
    (transaction cfg sk p cap anchor s tx tags timestamp round leaf ops).custody =
      (executeTransaction cfg sk p cap anchor s.custody tx tags timestamp round leaf ops).1 := by
  unfold transaction
  rw [compute_local]
  change PolicyVault.mk _ (consume _ _ _).1 = _
  rw [consume_state cfg sk s.custody.policy.party]
  rfl

theorem transaction_output (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy)
    (cap anchor : Nat) (s : State) (tx : TransactionIntent)
    (tags : List InitiatorPeerTag) (timestamp round leaf : Nat) (ops : List RoundOpening) :
    (transaction cfg sk p cap anchor s tx tags timestamp round leaf ops).buffered =
      (executeTransaction cfg sk p cap anchor s.custody tx tags timestamp round leaf ops).2 := by
  unfold transaction
  rw [compute_begin_output]
  have hid : (mintTransaction p cap anchor s.custody tx tags timestamp round leaf ops).policy.party =
      s.custody.policy.party := by
    by_cases ha : policyCheckAdmission s.custody.policy tx tags timestamp = true <;>
      simp only [mintTransaction, authenticatedPolicyGuardStep, ha, Bool.false_eq_true, ↓reduceIte]
  simp only [reserve]
  rw [hid]
  rfl

theorem transaction_sound (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy)
    (cap anchor : Nat) (s : State) (tx : TransactionIntent)
    (tags : List InitiatorPeerTag) (timestamp round leaf : Nat) (ops : List RoundOpening)
    (c : Certificate)
    (h : (transaction cfg sk p cap anchor s tx tags timestamp round leaf ops).buffered = some c) :
    c.party = s.custody.policy.party ∧
    policyCheckAdmission s.custody.policy tx tags timestamp = true ∧
    c.intent.spend = tx.amount_units ∧ c.intent.message = toCanonicalSigningBytes tx ∧
    verify cfg (derivePublicKey cfg.suite cfg.params sk) c.party c.intent c.signature = true := by
  rw [transaction_output] at h
  exact executeTransaction_sound cfg sk p cap anchor s.custody tx tags timestamp round leaf ops c h

end Qsag.Custody.Release
end
#verify_constructive Qsag.Custody.Release.run_safe
#verify_constructive Qsag.Custody.Release.transaction_sound
#verify_constructive Qsag.Custody.Release.compute_begin_output
#verify_constructive Qsag.Custody.Release.crash_retains_effects

#verify_constructive Qsag.Custody.Release.produced_has_burn

#verify_constructive Qsag.Custody.Release.transaction_custody
