module
public import Qsag.Custody.SeparatedCustodyCore
import all Qsag.Custody.SeparatedCustodyCore
import Qsag.Tactic.AssuranceKit

/-! Atomic spec transitions for one custodian. Durable changes precede release.
The host can forget, retry, reorder, or crash between transitions. Actual fsync,
key isolation, authenticated durable storage, and monotone hardware anchoring are
refinement obligations, not conclusions of this state-machine model. In particular
a same-sequence forged disk image is NOT authenticated by a bare sequence counter.
-/
public section
namespace Qsag.Custody
set_option autoImplicit false

structure Burn where
  intent : Intent
  digest : List UInt8
  openings : List RoundOpening

structure Ledger where
  nextLeaf : Nat := 0
  nextRound : Nat := 0
  spent : Nat := 0
  anchor : Nat := 0
  burned : List Burn := []

structure Vault where
  durable : Ledger := {}
  active : Option Intent := none
  attempted : List Intent := []
  poisoned : Bool := false

def initial : Vault := {}

def mintGuard (p : RoundPolicy) (cap : Nat) (v : Vault) (b : Burn) : Bool :=
  decide (v.durable.nextLeaf ≤ b.intent.leaf ∧ b.intent.round = v.durable.nextRound ∧
    v.durable.spent + b.intent.spend ≤ cap ∧
    b.intent.session ∉ v.durable.burned.map (fun x => x.intent.session) ∧
    b.intent.message ≠ []) && checkRound p b.intent b.digest b.openings

/-- The new external anchor and all burned cursors are returned together. A
permit is the exact stored request, not merely a forgeable generation number. -/
def mint (p : RoundPolicy) (cap anchor : Nat) (v : Vault) (b : Burn) : Vault :=
  if v.poisoned || decide (v.durable.anchor ≠ anchor) then
    { v with poisoned := true, active := none }
  else if mintGuard p cap v b then
    { v with
      durable := ⟨b.intent.leaf + 1, v.durable.nextRound + 1,
        v.durable.spent + b.intent.spend, anchor + 1, b :: v.durable.burned⟩
      active := some b.intent }
  else v

/-- In particular failure/abort of the production signer does not refund the
leaf or the spend. Every oracle call, including a failed call, is recorded. -/
def release (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) : Vault × Option Certificate :=
  if v.poisoned || decide (v.durable.anchor ≠ anchor) then
    ({ v with poisoned := true, active := none }, none)
  else if v.active = some r then
    ({ v with active := none, attempted := r :: v.attempted },
      (sign cfg sk party r).map (fun sig => ⟨party, r, sig⟩))
  else (v, none)

/-- `mem::forget` and crash both discard the volatile grant; neither refunds
durable reservations. This is stronger than safety dependent on Drop running. -/
@[expose] def forget (v : Vault) : Vault := { v with active := none }

structure Safe (p : RoundPolicy) (cap : Nat) (v : Vault) : Prop where
  budget : v.durable.spent ≤ cap
  accounting : v.durable.spent = (v.durable.burned.map (fun b => b.intent.spend)).sum
  past : ∀ b ∈ v.durable.burned,
    b.intent.leaf < v.durable.nextLeaf ∧ b.intent.round < v.durable.nextRound
  uniqueLeaf : ∀ b ∈ v.durable.burned, ∀ c ∈ v.durable.burned,
    b.intent.leaf = c.intent.leaf → b.intent = c.intent
  approved : ∀ b ∈ v.durable.burned,
    checkRound p b.intent b.digest b.openings = true ∧ b.intent.message ≠ []
  activeBurned : ∀ r, v.active = some r → ∃ b ∈ v.durable.burned, b.intent = r
  attemptedBurned : ∀ r ∈ v.attempted, ∃ b ∈ v.durable.burned, b.intent = r
  activeFresh : ∀ r, v.active = some r → r ∉ v.attempted
  attemptedNodup : v.attempted.Nodup

theorem initial_safe (p : RoundPolicy) (cap : Nat) : Safe p cap initial := by
  constructor
  · exact Nat.zero_le _
  · rfl
  · intro b h; cases h
  · intro b h; cases h
  · intro b h; cases h
  · intro r h; cases h
  · intro r h; cases h
  · intro r h; cases h
  · exact .nil

private theorem disable_safe {p : RoundPolicy} {cap : Nat} {v : Vault}
    (h : Safe p cap v) (poison : Bool) :
    Safe p cap { v with active := none, poisoned := poison } := by
  exact ⟨h.budget, h.accounting, h.past, h.uniqueLeaf, h.approved,
    (fun _ he => by cases he), h.attemptedBurned, (fun _ he => by cases he), h.attemptedNodup⟩

theorem mint_safe (p : RoundPolicy) (cap anchor : Nat) (v : Vault) (b : Burn)
    (h : Safe p cap v) : Safe p cap (mint p cap anchor v b) := by
  unfold mint
  split
  · exact disable_safe h true
  · split
    next hg =>
      obtain ⟨hc, hm⟩ := Bool.and_eq_true_iff.mp hg
      obtain ⟨hl, hr, hb, _hf, hn⟩ := of_decide_eq_true hc
      constructor
      · exact hb
      · change v.durable.spent + b.intent.spend =
          b.intent.spend + (v.durable.burned.map (fun c => c.intent.spend)).sum
        rw [h.accounting, Nat.add_comm]
      · intro c hmem
        rcases List.mem_cons.mp hmem with he | he
        · subst c
          exact ⟨Nat.lt_succ_self _, hr ▸ Nat.lt_succ_self _⟩
        · obtain ⟨hcl, hcr⟩ := h.past c he
          exact ⟨Nat.lt_trans hcl (Nat.lt_succ_of_le hl), Nat.lt_trans hcr (Nat.lt_succ_self _)⟩
      · intro c hc d hd heq
        rcases List.mem_cons.mp hc with hc | hc
        · subst c
          rcases List.mem_cons.mp hd with hd | hd
          · subst d; rfl
          · have hp := (h.past d hd).1
            exact False.elim ((Nat.not_lt_of_ge hl) (heq ▸ hp))
        · rcases List.mem_cons.mp hd with hd | hd
          · subst d
            have hp := (h.past c hc).1
            exact False.elim ((Nat.not_lt_of_ge hl) (heq ▸ hp))
          · exact h.uniqueLeaf c hc d hd heq
      · intro c hc
        rcases List.mem_cons.mp hc with hc | hc
        · subst c; exact ⟨hm, hn⟩
        · exact h.approved c hc
      · intro r he
        have he' : b.intent = r := Option.some.inj he
        exact ⟨b, List.mem_cons_self, he'⟩
      · intro r hm
        obtain ⟨c, hc, he⟩ := h.attemptedBurned r hm
        exact ⟨c, List.mem_cons_of_mem _ hc, he⟩
      · intro r he hrmem
        have he' : b.intent = r := Option.some.inj he
        obtain ⟨c, hc, hcr⟩ := h.attemptedBurned r hrmem
        have hp := (h.past c hc).1
        rw [hcr, ← he'] at hp
        exact (Nat.not_lt_of_ge hl) hp
      · exact h.attemptedNodup
    next => exact h

theorem mint_granted (p : RoundPolicy) (cap anchor : Nat) (v : Vault) (b : Burn)
    (r : Intent) (ha : v.active = none) (h : (mint p cap anchor v b).active = some r) :
    mintGuard p cap v b = true ∧ b.intent = r := by
  unfold mint at h
  split at h
  · cases h
  · split at h
    next hg => exact ⟨hg, Option.some.inj h⟩
    next => rw [ha] at h; cases h

theorem release_safe (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (p : RoundPolicy) (cap : Nat) (v : Vault) (r : Intent) (h : Safe p cap v) :
    Safe p cap (release cfg sk party anchor v r).1 := by
  unfold release
  split
  · exact disable_safe h true
  · split
    next ha =>
      refine ⟨h.budget, h.accounting, h.past, h.uniqueLeaf, h.approved,
        (fun _ he => by cases he), ?_, (fun _ he => by cases he), ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with hs | hs
        · subst s; exact h.activeBurned r ha
        · exact h.attemptedBurned s hs
      · exact List.nodup_cons.mpr ⟨h.activeFresh r ha, h.attemptedNodup⟩
    next => exact h

theorem forget_safe (p : RoundPolicy) (cap : Nat) (v : Vault) (h : Safe p cap v) :
    Safe p cap (forget v) := by
  exact ⟨h.budget, h.accounting, h.past, h.uniqueLeaf, h.approved,
    (fun _ he => by cases he), h.attemptedBurned, (fun _ he => by cases he), h.attemptedNodup⟩

inductive Command where
  | mint (anchor : Nat) (b : Burn)
  | release (anchor : Nat) (r : Intent)
  | forget
  | crash

def step (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (p : RoundPolicy) (cap : Nat) (v : Vault) : Command → Vault
  | .mint a b => mint p cap a v b
  | .release a r => (release cfg sk party a v r).1
  | .forget | .crash => forget v

def run (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (p : RoundPolicy) (cap : Nat) : Vault → List Command → Vault
  | v, [] => v
  | v, c :: cs => run cfg sk party p cap (step cfg sk party p cap v c) cs

theorem run_safe (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (p : RoundPolicy) (cap : Nat) (cs : List Command) (v : Vault) (h : Safe p cap v) :
    Safe p cap (run cfg sk party p cap v cs) := by
  induction cs generalizing v with
  | nil => exact h
  | cons c cs ih =>
    apply ih
    cases c with
    | mint a b => exact mint_safe p cap a v b h
    | release a r => exact release_safe cfg sk party a p cap v r h
    | forget => exact forget_safe p cap v h
    | crash => exact forget_safe p cap v h

theorem release_durable (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) :
    (release cfg sk party anchor v r).1.durable = v.durable := by
  unfold release; split <;> first | rfl | (split <;> rfl)

theorem forget_burns (v : Vault) : (forget v).durable = v.durable := rfl

theorem release_no_active (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) (h : v.active = none) :
    (release cfg sk party anchor v r).2 = none := by
  unfold release
  split
  · rfl
  · simp [h]

theorem release_consumes (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) (c : Certificate)
    (h : (release cfg sk party anchor v r).2 = some c) :
    (release cfg sk party anchor v r).1.active = none := by
  unfold release
  split
  · rfl
  next hp =>
    split
    · rfl
    next ha =>
      simp only [release, hp, ha, ↓reduceIte] at h
      cases h

/-- Replay rejection holds even if the caller retains or copies the old handle. -/
theorem release_replay_rejected (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) (c : Certificate)
    (h : (release cfg sk party anchor v r).2 = some c) :
    (release cfg sk party anchor (release cfg sk party anchor v r).1 r).2 = none :=
  release_no_active cfg sk party anchor _ r (release_consumes cfg sk party anchor v r c h)

/-- Successful outputs contain precisely the production signer's result for
the bound request, rather than a caller-selected signature. -/
theorem release_output (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) (c : Certificate)
    (h : (release cfg sk party anchor v r).2 = some c) :
    c.party = party ∧ c.intent = r ∧ sign cfg sk party r = some c.signature := by
  unfold release at h
  split at h
  · cases h
  · split at h
    next =>
      cases hs : sign cfg sk party r with
      | none => simp only [hs, Option.map_none] at h; cases h
      | some sig =>
        simp only [hs, Option.map_some, Option.some.injEq] at h
        subst c
        exact ⟨rfl, rfl, rfl⟩
    next => cases h

theorem release_verifies (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) (c : Certificate)
    (h : (release cfg sk party anchor v r).2 = some c) :
    verify cfg (derivePublicKey cfg.suite cfg.params sk) c.party c.intent c.signature = true := by
  obtain ⟨hp, hr, hs⟩ := release_output cfg sk party anchor v r c h
  rw [hp, hr]
  exact sign_verifies cfg sk party r c.signature hs

theorem release_wrong_request (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r s : Intent) (ha : v.active = some s) (hne : r ≠ s) :
    (release cfg sk party anchor v r).2 = none := by
  unfold release
  split
  · rfl
  · have hn : ¬ v.active = some r := by
      intro he; exact hne (Option.some.inj (he.symm.trans ha))
    simp only [hn, ↓reduceIte]

def queries (cfg : SigningConfig) (party : Nat) (v : Vault) : List ProdSigningQuery :=
  v.attempted.map (query cfg party)

theorem queries_one_time (cfg : SigningConfig) (party : Nat) (p : RoundPolicy)
    (cap : Nat) (v : Vault) (h : Safe p cap v) :
    ∀ q ∈ queries cfg party v, ∀ q' ∈ queries cfg party v, q.epoch = q'.epoch → q = q' := by
  intro q hq q' hq' he
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq'
  obtain ⟨b, hb, heB⟩ := h.attemptedBurned r hr
  obtain ⟨c, hc, heC⟩ := h.attemptedBurned s hs
  have hrs : r = s := by
    rw [← heB, ← heC]
    apply h.uniqueLeaf b hb c hc
    simpa only [query, heB, heC] using he
  rw [hrs]

/-- This is a conclusion about actual trace-generated state, not an assumed
one-time oracle discipline fed to the cryptographic reduction. -/
theorem trace_queries_one_time (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (p : RoundPolicy) (cap : Nat) (cs : List Command) :
    ∀ q ∈ queries cfg party (run cfg sk party p cap initial cs),
    ∀ q' ∈ queries cfg party (run cfg sk party p cap initial cs),
    q.epoch = q'.epoch → q = q' :=
  queries_one_time cfg party p cap _ (run_safe cfg sk party p cap cs initial (initial_safe p cap))

/-- The budget bound is about the sum of actual burned transaction spends,
including forgotten or failed requests, not merely an unrelated counter. -/
theorem trace_burned_spend_le_cap (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (p : RoundPolicy) (cap : Nat) (cs : List Command) :
    (((run cfg sk party p cap initial cs).durable.burned).map (fun b => b.intent.spend)).sum ≤ cap := by
  have hs := run_safe cfg sk party p cap cs initial (initial_safe p cap)
  rw [← hs.accounting]
  exact hs.budget

end Qsag.Custody
end
set_option maxRecDepth 4096
#verify_constructive Qsag.Custody.run_safe
#verify_constructive Qsag.Custody.trace_queries_one_time
#verify_constructive Qsag.Custody.release_replay_rejected
#verify_constructive Qsag.Custody.release_verifies
#verify_constructive Qsag.Custody.forget_burns
#verify_constructive Qsag.Custody.trace_burned_spend_le_cap
