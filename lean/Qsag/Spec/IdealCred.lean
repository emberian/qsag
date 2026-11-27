module
/-
# Qsag.Spec.IdealCred — Ideal Selective-Disclosure Anonymous Credential & TOPRF Functionality

Layer-0 ideal functionality for `crates/qsag-cred/src/blind_vc.rs` (`PiBlindVc`: per-epoch
accumulator, selective-disclosure presentations) and the replicated threshold OPRF of
`crates/qsag-cred/src/voprf.rs`.

Authentication is an ideal-world event, not a checkable token. Every input is a pair
`(port, command)`. The ports are the issuer, each holder `h`, each TOPRF server `i`, the TOPRF
client and the adversary. `IdealCredState.speaksFor` lets a command through only on the port of
the party it is attributed to, or on the adversary port when that party is corrupt in the current
state.

**Adaptive corruption.** The corruption set (issuer flag, corrupt holders, corrupt servers) is
part of the state. It starts as the set named by the configuration and grows by the command
`.corrupt party`, admitted on the adversary port only, always answered `.corrupted`, at any point
of a run. Corruption is never undone (`idealCredStep_provenance`, `idealCred_trace_provenance`:
the corruption set only grows). The functionality enforces no corruption budget: a bound on the
number of corrupt servers is a hypothesis of the theorem that needs it, about the state in which
the event happens. Guarantees come in two forms: about the state in which an input was processed
(`CredEventAt`), and, by monotonicity, about the final state of the run. The second gives:
a party that is not corrupt at the end of a run sent every command attributed to it in that run
on its own port (`idealCredMachine_honest_issuer_port`, `idealCredMachine_honest_holder_port`,
`idealCredMachine_honest_server_port`).

* **Issuance** creates a record owned by the holder it names; the credential identifier in the
  output is the possession capability. Every record of a run was created by an issuance event of
  that run, on the issuer port, or on the adversary port in a state where the issuer was corrupt
  (`idealCredMachine_record_provenance`, `idealCredMachine_record_provenance_at`).
* **Presentation** of credential `cid` by holder `h` is accepted only for a record with that
  identifier owned by `h`, of the current epoch, whose attributes satisfy the statement, for the
  current issuer key, epoch and accumulator root and a fresh challenge. It was made on the port of
  `h`, or on the adversary port in a state where `h` was corrupt
  (`idealCredMachine_presentation_provenance`). Which eligible credential was shown is invisible
  in outputs and successor state (`idealCredMachine_presentation_trace_unlinkable`).
* **TOPRF.** Servers approve tickets `(keyId, epoch, counter)` on their own ports. An evaluation is
  answered when `toprfOnlineServers` (four of five, `voprf.rs:4`–`5`) distinct servers approved
  its ticket, the per-key quota is not exhausted and the counter passes `admit_counter`
  (`voprf.rs:310`). It returns the keyed-table value of `(keyId, epoch, input)`. If at most
  `toprfMaxCorrupt` servers are corrupt in the state that answers, at least one approval came from
  the port of a server not corrupt in that state (`idealCredMachine_toprf_provenance`). An approval
  stays recorded when its server is corrupted later, and the adversary can reach the quorum alone
  once it has corrupted enough servers (`idealCredDemo_adaptive_quorum_without_server_port`).

Not modelled: corrupting a holder hands the adversary that holder's port (it can then present the
holder's credentials), but there is no separate leakage output for the holder's attribute values,
and likewise none for issuer or server key material; record identifiers are already public
outputs of issuance. With a corrupt issuer the adversary can issue anything
(`idealCredDemo_corrupt_issuer_issues`). One ticket covers one item; batches and per-credential
revocation (other than epoch rotation) are not modelled.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## Verifier-owned challenge ledgers

The executable state below follows `presentation_challenge.rs`: only outstanding challenges
are retained, issuance is bounded, expiry frees capacity, and a valid presentation removes its
challenge. Each verifier owns its entire ledger (including capacity and issuance counter),
independently of the statement scope. One verifier may issue for several scopes; two verifiers
may use identical scopes and challenge names without sharing state.
`Nat` challenge names idealize collision-free outputs of the Rust cSHAKE derivation containing
that ledger's strictly increasing issuance counter. This is an ideal-function model, not a
claim that a finite digest is injective, nor a proof of its unpredictability. Clock rollback
can extend an outstanding challenge's lifetime but cannot resurrect a consumed challenge.
-/

structure VerifierChallengeLedger where
  capacity : Nat := 65536
  issued : Nat := 0
  outstanding : List ((Bytes × Nat) × Nat) := []
  deriving DecidableEq, Repr

/-- The verifier clock is a caller parameter, as for Rust `ledger.at(now)`. -/
def VerifierChallengeLedger.accepts (l : VerifierChallengeLedger) (scope : Bytes) (nonce now : Nat) : Bool :=
  l.outstanding.any (fun e => decide (e.1 = (scope, nonce)) && decide (now < e.2))

/-- Remove every occurrence: malformed duplicate entries cannot permit replay either. -/
def VerifierChallengeLedger.consume (l : VerifierChallengeLedger) (scope : Bytes) (nonce : Nat) :
    VerifierChallengeLedger :=
  { l with outstanding := l.outstanding.filter (fun e => decide (e.1 ≠ (scope, nonce))) }

/-- Fresh challenge issuance, including the Rust capacity and u64 lifetime/counter bounds.
    A live challenge is never evicted to make room. -/
def VerifierChallengeLedger.issue (l : VerifierChallengeLedger) (scope : Bytes) (now ttl : Nat) :
    Option (VerifierChallengeLedger × Nat) :=
  let live := l.outstanding.filter (fun e => decide (now < e.2))
  if 0 < l.capacity ∧ l.capacity ≤ 65536 ∧ 0 < ttl ∧ now + ttl < 2^64 ∧
      live.length < l.capacity ∧ l.issued + 1 < 2^64 then
    some ({ l with issued := l.issued + 1,
                   outstanding := ((scope, l.issued + 1), now + ttl) :: live }, l.issued + 1)
  else none

/-- Rust prunes expired challenges after validating the capacity and lifetime, before checking
    remaining room and counter exhaustion. This mutation survives a later issuance refusal. -/
def VerifierChallengeLedger.prune (l : VerifierChallengeLedger) (now : Nat) :
    VerifierChallengeLedger :=
  { l with outstanding := l.outstanding.filter (fun e => decide (now < e.2)) }

/-- Stateful issuance, including its failure path. `issue` computes a successful fresh issue;
    this wrapper preserves the Rust post-pruning state when a later check refuses it. -/
def VerifierChallengeLedger.issueAttempt (l : VerifierChallengeLedger) (scope : Bytes)
    (now ttl : Nat) : VerifierChallengeLedger × Option Nat :=
  if 0 < l.capacity ∧ l.capacity ≤ 65536 ∧ 0 < ttl ∧ now + ttl < 2^64 then
    match l.issue scope now ttl with
    | some (next, nonce) => (next, some nonce)
    | none => (l.prune now, none)
  else (l, none)

/-- A proof failure never touches the ledger; consumption happens only after verification. -/
def VerifierChallengeLedger.verify (l : VerifierChallengeLedger) (proofValid : Bool)
    (scope : Bytes) (nonce now : Nat) : VerifierChallengeLedger × Bool :=
  if proofValid && l.accepts scope nonce now then (l.consume scope nonce, true) else (l, false)

/-- Explicit proof-audit opt-out, mirroring Rust `ReplayNotPrevented`. It is deliberately
    separate from the authorization machine and gives no one-time acceptance guarantee. -/
def ReplayNotPrevented (expected nonce : Nat) (proofValid : Bool) : Bool :=
  proofValid && decide (expected = nonce)

abbrev VerifierChallengeLedgers := Nat → VerifierChallengeLedger

def VerifierChallengeLedgers.set (ls : VerifierChallengeLedgers) (verifier : Nat)
    (l : VerifierChallengeLedger) : VerifierChallengeLedgers :=
  fun v => if v = verifier then l else ls v

def VerifierChallengeLedgers.consume (ls : VerifierChallengeLedgers) (verifier : Nat)
    (scope : Bytes) (nonce : Nat) : VerifierChallengeLedgers :=
  ls.set verifier ((ls verifier).consume scope nonce)

theorem VerifierChallengeLedger.consume_rejects (l : VerifierChallengeLedger)
    (scope : Bytes) (nonce now : Nat) : (l.consume scope nonce).accepts scope nonce now = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨e, he, hBoth⟩ := List.any_eq_true.mp h
  have hEq := (Bool.and_eq_true_iff.mp hBoth).1
  obtain ⟨_, hNe⟩ := List.mem_filter.mp he
  exact (of_decide_eq_true hNe) (of_decide_eq_true hEq)

theorem VerifierChallengeLedger.invalid_proof_preserves (l : VerifierChallengeLedger)
    (scope : Bytes) (nonce now : Nat) : l.verify false scope nonce now = (l, false) := by rfl

/-- A successful verification makes the same challenge fail, even at an earlier clock time. -/
theorem VerifierChallengeLedger.accepted_at_most_once (l l' : VerifierChallengeLedger)
    (proofValid : Bool) (scope : Bytes) (nonce now later : Nat)
    (h : l.verify proofValid scope nonce now = (l', true)) :
    l'.verify true scope nonce later = (l', false) := by
  unfold verify at h
  split at h
  · have hs := (Prod.mk.inj h).1
    rw [← hs]
    simp only [verify, consume_rejects, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  · cases (Prod.mk.inj h).2

/-- Equality of the observer's ledger suffices for identical refusals and successor state;
    all other verifier ledgers may differ arbitrarily. -/
theorem VerifierChallengeLedgers.refusal_noninterference (a b : VerifierChallengeLedgers)
    (verifier : Nat) (h : a verifier = b verifier) (valid : Bool) (scope : Bytes) (nonce now : Nat) :
    (a verifier).verify valid scope nonce now = (b verifier).verify valid scope nonce now := by rw [h]

theorem VerifierChallengeLedgers.set_other (ls : VerifierChallengeLedgers)
    (a b : Nat) (h : b ≠ a) (l : VerifierChallengeLedger) :
    (ls.set a l) b = ls b := by
  simp only [set, h, ↓reduceIte]

/-- Every outstanding name came from an issuance no later than the current counter. -/
def VerifierChallengeLedger.WellFormed (l : VerifierChallengeLedger) : Prop :=
  ∀ e ∈ l.outstanding, e.1.2 ≤ l.issued

/-- Consumed (or expired and pruned) names cannot be reissued: the counter has passed them. -/
def VerifierChallengeLedger.Retired (l : VerifierChallengeLedger) (scope : Bytes) (nonce : Nat) : Prop :=
  nonce ≤ l.issued ∧ ∀ e ∈ l.outstanding, e.1 ≠ (scope, nonce)

theorem VerifierChallengeLedger.issue_shape {l l' : VerifierChallengeLedger} {scope : Bytes} {now ttl n : Nat}
    (h : l.issue scope now ttl = some (l', n)) :
    n = l.issued + 1 ∧ l'.issued = l.issued + 1 ∧
      ∀ e ∈ l'.outstanding, e.1.2 = n ∨ e ∈ l.outstanding := by
  unfold issue at h
  dsimp only at h
  split at h
  · obtain ⟨hs, hn⟩ := Prod.mk.inj (Option.some.inj h)
    rw [← hs, ← hn]
    refine ⟨rfl, rfl, fun e he => ?_⟩
    rcases List.mem_cons.mp he with he | he
    · exact Or.inl (congrArg (fun e : (Bytes × Nat) × Nat => e.1.2) he)
    · exact Or.inr (List.mem_filter.mp he).1
  · cases h

/-- All possible ledger changes, including intervening issuance, successful consumption,
    refusal, and changes to other scopes. No constructor permits restoring old state. -/
inductive VerifierLedgerEvolution : VerifierChallengeLedger → VerifierChallengeLedger → Prop
  | refl (l) : VerifierLedgerEvolution l l
  | issue {l l' scope now ttl n} (h : l.issue scope now ttl = some (l', n)) :
      VerifierLedgerEvolution l l'
  | consume (l scope nonce) : VerifierLedgerEvolution l (l.consume scope nonce)
  | prune (l now) : VerifierLedgerEvolution l (l.prune now)
  | trans {a b c} : VerifierLedgerEvolution a b → VerifierLedgerEvolution b c →
      VerifierLedgerEvolution a c

theorem VerifierLedgerEvolution.wellFormed {l l' : VerifierChallengeLedger}
    (h : VerifierLedgerEvolution l l') (hw : l.WellFormed) : l'.WellFormed := by
  induction h with
  | refl => exact hw
  | issue h =>
    obtain ⟨hn, hi, he⟩ := VerifierChallengeLedger.issue_shape h
    intro e hem
    rw [hi]
    rcases he e hem with hnew | hold
    · rw [hnew, hn]
      exact Nat.le_refl _
    · exact Nat.le_trans (hw e hold) (Nat.le_succ _)
  | consume l scope nonce =>
    exact fun e he => hw e (List.mem_filter.mp he).1
  | prune l now =>
    exact fun e he => hw e (List.mem_filter.mp he).1
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hw)

theorem VerifierLedgerEvolution.retired {l l' : VerifierChallengeLedger}
    (h : VerifierLedgerEvolution l l') {scope : Bytes} {nonce : Nat} (hr : l.Retired scope nonce) :
    l'.Retired scope nonce := by
  induction h with
  | refl => exact hr
  | issue h =>
    obtain ⟨hn, hi, he⟩ := VerifierChallengeLedger.issue_shape h
    refine ⟨hi ▸ Nat.le_trans hr.1 (Nat.le_succ _), fun e hem eq => ?_⟩
    rcases he e hem with hnew | hold
    · have hn' : nonce = _ + 1 := (congrArg Prod.snd eq).symm.trans (hnew.trans hn)
      exact Nat.not_succ_le_self _ (hn' ▸ hr.1)
    · exact hr.2 e hold eq
  | consume l other n =>
    exact ⟨hr.1, fun e he => hr.2 e (List.mem_filter.mp he).1⟩
  | prune l now =>
    exact ⟨hr.1, fun e he => hr.2 e (List.mem_filter.mp he).1⟩
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hr)

theorem VerifierChallengeLedger.issueAttempt_evolution (l : VerifierChallengeLedger)
    (scope : Bytes) (now ttl : Nat) :
    VerifierLedgerEvolution l (l.issueAttempt scope now ttl).1 := by
  unfold issueAttempt
  split
  · cases he : l.issue scope now ttl with
    | none => exact .prune _ _
    | some pair =>
      obtain ⟨next, nonce⟩ := pair
      exact .issue he
  · exact .refl _

theorem VerifierChallengeLedger.accepted_retired (l : VerifierChallengeLedger)
    (scope : Bytes) (nonce now : Nat) (hw : l.WellFormed) (ha : l.accepts scope nonce now = true) :
    (l.consume scope nonce).Retired scope nonce := by
  obtain ⟨e, he, hb⟩ := List.any_eq_true.mp ha
  have hn := of_decide_eq_true (Bool.and_eq_true_iff.mp hb).1
  have hn' : e.1.2 = nonce := congrArg Prod.snd hn
  refine ⟨hn' ▸ hw e he, fun e he => ?_⟩
  exact of_decide_eq_true (List.mem_filter.mp he).2

theorem VerifierChallengeLedger.Retired.rejects {l : VerifierChallengeLedger} {scope : Bytes} {nonce : Nat}
    (hr : l.Retired scope nonce) (now : Nat) : l.accepts scope nonce now = false := by
  apply Bool.eq_false_iff.mpr
  intro ha
  obtain ⟨e, he, hb⟩ := List.any_eq_true.mp ha
  exact hr.2 e he (of_decide_eq_true (Bool.and_eq_true_iff.mp hb).1)

/-! ## 1. Statements, ports, commands -/

/-- Public selective-disclosure presentation statement pinned by the verifier (`blind_vc.rs`):
    contains only the disclosed `(index, value)` pairs, never the full hidden attribute vector. -/
structure CredentialStatement (Attr : Type) where
  issuerPk : Bytes
  epoch : Nat
  accumulatorRoot : Digest256
  disclosed : List (Nat × Attr)
  /-- Ideal fresh name of the challenge issued by this verifier ledger. -/
  challengeNonce : Nat
  /-- Verifier instance selected by the service caller, independently of the scope. -/
  verifier : Nat := 0
  verifierScope : Bytes := []
  deriving DecidableEq, Repr

/-- Disclosed attribute indices are strictly below `pqCredentialProfile.maxAttrs` (`32`) and
    duplicate-free (`InvalidDisclosedAttributeIndex`, `DuplicateDisclosedAttributeIndex` in
    `blind_vc.rs`). -/
@[expose] def DisclosedIndicesValid {Attr : Type} (stmt : CredentialStatement Attr) : Bool :=
  stmt.disclosed.all (fun p => decide (p.1 < pqCredentialProfile.maxAttrs)) &&
  decide (stmt.disclosed.map Prod.fst).Nodup

/-- The attribute vector `attrs` satisfies `stmt`: it has between `1` and `maxAttrs` (`32`)
    attributes (`blind_vc.rs:179`), the disclosed index list is valid, and every
    `(idx, val) ∈ stmt.disclosed` equals `attrs[idx]?`. -/
@[expose] def CredentialMatchesAttributes {Attr : Type} [DecidableEq Attr]
    (stmt : CredentialStatement Attr) (attrs : List Attr) : Bool :=
  decide (0 < attrs.length) &&
  decide (attrs.length ≤ pqCredentialProfile.maxAttrs) &&
  DisclosedIndicesValid stmt &&
  stmt.disclosed.all (fun (idx, val) => decide (attrs[idx]? = some val))

/-- What a TOPRF server approves and charges: never the evaluation input. -/
structure ToprfTicket where
  keyId : Bytes
  epoch : Nat
  counter : Nat
  deriving DecidableEq, Repr

/-- A point of the keyed ideal function. -/
structure ToprfPoint where
  keyId : Bytes
  epoch : Nat
  input : Bytes
  deriving DecidableEq, Repr

/-- The interfaces of the functionality. An input arriving on `holder h` or `server i` was sent
    by that honest party; everything the adversary sends arrives on `adversary`. -/
inductive CredPort where
  | issuer
  | holder (id : Nat)
  | server (index : Nat)
  | verifier (id : Nat)
  | client
  | adversary
  deriving DecidableEq, Repr

/-- The parties that can be corrupted. The TOPRF client has no authenticated commands. -/
inductive CredParty where
  | issuer
  | holder (id : Nat)
  | server (index : Nat)
  deriving DecidableEq, Repr

/-- Commands, each attributed to the party it names. -/
inductive CredCommand (Attr : Type) where
  /-- The issuer issues a credential with `attrs` to `holder`, moving the accumulator to `newRoot`. -/
  | issue (holder : Nat) (attrs : List Attr) (newRoot : Digest256)
  /-- The issuer retires the current epoch. -/
  | advanceEpoch (newEpoch : Nat) (newRoot : Digest256)
  /-- `holder` shows credential `credId` for `stmt`. -/
  | present (holder : Nat) (credId : Nat) (stmt : CredentialStatement Attr)
  /-- Only the named verifier can issue into its own ledger. -/
  | advanceClock (verifier now : Nat)
  | issueChallenge (verifier : Nat) (scope : Bytes) (now ttl : Nat)
  /-- TOPRF server `server` approves `ticket`. -/
  | approveToprf (server : Nat) (ticket : ToprfTicket)
  /-- Evaluation request for `input` under `ticket`. -/
  | evalToprf (ticket : ToprfTicket) (input : Bytes)
  /-- The adversary corrupts `party`. -/
  | corrupt (party : CredParty)

/-- The port on which an honest `party` speaks. -/
@[expose] def CredParty.port : CredParty → CredPort
  | .issuer => .issuer
  | .holder h => .holder h
  | .server i => .server i

/-- The party a command is attributed to; evaluation and corruption requests are attributed to
    no party. -/
@[expose] def CredCommand.party {Attr : Type} : CredCommand Attr → Option CredParty
  | .issue _ _ _ => some .issuer
  | .advanceEpoch _ _ => some .issuer
  | .present h _ _ => some (.holder h)
  | .advanceClock _ _ => none
  | .issueChallenge _ _ _ _ => none
  | .approveToprf i _ => some (.server i)
  | .evalToprf _ _ => none
  | .corrupt _ => none

/-- An input is a command together with the port it arrived on. -/
abbrev IdealCredInput (Attr : Type) : Type := CredPort × CredCommand Attr

/-- Outputs emitted by `IdealCred`. -/
inductive IdealCredOutput (O : Type) where
  | issued (credId : Nat)
  | epochAdvanced (epoch : Nat)
  | presentationVerdict (ok : Bool)
  | challengeIssued (nonce : Nat)
  | challengeRefused
  | clockAdvanced
  | toprfApproved
  | toprfEvaluated (out : O)
  | corrupted
  deriving DecidableEq, Repr

/-- Refusal is observable, and unlike a rejected caller port it can carry a pruned successor. -/
def challengeIssueOutput {O : Type} : Option Nat → IdealCredOutput O
  | some nonce => .challengeIssued nonce
  | none => .challengeRefused

/-- Configuration: initial public parameters, the initial corruption set (`issuerCorrupt`,
    `corruptHolders`, `corruptServers`: the parties corrupt before the run starts), the keyed
    ideal function `oprf` and the enrolled per-key evaluation quota (`CounterStore::reserve`,
    `voprf.rs:132`). -/
structure IdealCredConfig (O : Type) where
  issuerPk : Bytes
  epoch₀ : Nat
  root₀ : Digest256
  issuerCorrupt : Bool
  corruptHolders : List Nat
  corruptServers : List Nat
  oprf : ToprfPoint → O
  oprfQuota : Nat
  /-- Each verifier's bound applies across all scopes issued by that instance. -/
  challengeCapacity : Nat → Nat := fun _ => 65536

/-- Number of initially corrupt TOPRF servers among the committee indices. -/
def IdealCredConfig.corruptServerCount {O : Type} (cfg : IdealCredConfig O) : Nat :=
  (List.range pqCredentialProfile.toprfServers).countP (fun i => decide (i ∈ cfg.corruptServers))

/-- An issued credential: its identifier (the holder's capability), owner, attributes, epoch of
    issuance and the accumulator root after it. -/
structure CredentialRecord (Attr : Type) where
  credId : Nat
  holder : Nat
  attrs : List Attr
  epoch : Nat
  root : Digest256

/-! ## 2. State and transition -/

/-- Credential custody and independent verifier ledgers. The holder has no challenge history;
    `issueChallenge` acts on the verifier port and a presentation consumes only the selected
    verifier's outstanding `(scope, nonce)` after all credential checks succeed. -/
structure IdealCredState (Attr O : Type) where
  issuerPk : Bytes
  epoch : Nat
  accumulatorRoot : Digest256
  issuedThisEpoch : Nat
  issuerCorrupt : Bool
  corruptHolders : List Nat
  corruptServers : List Nat
  records : List (CredentialRecord Attr)
  challengeLedgers : VerifierChallengeLedgers
  toprfApprovals : List (Nat × ToprfTicket)
  oprfTable : List (ToprfPoint × O)
  oprfCharges : List ToprfTicket
  /-- Latest clock sample supplied by each authenticated verifier. -/
  verifierTime : Nat → Nat := fun _ => 0

@[expose] def IdealCredState.empty {Attr O : Type} (cfg : IdealCredConfig O) :
    IdealCredState Attr O :=
  { issuerPk := cfg.issuerPk
    epoch := cfg.epoch₀
    accumulatorRoot := cfg.root₀
    issuedThisEpoch := 0
    issuerCorrupt := cfg.issuerCorrupt
    corruptHolders := cfg.corruptHolders
    corruptServers := cfg.corruptServers
    records := []
    challengeLedgers := fun verifier => { capacity := cfg.challengeCapacity verifier }
    toprfApprovals := []
    oprfTable := []
    oprfCharges := [] }

/-- Number of TOPRF servers among the committee indices that are corrupt in `st`. -/
def IdealCredState.corruptServerCount {Attr O : Type} (st : IdealCredState Attr O) : Nat :=
  (List.range pqCredentialProfile.toprfServers).countP (fun i => decide (i ∈ st.corruptServers))

/-- The initial state has the configured corruption set, so its corrupt-server count is the
    configured one. -/
theorem IdealCredState.empty_corruptServerCount {Attr O : Type} (cfg : IdealCredConfig O) :
    (IdealCredState.empty (Attr := Attr) cfg).corruptServerCount = cfg.corruptServerCount := by
  rfl

/-- `party` is in the corruption set of `st`. -/
@[expose] def IdealCredState.isCorrupt {Attr O : Type} (st : IdealCredState Attr O) :
    CredParty → Prop
  | .issuer => st.issuerCorrupt = true
  | .holder h => h ∈ st.corruptHolders
  | .server i => i ∈ st.corruptServers

/-- `st` with `party` added to the corruption set; nothing else changes. -/
@[expose] def IdealCredState.withCorrupt {Attr O : Type} (st : IdealCredState Attr O) :
    CredParty → IdealCredState Attr O
  | .issuer => { st with issuerCorrupt := true }
  | .holder h => { st with corruptHolders := h :: st.corruptHolders }
  | .server i => { st with corruptServers := i :: st.corruptServers }

/-- Every party corrupt in `st` is corrupt in `st'`. -/
structure CredCorruptionLe {Attr O : Type} (st st' : IdealCredState Attr O) : Prop where
  issuer : st.issuerCorrupt = true → st'.issuerCorrupt = true
  holders : ∀ h ∈ st.corruptHolders, h ∈ st'.corruptHolders
  servers : ∀ i ∈ st.corruptServers, i ∈ st'.corruptServers

theorem CredCorruptionLe.refl {Attr O : Type} (st : IdealCredState Attr O) :
    CredCorruptionLe st st :=
  ⟨fun h => h, fun _ h => h, fun _ h => h⟩

theorem CredCorruptionLe.trans {Attr O : Type} {s₁ s₂ s₃ : IdealCredState Attr O}
    (h₁ : CredCorruptionLe s₁ s₂) (h₂ : CredCorruptionLe s₂ s₃) : CredCorruptionLe s₁ s₃ :=
  ⟨fun h => h₂.issuer (h₁.issuer h), fun x h => h₂.holders x (h₁.holders x h),
    fun x h => h₂.servers x (h₁.servers x h)⟩

/-- `CredCorruptionLe` in terms of `IdealCredState.isCorrupt`. -/
theorem CredCorruptionLe.isCorrupt {Attr O : Type} {st st' : IdealCredState Attr O}
    (hLe : CredCorruptionLe st st') (party : CredParty) (h : st.isCorrupt party) :
    st'.isCorrupt party := by
  cases party with
  | issuer => exact hLe.issuer h
  | holder x => exact hLe.holders x h
  | server x => exact hLe.servers x h

/-- Corrupting a party makes it corrupt and keeps every corrupt party corrupt. -/
theorem IdealCredState.withCorrupt_le {Attr O : Type} (st : IdealCredState Attr O)
    (party : CredParty) :
    (st.withCorrupt party).isCorrupt party ∧ CredCorruptionLe st (st.withCorrupt party) := by
  cases party with
  | issuer => exact ⟨rfl, fun _ => rfl, fun _ h => h, fun _ h => h⟩
  | holder x => exact ⟨List.Mem.head _, fun h => h, fun _ h => List.Mem.tail _ h, fun _ h => h⟩
  | server x => exact ⟨List.Mem.head _, fun h => h, fun _ h => h, fun _ h => List.Mem.tail _ h⟩

/-- Port discipline: a command is admitted on the port of the party it is attributed to, or on the
    adversary port when that party is corrupt in `st`. Evaluation requests may come from anyone;
    corruption requests only from the adversary. -/
@[expose] def IdealCredState.speaksFor {Attr O : Type} (st : IdealCredState Attr O)
    (port : CredPort) : CredCommand Attr → Bool
  | .issue _ _ _ => decide (port = .issuer) || (decide (port = .adversary) && st.issuerCorrupt)
  | .advanceEpoch _ _ =>
    decide (port = .issuer) || (decide (port = .adversary) && st.issuerCorrupt)
  | .present h _ _ =>
    decide (port = .holder h) || (decide (port = .adversary) && decide (h ∈ st.corruptHolders))
  | .advanceClock verifier _ => decide (port = .verifier verifier)
  | .issueChallenge verifier _ _ _ => decide (port = .verifier verifier)
  | .approveToprf i _ =>
    decide (port = .server i) || (decide (port = .adversary) && decide (i ∈ st.corruptServers))
  | .evalToprf _ _ => true
  | .corrupt _ => decide (port = .adversary)

/-- Issuance gate: positive arity at most `maxAttrs`, accumulator capacity per epoch. -/
def IdealCredState.issueAccepts {Attr O : Type} (st : IdealCredState Attr O)
    (attrs : List Attr) : Bool :=
  decide (0 < attrs.length) &&
  decide (attrs.length ≤ pqCredentialProfile.maxAttrs) &&
  decide (st.issuedThisEpoch < 2 ^ pqCredentialProfile.accumulatorDepth)

/-- Holder `h` owns a record with identifier `cid`, of the current epoch, satisfying `stmt`. -/
def IdealCredState.eligible {Attr O : Type} [DecidableEq Attr] (st : IdealCredState Attr O)
    (h cid : Nat) (stmt : CredentialStatement Attr) : Bool :=
  st.records.any (fun r =>
    decide (r.credId = cid) && decide (r.holder = h) && decide (r.epoch = st.epoch) &&
      CredentialMatchesAttributes stmt r.attrs)

/-- Presentation gate: current issuer key, epoch and accumulator root, fresh challenge, `eligible`. -/
def IdealCredState.presentAccepts {Attr O : Type} [DecidableEq Attr]
    (st : IdealCredState Attr O) (h cid : Nat) (stmt : CredentialStatement Attr) : Bool :=
  decide (stmt.issuerPk = st.issuerPk) &&
  decide (stmt.epoch = st.epoch) &&
  decide (stmt.accumulatorRoot = st.accumulatorRoot) &&
  (st.challengeLedgers stmt.verifier).accepts stmt.verifierScope stmt.challengeNonce (st.verifierTime stmt.verifier) &&
  st.eligible h cid stmt

/-- Number of distinct committee servers that approved `t`. -/
def IdealCredState.approvalCount {Attr O : Type} (st : IdealCredState Attr O)
    (t : ToprfTicket) : Nat :=
  (List.range pqCredentialProfile.toprfServers).countP
    (fun i => decide ((i, t) ∈ st.toprfApprovals))

/-- Evaluation gate, the conditions under which the `voprf.rs` backend answers:
    * `toprfOnlineServers` distinct servers approved the ticket (four of five online,
      `voprf.rs:4`–`5`);
    * the ticket is for the current epoch and the key has quota left (`voprf.rs:132`);
    * `admit_counter` (`voprf.rs:310`–`326`): the counter exceeds every counter charged to the key
      and is within `toprfCounterWindow` of one of them, or is below the window when none was
      charged; and it is not `u64::MAX = 18446744073709551615`. -/
def IdealCredState.toprfAccepts {Attr O : Type} (st : IdealCredState Attr O)
    (cfg : IdealCredConfig O) (t : ToprfTicket) : Bool :=
  decide (pqCredentialProfile.toprfOnlineServers ≤ st.approvalCount t) &&
  decide (t.epoch = st.epoch) &&
  decide (st.oprfCharges.countP (fun c => decide (c.keyId = t.keyId)) < cfg.oprfQuota) &&
  st.oprfCharges.all (fun c => !decide (c.keyId = t.keyId) || decide (c.counter < t.counter)) &&
  (st.oprfCharges.any (fun c => decide (c.keyId = t.keyId) &&
      decide (t.counter ≤ c.counter + pqCredentialProfile.toprfCounterWindow)) ||
    (!st.oprfCharges.any (fun c => decide (c.keyId = t.keyId)) &&
      decide (t.counter < pqCredentialProfile.toprfCounterWindow))) &&
  decide (t.counter < 18446744073709551615)

/-- A backwards sample cannot extend the lifetime of an outstanding challenge. -/
def advanceVerifierTime (clock : Nat → Nat) (verifier now : Nat) : Nat → Nat :=
  fun v => if v = verifier then max (clock v) now else clock v

/-- Effect of a command once the port discipline admitted it. -/
def credExec {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    (st : IdealCredState Attr O) :
    CredCommand Attr → Option (IdealCredState Attr O × IdealCredOutput O)
  | .issue h attrs newRoot =>
    if st.issueAccepts attrs then
      some ({ st with
              records := st.records ++
                [{ credId := st.records.length, holder := h, attrs := attrs, epoch := st.epoch,
                   root := newRoot }]
              accumulatorRoot := newRoot
              issuedThisEpoch := st.issuedThisEpoch + 1 },
            .issued st.records.length)
    else none
  | .advanceEpoch newEpoch newRoot =>
    if decide (st.epoch < newEpoch) then
      some ({ st with epoch := newEpoch, accumulatorRoot := newRoot, issuedThisEpoch := 0 },
            .epochAdvanced newEpoch)
    else none
  | .present h cid stmt =>
    if st.presentAccepts h cid stmt then
      some ({ st with challengeLedgers := st.challengeLedgers.consume stmt.verifier stmt.verifierScope stmt.challengeNonce },
            .presentationVerdict true)
    else some (st, .presentationVerdict false)
  | .advanceClock verifier now =>
    some ({ st with verifierTime := advanceVerifierTime st.verifierTime verifier now }, .clockAdvanced)
  | .issueChallenge verifier scope now ttl =>
    let attempt := (st.challengeLedgers verifier).issueAttempt scope (max (st.verifierTime verifier) now) ttl
    some ({ st with
                challengeLedgers := st.challengeLedgers.set verifier attempt.1
                verifierTime := advanceVerifierTime st.verifierTime verifier now },
      challengeIssueOutput attempt.2)
  | .approveToprf i t =>
    if decide (i < pqCredentialProfile.toprfServers) && decide (t.epoch = st.epoch) then
      some ({ st with toprfApprovals := (i, t) :: st.toprfApprovals }, .toprfApproved)
    else none
  | .evalToprf t input =>
    if st.toprfAccepts cfg t then
      match st.oprfTable.find? (fun e => decide (e.1 = ⟨t.keyId, t.epoch, input⟩)) with
      | some e =>
        some ({ st with oprfCharges := t :: st.oprfCharges }, .toprfEvaluated e.2)
      | none =>
        some ({ st with
                oprfCharges := t :: st.oprfCharges
                oprfTable := (⟨t.keyId, t.epoch, input⟩, cfg.oprf ⟨t.keyId, t.epoch, input⟩) ::
                  st.oprfTable },
              .toprfEvaluated (cfg.oprf ⟨t.keyId, t.epoch, input⟩))
    else none
  | .corrupt party => some (st.withCorrupt party, .corrupted)

/-- Transition function: inputs violating the port discipline are rejected. -/
@[expose] def idealCredStep {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    (st : IdealCredState Attr O) (inp : IdealCredInput Attr) :
    Option (IdealCredState Attr O × IdealCredOutput O) :=
  if st.speaksFor inp.1 inp.2 then credExec cfg st inp.2 else none

/-- Reactive `Machine` for `IdealCred`, started from `IdealCredState.empty cfg`. -/
@[expose] def idealCredMachine {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O) :
    Machine (IdealCredState Attr O) (IdealCredInput Attr) (IdealCredOutput O) where
  Init st := st = IdealCredState.empty cfg
  step := idealCredStep cfg
  errStep st _ := st

/-! ## 3. Inversion of single transitions -/

section Inversion
variable {Attr O : Type} [DecidableEq Attr] {cfg : IdealCredConfig O}
  {st st' : IdealCredState Attr O} {out : IdealCredOutput O}

/-- An accepted input was admitted by the port discipline and executed. -/
theorem idealCredStep_inv {port : CredPort} {cmd : CredCommand Attr}
    (hStep : idealCredStep cfg st (port, cmd) = some (st', out)) :
    st.speaksFor port cmd = true ∧ credExec cfg st cmd = some (st', out) := by
  have h : (if st.speaksFor port cmd then credExec cfg st cmd else none) = some (st', out) := hStep
  cases hS : st.speaksFor port cmd with
  | false =>
    simp only [hS, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  | true =>
    simp only [hS, ↓reduceIte] at h
    exact ⟨rfl, h⟩

theorem idealCredStep_of_speaksFor {port : CredPort} {cmd : CredCommand Attr}
    (hS : st.speaksFor port cmd = true) :
    idealCredStep cfg st (port, cmd) = credExec cfg st cmd := by
  have h : idealCredStep cfg st (port, cmd) =
      (if st.speaksFor port cmd then credExec cfg st cmd else none) := by rfl
  rw [h, hS]
  simp only [↓reduceIte]

theorem idealCredStep_eq_none_of_not_speaksFor {port : CredPort} {cmd : CredCommand Attr}
    (hS : st.speaksFor port cmd = false) : idealCredStep cfg st (port, cmd) = none := by
  have h : idealCredStep cfg st (port, cmd) =
      (if st.speaksFor port cmd then credExec cfg st cmd else none) := by rfl
  rw [h, hS]
  simp only [Bool.false_eq_true, ↓reduceIte]

theorem idealCredStep_eq_none_of_exec {port : CredPort} {cmd : CredCommand Attr}
    (hE : credExec cfg st cmd = none) : idealCredStep cfg st (port, cmd) = none := by
  cases hS : st.speaksFor port cmd with
  | false => exact idealCredStep_eq_none_of_not_speaksFor hS
  | true => rw [idealCredStep_of_speaksFor hS, hE]

theorem credExec_issue_inv {h : Nat} {attrs : List Attr} {newRoot : Digest256}
    (hExec : credExec cfg st (.issue h attrs newRoot) = some (st', out)) :
    st.issueAccepts attrs = true ∧
    st' = { st with
            records := st.records ++
              [{ credId := st.records.length, holder := h, attrs := attrs, epoch := st.epoch,
                 root := newRoot }]
            accumulatorRoot := newRoot
            issuedThisEpoch := st.issuedThisEpoch + 1 } ∧
    out = .issued st.records.length := by
  cases hC : st.issueAccepts attrs with
  | false =>
    simp only [credExec, hC, Bool.false_eq_true, ↓reduceIte] at hExec
    cases hExec
  | true =>
    simp only [credExec, hC, ↓reduceIte] at hExec
    obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj hExec)
    exact ⟨rfl, hSt.symm, hOut.symm⟩

theorem credExec_advanceEpoch_inv {newEpoch : Nat} {newRoot : Digest256}
    (hExec : credExec cfg st (.advanceEpoch newEpoch newRoot) = some (st', out)) :
    st.epoch < newEpoch ∧
    st' = { st with epoch := newEpoch, accumulatorRoot := newRoot, issuedThisEpoch := 0 } ∧
    out = .epochAdvanced newEpoch := by
  cases hC : decide (st.epoch < newEpoch) with
  | false =>
    simp only [credExec, hC, Bool.false_eq_true, ↓reduceIte] at hExec
    cases hExec
  | true =>
    simp only [credExec, hC, ↓reduceIte] at hExec
    obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj hExec)
    exact ⟨of_decide_eq_true hC, hSt.symm, hOut.symm⟩

/-- A presentation is determined by the presentation gate. -/
theorem credExec_present_eq (cfg : IdealCredConfig O) (st : IdealCredState Attr O)
    (h cid : Nat) (stmt : CredentialStatement Attr) :
    credExec cfg st (.present h cid stmt) =
      some (if st.presentAccepts h cid stmt then
              ({ st with challengeLedgers := st.challengeLedgers.consume stmt.verifier stmt.verifierScope stmt.challengeNonce },
               IdealCredOutput.presentationVerdict true)
            else (st, IdealCredOutput.presentationVerdict false)) := by
  cases hC : st.presentAccepts h cid stmt with
  | false => simp only [credExec, hC, Bool.false_eq_true, ↓reduceIte]
  | true => simp only [credExec, hC, ↓reduceIte]

omit [DecidableEq Attr] in
theorem IdealCredState.issueAccepts_eq (st : IdealCredState Attr O) (attrs : List Attr) :
    st.issueAccepts attrs =
      (decide (0 < attrs.length) &&
       decide (attrs.length ≤ pqCredentialProfile.maxAttrs) &&
       decide (st.issuedThisEpoch < 2 ^ pqCredentialProfile.accumulatorDepth)) := by
  rfl

theorem IdealCredState.eligible_eq (st : IdealCredState Attr O)
    (h cid : Nat) (stmt : CredentialStatement Attr) :
    st.eligible h cid stmt =
      st.records.any (fun r =>
        decide (r.credId = cid) && decide (r.holder = h) && decide (r.epoch = st.epoch) &&
          CredentialMatchesAttributes stmt r.attrs) := by
  rfl

theorem IdealCredState.presentAccepts_eq (st : IdealCredState Attr O)
    (h cid : Nat) (stmt : CredentialStatement Attr) :
    st.presentAccepts h cid stmt =
      (decide (stmt.issuerPk = st.issuerPk) &&
       decide (stmt.epoch = st.epoch) &&
       decide (stmt.accumulatorRoot = st.accumulatorRoot) &&
       (st.challengeLedgers stmt.verifier).accepts stmt.verifierScope stmt.challengeNonce (st.verifierTime stmt.verifier) &&
       st.eligible h cid stmt) := by
  rfl

omit [DecidableEq Attr] in
theorem IdealCredState.approvalCount_eq (st : IdealCredState Attr O) (t : ToprfTicket) :
    st.approvalCount t =
      (List.range pqCredentialProfile.toprfServers).countP
        (fun i => decide ((i, t) ∈ st.toprfApprovals)) := by
  rfl

omit [DecidableEq Attr] in
theorem IdealCredState.toprfAccepts_eq (st : IdealCredState Attr O)
    (cfg : IdealCredConfig O) (t : ToprfTicket) :
    st.toprfAccepts cfg t =
      (decide (pqCredentialProfile.toprfOnlineServers ≤ st.approvalCount t) &&
       decide (t.epoch = st.epoch) &&
       decide (st.oprfCharges.countP (fun c => decide (c.keyId = t.keyId)) < cfg.oprfQuota) &&
       st.oprfCharges.all (fun c => !decide (c.keyId = t.keyId) || decide (c.counter < t.counter)) &&
       (st.oprfCharges.any (fun c => decide (c.keyId = t.keyId) &&
           decide (t.counter ≤ c.counter + pqCredentialProfile.toprfCounterWindow)) ||
         (!st.oprfCharges.any (fun c => decide (c.keyId = t.keyId)) &&
           decide (t.counter < pqCredentialProfile.toprfCounterWindow))) &&
       decide (t.counter < 18446744073709551615)) := by
  rfl

theorem credExec_issue_eq (cfg : IdealCredConfig O) (st : IdealCredState Attr O)
    (h : Nat) (attrs : List Attr) (newRoot : Digest256) :
    credExec cfg st (.issue h attrs newRoot) =
      if st.issueAccepts attrs then
        some ({ st with
                records := st.records ++
                  [{ credId := st.records.length, holder := h, attrs := attrs, epoch := st.epoch,
                     root := newRoot }]
                accumulatorRoot := newRoot
                issuedThisEpoch := st.issuedThisEpoch + 1 },
              .issued st.records.length)
      else none := by
  rfl

theorem credExec_advanceEpoch_eq (cfg : IdealCredConfig O) (st : IdealCredState Attr O)
    (newEpoch : Nat) (newRoot : Digest256) :
    credExec cfg st (.advanceEpoch newEpoch newRoot) =
      if decide (st.epoch < newEpoch) then
        some ({ st with epoch := newEpoch, accumulatorRoot := newRoot, issuedThisEpoch := 0 },
              .epochAdvanced newEpoch)
      else none := by
  rfl

theorem credExec_approveToprf_eq (cfg : IdealCredConfig O) (st : IdealCredState Attr O)
    (i : Nat) (t : ToprfTicket) :
    credExec cfg st (.approveToprf i t) =
      if decide (i < pqCredentialProfile.toprfServers) && decide (t.epoch = st.epoch) then
        some ({ st with toprfApprovals := (i, t) :: st.toprfApprovals }, .toprfApproved)
      else none := by
  rfl

theorem credExec_evalToprf_eq (cfg : IdealCredConfig O) (st : IdealCredState Attr O)
    (t : ToprfTicket) (input : Bytes) :
    credExec cfg st (.evalToprf t input) =
      if st.toprfAccepts cfg t then
        match st.oprfTable.find? (fun e => decide (e.1 = ⟨t.keyId, t.epoch, input⟩)) with
        | some e =>
          some ({ st with oprfCharges := t :: st.oprfCharges }, .toprfEvaluated e.2)
        | none =>
          some ({ st with
                  oprfCharges := t :: st.oprfCharges
                  oprfTable := (⟨t.keyId, t.epoch, input⟩, cfg.oprf ⟨t.keyId, t.epoch, input⟩) ::
                    st.oprfTable },
                .toprfEvaluated (cfg.oprf ⟨t.keyId, t.epoch, input⟩))
      else none := by
  rfl

theorem credExec_present_true_inv {h cid : Nat} {stmt : CredentialStatement Attr}
    (hExec : credExec cfg st (.present h cid stmt) = some (st', .presentationVerdict true)) :
    st.presentAccepts h cid stmt = true ∧
    st' = { st with challengeLedgers := st.challengeLedgers.consume stmt.verifier stmt.verifierScope stmt.challengeNonce } := by
  rw [credExec_present_eq] at hExec
  cases hC : st.presentAccepts h cid stmt with
  | false =>
    simp only [hC, Bool.false_eq_true, ↓reduceIte] at hExec
    obtain ⟨_, hOut⟩ := Prod.mk.inj (Option.some.inj hExec)
    cases hOut
  | true =>
    simp only [hC, ↓reduceIte] at hExec
    obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hExec)
    exact ⟨rfl, hSt.symm⟩

theorem credExec_issueChallenge_eq (cfg : IdealCredConfig O) (st : IdealCredState Attr O)
    (verifier : Nat) (scope : Bytes) (now ttl : Nat) :
    credExec cfg st (.issueChallenge verifier scope now ttl) =
      let attempt := (st.challengeLedgers verifier).issueAttempt scope (max (st.verifierTime verifier) now) ttl
      some ({ st with
                challengeLedgers := st.challengeLedgers.set verifier attempt.1
                verifierTime := advanceVerifierTime st.verifierTime verifier now },
        challengeIssueOutput attempt.2) := by
  rfl

theorem credExec_issueChallenge_inv {verifier : Nat} {scope : Bytes} {now ttl : Nat}
    (hExec : credExec cfg st (.issueChallenge verifier scope now ttl) = some (st', out)) :
    ∃ l result, (st.challengeLedgers verifier).issueAttempt scope (max (st.verifierTime verifier) now) ttl = (l, result) ∧
      st' = { st with
                challengeLedgers := st.challengeLedgers.set verifier l
                verifierTime := advanceVerifierTime st.verifierTime verifier now } ∧
      out = challengeIssueOutput result := by
  simp only [credExec] at hExec
  obtain ⟨hs, ho⟩ := Prod.mk.inj (Option.some.inj hExec)
  exact ⟨_, _, rfl, hs.symm, ho.symm⟩

theorem credExec_approveToprf_inv {i : Nat} {t : ToprfTicket}
    (hExec : credExec cfg st (.approveToprf i t) = some (st', out)) :
    i < pqCredentialProfile.toprfServers ∧ t.epoch = st.epoch ∧
    st' = { st with toprfApprovals := (i, t) :: st.toprfApprovals } ∧
    out = .toprfApproved := by
  cases hC : (decide (i < pqCredentialProfile.toprfServers) && decide (t.epoch = st.epoch)) with
  | false =>
    simp only [credExec, hC, Bool.false_eq_true, ↓reduceIte] at hExec
    cases hExec
  | true =>
    simp only [credExec, hC, ↓reduceIte] at hExec
    obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj hExec)
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hC
    exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, hSt.symm, hOut.symm⟩

theorem credExec_evalToprf_inv {t : ToprfTicket} {input : Bytes}
    (hExec : credExec cfg st (.evalToprf t input) = some (st', out)) :
    st.toprfAccepts cfg t = true ∧
    ((∃ o : O, ((⟨t.keyId, t.epoch, input⟩ : ToprfPoint), o) ∈ st.oprfTable ∧
        st' = { st with oprfCharges := t :: st.oprfCharges } ∧ out = .toprfEvaluated o) ∨
     (st' = { st with
              oprfCharges := t :: st.oprfCharges
              oprfTable := (⟨t.keyId, t.epoch, input⟩, cfg.oprf ⟨t.keyId, t.epoch, input⟩) ::
                st.oprfTable } ∧
      out = .toprfEvaluated (cfg.oprf ⟨t.keyId, t.epoch, input⟩))) := by
  cases hC : st.toprfAccepts cfg t with
  | false =>
    simp only [credExec, hC, Bool.false_eq_true, ↓reduceIte] at hExec
    cases hExec
  | true =>
    simp only [credExec, hC, ↓reduceIte] at hExec
    refine ⟨rfl, ?_⟩
    cases hF : st.oprfTable.find? (fun e => decide (e.1 = ⟨t.keyId, t.epoch, input⟩)) with
    | some e =>
      rw [hF] at hExec
      obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj hExec)
      have hDec : decide (e.1 = (⟨t.keyId, t.epoch, input⟩ : ToprfPoint)) = true :=
        List.find?_some
          (p := fun e : ToprfPoint × O =>
            decide (e.1 = (⟨t.keyId, t.epoch, input⟩ : ToprfPoint))) hF
      have hKey : e.1 = ⟨t.keyId, t.epoch, input⟩ := of_decide_eq_true hDec
      have hMem : e ∈ st.oprfTable := List.mem_of_find?_eq_some hF
      refine Or.inl ⟨e.2, ?_, hSt.symm, hOut.symm⟩
      rw [← hKey]
      exact hMem
    | none =>
      rw [hF] at hExec
      obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj hExec)
      exact Or.inr ⟨hSt.symm, hOut.symm⟩

theorem credExec_corrupt_inv {party : CredParty}
    (hExec : credExec cfg st (.corrupt party) = some (st', out)) :
    st' = st.withCorrupt party ∧ out = .corrupted := by
  have h : some (st.withCorrupt party, IdealCredOutput.corrupted) = some (st', out) := hExec
  obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hSt.symm, hOut.symm⟩

/-- A corruption request on the adversary port is always answered, with the party added to the
    corruption set. -/
theorem idealCredStep_corrupt_eq (cfg : IdealCredConfig O) (st : IdealCredState Attr O)
    (party : CredParty) :
    idealCredStep cfg st (.adversary, .corrupt party) =
      some (st.withCorrupt party, .corrupted) := by
  have hS : st.speaksFor .adversary (CredCommand.corrupt (Attr := Attr) party) = true := by
    simp only [IdealCredState.speaksFor, decide_true]
  rw [idealCredStep_of_speaksFor hS]
  rfl

/-- The output of an accepted input determines the kind of command that produced it. -/
theorem idealCredStep_output_command {port : CredPort} {cmd : CredCommand Attr}
    (hStep : idealCredStep cfg st (port, cmd) = some (st', out)) :
    match out with
    | .issued _ => ∃ h attrs newRoot, cmd = .issue h attrs newRoot
    | .epochAdvanced _ => ∃ newEpoch newRoot, cmd = .advanceEpoch newEpoch newRoot
    | .presentationVerdict _ => ∃ h cid stmt, cmd = .present h cid stmt
    | .challengeIssued _ => ∃ verifier scope now ttl, cmd = .issueChallenge verifier scope now ttl
    | .clockAdvanced => ∃ verifier now, cmd = .advanceClock verifier now
    | .challengeRefused => ∃ verifier scope now ttl, cmd = .issueChallenge verifier scope now ttl
    | .toprfApproved => ∃ i t, cmd = .approveToprf i t
    | .toprfEvaluated _ => ∃ t input, cmd = .evalToprf t input
    | .corrupted => ∃ party, cmd = .corrupt party := by
  have hExec := (idealCredStep_inv hStep).2
  cases cmd with
  | advanceClock verifier now =>
    change some (_, IdealCredOutput.clockAdvanced) = some (st', out) at hExec
    cases hExec
    exact ⟨verifier, now, rfl⟩
  | issueChallenge verifier scope now ttl =>
    obtain ⟨_, result, _, _, hOut⟩ := credExec_issueChallenge_inv hExec
    subst hOut
    cases result <;> exact ⟨verifier, scope, now, ttl, rfl⟩
  | issue h attrs newRoot =>
    obtain ⟨_, _, hOut⟩ := credExec_issue_inv hExec
    subst hOut
    exact ⟨h, attrs, newRoot, rfl⟩
  | advanceEpoch newEpoch newRoot =>
    obtain ⟨_, _, hOut⟩ := credExec_advanceEpoch_inv hExec
    subst hOut
    exact ⟨newEpoch, newRoot, rfl⟩
  | present h cid stmt =>
    rw [credExec_present_eq] at hExec
    cases hC : st.presentAccepts h cid stmt with
    | false =>
      simp only [hC, Bool.false_eq_true, ↓reduceIte] at hExec
      obtain ⟨_, hOut⟩ := Prod.mk.inj (Option.some.inj hExec)
      subst hOut
      exact ⟨h, cid, stmt, rfl⟩
    | true =>
      simp only [hC, ↓reduceIte] at hExec
      obtain ⟨_, hOut⟩ := Prod.mk.inj (Option.some.inj hExec)
      subst hOut
      exact ⟨h, cid, stmt, rfl⟩
  | approveToprf i t =>
    obtain ⟨_, _, _, hOut⟩ := credExec_approveToprf_inv hExec
    subst hOut
    exact ⟨i, t, rfl⟩
  | evalToprf t input =>
    obtain ⟨_, hCase⟩ := credExec_evalToprf_inv hExec
    rcases hCase with ⟨o, _, _, hOut⟩ | ⟨_, hOut⟩
    · subst hOut
      exact ⟨t, input, rfl⟩
    · subst hOut
      exact ⟨t, input, rfl⟩
  | corrupt party =>
    obtain ⟨_, hOut⟩ := credExec_corrupt_inv hExec
    subst hOut
    exact ⟨party, rfl⟩

/-- In the initial state an issuer-port issuance of a one-attribute credential is answered with
    identifier `0`. -/
theorem idealCredStep_issuer_issues_at_init (cfg : IdealCredConfig O) (h : Nat) (a : Attr)
    (newRoot : Digest256) :
    (idealCredStep cfg (IdealCredState.empty cfg) (.issuer, .issue h [a] newRoot)).map Prod.snd =
      some (.issued 0) := by
  have hS : (IdealCredState.empty (Attr := Attr) cfg).speaksFor .issuer (.issue h [a] newRoot) =
      true := by
    simp only [IdealCredState.speaksFor, decide_true, Bool.true_or]
  have hAcc : (IdealCredState.empty (Attr := Attr) cfg).issueAccepts [a] = true := by rfl
  rw [idealCredStep_of_speaksFor hS]
  simp only [credExec, hAcc, ↓reduceIte]
  rfl

end Inversion

/-- The actual machine makes only lawful ledger changes, independently at each verifier. -/
theorem credExec_ledger_evolution {Attr O : Type} [DecidableEq Attr]
    {cfg : IdealCredConfig O} {st st' : IdealCredState Attr O}
    {cmd : CredCommand Attr} {out : IdealCredOutput O}
    (hs : credExec cfg st cmd = some (st', out)) (scope : Nat) :
    VerifierLedgerEvolution (st.challengeLedgers scope) (st'.challengeLedgers scope) := by
  cases cmd with
  | advanceClock verifier now =>
    change some (_, IdealCredOutput.clockAdvanced) = some (st', out) at hs
    cases hs
    exact .refl _
  | issueChallenge target issueScope now ttl =>
    obtain ⟨l, n, hi, hst, _⟩ := credExec_issueChallenge_inv hs
    subst hst
    by_cases he : scope = target
    · subst scope
      have hev := (st.challengeLedgers target).issueAttempt_evolution issueScope (max (st.verifierTime target) now) ttl
      rw [hi] at hev
      simpa only [VerifierChallengeLedgers.set, ↓reduceIte] using
        hev
    · simp only [VerifierChallengeLedgers.set, he, ↓reduceIte]
      exact .refl _
  | present h cid stmt =>
    rw [credExec_present_eq] at hs
    cases ha : st.presentAccepts h cid stmt <;>
      simp only [ha, Bool.false_eq_true, ↓reduceIte] at hs
    · have hst := (Prod.mk.inj (Option.some.inj hs)).1
      rw [← hst]
      exact .refl _
    · have hst := (Prod.mk.inj (Option.some.inj hs)).1
      rw [← hst]
      by_cases he : scope = stmt.verifier
      · simp only [VerifierChallengeLedgers.consume, VerifierChallengeLedgers.set,
          he, ↓reduceIte]
        exact .consume _ _ _
      · simp only [VerifierChallengeLedgers.consume, VerifierChallengeLedgers.set,
          he, ↓reduceIte]
        exact .refl _
  | issue h attrs root =>
    obtain ⟨_, hst, _⟩ := credExec_issue_inv hs
    subst hst
    exact .refl _
  | advanceEpoch epoch root =>
    obtain ⟨_, hst, _⟩ := credExec_advanceEpoch_inv hs
    subst hst
    exact .refl _
  | approveToprf i t =>
    obtain ⟨_, _, hst, _⟩ := credExec_approveToprf_inv hs
    subst hst
    exact .refl _
  | evalToprf t input =>
    obtain ⟨_, hcase⟩ := credExec_evalToprf_inv hs
    rcases hcase with ⟨_, _, hst, _⟩ | ⟨hst, _⟩ <;> subst hst <;> exact .refl _
  | corrupt party =>
    obtain ⟨hst, _⟩ := credExec_corrupt_inv hs
    subst hst
    cases party <;> exact .refl _

theorem idealCredMachine_ledger_evolution {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (ht : (idealCredMachine cfg).ValidTrace st tr st') (scope : Nat) :
    VerifierLedgerEvolution (st.challengeLedgers scope) (st'.challengeLedgers scope) := by
  induction ht with
  | nil => exact .refl _
  | accept hs _ ih => exact .trans (credExec_ledger_evolution (idealCredStep_inv hs).2 scope) ih
  | reject _ _ _ ih => exact ih

theorem idealCredMachine_ledger_wellFormed {Attr O : Type} [DecidableEq Attr]
    {cfg : IdealCredConfig O} {st : IdealCredState Attr O}
    (hr : (idealCredMachine cfg).Reachable st) (scope : Nat) :
    (st.challengeLedgers scope).WellFormed := by
  obtain ⟨s, tr, hi, ht⟩ := hr
  have he : s = IdealCredState.empty cfg := hi
  subst s
  exact (idealCredMachine_ledger_evolution cfg ht scope).wellFormed (fun _ h => nomatch h)

/-! ## 4. Reachable-state invariant -/

/-- Invariant of every reachable state: the issuer key is that of the configuration; every party
    of the configured initial corruption set is corrupt; every record has between `1` and
    `maxAttrs` attributes and an epoch not after the current one; every revealed TOPRF value is the value of `oprf`; per key, no more points
    are revealed than tickets charged, no more tickets charged than the quota, and charged
    counters strictly increase. -/
structure IdealCredInv {Attr O : Type} (cfg : IdealCredConfig O)
    (st : IdealCredState Attr O) : Prop where
  issuerPk_eq : st.issuerPk = cfg.issuerPk
  issuerCorrupt_of_cfg : cfg.issuerCorrupt = true → st.issuerCorrupt = true
  corruptHolders_of_cfg : ∀ h ∈ cfg.corruptHolders, h ∈ st.corruptHolders
  corruptServers_of_cfg : ∀ i ∈ cfg.corruptServers, i ∈ st.corruptServers
  records_wf : ∀ r ∈ st.records,
    0 < r.attrs.length ∧ r.attrs.length ≤ pqCredentialProfile.maxAttrs ∧ r.epoch ≤ st.epoch
  table_graph : ∀ e ∈ st.oprfTable, e.2 = cfg.oprf e.1
  table_charged : ∀ k : Bytes,
    st.oprfTable.countP (fun e => decide (e.1.keyId = k)) ≤
      st.oprfCharges.countP (fun c => decide (c.keyId = k))
  charges_budget : ∀ k : Bytes,
    st.oprfCharges.countP (fun c => decide (c.keyId = k)) ≤ cfg.oprfQuota
  charges_fresh : st.oprfCharges.Pairwise
    (fun newer older => newer.keyId = older.keyId → older.counter < newer.counter)

private theorem credCountP_cons_congr {α β : Type} (p : α → Bool) (q : β → Bool) (a : α) (b : β)
    (l : List α) (m : List β) (hab : p a = q b) (h : l.countP p ≤ m.countP q) :
    (a :: l).countP p ≤ (b :: m).countP q := by
  rw [List.countP_cons, List.countP_cons, hab]
  exact Nat.add_le_add_right h _

private theorem credCountP_le_cons {β : Type} (q : β → Bool) (b : β) (m : List β) (n : Nat)
    (h : n ≤ m.countP q) : n ≤ (b :: m).countP q := by
  rw [List.countP_cons]
  exact Nat.le_trans h (Nat.le_add_right _ _)

private theorem credCountP_cons_le_of_lt {β : Type} (q : β → Bool) (b : β) (m : List β) (n : Nat)
    (h : m.countP q < n) : (b :: m).countP q ≤ n := by
  rw [List.countP_cons]
  cases q b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact Nat.le_of_lt h
  | true =>
    simp only [↓reduceIte]
    exact h

private theorem credCountP_cons_of_false {β : Type} (q : β → Bool) (b : β) (m : List β)
    (hb : q b = false) : (b :: m).countP q = m.countP q := by
  rw [List.countP_cons, hb]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

/-- If `p` holds more often than `q` on a list, some element satisfies `p` and not `q`. -/
private theorem credExists_of_countP_lt {α : Type} (p q : α → Bool) :
    ∀ l : List α, l.countP q < l.countP p → ∃ a ∈ l, p a = true ∧ q a = false := by
  intro l
  induction l with
  | nil =>
    intro h
    simp only [List.countP_nil] at h
    exact absurd h (Nat.lt_irrefl 0)
  | cons a l ih =>
    intro h
    rw [List.countP_cons, List.countP_cons] at h
    cases hp : p a with
    | true =>
      cases hq : q a with
      | false => exact ⟨a, List.Mem.head _, hp, hq⟩
      | true =>
        simp only [hp, hq, ↓reduceIte] at h
        obtain ⟨b, hb, hpb, hqb⟩ := ih (Nat.lt_of_succ_lt_succ h)
        exact ⟨b, List.Mem.tail _ hb, hpb, hqb⟩
    | false =>
      cases hq : q a with
      | false =>
        simp only [hp, hq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
        obtain ⟨b, hb, hpb, hqb⟩ := ih h
        exact ⟨b, List.Mem.tail _ hb, hpb, hqb⟩
      | true =>
        simp only [hp, hq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
        obtain ⟨b, hb, hpb, hqb⟩ := ih (Nat.lt_of_succ_lt h)
        exact ⟨b, List.Mem.tail _ hb, hpb, hqb⟩

private theorem idealCredInv_toprf_charge {Attr O : Type} {cfg : IdealCredConfig O}
    {st : IdealCredState Attr O} {t : ToprfTicket}
    (hInv : IdealCredInv cfg st) (hAcc : st.toprfAccepts cfg t = true) :
    (∀ k : Bytes, (t :: st.oprfCharges).countP (fun c => decide (c.keyId = k)) ≤ cfg.oprfQuota) ∧
    (t :: st.oprfCharges).Pairwise
      (fun newer older => newer.keyId = older.keyId → older.counter < newer.counter) := by
  simp only [IdealCredState.toprfAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
  obtain ⟨⟨⟨⟨_, hQuota⟩, hFresh⟩, _⟩, _⟩ := hAcc
  refine ⟨fun k => ?_, List.pairwise_cons.mpr ⟨fun c hc hk => ?_, hInv.charges_fresh⟩⟩
  · by_cases hk : t.keyId = k
    · rw [← hk]
      exact credCountP_cons_le_of_lt _ t _ _ hQuota
    · rw [credCountP_cons_of_false _ t _ (decide_eq_false hk)]
      exact hInv.charges_budget k
  · have h := List.all_eq_true.mp hFresh c hc
    rw [decide_eq_true hk.symm] at h
    exact of_decide_eq_true h

/-- Every executed command preserves `IdealCredInv`. -/
theorem idealCredInv_exec {Attr O : Type} [DecidableEq Attr] {cfg : IdealCredConfig O}
    {st st' : IdealCredState Attr O} {cmd : CredCommand Attr} {out : IdealCredOutput O}
    (hInv : IdealCredInv cfg st) (hExec : credExec cfg st cmd = some (st', out)) :
    IdealCredInv cfg st' := by
  cases cmd with
  | advanceClock verifier now =>
    change some (_, IdealCredOutput.clockAdvanced) = some (st', out) at hExec
    cases hExec
    exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg, hInv.corruptHolders_of_cfg,
      hInv.corruptServers_of_cfg, hInv.records_wf, hInv.table_graph, hInv.table_charged,
      hInv.charges_budget, hInv.charges_fresh⟩
  | issueChallenge verifier scope now ttl =>
    obtain ⟨_, _, _, hSt, _⟩ := credExec_issueChallenge_inv hExec
    subst hSt
    exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg, hInv.corruptHolders_of_cfg,
      hInv.corruptServers_of_cfg, hInv.records_wf, hInv.table_graph, hInv.table_charged,
      hInv.charges_budget, hInv.charges_fresh⟩
  | issue h attrs newRoot =>
    obtain ⟨hAcc, hSt, _⟩ := credExec_issue_inv hExec
    simp only [IdealCredState.issueAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
    obtain ⟨⟨hPos, hMax⟩, _⟩ := hAcc
    subst hSt
    refine ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg, hInv.corruptHolders_of_cfg,
      hInv.corruptServers_of_cfg, fun r hr => ?_, hInv.table_graph, hInv.table_charged,
      hInv.charges_budget, hInv.charges_fresh⟩
    rcases List.mem_append.mp hr with hOld | hNew
    · exact hInv.records_wf r hOld
    · rw [List.mem_singleton.mp hNew]
      exact ⟨hPos, hMax, Nat.le_refl _⟩
  | advanceEpoch newEpoch newRoot =>
    obtain ⟨hLt, hSt, _⟩ := credExec_advanceEpoch_inv hExec
    subst hSt
    refine ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg, hInv.corruptHolders_of_cfg,
      hInv.corruptServers_of_cfg, fun r hr => ?_, hInv.table_graph, hInv.table_charged,
      hInv.charges_budget, hInv.charges_fresh⟩
    obtain ⟨hPos, hMax, hEp⟩ := hInv.records_wf r hr
    exact ⟨hPos, hMax, Nat.le_trans hEp (Nat.le_of_lt hLt)⟩
  | present h cid stmt =>
    rw [credExec_present_eq] at hExec
    cases hC : st.presentAccepts h cid stmt with
    | false =>
      simp only [hC, Bool.false_eq_true, ↓reduceIte] at hExec
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hExec)
      rw [← hSt]
      exact hInv
    | true =>
      simp only [hC, ↓reduceIte] at hExec
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hExec)
      rw [← hSt]
      exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg, hInv.corruptHolders_of_cfg,
        hInv.corruptServers_of_cfg, hInv.records_wf, hInv.table_graph, hInv.table_charged,
        hInv.charges_budget, hInv.charges_fresh⟩
  | approveToprf i t =>
    obtain ⟨_, _, hSt, _⟩ := credExec_approveToprf_inv hExec
    subst hSt
    exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg, hInv.corruptHolders_of_cfg,
      hInv.corruptServers_of_cfg, hInv.records_wf, hInv.table_graph, hInv.table_charged,
      hInv.charges_budget, hInv.charges_fresh⟩
  | evalToprf t input =>
    obtain ⟨hAcc, hCase⟩ := credExec_evalToprf_inv hExec
    obtain ⟨hBudget, hFresh⟩ := idealCredInv_toprf_charge hInv hAcc
    rcases hCase with ⟨o, _, hSt, _⟩ | ⟨hSt, _⟩
    · subst hSt
      exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg, hInv.corruptHolders_of_cfg,
        hInv.corruptServers_of_cfg, hInv.records_wf, hInv.table_graph,
        fun k => credCountP_le_cons _ t _ _ (hInv.table_charged k), hBudget, hFresh⟩
    · subst hSt
      refine ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg, hInv.corruptHolders_of_cfg,
        hInv.corruptServers_of_cfg, hInv.records_wf, fun e he => ?_,
        fun k => credCountP_cons_congr _ _ _ t _ _ rfl (hInv.table_charged k), hBudget, hFresh⟩
      rcases List.mem_cons.mp he with hNew | hOld
      · rw [hNew]
      · exact hInv.table_graph e hOld
  | corrupt party =>
    obtain ⟨hSt, _⟩ := credExec_corrupt_inv hExec
    subst hSt
    cases party with
    | issuer =>
      exact ⟨hInv.issuerPk_eq, fun _ => rfl, hInv.corruptHolders_of_cfg,
        hInv.corruptServers_of_cfg, hInv.records_wf, hInv.table_graph, hInv.table_charged,
        hInv.charges_budget, hInv.charges_fresh⟩
    | holder x =>
      exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg,
        fun h hh => List.Mem.tail _ (hInv.corruptHolders_of_cfg h hh),
        hInv.corruptServers_of_cfg, hInv.records_wf, hInv.table_graph, hInv.table_charged,
        hInv.charges_budget, hInv.charges_fresh⟩
    | server x =>
      exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_of_cfg, hInv.corruptHolders_of_cfg,
        fun i hi => List.Mem.tail _ (hInv.corruptServers_of_cfg i hi), hInv.records_wf,
        hInv.table_graph, hInv.table_charged, hInv.charges_budget, hInv.charges_fresh⟩

/-- `IdealCredInv` holds in every reachable state. -/
theorem idealCredInv_reachable {Attr O : Type} [DecidableEq Attr] {cfg : IdealCredConfig O}
    {st : IdealCredState Attr O}
    (hReach : (idealCredMachine (Attr := Attr) cfg).Reachable st) : IdealCredInv cfg st := by
  obtain ⟨s₀, tr, hInit, hTr⟩ := hReach
  have h₀ : IdealCredInv cfg s₀ := by
    have hEq : s₀ = IdealCredState.empty cfg := hInit
    rw [hEq]
    exact ⟨rfl, (fun h => h), (fun _ h => h), (fun _ h => h), (fun _ hr => nomatch hr), (fun _ he => nomatch he),
      (fun _ => Nat.le_refl _), (fun _ => Nat.zero_le _), List.Pairwise.nil⟩
  clear hInit
  induction hTr with
  | nil _ => exact h₀
  | @accept s s' sf inp out rest hStep _ ih =>
    obtain ⟨port, cmd⟩ := inp
    exact ih (idealCredInv_exec h₀ (idealCredStep_inv hStep).2)
  | reject _ _ _ ih => exact ih h₀

/-! ## 5. Provenance over traces -/

private theorem credCorruptionLe_of_eq {Attr O : Type} {st st' : IdealCredState Attr O}
    (hI : st'.issuerCorrupt = st.issuerCorrupt) (hH : st'.corruptHolders = st.corruptHolders)
    (hS : st'.corruptServers = st.corruptServers) : CredCorruptionLe st st' :=
  ⟨fun h => hI.trans h, fun _ h => by rw [hH]; exact h, fun _ h => by rw [hS]; exact h⟩

/-- **Port discipline of one accepted input.** A command attributed to `party` arrived on the
    port of `party`, or on the adversary port in a state where `party` is corrupt. -/
theorem idealCredStep_attributed {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    {st st' : IdealCredState Attr O} {port : CredPort} {cmd : CredCommand Attr}
    {out : IdealCredOutput O} {party : CredParty}
    (hStep : idealCredStep cfg st (port, cmd) = some (st', out))
    (hParty : cmd.party = some party) :
    port = party.port ∨ (port = CredPort.adversary ∧ st.isCorrupt party) := by
  have hSpeak := (idealCredStep_inv hStep).1
  cases cmd with
  | advanceClock verifier now =>
    exact nomatch hParty
  | issueChallenge verifier scope now ttl =>
    have hP : (none : Option CredParty) = some party := hParty
    exact nomatch hP
  | issue h attrs newRoot =>
    have hP : CredParty.issuer = party := Option.some.inj hParty
    subst hP
    simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hSpeak
    exact hSpeak
  | advanceEpoch newEpoch newRoot =>
    have hP : CredParty.issuer = party := Option.some.inj hParty
    subst hP
    simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hSpeak
    exact hSpeak
  | present h cid stmt =>
    have hP : CredParty.holder h = party := Option.some.inj hParty
    subst hP
    simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hSpeak
    exact hSpeak
  | approveToprf i t =>
    have hP : CredParty.server i = party := Option.some.inj hParty
    subst hP
    simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hSpeak
    exact hSpeak
  | evalToprf t input =>
    have hP : (none : Option CredParty) = some party := hParty
    exact nomatch hP
  | corrupt p =>
    have hP : (none : Option CredParty) = some party := hParty
    exact nomatch hP

/-- One accepted input: the corruption set only grows; a new record comes from this very input
    being an issuance, on the issuer port or on the adversary port with the issuer corrupt in
    `st`; a new approval comes from this very input being an approval, on that server's port or on
    the adversary port with the server corrupt in `st`. -/
theorem idealCredStep_provenance {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    {st st' : IdealCredState Attr O} {inp : IdealCredInput Attr} {out : IdealCredOutput O}
    (hStep : idealCredStep cfg st inp = some (st', out)) :
    CredCorruptionLe st st' ∧
    (∀ r ∈ st'.records, r ∈ st.records ∨
      ∃ port : CredPort,
        (inp, out) = ((port, CredCommand.issue r.holder r.attrs r.root),
          IdealCredOutput.issued r.credId) ∧
        (port = CredPort.issuer ∨ (port = CredPort.adversary ∧ st.issuerCorrupt = true))) ∧
    (∀ a ∈ st'.toprfApprovals, a ∈ st.toprfApprovals ∨
      ∃ port : CredPort,
        (inp, out) = ((port, CredCommand.approveToprf a.1 a.2),
          IdealCredOutput.toprfApproved) ∧
        (port = CredPort.server a.1 ∨
          (port = CredPort.adversary ∧ a.1 ∈ st.corruptServers))) := by
  obtain ⟨port, cmd⟩ := inp
  obtain ⟨hSpeak, hExec⟩ := idealCredStep_inv hStep
  cases cmd with
  | advanceClock verifier now =>
    change some (_, IdealCredOutput.clockAdvanced) = some (st', out) at hExec
    cases hExec
    exact ⟨credCorruptionLe_of_eq rfl rfl rfl, fun _ hr => Or.inl hr, fun _ ha => Or.inl ha⟩
  | issueChallenge verifier scope now ttl =>
    obtain ⟨_, _, _, hSt, _⟩ := credExec_issueChallenge_inv hExec
    subst hSt
    exact ⟨credCorruptionLe_of_eq rfl rfl rfl, fun _ hr => Or.inl hr, fun _ ha => Or.inl ha⟩
  | issue h attrs newRoot =>
    obtain ⟨_, hSt, hOut⟩ := credExec_issue_inv hExec
    simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hSpeak
    subst hSt
    subst hOut
    refine ⟨credCorruptionLe_of_eq rfl rfl rfl, fun r hr => ?_, fun a ha => Or.inl ha⟩
    rcases List.mem_append.mp hr with hOld | hNew
    · exact Or.inl hOld
    · have hR := List.mem_singleton.mp hNew
      subst hR
      exact Or.inr ⟨port, rfl, hSpeak⟩
  | advanceEpoch newEpoch newRoot =>
    obtain ⟨_, hSt, _⟩ := credExec_advanceEpoch_inv hExec
    subst hSt
    exact ⟨credCorruptionLe_of_eq rfl rfl rfl, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
  | present h cid stmt =>
    rw [credExec_present_eq] at hExec
    cases hC : st.presentAccepts h cid stmt with
    | false =>
      simp only [hC, Bool.false_eq_true, ↓reduceIte] at hExec
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hExec)
      subst hSt
      exact ⟨CredCorruptionLe.refl _, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
    | true =>
      simp only [hC, ↓reduceIte] at hExec
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hExec)
      subst hSt
      exact ⟨credCorruptionLe_of_eq rfl rfl rfl, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
  | approveToprf i t =>
    obtain ⟨_, _, hSt, hOut⟩ := credExec_approveToprf_inv hExec
    simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hSpeak
    subst hSt
    subst hOut
    refine ⟨credCorruptionLe_of_eq rfl rfl rfl, fun r hr => Or.inl hr, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with hNew | hOld
    · subst hNew
      exact Or.inr ⟨port, rfl, hSpeak⟩
    · exact Or.inl hOld
  | evalToprf t input =>
    obtain ⟨_, hCase⟩ := credExec_evalToprf_inv hExec
    rcases hCase with ⟨o, _, hSt, _⟩ | ⟨hSt, _⟩
    · subst hSt
      exact ⟨credCorruptionLe_of_eq rfl rfl rfl, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
    · subst hSt
      exact ⟨credCorruptionLe_of_eq rfl rfl rfl, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
  | corrupt party =>
    obtain ⟨hSt, _⟩ := credExec_corrupt_inv hExec
    subst hSt
    refine ⟨(st.withCorrupt_le party).2, fun r hr => Or.inl ?_, fun a ha => Or.inl ?_⟩
    · cases party <;> exact hr
    · cases party <;> exact ha

/-- **Corruption is monotone along a run**: every party corrupt at the start is corrupt at the
    end. -/
theorem idealCred_trace_corruption_monotone {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (hTr : (idealCredMachine cfg).ValidTrace s tr st) : CredCorruptionLe s st := by
  induction hTr with
  | nil _ => exact CredCorruptionLe.refl _
  | @accept s s' sf inp out rest hStep _ ih =>
    exact (idealCredStep_provenance cfg hStep).1.trans ih
  | reject _ _ _ ih => exact ih

/-- The run `tr` from `s` to `st` processed the accepted event `ev` in state `sAt`: the run splits
    as a run from `s` to `sAt`, the step answering `ev`, and a run to `st`. -/
inductive CredEventAt {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    (s : IdealCredState Attr O) (tr : List (IdealCredInput Attr × IdealCredOutput O))
    (st sAt : IdealCredState Attr O) (ev : IdealCredInput Attr × IdealCredOutput O) : Prop where
  | intro (pre post : List (IdealCredInput Attr × IdealCredOutput O))
      (sNext : IdealCredState Attr O)
      (hSplit : tr = pre ++ ev :: post)
      (hPre : (idealCredMachine cfg).ValidTrace s pre sAt)
      (hStep : (idealCredMachine cfg).step sAt ev.1 = some (sNext, ev.2))
      (hPost : (idealCredMachine cfg).ValidTrace sNext post st) :
      CredEventAt cfg s tr st sAt ev

section EventAt
variable {Attr O : Type} [DecidableEq Attr] {cfg : IdealCredConfig O}
  {s st sAt : IdealCredState Attr O} {tr : List (IdealCredInput Attr × IdealCredOutput O)}
  {ev : IdealCredInput Attr × IdealCredOutput O}

theorem CredEventAt.mem (h : CredEventAt cfg s tr st sAt ev) : ev ∈ tr := by
  obtain ⟨pre, post, _, hSplit, _, _, _⟩ := h
  rw [hSplit]
  exact List.mem_append_right _ (List.Mem.head _)

theorem CredEventAt.step (h : CredEventAt cfg s tr st sAt ev) :
    ∃ sNext : IdealCredState Attr O, idealCredStep cfg sAt ev.1 = some (sNext, ev.2) := by
  obtain ⟨_, _, sNext, _, _, hStep, _⟩ := h
  exact ⟨sNext, hStep⟩

/-- The state in which an event of a run from an initial state was processed is reachable. -/
theorem CredEventAt.reachable (h : CredEventAt cfg s tr st sAt ev)
    (hInit : (idealCredMachine cfg).Init s) : (idealCredMachine cfg).Reachable sAt := by
  obtain ⟨pre, _, _, _, hPre, _, _⟩ := h
  exact ⟨s, pre, hInit, hPre⟩

/-- Whoever is corrupt at the start is corrupt when the event is processed, and whoever is
    corrupt then is corrupt at the end. -/
theorem CredEventAt.corruption_le (h : CredEventAt cfg s tr st sAt ev) :
    CredCorruptionLe s sAt ∧ CredCorruptionLe sAt st := by
  obtain ⟨pre, post, sNext, _, hPre, hStep, hPost⟩ := h
  exact ⟨idealCred_trace_corruption_monotone cfg hPre,
    (idealCredStep_provenance cfg hStep).1.trans (idealCred_trace_corruption_monotone cfg hPost)⟩

theorem CredEventAt.head {s' : IdealCredState Attr O} {inp : IdealCredInput Attr}
    {out : IdealCredOutput O} {rest : List (IdealCredInput Attr × IdealCredOutput O)}
    (hStep : (idealCredMachine cfg).step s inp = some (s', out))
    (hRest : (idealCredMachine cfg).ValidTrace s' rest st) (hEq : (inp, out) = ev) :
    CredEventAt cfg s ((inp, out) :: rest) st s ev := by
  subst hEq
  exact .intro [] rest s' rfl (.nil s) hStep hRest

theorem CredEventAt.tail_accept {s₀ : IdealCredState Attr O} {inp : IdealCredInput Attr}
    {out : IdealCredOutput O}
    (h : CredEventAt cfg s tr st sAt ev)
    (hStep : (idealCredMachine cfg).step s₀ inp = some (s, out)) :
    CredEventAt cfg s₀ ((inp, out) :: tr) st sAt ev := by
  obtain ⟨pre, post, sNext, hSplit, hPre, hStepAt, hPost⟩ := h
  refine .intro ((inp, out) :: pre) post sNext ?_ (.accept hStep hPre) hStepAt hPost
  rw [hSplit]
  rfl

theorem CredEventAt.tail_reject {s₀ : IdealCredState Attr O} (inp : IdealCredInput Attr)
    (h : CredEventAt cfg ((idealCredMachine cfg).errStep s₀ inp) tr st sAt ev)
    (hNone : (idealCredMachine cfg).step s₀ inp = none) :
    CredEventAt cfg s₀ tr st sAt ev := by
  obtain ⟨pre, post, sNext, hSplit, hPre, hStepAt, hPost⟩ := h
  exact .intro pre post sNext hSplit (.reject inp hNone hPre) hStepAt hPost

end EventAt

/-- Every event of a run was processed in some state of that run. -/
theorem idealCred_trace_event_at {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    {s st : IdealCredState Attr O} {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (hTr : (idealCredMachine cfg).ValidTrace s tr st)
    (ev : IdealCredInput Attr × IdealCredOutput O) (hEv : ev ∈ tr) :
    ∃ sAt : IdealCredState Attr O, CredEventAt cfg s tr st sAt ev := by
  induction hTr with
  | nil _ => exact nomatch hEv
  | @accept s s' sf inp out rest hStep hRest ih =>
    rcases List.mem_cons.mp hEv with hHead | hTail
    · exact ⟨s, CredEventAt.head hStep hRest hHead.symm⟩
    · obtain ⟨sAt, hAt⟩ := ih hTail
      exact ⟨sAt, hAt.tail_accept hStep⟩
  | @reject s sf inp rest hNone _ ih =>
    obtain ⟨sAt, hAt⟩ := ih hEv
    exact ⟨sAt, CredEventAt.tail_reject inp hAt hNone⟩

/-- Along any run: the corruption set only grows; every record of the final state was already
    present, or the run contains its issuance, processed on the issuer port or on the adversary
    port in a state where the issuer was corrupt; every approval was already present, or the run
    contains it, processed on that server's port or on the adversary port in a state where the
    server was corrupt. -/
theorem idealCred_trace_provenance {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    {s st : IdealCredState Attr O} {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (hTr : (idealCredMachine cfg).ValidTrace s tr st) :
    CredCorruptionLe s st ∧
    (∀ r ∈ st.records, r ∈ s.records ∨
      ∃ (port : CredPort) (sAt : IdealCredState Attr O),
        CredEventAt cfg s tr st sAt
          ((port, CredCommand.issue r.holder r.attrs r.root), IdealCredOutput.issued r.credId) ∧
        (port = CredPort.issuer ∨ (port = CredPort.adversary ∧ sAt.issuerCorrupt = true))) ∧
    (∀ a ∈ st.toprfApprovals, a ∈ s.toprfApprovals ∨
      ∃ (port : CredPort) (sAt : IdealCredState Attr O),
        CredEventAt cfg s tr st sAt
          ((port, CredCommand.approveToprf a.1 a.2), IdealCredOutput.toprfApproved) ∧
        (port = CredPort.server a.1 ∨
          (port = CredPort.adversary ∧ a.1 ∈ sAt.corruptServers))) := by
  induction hTr with
  | nil _ => exact ⟨CredCorruptionLe.refl _, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
  | @accept s s' sf inp out rest hStep hRest ih =>
    obtain ⟨hLe, hRec, hApp⟩ := ih
    obtain ⟨hLe', hRec', hApp'⟩ := idealCredStep_provenance cfg hStep
    refine ⟨hLe'.trans hLe, fun r hr => ?_, fun a ha => ?_⟩
    · rcases hRec r hr with h1 | ⟨port, sAt, hAt, hPort⟩
      · rcases hRec' r h1 with g1 | ⟨port, hEq, hPort⟩
        · exact Or.inl g1
        · exact Or.inr ⟨port, s, CredEventAt.head hStep hRest hEq, hPort⟩
      · exact Or.inr ⟨port, sAt, hAt.tail_accept hStep, hPort⟩
    · rcases hApp a ha with h1 | ⟨port, sAt, hAt, hPort⟩
      · rcases hApp' a h1 with g1 | ⟨port, hEq, hPort⟩
        · exact Or.inl g1
        · exact Or.inr ⟨port, s, CredEventAt.head hStep hRest hEq, hPort⟩
      · exact Or.inr ⟨port, sAt, hAt.tail_accept hStep, hPort⟩
  | @reject s sf inp rest hNone _ ih =>
    obtain ⟨hLe, hRec, hApp⟩ := ih
    refine ⟨hLe, fun r hr => ?_, fun a ha => ?_⟩
    · rcases hRec r hr with h1 | ⟨port, sAt, hAt, hPort⟩
      · exact Or.inl h1
      · exact Or.inr ⟨port, sAt, CredEventAt.tail_reject inp hAt hNone, hPort⟩
    · rcases hApp a ha with h1 | ⟨port, sAt, hAt, hPort⟩
      · exact Or.inl h1
      · exact Or.inr ⟨port, sAt, CredEventAt.tail_reject inp hAt hNone, hPort⟩

/-! ### Port discipline along a run, relative to the corruption set at the event and at the end -/

/-- Event-time form: an event of a run whose command is attributed to `party` arrived on the port
    of `party`, or on the adversary port while `party` was corrupt in the state that processed
    it. -/
theorem idealCredMachine_attributed_port_at {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s st sAt : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort}
    {cmd : CredCommand Attr} {out : IdealCredOutput O} {party : CredParty}
    (hAt : CredEventAt cfg s tr st sAt ((port, cmd), out))
    (hParty : cmd.party = some party) :
    port = party.port ∨ (port = CredPort.adversary ∧ sAt.isCorrupt party) := by
  obtain ⟨sNext, hStep⟩ := hAt.step
  exact idealCredStep_attributed cfg hStep hParty

/-- End-of-run form: an event of a run whose command is attributed to `party` arrived on the port
    of `party`, or on the adversary port and `party` is corrupt in the final state. -/
theorem idealCredMachine_attributed_port {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort}
    {cmd : CredCommand Attr} {out : IdealCredOutput O} {party : CredParty}
    (hTr : (idealCredMachine cfg).ValidTrace s tr st)
    (hEv : ((port, cmd), out) ∈ tr) (hParty : cmd.party = some party) :
    port = party.port ∨ (port = CredPort.adversary ∧ st.isCorrupt party) := by
  obtain ⟨sAt, hAt⟩ := idealCred_trace_event_at cfg hTr _ hEv
  rcases idealCredMachine_attributed_port_at cfg hAt hParty with h | ⟨h, hC⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hAt.corruption_le.2.isCorrupt party hC⟩

/-- **A party honest at the end of a run spoke only for itself.** If `party` is not corrupt in the
    final state of a run, every event of the run whose command is attributed to `party` arrived
    on the port of `party`. -/
theorem idealCredMachine_honest_party_port {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort}
    {cmd : CredCommand Attr} {out : IdealCredOutput O} {party : CredParty}
    (hTr : (idealCredMachine cfg).ValidTrace s tr st) (hHonest : ¬ st.isCorrupt party)
    (hEv : ((port, cmd), out) ∈ tr) (hParty : cmd.party = some party) :
    port = party.port := by
  rcases idealCredMachine_attributed_port cfg hTr hEv hParty with h | ⟨_, hC⟩
  · exact h
  · exact absurd hC hHonest

/-- **Issuer honest at the end.** If the issuer is not corrupt in the final state of a run, every
    issuance and every epoch update of the run arrived on the issuer port. -/
theorem idealCredMachine_honest_issuer_port {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort}
    {cmd : CredCommand Attr} {out : IdealCredOutput O}
    (hTr : (idealCredMachine cfg).ValidTrace s tr st) (hHonest : st.issuerCorrupt = false)
    (hEv : ((port, cmd), out) ∈ tr)
    (hCmd : (∃ h attrs newRoot, cmd = CredCommand.issue h attrs newRoot) ∨
      (∃ newEpoch newRoot, cmd = CredCommand.advanceEpoch newEpoch newRoot)) :
    port = CredPort.issuer := by
  have hH : ¬ st.isCorrupt CredParty.issuer := by
    intro hC
    have hC' : st.issuerCorrupt = true := hC
    rw [hHonest] at hC'
    cases hC'
  have hParty : cmd.party = some CredParty.issuer := by
    rcases hCmd with ⟨h, attrs, newRoot, hC⟩ | ⟨newEpoch, newRoot, hC⟩
    · rw [hC]
      rfl
    · rw [hC]
      rfl
  exact idealCredMachine_honest_party_port cfg hTr hH hEv hParty

/-- **Holder honest at the end.** If holder `h` is not corrupt in the final state of a run, every
    presentation in the name of `h` that the run processed (accepted or answered with the verdict
    `false`) arrived on the port of `h`. -/
theorem idealCredMachine_honest_holder_port {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort} {h cid : Nat}
    {stmt : CredentialStatement Attr} {out : IdealCredOutput O}
    (hTr : (idealCredMachine cfg).ValidTrace s tr st) (hHonest : h ∉ st.corruptHolders)
    (hEv : ((port, CredCommand.present h cid stmt), out) ∈ tr) :
    port = CredPort.holder h :=
  idealCredMachine_honest_party_port cfg (party := CredParty.holder h) hTr hHonest hEv rfl

/-- **Server honest at the end.** If TOPRF server `i` is not corrupt in the final state of a run,
    every approval in the name of `i` in the run arrived on the port of `i`. -/
theorem idealCredMachine_honest_server_port {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort} {i : Nat}
    {t : ToprfTicket} {out : IdealCredOutput O}
    (hTr : (idealCredMachine cfg).ValidTrace s tr st) (hHonest : i ∉ st.corruptServers)
    (hEv : ((port, CredCommand.approveToprf (Attr := Attr) i t), out) ∈ tr) :
    port = CredPort.server i :=
  idealCredMachine_honest_party_port cfg (party := CredParty.server i) hTr hHonest hEv rfl

/-! ### Issuance and possession provenance -/

/-- **Issuance provenance, event-time form.** Every record of a run from the initial state was
    created by an issuance event of that run, naming its holder, attributes and root and answered
    with its identifier; that event was processed on the issuer port, or on the adversary port in
    a state where the issuer was corrupt. -/
theorem idealCredMachine_record_provenance_at {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s₀ st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (hInit : (idealCredMachine cfg).Init s₀) (hTr : (idealCredMachine cfg).ValidTrace s₀ tr st)
    (r : CredentialRecord Attr) (hr : r ∈ st.records) :
    ∃ (port : CredPort) (sAt : IdealCredState Attr O),
      CredEventAt cfg s₀ tr st sAt
        ((port, CredCommand.issue r.holder r.attrs r.root), IdealCredOutput.issued r.credId) ∧
      (port = CredPort.issuer ∨ (port = CredPort.adversary ∧ sAt.issuerCorrupt = true)) := by
  have hEq : s₀ = IdealCredState.empty cfg := hInit
  subst hEq
  rcases (idealCred_trace_provenance cfg hTr).2.1 r hr with h | h
  · exact nomatch h
  · exact h

/-- **Issuance provenance, end-of-run form.** Every record of a run from the initial state was
    created by an issuance event of that run, on the issuer port, or on the adversary port and
    the issuer is corrupt in the final state. -/
theorem idealCredMachine_record_provenance {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s₀ st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (hInit : (idealCredMachine cfg).Init s₀) (hTr : (idealCredMachine cfg).ValidTrace s₀ tr st)
    (r : CredentialRecord Attr) (hr : r ∈ st.records) :
    ∃ port : CredPort,
      ((port, CredCommand.issue r.holder r.attrs r.root), IdealCredOutput.issued r.credId) ∈ tr ∧
      (port = CredPort.issuer ∨ (port = CredPort.adversary ∧ st.issuerCorrupt = true)) := by
  obtain ⟨port, sAt, hAt, hPort⟩ := idealCredMachine_record_provenance_at cfg hInit hTr r hr
  refine ⟨port, hAt.mem, ?_⟩
  rcases hPort with h | ⟨h, hC⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hAt.corruption_le.2.issuer hC⟩

/-- With the issuer not corrupt at the end of a run from the initial state, every record was
    created by an issuer-port issuance event of that run. -/
theorem idealCredMachine_record_provenance_honest_issuer {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s₀ st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (hInit : (idealCredMachine cfg).Init s₀) (hTr : (idealCredMachine cfg).ValidTrace s₀ tr st)
    (hHonest : st.issuerCorrupt = false)
    (r : CredentialRecord Attr) (hr : r ∈ st.records) :
    ((CredPort.issuer, CredCommand.issue r.holder r.attrs r.root),
      IdealCredOutput.issued r.credId) ∈ tr := by
  obtain ⟨port, hMem, hPort⟩ := idealCredMachine_record_provenance cfg hInit hTr r hr
  rcases hPort with h | ⟨_, hC⟩
  · rw [h] at hMem
    exact hMem
  · rw [hHonest] at hC
    cases hC

/-- An accepted issuance arrived on the issuer port, or on the adversary port in a state where the
    issuer is corrupt, and the credential has between `1` and `maxAttrs` attributes. -/
theorem idealCredMachine_issuance_authenticated {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O} {port : CredPort} {h : Nat}
    {attrs : List Attr} {newRoot : Digest256} {out : IdealCredOutput O}
    (hStep : (idealCredMachine cfg).step st (port, .issue h attrs newRoot) = some (st', out)) :
    (port = CredPort.issuer ∨ (port = CredPort.adversary ∧ st.issuerCorrupt = true)) ∧
    0 < attrs.length ∧ attrs.length ≤ pqCredentialProfile.maxAttrs := by
  obtain ⟨hSpeak, hExec⟩ := idealCredStep_inv hStep
  obtain ⟨hAcc, _, _⟩ := credExec_issue_inv hExec
  simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hSpeak
  simp only [IdealCredState.issueAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
  exact ⟨hSpeak, hAcc.1.1, hAcc.1.2⟩

/-- Presentation soundness of a single step: an accepted presentation was admitted for holder `h`
    (own port, or adversary port with `h` corrupt), names the current issuer key, epoch and
    accumulator root, uses a fresh challenge that the step burns, has valid disclosed indices, and
    `h` owns a record with identifier `cid` of the current epoch satisfying the statement. -/
theorem idealCredMachine_presentation_sound {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O} {port : CredPort} {h cid : Nat}
    {stmt : CredentialStatement Attr}
    (hStep : (idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st', .presentationVerdict true)) :
    (port = CredPort.holder h ∨ (port = CredPort.adversary ∧ h ∈ st.corruptHolders)) ∧
    stmt.issuerPk = st.issuerPk ∧
    stmt.epoch = st.epoch ∧
    stmt.accumulatorRoot = st.accumulatorRoot ∧
    (st.challengeLedgers stmt.verifier).accepts stmt.verifierScope stmt.challengeNonce (st.verifierTime stmt.verifier) = true ∧
    (∀ now, (st'.challengeLedgers stmt.verifier).accepts stmt.verifierScope stmt.challengeNonce now = false) ∧
    DisclosedIndicesValid stmt = true ∧
    ∃ r ∈ st.records, r.credId = cid ∧ r.holder = h ∧ r.epoch = st.epoch ∧
      CredentialMatchesAttributes stmt r.attrs = true := by
  obtain ⟨hSpeak, hExec⟩ := idealCredStep_inv hStep
  obtain ⟨hAcc, hSt⟩ := credExec_present_true_inv hExec
  simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hSpeak
  simp only [IdealCredState.presentAccepts, IdealCredState.eligible, Bool.and_eq_true,
    decide_eq_true_eq, List.any_eq_true] at hAcc
  obtain ⟨⟨⟨⟨hPk, hEp⟩, hRoot⟩, hFresh⟩, r, hr, ⟨⟨hId, hH⟩, hREp⟩, hMatch⟩ := hAcc
  have hIdx : DisclosedIndicesValid stmt = true := by
    have hM := hMatch
    simp only [CredentialMatchesAttributes, Bool.and_eq_true] at hM
    exact hM.1.2
  subst hSt
  refine ⟨hSpeak, hPk, hEp, hRoot, hFresh, ?_, hIdx, r, hr, hId, hH, hREp, hMatch⟩
  intro now
  simp only [VerifierChallengeLedgers.consume, VerifierChallengeLedgers.set, ↓reduceIte]
  exact VerifierChallengeLedger.consume_rejects _ _ _ _

/-- **Possession provenance.** If, after a run from the initial state, a presentation of
    credential `cid` by holder `h` is accepted in state `st`, then it arrived on the port of `h`,
    or on the adversary port with `h` corrupt in `st`; and `h` owns a record with that identifier,
    of the statement's epoch, satisfying the statement, which an issuance event of the run issued
    to `h`, on the issuer port, or on the adversary port and the issuer is corrupt in `st`. -/
theorem idealCredMachine_presentation_provenance {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s₀ st st' : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort} {h cid : Nat}
    {stmt : CredentialStatement Attr}
    (hInit : (idealCredMachine cfg).Init s₀) (hTr : (idealCredMachine cfg).ValidTrace s₀ tr st)
    (hStep : (idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st', .presentationVerdict true)) :
    (port = CredPort.holder h ∨ (port = CredPort.adversary ∧ h ∈ st.corruptHolders)) ∧
    stmt.issuerPk = cfg.issuerPk ∧
    ∃ r ∈ st.records, r.credId = cid ∧ r.holder = h ∧ r.epoch = stmt.epoch ∧
      CredentialMatchesAttributes stmt r.attrs = true ∧
      ∃ issuePort : CredPort,
        ((issuePort, CredCommand.issue h r.attrs r.root), IdealCredOutput.issued cid) ∈ tr ∧
        (issuePort = CredPort.issuer ∨
          (issuePort = CredPort.adversary ∧ st.issuerCorrupt = true)) := by
  have hInv := idealCredInv_reachable ⟨s₀, tr, hInit, hTr⟩
  obtain ⟨hPort, hPk, hEp, _, _, _, _, r, hr, hId, hH, hREp, hMatch⟩ :=
    idealCredMachine_presentation_sound cfg hStep
  obtain ⟨issuePort, hMem, hIssuePort⟩ := idealCredMachine_record_provenance cfg hInit hTr r hr
  rw [hId, hH] at hMem
  exact ⟨hPort, hPk.trans hInv.issuerPk_eq, r, hr, hId, hH, hREp.trans hEp.symm, hMatch,
    issuePort, hMem, hIssuePort⟩

/-- **Possession provenance with honest parties.** If, after a run from the initial state, a
    presentation of credential `cid` by holder `h` is accepted in a state where neither `h` nor
    the issuer is corrupt, then it arrived on the port of `h` and the run contains the issuer-port
    issuance of `cid` to `h`. -/
theorem idealCredMachine_presentation_provenance_honest {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s₀ st st' : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort} {h cid : Nat}
    {stmt : CredentialStatement Attr}
    (hInit : (idealCredMachine cfg).Init s₀) (hTr : (idealCredMachine cfg).ValidTrace s₀ tr st)
    (hHolder : h ∉ st.corruptHolders) (hIssuer : st.issuerCorrupt = false)
    (hStep : (idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st', .presentationVerdict true)) :
    port = CredPort.holder h ∧
    ∃ r ∈ st.records, r.credId = cid ∧ r.holder = h ∧
      ((CredPort.issuer, CredCommand.issue h r.attrs r.root), IdealCredOutput.issued cid) ∈ tr := by
  obtain ⟨hPort, _, r, hr, hId, hH, _, _, issuePort, hMem, hIssuePort⟩ :=
    idealCredMachine_presentation_provenance cfg hInit hTr hStep
  refine ⟨?_, r, hr, hId, hH, ?_⟩
  · rcases hPort with hP | ⟨_, hC⟩
    · exact hP
    · exact absurd hC hHolder
  · rcases hIssuePort with hP | ⟨_, hC⟩
    · rw [hP] at hMem
      exact hMem
    · rw [hIssuer] at hC
      cases hC

/-! ### Rejection of unauthenticated behaviour -/

/-- Tooth (audit #2): in a state where the issuer is not corrupt, an issuance arriving on any port
    other than the issuer's — in particular the adversary's — is rejected, whatever holder,
    attributes and root it names. -/
theorem idealCredMachine_rejects_foreign_issue {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st : IdealCredState Attr O} (port : CredPort) (h : Nat)
    (attrs : List Attr) (newRoot : Digest256)
    (hHonest : st.issuerCorrupt = false) (hPort : ¬ (port = CredPort.issuer)) :
    (idealCredMachine cfg).step st (port, .issue h attrs newRoot) = none := by
  apply idealCredStep_eq_none_of_not_speaksFor
  simp only [IdealCredState.speaksFor, hHonest, decide_eq_false hPort, Bool.and_false,
    Bool.or_false]

/-- Tooth (audit #2): in a state where the issuer is not corrupt, an epoch / accumulator-root
    update arriving on any other port is rejected. -/
theorem idealCredMachine_rejects_foreign_epoch_advance {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st : IdealCredState Attr O} (port : CredPort) (newEpoch : Nat)
    (newRoot : Digest256)
    (hHonest : st.issuerCorrupt = false) (hPort : ¬ (port = CredPort.issuer)) :
    (idealCredMachine cfg).step st (port, .advanceEpoch newEpoch newRoot) = none := by
  apply idealCredStep_eq_none_of_not_speaksFor
  simp only [IdealCredState.speaksFor, hHonest, decide_eq_false hPort, Bool.and_false,
    Bool.or_false]

/-- Tooth: a corruption request arriving on any port other than the adversary's is rejected. -/
theorem idealCredMachine_rejects_foreign_corrupt {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (port : CredPort) (party : CredParty)
    (hPort : ¬ (port = CredPort.adversary)) :
    (idealCredMachine (Attr := Attr) cfg).step st (port, .corrupt party) = none := by
  apply idealCredStep_eq_none_of_not_speaksFor
  simp only [IdealCredState.speaksFor, decide_eq_false hPort]

/-- A corruption request on the adversary port is answered in every state; afterwards the party is
    corrupt, every earlier corrupt party still is, and records, approvals, charges, epoch and
    verifier ledgers are unchanged. -/
theorem idealCredMachine_corrupt_accepted {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (party : CredParty) :
    ∃ st' : IdealCredState Attr O,
      (idealCredMachine cfg).step st (.adversary, .corrupt party) = some (st', .corrupted) ∧
      st'.isCorrupt party ∧ CredCorruptionLe st st' ∧
      st'.records = st.records ∧ st'.toprfApprovals = st.toprfApprovals ∧
      st'.oprfCharges = st.oprfCharges ∧ st'.oprfTable = st.oprfTable ∧
      st'.epoch = st.epoch ∧ st'.accumulatorRoot = st.accumulatorRoot ∧
      st'.challengeLedgers = st.challengeLedgers := by
  refine ⟨st.withCorrupt party, idealCredStep_corrupt_eq cfg st party,
    (st.withCorrupt_le party).1, (st.withCorrupt_le party).2, ?_⟩
  cases party <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Tooth (audit #10): a credential with zero attributes is never issued, on any port. -/
theorem idealCredMachine_rejects_empty_credential {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (port : CredPort) (h : Nat)
    (attrs : List Attr) (newRoot : Digest256) (hEmpty : attrs.length = 0) :
    (idealCredMachine cfg).step st (port, .issue h attrs newRoot) = none := by
  apply idealCredStep_eq_none_of_exec
  have hAcc : st.issueAccepts attrs = false := by
    simp only [IdealCredState.issueAccepts, hEmpty, Nat.lt_irrefl, decide_false, Bool.false_and]
  simp only [credExec, hAcc, Bool.false_eq_true, ↓reduceIte]

/-- Tooth (audit #2): a presentation in the name of a holder not corrupt in the current state,
    arriving on any port other than that holder's, is rejected, whatever credential it names. -/
theorem idealCredMachine_rejects_foreign_presentation {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st : IdealCredState Attr O} (port : CredPort) (h cid : Nat)
    (stmt : CredentialStatement Attr)
    (hHonest : h ∉ st.corruptHolders) (hPort : ¬ (port = CredPort.holder h)) :
    (idealCredMachine cfg).step st (port, .present h cid stmt) = none := by
  apply idealCredStep_eq_none_of_not_speaksFor
  simp only [IdealCredState.speaksFor, decide_eq_false hHonest, decide_eq_false hPort,
    Bool.and_false, Bool.or_false]

/-- Tooth (audit #2): a party presenting on its own port a credential identifier none of whose
    records it owns is never accepted, even for an empty disclosure. -/
theorem idealCredMachine_rejects_unheld_credential {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O} (port : CredPort) (h cid : Nat)
    (stmt : CredentialStatement Attr)
    (hNotOwner : ∀ r ∈ st.records, r.credId = cid → ¬ (r.holder = h)) :
    ¬ ((idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st', .presentationVerdict true)) := by
  intro hStep
  obtain ⟨_, _, _, _, _, _, _, r, hr, hId, hH, _⟩ :=
    idealCredMachine_presentation_sound cfg hStep
  exact hNotOwner r hr hId hH

/-- Tooth (audit #9): a statement for any epoch other than the current one is never accepted. -/
theorem idealCredMachine_rejects_stale_epoch {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O} (port : CredPort) (h cid : Nat)
    (stmt : CredentialStatement Attr) (hStale : ¬ (stmt.epoch = st.epoch)) :
    ¬ ((idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st', .presentationVerdict true)) := by
  intro hStep
  obtain ⟨_, _, hEp, _⟩ := idealCredMachine_presentation_sound cfg hStep
  exact hStale hEp

/-- Tooth (audit #9): after an epoch rotation, no credential issued before it is presentable. -/
theorem idealCredMachine_rejects_retired_credential {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st₁ st₂ : IdealCredState Attr O} (port₀ port : CredPort)
    (newEpoch : Nat) (newRoot : Digest256) (out : IdealCredOutput O) (h cid : Nat)
    (stmt : CredentialStatement Attr)
    (hReach : (idealCredMachine cfg).Reachable st)
    (hAdvance : (idealCredMachine cfg).step st (port₀, .advanceEpoch newEpoch newRoot) =
      some (st₁, out)) :
    ¬ ((idealCredMachine cfg).step st₁ (port, .present h cid stmt) =
      some (st₂, .presentationVerdict true)) := by
  intro hStep
  have hInv := idealCredInv_reachable hReach
  obtain ⟨hLt, hSt, _⟩ := credExec_advanceEpoch_inv (idealCredStep_inv hAdvance).2
  obtain ⟨_, _, _, _, _, _, _, r, hr, _, _, hREp, _⟩ :=
    idealCredMachine_presentation_sound cfg hStep
  subst hSt
  obtain ⟨_, _, hLe⟩ := hInv.records_wf r hr
  have hREp' : r.epoch = newEpoch := hREp
  rw [hREp'] at hLe
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLt hLe)

/-- Tooth: a challenge nonce is accepted at most once. -/
theorem idealCredMachine_rejects_replayed_challenge {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st₁ st₂ : IdealCredState Attr O} (port port' : CredPort)
    (h cid h' cid' : Nat) (stmt stmt' : CredentialStatement Attr)
    (hVerifier : stmt'.verifier = stmt.verifier)
    (hScope : stmt'.verifierScope = stmt.verifierScope)
    (hSame : stmt'.challengeNonce = stmt.challengeNonce)
    (hFirst : (idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st₁, .presentationVerdict true)) :
    ¬ ((idealCredMachine cfg).step st₁ (port', .present h' cid' stmt') =
      some (st₂, .presentationVerdict true)) := by
  intro hSecond
  obtain ⟨_, _, _, _, _, hBurned, _⟩ := idealCredMachine_presentation_sound cfg hFirst
  obtain ⟨_, _, _, _, hFresh, _⟩ := idealCredMachine_presentation_sound cfg hSecond
  rw [hVerifier, hSame, hScope, hBurned] at hFresh
  cases hFresh

/-- At most one acceptance of a challenge in its scope throughout a run, even with arbitrary
    intervening issuance, other presentations, epoch changes, corruption, and clock rollback. -/
theorem idealCredMachine_challenge_at_most_once_trace {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st₁ mid st₂ : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (port port' : CredPort) (h cid h' cid' : Nat) (stmt stmt' : CredentialStatement Attr)
    (hr : (idealCredMachine cfg).Reachable st)
    (hFirst : (idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st₁, .presentationVerdict true))
    (ht : (idealCredMachine cfg).ValidTrace st₁ tr mid)
    (hVerifier : stmt'.verifier = stmt.verifier)
    (hScope : stmt'.verifierScope = stmt.verifierScope)
    (hNonce : stmt'.challengeNonce = stmt.challengeNonce) :
    (idealCredMachine cfg).step mid (port', .present h' cid' stmt') ≠
      some (st₂, .presentationVerdict true) := by
  have hw := idealCredMachine_ledger_wellFormed hr stmt.verifier
  have ha := (idealCredMachine_presentation_sound cfg hFirst).2.2.2.2.1
  have hRet := VerifierChallengeLedger.accepted_retired _ _ _ _ hw ha
  obtain ⟨_, hs⟩ := credExec_present_true_inv (idealCredStep_inv hFirst).2
  have hRet₁ : (st₁.challengeLedgers stmt.verifier).Retired stmt.verifierScope stmt.challengeNonce := by
    rw [hs]
    simpa only [VerifierChallengeLedgers.consume, VerifierChallengeLedgers.set, ↓reduceIte] using hRet
  have hRetMid := (idealCredMachine_ledger_evolution cfg ht stmt.verifier).retired hRet₁
  intro hSecond
  have hb := (idealCredMachine_presentation_sound cfg hSecond).2.2.2.2.1
  rw [hVerifier, hScope, hNonce, hRetMid.rejects] at hb
  cases hb

/-- Changing another verifier's entire ledger cannot change this verifier's presentation verdict,
    even when both use the identical scope and nonce. The other verifier's consumption history
    cannot become a refusal side channel. -/
theorem idealCredMachine_presentation_ledger_noninterference {Attr O : Type} [DecidableEq Attr]
    (st : IdealCredState Attr O) (other : Nat) (replacement : VerifierChallengeLedger)
    (h cid : Nat) (stmt : CredentialStatement Attr) (hne : stmt.verifier ≠ other) :
    ({ st with challengeLedgers := st.challengeLedgers.set other replacement } :
      IdealCredState Attr O).presentAccepts h cid stmt = st.presentAccepts h cid stmt := by
  simp only [IdealCredState.presentAccepts, IdealCredState.eligible,
    VerifierChallengeLedgers.set, hne, ↓reduceIte]

/-- A real accepted presentation on A leaves all of B's ledger state untouched, including
    B's outstanding challenges, issuance counter, capacity, and resulting refusals. -/
theorem idealCredMachine_presentation_preserves_other_ledger {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O} {port : CredPort} {h cid : Nat}
    {stmt : CredentialStatement Attr} (other : Nat) (hne : other ≠ stmt.verifier)
    (hs : (idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st', .presentationVerdict true)) :
    st'.challengeLedgers other = st.challengeLedgers other := by
  obtain ⟨_, he⟩ := credExec_present_true_inv (idealCredStep_inv hs).2
  rw [he]
  exact VerifierChallengeLedgers.set_other _ _ _ hne _

/-- Issuance on A cannot consume B's capacity or change B's issued names or refusals. -/
theorem idealCredMachine_issue_preserves_other_ledger {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O} {port : CredPort}
    {verifier : Nat} {scope : Bytes} {now ttl : Nat} {out : IdealCredOutput O}
    (other : Nat) (hne : other ≠ verifier)
    (hs : (idealCredMachine cfg).step st (port, .issueChallenge verifier scope now ttl) = some (st', out)) :
    st'.challengeLedgers other = st.challengeLedgers other := by
  obtain ⟨_, _, _, he, _⟩ := credExec_issueChallenge_inv (idealCredStep_inv hs).2
  rw [he]
  exact VerifierChallengeLedgers.set_other _ _ _ hne _

/-- The other verifier cannot detect an accepted presentation through its next refusal:
    the actual successor machine state gives exactly the same verdict at its scope. -/
theorem idealCredMachine_presentation_preserves_other_verdict {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O} {port : CredPort} {h cid : Nat}
    {stmt : CredentialStatement Attr} (h' cid' : Nat) (other : CredentialStatement Attr)
    (hne : other.verifier ≠ stmt.verifier)
    (hs : (idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st', .presentationVerdict true)) :
    st'.presentAccepts h' cid' other = st.presentAccepts h' cid' other := by
  obtain ⟨_, he⟩ := credExec_present_true_inv (idealCredStep_inv hs).2
  rw [he]
  exact idealCredMachine_presentation_ledger_noninterference st stmt.verifier
    ((st.challengeLedgers stmt.verifier).consume stmt.verifierScope stmt.challengeNonce) h' cid' other hne

/-! ## 6. Selective-disclosure privacy and unlinkability -/

/-- Agreement on the disclosed positions transfers satisfaction of a statement between attribute
    vectors of admissible length. -/
theorem credentialMatchesAttributes_of_agree {Attr : Type} [DecidableEq Attr]
    (stmt : CredentialStatement Attr) (attrs₁ attrs₂ : List Attr)
    (hPos : 0 < attrs₂.length) (hMax : attrs₂.length ≤ pqCredentialProfile.maxAttrs)
    (hAgree : ∀ p ∈ stmt.disclosed, attrs₁[p.1]? = attrs₂[p.1]?)
    (hSat : CredentialMatchesAttributes stmt attrs₁ = true) :
    CredentialMatchesAttributes stmt attrs₂ = true := by
  simp only [CredentialMatchesAttributes, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hSat ⊢
  obtain ⟨⟨_, hIdx⟩, hAll⟩ := hSat
  refine ⟨⟨⟨hPos, hMax⟩, hIdx⟩, fun p hp => ?_⟩
  rw [← hAgree p hp]
  exact hAll p hp

/-- Two holders presenting on their own ports are told apart only through eligibility. -/
theorem idealCredStep_present_congr {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    (st : IdealCredState Attr O) (h₁ cid₁ h₂ cid₂ : Nat) (stmt : CredentialStatement Attr)
    (hElig : st.eligible h₁ cid₁ stmt = st.eligible h₂ cid₂ stmt) :
    idealCredStep cfg st (.holder h₁, .present h₁ cid₁ stmt) =
      idealCredStep cfg st (.holder h₂, .present h₂ cid₂ stmt) := by
  have hS : ∀ h cid : Nat, st.speaksFor (.holder h) (.present h cid stmt) = true := by
    intro h cid
    simp only [IdealCredState.speaksFor, decide_true, Bool.true_or]
  rw [idealCredStep_of_speaksFor (hS h₁ cid₁), idealCredStep_of_speaksFor (hS h₂ cid₂),
    credExec_present_eq, credExec_present_eq]
  unfold IdealCredState.presentAccepts
  rw [hElig]

/-- **Selective-disclosure privacy and single-show unlinkability.** Let two records of the
    current epoch agree on the positions disclosed by `stmt` and possibly differ everywhere else
    (attributes, owner, identifier), the first satisfying `stmt`. Then their owners' presentations
    of `stmt` produce the same verdict and the same successor state. -/
theorem idealCredMachine_selective_disclosure_privacy {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O)
    (stmt : CredentialStatement Attr) (r₁ r₂ : CredentialRecord Attr)
    (hMem₁ : r₁ ∈ st.records) (hMem₂ : r₂ ∈ st.records)
    (hLive₁ : r₁.epoch = st.epoch) (hLive₂ : r₂.epoch = st.epoch)
    (hPos₂ : 0 < r₂.attrs.length) (hMax₂ : r₂.attrs.length ≤ pqCredentialProfile.maxAttrs)
    (hAgreeDisclosed : ∀ p ∈ stmt.disclosed, r₁.attrs[p.1]? = r₂.attrs[p.1]?)
    (hSat₁ : CredentialMatchesAttributes stmt r₁.attrs = true) :
    (idealCredMachine cfg).step st (.holder r₁.holder, .present r₁.holder r₁.credId stmt) =
      (idealCredMachine cfg).step st (.holder r₂.holder, .present r₂.holder r₂.credId stmt) := by
  have hSat₂ := credentialMatchesAttributes_of_agree stmt r₁.attrs r₂.attrs hPos₂ hMax₂
    hAgreeDisclosed hSat₁
  have hE₁ : st.eligible r₁.holder r₁.credId stmt = true := by
    simp only [IdealCredState.eligible, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨r₁, hMem₁, ⟨⟨rfl, rfl⟩, hLive₁⟩, hSat₁⟩
  have hE₂ : st.eligible r₂.holder r₂.credId stmt = true := by
    simp only [IdealCredState.eligible, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨r₂, hMem₂, ⟨⟨rfl, rfl⟩, hLive₂⟩, hSat₂⟩
  exact idealCredStep_present_congr cfg st _ _ _ _ stmt (hE₁.trans hE₂.symm)

/-- Final state and output sequence of a machine on an input sequence, rejected inputs included. -/
def credRun {S In Out : Type} (M : Machine S In Out) : S → List In → S × List (Option Out)
  | s, [] => (s, [])
  | s, inp :: rest =>
    ((credRun M (M.runStep s inp).1 rest).1,
     (M.runStep s inp).2 :: (credRun M (M.runStep s inp).1 rest).2)

/-- Two input sequences that differ only in *which eligible holder and credential* is shown at
    each presentation. Eligibility is evaluated in the state reached at that point of the run, so
    any other inputs may be interleaved freely and identically on both sides. -/
inductive PresentationSwap {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O) :
    IdealCredState Attr O → List (IdealCredInput Attr) → List (IdealCredInput Attr) → Prop where
  | nil (st : IdealCredState Attr O) : PresentationSwap cfg st [] []
  | same {st : IdealCredState Attr O} (inp : IdealCredInput Attr)
      {xs ys : List (IdealCredInput Attr)} :
      PresentationSwap cfg ((idealCredMachine cfg).runStep st inp).1 xs ys →
      PresentationSwap cfg st (inp :: xs) (inp :: ys)
  | swap {st : IdealCredState Attr O} {h₁ cid₁ h₂ cid₂ : Nat}
      {stmt : CredentialStatement Attr} {xs ys : List (IdealCredInput Attr)} :
      st.eligible h₁ cid₁ stmt = true →
      st.eligible h₂ cid₂ stmt = true →
      PresentationSwap cfg
        ((idealCredMachine cfg).runStep st (.holder h₁, .present h₁ cid₁ stmt)).1 xs ys →
      PresentationSwap cfg st
        ((.holder h₁, .present h₁ cid₁ stmt) :: xs) ((.holder h₂, .present h₂ cid₂ stmt) :: ys)

/-- **Trace-level presentation unlinkability.** Along two runs from the same state whose inputs
    differ only in which eligible holder and credential is shown at each presentation, every
    output and the final state coincide. The inputs are fixed sequences, not adversary strategies. -/
theorem idealCredMachine_presentation_trace_unlinkable {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (xs ys : List (IdealCredInput Attr))
    (hSwap : PresentationSwap cfg st xs ys) :
    credRun (idealCredMachine cfg) st xs = credRun (idealCredMachine cfg) st ys := by
  induction hSwap with
  | nil _ => rfl
  | same inp _ ih =>
    simp only [credRun, ih]
  | @swap st h₁ cid₁ h₂ cid₂ stmt xs ys hE₁ hE₂ _ ih =>
    have hStepEq :
        (idealCredMachine cfg).runStep st (.holder h₂, .present h₂ cid₂ stmt) =
          (idealCredMachine cfg).runStep st (.holder h₁, .present h₁ cid₁ stmt) := by
      have h := idealCredStep_present_congr cfg st h₂ cid₂ h₁ cid₁ stmt (hE₂.trans hE₁.symm)
      simp only [Machine.runStep, idealCredMachine, h]
    simp only [credRun, hStepEq, ih]

/-- Tooth: a holder that is not eligible is distinguishable from one that is, so
    `PresentationSwap` cannot drop its eligibility premises. -/
theorem idealCredMachine_ineligible_presentation_distinguishable {Attr O : Type}
    [DecidableEq Attr] (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O}
    (h₁ cid₁ h₂ cid₂ : Nat) (stmt : CredentialStatement Attr)
    (hAccepted : (idealCredMachine cfg).step st (.holder h₁, .present h₁ cid₁ stmt) =
      some (st', .presentationVerdict true))
    (hIneligible : st.eligible h₂ cid₂ stmt = false) :
    ¬ ((idealCredMachine cfg).step st (.holder h₁, .present h₁ cid₁ stmt) =
      (idealCredMachine cfg).step st (.holder h₂, .present h₂ cid₂ stmt)) := by
  intro hEq
  rw [hAccepted] at hEq
  obtain ⟨hAcc, _⟩ := credExec_present_true_inv (idealCredStep_inv hEq.symm).2
  simp only [IdealCredState.presentAccepts, hIneligible, Bool.and_false] at hAcc
  cases hAcc

/-! ## 7. Ideal threshold OPRF -/

/-- **TOPRF evaluation provenance.** If, after a run from the initial state, an evaluation is
    answered in a state `st` with at most `toprfMaxCorrupt` corrupt servers, then the answer is
    the value of the keyed function at `(keyId, epoch, input)`, at least `toprfOnlineServers`
    distinct servers approved the ticket, and the run contains an approval of that ticket on the
    port of a committee server that is not corrupt in `st`, processed in a state `sAt` in which
    that server was not corrupt either. Approvals recorded for servers corrupted between their
    approval and the evaluation count towards the quorum; the bound on `st` still leaves one
    approver outside the corruption set. -/
theorem idealCredMachine_toprf_provenance {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s₀ st st' : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort} {t : ToprfTicket}
    {input : Bytes} {out : IdealCredOutput O}
    (hInit : (idealCredMachine cfg).Init s₀) (hTr : (idealCredMachine cfg).ValidTrace s₀ tr st)
    (hCorrupt : st.corruptServerCount ≤ pqCredentialProfile.toprfMaxCorrupt)
    (hStep : (idealCredMachine cfg).step st (port, .evalToprf t input) = some (st', out)) :
    out = .toprfEvaluated (cfg.oprf ⟨t.keyId, t.epoch, input⟩) ∧
    pqCredentialProfile.toprfOnlineServers ≤ st.approvalCount t ∧
    ∃ i : Nat, i < pqCredentialProfile.toprfServers ∧ i ∉ st.corruptServers ∧
      ((CredPort.server i, CredCommand.approveToprf i t), IdealCredOutput.toprfApproved) ∈ tr ∧
      ∃ sAt : IdealCredState Attr O, i ∉ sAt.corruptServers ∧
        CredEventAt cfg s₀ tr st sAt
          ((CredPort.server i, CredCommand.approveToprf i t), IdealCredOutput.toprfApproved) := by
  have hInv := idealCredInv_reachable ⟨s₀, tr, hInit, hTr⟩
  have hStep' : idealCredStep cfg st (port, .evalToprf t input) = some (st', out) := hStep
  obtain ⟨hAcc, hCase⟩ := credExec_evalToprf_inv (idealCredStep_inv hStep').2
  simp only [IdealCredState.toprfAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
  obtain ⟨⟨⟨⟨⟨hQuorum, _⟩, _⟩, _⟩, _⟩, _⟩ := hAcc
  have hOut : out = .toprfEvaluated (cfg.oprf ⟨t.keyId, t.epoch, input⟩) := by
    rcases hCase with ⟨o, hMem, _, hOut⟩ | ⟨_, hOut⟩
    · have hGraph : o = cfg.oprf ⟨t.keyId, t.epoch, input⟩ := hInv.table_graph _ hMem
      rw [hOut, hGraph]
    · exact hOut
  have hGap : pqCredentialProfile.toprfMaxCorrupt < pqCredentialProfile.toprfOnlineServers := by
    decide
  have hLt : (List.range pqCredentialProfile.toprfServers).countP
        (fun i => decide (i ∈ st.corruptServers)) <
      (List.range pqCredentialProfile.toprfServers).countP
        (fun i => decide ((i, t) ∈ st.toprfApprovals)) :=
    Nat.lt_of_le_of_lt hCorrupt (Nat.lt_of_lt_of_le hGap hQuorum)
  obtain ⟨i, hi, hApproved, hHonest⟩ := credExists_of_countP_lt _ _ _ hLt
  have hMem : (i, t) ∈ st.toprfApprovals := of_decide_eq_true hApproved
  have hNotCorrupt : i ∉ st.corruptServers := of_decide_eq_false hHonest
  have hEq : s₀ = IdealCredState.empty cfg := hInit
  subst hEq
  refine ⟨hOut, hQuorum, i, List.mem_range.mp hi, hNotCorrupt, ?_⟩
  rcases (idealCred_trace_provenance cfg hTr).2.2 (i, t) hMem with h | ⟨p, sAt, hAt, hPort⟩
  · exact nomatch h
  · have hNotAt : i ∉ sAt.corruptServers := fun hC => hNotCorrupt (hAt.corruption_le.2.servers i hC)
    rcases hPort with hP | ⟨_, hC⟩
    · subst hP
      exact ⟨hAt.mem, sAt, hNotAt, hAt⟩
    · exact absurd hC hNotAt

/-- **TOPRF rate budget.** In a reachable state, for every key: the number of points of the keyed
    function revealed so far is at most the number of tickets charged to the key, which is at most
    the quota; and no ticket of the key was charged with a counter at or below an earlier one. -/
theorem idealCredMachine_toprf_budget {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (keyId : Bytes)
    (hReach : (idealCredMachine cfg).Reachable st) :
    st.oprfTable.countP (fun e => decide (e.1.keyId = keyId)) ≤
      st.oprfCharges.countP (fun c => decide (c.keyId = keyId)) ∧
    st.oprfCharges.countP (fun c => decide (c.keyId = keyId)) ≤ cfg.oprfQuota ∧
    st.oprfCharges.Pairwise
      (fun newer older => newer.keyId = older.keyId → older.counter < newer.counter) := by
  have hInv := idealCredInv_reachable hReach
  exact ⟨hInv.table_charged keyId, hInv.charges_budget keyId, hInv.charges_fresh⟩

/-- What the TOPRF servers see of the functionality's state: approvals and charged tickets. -/
def IdealCredState.serverView {Attr O : Type} (st : IdealCredState Attr O) :
    List (Nat × ToprfTicket) × List ToprfTicket :=
  (st.toprfApprovals, st.oprfCharges)

/-- **Input independence of the server view.** Whether an evaluation is answered, and the server
    view after it, do not depend on the evaluation input. This is a property of the ideal
    functionality's bookkeeping; it is not a blindness statement about any protocol. -/
theorem idealCredMachine_toprf_server_view_input_independent {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (port : CredPort) (t : ToprfTicket)
    (input₁ input₂ : Bytes) :
    ((idealCredMachine cfg).step st (port, .evalToprf t input₁)).map (fun p => p.1.serverView) =
      ((idealCredMachine cfg).step st (port, .evalToprf t input₂)).map
        (fun p => p.1.serverView) := by
  have hOne : ∀ input : Bytes,
      ((idealCredMachine cfg).step st (port, .evalToprf t input)).map (fun p => p.1.serverView) =
        if st.toprfAccepts cfg t then some (st.toprfApprovals, t :: st.oprfCharges) else none := by
    intro input
    have hS : st.speaksFor port (.evalToprf t input) = true := by rfl
    have hStep : (idealCredMachine cfg).step st (port, .evalToprf t input) =
        credExec cfg st (.evalToprf t input) := idealCredStep_of_speaksFor hS
    rw [hStep]
    cases hC : st.toprfAccepts cfg t with
    | false => simp only [credExec, hC, Bool.false_eq_true, ↓reduceIte, Option.map_none]
    | true =>
      simp only [credExec, hC, ↓reduceIte]
      cases st.oprfTable.find? (fun e => decide (e.1 = ⟨t.keyId, t.epoch, input⟩)) <;> rfl
  rw [hOne input₁, hOne input₂]

/-- Tooth (audit #9): fewer than `toprfOnlineServers` approving servers release no TOPRF value. -/
theorem idealCredMachine_toprf_rejects_below_quorum {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (port : CredPort) (t : ToprfTicket)
    (input : Bytes)
    (hFew : st.approvalCount t < pqCredentialProfile.toprfOnlineServers) :
    (idealCredMachine cfg).step st (port, .evalToprf t input) = none := by
  show idealCredStep cfg st (port, .evalToprf t input) = none
  apply idealCredStep_eq_none_of_exec
  have hAcc : st.toprfAccepts cfg t = false := by
    have hNot : ¬ (pqCredentialProfile.toprfOnlineServers ≤ st.approvalCount t) :=
      Nat.not_le_of_gt hFew
    simp only [IdealCredState.toprfAccepts, decide_eq_false hNot, Bool.false_and]
  simp only [credExec, hAcc, Bool.false_eq_true, ↓reduceIte]

/-- Tooth: an approval in the name of a server not corrupt in the current state, arriving on any
    other port, is rejected: the adversary can add approvals only for servers it has corrupted. -/
theorem idealCredMachine_rejects_foreign_approval {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st : IdealCredState Attr O} (port : CredPort) (i : Nat)
    (t : ToprfTicket)
    (hHonest : i ∉ st.corruptServers) (hPort : ¬ (port = CredPort.server i)) :
    (idealCredMachine cfg).step st (port, .approveToprf i t) = none := by
  apply idealCredStep_eq_none_of_not_speaksFor
  simp only [IdealCredState.speaksFor, decide_eq_false hHonest, decide_eq_false hPort,
    Bool.and_false, Bool.or_false]

/-- Tooth (audit #9): a key whose quota is exhausted releases no further TOPRF value. -/
theorem idealCredMachine_toprf_rejects_over_budget {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (port : CredPort) (t : ToprfTicket)
    (input : Bytes)
    (hSpent : cfg.oprfQuota ≤ st.oprfCharges.countP (fun c => decide (c.keyId = t.keyId))) :
    (idealCredMachine cfg).step st (port, .evalToprf t input) = none := by
  show idealCredStep cfg st (port, .evalToprf t input) = none
  apply idealCredStep_eq_none_of_exec
  have hAcc : st.toprfAccepts cfg t = false := by
    have hNot : ¬ (st.oprfCharges.countP (fun c => decide (c.keyId = t.keyId)) < cfg.oprfQuota) :=
      Nat.not_lt_of_ge hSpent
    simp only [IdealCredState.toprfAccepts, decide_eq_false hNot, Bool.and_false, Bool.false_and]
  simp only [credExec, hAcc, Bool.false_eq_true, ↓reduceIte]

/-- Tooth (audit #9): a ticket whose counter does not exceed one already charged to its key is
    rejected, so no ticket is redeemed twice. -/
theorem idealCredMachine_toprf_rejects_replayed_ticket {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (port : CredPort) (t c : ToprfTicket)
    (input : Bytes)
    (hCharged : c ∈ st.oprfCharges) (hKey : c.keyId = t.keyId) (hOld : t.counter ≤ c.counter) :
    (idealCredMachine cfg).step st (port, .evalToprf t input) = none := by
  show idealCredStep cfg st (port, .evalToprf t input) = none
  apply idealCredStep_eq_none_of_exec
  cases hC : st.toprfAccepts cfg t with
  | false => simp only [credExec, hC, Bool.false_eq_true, ↓reduceIte]
  | true =>
    simp only [IdealCredState.toprfAccepts, Bool.and_eq_true] at hC
    have h := List.all_eq_true.mp hC.1.1.2 c hCharged
    rw [decide_eq_true hKey] at h
    exact absurd (of_decide_eq_true h) (Nat.not_lt_of_ge hOld)

/-- Tooth (`admit_counter`, `voprf.rs:313`): the counter `u64::MAX` is never admitted. -/
theorem idealCredMachine_toprf_rejects_max_counter {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (port : CredPort) (t : ToprfTicket)
    (input : Bytes) (hMax : t.counter = 18446744073709551615) :
    (idealCredMachine cfg).step st (port, .evalToprf t input) = none := by
  show idealCredStep cfg st (port, .evalToprf t input) = none
  apply idealCredStep_eq_none_of_exec
  have hAcc : st.toprfAccepts cfg t = false := by
    simp only [IdealCredState.toprfAccepts, hMax, Nat.lt_irrefl, decide_false, Bool.and_false]
  simp only [credExec, hAcc, Bool.false_eq_true, ↓reduceIte]

/-! ## 8. A concrete run: the audit counterexamples on the machine itself -/

/-- Demo configuration over `Nat` attributes and outputs: holder `9` and server `4` are corrupt
    from the start, the issuer is corrupt from the start iff `issuerCorrupt`, and each key has a
    quota of two. -/
def idealCredDemoConfig (issuerCorrupt : Bool) : IdealCredConfig Nat where
  issuerPk := [1]
  epoch₀ := 0
  root₀ := 0#256
  issuerCorrupt := issuerCorrupt
  corruptHolders := [9]
  corruptServers := [4]
  oprf pt := pt.epoch + pt.input.length
  oprfQuota := 2

/-- State after the honest issuer issued credential `0` with attributes `[11, 22]` to holder `1`. -/
def idealCredDemoState : IdealCredState Nat Nat :=
  (credRun (idealCredMachine (idealCredDemoConfig false)) (IdealCredState.empty (idealCredDemoConfig false))
    [(.issuer, .issue 1 [11, 22] 1#256), (.verifier 0, .issueChallenge 0 [] 0 60)]).1

/-- Statement against the demo state disclosing `disclosed`. -/
def idealCredDemoStatement (disclosed : List (Nat × Nat)) : CredentialStatement Nat :=
  { issuerPk := [1], epoch := 0, accumulatorRoot := 1#256, disclosed := disclosed,
    challengeNonce := 1 }

/-- The gates are satisfiable: the issuer-port issuance is answered with identifier `0`, and
    holder `1` is accepted on its own port for the empty disclosure and for attribute `1`. -/
theorem idealCredDemo_accepts :
    ((idealCredMachine (idealCredDemoConfig false)).step (IdealCredState.empty (idealCredDemoConfig false))
        (.issuer, .issue 1 [11, 22] 1#256)).map Prod.snd = some (.issued 0) ∧
    ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
        (.holder 1, .present 1 0 (idealCredDemoStatement []))).map Prod.snd =
      some (.presentationVerdict true) ∧
    ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
        (.holder 1, .present 1 0 (idealCredDemoStatement [(1, 22)]))).map Prod.snd =
      some (.presentationVerdict true) := by
  decide +kernel

/-- Tooth (audit #2, the referee's counterexample, on the machine): with an honest issuer,
    (a) an adversary-port issuance of invented attributes is rejected;
    (b) holder `2`, who holds nothing, is not accepted for credential `0` with an empty disclosure,
        neither in its own name nor (c) in the name of holder `1`;
    (d) the adversary is rejected presenting in the name of honest holder `1`, and
    (e) is not accepted in the name of corrupt holder `9`, who does not hold credential `0`;
    (f) holder `1` is not accepted for a false attribute value. -/
theorem idealCredDemo_rejects :
    ¬ (((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.adversary, .issue 9 [99] 2#256)).isSome = true ∨
      ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.holder 2, .present 2 0 (idealCredDemoStatement []))).map Prod.snd =
        some (.presentationVerdict true) ∨
      ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.holder 2, .present 1 0 (idealCredDemoStatement []))).isSome = true ∨
      ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.adversary, .present 1 0 (idealCredDemoStatement []))).isSome = true ∨
      ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.adversary, .present 9 0 (idealCredDemoStatement []))).map Prod.snd =
        some (.presentationVerdict true) ∨
      ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.holder 1, .present 1 0 (idealCredDemoStatement [(1, 23)]))).map Prod.snd =
        some (.presentationVerdict true)) := by
  decide +kernel

/-- Caveat: the guarantees are relative to the corruption set. With an initially corrupt issuer
    the very adversary-port issuance of invented attributes rejected above is accepted. -/
theorem idealCredDemo_corrupt_issuer_issues :
    ((idealCredMachine (idealCredDemoConfig true)).step (IdealCredState.empty (idealCredDemoConfig true))
        (.adversary, .issue 9 [99] 2#256)).map Prod.snd = some (.issued 0) := by
  decide +kernel

/-- Demo ticket. -/
def idealCredDemoTicket : ToprfTicket := ⟨[3], 0, 4⟩

/-- Demo run in which servers `approvers` approve the demo ticket on their own ports. -/
def idealCredDemoApproved (approvers : List Nat) : IdealCredState Nat Nat :=
  (credRun (idealCredMachine (idealCredDemoConfig false)) (IdealCredState.empty (idealCredDemoConfig false))
    (approvers.map (fun i => (CredPort.server i, CredCommand.approveToprf i idealCredDemoTicket)))).1

/-- With four server-port approvals the evaluation returns the keyed-table value. -/
theorem idealCredDemo_toprf_accepts :
    ((idealCredMachine (idealCredDemoConfig false)).step (idealCredDemoApproved [0, 1, 2, 3])
        (.client, .evalToprf idealCredDemoTicket [8, 8])).map Prod.snd =
      some (.toprfEvaluated 2) := by
  decide +kernel

/-- Tooth: three approvals (the security threshold is two, but the backend answers only with four
    servers online) release nothing; neither do repeated approvals by one server; the adversary
    cannot approve for honest server `3`; and a first counter at the window bound is refused. -/
theorem idealCredDemo_toprf_rejects :
    ¬ (((idealCredMachine (idealCredDemoConfig false)).step (idealCredDemoApproved [0, 1, 2])
          (.client, .evalToprf idealCredDemoTicket [8, 8])).isSome = true ∨
      ((idealCredMachine (idealCredDemoConfig false)).step
          (idealCredDemoApproved [0, 0, 0, 0, 1, 2])
          (.client, .evalToprf idealCredDemoTicket [8, 8])).isSome = true ∨
      ((idealCredMachine (idealCredDemoConfig false)).step (idealCredDemoApproved [0, 1, 2])
          (.adversary, .approveToprf 3 idealCredDemoTicket)).isSome = true ∨
      ((idealCredMachine (idealCredDemoConfig false)).step (idealCredDemoApproved [0, 1, 2, 3])
          (.client, .evalToprf ⟨[3], 0, 64⟩ [8, 8])).isSome = true) := by
  decide +kernel

/-! ### Adaptive corruption on the demo run -/

/-- The accepted `(input, output)` pairs of `credRun`, in order. -/
def credRunTrace {S In Out : Type} (M : Machine S In Out) : S → List In → List (In × Out)
  | _, [] => []
  | s, inp :: rest =>
    match (M.runStep s inp).2 with
    | some out => (inp, out) :: credRunTrace M (M.runStep s inp).1 rest
    | none => credRunTrace M (M.runStep s inp).1 rest

/-- `credRun` on an input sequence is a valid run with trace `credRunTrace`. -/
theorem credRun_validTrace {S In Out : Type} (M : Machine S In Out) (xs : List In) :
    ∀ s : S, M.ValidTrace s (credRunTrace M s xs) (credRun M s xs).1 := by
  induction xs with
  | nil => exact fun s => .nil s
  | cons inp rest ih =>
    intro s
    cases hS : M.step s inp with
    | none =>
      have hR : M.runStep s inp = (M.errStep s inp, none) := by
        simp only [Machine.runStep, hS]
      simp only [credRunTrace, credRun, hR]
      exact .reject inp hS (ih _)
    | some p =>
      obtain ⟨s', out⟩ := p
      have hR : M.runStep s inp = (s', some out) := by
        simp only [Machine.runStep, hS]
      simp only [credRunTrace, credRun, hR]
      exact .accept hS (ih _)

/-- Adaptive corruption of a holder, on the demo state (holder `1` owns credential `0` and is not
    corrupt): once the adversary has corrupted holder `1`, the adversary-port presentation in the
    name of holder `1` — rejected before, `idealCredDemo_adaptive_rejects` — is accepted. -/
theorem idealCredDemo_adaptive_holder_corruption_accepts :
    (credRun (idealCredMachine (idealCredDemoConfig false)) idealCredDemoState
        [(.adversary, .corrupt (.holder 1)),
         (.adversary, .present 1 0 (idealCredDemoStatement []))]).2 =
      [some .corrupted, some (.presentationVerdict true)] := by
  decide +kernel

/-- Tooth: on the demo state,
    (a) the adversary-port presentation in the name of holder `1`, not yet corrupt, is rejected;
    (b) it is still rejected after the adversary corrupted a different holder (`2`);
    (c) a corruption request is rejected on the holder's own port, (d) on the issuer port and
    (e) on the client port. -/
theorem idealCredDemo_adaptive_rejects :
    ¬ (((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.adversary, .present 1 0 (idealCredDemoStatement []))).isSome = true ∨
      (credRun (idealCredMachine (idealCredDemoConfig false)) idealCredDemoState
          [(.adversary, .corrupt (.holder 2)),
           (.adversary, .present 1 0 (idealCredDemoStatement []))]).2 =
        [some .corrupted, some (.presentationVerdict true)] ∨
      ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.holder 1, .corrupt (.holder 1))).isSome = true ∨
      ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.issuer, .corrupt .issuer)).isSome = true ∨
      ((idealCredMachine (idealCredDemoConfig false)).step idealCredDemoState
          (.client, .corrupt (.server 0))).isSome = true) := by
  decide +kernel

/-- Inputs of the adaptive TOPRF demo: the adversary corrupts servers `0`, `1`, `2` (server `4` is
    corrupt from the start) and approves the demo ticket in the name of all four, on its own
    port. -/
def idealCredDemoAdaptiveQuorumInputs : List (IdealCredInput Nat) :=
  [(.adversary, .corrupt (.server 0)), (.adversary, .corrupt (.server 1)),
   (.adversary, .corrupt (.server 2)),
   (.adversary, .approveToprf 0 idealCredDemoTicket),
   (.adversary, .approveToprf 1 idealCredDemoTicket),
   (.adversary, .approveToprf 2 idealCredDemoTicket),
   (.adversary, .approveToprf 4 idealCredDemoTicket)]

/-- After the adaptive TOPRF demo inputs, every one of which is answered, the evaluation is
    answered although every input of the run arrived on the adversary port; four committee
    servers are then corrupt. -/
theorem idealCredDemo_adaptive_quorum_without_server_port :
    (credRun (idealCredMachine (idealCredDemoConfig false))
        (IdealCredState.empty (idealCredDemoConfig false))
        (idealCredDemoAdaptiveQuorumInputs ++
          [(.adversary, .evalToprf idealCredDemoTicket [8, 8])])).2 =
      [some .corrupted, some .corrupted, some .corrupted, some .toprfApproved,
       some .toprfApproved, some .toprfApproved, some .toprfApproved,
       some (.toprfEvaluated 2)] ∧
    idealCredDemoAdaptiveQuorumInputs.all (fun inp => decide (inp.1 = CredPort.adversary)) = true ∧
    (credRun (idealCredMachine (idealCredDemoConfig false))
        (IdealCredState.empty (idealCredDemoConfig false))
        idealCredDemoAdaptiveQuorumInputs).1.corruptServerCount = 4 := by
  decide +kernel

/-- Tooth: `idealCredMachine_toprf_provenance` is false without its bound on the number of corrupt
    servers in the answering state. In the adaptive TOPRF demo run an evaluation is answered and
    the run contains no approval on any server port. -/
theorem idealCredDemo_toprf_provenance_needs_corruption_bound :
    ¬ (∀ (st st' : IdealCredState Nat Nat)
        (tr : List (IdealCredInput Nat × IdealCredOutput Nat)) (port : CredPort)
        (t : ToprfTicket) (input : Bytes) (out : IdealCredOutput Nat),
        (idealCredMachine (idealCredDemoConfig false)).ValidTrace
          (IdealCredState.empty (idealCredDemoConfig false)) tr st →
        (idealCredMachine (idealCredDemoConfig false)).step st (port, .evalToprf t input) =
          some (st', out) →
        ∃ i : Nat, ((CredPort.server i, CredCommand.approveToprf i t),
          IdealCredOutput.toprfApproved) ∈ tr) := by
  intro hAll
  have hNoServer : (credRunTrace (idealCredMachine (idealCredDemoConfig false))
      (IdealCredState.empty (idealCredDemoConfig false)) idealCredDemoAdaptiveQuorumInputs).all
        (fun ev => decide (ev.1.1 = CredPort.adversary)) = true := by
    decide +kernel
  have hSome : ((idealCredMachine (idealCredDemoConfig false)).step
      (credRun (idealCredMachine (idealCredDemoConfig false))
        (IdealCredState.empty (idealCredDemoConfig false)) idealCredDemoAdaptiveQuorumInputs).1
      (.adversary, .evalToprf idealCredDemoTicket [8, 8])).isSome = true := by
    decide +kernel
  cases hS : (idealCredMachine (idealCredDemoConfig false)).step
      (credRun (idealCredMachine (idealCredDemoConfig false))
        (IdealCredState.empty (idealCredDemoConfig false)) idealCredDemoAdaptiveQuorumInputs).1
      (.adversary, .evalToprf idealCredDemoTicket [8, 8]) with
  | none =>
    rw [hS] at hSome
    cases hSome
  | some p =>
    obtain ⟨i, hi⟩ := hAll _ p.1 _ _ _ _ p.2 (credRun_validTrace _ _ _) hS
    have hAdv := List.all_eq_true.mp hNoServer _ hi
    exact nomatch of_decide_eq_true hAdv

/-! ## Independent verifier ledgers, issuance and consumption order -/

def ledgerTeethStatement (verifier : Nat) : CredentialStatement Nat :=
  { issuerPk := [1], epoch := 0, accumulatorRoot := 1#256, disclosed := [],
    verifier := verifier, verifierScope := [9], challengeNonce := 1 }

/-- Both verifiers issue the same ideal nonce name. A accepts once, its replay is refused,
    and B still accepts. A later issuance cannot resurrect A's first nonce. -/
def ledgerTeethIndependentOutputs : List (Option (IdealCredOutput Nat)) :=
  (credRun (idealCredMachine (idealCredDemoConfig false))
      (IdealCredState.empty (idealCredDemoConfig false))
      [(.issuer, .issue 1 [11, 22] 1#256),
       (.verifier 1, .issueChallenge 1 [9] 0 60),
       (.verifier 2, .issueChallenge 2 [9] 0 60),
       (.holder 1, .present 1 0 (ledgerTeethStatement 1)),
       (.holder 1, .present 1 0 (ledgerTeethStatement 1)),
       (.holder 1, .present 1 0 (ledgerTeethStatement 2)),
       (.verifier 1, .issueChallenge 1 [9] 0 60),
       (.holder 1, .present 1 0 (ledgerTeethStatement 1))]).2

theorem tooth_verifiers_independent_and_replay_refused :
    ledgerTeethIndependentOutputs =
      [some (.issued 0), some (.challengeIssued 1), some (.challengeIssued 1),
       some (.presentationVerdict true), some (.presentationVerdict false),
       some (.presentationVerdict true), some (.challengeIssued 2),
       some (.presentationVerdict false)] := by
  decide +kernel

/-- Wrong proof/statement, unknown challenge, expired challenge, and foreign verifier port are
    refusals. The invalid statement does not burn the outstanding valid challenge. -/
def ledgerTeethInvalidOutputs : List (Option (IdealCredOutput Nat)) :=
  (credRun (idealCredMachine (idealCredDemoConfig false))
      (IdealCredState.empty (idealCredDemoConfig false))
      [(.issuer, .issue 1 [11, 22] 1#256),
       (.verifier 2, .issueChallenge 1 [9] 0 60),
       (.holder 1, .present 1 0 (ledgerTeethStatement 1)),
       (.verifier 1, .issueChallenge 1 [9] 0 60),
       (.holder 1, .present 1 0 { ledgerTeethStatement 1 with verifierScope := [8] }),
       (.holder 1, .present 1 0 { ledgerTeethStatement 1 with disclosed := [(0, 99)] }),
       (.holder 1, .advanceClock 1 60),
       (.holder 1, .present 1 0 (ledgerTeethStatement 1))]).2

theorem tooth_invalid_proof_does_not_consume_challenge :
    ledgerTeethInvalidOutputs =
      [some (.issued 0), none, some (.presentationVerdict false), some (.challengeIssued 1),
       some (.presentationVerdict false), some (.presentationVerdict false), none,
       some (.presentationVerdict true)] := by
  decide +kernel

/-- The same proof expires at the verifier's deadline. An earlier sample cannot revive it. -/
theorem verifier_clock_expires_challenge :
    (credRun (idealCredMachine (idealCredDemoConfig false))
      (IdealCredState.empty (idealCredDemoConfig false))
      [(.issuer, .issue 1 [11, 22] 1#256), (.verifier 1, .issueChallenge 1 [9] 10 60),
       (.verifier 1, .advanceClock 1 70), (.verifier 1, .advanceClock 1 10),
       (.holder 1, .present 1 0 (ledgerTeethStatement 1))]).2 =
      [some (.issued 0), some (.challengeIssued 1), some .clockAdvanced,
       some .clockAdvanced, some (.presentationVerdict false)] := by decide +kernel

def ledgerTeethFull : VerifierChallengeLedger :=
  { capacity := 2, issued := 2, outstanding := [(([1], 1), 10), (([2], 2), 50)] }

/-- Full capacity refuses to evict live sessions, while expiry and consumption free capacity.
    The issue counter continues past consumed names. Invalid capacities/lifetimes fail closed. -/
theorem tooth_ledger_capacity_expiry_and_fresh_issuance :
    ledgerTeethFull.issue [3] 9 10 = none ∧
    (ledgerTeethFull.issue [3] 10 10).map (fun p => (p.1.outstanding, p.2)) =
      some ([(([3], 3), 20), (([2], 2), 50)], 3) ∧
    ((ledgerTeethFull.consume [1] 1).issue [2] 1 10).map Prod.snd = some 3 ∧
    ({ capacity := 0 } : VerifierChallengeLedger).issue [] 0 10 = none ∧
    ({ capacity := 65537 } : VerifierChallengeLedger).issue [] 0 10 = none ∧
    ({} : VerifierChallengeLedger).issue [] 0 0 = none ∧
    ({} : VerifierChallengeLedger).issue [] (2^64 - 1) 1 = none := by
  decide +kernel

/-- A verifier's capacity is shared across scopes, while another verifier has its own capacity. -/
theorem tooth_capacity_shared_by_scopes_not_verifiers :
    (credRun (idealCredMachine { idealCredDemoConfig false with challengeCapacity := fun _ => 1 })
      (IdealCredState.empty { idealCredDemoConfig false with challengeCapacity := fun _ => 1 })
      [(.verifier 1, CredCommand.issueChallenge (Attr := Nat) 1 [1] 0 60),
       (.verifier 1, .issueChallenge 1 [2] 0 60),
       (.verifier 2, .issueChallenge 2 [2] 0 60)]).2 =
      [some (.challengeIssued 1), some .challengeRefused, some (.challengeIssued 1)] := by
  decide +kernel

def ledgerTeethExhausted : VerifierChallengeLedger :=
  { capacity := 2, issued := 2^64 - 1, outstanding := [(([1], 1), 10)] }

/-- Counter exhaustion happens after expiry pruning. A subsequent backwards clock cannot
    restore that expired entry; an earlier lifetime-validation failure does not prune it. -/
theorem tooth_failed_issue_retains_pruning :
    (ledgerTeethExhausted.issueAttempt [2] 10 1).2 = none ∧
    (ledgerTeethExhausted.issueAttempt [2] 10 1).1.accepts [1] 1 0 = false ∧
    (ledgerTeethExhausted.issueAttempt [2] 10 0).1.accepts [1] 1 0 = true := by
  decide +kernel

/-- The deliberately named opt-out really permits replay; it is not covered by the ledger
    one-time acceptance theorem. A different expected challenge is still rejected. -/
theorem tooth_replay_not_prevented_really_replays :
    [1, 1, 2].map (fun nonce => ReplayNotPrevented 1 nonce true) =
      [true, true, false] := by
  decide +kernel

#verify_constructive
  tooth_verifiers_independent_and_replay_refused
  tooth_invalid_proof_does_not_consume_challenge
  tooth_ledger_capacity_expiry_and_fresh_issuance
  tooth_capacity_shared_by_scopes_not_verifiers
  tooth_failed_issue_retains_pruning
  tooth_replay_not_prevented_really_replays

/-- Refute a global challenge blacklist: it would refuse verifier B after verifier A's
    acceptance, despite B's independently issued, identical `(scope, nonce)`. -/
theorem tooth_global_challenge_blacklist_wrong :
    ledgerTeethIndependentOutputs ≠
      [some (.issued 0), some (.challengeIssued 1), some (.challengeIssued 1),
       some (.presentationVerdict true), some (.presentationVerdict false),
       some (.presentationVerdict false), some (.challengeIssued 2),
       some (.presentationVerdict false)] := by
  decide +kernel

/-- Refute consumption before verification: the valid attempt after the forged one succeeds. -/
theorem tooth_consume_before_verify_wrong :
    ledgerTeethInvalidOutputs ≠
      [some (.issued 0), none, some (.presentationVerdict false), some (.challengeIssued 1),
       some (.presentationVerdict false), some (.presentationVerdict false),
       none, some (.presentationVerdict false)] := by
  decide +kernel

/-- Refute failure to remove the first challenge: its last replay still fails after reissuance. -/
theorem tooth_reissue_resurrects_consumed_nonce_wrong :
    ledgerTeethIndependentOutputs ≠
      [some (.issued 0), some (.challengeIssued 1), some (.challengeIssued 1),
       some (.presentationVerdict true), some (.presentationVerdict false),
       some (.presentationVerdict true), some (.challengeIssued 2),
       some (.presentationVerdict true)] := by
  decide +kernel

#tooth_pair idealCredMachine_challenge_at_most_once_trace vs
  tooth_reissue_resurrects_consumed_nonce_wrong
#tooth_pair idealCredMachine_presentation_preserves_other_verdict vs
  tooth_global_challenge_blacklist_wrong
#tooth_pair idealCredMachine_presentation_sound vs
  tooth_consume_before_verify_wrong

#verify_constructive
  Qsag.Spec.VerifierChallengeLedger.accepted_at_most_once
  Qsag.Spec.VerifierChallengeLedger.invalid_proof_preserves
  Qsag.Spec.VerifierLedgerEvolution.wellFormed
  Qsag.Spec.VerifierLedgerEvolution.retired
  Qsag.Spec.idealCredMachine_ledger_evolution
  Qsag.Spec.idealCredMachine_challenge_at_most_once_trace
  Qsag.Spec.idealCredMachine_presentation_ledger_noninterference
  Qsag.Spec.idealCredMachine_presentation_preserves_other_ledger
  Qsag.Spec.idealCredMachine_issue_preserves_other_ledger
  Qsag.Spec.idealCredMachine_presentation_preserves_other_verdict
  Qsag.Spec.idealCredInv_exec
  Qsag.Spec.idealCredInv_reachable
  Qsag.Spec.idealCredStep_provenance
  Qsag.Spec.idealCredStep_attributed
  Qsag.Spec.idealCredStep_corrupt_eq
  Qsag.Spec.idealCredStep_output_command
  Qsag.Spec.idealCredStep_issuer_issues_at_init
  Qsag.Spec.idealCred_trace_provenance
  Qsag.Spec.idealCred_trace_corruption_monotone
  Qsag.Spec.idealCred_trace_event_at
  Qsag.Spec.idealCredMachine_attributed_port_at
  Qsag.Spec.idealCredMachine_attributed_port
  Qsag.Spec.idealCredMachine_honest_party_port
  Qsag.Spec.idealCredMachine_honest_issuer_port
  Qsag.Spec.idealCredMachine_honest_holder_port
  Qsag.Spec.idealCredMachine_honest_server_port
  Qsag.Spec.idealCredMachine_record_provenance_at
  Qsag.Spec.idealCredMachine_record_provenance
  Qsag.Spec.idealCredMachine_record_provenance_honest_issuer
  Qsag.Spec.idealCredMachine_presentation_provenance_honest
  Qsag.Spec.idealCredMachine_corrupt_accepted
  Qsag.Spec.credRun_validTrace
  Qsag.Spec.idealCredDemo_adaptive_holder_corruption_accepts
  Qsag.Spec.idealCredDemo_adaptive_quorum_without_server_port
  Qsag.Spec.idealCredMachine_issuance_authenticated
  Qsag.Spec.idealCredMachine_presentation_sound
  Qsag.Spec.idealCredMachine_presentation_provenance
  Qsag.Spec.credentialMatchesAttributes_of_agree
  Qsag.Spec.idealCredMachine_selective_disclosure_privacy
  Qsag.Spec.idealCredMachine_presentation_trace_unlinkable
  Qsag.Spec.idealCredMachine_toprf_provenance
  Qsag.Spec.idealCredMachine_toprf_budget
  Qsag.Spec.idealCredMachine_toprf_server_view_input_independent
  Qsag.Spec.idealCredDemo_accepts
  Qsag.Spec.idealCredDemo_corrupt_issuer_issues
  Qsag.Spec.idealCredDemo_toprf_accepts

#tooth_pair Qsag.Spec.idealCredMachine_issuance_authenticated vs
  Qsag.Spec.idealCredMachine_rejects_foreign_issue
#tooth_pair Qsag.Spec.idealCredMachine_record_provenance vs
  Qsag.Spec.idealCredMachine_rejects_foreign_epoch_advance
#tooth_pair Qsag.Spec.idealCredMachine_issuance_authenticated vs
  Qsag.Spec.idealCredMachine_rejects_empty_credential
#tooth_pair Qsag.Spec.idealCredMachine_presentation_provenance vs
  Qsag.Spec.idealCredMachine_rejects_foreign_presentation
#tooth_pair Qsag.Spec.idealCredMachine_presentation_provenance vs
  Qsag.Spec.idealCredMachine_rejects_unheld_credential
#tooth_pair Qsag.Spec.idealCredMachine_presentation_sound vs
  Qsag.Spec.idealCredMachine_rejects_stale_epoch
#tooth_pair Qsag.Spec.idealCredMachine_presentation_provenance vs
  Qsag.Spec.idealCredMachine_rejects_retired_credential
#tooth_pair Qsag.Spec.idealCredMachine_presentation_sound vs
  Qsag.Spec.idealCredMachine_rejects_replayed_challenge
#tooth_pair Qsag.Spec.idealCredMachine_selective_disclosure_privacy vs
  Qsag.Spec.idealCredMachine_ineligible_presentation_distinguishable
#tooth_pair Qsag.Spec.idealCredMachine_toprf_provenance vs
  Qsag.Spec.idealCredMachine_toprf_rejects_below_quorum
#tooth_pair Qsag.Spec.idealCredMachine_toprf_provenance vs
  Qsag.Spec.idealCredMachine_rejects_foreign_approval
#tooth_pair Qsag.Spec.idealCredMachine_toprf_budget vs
  Qsag.Spec.idealCredMachine_toprf_rejects_over_budget
#tooth_pair Qsag.Spec.idealCredMachine_toprf_budget vs
  Qsag.Spec.idealCredMachine_toprf_rejects_replayed_ticket
#tooth_pair Qsag.Spec.idealCredMachine_toprf_provenance vs
  Qsag.Spec.idealCredMachine_toprf_rejects_max_counter
#tooth_pair Qsag.Spec.idealCredDemo_accepts vs
  Qsag.Spec.idealCredDemo_rejects
#tooth_pair Qsag.Spec.idealCredDemo_toprf_accepts vs
  Qsag.Spec.idealCredDemo_toprf_rejects
#tooth_pair Qsag.Spec.idealCredMachine_corrupt_accepted vs
  Qsag.Spec.idealCredMachine_rejects_foreign_corrupt
#tooth_pair Qsag.Spec.idealCredDemo_adaptive_holder_corruption_accepts vs
  Qsag.Spec.idealCredDemo_adaptive_rejects
#tooth_pair Qsag.Spec.idealCredMachine_toprf_provenance vs
  Qsag.Spec.idealCredDemo_toprf_provenance_needs_corruption_bound
#tooth_pair Qsag.Spec.idealCredMachine_honest_holder_port vs
  Qsag.Spec.idealCredDemo_adaptive_rejects

end Qsag.Spec
end
