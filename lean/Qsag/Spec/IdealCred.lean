module
/-
# Qsag.Spec.IdealCred — Ideal Selective-Disclosure Anonymous Credential & TOPRF Functionality

Layer-0 ideal functionality for `crates/qsag-cred/src/blind_vc.rs` (`PiBlindVc`: per-epoch
accumulator, selective-disclosure presentations) and the replicated threshold OPRF of
`crates/qsag-cred/src/voprf.rs`.

Authentication is an ideal-world event, not a checkable token. Every input is a pair
`(port, command)`. The ports are the issuer, each holder `h`, each TOPRF server `i`, the TOPRF
client and the adversary. The corruption set (issuer flag, corrupt holders, corrupt servers) is
part of the state, fixed by the configuration and never changed by a transition: corruption is
static. `IdealCredState.speaksFor` lets a command through only on the port of the party it is
attributed to, or on the adversary port when that party is corrupt.

* **Issuance** creates a record owned by the holder it names; the credential identifier in the
  output is the possession capability. Every record of a run was created by an issuer-port event
  of that run, unless the issuer is corrupt (`idealCredMachine_record_provenance`).
* **Presentation** of credential `cid` by holder `h` is accepted only for a record with that
  identifier owned by `h`, of the current epoch, whose attributes satisfy the statement, for the
  current issuer key, epoch and accumulator root and a fresh challenge. It was made on the port of
  `h` unless `h` is corrupt (`idealCredMachine_presentation_provenance`). Which eligible credential
  was shown is invisible in outputs and successor state
  (`idealCredMachine_presentation_trace_unlinkable`).
* **TOPRF.** Servers approve tickets `(keyId, epoch, counter)` on their own ports. An evaluation is
  answered when `toprfOnlineServers` (four of five, `voprf.rs:4`–`5`) distinct servers approved
  its ticket, the per-key quota is not exhausted and the counter passes `admit_counter`
  (`voprf.rs:310`). It returns the keyed-table value of `(keyId, epoch, input)`. With at most
  `toprfMaxCorrupt` corrupt servers at least one approval came from an honest server port
  (`idealCredMachine_toprf_provenance`).

With a corrupt issuer the adversary can issue anything (`idealCredDemo_corrupt_issuer_issues`): the
guarantees are exactly relative to the corruption set. One ticket covers one item; batches and
per-credential revocation (other than epoch rotation) are not modelled.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## 1. Statements, ports, commands -/

/-- Public selective-disclosure presentation statement pinned by the verifier (`blind_vc.rs`):
    contains only the disclosed `(index, value)` pairs, never the full hidden attribute vector. -/
structure CredentialStatement (Attr : Type) where
  issuerPk : Bytes
  epoch : Nat
  accumulatorRoot : Digest256
  disclosed : List (Nat × Attr)
  challengeNonce : Bytes
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
  | client
  | adversary
  deriving DecidableEq, Repr

/-- Commands, each attributed to the party it names. -/
inductive CredCommand (Attr : Type) where
  /-- The issuer issues a credential with `attrs` to `holder`, moving the accumulator to `newRoot`. -/
  | issue (holder : Nat) (attrs : List Attr) (newRoot : Digest256)
  /-- The issuer retires the current epoch. -/
  | advanceEpoch (newEpoch : Nat) (newRoot : Digest256)
  /-- `holder` shows credential `credId` for `stmt`. -/
  | present (holder : Nat) (credId : Nat) (stmt : CredentialStatement Attr)
  /-- TOPRF server `server` approves `ticket`. -/
  | approveToprf (server : Nat) (ticket : ToprfTicket)
  /-- Evaluation request for `input` under `ticket`. -/
  | evalToprf (ticket : ToprfTicket) (input : Bytes)

/-- An input is a command together with the port it arrived on. -/
abbrev IdealCredInput (Attr : Type) : Type := CredPort × CredCommand Attr

/-- Outputs emitted by `IdealCred`. -/
inductive IdealCredOutput (O : Type) where
  | issued (credId : Nat)
  | epochAdvanced (epoch : Nat)
  | presentationVerdict (ok : Bool)
  | toprfApproved
  | toprfEvaluated (out : O)
  deriving DecidableEq, Repr

/-- Configuration: initial public parameters, the static corruption set, the keyed ideal function
    `oprf` and the enrolled per-key evaluation quota (`CounterStore::reserve`, `voprf.rs:132`). -/
structure IdealCredConfig (O : Type) where
  issuerPk : Bytes
  epoch₀ : Nat
  root₀ : Digest256
  issuerCorrupt : Bool
  corruptHolders : List Nat
  corruptServers : List Nat
  oprf : ToprfPoint → O
  oprfQuota : Nat

/-- Number of corrupt TOPRF servers among the committee indices. -/
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

/-- Ideal credential state: public parameters, the corruption set, the issued records, consumed
    verifier challenges, recorded server approvals, the revealed part of the TOPRF graph and the
    charged tickets (newest first). -/
structure IdealCredState (Attr O : Type) where
  issuerPk : Bytes
  epoch : Nat
  accumulatorRoot : Digest256
  issuedThisEpoch : Nat
  issuerCorrupt : Bool
  corruptHolders : List Nat
  corruptServers : List Nat
  records : List (CredentialRecord Attr)
  usedChallenges : List Bytes
  toprfApprovals : List (Nat × ToprfTicket)
  oprfTable : List (ToprfPoint × O)
  oprfCharges : List ToprfTicket

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
    usedChallenges := []
    toprfApprovals := []
    oprfTable := []
    oprfCharges := [] }

/-- Port discipline: a command is admitted on the port of the party it is attributed to, or on the
    adversary port when that party is corrupt. Evaluation requests may come from anyone. -/
@[expose] def IdealCredState.speaksFor {Attr O : Type} (st : IdealCredState Attr O)
    (port : CredPort) : CredCommand Attr → Bool
  | .issue _ _ _ => decide (port = .issuer) || (decide (port = .adversary) && st.issuerCorrupt)
  | .advanceEpoch _ _ =>
    decide (port = .issuer) || (decide (port = .adversary) && st.issuerCorrupt)
  | .present h _ _ =>
    decide (port = .holder h) || (decide (port = .adversary) && decide (h ∈ st.corruptHolders))
  | .approveToprf i _ =>
    decide (port = .server i) || (decide (port = .adversary) && decide (i ∈ st.corruptServers))
  | .evalToprf _ _ => true

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
  decide (stmt.challengeNonce ∉ st.usedChallenges) &&
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
      some ({ st with usedChallenges := stmt.challengeNonce :: st.usedChallenges },
            .presentationVerdict true)
    else some (st, .presentationVerdict false)
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
              ({ st with usedChallenges := stmt.challengeNonce :: st.usedChallenges },
               IdealCredOutput.presentationVerdict true)
            else (st, IdealCredOutput.presentationVerdict false)) := by
  cases hC : st.presentAccepts h cid stmt with
  | false => simp only [credExec, hC, Bool.false_eq_true, ↓reduceIte]
  | true => simp only [credExec, hC, ↓reduceIte]

theorem credExec_present_true_inv {h cid : Nat} {stmt : CredentialStatement Attr}
    (hExec : credExec cfg st (.present h cid stmt) = some (st', .presentationVerdict true)) :
    st.presentAccepts h cid stmt = true ∧
    st' = { st with usedChallenges := stmt.challengeNonce :: st.usedChallenges } := by
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

/-- The output of an accepted input determines the kind of command that produced it. -/
theorem idealCredStep_output_command {port : CredPort} {cmd : CredCommand Attr}
    (hStep : idealCredStep cfg st (port, cmd) = some (st', out)) :
    match out with
    | .issued _ => ∃ h attrs newRoot, cmd = .issue h attrs newRoot
    | .epochAdvanced _ => ∃ newEpoch newRoot, cmd = .advanceEpoch newEpoch newRoot
    | .presentationVerdict _ => ∃ h cid stmt, cmd = .present h cid stmt
    | .toprfApproved => ∃ i t, cmd = .approveToprf i t
    | .toprfEvaluated _ => ∃ t input, cmd = .evalToprf t input := by
  have hExec := (idealCredStep_inv hStep).2
  cases cmd with
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

/-! ## 4. Reachable-state invariant -/

/-- Invariant of every reachable state: the issuer key and the corruption set are those of the
    configuration; every record has between `1` and `maxAttrs` attributes and an epoch not after
    the current one; every revealed TOPRF value is the value of `oprf`; per key, no more points
    are revealed than tickets charged, no more tickets charged than the quota, and charged
    counters strictly increase. -/
structure IdealCredInv {Attr O : Type} (cfg : IdealCredConfig O)
    (st : IdealCredState Attr O) : Prop where
  issuerPk_eq : st.issuerPk = cfg.issuerPk
  issuerCorrupt_eq : st.issuerCorrupt = cfg.issuerCorrupt
  corruptHolders_eq : st.corruptHolders = cfg.corruptHolders
  corruptServers_eq : st.corruptServers = cfg.corruptServers
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
  | issue h attrs newRoot =>
    obtain ⟨hAcc, hSt, _⟩ := credExec_issue_inv hExec
    simp only [IdealCredState.issueAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
    obtain ⟨⟨hPos, hMax⟩, _⟩ := hAcc
    subst hSt
    refine ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_eq, hInv.corruptHolders_eq,
      hInv.corruptServers_eq, fun r hr => ?_, hInv.table_graph, hInv.table_charged,
      hInv.charges_budget, hInv.charges_fresh⟩
    rcases List.mem_append.mp hr with hOld | hNew
    · exact hInv.records_wf r hOld
    · rw [List.mem_singleton.mp hNew]
      exact ⟨hPos, hMax, Nat.le_refl _⟩
  | advanceEpoch newEpoch newRoot =>
    obtain ⟨hLt, hSt, _⟩ := credExec_advanceEpoch_inv hExec
    subst hSt
    refine ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_eq, hInv.corruptHolders_eq,
      hInv.corruptServers_eq, fun r hr => ?_, hInv.table_graph, hInv.table_charged,
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
      exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_eq, hInv.corruptHolders_eq,
        hInv.corruptServers_eq, hInv.records_wf, hInv.table_graph, hInv.table_charged,
        hInv.charges_budget, hInv.charges_fresh⟩
  | approveToprf i t =>
    obtain ⟨_, _, hSt, _⟩ := credExec_approveToprf_inv hExec
    subst hSt
    exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_eq, hInv.corruptHolders_eq,
      hInv.corruptServers_eq, hInv.records_wf, hInv.table_graph, hInv.table_charged,
      hInv.charges_budget, hInv.charges_fresh⟩
  | evalToprf t input =>
    obtain ⟨hAcc, hCase⟩ := credExec_evalToprf_inv hExec
    obtain ⟨hBudget, hFresh⟩ := idealCredInv_toprf_charge hInv hAcc
    rcases hCase with ⟨o, _, hSt, _⟩ | ⟨hSt, _⟩
    · subst hSt
      exact ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_eq, hInv.corruptHolders_eq,
        hInv.corruptServers_eq, hInv.records_wf, hInv.table_graph,
        fun k => credCountP_le_cons _ t _ _ (hInv.table_charged k), hBudget, hFresh⟩
    · subst hSt
      refine ⟨hInv.issuerPk_eq, hInv.issuerCorrupt_eq, hInv.corruptHolders_eq,
        hInv.corruptServers_eq, hInv.records_wf, fun e he => ?_,
        fun k => credCountP_cons_congr _ _ _ t _ _ rfl (hInv.table_charged k), hBudget, hFresh⟩
      rcases List.mem_cons.mp he with hNew | hOld
      · rw [hNew]
      · exact hInv.table_graph e hOld

/-- `IdealCredInv` holds in every reachable state. -/
theorem idealCredInv_reachable {Attr O : Type} [DecidableEq Attr] {cfg : IdealCredConfig O}
    {st : IdealCredState Attr O}
    (hReach : (idealCredMachine (Attr := Attr) cfg).Reachable st) : IdealCredInv cfg st := by
  obtain ⟨s₀, tr, hInit, hTr⟩ := hReach
  have h₀ : IdealCredInv cfg s₀ := by
    have hEq : s₀ = IdealCredState.empty cfg := hInit
    rw [hEq]
    exact ⟨rfl, rfl, rfl, rfl, (fun _ hr => nomatch hr), (fun _ he => nomatch he),
      (fun _ => Nat.le_refl _), (fun _ => Nat.zero_le _), List.Pairwise.nil⟩
  clear hInit
  induction hTr with
  | nil _ => exact h₀
  | @accept s s' sf inp out rest hStep _ ih =>
    obtain ⟨port, cmd⟩ := inp
    exact ih (idealCredInv_exec h₀ (idealCredStep_inv hStep).2)
  | reject _ _ _ ih => exact ih h₀

/-! ## 5. Provenance over traces -/

/-- One accepted input: the corruption set is unchanged; a new record comes from this very input
    being an issuer-port issuance, unless the issuer is corrupt; a new approval comes from this
    very input being an approval on that server's port, unless the server is corrupt. -/
theorem idealCredStep_provenance {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    {st st' : IdealCredState Attr O} {inp : IdealCredInput Attr} {out : IdealCredOutput O}
    (hStep : idealCredStep cfg st inp = some (st', out)) :
    (st'.issuerCorrupt = st.issuerCorrupt ∧ st'.corruptHolders = st.corruptHolders ∧
      st'.corruptServers = st.corruptServers) ∧
    (∀ r ∈ st'.records, r ∈ st.records ∨ st.issuerCorrupt = true ∨
      (inp, out) = ((CredPort.issuer, CredCommand.issue r.holder r.attrs r.root),
        IdealCredOutput.issued r.credId)) ∧
    (∀ a ∈ st'.toprfApprovals, a ∈ st.toprfApprovals ∨ a.1 ∈ st.corruptServers ∨
      (inp, out) = ((CredPort.server a.1, CredCommand.approveToprf a.1 a.2),
        IdealCredOutput.toprfApproved)) := by
  obtain ⟨port, cmd⟩ := inp
  obtain ⟨hSpeak, hExec⟩ := idealCredStep_inv hStep
  cases cmd with
  | issue h attrs newRoot =>
    obtain ⟨_, hSt, hOut⟩ := credExec_issue_inv hExec
    simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hSpeak
    subst hSt
    subst hOut
    refine ⟨⟨rfl, rfl, rfl⟩, fun r hr => ?_, fun a ha => Or.inl ha⟩
    rcases List.mem_append.mp hr with hOld | hNew
    · exact Or.inl hOld
    · rcases hSpeak with hP | ⟨_, hC⟩
      · rw [List.mem_singleton.mp hNew, hP]
        exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl hC)
  | advanceEpoch newEpoch newRoot =>
    obtain ⟨_, hSt, _⟩ := credExec_advanceEpoch_inv hExec
    subst hSt
    exact ⟨⟨rfl, rfl, rfl⟩, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
  | present h cid stmt =>
    rw [credExec_present_eq] at hExec
    cases hC : st.presentAccepts h cid stmt with
    | false =>
      simp only [hC, Bool.false_eq_true, ↓reduceIte] at hExec
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hExec)
      subst hSt
      exact ⟨⟨rfl, rfl, rfl⟩, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
    | true =>
      simp only [hC, ↓reduceIte] at hExec
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hExec)
      subst hSt
      exact ⟨⟨rfl, rfl, rfl⟩, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
  | approveToprf i t =>
    obtain ⟨_, _, hSt, hOut⟩ := credExec_approveToprf_inv hExec
    simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hSpeak
    subst hSt
    subst hOut
    refine ⟨⟨rfl, rfl, rfl⟩, fun r hr => Or.inl hr, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with hNew | hOld
    · rcases hSpeak with hP | ⟨_, hC⟩
      · rw [hNew, hP]
        exact Or.inr (Or.inr rfl)
      · rw [hNew]
        exact Or.inr (Or.inl hC)
    · exact Or.inl hOld
  | evalToprf t input =>
    obtain ⟨_, hCase⟩ := credExec_evalToprf_inv hExec
    rcases hCase with ⟨o, _, hSt, _⟩ | ⟨hSt, _⟩
    · subst hSt
      exact ⟨⟨rfl, rfl, rfl⟩, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
    · subst hSt
      exact ⟨⟨rfl, rfl, rfl⟩, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩

/-- Along any run: corruption is static; every record of the final state was already present,
    or the issuer is corrupt, or the run contains its issuer-port issuance; every approval was
    already present, or its server is corrupt, or the run contains it on that server's port. -/
theorem idealCred_trace_provenance {Attr O : Type} [DecidableEq Attr] (cfg : IdealCredConfig O)
    {s st : IdealCredState Attr O} {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (hTr : (idealCredMachine cfg).ValidTrace s tr st) :
    (st.issuerCorrupt = s.issuerCorrupt ∧ st.corruptHolders = s.corruptHolders ∧
      st.corruptServers = s.corruptServers) ∧
    (∀ r ∈ st.records, r ∈ s.records ∨ s.issuerCorrupt = true ∨
      ((CredPort.issuer, CredCommand.issue r.holder r.attrs r.root),
        IdealCredOutput.issued r.credId) ∈ tr) ∧
    (∀ a ∈ st.toprfApprovals, a ∈ s.toprfApprovals ∨ a.1 ∈ s.corruptServers ∨
      ((CredPort.server a.1, CredCommand.approveToprf a.1 a.2),
        IdealCredOutput.toprfApproved) ∈ tr) := by
  induction hTr with
  | nil _ => exact ⟨⟨rfl, rfl, rfl⟩, fun r hr => Or.inl hr, fun a ha => Or.inl ha⟩
  | @accept s s' sf inp out rest hStep _ ih =>
    obtain ⟨⟨hI, hH, hS⟩, hRec, hApp⟩ := ih
    obtain ⟨⟨hI', hH', hS'⟩, hRec', hApp'⟩ := idealCredStep_provenance cfg hStep
    refine ⟨⟨hI.trans hI', hH.trans hH', hS.trans hS'⟩, fun r hr => ?_, fun a ha => ?_⟩
    · rcases hRec r hr with h1 | h2 | h3
      · rcases hRec' r h1 with g1 | g2 | g3
        · exact Or.inl g1
        · exact Or.inr (Or.inl g2)
        · exact Or.inr (Or.inr (g3 ▸ List.Mem.head _))
      · exact Or.inr (Or.inl (hI' ▸ h2))
      · exact Or.inr (Or.inr (List.Mem.tail _ h3))
    · rcases hApp a ha with h1 | h2 | h3
      · rcases hApp' a h1 with g1 | g2 | g3
        · exact Or.inl g1
        · exact Or.inr (Or.inl g2)
        · exact Or.inr (Or.inr (g3 ▸ List.Mem.head _))
      · exact Or.inr (Or.inl (hS' ▸ h2))
      · exact Or.inr (Or.inr (List.Mem.tail _ h3))
  | reject _ _ _ ih => exact ih

/-- **Issuance provenance.** Every record of a run from the initial state was created by an
    issuer-port issuance event of that run, naming its holder, attributes and root and answered
    with its identifier — unless the issuer is corrupt. -/
theorem idealCredMachine_record_provenance {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s₀ st : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)}
    (hInit : (idealCredMachine cfg).Init s₀) (hTr : (idealCredMachine cfg).ValidTrace s₀ tr st)
    (r : CredentialRecord Attr) (hr : r ∈ st.records) :
    cfg.issuerCorrupt = true ∨
    ((CredPort.issuer, CredCommand.issue r.holder r.attrs r.root),
      IdealCredOutput.issued r.credId) ∈ tr := by
  have hEq : s₀ = IdealCredState.empty cfg := hInit
  subst hEq
  rcases (idealCred_trace_provenance cfg hTr).2.1 r hr with h | h | h
  · exact nomatch h
  · exact Or.inl h
  · exact Or.inr h

/-- An accepted issuance arrived on the issuer port, or on the adversary port with a corrupt
    issuer, and the credential has between `1` and `maxAttrs` attributes. -/
theorem idealCredMachine_issuance_authenticated {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st st' : IdealCredState Attr O} {port : CredPort} {h : Nat}
    {attrs : List Attr} {newRoot : Digest256} {out : IdealCredOutput O}
    (hReach : (idealCredMachine cfg).Reachable st)
    (hStep : (idealCredMachine cfg).step st (port, .issue h attrs newRoot) = some (st', out)) :
    (port = CredPort.issuer ∨ (port = CredPort.adversary ∧ cfg.issuerCorrupt = true)) ∧
    0 < attrs.length ∧ attrs.length ≤ pqCredentialProfile.maxAttrs := by
  obtain ⟨hSpeak, hExec⟩ := idealCredStep_inv hStep
  obtain ⟨hAcc, _, _⟩ := credExec_issue_inv hExec
  simp only [IdealCredState.speaksFor, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hSpeak
  simp only [IdealCredState.issueAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
  rw [(idealCredInv_reachable hReach).issuerCorrupt_eq] at hSpeak
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
    stmt.challengeNonce ∉ st.usedChallenges ∧
    stmt.challengeNonce ∈ st'.usedChallenges ∧
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
  exact ⟨hSpeak, hPk, hEp, hRoot, hFresh, List.Mem.head _, hIdx, r, hr, hId, hH, hREp, hMatch⟩

/-- **Possession provenance.** If, after a run from the initial state, a presentation of
    credential `cid` by holder `h` is accepted, then it arrived on the port of `h` (or `h` is
    corrupt), and `h` owns a record with that identifier, of the statement's epoch, satisfying the
    statement, which an issuer-port event of the run issued to `h` (or the issuer is corrupt). -/
theorem idealCredMachine_presentation_provenance {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s₀ st st' : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort} {h cid : Nat}
    {stmt : CredentialStatement Attr}
    (hInit : (idealCredMachine cfg).Init s₀) (hTr : (idealCredMachine cfg).ValidTrace s₀ tr st)
    (hStep : (idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st', .presentationVerdict true)) :
    (port = CredPort.holder h ∨ (port = CredPort.adversary ∧ h ∈ cfg.corruptHolders)) ∧
    stmt.issuerPk = cfg.issuerPk ∧
    ∃ r ∈ st.records, r.credId = cid ∧ r.holder = h ∧ r.epoch = stmt.epoch ∧
      CredentialMatchesAttributes stmt r.attrs = true ∧
      (cfg.issuerCorrupt = true ∨
        ((CredPort.issuer, CredCommand.issue h r.attrs r.root),
          IdealCredOutput.issued cid) ∈ tr) := by
  have hInv := idealCredInv_reachable ⟨s₀, tr, hInit, hTr⟩
  obtain ⟨hPort, hPk, hEp, _, _, _, _, r, hr, hId, hH, hREp, hMatch⟩ :=
    idealCredMachine_presentation_sound cfg hStep
  have hProv := idealCredMachine_record_provenance cfg hInit hTr r hr
  rw [hInv.corruptHolders_eq] at hPort
  rw [hId, hH] at hProv
  exact ⟨hPort, hPk.trans hInv.issuerPk_eq, r, hr, hId, hH, hREp.trans hEp.symm, hMatch, hProv⟩

/-! ### Rejection of unauthenticated behaviour -/

/-- Tooth (audit #2): with an honest issuer, an issuance arriving on any port other than the
    issuer's — in particular the adversary's — is rejected in every reachable state, whatever
    holder, attributes and root it names. -/
theorem idealCredMachine_rejects_foreign_issue {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st : IdealCredState Attr O} (port : CredPort) (h : Nat)
    (attrs : List Attr) (newRoot : Digest256)
    (hReach : (idealCredMachine cfg).Reachable st)
    (hHonest : cfg.issuerCorrupt = false) (hPort : ¬ (port = CredPort.issuer)) :
    (idealCredMachine cfg).step st (port, .issue h attrs newRoot) = none := by
  apply idealCredStep_eq_none_of_not_speaksFor
  simp only [IdealCredState.speaksFor, (idealCredInv_reachable hReach).issuerCorrupt_eq, hHonest,
    decide_eq_false hPort, Bool.and_false, Bool.or_false]

/-- Tooth (audit #2): with an honest issuer, an epoch / accumulator-root update arriving on any
    other port is rejected in every reachable state. -/
theorem idealCredMachine_rejects_foreign_epoch_advance {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st : IdealCredState Attr O} (port : CredPort) (newEpoch : Nat)
    (newRoot : Digest256)
    (hReach : (idealCredMachine (Attr := Attr) cfg).Reachable st)
    (hHonest : cfg.issuerCorrupt = false) (hPort : ¬ (port = CredPort.issuer)) :
    (idealCredMachine cfg).step st (port, .advanceEpoch newEpoch newRoot) = none := by
  apply idealCredStep_eq_none_of_not_speaksFor
  simp only [IdealCredState.speaksFor, (idealCredInv_reachable hReach).issuerCorrupt_eq, hHonest,
    decide_eq_false hPort, Bool.and_false, Bool.or_false]

/-- Tooth (audit #10): a credential with zero attributes is never issued, on any port. -/
theorem idealCredMachine_rejects_empty_credential {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) (st : IdealCredState Attr O) (port : CredPort) (h : Nat)
    (attrs : List Attr) (newRoot : Digest256) (hEmpty : attrs.length = 0) :
    (idealCredMachine cfg).step st (port, .issue h attrs newRoot) = none := by
  apply idealCredStep_eq_none_of_exec
  have hAcc : st.issueAccepts attrs = false := by
    simp only [IdealCredState.issueAccepts, hEmpty, Nat.lt_irrefl, decide_false, Bool.false_and]
  simp only [credExec, hAcc, Bool.false_eq_true, ↓reduceIte]

/-- Tooth (audit #2): a presentation in the name of an honest holder arriving on any port other
    than that holder's is rejected in every reachable state, whatever credential it names. -/
theorem idealCredMachine_rejects_foreign_presentation {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st : IdealCredState Attr O} (port : CredPort) (h cid : Nat)
    (stmt : CredentialStatement Attr)
    (hReach : (idealCredMachine cfg).Reachable st)
    (hHonest : h ∉ cfg.corruptHolders) (hPort : ¬ (port = CredPort.holder h)) :
    (idealCredMachine cfg).step st (port, .present h cid stmt) = none := by
  apply idealCredStep_eq_none_of_not_speaksFor
  simp only [IdealCredState.speaksFor, (idealCredInv_reachable hReach).corruptHolders_eq,
    decide_eq_false hHonest, decide_eq_false hPort, Bool.and_false, Bool.or_false]

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
    (hSame : stmt'.challengeNonce = stmt.challengeNonce)
    (hFirst : (idealCredMachine cfg).step st (port, .present h cid stmt) =
      some (st₁, .presentationVerdict true)) :
    ¬ ((idealCredMachine cfg).step st₁ (port', .present h' cid' stmt') =
      some (st₂, .presentationVerdict true)) := by
  intro hSecond
  obtain ⟨_, _, _, _, _, hBurned, _⟩ := idealCredMachine_presentation_sound cfg hFirst
  obtain ⟨_, _, _, _, hFresh, _⟩ := idealCredMachine_presentation_sound cfg hSecond
  rw [hSame] at hFresh
  exact hFresh hBurned

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

/-- **TOPRF evaluation provenance.** If, after a run from the initial state with at most
    `toprfMaxCorrupt` corrupt servers, an evaluation is answered, then the answer is the value of
    the keyed function at `(keyId, epoch, input)`, at least `toprfOnlineServers` distinct servers
    approved the ticket, and the run contains an approval of that ticket on the port of an honest
    committee server. -/
theorem idealCredMachine_toprf_provenance {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {s₀ st st' : IdealCredState Attr O}
    {tr : List (IdealCredInput Attr × IdealCredOutput O)} {port : CredPort} {t : ToprfTicket}
    {input : Bytes} {out : IdealCredOutput O}
    (hInit : (idealCredMachine cfg).Init s₀) (hTr : (idealCredMachine cfg).ValidTrace s₀ tr st)
    (hCorrupt : cfg.corruptServerCount ≤ pqCredentialProfile.toprfMaxCorrupt)
    (hStep : (idealCredMachine cfg).step st (port, .evalToprf t input) = some (st', out)) :
    out = .toprfEvaluated (cfg.oprf ⟨t.keyId, t.epoch, input⟩) ∧
    pqCredentialProfile.toprfOnlineServers ≤ st.approvalCount t ∧
    ∃ i : Nat, i < pqCredentialProfile.toprfServers ∧ i ∉ cfg.corruptServers ∧
      ((CredPort.server i, CredCommand.approveToprf i t), IdealCredOutput.toprfApproved) ∈ tr := by
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
        (fun i => decide (i ∈ cfg.corruptServers)) <
      (List.range pqCredentialProfile.toprfServers).countP
        (fun i => decide ((i, t) ∈ st.toprfApprovals)) :=
    Nat.lt_of_le_of_lt hCorrupt (Nat.lt_of_lt_of_le hGap hQuorum)
  obtain ⟨i, hi, hApproved, hHonest⟩ := credExists_of_countP_lt _ _ _ hLt
  have hMem : (i, t) ∈ st.toprfApprovals := of_decide_eq_true hApproved
  have hNotCorrupt : i ∉ cfg.corruptServers := of_decide_eq_false hHonest
  have hEq : s₀ = IdealCredState.empty cfg := hInit
  subst hEq
  refine ⟨hOut, hQuorum, i, List.mem_range.mp hi, hNotCorrupt, ?_⟩
  rcases (idealCred_trace_provenance cfg hTr).2.2 (i, t) hMem with h | h | h
  · exact nomatch h
  · exact absurd h hNotCorrupt
  · exact h

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

/-- Tooth: an approval in the name of an honest server arriving on any other port is rejected in
    every reachable state, so the adversary cannot manufacture a quorum. -/
theorem idealCredMachine_rejects_foreign_approval {Attr O : Type} [DecidableEq Attr]
    (cfg : IdealCredConfig O) {st : IdealCredState Attr O} (port : CredPort) (i : Nat)
    (t : ToprfTicket)
    (hReach : (idealCredMachine (Attr := Attr) cfg).Reachable st)
    (hHonest : i ∉ cfg.corruptServers) (hPort : ¬ (port = CredPort.server i)) :
    (idealCredMachine cfg).step st (port, .approveToprf i t) = none := by
  apply idealCredStep_eq_none_of_not_speaksFor
  simp only [IdealCredState.speaksFor, (idealCredInv_reachable hReach).corruptServers_eq,
    decide_eq_false hHonest, decide_eq_false hPort, Bool.and_false, Bool.or_false]

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

/-- Demo configuration over `Nat` attributes and outputs: holder `9` and server `4` are corrupt,
    the issuer is corrupt iff `issuerCorrupt`, and each key has a quota of two. -/
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
    [(.issuer, .issue 1 [11, 22] 1#256)]).1

/-- Statement against the demo state disclosing `disclosed`. -/
def idealCredDemoStatement (disclosed : List (Nat × Nat)) : CredentialStatement Nat :=
  { issuerPk := [1], epoch := 0, accumulatorRoot := 1#256, disclosed := disclosed,
    challengeNonce := [9] }

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

/-- Caveat: the guarantees are relative to the corruption set. With a corrupt issuer the very
    adversary-port issuance of invented attributes rejected above is accepted. -/
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

#verify_constructive
  Qsag.Spec.idealCredInv_exec
  Qsag.Spec.idealCredInv_reachable
  Qsag.Spec.idealCredStep_provenance
  Qsag.Spec.idealCredStep_output_command
  Qsag.Spec.idealCredStep_issuer_issues_at_init
  Qsag.Spec.idealCred_trace_provenance
  Qsag.Spec.idealCredMachine_record_provenance
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

end Qsag.Spec
end
