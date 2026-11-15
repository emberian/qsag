module
/-
# Qsag.Spec.IdealCred — Ideal Selective-Disclosure Anonymous Credential & TOPRF Specification

Layer-0 ideal functionality for `crates/qsag-cred/src/blind_vc.rs` (`PiBlindVc`: per-epoch Poseidon2
accumulator, `N = 256` seed-tree MPC-in-the-head selective-disclosure presentations) and the
replicated threshold OPRF of `crates/qsag-cred/src/voprf.rs`.

The machine is parameterized by a `CredAuthority`: the cryptographic relations of the scheme
(`opens`, `issuerAuthorizes`, `serverApproves`) and the ideal keyed function `oprf`. No law is
assumed of them; unforgeability of the authorization relations is the obligation of whoever
instantiates them. The interfaces are separated by `IdealCredInput.port`:

1. **Issuer** (`.issue`, `.advanceEpoch`): every accepted transition carries an authorization
   accepted by `issuerAuthorizes` for the exact `IssuerAction` it performs (epoch, leaf index,
   previous root, leaf, attributes, new root). A credential has between `1` and `maxAttrs`
   attributes. Each enrolled `CredentialRecord` keeps its authorization, so
   `idealCredMachine_presentation_authenticated` traces every accepted presentation of a reachable
   state back to an issuer-authorized record.
2. **Holder → verifier** (`.present`): the holder supplies a possession secret; the presentation is
   accepted only if that secret `opens` the leaf of a record of the *current* epoch whose attributes
   satisfy the statement, the statement names the current issuer key, epoch and accumulator root,
   and its challenge nonce is fresh. Epoch rotation retires every earlier credential.
   The successor state and the verdict do not depend on which eligible credential was shown
   (`idealCredMachine_selective_disclosure_privacy`), also along whole input sequences
   (`idealCredMachine_presentation_trace_unlinkable`).
3. **TOPRF client** (`.evalToprf`): a ticket `(keyId, epoch, counter)` approved by at least
   `toprfThreshold` distinct servers, with a strictly increasing counter and within the per-key
   quota, releases the table value of `(keyId, epoch, input)`; a fresh point is entered as
   `oprf (keyId, epoch, input)`. Acceptance and charging are independent of the input
   (`idealCredMachine_toprf_oblivious`), and at most `oprfQuota` points per key are ever revealed
   (`idealCredMachine_toprf_budget`).

Corruption is static: the machine has no corruption transition. The adversary is any caller of the
holder and client interfaces, and of the issuer interface without a valid authorization.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## 1. Statements, authority relations, records -/

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

/-- The two state changes only the issuer may make, with everything they bind. -/
inductive IssuerAction (Attr Leaf : Type) where
  /-- Append `leaf` with `attrs` at position `leafIndex` of epoch `epoch`, moving the accumulator
      root from `prevRoot` to `newRoot`. -/
  | issue (epoch leafIndex : Nat) (prevRoot : Digest256) (leaf : Leaf) (attrs : List Attr)
      (newRoot : Digest256)
  /-- Retire epoch `epoch` and open `newEpoch` with accumulator root `newRoot`. -/
  | advanceEpoch (epoch newEpoch : Nat) (prevRoot newRoot : Digest256)

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

/-- Cryptographic relations and ideal function the credential functionality is parameterized by.
    * `opens secret leaf`: the holder secret is an opening of the enrolled leaf commitment;
    * `issuerAuthorizes pk action auth`: `auth` is the issuer's authorization of exactly `action`
      under `pk` (in `blind_vc.rs`, the threshold-issued receipt and the `IssuerRootAttestation`);
    * `serverApproves i ticket auth`: TOPRF server `i` approved and durably reserved `ticket`
      (`CounterStore::reserve`, `voprf.rs:125`);
    * `oprf`: the keyed function; `oprfQuota`: the enrolled per-key evaluation quota. -/
structure CredAuthority (Attr : Type) : Type 1 where
  Leaf : Type
  HolderSecret : Type
  IssuerAuth : Type
  ServerAuth : Type
  OprfOut : Type
  opens : HolderSecret → Leaf → Bool
  issuerAuthorizes : Bytes → IssuerAction Attr Leaf → IssuerAuth → Bool
  serverApproves : Nat → ToprfTicket → ServerAuth → Bool
  oprf : ToprfPoint → OprfOut
  oprfQuota : Nat

/-- An enrolled credential together with the issuance it came from — the `IssuerAction.issue`
    with these `epoch`, `leafIndex`, `prevRoot`, `leaf`, `attrs`, `root` — and its authorization. -/
structure CredentialRecord {Attr : Type} (A : CredAuthority Attr) where
  leaf : A.Leaf
  attrs : List Attr
  epoch : Nat
  leafIndex : Nat
  prevRoot : Digest256
  root : Digest256
  auth : A.IssuerAuth

/-! ## 2. State, interfaces, transition -/

/-- Ideal credential state: issuer key, current accumulator epoch and root, the number of leaves
    of the current epoch, all enrolled records, consumed verifier challenges, the revealed part of
    the TOPRF graph and the charged TOPRF tickets (newest first). -/
structure IdealCredState {Attr : Type} (A : CredAuthority Attr) where
  issuerPk : Bytes
  epoch : Nat
  accumulatorRoot : Digest256
  issuedThisEpoch : Nat
  records : List (CredentialRecord A)
  usedChallenges : List Bytes
  oprfTable : List (ToprfPoint × A.OprfOut)
  oprfCharges : List ToprfTicket

@[expose] def IdealCredState.empty {Attr : Type} {A : CredAuthority Attr}
    (pk : Bytes) (epoch₀ : Nat) (root₀ : Digest256) : IdealCredState A :=
  { issuerPk := pk
    epoch := epoch₀
    accumulatorRoot := root₀
    issuedThisEpoch := 0
    records := []
    usedChallenges := []
    oprfTable := []
    oprfCharges := [] }

/-- Commands of `IdealCred`. `.issue` and `.advanceEpoch` carry an issuer authorization;
    `.present` carries the holder's possession secret, never attributes or a registry position;
    `.evalToprf` carries the server approvals of its ticket. -/
inductive IdealCredInput {Attr : Type} (A : CredAuthority Attr) where
  | issue (leaf : A.Leaf) (attrs : List Attr) (newRoot : Digest256) (auth : A.IssuerAuth)
  | advanceEpoch (newEpoch : Nat) (newRoot : Digest256) (auth : A.IssuerAuth)
  | present (secret : A.HolderSecret) (stmt : CredentialStatement Attr)
  | evalToprf (ticket : ToprfTicket) (input : Bytes) (approvals : List (Nat × A.ServerAuth))

/-- The three interfaces of the functionality. -/
inductive CredPort where
  | issuer
  | holder
  | toprfClient
  deriving DecidableEq, Repr

/-- The interface a command arrives on. -/
@[expose] def IdealCredInput.port {Attr : Type} {A : CredAuthority Attr} : IdealCredInput A → CredPort
  | .issue _ _ _ _ => .issuer
  | .advanceEpoch _ _ _ => .issuer
  | .present _ _ => .holder
  | .evalToprf _ _ _ => .toprfClient

/-- Outputs emitted by `IdealCred`. -/
inductive IdealCredOutput (O : Type) where
  | issued (leafIndex : Nat)
  | epochAdvanced (epoch : Nat)
  | presentationVerdict (ok : Bool)
  | toprfEvaluated (out : O)

/-- Issuance gate: positive arity at most `maxAttrs`, accumulator capacity `2 ^ accumulatorDepth`
    per epoch, and an authorization of this exact issuance at the current epoch, index and root. -/
@[expose] def IdealCredState.issueAccepts {Attr : Type} {A : CredAuthority Attr}
    (st : IdealCredState A) (leaf : A.Leaf) (attrs : List Attr) (newRoot : Digest256)
    (auth : A.IssuerAuth) : Bool :=
  decide (0 < attrs.length) &&
  decide (attrs.length ≤ pqCredentialProfile.maxAttrs) &&
  decide (st.issuedThisEpoch < 2 ^ pqCredentialProfile.accumulatorDepth) &&
  A.issuerAuthorizes st.issuerPk
    (.issue st.epoch st.issuedThisEpoch st.accumulatorRoot leaf attrs newRoot) auth

/-- Epoch-rotation gate: strictly increasing epoch and an authorization of this exact rotation. -/
@[expose] def IdealCredState.advanceAccepts {Attr : Type} {A : CredAuthority Attr}
    (st : IdealCredState A) (newEpoch : Nat) (newRoot : Digest256) (auth : A.IssuerAuth) : Bool :=
  decide (st.epoch < newEpoch) &&
  A.issuerAuthorizes st.issuerPk
    (.advanceEpoch st.epoch newEpoch st.accumulatorRoot newRoot) auth

/-- `secret` opens a record of the current epoch whose attributes satisfy `stmt`. -/
@[expose] def IdealCredState.eligible {Attr : Type} [DecidableEq Attr] {A : CredAuthority Attr}
    (st : IdealCredState A) (secret : A.HolderSecret) (stmt : CredentialStatement Attr) : Bool :=
  st.records.any (fun r =>
    A.opens secret r.leaf && decide (r.epoch = st.epoch) &&
      CredentialMatchesAttributes stmt r.attrs)

/-- Presentation gate: the statement names the current issuer key, epoch and accumulator root,
    its challenge is fresh, and the presenter is `eligible`. -/
@[expose] def IdealCredState.presentAccepts {Attr : Type} [DecidableEq Attr] {A : CredAuthority Attr}
    (st : IdealCredState A) (secret : A.HolderSecret) (stmt : CredentialStatement Attr) : Bool :=
  decide (stmt.issuerPk = st.issuerPk) &&
  decide (stmt.epoch = st.epoch) &&
  decide (stmt.accumulatorRoot = st.accumulatorRoot) &&
  decide (stmt.challengeNonce ∉ st.usedChallenges) &&
  st.eligible secret stmt

/-- TOPRF gate: at least `toprfThreshold` distinct servers with index below `toprfServers` approved
    the ticket, the ticket is for the current epoch, the key has quota left, and the counter exceeds
    every counter already charged to the key. -/
@[expose] def IdealCredState.toprfAccepts {Attr : Type} {A : CredAuthority Attr}
    (st : IdealCredState A) (t : ToprfTicket) (approvals : List (Nat × A.ServerAuth)) : Bool :=
  decide (approvals.map Prod.fst).Nodup &&
  approvals.all (fun p =>
    decide (p.1 < pqCredentialProfile.toprfServers) && A.serverApproves p.1 t p.2) &&
  decide (pqCredentialProfile.toprfThreshold ≤ approvals.length) &&
  decide (t.epoch = st.epoch) &&
  decide (st.oprfCharges.countP (fun c => decide (c.keyId = t.keyId)) < A.oprfQuota) &&
  st.oprfCharges.all (fun c => !decide (c.keyId = t.keyId) || decide (c.counter < t.counter))

/-- Transition function of `IdealCred`. Issuer and TOPRF commands that fail their gate are
    rejected; a presentation always yields a verdict and burns its challenge only when accepted. -/
@[expose] def idealCredStep {Attr : Type} [DecidableEq Attr] (A : CredAuthority Attr)
    (st : IdealCredState A) :
    IdealCredInput A → Option (IdealCredState A × IdealCredOutput A.OprfOut)
  | .issue leaf attrs newRoot auth =>
    if st.issueAccepts leaf attrs newRoot auth then
      some ({ st with
              records := st.records ++
                [{ leaf := leaf, attrs := attrs, epoch := st.epoch,
                   leafIndex := st.issuedThisEpoch, prevRoot := st.accumulatorRoot,
                   root := newRoot, auth := auth }]
              accumulatorRoot := newRoot
              issuedThisEpoch := st.issuedThisEpoch + 1 },
            .issued st.issuedThisEpoch)
    else none
  | .advanceEpoch newEpoch newRoot auth =>
    if st.advanceAccepts newEpoch newRoot auth then
      some ({ st with epoch := newEpoch, accumulatorRoot := newRoot, issuedThisEpoch := 0 },
            .epochAdvanced newEpoch)
    else none
  | .present secret stmt =>
    if st.presentAccepts secret stmt then
      some ({ st with usedChallenges := stmt.challengeNonce :: st.usedChallenges },
            .presentationVerdict true)
    else some (st, .presentationVerdict false)
  | .evalToprf t input approvals =>
    if st.toprfAccepts t approvals then
      match st.oprfTable.find? (fun e => decide (e.1 = ⟨t.keyId, t.epoch, input⟩)) with
      | some e =>
        some ({ st with oprfCharges := t :: st.oprfCharges }, .toprfEvaluated e.2)
      | none =>
        some ({ st with
                oprfCharges := t :: st.oprfCharges
                oprfTable := (⟨t.keyId, t.epoch, input⟩, A.oprf ⟨t.keyId, t.epoch, input⟩) ::
                  st.oprfTable },
              .toprfEvaluated (A.oprf ⟨t.keyId, t.epoch, input⟩))
    else none

/-- Reactive `Machine` for `IdealCred`, started at issuer key `pk₀`, epoch `epoch₀` and
    accumulator root `root₀` with no credential enrolled. -/
@[expose] def idealCredMachine {Attr : Type} [DecidableEq Attr] (A : CredAuthority Attr)
    (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256) :
    Machine (IdealCredState A) (IdealCredInput A) (IdealCredOutput A.OprfOut) where
  Init st := st = IdealCredState.empty pk₀ epoch₀ root₀
  step := idealCredStep A
  errStep st _ := st

/-! ## 3. Inversion of single transitions -/

theorem idealCredStep_issue_inv {Attr : Type} [DecidableEq Attr] {A : CredAuthority Attr}
    {st st' : IdealCredState A} {leaf : A.Leaf} {attrs : List Attr} {newRoot : Digest256}
    {auth : A.IssuerAuth} {out : IdealCredOutput A.OprfOut}
    (hStep : idealCredStep A st (.issue leaf attrs newRoot auth) = some (st', out)) :
    st.issueAccepts leaf attrs newRoot auth = true ∧
    st' = { st with
            records := st.records ++
              [{ leaf := leaf, attrs := attrs, epoch := st.epoch,
                 leafIndex := st.issuedThisEpoch, prevRoot := st.accumulatorRoot,
                 root := newRoot, auth := auth }]
            accumulatorRoot := newRoot
            issuedThisEpoch := st.issuedThisEpoch + 1 } ∧
    out = .issued st.issuedThisEpoch := by
  cases hC : st.issueAccepts leaf attrs newRoot auth with
  | false =>
    simp only [idealCredStep, hC, Bool.false_eq_true, ↓reduceIte] at hStep
    cases hStep
  | true =>
    simp only [idealCredStep, hC, ↓reduceIte] at hStep
    obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj hStep)
    exact ⟨rfl, hSt.symm, hOut.symm⟩

theorem idealCredStep_advanceEpoch_inv {Attr : Type} [DecidableEq Attr] {A : CredAuthority Attr}
    {st st' : IdealCredState A} {newEpoch : Nat} {newRoot : Digest256}
    {auth : A.IssuerAuth} {out : IdealCredOutput A.OprfOut}
    (hStep : idealCredStep A st (.advanceEpoch newEpoch newRoot auth) = some (st', out)) :
    st.advanceAccepts newEpoch newRoot auth = true ∧
    st' = { st with epoch := newEpoch, accumulatorRoot := newRoot, issuedThisEpoch := 0 } ∧
    out = .epochAdvanced newEpoch := by
  cases hC : st.advanceAccepts newEpoch newRoot auth with
  | false =>
    simp only [idealCredStep, hC, Bool.false_eq_true, ↓reduceIte] at hStep
    cases hStep
  | true =>
    simp only [idealCredStep, hC, ↓reduceIte] at hStep
    obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj hStep)
    exact ⟨rfl, hSt.symm, hOut.symm⟩

/-- A presentation step is determined by the presentation gate. -/
theorem idealCredStep_present_eq {Attr : Type} [DecidableEq Attr] (A : CredAuthority Attr)
    (st : IdealCredState A) (secret : A.HolderSecret) (stmt : CredentialStatement Attr) :
    idealCredStep A st (.present secret stmt) =
      some (if st.presentAccepts secret stmt then
              ({ st with usedChallenges := stmt.challengeNonce :: st.usedChallenges },
               IdealCredOutput.presentationVerdict true)
            else (st, IdealCredOutput.presentationVerdict false)) := by
  cases hC : st.presentAccepts secret stmt with
  | false => simp only [idealCredStep, hC, Bool.false_eq_true, ↓reduceIte]
  | true => simp only [idealCredStep, hC, ↓reduceIte]

theorem idealCredStep_present_true_inv {Attr : Type} [DecidableEq Attr] {A : CredAuthority Attr}
    {st st' : IdealCredState A} {secret : A.HolderSecret} {stmt : CredentialStatement Attr}
    (hStep : idealCredStep A st (.present secret stmt) = some (st', .presentationVerdict true)) :
    st.presentAccepts secret stmt = true ∧
    st' = { st with usedChallenges := stmt.challengeNonce :: st.usedChallenges } := by
  rw [idealCredStep_present_eq] at hStep
  cases hC : st.presentAccepts secret stmt with
  | false =>
    simp only [hC, Bool.false_eq_true, ↓reduceIte] at hStep
    obtain ⟨_, hOut⟩ := Prod.mk.inj (Option.some.inj hStep)
    cases hOut
  | true =>
    simp only [hC, ↓reduceIte] at hStep
    obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hStep)
    exact ⟨rfl, hSt.symm⟩

theorem idealCredStep_evalToprf_inv {Attr : Type} [DecidableEq Attr] {A : CredAuthority Attr}
    {st st' : IdealCredState A} {t : ToprfTicket} {input : Bytes}
    {approvals : List (Nat × A.ServerAuth)} {out : IdealCredOutput A.OprfOut}
    (hStep : idealCredStep A st (.evalToprf t input approvals) = some (st', out)) :
    st.toprfAccepts t approvals = true ∧
    ((∃ o : A.OprfOut, ((⟨t.keyId, t.epoch, input⟩ : ToprfPoint), o) ∈ st.oprfTable ∧
        st' = { st with oprfCharges := t :: st.oprfCharges } ∧ out = .toprfEvaluated o) ∨
     (st' = { st with
              oprfCharges := t :: st.oprfCharges
              oprfTable := (⟨t.keyId, t.epoch, input⟩, A.oprf ⟨t.keyId, t.epoch, input⟩) ::
                st.oprfTable } ∧
      out = .toprfEvaluated (A.oprf ⟨t.keyId, t.epoch, input⟩))) := by
  cases hC : st.toprfAccepts t approvals with
  | false =>
    simp only [idealCredStep, hC, Bool.false_eq_true, ↓reduceIte] at hStep
    cases hStep
  | true =>
    simp only [idealCredStep, hC, ↓reduceIte] at hStep
    refine ⟨rfl, ?_⟩
    cases hF : st.oprfTable.find? (fun e => decide (e.1 = ⟨t.keyId, t.epoch, input⟩)) with
    | some e =>
      rw [hF] at hStep
      obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj hStep)
      have hDec : decide (e.1 = (⟨t.keyId, t.epoch, input⟩ : ToprfPoint)) = true :=
        List.find?_some
          (p := fun e : ToprfPoint × A.OprfOut =>
            decide (e.1 = (⟨t.keyId, t.epoch, input⟩ : ToprfPoint))) hF
      have hKey : e.1 = ⟨t.keyId, t.epoch, input⟩ := of_decide_eq_true hDec
      have hMem : e ∈ st.oprfTable := List.mem_of_find?_eq_some hF
      refine Or.inl ⟨e.2, ?_, hSt.symm, hOut.symm⟩
      rw [← hKey]
      exact hMem
    | none =>
      rw [hF] at hStep
      obtain ⟨hSt, hOut⟩ := Prod.mk.inj (Option.some.inj hStep)
      exact Or.inr ⟨hSt.symm, hOut.symm⟩

/-! ## 4. Reachable-state invariant -/

/-- Invariant of every reachable `IdealCred` state:
    the issuer key never changes; every record was authorized by the issuer for exactly its
    issuance, has between `1` and `maxAttrs` attributes and an epoch not after the current one;
    every revealed TOPRF value is the value of `oprf`; per key, no more points are revealed than
    tickets charged, no more tickets charged than the quota, and charged counters strictly
    increase. -/
structure IdealCredInv {Attr : Type} (A : CredAuthority Attr) (pk₀ : Bytes)
    (st : IdealCredState A) : Prop where
  issuerPk_eq : st.issuerPk = pk₀
  records_authorized : ∀ r ∈ st.records,
    A.issuerAuthorizes pk₀
      (.issue r.epoch r.leafIndex r.prevRoot r.leaf r.attrs r.root) r.auth = true ∧
    0 < r.attrs.length ∧
    r.attrs.length ≤ pqCredentialProfile.maxAttrs ∧ r.epoch ≤ st.epoch
  table_graph : ∀ e ∈ st.oprfTable, e.2 = A.oprf e.1
  table_charged : ∀ k : Bytes,
    st.oprfTable.countP (fun e => decide (e.1.keyId = k)) ≤
      st.oprfCharges.countP (fun c => decide (c.keyId = k))
  charges_budget : ∀ k : Bytes,
    st.oprfCharges.countP (fun c => decide (c.keyId = k)) ≤ A.oprfQuota
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

private theorem idealCredInv_toprf_charge {Attr : Type} {A : CredAuthority Attr} {pk₀ : Bytes}
    {st : IdealCredState A} {t : ToprfTicket} {approvals : List (Nat × A.ServerAuth)}
    (hInv : IdealCredInv A pk₀ st) (hAcc : st.toprfAccepts t approvals = true) :
    (∀ k : Bytes, (t :: st.oprfCharges).countP (fun c => decide (c.keyId = k)) ≤ A.oprfQuota) ∧
    (t :: st.oprfCharges).Pairwise
      (fun newer older => newer.keyId = older.keyId → older.counter < newer.counter) := by
  simp only [IdealCredState.toprfAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
  obtain ⟨⟨_, hQuota⟩, hFresh⟩ := hAcc
  refine ⟨fun k => ?_, List.pairwise_cons.mpr ⟨fun c hc hk => ?_, hInv.charges_fresh⟩⟩
  · by_cases hk : t.keyId = k
    · rw [← hk]
      exact credCountP_cons_le_of_lt _ t _ _ hQuota
    · rw [credCountP_cons_of_false _ t _ (decide_eq_false hk)]
      exact hInv.charges_budget k
  · have h := List.all_eq_true.mp hFresh c hc
    rw [decide_eq_true hk.symm] at h
    exact of_decide_eq_true h

/-- Every accepted transition preserves `IdealCredInv`. -/
theorem idealCredInv_step {Attr : Type} [DecidableEq Attr] {A : CredAuthority Attr} {pk₀ : Bytes}
    {st st' : IdealCredState A} {inp : IdealCredInput A} {out : IdealCredOutput A.OprfOut}
    (hInv : IdealCredInv A pk₀ st) (hStep : idealCredStep A st inp = some (st', out)) :
    IdealCredInv A pk₀ st' := by
  cases inp with
  | issue leaf attrs newRoot auth =>
    obtain ⟨hAcc, hSt, _⟩ := idealCredStep_issue_inv hStep
    simp only [IdealCredState.issueAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
    obtain ⟨⟨⟨hPos, hMax⟩, _⟩, hAuth⟩ := hAcc
    rw [hInv.issuerPk_eq] at hAuth
    subst hSt
    refine ⟨hInv.issuerPk_eq, fun r hr => ?_, hInv.table_graph, hInv.table_charged,
      hInv.charges_budget, hInv.charges_fresh⟩
    rcases List.mem_append.mp hr with hOld | hNew
    · exact hInv.records_authorized r hOld
    · rw [List.mem_singleton.mp hNew]
      exact ⟨hAuth, hPos, hMax, Nat.le_refl _⟩
  | advanceEpoch newEpoch newRoot auth =>
    obtain ⟨hAcc, hSt, _⟩ := idealCredStep_advanceEpoch_inv hStep
    simp only [IdealCredState.advanceAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
    subst hSt
    refine ⟨hInv.issuerPk_eq, fun r hr => ?_, hInv.table_graph, hInv.table_charged,
      hInv.charges_budget, hInv.charges_fresh⟩
    obtain ⟨hA, hPos, hMax, hEp⟩ := hInv.records_authorized r hr
    exact ⟨hA, hPos, hMax, Nat.le_trans hEp (Nat.le_of_lt hAcc.1)⟩
  | present secret stmt =>
    rw [idealCredStep_present_eq] at hStep
    cases hC : st.presentAccepts secret stmt with
    | false =>
      simp only [hC, Bool.false_eq_true, ↓reduceIte] at hStep
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hStep)
      rw [← hSt]
      exact hInv
    | true =>
      simp only [hC, ↓reduceIte] at hStep
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hStep)
      rw [← hSt]
      exact ⟨hInv.issuerPk_eq, hInv.records_authorized, hInv.table_graph, hInv.table_charged,
        hInv.charges_budget, hInv.charges_fresh⟩
  | evalToprf t input approvals =>
    obtain ⟨hAcc, hCase⟩ := idealCredStep_evalToprf_inv hStep
    obtain ⟨hBudget, hFresh⟩ := idealCredInv_toprf_charge hInv hAcc
    rcases hCase with ⟨o, _, hSt, _⟩ | ⟨hSt, _⟩
    · subst hSt
      exact ⟨hInv.issuerPk_eq, hInv.records_authorized, hInv.table_graph,
        fun k => credCountP_le_cons _ t _ _ (hInv.table_charged k), hBudget, hFresh⟩
    · subst hSt
      refine ⟨hInv.issuerPk_eq, hInv.records_authorized, fun e he => ?_,
        fun k => credCountP_cons_congr _ _ _ t _ _ rfl (hInv.table_charged k), hBudget, hFresh⟩
      rcases List.mem_cons.mp he with hNew | hOld
      · rw [hNew]
      · exact hInv.table_graph e hOld

/-- `IdealCredInv` holds in every reachable state. -/
theorem idealCredInv_reachable {Attr : Type} [DecidableEq Attr] {A : CredAuthority Attr}
    {pk₀ : Bytes} {epoch₀ : Nat} {root₀ : Digest256} {st : IdealCredState A}
    (hReach : (idealCredMachine A pk₀ epoch₀ root₀).Reachable st) : IdealCredInv A pk₀ st := by
  obtain ⟨s₀, tr, hInit, hTr⟩ := hReach
  have h₀ : IdealCredInv A pk₀ s₀ := by
    have hEq : s₀ = IdealCredState.empty pk₀ epoch₀ root₀ := hInit
    rw [hEq]
    exact ⟨rfl, (fun _ hr => nomatch hr), (fun _ he => nomatch he), (fun _ => Nat.le_refl _),
      (fun _ => Nat.zero_le _), List.Pairwise.nil⟩
  clear hInit
  induction hTr with
  | nil _ => exact h₀
  | accept hStep _ ih => exact ih (idealCredInv_step h₀ hStep)
  | reject _ _ _ ih => exact ih h₀

/-! ## 5. Authenticated issuance and possession -/

/-- An accepted issuance is authorized by the issuer for exactly the transition performed, and the
    credential has between `1` and `maxAttrs` attributes. -/
theorem idealCredMachine_issuance_authenticated {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st' : IdealCredState A) (leaf : A.Leaf) (attrs : List Attr) (newRoot : Digest256)
    (auth : A.IssuerAuth) (out : IdealCredOutput A.OprfOut)
    (hStep : (idealCredMachine A pk₀ epoch₀ root₀).step st (.issue leaf attrs newRoot auth) =
      some (st', out)) :
    A.issuerAuthorizes st.issuerPk
      (.issue st.epoch st.issuedThisEpoch st.accumulatorRoot leaf attrs newRoot) auth = true ∧
    0 < attrs.length ∧ attrs.length ≤ pqCredentialProfile.maxAttrs ∧
    st'.accumulatorRoot = newRoot ∧ st'.epoch = st.epoch := by
  obtain ⟨hAcc, hSt, _⟩ := idealCredStep_issue_inv hStep
  simp only [IdealCredState.issueAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
  obtain ⟨⟨⟨hPos, hMax⟩, _⟩, hAuth⟩ := hAcc
  subst hSt
  exact ⟨hAuth, hPos, hMax, rfl, rfl⟩

/-- An accepted epoch rotation is authorized by the issuer and strictly increases the epoch. -/
theorem idealCredMachine_epoch_advance_authenticated {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st' : IdealCredState A) (newEpoch : Nat) (newRoot : Digest256)
    (auth : A.IssuerAuth) (out : IdealCredOutput A.OprfOut)
    (hStep : (idealCredMachine A pk₀ epoch₀ root₀).step st (.advanceEpoch newEpoch newRoot auth) =
      some (st', out)) :
    A.issuerAuthorizes st.issuerPk
      (.advanceEpoch st.epoch newEpoch st.accumulatorRoot newRoot) auth = true ∧
    st.epoch < st'.epoch ∧ st'.epoch = newEpoch ∧ st'.accumulatorRoot = newRoot := by
  obtain ⟨hAcc, hSt, _⟩ := idealCredStep_advanceEpoch_inv hStep
  simp only [IdealCredState.advanceAccepts, Bool.and_eq_true, decide_eq_true_eq] at hAcc
  subst hSt
  exact ⟨hAcc.2, hAcc.1, rfl, rfl⟩

/-- Commands on the holder and TOPRF-client interfaces never change what the issuer controls:
    the issuer key, the epoch, the accumulator root, the leaf count and the enrolled records. -/
theorem idealCredMachine_issuer_state_frame {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st' : IdealCredState A) (inp : IdealCredInput A) (out : IdealCredOutput A.OprfOut)
    (hPort : ¬ (inp.port = CredPort.issuer))
    (hStep : (idealCredMachine A pk₀ epoch₀ root₀).step st inp = some (st', out)) :
    st'.issuerPk = st.issuerPk ∧ st'.epoch = st.epoch ∧
    st'.accumulatorRoot = st.accumulatorRoot ∧ st'.issuedThisEpoch = st.issuedThisEpoch ∧
    st'.records = st.records := by
  cases inp with
  | issue leaf attrs newRoot auth => exact absurd rfl hPort
  | advanceEpoch newEpoch newRoot auth => exact absurd rfl hPort
  | present secret stmt =>
    have hStep' : idealCredStep A st (.present secret stmt) = some (st', out) := hStep
    rw [idealCredStep_present_eq] at hStep'
    cases hC : st.presentAccepts secret stmt with
    | false =>
      simp only [hC, Bool.false_eq_true, ↓reduceIte] at hStep'
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hStep')
      rw [← hSt]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | true =>
      simp only [hC, ↓reduceIte] at hStep'
      obtain ⟨hSt, _⟩ := Prod.mk.inj (Option.some.inj hStep')
      rw [← hSt]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | evalToprf t input approvals =>
    obtain ⟨_, hCase⟩ := idealCredStep_evalToprf_inv hStep
    rcases hCase with ⟨o, _, hSt, _⟩ | ⟨hSt, _⟩
    · subst hSt
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · subst hSt
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Presentation soundness of a single step: an accepted presentation names the current issuer
    key, epoch and accumulator root, uses a fresh challenge that is burned by the step, has valid
    disclosed indices, and the presented secret opens a record of the current epoch whose
    attributes satisfy the statement. -/
theorem idealCredMachine_presentation_sound {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st' : IdealCredState A) (secret : A.HolderSecret) (stmt : CredentialStatement Attr)
    (hStep : (idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret stmt) =
      some (st', .presentationVerdict true)) :
    stmt.issuerPk = st.issuerPk ∧
    stmt.epoch = st.epoch ∧
    stmt.accumulatorRoot = st.accumulatorRoot ∧
    stmt.challengeNonce ∉ st.usedChallenges ∧
    stmt.challengeNonce ∈ st'.usedChallenges ∧
    DisclosedIndicesValid stmt = true ∧
    ∃ r ∈ st.records, A.opens secret r.leaf = true ∧ r.epoch = st.epoch ∧
      CredentialMatchesAttributes stmt r.attrs = true := by
  obtain ⟨hAcc, hSt⟩ := idealCredStep_present_true_inv hStep
  simp only [IdealCredState.presentAccepts, IdealCredState.eligible, Bool.and_eq_true,
    decide_eq_true_eq, List.any_eq_true] at hAcc
  obtain ⟨⟨⟨⟨hPk, hEp⟩, hRoot⟩, hFresh⟩, r, hr, ⟨hOpen, hREp⟩, hMatch⟩ := hAcc
  have hIdx : DisclosedIndicesValid stmt = true := by
    have hM := hMatch
    simp only [CredentialMatchesAttributes, Bool.and_eq_true] at hM
    exact hM.1.2
  subst hSt
  exact ⟨hPk, hEp, hRoot, hFresh, List.Mem.head _, hIdx, r, hr, hOpen, hREp, hMatch⟩

/-- **Authenticated possession.** In a reachable state, an accepted presentation is backed by an
    enrolled record that the presented secret opens, issued in the statement's (current) epoch
    with attributes satisfying the statement, and whose issuance — leaf, attributes, epoch, leaf
    index and accumulator roots — the issuer authorized under `pk₀`. -/
theorem idealCredMachine_presentation_authenticated {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st' : IdealCredState A) (secret : A.HolderSecret) (stmt : CredentialStatement Attr)
    (hReach : (idealCredMachine A pk₀ epoch₀ root₀).Reachable st)
    (hStep : (idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret stmt) =
      some (st', .presentationVerdict true)) :
    stmt.issuerPk = pk₀ ∧
    ∃ r ∈ st.records,
      A.opens secret r.leaf = true ∧
      r.epoch = stmt.epoch ∧
      CredentialMatchesAttributes stmt r.attrs = true ∧
      0 < r.attrs.length ∧
      A.issuerAuthorizes pk₀
        (.issue r.epoch r.leafIndex r.prevRoot r.leaf r.attrs r.root) r.auth = true := by
  have hInv := idealCredInv_reachable hReach
  obtain ⟨hPk, hEp, _, _, _, _, r, hr, hOpen, hREp, hMatch⟩ :=
    idealCredMachine_presentation_sound A pk₀ epoch₀ root₀ st st' secret stmt hStep
  obtain ⟨hAuth, hPos, _, _⟩ := hInv.records_authorized r hr
  exact ⟨hPk.trans hInv.issuerPk_eq, r, hr, hOpen, hREp.trans hEp.symm, hMatch, hPos, hAuth⟩

/-! ### Rejection of the unauthenticated behaviours -/

/-- Tooth (audit #2): an issuance the issuer did not authorize is rejected, whatever its
    attributes and root. -/
theorem idealCredMachine_rejects_unauthorized_issue {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (leaf : A.Leaf) (attrs : List Attr) (newRoot : Digest256)
    (auth : A.IssuerAuth)
    (hForged : A.issuerAuthorizes st.issuerPk
      (.issue st.epoch st.issuedThisEpoch st.accumulatorRoot leaf attrs newRoot) auth = false) :
    (idealCredMachine A pk₀ epoch₀ root₀).step st (.issue leaf attrs newRoot auth) = none := by
  have hAcc : st.issueAccepts leaf attrs newRoot auth = false := by
    simp only [IdealCredState.issueAccepts, hForged, Bool.and_false]
  simp only [idealCredMachine, idealCredStep, hAcc, Bool.false_eq_true, ↓reduceIte]

/-- Tooth (audit #2): an accumulator-root / epoch update the issuer did not authorize is rejected. -/
theorem idealCredMachine_rejects_unauthorized_epoch_advance {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (newEpoch : Nat) (newRoot : Digest256) (auth : A.IssuerAuth)
    (hForged : A.issuerAuthorizes st.issuerPk
      (.advanceEpoch st.epoch newEpoch st.accumulatorRoot newRoot) auth = false) :
    (idealCredMachine A pk₀ epoch₀ root₀).step st (.advanceEpoch newEpoch newRoot auth) = none := by
  have hAcc : st.advanceAccepts newEpoch newRoot auth = false := by
    simp only [IdealCredState.advanceAccepts, hForged, Bool.and_false]
  simp only [idealCredMachine, idealCredStep, hAcc, Bool.false_eq_true, ↓reduceIte]

/-- Tooth (audit #10): a credential with zero attributes is never issued, even with an
    authorization the issuer relation accepts. -/
theorem idealCredMachine_rejects_empty_credential {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (leaf : A.Leaf) (attrs : List Attr) (newRoot : Digest256)
    (auth : A.IssuerAuth) (hEmpty : attrs.length = 0) :
    (idealCredMachine A pk₀ epoch₀ root₀).step st (.issue leaf attrs newRoot auth) = none := by
  have hAcc : st.issueAccepts leaf attrs newRoot auth = false := by
    simp only [IdealCredState.issueAccepts, hEmpty, Nat.lt_irrefl, decide_false,
      Bool.false_and]
  simp only [idealCredMachine, idealCredStep, hAcc, Bool.false_eq_true, ↓reduceIte]

/-- Tooth (audit #2): a presenter whose secret opens no enrolled leaf is never accepted, whatever
    the statement — in particular with an empty disclosure list. -/
theorem idealCredMachine_rejects_unpossessed_presentation {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st' : IdealCredState A) (secret : A.HolderSecret) (stmt : CredentialStatement Attr)
    (hNoLeaf : ∀ r ∈ st.records, A.opens secret r.leaf = false) :
    ¬ ((idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret stmt) =
      some (st', .presentationVerdict true)) := by
  intro hStep
  obtain ⟨_, _, _, _, _, _, r, hr, hOpen, _⟩ :=
    idealCredMachine_presentation_sound A pk₀ epoch₀ root₀ st st' secret stmt hStep
  rw [hNoLeaf r hr] at hOpen
  cases hOpen

/-- Tooth (audit #9): a statement for any epoch other than the current one is never accepted. -/
theorem idealCredMachine_rejects_stale_epoch {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st' : IdealCredState A) (secret : A.HolderSecret) (stmt : CredentialStatement Attr)
    (hStale : ¬ (stmt.epoch = st.epoch)) :
    ¬ ((idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret stmt) =
      some (st', .presentationVerdict true)) := by
  intro hStep
  obtain ⟨_, hEp, _⟩ :=
    idealCredMachine_presentation_sound A pk₀ epoch₀ root₀ st st' secret stmt hStep
  exact hStale hEp

/-- Tooth (audit #9): after an epoch rotation, a credential issued before it is no longer
    presentable, for any statement. -/
theorem idealCredMachine_rejects_retired_credential {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st₁ st₂ : IdealCredState A) (newEpoch : Nat) (newRoot : Digest256) (auth : A.IssuerAuth)
    (out : IdealCredOutput A.OprfOut)
    (secret : A.HolderSecret) (stmt : CredentialStatement Attr)
    (hReach : (idealCredMachine A pk₀ epoch₀ root₀).Reachable st)
    (hAdvance : (idealCredMachine A pk₀ epoch₀ root₀).step st
      (.advanceEpoch newEpoch newRoot auth) = some (st₁, out)) :
    ¬ ((idealCredMachine A pk₀ epoch₀ root₀).step st₁ (.present secret stmt) =
      some (st₂, .presentationVerdict true)) := by
  intro hStep
  have hInv := idealCredInv_reachable hReach
  obtain ⟨_, hLt, _, _⟩ := idealCredMachine_epoch_advance_authenticated A pk₀ epoch₀ root₀
    st st₁ newEpoch newRoot auth out hAdvance
  obtain ⟨_, hSt, _⟩ := idealCredStep_advanceEpoch_inv hAdvance
  obtain ⟨_, _, _, _, _, _, r, hr, _, hREp, _⟩ :=
    idealCredMachine_presentation_sound A pk₀ epoch₀ root₀ st₁ st₂ secret stmt hStep
  have hrOld : r ∈ st.records := by
    rw [hSt] at hr
    exact hr
  obtain ⟨_, _, _, hLe⟩ := hInv.records_authorized r hrOld
  rw [hREp] at hLe
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLt hLe)

/-- Tooth: a challenge nonce is accepted at most once. -/
theorem idealCredMachine_rejects_replayed_challenge {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st₁ st₂ : IdealCredState A) (secret secret' : A.HolderSecret)
    (stmt stmt' : CredentialStatement Attr)
    (hSame : stmt'.challengeNonce = stmt.challengeNonce)
    (hFirst : (idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret stmt) =
      some (st₁, .presentationVerdict true)) :
    ¬ ((idealCredMachine A pk₀ epoch₀ root₀).step st₁ (.present secret' stmt') =
      some (st₂, .presentationVerdict true)) := by
  intro hSecond
  obtain ⟨_, _, _, _, hBurned, _⟩ :=
    idealCredMachine_presentation_sound A pk₀ epoch₀ root₀ st st₁ secret stmt hFirst
  obtain ⟨_, _, _, hFresh, _⟩ :=
    idealCredMachine_presentation_sound A pk₀ epoch₀ root₀ st₁ st₂ secret' stmt' hSecond
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

/-- A presentation step depends on the presented secret only through eligibility. -/
theorem idealCredStep_present_congr {Attr : Type} [DecidableEq Attr] (A : CredAuthority Attr)
    (st : IdealCredState A) (secret₁ secret₂ : A.HolderSecret) (stmt : CredentialStatement Attr)
    (hElig : st.eligible secret₁ stmt = st.eligible secret₂ stmt) :
    idealCredStep A st (.present secret₁ stmt) = idealCredStep A st (.present secret₂ stmt) := by
  rw [idealCredStep_present_eq, idealCredStep_present_eq]
  unfold IdealCredState.presentAccepts
  rw [hElig]

/-- **Selective-disclosure privacy and single-show unlinkability.** Let two holders own records of
    the current epoch whose attribute vectors agree on the positions disclosed by `stmt` and may
    differ everywhere else, the first of which satisfies `stmt`. Then presenting `stmt` with either
    secret produces the same verdict *and the same successor state*: neither the verifier's output
    nor anything the functionality does afterwards depends on which of the two credentials, or
    which undisclosed attributes, were used. -/
theorem idealCredMachine_selective_disclosure_privacy {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (secret₁ secret₂ : A.HolderSecret)
    (stmt : CredentialStatement Attr) (r₁ r₂ : CredentialRecord A)
    (hMem₁ : r₁ ∈ st.records) (hMem₂ : r₂ ∈ st.records)
    (hOpen₁ : A.opens secret₁ r₁.leaf = true) (hOpen₂ : A.opens secret₂ r₂.leaf = true)
    (hLive₁ : r₁.epoch = st.epoch) (hLive₂ : r₂.epoch = st.epoch)
    (hPos₂ : 0 < r₂.attrs.length) (hMax₂ : r₂.attrs.length ≤ pqCredentialProfile.maxAttrs)
    (hAgreeDisclosed : ∀ p ∈ stmt.disclosed, r₁.attrs[p.1]? = r₂.attrs[p.1]?)
    (hSat₁ : CredentialMatchesAttributes stmt r₁.attrs = true) :
    (idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret₁ stmt) =
      (idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret₂ stmt) := by
  have hSat₂ := credentialMatchesAttributes_of_agree stmt r₁.attrs r₂.attrs hPos₂ hMax₂
    hAgreeDisclosed hSat₁
  have hE₁ : st.eligible secret₁ stmt = true := by
    simp only [IdealCredState.eligible, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨r₁, hMem₁, ⟨hOpen₁, hLive₁⟩, hSat₁⟩
  have hE₂ : st.eligible secret₂ stmt = true := by
    simp only [IdealCredState.eligible, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨r₂, hMem₂, ⟨hOpen₂, hLive₂⟩, hSat₂⟩
  exact idealCredStep_present_congr A st secret₁ secret₂ stmt (hE₁.trans hE₂.symm)

/-- Final state and output sequence of a machine on an input sequence, rejected inputs included. -/
def credRun {S In Out : Type} (M : Machine S In Out) : S → List In → S × List (Option Out)
  | s, [] => (s, [])
  | s, inp :: rest =>
    ((credRun M (M.runStep s inp).1 rest).1,
     (M.runStep s inp).2 :: (credRun M (M.runStep s inp).1 rest).2)

/-- Two input sequences that differ only in *which eligible credential* is shown at each
    presentation. Eligibility is evaluated in the state reached at that point of the run, so issuer
    commands, epoch rotations, TOPRF evaluations and failed presentations may be interleaved
    freely and identically on both sides. -/
inductive PresentationSwap {Attr : Type} [DecidableEq Attr] (A : CredAuthority Attr)
    (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256) :
    IdealCredState A → List (IdealCredInput A) → List (IdealCredInput A) → Prop where
  | nil (st : IdealCredState A) : PresentationSwap A pk₀ epoch₀ root₀ st [] []
  | same {st : IdealCredState A} (inp : IdealCredInput A) {xs ys : List (IdealCredInput A)} :
      PresentationSwap A pk₀ epoch₀ root₀
        ((idealCredMachine A pk₀ epoch₀ root₀).runStep st inp).1 xs ys →
      PresentationSwap A pk₀ epoch₀ root₀ st (inp :: xs) (inp :: ys)
  | swap {st : IdealCredState A} {secret₁ secret₂ : A.HolderSecret}
      {stmt : CredentialStatement Attr} {xs ys : List (IdealCredInput A)} :
      st.eligible secret₁ stmt = true →
      st.eligible secret₂ stmt = true →
      PresentationSwap A pk₀ epoch₀ root₀
        ((idealCredMachine A pk₀ epoch₀ root₀).runStep st (.present secret₁ stmt)).1 xs ys →
      PresentationSwap A pk₀ epoch₀ root₀ st
        (.present secret₁ stmt :: xs) (.present secret₂ stmt :: ys)

/-- **Trace-level presentation unlinkability.** Along two runs from the same state whose inputs
    differ only in which eligible credential is shown at each presentation, every output — issuer
    acknowledgements, verdicts, TOPRF values, rejections — and the final state coincide. -/
theorem idealCredMachine_presentation_trace_unlinkable {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (xs ys : List (IdealCredInput A))
    (hSwap : PresentationSwap A pk₀ epoch₀ root₀ st xs ys) :
    credRun (idealCredMachine A pk₀ epoch₀ root₀) st xs =
      credRun (idealCredMachine A pk₀ epoch₀ root₀) st ys := by
  induction hSwap with
  | nil _ => rfl
  | same inp _ ih =>
    simp only [credRun, ih]
  | @swap st secret₁ secret₂ stmt xs ys hE₁ hE₂ _ ih =>
    have hStepEq : (idealCredMachine A pk₀ epoch₀ root₀).runStep st (.present secret₂ stmt) =
        (idealCredMachine A pk₀ epoch₀ root₀).runStep st (.present secret₁ stmt) := by
      have h := idealCredStep_present_congr A st secret₂ secret₁ stmt (hE₂.trans hE₁.symm)
      simp only [Machine.runStep, idealCredMachine, h]
    simp only [credRun, hStepEq, ih]

/-- Tooth: a presenter that is not eligible is distinguishable from one that is, so
    `PresentationSwap` cannot drop its eligibility premises. -/
theorem idealCredMachine_ineligible_presentation_distinguishable {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st' : IdealCredState A) (secret₁ secret₂ : A.HolderSecret)
    (stmt : CredentialStatement Attr)
    (hAccepted : (idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret₁ stmt) =
      some (st', .presentationVerdict true))
    (hIneligible : st.eligible secret₂ stmt = false) :
    ¬ ((idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret₁ stmt) =
      (idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret₂ stmt)) := by
  intro hEq
  rw [hAccepted] at hEq
  obtain ⟨hAcc, _⟩ := idealCredStep_present_true_inv hEq.symm
  simp only [IdealCredState.presentAccepts, hIneligible, Bool.and_false] at hAcc
  cases hAcc

/-! ## 7. Ideal threshold OPRF -/

/-- **Ideal TOPRF evaluation.** In a reachable state an accepted evaluation returns the value of
    the keyed function at `(keyId, epoch, input)` — the same value for every evaluation of that
    point, in any state — and was approved by at least `toprfThreshold` distinct servers with
    index below `toprfServers`, for the current epoch, with quota left on the key. -/
theorem idealCredMachine_toprf_evaluation {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st st' : IdealCredState A) (t : ToprfTicket) (input : Bytes)
    (approvals : List (Nat × A.ServerAuth)) (out : IdealCredOutput A.OprfOut)
    (hReach : (idealCredMachine A pk₀ epoch₀ root₀).Reachable st)
    (hStep : (idealCredMachine A pk₀ epoch₀ root₀).step st (.evalToprf t input approvals) =
      some (st', out)) :
    out = .toprfEvaluated (A.oprf ⟨t.keyId, t.epoch, input⟩) ∧
    (approvals.map Prod.fst).Nodup ∧
    (∀ p ∈ approvals, p.1 < pqCredentialProfile.toprfServers ∧
      A.serverApproves p.1 t p.2 = true) ∧
    pqCredentialProfile.toprfThreshold ≤ approvals.length ∧
    t.epoch = st.epoch ∧
    st.oprfCharges.countP (fun c => decide (c.keyId = t.keyId)) < A.oprfQuota ∧
    st'.oprfCharges = t :: st.oprfCharges := by
  have hInv := idealCredInv_reachable hReach
  obtain ⟨hAcc, hCase⟩ := idealCredStep_evalToprf_inv hStep
  simp only [IdealCredState.toprfAccepts, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hAcc
  obtain ⟨⟨⟨⟨⟨hNodup, hServers⟩, hThr⟩, hEp⟩, hQuota⟩, _⟩ := hAcc
  have hOut : out = .toprfEvaluated (A.oprf ⟨t.keyId, t.epoch, input⟩) ∧
      st'.oprfCharges = t :: st.oprfCharges := by
    rcases hCase with ⟨o, hMem, hSt, hOut⟩ | ⟨hSt, hOut⟩
    · have hGraph : o = A.oprf ⟨t.keyId, t.epoch, input⟩ := hInv.table_graph _ hMem
      subst hSt
      rw [hOut, hGraph]
      exact ⟨rfl, rfl⟩
    · subst hSt
      exact ⟨hOut, rfl⟩
  exact ⟨hOut.1, hNodup, hServers, hThr, hEp, hQuota, hOut.2⟩

/-- **TOPRF rate budget.** In a reachable state, for every key: the number of points of the keyed
    function revealed so far is at most the number of tickets charged to the key, which is at most
    the quota; and no ticket of the key was charged with a counter at or below an earlier one. -/
theorem idealCredMachine_toprf_budget {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (keyId : Bytes)
    (hReach : (idealCredMachine A pk₀ epoch₀ root₀).Reachable st) :
    st.oprfTable.countP (fun e => decide (e.1.keyId = keyId)) ≤
      st.oprfCharges.countP (fun c => decide (c.keyId = keyId)) ∧
    st.oprfCharges.countP (fun c => decide (c.keyId = keyId)) ≤ A.oprfQuota ∧
    st.oprfCharges.Pairwise
      (fun newer older => newer.keyId = older.keyId → older.counter < newer.counter) := by
  have hInv := idealCredInv_reachable hReach
  exact ⟨hInv.table_charged keyId, hInv.charges_budget keyId, hInv.charges_fresh⟩

/-- **TOPRF obliviousness.** Whether an evaluation is accepted, and the ticket ledger after it, do
    not depend on the evaluation input: the servers' side of the functionality sees the ticket only. -/
theorem idealCredMachine_toprf_oblivious {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (t : ToprfTicket) (input₁ input₂ : Bytes)
    (approvals : List (Nat × A.ServerAuth)) :
    ((idealCredMachine A pk₀ epoch₀ root₀).step st (.evalToprf t input₁ approvals)).map
        (fun p => p.1.oprfCharges) =
      ((idealCredMachine A pk₀ epoch₀ root₀).step st (.evalToprf t input₂ approvals)).map
        (fun p => p.1.oprfCharges) := by
  have hOne : ∀ input : Bytes,
      ((idealCredMachine A pk₀ epoch₀ root₀).step st (.evalToprf t input approvals)).map
          (fun p => p.1.oprfCharges) =
        if st.toprfAccepts t approvals then some (t :: st.oprfCharges) else none := by
    intro input
    cases hC : st.toprfAccepts t approvals with
    | false => simp only [idealCredMachine, idealCredStep, hC, Bool.false_eq_true, ↓reduceIte,
        Option.map_none]
    | true =>
      simp only [idealCredMachine, idealCredStep, hC, ↓reduceIte]
      cases st.oprfTable.find? (fun e => decide (e.1 = ⟨t.keyId, t.epoch, input⟩)) <;> rfl
  rw [hOne input₁, hOne input₂]

/-- Tooth (audit #9): fewer approvals than `toprfThreshold` never release a TOPRF value. -/
theorem idealCredMachine_toprf_rejects_below_threshold {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (t : ToprfTicket) (input : Bytes)
    (approvals : List (Nat × A.ServerAuth))
    (hFew : approvals.length < pqCredentialProfile.toprfThreshold) :
    (idealCredMachine A pk₀ epoch₀ root₀).step st (.evalToprf t input approvals) = none := by
  have hAcc : st.toprfAccepts t approvals = false := by
    have hNot : ¬ (pqCredentialProfile.toprfThreshold ≤ approvals.length) := Nat.not_le_of_gt hFew
    simp only [IdealCredState.toprfAccepts, decide_eq_false hNot, Bool.and_false, Bool.false_and]
  simp only [idealCredMachine, idealCredStep, hAcc, Bool.false_eq_true, ↓reduceIte]

/-- Tooth (audit #9): a key whose quota is exhausted releases no further TOPRF value. -/
theorem idealCredMachine_toprf_rejects_over_budget {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (t : ToprfTicket) (input : Bytes)
    (approvals : List (Nat × A.ServerAuth))
    (hSpent : A.oprfQuota ≤ st.oprfCharges.countP (fun c => decide (c.keyId = t.keyId))) :
    (idealCredMachine A pk₀ epoch₀ root₀).step st (.evalToprf t input approvals) = none := by
  have hAcc : st.toprfAccepts t approvals = false := by
    have hNot : ¬ (st.oprfCharges.countP (fun c => decide (c.keyId = t.keyId)) < A.oprfQuota) :=
      Nat.not_lt_of_ge hSpent
    simp only [IdealCredState.toprfAccepts, decide_eq_false hNot, Bool.and_false, Bool.false_and]
  simp only [idealCredMachine, idealCredStep, hAcc, Bool.false_eq_true, ↓reduceIte]

/-- Tooth (audit #9): a ticket whose counter does not exceed one already charged to its key is
    rejected, so no ticket is redeemed twice. -/
theorem idealCredMachine_toprf_rejects_replayed_ticket {Attr : Type} [DecidableEq Attr]
    (A : CredAuthority Attr) (pk₀ : Bytes) (epoch₀ : Nat) (root₀ : Digest256)
    (st : IdealCredState A) (t c : ToprfTicket) (input : Bytes)
    (approvals : List (Nat × A.ServerAuth))
    (hCharged : c ∈ st.oprfCharges) (hKey : c.keyId = t.keyId) (hOld : t.counter ≤ c.counter) :
    (idealCredMachine A pk₀ epoch₀ root₀).step st (.evalToprf t input approvals) = none := by
  cases hC : st.toprfAccepts t approvals with
  | false => simp only [idealCredMachine, idealCredStep, hC, Bool.false_eq_true, ↓reduceIte]
  | true =>
    simp only [IdealCredState.toprfAccepts, Bool.and_eq_true] at hC
    have h := List.all_eq_true.mp hC.2 c hCharged
    rw [decide_eq_true hKey] at h
    exact absurd (of_decide_eq_true h) (Nat.not_lt_of_ge hOld)

/-! ## 8. A concrete authority: the gates are satisfiable and the audit counterexamples fail -/

/-- Toy authority over `Nat` attributes: leaf `ℓ` is opened by secret `ℓ + 1000`, the issuer
    authorizes an issuance with the tag `7 + leaf + leafIndex` and a rotation with the new epoch,
    server `i` approves a ticket with `i + counter`, and each key has a quota of two. -/
@[expose] def idealCredDemoAuthority : CredAuthority Nat where
  Leaf := Nat
  HolderSecret := Nat
  IssuerAuth := Nat
  ServerAuth := Nat
  OprfOut := Nat
  opens secret leaf := secret == leaf + 1000
  issuerAuthorizes _ action auth :=
    match action with
    | .issue _ leafIndex _ leaf _ _ => auth == 7 + leaf + leafIndex
    | .advanceEpoch _ newEpoch _ _ => auth == newEpoch
  serverApproves i t auth := auth == i + t.counter
  oprf pt := pt.epoch + pt.input.length
  oprfQuota := 2

/-- Demo state after the issuer enrolled leaf `5` with attributes `[11, 22]`. -/
def idealCredDemoState : IdealCredState idealCredDemoAuthority :=
  { issuerPk := [1]
    epoch := 0
    accumulatorRoot := 1#256
    issuedThisEpoch := 1
    records := [{ leaf := (5 : Nat), attrs := [11, 22], epoch := 0, leafIndex := 0,
                  prevRoot := 0#256, root := 1#256, auth := (12 : Nat) }]
    usedChallenges := []
    oprfTable := []
    oprfCharges := [] }

/-- Empty-disclosure statement against the demo state. -/
def idealCredDemoStatement (epoch : Nat) : CredentialStatement Nat :=
  { issuerPk := [1], epoch := epoch, accumulatorRoot := 1#256, disclosed := [],
    challengeNonce := [9] }

/-- The gates are satisfiable: the issuance that produces the demo record is accepted from the
    empty state, and the holder of leaf `5` (secret `1005`) is accepted for the empty-disclosure
    statement and for the disclosure of attribute `1`. -/
theorem idealCredDemo_accepts :
    (IdealCredState.empty [1] 0 0#256 : IdealCredState idealCredDemoAuthority).issueAccepts
      (5 : Nat) [11, 22] 1#256 (12 : Nat) = true ∧
    idealCredDemoState.presentAccepts (1005 : Nat) (idealCredDemoStatement 0) = true ∧
    idealCredDemoState.presentAccepts (1005 : Nat)
      { idealCredDemoStatement 0 with disclosed := [(1, 22)] } = true := by
  decide

/-- Tooth (audit #2, the referee's counterexample): against the demo state, neither the registry
    position `0`, nor the public leaf `5`, is accepted as a possession secret for the
    empty-disclosure statement; an issuance of invented attributes under a replayed authorization
    is rejected; and the holder is rejected for a stale epoch and for a false attribute value. -/
theorem idealCredDemo_rejects :
    ¬ (idealCredDemoState.presentAccepts (0 : Nat) (idealCredDemoStatement 0) = true ∨
      idealCredDemoState.presentAccepts (5 : Nat) (idealCredDemoStatement 0) = true ∨
      idealCredDemoState.issueAccepts (6 : Nat) [99] 2#256 (12 : Nat) = true ∨
      idealCredDemoState.presentAccepts (1005 : Nat) (idealCredDemoStatement 1) = true ∨
      idealCredDemoState.presentAccepts (1005 : Nat)
        { idealCredDemoStatement 0 with disclosed := [(1, 23)] } = true) := by
  decide

/-- The demo TOPRF gate accepts two approvals of a fresh ticket. -/
theorem idealCredDemo_toprf_accepts :
    idealCredDemoState.toprfAccepts ⟨[3], 0, 4⟩ ([(0, 4), (3, 7)] : List (Nat × Nat)) = true := by
  decide

/-- Tooth: the demo TOPRF gate rejects a single approval, a duplicated server, an approval for a
    different counter, a server index outside the committee, and a ticket for another epoch. -/
theorem idealCredDemo_toprf_rejects :
    ¬ (idealCredDemoState.toprfAccepts ⟨[3], 0, 4⟩ ([(0, 4)] : List (Nat × Nat)) = true ∨
      idealCredDemoState.toprfAccepts ⟨[3], 0, 4⟩ ([(0, 4), (0, 4)] : List (Nat × Nat)) = true ∨
      idealCredDemoState.toprfAccepts ⟨[3], 0, 4⟩ ([(0, 4), (3, 8)] : List (Nat × Nat)) = true ∨
      idealCredDemoState.toprfAccepts ⟨[3], 0, 4⟩ ([(0, 4), (5, 9)] : List (Nat × Nat)) = true ∨
      idealCredDemoState.toprfAccepts ⟨[3], 1, 4⟩ ([(0, 4), (3, 7)] : List (Nat × Nat)) = true) := by
  decide

/-- Statistical simulation / HVZK closeness record expressed directly in canonical `Spec.RatBound`. -/
structure CredHvzkBound where
  statisticalDistance : RatBound
  securityBits : Nat
  meetsBudget : statisticalDistance.atLeastBits securityBits

#verify_constructive
  Qsag.Spec.idealCredInv_step
  Qsag.Spec.idealCredInv_reachable
  Qsag.Spec.idealCredMachine_issuance_authenticated
  Qsag.Spec.idealCredMachine_epoch_advance_authenticated
  Qsag.Spec.idealCredMachine_issuer_state_frame
  Qsag.Spec.idealCredMachine_presentation_sound
  Qsag.Spec.idealCredMachine_presentation_authenticated
  Qsag.Spec.credentialMatchesAttributes_of_agree
  Qsag.Spec.idealCredMachine_selective_disclosure_privacy
  Qsag.Spec.idealCredMachine_presentation_trace_unlinkable
  Qsag.Spec.idealCredMachine_toprf_evaluation
  Qsag.Spec.idealCredMachine_toprf_budget
  Qsag.Spec.idealCredMachine_toprf_oblivious
  Qsag.Spec.idealCredDemo_accepts
  Qsag.Spec.idealCredDemo_toprf_accepts

#tooth_pair Qsag.Spec.idealCredMachine_issuance_authenticated vs
  Qsag.Spec.idealCredMachine_rejects_unauthorized_issue
#tooth_pair Qsag.Spec.idealCredMachine_epoch_advance_authenticated vs
  Qsag.Spec.idealCredMachine_rejects_unauthorized_epoch_advance
#tooth_pair Qsag.Spec.idealCredMachine_issuance_authenticated vs
  Qsag.Spec.idealCredMachine_rejects_empty_credential
#tooth_pair Qsag.Spec.idealCredMachine_presentation_authenticated vs
  Qsag.Spec.idealCredMachine_rejects_unpossessed_presentation
#tooth_pair Qsag.Spec.idealCredMachine_presentation_sound vs
  Qsag.Spec.idealCredMachine_rejects_stale_epoch
#tooth_pair Qsag.Spec.idealCredMachine_presentation_authenticated vs
  Qsag.Spec.idealCredMachine_rejects_retired_credential
#tooth_pair Qsag.Spec.idealCredMachine_presentation_sound vs
  Qsag.Spec.idealCredMachine_rejects_replayed_challenge
#tooth_pair Qsag.Spec.idealCredMachine_selective_disclosure_privacy vs
  Qsag.Spec.idealCredMachine_ineligible_presentation_distinguishable
#tooth_pair Qsag.Spec.idealCredMachine_toprf_evaluation vs
  Qsag.Spec.idealCredMachine_toprf_rejects_below_threshold
#tooth_pair Qsag.Spec.idealCredMachine_toprf_budget vs
  Qsag.Spec.idealCredMachine_toprf_rejects_over_budget
#tooth_pair Qsag.Spec.idealCredMachine_toprf_budget vs
  Qsag.Spec.idealCredMachine_toprf_rejects_replayed_ticket
#tooth_pair Qsag.Spec.idealCredDemo_accepts vs
  Qsag.Spec.idealCredDemo_rejects
#tooth_pair Qsag.Spec.idealCredDemo_toprf_accepts vs
  Qsag.Spec.idealCredDemo_toprf_rejects

end Qsag.Spec
end
