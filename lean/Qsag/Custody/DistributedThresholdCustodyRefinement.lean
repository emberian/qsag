module
/-
# Qsag.Custody.DistributedThresholdCustodyRefinement — `(t, n)` Shamir custodians, a network buffer and a coordinator ledger refine `Spec.IdealCustody`

The concrete machine has one state component per place where custody state lives:

* every custodian holds a Shamir share, a durable latch (`latch`, `latched`: at most one intent per
  epoch, epochs strictly increasing) and volatile session coupons that a crash erases;
* the network holds a buffer of approval messages. A message names its sender, the deployment it
  is for, the full intent and the sender's share. An honest custodian's message enters only through
  its own `approve` turn, and only for the deployment the custodian is enrolled in; the adversary
  may corrupt custodians adaptively (below the threshold), inject messages for corrupted senders,
  drop any message, and crash any custodian;
* the coordinator holds the `Spec.CustodyLedger` (budget, epoch watermark, sessions, WAL,
  quarantine flag) and runs `Spec.custodyLedgerSign` on it.

`execute` counts an approver only if the buffer holds a message from that approver for exactly this
deployment and this intent whose share passes the public commitment check. The released signature is
computed from the Lagrange reconstruction of those shares, never from the dealer polynomial.

`distCustody_refines_ideal` is a `Spec.DataRefines` witness into `Spec.idealCustodyMachine`:
`approve` implements the ideal `.approve` port, `inject` (for this deployment) the adversary's
`.advApprove` port, `corrupt` the ideal `.corrupt` port and `execute` the ideal `.sign` port; crashes,
drops and injected messages for other deployments are internal. The ledger is carried over
unchanged, so the quarantine flag is the ideal functionality's own flag.

What is proved from `Deployment.WellFormed` and what is assumed:

* Lagrange completeness is proved: any duplicate-free list of at least `threshold` enrolled
  custodians reconstructs the dealt key from the dealt shares (`reconstruct_dealt_shares`), from
  `points_nodup` and `degree`.
* `points_nonzero` is used by `corrupt_shares_independent_of_secret`: the shares of fewer than
  `threshold` custodians are consistent with every candidate key.
* `verifyShare_sound` (a share that passes the public check is the dealt share) is proved from
  `commit_binding`, which states that the share commitment is injective. For a hash commitment
  this is collision resistance idealised as injectivity; it is an assumption of the model, named in
  `WellFormed`. `verifyShare_dealt_or_collision` is the unconditional form.

Limits. The refinement is one-directional: the concrete machine rejects an `execute` whose
approvals have not arrived, and an `approve` at a latched epoch or with a spent coupon, where the
ideal functionality would accept. `execute_ready_fresh_releases` is the only liveness statement: a
ready quorum on a fresh intent within budget releases the dealt key's signature. Nothing is claimed
about message delivery. The interface map forgets the share that a corruption reveals, so the
refinement does not speak about key secrecy; `corrupt_shares_independent_of_secret` is the secrecy
statement, and it is information-theoretic about the dealt shares only.
-/

public import Qsag.Spec.IdealCustody
public import Qsag.Spec.IdealSign
public import Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.DistCustody

open Qsag.Spec

set_option autoImplicit false

/-! ## 1. Distributed state -/

/-- One custodian: its share, its durable latch and its volatile coupons. -/
structure Custodian (F : Type) where
  share : F
  latch : Nat
  latched : List CustodyIntent
  coupons : List Nat

/-- An approval in transit: the sender's share bound to one deployment and one intent. -/
structure Approval (F : Type) where
  sender : Nat
  deploymentId : Nat
  intent : CustodyIntent
  share : F

/-- Custodians, network buffer, corruption set and the coordinator's ledger. -/
structure State (F PK D Sig : Type) where
  nodes : Nat → Custodian F
  buffer : List (Approval F)
  corrupt : List Nat
  ledger : CustodyLedger PK D Sig

/-- Schedule alphabet. -/
inductive Turn (F : Type) where
  | approve (p deploymentId : Nat) (intent : CustodyIntent)
  | inject (m : Approval F)
  | corrupt (p : Nat)
  | crash (p : Nat)
  | dropMsg (idx : Nat)
  | execute (deploymentId : Nat) (approvers : List Nat) (intent : CustodyIntent)
      (abortBeforeRelease : Bool)

/-- Outputs. `corrupted` hands the adversary the custodian's share and its durable approval log. -/
inductive Event (F Sig : Type) where
  | approved
  | injected
  | corrupted (share : F) (latched : List CustodyIntent)
  | recovered
  | dropped
  | custody (out : CustodyOutcome Sig)
  deriving DecidableEq

/-- Static deployment. `poly` is the dealer's polynomial; the machine reads it only to set the
    initial shares. `shareCommitment p` is the public commitment to custodian `p`'s share. -/
structure Deployment (F C PK D Sig : Type) where
  deploymentId : Nat
  pk : PK
  quorum : CustodyQuorumProfile
  point : Nat → F
  poly : List F
  commit : F → C
  shareCommitment : Nat → C
  digests : CustodyDigestScheme D
  signWith : F → D → Sig

section Defs

variable {F C PK D Sig : Type} [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]

/-- The dealt signing key `poly(0)`. -/
@[expose] def Deployment.secret (dep : Deployment F C PK D Sig) : F :=
  RoundPoly.evalCoeffs dep.poly CommRingOps.zero

/-- The share dealt to custodian `p`. -/
@[expose] def Deployment.trueShare (dep : Deployment F C PK D Sig) (p : Nat) : F :=
  RoundPoly.evalCoeffs dep.poly (dep.point p)

/-- The ideal functionality's signing oracle for this deployment: the dealt key's signature. -/
@[expose] def Deployment.idealOracle (dep : Deployment F C PK D Sig) : D → Sig :=
  dep.signWith dep.secret

/-- The public share check: the share opens custodian `p`'s commitment. -/
@[expose] def Deployment.verifyShare (dep : Deployment F C PK D Sig) (p : Nat) (s : F) : Bool :=
  decide (dep.commit s = dep.shareCommitment p)

/-- Deployment conditions. `commit_binding` is the modelling assumption on the commitment; the
    other four are checkable facts about the dealt parameters. -/
structure Deployment.WellFormed (dep : Deployment F C PK D Sig) : Prop where
  /-- Enrolled custodians have pairwise distinct evaluation points. -/
  points_nodup : ((List.range dep.quorum.numParties).map dep.point).Nodup
  /-- No enrolled custodian is dealt the key itself. -/
  points_nonzero : ∀ p : Nat, p < dep.quorum.numParties → dep.point p ≠ CommRingOps.zero
  /-- The polynomial has exactly `threshold` coefficients (degree below the threshold). -/
  degree : dep.poly.length = dep.quorum.threshold
  /-- The public commitments are the commitments to the dealt shares. -/
  commitments_dealt : ∀ p : Nat, p < dep.quorum.numParties →
    dep.shareCommitment p = dep.commit (dep.trueShare p)
  /-- The share commitment is injective. -/
  commit_binding : ∀ s s' : F, dep.commit s = dep.commit s' → s = s'

@[expose] def State.init (dep : Deployment F C PK D Sig) : State F PK D Sig where
  nodes := fun p => { share := dep.trueShare p, latch := 0, latched := [], coupons := [] }
  buffer := []
  corrupt := []
  ledger := (IdealCustodyState.init dep.deploymentId dep.pk dep.quorum).ledger

def setNode (nodes : Nat → Custodian F) (p : Nat) (c : Custodian F) :
    Nat → Custodian F :=
  fun q => if q = p then c else nodes q

/-- `m` is a verified approval of `i` by `p` for this deployment. -/
def supports (dep : Deployment F C PK D Sig) (i : CustodyIntent) (p : Nat)
    (m : Approval F) : Bool :=
  decide (m.sender = p) && decide (m.deploymentId = dep.deploymentId) &&
    decide (m.intent = i) && dep.verifyShare p m.share

/-- The first verified share from `p` for `i` in the buffer. -/
def approvalShare (dep : Deployment F C PK D Sig) (buffer : List (Approval F))
    (i : CustodyIntent) (p : Nat) : Option F :=
  (buffer.find? (supports dep i p)).map (fun m => m.share)

/-- The coordinator's quorum check: enough distinct enrolled approvers, each with a verified
    buffered approval of exactly this intent for this deployment. -/
def quorumReady (dep : Deployment F C PK D Sig) (buffer : List (Approval F))
    (approvers : List Nat) (i : CustodyIntent) : Bool :=
  decide (dep.quorum.threshold ≤ approvers.length) &&
  decide approvers.Nodup &&
  approvers.all (fun p =>
    decide (p < dep.quorum.numParties) && (approvalShare dep buffer i p).isSome)

/-- Lagrange reconstruction at zero from points and shares. -/
@[expose] def reconstruct (pts shares : List F) : F :=
  ringListSum (List.zipWith (fun x s => lagrangeToAdditiveShare pts x s) pts shares)

/-- The key the coordinator reconstructs for `i` from the buffered shares of `approvers`. -/
def quorumKey (dep : Deployment F C PK D Sig) (buffer : List (Approval F))
    (approvers : List Nat) (i : CustodyIntent) : F :=
  reconstruct (approvers.map dep.point)
    (approvers.map (fun p => (approvalShare dep buffer i p).getD CommRingOps.zero))

/-- Coordinator transition: the ledger's signing transition, signing with the reconstructed key
    and counting the named approvers only when the quorum check passes. A WAL replay needs no
    quorum, exactly as in the ledger. -/
def executeStep (dep : Deployment F C PK D Sig) (st : State F PK D Sig)
    (d : Nat) (approvers : List Nat) (i : CustodyIntent) (ab : Bool) :
    Option (State F PK D Sig × CustodyOutcome Sig) :=
  (custodyLedgerSign dep.digests (dep.signWith (quorumKey dep st.buffer approvers i)) st.ledger
      (if quorumReady dep st.buffer approvers i then approvers.length else 0) d i ab).map
    (fun r => ({ st with ledger := r.1 }, r.2))

/-- One turn of the distributed system. -/
@[expose] def step (dep : Deployment F C PK D Sig) (st : State F PK D Sig) :
    Turn F → Option (State F PK D Sig × Event F Sig)
  | .approve p d i =>
    if p < dep.quorum.numParties ∧ p ∉ st.corrupt ∧ d = dep.deploymentId ∧
        (st.nodes p).latch ≤ i.epoch ∧ i.sessionId ∉ (st.nodes p).coupons then
      some ({ st with
              nodes := setNode st.nodes p
                { share := (st.nodes p).share
                  latch := i.epoch + 1
                  latched := i :: (st.nodes p).latched
                  coupons := i.sessionId :: (st.nodes p).coupons }
              buffer := { sender := p, deploymentId := d, intent := i,
                          share := (st.nodes p).share } :: st.buffer },
            .approved)
    else none
  | .inject m =>
    if m.sender ∈ st.corrupt then
      some ({ st with buffer := m :: st.buffer }, .injected)
    else none
  | .corrupt p =>
    if p < dep.quorum.numParties ∧ p ∉ st.corrupt ∧
        st.corrupt.length + 1 < dep.quorum.threshold then
      some ({ st with corrupt := p :: st.corrupt },
            .corrupted (st.nodes p).share (st.nodes p).latched)
    else none
  | .crash p =>
    some ({ st with
            nodes := setNode st.nodes p
              { share := (st.nodes p).share
                latch := (st.nodes p).latch
                latched := (st.nodes p).latched
                coupons := [] } },
          .recovered)
  | .dropMsg idx =>
    some ({ st with buffer := st.buffer.take idx ++ st.buffer.drop (idx + 1) }, .dropped)
  | .execute d approvers i ab =>
    (executeStep dep st d approvers i ab).map (fun r => (r.1, Event.custody r.2))

/-- The distributed custody machine. -/
@[expose] def distMachine (dep : Deployment F C PK D Sig) :
    Machine (State F PK D Sig) (Turn F) (Event F Sig) where
  Init st := st = State.init dep
  step := step dep
  errStep st _ := st

/-- The ideal port a turn implements. A crash, a drop and an injected message for another
    deployment are internal. -/
@[expose] def visIn (dep : Deployment F C PK D Sig) : Turn F → Option CustodyInput
  | .approve p d i => some (.approve p d i)
  | .inject m =>
    if m.deploymentId = dep.deploymentId then
      some (.advApprove m.sender m.deploymentId m.intent)
    else none
  | .corrupt p => some (.corrupt p)
  | .crash _ => none
  | .dropMsg _ => none
  | .execute d _ i ab => some (.sign d i ab)

/-- The ideal output of an event. The share revealed by a corruption has no ideal counterpart and
    is forgotten; internal events never reach the abstract trace. -/
@[expose] def visOut : Event F Sig → CustodyOutcome Sig
  | .approved => .approvalRecorded
  | .injected => .approvalRecorded
  | .corrupted _ latched => .corrupted latched
  | .recovered => .approvalRecorded
  | .dropped => .approvalRecorded
  | .custody out => out

/-- Invariant of the concrete state alone. -/
structure Inv (dep : Deployment F C PK D Sig) (st : State F PK D Sig) : Prop where
  deployment : st.ledger.deploymentId = dep.deploymentId
  enrolled : st.ledger.enrolledPk = dep.pk
  profile : st.ledger.quorum = dep.quorum
  shares : ∀ p : Nat, (st.nodes p).share = dep.trueShare p
  latchBound : ∀ (p : Nat) (e : CustodyIntent), e ∈ (st.nodes p).latched →
    e.epoch < (st.nodes p).latch
  latchNodup : ∀ p : Nat, ((st.nodes p).latched.map CustodyIntent.epoch).Nodup

/-- Simulation relation: the ledgers and corruption sets coincide, every custodian's durable log
    is exactly what the ideal functionality reveals on its corruption, and every buffered message
    for this deployment is backed by a recorded permit. -/
structure Rel (dep : Deployment F C PK D Sig) (c : State F PK D Sig)
    (a : IdealCustodyState PK D Sig) : Prop where
  inv : Inv dep c
  ledger : a.ledger = c.ledger
  corrupt : a.corruptParties = c.corrupt
  latched : ∀ p : Nat, (c.nodes p).latched = custodyRevealed a.honestApprovals p
  buffered : ∀ m : Approval F, m ∈ c.buffer → m.deploymentId = dep.deploymentId →
    CustodyApproval.mk m.sender m.deploymentId m.intent ∈ a.honestApprovals ∨
      CustodyApproval.mk m.sender m.deploymentId m.intent ∈ a.corruptApprovals

/-! ## 2. Elementary lemmas -/

private theorem dc_if_pos {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem dc_if_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

omit [LawfulField F] [DecidableEq F] in
private theorem setNode_self (nodes : Nat → Custodian F) (p : Nat) (c : Custodian F) :
    setNode nodes p c p = c := by
  unfold setNode
  exact dc_if_pos rfl _ _

omit [LawfulField F] [DecidableEq F] in
private theorem setNode_ne (nodes : Nat → Custodian F) (p q : Nat) (c : Custodian F)
    (h : q ≠ p) : setNode nodes p c q = nodes q := by
  unfold setNode
  exact dc_if_neg h _ _

/-- A map that is duplicate-free on a list is injective on its members. -/
private theorem inj_of_nodup_map {α β : Type} (f : α → β) :
    ∀ (L : List α), (L.map f).Nodup → ∀ a b : α, a ∈ L → b ∈ L → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, hNd, a, b, ha, hb, hEq => by
    rw [List.map_cons, List.nodup_cons] at hNd
    rcases List.mem_cons.mp ha with hax | hax
    · rcases List.mem_cons.mp hb with hbx | hbx
      · exact hax.trans hbx.symm
      · exact absurd (List.mem_map.mpr ⟨b, hbx, (hax ▸ hEq).symm⟩) hNd.1
    · rcases List.mem_cons.mp hb with hbx | hbx
      · exact absurd (List.mem_map.mpr ⟨a, hax, hbx ▸ hEq⟩) hNd.1
      · exact inj_of_nodup_map f xs hNd.2 a b hax hbx hEq

private theorem nodup_map_of_inj_on {α : Type} (f : Nat → α) (bound : Nat)
    (hInj : ∀ p q : Nat, p < bound → q < bound → f p = f q → p = q) :
    ∀ (L : List Nat), L.Nodup → (∀ p, p ∈ L → p < bound) → (L.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hNd, hB => by
    obtain ⟨hxNot, hNdXs⟩ := List.nodup_cons.mp hNd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj_on f bound hInj xs hNdXs
      (fun p hp => hB p (List.mem_cons_of_mem _ hp))⟩
    intro hMem
    obtain ⟨y, hy, hEq⟩ := List.mem_map.mp hMem
    have hyx : y = x := hInj y x (hB y (List.mem_cons_of_mem _ hy))
      (hB x List.mem_cons_self) hEq
    exact hxNot (hyx ▸ hy)

private theorem zipWith_map_map {α β γ δ : Type} (f : β → γ → δ) (g : α → β) (h : α → γ) :
    ∀ (L : List α), List.zipWith f (L.map g) (L.map h) = L.map (fun a => f (g a) (h a))
  | [] => rfl
  | a :: as => by
    rw [List.map_cons, List.map_cons, List.zipWith_cons_cons, zipWith_map_map f g h as,
      List.map_cons]

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
/-- Distinct enrolled custodians have distinct evaluation points. -/
theorem Deployment.WellFormed.point_inj {dep : Deployment F C PK D Sig} (hWf : dep.WellFormed)
    {p q : Nat} (hp : p < dep.quorum.numParties) (hq : q < dep.quorum.numParties)
    (h : dep.point p = dep.point q) : p = q :=
  inj_of_nodup_map dep.point _ hWf.points_nodup p q
    (List.mem_range.mpr hp) (List.mem_range.mpr hq) h

/-! ## 3. The share check -/

omit [DecidableEq D] in
/-- Unconditional form of the share check: a share that passes it is the dealt share, or it is a
    second opening of the dealt commitment. -/
theorem verifyShare_dealt_or_collision (dep : Deployment F C PK D Sig) {p : Nat} {s : F}
    (hDealt : dep.shareCommitment p = dep.commit (dep.trueShare p))
    (h : dep.verifyShare p s = true) :
    s = dep.trueShare p ∨ (s ≠ dep.trueShare p ∧ dep.commit s = dep.commit (dep.trueShare p)) := by
  have hC : dep.commit s = dep.commit (dep.trueShare p) := by
    unfold Deployment.verifyShare at h
    exact (of_decide_eq_true h).trans hDealt
  by_cases hs : s = dep.trueShare p
  · exact .inl hs
  · exact .inr ⟨hs, hC⟩

omit [DecidableEq F] [DecidableEq D] in
/-- Under `commit_binding`, a share of an enrolled custodian that passes the public check is the
    dealt share. -/
theorem verifyShare_sound (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed) {p : Nat} {s : F}
    (hp : p < dep.quorum.numParties) (h : dep.verifyShare p s = true) : s = dep.trueShare p := by
  unfold Deployment.verifyShare at h
  exact hWf.commit_binding _ _ ((of_decide_eq_true h).trans (hWf.commitments_dealt p hp))

omit [LawfulField F] [DecidableEq F] [DecidableEq D] in
theorem approvalShare_sound (dep : Deployment F C PK D Sig) (buffer : List (Approval F))
    (i : CustodyIntent) (p : Nat) (s : F)
    (h : approvalShare dep buffer i p = some s) :
    ∃ m : Approval F, m ∈ buffer ∧ m.sender = p ∧ m.deploymentId = dep.deploymentId ∧
      m.intent = i ∧ m.share = s ∧ dep.verifyShare p s = true := by
  unfold approvalShare at h
  cases hFind : buffer.find? (supports dep i p) with
  | none => rw [hFind] at h; cases h
  | some m =>
    rw [hFind] at h
    have hs : m.share = s := Option.some.inj h
    have hSup : supports dep i p m = true := List.find?_some hFind
    unfold supports at hSup
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hSup
    exact ⟨m, List.mem_of_find?_eq_some hFind, of_decide_eq_true hSup.1.1.1,
      of_decide_eq_true hSup.1.1.2, of_decide_eq_true hSup.1.2, hs, hs ▸ hSup.2⟩

omit [LawfulField F] [DecidableEq F] [DecidableEq D] in
/-- What the coordinator's quorum check establishes. -/
theorem quorumReady_spec (dep : Deployment F C PK D Sig) (buffer : List (Approval F))
    (approvers : List Nat) (i : CustodyIntent) (h : quorumReady dep buffer approvers i = true) :
    dep.quorum.threshold ≤ approvers.length ∧ approvers.Nodup ∧
    ∀ p, p ∈ approvers → p < dep.quorum.numParties ∧
      ∃ s : F, approvalShare dep buffer i p = some s := by
  unfold quorumReady at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2, ?_⟩
  intro p hp
  have hp' := List.all_eq_true.mp h.2 p hp
  rw [Bool.and_eq_true] at hp'
  refine ⟨of_decide_eq_true hp'.1, ?_⟩
  cases hS : approvalShare dep buffer i p with
  | none => rw [hS] at hp'; exact absurd hp'.2 Bool.false_ne_true
  | some s => exact ⟨s, rfl⟩

/-! ## 4. Lagrange completeness and share secrecy -/

omit [DecidableEq C] [DecidableEq D] in
/-- **Lagrange completeness.** Any duplicate-free list of at least `threshold` enrolled custodians
    reconstructs the dealt key from the dealt shares. -/
theorem reconstruct_dealt_shares (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed)
    (approvers : List Nat) (hNd : approvers.Nodup)
    (hEnrolled : ∀ p, p ∈ approvers → p < dep.quorum.numParties)
    (hThr : dep.quorum.threshold ≤ approvers.length) :
    reconstruct (approvers.map dep.point) (approvers.map dep.trueShare) = dep.secret := by
  have hPtsNd : (approvers.map dep.point).Nodup :=
    nodup_map_of_inj_on dep.point dep.quorum.numParties (fun _ _ hp hq h => hWf.point_inj hp hq h)
      approvers hNd hEnrolled
  have hLen : (approvers.map dep.point).length = approvers.length := List.length_map _
  unfold reconstruct
  have hMap : approvers.map (fun a =>
      lagrangeToAdditiveShare (approvers.map dep.point) (dep.point a) (dep.trueShare a)) =
      (approvers.map dep.point).map (fun x =>
        lagrangeToAdditiveShare (approvers.map dep.point) x
          (RoundPoly.evalCoeffs dep.poly x)) :=
    (List.map_map (f := dep.point)
      (g := fun x => lagrangeToAdditiveShare (approvers.map dep.point) x
        (RoundPoly.evalCoeffs dep.poly x)) (l := approvers)).symm
  rw [zipWith_map_map, hMap]
  exact lagrange_to_additive_reconstructs_poly (approvers.map dep.point).length
    (hLen ▸ Nat.le_trans dep.quorum.h_pos hThr) (approvers.map dep.point) hPtsNd rfl
    dep.poly (hLen ▸ hWf.degree ▸ hThr)

omit [DecidableEq D] in
/-- Reconstruction from any accepted quorum yields the dealt key. -/
theorem quorumKey_eq_secret (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed)
    (buffer : List (Approval F)) (approvers : List Nat) (i : CustodyIntent)
    (h : quorumReady dep buffer approvers i = true) :
    quorumKey dep buffer approvers i = dep.secret := by
  obtain ⟨hThr, hNd, hAll⟩ := quorumReady_spec dep buffer approvers i h
  have hShares : approvers.map
      (fun p => (approvalShare dep buffer i p).getD CommRingOps.zero) =
      approvers.map dep.trueShare := by
    apply List.map_congr_left
    intro p hp
    obtain ⟨hLt, s, hs⟩ := hAll p hp
    obtain ⟨_, _, _, _, _, _, hVer⟩ := approvalShare_sound dep buffer i p s hs
    rw [hs]
    exact verifyShare_sound dep hWf hLt hVer
  unfold quorumKey
  rw [hShares]
  exact reconstruct_dealt_shares dep hWf approvers hNd (fun p hp => (hAll p hp).1) hThr

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
/-- **Share secrecy below the threshold.** For any list of fewer than `threshold` enrolled
    custodians and any shift `w` of the dealt key, there is a bijection of the dealer polynomials
    (`threshold` coefficients) that adds `w` to the key and leaves every share of those custodians
    unchanged. `points_nonzero` is what makes this true. -/
theorem corrupt_shares_independent_of_secret (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed)
    (corrupt : List Nat) (hEnrolled : ∀ p, p ∈ corrupt → p < dep.quorum.numParties)
    (hFew : corrupt.length < dep.quorum.threshold) (w : F) :
    ∃ e : SimpleEquiv (ShamirPadPoly F dep.quorum.threshold) (ShamirPadPoly F dep.quorum.threshold),
      ∀ P : ShamirPadPoly F dep.quorum.threshold,
        RoundPoly.evalCoeffs (e.toFun P).1 CommRingOps.zero =
          CommRingOps.add w (RoundPoly.evalCoeffs P.1 CommRingOps.zero) ∧
        ∀ p : Nat, p ∈ corrupt →
          RoundPoly.evalCoeffs (e.toFun P).1 (dep.point p) =
            RoundPoly.evalCoeffs P.1 (dep.point p) := by
  have hCard : (corrupt.map dep.point).length + 1 ≤ dep.quorum.threshold := by
    rw [List.length_map]
    exact Nat.succ_le_of_lt hFew
  have hNz : ∀ c ∈ corrupt.map dep.point, c ≠ CommRingOps.zero := by
    intro c hc
    obtain ⟨q, hq, hEq⟩ := List.mem_map.mp hc
    exact hEq ▸ hWf.points_nonzero q (hEnrolled q hq)
  refine ⟨shamir_rebalanceEquiv LawfulField.inv dep.quorum.threshold (corrupt.map dep.point) w
    hCard, fun P => ?_⟩
  have h := pad_bijection_masked_openings_uniform (R := F) LawfulField.inv
    (fun _ hx => LawfulField.mul_inv_cancel hx) dep.quorum.threshold (corrupt.map dep.point) w
    hCard hNz P
  exact ⟨(LawfulCommRing.zero_add _).symm.trans h.1,
    fun p hp => h.2 _ (List.mem_map_of_mem hp)⟩

/-! ## 5. Invariant preservation -/

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
theorem init_inv (dep : Deployment F C PK D Sig) :
    Inv dep (State.init dep : State F PK D Sig) where
  deployment := rfl
  enrolled := rfl
  profile := rfl
  shares _ := rfl
  latchBound _ _ h := absurd h List.not_mem_nil
  latchNodup _ := List.nodup_nil

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
/-- Replacing one node by a node with the same share and a sound latch preserves the invariant;
    the buffer and the corruption set are not constrained by it. -/
private theorem inv_of_node_update (dep : Deployment F C PK D Sig) (st : State F PK D Sig)
    (p : Nat) (c : Custodian F) (buffer' : List (Approval F)) (corrupt' : List Nat)
    (hInv : Inv dep st)
    (hShare : c.share = (st.nodes p).share)
    (hBound : ∀ e : CustodyIntent, e ∈ c.latched → e.epoch < c.latch)
    (hNd : (c.latched.map CustodyIntent.epoch).Nodup) :
    Inv dep { st with nodes := setNode st.nodes p c, buffer := buffer', corrupt := corrupt' } where
  deployment := hInv.deployment
  enrolled := hInv.enrolled
  profile := hInv.profile
  shares q := by
    show (setNode st.nodes p c q).share = dep.trueShare q
    by_cases hqp : q = p
    · subst hqp
      rw [setNode_self, hShare]
      exact hInv.shares q
    · rw [setNode_ne _ _ _ _ hqp]
      exact hInv.shares q
  latchBound q e he := by
    show e.epoch < (setNode st.nodes p c q).latch
    have he' : e ∈ (setNode st.nodes p c q).latched := he
    by_cases hqp : q = p
    · subst hqp
      rw [setNode_self] at he' ⊢
      exact hBound e he'
    · rw [setNode_ne _ _ _ _ hqp] at he' ⊢
      exact hInv.latchBound q e he'
  latchNodup q := by
    show ((setNode st.nodes p c q).latched.map CustodyIntent.epoch).Nodup
    by_cases hqp : q = p
    · subst hqp
      rw [setNode_self]
      exact hNd
    · rw [setNode_ne _ _ _ _ hqp]
      exact hInv.latchNodup q

/-- Inversion of the coordinator's transition. -/
theorem executeStep_inv {dep : Deployment F C PK D Sig} {st st' : State F PK D Sig}
    {d : Nat} {approvers : List Nat} {i : CustodyIntent} {ab : Bool} {out : CustodyOutcome Sig}
    (h : executeStep dep st d approvers i ab = some (st', out)) :
    ∃ L', custodyLedgerSign dep.digests (dep.signWith (quorumKey dep st.buffer approvers i))
        st.ledger (if quorumReady dep st.buffer approvers i then approvers.length else 0)
        d i ab = some (L', out) ∧ st' = { st with ledger := L' } := by
  unfold executeStep at h
  cases hL : custodyLedgerSign dep.digests (dep.signWith (quorumKey dep st.buffer approvers i))
      st.ledger (if quorumReady dep st.buffer approvers i then approvers.length else 0)
      d i ab with
  | none => rw [hL] at h; cases h
  | some r =>
    obtain ⟨L', o⟩ := r
    rw [hL] at h
    cases h
    exact ⟨L', rfl, rfl⟩

/-- An accepted coordinator transition is the ledger's transition under the dealt key's oracle
    with the same approval count. -/
theorem executeStep_ledger_ideal (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed)
    {st : State F PK D Sig} {d : Nat} {approvers : List Nat} {i : CustodyIntent} {ab : Bool}
    {L' : CustodyLedger PK D Sig} {out : CustodyOutcome Sig}
    (h : custodyLedgerSign dep.digests (dep.signWith (quorumKey dep st.buffer approvers i))
        st.ledger (if quorumReady dep st.buffer approvers i then approvers.length else 0)
        d i ab = some (L', out)) :
    custodyLedgerSign dep.digests dep.idealOracle st.ledger
        (if quorumReady dep st.buffer approvers i then approvers.length else 0)
        d i ab = some (L', out) := by
  cases hQ : quorumReady dep st.buffer approvers i with
  | true =>
    rw [quorumKey_eq_secret dep hWf st.buffer approvers i hQ] at h
    rw [hQ] at h
    exact h
  | false =>
    rw [hQ] at h
    rw [dc_if_neg Bool.false_ne_true] at h ⊢
    obtain ⟨_, _, hCase⟩ := custodyLedgerSign_inv h
    rcases hCase with ⟨r, hF, _, _, _⟩ | ⟨_, _, _, hThr, _, _⟩
    · rw [← custodyLedgerSign_replay_irrelevant
        (o := dep.signWith (quorumKey dep st.buffer approvers i)) (n := 0) hF]
      exact h
    · exact absurd (Nat.lt_of_lt_of_le st.ledger.quorum.h_pos hThr) (Nat.lt_irrefl 0)

/-! ## 6. The refinement -/

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
theorem init_rel (dep : Deployment F C PK D Sig) :
    Rel dep (State.init dep : State F PK D Sig)
      (IdealCustodyState.init dep.deploymentId dep.pk dep.quorum) where
  inv := init_inv dep
  ledger := rfl
  corrupt := rfl
  latched _ := rfl
  buffered _ h _ := absurd h List.not_mem_nil

/-- One accepted concrete turn that implements an ideal port is an accepted step of the ideal
    functionality on that port with the mapped output, and the relation is preserved. -/
theorem step_sim_visible (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed)
    {c c' : State F PK D Sig} {a : IdealCustodyState PK D Sig} {turn : Turn F}
    {ev : Event F Sig} {j : CustodyInput}
    (hRel : Rel dep c a) (hStep : step dep c turn = some (c', ev))
    (hVis : visIn dep turn = some j) :
    ∃ a' : IdealCustodyState PK D Sig,
      idealCustodyStep dep.digests dep.idealOracle a j = some (a', visOut ev) ∧ Rel dep c' a' := by
  have hNum : a.ledger.quorum.numParties = dep.quorum.numParties := by
    rw [hRel.ledger, hRel.inv.profile]
  have hThr : a.ledger.quorum.threshold = dep.quorum.threshold := by
    rw [hRel.ledger, hRel.inv.profile]
  have hDep : a.ledger.deploymentId = dep.deploymentId := by
    rw [hRel.ledger, hRel.inv.deployment]
  cases turn with
  | approve p d i =>
    have hj : CustodyInput.approve p d i = j := Option.some.inj hVis
    subst hj
    unfold step at hStep
    dsimp only at hStep
    by_cases hg : p < dep.quorum.numParties ∧ p ∉ c.corrupt ∧ d = dep.deploymentId ∧
        (c.nodes p).latch ≤ i.epoch ∧ i.sessionId ∉ (c.nodes p).coupons
    · rw [dc_if_pos hg] at hStep
      cases hStep
      obtain ⟨hLt, hHon, hD, hLatch, _⟩ := hg
      refine ⟨_, idealCustodyStep_approve_of i
        ⟨hNum ▸ hLt, hRel.corrupt ▸ hHon, hD.trans hDep.symm⟩, ?_⟩
      refine
        { inv := inv_of_node_update dep c p _ _ _ hRel.inv rfl ?_ ?_
          ledger := hRel.ledger
          corrupt := hRel.corrupt
          latched := ?_
          buffered := ?_ }
      · intro e he
        show e.epoch < i.epoch + 1
        rcases List.mem_cons.mp he with hEq | hOld
        · rw [hEq]
          exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hRel.inv.latchBound p e hOld) hLatch)
      · show ((i :: (c.nodes p).latched).map CustodyIntent.epoch).Nodup
        rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, hRel.inv.latchNodup p⟩
        intro hMem
        obtain ⟨e, he, hEq⟩ := List.mem_map.mp hMem
        have hLtE := hRel.inv.latchBound p e he
        rw [hEq] at hLtE
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLtE hLatch)
      · intro q
        show (setNode c.nodes p _ q).latched =
          custodyRevealed (CustodyApproval.mk p d i :: a.honestApprovals) q
        by_cases hqp : q = p
        · subst hqp
          rw [setNode_self, custodyRevealed_cons_self]
          exact congrArg _ (hRel.latched q)
        · rw [setNode_ne _ _ _ _ hqp, custodyRevealed_cons_ne _ _ _ (fun h => hqp h.symm)]
          exact hRel.latched q
      · intro m hm hmD
        rcases List.mem_cons.mp hm with hEq | hOld
        · refine .inl ?_
          rw [hEq]
          exact List.mem_cons_self
        · exact (hRel.buffered m hOld hmD).imp (List.mem_cons_of_mem _) id
    · rw [dc_if_neg hg] at hStep
      cases hStep
  | inject m =>
    unfold visIn at hVis
    dsimp only at hVis
    by_cases hmD : m.deploymentId = dep.deploymentId
    · rw [dc_if_pos hmD] at hVis
      have hj : CustodyInput.advApprove m.sender m.deploymentId m.intent = j :=
        Option.some.inj hVis
      subst hj
      unfold step at hStep
      dsimp only at hStep
      by_cases hg : m.sender ∈ c.corrupt
      · rw [dc_if_pos hg] at hStep
        cases hStep
        refine ⟨_, idealCustodyStep_advApprove_of m.intent
          ⟨hRel.corrupt ▸ hg, hmD.trans hDep.symm⟩, ?_⟩
        exact
          { inv :=
              { deployment := hRel.inv.deployment
                enrolled := hRel.inv.enrolled
                profile := hRel.inv.profile
                shares := hRel.inv.shares
                latchBound := hRel.inv.latchBound
                latchNodup := hRel.inv.latchNodup }
            ledger := hRel.ledger
            corrupt := hRel.corrupt
            latched := hRel.latched
            buffered := fun m' hm' hm'D => by
              rcases List.mem_cons.mp hm' with hEq | hOld
              · refine .inr ?_
                rw [hEq]
                exact List.mem_cons_self
              · exact (hRel.buffered m' hOld hm'D).imp id (List.mem_cons_of_mem _) }
      · rw [dc_if_neg hg] at hStep
        cases hStep
    · rw [dc_if_neg hmD] at hVis
      cases hVis
  | corrupt p =>
    have hj : CustodyInput.corrupt p = j := Option.some.inj hVis
    subst hj
    unfold step at hStep
    dsimp only at hStep
    by_cases hg : p < dep.quorum.numParties ∧ p ∉ c.corrupt ∧
        c.corrupt.length + 1 < dep.quorum.threshold
    · rw [dc_if_pos hg] at hStep
      cases hStep
      have hStepA := idealCustodyStep_corrupt_of (S := dep.digests) (oracleSign := dep.idealOracle)
        (st := a) (p := p) ⟨hNum ▸ hg.1, hRel.corrupt ▸ hg.2.1, by
          rw [hRel.corrupt, hThr]
          exact hg.2.2⟩
      refine ⟨{ a with corruptParties := p :: a.corruptParties }, ?_, ?_⟩
      · rw [hStepA]
        show some (_, CustodyOutcome.corrupted (custodyRevealed a.honestApprovals p)) =
          some (_, CustodyOutcome.corrupted (c.nodes p).latched)
        rw [hRel.latched p]
      · exact
          { inv :=
              { deployment := hRel.inv.deployment
                enrolled := hRel.inv.enrolled
                profile := hRel.inv.profile
                shares := hRel.inv.shares
                latchBound := hRel.inv.latchBound
                latchNodup := hRel.inv.latchNodup }
            ledger := hRel.ledger
            corrupt := congrArg (List.cons p) hRel.corrupt
            latched := hRel.latched
            buffered := hRel.buffered }
    · rw [dc_if_neg hg] at hStep
      cases hStep
  | crash _ => cases hVis
  | dropMsg _ => cases hVis
  | execute d approvers i ab =>
    have hj : CustodyInput.sign d i ab = j := Option.some.inj hVis
    subst hj
    have hStep' : (executeStep dep c d approvers i ab).map (fun r => (r.1, Event.custody r.2)) =
        some (c', ev) := hStep
    cases hEx : executeStep dep c d approvers i ab with
    | none => rw [hEx] at hStep'; cases hStep'
    | some r =>
      obtain ⟨c₁, o⟩ := r
      rw [hEx] at hStep'
      cases hStep'
      obtain ⟨L', hL, hc₁⟩ := executeStep_inv hEx
      subst hc₁
      have hIdeal := executeStep_ledger_ideal dep hWf hL
      have hCount : (if quorumReady dep c.buffer approvers i then approvers.length else 0) ≤
          (custodyApprovers a.ledger.quorum.numParties a.honestApprovals a.corruptApprovals
            a.ledger.deploymentId i).length := by
        cases hQ : quorumReady dep c.buffer approvers i with
        | false =>
          rw [dc_if_neg Bool.false_ne_true]
          exact Nat.zero_le _
        | true =>
          rw [dc_if_pos rfl]
          obtain ⟨_, hNd, hAll⟩ := quorumReady_spec dep c.buffer approvers i hQ
          refine custodyApprovers_length_le_of_subset hNd (fun p hp => ?_)
          obtain ⟨hLt, s, hs⟩ := hAll p hp
          obtain ⟨m, hmBuf, hmS, hmD, hmI, _, _⟩ := approvalShare_sound dep c.buffer i p s hs
          have hB := hRel.buffered m hmBuf hmD
          rw [hmS, hmD, hmI] at hB
          rw [hDep]
          exact ⟨hNum ▸ hLt, hB⟩
      have hA := custodyLedgerSign_mono hIdeal hCount
      rw [← hRel.ledger] at hA
      refine ⟨_, idealCustodyStep_sign_of hA, ?_⟩
      obtain ⟨hD', hPk', hQ'⟩ := custodyLedgerSign_static hL
      exact
        { inv :=
            { deployment := hD'.trans hRel.inv.deployment
              enrolled := hPk'.trans hRel.inv.enrolled
              profile := hQ'.trans hRel.inv.profile
              shares := hRel.inv.shares
              latchBound := hRel.inv.latchBound
              latchNodup := hRel.inv.latchNodup }
          ledger := rfl
          corrupt := hRel.corrupt
          latched := hRel.latched
          buffered := hRel.buffered }

/-- Internal turns preserve the relation with the same ideal state. -/
theorem step_sim_internal (dep : Deployment F C PK D Sig)
    {c c' : State F PK D Sig} {a : IdealCustodyState PK D Sig} {turn : Turn F}
    {ev : Event F Sig}
    (hRel : Rel dep c a) (hStep : step dep c turn = some (c', ev))
    (hInt : visIn dep turn = none) : Rel dep c' a := by
  cases turn with
  | approve _ _ _ => cases hInt
  | inject m =>
    unfold visIn at hInt
    dsimp only at hInt
    by_cases hmD : m.deploymentId = dep.deploymentId
    · rw [dc_if_pos hmD] at hInt
      cases hInt
    · unfold step at hStep
      dsimp only at hStep
      by_cases hg : m.sender ∈ c.corrupt
      · rw [dc_if_pos hg] at hStep
        cases hStep
        exact
          { inv :=
              { deployment := hRel.inv.deployment
                enrolled := hRel.inv.enrolled
                profile := hRel.inv.profile
                shares := hRel.inv.shares
                latchBound := hRel.inv.latchBound
                latchNodup := hRel.inv.latchNodup }
            ledger := hRel.ledger
            corrupt := hRel.corrupt
            latched := hRel.latched
            buffered := fun m' hm' hm'D => by
              rcases List.mem_cons.mp hm' with hEq | hOld
              · exact absurd (hEq ▸ hm'D) hmD
              · exact hRel.buffered m' hOld hm'D }
      · rw [dc_if_neg hg] at hStep
        cases hStep
  | corrupt _ => cases hInt
  | crash p =>
    unfold step at hStep
    cases hStep
    exact
      { inv := inv_of_node_update dep c p _ _ _ hRel.inv rfl
          (fun e he => hRel.inv.latchBound p e he) (hRel.inv.latchNodup p)
        ledger := hRel.ledger
        corrupt := hRel.corrupt
        latched := fun q => by
          show (setNode c.nodes p _ q).latched = custodyRevealed a.honestApprovals q
          by_cases hqp : q = p
          · subst hqp
            rw [setNode_self]
            exact hRel.latched q
          · rw [setNode_ne _ _ _ _ hqp]
            exact hRel.latched q
        buffered := hRel.buffered }
  | dropMsg idx =>
    unfold step at hStep
    cases hStep
    exact
      { inv :=
          { deployment := hRel.inv.deployment
            enrolled := hRel.inv.enrolled
            profile := hRel.inv.profile
            shares := hRel.inv.shares
            latchBound := hRel.inv.latchBound
            latchNodup := hRel.inv.latchNodup }
        ledger := hRel.ledger
        corrupt := hRel.corrupt
        latched := hRel.latched
        buffered := fun m hm hmD => by
          rcases List.mem_append.mp hm with hT | hDr
          · exact hRel.buffered m (List.mem_of_mem_take hT) hmD
          · exact hRel.buffered m (List.mem_of_mem_drop hDr) hmD }
  | execute _ _ _ _ => cases hInt

/-- **Distributed `(t, n)` custody refines `Spec.idealCustodyMachine`** for the deployment's own
    `deploymentId`, with the dealt key's signature as the ideal oracle. -/
def distCustody_refines_ideal (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed) :
    DataRefines (distMachine dep)
      (idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk dep.quorum)
      (visIn dep) visOut where
  Rel := Rel dep
  absInit := fun _ => IdealCustodyState.init dep.deploymentId dep.pk dep.quorum
  init_ok {c₀} hInit := by
    have h0 : c₀ = State.init dep := hInit
    subst h0
    exact ⟨rfl, init_rel dep⟩
  sim_visible hRel hStepC hVis := step_sim_visible dep hWf hRel hStepC hVis
  sim_internal hRel hStepC hVis := step_sim_internal dep hRel hStepC hVis
  sim_reject hRel _ := hRel

/-- Every execution of the distributed system projects to an execution of the ideal
    functionality on its `approve`, `inject`, `corrupt` and `execute` turns. -/
theorem distCustody_trace_inclusion (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed)
    {tr : List (Turn F × Event F Sig)} (hAdmits : (distMachine dep).AdmitsTrace tr) :
    (idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk
        dep.quorum).AdmitsTrace (projectTrace (visIn dep) visOut tr) :=
  (distCustody_refines_ideal dep hWf).preserve_admitsTrace hAdmits

/-! ## 7. Consequences on reachable states -/

/-- **Safety of every reachable distributed state.** Fewer than `threshold` custodians are
    corrupted; cumulative spend is within the cap; every WAL record carries the dealt key's
    signature on `digest deploymentId intent`, and its intent is in the durable log of an enrolled
    custodian, whose latch has moved past its epoch. -/
theorem distCustody_reachable_safe (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed)
    {st : State F PK D Sig} (hReach : (distMachine dep).Reachable st) :
    st.corrupt.length < dep.quorum.threshold ∧
    st.ledger.spent ≤ dep.quorum.spendCap ∧
    (∀ r : CustodyRelease D Sig, r ∈ st.ledger.releasedHistory →
      r.sig = dep.signWith dep.secret (dep.digests.digest dep.deploymentId r.intent) ∧
      ∃ p : Nat, p < dep.quorum.numParties ∧ r.intent ∈ (st.nodes p).latched ∧
        r.intent.epoch < (st.nodes p).latch) := by
  obtain ⟨a, hReachA, hRel⟩ := (distCustody_refines_ideal dep hWf).reachable_rel hReach
  have hRel' : Rel dep st a := hRel
  have hSafe := idealCustody_reachable_safeInv hReachA
  refine ⟨hRel'.corrupt ▸ hSafe.corruptBudget, hRel'.ledger ▸ hSafe.budget, ?_⟩
  intro r hr
  obtain ⟨hSig, p, hLt, hMem⟩ :=
    idealCustody_reachable_release_honestly_approved hReachA (hRel'.ledger ▸ hr)
  refine ⟨hSig, p, hLt, ?_⟩
  have hLat : r.intent ∈ (st.nodes p).latched := by
    rw [hRel'.latched p]
    unfold custodyRevealed
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hMem, decide_eq_true rfl⟩, rfl⟩
  exact ⟨hLat, hRel'.inv.latchBound p _ hLat⟩

/-- **Honest custodians do not equivocate.** In every reachable state a custodian has latched at
    most one intent per epoch. -/
theorem distCustody_latch_unique (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed)
    {st : State F PK D Sig} (hReach : (distMachine dep).Reachable st) (p : Nat) :
    ((st.nodes p).latched.map CustodyIntent.epoch).Nodup := by
  obtain ⟨_, _, hRel⟩ := (distCustody_refines_ideal dep hWf).reachable_rel hReach
  have hRel' : Rel dep st _ := hRel
  exact hRel'.inv.latchNodup p

/-- **The durable latch survives a crash; the coupons do not.** After custodian `p` crashes its
    coupons are gone, and it still refuses to approve any intent at an epoch it has latched. -/
theorem latched_epoch_rejected_after_crash (dep : Deployment F C PK D Sig)
    {st st' : State F PK D Sig} {ev : Event F Sig} (hInv : Inv dep st) (p : Nat)
    (hCrash : step dep st (.crash p) = some (st', ev))
    (d : Nat) (i e : CustodyIntent) (hEpoch : e.epoch = i.epoch)
    (hLatched : e ∈ (st.nodes p).latched) :
    (st'.nodes p).coupons = [] ∧ step dep st' (.approve p d i) = none := by
  unfold step at hCrash
  cases hCrash
  have hLt : i.epoch < (st.nodes p).latch := hEpoch ▸ hInv.latchBound p _ hLatched
  refine ⟨?_, ?_⟩
  · show (setNode st.nodes p _ p).coupons = []
    rw [setNode_self]
  · unfold step
    dsimp only
    refine dc_if_neg (fun hg => ?_) _ _
    have hLe : (setNode st.nodes p
        { share := (st.nodes p).share, latch := (st.nodes p).latch,
          latched := (st.nodes p).latched, coupons := [] } p).latch ≤ i.epoch := hg.2.2.2.1
    rw [setNode_self] at hLe
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLt hLe)

/-- **Conditional liveness of the coordinator.** If the quorum check passes for `approvers` and
    `i`, the ledger is not quarantined, has no committed record at `i.epoch`, the epoch and session
    are fresh and `i.spend` fits the budget, then `execute` releases the dealt key's signature on
    `digest deploymentId i`. -/
theorem execute_ready_fresh_releases (dep : Deployment F C PK D Sig) (hWf : dep.WellFormed)
    {st : State F PK D Sig} (hInv : Inv dep st) (approvers : List Nat) (i : CustodyIntent)
    (hReady : quorumReady dep st.buffer approvers i = true)
    (hP : st.ledger.poisoned = false)
    (hF : findReleasedEpoch st.ledger.releasedHistory i.epoch = none)
    (hEp : st.ledger.nextFreshEpoch ≤ i.epoch) (hSess : i.sessionId ∉ st.ledger.usedSessions)
    (hCap : st.ledger.spent + i.spend ≤ dep.quorum.spendCap) :
    (step dep st (.execute dep.deploymentId approvers i false)).map Prod.snd =
      some (.custody (.released
        (dep.signWith dep.secret (dep.digests.digest dep.deploymentId i)))) := by
  obtain ⟨hThr, _, _⟩ := quorumReady_spec dep st.buffer approvers i hReady
  have hL := custodyLedgerSign_fresh_release (S := dep.digests)
    (oracleSign := dep.signWith (quorumKey dep st.buffer approvers i))
    (L := st.ledger) (n := approvers.length) (dep := dep.deploymentId) (i := i)
    hP hInv.deployment.symm hF hEp hSess (hInv.profile ▸ hThr) (hInv.profile ▸ hCap)
  rw [quorumKey_eq_secret dep hWf st.buffer approvers i hReady, hInv.deployment] at hL
  show ((executeStep dep st dep.deploymentId approvers i false).map
    (fun r => (r.1, Event.custody r.2))).map Prod.snd = _
  unfold executeStep
  rw [hReady, dc_if_pos rfl, quorumKey_eq_secret dep hWf st.buffer approvers i hReady, hL]
  rfl

end Defs

/-! ## 8. Unconditional Share-Check Branching & Zero-Reconstruction Share-Opening Custody (`L-Ex-6`)

Upgrades the distributed custody refinement along all three model axes:
1. **Genuine `Spec.SigScheme` (`ShareOpeningDeployment.sigScheme`)**: signatures are produced and
   verified against a real `Spec.SigScheme PK SK Sig` (`verify pk (encodeDigest digest) sig = true`
   via `sigScheme.correct`), replacing uninterpreted `signWith : F → D → Sig`.
2. **Share-Level Per-Request Opening Release (Zero Key Reconstruction)**: each custodian holds only
   its local `Share` and emits only a per-request contribution `Contrib` (`evalContrib`) on `.approve`;
   the public combiner `assembleSig : List (Nat × Contrib) → Nat → D → Option Sig` assembles the
   signature without any party or coordinator holding or reconstructing `SK` or long-term `Share`s.
3. **Collision-Branching 256-Bit Commitment (`commit : Preimage → BitVec 256`)**: eliminates global
   commitment injectivity (`commit_binding`), providing both:
   * `distCustody_injOn_dataRefines_ideal`: finite-set `InjOnPreimages` on observed preimages yields
     full `Spec.DataRefines` into `Spec.idealCustodyMachine`, and
   * `distCustody_dataRefines_or_collision`: unconditionally for ANY compressing 256-bit hash
     `commit : Preimage → BitVec 256`, every multi-turn trace of `shareOpeningMachine` either
     projects to an admitted `Spec.idealCustodyMachine` trace with `sigScheme.verify = true` on
     every released/WAL signature, or constructively yields an explicit colliding pair `x₁ ≠ x₂`
     observed in the transcript with `commit x₁ = commit x₂` (`0 Classical.choice`). -/

section UnconditionalAndShareOpening

/-- Deployment structural conditions WITHOUT global `commit_binding`. -/
structure Deployment.WellFormedNoBinding {F C PK D Sig : Type} [LawfulField F]
    (dep : Deployment F C PK D Sig) : Prop where
  points_nodup : ((List.range dep.quorum.numParties).map dep.point).Nodup
  points_nonzero : ∀ p : Nat, p < dep.quorum.numParties → dep.point p ≠ CommRingOps.zero
  degree : dep.poly.length = dep.quorum.threshold
  commitments_dealt : ∀ p : Nat, p < dep.quorum.numParties →
    dep.shareCommitment p = dep.commit (dep.trueShare p)

/-- Unconditional reconstruction-or-collision lemma from `verifyShare_dealt_or_collision`:
    without `commit_binding`, any accepted quorum either reconstructs `dep.secret` or witnesses an
    explicit buffered share collision against a dealt share commitment (`0 Classical.choice`). -/
theorem quorumKey_eq_secret_or_collision {F C PK D Sig : Type}
    [LawfulField F] [DecidableEq F] [DecidableEq C]
    (dep : Deployment F C PK D Sig) (hWf : dep.WellFormedNoBinding)
    (buffer : List (Approval F)) (approvers : List Nat) (i : CustodyIntent)
    (h : quorumReady dep buffer approvers i = true) :
    quorumKey dep buffer approvers i = dep.secret ∨
      ∃ m ∈ buffer, ∃ p < dep.quorum.numParties,
        m.sender = p ∧ m.deploymentId = dep.deploymentId ∧ m.intent = i ∧
        m.share ≠ dep.trueShare p ∧ dep.commit m.share = dep.commit (dep.trueShare p) := by
  obtain ⟨hThr, hNd, hAll⟩ := quorumReady_spec dep buffer approvers i h
  cases hMis : approvers.find? (fun p =>
      decide ((approvalShare dep buffer i p).getD CommRingOps.zero ≠ dep.trueShare p)) with
  | none =>
    left
    have hShares : approvers.map
        (fun p => (approvalShare dep buffer i p).getD CommRingOps.zero) =
        approvers.map dep.trueShare := by
      apply List.map_congr_left
      intro p hp
      have hFalse := List.find?_eq_none.mp hMis p hp
      by_cases hEq : (approvalShare dep buffer i p).getD CommRingOps.zero = dep.trueShare p
      · exact hEq
      · exact absurd (decide_eq_true hEq) hFalse
    have hPointInj : ∀ p q : Nat, p < dep.quorum.numParties → q < dep.quorum.numParties →
        dep.point p = dep.point q → p = q := fun p q hp hq hEq =>
      inj_of_nodup_map dep.point _ hWf.points_nodup p q
        (List.mem_range.mpr hp) (List.mem_range.mpr hq) hEq
    have hPtsNd : (approvers.map dep.point).Nodup :=
      nodup_map_of_inj_on dep.point dep.quorum.numParties hPointInj approvers hNd
        (fun p hp => (hAll p hp).1)
    have hLen : (approvers.map dep.point).length = approvers.length := List.length_map _
    unfold quorumKey reconstruct
    rw [hShares, zipWith_map_map]
    have hMap : approvers.map (fun a =>
        lagrangeToAdditiveShare (approvers.map dep.point) (dep.point a) (dep.trueShare a)) =
        (approvers.map dep.point).map (fun x =>
          lagrangeToAdditiveShare (approvers.map dep.point) x
            (RoundPoly.evalCoeffs dep.poly x)) :=
      (List.map_map (f := dep.point)
        (g := fun x => lagrangeToAdditiveShare (approvers.map dep.point) x
          (RoundPoly.evalCoeffs dep.poly x)) (l := approvers)).symm
    rw [hMap]
    exact lagrange_to_additive_reconstructs_poly (approvers.map dep.point).length
      (hLen ▸ Nat.le_trans dep.quorum.h_pos hThr) (approvers.map dep.point) hPtsNd rfl
      dep.poly (hLen ▸ hWf.degree ▸ hThr)
  | some p =>
    right
    have hpMem : p ∈ approvers := List.mem_of_find?_eq_some hMis
    have hpNe : (approvalShare dep buffer i p).getD CommRingOps.zero ≠ dep.trueShare p :=
      of_decide_eq_true (List.find?_some
        (p := fun q => decide ((approvalShare dep buffer i q).getD CommRingOps.zero ≠ dep.trueShare q)) hMis)
    obtain ⟨hLt, s, hs⟩ := hAll p hpMem
    rw [hs] at hpNe
    dsimp only [Option.getD] at hpNe
    obtain ⟨m, hmBuf, hmS, hmD, hmI, hmShare, hVer⟩ := approvalShare_sound dep buffer i p s hs
    rcases verifyShare_dealt_or_collision dep (hWf.commitments_dealt p hLt) hVer with hEq | ⟨hNe, hCol⟩
    · exact absurd hEq hpNe
    · exact ⟨m, hmBuf, p, hLt, hmS, hmD, hmI, hmShare ▸ hNe, hmShare ▸ hCol⟩

/-- One share-opening custodian: holds its private `Share`, durable epoch latch, and volatile coupons. -/
structure ShareCustodian (Share : Type) where
  share : Share
  latch : Nat
  latched : List CustodyIntent
  coupons : List Nat

/-- Per-request share-opening approval in transit: carries ONLY the per-request contribution `contrib`
    (never the custodian's reusable `Share` or `SK`). -/
structure ShareApproval (Contrib : Type) where
  sender : Nat
  deploymentId : Nat
  intent : CustodyIntent
  contrib : Contrib
  deriving DecidableEq, Repr

/-- Distributed state of the share-opening custody machine (zero `SK` in state). -/
structure ShareState (Share Contrib PK D Sig : Type) where
  nodes : Nat → ShareCustodian Share
  buffer : List (ShareApproval Contrib)
  corrupt : List Nat
  ledger : CustodyLedger PK D Sig

/-- Schedule alphabet of the share-opening custody machine. -/
inductive ShareTurn (Contrib : Type) where
  | approve (p deploymentId : Nat) (intent : CustodyIntent)
  | inject (m : ShareApproval Contrib)
  | corrupt (p : Nat)
  | crash (p : Nat)
  | dropMsg (idx : Nat)
  | execute (deploymentId : Nat) (approvers : List Nat) (intent : CustodyIntent)
      (abortBeforeRelease : Bool)
  deriving DecidableEq, Repr

/-- Observable event of the share-opening custody machine. -/
inductive ShareEvent (Share Sig : Type) where
  | approved
  | injected
  | corrupted (share : Share) (latched : List CustodyIntent)
  | recovered
  | dropped
  | custody (out : CustodyOutcome Sig)
  deriving DecidableEq, Repr

/-- Share-opening deployment parameterized over a genuine `Spec.SigScheme PK SK Sig`, per-request
    share-opening evaluator `evalContrib`, public key-free signature combiner `assembleSig`, and a
    compressing 256-bit commitment hash `commit : Preimage → BitVec 256`. -/
structure ShareOpeningDeployment (Share Contrib Preimage PK SK D Sig : Type) where
  deploymentId : Nat
  quorum : CustodyQuorumProfile
  sigScheme : SigScheme PK SK Sig
  dealtSk : SK
  fallbackSig : Sig
  digests : CustodyDigestScheme D
  encodeDigest : D → Bytes
  epochOfDigest : D → Nat
  dealShare : Nat → Share
  evalContrib : Nat → Share → Nat → CustodyIntent → Contrib
  assembleSig : List (Nat × Contrib) → Nat → D → Option Sig
  preimageOf : Nat → Nat → CustodyIntent → Contrib → Preimage
  commit : Preimage → BitVec 256
  commitmentOf : Nat → Nat → CustodyIntent → BitVec 256

/-- Enrolled public key derived via `sigScheme.derivePk`. -/
def ShareOpeningDeployment.pk {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) : PK :=
  dep.sigScheme.derivePk dep.dealtSk

/-- Dealt per-request share contribution of custodian `p` for intent `i`. -/
def ShareOpeningDeployment.trueContrib {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (p : Nat) (i : CustodyIntent) : Contrib :=
  dep.evalContrib p (dep.dealShare p) dep.deploymentId i

/-- Ideal signing oracle induced by `sigScheme.sign dealtSk`. -/
def ShareOpeningDeployment.idealOracle {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) (d : D) : Sig :=
  (dep.sigScheme.sign dep.dealtSk (dep.epochOfDigest d) (dep.encodeDigest d)).getD dep.fallbackSig

/-- Deployment structural laws — ZERO global `commit` injectivity assumption! -/
structure ShareOpeningDeployment.WellFormed {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) : Prop where
  /-- Digest recovers `i.epoch` via `epochOfDigest`. -/
  epoch_digest : ∀ i : CustodyIntent,
    dep.epochOfDigest (dep.digests.digest dep.deploymentId i) = i.epoch
  /-- Preimage encoding frames `Contrib` injectively at fixed `(p, d, i)`. -/
  preimage_framed : ∀ (p d : Nat) (i : CustodyIntent) (c₁ c₂ : Contrib),
    dep.preimageOf p d i c₁ = dep.preimageOf p d i c₂ → c₁ = c₂
  /-- Public commitments match `commit` of the dealt per-request contributions. -/
  commitments_dealt : ∀ p : Nat, p < dep.quorum.numParties → ∀ i : CustodyIntent,
    dep.commitmentOf p dep.deploymentId i =
      dep.commit (dep.preimageOf p dep.deploymentId i (dep.trueContrib p i))
  /-- Public assembly of dealt per-request contributions agrees with `sigScheme.sign dealtSk`. -/
  assemble_dealt : ∀ (approvers : List Nat) (i : CustodyIntent),
    approvers.Nodup →
    (∀ p, p ∈ approvers → p < dep.quorum.numParties) →
    dep.quorum.threshold ≤ approvers.length →
    dep.assembleSig (approvers.map (fun p => (p, dep.trueContrib p i))) i.epoch
      (dep.digests.digest dep.deploymentId i) =
      dep.sigScheme.sign dep.dealtSk i.epoch
        (dep.encodeDigest (dep.digests.digest dep.deploymentId i))

/-- Initial state of the share-opening custody machine (stores only `dealShare p` per node and
    `sigScheme.derivePk dealtSk` in the ledger; `dealtSk` never enters runtime state). -/
@[expose] def ShareState.init {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) :
    ShareState Share Contrib PK D Sig where
  nodes := fun p => { share := dep.dealShare p, latch := 0, latched := [], coupons := [] }
  buffer := []
  corrupt := []
  ledger := (IdealCustodyState.init dep.deploymentId (dep.sigScheme.derivePk dep.dealtSk) dep.quorum).ledger

/-- One transition of the share-opening custody machine. Notice `dep.dealtSk` is NEVER read in any
    runtime transition (`derivePk dep.dealtSk` is read from `st.ledger.enrolledPk`!). -/
@[expose] def shareOpeningStep {Share Contrib Preimage PK SK D Sig : Type} [DecidableEq D]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (st : ShareState Share Contrib PK D Sig) :
    ShareTurn Contrib → Option (ShareState Share Contrib PK D Sig × ShareEvent Share Sig)
  | .approve p d i =>
    if p < dep.quorum.numParties ∧ p ∉ st.corrupt ∧ d = dep.deploymentId ∧
        (st.nodes p).latch ≤ i.epoch ∧ i.sessionId ∉ (st.nodes p).coupons then
      let contrib := dep.evalContrib p (st.nodes p).share d i
      some ({ st with
              nodes := fun q =>
                if q = p then
                  { share := (st.nodes p).share
                    latch := i.epoch + 1
                    latched := i :: (st.nodes p).latched
                    coupons := i.sessionId :: (st.nodes p).coupons }
                else st.nodes q
              buffer := { sender := p, deploymentId := d, intent := i, contrib := contrib } :: st.buffer },
            .approved)
    else none
  | .inject m =>
    if m.sender ∈ st.corrupt then
      some ({ st with buffer := m :: st.buffer }, .injected)
    else none
  | .corrupt p =>
    if p < dep.quorum.numParties ∧ p ∉ st.corrupt ∧
        st.corrupt.length + 1 < dep.quorum.threshold then
      some ({ st with corrupt := p :: st.corrupt },
            .corrupted (st.nodes p).share (st.nodes p).latched)
    else none
  | .crash p =>
    some ({ st with
            nodes := fun q =>
              if q = p then
                { share := (st.nodes p).share
                  latch := (st.nodes p).latch
                  latched := (st.nodes p).latched
                  coupons := [] }
              else st.nodes q },
          .recovered)
  | .dropMsg idx =>
    some ({ st with buffer := st.buffer.take idx ++ st.buffer.drop (idx + 1) }, .dropped)
  | .execute d approvers i ab =>
    let matchMsg (p : Nat) (m : ShareApproval Contrib) : Bool :=
      decide (m.sender = p) && decide (m.deploymentId = dep.deploymentId) &&
      decide (m.intent = i) &&
      decide (dep.commit (dep.preimageOf p dep.deploymentId i m.contrib) =
        dep.commitmentOf p dep.deploymentId i)
    let ready : Bool :=
      decide (dep.quorum.threshold ≤ approvers.length) &&
      decide approvers.Nodup &&
      approvers.all (fun p =>
        decide (p < dep.quorum.numParties) && (st.buffer.find? (matchMsg p)).isSome)
    match findReleasedEpoch st.ledger.releasedHistory i.epoch with
    | some _ =>
      (custodyLedgerSign dep.digests (fun _ => dep.fallbackSig) st.ledger 0 d i ab).map
        (fun r => ({ st with ledger := r.1 }, .custody r.2))
    | none =>
      if ab = true then
        (custodyLedgerSign dep.digests (fun _ => dep.fallbackSig) st.ledger
          (if ready then approvers.length else 0) d i true).map
          (fun r => ({ st with ledger := r.1 }, .custody r.2))
      else if ready = true then
        let contribs : List (Nat × Contrib) :=
          approvers.filterMap (fun p =>
            (st.buffer.find? (matchMsg p)).map (fun m => (p, m.contrib)))
        let dig := dep.digests.digest dep.deploymentId i
        match dep.assembleSig contribs i.epoch dig with
        | none => none
        | some sig =>
          if dep.sigScheme.verify st.ledger.enrolledPk (dep.encodeDigest dig) sig = true then
            (custodyLedgerSign dep.digests (fun _ => sig) st.ledger approvers.length d i false).map
              (fun r => ({ st with ledger := r.1 }, .custody r.2))
          else none
      else none

/-- Reactive `Spec.Machine` for the share-opening threshold custody system. -/
def shareOpeningMachine {Share Contrib Preimage PK SK D Sig : Type} [DecidableEq D]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) :
    Machine (ShareState Share Contrib PK D Sig) (ShareTurn Contrib) (ShareEvent Share Sig) where
  Init st := st = ShareState.init dep
  step := shareOpeningStep dep
  errStep st _ := st

/-- Interface map from `ShareTurn` to `Spec.CustodyInput`. -/
def shareVisIn {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) :
    ShareTurn Contrib → Option CustodyInput
  | .approve p d i => some (.approve p d i)
  | .inject m =>
    if m.deploymentId = dep.deploymentId then
      some (.advApprove m.sender m.deploymentId m.intent)
    else none
  | .corrupt p => some (.corrupt p)
  | .crash _ => none
  | .dropMsg _ => none
  | .execute d _ i ab => some (.sign d i ab)

/-- Interface map from `ShareEvent` to `Spec.CustodyOutcome`. -/
def shareVisOut {Share Sig : Type} : ShareEvent Share Sig → CustodyOutcome Sig
  | .approved => .approvalRecorded
  | .injected => .approvalRecorded
  | .corrupted _ latched => .corrupted latched
  | .recovered => .approvalRecorded
  | .dropped => .approvalRecorded
  | .custody out => out

theorem shareVisIn_eq {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (t : ShareTurn Contrib) :
    shareVisIn dep t =
      match t with
      | .approve p d i => some (.approve p d i)
      | .inject m =>
        if m.deploymentId = dep.deploymentId then
          some (.advApprove m.sender m.deploymentId m.intent)
        else none
      | .corrupt p => some (.corrupt p)
      | .crash _ => none
      | .dropMsg _ => none
      | .execute d _ i ab => some (.sign d i ab) := by
  cases t <;> rfl

theorem shareVisOut_eq {Share Sig : Type} (e : ShareEvent Share Sig) :
    shareVisOut e =
      match e with
      | .approved => .approvalRecorded
      | .injected => .approvalRecorded
      | .corrupted _ latched => .corrupted latched
      | .recovered => .approvalRecorded
      | .dropped => .approvalRecorded
      | .custody out => out := by
  cases e <;> rfl

/-- Constructive share-contribution check (`0 Classical.choice`): any contribution `c` passing the
    256-bit commitment check for enrolled custodian `p` is either `dep.trueContrib p i` or produces
    an explicit colliding preimage pair `x₁ ≠ x₂` under `dep.commit`. -/
theorem verifyContrib_dealt_or_collision {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq Contrib]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (hWf : dep.WellFormed) {p : Nat} {i : CustodyIntent} {c : Contrib}
    (hp : p < dep.quorum.numParties)
    (hVer : dep.commit (dep.preimageOf p dep.deploymentId i c) =
      dep.commitmentOf p dep.deploymentId i) :
    c = dep.trueContrib p i ∨
      (dep.preimageOf p dep.deploymentId i c ≠
        dep.preimageOf p dep.deploymentId i (dep.trueContrib p i) ∧
       dep.commit (dep.preimageOf p dep.deploymentId i c) =
        dep.commit (dep.preimageOf p dep.deploymentId i (dep.trueContrib p i))) := by
  have hCol : dep.commit (dep.preimageOf p dep.deploymentId i c) =
      dep.commit (dep.preimageOf p dep.deploymentId i (dep.trueContrib p i)) :=
    hVer.trans (hWf.commitments_dealt p hp i)
  by_cases hc : c = dep.trueContrib p i
  · exact .inl hc
  · refine .inr ⟨fun hPre => hc (hWf.preimage_framed p dep.deploymentId i c _ hPre), hCol⟩

/-- Preimages observed across all `.approve` and `.inject` turns in a trace (paired with dealt
    counterpart preimages so any collision in the execution lies inside this finite list). -/
def observedSharePreimages {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) :
    List (ShareTurn Contrib × ShareEvent Share Sig) → List Preimage
  | [] => []
  | (turn, _) :: rest =>
    match turn with
    | .approve p d i =>
      dep.preimageOf p d i (dep.evalContrib p (dep.dealShare p) d i) ::
      dep.preimageOf p d i (dep.trueContrib p i) ::
      observedSharePreimages dep rest
    | .inject m =>
      dep.preimageOf m.sender m.deploymentId m.intent m.contrib ::
      dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ::
      observedSharePreimages dep rest
    | _ => observedSharePreimages dep rest

/-- Finite-set injectivity (`InjOn`) of `commit` restricted to an observed preimage list `obs`.
    Unlike global injectivity on `Bytes → BitVec 256` (which is mathematically `False`), this
    finite-set condition holds and is kernel-decidable on every collision-free execution. -/
abbrev InjOnPreimages {Preimage : Type} (commit : Preimage → BitVec 256) (obs : List Preimage) : Prop :=
  ∀ x ∈ obs, ∀ y ∈ obs, commit x = commit y → x = y

instance instDecidableInjOnPreimages {Preimage : Type} [DecidableEq Preimage]
    (commit : Preimage → BitVec 256) (obs : List Preimage) :
    Decidable (InjOnPreimages commit obs) :=
  if h : obs.all (fun x => obs.all (fun y => !decide (commit x = commit y) || decide (x = y))) then
    .isTrue (fun x hx y hy hEq => by
      have hx' := List.all_eq_true.mp h x hx
      have hy' := List.all_eq_true.mp hx' y hy
      rcases Bool.or_eq_true_iff.mp hy' with hNe | hSame
      · rw [decide_eq_true hEq] at hNe; cases hNe
      · exact of_decide_eq_true hSame)
  else
    .isFalse (fun hInj => h (by
      rw [List.all_eq_true]
      intro x hx
      rw [List.all_eq_true]
      intro y hy
      by_cases hEq : commit x = commit y
      · exact Bool.or_eq_true_iff.mpr (.inr (decide_eq_true (hInj x hx y hy hEq)))
      · rw [decide_eq_false hEq]; rfl))

/-- Guarded transition restricting buffered messages to a finite observed preimage list `obs`. -/
def shareOpeningObservedStep {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq Preimage] [DecidableEq D]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (obs : List Preimage)
    (st : ShareState Share Contrib PK D Sig) (turn : ShareTurn Contrib) :
    Option (ShareState Share Contrib PK D Sig × ShareEvent Share Sig) :=
  match turn with
  | .approve p d i =>
    let c := dep.evalContrib p (st.nodes p).share d i
    if dep.preimageOf p d i c ∈ obs ∧ dep.preimageOf p d i (dep.trueContrib p i) ∈ obs then
      shareOpeningStep dep st (.approve p d i)
    else none
  | .inject m =>
    if dep.preimageOf m.sender m.deploymentId m.intent m.contrib ∈ obs ∧
        dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ∈ obs then
      shareOpeningStep dep st (.inject m)
    else none
  | t => shareOpeningStep dep st t

/-- Guarded `Spec.Machine` over a finite observed preimage domain `obs`. -/
def shareOpeningObservedMachine {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq Preimage] [DecidableEq D]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (obs : List Preimage) :
    Machine (ShareState Share Contrib PK D Sig) (ShareTurn Contrib) (ShareEvent Share Sig) where
  Init st := st = ShareState.init dep
  step := shareOpeningObservedStep dep obs
  errStep st _ := st

/-- Concrete state invariant of `ShareState`. -/
structure ShareInv {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (st : ShareState Share Contrib PK D Sig) : Prop where
  deployment : st.ledger.deploymentId = dep.deploymentId
  enrolled : st.ledger.enrolledPk = dep.pk
  profile : st.ledger.quorum = dep.quorum
  shares : ∀ p : Nat, (st.nodes p).share = dep.dealShare p
  latchBound : ∀ (p : Nat) (e : CustodyIntent), e ∈ (st.nodes p).latched →
    e.epoch < (st.nodes p).latch
  latchNodup : ∀ p : Nat, ((st.nodes p).latched.map CustodyIntent.epoch).Nodup
  walVerified : ∀ r ∈ st.ledger.releasedHistory,
    dep.sigScheme.verify dep.pk (dep.encodeDigest r.digest) r.sig = true

/-- Simulation relation from `ShareState` into `Spec.IdealCustodyState`. -/
structure ShareRel {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (c : ShareState Share Contrib PK D Sig)
    (a : IdealCustodyState PK D Sig) : Prop where
  inv : ShareInv dep c
  ledger : a.ledger = c.ledger
  corrupt : a.corruptParties = c.corrupt
  latched : ∀ p : Nat, (c.nodes p).latched = custodyRevealed a.honestApprovals p
  buffered : ∀ m : ShareApproval Contrib, m ∈ c.buffer → m.deploymentId = dep.deploymentId →
    CustodyApproval.mk m.sender m.deploymentId m.intent ∈ a.honestApprovals ∨
      CustodyApproval.mk m.sender m.deploymentId m.intent ∈ a.corruptApprovals

private theorem sh_if_pos {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem sh_if_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem shareInit_rel {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) :
    ShareRel dep (ShareState.init dep : ShareState Share Contrib PK D Sig)
      (IdealCustodyState.init dep.deploymentId dep.pk dep.quorum) where
  inv :=
    { deployment := rfl
      enrolled := rfl
      profile := rfl
      shares _ := rfl
      latchBound _ _ h := absurd h List.not_mem_nil
      latchNodup _ := List.nodup_nil
      walVerified _ h := absurd h List.not_mem_nil }
  ledger := rfl
  corrupt := rfl
  latched _ := rfl
  buffered _ h _ := absurd h List.not_mem_nil

private theorem filterMap_all_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (L : List α), (∀ a ∈ L, f a = some (g a)) → L.filterMap f = L.map g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons,
      filterMap_all_some f g xs (fun a ha => h a (List.mem_cons_of_mem _ ha))]

private theorem option_map_ledger_buffer {Share Contrib PK D Sig : Type}
    {c c' : ShareState Share Contrib PK D Sig} {ev : ShareEvent Share Sig}
    {res : Option (CustodyLedger PK D Sig × CustodyOutcome Sig)}
    (h : res.map (fun r => ({ c with ledger := r.1 }, ShareEvent.custody r.2)) = some (c', ev)) :
    c'.buffer = c.buffer := by
  cases res with
  | none => cases h
  | some pair =>
    dsimp only [Option.map] at h
    injection h with hPair
    injection hPair with hSt _
    rw [← hSt]

private theorem shareOpeningStep_execute_buffer {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq D]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    {c c' : ShareState Share Contrib PK D Sig}
    {d : Nat} {approvers : List Nat} {i : CustodyIntent} {ab : Bool}
    {ev : ShareEvent Share Sig}
    (h : shareOpeningStep dep c (.execute d approvers i ab) = some (c', ev)) :
    c'.buffer = c.buffer := by
  unfold shareOpeningStep at h
  dsimp only at h
  cases hF : findReleasedEpoch c.ledger.releasedHistory i.epoch with
  | some _ =>
    rw [hF] at h
    exact option_map_ledger_buffer h
  | none =>
    rw [hF] at h
    dsimp only at h
    cases ab with
    | true =>
      rw [sh_if_pos rfl] at h
      exact option_map_ledger_buffer h
    | false =>
      rw [sh_if_neg Bool.false_ne_true] at h
      by_cases hR :
          (decide (dep.quorum.threshold ≤ approvers.length) &&
            decide approvers.Nodup &&
            approvers.all (fun p =>
              decide (p < dep.quorum.numParties) &&
              (c.buffer.find? (fun m =>
                decide (m.sender = p) && decide (m.deploymentId = dep.deploymentId) &&
                decide (m.intent = i) &&
                decide (dep.commit (dep.preimageOf p dep.deploymentId i m.contrib) =
                  dep.commitmentOf p dep.deploymentId i))).isSome)) = true
      · rw [sh_if_pos hR] at h
        cases hAss : dep.assembleSig _ i.epoch (dep.digests.digest dep.deploymentId i) with
        | none => rw [hAss] at h; cases h
        | some sig =>
          rw [hAss] at h
          by_cases hV : dep.sigScheme.verify c.ledger.enrolledPk
              (dep.encodeDigest (dep.digests.digest dep.deploymentId i)) sig = true
          · rw [sh_if_pos hV] at h
            exact option_map_ledger_buffer h
          · rw [sh_if_neg hV] at h; cases h
      · rw [sh_if_neg hR] at h; cases h

private theorem shareStep_sim_or_collision {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq Contrib] [DecidableEq D]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (hWf : dep.WellFormed)
    {c c' : ShareState Share Contrib PK D Sig}
    {a : IdealCustodyState PK D Sig}
    {turn : ShareTurn Contrib} {ev : ShareEvent Share Sig}
    (hRel : ShareRel dep c a)
    (hStep : shareOpeningStep dep c turn = some (c', ev)) :
    (match shareVisIn dep turn with
     | some j =>
       ∃ a' : IdealCustodyState PK D Sig,
         idealCustodyStep dep.digests dep.idealOracle a j = some (a', shareVisOut ev) ∧
         ShareRel dep c' a'
     | none => ShareRel dep c' a) ∨
    (∃ m ∈ c.buffer, ∃ p < dep.quorum.numParties,
      m.sender = p ∧ m.deploymentId = dep.deploymentId ∧
      dep.preimageOf p dep.deploymentId m.intent m.contrib ≠
        dep.preimageOf p dep.deploymentId m.intent (dep.trueContrib p m.intent) ∧
      dep.commit (dep.preimageOf p dep.deploymentId m.intent m.contrib) =
        dep.commit (dep.preimageOf p dep.deploymentId m.intent (dep.trueContrib p m.intent))) := by
  have hNum : a.ledger.quorum.numParties = dep.quorum.numParties := by
    rw [hRel.ledger, hRel.inv.profile]
  have hThr : a.ledger.quorum.threshold = dep.quorum.threshold := by
    rw [hRel.ledger, hRel.inv.profile]
  have hDep : a.ledger.deploymentId = dep.deploymentId := by
    rw [hRel.ledger, hRel.inv.deployment]
  cases turn with
  | approve p d i =>
    left
    dsimp only [shareVisIn]
    unfold shareOpeningStep at hStep
    dsimp only at hStep
    by_cases hg : p < dep.quorum.numParties ∧ p ∉ c.corrupt ∧ d = dep.deploymentId ∧
        (c.nodes p).latch ≤ i.epoch ∧ i.sessionId ∉ (c.nodes p).coupons
    · rw [sh_if_pos hg] at hStep
      cases hStep
      obtain ⟨hLt, hHon, hD, hLatch, _⟩ := hg
      refine ⟨_, idealCustodyStep_approve_of (S := dep.digests) (oracleSign := dep.idealOracle) i
        ⟨hNum ▸ hLt, hRel.corrupt ▸ hHon, hD.trans hDep.symm⟩,
        { inv :=
            { deployment := hRel.inv.deployment
              enrolled := hRel.inv.enrolled
              profile := hRel.inv.profile
              shares := fun q => by
                dsimp only
                by_cases hqp : q = p
                · subst hqp; rw [sh_if_pos rfl]; exact hRel.inv.shares q
                · rw [sh_if_neg hqp]; exact hRel.inv.shares q
              latchBound := fun q e he => by
                dsimp only at he ⊢
                by_cases hqp : q = p
                · subst hqp
                  rw [sh_if_pos rfl] at he ⊢
                  rcases List.mem_cons.mp he with rfl | hOld
                  · exact Nat.lt_succ_self _
                  · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hRel.inv.latchBound q e hOld) hLatch)
                · rw [sh_if_neg hqp] at he ⊢
                  exact hRel.inv.latchBound q e he
              latchNodup := fun q => by
                dsimp only
                by_cases hqp : q = p
                · subst hqp
                  rw [sh_if_pos rfl, List.map_cons, List.nodup_cons]
                  refine ⟨?_, hRel.inv.latchNodup q⟩
                  intro hMem
                  obtain ⟨e, he, hEq⟩ := List.mem_map.mp hMem
                  have hLtE := hRel.inv.latchBound q e he
                  rw [hEq] at hLtE
                  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hLtE hLatch)
                · rw [sh_if_neg hqp]
                  exact hRel.inv.latchNodup q
              walVerified := hRel.inv.walVerified }
          ledger := hRel.ledger
          corrupt := hRel.corrupt
          latched := fun q => by
            dsimp only
            by_cases hqp : q = p
            · subst hqp
              rw [sh_if_pos rfl, custodyRevealed_cons_self]
              exact congrArg _ (hRel.latched q)
            · rw [sh_if_neg hqp, custodyRevealed_cons_ne _ _ _ (fun h => hqp h.symm)]
              exact hRel.latched q
          buffered := fun m hm hmD => by
            rcases List.mem_cons.mp hm with rfl | hOld
            · exact .inl List.mem_cons_self
            · exact (hRel.buffered m hOld hmD).imp (List.mem_cons_of_mem _) id }⟩
    · rw [sh_if_neg hg] at hStep; cases hStep
  | inject m =>
    left
    unfold shareOpeningStep at hStep
    dsimp only at hStep
    by_cases hg : m.sender ∈ c.corrupt
    · rw [sh_if_pos hg] at hStep
      cases hStep
      dsimp only [shareVisIn]
      by_cases hmD : m.deploymentId = dep.deploymentId
      · rw [sh_if_pos hmD]
        refine ⟨_, idealCustodyStep_advApprove_of (S := dep.digests) (oracleSign := dep.idealOracle)
          m.intent ⟨hRel.corrupt ▸ hg, hmD.trans hDep.symm⟩,
          { inv :=
              { deployment := hRel.inv.deployment
                enrolled := hRel.inv.enrolled
                profile := hRel.inv.profile
                shares := hRel.inv.shares
                latchBound := hRel.inv.latchBound
                latchNodup := hRel.inv.latchNodup
                walVerified := hRel.inv.walVerified }
            ledger := hRel.ledger
            corrupt := hRel.corrupt
            latched := hRel.latched
            buffered := fun m' hm' hm'D => by
              rcases List.mem_cons.mp hm' with rfl | hOld
              · exact .inr List.mem_cons_self
              · exact (hRel.buffered m' hOld hm'D).imp id (List.mem_cons_of_mem _) }⟩
      · rw [sh_if_neg hmD]
        exact
          { inv :=
              { deployment := hRel.inv.deployment
                enrolled := hRel.inv.enrolled
                profile := hRel.inv.profile
                shares := hRel.inv.shares
                latchBound := hRel.inv.latchBound
                latchNodup := hRel.inv.latchNodup
                walVerified := hRel.inv.walVerified }
            ledger := hRel.ledger
            corrupt := hRel.corrupt
            latched := hRel.latched
            buffered := fun m' hm' hm'D => by
              rcases List.mem_cons.mp hm' with rfl | hOld
              · exact absurd hm'D hmD
              · exact hRel.buffered m' hOld hm'D }
    · rw [sh_if_neg hg] at hStep; cases hStep
  | corrupt p =>
    left
    dsimp only [shareVisIn]
    unfold shareOpeningStep at hStep
    dsimp only at hStep
    by_cases hg : p < dep.quorum.numParties ∧ p ∉ c.corrupt ∧
        c.corrupt.length + 1 < dep.quorum.threshold
    · rw [sh_if_pos hg] at hStep
      cases hStep
      have hStepA := idealCustodyStep_corrupt_of (S := dep.digests) (oracleSign := dep.idealOracle)
        (st := a) (p := p) ⟨hNum ▸ hg.1, hRel.corrupt ▸ hg.2.1, by
          rw [hRel.corrupt, hThr]; exact hg.2.2⟩
      refine ⟨{ a with corruptParties := p :: a.corruptParties }, ?_,
        { inv :=
            { deployment := hRel.inv.deployment
              enrolled := hRel.inv.enrolled
              profile := hRel.inv.profile
              shares := hRel.inv.shares
              latchBound := hRel.inv.latchBound
              latchNodup := hRel.inv.latchNodup
              walVerified := hRel.inv.walVerified }
          ledger := hRel.ledger
          corrupt := congrArg (List.cons p) hRel.corrupt
          latched := hRel.latched
          buffered := hRel.buffered }⟩
      rw [hStepA]
      show some (_, CustodyOutcome.corrupted (custodyRevealed a.honestApprovals p)) =
        some (_, CustodyOutcome.corrupted (c.nodes p).latched)
      rw [hRel.latched p]
    · rw [sh_if_neg hg] at hStep; cases hStep
  | crash p =>
    left
    dsimp only [shareVisIn]
    unfold shareOpeningStep at hStep
    cases hStep
    exact
      { inv :=
          { deployment := hRel.inv.deployment
            enrolled := hRel.inv.enrolled
            profile := hRel.inv.profile
            shares := fun q => by
              dsimp only
              by_cases hqp : q = p
              · subst hqp; rw [sh_if_pos rfl]; exact hRel.inv.shares q
              · rw [sh_if_neg hqp]; exact hRel.inv.shares q
            latchBound := fun q e he => by
              dsimp only at he ⊢
              by_cases hqp : q = p
              · subst hqp; rw [sh_if_pos rfl] at he ⊢; exact hRel.inv.latchBound q e he
              · rw [sh_if_neg hqp] at he ⊢; exact hRel.inv.latchBound q e he
            latchNodup := fun q => by
              dsimp only
              by_cases hqp : q = p
              · subst hqp; rw [sh_if_pos rfl]; exact hRel.inv.latchNodup q
              · rw [sh_if_neg hqp]; exact hRel.inv.latchNodup q
            walVerified := hRel.inv.walVerified }
        ledger := hRel.ledger
        corrupt := hRel.corrupt
        latched := fun q => by
          dsimp only
          by_cases hqp : q = p
          · subst hqp; rw [sh_if_pos rfl]; exact hRel.latched q
          · rw [sh_if_neg hqp]; exact hRel.latched q
        buffered := hRel.buffered }
  | dropMsg idx =>
    left
    dsimp only [shareVisIn]
    unfold shareOpeningStep at hStep
    cases hStep
    exact
      { inv :=
          { deployment := hRel.inv.deployment
            enrolled := hRel.inv.enrolled
            profile := hRel.inv.profile
            shares := hRel.inv.shares
            latchBound := hRel.inv.latchBound
            latchNodup := hRel.inv.latchNodup
            walVerified := hRel.inv.walVerified }
        ledger := hRel.ledger
        corrupt := hRel.corrupt
        latched := hRel.latched
        buffered := fun m hm hmD => by
          rcases List.mem_append.mp hm with hT | hDr
          · exact hRel.buffered m (List.mem_of_mem_take hT) hmD
          · exact hRel.buffered m (List.mem_of_mem_drop hDr) hmD }
  | execute d approvers i ab =>
    dsimp only [shareVisIn]
    unfold shareOpeningStep at hStep
    dsimp only at hStep
    let matchMsg (p : Nat) (m : ShareApproval Contrib) : Bool :=
      decide (m.sender = p) && decide (m.deploymentId = dep.deploymentId) &&
      decide (m.intent = i) &&
      decide (dep.commit (dep.preimageOf p dep.deploymentId i m.contrib) =
        dep.commitmentOf p dep.deploymentId i)
    let ready : Bool :=
      decide (dep.quorum.threshold ≤ approvers.length) &&
      decide approvers.Nodup &&
      approvers.all (fun p =>
        decide (p < dep.quorum.numParties) && (c.buffer.find? (matchMsg p)).isSome)
    have hReadySpec : ready = true →
        dep.quorum.threshold ≤ approvers.length ∧ approvers.Nodup ∧
        ∀ p ∈ approvers, p < dep.quorum.numParties ∧
          ∃ m : ShareApproval Contrib, c.buffer.find? (matchMsg p) = some m ∧
            m ∈ c.buffer ∧ m.sender = p ∧ m.deploymentId = dep.deploymentId ∧ m.intent = i ∧
            dep.commit (dep.preimageOf p dep.deploymentId i m.contrib) =
              dep.commitmentOf p dep.deploymentId i := by
      intro hR
      dsimp only [ready] at hR
      rw [Bool.and_eq_true, Bool.and_eq_true] at hR
      refine ⟨of_decide_eq_true hR.1.1, of_decide_eq_true hR.1.2, ?_⟩
      intro p hp
      have hp' := List.all_eq_true.mp hR.2 p hp
      rw [Bool.and_eq_true] at hp'
      refine ⟨of_decide_eq_true hp'.1, ?_⟩
      cases hF : c.buffer.find? (matchMsg p) with
      | none => rw [hF] at hp'; cases hp'.2
      | some m =>
        have hM := List.find?_some hF
        dsimp only [matchMsg] at hM
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hM
        exact ⟨m, rfl, List.mem_of_find?_eq_some hF, of_decide_eq_true hM.1.1.1,
          of_decide_eq_true hM.1.1.2, of_decide_eq_true hM.1.2, of_decide_eq_true hM.2⟩
    have hReadyCount : (if ready then approvers.length else 0) ≤
        (custodyApprovers a.ledger.quorum.numParties a.honestApprovals a.corruptApprovals
          a.ledger.deploymentId i).length := by
      cases hR : ready with
      | false => rw [sh_if_neg Bool.false_ne_true]; exact Nat.zero_le _
      | true =>
        rw [sh_if_pos rfl]
        obtain ⟨_, hNd, hAll⟩ := hReadySpec hR
        refine custodyApprovers_length_le_of_subset hNd (fun p hp => ?_)
        obtain ⟨hLt, m, _, hmBuf, hmS, hmD, hmI, _⟩ := hAll p hp
        have hB := hRel.buffered m hmBuf hmD
        rw [hmS, hmD, hmI] at hB
        rw [hDep]
        exact ⟨hNum ▸ hLt, hB⟩
    cases hFindEp : findReleasedEpoch c.ledger.releasedHistory i.epoch with
    | some rec =>
      left
      rw [hFindEp] at hStep
      dsimp only at hStep
      cases hL : custodyLedgerSign dep.digests (fun _ => dep.fallbackSig) c.ledger 0 d i ab with
      | none => rw [hL] at hStep; cases hStep
      | some pair =>
        rcases pair with ⟨L', o⟩
        rw [hL] at hStep
        cases hStep
        have hIrrel := custodyLedgerSign_replay_irrelevant
          (S := dep.digests) (dep := d) (ab := ab)
          (o := fun _ => dep.fallbackSig) (o' := dep.idealOracle)
          (n := 0) (m := (custodyApprovers a.ledger.quorum.numParties a.honestApprovals
            a.corruptApprovals a.ledger.deploymentId i).length) hFindEp
        rw [hIrrel, ← hRel.ledger] at hL
        obtain ⟨_, _, hCase⟩ := custodyLedgerSign_inv hL
        rcases hCase with ⟨_, _, _, hSame, _⟩ | ⟨hNone, _⟩
        · refine ⟨_, idealCustodyStep_sign_of (S := dep.digests) (oracleSign := dep.idealOracle) hL,
            { inv := by
                rw [hSame, hRel.ledger]
                exact hRel.inv
              ledger := rfl
              corrupt := hRel.corrupt
              latched := hRel.latched
              buffered := hRel.buffered }⟩
        · rw [hRel.ledger, hFindEp] at hNone; cases hNone
    | none =>
      rw [hFindEp] at hStep
      dsimp only at hStep
      cases hab : ab with
      | true =>
        left
        rw [hab, sh_if_pos rfl] at hStep
        change (custodyLedgerSign dep.digests (fun _ => dep.fallbackSig) c.ledger
            (if ready then approvers.length else 0) d i true).map
            (fun r => ({ c with ledger := r.1 }, .custody r.2)) = some (c', ev) at hStep
        cases hL : custodyLedgerSign dep.digests (fun _ => dep.fallbackSig) c.ledger
            (if ready then approvers.length else 0) d i true with
        | none => rw [hL] at hStep; cases hStep
        | some pair =>
          rcases pair with ⟨L', o⟩
          rw [hL] at hStep
          cases hStep
          obtain ⟨hPois, hDepEq, hCase⟩ := custodyLedgerSign_inv hL
          rcases hCase with ⟨_, hFound, _⟩ | ⟨_, hEp, hSess, hQ, hCap, hAbCase⟩
          · rw [hFindEp] at hFound; cases hFound
          · rcases hAbCase with ⟨_, hL', hOut⟩ | ⟨hFalse, _⟩
            · have hIdeal : custodyLedgerSign dep.digests dep.idealOracle c.ledger
                  (if ready then approvers.length else 0) d i true = some (L', o) := by
                unfold custodyLedgerSign
                rw [sh_if_pos ⟨hPois, hDepEq⟩, hFindEp]
                dsimp only
                rw [sh_if_pos ⟨hEp, hSess, hQ, hCap⟩, sh_if_pos rfl, hL', hOut]
              have hMono := custodyLedgerSign_mono hIdeal hReadyCount
              rw [← hRel.ledger] at hMono
              obtain ⟨hD', hPk', hQ'⟩ := custodyLedgerSign_static hL
              refine ⟨_, idealCustodyStep_sign_of (S := dep.digests) (oracleSign := dep.idealOracle) hMono,
                { inv :=
                    { deployment := hD'.trans hRel.inv.deployment
                      enrolled := hPk'.trans hRel.inv.enrolled
                      profile := hQ'.trans hRel.inv.profile
                      shares := hRel.inv.shares
                      latchBound := hRel.inv.latchBound
                      latchNodup := hRel.inv.latchNodup
                      walVerified := by rw [hL']; exact hRel.inv.walVerified }
                  ledger := rfl
                  corrupt := hRel.corrupt
                  latched := hRel.latched
                  buffered := hRel.buffered }⟩
            · cases hFalse
      | false =>
        rw [hab, sh_if_neg Bool.false_ne_true] at hStep
        change (if ready = true then
            let contribs := approvers.filterMap (fun p =>
              (c.buffer.find? (matchMsg p)).map (fun m => (p, m.contrib)))
            let dig := dep.digests.digest dep.deploymentId i
            match dep.assembleSig contribs i.epoch dig with
            | none => none
            | some sig =>
              if dep.sigScheme.verify c.ledger.enrolledPk (dep.encodeDigest dig) sig = true then
                (custodyLedgerSign dep.digests (fun _ => sig) c.ledger approvers.length d i false).map
                  (fun r => ({ c with ledger := r.1 }, .custody r.2))
              else none
          else none) = some (c', ev) at hStep
        cases hR : ready with
        | false => rw [hR, sh_if_neg Bool.false_ne_true] at hStep; cases hStep
        | true =>
          rw [hR, sh_if_pos rfl] at hStep
          dsimp only at hStep
          obtain ⟨hThrLen, hNd, hAll⟩ := hReadySpec hR
          cases hBad : approvers.find? (fun p =>
              match c.buffer.find? (matchMsg p) with
              | none => false
              | some m => decide (m.contrib ≠ dep.trueContrib p i)) with
          | some p =>
            right
            have hpMem : p ∈ approvers := List.mem_of_find?_eq_some hBad
            have hSome := List.find?_some (p := fun q =>
              match c.buffer.find? (matchMsg q) with
              | none => false
              | some m => decide (m.contrib ≠ dep.trueContrib q i)) hBad
            obtain ⟨hLt, m, hFindM, hmBuf, hmS, hmD, hmI, hComEq⟩ := hAll p hpMem
            rw [hFindM] at hSome
            have hmNe : m.contrib ≠ dep.trueContrib p i := of_decide_eq_true hSome
            rcases verifyContrib_dealt_or_collision dep hWf hLt hComEq with hEq | ⟨hPreNe, hCol⟩
            · exact absurd hEq hmNe
            · exact ⟨m, hmBuf, p, hLt, hmS, hmD, hmI ▸ hPreNe, hmI ▸ hCol⟩
          | none =>
            left
            have hContribsEq :
                approvers.filterMap (fun p =>
                  (c.buffer.find? (matchMsg p)).map (fun m => (p, m.contrib))) =
                approvers.map (fun p => (p, dep.trueContrib p i)) := by
              apply filterMap_all_some
              intro p hp
              obtain ⟨_, m, hFindM, _, _, _, _, _⟩ := hAll p hp
              have hFalse := List.find?_eq_none.mp hBad p hp
              rw [hFindM] at hFalse ⊢
              have hmEq : m.contrib = dep.trueContrib p i := by
                by_cases hE : m.contrib = dep.trueContrib p i
                · exact hE
                · exact absurd (decide_eq_true hE) hFalse
              dsimp only [Option.map]
              rw [hmEq]
            rw [hContribsEq] at hStep
            let dig := dep.digests.digest dep.deploymentId i
            have hAssem := hWf.assemble_dealt approvers i hNd (fun p hp => (hAll p hp).1) hThrLen
            cases hAss : dep.assembleSig (approvers.map (fun p => (p, dep.trueContrib p i))) i.epoch dig with
            | none => rw [hAss] at hStep; cases hStep
            | some sig =>
              rw [hAss] at hStep
              dsimp only at hStep
              have hSign : dep.sigScheme.sign dep.dealtSk i.epoch (dep.encodeDigest dig) = some sig :=
                hAssem.symm.trans hAss
              have hVer : dep.sigScheme.verify dep.pk (dep.encodeDigest dig) sig = true :=
                dep.sigScheme.correct dep.dealtSk i.epoch (dep.encodeDigest dig) sig hSign
              by_cases hVerL : dep.sigScheme.verify c.ledger.enrolledPk (dep.encodeDigest dig) sig = true
              · rw [sh_if_pos hVerL] at hStep
                cases hL : custodyLedgerSign dep.digests (fun _ => sig) c.ledger
                    approvers.length d i false with
                | none => rw [hL] at hStep; cases hStep
                | some pair =>
                  rcases pair with ⟨L', o⟩
                  rw [hL] at hStep
                  cases hStep
                  obtain ⟨hPois, hDepEq, hCase⟩ := custodyLedgerSign_inv hL
                  rcases hCase with ⟨_, hFound, _⟩ | ⟨_, hEp, hSess, hQ, hCap, hAbCase⟩
                  · rw [hFindEp] at hFound; cases hFound
                  · rcases hAbCase with ⟨hAbT, _⟩ | ⟨_, hL', hOut⟩
                    · cases hAbT
                    · have hOraEq : dep.idealOracle (dep.digests.digest c.ledger.deploymentId i) = sig := by
                        rw [hRel.inv.deployment]
                        show (dep.sigScheme.sign dep.dealtSk (dep.epochOfDigest dig) (dep.encodeDigest dig)).getD
                          dep.fallbackSig = sig
                        rw [hWf.epoch_digest i, hSign]
                        rfl
                      have hIdeal : custodyLedgerSign dep.digests dep.idealOracle c.ledger
                          (if ready then approvers.length else 0) d i false = some (L', o) := by
                        rw [hR, sh_if_pos rfl]
                        unfold custodyLedgerSign
                        rw [sh_if_pos ⟨hPois, hDepEq⟩, hFindEp]
                        dsimp only
                        rw [sh_if_pos ⟨hEp, hSess, hQ, hCap⟩, sh_if_neg Bool.false_ne_true,
                          hOraEq, hL', hOut]
                      have hMono := custodyLedgerSign_mono hIdeal hReadyCount
                      rw [← hRel.ledger] at hMono
                      obtain ⟨hD', hPk', hQ'⟩ := custodyLedgerSign_static hL
                      refine ⟨_, idealCustodyStep_sign_of (S := dep.digests) (oracleSign := dep.idealOracle) hMono,
                        { inv :=
                            { deployment := hD'.trans hRel.inv.deployment
                              enrolled := hPk'.trans hRel.inv.enrolled
                              profile := hQ'.trans hRel.inv.profile
                              shares := hRel.inv.shares
                              latchBound := hRel.inv.latchBound
                              latchNodup := hRel.inv.latchNodup
                              walVerified := fun r hr => by
                                rw [hL'] at hr
                                rcases List.mem_cons.mp hr with rfl | hOld
                                · dsimp only
                                  rw [hRel.inv.deployment]
                                  exact hVer
                                · exact hRel.inv.walVerified r hOld }
                          ledger := rfl
                          corrupt := hRel.corrupt
                          latched := hRel.latched
                          buffered := hRel.buffered }⟩
              · rw [sh_if_neg hVerL] at hStep; cases hStep

/-- **Finite-Set `InjOn` `Spec.DataRefines` Theorem (`distCustody_injOn_dataRefines_ideal`)**:
    Whenever `dep.commit` is collision-free on a finite observed preimage list `obs`
    (`InjOnPreimages dep.commit obs`, with ZERO global injectivity assumption!), the `obs`-guarded
    share-opening machine refines `Spec.idealCustodyMachine` via `Spec.DataRefines`. -/
def distCustody_injOn_dataRefines_ideal {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq Contrib] [DecidableEq Preimage] [DecidableEq D]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (hWf : dep.WellFormed) (obs : List Preimage)
    (hInj : InjOnPreimages dep.commit obs) :
    DataRefines (shareOpeningObservedMachine dep obs)
      (idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk dep.quorum)
      (shareVisIn dep) shareVisOut where
  Rel c a :=
    ShareRel dep c a ∧
    ∀ m ∈ c.buffer,
      dep.preimageOf m.sender m.deploymentId m.intent m.contrib ∈ obs ∧
      dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ∈ obs
  absInit _ := IdealCustodyState.init dep.deploymentId dep.pk dep.quorum
  init_ok {c₀} hInit := by
    have hc : c₀ = ShareState.init dep := hInit
    subst hc
    exact ⟨rfl, shareInit_rel dep, fun _ h => absurd h List.not_mem_nil⟩
  sim_visible {c c' a turn ev j} hRelPair hStepObs hVis := by
    obtain ⟨hRel, hObsBuf⟩ := hRelPair
    have hUnpack : shareOpeningStep dep c turn = some (c', ev) ∧
        ∀ m ∈ c'.buffer,
          dep.preimageOf m.sender m.deploymentId m.intent m.contrib ∈ obs ∧
          dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ∈ obs := by
      cases turn with
      | approve p d i =>
        change shareOpeningObservedStep dep obs c (.approve p d i) = some (c', ev) at hStepObs
        unfold shareOpeningObservedStep at hStepObs
        dsimp only at hStepObs
        by_cases hIn : dep.preimageOf p d i (dep.evalContrib p (c.nodes p).share d i) ∈ obs ∧
            dep.preimageOf p d i (dep.trueContrib p i) ∈ obs
        · rw [sh_if_pos hIn] at hStepObs
          refine ⟨hStepObs, ?_⟩
          unfold shareOpeningStep at hStepObs
          dsimp only at hStepObs
          by_cases hg : p < dep.quorum.numParties ∧ p ∉ c.corrupt ∧ d = dep.deploymentId ∧
              (c.nodes p).latch ≤ i.epoch ∧ i.sessionId ∉ (c.nodes p).coupons
          · rw [sh_if_pos hg] at hStepObs; cases hStepObs
            intro m hm
            rcases List.mem_cons.mp hm with rfl | hOld
            · exact hIn
            · exact hObsBuf m hOld
          · rw [sh_if_neg hg] at hStepObs; cases hStepObs
        · rw [sh_if_neg hIn] at hStepObs; cases hStepObs
      | inject m =>
        change shareOpeningObservedStep dep obs c (.inject m) = some (c', ev) at hStepObs
        unfold shareOpeningObservedStep at hStepObs
        dsimp only at hStepObs
        by_cases hIn : dep.preimageOf m.sender m.deploymentId m.intent m.contrib ∈ obs ∧
            dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ∈ obs
        · rw [sh_if_pos hIn] at hStepObs
          refine ⟨hStepObs, ?_⟩
          unfold shareOpeningStep at hStepObs
          dsimp only at hStepObs
          by_cases hg : m.sender ∈ c.corrupt
          · rw [sh_if_pos hg] at hStepObs; cases hStepObs
            intro m' hm'
            rcases List.mem_cons.mp hm' with rfl | hOld
            · exact hIn
            · exact hObsBuf m' hOld
          · rw [sh_if_neg hg] at hStepObs; cases hStepObs
        · rw [sh_if_neg hIn] at hStepObs; cases hStepObs
      | corrupt p =>
        change shareOpeningStep dep c (.corrupt p) = some (c', ev) at hStepObs
        refine ⟨hStepObs, ?_⟩
        unfold shareOpeningStep at hStepObs; dsimp only at hStepObs
        by_cases hg : p < dep.quorum.numParties ∧ p ∉ c.corrupt ∧
            c.corrupt.length + 1 < dep.quorum.threshold
        · rw [sh_if_pos hg] at hStepObs; cases hStepObs; exact hObsBuf
        · rw [sh_if_neg hg] at hStepObs; cases hStepObs
      | crash _ => cases hVis
      | dropMsg _ => cases hVis
      | execute d approvers i ab =>
        change shareOpeningStep dep c (.execute d approvers i ab) = some (c', ev) at hStepObs
        refine ⟨hStepObs, ?_⟩
        rw [shareOpeningStep_execute_buffer dep hStepObs]
        exact hObsBuf
    rcases shareStep_sim_or_collision dep hWf hRel hUnpack.1 with hSim | ⟨m, hmBuf, p, _, rfl, hmD, hNe, hCol⟩
    · rw [hVis] at hSim
      obtain ⟨a', hStepA, hRel'⟩ := hSim
      exact ⟨a', hStepA, hRel', hUnpack.2⟩
    · obtain ⟨h1, h2⟩ := hObsBuf m hmBuf
      rw [hmD] at h1 h2
      exact absurd (hInj _ h1 _ h2 hCol) hNe
  sim_internal {c c' a turn ev} hRelPair hStepObs hInt := by
    obtain ⟨hRel, hObsBuf⟩ := hRelPair
    have hUnpack : shareOpeningStep dep c turn = some (c', ev) ∧
        ∀ m ∈ c'.buffer,
          dep.preimageOf m.sender m.deploymentId m.intent m.contrib ∈ obs ∧
          dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ∈ obs := by
      cases turn with
      | approve _ _ _ => cases hInt
      | corrupt _ => cases hInt
      | execute _ _ _ _ => cases hInt
      | inject m =>
        change shareOpeningObservedStep dep obs c (.inject m) = some (c', ev) at hStepObs
        unfold shareOpeningObservedStep at hStepObs; dsimp only at hStepObs
        by_cases hIn : dep.preimageOf m.sender m.deploymentId m.intent m.contrib ∈ obs ∧
            dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ∈ obs
        · rw [sh_if_pos hIn] at hStepObs
          refine ⟨hStepObs, ?_⟩
          unfold shareOpeningStep at hStepObs; dsimp only at hStepObs
          by_cases hg : m.sender ∈ c.corrupt
          · rw [sh_if_pos hg] at hStepObs; cases hStepObs
            intro m' hm'
            rcases List.mem_cons.mp hm' with rfl | hOld
            · exact hIn
            · exact hObsBuf m' hOld
          · rw [sh_if_neg hg] at hStepObs; cases hStepObs
        · rw [sh_if_neg hIn] at hStepObs; cases hStepObs
      | crash p =>
        change shareOpeningStep dep c (.crash p) = some (c', ev) at hStepObs
        refine ⟨hStepObs, ?_⟩
        unfold shareOpeningStep at hStepObs; cases hStepObs; exact hObsBuf
      | dropMsg idx =>
        change shareOpeningStep dep c (.dropMsg idx) = some (c', ev) at hStepObs
        refine ⟨hStepObs, ?_⟩
        unfold shareOpeningStep at hStepObs; cases hStepObs
        intro m hm
        rcases List.mem_append.mp hm with hT | hDr
        · exact hObsBuf m (List.mem_of_mem_take hT)
        · exact hObsBuf m (List.mem_of_mem_drop hDr)
    rcases shareStep_sim_or_collision dep hWf hRel hUnpack.1 with hSim | ⟨m, hmBuf, p, _, rfl, hmD, hNe, hCol⟩
    · rw [hInt] at hSim
      exact ⟨hSim, hUnpack.2⟩
    · obtain ⟨h1, h2⟩ := hObsBuf m hmBuf
      rw [hmD] at h1 h2
      exact absurd (hInj _ h1 _ h2 hCol) hNe
  sim_reject hRelPair _ := hRelPair

private theorem shareTrace_lift_or_collision {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq Contrib] [DecidableEq D]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (hWf : dep.WellFormed) :
    ∀ {c₀ cFinal : ShareState Share Contrib PK D Sig}
      {a₀ : IdealCustodyState PK D Sig}
      {obsPrefix : List Preimage}
      {tr : List (ShareTurn Contrib × ShareEvent Share Sig)},
      ShareRel dep c₀ a₀ →
      (∀ m ∈ c₀.buffer,
        dep.preimageOf m.sender m.deploymentId m.intent m.contrib ∈ obsPrefix ∧
        dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ∈ obsPrefix) →
      (shareOpeningMachine dep).ValidTrace c₀ tr cFinal →
      (∃ aFinal : IdealCustodyState PK D Sig,
        (idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk dep.quorum).ValidTrace
          a₀ (projectTrace (shareVisIn dep) shareVisOut tr) aFinal ∧
        ShareRel dep cFinal aFinal) ∨
      (∃ x₁ x₂ : Preimage,
        x₁ ≠ x₂ ∧ dep.commit x₁ = dep.commit x₂ ∧
        x₁ ∈ obsPrefix ++ observedSharePreimages dep tr ∧
        x₂ ∈ obsPrefix ++ observedSharePreimages dep tr)
  | _, _, a₀, _, _, hRel, _, .nil _ => .inl ⟨a₀, .nil a₀, hRel⟩
  | c, cFinal, a₀, obsPrefix, _, hRel, hBufObs, .reject _ _ hRest =>
    shareTrace_lift_or_collision dep hWf hRel hBufObs hRest
  | c, cFinal, a₀, obsPrefix, (turn, ev) :: rest, hRel, hBufObs, .accept hStep hRest => by
    have hStep' : shareOpeningStep dep c turn = some (_, ev) := hStep
    rcases shareStep_sim_or_collision dep hWf hRel hStep' with hSim | ⟨m, hmBuf, p, _, rfl, hmD, hNe, hCol⟩
    · let stepObs : List Preimage :=
        match turn with
        | .approve p d i =>
          [dep.preimageOf p d i (dep.evalContrib p (dep.dealShare p) d i),
           dep.preimageOf p d i (dep.trueContrib p i)]
        | .inject m =>
          [dep.preimageOf m.sender m.deploymentId m.intent m.contrib,
           dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent)]
        | _ => []
      have hObsEq : obsPrefix ++ observedSharePreimages dep ((turn, ev) :: rest) =
          (obsPrefix ++ stepObs) ++ observedSharePreimages dep rest := by
        cases turn <;> simp [observedSharePreimages, stepObs, List.append_assoc]
      have hBufObsNext : ∀ {c₁}, shareOpeningStep dep c turn = some (c₁, ev) →
          ∀ m ∈ c₁.buffer,
            dep.preimageOf m.sender m.deploymentId m.intent m.contrib ∈ obsPrefix ++ stepObs ∧
            dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ∈ obsPrefix ++ stepObs := by
        intro c₁ hS m' hm'
        cases turn with
        | approve p d i =>
          unfold shareOpeningStep at hS; dsimp only at hS
          by_cases hg : p < dep.quorum.numParties ∧ p ∉ c.corrupt ∧ d = dep.deploymentId ∧
              (c.nodes p).latch ≤ i.epoch ∧ i.sessionId ∉ (c.nodes p).coupons
          · rw [sh_if_pos hg] at hS; cases hS
            rcases List.mem_cons.mp hm' with rfl | hOld
            · dsimp only [stepObs]
              rw [hRel.inv.shares p]
              exact ⟨List.mem_append_right _ List.mem_cons_self,
                List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
            · exact (hBufObs m' hOld).imp (List.mem_append_left _) (List.mem_append_left _)
          · rw [sh_if_neg hg] at hS; cases hS
        | inject m =>
          unfold shareOpeningStep at hS; dsimp only at hS
          by_cases hg : m.sender ∈ c.corrupt
          · rw [sh_if_pos hg] at hS; cases hS
            rcases List.mem_cons.mp hm' with rfl | hOld
            · exact ⟨List.mem_append_right _ List.mem_cons_self,
                List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
            · exact (hBufObs m' hOld).imp (List.mem_append_left _) (List.mem_append_left _)
          · rw [sh_if_neg hg] at hS; cases hS
        | corrupt p =>
          unfold shareOpeningStep at hS; dsimp only at hS
          by_cases hg : p < dep.quorum.numParties ∧ p ∉ c.corrupt ∧
              c.corrupt.length + 1 < dep.quorum.threshold
          · rw [sh_if_pos hg] at hS; cases hS
            exact (hBufObs m' hm').imp (List.mem_append_left _) (List.mem_append_left _)
          · rw [sh_if_neg hg] at hS; cases hS
        | crash p =>
          unfold shareOpeningStep at hS; cases hS
          exact (hBufObs m' hm').imp (List.mem_append_left _) (List.mem_append_left _)
        | dropMsg idx =>
          unfold shareOpeningStep at hS; cases hS
          rcases List.mem_append.mp hm' with hT | hDr
          · exact (hBufObs m' (List.mem_of_mem_take hT)).imp (List.mem_append_left _) (List.mem_append_left _)
          · exact (hBufObs m' (List.mem_of_mem_drop hDr)).imp (List.mem_append_left _) (List.mem_append_left _)
        | execute d approvers i ab =>
          rw [shareOpeningStep_execute_buffer dep hS] at hm'
          exact (hBufObs m' hm').imp (List.mem_append_left _) (List.mem_append_left _)
      cases hVis : shareVisIn dep turn with
      | some j =>
        rw [hVis] at hSim
        obtain ⟨a₁, hStepA, hRel₁⟩ := hSim
        rcases shareTrace_lift_or_collision dep hWf hRel₁ (hBufObsNext hStep') hRest with
          ⟨aFinal, hTrA, hRelF⟩ | ⟨x₁, x₂, hNe, hCol, hx₁, hx₂⟩
        · refine .inl ⟨aFinal, ?_, hRelF⟩
          simp only [projectTrace, hVis]
          exact .accept hStepA hTrA
        · rw [← hObsEq] at hx₁ hx₂
          exact .inr ⟨x₁, x₂, hNe, hCol, hx₁, hx₂⟩
      | none =>
        rw [hVis] at hSim
        rcases shareTrace_lift_or_collision dep hWf hSim (hBufObsNext hStep') hRest with
          ⟨aFinal, hTrA, hRelF⟩ | ⟨x₁, x₂, hNe, hCol, hx₁, hx₂⟩
        · refine .inl ⟨aFinal, ?_, hRelF⟩
          simp only [projectTrace, hVis]
          exact hTrA
        · rw [← hObsEq] at hx₁ hx₂
          exact .inr ⟨x₁, x₂, hNe, hCol, hx₁, hx₂⟩
    · obtain ⟨h1, h2⟩ := hBufObs m hmBuf
      rw [hmD] at h1 h2
      exact .inr ⟨_, _, hNe, hCol, List.mem_append_left _ h1, List.mem_append_left _ h2⟩

/-- **Unconditional Collision-Branching Refinement Theorem (`distCustody_dataRefines_or_collision`)**:
    For ANY compressing commitment hash `commit : Preimage → BitVec 256` with **zero injectivity
    assumptions**, every multi-turn execution of `shareOpeningMachine dep` from `ShareState.init dep`
    EITHER:
    1. Projects to an admitted `Spec.idealCustodyMachine` trace where every WAL/released signature
       passes `dep.sigScheme.verify dep.pk (dep.encodeDigest r.digest) r.sig = true`, fewer than
       `threshold` parties are corrupted, cumulative spend stays within `spendCap`, and every WAL
       record was approved in the durable latch of an enrolled custodian, OR
    2. Yields an explicit colliding preimage pair `x₁ ≠ x₂` observed in the transcript with
       `dep.commit x₁ = dep.commit x₂`! -/
theorem distCustody_dataRefines_or_collision {Share Contrib Preimage PK SK D Sig : Type}
    [DecidableEq Contrib] [DecidableEq D]
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (hWf : dep.WellFormed)
    {stFinal : ShareState Share Contrib PK D Sig}
    {tr : List (ShareTurn Contrib × ShareEvent Share Sig)}
    (hTr : (shareOpeningMachine dep).ValidTrace (ShareState.init dep) tr stFinal) :
    ((idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk
        dep.quorum).AdmitsTrace (projectTrace (shareVisIn dep) shareVisOut tr) ∧
      stFinal.corrupt.length < dep.quorum.threshold ∧
      stFinal.ledger.spent ≤ dep.quorum.spendCap ∧
      (∀ r : CustodyRelease D Sig, r ∈ stFinal.ledger.releasedHistory →
        dep.sigScheme.verify dep.pk (dep.encodeDigest r.digest) r.sig = true ∧
        r.sig = dep.idealOracle (dep.digests.digest dep.deploymentId r.intent) ∧
        ∃ p : Nat, p < dep.quorum.numParties ∧ r.intent ∈ (stFinal.nodes p).latched ∧
          r.intent.epoch < (stFinal.nodes p).latch)) ∨
    (∃ x₁ x₂ : Preimage,
      x₁ ≠ x₂ ∧ dep.commit x₁ = dep.commit x₂ ∧
      x₁ ∈ observedSharePreimages dep tr ∧
      x₂ ∈ observedSharePreimages dep tr) := by
  rcases shareTrace_lift_or_collision dep hWf (obsPrefix := []) (shareInit_rel dep)
      (fun _ h => absurd h List.not_mem_nil) hTr with
    ⟨aFinal, hTrA, hRelF⟩ | ⟨x₁, x₂, hNe, hCol, hx₁, hx₂⟩
  · left
    have hReachA : (idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk
        dep.quorum).Reachable aFinal := ⟨_, _, rfl, hTrA⟩
    have hSafe := idealCustody_reachable_safeInv hReachA
    refine ⟨⟨_, aFinal, rfl, hTrA⟩, hRelF.corrupt ▸ hSafe.corruptBudget,
      hRelF.ledger ▸ hSafe.budget, ?_⟩
    intro r hr
    obtain ⟨hSig, p, hLt, hMem⟩ :=
      idealCustody_reachable_release_honestly_approved hReachA (hRelF.ledger ▸ hr)
    have hLat : r.intent ∈ (stFinal.nodes p).latched := by
      rw [hRelF.latched p]
      unfold custodyRevealed
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hMem, decide_eq_true rfl⟩, rfl⟩
    exact ⟨hRelF.inv.walVerified r hr, hSig, p, hLt, hLat, hRelF.inv.latchBound p _ hLat⟩
  · right
    rw [List.nil_append] at hx₁ hx₂
    exact ⟨x₁, x₂, hNe, hCol, hx₁, hx₂⟩

end UnconditionalAndShareOpening

#verify_constructive
  Qsag.DistCustody.Deployment.WellFormed.point_inj
  Qsag.DistCustody.verifyShare_dealt_or_collision
  Qsag.DistCustody.verifyShare_sound
  Qsag.DistCustody.reconstruct_dealt_shares
  Qsag.DistCustody.quorumKey_eq_secret
  Qsag.DistCustody.quorumKey_eq_secret_or_collision
  Qsag.DistCustody.corrupt_shares_independent_of_secret
  Qsag.DistCustody.init_inv
  Qsag.DistCustody.executeStep_ledger_ideal
  Qsag.DistCustody.step_sim_visible
  Qsag.DistCustody.step_sim_internal
  Qsag.DistCustody.distCustody_trace_inclusion
  Qsag.DistCustody.distCustody_reachable_safe
  Qsag.DistCustody.distCustody_latch_unique
  Qsag.DistCustody.latched_epoch_rejected_after_crash
  Qsag.DistCustody.execute_ready_fresh_releases
  Qsag.DistCustody.verifyContrib_dealt_or_collision
  Qsag.DistCustody.distCustody_dataRefines_or_collision

end Qsag.DistCustody
end
