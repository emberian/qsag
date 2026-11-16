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

