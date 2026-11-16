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
public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
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

abbrev setNode (nodes : Nat → Custodian F) (p : Nat) (c : Custodian F) :
    Nat → Custodian F :=
  fun q => if q = p then c else nodes q

/-- `m` is a verified approval of `i` by `p` for this deployment. -/
abbrev supports (dep : Deployment F C PK D Sig) (i : CustodyIntent) (p : Nat)
    (m : Approval F) : Bool :=
  decide (m.sender = p) && decide (m.deploymentId = dep.deploymentId) &&
    decide (m.intent = i) && dep.verifyShare p m.share

/-- The first verified share from `p` for `i` in the buffer. -/
abbrev approvalShare (dep : Deployment F C PK D Sig) (buffer : List (Approval F))
    (i : CustodyIntent) (p : Nat) : Option F :=
  (buffer.find? (supports dep i p)).map (fun m => m.share)

/-- The coordinator's quorum check: enough distinct enrolled approvers, each with a verified
    buffered approval of exactly this intent for this deployment. -/
abbrev quorumReady (dep : Deployment F C PK D Sig) (buffer : List (Approval F))
    (approvers : List Nat) (i : CustodyIntent) : Bool :=
  decide (dep.quorum.threshold ≤ approvers.length) &&
  decide approvers.Nodup &&
  approvers.all (fun p =>
    decide (p < dep.quorum.numParties) && (approvalShare dep buffer i p).isSome)

/-- Lagrange reconstruction at zero from distinct evaluation points and shares (zero on duplicate points). -/
@[expose] def reconstruct (pts shares : List F) : F :=
  if pts.Nodup then
    ringListSum (List.zipWith (fun x s => lagrangeToAdditiveShare pts x s) pts shares)
  else
    CommRingOps.zero

/-- The key the coordinator reconstructs for `i` from the buffered shares of `approvers`. -/
abbrev quorumKey (dep : Deployment F C PK D Sig) (buffer : List (Approval F))
    (approvers : List Nat) (i : CustodyIntent) : F :=
  reconstruct (approvers.map dep.point)
    (approvers.map (fun p => (approvalShare dep buffer i p).getD CommRingOps.zero))

/-- Coordinator transition: the ledger's signing transition, signing with the reconstructed key
    and counting the named approvers only when the quorum check passes. A WAL replay needs no
    quorum, exactly as in the ledger. -/
abbrev executeStep (dep : Deployment F C PK D Sig) (st : State F PK D Sig)
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
  rw [dc_if_pos hPtsNd]
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
    rw [dc_if_pos hPtsNd, hShares, zipWith_map_map]
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
abbrev ShareOpeningDeployment.pk {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) : PK :=
  dep.sigScheme.derivePk dep.dealtSk

/-- Dealt per-request share contribution of custodian `p` for intent `i`. -/
abbrev ShareOpeningDeployment.trueContrib {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (p : Nat) (i : CustodyIntent) : Contrib :=
  dep.evalContrib p (dep.dealShare p) dep.deploymentId i

/-- Ideal signing oracle induced by `sigScheme.sign dealtSk`. -/
abbrev ShareOpeningDeployment.idealOracle {Share Contrib Preimage PK SK D Sig : Type}
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
abbrev shareOpeningMachine {Share Contrib Preimage PK SK D Sig : Type} [DecidableEq D]
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

theorem observedSharePreimages_nil {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig) :
    observedSharePreimages dep ([] : List (ShareTurn Contrib × ShareEvent Share Sig)) = [] := by
  rfl

theorem observedSharePreimages_cons {Share Contrib Preimage PK SK D Sig : Type}
    (dep : ShareOpeningDeployment Share Contrib Preimage PK SK D Sig)
    (turn : ShareTurn Contrib) (ev : ShareEvent Share Sig)
    (rest : List (ShareTurn Contrib × ShareEvent Share Sig)) :
    observedSharePreimages dep ((turn, ev) :: rest) =
      match turn with
      | .approve p d i =>
        dep.preimageOf p d i (dep.evalContrib p (dep.dealShare p) d i) ::
        dep.preimageOf p d i (dep.trueContrib p i) ::
        observedSharePreimages dep rest
      | .inject m =>
        dep.preimageOf m.sender m.deploymentId m.intent m.contrib ::
        dep.preimageOf m.sender m.deploymentId m.intent (dep.trueContrib m.sender m.intent) ::
        observedSharePreimages dep rest
      | _ => observedSharePreimages dep rest := by
  cases turn <;> rfl

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
          dsimp only at h
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

/-! ## 9. Authenticated custodian network: `Fin n` parties, MAC'd acknowledgements, sealed WAL

Section 1's `distMachine` gives the adversary an authenticated channel for free: `inject` is only
accepted for a sender that is already corrupted. The machine of this section removes that
assumption and adds the durable state the Rust custodians keep.

* The custodians are a `Fin n`-indexed family of `AuthParty` records (`n = quorum.numParties`).
  Besides share, latch, approval log and volatile coupons, a party holds its WAL record on disk as
  raw bytes in the `FsBeltWal` format of `Qsag.sealBeltWalRecord` (72-byte header
  `generation || reservation || nonce`, state bytes, MAC under `"QSAG.BELT.LATCH.WAL.MAC/v3"`),
  the ticket it was sealed under, and an `anchor`: the tag of the last committed record, kept
  outside the disk (`LedgerCheckpoint.tag`).
* An acknowledgement on the wire carries `Qsag.custodianAckTag` (`"QSAG.BELT.ACK.v1"`) under the
  sender's key over the coordinator's guard-key commitment, the epoch, a message tag of
  `(deploymentId, intent)` and the sender's id. The coordinator counts an approver only if the
  wire holds an acknowledgement from it with a valid tag and a share that opens its commitment.
* The adversary may put any message on the wire at any time (`inject` in the name of a corrupted
  custodian, `deliver` in the name of an uncorrupted one), drop any message, corrupt custodians
  adaptively below the threshold, overwrite any custodian's disk record with arbitrary bytes
  (`tamperDisk`) and crash any custodian. A crashed custodian recovers its latch and log from the
  disk record through `unsealBeltWalRecord`, the anchor comparison and `parseState`; if recovery
  fails it is poisoned and approves nothing further.

Two events separate this machine from the ideal functionality, and `authViolation` decides them:

* `deliver m` where `m` carries a valid tag in the name of an uncorrupted enrolled custodian for
  this deployment and an intent that custodian has not approved. `deliver_violation_classified`
  shows such an `m` is a tag on a preimage the custodian never tagged, or two intents share a
  message tag.
* `crash p` where the disk record passes recovery with a latch or log other than the custodian's
  own. `crash_violation_collision` shows this exhibits a collision of the hash.

`authGuardedMachine` is `authMachine` with these two turns refused. `authCustody_refines_ideal` is
a `Spec.DataRefines` witness from the guarded machine into `Spec.idealCustodyMachine`;
`authMachine_trace_guarded_or_violation` shows the two machines run identically up to the first
violation; `authCustody_ideal_or_forgery` combines them for `authMachine` itself.

Assumed, in `AuthDeployment.WellFormed`: the Shamir deployment conditions of Section 1 (including
injectivity of the share commitment), and `parseState (stateBytes l L) = some (l, L)` for the
state codec, which stands for `BeltLatchState::to_bytes` / `from_bytes`. Nothing is assumed about
the hash; no probability is assigned to the violation events here. Not modelled: the coordinator
is a single trusted ledger as in Section 1, the anchor is not adversarially writable, keys are
static, and the generation counter is a `UInt64` that wraps (a wrapped record has generation 0 and
is refused at recovery). The refinement is one-directional, as in Section 1. -/

section Authenticated

variable {F C PK D Sig : Type} [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]

/-- Deployment of the authenticated network: the Shamir deployment, the hash, the per-custodian
    acknowledgement and WAL keys, the coordinator's guard-key commitment, the message tag of
    `(deploymentId, intent)`, the anchor's tickets and the state codec. -/
structure AuthDeployment (F C PK D Sig : Type) where
  core : Deployment F C PK D Sig
  hash : List UInt8 → Digest256
  ackKey : Nat → Digest256
  guardKeyCommit : Digest256
  msgTag : Nat → CustodyIntent → Digest256
  walKey : Nat → Digest256
  lockSeal : Nat → List UInt8
  ticket : Nat → UInt64 → Digest256 × Digest256
  stateBytes : Nat → List CustodyIntent → List UInt8
  parseState : List UInt8 → Option (Nat × List CustodyIntent)

/-- Deployment conditions: those of the Shamir deployment, and the state codec round trip. -/
structure AuthDeployment.WellFormed (dep : AuthDeployment F C PK D Sig) : Prop where
  core : dep.core.WellFormed
  parse_stateBytes : ∀ (l : Nat) (L : List CustodyIntent),
    dep.parseState (dep.stateBytes l L) = some (l, L)

/-- An acknowledgement on the wire. -/
structure AuthAck (F : Type) where
  sender : Nat
  deploymentId : Nat
  intent : CustodyIntent
  share : F
  mac : Digest256

/-- One custodian. `coupons` is volatile; `disk` is adversarially writable; `anchor` is not. -/
structure AuthParty (F : Type) where
  share : F
  latch : Nat
  latched : List CustodyIntent
  coupons : List Nat
  poisoned : Bool
  ticket : BeltWalTicketSeal
  disk : List UInt8
  anchor : Digest256

/-- Custodians, wire, corruption set and the coordinator's ledger. -/
structure AuthState (F PK D Sig : Type) (n : Nat) where
  parties : Fin n → AuthParty F
  wire : List (AuthAck F)
  corrupt : List Nat
  ledger : CustodyLedger PK D Sig

/-- Schedule alphabet. `inject` and `deliver` together let the adversary place any message on the
    wire; the constructor records whether the named sender is corrupted at that moment. -/
inductive AuthTurn (F : Type) (n : Nat) where
  | approve (p : Fin n) (deploymentId : Nat) (intent : CustodyIntent)
  | inject (m : AuthAck F)
  | deliver (m : AuthAck F)
  | corrupt (p : Fin n)
  | crash (p : Fin n)
  | tamperDisk (p : Fin n) (raw : List UInt8)
  | dropMsg (idx : Nat)
  | execute (deploymentId : Nat) (approvers : List Nat) (intent : CustodyIntent)
      (abortBeforeRelease : Bool)

/-- Outputs. -/
inductive AuthEvent (F Sig : Type) where
  | approved (ack : AuthAck F)
  | injected
  | delivered
  | corrupted (share : F) (latched : List CustodyIntent)
  | recovered (restored : Bool)
  | tampered
  | dropped
  | custody (out : CustodyOutcome Sig)

/-- The `SHAKE256` preimage of custodian `p`'s acknowledgement of `(d, i)`. -/
def AuthDeployment.ackFrame (dep : AuthDeployment F C PK D Sig) (p d : Nat)
    (i : CustodyIntent) : List UInt8 :=
  custodianAckFrame (dep.ackKey p) dep.guardKeyCommit (UInt64.ofNat i.epoch) (dep.msgTag d i)
    (UInt8.ofNat p)

/-- Custodian `p`'s acknowledgement tag on `(d, i)`: `custodianAckTag` of the frame fields. -/
def AuthDeployment.ackMac (dep : AuthDeployment F C PK D Sig) (p d : Nat)
    (i : CustodyIntent) : Digest256 :=
  custodianAckTag dep.hash (dep.ackKey p) dep.guardKeyCommit (UInt64.ofNat i.epoch)
    (dep.msgTag d i) (UInt8.ofNat p)

/-- The coordinator's check on a wire message: an enrolled sender and a correct tag. -/
def AuthDeployment.ackValid (dep : AuthDeployment F C PK D Sig) (m : AuthAck F) : Bool :=
  decide (m.sender < dep.core.quorum.numParties) &&
    decide (m.mac = dep.ackMac m.sender m.deploymentId m.intent)

/-- The approval an acknowledgement carries. -/
def AuthAck.toApproval (m : AuthAck F) : Approval F :=
  { sender := m.sender, deploymentId := m.deploymentId, intent := m.intent, share := m.share }

/-- The approvals the coordinator reads off the wire: those with a valid tag. -/
def AuthDeployment.verified (dep : AuthDeployment F C PK D Sig) (wire : List (AuthAck F)) :
    List (Approval F) :=
  (wire.filter dep.ackValid).map AuthAck.toApproval

/-- The WAL record MAC of custodian `p`. -/
def AuthDeployment.sealTag (dep : AuthDeployment F C PK D Sig) (p : Nat)
    (tkt : BeltWalTicketSeal) (bytes : List UInt8) : Digest256 :=
  computeBeltWalSealTag dep.hash (dep.walKey p) (dep.lockSeal p) tkt bytes

/-- The ticket of the next record: the successor generation with the anchor's reservation and
    nonce for it. -/
def AuthDeployment.nextTicket (dep : AuthDeployment F C PK D Sig) (p : Nat)
    (tkt : BeltWalTicketSeal) : BeltWalTicketSeal :=
  { generation := tkt.generation + 1
    reservation := (dep.ticket p (tkt.generation + 1)).1
    nonce := (dep.ticket p (tkt.generation + 1)).2 }

/-- Genesis ticket: generation 1, no anchor reservation (`FsBeltWal::provision_genesis`). -/
def genesisTicket : BeltWalTicketSeal :=
  { generation := 1, reservation := 0#256, nonce := 0#256 }

/-- Recovery of custodian `p` from its disk record: `unsealBeltWalRecord`, comparison of the
    record's MAC with the anchor, and the state parse. -/
def AuthDeployment.recover (dep : AuthDeployment F C PK D Sig) (p : Nat) (anchor : Digest256)
    (disk : List UInt8) : Option (BeltWalTicketSeal × Nat × List CustodyIntent) :=
  match unsealBeltWalRecord dep.hash (dep.walKey p) (dep.lockSeal p) disk with
  | none => none
  | some (tkt, bytes) =>
    if dep.sealTag p tkt bytes = anchor then
      match dep.parseState bytes with
      | some s => some (tkt, s.1, s.2)
      | none => none
    else none

/-- The custodian after approving `i`: latch, log and coupon advanced, and a fresh record sealed
    under the next ticket and committed to the anchor. -/
def AuthDeployment.approveParty (dep : AuthDeployment F C PK D Sig) (p : Nat) (i : CustodyIntent)
    (P : AuthParty F) : AuthParty F :=
  { share := P.share
    latch := i.epoch + 1
    latched := i :: P.latched
    coupons := i.sessionId :: P.coupons
    poisoned := false
    ticket := dep.nextTicket p P.ticket
    disk := sealBeltWalRecord dep.hash (dep.walKey p) (dep.lockSeal p) (dep.nextTicket p P.ticket)
      (dep.stateBytes (i.epoch + 1) (i :: P.latched))
    anchor := dep.sealTag p (dep.nextTicket p P.ticket)
      (dep.stateBytes (i.epoch + 1) (i :: P.latched)) }

/-- The acknowledgement custodian `p` sends for `(d, i)`. -/
def AuthDeployment.approveAck (dep : AuthDeployment F C PK D Sig) (p d : Nat) (i : CustodyIntent)
    (P : AuthParty F) : AuthAck F :=
  { sender := p, deploymentId := d, intent := i, share := P.share, mac := dep.ackMac p d i }

/-- The custodian after a crash: coupons gone; latch, log and ticket read back from the disk
    record, or the custodian poisoned when the record is refused. -/
def AuthDeployment.crashParty (dep : AuthDeployment F C PK D Sig) (p : Nat) (P : AuthParty F) :
    AuthParty F :=
  match dep.recover p P.anchor P.disk with
  | some r =>
    { share := P.share, latch := r.2.1, latched := r.2.2, coupons := [], poisoned := P.poisoned,
      ticket := r.1, disk := P.disk, anchor := P.anchor }
  | none =>
    { share := P.share, latch := P.latch, latched := P.latched, coupons := [], poisoned := true,
      ticket := P.ticket, disk := P.disk, anchor := P.anchor }

abbrev setParty {n : Nat} (parties : Fin n → AuthParty F) (p : Fin n) (P : AuthParty F) :
    Fin n → AuthParty F :=
  fun q => if q = p then P else parties q

/-- Initial state: dealt shares, genesis records on disk and in the anchors. -/
def AuthState.init (dep : AuthDeployment F C PK D Sig) :
    AuthState F PK D Sig dep.core.quorum.numParties where
  parties := fun p =>
    { share := dep.core.trueShare p.val
      latch := 0
      latched := []
      coupons := []
      poisoned := false
      ticket := genesisTicket
      disk := sealBeltWalRecord dep.hash (dep.walKey p.val) (dep.lockSeal p.val) genesisTicket
        (dep.stateBytes 0 [])
      anchor := dep.sealTag p.val genesisTicket (dep.stateBytes 0 []) }
  wire := []
  corrupt := []
  ledger := (IdealCustodyState.init dep.core.deploymentId dep.core.pk dep.core.quorum).ledger

/-- The approval log of custodian `q`, empty for an index that is not enrolled. -/
def AuthState.latchedOf {n : Nat} (st : AuthState F PK D Sig n) (q : Nat) : List CustodyIntent :=
  if h : q < n then (st.parties ⟨q, h⟩).latched else []

/-- One turn of the authenticated network. -/
def authStep (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties) :
    AuthTurn F dep.core.quorum.numParties →
      Option (AuthState F PK D Sig dep.core.quorum.numParties × AuthEvent F Sig)
  | .approve p d i =>
    if p.val ∉ st.corrupt ∧ d = dep.core.deploymentId ∧ (st.parties p).latch ≤ i.epoch ∧
        i.sessionId ∉ (st.parties p).coupons ∧ (st.parties p).poisoned = false then
      some ({ st with
              parties := setParty st.parties p (dep.approveParty p.val i (st.parties p))
              wire := dep.approveAck p.val d i (st.parties p) :: st.wire },
            .approved (dep.approveAck p.val d i (st.parties p)))
    else none
  | .inject m =>
    if m.sender ∈ st.corrupt then
      some ({ st with wire := m :: st.wire }, .injected)
    else none
  | .deliver m =>
    if m.sender ∉ st.corrupt then
      some ({ st with wire := m :: st.wire }, .delivered)
    else none
  | .corrupt p =>
    if p.val ∉ st.corrupt ∧ st.corrupt.length + 1 < dep.core.quorum.threshold then
      some ({ st with corrupt := p.val :: st.corrupt },
            .corrupted (st.parties p).share (st.parties p).latched)
    else none
  | .crash p =>
    some ({ st with parties := setParty st.parties p (dep.crashParty p.val (st.parties p)) },
          .recovered (dep.recover p.val (st.parties p).anchor (st.parties p).disk).isSome)
  | .tamperDisk p raw =>
    some ({ st with
            parties := setParty st.parties p
              { share := (st.parties p).share, latch := (st.parties p).latch,
                latched := (st.parties p).latched, coupons := (st.parties p).coupons,
                poisoned := (st.parties p).poisoned, ticket := (st.parties p).ticket,
                disk := raw, anchor := (st.parties p).anchor } },
          .tampered)
  | .dropMsg idx =>
    some ({ st with wire := st.wire.take idx ++ st.wire.drop (idx + 1) }, .dropped)
  | .execute d approvers i ab =>
    (custodyLedgerSign dep.core.digests
        (dep.core.signWith (quorumKey dep.core (dep.verified st.wire) approvers i)) st.ledger
        (if quorumReady dep.core (dep.verified st.wire) approvers i then approvers.length else 0)
        d i ab).map
      (fun r => ({ st with ledger := r.1 }, AuthEvent.custody r.2))

/-- The two events that separate the network from the ideal functionality: a delivered message
    with a valid tag in the name of an uncorrupted custodian for an intent it has not approved,
    and a crash whose disk record passes recovery with another latch or log. -/
def authViolation (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties) :
    AuthTurn F dep.core.quorum.numParties → Bool
  | .deliver m =>
    dep.ackValid m && decide (m.deploymentId = dep.core.deploymentId) &&
      decide (m.sender ∉ st.corrupt) && !decide (m.intent ∈ st.latchedOf m.sender)
  | .crash p =>
    match dep.recover p.val (st.parties p).anchor (st.parties p).disk with
    | some r => !decide (r.2.1 = (st.parties p).latch ∧ r.2.2 = (st.parties p).latched)
    | none => false
  | _ => false

/-- The authenticated custodian network. -/
def authMachine (dep : AuthDeployment F C PK D Sig) :
    Machine (AuthState F PK D Sig dep.core.quorum.numParties)
      (AuthTurn F dep.core.quorum.numParties) (AuthEvent F Sig) where
  Init st := st = AuthState.init dep
  step := authStep dep
  errStep st _ := st

/-- `authMachine` with the two violation turns refused. -/
def authGuardedMachine (dep : AuthDeployment F C PK D Sig) :
    Machine (AuthState F PK D Sig dep.core.quorum.numParties)
      (AuthTurn F dep.core.quorum.numParties) (AuthEvent F Sig) where
  Init st := st = AuthState.init dep
  step st t := if authViolation dep st t = true then none else authStep dep st t
  errStep st _ := st

/-- The ideal port a turn implements. An injected message counts as an adversarial permit when it
    is for this deployment and carries a valid tag; `deliver`, `crash`, `tamperDisk` and `dropMsg`
    are internal. -/
def authVisIn (dep : AuthDeployment F C PK D Sig) :
    AuthTurn F dep.core.quorum.numParties → Option CustodyInput
  | .approve p d i => some (.approve p.val d i)
  | .inject m =>
    if m.deploymentId = dep.core.deploymentId ∧ dep.ackValid m = true then
      some (.advApprove m.sender m.deploymentId m.intent)
    else none
  | .deliver _ => none
  | .corrupt p => some (.corrupt p.val)
  | .crash _ => none
  | .tamperDisk _ _ => none
  | .dropMsg _ => none
  | .execute d _ i ab => some (.sign d i ab)

/-- The ideal output of an event. -/
def authVisOut : AuthEvent F Sig → CustodyOutcome Sig
  | .approved _ => .approvalRecorded
  | .injected => .approvalRecorded
  | .delivered => .approvalRecorded
  | .corrupted _ latched => .corrupted latched
  | .recovered _ => .approvalRecorded
  | .tampered => .approvalRecorded
  | .dropped => .approvalRecorded
  | .custody out => out

/-! ### The Section 1 view of an authenticated state -/

def AuthParty.toCustodian (P : AuthParty F) : Custodian F :=
  { share := P.share, latch := P.latch, latched := P.latched, coupons := P.coupons }

/-- The custodian table of Section 1 read off the `Fin n` family; an index that is not enrolled
    shows the dealt share and an empty log, as in `State.init`. -/
def viewNodes (dep : AuthDeployment F C PK D Sig)
    (parties : Fin dep.core.quorum.numParties → AuthParty F) : Nat → Custodian F :=
  fun q =>
    if h : q < dep.core.quorum.numParties then (parties ⟨q, h⟩).toCustodian
    else { share := dep.core.trueShare q, latch := 0, latched := [], coupons := [] }

/-- The Section 1 state the coordinator and the ideal functionality see: the custodians' shares,
    latches, logs and coupons, and the approvals with a valid tag. -/
def AuthDeployment.view (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties) : State F PK D Sig where
  nodes := viewNodes dep st.parties
  buffer := dep.verified st.wire
  corrupt := st.corrupt
  ledger := st.ledger

private theorem dc_dif_pos {α : Type} {p : Prop} [Decidable p] (hp : p) (a : p → α)
    (b : ¬ p → α) : (if h : p then a h else b h) = a hp := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem dc_dif_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a : p → α)
    (b : ¬ p → α) : (if h : p then a h else b h) = b hnp := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

omit [LawfulField F] [DecidableEq F] [DecidableEq D] in
private theorem state_ext {a b : State F PK D Sig} (hN : a.nodes = b.nodes)
    (hB : a.buffer = b.buffer) (hC : a.corrupt = b.corrupt) (hL : a.ledger = b.ledger) :
    a = b := by
  cases a; cases b
  dsimp only at hN hB hC hL
  subst hN hB hC hL
  rfl

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem viewNodes_enrolled (dep : AuthDeployment F C PK D Sig)
    (parties : Fin dep.core.quorum.numParties → AuthParty F)
    (p : Fin dep.core.quorum.numParties) :
    viewNodes dep parties p.val = (parties p).toCustodian := by
  unfold viewNodes
  exact dc_dif_pos p.isLt _ _

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem viewNodes_setParty (dep : AuthDeployment F C PK D Sig)
    (parties : Fin dep.core.quorum.numParties → AuthParty F)
    (p : Fin dep.core.quorum.numParties) (P : AuthParty F) :
    viewNodes dep (setParty parties p P) = setNode (viewNodes dep parties) p.val P.toCustodian := by
  funext q
  by_cases hqp : q = p.val
  · subst hqp
    rw [setNode_self, viewNodes_enrolled]
    show (if p = p then P else parties p).toCustodian = P.toCustodian
    rw [dc_if_pos rfl]
  · rw [setNode_ne _ _ _ _ hqp]
    by_cases hq : q < dep.core.quorum.numParties
    · have hne : (⟨q, hq⟩ : Fin dep.core.quorum.numParties) ≠ p :=
        fun h => hqp (congrArg Fin.val h)
      unfold viewNodes
      rw [dc_dif_pos hq, dc_dif_pos hq]
      show (if (⟨q, hq⟩ : Fin dep.core.quorum.numParties) = p then P
        else parties ⟨q, hq⟩).toCustodian = _
      rw [dc_if_neg hne]
    · unfold viewNodes
      rw [dc_dif_neg hq, dc_dif_neg hq]

omit [LawfulField F] [DecidableEq F] in
private theorem setNode_same (nodes : Nat → Custodian F) (p : Nat) :
    setNode nodes p (nodes p) = nodes := by
  funext q
  by_cases hqp : q = p
  · subst hqp
    exact setNode_self _ _ _
  · exact setNode_ne _ _ _ _ hqp

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem verified_cons_valid (dep : AuthDeployment F C PK D Sig) (m : AuthAck F)
    (wire : List (AuthAck F)) (h : dep.ackValid m = true) :
    dep.verified (m :: wire) = m.toApproval :: dep.verified wire := by
  unfold AuthDeployment.verified
  rw [List.filter_cons_of_pos h, List.map_cons]

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem verified_cons_invalid (dep : AuthDeployment F C PK D Sig) (m : AuthAck F)
    (wire : List (AuthAck F)) (h : ¬ dep.ackValid m = true) :
    dep.verified (m :: wire) = dep.verified wire := by
  unfold AuthDeployment.verified
  rw [List.filter_cons_of_neg h]

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem verified_subset (dep : AuthDeployment F C PK D Sig) {w' w : List (AuthAck F)}
    (hSub : ∀ m, m ∈ w' → m ∈ w) {a : Approval F} (ha : a ∈ dep.verified w') :
    a ∈ dep.verified w := by
  unfold AuthDeployment.verified at ha ⊢
  obtain ⟨m, hm, hEq⟩ := List.mem_map.mp ha
  obtain ⟨hmW, hV⟩ := List.mem_filter.mp hm
  exact List.mem_map.mpr ⟨m, List.mem_filter.mpr ⟨hSub m hmW, hV⟩, hEq⟩

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
/-- Replacing the buffer by one whose messages for this deployment are all backed by a recorded
    permit preserves the Section 1 relation. -/
private theorem rel_of_buffer (dep : Deployment F C PK D Sig) {c : State F PK D Sig}
    {a : IdealCustodyState PK D Sig} (hRel : Rel dep c a) (buffer' : List (Approval F))
    (hB : ∀ m : Approval F, m ∈ buffer' → m.deploymentId = dep.deploymentId →
      CustodyApproval.mk m.sender m.deploymentId m.intent ∈ a.honestApprovals ∨
        CustodyApproval.mk m.sender m.deploymentId m.intent ∈ a.corruptApprovals) :
    Rel dep { c with buffer := buffer' } a :=
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
    buffered := hB }

/-! ### The WAL invariant -/

/-- Every custodian's anchor is the MAC, under its current ticket, of state bytes that parse to
    its latch and log. -/
def AuthPartiesInv (dep : AuthDeployment F C PK D Sig)
    (parties : Fin dep.core.quorum.numParties → AuthParty F) : Prop :=
  ∀ p : Fin dep.core.quorum.numParties, ∃ bytes : List UInt8,
    (parties p).anchor = dep.sealTag p.val (parties p).ticket bytes ∧
      dep.parseState bytes = some ((parties p).latch, (parties p).latched)

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem partiesInv_setParty (dep : AuthDeployment F C PK D Sig)
    {parties : Fin dep.core.quorum.numParties → AuthParty F} (hInv : AuthPartiesInv dep parties)
    (p : Fin dep.core.quorum.numParties) (P : AuthParty F)
    (hP : ∃ bytes : List UInt8, P.anchor = dep.sealTag p.val P.ticket bytes ∧
      dep.parseState bytes = some (P.latch, P.latched)) :
    AuthPartiesInv dep (setParty parties p P) := by
  intro q
  by_cases hq : q = p
  · subst hq
    have e : setParty parties q P q = P := dc_if_pos rfl _ _
    rw [e]
    exact hP
  · have e : setParty parties p P q = parties q := dc_if_neg hq _ _
    rw [e]
    exact hInv q

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
/-- An accepted recovery returns a ticket and state bytes whose MAC is the anchor. -/
theorem AuthDeployment.recover_some (dep : AuthDeployment F C PK D Sig) {p : Nat}
    {anchor : Digest256} {disk : List UInt8} {tkt : BeltWalTicketSeal} {l : Nat}
    {L : List CustodyIntent} (h : dep.recover p anchor disk = some (tkt, l, L)) :
    ∃ bytes : List UInt8,
      unsealBeltWalRecord dep.hash (dep.walKey p) (dep.lockSeal p) disk = some (tkt, bytes) ∧
      dep.sealTag p tkt bytes = anchor ∧ dep.parseState bytes = some (l, L) := by
  unfold AuthDeployment.recover at h
  cases hU : unsealBeltWalRecord dep.hash (dep.walKey p) (dep.lockSeal p) disk with
  | none => rw [hU] at h; cases h
  | some r =>
    obtain ⟨tkt', bytes⟩ := r
    rw [hU] at h
    dsimp only at h
    by_cases hA : dep.sealTag p tkt' bytes = anchor
    · rw [dc_if_pos hA] at h
      cases hP : dep.parseState bytes with
      | none => rw [hP] at h; cases h
      | some s =>
        obtain ⟨l', L'⟩ := s
        rw [hP] at h
        cases h
        exact ⟨bytes, rfl, hA, hP⟩
    · rw [dc_if_neg hA] at h
      cases h

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
/-- **An untampered record recovers.** The record a custodian seals at a nonzero generation,
    checked against the anchor it committed, returns the sealed latch and log. -/
theorem AuthDeployment.recover_sealed (dep : AuthDeployment F C PK D Sig) (hWf : dep.WellFormed)
    (p : Nat) (tkt : BeltWalTicketSeal) (hGen : tkt.generation ≠ 0) (l : Nat)
    (L : List CustodyIntent) :
    dep.recover p (dep.sealTag p tkt (dep.stateBytes l L))
        (sealBeltWalRecord dep.hash (dep.walKey p) (dep.lockSeal p) tkt (dep.stateBytes l L)) =
      some (tkt, l, L) := by
  unfold AuthDeployment.recover
  rw [unsealBeltWalRecord_sealBeltWalRecord dep.hash (dep.walKey p) (dep.lockSeal p) tkt
    (dep.stateBytes l L) hGen]
  dsimp only
  rw [dc_if_pos rfl, hWf.parse_stateBytes l L]

/-! ### The refinement of the guarded machine -/

/-- Simulation relation: the Section 1 relation on the view, the ideal functionality's safety
    invariant, and the WAL invariant. -/
structure AuthRel (dep : AuthDeployment F C PK D Sig)
    (c : AuthState F PK D Sig dep.core.quorum.numParties) (a : IdealCustodyState PK D Sig) :
    Prop where
  rel : Rel dep.core (dep.view c) a
  safe : a.SafeInv dep.core.digests dep.core.idealOracle dep.core.deploymentId dep.core.pk
    dep.core.quorum
  wal : AuthPartiesInv dep c.parties

private theorem guarded_step_some (dep : AuthDeployment F C PK D Sig)
    {c c' : AuthState F PK D Sig dep.core.quorum.numParties}
    {t : AuthTurn F dep.core.quorum.numParties} {ev : AuthEvent F Sig}
    (h : (authGuardedMachine dep).step c t = some (c', ev)) :
    authViolation dep c t = false ∧ authStep dep c t = some (c', ev) := by
  have h' : (if authViolation dep c t = true then none else authStep dep c t) = some (c', ev) := h
  cases hV : authViolation dep c t with
  | true => rw [hV, dc_if_pos rfl] at h'; cases h'
  | false =>
    rw [hV, dc_if_neg Bool.false_ne_true] at h'
    exact ⟨rfl, h'⟩

private theorem guarded_step_of_no_violation (dep : AuthDeployment F C PK D Sig)
    (c : AuthState F PK D Sig dep.core.quorum.numParties)
    (t : AuthTurn F dep.core.quorum.numParties) (hV : authViolation dep c t = false) :
    (authGuardedMachine dep).step c t = authStep dep c t := by
  show (if authViolation dep c t = true then none else authStep dep c t) = authStep dep c t
  rw [hV, dc_if_neg Bool.false_ne_true]

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
/-- A delivered message that is not a violation, has a valid tag and is for this deployment is
    backed by a permit recorded through its sender's own port. -/
private theorem deliver_backed (dep : AuthDeployment F C PK D Sig)
    {c : AuthState F PK D Sig dep.core.quorum.numParties} {a : IdealCustodyState PK D Sig}
    (hRel : AuthRel dep c a) (m : AuthAck F) (hNotCor : m.sender ∉ c.corrupt)
    (hV : authViolation dep c (.deliver m) = false) (hValid : dep.ackValid m = true)
    (hDep : m.deploymentId = dep.core.deploymentId) :
    CustodyApproval.mk m.sender m.deploymentId m.intent ∈ a.honestApprovals := by
  have hEnr : m.sender < dep.core.quorum.numParties := by
    unfold AuthDeployment.ackValid at hValid
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hValid).1
  have hMem : m.intent ∈ c.latchedOf m.sender := by
    by_cases hMem : m.intent ∈ c.latchedOf m.sender
    · exact hMem
    · have hT : authViolation dep c (.deliver m) = true := by
        show (dep.ackValid m && decide (m.deploymentId = dep.core.deploymentId) &&
          decide (m.sender ∉ c.corrupt) && !decide (m.intent ∈ c.latchedOf m.sender)) = true
        rw [hValid, decide_eq_true hDep, decide_eq_true hNotCor, decide_eq_false hMem]
        rfl
      rw [hT] at hV
      cases hV
  have hLat : m.intent ∈ ((dep.view c).nodes m.sender).latched := by
    unfold AuthState.latchedOf at hMem
    rw [dc_dif_pos hEnr] at hMem
    show m.intent ∈ (viewNodes dep c.parties m.sender).latched
    unfold viewNodes
    rw [dc_dif_pos hEnr]
    exact hMem
  rw [hRel.rel.latched m.sender] at hLat
  obtain ⟨ap, hap, hParty, hInt⟩ := custodyRevealed_mem hLat
  have hApDep := (hRel.safe.honestBound ap hap).1
  cases ap with
  | mk party deploymentId intent =>
    dsimp only at hParty hInt hApDep
    subst hParty hInt
    rw [hDep, ← hApDep]
    exact hap

/-- A visible accepted turn of the guarded machine is an accepted step of the ideal functionality
    on its port with the mapped output. -/
private theorem auth_sim_visible (dep : AuthDeployment F C PK D Sig) (hWf : dep.WellFormed)
    {c c' : AuthState F PK D Sig dep.core.quorum.numParties} {a : IdealCustodyState PK D Sig}
    {t : AuthTurn F dep.core.quorum.numParties} {ev : AuthEvent F Sig} {j : CustodyInput}
    (hRel : AuthRel dep c a) (hStep : authStep dep c t = some (c', ev))
    (hVis : authVisIn dep t = some j) :
    ∃ a' : IdealCustodyState PK D Sig,
      idealCustodyStep dep.core.digests dep.core.idealOracle a j = some (a', authVisOut ev) ∧
        AuthRel dep c' a' := by
  cases t with
  | approve p d i =>
    cases hVis
    unfold authStep at hStep
    dsimp only at hStep
    by_cases hG : p.val ∉ c.corrupt ∧ d = dep.core.deploymentId ∧ (c.parties p).latch ≤ i.epoch ∧
        i.sessionId ∉ (c.parties p).coupons ∧ (c.parties p).poisoned = false
    · rw [dc_if_pos hG] at hStep
      cases hStep
      have hNode : (dep.view c).nodes p.val = (c.parties p).toCustodian :=
        viewNodes_enrolled dep c.parties p
      have hg : p.val < dep.core.quorum.numParties ∧ p.val ∉ (dep.view c).corrupt ∧
          d = dep.core.deploymentId ∧ ((dep.view c).nodes p.val).latch ≤ i.epoch ∧
          i.sessionId ∉ ((dep.view c).nodes p.val).coupons := by
        rw [hNode]
        exact ⟨p.isLt, hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1⟩
      have hAckValid : dep.ackValid (dep.approveAck p.val d i (c.parties p)) = true := by
        unfold AuthDeployment.ackValid AuthDeployment.approveAck
        dsimp only
        rw [decide_eq_true p.isLt, decide_eq_true rfl]
        rfl
      have hD : step dep.core (dep.view c) (.approve p.val d i) =
          some (dep.view
            { c with
              parties := setParty c.parties p (dep.approveParty p.val i (c.parties p))
              wire := dep.approveAck p.val d i (c.parties p) :: c.wire }, Event.approved) := by
        unfold step
        dsimp only
        rw [dc_if_pos hg]
        refine congrArg (fun s => some (s, Event.approved)) (state_ext ?_ ?_ rfl rfl)
        · show setNode (dep.view c).nodes p.val _ = viewNodes dep (setParty c.parties p _)
          rw [viewNodes_setParty, hNode]
          rfl
        · show _ :: (dep.view c).buffer = dep.verified (_ :: c.wire)
          rw [verified_cons_valid dep _ _ hAckValid, hNode]
          rfl
      obtain ⟨a', hA, hRel'⟩ := step_sim_visible dep.core hWf.core hRel.rel hD rfl
      exact ⟨a', hA,
        { rel := hRel'
          safe := idealCustodyStep_preserves_safeInv hRel.safe hA
          wal := partiesInv_setParty dep hRel.wal p _
            ⟨dep.stateBytes (i.epoch + 1) (i :: (c.parties p).latched), rfl,
              hWf.parse_stateBytes _ _⟩ }⟩
    · rw [dc_if_neg hG] at hStep
      cases hStep
  | inject m =>
    have hVis' : (if m.deploymentId = dep.core.deploymentId ∧ dep.ackValid m = true then
        some (CustodyInput.advApprove m.sender m.deploymentId m.intent) else none) = some j := hVis
    by_cases hc : m.deploymentId = dep.core.deploymentId ∧ dep.ackValid m = true
    · rw [dc_if_pos hc] at hVis'
      cases hVis'
      unfold authStep at hStep
      dsimp only at hStep
      by_cases hCor : m.sender ∈ c.corrupt
      · rw [dc_if_pos hCor] at hStep
        cases hStep
        have hD : step dep.core (dep.view c) (.inject m.toApproval) =
            some (dep.view { c with wire := m :: c.wire }, Event.injected) := by
          unfold step
          dsimp only
          have hCor' : m.toApproval.sender ∈ (dep.view c).corrupt := hCor
          rw [dc_if_pos hCor']
          refine congrArg (fun s => some (s, Event.injected)) (state_ext rfl ?_ rfl rfl)
          show _ :: (dep.view c).buffer = dep.verified (m :: c.wire)
          rw [verified_cons_valid dep _ _ hc.2]
          rfl
        have hVisD : visIn dep.core (.inject m.toApproval) =
            some (.advApprove m.sender m.deploymentId m.intent) := by
          show (if m.toApproval.deploymentId = dep.core.deploymentId then
            some (CustodyInput.advApprove m.toApproval.sender m.toApproval.deploymentId
              m.toApproval.intent) else none) = _
          have hDep' : m.toApproval.deploymentId = dep.core.deploymentId := hc.1
          rw [dc_if_pos hDep']
          rfl
        obtain ⟨a', hA, hRel'⟩ := step_sim_visible dep.core hWf.core hRel.rel hD hVisD
        exact ⟨a', hA,
          { rel := hRel'
            safe := idealCustodyStep_preserves_safeInv hRel.safe hA
            wal := hRel.wal }⟩
      · rw [dc_if_neg hCor] at hStep
        cases hStep
    · rw [dc_if_neg hc] at hVis'
      cases hVis'
  | deliver m => cases hVis
  | corrupt p =>
    cases hVis
    unfold authStep at hStep
    dsimp only at hStep
    by_cases hG : p.val ∉ c.corrupt ∧ c.corrupt.length + 1 < dep.core.quorum.threshold
    · rw [dc_if_pos hG] at hStep
      cases hStep
      have hNode : (dep.view c).nodes p.val = (c.parties p).toCustodian :=
        viewNodes_enrolled dep c.parties p
      have hg : p.val < dep.core.quorum.numParties ∧ p.val ∉ (dep.view c).corrupt ∧
          (dep.view c).corrupt.length + 1 < dep.core.quorum.threshold := ⟨p.isLt, hG.1, hG.2⟩
      have hD : step dep.core (dep.view c) (.corrupt p.val) =
          some (dep.view { c with corrupt := p.val :: c.corrupt },
            Event.corrupted (c.parties p).share (c.parties p).latched) := by
        unfold step
        dsimp only
        rw [dc_if_pos hg, hNode]
        rfl
      obtain ⟨a', hA, hRel'⟩ := step_sim_visible dep.core hWf.core hRel.rel hD rfl
      exact ⟨a', hA,
        { rel := hRel'
          safe := idealCustodyStep_preserves_safeInv hRel.safe hA
          wal := hRel.wal }⟩
    · rw [dc_if_neg hG] at hStep
      cases hStep
  | crash p => cases hVis
  | tamperDisk p raw => cases hVis
  | dropMsg idx => cases hVis
  | execute d approvers i ab =>
    cases hVis
    unfold authStep at hStep
    dsimp only at hStep
    cases hS : custodyLedgerSign dep.core.digests
        (dep.core.signWith (quorumKey dep.core (dep.verified c.wire) approvers i)) c.ledger
        (if quorumReady dep.core (dep.verified c.wire) approvers i then approvers.length else 0)
        d i ab with
    | none => rw [hS] at hStep; cases hStep
    | some r =>
      rw [hS] at hStep
      cases hStep
      have hD : step dep.core (dep.view c) (.execute d approvers i ab) =
          some (dep.view { c with ledger := r.1 }, Event.custody r.2) := by
        show ((custodyLedgerSign dep.core.digests
            (dep.core.signWith (quorumKey dep.core (dep.verified c.wire) approvers i)) c.ledger
            (if quorumReady dep.core (dep.verified c.wire) approvers i then approvers.length
              else 0) d i ab).map
            (fun r => ({ dep.view c with ledger := r.1 }, r.2))).map
            (fun r => (r.1, Event.custody r.2)) = _
        rw [hS]
        rfl
      obtain ⟨a', hA, hRel'⟩ := step_sim_visible dep.core hWf.core hRel.rel hD rfl
      exact ⟨a', hA,
        { rel := hRel'
          safe := idealCustodyStep_preserves_safeInv hRel.safe hA
          wal := hRel.wal }⟩

/-- An internal accepted turn of the guarded machine preserves the relation with the same ideal
    state. -/
private theorem auth_sim_internal (dep : AuthDeployment F C PK D Sig)
    {c c' : AuthState F PK D Sig dep.core.quorum.numParties} {a : IdealCustodyState PK D Sig}
    {t : AuthTurn F dep.core.quorum.numParties} {ev : AuthEvent F Sig}
    (hRel : AuthRel dep c a) (hViol : authViolation dep c t = false)
    (hStep : authStep dep c t = some (c', ev)) (hInt : authVisIn dep t = none) :
    AuthRel dep c' a := by
  cases t with
  | approve p d i => cases hInt
  | inject m =>
    have hInt' : (if m.deploymentId = dep.core.deploymentId ∧ dep.ackValid m = true then
        some (CustodyInput.advApprove m.sender m.deploymentId m.intent) else none) = none := hInt
    by_cases hc : m.deploymentId = dep.core.deploymentId ∧ dep.ackValid m = true
    · rw [dc_if_pos hc] at hInt'
      cases hInt'
    · unfold authStep at hStep
      dsimp only at hStep
      by_cases hCor : m.sender ∈ c.corrupt
      · rw [dc_if_pos hCor] at hStep
        cases hStep
        by_cases hValid : dep.ackValid m = true
        · have hDepNe : ¬ m.deploymentId = dep.core.deploymentId := fun h => hc ⟨h, hValid⟩
          have hD : step dep.core (dep.view c) (.inject m.toApproval) =
              some (dep.view { c with wire := m :: c.wire }, Event.injected) := by
            unfold step
            dsimp only
            have hCor' : m.toApproval.sender ∈ (dep.view c).corrupt := hCor
            rw [dc_if_pos hCor']
            refine congrArg (fun s => some (s, Event.injected)) (state_ext rfl ?_ rfl rfl)
            show _ :: (dep.view c).buffer = dep.verified (m :: c.wire)
            rw [verified_cons_valid dep _ _ hValid]
            rfl
          have hVisD : visIn dep.core (.inject m.toApproval) = none := by
            show (if m.toApproval.deploymentId = dep.core.deploymentId then
              some (CustodyInput.advApprove m.toApproval.sender m.toApproval.deploymentId
                m.toApproval.intent) else none) = _
            have hDep' : ¬ m.toApproval.deploymentId = dep.core.deploymentId := hDepNe
            rw [dc_if_neg hDep']
          exact
            { rel := step_sim_internal dep.core hRel.rel hD hVisD
              safe := hRel.safe
              wal := hRel.wal }
        · have hView : dep.view { c with wire := m :: c.wire } = dep.view c :=
            state_ext rfl (verified_cons_invalid dep m c.wire hValid) rfl rfl
          exact
            { rel := hView ▸ hRel.rel
              safe := hRel.safe
              wal := hRel.wal }
      · rw [dc_if_neg hCor] at hStep
        cases hStep
  | deliver m =>
    unfold authStep at hStep
    dsimp only at hStep
    by_cases hNotCor : m.sender ∉ c.corrupt
    · rw [dc_if_pos hNotCor] at hStep
      cases hStep
      by_cases hValid : dep.ackValid m = true
      · refine
          { rel := rel_of_buffer dep.core hRel.rel (dep.verified (m :: c.wire)) ?_
            safe := hRel.safe
            wal := hRel.wal }
        intro m' hm' hm'D
        rw [verified_cons_valid dep _ _ hValid] at hm'
        rcases List.mem_cons.mp hm' with hEq | hOld
        · subst hEq
          exact .inl (deliver_backed dep hRel m hNotCor hViol hValid hm'D)
        · exact hRel.rel.buffered m' hOld hm'D
      · have hView : dep.view { c with wire := m :: c.wire } = dep.view c :=
          state_ext rfl (verified_cons_invalid dep m c.wire hValid) rfl rfl
        exact
          { rel := hView ▸ hRel.rel
            safe := hRel.safe
            wal := hRel.wal }
    · rw [dc_if_neg hNotCor] at hStep
      cases hStep
  | corrupt p => cases hInt
  | crash p =>
    unfold authStep at hStep
    dsimp only at hStep
    cases hStep
    have hNode : (dep.view c).nodes p.val = (c.parties p).toCustodian :=
      viewNodes_enrolled dep c.parties p
    have hCust : (dep.crashParty p.val (c.parties p)).toCustodian =
        { share := (c.parties p).share, latch := (c.parties p).latch,
          latched := (c.parties p).latched, coupons := [] } := by
      unfold AuthDeployment.crashParty
      cases hR : dep.recover p.val (c.parties p).anchor (c.parties p).disk with
      | none => rfl
      | some r =>
        have hV : (!decide (r.2.1 = (c.parties p).latch ∧ r.2.2 = (c.parties p).latched)) =
            false := by
          have hV' : (match dep.recover p.val (c.parties p).anchor (c.parties p).disk with
            | some r => !decide (r.2.1 = (c.parties p).latch ∧ r.2.2 = (c.parties p).latched)
            | none => false) = false := hViol
          rw [hR] at hV'
          exact hV'
        have hEq : r.2.1 = (c.parties p).latch ∧ r.2.2 = (c.parties p).latched := by
          by_cases hEq : r.2.1 = (c.parties p).latch ∧ r.2.2 = (c.parties p).latched
          · exact hEq
          · rw [decide_eq_false hEq] at hV
            cases hV
        show AuthParty.toCustodian
          { share := (c.parties p).share, latch := r.2.1, latched := r.2.2, coupons := [],
            poisoned := (c.parties p).poisoned, ticket := r.1, disk := (c.parties p).disk,
            anchor := (c.parties p).anchor } = _
        unfold AuthParty.toCustodian
        dsimp only
        rw [hEq.1, hEq.2]
    have hD : step dep.core (dep.view c) (.crash p.val) =
        some (dep.view
          { c with parties := setParty c.parties p (dep.crashParty p.val (c.parties p)) },
          Event.recovered) := by
      unfold step
      dsimp only
      refine congrArg (fun s => some (s, Event.recovered)) (state_ext ?_ rfl rfl rfl)
      show setNode (dep.view c).nodes p.val _ = viewNodes dep (setParty c.parties p _)
      rw [viewNodes_setParty, hCust, hNode]
      rfl
    refine
      { rel := step_sim_internal dep.core hRel.rel hD rfl
        safe := hRel.safe
        wal := partiesInv_setParty dep hRel.wal p _ ?_ }
    unfold AuthDeployment.crashParty
    cases hR : dep.recover p.val (c.parties p).anchor (c.parties p).disk with
    | none => exact hRel.wal p
    | some r =>
      obtain ⟨tkt, l, L⟩ := r
      obtain ⟨bytes, _, hTag, hParse⟩ := dep.recover_some hR
      exact ⟨bytes, hTag.symm, hParse⟩
  | tamperDisk p raw =>
    unfold authStep at hStep
    dsimp only at hStep
    cases hStep
    have hView : dep.view
        { c with
          parties := setParty c.parties p
            { share := (c.parties p).share, latch := (c.parties p).latch,
              latched := (c.parties p).latched, coupons := (c.parties p).coupons,
              poisoned := (c.parties p).poisoned, ticket := (c.parties p).ticket,
              disk := raw, anchor := (c.parties p).anchor } } = dep.view c := by
      refine state_ext ?_ rfl rfl rfl
      show viewNodes dep (setParty c.parties p _) = viewNodes dep c.parties
      rw [viewNodes_setParty]
      have hSame : AuthParty.toCustodian
          { share := (c.parties p).share, latch := (c.parties p).latch,
            latched := (c.parties p).latched, coupons := (c.parties p).coupons,
            poisoned := (c.parties p).poisoned, ticket := (c.parties p).ticket,
            disk := raw, anchor := (c.parties p).anchor } =
          viewNodes dep c.parties p.val := by
        rw [viewNodes_enrolled]
        rfl
      rw [hSame]
      exact setNode_same _ _
    exact
      { rel := hView ▸ hRel.rel
        safe := hRel.safe
        wal := partiesInv_setParty dep hRel.wal p _ (hRel.wal p) }
  | dropMsg idx =>
    unfold authStep at hStep
    dsimp only at hStep
    cases hStep
    refine
      { rel := rel_of_buffer dep.core hRel.rel
          (dep.verified (c.wire.take idx ++ c.wire.drop (idx + 1))) ?_
        safe := hRel.safe
        wal := hRel.wal }
    intro m' hm' hm'D
    refine hRel.rel.buffered m' (verified_subset dep ?_ hm') hm'D
    intro m hm
    rcases List.mem_append.mp hm with hT | hDr
    · exact List.mem_of_mem_take hT
    · exact List.mem_of_mem_drop hDr
  | execute d approvers i ab => cases hInt

omit [DecidableEq C] in
omit [DecidableEq F] [DecidableEq D] in
private theorem auth_init_rel (dep : AuthDeployment F C PK D Sig) (hWf : dep.WellFormed) :
    AuthRel dep (AuthState.init dep)
      (IdealCustodyState.init dep.core.deploymentId dep.core.pk dep.core.quorum) where
  rel := by
    have hView : dep.view (AuthState.init dep) = State.init dep.core := by
      refine state_ext ?_ rfl rfl rfl
      funext q
      show viewNodes dep (AuthState.init dep).parties q = _
      unfold viewNodes
      by_cases hq : q < dep.core.quorum.numParties
      · rw [dc_dif_pos hq]
        rfl
      · rw [dc_dif_neg hq]
        rfl
    rw [hView]
    exact init_rel dep.core
  safe := IdealCustodyState.init_safeInv _ _ _ _ _
  wal := fun p => ⟨dep.stateBytes 0 [], rfl, hWf.parse_stateBytes 0 []⟩

/-- **The guarded authenticated network refines `Spec.idealCustodyMachine`.** `approve`, a
    validly tagged `inject` for this deployment, `corrupt` and `execute` implement the four ideal
    ports; every other accepted turn leaves the ideal state where it is. -/
def authCustody_refines_ideal (dep : AuthDeployment F C PK D Sig) (hWf : dep.WellFormed) :
    DataRefines (authGuardedMachine dep)
      (idealCustodyMachine dep.core.digests dep.core.idealOracle dep.core.deploymentId
        dep.core.pk dep.core.quorum)
      (authVisIn dep) authVisOut where
  Rel := AuthRel dep
  absInit := fun _ => IdealCustodyState.init dep.core.deploymentId dep.core.pk dep.core.quorum
  init_ok {c₀} hInit := by
    have h0 : c₀ = AuthState.init dep := hInit
    subst h0
    exact ⟨rfl, auth_init_rel dep hWf⟩
  sim_visible hRel hStepC hVis :=
    auth_sim_visible dep hWf hRel (guarded_step_some dep hStepC).2 hVis
  sim_internal hRel hStepC hVis :=
    auth_sim_internal dep hRel (guarded_step_some dep hStepC).1 (guarded_step_some dep hStepC).2
      hVis
  sim_reject hRel _ := hRel

/-! ### What a violation is -/

/-- A tag on a fresh preimage: `m` carries the correct `custodianAckTag` under the key of an
    enrolled, uncorrupted custodian, and its preimage differs from the preimage of every
    acknowledgement that custodian has sent. -/
def AckMacForgery (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties) (m : AuthAck F) : Prop :=
  m.sender < dep.core.quorum.numParties ∧ m.sender ∉ st.corrupt ∧
    m.mac = dep.ackMac m.sender m.deploymentId m.intent ∧
    ∀ i : CustodyIntent, i ∈ st.latchedOf m.sender →
      dep.ackFrame m.sender dep.core.deploymentId i ≠
        dep.ackFrame m.sender m.deploymentId m.intent

/-- Two distinct intents of this deployment with the same message tag. -/
def MsgTagCollision (dep : AuthDeployment F C PK D Sig) : Prop :=
  ∃ i j : CustodyIntent, i ≠ j ∧
    dep.msgTag dep.core.deploymentId i = dep.msgTag dep.core.deploymentId j

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
/-- **A `deliver` violation is a tag forgery or a message-tag collision.** -/
theorem deliver_violation_classified (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties) (m : AuthAck F)
    (hV : authViolation dep st (.deliver m) = true) :
    AckMacForgery dep st m ∨ MsgTagCollision dep := by
  have hV' : (dep.ackValid m && decide (m.deploymentId = dep.core.deploymentId) &&
      decide (m.sender ∉ st.corrupt) && !decide (m.intent ∈ st.latchedOf m.sender)) = true := hV
  obtain ⟨h123, h4⟩ := Bool.and_eq_true_iff.mp hV'
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h123
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
  have hDep : m.deploymentId = dep.core.deploymentId := of_decide_eq_true h2
  have hNotCor : m.sender ∉ st.corrupt := of_decide_eq_true h3
  have hNotMem : m.intent ∉ st.latchedOf m.sender := by
    intro hMem
    rw [decide_eq_true hMem] at h4
    cases h4
  unfold AuthDeployment.ackValid at h1
  obtain ⟨hEnr, hMac⟩ := Bool.and_eq_true_iff.mp h1
  cases hAny : (st.latchedOf m.sender).any
      (fun i => decide (dep.msgTag dep.core.deploymentId i =
        dep.msgTag dep.core.deploymentId m.intent)) with
  | true =>
    obtain ⟨i, hi, hTag⟩ := List.any_eq_true.mp hAny
    exact .inr ⟨i, m.intent, fun h => hNotMem (h ▸ hi), of_decide_eq_true hTag⟩
  | false =>
    refine .inl ⟨of_decide_eq_true hEnr, hNotCor, of_decide_eq_true hMac, ?_⟩
    intro i hi hFrame
    unfold AuthDeployment.ackFrame at hFrame
    rw [hDep] at hFrame
    have hTag := (custodianAckFrame_injective hFrame).2.2.2.1
    have hT : (st.latchedOf m.sender).any
        (fun i => decide (dep.msgTag dep.core.deploymentId i =
          dep.msgTag dep.core.deploymentId m.intent)) = true :=
      List.any_eq_true.mpr ⟨i, hi, decide_eq_true hTag⟩
    rw [hT] at hAny
    cases hAny

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
/-- **A `crash` violation exhibits a hash collision.** Under the WAL invariant, a disk record that
    passes recovery with a latch or log other than the custodian's own has the anchor's MAC on
    other state bytes. -/
theorem crash_violation_collision (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties) (hInv : AuthPartiesInv dep st.parties)
    (p : Fin dep.core.quorum.numParties) (hV : authViolation dep st (.crash p) = true) :
    Nonempty (HashCollision256 dep.hash) := by
  have hV' : (match dep.recover p.val (st.parties p).anchor (st.parties p).disk with
    | some r => !decide (r.2.1 = (st.parties p).latch ∧ r.2.2 = (st.parties p).latched)
    | none => false) = true := hV
  cases hR : dep.recover p.val (st.parties p).anchor (st.parties p).disk with
  | none => rw [hR] at hV'; cases hV'
  | some r =>
    obtain ⟨tkt, l, L⟩ := r
    rw [hR] at hV'
    have hNe : ¬ (l = (st.parties p).latch ∧ L = (st.parties p).latched) := by
      intro hEq
      have hV'' : (!decide (l = (st.parties p).latch ∧ L = (st.parties p).latched)) = true := hV'
      rw [decide_eq_true hEq] at hV''
      cases hV''
    obtain ⟨bytes', _, hTag', hParse'⟩ := dep.recover_some hR
    obtain ⟨bytes, hAnchor, hParse⟩ := hInv p
    have hTagEq : computeBeltWalSealTag dep.hash (dep.walKey p.val) (dep.lockSeal p.val) tkt
        bytes' = computeBeltWalSealTag dep.hash (dep.walKey p.val) (dep.lockSeal p.val)
        (st.parties p).ticket bytes := hTag'.trans hAnchor
    rcases computeBeltWalSealTag_binding dep.hash hTagEq with ⟨_, _, _, hBytes⟩ | hCol
    · rw [hBytes, hParse] at hParse'
      have hPair := Option.some.inj hParse'
      exact absurd ⟨(congrArg Prod.fst hPair).symm, (congrArg Prod.snd hPair).symm⟩ hNe
    · exact hCol

/-! ### The unguarded machine -/

/-- **Identical until the first violation.** Every execution of `authMachine` is an execution of
    the guarded machine, or has a prefix that the guarded machine also runs and that ends in a
    state where the next turn is a violation. -/
theorem authMachine_trace_guarded_or_violation (dep : AuthDeployment F C PK D Sig)
    {s s' : AuthState F PK D Sig dep.core.quorum.numParties}
    {tr : List (AuthTurn F dep.core.quorum.numParties × AuthEvent F Sig)}
    (hTr : (authMachine dep).ValidTrace s tr s') :
    (authGuardedMachine dep).ValidTrace s tr s' ∨
      ∃ (tr₀ : List (AuthTurn F dep.core.quorum.numParties × AuthEvent F Sig))
        (st : AuthState F PK D Sig dep.core.quorum.numParties)
        (t : AuthTurn F dep.core.quorum.numParties),
        (authGuardedMachine dep).ValidTrace s tr₀ st ∧ authViolation dep st t = true := by
  induction hTr with
  | nil s => exact .inl (.nil s)
  | @accept s s₁ sF inp out rest hStep _ ih =>
    cases hV : authViolation dep s inp with
    | true => exact .inr ⟨[], s, inp, .nil s, hV⟩
    | false =>
      have hG : (authGuardedMachine dep).step s inp = some (s₁, out) :=
        (guarded_step_of_no_violation dep s inp hV).trans hStep
      rcases ih with hT | ⟨tr₀, st, t, hT, hVt⟩
      · exact .inl (.accept hG hT)
      · exact .inr ⟨(inp, out) :: tr₀, st, t, .accept hG hT, hVt⟩
  | @reject s sF inp rest hNone _ ih =>
    have hG : (authGuardedMachine dep).step s inp = none := by
      cases hV : authViolation dep s inp with
      | true =>
        show (if authViolation dep s inp = true then none else authStep dep s inp) = none
        rw [hV, dc_if_pos rfl]
      | false => exact (guarded_step_of_no_violation dep s inp hV).trans hNone
    rcases ih with hT | ⟨tr₀, st, t, hT, hVt⟩
    · exact .inl (.reject inp hG hT)
    · exact .inr ⟨tr₀, st, t, .reject inp hG hT, hVt⟩

/-- **Every execution of the authenticated network is an execution of the ideal functionality, or
    exhibits a forgery or a collision.** For any schedule of `authMachine` from its initial state,
    the projected trace is a trace of `Spec.idealCustodyMachine`, or a state the guarded machine
    reaches admits a tag forgery, or two intents share a message tag, or the hash has a
    collision. -/
theorem authCustody_ideal_or_forgery (dep : AuthDeployment F C PK D Sig) (hWf : dep.WellFormed)
    {tr : List (AuthTurn F dep.core.quorum.numParties × AuthEvent F Sig)}
    (hAdmits : (authMachine dep).AdmitsTrace tr) :
    (idealCustodyMachine dep.core.digests dep.core.idealOracle dep.core.deploymentId dep.core.pk
        dep.core.quorum).AdmitsTrace (projectTrace (authVisIn dep) authVisOut tr) ∨
    (∃ (st : AuthState F PK D Sig dep.core.quorum.numParties) (m : AuthAck F),
      (authGuardedMachine dep).Reachable st ∧ AckMacForgery dep st m) ∨
    MsgTagCollision dep ∨ Nonempty (HashCollision256 dep.hash) := by
  obtain ⟨s₀, sF, hInit, hTr⟩ := hAdmits
  have hInitG : (authGuardedMachine dep).Init s₀ := hInit
  rcases authMachine_trace_guarded_or_violation dep hTr with hG | ⟨tr₀, st, t, hG, hV⟩
  · exact .inl ((authCustody_refines_ideal dep hWf).preserve_admitsTrace ⟨s₀, sF, hInitG, hG⟩)
  · have hReach : (authGuardedMachine dep).Reachable st := ⟨s₀, tr₀, hInitG, hG⟩
    obtain ⟨a, _, hRel⟩ := (authCustody_refines_ideal dep hWf).reachable_rel hReach
    have hRel' : AuthRel dep st a := hRel
    cases t with
    | deliver m =>
      rcases deliver_violation_classified dep st m hV with hF | hC
      · exact .inr (.inl ⟨st, m, hReach, hF⟩)
      · exact .inr (.inr (.inl hC))
    | crash p => exact .inr (.inr (.inr (crash_violation_collision dep st hRel'.wal p hV)))
    | approve p d i => cases hV
    | inject m => cases hV
    | corrupt p => cases hV
    | tamperDisk p raw => cases hV
    | dropMsg idx => cases hV
    | execute d approvers i ab => cases hV

/-- **Safety of every state the guarded network reaches.** Fewer than `threshold` custodians are
    corrupted; cumulative spend is within the cap; every WAL release carries the dealt key's
    signature on `digest deploymentId intent` and its intent is in the approval log of an enrolled
    custodian whose latch has moved past its epoch; no custodian has approved two intents at one
    epoch; and every custodian's anchor commits to its latch and log. -/
theorem authCustody_reachable_safe (dep : AuthDeployment F C PK D Sig) (hWf : dep.WellFormed)
    {st : AuthState F PK D Sig dep.core.quorum.numParties}
    (hReach : (authGuardedMachine dep).Reachable st) :
    st.corrupt.length < dep.core.quorum.threshold ∧
    st.ledger.spent ≤ dep.core.quorum.spendCap ∧
    (∀ r : CustodyRelease D Sig, r ∈ st.ledger.releasedHistory →
      r.sig = dep.core.signWith dep.core.secret
        (dep.core.digests.digest dep.core.deploymentId r.intent) ∧
      ∃ p : Fin dep.core.quorum.numParties, r.intent ∈ (st.parties p).latched ∧
        r.intent.epoch < (st.parties p).latch) ∧
    (∀ p : Fin dep.core.quorum.numParties,
      ((st.parties p).latched.map CustodyIntent.epoch).Nodup) ∧
    AuthPartiesInv dep st.parties := by
  obtain ⟨a, hReachA, hRel⟩ := (authCustody_refines_ideal dep hWf).reachable_rel hReach
  have hRel' : AuthRel dep st a := hRel
  have hCor : a.corruptParties = st.corrupt := hRel'.rel.corrupt
  have hLed : a.ledger = st.ledger := hRel'.rel.ledger
  refine ⟨hCor ▸ hRel'.safe.corruptBudget, hLed ▸ hRel'.safe.budget, ?_, ?_, hRel'.wal⟩
  · intro r hr
    obtain ⟨hSig, q, hLt, hMem⟩ :=
      idealCustody_reachable_release_honestly_approved hReachA (hLed ▸ hr)
    refine ⟨hSig, ⟨q, hLt⟩, ?_⟩
    have hLat : r.intent ∈ ((dep.view st).nodes q).latched := by
      rw [hRel'.rel.latched q]
      unfold custodyRevealed
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hMem, decide_eq_true rfl⟩, rfl⟩
    have hBound := hRel'.rel.inv.latchBound q _ hLat
    have hNode : (dep.view st).nodes q = (st.parties ⟨q, hLt⟩).toCustodian :=
      viewNodes_enrolled dep st.parties ⟨q, hLt⟩
    rw [hNode] at hLat hBound
    exact ⟨hLat, hBound⟩
  · intro p
    have hNd := hRel'.rel.inv.latchNodup p.val
    have hNode : (dep.view st).nodes p.val = (st.parties p).toCustodian :=
      viewNodes_enrolled dep st.parties p
    rw [hNode] at hNd
    exact hNd

/-! ### Runs and the unsafe-release event -/

/-- The state after running a schedule on `authMachine`, and whether some turn was a violation
    of kind `ev` at the state it was taken in. -/
def authRun (dep : AuthDeployment F C PK D Sig)
    (ev : AuthState F PK D Sig dep.core.quorum.numParties →
      AuthTurn F dep.core.quorum.numParties → Bool) :
    AuthState F PK D Sig dep.core.quorum.numParties →
      List (AuthTurn F dep.core.quorum.numParties) →
      AuthState F PK D Sig dep.core.quorum.numParties × Bool
  | st, [] => (st, false)
  | st, t :: ts =>
    ((authRun dep ev ((authMachine dep).runStep st t).1 ts).1,
      ev st t || (authRun dep ev ((authMachine dep).runStep st t).1 ts).2)

/-- The `deliver` half of `authViolation`. -/
def authAckViolation (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties) :
    AuthTurn F dep.core.quorum.numParties → Bool
  | .deliver m => authViolation dep st (.deliver m)
  | _ => false

/-- The `crash` half of `authViolation`. -/
def authWalViolation (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties) :
    AuthTurn F dep.core.quorum.numParties → Bool
  | .crash p => authViolation dep st (.crash p)
  | _ => false

/-- The coordinator's WAL holds a release whose intent is in no enrolled custodian's approval
    log. -/
def authUnsafeRelease (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties) : Bool :=
  st.ledger.releasedHistory.any (fun r =>
    !(List.range dep.core.quorum.numParties).any (fun q => decide (r.intent ∈ st.latchedOf q)))

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
theorem authViolation_split (dep : AuthDeployment F C PK D Sig)
    (st : AuthState F PK D Sig dep.core.quorum.numParties)
    (t : AuthTurn F dep.core.quorum.numParties) :
    authViolation dep st t = (authAckViolation dep st t || authWalViolation dep st t) := by
  cases t with
  | deliver m => exact (Bool.or_false _).symm
  | crash p => exact (Bool.false_or _).symm
  | approve p d i => rfl
  | inject m => rfl
  | corrupt p => rfl
  | tamperDisk p raw => rfl
  | dropMsg idx => rfl
  | execute d approvers i ab => rfl

/-- The final state of a run does not depend on the event that is tracked. -/
theorem authRun_state (dep : AuthDeployment F C PK D Sig)
    (ev ev' : AuthState F PK D Sig dep.core.quorum.numParties →
      AuthTurn F dep.core.quorum.numParties → Bool) :
    ∀ (ts : List (AuthTurn F dep.core.quorum.numParties))
      (st : AuthState F PK D Sig dep.core.quorum.numParties),
      (authRun dep ev st ts).1 = (authRun dep ev' st ts).1
  | [], _ => rfl
  | _ :: ts, _ => authRun_state dep ev ev' ts _

/-- A run flags a violation exactly when it flags one of the two kinds. -/
theorem authRun_violation_split (dep : AuthDeployment F C PK D Sig) :
    ∀ (ts : List (AuthTurn F dep.core.quorum.numParties))
      (st : AuthState F PK D Sig dep.core.quorum.numParties),
      (authRun dep (authViolation dep) st ts).2 =
        ((authRun dep (authAckViolation dep) st ts).2 ||
          (authRun dep (authWalViolation dep) st ts).2)
  | [], _ => rfl
  | t :: ts, st => by
    show (authViolation dep st t ||
        (authRun dep (authViolation dep) ((authMachine dep).runStep st t).1 ts).2) =
      ((authAckViolation dep st t ||
          (authRun dep (authAckViolation dep) ((authMachine dep).runStep st t).1 ts).2) ||
        (authWalViolation dep st t ||
          (authRun dep (authWalViolation dep) ((authMachine dep).runStep st t).1 ts).2))
    rw [authRun_violation_split dep ts, authViolation_split]
    cases authAckViolation dep st t <;> cases authWalViolation dep st t <;>
      cases (authRun dep (authAckViolation dep) ((authMachine dep).runStep st t).1 ts).2 <;>
      cases (authRun dep (authWalViolation dep) ((authMachine dep).runStep st t).1 ts).2 <;> rfl

/-- A run without a violation is an execution of the guarded machine. -/
theorem authRun_guarded (dep : AuthDeployment F C PK D Sig)
    (ts : List (AuthTurn F dep.core.quorum.numParties)) :
    ∀ (st : AuthState F PK D Sig dep.core.quorum.numParties),
      (authRun dep (authViolation dep) st ts).2 = false →
      ∃ tr : List (AuthTurn F dep.core.quorum.numParties × AuthEvent F Sig),
        (authGuardedMachine dep).ValidTrace st tr (authRun dep (authViolation dep) st ts).1 := by
  induction ts with
  | nil => exact fun st _ => ⟨[], .nil st⟩
  | cons t ts ih =>
    intro st h
    have h' : (authViolation dep st t ||
        (authRun dep (authViolation dep) ((authMachine dep).runStep st t).1 ts).2) = false := h
    obtain ⟨hV, hRest⟩ := Bool.or_eq_false_iff.mp h'
    obtain ⟨tr, hTr⟩ := ih ((authMachine dep).runStep st t).1 hRest
    have hTr' : (authGuardedMachine dep).ValidTrace ((authMachine dep).runStep st t).1 tr
        (authRun dep (authViolation dep) st (t :: ts)).1 := hTr
    cases hS : authStep dep st t with
    | none =>
      have hNext : ((authMachine dep).runStep st t).1 = st := by
        unfold Machine.runStep
        have hS' : (authMachine dep).step st t = none := hS
        rw [hS']
        rfl
      rw [hNext] at hTr'
      exact ⟨tr, .reject t ((guarded_step_of_no_violation dep st t hV).trans hS) hTr'⟩
    | some r =>
      have hNext : ((authMachine dep).runStep st t).1 = r.1 := by
        unfold Machine.runStep
        have hS' : (authMachine dep).step st t = some r := hS
        rw [hS']
      rw [hNext] at hTr'
      exact ⟨(t, r.2) :: tr,
        .accept ((guarded_step_of_no_violation dep st t hV).trans hS) hTr'⟩

/-- **An unsafe release needs a violation.** If, after any schedule from the initial state, the
    coordinator's WAL holds a release that no enrolled custodian approved, then some turn of the
    schedule was a violation. -/
theorem authRun_unsafe_release_violation (dep : AuthDeployment F C PK D Sig)
    (hWf : dep.WellFormed) (ts : List (AuthTurn F dep.core.quorum.numParties))
    (hU : authUnsafeRelease dep
      (authRun dep (authViolation dep) (AuthState.init dep) ts).1 = true) :
    (authRun dep (authViolation dep) (AuthState.init dep) ts).2 = true := by
  cases hB : (authRun dep (authViolation dep) (AuthState.init dep) ts).2 with
  | true => rfl
  | false =>
    obtain ⟨tr, hTr⟩ := authRun_guarded dep ts (AuthState.init dep) hB
    have hReach : (authGuardedMachine dep).Reachable
        (authRun dep (authViolation dep) (AuthState.init dep) ts).1 :=
      ⟨AuthState.init dep, tr, rfl, hTr⟩
    obtain ⟨_, _, hRelease, _, _⟩ := authCustody_reachable_safe dep hWf hReach
    unfold authUnsafeRelease at hU
    obtain ⟨r, hr, hb⟩ := List.any_eq_true.mp hU
    obtain ⟨_, p, hMem, _⟩ := hRelease r hr
    have hLat : r.intent ∈
        (authRun dep (authViolation dep) (AuthState.init dep) ts).1.latchedOf p.val := by
      unfold AuthState.latchedOf
      rw [dc_dif_pos p.isLt]
      exact hMem
    have hAny : (List.range dep.core.quorum.numParties).any (fun q => decide (r.intent ∈
        (authRun dep (authViolation dep) (AuthState.init dep) ts).1.latchedOf q)) = true :=
      List.any_eq_true.mpr ⟨p.val, List.mem_range.mpr p.isLt, decide_eq_true hLat⟩
    rw [hAny] at hb
    cases hb

end Authenticated

#verify_constructive
  Qsag.DistCustody.AuthDeployment.recover_some
  Qsag.DistCustody.AuthDeployment.recover_sealed
  Qsag.DistCustody.deliver_violation_classified
  Qsag.DistCustody.crash_violation_collision
  Qsag.DistCustody.authMachine_trace_guarded_or_violation
  Qsag.DistCustody.authCustody_ideal_or_forgery
  Qsag.DistCustody.authCustody_reachable_safe
  Qsag.DistCustody.authRun_violation_split
  Qsag.DistCustody.authRun_guarded
  Qsag.DistCustody.authRun_unsafe_release_violation

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
