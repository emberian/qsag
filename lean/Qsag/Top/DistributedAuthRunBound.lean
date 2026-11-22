module
public import Qsag.Top.CertCustodyAdaptiveBound
public import Qsag.Custody.DistributedThresholdCustodyRefinement
public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
public import Qsag.Custody.KeyHidingAuthCustodyBound
public import Qsag.Spec.Assumptions
import Qsag.Tactic.Prelude

public section
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag.DistributedAuthRun
open Spec KeyHidingCustody DistCustody

abbrev DeploymentId := Vector UInt8 32

/-- Rust authenticates the fixed header, mode, 32 deployment bytes, then the payload. -/
structure Frame where
  header : Vector UInt8 56
  mode : UInt8
  deployment : DeploymentId
  payload : Spec.Bytes
  deriving DecidableEq

def Frame.raw (m : Frame) : Spec.Bytes :=
  m.header.toList ++ m.mode :: (m.deployment.toList ++ m.payload)

theorem Frame.raw_injective {a b : Frame} (h : a.raw = b.raw) : a = b := by
  cases a with
  | mk ha ma da pa =>
    cases b with
    | mk hb mb db pb =>
      have hh := congrArg (List.take 56) h
      have hh' : ha = hb := Vector.toList_inj.mp (by simpa [Frame.raw, List.take_append] using hh)
      subst hb
      obtain ⟨rfl,body⟩ := List.cons.inj (List.append_cancel_left h)
      have hd := congrArg (List.take 32) body
      have hd' : da = db := Vector.toList_inj.mp (by simpa [List.take_append] using hd)
      subst db
      cases List.append_cancel_left body
      rfl

def accepts (id : DeploymentId) (mac : Spec.Bytes → Spec.Bytes) (m : Frame) (tag : Spec.Bytes) : Bool :=
  decide (m.deployment = id) && decide (tag = mac m.raw)

theorem foreign_replay_rejected (a b : DeploymentId) (hne : a ≠ b)
    (mac : Spec.Bytes → Spec.Bytes) (m : Frame) (hm : m.deployment = a) (tag : Spec.Bytes) :
    accepts b mac m tag = false := by simp [accepts, hm, hne]

theorem relabel_requires_collision (m : Frame) (b : DeploymentId) (mac : Spec.Bytes → Spec.Bytes)
    (hne : m.deployment ≠ b) (h : accepts b mac {m with deployment := b} (mac m.raw) = true) :
    m.raw ≠ ({m with deployment := b} : Frame).raw ∧
      mac m.raw = mac ({m with deployment := b} : Frame).raw := by
  constructor
  · intro he
    have he' : m.deployment.toList ++ m.payload = b.toList ++ m.payload := by
      exact (List.cons.inj (List.append_cancel_left he)).2
    exact hne (Vector.toList_inj.mp (List.append_cancel_right he'))
  · exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

theorem tooth_unbound_relabel (m : Frame) (a b : DeploymentId) (hne : a ≠ b)
    (weak : Spec.Bytes → Spec.Bytes) :
    ∃ mac : Spec.Bytes → Spec.Bytes, accepts b mac {m with deployment := b}
      (mac ({m with deployment := a} : Frame).raw) = true ∧ a ≠ b := by
  let mac := fun raw : Spec.Bytes => weak (raw.drop 89)
  refine ⟨mac, ?_, hne⟩
  have skip (id : DeploymentId) : (({m with deployment := id} : Frame).raw).drop 89 = m.payload := by
    simp [Frame.raw, List.drop_append, List.drop_succ_cons]
  simp [accepts, mac, skip]

#tooth_pair foreign_replay_rejected vs tooth_unbound_relabel

/-! A bounded interactive environment sees the tag on each issued frame and the verification
bit on every submission. The challenger exposes a separate function per directional link. -/
inductive WireCode (k : Nat) (R : Type) : Nat → Type 1 where
  | done (r : R) : WireCode k R b
  | tick (next : WireCode k R b) : WireCode k R (b+1)
  | issue (p : Fin k) (m : Frame) (next : Spec.Bytes → WireCode k R b) : WireCode k R (b+1)
  | check (p : Fin k) (m : Frame) (tag : Spec.Bytes) (next : Bool → WireCode k R b) : WireCode k R (b+1)

abbrev History (k : Nat) := List ((Fin k × Frame) × Spec.Bytes)
abbrev Macs (k : Nat) := Fin k → Frame → Spec.Bytes

def issued (hist : History k) (p : Fin k) : List Frame :=
  hist.filterMap fun ((q,m),_) => if q = p then some m else none

def Authentic (f : Macs k) (hist : History k) :=
  ∀ q m t, ((q,m),t) ∈ hist → t = f q m

private theorem auth_cons {f : Macs k} {hist : History k} (h : Authentic f hist) (q m) :
    Authentic f (((q,m),f q m)::hist) := by
  intro r n t hm
  rcases List.mem_cons.mp hm with he | ht
  · cases he; rfl
  · exact h _ _ _ ht

private theorem fresh_of_miss {f : Macs k} {hist : History k} (h : Authentic f hist)
    (p m) (miss : ((p,m),f p m) ∉ hist) : m ∉ issued hist p := by
  intro hm
  obtain ⟨⟨⟨q,n⟩,t⟩, ht, he⟩ := List.mem_filterMap.mp hm
  dsimp only at he
  split at he
  · next eq => subst q; cases he; exact miss (h p _ t ht ▸ ht)
  · cases he

/-- Online execution and its table-only simulation. The latter accepts precisely issued pairs. -/
def run (ideal : Bool) (f : Macs k) : {b : Nat} → WireCode k R b → History k → R
  | _, .done r, _ => r
  | _, .tick next, hist => run ideal f next hist
  | _, .issue p m next, hist => run ideal f (next (f p m)) (((p,m), f p m)::hist)
  | _, .check p m t next, hist =>
    run ideal f (next (if ideal then decide (((p,m),t) ∈ hist) else decide (t = f p m))) hist

def WireCode.map (g : R → S) : {b : Nat} → WireCode k R b → WireCode k S b
  | _, .done r => .done (g r)
  | _, .tick c => .tick (c.map g)
  | _, .issue p m next => .issue p m (fun t => (next t).map g)
  | _, .check p m t next => .check p m t (fun v => (next v).map g)

private theorem run_map (g : R → S) (ideal : Bool) (f : Macs k) (A : WireCode k R b)
    (hist : History k) : run ideal f (A.map g) hist = g (run ideal f A hist) := by
  induction A generalizing hist with
  | done => rfl
  | tick _ ih => exact ih _
  | issue _ _ _ ih => exact ih _ _
  | check _ _ _ _ ih => exact ih _ _

/-- Stop at the guessed submission. All other replies can be simulated from logged tags,
the other independent keys, and the single target tag oracle. -/
def forger (r : Fin k) (other : Macs k) (slot : Nat) (fallback : Frame × Spec.Bytes) :
    {b : Nat} → WireCode k R b → History k → Code (tagIface Frame) (Frame × Spec.Bytes)
  | _, .done _, _ => .ret fallback
  | _, .tick next, hist => forger r other slot fallback next hist
  | _, .issue p m next, hist =>
    if p = r then
      .call m (fun t => forger r other slot fallback (next t) (((p,m),t)::hist))
    else
      let t := other p m
      forger r other slot fallback (next t) (((p,m),t)::hist)
  | b+1, .check p m t next, hist =>
    if p = r ∧ b = slot then .ret (m,t)
    else forger r other slot fallback (next (decide (((p,m),t) ∈ hist))) hist

/-- Local description of the first genuine difference on a prefix. The slot counts down, so
different submissions cannot use the same slot even when the environment branches. -/
inductive Hit (f : Macs k) (r : Fin k) (slot : Nat) :
    {b : Nat} → WireCode k R b → History k → Prop where
  | tick {next hist} : Hit f r slot next hist → Hit f r slot (.tick next) hist
  | here {m t next hist} (valid : t = f r m) (fresh : ((r,m),t) ∉ hist) :
      Hit f r slot (.check (b := slot) r m t next) hist
  | issue {p m next hist} :
      Hit f r slot (next (f p m)) (((p,m), f p m)::hist) →
      Hit f r slot (.issue p m next) hist
  | check {p m t next hist} :
      Hit f r slot (next (decide (((p,m),t) ∈ hist))) hist →
      Hit f r slot (.check p m t next) hist

private theorem hit_lt {f : Macs k} {r s} {A : WireCode k R b} {hist}
    (h : Hit f r s A hist) : s < b := by induction h <;> omega

theorem identical_or_hit (f : Macs k) (A : WireCode k R b) (hist : History k)
    (h : Authentic f hist) :
    run false f A hist = run true f A hist ∨ ∃ r s, Hit f r s A hist := by
  induction A generalizing hist with
  | done => exact .inl rfl
  | tick next ih =>
    rcases ih hist h with he | ⟨r,s,hit⟩
    · exact .inl he
    · exact .inr ⟨r,s,.tick hit⟩
  | issue p m next ih =>
    rcases ih (f p m) _ (auth_cons h p m) with eq | ⟨r,s,hit⟩
    · exact .inl eq
    · exact .inr ⟨r,s,.issue hit⟩
  | @check b p m t next ih =>
    by_cases mem : ((p,m),t) ∈ hist
    · have eq := h p m t mem
      simp only [run, Bool.false_eq_true, ↓reduceIte, decide_eq_true eq, decide_eq_true mem]
      rcases ih true hist h with he | ⟨r,s,hit⟩
      · exact .inl he
      · exact .inr ⟨r,s,.check (by simpa only [decide_eq_true mem] using hit)⟩
    · by_cases eq : t = f p m
      · exact .inr ⟨p,b,.here eq mem⟩
      · simp only [run, Bool.false_eq_true, ↓reduceIte, decide_eq_false eq, decide_eq_false mem]
        rcases ih false hist h with he | ⟨r,s,hit⟩
        · exact .inl he
        · exact .inr ⟨r,s,.check (by simpa only [decide_eq_false mem] using hit)⟩

theorem hit_wins {f : Macs k} {r : Fin k} {s b} {A : WireCode k R b} {hist}
    (hit : Hit f r s A hist) (other : Macs k) (indep : ∀ p, p ≠ r → other p = f p)
    (enc : Frame → Spec.Bytes) (target : Spec.Bytes → Spec.Bytes) (key : ∀ m, target (enc m) = f r m)
    (q : Nat) (fallback : Frame × Spec.Bytes) (log : List Frame)
    (hl : ∀ m, m ∈ log ↔ m ∈ issued hist r) (budget : log.length + b ≤ q)
    (h : Authentic f hist) :
    msgFreshWin enc target
      (Code.play (tagOracle enc target q) (forger r other s fallback A hist) log) = true := by
  induction hit generalizing log with
  | tick hit ih => exact ih log hl (by omega) h
  | @here m t next hist valid fresh =>
    subst t
    simp only [forger, and_self, ↓reduceIte, Code.play_ret, msgFreshWin.public_eqs, key, decide_true,
      Bool.and_true]
    exact decide_eq_true (fun hm => fresh_of_miss h _ _ fresh ((hl _).mp hm))
  | @issue _ p m next hist hit ih =>
    rw [forger]
    split
    · next eq =>
      subst p
      have hq : log.length < q := by omega
      rw [Code.play_call, tagOracle_pos enc target q hq, key]
      exact ih _ (fun x => by simp [issued, hl, or_comm]) (by simp; omega) (auth_cons h _ _)
    · next ne =>
      rw [indep p ne]
      exact ih log (fun x => by simp [issued, ne, hl]) (by omega) (auth_cons h _ _)
  | @check _ p m t next hist hit ih =>
    have lt := hit_lt hit
    rw [forger, ite_eq_right (by omega)]
    exact ih log hl (by omega) h

section Network
variable {F C PK D Sig : Type} [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
variable (dep : AuthDeployment F C PK D Sig)

abbrev StateOf (dep : AuthDeployment F C PK D Sig) := AuthState F PK D Sig dep.core.quorum.numParties
abbrev TurnOf (dep : AuthDeployment F C PK D Sig) := AuthTurn F dep.core.quorum.numParties
abbrev PartyOf (dep : AuthDeployment F C PK D Sig) := Fin dep.core.quorum.numParties

def advance (st : StateOf dep) (t : TurnOf dep) := ((authMachine dep).runStep st t).1

def walInput (p : PartyOf dep) (t : BeltWalTicketSeal) (bs : Spec.Bytes) : Spec.Bytes :=
  encodeMultiFrame [beltLatchWalMacTag.data.toList,
    encodeMultiFrame (beltWalSealTagFields (dep.walKey p.val) (dep.lockSeal p.val) t bs)]

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem wal_bytes {p : PartyOf dep} {s t bs cs}
    (he : walInput dep p s bs = walInput dep p t cs) : bs = cs := by
  obtain ⟨_, inner, _⟩ := List.cons.inj (encodeMultiFrame_injective he) |>.imp_right List.cons.inj
  rw [beltWalSealTagFields.public_eqs, beltWalSealTagFields.public_eqs] at inner
  exact (list6_eq_iff (encodeMultiFrame_injective inner)).2.2.2.2.2

def anchored (p : PartyOf dep) (P : AuthParty F) : Prop :=
  P.anchor = dep.sealTag p.val P.ticket (dep.stateBytes P.latch P.latched)

abbrev WalPair := Spec.Bytes × Spec.Bytes

/-- Concrete challenger output. It contains the actual disk preimage and the currently
anchored preimage and can be checked without interpreting a custody violation. -/
def diskPair (st : StateOf dep) (t : TurnOf dep) : Option WalPair :=
  match t with
  | .crash p =>
    let P := st.parties p
    (unsealBeltWalRecord dep.hash (dep.walKey p.val) (dep.lockSeal p.val) P.disk).map
      fun (ticket,bs) => (walInput dep p ticket bs,
        walInput dep p P.ticket (dep.stateBytes P.latch P.latched))
  | _ => none

def clash (hash : Spec.Bytes → Digest256) (pair : WalPair) : Bool :=
  decide (pair.1 ≠ pair.2 ∧ hash pair.1 = hash pair.2)

def diskBad (st : StateOf dep) (t : TurnOf dep) : Bool :=
  (diskPair dep st t).any (clash dep.hash)

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem intact_recovery (wf : dep.WellFormed) (st : StateOf dep) (p : PartyOf dep)
    (anc : anchored dep p (st.parties p)) (safe : diskBad dep st (.crash p) = false)
    {t l L} (hr : dep.recover p.val (st.parties p).anchor (st.parties p).disk = some (t,l,L)) :
    l = (st.parties p).latch ∧ L = (st.parties p).latched ∧
      (st.parties p).anchor = dep.sealTag p.val t (dep.stateBytes l L) := by
  obtain ⟨bs, hu, ht, hd⟩ := dep.recover_some hr
  let P := st.parties p
  have hashes : dep.hash (walInput dep p t bs) =
      dep.hash (walInput dep p P.ticket (dep.stateBytes P.latch P.latched)) := by
    simpa only [anchored, walInput, AuthDeployment.sealTag.public_eqs, computeBeltWalSealTag.public_eqs] using ht.trans anc
  have no := safe
  simp only [diskBad, diskPair, hu, Option.map_some, Option.any_some, clash] at no
  have he : walInput dep p t bs = walInput dep p P.ticket (dep.stateBytes P.latch P.latched) := by
    by_cases hn : walInput dep p t bs = walInput dep p P.ticket (dep.stateBytes P.latch P.latched)
    · exact hn
    exfalso
    have yes := decide_eq_true (And.intro hn hashes)
    exact Bool.noConfusion (yes.symm.trans no)
  have bytes := wal_bytes dep he
  rw [bytes, wf.parse_stateBytes] at hd
  cases Option.some.inj hd
  exact ⟨rfl, rfl, bytes ▸ ht.symm⟩

private theorem advance_none {st : StateOf dep} {t : TurnOf dep} (h : authStep dep st t = none) :
    advance dep st t = st := by
  unfold advance Machine.runStep
  simp only [authMachine.public_eqs, h]

private theorem advance_some {st : StateOf dep} {t : TurnOf dep} {s o}
    (h : authStep dep st t = some (s,o)) : advance dep st t = s := by
  unfold advance Machine.runStep
  simp only [authMachine.public_eqs, h]

/-- On a collision-free turn, every old approval persists and every new anchor is consistent. -/
private theorem step_logs (wf : dep.WellFormed) (st : StateOf dep) (t : TurnOf dep)
    (anc : ∀ p, anchored dep p (st.parties p)) (hc : diskBad dep st t = false) :
    ∀ p, anchored dep p ((advance dep st t).parties p) ∧
      (st.parties p).latched ⊆ ((advance dep st t).parties p).latched := by
  intro p
  cases he : authStep dep st t with
  | none => rw [advance_none dep he]; exact ⟨anc _, fun _ h => h⟩
  | some pair =>
    obtain ⟨s,o⟩ := pair
    rw [advance_some dep he]
    cases t with
    | approve q d i =>
      simp only [authStep.public_eqs] at he
      split at he <;> cases he
      by_cases eq : p = q
      · subst p
        simp only [setParty, ↓reduceIte]
        simp only [anchored, AuthDeployment.approveParty.public_eqs]
        exact ⟨trivial, fun _ h => List.mem_cons_of_mem _ h⟩
      · simpa only [setParty, eq, ↓reduceIte] using And.intro (anc p) (List.Subset.refl _)
    | crash q =>
      simp only [authStep.public_eqs] at he
      cases he
      by_cases eq : p = q
      · subst p
        simp only [setParty, ↓reduceIte, AuthDeployment.crashParty.public_eqs]
        cases hr : dep.recover q.val (st.parties q).anchor (st.parties q).disk with
        | some r =>
          obtain ⟨t,l,L⟩ := r
          obtain ⟨hl,hL,ha⟩ := intact_recovery dep wf st q (anc q) hc hr
          exact ⟨ha, hL ▸ List.Subset.refl _⟩
        | none => exact ⟨anc _, List.Subset.refl _⟩
      · simpa only [setParty, eq, ↓reduceIte] using And.intro (anc p) (List.Subset.refl _)
    | tamperDisk q raw =>
      simp only [authStep.public_eqs] at he
      cases he
      by_cases eq : p = q
      · subst p; simp only [setParty, ↓reduceIte]; exact ⟨anc _, List.Subset.refl _⟩
      · simpa only [setParty, eq, ↓reduceIte] using And.intro (anc p) (List.Subset.refl _)
    | execute d ps i abort =>
      simp only [authStep.public_eqs, Option.map_eq_some_iff] at he
      obtain ⟨_,_,e⟩ := he
      cases e
      exact ⟨anc _, List.Subset.refl _⟩
    | dropMsg => simp only [authStep.public_eqs] at he; cases he; exact ⟨anc _, List.Subset.refl _⟩
    | inject | deliver | corrupt =>
      simp only [authStep.public_eqs] at he
      split at he <;> cases he
      exact ⟨anc _, List.Subset.refl _⟩

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem crash_clean (wf : dep.WellFormed) (st : StateOf dep) (p : PartyOf dep)
    (anc : ∀ q, anchored dep q (st.parties q)) (hc : diskBad dep st (.crash p) = false) :
    authViolation dep st (.crash p) = false := by
  simp only [authViolation.public_eqs]
  cases hr : dep.recover p.val (st.parties p).anchor (st.parties p).disk with
  | some r =>
    obtain ⟨t,l,L⟩ := r
    obtain ⟨hl,hL,_⟩ := intact_recovery dep wf st p (anc p) hc hr
    simp [hl,hL]
  | none => rfl

/-- All ordinary machine turns except delivery in an honest sender's name. The latter
enters through the authenticated receive port below. Corrupt injection remains available. -/
def localTurn : TurnOf dep → Bool
  | .deliver _ => false
  | _ => true

abbrev Decoder (dep : AuthDeployment F C PK D Sig) := PartyOf dep → Frame → Option (AuthAck F)

/-- Read the decoded acknowledgment only on its own link and deployment. -/
def readAck (id : DeploymentId) (decode : Decoder dep) (p : PartyOf dep) (m : Frame) :=
  if m.deployment = id then (decode p m).filter (fun a => decide (a.sender = p.val)) else none

def entitled (id : DeploymentId) (decode : Decoder dep) (st : StateOf dep) (p : PartyOf dep)
    (m : Frame) : Prop :=
  ∀ a, readAck dep id decode p m = some a → a.intent ∈ (st.parties p).latched

/-- Local steps expose their actual state to the continuation. A holder may request
authentication of any already latched approval, and arbitrary foreign-domain frames.
Network submissions need no proof of provenance. -/
inductive Client (id : DeploymentId) (decode : Decoder dep) : StateOf dep → Nat → Type 1 where
  | done : Client id decode st b
  | step (t : TurnOf dep) (allowed : localTurn dep t = true)
      (next : Client id decode (advance dep st t) b) : Client id decode st (b+1)
  | seal (p : PartyOf dep) (m : Frame) (allowed : entitled dep id decode st p m)
      (next : Spec.Bytes → Client id decode st b) : Client id decode st (b+1)
  | idle (next : Client id decode st b) : Client id decode st (b+1)
  | receive (p : PartyOf dep) (m : Frame) (tag : Spec.Bytes) (a : AuthAck F)
      (decoded : readAck dep id decode p m = some a)
      (accept : Client id decode (advance dep st (.deliver a)) b)
      (reject : Client id decode st b) : Client id decode st (b+1)

/-- Unrestricted submission interface. Malformed, misrouted and foreign frames are refused. -/
def ingress {id decode st b} (p : PartyOf dep) (m : Frame) (tag : Spec.Bytes)
    (pass : (a : AuthAck F) → Client dep id decode (advance dep st (.deliver a)) b)
    (fail : Client dep id decode st b) : Client dep id decode st (b+1) :=
  match hr : readAck dep id decode p m with
  | none => .idle fail
  | some a => .receive p m tag a hr (pass a) fail

/-- Endpoint-side signing request. The executable gate looks up the decoded intent in the
sender's own current WAL-backed log. A rejected request consumes one action. -/
def sealRequest {id decode st b} (p : PartyOf dep) (m : Frame)
    (ok : Spec.Bytes → Client dep id decode st b) (fail : Client dep id decode st b) :
    Client dep id decode st (b+1) :=
  match hr : readAck dep id decode p m with
  | none => .seal p m (fun _ h => by rw [hr] at h; cases h) ok
  | some a =>
    if h : a.intent ∈ (st.parties p).latched then
      .seal p m (fun _ he => by rw [hr] at he; cases he; exact h) ok
    else .idle fail

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem read_foreign {id decode} {m : Frame} (hne : m.deployment ≠ id) (p : PartyOf dep) :
    readAck dep id decode p m = none := by simp [readAck, hne]

theorem ingress_foreign_refused {id decode st b} (p : PartyOf dep) (m : Frame) (tag : Spec.Bytes)
    (hne : m.deployment ≠ id)
    (pass : (a : AuthAck F) → Client dep id decode (advance dep st (.deliver a)) b)
    (fail : Client dep id decode st b) :
    ingress dep p m tag pass fail = .idle fail := by
  unfold ingress
  split
  · rfl
  · next _ he => rw [read_foreign dep hne p] at he; cases he

def network {id decode st} : {b : Nat} → Client dep id decode st b →
    WireCode dep.core.quorum.numParties (List (TurnOf dep)) b
  | _, .done => .done []
  | _, .step t _ next => .tick ((network next).map (t :: ·))
  | _, .seal p m _ next => .issue p m (fun tag => network (next tag))
  | _, .idle next => .tick (network next)
  | _, .receive p m tag a _ pass fail => .check p m tag (fun valid =>
      if valid then (network pass).map (.deliver a :: ·) else network fail)

/-- An accepted approval, issuance of its signed frame, and verified redelivery take the
ordinary machine path. The authorization tested by sealRequest follows from authStep. -/
theorem approve_seal_deliver {id decode} (st : StateOf dep) (p : PartyOf dep)
    (i : CustodyIntent) (m : Frame)
    (acceptsApproval : p.val ∉ st.corrupt ∧ (st.parties p).latch ≤ i.epoch ∧
      i.sessionId ∉ (st.parties p).coupons ∧ (st.parties p).poisoned = false)
    (decodes : readAck dep id decode p m =
      some (dep.approveAck p.val dep.core.deploymentId i (st.parties p)))
    (f : Macs dep.core.quorum.numParties) :
    let d := dep.core.deploymentId
    let A : Client dep id decode st 3 := .step (.approve p d i) (by simp [localTurn])
      (sealRequest dep p m (fun tag => ingress dep p m tag (fun _ => .done) .done) .done)
    run false f (network dep A) [] =
      [.approve p d i, .deliver (dep.approveAck p.val d i (st.parties p))] := by
  let t : TurnOf dep := .approve p dep.core.deploymentId i
  let a := dep.approveAck p.val dep.core.deploymentId i (st.parties p)
  have he : authStep dep st t = some
      ({st with parties := setParty st.parties p (dep.approveParty p.val i (st.parties p)),
                wire := a :: st.wire}, .approved a) := by
    simp [t,authStep.public_eqs,a,acceptsApproval.1,acceptsApproval.2.1,acceptsApproval.2.2.1,acceptsApproval.2.2.2]
  have latched : a.intent ∈ ((advance dep st t).parties p).latched := by
    rw [advance_some dep he]
    simp only [setParty,↓reduceIte,AuthDeployment.approveParty.public_eqs,a,AuthDeployment.approveAck.public_eqs,
      List.mem_cons_self]
  dsimp only
  simp only [network, run, run_map]
  unfold sealRequest
  split
  · next _ h => rw [decodes] at h; cases h
  · next a' h =>
    rw [decodes] at h
    cases h
    dsimp only [a,t] at latched
    simp only [dite_eq_left latched]
    simp only [network,run]
    unfold ingress
    split
    · next _ h => rw [decodes] at h; cases h
    · next a' h =>
      rw [decodes] at h
      cases h
      simp only [network,run,run_map,↓reduceIte,Bool.false_eq_true,decide_true]

omit [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem local_clean (wf : dep.WellFormed) (st : StateOf dep) (t : TurnOf dep)
    (ht : localTurn dep t = true) (ha : ∀ p, anchored dep p (st.parties p))
    (hc : diskBad dep st t = false) : authViolation dep st t = false := by
  cases t with
  | deliver => cases ht
  | crash p => exact crash_clean dep wf st p ha hc
  | _ => simp only [authViolation.public_eqs]

omit [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D] in
private theorem delivered_clean {id decode} {p : PartyOf dep} {m : Frame} {a : AuthAck F}
    (st : StateOf dep) (hr : readAck dep id decode p m = some a)
    (h : entitled dep id decode st p m) : authViolation dep st (.deliver a) = false := by
  have hs : a.sender = p.val := by
    unfold readAck at hr
    split at hr
    · exact of_decide_eq_true (Option.filter_eq_some_iff.mp hr).2
    · cases hr
  have hm : a.intent ∈ st.latchedOf a.sender := by
    simpa only [hs, AuthState.latchedOf.public_eqs, dite_eq_left p.isLt] using h a hr
  simp [authViolation.public_eqs, hm]

abbrev Backed {id : DeploymentId} (decode : Decoder dep) (st : StateOf dep)
    (hist : History dep.core.quorum.numParties) :=
  ∀ p m t, ((p,m),t) ∈ hist → entitled dep id decode st p m

private theorem backed_step {id decode st hist} (t : TurnOf dep)
    (h : Backed dep (id := id) decode st hist)
    (logs : ∀ p, (st.parties p).latched ⊆ ((advance dep st t).parties p).latched) :
    Backed dep (id := id) decode (advance dep st t) hist :=
  fun p m tag hm a hr => logs p (h p m tag hm a hr)

private theorem clean_cons {st : StateOf dep} {t ts} {ev}
    (hc : (authRun dep ev st (t::ts)).2 = false) :
    ev st t = false ∧ (authRun dep ev (advance dep st t) ts).2 = false :=
  Bool.or_eq_false_iff.mp (by simpa only [advance, authRun.public_eq_2] using hc)

/-- The replay-table world forces every delivery to be backed by the actual persistent
approval log, until a pair of unequal WAL inputs hashes to the same anchor. -/
theorem table_run_clean (wf : dep.WellFormed) {id decode st} (A : Client dep id decode st b)
    (f : Macs dep.core.quorum.numParties) (hist : History dep.core.quorum.numParties)
    (ha : ∀ p, anchored dep p (st.parties p)) (hb : Backed dep (id := id) decode st hist)
    (hc : (authRun dep (diskBad dep) st (run true f (network dep A) hist)).2 = false) :
    (authRun dep (authViolation dep) st (run true f (network dep A) hist)).2 = false := by
  induction A generalizing hist with
  | done => simp only [network, run, authRun.public_eq_1]
  | @step st b t ht next ih =>
    simp only [network, run, run_map] at hc ⊢
    obtain ⟨hc,rest⟩ := clean_cons dep hc
    have laws := step_logs dep wf st t ha hc
    rw [authRun.public_eq_2]
    exact Bool.or_eq_false_iff.mpr ⟨local_clean dep wf st t ht ha hc,
      ih _ (fun p => (laws p).1) (backed_step dep t hb (fun p => (laws p).2)) rest⟩
  | «seal» p m allow next ih =>
    apply ih _ _ ha _ hc
    intro r n tag hm
    rcases List.mem_cons.mp hm with he | ht
    · cases he; exact allow
    · exact hb _ _ _ ht
  | idle next ih => exact ih hist ha hb hc
  | @receive st b p m tag a hr pass fail ihP ihF =>
    by_cases mem : ((p,m),tag) ∈ hist
    · have eq : run true f (network dep (.receive p m tag a hr pass fail)) hist =
          .deliver a :: run true f (network dep pass) hist := by
        change run true f (if decide (((p,m),tag) ∈ hist) then _ else _) hist = _
        rw [decide_eq_true mem]
        exact run_map .. 
      rw [eq] at hc ⊢
      obtain ⟨localSafe,rest⟩ := clean_cons dep hc
      have laws := step_logs dep wf st (.deliver a) ha localSafe
      rw [authRun.public_eq_2]
      exact Bool.or_eq_false_iff.mpr ⟨delivered_clean dep st hr (hb _ _ _ mem),
        ihP _ (fun p => (laws p).1) (backed_step dep _ hb (fun p => (laws p).2)) rest⟩
    · have eq : run true f (network dep (.receive p m tag a hr pass fail)) hist =
          run true f (network dep fail) hist := by
        change run true f (if decide (((p,m),tag) ∈ hist) then _ else _) hist = _
        rw [decide_eq_false mem]
        rfl
      rw [eq] at hc ⊢
      exact ihF hist ha hb hc

/-- Output actual byte strings for the WAL collision experiment on a schedule. -/
def walExtract (st : StateOf dep) : List (TurnOf dep) → WalPair
  | [] => ([],[])
  | t::ts => if diskBad dep st t then (diskPair dep st t).getD ([],[])
             else walExtract (advance dep st t) ts

theorem walExtract_correct (ts : List (TurnOf dep)) (st : StateOf dep) :
    clash dep.hash (walExtract dep st ts) = (authRun dep (diskBad dep) st ts).2 := by
  induction ts generalizing st with
  | nil => simp [clash, walExtract, authRun.public_eqs]
  | cons t ts ih =>
    simp only [walExtract, authRun.public_eqs]
    split
    · next h =>
      rw [h, Bool.true_or]
      unfold diskBad at h
      cases he : diskPair dep st t <;> simp_all
    · next h =>
      simp only [Bool.not_eq_true] at h
      rw [h, Bool.false_or]
      exact ih _

end Network
/-- The only sampled secrets used by the outer-frame verifier are the link keys. Each
challenger split also supplies the comparison random function of the PRF game. -/
structure LinkGame (N k : Nat) where
  positive : 0 < N
  nC : Fin k → Nat
  nA : Fin k → Nat
  split : (p : Fin k) → CoinSplit N (nC p) (nA p)
  sample : (p : Fin k) → Fin (nC p) → Spec.Bytes × (Spec.Bytes → Spec.Bytes)
  digest : Spec.Bytes → Spec.Bytes
  prf : Spec.Bytes → Spec.Bytes → Spec.Bytes

namespace LinkGame
variable (G : LinkGame N k)
def enc (m : Frame) := G.digest m.raw
def keyed (ω : Fin N) (r : Fin k) := G.prf (G.sample r ((G.split r).chal ω)).1
def functions (ω : Fin N) : Macs k := fun p m => G.keyed ω p (G.enc m)

def rep (p : Fin k) (a : Fin (G.nA p)) :=
  (G.split p).pair ((G.split p).chal ⟨0,G.positive⟩) a

def Independent (A : Fin N → WireCode k R b) : Prop :=
  ∀ r i j, (G.split r).advc i = (G.split r).advc j →
    A i = A j ∧ ∀ p, p ≠ r → G.functions i p = G.functions j p

private def defaultFrame : Frame := ⟨Vector.replicate _ 0, 0, Vector.replicate _ 0, []⟩

def reduction (A : Fin N → WireCode k R b) (r : Fin k) (s : Fin b) (a : Fin (G.nA r)) :=
  forger r (G.functions (G.rep r a)) s.val (defaultFrame,[]) (A (G.rep r a)) []

def forgeGame (A : Fin N → WireCode k R b) (r : Fin k) (s : Fin b) : FinGame N :=
  eufCmaTagGame G.positive G.enc b (fun ω => G.keyed ω r)
    (fun ω => G.reduction A r s ((G.split r).advc ω))

theorem extract (A : Fin N → WireCode k R b) (indep : G.Independent A) (ω : Fin N) :
    run false (G.functions ω) (A ω) [] = run true (G.functions ω) (A ω) [] ∨
      ∃ r s, (G.forgeGame A r s).win ω = true := by
  rcases identical_or_hit _ (A ω) [] (fun _ _ _ h => nomatch h) with eq | ⟨r,s,hit⟩
  · exact .inl eq
  · let slot : Fin b := ⟨s,hit_lt hit⟩
    right
    refine ⟨r,slot,?_⟩
    obtain ⟨program,keys⟩ := indep r (G.rep r ((G.split r).advc ω)) ω ((G.split r).advc_pair ..)
    simp only [forgeGame, eufCmaTagGame.public_eqs, tagRun.public_eqs]
    change msgFreshWin G.enc (G.keyed ω r)
      (Code.play _ (forger r _ s _ (A (G.rep r ((G.split r).advc ω))) []) []) = true
    rw [program]
    exact hit_wins hit _ keys _ _ (fun _ => rfl) _ _ [] (fun _ => Iff.rfl)
      (by simp) (fun _ _ _ h => nomatch h)

/-- Primitive budgets for the specific, constructed query algorithms. -/
structure Hard (A : Fin N → WireCode k R b) (keyLen inLen outLen : Nat)
    (εPrf εDigest : Spec.RatBound) (classify : Code byteOracleIface Bool → Prop) : Prop where
  length : ∀ m, (G.enc m).length = inLen
  uniform : ∀ r, UniformOn (PrfSampleOk keyLen inLen outLen) (G.sample r)
  prfHard : PrfHard classify G.prf keyLen inLen outLen (b+1) εPrf
  member : ∀ r s a, classify (tagForgeDistinguisher G.enc b inLen (G.reduction A r s a))
  collision : ∀ r s, GameBound
    (encCollisionGame G.positive G.enc b (fun ω => G.keyed ω r)
      (fun ω => G.reduction A r s ((G.split r).advc ω))).winProb εDigest

theorem frame_collision_witness (out : (Frame × Spec.Bytes) × List Frame)
    (hit : encCollision G.enc out = true) : Nonempty (HashCollision G.digest) := by
  rw [encCollision.public_eqs] at hit
  obtain ⟨m,_,hm⟩ := List.any_eq_true.mp hit
  obtain ⟨hn,he⟩ := Bool.and_eq_true_iff.mp hm
  exact ⟨⟨m.raw, out.1.1.raw, fun eq => of_decide_eq_true hn (Frame.raw_injective eq),
    of_decide_eq_true he⟩⟩

theorem forgery_bound (A : Fin N → WireCode k R b) {classify keyLen inLen outLen εPrf εDigest}
    (hard : G.Hard A keyLen inLen outLen εPrf εDigest classify) (r s) :
    GameBound (G.forgeGame A r s).winProb ((εPrf.add (tagGuessBound outLen)).add εDigest) :=
  GameBound.trans (eufCmaTag_forgery_bound G.positive G.enc b inLen hard.length G.prf keyLen outLen
    hard.prfHard (G.split r) (G.sample r) (hard.uniform r) (G.reduction A r s) (hard.member r s))
    (Spec.RatBound.add_le_add (Spec.RatBound.le_refl _) (hard.collision r s))

end LinkGame

section Probability
variable {F C PK D Sig : Type} [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
variable (dep : AuthDeployment F C PK D Sig) {id : DeploymentId} {decode : Decoder dep}
variable (G : LinkGame N dep.core.quorum.numParties)
variable (client : Fin N → Client dep id decode (AuthState.init dep) b)

def schedule (ideal : Bool) (ω : Fin N) :=
  run ideal (G.functions ω) (network dep (client ω)) []

def unsafeGame : FinGame N :=
  ⟨G.positive, fun ω => authUnsafeRelease dep (authRun dep (authViolation dep) (AuthState.init dep)
    (schedule dep G client false ω)).1⟩

def walCollisionGame : FinGame N :=
  ⟨G.positive, fun ω => clash dep.hash (walExtract dep (AuthState.init dep)
    (schedule dep G client true ω))⟩

theorem distributed_authRun_adaptive_unsafe_release_bound
    (wf : dep.WellFormed) {classify keyLen inLen outLen εPrf εDigest εWal}
    (indep : G.Independent (fun ω => network dep (client ω)))
    (hard : G.Hard (fun ω => network dep (client ω)) keyLen inLen outLen εPrf εDigest classify)
    (wal : GameBound (walCollisionGame dep G client).winProb εWal) :
    GameBound (unsafeGame dep G client).winProb
      ((((εPrf.add (tagGuessBound outLen)).add εDigest).scale
        (dep.core.quorum.numParties * b)).add εWal) := by
  let A := fun ω => network dep (client ω)
  let split := CoinSplit.prod dep.core.quorum.numParties b
  let breaks := fun j => G.forgeGame A (split.chal j) (split.advc j)
  let anyBreak : FinGame N := ⟨G.positive, fun ω =>
    (List.finRange (dep.core.quorum.numParties * b)).any (fun j => (breaks j).win ω)⟩
  apply GameBound.trans (event_le_two_reductions _ anyBreak (walCollisionGame dep G client) ?_)
  · exact Spec.RatBound.add_le_add (event_le_family_reductions anyBreak breaks
      (fun _ h => by obtain ⟨j,_,hj⟩ := List.any_eq_true.mp h; exact ⟨j,hj⟩)
      (fun j => G.forgery_bound A hard (split.chal j) (split.advc j))) wal
  · intro ω win
    rcases G.extract A indep ω with eq | ⟨r,s,hit⟩
    · right
      change schedule dep G client false ω = schedule dep G client true ω at eq
      change authUnsafeRelease dep (authRun dep _ _ (schedule dep G client false ω)).1 = true at win
      rw [eq] at win
      have violation := authRun_unsafe_release_violation dep wf _ win
      change clash _ (walExtract dep _ _) = true
      rw [walExtract_correct]
      cases he : (authRun dep (diskBad dep) (AuthState.init dep) (schedule dep G client true ω)).2 with
      | true => rfl
      | false =>
        have clean := table_run_clean dep wf (client ω) (G.functions ω) []
          (fun _ => by simp only [anchored, AuthState.init.public_eqs]) (fun _ _ _ h => nomatch h) he
        exact Bool.noConfusion (violation.symm.trans clean)
    · left
      apply List.any_eq_true.mpr
      exact ⟨split.pair r s, List.mem_finRange _, by
        simpa only [breaks, split.chal_pair, split.advc_pair] using hit⟩

end Probability
#verify_constructive table_run_clean LinkGame.extract distributed_authRun_adaptive_unsafe_release_bound
#print axioms approve_seal_deliver
#print axioms ingress_foreign_refused
#print axioms table_run_clean
#print axioms LinkGame.extract
#print axioms LinkGame.forgery_bound
#print axioms network
#print axioms LinkGame.frame_collision_witness
#print axioms distributed_authRun_adaptive_unsafe_release_bound
#print axioms foreign_replay_rejected
#print axioms relabel_requires_collision
#print axioms walExtract_correct
end Qsag.DistributedAuthRun
