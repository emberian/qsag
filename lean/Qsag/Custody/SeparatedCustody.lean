module
public import Qsag.Protocol.Signing.HypertreeEufCma
public import Qsag.Protocol.Threshold.MaliciousSecurity
public import Qsag.Custody.CustodySuiteFull
public import Qsag.Protocol.Signing.ProdCollision
import Qsag.Tactic.AssuranceKit

/-! Spec-level custody approvals. This is NOT a threshold reconstruction of a signing key.
Each custodian has its own production Jorts key. The spine composes their approvals.
No public linear map is treated as a signature and no secrecy theorem is assumed.
The signer is partial: exhausted grinding burns its leaf without releasing a signature.
-/
public section
namespace Qsag.Custody
set_option autoImplicit false
set_option maxRecDepth 4096

structure Intent where
  session : Nat
  round : Nat
  leaf : Nat
  spend : Nat
  message : List UInt8
  deriving DecidableEq, Repr

/-- The signed approval bytes. The deployment identifier is framed first, so an approval is a
statement about one deployment. Unbounded integers use canonical LEB128, not truncating machine
casts. -/
def payload (deploymentId party : Nat) (r : Intent) : List UInt8 :=
  encodeMultiFrame ["QSAG.CUSTODY.APPROVAL/v3".toUTF8.toList, leb128 deploymentId, leb128 party,
    leb128 r.session, leb128 r.round, leb128 r.leaf, leb128 r.spend, r.message]

private theorem leb_inj {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (show leb128 a ++ [] = leb128 b ++ [] by simpa using h)).1

theorem payload_injective {d d' i j : Nat} {r s : Intent}
    (h : payload d i r = payload d' j s) : d = d' ∧ i = j ∧ r = s := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  have hd := leb_inj hf.2.1
  have hi := leb_inj hf.2.2.1
  have hs := leb_inj hf.2.2.2.1
  have hr := leb_inj hf.2.2.2.2.1
  have hl := leb_inj hf.2.2.2.2.2.1
  have hv := leb_inj hf.2.2.2.2.2.2.1
  have hm := hf.2.2.2.2.2.2.2.1
  refine ⟨hd, hi, ?_⟩
  cases r; cases s
  simp_all only

/-- Approval bytes of two different deployments never coincide, whatever the party and intent. -/
theorem payload_ne_of_deployment_ne {d d' : Nat} (hne : d ≠ d') (i j : Nat) (r s : Intent) :
    payload d i r ≠ payload d' j s :=
  fun h => hne (payload_injective h).1

structure SigningConfig where
  suite : TweakableHashSuite
  params : PqHashParams
  randomness : List UInt8
  grindLimit : Nat

def query (cfg : SigningConfig) (dep party : Nat) (r : Intent) : ProdSigningQuery :=
  ⟨payload dep party r, cfg.randomness, r.leaf, cfg.grindLimit⟩

/-- The actual production specification, including its self-verification. -/
def sign (cfg : SigningConfig) (sk : PqSecretKey) (dep party : Nat) (r : Intent) :
    Option PqHashSig :=
  evalProductionStatefulSign cfg.suite cfg.params sk (payload dep party r)
    cfg.randomness r.leaf cfg.grindLimit

def verify (cfg : SigningConfig) (pk : PqPublicKey) (dep party : Nat)
    (r : Intent) (sig : PqHashSig) : Bool :=
  verifyProductionPqHashSig cfg.suite cfg.params pk (payload dep party r) sig

theorem sign_verifies (cfg : SigningConfig) (sk : PqSecretKey) (dep party : Nat)
    (r : Intent) (sig : PqHashSig) (h : sign cfg sk dep party r = some sig) :
    verify cfg (derivePublicKey cfg.suite cfg.params sk) dep party r sig = true :=
  verifyProductionPqHashSig_evalProductionStatefulSign _ _ _ _ _ _ _ _ h

theorem sign_eq_query (cfg : SigningConfig) (sk : PqSecretKey) (dep party : Nat)
    (r : Intent) (hs : cfg.params.statefulJorts = true) :
    sign cfg sk dep party r = prodSignQuery cfg.suite cfg.params sk (query cfg dep party r) := by
  simp only [prodSignQuery_eq, hs, ↓reduceIte, query, sign]

structure RoundOpening where
  session : Nat
  round : Nat
  opening : BdozPairOpening

/-- Pads are addressed by the full session/round. Independence and erasure of
these pads are implementation obligations; this type does not assert them. -/
structure RoundPolicy where
  keys : Nat → Nat → BdozVerifierKeys
  roster : List Nat
  digest : Nat → List UInt8

def roundDomain : List UInt8 := "QSAG.CUSTODY.ROUND1/v2".toUTF8.toList

/-- The committed round binds the deployment and the entire intent before any permit is minted. -/
def roundCommitment (dep : Nat) (r : Intent) : List UInt8 :=
  cshake256Bytes roundDomain (payload dep 0 r)

def checkRound (p : RoundPolicy) (dep : Nat) (r : Intent) (digest : List UInt8)
    (ops : List RoundOpening) : Bool :=
  decide (digest.length = 32 ∧ digest = p.digest r.session ∧ digest = roundCommitment dep r) &&
  decide (ops ≠ [] ∧ ops.map (fun o => o.opening.partyId) = p.roster ∧ p.roster.Nodup) &&
  ops.all (fun o => decide (o.session = r.session ∧ o.round = r.round) &&
    verifyBdozPairMac (p.keys r.session r.round) o.opening)

theorem checkRound_commitment (p : RoundPolicy) (dep : Nat) (r : Intent) (digest : List UInt8)
    (ops : List RoundOpening) (h : checkRound p dep r digest ops = true) :
    digest = roundCommitment dep r :=
  (of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).2.2

/-- Reusing a committed round for another intent supplies a concrete pair of
different cSHAKE inputs with equal output. No collision-freedom axiom is used. -/
theorem accepted_round_context_or_collision (p : RoundPolicy) (dep : Nat) (r s : Intent)
    (digest : List UInt8) (ops ops' : List RoundOpening)
    (hr : checkRound p dep r digest ops = true) (hs : checkRound p dep s digest ops' = true) :
    r = s ∨ (payload dep 0 r ≠ payload dep 0 s ∧
      cshake256Bytes roundDomain (payload dep 0 r) =
        cshake256Bytes roundDomain (payload dep 0 s)) := by
  by_cases he : r = s
  · exact .inl he
  · exact .inr ⟨(fun hp => he (payload_injective hp).2.2),
      (checkRound_commitment p dep r digest ops hr).symm.trans
        (checkRound_commitment p dep s digest ops' hs)⟩

/-- One committed round digest accepted under two different deployments, by any two round
policies and for any two intents, is a cSHAKE collision on two different inputs. -/
theorem accepted_round_cross_deployment_collision (p p' : RoundPolicy) (d d' : Nat)
    (r s : Intent) (digest : List UInt8) (ops ops' : List RoundOpening) (hne : d ≠ d')
    (hr : checkRound p d r digest ops = true) (hs : checkRound p' d' s digest ops' = true) :
    payload d 0 r ≠ payload d' 0 s ∧
      cshake256Bytes roundDomain (payload d 0 r) =
        cshake256Bytes roundDomain (payload d' 0 s) :=
  ⟨payload_ne_of_deployment_ne hne 0 0 r s,
    (checkRound_commitment p d r digest ops hr).symm.trans
      (checkRound_commitment p' d' s digest ops' hs)⟩

theorem checkRound_opening (p : RoundPolicy) (dep : Nat) (r : Intent) (digest : List UInt8)
    (ops : List RoundOpening) (o : RoundOpening) (hm : o ∈ ops)
    (h : checkRound p dep r digest ops = true) :
    (o.session = r.session ∧ o.round = r.round) ∧
      verifyBdozPairMac (p.keys r.session r.round) o.opening = true := by
  have ha := (Bool.and_eq_true_iff.mp h).2
  have ho := List.all_eq_true.mp ha o hm
  exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp ho).1,
    (Bool.and_eq_true_iff.mp ho).2⟩

theorem checkRound_wrong_session (p : RoundPolicy) (dep : Nat) (r : Intent) (digest : List UInt8)
    (ops : List RoundOpening) (o : RoundOpening) (hm : o ∈ ops)
    (hne : o.session ≠ r.session) : checkRound p dep r digest ops = false := by
  cases h : checkRound p dep r digest ops
  · rfl
  · exact False.elim (hne (checkRound_opening p dep r digest ops o hm h).1.1)

/-- A changed accepted share is tied to the existing two-lane key-recovery
reduction, not declared authentic by a caller-supplied judgement. -/
theorem checkRound_changed_share (p : RoundPolicy) (dep : Nat) (r : Intent) (digest : List UInt8)
    (ops : List RoundOpening) (o : RoundOpening) (hon : BdozPairOpening)
    (hm : o ∈ ops) (h : checkRound p dep r digest ops = true)
    (hslot : hon.partyId = o.opening.partyId) (hne : hon.shareX ≠ o.opening.shareX)
    (hh : verifyBdozPairMac (p.keys r.session r.round) hon = true) :
    BdozMacForgeryWitness (p.keys r.session r.round) hon o.opening :=
  ⟨hslot, hne, hh, (checkRound_opening p dep r digest ops o hm h).2⟩

/-- All verification keys are public. Custodian secret keys remain in separate
local states; there is no reconstructed master secret in the coordinator. -/
structure Certificate where
  party : Nat
  intent : Intent
  signature : PqHashSig

/-- A certificate carries no deployment field: the verifier supplies its own deployment, and the
signature is checked on the approval bytes of that deployment. -/
def verifyCertificate (cfg : SigningConfig) (pks : Nat → PqPublicKey) (dep : Nat)
    (expected : Intent) (c : Certificate) : Bool :=
  decide (c.intent = expected) && verify cfg (pks c.party) dep c.party c.intent c.signature

theorem certificate_wrong_session (cfg : SigningConfig) (pks : Nat → PqPublicKey) (dep : Nat)
    (r : Intent) (c : Certificate) (hne : c.intent.session ≠ r.session) :
    verifyCertificate cfg pks dep r c = false := by
  have hn : c.intent ≠ r := fun he => hne (congrArg Intent.session he)
  simp [verifyCertificate, hn]

theorem certificate_invalid_rejected (cfg : SigningConfig) (pks : Nat → PqPublicKey) (dep : Nat)
    (r : Intent) (c : Certificate)
    (h : verify cfg (pks c.party) dep c.party c.intent c.signature = false) :
    verifyCertificate cfg pks dep r c = false := by
  simp only [verifyCertificate, h, Bool.and_false]

end Qsag.Custody
end
set_option maxRecDepth 4096
#verify_constructive Qsag.Custody.payload_injective
#verify_constructive Qsag.Custody.sign_verifies
#verify_constructive Qsag.Custody.checkRound_changed_share
#verify_constructive Qsag.Custody.certificate_wrong_session
#verify_constructive Qsag.Custody.accepted_round_context_or_collision
#verify_constructive Qsag.Custody.payload_ne_of_deployment_ne
#verify_constructive Qsag.Custody.accepted_round_cross_deployment_collision

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

/-- Immutable namespace of one custodian vault: the deployment it serves, the custodian's party
index, and an identifier of the signing key it guards. No transition changes it. -/
structure VaultIdentity where
  deploymentId : Nat
  party : Nat
  keyId : List UInt8
  deriving DecidableEq, Repr

/-- Key identity of a separated-custody custodian: an injective framing of its public key. -/
def publicKeyId (pk : PqPublicKey) : List UInt8 :=
  encodeMultiFrame ["QSAG.CUSTODY.KEYID/v1".toUTF8.toList, pk.pkSeed, pk.pkRoot]

theorem publicKeyId_injective :
    ∀ {a b : PqPublicKey}, publicKeyId a = publicKeyId b → a = b
  | ⟨s, r⟩, ⟨s', r'⟩, h => by
    have hf := encodeMultiFrame_injective h
    simp only [List.cons.injEq] at hf
    obtain ⟨_, hs, hr, _⟩ := hf
    subst hs
    subst hr
    rfl

/-- The vault is indexed by its identity. Grants (`active`) and the durable ledger live inside
one identity and are never moved to another. -/
structure Vault where
  identity : VaultIdentity
  durable : Ledger := {}
  active : Option Intent := none
  attempted : List Intent := []
  poisoned : Bool := false

def initial (id : VaultIdentity) : Vault := { identity := id }

/-- The round is checked against the commitment of the vault's own deployment. -/
def mintGuard (p : RoundPolicy) (cap : Nat) (v : Vault) (b : Burn) : Bool :=
  decide (v.durable.nextLeaf ≤ b.intent.leaf ∧ b.intent.round = v.durable.nextRound ∧
    v.durable.spent + b.intent.spend ≤ cap ∧
    b.intent.session ∉ v.durable.burned.map (fun x => x.intent.session) ∧
    b.intent.message ≠ []) &&
    checkRound p v.identity.deploymentId b.intent b.digest b.openings

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

/-- The caller of `release` supplies a party index and a secret key. Both must be the ones the
vault identity names: the party index itself, and a key whose public key has the stored id. -/
def holdsIdentity (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (id : VaultIdentity) : Bool :=
  decide (party = id.party ∧
    publicKeyId (derivePublicKey cfg.suite cfg.params sk) = id.keyId)

/-- Output for a consumed grant: the production signature on the approval bytes of the vault's
own deployment, and nothing at all for a caller that does not hold the vault identity. -/
def issue (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat) (id : VaultIdentity)
    (r : Intent) : Option Certificate :=
  if holdsIdentity cfg sk party id then
    (sign cfg sk id.deploymentId party r).map (fun sig => ⟨party, r, sig⟩)
  else none

theorem holdsIdentity_wrong_party (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (id : VaultIdentity) (h : party ≠ id.party) : holdsIdentity cfg sk party id = false :=
  decide_eq_false (fun hc => h hc.1)

theorem holdsIdentity_wrong_key (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (id : VaultIdentity)
    (h : publicKeyId (derivePublicKey cfg.suite cfg.params sk) ≠ id.keyId) :
    holdsIdentity cfg sk party id = false :=
  decide_eq_false (fun hc => h hc.2)

theorem issue_of_holds (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (id : VaultIdentity) (r : Intent) (h : holdsIdentity cfg sk party id = true) :
    issue cfg sk party id r =
      (sign cfg sk id.deploymentId party r).map (fun sig => ⟨party, r, sig⟩) := by
  unfold issue
  rw [h]
  rfl

theorem issue_foreign_none (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (id : VaultIdentity) (r : Intent) (h : holdsIdentity cfg sk party id = false) :
    issue cfg sk party id r = none := by
  unfold issue
  rw [h]
  rfl

theorem issue_some (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (id : VaultIdentity) (r : Intent) (c : Certificate)
    (h : issue cfg sk party id r = some c) :
    c.party = party ∧ c.intent = r ∧
    sign cfg sk id.deploymentId party r = some c.signature ∧
    party = id.party ∧
    publicKeyId (derivePublicKey cfg.suite cfg.params sk) = id.keyId := by
  cases hh : holdsIdentity cfg sk party id with
  | false => rw [issue_foreign_none cfg sk party id r hh] at h; cases h
  | true =>
    rw [issue_of_holds cfg sk party id r hh] at h
    have hid := of_decide_eq_true hh
    cases hs : sign cfg sk id.deploymentId party r with
    | none => rw [hs] at h; cases h
    | some sig =>
      rw [hs] at h
      cases h
      exact ⟨rfl, rfl, rfl, hid.1, hid.2⟩

/-- In particular failure/abort of the production signer does not refund the
leaf or the spend. Every oracle call, including a failed call, is recorded. A caller without
the vault identity also consumes the grant and receives nothing: the state change does not
depend on who asks, only the output does. -/
def release (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) : Vault × Option Certificate :=
  if v.poisoned || decide (v.durable.anchor ≠ anchor) then
    ({ v with poisoned := true, active := none }, none)
  else if v.active = some r then
    ({ v with active := none, attempted := r :: v.attempted }, issue cfg sk party v.identity r)
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
    checkRound p v.identity.deploymentId b.intent b.digest b.openings = true ∧
      b.intent.message ≠ []
  activeBurned : ∀ r, v.active = some r → ∃ b ∈ v.durable.burned, b.intent = r
  attemptedBurned : ∀ r ∈ v.attempted, ∃ b ∈ v.durable.burned, b.intent = r
  activeFresh : ∀ r, v.active = some r → r ∉ v.attempted
  attemptedNodup : v.attempted.Nodup

theorem initial_safe (p : RoundPolicy) (cap : Nat) (id : VaultIdentity) :
    Safe p cap (initial id) := by
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

theorem mint_identity (p : RoundPolicy) (cap anchor : Nat) (v : Vault) (b : Burn) :
    (mint p cap anchor v b).identity = v.identity := by
  unfold mint
  split
  · rfl
  · split <;> rfl

theorem release_identity (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) :
    (release cfg sk party anchor v r).1.identity = v.identity := by
  unfold release; split <;> first | rfl | (split <;> rfl)

theorem forget_identity (v : Vault) : (forget v).identity = v.identity := rfl

theorem step_identity (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (p : RoundPolicy) (cap : Nat) (v : Vault) (c : Command) :
    (step cfg sk party p cap v c).identity = v.identity := by
  cases c with
  | mint a b => exact mint_identity p cap a v b
  | release a r => exact release_identity cfg sk party a v r
  | forget => rfl
  | crash => rfl

/-- The identity is the same after any command sequence: mint, release, forget and crash never
re-home a vault, its ledger or its grant. -/
theorem run_identity (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (p : RoundPolicy) (cap : Nat) (cs : List Command) (v : Vault) :
    (run cfg sk party p cap v cs).identity = v.identity := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih => exact (ih _).trans (step_identity cfg sk party p cap v c)

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

/-- A successful release had the grant for exactly `r` live. -/
theorem release_some_active (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) (c : Certificate)
    (h : (release cfg sk party anchor v r).2 = some c) : v.active = some r := by
  unfold release at h
  split at h
  · cases h
  · split at h
    next ha => exact ha
    next => cases h

/-- Successful outputs contain precisely the production signer's result for the bound request
on the approval bytes of the vault's own deployment, rather than a caller-selected signature,
and are produced only for the party and key that the vault identity names. -/
theorem release_output (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) (c : Certificate)
    (h : (release cfg sk party anchor v r).2 = some c) :
    c.party = party ∧ c.intent = r ∧
    sign cfg sk v.identity.deploymentId party r = some c.signature ∧
    party = v.identity.party ∧
    publicKeyId (derivePublicKey cfg.suite cfg.params sk) = v.identity.keyId := by
  unfold release at h
  split at h
  · cases h
  · split at h
    next => exact issue_some cfg sk party v.identity r c h
    next => cases h

/-- A caller whose party index or key is not the one the vault identity names gets no
certificate, whatever grant is live. -/
theorem release_foreign_identity_rejected (cfg : SigningConfig) (sk : PqSecretKey)
    (party anchor : Nat) (v : Vault) (r : Intent)
    (h : holdsIdentity cfg sk party v.identity = false) :
    (release cfg sk party anchor v r).2 = none := by
  unfold release
  split
  · rfl
  · split
    · exact issue_foreign_none cfg sk party v.identity r h
    · rfl

theorem release_verifies (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) (c : Certificate)
    (h : (release cfg sk party anchor v r).2 = some c) :
    verify cfg (derivePublicKey cfg.suite cfg.params sk) v.identity.deploymentId
      c.party c.intent c.signature = true := by
  obtain ⟨hp, hr, hs, _, _⟩ := release_output cfg sk party anchor v r c h
  rw [hp, hr]
  exact sign_verifies cfg sk v.identity.deploymentId party r c.signature hs

theorem release_wrong_request (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r s : Intent) (ha : v.active = some s) (hne : r ≠ s) :
    (release cfg sk party anchor v r).2 = none := by
  unfold release
  split
  · rfl
  · have hn : ¬ v.active = some r := by
      intro he; exact hne (Option.some.inj (he.symm.trans ha))
    simp only [hn, ↓reduceIte]

def queries (cfg : SigningConfig) (dep party : Nat) (v : Vault) : List ProdSigningQuery :=
  v.attempted.map (query cfg dep party)

theorem queries_one_time (cfg : SigningConfig) (dep party : Nat) (p : RoundPolicy)
    (cap : Nat) (v : Vault) (h : Safe p cap v) :
    ∀ q ∈ queries cfg dep party v, ∀ q' ∈ queries cfg dep party v,
      q.epoch = q'.epoch → q = q' := by
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
theorem trace_queries_one_time (cfg : SigningConfig) (sk : PqSecretKey) (dep party : Nat)
    (p : RoundPolicy) (cap : Nat) (id : VaultIdentity) (cs : List Command) :
    ∀ q ∈ queries cfg dep party (run cfg sk party p cap (initial id) cs),
    ∀ q' ∈ queries cfg dep party (run cfg sk party p cap (initial id) cs),
    q.epoch = q'.epoch → q = q' :=
  queries_one_time cfg dep party p cap _
    (run_safe cfg sk party p cap cs (initial id) (initial_safe p cap id))

/-- The budget bound is about the sum of actual burned transaction spends,
including forgotten or failed requests, not merely an unrelated counter. -/
theorem trace_burned_spend_le_cap (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat)
    (p : RoundPolicy) (cap : Nat) (id : VaultIdentity) (cs : List Command) :
    (((run cfg sk party p cap (initial id) cs).durable.burned).map
      (fun b => b.intent.spend)).sum ≤ cap := by
  have hs := run_safe cfg sk party p cap cs (initial id) (initial_safe p cap id)
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
#verify_constructive Qsag.Custody.publicKeyId_injective
#verify_constructive Qsag.Custody.run_identity
#verify_constructive Qsag.Custody.release_output
#verify_constructive Qsag.Custody.release_foreign_identity_rejected

/-! Composition entry point for independently keyed production custody approvals.
This proves structural extraction to the existing production hash-signature break
events. It is not a computational advantage bound, a distributed threshold signer,
or a refinement of an ELF/MIR implementation. In particular no simulator may
replace a successfully issued certificate with an arbitrary signature.
-/
public section
namespace Qsag.Custody
set_option autoImplicit false
set_option maxRecDepth 4096

-- Nat-only constructive pigeonhole proof; the core List subset cardinality
-- lemma currently depends on Classical.choice.
private def eraseParty (x : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseParty x ys

private theorem eraseParty_length {x : Nat} :
    ∀ {xs : List Nat}, x ∈ xs → (eraseParty x xs).length + 1 = xs.length
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseParty
    by_cases he : x = y
    · simp only [he, ↓reduceIte, List.length_cons]
    · simp only [he, ↓reduceIte, List.length_cons]
      cases h with
      | head => exact False.elim (he rfl)
      | tail _ ht => exact congrArg Nat.succ (eraseParty_length ht)

private theorem eraseParty_mem {x z : Nat} (hn : z ≠ x) :
    ∀ {xs : List Nat}, z ∈ xs → z ∈ eraseParty x xs
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseParty
    by_cases he : x = y
    · simp only [he, ↓reduceIte]
      subst y
      cases h with
      | head => exact False.elim (hn rfl)
      | tail _ ht => exact ht
    · simp only [he, ↓reduceIte]
      cases h with
      | head => exact .head _
      | tail _ ht => exact .tail _ (eraseParty_mem hn ht)

private theorem party_subset_length : ∀ {xs ys : List Nat},
    xs.Nodup → xs ⊆ ys → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, .cons hn hd, hs => by
    have he := eraseParty_length (hs (.head _))
    have hsub : xs ⊆ eraseParty x ys := by
      intro z hz
      exact eraseParty_mem (fun hzx => hn z hz hzx.symm) (hs (.tail _ hz))
    have hi := party_subset_length hd hsub
    rw [List.length_cons, ← he]
    exact Nat.add_le_add_right hi 1

/-- Coordinator state is public; replay protection is independent of signature
validity. The corrupt-party list is used only in the theorem, not by this check. -/
def acceptQuorum (cfg : SigningConfig) (pks : Nat → PqPublicKey) (dep : Nat)
    (numParties threshold : Nat) (consumedSessions : List Nat)
    (r : Intent) (certs : List Certificate) : Bool :=
  decide (r.session ∉ consumedSessions) &&
  decide (0 < threshold ∧ threshold ≤ certs.length ∧
    (certs.map Certificate.party).Nodup ∧ ∀ c ∈ certs, c.party < numParties) &&
  certs.all (verifyCertificate cfg pks dep r)

/-- `acceptQuorum` accepts exactly a fresh session together with a positive threshold met by
duplicate-free, in-range certificates that each carry the submitted intent and a signature
verifying, under the signer's own key, on the approval bytes of the coordinator's deployment. -/
theorem acceptQuorum_spec (cfg : SigningConfig) (pks : Nat → PqPublicKey) (dep n t : Nat)
    (used : List Nat) (r : Intent) (cs : List Certificate) :
    acceptQuorum cfg pks dep n t used r cs = true ↔
      r.session ∉ used ∧ 0 < t ∧ t ≤ cs.length ∧ (cs.map Certificate.party).Nodup ∧
      (∀ c ∈ cs, c.party < n) ∧
      ∀ c ∈ cs, c.intent = r ∧ verify cfg (pks c.party) dep c.party r c.signature = true := by
  constructor
  · intro h
    obtain ⟨hg, ha⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hf, hs⟩ := Bool.and_eq_true_iff.mp hg
    have shape := of_decide_eq_true hs
    refine ⟨of_decide_eq_true hf, shape.1, shape.2.1, shape.2.2.1, shape.2.2.2, ?_⟩
    intro c hm
    have hv := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ha c hm)
    have he : c.intent = r := of_decide_eq_true hv.1
    refine ⟨he, ?_⟩
    rw [← he]
    exact hv.2
  · rintro ⟨hf, h0, hl, hn, hp, hv⟩
    unfold acceptQuorum
    refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true hf, decide_eq_true ⟨h0, hl, hn, hp⟩⟩, List.all_eq_true.mpr ?_⟩
    intro c hm
    obtain ⟨he, hs⟩ := hv c hm
    unfold verifyCertificate
    refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true he, ?_⟩
    rw [he]
    exact hs

structure Coordinator where
  consumedSessions : List Nat := []
  spent : Nat := 0
  capacity : Nat := 0

/-- The public coordinator records consumption on acceptance. Callers cannot
replay a session merely by supplying a different valid certificate set. -/
def submit (cfg : SigningConfig) (pks : Nat → PqPublicKey) (dep n t : Nat)
    (st : Coordinator) (r : Intent) (cs : List Certificate) : Coordinator × Bool :=
  if acceptQuorum cfg pks dep n t st.consumedSessions r cs then
    if st.spent + r.spend ≤ st.capacity then
      ({ st with
        consumedSessions := r.session :: st.consumedSessions
        spent := st.spent + r.spend }, true)
    else (st, false)
  else (st, false)

theorem submit_accepted (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (dep n t : Nat) (st : Coordinator) (r : Intent) (cs : List Certificate)
    (h : (submit cfg pks dep n t st r cs).2 = true) :
    acceptQuorum cfg pks dep n t st.consumedSessions r cs = true ∧
    st.spent + r.spend ≤ st.capacity ∧
    (submit cfg pks dep n t st r cs).1 =
      { st with
        consumedSessions := r.session :: st.consumedSessions
        spent := st.spent + r.spend } := by
  unfold submit at h ⊢
  split at h
  next ha =>
    split at h
    next hb => exact ⟨ha, hb, by simp only [ha, hb, ↓reduceIte]⟩
    next => cases h
  next => cases h

/-- A rejected submission leaves the coordinator state unchanged. -/
theorem submit_rejected (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (dep n t : Nat) (st : Coordinator) (r : Intent) (cs : List Certificate)
    (h : (submit cfg pks dep n t st r cs).2 = false) :
    (submit cfg pks dep n t st r cs).1 = st := by
  unfold submit at h ⊢
  split
  next ha =>
    split
    next hb => simp only [ha, hb, ↓reduceIte] at h; cases h
    next => rfl
  next => rfl

/-- `submit` accepts exactly when the quorum check passes and the spend fits the remaining
capacity. -/
theorem submit_accepted_iff (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (dep n t : Nat) (st : Coordinator) (r : Intent) (cs : List Certificate) :
    (submit cfg pks dep n t st r cs).2 = true ↔
      acceptQuorum cfg pks dep n t st.consumedSessions r cs = true ∧
      st.spent + r.spend ≤ st.capacity := by
  constructor
  · intro h
    exact ⟨(submit_accepted cfg pks dep n t st r cs h).1, (submit_accepted cfg pks dep n t st r cs h).2.1⟩
  · rintro ⟨ha, hb⟩
    unfold submit
    simp only [ha, hb, ↓reduceIte]

theorem submit_budget (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (dep n t : Nat) (st : Coordinator) (r : Intent) (cs : List Certificate)
    (h : (submit cfg pks dep n t st r cs).2 = true) :
    (submit cfg pks dep n t st r cs).1.spent ≤ st.capacity := by
  obtain ⟨_, hb, he⟩ := submit_accepted cfg pks dep n t st r cs h
  rw [he]
  exact hb

theorem quorum_replay_rejected (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (dep n t : Nat) (used : List Nat) (r : Intent) (cs : List Certificate)
    (h : r.session ∈ used) : acceptQuorum cfg pks dep n t used r cs = false := by
  simp [acceptQuorum, h]

theorem submit_replay_rejected (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (dep n t : Nat) (st : Coordinator) (r : Intent) (cs cs' : List Certificate)
    (h : (submit cfg pks dep n t st r cs).2 = true) :
    (submit cfg pks dep n t (submit cfg pks dep n t st r cs).1 r cs').2 = false := by
  rw [(submit_accepted cfg pks dep n t st r cs h).2.2]
  unfold submit
  rw [quorum_replay_rejected cfg pks dep n t _ r cs' List.mem_cons_self]
  rfl

theorem quorum_has_honest (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (dep n t : Nat) (used corrupt : List Nat) (r : Intent) (cs : List Certificate)
    (hc : corrupt.length < t) (h : acceptQuorum cfg pks dep n t used r cs = true) :
    ∃ c ∈ cs, c.party ∉ corrupt ∧ c.intent = r ∧
      verify cfg (pks c.party) dep c.party r c.signature = true := by
  obtain ⟨hg, ha⟩ := Bool.and_eq_true_iff.mp h
  have shape := of_decide_eq_true (Bool.and_eq_true_iff.mp hg).2
  rcases list_search (fun c : Certificate => c.party ∉ corrupt)
      (fun _ => Decidable.em _) cs with ⟨c, hm, hn⟩ | hall
  · have hv := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ha c hm)
    have he := of_decide_eq_true hv.1
    exact ⟨c, hm, hn, he, by simpa only [he] using hv.2⟩
  · have hsub : cs.map Certificate.party ⊆ corrupt := by
      intro i hi
      obtain ⟨c, hm, rfl⟩ := List.mem_map.mp hi
      exact Decidable.byContradiction (hall c hm)
    have hlen := party_subset_length shape.2.2.1 hsub
    rw [List.length_map] at hlen
    exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans shape.2.1 hlen)) hc)

/-- Identity of custodian `i` of deployment `dep` under key `sk`. -/
def custodianIdentity (cfg : SigningConfig) (dep i : Nat) (sk : PqSecretKey) : VaultIdentity :=
  ⟨dep, i, publicKeyId (derivePublicKey cfg.suite cfg.params sk)⟩

theorem holdsIdentity_custodian (cfg : SigningConfig) (dep i : Nat) (sk : PqSecretKey) :
    holdsIdentity cfg sk i (custodianIdentity cfg dep i sk) = true :=
  decide_eq_true ⟨rfl, rfl⟩

def stateAfter (cfg : SigningConfig) (dep : Nat) (keys : Nat → PqSecretKey)
    (policies : Nat → RoundPolicy) (caps : Nat → Nat)
    (traces : Nat → List Command) (i : Nat) : Vault :=
  run cfg (keys i) i (policies i) (caps i) (initial (custodianIdentity cfg dep i (keys i)))
    (traces i)

theorem stateAfter_identity (cfg : SigningConfig) (dep : Nat) (keys : Nat → PqSecretKey)
    (policies : Nat → RoundPolicy) (caps : Nat → Nat)
    (traces : Nat → List Command) (i : Nat) :
    (stateAfter cfg dep keys policies caps traces i).identity =
      custodianIdentity cfg dep i (keys i) :=
  run_identity cfg (keys i) i (policies i) (caps i) (traces i) _

def signingLog (cfg : SigningConfig) (sk : PqSecretKey) (dep i : Nat) (v : Vault) :=
  productionSigningLog cfg.suite cfg.params sk (queries cfg dep i v)

/-- `BurnedApproval` is concrete data membership plus the real MAC checker on the commitment of
the vault's own deployment; it is derived from execution, not a hypothetical judgement supplied
to it. -/
def BurnedApproval (p : RoundPolicy) (v : Vault) (r : Intent) : Prop :=
  ∃ b ∈ v.durable.burned, b.intent = r ∧
    checkRound p v.identity.deploymentId b.intent b.digest b.openings = true ∧
      b.intent.message ≠ []

theorem attempted_approved (p : RoundPolicy) (cap : Nat) (v : Vault)
    (hs : Safe p cap v) (r : Intent) (hm : r ∈ v.attempted) : BurnedApproval p v r := by
  obtain ⟨b, hb, he⟩ := hs.attemptedBurned r hm
  exact ⟨b, hb, he, hs.approved b hb⟩

theorem log_fresh_of_not_attempted (cfg : SigningConfig) (sk : PqSecretKey)
    (dep i : Nat) (v : Vault) (r : Intent) (hn : r ∉ v.attempted) :
    ∀ e ∈ signingLog cfg sk dep i v, e.1 ≠ payload dep i r := by
  intro e he hEq
  obtain ⟨q, hq, hm, _⟩ := productionSigningLog_generated _ _ _ _ e he
  obtain ⟨s, hs, hsq⟩ := List.mem_map.mp hq
  have hp : payload dep i s = payload dep i r := by
    simpa only [← hsq, query] using hm.symm.trans hEq
  exact hn ((payload_injective hp).2.2 ▸ hs)

/-- The candidate supplied to the signature game is the accepted certificate
itself, with the exact trace-derived oracle queries. This does not replace the
candidate by an arbitrary existential collision. -/
theorem accepted_fresh_certificate_wins (cfg : SigningConfig) (sk : PqSecretKey)
    (dep i : Nat) (v : Vault) (r : Intent) (sig : PqHashSig)
    (hn : r ∉ v.attempted)
    (hv : verify cfg (derivePublicKey cfg.suite cfg.params sk) dep i r sig = true) :
    prodEufCmaWin cfg.suite cfg.params ⟨sk, queries cfg dep i v, payload dep i r, sig⟩ = true := by
  have hf := log_fresh_of_not_attempted cfg sk dep i v r hn
  have hnot : payload dep i r ∉ (signingLog cfg sk dep i v).map Prod.fst := by
    intro hm
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
    exact hf e he heq
  rw [prodEufCmaWin_eq]
  exact Bool.and_eq_true_iff.mpr ⟨hv, decide_eq_true hnot⟩

/-- Every message a vault of deployment `d` ever put to its signing oracle is an approval
payload of `d`. None of them is an approval payload of another deployment, for any party and
any intent, whatever the vault has attempted. -/
theorem log_fresh_cross_deployment (cfg : SigningConfig) (sk : PqSecretKey)
    (d d' i j : Nat) (v : Vault) (r : Intent) (hne : d ≠ d') :
    ∀ e ∈ signingLog cfg sk d i v, e.1 ≠ payload d' j r := by
  intro e he hEq
  obtain ⟨q, hq, hm, _⟩ := productionSigningLog_generated _ _ _ _ e he
  obtain ⟨s, hs, hsq⟩ := List.mem_map.mp hq
  have hp : payload d i s = payload d' j r := by
    simpa only [← hsq, query] using hm.symm.trans hEq
  exact hne (payload_injective hp).1

/-- **A grant of one deployment is not consumable by another, short of a forgery.** Let `v` be
any reachable-or-not `Safe` vault, serving deployment `v.identity.deploymentId` under key `sk`,
with whatever grants it minted, consumed and signed. If a signature verifies under that key as
an approval for a different deployment `d'` (any party index `j`, any intent `r`, including an
intent the vault did sign for its own deployment), then that signature is a fresh-message win in
the signature game against the vault's whole signing log, and the production reduction yields a
target-collision or a WOTS preimage event. No certificate the vault released is such a
signature: `release_output` shows each is on `payload v.identity.deploymentId _ _`. -/
theorem grant_cross_deployment_consumption_forges (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap : Nat) (v : Vault) (hs : Safe p cap v)
    (d' j : Nat) (r : Intent) (sig : PqHashSig)
    (hw : cfg.params.w = 4 ∨ cfg.params.w = 16) (hst : cfg.params.statefulJorts = true)
    (hne : v.identity.deploymentId ≠ d')
    (hv : verify cfg (derivePublicKey cfg.suite cfg.params sk) d' j r sig = true) :
    prodEufCmaWin cfg.suite cfg.params
      ⟨sk, queries cfg v.identity.deploymentId v.identity.party v, payload d' j r, sig⟩ = true ∧
    (ProdSmTcrBreak cfg.suite cfg.params sk
        (signingLog cfg sk v.identity.deploymentId v.identity.party v) ∨
      ProdPreimageBreak cfg.suite cfg.params sk
        (signingLog cfg sk v.identity.deploymentId v.identity.party v) (payload d' j r) sig) := by
  have hf := log_fresh_cross_deployment cfg sk v.identity.deploymentId d' v.identity.party j v r hne
  have hnot : payload d' j r ∉
      (signingLog cfg sk v.identity.deploymentId v.identity.party v).map Prod.fst := by
    intro hm
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
    exact hf e he heq
  refine ⟨?_, ?_⟩
  · rw [prodEufCmaWin_eq]
    exact Bool.and_eq_true_iff.mpr ⟨hv, decide_eq_true hnot⟩
  · exact production_stateful_forgery_break cfg.suite cfg.params sk
      (queries cfg v.identity.deploymentId v.identity.party v) (payload d' j r) sig hw hst
      (queries_one_time cfg _ _ p cap v hs) hf hv

/-- A round committed for deployment `d` mints a grant in a vault of another deployment only
together with a cSHAKE collision on two different inputs. -/
theorem mintGuard_foreign_round_collision (p : RoundPolicy) (cap : Nat) (v : Vault) (b : Burn)
    (d : Nat) (r : Intent) (hne : d ≠ v.identity.deploymentId)
    (hd : b.digest = roundCommitment d r) (hg : mintGuard p cap v b = true) :
    payload d 0 r ≠ payload v.identity.deploymentId 0 b.intent ∧
      cshake256Bytes roundDomain (payload d 0 r) =
        cshake256Bytes roundDomain (payload v.identity.deploymentId 0 b.intent) :=
  ⟨payload_ne_of_deployment_ne hne 0 0 r b.intent,
    hd.symm.trans (checkRound_commitment p _ b.intent b.digest b.openings
      (Bool.and_eq_true_iff.mp hg).2)⟩

/-- Composition of the actual quorum checker, hostile per-party execution,
durable policy checks, real production verifier, and hash-signature reduction.
One-time leaf use and fresh-message signing-log separation are proved here.
Only the explicit stateful profile and supported radix select the existing
production reduction; no unforgeability or whole-system conclusion is a premise.
-/
theorem accepted_quorum_approval_or_hash_break
    (cfg : SigningConfig) (dep : Nat) (keys : Nat → PqSecretKey)
    (policies : Nat → RoundPolicy) (caps : Nat → Nat) (traces : Nat → List Command)
    (n t : Nat) (st : Coordinator) (corrupt : List Nat) (r : Intent) (cs : List Certificate)
    (hw : cfg.params.w = 4 ∨ cfg.params.w = 16)
    (hst : cfg.params.statefulJorts = true) (hc : corrupt.length < t)
    (h : (submit cfg (fun i => derivePublicKey cfg.suite cfg.params (keys i))
      dep n t st r cs).2 = true) :
    ∃ c ∈ cs, c.party ∉ corrupt ∧
      (BurnedApproval (policies c.party) (stateAfter cfg dep keys policies caps traces c.party) r ∨
       (prodEufCmaWin cfg.suite cfg.params
         ⟨keys c.party, queries cfg dep c.party (stateAfter cfg dep keys policies caps traces c.party),
           payload dep c.party r, c.signature⟩ = true ∧
       (ProdSmTcrBreak cfg.suite cfg.params (keys c.party)
         (signingLog cfg (keys c.party) dep c.party (stateAfter cfg dep keys policies caps traces c.party)) ∨
       ProdPreimageBreak cfg.suite cfg.params (keys c.party)
         (signingLog cfg (keys c.party) dep c.party (stateAfter cfg dep keys policies caps traces c.party))
         (payload dep c.party r) c.signature))) := by
  have hcheck := (submit_accepted cfg _ dep n t st r cs h).1
  obtain ⟨c, hcm, hch, _hctx, hv⟩ :=
    quorum_has_honest cfg _ dep n t st.consumedSessions corrupt r cs hc hcheck
  refine ⟨c, hcm, hch, ?_⟩
  let v := stateAfter cfg dep keys policies caps traces c.party
  have hs : Safe (policies c.party) (caps c.party) v :=
    run_safe cfg (keys c.party) c.party (policies c.party) (caps c.party)
      (traces c.party) _ (initial_safe _ _ _)
  by_cases hm : r ∈ v.attempted
  · exact .inl (attempted_approved _ _ v hs r hm)
  · right
    refine ⟨accepted_fresh_certificate_wins cfg (keys c.party) dep c.party v r c.signature hm hv, ?_⟩
    exact production_stateful_forgery_break cfg.suite cfg.params (keys c.party)
      (queries cfg dep c.party v) (payload dep c.party r) c.signature hw hst
      (queries_one_time cfg dep c.party _ _ v hs)
      (log_fresh_of_not_attempted cfg (keys c.party) dep c.party v r hm) hv

/-- The scheduler selects one custodian. Changing any other custodian's secret,
policy, capacity or history cannot change the selected local execution. -/
theorem local_state_isolated (cfg : SigningConfig) (dep : Nat) (keys keys' : Nat → PqSecretKey)
    (policies : Nat → RoundPolicy) (caps : Nat → Nat) (traces : Nat → List Command)
    (i : Nat) (h : keys i = keys' i) :
    stateAfter cfg dep keys policies caps traces i =
      stateAfter cfg dep keys' policies caps traces i := by
  simp only [stateAfter, h]

end Qsag.Custody
end
set_option maxRecDepth 4096
#verify_constructive Qsag.Custody.quorum_has_honest
#verify_constructive Qsag.Custody.acceptQuorum_spec
#verify_constructive Qsag.Custody.submit_accepted
#verify_constructive Qsag.Custody.submit_accepted_iff
#verify_constructive Qsag.Custody.submit_rejected
#verify_constructive Qsag.Custody.accepted_quorum_approval_or_hash_break
#verify_constructive Qsag.Custody.accepted_fresh_certificate_wins
#verify_constructive Qsag.Custody.quorum_replay_rejected
#verify_constructive Qsag.Custody.submit_replay_rejected
#verify_constructive Qsag.Custody.submit_budget
#verify_constructive Qsag.Custody.local_state_isolated
#verify_constructive Qsag.Custody.log_fresh_cross_deployment
#verify_constructive Qsag.Custody.grant_cross_deployment_consumption_forges
#verify_constructive Qsag.Custody.mintGuard_foreign_round_collision

/-! Bridge from the operational production transaction-policy specification to
the separate-key custody approval construction. Amount and signing bytes are
derived from the admitted transaction; they are not additional host arguments.
This does not claim implementation-level durable-store or threshold-MPC refinement.
-/
public section
namespace Qsag.Custody
set_option autoImplicit false
set_option maxRecDepth 4096

def transactionIntent (tx : TransactionIntent) (round leaf : Nat) : Intent :=
  ⟨ofLE tx.session_id.reverse, round, leaf, tx.amount_units, toCanonicalSigningBytes tx⟩

structure PolicyVault where
  policy : AuthenticatedPolicyState
  vault : Vault

/-- Both policy evaluation and resource reservation burn before signing. A
rejected request clears any older volatile grant while retaining durable burns.
Policy admission may burn even if the later MAC/resource check rejects, which
is deliberately fail-closed and does not refund an already authorized spend. -/
def mintTransaction (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) : PolicyVault :=
  let cleared := forget st.vault
  match authenticatedPolicyGuardStep st.policy tx tags timestamp with
  | .accepted policy' _ =>
    let r := transactionIntent tx round leaf
    ⟨policy', mint p cap anchor cleared ⟨r, roundCommitment st.vault.identity.deploymentId r, ops⟩⟩
  | .rejected _ _ => ⟨st.policy, cleared⟩

theorem mintTransaction_identity (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) :
    (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.identity =
      st.vault.identity := by
  unfold mintTransaction
  split
  · exact mint_identity p cap anchor (forget st.vault) _
  · rfl

/-- No hypothetical approval judgement is an argument: admission is recovered
from a successful execution of the actual policy-and-mediation entry point. -/
theorem transaction_grant_admitted (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (r : Intent)
    (h : (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.active = some r) :
    policyCheckAdmission st.policy tx tags timestamp = true ∧
    r = transactionIntent tx round leaf ∧
    checkRound p st.vault.identity.deploymentId r
      (roundCommitment st.vault.identity.deploymentId r) ops = true := by
  by_cases ha : policyCheckAdmission st.policy tx tags timestamp = true
  · simp only [mintTransaction, authenticatedPolicyGuardStep_eq, ha, ↓reduceIte] at h
    obtain ⟨hg, he⟩ := mint_granted p cap anchor (forget st.vault)
      ⟨transactionIntent tx round leaf,
        roundCommitment st.vault.identity.deploymentId (transactionIntent tx round leaf), ops⟩
      r rfl h
    change transactionIntent tx round leaf = r at he
    refine ⟨ha, he.symm, ?_⟩
    have hm := (Bool.and_eq_true_iff.mp hg).2
    rw [← he]
    exact hm
  · simp only [mintTransaction, authenticatedPolicyGuardStep_eq, ha] at h
    cases h

/-- The resource charge and signed message come from the exact transaction
that passed wire-width, time, pinned-policy, initiator-authentication, nonce,
session, recipient and rolling-spend checks. -/
theorem transaction_grant_binding (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (r : Intent)
    (h : (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.active = some r) :
    r.spend = tx.amount_units ∧ r.message = toCanonicalSigningBytes tx ∧
    tx.amount_units ≤ st.policy.rules.per_tx_cap ∧
    policyProjectedSpend st.policy tx ≤ st.policy.rules.velocity_window_cap ∧
    policyAuthenticatedInitiator st.policy tx tags = true := by
  obtain ⟨ha, hr, _⟩ := transaction_grant_admitted p cap anchor st tx tags timestamp round leaf ops r h
  have hb := policyAdmission_wire_and_burns ha
  rw [hr]
  exact ⟨rfl, rfl, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2⟩

theorem transaction_rejected_clears_grant (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (h : policyCheckAdmission st.policy tx tags timestamp = false) :
    (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.active = none ∧
    (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.durable = st.vault.durable := by
  simp only [mintTransaction, authenticatedPolicyGuardStep_eq, h, Bool.false_eq_true, ↓reduceIte]
  exact ⟨rfl, rfl⟩

/-- After admission, changing the asserted amount at release cannot substitute
another transaction or reuse an older grant. -/
theorem transaction_wrong_amount_rejected (cfg : SigningConfig) (sk : PqSecretKey)
    (party : Nat) (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (timestamp round leaf : Nat)
    (ops : List RoundOpening) (r bad : Intent)
    (h : (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault.active = some r)
    (hne : bad.spend ≠ tx.amount_units) :
    (release cfg sk party (anchor + 1)
      (mintTransaction p cap anchor st tx tags timestamp round leaf ops).vault bad).2 = none := by
  apply release_wrong_request cfg sk party (anchor + 1) _ bad r h
  intro he
  exact hne ((congrArg Intent.spend he).trans
    (transaction_grant_binding p cap anchor st tx tags timestamp round leaf ops r h).1)

/-- No successful release can bypass the policy result, even if a stale handle
was live before this mint attempt. -/
