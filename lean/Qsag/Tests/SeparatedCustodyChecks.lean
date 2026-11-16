module
public import Qsag.Protocol.Signing.HypertreeEufCma
meta import Qsag.Protocol.Signing.HypertreeEufCma
public import Qsag.Custody.CustodySuiteFull
meta import Qsag.Custody.CustodySuiteFull
public import Qsag.Oracle.Keccak
meta import Qsag.Oracle.Keccak
public import Qsag.Spec.Encoding
meta import Qsag.Spec.Encoding
public import Qsag.Custody.SeparatedCustody
meta import Qsag.Custody.SeparatedCustody
public import Qsag.Protocol.Signing.HashSigs
meta import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Threshold.MaliciousSecurity
meta import Qsag.Protocol.Threshold.MaliciousSecurity
public import Qsag.Math.Gf2Pow128
meta import Qsag.Math.Gf2Pow128
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag.Custody.Checks
set_option autoImplicit false
set_option maxRecDepth 4096

/-- Full 256-bit digest coverage and real cSHAKE256, with four stateful leaves.
This is an executable construction check, not a security-strength benchmark. -/
def cfg : SigningConfig := ⟨cshake256Suite, compactJortsProdParams,
  List.replicate 32 0x08, 4096⟩
def key : PqSecretKey :=
  ⟨List.replicate 32 0x17, List.replicate 32 0x29, List.replicate 32 0x43⟩
def request : Intent := ⟨7, 0, 1, 3, [0x63, 0x75, 0x73, 0x74, 0x6f, 0x64, 0x79]⟩
/-- Deployment identifier of the fixture, and the identity of its custodian-0 vault. -/
def dep : Nat := 0x51534147
def ident : VaultIdentity := custodianIdentity cfg dep 0 key
def vault0 : Vault := initial ident

def macKeys : BdozVerifierKeys :=
  ⟨towerOne 7, towerOne 7, fun _ => (towerOne 7, towerOne 7)⟩
def policy : RoundPolicy :=
  ⟨fun _ _ => macKeys, [0], fun _ => roundCommitment dep request⟩
def opening : RoundOpening :=
  ⟨7, 0, ⟨0, towerOne 7, towerZero 7, towerZero 7⟩⟩
def burn : Burn := ⟨request, roundCommitment dep request, [opening]⟩

/-! ### Deployment binding (BACKLOG-62)

`legacyPayload` is `Custody.payload` with the deployment frame removed and nothing else changed
(same `"QSAG.CUSTODY.APPROVAL/v3"` tag): the shape the approval bytes had before the deployment
identifier was framed in. `legacySign`/`legacyVerify` are the production signer and verifier on it.
They take a deployment argument and ignore it, which is the old shape: the vault and the permit
named no deployment. The teeth below show that in that shape a released approval is an approval
for every deployment, and that release served any caller. -/

def legacyPayload (_deploymentId party : Nat) (r : Intent) : List UInt8 :=
  encodeMultiFrame ["QSAG.CUSTODY.APPROVAL/v3".toUTF8.toList, leb128 party,
    leb128 r.session, leb128 r.round, leb128 r.leaf, leb128 r.spend, r.message]

def legacySign (cfg : SigningConfig) (sk : PqSecretKey) (dep party : Nat) (r : Intent) :
    Option PqHashSig :=
  evalProductionStatefulSign cfg.suite cfg.params sk (legacyPayload dep party r)
    cfg.randomness r.leaf cfg.grindLimit

def legacyVerify (cfg : SigningConfig) (pk : PqPublicKey) (dep party : Nat)
    (r : Intent) (sig : PqHashSig) : Bool :=
  verifyProductionPqHashSig cfg.suite cfg.params pk (legacyPayload dep party r) sig

/-- The old release: the grant is handed to whichever party index and key the caller supplies. -/
def legacyRelease (cfg : SigningConfig) (sk : PqSecretKey) (party anchor : Nat)
    (v : Vault) (r : Intent) : Vault × Option Certificate :=
  if v.poisoned || decide (v.durable.anchor ≠ anchor) then
    ({ v with poisoned := true, active := none }, none)
  else if v.active = some r then
    ({ v with active := none, attempted := r :: v.attempted },
      (legacySign cfg sk 0 party r).map (fun sig => ⟨party, r, sig⟩))
  else (v, none)

/-- The approval bytes of `(d, i, r)` and `(d', j, s)` coincide under the encoding `enc`. The
deployment-framed `payload` and the old `legacyPayload` are compared through this one relation. -/
def SameApprovalBytes (enc : Nat → Nat → Intent → List UInt8) (d d' i j : Nat) (r s : Intent) :
    Prop :=
  enc d i r = enc d' j s

theorem payload_binds_deployment_audited {d d' i j : Nat} {r s : Intent}
    (h : SameApprovalBytes payload d d' i j r s) : d = d' ∧ i = j ∧ r = s :=
  payload_injective h

theorem inhabited_equal_payloads :
    ∃ (d d' i j : Nat) (r s : Intent), SameApprovalBytes payload d d' i j r s :=
  ⟨dep, dep, 0, 0, request, request, rfl⟩

/-- Old shape: the approval bytes of two different deployments coincide, where the
deployment-framed bytes differ. -/
theorem tooth_legacy_payload_deployment_blind :
    ∃ (d d' i : Nat) (r : Intent), d ≠ d' ∧
      SameApprovalBytes legacyPayload d d' i i r r ∧ ¬ SameApprovalBytes payload d d' i i r r :=
  ⟨0, 1, 0, request, by decide, rfl, payload_ne_of_deployment_ne (by decide) 0 0 request request⟩

#verify_inhabited payload_binds_deployment_audited inhabited_equal_payloads
#tooth_pair payload_binds_deployment_audited vs tooth_legacy_payload_deployment_blind

theorem grant_cross_deployment_consumption_forges_audited (cfg : SigningConfig)
    (sk : PqSecretKey) (p : RoundPolicy) (cap : Nat) (v : Vault) (hs : Safe p cap v)
    (d' j : Nat) (r : Intent) (sig : PqHashSig)
    (hw : cfg.params.w = 4 ∨ cfg.params.w = 16) (hst : cfg.params.statefulJorts = true)
    (hne : v.identity.deploymentId ≠ d')
    (hv : verify cfg (derivePublicKey cfg.suite cfg.params sk) d' j r sig = true) :
    prodEufCmaWin cfg.suite cfg.params
      ⟨sk, queries cfg v.identity.deploymentId v.identity.party v, payload d' j r, sig⟩ = true ∧
    (ProdSmTcrBreak cfg.suite cfg.params sk
        (signingLog cfg sk v.identity.deploymentId v.identity.party v) ∨
      ProdPreimageBreak cfg.suite cfg.params sk
        (signingLog cfg sk v.identity.deploymentId v.identity.party v) (payload d' j r) sig) :=
  grant_cross_deployment_consumption_forges cfg sk p cap v hs d' j r sig hw hst hne hv

/-- The constant-hash toy suite, where a forgery exists: every premise of the theorem holds
jointly, with a vault of deployment `0` and an accepted approval for deployment `1`. -/
def toyCfg : SigningConfig := ⟨crumbToySuite, prodToyStatefulParams, [], 0⟩
def toyIntent : Intent := ⟨0, 0, 0, 0, []⟩

theorem toy_cross_deployment_approval_accepted :
    verify toyCfg (derivePublicKey toyCfg.suite toyCfg.params ⟨[], [], []⟩) 1 0 toyIntent
      prodToyForgery = true :=
  prodToyForgery_accepted_on (payload 1 0 toyIntent)

theorem toyCfg_radix : toyCfg.params.w = 4 := by
  show prodToyStatefulParams.w = 4
  rw [prodToyStatefulParams.public_eq_1]

theorem toyCfg_stateful : toyCfg.params.statefulJorts = true := by
  show prodToyStatefulParams.statefulJorts = true
  rw [prodToyStatefulParams.public_eq_1]

theorem inhabited_cross_deployment_forgery :
    ∃ (cfg : SigningConfig) (sk : PqSecretKey) (p : RoundPolicy) (cap : Nat) (v : Vault)
      (d' j : Nat) (r : Intent) (sig : PqHashSig),
      Safe p cap v ∧ (cfg.params.w = 4 ∨ cfg.params.w = 16) ∧
      cfg.params.statefulJorts = true ∧ v.identity.deploymentId ≠ d' ∧
      verify cfg (derivePublicKey cfg.suite cfg.params sk) d' j r sig = true :=
  ⟨toyCfg, ⟨[], [], []⟩, policy, 0, initial ⟨0, 0, []⟩, 1, 0, toyIntent, prodToyForgery,
    initial_safe policy 0 _, .inl toyCfg_radix, toyCfg_stateful, by decide,
    toy_cross_deployment_approval_accepted⟩

theorem legacySign_verifies (cfg : SigningConfig) (sk : PqSecretKey) (d d' party : Nat)
    (r : Intent) (sig : PqHashSig) (h : legacySign cfg sk d party r = some sig) :
    legacyVerify cfg (derivePublicKey cfg.suite cfg.params sk) d' party r sig = true :=
  verifyProductionPqHashSig_evalProductionStatefulSign _ _ _ _ _ _ _ _ h

/-- Old shape: an approval honestly signed while serving deployment `d` is accepted as an
approval for every other deployment `d'`. It is a signed message, so no forgery is involved. -/
theorem tooth_legacy_release_accepted_by_other_deployment (cfg : SigningConfig)
    (sk : PqSecretKey) (d d' party : Nat) (r : Intent) (sig : PqHashSig)
    (h : legacySign cfg sk d party r = some sig) :
    ¬ (legacyVerify cfg (derivePublicKey cfg.suite cfg.params sk) d' party r sig = false) := by
  rw [legacySign_verifies cfg sk d d' party r sig h]
  exact Bool.noConfusion

#verify_inhabited grant_cross_deployment_consumption_forges_audited inhabited_cross_deployment_forgery
#tooth_pair grant_cross_deployment_consumption_forges_audited vs tooth_legacy_release_accepted_by_other_deployment

theorem foreign_deployment_acceptance_forges_audited (d d' : Deployment)
    (commands : List HistoryCommand) (s' : SharedHistory) (r : Intent) (cs : List Certificate)
    (c : Certificate) (hc : c ∈ cs)
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true)
    (hne : d.deploymentId ≠ d'.deploymentId) (hsigner : d'.signer = d.signer)
    (hkey : publicKeys d' c.party = publicKeys d c.party)
    (hacc : (submitRecorded d' s' r cs).2 = true) :
    prodEufCmaWin d.signer.suite d.signer.params
      ⟨d.keys c.party,
        queries d.signer d.deploymentId c.party ((generatedHistory d commands).parties c.party).vault,
        payload d'.deploymentId c.party r, c.signature⟩ = true ∧
    (ProdSmTcrBreak d.signer.suite d.signer.params (d.keys c.party)
        (signingLog d.signer (d.keys c.party) d.deploymentId c.party
          ((generatedHistory d commands).parties c.party).vault) ∨
      ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
        (signingLog d.signer (d.keys c.party) d.deploymentId c.party
          ((generatedHistory d commands).parties c.party).vault)
        (payload d'.deploymentId c.party r) c.signature) :=
  foreign_deployment_acceptance_forges d d' commands s' r cs c hc hw hst hne hsigner hkey hacc

/-- Two deployments over the constant-hash toy suite that share every key and differ in their
identifier only. -/
def toyDeployment (dep : Nat) : Deployment :=
  { deploymentId := dep
    signer := toyCfg
    keys := fun _ => ⟨[], [], []⟩
    rounds := fun _ => policy
    caps := fun _ => 0
    policies := fun i => demoQuorumCustodian i [] []
    numParties := 1
    threshold := 1
    capacity := 0 }

def toyCertificate : Certificate := ⟨0, toyIntent, prodToyForgery⟩

theorem toy_foreign_deployment_accepts :
    (submitRecorded (toyDeployment 1) ⟨{ capacity := 0 }, []⟩ toyIntent [toyCertificate]).2 =
      true := by
  rw [submitRecorded_verdict]
  refine (submit_accepted_iff _ _ _ _ _ _ _ _).mpr
    ⟨(acceptQuorum_spec _ _ _ _ _ _ _ _).mpr ⟨by decide, by decide, by decide, by decide,
      by decide, ?_⟩, by decide⟩
  intro c hc
  rw [List.mem_singleton.mp hc]
  exact ⟨rfl, toy_cross_deployment_approval_accepted⟩

theorem inhabited_foreign_deployment_acceptance :
    ∃ (d d' : Deployment) (s' : SharedHistory) (r : Intent) (cs : List Certificate)
      (c : Certificate),
      c ∈ cs ∧ (d.signer.params.w = 4 ∨ d.signer.params.w = 16) ∧
      d.signer.params.statefulJorts = true ∧ d.deploymentId ≠ d'.deploymentId ∧
      d'.signer = d.signer ∧ publicKeys d' c.party = publicKeys d c.party ∧
      (submitRecorded d' s' r cs).2 = true :=
  ⟨toyDeployment 0, toyDeployment 1, ⟨{ capacity := 0 }, []⟩, toyIntent, [toyCertificate],
    toyCertificate, List.mem_singleton.mpr rfl, .inl toyCfg_radix, toyCfg_stateful, by decide,
    rfl, rfl,
    toy_foreign_deployment_accepts⟩

#verify_inhabited foreign_deployment_acceptance_forges_audited inhabited_foreign_deployment_acceptance
#tooth_pair foreign_deployment_acceptance_forges_audited vs tooth_legacy_release_accepted_by_other_deployment

theorem release_foreign_identity_rejected_audited (cfg : SigningConfig) (sk : PqSecretKey)
    (party anchor : Nat) (v : Vault) (r : Intent)
    (h : holdsIdentity cfg sk party v.identity = false) :
    (release cfg sk party anchor v r).2 = none :=
  release_foreign_identity_rejected cfg sk party anchor v r h

theorem ident_eq :
    ident = ⟨dep, 0, publicKeyId (derivePublicKey cfg.suite cfg.params key)⟩ := by
  unfold ident
  rw [custodianIdentity.public_eq_1]

theorem inhabited_foreign_caller :
    ∃ (cfg : SigningConfig) (sk : PqSecretKey) (party : Nat) (v : Vault),
      holdsIdentity cfg sk party v.identity = false :=
  ⟨cfg, key, 1, vault0, holdsIdentity_wrong_party cfg key 1 ident (by rw [ident_eq]; decide)⟩

/-- Old shape: with a live grant, release returns the signer's output for whatever party index
and key the caller supplies; the vault has no say. -/
theorem tooth_legacy_release_serves_any_caller (cfg : SigningConfig) (sk : PqSecretKey)
    (party : Nat) (v : Vault) (r : Intent) (hp : v.poisoned = false) (ha : v.active = some r) :
    ¬ ((legacyRelease cfg sk party v.durable.anchor v r).2 ≠
        (legacySign cfg sk 0 party r).map (fun sig => ⟨party, r, sig⟩)) := by
  intro hne
  apply hne
  simp only [legacyRelease, hp, ha, Bool.false_or, ne_eq, not_true_eq_false, decide_false,
    Bool.false_eq_true, ↓reduceIte]

#verify_inhabited release_foreign_identity_rejected_audited inhabited_foreign_caller
#tooth_pair release_foreign_identity_rejected_audited vs tooth_legacy_release_serves_any_caller

/-- Concrete positive admission uses nonempty payload, nonzero MAC slopes/pads,
and a nonzero share. This is not an all-zero field witness. -/
theorem legal_round : checkRound policy dep request burn.digest burn.openings = true := by
  have hd : burn.digest.length = 32 ∧ burn.digest = policy.digest request.session ∧
      burn.digest = roundCommitment dep request :=
    ⟨by
      show (roundCommitment dep request).length = 32
      rw [roundCommitment.public_eq_1]
      exact cshake256Bytes_length _ _, rfl, rfl⟩
  rw [checkRound.public_eq_1, decide_eq_true hd, Bool.true_and]
  decide +kernel

theorem legal_burn : mintGuard policy 10 vault0 burn = true := by
  have hid : vault0.identity.deploymentId = dep := by
    show ident.deploymentId = dep
    rw [ident_eq]
  unfold mintGuard
  rw [hid, show checkRound policy dep burn.intent burn.digest burn.openings = true from legal_round,
    Bool.and_true]
  decide +kernel

theorem nonzero_share : opening.opening.shareX ≠ towerZero 7 := by
  decide +kernel

theorem changed_share_rejected :
    checkRound policy dep request burn.digest
      [{ opening with opening := { opening.opening with shareX := towerZero 7 } }] = false := by
  let bad := { opening with opening := { opening.opening with shareX := towerZero 7 } }
  have hm : verifyBdozPairMac (policy.keys request.session request.round) bad.opening = false := by
    decide +kernel
  cases hh : checkRound policy dep request burn.digest [bad]
  · rfl
  · have hv := (checkRound_opening policy dep request burn.digest [bad] bad List.mem_cons_self hh).2
    rw [hm] at hv
    cases hv

theorem burned_before_release :
    (mint policy 10 0 vault0 burn).durable.spent = 3 ∧
    (mint policy 10 0 vault0 burn).durable.nextLeaf = 2 ∧
    (mint policy 10 0 vault0 burn).active = some request := by
  unfold mint
  rw [legal_burn]
  exact ⟨by decide +kernel, by decide +kernel, rfl⟩

theorem forget_cannot_refund :
    (forget (mint policy 10 0 vault0 burn)).durable.spent = 3 ∧
    (forget (mint policy 10 0 vault0 burn)).durable.nextLeaf = 2 ∧
    (release cfg key 0 1 (forget (mint policy 10 0 vault0 burn)) request).2 = none := by
  refine ⟨?_, ?_, ?_⟩
  · rw [forget_burns]
    exact burned_before_release.1
  · rw [forget_burns]
    exact burned_before_release.2.1
  · exact release_no_active cfg key 0 1 _ request rfl

/-- Run with Lean's evaluator; failures raise an error. No native-decision
axiom or assumed successful-signature premise enters any theorem. -/
def constructionCheck : IO Unit := do
  let v := mint policy 10 0 vault0 burn
  if checkRound policy dep { request with spend := 4 } burn.digest burn.openings then
    throw (IO.userError "old round commitment accepted changed spend")
  if checkRound policy dep { request with leaf := 2 } burn.digest burn.openings then
    throw (IO.userError "old round commitment accepted changed leaf")
  if checkRound policy dep { request with message := [0x78] } burn.digest burn.openings then
    throw (IO.userError "old round commitment accepted changed message")
  if checkRound policy (dep + 1) request burn.digest burn.openings then
    throw (IO.userError "round committed for one deployment accepted under another")
  if mintGuard policy 10 (initial { ident with deploymentId := dep + 1 }) burn then
    throw (IO.userError "vault of another deployment minted a grant from this deployment's round")
  let otherKey : PqSecretKey :=
    ⟨List.replicate 32 0x18, List.replicate 32 0x2A, List.replicate 32 0x44⟩
  unless (release cfg otherKey 0 1 v request).2.isNone do
    throw (IO.userError "vault released under a key other than the one in its identity")
  unless (release cfg key 1 1 v request).2.isNone do
    throw (IO.userError "vault released to a party other than the one in its identity")
  let (v', out) := release cfg key 0 1 v request
  let some c := out | throw (IO.userError "production signer exhausted its grind budget")
  let pks := fun _ => derivePublicKey cfg.suite cfg.params key
  unless verifyCertificate cfg pks dep request c do
    throw (IO.userError "issued production certificate failed verification")
  if verifyCertificate cfg pks (dep + 1) request c then
    throw (IO.userError "certificate issued for one deployment verified for another")
  if (submit cfg pks (dep + 1) 1 1 { capacity := 10 } request [c]).2 then
    throw (IO.userError "coordinator of another deployment consumed this deployment's grant")
  -- The pre-v3 shape, on the same key and request: the released approval is deployment-blind.
  let some legacySig := legacySign cfg key dep 0 request
    | throw (IO.userError "legacy-shape signer failed fixture")
  unless legacyVerify cfg (pks 0) (dep + 1) 0 request legacySig do
    throw (IO.userError "legacy-shape approval was unexpectedly deployment-bound")
  let (coord, accepted) := submit cfg pks dep 1 1 { capacity := 10 } request [c]
  unless accepted do
    throw (IO.userError "nonempty production quorum rejected")
  if (submit cfg pks dep 1 1 coord request [c]).2 then
    throw (IO.userError "consumed session replay accepted")
  if verifyCertificate cfg pks dep { request with session := 8 } c then
    throw (IO.userError "cross-session certificate accepted")
  let other := { request with session := 8 }
  if verifyCertificate cfg pks dep other { c with intent := other } then
    throw (IO.userError "signature survived relabeling to a new session")
  if acceptQuorum cfg pks dep 2 2 [] request [c, c] then
    throw (IO.userError "duplicate party counted twice toward quorum")
  if acceptQuorum cfg pks dep 1 1 [] request [] then
    throw (IO.userError "empty quorum accepted")
  if verify cfg (pks 0) dep 0 request { c.signature with msgTswCtr := 1 } then
    throw (IO.userError "malformed production signature accepted")
  unless (release cfg key 0 1 v' request).2.isNone do
    throw (IO.userError "released permit replay accepted")
  let peerKey := List.replicate 32 0x55
  let pair := demoQuorumSignedIntent peerKey 0 1 10 3 0 0x01
  let tx := pair.1
  let intent := transactionIntent tx 0 1
  let pol : RoundPolicy := ⟨fun _ _ => macKeys, [0], fun _ => roundCommitment dep intent⟩
  let op := { opening with session := intent.session }
  let st : PolicyVault := ⟨demoQuorumCustodian 0 peerKey (List.replicate 32 0x66), vault0⟩
  let admitted := mintTransaction pol 100 0 st tx pair.2 1000 0 1 [op]
  unless admitted.vault.active.isSome do
    throw (IO.userError "actual authenticated transaction failed custody admission")
  let (_, txOut) := executeTransaction cfg key pol 100 0 st tx pair.2 1000 0 1 [op]
  let some txCert := txOut | throw (IO.userError "admitted transaction failed production signing")
  unless decide (txCert.intent.spend = tx.amount_units ∧
      txCert.intent.message = toCanonicalSigningBytes tx) do
    throw (IO.userError "transaction amount/signing bytes detached from certificate")
  unless verifyCertificate cfg pks dep intent txCert do
    throw (IO.userError "transaction certificate failed production verification")
  if (submit cfg pks dep 1 1 { coord with capacity := 5 } intent [txCert]).2 then
    throw (IO.userError "second valid session exceeded coordinator aggregate spend cap")
  let excess := demoQuorumSignedIntent peerKey 0 1 11 61 0 0x02
  let excessIntent := transactionIntent excess.1 1 2
  let excessPol : RoundPolicy := ⟨fun _ _ => macKeys, [0], fun _ => roundCommitment dep excessIntent⟩
  let rejected := mintTransaction excessPol 100 1 admitted excess.1 excess.2 1000 1 2
    [{ opening with session := excessIntent.session, round := 1 }]
  unless rejected.vault.active.isNone && decide (rejected.vault.durable.spent = 3) do
    throw (IO.userError "excess transaction kept stale grant or changed durable accounting")
  let unauth := mintTransaction pol 100 0 st tx [] 1000 0 1 [op]
  unless unauth.vault.active.isNone do
    throw (IO.userError "unauthenticated transaction obtained a grant")
  IO.println "custody production check: authenticated transaction to cSHAKE/Jorts certificate passed; amount/message binding, full round context, deployment and vault-identity binding, invalid auth, spend cap, malformed signatures, quorum and replay guards passed"

end Qsag.Custody.Checks
end
set_option maxRecDepth 4096
#verify_constructive Qsag.Custody.Checks.legal_burn
#verify_constructive Qsag.Custody.Checks.changed_share_rejected
#verify_constructive Qsag.Custody.Checks.forget_cannot_refund
#eval Qsag.Custody.Checks.constructionCheck
