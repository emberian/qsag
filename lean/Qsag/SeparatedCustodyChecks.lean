module
public import Qsag.SeparatedCustodyPolicy
import all Qsag.SeparatedCustodySpine
import all Qsag.CompleteMediationBoundary
import all Qsag.SeparatedCustodyCore
import all Qsag.HashSigs
import all Qsag.MaliciousSecurity
import all Qsag.SeparatedCustodyPolicy
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

def macKeys : BdozVerifierKeys :=
  ⟨towerOne 7, towerOne 7, fun _ => (towerOne 7, towerOne 7)⟩
def policy : RoundPolicy :=
  ⟨fun _ _ => macKeys, [0], fun _ => roundCommitment request⟩
def opening : RoundOpening :=
  ⟨7, 0, ⟨0, towerOne 7, towerZero 7, towerZero 7⟩⟩
def burn : Burn := ⟨request, roundCommitment request, [opening]⟩

/-- Concrete positive admission uses nonempty payload, nonzero MAC slopes/pads,
and a nonzero share. This is not an all-zero field witness. -/
theorem legal_round : checkRound policy request burn.digest burn.openings = true := by
  have hd : burn.digest.length = 32 ∧ burn.digest = policy.digest request.session ∧
      burn.digest = roundCommitment request :=
    ⟨cshake256Bytes_length _ _, rfl, rfl⟩
  unfold checkRound
  rw [decide_eq_true hd, Bool.true_and]
  decide +kernel

theorem legal_burn : mintGuard policy 10 initial burn = true := by
  unfold mintGuard
  rw [show burn.intent = request from rfl, legal_round, Bool.and_true]
  decide +kernel

theorem nonzero_share : opening.opening.shareX ≠ towerZero 7 := by
  decide +kernel

theorem changed_share_rejected :
    checkRound policy request burn.digest
      [{ opening with opening := { opening.opening with shareX := towerZero 7 } }] = false := by
  let bad := { opening with opening := { opening.opening with shareX := towerZero 7 } }
  have hm : verifyBdozPairMac (policy.keys request.session request.round) bad.opening = false := by
    decide +kernel
  cases hh : checkRound policy request burn.digest [bad]
  · rfl
  · have hv := (checkRound_opening policy request burn.digest [bad] bad List.mem_cons_self hh).2
    rw [hm] at hv
    cases hv

theorem burned_before_release :
    (mint policy 10 0 initial burn).durable.spent = 3 ∧
    (mint policy 10 0 initial burn).durable.nextLeaf = 2 ∧
    (mint policy 10 0 initial burn).active = some request := by
  unfold mint
  rw [legal_burn]
  decide +kernel

theorem forget_cannot_refund :
    (forget (mint policy 10 0 initial burn)).durable.spent = 3 ∧
    (forget (mint policy 10 0 initial burn)).durable.nextLeaf = 2 ∧
    (release cfg key 0 1 (forget (mint policy 10 0 initial burn)) request).2 = none := by
  refine ⟨?_, ?_, ?_⟩
  · rw [forget_burns]
    exact burned_before_release.1
  · rw [forget_burns]
    exact burned_before_release.2.1
  · exact release_no_active cfg key 0 1 _ request rfl

/-- Run with Lean's evaluator; failures raise an error. No native-decision
axiom or assumed successful-signature premise enters any theorem. -/
def constructionCheck : IO Unit := do
  let v := mint policy 10 0 initial burn
  if checkRound policy { request with spend := 4 } burn.digest burn.openings then
    throw (IO.userError "old round commitment accepted changed spend")
  if checkRound policy { request with leaf := 2 } burn.digest burn.openings then
    throw (IO.userError "old round commitment accepted changed leaf")
  if checkRound policy { request with message := [0x78] } burn.digest burn.openings then
    throw (IO.userError "old round commitment accepted changed message")
  let (v', out) := release cfg key 0 1 v request
  let some c := out | throw (IO.userError "production signer exhausted its grind budget")
  let pks := fun _ => derivePublicKey cfg.suite cfg.params key
  unless verifyCertificate cfg pks request c do
    throw (IO.userError "issued production certificate failed verification")
  let (coord, accepted) := submit cfg pks 1 1 { capacity := 10 } request [c]
  unless accepted do
    throw (IO.userError "nonempty production quorum rejected")
  if (submit cfg pks 1 1 coord request [c]).2 then
    throw (IO.userError "consumed session replay accepted")
  if verifyCertificate cfg pks { request with session := 8 } c then
    throw (IO.userError "cross-session certificate accepted")
  let other := { request with session := 8 }
  if verifyCertificate cfg pks other { c with intent := other } then
    throw (IO.userError "signature survived relabeling to a new session")
  if acceptQuorum cfg pks 2 2 [] request [c, c] then
    throw (IO.userError "duplicate party counted twice toward quorum")
  if acceptQuorum cfg pks 1 1 [] request [] then
    throw (IO.userError "empty quorum accepted")
  if verify cfg (pks 0) 0 request { c.signature with msgTswCtr := 1 } then
    throw (IO.userError "malformed production signature accepted")
  unless (release cfg key 0 1 v' request).2.isNone do
    throw (IO.userError "released permit replay accepted")
  let peerKey := List.replicate 32 0x55
  let pair := demoQuorumSignedIntent peerKey 0 1 10 3 0 0x01
  let tx := pair.1
  let intent := transactionIntent tx 0 1
  let pol : RoundPolicy := ⟨fun _ _ => macKeys, [0], fun _ => roundCommitment intent⟩
  let op := { opening with session := intent.session }
  let st : PolicyVault := ⟨demoQuorumCustodian 0 peerKey (List.replicate 32 0x66), initial⟩
  let admitted := mintTransaction pol 100 0 st tx pair.2 1000 0 1 [op]
  unless admitted.vault.active.isSome do
    throw (IO.userError "actual authenticated transaction failed custody admission")
  let (_, txOut) := executeTransaction cfg key pol 100 0 st tx pair.2 1000 0 1 [op]
  let some txCert := txOut | throw (IO.userError "admitted transaction failed production signing")
  unless decide (txCert.intent.spend = tx.amount_units ∧
      txCert.intent.message = toCanonicalSigningBytes tx) do
    throw (IO.userError "transaction amount/signing bytes detached from certificate")
  unless verifyCertificate cfg pks intent txCert do
    throw (IO.userError "transaction certificate failed production verification")
  if (submit cfg pks 1 1 { coord with capacity := 5 } intent [txCert]).2 then
    throw (IO.userError "second valid session exceeded coordinator aggregate spend cap")
  let excess := demoQuorumSignedIntent peerKey 0 1 11 61 0 0x02
  let excessIntent := transactionIntent excess.1 1 2
  let excessPol : RoundPolicy := ⟨fun _ _ => macKeys, [0], fun _ => roundCommitment excessIntent⟩
  let rejected := mintTransaction excessPol 100 1 admitted excess.1 excess.2 1000 1 2
    [{ opening with session := excessIntent.session, round := 1 }]
  unless rejected.vault.active.isNone && decide (rejected.vault.durable.spent = 3) do
    throw (IO.userError "excess transaction kept stale grant or changed durable accounting")
  let unauth := mintTransaction pol 100 0 st tx [] 1000 0 1 [op]
  unless unauth.vault.active.isNone do
    throw (IO.userError "unauthenticated transaction obtained a grant")
  IO.println "custody production check: authenticated transaction to cSHAKE/Jorts certificate passed; amount/message binding, full round context, invalid auth, spend cap, malformed signatures, quorum and replay guards passed"

end Qsag.Custody.Checks
end
set_option maxRecDepth 4096
#verify_constructive Qsag.Custody.Checks.legal_burn
#verify_constructive Qsag.Custody.Checks.changed_share_rejected
#verify_constructive Qsag.Custody.Checks.forget_cannot_refund
#eval Qsag.Custody.Checks.constructionCheck
