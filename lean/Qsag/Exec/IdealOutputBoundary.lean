module

public import Qsag.Exec.InteractiveUcEngine

/-!
# Ideal output and retry boundary

These results check the engine's release policy and complete WAL bindings. The
three-round fixtures are policy tests, not signature-security instances. Concrete
SLH cut reconstruction is discharged separately in `RssSlhFullSecurity`.

`SessionScheduleReq` has session, epoch, message, supplied randomness, and approver
fields. All are framed. It has no profile identifier, retry-attempt counter, or
transport-domain field; the encoding version tag does not supply those semantics.
-/

public section
namespace Qsag
set_option autoImplicit false

private theorem ucLeb128_injective {x y : Nat} (h : leb128 x = leb128 y) : x = y := by
  exact (leb128_prefix_inj (show leb128 x ++ [] = leb128 y ++ [] by simpa using h)).1

private theorem ucLeb128_list_injective : ∀ {xs ys : List Nat},
    xs.map leb128 = ys.map leb128 → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    have hp := List.cons.inj h
    have hh := ucLeb128_injective hp.1
    have ht := ucLeb128_list_injective hp.2
    rw [hh, ht]

theorem encodeUcSigningRequest_injective {a b : SessionScheduleReq}
    (h : encodeUcSigningRequest a = encodeUcSigningRequest b) : a = b := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  rcases hf with ⟨_, hs, he, hm, hr, ha, _⟩
  have hs' := ucLeb128_injective hs
  have he' := ucLeb128_injective he
  have ha' := ucLeb128_list_injective (encodeMultiFrame_injective ha)
  cases a
  cases b
  simp only at hs' he' hm hr ha'
  cases hs'; cases he'; cases hm; cases hr; cases ha'
  rfl

theorem encodeUcPqPublicKey_injective {a b : PqPublicKey}
    (h : encodeUcPqPublicKey a = encodeUcPqPublicKey b) : a = b := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  cases a
  cases b
  rcases hf with ⟨_, hs, hr, _⟩
  cases hs; cases hr
  rfl

theorem ucPqPublicKeyDigest_length (pk : PqPublicKey) :
    (ucPqPublicKeyDigest pk).length = 32 :=
  shake256Xof_length 32 (encodeUcPqPublicKey pk)

def ucPqPublicKeyDigest_collision_or_eq (a b : PqPublicKey)
    (h : ucPqPublicKeyDigest a = ucPqPublicKeyDigest b) :
    PSum (a = b) (HashCollisionWitness (shake256Xof 32)) := by
  if hab : a = b then exact .inl hab
  else
    exact .inr ⟨encodeUcPqPublicKey a, encodeUcPqPublicKey b,
      fun heq => hab (encodeUcPqPublicKey_injective heq), h⟩

/-- A fresh successful ideal release is the oracle output. Replay is excluded by
    its explicit fresh-grant premise, rather than assuming the initial cache honest. -/
theorem execIdealSession_fresh_output
    {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (oracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState) (cl : IdealClusterState PK)
    (adv : AdvState) (tape : SimTape) (wal : WalLatchState) (ep : Nat) (sig : ByteArray)
    (hFresh : walPreSignStep cl.honestWal (sim.pkDigestOf cl.tsig.pk)
      (A.scheduleSession adv).1.reqEpoch (sim.msgDigestOf (A.scheduleSession adv).1) =
      .ok wal (.authorizedFresh ep))
    (hOut : (execIdealSession oracle sim A cl adv tape).2.2.outcome = .signOk sig) :
    sig = oracle (A.scheduleSession adv).1 := by
  unfold execIdealSession at hOut
  dsimp only at hOut
  cases hApproval : validThresholdApproval cl.tsig (A.scheduleSession adv).1.honestApprovers
  · simp only [hApproval, Bool.not_false, ↓reduceIte] at hOut
    cases hOut
  · simp only [hApproval, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hFresh] at hOut
    cases hv : sim.simVerifyRound1 _ _ _ _ _ with
    | inl err => rw [hv] at hOut; cases hOut
    | inr r2 =>
      rw [hv] at hOut
      dsimp only at hOut
      cases hb : sim.simPreCutBarrier _ _ _ _ _ with
      | inl err => rw [hb] at hOut; cases hOut
      | inr r3 =>
        rw [hb] at hOut
        dsimp only at hOut
        cases hf : sim.finalizeIdealCut _ _ _ _ _ _ with
        | inl err => rw [hf] at hOut; cases hOut
        | inr out =>
          rw [hf] at hOut
          cases hOut
          exact sim.finalizeIdealCut_output _ _ _ _ _ _ _ hf

/-- The first release and its exact retry are reachable, while a different intent
    at the same epoch cannot replay the cached output. -/
theorem ucWal_exact_retry_and_conflict (key : List UInt8) (sig : ByteArray)
    (req changed : SessionScheduleReq) (hEpoch : req.reqEpoch = 0)
    (hChangedEpoch : changed.reqEpoch = 0) (hDifferent : changed ≠ req) :
    let initial := initWalLatchState key
    let committed := walCommitAuthorized initial 0 (encodeUcSigningRequest req) sig
    walCommitBeforeRelease initial key 0 (encodeUcSigningRequest req) sig = .ok committed sig ∧
    walPreSignStep committed key req.reqEpoch (encodeUcSigningRequest req) =
      .ok committed (.replayCached sig) ∧
    walPreSignStep committed key changed.reqEpoch (encodeUcSigningRequest changed) =
      .err committed .staleOrOutOfOrderEpoch := by
  have hNe : encodeUcSigningRequest changed ≠ encodeUcSigningRequest req :=
    fun heq => hDifferent (encodeUcSigningRequest_injective heq)
  simp only [walCommitBeforeRelease, walPreSignStep, walCommitAuthorized, initWalLatchState,
    hEpoch, hChangedEpoch, hNe, decide_false, decide_true, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true, Nat.reduceBEq]
  exact ⟨trivial, trivial, rfl⟩

/-- The old truncation aliases these requests; the complete intent rejects the
    same-prefix/different-suffix replay and still permits an exact retry. -/
theorem tooth_uc_request_suffix_binding :
    let a : SessionScheduleReq := ⟨7, 0, List.replicate 32 9 ++ [1], [3], [0]⟩
    let b : SessionScheduleReq := ⟨7, 0, List.replicate 32 9 ++ [2], [3], [0]⟩
    a.msg.take 32 = b.msg.take 32 ∧
    encodeUcSigningRequest a ≠ encodeUcSigningRequest b := by
  refine ⟨by decide, ?_⟩
  intro h
  have heq := encodeUcSigningRequest_injective h
  have hMsg := congrArg SessionScheduleReq.msg heq
  have : (List.replicate 32 9 ++ [1] : List UInt8) ≠ List.replicate 32 9 ++ [2] := by decide
  exact this hMsg

/-- The key preimage binds the root even with an identical 32-byte seed. The
    resulting digest inequality requires hash collision resistance, not injectivity
    of SHAKE into 256 bits. -/
theorem tooth_uc_public_root_binding :
    let a : PqPublicKey := ⟨List.replicate 32 9, [1]⟩
    let b : PqPublicKey := ⟨List.replicate 32 9, [2]⟩
    (a.pkSeed ++ a.pkRoot).take 32 = (b.pkSeed ++ b.pkRoot).take 32 ∧
    encodeUcPqPublicKey a ≠ encodeUcPqPublicKey b := by
  refine ⟨by decide, ?_⟩
  intro h
  have heq := encodeUcPqPublicKey_injective h
  have hRoot := congrArg PqPublicKey.pkRoot heq
  cases hRoot

/-- The regression is consumed by both active Shamir constructors, so restoring
    their old message truncation fails this test even if the encoder remains. -/
theorem tooth_activeShamir_suffix_binding
    (t : Nat) (corruptPts checkPts : List Goldilocks) (maxGates : Nat)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (pkSeed : List UInt8)
    (grindLimit : Nat) (ser : Option PqHashSig → ByteArray) :
    let proto := activeShamirThresholdProtocol t corruptPts checkPts maxGates
      suite params o pkSeed grindLimit ser
    let sim := activeShamirBlackBoxSimulator t corruptPts checkPts maxGates
    let a : SessionScheduleReq := ⟨7, 0, List.replicate 32 9 ++ [1], [3], [0]⟩
    let b : SessionScheduleReq := ⟨7, 0, List.replicate 32 9 ++ [2], [3], [0]⟩
    proto.msgDigestOf a ≠ proto.msgDigestOf b ∧
    sim.msgDigestOf a ≠ sim.msgDigestOf b := by
  intro proto sim a b
  dsimp only [proto, sim, activeShamirThresholdProtocol, activeShamirBlackBoxSimulator]
  exact ⟨tooth_uc_request_suffix_binding.2, tooth_uc_request_suffix_binding.2⟩

/-- Both constructors pin the full key encoding's digest. Equality for distinct
    roots is consequently a hash-collision obligation, not a prefix alias. -/
theorem activeShamir_full_key_binding
    (t : Nat) (corruptPts checkPts : List Goldilocks) (maxGates : Nat)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (pkSeed : List UInt8)
    (grindLimit : Nat) (ser : Option PqHashSig → ByteArray) :
    (activeShamirThresholdProtocol t corruptPts checkPts maxGates
      suite params o pkSeed grindLimit ser).pkDigestOf = ucPqPublicKeyDigest ∧
    (activeShamirBlackBoxSimulator t corruptPts checkPts maxGates).pkDigestOf =
      ucPqPublicKeyDigest := by
  dsimp only [activeShamirThresholdProtocol, activeShamirBlackBoxSimulator]
  exact ⟨rfl, rfl⟩

/-- Engine-policy fixture, not a signature security instance. Deliberately proposes
    unrelated output bytes so the release boundary has something to reject. -/
def substitutionSimulator (proposal : ByteArray) (abort : Bool) :
    BlackBoxUcSimulator Unit Unit Unit Unit Unit where
  pkDigestOf := fun _ => List.replicate 32 0
  msgDigestOf := encodeUcSigningRequest
  simRound1 := fun _ _ _ _ _ => ([(0, packWire [1])], ())
  simVerifyRound1 := fun _ _ _ _ _ => .inr ()
  simRound2 := fun _ _ _ _ _ => ([(0, packWire [2])], ())
  simPreCutBarrier := fun _ _ _ _ _ => .inr ()
  simRound3 := fun _ _ _ _ sig _ => ([(0, sig)], ())
  simFinalizeCut := fun _ _ _ _ _ _ =>
    if abort then .inl (.cutOpenMismatch 0) else .inr proposal

def substitutionRequest : SessionScheduleReq := ⟨7, 0, [1, 2], [3], [0]⟩

def substitutionAdversary : UcRushingAdversary Unit where
  scheduleSession := fun _ => (substitutionRequest, ())
  rushRound1 := fun _ _ => (fun _ => packWire [], ())
  rushRound2 := fun _ _ => (fun _ => packWire [], ())
  rushRound3 := fun _ _ => (fun _ => packWire [], ())
  observeOutcome := fun _ _ => ()

def substitutionInitial : IdealClusterState Unit :=
  ⟨⟨(), 1, 1, [], [], []⟩, initWalLatchState (List.replicate 32 0), 0⟩

/-- Restoring the old direct delivery of the callback's payload breaks this
    nonempty substitution case. -/
theorem tooth_ideal_substitution_blocked :
    (substitutionSimulator (packWire [9]) false).simFinalizeCut () substitutionRequest ()
      (packWire [7]) [] [] = .inr (packWire [9]) ∧
    (substitutionSimulator (packWire [9]) false).finalizeIdealCut () substitutionRequest ()
      (packWire [7]) [] [] = .inr (packWire [7]) ∧
    packWire [9] ≠ packWire [7] := by
  exact ⟨rfl, rfl, by decide⟩

/-- A complete three-round successful run releases and caches the oracle bytes,
    even when the simulator proposes different bytes. -/
theorem witness_ideal_release_uses_oracle (sig proposal : ByteArray) :
    let run := execIdealSession (fun _ => sig) (substitutionSimulator proposal false)
      substitutionAdversary substitutionInitial () ()
    run.2.2.outcome = .signOk sig ∧
    run.2.2.honestRound3 = [(0, sig)] ∧
    run.1.honestWal.latchedRecord = some (0, encodeUcSigningRequest substitutionRequest, sig) ∧
    run.1.maskSessionCursor = 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The same reachable setup also permits selective abort after exposing the
    ideal output; it records the query and does not cache a successful release. -/
theorem witness_ideal_abort_retains_query (sig proposal : ByteArray) :
    let run := execIdealSession (fun _ => sig) (substitutionSimulator proposal true)
      substitutionAdversary substitutionInitial () ()
    run.2.2.outcome = .abort (.cutOpenMismatch 0) ∧
    run.2.2.honestRound3 = [(0, sig)] ∧
    run.1.tsig.approvedMsgs = [substitutionRequest.msg] ∧
    run.1.honestWal.latchedRecord = none ∧
    run.1.honestWal.poisoned = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#verify_constructive encodeUcSigningRequest_injective encodeUcPqPublicKey_injective
  ucPqPublicKeyDigest_length
  execIdealSession_fresh_output ucWal_exact_retry_and_conflict
  tooth_uc_request_suffix_binding tooth_uc_public_root_binding
  tooth_activeShamir_suffix_binding activeShamir_full_key_binding
  tooth_ideal_substitution_blocked witness_ideal_release_uses_oracle witness_ideal_abort_retains_query

end Qsag
end
