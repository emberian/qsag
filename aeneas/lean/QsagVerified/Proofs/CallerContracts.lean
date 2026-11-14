module
public import QsagVerified.Proofs.CredAndHdGuards
public import QsagVerified.Proofs.FtsSpnGuard
public import QsagVerified.Proofs.RssCutSession
public import QsagVerified.Proofs.MultiTurnMediationAndReachability

/-!
# Caller-computed predicates at the MIR boundary

These contracts state the obligations of unextracted callers. They do not assert that
receiving a Boolean establishes polynomial norms, durable storage, or MAC correctness.
`PolicyAndAddr` checks amounts, pins and monotone nonces directly; its pins still require
trusted provisioning. `TowerBdoz` evaluates its supplied field operands directly; the
relation of those operands to the caller's wire transcript remains a caller obligation.
The HD guard checks supplied commitments/residuals, not the derivation of those residuals.
The authenticated belt computes its own tags; key provisioning is `BeltProvisionedKeys`.
-/
public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result
open qsag_verified

/-- One-way soundness is sufficient for safety; completeness is a separate obligation. -/
def BooleanContract (reported : Bool) (Holds : Prop) : Prop := reported = true → Holds

/-- Each ML-DSA flag has its own semantic obligation for the exact submitted checks. -/
structure MlDsaCallerContract
    (ZNorm R0Norm W1Match CommitmentBound : cred_and_hd_guards.MlDsaBarrierChecks → Prop)
    (c : cred_and_hd_guards.MlDsaBarrierChecks) : Prop where
  zNorm : BooleanContract c.z_norm_ok (ZNorm c)
  r0Norm : BooleanContract c.r0_norm_ok (R0Norm c)
  w1Match : BooleanContract c.w1_match (W1Match c)
  commitmentBound : BooleanContract c.u_com_bound (CommitmentBound c)

/-- Semantic ML-DSA release safety over all accepted turns, conditional on the four
caller computations. Rejection wiping is provided by the underlying trace theorem. -/
theorem mldsa_release_under_caller_contract
    (ZNorm R0Norm W1Match CommitmentBound : cred_and_hd_guards.MlDsaBarrierChecks → Prop)
    (sid : Array Std.U8 32#usize) (attempt : Std.U32) (z : Array Std.U8 32#usize)
    (s t : cred_and_hd_guards.MlDsaReleaseGate)
    (turns : List (MirTurn cred_and_hd_guards.MlDsaBarrierChecks
      (Array Std.U8 32#usize) cred_and_hd_guards.CredHdGuardError))
    (hn : cred_and_hd_guards.MlDsaReleaseGate.new_sealed sid attempt z = .ok s)
    (ht : MirTrace (adaptStateResult cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share) s turns t)
    (hc : ∀ p ∈ mirAcceptedPairs turns,
      MlDsaCallerContract ZNorm R0Norm W1Match CommitmentBound p.1) :
    ∀ p ∈ mirAcceptedPairs turns,
      ZNorm p.1 ∧ R0Norm p.1 ∧ W1Match p.1 ∧ CommitmentBound p.1 ∧ p.2 = z := by
  intro p hp
  obtain ⟨_, _, hz, hr, hw, hu, hout⟩ :=
    (mldsa_gate_blocks_z_on_rejection_mir sid attempt z s t turns hn ht).2.2 p hp
  have h := hc p hp
  exact ⟨h.zNorm hz, h.r0Norm hr, h.w1Match hw, h.commitmentBound hu, hout⟩

/-- Zero residuals imply the external MAC relation only under this caller contract. -/
def FtsResidualContract (Holds : Array Std.U8 32#usize → Prop) : FtsMacStepInput → Prop
  | .verifyMac sid lo hi => lo = 0#u128 → hi = 0#u128 → Holds sid
  | _ => True

/-- Multi-turn semantic FTS release safety explicitly separates the reported round
count from evidence that all rounds and the external MAC relation were computed. -/
theorem fts_release_under_caller_contract
    (Holds : Array Std.U8 32#usize → Prop) (RoundsComplete : Prop)
    (sid : Array Std.U8 32#usize) (rounds : Std.U8) (lo hi : Std.U128)
    (s t : fts_spn_guard.FtsDeferredMacSession)
    (turns : List (MirTurn FtsMacStepInput FtsMacStepOutput fts_spn_guard.FtsGuardError))
    (hn : fts_spn_guard.FtsDeferredMacSession.new_spn48_evaluated sid rounds lo hi = .ok s)
    (ht : MirTrace (adaptStateResult mirFtsMacStep) s turns t)
    (hrounds : rounds = 48#u8 → RoundsComplete)
    (hc : ∀ p ∈ mirAcceptedPairs turns, FtsResidualContract Holds p.1) :
    ∀ inp outLo outHi, (inp, .outputReleased outLo outHi) ∈ mirAcceptedPairs turns →
      RoundsComplete ∧ Holds sid ∧ outLo = lo ∧ outHi = hi := by
  intro inp outLo outHi hp
  obtain ⟨hr, hl, hh, hm, _⟩ :=
    (fts_spn_output_implies_intermediate_mac_ok sid rounds lo hi s t turns hn ht).2.1 inp outLo outHi hp
  exact ⟨hrounds hr, hc _ hm rfl rfl, hl, hh⟩

/-- The RSS guard checks scalar zeros; their semantic meaning is provided by the caller. -/
def RssResidualContract (Holds : Array Std.U8 32#usize → Prop) : rss_cut_session.RssCutStepInput → Prop
  | .AdvanceRound3VerifyConsistency sid lo hi dzk =>
    lo = 0#u128 → hi = 0#u128 → dzk = 0#u64 → Holds sid
  | _ => True

theorem rss_release_under_caller_contract
    (Holds : Array Std.U8 32#usize → Prop)
    (sid comm : Array Std.U8 32#usize) (s t : rss_cut_session.RssCutGateSession)
    (turns : List (MirTurn rss_cut_session.RssCutStepInput
      rss_cut_session.RssCutStepOutput rss_cut_session.RssCutError))
    (hn : rss_cut_session.RssCutGateSession.new_round1_committed sid comm = .ok s)
    (ht : MirTrace (adaptStateResult rss_cut_session.RssCutGateSession.step) s turns t)
    (hc : ∀ p ∈ mirAcceptedPairs turns, RssResidualContract Holds p.1) :
    ∀ inp cut, (inp, .CutReleased cut) ∈ mirAcceptedPairs turns → Holds sid := by
  intro inp cut hp
  obtain ⟨_, _, hm⟩ :=
    (rss_cut_session_never_releases_unverified_cut sid comm s t turns hn ht).2.1 inp cut hp
  exact hc _ hm rfl rfl rfl

/-- An explicit three-call MIR transcript, indexed by the exact candidate. -/
def rssConcreteTurns (sid comm cut : Array Std.U8 32#usize) :
    List (MirTurn rss_cut_session.RssCutStepInput
      rss_cut_session.RssCutStepOutput rss_cut_session.RssCutError) :=
  [.accepted (.AdvanceRound2Chi sid comm cut) .Round2Ready,
   .accepted (.AdvanceRound3VerifyConsistency sid 0#u128 0#u128 0#u64) .Round3Verified,
   .accepted (.OpenVerifiedCut sid) (.CutReleased cut)]

/-- Concrete composition discharges the guard's phase, session and candidate-flow
obligations. It works for every candidate: zero residual inputs alone cannot establish
an external MAC relation on that candidate. -/
theorem rss_concrete_three_step_mir (sid comm cut : Array Std.U8 32#usize) :
    ∃ s t,
      rss_cut_session.RssCutGateSession.new_round1_committed sid comm = .ok s ∧
      MirTrace (adaptStateResult rss_cut_session.RssCutGateSession.step)
        s (rssConcreteTurns sid comm cut) t ∧
      t.phase = .CutOpened ∧ t.poisoned = false ∧
      t.candidate_cut_bytes = Array.repeat 32#usize 0#u8 := by
  let s : rss_cut_session.RssCutGateSession :=
    { session_id := sid, phase := .Round1MaskCommitted, mask_commitment := comm,
      candidate_cut_bytes := Array.repeat 32#usize 0#u8,
      consistency_verified := false, poisoned := false }
  let s1 : rss_cut_session.RssCutGateSession :=
    { s with
      phase := .Round2ChiEvaluated, candidate_cut_bytes := cut, consistency_verified := false }
  let s2 : rss_cut_session.RssCutGateSession :=
    { s1 with phase := .Round3ConsistencyVerified, consistency_verified := true }
  let s3 : rss_cut_session.RssCutGateSession :=
    { s2 with phase := .CutOpened, candidate_cut_bytes := Array.repeat 32#usize 0#u8 }
  have h1 : rss_cut_session.RssCutGateSession.step s (.AdvanceRound2Chi sid comm cut) =
      .ok (s1, .Ok .Round2Ready) := rss_step_round2_accepts s cut rfl rfl
  have h2 : rss_cut_session.RssCutGateSession.step s1
      (.AdvanceRound3VerifyConsistency sid 0#u128 0#u128 0#u64) =
      .ok (s2, .Ok .Round3Verified) := rss_step_round3_accepts s1 rfl rfl
  have h3 : rss_cut_session.RssCutGateSession.step s2 (.OpenVerifiedCut sid) =
      .ok (s3, .Ok (.CutReleased cut)) := rss_step_open_accepts s2 rfl rfl rfl
  have e1 : adaptStateResult rss_cut_session.RssCutGateSession.step s
      (.AdvanceRound2Chi sid comm cut) = .ok (.accepted s1 .Round2Ready) := by
    simp only [adaptStateResult, h1, result_bind_ok]
  have e2 : adaptStateResult rss_cut_session.RssCutGateSession.step s1
      (.AdvanceRound3VerifyConsistency sid 0#u128 0#u128 0#u64) =
      .ok (.accepted s2 .Round3Verified) := by
    simp only [adaptStateResult, h2, result_bind_ok]
  have e3 : adaptStateResult rss_cut_session.RssCutGateSession.step s2
      (.OpenVerifiedCut sid) = .ok (.accepted s3 (.CutReleased cut)) := by
    simp only [adaptStateResult, h3, result_bind_ok]
  exact ⟨s, s3, rfl, MirTrace.accept e1 (MirTrace.accept e2 (MirTrace.accept e3 (.nil s3))),
    rfl, rfl, rfl⟩

/-- A concrete caller contract that the available MIR really can discharge: the
successful residual-check input names the same session as the candidate transcript.
No assumption about accepted inputs is required. -/
theorem rss_concrete_session_contract (sid comm cut : Array Std.U8 32#usize) :
    ∀ p ∈ mirAcceptedPairs (rssConcreteTurns sid comm cut),
      RssResidualContract (fun checkedSid => checkedSid = sid) p.1 := by
  intro p hp
  simp only [rssConcreteTurns, mirAcceptedPairs, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl
  · trivial
  · exact fun _ _ _ => rfl
  · trivial

/-- Instantiate the generic release API on an actual three-step MIR execution, with
its session-binding contract proved above rather than supplied by the caller. This
only discharges session binding; external consistency still needs extracted producers. -/
theorem rss_concrete_release_contract_instantiated (sid comm cut : Array Std.U8 32#usize) :
    ∃ s t,
      rss_cut_session.RssCutGateSession.new_round1_committed sid comm = .ok s ∧
      MirTrace (adaptStateResult rss_cut_session.RssCutGateSession.step)
        s (rssConcreteTurns sid comm cut) t ∧
      ∀ inp out, (inp, .CutReleased out) ∈
        mirAcceptedPairs (rssConcreteTurns sid comm cut) → inp = .OpenVerifiedCut sid ∧ out = cut := by
  obtain ⟨s, t, hn, ht, _⟩ := rss_concrete_three_step_mir sid comm cut
  have hsession := rss_release_under_caller_contract (fun checkedSid => checkedSid = sid)
    sid comm s t (rssConcreteTurns sid comm cut) hn ht
    (rss_concrete_session_contract sid comm cut)
  refine ⟨s, t, hn, ht, ?_⟩
  intro inp out hp
  have _ := hsession inp out hp
  simpa [rssConcreteTurns, mirAcceptedPairs] using hp

/-- The existing semantic contract cannot be erased: an actual accepted multi-step
execution exists while the contract for an arbitrary external predicate is false.
This rules out replacing the missing producer proof with unconditional flag trust. -/
theorem rss_concrete_mir_does_not_establish_arbitrary_semantics
    (sid comm cut : Array Std.U8 32#usize) :
    ∃ s t,
      rss_cut_session.RssCutGateSession.new_round1_committed sid comm = .ok s ∧
      MirTrace (adaptStateResult rss_cut_session.RssCutGateSession.step)
        s (rssConcreteTurns sid comm cut) t ∧
      ¬ (∀ p ∈ mirAcceptedPairs (rssConcreteTurns sid comm cut),
        RssResidualContract (fun _ => False) p.1) := by
  obtain ⟨s, t, hn, ht, _⟩ := rss_concrete_three_step_mir sid comm cut
  refine ⟨s, t, hn, ht, ?_⟩
  intro hc
  exact hc (.AdvanceRound3VerifyConsistency sid 0#u128 0#u128 0#u64, .Round3Verified)
    (by simp [rssConcreteTurns, mirAcceptedPairs]) rfl rfl rfl

end qsag_verified.proofs
