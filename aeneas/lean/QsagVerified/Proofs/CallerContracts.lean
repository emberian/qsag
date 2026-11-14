module
public import QsagVerified.Proofs.CredAndHdGuards
public import QsagVerified.Proofs.FtsSpnGuard
public import QsagVerified.Proofs.RssCutSession

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
end qsag_verified.proofs
