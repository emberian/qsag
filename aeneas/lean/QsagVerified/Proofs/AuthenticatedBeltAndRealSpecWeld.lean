module

public import QsagVerified.Proofs.RealSpecFieldWeld
public import QsagVerified.Proofs.RssCutSession
public import Qsag.MirSpecBridge

/-!
# Guard weld between the Aeneas extraction and the `Qsag` protocol specifications

This module has both `QsagVerified.Funs` (the Charon/Aeneas output for `aeneas/qsag-verified`) and
`Qsag.MirSpecBridge` in a single kernel environment. `qsag_aeneas` requires the `qsag` Lake
package (`aeneas/lean/lakefile.toml`); nothing in `qsag` imports the extraction.

Every theorem below has an extracted function on one side and a `Qsag` definition on the other.
There is no intermediate structure standing in for the Rust: the concrete machine is the extracted
step function itself, viewed as a `Qsag.PartyMachine` by `extractedPartyMachine`
(`RealSpecFieldWeld.lean`).

Scope. This file welds the cut-session guard `rss_cut_session.RssCutGateSession.step` against
`Qsag.mirRssCutMachine`. The primitive welds live beside it: Goldilocks in
`RealSpecFieldWeld.lean`, the binary towers in `RealSpecTowerWeld.lean`, the Keccak permutation in
`RealSpecKeccakWeld.lean` and the WOTS+C digit check in `RealSpecHashWeld.lean`. `EpochLatch` has
no weld, and `StatefulVelocityGuard` differs from `Qsag.MirPolicyGuardState`
(`RealSpecGuardBoundary.lean` proves the mismatch). Production crates link the verified crate and
call some of its functions; a theorem here transfers to production only for a function production
actually calls.

Build. This module belongs to the `QsagCustodyWeld` library, because it needs the whole import
cone of `Qsag.MirSpecBridge`; the primitive welds are the separate `QsagSpecWeld` library.
-/

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-! ## 3. `RssCutGateSession.step` against `Qsag.mirRssCutMachine` -/

/-- A Rust `[u8; 32]` as the spec-side `Qsag.Bytes32`. -/
def bytes32OfArray (a : Array Std.U8 32#usize) : Qsag.Bytes32 :=
  ⟨(arrayU8ToBytes a).toArray, by rw [List.size_toArray, arrayU8ToBytes_length]; rfl⟩

theorem bytes32OfArray_injective {a b : Array Std.U8 32#usize}
    (h : bytes32OfArray a = bytes32OfArray b) : a = b := by
  have h2 : (arrayU8ToBytes a).toArray = (arrayU8ToBytes b).toArray := congrArg Vector.toArray h
  exact arrayU8ToBytes_injective (congrArg Array.toList h2)

@[local simp] private theorem bytes32OfArray_inj (a b : Array Std.U8 32#usize) :
    bytes32OfArray a = bytes32OfArray b ↔ a = b :=
  ⟨bytes32OfArray_injective, congrArg bytes32OfArray⟩

private theorem bytes32OfArray_zero :
    bytes32OfArray (Array.repeat 32#usize 0#u8) = Qsag.zeroBytes32 := by
  rw [Qsag.zeroBytes32_eq]
  rfl

@[local simp] private theorem u128_bv_eq_zero (x : Std.U128) : x.bv = 0 ↔ x = 0#u128 :=
  ⟨fun h => UScalar.ext h, fun h => by rw [h]; rfl⟩

@[local simp] private theorem u64_ofBitVec_eq_zero (x : Std.U64) :
    UInt64.ofBitVec x.bv = 0 ↔ x = 0#u64 :=
  ⟨fun h => UScalar.ext (congrArg UInt64.toBitVec h), fun h => by rw [h]; rfl⟩

/-- Phase abstraction, constructor for constructor. -/
def rssCutPhaseAbs : rss_cut_session.RssCutPhase → Qsag.MirRssCutPhase
  | .Round1MaskCommitted => .round1MaskCommitted
  | .Round2ChiEvaluated => .round2ChiEvaluated
  | .Round3ConsistencyVerified => .round3ConsistencyVerified
  | .CutOpened => .cutOpened
  | .Poisoned => .poisoned

/-- State abstraction, field for field. -/
def rssCutStateAbs (st : rss_cut_session.RssCutGateSession) : Qsag.MirRssCutSession :=
  { sessionId := bytes32OfArray st.session_id
    phase := rssCutPhaseAbs st.phase
    maskCommitment := bytes32OfArray st.mask_commitment
    candidateCutBytes := bytes32OfArray st.candidate_cut_bytes
    consistencyVerified := st.consistency_verified
    poisoned := st.poisoned }

/-- Input encoding. The Round-3 residuals pass through as the raw bit-vectors the guard receives. -/
def rssCutInputAbs : rss_cut_session.RssCutStepInput → Qsag.MirRssCutInput
  | .AdvanceRound2Chi reqSid recomputed cand =>
    .advanceRound2Chi (bytes32OfArray reqSid) (bytes32OfArray recomputed) (bytes32OfArray cand)
  | .AdvanceRound3VerifyConsistency reqSid lo hi dzk =>
    .advanceRound3VerifyConsistency (bytes32OfArray reqSid) lo.bv hi.bv (UInt64.ofBitVec dzk.bv)
  | .OpenVerifiedCut reqSid => .openVerifiedCut (bytes32OfArray reqSid)

/-- Output encoding. -/
def rssCutOutputAbs : rss_cut_session.RssCutStepOutput → Qsag.MirRssCutOutput
  | .Round2Ready => .round2Ready
  | .Round3Verified => .round3Verified
  | .CutReleased cut => .cutReleased (bytes32OfArray cut)

/-- The state abstraction of `new_round1_committed` is the spec's Round-1 state. -/
theorem rssCutStateAbs_new_round1_committed (sid comm : Array Std.U8 32#usize)
    (st : rss_cut_session.RssCutGateSession)
    (h : rss_cut_session.RssCutGateSession.new_round1_committed sid comm = .ok st) :
    rssCutStateAbs st =
      Qsag.MirRssCutSession.round1Committed (bytes32OfArray sid) (bytes32OfArray comm) := by
  unfold rss_cut_session.RssCutGateSession.new_round1_committed at h
  injection h with h
  subst h
  rw [Qsag.MirRssCutSession.round1Committed_eq]
  simp [rssCutStateAbs, rssCutPhaseAbs]
  exact bytes32OfArray_zero

set_option linter.unusedSimpArgs false in
/-- **Exact step characterisation.** For every state and input, the extracted
    `RssCutGateSession::step` returns normally (no panic, no divergence), and its result is the
    step of `Qsag.mirRssCutMachine` on the abstracted state and input: accepted with the abstracted
    successor and output, or rejected with successor `mirRssCutPoison`. -/
theorem rssCut_extracted_step_refines (st : rss_cut_session.RssCutGateSession)
    (i : rss_cut_session.RssCutStepInput) :
    match rss_cut_session.RssCutGateSession.step st i with
    | .ok (st', .Ok o) =>
      Qsag.mirRssCutMachine.step (rssCutStateAbs st) (rssCutInputAbs i) =
        some (rssCutStateAbs st', rssCutOutputAbs o)
    | .ok (st', .Err _) =>
      Qsag.mirRssCutMachine.step (rssCutStateAbs st) (rssCutInputAbs i) = none ∧
      Qsag.mirRssCutMachine.errStep (rssCutStateAbs st) (rssCutInputAbs i) = rssCutStateAbs st'
    | _ => False := by
  rcases st with ⟨sid, ph, mc, cand, cv, p⟩
  cases p
  · cases i with
    | AdvanceRound2Chi rs rc cc =>
      by_cases hsid : sid = rs <;> by_cases hmc : mc = rc <;> cases ph <;>
        simp [rss_cut_session.RssCutGateSession.step,
          rss_cut_session.RssCutGateSession.advance_round2_chi,
          rss_cut_session.poison_rss_cut_session, ct_eq_bytes32_spec,
          bind_eq_result_bind, result_bind_ok,
          Qsag.mirRssCutMachine_step_eq, Qsag.mirRssCutMachine_errStep_eq,
          Qsag.mirRssCutPoison_eq, Qsag.mirRssCutAccepts_round2, Qsag.mirRssCutNext_round2,
          rssCutStateAbs, rssCutInputAbs, rssCutOutputAbs, rssCutPhaseAbs, hsid, hmc] <;>
        exact bytes32OfArray_zero.symm
    | AdvanceRound3VerifyConsistency rs lo hi dzk =>
      by_cases hsid : sid = rs <;> by_cases hlo : lo = 0#u128 <;> by_cases hhi : hi = 0#u128 <;>
        by_cases hdzk : dzk = 0#u64 <;> cases ph <;>
        simp [rss_cut_session.RssCutGateSession.step,
          rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
          rss_cut_session.poison_rss_cut_session, ct_eq_bytes32_spec,
          bind_eq_result_bind, result_bind_ok,
          Qsag.mirRssCutMachine_step_eq, Qsag.mirRssCutMachine_errStep_eq,
          Qsag.mirRssCutPoison_eq, Qsag.mirRssCutAccepts_round3, Qsag.mirRssCutNext_round3,
          Qsag.residualsZero_eq,
          rssCutStateAbs, rssCutInputAbs, rssCutOutputAbs, rssCutPhaseAbs, hsid, hlo, hhi, hdzk] <;>
        first
          | exact bytes32OfArray_zero.symm
          | exact ⟨fun h => hhi (UScalar.ext h), bytes32OfArray_zero.symm⟩
          | exact ⟨fun h => hlo (UScalar.ext h), bytes32OfArray_zero.symm⟩
          | exact ⟨fun _ h => hhi (UScalar.ext h), bytes32OfArray_zero.symm⟩
    | OpenVerifiedCut rs =>
      by_cases hsid : sid = rs <;> cases cv <;> cases ph <;>
        simp [rss_cut_session.RssCutGateSession.step,
          rss_cut_session.RssCutGateSession.open_verified_cut,
          rss_cut_session.poison_rss_cut_session, ct_eq_bytes32_spec,
          bind_eq_result_bind, result_bind_ok,
          Qsag.mirRssCutMachine_step_eq, Qsag.mirRssCutMachine_errStep_eq,
          Qsag.mirRssCutPoison_eq, Qsag.mirRssCutAccepts_open, Qsag.mirRssCutNext_open,
          rssCutStateAbs, rssCutInputAbs, rssCutOutputAbs, rssCutPhaseAbs, hsid] <;>
        exact bytes32OfArray_zero.symm
  · cases i <;>
      simp [rss_cut_session.RssCutGateSession.step,
        rss_cut_session.RssCutGateSession.advance_round2_chi,
        rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
        rss_cut_session.RssCutGateSession.open_verified_cut,
        rss_cut_session.poison_rss_cut_session,
        bind_eq_result_bind, result_bind_ok,
        Qsag.mirRssCutMachine_step_eq, Qsag.mirRssCutMachine_errStep_eq,
        Qsag.mirRssCutPoison_eq, rssCutStateAbs, rssCutInputAbs, rssCutPhaseAbs] <;>
      exact bytes32OfArray_zero.symm

/-- The extracted cut-session guard as a `Qsag.PartyMachine` over extracted states and inputs. -/
def extractedRssCutMachine :
    Qsag.PartyMachine rss_cut_session.RssCutGateSession rss_cut_session.RssCutStepInput
      Qsag.MirRssCutOutput :=
  extractedPartyMachine rss_cut_session.RssCutGateSession.step rssCutOutputAbs

/-- **Weld (`extractedRssCut_forwardSim_mirRssCut`).**
    The Aeneas-extracted `RssCutGateSession::step` forward-simulates `Qsag.mirRssCutMachine`
    through the field-for-field abstraction `rssCutStateAbs`: equal outputs, equal accept/reject
    decisions, and equal post-states on both accepted and rejected steps. The relation is a
    function, so the simulation is lockstep. -/
def extractedRssCut_forwardSim_mirRssCut :
    Qsag.ForwardSim extractedRssCutMachine (comapInputs Qsag.mirRssCutMachine rssCutInputAbs) where
  Rel c a := a = rssCutStateAbs c
  sim_ok {c c' a inp out} hRel hStepC := by
    subst hRel
    have h := rssCut_extracted_step_refines c inp
    dsimp only [extractedRssCutMachine, extractedPartyMachine, comapInputs] at hStepC ⊢
    cases hf : rss_cut_session.RssCutGateSession.step c inp with
    | ok p =>
      rcases p with ⟨m1, r⟩
      cases r with
      | Ok o =>
        rw [hf] at h hStepC
        dsimp only at h hStepC
        simp only [Option.some.injEq, Prod.mk.injEq] at hStepC
        obtain ⟨rfl, rfl⟩ := hStepC
        rw [h]
        exact ⟨rfl, rfl⟩
      | Err e =>
        rw [hf] at hStepC
        simp at hStepC
    | fail e =>
      rw [hf] at hStepC
      simp at hStepC
    | div =>
      rw [hf] at hStepC
      simp at hStepC
  sim_err {c a inp} hRel hNoneC := by
    subst hRel
    have h := rssCut_extracted_step_refines c inp
    dsimp only [extractedRssCutMachine, extractedPartyMachine, comapInputs] at hNoneC ⊢
    cases hf : rss_cut_session.RssCutGateSession.step c inp with
    | ok p =>
      rcases p with ⟨m1, r⟩
      cases r with
      | Ok o =>
        rw [hf] at hNoneC
        simp at hNoneC
      | Err e =>
        rw [hf] at h
        dsimp only at h
        exact ⟨h.1, h.2⟩
    | fail e =>
      rw [hf] at h
      exact False.elim h
    | div =>
      rw [hf] at h
      exact False.elim h

/-- Any trace predicate that holds on every valid trace of the spec machine
    `Qsag.mirRssCutMachine` (read through the input encoding) holds on every multi-turn trace of the
    extracted guard started by `new_round1_committed`. This is how a `Qsag`-side safety theorem
    about the cut session becomes a theorem about the extracted code. -/
theorem extractedRssCut_inherits_spec_trace_safety
    (sid comm : Array Std.U8 32#usize) (st0 st_f : rss_cut_session.RssCutGateSession)
    (hNew : rss_cut_session.RssCutGateSession.new_round1_committed sid comm = .ok st0)
    {Safe : List (rss_cut_session.RssCutStepInput × Qsag.MirRssCutOutput) → Prop}
    {trace : List (rss_cut_session.RssCutStepInput × Qsag.MirRssCutOutput)}
    (hSafe : ∀ {tr : List (rss_cut_session.RssCutStepInput × Qsag.MirRssCutOutput)}
      {a_f : Qsag.MirRssCutSession},
      (comapInputs Qsag.mirRssCutMachine rssCutInputAbs).ValidTrace
        (Qsag.MirRssCutSession.round1Committed (bytes32OfArray sid) (bytes32OfArray comm))
        tr a_f → Safe tr)
    (hTrace : extractedRssCutMachine.ValidTrace st0 trace st_f) :
    Safe trace :=
  extractedRssCut_forwardSim_mirRssCut.preserve_trace_pred
    (rssCutStateAbs_new_round1_committed sid comm st0 hNew).symm hSafe hTrace

/-- `#tooth`: the weld is sensitive to the residual. From a Round-2 state, the extracted guard
    with a non-zero low residual does not accept, and the spec machine on the encoded input
    rejects as well, landing in the poisoned state with the candidate wiped. -/
theorem tooth_extractedRssCut_nonzero_residual_rejected
    (sid mc cand : Array Std.U8 32#usize) :
    let st : rss_cut_session.RssCutGateSession :=
      { session_id := sid, phase := .Round2ChiEvaluated, mask_commitment := mc,
        candidate_cut_bytes := cand, consistency_verified := false, poisoned := false }
    let inp : rss_cut_session.RssCutStepInput :=
      .AdvanceRound3VerifyConsistency sid 1#u128 0#u128 0#u64
    extractedRssCutMachine.step st inp = none ∧
    (extractedRssCutMachine.errStep st inp).poisoned = true ∧
    (extractedRssCutMachine.errStep st inp).candidate_cut_bytes = Array.repeat 32#usize 0#u8 ∧
    Qsag.mirRssCutMachine.step (rssCutStateAbs st) (rssCutInputAbs inp) = none := by
  intro st inp
  have hStep : rss_cut_session.RssCutGateSession.step st inp =
      .ok ({ session_id := sid, phase := .Poisoned, mask_commitment := mc,
             candidate_cut_bytes := Array.repeat 32#usize 0#u8,
             consistency_verified := false, poisoned := true },
           .Err rss_cut_session.RssCutError.ConsistencyCheckFailed) := by
    simp [st, inp, rss_cut_session.RssCutGateSession.step,
      rss_cut_session.RssCutGateSession.advance_round3_verify_consistency,
      rss_cut_session.poison_rss_cut_session, ct_eq_bytes32_spec,
      bind_eq_result_bind, result_bind_ok]
  have hRef := rssCut_extracted_step_refines st inp
  rw [hStep] at hRef
  dsimp only at hRef
  refine ⟨?_, ?_, ?_, hRef.1⟩
  · dsimp only [extractedRssCutMachine, extractedPartyMachine]
    rw [hStep]
  · dsimp only [extractedRssCutMachine, extractedPartyMachine]
    rw [hStep]
  · dsimp only [extractedRssCutMachine, extractedPartyMachine]
    rw [hStep]

end qsag_verified.proofs
