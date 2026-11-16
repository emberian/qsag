module
public import Qsag.Machine.MirSpecBridgeCore
import Qsag.Tactic.AssuranceKit
/-!
# Qsag.Tests.GuardedMachineSimInstance — Compositional 4-Guard Exercise (`zoom`, `prod`, `seq`)

Exercises the canonical guard-kit instances in `Qsag.Machine.MirSpecBridgeCore` (`mirVelocityGuard`,
`mirBeltLatchKernelGuard`, `mirMlDsaReleaseGuard`, `mirRssCutGuard`) composed directly through
`GuardedMachine.zoom`, `GuardedMachine.comapIn`, `GuardedMachine.prod`, and `GuardedMachine.seq`
with zero copied guard state structures or step functions and zero `LAW-M1` encapsulation bypasses.
-/
public section
namespace Qsag.Tests.GuardedMachineSimInstance
open Qsag
open Qsag.Exec.GuardedMachineSim
set_option autoImplicit false

/-! ## 1. Standalone Velocity Guard Multi-Turn Check (Preserved Interface) -/

def VelocityTraceSafe (g₀ : MirStatefulVelocityGuard)
    (tr : List (MirVelocitySpendRequest × BitVec 128)) (gF : MirStatefulVelocityGuard) : Prop :=
  let totalApproved := (tr.map (fun p => p.2.toNat)).foldr (· + ·) 0
  gF.spent_units.toNat = g₀.spent_units.toNat + totalApproved ∧
  gF.spent_units.toNat ≤ g₀.cap_units.toNat ∧
  totalApproved ≤ g₀.cap_units.toNat - g₀.spent_units.toNat ∧
  (∀ p ∈ tr, g₀.last_nonce.toNat < p.1.nonce.toNat ∧ p.1.window_id = g₀.window_id ∧
    p.1.policy_pin = g₀.policy_pin ∧ p.1.authority_pin = g₀.authority_pin) ∧
  tr.Pairwise (fun a b => a.1.nonce.toNat < b.1.nonce.toNat)

theorem mirVelocity_multiTurn_cap_and_monotonic_nonce
    {g₀ gF : MirStatefulVelocityGuard} {tr : List (MirVelocitySpendRequest × BitVec 128)}
    (hCap₀ : g₀.spent_units.toNat ≤ g₀.cap_units.toNat)
    (hTr : mirVelocityMachine.ValidTrace g₀ tr gF) : VelocityTraceSafe g₀ tr gF :=
  Qsag.mirVelocity_multiTurn_cap_and_monotonic_nonce hCap₀ hTr

theorem tooth_mirVelocity_nonMonotonic_nonce_rejected (g : MirStatefulVelocityGuard)
    (req : MirVelocitySpendRequest) (hBad : req.nonce.toNat ≤ g.last_nonce.toNat) :
    mirVelocityMachine.step g req = none :=
  Qsag.tooth_mirVelocity_nonMonotonic_nonce_rejected g req (.inl hBad)

theorem inhabited_mirVelocity_trace : ∃ (g₀ gF : MirStatefulVelocityGuard)
    (tr : List (MirVelocitySpendRequest × BitVec 128)),
    g₀.spent_units.toNat ≤ g₀.cap_units.toNat ∧ mirVelocityMachine.ValidTrace g₀ tr gF := by
  obtain ⟨g₀, gF, tr, hCap, hTrace, _⟩ := Qsag.inhabited_mirVelocity_two_turn_trace
  exact ⟨g₀, gF, tr, hCap, hTrace⟩

#verify_constructive mirVelocity_multiTurn_cap_and_monotonic_nonce
#verify_inhabited mirVelocity_multiTurn_cap_and_monotonic_nonce inhabited_mirVelocity_trace
#tooth_pair mirVelocity_multiTurn_cap_and_monotonic_nonce vs tooth_mirVelocity_nonMonotonic_nonce_rejected

/-! ## 2. Transporting `G.toParty.ValidTrace` to Canonical `M.ValidTrace` via `G.Models M` -/

theorem models_of_toParty_validTrace {S In Out : Type}
    {G : GuardedMachine S In Out} {M : PartyMachine S In Out}
    (hM : G.Models M) {s₀ sF : S} {tr : List (In × Out)}
    (hTr : G.toParty.ValidTrace s₀ tr sF) : M.ValidTrace s₀ tr sF := by
  refine G.models_self.trace_induction
    (motive := fun s tr sF => M.ValidTrace s tr sF) ?_ ?_ ?_ hTr
  · intro s
    exact .nil s
  · intro s i rest sF hg _ ih
    exact .accept (hM.step_of_guard hg) ih
  · intro s i rest sF hg _ ih
    have hRejEq : M.errStep s i = G.reject s i := hM.reject_eq s i hg
    exact .reject i (hM.none_of_guard hg) (hRejEq.symm ▸ ih)

theorem first_accept_of_nonempty_trace {S In Out : Type} {M : PartyMachine S In Out}
    (Inv : S → Prop)
    (hKeepRej : ∀ {s : S} {inp : In}, Inv s → M.step s inp = none → Inv (M.errStep s inp))
    {s₀ sF : S} {tr : List (In × Out)}
    (hTr : M.ValidTrace s₀ tr sF) (hInv : Inv s₀) (hNe : tr ≠ []) :
    ∃ (s s' : S) (inp : In) (out : Out), Inv s ∧ M.step s inp = some (s', out) := by
  induction hTr with
  | nil _ => exact False.elim (hNe rfl)
  | @accept s s' _ inp out _ hStep _ _ => exact ⟨s, s', inp, out, hInv, hStep⟩
  | @reject _ _ inp _ hNone _ ih => exact ih (hKeepRej hInv hNone) hNe

/-! ## 3. Composite 4-Guard Product Gate (`velocity × beltLatchKernel × mlDsaRelease × rssCut`) -/

/-- Unified custody turn input driving all four canonical MIR guards in lockstep. -/
structure FourGuardRequest where
  vel : MirVelocitySpendRequest
  belt : MirBeltLatchBindRequest
  mldsa : MirMlDsaBarrierChecks
  rss : MirRssCutInput

abbrev FourGuardState :=
  (MirStatefulVelocityGuard × MirBeltLatchKernel) × (MirMlDsaReleaseGate × MirRssCutSession)

abbrev FourGuardOutput :=
  (BitVec 128 × MirBeltLatchBindOutcome) × (List UInt8 × MirRssCutOutput)

/-- Composite 4-guard machine constructed via `GuardedMachine.comapIn` and `GuardedMachine.prod`. -/
def fourGuardComposite : GuardedMachine FourGuardState FourGuardRequest FourGuardOutput :=
  ((mirVelocityGuard.comapIn FourGuardRequest.vel).prod
    (mirBeltLatchKernelGuard.comapIn FourGuardRequest.belt)).prod
    ((mirMlDsaReleaseGuard.comapIn FourGuardRequest.mldsa).prod
      (mirRssCutGuard.comapIn FourGuardRequest.rss))

/-- **All-Four Multi-Turn Trace Theorem (`fourGuardComposite_multiTurn_safe`)**:
    Proved purely by projecting `fourGuardComposite` traces through `prod_fst_validTrace`,
    `prod_snd_validTrace`, and `comapIn_proj_trace` — ZERO nested `if` splits! -/
theorem fourGuardComposite_multiTurn_safe
    {s₀ sF : FourGuardState} {tr : List (FourGuardRequest × FourGuardOutput)}
    (hCap₀ : s₀.1.1.spent_units.toNat ≤ s₀.1.1.cap_units.toNat)
    (hWf₀ : s₀.1.2.WellFormed)
    (hTr : fourGuardComposite.toParty.ValidTrace s₀ tr sF) :
    VelocityTraceSafe s₀.1.1 (tr.map (fun p => (p.1.vel, p.2.1.1))) sF.1.1 ∧
    sF.1.2.WellFormed ∧
    (∀ p ∈ tr, p.1.belt.epoch.toNat < s₀.1.2.capacity_limit.toNat) ∧
    tr.length ≤ 1 ∧
    (∀ p ∈ tr, p.1.mldsa.z_norm_ok = true ∧ p.1.mldsa.r0_norm_ok = true ∧
      p.1.mldsa.w1_match = true ∧ p.1.mldsa.u_com_bound = true) ∧
    (∀ p ∈ tr, ∃ rs, mirRssCutGuard.guard rs p.1.rss = true) := by
  have hLeft := GuardedMachine.prod_fst_validTrace _ _ hTr
  have hRight := GuardedMachine.prod_snd_validTrace _ _ hTr
  have hVelParty := GuardedMachine.comapIn_proj_trace FourGuardRequest.vel mirVelocityGuard
    (GuardedMachine.prod_fst_validTrace _ _ hLeft)
  have hBeltParty := GuardedMachine.comapIn_proj_trace FourGuardRequest.belt mirBeltLatchKernelGuard
    (GuardedMachine.prod_snd_validTrace _ _ hLeft)
  have hMlParty := GuardedMachine.comapIn_proj_trace FourGuardRequest.mldsa mirMlDsaReleaseGuard
    (GuardedMachine.prod_fst_validTrace _ _ hRight)
  have hRssParty := GuardedMachine.comapIn_proj_trace FourGuardRequest.rss mirRssCutGuard
    (GuardedMachine.prod_snd_validTrace _ _ hRight)
  have hVel : VelocityTraceSafe s₀.1.1 (tr.map (fun p => (p.1.vel, p.2.1.1))) sF.1.1 := by
    have hM := models_of_toParty_validTrace mirVelocity_models hVelParty
    simpa only [List.map_map, Function.comp_def] using
      mirVelocity_multiTurn_cap_and_monotonic_nonce hCap₀ hM
  obtain ⟨hBeltWf, hBeltCap, _⟩ :=
    Qsag.mirBeltLatchKernel_equivocation_free hWf₀
      (models_of_toParty_validTrace mirBeltLatchKernel_models hBeltParty)
  obtain ⟨hMlLen, hMlFlags, _⟩ :=
    Qsag.mirMlDsa_at_most_one_release_through_barrier
      (models_of_toParty_validTrace mirMlDsaRelease_models hMlParty)
  obtain ⟨_, hRssAll⟩ := mirRssCutGuard.models_self.trace_invariant (fun _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) hRssParty trivial
  refine ⟨hVel, hBeltWf, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hMem : (p.1.belt, p.2.1.2) ∈
        ((tr.map (fun x => (x.1, x.2.1))).map (fun x => (x.1, x.2.2))).map
          (fun x => (FourGuardRequest.belt x.1, x.2)) := by
      simp only [List.map_map, Function.comp_def]
      exact List.mem_map_of_mem (f := fun x : FourGuardRequest × FourGuardOutput => (x.1.belt, x.2.1.2)) hp
    exact hBeltCap _ hMem
  · simpa only [List.length_map] using hMlLen
  · intro p hp
    have hMem : (p.1.mldsa, p.2.2.1) ∈
        ((tr.map (fun x => (x.1, x.2.2))).map (fun x => (x.1, x.2.1))).map
          (fun x => (FourGuardRequest.mldsa x.1, x.2)) := by
      simp only [List.map_map, Function.comp_def]
      exact List.mem_map_of_mem (f := fun x : FourGuardRequest × FourGuardOutput => (x.1.mldsa, x.2.2.1)) hp
    obtain ⟨_, _, hz, hr0, hw1, hu⟩ := hMlFlags _ hMem
    exact ⟨hz, hr0, hw1, hu⟩
  · intro p hp
    have hMem : (p.1.rss, p.2.2.2) ∈
        ((tr.map (fun x => (x.1, x.2.2))).map (fun x => (x.1, x.2.2))).map
          (fun x => (FourGuardRequest.rss x.1, x.2)) := by
      simp only [List.map_map, Function.comp_def]
      exact List.mem_map_of_mem (f := fun x : FourGuardRequest × FourGuardOutput => (x.1.rss, x.2.2.2)) hp
    obtain ⟨rs, _, hg, _⟩ := hRssAll _ hMem
    exact ⟨rs, hg⟩

/-! ## 4. Sequential Zoom Pipeline (`velocity ⟫ mlDsaRelease` via `Lens` + `zoom` + `seq`) -/

/-- Sequential pipeline on `MirStatefulVelocityGuard × MirMlDsaReleaseGate`:
    First runs `mirVelocityGuard` on `.1`, then zooms `mirMlDsaReleaseGuard` onto `.2`!
    If ML-DSA barrier checks fail, the velocity state update (`mirVelocityGuard.next`) stays
    committed while the ML-DSA share is wiped to 32 zero bytes and `aborted = true`! -/
def velThenMlDsaPipeline :
    GuardedMachine (MirStatefulVelocityGuard × MirMlDsaReleaseGate)
      (MirVelocitySpendRequest × MirMlDsaBarrierChecks) (List UInt8) :=
  let g₁ : GuardedMachine (MirStatefulVelocityGuard × MirMlDsaReleaseGate)
      (MirVelocitySpendRequest × MirMlDsaBarrierChecks) MirMlDsaBarrierChecks :=
    { guard := fun s req => mirVelocityGuard.guard s.1 req.1
      next := fun s req => (mirVelocityGuard.next s.1 req.1, s.2)
      out := fun _ req => req.2
      reject := fun s req => (mirVelocityGuard.reject s.1 req.1, s.2) }
  let l₂ : Lens (MirStatefulVelocityGuard × MirMlDsaReleaseGate) MirMlDsaReleaseGate := ⟨Prod.snd, fun p y => (p.1, y)⟩
  let g₂ := mirMlDsaReleaseGuard.zoom l₂
  g₁.seq g₂

/-- **Sequential Burn-and-Wipe Theorem (`velThenMlDsa_barrier_fail_commits_vel_and_wipes_share`)**:
    For ANY velocity pass (`mirVelocityMachine.step v₀ vReq = some (v₁, amt)`) paired with ANY
    failing ML-DSA barrier check (`(mBad.z_norm_ok && ... && mBad.u_com_bound) = false`),
    `velThenMlDsaPipeline` rejects (`step = none`), commits `v₁` in `.1`, AND wipes/aborts `.2`! -/
theorem velThenMlDsa_barrier_fail_commits_vel_and_wipes_share
    {v₀ v₁ : MirStatefulVelocityGuard} {vReq : MirVelocitySpendRequest} {amt : BitVec 128}
    (m₀ : MirMlDsaReleaseGate) (mBad : MirMlDsaBarrierChecks)
    (hVelOk : mirVelocityMachine.step v₀ vReq = some (v₁, amt))
    (hFail : (mBad.z_norm_ok && mBad.r0_norm_ok && mBad.w1_match && mBad.u_com_bound) = false) :
    velThenMlDsaPipeline.toParty.step (v₀, m₀) (vReq, mBad) = none ∧
    (velThenMlDsaPipeline.toParty.errStep (v₀, m₀) (vReq, mBad)).1 = v₁ ∧
    (velThenMlDsaPipeline.toParty.errStep (v₀, m₀) (vReq, mBad)).2.aborted = true ∧
    (velThenMlDsaPipeline.toParty.errStep (v₀, m₀) (vReq, mBad)).2.z_share_masked =
      List.replicate 32 0 := by
  obtain ⟨hgV, hvNext, _⟩ := mirVelocity_models.accepted hVelOk
  obtain ⟨hMlNone, hAb, hZero⟩ := mirMlDsa_failed_barrier_aborts_and_zeros_share_full m₀ mBad hFail
  obtain ⟨hgM, hRejEq⟩ := mirMlDsaRelease_models.rejected hMlNone
  have hgSeq : velThenMlDsaPipeline.guard (v₀, m₀) (vReq, mBad) = false := by
    dsimp only [velThenMlDsaPipeline, GuardedMachine.seq, GuardedMachine.zoom, Lens.snd]
    rw [hgV, hgM]
    rfl
  refine ⟨velThenMlDsaPipeline.step_reject hgSeq, ?_⟩
  dsimp only [velThenMlDsaPipeline, GuardedMachine.toParty, GuardedMachine.seq, GuardedMachine.zoom]
  simp only [hgV, ↓reduceIte, ← hvNext, ← hRejEq]
  exact ⟨trivial, hAb, hZero⟩

/-- Concrete 1-turn accepting witness for `fourGuardComposite` exercising all 4 guards simultaneously! -/
theorem inhabited_fourGuardComposite_trace :
    ∃ (s₀ sF : FourGuardState) (tr : List (FourGuardRequest × FourGuardOutput)),
      s₀.1.1.spent_units.toNat ≤ s₀.1.1.cap_units.toNat ∧
      s₀.1.2.WellFormed ∧
      fourGuardComposite.toParty.ValidTrace s₀ tr sF := by
  obtain ⟨vg₀, _, vTr, _, hvTrace, hvLen⟩ := Qsag.inhabited_mirVelocity_two_turn_trace
  have hvNe : vTr ≠ [] := by intro h; rw [h] at hvLen; cases hvLen
  obtain ⟨v₀, _, vReq, _, _, hvStep⟩ := first_accept_of_nonempty_trace
    (fun _ => True) (fun _ _ => trivial) hvTrace trivial hvNe
  have hvCap : v₀.spent_units.toNat ≤ v₀.cap_units.toNat := by
    have hNotOver : ¬ (v₀.cap_units.toNat < v₀.spent_units.toNat + vReq.amount_units.toNat) := by
      intro hOver
      have hNone := Qsag.tooth_mirVelocity_nonMonotonic_nonce_rejected v₀ vReq (.inr hOver)
      rw [hNone] at hvStep
      cases hvStep
    omega
  obtain ⟨bk₀, _, bTr, hbWf₀, hbTrace, hbMap⟩ := Qsag.inhabited_mirBeltLatchKernel_fresh_and_replay
  have hbNe : bTr ≠ [] := by intro h; rw [h] at hbMap; cases hbMap
  obtain ⟨k₀, _, bReq, _, hbWf, hbStep⟩ := first_accept_of_nonempty_trace
    MirBeltLatchKernel.WellFormed
    (fun {k inp} hW hNone =>
      (Qsag.mirBeltLatchKernel_equivocation_free hW (.reject inp hNone (.nil _))).1)
    hbTrace hbWf₀ hbNe
  obtain ⟨mg₀, _, mTr, hmTrace, hmLen⟩ := Qsag.inhabited_mirMlDsa_honest_release
  have hmNe : mTr ≠ [] := by intro h; rw [h] at hmLen; cases hmLen
  obtain ⟨m₀, _, mReq, _, _, hmStep⟩ := first_accept_of_nonempty_trace
    (fun _ => True) (fun _ _ => trivial) hmTrace trivial hmNe
  let r₀ : MirRssCutSession := MirRssCutSession.round1Committed zeroBytes32 zeroBytes32
  let rReq : MirRssCutInput := .advanceRound2Chi zeroBytes32 zeroBytes32 zeroBytes32
  have hrStep : mirRssCutMachine.step r₀ rReq = some ((mirRssCutNext r₀ rReq).1, (mirRssCutNext r₀ rReq).2) := by
    rw [mirRssCutMachine_step_eq]
    have hUnp : (!r₀.poisoned) = true := by
      show (!(MirRssCutSession.round1Committed zeroBytes32 zeroBytes32).poisoned) = true
      rw [MirRssCutSession.round1Committed_eq]
      rfl
    have hAcc : mirRssCutAccepts r₀ rReq = true := by
      dsimp only [r₀, rReq]
      rw [mirRssCutAccepts_round2, MirRssCutSession.round1Committed_eq]
      dsimp only
      rw [decide_eq_true rfl, decide_eq_true rfl]
      rfl
    rw [hUnp, hAcc]
    rfl
  obtain ⟨hgV, _, _⟩ := mirVelocity_models.accepted hvStep
  obtain ⟨hgB, _, _⟩ := mirBeltLatchKernel_models.accepted hbStep
  obtain ⟨hgM, _, _⟩ := mirMlDsaRelease_models.accepted hmStep
  obtain ⟨hgR, _, _⟩ := mirRssCut_models.accepted hrStep
  let s₀ : FourGuardState := ((v₀, k₀), (m₀, r₀))
  let req : FourGuardRequest := ⟨vReq, bReq, mReq, rReq⟩
  have hGuard : fourGuardComposite.guard s₀ req = true := by
    dsimp only [fourGuardComposite, GuardedMachine.prod, GuardedMachine.comapIn]
    rw [hgV, hgB, hgM, hgR]
    rfl
  exact ⟨s₀, fourGuardComposite.next s₀ req, [(req, fourGuardComposite.out s₀ req)],
    hvCap, hbWf, .accept (fourGuardComposite.step_accept hGuard) (.nil _)⟩

/-- Tooth for `fourGuardComposite`: a poisoned `MirRssCutSession` causes the entire 4-guard
    product to reject even when velocity, belt-latch, and ML-DSA checks all pass! -/
theorem tooth_fourGuardComposite_poisoned_rss_blocks_all
    (s : FourGuardState) (req : FourGuardRequest) (hP : s.2.2.poisoned = true) :
    ¬ ∃ out, fourGuardComposite.toParty.step s req = some out := by
  have hRssNone : mirRssCutMachine.step s.2.2 req.rss = none := by
    rw [mirRssCutMachine_step_eq, hP]
    rfl
  obtain ⟨hgR, _⟩ := mirRssCut_models.rejected hRssNone
  have hRej : fourGuardComposite.toParty.step s req = none := by
    apply fourGuardComposite.step_reject
    dsimp only [fourGuardComposite, GuardedMachine.prod, GuardedMachine.comapIn]
    rw [hgR, Bool.and_false, Bool.and_false]
  rintro ⟨out, hSome⟩
  rw [hRej] at hSome
  cases hSome

#verify_constructive
  models_of_toParty_validTrace
  first_accept_of_nonempty_trace
  fourGuardComposite_multiTurn_safe
  velThenMlDsa_barrier_fail_commits_vel_and_wipes_share
  inhabited_fourGuardComposite_trace
  tooth_fourGuardComposite_poisoned_rss_blocks_all
#verify_inhabited fourGuardComposite_multiTurn_safe inhabited_fourGuardComposite_trace
#tooth_pair fourGuardComposite_multiTurn_safe vs tooth_fourGuardComposite_poisoned_rss_blocks_all

end Qsag.Tests.GuardedMachineSimInstance
end
