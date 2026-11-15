module

public import Qsag.Math.Constructive

/-!
# Qsag.Exec.SimulationSpine — Compositional Forward Simulation, Rushing-Network Lifter & Canonical Codecs

Shared `0 Classical.choice` architectural spine unifying protocol pillars and MIR bridges:
1. **Canonical `PartyMachine`, `StepOutcome`, `LockstepSim` & `ForwardSim`**:
   - Deterministic `Option`-based / `StepOutcome`-based per-party state machines with stateful
     error/quarantine transitions (`errStep`).
   - Vertical composition (`ForwardSim.refl`, `ForwardSim.trans`) threading `.rlib ISA` $\to$
     `MIR Exec` $\to$ `Clean Party Spec` $\to$ `Ideal Protocol`, plus `ForwardSim.preserve_trace_pred`.
2. **`N`-Party Rushing-Network Product Simulation Lifter (`network_sim_of_party_sims`, `network_forward_sim`)**:
   - Models an `N`-party round-stepped multi-session network with persistent per-party state
     `(Fin N → PartySt)` driven by an arbitrary stateful rushing adversary `Adv` (who observes
     honest outbound round messages before choosing corrupt outputs and message delivery order).
   - Proves that per-party `ForwardSim` on every honest party `i ∉ corruptSet` lifts to exact
     equality of rushing adversary views and network output transcripts across arbitrary schedules.
3. **Canonical Fixed-Width & Length-Framed `CanonicalCodec` Combinators**:
   - `FixedCodec α width` (`FixedCodec.u8`, `FixedCodec.u32be`, `FixedCodec.u64be`, `FixedCodec.u64le`,
     `FixedCodec.bytes`, `FixedCodec.pair`) with automatic round-trip and prefix-slicing injectivity.
   - `FramedBytesCodec` (`u32be_len || payload` strict prefix-free stream injectivity & multi-field
     `concatFramed_injective`) and `DomainSeparatedTag` (`tag₁ ≠ tag₂ → domainFrame tag₁ x ≠ domainFrame tag₂ y`).
-/

public section

namespace Qsag

set_option autoImplicit false

/-! ## 1. Canonical `PartyMachine`, `LockstepSim` & Vertical `ForwardSim` (`0 Classical.choice`) -/

/-- Explicit step outcome when failed attempts mutate persistent state (quarantine, MAC burn, WAL). -/
inductive StepOutcome (S Out Err : Type) where
  | ok (nextState : S) (output : Out)
  | err (nextState : S) (error : Err)
  deriving Repr, DecidableEq

/-- Canonical per-party protocol state machine.
    `step` handles accepted transitions `some (s', out)`; when `step s inp = none`,
    `errStep s inp` updates the persistent state (defaulting to `s` for pure partial transitions). -/
structure PartyMachine (S In Out : Type) where
  step : S → In → Option (S × Out)
  errStep : S → In → S := fun s _ => s

/-- Construct a `PartyMachine` from a pure partial transition `S → In → Option (S × Out)`. -/
@[expose]
def PartyMachine.ofOption {S In Out : Type} (f : S → In → Option (S × Out)) :
    PartyMachine S In Out :=
  { step := f, errStep := fun s _ => s }

/-- Construct a `PartyMachine` from an error-mutating `StepOutcome` transition. -/
@[expose]
def PartyMachine.ofOutcome {S In Out Err : Type} (f : S → In → StepOutcome S Out Err) :
    PartyMachine S In Out where
  step s inp :=
    match f s inp with
    | .ok s' out => some (s', out)
    | .err _ _ => none
  errStep s inp :=
    match f s inp with
    | .ok s' _ => s'
    | .err s' _ => s'

/-- Execute one total step of `M`, returning `(nextState, some out)` on accept or
    `(M.errStep s inp, none)` on rejection. -/
@[expose]
def PartyMachine.runStep {S In Out : Type} (M : PartyMachine S In Out)
    (s : S) (inp : In) : S × Option Out :=
  match M.step s inp with
  | some (s', out) => (s', some out)
  | none => (M.errStep s inp, none)

/-- Inductive multi-turn valid trace of accepted `(In × Out)` pairs for `PartyMachine`,
    retaining rejected transitions via `M.errStep`. -/
inductive PartyMachine.ValidTrace {S In Out : Type} (M : PartyMachine S In Out) :
    S → List (In × Out) → S → Prop where
  | nil (s : S) : M.ValidTrace s [] s
  | accept {s s' s_final : S} {inp : In} {out : Out} {rest : List (In × Out)} :
      M.step s inp = some (s', out) →
      M.ValidTrace s' rest s_final →
      M.ValidTrace s ((inp, out) :: rest) s_final
  | reject {s s_final : S} (inp : In) {rest : List (In × Out)} :
      M.step s inp = none →
      M.ValidTrace (M.errStep s inp) rest s_final →
      M.ValidTrace s rest s_final

/-- Compositional forward simulation: concrete machine `C` forward-simulates abstract machine `A`.
    Uses deterministic `match A.step a inp` rather than `Exists` so `0 Classical.choice` is used. -/
structure ForwardSim {S_c S_a In Out : Type}
    (C : PartyMachine S_c In Out) (A : PartyMachine S_a In Out) : Type 1 where
  Rel : S_c → S_a → Prop
  sim_ok : ∀ {c c' : S_c} {a : S_a} {inp : In} {out : Out},
    Rel c a →
    C.step c inp = some (c', out) →
    match A.step a inp with
    | none => False
    | some (a', out_a) => out_a = out ∧ Rel c' a'
  sim_err : ∀ {c : S_c} {a : S_a} {inp : In},
    Rel c a →
    C.step c inp = none →
    A.step a inp = none ∧ Rel (C.errStep c inp) (A.errStep a inp)

/-- Functional lockstep simulation via an explicit abstraction map `abs : S_c → S_a`
    and concrete state invariant `Inv : S_c → Prop`. -/
structure LockstepSim {S_c S_a In Out : Type}
    (C : PartyMachine S_c In Out) (A : PartyMachine S_a In Out) : Type 1 where
  Inv : S_c → Prop
  abs : S_c → S_a
  step_eq : ∀ {c : S_c} (inp : In),
    Inv c →
    match C.step c inp with
    | some (c', out) => Inv c' ∧ A.step (abs c) inp = some (abs c', out)
    | none => Inv (C.errStep c inp) ∧ A.step (abs c) inp = none ∧
        abs (C.errStep c inp) = A.errStep (abs c) inp

/-- Every `LockstepSim` induces a canonical `ForwardSim`. -/
def LockstepSim.toForwardSim {S_c S_a In Out : Type}
    {C : PartyMachine S_c In Out} {A : PartyMachine S_a In Out}
    (L : LockstepSim C A) : ForwardSim C A where
  Rel c a := L.Inv c ∧ L.abs c = a
  sim_ok {c c' a inp out} hRel hStepC := by
    rcases hRel with ⟨hInv, rfl⟩
    have h := L.step_eq inp hInv
    rw [hStepC] at h
    rcases h with ⟨hInv', hStepA⟩
    rw [hStepA]
    exact ⟨rfl, hInv', rfl⟩
  sim_err {c a inp} hRel hNoneC := by
    rcases hRel with ⟨hInv, rfl⟩
    have h := L.step_eq inp hInv
    rw [hNoneC] at h
    rcases h with ⟨hInv', hNoneA, hErrEq⟩
    exact ⟨hNoneA, hInv', hErrEq⟩

@[simp]
theorem LockstepSim.toForwardSim_rel {S_c S_a In Out : Type}
    {C : PartyMachine S_c In Out} {A : PartyMachine S_a In Out}
    (L : LockstepSim C A) (c : S_c) (a : S_a) :
    L.toForwardSim.Rel c a ↔ L.Inv c ∧ L.abs c = a := Iff.rfl

/-- Reflexivity of `ForwardSim`. -/
def ForwardSim.refl {S In Out : Type} (M : PartyMachine S In Out) : ForwardSim M M where
  Rel := Eq
  sim_ok hRel hStep := by
    subst hRel
    rw [hStep]
    exact ⟨rfl, rfl⟩
  sim_err hRel hNone := by
    subst hRel
    exact ⟨hNone, rfl⟩

@[simp]
theorem ForwardSim.refl_rel {S In Out : Type} (M : PartyMachine S In Out) (s₁ s₂ : S) :
    (ForwardSim.refl M).Rel s₁ s₂ ↔ s₁ = s₂ := Iff.rfl

/-- Vertical transitivity of `ForwardSim` (`C → M → A`, e.g. `.rlib ISA → MIR → Spec → Ideal`)
    proved constructively with **zero `Classical.choice`**. -/
def ForwardSim.trans {S₁ S₂ S₃ In Out : Type}
    {M₁ : PartyMachine S₁ In Out}
    {M₂ : PartyMachine S₂ In Out}
    {M₃ : PartyMachine S₃ In Out}
    (sim12 : ForwardSim M₁ M₂) (sim23 : ForwardSim M₂ M₃) : ForwardSim M₁ M₃ where
  Rel s₁ s₃ := ∃ s₂ : S₂, sim12.Rel s₁ s₂ ∧ sim23.Rel s₂ s₃
  sim_ok {s₁ s₁' s₃ inp out} hRel hStep1 := by
    rcases hRel with ⟨s₂, h12, h23⟩
    have hMid := sim12.sim_ok h12 hStep1
    cases hStep2 : M₂.step s₂ inp with
    | none =>
      rw [hStep2] at hMid
      exact False.elim hMid
    | some pair2 =>
      rw [hStep2] at hMid
      rcases pair2 with ⟨s₂', out₂⟩
      rcases hMid with ⟨rfl, h12'⟩
      have hTop := sim23.sim_ok h23 hStep2
      cases hStep3 : M₃.step s₃ inp with
      | none =>
        rw [hStep3] at hTop
        exact False.elim hTop
      | some pair3 =>
        rw [hStep3] at hTop
        rcases pair3 with ⟨s₃', out₃⟩
        rcases hTop with ⟨hOutEq, h23'⟩
        exact ⟨hOutEq, ⟨s₂', h12', h23'⟩⟩
  sim_err {s₁ s₃ inp} hRel hNone1 := by
    rcases hRel with ⟨s₂, h12, h23⟩
    obtain ⟨hNone2, h12'⟩ := sim12.sim_err h12 hNone1
    obtain ⟨hNone3, h23'⟩ := sim23.sim_err h23 hNone2
    exact ⟨hNone3, ⟨M₂.errStep s₂ inp, h12', h23'⟩⟩

@[simp]
theorem ForwardSim.trans_rel {S₁ S₂ S₃ In Out : Type}
    {M₁ : PartyMachine S₁ In Out}
    {M₂ : PartyMachine S₂ In Out}
    {M₃ : PartyMachine S₃ In Out}
    (sim12 : ForwardSim M₁ M₂) (sim23 : ForwardSim M₂ M₃) (s₁ : S₁) (s₃ : S₃) :
    (sim12.trans sim23).Rel s₁ s₃ ↔ ∃ s₂ : S₂, sim12.Rel s₁ s₂ ∧ sim23.Rel s₂ s₃ := Iff.rfl

/-- Key single-step lockstep lemma: related states emit **identical** `Option Out` outputs
    and transition to related next states under `runStep`. -/
theorem ForwardSim.preserve_runStep {S_c S_a In Out : Type}
    {C : PartyMachine S_c In Out} {A : PartyMachine S_a In Out}
    (sim : ForwardSim C A) {c : S_c} {a : S_a} (inp : In) (hRel : sim.Rel c a) :
    (C.runStep c inp).2 = (A.runStep a inp).2 ∧
      sim.Rel (C.runStep c inp).1 (A.runStep a inp).1 := by
  dsimp only [PartyMachine.runStep]
  cases hStepC : C.step c inp with
  | some pairC =>
    rcases pairC with ⟨c', out⟩
    have hOk := sim.sim_ok hRel hStepC
    cases hStepA : A.step a inp with
    | none => rw [hStepA] at hOk; exact False.elim hOk
    | some pairA =>
      rw [hStepA] at hOk
      rcases pairA with ⟨a', out_a⟩
      rcases hOk with ⟨rfl, hRel'⟩
      exact ⟨rfl, hRel'⟩
  | none =>
    obtain ⟨hNoneA, hRel'⟩ := sim.sim_err hRel hStepC
    rw [hNoneA]
    exact ⟨rfl, hRel'⟩

/-- Lift any multi-turn concrete `ValidTrace` across `ForwardSim` (`0 Classical.choice`). -/
theorem ForwardSim.lift_validTrace {S_c S_a In Out : Type}
    {C : PartyMachine S_c In Out} {A : PartyMachine S_a In Out}
    (sim : ForwardSim C A) :
    ∀ {c₀ c_final : S_c} {a₀ : S_a} {trace : List (In × Out)},
      sim.Rel c₀ a₀ →
      C.ValidTrace c₀ trace c_final →
      ∃ a_final : S_a, A.ValidTrace a₀ trace a_final ∧ sim.Rel c_final a_final
  | _, _, a₀, _, hRel, .nil _ => ⟨a₀, .nil a₀, hRel⟩
  | _, _, a₀, _, hRel, .accept hStepC hTail => by
    have hOk := sim.sim_ok hRel hStepC
    cases hStepA : A.step a₀ _ with
    | none => rw [hStepA] at hOk; exact False.elim hOk
    | some pairA =>
      rw [hStepA] at hOk
      rcases pairA with ⟨a₁, out_a⟩
      rcases hOk with ⟨rfl, hRel₁⟩
      obtain ⟨a_final, hTraceA, hRelF⟩ := sim.lift_validTrace hRel₁ hTail
      exact ⟨a_final, .accept hStepA hTraceA, hRelF⟩
  | _, _, _, _, hRel, .reject inp hNoneC hTail => by
    obtain ⟨hNoneA, hRel₁⟩ := sim.sim_err hRel hNoneC
    obtain ⟨a_final, hTraceA, hRelF⟩ := sim.lift_validTrace hRel₁ hTail
    exact ⟨a_final, .reject inp hNoneA hTraceA, hRelF⟩

/-- **Trace Safety Preservation (`ForwardSim.preserve_trace_pred`)**:
    Any multi-turn trace predicate `Safe : List (In × Out) → Prop` that holds on all valid
    traces of `A` from `a₀` automatically holds on all valid traces of `C` from related `c₀`. -/
theorem ForwardSim.preserve_trace_pred {S_c S_a In Out : Type}
    {C : PartyMachine S_c In Out} {A : PartyMachine S_a In Out}
    (sim : ForwardSim C A)
    {Safe : List (In × Out) → Prop}
    {c₀ c_final : S_c} {a₀ : S_a} {trace : List (In × Out)}
    (hRel : sim.Rel c₀ a₀)
    (hSafeA : ∀ {tr : List (In × Out)} {a_f : S_a}, A.ValidTrace a₀ tr a_f → Safe tr)
    (hTraceC : C.ValidTrace c₀ trace c_final) :
    Safe trace := by
  obtain ⟨_, hTraceA, _⟩ := sim.lift_validTrace hRel hTraceC
  exact hSafeA hTraceA

/-! ## 2. `N`-Party Rushing-Network Product Simulation Lifter (`network_sim_of_party_sims`) -/

private def finBeq {N : Nat} (i j : Fin N) : Bool :=
  i.val == j.val

private theorem finBeq_eq_true_iff {N : Nat} (i j : Fin N) :
    finBeq i j = true ↔ i = j := by
  unfold finBeq
  constructor
  · intro h
    exact Fin.ext (Nat.eq_of_beq_eq_true h)
  · rintro rfl
    exact Nat.beq_refl _

/-- Constructive boolean check for membership in `corruptSet : List (Fin N)`. -/
def isCorruptParty {N : Nat} (i : Fin N) : List (Fin N) → Bool
  | [] => false
  | c :: cs => finBeq i c || isCorruptParty i cs

theorem isCorruptParty_eq_false_iff {N : Nat} (i : Fin N) :
    ∀ (cs : List (Fin N)), isCorruptParty i cs = false ↔ i ∉ cs
  | [] => by simp [isCorruptParty]
  | c :: cs => by
    simp only [isCorruptParty, Bool.or_eq_false_iff, isCorruptParty_eq_false_iff i cs,
      List.mem_cons, not_or]
    constructor
    · rintro ⟨hNeB, hRest⟩
      refine ⟨?_, hRest⟩
      intro hEq
      rw [(finBeq_eq_true_iff i c).mpr hEq] at hNeB
      cases hNeB
    · rintro ⟨hNe, hRest⟩
      refine ⟨?_, hRest⟩
      cases hb : finBeq i c
      · rfl
      · exact False.elim (hNe ((finBeq_eq_true_iff i c).mp hb))

/-- Update party `idx` in persistent `N`-party state `Fin N → PartySt`. -/
def updatePartyState {N : Nat} {PartySt : Type}
    (net : Fin N → PartySt) (idx : Fin N) (v : PartySt) : Fin N → PartySt :=
  fun j => if finBeq j idx then v else net j

theorem updatePartyState_self {N : Nat} {PartySt : Type}
    (net : Fin N → PartySt) (idx : Fin N) (v : PartySt) :
    updatePartyState net idx v idx = v := by
  unfold updatePartyState
  rw [(finBeq_eq_true_iff idx idx).mpr rfl]
  rfl

theorem updatePartyState_ne {N : Nat} {PartySt : Type}
    (net : Fin N → PartySt) {idx j : Fin N} (v : PartySt) (hNe : j ≠ idx) :
    updatePartyState net idx v j = net j := by
  unfold updatePartyState
  cases hb : finBeq j idx
  · rfl
  · exact False.elim (hNe ((finBeq_eq_true_iff j idx).mp hb))

/-- Schedule entry for one network round (session/round metadata + ordered honest activations). -/
structure RoundSchedule (N : Nat) (Meta : Type) where
  metaInfo : Meta
  honestActivationOrder : List (Fin N)

/-- Observable transcript of a single rushing-network round. -/
structure RoundTranscript (N : Nat) (Out CorruptOut : Type) where
  honestOutbound : List (Fin N × Option Out)
  corruptRushingOut : CorruptOut
  deliveredOutputs : List (Fin N × Option Out)
  deriving Repr, DecidableEq

/-- Arbitrary stateful rushing adversary / network scheduler:
    1. `prepareHonestInputs` selects round inputs for honest parties;
    2. `rushStep` observes all `honestOutbound` messages **before** producing `CorruptOut`
       and choosing an arbitrary ordered `(recipient, input)` delivery queue;
    3. `absorbDeliveries` updates adversary state with honest delivery responses. -/
structure RushingAdversary (N : Nat) (Meta In Out CorruptOut AdvSt : Type) where
  prepareHonestInputs : AdvSt → Meta → (Fin N → In) × AdvSt
  rushStep : AdvSt → Meta → List (Fin N × Option Out) →
    AdvSt × CorruptOut × List (Fin N × In)
  absorbDeliveries : AdvSt → Meta → List (Fin N × Option Out) → AdvSt

/-- Execute an ordered list of `(party, input)` activations on honest parties (`i ∉ corruptSet`),
    ignoring corrupt party slots (whose outputs are controlled directly by `Adv`). -/
def runHonestQueue {N : Nat} {PartySt In Out : Type}
    (corruptSet : List (Fin N))
    (machines : Fin N → PartyMachine PartySt In Out)
    (net : Fin N → PartySt) :
    List (Fin N × In) → (Fin N → PartySt) × List (Fin N × Option Out)
  | [] => (net, [])
  | (i, inp) :: rest =>
    if isCorruptParty i corruptSet then
      runHonestQueue corruptSet machines net rest
    else
      let (st', outOpt) := (machines i).runStep (net i) inp
      let net' := updatePartyState net i st'
      let (netFinal, tailOut) := runHonestQueue corruptSet machines net' rest
      (netFinal, (i, outOpt) :: tailOut)

/-- Execute one full rushing round on `(net, advSt)`. -/
def stepRushingRound {N : Nat} {PartySt Meta In Out CorruptOut AdvSt : Type}
    (corruptSet : List (Fin N))
    (machines : Fin N → PartyMachine PartySt In Out)
    (Adv : RushingAdversary N Meta In Out CorruptOut AdvSt)
    (net : Fin N → PartySt) (advSt : AdvSt) (sched : RoundSchedule N Meta) :
    (Fin N → PartySt) × AdvSt × RoundTranscript N Out CorruptOut :=
  let (inFn, adv₁) := Adv.prepareHonestInputs advSt sched.metaInfo
  let initQueue := sched.honestActivationOrder.map (fun i => (i, inFn i))
  let (net₁, honestOut) := runHonestQueue corruptSet machines net initQueue
  let (adv₂, corruptOut, deliveryQueue) := Adv.rushStep adv₁ sched.metaInfo honestOut
  let (net₂, deliveredOut) := runHonestQueue corruptSet machines net₁ deliveryQueue
  let adv₃ := Adv.absorbDeliveries adv₂ sched.metaInfo deliveredOut
  (net₂, adv₃, ⟨honestOut, corruptOut, deliveredOut⟩)

/-- Full multi-round, multi-session network execution result. -/
structure NetworkExecResult (N : Nat) (PartySt AdvSt Out CorruptOut : Type) where
  partyState : Fin N → PartySt
  advState : AdvSt
  transcript : List (RoundTranscript N Out CorruptOut)

/-- Execute an `N`-party network across an arbitrary multi-session schedule `sched`. -/
@[expose]
def execRushingNetwork {N : Nat} {PartySt Meta In Out CorruptOut AdvSt : Type}
    (corruptSet : List (Fin N))
    (machines : Fin N → PartyMachine PartySt In Out)
    (Adv : RushingAdversary N Meta In Out CorruptOut AdvSt)
    (net : Fin N → PartySt) (advSt : AdvSt) :
    List (RoundSchedule N Meta) → NetworkExecResult N PartySt AdvSt Out CorruptOut
  | [] => ⟨net, advSt, []⟩
  | r :: rs =>
    let (net', adv', tr) := stepRushingRound corruptSet machines Adv net advSt r
    let tail := execRushingNetwork corruptSet machines Adv net' adv' rs
    ⟨tail.partyState, tail.advState, tr :: tail.transcript⟩

private theorem runHonestQueue_sim {N : Nat} {S_c S_a In Out : Type}
    (corruptSet : List (Fin N))
    (C : Fin N → PartyMachine S_c In Out)
    (S : Fin N → PartyMachine S_a In Out)
    (sims : ∀ (i : Fin N), i ∉ corruptSet → ForwardSim (C i) (S i)) :
    ∀ (queue : List (Fin N × In)) (net_c : Fin N → S_c) (net_s : Fin N → S_a),
      (∀ (i : Fin N) (hi : i ∉ corruptSet), (sims i hi).Rel (net_c i) (net_s i)) →
      let res_c := runHonestQueue corruptSet C net_c queue
      let res_s := runHonestQueue corruptSet S net_s queue
      res_c.2 = res_s.2 ∧
        (∀ (i : Fin N) (hi : i ∉ corruptSet), (sims i hi).Rel (res_c.1 i) (res_s.1 i))
  | [], _, _, hRel => ⟨rfl, hRel⟩
  | (idx, inp) :: rest, net_c, net_s, hRel => by
    dsimp only [runHonestQueue]
    cases hCorr : isCorruptParty idx corruptSet
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hHonestIdx : idx ∉ corruptSet := (isCorruptParty_eq_false_iff idx corruptSet).mp hCorr
      obtain ⟨hOutEq, hRelIdx'⟩ :=
        (sims idx hHonestIdx).preserve_runStep inp (hRel idx hHonestIdx)
      have hRelUpd : ∀ (j : Fin N) (hj : j ∉ corruptSet),
          (sims j hj).Rel
            (updatePartyState net_c idx ((C idx).runStep (net_c idx) inp).1 j)
            (updatePartyState net_s idx ((S idx).runStep (net_s idx) inp).1 j) := by
        intro j hj
        cases hEqB : finBeq j idx
        · have hNe : j ≠ idx := by
            intro hEq
            rw [(finBeq_eq_true_iff j idx).mpr hEq] at hEqB
            cases hEqB
          rw [updatePartyState_ne net_c _ hNe, updatePartyState_ne net_s _ hNe]
          exact hRel j hj
        · have hEq : j = idx := (finBeq_eq_true_iff j idx).mp hEqB
          subst hEq
          rw [updatePartyState_self, updatePartyState_self]
          exact hRelIdx'
      obtain ⟨hTailOut, hTailRel⟩ :=
        runHonestQueue_sim corruptSet C S sims rest _ _ hRelUpd
      rw [hOutEq, hTailOut]
      exact ⟨rfl, hTailRel⟩
    · simp only [↓reduceIte]
      exact runHonestQueue_sim corruptSet C S sims rest net_c net_s hRel

private theorem stepRushingRound_sim {N : Nat} {S_c S_a Meta In Out CorruptOut AdvSt : Type}
    (corruptSet : List (Fin N))
    (C : Fin N → PartyMachine S_c In Out)
    (S : Fin N → PartyMachine S_a In Out)
    (Adv : RushingAdversary N Meta In Out CorruptOut AdvSt)
    (sims : ∀ (i : Fin N), i ∉ corruptSet → ForwardSim (C i) (S i))
    (net_c : Fin N → S_c) (net_s : Fin N → S_a) (advSt : AdvSt)
    (sched : RoundSchedule N Meta)
    (hRel : ∀ (i : Fin N) (hi : i ∉ corruptSet), (sims i hi).Rel (net_c i) (net_s i)) :
    let out_c := stepRushingRound corruptSet C Adv net_c advSt sched
    let out_s := stepRushingRound corruptSet S Adv net_s advSt sched
    out_c.2.1 = out_s.2.1 ∧ out_c.2.2 = out_s.2.2 ∧
      (∀ (i : Fin N) (hi : i ∉ corruptSet), (sims i hi).Rel (out_c.1 i) (out_s.1 i)) := by
  dsimp only [stepRushingRound]
  let prep := Adv.prepareHonestInputs advSt sched.metaInfo
  let initQueue := sched.honestActivationOrder.map (fun i => (i, prep.1 i))
  obtain ⟨hHonestOut, hRel₁⟩ :=
    runHonestQueue_sim corruptSet C S sims initQueue net_c net_s hRel
  let q1_c := runHonestQueue corruptSet C net_c initQueue
  let q1_s := runHonestQueue corruptSet S net_s initQueue
  change q1_c.2 = q1_s.2 at hHonestOut
  have hRushEq : Adv.rushStep prep.2 sched.metaInfo q1_c.2 =
      Adv.rushStep prep.2 sched.metaInfo q1_s.2 := by
    rw [hHonestOut]
  let rush_s := Adv.rushStep prep.2 sched.metaInfo q1_s.2
  obtain ⟨hDelivOut, hRel₂⟩ :=
    runHonestQueue_sim corruptSet C S sims rush_s.2.2 q1_c.1 q1_s.1 hRel₁
  change
    (let rush_c := Adv.rushStep prep.2 sched.metaInfo q1_c.2
     let q2_c := runHonestQueue corruptSet C q1_c.1 rush_c.2.2
     let q2_s := runHonestQueue corruptSet S q1_s.1 rush_s.2.2
     Adv.absorbDeliveries rush_c.1 sched.metaInfo q2_c.2 =
       Adv.absorbDeliveries rush_s.1 sched.metaInfo q2_s.2 ∧
     RoundTranscript.mk q1_c.2 rush_c.2.1 q2_c.2 =
       RoundTranscript.mk q1_s.2 rush_s.2.1 q2_s.2 ∧
     (∀ (i : Fin N) (hi : i ∉ corruptSet), (sims i hi).Rel (q2_c.1 i) (q2_s.1 i)))
  dsimp only
  rw [hRushEq]
  change _ ∧ _ ∧ _
  rw [hHonestOut, hDelivOut]
  exact ⟨rfl, rfl, hRel₂⟩

/-- **`N`-Party Rushing-Network Product Simulation Lifter (`network_sim_of_party_sims`)**:
    If for every honest party `i ∉ corruptSet`, concrete machine `C i` forward-simulates
    spec machine `S i`, then for **ANY** stateful rushing adversary `Adv`, **ANY** initial
    adversary state `adv₀`, and **ANY** multi-session schedule `sched`, the concrete network
    execution produces **bit-for-bit identical** adversary views and output transcripts as
    the spec network execution while preserving all per-party simulation invariants! -/
theorem network_sim_of_party_sims {N : Nat} {S_c S_a Meta In Out CorruptOut AdvSt : Type}
    (corruptSet : List (Fin N))
    (C : Fin N → PartyMachine S_c In Out)
    (S : Fin N → PartyMachine S_a In Out)
    (Adv : RushingAdversary N Meta In Out CorruptOut AdvSt)
    (sims : ∀ (i : Fin N), i ∉ corruptSet → ForwardSim (C i) (S i))
    (init_c : Fin N → S_c) (init_s : Fin N → S_a) (adv₀ : AdvSt) :
    ∀ (sched : List (RoundSchedule N Meta)),
      (∀ (i : Fin N) (hi : i ∉ corruptSet), (sims i hi).Rel (init_c i) (init_s i)) →
      let res_c := execRushingNetwork corruptSet C Adv init_c adv₀ sched
      let res_s := execRushingNetwork corruptSet S Adv init_s adv₀ sched
      res_c.advState = res_s.advState ∧
        res_c.transcript = res_s.transcript ∧
        (∀ (i : Fin N) (hi : i ∉ corruptSet),
          (sims i hi).Rel (res_c.partyState i) (res_s.partyState i))
  | [], hRel => ⟨rfl, rfl, hRel⟩
  | r :: rs, hRel => by
    dsimp only [execRushingNetwork]
    obtain ⟨hAdv1, hTr1, hRel1⟩ :=
      stepRushingRound_sim corruptSet C S Adv sims init_c init_s adv₀ r hRel
    let st1_c := stepRushingRound corruptSet C Adv init_c adv₀ r
    let st1_s := stepRushingRound corruptSet S Adv init_s adv₀ r
    change st1_c.2.1 = st1_s.2.1 at hAdv1
    change st1_c.2.2 = st1_s.2.2 at hTr1
    rw [hAdv1, hTr1]
    obtain ⟨hAdvTail, hTrTail, hRelTail⟩ :=
      network_sim_of_party_sims corruptSet C S Adv sims st1_c.1 st1_s.1 st1_s.2.1 rs hRel1
    exact ⟨hAdvTail, congrArg (st1_s.2.2 :: ·) hTrTail, hRelTail⟩

/-- Package an `N`-party rushing network as a composite `PartyMachine` so network-level
    simulations compose vertically via `ForwardSim.trans`. -/
