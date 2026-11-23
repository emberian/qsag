module
/-
# Qsag.Spec.CorruptibleSignSimulation — Key-Reveal Simulation of the Corruptible Signer

`Qsag.Spec.IdealSign` refines only the corruption-free fragment of the signing functionality by a
real machine (`latchedSigner_refines_ideal`). This module adds a real machine with a key-reveal
output and relates all of its runs, before and after the reveal, to
`idealSignCorruptibleMachine`.

1. **Interface simulators (`Machine.simulate`).** `A.simulate simIn simOut` is `A` behind a
   stateless translator: a real-world input `inp` becomes the ideal input `simIn inp` (or is
   refused when `simIn inp = none`), and an ideal reply `o` is shown to the environment as
   `simOut o`. Its state is the state of `A`, and its transitions are transitions of `A`
   (`Machine.simulate_step_some`). Every run of the simulated world projects, state for state,
   to a run of `A` on the translated inputs (`Machine.simulate_validTrace_project`).
2. **Adaptive environments (`Machine.interact`).** An environment picks each input from the
   replies seen so far. Related states of a `Refines` witness give equal transcripts against
   every environment (`Refines.interact_eq`).
3. **Real machine (`latchedCorruptibleSignerMachine`).** State `(sk, nextEpoch, corrupted)`.
   `.sign` is the epoch latch of `latchedSignerMachine` in front of `S.sign sk`; `.exposeKey`
   sets `corrupted` and outputs `sk`; after that `.offlineSign req` returns
   `S.sign sk req.epoch req.message` without consulting or moving the latch, and
   `.register req sig` returns any `sig` that `S.verify (S.derivePk sk)` accepts.
4. **Simulated ideal world (`corruptibleSignSimulator`).** The functionality
   `idealSignCorruptibleMachine` enrolled with `S.derivePk skSim` and candidate oracle
   `S.sign skSim`, behind the translator `corruptibleSignSimIn` / `corruptibleSignSimOut`:
   `.sign ↦ .sign`, `.exposeKey ↦ .corrupt` with the reply `.corrupted` shown as `.key skSim`,
   `.offlineSign req ↦ .inject req sig` for `sig` computed with `skSim`, and
   `.register req sig ↦ .inject req sig`. The functionality holds no key; the simulator does.
5. **Results.**
   - `latchedCorruptibleSigner_refines_simulator`: a `Refines` witness from the real machine
     with key `sk` to the simulated ideal world with `skSim = sk` (same accept/reject
     behaviour, equal outputs, on every input in every reachable state).
   - `latchedCorruptibleSigner_adaptive_view_eq_simulator`: equal transcripts against every
     adaptive environment and every number of rounds.
   - `latchedCorruptibleSigner_simulated_by_idealSignCorruptible`: every initialized trace of
     the real machine is a trace of the simulated world, its translation is an initialized
     trace of `idealSignCorruptibleMachine`, every injected signature of that trace verifies,
     and every `.inject` in it is preceded by a `.corrupt`.
   - Guarantees transferred from the functionality: every signature the real machine emits
     verifies (`latchedCorruptibleSigner_emitted_verified`); a run that ends unexposed
     consists of honest signatures at strictly increasing epochs
     (`latchedCorruptibleSigner_unexposed_run_safe`).

**Scope.** The coupling is `skSim = sk`: the simulator reveals the key whose public key it
enrolled. Equality of public keys is not enough, because the key is an output
(`corruptibleSignSimulator_wrong_key_view_differs`). All machines here are deterministic and the
statements are exact (no probability). Nothing is claimed about what the revealed key allows
beyond the interface (`.offlineSign`, `.register`), about key generation, or about schemes with
per-request randomness (`S.sign` is a function of key, epoch and message).
`Spec.DataRefines` is not used for the projection to `idealSignCorruptibleMachine`: its
`sim_reject` field keeps the abstract state fixed on a rejected input, while a rejected `.sign`
at an admissible epoch consumes that epoch in the functionality; the projection theorem keeps
the rejected inputs instead.
-/

public import Qsag.Spec.IdealSign
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

private theorem corrAndSplit {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

private theorem corrIteSome {α : Type} {c : Bool} {x : Option α} {y : α}
    (h : (if c = true then x else none) = some y) : c = true ∧ x = some y := by
  cases c with
  | false =>
    have h2 : (none : Option α) = some y := h
    cases h2
  | true => exact ⟨rfl, h⟩

private theorem corrMapSome {α β : Type} {x : Option α} {f : α → β} {y : β}
    (h : x.map f = some y) : ∃ s, x = some s ∧ f s = y := by
  cases x with
  | none =>
    have h2 : (none : Option β) = some y := h
    cases h2
  | some s => exact ⟨s, rfl, Option.some.inj h⟩

/-! ## 1. Interface simulators -/

/-- `A` behind a stateless interface translator. An input `inp` is forwarded to `A` as
    `simIn inp`, or refused when `simIn inp = none`; a reply `o` of `A` is shown as `simOut o`.
    The state is the state of `A` and changes only through `A.step` and `A.errStep`. -/
@[expose] def Machine.simulate {St In_a Out_a In_r Out_r : Type} (A : Machine St In_a Out_a)
    (simIn : In_r → Option In_a) (simOut : Out_a → Out_r) : Machine St In_r Out_r where
  Init := A.Init
  step s inp :=
    match simIn inp with
    | some j => (A.step s j).map (fun p => (p.1, simOut p.2))
    | none => none
  errStep s inp :=
    match simIn inp with
    | some j => A.errStep s j
    | none => s

section Simulate
variable {St In_a Out_a In_r Out_r : Type} {A : Machine St In_a Out_a}
  {simIn : In_r → Option In_a} {simOut : Out_a → Out_r}

/-- A translated input that `A` accepts is accepted with the translated reply. -/
theorem Machine.simulate_step_of {s s' : St} {inp : In_r} {j : In_a} {o : Out_a}
    (hIn : simIn inp = some j) (hStep : A.step s j = some (s', o)) :
    (A.simulate simIn simOut).step s inp = some (s', simOut o) := by
  show (match simIn inp with
    | some j => (A.step s j).map (fun p => (p.1, simOut p.2))
    | none => none) = some (s', simOut o)
  rw [hIn]
  show (A.step s j).map (fun p => (p.1, simOut p.2)) = some (s', simOut o)
  rw [hStep]
  rfl

/-- **Every accepted step of the simulated world is an accepted step of `A`** on the
    translated input, between the same states. -/
theorem Machine.simulate_step_some {s s' : St} {inp : In_r} {out : Out_r}
    (h : (A.simulate simIn simOut).step s inp = some (s', out)) :
    ∃ (j : In_a) (o : Out_a), simIn inp = some j ∧ A.step s j = some (s', o) ∧
      out = simOut o := by
  have h' : (match simIn inp with
    | some j => (A.step s j).map (fun p => (p.1, simOut p.2))
    | none => none) = some (s', out) := h
  cases hIn : simIn inp with
  | none =>
    rw [hIn] at h'
    have h2 : (none : Option (St × Out_r)) = some (s', out) := h'
    cases h2
  | some j =>
    rw [hIn] at h'
    have h2 : (A.step s j).map (fun p => (p.1, simOut p.2)) = some (s', out) := h'
    obtain ⟨p, hP, hPair⟩ := corrMapSome h2
    have hs : p.1 = s' := congrArg Prod.fst hPair
    refine ⟨j, p.2, rfl, ?_, (congrArg Prod.snd hPair).symm⟩
    rw [← hs]
    exact hP

/-- A translated input that `A` rejects is rejected, with the `errStep` of `A`. -/
theorem Machine.simulate_reject_of {s : St} {inp : In_r} {j : In_a}
    (hIn : simIn inp = some j) (hStep : A.step s j = none) :
    (A.simulate simIn simOut).step s inp = none ∧
    (A.simulate simIn simOut).errStep s inp = A.errStep s j := by
  constructor
  · show (match simIn inp with
      | some j => (A.step s j).map (fun p => (p.1, simOut p.2))
      | none => none) = none
    rw [hIn]
    show (A.step s j).map (fun p => (p.1, simOut p.2)) = none
    rw [hStep]
    rfl
  · show (match simIn inp with
      | some j => A.errStep s j
      | none => s) = A.errStep s j
    rw [hIn]

/-- An input the translator refuses is rejected and leaves the state unchanged. -/
theorem Machine.simulate_refuse_of {s : St} {inp : In_r} (hIn : simIn inp = none) :
    (A.simulate simIn simOut).step s inp = none ∧
    (A.simulate simIn simOut).errStep s inp = s := by
  constructor
  · show (match simIn inp with
      | some j => (A.step s j).map (fun p => (p.1, simOut p.2))
      | none => none) = none
    rw [hIn]
  · show (match simIn inp with
      | some j => A.errStep s j
      | none => s) = s
    rw [hIn]

private theorem projectTrace_cons_some {In_c In_a' Out_c Out_a' : Type}
    {visIn : In_c → Option In_a'} {visOut : Out_c → Out_a'} {inp : In_c} {j : In_a'}
    (h : visIn inp = some j) (out : Out_c) (rest : List (In_c × Out_c)) :
    projectTrace visIn visOut ((inp, out) :: rest) =
      (j, visOut out) :: projectTrace visIn visOut rest := by
  simp only [projectTrace, h]

/-- **Every run of the simulated world projects to a run of `A`** between the same states:
    accepted events become the accepted translated events, refused inputs disappear, and inputs
    `A` rejected stay rejected inputs of `A`. `visOut` is any left inverse of `simOut`. -/
theorem Machine.simulate_validTrace_project {visOut : Out_r → Out_a}
    (hVis : ∀ o : Out_a, visOut (simOut o) = o) :
    ∀ {s s' : St} {tr : List (In_r × Out_r)},
      (A.simulate simIn simOut).ValidTrace s tr s' →
      A.ValidTrace s (projectTrace simIn visOut tr) s'
  | _, _, _, .nil _ => .nil _
  | _, _, _, .accept (inp := inp) (out := out) (rest := rest) hStep hRest => by
    obtain ⟨j, o, hIn, hA, hOut⟩ := Machine.simulate_step_some hStep
    have ih := Machine.simulate_validTrace_project hVis hRest
    rw [projectTrace_cons_some hIn, hOut, hVis]
    exact .accept hA ih
  | s, _, _, .reject inp hNone hRest => by
    have ih := Machine.simulate_validTrace_project hVis hRest
    cases hIn : simIn inp with
    | none =>
      rw [(Machine.simulate_refuse_of (A := A) (simOut := simOut) (s := s) hIn).2] at ih
      exact ih
    | some j =>
      have hA : A.step s j = none := by
        cases hS : A.step s j with
        | none => rfl
        | some p =>
          rw [Machine.simulate_step_of hIn (show A.step s j = some (p.1, p.2) from hS)] at hNone
          cases hNone
      rw [(Machine.simulate_reject_of (simOut := simOut) hIn hA).2] at ih
      exact .reject j hA ih

end Simulate

/-- A run through an accepted event splits at that event. -/
theorem Machine.validTrace_split {St In Out : Type} {M : Machine St In Out} {ev : In × Out}
    {post : List (In × Out)} {s s' : St} (pre : List (In × Out))
    (h : M.ValidTrace s (pre ++ ev :: post) s') :
    ∃ m m' : St, M.ValidTrace s pre m ∧ M.step m ev.1 = some (m', ev.2) ∧
      M.ValidTrace m' post s' := by
  generalize hT : pre ++ ev :: post = tr at h
  induction h generalizing pre with
  | nil s =>
    cases pre with
    | nil => cases hT
    | cons p pre' => cases hT
  | @accept s₀ s₁ s₂ inp out rest hStep hRest ih =>
    cases pre with
    | nil =>
      have hT' : ev :: post = (inp, out) :: rest := hT
      injection hT' with hEv hPost
      refine ⟨s₀, s₁, .nil _, ?_, ?_⟩
      · rw [hEv]
        exact hStep
      · rw [hPost]
        exact hRest
    | cons p pre' =>
      have hT' : p :: (pre' ++ ev :: post) = (inp, out) :: rest := hT
      injection hT' with hP hRestEq
      obtain ⟨m, m', hPre, hStepM, hPost⟩ := ih pre' hRestEq
      refine ⟨m, m', ?_, hStepM, hPost⟩
      rw [hP]
      exact .accept hStep hPre
  | reject inp hNone hRest ih =>
    obtain ⟨m, m', hPre, hStepM, hPost⟩ := ih pre hT
    exact ⟨m, m', .reject inp hNone hPre, hStepM, hPost⟩

/-! ## 2. Adaptive environments -/

/-- The transcript of at most `fuel` rounds of the adaptive environment `env` against `M` from
    state `s`. `view` is the list of replies so far, newest first, with `none` for a rejected
    input; `env view` is the next input, or `none` to stop. -/
@[expose] def Machine.interact {St In Out : Type} (M : Machine St In Out)
    (env : List (Option Out) → Option In) : Nat → St → List (Option Out) → List (Option Out)
  | 0, _, view => view
  | fuel + 1, s, view =>
    match env view with
    | none => view
    | some inp => M.interact env fuel (M.runStep s inp).1 ((M.runStep s inp).2 :: view)

/-- **A refinement gives equal transcripts against every adaptive environment**, from any pair
    of related states and any common history. -/
theorem Refines.interact_eq {S_c S_a In Out : Type} {C : Machine S_c In Out}
    {A : Machine S_a In Out} (sim : C ⊑ A) (env : List (Option Out) → Option In) :
    ∀ (fuel : Nat) {c : S_c} {a : S_a} (view : List (Option Out)),
      sim.Rel c a → C.interact env fuel c view = A.interact env fuel a view
  | 0, _, _, _, _ => rfl
  | fuel + 1, c, a, view, hRel => by
    show (match env view with
      | none => view
      | some inp => C.interact env fuel (C.runStep c inp).1 ((C.runStep c inp).2 :: view)) =
      (match env view with
      | none => view
      | some inp => A.interact env fuel (A.runStep a inp).1 ((A.runStep a inp).2 :: view))
    cases env view with
    | none => rfl
    | some inp =>
      obtain ⟨hOut, hRel'⟩ := sim.preserve_runStep inp hRel
      show C.interact env fuel (C.runStep c inp).1 ((C.runStep c inp).2 :: view) =
        A.interact env fuel (A.runStep a inp).1 ((A.runStep a inp).2 :: view)
      rw [hOut]
      exact Refines.interact_eq sim env fuel _ hRel'

/-! ## 3. The corruptible latched signer -/

/-- Inputs of the corruptible signer: an honest signing request, the exposure of the key, a
    signature computed offline with the exposed key, and the registration of a signature
    supplied by the environment. -/
inductive CorruptibleSignerCommand (Sig : Type) where
  | sign (req : SignRequest)
  | exposeKey
  | offlineSign (req : SignRequest)
  | register (req : SignRequest) (sig : Sig)

/-- Outputs of the corruptible signer: a signature, or the secret key. -/
inductive CorruptibleSignerReply (SK Sig : Type) where
  | signature (sig : Sig)
  | key (sk : SK)

/-- State of the corruptible signer: the secret key, the least epoch the latch still admits,
    and whether the key has been exposed. -/
structure CorruptibleSignerState (SK : Type) where
  sk : SK
  nextEpoch : Nat
  corrupted : Bool

/-- **The latched signer with key exposure.**

    `.sign req` is `latchedSignerMachine`: an admissible epoch moves the latch to `epoch + 1`
    whether or not `S.sign` returns a signature, in every state. `.exposeKey` is always
    accepted, sets `corrupted` and outputs the key. `.offlineSign req` is accepted exactly when
    `corrupted = true` and `S.sign sk req.epoch req.message` returns a signature, which it
    outputs; `.register req sig` is accepted exactly when `corrupted = true` and
    `S.verify (S.derivePk sk) req.message sig = true`, and outputs `sig`. Neither consults or
    moves the latch. -/
@[expose] def latchedCorruptibleSignerMachine {PK SK Sig : Type} (S : SigScheme PK SK Sig)
    (sk₀ : SK) (stateful₀ : Bool) (maxWindow : Nat) :
    Machine (CorruptibleSignerState SK) (CorruptibleSignerCommand Sig)
      (CorruptibleSignerReply SK Sig) where
  Init c := c = ⟨sk₀, 0, false⟩
  step c cmd :=
    match cmd with
    | .sign req =>
      if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
        (S.sign c.sk req.epoch req.message).map
          (fun sig => ({ c with nextEpoch := req.epoch + 1 }, CorruptibleSignerReply.signature sig))
      else none
    | .exposeKey => some ({ c with corrupted := true }, CorruptibleSignerReply.key c.sk)
    | .offlineSign req =>
      if c.corrupted = true then
        (S.sign c.sk req.epoch req.message).map
          (fun sig => (c, CorruptibleSignerReply.signature sig))
      else none
    | .register req sig =>
      if (c.corrupted && S.verify (S.derivePk c.sk) req.message sig) = true then
        some (c, CorruptibleSignerReply.signature sig)
      else none
  errStep c cmd :=
    match cmd with
    | .sign req =>
      if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
        { c with nextEpoch := req.epoch + 1 }
      else c
    | .exposeKey => c
    | .offlineSign _ => c
    | .register _ _ => c

/-- Every signature a trace of the corruptible signer emitted, with its request, in order:
    honest, offline and registered. -/
@[expose] def corruptibleSignerEmitted {SK Sig : Type} :
    List (CorruptibleSignerCommand Sig × CorruptibleSignerReply SK Sig) →
      List (SignRequest × Sig)
  | [] => []
  | (.sign req, .signature sig) :: rest => (req, sig) :: corruptibleSignerEmitted rest
  | (.offlineSign req, .signature sig) :: rest => (req, sig) :: corruptibleSignerEmitted rest
  | (.register req _, .signature sig) :: rest => (req, sig) :: corruptibleSignerEmitted rest
  | (.sign _, .key _) :: rest => corruptibleSignerEmitted rest
  | (.offlineSign _, .key _) :: rest => corruptibleSignerEmitted rest
  | (.register _ _, .key _) :: rest => corruptibleSignerEmitted rest
  | (.exposeKey, _) :: rest => corruptibleSignerEmitted rest

section Real
variable {PK SK Sig : Type} {S : SigScheme PK SK Sig} {sk₀ : SK} {stateful₀ : Bool}
  {maxWindow : Nat}

/-- An accepted `.sign` passed the latch, outputs `S.sign` under the state's key and moves the
    latch past the request's epoch. -/
theorem latchedCorruptibleSigner_sign_step_some {c c' : CorruptibleSignerState SK}
    {req : SignRequest} {out : CorruptibleSignerReply SK Sig}
    (h : (latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).step c (.sign req) =
      some (c', out)) :
    ∃ sig : Sig, epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true ∧
      S.sign c.sk req.epoch req.message = some sig ∧
      c' = { c with nextEpoch := req.epoch + 1 } ∧
      out = CorruptibleSignerReply.signature sig := by
  have h' : (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
      (S.sign c.sk req.epoch req.message).map
        (fun sig => (({ c with nextEpoch := req.epoch + 1 } : CorruptibleSignerState SK),
          (CorruptibleSignerReply.signature sig : CorruptibleSignerReply SK Sig)))
      else none) = some (c', out) := h
  obtain ⟨hA, hMap⟩ := corrIteSome h'
  obtain ⟨s, hSign, hPair⟩ := corrMapSome hMap
  exact ⟨s, hA, hSign, (congrArg Prod.fst hPair).symm, (congrArg Prod.snd hPair).symm⟩

/-- `.exposeKey` is accepted in every state, sets the flag and outputs the state's key. -/
theorem latchedCorruptibleSigner_exposeKey_step (c : CorruptibleSignerState SK) :
    (latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).step c .exposeKey =
      some ({ c with corrupted := true }, CorruptibleSignerReply.key c.sk) := by
  rfl

theorem latchedCorruptibleSigner_exposeKey_step_some {c c' : CorruptibleSignerState SK}
    {out : CorruptibleSignerReply SK Sig}
    (h : (latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).step c .exposeKey =
      some (c', out)) :
    c' = { c with corrupted := true } ∧ out = CorruptibleSignerReply.key c.sk := by
  rw [latchedCorruptibleSigner_exposeKey_step] at h
  have hPair := Option.some.inj h
  exact ⟨(congrArg Prod.fst hPair).symm, (congrArg Prod.snd hPair).symm⟩

/-- **An accepted `.offlineSign` happens after exposure**, outputs `S.sign` under the state's
    key and leaves the state, the latch included, unchanged. -/
theorem latchedCorruptibleSigner_offlineSign_step_some {c c' : CorruptibleSignerState SK}
    {req : SignRequest} {out : CorruptibleSignerReply SK Sig}
    (h : (latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).step c
      (.offlineSign req) = some (c', out)) :
    ∃ sig : Sig, c.corrupted = true ∧ S.sign c.sk req.epoch req.message = some sig ∧
      c' = c ∧ out = CorruptibleSignerReply.signature sig := by
  have h' : (if c.corrupted = true then
      (S.sign c.sk req.epoch req.message).map
        (fun sig => (c, (CorruptibleSignerReply.signature sig : CorruptibleSignerReply SK Sig)))
      else none) = some (c', out) := h
  obtain ⟨hC, hMap⟩ := corrIteSome h'
  obtain ⟨s, hSign, hPair⟩ := corrMapSome hMap
  exact ⟨s, hC, hSign, (congrArg Prod.fst hPair).symm, (congrArg Prod.snd hPair).symm⟩

/-- **An accepted `.register` happens after exposure** and carries a signature the verifier
    accepts under the public key of the state's key; the state is unchanged. -/
theorem latchedCorruptibleSigner_register_step_some {c c' : CorruptibleSignerState SK}
    {req : SignRequest} {sig : Sig} {out : CorruptibleSignerReply SK Sig}
    (h : (latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).step c
      (.register req sig) = some (c', out)) :
    c.corrupted = true ∧ S.verify (S.derivePk c.sk) req.message sig = true ∧
      c' = c ∧ out = CorruptibleSignerReply.signature sig := by
  have h' : (if (c.corrupted && S.verify (S.derivePk c.sk) req.message sig) = true then
      some (c, (CorruptibleSignerReply.signature sig : CorruptibleSignerReply SK Sig))
      else none) = some (c', out) := h
  obtain ⟨hC, hEq⟩ := corrIteSome h'
  obtain ⟨hc, hv⟩ := corrAndSplit hC
  have hPair := Option.some.inj hEq
  exact ⟨hc, hv, (congrArg Prod.fst hPair).symm, (congrArg Prod.snd hPair).symm⟩

/-- A rejection changes neither the key nor the exposure flag. -/
theorem latchedCorruptibleSigner_errStep_facts (c : CorruptibleSignerState SK)
    (cmd : CorruptibleSignerCommand Sig) :
    ((latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).errStep c cmd).sk = c.sk ∧
    ((latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).errStep c cmd).corrupted =
      c.corrupted := by
  cases cmd with
  | sign req =>
    show (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
        ({ c with nextEpoch := req.epoch + 1 } : CorruptibleSignerState SK) else c).sk = c.sk ∧
      (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
        ({ c with nextEpoch := req.epoch + 1 } : CorruptibleSignerState SK) else c).corrupted =
        c.corrupted
    cases epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch <;> exact ⟨rfl, rfl⟩
  | exposeKey => exact ⟨rfl, rfl⟩
  | offlineSign req => exact ⟨rfl, rfl⟩
  | register req sig => exact ⟨rfl, rfl⟩

/-- The key never changes along a run. -/
theorem latchedCorruptibleSigner_trace_key :
    ∀ {s s' : CorruptibleSignerState SK}
      {tr : List (CorruptibleSignerCommand Sig × CorruptibleSignerReply SK Sig)},
      (latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).ValidTrace s tr s' →
      s'.sk = s.sk
  | _, _, _, .nil _ => rfl
  | _, _, _, .accept (inp := inp) hStep hRest => by
    have ih := latchedCorruptibleSigner_trace_key hRest
    cases inp with
    | sign req =>
      obtain ⟨_, _, _, hc, _⟩ := latchedCorruptibleSigner_sign_step_some hStep
      rw [hc] at ih
      exact ih
    | exposeKey =>
      obtain ⟨hc, _⟩ := latchedCorruptibleSigner_exposeKey_step_some hStep
      rw [hc] at ih
      exact ih
    | offlineSign req =>
      obtain ⟨_, _, _, hc, _⟩ := latchedCorruptibleSigner_offlineSign_step_some hStep
      rw [hc] at ih
      exact ih
    | register req sig =>
      obtain ⟨_, _, hc, _⟩ := latchedCorruptibleSigner_register_step_some hStep
      rw [hc] at ih
      exact ih
  | s, _, _, .reject inp _ hRest => by
    have ih := latchedCorruptibleSigner_trace_key hRest
    rw [(latchedCorruptibleSigner_errStep_facts s inp).1] at ih
    exact ih

/-- **A run that ends unexposed started unexposed and accepted only honest `.sign` events**: no
    output of the run is the key, and no signature bypassed the latch. -/
theorem latchedCorruptibleSigner_trace_unexposed :
    ∀ {s s' : CorruptibleSignerState SK}
      {tr : List (CorruptibleSignerCommand Sig × CorruptibleSignerReply SK Sig)},
      (latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).ValidTrace s tr s' →
      s'.corrupted = false →
      s.corrupted = false ∧
      ∀ ev ∈ tr, ∃ (req : SignRequest) (sig : Sig),
        ev = (CorruptibleSignerCommand.sign req, CorruptibleSignerReply.signature sig)
  | _, _, _, .nil _, hU => ⟨hU, fun _ h => (nomatch h)⟩
  | _, _, _, .accept (inp := inp) hStep hRest, hU => by
    obtain ⟨ihC, ihEv⟩ := latchedCorruptibleSigner_trace_unexposed hRest hU
    cases inp with
    | sign req =>
      obtain ⟨sig, _, _, hc, hOut⟩ := latchedCorruptibleSigner_sign_step_some hStep
      rw [hc] at ihC
      refine ⟨ihC, fun ev hev => ?_⟩
      rcases List.mem_cons.mp hev with hH | hT
      · exact ⟨req, sig, by rw [hH, hOut]⟩
      · exact ihEv ev hT
    | exposeKey =>
      obtain ⟨hc, _⟩ := latchedCorruptibleSigner_exposeKey_step_some hStep
      rw [hc] at ihC
      exact Bool.noConfusion (ihC : true = false)
    | offlineSign req =>
      obtain ⟨_, hCor, _, hc, _⟩ := latchedCorruptibleSigner_offlineSign_step_some hStep
      rw [hc] at ihC
      exact Bool.noConfusion (hCor.symm.trans ihC)
    | register req sig =>
      obtain ⟨hCor, _, hc, _⟩ := latchedCorruptibleSigner_register_step_some hStep
      rw [hc] at ihC
      exact Bool.noConfusion (hCor.symm.trans ihC)
  | s, _, _, .reject inp _ hRest, hU => by
    obtain ⟨ihC, ihEv⟩ := latchedCorruptibleSigner_trace_unexposed hRest hU
    rw [(latchedCorruptibleSigner_errStep_facts s inp).2] at ihC
    exact ⟨ihC, ihEv⟩

end Real

/-! ## 4. The simulator around `idealSignCorruptibleMachine` -/

/-- Input translation of the simulator holding `skSim`. `.exposeKey` becomes `.corrupt`; an
    offline signature becomes the injection of the signature the simulator computes with
    `skSim` (refused when `S.sign skSim` returns none); a registered signature becomes its
    injection. -/
@[expose] def corruptibleSignSimIn {PK SK Sig : Type} (S : SigScheme PK SK Sig) (skSim : SK) :
    CorruptibleSignerCommand Sig → Option (SignCommand Sig)
  | .sign req => some (.sign req)
  | .exposeKey => some .corrupt
  | .offlineSign req =>
    (S.sign skSim req.epoch req.message).map (fun sig => SignCommand.inject req sig)
  | .register req sig => some (.inject req sig)

/-- Output translation of the simulator: the acknowledgement of a corruption is shown to the
    environment as the key `skSim`. -/
@[expose] def corruptibleSignSimOut {SK Sig : Type} (skSim : SK) :
    SignReply Sig → CorruptibleSignerReply SK Sig
  | .signature sig => .signature sig
  | .corrupted => .key skSim

/-- The functionality's view of a real output: a revealed key is the acknowledgement
    `.corrupted`. A left inverse of `corruptibleSignSimOut`. -/
@[expose] def corruptibleSignVisOut {SK Sig : Type} :
    CorruptibleSignerReply SK Sig → SignReply Sig
  | .signature sig => .signature sig
  | .key _ => .corrupted

/-- **The simulated ideal world**: `idealSignCorruptibleMachine`, enrolled with the public key
    of `skSim` and proposing the signatures of `S.sign skSim`, behind the simulator's interface
    translation. Its state is the state of the functionality, which holds no key. -/
@[expose] def corruptibleSignSimulator {PK SK Sig : Type} (S : SigScheme PK SK Sig) (skSim : SK)
    (stateful₀ : Bool) (maxWindow : Nat) :
    Machine (CorruptibleSignState PK Sig) (CorruptibleSignerCommand Sig)
      (CorruptibleSignerReply SK Sig) :=
  (idealSignCorruptibleMachine S (S.derivePk skSim) stateful₀ maxWindow
      (fun req => S.sign skSim req.epoch req.message)).simulate
    (corruptibleSignSimIn S skSim) (corruptibleSignSimOut skSim)

section Simulator
variable {PK SK Sig : Type}

theorem corruptibleSignVisOut_simOut (skSim : SK) (o : SignReply Sig) :
    corruptibleSignVisOut (corruptibleSignSimOut skSim o) = o := by
  cases o <;> rfl

theorem corruptibleSignSimIn_offlineSign {S : SigScheme PK SK Sig} {skSim : SK}
    {req : SignRequest} {sig : Sig} (h : S.sign skSim req.epoch req.message = some sig) :
    corruptibleSignSimIn S skSim (.offlineSign req) = some (SignCommand.inject req sig) := by
  show (S.sign skSim req.epoch req.message).map (fun sig => SignCommand.inject req sig) =
    some (SignCommand.inject req sig)
  rw [h]
  rfl

theorem corruptibleSignSimIn_offlineSign_none {S : SigScheme PK SK Sig} {skSim : SK}
    {req : SignRequest} (h : S.sign skSim req.epoch req.message = none) :
    corruptibleSignSimIn S skSim (.offlineSign req) = none := by
  show (S.sign skSim req.epoch req.message).map (fun sig => SignCommand.inject req sig) = none
  rw [h]
  rfl

/-- A translated input the functionality accepts is accepted by the simulated world. -/
theorem corruptibleSignSimulator_step_of (S : SigScheme PK SK Sig) (skSim : SK)
    (stateful₀ : Bool) (maxWindow : Nat) {a a' : CorruptibleSignState PK Sig}
    (cmd : CorruptibleSignerCommand Sig) {j : SignCommand Sig} {o : SignReply Sig}
    (hIn : corruptibleSignSimIn S skSim cmd = some j)
    (hStep : (idealSignCorruptibleMachine S (S.derivePk skSim) stateful₀ maxWindow
      (fun req => S.sign skSim req.epoch req.message)).step a j = some (a', o)) :
    (corruptibleSignSimulator S skSim stateful₀ maxWindow).step a cmd =
      some (a', corruptibleSignSimOut skSim o) :=
  Machine.simulate_step_of hIn hStep

/-- A translated input the functionality rejects is rejected by the simulated world, with the
    functionality's `errStep`. -/
theorem corruptibleSignSimulator_reject_of (S : SigScheme PK SK Sig) (skSim : SK)
    (stateful₀ : Bool) (maxWindow : Nat) {a : CorruptibleSignState PK Sig}
    (cmd : CorruptibleSignerCommand Sig) {j : SignCommand Sig}
    (hIn : corruptibleSignSimIn S skSim cmd = some j)
    (hStep : (idealSignCorruptibleMachine S (S.derivePk skSim) stateful₀ maxWindow
      (fun req => S.sign skSim req.epoch req.message)).step a j = none) :
    (corruptibleSignSimulator S skSim stateful₀ maxWindow).step a cmd = none ∧
    (corruptibleSignSimulator S skSim stateful₀ maxWindow).errStep a cmd =
      (idealSignCorruptibleMachine S (S.derivePk skSim) stateful₀ maxWindow
        (fun req => S.sign skSim req.epoch req.message)).errStep a j :=
  Machine.simulate_reject_of hIn hStep

/-- An input the simulator refuses is rejected and leaves the functionality untouched. -/
theorem corruptibleSignSimulator_refuse_of (S : SigScheme PK SK Sig) (skSim : SK)
    (stateful₀ : Bool) (maxWindow : Nat) (a : CorruptibleSignState PK Sig)
    {cmd : CorruptibleSignerCommand Sig} (hIn : corruptibleSignSimIn S skSim cmd = none) :
    (corruptibleSignSimulator S skSim stateful₀ maxWindow).step a cmd = none ∧
    (corruptibleSignSimulator S skSim stateful₀ maxWindow).errStep a cmd = a :=
  Machine.simulate_refuse_of hIn

/-- **Before `.corrupt` the simulator cannot register a signature**, valid or not: the
    functionality rejects the `.inject` that `.register` translates to. -/
theorem corruptibleSignSimulator_register_rejected_unexposed (S : SigScheme PK SK Sig)
    (skSim : SK) (stateful₀ : Bool) (maxWindow : Nat) {a : CorruptibleSignState PK Sig}
    (hU : a.corrupted = false) (req : SignRequest) (sig : Sig) :
    (corruptibleSignSimulator S skSim stateful₀ maxWindow).step a (.register req sig) = none :=
  (corruptibleSignSimulator_reject_of S skSim stateful₀ maxWindow (.register req sig) rfl
    (idealSignCorruptibleMachine_inject_step_of_uncorrupted req sig hU)).1

/-- **Before `.corrupt` the simulator cannot emit an offline signature.** -/
theorem corruptibleSignSimulator_offlineSign_rejected_unexposed (S : SigScheme PK SK Sig)
    (skSim : SK) (stateful₀ : Bool) (maxWindow : Nat) {a : CorruptibleSignState PK Sig}
    (hU : a.corrupted = false) (req : SignRequest) :
    (corruptibleSignSimulator S skSim stateful₀ maxWindow).step a (.offlineSign req) = none := by
  cases hSg : S.sign skSim req.epoch req.message with
  | none =>
    exact (corruptibleSignSimulator_refuse_of S skSim stateful₀ maxWindow a
      (corruptibleSignSimIn_offlineSign_none hSg)).1
  | some sig =>
    exact (corruptibleSignSimulator_reject_of S skSim stateful₀ maxWindow (.offlineSign req)
      (corruptibleSignSimIn_offlineSign hSg)
      (idealSignCorruptibleMachine_inject_step_of_uncorrupted req sig hU)).1

end Simulator

/-! ## 5. Injections of the functionality happen after a corruption -/

section IdealOrder
variable {PK SK Sig : Type} {S : SigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool}
  {maxWindow : Nat} {oracleSign : SignRequest → Option Sig}

/-- A run of the functionality that starts uncorrupted and ends corrupted contains an accepted
    `.corrupt`. -/
theorem idealSignCorruptibleMachine_trace_corrupt_event :
    ∀ {s s' : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)},
      (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s tr s' →
      s.corrupted = false → s'.corrupted = true →
      (SignCommand.corrupt, SignReply.corrupted) ∈ tr
  | _, _, _, .nil _, hF, hT => Bool.noConfusion (hF.symm.trans hT)
  | _, _, _, .accept (s' := s₁) (inp := inp) hStep hRest, hF, hT => by
    cases inp with
    | sign req =>
      obtain ⟨inner', sig, _, hSt, _⟩ := idealSignCorruptibleMachine_sign_step_some hStep
      have hF' : s₁.corrupted = false := by
        rw [hSt]
        exact hF
      exact List.mem_cons_of_mem _
        (idealSignCorruptibleMachine_trace_corrupt_event hRest hF' hT)
    | corrupt =>
      obtain ⟨_, hOut⟩ := idealSignCorruptibleMachine_corrupt_step_some hStep
      rw [hOut]
      exact List.mem_cons.mpr (.inl rfl)
    | inject req sig =>
      obtain ⟨hc, _, _, _⟩ := idealSignCorruptibleMachine_inject_step_some hStep
      exact Bool.noConfusion (hF.symm.trans hc)
  | s, _, _, .reject inp _ hRest, hF, hT => by
    have hF' : ((idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).errStep s
        inp).corrupted = false := by
      cases inp <;> exact hF
    exact idealSignCorruptibleMachine_trace_corrupt_event hRest hF' hT

/-- **In an initialized run of the functionality every accepted `.inject` is preceded by an
    accepted `.corrupt`.** -/
theorem idealSignCorruptibleMachine_inject_after_corrupt
    {pre post : List (SignCommand Sig × SignReply Sig)} {req : SignRequest} {sig : Sig}
    {out : SignReply Sig} {s_final : CorruptibleSignState PK Sig}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (CorruptibleSignState.empty pk₀ stateful₀)
      (pre ++ (SignCommand.inject req sig, out) :: post) s_final) :
    (SignCommand.corrupt, SignReply.corrupted) ∈ pre := by
  obtain ⟨m, m', hPre, hStep, _⟩ := Machine.validTrace_split pre hTrace
  obtain ⟨hc, _, _, _⟩ := idealSignCorruptibleMachine_inject_step_some hStep
  exact idealSignCorruptibleMachine_trace_corrupt_event hPre rfl hc

/-- **Before `.corrupt` the functionality rejects `.inject`.** After any initialized run that
    accepted no `.corrupt`, every `.inject` is rejected, for every request and signature, the
    ones the verifier accepts included. -/
theorem idealSignCorruptible_inject_rejected_before_corrupt
    {tr : List (SignCommand Sig × SignReply Sig)} {s : CorruptibleSignState PK Sig}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (CorruptibleSignState.empty pk₀ stateful₀) tr s)
    (hNo : (SignCommand.corrupt, SignReply.corrupted) ∉ tr) (req : SignRequest) (sig : Sig) :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step s
      (.inject req sig) = none := by
  cases hC : s.corrupted with
  | false => exact idealSignCorruptibleMachine_inject_step_of_uncorrupted req sig hC
  | true => exact absurd (idealSignCorruptibleMachine_trace_corrupt_event hTrace rfl hC) hNo

end IdealOrder

/-! ## 6. The real machine refines the simulated ideal world -/

/-- **The corruptible latched signer refines the simulated ideal world** whose simulator holds
    the same key: on every input, in every pair of related states, both accept or both reject,
    with equal outputs — the key included — and related successor states. The relation equates
    the latch position, the mode, the enrolled public key and the exposure flag. -/
def latchedCorruptibleSigner_refines_simulator {PK SK Sig : Type} (S : SigScheme PK SK Sig)
    (sk : SK) (stateful₀ : Bool) (maxWindow : Nat) :
    latchedCorruptibleSignerMachine S sk stateful₀ maxWindow ⊑
      corruptibleSignSimulator S sk stateful₀ maxWindow where
  Rel c a := c.sk = sk ∧ a.inner.nextEpoch = c.nextEpoch ∧ a.inner.statefulEpochs = stateful₀ ∧
    a.inner.enrolledPk = S.derivePk sk ∧ a.corrupted = c.corrupted
  absInit _ := CorruptibleSignState.empty (S.derivePk sk) stateful₀
  init_ok {c₀} hInit := by
    have hC : c₀ = ⟨sk, 0, false⟩ := hInit
    rw [hC]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  sim_ok {c c' a inp out} hRel hStepC := by
    obtain ⟨hSk, hN, hS, hPk, hCor⟩ := hRel
    cases inp with
    | sign req =>
      obtain ⟨sig, hA, hSign, hc, hOut⟩ := latchedCorruptibleSigner_sign_step_some hStepC
      rw [hSk] at hSign
      have hA' : epochAdmissible a.inner.statefulEpochs maxWindow a.inner.nextEpoch req.epoch =
          true := by
        rw [hS, hN]
        exact hA
      have hV : S.verify a.inner.enrolledPk req.message sig = true := by
        rw [hPk]
        exact S.correct sk req.epoch req.message sig hSign
      rw [corruptibleSignSimulator_step_of S sk stateful₀ maxWindow (.sign req) rfl
        (idealSignCorruptibleMachine_sign_step_of_ideal
          (idealSignMachine_step_of_valid (S := S) (pk₀ := S.derivePk sk)
            (stateful₀ := stateful₀) (maxWindow := maxWindow)
            (oracleSign := fun r => S.sign sk r.epoch r.message) hA' hSign hV)), hc, hOut]
      exact ⟨rfl, hSk, rfl, hS, hPk, hCor⟩
    | exposeKey =>
      obtain ⟨hc, hOut⟩ := latchedCorruptibleSigner_exposeKey_step_some hStepC
      rw [corruptibleSignSimulator_step_of S sk stateful₀ maxWindow .exposeKey rfl
        (idealSignCorruptibleMachine_corrupt_step a), hc, hOut]
      exact ⟨congrArg CorruptibleSignerReply.key hSk.symm, hSk, hN, hS, hPk, rfl⟩
    | offlineSign req =>
      obtain ⟨sig, hC, hSign, hc, hOut⟩ :=
        latchedCorruptibleSigner_offlineSign_step_some hStepC
      rw [hSk] at hSign
      have hV : S.verify a.inner.enrolledPk req.message sig = true := by
        rw [hPk]
        exact S.correct sk req.epoch req.message sig hSign
      rw [corruptibleSignSimulator_step_of S sk stateful₀ maxWindow (.offlineSign req)
        (corruptibleSignSimIn_offlineSign hSign)
        (idealSignCorruptibleMachine_inject_step_of_corrupted (hCor.trans hC) hV), hc, hOut]
      exact ⟨rfl, hSk, hN, hS, hPk, hCor⟩
    | register req sig =>
      obtain ⟨hC, hVer, hc, hOut⟩ := latchedCorruptibleSigner_register_step_some hStepC
      rw [hSk] at hVer
      have hV : S.verify a.inner.enrolledPk req.message sig = true := by
        rw [hPk]
        exact hVer
      rw [corruptibleSignSimulator_step_of S sk stateful₀ maxWindow (.register req sig) rfl
        (idealSignCorruptibleMachine_inject_step_of_corrupted (hCor.trans hC) hV), hc, hOut]
      exact ⟨rfl, hSk, hN, hS, hPk, hCor⟩
  sim_err {c a inp} hRel hNoneC := by
    obtain ⟨hSk, hN, hS, hPk, hCor⟩ := hRel
    cases inp with
    | sign req =>
      have hNoneC' : (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
          (S.sign c.sk req.epoch req.message).map
            (fun sig => (({ c with nextEpoch := req.epoch + 1 } : CorruptibleSignerState SK),
              (CorruptibleSignerReply.signature sig : CorruptibleSignerReply SK Sig)))
          else none) = none := hNoneC
      cases hA : epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch with
      | false =>
        have hA' : epochAdmissible a.inner.statefulEpochs maxWindow a.inner.nextEpoch
            req.epoch = false := by
          rw [hS, hN]
          exact hA
        have hErrC : (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).errStep c
            (.sign req) = c := by
          show (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
            ({ c with nextEpoch := req.epoch + 1 } : CorruptibleSignerState SK) else c) = c
          rw [hA]
          rfl
        obtain ⟨hNoneW, hErrW⟩ := corruptibleSignSimulator_reject_of S sk stateful₀ maxWindow
          (a := a) (.sign req) rfl
          (idealSignCorruptibleMachine_sign_step_none_iff.mpr
            (idealSignMachine_step_of_inadmissible hA'))
        rw [hErrC, hErrW, idealSignCorruptibleMachine_sign_errStep,
          idealSignMachine_errStep_of_inadmissible hA']
        exact ⟨hNoneW, hSk, hN, hS, hPk, hCor⟩
      | true =>
        rw [hA] at hNoneC'
        have hSignC : S.sign c.sk req.epoch req.message = none := by
          cases hSg : S.sign c.sk req.epoch req.message with
          | none => rfl
          | some s =>
            rw [hSg] at hNoneC'
            cases hNoneC'
        rw [hSk] at hSignC
        have hA' : epochAdmissible a.inner.statefulEpochs maxWindow a.inner.nextEpoch
            req.epoch = true := by
          rw [hS, hN]
          exact hA
        have hErrC : (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).errStep c
            (.sign req) = { c with nextEpoch := req.epoch + 1 } := by
          show (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
            ({ c with nextEpoch := req.epoch + 1 } : CorruptibleSignerState SK) else c) =
            { c with nextEpoch := req.epoch + 1 }
          rw [hA]
          rfl
        obtain ⟨hNoneW, hErrW⟩ := corruptibleSignSimulator_reject_of S sk stateful₀ maxWindow
          (a := a) (.sign req) rfl
          (idealSignCorruptibleMachine_sign_step_none_iff.mpr
            (idealSignMachine_step_of_no_candidate
              (oracleSign := fun r => S.sign sk r.epoch r.message) hSignC))
        rw [hErrC, hErrW, idealSignCorruptibleMachine_sign_errStep,
          idealSignMachine_errStep_of_admissible hA']
        exact ⟨hNoneW, hSk, rfl, hS, hPk, hCor⟩
    | exposeKey =>
      rw [latchedCorruptibleSigner_exposeKey_step] at hNoneC
      cases hNoneC
    | offlineSign req =>
      have hErrC : (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).errStep c
          (.offlineSign req) = c := rfl
      cases hSg : S.sign sk req.epoch req.message with
      | none =>
        obtain ⟨hNoneW, hErrW⟩ := corruptibleSignSimulator_refuse_of S sk stateful₀ maxWindow a
          (corruptibleSignSimIn_offlineSign_none hSg)
        rw [hErrC, hErrW]
        exact ⟨hNoneW, hSk, hN, hS, hPk, hCor⟩
      | some sig =>
        have hCf : c.corrupted = false := by
          cases hCc : c.corrupted with
          | false => rfl
          | true =>
            have hNoneC' : (if c.corrupted = true then
                (S.sign c.sk req.epoch req.message).map
                  (fun sig => (c, (CorruptibleSignerReply.signature sig :
                    CorruptibleSignerReply SK Sig)))
                else none) = none := hNoneC
            rw [hCc, hSk, hSg] at hNoneC'
            cases hNoneC'
        obtain ⟨hNoneW, hErrW⟩ := corruptibleSignSimulator_reject_of S sk stateful₀ maxWindow
          (a := a) (.offlineSign req) (corruptibleSignSimIn_offlineSign hSg)
          (idealSignCorruptibleMachine_inject_step_of_uncorrupted req sig (hCor.trans hCf))
        rw [hErrC, hErrW, idealSignCorruptibleMachine_inject_errStep]
        exact ⟨hNoneW, hSk, hN, hS, hPk, hCor⟩
    | register req sig =>
      have hErrC : (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).errStep c
          (.register req sig) = c := rfl
      have hNoneC' : (if (c.corrupted && S.verify (S.derivePk c.sk) req.message sig) = true then
          some (c, (CorruptibleSignerReply.signature sig : CorruptibleSignerReply SK Sig))
          else none) = none := hNoneC
      have hI : (idealSignCorruptibleMachine S (S.derivePk sk) stateful₀ maxWindow
          (fun r => S.sign sk r.epoch r.message)).step a (.inject req sig) = none := by
        cases hCc : c.corrupted with
        | false =>
          exact idealSignCorruptibleMachine_inject_step_of_uncorrupted req sig (hCor.trans hCc)
        | true =>
          cases hVv : S.verify (S.derivePk sk) req.message sig with
          | false =>
            exact idealSignCorruptibleMachine_inject_step_of_unverified (by rw [hPk]; exact hVv)
          | true =>
            rw [hCc, hSk, hVv] at hNoneC'
            cases hNoneC'
      obtain ⟨hNoneW, hErrW⟩ := corruptibleSignSimulator_reject_of S sk stateful₀ maxWindow
        (a := a) (.register req sig) rfl hI
      rw [hErrC, hErrW, idealSignCorruptibleMachine_inject_errStep]
      exact ⟨hNoneW, hSk, hN, hS, hPk, hCor⟩

section Headline
variable {PK SK Sig : Type}

/-- **Perfect simulation against adaptive environments.** For every environment that chooses
    its inputs from the replies it has seen (the revealed key among them) and every number of
    rounds, the transcript against the corruptible latched signer equals the transcript against
    the simulated ideal world. -/
theorem latchedCorruptibleSigner_adaptive_view_eq_simulator (S : SigScheme PK SK Sig) (sk : SK)
    (stateful₀ : Bool) (maxWindow : Nat)
    (env : List (Option (CorruptibleSignerReply SK Sig)) → Option (CorruptibleSignerCommand Sig))
    (fuel : Nat) :
    (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).interact env fuel
        ⟨sk, 0, false⟩ [] =
      (corruptibleSignSimulator S sk stateful₀ maxWindow).interact env fuel
        (CorruptibleSignState.empty (S.derivePk sk) stateful₀) [] :=
  (latchedCorruptibleSigner_refines_simulator S sk stateful₀ maxWindow).interact_eq env fuel []
    ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Every run of the real machine is a run of the simulated world and projects to a run of
    the functionality**, ending in a functionality state with the same exposure flag and latch
    position. -/
theorem latchedCorruptibleSigner_run_projects_to_ideal (S : SigScheme PK SK Sig) (sk : SK)
    (stateful₀ : Bool) (maxWindow : Nat)
    {tr : List (CorruptibleSignerCommand Sig × CorruptibleSignerReply SK Sig)}
    {c_final : CorruptibleSignerState SK}
    (hTrace : (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).ValidTrace
      ⟨sk, 0, false⟩ tr c_final) :
    ∃ a_final : CorruptibleSignState PK Sig,
      (corruptibleSignSimulator S sk stateful₀ maxWindow).ValidTrace
        (CorruptibleSignState.empty (S.derivePk sk) stateful₀) tr a_final ∧
      (idealSignCorruptibleMachine S (S.derivePk sk) stateful₀ maxWindow
        (fun req => S.sign sk req.epoch req.message)).ValidTrace
        (CorruptibleSignState.empty (S.derivePk sk) stateful₀)
        (projectTrace (corruptibleSignSimIn S sk) corruptibleSignVisOut tr) a_final ∧
      a_final.corrupted = c_final.corrupted ∧ a_final.inner.nextEpoch = c_final.nextEpoch := by
  obtain ⟨a_final, hW, hRel⟩ :=
    (latchedCorruptibleSigner_refines_simulator S sk stateful₀ maxWindow).lift_validTrace
      (a₀ := CorruptibleSignState.empty (S.derivePk sk) stateful₀) ⟨rfl, rfl, rfl, rfl, rfl⟩
      hTrace
  obtain ⟨_, hN, _, _, hCor⟩ := hRel
  exact ⟨a_final, hW,
    Machine.simulate_validTrace_project (corruptibleSignVisOut_simOut sk) hW, hCor, hN⟩

/-- **The corruptible latched signer is simulated by `idealSignCorruptibleMachine`.** For
    every initialized trace `tr` of the real machine with key `sk`:
    1. `tr` is, event for event, an initialized trace of the simulated ideal world;
    2. its translation is an initialized trace of the functionality;
    3. every signature the simulator injected verifies under the enrolled public key;
    4. every `.inject` of the translated trace is preceded by a `.corrupt`. -/
theorem latchedCorruptibleSigner_simulated_by_idealSignCorruptible (S : SigScheme PK SK Sig)
    (sk : SK) (stateful₀ : Bool) (maxWindow : Nat)
    {tr : List (CorruptibleSignerCommand Sig × CorruptibleSignerReply SK Sig)}
    (hAdmits : (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).AdmitsTrace tr) :
    (corruptibleSignSimulator S sk stateful₀ maxWindow).AdmitsTrace tr ∧
    (idealSignCorruptibleMachine S (S.derivePk sk) stateful₀ maxWindow
      (fun req => S.sign sk req.epoch req.message)).AdmitsTrace
      (projectTrace (corruptibleSignSimIn S sk) corruptibleSignVisOut tr) ∧
    (∀ p ∈ injectedEvents (projectTrace (corruptibleSignSimIn S sk) corruptibleSignVisOut tr),
      S.verify (S.derivePk sk) p.1.message p.2 = true) ∧
    (∀ (pre post : List (SignCommand Sig × SignReply Sig)) (req : SignRequest) (sig : Sig)
      (out : SignReply Sig),
      projectTrace (corruptibleSignSimIn S sk) corruptibleSignVisOut tr =
        pre ++ (SignCommand.inject req sig, out) :: post →
      (SignCommand.corrupt, SignReply.corrupted) ∈ pre) := by
  obtain ⟨c₀, c_final, hInit, hTrace⟩ := hAdmits
  have hInit' : c₀ = ⟨sk, 0, false⟩ := hInit
  rw [hInit'] at hTrace
  obtain ⟨a_final, hW, hI, _, _⟩ :=
    latchedCorruptibleSigner_run_projects_to_ideal S sk stateful₀ maxWindow hTrace
  refine ⟨⟨_, a_final, rfl, hW⟩, ⟨_, a_final, rfl, hI⟩,
    idealSignCorruptibleMachine_trace_injected_verified hI, ?_⟩
  intro pre post req sig out hEq
  rw [hEq] at hI
  exact idealSignCorruptibleMachine_inject_after_corrupt hI

/-- For a run of the real machine whose key is the simulator's, the emitted signatures of the
    translated trace are the emitted signatures of the run. -/
theorem latchedCorruptibleSigner_trace_emitted_eq_projected {S : SigScheme PK SK Sig} {sk : SK}
    {stateful₀ : Bool} {maxWindow : Nat} :
    ∀ {s s' : CorruptibleSignerState SK}
      {tr : List (CorruptibleSignerCommand Sig × CorruptibleSignerReply SK Sig)},
      (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).ValidTrace s tr s' →
      s.sk = sk →
      emittedEvents (projectTrace (corruptibleSignSimIn S sk) corruptibleSignVisOut tr) =
        corruptibleSignerEmitted tr
  | _, _, _, .nil _, _ => rfl
  | s, _, _, .accept (s' := s₁) (inp := inp) (out := out) (rest := rest) hStep hRest, hSk => by
    cases inp with
    | sign req =>
      obtain ⟨sig, _, _, hc, hOut⟩ := latchedCorruptibleSigner_sign_step_some hStep
      have hSk₁ : s₁.sk = sk := by
        rw [hc]
        exact hSk
      have ih := latchedCorruptibleSigner_trace_emitted_eq_projected hRest hSk₁
      rw [hOut]
      show (req, sig) :: emittedEvents
          (projectTrace (corruptibleSignSimIn S sk) corruptibleSignVisOut rest) =
        (req, sig) :: corruptibleSignerEmitted rest
      rw [ih]
    | exposeKey =>
      obtain ⟨hc, hOut⟩ := latchedCorruptibleSigner_exposeKey_step_some hStep
      have hSk₁ : s₁.sk = sk := by
        rw [hc]
        exact hSk
      have ih := latchedCorruptibleSigner_trace_emitted_eq_projected hRest hSk₁
      rw [hOut]
      exact ih
    | offlineSign req =>
      obtain ⟨sig, _, hSign, hc, hOut⟩ := latchedCorruptibleSigner_offlineSign_step_some hStep
      have hSk₁ : s₁.sk = sk := by
        rw [hc]
        exact hSk
      have ih := latchedCorruptibleSigner_trace_emitted_eq_projected hRest hSk₁
      rw [hSk] at hSign
      rw [hOut, projectTrace_cons_some (corruptibleSignSimIn_offlineSign hSign)]
      show (req, sig) :: emittedEvents
          (projectTrace (corruptibleSignSimIn S sk) corruptibleSignVisOut rest) =
        (req, sig) :: corruptibleSignerEmitted rest
      rw [ih]
    | register req sig =>
      obtain ⟨_, _, hc, hOut⟩ := latchedCorruptibleSigner_register_step_some hStep
      have hSk₁ : s₁.sk = sk := by
        rw [hc]
        exact hSk
      have ih := latchedCorruptibleSigner_trace_emitted_eq_projected hRest hSk₁
      rw [hOut]
      show (req, sig) :: emittedEvents
          (projectTrace (corruptibleSignSimIn S sk) corruptibleSignVisOut rest) =
        (req, sig) :: corruptibleSignerEmitted rest
      rw [ih]
  | s, _, _, .reject inp _ hRest, hSk =>
    latchedCorruptibleSigner_trace_emitted_eq_projected hRest
      ((latchedCorruptibleSigner_errStep_facts s inp).1.trans hSk)

/-- **Every signature the corruptible signer emits verifies under its public key**: honest,
    offline or registered, before or after the key is exposed. The guarantee is that of
    `idealSignCorruptibleMachine`, carried to the real machine by the simulation. -/
theorem latchedCorruptibleSigner_emitted_verified (S : SigScheme PK SK Sig) (sk : SK)
    (stateful₀ : Bool) (maxWindow : Nat)
    {tr : List (CorruptibleSignerCommand Sig × CorruptibleSignerReply SK Sig)}
    (hAdmits : (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).AdmitsTrace tr) :
    ∀ p ∈ corruptibleSignerEmitted tr, S.verify (S.derivePk sk) p.1.message p.2 = true := by
  obtain ⟨c₀, c_final, hInit, hTrace⟩ := hAdmits
  have hInit' : c₀ = ⟨sk, 0, false⟩ := hInit
  rw [hInit'] at hTrace
  obtain ⟨a_final, _, hI, _, _⟩ :=
    latchedCorruptibleSigner_run_projects_to_ideal S sk stateful₀ maxWindow hTrace
  have hVer := idealSignCorruptibleMachine_trace_emitted_verified hI
  rw [latchedCorruptibleSigner_trace_emitted_eq_projected hTrace rfl] at hVer
  exact hVer

/-- **Unexposed runs are honest runs.** If an initialized run of the corruptible signer ends
    with the key unexposed, then each of its events is an honest signature (no output is the
    key and no signature bypassed the latch), every signature verifies, and in stateful mode
    the epochs strictly increase. The epoch clause fails for exposed runs
    (`latchedCorruptibleSigner_exposed_run_reuses_epoch`). -/
theorem latchedCorruptibleSigner_unexposed_run_safe (S : SigScheme PK SK Sig) (sk : SK)
    (stateful₀ : Bool) (maxWindow : Nat)
    {tr : List (CorruptibleSignerCommand Sig × CorruptibleSignerReply SK Sig)}
    {c_final : CorruptibleSignerState SK}
    (hTrace : (latchedCorruptibleSignerMachine S sk stateful₀ maxWindow).ValidTrace
      ⟨sk, 0, false⟩ tr c_final)
    (hU : c_final.corrupted = false) :
    (∀ ev ∈ tr, ∃ (req : SignRequest) (sig : Sig),
      ev = (CorruptibleSignerCommand.sign req, CorruptibleSignerReply.signature sig)) ∧
    (∀ p ∈ corruptibleSignerEmitted tr, S.verify (S.derivePk sk) p.1.message p.2 = true) ∧
    (stateful₀ = true →
      (corruptibleSignerEmitted tr).Pairwise (fun a b => a.1.epoch < b.1.epoch)) := by
  obtain ⟨a_final, _, hI, hCor, _⟩ :=
    latchedCorruptibleSigner_run_projects_to_ideal S sk stateful₀ maxWindow hTrace
  obtain ⟨_, hVer, hPw, _, _⟩ :=
    idealSignCorruptibleMachine_uncorrupted_trace_safe hI (hCor.trans hU)
  rw [latchedCorruptibleSigner_trace_emitted_eq_projected hTrace rfl] at hVer hPw
  exact ⟨(latchedCorruptibleSigner_trace_unexposed hTrace hU).2, hVer, hPw⟩

end Headline

/-! ## 7. Rejected behaviours -/

/-- Scheme with two distinct secret keys (`false`, `true`) mapping to one public key `0xA5`
    and signing with key-and-message-bound tag `0xA5 ^^^ m.headD 0`. -/
def corruptToyTwoKeyScheme : SigScheme UInt8 Bool UInt8 where
  derivePk _ := 0xA5
  sign _ _ m := some (0xA5 ^^^ m.headD 0)
  verify pk m sig := decide (sig = pk ^^^ m.headD 0)
  correct _ _ _ _ h := by
    injection h with hEq
    subst hEq
    exact decide_eq_true rfl

/-- **A simulator holding another key is told apart in one round.** If `skSim ≠ sk₀`, the
    environment that asks for the key sees `sk₀` from the real machine and `skSim` from the
    simulated world, whether or not the two keys have the same public key. -/
theorem corruptibleSignSimulator_wrong_key_view_differs {PK SK Sig : Type}
    (S : SigScheme PK SK Sig) {sk₀ skSim : SK} (hNe : skSim ≠ sk₀) (stateful₀ : Bool)
    (maxWindow : Nat) :
    (latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow).interact
        (fun _ => some CorruptibleSignerCommand.exposeKey) 1 ⟨sk₀, 0, false⟩ [] ≠
      (corruptibleSignSimulator S skSim stateful₀ maxWindow).interact
        (fun _ => some CorruptibleSignerCommand.exposeKey) 1
        (CorruptibleSignState.empty (S.derivePk skSim) stateful₀) [] := by
  intro h
  have h' : [some (CorruptibleSignerReply.key sk₀ : CorruptibleSignerReply SK Sig)] =
      [some (CorruptibleSignerReply.key skSim)] := h
  injection h' with h1 _
  injection h1 with h2
  injection h2 with h3
  exact hNe h3.symm

/-- **No refinement to a simulator holding another key.** -/
theorem corruptibleSignSimulator_wrong_key_not_refinement {PK SK Sig : Type}
    (S : SigScheme PK SK Sig) {sk₀ skSim : SK} (hNe : skSim ≠ sk₀) (stateful₀ : Bool)
    (maxWindow : Nat) :
    ¬ Nonempty (latchedCorruptibleSignerMachine S sk₀ stateful₀ maxWindow ⊑
      corruptibleSignSimulator S skSim stateful₀ maxWindow) := by
  rintro ⟨sim⟩
  obtain ⟨hInitA, hRel⟩ := sim.init_ok (c₀ := ⟨sk₀, 0, false⟩) rfl
  have hInitA' : sim.absInit ⟨sk₀, 0, false⟩ =
      CorruptibleSignState.empty (S.derivePk skSim) stateful₀ := hInitA
  have hEq := sim.interact_eq (fun _ => some CorruptibleSignerCommand.exposeKey) 1 [] hRel
  rw [hInitA'] at hEq
  exact corruptibleSignSimulator_wrong_key_view_differs S hNe stateful₀ maxWindow hEq

/-- The two keys of `corruptToyTwoKeyScheme` have the same public key and sign identically, and
    a simulator holding the other one is still told apart. -/
theorem corruptToyTwoKey_same_pk_wrong_key_view_differs :
    (latchedCorruptibleSignerMachine corruptToyTwoKeyScheme false true 8).interact
        (fun _ => some CorruptibleSignerCommand.exposeKey) 1 ⟨false, 0, false⟩ [] ≠
      (corruptibleSignSimulator corruptToyTwoKeyScheme true true 8).interact
        (fun _ => some CorruptibleSignerCommand.exposeKey) 1
        (CorruptibleSignState.empty (corruptToyTwoKeyScheme.derivePk true) true) [] :=
  corruptibleSignSimulator_wrong_key_view_differs corruptToyTwoKeyScheme (by decide) true 8

/-- The run `sign` at epoch `0`, `exposeKey`, `offlineSign` at epoch `0` of the stateful keyed-tag
    signer: an initialized trace that ends exposed. -/
theorem witness_latchedCorruptibleSigner_exposed_run :
    ∃ tr : List (CorruptibleSignerCommand UInt8 × CorruptibleSignerReply Bool UInt8),
      (latchedCorruptibleSignerMachine corruptToyTwoKeyScheme false true 8).AdmitsTrace tr ∧
      corruptibleSignerEmitted tr =
        [((⟨0, []⟩ : SignRequest), 0xA5), ((⟨0, [1]⟩ : SignRequest), 0xA4)] :=
  ⟨[(.sign ⟨0, []⟩, .signature 0xA5), (.exposeKey, .key false),
      (.offlineSign ⟨0, [1]⟩, .signature 0xA4)],
    ⟨⟨false, 0, false⟩, ⟨false, 1, true⟩, rfl,
      .accept (s' := ⟨false, 1, false⟩) rfl
        (.accept (s' := ⟨false, 1, true⟩) rfl
          (.accept (s' := ⟨false, 1, true⟩) rfl (.nil _)))⟩, rfl⟩

/-- **The one-time-epoch property fails once the key is exposed.** Without the hypothesis that
    the run ends unexposed, the epoch clause of `latchedCorruptibleSigner_unexposed_run_safe`
    is false: after `sign` at epoch `0` and `exposeKey`, an `offlineSign` at epoch `0` is
    accepted, so two emitted signatures share an epoch. -/
theorem latchedCorruptibleSigner_exposed_run_reuses_epoch :
    ¬ (∀ (tr : List (CorruptibleSignerCommand UInt8 × CorruptibleSignerReply Bool UInt8))
        (c_final : CorruptibleSignerState Bool),
        (latchedCorruptibleSignerMachine corruptToyTwoKeyScheme false true 8).ValidTrace
          ⟨false, 0, false⟩ tr c_final →
        (corruptibleSignerEmitted tr).Pairwise (fun a b => a.1.epoch < b.1.epoch)) := by
  intro h
  have hTr : (latchedCorruptibleSignerMachine corruptToyTwoKeyScheme false true 8).ValidTrace
      ⟨false, 0, false⟩
      [(.sign ⟨0, []⟩, .signature 0xA5), (.exposeKey, .key false),
        (.offlineSign ⟨0, [1]⟩, .signature 0xA4)] ⟨false, 1, true⟩ :=
    .accept (s' := ⟨false, 1, false⟩) rfl
      (.accept (s' := ⟨false, 1, true⟩) rfl
        (.accept (s' := ⟨false, 1, true⟩) rfl (.nil _)))
  have hPw : List.Pairwise (fun a b : SignRequest × UInt8 => a.1.epoch < b.1.epoch)
      [((⟨0, []⟩ : SignRequest), 0xA5), ((⟨0, [1]⟩ : SignRequest), 0xA4)] := h _ _ hTr
  exact Nat.lt_irrefl 0 ((List.pairwise_cons.mp hPw).1 _ (List.mem_cons.mpr (.inl rfl)))

/-- Key-and-message-bound scheme whose signer fails at epoch `0` and emits verified tags for `ep > 0`. -/
def corruptToyBurnScheme : SigScheme UInt8 UInt8 UInt8 where
  derivePk sk := sk ^^^ 0x5A
  sign sk ep m := if ep = 0 then none else some ((sk ^^^ 0x5A) ^^^ m.headD 0)
  verify pk m sig := decide (sig = pk ^^^ m.headD 0)
  correct sk ep m sig h := by
    split at h
    · cases h
    · injection h with hEq
      subst hEq
      exact decide_eq_true rfl

/-- **The projection to the functionality is not a `DataRefines`.** For the stateful signer of
    `corruptToyBurnScheme` with window `0`, no `DataRefines` witness relates the real machine
    to `idealSignCorruptibleMachine` through the simulator's interface maps: the failed
    signature at epoch `0` consumes that epoch in the real machine, `sim_reject` keeps the
    functionality's state fixed, and the request for epoch `1` that the real machine then
    accepts is outside the functionality's window. -/
theorem latchedCorruptibleSigner_no_dataRefines_to_ideal :
    ¬ Nonempty (DataRefines (latchedCorruptibleSignerMachine corruptToyBurnScheme 0 true 0)
      (idealSignCorruptibleMachine corruptToyBurnScheme 0x5A true 0
        (fun req => corruptToyBurnScheme.sign 0 req.epoch req.message))
      (corruptibleSignSimIn corruptToyBurnScheme 0) corruptibleSignVisOut) := by
  rintro ⟨D⟩
  obtain ⟨hInitA, hRel₀⟩ := D.init_ok (c₀ := ⟨0, 0, false⟩) rfl
  have hA₀ : D.absInit ⟨0, 0, false⟩ = CorruptibleSignState.empty 0x5A true := hInitA
  rw [hA₀] at hRel₀
  have hRel₁ := D.sim_reject (inp := .sign ⟨0, []⟩) hRel₀ rfl
  obtain ⟨a', hStepA, _⟩ := D.sim_visible (inp := .sign ⟨1, []⟩) (out := .signature 0x5A)
    (j := .sign ⟨1, []⟩) (c' := ⟨0, 2, false⟩) hRel₁ rfl rfl
  have hNone : (idealSignCorruptibleMachine corruptToyBurnScheme 0x5A true 0
      (fun req => corruptToyBurnScheme.sign 0 req.epoch req.message)).step
      (CorruptibleSignState.empty 0x5A true) (.sign ⟨1, []⟩) = none := rfl
  rw [hNone] at hStepA
  cases hStepA

#tooth_pair latchedCorruptibleSigner_adaptive_view_eq_simulator vs
  corruptibleSignSimulator_wrong_key_view_differs
#tooth_pair latchedCorruptibleSigner_adaptive_view_eq_simulator vs
  corruptToyTwoKey_same_pk_wrong_key_view_differs
#tooth_pair latchedCorruptibleSigner_simulated_by_idealSignCorruptible vs
  idealSignCorruptible_inject_rejected_before_corrupt
#tooth_pair latchedCorruptibleSigner_simulated_by_idealSignCorruptible vs
  corruptibleSignSimulator_wrong_key_not_refinement
#tooth_pair latchedCorruptibleSigner_run_projects_to_ideal vs
  corruptibleSignSimulator_register_rejected_unexposed
#tooth_pair latchedCorruptibleSigner_unexposed_run_safe vs
  latchedCorruptibleSigner_exposed_run_reuses_epoch
#tooth_pair latchedCorruptibleSigner_run_projects_to_ideal vs
  latchedCorruptibleSigner_no_dataRefines_to_ideal

#verify_kernel
  Qsag.Spec.latchedCorruptibleSigner_refines_simulator

#verify_constructive
  Qsag.Spec.Machine.simulate_step_of
  Qsag.Spec.Machine.simulate_step_some
  Qsag.Spec.Machine.simulate_reject_of
  Qsag.Spec.Machine.simulate_refuse_of
  Qsag.Spec.Machine.simulate_validTrace_project
  Qsag.Spec.Machine.validTrace_split
  Qsag.Spec.Refines.interact_eq
  Qsag.Spec.latchedCorruptibleSigner_sign_step_some
  Qsag.Spec.latchedCorruptibleSigner_exposeKey_step
  Qsag.Spec.latchedCorruptibleSigner_exposeKey_step_some
  Qsag.Spec.latchedCorruptibleSigner_offlineSign_step_some
  Qsag.Spec.latchedCorruptibleSigner_register_step_some
  Qsag.Spec.latchedCorruptibleSigner_errStep_facts
  Qsag.Spec.latchedCorruptibleSigner_trace_key
  Qsag.Spec.latchedCorruptibleSigner_trace_unexposed
  Qsag.Spec.corruptibleSignVisOut_simOut
  Qsag.Spec.corruptibleSignSimIn_offlineSign
  Qsag.Spec.corruptibleSignSimIn_offlineSign_none
  Qsag.Spec.corruptibleSignSimulator_step_of
  Qsag.Spec.corruptibleSignSimulator_reject_of
  Qsag.Spec.corruptibleSignSimulator_refuse_of
  Qsag.Spec.corruptibleSignSimulator_register_rejected_unexposed
  Qsag.Spec.corruptibleSignSimulator_offlineSign_rejected_unexposed
  Qsag.Spec.idealSignCorruptibleMachine_trace_corrupt_event
  Qsag.Spec.idealSignCorruptibleMachine_inject_after_corrupt
  Qsag.Spec.latchedCorruptibleSigner_adaptive_view_eq_simulator
  Qsag.Spec.latchedCorruptibleSigner_run_projects_to_ideal
  Qsag.Spec.latchedCorruptibleSigner_simulated_by_idealSignCorruptible
  Qsag.Spec.latchedCorruptibleSigner_trace_emitted_eq_projected
  Qsag.Spec.latchedCorruptibleSigner_emitted_verified
  Qsag.Spec.latchedCorruptibleSigner_unexposed_run_safe
  Qsag.Spec.idealSignCorruptible_inject_rejected_before_corrupt
  Qsag.Spec.corruptibleSignSimulator_wrong_key_view_differs
  Qsag.Spec.corruptibleSignSimulator_wrong_key_not_refinement
  Qsag.Spec.corruptToyTwoKey_same_pk_wrong_key_view_differs
  Qsag.Spec.witness_latchedCorruptibleSigner_exposed_run
  Qsag.Spec.latchedCorruptibleSigner_exposed_run_reuses_epoch
  Qsag.Spec.latchedCorruptibleSigner_no_dataRefines_to_ideal

#verify_inhabited Qsag.Spec.latchedCorruptibleSigner_simulated_by_idealSignCorruptible
  Qsag.Spec.witness_latchedCorruptibleSigner_exposed_run

#print axioms Qsag.Spec.latchedCorruptibleSigner_refines_simulator
#print axioms Qsag.Spec.latchedCorruptibleSigner_adaptive_view_eq_simulator
#print axioms Qsag.Spec.latchedCorruptibleSigner_simulated_by_idealSignCorruptible
#print axioms Qsag.Spec.latchedCorruptibleSigner_unexposed_run_safe

end Qsag.Spec
end
