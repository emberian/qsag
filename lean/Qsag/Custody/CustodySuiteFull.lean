module
/-
# Custody, policy, addressing and migration

Operational party-machine exports at the end of this file use public wire events,
enrolled MAC authority, actual masked HD observations, authenticated policy rotation,
and a commit-before-verifier-challenge Co-ZK circuit transcript. The FTS circuit uses
Rust's two polynomial-basis lanes, round-constant encoding, MDS and feed-forward.

Earlier algebraic/evidence machines are retained under explicit Evidence names for
compatibility and negative tests. They are not exported as network machines. Named
compatibility theorems retain their evidence claims and add operational guarantees.

Model boundaries: the new FTS interpreter records round-power openings and final
MAC barriers; it is not a proof of Rust's per-party power-tuple preprocessing or a
bytecode refinement. HD privacy assumes independently uniform one-time masks and
is conditional on the enrolled public-key fiber. Co-ZK uses independent private
verifier coins, not an unproved Fiat-Shamir random-oracle reduction. Policy MAC
verification is concrete; computational unforgeability remains a primitive security
assumption. No computational-security assumption is replaced by nonempty bytes.
-/

public import Qsag.Math.Constructive
public import Qsag.Exec.SimulationSpine
public import Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.UcGames
public import Qsag.Protocol.Threshold.MaliciousSecurity

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 0. Shared Multi-Turn Guard Transition, Quarantine Trace & `SimulationSpine` Bridge -/

/-- Outcome of a stateful custody guard transition where rejected attempts may still mutate
    persistent quarantine or burn state. -/
inductive CustodyStepOutcome (S Out Err : Type) where
  | accepted (nextState : S) (output : Out)
  | rejected (nextState : S) (err : Err)
  deriving DecidableEq, Repr

/-- Convert `CustodyStepOutcome` into `SimulationSpine`'s `StepOutcome`. -/
def CustodyStepOutcome.toStepOutcome {S Out Err : Type} :
    CustodyStepOutcome S Out Err → StepOutcome S Out Err
  | .accepted s' out => .ok s' out
  | .rejected s' err => .err s' err

/-- Lift any `CustodyStepOutcome` transition into a compositional `SimulationSpine` `PartyMachine`,
    preserving quarantine/burn state mutations on rejected inputs. -/
def PartyMachine.ofCustodyStep {S In Out Err : Type}
    (step : S → In → CustodyStepOutcome S Out Err) : PartyMachine S In Out :=
  PartyMachine.ofOutcome (fun s inp => (step s inp).toStepOutcome)

/-- Pure partial Mealy projection (`S → In → Option (S × Out)`) for compositional simulation spines. -/
def custodyAcceptedStep {S In Out Err : Type}
    (step : S → In → CustodyStepOutcome S Out Err) (s : S) (inp : In) : Option (S × Out) :=
  match step s inp with
  | .accepted s' out => some (s', out)
  | .rejected _ _ => none

/-- Multi-turn execution trace recording both accepted outputs (`some out`) and rejected attempts
    (`none`, including state-mutating quarantine transitions). -/
inductive ValidCustodyTrace {S In Out Err : Type}
    (step : S → In → CustodyStepOutcome S Out Err) :
    S → List (In × Option Out) → S → Prop where
  | nil (s : S) : ValidCustodyTrace step s [] s
  | consAccepted {s s' sFinal : S} {inp : In} {out : Out} {rest : List (In × Option Out)}
      (hStep : step s inp = .accepted s' out)
      (hRest : ValidCustodyTrace step s' rest sFinal) :
      ValidCustodyTrace step s ((inp, some out) :: rest) sFinal
  | consRejected {s s' sFinal : S} {inp : In} {err : Err} {rest : List (In × Option Out)}
      (hStep : step s inp = .rejected s' err)
      (hRest : ValidCustodyTrace step s' rest sFinal) :
      ValidCustodyTrace step s ((inp, none) :: rest) sFinal

/-- Extract all accepted `(In × Out)` pairs emitted along a multi-turn custody trace. -/
def traceApprovedPairs {In Out : Type} : List (In × Option Out) → List (In × Out)
  | [] => []
  | (inp, some out) :: rest => (inp, out) :: traceApprovedPairs rest
  | (_, none) :: rest => traceApprovedPairs rest

/-- Every `ValidCustodyTrace` induces a valid `SimulationSpine` `PartyMachine.ValidTrace`
    with identical initial/final states and accepted `(In × Out)` transcript. -/
theorem validCustodyTrace_to_partyMachine_validTrace {S In Out Err : Type}
    {step : S → In → CustodyStepOutcome S Out Err}
    {s₀ sFinal : S} {trace : List (In × Option Out)}
    (hTr : ValidCustodyTrace step s₀ trace sFinal) :
    (PartyMachine.ofCustodyStep step).ValidTrace s₀ (traceApprovedPairs trace) sFinal := by
  induction hTr with
  | nil s => exact .nil s
  | @consAccepted s s' _ inp out _ hStep _ ih =>
    apply PartyMachine.ValidTrace.accept _ ih
    unfold PartyMachine.ofCustodyStep PartyMachine.ofOutcome
    dsimp only
    rw [hStep]
    rfl
  | @consRejected s s' _ inp err _ hStep _ ih =>
    have hNone : (PartyMachine.ofCustodyStep step).step s inp = none := by
      unfold PartyMachine.ofCustodyStep PartyMachine.ofOutcome
      dsimp only
      rw [hStep]
      rfl
    have hErr : (PartyMachine.ofCustodyStep step).errStep s inp = s' := by
      unfold PartyMachine.ofCustodyStep PartyMachine.ofOutcome
      dsimp only
      rw [hStep]
      rfl
    exact PartyMachine.ValidTrace.reject inp hNone (hErr ▸ ih)

/-- Extract all accepted outputs emitted along a multi-turn custody trace. -/
def traceApprovedOutputs {In Out : Type} : List (In × Option Out) → List Out
  | [] => []
  | (_, some out) :: rest => out :: traceApprovedOutputs rest
  | (_, none) :: rest => traceApprovedOutputs rest

@[simp] theorem traceApprovedOutputs_nil {In Out : Type} :
    traceApprovedOutputs ([] : List (In × Option Out)) = [] := by rfl

@[simp] theorem traceApprovedOutputs_cons_some {In Out : Type}
    (inp : In) (out : Out) (rest : List (In × Option Out)) :
    traceApprovedOutputs ((inp, some out) :: rest) = out :: traceApprovedOutputs rest := by rfl

@[simp] theorem traceApprovedOutputs_cons_none {In Out : Type}
    (inp : In) (rest : List (In × Option Out)) :
    traceApprovedOutputs ((inp, none) :: rest) = traceApprovedOutputs rest := by rfl

/-! ## §1. `qsag-fts` — Constant-Sum Winternitz (`WOTS+CS`) & 48-Round `x^7` SPN Deferred-MAC Session -/

/-- Validity predicate for an `L`-chain Constant-Sum Winternitz codeword with base `base` and sum `S`. -/
@[expose] def validWotsCsCodeword (L base S : Nat) (d : List Nat) : Prop :=
  d.length = L ∧ (∀ x ∈ d, x < base) ∧ d.foldr (· + ·) 0 = S

/-- Iterated Winternitz chain evaluation from step `start` for `steps` applications of `F chainIdx`. -/
@[expose] def wotsChainIter {Node : Type} (F : Nat → Nat → Node → Node)
    (chainIdx start : Nat) : Nat → Node → Node
  | 0, x => x
  | k + 1, x => wotsChainIter F chainIdx (start + 1) k (F chainIdx start x)

theorem wotsChainIter_add {Node : Type} (F : Nat → Nat → Node → Node)
    (chainIdx start a b : Nat) (x : Node) :
    wotsChainIter F chainIdx start (a + b) x =
      wotsChainIter F chainIdx (start + a) b (wotsChainIter F chainIdx start a x) := by
  induction a generalizing start x with
  | zero =>
    simp [wotsChainIter]
  | succ a ih =>
    have hAdd : a + 1 + b = (a + b) + 1 := by omega
    have hStart : start + 1 + a = start + (a + 1) := by omega
    rw [hAdd]
    simp only [wotsChainIter]
    rw [ih (start + 1) (F chainIdx start x), hStart]

private def findStrictLtOfSumLt :
    (xs ys : List Nat) →
    (hLen : xs.length = ys.length) →
    xs.foldr (· + ·) 0 < ys.foldr (· + ·) 0 →
    { i : Fin ys.length // xs[i.val]'(Nat.lt_of_lt_of_eq i.isLt hLen.symm) < ys[i.val] }
  | [], [], _, hLt => False.elim (Nat.lt_irrefl 0 hLt)
  | x :: xs, y :: ys, hLen, hLt =>
    if hxy : x < y then
      ⟨⟨0, Nat.zero_lt_succ ys.length⟩, hxy⟩
    else
      have hLen' : xs.length = ys.length := Nat.succ.inj hLen
      have hTailLt : xs.foldr (· + ·) 0 < ys.foldr (· + ·) 0 := by
        simp only [List.foldr_cons] at hLt
        omega
      let ⟨idx, hIdxLt⟩ := findStrictLtOfSumLt xs ys hLen' hTailLt
      ⟨⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩, hIdxLt⟩

private def extractStrictDecreaseAux :
    (dStar d : List Nat) →
    (hLen : dStar.length = d.length) →
    dStar ≠ d →
    dStar.foldr (· + ·) 0 = d.foldr (· + ·) 0 →
    { i : Fin d.length // dStar[i.val]'(Nat.lt_of_lt_of_eq i.isLt hLen.symm) < d[i.val] }
  | [], [], _, hNe, _ => False.elim (hNe rfl)
  | x :: xs, y :: ys, hLen, hNe, hSum =>
    have hLen' : xs.length = ys.length := Nat.succ.inj hLen
    if hlt : x < y then
      ⟨⟨0, Nat.zero_lt_succ ys.length⟩, hlt⟩
    else if hgt : y < x then
      have hTailLt : xs.foldr (· + ·) 0 < ys.foldr (· + ·) 0 := by
        simp only [List.foldr_cons] at hSum
        omega
      let ⟨idx, hIdxLt⟩ := findStrictLtOfSumLt xs ys hLen' hTailLt
      ⟨⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩, hIdxLt⟩
    else
      have hxy : x = y := by omega
      have hTailNe : xs ≠ ys := fun hEq => hNe (by subst hxy hEq; rfl)
      have hTailSum : xs.foldr (· + ·) 0 = ys.foldr (· + ·) 0 := by
        simp only [List.foldr_cons] at hSum
        omega
      let ⟨idx, hIdxLt⟩ := extractStrictDecreaseAux xs ys hLen' hTailNe hTailSum
      ⟨⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩, hIdxLt⟩

/-- Constructive index extractor (no choice operator) witnessing strict coordinate decrease
    between any two distinct constant-sum codewords. -/
def extractWotsCsDecrease {L base S : Nat} (dStar d : List Nat)
    (hStar : validWotsCsCodeword L base S dStar)
    (hOrig : validWotsCsCodeword L base S d)
    (hNe : dStar ≠ d) :
    { i : Fin L //
        dStar[i.val]'(Nat.lt_of_lt_of_eq i.isLt hStar.1.symm) <
        d[i.val]'(Nat.lt_of_lt_of_eq i.isLt hOrig.1.symm) } :=
  let ⟨idx, hLt⟩ :=
    extractStrictDecreaseAux dStar d (hStar.1.trans hOrig.1.symm) hNe (hStar.2.2.trans hOrig.2.2.symm)
  ⟨⟨idx.val, Nat.lt_of_lt_of_eq idx.isLt hOrig.1⟩, hLt⟩

/-- **1-Time `WOTS+CS` Strict Incomparability (`wotsCs_single_use_incomparable`)**:
    For arbitrary chain count `L`, digit base `base`, and target sum `S` (including deployed
    `(L = 68, base = 5, S = 136)` and `(L = 68, base = 5, S = 136)`), any two distinct valid
    codewords `dStar ≠ d` satisfy `∃ i : Fin L, dStar[i] < d[i]`. -/
theorem wotsCs_single_use_incomparable (L base S : Nat) (dStar d : List Nat)
    (hStar : validWotsCsCodeword L base S dStar)
    (hOrig : validWotsCsCodeword L base S d)
    (hNe : dStar ≠ d) :
    ∃ i : Fin L,
      dStar[i.val]'(Nat.lt_of_lt_of_eq i.isLt hStar.1.symm) <
      d[i.val]'(Nat.lt_of_lt_of_eq i.isLt hOrig.1.symm) := by
  let ⟨i, hi⟩ := extractWotsCsDecrease dStar d hStar hOrig hNe
  exact ⟨i, hi⟩

/-- Deployed `(L = 68, base = 5, S = 136)` (`winternitz_w = 5`, `CUSTODY_H10_W5`) instantiation
    of `wotsCs_single_use_incomparable`. -/
theorem wotsCs_single_use_incomparable_deployed (dStar d : List Nat)
    (hStar : validWotsCsCodeword 68 5 136 dStar)
    (hOrig : validWotsCsCodeword 68 5 136 d)
    (hNe : dStar ≠ d) :
    ∃ i : Fin 68,
      dStar[i.val]'(Nat.lt_of_lt_of_eq i.isLt hStar.1.symm) <
      d[i.val]'(Nat.lt_of_lt_of_eq i.isLt hOrig.1.symm) :=
  wotsCs_single_use_incomparable 68 5 136 dStar d hStar hOrig hNe

/-- Constructive backward chain preimage witness against an honest 1-time `WOTS+CS` signature. -/
structure WotsChainPreimageWitness {Node : Type} {L : Nat}
    (F : Nat → Nat → Node → Node) (honestSig : Fin L → Node)
    (dStar d : List Nat) (hStarLen : dStar.length = L) (hOrigLen : d.length = L) where
  chainIdx : Fin L
  strict_decrease : dStar[chainIdx.val]'(Nat.lt_of_lt_of_eq chainIdx.isLt hStarLen.symm) <
                    d[chainIdx.val]'(Nat.lt_of_lt_of_eq chainIdx.isLt hOrigLen.symm)
  preimageNode : Node
  step_preimage_eq :
    F chainIdx.val (d[chainIdx.val]'(Nat.lt_of_lt_of_eq chainIdx.isLt hOrigLen.symm) - 1) preimageNode =
      honestSig chainIdx

/-- Constructive step-collision (claw) witness in `F` when two distinct chain states merge before `pk`. -/
structure WotsChainCollisionWitness {Node : Type} (F : Nat → Nat → Node → Node) (base : Nat) where
  chainIdx : Nat
  stepPos : Nat
  step_lt : stepPos + 1 < base
  nodeA : Node
  nodeB : Node
  nodes_ne : nodeA ≠ nodeB
  step_eq : F chainIdx stepPos nodeA = F chainIdx stepPos nodeB

private def extractChainClaw {Node : Type} [DecidableEq Node]
    (F : Nat → Nat → Node → Node) (chainIdx base : Nat) :
    (start rem : Nat) → (a b : Node) →
    start + rem + 1 = base →
    a ≠ b →
    wotsChainIter F chainIdx start rem a = wotsChainIter F chainIdx start rem b →
    WotsChainCollisionWitness F base
  | _, 0, _, _, _, hNe, hEq => False.elim (hNe hEq)
  | start, rem + 1, a, b, hBound, hNe, hEq =>
    if hStepEq : F chainIdx start a = F chainIdx start b then
      { chainIdx := chainIdx
        stepPos := start
        step_lt := by omega
        nodeA := a
        nodeB := b
        nodes_ne := hNe
        step_eq := hStepEq }
    else
      extractChainClaw F chainIdx base (start + 1) rem
        (F chainIdx start a) (F chainIdx start b) (by omega) hStepEq hEq

/-- **Constructive `WOTS+CS` 1-CMA Chain Preimage Reduction (`wotsCs_euf_1cma_extract_chain_preimage`)**:
    Given public endpoints `pk i = F^(base - 1)(sk i)`, one honest signature
    `honestSig i = F^(d[i])(sk i)` on valid codeword `d`, and any valid forged signature
    `forgedSig` on distinct codeword `dStar ≠ d` (`F^(base - 1 - dStar[i])(forgedSig i) = pk i`),
    constructively (no choice operator) extracts EITHER a direct 1-step backward chain preimage
    of `honestSig i` at an index with `dStar[i] < d[i]`, OR an explicit step collision in `F`. -/
def wotsCs_euf_1cma_extract_chain_preimage {Node : Type} [DecidableEq Node]
    {L base S : Nat} (F : Nat → Nat → Node → Node)
    (sk : Fin L → Node)
    (d dStar : List Nat)
    (hOrig : validWotsCsCodeword L base S d)
    (hStar : validWotsCsCodeword L base S dStar)
    (hNe : dStar ≠ d)
    (honestSig forgedSig : Fin L → Node)
    (hHonest : ∀ i : Fin L,
      honestSig i = wotsChainIter F i.val 0 (d[i.val]'(Nat.lt_of_lt_of_eq i.isLt hOrig.1.symm)) (sk i))
    (hForgedVerifies : ∀ i : Fin L,
      let diStar := dStar[i.val]'(Nat.lt_of_lt_of_eq i.isLt hStar.1.symm)
      wotsChainIter F i.val diStar (base - 1 - diStar) (forgedSig i) =
        wotsChainIter F i.val 0 (base - 1) (sk i)) :
    PSum (WotsChainPreimageWitness F honestSig dStar d hStar.1 hOrig.1)
         (WotsChainCollisionWitness F base) :=
  let ⟨i, hiLt⟩ := extractWotsCsDecrease dStar d hStar hOrig hNe
  let di := d[i.val]'(Nat.lt_of_lt_of_eq i.isLt hOrig.1.symm)
  let diStar := dStar[i.val]'(Nat.lt_of_lt_of_eq i.isLt hStar.1.symm)
  have hDiLtBase : di < base := hOrig.2.1 di (List.getElem_mem _)
  let k := di - 1 - diStar
  let u := wotsChainIter F i.val diStar k (forgedSig i)
  let vForged := F i.val (di - 1) u
  have hStepU : wotsChainIter F i.val diStar (k + 1) (forgedSig i) = vForged := by
    rw [wotsChainIter_add F i.val diStar k 1 (forgedSig i)]
    have hPos : diStar + k = di - 1 := by omega
    simp [wotsChainIter, u, vForged, hPos]
  if hHit : vForged = honestSig i then
    .inl { chainIdx := i
           strict_decrease := hiLt
           preimageNode := u
           step_preimage_eq := hHit }
  else
    let rem := base - 1 - di
    have hSplitForged :
        wotsChainIter F i.val di rem vForged =
          wotsChainIter F i.val 0 (base - 1) (sk i) := by
      have hVer := hForgedVerifies i
      dsimp only at hVer
      have hDecomp : base - 1 - diStar = (k + 1) + rem := by omega
      have hStartEq : diStar + (k + 1) = di := by omega
      rw [hDecomp, wotsChainIter_add, hStepU, hStartEq] at hVer
      exact hVer
    have hSplitHonest :
        wotsChainIter F i.val di rem (honestSig i) =
          wotsChainIter F i.val 0 (base - 1) (sk i) := by
      have hDecomp : base - 1 = di + rem := by omega
      rw [hDecomp, wotsChainIter_add, Nat.zero_add, ← hHonest i]
    .inr (extractChainClaw F i.val base di rem vForged (honestSig i)
            (by omega) hHit (hSplitForged.trans hSplitHonest.symm))

private theorem foldr_add_replicate : ∀ (n c : Nat),
    (List.replicate n c).foldr (· + ·) 0 = n * c
  | 0, _ => by simp
  | n + 1, c => by
    simp only [List.replicate_succ, List.foldr_cons, foldr_add_replicate n c, Nat.succ_mul]
    omega

/-- Concrete first honest codeword at `(L = 68, S = 136)`: `[3, 1, 2, 2, ..., 2]`. -/
def wotsTwoUseD1 : List Nat := 3 :: 1 :: List.replicate 66 2

/-- Concrete second honest codeword at `(L = 68, S = 136)`: `[1, 3, 2, 2, ..., 2]`. -/
def wotsTwoUseD2 : List Nat := 1 :: 3 :: List.replicate 66 2

/-- Concrete forged third codeword at `(L = 68, S = 136)`: `[2, 2, 2, 2, ..., 2]`. -/
def wotsTwoUseDStar : List Nat := List.replicate 68 2

/-- Explicit forward-only signature combination when two codewords cover every coordinate of `dStar`. -/
def wotsForwardOnlyForge {Node : Type} (F : Nat → Nat → Node → Node)
    (sig1 sig2 : Fin 68 → Node) (i : Fin 68) : Node :=
  if i.val = 0 then F 0 1 (sig2 i)
  else if i.val = 1 then F 1 1 (sig1 i)
  else sig1 i

/-- **`#tooth` 2-Signature Collapse (`tooth_wotsCs_two_signatures_enable_forward_only_forgery`)**:
    Once an epoch allows `count >= 2` signatures under the same deployed `WOTS+CS` leaf
    (`L = 68, base = 5, S = 136`, `winternitz_w = 5`), two distinct valid codewords `d¹` and `d²`
    satisfy `∀ i, min(d¹[i], d²[i]) ≤ d*[i]` on a third distinct valid codeword `d* ∉ {d¹, d²}`,
    enabling an explicit **forward-only** signature forgery for **every** chain function `F` with
    zero backward hash inversions! -/
theorem tooth_wotsCs_two_signatures_enable_forward_only_forgery :
    validWotsCsCodeword 68 5 136 wotsTwoUseD1 ∧
    validWotsCsCodeword 68 5 136 wotsTwoUseD2 ∧
    validWotsCsCodeword 68 5 136 wotsTwoUseDStar ∧
    wotsTwoUseD1 ≠ wotsTwoUseD2 ∧
    wotsTwoUseDStar ≠ wotsTwoUseD1 ∧
    wotsTwoUseDStar ≠ wotsTwoUseD2 ∧
    (∀ i : Fin 68,
      Nat.min (wotsTwoUseD1[i.val]'(by simp [wotsTwoUseD1]))
              (wotsTwoUseD2[i.val]'(by simp [wotsTwoUseD2])) ≤
        wotsTwoUseDStar[i.val]'(by simp [wotsTwoUseDStar])) ∧
    (∀ {Node : Type} (F : Nat → Nat → Node → Node) (sk : Fin 68 → Node),
      let sig1 : Fin 68 → Node := fun i =>
        wotsChainIter F i.val 0 (wotsTwoUseD1[i.val]'(by simp [wotsTwoUseD1])) (sk i)
      let sig2 : Fin 68 → Node := fun i =>
        wotsChainIter F i.val 0 (wotsTwoUseD2[i.val]'(by simp [wotsTwoUseD2])) (sk i)
      let forged := wotsForwardOnlyForge F sig1 sig2
      ∀ i : Fin 68,
        let diStar := wotsTwoUseDStar[i.val]'(by simp [wotsTwoUseDStar])
        wotsChainIter F i.val diStar (5 - 1 - diStar) (forged i) =
          wotsChainIter F i.val 0 (5 - 1) (sk i)) := by
  have hBound5_1 : ∀ x ∈ wotsTwoUseD1, x < 5 := by
    intro x hx
    simp only [wotsTwoUseD1, List.mem_cons] at hx
    rcases hx with rfl | rfl | hRep
    · decide
    · decide
    · rw [List.mem_replicate] at hRep; omega
  have hBound5_2 : ∀ x ∈ wotsTwoUseD2, x < 5 := by
    intro x hx
    simp only [wotsTwoUseD2, List.mem_cons] at hx
    rcases hx with rfl | rfl | hRep
    · decide
    · decide
    · rw [List.mem_replicate] at hRep; omega
  have hBound5_S : ∀ x ∈ wotsTwoUseDStar, x < 5 := by
    intro x hx
    simp only [wotsTwoUseDStar, List.mem_replicate] at hx
    omega
  have hSum1 : wotsTwoUseD1.foldr (· + ·) 0 = 136 := by
    simp only [wotsTwoUseD1, List.foldr_cons, foldr_add_replicate]
  have hSum2 : wotsTwoUseD2.foldr (· + ·) 0 = 136 := by
    simp only [wotsTwoUseD2, List.foldr_cons, foldr_add_replicate]
  have hSumS : wotsTwoUseDStar.foldr (· + ·) 0 = 136 := by
    simp only [wotsTwoUseDStar, foldr_add_replicate]
  refine ⟨⟨by simp [wotsTwoUseD1], hBound5_1, hSum1⟩,
          ⟨by simp [wotsTwoUseD2], hBound5_2, hSum2⟩,
          ⟨by simp [wotsTwoUseDStar], hBound5_S, hSumS⟩,
          by decide, by decide, by decide, ?_, ?_⟩
  · intro ⟨idx, hIdx⟩
    match idx with
    | 0 => simp [wotsTwoUseD1, wotsTwoUseD2, wotsTwoUseDStar]
    | 1 => simp [wotsTwoUseD1, wotsTwoUseD2, wotsTwoUseDStar]
    | k + 2 =>
      simp only [wotsTwoUseD1, wotsTwoUseD2, wotsTwoUseDStar, List.getElem_cons_succ, List.getElem_replicate]
      decide
  · intro Node F sk sig1 sig2 forged i
    rcases i with ⟨idx, hIdx⟩
    match idx with
    | 0 =>
      change wotsChainIter F 0 2 2 (F 0 1 (wotsChainIter F 0 0 1 (sk ⟨0, hIdx⟩))) =
        wotsChainIter F 0 0 4 (sk ⟨0, hIdx⟩)
      have h1 : F 0 1 (wotsChainIter F 0 0 1 (sk ⟨0, hIdx⟩)) = wotsChainIter F 0 0 2 (sk ⟨0, hIdx⟩) := by
        simp [wotsChainIter]
      rw [h1]
      exact (wotsChainIter_add F 0 0 2 2 (sk ⟨0, hIdx⟩)).symm
    | 1 =>
      change wotsChainIter F 1 2 2 (F 1 1 (wotsChainIter F 1 0 1 (sk ⟨1, hIdx⟩))) =
        wotsChainIter F 1 0 4 (sk ⟨1, hIdx⟩)
      have h1 : F 1 1 (wotsChainIter F 1 0 1 (sk ⟨1, hIdx⟩)) = wotsChainIter F 1 0 2 (sk ⟨1, hIdx⟩) := by
        simp [wotsChainIter]
      rw [h1]
      exact (wotsChainIter_add F 1 0 2 2 (sk ⟨1, hIdx⟩)).symm
    | k + 2 =>
      have hNe0 : k + 2 ≠ 0 := by omega
      have hNe1 : k + 2 ≠ 1 := by omega
      have hStarGet : wotsTwoUseDStar[k + 2]'(by simp [wotsTwoUseDStar]; omega) = 2 := by
        simp only [wotsTwoUseDStar, List.getElem_replicate]
      have hD1Get : wotsTwoUseD1[k + 2]'(by simp [wotsTwoUseD1]; omega) = 2 := by
        simp only [wotsTwoUseD1, List.getElem_cons_succ, List.getElem_replicate]
      dsimp only [forged, wotsForwardOnlyForge, sig1]
      simp only [hNe0, hNe1, ↓reduceIte, hStarGet, hD1Get]
      exact (wotsChainIter_add F (k + 2) 0 2 2 (sk ⟨k + 2, hIdx⟩)).symm

/-- Inhabitedness witness for `wotsCs_single_use_incomparable_deployed` (`L = 68, base = 5, S = 136`)
    and `wotsCs_euf_1cma_extract_chain_preimage`. -/
theorem witness_wotsCs_1cma_inhabited :
    ∃ (d dStar : List Nat),
      validWotsCsCodeword 68 5 136 d ∧
      validWotsCsCodeword 68 5 136 dStar ∧
      dStar ≠ d :=
  ⟨wotsTwoUseD1, wotsTwoUseD2,
   tooth_wotsCs_two_signatures_enable_forward_only_forgery.1,
   tooth_wotsCs_two_signatures_enable_forward_only_forgery.2.1,
   tooth_wotsCs_two_signatures_enable_forward_only_forgery.2.2.2.1.symm⟩

/-! ### §1.2 48-Round $x^7$ SPN Deferred-MAC Session & `#tooth` Degree-6 Key Equation -/

/-- Tower-basis algebraic $x^7$ S-box; the deployed polynomial-basis circuit is defined below. -/
@[expose] def towerPow7 (x : Tower128) : Tower128 :=
  let x2 := towerMul 7 x x
  let x3 := towerMul 7 x2 x
  let x4 := towerMul 7 x2 x2
  towerMul 7 x4 x3

/-- Full 48-round $x^7$ key-alternating SPN evaluation over `Tower128`. -/
def evalScalarSpn48Evidence (roundKeys : Fin 49 → Tower128) (input : Tower128) : Tower128 :=
  let rec loop (r : Nat) (st : Tower128) : Tower128 :=
    match r with
    | 0 => st
    | k + 1 =>
      let idx := 48 - (k + 1)
      let rk := if h : idx < 49 then roundKeys ⟨idx, h⟩ else towerZero 7
      loop k (towerPow7 (towerAdd 7 st rk))
  let pre := loop 48 input
  towerAdd 7 pre (roundKeys ⟨48, by decide⟩)

private theorem towerSq_add (a b : Tower128) :
    towerMul 7 (towerAdd 7 a b) (towerAdd 7 a b) =
      towerAdd 7 (towerMul 7 a a) (towerMul 7 b b) := by
  rw [towerMul_add_distrib, towerAdd_mul_distrib, towerAdd_mul_distrib, towerMul_comm 7 b a]
  simp only [towerAdd_assoc, towerAdd_cancel]

/-- Degree-6 differential polynomial coefficients `[Δ^7, Δ^6, Δ^5, Δ^4, Δ^3, Δ^2, Δ]` over `GF(2^128)`. -/
def spnDeg6DiffCoeffs (delta : Tower128) : List Tower128 :=
  let d2 := towerMul 7 delta delta
  let d3 := towerMul 7 d2 delta
  let d4 := towerMul 7 d2 d2
  let d5 := towerMul 7 d4 delta
  let d6 := towerMul 7 d4 d2
  let d7 := towerMul 7 d4 d3
  [d7, d6, d5, d4, d3, d2, delta]

private theorem towerPow7_xor_diff_eq_evalCoeffs (x delta : Tower128) :
    towerAdd 7 (towerPow7 (towerAdd 7 x delta)) (towerPow7 x) =
      RoundPoly.evalCoeffs (spnDeg6DiffCoeffs delta) x := by
  unfold towerPow7 spnDeg6DiffCoeffs
  dsimp only
  simp only [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil]
  dsimp only [CommRingOps.add, CommRingOps.mul, CommRingOps.zero, towerCommRingOps]
  rw [towerSq_add x delta, towerSq_add (towerMul 7 x x) (towerMul 7 delta delta)]
  simp only [towerMul_zero, towerAdd_zero, towerMul_add_distrib, towerAdd_mul_distrib]
  simp only [towerMul_comm 7, towerMul_left_comm_of_assoc 7 (towerMul_assoc 7)]
  simp only [towerAdd_assoc, towerAdd_comm 7, towerAdd_left_comm, towerAdd_cancel]

/-- **`#tooth` Value-Open-Before-MAC Vulnerability (`tooth_value_open_before_mac_yields_deg6_key_eq`)**:
    If a protocol opens Round-48 SPN output `(x ⊕ Δ)^7 ⊕ k_48` before verifying intermediate
    power/Beaver MACs, XORing with an honest output `x^7 ⊕ k_48` cancels the final round key
    `k_48` identically, yielding the non-zero degree-6 polynomial
    `RoundPoly.evalCoeffs (spnDeg6DiffCoeffs Δ) x` with leading coefficient `Δ ≠ 0` and pinning
    secret `x` to **at most 6 candidate roots** in any duplicate-free domain `S ⊆ GF(2^128)`! -/
theorem tooth_value_open_before_mac_yields_deg6_key_eq
    (x delta k48 : Tower128) (hDeltaNe : delta ≠ towerZero 7)
    (S : List Tower128) (hNodup : S.Nodup) :
    let honestOut := towerAdd 7 (towerPow7 x) k48
    let faultedOut := towerAdd 7 (towerPow7 (towerAdd 7 x delta)) k48
    let diffObs := towerAdd 7 faultedOut honestOut
    diffObs = towerAdd 7 (towerPow7 (towerAdd 7 x delta)) (towerPow7 x) ∧
    diffObs = RoundPoly.evalCoeffs (spnDeg6DiffCoeffs delta) x ∧
    (spnDeg6DiffCoeffs delta).length = 7 ∧
    delta ∈ spnDeg6DiffCoeffs delta ∧
    (7 ≤ S.length →
      (S.filter (fun z =>
        decide (towerAdd 7 (RoundPoly.evalCoeffs (spnDeg6DiffCoeffs delta) z) diffObs = towerZero 7))).length ≤ 6) := by
  intro honestOut faultedOut diffObs
  have hCancel : diffObs = towerAdd 7 (towerPow7 (towerAdd 7 x delta)) (towerPow7 x) := by
    dsimp only [diffObs, faultedOut, honestOut]
    rw [towerAdd_assoc 7, ← towerAdd_assoc 7 k48 (towerPow7 x) k48,
        towerAdd_comm 7 k48 (towerPow7 x), towerAdd_assoc 7 (towerPow7 x) k48 k48,
        towerAdd_self_zero, towerAdd_zero]
  have hPoly : diffObs = RoundPoly.evalCoeffs (spnDeg6DiffCoeffs delta) x :=
    hCancel.trans (towerPow7_xor_diff_eq_evalCoeffs x delta)
  refine ⟨hCancel, hPoly, rfl, by simp [spnDeg6DiffCoeffs], ?_⟩
  intro hDom
  let d2 := towerMul 7 delta delta
  let d3 := towerMul 7 d2 delta
  let d4 := towerMul 7 d2 d2
  let d5 := towerMul 7 d4 delta
  let d6 := towerMul 7 d4 d2
  let d7 := towerMul 7 d4 d3
  let shiftedCs : List Tower128 := [towerAdd 7 d7 diffObs, d6, d5, d4, d3, d2, delta]
  have hShiftedLen : shiftedCs.length ≤ 7 := by simp [shiftedCs]
  have hEvalShift : ∀ z : Tower128,
      RoundPoly.evalCoeffs shiftedCs z =
        towerAdd 7 (RoundPoly.evalCoeffs (spnDeg6DiffCoeffs delta) z) diffObs := by
    intro z
    let rem := RoundPoly.evalCoeffs [d6, d5, d4, d3, d2, delta] z
    change towerAdd 7 (towerAdd 7 d7 diffObs) (towerMul 7 z rem) =
      towerAdd 7 (towerAdd 7 d7 (towerMul 7 z rem)) diffObs
    rw [towerAdd_assoc 7 d7 diffObs (towerMul 7 z rem),
        towerAdd_comm 7 diffObs (towerMul 7 z rem),
        ← towerAdd_assoc 7 d7 (towerMul 7 z rem) diffObs]
  have hFindOrAll : ∀ xs : List Tower128,
      (∃ z₀ : Tower128, RoundPoly.evalCoeffs shiftedCs z₀ ≠ towerZero 7) ∨
      (∀ z ∈ xs, RoundPoly.evalCoeffs shiftedCs z = towerZero 7) := by
    intro xs
    induction xs with
    | nil => exact Or.inr (fun _ hm => by cases hm)
    | cons a as ih =>
      if ha : RoundPoly.evalCoeffs shiftedCs a = towerZero 7 then
        rcases ih with hEx | hAll
        · exact Or.inl hEx
        · exact Or.inr (fun z hz => by
            rcases List.mem_cons.mp hz with rfl | hTl
            · exact ha
            · exact hAll z hTl)
      else
        exact Or.inl ⟨a, ha⟩
  have hNonzeroEval : ∃ z₀ : Tower128, RoundPoly.evalCoeffs shiftedCs z₀ ≠ towerZero 7 := by
    rcases hFindOrAll (S.take 7) with hEx | hAllZero
    · exact hEx
    · exfalso
      have hTakeLen : (S.take 7).length = 7 := List.length_take_of_le hDom
      have hTakeNd : (S.take 7).Nodup := (List.take_sublist 7 S).nodup hNodup
      have hAllCoeffs := poly_coeffs_zero_of_vanish_nodup (S.take 7) shiftedCs hTakeNd
        (by rw [hTakeLen]; exact hShiftedLen) hAllZero
      exact hDeltaNe (hAllCoeffs delta (by simp [shiftedCs]))
  have hRoots := RoundPoly.roots_nodup_length_le 6 shiftedCs S hNodup hShiftedLen hNonzeroEval
  have hFiltCongr :
      S.filter (fun z =>
        decide (towerAdd 7 (RoundPoly.evalCoeffs (spnDeg6DiffCoeffs delta) z) diffObs = towerZero 7)) =
      S.filter (fun z => decide (RoundPoly.evalCoeffs shiftedCs z = towerZero 7)) := by
    apply List.filter_congr
    intro z _
    rw [hEvalShift z]
  rw [hFiltCongr]
  exact hRoots

/-- Phases of `ParallelSeededSignSession` enforcing deferred MAC verification before `ValueOpen`. -/
inductive FtsSpnPhase where
  | powerOpen
  | intermediateMacCommit
  | intermediateMacOpen
  | valueCommit
  | valueOpen
  deriving DecidableEq, Repr

/-- Concrete 49-key SPN round-key schedule (`k_0 .. k_48`) with `DecidableEq`. -/
structure SpnKeySchedule48 where
  keys : List Tower128
  deriving DecidableEq

/-- Lookup round key `r ∈ 0..48` from `SpnKeySchedule48` (zero-padded if short). -/
def SpnKeySchedule48.keyAt (ks : SpnKeySchedule48) (i : Fin 49) : Tower128 :=
  ks.keys.getD i.val (towerZero 7)

/-- Active 48-round $x^7$ SPN signing session state binding the key schedule and 48-round evaluation. -/
structure FtsActiveSession where
  epoch : Nat
  phase : FtsSpnPhase
  alpha : Tower128
  keySchedule : SpnKeySchedule48
  spnInput : Tower128
  powerFaultDelta : Tower128
  intermMacCommitHash : List UInt8
  openedIntermDeltaGamma : Tower128
  valueCommitHash : List UInt8
  unmaskedRound48Share : Tower128
  deriving DecidableEq

/-- Persistent multi-session FTS signing guard with durable 1-use WAL burn and MAC-key quarantine. -/
structure FtsEpochGuardState where
  burnedEpochs : List Nat
  macContextPoisoned : Bool
  active : Option FtsActiveSession
  deriving DecidableEq

/-- Inputs driving `ParallelSeededSignSession` across epochs. -/
inductive FtsSpnInput where
  | beginEpoch (epoch : Nat) (alpha : Tower128) (keySchedule : SpnKeySchedule48) (spnInput : Tower128)
  | submitPowerOpen (powerFaultDelta : Tower128)
  | submitIntermMacCommit (commitDigest : List UInt8)
  | submitIntermMacOpen (deltaGamma : Tower128) (salt : List UInt8)
  | submitValueCommit (commitDigest : List UInt8)
  | submitValueOpen (salt : List UInt8)
  deriving DecidableEq

/-- PRIVATE ghost evidence. Never use this type as a network/audit event. -/
inductive FtsSpnPrivateEvidence where
  | epochStarted (epoch : Nat)
  | phaseAdvanced (epoch : Nat) (nextPhase : FtsSpnPhase)
  | releasedRound48Signature (epoch : Nat) (round48Share : Tower128)
      (keySchedule : SpnKeySchedule48) (spnInput : Tower128)
      (recordedFaultDelta recordedDeltaGamma recordedAlpha : Tower128)
  deriving DecidableEq

/-- Error codes returned by `ftsSpnEvidenceStep` (including poisoning transitions). -/
inductive FtsSpnErr where
  | macContextQuarantined
  | epochAlreadyBurned
  | sessionBusyOrWrongPhase
  | intermediateMacOrCommitFailed
  | valueCommitMismatch
  deriving DecidableEq, Repr

/-- Canonical length-framed commitment payload for a `Tower128` opening + salt (`0` string literals). -/
def encodeTower128CommitPayload (domainByte : UInt8) (val : Tower128) (salt : List UInt8) : List UInt8 :=
  encodeMultiFrame [[domainByte], be 16 (packTower 7 val).toNat, salt]

/-- Legacy evidence-model step transition of `ParallelSeededSignSession` (`PowerOpen -> IntermediateMacCommit ->
    IntermediateMacOpen -> ValueCommit -> ValueOpen` + durable 1-use burn + MAC quarantine),
    evaluating `evalScalarSpn48Evidence` directly inside the state machine rather than trusting caller outputs. -/
def ftsSpnEvidenceStep (H : Hash) (st : FtsEpochGuardState) (inp : FtsSpnInput) :
    CustodyStepOutcome FtsEpochGuardState FtsSpnPrivateEvidence FtsSpnErr :=
  if st.macContextPoisoned then
    .rejected st .macContextQuarantined
  else
    match inp, st.active with
    | .beginEpoch ep alpha ks xIn, none =>
      if ep ∈ st.burnedEpochs then
        .rejected st .epochAlreadyBurned
      else
        let honest48 := evalScalarSpn48Evidence ks.keyAt xIn
        let sess : FtsActiveSession :=
          { epoch := ep
            phase := .powerOpen
            alpha := alpha
            keySchedule := ks
            spnInput := xIn
            powerFaultDelta := towerZero 7
            intermMacCommitHash := []
            openedIntermDeltaGamma := towerZero 7
            valueCommitHash := []
            unmaskedRound48Share := honest48 }
        .accepted { st with burnedEpochs := ep :: st.burnedEpochs, active := some sess }
                  (.epochStarted ep)
    | .submitPowerOpen deltaX, some sess =>
      if sess.phase == .powerOpen then
        let evaluated48 := evalScalarSpn48Evidence sess.keySchedule.keyAt (towerAdd 7 sess.spnInput deltaX)
        let sess' :=
          { sess with
            phase := .intermediateMacCommit
            powerFaultDelta := deltaX
            unmaskedRound48Share := evaluated48 }
        .accepted { st with active := some sess' } (.phaseAdvanced sess.epoch .intermediateMacCommit)
      else
        .rejected st .sessionBusyOrWrongPhase
    | .submitIntermMacCommit cHash, some sess =>
      if sess.phase == .intermediateMacCommit then
        let sess' := { sess with phase := .intermediateMacOpen, intermMacCommitHash := cHash }
        .accepted { st with active := some sess' } (.phaseAdvanced sess.epoch .intermediateMacOpen)
      else
        .rejected st .sessionBusyOrWrongPhase
    | .submitIntermMacOpen dGamma salt, some sess =>
      if sess.phase == .intermediateMacOpen then
        let expectedCommit := H (encodeTower128CommitPayload 0x41 dGamma salt)
        let macOk := verifyLinearMacEquation sess.alpha (towerZero 7) sess.powerFaultDelta dGamma
        if expectedCommit == sess.intermMacCommitHash && macOk then
          let sess' := { sess with phase := .valueCommit, openedIntermDeltaGamma := dGamma }
          .accepted { st with active := some sess' } (.phaseAdvanced sess.epoch .valueCommit)
        else
          .rejected { st with macContextPoisoned := true, active := none } .intermediateMacOrCommitFailed
      else
        .rejected st .sessionBusyOrWrongPhase
    | .submitValueCommit vHash, some sess =>
      if sess.phase == .valueCommit then
        let sess' := { sess with phase := .valueOpen, valueCommitHash := vHash }
        .accepted { st with active := some sess' } (.phaseAdvanced sess.epoch .valueOpen)
      else
        .rejected st .sessionBusyOrWrongPhase
    | .submitValueOpen salt, some sess =>
      if sess.phase == .valueOpen then
        let expectedCommit := H (encodeTower128CommitPayload 0x42 sess.unmaskedRound48Share salt)
        if expectedCommit == sess.valueCommitHash then
          .accepted { st with active := none }
            (.releasedRound48Signature sess.epoch sess.unmaskedRound48Share
              sess.keySchedule sess.spnInput
              sess.powerFaultDelta sess.openedIntermDeltaGamma sess.alpha)
        else
          .rejected { st with macContextPoisoned := true, active := none } .valueCommitMismatch
      else
        .rejected st .sessionBusyOrWrongPhase
    | _, _ => .rejected st .sessionBusyOrWrongPhase

/-- Extract all epochs that emitted an unmasked Round-48 signature along an FTS event list. -/
def ftsReleasedEpochs : List FtsSpnPrivateEvidence → List Nat
  | [] => []
  | .releasedRound48Signature ep _ _ _ _ _ _ :: rest => ep :: ftsReleasedEpochs rest
  | _ :: rest => ftsReleasedEpochs rest

/-- Well-formedness invariant of `FtsEpochGuardState` across multi-session traces, including
    exact binding of `unmaskedRound48Share` to `evalScalarSpn48Evidence`. -/
def FtsStateInv (st : FtsEpochGuardState) : Prop :=
  match st.active with
  | none => True
  | some sess =>
    sess.epoch ∈ st.burnedEpochs ∧
    sess.unmaskedRound48Share =
      evalScalarSpn48Evidence sess.keySchedule.keyAt (towerAdd 7 sess.spnInput sess.powerFaultDelta) ∧
    (sess.phase = .valueCommit ∨ sess.phase = .valueOpen →
      verifyLinearMacEquation sess.alpha (towerZero 7)
        sess.powerFaultDelta sess.openedIntermDeltaGamma = true)

private theorem fts_step_preserves_inv_and_sound {H : Hash}
    {st st' : FtsEpochGuardState} {inp : FtsSpnInput}
    (hInv : FtsStateInv st) :
    (∀ ev, ftsSpnEvidenceStep H st inp = .accepted st' ev →
      FtsStateInv st' ∧
      (∀ ep out48 ks xIn dX dG alpha,
        ev = .releasedRound48Signature ep out48 ks xIn dX dG alpha →
          ep ∈ st.burnedEpochs ∧
          st'.active = none ∧
          st'.burnedEpochs = st.burnedEpochs ∧
          ((dX = towerZero 7 ∧ out48 = evalScalarSpn48Evidence ks.keyAt xIn) ∨
            MacKeyRecoveryWitness 7 alpha dX dG))) ∧
    (∀ err, ftsSpnEvidenceStep H st inp = .rejected st' err → FtsStateInv st') := by
  refine ⟨?_, ?_⟩
  · intro ev hAcc
    unfold ftsSpnEvidenceStep at hAcc
    if hPois : st.macContextPoisoned = true then
      simp [hPois] at hAcc
    else
      simp only [hPois, Bool.false_eq_true, ↓reduceIte] at hAcc
      cases inp with
      | beginEpoch ep alpha ks xIn =>
        cases hAct : st.active with
        | none =>
          simp only [hAct] at hAcc
          if hMem : ep ∈ st.burnedEpochs then
            simp [hMem] at hAcc
          else
            simp only [hMem, ↓reduceIte, CustodyStepOutcome.accepted.injEq] at hAcc
            rcases hAcc with ⟨rfl, rfl⟩
            refine ⟨⟨.head _, by dsimp only; rw [towerAdd_zero],
              fun hPh => by rcases hPh with h | h <;> cases h⟩, ?_⟩
            intro _ _ _ _ _ _ _ hEv; cases hEv
        | some _ => simp [hAct] at hAcc
      | submitPowerOpen deltaX =>
        cases hAct : st.active with
        | none => simp [hAct] at hAcc
        | some sess =>
          unfold FtsStateInv at hInv
          rw [hAct] at hInv
          simp only [hAct] at hAcc
          split at hAcc
          · simp only [CustodyStepOutcome.accepted.injEq] at hAcc
            rcases hAcc with ⟨rfl, rfl⟩
            refine ⟨⟨hInv.1, rfl, fun hPh => by rcases hPh with h | h <;> cases h⟩, ?_⟩
            intro _ _ _ _ _ _ _ hEv; cases hEv
          · cases hAcc
      | submitIntermMacCommit cHash =>
        cases hAct : st.active with
        | none => simp [hAct] at hAcc
        | some sess =>
          unfold FtsStateInv at hInv
          rw [hAct] at hInv
          simp only [hAct] at hAcc
          split at hAcc
          · simp only [CustodyStepOutcome.accepted.injEq] at hAcc
            rcases hAcc with ⟨rfl, rfl⟩
            refine ⟨⟨hInv.1, hInv.2.1, fun hPh => by rcases hPh with h | h <;> cases h⟩, ?_⟩
            intro _ _ _ _ _ _ _ hEv; cases hEv
          · cases hAcc
      | submitIntermMacOpen dGamma salt =>
        cases hAct : st.active with
        | none => simp [hAct] at hAcc
        | some sess =>
          unfold FtsStateInv at hInv
          rw [hAct] at hInv
          simp only [hAct] at hAcc
          if hPh : (sess.phase == .intermediateMacOpen) = true then
            simp only [hPh, ↓reduceIte] at hAcc
            split at hAcc
            · rename_i hBoth
              simp only [Bool.and_eq_true] at hBoth
              simp only [CustodyStepOutcome.accepted.injEq] at hAcc
              rcases hAcc with ⟨rfl, rfl⟩
              refine ⟨⟨hInv.1, hInv.2.1, fun _ => hBoth.2⟩, ?_⟩
              intro _ _ _ _ _ _ _ hEv; cases hEv
            · cases hAcc
          else
            simp [hPh] at hAcc
      | submitValueCommit vHash =>
        cases hAct : st.active with
        | none => simp [hAct] at hAcc
        | some sess =>
          unfold FtsStateInv at hInv
          rw [hAct] at hInv
          simp only [hAct] at hAcc
          if hPh : (sess.phase == .valueCommit) = true then
            have hPhEq : sess.phase = .valueCommit := of_decide_eq_true hPh
            simp only [hPh, ↓reduceIte, CustodyStepOutcome.accepted.injEq] at hAcc
            rcases hAcc with ⟨rfl, rfl⟩
            refine ⟨⟨hInv.1, hInv.2.1, fun _ => hInv.2.2 (Or.inl hPhEq)⟩, ?_⟩
            intro _ _ _ _ _ _ _ hEv; cases hEv
          else
            simp [hPh] at hAcc
      | submitValueOpen salt =>
        cases hAct : st.active with
        | none => simp [hAct] at hAcc
        | some sess =>
          unfold FtsStateInv at hInv
          rw [hAct] at hInv
          simp only [hAct] at hAcc
          if hPh : (sess.phase == .valueOpen) = true then
            have hPhEq : sess.phase = .valueOpen := of_decide_eq_true hPh
            simp only [hPh, ↓reduceIte] at hAcc
            split at hAcc
            · simp only [CustodyStepOutcome.accepted.injEq] at hAcc
              rcases hAcc with ⟨rfl, rfl⟩
              refine ⟨trivial, ?_⟩
              intro ep out48 ks xIn dX dG alpha hEv
              injection hEv with hEp hOut hKs hX hDX hDG hAl
              subst hEp hOut hKs hX hDX hDG hAl
              refine ⟨hInv.1, rfl, rfl, ?_⟩
              have hSpn := hInv.2.1
              have hMac := hInv.2.2 (Or.inr hPhEq)
              if hZero : sess.powerFaultDelta = towerZero 7 then
                apply Or.inl
                refine ⟨hZero, ?_⟩
                rw [hSpn, hZero, towerAdd_zero]
              else
                right
                have hRel : sess.openedIntermDeltaGamma =
                    towerMul 7 sess.alpha (towerAdd 7 sess.powerFaultDelta (towerZero 7)) :=
                  of_decide_eq_true hMac
                rw [towerAdd_zero] at hRel
                exact { deltaX_ne := hZero
                        mac_relation := hRel
                        recovered_eq := by
                          rw [hRel, towerMul_assoc, towerMul_inv 7 _ hZero, towerMul_one] }
            · cases hAcc
          else
            simp [hPh] at hAcc
  · intro err hRej
    unfold ftsSpnEvidenceStep at hRej
    if hPois : st.macContextPoisoned = true then
      simp only [hPois, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hRej
      rcases hRej with ⟨rfl, _⟩; exact hInv
    else
      simp only [hPois, Bool.false_eq_true, ↓reduceIte] at hRej
      cases inp with
      | beginEpoch ep alpha ks xIn =>
        cases hAct : st.active with
        | none =>
          simp only [hAct] at hRej
          split at hRej
          · simp only [CustodyStepOutcome.rejected.injEq] at hRej
            rcases hRej with ⟨rfl, _⟩; exact hInv
          · cases hRej
        | some _ =>
          simp only [hAct, CustodyStepOutcome.rejected.injEq] at hRej
          rcases hRej with ⟨rfl, _⟩; exact hInv
      | submitPowerOpen _ | submitIntermMacCommit _ | submitValueCommit _ =>
        cases hAct : st.active with
        | none =>
          simp only [hAct, CustodyStepOutcome.rejected.injEq] at hRej
          rcases hRej with ⟨rfl, _⟩; exact hInv
        | some _ =>
          simp only [hAct] at hRej
          split at hRej
          · cases hRej
          · simp only [CustodyStepOutcome.rejected.injEq] at hRej
            rcases hRej with ⟨rfl, _⟩; exact hInv
      | submitIntermMacOpen _ _ | submitValueOpen _ =>
        cases hAct : st.active with
        | none =>
          simp only [hAct, CustodyStepOutcome.rejected.injEq] at hRej
          rcases hRej with ⟨rfl, _⟩; exact hInv
        | some _ =>
          simp only [hAct] at hRej
          split at hRej
          · split at hRej
            · cases hRej
            · simp only [CustodyStepOutcome.rejected.injEq] at hRej
              rcases hRej with ⟨rfl, _⟩; trivial
          · simp only [CustodyStepOutcome.rejected.injEq] at hRej
            rcases hRej with ⟨rfl, _⟩; exact hInv

private theorem fts_no_release_if_burned_inactive {H : Hash}
    {st stFinal : FtsEpochGuardState}
    {trace : List (FtsSpnInput × Option FtsSpnPrivateEvidence)}
    (hTr : ValidCustodyTrace (ftsSpnEvidenceStep H) st trace stFinal) :
    ∀ ep : Nat,
      ep ∈ st.burnedEpochs →
      (∀ sess, st.active = some sess → sess.epoch ≠ ep) →
      ep ∉ ftsReleasedEpochs (traceApprovedOutputs trace) := by
  induction hTr with
  | nil =>
    intro _ _ _ hMem; cases hMem
  | @consAccepted s s' _ inp out rest hStep _ ih =>
    intro ep hBurn hInact
    unfold ftsSpnEvidenceStep at hStep
    if hPois : s.macContextPoisoned = true then
      simp [hPois] at hStep
    else
      simp only [hPois, Bool.false_eq_true, ↓reduceIte] at hStep
      cases inp with
      | beginEpoch epNew alpha ks xIn =>
        cases hAct : s.active with
        | none =>
          simp only [hAct] at hStep
          if hAlready : epNew ∈ s.burnedEpochs then
            simp [hAlready] at hStep
          else
            simp only [hAlready, ↓reduceIte, CustodyStepOutcome.accepted.injEq] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hNeEp : epNew ≠ ep := fun hEq => hAlready (hEq ▸ hBurn)
            simp only [traceApprovedOutputs_cons_some, ftsReleasedEpochs]
            exact ih ep (.tail _ hBurn) (fun sess hs => by injection hs with hsEq; rw [← hsEq]; exact hNeEp)
        | some _ => simp [hAct] at hStep
      | submitPowerOpen deltaX =>
        cases hAct : s.active with
        | none => simp [hAct] at hStep
        | some sess =>
          simp only [hAct] at hStep
          split at hStep
          · simp only [CustodyStepOutcome.accepted.injEq] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [traceApprovedOutputs_cons_some, ftsReleasedEpochs]
            exact ih ep hBurn (fun s2 hs2 => by injection hs2 with hsEq; rw [← hsEq]; exact hInact sess hAct)
          · cases hStep
      | submitIntermMacCommit cHash =>
        cases hAct : s.active with
        | none => simp [hAct] at hStep
        | some sess =>
          simp only [hAct] at hStep
          split at hStep
          · simp only [CustodyStepOutcome.accepted.injEq] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [traceApprovedOutputs_cons_some, ftsReleasedEpochs]
            exact ih ep hBurn (fun s2 hs2 => by injection hs2 with hsEq; rw [← hsEq]; exact hInact sess hAct)
          · cases hStep
      | submitIntermMacOpen dGamma salt =>
        cases hAct : s.active with
        | none => simp [hAct] at hStep
        | some sess =>
          simp only [hAct] at hStep
          split at hStep
          · split at hStep
            · simp only [CustodyStepOutcome.accepted.injEq] at hStep
              rcases hStep with ⟨rfl, rfl⟩
              simp only [traceApprovedOutputs_cons_some, ftsReleasedEpochs]
              exact ih ep hBurn (fun s2 hs2 => by injection hs2 with hsEq; rw [← hsEq]; exact hInact sess hAct)
            · cases hStep
          · cases hStep
      | submitValueCommit vHash =>
        cases hAct : s.active with
        | none => simp [hAct] at hStep
        | some sess =>
          simp only [hAct] at hStep
          split at hStep
          · simp only [CustodyStepOutcome.accepted.injEq] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [traceApprovedOutputs_cons_some, ftsReleasedEpochs]
            exact ih ep hBurn (fun s2 hs2 => by injection hs2 with hsEq; rw [← hsEq]; exact hInact sess hAct)
          · cases hStep
      | submitValueOpen salt =>
        cases hAct : s.active with
        | none => simp [hAct] at hStep
        | some sess =>
          simp only [hAct] at hStep
          split at hStep
          · split at hStep
            · simp only [CustodyStepOutcome.accepted.injEq] at hStep
              rcases hStep with ⟨rfl, rfl⟩
              simp only [traceApprovedOutputs_cons_some, ftsReleasedEpochs, List.mem_cons, not_or]
              refine ⟨fun hEq => hInact sess hAct hEq.symm, ih ep hBurn (fun _ hs2 => by cases hs2)⟩
            · cases hStep
          · cases hStep
  | @consRejected s s' _ inp err rest hStep _ ih =>
    intro ep hBurn hInact
    simp only [traceApprovedOutputs_cons_none]
    unfold ftsSpnEvidenceStep at hStep
    if hPois : s.macContextPoisoned = true then
      simp only [hPois, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
      rcases hStep with ⟨rfl, _⟩
      exact ih ep hBurn hInact
    else
      simp only [hPois, Bool.false_eq_true, ↓reduceIte] at hStep
      cases inp with
      | beginEpoch _ _ _ _ =>
        cases hAct : s.active with
        | none =>
          simp only [hAct] at hStep
          split at hStep
          · simp only [CustodyStepOutcome.rejected.injEq] at hStep
            rcases hStep with ⟨rfl, _⟩; exact ih ep hBurn (fun sess hs => by rw [hAct] at hs; cases hs)
          · cases hStep
        | some _ =>
          simp only [hAct, CustodyStepOutcome.rejected.injEq] at hStep
          rcases hStep with ⟨rfl, _⟩; exact ih ep hBurn (fun sess hs => hInact sess (hAct ▸ hs))
      | submitPowerOpen _ | submitIntermMacCommit _ | submitValueCommit _ =>
        cases hAct : s.active with
        | none =>
          simp only [hAct, CustodyStepOutcome.rejected.injEq] at hStep
          rcases hStep with ⟨rfl, _⟩; exact ih ep hBurn (fun sess hs => by rw [hAct] at hs; cases hs)
        | some _ =>
          simp only [hAct] at hStep
          split at hStep
          · cases hStep
          · simp only [CustodyStepOutcome.rejected.injEq] at hStep
            rcases hStep with ⟨rfl, _⟩; exact ih ep hBurn (fun sess hs => hInact sess (hAct ▸ hs))
      | submitIntermMacOpen _ _ | submitValueOpen _ =>
        cases hAct : s.active with
        | none =>
          simp only [hAct, CustodyStepOutcome.rejected.injEq] at hStep
          rcases hStep with ⟨rfl, _⟩; exact ih ep hBurn (fun sess hs => by rw [hAct] at hs; cases hs)
        | some _ =>
          simp only [hAct] at hStep
          split at hStep
          · split at hStep
            · cases hStep
            · simp only [CustodyStepOutcome.rejected.injEq] at hStep
              rcases hStep with ⟨rfl, _⟩; exact ih ep hBurn (fun _ hs => by cases hs)
          · simp only [CustodyStepOutcome.rejected.injEq] at hStep
            rcases hStep with ⟨rfl, _⟩; exact ih ep hBurn (fun sess hs => hInact sess (hAct ▸ hs))

/-- **Multi-Turn 48-Round $x^7$ SPN Deferred-MAC & Single-Use Theorem (`fts_spn_deferred_mac_blocks_dfa_across_epochs`)**:
    Across ANY multi-session execution trace starting from `st₀` (`FtsStateInv st₀`):
    1. **Single-Use Epoch Safety**: `(ftsReleasedEpochs (traceApprovedOutputs trace)).Nodup` —
       no epoch ever emits `> 1` signature regardless of aborts or replay attempts.
    2. **Deferred-MAC 48-Round SPN Integrity**: Every `.releasedRound48Signature ep out48 ks xIn dX dG alpha`
       recorded in the PRIVATE evidence trace satisfies EITHER
       `dX = 0 ∧ out48 = evalScalarSpn48Evidence ks.keyAt xIn` (exact honest 48-round $x^7$ SPN evaluation
       with zero intermediate power/Beaver fault) OR `MacKeyRecoveryWitness 7 alpha dX dG`
       (global `GF(2^128)` MAC key algebraically forged).
    3. **Permanent Quarantine Latch**: Once `macContextPoisoned = true` (triggered immediately on
       any failed MAC or commitment opening), `stFinal.macContextPoisoned = true` and zero events
       are ever emitted again. -/
theorem fts_spn_deferred_mac_blocks_dfa_across_epochs_evidence
    (H : Hash) {st₀ stFinal : FtsEpochGuardState}
    {trace : List (FtsSpnInput × Option FtsSpnPrivateEvidence)}
    (hInv₀ : FtsStateInv st₀)
    (hTrace : ValidCustodyTrace (ftsSpnEvidenceStep H) st₀ trace stFinal) :
    (ftsReleasedEpochs (traceApprovedOutputs trace)).Nodup ∧
    (∀ ep out48 ks xIn dX dG alpha,
      FtsSpnPrivateEvidence.releasedRound48Signature ep out48 ks xIn dX dG alpha ∈ traceApprovedOutputs trace →
        (dX = towerZero 7 ∧ out48 = evalScalarSpn48Evidence ks.keyAt xIn) ∨
        MacKeyRecoveryWitness 7 alpha dX dG) ∧
    (st₀.macContextPoisoned = true →
      stFinal.macContextPoisoned = true ∧ traceApprovedOutputs trace = []) := by
  suffices ∀ {s sf : FtsEpochGuardState} {tr : List (FtsSpnInput × Option FtsSpnPrivateEvidence)},
      ValidCustodyTrace (ftsSpnEvidenceStep H) s tr sf →
      FtsStateInv s →
      (ftsReleasedEpochs (traceApprovedOutputs tr)).Nodup ∧
      (∀ ep out48 ks xIn dX dG alpha,
        FtsSpnPrivateEvidence.releasedRound48Signature ep out48 ks xIn dX dG alpha ∈ traceApprovedOutputs tr →
          (dX = towerZero 7 ∧ out48 = evalScalarSpn48Evidence ks.keyAt xIn) ∨
          MacKeyRecoveryWitness 7 alpha dX dG) ∧
      (s.macContextPoisoned = true →
        sf.macContextPoisoned = true ∧ traceApprovedOutputs tr = []) by
    exact this hTrace hInv₀
  intro s sf tr hT
  induction hT with
  | nil =>
    intro _
    exact ⟨.nil, fun _ _ _ _ _ _ _ hm => (by cases hm), fun hP => ⟨hP, rfl⟩⟩
  | @consAccepted s s' _ inp out rest hStep hRest ih =>
    intro hInvS
    obtain ⟨hStepAcc, _⟩ := fts_step_preserves_inv_and_sound (H := H) (st := s) (st' := s') (inp := inp) hInvS
    obtain ⟨hInv', hRelProp⟩ := hStepAcc out hStep
    obtain ⟨hNdRest, hSoundRest, _⟩ := ih hInv'
    refine ⟨?_, ?_, ?_⟩
    · cases out with
      | epochStarted _ =>
        simpa [traceApprovedOutputs_cons_some, ftsReleasedEpochs] using hNdRest
      | phaseAdvanced _ _ =>
        simpa [traceApprovedOutputs_cons_some, ftsReleasedEpochs] using hNdRest
      | releasedRound48Signature ep out48 ks xIn dX dG alpha =>
        obtain ⟨hEpBurnS, hActNone, hBurnEq, _⟩ := hRelProp ep out48 ks xIn dX dG alpha rfl
        have hNotInRest : ep ∉ ftsReleasedEpochs (traceApprovedOutputs rest) :=
          fts_no_release_if_burned_inactive hRest ep
            (hBurnEq ▸ hEpBurnS) (fun _ hs => by rw [hActNone] at hs; cases hs)
        simp only [traceApprovedOutputs_cons_some, ftsReleasedEpochs]
        exact .cons (fun x hx hEq => hNotInRest (hEq ▸ hx)) hNdRest
    · intro ep out48 ks xIn dX dG alpha hMem
      simp only [traceApprovedOutputs_cons_some, List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · exact (hRelProp ep out48 ks xIn dX dG alpha hHead.symm).2.2.2
      · exact hSoundRest ep out48 ks xIn dX dG alpha hTail
    · intro hPois
      unfold ftsSpnEvidenceStep at hStep
      simp [hPois] at hStep
  | @consRejected s s' _ inp err rest hStep _ ih =>
    intro hInvS
    obtain ⟨_, hStepRej⟩ := fts_step_preserves_inv_and_sound (H := H) (st := s) (st' := s') (inp := inp) hInvS
    have hInv' := hStepRej err hStep
    obtain ⟨hNdRest, hSoundRest, hPoisRest⟩ := ih hInv'
    simp only [traceApprovedOutputs_cons_none]
    refine ⟨hNdRest, hSoundRest, fun hPois => ?_⟩
    unfold ftsSpnEvidenceStep at hStep
    simp only [hPois, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
    rcases hStep with ⟨rfl, _⟩
    exact hPoisRest hPois

/-- **`#tooth` Deferred-MAC Quarantine Witness (`tooth_fts_spn_dfa_fault_quarantined_before_value_open`)**:
    When a non-zero DFA fault `dX ≠ 0` is injected into the 48-round $x^7$ SPN session without
    knowing `alpha * dX`, `ftsSpnEvidenceStep` aborts at `.intermediateMacOpen`, permanently sets
    `macContextPoisoned = true`, clears `active = none`, and never reaches `ValueOpen`. -/
theorem tooth_fts_spn_dfa_fault_quarantined_before_value_open
    (H : Hash) (ep : Nat) (alpha dX dGamma : Tower128)
    (ks : SpnKeySchedule48) (xIn : Tower128) (salt : List UInt8)
    (hBadMac : verifyLinearMacEquation alpha (towerZero 7) dX dGamma = false) :
    let cHash := H (encodeTower128CommitPayload 0x41 dGamma salt)
    let st : FtsEpochGuardState :=
      { burnedEpochs := [ep]
        macContextPoisoned := false
        active := some
          { epoch := ep
            phase := .intermediateMacOpen
            alpha := alpha
            keySchedule := ks
            spnInput := xIn
            powerFaultDelta := dX
            intermMacCommitHash := cHash
            openedIntermDeltaGamma := towerZero 7
            valueCommitHash := []
            unmaskedRound48Share := evalScalarSpn48Evidence ks.keyAt (towerAdd 7 xIn dX) } }
    ftsSpnEvidenceStep H st (.submitIntermMacOpen dGamma salt) =
      .rejected { st with macContextPoisoned := true, active := none } .intermediateMacOrCommitFailed := by
  intro cHash st
  unfold ftsSpnEvidenceStep
  dsimp only [st]
  simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl, hBadMac, Bool.and_false]

private theorem uint8List_beq_self : ∀ xs : List UInt8, (xs == xs) = true
  | [] => rfl
  | x :: xs => by
    have hx : (x == x) = true := decide_eq_true rfl
    change ((x == x) && (xs == xs)) = true
    rw [hx, Bool.true_and]
    exact uint8List_beq_self xs

/-- Inhabitedness witness for `fts_spn_deferred_mac_blocks_dfa_across_epochs` instantiated with
    authentic 256-bit `shake256Xof 32` (`(H [0x00]).length = 32 ∧ H [0x00] ≠ [0x00]`) and a concrete
    49-key SPN schedule executing `evalScalarSpn48Evidence` end-to-end across all 6 session phases. -/
theorem witness_fts_spn_session_inhabited :
    let H : Hash := shake256Xof 32
    let ks : SpnKeySchedule48 := { keys := List.replicate 49 (towerOne 7) }
    let xIn : Tower128 := towerOne 7
    let st₀ : FtsEpochGuardState := { burnedEpochs := [], macContextPoisoned := false, active := none }
    (H [0x00]).length = 32 ∧
    H [0x00] ≠ [0x00] ∧
    ∃ trace stFinal,
      FtsStateInv st₀ ∧
      ValidCustodyTrace (ftsSpnEvidenceStep H) st₀ trace stFinal ∧
      ftsReleasedEpochs (traceApprovedOutputs trace) = [0] ∧
      FtsSpnPrivateEvidence.releasedRound48Signature 0 (evalScalarSpn48Evidence ks.keyAt xIn) ks xIn
        (towerZero 7) (towerZero 7) (towerOne 7) ∈ traceApprovedOutputs trace := by
  intro H ks xIn st₀
  have hLen32 : (H [0x00]).length = 32 := shake256Xof_length 32 [0x00]
  have hNotId : H [0x00] ≠ [0x00] := by
    intro hEq
    have hL := congrArg List.length hEq
    rw [hLen32] at hL
    cases hL
  refine ⟨hLen32, hNotId, ?_⟩
  let alpha := towerOne 7
  let out48 := evalScalarSpn48Evidence ks.keyAt xIn
  let salt : List UInt8 := [0x01, 0x02]
  let cMac := H (encodeTower128CommitPayload 0x41 (towerZero 7) salt)
  let cVal := H (encodeTower128CommitPayload 0x42 out48 salt)
  let s1 : FtsEpochGuardState :=
    { burnedEpochs := [0], macContextPoisoned := false,
      active := some { epoch := 0, phase := .powerOpen, alpha := alpha,
                       keySchedule := ks, spnInput := xIn, powerFaultDelta := towerZero 7,
                       intermMacCommitHash := [], openedIntermDeltaGamma := towerZero 7,
                       valueCommitHash := [], unmaskedRound48Share := out48 } }
  let s2 : FtsEpochGuardState :=
    { s1 with active := some { epoch := 0, phase := .intermediateMacCommit, alpha := alpha,
                               keySchedule := ks, spnInput := xIn,
                               powerFaultDelta := towerZero 7, intermMacCommitHash := [],
                               openedIntermDeltaGamma := towerZero 7, valueCommitHash := [],
                               unmaskedRound48Share := out48 } }
  let s3 : FtsEpochGuardState :=
    { s1 with active := some { epoch := 0, phase := .intermediateMacOpen, alpha := alpha,
                               keySchedule := ks, spnInput := xIn,
                               powerFaultDelta := towerZero 7, intermMacCommitHash := cMac,
                               openedIntermDeltaGamma := towerZero 7, valueCommitHash := [],
                               unmaskedRound48Share := out48 } }
  let s4 : FtsEpochGuardState :=
    { s1 with active := some { epoch := 0, phase := .valueCommit, alpha := alpha,
                               keySchedule := ks, spnInput := xIn,
                               powerFaultDelta := towerZero 7, intermMacCommitHash := cMac,
                               openedIntermDeltaGamma := towerZero 7, valueCommitHash := [],
                               unmaskedRound48Share := out48 } }
  let s5 : FtsEpochGuardState :=
    { s1 with active := some { epoch := 0, phase := .valueOpen, alpha := alpha,
                               keySchedule := ks, spnInput := xIn,
                               powerFaultDelta := towerZero 7, intermMacCommitHash := cMac,
                               openedIntermDeltaGamma := towerZero 7, valueCommitHash := cVal,
                               unmaskedRound48Share := out48 } }
  let s6 : FtsEpochGuardState := { burnedEpochs := [0], macContextPoisoned := false, active := none }
  have hs1 : ftsSpnEvidenceStep H st₀ (.beginEpoch 0 alpha ks xIn) = .accepted s1 (.epochStarted 0) := by
    unfold ftsSpnEvidenceStep
    dsimp only [st₀, s1, out48]
    simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil]
  have hs2 : ftsSpnEvidenceStep H s1 (.submitPowerOpen (towerZero 7)) =
      .accepted s2 (.phaseAdvanced 0 .intermediateMacCommit) := by
    unfold ftsSpnEvidenceStep
    dsimp only [s1, s2, out48]
    simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl, towerAdd_zero]
  have hs3 : ftsSpnEvidenceStep H s2 (.submitIntermMacCommit cMac) =
      .accepted s3 (.phaseAdvanced 0 .intermediateMacOpen) := by
    unfold ftsSpnEvidenceStep
    dsimp only [s1, s2, s3]
    simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl]
  have hs4 : ftsSpnEvidenceStep H s3 (.submitIntermMacOpen (towerZero 7) salt) =
      .accepted s4 (.phaseAdvanced 0 .valueCommit) := by
    have hBeqMac : (H (encodeTower128CommitPayload 0x41 (towerZero 7) salt) == cMac) = true :=
      uint8List_beq_self cMac
    have hMac : verifyLinearMacEquation alpha (towerZero 7) (towerZero 7) (towerZero 7) = true := by
      unfold verifyLinearMacEquation
      apply decide_eq_true_eq.mpr
      dsimp only [CommRingOps.sub, CommRingOps.mul, towerCommRingOps]
      rw [towerAdd_self_zero, towerMul_zero]
    unfold ftsSpnEvidenceStep
    dsimp only [s1, s3, s4]
    simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl, hBeqMac, hMac, Bool.and_self]
  have hs5 : ftsSpnEvidenceStep H s4 (.submitValueCommit cVal) =
      .accepted s5 (.phaseAdvanced 0 .valueOpen) := by
    unfold ftsSpnEvidenceStep
    dsimp only [s1, s4, s5]
    simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl]
  have hs6 : ftsSpnEvidenceStep H s5 (.submitValueOpen salt) =
      .accepted s6 (.releasedRound48Signature 0 out48 ks xIn (towerZero 7) (towerZero 7) alpha) := by
    have hBeqVal : (H (encodeTower128CommitPayload 0x42 out48 salt) == cVal) = true :=
      uint8List_beq_self cVal
    unfold ftsSpnEvidenceStep
    dsimp only [s1, s5, s6]
    simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl, hBeqVal]
  refine ⟨[(.beginEpoch 0 alpha ks xIn, some (.epochStarted 0)),
           (.submitPowerOpen (towerZero 7), some (.phaseAdvanced 0 .intermediateMacCommit)),
           (.submitIntermMacCommit cMac, some (.phaseAdvanced 0 .intermediateMacOpen)),
           (.submitIntermMacOpen (towerZero 7) salt, some (.phaseAdvanced 0 .valueCommit)),
           (.submitValueCommit cVal, some (.phaseAdvanced 0 .valueOpen)),
           (.submitValueOpen salt, some (.releasedRound48Signature 0 out48 ks xIn (towerZero 7) (towerZero 7) alpha))],
          s6, trivial, ?_, rfl, ?_⟩
  · exact .consAccepted hs1 (.consAccepted hs2 (.consAccepted hs3 (.consAccepted hs4 (.consAccepted hs5 (.consAccepted hs6 (.nil s6))))))
  · simp [traceApprovedOutputs_cons_some, out48, alpha]

/-! ## §2. `qsag-hd` — Lattice `AuthorizedHdProjection` over `HdFq204` (`q = 8380417`), Short-Secret MLWE & Committed MAC Zero-Test -/

/-- Prime lattice modulus $q = 8380417 = 2^{23} - 2^{13} + 1$, CBD bound $\eta = 2$, and 7-repetition
    sacrifice parameters of dealerless `qsag-hd`. -/
def hdModuleQ : Nat := 8380417
def hdCbdEta : Nat := 2
def hdRekeySacrificeReps : Nat := 7
def hdTotalSacrificeLanes : Nat := 14

private def hdNoDivTree (n lo : Nat) : Nat → Bool
  | 0 => (n % lo != 0)
  | d + 1 => hdNoDivTree n lo d && hdNoDivTree n (lo + 2 ^ d) d

private theorem hdNoDivTree_sound :
    ∀ (d n lo : Nat), hdNoDivTree n lo d = true →
      ∀ k : Nat, lo ≤ k → k < lo + 2 ^ d → ¬ (k ∣ n)
  | 0, n, lo, hok, k, hlo, hhi, hdvd => by
    have hk : k = lo := by simp at hhi; omega
    subst hk
    simp only [hdNoDivTree, bne_iff_ne] at hok
    exact hok (Nat.mod_eq_zero_of_dvd hdvd)
  | d + 1, n, lo, hok, k, hlo, hhi, hdvd => by
    simp only [hdNoDivTree, Bool.and_eq_true] at hok
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    if hmid : k < lo + 2 ^ d then
      exact hdNoDivTree_sound d n lo hok.1 k hlo hmid hdvd
    else
      exact hdNoDivTree_sound d n (lo + 2 ^ d) hok.2 k (by omega) (by omega) hdvd

private theorem hdModuleQ_no_small_div : hdNoDivTree hdModuleQ 2 12 = true := by decide

/-- Constructive divisor classification proving `hdModuleQ = 8380417` is prime ($\lfloor\sqrt{q}\rfloor = 2894 < 2 + 2^{12}$). -/
theorem hdModuleQ_dvd_cases (d : Nat) (hd : d ∣ hdModuleQ) :
    d = 1 ∨ d = hdModuleQ := by
  if hd1 : d = 1 then exact .inl hd1
  else if hdq : d = hdModuleQ then exact .inr hdq
  else
    exfalso
    obtain ⟨e, he⟩ := hd
    have hdPos : 2 ≤ d := by
      if hd0 : d = 0 then subst hd0; simp [hdModuleQ] at he
      else omega
    have hePos : 2 ≤ e := by
      if he0 : e = 0 then subst he0; simp [hdModuleQ] at he
      else if he1 : e = 1 then subst he1; simp at he; exact False.elim (hdq he.symm)
      else omega
    have hno := hdNoDivTree_sound 12 hdModuleQ 2 hdModuleQ_no_small_div
    have h2pow12 : (2 : Nat) + 2 ^ 12 = 4098 := rfl
    rw [h2pow12] at hno
    if hle : d ≤ e then
      have hdLt : d < 2896 := by
        if hge : 2896 ≤ d then
          have hsq : 2896 * 2896 ≤ d * e := Nat.mul_le_mul hge (Nat.le_trans hge hle)
          unfold hdModuleQ at he; omega
        else omega
      exact hno d hdPos (by omega) ⟨e, he⟩
    else
      have heLt : e < 2896 := by
        if hge : 2896 ≤ e then
          have hsq : 2896 * 2896 ≤ d * e := Nat.mul_le_mul (by omega) hge
          unfold hdModuleQ at he; omega
        else omega
      exact hno e hePos (by omega) ⟨d, Nat.mul_comm d e ▸ he⟩

private theorem hdModuleQ_dvd_mul {a b : Nat}
    (hdvd : hdModuleQ ∣ a * b) (hna : ¬ (hdModuleQ ∣ a)) : hdModuleQ ∣ b := by
  obtain ⟨hda, hdp⟩ := extGcd_dvd a hdModuleQ
  have hg1 : (extGcd a hdModuleQ).1 = 1 := by
    rcases hdModuleQ_dvd_cases _ hdp with h1 | hpp
    · exact h1
    · rw [hpp] at hda; exact False.elim (hna hda)
  have hbez := extGcd_bezout a hdModuleQ
  rw [hg1] at hbez
  obtain ⟨k, hk⟩ := hdvd
  have hmul : ((a : Int) * (extGcd a hdModuleQ).2.1 + (hdModuleQ : Int) * (extGcd a hdModuleQ).2.2) * (b : Int) =
      1 * (b : Int) := congrArg (· * (b : Int)) hbez
  rw [Int.add_mul, Int.one_mul] at hmul
  have hab : (a : Int) * (extGcd a hdModuleQ).2.1 * (b : Int) =
      (hdModuleQ : Int) * ((k : Int) * (extGcd a hdModuleQ).2.1) := by
    have hkInt : (a : Int) * (b : Int) = (hdModuleQ : Int) * (k : Int) := by exact_mod_cast hk
    rw [Int.mul_right_comm (a : Int), hkInt, Int.mul_assoc]
  rw [hab, Int.mul_assoc (hdModuleQ : Int), ← Int.mul_add] at hmul
  exact Int.ofNat_dvd.1 ⟨(k : Int) * (extGcd a hdModuleQ).2.1 + (extGcd a hdModuleQ).2.2 * (b : Int), hmul.symm⟩

/-- Canonical prime-field carrier $\mathbb{Z}_q$ ($q = 8380417$) for `qsag-hd` Module-LWE and MACs. -/
structure HdFq204 where
  val : Nat
  isLt : val < hdModuleQ
  deriving DecidableEq, Repr

namespace HdFq204

theorem ext {a b : HdFq204} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

def ofNat (n : Nat) : HdFq204 :=
  ⟨n % hdModuleQ, Nat.mod_lt n (by decide)⟩

def zero : HdFq204 := ⟨0, by decide⟩
def one : HdFq204 := ⟨1, by decide⟩

instance : Inhabited HdFq204 := ⟨zero⟩

@[simp] theorem zero_val : zero.val = 0 := by rfl
@[simp] theorem one_val : one.val = 1 := by rfl
@[simp] theorem ofNat_val (n : Nat) : (ofNat n).val = n % hdModuleQ := by rfl

def add (a b : HdFq204) : HdFq204 :=
  if h : a.val + b.val < hdModuleQ then
    ⟨a.val + b.val, h⟩
  else
    ⟨a.val + b.val - hdModuleQ, by have := a.isLt; have := b.isLt; omega⟩

theorem add_val (a b : HdFq204) : (add a b).val = (a.val + b.val) % hdModuleQ := by
  unfold add
  have ha := a.isLt; have hb := b.isLt
  if hlt : a.val + b.val < hdModuleQ then
    simp only [hlt, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt hlt).symm
  else
    simp only [hlt, ↓reduceDIte]
    have hEq : a.val + b.val = (a.val + b.val - hdModuleQ) + hdModuleQ * 1 := by omega
    conv => rhs; rw [hEq, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def neg (a : HdFq204) : HdFq204 :=
  if _ : a.val = 0 then ⟨0, by decide⟩ else ⟨hdModuleQ - a.val, by have := a.isLt; omega⟩

theorem neg_val (a : HdFq204) : (neg a).val = (hdModuleQ - a.val) % hdModuleQ := by
  unfold neg
  have ha := a.isLt
  if h0 : a.val = 0 then
    simp [h0]
  else
    simp only [h0, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def sub (a b : HdFq204) : HdFq204 :=
  if _ : b.val ≤ a.val then
    ⟨a.val - b.val, by have := a.isLt; omega⟩
  else
    ⟨a.val + hdModuleQ - b.val, by have := a.isLt; have := b.isLt; omega⟩

theorem sub_val (a b : HdFq204) : (sub a b).val = (a.val + hdModuleQ - b.val) % hdModuleQ := by
  unfold sub
  have ha := a.isLt; have hb := b.isLt
  if hle : b.val ≤ a.val then
    simp only [hle, ↓reduceDIte]
    have hEq : a.val + hdModuleQ - b.val = (a.val - b.val) + hdModuleQ * 1 := by omega
    conv => rhs; rw [hEq, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  else
    simp only [hle, ↓reduceDIte]
    exact (Nat.mod_eq_of_lt (by omega)).symm

def mul (a b : HdFq204) : HdFq204 :=
  ⟨(a.val * b.val) % hdModuleQ, Nat.mod_lt _ (by decide)⟩

@[simp] theorem mul_val (a b : HdFq204) : (mul a b).val = (a.val * b.val) % hdModuleQ := by rfl

theorem add_assoc (a b c : HdFq204) : add (add a b) c = add a (add b c) :=
  ext <| by rw [add_val, add_val, add_val, add_val, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem add_comm (a b : HdFq204) : add a b = add b a :=
  ext <| by rw [add_val, add_val, Nat.add_comm]

theorem zero_add (a : HdFq204) : add zero a = a :=
  ext <| by rw [add_val, zero_val, Nat.zero_add, Nat.mod_eq_of_lt a.isLt]

theorem add_zero (a : HdFq204) : add a zero = a :=
  ext <| by rw [add_val, zero_val, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]

theorem add_left_neg (a : HdFq204) : add (neg a) a = zero :=
  ext <| by
    rw [add_val, neg_val, Nat.mod_add_mod]
    have ha := a.isLt
    have hEq : hdModuleQ - a.val + a.val = hdModuleQ := by omega
    rw [hEq, Nat.mod_self, zero_val]

theorem add_right_neg (a : HdFq204) : add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem sub_eq_add_neg (a b : HdFq204) : sub a b = add a (neg b) :=
  ext <| by
    rw [sub_val, add_val, neg_val, Nat.add_mod_mod]
    have hb := b.isLt
    have hEq : a.val + (hdModuleQ - b.val) = a.val + hdModuleQ - b.val := by omega
    rw [hEq]

theorem mul_assoc (a b c : HdFq204) : mul (mul a b) c = mul a (mul b c) :=
  ext <| by rw [mul_val, mul_val, mul_val, mul_val, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

theorem mul_comm (a b : HdFq204) : mul a b = mul b a :=
  ext <| by rw [mul_val, mul_val, Nat.mul_comm]

theorem one_mul (a : HdFq204) : mul one a = a :=
  ext <| by rw [mul_val, one_val, Nat.one_mul, Nat.mod_eq_of_lt a.isLt]

theorem mul_one (a : HdFq204) : mul a one = a :=
  ext <| by rw [mul_val, one_val, Nat.mul_one, Nat.mod_eq_of_lt a.isLt]

theorem mul_zero (a : HdFq204) : mul a zero = zero :=
  ext <| by rw [mul_val, zero_val, Nat.mul_zero, Nat.zero_mod]

theorem zero_mul (a : HdFq204) : mul zero a = zero :=
  ext <| by rw [mul_val, zero_val, Nat.zero_mul, Nat.zero_mod]

theorem left_distrib (a b c : HdFq204) : mul a (add b c) = add (mul a b) (mul a c) :=
  ext <| by
    rw [mul_val, add_val, add_val, mul_val, mul_val,
        Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.left_distrib, Nat.add_mod]

theorem right_distrib (a b c : HdFq204) : mul (add a b) c = add (mul a c) (mul b c) :=
  ext <| by
    rw [mul_val, add_val, add_val, mul_val, mul_val,
        Nat.mod_mul_mod, Nat.right_distrib, Nat.add_mod]

theorem add_left_cancel {a b c : HdFq204} (h : add a b = add a c) : b = c := by
  have h1 := congrArg (add (neg a)) h
  rwa [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1

def ofInt (z : Int) : HdFq204 :=
  ⟨(z % (hdModuleQ : Int)).toNat, by
    have := Int.emod_nonneg z (show (hdModuleQ : Int) ≠ 0 by decide)
    have := Int.emod_lt_of_pos z (show (0 : Int) < hdModuleQ by decide)
    omega⟩

theorem ofInt_val (z : Int) : ((ofInt z).val : Int) = z % (hdModuleQ : Int) :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))

theorem ofInt_nat (a : HdFq204) : ofInt (a.val : Int) = a := by
  apply ext; apply Int.ofNat_inj.mp
  rw [ofInt_val]
  exact Int.emod_eq_of_lt (by omega) (by have := a.isLt; omega)

theorem mul_int (a b : HdFq204) :
    ((mul a b).val : Int) = ((a.val : Int) * (b.val : Int)) % (hdModuleQ : Int) := by
  rw [mul_val, Int.natCast_emod, Int.natCast_mul]

theorem ofInt_mul (a b : Int) : mul (ofInt a) (ofInt b) = ofInt (a * b) := by
  apply ext; apply Int.ofNat_inj.mp
  rw [mul_int, ofInt_val, ofInt_val, ofInt_val, ← Int.mul_emod]

/-- Constructive Bézout field inverse via `extGcd` (`0 ↦ 0`). -/
def inv (a : HdFq204) : HdFq204 :=
  if a.val = 0 then zero else ofInt (extGcd a.val hdModuleQ).2.1

theorem mul_inv_cancel {a : HdFq204} (ha : a ≠ zero) : mul a (inv a) = one := by
  have ha0 : a.val ≠ 0 := fun hz => ha (ext hz)
  unfold inv
  simp only [ha0, ↓reduceIte]
  obtain ⟨hda, hdq⟩ := extGcd_dvd a.val hdModuleQ
  have hg1 : (extGcd a.val hdModuleQ).1 = 1 := by
    rcases hdModuleQ_dvd_cases _ hdq with h1 | hqq
    · exact h1
    · rw [hqq] at hda
      have hle := Nat.le_of_dvd (by omega) hda
      have := a.isLt; omega
  have hbez := extGcd_bezout a.val hdModuleQ
  rw [hg1] at hbez
  generalize hx : (extGcd a.val hdModuleQ).2.1 = x at hbez ⊢
  generalize hy : (extGcd a.val hdModuleQ).2.2 = y at hbez
  rw [← ofInt_nat a, ofInt_mul]
  apply ext; apply Int.ofNat_inj.mp
  rw [ofInt_val, one_val]
  have hEq : (a.val : Int) * x = (1 : Int) + (hdModuleQ : Int) * (-y) := by
    rw [Int.mul_neg]
    omega
  rw [hEq, Int.add_mul_emod_self_left]
  decide

/-- Centered infinity-norm magnitude $|a \bmod^\pm q| \in [0, 4190208]$ over $\mathbb{Z}_{8380417}$. -/
def centeredAbs (a : HdFq204) : Nat :=
  if a.val ≤ hdModuleQ / 2 then a.val else hdModuleQ - a.val

theorem val_lt_256_pow_4 (a : HdFq204) : a.val < 256 ^ 4 := by
  have ha := a.isLt
  unfold hdModuleQ at ha
  omega

end HdFq204

instance : CommRingOps HdFq204 where
  zero := HdFq204.zero
  one := HdFq204.one
  add := HdFq204.add
  mul := HdFq204.mul
  neg := HdFq204.neg
  sub := HdFq204.sub

instance : LawfulCommRing HdFq204 where
  add_assoc := HdFq204.add_assoc
  add_comm := HdFq204.add_comm
  zero_add := HdFq204.zero_add
  add_zero := HdFq204.add_zero
  add_left_neg := HdFq204.add_left_neg
  sub_eq_add_neg := HdFq204.sub_eq_add_neg
  mul_assoc := HdFq204.mul_assoc
  mul_comm := HdFq204.mul_comm
  one_mul := HdFq204.one_mul
  mul_one := HdFq204.mul_one
  left_distrib := HdFq204.left_distrib
  right_distrib := HdFq204.right_distrib

instance : NoZeroDivisors HdFq204 where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have hval : (a.val * b.val) % hdModuleQ = 0 := congrArg HdFq204.val h
    have hdvd : hdModuleQ ∣ a.val * b.val := Nat.dvd_of_mod_eq_zero hval
    if ha0 : a.val = 0 then
      exact .inl (HdFq204.ext ha0)
    else
      have hna : ¬ (hdModuleQ ∣ a.val) := fun hda => by
        have hle := Nat.le_of_dvd (by omega) hda
        have := a.isLt; omega
      have hdb := hdModuleQ_dvd_mul hdvd hna
      if hb0 : b.val = 0 then
        exact .inr (HdFq204.ext hb0)
      else
        have hle := Nat.le_of_dvd (by omega) hdb
        have := b.isLt; omega

private theorem hdFq204_add_sub_self_left (a b : HdFq204) :
    HdFq204.sub (HdFq204.add a b) a = b := by
  change CommRingOps.sub (CommRingOps.add a b) a = b
  rw [LawfulCommRing.sub_eq_add_neg (R := HdFq204),
      LawfulCommRing.add_comm (R := HdFq204) a b,
      LawfulCommRing.add_assoc (R := HdFq204),
      LawfulCommRing.add_right_neg (R := HdFq204),
      LawfulCommRing.add_zero (R := HdFq204)]

/-- Concrete 7-repetition per-lane sacrifice verifier over `HdFq204`: a lane with additive fault
    `delta` and per-repetition sacrifice mask errors `maskErr : Fin 7 → HdFq204` passes challenge
    tuple `chals : Fin 7 → HdFq204` iff `delta * chals r + maskErr r = 0` for all `r : Fin 7`. -/
def verifyHdRekeySacrificeLane7 (delta : HdFq204) (maskErr : Fin 7 → HdFq204)
    (chals : Fin 7 → HdFq204) : Bool :=
  let rec go (k : Nat) (hk : k ≤ 7) : Bool :=
    match k with
    | 0 => true
    | m + 1 =>
      let idx : Fin 7 := ⟨m, Nat.lt_of_succ_le hk⟩
      decide (HdFq204.add (HdFq204.mul delta (chals idx)) (maskErr idx) = HdFq204.zero) &&
      go m (Nat.le_of_succ_le hk)
  go 7 (Nat.le_refl 7)

theorem verifyHdRekeySacrificeLane7_true_iff (delta : HdFq204)
    (maskErr chals : Fin 7 → HdFq204) :
    verifyHdRekeySacrificeLane7 delta maskErr chals = true ↔
      ∀ r : Fin 7, HdFq204.add (HdFq204.mul delta (chals r)) (maskErr r) = HdFq204.zero := by
  unfold verifyHdRekeySacrificeLane7
  suffices ∀ (k : Nat) (hk : k ≤ 7),
      verifyHdRekeySacrificeLane7.go delta maskErr chals k hk = true ↔
        ∀ r : Fin 7, r.val < k →
          HdFq204.add (HdFq204.mul delta (chals r)) (maskErr r) = HdFq204.zero by
    simpa using this 7 (Nat.le_refl 7)
  intro k hk
  induction k with
  | zero => simp [verifyHdRekeySacrificeLane7.go]
  | succ m ih =>
    simp only [verifyHdRekeySacrificeLane7.go, Bool.and_eq_true, decide_eq_true_eq,
               ih (Nat.le_of_succ_le hk)]
    constructor
    · rintro ⟨hM, hBelow⟩ ⟨rv, hrv⟩ hLtSucc
      dsimp only at hLtSucc
      if hEq : rv = m then
        subst hEq; exact hM
      else
        exact hBelow ⟨rv, hrv⟩ (by dsimp only; omega)
    · intro hAll
      exact ⟨hAll ⟨m, Nat.lt_of_succ_le hk⟩ (Nat.lt_succ_self m),
             fun r hr => hAll r (Nat.lt_succ_of_lt hr)⟩

private theorem nodup_filter_length_le_one {α : Type} {xs : List α} {p : α → Bool}
    (hNd : xs.Nodup) (hUniq : ∀ a b : α, p a = true → p b = true → a = b) :
    (xs.filter p).length ≤ 1 := by
  have hFiltNd : (xs.filter p).Nodup := hNd.sublist (List.filter_sublist)
  cases hEq : xs.filter p with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons b tl =>
      rw [hEq] at hFiltNd
      have haMem : a ∈ xs.filter p := hEq ▸ .head _
      have hbMem : b ∈ xs.filter p := hEq ▸ .tail _ (.head _)
      have haP : p a = true := (List.mem_filter.mp haMem).2
      have hbP : p b = true := (List.mem_filter.mp hbMem).2
      have hab : a = b := hUniq a b haP hbP
      rcases List.nodup_cons.mp hFiltNd with ⟨haNotMem, _⟩
      exact False.elim (haNotMem (hab ▸ .head _))

private theorem filter_or_length_le {α : Type} (p q : α → Bool) (s : List α) :
    (s.filter (fun x => p x || q x)).length ≤ (s.filter p).length + (s.filter q).length := by
  induction s with
  | nil => simp
  | cons x tl ih =>
    simp only [List.filter]
    cases p x <;> cases q x <;> simp <;> omega

private theorem filter_const_false_len {α : Type} :
    ∀ (xs : List α), (xs.filter (fun _ => false)).length = 0
  | [] => rfl
  | _ :: tl => filter_const_false_len tl

private theorem filter_any_length_le_sum {α β : Type} (lanes : List β)
    (pred : β → α → Bool) (xs : List α) :
    (xs.filter (fun x => lanes.any (fun l => pred l x))).length ≤
      (lanes.map (fun l => (xs.filter (pred l)).length)).sum := by
  induction lanes with
  | nil =>
    have h0 : (xs.filter (fun x => ([] : List β).any (fun l => pred l x))).length = 0 :=
      filter_const_false_len xs
    rw [h0]
    exact Nat.zero_le _
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons, List.any_cons]
    exact Nat.le_trans (filter_or_length_le (pred l) (fun x => ls.any (fun b => pred b x)) xs)
      (Nat.add_le_add_left ih _)

/-- **Algebraic Root-Counting & Schwartz-Zippel Sacrifice Bound (`hd_dealerless_rekey_sacrifice_soundness_lt_two_pow_neg157`)**:
    1. **Univariate Polynomial Root Bound over `HdFq204`**: Any non-zero degree-`≤ d` sacrifice error
       polynomial `errCoeffs : List HdFq204` (`errCoeffs.length ≤ d + 1`) vanishes on at most `d`
       challenges in ANY duplicate-free challenge set `S : List HdFq204`.
    2. **7-Repetition Per-Lane Pinning**: For any faulted lane with `delta ≠ 0`, at most **1**
       7-challenge tuple `c : Fin 7 → HdFq204` in any duplicate-free `T` passes `verifyHdRekeySacrificeLane7`.
    3. **14-Lane Union Bound `< 2^-157`**: Across any list `faultedLanes` of up to `14` faulted child +
       parent MAC lanes (`faultedLanes.length ≤ hdTotalSacrificeLanes`), the total count of accepting
       7-challenge tuples in `T` is `≤ 14`, so the cheating ratio over the `q^7 = 8380417^7` challenge
       space satisfies `2^160 < q^7` and `ratLe (acceptingCount, q^7) (1, 2^157)`. -/
theorem hd_dealerless_rekey_sacrifice_soundness_lt_two_pow_neg157 :
    (∀ (d : Nat) (errCoeffs S : List HdFq204),
      S.Nodup →
      errCoeffs.length ≤ d + 1 →
      (∃ z : HdFq204, RoundPoly.evalCoeffs errCoeffs z ≠ HdFq204.zero) →
      (S.filter (fun c => decide (RoundPoly.evalCoeffs errCoeffs c = HdFq204.zero))).length ≤ d) ∧
    (∀ (delta : HdFq204) (maskErr : Fin 7 → HdFq204) (T : List (Fin 7 → HdFq204)),
      delta ≠ HdFq204.zero →
      T.Nodup →
      (T.filter (verifyHdRekeySacrificeLane7 delta maskErr)).length ≤ 1) ∧
    (∀ (faultedLanes : List (HdFq204 × (Fin 7 → HdFq204))) (T : List (Fin 7 → HdFq204)),
      faultedLanes.length ≤ hdTotalSacrificeLanes →
      (∀ lane ∈ faultedLanes, lane.1 ≠ HdFq204.zero) →
      T.Nodup →
      let accepting := T.filter (fun c =>
        faultedLanes.any (fun lane => verifyHdRekeySacrificeLane7 lane.1 lane.2 c))
      accepting.length ≤ hdTotalSacrificeLanes ∧
      2 ^ 160 < hdModuleQ ^ hdRekeySacrificeReps ∧
      ratLe (accepting.length, hdModuleQ ^ hdRekeySacrificeReps) (1, 2 ^ 157)) := by
  have hPerLane : ∀ (delta : HdFq204) (maskErr : Fin 7 → HdFq204) (T : List (Fin 7 → HdFq204)),
      delta ≠ HdFq204.zero →
      T.Nodup →
      (T.filter (verifyHdRekeySacrificeLane7 delta maskErr)).length ≤ 1 := by
    intro delta maskErr T hNe Tnd
    apply nodup_filter_length_le_one Tnd
    intro c1 c2 hc1 hc2
    rw [verifyHdRekeySacrificeLane7_true_iff] at hc1 hc2
    funext r
    have hr1 := hc1 r
    have hr2 := hc2 r
    have hEqProd : HdFq204.mul delta (c1 r) = HdFq204.mul delta (c2 r) := by
      have hAddEq : HdFq204.add (HdFq204.mul delta (c1 r)) (maskErr r) =
          HdFq204.add (HdFq204.mul delta (c2 r)) (maskErr r) := hr1.trans hr2.symm
      have hComm1 := HdFq204.add_comm (maskErr r) (HdFq204.mul delta (c1 r))
      have hComm2 := HdFq204.add_comm (HdFq204.mul delta (c2 r)) (maskErr r)
      exact HdFq204.add_left_cancel (hComm1.trans (hAddEq.trans hComm2))
    have hSubZero : CommRingOps.mul delta (HdFq204.sub (c1 r) (c2 r)) = CommRingOps.zero := by
      change HdFq204.mul delta (HdFq204.sub (c1 r) (c2 r)) = HdFq204.zero
      rw [HdFq204.sub_eq_add_neg, HdFq204.left_distrib]
      have hMulNeg : HdFq204.mul delta (HdFq204.neg (c2 r)) =
          HdFq204.neg (HdFq204.mul delta (c2 r)) := by
        apply HdFq204.add_left_cancel (a := HdFq204.mul delta (c2 r))
        rw [← HdFq204.left_distrib, HdFq204.add_right_neg, HdFq204.mul_zero, HdFq204.add_right_neg]
      rw [hMulNeg, hEqProd, HdFq204.add_right_neg]
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hSubZero with hZ | hDiffZ
    · exact False.elim (hNe hZ)
    · exact (LawfulCommRing.sub_eq_zero_iff (R := HdFq204)).mp hDiffZ
  refine ⟨?_, hPerLane, ?_⟩
  · intro d errCoeffs S hNd hLen hNz
    exact RoundPoly.roots_nodup_length_le d errCoeffs S hNd hLen hNz
  · intro faultedLanes T hLanesLe hAllNz hTnd accepting
    have hSumBound :
        (faultedLanes.map (fun lane =>
          (T.filter (verifyHdRekeySacrificeLane7 lane.1 lane.2)).length)).sum ≤
        faultedLanes.length := by
      induction faultedLanes with
      | nil => exact Nat.zero_le 0
      | cons l ls ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have hl1 := hPerLane l.1 l.2 T (hAllNz l (.head _)) hTnd
        have hls := ih (Nat.le_of_succ_le hLanesLe) (fun x hx => hAllNz x (.tail _ hx))
        omega
    have hAccLe : accepting.length ≤ hdTotalSacrificeLanes :=
      Nat.le_trans (filter_any_length_le_sum faultedLanes
        (fun lane c => verifyHdRekeySacrificeLane7 lane.1 lane.2 c) T)
        (Nat.le_trans hSumBound hLanesLe)
    have hPow : 2 ^ 160 < hdModuleQ ^ hdRekeySacrificeReps := by
      unfold hdModuleQ hdRekeySacrificeReps; decide
    refine ⟨hAccLe, hPow, ?_⟩
    unfold ratLe hdModuleQ hdRekeySacrificeReps
    dsimp only
    unfold hdTotalSacrificeLanes at hAccLe
    refine ⟨by decide, by decide, ?_⟩
    have h14 : 14 * (2 ^ 157 : Nat) ≤ 1 * (8380417 ^ 7 : Nat) := by decide
    exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ 157) hAccLe) h14

/-- Sum of an `n`-party `HdFq204` vector. -/
def finHdFq204Sum : (n : Nat) → (Fin n → HdFq204) → HdFq204
  | 0, _ => HdFq204.zero
  | n + 1, f =>
    HdFq204.add (f ⟨0, Nat.zero_lt_succ n⟩)
      (finHdFq204Sum n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

/-- Inner product of a linear form `w : Fin dim → HdFq204` with secret vector `s : Fin dim → HdFq204`. -/
def evalLinearForm : (dim : Nat) → (Fin dim → HdFq204) → (Fin dim → HdFq204) → HdFq204
  | 0, _, _ => HdFq204.zero
  | d + 1, w, s =>
    HdFq204.add
      (HdFq204.mul (w ⟨0, Nat.zero_lt_succ d⟩) (s ⟨0, Nat.zero_lt_succ d⟩))
      (evalLinearForm d (fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
                        (fun i => s ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

/-- Coordinate basis vector `e_j : Fin dim → HdFq204` (`1` at `j`, `0` elsewhere). -/
def basisLinearForm (dim : Nat) (j : Fin dim) : Fin dim → HdFq204 :=
  fun i => if i = j then HdFq204.one else HdFq204.zero

theorem evalLinearForm_basis : ∀ (dim : Nat) (j : Fin dim) (s : Fin dim → HdFq204),
    evalLinearForm dim (basisLinearForm dim j) s = s j
  | 0, j, _ => Fin.elim0 j
  | d + 1, ⟨0, _⟩, s => by
    simp only [evalLinearForm, basisLinearForm, ↓reduceIte]
    have hZeroTail : ∀ (k : Nat) (f : Fin k → HdFq204),
        evalLinearForm k (fun _ => HdFq204.zero) f = HdFq204.zero := by
      intro k f
      induction k with
      | zero => rfl
      | succ m ih =>
        simp only [evalLinearForm, ih]
        change CommRingOps.add (CommRingOps.mul CommRingOps.zero _) CommRingOps.zero = CommRingOps.zero
        rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    have hShiftZero :
        (fun i : Fin d => if (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (d + 1)) = ⟨0, Nat.zero_lt_succ d⟩
          then HdFq204.one else HdFq204.zero) = (fun _ => HdFq204.zero) := by
      funext i
      simp
    rw [hShiftZero, hZeroTail]
    change CommRingOps.add (CommRingOps.mul CommRingOps.one (s ⟨0, _⟩)) CommRingOps.zero = s ⟨0, _⟩
    rw [LawfulCommRing.one_mul, LawfulCommRing.add_zero]
  | d + 1, ⟨k + 1, hk⟩, s => by
    simp only [evalLinearForm, basisLinearForm]
    have hNe0 : (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)) ≠ ⟨k + 1, hk⟩ :=
      fun h => Nat.noConfusion (congrArg Fin.val h)
    simp only [hNe0, ↓reduceIte]
    have hShiftBasis :
        (fun i : Fin d => if (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (d + 1)) = ⟨k + 1, hk⟩
          then HdFq204.one else HdFq204.zero) =
        basisLinearForm d ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := by
      funext i
      unfold basisLinearForm
      by_cases hik : i.val = k
      · have h2 : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hik
        simp [h2]
      · have h1 : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (d + 1)) ≠ ⟨k + 1, hk⟩ :=
          fun h => hik (Nat.succ.inj (congrArg Fin.val h))
        have h2 : i ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ :=
          fun h => hik (congrArg Fin.val h)
        simp [h1, h2]
    rw [hShiftBasis, evalLinearForm_basis d ⟨k, Nat.lt_of_succ_lt_succ hk⟩]
    change CommRingOps.add (CommRingOps.mul CommRingOps.zero _) (s ⟨k + 1, hk⟩) = s ⟨k + 1, hk⟩
    rw [LawfulCommRing.zero_mul, LawfulCommRing.zero_add]

/-- Canonical length-framed custodian share commitment binding `hardened : Bool` (`0` string literals). -/
def encodeHdShareCommit (ceremonyId : List UInt8) (partyIdx : Nat) (hardened : Bool)
    (shareBytes : List UInt8) (chainCodeSecret : List UInt8) : List UInt8 :=
  encodeMultiFrame [[0x48, 0x44, 0x53, 0x48], ceremonyId, leb128 partyIdx,
                    [if hardened then 0x01 else 0x00], shareBytes, chainCodeSecret]

/-- Strict injectivity of `encodeHdShareCommit` across all fields including `hardened : Bool`. -/
theorem encodeHdShareCommit_injective
    {c₁ c₂ : List UInt8} {p₁ p₂ : Nat} {h₁ h₂ : Bool}
    {sh₁ sh₂ cc₁ cc₂ : List UInt8}
    (hEq : encodeHdShareCommit c₁ p₁ h₁ sh₁ cc₁ = encodeHdShareCommit c₂ p₂ h₂ sh₂ cc₂) :
    c₁ = c₂ ∧ p₁ = p₂ ∧ h₁ = h₂ ∧ sh₁ = sh₂ ∧ cc₁ = cc₂ := by
  have hFrames := encodeMultiFrame_injective hEq
  simp only [List.cons.injEq] at hFrames
  rcases hFrames with ⟨_, rfl, hP, ⟨hFlag, _⟩, rfl, rfl, _⟩
  have hPid : p₁ = p₂ := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hP)).1
  have hBool : h₁ = h₂ := by cases h₁ <;> cases h₂ <;> simp at hFlag <;> rfl
  exact ⟨rfl, hPid, hBool, rfl, rfl⟩

/-- Canonical length-framed per-party MAC residual commitment preimage over `HdFq204` binding `hardened : Bool`. -/
def encodeHdResidualCommit (sessionTag : List UInt8) (partyIdx : Nat) (hardened : Bool)
    (residual : HdFq204) (salt : List UInt8) : List UInt8 :=
  encodeMultiFrame [[0x48, 0x44, 0x5A, 0x54], sessionTag, leb128 partyIdx,
                    [if hardened then 0x01 else 0x00], be 4 residual.val, salt]

/-- Strict injectivity of `encodeHdResidualCommit` on all five protocol fields including `hardened : Bool`. -/
theorem encodeHdResidualCommit_injective
    {tag₁ tag₂ : List UInt8} {p₁ p₂ : Nat} {h₁ h₂ : Bool}
    {z₁ z₂ : HdFq204} {s₁ s₂ : List UInt8}
    (hEq : encodeHdResidualCommit tag₁ p₁ h₁ z₁ s₁ = encodeHdResidualCommit tag₂ p₂ h₂ z₂ s₂) :
    tag₁ = tag₂ ∧ p₁ = p₂ ∧ h₁ = h₂ ∧ z₁ = z₂ ∧ s₁ = s₂ := by
  have hFrames := encodeMultiFrame_injective hEq
  simp only [List.cons.injEq] at hFrames
  rcases hFrames with ⟨_, rfl, hP, ⟨hFlag, _⟩, hZ, rfl, _⟩
  have hPid : p₁ = p₂ := (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hP)).1
  have hBool : h₁ = h₂ := by cases h₁ <;> cases h₂ <;> simp at hFlag <;> rfl
  have hZVal := be_injective (HdFq204.val_lt_256_pow_4 z₁) (HdFq204.val_lt_256_pow_4 z₂) hZ
  exact ⟨rfl, hPid, hBool, HdFq204.ext hZVal, rfl⟩

/-- Frozen per-party MAC commitment barrier state over `HdFq204` before any MAC residual is opened. -/
structure HdFrozenZeroTest (n : Nat) where
  sessionTag : List UInt8
  maskId : Nat
  hardened : Bool
  yTrue : HdFq204
  yCandidate : HdFq204
  alphaChild : HdFq204
  deltaGamma : HdFq204
  frozenCommits : Fin n → List UInt8

/-- Persistent `qsag-hd` family state tracking enrolled `HdFq204` custodian shares, `parentHardened`
    lineage pin, durable query budget, consumed `OpeningMask`s, and family quarantine. -/
structure HdFamilyState (n dim : Nat) where
  parentHardened : Bool
  enrolledShares : Fin n → Fin dim → HdFq204
  budgetCap : Nat
  usedQueries : Nat
  consumedMasks : List Nat
  familyQuarantined : Bool
  frozen : Option (HdFrozenZeroTest n)

/-- Inputs to the two-phase committed MAC zero-test (`freeze -> open -> quarantine on mismatch`),
    evaluating `wForm` directly against `enrolledShares` rather than trusting caller `yTrue`. -/
inductive HdZeroTestInput (n dim : Nat) where
  | freezeMacCommits (sessionTag : List UInt8) (maskId : Nat)
      (reqHardened publicChainCodeProvided : Bool)
      (wForm : Fin dim → HdFq204)
      (yCandidate alphaChild deltaGamma : HdFq204)
      (commits : Fin n → List UInt8)
  | openMacResiduals (residuals : Fin n → HdFq204) (salts : Fin n → List UInt8)

/-- Errors produced by `hdZeroTestEvidenceStep`. -/
inductive HdErr where
  | familyQuarantined
  | hardenedLineageDowngradeBlocked
  | queryBudgetExceeded
  | openingMaskReused
  | invalidSessionPhase
  | zeroTestOrCommitmentMismatch
  deriving DecidableEq, Repr

/-- Indexed verification that every custodian `i : Fin n` opened the exact `HdFq204` residual and
    `hardened` lineage flag frozen in Phase 1. -/
def verifyAllHdCommits (H : Hash) (sessionTag : List UInt8) (hardened : Bool) (n : Nat)
    (commits : Fin n → List UInt8) (residuals : Fin n → HdFq204)
    (salts : Fin n → List UInt8) : Bool :=
  let rec go (k : Nat) (hk : k ≤ n) : Bool :=
    match k with
    | 0 => true
    | m + 1 =>
      let idx : Fin n := ⟨m, Nat.lt_of_succ_le hk⟩
      (H (encodeHdResidualCommit sessionTag m hardened (residuals idx) (salts idx)) == commits idx) &&
      go m (Nat.le_of_succ_le hk)
  go n (Nat.le_refl n)

theorem verifyAllHdCommits_true_iff (H : Hash) (sessionTag : List UInt8) (hardened : Bool) (n : Nat)
    (commits : Fin n → List UInt8) (residuals : Fin n → HdFq204)
    (salts : Fin n → List UInt8) :
    verifyAllHdCommits H sessionTag hardened n commits residuals salts = true ↔
      ∀ i : Fin n, H (encodeHdResidualCommit sessionTag i.val hardened (residuals i) (salts i)) = commits i := by
  unfold verifyAllHdCommits
  suffices ∀ (k : Nat) (hk : k ≤ n),
      verifyAllHdCommits.go H sessionTag hardened n commits residuals salts k hk = true ↔
        ∀ (i : Fin n), i.val < k →
          H (encodeHdResidualCommit sessionTag i.val hardened (residuals i) (salts i)) = commits i by
    simpa using this n (Nat.le_refl n)
  intro k hk
  induction k with
  | zero =>
    simp [verifyAllHdCommits.go]
  | succ m ih =>
    simp only [verifyAllHdCommits.go, Bool.and_eq_true, beq_iff_eq, ih (Nat.le_of_succ_le hk)]
    constructor
    · rintro ⟨hM, hBelow⟩ ⟨iv, hivLt⟩ hivSucc
      dsimp only at hivSucc
      if hEq : iv = m then
        subst hEq
        exact hM
      else
        have hivM : iv < m := by omega
        exact hBelow ⟨iv, hivLt⟩ hivM
    · intro hAll
      exact ⟨hAll ⟨m, Nat.lt_of_succ_le hk⟩ (Nat.lt_succ_self m),
             fun i hi => hAll i (Nat.lt_succ_of_lt hi)⟩

/-- PRIVATE ghost evidence. Never use this type as a network/audit event. -/
inductive HdZeroTestPrivateEvidence where
  | commitsFrozen (maskId : Nat) (hardened : Bool)
  | scalarReleased (maskId : Nat) (hardened : Bool) (yOpened yTrue alphaChild deltaGamma : HdFq204)
  deriving DecidableEq, Repr

/-- Legacy evidence-model step transition of `qsag-hd` per-party committed MAC zero-testing over `HdFq204`
    (`q = 8380417`) with hardened-lineage non-downgrade enforcement, internal `evalLinearForm`
    evaluation against `enrolledShares`, single-use `OpeningMask`, bounded `DurableQueryBudget`,
    and immediate family quarantine on mismatch. -/
def hdZeroTestEvidenceStep (H : Hash) (n dim : Nat)
    (st : HdFamilyState n dim) (inp : HdZeroTestInput n dim) :
    CustodyStepOutcome (HdFamilyState n dim) HdZeroTestPrivateEvidence HdErr :=
  if st.familyQuarantined then
    .rejected st .familyQuarantined
  else
    match inp, st.frozen with
    | .freezeMacCommits tag maskId reqHard pubCcProvided wForm yCand alphaChild dGamma commits, none =>
      if (st.parentHardened && !reqHard) || (reqHard && pubCcProvided) then
        .rejected st .hardenedLineageDowngradeBlocked
      else if ¬ (st.usedQueries < st.budgetCap) then
        .rejected st .queryBudgetExceeded
      else if maskId ∈ st.consumedMasks then
        .rejected st .openingMaskReused
      else
        let yTrue := finHdFq204Sum n (fun i => evalLinearForm dim wForm (st.enrolledShares i))
        let frz : HdFrozenZeroTest n :=
          { sessionTag := tag
            maskId := maskId
            hardened := reqHard
            yTrue := yTrue
            yCandidate := yCand
            alphaChild := alphaChild
            deltaGamma := dGamma
            frozenCommits := commits }
        .accepted { st with usedQueries := st.usedQueries + 1
                            consumedMasks := maskId :: st.consumedMasks
                            frozen := some frz }
                  (.commitsFrozen maskId reqHard)
    | .openMacResiduals residuals salts, some frz =>
      let commitsOk := verifyAllHdCommits H frz.sessionTag frz.hardened n frz.frozenCommits residuals salts
      let sumZero := decide (finHdFq204Sum n residuals = HdFq204.zero)
      let macConsistent :=
        decide (finHdFq204Sum n residuals =
          HdFq204.sub frz.deltaGamma (HdFq204.mul frz.alphaChild (HdFq204.sub frz.yCandidate frz.yTrue)))
      if commitsOk && sumZero && macConsistent then
        .accepted { st with frozen := none }
          (.scalarReleased frz.maskId frz.hardened frz.yCandidate frz.yTrue frz.alphaChild frz.deltaGamma)
      else
        .rejected { st with familyQuarantined := true, frozen := none } .zeroTestOrCommitmentMismatch
    | _, _ => .rejected st .invalidSessionPhase

/-- **`#tooth` Hardened-Lineage Downgrade Rejection (`tooth_hd_hardened_parent_blocks_public_chaincode_downgrade`)**:
    Any attempt to derive an unhardened child (`reqHard = false`) from a hardened parent share
    (`parentHardened = true`), or to supply an untrusted `publicChainCodeProvided = true` on a
    hardened derivation, is rejected immediately with `.hardenedLineageDowngradeBlocked`. -/
theorem tooth_hd_hardened_parent_blocks_public_chaincode_downgrade
    (H : Hash) (n dim : Nat) (st : HdFamilyState n dim)
    (hClean : st.familyQuarantined = false) (hIdle : st.frozen = none)
    (tag : List UInt8) (maskId : Nat) (wForm : Fin dim → HdFq204)
    (yCand aChild dG : HdFq204) (commits : Fin n → List UInt8) :
    (st.parentHardened = true →
      hdZeroTestEvidenceStep H n dim st
        (.freezeMacCommits tag maskId false false wForm yCand aChild dG commits) =
      .rejected st .hardenedLineageDowngradeBlocked) ∧
    hdZeroTestEvidenceStep H n dim st
      (.freezeMacCommits tag maskId true true wForm yCand aChild dG commits) =
      .rejected st .hardenedLineageDowngradeBlocked := by
  constructor
  · intro hPar
    unfold hdZeroTestEvidenceStep
    simp [hClean, hIdle, hPar]
  · unfold hdZeroTestEvidenceStep
    simp [hClean, hIdle]

/-- Constructive anti-rushing commitment binding extractor (no choice operator): any party `c`
    opening an adapted residual `zAdapt ≠ zOrig` or flipped `hardened` flag against its frozen
    commitment yields a hash collision. -/
def extractHdRushingCollision (H : Hash) (sessionTag : List UInt8) (partyIdx : Nat)
    (hOrig hAdapt : Bool) (zOrig zAdapt : HdFq204) (saltOrig saltAdapt : List UInt8)
    (hAdaptNe : hAdapt ≠ hOrig ∨ zAdapt ≠ zOrig)
    (hMatchFrozen :
      H (encodeHdResidualCommit sessionTag partyIdx hAdapt zAdapt saltAdapt) =
      H (encodeHdResidualCommit sessionTag partyIdx hOrig zOrig saltOrig)) :
    HashCollisionWitness H :=
  { m1 := encodeHdResidualCommit sessionTag partyIdx hAdapt zAdapt saltAdapt
    m2 := encodeHdResidualCommit sessionTag partyIdx hOrig zOrig saltOrig
    ne := fun hEq => by
      have hInj := encodeHdResidualCommit_injective hEq
      rcases hAdaptNe with hB | hZ
      · exact hB hInj.2.2.1
      · exact hZ hInj.2.2.2.1
    eq := hMatchFrozen }

/-- Constructive dealerless child-MAC rotation bijection over `HdFq204` proving that disclosing or
    recovering `alphaChild = alphaParent + childPad` leaves `(alphaParent, alphaSibling)` uniform! -/
def hdChildMacRotationIndependenceEquiv (disclosedAlphaChild : HdFq204) :
    SimpleEquiv
      (HdFq204 × HdFq204)
      { state : (HdFq204 × HdFq204) × (HdFq204 × HdFq204) //
          HdFq204.add state.1.1 state.2.1 = disclosedAlphaChild ∧
          HdFq204.add state.1.1 state.2.2 = state.1.2 } where
  toFun := fun ⟨aParent, aSibling⟩ =>
    ⟨((aParent, aSibling),
      (HdFq204.sub disclosedAlphaChild aParent, HdFq204.sub aSibling aParent)),
     ⟨LawfulCommRing.add_sub_cancel_left (R := HdFq204) aParent disclosedAlphaChild,
      LawfulCommRing.add_sub_cancel_left (R := HdFq204) aParent aSibling⟩⟩
  invFun := fun ⟨⟨⟨aParent, aSibling⟩, _⟩, _⟩ => (aParent, aSibling)
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨⟨⟨aParent, aSibling⟩, ⟨cPad, sPad⟩⟩, ⟨hChild, hSib⟩⟩ => by
    dsimp only at hChild hSib
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change HdFq204.sub disclosedAlphaChild aParent = cPad
        rw [← hChild]; exact hdFq204_add_sub_self_left aParent cPad
      · change HdFq204.sub aSibling aParent = sPad
        rw [← hSib]; exact hdFq204_add_sub_self_left aParent sPad

/-- **`qsag-hd` Committed Per-Party MAC Zero-Test, Hardened Binding & Quarantine (`hd_committed_zero_test_sound`)**:
    1. **Anti-Rushing & Hardened-Flag Binding**: Adapting any residual `zAdapt ≠ zOrig` or flipping
       `hardened` on either residual or share commitments constructively yields `Collision H`.
    2. **Fault Soundness & Quarantine-Before-Release over `HdFq204`**: On any step of `hdZeroTestEvidenceStep`,
       no scalar with `yOpened ≠ yTrue` is ever released unless `dGamma * (yOpened - yTrue)⁻¹ = alphaChild`
       in $\mathbb{Z}_{8380417}$, and any failed zero-test sets `familyQuarantined = true`.
    3. **Dealerless Rotation Independence**: Any non-zero child rotation pad satisfies `alphaChild ≠ alphaParent`. -/
theorem hd_committed_zero_test_sound (H : Hash) (n dim : Nat) :
    (∀ sessionTag partyIdx hOrig hAdapt zOrig zAdapt saltOrig saltAdapt,
      (hAdapt ≠ hOrig ∨ zAdapt ≠ zOrig) →
      H (encodeHdResidualCommit sessionTag partyIdx hAdapt zAdapt saltAdapt) =
        H (encodeHdResidualCommit sessionTag partyIdx hOrig zOrig saltOrig) →
      Collision H) ∧
    (∀ cid pid h1 h2 sh1 sh2 cc1 cc2,
      h1 ≠ h2 →
      H (encodeHdShareCommit cid pid h1 sh1 cc1) = H (encodeHdShareCommit cid pid h2 sh2 cc2) →
      Collision H) ∧
    (∀ (st st' : HdFamilyState n dim) (inp : HdZeroTestInput n dim)
       (maskId : Nat) (hardened : Bool) (yOpened yTrue alphaChild dGamma : HdFq204),
      hdZeroTestEvidenceStep H n dim st inp =
        .accepted st' (.scalarReleased maskId hardened yOpened yTrue alphaChild dGamma) →
      yOpened = yTrue ∨
        HdFq204.mul dGamma (HdFq204.inv (HdFq204.sub yOpened yTrue)) = alphaChild) ∧
    (∀ (st stFinal : HdFamilyState n dim)
       (trace : List (HdZeroTestInput n dim × Option HdZeroTestPrivateEvidence)),
      st.familyQuarantined = true →
      ValidCustodyTrace (hdZeroTestEvidenceStep H n dim) st trace stFinal →
      stFinal.familyQuarantined = true ∧ traceApprovedOutputs trace = []) ∧
    (∀ (alphaParent childPad : HdFq204),
      childPad ≠ HdFq204.zero →
      HdFq204.add alphaParent childPad ≠ alphaParent) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro tag pid hO hA zOrig zAdapt sOrig sAdapt hNe hEq
    exact (extractHdRushingCollision H tag pid hO hA zOrig zAdapt sOrig sAdapt hNe hEq).toCollision
  · intro cid pid h1 h2 sh1 sh2 cc1 cc2 hNe hEq
    exact (HashCollisionWitness.mk
      (encodeHdShareCommit cid pid h1 sh1 cc1)
      (encodeHdShareCommit cid pid h2 sh2 cc2)
      (fun hPre => hNe (encodeHdShareCommit_injective hPre).2.2.1)
      hEq).toCollision
  · intro st st' inp maskId hardened yOpened yTrue alphaChild dGamma hStep
    unfold hdZeroTestEvidenceStep at hStep
    if hQ : st.familyQuarantined = true then
      simp [hQ] at hStep
    else
      simp only [hQ, Bool.false_eq_true, ↓reduceIte] at hStep
      cases inp with
      | freezeMacCommits _ _ _ _ _ _ _ _ _ =>
        cases hFrz : st.frozen <;> simp only [hFrz] at hStep
        · split at hStep
          · cases hStep
          · split at hStep
            · cases hStep
            · split at hStep <;> cases hStep
        · cases hStep
      | openMacResiduals residuals salts =>
        cases hFrz : st.frozen with
        | none => simp [hFrz] at hStep
        | some frz =>
          simp only [hFrz] at hStep
          split at hStep
          · rename_i hChecks
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hChecks
            rcases hChecks with ⟨⟨_, hSum0⟩, hMacEq⟩
            simp only [CustodyStepOutcome.accepted.injEq, HdZeroTestPrivateEvidence.scalarReleased.injEq] at hStep
            rcases hStep with ⟨_, _, _, hYO, hYT, hAC, hDG⟩
            subst hYO hYT hAC hDG
            if hEqY : frz.yCandidate = frz.yTrue then
              exact Or.inl hEqY
            else
              right
              have hSub0 : HdFq204.sub frz.deltaGamma
                  (HdFq204.mul frz.alphaChild (HdFq204.sub frz.yCandidate frz.yTrue)) =
                  HdFq204.zero := hMacEq.symm.trans hSum0
              have hDgEq : frz.deltaGamma =
                  HdFq204.mul frz.alphaChild (HdFq204.sub frz.yCandidate frz.yTrue) :=
                (LawfulCommRing.sub_eq_zero_iff (R := HdFq204)).mp hSub0
              have hDyNe : HdFq204.sub frz.yCandidate frz.yTrue ≠ HdFq204.zero :=
                fun hZ => hEqY ((LawfulCommRing.sub_eq_zero_iff (R := HdFq204)).mp hZ)
              rw [hDgEq, HdFq204.mul_assoc, HdFq204.mul_inv_cancel hDyNe, HdFq204.mul_one]
          · cases hStep
  · intro st stFinal trace hQuar hTr
    induction hTr with
    | nil => exact ⟨hQuar, rfl⟩
    | consAccepted hStep _ _ =>
      unfold hdZeroTestEvidenceStep at hStep
      simp [hQuar] at hStep
    | consRejected hStep _ ih =>
      unfold hdZeroTestEvidenceStep at hStep
      simp only [hQuar, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
      rcases hStep with ⟨rfl, _⟩
      simpa using ih hQuar
  · intro alphaParent childPad hPadNe hEq
    have hCancel := LawfulCommRing.add_left_cancel (R := HdFq204) (a := alphaParent)
      (b := childPad) (c := HdFq204.zero)
      (hEq.trans (LawfulCommRing.add_zero (R := HdFq204) alphaParent).symm)
    exact hPadNe hCancel

/-- **`#tooth` Uncommitted Zero-Test Vulnerability (`tooth_uncommitted_zero_test_rushing_forgery`)**:
    Without Phase-1 commitment freezing, after honest custodians broadcast residual sum `zHonestSum`,
    a single rushing custodian sets `zCorrupt := -zHonestSum` so `zHonestSum + zCorrupt = 0` passes
    unconditionally for ANY forged scalar `yForged ≠ yTrue` over `HdFq204` without knowing `alphaChild`! -/
theorem tooth_uncommitted_zero_test_rushing_forgery
    (zHonestSum yTrue yForged : HdFq204) (hForged : yForged ≠ yTrue) :
    let zCorrupt := HdFq204.neg zHonestSum
    yForged ≠ yTrue ∧
    HdFq204.add zHonestSum zCorrupt = HdFq204.zero :=
  ⟨hForged, LawfulCommRing.add_right_neg (R := HdFq204) zHonestSum⟩

/-- **`#tooth` Unrestricted Linear Forms Reconstruct Secret (`tooth_unrestricted_linear_forms_reconstruct_secret`)**:
    Allowing callers to evaluate `dim` unrestricted linear forms recovers every coordinate of secret
    vector `s : Fin dim → HdFq204` uniquely (`s₁ = s₂`). -/
theorem tooth_unrestricted_linear_forms_reconstruct_secret (dim : Nat)
    (s₁ s₂ : Fin dim → HdFq204)
    (hSame : ∀ j : Fin dim,
      evalLinearForm dim (basisLinearForm dim j) s₁ =
      evalLinearForm dim (basisLinearForm dim j) s₂) :
    s₁ = s₂ := by
  funext j
  have hj := hSame j
  rw [evalLinearForm_basis, evalLinearForm_basis] at hj
  exact hj

/-- Short CBD infinity-norm predicate `‖v‖_∞ ≤ eta` over `HdFq204` (`centeredAbs ≤ eta`). -/
def isShortHdVec (eta dim : Nat) (v : Fin dim → HdFq204) : Prop :=
  ∀ i : Fin dim, HdFq204.centeredAbs (v i) ≤ eta

/-- Public Module-LWE key map `t_pub(r) = ⟨A_r, s1⟩ + s2(r)` over `HdFq204` (`q = 8380417`). -/
def mlwePublicRelation (d1 d2 : Nat) (A : Fin d2 → Fin d1 → HdFq204)
    (s1 : Fin d1 → HdFq204) (s2 : Fin d2 → HdFq204) (r : Fin d2) : HdFq204 :=
  HdFq204.add (evalLinearForm d1 (A r) s1) (s2 r)

/-- Short Module-LWE witness fiber `(s1, s2)` over `HdFq204` satisfying `‖s1‖_∞ ≤ eta ∧ ‖s2‖_∞ ≤ eta`
    and matching the public key `tPub = A s1 + s2`. -/
abbrev ShortMlweWitness (eta d1 d2 : Nat)
    (A : Fin d2 → Fin d1 → HdFq204) (tPub : Fin d2 → HdFq204) : Type :=
  { sec : (Fin d1 → HdFq204) × (Fin d2 → HdFq204) //
      isShortHdVec eta d1 sec.1 ∧
      isShortHdVec eta d2 sec.2 ∧
      mlwePublicRelation d1 d2 A sec.1 sec.2 = tPub }

/-- **`#tooth` Short CBD Error Bound Rejects Arbitrary `s1` (`tooth_short_cbd_mlwe_rejects_arbitrary_s1`)**:
    Unlike an unconstrained `s2 : Fin d2 → F_q` model where every `s1` trivially satisfies
    `tPub = A s1 + s2`, enforcing `‖s2‖_∞ ≤ hdCbdEta` (`= 2`) over `HdFq204` genuinely constrains `s1`:
    for `A = [[1]]`, `tPub = [1]` (admitting short witness `s1 = [1], s2 = [0]`), candidate `s1Bad = [100]`
    forces `s2 = tPub - A s1Bad = -99` with `centeredAbs = 99 > 2`, so **no** short `s2` exists! -/
theorem tooth_short_cbd_mlwe_rejects_arbitrary_s1 :
    let A : Fin 1 → Fin 1 → HdFq204 := fun _ _ => HdFq204.one
    let s1Good : Fin 1 → HdFq204 := fun _ => HdFq204.one
    let s2Good : Fin 1 → HdFq204 := fun _ => HdFq204.zero
    let tPub : Fin 1 → HdFq204 := mlwePublicRelation 1 1 A s1Good s2Good
    let s1Bad : Fin 1 → HdFq204 := fun _ => ⟨100, by decide⟩
    (isShortHdVec hdCbdEta 1 s1Good ∧ isShortHdVec hdCbdEta 1 s2Good) ∧
    (¬ ∃ s2 : Fin 1 → HdFq204,
      isShortHdVec hdCbdEta 1 s2 ∧ mlwePublicRelation 1 1 A s1Bad s2 = tPub) := by
  intro A s1Good s2Good tPub s1Bad
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst hi; decide
  · intro i
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst hi; decide
  · rintro ⟨s2, hShort, hRel⟩
    have hr0 := congrFun hRel ⟨0, by decide⟩
    have hs2Val : s2 ⟨0, by decide⟩ = HdFq204.sub (tPub ⟨0, by decide⟩)
        (evalLinearForm 1 (A ⟨0, by decide⟩) s1Bad) := by
      dsimp only [mlwePublicRelation] at hr0
      rw [← hr0]
      exact (hdFq204_add_sub_self_left _ _).symm
    have hShort0 := hShort ⟨0, by decide⟩
    rw [hs2Val] at hShort0
    have hEvalBad : HdFq204.centeredAbs
        (HdFq204.sub (tPub ⟨0, by decide⟩) (evalLinearForm 1 (A ⟨0, by decide⟩) s1Bad)) = 99 := by
      dsimp only [tPub, mlwePublicRelation, A, s1Good, s2Good, s1Bad]
      decide
    rw [hEvalBad] at hShort0
    unfold hdCbdEta at hShort0
    omega

/-- Constructive `SimpleEquiv` over `HdFq204` (`q = 8380417`) proving that across `Q` authorized
    child projections `wForms : Fin Q → Fin d1 → HdFq204` protected by single-use `OpeningMask`s
    `m : Fin Q → HdFq204`, every bounded short secret witness `(s1, s2) : ShortMlweWitness eta d1 d2 A tPub`
    (`‖s1‖_∞ ≤ eta ∧ ‖s2‖_∞ ≤ eta`) pairs bijectively with a unique mask vector producing any observed
    transcript `openedTranscript : Fin Q → HdFq204` — leaking **zero** bits about which short `(s1, s2)`
    in the MLWE fiber is held! -/
