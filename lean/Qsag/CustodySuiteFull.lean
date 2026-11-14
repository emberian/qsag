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

public import Qsag.Constructive
public import Qsag.SimulationSpine
public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Keccak
public import Qsag.UcGames
public import Qsag.MaliciousSecurity

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
def hdAuthorizedMlweFiberEquiv (eta d1 d2 Q : Nat)
    (A : Fin d2 → Fin d1 → HdFq204) (tPub : Fin d2 → HdFq204)
    (wForms : Fin Q → Fin d1 → HdFq204)
    (openedTranscript : Fin Q → HdFq204) :
    SimpleEquiv
      (ShortMlweWitness eta d1 d2 A tPub)
      { state : ShortMlweWitness eta d1 d2 A tPub × (Fin Q → HdFq204) //
          ∀ q : Fin Q,
            HdFq204.add (evalLinearForm d1 (wForms q) state.1.val.1) (state.2 q) =
              openedTranscript q } where
  toFun := fun w =>
    let masks : Fin Q → HdFq204 :=
      fun q => HdFq204.sub (openedTranscript q) (evalLinearForm d1 (wForms q) w.val.1)
    have hOpen : ∀ q : Fin Q,
        HdFq204.add (evalLinearForm d1 (wForms q) w.val.1) (masks q) = openedTranscript q :=
      fun q => LawfulCommRing.add_sub_cancel_left (R := HdFq204)
        (evalLinearForm d1 (wForms q) w.val.1) (openedTranscript q)
    ⟨(w, masks), hOpen⟩
  invFun := fun ⟨⟨w, _⟩, _⟩ => w
  left_inv := fun _ => rfl
  right_inv := fun ⟨⟨w, masks⟩, hOpen⟩ => by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext q
      have hq := hOpen q
      dsimp only at hq ⊢
      rw [← hq]
      exact hdFq204_add_sub_self_left (evalLinearForm d1 (wForms q) w.val.1) (masks q)

/-- Constructive `SimpleEquiv` over `HdFq204` proving that under any bounded query budget `used ≤ dim`,
    the fiber of short secrets (`‖s‖_∞ ≤ eta`) consistent with `used` short opened coordinates
    is bijective to `{ free : Fin (dim - used) → HdFq204 // isShortHdVec eta (dim - used) free }`. -/
def hdBudgetSubspaceEntropyEquiv (eta dim used : Nat) (hLt : used ≤ dim)
    (opened : Fin used → HdFq204) (hOpenedShort : isShortHdVec eta used opened) :
    SimpleEquiv
      { free : Fin (dim - used) → HdFq204 // isShortHdVec eta (dim - used) free }
      { s : Fin dim → HdFq204 //
          isShortHdVec eta dim s ∧
          ∀ i : Fin used, s ⟨i.val, Nat.lt_of_lt_of_le i.isLt hLt⟩ = opened i } where
  toFun := fun ⟨freeCoords, hFreeShort⟩ =>
    ⟨fun j =>
      if hj : j.val < used then
        opened ⟨j.val, hj⟩
      else
        freeCoords ⟨j.val - used, by omega⟩,
     ⟨fun j => by
        dsimp only
        if hj : j.val < used then
          simp only [hj, ↓reduceDIte]
          exact hOpenedShort ⟨j.val, hj⟩
        else
          simp only [hj, ↓reduceDIte]
          exact hFreeShort ⟨j.val - used, by omega⟩,
      fun i => by simp [i.isLt]⟩⟩
  invFun := fun ⟨s, ⟨hShortS, _⟩⟩ =>
    ⟨fun k => s ⟨used + k.val, by omega⟩,
     fun k => hShortS ⟨used + k.val, by omega⟩⟩
  left_inv := fun ⟨freeCoords, _⟩ => by
    apply Subtype.ext
    funext k
    dsimp only
    have hNotLt : ¬ (used + k.val < used) := by omega
    have hSub : used + k.val - used = k.val := by omega
    simp [hNotLt, hSub]
  right_inv := fun ⟨s, ⟨_, hs⟩⟩ => by
    apply Subtype.ext
    funext j
    dsimp only
    if hj : j.val < used then
      simp only [hj, ↓reduceDIte]
      exact (hs ⟨j.val, hj⟩).symm
    else
      have hIdx : (⟨used + (j.val - used), by omega⟩ : Fin dim) = j := by
        apply Fin.ext
        dsimp only
        omega
      simp [hj, hIdx]

/-- Extract all single-use `OpeningMask` IDs frozen along an HD event trace. -/
def hdFrozenMaskIds : List HdZeroTestPrivateEvidence → List Nat
  | [] => []
  | .commitsFrozen mid _ :: rest => mid :: hdFrozenMaskIds rest
  | .scalarReleased _ _ _ _ _ _ :: rest => hdFrozenMaskIds rest

private theorem hd_no_freeze_if_consumed {H : Hash} {n dim : Nat}
    {st stFinal : HdFamilyState n dim}
    {trace : List (HdZeroTestInput n dim × Option HdZeroTestPrivateEvidence)}
    (hTr : ValidCustodyTrace (hdZeroTestEvidenceStep H n dim) st trace stFinal) :
    ∀ m ∈ st.consumedMasks, m ∉ hdFrozenMaskIds (traceApprovedOutputs trace) := by
  induction hTr with
  | nil => intro _ _ hm; cases hm
  | @consAccepted s s' _ inp out rest hStep _ ih =>
    intro m hm
    unfold hdZeroTestEvidenceStep at hStep
    if hQ : s.familyQuarantined = true then
      simp [hQ] at hStep
    else
      simp only [hQ, Bool.false_eq_true, ↓reduceIte] at hStep
      cases inp with
      | freezeMacCommits tag maskId reqH pubCc wForm yCand alphaChild dGamma commits =>
        cases hFrz : s.frozen with
        | none =>
          simp only [hFrz] at hStep
          if hHard : ((s.parentHardened && !reqH) || (reqH && pubCc)) = true then
            simp [hHard] at hStep
          else
            simp only [hHard, Bool.false_eq_true, ↓reduceIte] at hStep
            if hCap : ¬ (s.usedQueries < s.budgetCap) then
              simp [hCap] at hStep
            else
              simp only [hCap, ↓reduceIte] at hStep
              if hUsed : maskId ∈ s.consumedMasks then
                simp [hUsed] at hStep
              else
                simp only [hUsed, ↓reduceIte, CustodyStepOutcome.accepted.injEq] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hNe : m ≠ maskId := fun hEq => hUsed (hEq ▸ hm)
                simp only [traceApprovedOutputs_cons_some, hdFrozenMaskIds, List.mem_cons, not_or]
                exact ⟨hNe, ih m (.tail _ hm)⟩
        | some _ => simp [hFrz] at hStep
      | openMacResiduals residuals salts =>
        cases hFrz : s.frozen with
        | none => simp [hFrz] at hStep
        | some frz =>
          simp only [hFrz] at hStep
          split at hStep <;> cases hStep
          simp only [traceApprovedOutputs_cons_some, hdFrozenMaskIds]
          exact ih m hm
  | @consRejected s s' _ inp err rest hStep _ ih =>
    intro m hm
    simp only [traceApprovedOutputs_cons_none]
    unfold hdZeroTestEvidenceStep at hStep
    if hQ : s.familyQuarantined = true then
      simp only [hQ, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
      rcases hStep with ⟨rfl, _⟩; exact ih m hm
    else
      simp only [hQ, Bool.false_eq_true, ↓reduceIte] at hStep
      cases inp with
      | freezeMacCommits _ _ _ _ _ _ _ _ _ =>
        cases hFrz : s.frozen <;> simp only [hFrz] at hStep
        · split at hStep
          · simp only [CustodyStepOutcome.rejected.injEq] at hStep
            rcases hStep with ⟨rfl, _⟩; exact ih m hm
          · split at hStep
            · simp only [CustodyStepOutcome.rejected.injEq] at hStep
              rcases hStep with ⟨rfl, _⟩; exact ih m hm
            · split at hStep
              · simp only [CustodyStepOutcome.rejected.injEq] at hStep
                rcases hStep with ⟨rfl, _⟩; exact ih m hm
              · cases hStep
        · simp only [CustodyStepOutcome.rejected.injEq] at hStep
          rcases hStep with ⟨rfl, _⟩; exact ih m hm
      | openMacResiduals _ _ =>
        cases hFrz : s.frozen <;> simp only [hFrz] at hStep
        · simp only [CustodyStepOutcome.rejected.injEq] at hStep
          rcases hStep with ⟨rfl, _⟩; exact ih m hm
        · split at hStep
          · cases hStep
          · simp only [CustodyStepOutcome.rejected.injEq] at hStep
            rcases hStep with ⟨rfl, _⟩; exact ih m hm

/-- **Authorized HD Projection, Short-Secret MLWE & Bounded Budget Security
    (`hd_authorized_budget_blocks_full_rank_reconstruction`)**:
    1. Across any multi-turn `hdZeroTestEvidenceStep` trace over `HdFq204` (`q = 8380417`) from `st₀`
       (`st₀.usedQueries ≤ st₀.budgetCap`), `stFinal.usedQueries ≤ st₀.budgetCap` and all consumed
       `OpeningMask` IDs are duplicate-free (`Nodup`).
    2. For ANY two distinct short MLWE witnesses `wA ≠ wB : ShortMlweWitness hdCbdEta d1 d2 A tPub`
       (`‖s1‖_∞ ≤ 2 ∧ ‖s2‖_∞ ≤ 2`) and ANY `Q` authorized projections `wForms` and transcript `tr`,
       `hdAuthorizedMlweFiberEquiv` produces distinct masked states `(wA, masksA) ≠ (wB, masksB)`
       matching **identical** public key `tPub` and **identical** masked openings `tr`.
    3. Whenever `budgetCap < dim`, even unmasked prefix openings of a short secret (`‖opened‖_∞ ≤ hdCbdEta`)
       admit distinct **short** secrets `sA ≠ sB` (`‖sA‖_∞ ≤ hdCbdEta ∧ ‖sB‖_∞ ≤ hdCbdEta`) matching all
       `budgetCap` opened coordinates! -/
theorem hd_authorized_budget_blocks_full_rank_reconstruction_evidence
    (H : Hash) (n dim : Nat) :
    (∀ {st₀ stFinal : HdFamilyState n dim}
       {trace : List (HdZeroTestInput n dim × Option HdZeroTestPrivateEvidence)},
      st₀.usedQueries ≤ st₀.budgetCap →
      ValidCustodyTrace (hdZeroTestEvidenceStep H n dim) st₀ trace stFinal →
      stFinal.usedQueries ≤ st₀.budgetCap ∧
      (hdFrozenMaskIds (traceApprovedOutputs trace)).Nodup) ∧
    (∀ (d1 d2 Q : Nat) (A : Fin d2 → Fin d1 → HdFq204) (tPub : Fin d2 → HdFq204)
       (wForms : Fin Q → Fin d1 → HdFq204) (tr : Fin Q → HdFq204)
       (wA wB : ShortMlweWitness hdCbdEta d1 d2 A tPub),
      wA ≠ wB →
      ∃ masksA masksB : Fin Q → HdFq204,
        isShortHdVec hdCbdEta d1 wA.val.1 ∧ isShortHdVec hdCbdEta d2 wA.val.2 ∧
        isShortHdVec hdCbdEta d1 wB.val.1 ∧ isShortHdVec hdCbdEta d2 wB.val.2 ∧
        mlwePublicRelation d1 d2 A wA.val.1 wA.val.2 = tPub ∧
        mlwePublicRelation d1 d2 A wB.val.1 wB.val.2 = tPub ∧
        (∀ q : Fin Q,
          HdFq204.add (evalLinearForm d1 (wForms q) wA.val.1) (masksA q) = tr q ∧
          HdFq204.add (evalLinearForm d1 (wForms q) wB.val.1) (masksB q) = tr q)) ∧
    (∀ (dimC budgetCap : Nat) (hCapLt : budgetCap < dimC)
       (opened : Fin budgetCap → HdFq204) (_hShortOpen : isShortHdVec hdCbdEta budgetCap opened),
      ∃ sA sB : Fin dimC → HdFq204,
        sA ≠ sB ∧
        isShortHdVec hdCbdEta dimC sA ∧
        isShortHdVec hdCbdEta dimC sB ∧
        (∀ i : Fin budgetCap, sA ⟨i.val, Nat.lt_trans i.isLt hCapLt⟩ = opened i) ∧
        (∀ i : Fin budgetCap, sB ⟨i.val, Nat.lt_trans i.isLt hCapLt⟩ = opened i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro st₀ stFinal trace hCap₀ hTr
    suffices ∀ {s sf : HdFamilyState n dim}
        {tr : List (HdZeroTestInput n dim × Option HdZeroTestPrivateEvidence)},
        ValidCustodyTrace (hdZeroTestEvidenceStep H n dim) s tr sf →
        s.usedQueries ≤ s.budgetCap →
        sf.usedQueries ≤ s.budgetCap ∧
        (hdFrozenMaskIds (traceApprovedOutputs tr)).Nodup by
      exact this hTr hCap₀
    intro s sf tr hT
    induction hT with
    | nil => intro hLe; exact ⟨hLe, .nil⟩
    | @consAccepted st st' _ inp out rest hStep hRest ih =>
      intro hLe
      unfold hdZeroTestEvidenceStep at hStep
      if hQ : st.familyQuarantined = true then
        simp [hQ] at hStep
      else
        simp only [hQ, Bool.false_eq_true, ↓reduceIte] at hStep
        cases inp with
        | freezeMacCommits tag maskId reqH pubCc wForm yCand alphaChild dGamma commits =>
          cases hFrz : st.frozen with
          | none =>
            simp only [hFrz] at hStep
            if hHard : ((st.parentHardened && !reqH) || (reqH && pubCc)) = true then
              simp [hHard] at hStep
            else
              simp only [hHard, Bool.false_eq_true, ↓reduceIte] at hStep
              if hCap : ¬ (st.usedQueries < st.budgetCap) then
                simp [hCap] at hStep
              else
                simp only [hCap, ↓reduceIte] at hStep
                if hUsed : maskId ∈ st.consumedMasks then
                  simp [hUsed] at hStep
                else
                  simp only [hUsed, ↓reduceIte, CustodyStepOutcome.accepted.injEq] at hStep
                  rcases hStep with ⟨rfl, rfl⟩
                  have hUsedLt : st.usedQueries < st.budgetCap := Decidable.of_not_not hCap
                  obtain ⟨hFinLe, hNdRest⟩ := ih (Nat.succ_le_of_lt hUsedLt)
                  have hNotInRest : maskId ∉ hdFrozenMaskIds (traceApprovedOutputs rest) :=
                    hd_no_freeze_if_consumed hRest maskId (.head _)
                  simp only [traceApprovedOutputs_cons_some, hdFrozenMaskIds]
                  exact ⟨hFinLe, .cons (fun x hx hEq => hNotInRest (hEq ▸ hx)) hNdRest⟩
          | some _ => simp [hFrz] at hStep
        | openMacResiduals residuals salts =>
          cases hFrz : st.frozen with
          | none => simp [hFrz] at hStep
          | some frz =>
            simp only [hFrz] at hStep
            split at hStep <;> cases hStep
            obtain ⟨hFinLe, hNdRest⟩ := ih hLe
            simpa [traceApprovedOutputs_cons_some, hdFrozenMaskIds] using And.intro hFinLe hNdRest
    | @consRejected st st' _ inp err rest hStep _ ih =>
      intro hLe
      simp only [traceApprovedOutputs_cons_none]
      unfold hdZeroTestEvidenceStep at hStep
      if hQ : st.familyQuarantined = true then
        simp only [hQ, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
        rcases hStep with ⟨rfl, _⟩; exact ih hLe
      else
        simp only [hQ, Bool.false_eq_true, ↓reduceIte] at hStep
        cases inp with
        | freezeMacCommits _ _ _ _ _ _ _ _ _ =>
          cases hFrz : st.frozen <;> simp only [hFrz] at hStep
          · split at hStep
            · simp only [CustodyStepOutcome.rejected.injEq] at hStep
              rcases hStep with ⟨rfl, _⟩; exact ih hLe
            · split at hStep
              · simp only [CustodyStepOutcome.rejected.injEq] at hStep
                rcases hStep with ⟨rfl, _⟩; exact ih hLe
              · split at hStep
                · simp only [CustodyStepOutcome.rejected.injEq] at hStep
                  rcases hStep with ⟨rfl, _⟩; exact ih hLe
                · cases hStep
          · simp only [CustodyStepOutcome.rejected.injEq] at hStep
            rcases hStep with ⟨rfl, _⟩; exact ih hLe
        | openMacResiduals _ _ =>
          cases hFrz : st.frozen <;> simp only [hFrz] at hStep
          · simp only [CustodyStepOutcome.rejected.injEq] at hStep
            rcases hStep with ⟨rfl, _⟩; exact ih hLe
          · split at hStep
            · cases hStep
            · simp only [CustodyStepOutcome.rejected.injEq] at hStep
              rcases hStep with ⟨rfl, _⟩; exact ih hLe
  · intro d1 d2 Q A tPub wForms tr wA wB _
    let eqv := hdAuthorizedMlweFiberEquiv hdCbdEta d1 d2 Q A tPub wForms tr
    let stA := eqv.toFun wA
    let stB := eqv.toFun wB
    exact ⟨stA.val.2, stB.val.2, wA.property.1, wA.property.2.1, wB.property.1, wB.property.2.1,
           wA.property.2.2, wB.property.2.2, fun q => ⟨stA.property q, stB.property q⟩⟩
  · intro dimC budgetCap hCapLt opened hShortOpen
    let eqv := hdBudgetSubspaceEntropyEquiv hdCbdEta dimC budgetCap (Nat.le_of_lt hCapLt) opened hShortOpen
    have hZShort : isShortHdVec hdCbdEta (dimC - budgetCap) (fun _ => HdFq204.zero) :=
      fun _ => show HdFq204.zero.centeredAbs ≤ hdCbdEta by decide
    have hOShort : isShortHdVec hdCbdEta (dimC - budgetCap) (fun _ => HdFq204.one) :=
      fun _ => show HdFq204.one.centeredAbs ≤ hdCbdEta by decide
    let sA := eqv.toFun ⟨fun _ => HdFq204.zero, hZShort⟩
    let sB := eqv.toFun ⟨fun _ => HdFq204.one, hOShort⟩
    have hNe : sA.val ≠ sB.val := by
      intro hEq
      have hk := congrFun hEq ⟨budgetCap, hCapLt⟩
      dsimp only [sA, sB, eqv, hdBudgetSubspaceEntropyEquiv] at hk
      have hIrrefl : ¬ (budgetCap < budgetCap) := Nat.lt_irrefl budgetCap
      simp only [hIrrefl, ↓reduceDIte] at hk
      exact Nat.noConfusion (congrArg HdFq204.val hk)
    exact ⟨sA.val, sB.val, hNe, sA.property.1, sB.property.1, sA.property.2, sB.property.2⟩

/-- Inhabitedness witness for `hd_committed_zero_test_sound` and `hd_authorized_budget_blocks_full_rank_reconstruction`
    over `HdFq204` (`q = 8380417`) instantiated with authentic 256-bit `shake256Xof 32` (`H [0x00] ≠ [0x00]`),
    hardened lineage (`parentHardened = true`), and internal linear-form share evaluation. -/
theorem witness_hd_zero_test_inhabited :
    let H : Hash := shake256Xof 32
    let st₀ : HdFamilyState 1 1 :=
      { parentHardened := true
        enrolledShares := fun _ _ => HdFq204.one
        budgetCap := 4
        usedQueries := 0
        consumedMasks := []
        familyQuarantined := false
        frozen := none }
    (H [0x00]).length = 32 ∧
    H [0x00] ≠ [0x00] ∧
    ∃ trace stFinal,
      ValidCustodyTrace (hdZeroTestEvidenceStep H 1 1) st₀ trace stFinal ∧
      hdFrozenMaskIds (traceApprovedOutputs trace) = [7] ∧
      stFinal.usedQueries = 1 ∧
      stFinal.familyQuarantined = false := by
  intro H st₀
  have hLen32 : (H [0x00]).length = 32 := shake256Xof_length 32 [0x00]
  have hNotId : H [0x00] ≠ [0x00] := by
    intro hEq
    have hL := congrArg List.length hEq
    rw [hLen32] at hL
    cases hL
  refine ⟨hLen32, hNotId, ?_⟩
  let wForm : Fin 1 → HdFq204 := fun _ => HdFq204.one
  let c0 := H (encodeHdResidualCommit [0x01] 0 true HdFq204.zero [0xAA])
  let yTrueVal := finHdFq204Sum 1 (fun i => evalLinearForm 1 wForm (st₀.enrolledShares i))
  let frz : HdFrozenZeroTest 1 :=
    { sessionTag := [0x01], maskId := 7, hardened := true,
      yTrue := yTrueVal, yCandidate := HdFq204.one,
      alphaChild := HdFq204.one, deltaGamma := HdFq204.zero, frozenCommits := fun _ => c0 }
  let s1 : HdFamilyState 1 1 :=
    { st₀ with usedQueries := 1, consumedMasks := [7], frozen := some frz }
  let s2 : HdFamilyState 1 1 :=
    { st₀ with usedQueries := 1, consumedMasks := [7], frozen := none }
  have hs1 : hdZeroTestEvidenceStep H 1 1 st₀
      (.freezeMacCommits [0x01] 7 true false wForm HdFq204.one HdFq204.one HdFq204.zero (fun _ => c0)) =
      .accepted s1 (.commitsFrozen 7 true) := by
    have hBudget : 0 < 4 := by decide
    unfold hdZeroTestEvidenceStep
    dsimp only [st₀, s1, frz, yTrueVal]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.and_false, Bool.or_self,
      List.not_mem_nil, hBudget, not_true_eq_false, Nat.zero_add]
  have hs2 : hdZeroTestEvidenceStep H 1 1 s1
      (.openMacResiduals (fun _ => HdFq204.zero) (fun _ => [0xAA])) =
      .accepted s2 (.scalarReleased 7 true HdFq204.one yTrueVal HdFq204.one HdFq204.zero) := by
    have hVer : verifyAllHdCommits H [0x01] true 1 (fun _ => c0) (fun _ => HdFq204.zero) (fun _ => [0xAA]) = true := by
      rw [verifyAllHdCommits_true_iff]
      intro ⟨i, hi⟩
      have hi0 : i = 0 := by omega
      subst hi0
      rfl
    have hYTrueEq : yTrueVal = HdFq204.one := by
      dsimp only [yTrueVal, st₀, wForm]
      decide
    have hSum : finHdFq204Sum 1 (fun _ => HdFq204.zero) = HdFq204.zero := by decide
    have hSub : HdFq204.sub HdFq204.zero
        (HdFq204.mul HdFq204.one (HdFq204.sub HdFq204.one yTrueVal)) = HdFq204.zero := by
      rw [hYTrueEq]; decide
    unfold hdZeroTestEvidenceStep
    dsimp only [s1, s2, st₀, frz]
    simp only [Bool.false_eq_true, ↓reduceIte, hVer, hSum, hSub, decide_true, Bool.and_self]
  refine ⟨[(.freezeMacCommits [0x01] 7 true false wForm HdFq204.one HdFq204.one HdFq204.zero (fun _ => c0),
            some (.commitsFrozen 7 true)),
           (.openMacResiduals (fun _ => HdFq204.zero) (fun _ => [0xAA]),
            some (.scalarReleased 7 true HdFq204.one yTrueVal HdFq204.one HdFq204.zero))],
          s2, .consAccepted hs1 (.consAccepted hs2 (.nil s2)), by rfl, by rfl, by rfl⟩

/-! ## §3. `qsag-policy` & `qsag-addr` — Stateful Velocity Guard, V2 Intent Codec, Watermark Replay & Hybrid Pinning -/

/-- Fixed-width little-endian byte encoder (`w` low bytes of `n`, matching `to_le_bytes` in Rust). -/
def le : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: le w (n / 256)

/-- Little-endian byte list decoded as a natural number. -/
def ofLE : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * ofLE rest

@[simp] theorem length_le (w n : Nat) : (le w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [le, ih]

theorem ofLE_le {w n : Nat} (hn : n < 256 ^ w) : ofLE (le w n) = n := by
  induction w generalizing n with
  | zero => simp at hn; subst hn; rfl
  | succ w ih =>
    have hpow : 256 ^ (w + 1) = 256 ^ w * 256 := Nat.pow_succ ..
    have hn' : n / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hn)
    simp only [le, ofLE, ih hn', UInt8.toNat_ofNat']
    have h8 : (2 : Nat) ^ 8 = 256 := rfl
    rw [h8]
    omega

theorem le_injective {w n m : Nat} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : le w n = le w m) : n = m := by
  have hDec := congrArg ofLE h
  rw [ofLE_le hn, ofLE_le hm] at hDec
  exact hDec

/-- Structural body of `u64 LE` slice framing matching `cshake256_framed_32` in `qsag-core`. -/
def encodeFramedU64LeBody : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => (le 8 f.length ++ f) ++ encodeFramedU64LeBody fs

/-- Canonical `u64 LE` multi-slice framing: `(slices.len() as u64).to_le_bytes()` followed by
    `(s.len() as u64).to_le_bytes() || s` for each slice, byte-exact with `cshake256_framed_32`. -/
def encodeFramedU64Le (frames : List (List UInt8)) : List UInt8 :=
  le 8 frames.length ++ encodeFramedU64LeBody frames

/-- Stream decoder for `k` consecutive `u64 LE` length-prefixed byte slices. -/
def decodeFramedU64LeItems : Nat → List UInt8 → Option (List (List UInt8) × List UInt8)
  | 0, bs => some ([], bs)
  | k + 1, bs =>
    if bs.length < 8 then none
    else
      let flen := ofLE (bs.take 8)
      let r1 := bs.drop 8
      if r1.length < flen then none
      else
        let f := r1.take flen
        let r2 := r1.drop flen
        match decodeFramedU64LeItems k r2 with
        | none => none
        | some (fs, r3) => some (f :: fs, r3)

/-- Exact decoder for `encodeFramedU64Le`. -/
def decodeFramedU64Le (bs : List UInt8) : Option (List (List UInt8)) :=
  if bs.length < 8 then none
  else
    let count := ofLE (bs.take 8)
    match decodeFramedU64LeItems count (bs.drop 8) with
    | some (fs, []) => some fs
    | _ => none

private theorem decodeFramedU64LeItems_encode :
    ∀ (frames : List (List UInt8)) (rest : List UInt8),
      (∀ f ∈ frames, f.length < 256 ^ 8) →
      decodeFramedU64LeItems frames.length (encodeFramedU64LeBody frames ++ rest) =
        some (frames, rest)
  | [], rest, _ => rfl
  | f :: fs, rest, hB => by
    have hf : f.length < 256 ^ 8 := hB f (.head _)
    have hfs : ∀ g ∈ fs, g.length < 256 ^ 8 := fun g hg => hB g (.tail _ hg)
    simp only [List.length_cons, encodeFramedU64LeBody, List.append_assoc]
    unfold decodeFramedU64LeItems
    have hNotLt8 : ¬ ((le 8 f.length ++ (f ++ (encodeFramedU64LeBody fs ++ rest))).length < 8) := by
      simp only [List.length_append, length_le]; omega
    have hTake8 : (le 8 f.length ++ (f ++ (encodeFramedU64LeBody fs ++ rest))).take 8 = le 8 f.length := by
      simp [length_le]
    have hDrop8 : (le 8 f.length ++ (f ++ (encodeFramedU64LeBody fs ++ rest))).drop 8 =
        f ++ (encodeFramedU64LeBody fs ++ rest) := by
      simp [length_le]
    simp only [hNotLt8, ↓reduceIte, hTake8, hDrop8, ofLE_le hf]
    have hNotLtF : ¬ ((f ++ (encodeFramedU64LeBody fs ++ rest)).length < f.length) := by
      rw [List.length_append]; omega
    simp only [hNotLtF, ↓reduceIte, List.take_left, List.drop_left,
      decodeFramedU64LeItems_encode fs rest hfs]

theorem decodeFramedU64Le_encodeFramedU64Le {frames : List (List UInt8)}
    (hCnt : frames.length < 256 ^ 8)
    (hAll : ∀ f ∈ frames, f.length < 256 ^ 8) :
    decodeFramedU64Le (encodeFramedU64Le frames) = some frames := by
  unfold decodeFramedU64Le encodeFramedU64Le
  have hNotLt8 : ¬ ((le 8 frames.length ++ encodeFramedU64LeBody frames).length < 8) := by
    simp only [List.length_append, length_le]; omega
  have hTake8 : (le 8 frames.length ++ encodeFramedU64LeBody frames).take 8 = le 8 frames.length := by
    simp [length_le]
  have hDrop8 : (le 8 frames.length ++ encodeFramedU64LeBody frames).drop 8 = encodeFramedU64LeBody frames := by
    simp [length_le]
  simp only [hNotLt8, ↓reduceIte, hTake8, hDrop8, ofLE_le hCnt]
  have hItems := decodeFramedU64LeItems_encode frames [] hAll
  rw [List.append_nil] at hItems
  rw [hItems]

theorem encodeFramedU64Le_injective {xs ys : List (List UInt8)}
    (hCx : xs.length < 256 ^ 8) (hAx : ∀ f ∈ xs, f.length < 256 ^ 8)
    (hCy : ys.length < 256 ^ 8) (hAy : ∀ f ∈ ys, f.length < 256 ^ 8)
    (hEq : encodeFramedU64Le xs = encodeFramedU64Le ys) : xs = ys := by
  have hDec := congrArg decodeFramedU64Le hEq
  rw [decodeFramedU64Le_encodeFramedU64Le hCx hAx,
      decodeFramedU64Le_encodeFramedU64Le hCy hAy] at hDec
  injection hDec

/-- Module-local structural unsigned LEB128 encoder for unbounded-`Nat` mathematical fallback (no choice operator). -/
def txLeb128Aux : Nat → Nat → List UInt8
  | 0, _ => [0]
  | f + 1, n =>
    if n < 128 then
      [UInt8.ofNat n]
    else
      UInt8.ofNat (128 + n % 128) :: txLeb128Aux f (n / 128)

def txLeb128 (n : Nat) : List UInt8 :=
  txLeb128Aux n n

def txEncodeField (bs : List UInt8) : List UInt8 :=
  txLeb128 bs.length ++ bs

/-- Constructive structural unsigned LEB128 stream decoder (no choice operator). -/
def decodeLeb128 : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then
      some (b.toNat, bs)
    else
      match decodeLeb128 bs with
      | none => none
      | some (hi, rest) => some (b.toNat % 128 + 128 * hi, rest)

private theorem decodeLeb128_txLeb128Aux :
    ∀ (f n : Nat) (rest : List UInt8),
      n ≤ f → decodeLeb128 (txLeb128Aux f n ++ rest) = some (n, rest)
  | 0, n, rest, hn => by
    have hz : n = 0 := by omega
    subst hz
    simp [txLeb128Aux, decodeLeb128]
  | f + 1, n, rest, hn => by
    simp only [txLeb128Aux]
    if hlt : n < 128 then
      have hToNat : (UInt8.ofNat n).toNat = n := by
        rw [UInt8.toNat_ofNat']
        have h8 : (2 : Nat) ^ 8 = 256 := rfl
        rw [h8]; omega
      simp [hlt, decodeLeb128, hToNat]
    else
      have hToNat : (UInt8.ofNat (128 + n % 128)).toNat = 128 + n % 128 := by
        rw [UInt8.toNat_ofNat']
        have h8 : (2 : Nat) ^ 8 = 256 := rfl
        rw [h8]; omega
      have hNotLt2 : ¬ (128 + n % 128 < 128) := by omega
      have ih := decodeLeb128_txLeb128Aux f (n / 128) rest (by omega)
      simp only [hlt, ↓reduceIte, List.cons_append]
      unfold decodeLeb128
      simp only [hToNat, hNotLt2, ↓reduceIte, ih]
      congr 1; congr 1; omega

theorem decodeLeb128_txLeb128 (n : Nat) (rest : List UInt8) :
    decodeLeb128 (txLeb128 n ++ rest) = some (n, rest) :=
  decodeLeb128_txLeb128Aux n n rest (Nat.le_refl n)

def decodeLeb128Exact (bs : List UInt8) : Option Nat :=
  match decodeLeb128 bs with
  | some (n, []) => some n
  | _ => none

theorem decodeLeb128Exact_txLeb128 (n : Nat) :
    decodeLeb128Exact (txLeb128 n) = some n := by
  unfold decodeLeb128Exact
  have h := decodeLeb128_txLeb128 n []
  rw [List.append_nil] at h
  rw [h]

/-- Length-prefixed byte field stream decoder paired with `txEncodeField`. -/
def decodeListField (xs : List UInt8) : Option (List UInt8 × List UInt8) :=
  match decodeLeb128 xs with
  | none => none
  | some (len, rest) =>
    if rest.length < len then none
    else some (rest.take len, rest.drop len)

theorem decodeListField_txEncodeField (field rest : List UInt8) :
    decodeListField (txEncodeField field ++ rest) = some (field, rest) := by
  unfold decodeListField txEncodeField
  rw [List.append_assoc, decodeLeb128_txLeb128]
  dsimp only
  have hNotLt : ¬ ((field ++ rest).length < field.length) := by
    rw [List.length_append]; omega
  simp only [hNotLt, ↓reduceIte]
  rw [List.take_left, List.drop_left]

def txEncodeListFields : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => txEncodeField f ++ txEncodeListFields fs

def txDecodeListFields : Nat → List UInt8 → Option (List (List UInt8) × List UInt8)
  | 0, bs => some ([], bs)
  | k + 1, bs =>
    match decodeListField bs with
    | none => none
    | some (f, rest) =>
      match txDecodeListFields k rest with
      | none => none
      | some (fs, rest2) => some (f :: fs, rest2)

private theorem txDecodeListFields_txEncodeListFields :
    ∀ (fs : List (List UInt8)),
      txDecodeListFields fs.length (txEncodeListFields fs) = some (fs, [])
  | [] => rfl
  | f :: fs => by
    simp only [List.length_cons, txEncodeListFields]
    unfold txDecodeListFields
    rw [decodeListField_txEncodeField]
    dsimp only
    rw [txDecodeListFields_txEncodeListFields fs]

/-- Canonical transaction intent bound by `qsag-policy` (`QSAG.POLICY.INTENT.V2`, `0` string literals),
    preserving all 24 production fields of `crates/qsag-policy` alongside `policy_digest`. -/
structure TransactionIntent where
  recipient : List UInt8
  amount_units : Nat
  window_id : Nat
  policy_digest : List UInt8
  authority_digest : List UInt8
  nonce : Nat
  chain_id : Nat := 1
  suite_tag : Nat := 0x0501
  recipient_hrp : List UInt8 := []
  recipient_version : Nat := 1
  recipient_suite_tag : Nat := 0x0501
  recipient_kind : Nat := 0
  rolling_window_spent : Nat := 0
  timestamp_secs : Nat := 0
  initiator_party : Nat := 0
  init_mac_bytes : List UInt8 := []
  approver_bytes : List UInt8 := []
  payload_digest : List UInt8 := []
  rolling_window_accumulator : List UInt8 := []
  signing_key_id : List UInt8 := []
  policy_revision : Nat := 0
  message_digest : List UInt8 := []
  signing_context_digest : List UInt8 := []
  session_id : List UInt8 := []
  quorum_bytes : List UInt8 := []
  deriving DecidableEq, Repr

/-- Exact ASCII domain tag `QSAG.POLICY.INTENT.V2` (`21` bytes, matching `qsag-policy`). -/
def txIntentDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x50, 0x4F, 0x4C, 0x49, 0x43, 0x59, 0x2E,
   0x49, 0x4E, 0x54, 0x45, 0x4E, 0x54, 0x2E, 0x56, 0x32]

/-- Exact ASCII domain tag `QSAG.POLICY.SIGNED_INTENT.V2` (`28` bytes, matching `qsag-policy`). -/
def txSignedIntentDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x50, 0x4F, 0x4C, 0x49, 0x43, 0x59, 0x2E,
   0x53, 0x49, 0x47, 0x4E, 0x45, 0x44, 0x5F, 0x49, 0x4E, 0x54, 0x45, 0x4E, 0x54, 0x2E, 0x56, 0x32]

/-- Exact 24 byte-slice frames passed to `cshake256_framed_32(b"QSAG.POLICY.INTENT.V2", &[...])`
    by `TransactionIntent::canonical_digest` in `crates/qsag-policy/src/lib.rs:363-395`. -/
def txIntentProdFrames (tx : TransactionIntent) : List (List UInt8) :=
  [be 8 tx.chain_id,
   be 2 tx.suite_tag,
   tx.recipient_hrp,
   be 1 tx.recipient_version,
   be 2 tx.recipient_suite_tag,
   be 1 tx.recipient_kind,
   tx.recipient,
   be 16 tx.amount_units,
   be 16 tx.rolling_window_spent,
   be 8 tx.window_id,
   be 32 tx.nonce,
   be 8 tx.timestamp_secs,
   be 2 tx.initiator_party,
   tx.init_mac_bytes,
   tx.approver_bytes,
   tx.payload_digest,
   tx.authority_digest,
   tx.rolling_window_accumulator,
   tx.signing_key_id,
   be 8 tx.policy_revision,
   tx.message_digest,
   tx.signing_context_digest,
   tx.session_id,
   tx.quorum_bytes]

/-- Production `TransactionIntent::canonical_digest` (`cshake256Bytes` under `"QSAG.POLICY.INTENT.V2"`
    over `encodeFramedU64Le (txIntentProdFrames tx)`). -/
def canonicalIntentDigest (tx : TransactionIntent) : List UInt8 :=
  cshake256Bytes txIntentDomainTag (encodeFramedU64Le (txIntentProdFrames tx))

/-- Production `TransactionIntent::to_canonical_signing_bytes`:
    `"QSAG.POLICY.SIGNED_INTENT.V2" || policy_digest || canonical_digest(tx with message_digest := [0; 32])`. -/
def toCanonicalSigningBytes (tx : TransactionIntent) : List UInt8 :=
  txSignedIntentDomainTag ++ tx.policy_digest ++
    canonicalIntentDigest { tx with message_digest := List.replicate 32 0 }

private theorem be_length_lt_u64 {w : Nat} (hw : w ≤ 32) (n : Nat) :
    (be w n).length < 256 ^ 8 := by
  rw [length_be]
  exact Nat.lt_of_le_of_lt hw (by decide)

/-- Scalar wire-width predicate confirming that all 12 integer scalars of `tx` fit production Rust widths. -/
def txScalarsFitWire (tx : TransactionIntent) : Bool :=
  decide (tx.chain_id < 256 ^ 8) &&
  decide (tx.suite_tag < 256 ^ 2) &&
  decide (tx.recipient_version < 256 ^ 1) &&
  decide (tx.recipient_suite_tag < 256 ^ 2) &&
  decide (tx.recipient_kind < 256 ^ 1) &&
  decide (tx.amount_units < 256 ^ 16) &&
  decide (tx.rolling_window_spent < 256 ^ 16) &&
  decide (tx.window_id < 256 ^ 8) &&
  decide (tx.nonce < 256 ^ 32) &&
  decide (tx.timestamp_secs < 256 ^ 8) &&
  decide (tx.initiator_party < 256 ^ 2) &&
  decide (tx.policy_revision < 256 ^ 8)

/-- Slice-length predicate confirming that all 13 byte-slice fields of `tx` fit `u64` length prefixes. -/
def txSlicesFitU64 (tx : TransactionIntent) : Bool :=
  decide (tx.policy_digest.length < 256 ^ 8) &&
  decide (tx.recipient_hrp.length < 256 ^ 8) &&
  decide (tx.recipient.length < 256 ^ 8) &&
  decide (tx.init_mac_bytes.length < 256 ^ 8) &&
  decide (tx.approver_bytes.length < 256 ^ 8) &&
  decide (tx.payload_digest.length < 256 ^ 8) &&
  decide (tx.authority_digest.length < 256 ^ 8) &&
  decide (tx.rolling_window_accumulator.length < 256 ^ 8) &&
  decide (tx.signing_key_id.length < 256 ^ 8) &&
  decide (tx.message_digest.length < 256 ^ 8) &&
  decide (tx.signing_context_digest.length < 256 ^ 8) &&
  decide (tx.session_id.length < 256 ^ 8) &&
  decide (tx.quorum_bytes.length < 256 ^ 8)

/-- Wire-width predicate confirming that every scalar and slice of `tx` fits production Rust integer widths. -/
def txFitsWireWidths (tx : TransactionIntent) : Bool :=
  txScalarsFitWire tx && txSlicesFitU64 tx

private def txFallbackFields (tx : TransactionIntent) : List (List UInt8) :=
  [tx.recipient, txLeb128 tx.amount_units, txLeb128 tx.window_id,
   tx.policy_digest, tx.authority_digest, txLeb128 tx.nonce,
   txLeb128 tx.chain_id, txLeb128 tx.suite_tag, tx.recipient_hrp,
   txLeb128 tx.recipient_version, txLeb128 tx.recipient_suite_tag, txLeb128 tx.recipient_kind,
   txLeb128 tx.rolling_window_spent, txLeb128 tx.timestamp_secs, txLeb128 tx.initiator_party,
   tx.init_mac_bytes, tx.approver_bytes, tx.payload_digest,
   tx.rolling_window_accumulator, tx.signing_key_id, txLeb128 tx.policy_revision,
   tx.message_digest, tx.signing_context_digest, tx.session_id, tx.quorum_bytes]

/-- Canonical `QSAG.POLICY.INTENT.V2` `u64 LE`-framed serializer for `TransactionIntent`
    (with a disjoint `0xFF`-prefixed lossless extension strictly for out-of-wire-range mathematical `Nat`s). -/
def encodeTransactionIntent (tx : TransactionIntent) : List UInt8 :=
  if txFitsWireWidths tx then
    txIntentDomainTag ++ encodeFramedU64Le (tx.policy_digest :: txIntentProdFrames tx)
  else
    0xFF :: txEncodeListFields (txFallbackFields tx)

/-- Canonical `QSAG.POLICY.INTENT.V2` `u64 LE`-framed decoder for `TransactionIntent`. -/
def decodeTransactionIntent (bytes : List UInt8) : Option TransactionIntent :=
  if bytes.head? == some 0xFF then
    match txDecodeListFields 25 (bytes.drop 1) with
    | some ([fRec, fAmt, fWid, polDig, fAuth, fNonce, fCid, fSuite, fHrp,
             fVer, fRecSuite, fKind, fSpent, fTs, fInit, fMacs, fAppr, fPay,
             fAcc, fKey, fRev, fMsg, fCtx, fSess, fQuo], []) =>
      match decodeLeb128Exact fAmt, decodeLeb128Exact fWid, decodeLeb128Exact fNonce,
            decodeLeb128Exact fCid, decodeLeb128Exact fSuite, decodeLeb128Exact fVer,
            decodeLeb128Exact fRecSuite, decodeLeb128Exact fKind, decodeLeb128Exact fSpent,
            decodeLeb128Exact fTs, decodeLeb128Exact fInit, decodeLeb128Exact fRev with
      | some amt, some wid, some nce, some cid, some ste, some ver,
        some rste, some knd, some spn, some ts, some ini, some rev =>
        some { recipient := fRec, amount_units := amt, window_id := wid,
               policy_digest := polDig, authority_digest := fAuth, nonce := nce,
               chain_id := cid, suite_tag := ste, recipient_hrp := fHrp,
               recipient_version := ver, recipient_suite_tag := rste, recipient_kind := knd,
               rolling_window_spent := spn, timestamp_secs := ts, initiator_party := ini,
               init_mac_bytes := fMacs, approver_bytes := fAppr, payload_digest := fPay,
               rolling_window_accumulator := fAcc, signing_key_id := fKey, policy_revision := rev,
               message_digest := fMsg, signing_context_digest := fCtx,
               session_id := fSess, quorum_bytes := fQuo }
      | _, _, _, _, _, _, _, _, _, _, _, _ => none
    | _ => none
  else if bytes.take 21 != txIntentDomainTag then none
  else
    match decodeFramedU64Le (bytes.drop 21) with
    | some [polDig, fCid, fSuite, fHrp, fVer, fRecSuite, fKind, fRec,
            fAmt, fSpent, fWid, fNonce, fTs, fInit, fMacs, fAppr, fPay,
            fAuth, fAcc, fKey, fRev, fMsg, fCtx, fSess, fQuo] =>
      if fCid.length == 8 && fSuite.length == 2 && fVer.length == 1 &&
         fRecSuite.length == 2 && fKind.length == 1 && fAmt.length == 16 &&
         fSpent.length == 16 && fWid.length == 8 && fNonce.length == 32 &&
         fTs.length == 8 && fInit.length == 2 && fRev.length == 8 then
        some { recipient := fRec, amount_units := ofBE fAmt, window_id := ofBE fWid,
               policy_digest := polDig, authority_digest := fAuth, nonce := ofBE fNonce,
               chain_id := ofBE fCid, suite_tag := ofBE fSuite, recipient_hrp := fHrp,
               recipient_version := ofBE fVer, recipient_suite_tag := ofBE fRecSuite,
               recipient_kind := ofBE fKind, rolling_window_spent := ofBE fSpent,
               timestamp_secs := ofBE fTs, initiator_party := ofBE fInit,
               init_mac_bytes := fMacs, approver_bytes := fAppr, payload_digest := fPay,
               rolling_window_accumulator := fAcc, signing_key_id := fKey,
               policy_revision := ofBE fRev, message_digest := fMsg,
               signing_context_digest := fCtx, session_id := fSess, quorum_bytes := fQuo }
      else none
    | _ => none

/-- For every Rust-width `TransactionIntent` (`txFitsWireWidths tx = true`), `encodeTransactionIntent`
    emits the exact `"QSAG.POLICY.INTENT.V2"` + `encodeFramedU64Le` byte layout. -/
theorem encodeTransactionIntent_eq_framed {tx : TransactionIntent}
    (hW : txFitsWireWidths tx = true) :
    encodeTransactionIntent tx =
      txIntentDomainTag ++ encodeFramedU64Le (tx.policy_digest :: txIntentProdFrames tx) := by
  unfold encodeTransactionIntent
  simp [hW]

private theorem list3_len_lt_u64 (a b c : List UInt8) : [a, b, c].length < 256 ^ 8 := by
  simp only [List.length_cons, List.length_nil]
  decide

private theorem list5_len_lt_u64 (a b c d e : List UInt8) : [a, b, c, d, e].length < 256 ^ 8 := by
  simp only [List.length_cons, List.length_nil]
  decide

private theorem forall_mem_cons_lt_u64 {x : List UInt8} {xs : List (List UInt8)}
    (hx : x.length < 256 ^ 8) (hxs : ∀ f ∈ xs, f.length < 256 ^ 8) :
    ∀ f ∈ x :: xs, f.length < 256 ^ 8 := by
  intro f hf
  cases hf with
  | head => exact hx
  | tail _ hTail => exact hxs f hTail

private theorem txProdFrames_all_lt_u64 {tx : TransactionIntent}
    (hW : txFitsWireWidths tx = true) :
    (tx.policy_digest :: txIntentProdFrames tx).length < 256 ^ 8 ∧
    (∀ f ∈ tx.policy_digest :: txIntentProdFrames tx, f.length < 256 ^ 8) := by
  have hSl : txSlicesFitU64 tx = true := (Bool.and_eq_true_iff.mp hW).2
  simp only [txSlicesFitU64, Bool.and_eq_true, and_assoc, decide_eq_true_eq] at hSl
  rcases hSl with ⟨hPol, hHrp, hRec, hMac, hApp, hPay, hAut, hAcc, hKey, hMsg, hCtx, hSes, hQuo⟩
  have hLen25 : (tx.policy_digest :: txIntentProdFrames tx).length < 256 ^ 8 := by
    rw [show (tx.policy_digest :: txIntentProdFrames tx).length = 25 from rfl]
    decide
  refine ⟨hLen25, ?_⟩
  dsimp only [txIntentProdFrames]
  exact forall_mem_cons_lt_u64 hPol
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 hHrp
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 hRec
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 hMac
    (forall_mem_cons_lt_u64 hApp
    (forall_mem_cons_lt_u64 hPay
    (forall_mem_cons_lt_u64 hAut
    (forall_mem_cons_lt_u64 hAcc
    (forall_mem_cons_lt_u64 hKey
    (forall_mem_cons_lt_u64 (be_length_lt_u64 (by decide) _)
    (forall_mem_cons_lt_u64 hMsg
    (forall_mem_cons_lt_u64 hCtx
    (forall_mem_cons_lt_u64 hSes
    (forall_mem_cons_lt_u64 hQuo
      (fun _ hf => nomatch hf)))))))))))))))))))))))))

/-- Exact roundtrip theorem `decodeTransactionIntent (encodeTransactionIntent tx) = some tx`
    across all 25 fields of `TransactionIntent`. -/
theorem decodeTransactionIntent_encodeTransactionIntent (tx : TransactionIntent) :
    decodeTransactionIntent (encodeTransactionIntent tx) = some tx := by
  unfold encodeTransactionIntent
  cases hW : txFitsWireWidths tx
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold decodeTransactionIntent
    have hHeadFF :
        ((0xFF :: txEncodeListFields (txFallbackFields tx)).head? == some 0xFF) = true := by
      show (some (0xFF : UInt8) == some 0xFF) = true
      decide
    rw [hHeadFF]
    simp only [↓reduceIte, List.drop_succ_cons, List.drop_zero]
    have hDec25 : txDecodeListFields 25 (txEncodeListFields (txFallbackFields tx)) =
        some (txFallbackFields tx, []) :=
      txDecodeListFields_txEncodeListFields (txFallbackFields tx)
    rw [hDec25]
    dsimp only [txFallbackFields]
    simp only [decodeLeb128Exact_txLeb128]
  · simp only [↓reduceIte]
    obtain ⟨hCnt, hAll⟩ := txProdFrames_all_lt_u64 hW
    have hSc : txScalarsFitWire tx = true := (Bool.and_eq_true_iff.mp hW).1
    simp only [txScalarsFitWire, Bool.and_eq_true, and_assoc, decide_eq_true_eq] at hSc
    rcases hSc with ⟨hCid, hSte, hVer, hRste, hKnd, hAmt, hSpn, hWid, hNce, hTs, hIni, hRev⟩
    let framed := encodeFramedU64Le (tx.policy_digest :: txIntentProdFrames tx)
    have hHeadNotFF : ((txIntentDomainTag ++ framed).head? == some 0xFF) = false := by
      show (some (0x51 : UInt8) == some 0xFF) = false
      decide
    have hTagLen : txIntentDomainTag.length = 21 := rfl
    have hTake : (txIntentDomainTag ++ framed).take 21 = txIntentDomainTag := by
      simp [hTagLen]
    have hDrop : (txIntentDomainTag ++ framed).drop 21 = framed := by
      simp [hTagLen]
    have hTagBne : (txIntentDomainTag != txIntentDomainTag) = false := by decide
    have hDecFramed : decodeFramedU64Le framed = some (tx.policy_digest :: txIntentProdFrames tx) :=
      decodeFramedU64Le_encodeFramedU64Le hCnt hAll
    have hWidthsOk :
        ((be 8 tx.chain_id).length == 8 && (be 2 tx.suite_tag).length == 2 &&
         (be 1 tx.recipient_version).length == 1 && (be 2 tx.recipient_suite_tag).length == 2 &&
         (be 1 tx.recipient_kind).length == 1 && (be 16 tx.amount_units).length == 16 &&
         (be 16 tx.rolling_window_spent).length == 16 && (be 8 tx.window_id).length == 8 &&
         (be 32 tx.nonce).length == 32 && (be 8 tx.timestamp_secs).length == 8 &&
         (be 2 tx.initiator_party).length == 2 && (be 8 tx.policy_revision).length == 8) = true := by
      simp only [length_be]
      decide
    unfold decodeTransactionIntent
    rw [hHeadNotFF]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hTake, hTagBne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hDrop, hDecFramed]
    dsimp only [txIntentProdFrames]
    rw [hWidthsOk]
    simp only [↓reduceIte]
    rw [ofBE_be hCid, ofBE_be hSte, ofBE_be hVer, ofBE_be hRste, ofBE_be hKnd,
        ofBE_be hAmt, ofBE_be hSpn, ofBE_be hWid, ofBE_be hNce, ofBE_be hTs,
        ofBE_be hIni, ofBE_be hRev]

/-- Strict injectivity of `encodeTransactionIntent` across all 25 fields. -/
theorem encodeTransactionIntent_injective {tx₁ tx₂ : TransactionIntent}
    (hEq : encodeTransactionIntent tx₁ = encodeTransactionIntent tx₂) :
    tx₁ = tx₂ := by
  have hDec := congrArg decodeTransactionIntent hEq
  rw [decodeTransactionIntent_encodeTransactionIntent,
      decodeTransactionIntent_encodeTransactionIntent] at hDec
  injection hDec

/-- Constructive (no choice operator) binding theorem for `toCanonicalSigningBytes`:
    any collision in `toCanonicalSigningBytes` between two fixed-width intents with 32-byte
    `policy_digest`s either agrees on `policy_digest` and every non-`message_digest` field of
    `TransactionIntent` OR yields an explicit `HashCollisionWitness` on
    `cshake256Bytes txIntentDomainTag`. -/
def toCanonicalSigningBytes_binding_or_collision
    (tx₁ tx₂ : TransactionIntent)
    (hPol₁ : tx₁.policy_digest.length = 32)
    (hPol₂ : tx₂.policy_digest.length = 32)
    (hW₁ : txFitsWireWidths { tx₁ with message_digest := List.replicate 32 0 } = true)
    (hW₂ : txFitsWireWidths { tx₂ with message_digest := List.replicate 32 0 } = true)
    (hEq : toCanonicalSigningBytes tx₁ = toCanonicalSigningBytes tx₂) :
    PSum (HashCollisionWitness (cshake256Bytes txIntentDomainTag))
         (tx₁.policy_digest = tx₂.policy_digest ∧
          { tx₁ with message_digest := List.replicate 32 0 } =
            { tx₂ with message_digest := List.replicate 32 0 }) :=
  let z₁ := { tx₁ with message_digest := List.replicate 32 0 }
  let z₂ := { tx₂ with message_digest := List.replicate 32 0 }
  have hStripTag :
      tx₁.policy_digest ++ canonicalIntentDigest z₁ =
        tx₂.policy_digest ++ canonicalIntentDigest z₂ := by
    unfold toCanonicalSigningBytes at hEq
    simp only [List.append_assoc] at hEq
    exact (List.append_inj hEq rfl).2
  have hSplitPol :
      tx₁.policy_digest = tx₂.policy_digest ∧
      canonicalIntentDigest z₁ = canonicalIntentDigest z₂ :=
    List.append_inj hStripTag (hPol₁.trans hPol₂.symm)
  if hZ : z₁ = z₂ then
    .inr ⟨hSplitPol.1, hZ⟩
  else
    let m1 := encodeFramedU64Le (txIntentProdFrames z₁)
    let m2 := encodeFramedU64Le (txIntentProdFrames z₂)
    have hPreNe : m1 ≠ m2 := fun hmEq => by
      have hFullEq : encodeTransactionIntent z₁ = encodeTransactionIntent z₂ := by
        rw [encodeTransactionIntent_eq_framed hW₁, encodeTransactionIntent_eq_framed hW₂]
        obtain ⟨_, hAll₁⟩ := txProdFrames_all_lt_u64 hW₁
        obtain ⟨_, hAll₂⟩ := txProdFrames_all_lt_u64 hW₂
        have hCnt24₁ : (txIntentProdFrames z₁).length < 256 ^ 8 := by
          rw [show (txIntentProdFrames z₁).length = 24 from rfl]; decide
        have hCnt24₂ : (txIntentProdFrames z₂).length < 256 ^ 8 := by
          rw [show (txIntentProdFrames z₂).length = 24 from rfl]; decide
        have hFramesEq := encodeFramedU64Le_injective
          hCnt24₁ (fun f hf => hAll₁ f (.tail _ hf))
          hCnt24₂ (fun f hf => hAll₂ f (.tail _ hf)) hmEq
        have hPolZ : z₁.policy_digest = z₂.policy_digest := hSplitPol.1
        have hListEq : z₁.policy_digest :: txIntentProdFrames z₁ =
            z₂.policy_digest :: txIntentProdFrames z₂ :=
          (congrArg (· :: txIntentProdFrames z₁) hPolZ).trans
            (congrArg (z₂.policy_digest :: ·) hFramesEq)
        exact congrArg (fun xs => txIntentDomainTag ++ encodeFramedU64Le xs) hListEq
      exact hZ (encodeTransactionIntent_injective hFullEq)
    .inl { m1 := m1, m2 := m2, ne := hPreNe, eq := hSplitPol.2 }

/-- Legacy evidence-model multi-turn policy state maintained inside custodian HSM / signer memory. -/
structure StatefulPolicyGuard where
  window_id : Nat
  velocity_window_cap : Nat
  accumulated_spend : Nat
  burned_intent_nonces : List Nat
  pinned_policy_digest : List UInt8
  pinned_authority_digest : List UInt8
  allowed_recipients : List (List UInt8)
  per_tx_cap : Nat
  deriving DecidableEq, Repr

/-- Approved signing envelope emitted by `policyCodecEvidenceStep`. -/
structure ApprovedIntentEnvelope where
  intent : TransactionIntent
  canonicalBytes : List UInt8
  deriving DecidableEq, Repr

/-- Rejection reasons of `policyCodecEvidenceStep`. -/
inductive PolicyRejectReason where
  | windowMismatch
  | policyDigestMismatch
  | authorityDigestMismatch
  | recipientNotAllowlisted
  | perTxCapExceeded
  | velocityWindowExceeded
  | duplicateIntentNonce
  deriving DecidableEq, Repr

/-- Canonical single-guardian stateful velocity, allowlist, digest-pinning, and nonce-replay guard
    transition bridged to Rust MIR in `MirSpecBridge.lean` (`mirPolicyGuard_forwardSim_custodyPolicy`). -/
def policyGuardStep (g : StatefulPolicyGuard) (tx : TransactionIntent) :
    CustodyStepOutcome StatefulPolicyGuard ApprovedIntentEnvelope PolicyRejectReason :=
  if tx.window_id != g.window_id then
    .rejected g .windowMismatch
  else if tx.policy_digest != g.pinned_policy_digest then
    .rejected g .policyDigestMismatch
  else if tx.authority_digest != g.pinned_authority_digest then
    .rejected g .authorityDigestMismatch
  else if ¬ (tx.recipient ∈ g.allowed_recipients) then
    .rejected g .recipientNotAllowlisted
  else if ¬ (tx.amount_units ≤ g.per_tx_cap) then
    .rejected g .perTxCapExceeded
  else if ¬ (g.accumulated_spend + tx.amount_units ≤ g.velocity_window_cap) then
    .rejected g .velocityWindowExceeded
  else if tx.nonce ∈ g.burned_intent_nonces then
    .rejected g .duplicateIntentNonce
  else
    let g' : StatefulPolicyGuard :=
      { g with accumulated_spend := g.accumulated_spend + tx.amount_units
               burned_intent_nonces := tx.nonce :: g.burned_intent_nonces }
    .accepted g' { intent := tx, canonicalBytes := encodeTransactionIntent tx }

/-- Compatibility alias for codec-evidence harnesses inside `CustodySuiteFull`. -/
abbrev policyCodecEvidenceStep :
    StatefulPolicyGuard → TransactionIntent →
      CustodyStepOutcome StatefulPolicyGuard ApprovedIntentEnvelope PolicyRejectReason :=
  policyGuardStep

private theorem policy_no_nonce_if_burned
    {g gFinal : StatefulPolicyGuard}
    {trace : List (TransactionIntent × Option ApprovedIntentEnvelope)}
    (hTr : ValidCustodyTrace policyGuardStep g trace gFinal) :
    ∀ nonce ∈ g.burned_intent_nonces,
      nonce ∉ (traceApprovedOutputs trace).map (fun e => e.intent.nonce) := by
  induction hTr with
  | nil => intro _ _ hm; cases hm
  | @consAccepted s s' _ tx env rest hStep _ ih =>
    intro nonce hBurn
    unfold policyGuardStep at hStep
    if h1 : (tx.window_id != s.window_id) = true then simp [h1] at hStep
    else if h2 : (tx.policy_digest != s.pinned_policy_digest) = true then simp [h1, h2] at hStep
    else if h3 : (tx.authority_digest != s.pinned_authority_digest) = true then simp [h1, h2, h3] at hStep
    else if h4 : ¬ (tx.recipient ∈ s.allowed_recipients) then simp [h1, h2, h3, h4] at hStep
    else if h5 : ¬ (tx.amount_units ≤ s.per_tx_cap) then simp [h1, h2, h3, h4, h5] at hStep
    else if h6 : ¬ (s.accumulated_spend + tx.amount_units ≤ s.velocity_window_cap) then
      simp [h1, h2, h3, h4, h5, h6] at hStep
    else if h7 : tx.nonce ∈ s.burned_intent_nonces then
      simp [h1, h2, h3, h4, h5, h6, h7] at hStep
    else
      simp only [h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ↓reduceIte,
        CustodyStepOutcome.accepted.injEq] at hStep
      rcases hStep with ⟨rfl, rfl⟩
      have hNe : nonce ≠ tx.nonce := fun hEq => h7 (hEq ▸ hBurn)
      simp only [traceApprovedOutputs_cons_some, List.map_cons, List.mem_cons, not_or]
      exact ⟨hNe, ih nonce (.tail _ hBurn)⟩
  | @consRejected s s' _ tx err rest hStep _ ih =>
    intro nonce hBurn
    simp only [traceApprovedOutputs_cons_none]
    unfold policyGuardStep at hStep
    split at hStep
    · cases hStep; exact ih nonce hBurn
    · split at hStep
      · cases hStep; exact ih nonce hBurn
      · split at hStep
        · cases hStep; exact ih nonce hBurn
        · split at hStep
          · cases hStep; exact ih nonce hBurn
          · split at hStep
            · cases hStep; exact ih nonce hBurn
            · split at hStep
              · cases hStep; exact ih nonce hBurn
              · split at hStep <;> cases hStep
                exact ih nonce hBurn

/-- **Multi-Turn Stateful Policy Velocity, Replay & Intent-Binding Theorem
    (`policy_multiturn_velocity_and_intent_binding`)**:
    Across ANY multi-turn signing trace starting from `g₀` (`g₀.accumulated_spend ≤ g₀.velocity_window_cap`):
    1. **Cumulative Velocity Safety**: `g₀.accumulated_spend + ∑ approved.amount_units = gFinal.accumulated_spend ≤ g₀.velocity_window_cap`
       (hence `∑ approved.amount_units ≤ g₀.velocity_window_cap`!).
    2. **Zero Nonce Replay**: `(approved.map nonce).Nodup` and zero pre-burned nonces are ever approved.
    3. **Pinned Policy/Authority/Allowlist Binding**: Every approved envelope matches `g₀.window_id`,
       `g₀.pinned_policy_digest`, `g₀.pinned_authority_digest`, `g₀.allowed_recipients`, and `≤ g₀.per_tx_cap`.
    4. **Bijective Canonical V2 Intent Codec**: `decodeTransactionIntent (encodeTransactionIntent tx) = some tx`
       and `encodeTransactionIntent` is strictly injective across all 25 fields! -/
theorem policy_multiturn_velocity_and_intent_binding
    {g₀ gFinal : StatefulPolicyGuard}
    {trace : List (TransactionIntent × Option ApprovedIntentEnvelope)}
    (hInitLe : g₀.accumulated_spend ≤ g₀.velocity_window_cap)
    (hTrace : ValidCustodyTrace policyGuardStep g₀ trace gFinal) :
    let approved := traceApprovedOutputs trace
    let approvedSum := (approved.map (fun e => e.intent.amount_units)).foldr (· + ·) 0
    g₀.accumulated_spend + approvedSum = gFinal.accumulated_spend ∧
    gFinal.accumulated_spend ≤ g₀.velocity_window_cap ∧
    approvedSum ≤ g₀.velocity_window_cap ∧
    (approved.map (fun e => e.intent.nonce)).Nodup ∧
    (∀ e ∈ approved,
      e.intent.nonce ∉ g₀.burned_intent_nonces ∧
      e.intent.window_id = g₀.window_id ∧
      e.intent.policy_digest = g₀.pinned_policy_digest ∧
      e.intent.authority_digest = g₀.pinned_authority_digest ∧
      e.intent.recipient ∈ g₀.allowed_recipients ∧
      e.intent.amount_units ≤ g₀.per_tx_cap ∧
      e.canonicalBytes = encodeTransactionIntent e.intent) ∧
    (∀ tx : TransactionIntent, decodeTransactionIntent (encodeTransactionIntent tx) = some tx) ∧
    (∀ tx₁ tx₂ : TransactionIntent, encodeTransactionIntent tx₁ = encodeTransactionIntent tx₂ → tx₁ = tx₂) := by
  have hCore : ∀ {s sf : StatefulPolicyGuard}
      {tr : List (TransactionIntent × Option ApprovedIntentEnvelope)},
      ValidCustodyTrace policyGuardStep s tr sf →
      s.accumulated_spend ≤ s.velocity_window_cap →
      let app := traceApprovedOutputs tr
      let appSum := (app.map (fun e => e.intent.amount_units)).foldr (· + ·) 0
      s.accumulated_spend + appSum = sf.accumulated_spend ∧
      sf.accumulated_spend ≤ s.velocity_window_cap ∧
      (app.map (fun e => e.intent.nonce)).Nodup ∧
      (∀ e ∈ app,
        e.intent.nonce ∉ s.burned_intent_nonces ∧
        e.intent.window_id = s.window_id ∧
        e.intent.policy_digest = s.pinned_policy_digest ∧
        e.intent.authority_digest = s.pinned_authority_digest ∧
        e.intent.recipient ∈ s.allowed_recipients ∧
        e.intent.amount_units ≤ s.per_tx_cap ∧
        e.canonicalBytes = encodeTransactionIntent e.intent) := by
    intro s sf tr hTr
    induction hTr with
    | nil =>
      intro hLe
      exact ⟨by simp, hLe, .nil, fun _ hm => by cases hm⟩
    | @consAccepted st st' _ tx env rest hStep hRest ih =>
      intro hLe
      unfold policyGuardStep at hStep
      if h1 : (tx.window_id != st.window_id) = true then simp [h1] at hStep
      else if h2 : (tx.policy_digest != st.pinned_policy_digest) = true then simp [h1, h2] at hStep
      else if h3 : (tx.authority_digest != st.pinned_authority_digest) = true then simp [h1, h2, h3] at hStep
      else if h4 : ¬ (tx.recipient ∈ st.allowed_recipients) then simp [h1, h2, h3, h4] at hStep
      else if h5 : ¬ (tx.amount_units ≤ st.per_tx_cap) then simp [h1, h2, h3, h4, h5] at hStep
      else if h6 : ¬ (st.accumulated_spend + tx.amount_units ≤ st.velocity_window_cap) then
        simp [h1, h2, h3, h4, h5, h6] at hStep
      else if h7 : tx.nonce ∈ st.burned_intent_nonces then
        simp [h1, h2, h3, h4, h5, h6, h7] at hStep
      else
        simp only [h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ↓reduceIte,
          CustodyStepOutcome.accepted.injEq] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        have hWin : tx.window_id = st.window_id := by
          cases hEq : (tx.window_id == st.window_id)
          · exfalso; exact h1 (by simp [bne, hEq])
          · exact of_decide_eq_true hEq
        have hPol : tx.policy_digest = st.pinned_policy_digest := by
          cases hEq : (tx.policy_digest == st.pinned_policy_digest)
          · exfalso; exact h2 (by simp [bne, hEq])
          · exact eq_of_beq hEq
        have hAuth : tx.authority_digest = st.pinned_authority_digest := by
          cases hEq : (tx.authority_digest == st.pinned_authority_digest)
          · exfalso; exact h3 (by simp [bne, hEq])
          · exact eq_of_beq hEq
        have hRecip : tx.recipient ∈ st.allowed_recipients := by
          cases Decidable.em (tx.recipient ∈ st.allowed_recipients) with
          | inl h => exact h
          | inr hn => exact False.elim (h4 hn)
        have hPerTx : tx.amount_units ≤ st.per_tx_cap := Decidable.of_not_not h5
        have hVel : st.accumulated_spend + tx.amount_units ≤ st.velocity_window_cap :=
          Decidable.of_not_not h6
        obtain ⟨hSumEq, hFinLe, hNdRest, hPropsRest⟩ := ih hVel
        dsimp only at hSumEq hFinLe
        have hNotInRest : tx.nonce ∉ (traceApprovedOutputs rest).map (fun e => e.intent.nonce) :=
          policy_no_nonce_if_burned hRest tx.nonce (.head _)
        simp only [traceApprovedOutputs_cons_some, List.map_cons, List.foldr_cons]
        refine ⟨by rw [← Nat.add_assoc, hSumEq], hFinLe,
                .cons (fun x hx hEq => hNotInRest (hEq ▸ hx)) hNdRest, ?_⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | hTail
        · exact ⟨h7, hWin, hPol, hAuth, hRecip, hPerTx, rfl⟩
        · obtain ⟨hNotBurn', hW', hP', hA', hR', hCap', hBytes'⟩ := hPropsRest e hTail
          exact ⟨fun hb => hNotBurn' (.tail _ hb), hW', hP', hA', hR', hCap', hBytes'⟩
    | @consRejected st st' _ tx err rest hStep _ ih =>
      intro hLe
      simp only [traceApprovedOutputs_cons_none]
      unfold policyGuardStep at hStep
      split at hStep
      · cases hStep; exact ih hLe
      · split at hStep
        · cases hStep; exact ih hLe
        · split at hStep
          · cases hStep; exact ih hLe
          · split at hStep
            · cases hStep; exact ih hLe
            · split at hStep
              · cases hStep; exact ih hLe
              · split at hStep
                · cases hStep; exact ih hLe
                · split at hStep <;> cases hStep
                  exact ih hLe
  obtain ⟨hSumEq, hFinLe, hNd, hProps⟩ := hCore hTrace hInitLe
  exact ⟨hSumEq, hFinLe, Nat.le_trans (Nat.le_add_left _ _) (hSumEq.symm ▸ hFinLe), hNd, hProps,
         decodeTransactionIntent_encodeTransactionIntent,
         fun _ _ h => encodeTransactionIntent_injective h⟩

/-! ### §3.1b Monotonic `minNonceWatermark` + Sliding-Window Bitmap Replay & Clock-Anchored Epoch Guard -/

/-- Read slot `k` of a bounded sliding-window anti-replay bitmap (`false` out of bounds). -/
def slidingWindowTest (bm : List Bool) (k : Nat) : Bool :=
  bm.getD k false

/-- Construct a fixed-width `w`-slot sliding-window bitmap structurally (no choice operator). -/
def buildSlidingWindow : Nat → (Nat → Bool) → List Bool
  | 0, _ => []
  | w + 1, f => f 0 :: buildSlidingWindow w (fun i => f (i + 1))

@[simp] theorem buildSlidingWindow_length (w : Nat) (f : Nat → Bool) :
    (buildSlidingWindow w f).length = w := by
  induction w generalizing f with
  | zero => rfl
  | succ w ih => simp [buildSlidingWindow, ih]

theorem slidingWindowTest_buildSlidingWindow :
    ∀ (w : Nat) (f : Nat → Bool) (k : Nat),
      slidingWindowTest (buildSlidingWindow w f) k = if k < w then f k else false
  | 0, _, k => by
    have hn : ¬ (k < 0) := Nat.not_lt_zero k
    simp [buildSlidingWindow, slidingWindowTest, hn]
  | w + 1, f, 0 => by
    simp [buildSlidingWindow, slidingWindowTest]
  | w + 1, f, j + 1 => by
    unfold buildSlidingWindow slidingWindowTest
    dsimp only [List.getD]
    change slidingWindowTest (buildSlidingWindow w (fun i => f (i + 1))) j = _
    rw [slidingWindowTest_buildSlidingWindow w (fun i => f (i + 1)) j]
    if hj : j < w then
      have hj' : j + 1 < w + 1 := Nat.succ_lt_succ hj
      simp [hj, hj']
    else
      have hj' : ¬ (j + 1 < w + 1) := fun h => hj (Nat.lt_of_succ_lt_succ h)
      simp [hj, hj']

theorem slidingWindowTest_buildSlidingWindow_of_lt {w k : Nat} (f : Nat → Bool) (hk : k < w) :
    slidingWindowTest (buildSlidingWindow w f) k = f k := by
  rw [slidingWindowTest_buildSlidingWindow]
  simp only [hk, ↓reduceIte]

theorem slidingWindowTest_ge_length :
    ∀ (bm : List Bool) (k : Nat), bm.length ≤ k → slidingWindowTest bm k = false
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: bs, j + 1, h =>
    slidingWindowTest_ge_length bs j (Nat.le_of_succ_le_succ h)

/-- Legacy evidence-model bounded-state `qsag-policy` guard eliminating the 256-slot FIFO eviction replay wrap
    via monotonic `minNonceWatermark` + `slidingWindowWidth`-slot bitmap, default-on initiator MAC
    authentication (`requireAuthenticatedInitiator := true`), and clock-anchored epoch rotation. -/
structure PolicyWatermarkGuard where
  chain_id : Nat
  pinned_suite_tag : Nat
  window_id : Nat
  epoch_start_secs : Nat
  epoch_duration_secs : Nat
  velocity_window_cap : Nat
  accumulated_spend : Nat
  per_tx_cap : Nat
  minNonceWatermark : Nat
  slidingWindowWidth : Nat
  slidingBitmap : List Bool
  pinned_policy_digest : List UInt8
  pinned_authority_digest : List UInt8
  allowed_recipients : List (List UInt8)
  requireAuthenticatedInitiator : Bool := true
  deriving DecidableEq, Repr

/-- Candidate inputs to `policyBitmapEvidenceStep` (signing intent evaluation or clock-anchored window advance). -/
inductive PolicyWatermarkInput where
  | evaluateIntent (tx : TransactionIntent)
  | advanceEpoch (nowSecs : Nat)
  deriving DecidableEq, Repr

/-- Observable events of `policyBitmapEvidenceStep`. -/
inductive PolicyWatermarkEvent where
  | intentApproved (intent : TransactionIntent) (canonicalSigningBytes : List UInt8)
  | epochAdvanced (newWindowId : Nat) (newEpochStartSecs : Nat)
  deriving DecidableEq, Repr

/-- Rejection reasons of `policyBitmapEvidenceStep`. -/
inductive PolicyWatermarkReject where
  | invalidWindowWidth
  | chainOrSuiteMismatch
  | windowMismatch
  | policyOrAuthorityDigestMismatch
  | unauthenticatedInitiator
  | recipientNotAllowlisted
  | perTxCapExceeded
  | velocityWindowExceeded
  | nonceBelowWatermark
  | duplicateNonceInSlidingWindow
  | epochAdvanceTooEarly
  deriving DecidableEq, Repr

/-- Legacy evidence-model `PolicyWatermarkGuard` transition enforcing monotonic `minNonceWatermark` + sliding-window
    anti-replay, default-on initiator MAC authentication, and clock-anchored velocity window rotation
    that preserves `(minNonceWatermark, slidingBitmap)` across epochs. -/
def policyBitmapEvidenceStep (g : PolicyWatermarkGuard) (inp : PolicyWatermarkInput) :
    CustodyStepOutcome PolicyWatermarkGuard PolicyWatermarkEvent PolicyWatermarkReject :=
  if g.slidingWindowWidth == 0 || g.slidingBitmap.length != g.slidingWindowWidth then
    .rejected g .invalidWindowWidth
  else
    match inp with
    | .advanceEpoch nowSecs =>
      if g.epoch_duration_secs == 0 || decide (nowSecs < g.epoch_start_secs + g.epoch_duration_secs) then
        .rejected g .epochAdvanceTooEarly
      else
        let g' : PolicyWatermarkGuard :=
          { g with window_id := g.window_id + 1
                   epoch_start_secs := nowSecs
                   accumulated_spend := 0 }
        .accepted g' (.epochAdvanced (g.window_id + 1) nowSecs)
    | .evaluateIntent tx =>
      if tx.chain_id != g.chain_id || tx.suite_tag != g.pinned_suite_tag ||
         tx.recipient_suite_tag != g.pinned_suite_tag then
        .rejected g .chainOrSuiteMismatch
      else if tx.window_id != g.window_id then
        .rejected g .windowMismatch
      else if tx.policy_digest != g.pinned_policy_digest ||
              tx.authority_digest != g.pinned_authority_digest then
        .rejected g .policyOrAuthorityDigestMismatch
      else if g.requireAuthenticatedInitiator && tx.init_mac_bytes.isEmpty then
        .rejected g .unauthenticatedInitiator
      else if ¬ (tx.recipient ∈ g.allowed_recipients) then
        .rejected g .recipientNotAllowlisted
      else if ¬ (tx.amount_units ≤ g.per_tx_cap) then
        .rejected g .perTxCapExceeded
      else if ¬ (g.accumulated_spend + tx.amount_units ≤ g.velocity_window_cap) then
        .rejected g .velocityWindowExceeded
      else if tx.nonce < g.minNonceWatermark then
        .rejected g .nonceBelowWatermark
      else
        let w := g.slidingWindowWidth
        let offset := tx.nonce - g.minNonceWatermark
        if offset < w then
          if slidingWindowTest g.slidingBitmap offset then
            .rejected g .duplicateNonceInSlidingWindow
          else
            let bm' := buildSlidingWindow w (fun i => slidingWindowTest g.slidingBitmap i || decide (i = offset))
            let g' := { g with accumulated_spend := g.accumulated_spend + tx.amount_units
                               slidingBitmap := bm' }
            .accepted g' (.intentApproved tx (toCanonicalSigningBytes tx))
        else
          let shift := offset - (w - 1)
          let wm' := g.minNonceWatermark + shift
          let bm' := buildSlidingWindow w (fun i =>
            slidingWindowTest g.slidingBitmap (i + shift) || decide (i = w - 1))
          let g' := { g with accumulated_spend := g.accumulated_spend + tx.amount_units
                             minNonceWatermark := wm'
                             slidingBitmap := bm' }
          .accepted g' (.intentApproved tx (toCanonicalSigningBytes tx))

/-- Logical consumption predicate of the `(minNonceWatermark, slidingBitmap)` anti-replay state:
    every nonce strictly below `minNonceWatermark` or marked inside `slidingBitmap` is permanently consumed. -/
def nonceConsumedByWatermark (g : PolicyWatermarkGuard) (n : Nat) : Prop :=
  n < g.minNonceWatermark ∨ slidingWindowTest g.slidingBitmap (n - g.minNonceWatermark) = true

/-- Extract all approved `(intent, canonicalSigningBytes)` pairs from a `PolicyWatermarkEvent` list. -/
def watermarkApprovedIntents : List PolicyWatermarkEvent → List (TransactionIntent × List UInt8)
  | [] => []
  | .intentApproved tx sigBytes :: rest => (tx, sigBytes) :: watermarkApprovedIntents rest
  | .epochAdvanced _ _ :: rest => watermarkApprovedIntents rest

private theorem policyBitmapEvidenceStep_rejected_eq
    {g g' : PolicyWatermarkGuard} {inp : PolicyWatermarkInput} {err : PolicyWatermarkReject}
    (hStep : policyBitmapEvidenceStep g inp = .rejected g' err) :
    g' = g := by
  unfold policyBitmapEvidenceStep at hStep
  if hBad : (g.slidingWindowWidth == 0 || g.slidingBitmap.length != g.slidingWindowWidth) = true then
    simp only [hBad, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
    exact hStep.1.symm
  else
    simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hStep
    cases inp with
    | advanceEpoch nowSecs =>
      if hEarly : (g.epoch_duration_secs == 0 ||
                   decide (nowSecs < g.epoch_start_secs + g.epoch_duration_secs)) = true then
        simp only [hEarly, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
        exact hStep.1.symm
      else
        simp [hEarly] at hStep
    | evaluateIntent tx =>
      if c1 : (tx.chain_id != g.chain_id || tx.suite_tag != g.pinned_suite_tag ||
               tx.recipient_suite_tag != g.pinned_suite_tag) = true then
        simp only [c1, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep; exact hStep.1.symm
      else if c2 : (tx.window_id != g.window_id) = true then
        simp only [c1, c2, Bool.false_eq_true, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep; exact hStep.1.symm
      else if c3 : (tx.policy_digest != g.pinned_policy_digest ||
                    tx.authority_digest != g.pinned_authority_digest) = true then
        simp only [c1, c2, c3, Bool.false_eq_true, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep; exact hStep.1.symm
      else if c4 : (g.requireAuthenticatedInitiator && tx.init_mac_bytes.isEmpty) = true then
        simp only [c1, c2, c3, c4, Bool.false_eq_true, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep; exact hStep.1.symm
      else if c5 : ¬ (tx.recipient ∈ g.allowed_recipients) then
        simp only [c1, c2, c3, c4, c5, not_false_eq_true, Bool.false_eq_true, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep; exact hStep.1.symm
      else if c6 : ¬ (tx.amount_units ≤ g.per_tx_cap) then
        simp only [c1, c2, c3, c4, c5, c6, not_false_eq_true, Bool.false_eq_true, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep; exact hStep.1.symm
      else if c7 : ¬ (g.accumulated_spend + tx.amount_units ≤ g.velocity_window_cap) then
        simp only [c1, c2, c3, c4, c5, c6, c7, not_false_eq_true, Bool.false_eq_true, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep; exact hStep.1.symm
      else if c8 : tx.nonce < g.minNonceWatermark then
        simp only [c1, c2, c3, c4, c5, c6, c7, c8, Bool.false_eq_true, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep; exact hStep.1.symm
      else
        simp only [c1, c2, c3, c4, c5, c6, c7, c8, Bool.false_eq_true, ↓reduceIte] at hStep
        if hInWin : tx.nonce - g.minNonceWatermark < g.slidingWindowWidth then
          simp only [hInWin, ↓reduceIte] at hStep
          if hDup : slidingWindowTest g.slidingBitmap (tx.nonce - g.minNonceWatermark) = true then
            simp only [hDup, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep; exact hStep.1.symm
          else
            simp [hDup] at hStep
        else
          simp [hInWin] at hStep

private theorem watermark_consumed_preserved_and_marks
    {g g' : PolicyWatermarkGuard} {inp : PolicyWatermarkInput} {ev : PolicyWatermarkEvent}
    (hStep : policyBitmapEvidenceStep g inp = .accepted g' ev) :
    0 < g'.slidingWindowWidth ∧
    g'.slidingBitmap.length = g'.slidingWindowWidth ∧
    g.minNonceWatermark ≤ g'.minNonceWatermark ∧
    g'.requireAuthenticatedInitiator = g.requireAuthenticatedInitiator ∧
    (∀ n, nonceConsumedByWatermark g n → nonceConsumedByWatermark g' n) ∧
    (∀ tx sb, ev = .intentApproved tx sb →
      ¬ nonceConsumedByWatermark g tx.nonce ∧
      nonceConsumedByWatermark g' tx.nonce ∧
      sb = toCanonicalSigningBytes tx ∧
      (g.requireAuthenticatedInitiator = true → tx.init_mac_bytes ≠ [])) := by
  unfold policyBitmapEvidenceStep at hStep
  if hBadW : (g.slidingWindowWidth == 0 || g.slidingBitmap.length != g.slidingWindowWidth) = true then
    simp only [hBadW, ↓reduceIte] at hStep; nomatch hStep
  else
    have hWPos : 0 < g.slidingWindowWidth := by
      cases hZ : (g.slidingWindowWidth == 0)
      · have hNe0 : g.slidingWindowWidth ≠ 0 := fun h0 => by rw [h0] at hZ; cases hZ
        omega
      · exfalso; rw [hZ] at hBadW; exact hBadW rfl
    have hBmLen : g.slidingBitmap.length = g.slidingWindowWidth := by
      cases hEq : (g.slidingBitmap.length == g.slidingWindowWidth)
      · exfalso
        cases hZ : (g.slidingWindowWidth == 0) <;>
          simp only [hZ, bne, hEq, Bool.not_false, Bool.or_true] at hBadW <;>
          exact hBadW trivial
      · exact of_decide_eq_true hEq
    simp only [hBadW, Bool.false_eq_true, ↓reduceIte] at hStep
    cases inp with
    | advanceEpoch nowSecs =>
      if hEarly : (g.epoch_duration_secs == 0 ||
                   decide (nowSecs < g.epoch_start_secs + g.epoch_duration_secs)) = true then
        simp only [hEarly, ↓reduceIte] at hStep; nomatch hStep
      else
        simp only [hEarly, Bool.false_eq_true, ↓reduceIte] at hStep
        injection hStep with hSt hEv
        subst hSt hEv
        exact ⟨hWPos, hBmLen, Nat.le_refl _, rfl, fun _ h => h, fun _ _ hEv => by cases hEv⟩
    | evaluateIntent tx =>
      if c1 : (tx.chain_id != g.chain_id || tx.suite_tag != g.pinned_suite_tag ||
               tx.recipient_suite_tag != g.pinned_suite_tag) = true then
        simp only [c1, ↓reduceIte] at hStep; nomatch hStep
      else if c2 : (tx.window_id != g.window_id) = true then
        simp only [c1, c2, Bool.false_eq_true, ↓reduceIte] at hStep; nomatch hStep
      else if c3 : (tx.policy_digest != g.pinned_policy_digest ||
                    tx.authority_digest != g.pinned_authority_digest) = true then
        simp only [c1, c2, c3, Bool.false_eq_true, ↓reduceIte] at hStep; nomatch hStep
      else if c4 : (g.requireAuthenticatedInitiator && tx.init_mac_bytes.isEmpty) = true then
        simp only [c1, c2, c3, c4, Bool.false_eq_true, ↓reduceIte] at hStep; nomatch hStep
      else if c5 : ¬ (tx.recipient ∈ g.allowed_recipients) then
        simp only [c1, c2, c3, c4, c5, not_false_eq_true, Bool.false_eq_true, ↓reduceIte] at hStep; nomatch hStep
      else if c6 : ¬ (tx.amount_units ≤ g.per_tx_cap) then
        simp only [c1, c2, c3, c4, c5, c6, not_false_eq_true, Bool.false_eq_true, ↓reduceIte] at hStep; nomatch hStep
      else if c7 : ¬ (g.accumulated_spend + tx.amount_units ≤ g.velocity_window_cap) then
        simp only [c1, c2, c3, c4, c5, c6, c7, not_false_eq_true, Bool.false_eq_true, ↓reduceIte] at hStep; nomatch hStep
      else if c8 : tx.nonce < g.minNonceWatermark then
        simp only [c1, c2, c3, c4, c5, c6, c7, c8, Bool.false_eq_true, ↓reduceIte] at hStep; nomatch hStep
      else
        simp only [c1, c2, c3, c4, c5, c6, c7, c8, Bool.false_eq_true, ↓reduceIte] at hStep
        have hAuthInit : g.requireAuthenticatedInitiator = true → tx.init_mac_bytes ≠ [] := by
          intro hReq hEmp
          rw [hReq, hEmp] at c4
          exact c4 rfl
        if hInWin : tx.nonce - g.minNonceWatermark < g.slidingWindowWidth then
          simp only [hInWin, ↓reduceIte] at hStep
          if hDup : slidingWindowTest g.slidingBitmap (tx.nonce - g.minNonceWatermark) = true then
            simp only [hDup, ↓reduceIte] at hStep; nomatch hStep
          else
            simp only [hDup, Bool.false_eq_true, ↓reduceIte] at hStep
            injection hStep with hSt hEvStep
            subst hSt hEvStep
            refine ⟨hWPos, buildSlidingWindow_length _ _, Nat.le_refl _, rfl, ?_, ?_⟩
            · intro n hn
              rcases hn with hLt | hBit
              · exact Or.inl hLt
              · apply Or.inr
                have hLtW : n - g.minNonceWatermark < g.slidingWindowWidth := by
                  if hLt' : n - g.minNonceWatermark < g.slidingWindowWidth then exact hLt'
                  else
                    rw [slidingWindowTest_ge_length g.slidingBitmap _ (by omega)] at hBit
                    cases hBit
                rw [slidingWindowTest_buildSlidingWindow_of_lt _ hLtW]
                exact Bool.or_eq_true_iff.mpr (Or.inl hBit)
            · intro tx' sb' hEv
              injection hEv with hTx hSb
              subst hTx hSb
              refine ⟨?_, ?_, rfl, hAuthInit⟩
              · rintro (hLt | hBit)
                · exact c8 hLt
                · exact hDup hBit
              · apply Or.inr
                rw [slidingWindowTest_buildSlidingWindow_of_lt _ hInWin]
                exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true rfl))
        else
          simp only [hInWin, ↓reduceIte] at hStep
          injection hStep with hSt hEvStep
          subst hSt hEvStep
          refine ⟨hWPos, buildSlidingWindow_length _ _, Nat.le_add_right _ _, rfl, ?_, ?_⟩
          · intro n hn
            if hBelowNew :
                n < g.minNonceWatermark + ((tx.nonce - g.minNonceWatermark) - (g.slidingWindowWidth - 1)) then
              exact Or.inl hBelowNew
            else
              rcases hn with hLtOld | hBitOld
              · exfalso; omega
              · apply Or.inr
                have hOldLtW : n - g.minNonceWatermark < g.slidingWindowWidth := by
                  if hLt' : n - g.minNonceWatermark < g.slidingWindowWidth then exact hLt'
                  else
                    rw [slidingWindowTest_ge_length g.slidingBitmap _ (by omega)] at hBitOld
                    cases hBitOld
                have hNewLtW :
                    n - (g.minNonceWatermark + ((tx.nonce - g.minNonceWatermark) - (g.slidingWindowWidth - 1))) <
                      g.slidingWindowWidth := by omega
                have hIdxEq :
                    n - (g.minNonceWatermark + ((tx.nonce - g.minNonceWatermark) - (g.slidingWindowWidth - 1))) +
                      ((tx.nonce - g.minNonceWatermark) - (g.slidingWindowWidth - 1)) =
                      n - g.minNonceWatermark := by omega
                rw [slidingWindowTest_buildSlidingWindow_of_lt _ hNewLtW]
                exact Bool.or_eq_true_iff.mpr (Or.inl (hIdxEq.symm ▸ hBitOld))
          · intro tx' sb' hEv
            injection hEv with hTx hSb
            subst hTx hSb
            refine ⟨?_, ?_, rfl, hAuthInit⟩
            · rintro (hLt | hBit)
              · exact c8 hLt
              · rw [slidingWindowTest_ge_length g.slidingBitmap _ (by omega)] at hBit
                cases hBit
            · apply Or.inr
              have hTopIdx :
                  tx.nonce - (g.minNonceWatermark + ((tx.nonce - g.minNonceWatermark) - (g.slidingWindowWidth - 1))) =
                    g.slidingWindowWidth - 1 := by omega
              have hWm1Lt : g.slidingWindowWidth - 1 < g.slidingWindowWidth := by omega
              rw [hTopIdx, slidingWindowTest_buildSlidingWindow_of_lt _ hWm1Lt]
              exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true rfl))

private theorem watermark_no_approved_if_consumed
    {g gFinal : PolicyWatermarkGuard}
    {trace : List (PolicyWatermarkInput × Option PolicyWatermarkEvent)}
    (hTr : ValidCustodyTrace policyBitmapEvidenceStep g trace gFinal) :
    ∀ n, nonceConsumedByWatermark g n →
      n ∉ (watermarkApprovedIntents (traceApprovedOutputs trace)).map (fun p => p.1.nonce) := by
  induction hTr with
  | nil => intro _ _ hm; cases hm
  | @consAccepted s s' _ inp ev rest hStep _ ih =>
    obtain ⟨_, _, _, _, hMono, hMark⟩ := watermark_consumed_preserved_and_marks hStep
    intro n hn
    cases ev with
    | epochAdvanced wId nowS =>
      simpa [traceApprovedOutputs_cons_some, watermarkApprovedIntents] using ih n (hMono n hn)
    | intentApproved tx sb =>
      obtain ⟨hFreshTx, _, _, _⟩ := hMark tx sb rfl
      have hNe : n ≠ tx.nonce := fun hEq => hFreshTx (hEq ▸ hn)
      simp only [traceApprovedOutputs_cons_some, watermarkApprovedIntents, List.map_cons,
        List.mem_cons, not_or]
      exact ⟨hNe, ih n (hMono n hn)⟩
  | @consRejected s s' _ inp err rest hStep _ ih =>
    have hSame : s' = s := policyBitmapEvidenceStep_rejected_eq hStep
    subst hSame
    simpa [traceApprovedOutputs_cons_none] using ih

/-- **Multi-Turn Monotonic Watermark + Sliding-Window Anti-Replay & Initiator-Auth Soundness
    (`policy_watermark_sliding_window_multiturn_sound`)**:
    Across ANY multi-turn signing and clock-epoch trace of arbitrary length (including `> 256`
    transactions and across multiple velocity window rotations):
    1. `minNonceWatermark` never decreases (`g₀.minNonceWatermark ≤ gFinal.minNonceWatermark`),
    2. **Zero Nonce Replay Ever**: `(approved.map nonce).Nodup` holds unconditionally with $O(W)$ state
       (zero FIFO ring-eviction wrap!),
    3. Every approved nonce satisfies `g₀.minNonceWatermark ≤ tx.nonce` and `!nonceConsumedByWatermark g₀ tx.nonce`,
    4. Every approved envelope emits `toCanonicalSigningBytes tx` (`QSAG.POLICY.SIGNED_INTENT.V2`)
       and carries non-empty `init_mac_bytes` whenever `g₀.requireAuthenticatedInitiator = true`. -/
theorem policy_watermark_sliding_window_multiturn_sound_evidence
    {g₀ gFinal : PolicyWatermarkGuard}
    {trace : List (PolicyWatermarkInput × Option PolicyWatermarkEvent)}
    (hTrace : ValidCustodyTrace policyBitmapEvidenceStep g₀ trace gFinal) :
    let approved := watermarkApprovedIntents (traceApprovedOutputs trace)
    g₀.minNonceWatermark ≤ gFinal.minNonceWatermark ∧
    (approved.map (fun p => p.1.nonce)).Nodup ∧
    (∀ p ∈ approved,
      g₀.minNonceWatermark ≤ p.1.nonce ∧
      ¬ nonceConsumedByWatermark g₀ p.1.nonce ∧
      p.2 = toCanonicalSigningBytes p.1 ∧
      (g₀.requireAuthenticatedInitiator = true → p.1.init_mac_bytes ≠ [])) := by
  induction hTrace with
  | nil =>
    exact ⟨Nat.le_refl _, .nil, fun _ hm => by cases hm⟩
  | @consAccepted s s' _ inp ev rest hStep hRest ih =>
    obtain ⟨_, _, hWmStep, hReqEq, hMono, hMark⟩ := watermark_consumed_preserved_and_marks hStep
    obtain ⟨hWmRest, hNdRest, hPropsRest⟩ := ih
    cases ev with
    | epochAdvanced wId nowS =>
      simp only [traceApprovedOutputs_cons_some, watermarkApprovedIntents]
      refine ⟨Nat.le_trans hWmStep hWmRest, hNdRest, ?_⟩
      intro p hp
      obtain ⟨hGe', hNotCons', hBytes', hMac'⟩ := hPropsRest p hp
      exact ⟨Nat.le_trans hWmStep hGe', fun hc => hNotCons' (hMono _ hc),
             hBytes', fun hReq => hMac' (hReqEq.trans hReq)⟩
    | intentApproved tx sb =>
      obtain ⟨hFreshTx, hConsAfter, hSbEq, hMacHead⟩ := hMark tx sb rfl
      have hNotInRest : tx.nonce ∉ (watermarkApprovedIntents (traceApprovedOutputs rest)).map (fun p => p.1.nonce) :=
        watermark_no_approved_if_consumed hRest tx.nonce hConsAfter
      simp only [traceApprovedOutputs_cons_some, watermarkApprovedIntents, List.map_cons]
      refine ⟨Nat.le_trans hWmStep hWmRest,
              .cons (fun x hx hEq => hNotInRest (hEq ▸ hx)) hNdRest, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hTail
      · have hGeWm : s.minNonceWatermark ≤ tx.nonce :=
          Nat.not_lt.mp (fun hLt => hFreshTx (Or.inl hLt))
        exact ⟨hGeWm, hFreshTx, hSbEq, hMacHead⟩
      · obtain ⟨hGe', hNotCons', hBytes', hMac'⟩ := hPropsRest p hTail
        exact ⟨Nat.le_trans hWmStep hGe', fun hc => hNotCons' (hMono _ hc),
               hBytes', fun hReq => hMac' (hReqEq.trans hReq)⟩
  | @consRejected s s' _ inp err rest hStep _ ih =>
    have hSame : s' = s := policyBitmapEvidenceStep_rejected_eq hStep
    subst hSame
    simpa [traceApprovedOutputs_cons_none] using ih

/-- Bounded FIFO ring buffer (`cap` slots) vulnerable to eviction-wrap replay once `cap + 1` distinct nonces pass. -/
def fifoBurnRingStep (cap : Nat) (ring : List Nat) (nonce : Nat) : Option (List Nat) :=
  if nonce ∈ ring then none
  else some ((nonce :: ring).take cap)

/-- Ascending sequence `[start, start + 1, ..., start + count - 1]`. -/
def seqFrom : Nat → Nat → List Nat
  | _, 0 => []
  | s, k + 1 => s :: seqFrom (s + 1) k

private theorem seqFrom_length : ∀ (s k : Nat), (seqFrom s k).length = k
  | _, 0 => rfl
  | s, k + 1 => congrArg Nat.succ (seqFrom_length (s + 1) k)

private theorem zero_not_mem_seqFrom : ∀ (s k : Nat), 0 < s → 0 ∉ seqFrom s k
  | _, 0, _, hm => by cases hm
  | s, k + 1, hs, hm => by
    rcases List.mem_cons.mp hm with h0 | htl
    · omega
    · exact zero_not_mem_seqFrom (s + 1) k (by omega) htl

private theorem take_take_succ : ∀ (m : Nat) (xs : List Nat),
    (xs.take (m + 1)).take m = xs.take m
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => congrArg (x :: ·) (take_take_succ k xs)

private theorem foldl_take_cap_eq_reverse_take (cap : Nat) :
    ∀ (ns acc : List Nat),
      ns.foldl (fun r n => (n :: r).take cap) (acc.take cap) =
        (ns.reverse ++ acc).take cap
  | [], _ => by simp
  | n :: ns, acc => by
    simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    have hStep : (n :: acc.take cap).take cap = (n :: acc).take cap := by
      cases cap with
      | zero => rfl
      | succ m => exact congrArg (n :: ·) (take_take_succ m acc)
    rw [hStep]
    exact foldl_take_cap_eq_reverse_take cap ns (n :: acc)

/-- **`#tooth` 256-Slot FIFO Burn-Ring Eviction Replay (`tooth_fifo_ring_256_eviction_allows_replay_at_257`)**:
    In a 256-slot FIFO burn ring (`MAX_BURNED_INTENT_NONCES = 256`), submitting 257 distinct nonces
    `0, 1, ..., 256` (`seqFrom 0 257`) evicts nonce `0` at transaction `#257`, allowing nonce `0` to be
    replayed and accepted a SECOND time, whereas `policyBitmapEvidenceStep` advances `minNonceWatermark`
    above `0` and deterministically rejects the replay of `0` with `.nonceBelowWatermark`! -/
theorem tooth_fifo_ring_256_eviction_allows_replay_at_257 :
    let nonces257 := seqFrom 0 257
    let ringAfter257 := nonces257.foldl (fun r n => (n :: r).take 256) []
    0 ∈ nonces257 ∧
    nonces257.length = 257 ∧
    0 ∉ ringAfter257 ∧
    (fifoBurnRingStep 256 ringAfter257 0).isSome = true ∧
    (let g₀ : PolicyWatermarkGuard :=
       { chain_id := 1, pinned_suite_tag := 0x0501, window_id := 1,
         epoch_start_secs := 1000, epoch_duration_secs := 3600,
         velocity_window_cap := 1000000, accumulated_spend := 0, per_tx_cap := 1000,
         minNonceWatermark := 1, slidingWindowWidth := 4,
         slidingBitmap := [true, true, true, true],
         pinned_policy_digest := [0xAA], pinned_authority_digest := [0xBB],
         allowed_recipients := [[0x01]], requireAuthenticatedInitiator := true }
     let replay0 : TransactionIntent :=
       { recipient := [0x01], amount_units := 1, window_id := 1,
         policy_digest := [0xAA], authority_digest := [0xBB], nonce := 0,
         init_mac_bytes := [0x01] }
     policyBitmapEvidenceStep g₀ (.evaluateIntent replay0) =
       .rejected g₀ .nonceBelowWatermark) := by
  intro nonces257 ringAfter257
  have hFold : ringAfter257 = (seqFrom 1 256).reverse := by
    change (0 :: seqFrom 1 256).foldl (fun r n => (n :: r).take 256) (([] : List Nat).take 256) = _
    rw [foldl_take_cap_eq_reverse_take 256 (0 :: seqFrom 1 256) [],
        List.append_nil, List.reverse_cons]
    have hRevLen : (seqFrom 1 256).reverse.length = 256 := by
      rw [List.length_reverse, seqFrom_length]
    simp [hRevLen]
  have hNotIn : 0 ∉ ringAfter257 := by
    rw [hFold, List.mem_reverse]
    exact zero_not_mem_seqFrom 1 256 (by decide)
  have hSome : (fifoBurnRingStep 256 ringAfter257 0).isSome = true := by
    unfold fifoBurnRingStep
    simp [hNotIn]
  refine ⟨.head _, seqFrom_length 0 257, hNotIn, hSome, ?_⟩
  decide

/-- Stateless caller-supplied velocity predicate vulnerable to stale/forged `rolling_window_spent = 0`. -/
def statelessCallerVelocityCheck (cap callerSuppliedSpent amount : Nat) : Bool :=
  decide (callerSuppliedSpent + amount ≤ cap)

/-- **`#tooth` Stateless Caller-Spent Velocity Bypass (`tooth_stateless_velocity_caller_spent_bypass`)**:
    When velocity evaluation trusts caller-supplied `rolling_window_spent = 0` instead of authoritative
    custodian state, two `60`-unit requests under `velocity_window_cap = 100` BOTH pass (`60 + 60 = 120 > 100`),
    whereas `StatefulPolicyGuard` approves the first `60` and deterministically rejects the second! -/
theorem tooth_stateless_velocity_caller_spent_bypass :
    statelessCallerVelocityCheck 100 0 60 = true ∧
    statelessCallerVelocityCheck 100 0 60 = true ∧
    60 + 60 > 100 ∧
    (let g₀ : StatefulPolicyGuard :=
       { window_id := 1, velocity_window_cap := 100, accumulated_spend := 0,
         burned_intent_nonces := [], pinned_policy_digest := [0xAA],
         pinned_authority_digest := [0xBB], allowed_recipients := [[0x01]], per_tx_cap := 80 }
     let tx1 : TransactionIntent :=
       { recipient := [0x01], amount_units := 60, window_id := 1,
         policy_digest := [0xAA], authority_digest := [0xBB], nonce := 10 }
     let tx2 : TransactionIntent :=
       { recipient := [0x01], amount_units := 60, window_id := 1,
         policy_digest := [0xAA], authority_digest := [0xBB], nonce := 11 }
     match policyCodecEvidenceStep g₀ tx1 with
     | .accepted g₁ _ =>
       policyCodecEvidenceStep g₁ tx2 = .rejected g₁ .velocityWindowExceeded
     | .rejected _ _ => False) := by
  simp [statelessCallerVelocityCheck, policyCodecEvidenceStep, policyGuardStep]

/-- Inhabitedness witness for `policy_multiturn_velocity_and_intent_binding` approving two distinct
    transactions (`40 + 55 = 95 ≤ 100`) and rejecting a third overflow request (`95 + 20 > 100`). -/
theorem witness_policy_multiturn_inhabited :
    let g₀ : StatefulPolicyGuard :=
      { window_id := 1, velocity_window_cap := 100, accumulated_spend := 0,
         burned_intent_nonces := [], pinned_policy_digest := [0xAA],
         pinned_authority_digest := [0xBB], allowed_recipients := [[0x01]], per_tx_cap := 60 }
    ∃ trace gFinal,
      ValidCustodyTrace policyCodecEvidenceStep g₀ trace gFinal ∧
      (traceApprovedOutputs trace).length = 2 ∧
      gFinal.accumulated_spend = 95 := by
  intro g₀
  let tx1 : TransactionIntent :=
    { recipient := [0x01], amount_units := 40, window_id := 1,
      policy_digest := [0xAA], authority_digest := [0xBB], nonce := 1 }
  let tx2 : TransactionIntent :=
    { recipient := [0x01], amount_units := 55, window_id := 1,
      policy_digest := [0xAA], authority_digest := [0xBB], nonce := 2 }
  let tx3 : TransactionIntent :=
    { recipient := [0x01], amount_units := 20, window_id := 1,
      policy_digest := [0xAA], authority_digest := [0xBB], nonce := 3 }
  let g₁ := { g₀ with accumulated_spend := 40, burned_intent_nonces := [1] }
  let g₂ := { g₀ with accumulated_spend := 95, burned_intent_nonces := [2, 1] }
  have hs1 : policyCodecEvidenceStep g₀ tx1 =
      .accepted g₁ { intent := tx1, canonicalBytes := encodeTransactionIntent tx1 } := by
    simp [policyCodecEvidenceStep, policyGuardStep, g₀, g₁, tx1]
  have hs2 : policyCodecEvidenceStep g₁ tx2 =
      .accepted g₂ { intent := tx2, canonicalBytes := encodeTransactionIntent tx2 } := by
    simp [policyCodecEvidenceStep, policyGuardStep, g₀, g₁, g₂, tx2]
  have hs3 : policyCodecEvidenceStep g₂ tx3 = .rejected g₂ .velocityWindowExceeded := by
    simp [policyCodecEvidenceStep, policyGuardStep, g₀, g₂, tx3]
  refine ⟨[(tx1, some { intent := tx1, canonicalBytes := encodeTransactionIntent tx1 }),
           (tx2, some { intent := tx2, canonicalBytes := encodeTransactionIntent tx2 }),
           (tx3, none)],
          g₂, .consAccepted hs1 (.consAccepted hs2 (.consRejected hs3 (.nil g₂))),
          by rfl, by rfl⟩

/-! ### §3.2 `qsag-addr` — `Bech32m` (`0x2bc830a3`) Polymod & `HybridPinnedEnvelope` Non-Strippability -/

/-- BIP-350 `Bech32m` target constant `0x2bc830a3` and rejected legacy BIP-173 constant `1`. -/
def bech32mConstBv : BitVec 32 := 0x2bc830a3#32
def bech32LegacyConstBv : BitVec 32 := 1#32

/-- Single 5-bit `GF(32)` BCH polymod step over `BitVec 32` matching `bech32_polymod_step` in `qsag-addr`. -/
def bech32StepBv (chk : BitVec 32) (v : BitVec 8) : BitVec 32 :=
  let b0 := ((chk &&& 0x01ffffff#32) <<< 5) ^^^ (v.setWidth 32 &&& 0x1f#32)
  let b1 := if chk.getLsbD 25 then b0 ^^^ 0x3b6a57b2#32 else b0
  let b2 := if chk.getLsbD 26 then b1 ^^^ 0x26508e6d#32 else b1
  let b3 := if chk.getLsbD 27 then b2 ^^^ 0x1ea119fa#32 else b2
  let b4 := if chk.getLsbD 28 then b3 ^^^ 0x3d4233dd#32 else b3
  if chk.getLsbD 29 then b4 ^^^ 0x2a1462b3#32 else b4

/-- Folded `Bech32` / `Bech32m` polymod accumulator starting from an arbitrary 32-bit state. -/
def bech32FoldBv : BitVec 32 → List UInt8 → BitVec 32
  | chk, [] => chk
  | chk, v :: vals => bech32FoldBv (bech32StepBv chk v.toBitVec) vals

/-- Canonical `Bech32m` polymod function (`chk₀ = 1`). -/
@[expose] def bech32Polymod (values : List UInt8) : UInt32 :=
  UInt32.ofBitVec (bech32FoldBv 1#32 values)

/-- BIP-173 / BIP-350 HRP expansion (`[b >> 5 | b ∈ hrp] ++ [0] ++ [b & 31 | b ∈ hrp]`). -/
def bech32HrpExpand (hrpLower : List UInt8) : List UInt8 :=
  (hrpLower.map (fun b => b >>> (5 : UInt8))) ++ [(0 : UInt8)] ++ (hrpLower.map (fun b => b &&& (0x1f : UInt8)))

/-- Extract the six 5-bit `Bech32m` checksum symbols from a 30-bit residual `t : BitVec 32`. -/
def unpackBech32ChecksumWords (t : BitVec 32) : List UInt8 :=
  [UInt8.ofBitVec ((t >>> 25).setWidth 8 &&& 0x1f#8),
   UInt8.ofBitVec ((t >>> 20).setWidth 8 &&& 0x1f#8),
   UInt8.ofBitVec ((t >>> 15).setWidth 8 &&& 0x1f#8),
   UInt8.ofBitVec ((t >>> 10).setWidth 8 &&& 0x1f#8),
   UInt8.ofBitVec ((t >>> 5).setWidth 8 &&& 0x1f#8),
   UInt8.ofBitVec (t.setWidth 8 &&& 0x1f#8)]

/-- Compute the 6-symbol `Bech32m` checksum for `(hrpLower, data5)`. -/
def bech32mCreateChecksum (hrpLower data5 : List UInt8) : List UInt8 :=
  let values := bech32HrpExpand hrpLower ++ data5 ++ [0, 0, 0, 0, 0, 0]
  let pmod := (bech32Polymod values).toBitVec ^^^ bech32mConstBv
  unpackBech32ChecksumWords pmod

/-- Strict `Bech32m` (`0x2bc830a3`) checksum verification predicate. -/
def bech32mVerify (hrpLower payloadWithChecksum : List UInt8) : Bool :=
  decide ((bech32Polymod (bech32HrpExpand hrpLower ++ payloadWithChecksum)).toBitVec = bech32mConstBv)

private theorem cond_xor_distrib (b1 b2 : Bool) (x1 x2 G : BitVec 32) :
    (if (b1 != b2) then (x1 ^^^ x2) ^^^ G else x1 ^^^ x2) =
      (if b1 then x1 ^^^ G else x1) ^^^ (if b2 then x2 ^^^ G else x2) := by
  cases b1 <;> cases b2 <;> dsimp <;>
    (apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor];
     cases x1.getLsbD i <;> cases x2.getLsbD i <;> cases G.getLsbD i <;> rfl)

private theorem bech32StepBv_xor (c1 c2 : BitVec 32) (v1 v2 : BitVec 8) :
    bech32StepBv (c1 ^^^ c2) (v1 ^^^ v2) = bech32StepBv c1 v1 ^^^ bech32StepBv c2 v2 := by
  have hBase :
      (((c1 ^^^ c2) &&& 0x01ffffff#32) <<< 5) ^^^ ((v1 ^^^ v2).setWidth 32 &&& 0x1f#32) =
      ((((c1 &&& 0x01ffffff#32) <<< 5) ^^^ (v1.setWidth 32 &&& 0x1f#32)) ^^^
       (((c2 &&& 0x01ffffff#32) <<< 5) ^^^ (v2.setWidth 32 &&& 0x1f#32))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    by_cases h5 : i < 5
    · simp only [h5, decide_true]
      cases v1.getLsbD i <;> cases v2.getLsbD i <;> cases (0x1f#32).getLsbD i <;> rfl
    · simp only [h5, decide_false]
      cases c1.getLsbD (i - 5) <;> cases c2.getLsbD (i - 5) <;>
        cases (0x01ffffff#32).getLsbD (i - 5) <;>
        cases v1.getLsbD i <;> cases v2.getLsbD i <;> cases (0x1f#32).getLsbD i <;> rfl
  unfold bech32StepBv
  dsimp only
  simp only [BitVec.getLsbD_xor, hBase]
  rw [cond_xor_distrib, cond_xor_distrib, cond_xor_distrib, cond_xor_distrib, cond_xor_distrib]

private theorem bech32FoldBv_append (c : BitVec 32) (xs ys : List UInt8) :
    bech32FoldBv c (xs ++ ys) = bech32FoldBv (bech32FoldBv c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => exact ih (bech32StepBv c x.toBitVec)

private theorem bech32FoldBv_xor_zeros (c : BitVec 32) :
    ∀ (ys : List UInt8),
      bech32FoldBv c ys =
        bech32FoldBv c (List.replicate ys.length 0) ^^^ bech32FoldBv 0#32 ys
  | [] => by
    apply BitVec.eq_of_getLsbD_eq
    intro i _; simp [bech32FoldBv]
  | y :: ys => by
    have hStep : bech32StepBv c y.toBitVec =
        bech32StepBv c (0 : UInt8).toBitVec ^^^ bech32StepBv 0#32 y.toBitVec := by
      have hc : c = c ^^^ 0#32 := by
        apply BitVec.eq_of_getLsbD_eq; intro i _; simp
      have hy : y.toBitVec = (0 : UInt8).toBitVec ^^^ y.toBitVec := by
        apply BitVec.eq_of_getLsbD_eq; intro i _; simp
      conv => lhs; rw [hc, hy]
      exact bech32StepBv_xor c 0#32 (0 : UInt8).toBitVec y.toBitVec
    have hGen : ∀ (a b : BitVec 32) (zs : List UInt8),
        bech32FoldBv (a ^^^ b) zs =
          bech32FoldBv a (List.replicate zs.length 0) ^^^ bech32FoldBv b zs := by
      intro a b zs
      induction zs generalizing a b with
      | nil => rfl
      | cons z zs ih =>
        simp only [List.length_cons, List.replicate_succ, bech32FoldBv]
        have hz : z.toBitVec = (0 : UInt8).toBitVec ^^^ z.toBitVec := by
          apply BitVec.eq_of_getLsbD_eq; intro i _; simp
        conv => lhs; rw [hz]
        rw [bech32StepBv_xor, ih]
    simp only [List.length_cons, List.replicate_succ, bech32FoldBv, hStep]
    exact hGen _ _ ys

private theorem bech32StepBv_high_bits_zero (c : BitVec 32) (v : BitVec 8) :
    (bech32StepBv c v).getLsbD 30 = false ∧ (bech32StepBv c v).getLsbD 31 = false := by
  have hCondZero : ∀ (cond : Bool) (x G : BitVec 32) (k : Nat),
      x.getLsbD k = false → G.getLsbD k = false →
      (if cond then x ^^^ G else x).getLsbD k = false := by
    intro cond x G k hx hG
    cases cond <;> simp [BitVec.getLsbD_xor, hx, hG]
  unfold bech32StepBv
  dsimp only
  constructor
  · repeat' apply hCondZero
    · simp
    all_goals decide
  · repeat' apply hCondZero
    · simp
    all_goals decide

private theorem bech32FoldBv_high_bits_zero :
    ∀ (c : BitVec 32) (vals : List UInt8),
      c.getLsbD 30 = false → c.getLsbD 31 = false →
      (bech32FoldBv c vals).getLsbD 30 = false ∧ (bech32FoldBv c vals).getLsbD 31 = false
  | _, [], h30, h31 => ⟨h30, h31⟩
  | c, v :: vals, _, _ =>
    let ⟨n30, n31⟩ := bech32StepBv_high_bits_zero c v.toBitVec
    bech32FoldBv_high_bits_zero _ vals n30 n31

private theorem bech32StepBv_no_top (c : BitVec 32) (v : BitVec 8)
    (h25 : c.getLsbD 25 = false) (h26 : c.getLsbD 26 = false)
    (h27 : c.getLsbD 27 = false) (h28 : c.getLsbD 28 = false)
    (h29 : c.getLsbD 29 = false) :
    ∀ i < 32,
      (bech32StepBv c v).getLsbD i =
        if i < 5 then v.getLsbD i
        else if i < 30 then c.getLsbD (i - 5)
        else false := by
  intro i hi
  unfold bech32StepBv
  simp only [h25, h26, h27, h28, h29, Bool.false_eq_true, ↓reduceIte,
    BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  if h5 : i < 5 then
    have hm5 : (0x1f#32).getLsbD i = true := by
      match i with | 0 | 1 | 2 | 3 | 4 => decide
    simp [h5, hm5]
  else if h30 : i < 30 then
    have hv0 : (0x1f#32).getLsbD i = false := by
      rcases (show i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨
                   i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨
                   i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hcMask : (0x01ffffff#32).getLsbD (i - 5) = true := by
      rcases (show i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨
                   i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨
                   i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [h5, h30, hv0, hcMask]
  else
    rcases (show i = 30 ∨ i = 31 by omega) with rfl | rfl <;> simp

private theorem bech32FoldBv_six_words (w5 w4 w3 w2 w1 w0 : UInt8) :
    ∀ i < 32,
      (bech32FoldBv 0#32 [w5, w4, w3, w2, w1, w0]).getLsbD i =
        if i < 5 then w0.toBitVec.getLsbD i
        else if i < 10 then w1.toBitVec.getLsbD (i - 5)
        else if i < 15 then w2.toBitVec.getLsbD (i - 10)
        else if i < 20 then w3.toBitVec.getLsbD (i - 15)
        else if i < 25 then w4.toBitVec.getLsbD (i - 20)
        else if i < 30 then w5.toBitVec.getLsbD (i - 25)
        else false := by
  let s1 := bech32StepBv 0#32 w5.toBitVec
  have hs1 : ∀ i < 32, s1.getLsbD i = if i < 5 then w5.toBitVec.getLsbD i else false := by
    intro i hi
    rw [bech32StepBv_no_top 0#32 w5.toBitVec rfl rfl rfl rfl rfl i hi]
    split <;> simp
  let s2 := bech32StepBv s1 w4.toBitVec
  have hs2 : ∀ i < 32, s2.getLsbD i =
      if i < 5 then w4.toBitVec.getLsbD i
      else if i < 10 then w5.toBitVec.getLsbD (i - 5) else false := by
    intro i hi
    rw [bech32StepBv_no_top s1 w4.toBitVec
      (by rw [hs1 25 (by decide)]; simp) (by rw [hs1 26 (by decide)]; simp)
      (by rw [hs1 27 (by decide)]; simp) (by rw [hs1 28 (by decide)]; simp)
      (by rw [hs1 29 (by decide)]; simp) i hi]
    if h5 : i < 5 then simp [h5]
    else if h30 : i < 30 then
      simp only [h5, h30, ↓reduceIte, hs1 (i - 5) (by omega)]
      if h10 : i < 10 then
        have hLt5 : i - 5 < 5 := by omega
        simp [h10, hLt5]
      else
        have hNot5 : ¬ (i - 5 < 5) := by omega
        simp [h10, hNot5]
    else
      have hNot10 : ¬ (i < 10) := by omega
      simp [h5, h30, hNot10]
  let s3 := bech32StepBv s2 w3.toBitVec
  have hs3 : ∀ i < 32, s3.getLsbD i =
      if i < 5 then w3.toBitVec.getLsbD i
      else if i < 10 then w4.toBitVec.getLsbD (i - 5)
      else if i < 15 then w5.toBitVec.getLsbD (i - 10) else false := by
    intro i hi
    rw [bech32StepBv_no_top s2 w3.toBitVec
      (by rw [hs2 25 (by decide)]; simp) (by rw [hs2 26 (by decide)]; simp)
      (by rw [hs2 27 (by decide)]; simp) (by rw [hs2 28 (by decide)]; simp)
      (by rw [hs2 29 (by decide)]; simp) i hi]
    if h5 : i < 5 then simp [h5]
    else if h10 : i < 10 then
      have h30 : i < 30 := by omega
      have hSub5 : i - 5 < 5 := by omega
      simp [h5, h10, h30, hs2 (i - 5) (by omega), hSub5]
    else if h15 : i < 15 then
      have h30 : i < 30 := by omega
      have hNot5 : ¬ (i - 5 < 5) := by omega
      have hSub10 : i - 5 < 10 := by omega
      have hArith : i - 5 - 5 = i - 10 := by omega
      simp [h5, h10, h15, h30, hs2 (i - 5) (by omega), hNot5, hSub10, hArith]
    else
      if h30 : i < 30 then
        have hNot5 : ¬ (i - 5 < 5) := by omega
        have hNot10 : ¬ (i - 5 < 10) := by omega
        simp [h5, h10, h15, h30, hs2 (i - 5) (by omega), hNot5, hNot10]
      else
        simp [h5, h10, h15, h30]
  let s4 := bech32StepBv s3 w2.toBitVec
  have hs4 : ∀ i < 32, s4.getLsbD i =
      if i < 5 then w2.toBitVec.getLsbD i
      else if i < 10 then w3.toBitVec.getLsbD (i - 5)
      else if i < 15 then w4.toBitVec.getLsbD (i - 10)
      else if i < 20 then w5.toBitVec.getLsbD (i - 15) else false := by
    intro i hi
    rw [bech32StepBv_no_top s3 w2.toBitVec
      (by rw [hs3 25 (by decide)]; simp) (by rw [hs3 26 (by decide)]; simp)
      (by rw [hs3 27 (by decide)]; simp) (by rw [hs3 28 (by decide)]; simp)
      (by rw [hs3 29 (by decide)]; simp) i hi]
    if h5 : i < 5 then simp [h5]
    else if h10 : i < 10 then
      simp [h5, h10, show i < 30 by omega, hs3 (i - 5) (by omega), show i - 5 < 5 by omega]
    else if h15 : i < 15 then
      simp [h5, h10, h15, show i < 30 by omega, hs3 (i - 5) (by omega),
            show ¬(i - 5 < 5) by omega, show i - 5 < 10 by omega, show i - 5 - 5 = i - 10 by omega]
    else if h20 : i < 20 then
      simp [h5, h10, h15, h20, show i < 30 by omega, hs3 (i - 5) (by omega),
            show ¬(i - 5 < 5) by omega, show ¬(i - 5 < 10) by omega,
            show i - 5 < 15 by omega, show i - 5 - 10 = i - 15 by omega]
    else if h30 : i < 30 then
      simp [h5, h10, h15, h20, h30, hs3 (i - 5) (by omega),
            show ¬(i - 5 < 5) by omega, show ¬(i - 5 < 10) by omega, show ¬(i - 5 < 15) by omega]
    else simp [h5, h10, h15, h20, h30]
  let s5 := bech32StepBv s4 w1.toBitVec
  have hs5 : ∀ i < 32, s5.getLsbD i =
      if i < 5 then w1.toBitVec.getLsbD i
      else if i < 10 then w2.toBitVec.getLsbD (i - 5)
      else if i < 15 then w3.toBitVec.getLsbD (i - 10)
      else if i < 20 then w4.toBitVec.getLsbD (i - 15)
      else if i < 25 then w5.toBitVec.getLsbD (i - 20) else false := by
    intro i hi
    rw [bech32StepBv_no_top s4 w1.toBitVec
      (by rw [hs4 25 (by decide)]; simp) (by rw [hs4 26 (by decide)]; simp)
      (by rw [hs4 27 (by decide)]; simp) (by rw [hs4 28 (by decide)]; simp)
      (by rw [hs4 29 (by decide)]; simp) i hi]
    if h5 : i < 5 then simp [h5]
    else if h10 : i < 10 then
      simp [h5, h10, show i < 30 by omega, hs4 (i - 5) (by omega), show i - 5 < 5 by omega]
    else if h15 : i < 15 then
      simp [h5, h10, h15, show i < 30 by omega, hs4 (i - 5) (by omega),
            show ¬(i - 5 < 5) by omega, show i - 5 < 10 by omega, show i - 5 - 5 = i - 10 by omega]
    else if h20 : i < 20 then
      simp [h5, h10, h15, h20, show i < 30 by omega, hs4 (i - 5) (by omega),
            show ¬(i - 5 < 5) by omega, show ¬(i - 5 < 10) by omega,
            show i - 5 < 15 by omega, show i - 5 - 10 = i - 15 by omega]
    else if h25 : i < 25 then
      simp [h5, h10, h15, h20, h25, show i < 30 by omega, hs4 (i - 5) (by omega),
            show ¬(i - 5 < 5) by omega, show ¬(i - 5 < 10) by omega,
            show ¬(i - 5 < 15) by omega, show i - 5 < 20 by omega, show i - 5 - 15 = i - 20 by omega]
    else if h30 : i < 30 then
      simp [h5, h10, h15, h20, h25, h30, hs4 (i - 5) (by omega),
            show ¬(i - 5 < 5) by omega, show ¬(i - 5 < 10) by omega,
            show ¬(i - 5 < 15) by omega, show ¬(i - 5 < 20) by omega]
    else simp [h5, h10, h15, h20, h25, h30]
  intro i hi
  change (bech32StepBv s5 w0.toBitVec).getLsbD i = _
  rw [bech32StepBv_no_top s5 w0.toBitVec
    (by rw [hs5 25 (by decide)]; simp) (by rw [hs5 26 (by decide)]; simp)
    (by rw [hs5 27 (by decide)]; simp) (by rw [hs5 28 (by decide)]; simp)
    (by rw [hs5 29 (by decide)]; simp) i hi]
  if h5 : i < 5 then simp [h5]
  else if h10 : i < 10 then
    simp [h5, h10, show i < 30 by omega, hs5 (i - 5) (by omega), show i - 5 < 5 by omega]
  else if h15 : i < 15 then
    simp [h5, h10, h15, show i < 30 by omega, hs5 (i - 5) (by omega),
          show ¬(i - 5 < 5) by omega, show i - 5 < 10 by omega, show i - 5 - 5 = i - 10 by omega]
  else if h20 : i < 20 then
    simp [h5, h10, h15, h20, show i < 30 by omega, hs5 (i - 5) (by omega),
          show ¬(i - 5 < 5) by omega, show ¬(i - 5 < 10) by omega,
          show i - 5 < 15 by omega, show i - 5 - 10 = i - 15 by omega]
  else if h25 : i < 25 then
    simp [h5, h10, h15, h20, h25, show i < 30 by omega, hs5 (i - 5) (by omega),
          show ¬(i - 5 < 5) by omega, show ¬(i - 5 < 10) by omega,
          show ¬(i - 5 < 15) by omega, show i - 5 < 20 by omega, show i - 5 - 15 = i - 20 by omega]
  else if h30 : i < 30 then
    simp [h5, h10, h15, h20, h25, h30, hs5 (i - 5) (by omega),
          show ¬(i - 5 < 5) by omega, show ¬(i - 5 < 10) by omega,
          show ¬(i - 5 < 15) by omega, show ¬(i - 5 < 20) by omega,
          show i - 5 < 25 by omega, show i - 5 - 20 = i - 25 by omega]
  else simp [h5, h10, h15, h20, h25, h30]

private theorem bech32FoldBv_unpack_id (t : BitVec 32)
    (h30 : t.getLsbD 30 = false) (h31 : t.getLsbD 31 = false) :
    bech32FoldBv 0#32 (unpackBech32ChecksumWords t) = t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold unpackBech32ChecksumWords
  rw [bech32FoldBv_six_words _ _ _ _ _ _ i hi]
  have hMask5 : ∀ k < 5, (0x1f#8).getLsbD k = true := by
    intro k hk; match k with | 0 | 1 | 2 | 3 | 4 => decide
  if h5 : i < 5 then
    simp [h5, show i < 8 by omega, hMask5 i h5]
  else if h10 : i < 10 then
    simp [h5, h10, BitVec.getLsbD_ushiftRight, show i - 5 < 8 by omega,
          hMask5 (i - 5) (by omega), show 5 + (i - 5) = i by omega]
  else if h15 : i < 15 then
    simp [h5, h10, h15, BitVec.getLsbD_ushiftRight, show i - 10 < 8 by omega,
          hMask5 (i - 10) (by omega), show 10 + (i - 10) = i by omega]
  else if h20 : i < 20 then
    simp [h5, h10, h15, h20, BitVec.getLsbD_ushiftRight, show i - 15 < 8 by omega,
          hMask5 (i - 15) (by omega), show 15 + (i - 15) = i by omega]
  else if h25 : i < 25 then
    simp [h5, h10, h15, h20, h25, BitVec.getLsbD_ushiftRight, show i - 20 < 8 by omega,
          hMask5 (i - 20) (by omega), show 20 + (i - 20) = i by omega]
  else if h30i : i < 30 then
    simp [h5, h10, h15, h20, h25, h30i, BitVec.getLsbD_ushiftRight, show i - 25 < 8 by omega,
          hMask5 (i - 25) (by omega), show 25 + (i - 25) = i by omega]
  else
    rcases (show i = 30 ∨ i = 31 by omega) with rfl | rfl
    · simp only; exact h30.symm
    · simp only; exact h31.symm

/-- **Universal `Bech32m` (`0x2bc830a3`) Roundtrip, BIP-173 Rejection & BIP-350 Test Vector
    (`bech32m_encode_verify_roundtrip`)**:
    For EVERY `hrpLower` and EVERY `data5 : List UInt8`:
    1. `bech32mVerify hrpLower (data5 ++ bech32mCreateChecksum hrpLower data5) = true`
    2. Legacy BIP-173 (`const = 1`) residual never collides with `Bech32m` (`0x2bc830a3 ≠ 1`)
    3. Official BIP-350 test vector `"a1lqfn3a"` (`hrp = [97]`, checksum `[31, 0, 9, 19, 17, 29]`) passes! -/
theorem bech32m_encode_verify_roundtrip (hrpLower data5 : List UInt8) :
    let cs := bech32mCreateChecksum hrpLower data5
    bech32mVerify hrpLower (data5 ++ cs) = true ∧
    (bech32Polymod (bech32HrpExpand hrpLower ++ (data5 ++ cs))).toBitVec ≠ bech32LegacyConstBv ∧
    bech32mVerify [97] [31, 0, 9, 19, 17, 29] = true := by
  intro cs
  let pfx := bech32HrpExpand hrpLower ++ data5
  let raw := bech32FoldBv 1#32 (pfx ++ [0, 0, 0, 0, 0, 0])
  have hRawHi := bech32FoldBv_high_bits_zero 1#32 (pfx ++ [0, 0, 0, 0, 0, 0]) (by decide) (by decide)
  have hTarget30 : (raw ^^^ bech32mConstBv).getLsbD 30 = false := by
    rw [BitVec.getLsbD_xor, hRawHi.1]
    decide
  have hTarget31 : (raw ^^^ bech32mConstBv).getLsbD 31 = false := by
    rw [BitVec.getLsbD_xor, hRawHi.2]
    decide
  have hFoldEq : bech32FoldBv 1#32 (bech32HrpExpand hrpLower ++ (data5 ++ cs)) = bech32mConstBv := by
    have hAssoc : bech32HrpExpand hrpLower ++ (data5 ++ cs) = pfx ++ cs := by
      simp [pfx, List.append_assoc]
    rw [hAssoc, bech32FoldBv_append]
    have hCsLen : cs.length = 6 := by simp [cs, bech32mCreateChecksum, unpackBech32ChecksumWords]
    rw [bech32FoldBv_xor_zeros (bech32FoldBv 1#32 pfx) cs, hCsLen]
    have hRep6 : List.replicate 6 (0 : UInt8) = [0, 0, 0, 0, 0, 0] := rfl
    rw [hRep6, ← bech32FoldBv_append]
    change raw ^^^ bech32FoldBv 0#32 (unpackBech32ChecksumWords (raw ^^^ bech32mConstBv)) = bech32mConstBv
    rw [bech32FoldBv_unpack_id (raw ^^^ bech32mConstBv) hTarget30 hTarget31]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor]
    cases raw.getLsbD i <;> cases bech32mConstBv.getLsbD i <;> rfl
  have hVer : bech32mVerify hrpLower (data5 ++ cs) = true := by
    unfold bech32mVerify bech32Polymod
    simp [hFoldEq]
  have hNotLegacy : (bech32Polymod (bech32HrpExpand hrpLower ++ (data5 ++ cs))).toBitVec ≠ bech32LegacyConstBv := by
    unfold bech32Polymod
    rw [UInt32.toBitVec_ofBitVec, hFoldEq]
    decide
  exact ⟨hVer, hNotLegacy, by decide⟩

/-- Role tag separating classical and post-quantum signing transcripts inside `HybridPinnedEnvelope`. -/
inductive HybridRole where
  | classical
  | postQuantum
  deriving DecidableEq, Repr

def hybridRoleByte : HybridRole → UInt8
  | .classical => 0x01
  | .postQuantum => 0x02

/-- Production conjunctive hybrid `WitnessSuiteTag` constants (`crates/qsag-addr/src/lib.rs:61-62`). -/
def suiteHybridSecp256k1MlDsa44 : Nat := 0x0501
def suiteHybridEd25519MlDsa65 : Nat := 0x0502

/-- Production `HybridComponentAlgorithm` `#[repr(u16)]` discriminants (`crates/qsag-addr/src/lib.rs:335-344`). -/
def algClassicalSecp256k1 : Nat := 0x0001
def algClassicalEd25519 : Nat := 0x0002
def algPqMlDsa44 : Nat := 0x0101
def algPqMlDsa65 : Nat := 0x0102

/-- Exact production `HybridSuiteSpec::for_suite` mapping (`0x0501 ↔ (0x0001, 0x0101)`, `0x0502 ↔ (0x0002, 0x0102)`). -/
def validHybridSuiteTriplet (suiteTag classicalAlg pqAlg : Nat) : Bool :=
  decide ((suiteTag = suiteHybridSecp256k1MlDsa44 ∧
           classicalAlg = algClassicalSecp256k1 ∧
           pqAlg = algPqMlDsa44) ∨
          (suiteTag = suiteHybridEd25519MlDsa65 ∧
           classicalAlg = algClassicalEd25519 ∧
           pqAlg = algPqMlDsa65))

/-- Exact ASCII domain prefix `"QSAG.HYBRID.V2"` (`14` bytes). -/
def hybridPinnedMagic : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x48, 0x59, 0x42, 0x52, 0x49, 0x44, 0x2E, 0x56, 0x32]

/-- Exact ASCII domain tag `"QSAG.HYBRID.PK_CLASSICAL.V2"` (`27` bytes). -/
def hybridPkClassicalDomain : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x48, 0x59, 0x42, 0x52, 0x49, 0x44, 0x2E,
   0x50, 0x4B, 0x5F, 0x43, 0x4C, 0x41, 0x53, 0x53, 0x49, 0x43, 0x41, 0x4C, 0x2E, 0x56, 0x32]

/-- Exact ASCII domain tag `"QSAG.HYBRID.PK_PQ.V2"` (`20` bytes). -/
def hybridPkPqDomain : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x48, 0x59, 0x42, 0x52, 0x49, 0x44, 0x2E,
   0x50, 0x4B, 0x5F, 0x50, 0x51, 0x2E, 0x56, 0x32]

/-- Exact ASCII domain tag `"QSAG.HYBRID.ID_COMMIT.V2"` (`24` bytes). -/
def hybridIdCommitDomain : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x48, 0x59, 0x42, 0x52, 0x49, 0x44, 0x2E,
   0x49, 0x44, 0x5F, 0x43, 0x4F, 0x4D, 0x4D, 0x49, 0x54, 0x2E, 0x56, 0x32]

/-- Domain-separated sponge family `(customization : List UInt8) → (input : List UInt8) → List UInt8`,
    instantiated directly in production by `cshake256Bytes`. -/
abbrev DomainHash := List UInt8 → List UInt8 → List UInt8

/-- Constructive same-domain collision witness on `H_dom`. -/
structure DomainHashCollisionWitness (H_dom : DomainHash) where
  domain : List UInt8
  m1 : List UInt8
  m2 : List UInt8
  ne : m1 ≠ m2
  eq : H_dom domain m1 = H_dom domain m2
  deriving Repr

/-- Exact `HybridPinnedEnvelope::hash_classical_pk`:
    `cshake256_framed_32(b"QSAG.HYBRID.PK_CLASSICAL.V2", &[&suite_be2, &classical_alg_be2, pk_classical])`. -/
def hashHybridClassicalPk (H_dom : DomainHash) (suiteTag classicalAlg : Nat)
    (pkClassical : List UInt8) : List UInt8 :=
  H_dom hybridPkClassicalDomain (encodeFramedU64Le [be 2 suiteTag, be 2 classicalAlg, pkClassical])

/-- Exact `HybridPinnedEnvelope::hash_pq_pk`:
    `cshake256_framed_32(b"QSAG.HYBRID.PK_PQ.V2", &[&suite_be2, &pq_alg_be2, pk_pq])`. -/
def hashHybridPqPk (H_dom : DomainHash) (suiteTag pqAlg : Nat)
    (pkPq : List UInt8) : List UInt8 :=
  H_dom hybridPkPqDomain (encodeFramedU64Le [be 2 suiteTag, be 2 pqAlg, pkPq])

/-- Exact `HybridPinnedEnvelope::compute_id_commit`:
    `cshake256_framed_32(b"QSAG.HYBRID.ID_COMMIT.V2", &[&suite_be2, &c_be2, &pq_be2, pk_c_digest, pk_pq_digest])`. -/
def computeAddrHybridIdCommit (H_dom : DomainHash) (suiteTag classicalAlg pqAlg : Nat)
    (pkClassicalDigest pkPqDigest : List UInt8) : List UInt8 :=
  H_dom hybridIdCommitDomain
    (encodeFramedU64Le [be 2 suiteTag, be 2 classicalAlg, be 2 pqAlg,
                        pkClassicalDigest, pkPqDigest])

/-- Exact `HybridPinnedEnvelope::signing_transcript` (`crates/qsag-addr/src/lib.rs:566-586`):
    `"QSAG.HYBRID.V2" || role (1) || suite (2, BE) || classical_alg (2, BE) || pq_alg (2, BE)`
    `|| id_commit (32) || pk_classical_digest (32) || pk_pq_digest (32) || len(msg) (8, BE) || msg`. -/
def encodeHybridRolePayload (role : HybridRole) (suiteTag classicalAlg pqAlg : Nat)
    (idCommit pkClassicalDigest pkPqDigest msg : List UInt8) : List UInt8 :=
  hybridPinnedMagic ++
  ([hybridRoleByte role] ++
  (be 2 suiteTag ++
  (be 2 classicalAlg ++
  (be 2 pqAlg ++
  (idCommit ++
  (pkClassicalDigest ++
  (pkPqDigest ++
  (be 8 msg.length ++ msg))))))))

theorem encodeHybridRolePayload_injective
    {r₁ r₂ : HybridRole} {s₁ s₂ c₁ c₂ p₁ p₂ : Nat}
    {id₁ id₂ pkCD₁ pkCD₂ pkPD₁ pkPD₂ m₁ m₂ : List UInt8}
    (hs₁ : s₁ < 256 ^ 2) (hs₂ : s₂ < 256 ^ 2)
    (hc₁ : c₁ < 256 ^ 2) (hc₂ : c₂ < 256 ^ 2)
    (hp₁ : p₁ < 256 ^ 2) (hp₂ : p₂ < 256 ^ 2)
    (hid₁ : id₁.length = 32) (hid₂ : id₂.length = 32)
    (hcd₁ : pkCD₁.length = 32) (hcd₂ : pkCD₂.length = 32)
    (hpd₁ : pkPD₁.length = 32) (hpd₂ : pkPD₂.length = 32)
    (hEq : encodeHybridRolePayload r₁ s₁ c₁ p₁ id₁ pkCD₁ pkPD₁ m₁ =
           encodeHybridRolePayload r₂ s₂ c₂ p₂ id₂ pkCD₂ pkPD₂ m₂) :
    r₁ = r₂ ∧ s₁ = s₂ ∧ c₁ = c₂ ∧ p₁ = p₂ ∧
    id₁ = id₂ ∧ pkCD₁ = pkCD₂ ∧ pkPD₁ = pkPD₂ ∧ m₁ = m₂ := by
  unfold encodeHybridRolePayload at hEq
  obtain ⟨_, t1⟩ := List.append_inj hEq rfl
  obtain ⟨hRole, t2⟩ := List.append_inj t1 rfl
  obtain ⟨hS, t3⟩ := List.append_inj t2 (by simp [length_be])
  obtain ⟨hC, t4⟩ := List.append_inj t3 (by simp [length_be])
  obtain ⟨hP, t5⟩ := List.append_inj t4 (by simp [length_be])
  obtain ⟨hId, t6⟩ := List.append_inj t5 (hid₁.trans hid₂.symm)
  obtain ⟨hCD, t7⟩ := List.append_inj t6 (hcd₁.trans hcd₂.symm)
  obtain ⟨hPD, t8⟩ := List.append_inj t7 (hpd₁.trans hpd₂.symm)
  obtain ⟨_, hM⟩ := List.append_inj t8 (by simp [length_be])
  have hr : r₁ = r₂ := by
    cases r₁ <;> cases r₂ <;> simp [hybridRoleByte] at hRole <;> rfl
  exact ⟨hr, be_injective hs₁ hs₂ hS, be_injective hc₁ hc₂ hC, be_injective hp₁ hp₂ hP,
         hId, hCD, hPD, hM⟩

/-- Non-malleable conjunctive hybrid signature envelope byte-aligned with `HybridPinnedEnvelope`
    in `crates/qsag-addr/src/lib.rs:504-515`. -/
structure HybridPinnedEnvelope where
  suiteTag : Nat
  classicalAlg : Nat
  pqAlg : Nat
  idCommit : List UInt8
  pkClassicalDigest : List UInt8
  pkPqDigest : List UInt8
  pkClassical : List UInt8
  pkPq : List UInt8
  sigClassical : List UInt8
  sigPq : List UInt8
  deriving DecidableEq, Repr

/-- Conjunctive hybrid envelope verifier pinning `validHybridSuiteTriplet` (`0x0501` / `0x0502`),
    32-byte `pkClassicalDigest`, `pkPqDigest`, `idCommit` preimages (`u64 LE` framed), and both
    role-separated `"QSAG.HYBRID.V2"` signatures. -/
@[expose] def verifyHybridPinnedEnvelope (H_dom : DomainHash)
    (verifyClassical verifyPq : List UInt8 → List UInt8 → List UInt8 → Bool)
    (expectedSuite expectedClassicalAlg expectedPqAlg : Nat)
    (expectedIdCommit msg : List UInt8)
    (env : HybridPinnedEnvelope) : Bool :=
  let suiteValid := validHybridSuiteTriplet env.suiteTag env.classicalAlg env.pqAlg
  let widthsOk :=
    decide (env.idCommit.length = 32 ∧
            env.pkClassicalDigest.length = 32 ∧
            env.pkPqDigest.length = 32 ∧
            env.pkClassical.length < 256 ^ 8 ∧
            env.pkPq.length < 256 ^ 8)
  let tagsMatch :=
    decide (env.suiteTag = expectedSuite ∧
            env.classicalAlg = expectedClassicalAlg ∧
            env.pqAlg = expectedPqAlg ∧
            env.idCommit = expectedIdCommit)
  let recomputedPkCD :=
    hashHybridClassicalPk H_dom env.suiteTag env.classicalAlg env.pkClassical
  let recomputedPkPD :=
    hashHybridPqPk H_dom env.suiteTag env.pqAlg env.pkPq
  let recomputedId :=
    computeAddrHybridIdCommit H_dom env.suiteTag env.classicalAlg env.pqAlg
      env.pkClassicalDigest env.pkPqDigest
  let digestsMatch :=
    decide (recomputedPkCD = env.pkClassicalDigest ∧
            recomputedPkPD = env.pkPqDigest ∧
            recomputedId = expectedIdCommit)
  let cTranscript :=
    encodeHybridRolePayload .classical env.suiteTag env.classicalAlg env.pqAlg
      env.idCommit env.pkClassicalDigest env.pkPqDigest msg
  let pqTranscript :=
    encodeHybridRolePayload .postQuantum env.suiteTag env.classicalAlg env.pqAlg
      env.idCommit env.pkClassicalDigest env.pkPqDigest msg
  suiteValid && widthsOk && tagsMatch && digestsMatch &&
  verifyClassical env.pkClassical cTranscript env.sigClassical &&
  verifyPq env.pkPq pqTranscript env.sigPq

/-- Constructive conjunctive EUF-CMA forgery witness on the exact pinned `(pkClassical, pkPq)` pair. -/
structure HybridCombinedForgeryWitness
    (verifyClassical verifyPq : List UInt8 → List UInt8 → List UInt8 → Bool)
    (pinnedPkC pinnedPkPq : List UInt8)
    (signedClassicalPayloads signedPqPayloads : List (List UInt8)) where
  classicalPayload : List UInt8
  classicalSig : List UInt8
  classical_fresh : classicalPayload ∉ signedClassicalPayloads
  classical_valid : verifyClassical pinnedPkC classicalPayload classicalSig = true
  pqPayload : List UInt8
  pqSig : List UInt8
  pq_fresh : pqPayload ∉ signedPqPayloads
  pq_valid : verifyPq pinnedPkPq pqPayload pqSig = true
  role_disjoint : classicalPayload ≠ pqPayload

private theorem hybridSuite_u16_bounds {s c p : Nat}
    (h : validHybridSuiteTriplet s c p = true) :
    s < 256 ^ 2 ∧ c < 256 ^ 2 ∧ p < 256 ^ 2 := by
  unfold validHybridSuiteTriplet suiteHybridSecp256k1MlDsa44 suiteHybridEd25519MlDsa65
    algClassicalSecp256k1 algClassicalEd25519 algPqMlDsa44 algPqMlDsa65 at h
  rcases of_decide_eq_true h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide

/-- **Hybrid Non-Strippability & Conjunctive EUF-CMA Reduction
    (`hybrid_pinned_non_strippable_and_combined_euf_cma`)**:
    Suppose an identity pins `pinnedId = computeAddrHybridIdCommit H_dom suite cAlg pqAlg pkCD pkPD`
    (with `pkCD = hashHybridClassicalPk H_dom suite cAlg pkC`, `pkPD = hashHybridPqPk H_dom suite pqAlg pkPq`,
    `0x0501` or `0x0502`), and honest signers have only signed messages `m ∈ signedMsgs` under `(pkC, pkPq)`.
    Any accepted `HybridPinnedEnvelope` on a fresh message `msg ∉ signedMsgs` (or with substituted keys)
    constructively (no choice operator) yields EITHER:
    1. A same-domain `DomainHashCollisionWitness H_dom` on `"QSAG.HYBRID.ID_COMMIT.V2"`,
       `"QSAG.HYBRID.PK_CLASSICAL.V2"`, or `"QSAG.HYBRID.PK_PQ.V2"` (blocking PQ/classical key stripping!), OR
    2. A **simultaneous** `HybridCombinedForgeryWitness` breaking **BOTH** `verifyClassical` on `pkC`
       AND `verifyPq` on `pkPq` with disjoint `"QSAG.HYBRID.V2"` role-separated transcripts! -/
def hybrid_pinned_non_strippable_and_combined_euf_cma
    (H_dom : DomainHash)
    (verifyClassical verifyPq : List UInt8 → List UInt8 → List UInt8 → Bool)
    (suite cAlg pqAlg : Nat) (pkC pkPq : List UInt8)
    (signedMsgs : List (List UInt8))
    (msg : List UInt8) (env : HybridPinnedEnvelope)
    (hOut32 : ∀ dom x, (H_dom dom x).length = 32)
    (hPkCBound : pkC.length < 256 ^ 8)
    (hPkPqBound : pkPq.length < 256 ^ 8)
    (hFreshOrSubst : msg ∉ signedMsgs ∨ env.pkClassical ≠ pkC ∨ env.pkPq ≠ pkPq)
    (hAccept :
      let pkCD := hashHybridClassicalPk H_dom suite cAlg pkC
      let pkPD := hashHybridPqPk H_dom suite pqAlg pkPq
      let pinnedId := computeAddrHybridIdCommit H_dom suite cAlg pqAlg pkCD pkPD
      verifyHybridPinnedEnvelope H_dom verifyClassical verifyPq
        suite cAlg pqAlg pinnedId msg env = true) :
    let pkCD := hashHybridClassicalPk H_dom suite cAlg pkC
    let pkPD := hashHybridPqPk H_dom suite pqAlg pkPq
    let pinnedId := computeAddrHybridIdCommit H_dom suite cAlg pqAlg pkCD pkPD
    let honestC := signedMsgs.map (fun m =>
      encodeHybridRolePayload .classical suite cAlg pqAlg pinnedId pkCD pkPD m)
    let honestPq := signedMsgs.map (fun m =>
      encodeHybridRolePayload .postQuantum suite cAlg pqAlg pinnedId pkCD pkPD m)
    PSum (DomainHashCollisionWitness H_dom)
         (HybridCombinedForgeryWitness verifyClassical verifyPq pkC pkPq honestC honestPq) :=
  let pkCD := hashHybridClassicalPk H_dom suite cAlg pkC
  let pkPD := hashHybridPqPk H_dom suite pqAlg pkPq
  let pinnedId := computeAddrHybridIdCommit H_dom suite cAlg pqAlg pkCD pkPD
  have hUnpack :
      validHybridSuiteTriplet env.suiteTag env.classicalAlg env.pqAlg = true ∧
      (env.idCommit.length = 32 ∧ env.pkClassicalDigest.length = 32 ∧
       env.pkPqDigest.length = 32 ∧ env.pkClassical.length < 256 ^ 8 ∧
       env.pkPq.length < 256 ^ 8) ∧
      (env.suiteTag = suite ∧ env.classicalAlg = cAlg ∧ env.pqAlg = pqAlg ∧ env.idCommit = pinnedId) ∧
      (hashHybridClassicalPk H_dom env.suiteTag env.classicalAlg env.pkClassical = env.pkClassicalDigest ∧
       hashHybridPqPk H_dom env.suiteTag env.pqAlg env.pkPq = env.pkPqDigest ∧
       computeAddrHybridIdCommit H_dom env.suiteTag env.classicalAlg env.pqAlg
         env.pkClassicalDigest env.pkPqDigest = pinnedId) ∧
      verifyClassical env.pkClassical
        (encodeHybridRolePayload .classical env.suiteTag env.classicalAlg env.pqAlg
          env.idCommit env.pkClassicalDigest env.pkPqDigest msg) env.sigClassical = true ∧
      verifyPq env.pkPq
        (encodeHybridRolePayload .postQuantum env.suiteTag env.classicalAlg env.pqAlg
          env.idCommit env.pkClassicalDigest env.pkPqDigest msg) env.sigPq = true := by
    dsimp only at hAccept
    unfold verifyHybridPinnedEnvelope at hAccept
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAccept
    exact ⟨hAccept.1.1.1.1.1, hAccept.1.1.1.1.2, hAccept.1.1.1.2,
           hAccept.1.1.2, hAccept.1.2, hAccept.2⟩
  if hKeysEq : env.pkClassical = pkC ∧ env.pkPq = pkPq then
    have hMsgFresh : msg ∉ signedMsgs := by
      rcases hFreshOrSubst with hm | hc | hp
      · exact hm
      · exact False.elim (hc hKeysEq.1)
      · exact False.elim (hp hKeysEq.2)
    have hSuiteValid : validHybridSuiteTriplet suite cAlg pqAlg = true := by
      rcases hUnpack.2.2.1 with ⟨hS, hCA, hPA, _⟩
      simpa [hS, hCA, hPA] using hUnpack.1
    have hU16 := hybridSuite_u16_bounds hSuiteValid
    have hEnvCD : env.pkClassicalDigest = pkCD := by
      rcases hUnpack.2.2.1 with ⟨hS, hCA, _, _⟩
      have hRec := hUnpack.2.2.2.1.1
      rw [hS, hCA, hKeysEq.1] at hRec
      exact hRec.symm
    have hEnvPD : env.pkPqDigest = pkPD := by
      rcases hUnpack.2.2.1 with ⟨hS, _, hPA, _⟩
      have hRec := hUnpack.2.2.2.1.2.1
      rw [hS, hPA, hKeysEq.2] at hRec
      exact hRec.symm
    let cPay := encodeHybridRolePayload .classical suite cAlg pqAlg pinnedId pkCD pkPD msg
    let pqPay := encodeHybridRolePayload .postQuantum suite cAlg pqAlg pinnedId pkCD pkPD msg
    have hcVal : verifyClassical pkC cPay env.sigClassical = true := by
      rcases hUnpack.2.2.1 with ⟨hS, hCA, hPA, hId⟩
      simpa [cPay, hS, hCA, hPA, hId, hEnvCD, hEnvPD, hKeysEq.1] using hUnpack.2.2.2.2.1
    have hpqVal : verifyPq pkPq pqPay env.sigPq = true := by
      rcases hUnpack.2.2.1 with ⟨hS, hCA, hPA, hId⟩
      simpa [pqPay, hS, hCA, hPA, hId, hEnvCD, hEnvPD, hKeysEq.2] using hUnpack.2.2.2.2.2
    have hId32 : pinnedId.length = 32 := hOut32 _ _
    have hCD32 : pkCD.length = 32 := hOut32 _ _
    have hPD32 : pkPD.length = 32 := hOut32 _ _
    have hcFresh : cPay ∉ signedMsgs.map (fun m =>
        encodeHybridRolePayload .classical suite cAlg pqAlg pinnedId pkCD pkPD m) := by
      intro hMem
      rw [List.mem_map] at hMem
      obtain ⟨m', hm'Mem, hm'Eq⟩ := hMem
      have hInj := encodeHybridRolePayload_injective
        hU16.1 hU16.1 hU16.2.1 hU16.2.1 hU16.2.2 hU16.2.2
        hId32 hId32 hCD32 hCD32 hPD32 hPD32 hm'Eq
      exact hMsgFresh (hInj.2.2.2.2.2.2.2 ▸ hm'Mem)
    have hpqFresh : pqPay ∉ signedMsgs.map (fun m =>
        encodeHybridRolePayload .postQuantum suite cAlg pqAlg pinnedId pkCD pkPD m) := by
      intro hMem
      rw [List.mem_map] at hMem
      obtain ⟨m', hm'Mem, hm'Eq⟩ := hMem
      have hInj := encodeHybridRolePayload_injective
        hU16.1 hU16.1 hU16.2.1 hU16.2.1 hU16.2.2 hU16.2.2
        hId32 hId32 hCD32 hCD32 hPD32 hPD32 hm'Eq
      exact hMsgFresh (hInj.2.2.2.2.2.2.2 ▸ hm'Mem)
    have hDisj : cPay ≠ pqPay := fun hEq => by
      have hR := (encodeHybridRolePayload_injective
        hU16.1 hU16.1 hU16.2.1 hU16.2.1 hU16.2.2 hU16.2.2
        hId32 hId32 hCD32 hCD32 hPD32 hPD32 hEq).1
      cases hR
    .inr { classicalPayload := cPay
           classicalSig := env.sigClassical
           classical_fresh := hcFresh
           classical_valid := hcVal
           pqPayload := pqPay
           pqSig := env.sigPq
           pq_fresh := hpqFresh
           pq_valid := hpqVal
           role_disjoint := hDisj }
  else if hDigsEq : env.pkClassicalDigest = pkCD ∧ env.pkPqDigest = pkPD then
    if hPkCEq : env.pkClassical = pkC then
      have hPkPqNe : env.pkPq ≠ pkPq := fun hEq => hKeysEq ⟨hPkCEq, hEq⟩
      let m1 := encodeFramedU64Le [be 2 env.suiteTag, be 2 env.pqAlg, env.pkPq]
      let m2 := encodeFramedU64Le [be 2 suite, be 2 pqAlg, pkPq]
      have hNe : m1 ≠ m2 := fun hmEq => by
        have hF := encodeFramedU64Le_injective
          (list3_len_lt_u64 _ _ _)
          (fun f hf => by
            rcases List.mem_cons.mp hf with rfl | hf1
            · exact be_length_lt_u64 (by decide) _
            · rcases List.mem_cons.mp hf1 with rfl | hf2
              · exact be_length_lt_u64 (by decide) _
              · rcases List.mem_cons.mp hf2 with rfl | hf3
                · exact hUnpack.2.1.2.2.2.2
                · cases hf3)
          (list3_len_lt_u64 _ _ _)
          (fun f hf => by
            rcases List.mem_cons.mp hf with rfl | hf1
            · exact be_length_lt_u64 (by decide) _
            · rcases List.mem_cons.mp hf1 with rfl | hf2
              · exact be_length_lt_u64 (by decide) _
              · rcases List.mem_cons.mp hf2 with rfl | hf3
                · exact hPkPqBound
                · cases hf3)
          hmEq
        simp only [List.cons.injEq] at hF
        exact hPkPqNe hF.2.2.1
      have hHashEq : H_dom hybridPkPqDomain m1 = H_dom hybridPkPqDomain m2 := by
        change hashHybridPqPk H_dom env.suiteTag env.pqAlg env.pkPq = pkPD
        exact hUnpack.2.2.2.1.2.1.trans hDigsEq.2
      .inl { domain := hybridPkPqDomain, m1 := m1, m2 := m2, ne := hNe, eq := hHashEq }
    else
      let m1 := encodeFramedU64Le [be 2 env.suiteTag, be 2 env.classicalAlg, env.pkClassical]
      let m2 := encodeFramedU64Le [be 2 suite, be 2 cAlg, pkC]
      have hNe : m1 ≠ m2 := fun hmEq => by
        have hF := encodeFramedU64Le_injective
          (list3_len_lt_u64 _ _ _)
          (fun f hf => by
            rcases List.mem_cons.mp hf with rfl | hf1
            · exact be_length_lt_u64 (by decide) _
            · rcases List.mem_cons.mp hf1 with rfl | hf2
              · exact be_length_lt_u64 (by decide) _
              · rcases List.mem_cons.mp hf2 with rfl | hf3
                · exact hUnpack.2.1.2.2.2.1
                · cases hf3)
          (list3_len_lt_u64 _ _ _)
          (fun f hf => by
            rcases List.mem_cons.mp hf with rfl | hf1
            · exact be_length_lt_u64 (by decide) _
            · rcases List.mem_cons.mp hf1 with rfl | hf2
              · exact be_length_lt_u64 (by decide) _
              · rcases List.mem_cons.mp hf2 with rfl | hf3
                · exact hPkCBound
                · cases hf3)
          hmEq
        simp only [List.cons.injEq] at hF
        exact hPkCEq hF.2.2.1
      have hHashEq : H_dom hybridPkClassicalDomain m1 = H_dom hybridPkClassicalDomain m2 := by
        change hashHybridClassicalPk H_dom env.suiteTag env.classicalAlg env.pkClassical = pkCD
        exact hUnpack.2.2.2.1.1.trans hDigsEq.1
      .inl { domain := hybridPkClassicalDomain, m1 := m1, m2 := m2, ne := hNe, eq := hHashEq }
  else
    let m1 := encodeFramedU64Le [be 2 env.suiteTag, be 2 env.classicalAlg, be 2 env.pqAlg,
                                 env.pkClassicalDigest, env.pkPqDigest]
    let m2 := encodeFramedU64Le [be 2 suite, be 2 cAlg, be 2 pqAlg, pkCD, pkPD]
    have hNe : m1 ≠ m2 := fun hmEq => by
      have hCD32 : pkCD.length = 32 := hOut32 _ _
      have hPD32 : pkPD.length = 32 := hOut32 _ _
      have hF := encodeFramedU64Le_injective
        (list5_len_lt_u64 _ _ _ _ _)
        (fun f hf => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl | rfl | rfl | rfl
          · exact be_length_lt_u64 (by decide) _
          · exact be_length_lt_u64 (by decide) _
          · exact be_length_lt_u64 (by decide) _
          · rw [hUnpack.2.1.2.1]; decide
          · rw [hUnpack.2.1.2.2.1]; decide)
        (list5_len_lt_u64 _ _ _ _ _)
        (fun f hf => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl | rfl | rfl | rfl
          · exact be_length_lt_u64 (by decide) _
          · exact be_length_lt_u64 (by decide) _
          · exact be_length_lt_u64 (by decide) _
          · rw [hCD32]; decide
          · rw [hPD32]; decide)
        hmEq
      simp only [List.cons.injEq] at hF
      exact hDigsEq ⟨hF.2.2.2.1, hF.2.2.2.2.1⟩
    have hHashEq : H_dom hybridIdCommitDomain m1 = H_dom hybridIdCommitDomain m2 :=
      hUnpack.2.2.2.1.2.2
    .inl { domain := hybridIdCommitDomain, m1 := m1, m2 := m2, ne := hNe, eq := hHashEq }

/-- Naive unpinned hybrid verifier vulnerable to PQ key substitution / stripping. -/
def unpinnedHybridVerify
    (verifyClassical verifyPq : List UInt8 → List UInt8 → List UInt8 → Bool)
    (pinnedPkC msg candidatePkPq sigC sigPq : List UInt8) : Bool :=
  verifyClassical pinnedPkC msg sigC && verifyPq candidatePkPq msg sigPq

/-- **`#tooth` Unpinned Hybrid Key-Stripping Attack (`tooth_unpinned_concatenation_allows_pq_key_stripping`)**:
    If the classical signature signs raw `msg` without pinning `pkPq` (and the identity does not pin
    `idCommit`), a quantum adversary who breaks ONLY `pinnedPkC` substitutes its OWN fresh `attackerPkPq ≠ honestPkPq`
    and passes verification with zero forgery against `honestPkPq`! -/
theorem tooth_unpinned_concatenation_allows_pq_key_stripping :
    let verifyC : List UInt8 → List UInt8 → List UInt8 → Bool := fun pk m s => decide (s = pk ++ m)
    let verifyPq : List UInt8 → List UInt8 → List UInt8 → Bool := fun pk m s => decide (s = pk ++ m)
    let honestPkC : List UInt8 := [0x11]
    let honestPkPq : List UInt8 := [0x22]
    let attackerPkPq : List UInt8 := [0x99]
    let msg : List UInt8 := [0x42]
    attackerPkPq ≠ honestPkPq ∧
    unpinnedHybridVerify verifyC verifyPq honestPkC msg attackerPkPq
      (honestPkC ++ msg) (attackerPkPq ++ msg) = true ∧
    verifyPq honestPkPq msg (attackerPkPq ++ msg) = false := by
  decide

/-- **`#tooth` Swapped Suite / Algorithm Triplet Rejection (`tooth_hybrid_swapped_suite_alg_rejected`)**:
    Production `validHybridSuiteTriplet` accepts `0x0501 = (Secp256k1=0x0001, MlDsa44=0x0101)` and
    `0x0502 = (Ed25519=0x0002, MlDsa65=0x0102)`, while rejecting swapped/colliding pairings such as
    `(0x0501, 0x0002, 0x0102)`! -/
theorem tooth_hybrid_swapped_suite_alg_rejected :
    validHybridSuiteTriplet suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 algPqMlDsa44 = true ∧
    validHybridSuiteTriplet suiteHybridEd25519MlDsa65 algClassicalEd25519 algPqMlDsa65 = true ∧
    validHybridSuiteTriplet suiteHybridSecp256k1MlDsa44 algClassicalEd25519 algPqMlDsa65 = false := by
  decide

/-- Non-trivial inhabitedness witness for `verifyHybridPinnedEnvelope` over concrete SP 800-185
    `cshake256Bytes`, production suite `0x0501` (`HybridSecp256k1MlDsa44`), and distinct role-tagged
    classical/PQ verifiers. -/
theorem witness_hybrid_envelope_inhabited :
    let H_dom : DomainHash := cshake256Bytes
    let verifyClassical : List UInt8 → List UInt8 → List UInt8 → Bool :=
      fun pk pay sig => decide (sig = (0xC1 : UInt8) :: (pk ++ pay))
    let verifyPq : List UInt8 → List UInt8 → List UInt8 → Bool :=
      fun pk pay sig => decide (sig = (0x51 : UInt8) :: (pk ++ pay))
    let pkC : List UInt8 := [0x02, 0x11, 0x22]
    let pkPq : List UInt8 := [0x33, 0x44, 0x55]
    let pkCD := hashHybridClassicalPk H_dom suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 pkC
    let pkPD := hashHybridPqPk H_dom suiteHybridSecp256k1MlDsa44 algPqMlDsa44 pkPq
    let idC := computeAddrHybridIdCommit H_dom suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 algPqMlDsa44 pkCD pkPD
    let cPay := encodeHybridRolePayload .classical suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 algPqMlDsa44 idC pkCD pkPD [0xFF]
    let pqPay := encodeHybridRolePayload .postQuantum suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 algPqMlDsa44 idC pkCD pkPD [0xFF]
    let env : HybridPinnedEnvelope :=
      { suiteTag := suiteHybridSecp256k1MlDsa44
        classicalAlg := algClassicalSecp256k1
        pqAlg := algPqMlDsa44
        idCommit := idC
        pkClassicalDigest := pkCD
        pkPqDigest := pkPD
        pkClassical := pkC
        pkPq := pkPq
        sigClassical := (0xC1 : UInt8) :: (pkC ++ cPay)
        sigPq := (0x51 : UInt8) :: (pkPq ++ pqPay) }
    (H_dom hybridIdCommitDomain [0x00]).length = 32 ∧
    H_dom hybridIdCommitDomain [0x00] ≠ [0x00] ∧
    verifyClassical pkC cPay env.sigPq = false ∧
    verifyHybridPinnedEnvelope H_dom verifyClassical verifyPq
      suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 algPqMlDsa44 idC [0xFF] env = true := by
  intro H_dom verifyClassical verifyPq pkC pkPq pkCD pkPD idC cPay pqPay env
  have hLen32 : (H_dom hybridIdCommitDomain [0x00]).length = 32 :=
    cshake256Bytes_length hybridIdCommitDomain [0x00]
  have hNotId : H_dom hybridIdCommitDomain [0x00] ≠ [0x00] := by
    intro hEq
    have hL := congrArg List.length hEq
    rw [hLen32] at hL
    cases hL
  have hCrossRole : verifyClassical pkC cPay env.sigPq = false := by
    dsimp only [verifyClassical, env]
    exact decide_eq_false (fun h => by injection h with hHd _; cases hHd)
  have hIdLen : idC.length = 32 := cshake256Bytes_length _ _
  have hCDLen : pkCD.length = 32 := cshake256Bytes_length _ _
  have hPDLen : pkPD.length = 32 := cshake256Bytes_length _ _
  have hPkCLen : pkC.length < 256 ^ 8 := by decide
  have hPkPqLen : pkPq.length < 256 ^ 8 := by decide
  have hSuiteOk : validHybridSuiteTriplet suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 algPqMlDsa44 = true := by decide
  have hCDDef : hashHybridClassicalPk H_dom suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 pkC = pkCD := rfl
  have hPDDef : hashHybridPqPk H_dom suiteHybridSecp256k1MlDsa44 algPqMlDsa44 pkPq = pkPD := rfl
  have hIdDef : computeAddrHybridIdCommit H_dom suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 algPqMlDsa44 pkCD pkPD = idC := rfl
  have hcPayDef : encodeHybridRolePayload .classical suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 algPqMlDsa44 idC pkCD pkPD [0xFF] = cPay := rfl
  have hpqPayDef : encodeHybridRolePayload .postQuantum suiteHybridSecp256k1MlDsa44 algClassicalSecp256k1 algPqMlDsa44 idC pkCD pkPD [0xFF] = pqPay := rfl
  refine ⟨hLen32, hNotId, hCrossRole, ?_⟩
  unfold verifyHybridPinnedEnvelope
  dsimp only [env, verifyClassical, verifyPq]
  simp only [hSuiteOk, hIdLen, hCDLen, hPDLen, hPkCLen, hPkPqLen,
    hCDDef, hPDDef, hIdDef, hcPayDef, hpqPayDef, and_self, decide_true, Bool.and_self]

/-! ## §4. `qsag-migrate` — 219-Repetition ZKBoo Soundness (`< 2^-128`) & 3-of-3 Outer-MPC Key Privacy -/

/-- Count how many challenge vectors in `(Fin R → Fin 3)` pass all `R` frozen ZKBoo repetitions. -/
def countAcceptingChallenges : (R : Nat) → (Fin R → Fin 3 → Bool) → Nat
  | 0, _ => 1
  | r + 1, accept =>
    let sub := countAcceptingChallenges r (fun idx c => accept ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩ c)
    (if accept ⟨0, Nat.zero_lt_succ r⟩ ⟨0, by decide⟩ then sub else 0) +
    (if accept ⟨0, Nat.zero_lt_succ r⟩ ⟨1, by decide⟩ then sub else 0) +
    (if accept ⟨0, Nat.zero_lt_succ r⟩ ⟨2, by decide⟩ then sub else 0)

theorem countAcceptingChallenges_le_two_pow :
    ∀ (R : Nat) (accept : Fin R → Fin 3 → Bool),
      (∀ r : Fin R, ∃ bad : Fin 3, accept r bad = false) →
      countAcceptingChallenges R accept ≤ 2 ^ R
  | 0, _, _ => by simp [countAcceptingChallenges]
  | r + 1, accept, hAtMostTwo => by
    simp only [countAcceptingChallenges]
    have ih := countAcceptingChallenges_le_two_pow r
      (fun idx c => accept ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩ c)
      (fun idx => hAtMostTwo ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩)
    obtain ⟨⟨b, hb⟩, hBad0⟩ := hAtMostTwo ⟨0, Nat.zero_lt_succ r⟩
    have hSumLe :
        (if accept ⟨0, Nat.zero_lt_succ r⟩ ⟨0, by decide⟩ then
           countAcceptingChallenges r (fun idx c => accept ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩ c) else 0) +
        (if accept ⟨0, Nat.zero_lt_succ r⟩ ⟨1, by decide⟩ then
           countAcceptingChallenges r (fun idx c => accept ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩ c) else 0) +
        (if accept ⟨0, Nat.zero_lt_succ r⟩ ⟨2, by decide⟩ then
           countAcceptingChallenges r (fun idx c => accept ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩ c) else 0) ≤
        2 * countAcceptingChallenges r (fun idx c => accept ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩ c) := by
      rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl
      · simp only [hBad0, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        split <;> split <;> omega
      · simp only [hBad0, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        split <;> split <;> omega
      · simp only [hBad0, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        split <;> split <;> omega
    have hPow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
    omega

/-- **219-Repetition ZKBoo Soundness Bound (`zkboo_219_soundness_lt_two_pow_neg128`)**:
    1. Exact integer inequality `(2 : Nat) ^ 219 * 2 ^ 128 < 3 ^ 219` and rational `< 2^-128` bound
       `ratLe (2 ^ 219, 3 ^ 219) (1, 2 ^ 128)`.
    2. For ANY frozen 219-repetition ZKBoo ceremony commitment root on an invalid statement where each
       repetition rejects at least 1 of the 3 head pairs `{0,1}`, `{1,2}`, `{2,0}`, at most `2 ^ 219`
       of the `3 ^ 219` Fiat-Shamir challenge vectors accept, achieving `ratLe (accepting, 3 ^ 219) (1, 2 ^ 128)`. -/
theorem zkboo_219_soundness_lt_two_pow_neg128 :
    (2 : Nat) ^ 219 * 2 ^ 128 < 3 ^ 219 ∧
    ratLe (2 ^ 219, 3 ^ 219) (1, 2 ^ 128) ∧
    (∀ accept : Fin 219 → Fin 3 → Bool,
      (∀ r : Fin 219, ∃ bad : Fin 3, accept r bad = false) →
      countAcceptingChallenges 219 accept ≤ 2 ^ 219 ∧
      ratLe (countAcceptingChallenges 219 accept, 3 ^ 219) (1, 2 ^ 128)) := by
  have hStrict : (2 : Nat) ^ 219 * 2 ^ 128 < 3 ^ 219 := by decide
  have hPos3 : 0 < (3 : Nat) ^ 219 := by decide
  have hPos2 : 0 < (2 : Nat) ^ 128 := by decide
  refine ⟨hStrict, ⟨hPos3, hPos2, Nat.le_of_lt (by rw [Nat.one_mul]; exact hStrict)⟩, ?_⟩
  intro accept hLocal
  have hCnt := countAcceptingChallenges_le_two_pow 219 accept hLocal
  refine ⟨hCnt, ⟨hPos3, hPos2, ?_⟩⟩
  have hMul := Nat.mul_le_mul_right (2 ^ 128) hCnt
  omega

/-- Cyclic successor `(c + 1) mod 3` on `Fin 3`. -/
def nextFin3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩

/-- Cyclic second successor `(c + 2) mod 3` on `Fin 3` (the unique unopened head / second honest custodian). -/
def thirdFin3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨2, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩
  | ⟨2, _⟩ => ⟨1, by decide⟩

private theorem bvXor_comm {w : Nat} (a b : BitVec w) : a ^^^ b = b ^^^ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _; simp only [BitVec.getLsbD_xor]; cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem bvXor_assoc {w : Nat} (a b c : BitVec w) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _; simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

private theorem bvXor_self {w : Nat} (a : BitVec w) : a ^^^ a = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _; simp

private theorem bvXor_zero {w : Nat} (a : BitVec w) : a ^^^ 0#w = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _; simp

private theorem bvXor_cancel_right {w : Nat} (a b : BitVec w) : (a ^^^ b) ^^^ b = a := by
  rw [bvXor_assoc, bvXor_self, bvXor_zero]

private theorem bvXor_fin3_perm {w : Nat} (c : Fin 3) (f : Fin 3 → BitVec w) :
    (f ⟨0, by decide⟩ ^^^ f ⟨1, by decide⟩) ^^^ f ⟨2, by decide⟩ =
      (f c ^^^ f (nextFin3 c)) ^^^ f (thirdFin3 c) := by
  rcases c with ⟨idx, hIdx⟩
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl
  · rfl
  · dsimp only [nextFin3, thirdFin3]
    rw [bvXor_comm (f ⟨0, by decide⟩) (f ⟨1, by decide⟩),
        bvXor_assoc (f ⟨1, by decide⟩) (f ⟨0, by decide⟩) (f ⟨2, by decide⟩),
        bvXor_comm (f ⟨0, by decide⟩) (f ⟨2, by decide⟩),
        ← bvXor_assoc]
  · dsimp only [nextFin3, thirdFin3]
    rw [bvXor_comm ((f ⟨0, by decide⟩) ^^^ (f ⟨1, by decide⟩)) (f ⟨2, by decide⟩),
        ← bvXor_assoc]

/-- Complete 3-of-3 physical + virtual witness sharing configuration across `R` ZKBoo repetitions. -/
structure OuterMpcConfig (wBits R : Nat) where
  /-- Physical custodian shares `s_0, s_1, s_2` of witness `w = s_0 ⊕ s_1 ⊕ s_2`. -/
  s : Fin 3 → BitVec wBits
  /-- Virtual ZKBoo head shares `v_{r,0}, v_{r,1}, v_{r,2}` satisfying `v_{r,0} ⊕ v_{r,1} ⊕ v_{r,2} = w`. -/
  v : Fin R → Fin 3 → BitVec wBits
  /-- 3-of-3 outer-MPC physical masks `m_{r,h,0}, m_{r,h,1}, m_{r,h,2}` satisfying `⊕_p m_{r,h,p} = v_{r,h}`. -/
  m : Fin R → Fin 3 → Fin 3 → BitVec wBits

/-- Consistency predicate of a 3-of-3 outer-MPC configuration encoding private key `w`. -/
def ValidOuterMpcConfig (wBits R : Nat) (w : BitVec wBits) (cfg : OuterMpcConfig wBits R) : Prop :=
  (cfg.s ⟨0, by decide⟩ ^^^ cfg.s ⟨1, by decide⟩) ^^^ cfg.s ⟨2, by decide⟩ = w ∧
  (∀ r : Fin R, (cfg.v r ⟨0, by decide⟩ ^^^ cfg.v r ⟨1, by decide⟩) ^^^ cfg.v r ⟨2, by decide⟩ = w) ∧
  (∀ (r : Fin R) (h : Fin 3),
    (cfg.m r h ⟨0, by decide⟩ ^^^ cfg.m r h ⟨1, by decide⟩) ^^^ cfg.m r h ⟨2, by decide⟩ = cfg.v r h)

/-- Corrupted physical custodian `c`'s complete joint view across all `R` ZKBoo repetitions:
    `(s_c, {m_{r,h,c}}_{r,h}, {(v_{r, e_r}, v_{r, e_r + 1})}_r)`. -/
structure CustodianJointView (wBits R : Nat) where
  ownKeyShare : BitVec wBits
  ownHeadMasks : Fin R → Fin 3 → BitVec wBits
  openedVirtualHeads : Fin R → BitVec wBits × BitVec wBits

/-- Exact joint view projection observed by corrupted physical custodian `c` under challenge `e`. -/
@[expose] def custodianJointView (wBits R : Nat) (c : Fin 3) (e : Fin R → Fin 3)
    (cfg : OuterMpcConfig wBits R) : CustodianJointView wBits R :=
  { ownKeyShare := cfg.s c
    ownHeadMasks := fun r h => cfg.m r h c
    openedVirtualHeads := fun r => (cfg.v r (e r), cfg.v r (nextFin3 (e r))) }

/-- Fixed witness-and-view-independent honest mask residual space (`1 + 3*R` `wBits`-bit words). -/
abbrev HonestOuterMaskSpace (wBits R : Nat) :=
  BitVec wBits × (Fin R → Fin 3 → BitVec wBits)

private theorem fin3_cases_disjoint : ∀ c : Fin 3,
    nextFin3 c ≠ c ∧ thirdFin3 c ≠ c ∧ thirdFin3 c ≠ nextFin3 c
  | ⟨0, _⟩ => ⟨fun h => (by cases h), fun h => (by cases h), fun h => (by cases h)⟩
  | ⟨1, _⟩ => ⟨fun h => (by cases h), fun h => (by cases h), fun h => (by cases h)⟩
  | ⟨2, _⟩ => ⟨fun h => (by cases h), fun h => (by cases h), fun h => (by cases h)⟩
  | ⟨_ + 3, h⟩ => absurd h (by omega)

private theorem fin3_trichotomy : ∀ u p : Fin 3,
    p = u ∨ p = nextFin3 u ∨ p = thirdFin3 u
  | ⟨0, _⟩, ⟨0, _⟩ => Or.inl rfl
  | ⟨0, _⟩, ⟨1, _⟩ => Or.inr (Or.inl rfl)
  | ⟨0, _⟩, ⟨2, _⟩ => Or.inr (Or.inr rfl)
  | ⟨1, _⟩, ⟨1, _⟩ => Or.inl rfl
  | ⟨1, _⟩, ⟨2, _⟩ => Or.inr (Or.inl rfl)
  | ⟨1, _⟩, ⟨0, _⟩ => Or.inr (Or.inr rfl)
  | ⟨2, _⟩, ⟨2, _⟩ => Or.inl rfl
  | ⟨2, _⟩, ⟨0, _⟩ => Or.inr (Or.inl rfl)
  | ⟨2, _⟩, ⟨1, _⟩ => Or.inr (Or.inr rfl)
  | ⟨_ + 3, h⟩, _ => absurd h (by omega)
  | _, ⟨_ + 3, h⟩ => absurd h (by omega)

/-- Constructive `SimpleEquiv` (no choice operator) proving that for ANY witness `w`, ANY corrupted
    physical custodian `c ∈ Fin 3`, ANY challenge vector `e : Fin R → Fin 3`, and ANY target joint view
    `V : CustodianJointView wBits R`, the fiber of valid configurations producing `V` is bijective to
    the constant `HonestOuterMaskSpace wBits R`! -/
def outerMpcViewFiberEquiv (wBits R : Nat) (w : BitVec wBits)
    (c : Fin 3) (e : Fin R → Fin 3) (V : CustodianJointView wBits R) :
    SimpleEquiv
      (HonestOuterMaskSpace wBits R)
      { cfg : OuterMpcConfig wBits R //
          ValidOuterMpcConfig wBits R w cfg ∧ custodianJointView wBits R c e cfg = V } where
  toFun := fun ⟨freeKeyMask, freeHeadMasks⟩ =>
    let s : Fin 3 → BitVec wBits := fun p =>
      if p = c then V.ownKeyShare
      else if p = nextFin3 c then freeKeyMask
      else (V.ownKeyShare ^^^ freeKeyMask) ^^^ w
    let v : Fin R → Fin 3 → BitVec wBits := fun r h =>
      if h = e r then (V.openedVirtualHeads r).1
      else if h = nextFin3 (e r) then (V.openedVirtualHeads r).2
      else ((V.openedVirtualHeads r).1 ^^^ (V.openedVirtualHeads r).2) ^^^ w
    let m : Fin R → Fin 3 → Fin 3 → BitVec wBits := fun r h p =>
      if p = c then V.ownHeadMasks r h
      else if p = nextFin3 c then freeHeadMasks r h
      else (V.ownHeadMasks r h ^^^ freeHeadMasks r h) ^^^ v r h
    have hDisjC := fin3_cases_disjoint c
    have hKeySum : (s ⟨0, by decide⟩ ^^^ s ⟨1, by decide⟩) ^^^ s ⟨2, by decide⟩ = w := by
      rw [bvXor_fin3_perm c s]
      have hs0 : s c = V.ownKeyShare := by simp [s]
      have hs1 : s (nextFin3 c) = freeKeyMask := by simp [s, hDisjC.1]
      have hs2 : s (thirdFin3 c) = (V.ownKeyShare ^^^ freeKeyMask) ^^^ w := by
        simp [s, hDisjC.2.1, hDisjC.2.2]
      rw [hs0, hs1, hs2, ← bvXor_assoc (V.ownKeyShare ^^^ freeKeyMask), bvXor_self,
          bvXor_comm 0#wBits w, bvXor_zero]
    have hVirtSum : ∀ r : Fin R,
        (v r ⟨0, by decide⟩ ^^^ v r ⟨1, by decide⟩) ^^^ v r ⟨2, by decide⟩ = w := by
      intro r
      have hDisjE := fin3_cases_disjoint (e r)
      rw [bvXor_fin3_perm (e r) (v r)]
      have hv0 : v r (e r) = (V.openedVirtualHeads r).1 := by simp [v]
      have hv1 : v r (nextFin3 (e r)) = (V.openedVirtualHeads r).2 := by simp [v, hDisjE.1]
      have hv2 : v r (thirdFin3 (e r)) =
          ((V.openedVirtualHeads r).1 ^^^ (V.openedVirtualHeads r).2) ^^^ w := by
        simp [v, hDisjE.2.1, hDisjE.2.2]
      rw [hv0, hv1, hv2, ← bvXor_assoc ((V.openedVirtualHeads r).1 ^^^ (V.openedVirtualHeads r).2),
          bvXor_self, bvXor_comm 0#wBits w, bvXor_zero]
    have hMaskSum : ∀ (r : Fin R) (h : Fin 3),
        (m r h ⟨0, by decide⟩ ^^^ m r h ⟨1, by decide⟩) ^^^ m r h ⟨2, by decide⟩ = v r h := by
      intro r h
      rw [bvXor_fin3_perm c (m r h)]
      have hm0 : m r h c = V.ownHeadMasks r h := by simp [m]
      have hm1 : m r h (nextFin3 c) = freeHeadMasks r h := by simp [m, hDisjC.1]
      have hm2 : m r h (thirdFin3 c) = (V.ownHeadMasks r h ^^^ freeHeadMasks r h) ^^^ v r h := by
        simp [m, hDisjC.2.1, hDisjC.2.2]
      rw [hm0, hm1, hm2, ← bvXor_assoc (V.ownHeadMasks r h ^^^ freeHeadMasks r h),
          bvXor_self, bvXor_comm 0#wBits (v r h), bvXor_zero]
    have hViewEq : custodianJointView wBits R c e ⟨s, v, m⟩ = V := by
      cases V with
      | mk ownK ownM openV =>
        unfold custodianJointView
        congr 1
        · simp [s]
        · funext r h; simp [m]
        · funext r
          have hDisjE := fin3_cases_disjoint (e r)
          apply Prod.ext
          · simp [v]
          · simp [v, hDisjE.1]
    ⟨⟨s, v, m⟩, ⟨⟨hKeySum, hVirtSum, hMaskSum⟩, hViewEq⟩⟩
  invFun := fun ⟨cfg, _⟩ =>
    (cfg.s (nextFin3 c), fun r h => cfg.m r h (nextFin3 c))
  left_inv := fun ⟨freeKeyMask, freeHeadMasks⟩ => by
    have hDisjC := fin3_cases_disjoint c
    apply Prod.ext
    · simp [hDisjC.1]
    · funext r h; simp [hDisjC.1]
  right_inv := fun ⟨⟨s, v, m⟩, ⟨⟨hKeySum, hVirtSum, hMaskSum⟩, hViewEq⟩⟩ => by
    apply Subtype.ext
    have hDisjC := fin3_cases_disjoint c
    have hOwnK : V.ownKeyShare = s c := (congrArg CustodianJointView.ownKeyShare hViewEq).symm
    have hOwnM : ∀ r h, V.ownHeadMasks r h = m r h c := fun r h =>
      congrFun (congrFun (congrArg CustodianJointView.ownHeadMasks hViewEq).symm r) h
    have hOpenV : ∀ r, V.openedVirtualHeads r = (v r (e r), v r (nextFin3 (e r))) := fun r =>
      congrFun (congrArg CustodianJointView.openedVirtualHeads hViewEq).symm r
    have hSolveThird : ∀ (u : Fin 3) (f : Fin 3 → BitVec wBits) (target : BitVec wBits),
        (f ⟨0, by decide⟩ ^^^ f ⟨1, by decide⟩) ^^^ f ⟨2, by decide⟩ = target →
        (f u ^^^ f (nextFin3 u)) ^^^ target = f (thirdFin3 u) := by
      intro u f target hEq
      rw [← hEq, bvXor_fin3_perm u f, ← bvXor_assoc (f u ^^^ f (nextFin3 u)),
          bvXor_self, bvXor_comm 0#wBits _, bvXor_zero]
    have hS : (fun p =>
        if p = c then V.ownKeyShare
        else if p = nextFin3 c then s (nextFin3 c)
        else (V.ownKeyShare ^^^ s (nextFin3 c)) ^^^ w) = s := by
      funext p
      rcases fin3_trichotomy c p with rfl | rfl | rfl
      · simp [hOwnK]
      · simp [hDisjC.1]
      · simp [hDisjC.2.1, hDisjC.2.2, hOwnK, hSolveThird c s w hKeySum]
    have hV : (fun r h =>
        if h = e r then (V.openedVirtualHeads r).1
        else if h = nextFin3 (e r) then (V.openedVirtualHeads r).2
        else ((V.openedVirtualHeads r).1 ^^^ (V.openedVirtualHeads r).2) ^^^ w) = v := by
      funext r h
      have hDisjE := fin3_cases_disjoint (e r)
      rcases fin3_trichotomy (e r) h with rfl | rfl | rfl
      · simp [hOpenV r]
      · simp [hDisjE.1, hOpenV r]
      · simp [hDisjE.2.1, hDisjE.2.2, hOpenV r, hSolveThird (e r) (v r) w (hVirtSum r)]
    have hM : (fun r h p =>
        if p = c then V.ownHeadMasks r h
        else if p = nextFin3 c then m r h (nextFin3 c)
        else (V.ownHeadMasks r h ^^^ m r h (nextFin3 c)) ^^^
          (if h = e r then (V.openedVirtualHeads r).1
           else if h = nextFin3 (e r) then (V.openedVirtualHeads r).2
           else ((V.openedVirtualHeads r).1 ^^^ (V.openedVirtualHeads r).2) ^^^ w)) = m := by
      funext r h p
      have hVrh := congrFun (congrFun hV r) h
      rw [hVrh]
      rcases fin3_trichotomy c p with rfl | rfl | rfl
      · simp [hOwnM r h]
      · simp [hDisjC.1]
      · simp [hDisjC.2.1, hDisjC.2.2, hOwnM r h, hSolveThird c (m r h) (v r h) (hMaskSum r h)]
    dsimp only
    rw [hS, hV, hM]

/-- Direct constructive `SimpleEquiv` (no choice operator) mapping valid configurations for witness
    `w₁` bijectively to valid configurations for witness `w₂` with **identical** `custodianJointView c e`! -/
def outerMpcWitnessShiftEquiv (wBits R : Nat) (w₁ w₂ : BitVec wBits)
    (c : Fin 3) (e : Fin R → Fin 3) (V : CustodianJointView wBits R) :
    SimpleEquiv
      { cfg : OuterMpcConfig wBits R //
          ValidOuterMpcConfig wBits R w₁ cfg ∧ custodianJointView wBits R c e cfg = V }
      { cfg : OuterMpcConfig wBits R //
          ValidOuterMpcConfig wBits R w₂ cfg ∧ custodianJointView wBits R c e cfg = V } :=
  let e1 := outerMpcViewFiberEquiv wBits R w₁ c e V
  let e2 := outerMpcViewFiberEquiv wBits R w₂ c e V
  { toFun := fun x => e2.toFun (e1.invFun x)
    invFun := fun y => e1.toFun (e2.invFun y)
    left_inv := fun x => by rw [e2.left_inv, e1.right_inv]
    right_inv := fun y => by rw [e1.left_inv, e2.right_inv] }

/-- **3-of-3 Outer-MPC Single-Custodian Perfect Key Privacy (`cozk_outer_mpc_one_custodian_perfect_key_privacy`)**:
    At deployed parameters (`wBits = 256` secp256k1/Ed25519 private key, `R = 219` ZKBoo repetitions),
    for ANY corrupted physical custodian `c ∈ Fin 3`, ANY challenge vector `e : Fin 219 → Fin 3`,
    ANY two candidate private keys `w₁, w₂ : BitVec 256`, and ANY target joint view `V`:
    1. Both witness fibers `{ cfg | ValidOuterMpcConfig 256 219 w cfg ∧ custodianJointView 256 219 c e cfg = V }`
       are constructively bijective to the constant `HonestOuterMaskSpace 256 219` (proving uniform
       view distribution across ALL `V` and complete independence of `w`!).
    2. `outerMpcWitnessShiftEquiv` gives an explicit constructive bijection (no choice operator)
       between the `w₁`-fiber and the `w₂`-fiber preserving `custodianJointView` identically! -/
def cozk_outer_mpc_one_custodian_perfect_key_privacy
    (c : Fin 3) (e : Fin 219 → Fin 3)
    (w₁ w₂ : BitVec 256) (V : CustodianJointView 256 219) :
    SimpleEquiv
      (HonestOuterMaskSpace 256 219)
      { cfg : OuterMpcConfig 256 219 //
          ValidOuterMpcConfig 256 219 w₁ cfg ∧ custodianJointView 256 219 c e cfg = V } ×
    SimpleEquiv
      { cfg : OuterMpcConfig 256 219 //
          ValidOuterMpcConfig 256 219 w₁ cfg ∧ custodianJointView 256 219 c e cfg = V }
      { cfg : OuterMpcConfig 256 219 //
          ValidOuterMpcConfig 256 219 w₂ cfg ∧ custodianJointView 256 219 c e cfg = V } :=
  (outerMpcViewFiberEquiv 256 219 w₁ c e V,
   outerMpcWitnessShiftEquiv 256 219 w₁ w₂ c e V)

/-- Explicit 1-repetition private-key extractor against legacy direct-head custodian assignment. -/
def recoverKeyFromDirectHeadAssignment {wBits : Nat} (c er : Fin 3)
    (ownHeldHeads openedHeads : BitVec wBits × BitVec wBits) : BitVec wBits :=
  if er = nextFin3 c then
    (ownHeldHeads.1 ^^^ ownHeldHeads.2) ^^^ openedHeads.2
  else
    (ownHeldHeads.1 ^^^ ownHeldHeads.2) ^^^ openedHeads.1

/-- **`#tooth` Direct-Head Assignment Single-Repetition Key Leak (`tooth_direct_head_assignment_leaks_key_in_one_rep`)**:
    If physical custodian `c` directly holds virtual heads `(v_c, v_{c+1})` without outer-MPC 3-of-3
    masking, then on ANY repetition where `e_r ≠ c` (`2/3` probability in 1 repetition!), `c` observes
    the third virtual head share and deterministically recovers the full private key `w = v_0 ⊕ v_1 ⊕ v_2`! -/
theorem tooth_direct_head_assignment_leaks_key_in_one_rep
    {wBits : Nat} (w : BitVec wBits) (v : Fin 3 → BitVec wBits)
    (hValid : (v ⟨0, by decide⟩ ^^^ v ⟨1, by decide⟩) ^^^ v ⟨2, by decide⟩ = w)
    (c er : Fin 3) (hChallengeNe : er ≠ c) :
    let ownHeld := (v c, v (nextFin3 c))
    let opened := (v er, v (nextFin3 er))
    recoverKeyFromDirectHeadAssignment c er ownHeld opened = w := by
  intro ownHeld opened
  have hPerm := bvXor_fin3_perm c v
  rw [hValid] at hPerm
  unfold recoverKeyFromDirectHeadAssignment
  if hNext : er = nextFin3 c then
    have hNext2 : nextFin3 (nextFin3 c) = thirdFin3 c := by
      rcases c with ⟨ci, hci⟩
      rcases (show ci = 0 ∨ ci = 1 ∨ ci = 2 by omega) with rfl | rfl | rfl <;> rfl
    simp only [hNext, ↓reduceIte, ownHeld, opened, hNext2]
    exact hPerm.symm
  else
    have hThird : er = thirdFin3 c := by
      rcases c with ⟨ci, hci⟩; rcases er with ⟨ei, hei⟩
      rcases (show ci = 0 ∨ ci = 1 ∨ ci = 2 by omega) with rfl | rfl | rfl <;>
        rcases (show ei = 0 ∨ ei = 1 ∨ ei = 2 by omega) with rfl | rfl | rfl <;>
        simp_all [nextFin3, thirdFin3]
    have hNe3 : thirdFin3 c ≠ nextFin3 c := (fin3_cases_disjoint c).2.2
    simp only [ownHeld, opened, hThird, hNe3, ↓reduceIte]
    exact hPerm.symm

/-- Inhabitedness witness for `cozk_outer_mpc_one_custodian_perfect_key_privacy` and `zkboo_219_soundness_lt_two_pow_neg128`. -/
theorem witness_cozk_outer_mpc_inhabited :
    let w : BitVec 256 := 42#256
    let c : Fin 3 := ⟨0, by decide⟩
    let e : Fin 219 → Fin 3 := fun _ => ⟨1, by decide⟩
    let V : CustodianJointView 256 219 :=
      { ownKeyShare := 0#256
        ownHeadMasks := fun _ _ => 0#256
        openedVirtualHeads := fun _ => (0#256, 0#256) }
    ∃ cfg : OuterMpcConfig 256 219,
      ValidOuterMpcConfig 256 219 w cfg ∧
      custodianJointView 256 219 c e cfg = V := by
  intro w c e V
  let item := (outerMpcViewFiberEquiv 256 219 w c e V).toFun (0#256, fun _ _ => 0#256)
  exact ⟨item.1, item.2⟩

/-! ### §4c. Pre-Open Batch Beaver/BBCGGI19 Multiplication & Conversion Sacrifice Gate -/

/-- Phase discipline for active 3-of-3 outer-MPC Co-ZK ceremony gating head openings behind
    frozen ceremony root commitment and batch multiplication/conversion sacrifice. -/
inductive CoZkCeremonyPhase where
  | awaitingRootFreeze
  | rootFrozen (ceremonyRoot : List UInt8) (sacrificeCoin1 sacrificeCoin2 : Tower128)
  | sacrificeVerified (ceremonyRoot : List UInt8)
  | headsReleased (ceremonyRoot : List UInt8)
  | aborted
  deriving DecidableEq

/-- Persistent per-ceremony state enforcing single-shot execution and irreversible abort on fault. -/
structure CoZkCeremonyState where
  sessionTag : List UInt8
  phase : CoZkCeremonyPhase
  aborted : Bool
  deriving DecidableEq

/-- Candidate transitions of the pre-open sacrifice ceremony machine. -/
inductive CoZkCeremonyInput where
  | freezeCeremonyRoot
      (statementBytes : List UInt8)
      (repCommitDigests : List (List UInt8))
      (coin1 coin2 : Tower128)
  | verifyPreOpenSacrifice
      (rssCheckMsg : RssActiveOpenMsg)
      (gateDeltas : List Tower128)
  | releaseChallengedHeads
      (ceremonyRoot : List UInt8)
      (openedHeadsDigest : List UInt8)
  deriving DecidableEq

/-- Publicly observable events emitted on accepted ceremony steps. -/
inductive CoZkCeremonyEvent where
  | ceremonyRootFrozen (ceremonyRoot : List UInt8)
  | preOpenSacrificePassed (ceremonyRoot : List UInt8) (checkedGateCount : Nat)
  | challengedHeadsReleased (ceremonyRoot : List UInt8) (openedHeadsDigest : List UInt8)
  deriving DecidableEq, Repr

/-- Rejection and quarantine reasons of `cozkOrderingEvidenceStep`. -/
inductive CoZkCeremonyReject where
  | ceremonyAlreadyAborted
  | preOpenSacrificeFailed
  | rootMismatchOnOpen
  | invalidPhaseTransition
  deriving DecidableEq, Repr

/-- Exact ASCII domain tag `"QSAG.MIGRATE.ROOT.V3"` (`20` bytes). -/
def migrateRootDomain : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x4D, 0x49, 0x47, 0x52, 0x41, 0x54, 0x45, 0x2E,
   0x52, 0x4F, 0x4F, 0x54, 0x2E, 0x56, 0x33]

/-- Active pre-open outer-MPC ceremony step gating ZKBoo head-view release strictly behind:
    1. Freezing the 219-repetition ceremony commitment root (`QSAG.MIGRATE.ROOT.V3` + `encodeFramedU64Le`),
    2. 2-of-3 replicated holder cross-check (`verifyRssActiveOpen rssMsg == some 0`), and
    3. Vanishing of two independent `Tower128` batch multiplication/conversion sacrifice polynomials. -/
def cozkOrderingEvidenceStep (H : Hash)
    (st : CoZkCeremonyState) (inp : CoZkCeremonyInput) :
    CustodyStepOutcome CoZkCeremonyState CoZkCeremonyEvent CoZkCeremonyReject :=
  if st.aborted then
    .rejected { st with phase := .aborted, aborted := true } .ceremonyAlreadyAborted
  else
    match st.phase, inp with
    | .awaitingRootFreeze, .freezeCeremonyRoot stmtBytes repCommits coin1 coin2 =>
      let root := H (encodeFramedU64Le (migrateRootDomain ::
                      st.sessionTag :: stmtBytes :: repCommits))
      .accepted { st with phase := .rootFrozen root coin1 coin2 } (.ceremonyRootFrozen root)
    | .rootFrozen root coin1 coin2, .verifyPreOpenSacrifice rssMsg gateDeltas =>
      if verifyRssActiveOpen rssMsg == some 0 &&
         batchDeviationPoly gateDeltas coin1 == towerZero 7 &&
         batchDeviationPoly gateDeltas coin2 == towerZero 7 then
        .accepted { st with phase := .sacrificeVerified root }
          (.preOpenSacrificePassed root gateDeltas.length)
      else
        .rejected { st with phase := .aborted, aborted := true } .preOpenSacrificeFailed
    | .sacrificeVerified root, .releaseChallengedHeads reqRoot openedDigest =>
      if reqRoot == root then
        .accepted { st with phase := .headsReleased root }
          (.challengedHeadsReleased root openedDigest)
      else
        .rejected { st with phase := .aborted, aborted := true } .rootMismatchOnOpen
    | _, _ =>
      .rejected { st with phase := .aborted, aborted := true } .invalidPhaseTransition

/-- Count how many `.challengedHeadsReleased` events appear in a ceremony event list. -/
def cozkCountHeadReleases : List CoZkCeremonyEvent → Nat
  | [] => 0
  | .challengedHeadsReleased _ _ :: rest => 1 + cozkCountHeadReleases rest
  | _ :: rest => cozkCountHeadReleases rest

private theorem cozk_aborted_releases_nothing {H : Hash}
    {st stFinal : CoZkCeremonyState}
    {trace : List (CoZkCeremonyInput × Option CoZkCeremonyEvent)}
    (hAb : st.aborted = true)
    (hTr : ValidCustodyTrace (cozkOrderingEvidenceStep H) st trace stFinal) :
    stFinal.aborted = true ∧ traceApprovedOutputs trace = [] := by
  induction hTr with
  | nil => exact ⟨hAb, rfl⟩
  | consAccepted hStep _ _ =>
    unfold cozkOrderingEvidenceStep at hStep
    simp [hAb] at hStep
  | consRejected hStep _ ih =>
    unfold cozkOrderingEvidenceStep at hStep
    simp only [hAb, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
    rcases hStep with ⟨rfl, _⟩
    simpa using ih rfl

private theorem cozk_headsReleased_emits_nothing {H : Hash}
    {st stFinal : CoZkCeremonyState} {r : List UInt8}
    {trace : List (CoZkCeremonyInput × Option CoZkCeremonyEvent)}
    (hPh : st.phase = .headsReleased r)
    (hTr : ValidCustodyTrace (cozkOrderingEvidenceStep H) st trace stFinal) :
    traceApprovedOutputs trace = [] := by
  cases hTr with
  | nil => rfl
  | @consAccepted _ _ _ inp _ _ hStep _ =>
    unfold cozkOrderingEvidenceStep at hStep
    if hAb : st.aborted = true then
      simp [hAb] at hStep
    else
      simp only [hAb, Bool.false_eq_true, ↓reduceIte, hPh] at hStep
      cases inp <;> cases hStep
  | @consRejected _ s' _ inp _ rest hStep hRest =>
    simp only [traceApprovedOutputs_cons_none]
    unfold cozkOrderingEvidenceStep at hStep
    if hAb : st.aborted = true then
      simp only [hAb, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
      rcases hStep with ⟨rfl, _⟩
      exact (cozk_aborted_releases_nothing rfl hRest).2
    else
      simp only [hAb, Bool.false_eq_true, ↓reduceIte, hPh] at hStep
      cases inp <;> simp only [CustodyStepOutcome.rejected.injEq] at hStep <;>
        rcases hStep with ⟨rfl, _⟩ <;>
        exact (cozk_aborted_releases_nothing rfl hRest).2

private theorem cozk_trace_ordering_and_single_release {H : Hash}
    {st stFinal : CoZkCeremonyState}
    {trace : List (CoZkCeremonyInput × Option CoZkCeremonyEvent)}
    (hTr : ValidCustodyTrace (cozkOrderingEvidenceStep H) st trace stFinal) :
    cozkCountHeadReleases (traceApprovedOutputs trace) ≤ 1 ∧
    (∀ rOut dig,
      .challengedHeadsReleased rOut dig ∈ traceApprovedOutputs trace →
      (st.phase = .sacrificeVerified rOut ∧ st.aborted = false) ∨
      ∃ nGates, .preOpenSacrificePassed rOut nGates ∈ traceApprovedOutputs trace) := by
  induction hTr with
  | nil =>
    exact ⟨by simp [cozkCountHeadReleases], fun _ _ hm => by cases hm⟩
  | @consAccepted s s' _ inp out rest hStep hRest ih =>
    unfold cozkOrderingEvidenceStep at hStep
    if hAb : s.aborted = true then
      simp [hAb] at hStep
    else
      have hAbFalse : s.aborted = false := Bool.eq_false_iff.mpr hAb
      simp only [hAb, Bool.false_eq_true, ↓reduceIte] at hStep
      cases hPh : s.phase <;> cases inp <;> simp only [hPh] at hStep
      case awaitingRootFreeze.freezeCeremonyRoot stmtBytes repCommits coin1 coin2 =>
        simp only [CustodyStepOutcome.accepted.injEq] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        obtain ⟨hCnt, hOrd⟩ := ih
        refine ⟨by simpa [cozkCountHeadReleases] using hCnt, ?_⟩
        intro rOut dig hMem
        rcases List.mem_cons.mp hMem with hEq | hTail
        · cases hEq
        · rcases hOrd rOut dig hTail with ⟨hBad, _⟩ | ⟨nG, hnG⟩
          · cases hBad
          · exact Or.inr ⟨nG, .tail _ hnG⟩
      case rootFrozen.verifyPreOpenSacrifice root coin1 coin2 rssMsg gateDeltas =>
        split at hStep
        · simp only [CustodyStepOutcome.accepted.injEq] at hStep
          rcases hStep with ⟨rfl, rfl⟩
          obtain ⟨hCnt, hOrd⟩ := ih
          refine ⟨by simpa [cozkCountHeadReleases] using hCnt, ?_⟩
          intro rOut dig hMem
          rcases List.mem_cons.mp hMem with hEq | hTail
          · cases hEq
          · rcases hOrd rOut dig hTail with ⟨hSv, _⟩ | ⟨nG, hnG⟩
            · injection hSv with hRootEq
              subst hRootEq
              exact Or.inr ⟨gateDeltas.length, .head _⟩
            · exact Or.inr ⟨nG, .tail _ hnG⟩
        · cases hStep
      case sacrificeVerified.releaseChallengedHeads root reqRoot openedDigest =>
        split at hStep
        · simp only [CustodyStepOutcome.accepted.injEq] at hStep
          rcases hStep with ⟨rfl, rfl⟩
          have hEmptyRest : traceApprovedOutputs rest = [] :=
            cozk_headsReleased_emits_nothing rfl hRest
          refine ⟨by simp [cozkCountHeadReleases, hEmptyRest], ?_⟩
          intro rOut dig hMem
          simp only [traceApprovedOutputs_cons_some, hEmptyRest, List.mem_singleton] at hMem
          cases hMem
          exact Or.inl ⟨rfl, hAbFalse⟩
        · cases hStep
      all_goals cases hStep
  | @consRejected s s' _ inp err rest hStep hRest _ =>
    simp only [traceApprovedOutputs_cons_none]
    unfold cozkOrderingEvidenceStep at hStep
    if hAb : s.aborted = true then
      simp only [hAb, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
      rcases hStep with ⟨rfl, _⟩
      have hEmpty := (cozk_aborted_releases_nothing rfl hRest).2
      exact ⟨by simp [hEmpty, cozkCountHeadReleases], fun _ _ hm => by simp [hEmpty] at hm⟩
    else
      simp only [hAb, Bool.false_eq_true, ↓reduceIte] at hStep
      have hNextAb : s'.aborted = true := by
        cases hPh : s.phase <;> cases inp <;> simp only [hPh] at hStep
        case awaitingRootFreeze.freezeCeremonyRoot =>
          cases hStep
        case rootFrozen.verifyPreOpenSacrifice =>
          split at hStep
          · cases hStep
          · simp only [CustodyStepOutcome.rejected.injEq] at hStep
            rcases hStep with ⟨rfl, _⟩
            rfl
        case sacrificeVerified.releaseChallengedHeads =>
          split at hStep
          · cases hStep
          · simp only [CustodyStepOutcome.rejected.injEq] at hStep
            rcases hStep with ⟨rfl, _⟩
            rfl
        all_goals
          simp only [CustodyStepOutcome.rejected.injEq] at hStep
          rcases hStep with ⟨rfl, _⟩
          rfl
      have hEmpty := (cozk_aborted_releases_nothing hNextAb hRest).2
      exact ⟨by simp [hEmpty, cozkCountHeadReleases], fun _ _ hm => by simp [hEmpty] at hm⟩

/-- **Pre-Open Batch Beaver/BBCGGI19 Multiplication & Conversion Sacrifice Soundness
    (`cozk_pre_open_mul_sacrifice_blocks_corrupted_head_release`)**:
    1. **Strict Pre-Open Sacrifice Ordering & Single-Use Consumption**: Across ANY multi-step trace
       from `.awaitingRootFreeze`, at most `1` `.challengedHeadsReleased` event is ever emitted, and
       zero challenged head views are ever released unless `.preOpenSacrificePassed` accepted on the
       exact frozen ceremony root.
    2. **Irreversible Abort & 2-of-3 Replicated Cross-Check Soundness**: Any failed sacrifice check
       irreversibly aborts the ceremony (`aborted = true`), and any accepted `verifyPreOpenSacrifice`
       step enforces `verifyRssActiveOpen rssMsg = some 0` (which against `≤ 1` corrupt custodian
       forces `reconstructRssWord trueShares = 0` with `0` error!) together with vanishing of both
       `Tower128` sacrifice polynomials.
    3. **Batch Multiplication / A2B-B2A Schwartz-Zippel Soundness (`< 2^-130 < 2^-128`)**: For ANY
       circuit of `L ≤ 2 ^ 63` outer-MPC multiplication / conversion gates with at least one faulted
       gate (`∃ d ∈ gateDeltas, d ≠ towerZero 7`), at most `L` single-coin challenges in any `Nodup`
       `Tower128` domain accept, and the 2-coin cheating bound satisfies
       `ratLe (L * L, 2 ^ 128 * 2 ^ 128) (1, 2 ^ 130)` (`< 2^-128`). -/
theorem cozk_pre_open_mul_sacrifice_blocks_corrupted_head_release_evidence (H : Hash) :
    (∀ (tag : List UInt8) (stFinal : CoZkCeremonyState)
       (trace : List (CoZkCeremonyInput × Option CoZkCeremonyEvent)),
      let st₀ : CoZkCeremonyState := { sessionTag := tag, phase := .awaitingRootFreeze, aborted := false }
      ValidCustodyTrace (cozkOrderingEvidenceStep H) st₀ trace stFinal →
      cozkCountHeadReleases (traceApprovedOutputs trace) ≤ 1 ∧
      (∀ rOut dig,
        .challengedHeadsReleased rOut dig ∈ traceApprovedOutputs trace →
        ∃ nGates, .preOpenSacrificePassed rOut nGates ∈ traceApprovedOutputs trace)) ∧
    (∀ (st st' : CoZkCeremonyState) (rssMsg : RssActiveOpenMsg)
       (gateDeltas : List Tower128) (ev : CoZkCeremonyEvent)
       (trueCheckShares : RssWord64) (corruptIdx : Nat),
      (corruptIdx ≠ 0 → rssMsg.p0_x0 = trueCheckShares.x0 ∧ rssMsg.p0_x1 = trueCheckShares.x1) →
      (corruptIdx ≠ 1 → rssMsg.p1_x1 = trueCheckShares.x1 ∧ rssMsg.p1_x2 = trueCheckShares.x2) →
      (corruptIdx ≠ 2 → rssMsg.p2_x2 = trueCheckShares.x2 ∧ rssMsg.p2_x0 = trueCheckShares.x0) →
      cozkOrderingEvidenceStep H st (.verifyPreOpenSacrifice rssMsg gateDeltas) = .accepted st' ev →
      reconstructRssWord trueCheckShares = 0 ∧
      ∃ root coin1 coin2,
        st.phase = .rootFrozen root coin1 coin2 ∧
        batchDeviationPoly gateDeltas coin1 = towerZero 7 ∧
        batchDeviationPoly gateDeltas coin2 = towerZero 7) ∧
    (∀ (L : Nat) (gateDeltas S : List Tower128),
      L ≤ 2 ^ 63 →
      S.Nodup →
      gateDeltas.length ≤ L →
      L + 1 ≤ S.length →
      (∃ d ∈ gateDeltas, d ≠ towerZero 7) →
      (S.filter (fun r => decide (batchDeviationPoly gateDeltas r = towerZero 7))).length ≤ L ∧
      ratLe (L * L, 2 ^ 128 * 2 ^ 128) (1, 2 ^ 130)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro tag stFinal trace st₀ hTr
    obtain ⟨hCnt, hOrd⟩ := cozk_trace_ordering_and_single_release hTr
    refine ⟨hCnt, ?_⟩
    intro rOut dig hMem
    rcases hOrd rOut dig hMem with ⟨hBad, _⟩ | hOk
    · cases hBad
    · exact hOk
  · intro st st' rssMsg gateDeltas ev trueShares corruptIdx hH0 hH1 hH2 hStep
    unfold cozkOrderingEvidenceStep at hStep
    if hAb : st.aborted = true then
      simp [hAb] at hStep
    else
      simp only [hAb, Bool.false_eq_true, ↓reduceIte] at hStep
      cases hPh : st.phase <;> simp only [hPh] at hStep
      case rootFrozen root coin1 coin2 =>
        split at hStep
        · rename_i hChecks
          rcases Bool.and_eq_true_iff.mp hChecks with ⟨h01, hC2⟩
          rcases Bool.and_eq_true_iff.mp h01 with ⟨hRss, hC1⟩
          have hOpen0 : verifyRssActiveOpen rssMsg = some 0 := eq_of_beq hRss
          have hTrue0 : (0 : UInt64) = reconstructRssWord trueShares :=
            rss_flnw_active_open_sound trueShares rssMsg corruptIdx 0 hH0 hH1 hH2 hOpen0
          exact ⟨hTrue0.symm, root, coin1, coin2, rfl, eq_of_beq hC1, eq_of_beq hC2⟩
        · cases hStep
      all_goals cases hStep
  · intro L gateDeltas S hL63 hNodup hLen hDom hNonzero
    have hRoots := (bdoz_2lane_mac_soundness L gateDeltas S hNodup hLen hDom hNonzero).1
    have hDenPos : 0 < (2 : Nat) ^ 128 * 2 ^ 128 := by decide
    have hTargetPos : 0 < (2 : Nat) ^ 130 := by decide
    have hSq : L * L ≤ 2 ^ 63 * 2 ^ 63 := Nat.mul_le_mul hL63 hL63
    have hScaled : L * L * 2 ^ 130 ≤ 2 ^ 63 * 2 ^ 63 * 2 ^ 130 :=
      Nat.mul_le_mul_right (2 ^ 130) hSq
    have hExactPow : (2 : Nat) ^ 63 * 2 ^ 63 * 2 ^ 130 = 1 * (2 ^ 128 * 2 ^ 128) := by decide
    rw [hExactPow] at hScaled
    exact ⟨hRoots, ⟨hDenPos, hTargetPos, hScaled⟩⟩

/-- **`#tooth` Unverified Outer Multiplication Selective-Failure Key-Bit Leak
    (`tooth_unverified_outer_mul_selective_fault_leaks_key_bit`)**:
    In passive 3-of-3 XOR sharing (`w_bit = w0 ^^ w1 ^^ w2`, `guard = y0 ^^ y1 ^^ y2 = false`),
    an honest AND gate `(w0 ^^ w1 ^^ w2) && (y0 ^^ y1 ^^ y2)` always outputs `false` (leaking `0`
    bits of unknown share `w2`), whereas if corrupt custodian `0` flips ONLY `y0 ↦ !y0` inside an
    unverified multiplication gate without pre-open sacrifice, the opened gate output equals the
    secret witness bit `w0 ^^ w1 ^^ w2` identically! -/
theorem tooth_unverified_outer_mul_selective_fault_leaks_key_bit
    (w0 w1 w2 y0 y1 y2 : Bool)
    (hZeroGuard : ((y0 ^^ y1) ^^ y2) = false) :
    (((w0 ^^ w1) ^^ w2) && ((y0 ^^ y1) ^^ y2)) = false ∧
    (((w0 ^^ w1) ^^ w2) && (((!y0) ^^ y1) ^^ y2)) = ((w0 ^^ w1) ^^ w2) := by
  revert hZeroGuard
  cases w0 <;> cases w1 <;> cases w2 <;> cases y0 <;> cases y1 <;> cases y2 <;> decide

private theorem evalCoeffs_replicate_zero_tower128 :
    ∀ (k : Nat) (r : Tower128),
      RoundPoly.evalCoeffs (List.replicate k (towerZero 7)) r = towerZero 7
  | 0, _ => rfl
  | k + 1, r => by
    change towerAdd 7 (towerZero 7)
      (towerMul 7 r (RoundPoly.evalCoeffs (List.replicate k (towerZero 7)) r)) = towerZero 7
    rw [evalCoeffs_replicate_zero_tower128 k r, towerMul_zero, towerAdd_zero]

/-- **`#tooth` Non-Zero Multiplication Gate Deviation Aborts Ceremony (`tooth_cozk_nonzero_gate_delta_aborts_ceremony`)**:
    When a faulted outer-MPC multiplication gate produces a non-zero residual
    `gateDeltas = [towerOne 7, towerZero 7, towerZero 7]`, `cozkOrderingEvidenceStep`
    evaluates `batchDeviationPoly` at non-zero sacrifice coin `coin1 = towerOne 7`, detects
    `towerOne 7 ≠ towerZero 7`, rejects with `.preOpenSacrificeFailed`, and irreversibly sets `aborted = true`! -/
theorem tooth_cozk_nonzero_gate_delta_aborts_ceremony (H : Hash) :
    let s0 : UInt64 := 0x123456789ABCDEF0
    let s1 : UInt64 := 0x0FEDCBA987654321
    let s2 : UInt64 := s0 ^^^ s1
    let rss : RssActiveOpenMsg :=
      { p0_x0 := s0, p0_x1 := s1, p1_x1 := s1, p1_x2 := s2, p2_x2 := s2, p2_x0 := s0 }
    let coin1 : Tower128 := towerOne 7
    let coin2 : Tower128 := (towerZero 6, towerOne 6)
    let st : CoZkCeremonyState :=
      { sessionTag := [0x09], phase := .rootFrozen [0xAA] coin1 coin2, aborted := false }
    let faultedGates : List Tower128 := [towerOne 7, towerZero 7, towerZero 7]
    cozkOrderingEvidenceStep H st (.verifyPreOpenSacrifice rss faultedGates) =
      .rejected { st with phase := .aborted, aborted := true } .preOpenSacrificeFailed := by
  intro s0 s1 s2 rss coin1 coin2 st faultedGates
  have hRssB : (verifyRssActiveOpen rss == some 0) = true := by decide
  have hDevFault : batchDeviationPoly faultedGates coin1 = towerOne 7 := by
    have hZ2 : RoundPoly.evalCoeffs [towerZero 7, towerZero 7] coin1 = towerZero 7 :=
      evalCoeffs_replicate_zero_tower128 2 coin1
    have hStep1 : RoundPoly.evalCoeffs [towerOne 7, towerZero 7, towerZero 7] coin1 = towerOne 7 := by
      change towerAdd 7 (towerOne 7) (towerMul 7 coin1 (RoundPoly.evalCoeffs [towerZero 7, towerZero 7] coin1)) = towerOne 7
      rw [hZ2, towerMul_zero, towerAdd_zero]
    change towerAdd 7 (towerZero 7) (towerMul 7 (towerOne 7) (RoundPoly.evalCoeffs [towerOne 7, towerZero 7, towerZero 7] coin1)) = towerOne 7
    rw [hStep1, towerMul_one, towerZero_add]
  have hNe10 : (towerOne 7 == towerZero 7) = false := by decide
  have hDevB : (batchDeviationPoly faultedGates coin1 == towerZero 7) = false := by
    rw [hDevFault]; exact hNe10
  unfold cozkOrderingEvidenceStep
  dsimp only [st]
  rw [hRssB, hDevB]
  rfl

/-- Non-trivial inhabitedness witness for `cozkOrderingEvidenceStep` and
    `cozk_pre_open_mul_sacrifice_blocks_corrupted_head_release` over concrete 256-bit `shake256Xof 32`,
    non-zero 2-of-3 RSS shares summing to `0`, distinct non-zero `Tower128` sacrifice coins `coin1 ≠ coin2`,
    and a non-empty 3-gate multiplication batch (`checkedGateCount = 3`). -/
theorem witness_cozk_pre_open_ceremony_inhabited :
    let H : Hash := shake256Xof 32
    let st₀ : CoZkCeremonyState :=
      { sessionTag := [0x09], phase := .awaitingRootFreeze, aborted := false }
    let coin1 : Tower128 := towerOne 7
    let coin2 : Tower128 := (towerZero 6, towerOne 6)
    (H [0x00]).length = 32 ∧
    H [0x00] ≠ [0x00] ∧
    coin1 ≠ towerZero 7 ∧
    coin2 ≠ towerZero 7 ∧
    coin1 ≠ coin2 ∧
    ∃ trace stFinal root,
      ValidCustodyTrace (cozkOrderingEvidenceStep H) st₀ trace stFinal ∧
      traceApprovedOutputs trace =
        [.ceremonyRootFrozen root,
         .preOpenSacrificePassed root 3,
         .challengedHeadsReleased root [0x77]] ∧
      cozkCountHeadReleases (traceApprovedOutputs trace) = 1 ∧
      stFinal.aborted = false := by
  intro H st₀ coin1 coin2
  have hLen32 : (H [0x00]).length = 32 := shake256Xof_length 32 [0x00]
  have hNotId : H [0x00] ≠ [0x00] := by
    intro hEq
    have hL := congrArg List.length hEq
    rw [hLen32] at hL
    cases hL
  have hc1Nz : coin1 ≠ towerZero 7 :=
    fun h => by cases congrArg (fun p : TowerElem 7 => p.1.1.1.1.1.1.1) h
  have hc2Nz : coin2 ≠ towerZero 7 :=
    fun h => by cases congrArg (fun p : TowerElem 7 => p.2.1.1.1.1.1.1) h
  have hc12Ne : coin1 ≠ coin2 :=
    fun h => by cases congrArg (fun p : TowerElem 7 => p.1.1.1.1.1.1.1) h
  refine ⟨hLen32, hNotId, hc1Nz, hc2Nz, hc12Ne, ?_⟩
  let sh0 : UInt64 := 0x123456789ABCDEF0
  let sh1 : UInt64 := 0x0FEDCBA987654321
  let sh2 : UInt64 := sh0 ^^^ sh1
  let honestRss : RssActiveOpenMsg :=
    { p0_x0 := sh0, p0_x1 := sh1, p1_x1 := sh1, p1_x2 := sh2, p2_x2 := sh2, p2_x0 := sh0 }
  let honestGates : List Tower128 := [towerZero 7, towerZero 7, towerZero 7]
  let root := H (encodeFramedU64Le [migrateRootDomain, [0x09], [0x01], [0x02]])
  let s1 : CoZkCeremonyState := { sessionTag := [0x09], phase := .rootFrozen root coin1 coin2, aborted := false }
  let s2 : CoZkCeremonyState := { sessionTag := [0x09], phase := .sacrificeVerified root, aborted := false }
  let s3 : CoZkCeremonyState := { sessionTag := [0x09], phase := .headsReleased root, aborted := false }
  have hStep1 : cozkOrderingEvidenceStep H st₀ (.freezeCeremonyRoot [0x01] [[0x02]] coin1 coin2) =
      .accepted s1 (.ceremonyRootFrozen root) := rfl
  have hStep2 : cozkOrderingEvidenceStep H s1 (.verifyPreOpenSacrifice honestRss honestGates) =
      .accepted s2 (.preOpenSacrificePassed root 3) := by
    have hRssB : (verifyRssActiveOpen honestRss == some 0) = true := by decide
    have hDev1 : batchDeviationPoly honestGates coin1 = towerZero 7 :=
      evalCoeffs_replicate_zero_tower128 4 coin1
    have hDev2 : batchDeviationPoly honestGates coin2 = towerZero 7 :=
      evalCoeffs_replicate_zero_tower128 4 coin2
    have hDevB1 : (batchDeviationPoly honestGates coin1 == towerZero 7) = true :=
      beq_iff_eq.mpr hDev1
    have hDevB2 : (batchDeviationPoly honestGates coin2 == towerZero 7) = true :=
      beq_iff_eq.mpr hDev2
    unfold cozkOrderingEvidenceStep
    dsimp only [s1, s2]
    rw [hRssB, hDevB1, hDevB2]
    rfl
  have hStep3 : cozkOrderingEvidenceStep H s2 (.releaseChallengedHeads root [0x77]) =
      .accepted s3 (.challengedHeadsReleased root [0x77]) := by
    have hRootB : (root == root) = true := uint8List_beq_self root
    unfold cozkOrderingEvidenceStep
    dsimp only [s2, s3]
    rw [hRootB]
    rfl
  refine ⟨[(.freezeCeremonyRoot [0x01] [[0x02]] coin1 coin2, some (.ceremonyRootFrozen root)),
           (.verifyPreOpenSacrifice honestRss honestGates, some (.preOpenSacrificePassed root 3)),
           (.releaseChallengedHeads root [0x77], some (.challengedHeadsReleased root [0x77]))],
          s3, root, .consAccepted hStep1 (.consAccepted hStep2 (.consAccepted hStep3 (.nil s3))),
          by rfl, by rfl, by rfl⟩


/-! ## Operational custody boundary

The preceding `*EvidenceStep` machines are private-state mathematical models, retained
for source compatibility of their algebraic theorems and negative examples. Their
trace pairs contain secret inputs and are NOT network transcripts. In particular the
old scalar SPN, bitmap policy, and caller-selected sacrifice coins are not Rust
refinements. Only the operational machines below are packaged as party machines.

Secrecy here means no additional disclosure beyond explicitly declassified signatures,
commitments and masked openings. Unconditional independence of signatures from signing
keys would be false. Hash/MAC security and independent private randomness are separate
cryptographic assumptions, never inferred from byte length or a query counter.
-/

/-! ### Operational Domain-Separation Byte Constants (`0` String Literals) -/

/-- Exact ASCII bytes of `QSAG.POLICY.INITIATOR_AUTH_PREIMAGE.V1` (38 bytes, `0` string literals). -/
def policyInitAuthPreimageDomainV1 : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x50, 0x4F, 0x4C, 0x49, 0x43, 0x59, 0x2E, 0x49, 0x4E, 0x49, 0x54,
   0x49, 0x41, 0x54, 0x4F, 0x52, 0x5F, 0x41, 0x55, 0x54, 0x48, 0x5F, 0x50, 0x52, 0x45, 0x49, 0x4D,
   0x41, 0x47, 0x45, 0x2E, 0x56, 0x31]

/-- Exact ASCII bytes of `QSAG.POLICY.INITIATOR_AUTH_MAC.V1` (33 bytes, `0` string literals). -/
def policyInitAuthMacDomainV1 : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x50, 0x4F, 0x4C, 0x49, 0x43, 0x59, 0x2E, 0x49, 0x4E, 0x49, 0x54,
   0x49, 0x41, 0x54, 0x4F, 0x52, 0x5F, 0x41, 0x55, 0x54, 0x48, 0x5F, 0x4D, 0x41, 0x43, 0x2E, 0x56,
   0x31]

/-- Exact ASCII bytes of `QSAG.POLICY.WINDOW_ADVANCE/v1` (29 bytes, `0` string literals). -/
def policyWindowAdvanceDomainV1 : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x50, 0x4F, 0x4C, 0x49, 0x43, 0x59, 0x2E, 0x57, 0x49, 0x4E, 0x44,
   0x4F, 0x57, 0x5F, 0x41, 0x44, 0x56, 0x41, 0x4E, 0x43, 0x45, 0x2F, 0x76, 0x31]

/-- Exact ASCII bytes of `QSAG.MIGRATE.CHECKED_HEADS.V1` (29 bytes, `0` string literals). -/
def cozkCheckedHeadsDomainV1 : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x4D, 0x49, 0x47, 0x52, 0x41, 0x54, 0x45, 0x2E, 0x43, 0x48, 0x45,
   0x43, 0x4B, 0x45, 0x44, 0x5F, 0x48, 0x45, 0x41, 0x44, 0x53, 0x2E, 0x56, 0x31]

/-- Exact ASCII bytes of `QSAG.MIGRATE.HEAD_COMMIT.V1` (27 bytes, `0` string literals). -/
def cozkHeadCommitDomainV1 : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x4D, 0x49, 0x47, 0x52, 0x41, 0x54, 0x45, 0x2E, 0x48, 0x45, 0x41,
   0x44, 0x5F, 0x43, 0x4F, 0x4D, 0x4D, 0x49, 0x54, 0x2E, 0x56, 0x31]

/-- Exact ASCII bytes of `QSAG.PSFTS.POW7_ROUND.V4` (24 bytes, `0` string literals). -/
def ftsPow7RoundDomainV4 : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2E, 0x50, 0x4F, 0x57, 0x37, 0x5F,
   0x52, 0x4F, 0x55, 0x4E, 0x44, 0x2E, 0x56, 0x34]

/-- Exact ASCII bytes of `QSAG.PSFTS.SIGN_CONTEXT.V3` (26 bytes, `0` string literals). -/
def ftsSignContextDomainV3 : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2E, 0x53, 0x49, 0x47, 0x4E, 0x5F,
   0x43, 0x4F, 0x4E, 0x54, 0x45, 0x58, 0x54, 0x2E, 0x56, 0x33]

/-- Exact ASCII bytes of `QSAG.PSFTS.HMSG.V2` (18 bytes, `0` string literals). -/
def ftsHmsgDomainV2 : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2E, 0x48, 0x4D, 0x53, 0x47, 0x2E,
   0x56, 0x32]

/-- Run an operational transition, retaining rejection observations (`none`) while emitting
    only explicitly declassified public wire events (`some out`). -/
def custodyWireTrace {S In Out Err : Type} (step : S → In → CustodyStepOutcome S Out Err) :
    S → List In → List (Option Out)
  | _, [] => []
  | s, i :: rest =>
    match step s i with
    | .accepted s' out => some out :: custodyWireTrace step s' rest
    | .rejected s' _ => none :: custodyWireTrace step s' rest

/-! ### §A. Operational Authenticated Policy, Authoritative Timestamp, Window Rotation & Quorum-Switching Spend-Cap -/

/-- Sparse sorted set with an inclusive permanent eviction floor (Rust's nonce & session burn sets). -/
structure PolicyBurnSet where
  floor : Option Nat := none
  values : List Nat := []
  deriving DecidableEq, Repr

/-- Computable Boolean membership test for `PolicyBurnSet`. -/
def policyIsBurned (s : PolicyBurnSet) (v : Nat) : Bool :=
  match s.floor with
  | some f => decide (v ≤ f) || decide (v ∈ s.values)
  | none => decide (v ∈ s.values)

/-- Propositional wrapper for `policyIsBurned` (automatically `Decidable` without module-expose overhead). -/
abbrev policyBurned (s : PolicyBurnSet) (v : Nat) : Prop :=
  policyIsBurned s v = true

theorem policyBurned_iff (s : PolicyBurnSet) (v : Nat) :
    policyBurned s v ↔ (∃ f, s.floor = some f ∧ v ≤ f) ∨ v ∈ s.values := by
  unfold policyBurned policyIsBurned
  cases hf : s.floor with
  | none =>
    simp
  | some f =>
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (hle | hmem)
      · exact Or.inl ⟨f, rfl, hle⟩
      · exact Or.inr hmem
    · rintro (⟨f', hEq, hle⟩ | hmem)
      · cases hEq; exact Or.inl hle
      · exact Or.inr hmem

def policyInsertSorted (v : Nat) : List Nat → List Nat
  | [] => [v]
  | x :: xs =>
    if v < x then v :: x :: xs
    else if v = x then x :: xs
    else x :: policyInsertSorted v xs

def policyBurn (cap : Nat) (s : PolicyBurnSet) (v : Nat) : PolicyBurnSet :=
  if (policyInsertSorted v s.values).length ≤ cap then
    { floor := s.floor, values := policyInsertSorted v s.values }
  else
    match policyInsertSorted v s.values with
    | [] => s
    | x :: rest => { floor := some (max (s.floor.getD 0) x), values := rest }

private theorem policyInsertSorted_mem (v x : Nat) (xs : List Nat) :
    x ∈ policyInsertSorted v xs ↔ x = v ∨ x ∈ xs := by
  induction xs with
  | nil => simp [policyInsertSorted]
  | cons y ys ih =>
    unfold policyInsertSorted
    if hlt : v < y then
      simp [hlt, List.mem_cons]
    else if heq : v = y then
      subst heq
      simp only [hlt, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)
      · rintro (rfl | rfl | h)
        · exact Or.inl rfl
        · exact Or.inl rfl
        · exact Or.inr h
    else
      simp only [hlt, heq, ↓reduceIte, List.mem_cons, ih]
      constructor
      · rintro (rfl | rfl | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)
      · rintro (rfl | rfl | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)

/-- Eviction cannot resurrect an old nonce or session, even if the caller supplied
    an already burned value. This lemma does not assume a sorted input state. -/
theorem policyBurn_persistent (cap : Nat) (s : PolicyBurnSet) (v x : Nat)
    (h : policyBurned s x) : policyBurned (policyBurn cap s v) x := by
  rw [policyBurned_iff] at h ⊢
  unfold policyBurn
  if hLen : (policyInsertSorted v s.values).length ≤ cap then
    simp only [hLen, ↓reduceIte]
    rcases h with hfl | hmem
    · exact Or.inl hfl
    · exact Or.inr ((policyInsertSorted_mem v x s.values).2 (Or.inr hmem))
  else
    simp only [hLen, ↓reduceIte]
    cases he : policyInsertSorted v s.values with
    | nil => exact h
    | cons y ys =>
      dsimp only
      rcases h with ⟨f, hf, hx⟩ | hx
      · apply Or.inl
        refine ⟨max (s.floor.getD 0) y, rfl, ?_⟩
        rw [hf]
        exact Nat.le_trans hx (Nat.le_max_left f y)
      · have hm := (policyInsertSorted_mem v x s.values).2 (Or.inr hx)
        rw [he] at hm
        rcases List.mem_cons.mp hm with hxy | htail
        · subst x
          exact Or.inl ⟨max (s.floor.getD 0) y, rfl, Nat.le_max_right _ _⟩
        · exact Or.inr htail

/-- An approving step burns the new identifier as well as preserving older ones. -/
theorem policyBurn_marks (cap : Nat) (s : PolicyBurnSet) (v : Nat) :
    policyBurned (policyBurn cap s v) v := by
  rw [policyBurned_iff]
  have hm := (policyInsertSorted_mem v v s.values).2 (Or.inl rfl)
  unfold policyBurn
  if hLen : (policyInsertSorted v s.values).length ≤ cap then
    simp only [hLen, ↓reduceIte]
    exact Or.inr hm
  else
    simp only [hLen, ↓reduceIte]
    cases he : policyInsertSorted v s.values with
    | nil => rw [he] at hm; cases hm
    | cons x xs =>
      dsimp only
      rw [he] at hm
      rcases List.mem_cons.mp hm with hv | hv
      · subst v
        exact Or.inl ⟨max (s.floor.getD 0) x, rfl, Nat.le_max_right _ _⟩
      · exact Or.inr hv

structure InitiatorPeerTag where
  approver : Nat
  tag : List UInt8
  deriving DecidableEq, Repr

structure PolicyWindowAuthorization where
  newWindow : Nat
  mac : List UInt8
  deriving DecidableEq, Repr

/-- Enrolled keys and validity bounds are durable custodian state, never supplied by an unauthenticated caller. -/
structure AuthenticatedPolicyState where
  rules : StatefulPolicyGuard
  party : Nat
  chain : Nat
  suite : Nat
  pairwiseKeys : List (Nat × List UInt8)
  windowKey : List UInt8
  policyId : List UInt8
  validNotBeforeSecs : Nat := 0
  validNotAfterSecs : Nat := 256 ^ 8 - 1
  forbidSelfApproval : Bool := true
  externalSpendFloor : Nat := 0
  nonceBurns : PolicyBurnSet := {}
  sessionBurns : PolicyBurnSet := {}
  burnCapacity : Nat := 256
  deriving DecidableEq, Repr

def policyInitiatorAuthDigest (tx : TransactionIntent) : List UInt8 :=
  cshake256Bytes policyInitAuthPreimageDomainV1
    (encodeFramedU64Le
      [tx.policy_digest, be 8 tx.chain_id, be 2 tx.suite_tag, tx.recipient_hrp,
       be 1 tx.recipient_version, be 2 tx.recipient_suite_tag, be 1 tx.recipient_kind,
       tx.recipient, be 16 tx.amount_units, be 16 tx.rolling_window_spent,
       be 8 tx.window_id, be 32 tx.nonce, be 8 tx.timestamp_secs,
       be 2 tx.initiator_party, tx.approver_bytes, tx.payload_digest,
       tx.authority_digest, tx.rolling_window_accumulator, tx.signing_key_id,
       be 8 tx.policy_revision, tx.signing_context_digest, tx.session_id, tx.quorum_bytes])

def policyInitiatorTag (key : List UInt8) (approver : Nat) (tx : TransactionIntent) : List UInt8 :=
  cshake256Bytes policyInitAuthMacDomainV1
    (encodeFramedU64Le [key, be 2 tx.initiator_party, be 2 approver, policyInitiatorAuthDigest tx])

theorem policyInitiatorTag_length (key : List UInt8) (approver : Nat) (tx : TransactionIntent) :
    (policyInitiatorTag key approver tx).length = 32 :=
  cshake256Bytes_length _ _

def policyWindowTag (g : AuthenticatedPolicyState) (next : Nat) : List UInt8 :=
  cshake256Bytes policyWindowAdvanceDomainV1
    (encodeFramedU64Le [g.windowKey, g.policyId, be 8 g.rules.window_id, be 8 next])

def policyInsertTag (t : InitiatorPeerTag) : List InitiatorPeerTag → List InitiatorPeerTag
  | [] => [t]
  | x :: xs => if t.approver ≤ x.approver then t :: x :: xs else x :: policyInsertTag t xs

/-- Rust sorts tags by approver before hashing; duplicates are retained so the
    per-approver authentication check can reject them. -/
def encodeInitiatorTags (tags : List InitiatorPeerTag) : List UInt8 :=
  (tags.foldr policyInsertTag []).flatMap (fun t => be 2 t.approver ++ t.tag)

/-- `approver_bytes` is a sorted sequence of big-endian u16 identifiers, matching Rust's preimage check. -/
def policyCanonicalApprovers : List UInt8 → Bool
  | [] => true
  | a :: b :: rest =>
    match rest with
    | [] => true
    | c :: d :: _ => decide (ofLE [b, a] < ofLE [d, c]) && policyCanonicalApprovers rest
    | _ => false
  | _ => false

theorem policy_duplicate_approvers_rejected (a b : UInt8) (rest : List UInt8) :
    policyCanonicalApprovers (a :: b :: a :: b :: rest) = false := by
  simp [policyCanonicalApprovers]

/-- Unique tag check for THIS approver; duplicate entries fail even when one tag is correct. -/
def policyAuthenticatedInitiator (g : AuthenticatedPolicyState) (tx : TransactionIntent)
    (tags : List InitiatorPeerTag) : Bool :=
  if tx.initiator_party == g.party then !g.forbidSelfApproval
  else
    match g.pairwiseKeys.find? (fun p => p.1 == tx.initiator_party) with
    | none => false
    | some (_, key) =>
      match tags.filter (fun t => t.approver == g.party) with
      | [t] => t.tag == policyInitiatorTag key g.party tx
      | _ => false

/-- Fixed digest sizes and bounded scalars enforced at the signing boundary. -/
def policyCheckWireDomain (tx : TransactionIntent) : Bool :=
  txFitsWireWidths { tx with message_digest := List.replicate 32 0 } &&
  decide (tx.policy_digest.length = 32 ∧ tx.authority_digest.length = 32 ∧
          tx.recipient.length = 32 ∧ tx.payload_digest.length = 32 ∧
          tx.rolling_window_accumulator.length = 32 ∧ tx.signing_key_id.length = 32 ∧
          tx.message_digest.length = 32 ∧ tx.signing_context_digest.length = 32 ∧
          tx.session_id.length = 32)

abbrev policyWireDomain (tx : TransactionIntent) : Prop :=
  policyCheckWireDomain tx = true

def policyProjectedSpend (g : AuthenticatedPolicyState) (tx : TransactionIntent) : Nat :=
  max (max g.rules.accumulated_spend tx.rolling_window_spent) g.externalSpendFloor + tx.amount_units

/-- Full operational admission check including authoritative `currentTimestamp` bounds,
    cryptographic initiator MAC verification, canonical wire bounds, and dual nonce/session burn exclusion. -/
def policyCheckAdmission (g : AuthenticatedPolicyState) (tx : TransactionIntent)
    (tags : List InitiatorPeerTag) (currentTimestamp : Nat) : Bool :=
  policyCheckWireDomain tx &&
  decide (tx.chain_id = g.chain ∧ tx.suite_tag = g.suite ∧ tx.recipient_suite_tag = g.suite) &&
  decide (g.validNotBeforeSecs ≤ currentTimestamp ∧ currentTimestamp ≤ g.validNotAfterSecs ∧
          tx.timestamp_secs = currentTimestamp) &&
  decide (tx.window_id = g.rules.window_id ∧ tx.policy_digest = g.rules.pinned_policy_digest ∧
          tx.authority_digest = g.rules.pinned_authority_digest) &&
  decide (tx.recipient ∈ g.rules.allowed_recipients ∧ tx.amount_units ≤ g.rules.per_tx_cap) &&
  decide (policyProjectedSpend g tx ≤ g.rules.velocity_window_cap ∧
          policyProjectedSpend g tx < 256 ^ 16) &&
  !policyIsBurned g.nonceBurns tx.nonce &&
  !policyIsBurned g.sessionBurns (ofLE tx.session_id.reverse) &&
  decide (encodeInitiatorTags tags = tx.init_mac_bytes) &&
  policyAuthenticatedInitiator g tx tags &&
  policyCanonicalApprovers tx.approver_bytes &&
  tags.all (fun t => decide (t.approver < 256 ^ 2 ∧ t.tag.length = 32))

abbrev PolicyAdmission (g : AuthenticatedPolicyState) (tx : TransactionIntent)
    (tags : List InitiatorPeerTag) (currentTimestamp : Nat) : Prop :=
  policyCheckAdmission g tx tags currentTimestamp = true

theorem policyAdmission_wire_and_burns {g : AuthenticatedPolicyState} {tx : TransactionIntent}
    {tags : List InitiatorPeerTag} {ts : Nat}
    (h : PolicyAdmission g tx tags ts) :
    txFitsWireWidths { tx with message_digest := List.replicate 32 0 } = true ∧
    tx.policy_digest.length = 32 ∧
    g.validNotBeforeSecs ≤ ts ∧ ts ≤ g.validNotAfterSecs ∧ tx.timestamp_secs = ts ∧
    tx.window_id = g.rules.window_id ∧
    tx.amount_units ≤ g.rules.per_tx_cap ∧
    policyProjectedSpend g tx ≤ g.rules.velocity_window_cap ∧
    ¬ policyBurned g.nonceBurns tx.nonce ∧
    ¬ policyBurned g.sessionBurns (ofLE tx.session_id.reverse) ∧
    policyAuthenticatedInitiator g tx tags = true := by
  unfold PolicyAdmission policyCheckAdmission at h
  simp only [Bool.and_eq_true, and_assoc] at h
  rcases h with ⟨hDom, _, hTs, hWinPol, hRecCap, hProj, hNb, hSb, _, hAuth, _, _⟩
  unfold policyCheckWireDomain at hDom
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hDom hTs hWinPol hRecCap hProj
  simp only [Bool.not_eq_true'] at hNb hSb
  exact ⟨hDom.1, hDom.2.1, hTs.1, hTs.2.1, hTs.2.2, hWinPol.1, hRecCap.2, hProj.1,
         (fun hc => Bool.noConfusion (hc.symm.trans hNb)),
         (fun hc => Bool.noConfusion (hc.symm.trans hSb)),
         hAuth⟩

inductive AuthenticatedPolicyInput where
  | evaluate (tx : TransactionIntent) (tags : List InitiatorPeerTag) (currentTimestamp : Nat)
  | advance (authorization : PolicyWindowAuthorization)
  deriving DecidableEq, Repr

/-- Operational single-custodian authenticated policy evaluation step emitting canonical signing bytes. -/
def authenticatedPolicyGuardStep (g : AuthenticatedPolicyState) (tx : TransactionIntent)
    (tags : List InitiatorPeerTag) (currentTimestamp : Nat) :
    CustodyStepOutcome AuthenticatedPolicyState PolicyWatermarkEvent PolicyWatermarkReject :=
  if policyCheckAdmission g tx tags currentTimestamp then
    let rules' : StatefulPolicyGuard :=
      { g.rules with accumulated_spend := policyProjectedSpend g tx }
    let g' : AuthenticatedPolicyState :=
      { g with
        rules := rules'
        nonceBurns := policyBurn g.burnCapacity g.nonceBurns tx.nonce
        sessionBurns := policyBurn g.burnCapacity g.sessionBurns (ofLE tx.session_id.reverse) }
    .accepted g' (.intentApproved tx (toCanonicalSigningBytes tx))
  else
    .rejected g .unauthenticatedInitiator

/-- Operational custodian guard supporting both authenticated evaluations and MAC-authorized window advances. -/
def policyWatermarkGuardStep (g : AuthenticatedPolicyState) (inp : AuthenticatedPolicyInput) :
    CustodyStepOutcome AuthenticatedPolicyState PolicyWatermarkEvent PolicyWatermarkReject :=
  match inp with
  | .evaluate tx tags ts => authenticatedPolicyGuardStep g tx tags ts
  | .advance auth =>
    if decide (g.rules.window_id < auth.newWindow ∧ auth.newWindow < 256 ^ 8 ∧
               auth.mac = policyWindowTag g auth.newWindow) then
      let rules' : StatefulPolicyGuard :=
        { g.rules with window_id := auth.newWindow, accumulated_spend := 0 }
      let g' : AuthenticatedPolicyState :=
        { g with rules := rules' }
      .accepted g' (.epochAdvanced auth.newWindow 0)
    else
      .rejected g .epochAdvanceTooEarly

theorem policy_window_advance_preserves_external_floor (g g' : AuthenticatedPolicyState)
    (auth : PolicyWindowAuthorization) (ev : PolicyWatermarkEvent)
    (h : policyWatermarkGuardStep g (.advance auth) = .accepted g' ev) :
    g'.externalSpendFloor = g.externalSpendFloor := by
  unfold policyWatermarkGuardStep at h
  if hc : g.rules.window_id < auth.newWindow ∧ auth.newWindow < 256 ^ 8 ∧
      auth.mac = policyWindowTag g auth.newWindow then
    simp only [hc] at h
    rcases CustodyStepOutcome.accepted.inj h with ⟨rfl, _⟩
    rfl
  else simp [hc] at h

theorem policy_approval_requires_authentication (g g' : AuthenticatedPolicyState)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (ts : Nat) (ev : PolicyWatermarkEvent)
    (h : authenticatedPolicyGuardStep g tx tags ts = .accepted g' ev) :
    PolicyAdmission g tx tags ts ∧ ev = .intentApproved tx (toCanonicalSigningBytes tx) := by
  unfold authenticatedPolicyGuardStep at h
  cases hAdm : policyCheckAdmission g tx tags ts <;> simp [hAdm] at h
  exact ⟨hAdm, h.2.symm⟩

/-- Accepted signing bytes bind `policy_digest` and all 24 non-`message_digest` intent fields
    without separate domain hypotheses (domain bounds are discharged by `authenticatedPolicyGuardStep`). -/
def policy_accepted_bytes_binding (g₁ g₂ s₁ s₂ : AuthenticatedPolicyState)
    (tx₁ tx₂ : TransactionIntent) (tags₁ tags₂ : List InitiatorPeerTag) (ts₁ ts₂ : Nat)
    (ev₁ ev₂ : PolicyWatermarkEvent)
    (h₁ : authenticatedPolicyGuardStep g₁ tx₁ tags₁ ts₁ = .accepted s₁ ev₁)
    (h₂ : authenticatedPolicyGuardStep g₂ tx₂ tags₂ ts₂ = .accepted s₂ ev₂)
    (heq : toCanonicalSigningBytes tx₁ = toCanonicalSigningBytes tx₂) :
    PSum (HashCollisionWitness (cshake256Bytes txIntentDomainTag))
      (tx₁.policy_digest = tx₂.policy_digest ∧
       { tx₁ with message_digest := List.replicate 32 0 } =
       { tx₂ with message_digest := List.replicate 32 0 }) :=
  let a := policyAdmission_wire_and_burns (policy_approval_requires_authentication _ _ _ _ _ _ h₁).1
  let b := policyAdmission_wire_and_burns (policy_approval_requires_authentication _ _ _ _ _ _ h₂).1
  toCanonicalSigningBytes_binding_or_collision tx₁ tx₂ a.2.1 b.2.1 a.1 b.1 heq

theorem policy_authorized_rotation_preserves_replay (g g' : AuthenticatedPolicyState)
    (a : PolicyWindowAuthorization) (ev : PolicyWatermarkEvent)
    (h : policyWatermarkGuardStep g (.advance a) = .accepted g' ev) :
    g.rules.window_id < g'.rules.window_id ∧ a.mac = policyWindowTag g a.newWindow ∧
    g'.nonceBurns = g.nonceBurns ∧ g'.sessionBurns = g.sessionBurns := by
  unfold policyWatermarkGuardStep at h
  if hc : g.rules.window_id < a.newWindow ∧ a.newWindow < 256 ^ 8 ∧
          a.mac = policyWindowTag g a.newWindow then
    simp only [hc] at h
    rcases CustodyStepOutcome.accepted.inj h with ⟨rfl, _⟩
    exact ⟨hc.1, hc.2.2, rfl, rfl⟩
  else
    simp [hc] at h

/-- Every accepted operational policy step preserves both kinds of previously burned identifiers. -/
theorem policy_operational_replay_persistent (s s' : AuthenticatedPolicyState)
    (inp : AuthenticatedPolicyInput) (ev : PolicyWatermarkEvent)
    (h : policyWatermarkGuardStep s inp = .accepted s' ev) (x : Nat) :
    (policyBurned s.nonceBurns x → policyBurned s'.nonceBurns x) ∧
    (policyBurned s.sessionBurns x → policyBurned s'.sessionBurns x) := by
  cases inp with
  | advance auth =>
    have hs := policy_authorized_rotation_preserves_replay s s' auth ev h
    rw [hs.2.2.1, hs.2.2.2]
    exact ⟨id, id⟩
  | evaluate tx tags ts =>
    change authenticatedPolicyGuardStep s tx tags ts = .accepted s' ev at h
    unfold authenticatedPolicyGuardStep at h
    cases hAdm : policyCheckAdmission s tx tags ts <;> simp [hAdm] at h
    rcases h with ⟨rfl, _⟩
    exact ⟨policyBurn_persistent _ _ _ x, policyBurn_persistent _ _ _ x⟩

/-- Rejected operational policy requests leave durable state unchanged. -/
theorem policy_operational_rejection_state (s s' : AuthenticatedPolicyState)
    (inp : AuthenticatedPolicyInput) (err : PolicyWatermarkReject)
    (h : policyWatermarkGuardStep s inp = .rejected s' err) : s' = s := by
  cases inp with
  | advance auth =>
    unfold policyWatermarkGuardStep at h
    if hc : s.rules.window_id < auth.newWindow ∧ auth.newWindow < 256 ^ 8 ∧
            auth.mac = policyWindowTag s auth.newWindow then
      simp [hc] at h
    else
      simp [hc] at h
      exact h.1.symm
  | evaluate tx tags ts =>
    change authenticatedPolicyGuardStep s tx tags ts = .rejected s' err at h
    unfold authenticatedPolicyGuardStep at h
    cases hAdm : policyCheckAdmission s tx tags ts <;> simp [hAdm] at h
    exact h.1.symm

/-- Burn persistence holds over arbitrary accepted, rejected, and window-rotation traces. -/
theorem policy_operational_trace_replay_persistent
    {s sf : AuthenticatedPolicyState}
    {tr : List (AuthenticatedPolicyInput × Option PolicyWatermarkEvent)}
    (h : ValidCustodyTrace policyWatermarkGuardStep s tr sf) (x : Nat) :
    (policyBurned s.nonceBurns x → policyBurned sf.nonceBurns x) ∧
    (policyBurned s.sessionBurns x → policyBurned sf.sessionBurns x) := by
  induction h with
  | nil => exact ⟨id, id⟩
  | consAccepted hs _ ih =>
    have hp := policy_operational_replay_persistent _ _ _ _ hs x
    exact ⟨fun hx => ih.1 (hp.1 hx), fun hx => ih.2 (hp.2 hx)⟩
  | consRejected hs _ ih =>
    have he := policy_operational_rejection_state _ _ _ _ hs
    subst he
    exact ih

private theorem policy_operational_burned_not_in_future
    {s sf : AuthenticatedPolicyState}
    {tr : List (AuthenticatedPolicyInput × Option PolicyWatermarkEvent)}
    (hTr : ValidCustodyTrace policyWatermarkGuardStep s tr sf) :
    (∀ x, policyBurned s.nonceBurns x →
      x ∉ (watermarkApprovedIntents (traceApprovedOutputs tr)).map (fun p => p.1.nonce)) ∧
    (∀ y, policyBurned s.sessionBurns y →
      y ∉ (watermarkApprovedIntents (traceApprovedOutputs tr)).map (fun p => ofLE p.1.session_id.reverse)) := by
  induction hTr with
  | nil =>
    exact ⟨fun _ _ hm => by simp [traceApprovedOutputs, watermarkApprovedIntents] at hm,
           fun _ _ hm => by simp [traceApprovedOutputs, watermarkApprovedIntents] at hm⟩
  | @consAccepted st st' _ inp ev rest hStep _ ih =>
    cases inp with
    | advance auth =>
      unfold policyWatermarkGuardStep at hStep
      if hc : st.rules.window_id < auth.newWindow ∧ auth.newWindow < 256 ^ 8 ∧
              auth.mac = policyWindowTag st auth.newWindow then
        simp only [hc] at hStep
        rcases CustodyStepOutcome.accepted.inj hStep with ⟨rfl, rfl⟩
        simp only [traceApprovedOutputs_cons_some, watermarkApprovedIntents]
        exact ih
      else
        simp [hc] at hStep
    | evaluate tx tags ts =>
      change authenticatedPolicyGuardStep st tx tags ts = .accepted st' ev at hStep
      unfold authenticatedPolicyGuardStep at hStep
      cases hAdm : policyCheckAdmission st tx tags ts <;> simp [hAdm] at hStep
      rcases hStep with ⟨rfl, rfl⟩
      have hWb := policyAdmission_wire_and_burns hAdm
      simp only [traceApprovedOutputs_cons_some, watermarkApprovedIntents, List.map_cons, List.mem_cons]
      refine ⟨?_, ?_⟩
      · intro x hx
        rintro (rfl | hTail)
        · exact hWb.2.2.2.2.2.2.2.2.1 hx
        · exact ih.1 x (policyBurn_persistent _ _ _ x hx) hTail
      · intro y hy
        rintro (rfl | hTail)
        · exact hWb.2.2.2.2.2.2.2.2.2.1 hy
        · exact ih.2 y (policyBurn_persistent _ _ _ y hy) hTail
  | @consRejected st st' _ inp err rest hStep _ ih =>
    have he := policy_operational_rejection_state st st' inp err hStep
    subst he
    simp only [traceApprovedOutputs_cons_none]
    exact ih

/-- **Multi-Turn Operational Policy Soundness Across Window Rotations (`policy_operational_multiturn_sound`)**:
    Across ANY multi-turn trace of `policyWatermarkGuardStep` (interleaving evaluations, rejections,
    and MAC-authorized window rotations):
    1. Every approved intent nonces list is strictly `Nodup` across all windows.
    2. Every approved session identifier (`ofLE tx.session_id.reverse`) list is strictly `Nodup` across all windows.
    3. Every approved `(tx, bytes)` emitted `toCanonicalSigningBytes tx`, passed cryptographic initiator
       authentication (`∃ tags, policyAuthenticatedInitiator s₀ tx tags = true`), and never reused a
       pre-burned nonce or session. -/
theorem policy_operational_multiturn_sound
    {s₀ sf : AuthenticatedPolicyState}
    {tr : List (AuthenticatedPolicyInput × Option PolicyWatermarkEvent)}
    (hTr : ValidCustodyTrace policyWatermarkGuardStep s₀ tr sf) :
    ((watermarkApprovedIntents (traceApprovedOutputs tr)).map (fun p => p.1.nonce)).Nodup ∧
    ((watermarkApprovedIntents (traceApprovedOutputs tr)).map (fun p => ofLE p.1.session_id.reverse)).Nodup ∧
    (∀ p ∈ watermarkApprovedIntents (traceApprovedOutputs tr),
      ¬ policyBurned s₀.nonceBurns p.1.nonce ∧
      ¬ policyBurned s₀.sessionBurns (ofLE p.1.session_id.reverse) ∧
      p.2 = toCanonicalSigningBytes p.1 ∧
      (∃ tags, policyAuthenticatedInitiator s₀ p.1 tags = true) ∧
      txFitsWireWidths { p.1 with message_digest := List.replicate 32 0 } = true ∧
      p.1.policy_digest.length = 32) := by
  induction hTr with
  | nil =>
    exact ⟨.nil, .nil, fun _ hm => by simp [traceApprovedOutputs, watermarkApprovedIntents] at hm⟩
  | @consAccepted st st' _ inp ev rest hStep hRest ih =>
    cases inp with
    | advance auth =>
      unfold policyWatermarkGuardStep at hStep
      if hc : st.rules.window_id < auth.newWindow ∧ auth.newWindow < 256 ^ 8 ∧
              auth.mac = policyWindowTag st auth.newWindow then
        simp only [hc] at hStep
        rcases CustodyStepOutcome.accepted.inj hStep with ⟨rfl, rfl⟩
        simp only [traceApprovedOutputs_cons_some, watermarkApprovedIntents]
        exact ih
      else
        simp [hc] at hStep
    | evaluate tx tags ts =>
      change authenticatedPolicyGuardStep st tx tags ts = .accepted st' ev at hStep
      unfold authenticatedPolicyGuardStep at hStep
      cases hAdm : policyCheckAdmission st tx tags ts <;> simp [hAdm] at hStep
      rcases hStep with ⟨rfl, rfl⟩
      have hWb := policyAdmission_wire_and_burns hAdm
      have hNoFuture := policy_operational_burned_not_in_future hRest
      have hNonceNotRest := hNoFuture.1 tx.nonce (policyBurn_marks _ _ _)
      have hSessNotRest := hNoFuture.2 (ofLE tx.session_id.reverse) (policyBurn_marks _ _ _)
      simp only [traceApprovedOutputs_cons_some, watermarkApprovedIntents, List.map_cons]
      refine ⟨.cons (fun x hx hEq => hNonceNotRest (hEq ▸ hx)) ih.1,
              .cons (fun y hy hEq => hSessNotRest (hEq ▸ hy)) ih.2.1,
              ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hTail
      · exact ⟨hWb.2.2.2.2.2.2.2.2.1, hWb.2.2.2.2.2.2.2.2.2.1, rfl,
               ⟨tags, hWb.2.2.2.2.2.2.2.2.2.2⟩, hWb.1, hWb.2.1⟩
      · obtain ⟨hNb', hSb', hBytes', hAuth', hFit', hLen'⟩ := ih.2.2 p hTail
        exact ⟨fun hb => hNb' (policyBurn_persistent _ _ _ _ hb),
               fun hb => hSb' (policyBurn_persistent _ _ _ _ hb),
               hBytes', hAuth', hFit', hLen'⟩
  | @consRejected st st' _ inp err rest hStep _ ih =>
    have he := policy_operational_rejection_state st st' inp err hStep
    subst he
    simp only [traceApprovedOutputs_cons_none]
    exact ih

/-- Concrete attacker-submitted tag and context witness relative to the initiator's signing-oracle history. -/
structure PolicyProducedForgery (g : AuthenticatedPolicyState) (tx : TransactionIntent)
    (submitted : List InitiatorPeerTag) (oracleHistory : List (List UInt8)) where
  peerKey : List UInt8
  actualTag : InitiatorPeerTag
  enrolled : g.pairwiseKeys.find? (fun p => p.1 == tx.initiator_party) =
    some (tx.initiator_party, peerKey)
  uniqueSubmitted : submitted.filter (fun t => t.approver == g.party) = [actualTag]
  verifies : actualTag.tag = policyInitiatorTag peerKey g.party tx
  freshContext : policyInitiatorAuthDigest tx ∉ oracleHistory

/-- Constructive (`0 Classical.choice`) authentication-or-forgery extractor: remote acceptance checks
    a unique actual tag under an enrolled pairwise key, so its context is either in `history` or
    constructively yields a `PolicyProducedForgery`. -/
def policy_authentication_or_produced_forgery (g : AuthenticatedPolicyState)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (history : List (List UInt8))
    (remote : tx.initiator_party ≠ g.party)
    (accepted : policyAuthenticatedInitiator g tx tags = true) :
    PSum (policyInitiatorAuthDigest tx ∈ history)
      (PolicyProducedForgery g tx tags history) :=
  if hMem : decide (policyInitiatorAuthDigest tx ∈ history) = true then
    .inl (of_decide_eq_true hMem)
  else
    .inr <| by
      have old : policyInitiatorAuthDigest tx ∉ history :=
        fun hm => hMem (decide_eq_true hm)
      unfold policyAuthenticatedInitiator at accepted
      have hNeBool : (tx.initiator_party == g.party) = false :=
        beq_false_of_ne remote
      simp only [hNeBool, Bool.false_eq_true, ↓reduceIte] at accepted
      cases hk : g.pairwiseKeys.find? (fun p => p.1 == tx.initiator_party) with
      | none => rw [hk] at accepted; cases accepted
      | some pair =>
        rcases pair with ⟨party, key⟩
        have hp : party = tx.initiator_party := eq_of_beq (show (party == tx.initiator_party) = true from List.find?_some (p := fun p : Nat × List UInt8 => p.1 == tx.initiator_party) hk)
        subst party
        rw [hk] at accepted
        dsimp only at accepted
        cases ht : tags.filter (fun t => t.approver == g.party) with
        | nil => rw [ht] at accepted; cases accepted
        | cons tag rest =>
          cases rest with
          | nil =>
            rw [ht] at accepted
            exact ⟨key, tag, hk, ht, eq_of_beq accepted, old⟩
          | cons _ _ =>
            rw [ht] at accepted; cases accepted

/-- #tooth: an authenticated old-window authorization cannot be replayed in its new window. -/
theorem tooth_policy_rotation_not_timestamp (g : AuthenticatedPolicyState)
    (a : PolicyWindowAuthorization) (h : a.newWindow ≤ g.rules.window_id) :
    policyWatermarkGuardStep g (.advance a) = .rejected g .epochAdvanceTooEarly := by
  unfold policyWatermarkGuardStep
  have hn : ¬ (g.rules.window_id < a.newWindow ∧ a.newWindow < 256 ^ 8 ∧
               a.mac = policyWindowTag g a.newWindow) := fun hc => Nat.not_lt.mpr h hc.1
  simp [hn]

/-- #tooth: duplicate matching approver tags are rejected, even if valid. -/
theorem tooth_policy_duplicate_initiator_tags (g : AuthenticatedPolicyState)
    (tx : TransactionIntent) (key : List UInt8) (hparty : tx.initiator_party ≠ g.party)
    (hkey : g.pairwiseKeys.find? (fun p => p.1 == tx.initiator_party) = some (tx.initiator_party, key)) :
    policyAuthenticatedInitiator g tx
      [⟨g.party, policyInitiatorTag key g.party tx⟩,
       ⟨g.party, policyInitiatorTag key g.party tx⟩] = false := by
  unfold policyAuthenticatedInitiator
  simp [beq_false_of_ne hparty, hkey]

/-- #tooth: a burned session identifier blocks the operational path even on a fresh nonce. -/
theorem tooth_policy_session_replay_rejected (s : AuthenticatedPolicyState)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (ts : Nat)
    (h : policyBurned s.sessionBurns (ofLE tx.session_id.reverse)) :
    authenticatedPolicyGuardStep s tx tags ts = .rejected s .unauthenticatedInitiator := by
  have hFalse : policyCheckAdmission s tx tags ts = false := by
    cases hc : policyCheckAdmission s tx tags ts
    · rfl
    · exfalso
      exact (policyAdmission_wire_and_burns hc).2.2.2.2.2.2.2.2.2.1 h
  simp [authenticatedPolicyGuardStep, hFalse]

/-- #tooth: the 0 versus 2^256 nonce encoding collision is outside the accepted signing domain. -/
theorem tooth_policy_overwide_nonce_rejected (g : AuthenticatedPolicyState)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (ts : Nat) (hn : 256 ^ 32 ≤ tx.nonce) :
    authenticatedPolicyGuardStep g tx tags ts = .rejected g .unauthenticatedInitiator := by
  have hfit : txFitsWireWidths { tx with message_digest := List.replicate 32 0 } = false := by
    simp [txFitsWireWidths, txScalarsFitWire, Nat.not_lt.mpr hn]
  have hFalse : policyCheckAdmission g tx tags ts = false := by
    cases hc : policyCheckAdmission g tx tags ts
    · rfl
    · exfalso
      have hf := (policyAdmission_wire_and_burns hc).1
      rw [hfit] at hf
      cases hf
  simp [authenticatedPolicyGuardStep, hFalse]

/-- #tooth: caller-forged intent timestamp or expired authoritative timestamp is rejected
    even when all initiator MACs and velocity bounds hold. -/
theorem tooth_policy_forged_or_expired_timestamp_rejected (g : AuthenticatedPolicyState)
    (tx : TransactionIntent) (tags : List InitiatorPeerTag) (ts : Nat)
    (hBad : tx.timestamp_secs ≠ ts ∨ g.validNotAfterSecs < ts) :
    authenticatedPolicyGuardStep g tx tags ts = .rejected g .unauthenticatedInitiator := by
  have hFalse : policyCheckAdmission g tx tags ts = false := by
    cases hc : policyCheckAdmission g tx tags ts
    · rfl
    · exfalso
      have hw := policyAdmission_wire_and_burns hc
      rcases hBad with hNe | hExp
      · exact hNe hw.2.2.2.2.1
      · exact Nat.not_lt.mpr hw.2.2.2.1 hExp
  simp [authenticatedPolicyGuardStep, hFalse]

/-! #### Quorum-Switching Cumulative Spend-Cap & `SharedWindowSpendLedger` (`qsag-policy` Focus 04 #2) -/

/-- Shared window spend and replay ledger mirroring `SharedWindowSpendLedger` in `crates/qsag-policy/src/lib.rs`:
    tracks global cumulative spend across switching `t`-of-`n` signing quorums within each active window
    and retains global nonce/session burn sets across window rotations. -/
structure SharedWindowSpendLedger where
  windowId : Nat
  velocityWindowCap : Nat
  cumulativeSpent : Nat := 0
  nonceBurns : PolicyBurnSet := {}
  sessionBurns : PolicyBurnSet := {}
  burnCapacity : Nat := 256
  deriving DecidableEq, Repr

/-- Multi-custodian policy cluster coordinating a `threshold`-of-`n` roster of `AuthenticatedPolicyState`
    signers through `SharedWindowSpendLedger`. -/
structure PolicyQuorumCluster where
  threshold : Nat
  ledger : SharedWindowSpendLedger
  custodians : List AuthenticatedPolicyState
  deriving DecidableEq, Repr

inductive PolicyQuorumInput where
  | approveQuorum (quorum : List Nat) (tx : TransactionIntent)
      (tags : List InitiatorPeerTag) (currentTimestamp : Nat)
  | advanceClusterWindow (newWindow : Nat) (auths : List (Nat × PolicyWindowAuthorization))
  deriving DecidableEq, Repr

inductive PolicyQuorumEvent where
  | quorumApproved (quorum : List Nat) (intent : TransactionIntent) (canonicalBytes : List UInt8)
  | clusterWindowAdvanced (newWindow : Nat)
  deriving DecidableEq, Repr

inductive PolicyQuorumReject where
  | invalidQuorumOrDuplicateParty
  | ledgerWindowMismatch
  | globalVelocityCapExceeded
  | globalReplayDetected
  | custodianRejected
  | invalidWindowAdvance
  deriving DecidableEq, Repr

/-- Update every custodian participating in `quorum` via `authenticatedPolicyGuardStep`; fails (`none`)
    if any requested party ID is missing from `custodians` or rejects the intent. -/
def policyUpdateQuorumCustodians (quorum : List Nat) (tx : TransactionIntent)
    (tags : List InitiatorPeerTag) (ts : Nat) :
    List AuthenticatedPolicyState → Option (List AuthenticatedPolicyState)
  | [] => if quorum.isEmpty then some [] else none
  | c :: cs =>
    if c.party ∈ quorum then
      match authenticatedPolicyGuardStep c tx tags ts,
            policyUpdateQuorumCustodians (quorum.filter (· != c.party)) tx tags ts cs with
      | .accepted c' _, some cs' => some (c' :: cs')
      | _, _ => none
    else
      match policyUpdateQuorumCustodians quorum tx tags ts cs with
      | some cs' => some (c :: cs')
      | none => none

/-- Advance every custodian in the cluster to `newWindow` using its enrolled `windowKey` MAC. -/
def policyAdvanceAllCustodians (newWindow : Nat) (auths : List (Nat × PolicyWindowAuthorization)) :
    List AuthenticatedPolicyState → Option (List AuthenticatedPolicyState)
  | [] => some []
  | c :: cs =>
    match auths.find? (fun p => p.1 == c.party) with
    | none => none
    | some (_, auth) =>
      if auth.newWindow == newWindow then
        match policyWatermarkGuardStep c (.advance auth),
              policyAdvanceAllCustodians newWindow auths cs with
        | .accepted c' _, some cs' => some (c' :: cs')
        | _, _ => none
      else
        none

/-- Operational multi-quorum policy barrier enforcing `SharedWindowSpendLedger` across switching quorums:
    every approval checks global `cumulativeSpent + tx.amount_units ≤ velocityWindowCap`, pins
    `tx.rolling_window_spent = cumulativeSpent`, burns `(nonce, session)` globally, and requires
    `threshold` distinct custodians in `quorum` to pass `authenticatedPolicyGuardStep`. -/
def policyQuorumClusterStep (cl : PolicyQuorumCluster) (inp : PolicyQuorumInput) :
    CustodyStepOutcome PolicyQuorumCluster PolicyQuorumEvent PolicyQuorumReject :=
  match inp with
  | .approveQuorum quorum tx tags ts =>
    if ¬ (0 < cl.threshold ∧ cl.threshold ≤ quorum.length ∧ quorum.Nodup ∧
        (∀ p ∈ quorum, p < 256 ^ 2) ∧
        tx.approver_bytes = quorum.flatMap (be 2) ∧ tx.quorum_bytes = quorum.flatMap (be 2)) then
      .rejected cl .invalidQuorumOrDuplicateParty
    else if ¬ (tx.window_id = cl.ledger.windowId ∧ tx.rolling_window_spent = cl.ledger.cumulativeSpent) then
      .rejected cl .ledgerWindowMismatch
    else if ¬ (cl.ledger.cumulativeSpent + tx.amount_units ≤ cl.ledger.velocityWindowCap ∧
               cl.ledger.cumulativeSpent + tx.amount_units < 256 ^ 16) then
      .rejected cl .globalVelocityCapExceeded
    else if policyIsBurned cl.ledger.nonceBurns tx.nonce ||
            policyIsBurned cl.ledger.sessionBurns (ofLE tx.session_id.reverse) then
      .rejected cl .globalReplayDetected
    else
      match policyUpdateQuorumCustodians quorum tx tags ts cl.custodians with
      | none => .rejected cl .custodianRejected
      | some custodians' =>
        let ledger' : SharedWindowSpendLedger :=
          { cl.ledger with
            cumulativeSpent := cl.ledger.cumulativeSpent + tx.amount_units
            nonceBurns := policyBurn cl.ledger.burnCapacity cl.ledger.nonceBurns tx.nonce
            sessionBurns := policyBurn cl.ledger.burnCapacity cl.ledger.sessionBurns (ofLE tx.session_id.reverse) }
        .accepted { cl with ledger := ledger', custodians := custodians' }
          (.quorumApproved quorum tx (toCanonicalSigningBytes tx))
  | .advanceClusterWindow newWindow auths =>
    if ¬ (cl.ledger.windowId < newWindow ∧ newWindow < 256 ^ 8) then
      .rejected cl .invalidWindowAdvance
    else
      match policyAdvanceAllCustodians newWindow auths cl.custodians with
      | none => .rejected cl .invalidWindowAdvance
      | some custodians' =>
        let ledger' : SharedWindowSpendLedger :=
          { cl.ledger with windowId := newWindow, cumulativeSpent := 0 }
        .accepted { cl with ledger := ledger', custodians := custodians' }
          (.clusterWindowAdvanced newWindow)

/-- Extract approved `(quorum, tx, canonicalBytes)` triples from `PolicyQuorumEvent` outputs. -/
def quorumApprovedIntents : List PolicyQuorumEvent → List (List Nat × TransactionIntent × List UInt8)
  | [] => []
  | .quorumApproved q tx bs :: rest => (q, tx, bs) :: quorumApprovedIntents rest
  | .clusterWindowAdvanced _ :: rest => quorumApprovedIntents rest

/-- Whether a cluster input trace contains no window-advance events (single-window switching-quorum segment). -/
def quorumTraceStaysInWindow : List (PolicyQuorumInput × Option PolicyQuorumEvent) → Prop
  | [] => True
  | (.approveQuorum _ _ _ _, _) :: rest => quorumTraceStaysInWindow rest
  | (.advanceClusterWindow _ _, none) :: rest => quorumTraceStaysInWindow rest
  | (.advanceClusterWindow _ _, some _) :: _ => False

private theorem policyQuorumCluster_rejection_state
    {cl cl' : PolicyQuorumCluster} {inp : PolicyQuorumInput} {err : PolicyQuorumReject}
    (h : policyQuorumClusterStep cl inp = .rejected cl' err) : cl' = cl := by
  cases inp with
  | approveQuorum q tx tags ts =>
    unfold policyQuorumClusterStep at h
    if h1 : ¬ (0 < cl.threshold ∧ cl.threshold ≤ q.length ∧ q.Nodup ∧
          (∀ p ∈ q, p < 256 ^ 2) ∧ tx.approver_bytes = q.flatMap (be 2) ∧ tx.quorum_bytes = q.flatMap (be 2)) then
      simp [h1] at h; exact h.1.symm
    else if h2 : ¬ (tx.window_id = cl.ledger.windowId ∧ tx.rolling_window_spent = cl.ledger.cumulativeSpent) then
      simp [h1, h2] at h; exact h.1.symm
    else if h3 : ¬ (cl.ledger.cumulativeSpent + tx.amount_units ≤ cl.ledger.velocityWindowCap ∧
                    cl.ledger.cumulativeSpent + tx.amount_units < 256 ^ 16) then
      simp [h1, h2, h3] at h; exact h.1.symm
    else if h4 : (policyIsBurned cl.ledger.nonceBurns tx.nonce ||
                  policyIsBurned cl.ledger.sessionBurns (ofLE tx.session_id.reverse)) = true then
      simp [h1, h2, h3, h4] at h; exact h.1.symm
    else
      simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at h
      cases hUpd : policyUpdateQuorumCustodians q tx tags ts cl.custodians <;>
        simp [hUpd] at h
      exact h.1.symm
  | advanceClusterWindow nw auths =>
    unfold policyQuorumClusterStep at h
    if hWin : ¬ (cl.ledger.windowId < nw ∧ nw < 256 ^ 8) then
      simp [hWin] at h; exact h.1.symm
    else
      simp only [hWin, ↓reduceIte] at h
      cases hAdv : policyAdvanceAllCustodians nw auths cl.custodians <;>
        simp [hAdv] at h
      exact h.1.symm

private theorem policyQuorumCluster_burned_not_in_future
    {cl clf : PolicyQuorumCluster}
    {tr : List (PolicyQuorumInput × Option PolicyQuorumEvent)}
    (hTr : ValidCustodyTrace policyQuorumClusterStep cl tr clf) :
    (∀ x, policyBurned cl.ledger.nonceBurns x →
      x ∉ (quorumApprovedIntents (traceApprovedOutputs tr)).map (fun e => e.2.1.nonce)) ∧
    (∀ y, policyBurned cl.ledger.sessionBurns y →
      y ∉ (quorumApprovedIntents (traceApprovedOutputs tr)).map (fun e => ofLE e.2.1.session_id.reverse)) := by
  induction hTr with
  | nil =>
    exact ⟨fun _ _ hm => by simp [traceApprovedOutputs, quorumApprovedIntents] at hm,
           fun _ _ hm => by simp [traceApprovedOutputs, quorumApprovedIntents] at hm⟩
  | @consAccepted st st' _ inp ev rest hStep _ ih =>
    cases inp with
    | advanceClusterWindow nw auths =>
      unfold policyQuorumClusterStep at hStep
      if hWin : ¬ (st.ledger.windowId < nw ∧ nw < 256 ^ 8) then
        simp [hWin] at hStep
      else
        simp only [hWin, ↓reduceIte] at hStep
        cases hAdv2 : policyAdvanceAllCustodians nw auths st.custodians <;>
          simp [hAdv2] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        simp only [traceApprovedOutputs_cons_some, quorumApprovedIntents]
        exact ih
    | approveQuorum q tx tags ts =>
      unfold policyQuorumClusterStep at hStep
      if h1 : ¬ (0 < st.threshold ∧ st.threshold ≤ q.length ∧ q.Nodup ∧
          (∀ p ∈ q, p < 256 ^ 2) ∧ tx.approver_bytes = q.flatMap (be 2) ∧ tx.quorum_bytes = q.flatMap (be 2)) then simp [h1] at hStep
      else if h2 : ¬ (tx.window_id = st.ledger.windowId ∧ tx.rolling_window_spent = st.ledger.cumulativeSpent) then
        simp [h1, h2] at hStep
      else if h3 : ¬ (st.ledger.cumulativeSpent + tx.amount_units ≤ st.ledger.velocityWindowCap ∧
                      st.ledger.cumulativeSpent + tx.amount_units < 256 ^ 16) then
        simp [h1, h2, h3] at hStep
      else if h4 : (policyIsBurned st.ledger.nonceBurns tx.nonce ||
                    policyIsBurned st.ledger.sessionBurns (ofLE tx.session_id.reverse)) = true then
        simp [h1, h2, h3, h4] at hStep
      else
        simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at hStep
        cases hUpd : policyUpdateQuorumCustodians q tx tags ts st.custodians <;>
          simp [hUpd] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        simp only [Bool.or_eq_true, not_or] at h4
        simp only [traceApprovedOutputs_cons_some, quorumApprovedIntents, List.map_cons, List.mem_cons]
        refine ⟨?_, ?_⟩
        · intro x hx
          rintro (rfl | hTail)
          · exact h4.1 hx
          · exact ih.1 x (policyBurn_persistent _ _ _ x hx) hTail
        · intro y hy
          rintro (rfl | hTail)
          · exact h4.2 hy
          · exact ih.2 y (policyBurn_persistent _ _ _ y hy) hTail
  | @consRejected st st' _ inp err rest hStep _ ih =>
    have he := policyQuorumCluster_rejection_state hStep
    subst he
    simp only [traceApprovedOutputs_cons_none]
    exact ih

/-- **Multi-Turn Quorum-Switching Cumulative Spend-Cap & Global Replay Soundness
    (`policy_quorum_switching_cumulative_spend_and_replay_sound`)**:
    Across ANY multi-turn trace of `policyQuorumClusterStep` over arbitrarily switching `t`-of-`n`
    signing quorums `Q₁, Q₂, ...` (including disjoint quorums!):
    1. **Global Replay Exclusion Across Quorums & Windows**: Approved `nonce`s and `session_id`s are
       strictly `Nodup` across the entire multi-quorum, multi-window trace, and never reuse pre-burned IDs.
    2. **Quorum Authenticity & Canonical Bytes**: Every approved `(q, tx, bs)` has `threshold ≤ q.length`,
       `q.Nodup`, and `bs = toCanonicalSigningBytes tx`.
    3. **Cumulative Spend-Cap Across Switching Quorums**: Along any window trace segment (`quorumTraceStaysInWindow tr`)
       starting with `cl₀.ledger.cumulativeSpent ≤ cl₀.ledger.velocityWindowCap`,
       `cl₀.ledger.cumulativeSpent + ∑ approved.amount_units = clf.ledger.cumulativeSpent ≤ cl₀.ledger.velocityWindowCap`
       — completely eliminating disjoint-quorum cumulative velocity bypass! -/
theorem policy_quorum_switching_cumulative_spend_and_replay_sound
    {cl₀ clf : PolicyQuorumCluster}
    {tr : List (PolicyQuorumInput × Option PolicyQuorumEvent)}
    (hTrace : ValidCustodyTrace policyQuorumClusterStep cl₀ tr clf) :
    let approved := quorumApprovedIntents (traceApprovedOutputs tr)
    let approvedSum := (approved.map (fun e => e.2.1.amount_units)).foldr (· + ·) 0
    (approved.map (fun e => e.2.1.nonce)).Nodup ∧
    (approved.map (fun e => ofLE e.2.1.session_id.reverse)).Nodup ∧
    (∀ e ∈ approved,
      0 < cl₀.threshold ∧ cl₀.threshold ≤ e.1.length ∧ e.1.Nodup ∧
      ¬ policyBurned cl₀.ledger.nonceBurns e.2.1.nonce ∧
      ¬ policyBurned cl₀.ledger.sessionBurns (ofLE e.2.1.session_id.reverse) ∧
      e.2.2 = toCanonicalSigningBytes e.2.1) ∧
    (quorumTraceStaysInWindow tr →
      cl₀.ledger.cumulativeSpent ≤ cl₀.ledger.velocityWindowCap →
      cl₀.ledger.cumulativeSpent + approvedSum = clf.ledger.cumulativeSpent ∧
      clf.ledger.cumulativeSpent ≤ cl₀.ledger.velocityWindowCap ∧
      approvedSum ≤ cl₀.ledger.velocityWindowCap) := by
  induction hTrace with
  | nil =>
    refine ⟨.nil, .nil, fun _ hm => by simp [traceApprovedOutputs, quorumApprovedIntents] at hm, ?_⟩
    intro _ hLe
    exact ⟨by simp [traceApprovedOutputs, quorumApprovedIntents], hLe, Nat.zero_le _⟩
  | @consAccepted st st' sf' inp ev rest hStep hRest ih =>
    cases inp with
    | advanceClusterWindow nw auths =>
      unfold policyQuorumClusterStep at hStep
      if hWin : ¬ (st.ledger.windowId < nw ∧ nw < 256 ^ 8) then
        simp [hWin] at hStep
      else
        simp only [hWin, ↓reduceIte] at hStep
        cases hAdv : policyAdvanceAllCustodians nw auths st.custodians <;>
          simp [hAdv] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        simp only [traceApprovedOutputs_cons_some, quorumApprovedIntents]
        refine ⟨ih.1, ih.2.1, ih.2.2.1, ?_⟩
        intro hStay
        cases hStay
    | approveQuorum q tx tags ts =>
      unfold policyQuorumClusterStep at hStep
      if h1 : ¬ (0 < st.threshold ∧ st.threshold ≤ q.length ∧ q.Nodup ∧
          (∀ p ∈ q, p < 256 ^ 2) ∧ tx.approver_bytes = q.flatMap (be 2) ∧ tx.quorum_bytes = q.flatMap (be 2)) then simp [h1] at hStep
      else if h2 : ¬ (tx.window_id = st.ledger.windowId ∧ tx.rolling_window_spent = st.ledger.cumulativeSpent) then
        simp [h1, h2] at hStep
      else if h3 : ¬ (st.ledger.cumulativeSpent + tx.amount_units ≤ st.ledger.velocityWindowCap ∧
                      st.ledger.cumulativeSpent + tx.amount_units < 256 ^ 16) then
        simp [h1, h2, h3] at hStep
      else if h4 : (policyIsBurned st.ledger.nonceBurns tx.nonce ||
                    policyIsBurned st.ledger.sessionBurns (ofLE tx.session_id.reverse)) = true then
        simp [h1, h2, h3, h4] at hStep
      else
        simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at hStep
        cases hUpd : policyUpdateQuorumCustodians q tx tags ts st.custodians <;>
          simp [hUpd] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        have hQProps : 0 < st.threshold ∧ st.threshold ≤ q.length ∧ q.Nodup := ⟨(Decidable.of_not_not h1).1, (Decidable.of_not_not h1).2.1, (Decidable.of_not_not h1).2.2.1⟩
        have hVelProps : st.ledger.cumulativeSpent + tx.amount_units ≤ st.ledger.velocityWindowCap ∧
            st.ledger.cumulativeSpent + tx.amount_units < 256 ^ 16 := Decidable.of_not_not h3
        simp only [Bool.or_eq_true, not_or] at h4
        have hNoFuture := policyQuorumCluster_burned_not_in_future hRest
        have hNonceNot := hNoFuture.1 tx.nonce (policyBurn_marks _ _ _)
        have hSessNot := hNoFuture.2 (ofLE tx.session_id.reverse) (policyBurn_marks _ _ _)
        simp only [traceApprovedOutputs_cons_some, quorumApprovedIntents, List.map_cons, List.foldr_cons]
        refine ⟨.cons (fun x hx hEq => hNonceNot (hEq ▸ hx)) ih.1,
                .cons (fun y hy hEq => hSessNot (hEq ▸ hy)) ih.2.1,
                ?_, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | hTail
          · exact ⟨hQProps.1, hQProps.2.1, hQProps.2.2, h4.1, h4.2, rfl⟩
          · obtain ⟨hT1, hT2, hNdQ, hNb', hSb', hBs⟩ := ih.2.2.1 e hTail
            exact ⟨hT1, hT2, hNdQ,
                   fun hb => hNb' (policyBurn_persistent _ _ _ _ hb),
                   fun hb => hSb' (policyBurn_persistent _ _ _ _ hb),
                   hBs⟩
        · intro hStay _
          have hRestSpend := ih.2.2.2 hStay hVelProps.1
          dsimp only at hRestSpend
          have hSumEq : st.ledger.cumulativeSpent +
              (tx.amount_units +
                (List.map (fun e => e.2.1.amount_units)
                  (quorumApprovedIntents (traceApprovedOutputs rest))).foldr (· + ·) 0) =
              sf'.ledger.cumulativeSpent := by
            rw [← Nat.add_assoc]
            exact hRestSpend.1
          exact ⟨hSumEq, hRestSpend.2.1,
                 Nat.le_trans (Nat.le_add_left _ _) (hSumEq.symm ▸ hRestSpend.2.1)⟩
  | @consRejected st st' _ inp err rest hStep _ ih =>
    have he := policyQuorumCluster_rejection_state hStep
    subst he
    simp only [traceApprovedOutputs_cons_none]
    refine ⟨ih.1, ih.2.1, ih.2.2.1, ?_⟩
    intro hStay hLe
    cases inp with
    | approveQuorum _ _ _ _ => exact ih.2.2.2 hStay hLe
    | advanceClusterWindow _ _ => exact ih.2.2.2 hStay hLe

/-- Concrete helper intent for quorum-switching `#tooth` and inhabitedness proofs. -/
def demoQuorumBaseIntent (nonceVal amountVal rollingSpent : Nat)
    (sessByte : UInt8) (approverBytes : List UInt8) : TransactionIntent :=
  { policy_digest := List.replicate 32 0xAA
    chain_id := 1
    suite_tag := 2
    recipient_hrp := [0x71, 0x73]
    recipient_version := 1
    recipient_suite_tag := 2
    recipient_kind := 0
    recipient := List.replicate 32 0xBB
    amount_units := amountVal
    rolling_window_spent := rollingSpent
    window_id := 1
    nonce := nonceVal
    timestamp_secs := 1000
    initiator_party := 99
    init_mac_bytes := []
    approver_bytes := approverBytes
    payload_digest := List.replicate 32 0xCC
    authority_digest := List.replicate 32 0xDD
    rolling_window_accumulator := List.replicate 32 0xEE
    signing_key_id := List.replicate 32 0x11
    policy_revision := 1
    message_digest := List.replicate 32 0x22
    signing_context_digest := List.replicate 32 0x33
    session_id := List.replicate 31 0x00 ++ [sessByte]
    quorum_bytes := approverBytes }

def demoQuorumSignedIntent (key : List UInt8) (pA pB : Nat)
    (nonceVal amountVal rollingSpent : Nat) (sessByte : UInt8) :
    TransactionIntent × List InitiatorPeerTag :=
  let appBytes := be 2 pA ++ be 2 pB
  let base := demoQuorumBaseIntent nonceVal amountVal rollingSpent sessByte appBytes
  let tags : List InitiatorPeerTag :=
    [⟨pA, policyInitiatorTag key pA base⟩, ⟨pB, policyInitiatorTag key pB base⟩]
  ({ base with init_mac_bytes := encodeInitiatorTags tags }, tags)

def demoQuorumCustodian (partyId : Nat) (key winKey : List UInt8) : AuthenticatedPolicyState :=
  { rules :=
      { window_id := 1
        velocity_window_cap := 100
        accumulated_spend := 0
        burned_intent_nonces := []
        pinned_policy_digest := List.replicate 32 0xAA
        pinned_authority_digest := List.replicate 32 0xDD
        allowed_recipients := [List.replicate 32 0xBB]
        per_tx_cap := 60 }
    party := partyId
    chain := 1
    suite := 2
    pairwiseKeys := [(99, key)]
    windowKey := winKey
    policyId := List.replicate 32 0xAA
    validNotBeforeSecs := 500
    validNotAfterSecs := 2000 }

/-- **`#tooth` Uncoordinated Disjoint-Quorum Spend-Cap Bypass (`tooth_uncoordinated_quorum_switching_bypasses_spend_cap`)**:
    Without `SharedWindowSpendLedger` (or a mandatory accounting-guardian intersection), switching from
    2-of-4 quorum `{0, 1}` (`amount = 60`, `rolling_window_spent = 0`) to disjoint quorum `{2, 3}`
    (`amount = 60`, `rolling_window_spent = 0`) allows BOTH quorums to pass `authenticatedPolicyGuardStep`
    locally under `velocity_window_cap = 100`, approving `60 + 60 = 120 > 100`, whereas
    `policyQuorumClusterStep` rejects the second spend! -/
theorem tooth_uncoordinated_quorum_switching_bypasses_spend_cap :
    let key : List UInt8 := List.replicate 32 0x55
    let winKey : List UInt8 := List.replicate 32 0x66
    let c0 := demoQuorumCustodian 0 key winKey
    let c1 := demoQuorumCustodian 1 key winKey
    let c2 := demoQuorumCustodian 2 key winKey
    let c3 := demoQuorumCustodian 3 key winKey
    let pA := demoQuorumSignedIntent key 0 1 10 60 0 0x01
    let pB := demoQuorumSignedIntent key 2 3 11 60 0 0x02
    let pBH := demoQuorumSignedIntent key 2 3 11 60 60 0x02
    let cl0 : PolicyQuorumCluster :=
      { threshold := 2
        ledger := { windowId := 1, velocityWindowCap := 100, cumulativeSpent := 0 }
        custodians := [c0, c1, c2, c3] }
    (∃ c0' c1' c2' c3',
      authenticatedPolicyGuardStep c0 pA.1 pA.2 1000 =
        CustodyStepOutcome.accepted c0' (.intentApproved pA.1 (toCanonicalSigningBytes pA.1)) ∧
      authenticatedPolicyGuardStep c1 pA.1 pA.2 1000 =
        CustodyStepOutcome.accepted c1' (.intentApproved pA.1 (toCanonicalSigningBytes pA.1)) ∧
      authenticatedPolicyGuardStep c2 pB.1 pB.2 1000 =
        CustodyStepOutcome.accepted c2' (.intentApproved pB.1 (toCanonicalSigningBytes pB.1)) ∧
      authenticatedPolicyGuardStep c3 pB.1 pB.2 1000 =
        CustodyStepOutcome.accepted c3' (.intentApproved pB.1 (toCanonicalSigningBytes pB.1)) ∧
      pA.1.amount_units + pB.1.amount_units > c0.rules.velocity_window_cap) ∧
    (∃ cl1,
      policyQuorumClusterStep cl0 (.approveQuorum [0, 1] pA.1 pA.2 1000) =
        CustodyStepOutcome.accepted cl1 (.quorumApproved [0, 1] pA.1 (toCanonicalSigningBytes pA.1)) ∧
      policyQuorumClusterStep cl1 (.approveQuorum [2, 3] pB.1 pB.2 1000) =
        CustodyStepOutcome.rejected cl1 .ledgerWindowMismatch ∧
      policyQuorumClusterStep cl1 (.approveQuorum [2, 3] pBH.1 pBH.2 1000) =
        CustodyStepOutcome.rejected cl1 .globalVelocityCapExceeded) := by
  intro key winKey c0 c1 c2 c3 pA pB pBH cl0
  have hTagEq : ∀ (k : List UInt8) (p a b n amt sp : Nat) (sb : UInt8),
      policyInitiatorTag k p (demoQuorumSignedIntent k a b n amt sp sb).1 =
        policyInitiatorTag k p (demoQuorumBaseIntent n amt sp sb (be 2 a ++ be 2 b)) :=
    fun _ _ _ _ _ _ _ _ => rfl
  have hAdm0 : policyCheckAdmission c0 pA.1 pA.2 1000 = true := by
    dsimp only [c0, pA, key, winKey, demoQuorumCustodian, demoQuorumSignedIntent, demoQuorumBaseIntent]
    simp [policyCheckAdmission, policyCheckWireDomain, txFitsWireWidths, txScalarsFitWire,
      txSlicesFitU64, policyProjectedSpend, policyIsBurned, encodeInitiatorTags, policyInsertTag,
      policyAuthenticatedInitiator, policyInitiatorTag_length, policyCanonicalApprovers, be, ofLE]
    rfl
  have hAdm1 : policyCheckAdmission c1 pA.1 pA.2 1000 = true := by
    dsimp only [c1, pA, key, winKey, demoQuorumCustodian, demoQuorumSignedIntent, demoQuorumBaseIntent]
    simp [policyCheckAdmission, policyCheckWireDomain, txFitsWireWidths, txScalarsFitWire,
      txSlicesFitU64, policyProjectedSpend, policyIsBurned, encodeInitiatorTags, policyInsertTag,
      policyAuthenticatedInitiator, policyInitiatorTag_length, policyCanonicalApprovers, be, ofLE]
    rfl
  have hAdm2 : policyCheckAdmission c2 pB.1 pB.2 1000 = true := by
    dsimp only [c2, pB, key, winKey, demoQuorumCustodian, demoQuorumSignedIntent, demoQuorumBaseIntent]
    simp [policyCheckAdmission, policyCheckWireDomain, txFitsWireWidths, txScalarsFitWire,
      txSlicesFitU64, policyProjectedSpend, policyIsBurned, encodeInitiatorTags, policyInsertTag,
      policyAuthenticatedInitiator, policyInitiatorTag_length, policyCanonicalApprovers, be, ofLE]
    rfl
  have hAdm3 : policyCheckAdmission c3 pB.1 pB.2 1000 = true := by
    dsimp only [c3, pB, key, winKey, demoQuorumCustodian, demoQuorumSignedIntent, demoQuorumBaseIntent]
    simp [policyCheckAdmission, policyCheckWireDomain, txFitsWireWidths, txScalarsFitWire,
      txSlicesFitU64, policyProjectedSpend, policyIsBurned, encodeInitiatorTags, policyInsertTag,
      policyAuthenticatedInitiator, policyInitiatorTag_length, policyCanonicalApprovers, be, ofLE]
    rfl
  let n0 : AuthenticatedPolicyState := { c0 with
    rules := { c0.rules with accumulated_spend := policyProjectedSpend c0 pA.1 }
    nonceBurns := policyBurn c0.burnCapacity c0.nonceBurns pA.1.nonce
    sessionBurns := policyBurn c0.burnCapacity c0.sessionBurns (ofLE pA.1.session_id.reverse) }
  let n1 : AuthenticatedPolicyState := { c1 with
    rules := { c1.rules with accumulated_spend := policyProjectedSpend c1 pA.1 }
    nonceBurns := policyBurn c1.burnCapacity c1.nonceBurns pA.1.nonce
    sessionBurns := policyBurn c1.burnCapacity c1.sessionBurns (ofLE pA.1.session_id.reverse) }
  let n2 : AuthenticatedPolicyState := { c2 with
    rules := { c2.rules with accumulated_spend := policyProjectedSpend c2 pB.1 }
    nonceBurns := policyBurn c2.burnCapacity c2.nonceBurns pB.1.nonce
    sessionBurns := policyBurn c2.burnCapacity c2.sessionBurns (ofLE pB.1.session_id.reverse) }
  let n3 : AuthenticatedPolicyState := { c3 with
    rules := { c3.rules with accumulated_spend := policyProjectedSpend c3 pB.1 }
    nonceBurns := policyBurn c3.burnCapacity c3.nonceBurns pB.1.nonce
    sessionBurns := policyBurn c3.burnCapacity c3.sessionBurns (ofLE pB.1.session_id.reverse) }
  refine ⟨⟨n0, n1, n2, n3, ?_, ?_, ?_, ?_, by decide⟩, ?_⟩
  · unfold authenticatedPolicyGuardStep; rw [hAdm0]; simp only [↓reduceIte]; rfl
  · unfold authenticatedPolicyGuardStep; rw [hAdm1]; simp only [↓reduceIte]; rfl
  · unfold authenticatedPolicyGuardStep; rw [hAdm2]; simp only [↓reduceIte]; rfl
  · unfold authenticatedPolicyGuardStep; rw [hAdm3]; simp only [↓reduceIte]; rfl
  · have hStep0 : authenticatedPolicyGuardStep c0 pA.1 pA.2 1000 =
        .accepted { c0 with
          rules := { c0.rules with accumulated_spend := policyProjectedSpend c0 pA.1 }
          nonceBurns := policyBurn c0.burnCapacity c0.nonceBurns pA.1.nonce
          sessionBurns := policyBurn c0.burnCapacity c0.sessionBurns (ofLE pA.1.session_id.reverse) }
          (.intentApproved pA.1 (toCanonicalSigningBytes pA.1)) := by
      unfold authenticatedPolicyGuardStep; rw [hAdm0]; simp
    have hStep1 : authenticatedPolicyGuardStep c1 pA.1 pA.2 1000 =
        .accepted { c1 with
          rules := { c1.rules with accumulated_spend := policyProjectedSpend c1 pA.1 }
          nonceBurns := policyBurn c1.burnCapacity c1.nonceBurns pA.1.nonce
          sessionBurns := policyBurn c1.burnCapacity c1.sessionBurns (ofLE pA.1.session_id.reverse) }
          (.intentApproved pA.1 (toCanonicalSigningBytes pA.1)) := by
      unfold authenticatedPolicyGuardStep; rw [hAdm1]; simp
    have hUpdA : policyUpdateQuorumCustodians [0, 1] pA.1 pA.2 1000 [c0, c1, c2, c3] =
        some [
          { c0 with
            rules := { c0.rules with accumulated_spend := policyProjectedSpend c0 pA.1 }
            nonceBurns := policyBurn c0.burnCapacity c0.nonceBurns pA.1.nonce
            sessionBurns := policyBurn c0.burnCapacity c0.sessionBurns (ofLE pA.1.session_id.reverse) },
          { c1 with
            rules := { c1.rules with accumulated_spend := policyProjectedSpend c1 pA.1 }
            nonceBurns := policyBurn c1.burnCapacity c1.nonceBurns pA.1.nonce
            sessionBurns := policyBurn c1.burnCapacity c1.sessionBurns (ofLE pA.1.session_id.reverse) },
          c2, c3] := by
      have hc0p : c0.party = 0 := rfl
      have hc1p : c1.party = 1 := rfl
      have hc2p : c2.party = 2 := rfl
      have hc3p : c3.party = 3 := rfl
      simp [policyUpdateQuorumCustodians, hc0p, hc1p, hc2p, hc3p, hStep0, hStep1]
    let cl1 : PolicyQuorumCluster :=
      { cl0 with
        ledger := { cl0.ledger with
          cumulativeSpent := 60
          nonceBurns := policyBurn cl0.ledger.burnCapacity cl0.ledger.nonceBurns pA.1.nonce
          sessionBurns := policyBurn cl0.ledger.burnCapacity cl0.ledger.sessionBurns (ofLE pA.1.session_id.reverse) }
        custodians := [
          { c0 with
            rules := { c0.rules with accumulated_spend := policyProjectedSpend c0 pA.1 }
            nonceBurns := policyBurn c0.burnCapacity c0.nonceBurns pA.1.nonce
            sessionBurns := policyBurn c0.burnCapacity c0.sessionBurns (ofLE pA.1.session_id.reverse) },
          { c1 with
            rules := { c1.rules with accumulated_spend := policyProjectedSpend c1 pA.1 }
            nonceBurns := policyBurn c1.burnCapacity c1.nonceBurns pA.1.nonce
            sessionBurns := policyBurn c1.burnCapacity c1.sessionBurns (ofLE pA.1.session_id.reverse) },
          c2, c3] }
    refine ⟨cl1, ?_, ?_, ?_⟩
    · unfold policyQuorumClusterStep
      dsimp only
      split
      next bad => exact False.elim (bad (by decide))
      next =>
        split
        next bad => exact False.elim (bad (by decide))
        next =>
          split
          next bad => exact False.elim (bad (by decide))
          next =>
            have hnb : policyIsBurned cl0.ledger.nonceBurns pA.1.nonce = false := rfl
            have hsb : policyIsBurned cl0.ledger.sessionBurns (ofLE pA.1.session_id.reverse) = false := rfl
            simp only [hnb, hsb, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
            rw [show cl0.custodians = [c0, c1, c2, c3] from rfl, hUpdA]
            rfl
    · unfold policyQuorumClusterStep
      have hnd : ([2, 3] : List Nat).Nodup := by decide
      simp [cl1, cl0, pB, demoQuorumSignedIntent, demoQuorumBaseIntent, hnd]
    · unfold policyQuorumClusterStep
      have hnd : ([2, 3] : List Nat).Nodup := by decide
      simp [cl1, cl0, pBH, demoQuorumSignedIntent, demoQuorumBaseIntent, hnd]

/-! ### §B. Operational Commit-Before-Challenge Co-ZK Sacrifice Bound to Challenged ZKBoo Output Heads -/

/-- An enrolled multiplication circuit; indices address initial or earlier wires only. -/
structure CoZkMulGate where
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

structure CoZkExecution where
  wires : List Tower128
  errors : List Tower128
  deriving DecidableEq

/-- Errors are computed directly from the circuit wires, never supplied separately by the caller. -/
def cozkRecordExecution : List CoZkMulGate → List Tower128 → List Tower128 → Option CoZkExecution
  | [], [], wires => some ⟨wires, []⟩
  | g :: gs, z :: zs, wires =>
    if g.left < wires.length ∧ g.right < wires.length then
      match cozkRecordExecution gs zs (wires ++ [z]) with
      | none => none
      | some ex =>
        let err := towerAdd 7 z (towerMul 7 (wires.getD g.left (towerZero 7))
                                            (wires.getD g.right (towerZero 7)))
        some { wires := ex.wires, errors := err :: ex.errors }
    else none
  | _, _, _ => none

def cozkEncodeWires (ws : List Tower128) : List UInt8 :=
  encodeMultiFrame (ws.map (fun w => be 16 (packTower 7 w).toNat))

private theorem list_map_inj_local {α β : Type} {f : α → β}
    (hf : ∀ x y, f x = f y → x = y) :
    ∀ {xs ys : List α}, xs.map f = ys.map f → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf x y h.1, list_map_inj_local hf h.2]

/-- Strict injectivity of `cozkEncodeWires` across arbitrary `Tower128` wire lists. -/
theorem cozkEncodeWires_injective {ws₁ ws₂ : List Tower128}
    (h : cozkEncodeWires ws₁ = cozkEncodeWires ws₂) : ws₁ = ws₂ := by
  have hFrames := encodeMultiFrame_injective h
  refine list_map_inj_local (fun w₁ w₂ hw => ?_) hFrames
  have hPow : (2 ^ (2 ^ 7) : Nat) = 256 ^ 16 := rfl
  have hLt₁ : (packTower 7 w₁).toNat < 256 ^ 16 := hPow ▸ (packTower 7 w₁).isLt
  have hLt₂ : (packTower 7 w₂).toNat < 256 ^ 16 := hPow ▸ (packTower 7 w₂).isLt
  have hNat := be_injective hLt₁ hLt₂ hw
  have hBv : packTower 7 w₁ = packTower 7 w₂ := BitVec.eq_of_toNat_eq hNat
  have hUnpack := congrArg (unpackTower 7) hBv
  simpa only [unpackTower_packTower] using hUnpack

/-- Second opened ZKBoo party `(e + 1) mod 3` for challenge `e : Fin 3`. -/
def cozkNextParty (e : Fin 3) : Fin 3 :=
  ⟨(e.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

/-- Unopened 3rd ZKBoo party `(e + 2) mod 3` whose view stays hidden while its commitment is released. -/
def cozkHiddenParty (e : Fin 3) : Fin 3 :=
  ⟨(e.val + 2) % 3, Nat.mod_lt _ (by decide)⟩

theorem cozkHiddenParty_ne_challenged (e : Fin 3) :
    cozkHiddenParty e ≠ e ∧ cozkHiddenParty e ≠ cozkNextParty e := by
  have he := e.isLt
  have hc : e.val = 0 ∨ e.val = 1 ∨ e.val = 2 := by omega
  rcases hc with h | h | h <;>
    (constructor <;> intro hEq <;> have hv := congrArg Fin.val hEq <;>
      simp [cozkHiddenParty, cozkNextParty, h] at hv)

/-- Frozen execution binding BOTH the circuit wires/errors AND the 3 party ZKBoo head views + commitments. -/
structure CoZkFrozenExecution where
  root : List UInt8
  execution : CoZkExecution
  headsDigest : List UInt8
  headViews : Fin 3 → List UInt8
  headCommits : Fin 3 → List UInt8

inductive CoZkCommittedPhase where
  | awaiting
  | committed (frozen : CoZkFrozenExecution)
  | challenged (frozen : CoZkFrozenExecution) (coin1 coin2 : Tower128) (zkbooChal : Fin 3)
  | verified (frozen : CoZkFrozenExecution) (zkbooChal : Fin 3)
  | completed
  | aborted

/-- Enrollment and phase state. The three legacy verifier-tape fields are retained
for compatibility; the operational challenge step derives fresh values from the frozen root. -/
structure CoZkCommittedState where
  sessionTag : List UInt8
  statement : List UInt8
  initialWires : List Tower128
  circuit : List CoZkMulGate
  verifierCoin1 : Tower128
  verifierCoin2 : Tower128
  zkbooChallenge : Fin 3 := ⟨0, by decide⟩
  phase : CoZkCommittedPhase := .awaiting

inductive CoZkCommittedInput where
  | freezeWires (gateOutputs : List Tower128) (headViews : Fin 3 → List UInt8)
      (headSalts : Fin 3 → List UInt8) (commitmentSalt : List UInt8)
  | challenge
  | verify (rssCheck : RssActiveOpenMsg)
  | release

inductive CoZkPublicEvent where
  | committed (root : List UInt8)
  | challenge (root : List UInt8) (coin1 coin2 : Tower128) (zkbooChal : Fin 3)
  | verified (root : List UInt8)
  | released (root headsDigest : List UInt8) (zkbooChal : Fin 3)
      (openedHead0 openedHead1 hiddenHeadCommit : List UInt8)
  deriving DecidableEq

def cozkHeadCommit (H : Hash) (party : Fin 3) (view salt : List UInt8) : List UInt8 :=
  H (encodeMultiFrame [cozkHeadCommitDomainV1, be 1 party.val, view, salt])

def cozkFreezePreimage (s : CoZkCommittedState) (ex : CoZkExecution)
    (hc0 hc1 hc2 salt : List UInt8) : List UInt8 :=
  let circuitBytes := encodeMultiFrame
    (s.circuit.map (fun g => encodeMultiFrame [txLeb128 g.left, txLeb128 g.right]))
  encodeMultiFrame [migrateRootDomain, s.sessionTag, s.statement,
                    circuitBytes, cozkEncodeWires ex.wires, hc0, hc1, hc2, salt]

def cozkFreezeExecution (H : Hash) (s : CoZkCommittedState) (ex : CoZkExecution)
    (headViews headSalts : Fin 3 → List UInt8) (salt : List UInt8) : CoZkFrozenExecution :=
  let hc : Fin 3 → List UInt8 := fun j => cozkHeadCommit H j (headViews j) (headSalts j)
  let root := H (cozkFreezePreimage s ex (hc ⟨0, by decide⟩) (hc ⟨1, by decide⟩) (hc ⟨2, by decide⟩) salt)
  let headsDigest := H (encodeMultiFrame
    [cozkCheckedHeadsDomainV1, root, cozkEncodeWires ex.wires,
     headViews ⟨0, by decide⟩, headViews ⟨1, by decide⟩, headViews ⟨2, by decide⟩])
  { root := root
    execution := ex
    headsDigest := headsDigest
    headViews := headViews
    headCommits := hc }

/-- Interpret the supplied head seeds as two additive masks; the third head is
computed from the recorded execution. No caller supplies the residual head. -/
def cozkHeadMask (seed : List UInt8) (i : Nat) : Tower128 :=
  unpackTower 7 (BitVec.ofNat 128 (ofLE ((seed.drop (16 * i)).take 16)))

def cozkHeadShare (w : Tower128) (seeds : Fin 3 → List UInt8) (i : Nat)
    (j : Fin 3) : Tower128 :=
  let a := cozkHeadMask (seeds ⟨0, by decide⟩) i
  let b := cozkHeadMask (seeds ⟨1, by decide⟩) i
  if j.val = 0 then a else if j.val = 1 then b else towerAdd 7 w (towerAdd 7 a b)

theorem cozk_heads_reconstruct_recorded_wire (w : Tower128) (seeds : Fin 3 → List UInt8) (i : Nat) :
    towerAdd 7 (towerAdd 7 (cozkHeadShare w seeds i ⟨0, by decide⟩)
      (cozkHeadShare w seeds i ⟨1, by decide⟩)) (cozkHeadShare w seeds i ⟨2, by decide⟩) = w := by
  dsimp [cozkHeadShare]
  rw [towerAdd_comm 7 w, ← towerAdd_assoc, towerAdd_self_zero, towerZero_add]

def cozkExecutionHead (ex : CoZkExecution) (seeds : Fin 3 → List UInt8)
    (j : Fin 3) : List Tower128 :=
  ex.wires.zipIdx |>.map (fun (w, i) => cozkHeadShare w seeds i j)

def cozkBoundHeadViews (ex : CoZkExecution) (seeds : Fin 3 → List UInt8) :
    Fin 3 → List UInt8 := fun j => cozkEncodeWires (cozkExecutionHead ex seeds j)

/-- Fiat-Shamir challenges are functions of the frozen root and statement. -/
def cozkFrozenCoin (H : Hash) (s : CoZkCommittedState) (f : CoZkFrozenExecution)
    (lane : Nat) : Tower128 :=
  let x := unpackTower 7 (BitVec.ofNat 128 (ofLE (H (encodeMultiFrame
    [migrateRootDomain, s.statement, f.root, be 1 lane]))))
  if x = towerZero 7 then towerOne 7 else x

theorem cozk_frozen_coin_nonzero (H : Hash) (s : CoZkCommittedState)
    (f : CoZkFrozenExecution) (lane : Nat) :
    cozkFrozenCoin H s f lane ≠ towerZero 7 := by
  unfold cozkFrozenCoin
  dsimp only
  split
  · exact towerOne_ne_zero 7
  · assumption

def cozkFrozenChallenge (H : Hash) (s : CoZkCommittedState) (f : CoZkFrozenExecution) : Fin 3 :=
  ⟨ofLE (H (encodeMultiFrame [migrateRootDomain, s.statement, f.root, [3]])) % 3,
    Nat.mod_lt _ (by decide)⟩

/-- Operational commit-before-challenge Co-ZK sacrifice step:
    1. Freezes circuit wires and all 3 ZKBoo head commitments BEFORE exposing coins/challenge;
    2. Reveals `(verifierCoin1, verifierCoin2, zkbooChallenge)`;
    3. Verifies 1-of-3 active RSS open + dual `Tower128` `batchDeviationPoly` sacrifice;
    4. Releases ONLY `headsDigest`, the challenged 2-of-3 head views `(e, e+1)`, and `headCommits (e+2)`. -/
def cozkPreOpenCeremonyStep (H : Hash) (s : CoZkCommittedState) (i : CoZkCommittedInput) :
    CustodyStepOutcome CoZkCommittedState CoZkPublicEvent CoZkCeremonyReject :=
  match s.phase, i with
  | .awaiting, .freezeWires outputs headViews headSalts salt =>
    match cozkRecordExecution s.circuit outputs s.initialWires with
    | none => .rejected { s with phase := .aborted } .preOpenSacrificeFailed
    | some ex =>
      let f := cozkFreezeExecution H s ex (cozkBoundHeadViews ex headViews) headSalts salt
      .accepted { s with phase := .committed f } (.committed f.root)
  | .committed f, .challenge =>
    .accepted { s with phase := (.challenged f (cozkFrozenCoin H s f 1)
        (cozkFrozenCoin H s f 2) (cozkFrozenChallenge H s f)) }
      (.challenge f.root (cozkFrozenCoin H s f 1) (cozkFrozenCoin H s f 2)
        (cozkFrozenChallenge H s f))
  | .challenged f c₁ c₂ eChal, .verify rss =>
    if verifyRssActiveOpen rss = some 0 ∧
       batchDeviationPoly f.execution.errors c₁ = towerZero 7 ∧
       batchDeviationPoly f.execution.errors c₂ = towerZero 7 then
      .accepted { s with phase := .verified f eChal } (.verified f.root)
    else
      .rejected { s with phase := .aborted } .preOpenSacrificeFailed
  | .verified f eChal, .release =>
    .accepted { s with phase := .completed }
      (.released f.root f.headsDigest eChal
        (f.headViews eChal)
        (f.headViews (cozkNextParty eChal))
        (f.headCommits (cozkHiddenParty eChal)))
  | _, _ => .rejected { s with phase := .aborted } .invalidPhaseTransition

/-- Every release emits the exact challenged 2-of-3 head views and hidden commitment from the verified freeze. -/
theorem cozk_release_bound_to_checked_wires (H : Hash) (s s' : CoZkCommittedState)
    (root digest : List UInt8) (eChal : Fin 3) (v0 v1 hcHidden : List UInt8)
    (h : cozkPreOpenCeremonyStep H s .release =
         .accepted s' (.released root digest eChal v0 v1 hcHidden)) :
    ∃ f, s.phase = .verified f eChal ∧
      root = f.root ∧ digest = f.headsDigest ∧
      v0 = f.headViews eChal ∧ v1 = f.headViews (cozkNextParty eChal) ∧
      hcHidden = f.headCommits (cozkHiddenParty eChal) := by
  cases hp : s.phase <;> simp [cozkPreOpenCeremonyStep, hp] at h
  case verified f e =>
    rcases h with ⟨_, hr, hd, he, hv0, hv1, hhc⟩
    subst he
    exact ⟨f, rfl, hr.symm, hd.symm, hv0.symm, hv1.symm, hhc.symm⟩

/-- Verification checks ONLY the gate-error vector frozen before challenge disclosure. -/
theorem cozk_verification_checks_frozen_errors (H : Hash) (s s' : CoZkCommittedState)
    (rss : RssActiveOpenMsg) (ev : CoZkPublicEvent)
    (h : cozkPreOpenCeremonyStep H s (.verify rss) = .accepted s' ev) :
    ∃ f c₁ c₂ eChal, s.phase = .challenged f c₁ c₂ eChal ∧
      verifyRssActiveOpen rss = some 0 ∧
      batchDeviationPoly f.execution.errors c₁ = towerZero 7 ∧
      batchDeviationPoly f.execution.errors c₂ = towerZero 7 ∧
      s'.phase = .verified f eChal := by
  cases hp : s.phase <;> simp only [cozkPreOpenCeremonyStep, hp] at h
  case challenged f c₁ c₂ eChal =>
    split at h
    · rename_i hc
      cases h
      exact ⟨f, c₁, c₂, eChal, rfl, hc.1, hc.2.1, hc.2.2, rfl⟩
    · cases h
  all_goals cases h

/-- #tooth: post-challenge wire or head substitution is rejected unconditionally. -/
theorem tooth_cozk_postchallenge_wire_substitution_rejected (H : Hash)
    (s : CoZkCommittedState) (f : CoZkFrozenExecution) (a b : Tower128) (eChal : Fin 3)
    (outputs : List Tower128) (hv hs : Fin 3 → List UInt8) (salt : List UInt8) :
    cozkPreOpenCeremonyStep H { s with phase := .challenged f a b eChal }
      (.freezeWires outputs hv hs salt) =
      .rejected { s with phase := .aborted } .invalidPhaseTransition := by
  unfold cozkPreOpenCeremonyStep
  rfl

/-- Fixed-computation verifier experiment: Cartesian product of two independent uniform coins AFTER `f` is frozen. -/
def cozkAcceptingCoinPairs (f : CoZkFrozenExecution) (coins : List Tower128) : Nat :=
  let roots := coins.filter (fun r => decide (batchDeviationPoly f.execution.errors r = towerZero 7))
  roots.length * roots.length

theorem cozk_committed_experiment_bound (f : CoZkFrozenExecution) (coins : List Tower128)
    (L : Nat) (hn : coins.Nodup) (hl : f.execution.errors.length ≤ L)
    (hd : L + 1 ≤ coins.length) (he : ∃ d ∈ f.execution.errors, d ≠ towerZero 7) :
    cozkAcceptingCoinPairs f coins ≤ L * L := by
  have h := (bdoz_2lane_mac_soundness L f.execution.errors coins hn hl hd he).1
  exact Nat.mul_le_mul h h

/-- Frozen root and head commitments are completely independent of the enrolled future verifier tape. -/
theorem cozk_commit_before_coins (H : Hash) (s : CoZkCommittedState)
    (ex : CoZkExecution) (hv hs : Fin 3 → List UInt8) (salt : List UInt8)
    (a b : Tower128) (eChal : Fin 3) :
    (cozkFreezeExecution H
      { s with verifierCoin1 := a, verifierCoin2 := b, zkbooChallenge := eChal } ex hv hs salt).root =
      (cozkFreezeExecution H s ex hv hs salt).root ∧
    (cozkFreezeExecution H
      { s with verifierCoin1 := a, verifierCoin2 := b, zkbooChallenge := eChal } ex hv hs salt).headsDigest =
      (cozkFreezeExecution H s ex hv hs salt).headsDigest := by
  unfold cozkFreezeExecution cozkFreezePreimage
  exact ⟨rfl, rfl⟩

/-- Constructive (`0 Classical.choice`) commitment binding for `cozkFreezeExecution`: equal ceremony
    roots either bind `sessionTag`, `statement`, every circuit wire `ex.wires`, and all 3 party head
    commitments, OR constructively yield a `HashCollisionWitness H`. -/
def cozk_frozen_root_binding_or_collision (H : Hash)
    (s₁ s₂ : CoZkCommittedState) (ex₁ ex₂ : CoZkExecution)
    (hv₁ hs₁ hv₂ hs₂ : Fin 3 → List UInt8) (salt₁ salt₂ : List UInt8)
    (hRootEq : (cozkFreezeExecution H s₁ ex₁ hv₁ hs₁ salt₁).root =
               (cozkFreezeExecution H s₂ ex₂ hv₂ hs₂ salt₂).root) :
    PSum (HashCollisionWitness H)
      (s₁.sessionTag = s₂.sessionTag ∧
       s₁.statement = s₂.statement ∧
       ex₁.wires = ex₂.wires ∧
       (∀ j : Fin 3, (cozkFreezeExecution H s₁ ex₁ hv₁ hs₁ salt₁).headCommits j =
                     (cozkFreezeExecution H s₂ ex₂ hv₂ hs₂ salt₂).headCommits j) ∧
       salt₁ = salt₂) :=
  let hc₁ : Fin 3 → List UInt8 := fun j => cozkHeadCommit H j (hv₁ j) (hs₁ j)
  let hc₂ : Fin 3 → List UInt8 := fun j => cozkHeadCommit H j (hv₂ j) (hs₂ j)
  let pre₁ := cozkFreezePreimage s₁ ex₁ (hc₁ ⟨0, by decide⟩) (hc₁ ⟨1, by decide⟩) (hc₁ ⟨2, by decide⟩) salt₁
  let pre₂ := cozkFreezePreimage s₂ ex₂ (hc₂ ⟨0, by decide⟩) (hc₂ ⟨1, by decide⟩) (hc₂ ⟨2, by decide⟩) salt₂
  if hPre : decide (pre₁ = pre₂) = true then
    .inr <| by
      have hp := of_decide_eq_true hPre
      have hFrames := encodeMultiFrame_injective hp
      simp only [List.cons.injEq] at hFrames
      rcases hFrames with ⟨_, hTag, hStmt, _, hWires, h0, h1, h2, hSalt, _⟩
      refine ⟨hTag, hStmt, cozkEncodeWires_injective hWires, ?_, hSalt⟩
      intro j
      have hj := j.isLt
      have hc : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
      rcases hc with hj0 | hj1 | hj2
      · have he : j = ⟨0, by decide⟩ := Fin.ext hj0; subst he; exact h0
      · have he : j = ⟨1, by decide⟩ := Fin.ext hj1; subst he; exact h1
      · have he : j = ⟨2, by decide⟩ := Fin.ext hj2; subst he; exact h2
  else
    .inl
      { m1 := pre₁
        m2 := pre₂
        ne := fun hEq => hPre (decide_eq_true hEq)
        eq := hRootEq }

/-- 3rd-head privacy at release: the unopened head `cozkHiddenParty eChal` never enters the released
    opened-head pair `(openedHead0, openedHead1)`. -/
theorem cozk_hidden_head_view_noninterference (eChal : Fin 3)
    (hv₁ hv₂ : Fin 3 → List UInt8)
    (hAgreeOpened : ∀ j : Fin 3, j ≠ cozkHiddenParty eChal → hv₁ j = hv₂ j) :
    hv₁ eChal = hv₂ eChal ∧ hv₁ (cozkNextParty eChal) = hv₂ (cozkNextParty eChal) := by
  have hNe := cozkHiddenParty_ne_challenged eChal
  exact ⟨hAgreeOpened eChal hNe.1.symm, hAgreeOpened (cozkNextParty eChal) hNe.2.symm⟩

/-- Count `.released` events along a public Co-ZK event trace. -/
def cozkCountPublicReleases : List CoZkPublicEvent → Nat
  | [] => 0
  | .released _ _ _ _ _ _ :: rest => 1 + cozkCountPublicReleases rest
  | _ :: rest => cozkCountPublicReleases rest

private theorem cozk_terminal_no_releases (H : Hash)
    {s sf : CoZkCommittedState} {tr : List (CoZkCommittedInput × Option CoZkPublicEvent)}
    (hTerm : s.phase = .completed ∨ s.phase = .aborted)
    (hTr : ValidCustodyTrace (cozkPreOpenCeremonyStep H) s tr sf) :
    cozkCountPublicReleases (traceApprovedOutputs tr) = 0 ∧
    ∀ r d e v0 v1 hc, .released r d e v0 v1 hc ∉ traceApprovedOutputs tr := by
  induction hTr with
  | nil => exact ⟨rfl, fun _ _ _ _ _ _ hm => by simp [traceApprovedOutputs] at hm⟩
  | @consAccepted st st' _ inp ev rest hStep _ _ =>
    rcases hTerm with hp | hp <;> simp [cozkPreOpenCeremonyStep, hp] at hStep
  | @consRejected st st' _ inp err rest hStep _ ih =>
    simp only [traceApprovedOutputs_cons_none]
    rcases hTerm with hp | hp <;>
      (unfold cozkPreOpenCeremonyStep at hStep; rw [hp] at hStep;
       cases inp <;> cases hStep <;> exact ih (Or.inr rfl))

/-- **Multi-Turn Operational Co-ZK Ceremony Soundness (`cozk_multiturn_operational_ceremony_sound`)**:
    Across ANY multi-turn trace starting from `.awaiting`:
    1. At most **1** `.released` head-opening event can ever be emitted.
    2. Every emitted `.released root digest eChal v0 v1 hcHidden` comes from a `CoZkFrozenExecution`
       computed via `cozkRecordExecution` BEFORE `(verifierCoin1, verifierCoin2, zkbooChallenge)` were
       revealed, verified under `verifyRssActiveOpen = some 0` and BOTH `batchDeviationPoly` checks,
       with `eChal = s₀.zkbooChallenge`, `v0 = f.headViews eChal`, `v1 = f.headViews (cozkNextParty eChal)`,
       and `hcHidden = f.headCommits (cozkHiddenParty eChal)`. -/
theorem cozk_multiturn_operational_ceremony_sound (H : Hash)
    {s₀ sf : CoZkCommittedState}
    {tr : List (CoZkCommittedInput × Option CoZkPublicEvent)}
    (hInit : s₀.phase = .awaiting)
    (hTr : ValidCustodyTrace (cozkPreOpenCeremonyStep H) s₀ tr sf) :
    cozkCountPublicReleases (traceApprovedOutputs tr) ≤ 1 ∧
    (∀ root digest eChal v0 v1 hcHidden,
      .released root digest eChal v0 v1 hcHidden ∈ traceApprovedOutputs tr →
      ∃ outputs hv hs salt ex rss,
        cozkRecordExecution s₀.circuit outputs s₀.initialWires = some ex ∧
        let f := cozkFreezeExecution H s₀ ex (cozkBoundHeadViews ex hv) hs salt
        eChal = cozkFrozenChallenge H s₀ f ∧
        verifyRssActiveOpen rss = some 0 ∧
        batchDeviationPoly f.execution.errors (cozkFrozenCoin H s₀ f 1) = towerZero 7 ∧
        batchDeviationPoly f.execution.errors (cozkFrozenCoin H s₀ f 2) = towerZero 7 ∧
        root = f.root ∧ digest = f.headsDigest ∧
        v0 = f.headViews eChal ∧ v1 = f.headViews (cozkNextParty eChal) ∧
        hcHidden = f.headCommits (cozkHiddenParty eChal)) := by
  have hFromVerified : ∀ (f : CoZkFrozenExecution) {st stf : CoZkCommittedState}
      {t : List (CoZkCommittedInput × Option CoZkPublicEvent)},
      st.phase = .verified f (cozkFrozenChallenge H s₀ f) →
      ValidCustodyTrace (cozkPreOpenCeremonyStep H) st t stf →
      cozkCountPublicReleases (traceApprovedOutputs t) ≤ 1 ∧
      ∀ r d e v0 v1 hc, .released r d e v0 v1 hc ∈ traceApprovedOutputs t →
        e = (cozkFrozenChallenge H s₀ f) ∧ r = f.root ∧ d = f.headsDigest ∧
        v0 = f.headViews e ∧ v1 = f.headViews (cozkNextParty e) ∧
        hc = f.headCommits (cozkHiddenParty e) := by
    intro f st stf t hp ht
    induction ht with
    | nil => exact ⟨Nat.zero_le _, fun _ _ _ _ _ _ hm => by simp [traceApprovedOutputs] at hm⟩
    | @consAccepted a b _ inp ev rest hs hr _ =>
      unfold cozkPreOpenCeremonyStep at hs
      rw [hp] at hs
      cases inp <;> simp at hs
      rcases hs with ⟨rfl, rfl⟩
      have hTerm := cozk_terminal_no_releases H (Or.inl rfl) hr
      simp only [traceApprovedOutputs_cons_some, cozkCountPublicReleases, hTerm.1, Nat.add_zero]
      refine ⟨Nat.le_refl 1, ?_⟩
      intro r d e v0 v1 hc hm
      rcases List.mem_cons.mp hm with hEq | hTail
      · cases hEq
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact False.elim (hTerm.2 r d e v0 v1 hc hTail)
    | @consRejected a b _ inp err rest hs hr _ =>
      unfold cozkPreOpenCeremonyStep at hs
      rw [hp] at hs
      cases inp <;> simp at hs <;> rcases hs with ⟨rfl, _⟩
      all_goals
        have hTerm := cozk_terminal_no_releases H (Or.inr rfl) hr
        simp only [traceApprovedOutputs_cons_none, hTerm.1]
        exact ⟨Nat.zero_le _, fun r d e v0 v1 hc hm => False.elim (hTerm.2 r d e v0 v1 hc hm)⟩
  have hFromChallenged : ∀ (f : CoZkFrozenExecution) {st stf : CoZkCommittedState}
      {t : List (CoZkCommittedInput × Option CoZkPublicEvent)},
      st.phase = .challenged f (cozkFrozenCoin H s₀ f 1) (cozkFrozenCoin H s₀ f 2) (cozkFrozenChallenge H s₀ f) →
      ValidCustodyTrace (cozkPreOpenCeremonyStep H) st t stf →
      cozkCountPublicReleases (traceApprovedOutputs t) ≤ 1 ∧
      ∀ r d e v0 v1 hc, .released r d e v0 v1 hc ∈ traceApprovedOutputs t →
        ∃ rss, verifyRssActiveOpen rss = some 0 ∧
          batchDeviationPoly f.execution.errors (cozkFrozenCoin H s₀ f 1) = towerZero 7 ∧
          batchDeviationPoly f.execution.errors (cozkFrozenCoin H s₀ f 2) = towerZero 7 ∧
          e = (cozkFrozenChallenge H s₀ f) ∧ r = f.root ∧ d = f.headsDigest ∧
          v0 = f.headViews e ∧ v1 = f.headViews (cozkNextParty e) ∧
          hc = f.headCommits (cozkHiddenParty e) := by
    intro f st stf t hp ht
    induction ht with
    | nil => exact ⟨Nat.zero_le _, fun _ _ _ _ _ _ hm => by simp [traceApprovedOutputs] at hm⟩
    | @consAccepted a b _ inp ev rest hs hr _ =>
      unfold cozkPreOpenCeremonyStep at hs
      rw [hp] at hs
      cases inp with
      | verify rss =>
        dsimp only at hs
        split at hs
        · rename_i hChk
          rcases hs with ⟨rfl, rfl⟩
          have hv := @hFromVerified f { a with phase := .verified f (cozkFrozenChallenge H s₀ f) } _ rest rfl hr
          simp only [traceApprovedOutputs_cons_some, cozkCountPublicReleases]
          refine ⟨hv.1, ?_⟩
          intro r d e v0 v1 hc hm
          rcases List.mem_cons.mp hm with hEq | hTail
          · cases hEq
          · obtain ⟨he, hr', hd', hv0', hv1', hhc'⟩ := hv.2 r d e v0 v1 hc hTail
            exact ⟨rss, hChk.1, hChk.2.1, hChk.2.2, he, hr', hd', hv0', hv1', hhc'⟩
        · cases hs
      | _ => simp at hs
    | @consRejected a b _ inp err rest hs hr _ =>
      unfold cozkPreOpenCeremonyStep at hs
      rw [hp] at hs
      cases inp with
      | verify rss =>
        dsimp only at hs
        split at hs
        · cases hs
        · rcases hs with ⟨rfl, _⟩
          have hTerm := cozk_terminal_no_releases H (Or.inr rfl) hr
          simp only [traceApprovedOutputs_cons_none, hTerm.1]
          exact ⟨Nat.zero_le _, fun r d e v0 v1 hc hm => False.elim (hTerm.2 r d e v0 v1 hc hm)⟩
      | _ =>
        simp at hs; rcases hs with ⟨rfl, _⟩
        have hTerm := cozk_terminal_no_releases H (Or.inr rfl) hr
        simp only [traceApprovedOutputs_cons_none, hTerm.1]
        exact ⟨Nat.zero_le _, fun r d e v0 v1 hc hm => False.elim (hTerm.2 r d e v0 v1 hc hm)⟩
  have hFromCommitted : ∀ (f : CoZkFrozenExecution) {st stf : CoZkCommittedState}
      {t : List (CoZkCommittedInput × Option CoZkPublicEvent)},
      st.statement = s₀.statement →
      st.phase = .committed f →
      ValidCustodyTrace (cozkPreOpenCeremonyStep H) st t stf →
      cozkCountPublicReleases (traceApprovedOutputs t) ≤ 1 ∧
      ∀ r d e v0 v1 hc, .released r d e v0 v1 hc ∈ traceApprovedOutputs t →
        ∃ rss, verifyRssActiveOpen rss = some 0 ∧
          batchDeviationPoly f.execution.errors (cozkFrozenCoin H s₀ f 1) = towerZero 7 ∧
          batchDeviationPoly f.execution.errors (cozkFrozenCoin H s₀ f 2) = towerZero 7 ∧
          e = (cozkFrozenChallenge H s₀ f) ∧ r = f.root ∧ d = f.headsDigest ∧
          v0 = f.headViews e ∧ v1 = f.headViews (cozkNextParty e) ∧
          hc = f.headCommits (cozkHiddenParty e) := by
    intro f st stf t hstmt hp ht
    induction ht with
    | nil => exact ⟨Nat.zero_le _, fun _ _ _ _ _ _ hm => by simp [traceApprovedOutputs] at hm⟩
    | @consAccepted a b _ inp ev rest hs hr _ =>
      unfold cozkPreOpenCeremonyStep at hs
      rw [hp] at hs
      cases inp <;> simp at hs
      rcases hs with ⟨rfl, rfl⟩
      have hCh := @hFromChallenged f
        { a with phase := (.challenged f (cozkFrozenCoin H a f 1) (cozkFrozenCoin H a f 2) (cozkFrozenChallenge H a f)) } _ rest
        (by simp [cozkFrozenCoin, cozkFrozenChallenge, hstmt]) hr
      simp only [traceApprovedOutputs_cons_some, cozkCountPublicReleases]
      refine ⟨hCh.1, ?_⟩
      intro r d e v0 v1 hc hm
      rcases List.mem_cons.mp hm with hEq | hTail
      · cases hEq
      · exact hCh.2 r d e v0 v1 hc hTail
    | @consRejected a b _ inp err rest hs hr _ =>
      unfold cozkPreOpenCeremonyStep at hs
      rw [hp] at hs
      cases inp <;> simp at hs <;> rcases hs with ⟨rfl, _⟩
      all_goals
        have hTerm := cozk_terminal_no_releases H (Or.inr rfl) hr
        simp only [traceApprovedOutputs_cons_none, hTerm.1]
        exact ⟨Nat.zero_le _, fun r d e v0 v1 hc hm => False.elim (hTerm.2 r d e v0 v1 hc hm)⟩
  cases hTr with
  | nil => exact ⟨Nat.zero_le _, fun _ _ _ _ _ _ hm => by simp [traceApprovedOutputs] at hm⟩
  | @consAccepted _ st' _ inp ev rest hs hr =>
    unfold cozkPreOpenCeremonyStep at hs
    rw [hInit] at hs
    cases inp with
    | freezeWires outputs hv hsSalts salt =>
      dsimp only at hs
      cases hRec : cozkRecordExecution s₀.circuit outputs s₀.initialWires with
      | none => simp [hRec] at hs
      | some ex =>
        simp only [hRec, CustodyStepOutcome.accepted.injEq] at hs
        rcases hs with ⟨rfl, rfl⟩
        have hCm := @hFromCommitted (cozkFreezeExecution H s₀ ex (cozkBoundHeadViews ex hv) hsSalts salt)
          { s₀ with phase := .committed (cozkFreezeExecution H s₀ ex (cozkBoundHeadViews ex hv) hsSalts salt) }
          _ rest rfl rfl hr
        simp only [traceApprovedOutputs_cons_some, cozkCountPublicReleases]
        refine ⟨hCm.1, ?_⟩
        intro r d e v0 v1 hc hm
        rcases List.mem_cons.mp hm with hEq | hTail
        · cases hEq
        · obtain ⟨rss, hRss, hB1, hB2, he, hr', hd', hv0', hv1', hhc'⟩ := hCm.2 r d e v0 v1 hc hTail
          exact ⟨outputs, hv, hsSalts, salt, ex, rss, hRec, he, hRss, hB1, hB2, hr', hd', hv0', hv1', hhc'⟩
    | _ => simp at hs
  | @consRejected _ st' _ inp err rest hs hr =>
    unfold cozkPreOpenCeremonyStep at hs
    rw [hInit] at hs
    have hAb : st'.phase = .aborted := by
      cases inp with
      | freezeWires outputs hv hsSalts salt =>
        dsimp only at hs
        cases hRec : cozkRecordExecution s₀.circuit outputs s₀.initialWires <;> simp [hRec] at hs
        rcases hs with ⟨rfl, _⟩; rfl
      | _ => simp at hs; rcases hs with ⟨rfl, _⟩; rfl
    have hTerm := cozk_terminal_no_releases H (Or.inr hAb) hr
    simp only [traceApprovedOutputs_cons_none, hTerm.1]
    exact ⟨Nat.zero_le _, fun r d e v0 v1 hc hm => False.elim (hTerm.2 r d e v0 v1 hc hm)⟩

/-- Any hash admits an honest freeze/challenge/verify/release trace. Challenges
and released heads are derived from the recorded execution, not preset fixture bytes. -/
theorem inhabited_cozk_operational_ceremony_trace (H : Hash) :
    ∃ s₀ tr sf root digest e v0 v1 hc,
      s₀.phase = .awaiting ∧ ValidCustodyTrace (cozkPreOpenCeremonyStep H) s₀ tr sf ∧
      .released root digest e v0 v1 hc ∈ traceApprovedOutputs tr := by
  let s₀ : CoZkCommittedState :=
    { sessionTag := [1], statement := [2], initialWires := [], circuit := [],
      verifierCoin1 := towerZero 7, verifierCoin2 := towerZero 7 }
  let hv : Fin 3 → List UInt8 := fun _ => []
  let ex : CoZkExecution := ⟨[], []⟩
  let f := cozkFreezeExecution H s₀ ex (cozkBoundHeadViews ex hv) hv []
  let s1 := { s₀ with phase := .committed f }
  let c1 := cozkFrozenCoin H s1 f 1
  let c2 := cozkFrozenCoin H s1 f 2
  let e := cozkFrozenChallenge H s1 f
  let s2 := { s1 with phase := .challenged f c1 c2 e }
  let s3 := { s2 with phase := .verified f e }
  let s4 := { s3 with phase := .completed }
  let rss : RssActiveOpenMsg := ⟨0, 0, 0, 0, 0, 0⟩
  let ev := CoZkPublicEvent.released f.root f.headsDigest e
    (f.headViews e) (f.headViews (cozkNextParty e)) (f.headCommits (cozkHiddenParty e))
  have h1 : cozkPreOpenCeremonyStep H s₀ (.freezeWires [] hv hv []) =
      .accepted s1 (.committed f.root) := rfl
  have h2 : cozkPreOpenCeremonyStep H s1 .challenge =
      .accepted s2 (.challenge f.root c1 c2 e) := rfl
  have h3 : cozkPreOpenCeremonyStep H s2 (.verify rss) =
      .accepted s3 (.verified f.root) := by
    have hr : verifyRssActiveOpen rss = some 0 := by decide
    have hz (c : Tower128) : batchDeviationPoly [] c = towerZero 7 := by
      change towerAdd 7 (towerZero 7) (towerMul 7 c (towerZero 7)) = towerZero 7
      rw [towerMul_zero, towerAdd_zero]
    change (if verifyRssActiveOpen rss = some 0 ∧ batchDeviationPoly [] c1 = towerZero 7 ∧
        batchDeviationPoly [] c2 = towerZero 7 then _ else _) = _
    rw [ite_eq_left ⟨hr, hz c1, hz c2⟩]
  have h4 : cozkPreOpenCeremonyStep H s3 .release = .accepted s4 ev := rfl
  refine ⟨s₀, [(.freezeWires [] hv hv [], some (.committed f.root)),
    (.challenge, some (.challenge f.root c1 c2 e)), (.verify rss, some (.verified f.root)),
    (.release, some ev)], s4, f.root, f.headsDigest, e, f.headViews e, f.headViews (cozkNextParty e),
    f.headCommits (cozkHiddenParty e),
    rfl, .consAccepted h1 (.consAccepted h2 (.consAccepted h3 (.consAccepted h4 (.nil s4)))), ?_⟩
  simp [traceApprovedOutputs, ev]

/-! ### §C. Operational Rust-Aligned 2-Lane Polynomial-Basis FTS SPN, Rushing-Abort Poisoning & Domain-Prefixed Signing -/

/-- Inner shift-and-reduce loop for polynomial-basis multiplication modulo $x^{128} + x^7 + x^2 + x + 1$,
    matching `qsag_accel::gf2_128::gf2_128_mul` (`0x87#128`). -/
def ftsRustMulGo : Nat → BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128
  | 0, _, _, acc => acc
  | n + 1, x, y, acc =>
    let acc' := if y.getLsbD 0 then acc ^^^ x else acc
    let x' := (x <<< 1) ^^^ (if x.getLsbD 127 then 0x87#128 else 0#128)
    ftsRustMulGo n x' (y >>> 1) acc'

/-- Polynomial-basis multiplication modulo $x^{128} + x^7 + x^2 + x + 1$ (`gf2_128_mul`). -/
def ftsRustMul (a b : BitVec 128) : BitVec 128 :=
  ftsRustMulGo 128 a b 0#128

private theorem ftsRustMulGo_zero_right :
    ∀ (n : Nat) (x acc : BitVec 128), ftsRustMulGo n x 0#128 acc = acc
  | 0, _, acc => rfl
  | n + 1, x, acc => by
    unfold ftsRustMulGo
    have hb : (0#128 : BitVec 128).getLsbD 0 = false := rfl
    have hs : (0#128 : BitVec 128) >>> 1 = 0#128 := rfl
    rw [hb, hs]
    exact ftsRustMulGo_zero_right n _ acc

/-- Multiplicative identity on the right (`ftsRustMul a 1#128 = a`) over polynomial-basis `GF(2^128)`. -/
theorem ftsRustMul_one_right (a : BitVec 128) : ftsRustMul a 1#128 = a := by
  unfold ftsRustMul ftsRustMulGo
  have hb : (1#128 : BitVec 128).getLsbD 0 = true := rfl
  have hs : (1#128 : BitVec 128) >>> 1 = 0#128 := rfl
  rw [hb, hs]
  simp only [↓reduceIte]
  rw [ftsRustMulGo_zero_right, BitVec.zero_xor]

abbrev FtsLanes := BitVec 128 × BitVec 128

def ftsRustPow7 (x : BitVec 128) : BitVec 128 :=
  let x2 := ftsRustMul x x
  let x4 := ftsRustMul x2 x2
  ftsRustMul (ftsRustMul x x2) x4

def ftsDecodeLanes (bs : List UInt8) : FtsLanes :=
  (BitVec.ofNat 128 (ofLE (bs.take 16)), BitVec.ofNat 128 (ofLE ((bs.drop 16).take 16)))

def ftsEncodeLanes (v : FtsLanes) : List UInt8 :=
  le 16 v.1.toNat ++ le 16 v.2.toNat

/-- Domain-prefixed signing context matching `QSAG.PSFTS.SIGN_CONTEXT.V3` in `parallel_mpc.rs`. -/
def ftsSigningContextV3 (sessionSeed pkSeed : List UInt8) (epoch useCount : Nat)
    (msg quorumBytes : List UInt8) : List UInt8 :=
  cshake256Bytes ftsSignContextDomainV3
    (encodeFramedU64Le
      [sessionSeed, pkSeed, be 4 epoch, [UInt8.ofNat (useCount % 256)], msg, quorumBytes])

/-- Domain-prefixed FTS message hash matching `QSAG.PSFTS.HMSG.V2` in `parallel_mpc.rs`. -/
def ftsHmsgV2 (randomizer pkSeed rootBytes : List UInt8) (epoch grindCounter : Nat)
    (msg : List UInt8) : List UInt8 :=
  cshake256Bytes ftsHmsgDomainV2
    (encodeFramedU64Le [randomizer, pkSeed, rootBytes, be 4 epoch, be 4 grindCounter, msg])

def ftsRustRoundConstants (tweak : FtsLanes) (r : Nat) : FtsLanes :=
  ftsDecodeLanes (cshake256Bytes ftsPow7RoundDomainV4
    (encodeFramedU64Le [le 16 tweak.1.toNat, le 16 tweak.2.toNat, be 4 r]))

/-- Exact 2-lane SplitMix64 MDS diffusion matching `GF128_MDS_A` and `GF128_MDS_B` in `parallel_mpc.rs:19-20`. -/
def ftsRustMix (p : FtsLanes) : FtsLanes :=
  (p.1 ^^^ ftsRustMul p.2 0x9E3779B97F4A7C15F39CC0605CEDC835#128,
   p.2 ^^^ ftsRustMul p.1 0xBF58476D1CE4E5B994D049BB133111EB#128)

def ftsRustRoundPowers (tweak st : FtsLanes) (r : Nat) : FtsLanes :=
  let rc := ftsRustRoundConstants tweak r
  (ftsRustPow7 (st.1 ^^^ rc.1), ftsRustPow7 (st.2 ^^^ rc.2))

/-- Step-indexed helper for the 2-lane `x^7` SPN + MDS + Davies-Meyer feed-forward. -/
def evalSpnSteps (tweak : FtsLanes) : Nat → Nat → FtsLanes → FtsLanes → FtsLanes
  | 0, _, input, st => (st.1 ^^^ input.1, st.2 ^^^ input.2)
  | n + 1, r, input, st =>
    evalSpnSteps tweak n (r + 1) input (ftsRustMix (ftsRustRoundPowers tweak st r))

/-- The deployed two-lane 48-round circuit (`SPN_ROUNDS = 48`), including derived round constants,
    2-lane MDS diffusion, and Davies-Meyer feed-forward of both input lanes. -/
def evalSpn48Rounds (tweak input : FtsLanes) : FtsLanes :=
  evalSpnSteps tweak 48 0 input input

/-- Arbitrary faults at each of the two power openings of each round; MAC authority is enrolled state. -/
structure FtsRecordedOpening where
  maskedOpenings : FtsLanes
  tagDeviationLeft : FtsLanes
  tagDeviationRight : FtsLanes
  deriving DecidableEq

/-- Both independent MAC lanes authenticate each scalar opening. -/
def ftsScalarResidual (alpha : FtsLanes) (expected opened : BitVec 128)
    (deltaTag : FtsLanes) : FtsLanes :=
  (deltaTag.1 ^^^ ftsRustMul alpha.1 (opened ^^^ expected),
   deltaTag.2 ^^^ ftsRustMul alpha.2 (opened ^^^ expected))

def ftsOpeningResidual (alpha expected opened : FtsLanes)
    (deltaTag : FtsLanes × FtsLanes) : FtsLanes × FtsLanes :=
  (ftsScalarResidual alpha expected.1 opened.1 deltaTag.1,
   ftsScalarResidual alpha expected.2 opened.2 deltaTag.2)

def ftsZeroResidual : FtsLanes × FtsLanes := ((0#128, 0#128), (0#128, 0#128))

def ftsFinalResidualBytes (r : FtsLanes × FtsLanes) : List UInt8 :=
  ftsEncodeLanes r.1 ++ ftsEncodeLanes r.2

structure FtsRecordedExecution where
  output : FtsLanes
  residuals : List FtsLanes
  deriving DecidableEq

/-- Each round opens masked wire `d = x + a`, computes `(d + a)^7 = x^7` from authenticated powers of `a`,
    applies `ftsRustMix`, and records the two 2-lane BDOZ residuals. -/
def ftsRecordPowers (alpha tweak input : FtsLanes) (masks : List FtsLanes) :
    Nat → FtsLanes → List FtsRecordedOpening → FtsRecordedExecution
  | _, st, [] => ⟨(st.1 ^^^ input.1, st.2 ^^^ input.2), []⟩
  | r, st, op :: ops =>
    let a := masks.getD r (0#128, 0#128)
    let rc := ftsRustRoundConstants tweak r
    let expectedD := (st.1 ^^^ rc.1 ^^^ a.1, st.2 ^^^ rc.2 ^^^ a.2)
    let powers := (ftsRustPow7 (op.maskedOpenings.1 ^^^ a.1),
                   ftsRustPow7 (op.maskedOpenings.2 ^^^ a.2))
    let rest := ftsRecordPowers alpha tweak input masks (r + 1) (ftsRustMix powers) ops
    { output := rest.output
      residuals :=
        ftsScalarResidual alpha expectedD.1 op.maskedOpenings.1 op.tagDeviationLeft ::
        ftsScalarResidual alpha expectedD.2 op.maskedOpenings.2 op.tagDeviationRight ::
        rest.residuals }

/-- Concrete nonzero polynomial-basis dual-lane BDOZ MAC forgery witness over `GF(2^128)^2`. -/
structure FtsPolynomialMacForgery (alpha : FtsLanes) where
  delta : BitVec 128
  deltaNonzero : delta ≠ 0#128
  tagDelta : FtsLanes
  forgesLeft : ftsRustMul alpha.1 delta = tagDelta.1
  forgesRight : ftsRustMul alpha.2 delta = tagDelta.2
  deriving DecidableEq

private theorem bv128_xor_cancel_right (u v : BitVec 128) : (u ^^^ v) ^^^ v = u := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem bv128_eq_of_xor_eq_zero {u v : BitVec 128} (h : u ^^^ v = 0#128) : v = u := by
  have hx := congrArg (fun z => u ^^^ z) h
  simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.xor_zero] using hx

private def extractFtsScalarForgery (alpha : FtsLanes) (expected opened : BitVec 128)
    (deltaTag : FtsLanes) (hNe : opened ≠ expected)
    (hZero : ftsScalarResidual alpha expected opened deltaTag = (0#128, 0#128)) :
    FtsPolynomialMacForgery alpha :=
  have hPair := Prod.mk.inj hZero
  { delta := opened ^^^ expected
    deltaNonzero := fun hz => hNe (bv128_eq_of_xor_eq_zero hz).symm
    tagDelta := deltaTag
    forgesLeft := bv128_eq_of_xor_eq_zero hPair.1
    forgesRight := bv128_eq_of_xor_eq_zero hPair.2 }

/-- Constructive (`0 Classical.choice`) round-by-round SPN verification theorem: if all recorded
    BDOZ residuals vanish, either the evaluated output equals `evalSpnSteps` on zero faults, OR
    we constructively extract an explicit `FtsPolynomialMacForgery alpha` from the first faulted wire. -/
def ftsRecordPowers_authentic_or_forgery (alpha tweak input : FtsLanes) (masks : List FtsLanes) :
    ∀ (r : Nat) (st : FtsLanes) (ops : List FtsRecordedOpening),
      (ftsRecordPowers alpha tweak input masks r st ops).residuals.all (· == (0#128, 0#128)) = true →
      PSum ((ftsRecordPowers alpha tweak input masks r st ops).output =
              evalSpnSteps tweak ops.length r input st)
           (FtsPolynomialMacForgery alpha)
  | _, st, [], _ => .inl rfl
  | r, st, op :: ops, hAll =>
    let a := masks.getD r (0#128, 0#128)
    let rc := ftsRustRoundConstants tweak r
    let expectedD := (st.1 ^^^ rc.1 ^^^ a.1, st.2 ^^^ rc.2 ^^^ a.2)
    have hCons1 :
        (ftsScalarResidual alpha expectedD.1 op.maskedOpenings.1 op.tagDeviationLeft == (0#128, 0#128)) = true ∧
        (ftsScalarResidual alpha expectedD.2 op.maskedOpenings.2 op.tagDeviationRight == (0#128, 0#128)) = true ∧
        (ftsRecordPowers alpha tweak input masks (r + 1)
          (ftsRustMix (ftsRustPow7 (op.maskedOpenings.1 ^^^ a.1),
                       ftsRustPow7 (op.maskedOpenings.2 ^^^ a.2))) ops).residuals.all
          (· == (0#128, 0#128)) = true := by
      unfold ftsRecordPowers at hAll
      simp only [List.all_cons, Bool.and_eq_true] at hAll
      exact ⟨hAll.1, hAll.2.1, hAll.2.2⟩
    if hL : decide (op.maskedOpenings.1 = expectedD.1) = true then
      if hR : decide (op.maskedOpenings.2 = expectedD.2) = true then
        have hEqL : op.maskedOpenings.1 = st.1 ^^^ rc.1 ^^^ a.1 := of_decide_eq_true hL
        have hEqR : op.maskedOpenings.2 = st.2 ^^^ rc.2 ^^^ a.2 := of_decide_eq_true hR
        have hPowEq :
            (ftsRustPow7 (op.maskedOpenings.1 ^^^ a.1),
             ftsRustPow7 (op.maskedOpenings.2 ^^^ a.2)) =
            ftsRustRoundPowers tweak st r := by
          rw [hEqL, hEqR, bv128_xor_cancel_right, bv128_xor_cancel_right]
          rfl
        match hRec : ftsRecordPowers_authentic_or_forgery alpha tweak input masks (r + 1)
            (ftsRustMix (ftsRustPow7 (op.maskedOpenings.1 ^^^ a.1),
                         ftsRustPow7 (op.maskedOpenings.2 ^^^ a.2))) ops hCons1.2.2 with
        | .inr forg => .inr forg
        | .inl hOutEq =>
          .inl <| by
            unfold ftsRecordPowers
            dsimp only
            rw [hOutEq, hPowEq]
            rfl
      else
        .inr (extractFtsScalarForgery alpha expectedD.2 op.maskedOpenings.2 op.tagDeviationRight
          (fun heq => hR (decide_eq_true heq)) (eq_of_beq hCons1.2.1))
    else
      .inr (extractFtsScalarForgery alpha expectedD.1 op.maskedOpenings.1 op.tagDeviationLeft
        (fun heq => hL (decide_eq_true heq)) (eq_of_beq hCons1.1))

/-- Full 8-phase `sign_session.rs` wire state machine (`PowerCommit -> PowerOpen -> IntermediateMacCommit ->
    IntermediateMacOpen -> ValueCommit -> ValueOpen -> MacCommit -> MacOpen`) plus terminal states. -/
inductive FtsWirePhase where
  | powerCommit
  | powerOpen
  | intermediateMacCommit
  | intermediateMacOpen
  | valueCommit
  | valueOpen
  | macCommit
  | macOpen
  | completed
  | quarantined
  deriving DecidableEq, Repr

structure FtsWireState where
  epoch : Nat
  signingContext : List UInt8
  alpha : FtsLanes
  tweak : FtsLanes
  input : FtsLanes
  powerMasks : List FtsLanes
  phase : FtsWirePhase := .powerCommit
  macOpeningExposed : Bool := false
  powerCommitment : List UInt8 := []
  execution : FtsRecordedExecution := ⟨(0#128, 0#128), []⟩
  commitment : List UInt8 := []
  candidate : FtsLanes := (0#128, 0#128)
  finalResidual : FtsLanes × FtsLanes := ftsZeroResidual
  deriving DecidableEq

inductive FtsWireInput where
  | powerCommit (digest : List UInt8)
  | powerOpen (openings : List FtsRecordedOpening) (salt : List UInt8)
  | intermediateMacCommit (digest : List UInt8)
  | intermediateMacOpen (salt : List UInt8)
  | valueCommit (digest : List UInt8)
  | valueOpen (candidate : FtsLanes) (tagDeviation : FtsLanes × FtsLanes) (salt : List UInt8)
  | macCommit (digest : List UInt8)
  | macOpen (salt : List UInt8)
  deriving DecidableEq

/-- Public wire events have zero secret keys, inputs, reusable shares, or proof-evidence fields. -/
inductive FtsSpnEvent where
  | phaseAdvanced (epoch : Nat) (phase : FtsWirePhase)
  | releasedRound48Signature (epoch : Nat) (signature : List UInt8)
  deriving DecidableEq, Repr

def ftsOpeningsBytes (ops : List FtsRecordedOpening) : List UInt8 :=
  encodeMultiFrame (ops.map (fun op => encodeMultiFrame
    [ftsEncodeLanes op.maskedOpenings, ftsEncodeLanes op.tagDeviationLeft,
      ftsEncodeLanes op.tagDeviationRight]))

def ftsResidualBytes (rs : List FtsLanes) : List UInt8 :=
  encodeMultiFrame (rs.map ftsEncodeLanes)

def ftsWireCommit (H : Hash) (epoch : Nat) (signingContext : List UInt8) (domain : UInt8)
    (payload salt : List UInt8) : List UInt8 :=
  H (encodeMultiFrame [[domain], txLeb128 epoch, signingContext, payload, salt])

/-- Operational 8-phase commit-then-open SPN session matching `sign_session.rs`:
    1. `powerCommit` / `powerOpen`: commits and opens all 48 2-lane round-power masked wires;
    2. `intermediateMacCommit` / `intermediateMacOpen`: commits and opens all 96 2-lane BDOZ residuals
       (`macOpeningExposed := true`; any abort or mismatch permanently quarantines the MAC share!);
    3. `valueCommit` / `valueOpen`: commits and opens the unmasked 2-lane candidate output;
    4. `macCommit` / `macOpen`: commits and opens the final 2-lane output MAC barrier before release. -/
def ftsSpnStep (H : Hash) (s : FtsWireState) (i : FtsWireInput) :
    CustodyStepOutcome FtsWireState FtsSpnEvent FtsSpnErr :=
  match s.phase, i with
  | .powerCommit, .powerCommit digest =>
    .accepted { s with powerCommitment := digest, phase := .powerOpen }
      (.phaseAdvanced s.epoch .powerOpen)
  | .powerOpen, .powerOpen ops salt =>
    if ops.length = 48 ∧ s.powerMasks.length = 48 ∧
       ftsWireCommit H s.epoch s.signingContext 0 (ftsOpeningsBytes ops) salt = s.powerCommitment then
      let ex := ftsRecordPowers s.alpha s.tweak s.input s.powerMasks 0 s.input ops
      .accepted { s with execution := ex, phase := .intermediateMacCommit }
        (.phaseAdvanced s.epoch .intermediateMacCommit)
    else
      .rejected { s with phase := .quarantined } .intermediateMacOrCommitFailed
  | .intermediateMacCommit, .intermediateMacCommit digest =>
    .accepted { s with commitment := digest, phase := .intermediateMacOpen }
      (.phaseAdvanced s.epoch .intermediateMacOpen)
  | .intermediateMacOpen, .intermediateMacOpen salt =>
    if s.execution.residuals.all (fun r => r == (0#128, 0#128)) ∧
       ftsWireCommit H s.epoch s.signingContext 1 (ftsResidualBytes s.execution.residuals) salt = s.commitment then
      .accepted { s with phase := .valueCommit, macOpeningExposed := true }
        (.phaseAdvanced s.epoch .valueCommit)
    else
      .rejected { s with phase := .quarantined, macOpeningExposed := true } .intermediateMacOrCommitFailed
  | .valueCommit, .valueCommit digest =>
    .accepted { s with commitment := digest, phase := .valueOpen }
      (.phaseAdvanced s.epoch .valueOpen)
  | .valueOpen, .valueOpen candidate tagDelta salt =>
    if ftsWireCommit H s.epoch s.signingContext 2 (ftsEncodeLanes candidate) salt = s.commitment then
      let finRes := ftsOpeningResidual s.alpha s.execution.output candidate tagDelta
      .accepted { s with candidate := candidate, finalResidual := finRes, phase := .macCommit }
        (.phaseAdvanced s.epoch .macCommit)
    else
      .rejected { s with phase := .quarantined } .intermediateMacOrCommitFailed
  | .macCommit, .macCommit digest =>
    .accepted { s with commitment := digest, phase := .macOpen }
      (.phaseAdvanced s.epoch .macOpen)
  | .macOpen, .macOpen salt =>
    if s.finalResidual = ftsZeroResidual ∧
       ftsWireCommit H s.epoch s.signingContext 3 (ftsFinalResidualBytes s.finalResidual) salt = s.commitment then
      .accepted { s with phase := .completed, macOpeningExposed := true }
        (.releasedRound48Signature s.epoch (ftsEncodeLanes s.candidate))
    else
      .rejected { s with phase := .quarantined, macOpeningExposed := true } .intermediateMacOrCommitFailed
  | _, _ =>
    .rejected { s with phase := .quarantined } .intermediateMacOrCommitFailed

/-- #tooth: `valueOpen` never releases a signature without the subsequent `macCommit`/`macOpen` barrier. -/
theorem tooth_fts_value_open_not_release (H : Hash) (s s' : FtsWireState)
    (v : FtsLanes) (d : FtsLanes × FtsLanes) (salt sig : List UInt8) (ep : Nat) :
    ftsSpnStep H s (.valueOpen v d salt) ≠ .accepted s' (.releasedRound48Signature ep sig) := by
  intro h
  cases hp : s.phase <;> simp only [ftsSpnStep, hp] at h
  case valueOpen => split at h <;> cases h
  all_goals cases h

/-- Every operational signature release passes the final `macOpen` barrier. -/
theorem fts_wire_release_requires_final_mac (H : Hash) (s s' : FtsWireState)
    (i : FtsWireInput) (ep : Nat) (sig : List UInt8)
    (h : ftsSpnStep H s i = .accepted s' (.releasedRound48Signature ep sig)) :
    s.phase = .macOpen ∧ s.finalResidual = ftsZeroResidual ∧
    ep = s.epoch ∧ sig = ftsEncodeLanes s.candidate := by
  cases hp : s.phase <;> cases i <;> simp only [ftsSpnStep, hp] at h
  case macOpen.macOpen salt =>
    if hc : s.finalResidual = ftsZeroResidual ∧
            ftsWireCommit H s.epoch s.signingContext 3 (ftsFinalResidualBytes s.finalResidual) salt = s.commitment then
      rw [ite_eq_left hc] at h
      rcases CustodyStepOutcome.accepted.inj h with ⟨rfl, hEv⟩
      rcases FtsSpnEvent.releasedRound48Signature.inj hEv with ⟨rfl, rfl⟩
      exact ⟨rfl, hc.1, rfl, rfl⟩
    else
      rw [ite_eq_right hc] at h
      cases h
  all_goals first | cases h | (split at h <;> cases h)

private theorem ftsSpnStep_release_completed (H : Hash) {s s' : FtsWireState}
    {i : FtsWireInput} {ep : Nat} {sig : List UInt8}
    (h : ftsSpnStep H s i = .accepted s' (.releasedRound48Signature ep sig)) :
    s'.phase = .completed := by
  cases hp : s.phase <;> cases i <;> simp only [ftsSpnStep, hp] at h
  case macOpen.macOpen salt =>
    if hc : s.finalResidual = ftsZeroResidual ∧
            ftsWireCommit H s.epoch s.signingContext 3 (ftsFinalResidualBytes s.finalResidual) salt = s.commitment then
      rw [ite_eq_left hc] at h
      rcases CustodyStepOutcome.accepted.inj h with ⟨rfl, _⟩
      rfl
    else
      rw [ite_eq_right hc] at h
      cases h
  all_goals first | cases h | (split at h <;> cases h)

/-- Constructive (`0 Classical.choice`) end-to-end 48-round 2-lane SPN + final-output MAC soundness:
    when `ops.length = 48` passes `intermediateMacOpen` and `candidate` passes `macOpen`, either
    `candidate = evalSpn48Rounds tweak input` OR we constructively extract `FtsPolynomialMacForgery alpha`. -/
def fts_spn_release_authentic_or_forgery (alpha tweak input : FtsLanes)
    (masks : List FtsLanes) (ops : List FtsRecordedOpening)
    (candidate : FtsLanes) (finalTagDelta : FtsLanes × FtsLanes)
    (hLen : ops.length = 48)
    (hInterm : (ftsRecordPowers alpha tweak input masks 0 input ops).residuals.all
                 (· == (0#128, 0#128)) = true)
    (hFinal : ftsOpeningResidual alpha
                (ftsRecordPowers alpha tweak input masks 0 input ops).output
                candidate finalTagDelta = ftsZeroResidual) :
    PSum (candidate = evalSpn48Rounds tweak input) (FtsPolynomialMacForgery alpha) :=
  match ftsRecordPowers_authentic_or_forgery alpha tweak input masks 0 input ops hInterm with
  | .inr forg => .inr forg
  | .inl hExecEq =>
    let exOut := (ftsRecordPowers alpha tweak input masks 0 input ops).output
    have hPair := Prod.mk.inj hFinal
    if hL : decide (candidate.1 = exOut.1) = true then
      if hR : decide (candidate.2 = exOut.2) = true then
        .inl <| by
          have hcEq : candidate = exOut := Prod.ext (of_decide_eq_true hL) (of_decide_eq_true hR)
          rw [hcEq]
          dsimp only [exOut]
          rw [hExecEq, hLen]
          rfl
      else
        .inr (extractFtsScalarForgery alpha exOut.2 candidate.2 finalTagDelta.2
          (fun heq => hR (decide_eq_true heq)) hPair.2)
    else
      .inr (extractFtsScalarForgery alpha exOut.1 candidate.1 finalTagDelta.1
        (fun heq => hL (decide_eq_true heq)) hPair.1)

/-- #tooth: without a forged tag deviation (`tagDelta = (0, 0)`), injecting a unit fault `1#128`
    on ANY wire under enrolled `alpha.1 ≠ 0#128` produces nonzero BDOZ residual `alpha.1 ≠ 0#128`! -/
theorem tooth_fts_unit_fault_detected_without_tag_forgery (alpha : FtsLanes)
    (expected : BitVec 128) (hAlpha : alpha.1 ≠ 0#128) :
    ftsScalarResidual alpha expected (expected ^^^ 1#128) (0#128, 0#128) ≠ (0#128, 0#128) := by
  intro hZero
  have h1 := (Prod.mk.inj hZero).1
  unfold ftsScalarResidual at h1
  dsimp only at h1
  have hDelta : (expected ^^^ 1#128) ^^^ expected = 1#128 := by
    rw [BitVec.xor_comm expected 1#128, bv128_xor_cancel_right]
  rw [hDelta, BitVec.zero_xor, ftsRustMul_one_right] at h1
  exact hAlpha h1

def ftsPublicObservation : FtsSpnEvent → Nat × Sum FtsWirePhase (List UInt8)
  | .phaseAdvanced ep phase => (ep, .inl phase)
  | .releasedRound48Signature ep signature => (ep, .inr signature)

def ftsPublicObservationInverse : Nat × Sum FtsWirePhase (List UInt8) → FtsSpnEvent
  | (ep, .inl phase) => .phaseAdvanced ep phase
  | (ep, .inr signature) => .releasedRound48Signature ep signature

/-- Trace-level noninterference modulo authorized signature/phase disclosure:
    `FtsSpnEvent` carries zero hidden secret-key or proof-evidence fields. -/
theorem fts_wire_trace_no_extra_secret_fields (xs ys : List FtsSpnEvent)
    (h : xs.map ftsPublicObservation = ys.map ftsPublicObservation) : xs = ys := by
  have hId : ∀ zs : List FtsSpnEvent, (zs.map ftsPublicObservation).map ftsPublicObservationInverse = zs := by
    intro zs
    induction zs with
    | nil => rfl
    | cons z rest ih =>
      cases z <;> simp only [List.map_cons, ftsPublicObservation, ftsPublicObservationInverse, ih]
  rw [← hId xs, ← hId ys, h]

/-- Public parameters absorbed by the distributed FTS signing transcript. -/
structure FtsDistributedContext where
  roster : List UInt16
  merkleRoot : List UInt64
  treeHeight : Nat
  winternitzW : Nat
  numChains : Nat
  targetSum : Nat
  count : UInt8
  leafMode : Bool
  deriving DecidableEq

def ftsDistributedSigningContextV4 (c : FtsDistributedContext)
    (sid pkSeed : List UInt8) (epoch : Nat) (msg : List UInt8) : List UInt8 :=
  let context := c.roster.flatMap (fun i => be 2 i.toNat) ++
    c.merkleRoot.flatMap (fun x => le 8 x.toNat) ++
    [c.treeHeight, c.winternitzW, c.numChains, c.targetSum].flatMap (be 8)
  cshake256Bytes "QSAG.PSFTS.DISTRIBUTED.V4".toUTF8.data.toList
    (encodeFramedU64Le [sid, pkSeed, be 4 epoch,
      [c.count, if c.leafMode then 1 else 0], msg, context])

structure FtsOperationalGuard where
  enrolledAlpha : FtsLanes
  alphaLeftNonzero : enrolledAlpha.1 ≠ 0#128
  alphaRightNonzero : enrolledAlpha.2 ≠ 0#128
  pkSeed : List UInt8 := List.replicate 32 0
  enrolledInput : FtsLanes
  powerMaskTape : List FtsLanes
  distributedContext : Option FtsDistributedContext := none
  burnedEpochs : List Nat := []
  active : Option FtsWireState := none
  quarantined : Bool := false
  deriving DecidableEq

inductive FtsOperationalInput where
  | beginEpoch (epoch : Nat) (publicTweak : FtsLanes) (sessionSeed msg quorumBytes : List UInt8)
  | session (input : FtsWireInput)
  deriving DecidableEq

/-- Epoch burn precedes every opening. MAC exposure permanently quarantines the
long-term share; earlier protocol rejection burns the epoch and discards the session. -/
def ftsSpnEpochStep (H : Hash) (s : FtsOperationalGuard) (i : FtsOperationalInput) :
    CustodyStepOutcome FtsOperationalGuard FtsSpnEvent FtsSpnErr :=
  if s.quarantined then
    .rejected s .macContextQuarantined
  else
    match s.active, i with
    | none, .beginEpoch ep tweak sessSeed msg quorumBytes =>
      if ep ∈ s.burnedEpochs ∨ 2 ^ 32 ≤ ep ∨ s.powerMaskTape.length < 48 then
        .rejected s .epochAlreadyBurned
      else
        let ctx := match s.distributedContext with
          | none => ftsSigningContextV3 sessSeed s.pkSeed ep 1 msg quorumBytes
          | some c => ftsDistributedSigningContextV4 c sessSeed s.pkSeed ep msg
        let activeState : FtsWireState :=
          { epoch := ep
            signingContext := ctx
            alpha := s.enrolledAlpha
            tweak := tweak
            input := s.enrolledInput
            powerMasks := s.powerMaskTape.take 48 }
        let s' : FtsOperationalGuard :=
          { s with
            burnedEpochs := ep :: s.burnedEpochs
            powerMaskTape := s.powerMaskTape.drop 48
            active := some activeState }
        .accepted s' (.phaseAdvanced ep .powerCommit)
    | some active, .session inp =>
      match ftsSpnStep H active inp with
      | .rejected _ err =>
        .rejected { s with active := none, quarantined := (active.macOpeningExposed || active.phase == .intermediateMacOpen || active.phase == .macOpen) } err
      | .accepted next event =>
        let nextActive := if next.phase == .completed then none else some next
        .accepted { s with active := nextActive } event
    | _, _ =>
      .rejected s .sessionBusyOrWrongPhase

/-- #tooth: an already consumed epoch cannot restart, regardless of public tweak or message. -/
theorem tooth_fts_epoch_burn_survives_sessions (H : Hash) (s : FtsOperationalGuard)
    (ep : Nat) (tweak : FtsLanes) (sessSeed msg qBytes : List UInt8)
    (hq : s.quarantined = false) (ha : s.active = none) (hb : ep ∈ s.burnedEpochs) :
    ftsSpnEpochStep H s (.beginEpoch ep tweak sessSeed msg qBytes) =
      .rejected s .epochAlreadyBurned := by
  simp [ftsSpnEpochStep, hq, ha, hb]

/-- #tooth: any mismatch or rushing abort during `intermediateMacOpen` or `macOpen` permanently
    poisons (`quarantined = true`) the `FtsOperationalGuard` share. -/
theorem tooth_fts_rushing_mac_abort_quarantines_guard (H : Hash) (s : FtsOperationalGuard)
    (active : FtsWireState) (salt : List UInt8)
    (hq : s.quarantined = false) (ha : s.active = some active)
    (hPhase : active.phase = .intermediateMacOpen)
    (hBad : ftsWireCommit H active.epoch active.signingContext 1
              (ftsResidualBytes active.execution.residuals) salt ≠ active.commitment) :
    ftsSpnEpochStep H s (.session (.intermediateMacOpen salt)) =
      .rejected { s with active := none, quarantined := true } .intermediateMacOrCommitFailed := by
  unfold ftsSpnEpochStep
  simp only [hq, Bool.false_eq_true, ↓reduceIte, ha]
  unfold ftsSpnStep
  simp [hPhase, hBad]

theorem fts_epoch_quarantine_wire_silence (H : Hash) (s : FtsOperationalGuard)
    (hq : s.quarantined = true) (inputs : List FtsOperationalInput) :
    custodyWireTrace (ftsSpnEpochStep H) s inputs = List.replicate inputs.length none := by
  induction inputs with
  | nil => rfl
  | cons i rest ih =>
    simp only [custodyWireTrace, ftsSpnEpochStep, hq, ↓reduceIte, ih, List.length_cons,
               List.replicate_succ]

def ftsOperationalReleasedEpochs : List FtsSpnEvent → List Nat
  | [] => []
  | .releasedRound48Signature ep _ :: rest => ep :: ftsOperationalReleasedEpochs rest
  | .phaseAdvanced _ _ :: rest => ftsOperationalReleasedEpochs rest

private theorem ftsSpnStep_preserves_epoch (H : Hash) {w w' : FtsWireState}
    {i : FtsWireInput} {ev : FtsSpnEvent}
    (h : ftsSpnStep H w i = .accepted w' ev) : w'.epoch = w.epoch := by
  cases hp : w.phase <;> cases i <;> simp only [ftsSpnStep, hp] at h
  all_goals first
    | cases h
    | (split at h <;> try cases h)
  all_goals first | rfl | (rcases h with ⟨rfl, _⟩; rfl)

private theorem ftsOperational_burned_not_released (H : Hash)
    {s sf : FtsOperationalGuard} {tr : List (FtsOperationalInput × Option FtsSpnEvent)}
    (hAct : ∀ w, s.active = some w → w.epoch ∈ s.burnedEpochs)
    (hTr : ValidCustodyTrace (ftsSpnEpochStep H) s tr sf) :
    ∀ x ∈ s.burnedEpochs,
      (∀ w, s.active = some w → w.epoch ≠ x) →
      x ∉ ftsOperationalReleasedEpochs (traceApprovedOutputs tr) := by
  induction hTr with
  | nil => intro _ _ _ hm; cases hm
  | @consAccepted st st' _ inp ev rest hs _ ih =>
    intro x hx hNotAct
    unfold ftsSpnEpochStep at hs
    if hq : st.quarantined = true then simp [hq] at hs
    else
      simp only [hq, Bool.false_eq_true, ↓reduceIte] at hs
      cases hA : st.active with
      | none =>
        cases inp with
        | session _ => simp [hA] at hs
        | beginEpoch ep tw ss msg qb =>
          simp only [hA] at hs
          if hRej : ep ∈ st.burnedEpochs ∨ 2 ^ 32 ≤ ep ∨ st.powerMaskTape.length < 48 then
            simp [hRej] at hs
          else
            simp only [hRej, ↓reduceIte, CustodyStepOutcome.accepted.injEq] at hs
            rcases hs with ⟨rfl, rfl⟩
            have hNeEp : ep ≠ x := fun hEq => hRej (Or.inl (hEq ▸ hx))
            simp only [traceApprovedOutputs_cons_some, ftsOperationalReleasedEpochs]
            refine ih ?_ x (.tail _ hx) ?_
            · intro w hw; simp at hw; subst hw; exact .head _
            · intro w hw; simp at hw; subst hw; exact hNeEp
      | some w =>
        cases inp with
        | beginEpoch _ _ _ _ _ => simp [hA] at hs
        | session winp =>
          simp only [hA] at hs
          cases hWs : ftsSpnStep H w winp with
          | rejected _ _ => simp [hWs] at hs
          | accepted wNext wEv =>
            simp only [hWs, CustodyStepOutcome.accepted.injEq] at hs
            rcases hs with ⟨rfl, rfl⟩
            have hwEp := ftsSpnStep_preserves_epoch H hWs
            have hwNe : w.epoch ≠ x := hNotAct w hA
            cases wEv with
            | phaseAdvanced _ _ =>
              simp only [traceApprovedOutputs_cons_some, ftsOperationalReleasedEpochs]
              refine ih ?_ x hx ?_
              · intro w' hw'
                by_cases hc : (wNext.phase == .completed) = true
                · simp [hc] at hw'
                · simp [hc] at hw'; subst hw'; rw [hwEp]; exact hAct w hA
              · intro w' hw'
                by_cases hc : (wNext.phase == .completed) = true
                · simp [hc] at hw'
                · simp [hc] at hw'; subst hw'; rw [hwEp]; exact hwNe
            | releasedRound48Signature epOut sig =>
              have hRel := fts_wire_release_requires_final_mac H w wNext winp epOut sig hWs
              have hComp : wNext.phase = .completed := by
                cases hp : w.phase <;> cases winp <;> simp only [ftsSpnStep, hp] at hWs
                all_goals first | cases hWs | (split at hWs <;> try cases hWs)
                all_goals first | rfl | (rcases hWs with ⟨rfl, _⟩; rfl)
              simp only [traceApprovedOutputs_cons_some, ftsOperationalReleasedEpochs, List.mem_cons]
              rintro (hEq | hTail)
              · exact hwNe (hRel.2.2.1.symm.trans hEq.symm)
              · exact ih (fun w' hw' => by simp [hComp] at hw') x hx
                  (fun w' hw' => by simp [hComp] at hw') hTail
  | @consRejected st st' _ inp err rest hs _ ih =>
    intro x hx hNotAct
    simp only [traceApprovedOutputs_cons_none]
    unfold ftsSpnEpochStep at hs
    if hq : st.quarantined = true then
      simp [hq] at hs; rcases hs with ⟨rfl, _⟩; exact ih hAct x hx hNotAct
    else
      simp only [hq, Bool.false_eq_true, ↓reduceIte] at hs
      cases hA : st.active with
      | none =>
        cases inp with
        | session _ => simp [hA] at hs; rcases hs with ⟨rfl, _⟩; exact ih hAct x hx hNotAct
        | beginEpoch ep tw ss msg qb =>
          simp only [hA] at hs
          split at hs <;> simp at hs
          rcases hs with ⟨rfl, _⟩; exact ih hAct x hx hNotAct
      | some w =>
        cases inp with
        | beginEpoch _ _ _ _ _ => simp [hA] at hs; rcases hs with ⟨rfl, _⟩; exact ih hAct x hx hNotAct
        | session winp =>
          simp only [hA] at hs
          cases hWs : ftsSpnStep H w winp <;> simp [hWs] at hs
          rcases hs with ⟨rfl, _⟩
          exact ih (fun _ hw => by cases hw) x hx (fun _ hw => by cases hw)

/-- **Multi-Epoch Operational FTS SPN Soundness (`fts_operational_multiepoch_sound`)**:
    Across ANY multi-turn trace of `ftsSpnEpochStep` starting from an idle guard (`s₀.active = none`):
    1. `(ftsOperationalReleasedEpochs (traceApprovedOutputs tr)).Nodup` — zero epoch reuse across sessions!
    2. Every released epoch was unburned at `s₀` (`ep ∉ s₀.burnedEpochs`). -/
theorem fts_operational_multiepoch_sound (H : Hash)
    {s₀ sf : FtsOperationalGuard} {tr : List (FtsOperationalInput × Option FtsSpnEvent)}
    (hIdle : s₀.active = none)
    (hTr : ValidCustodyTrace (ftsSpnEpochStep H) s₀ tr sf) :
    (ftsOperationalReleasedEpochs (traceApprovedOutputs tr)).Nodup ∧
    (∀ ep ∈ ftsOperationalReleasedEpochs (traceApprovedOutputs tr), ep ∉ s₀.burnedEpochs) := by
  have hCore : ∀ {s sf' : FtsOperationalGuard}
      {t : List (FtsOperationalInput × Option FtsSpnEvent)},
      (∀ w, s.active = some w → w.epoch ∈ s.burnedEpochs) →
      ValidCustodyTrace (ftsSpnEpochStep H) s t sf' →
      (ftsOperationalReleasedEpochs (traceApprovedOutputs t)).Nodup := by
    intro s sf' t hAct ht
    induction ht with
    | nil => exact .nil
    | @consAccepted st st' _ inp ev rest hs hr ih =>
      unfold ftsSpnEpochStep at hs
      if hq : st.quarantined = true then simp [hq] at hs
      else
        simp only [hq, Bool.false_eq_true, ↓reduceIte] at hs
        cases hA : st.active with
        | none =>
          cases inp with
          | session _ => simp [hA] at hs
          | beginEpoch ep tw ss msg qb =>
            simp only [hA] at hs
            split at hs
            · cases hs
            · rcases hs with ⟨rfl, rfl⟩
              simp only [traceApprovedOutputs_cons_some, ftsOperationalReleasedEpochs]
              exact ih (fun w hw => by simp at hw; subst hw; exact .head _)
        | some w =>
          cases inp with
          | beginEpoch _ _ _ _ _ => simp [hA] at hs
          | session winp =>
            simp only [hA] at hs
            cases hWs : ftsSpnStep H w winp with
            | rejected _ _ => simp [hWs] at hs
            | accepted wNext wEv =>
              simp only [hWs, CustodyStepOutcome.accepted.injEq] at hs
              rcases hs with ⟨rfl, rfl⟩
              have hwEp := ftsSpnStep_preserves_epoch H hWs
              cases wEv with
              | phaseAdvanced _ _ =>
                simp only [traceApprovedOutputs_cons_some, ftsOperationalReleasedEpochs]
                refine ih ?_
                intro w' hw'
                by_cases hc : (wNext.phase == .completed) = true
                · simp [hc] at hw'
                · simp [hc] at hw'; subst hw'; rw [hwEp]; exact hAct w hA
              | releasedRound48Signature epOut sig =>
                have hRel := fts_wire_release_requires_final_mac H w wNext winp epOut sig hWs
                have hComp : wNext.phase = .completed := by
                  cases hp : w.phase <;> cases winp <;> simp only [ftsSpnStep, hp] at hWs
                  all_goals first | cases hWs | (split at hWs <;> try cases hWs)
                  all_goals first | rfl | (rcases hWs with ⟨rfl, _⟩; rfl)
                have hNotInRest : epOut ∉ ftsOperationalReleasedEpochs (traceApprovedOutputs rest) := by
                  have hBurned : epOut ∈ st.burnedEpochs := hRel.2.2.1 ▸ hAct w hA
                  exact ftsOperational_burned_not_released H
                    (fun w' hw' => by simp [hComp] at hw') hr epOut hBurned
                    (fun w' hw' => by simp [hComp] at hw')
                simp only [traceApprovedOutputs_cons_some, ftsOperationalReleasedEpochs]
                exact .cons (fun y hy hEq => hNotInRest (hEq ▸ hy))
                  (ih (fun w' hw' => by simp [hComp] at hw'))
    | @consRejected st st' _ inp err rest hs _ ih =>
      simp only [traceApprovedOutputs_cons_none]
      unfold ftsSpnEpochStep at hs
      if hq : st.quarantined = true then
        simp [hq] at hs; rcases hs with ⟨rfl, _⟩; exact ih hAct
      else
        simp only [hq, Bool.false_eq_true, ↓reduceIte] at hs
        cases hA : st.active with
        | none =>
          cases inp <;> try simp only [hA] at hs
          · split at hs <;> try simp only [CustodyStepOutcome.rejected.injEq] at hs
            all_goals first | (rcases hs with ⟨rfl, _⟩; exact ih hAct) | (cases hs)
          · rcases hs with ⟨rfl, _⟩; exact ih hAct
        | some w =>
          cases inp with
          | beginEpoch _ _ _ _ _ =>
            simp only [hA, CustodyStepOutcome.rejected.injEq] at hs
            rcases hs with ⟨rfl, _⟩; exact ih hAct
          | session winp =>
            simp only [hA] at hs
            cases hWs : ftsSpnStep H w winp with
            | accepted next event => simp [hWs] at hs
            | rejected next err =>
              simp only [hWs, CustodyStepOutcome.rejected.injEq] at hs
              rcases hs with ⟨rfl, _⟩; exact ih (fun _ hw => by cases hw)
  refine ⟨hCore (fun w hw => by rw [hIdle] at hw; cases hw) hTr, ?_⟩
  intro ep hMem hIn0
  exact ftsOperational_burned_not_released H
    (fun w hw => by rw [hIdle] at hw; cases hw) hTr ep hIn0
    (fun w hw => by rw [hIdle] at hw; cases hw) hMem

/-! ### §D. Operational HD Query-Budget Privacy, Multi-Turn Soundness & Unmasked Radix-5 Separation -/

/-- Observable HD events contain only a query identifier, lineage flag, and MASKED opening. -/
inductive HdZeroTestEvent where
  | commitsFrozen (query : Nat) (hardened : Bool)
  | scalarReleased (query : Nat) (hardened : Bool) (maskedOpening : HdFq204)
  deriving DecidableEq, Repr

structure HdMaskedPending (n : Nat) where
  query : Nat
  sessionTag : List UInt8
  maskedTrue : HdFq204
  candidate : HdFq204
  commits : Fin n → List UInt8

/-- `observations` is the enrolled one-time masked projection tape; raw secrets are never retained. -/
structure HdMaskedState (n d1 d2 Q : Nat) where
  observations : Fin Q → HdFq204
  alpha : HdFq204
  alphaNonzero : alpha ≠ HdFq204.zero
  hardened : Bool
  used : Nat := 0
  pending : Option (HdMaskedPending n) := none
  quarantined : Bool := false

inductive HdMaskedInput (n : Nat) where
  | freeze (sessionTag : List UInt8) (candidate : HdFq204) (commits : Fin n → List UInt8)
  | openResiduals (residuals : Fin n → HdFq204) (salts : Fin n → List UInt8)

/-- Actual masked scalar observation used by BOTH operational execution and posterior fiber proofs. -/
def hdMaskedObservation (d1 Q : Nat) (forms : Fin Q → Fin d1 → HdFq204)
    (secret : Fin d1 → HdFq204) (masks : Fin Q → HdFq204) : Fin Q → HdFq204 :=
  fun q => HdFq204.add (evalLinearForm d1 (forms q) secret) (masks q)

def hdMaskedEnroll (n d1 d2 Q : Nat)
    (A : Fin d2 → Fin d1 → HdFq204) (t : Fin d2 → HdFq204)
    (secret : ShortMlweWitness hdCbdEta d1 d2 A t)
    (forms : Fin Q → Fin d1 → HdFq204) (masks : Fin Q → HdFq204)
    (alpha : HdFq204) (ha : alpha ≠ HdFq204.zero) (hard : Bool) : HdMaskedState n d1 d2 Q :=
  { observations := hdMaskedObservation d1 Q forms secret.val.1 masks
    alpha := alpha
    alphaNonzero := ha
    hardened := hard }

/-- A projection index addresses an already-public row of the flattened module
relation. General arbitrary forms remain available for the abstract privacy theorem. -/
structure AuthorizedHdProjection (d2 : Nat) where
  publicRelationCoefficient : Fin d2

def hdAuthorizedEnroll (n d1 d2 Q : Nat)
    (A : Fin d2 → Fin d1 → HdFq204) (t : Fin d2 → HdFq204)
    (secret : ShortMlweWitness hdCbdEta d1 d2 A t)
    (projections : Fin Q → AuthorizedHdProjection d2) (masks : Fin Q → HdFq204)
    (alpha : HdFq204) (ha : alpha ≠ HdFq204.zero) (parentHard requestedHard : Bool) :
    Option (HdMaskedState n d1 d2 Q) :=
  if parentHard && !requestedHard then none else
    some (hdMaskedEnroll n d1 d2 Q A t secret
      (fun q => A (projections q).publicRelationCoefficient) masks alpha ha requestedHard)

theorem hd_hardened_parent_rejects_downgrade (n d1 d2 Q : Nat)
    (A : Fin d2 → Fin d1 → HdFq204) (t : Fin d2 → HdFq204)
    (secret : ShortMlweWitness hdCbdEta d1 d2 A t)
    (projections : Fin Q → AuthorizedHdProjection d2) (masks : Fin Q → HdFq204)
    (alpha : HdFq204) (ha : alpha ≠ HdFq204.zero) :
    hdAuthorizedEnroll n d1 d2 Q A t secret projections masks alpha ha true false = none := by
  unfold hdAuthorizedEnroll
  rfl

def hdZeroTestStep (H : Hash) (n d1 d2 Q : Nat)
    (s : HdMaskedState n d1 d2 Q) (i : HdMaskedInput n) :
    CustodyStepOutcome (HdMaskedState n d1 d2 Q) HdZeroTestEvent HdErr :=
  if s.quarantined then
    .rejected s .familyQuarantined
  else
    match s.pending, i with
    | none, .freeze tag candidate commits =>
      if h : s.used < Q then
        let q : Fin Q := ⟨s.used, h⟩
        let expected := s.observations q
        let s' : HdMaskedState n d1 d2 Q :=
          { s with
            used := s.used + 1
            pending := some ⟨s.used, tag, expected, candidate, commits⟩ }
        .accepted s' (.commitsFrozen s.used s.hardened)
      else
        .rejected s .queryBudgetExceeded
    | some f, .openResiduals residuals salts =>
      if verifyAllHdCommits H f.sessionTag s.hardened n f.commits residuals salts = true ∧
         finHdFq204Sum n residuals = HdFq204.zero ∧
         finHdFq204Sum n residuals =
           HdFq204.mul s.alpha (HdFq204.sub f.candidate f.maskedTrue) then
        .accepted { s with pending := none } (.scalarReleased f.query s.hardened f.candidate)
      else
        .rejected { s with pending := none, quarantined := true } .zeroTestOrCommitmentMismatch
    | _, _ =>
      .rejected s .invalidSessionPhase

/-- Acceptance is tied to enrolled nonzero MAC authority `s.alpha ≠ 0` over prime field `HdFq204`. -/
theorem hd_masked_release_sound (n d1 d2 Q : Nat)
    (s : HdMaskedState n d1 d2 Q) (f : HdMaskedPending n)
    (residuals : Fin n → HdFq204)
    (hc : finHdFq204Sum n residuals = HdFq204.zero)
    (hm : finHdFq204Sum n residuals = HdFq204.mul s.alpha (HdFq204.sub f.candidate f.maskedTrue)) :
    f.candidate = f.maskedTrue := by
  have hz : HdFq204.mul s.alpha (HdFq204.sub f.candidate f.maskedTrue) = HdFq204.zero :=
    hm.symm.trans hc
  have hd := NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz
  rcases hd with ha | hd
  · exact False.elim (s.alphaNonzero ha)
  · exact (LawfulCommRing.sub_eq_zero_iff (R := HdFq204)).mp hd

def hdOperationalReleasedQueries : List HdZeroTestEvent → List Nat
  | [] => []
  | .scalarReleased q _ _ :: rest => q :: hdOperationalReleasedQueries rest
  | .commitsFrozen _ _ :: rest => hdOperationalReleasedQueries rest

/-- Invariant relating `pending` to `used` and `observations` along operational HD traces. -/
def HdOperationalInv {n d1 d2 Q : Nat} (s : HdMaskedState n d1 d2 Q) : Prop :=
  s.used ≤ Q ∧
  match s.pending with
  | none => True
  | some f => ∃ hq : f.query < Q, f.query < s.used ∧ f.maskedTrue = s.observations ⟨f.query, hq⟩

private theorem hdOperational_queries_ge_floor (H : Hash) (n d1 d2 Q : Nat)
    {s sf : HdMaskedState n d1 d2 Q} {tr : List (HdMaskedInput n × Option HdZeroTestEvent)}
    (hTr : ValidCustodyTrace (hdZeroTestStep H n d1 d2 Q) s tr sf) :
    ∀ x, x < s.used → (∀ f, s.pending = some f → f.query ≠ x) →
      x ∉ hdOperationalReleasedQueries (traceApprovedOutputs tr) := by
  induction hTr with
  | nil => intro _ _ _ hm; cases hm
  | @consAccepted st st' _ inp ev rest hs _ ih =>
    intro x hx hNoP
    unfold hdZeroTestStep at hs
    if hq : st.quarantined = true then simp [hq] at hs
    else
      simp only [hq, Bool.false_eq_true, ↓reduceIte] at hs
      cases hp : st.pending with
      | none =>
        cases inp with
        | openResiduals _ _ => simp [hp] at hs
        | freeze tag cand commits =>
          simp only [hp] at hs
          if hLt : st.used < Q then
            simp only [hLt, ↓reduceDIte, CustodyStepOutcome.accepted.injEq] at hs
            rcases hs with ⟨rfl, rfl⟩
            simp only [traceApprovedOutputs_cons_some, hdOperationalReleasedQueries]
            refine ih x (Nat.lt_succ_of_lt hx) ?_
            intro f hf; cases hf; exact Nat.ne_of_gt hx
          else
            simp [hLt] at hs
      | some f =>
        cases inp with
        | freeze _ _ _ => simp [hp] at hs
        | openResiduals res salts =>
          simp only [hp] at hs
          split at hs
          · rcases hs with ⟨rfl, rfl⟩
            have hNe : f.query ≠ x := hNoP f hp
            simp only [traceApprovedOutputs_cons_some, hdOperationalReleasedQueries, List.mem_cons]
            rintro (hEq | hTail)
            · exact hNe hEq.symm
            · exact ih x hx (fun _ hf => by cases hf) hTail
          · cases hs
  | @consRejected st st' _ inp err rest hs _ ih =>
    intro x hx hNoP
    simp only [traceApprovedOutputs_cons_none]
    unfold hdZeroTestStep at hs
    if hq : st.quarantined = true then
      simp [hq] at hs; rcases hs with ⟨rfl, _⟩; exact ih x hx hNoP
    else
      simp only [hq, Bool.false_eq_true, ↓reduceIte] at hs
      cases hp : st.pending with
      | none =>
        cases inp with
        | openResiduals _ _ => simp [hp] at hs; rcases hs with ⟨rfl, _⟩; exact ih x hx hNoP
        | freeze _ _ _ =>
          simp only [hp] at hs
          if hLt : st.used < Q then simp [hLt] at hs
          else simp [hLt] at hs; rcases hs with ⟨rfl, _⟩; exact ih x hx hNoP
      | some f =>
        cases inp with
        | freeze _ _ _ => simp [hp] at hs; rcases hs with ⟨rfl, _⟩; exact ih x hx hNoP
        | openResiduals _ _ =>
          simp only [hp] at hs
          split at hs
          · cases hs
          · rcases hs with ⟨rfl, _⟩; exact ih x hx (fun _ hf => by cases hf)

/-- **Multi-Turn Operational HD Query-Budget & SPDZ Zero-Test Soundness (`hd_operational_multiturn_sound`)**:
    Across ANY multi-turn trace of `hdZeroTestStep` starting from an enrolled state (`HdOperationalInv s₀`):
    1. **Hard Query-Budget Cap**: `sf.used ≤ Q`.
    2. **Unique One-Time Mask Consumption**: `(hdOperationalReleasedQueries (traceApprovedOutputs tr)).Nodup`.
    3. **Enrolled MAC Authenticity**: Every `.scalarReleased q hard val` in `traceApprovedOutputs tr`
       satisfies `hard = s₀.hardened` and `∃ hq : q < Q, val = s₀.observations ⟨q, hq⟩`! -/
theorem hd_operational_multiturn_sound (H : Hash) (n d1 d2 Q : Nat)
    {s₀ sf : HdMaskedState n d1 d2 Q}
    {tr : List (HdMaskedInput n × Option HdZeroTestEvent)}
    (hInv₀ : HdOperationalInv s₀)
    (hTr : ValidCustodyTrace (hdZeroTestStep H n d1 d2 Q) s₀ tr sf) :
    sf.used ≤ Q ∧
    (hdOperationalReleasedQueries (traceApprovedOutputs tr)).Nodup ∧
    (∀ q hard val, .scalarReleased q hard val ∈ traceApprovedOutputs tr →
      hard = s₀.hardened ∧ ∃ hq : q < Q, val = s₀.observations ⟨q, hq⟩) := by
  induction hTr with
  | nil => exact ⟨hInv₀.1, .nil, fun _ _ _ hm => by cases hm⟩
  | @consAccepted st st' _ inp ev rest hs hr ih =>
    unfold hdZeroTestStep at hs
    if hq : st.quarantined = true then simp [hq] at hs
    else
      simp only [hq, Bool.false_eq_true, ↓reduceIte] at hs
      cases hp : st.pending with
      | none =>
        cases inp with
        | openResiduals _ _ => simp [hp] at hs
        | freeze tag cand commits =>
          simp only [hp] at hs
          if hLt : st.used < Q then
            simp only [hLt, ↓reduceDIte, CustodyStepOutcome.accepted.injEq] at hs
            rcases hs with ⟨rfl, rfl⟩
            obtain ⟨hUsedF, hNdRest, hPropsRest⟩ := ih
              ⟨Nat.succ_le_of_lt hLt, ⟨hLt, Nat.lt_succ_self _, rfl⟩⟩
            simp only [traceApprovedOutputs_cons_some, hdOperationalReleasedQueries]
            refine ⟨hUsedF, hNdRest, ?_⟩
            intro q hard val hm
            rcases List.mem_cons.mp hm with hEq | hTail
            · cases hEq
            · exact hPropsRest q hard val hTail
          else
            simp [hLt] at hs
      | some f =>
        cases inp with
        | freeze _ _ _ => simp [hp] at hs
        | openResiduals res salts =>
          simp only [hp] at hs
          split at hs
          · rename_i hChk
            rcases hs with ⟨rfl, rfl⟩
            have hPendInv := hInv₀.2
            rw [hp] at hPendInv
            obtain ⟨hfLtQ, hfLtUsed, hfTrue⟩ := hPendInv
            have hCandEq := hd_masked_release_sound n d1 d2 Q st f res hChk.2.1 hChk.2.2
            obtain ⟨hUsedF, hNdRest, hPropsRest⟩ := ih ⟨hInv₀.1, trivial⟩
            have hNotInRest : f.query ∉ hdOperationalReleasedQueries (traceApprovedOutputs rest) :=
              hdOperational_queries_ge_floor H n d1 d2 Q hr f.query hfLtUsed
                (fun _ hf => by cases hf)
            simp only [traceApprovedOutputs_cons_some, hdOperationalReleasedQueries]
            refine ⟨hUsedF, .cons (fun y hy hEq => hNotInRest (hEq ▸ hy)) hNdRest, ?_⟩
            intro q hard val hm
            rcases List.mem_cons.mp hm with hEq | hTail
            · cases hEq
              exact ⟨rfl, hfLtQ, hCandEq.trans hfTrue⟩
            · exact hPropsRest q hard val hTail
          · cases hs
  | @consRejected st st' _ inp err rest hs _ ih =>
    simp only [traceApprovedOutputs_cons_none]
    unfold hdZeroTestStep at hs
    if hq : st.quarantined = true then
      simp [hq] at hs; rcases hs with ⟨rfl, _⟩; exact ih hInv₀
    else
      simp only [hq, Bool.false_eq_true, ↓reduceIte] at hs
      cases hp : st.pending with
      | none =>
        cases inp with
        | openResiduals _ _ => simp [hp] at hs; rcases hs with ⟨rfl, _⟩; exact ih hInv₀
        | freeze _ _ _ =>
          simp only [hp] at hs
          if hLt : st.used < Q then simp [hLt] at hs
          else simp [hLt] at hs; rcases hs with ⟨rfl, _⟩; exact ih hInv₀
      | some f =>
        cases inp with
        | freeze _ _ _ => simp [hp] at hs; rcases hs with ⟨rfl, _⟩; exact ih hInv₀
        | openResiduals _ _ =>
          simp only [hp] at hs
          split at hs
          · cases hs
          · rcases hs with ⟨rfl, _⟩
            exact ih ⟨hInv₀.1, trivial⟩

/-- Exact posterior fibers of the ACTUAL masked observation over the public MLWE witness fiber. -/
def hd_actual_observation_fiber (d1 d2 Q : Nat)
    (A : Fin d2 → Fin d1 → HdFq204) (t : Fin d2 → HdFq204)
    (forms : Fin Q → Fin d1 → HdFq204) (obs : Fin Q → HdFq204) :
    SimpleEquiv (ShortMlweWitness hdCbdEta d1 d2 A t)
      { state : ShortMlweWitness hdCbdEta d1 d2 A t × (Fin Q → HdFq204) //
        ∀ q, hdMaskedObservation d1 Q forms state.1.val.1 state.2 q = obs q } :=
  hdAuthorizedMlweFiberEquiv hdCbdEta d1 d2 Q A t forms obs

theorem hd_masked_observation_secret_independence (d1 Q : Nat)
    (forms : Fin Q → Fin d1 → HdFq204) (s₁ s₂ : Fin d1 → HdFq204)
    (m₁ : Fin Q → HdFq204) :
    ∃ m₂ : Fin Q → HdFq204,
      hdMaskedObservation d1 Q forms s₁ m₁ = hdMaskedObservation d1 Q forms s₂ m₂ := by
  refine ⟨fun q => HdFq204.sub (hdMaskedObservation d1 Q forms s₁ m₁ q)
    (evalLinearForm d1 (forms q) s₂), ?_⟩
  funext q
  exact (LawfulCommRing.add_sub_cancel_left (R := HdFq204)
    (evalLinearForm d1 (forms q) s₂) (hdMaskedObservation d1 Q forms s₁ m₁ q)).symm

/-- Full-trace coupling across arbitrary multi-turn inputs, failed checks, and selective aborts. -/
theorem hd_actual_wire_trace_secret_independence (H : Hash) (n d1 d2 Q : Nat)
    (A : Fin d2 → Fin d1 → HdFq204) (t : Fin d2 → HdFq204)
    (s₁ s₂ : ShortMlweWitness hdCbdEta d1 d2 A t)
    (forms : Fin Q → Fin d1 → HdFq204) (m₁ : Fin Q → HdFq204)
    (alpha : HdFq204) (ha : alpha ≠ HdFq204.zero) (hard : Bool) :
    ∃ m₂ : Fin Q → HdFq204, ∀ inputs : List (HdMaskedInput n),
      custodyWireTrace (hdZeroTestStep H n d1 d2 Q)
        (hdMaskedEnroll n d1 d2 Q A t s₁ forms m₁ alpha ha hard) inputs =
      custodyWireTrace (hdZeroTestStep H n d1 d2 Q)
        (hdMaskedEnroll n d1 d2 Q A t s₂ forms m₂ alpha ha hard) inputs := by
  obtain ⟨m₂, hm⟩ := hd_masked_observation_secret_independence d1 Q forms s₁.val.1 s₂.val.1 m₁
  refine ⟨m₂, ?_⟩
  intro inputs
  have hs : hdMaskedEnroll n d1 d2 Q A t s₁ forms m₁ alpha ha hard =
      hdMaskedEnroll n d1 d2 Q A t s₂ forms m₂ alpha ha hard := by
    unfold hdMaskedEnroll
    rw [hm]
  rw [hs]

/-- Exact mask-fiber `SimpleEquiv` for ANY two valid short MLWE witnesses over ANY actual multi-turn
    wire trace `targetTrace`: under uniform independent masks, every short witness in the MLWE fiber
    has the exact same measure of mask tapes realizing `targetTrace`! -/
def hd_general_witness_wire_trace_mask_equiv (H : Hash) (n d1 d2 Q : Nat)
    (A : Fin d2 → Fin d1 → HdFq204) (t : Fin d2 → HdFq204)
    (s₁ s₂ : ShortMlweWitness hdCbdEta d1 d2 A t)
    (forms : Fin Q → Fin d1 → HdFq204)
    (alpha : HdFq204) (ha : alpha ≠ HdFq204.zero) (hard : Bool)
    (inputs : List (HdMaskedInput n)) (targetTrace : List (Option HdZeroTestEvent)) :
    SimpleEquiv
      { m₁ : Fin Q → HdFq204 //
          custodyWireTrace (hdZeroTestStep H n d1 d2 Q)
            (hdMaskedEnroll n d1 d2 Q A t s₁ forms m₁ alpha ha hard) inputs = targetTrace }
      { m₂ : Fin Q → HdFq204 //
          custodyWireTrace (hdZeroTestStep H n d1 d2 Q)
            (hdMaskedEnroll n d1 d2 Q A t s₂ forms m₂ alpha ha hard) inputs = targetTrace } where
  toFun := fun ⟨m₁, h₁⟩ =>
    let shift : Fin Q → HdFq204 := fun q =>
      HdFq204.sub (hdMaskedObservation d1 Q forms s₁.val.1 m₁ q) (evalLinearForm d1 (forms q) s₂.val.1)
    have hObs : hdMaskedObservation d1 Q forms s₂.val.1 shift =
        hdMaskedObservation d1 Q forms s₁.val.1 m₁ := by
      funext q
      exact LawfulCommRing.add_sub_cancel_left (R := HdFq204)
        (evalLinearForm d1 (forms q) s₂.val.1) (hdMaskedObservation d1 Q forms s₁.val.1 m₁ q)
    ⟨shift, by
      have he : hdMaskedEnroll n d1 d2 Q A t s₂ forms shift alpha ha hard =
          hdMaskedEnroll n d1 d2 Q A t s₁ forms m₁ alpha ha hard := by
        unfold hdMaskedEnroll; rw [hObs]
      rw [he, h₁]⟩
  invFun := fun ⟨m₂, h₂⟩ =>
    let shift : Fin Q → HdFq204 := fun q =>
      HdFq204.sub (hdMaskedObservation d1 Q forms s₂.val.1 m₂ q) (evalLinearForm d1 (forms q) s₁.val.1)
    have hObs : hdMaskedObservation d1 Q forms s₁.val.1 shift =
        hdMaskedObservation d1 Q forms s₂.val.1 m₂ := by
      funext q
      exact LawfulCommRing.add_sub_cancel_left (R := HdFq204)
        (evalLinearForm d1 (forms q) s₁.val.1) (hdMaskedObservation d1 Q forms s₂.val.1 m₂ q)
    ⟨shift, by
      have he : hdMaskedEnroll n d1 d2 Q A t s₁ forms shift alpha ha hard =
          hdMaskedEnroll n d1 d2 Q A t s₂ forms m₂ alpha ha hard := by
        unfold hdMaskedEnroll; rw [hObs]
      rw [he, h₂]⟩
  left_inv := fun ⟨m₁, _⟩ => by
    apply Subtype.ext
    funext q
    dsimp only [hdMaskedObservation]
    change CommRingOps.sub (CommRingOps.add _ (CommRingOps.sub (CommRingOps.add _ _) _)) _ = _
    rw [LawfulCommRing.add_sub_cancel_left (R := HdFq204)]
    exact hdFq204_add_sub_self_left _ _
  right_inv := fun ⟨m₂, _⟩ => by
    apply Subtype.ext
    funext q
    dsimp only [hdMaskedObservation]
    change CommRingOps.sub (CommRingOps.add _ (CommRingOps.sub (CommRingOps.add _ _) _)) _ = _
    rw [LawfulCommRing.add_sub_cancel_left (R := HdFq204)]
    exact hdFq204_add_sub_self_left _ _

/-- Short CBD digit mapping `x : Fin 5 ↦ x - 2 ∈ {-2, -1, 0, 1, 2}` in `HdFq204`. -/
def hdFiveDigit (x : Fin 5) : HdFq204 :=
  HdFq204.ofInt (Int.ofNat x.val - 2)

theorem hdFiveDigit_short (x : Fin 5) : (hdFiveDigit x).centeredAbs ≤ hdCbdEta := by
  have hx := x.isLt
  have hc : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 := by omega
  rcases hc with h | h | h | h | h <;> (unfold hdFiveDigit; rw [h]; decide)

theorem hdFiveDigit_injective (x y : Fin 5) (h : hdFiveDigit x = hdFiveDigit y) : x = y := by
  have hv := congrArg HdFq204.val h
  have hx := x.isLt
  have hy := y.isLt
  have cx : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 := by omega
  have cy : y.val = 0 ∨ y.val = 1 ∨ y.val = 2 ∨ y.val = 3 ∨ y.val = 4 := by omega
  apply Fin.ext
  rcases cx with hx | hx | hx | hx | hx <;>
    rcases cy with hy | hy | hy | hy | hy <;>
    (unfold hdFiveDigit at hv; rw [hx, hy] at hv; simp [HdFq204.ofInt, hdModuleQ] at hv ⊢; try omega)

private theorem evalLinearForm_zero_matrix :
    ∀ (d : Nat) (s : Fin d → HdFq204), evalLinearForm d (fun _ => HdFq204.zero) s = HdFq204.zero
  | 0, _ => rfl
  | d + 1, s => by
    simp only [evalLinearForm, HdFq204.zero_mul, HdFq204.zero_add]
    exact evalLinearForm_zero_matrix d _

/-- General `d1`-dimensional short-secret witness family (`5 ^ d1` distinct valid short secrets!). -/
def hdShortVecWitness (d1 d2 : Nat) (coords : Fin d1 → Fin 5) :
    ShortMlweWitness hdCbdEta d1 d2 (fun _ _ => HdFq204.zero) (fun _ => HdFq204.zero) :=
  ⟨(fun i => hdFiveDigit (coords i), fun _ => HdFq204.zero), by
    refine ⟨fun i => hdFiveDigit_short (coords i), fun _ => by change HdFq204.zero.centeredAbs ≤ hdCbdEta; decide, ?_⟩
    funext r
    simp only [mlwePublicRelation, evalLinearForm_zero_matrix, HdFq204.add_zero]⟩

theorem hdShortVecWitness_injective (d1 d2 : Nat) (x y : Fin d1 → Fin 5)
    (h : hdShortVecWitness d1 d2 x = hdShortVecWitness d1 d2 y) : x = y := by
  funext i
  have hi := congrFun (congrArg (fun w => w.val.1) h) i
  exact hdFiveDigit_injective (x i) (y i) hi

/-- Explicit 1D 5-witness specialization retained for clarity. -/
def hdFiveShortWitness (x : Fin 5) :
    ShortMlweWitness hdCbdEta 1 1 (fun _ _ => HdFq204.zero) (fun _ => HdFq204.zero) :=
  hdShortVecWitness 1 1 (fun _ => x)

theorem hdFiveShortWitness_injective (x y : Fin 5)
    (h : hdFiveShortWitness x = hdFiveShortWitness y) : x = y := by
  have hf := hdShortVecWitness_injective 1 1 (fun _ => x) (fun _ => y) h
  exact congrFun hf ⟨0, by decide⟩

theorem tooth_hd_actual_fiber_has_five_short_preimages (Q : Nat)
    (forms : Fin Q → Fin 1 → HdFq204) (obs : Fin Q → HdFq204) :
    ∃ preimages : Fin 5 →
      { state : ShortMlweWitness hdCbdEta 1 1
          (fun _ _ => HdFq204.zero) (fun _ => HdFq204.zero) × (Fin Q → HdFq204) //
        ∀ q, hdMaskedObservation 1 Q forms state.1.val.1 state.2 q = obs q },
      ∀ x y, preimages x = preimages y → x = y := by
  let e := hd_actual_observation_fiber 1 1 Q
    (fun _ _ => HdFq204.zero) (fun _ => HdFq204.zero) forms obs
  refine ⟨fun x => e.toFun (hdFiveShortWitness x), ?_⟩
  intro x y h
  apply hdFiveShortWitness_injective x y
  have hi := congrArg e.invFun h
  simpa only [e.left_inv] using hi

/-- Exact multi-dimensional `5 ^ d1`-element posterior fiber on the actual operational observation. -/
def hdMultiDimPosteriorEquiv (d1 d2 Q : Nat) (forms : Fin Q → Fin d1 → HdFq204)
    (obs : Fin Q → HdFq204) :
    SimpleEquiv (Fin d1 → Fin 5)
      { state : (Fin d1 → Fin 5) × (Fin Q → HdFq204) //
        ∀ q, hdMaskedObservation d1 Q forms (hdShortVecWitness d1 d2 state.1).val.1 state.2 q = obs q } where
  toFun := fun x =>
    ⟨(x, fun q => HdFq204.sub (obs q)
      (evalLinearForm d1 (forms q) (hdShortVecWitness d1 d2 x).val.1)),
     fun q => LawfulCommRing.add_sub_cancel_left (R := HdFq204)
      (evalLinearForm d1 (forms q) (hdShortVecWitness d1 d2 x).val.1) (obs q)⟩
  invFun := fun s => s.val.1
  left_inv := fun _ => rfl
  right_inv := fun ⟨⟨x, masks⟩, h⟩ => by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext q
      have hq := h q
      dsimp only [hdMaskedObservation] at hq ⊢
      rw [← hq]
      exact hdFq204_add_sub_self_left _ _

def hdFivePosteriorEquiv (Q : Nat) (forms : Fin Q → Fin 1 → HdFq204)
    (obs : Fin Q → HdFq204) :
    SimpleEquiv (Fin 5)
      { state : Fin 5 × (Fin Q → HdFq204) //
        ∀ q, hdMaskedObservation 1 Q forms (hdFiveShortWitness state.1).val.1 state.2 q = obs q } where
  toFun := fun x =>
    ⟨(x, fun q => HdFq204.sub (obs q)
      (evalLinearForm 1 (forms q) (hdFiveShortWitness x).val.1)),
     fun q => LawfulCommRing.add_sub_cancel_left (R := HdFq204)
      (evalLinearForm 1 (forms q) (hdFiveShortWitness x).val.1) (obs q)⟩
  invFun := fun s => s.val.1
  left_inv := fun _ => rfl
  right_inv := fun ⟨⟨x, masks⟩, h⟩ => by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext q
      have hq := h q
      dsimp only [hdMaskedObservation] at hq ⊢
      rw [← hq]
      exact hdFq204_add_sub_self_left _ _

/-- Conditional min-entropy ≥ 2 bits for 1D (`1/5 ≤ 1/2^2`) and ≥ 18 bits for 8D (`1/5^8 ≤ 1/2^18`,
    since `5^8 = 390,625 ≥ 262,144 = 2^18`) over the exact posterior fibers! -/
theorem hd_five_posterior_min_entropy_two_bits (guess : Fin 5) :
    (([⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩] : List (Fin 5)).filter
      (fun x => decide (x = guess))).length = 1 ∧
    ratLe (1, 5) (1, 2 ^ 2) ∧
    ratLe (1, 5 ^ 8) (1, 2 ^ 18) := by
  refine ⟨?_, ?_, ?_⟩
  · have hg := guess.isLt
    have hc : guess.val = 0 ∨ guess.val = 1 ∨ guess.val = 2 ∨ guess.val = 3 ∨ guess.val = 4 := by omega
    rcases hc with h | h | h | h | h
    · have he : guess = ⟨0, by decide⟩ := Fin.ext h; subst he; decide
    · have he : guess = ⟨1, by decide⟩ := Fin.ext h; subst he; decide
    · have he : guess = ⟨2, by decide⟩ := Fin.ext h; subst he; decide
    · have he : guess = ⟨3, by decide⟩ := Fin.ext h; subst he; decide
    · have he : guess = ⟨4, by decide⟩ := Fin.ext h; subst he; decide
  · unfold ratLe; refine ⟨by decide, by decide, by decide⟩
  · unfold ratLe; refine ⟨by decide, by decide, by decide⟩

/-! #### Shard 3 #7 Separation `#tooth`: Unmasked Radix-5 Linear Query Collapses `5^8` Short Secrets in 1 Query -/

/-- Unauthorized radix-5 packing form $w_i = 5^i \bmod q$ ($q = 8380417$). -/
def hdRadix5Form (d : Nat) : Fin d → HdFq204 :=
  fun i => HdFq204.ofNat (5 ^ i.val)

/-- Exact base-5 integer decoding of `d` digits in `{0, 1, 2, 3, 4}`. -/
def hdRadix5Nat : (d : Nat) → (Fin d → Fin 5) → Nat
  | 0, _ => 0
  | d + 1, x => (x ⟨0, Nat.zero_lt_succ d⟩).val +
      5 * hdRadix5Nat d (fun i => x ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private theorem hdRadix5Nat_lt_pow : ∀ (d : Nat) (x : Fin d → Fin 5), hdRadix5Nat d x < 5 ^ d
  | 0, _ => by change 0 < 1; decide
  | d + 1, x => by
    unfold hdRadix5Nat
    have h0 := (x ⟨0, Nat.zero_lt_succ d⟩).isLt
    have hTail := hdRadix5Nat_lt_pow d (fun i => x ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    have hPow : 5 ^ (d + 1) = 5 * 5 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
    omega

private theorem hdRadix5Nat_injective :
    ∀ (d : Nat) (x y : Fin d → Fin 5), hdRadix5Nat d x = hdRadix5Nat d y → x = y
  | 0, x, y, _ => funext (fun i => Fin.elim0 i)
  | d + 1, x, y, h => by
    unfold hdRadix5Nat at h
    have hx0 := (x ⟨0, Nat.zero_lt_succ d⟩).isLt
    have hy0 := (y ⟨0, Nat.zero_lt_succ d⟩).isLt
    have hEq0 : (x ⟨0, Nat.zero_lt_succ d⟩).val = (y ⟨0, Nat.zero_lt_succ d⟩).val := by omega
    have hEqTailNat :
        hdRadix5Nat d (fun i => x ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) =
        hdRadix5Nat d (fun i => y ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) := by omega
    have hEqTail := hdRadix5Nat_injective d _ _ hEqTailNat
    funext i
    cases i using Fin.cases with
    | zero => exact Fin.ext hEq0
    | succ j => exact congrFun hEqTail j

private theorem hdFiveDigit_add_two (x : Fin 5) :
    HdFq204.add (hdFiveDigit x) (HdFq204.ofNat 2) = HdFq204.ofNat x.val := by
  have hx := x.isLt
  have hc : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 := by omega
  rcases hc with h | h | h | h | h <;> (unfold hdFiveDigit; rw [h]; decide)

private theorem evalLinearForm_add_vec :
    ∀ (d : Nat) (w a b : Fin d → HdFq204),
      HdFq204.add (evalLinearForm d w a) (evalLinearForm d w b) =
        evalLinearForm d w (fun i => HdFq204.add (a i) (b i))
  | 0, _, _, _ => HdFq204.add_zero HdFq204.zero
  | d + 1, w, a, b => by
    simp only [evalLinearForm]
    let u1 := HdFq204.mul (w ⟨0, Nat.zero_lt_succ d⟩) (a ⟨0, Nat.zero_lt_succ d⟩)
    let v1 := evalLinearForm d (fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
                               (fun i => a ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    let u2 := HdFq204.mul (w ⟨0, Nat.zero_lt_succ d⟩) (b ⟨0, Nat.zero_lt_succ d⟩)
    let v2 := evalLinearForm d (fun i => w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
                               (fun i => b ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    have hSwap : HdFq204.add (HdFq204.add u1 v1) (HdFq204.add u2 v2) =
        HdFq204.add (HdFq204.add u1 u2) (HdFq204.add v1 v2) := by
      rw [HdFq204.add_assoc, ← HdFq204.add_assoc v1 u2 v2, HdFq204.add_comm v1 u2,
          HdFq204.add_assoc u2 v1 v2, ← HdFq204.add_assoc]
    change HdFq204.add (HdFq204.add u1 v1) (HdFq204.add u2 v2) = _
    rw [hSwap, ← HdFq204.left_distrib, evalLinearForm_add_vec d]

private theorem evalLinearForm_scale_left :
    ∀ (d : Nat) (c : HdFq204) (w s : Fin d → HdFq204),
      evalLinearForm d (fun i => HdFq204.mul c (w i)) s = HdFq204.mul c (evalLinearForm d w s)
  | 0, c, _, _ => (HdFq204.mul_zero c).symm
  | d + 1, c, w, s => by
    simp only [evalLinearForm]
    rw [HdFq204.mul_assoc, evalLinearForm_scale_left d c, ← HdFq204.left_distrib]

private theorem hdFq204_ofNat_add (a b : Nat) :
    HdFq204.add (HdFq204.ofNat a) (HdFq204.ofNat b) = HdFq204.ofNat (a + b) :=
  HdFq204.ext <| by rw [HdFq204.add_val, HdFq204.ofNat_val, HdFq204.ofNat_val, HdFq204.ofNat_val, Nat.mod_add_mod, Nat.add_mod_mod]

private theorem hdFq204_ofNat_mul (a b : Nat) :
    HdFq204.mul (HdFq204.ofNat a) (HdFq204.ofNat b) = HdFq204.ofNat (a * b) :=
  HdFq204.ext <| by rw [HdFq204.mul_val, HdFq204.ofNat_val, HdFq204.ofNat_val, HdFq204.ofNat_val, Nat.mod_mul_mod, Nat.mul_mod_mod]

private theorem evalLinearForm_radix5_ofNat :
    ∀ (d : Nat) (x : Fin d → Fin 5),
      evalLinearForm d (hdRadix5Form d) (fun i => HdFq204.ofNat (x i).val) =
        HdFq204.ofNat (hdRadix5Nat d x)
  | 0, _ => rfl
  | d + 1, x => by
    simp only [evalLinearForm, hdRadix5Nat]
    have hw0 : hdRadix5Form (d + 1) ⟨0, Nat.zero_lt_succ d⟩ = HdFq204.one := rfl
    have hwShift :
        (fun i : Fin d => hdRadix5Form (d + 1) ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) =
        (fun i : Fin d => HdFq204.mul (HdFq204.ofNat 5) (hdRadix5Form d i)) := by
      funext i
      unfold hdRadix5Form
      dsimp only
      rw [hdFq204_ofNat_mul, Nat.pow_succ, Nat.mul_comm]
    rw [hw0, HdFq204.one_mul, hwShift, evalLinearForm_scale_left, evalLinearForm_radix5_ofNat d,
        hdFq204_ofNat_mul, hdFq204_ofNat_add]

/-- **`#tooth` Unmasked Radix-5 Linear Query Leaks All 8 Short Coordinates in 1 Query
    (`tooth_hd_unmasked_radix5_single_query_injective`)**:
    Because $5^8 = 390,625 < 8,380,417 = q$, a SINGLE unmasked linear evaluation
    $y = \sum_{i=0}^{7} 5^i s_i \bmod q$ is **strictly injective** across ALL $5^8 = 390,625$
    short 8-coordinate secrets $s \in [-2, 2]^8$ (`1 < 8` query collapses min-entropy to **0 bits**!),
    whereas `hdZeroTestStep`'s dealerless mask `masks q` (`hdMultiDimPosteriorEquiv 8`) preserves
    all $5^8 = 390,625$ short preimages (`≥ 18` bits conditional min-entropy) across arbitrary `Q` queries! -/
theorem tooth_hd_unmasked_radix5_single_query_injective
    (x y : Fin 8 → Fin 5)
    (hUnmaskedEq :
      evalLinearForm 8 (hdRadix5Form 8) (hdShortVecWitness 8 1 x).val.1 =
      evalLinearForm 8 (hdRadix5Form 8) (hdShortVecWitness 8 1 y).val.1) :
    x = y := by
  let shiftVec : Fin 8 → HdFq204 := fun _ => HdFq204.ofNat 2
  let offset : HdFq204 := evalLinearForm 8 (hdRadix5Form 8) shiftVec
  have hAdd := congrArg (fun z => HdFq204.add z offset) hUnmaskedEq
  dsimp only [offset, shiftVec, hdShortVecWitness] at hAdd
  rw [evalLinearForm_add_vec, evalLinearForm_add_vec] at hAdd
  have hL : (fun i : Fin 8 => HdFq204.add (hdFiveDigit (x i)) (HdFq204.ofNat 2)) =
      (fun i : Fin 8 => HdFq204.ofNat (x i).val) := funext (fun i => hdFiveDigit_add_two (x i))
  have hR : (fun i : Fin 8 => HdFq204.add (hdFiveDigit (y i)) (HdFq204.ofNat 2)) =
      (fun i : Fin 8 => HdFq204.ofNat (y i).val) := funext (fun i => hdFiveDigit_add_two (y i))
  rw [hL, hR, evalLinearForm_radix5_ofNat, evalLinearForm_radix5_ofNat] at hAdd
  have hVal := congrArg HdFq204.val hAdd
  simp only [HdFq204.ofNat_val] at hVal
  have hxLt : hdRadix5Nat 8 x < hdModuleQ :=
    Nat.lt_trans (hdRadix5Nat_lt_pow 8 x) (by decide : 5 ^ 8 < hdModuleQ)
  have hyLt : hdRadix5Nat 8 y < hdModuleQ :=
    Nat.lt_trans (hdRadix5Nat_lt_pow 8 y) (by decide : 5 ^ 8 < hdModuleQ)
  rw [Nat.mod_eq_of_lt hxLt, Nat.mod_eq_of_lt hyLt] at hVal
  exact hdRadix5Nat_injective 8 x y hVal

/-! ### §E. Strengthened Compatibility Theorems & Operational `PartyMachine` Exports -/

/-- Compatibility theorem pairing legacy scalar-SPN algebraic evidence with operational 8-phase
    `ftsSpnStep` / `ftsSpnEpochStep` multi-epoch non-replay and final-MAC barrier guarantees. -/
theorem fts_spn_deferred_mac_blocks_dfa_across_epochs
    (H : Hash) {st₀ stFinal : FtsEpochGuardState}
    {trace : List (FtsSpnInput × Option FtsSpnPrivateEvidence)}
    (hInv₀ : FtsStateInv st₀)
    (hTrace : ValidCustodyTrace (ftsSpnEvidenceStep H) st₀ trace stFinal) :
    ((ftsReleasedEpochs (traceApprovedOutputs trace)).Nodup ∧
    (∀ ep out48 ks xIn dX dG alpha,
      FtsSpnPrivateEvidence.releasedRound48Signature ep out48 ks xIn dX dG alpha ∈ traceApprovedOutputs trace →
        (dX = towerZero 7 ∧ out48 = evalScalarSpn48Evidence ks.keyAt xIn) ∨
        MacKeyRecoveryWitness 7 alpha dX dG) ∧
    (st₀.macContextPoisoned = true →
      stFinal.macContextPoisoned = true ∧ traceApprovedOutputs trace = [])) ∧
    (∀ (s s' : FtsWireState) (i : FtsWireInput) (ep : Nat) (sig : List UInt8),
      ftsSpnStep H s i = .accepted s' (.releasedRound48Signature ep sig) →
      s.phase = .macOpen ∧ s.finalResidual = ftsZeroResidual ∧
      ep = s.epoch ∧ sig = ftsEncodeLanes s.candidate) := by
  exact ⟨fts_spn_deferred_mac_blocks_dfa_across_epochs_evidence H hInv₀ hTrace,
         fts_wire_release_requires_final_mac H⟩

/-- Compatibility theorem pairing legacy sliding-window bitmap evidence with operational
    authenticated-rotation replay persistence (`policyWatermarkGuardStep`). -/
theorem policy_watermark_sliding_window_multiturn_sound
    {g₀ gFinal : PolicyWatermarkGuard}
    {trace : List (PolicyWatermarkInput × Option PolicyWatermarkEvent)}
    (hTrace : ValidCustodyTrace policyBitmapEvidenceStep g₀ trace gFinal) :
    (let approved := watermarkApprovedIntents (traceApprovedOutputs trace)
    g₀.minNonceWatermark ≤ gFinal.minNonceWatermark ∧
    (approved.map (fun p => p.1.nonce)).Nodup ∧
    (∀ p ∈ approved,
      g₀.minNonceWatermark ≤ p.1.nonce ∧
      ¬ nonceConsumedByWatermark g₀ p.1.nonce ∧
      p.2 = toCanonicalSigningBytes p.1 ∧
      (g₀.requireAuthenticatedInitiator = true → p.1.init_mac_bytes ≠ []))) ∧
    (∀ (g g' : AuthenticatedPolicyState) (a : PolicyWindowAuthorization) (ev : PolicyWatermarkEvent),
      policyWatermarkGuardStep g (.advance a) = .accepted g' ev →
      g.rules.window_id < g'.rules.window_id ∧ a.mac = policyWindowTag g a.newWindow ∧
      g'.nonceBurns = g.nonceBurns ∧ g'.sessionBurns = g.sessionBurns) := by
  exact ⟨policy_watermark_sliding_window_multiturn_sound_evidence hTrace,
         policy_authorized_rotation_preserves_replay⟩

/-- Compatibility theorem pairing legacy Co-ZK evidence with operational commit-before-challenge
    `cozkPreOpenCeremonyStep` binding directly to the challenged 2-of-3 ZKBoo head views. -/
theorem cozk_pre_open_mul_sacrifice_blocks_corrupted_head_release (H : Hash) :
    ((∀ (tag : List UInt8) (stFinal : CoZkCeremonyState)
       (trace : List (CoZkCeremonyInput × Option CoZkCeremonyEvent)),
      let st₀ : CoZkCeremonyState := { sessionTag := tag, phase := .awaitingRootFreeze, aborted := false }
      ValidCustodyTrace (cozkOrderingEvidenceStep H) st₀ trace stFinal →
      cozkCountHeadReleases (traceApprovedOutputs trace) ≤ 1 ∧
      (∀ rOut dig,
        .challengedHeadsReleased rOut dig ∈ traceApprovedOutputs trace →
        ∃ nGates, .preOpenSacrificePassed rOut nGates ∈ traceApprovedOutputs trace)) ∧
    (∀ (st st' : CoZkCeremonyState) (rssMsg : RssActiveOpenMsg)
       (gateDeltas : List Tower128) (ev : CoZkCeremonyEvent)
       (trueCheckShares : RssWord64) (corruptIdx : Nat),
      (corruptIdx ≠ 0 → rssMsg.p0_x0 = trueCheckShares.x0 ∧ rssMsg.p0_x1 = trueCheckShares.x1) →
      (corruptIdx ≠ 1 → rssMsg.p1_x1 = trueCheckShares.x1 ∧ rssMsg.p1_x2 = trueCheckShares.x2) →
      (corruptIdx ≠ 2 → rssMsg.p2_x2 = trueCheckShares.x2 ∧ rssMsg.p2_x0 = trueCheckShares.x0) →
      cozkOrderingEvidenceStep H st (.verifyPreOpenSacrifice rssMsg gateDeltas) = .accepted st' ev →
      reconstructRssWord trueCheckShares = 0 ∧
      ∃ root coin1 coin2,
        st.phase = .rootFrozen root coin1 coin2 ∧
        batchDeviationPoly gateDeltas coin1 = towerZero 7 ∧
        batchDeviationPoly gateDeltas coin2 = towerZero 7) ∧
    (∀ (L : Nat) (gateDeltas S : List Tower128),
      L ≤ 2 ^ 63 →
      S.Nodup →
      gateDeltas.length ≤ L →
      L + 1 ≤ S.length →
      (∃ d ∈ gateDeltas, d ≠ towerZero 7) →
      (S.filter (fun r => decide (batchDeviationPoly gateDeltas r = towerZero 7))).length ≤ L ∧
      ratLe (L * L, 2 ^ 128 * 2 ^ 128) (1, 2 ^ 130))) ∧
    (∀ (s s' : CoZkCommittedState) (root digest : List UInt8) (eChal : Fin 3) (v0 v1 hcHidden : List UInt8),
      cozkPreOpenCeremonyStep H s .release = .accepted s' (.released root digest eChal v0 v1 hcHidden) →
      ∃ f, s.phase = .verified f eChal ∧
        root = f.root ∧ digest = f.headsDigest ∧
        v0 = f.headViews eChal ∧ v1 = f.headViews (cozkNextParty eChal) ∧
        hcHidden = f.headCommits (cozkHiddenParty eChal)) := by
  exact ⟨cozk_pre_open_mul_sacrifice_blocks_corrupted_head_release_evidence H,
         cozk_release_bound_to_checked_wires H⟩

/-- Compatibility theorem pairing legacy HD evidence with operational `hdZeroTestStep` full-trace
    secret independence across the actual masked wire observation model. -/
theorem hd_authorized_budget_blocks_full_rank_reconstruction
    (H : Hash) (n dim : Nat) :
    ((∀ {st₀ stFinal : HdFamilyState n dim}
       {trace : List (HdZeroTestInput n dim × Option HdZeroTestPrivateEvidence)},
      st₀.usedQueries ≤ st₀.budgetCap →
      ValidCustodyTrace (hdZeroTestEvidenceStep H n dim) st₀ trace stFinal →
      stFinal.usedQueries ≤ st₀.budgetCap ∧
      (hdFrozenMaskIds (traceApprovedOutputs trace)).Nodup) ∧
    (∀ (d1 d2 Q : Nat) (A : Fin d2 → Fin d1 → HdFq204) (tPub : Fin d2 → HdFq204)
       (wForms : Fin Q → Fin d1 → HdFq204) (tr : Fin Q → HdFq204)
       (wA wB : ShortMlweWitness hdCbdEta d1 d2 A tPub),
      wA ≠ wB →
      ∃ masksA masksB : Fin Q → HdFq204,
        isShortHdVec hdCbdEta d1 wA.val.1 ∧ isShortHdVec hdCbdEta d2 wA.val.2 ∧
        isShortHdVec hdCbdEta d1 wB.val.1 ∧ isShortHdVec hdCbdEta d2 wB.val.2 ∧
        mlwePublicRelation d1 d2 A wA.val.1 wA.val.2 = tPub ∧
        mlwePublicRelation d1 d2 A wB.val.1 wB.val.2 = tPub ∧
        (∀ q : Fin Q,
          HdFq204.add (evalLinearForm d1 (wForms q) wA.val.1) (masksA q) = tr q ∧
          HdFq204.add (evalLinearForm d1 (wForms q) wB.val.1) (masksB q) = tr q)) ∧
    (∀ (dimC budgetCap : Nat) (hCapLt : budgetCap < dimC)
       (opened : Fin budgetCap → HdFq204) (_hShortOpen : isShortHdVec hdCbdEta budgetCap opened),
      ∃ sA sB : Fin dimC → HdFq204,
        sA ≠ sB ∧
        isShortHdVec hdCbdEta dimC sA ∧
        isShortHdVec hdCbdEta dimC sB ∧
        (∀ i : Fin budgetCap, sA ⟨i.val, Nat.lt_trans i.isLt hCapLt⟩ = opened i) ∧
        (∀ i : Fin budgetCap, sB ⟨i.val, Nat.lt_trans i.isLt hCapLt⟩ = opened i))) ∧
    (∀ (d1 d2 Q : Nat) (A : Fin d2 → Fin d1 → HdFq204) (t : Fin d2 → HdFq204)
      (s₁ s₂ : ShortMlweWitness hdCbdEta d1 d2 A t)
      (forms : Fin Q → Fin d1 → HdFq204) (m₁ : Fin Q → HdFq204)
      (alpha : HdFq204) (ha : alpha ≠ HdFq204.zero) (hard : Bool),
      ∃ m₂ : Fin Q → HdFq204, ∀ inputs : List (HdMaskedInput n),
        custodyWireTrace (hdZeroTestStep H n d1 d2 Q)
          (hdMaskedEnroll n d1 d2 Q A t s₁ forms m₁ alpha ha hard) inputs =
        custodyWireTrace (hdZeroTestStep H n d1 d2 Q)
          (hdMaskedEnroll n d1 d2 Q A t s₂ forms m₂ alpha ha hard) inputs) := by
  exact ⟨hd_authorized_budget_blocks_full_rank_reconstruction_evidence H n dim,
         hd_actual_wire_trace_secret_independence H n⟩

/-! ### Compositional Exports: Operational Party Machines Only -/

def ftsSpnPartyMachine (H : Hash) :
    PartyMachine FtsOperationalGuard FtsOperationalInput FtsSpnEvent :=
  PartyMachine.ofCustodyStep (ftsSpnEpochStep H)

def hdZeroTestPartyMachine (H : Hash) (n d1 d2 Q : Nat) :
    PartyMachine (HdMaskedState n d1 d2 Q) (HdMaskedInput n) HdZeroTestEvent :=
  PartyMachine.ofCustodyStep (hdZeroTestStep H n d1 d2 Q)

def policyGuardPartyMachine :
    PartyMachine AuthenticatedPolicyState AuthenticatedPolicyInput PolicyWatermarkEvent :=
  PartyMachine.ofCustodyStep policyWatermarkGuardStep

def policyWatermarkGuardPartyMachine :
    PartyMachine AuthenticatedPolicyState AuthenticatedPolicyInput PolicyWatermarkEvent :=
  PartyMachine.ofCustodyStep policyWatermarkGuardStep

def policyQuorumClusterPartyMachine :
    PartyMachine PolicyQuorumCluster PolicyQuorumInput PolicyQuorumEvent :=
  PartyMachine.ofCustodyStep policyQuorumClusterStep

def cozkCeremonyPartyMachine (H : Hash) :
    PartyMachine CoZkCommittedState CoZkCommittedInput CoZkPublicEvent :=
  PartyMachine.ofCustodyStep (cozkPreOpenCeremonyStep H)


/-- Replacing committed wires after challenge disclosure can never be an accepted transition. -/
theorem tooth_cozk_substitution_cannot_accept (H : Hash)
    (s : CoZkCommittedState) (f : CoZkFrozenExecution) (a b : Tower128) (e : Fin 3)
    (outputs : List Tower128) (hv hs : Fin 3 → List UInt8) (salt : List UInt8) :
    ¬ ∃ next ev, cozkPreOpenCeremonyStep H { s with phase := .challenged f a b e }
      (.freezeWires outputs hv hs salt) = .accepted next ev := by
  rw [tooth_cozk_postchallenge_wire_substitution_rejected]
  rintro ⟨next, ev, h⟩
  cases h

/-- An actual four-transition ceremony reaches a release from the initial phase. -/
theorem inhabited_cozk_reachable_release (H : Hash) :
    ∃ (s₀ : CoZkCommittedState), ∃ tr sf root digest e v0 v1 hc,
      s₀.phase = .awaiting ∧ ValidCustodyTrace (cozkPreOpenCeremonyStep H) s₀ tr sf ∧
      .released root digest e v0 v1 hc ∈ traceApprovedOutputs tr :=
  inhabited_cozk_operational_ceremony_trace H

#verify_inhabited cozk_multiturn_operational_ceremony_sound inhabited_cozk_reachable_release
#tooth_pair cozk_multiturn_operational_ceremony_sound vs tooth_cozk_substitution_cannot_accept

end Qsag
end
