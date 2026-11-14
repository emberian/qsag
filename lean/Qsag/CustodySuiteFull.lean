module
/-
# Qsag.CustodySuiteFull — End-to-End Custody, Policy, Addressing & Co-ZK Migration Proofs

Self-contained Lean 4.35 formalization of the five custody and migration subsystems
(`Init` + `Qsag` constructive foundations, `0` proof gaps, `0` custom axioms, `0 Classical.choice`):

1. **Few-Time Signatures (`qsag-fts`)**:
   - Constant-sum Winternitz (`WOTS+CS`, `L = 68, base = 32, S = 136` and `w = 5`) strict
     codeword incomparability (`wotsCs_single_use_incomparable`) and constructive 1-CMA
     hash-chain preimage / claw extraction (`wotsCs_euf_1cma_extract_chain_preimage`).
   - `#tooth` 2-signature forward-only forgery witness (`tooth_wotsCs_two_signatures_enable_forward_only_forgery`).
   - Multi-turn 48-round $x^7$ SPN deferred-MAC session guard (`fts_spn_deferred_mac_blocks_dfa_across_epochs`)
     with durable 1-use epoch burn and MAC-context quarantine, paired with `#tooth` degree-6
     key-canceling differential polynomial (`tooth_value_open_before_mac_yields_deg6_key_eq`).
2. **Hierarchical Lattice Custody (`qsag-hd`)**:
   - Per-party committed MAC zero-test (`hd_committed_zero_test_sound`), anti-rushing commitment
     binding, quarantine-before-release, dealerless child-MAC key rotation independence, and
     7-repetition mod-`8380417` sacrifice soundness (`< 2^-157`), paired with `#tooth` rushing
     residual adaptation (`tooth_uncommitted_zero_test_rushing_forgery`).
   - `AuthorizedHdProjection` Module-LWE secret-fiber uniformity, single-use `OpeningMask`, and
     bounded `DurableQueryBudget` subspace entropy (`hd_authorized_budget_blocks_full_rank_reconstruction`),
     paired with `#tooth` full-rank basis reconstruction (`tooth_unrestricted_linear_forms_reconstruct_secret`).
3. **Stateful Policy Guard & Hybrid Addressing (`qsag-policy`, `qsag-addr`)**:
   - Multi-turn `StatefulPolicyGuard` spend cap, nonce replay prevention, and bijective length-framed
     `TransactionIntent` codec (`policy_multiturn_velocity_and_intent_binding`), paired with `#tooth`
     stateless caller-supplied spend bypass (`tooth_stateless_velocity_caller_spent_bypass`).
   - Universal `GF(2)`-linear `Bech32m` (`0x2bc830a3`) roundtrip, legacy BIP-173 rejection, and
     6-symbol burst detection (`bech32m_encode_verify_roundtrip`), plus `HybridPinnedEnvelope`
     non-strippability and conjunctive EUF-CMA reduction
     (`hybrid_pinned_non_strippable_and_combined_euf_cma`, `tooth_unpinned_concatenation_allows_pq_key_stripping`).
4. **Co-ZK Migration Ceremony (`qsag-migrate`)**:
   - 219-repetition ZKBoo soundness `< 2^-128` under frozen ceremony root commitments
     (`zkboo_219_soundness_lt_two_pow_neg128`).
   - Constructive 3-of-3 outer-MPC physical custodian key-privacy bijection
     (`cozk_outer_mpc_one_custodian_perfect_key_privacy`) proving exact view uniformity and
     witness independence across all 219 repetitions, paired with `#tooth` single-repetition
     direct-head key recovery (`tooth_direct_head_assignment_leaks_key_in_one_rep`).
   - Pre-open batch Beaver/BBCGGI19 multiplication & conversion sacrifice gate
     (`cozk_pre_open_mul_sacrifice_blocks_corrupted_head_release`) with 2-of-3 replicated
     cross-check and 2-coin $\mathbb{F}_{2^{128}}$ soundness (`< 2^-130`), paired with `#tooth`
     input-inconsistent AND selective-failure key-bit leak
     (`tooth_unverified_outer_mul_selective_fault_leaks_key_bit`).
-/

public import Qsag.Constructive
public import Qsag.SimulationSpine
public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Keccak
public import Qsag.UcGames
public import Qsag.MaliciousSecurity

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

/-- Constructive index extractor (`0 Classical.choice`) witnessing strict coordinate decrease
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
    `(L = 68, base = 32, S = 136)` and `(L = 68, base = 5, S = 136)`), any two distinct valid
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
    constructively (`0 Classical.choice`) extracts EITHER a direct 1-step backward chain preimage
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

/-- Exact $x^7$ S-box map over `Tower128 = GF(2^128)` used in all 48 SPN rounds of `qsag-fts`. -/
@[expose] def towerPow7 (x : Tower128) : Tower128 :=
  let x2 := towerMul 7 x x
  let x3 := towerMul 7 x2 x
  let x4 := towerMul 7 x2 x2
  towerMul 7 x4 x3

/-- Full 48-round $x^7$ key-alternating SPN evaluation over `Tower128`. -/
def evalSpn48Rounds (roundKeys : Fin 49 → Tower128) (input : Tower128) : Tower128 :=
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

/-- Outbound network events emitted by `ftsSpnStep`. -/
inductive FtsSpnEvent where
  | epochStarted (epoch : Nat)
  | phaseAdvanced (epoch : Nat) (nextPhase : FtsSpnPhase)
  | releasedRound48Signature (epoch : Nat) (round48Share : Tower128)
      (keySchedule : SpnKeySchedule48) (spnInput : Tower128)
      (recordedFaultDelta recordedDeltaGamma recordedAlpha : Tower128)
  deriving DecidableEq

/-- Error codes returned by `ftsSpnStep` (including poisoning transitions). -/
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

/-- Authoritative step transition of `ParallelSeededSignSession` (`PowerOpen -> IntermediateMacCommit ->
    IntermediateMacOpen -> ValueCommit -> ValueOpen` + durable 1-use burn + MAC quarantine),
    evaluating `evalSpn48Rounds` directly inside the state machine rather than trusting caller outputs. -/
@[expose] def ftsSpnStep (H : Hash) (st : FtsEpochGuardState) (inp : FtsSpnInput) :
    CustodyStepOutcome FtsEpochGuardState FtsSpnEvent FtsSpnErr :=
  if st.macContextPoisoned then
    .rejected st .macContextQuarantined
  else
    match inp, st.active with
    | .beginEpoch ep alpha ks xIn, none =>
      if ep ∈ st.burnedEpochs then
        .rejected st .epochAlreadyBurned
      else
        let honest48 := evalSpn48Rounds ks.keyAt xIn
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
        let evaluated48 := evalSpn48Rounds sess.keySchedule.keyAt (towerAdd 7 sess.spnInput deltaX)
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
def ftsReleasedEpochs : List FtsSpnEvent → List Nat
  | [] => []
  | .releasedRound48Signature ep _ _ _ _ _ _ :: rest => ep :: ftsReleasedEpochs rest
  | _ :: rest => ftsReleasedEpochs rest

/-- Well-formedness invariant of `FtsEpochGuardState` across multi-session traces, including
    exact binding of `unmaskedRound48Share` to `evalSpn48Rounds`. -/
def FtsStateInv (st : FtsEpochGuardState) : Prop :=
  match st.active with
  | none => True
  | some sess =>
    sess.epoch ∈ st.burnedEpochs ∧
    sess.unmaskedRound48Share =
      evalSpn48Rounds sess.keySchedule.keyAt (towerAdd 7 sess.spnInput sess.powerFaultDelta) ∧
    (sess.phase = .valueCommit ∨ sess.phase = .valueOpen →
      verifyLinearMacEquation sess.alpha (towerZero 7)
        sess.powerFaultDelta sess.openedIntermDeltaGamma = true)

private theorem fts_step_preserves_inv_and_sound {H : Hash}
    {st st' : FtsEpochGuardState} {inp : FtsSpnInput}
    (hInv : FtsStateInv st) :
    (∀ ev, ftsSpnStep H st inp = .accepted st' ev →
      FtsStateInv st' ∧
      (∀ ep out48 ks xIn dX dG alpha,
        ev = .releasedRound48Signature ep out48 ks xIn dX dG alpha →
          ep ∈ st.burnedEpochs ∧
          st'.active = none ∧
          st'.burnedEpochs = st.burnedEpochs ∧
          ((dX = towerZero 7 ∧ out48 = evalSpn48Rounds ks.keyAt xIn) ∨
            MacKeyRecoveryWitness 7 alpha dX dG))) ∧
    (∀ err, ftsSpnStep H st inp = .rejected st' err → FtsStateInv st') := by
  refine ⟨?_, ?_⟩
  · intro ev hAcc
    unfold ftsSpnStep at hAcc
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
    unfold ftsSpnStep at hRej
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
    {trace : List (FtsSpnInput × Option FtsSpnEvent)}
    (hTr : ValidCustodyTrace (ftsSpnStep H) st trace stFinal) :
    ∀ ep : Nat,
      ep ∈ st.burnedEpochs →
      (∀ sess, st.active = some sess → sess.epoch ≠ ep) →
      ep ∉ ftsReleasedEpochs (traceApprovedOutputs trace) := by
  induction hTr with
  | nil =>
    intro _ _ _ hMem; cases hMem
  | @consAccepted s s' _ inp out rest hStep _ ih =>
    intro ep hBurn hInact
    unfold ftsSpnStep at hStep
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
    unfold ftsSpnStep at hStep
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
       emitted on the outbound transcript satisfies EITHER
       `dX = 0 ∧ out48 = evalSpn48Rounds ks.keyAt xIn` (exact honest 48-round $x^7$ SPN evaluation
       with zero intermediate power/Beaver fault) OR `MacKeyRecoveryWitness 7 alpha dX dG`
       (global `GF(2^128)` MAC key algebraically forged).
    3. **Permanent Quarantine Latch**: Once `macContextPoisoned = true` (triggered immediately on
       any failed MAC or commitment opening), `stFinal.macContextPoisoned = true` and zero events
       are ever emitted again. -/
theorem fts_spn_deferred_mac_blocks_dfa_across_epochs
    (H : Hash) {st₀ stFinal : FtsEpochGuardState}
    {trace : List (FtsSpnInput × Option FtsSpnEvent)}
    (hInv₀ : FtsStateInv st₀)
    (hTrace : ValidCustodyTrace (ftsSpnStep H) st₀ trace stFinal) :
    (ftsReleasedEpochs (traceApprovedOutputs trace)).Nodup ∧
    (∀ ep out48 ks xIn dX dG alpha,
      FtsSpnEvent.releasedRound48Signature ep out48 ks xIn dX dG alpha ∈ traceApprovedOutputs trace →
        (dX = towerZero 7 ∧ out48 = evalSpn48Rounds ks.keyAt xIn) ∨
        MacKeyRecoveryWitness 7 alpha dX dG) ∧
    (st₀.macContextPoisoned = true →
      stFinal.macContextPoisoned = true ∧ traceApprovedOutputs trace = []) := by
  suffices ∀ {s sf : FtsEpochGuardState} {tr : List (FtsSpnInput × Option FtsSpnEvent)},
      ValidCustodyTrace (ftsSpnStep H) s tr sf →
      FtsStateInv s →
      (ftsReleasedEpochs (traceApprovedOutputs tr)).Nodup ∧
      (∀ ep out48 ks xIn dX dG alpha,
        FtsSpnEvent.releasedRound48Signature ep out48 ks xIn dX dG alpha ∈ traceApprovedOutputs tr →
          (dX = towerZero 7 ∧ out48 = evalSpn48Rounds ks.keyAt xIn) ∨
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
      unfold ftsSpnStep at hStep
      simp [hPois] at hStep
  | @consRejected s s' _ inp err rest hStep _ ih =>
    intro hInvS
    obtain ⟨_, hStepRej⟩ := fts_step_preserves_inv_and_sound (H := H) (st := s) (st' := s') (inp := inp) hInvS
    have hInv' := hStepRej err hStep
    obtain ⟨hNdRest, hSoundRest, hPoisRest⟩ := ih hInv'
    simp only [traceApprovedOutputs_cons_none]
    refine ⟨hNdRest, hSoundRest, fun hPois => ?_⟩
    unfold ftsSpnStep at hStep
    simp only [hPois, ↓reduceIte, CustodyStepOutcome.rejected.injEq] at hStep
    rcases hStep with ⟨rfl, _⟩
    exact hPoisRest hPois

/-- **`#tooth` Deferred-MAC Quarantine Witness (`tooth_fts_spn_dfa_fault_quarantined_before_value_open`)**:
    When a non-zero DFA fault `dX ≠ 0` is injected into the 48-round $x^7$ SPN session without
    knowing `alpha * dX`, `ftsSpnStep` aborts at `.intermediateMacOpen`, permanently sets
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
            unmaskedRound48Share := evalSpn48Rounds ks.keyAt (towerAdd 7 xIn dX) } }
    ftsSpnStep H st (.submitIntermMacOpen dGamma salt) =
      .rejected { st with macContextPoisoned := true, active := none } .intermediateMacOrCommitFailed := by
  intro cHash st
  unfold ftsSpnStep
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
    49-key SPN schedule executing `evalSpn48Rounds` end-to-end across all 6 session phases. -/
theorem witness_fts_spn_session_inhabited :
    let H : Hash := shake256Xof 32
    let ks : SpnKeySchedule48 := { keys := List.replicate 49 (towerOne 7) }
    let xIn : Tower128 := towerOne 7
    let st₀ : FtsEpochGuardState := { burnedEpochs := [], macContextPoisoned := false, active := none }
    (H [0x00]).length = 32 ∧
    H [0x00] ≠ [0x00] ∧
    ∃ trace stFinal,
      FtsStateInv st₀ ∧
      ValidCustodyTrace (ftsSpnStep H) st₀ trace stFinal ∧
      ftsReleasedEpochs (traceApprovedOutputs trace) = [0] ∧
      FtsSpnEvent.releasedRound48Signature 0 (evalSpn48Rounds ks.keyAt xIn) ks xIn
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
  let out48 := evalSpn48Rounds ks.keyAt xIn
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
  have hs1 : ftsSpnStep H st₀ (.beginEpoch 0 alpha ks xIn) = .accepted s1 (.epochStarted 0) := by
    unfold ftsSpnStep
    dsimp only [st₀, s1, out48]
    simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil]
  have hs2 : ftsSpnStep H s1 (.submitPowerOpen (towerZero 7)) =
      .accepted s2 (.phaseAdvanced 0 .intermediateMacCommit) := by
    unfold ftsSpnStep
    dsimp only [s1, s2, out48]
    simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl, towerAdd_zero]
  have hs3 : ftsSpnStep H s2 (.submitIntermMacCommit cMac) =
      .accepted s3 (.phaseAdvanced 0 .intermediateMacOpen) := by
    unfold ftsSpnStep
    dsimp only [s1, s2, s3]
    simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl]
  have hs4 : ftsSpnStep H s3 (.submitIntermMacOpen (towerZero 7) salt) =
      .accepted s4 (.phaseAdvanced 0 .valueCommit) := by
    have hBeqMac : (H (encodeTower128CommitPayload 0x41 (towerZero 7) salt) == cMac) = true :=
      uint8List_beq_self cMac
    have hMac : verifyLinearMacEquation alpha (towerZero 7) (towerZero 7) (towerZero 7) = true := by
      unfold verifyLinearMacEquation
      apply decide_eq_true_eq.mpr
      dsimp only [CommRingOps.sub, CommRingOps.mul, towerCommRingOps]
      rw [towerAdd_self_zero, towerMul_zero]
    unfold ftsSpnStep
    dsimp only [s1, s3, s4]
    simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl, hBeqMac, hMac, Bool.and_self]
  have hs5 : ftsSpnStep H s4 (.submitValueCommit cVal) =
      .accepted s5 (.phaseAdvanced 0 .valueOpen) := by
    unfold ftsSpnStep
    dsimp only [s1, s4, s5]
    simp only [Bool.false_eq_true, ↓reduceIte, BEq.rfl]
  have hs6 : ftsSpnStep H s5 (.submitValueOpen salt) =
      .accepted s6 (.releasedRound48Signature 0 out48 ks xIn (towerZero 7) (towerZero 7) alpha) := by
    have hBeqVal : (H (encodeTower128CommitPayload 0x42 out48 salt) == cVal) = true :=
      uint8List_beq_self cVal
    unfold ftsSpnStep
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

private theorem filter_any_length_le_sum {α β : Type} (lanes : List β)
    (pred : β → α → Bool) (xs : List α) :
    (xs.filter (fun x => lanes.any (fun l => pred l x))).length ≤
      (lanes.map (fun l => (xs.filter (pred l)).length)).sum := by
  induction lanes with
  | nil => simp
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
      | nil => simp
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

/-- Errors produced by `hdZeroTestStep`. -/
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

/-- Outbound events of `hdZeroTestStep`. -/
inductive HdZeroTestEvent where
  | commitsFrozen (maskId : Nat) (hardened : Bool)
  | scalarReleased (maskId : Nat) (hardened : Bool) (yOpened yTrue alphaChild deltaGamma : HdFq204)
  deriving DecidableEq, Repr

/-- Authoritative step transition of `qsag-hd` per-party committed MAC zero-testing over `HdFq204`
    (`q = 8380417`) with hardened-lineage non-downgrade enforcement, internal `evalLinearForm`
    evaluation against `enrolledShares`, single-use `OpeningMask`, bounded `DurableQueryBudget`,
    and immediate family quarantine on mismatch. -/
@[expose] def hdZeroTestStep (H : Hash) (n dim : Nat)
    (st : HdFamilyState n dim) (inp : HdZeroTestInput n dim) :
    CustodyStepOutcome (HdFamilyState n dim) HdZeroTestEvent HdErr :=
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
      hdZeroTestStep H n dim st
        (.freezeMacCommits tag maskId false false wForm yCand aChild dG commits) =
      .rejected st .hardenedLineageDowngradeBlocked) ∧
    hdZeroTestStep H n dim st
      (.freezeMacCommits tag maskId true true wForm yCand aChild dG commits) =
      .rejected st .hardenedLineageDowngradeBlocked := by
  constructor
  · intro hPar
    unfold hdZeroTestStep
    simp [hClean, hIdle, hPar]
  · unfold hdZeroTestStep
    simp [hClean, hIdle]

/-- Constructive anti-rushing commitment binding extractor (`0 Classical.choice`): any party `c`
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
    2. **Fault Soundness & Quarantine-Before-Release over `HdFq204`**: On any step of `hdZeroTestStep`,
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
      hdZeroTestStep H n dim st inp =
        .accepted st' (.scalarReleased maskId hardened yOpened yTrue alphaChild dGamma) →
      yOpened = yTrue ∨
        HdFq204.mul dGamma (HdFq204.inv (HdFq204.sub yOpened yTrue)) = alphaChild) ∧
    (∀ (st stFinal : HdFamilyState n dim)
       (trace : List (HdZeroTestInput n dim × Option HdZeroTestEvent)),
      st.familyQuarantined = true →
      ValidCustodyTrace (hdZeroTestStep H n dim) st trace stFinal →
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
    unfold hdZeroTestStep at hStep
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
            simp only [CustodyStepOutcome.accepted.injEq, HdZeroTestEvent.scalarReleased.injEq] at hStep
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
      unfold hdZeroTestStep at hStep
      simp [hQuar] at hStep
    | consRejected hStep _ ih =>
      unfold hdZeroTestStep at hStep
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
def hdFrozenMaskIds : List HdZeroTestEvent → List Nat
  | [] => []
  | .commitsFrozen mid _ :: rest => mid :: hdFrozenMaskIds rest
  | .scalarReleased _ _ _ _ _ _ :: rest => hdFrozenMaskIds rest

private theorem hd_no_freeze_if_consumed {H : Hash} {n dim : Nat}
    {st stFinal : HdFamilyState n dim}
    {trace : List (HdZeroTestInput n dim × Option HdZeroTestEvent)}
    (hTr : ValidCustodyTrace (hdZeroTestStep H n dim) st trace stFinal) :
    ∀ m ∈ st.consumedMasks, m ∉ hdFrozenMaskIds (traceApprovedOutputs trace) := by
  induction hTr with
  | nil => intro _ _ hm; cases hm
  | @consAccepted s s' _ inp out rest hStep _ ih =>
    intro m hm
    unfold hdZeroTestStep at hStep
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
    unfold hdZeroTestStep at hStep
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
    1. Across any multi-turn `hdZeroTestStep` trace over `HdFq204` (`q = 8380417`) from `st₀`
       (`st₀.usedQueries ≤ st₀.budgetCap`), `stFinal.usedQueries ≤ st₀.budgetCap` and all consumed
       `OpeningMask` IDs are duplicate-free (`Nodup`).
    2. For ANY two distinct short MLWE witnesses `wA ≠ wB : ShortMlweWitness hdCbdEta d1 d2 A tPub`
       (`‖s1‖_∞ ≤ 2 ∧ ‖s2‖_∞ ≤ 2`) and ANY `Q` authorized projections `wForms` and transcript `tr`,
       `hdAuthorizedMlweFiberEquiv` produces distinct masked states `(wA, masksA) ≠ (wB, masksB)`
       matching **identical** public key `tPub` and **identical** masked openings `tr`.
    3. Whenever `budgetCap < dim`, even unmasked prefix openings of a short secret (`‖opened‖_∞ ≤ hdCbdEta`)
       admit distinct **short** secrets `sA ≠ sB` (`‖sA‖_∞ ≤ hdCbdEta ∧ ‖sB‖_∞ ≤ hdCbdEta`) matching all
       `budgetCap` opened coordinates! -/
theorem hd_authorized_budget_blocks_full_rank_reconstruction
    (H : Hash) (n dim : Nat) :
    (∀ {st₀ stFinal : HdFamilyState n dim}
       {trace : List (HdZeroTestInput n dim × Option HdZeroTestEvent)},
      st₀.usedQueries ≤ st₀.budgetCap →
      ValidCustodyTrace (hdZeroTestStep H n dim) st₀ trace stFinal →
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
        {tr : List (HdZeroTestInput n dim × Option HdZeroTestEvent)},
        ValidCustodyTrace (hdZeroTestStep H n dim) s tr sf →
        s.usedQueries ≤ s.budgetCap →
        sf.usedQueries ≤ s.budgetCap ∧
        (hdFrozenMaskIds (traceApprovedOutputs tr)).Nodup by
      exact this hTr hCap₀
    intro s sf tr hT
    induction hT with
    | nil => intro hLe; exact ⟨hLe, .nil⟩
    | @consAccepted st st' _ inp out rest hStep hRest ih =>
      intro hLe
      unfold hdZeroTestStep at hStep
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
      unfold hdZeroTestStep at hStep
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
      ValidCustodyTrace (hdZeroTestStep H 1 1) st₀ trace stFinal ∧
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
  have hs1 : hdZeroTestStep H 1 1 st₀
      (.freezeMacCommits [0x01] 7 true false wForm HdFq204.one HdFq204.one HdFq204.zero (fun _ => c0)) =
      .accepted s1 (.commitsFrozen 7 true) := by
    have hBudget : 0 < 4 := by decide
    unfold hdZeroTestStep
    dsimp only [st₀, s1, frz, yTrueVal]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.and_false, Bool.or_self,
      List.not_mem_nil, hBudget, not_true_eq_false, Nat.zero_add]
  have hs2 : hdZeroTestStep H 1 1 s1
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
    unfold hdZeroTestStep
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

/-- Module-local structural unsigned LEB128 encoder for unbounded-`Nat` mathematical fallback (`0 Classical.choice`). -/
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

/-- Constructive structural unsigned LEB128 stream decoder (`0 Classical.choice`). -/
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

/-- Constructive (`0 Classical.choice`) binding theorem for `toCanonicalSigningBytes`:
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

/-- Authoritative multi-turn policy state maintained inside custodian HSM / signer memory. -/
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

/-- Approved signing envelope emitted by `policyGuardStep`. -/
structure ApprovedIntentEnvelope where
  intent : TransactionIntent
  canonicalBytes : List UInt8
  deriving DecidableEq, Repr

/-- Rejection reasons of `policyGuardStep`. -/
inductive PolicyRejectReason where
  | windowMismatch
  | policyDigestMismatch
  | authorityDigestMismatch
  | recipientNotAllowlisted
  | perTxCapExceeded
  | velocityWindowExceeded
  | duplicateIntentNonce
  deriving DecidableEq, Repr

/-- Authoritative stateful velocity, allowlist, digest-pinning, and nonce-replay guard transition. -/
@[expose] def policyGuardStep (g : StatefulPolicyGuard) (tx : TransactionIntent) :
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

/-- Construct a fixed-width `w`-slot sliding-window bitmap structurally (`0 Classical.choice`). -/
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

theorem slidingWindowTest_ge_length :
    ∀ (bm : List Bool) (k : Nat), bm.length ≤ k → slidingWindowTest bm k = false
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: bs, j + 1, h =>
    slidingWindowTest_ge_length bs j (Nat.le_of_succ_le_succ h)

/-- Authoritative bounded-state `qsag-policy` guard eliminating the 256-slot FIFO eviction replay wrap
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

/-- Candidate inputs to `policyWatermarkGuardStep` (signing intent evaluation or clock-anchored window advance). -/
inductive PolicyWatermarkInput where
  | evaluateIntent (tx : TransactionIntent)
  | advanceEpoch (nowSecs : Nat)
  deriving DecidableEq, Repr

/-- Observable events of `policyWatermarkGuardStep`. -/
inductive PolicyWatermarkEvent where
  | intentApproved (intent : TransactionIntent) (canonicalSigningBytes : List UInt8)
  | epochAdvanced (newWindowId : Nat) (newEpochStartSecs : Nat)
  deriving DecidableEq, Repr

/-- Rejection reasons of `policyWatermarkGuardStep`. -/
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

/-- Authoritative `PolicyWatermarkGuard` transition enforcing monotonic `minNonceWatermark` + sliding-window
    anti-replay, default-on initiator MAC authentication, and clock-anchored velocity window rotation
    that preserves `(minNonceWatermark, slidingBitmap)` across epochs. -/
def policyWatermarkGuardStep (g : PolicyWatermarkGuard) (inp : PolicyWatermarkInput) :
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

private theorem policyWatermarkGuardStep_rejected_eq
    {g g' : PolicyWatermarkGuard} {inp : PolicyWatermarkInput} {err : PolicyWatermarkReject}
    (hStep : policyWatermarkGuardStep g inp = .rejected g' err) :
    g' = g := by
  unfold policyWatermarkGuardStep at hStep
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
    (hStep : policyWatermarkGuardStep g inp = .accepted g' ev) :
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
  unfold policyWatermarkGuardStep at hStep
  if hBadW : (g.slidingWindowWidth == 0 || g.slidingBitmap.length != g.slidingWindowWidth) = true then
    simp [hBadW] at hStep
  else
    have hWPos : 0 < g.slidingWindowWidth := by
      cases hZ : (g.slidingWindowWidth == 0)
      · have hNe0 : g.slidingWindowWidth ≠ 0 := fun h0 => by simp [h0] at hZ
        omega
      · exfalso; exact hBadW (by simp [hZ])
    have hBmLen : g.slidingBitmap.length = g.slidingWindowWidth := by
      cases hEq : (g.slidingBitmap.length == g.slidingWindowWidth)
      · exfalso; exact hBadW (by simp [bne, hEq])
      · exact of_decide_eq_true hEq
    simp only [hBadW, Bool.false_eq_true, ↓reduceIte] at hStep
    cases inp with
    | advanceEpoch nowSecs =>
      if hEarly : (g.epoch_duration_secs == 0 ||
                   decide (nowSecs < g.epoch_start_secs + g.epoch_duration_secs)) = true then
        simp [hEarly] at hStep
      else
        simp only [hEarly, Bool.false_eq_true, ↓reduceIte, CustodyStepOutcome.accepted.injEq] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        exact ⟨hWPos, hBmLen, Nat.le_refl _, rfl, fun _ h => h, fun _ _ hEv => by cases hEv⟩
    | evaluateIntent tx =>
      if c1 : (tx.chain_id != g.chain_id || tx.suite_tag != g.pinned_suite_tag ||
               tx.recipient_suite_tag != g.pinned_suite_tag) = true then
        simp [c1] at hStep
      else if c2 : (tx.window_id != g.window_id) = true then
        simp [c1, c2] at hStep
      else if c3 : (tx.policy_digest != g.pinned_policy_digest ||
                    tx.authority_digest != g.pinned_authority_digest) = true then
        simp [c1, c2, c3] at hStep
      else if c4 : (g.requireAuthenticatedInitiator && tx.init_mac_bytes.isEmpty) = true then
        simp [c1, c2, c3, c4] at hStep
      else if c5 : ¬ (tx.recipient ∈ g.allowed_recipients) then
        simp [c1, c2, c3, c4, c5] at hStep
      else if c6 : ¬ (tx.amount_units ≤ g.per_tx_cap) then
        simp [c1, c2, c3, c4, c5, c6] at hStep
      else if c7 : ¬ (g.accumulated_spend + tx.amount_units ≤ g.velocity_window_cap) then
        simp [c1, c2, c3, c4, c5, c6, c7] at hStep
      else if c8 : tx.nonce < g.minNonceWatermark then
        simp [c1, c2, c3, c4, c5, c6, c7, c8] at hStep
      else
        simp only [c1, c2, c3, c4, c5, c6, c7, c8, Bool.false_eq_true, ↓reduceIte] at hStep
        have hAuthInit : g.requireAuthenticatedInitiator = true → tx.init_mac_bytes ≠ [] := by
          intro hReq hEmp
          exact c4 (by simp [hReq, hEmp])
        if hInWin : tx.nonce - g.minNonceWatermark < g.slidingWindowWidth then
          simp only [hInWin, ↓reduceIte] at hStep
          if hDup : slidingWindowTest g.slidingBitmap (tx.nonce - g.minNonceWatermark) = true then
            simp [hDup] at hStep
          else
            simp only [hDup, Bool.false_eq_true, ↓reduceIte, CustodyStepOutcome.accepted.injEq] at hStep
            rcases hStep with ⟨rfl, rfl⟩
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
                rw [slidingWindowTest_buildSlidingWindow]
                simp only [hLtW, ↓reduceIte, Bool.or_eq_true]
                exact Or.inl hBit
            · intro tx' sb' hEv
              injection hEv with hTx hSb
              subst hTx hSb
              refine ⟨?_, ?_, rfl, hAuthInit⟩
              · rintro (hLt | hBit)
                · exact c8 hLt
                · exact hDup hBit
              · apply Or.inr
                rw [slidingWindowTest_buildSlidingWindow]
                simp only [hInWin, ↓reduceIte, Bool.or_eq_true]
                exact Or.inr rfl
        else
          simp only [hInWin, ↓reduceIte, CustodyStepOutcome.accepted.injEq] at hStep
          rcases hStep with ⟨rfl, rfl⟩
          refine ⟨hWPos, buildSlidingWindow_length _ _, Nat.le_add_right _ _, rfl, ?_, ?_⟩
          · intro n hn
            if hBelowNew :
                n < g.minNonceWatermark + ((tx.nonce - g.minNonceWatermark) - (g.slidingWindowWidth - 1)) then
              exact Or.inl hBelowNew
            else
              rcases hn with hLtOld | hBitOld
              · omega
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
                rw [slidingWindowTest_buildSlidingWindow]
                simp only [hNewLtW, ↓reduceIte, Bool.or_eq_true]
                exact Or.inl (hIdxEq.symm ▸ hBitOld)
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
              rw [hTopIdx, slidingWindowTest_buildSlidingWindow]
              simp only [hWm1Lt, ↓reduceIte, Bool.or_eq_true]
              exact Or.inr rfl

private theorem watermark_no_approved_if_consumed
    {g gFinal : PolicyWatermarkGuard}
    {trace : List (PolicyWatermarkInput × Option PolicyWatermarkEvent)}
    (hTr : ValidCustodyTrace policyWatermarkGuardStep g trace gFinal) :
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
    have hSame : s' = s := policyWatermarkGuardStep_rejected_eq hStep
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
theorem policy_watermark_sliding_window_multiturn_sound
    {g₀ gFinal : PolicyWatermarkGuard}
    {trace : List (PolicyWatermarkInput × Option PolicyWatermarkEvent)}
    (hTrace : ValidCustodyTrace policyWatermarkGuardStep g₀ trace gFinal) :
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
    have hSame : s' = s := policyWatermarkGuardStep_rejected_eq hStep
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
    replayed and accepted a SECOND time, whereas `policyWatermarkGuardStep` advances `minNonceWatermark`
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
     policyWatermarkGuardStep g₀ (.evaluateIntent replay0) =
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
     match policyGuardStep g₀ tx1 with
     | .accepted g₁ _ =>
       policyGuardStep g₁ tx2 = .rejected g₁ .velocityWindowExceeded
     | .rejected _ _ => False) := by
  simp [statelessCallerVelocityCheck, policyGuardStep]

/-- Inhabitedness witness for `policy_multiturn_velocity_and_intent_binding` approving two distinct
    transactions (`40 + 55 = 95 ≤ 100`) and rejecting a third overflow request (`95 + 20 > 100`). -/
theorem witness_policy_multiturn_inhabited :
    let g₀ : StatefulPolicyGuard :=
      { window_id := 1, velocity_window_cap := 100, accumulated_spend := 0,
         burned_intent_nonces := [], pinned_policy_digest := [0xAA],
         pinned_authority_digest := [0xBB], allowed_recipients := [[0x01]], per_tx_cap := 60 }
    ∃ trace gFinal,
      ValidCustodyTrace policyGuardStep g₀ trace gFinal ∧
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
  have hs1 : policyGuardStep g₀ tx1 =
      .accepted g₁ { intent := tx1, canonicalBytes := encodeTransactionIntent tx1 } := by
    simp [policyGuardStep, g₀, g₁, tx1]
  have hs2 : policyGuardStep g₁ tx2 =
      .accepted g₂ { intent := tx2, canonicalBytes := encodeTransactionIntent tx2 } := by
    simp [policyGuardStep, g₀, g₁, g₂, tx2]
  have hs3 : policyGuardStep g₂ tx3 = .rejected g₂ .velocityWindowExceeded := by
    simp [policyGuardStep, g₀, g₂, tx3]
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
  | chk, v :: vs => bech32FoldBv (bech32StepBv chk v.toBitVec) vs

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
    ∀ (c : BitVec 32) (vs : List UInt8),
      c.getLsbD 30 = false → c.getLsbD 31 = false →
      (bech32FoldBv c vs).getLsbD 30 = false ∧ (bech32FoldBv c vs).getLsbD 31 = false
  | _, [], h30, h31 => ⟨h30, h31⟩
  | c, v :: vs, _, _ =>
    let ⟨n30, n31⟩ := bech32StepBv_high_bits_zero c v.toBitVec
    bech32FoldBv_high_bits_zero _ vs n30 n31

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
