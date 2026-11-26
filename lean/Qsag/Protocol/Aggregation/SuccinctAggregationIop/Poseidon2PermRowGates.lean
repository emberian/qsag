module
/-
# Exact Degree-at-Most-7 Row Gates for the `Poseidon2` Permutation, Base-4 Digits, and Booleans (`trace.rs`)

The `Poseidon2PermWitness` row gates: external and internal round S-box residuals over the
round constants, the honest permutation witness `honestPoseidon2PermWitness` with residuals that
vanish exactly on it, the quartic base-4 digit gate `quarticBase4`, and the Boolean residual
`boolBitResidual`.
-/

public import Qsag.Protocol.Aggregation.SuccinctAggregationIop.RowArithmetizationKernels

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv
set_option autoImplicit false
set_option exponentiation.threshold 2048
attribute [local irreducible] verifyUpperLayers
attribute [local irreducible] computeMessageMu
attribute [local irreducible] verifyAggNativeSigStateful verifyAggNativeSigStateless

/-! ### Exact Degree-≤7 Algebraic Row Gates (`Poseidon2PermWitness`, Base-4, Unary WOTS+C, Merkle) -/

/-- Check whether every `Goldilocks` residual in a list vanishes. -/
@[expose] def allZeroGoldilocks (rs : List Goldilocks) : Bool :=
  rs.all (· == Goldilocks.zero)

theorem allZeroGoldilocks_append (a b : List Goldilocks) :
    allZeroGoldilocks (a ++ b) = (allZeroGoldilocks a && allZeroGoldilocks b) := by
  unfold allZeroGoldilocks
  exact List.all_append

theorem sub_eq_zero_iff_goldilocks (a b : Goldilocks) :
    (Goldilocks.sub a b == Goldilocks.zero) = true ↔ a = b := by
  rw [beq_iff_eq]
  exact LawfulCommRing.sub_eq_zero_iff

theorem gold_sub_eq_zero_iff (a b : Goldilocks) :
    Goldilocks.sub a b = Goldilocks.zero ↔ a = b :=
  LawfulCommRing.sub_eq_zero_iff

theorem list_map_eq_self_of_forall {α : Type} {f : α → α} :
    ∀ (l : List α), (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, h a (List.mem_cons_self ..),
        list_map_eq_self_of_forall l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Quartic base-4 gate `d * (d - 1) * (d - 2) * (d - 3)` (`degree 4 ≤ 7`, `arithmetize.rs`). -/
@[expose] def quarticBase4 (d : Goldilocks) : Goldilocks :=
  Goldilocks.mul
    (Goldilocks.mul d (Goldilocks.sub d Goldilocks.one))
    (Goldilocks.mul (Goldilocks.sub d (Goldilocks.ofNat 2)) (Goldilocks.sub d (Goldilocks.ofNat 3)))

theorem quarticBase4_eq_zero_iff (d : Goldilocks) :
    quarticBase4 d = Goldilocks.zero ↔ d.val < 4 := by
  constructor
  · intro h
    unfold quarticBase4 at h
    change CommRingOps.mul
      (CommRingOps.mul d (CommRingOps.sub d Goldilocks.one))
      (CommRingOps.mul (CommRingOps.sub d (Goldilocks.ofNat 2)) (CommRingOps.sub d (Goldilocks.ofNat 3))) =
      CommRingOps.zero at h
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h with h01 | h23
    · rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h01 with h0 | h1
      · rw [h0]; decide
      · have hd1 : d = Goldilocks.one := LawfulCommRing.sub_eq_zero_iff.mp h1
        rw [hd1]; decide
    · rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h23 with h2 | h3
      · have hd2 : d = Goldilocks.ofNat 2 := LawfulCommRing.sub_eq_zero_iff.mp h2
        rw [hd2]; decide
      · have hd3 : d = Goldilocks.ofNat 3 := LawfulCommRing.sub_eq_zero_iff.mp h3
        rw [hd3]; decide
  · intro hLt
    have hCases : d = Goldilocks.zero ∨ d = Goldilocks.one ∨
                  d = Goldilocks.ofNat 2 ∨ d = Goldilocks.ofNat 3 := by
      rcases d with ⟨v, hv⟩
      dsimp only at hLt
      have hvCases : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
      rcases hvCases with rfl | rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl (Goldilocks.ext rfl)))
      · exact .inr (.inr (.inr (Goldilocks.ext rfl)))
    rcases hCases with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Quadratic Boolean bit gate `b * (b - 1)` (`degree 2 ≤ 7`). -/
@[expose] def boolBitResidual (b : Goldilocks) : Goldilocks :=
  Goldilocks.mul b (Goldilocks.sub b Goldilocks.one)

theorem boolBitResidual_eq_zero_iff (b : Goldilocks) :
    boolBitResidual b = Goldilocks.zero ↔ (b = Goldilocks.zero ∨ b = Goldilocks.one) := by
  constructor
  · intro h
    change CommRingOps.mul b (CommRingOps.sub b Goldilocks.one) = CommRingOps.zero at h
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h with h0 | h1
    · exact .inl h0
    · exact .inr (LawfulCommRing.sub_eq_zero_iff.mp h1)
  · rintro (rfl | rfl) <;> decide +kernel

/-- Full 30-round Width-12 `Poseidon2` permutation row witness (`118` S-box wires + `12` output wires,
    matching `COL_SBOX_OUT = 12..130` in `trace.rs:32`). -/
structure Poseidon2PermWitness where
  input       : Poseidon2State12
  initExtSbox : List Poseidon2State12
  intSbox     : List Goldilocks
  termExtSbox : List Poseidon2State12
  output      : Poseidon2State12
  deriving DecidableEq, Repr

@[expose] def buildRoundsSboxPoly {RC ST SB : Type}
    (sboxFn : RC → ST → SB) (nextFn : ST → SB → ST) :
    List RC → ST → List SB
  | [], _ => []
  | rc :: rcs, cur =>
    let sb := sboxFn rc cur
    sb :: buildRoundsSboxPoly sboxFn nextFn rcs (nextFn cur sb)

@[expose] def roundsResidualsPoly {RC ST SB RES : Type}
    (sboxFn : RC → ST → SB) (nextFn : ST → SB → ST)
    (diffFn : SB → SB → List RES) (badRes : List RES) :
    List RC → List SB → ST → (ST × List RES)
  | [], [], cur => (cur, [])
  | rc :: rcs, sb :: sbs, cur =>
    let expected := sboxFn rc cur
    let (finalSt, restRes) := roundsResidualsPoly sboxFn nextFn diffFn badRes rcs sbs (nextFn cur sb)
    (finalSt, diffFn expected sb ++ restRes)
  | [], _ :: _, cur => (cur, badRes)
  | _ :: _, [], cur => (cur, badRes)

private theorem roundsResidualsPoly_honest {RC ST SB RES : Type}
    (sboxFn : RC → ST → SB) (nextFn : ST → SB → ST)
    (diffFn : SB → SB → List RES) (badRes : List RES)
    (roundFn : RC → ST → ST)
    (hRound : ∀ rc cur, nextFn cur (sboxFn rc cur) = roundFn rc cur)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hDiffSelf : ∀ sb, zeroPred (diffFn sb sb) = true) :
    ∀ (rcs : List RC) (cur : ST),
      zeroPred (roundsResidualsPoly sboxFn nextFn diffFn badRes rcs
        (buildRoundsSboxPoly sboxFn nextFn rcs cur) cur).2 = true ∧
      (roundsResidualsPoly sboxFn nextFn diffFn badRes rcs
        (buildRoundsSboxPoly sboxFn nextFn rcs cur) cur).1 = runRounds roundFn rcs cur
  | [], cur => by
    simp only [buildRoundsSboxPoly, roundsResidualsPoly, runRounds_nil]
    exact ⟨hNil, True.intro⟩
  | rc :: rcs, cur => by
    simp only [buildRoundsSboxPoly, roundsResidualsPoly, runRounds_cons]
    rw [hRound rc cur]
    have ih := roundsResidualsPoly_honest sboxFn nextFn diffFn badRes roundFn hRound
      zeroPred hNil hAppend hDiffSelf rcs (roundFn rc cur)
    rw [hAppend, hDiffSelf, ih.1]
    exact ⟨rfl, ih.2⟩

private theorem roundsResidualsPoly_allZero_iff {RC ST SB RES : Type}
    (sboxFn : RC → ST → SB) (nextFn : ST → SB → ST)
    (diffFn : SB → SB → List RES) (badRes : List RES)
    (roundFn : RC → ST → ST)
    (hRound : ∀ rc cur, nextFn cur (sboxFn rc cur) = roundFn rc cur)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true)
    (hBad : zeroPred badRes = false)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hDiffZeroIff : ∀ a b, zeroPred (diffFn a b) = true ↔ a = b) :
    ∀ (rcs : List RC) (sbs : List SB) (cur : ST),
      zeroPred (roundsResidualsPoly sboxFn nextFn diffFn badRes rcs sbs cur).2 = true ↔
        sbs = buildRoundsSboxPoly sboxFn nextFn rcs cur
  | [], [], _ => by
    dsimp only [roundsResidualsPoly, buildRoundsSboxPoly]
    simp [hNil]
  | [], _ :: _, _ => by
    dsimp only [roundsResidualsPoly, buildRoundsSboxPoly]
    simp [hBad]
  | _ :: _, [], _ => by
    dsimp only [roundsResidualsPoly, buildRoundsSboxPoly]
    simp [hBad]
  | rc :: rcs, sb :: sbs, cur => by
    dsimp only [roundsResidualsPoly, buildRoundsSboxPoly]
    rw [hAppend, Bool.and_eq_true, hDiffZeroIff, List.cons.injEq]
    constructor
    · rintro ⟨hSb, hRest⟩
      subst hSb
      rw [hRound rc cur] at hRest ⊢
      exact ⟨rfl, (roundsResidualsPoly_allZero_iff sboxFn nextFn diffFn badRes roundFn hRound
        zeroPred hNil hBad hAppend hDiffZeroIff rcs sbs (roundFn rc cur)).mp hRest⟩
    · rintro ⟨hSb, hSbs⟩
      subst hSb hSbs
      rw [hRound rc cur]
      have hSelf : ∀ x, zeroPred (diffFn x x) = true := fun x => (hDiffZeroIff x x).mpr rfl
      exact ⟨rfl, (roundsResidualsPoly_honest sboxFn nextFn diffFn badRes roundFn hRound
        zeroPred hNil hAppend hSelf rcs (roundFn rc cur)).1⟩

def extRoundSboxFn (rc cur : Poseidon2State12) : Poseidon2State12 :=
  sboxState12 (state12Add cur rc)

def extRoundNextFn (_cur sb : Poseidon2State12) : Poseidon2State12 :=
  applyME sb

def intRoundSboxFn (rc : Goldilocks) (cur : Poseidon2State12) : Goldilocks :=
  sbox7 (Goldilocks.add cur.b0.x0 rc)

def intRoundNextFn (cur : Poseidon2State12) (sb : Goldilocks) : Poseidon2State12 :=
  applyMI ⟨⟨sb, cur.b0.x1, cur.b0.x2, cur.b0.x3⟩, cur.b1, cur.b2⟩

@[expose] def buildExtRoundsSbox (rcs : List Poseidon2State12) (cur : Poseidon2State12) : List Poseidon2State12 :=
  buildRoundsSboxPoly extRoundSboxFn extRoundNextFn rcs cur

@[expose] def buildIntRoundsSbox (rcs : List Goldilocks) (cur : Poseidon2State12) : List Goldilocks :=
  buildRoundsSboxPoly intRoundSboxFn intRoundNextFn rcs cur

/-- Canonical honest `Poseidon2PermWitness` for `input`. -/
@[expose] def honestPoseidon2PermWitness (input : Poseidon2State12) : Poseidon2PermWitness :=
  let s0 := applyME input
  let initSb := buildExtRoundsSbox poseidon2InitialExtConsts s0
  let s1 := runRounds externalRound poseidon2InitialExtConsts s0
  let intSb := buildIntRoundsSbox poseidon2InternalConsts s1
  let s2 := runRounds internalRound poseidon2InternalConsts s1
  let termSb := buildExtRoundsSbox poseidon2TerminalExtConsts s2
  let s3 := runRounds externalRound poseidon2TerminalExtConsts s2
  { input       := input
    initExtSbox := initSb
    intSbox     := intSb
    termExtSbox := termSb
    output      := s3 }

@[expose] def extRoundsResiduals (rcs : List Poseidon2State12) (cur : Poseidon2State12)
    (sbs : List Poseidon2State12) : (Poseidon2State12 × List Goldilocks) :=
  roundsResidualsPoly extRoundSboxFn extRoundNextFn
    (fun a b => (state12Sub a b).toList) [Goldilocks.one] rcs sbs cur

def intRoundsResiduals (rcs : List Goldilocks) (cur : Poseidon2State12)
    (sbs : List Goldilocks) : (Poseidon2State12 × List Goldilocks) :=
  roundsResidualsPoly intRoundSboxFn intRoundNextFn
    (fun a b => [Goldilocks.sub a b]) [Goldilocks.one] rcs sbs cur

/-- Degree-7 S-box + linear round residuals (`118 + 12 = 130` residuals when well-shaped). -/
@[expose] def poseidon2PermResiduals (w : Poseidon2PermWitness) : List Goldilocks :=
  let s0 := applyME w.input
  let (s1, res1) := extRoundsResiduals poseidon2InitialExtConsts s0 w.initExtSbox
  let (s2, res2) := intRoundsResiduals poseidon2InternalConsts s1 w.intSbox
  let (s3, res3) := extRoundsResiduals poseidon2TerminalExtConsts s2 w.termExtSbox
  res1 ++ res2 ++ res3 ++ (state12Sub s3 w.output).toList

theorem state12Sub_toList_allZero_iff (a b : Poseidon2State12) :
    allZeroGoldilocks (state12Sub a b).toList = true ↔ a = b := by
  rcases a with ⟨⟨a0, a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩, ⟨a8, a9, a10, a11⟩⟩
  rcases b with ⟨⟨b0, b1, b2, b3⟩, ⟨b4, b5, b6, b7⟩, ⟨b8, b9, b10, b11⟩⟩
  unfold allZeroGoldilocks
  simp only [state12Sub_eq, lane4Sub_eq, Poseidon2State12.toList_eq]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    sub_eq_zero_iff_goldilocks, Poseidon2State12.mk.injEq, Lane4.mk.injEq]
  constructor
  · rintro ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩
    exact ⟨⟨e0, e1, e2, e3⟩, ⟨e4, e5, e6, e7⟩, ⟨e8, e9, e10, e11⟩⟩
  · rintro ⟨⟨e0, e1, e2, e3⟩, ⟨e4, e5, e6, e7⟩, ⟨e8, e9, e10, e11⟩⟩
    exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩

private theorem extRoundsResiduals_honest (rcs : List Poseidon2State12) (cur : Poseidon2State12) :
    allZeroGoldilocks (extRoundsResiduals rcs cur (buildExtRoundsSbox rcs cur)).2 = true ∧
    (extRoundsResiduals rcs cur (buildExtRoundsSbox rcs cur)).1 = runRounds externalRound rcs cur :=
  roundsResidualsPoly_honest extRoundSboxFn extRoundNextFn
    (fun a b => (state12Sub a b).toList) [Goldilocks.one] externalRound (fun rc cur => (externalRound_eq rc cur).symm)
    allZeroGoldilocks rfl allZeroGoldilocks_append
    (fun sb => (state12Sub_toList_allZero_iff sb sb).mpr rfl) rcs cur

private theorem extRoundsResiduals_allZero_iff
    (rcs : List Poseidon2State12) (cur : Poseidon2State12) (sbs : List Poseidon2State12) :
    allZeroGoldilocks (extRoundsResiduals rcs cur sbs).2 = true ↔
      sbs = buildExtRoundsSbox rcs cur :=
  roundsResidualsPoly_allZero_iff extRoundSboxFn extRoundNextFn
    (fun a b => (state12Sub a b).toList) [Goldilocks.one] externalRound (fun rc cur => (externalRound_eq rc cur).symm)
    allZeroGoldilocks rfl (by decide) allZeroGoldilocks_append state12Sub_toList_allZero_iff
    rcs sbs cur

private theorem intRoundsResiduals_honest (rcs : List Goldilocks) (cur : Poseidon2State12) :
    allZeroGoldilocks (intRoundsResiduals rcs cur (buildIntRoundsSbox rcs cur)).2 = true ∧
    (intRoundsResiduals rcs cur (buildIntRoundsSbox rcs cur)).1 = runRounds internalRound rcs cur :=
  roundsResidualsPoly_honest intRoundSboxFn intRoundNextFn
    (fun a b => [Goldilocks.sub a b]) [Goldilocks.one] internalRound (fun rc cur => (internalRound_eq rc cur).symm)
    allZeroGoldilocks rfl allZeroGoldilocks_append
    (fun sb => by
      change (Goldilocks.sub sb sb == Goldilocks.zero && true) = true
      rw [Bool.and_true]
      exact (sub_eq_zero_iff_goldilocks sb sb).mpr rfl) rcs cur

private theorem intRoundsResiduals_allZero_iff
    (rcs : List Goldilocks) (cur : Poseidon2State12) (sbs : List Goldilocks) :
    allZeroGoldilocks (intRoundsResiduals rcs cur sbs).2 = true ↔
      sbs = buildIntRoundsSbox rcs cur :=
  roundsResidualsPoly_allZero_iff intRoundSboxFn intRoundNextFn
    (fun a b => [Goldilocks.sub a b]) [Goldilocks.one] internalRound (fun rc cur => (internalRound_eq rc cur).symm)
    allZeroGoldilocks rfl (by decide) allZeroGoldilocks_append
    (fun a b => by
      change (Goldilocks.sub a b == Goldilocks.zero && true) = true ↔ a = b
      rw [Bool.and_true]
      exact sub_eq_zero_iff_goldilocks a b)
    rcs sbs cur

/-- **Exact 30-Round `Poseidon2` Row Constraint Soundness & Completeness (`poseidon2PermResiduals_allZero_iff`)**:
    All `130` degree-`≤ 7` residuals vanish if and only if `w` equals `honestPoseidon2PermWitness w.input`
    (fixing every intermediate S-box wire AND `w.output = poseidon2Perm12 w.input`)! -/
theorem poseidon2PermResiduals_allZero_iff (w : Poseidon2PermWitness) :
    allZeroGoldilocks (poseidon2PermResiduals w) = true ↔
      w = honestPoseidon2PermWitness w.input := by
  rcases w with ⟨inp, initSb, intSb, termSb, out⟩
  unfold poseidon2PermResiduals honestPoseidon2PermWitness
  dsimp only
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, state12Sub_toList_allZero_iff,
    Poseidon2PermWitness.mk.injEq, true_and]
  let s0 := applyME inp
  let s1 := runRounds externalRound poseidon2InitialExtConsts s0
  let s2 := runRounds internalRound poseidon2InternalConsts s1
  let s3 := runRounds externalRound poseidon2TerminalExtConsts s2
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, hOut⟩
    have e1 : initSb = buildExtRoundsSbox poseidon2InitialExtConsts s0 :=
      (extRoundsResiduals_allZero_iff poseidon2InitialExtConsts s0 initSb).mp h1
    subst e1
    have st1 : (extRoundsResiduals poseidon2InitialExtConsts s0
                 (buildExtRoundsSbox poseidon2InitialExtConsts s0)).1 = s1 :=
      (extRoundsResiduals_honest poseidon2InitialExtConsts s0).2
    rw [st1] at h2 h3 hOut
    have e2 : intSb = buildIntRoundsSbox poseidon2InternalConsts s1 :=
      (intRoundsResiduals_allZero_iff poseidon2InternalConsts s1 intSb).mp h2
    subst e2
    have st2 : (intRoundsResiduals poseidon2InternalConsts s1
                 (buildIntRoundsSbox poseidon2InternalConsts s1)).1 = s2 :=
      (intRoundsResiduals_honest poseidon2InternalConsts s1).2
    rw [st2] at h3 hOut
    have e3 : termSb = buildExtRoundsSbox poseidon2TerminalExtConsts s2 :=
      (extRoundsResiduals_allZero_iff poseidon2TerminalExtConsts s2 termSb).mp h3
    subst e3
    have st3 : (extRoundsResiduals poseidon2TerminalExtConsts s2
                 (buildExtRoundsSbox poseidon2TerminalExtConsts s2)).1 = s3 :=
      (extRoundsResiduals_honest poseidon2TerminalExtConsts s2).2
    rw [st3] at hOut
    exact ⟨rfl, rfl, rfl, hOut.symm⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    have hE1 := extRoundsResiduals_honest poseidon2InitialExtConsts s0
    rw [hE1.2]
    have hI := intRoundsResiduals_honest poseidon2InternalConsts s1
    rw [hI.2]
    have hE2 := extRoundsResiduals_honest poseidon2TerminalExtConsts s2
    rw [hE2.2]
    exact ⟨⟨⟨hE1.1, hI.1⟩, hE2.1⟩, rfl⟩

theorem poseidon2PermResiduals_output_eq {w : Poseidon2PermWitness}
    (hZero : allZeroGoldilocks (poseidon2PermResiduals w) = true) :
    w.output = poseidon2Perm12 w.input := by
  have hHon := (poseidon2PermResiduals_allZero_iff w).mp hZero
  calc w.output
    _ = (honestPoseidon2PermWitness w.input).output := congrArg Poseidon2PermWitness.output hHon
    _ = poseidon2Perm12 w.input := by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl

/-- All-zero `Poseidon2PermWitness` (used in `#tooth` all-zero trace rejection). -/
def zeroPoseidon2PermWitness : Poseidon2PermWitness where
  input       := state12Zero
  initExtSbox := List.replicate 4 state12Zero
  intSbox     := List.replicate 22 Goldilocks.zero
  termExtSbox := List.replicate 4 state12Zero
  output      := state12Zero

theorem first_external_zero_trace_rejected (output : Poseidon2State12) :
    allZeroGoldilocks (poseidon2PermResiduals
      { input := state12Zero, initExtSbox := List.replicate 4 state12Zero,
        intSbox := List.replicate 22 Goldilocks.zero,
        termExtSbox := List.replicate 4 state12Zero, output := output }) ≠ true := by
  intro h
  have he := congrArg (fun w : Poseidon2PermWitness => (w.initExtSbox.headD state12Zero).b0.x0)
    ((poseidon2PermResiduals_allZero_iff _).mp h)
  simp only [honestPoseidon2PermWitness, buildExtRoundsSbox, poseidon2InitialExtConsts_eq,
    buildRoundsSboxPoly, List.replicate_succ, List.headD_cons] at he
  have hz : state12Zero.b0.x0 = Goldilocks.zero := by rw [state12Zero_eq, lane4Zero_eq]
  exact poseidon2_initial_sbox_zero_nonzero (he.symm.trans hz)

theorem zeroPoseidon2PermWitness_rejected :
    allZeroGoldilocks (poseidon2PermResiduals zeroPoseidon2PermWitness) = false := by
  cases h : allZeroGoldilocks (poseidon2PermResiduals zeroPoseidon2PermWitness) with
  | false => rfl
  | true => exact False.elim (first_external_zero_trace_rejected state12Zero h)


end Qsag

end

public section

namespace Qsag

theorem allZeroGoldilocks_eq (rs : List Goldilocks) :
    allZeroGoldilocks rs = rs.all (· == Goldilocks.zero) := by rfl
end Qsag

end

public section

namespace Qsag

#export_eqns honestPoseidon2PermWitness
#export_eqns poseidon2PermResiduals

end Qsag
end
