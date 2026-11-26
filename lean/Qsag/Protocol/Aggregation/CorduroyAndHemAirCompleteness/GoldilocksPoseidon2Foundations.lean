module
/-
# Foundational `Goldilocks` Residual Lemmas and Group-A `Poseidon2` Round-Trace Lemmas

Boolean all-zero residual predicates over `Goldilocks` lists with their append / map laws, and
the round-trace lemmas for the Group-A `Poseidon2` permutation columns of the 256-column table.
-/

public import Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false
set_option maxErrors 1000

set_option Elab.async false
set_option exponentiation.threshold 2048

/-! ## §0. Foundational `Goldilocks` Algebraic & Group-A `Poseidon2` Round Trace Lemmas -/

/-- Boolean residual predicate: every `Goldilocks` entry in `xs` equals `Goldilocks.zero`. -/
def allZeroGold (xs : List Goldilocks) : Bool :=
  xs.all (· == Goldilocks.zero)

theorem allZeroGold_nil : allZeroGold [] = true := by
  unfold allZeroGold; rfl

theorem allZeroGold_cons (x : Goldilocks) (xs : List Goldilocks) :
    allZeroGold (x :: xs) = ((x == Goldilocks.zero) && allZeroGold xs) := by
  unfold allZeroGold; rfl

theorem allZeroGold_append (xs ys : List Goldilocks) :
    allZeroGold (xs ++ ys) = (allZeroGold xs && allZeroGold ys) := by
  unfold allZeroGold
  exact List.all_append

theorem goldSub_eq_zero_iff (a b : Goldilocks) :
    Goldilocks.sub a b = Goldilocks.zero ↔ a = b :=
  LawfulCommRing.sub_eq_zero_iff

def lane4ToList (u : Lane4) : List Goldilocks :=
  [u.x0, u.x1, u.x2, u.x3]

theorem lane4Sub_allZero_iff (a b : Lane4) :
    allZeroGold (lane4ToList (lane4Sub a b)) = true ↔ a = b := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp only [lane4Sub_eq, lane4ToList, allZeroGold]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  change (Goldilocks.sub a0 b0 = Goldilocks.zero ∧
          Goldilocks.sub a1 b1 = Goldilocks.zero ∧
          Goldilocks.sub a2 b2 = Goldilocks.zero ∧
          Goldilocks.sub a3 b3 = Goldilocks.zero) ↔ _
  simp only [goldSub_eq_zero_iff, Lane4.mk.injEq]

theorem state12Sub_allZero_iff (a b : Poseidon2State12) :
    allZeroGold (state12Sub a b).toList = true ↔ a = b := by
  rcases a with ⟨⟨a00, a01, a02, a03⟩, ⟨a10, a11, a12, a13⟩, ⟨a20, a21, a22, a23⟩⟩
  rcases b with ⟨⟨b00, b01, b02, b03⟩, ⟨b10, b11, b12, b13⟩, ⟨b20, b21, b22, b23⟩⟩
  simp only [state12Sub_eq, lane4Sub_eq, Poseidon2State12.toList_eq, allZeroGold]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  simp only [goldSub_eq_zero_iff, Poseidon2State12.mk.injEq, Lane4.mk.injEq]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨⟨h0, h1, h2, h3⟩, ⟨h4, h5, h6, h7⟩, ⟨h8, h9, h10, h11⟩⟩
  · rintro ⟨⟨h0, h1, h2, h3⟩, ⟨h4, h5, h6, h7⟩, ⟨h8, h9, h10, h11⟩⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- Full 30-round width-12 `Poseidon2` S-box witness (`4` initial external + `22` internal + `4` terminal external). -/
structure HemPoseidon2Witness where
  stIn        : Poseidon2State12
  initExtSbox : List Poseidon2State12
  intSbox     : List Goldilocks
  termExtSbox : List Poseidon2State12
  permOut     : Poseidon2State12
  deriving DecidableEq, Repr

private def buildExtSboxes : List Poseidon2State12 → Poseidon2State12 → Poseidon2State12 × List Poseidon2State12
  | [], cur => (cur, [])
  | rc :: rest, cur =>
    let sb := sboxState12 (state12Add cur rc)
    let (fin, tailSb) := buildExtSboxes rest (applyME sb)
    (fin, sb :: tailSb)

private def buildIntSboxes : List Goldilocks → Poseidon2State12 → Poseidon2State12 × List Goldilocks
  | [], cur => (cur, [])
  | rc :: rest, cur =>
    let sb := sbox7 (Goldilocks.add cur.b0.x0 rc)
    let next := applyMI ⟨⟨sb, cur.b0.x1, cur.b0.x2, cur.b0.x3⟩, cur.b1, cur.b2⟩
    let (fin, tailSb) := buildIntSboxes rest next
    (fin, sb :: tailSb)

private def evalExtRoundResiduals :
    List Poseidon2State12 → Poseidon2State12 → List Poseidon2State12 → Poseidon2State12 × List Goldilocks
  | [], cur, [] => (cur, [])
  | rc :: restRc, cur, sb :: restSb =>
    let expSb := sboxState12 (state12Add cur rc)
    let r0 := (state12Sub expSb sb).toList
    let (fin, rRest) := evalExtRoundResiduals restRc (applyME sb) restSb
    (fin, r0 ++ rRest)
  | _, cur, _ => (cur, [Goldilocks.one])

private def evalIntRoundResiduals :
    List Goldilocks → Poseidon2State12 → List Goldilocks → Poseidon2State12 × List Goldilocks
  | [], cur, [] => (cur, [])
  | rc :: restRc, cur, sb :: restSb =>
    let expSb := sbox7 (Goldilocks.add cur.b0.x0 rc)
    let r0 := Goldilocks.sub expSb sb
    let next := applyMI ⟨⟨sb, cur.b0.x1, cur.b0.x2, cur.b0.x3⟩, cur.b1, cur.b2⟩
    let (fin, rRest) := evalIntRoundResiduals restRc next restSb
    (fin, r0 :: rRest)
  | _, cur, _ => (cur, [Goldilocks.one])

/-- Honest 30-round width-12 `Poseidon2` trace witness for input `st`. -/
def honestHemPoseidon2Witness (st : Poseidon2State12) : HemPoseidon2Witness :=
  let s0 := applyME st
  let (s1, initSb) := buildExtSboxes poseidon2InitialExtConsts s0
  let (s2, intSb) := buildIntSboxes poseidon2InternalConsts s1
  let (s3, termSb) := buildExtSboxes poseidon2TerminalExtConsts s2
  { stIn := st, initExtSbox := initSb, intSbox := intSb, termExtSbox := termSb, permOut := s3 }

/-- Group-A degree-7 S-box & output wire residuals of a 30-round `Poseidon2` witness. -/
def hemPoseidon2GroupAResiduals (w : HemPoseidon2Witness) : List Goldilocks :=
  let (s1, r1) := evalExtRoundResiduals poseidon2InitialExtConsts (applyME w.stIn) w.initExtSbox
  let (s2, r2) := evalIntRoundResiduals poseidon2InternalConsts s1 w.intSbox
  let (s3, r3) := evalExtRoundResiduals poseidon2TerminalExtConsts s2 w.termExtSbox
  r1 ++ r2 ++ r3 ++ (state12Sub s3 w.permOut).toList

private theorem buildExtSboxes_spec :
    ∀ (rcs : List Poseidon2State12) (cur : Poseidon2State12),
      let out := buildExtSboxes rcs cur
      out.1 = runRounds externalRound rcs cur ∧
      out.2.length = rcs.length ∧
      (evalExtRoundResiduals rcs cur out.2).1 = out.1 ∧
      allZeroGold (evalExtRoundResiduals rcs cur out.2).2 = true
  | [], cur => by simp only [buildExtSboxes, evalExtRoundResiduals, runRounds_nil]; exact ⟨True.intro, True.intro, True.intro, rfl⟩
  | rc :: rest, cur => by
    let sb := sboxState12 (state12Add cur rc)
    obtain ⟨ih1, ihLen, ihEval1, ihZero⟩ := buildExtSboxes_spec rest (applyME sb)
    dsimp only [buildExtSboxes, evalExtRoundResiduals]
    rw [runRounds_cons, externalRound_eq]
    refine ⟨ih1, congrArg Nat.succ ihLen, ihEval1, ?_⟩
    rw [allZeroGold_append, Bool.and_eq_true]
    exact ⟨(state12Sub_allZero_iff sb sb).mpr rfl, ihZero⟩

private theorem buildIntSboxes_spec :
    ∀ (rcs : List Goldilocks) (cur : Poseidon2State12),
      let out := buildIntSboxes rcs cur
      out.1 = runRounds internalRound rcs cur ∧
      out.2.length = rcs.length ∧
      (evalIntRoundResiduals rcs cur out.2).1 = out.1 ∧
      allZeroGold (evalIntRoundResiduals rcs cur out.2).2 = true
  | [], cur => by simp only [buildIntSboxes, evalIntRoundResiduals, runRounds_nil]; exact ⟨True.intro, True.intro, True.intro, rfl⟩
  | rc :: rest, cur => by
    let sb := sbox7 (Goldilocks.add cur.b0.x0 rc)
    let next := applyMI ⟨⟨sb, cur.b0.x1, cur.b0.x2, cur.b0.x3⟩, cur.b1, cur.b2⟩
    obtain ⟨ih1, ihLen, ihEval1, ihZero⟩ := buildIntSboxes_spec rest next
    dsimp only [buildIntSboxes, evalIntRoundResiduals]
    rw [runRounds_cons, internalRound_eq]
    refine ⟨ih1, congrArg Nat.succ ihLen, ihEval1, ?_⟩
    rw [allZeroGold_cons, Bool.and_eq_true, beq_iff_eq]
    exact ⟨(goldSub_eq_zero_iff sb sb).mpr rfl, ihZero⟩

private theorem evalExtRoundResiduals_sound :
    ∀ (rcs : List Poseidon2State12) (cur : Poseidon2State12) (sbs : List Poseidon2State12),
      allZeroGold (evalExtRoundResiduals rcs cur sbs).2 = true →
      (evalExtRoundResiduals rcs cur sbs).1 = runRounds externalRound rcs cur
  | [], cur, [], _ => by rw [runRounds_nil]; rfl
  | [], cur, sb :: restSb, h => by
    dsimp only [evalExtRoundResiduals] at h
    exact absurd h (by decide)
  | rc :: restRc, cur, [], h => by
    dsimp only [evalExtRoundResiduals] at h
    exact absurd h (by decide)
  | rc :: restRc, cur, sb :: restSb, h => by
    dsimp only [evalExtRoundResiduals] at h ⊢
    rw [allZeroGold_append, Bool.and_eq_true] at h
    have hSb : sboxState12 (state12Add cur rc) = sb := (state12Sub_allZero_iff _ _).mp h.1
    rw [runRounds_cons, externalRound_eq, hSb]
    exact evalExtRoundResiduals_sound restRc (applyME sb) restSb h.2

private theorem evalIntRoundResiduals_sound :
    ∀ (rcs : List Goldilocks) (cur : Poseidon2State12) (sbs : List Goldilocks),
      allZeroGold (evalIntRoundResiduals rcs cur sbs).2 = true →
      (evalIntRoundResiduals rcs cur sbs).1 = runRounds internalRound rcs cur
  | [], cur, [], _ => by rw [runRounds_nil]; rfl
  | [], cur, sb :: restSb, h => by
    dsimp only [evalIntRoundResiduals] at h
    exact absurd h (by decide)
  | rc :: restRc, cur, [], h => by
    dsimp only [evalIntRoundResiduals] at h
    exact absurd h (by decide)
  | rc :: restRc, cur, sb :: restSb, h => by
    dsimp only [evalIntRoundResiduals] at h ⊢
    rw [allZeroGold_cons, Bool.and_eq_true, beq_iff_eq] at h
    have hSb : sbox7 (Goldilocks.add cur.b0.x0 rc) = sb := (goldSub_eq_zero_iff _ _).mp h.1
    rw [runRounds_cons, internalRound_eq, hSb]
    exact evalIntRoundResiduals_sound restRc _ restSb h.2

theorem honestHemPoseidon2Witness_output (st : Poseidon2State12) :
    (honestHemPoseidon2Witness st).stIn = st ∧
    (honestHemPoseidon2Witness st).permOut = poseidon2Perm12 st ∧
    (honestHemPoseidon2Witness st).initExtSbox.length = 4 ∧
    (honestHemPoseidon2Witness st).intSbox.length = 22 ∧
    (honestHemPoseidon2Witness st).termExtSbox.length = 4 ∧
    allZeroGold (hemPoseidon2GroupAResiduals (honestHemPoseidon2Witness st)) = true := by
  obtain ⟨e1, l1, ev1, z1⟩ := buildExtSboxes_spec poseidon2InitialExtConsts (applyME st)
  obtain ⟨e2, l2, ev2, z2⟩ := buildIntSboxes_spec poseidon2InternalConsts (buildExtSboxes poseidon2InitialExtConsts (applyME st)).1
  obtain ⟨e3, l3, ev3, z3⟩ := buildExtSboxes_spec poseidon2TerminalExtConsts
    (buildIntSboxes poseidon2InternalConsts (buildExtSboxes poseidon2InitialExtConsts (applyME st)).1).1
  have hLenInit : poseidon2InitialExtConsts.length = 4 := poseidon2InitialExtConsts_length
  have hLenInt  : poseidon2InternalConsts.length = 22 := poseidon2InternalConsts_length
  have hLenTerm : poseidon2TerminalExtConsts.length = 4 := poseidon2TerminalExtConsts_length
  refine ⟨rfl, ?_, l1.trans hLenInit, l2.trans hLenInt, l3.trans hLenTerm, ?_⟩
  · unfold honestHemPoseidon2Witness poseidon2Perm12
    dsimp only
    rw [e3, e2, e1]
  · unfold honestHemPoseidon2Witness hemPoseidon2GroupAResiduals
    dsimp only
    rw [ev1, ev2, ev3]
    simp only [allZeroGold_append, Bool.and_eq_true]
    exact ⟨⟨⟨z1, z2⟩, z3⟩, (state12Sub_allZero_iff _ _).mpr rfl⟩

/-- **Group-A `Poseidon2` Round Soundness (`hemPoseidon2GroupA_sound`)**:
    Whenever all 118 degree-7 S-box residuals and 12 output wire residuals vanish, `w.permOut`
    equals the exact 30-round width-12 permutation `poseidon2Perm12 w.stIn`. -/
theorem hemPoseidon2GroupA_sound (w : HemPoseidon2Witness)
    (hZero : allZeroGold (hemPoseidon2GroupAResiduals w) = true) :
    w.permOut = poseidon2Perm12 w.stIn := by
  unfold hemPoseidon2GroupAResiduals at hZero
  dsimp only at hZero
  simp only [allZeroGold_append, Bool.and_eq_true] at hZero
  rcases hZero with ⟨⟨⟨z1, z2⟩, z3⟩, zOut⟩
  have s1Eq := evalExtRoundResiduals_sound poseidon2InitialExtConsts (applyME w.stIn) w.initExtSbox z1
  have s2Eq := evalIntRoundResiduals_sound poseidon2InternalConsts _ w.intSbox z2
  have s3Eq := evalExtRoundResiduals_sound poseidon2TerminalExtConsts _ w.termExtSbox z3
  have outEq := (state12Sub_allZero_iff _ _).mp zOut
  unfold poseidon2Perm12
  rw [← outEq, s3Eq, s2Eq, s1Eq]

-- Seal 30-round `poseidon2Perm12` so subsequent symbolic proofs never unfold all 30 rounds.
attribute [local irreducible] poseidon2Perm12

end Qsag
end
